"""Benchmark helper for group-agnostic basis construction."""

from __future__ import annotations

import math
from collections.abc import Callable
from time import perf_counter

from equivariant_polynomials.core import (
    Irrep,
    RepresentationTheory,
    build_isotypic_data_trees_by_degree,
    extract_independent_generators,
    space_dimensions,
)

HilbertSeries = Callable[
    [tuple[Irrep, ...], tuple[int, ...], Irrep, int],
    tuple[int, ...],
]
BenchmarkSummary = dict[str, object]

__all__ = ("BenchmarkSummary", "benchmark")


def benchmark(
    theory: RepresentationTheory,
    hilbert_series: HilbertSeries,
    input_irreps: tuple[Irrep, ...],
    input_multiplicities: tuple[int, ...],
    output_irrep: Irrep,
    max_degree: int,
    invariant_irrep: Irrep,
    random_seed: int,
    modulus: int,
    verbose: bool = False,
) -> BenchmarkSummary:
    """Profile basis construction and report generator counts by degree."""
    total_start = perf_counter()

    step_start = perf_counter()
    invariant_trees = build_isotypic_data_trees_by_degree(
        theory,
        input_irreps,
        input_multiplicities,
        invariant_irrep,
        max_degree,
        random_seed=random_seed,
        modulus=modulus,
    )
    invariant_tree_seconds = perf_counter() - step_start
    if verbose:
        print(f"algebra tree: {invariant_tree_seconds:.3f} s")

    algebra_dimensions = hilbert_series(
        input_irreps,
        input_multiplicities,
        invariant_irrep,
        max_degree,
    )
    step_start = perf_counter()
    invariant_generators = extract_independent_generators(
        theory,
        invariant_trees,
        invariant_trees,
        lambda dimensions, _output_dimension: dimensions,
        lambda degree: degree // 2,
        random_seed=random_seed,
        modulus=modulus,
        first_generator_degree=1,
        target_dimensions_by_degree=algebra_dimensions,
    )
    algebra_seconds = perf_counter() - step_start
    if verbose:
        print(f"algebra generators: {algebra_seconds:.3f} s")

    candidate_algebra_dimensions = space_dimensions(invariant_trees)
    result: dict[str, object] = {
        "scenario": {
            "input_irreps": input_irreps,
            "input_multiplicities": input_multiplicities,
            "output_irrep": output_irrep,
            "invariant_irrep": invariant_irrep,
            "max_degree": max_degree,
            "random_seed": random_seed,
            "modulus": modulus,
        },
        "algebra": {
            "candidate_dimensions": candidate_algebra_dimensions,
            "hilbert_dimensions": algebra_dimensions,
            "matches_hilbert": candidate_algebra_dimensions == algebra_dimensions,
            "generator_counts": tuple(map(len, invariant_generators)),
            "tree_seconds": invariant_tree_seconds,
            "generator_seconds": algebra_seconds,
        },
        "module": None,
    }

    if output_irrep != invariant_irrep:
        step_start = perf_counter()
        covariant_trees = build_isotypic_data_trees_by_degree(
            theory,
            input_irreps,
            input_multiplicities,
            output_irrep,
            max_degree,
            random_seed=random_seed,
            modulus=modulus,
        )
        covariant_tree_seconds = perf_counter() - step_start
        if verbose:
            print(f"module tree: {covariant_tree_seconds:.3f} s")

        module_dimensions = hilbert_series(
            input_irreps,
            input_multiplicities,
            output_irrep,
            max_degree,
        )
        step_start = perf_counter()
        covariant_generators = extract_independent_generators(
            theory,
            invariant_trees,
            covariant_trees,
            lambda dimensions, output_dimension: tuple(
                math.ceil(d / output_dimension) for d in dimensions
            ),
            lambda degree: degree - 1,
            random_seed=random_seed,
            modulus=modulus,
            target_dimensions_by_degree=module_dimensions,
        )
        module_seconds = perf_counter() - step_start
        if verbose:
            print(f"module generators: {module_seconds:.3f} s")

        candidate_module_dimensions = space_dimensions(covariant_trees)
        result["module"] = {
            "candidate_dimensions": candidate_module_dimensions,
            "hilbert_dimensions": module_dimensions,
            "matches_hilbert": candidate_module_dimensions == module_dimensions,
            "generator_counts": tuple(map(len, covariant_generators)),
            "tree_seconds": covariant_tree_seconds,
            "generator_seconds": module_seconds,
        }

    result["total_seconds"] = perf_counter() - total_start
    if verbose:
        print(f"total: {result['total_seconds']:.3f} s")
    return result
