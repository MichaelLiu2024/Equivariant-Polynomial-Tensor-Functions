"""Benchmark helper for group-agnostic basis construction."""

from __future__ import annotations

from collections.abc import Callable
from time import perf_counter

from equivariant_polynomials.core import (
    Irrep,
    RepresentationTheory,
    extract_independent_generators,
)

HilbertSeries = Callable[
    [tuple[Irrep, ...], tuple[int, ...], Irrep, int],
    tuple[int, ...],
]
MultigradedHilbertSeries = Callable[
    [tuple[Irrep, ...], tuple[int, ...], Irrep, tuple[int, ...]],
    dict[tuple[int, ...], int],
]

__all__ = ("benchmark",)

MINIMAL_INTEGRITY_BASIS_SIZE_DATA = {
    ((1,), (1,), 0): (0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
    ((1,), (2,), 0): (0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
    ((1,), (3,), 0): (0, 0, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
    ((2,), (2,), 0): (0, 0, 3, 4, 1, 0),
    ((4,), (1,), 0): (0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0),
    ((1, 3), (1, 1), 0): (0, 0, 2, 0, 4, 0, 5, 3, 1, 7, 1, 2, 0, 1, 0, 1),
    ((2, 3), (1, 1), 0): (0, 0, 2, 2, 4, 4, 9, 9, 8, 5, 3, 2, 1, 1, 1),
    ((1, 2, 3), (1, 1, 1), 0): (0, 0, 3, 4, 12, 15, 37, 42, 38, 22, 9, 6, 3, 2, 1, 1),
    ((2, 3), (2, 1), 0): (0, 0, 4, 7, 14, 26, 52, 68, 60, 39),
    ((2, 3), (2, 1), 4): (0, 0, 6, 21, 63, 147, 264, 284, 133, 35),
    ((2, 3), (2, 1), 5): (0, 0, 2, 14, 62, 180, 378, 556),
    ((2, 3), (2, 1), 6): (0, 0, 1, 13, 55, 168, 402, 671),
    ((2, 4), (2, 1), 0): (0, 0, 4, 10, 16, 33, 57, 76, 66, 21, 7, 5),
}


def _known_generator_check(
    input_irreps: tuple[Irrep, ...],
    input_multiplicities: tuple[int, ...],
    output_irrep: Irrep,
    counts: tuple[int, ...],
) -> bool | None:
    known = MINIMAL_INTEGRITY_BASIS_SIZE_DATA.get(
        (input_irreps, input_multiplicities, output_irrep)
    )
    if known is None:
        return None
    known = known[: len(counts)]
    return counts[: len(known)] == known


def benchmark(
    theory: RepresentationTheory,
    hilbert_series: HilbertSeries,
    input_irreps: tuple[Irrep, ...],
    input_multiplicities: tuple[int, ...],
    output_irrep: Irrep,
    max_degree: int,
    random_seed: int,
    modulus: int,
    hilbert_series_multigraded: MultigradedHilbertSeries | None = None,
):
    """Run a basis-construction benchmark and report generator counts by degree."""
    total_start = perf_counter()
    trivial_irrep = theory.trivial_irrep
    max_multidegree = (max_degree,) * len(input_irreps)

    def run_generators(
        label: str,
        target_irrep: Irrep,
        probe_target: Callable[[tuple[int, ...], int], tuple[int, ...]],
        degree_limit: Callable[[int], int],
        *,
        first_generator_degree: int = 0,
        count_constant: bool = True,
    ) -> dict[str, object]:
        dimensions = hilbert_series(
            input_irreps,
            input_multiplicities,
            target_irrep,
            max_degree,
        )
        dimensions_by_multidegree = (
            hilbert_series_multigraded(
                input_irreps,
                input_multiplicities,
                target_irrep,
                max_multidegree,
            )
            if hilbert_series_multigraded is not None
            else None
        )

        step_start = perf_counter()
        generators = extract_independent_generators(
            theory,
            input_irreps,
            input_multiplicities,
            target_irrep,
            max_degree,
            probe_target,
            degree_limit,
            random_seed=random_seed,
            modulus=modulus,
            first_generator_degree=first_generator_degree,
            target_dimensions_by_multidegree=dimensions_by_multidegree,
        )
        seconds = perf_counter() - step_start
        print(f"{label} generators: {seconds:.3f} s")

        counts = tuple(map(len, generators))
        if not count_constant:
            counts = (0, *counts[1:])
        return {
            "hilbert_dimensions": dimensions,
            "generator_counts": counts,
            "matches_known_generators": _known_generator_check(
                input_irreps,
                input_multiplicities,
                target_irrep,
                counts,
            ),
            "generator_seconds": seconds,
        }

    result: dict[str, object] = {
        "scenario": {
            "input_irreps": input_irreps,
            "input_multiplicities": input_multiplicities,
            "output_irrep": output_irrep,
            "max_degree": max_degree,
            "random_seed": random_seed,
            "modulus": modulus,
        },
        "algebra": run_generators(
            "algebra",
            trivial_irrep,
            lambda dimensions, _output_dimension: dimensions,
            lambda degree: degree // 2,
            first_generator_degree=1,
            count_constant=False,
        ),
        "module": None,
    }

    if output_irrep != trivial_irrep:
        result["module"] = run_generators(
            "module",
            output_irrep,
            lambda dimensions, output_dimension: tuple(
                (dimension + output_dimension - 1) // output_dimension + 2
                if dimension
                else 0
                for dimension in dimensions
            ),
            lambda degree: degree - 1,
        )

    result["total_seconds"] = perf_counter() - total_start
    print(f"total: {result['total_seconds']:.3f} s")
    return result
