"""Group-agnostic independent algebra and module generator extraction."""

from __future__ import annotations

from collections.abc import Hashable
from typing import Callable

import numpy as np

from .combinatorics import (
    pivot_columns,
    row_kronecker_product,
    validate_waring_modulus,
)
from .evaluators import (
    evaluate_basis,
    sample_isotypic_input_probes,
)
from .bases import extract, space_dimensions
from .protocols import RepresentationTheory
from .types import IsotypicDataTree, IsotypicLeaf


ProbeTarget = Callable[[tuple[int, ...], int], tuple[int, ...]]
DegreeLimit = Callable[[int], int]
TreesByDegree = tuple[IsotypicDataTree, ...]


def compute_syndromes(
    theory: RepresentationTheory,
    polynomials: tuple[IsotypicLeaf, ...],
    probe_batches: tuple[np.ndarray, ...],
    modulus: int,
    output_dimension: int,
    young_tree_cache: dict[Hashable, np.ndarray] | None = None,
) -> np.ndarray:
    """Evaluate isotypic leaves as ``probe x output x column`` blocks.

    Empty polynomial sets still use the same rank-3 syndrome convention, with
    zero basis columns.
    """
    if not polynomials:
        return _empty_syndromes(probe_batches[0].shape[0], output_dimension, modulus)

    if young_tree_cache is None:
        young_tree_cache = {}
    blocks = tuple(
        evaluate_basis(
            theory,
            leaf,
            probe_batches,
            modulus,
            young_tree_cache,
        )
        for leaf in polynomials
    )
    if len(blocks) == 1:
        return blocks[0]
    return np.concatenate(blocks, axis=-1)


def extract_independent_generators(
    theory: RepresentationTheory,
    invariant_trees: TreesByDegree,
    covariant_trees: TreesByDegree,
    probe_target: ProbeTarget,
    degree_limit: DegreeLimit,
    random_seed: int,
    *,
    modulus: int,
    first_generator_degree: int = 0,
    target_dimensions_by_degree: tuple[int, ...] | None = None,
) -> tuple[tuple[IsotypicLeaf, ...], ...]:
    """Extract minimal homogeneous generators from evaluated basis syndromes.

    The pivoting machinery is independent of the concrete group.  Concrete
    backends may pass ``target_dimensions_by_degree`` when they have a faster
    dimension formula than counting the supplied isotypic tree leaves.
    """
    _validate_generator_trees(theory, invariant_trees, covariant_trees)
    if first_generator_degree < 0:
        raise ValueError("first_generator_degree must be nonnegative")

    max_degree = covariant_trees[-1].degree
    output_dimension = theory.irrep_dimension(covariant_trees[0].output_irrep)
    invariant_output_dimension = theory.irrep_dimension(invariant_trees[0].output_irrep)
    if target_dimensions_by_degree is None:
        target_dimensions = space_dimensions(covariant_trees)
    else:
        if len(target_dimensions_by_degree) != max_degree + 1:
            raise ValueError(
                "target_dimensions_by_degree must have one entry per degree "
                "through the maximum covariant tree degree"
            )
        if any(dimension < 0 for dimension in target_dimensions_by_degree):
            raise ValueError("target_dimensions_by_degree entries must be nonnegative")
        target_dimensions = target_dimensions_by_degree

    target_num_probes = probe_target(target_dimensions, output_dimension)
    if len(target_num_probes) != max_degree + 1:
        raise ValueError("probe_target must return one probe count per degree")
    if any(count < 0 for count in target_num_probes):
        raise ValueError("probe_target must return nonnegative probe counts")

    active_modulus = validate_waring_modulus(modulus, max_degree)
    max_probes = max(target_num_probes) if target_num_probes else 1
    probe_batches = sample_isotypic_input_probes(
        theory,
        covariant_trees[0].input_irreps,
        covariant_trees[0].input_multiplicities,
        max_probes,
        active_modulus,
        random_seed,
    )
    young_tree_cache: dict[Hashable, np.ndarray] = {}

    covariant_generators: list[tuple[IsotypicLeaf, ...]] = [
        tuple() for _ in range(max_degree + 1)
    ]
    covariant_syndromes = [
        _empty_syndromes(max_probes, output_dimension, active_modulus)
        for _ in range(max_degree + 1)
    ]
    invariant_syndromes = tuple(
        compute_syndromes(
            theory,
            invariant_trees[d].isotypic_leaves,
            probe_batches,
            active_modulus,
            invariant_output_dimension,
            young_tree_cache,
        )
        for d in range(max_degree + 1)
    )

    covariant_generators[0] = covariant_trees[0].isotypic_leaves
    covariant_syndromes[0] = compute_syndromes(
        theory,
        covariant_generators[0],
        probe_batches,
        active_modulus,
        output_dimension,
        young_tree_cache,
    )

    for degree in range(1, max_degree + 1):
        degree_leaves = covariant_trees[degree].isotypic_leaves
        if not degree_leaves:
            continue
        num_probes = target_num_probes[degree]

        previous_blocks = []
        for generator_degree in range(
            first_generator_degree,
            degree_limit(degree) + 1,
        ):
            invariant_degree = degree - generator_degree
            if invariant_degree <= 0:
                continue
            inv_syn = invariant_syndromes[invariant_degree]
            cov_syn = covariant_syndromes[generator_degree]
            if inv_syn.shape[-1] > 0 and cov_syn.shape[-1] > 0:
                previous_blocks.append(
                    row_kronecker_product(
                        inv_syn[:num_probes],
                        cov_syn[:num_probes],
                        active_modulus,
                    )
                )
        candidate_syndromes = compute_syndromes(
            theory,
            degree_leaves,
            tuple(batch[:num_probes, :, :] for batch in probe_batches),
            active_modulus,
            output_dimension,
            young_tree_cache,
        )
        previous_columns = sum(block.shape[-1] for block in previous_blocks)
        total_columns = previous_columns + candidate_syndromes.shape[-1]
        flat_syndromes_source = (
            np.concatenate((*previous_blocks, candidate_syndromes), axis=-1)
            if previous_blocks
            else candidate_syndromes
        )
        flat_syndromes = flat_syndromes_source.reshape((-1, total_columns))
        linear_indices = tuple(
            pivot - previous_columns
            for pivot in pivot_columns(flat_syndromes, active_modulus)
            if pivot >= previous_columns
        )
        covariant_generators[degree] = extract(
            linear_indices, degree_leaves
        )
        if degree < max_degree:
            covariant_syndromes[degree] = candidate_syndromes[
                ..., linear_indices
            ]
            if num_probes < max_probes and linear_indices:
                extra = compute_syndromes(
                    theory,
                    covariant_generators[degree],
                    tuple(batch[num_probes:, :, :] for batch in probe_batches),
                    active_modulus,
                    output_dimension,
                    young_tree_cache,
                )
                covariant_syndromes[degree] = np.concatenate(
                    [covariant_syndromes[degree], extra], axis=0
                )
    return tuple(covariant_generators)


def _empty_syndromes(
    probe_count: int,
    output_dimension: int,
    modulus: int,
) -> np.ndarray:
    dtype = np.complex128 if modulus == 0 else np.uint64
    return np.empty((probe_count, output_dimension, 0), dtype=dtype)


def _validate_generator_trees(
    theory: RepresentationTheory,
    invariant_trees: TreesByDegree,
    covariant_trees: TreesByDegree,
) -> None:
    if not invariant_trees:
        raise ValueError("invariant_trees must contain at least degree 0")
    if not covariant_trees:
        raise ValueError("covariant_trees must contain at least degree 0")
    for degree, tree in enumerate(invariant_trees):
        if tree.degree != degree:
            raise ValueError(f"invariant_trees[{degree}].degree must equal {degree}")
    for degree, tree in enumerate(covariant_trees):
        if tree.degree != degree:
            raise ValueError(f"covariant_trees[{degree}].degree must equal {degree}")
    invariant_tree = invariant_trees[0]
    covariant_tree = covariant_trees[0]
    if len(invariant_trees) < len(covariant_trees):
        raise ValueError(
            "invariant_trees must be computed through the maximum covariant degree"
        )
    if invariant_tree.input_irreps != covariant_tree.input_irreps:
        raise ValueError("invariant_trees and covariant_trees must share input_irreps")
    if invariant_tree.input_multiplicities != covariant_tree.input_multiplicities:
        raise ValueError(
            "invariant_trees and covariant_trees must share input_multiplicities"
        )
    _validate_tree_family_metadata(invariant_trees, invariant_tree, "invariant_trees")
    _validate_tree_family_metadata(covariant_trees, covariant_tree, "covariant_trees")
    if theory.irrep_dimension(invariant_tree.output_irrep) != 1:
        raise ValueError("invariant_trees output irrep must be one-dimensional")


def _validate_tree_family_metadata(
    trees_by_degree: TreesByDegree,
    first_tree: IsotypicDataTree,
    name: str,
) -> None:
    for tree in trees_by_degree[1:]:
        if tree.input_irreps != first_tree.input_irreps:
            raise ValueError(f"{name} must share input_irreps across degrees")
        if tree.input_multiplicities != first_tree.input_multiplicities:
            raise ValueError(f"{name} must share input_multiplicities across degrees")
        if tree.output_irrep != first_tree.output_irrep:
            raise ValueError(f"{name} must share output_irrep across degrees")


__all__ = (
    "DegreeLimit",
    "ProbeTarget",
    "TreesByDegree",
    "compute_syndromes",
    "extract_independent_generators",
)
