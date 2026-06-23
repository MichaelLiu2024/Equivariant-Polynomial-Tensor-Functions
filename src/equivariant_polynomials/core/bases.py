"""Abstract tensor-product and Schur-power basis construction."""

from __future__ import annotations

import math
from collections.abc import Callable, Sequence
from dataclasses import replace
from functools import cache
from itertools import product
from typing import TypeVar

import numpy as np

from .combinatorics import (
    conjugate_partition,
    ragged_multi_index,
    validate_modulus,
)
from .evaluators import (
    evaluate_antisymmetrized_tensor_train,
    evaluate_tensor_train,
    sample_tensor_power_probes,
)
from .protocols import RepresentationTheory
from .streaming import stream_independent_candidates
from .types import (
    Irrep,
    IsotypicLeaf,
    Partition,
    TensorTrain,
    TensorTrainCore,
    TensorTree,
)

MAX_RANK_ATTEMPTS = 4
_T = TypeVar("_T")


@cache
def tensor_product_basis(
    theory: RepresentationTheory,
    irreps: tuple[Irrep, ...],
    output: Irrep,
) -> tuple[TensorTrain, ...]:
    """Enumerate left-associated tensor-product bases.

    The group supplies binary constituent irreps together with their multiplicities.
    This routine assembles all compatible irrep paths and multiplicity choices
    into tensor-train core labels.
    """
    if not irreps:
        raise ValueError("irreps must be nonempty")
    irrep_count = len(irreps)
    if irrep_count == 1:
        return ((),) if irreps[0] == output else ()

    @cache
    def suffixes(i: int, left: Irrep) -> tuple[TensorTrain, ...]:
        if i == irrep_count:
            return ((),) if left == output else ()

        right = irreps[i]
        tensor_trains: list[TensorTrain] = []
        for next_output, multiplicity_count in theory.tensor_product_constituent_irreps(
            left,
            right,
        ):
            next_suffixes = suffixes(i + 1, next_output)
            if not next_suffixes:
                continue
            for multiplicity in range(1, multiplicity_count + 1):
                core = TensorTrainCore(left, right, next_output, multiplicity)
                for suffix in next_suffixes:
                    tensor_trains.append((core,) + suffix)
        return tuple(tensor_trains)

    return suffixes(1, irreps[0])


def _constituent_multiplicity(
    constituent_multiplicities: tuple[tuple[Irrep, int], ...],
    output: Irrep,
) -> int:
    for constituent, multiplicity in constituent_multiplicities:
        if constituent == output:
            return multiplicity
    return 0


def _has_tensor_product_constituent(
    theory: RepresentationTheory,
    irreps: tuple[Irrep, ...],
    output: Irrep,
) -> bool:
    if not irreps:
        raise ValueError("irreps must be nonempty")

    current = {irreps[0]}
    for right in irreps[1:]:
        current = {
            constituent
            for left in current
            for constituent, _multiplicity in theory.tensor_product_constituent_irreps(
                left,
                right,
            )
        }
    return output in current


def _rank_select_candidates(
    candidates: Sequence[_T],
    dimension: int,
    output_dimension: int,
    random_seed: int,
    modulus: int,
    attempt_evaluator: Callable[[int, int], Callable[[tuple[_T, ...]], np.ndarray]],
    error_message: Callable[[int], str],
) -> tuple[_T, ...]:
    base_num_probes = math.ceil(dimension / output_dimension) + 2
    last_rank = 0

    for attempt in range(MAX_RANK_ATTEMPTS):
        num_probes = base_num_probes + attempt
        selected, last_rank = stream_independent_candidates(
            candidates,
            attempt_evaluator(attempt, num_probes),
            dimension,
            num_probes * output_dimension,
            modulus,
            random_seed + attempt,
        )
        if len(selected) == dimension:
            return selected

    raise RuntimeError(error_message(last_rank))


def _rank_select_tensor_trains(
    theory: RepresentationTheory,
    irrep: Irrep,
    degree: int,
    output: Irrep,
    dimension: int,
    random_seed: int,
    antisymmetric: bool,
    modulus: int,
) -> tuple[TensorTrain, ...]:
    if dimension <= 0:
        return ()
    if degree == 0:
        return ((),) if dimension == 1 else ()

    candidates = tensor_product_basis(theory, (irrep,) * degree, output)
    output_dimension = theory.irrep_dimension(output)
    evaluate = (
        evaluate_antisymmetrized_tensor_train
        if antisymmetric
        else evaluate_tensor_train
    )

    def attempt_evaluator(
        attempt: int,
        num_probes: int,
    ) -> Callable[[tuple[TensorTrain, ...]], np.ndarray]:
        probe_vectors = sample_tensor_power_probes(
            theory,
            irrep,
            degree,
            num_probes,
            modulus,
            random_seed + attempt,
            antisymmetric,
        )

        def evaluate_batch(batch: tuple[TensorTrain, ...]) -> np.ndarray:
            return np.stack(
                [
                    evaluate(
                        theory,
                        tensor_train,
                        probe_vectors,
                        modulus,
                        "batch",
                    ).reshape(-1)
                    for tensor_train in batch
                ],
                axis=1,
            )

        return evaluate_batch

    kind = "exterior" if antisymmetric else "symmetric"
    return _rank_select_candidates(
        candidates,
        dimension,
        output_dimension,
        random_seed,
        modulus,
        attempt_evaluator,
        lambda rank: (
            f"rank probes found {rank} {kind}-power basis elements "
            f"for irrep={irrep}, degree={degree}, output={output}; "
            f"expected {dimension}"
        ),
    )


@cache
def symmetrized_power_basis(
    theory: RepresentationTheory,
    irrep: Irrep,
    degree: int,
    output: Irrep,
    partition: Partition,
    random_seed: int,
    antisymmetric: bool,
    modulus: int,
) -> tuple[TensorTrain, ...]:
    """Select a tensor-train basis for a single-row or single-column Schur part."""
    validate_modulus(modulus, max_degree=degree)
    return _rank_select_tensor_trains(
        theory,
        irrep,
        degree,
        output,
        _constituent_multiplicity(
            theory.schur_power_constituent_irreps(irrep, partition),
            output,
        ),
        random_seed=random_seed,
        antisymmetric=antisymmetric,
        modulus=modulus,
    )


def _rank_select_schur_power_candidates(
    theory: RepresentationTheory,
    irrep: Irrep,
    partition: Partition,
    output: Irrep,
    candidates: tuple[TensorTree, ...],
    dimension: int,
    random_seed: int,
    modulus: int,
) -> tuple[TensorTree, ...]:
    if dimension <= 0:
        return ()

    output_dimension = theory.irrep_dimension(output)

    def attempt_evaluator(
        attempt: int,
        num_probes: int,
    ) -> Callable[[tuple[TensorTree, ...]], np.ndarray]:
        probe_vectors = sample_tensor_power_probes(
            theory,
            irrep,
            len(partition),
            num_probes,
            modulus,
            random_seed + attempt,
            antisymmetric=True,
        )
        leaf_values: dict[TensorTrain, np.ndarray] = {}

        def evaluate_leaf(tensor_train: TensorTrain) -> np.ndarray:
            if tensor_train not in leaf_values:
                leaf_values[tensor_train] = evaluate_antisymmetrized_tensor_train(
                    theory,
                    tensor_train,
                    probe_vectors,
                    modulus,
                    "batch",
                )
            return leaf_values[tensor_train]

        def evaluate_batch(batch: tuple[TensorTree, ...]) -> np.ndarray:
            return np.stack(
                [
                    evaluate_tensor_train(
                        theory,
                        candidate.interior_tensor_train,
                        tuple(
                            evaluate_leaf(tensor_train)
                            for tensor_train in candidate.leaf_tensor_trains
                        ),
                        modulus,
                        "batch_multi",
                    ).reshape(-1)
                    for candidate in batch
                ],
                axis=1,
            )

        return evaluate_batch

    return _rank_select_candidates(
        candidates,
        dimension,
        output_dimension,
        random_seed,
        modulus,
        attempt_evaluator,
        lambda rank: (
            f"rank probes found {rank} Schur-power basis elements "
            f"for irrep={irrep}, partition={partition}, output={output}; "
            f"expected {dimension}"
        ),
    )


@cache
def schur_functor_basis(
    theory: RepresentationTheory,
    irrep: Irrep,
    partition: Partition,
    output: Irrep,
    random_seed: int,
    modulus: int,
) -> tuple[TensorTree, ...]:
    """Assemble an abstract tensor-tree basis for one Schur-power isotypic part.

    The abstract layer builds the same tensor-tree search space for every
    reductive group. It then selects independent candidates using random
    probes over the requested arithmetic mode and the concrete group's binary
    coupling tensors.
    """
    validate_modulus(modulus, max_degree=sum(partition))
    if not partition:
        return (
            (TensorTree((), ((),)),)
            if _constituent_multiplicity(
                theory.schur_power_constituent_irreps(irrep, ()),
                output,
            )
            else ()
        )
    if len(partition) == 1:
        return tuple(
            TensorTree(tensor_train, tuple(() for _ in range(partition[0])))
            for tensor_train in symmetrized_power_basis(
                theory,
                irrep,
                partition[0],
                output,
                partition,
                random_seed,
                False,
                modulus,
            )
        )
    if partition[0] == 1:
        return tuple(
            TensorTree((), (tensor_train,))
            for tensor_train in symmetrized_power_basis(
                theory,
                irrep,
                len(partition),
                output,
                partition,
                random_seed,
                True,
                modulus,
            )
        )

    dimension = _constituent_multiplicity(
        theory.schur_power_constituent_irreps(irrep, partition),
        output,
    )
    if dimension <= 0:
        return ()

    column_heights = conjugate_partition(partition)
    component_options = tuple(
        tuple(
            constituent
            for constituent, _multiplicity in theory.schur_power_constituent_irreps(
                irrep,
                (1,) * degree,
            )
        )
        for degree in column_heights
    )
    candidates: list[TensorTree] = []
    for intermediate_irreps in product(*component_options):
        if not _has_tensor_product_constituent(theory, intermediate_irreps, output):
            continue
        interior_tensor_trains = tensor_product_basis(
            theory,
            intermediate_irreps,
            output,
        )
        leaf_tensor_train_options = tuple(
            symmetrized_power_basis(
                theory,
                irrep,
                degree,
                intermediate,
                (1,) * degree,
                random_seed,
                True,
                modulus,
            )
            for degree, intermediate in zip(
                column_heights,
                intermediate_irreps,
            )
        )
        for interior_tensor_train in interior_tensor_trains:
            for leaf_tensor_trains in product(*leaf_tensor_train_options):
                candidates.append(TensorTree(interior_tensor_train, leaf_tensor_trains))

    return _rank_select_schur_power_candidates(
        theory,
        irrep,
        partition,
        output,
        tuple(candidates),
        dimension,
        random_seed=random_seed,
        modulus=modulus,
    )


def _leaf_basis_axes(leaf: IsotypicLeaf) -> tuple[int, ...]:
    input_axes = tuple(
        axis_length
        for tensor_trees, tableaux in zip(
            leaf.leaf_tensor_trees,
            leaf.semi_standard_young_tableaux,
        )
        for axis_length in (len(tensor_trees), len(tableaux))
    )
    return (len(leaf.interior_tensor_trains), *input_axes)


def space_dimension(
    isotypic_leaves: tuple[IsotypicLeaf, ...],
) -> int:
    return sum(
        math.prod(_leaf_basis_axes(leaf))
        for leaf in isotypic_leaves
    )


def extract(
    linear_indices: tuple[int, ...],
    leaves: tuple[IsotypicLeaf, ...],
) -> tuple[IsotypicLeaf, ...]:
    """Extract selected concrete leaf-basis elements from a degree basis."""
    if not linear_indices:
        return ()
    leaf_axes = tuple(_leaf_basis_axes(leaf) for leaf in leaves)
    leaf_dimensions = tuple(math.prod(axes) for axes in leaf_axes)
    out = []
    for leaf_index, basis_index in ragged_multi_index(
        linear_indices,
        leaf_dimensions,
    ):
        leaf = leaves[leaf_index]
        axis_indices = np.unravel_index(basis_index, leaf_axes[leaf_index])
        out.append(
            replace(
                leaf,
                interior_tensor_trains=(
                    leaf.interior_tensor_trains[axis_indices[0]],
                ),
                leaf_tensor_trees=tuple(
                    (choices[index],)
                    for choices, index in zip(
                        leaf.leaf_tensor_trees,
                        axis_indices[1::2],
                    )
                ),
                semi_standard_young_tableaux=tuple(
                    (choices[index],)
                    for choices, index in zip(
                        leaf.semi_standard_young_tableaux,
                        axis_indices[2::2],
                    )
                ),
            )
        )
    return tuple(out)


__all__ = (
    "tensor_product_basis",
    "symmetrized_power_basis",
    "schur_functor_basis",
    "space_dimension",
    "extract",
)
