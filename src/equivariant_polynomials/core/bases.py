"""Abstract tensor-product and Schur-power basis construction."""

from __future__ import annotations

import math
from collections.abc import Callable, Iterable, Iterator
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
    evaluate_power_basis_batch,
    evaluate_tensor_train,
    sample_tensor_power_probes,
)
from .protocols import RepresentationTheory
from .streaming import (
    shuffled_stream_batches,
    stream_batches,
    stream_independent_candidates,
)
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
    output_irrep: Irrep,
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
        return ((),) if irreps[0] == output_irrep else ()

    @cache
    def suffixes(i: int, left: Irrep) -> tuple[TensorTrain, ...]:
        if i == irrep_count:
            return ((),) if left == output_irrep else ()

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


def _stream_tensor_product_basis(
    theory: RepresentationTheory,
    irreps: tuple[Irrep, ...],
    output_irrep: Irrep,
    rng: np.random.Generator,
) -> Iterator[TensorTrain]:
    """Yield the tensor-product basis lazily in randomized order.

    Equivalent to ``tensor_product_basis`` as a set, but generates trains on
    demand with constituents shuffled at each coupling, so rank selection can
    stop after a handful of batches instead of materializing every path.
    """
    irrep_count = len(irreps)

    def suffixes(i: int, left: Irrep) -> Iterator[TensorTrain]:
        if i == irrep_count:
            if left == output_irrep:
                yield ()
            return

        right = irreps[i]
        constituents = list(theory.tensor_product_constituent_irreps(left, right))
        rng.shuffle(constituents)
        for next_output, multiplicity_count in constituents:
            for multiplicity in range(1, multiplicity_count + 1):
                core = TensorTrainCore(left, right, next_output, multiplicity)
                for suffix in suffixes(i + 1, next_output):
                    yield (core,) + suffix

    yield from suffixes(1, irreps[0])


def _constituent_multiplicity(
    constituent_multiplicities: tuple[tuple[Irrep, int], ...],
    output_irrep: Irrep,
) -> int:
    return dict(constituent_multiplicities).get(output_irrep, 0)


def _has_tensor_product_constituent(
    theory: RepresentationTheory,
    irreps: tuple[Irrep, ...],
    output_irrep: Irrep,
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
    return output_irrep in current


def _rank_select_candidates(
    make_batches: Callable[[int], Iterable[tuple[_T, ...]]],
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
            make_batches(random_seed + attempt),
            attempt_evaluator(attempt, num_probes),
            dimension,
            num_probes * output_dimension,
            modulus,
        )
        if len(selected) == dimension:
            return selected

    raise RuntimeError(error_message(last_rank))


@cache
def symmetrized_power_basis(
    theory: RepresentationTheory,
    irrep: Irrep,
    degree: int,
    output_irrep: Irrep,
    partition: Partition,
    random_seed: int,
    antisymmetric: bool,
    modulus: int,
) -> tuple[TensorTrain, ...]:
    """Select a tensor-train basis for a single-row or single-column Schur part."""
    validate_modulus(modulus, max_degree=degree, allow_complex=False)
    dimension = _constituent_multiplicity(
        theory.schur_power_constituent_irreps(irrep, partition),
        output_irrep,
    )
    if dimension <= 0:
        return ()
    if degree == 0:
        return ((),) if dimension == 1 else ()

    irreps = (irrep,) * degree
    output_dimension = theory.irrep_dimension(output_irrep)

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
            return evaluate_power_basis_batch(
                theory,
                batch,
                probe_vectors,
                modulus,
                antisymmetric,
            )

        return evaluate_batch

    kind = "exterior" if antisymmetric else "symmetric"
    return _rank_select_candidates(
        lambda seed: stream_batches(
            _stream_tensor_product_basis(
                theory, irreps, output_irrep, np.random.default_rng(seed)
            )
        ),
        dimension,
        output_dimension,
        random_seed,
        modulus,
        attempt_evaluator,
        lambda rank: (
            f"rank probes found {rank} {kind}-power basis elements "
            f"for irrep={irrep}, degree={degree}, output_irrep={output_irrep}; "
            f"expected {dimension}"
        ),
    )


def _rank_select_schur_power_candidates(
    theory: RepresentationTheory,
    irrep: Irrep,
    partition: Partition,
    output_irrep: Irrep,
    candidates: tuple[TensorTree, ...],
    dimension: int,
    random_seed: int,
    modulus: int,
) -> tuple[TensorTree, ...]:
    if dimension <= 0:
        return ()

    output_dimension = theory.irrep_dimension(output_irrep)

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
        lambda seed: shuffled_stream_batches(candidates, seed),
        dimension,
        output_dimension,
        random_seed,
        modulus,
        attempt_evaluator,
        lambda rank: (
            f"rank probes found {rank} Schur-power basis elements "
            f"for irrep={irrep}, partition={partition}, output_irrep={output_irrep}; "
            f"expected {dimension}"
        ),
    )


@cache
def schur_functor_basis(
    theory: RepresentationTheory,
    irrep: Irrep,
    partition: Partition,
    output_irrep: Irrep,
    random_seed: int,
    modulus: int,
) -> tuple[TensorTree, ...]:
    """Assemble an abstract tensor-tree basis for one Schur-power isotypic part.

    The abstract layer builds the same tensor-tree search space for every
    reductive group. It then selects independent candidates using random
    probes over the requested arithmetic mode and the concrete group's binary
    coupling tensors.
    """
    validate_modulus(modulus, max_degree=sum(partition), allow_complex=False)
    if not partition:
        # The degree-0 Schur functor is the trivial 1-dim space: it contributes
        # one (empty-train, single-empty-leaf) basis element iff ``output_irrep``
        # occurs in the trivial coupling, where the multiplicity is necessarily
        # 0 or 1.
        return (
            (TensorTree((), ((),)),)
            if _constituent_multiplicity(
                theory.schur_power_constituent_irreps(irrep, ()),
                output_irrep,
            )
            else ()
        )
    if len(partition) == 1 or partition[0] == 1:
        # Single-row (symmetric power) or single-column (exterior power). The
        # ``(1,)`` overlap stays in the row branch via ``len(partition) != 1``.
        is_column = len(partition) != 1
        degree = len(partition) if is_column else partition[0]
        return tuple(
            TensorTree((), (tensor_train,))
            if is_column
            else TensorTree(tensor_train, ((),) * degree)
            for tensor_train in symmetrized_power_basis(
                theory,
                irrep,
                degree,
                output_irrep,
                partition,
                random_seed,
                is_column,
                modulus,
            )
        )

    dimension = _constituent_multiplicity(
        theory.schur_power_constituent_irreps(irrep, partition),
        output_irrep,
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
        if not _has_tensor_product_constituent(theory, intermediate_irreps, output_irrep):
            continue
        interior_tensor_trains = tensor_product_basis(
            theory,
            intermediate_irreps,
            output_irrep,
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
        output_irrep,
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
            leaf.semistandard_young_tableaux,
        )
        for axis_length in (len(tensor_trees), len(tableaux))
    )
    return (len(leaf.interior_tensor_trains), *input_axes)


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
                semistandard_young_tableaux=tuple(
                    (choices[index],)
                    for choices, index in zip(
                        leaf.semistandard_young_tableaux,
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
    "extract",
)
