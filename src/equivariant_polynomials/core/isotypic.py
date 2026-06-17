"""Streamed construction of isotypic data blocks."""

from __future__ import annotations

from collections.abc import Iterator, Sequence
from dataclasses import dataclass
from itertools import product
from random import Random
from typing import TypeVar

from .bases import _constituent_multiplicity, tensor_product_basis
from .combinatorics import (
    integer_partitions,
    semistandard_young_tableaux,
    weak_compositions,
)
from .protocols import RepresentationTheory
from .types import Irrep, Partition, SSYT, TensorTrain

_T = TypeVar("_T")


@dataclass(frozen=True, slots=True)
class _IsotypicBlock:
    multidegree: tuple[int, ...]
    partitions: tuple[Partition, ...]
    intermediate_irreps: tuple[Irrep, ...]
    interior_tensor_trains: tuple[TensorTrain, ...]
    schur_dimensions: tuple[int, ...]
    semi_standard_young_tableaux: tuple[tuple[SSYT, ...], ...]


def stream_isotypic_data_tree(
    theory: RepresentationTheory,
    input_irreps: tuple[Irrep, ...],
    input_multiplicities: tuple[int, ...],
    output_irrep: Irrep,
    degree: int,
    *,
    multidegree: tuple[int, ...] | None = None,
    random_seed: int,
) -> Iterator[_IsotypicBlock]:
    """Yield streamed isotypic blocks for one degree or fixed multidegree."""
    _validate_metadata(input_irreps, input_multiplicities, degree)
    multidegrees = (
        (_validate_multidegree(input_irreps, degree, multidegree),)
        if multidegree is not None
        else weak_compositions(degree, len(input_irreps))
    )
    rng = Random(random_seed)

    for current_multidegree in _shuffled(multidegrees, rng):
        partition_options = tuple(
            integer_partitions(
                input_degree,
                max_length=min(
                    theory.irrep_dimension(input_irrep),
                    input_multiplicity,
                ),
            )
            for input_degree, input_irrep, input_multiplicity in zip(
                current_multidegree,
                input_irreps,
                input_multiplicities,
            )
        )

        for partitions in _shuffled_product(partition_options, rng):
            constituent_options = tuple(
                theory.schur_power_constituent_irreps(input_irrep, partition)
                for input_irrep, partition in zip(input_irreps, partitions)
            )
            intermediate_options = tuple(
                tuple(constituent for constituent, _multiplicity in constituents)
                for constituents in constituent_options
            )

            for intermediate_irreps in _shuffled_product(intermediate_options, rng):
                interior_tensor_trains = tensor_product_basis(
                    theory,
                    intermediate_irreps,
                    output_irrep,
                )
                if not interior_tensor_trains:
                    continue

                yield _IsotypicBlock(
                    multidegree=current_multidegree,
                    partitions=partitions,
                    intermediate_irreps=intermediate_irreps,
                    interior_tensor_trains=interior_tensor_trains,
                    schur_dimensions=tuple(
                        _constituent_multiplicity(constituents, intermediate_irrep)
                        for constituents, intermediate_irrep in zip(
                            constituent_options,
                            intermediate_irreps,
                        )
                    ),
                    semi_standard_young_tableaux=tuple(
                        semistandard_young_tableaux(
                            partition,
                            input_multiplicity,
                        )
                        for partition, input_multiplicity in zip(
                            partitions,
                            input_multiplicities,
                        )
                    ),
                )


def _validate_metadata(
    input_irreps: tuple[Irrep, ...],
    input_multiplicities: tuple[int, ...],
    degree: int,
) -> None:
    if not input_irreps:
        raise ValueError("input_irreps must be nonempty")
    if len(input_irreps) != len(input_multiplicities):
        raise ValueError("input_irreps and input_multiplicities must have equal length")
    if any(multiplicity <= 0 for multiplicity in input_multiplicities):
        raise ValueError("input multiplicities must be positive")
    if degree < 0:
        raise ValueError("degree must be nonnegative")


def _validate_multidegree(
    input_irreps: tuple[Irrep, ...],
    degree: int,
    multidegree: tuple[int, ...],
) -> tuple[int, ...]:
    if len(multidegree) != len(input_irreps):
        raise ValueError("multidegree must have one entry per input irrep")
    if any(input_degree < 0 for input_degree in multidegree):
        raise ValueError("multidegree entries must be nonnegative")
    if sum(multidegree) != degree:
        raise ValueError("multidegree entries must sum to degree")
    return multidegree


def _shuffled(
    items: Sequence[_T],
    rng: Random,
) -> tuple[_T, ...]:
    out = list(items)
    rng.shuffle(out)
    return tuple(out)


def _shuffled_product(
    options: tuple[Sequence[_T], ...],
    rng: Random,
) -> Iterator[tuple[_T, ...]]:
    yield from product(*(_shuffled(option, rng) for option in options))


__all__ = ("stream_isotypic_data_tree",)
