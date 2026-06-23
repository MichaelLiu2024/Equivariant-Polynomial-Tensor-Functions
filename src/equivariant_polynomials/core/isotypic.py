"""Streamed construction of isotypic data blocks."""

from __future__ import annotations

from collections.abc import Iterator, Sequence
from dataclasses import dataclass
from itertools import product
from random import Random
from typing import TypeVar

from .bases import _constituent_multiplicity, tensor_product_basis
from .combinatorics import (
    _validate_input_metadata,
    integer_partitions,
    semistandard_young_tableaux,
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
    multidegree: tuple[int, ...],
    *,
    random_seed: int,
) -> Iterator[_IsotypicBlock]:
    """Yield streamed isotypic blocks for a fixed multidegree."""
    _validate_input_metadata(
        input_irreps,
        input_multiplicities,
        degrees=multidegree,
    )
    rng = Random(random_seed)

    partition_options = tuple(
        integer_partitions(
            input_degree,
            max_length=min(
                theory.irrep_dimension(input_irrep),
                input_multiplicity,
            ),
        )
        for input_degree, input_irrep, input_multiplicity in zip(
            multidegree,
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
                multidegree=multidegree,
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


def _shuffled_product(
    options: tuple[Sequence[_T], ...],
    rng: Random,
) -> Iterator[tuple[_T, ...]]:
    shuffled_options = [list(option) for option in options]
    for option in shuffled_options:
        rng.shuffle(option)
    yield from product(*shuffled_options)


__all__ = ("stream_isotypic_data_tree",)
