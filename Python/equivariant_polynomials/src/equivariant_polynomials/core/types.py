"""Shared type aliases and immutable data containers."""

from __future__ import annotations

from dataclasses import dataclass

from typing import Any


Partition = tuple[int, ...]


@dataclass(frozen=True, slots=True)
class SSYT:
    entries_by_row: tuple[tuple[int, ...], ...]
    copies_by_row: tuple[tuple[int, ...], ...]


Irrep = Any


Multiplicity = Any


@dataclass(frozen=True, slots=True)
class TensorTrainCore:
    left: Irrep
    right: Irrep
    out: Irrep
    multiplicity: Multiplicity


TensorTrain = tuple[TensorTrainCore, ...]


@dataclass(frozen=True, slots=True)
class TensorTree:
    interior_tensor_train: TensorTrain
    leaf_tensor_trains: tuple[TensorTrain, ...]


@dataclass(frozen=True, slots=True)
class IsotypicLeaf:
    multidegree: tuple[int, ...]
    partitions: tuple[Partition, ...]
    intermediate_irreps: tuple[Irrep, ...]
    interior_tensor_trains: tuple[TensorTrain, ...]
    leaf_tensor_trees: tuple[tuple[TensorTree, ...], ...]
    semi_standard_young_tableaux: tuple[tuple[SSYT, ...], ...]


@dataclass(frozen=True, slots=True)
class IsotypicDataTree:
    input_irreps: tuple[Irrep, ...]
    input_multiplicities: tuple[int, ...]
    output_irrep: Irrep
    degree: int
    isotypic_leaves: tuple[IsotypicLeaf, ...]


__all__ = (
    "Partition",
    "SSYT",
    "Irrep",
    "Multiplicity",
    "TensorTrainCore",
    "TensorTrain",
    "TensorTree",
    "IsotypicLeaf",
    "IsotypicDataTree",
)
