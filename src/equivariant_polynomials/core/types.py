"""Shared type aliases and immutable records for abstract basis data."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, TypeAlias


Partition: TypeAlias = tuple[int, ...]
"""A Young diagram, encoded by weakly decreasing row lengths."""

Irrep: TypeAlias = Any
"""Concrete irreducible-representation label supplied by a group backend."""


@dataclass(frozen=True, slots=True)
class SSYT:
    """Semistandard Young tableau data used by Young symmetrizers.

    ``entries_by_row`` stores the selected multiplicity-basis indices in each
    tableau row. ``copies_by_row`` stores their repeated-copy counts for the
    monomial Waring grid used during evaluation.
    """

    entries_by_row: tuple[tuple[int, ...], ...]
    copies_by_row: tuple[tuple[int, ...], ...]


@dataclass(frozen=True, slots=True)
class TensorTrainCore:
    """One binary Clebsch-Gordan coupling in a left-associated tensor train."""

    left: Irrep
    right: Irrep
    out: Irrep
    multiplicity: int


TensorTrain: TypeAlias = tuple[TensorTrainCore, ...]
"""A sequence of couplings representing a left-associated tensor product."""


@dataclass(frozen=True, slots=True)
class TensorTree:
    """Tensor-train tree for one Schur-functor basis element."""

    interior_tensor_train: TensorTrain
    leaf_tensor_trains: tuple[TensorTrain, ...]


@dataclass(frozen=True, slots=True)
class IsotypicLeaf:
    """One factorized basis block in an isotypic data tree.

    Each leaf fixes the input multidegree, Schur partitions, intermediate
    irreps, tensor-tree choices, and tableau choices needed to evaluate one
    product block of basis columns.
    """

    multidegree: tuple[int, ...]
    partitions: tuple[Partition, ...]
    intermediate_irreps: tuple[Irrep, ...]
    interior_tensor_trains: tuple[TensorTrain, ...]
    leaf_tensor_trees: tuple[tuple[TensorTree, ...], ...]
    semi_standard_young_tableaux: tuple[tuple[SSYT, ...], ...]


__all__ = (
    "Partition",
    "Irrep",
    "SSYT",
    "TensorTrainCore",
    "TensorTrain",
    "TensorTree",
    "IsotypicLeaf",
)
