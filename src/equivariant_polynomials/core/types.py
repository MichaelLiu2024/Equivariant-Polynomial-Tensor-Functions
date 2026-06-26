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
    output: Irrep
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
    """One materialized isotypic basis block, ready to evaluate.

    Produced from an unmaterialized plan (``_IsotypicBlock``) once its Schur
    functors are realized as concrete tensor trees. It keeps only what
    evaluation reads: the interior tensor-train couplings, the per-input-axis
    materialized tensor trees, and the tableau choices for one product block of
    basis columns. The plan's bookkeeping fields (multidegree, partitions, and
    intermediate irreps) are consumed during materialization and not retained.
    """

    interior_tensor_trains: tuple[TensorTrain, ...]
    leaf_tensor_trees: tuple[tuple[TensorTree, ...], ...]
    semistandard_young_tableaux: tuple[tuple[SSYT, ...], ...]


__all__ = (
    "Partition",
    "Irrep",
    "SSYT",
    "TensorTrainCore",
    "TensorTrain",
    "TensorTree",
    "IsotypicLeaf",
)
