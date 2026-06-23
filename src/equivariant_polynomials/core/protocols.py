"""Protocols implemented by concrete group representation backends."""

from __future__ import annotations

from typing import Protocol

import numpy as np

from .types import Irrep, Partition, TensorTrainCore


class RepresentationTheory(Protocol):
    """Minimal representation-theory contract used by the abstract algorithms.

    Concrete backends own the meaning of ``Irrep`` labels. The abstract layer
    only asks for dimensions, decomposition rules, and Clebsch-Gordan tensors
    for specific binary tensor-product couplings.
    """

    trivial_irrep: Irrep
    """Irrep label for the one-dimensional trivial representation."""

    def irrep_dimension(
        self,
        irrep: Irrep,
    ) -> int:
        """Return the vector-space dimension of ``irrep``."""
        ...

    def tensor_product_constituent_irreps(
        self,
        left: Irrep,
        right: Irrep,
    ) -> tuple[tuple[Irrep, int], ...]:
        """Return constituents of ``left`` tensor ``right``.

        Each result is ``(constituent_irrep, multiplicity_count)``. Multiplicity
        counts are one-based in tensor-train cores: a count of ``m`` makes
        multiplicity labels ``1`` through ``m`` valid for that constituent.
        """
        ...

    def schur_power_constituent_irreps(
        self,
        irrep: Irrep,
        partition: Partition,
    ) -> tuple[tuple[Irrep, int], ...]:
        """Return constituents of the Schur functor indexed by ``partition``.

        Each result is ``(constituent_irrep, multiplicity_count)``.
        """
        ...

    def clebsch_gordan_tensor(
        self,
        core: TensorTrainCore,
        modulus: int,
    ) -> np.ndarray:
        """Return the binary coupling tensor selected by ``core`` and ``modulus``."""
        ...


__all__ = ("RepresentationTheory",)
