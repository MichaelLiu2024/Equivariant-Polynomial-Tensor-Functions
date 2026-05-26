"""Protocols implemented by concrete group representation backends."""

from __future__ import annotations

from typing import Protocol

import numpy as np

from .types import Irrep, Partition, TensorTrainCore


class RepresentationTheory(Protocol):
    """Contract supplied by a concrete group implementation."""

    def irrep_dimension(
        self,
        irrep: Irrep,
    ) -> int: ...

    def tensor_product_constituent_irreps(
        self,
        left: Irrep,
        right: Irrep,
    ) -> tuple[tuple[Irrep, int], ...]: ...

    def schur_power_constituent_irreps(
        self,
        irrep: Irrep,
        partition: Partition,
    ) -> tuple[tuple[Irrep, int], ...]: ...

    def clebsch_gordan_tensor(
        self,
        core: TensorTrainCore,
    ) -> np.ndarray: ...


__all__ = ("RepresentationTheory",)
