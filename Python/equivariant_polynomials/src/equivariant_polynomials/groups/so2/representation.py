"""Concrete SO(2) representation-theory backend."""

from __future__ import annotations

from functools import cache

import numpy as np

from equivariant_polynomials.core.types import Partition, TensorTrainCore


class SO2RepresentationTheory:
    """Concrete SO(2) implementation with integer weight labels."""

    @staticmethod
    def irrep_dimension(
        irrep: int,
    ) -> int:
        return 1

    @staticmethod
    def tensor_product_constituent_irreps(
        left: int,
        right: int,
    ) -> tuple[tuple[int, int], ...]:
        return ((left + right, 1),)

    @staticmethod
    @cache
    def schur_power_constituent_irreps(
        irrep: int,
        partition: Partition,
    ) -> tuple[tuple[int, int], ...]:
        if not partition:
            return ((0, 1),)
        if len(partition) == 1:
            return ((partition[0] * irrep, 1),)
        return ()

    @staticmethod
    @cache
    def clebsch_gordan_tensor(
        core: TensorTrainCore,
    ) -> np.ndarray:
        """Scalar Clebsch-Gordan tensor for one SO(2) tensor-product core."""
        value = core.out == core.left + core.right and core.multiplicity == 1
        out = np.asarray([[[int(value)]]], dtype=np.complex128)
        out.setflags(write=False)
        return out


__all__ = ("SO2RepresentationTheory",)
