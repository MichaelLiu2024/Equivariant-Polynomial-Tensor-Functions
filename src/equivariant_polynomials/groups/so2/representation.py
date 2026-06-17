"""Concrete SO(2) representation-theory backend."""

from __future__ import annotations

from functools import cache

import numpy as np

from equivariant_polynomials.core.combinatorics import validate_modulus
from equivariant_polynomials.core.types import (
    Partition,
    TensorTrainCore,
)


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
        modulus: int,
    ) -> np.ndarray:
        """Scalar Clebsch-Gordan tensor for one SO(2) tensor-product core."""
        validate_modulus(modulus)
        value = core.out == core.left + core.right and core.multiplicity == 1
        dtype = np.complex128 if modulus == 0 else np.uint64
        tensor = np.asarray([[[value]]], dtype=dtype)
        tensor.setflags(write=False)
        return tensor


__all__ = ("SO2RepresentationTheory",)
