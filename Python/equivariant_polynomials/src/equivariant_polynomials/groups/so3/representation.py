"""Concrete SO(3) representation-theory backend."""

from __future__ import annotations

from collections import Counter
from functools import cache
from math import comb, perm

import numpy as np

from equivariant_polynomials.core.combinatorics import semistandard_young_tableaux
from equivariant_polynomials.core.types import Partition, TensorTrainCore


class SO3RepresentationTheory:
    """Concrete SO(3) implementation."""

    @staticmethod
    def irrep_dimension(
        irrep: int,
    ) -> int:
        return 2 * irrep + 1

    @staticmethod
    def tensor_product_constituent_irreps(
        left: int,
        right: int,
    ) -> tuple[tuple[int, int], ...]:
        return tuple(
            (output, 1) for output in range(abs(left - right), left + right + 1)
        )

    @staticmethod
    @cache
    def schur_power_constituent_irreps(
        irrep: int,
        partition: Partition,
    ) -> tuple[tuple[int, int], ...]:
        weights: Counter[int] = Counter()
        for ssyt in semistandard_young_tableaux(
            partition,
            2 * irrep + 1,
        ):
            weight = sum(
                (entry - irrep) * copies
                for entries, row_copies in zip(
                    ssyt.entries_by_row,
                    ssyt.copies_by_row,
                )
                for entry, copies in zip(entries, row_copies)
            )
            weights[weight] += 1

        if not weights:
            return ()

        return tuple(
            (output, multiplicity)
            for output in range(max(weights) + 1)
            if (multiplicity := weights[output] - weights[output + 1]) > 0
        )

    @staticmethod
    @cache
    def clebsch_gordan_tensor(
        core: TensorTrainCore,
    ) -> np.ndarray:
        """Clebsch-Gordan tensor for one SO(3) tensor-product core."""
        l1 = core.left
        l2 = core.right
        l3 = core.out
        shape = (2 * l1 + 1, 2 * l2 + 1, 2 * l3 + 1)
        tensor = np.zeros(shape, dtype=np.complex128)
        r = l1 + l2 - l3
        if r >= 0:
            for m1 in range(-l1, l1 + 1):
                lo = max(-l2, -l3 - m1)
                hi = min(l2, l3 - m1)
                for m2 in range(lo, hi + 1):
                    total = 0
                    for s in range(r + 1):
                        total += (
                            (-1) ** s
                            * comb(r, s)
                            * perm(l1 + m1, r - s)
                            * perm(l1 - m1, s)
                            * perm(l2 + m2, s)
                            * perm(l2 - m2, r - s)
                        )
                    index = (l1 + m1, l2 + m2, l3 + m1 + m2)
                    tensor[index] = total

        tensor.setflags(write=False)
        return tensor


__all__ = ("SO3RepresentationTheory",)
