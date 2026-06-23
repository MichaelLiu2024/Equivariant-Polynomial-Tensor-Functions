"""Concrete SO(3) representation-theory backend."""

from __future__ import annotations

from collections import Counter
from functools import cache
from math import comb, perm

import numpy as np

from equivariant_polynomials.core.combinatorics import (
    arithmetic_dtype,
    semistandard_young_tableaux,
    validate_modulus,
)
from equivariant_polynomials.core.types import (
    Partition,
    TensorTrainCore,
)


def _clebsch_gordan_entry_mod(
    left: int,
    right: int,
    m1: int,
    m2: int,
    r: int,
    modulus: int,
) -> int:
    total = 0
    for s in range(r + 1):
        term = (
            comb(r, s)
            * perm(left + m1, r - s)
            * perm(left - m1, s)
            * perm(right + m2, s)
            * perm(right - m2, r - s)
        ) % modulus
        if s % 2:
            total = (total - term) % modulus
        else:
            total = (total + term) % modulus
    return total


def _clebsch_gordan_entry_exact(
    left: int,
    right: int,
    m1: int,
    m2: int,
    r: int,
) -> int:
    total = 0
    for s in range(r + 1):
        term = (
            comb(r, s)
            * perm(left + m1, r - s)
            * perm(left - m1, s)
            * perm(right + m2, s)
            * perm(right - m2, r - s)
        )
        total += -term if s % 2 else term
    return total


class SO3RepresentationTheory:
    """Concrete SO(3) implementation."""

    trivial_irrep = 0

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
        modulus: int,
    ) -> np.ndarray:
        """Clebsch-Gordan tensor for one SO(3) tensor-product core."""
        validate_modulus(modulus)
        left = core.left
        right = core.right
        out = core.out
        shape = (2 * left + 1, 2 * right + 1, 2 * out + 1)
        tensor = np.zeros(shape, dtype=arithmetic_dtype(modulus))
        r = left + right - out

        if modulus == 0:
            if r >= 0:
                for m1 in range(-left, left + 1):
                    lo = max(-right, -out - m1)
                    hi = min(right, out - m1)
                    for m2 in range(lo, hi + 1):
                        index = (left + m1, right + m2, out + m1 + m2)
                        tensor[index] = _clebsch_gordan_entry_exact(
                            left,
                            right,
                            m1,
                            m2,
                            r,
                        )
        elif 0 <= r <= 2 * min(left, right):
            for m1 in range(-left, left + 1):
                lo = max(-right, -out - m1)
                hi = min(right, out - m1)
                for m2 in range(lo, hi + 1):
                    index = (left + m1, right + m2, out + m1 + m2)
                    tensor[index] = _clebsch_gordan_entry_mod(
                        left,
                        right,
                        m1,
                        m2,
                        r,
                        modulus,
                    )

        tensor.setflags(write=False)
        return tensor


__all__ = ("SO3RepresentationTheory",)
