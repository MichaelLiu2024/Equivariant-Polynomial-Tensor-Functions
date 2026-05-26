"""Low-level combinatorial and finite-field utilities."""

from __future__ import annotations

import math
from bisect import bisect_right
from itertools import accumulate

import numpy as np
import sympy as sp
from sympy.utilities.iterables import partitions
from flint import nmod_mat

from .types import Partition, SSYT

def integer_partitions(
    d: int,
    max_part: int | None = None,
    max_length: int | None = None,
) -> tuple[Partition, ...]:
    """Integer partitions of ``d`` as weakly decreasing tuples of parts."""

    return tuple(
        tuple(
            part
            for part, multiplicity in sorted(partition.items(), reverse=True)
            for _ in range(multiplicity)
        )
        for partition in partitions(d, m=max_length, k=max_part)
    )

def conjugate_partition(
    partition: Partition,
) -> Partition:
    """Transpose a partition represented by its row lengths."""
    if not partition:
        return ()
    return tuple(
        sum(1 for row_len in partition if j < row_len)
        for j in range(max(partition))
    )

def weak_compositions(
    n: int,
    k: int,
) -> tuple[tuple[int, ...], ...]:
    """Return ``k`` nonnegative parts summing to ``n`` in lexicographic order."""
    if k == 0:
        if n == 0:
            return ((),)
        return ()
    if k == 1:
        return ((n,),)
    return tuple(
        (first, *rest)
        for first in range(n + 1)
        for rest in weak_compositions(n - first, k - 1)
    )

def next_unit_prime_mod(
    m: int,
) -> int:
    """Smallest prime congruent to 1 modulo ``m``."""
    step = 2 * m if (m % 2 == 1 and m > 1) else m
    x = 1
    while True:
        x += step
        if sp.isprime(x):
            return x

def waring_modulus_lcm(
    degree: int,
) -> int:
    """Root-of-unity divisibility needed for Waring grids up to ``degree``."""
    if degree < 0:
        raise ValueError("degree must be nonnegative")
    return math.lcm(*range(1, degree + 2))

def suggest_prime_modulus(
    degree: int,
) -> int:
    """Suggest the historical prime modulus compatible with grids through ``degree``."""
    return next_unit_prime_mod(waring_modulus_lcm(degree))

def validate_modulus(
    modulus: int,
) -> int:
    """Validate the package convention: ``0`` for characteristic zero, or a prime."""
    if modulus == 0:
        return 0
    if not sp.isprime(modulus):
        raise ValueError("modulus must be 0 or prime")
    return modulus

def validate_waring_modulus(
    modulus: int,
    degree: int,
) -> int:
    """Validate that ``modulus`` has the roots used by Waring grids to ``degree``."""
    modulus = validate_modulus(modulus)
    if modulus != 0 and (modulus - 1) % waring_modulus_lcm(degree) != 0:
        raise ValueError(
            "prime modulus must be congruent to 1 modulo lcm(1, ..., degree + 1)"
        )
    return modulus

def cond_mod(
    x: np.ndarray,
    modulus: int,
) -> np.ndarray:
    if not sp.isprime(modulus):
        return x
    return np.remainder(x, modulus, out=x) if x.flags.writeable else x % modulus

def ragged_multi_index(
    linear_indices: tuple[int, ...],
    dimensions: tuple[int, ...],
) -> tuple[tuple[int, int], ...]:
    """Convert 0-based linear indices into ragged 0-based index pairs."""
    acc = tuple(accumulate((0, *dimensions)))
    if linear_indices and (
        min(linear_indices) < 0 or max(linear_indices) >= acc[-1]
    ):
        raise IndexError(f"ragged indices outside total dimension {acc[-1]}")

    out = []
    for linear_index in linear_indices:
        block_index = bisect_right(acc, linear_index) - 1
        out.append((block_index, linear_index - acc[block_index]))
    return tuple(out)

def pivot_columns(
    A: np.ndarray,
    modulus: int
) -> tuple[int, ...]:
    if not sp.isprime(modulus):
        return sp.Matrix(A).rref()[1]
    M = nmod_mat(*A.shape, A.ravel().tolist(), modulus)
    R, rank = M.rref(inplace=True)

    num_cols = A.shape[1]
    return tuple(
        next(j for j in range(num_cols) if R[i, j])
        for i in range(rank)
    )

def row_kronecker_product(
    A: np.ndarray,
    B: np.ndarray,
    modulus: int,
):
    """Row-wise Kronecker product with vector and basis axes preserved.

    For syndrome arrays representing pointwise products in
    the invariant algebra tensor the covariant module, inputs shaped
    ``(probe, vector, columns)`` produce
    ``(probe, vector_A*vector_B, columns_A*columns_B)``.
    """
    out = (A[:, :, None, :, None] * B[:, None, :, None, :]).reshape(
        A.shape[0], A.shape[1] * B.shape[1], A.shape[2] * B.shape[2]
    )
    return cond_mod(out, modulus)

def semistandard_young_tableaux(
    partition: Partition,
    max_entry: int,
) -> tuple[SSYT, ...]:
    """Row-weak / column-strict tableau basis data with 0-based entries."""
    shape = partition
    if not shape:
        return (SSYT((), ()),)
    if max_entry <= 0 or len(shape) > max_entry:
        return ()

    starts = (0, *accumulate(shape[:-1]))
    n = sum(shape)

    left, above, hi = [-1] * n, [-1] * n, [max_entry] * n
    column_heights = conjugate_partition(shape)
    for i, row_len in enumerate(shape):
        start = starts[i]
        for j in range(row_len):
            pos = start + j
            left[pos] = pos - 1 if j else -1
            above[pos] = starts[i - 1] + j if i and j < shape[i - 1] else -1
            hi[pos] = max_entry - (column_heights[j] - i - 1)

    rows = tuple(
        tuple(starts[i] + j for j in range(row_len))
        for i, row_len in enumerate(shape)
    )

    vals = [0] * n
    out: list[SSYT] = []

    def emit() -> None:
        entries_by_row, copies_by_row = [], []

        for row in rows:
            it = iter(row)
            prev, count = vals[next(it)], 1
            entries, copies = [], []

            for pos in it:
                v = vals[pos]
                if v == prev:
                    count += 1
                else:
                    entries.append(prev)
                    copies.append(count)
                    prev, count = v, 1

            entries.append(prev)
            copies.append(count)
            entries_by_row.append(tuple(entries))
            copies_by_row.append(tuple(copies))

        out.append(SSYT(tuple(entries_by_row), tuple(copies_by_row)))

    def fill(pos: int) -> None:
        if pos == n:
            emit()
            return

        lp, ap = left[pos], above[pos]
        lo = vals[lp] if lp >= 0 else 0
        if ap >= 0 and vals[ap] + 1 > lo:
            lo = vals[ap] + 1

        for v in range(lo, hi[pos]):
            vals[pos] = v
            fill(pos + 1)

    fill(0)
    return tuple(out)


__all__ = (
    "Partition",
    "SSYT",
    "integer_partitions",
    "weak_compositions",
    "conjugate_partition",
    "cond_mod",
    "next_unit_prime_mod",
    "waring_modulus_lcm",
    "suggest_prime_modulus",
    "validate_modulus",
    "validate_waring_modulus",
    "ragged_multi_index",
    "pivot_columns",
    "row_kronecker_product",
    "semistandard_young_tableaux",
)
