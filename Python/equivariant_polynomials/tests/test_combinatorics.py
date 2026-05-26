from __future__ import annotations

import numpy as np
import pytest

from equivariant_polynomials.core.combinatorics import (
    cond_mod,
    conjugate_partition,
    integer_partitions,
    pivot_columns,
    ragged_multi_index,
    row_kronecker_product,
    semistandard_young_tableaux,
    suggest_prime_modulus,
    validate_waring_modulus,
    weak_compositions,
)


def test_integer_partitions_are_decreasing() -> None:
    assert integer_partitions(3) == ((3,), (2, 1), (1, 1, 1))
    assert integer_partitions(3, max_length=2) == ((3,), (2, 1))


def test_conjugate_partition() -> None:
    assert conjugate_partition((3, 1)) == (2, 1, 1)


def test_cond_mod_reduces_only_prime_moduli() -> None:
    x = np.asarray([5, 7], dtype=np.uint64)

    assert cond_mod(x, 0) is x
    assert np.array_equal(cond_mod(x, 4), np.asarray([5, 7], dtype=np.uint64))
    assert np.array_equal(cond_mod(x, 5), np.asarray([0, 2], dtype=np.uint64))


def test_suggest_prime_modulus_matches_waring_lcm_heuristic() -> None:
    assert suggest_prime_modulus(3) == 13
    assert suggest_prime_modulus(4) == 61


def test_validate_waring_modulus_rejects_incompatible_prime() -> None:
    with pytest.raises(ValueError, match="prime modulus"):
        validate_waring_modulus(17, 2)


def test_row_kronecker_product_modulus_zero_does_not_reduce() -> None:
    left = np.asarray([[[3], [5]]], dtype=np.uint64)
    right = np.asarray([[[7], [11]]], dtype=np.uint64)

    value = row_kronecker_product(left, right, 0)

    assert np.array_equal(
        value,
        np.asarray([[[21], [33], [35], [55]]], dtype=np.uint64),
    )


def test_pivot_columns_modulus_zero_uses_exact_rank() -> None:
    matrix = np.asarray([[2, 4], [1, 2]], dtype=np.uint64)

    assert pivot_columns(matrix, 0) == (0,)


def test_semistandard_young_tableaux_are_row_weak_column_strict() -> None:
    assert len(semistandard_young_tableaux((3,), 2)) == 4
    assert len(semistandard_young_tableaux((1, 1, 1), 3)) == 1


def test_weak_compositions() -> None:
    assert tuple(weak_compositions(2, 2)) == ((0, 2), (1, 1), (2, 0))


def test_ragged_multi_index() -> None:
    assert ragged_multi_index((0, 2, 4), (2, 3)) == ((0, 0), (1, 0), (1, 2))
