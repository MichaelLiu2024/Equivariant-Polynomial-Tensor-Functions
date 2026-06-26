from __future__ import annotations

import numpy as np
import pytest

from equivariant_polynomials.core.combinatorics import (
    conjugate_partition,
    integer_partitions,
    ragged_multi_index,
    reduce_modulo,
    row_kronecker_product,
    semistandard_young_tableaux,
    validate_modulus,
    weak_compositions,
)


def test_integer_partitions_are_decreasing() -> None:
    assert integer_partitions(3) == ((3,), (2, 1), (1, 1, 1))
    assert integer_partitions(3, max_length=2) == ((3,), (2, 1))


def test_conjugate_partition() -> None:
    assert conjugate_partition((3, 1)) == (2, 1, 1)


def test_validate_modulus_rejects_composite_modulus() -> None:
    with pytest.raises(ValueError, match="prime"):
        validate_modulus(4)


def test_reduce_modulo_reduces_nonzero_modulus() -> None:
    values = np.asarray([5, 7], dtype=np.uint64)

    assert reduce_modulo(values, 0) is values
    assert np.array_equal(reduce_modulo(values, 5), np.asarray([0, 2], dtype=np.uint64))


def test_validate_modulus_accepts_arbitrary_prime() -> None:
    validate_modulus(17)


def test_validate_modulus_requires_prime_larger_than_max_degree() -> None:
    with pytest.raises(ValueError, match="greater than max_degree"):
        validate_modulus(3, max_degree=3)

    validate_modulus(0, max_degree=3)
    validate_modulus(5, max_degree=4)


def test_row_kronecker_product_modulus_zero_does_not_reduce() -> None:
    left = np.asarray([[[3], [5]]], dtype=np.uint64)
    right = np.asarray([[[7], [11]]], dtype=np.uint64)

    value = row_kronecker_product(left, right, 0)

    assert np.array_equal(
        value,
        np.asarray([[[21], [33], [35], [55]]], dtype=np.uint64),
    )


def test_validate_modulus_rejects_complex_for_selection() -> None:
    # Complex arithmetic survives for evaluating selected generators
    # (allow_complex defaults to True) but is rejected for selection.
    validate_modulus(0)
    with pytest.raises(ValueError, match="positive prime"):
        validate_modulus(0, allow_complex=False)


def test_semistandard_young_tableaux_are_row_weak_column_strict() -> None:
    assert len(semistandard_young_tableaux((3,), 2)) == 4
    assert len(semistandard_young_tableaux((1, 1, 1), 3)) == 1


def test_weak_compositions() -> None:
    assert tuple(weak_compositions(2, 2)) == ((0, 2), (1, 1), (2, 0))


def test_ragged_multi_index() -> None:
    assert ragged_multi_index((0, 2, 4), (2, 3)) == ((0, 0), (1, 0), (1, 2))
