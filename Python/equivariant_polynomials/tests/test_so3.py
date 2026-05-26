from __future__ import annotations

import numpy as np

from equivariant_polynomials.core.evaluators import (
    evaluate_antisymmetrized_tensor_train,
    evaluate_tensor_train,
    evaluate_young_symmetrized_tensor_tree,
    monomial_waring_grid,
    sample_isotypic_input_probes,
)
from equivariant_polynomials.core.types import SSYT, TensorTrainCore, TensorTree
from equivariant_polynomials.groups.so3 import (
    SO3RepresentationTheory,
    hilbert_series_so3,
)


def test_tensor_product_constituent_irreps_for_two_vectors() -> None:
    assert SO3RepresentationTheory.tensor_product_constituent_irreps(1, 1) == (
        (0, 1),
        (1, 1),
        (2, 1),
    )


def test_schur_power_constituent_irreps_for_vector_squares() -> None:
    assert SO3RepresentationTheory.schur_power_constituent_irreps(1, (2,)) == (
        (0, 1),
        (2, 1),
    )
    assert SO3RepresentationTheory.schur_power_constituent_irreps(1, (1, 1)) == (
        (1, 1),
    )


def test_clebsch_gordan_tensor_shape_and_cache_contract() -> None:
    theory = SO3RepresentationTheory()
    core = TensorTrainCore(1, 1, 0, 1)
    tensor = theory.clebsch_gordan_tensor(core)

    assert tensor.shape == (3, 3, 1)
    assert tensor.dtype == np.complex128
    assert tensor.flags.writeable is False
    assert theory.clebsch_gordan_tensor(core) is tensor
    expected_tensor = np.asarray(
        [[[0], [0], [4]], [[0], [-2], [0]], [[4], [0], [0]]],
        dtype=np.complex128,
    )
    assert np.array_equal(tensor, expected_tensor)
    expected_modular_tensor = np.asarray(
        [[[0], [0], [4]], [[0], [5], [0]], [[4], [0], [0]]],
        dtype=np.uint64,
    )
    reduced_tensor = np.remainder(tensor.real, 7).astype(np.uint64)
    assert np.array_equal(reduced_tensor, expected_modular_tensor)


def test_batch_multi_appends_factor_axes_in_tensor_train_order() -> None:
    theory = SO3RepresentationTheory()
    modulus = 17
    core = TensorTrainCore(1, 1, 0, 1)

    for left_size, right_size in ((3, 4), (5, 2)):
        left = (
            np.arange(2 * left_size * 3, dtype=np.uint64).reshape(2, left_size, 3)
            % modulus
        )
        right = (
            np.arange(2 * right_size * 3, dtype=np.uint64).reshape(2, right_size, 3)
            % modulus
        )

        value = evaluate_tensor_train(
            theory,
            (core,),
            (left, right),
            modulus,
            "batch_multi",
        )
        expected = (
            np.einsum(
                "pai,pbj,ijk->pabk",
                left,
                right,
                np.asarray(
                    [[[0], [0], [4]], [[0], [15], [0]], [[4], [0], [0]]],
                    dtype=np.uint64,
                ),
            )
            % modulus
        )

        assert value.shape == (2, left_size, right_size, 1)
        assert value.dtype == np.uint64
        assert np.array_equal(value, expected)


def test_antisymmetrized_batch_multi_reorders_permuted_factor_axes() -> None:
    theory = SO3RepresentationTheory()
    modulus = 17
    core = TensorTrainCore(1, 1, 0, 1)
    left = np.arange(2 * 3 * 3, dtype=np.uint64).reshape(2, 3, 3) % modulus
    right = np.arange(2 * 4 * 3, dtype=np.uint64).reshape(2, 4, 3) % modulus

    value = evaluate_antisymmetrized_tensor_train(
        theory,
        (core,),
        (left, right),
        modulus,
        "batch_multi",
    )
    forward = evaluate_tensor_train(
        theory,
        (core,),
        (left, right),
        modulus,
        "batch_multi",
    )
    swapped = evaluate_tensor_train(
        theory,
        (core,),
        (right, left),
        modulus,
        "batch_multi",
    ).transpose(0, 2, 1, 3)

    assert value.shape == (2, 3, 4, 1)
    assert value.dtype == np.uint64
    assert np.array_equal(value, (forward + modulus - swapped) % modulus)


def test_isotypic_input_probes_are_probe_first() -> None:
    theory = SO3RepresentationTheory()

    probes = sample_isotypic_input_probes(
        theory,
        input_irreps=(1, 2),
        input_multiplicities=(2, 3),
        num_probes=5,
        modulus=17,
        random_seed=0,
    )

    assert tuple(probe.shape for probe in probes) == ((5, 2, 3), (5, 3, 5))


def test_young_symmetrized_tensor_tree_preserves_probe_first_layout() -> None:
    theory = SO3RepresentationTheory()
    modulus = 17
    probe_batches = np.arange(2 * 3 * 4, dtype=np.uint64).reshape(2, 3, 4)
    ssyt = SSYT(((0, 2),), ((1, 1),))

    value = evaluate_young_symmetrized_tensor_tree(
        theory,
        TensorTree((), ((),)),
        ssyt,
        probe_batches,
        modulus,
    )
    grid = monomial_waring_grid((1, 1), modulus)
    sym = np.einsum("rk,pkv->prv", grid, probe_batches[:, (0, 2), :]) % modulus
    coeff = np.prod(grid, axis=1, dtype=np.uint64) % modulus
    expected = np.tensordot(sym, coeff, axes=([1], [0])) % modulus

    assert value.shape == (2, 4)
    assert np.array_equal(value, expected)


def test_monomial_waring_grid_omits_minimal_power() -> None:
    modulus = 7
    powers = (2, 1)
    x = np.asarray([3, 5], dtype=np.uint64)
    grid = monomial_waring_grid(powers, modulus)
    coeff = np.prod(grid, axis=1, dtype=np.uint64) % modulus
    value = np.sum(coeff * ((grid @ x) % modulus) ** sum(powers)) % modulus
    expected = (3 * 3 * (3**2) * 5) % modulus

    assert np.array_equal(grid[:, 1], np.ones(grid.shape[0], dtype=np.uint64))
    assert value == expected


def test_complex_monomial_waring_grid_uses_roots_of_unity() -> None:
    powers = (2, 1)
    x = np.asarray([3, 5], dtype=np.complex128)
    grid = monomial_waring_grid(powers, 0)
    coeff = np.prod(grid, axis=1)
    value = np.sum(coeff * ((grid @ x) ** sum(powers)))
    expected = 3 * 3 * (3**2) * 5

    assert grid.dtype == np.complex128
    assert np.allclose(grid[:, 1], np.ones(grid.shape[0], dtype=np.complex128))
    assert np.allclose(value, expected)


def test_young_symmetrized_tensor_tree_shares_row_waring_choices() -> None:
    theory = SO3RepresentationTheory()
    modulus = 17
    probe_batches = np.asarray([[[2], [3]]], dtype=np.uint64)
    ssyt = SSYT(((0, 1),), ((1, 1),))

    value = evaluate_young_symmetrized_tensor_tree(
        theory,
        TensorTree((TensorTrainCore(0, 0, 0, 1),), ((), ())),
        ssyt,
        probe_batches,
        modulus,
    )
    expected = np.asarray([[(4 * 2 * 3) % modulus]], dtype=np.uint64)

    assert value.shape == (1, 1)
    assert np.array_equal(value, expected)


def test_young_symmetrized_tensor_tree_uses_complex_waring_grid_for_modulus_zero() -> None:
    theory = SO3RepresentationTheory()
    probe_batches = np.asarray([[[2], [3]]], dtype=np.uint64)
    ssyt = SSYT(((0, 1),), ((1, 1),))

    value = evaluate_young_symmetrized_tensor_tree(
        theory,
        TensorTree((TensorTrainCore(0, 0, 0, 1),), ((), ())),
        ssyt,
        probe_batches,
        0,
    )
    expected = np.asarray([[4 * 2 * 3]], dtype=np.complex128)

    assert value.shape == (1, 1)
    assert value.dtype == np.complex128
    assert np.allclose(value, expected)


def test_hilbert_series_for_single_vector_invariants() -> None:
    assert hilbert_series_so3((1,), (1,), 0, 3) == (1, 0, 1, 0)
