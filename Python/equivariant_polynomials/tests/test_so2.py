from __future__ import annotations

import numpy as np

from equivariant_polynomials import (
    SO2RepresentationTheory,
    TensorTrainCore,
    build_isotypic_data_trees_by_degree,
    hilbert_series_so2,
    space_dimensions,
)


def test_tensor_product_constituent_irreps_add_weights() -> None:
    assert SO2RepresentationTheory.tensor_product_constituent_irreps(-2, 5) == (
        (3, 1),
    )


def test_schur_power_constituent_irreps_are_row_only() -> None:
    assert SO2RepresentationTheory.schur_power_constituent_irreps(3, ()) == (
        (0, 1),
    )
    assert SO2RepresentationTheory.schur_power_constituent_irreps(3, (2,)) == (
        (6, 1),
    )
    assert SO2RepresentationTheory.schur_power_constituent_irreps(3, (1, 1)) == ()


def test_clebsch_gordan_tensor_is_scalar_weight_match() -> None:
    theory = SO2RepresentationTheory()
    tensor = theory.clebsch_gordan_tensor(TensorTrainCore(2, -3, -1, 1))
    invalid = theory.clebsch_gordan_tensor(TensorTrainCore(2, -3, 0, 1))

    assert tensor.shape == (1, 1, 1)
    assert tensor.dtype == np.complex128
    assert invalid.dtype == np.complex128
    assert tensor.flags.writeable is False
    assert np.array_equal(tensor, np.ones((1, 1, 1), dtype=np.complex128))
    assert np.array_equal(invalid, np.zeros((1, 1, 1), dtype=np.complex128))


def test_hilbert_series_counts_weighted_monomials() -> None:
    assert hilbert_series_so2((1, -1), (2, 1), 0, 4) == (1, 0, 2, 0, 3)
    assert hilbert_series_so2((1, -1), (2, 1), 1, 3) == (0, 2, 0, 3)


def test_isotypic_dimensions_match_so2_hilbert_series() -> None:
    theory = SO2RepresentationTheory()
    invariant_trees = build_isotypic_data_trees_by_degree(
        theory,
        input_irreps=(1, -1),
        input_multiplicities=(2, 1),
        output_irrep=0,
        max_degree=4,
        random_seed=0,
        modulus=61,
    )
    covariant_trees = build_isotypic_data_trees_by_degree(
        theory,
        input_irreps=(1, -1),
        input_multiplicities=(2, 1),
        output_irrep=1,
        max_degree=3,
        random_seed=0,
        modulus=13,
    )

    assert space_dimensions(invariant_trees) == hilbert_series_so2(
        (1, -1),
        (2, 1),
        0,
        4,
    )
    assert space_dimensions(covariant_trees) == hilbert_series_so2(
        (1, -1),
        (2, 1),
        1,
        3,
    )
