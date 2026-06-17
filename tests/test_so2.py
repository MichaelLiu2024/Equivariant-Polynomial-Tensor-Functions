from __future__ import annotations

import numpy as np
import math

from equivariant_polynomials import (
    SO2RepresentationTheory,
    TensorTrainCore,
    hilbert_series_so2,
    stream_isotypic_data_tree,
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
    core = TensorTrainCore(2, -3, -1, 1)
    invalid_core = TensorTrainCore(2, -3, 0, 1)
    integer = theory.clebsch_gordan_tensor(core, 7)
    tensor = theory.clebsch_gordan_tensor(core, 0)
    invalid = theory.clebsch_gordan_tensor(invalid_core, 0)

    assert integer.shape == (1, 1, 1)
    assert integer.dtype == np.uint64
    assert integer.flags.writeable is False
    assert tensor.shape == (1, 1, 1)
    assert tensor.dtype == np.complex128
    assert invalid.dtype == np.complex128
    assert tensor.flags.writeable is False
    assert theory.clebsch_gordan_tensor(core, 7) is integer
    assert theory.clebsch_gordan_tensor(core, 0) is tensor
    assert np.array_equal(integer, np.ones((1, 1, 1), dtype=np.uint64))
    assert np.array_equal(tensor, np.ones((1, 1, 1), dtype=np.complex128))
    assert np.array_equal(invalid, np.zeros((1, 1, 1), dtype=np.complex128))


def test_hilbert_series_counts_weighted_monomials() -> None:
    assert hilbert_series_so2((1, -1), (2, 1), 0, 4) == (1, 0, 2, 0, 3)
    assert hilbert_series_so2((1, -1), (2, 1), 1, 3) == (0, 2, 0, 3)


def test_isotypic_dimensions_match_so2_hilbert_series() -> None:
    theory = SO2RepresentationTheory()

    assert _streamed_space_dimensions(
        theory,
        input_irreps=(1, -1),
        input_multiplicities=(2, 1),
        output_irrep=0,
        max_degree=4,
        random_seed=0,
    ) == hilbert_series_so2(
        (1, -1),
        (2, 1),
        0,
        4,
    )
    assert _streamed_space_dimensions(
        theory,
        input_irreps=(1, -1),
        input_multiplicities=(2, 1),
        output_irrep=1,
        max_degree=3,
        random_seed=0,
    ) == hilbert_series_so2(
        (1, -1),
        (2, 1),
        1,
        3,
    )


def _streamed_space_dimensions(
    theory: SO2RepresentationTheory,
    *,
    input_irreps,
    input_multiplicities,
    output_irrep,
    max_degree: int,
    random_seed: int,
) -> tuple[int, ...]:
    return tuple(
        _source_space_dimension(
            tuple(
                stream_isotypic_data_tree(
                    theory,
                    input_irreps,
                    input_multiplicities,
                    output_irrep,
                    degree,
                    random_seed=random_seed,
                )
            )
        )
        for degree in range(max_degree + 1)
    )


def _source_space_dimension(sources) -> int:
    return sum(
        len(source.interior_tensor_trains)
        * math.prod(
            schur_dimension * len(tableaux)
            for schur_dimension, tableaux in zip(
                source.schur_dimensions,
                source.semi_standard_young_tableaux,
            )
        )
        for source in sources
    )
