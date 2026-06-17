from __future__ import annotations

import math

import pytest

from equivariant_polynomials import (
    SO3RepresentationTheory,
    hilbert_series_so3,
    stream_isotypic_data_tree,
)


def test_isotypic_dimensions_match_so3_hilbert_series() -> None:
    theory = SO3RepresentationTheory()

    assert tuple(
        _streamed_space_dimension(
            theory,
            input_irreps=(1,),
            input_multiplicities=(1,),
            output_irrep=0,
            degree=degree,
            random_seed=0,
        )
        for degree in range(4)
    ) == hilbert_series_so3((1,), (1,), 0, 3)


def test_stream_isotypic_data_tree_is_single_degree() -> None:
    theory = SO3RepresentationTheory()
    sources = tuple(
        stream_isotypic_data_tree(
            theory,
            input_irreps=(1,),
            input_multiplicities=(1,),
            output_irrep=0,
            degree=2,
            random_seed=0,
        )
    )

    assert _source_space_dimension(sources) == 1
    assert all(not hasattr(source, "degree") for source in sources)


def test_stream_isotypic_data_tree_accepts_fixed_multidegree() -> None:
    theory = SO3RepresentationTheory()

    assert _source_space_dimension(
        tuple(
            stream_isotypic_data_tree(
                theory,
                input_irreps=(1,),
                input_multiplicities=(1,),
                output_irrep=0,
                degree=2,
                multidegree=(2,),
                random_seed=0,
            )
        )
    ) == 1


def test_stream_isotypic_data_tree_rejects_wrong_multidegree() -> None:
    theory = SO3RepresentationTheory()

    with pytest.raises(ValueError, match="sum to degree"):
        tuple(
            stream_isotypic_data_tree(
                theory,
                input_irreps=(1,),
                input_multiplicities=(1,),
                output_irrep=0,
                degree=2,
                multidegree=(1,),
                random_seed=0,
            )
        )


def test_stream_isotypic_data_tree_rejects_invalid_metadata() -> None:
    theory = SO3RepresentationTheory()

    with pytest.raises(ValueError, match="degree must be nonnegative"):
        tuple(
            stream_isotypic_data_tree(
                theory,
                input_irreps=(1,),
                input_multiplicities=(1,),
                output_irrep=0,
                degree=-1,
                random_seed=0,
            )
        )


def _streamed_space_dimension(
    theory: SO3RepresentationTheory,
    *,
    input_irreps,
    input_multiplicities,
    output_irrep,
    degree: int,
    random_seed: int,
) -> int:
    return _source_space_dimension(
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
