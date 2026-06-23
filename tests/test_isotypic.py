from __future__ import annotations

import pytest

from equivariant_polynomials import (
    SO3RepresentationTheory,
    hilbert_series_so3,
    stream_isotypic_data_tree,
)


def test_isotypic_dimensions_match_so3_hilbert_series(
    streamed_space_dimensions,
) -> None:
    theory = SO3RepresentationTheory()

    assert streamed_space_dimensions(
        theory,
        input_irreps=(1,),
        input_multiplicities=(1,),
        output_irrep=0,
        max_degree=3,
        random_seed=0,
    ) == hilbert_series_so3((1,), (1,), 0, 3)


def test_stream_isotypic_data_tree_streams_fixed_multidegree(
    source_space_dimension,
) -> None:
    theory = SO3RepresentationTheory()
    sources = tuple(
        stream_isotypic_data_tree(
            theory,
            input_irreps=(1,),
            input_multiplicities=(1,),
            output_irrep=0,
            multidegree=(2,),
            random_seed=0,
        )
    )

    assert source_space_dimension(sources) == 1
    assert all(source.multidegree == (2,) for source in sources)
    assert all(not hasattr(source, "degree") for source in sources)


def test_stream_isotypic_data_tree_rejects_wrong_multidegree_length() -> None:
    theory = SO3RepresentationTheory()

    with pytest.raises(ValueError, match="one entry per input irrep"):
        tuple(
            stream_isotypic_data_tree(
                theory,
                input_irreps=(1,),
                input_multiplicities=(1,),
                output_irrep=0,
                multidegree=(1, 1),
                random_seed=0,
            )
        )


def test_stream_isotypic_data_tree_rejects_invalid_metadata() -> None:
    theory = SO3RepresentationTheory()

    with pytest.raises(ValueError, match="entries must be nonnegative"):
        tuple(
            stream_isotypic_data_tree(
                theory,
                input_irreps=(1,),
                input_multiplicities=(1,),
                output_irrep=0,
                multidegree=(-1,),
                random_seed=0,
            )
        )
