from __future__ import annotations

from equivariant_polynomials.core import (
    build_isotypic_data_trees_by_degree,
    extract_independent_generators,
)
from equivariant_polynomials.groups.so3 import (
    SO3RepresentationTheory,
    hilbert_series_so3,
)


def test_core_algebra_generator_extractor_accepts_abstract_dimensions() -> None:
    theory = SO3RepresentationTheory()
    invariant_trees = build_isotypic_data_trees_by_degree(
        theory,
        input_irreps=(1,),
        input_multiplicities=(1,),
        output_irrep=0,
        max_degree=3,
        random_seed=0,
        modulus=13,
    )

    generators = extract_independent_generators(
        theory,
        invariant_trees,
        invariant_trees,
        lambda dimensions, _output_dimension: dimensions,
        lambda degree: degree // 2,
        random_seed=0,
        modulus=13,
        first_generator_degree=1,
        target_dimensions_by_degree=hilbert_series_so3((1,), (1,), 0, 3),
    )

    assert tuple(map(len, generators)) == (1, 0, 1, 0)


def test_core_algebra_generator_extractor_can_count_tree_dimensions() -> None:
    theory = SO3RepresentationTheory()
    invariant_trees = build_isotypic_data_trees_by_degree(
        theory,
        input_irreps=(1,),
        input_multiplicities=(1,),
        output_irrep=0,
        max_degree=3,
        random_seed=0,
        modulus=13,
    )

    generators = extract_independent_generators(
        theory,
        invariant_trees,
        invariant_trees,
        lambda dimensions, _output_dimension: dimensions,
        lambda degree: degree // 2,
        random_seed=0,
        modulus=13,
        first_generator_degree=1,
    )

    assert tuple(map(len, generators)) == (1, 0, 1, 0)
