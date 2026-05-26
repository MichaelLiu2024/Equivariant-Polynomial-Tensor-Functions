from __future__ import annotations

import pytest

from equivariant_polynomials import (
    SO3RepresentationTheory,
    build_isotypic_data_tree,
    build_isotypic_data_trees_by_degree,
    hilbert_series_so3,
    space_dimension,
    space_dimensions,
)


def test_isotypic_dimensions_match_so3_hilbert_series() -> None:
    theory = SO3RepresentationTheory()
    trees_by_degree = build_isotypic_data_trees_by_degree(
        theory,
        input_irreps=(1,),
        input_multiplicities=(1,),
        output_irrep=0,
        max_degree=3,
        random_seed=0,
        modulus=13,
    )

    assert space_dimensions(trees_by_degree) == hilbert_series_so3(
        (1,),
        (1,),
        0,
        3,
    )


def test_isotypic_data_tree_is_single_degree() -> None:
    theory = SO3RepresentationTheory()
    tree = build_isotypic_data_tree(
        theory,
        input_irreps=(1,),
        input_multiplicities=(1,),
        output_irrep=0,
        degree=2,
        random_seed=0,
        modulus=7,
    )

    assert tree.degree == 2
    assert space_dimension(tree.isotypic_leaves) == 1
    assert all(not hasattr(leaf, "degree") for leaf in tree.isotypic_leaves)


def test_isotypic_data_tree_accepts_modulus_zero() -> None:
    theory = SO3RepresentationTheory()
    tree = build_isotypic_data_tree(
        theory,
        input_irreps=(1,),
        input_multiplicities=(1,),
        output_irrep=0,
        degree=2,
        random_seed=0,
        modulus=0,
    )

    assert space_dimension(tree.isotypic_leaves) == 1


def test_isotypic_data_tree_rejects_prime_without_required_roots() -> None:
    theory = SO3RepresentationTheory()

    with pytest.raises(ValueError, match="prime modulus"):
        build_isotypic_data_tree(
            theory,
            input_irreps=(1,),
            input_multiplicities=(1,),
            output_irrep=0,
            degree=2,
            random_seed=0,
            modulus=17,
        )
