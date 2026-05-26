"""Construction of isotypic data trees."""

from __future__ import annotations

from itertools import product

from .bases import (
    _has_tensor_product_constituent,
    _schur_functor_basis,
    tensor_product_basis,
)
from .combinatorics import (
    integer_partitions,
    semistandard_young_tableaux,
    validate_waring_modulus,
    weak_compositions,
)
from .protocols import RepresentationTheory
from .types import Irrep, IsotypicDataTree, IsotypicLeaf


def build_isotypic_data_tree(
    theory: RepresentationTheory,
    input_irreps: tuple[Irrep, ...],
    input_multiplicities: tuple[int, ...],
    output_irrep: Irrep,
    degree: int,
    *,
    random_seed: int,
    modulus: int,
) -> IsotypicDataTree:
    """Build the isotypic data tree for one homogeneous component of the invariant algebra/covariant module."""
    if not input_irreps:
        raise ValueError("input_irreps must be nonempty")
    if len(input_irreps) != len(input_multiplicities):
        raise ValueError("input_irreps and input_multiplicities must have equal length")
    if degree < 0:
        raise ValueError("degree must be nonnegative")
    if any(multiplicity <= 0 for multiplicity in input_multiplicities):
        raise ValueError("input multiplicities must be positive")

    active_modulus = validate_waring_modulus(modulus, degree)
    isotypic_leaves: list[IsotypicLeaf] = []
    for multidegree in weak_compositions(degree, len(input_irreps)):
        partition_options = tuple(
            integer_partitions(
                input_degree,
                max_length=min(
                    theory.irrep_dimension(input_irrep),
                    input_multiplicity,
                ),
            )
            for input_degree, input_irrep, input_multiplicity in zip(
                multidegree,
                input_irreps,
                input_multiplicities,
            )
        )

        for partitions in product(*partition_options):
            intermediate_irrep_options = tuple(
                tuple(
                    constituent
                    for constituent, _multiplicity in theory.schur_power_constituent_irreps(
                        input_irrep,
                        partition,
                    )
                )
                for input_irrep, partition in zip(
                    input_irreps,
                    partitions,
                )
            )

            for intermediate_irreps in product(*intermediate_irrep_options):
                if not _has_tensor_product_constituent(
                    theory,
                    intermediate_irreps,
                    output_irrep,
                ):
                    continue

                interior_tensor_trains = tensor_product_basis(
                    theory,
                    intermediate_irreps,
                    output_irrep,
                )
                leaf_tensor_trees = tuple(
                    _schur_functor_basis(
                        theory,
                        input_irrep,
                        partition,
                        intermediate_irrep,
                        random_seed,
                        active_modulus,
                    )
                    for input_irrep, partition, intermediate_irrep in zip(
                        input_irreps,
                        partitions,
                        intermediate_irreps,
                    )
                )
                semi_standard_young_tableaux = tuple(
                    semistandard_young_tableaux(
                        partition,
                        input_multiplicity,
                    )
                    for partition, input_multiplicity in zip(
                        partitions,
                        input_multiplicities,
                    )
                )
                isotypic_leaves.append(
                    IsotypicLeaf(
                        multidegree=multidegree,
                        partitions=partitions,
                        intermediate_irreps=intermediate_irreps,
                        interior_tensor_trains=interior_tensor_trains,
                        leaf_tensor_trees=leaf_tensor_trees,
                        semi_standard_young_tableaux=semi_standard_young_tableaux,
                    )
                )

    return IsotypicDataTree(
        input_irreps=input_irreps,
        input_multiplicities=input_multiplicities,
        output_irrep=output_irrep,
        degree=degree,
        isotypic_leaves=tuple(isotypic_leaves),
    )


def build_isotypic_data_trees_by_degree(
    theory: RepresentationTheory,
    input_irreps: tuple[Irrep, ...],
    input_multiplicities: tuple[int, ...],
    output_irrep: Irrep,
    max_degree: int,
    *,
    random_seed: int,
    modulus: int,
) -> tuple[IsotypicDataTree, ...]:
    """Build isotypic data trees for degrees ``0`` through ``max_degree``."""
    if max_degree < 0:
        raise ValueError("max_degree must be nonnegative")

    active_modulus = validate_waring_modulus(modulus, max_degree)
    return tuple(
        build_isotypic_data_tree(
            theory,
            input_irreps,
            input_multiplicities,
            output_irrep,
            degree,
            random_seed=random_seed,
            modulus=active_modulus,
        )
        for degree in range(max_degree + 1)
    )


__all__ = (
    "build_isotypic_data_tree",
    "build_isotypic_data_trees_by_degree",
)
