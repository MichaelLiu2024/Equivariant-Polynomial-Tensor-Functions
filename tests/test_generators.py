from __future__ import annotations

import math

import numpy as np
import pytest

import equivariant_polynomials.core.generators as generator_core
from equivariant_polynomials.core import (
    IsotypicLeaf,
    SSYT,
    TensorTree,
    extract_independent_generators,
)
from equivariant_polynomials.core.streaming import STREAM_BATCH_SIZE
from equivariant_polynomials.groups.so3 import (
    SO3RepresentationTheory,
    hilbert_series_so3_multigraded,
)


@pytest.mark.parametrize(
    "target_dimensions_by_multidegree",
    [
        None,
        hilbert_series_so3_multigraded((1,), (1,), 0, (3,)),
    ],
)
def test_core_algebra_generator_extractor_infers_target_dimensions(
    target_dimensions_by_multidegree,
) -> None:
    theory = SO3RepresentationTheory()

    generators = extract_independent_generators(
        theory,
        input_irreps=(1,),
        input_multiplicities=(1,),
        output_irrep=0,
        max_degree=3,
        probe_target=lambda dimensions, _output_dimension: dimensions,
        degree_limit=lambda degree: degree // 2,
        random_seed=0,
        modulus=13,
        first_generator_degree=1,
        target_dimensions_by_multidegree=target_dimensions_by_multidegree,
    )

    assert tuple(map(len, generators)) == (1, 0, 1, 0)


def test_probe_counts_are_copy_content_local(monkeypatch) -> None:
    class DimensionOnlyTheory:
        trivial_irrep = 0

        def irrep_dimension(self, irrep):
            return 1

        def schur_power_constituent_irreps(self, _irrep, partition):
            return ((0, 1),) if not partition else ((0, 1), (1, 6))

    theory = DimensionOnlyTheory()
    input_irreps = (1,)
    input_multiplicities = (2,)
    sampled_probe_counts = []
    streamed_probe_counts = []

    def fake_sample_probes(
        theory,
        input_irreps,
        input_multiplicities,
        num_probes,
        _modulus,
        _random_seed,
    ):
        sampled_probe_counts.append(num_probes)
        return tuple(
            np.ones(
                (num_probes, multiplicity, theory.irrep_dimension(irrep)),
                dtype=np.uint64,
            )
            for irrep, multiplicity in zip(input_irreps, input_multiplicities)
        )

    def fake_stream_content_generators(
        _theory,
        _leaves,
        _previous_basis,
        _needed,
        _probe_batches,
        num_probes,
        max_probes,
        modulus,
        output_dimension,
        _young_tree_cache,
    ):
        streamed_probe_counts.append((num_probes, max_probes))
        return (), generator_core._empty_syndromes(
            max_probes,
            output_dimension,
            modulus,
        )

    monkeypatch.setattr(
        generator_core,
        "sample_isotypic_input_probes",
        fake_sample_probes,
    )
    monkeypatch.setattr(
        generator_core,
        "_stream_content_generators",
        fake_stream_content_generators,
    )

    generator_core.extract_independent_generators(
        theory,
        input_irreps,
        input_multiplicities,
        1,
        2,
        lambda dimensions, output_dimension: tuple(
            math.ceil(dimension / output_dimension) + 2 if dimension else 0
            for dimension in dimensions
        ),
        lambda degree: degree - 1,
        random_seed=0,
        modulus=13,
        target_dimensions_by_multidegree={(2,): 18},
    )

    assert sampled_probe_counts == [8]
    assert streamed_probe_counts == [(8, 8), (8, 8), (8, 8)]


def test_previous_products_match_copy_content() -> None:
    syndromes = {
        (0, 1): np.full((1, 1, 1), 2, dtype=np.uint64),
        (1, 0): np.full((1, 1, 1), 3, dtype=np.uint64),
    }
    basis = generator_core._previous_content_product_basis(
        (1, 1),
        {(1, 0): np.ones((1, 1, 1), dtype=np.uint64)},
        syndromes.__getitem__,
        first_generator_degree=0,
        max_generator_degree=2,
        num_probes=1,
        output_dimension=1,
        modulus=13,
    )

    assert basis.tolist() == [[2]]


def test_stream_content_generators_evaluates_fixed_leaf_batches(
    monkeypatch,
) -> None:
    leaves = tuple(_unit_leaf(i) for i in range(3))
    calls = []

    def fake_compute_syndromes(
        _theory,
        polynomials,
        _probe_batches,
        _modulus,
        _output_dimension,
        _young_tree_cache,
    ):
        calls.append(polynomials)
        assert len(polynomials) <= STREAM_BATCH_SIZE
        return np.ones((1, 1, 1), dtype=np.uint64)

    monkeypatch.setattr(
        generator_core,
        "compute_syndromes",
        fake_compute_syndromes,
    )

    selected, syndromes = generator_core._stream_content_generators(
        theory=object(),
        leaves=iter(leaves),
        previous_basis=np.empty((1, 0), dtype=np.uint64),
        needed=1,
        probe_batches=(np.ones((1, 1, 1), dtype=np.uint64),),
        num_probes=1,
        max_probes=1,
        modulus=13,
        output_dimension=1,
        young_tree_cache={},
    )

    assert calls == [leaves]
    assert selected == (leaves[0],)
    assert syndromes.shape == (1, 1, 1)


def _unit_leaf(label: int) -> IsotypicLeaf:
    return _unit_leaf_for_multidegree((label,), label)


def _unit_leaf_for_multidegree(
    multidegree: tuple[int, ...],
    label: int,
) -> IsotypicLeaf:
    return IsotypicLeaf(
        multidegree=multidegree,
        partitions=tuple(() for _ in multidegree),
        intermediate_irreps=(label,),
        interior_tensor_trains=((),),
        leaf_tensor_trees=tuple((TensorTree((), ()),) for _ in multidegree),
        semi_standard_young_tableaux=tuple((SSYT((), ()),) for _ in multidegree),
    )
