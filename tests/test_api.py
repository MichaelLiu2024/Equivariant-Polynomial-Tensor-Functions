from __future__ import annotations

import numpy as np
import pytest

from equivariant_polynomials import (
    Covariant,
    CovariantCollection,
    IsotypicComponent,
    Options,
    Representation,
    SO2RepresentationTheory,
    SO3RepresentationTheory,
    covariant_basis,
    covariant_dimension,
    covariant_generators,
    covariant_hilbert_series,
    hilbert_series_so2,
    hilbert_series_so3,
    invariant_basis,
    invariant_dimension,
    invariant_generators,
    invariant_hilbert_series,
)


@pytest.fixture
def so3():
    return SO3RepresentationTheory()


@pytest.fixture
def vector(so3):
    return Representation.irrep(so3, 1, name="vector")


# --------------------------------------------------------------------------- #
# Representation
# --------------------------------------------------------------------------- #


def test_representation_normalizes_and_merges_components(so3) -> None:
    rep = Representation(so3, [1, (1, 2), IsotypicComponent(2, 3)])
    assert rep.irreps == (1, 2)
    assert rep.multiplicities == (3, 3)  # 1 + 2 merged, then 3
    assert rep.dimension == 3 * 3 + 3 * 5


def test_representation_irrep_and_trivial(so3) -> None:
    assert Representation.irrep(so3, 1).dimension == 3
    assert Representation.trivial(so3).is_trivial
    assert Representation.trivial(so3).dimension == 1


def test_representation_rejects_nonpositive_multiplicity(so3) -> None:
    with pytest.raises(ValueError):
        Representation.irrep(so3, 1, 0)


# --------------------------------------------------------------------------- #
# Graded dimensions match the group Molien series
# --------------------------------------------------------------------------- #


def test_invariant_hilbert_series_matches_molien(vector) -> None:
    assert invariant_hilbert_series(vector, 4) == hilbert_series_so3((1,), (1,), 0, 4)


def test_covariant_hilbert_series_matches_molien(so3, vector) -> None:
    codomain = Representation.irrep(so3, 1)
    assert covariant_hilbert_series(vector, codomain, 4) == hilbert_series_so3(
        (1,), (1,), 1, 4
    )


def test_dimension_helpers_agree_with_series(vector) -> None:
    assert invariant_dimension(vector, 2) == 1
    series = invariant_hilbert_series(vector, 4)
    assert tuple(invariant_dimension(vector, d) for d in range(5)) == series


def test_so2_hilbert_series_matches_molien() -> None:
    so2 = SO2RepresentationTheory()
    domain = Representation(so2, [(1, 2), (-1, 1)])
    assert invariant_hilbert_series(domain, 4) == hilbert_series_so2((1, -1), (2, 1), 0, 4)


def test_dimension_sums_over_codomain_components(so3, vector) -> None:
    codomain = Representation(so3, [(0, 1), (1, 2)])
    for degree in range(4):
        expected = invariant_dimension(vector, degree) + 2 * covariant_dimension(
            vector, Representation.irrep(so3, 1), degree
        )
        assert covariant_dimension(vector, codomain, degree) == expected


# --------------------------------------------------------------------------- #
# Generators: algebra vs module distinction
# --------------------------------------------------------------------------- #


def test_invariant_generators_are_algebra_generators(vector) -> None:
    generators = invariant_generators(vector, max_degree=4)
    assert generators.kind == "generators"
    assert not generators.is_module
    # constant 1 (degree 0) and |x|^2 (degree 2); |x|^4 is decomposable.
    assert generators.counts_by_degree() == (1, 0, 1, 0, 0)


def test_covariant_generators_into_trivial_are_module_generators(so3, vector) -> None:
    # M_G(X, trivial) = R_G(X) is a free rank-1 module: only the constant 1.
    generators = covariant_generators(vector, Representation.trivial(so3), max_degree=4)
    assert generators.is_module
    assert generators.counts_by_degree() == (1, 0, 0, 0, 0)


def test_covariant_module_generators_for_identity(vector) -> None:
    generators = covariant_generators(vector, vector, max_degree=4)
    assert generators.counts_by_degree() == (0, 1, 0, 0, 0)


def test_arbitrary_output_lifts_across_copies(so3, vector) -> None:
    codomain = Representation(so3, [(0, 1), (1, 2)])
    generators = covariant_generators(vector, codomain, max_degree=3)
    # degree 0: constant into the trivial copy; degree 1: identity into each l=1 copy.
    assert generators.counts_by_degree() == (1, 2, 0, 0)
    output_slots = {(g.output_irrep, g.output_copy) for g in generators if g.degree == 1}
    assert output_slots == {(1, 0), (1, 1)}


# --------------------------------------------------------------------------- #
# Evaluation
# --------------------------------------------------------------------------- #


def test_identity_covariant_returns_the_input(vector) -> None:
    generators = covariant_generators(vector, vector, max_degree=1)
    identity = generators[0]
    x = np.array([2.0, -1.0, 3.0], dtype=np.complex128)
    assert np.allclose(identity(x), x)


def test_quadratic_invariant_is_a_scalar(vector) -> None:
    generators = invariant_generators(vector, max_degree=2)
    quadratic = next(g for g in generators if g.degree == 2)
    value = quadratic(np.array([1.0, 2.0, 3.0]))
    assert value.shape == (1,)


def test_batched_evaluation(vector) -> None:
    generators = covariant_generators(vector, vector, max_degree=1)
    identity = generators[0]
    batch = np.arange(3 * 3, dtype=np.complex128).reshape(3, 1, 3)
    out = identity(batch)
    assert out.shape == (3, 3)
    assert np.allclose(out, batch[:, 0, :])


def test_evaluate_rejects_wrong_shape(vector) -> None:
    generators = covariant_generators(vector, vector, max_degree=1)
    with pytest.raises(ValueError):
        generators[0](np.zeros((2, 4)))  # wrong irrep dimension


# --------------------------------------------------------------------------- #
# Vector-space bases
# --------------------------------------------------------------------------- #


def test_covariant_basis_size_matches_dimension(so3, vector) -> None:
    codomain = Representation.irrep(so3, 2)
    basis = covariant_basis(vector, codomain, degree=2)
    assert len(basis) == covariant_dimension(vector, codomain, 2)


def test_basis_max_degree_spans_all_degrees(vector) -> None:
    basis = invariant_basis(vector, max_degree=4)
    assert len(basis) == sum(invariant_hilbert_series(vector, 4))
    assert basis.degrees() == (0, 2, 4)


def test_basis_requires_exactly_one_degree_argument(vector) -> None:
    with pytest.raises(ValueError):
        invariant_basis(vector)
    with pytest.raises(ValueError):
        invariant_basis(vector, degree=2, max_degree=3)


# --------------------------------------------------------------------------- #
# Combination / assembly (the ansatz inner sum)
# --------------------------------------------------------------------------- #


def test_combine_assembles_codomain_value(so3, vector) -> None:
    codomain = Representation(so3, [(0, 1), (1, 2)])
    generators = covariant_generators(vector, codomain, max_degree=3)
    coeffs = np.arange(1, len(generators) + 1, dtype=np.complex128)
    x = np.array([1.0, 0.0, 0.0])
    out = generators.combine(coeffs).evaluate(x)
    assert isinstance(out, tuple)
    assert out[0].shape == (1, 1)  # trivial component
    assert out[1].shape == (2, 3)  # two l=1 copies


def test_assemble_matches_combine_batched(so3, vector) -> None:
    codomain = Representation(so3, [(1, 2)])
    generators = covariant_generators(vector, codomain, max_degree=3)
    batch = np.arange(2 * 3, dtype=np.complex128).reshape(2, 1, 3)
    coeffs = np.arange(2 * len(generators), dtype=np.complex128).reshape(2, len(generators))
    combined = generators.combine(coeffs).evaluate(batch)
    assembled = generators.assemble(generators.evaluate(batch), coeffs)
    assert np.allclose(combined, assembled)
    assert combined.shape == (2, 2, 3)


def test_combine_checks_coefficient_count(vector) -> None:
    generators = invariant_generators(vector, max_degree=2)
    with pytest.raises(ValueError):
        generators.combine(np.ones(len(generators) + 1))


def test_combine_rejects_mismatched_batch(so3, vector) -> None:
    generators = covariant_generators(vector, Representation(so3, [(1, 2)]), max_degree=3)
    batch_x = np.arange(2 * 3, dtype=np.complex128).reshape(2, 1, 3)  # batch of 2
    coeffs = np.ones((3, len(generators)), dtype=np.complex128)  # batch of 3
    with pytest.raises(ValueError):
        generators.combine(coeffs).evaluate(batch_x)


# --------------------------------------------------------------------------- #
# Ambient coordinates
# --------------------------------------------------------------------------- #


def test_ambient_roundtrip(so3) -> None:
    domain = Representation.irrep(
        so3,
        1,
        to_isotypic=lambda x: (np.asarray(x, dtype=np.complex128).reshape(1, 3),),
        from_isotypic=lambda coords: coords[0],
    )
    generators = covariant_generators(domain, domain, max_degree=1)
    x = np.array([1.0, 2.0, 3.0])
    out = generators.combine(np.ones(len(generators))).evaluate(
        x, coordinates="ambient", output="ambient"
    )
    assert np.asarray(out).shape == (1, 3)


def test_ambient_requires_maps(vector) -> None:
    generators = covariant_generators(vector, vector, max_degree=1)
    with pytest.raises(ValueError):
        generators[0](np.zeros(3), coordinates="ambient")


# --------------------------------------------------------------------------- #
# Verification & determinism
# --------------------------------------------------------------------------- #


def test_verify_basis_and_generators(so3, vector) -> None:
    assert invariant_basis(vector, max_degree=4).verify()
    assert invariant_generators(vector, max_degree=4).verify()
    assert covariant_generators(vector, Representation(so3, [(0, 1), (1, 2)]), max_degree=3).verify()


def test_construction_is_deterministic(vector) -> None:
    options = Options(modulus=2521, seed=7)
    first = invariant_generators(vector, max_degree=4, options=options)
    second = invariant_generators(vector, max_degree=4, options=options)
    assert first.counts_by_degree() == second.counts_by_degree()


def test_mismatched_backends_raise(so3) -> None:
    so2 = SO2RepresentationTheory()
    domain = Representation.irrep(so3, 1)
    codomain = Representation.irrep(so2, 1)
    with pytest.raises(ValueError):
        covariant_basis(domain, codomain, degree=1)
