"""Correctness checks against known SO(3) integrity-basis / covariant-module sizes.

``MINIMAL_INTEGRITY_BASIS_SIZE_DATA`` records, for a range of SO(3) inputs, the
number of minimal generators in each degree (index ``d`` is the count of
degree-``d`` generators):

* entries with ``output_irrep == 0`` are minimal *algebra* generators of the
  invariant algebra ``R_G(X)`` (an integrity basis).  By convention the degree-0
  constant ``1`` is **not** counted as a generator, so these tuples start
  ``(0, 0, ...)``.
* entries with ``output_irrep != 0`` are minimal ``R_G(X)``-*module* generators of
  the covariant module ``M_G(X, H_output_irrep)``.

These are reference oracles from the classical SO(3) invariant-theory literature.
The tests recompute a prefix of each via the public API and check the match;
degrees are kept small so the suite stays fast, but the full tuples remain
available for deeper, on-demand verification.
"""

from __future__ import annotations

import pytest

from equivariant_polynomials import (
    Representation,
    SO3RepresentationTheory,
    covariant_generators,
    invariant_generators,
)

MINIMAL_INTEGRITY_BASIS_SIZE_DATA = {
    ((1,), (1,), 0): (0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
    ((1,), (2,), 0): (0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
    ((1,), (3,), 0): (0, 0, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
    ((2,), (2,), 0): (0, 0, 3, 4, 1, 0),
    ((4,), (1,), 0): (0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0),
    ((1, 3), (1, 1), 0): (0, 0, 2, 0, 4, 0, 5, 3, 1, 7, 1, 2, 0, 1, 0, 1),
    ((2, 3), (1, 1), 0): (0, 0, 2, 2, 4, 4, 9, 9, 8, 5, 3, 2, 1, 1, 1),
    ((1, 2, 3), (1, 1, 1), 0): (0, 0, 3, 4, 12, 15, 37, 42, 38, 22, 9, 6, 3, 2, 1, 1),
    ((2, 3), (2, 1), 0): (0, 0, 4, 7, 14, 26, 52, 68, 60, 39),
    ((2, 3), (2, 1), 4): (0, 0, 6, 21, 63, 147, 264, 284, 133, 35),
    ((2, 3), (2, 1), 5): (0, 0, 2, 14, 62, 180, 378, 556),
    ((2, 3), (2, 1), 6): (0, 0, 1, 13, 55, 168, 402, 671),
    ((2, 4), (2, 1), 0): (0, 0, 4, 10, 16, 33, 57, 76, 66, 21, 7, 5),
}

# (input_irreps, input_multiplicities, output_irrep, max_degree): how deep to
# recompute and check each oracle.  Degrees are kept small so the suite stays
# fast; the full tuples above remain available for deeper, on-demand checks.
KNOWN_COUNT_CASES = [
    ((1,), (1,), 0, 3),
    ((1,), (2,), 0, 3),
    ((1,), (3,), 0, 3),  # exercises the degree-3 determinant of three vectors
    ((2,), (2,), 0, 3),
    ((4,), (1,), 0, 4),
    ((1, 3), (1, 1), 0, 3),
    ((2, 3), (2, 1), 0, 3),  # algebra vs. module for the same input below
    ((2, 3), (2, 1), 4, 3),
    ((2, 3), (2, 1), 5, 3),
    ((2, 3), (2, 1), 6, 3),
]


@pytest.fixture
def so3():
    return SO3RepresentationTheory()


@pytest.mark.parametrize(
    "input_irreps, input_multiplicities, output_irrep, max_degree", KNOWN_COUNT_CASES
)
def test_generator_counts_match_known_sizes(
    so3, input_irreps, input_multiplicities, output_irrep, max_degree
) -> None:
    expected = MINIMAL_INTEGRITY_BASIS_SIZE_DATA[
        (input_irreps, input_multiplicities, output_irrep)
    ][: max_degree + 1]
    domain = Representation(so3, list(zip(input_irreps, input_multiplicities)))

    if output_irrep == so3.trivial_irrep:
        counts = list(invariant_generators(domain, max_degree=max_degree).counts_by_degree())
        counts[0] = 0  # the constant 1 is not part of the integrity basis
        counts = tuple(counts)
    else:
        codomain = Representation.irrep(so3, output_irrep)
        counts = covariant_generators(
            domain, codomain, max_degree=max_degree
        ).counts_by_degree()

    assert counts[: len(expected)] == expected
