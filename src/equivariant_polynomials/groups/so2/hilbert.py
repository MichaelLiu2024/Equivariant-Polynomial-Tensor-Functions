"""SO(2) Hilbert-series utilities."""

from __future__ import annotations

from collections import Counter

from equivariant_polynomials.core.combinatorics import _validate_input_metadata
from equivariant_polynomials.core.hilbert import multigraded_weight_distribution


def hilbert_series_so2(
    input_irreps: tuple[int, ...],
    input_multiplicities: tuple[int, ...],
    output_irrep: int,
    max_degree: int,
) -> tuple[int, ...]:
    """Multiplicity of H_output_irrep in Sym^d(sum_i m_i H_lambda_i)."""
    _validate_input_metadata(
        input_irreps,
        input_multiplicities,
        max_degree=max_degree,
        require_inputs=False,
    )

    # Each H_lambda is one-dimensional, so its weight diagram is the single weight
    # lambda; equal weights merge into one axis.  The SO(2) multiplicity is just
    # the dimension of the output weight space, summed over equal total degree.
    multiplicity_by_weight: Counter[int] = Counter()
    for weight, multiplicity in zip(input_irreps, input_multiplicities):
        multiplicity_by_weight[weight] += multiplicity

    weights = tuple(multiplicity_by_weight)
    distribution = multigraded_weight_distribution(
        tuple((weight,) for weight in weights),
        tuple(multiplicity_by_weight[weight] for weight in weights),
        (max_degree,) * len(weights),
    )

    totals = [0] * (max_degree + 1)
    for multidegree, weight_counts in distribution.items():
        degree = sum(multidegree)
        if degree <= max_degree:
            totals[degree] += weight_counts.get(output_irrep, 0)
    return tuple(totals)


__all__ = ("hilbert_series_so2",)
