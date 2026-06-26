"""SO(3) Hilbert-series utilities."""

from __future__ import annotations

from equivariant_polynomials.core.combinatorics import _validate_input_metadata
from equivariant_polynomials.core.hilbert import multigraded_weight_distribution


def hilbert_series_so3_multigraded(
    input_irreps: tuple[int, ...],
    input_multiplicities: tuple[int, ...],
    output_irrep: int,
    max_multidegree: tuple[int, ...],
) -> dict[tuple[int, ...], int]:
    """Multiplicity of ``V_output_irrep`` in each SO(3) multidegree."""
    _validate_input_metadata(
        input_irreps,
        input_multiplicities,
        degrees=max_multidegree,
        degrees_name="max_multidegree",
    )
    if output_irrep < 0 or any(ell < 0 for ell in input_irreps):
        raise ValueError("SO(3) irreps must be nonnegative integers")

    # V_ell carries the weights -ell..ell, each with one-dimensional weight space.
    distribution = multigraded_weight_distribution(
        tuple(range(-ell, ell + 1) for ell in input_irreps),
        input_multiplicities,
        max_multidegree,
    )
    return {
        multidegree: weight_counts.get(output_irrep, 0) - weight_counts.get(output_irrep + 1, 0)
        for multidegree, weight_counts in distribution.items()
    }


def hilbert_series_so3(
    input_irreps: tuple[int, ...],
    input_multiplicities: tuple[int, ...],
    output_irrep: int,
    max_degree: int,
) -> tuple[int, ...]:
    """Multiplicity of V_output_irrep in Sym^d(sum_i m_i V_l_i) for each d <= max_degree.

    The multigraded series summed over all multidegrees of equal total degree.
    """
    multigraded = hilbert_series_so3_multigraded(
        input_irreps,
        input_multiplicities,
        output_irrep,
        (max_degree,) * len(input_irreps),
    )
    totals = [0] * (max_degree + 1)
    for multidegree, value in multigraded.items():
        degree = sum(multidegree)
        if degree <= max_degree:
            totals[degree] += value
    return tuple(totals)


__all__ = ("hilbert_series_so3", "hilbert_series_so3_multigraded")
