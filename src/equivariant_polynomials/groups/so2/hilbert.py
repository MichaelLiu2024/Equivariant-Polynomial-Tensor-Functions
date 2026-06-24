"""SO(2) Hilbert-series utilities."""

from __future__ import annotations

from collections import Counter
from math import comb

from equivariant_polynomials.core.combinatorics import _validate_input_metadata


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

    multiplicity_by_weight: Counter[int] = Counter()
    for weight, multiplicity in zip(input_irreps, input_multiplicities):
        multiplicity_by_weight[weight] += multiplicity

    by_degree: list[dict[int, int]] = [{} for _ in range(max_degree + 1)]
    by_degree[0][0] = 1

    for weight, multiplicity in multiplicity_by_weight.items():
        coeffs = [
            comb(count + multiplicity - 1, multiplicity - 1)
            for count in range(max_degree + 1)
        ]
        next_by_degree: list[dict[int, int]] = [{} for _ in range(max_degree + 1)]

        for degree, weights in enumerate(by_degree):
            if not weights:
                continue
            for total_weight, value in weights.items():
                for count in range(max_degree - degree + 1):
                    shifted_weight = total_weight + count * weight
                    target = next_by_degree[degree + count]
                    target[shifted_weight] = (
                        target.get(shifted_weight, 0) + value * coeffs[count]
                    )

        by_degree = next_by_degree

    return tuple(weights.get(output_irrep, 0) for weights in by_degree)


__all__ = ("hilbert_series_so2",)
