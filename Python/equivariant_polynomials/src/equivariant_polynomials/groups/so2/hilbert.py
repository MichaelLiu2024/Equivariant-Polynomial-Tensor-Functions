"""SO(2) Hilbert-series utilities."""

from __future__ import annotations

from collections import Counter


def hilbert_series_so2(
    input_irreps: tuple[int, ...],
    input_multiplicities: tuple[int, ...],
    output_irrep: int,
    max_degree: int,
) -> tuple[int, ...]:
    """Multiplicity of H_output_irrep in Sym^d(sum_i m_i H_lambda_i)."""
    if len(input_irreps) != len(input_multiplicities):
        raise ValueError("input_irreps and input_multiplicities must have equal length")
    if max_degree < 0:
        raise ValueError("max_degree must be nonnegative")

    multiplicity_by_weight: Counter[int] = Counter()
    for weight, multiplicity in zip(input_irreps, input_multiplicities):
        if multiplicity <= 0:
            raise ValueError("input multiplicities must be positive")
        multiplicity_by_weight[weight] += multiplicity

    by_degree: list[dict[int, int]] = [{} for _ in range(max_degree + 1)]
    by_degree[0][0] = 1

    for weight, multiplicity in multiplicity_by_weight.items():
        coeffs = [1] * (max_degree + 1)
        for count in range(1, max_degree + 1):
            coeffs[count] = coeffs[count - 1] * (count + multiplicity - 1) // count

        shifts = [count * weight for count in range(max_degree + 1)]
        next_by_degree: list[dict[int, int]] = [{} for _ in range(max_degree + 1)]

        for degree, weights in enumerate(by_degree):
            if not weights:
                continue
            for total_weight, value in weights.items():
                for count in range(max_degree - degree + 1):
                    shifted_weight = total_weight + shifts[count]
                    target = next_by_degree[degree + count]
                    target[shifted_weight] = (
                        target.get(shifted_weight, 0) + value * coeffs[count]
                    )

        by_degree = next_by_degree

    return tuple(weights.get(output_irrep, 0) for weights in by_degree)


__all__ = ("hilbert_series_so2",)