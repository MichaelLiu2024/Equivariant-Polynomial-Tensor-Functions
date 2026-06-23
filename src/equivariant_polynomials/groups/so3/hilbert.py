"""SO(3) Hilbert-series utilities."""

from __future__ import annotations

from collections import Counter
from math import comb

from equivariant_polynomials.core.combinatorics import _validate_input_metadata


def hilbert_series_so3(
    input_irreps: tuple[int, ...],
    input_multiplicities: tuple[int, ...],
    output_irrep: int,
    max_degree: int,
) -> tuple[int, ...]:
    """Multiplicity of V_output_irrep in Sym^d(sum_i m_i V_l_i), d <= max_degree."""
    W = max_degree * max(input_irreps)

    if output_irrep > W:
        return (0,) * (max_degree + 1)

    offset = W + 1
    width = 2 * W + 3

    polys = [[0] * width for _ in range(max_degree + 1)]
    polys[0][offset] = 1

    weights: Counter[int] = Counter()
    for ell, mult in zip(input_irreps, input_multiplicities):
        for w in range(-ell, ell + 1):
            weights[w] += mult

    binoms = {
        mult: [comb(c + mult - 1, mult - 1) for c in range(max_degree + 1)]
        for mult in set(weights.values())
    }

    for w, mult in weights.items():
        next_polys = [[0] * width for _ in range(max_degree + 1)]
        b = binoms[mult]

        for d0, row in enumerate(polys):
            terms = [(i, a) for i, a in enumerate(row) if a]
            for c in range(max_degree - d0 + 1):
                target = next_polys[d0 + c]
                shift = c * w
                coeff = b[c]

                for i, a in terms:
                    target[i + shift] += a * coeff

        polys = next_polys

    i = offset + output_irrep
    return tuple(row[i] - row[i + 1] for row in polys)


def _block_weight_polys_so3(
    ell: int,
    multiplicity: int,
    max_degree: int,
) -> tuple[dict[int, int], ...]:
    by_degree: list[dict[int, int]] = [{} for _ in range(max_degree + 1)]
    by_degree[0][0] = 1

    coeffs = tuple(
        comb(count + multiplicity - 1, multiplicity - 1)
        for count in range(max_degree + 1)
    )

    for weight in range(-ell, ell + 1):
        next_by_degree: list[dict[int, int]] = [
            {} for _ in range(max_degree + 1)
        ]
        for degree0, weights0 in enumerate(by_degree):
            if not weights0:
                continue
            for count in range(max_degree - degree0 + 1):
                coeff = coeffs[count]
                shift = count * weight
                target = next_by_degree[degree0 + count]
                for q_weight, value in weights0.items():
                    shifted = q_weight + shift
                    target[shifted] = target.get(shifted, 0) + value * coeff
        by_degree = next_by_degree

    return tuple(by_degree)


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

    zero = (0,) * len(input_irreps)
    by_multidegree: dict[tuple[int, ...], dict[int, int]] = {zero: {0: 1}}

    for i, (ell, multiplicity, max_degree_i) in enumerate(
        zip(input_irreps, input_multiplicities, max_multidegree)
    ):
        block = _block_weight_polys_so3(ell, multiplicity, max_degree_i)
        next_by_multidegree: dict[tuple[int, ...], dict[int, int]] = {}
        for alpha, weights0 in by_multidegree.items():
            for count, weights1 in enumerate(block):
                new_alpha = alpha[:i] + (count,) + alpha[i + 1 :]
                target = next_by_multidegree.setdefault(new_alpha, {})
                for weight0, value0 in weights0.items():
                    for weight1, value1 in weights1.items():
                        weight = weight0 + weight1
                        target[weight] = target.get(weight, 0) + value0 * value1
        by_multidegree = next_by_multidegree

    return {
        alpha: weights.get(output_irrep, 0) - weights.get(output_irrep + 1, 0)
        for alpha, weights in by_multidegree.items()
    }


__all__ = ("hilbert_series_so3", "hilbert_series_so3_multigraded")
