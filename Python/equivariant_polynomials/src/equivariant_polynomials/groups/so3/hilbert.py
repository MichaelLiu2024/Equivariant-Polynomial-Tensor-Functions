"""SO(3) Hilbert-series utilities."""

from __future__ import annotations

from collections import Counter
from math import comb


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


__all__ = ("hilbert_series_so3",)
