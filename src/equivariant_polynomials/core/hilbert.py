"""Weight-distribution generating functions shared by group Hilbert series.

Each group series convolves stars-and-bars symmetric-power generating functions
over the input irreps' weight diagrams; only the weight diagram and the
weight-to-multiplicity rule are group specific and stay in the group backends.
"""

from __future__ import annotations

from collections.abc import Iterable
from math import comb


def symmetric_power_weight_distribution(
    weight_diagram: Iterable[int],
    multiplicity: int,
    max_degree: int,
) -> tuple[dict[int, int], ...]:
    """Per-degree ``{weight: count}`` of ``Sym^c`` (``c`` in ``0..max_degree``) of
    ``multiplicity`` copies of a representation with the given weight diagram."""
    by_degree: list[dict[int, int]] = [{} for _ in range(max_degree + 1)]
    by_degree[0][0] = 1
    coeffs = tuple(  # dim Sym^count of a multiplicity-dimensional weight space
        comb(count + multiplicity - 1, multiplicity - 1)
        for count in range(max_degree + 1)
    )
    for weight in weight_diagram:
        next_by_degree: list[dict[int, int]] = [{} for _ in range(max_degree + 1)]
        for degree, weight_counts in enumerate(by_degree):
            if not weight_counts:
                continue
            for count in range(max_degree - degree + 1):
                coeff, shift = coeffs[count], count * weight
                target = next_by_degree[degree + count]
                for weight0, value in weight_counts.items():
                    shifted = weight0 + shift
                    target[shifted] = target.get(shifted, 0) + value * coeff
        by_degree = next_by_degree
    return tuple(by_degree)


def multigraded_weight_distribution(
    weight_diagrams: tuple[Iterable[int], ...],
    multiplicities: tuple[int, ...],
    max_multidegree: tuple[int, ...],
) -> dict[tuple[int, ...], dict[int, int]]:
    """``{multidegree: {weight: count}}`` over the multidegree grid bounded by
    ``max_multidegree`` for the symmetric algebra on the inputs."""
    by_multidegree: dict[tuple[int, ...], dict[int, int]] = {(0,) * len(weight_diagrams): {0: 1}}
    for axis, (diagram, multiplicity, max_degree) in enumerate(
        zip(weight_diagrams, multiplicities, max_multidegree)
    ):
        block = symmetric_power_weight_distribution(diagram, multiplicity, max_degree)
        next_by_multidegree: dict[tuple[int, ...], dict[int, int]] = {}
        for multidegree, weight_counts0 in by_multidegree.items():
            for count, weight_counts1 in enumerate(block):
                target = next_by_multidegree.setdefault(multidegree[:axis] + (count,) + multidegree[axis + 1 :], {})
                for weight0, value0 in weight_counts0.items():
                    for weight1, value1 in weight_counts1.items():
                        weight = weight0 + weight1
                        target[weight] = target.get(weight, 0) + value0 * value1
        by_multidegree = next_by_multidegree
    return by_multidegree


__all__ = ("symmetric_power_weight_distribution", "multigraded_weight_distribution")
