from __future__ import annotations

import math
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
for path in (ROOT, SRC):
    if str(path) not in sys.path:
        sys.path.insert(0, str(path))

from equivariant_polynomials import stream_isotypic_data_tree, weak_compositions


def _source_space_dimension(sources) -> int:
    return sum(
        len(source.interior_tensor_trains)
        * math.prod(
            schur_dimension * len(tableaux)
            for schur_dimension, tableaux in zip(
                source.schur_dimensions,
                source.semi_standard_young_tableaux,
            )
        )
        for source in sources
    )


def _streamed_space_dimensions(
    theory,
    *,
    input_irreps,
    input_multiplicities,
    output_irrep,
    max_degree: int,
    random_seed: int,
) -> tuple[int, ...]:
    return tuple(
        sum(
            _source_space_dimension(
                tuple(
                    stream_isotypic_data_tree(
                        theory,
                        input_irreps,
                        input_multiplicities,
                        output_irrep,
                        multidegree,
                        random_seed=random_seed,
                    )
                )
            )
            for multidegree in weak_compositions(degree, len(input_irreps))
        )
        for degree in range(max_degree + 1)
    )


@pytest.fixture
def source_space_dimension():
    return _source_space_dimension


@pytest.fixture
def streamed_space_dimensions():
    return _streamed_space_dimensions
