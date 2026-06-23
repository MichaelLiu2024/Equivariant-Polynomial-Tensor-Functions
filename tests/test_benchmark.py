from __future__ import annotations

from benchmarks import benchmark
from equivariant_polynomials.groups.so3 import (
    SO3RepresentationTheory,
    hilbert_series_so3,
    hilbert_series_so3_multigraded,
)


def test_benchmark_checks_known_generator_counts() -> None:
    summary = benchmark(
        SO3RepresentationTheory(),
        hilbert_series_so3,
        input_irreps=(1,),
        input_multiplicities=(1,),
        output_irrep=0,
        max_degree=3,
        random_seed=0,
        modulus=13,
        hilbert_series_multigraded=hilbert_series_so3_multigraded,
    )

    assert summary["algebra"]["matches_known_generators"] is True
