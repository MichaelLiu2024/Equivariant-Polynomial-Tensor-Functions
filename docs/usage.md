# Usage

The main package is `equivariant_polynomials`.

```python
from equivariant_polynomials import (
    SO3RepresentationTheory,
    build_isotypic_data_tree,
    build_isotypic_data_trees_by_degree,
    hilbert_series_so3,
    space_dimension,
    space_dimensions,
)

random_seed = 12345
theory = SO3RepresentationTheory()
modulus = 2521
tree = build_isotypic_data_tree(
    theory,
    input_irreps=(1,),
    input_multiplicities=(1,),
    output_irrep=0,
    degree=2,
    random_seed=random_seed,
    modulus=modulus,
)
assert space_dimension(tree.isotypic_leaves) == 1

trees_by_degree = build_isotypic_data_trees_by_degree(
    theory,
    input_irreps=(1,),
    input_multiplicities=(1,),
    output_irrep=0,
    max_degree=3,
    random_seed=random_seed,
    modulus=modulus,
)
assert space_dimensions(trees_by_degree) == hilbert_series_so3(
    (1,),
    (1,),
    0,
    3,
)
```

For profiling-style checks, use `benchmarks.benchmark` with the representation
backend and Hilbert series you want to measure.  For finite-field arithmetic,
choose a prime modulus `p` with `p > max_degree`; for a single-degree call, use
that degree as the maximum.  The Waring grid imposes no root-of-unity congruence
on `p`, but very small primes can still be bad for randomized finite-field rank
probes.  The current suggested heuristic is `1000 < p < 10000`; `2521` is a
typical choice.

```python
from benchmarks import benchmark
from equivariant_polynomials import SO2RepresentationTheory, hilbert_series_so2

theory = SO2RepresentationTheory()
summary = benchmark(
    theory,
    hilbert_series_so2,
    input_irreps=(1, -1),
    input_multiplicities=(2, 1),
    output_irrep=0,
    max_degree=4,
    trivial_irrep=0,
    random_seed=0,
    modulus=2521,
)
```
