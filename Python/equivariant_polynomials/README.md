# Equivariant Polynomials

Layered Python implementation of representation-theoretic algorithms for
equivariant polynomial tensor functions.

## Installation

From this directory:

```bash
python -m pip install -e .
```

The import package is `equivariant_polynomials`:

```python
from equivariant_polynomials import (
    SO2RepresentationTheory,
    SO3RepresentationTheory,
    build_isotypic_data_tree,
    build_isotypic_data_trees_by_degree,
    hilbert_series_so2,
    hilbert_series_so3,
)
```

## Layout

- `src/equivariant_polynomials/core/` contains the group-agnostic types,
  protocols, combinatorics, evaluators, isotypic data-tree construction, and
  abstract tensor-basis and independent-generator extraction.
- `src/equivariant_polynomials/groups/so2/` and
  `src/equivariant_polynomials/groups/so3/` contain group-specific
  representation rules, Clebsch-Gordan tensors, and Hilbert-series utilities.
- `tests/` contains lightweight regression and smoke tests.
- `benchmarks/benchmark.py` contains the group-agnostic benchmark helper.
- `docs/` contains installation, usage, and theory notes.
- `notebooks/` contains profiling and example notebooks.
