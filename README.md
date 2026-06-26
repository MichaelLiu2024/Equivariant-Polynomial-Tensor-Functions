# Equivariant Polynomials

Layered Python implementation of representation-theoretic algorithms for
equivariant polynomial tensor functions.

## Installation

From this directory:

```bash
python -m pip install -e .
```

The import package is `equivariant_polynomials`.  The recommended entry point is
the high-level API: describe the input/output representations by their isotypic
decomposition, then ask for minimal generators or vector-space bases.

```python
from equivariant_polynomials import (
    SO3RepresentationTheory,
    Representation,
    invariant_generators,
    covariant_generators,
)

theory = SO3RepresentationTheory()
X = Representation(theory, [(2, 2), (3, 1)])      # 2 copies of l=2, plus l=3
Y = Representation.irrep(theory, 4)               # the l=4 irrep

invariants = invariant_generators(X, max_degree=6)        # algebra generators of R_G(X)
covariants = covariant_generators(X, Y, max_degree=6)     # module generators of M_G(X, Y)
```

The returned `Covariant` objects are callable and evaluate the equivariant
polynomials at points given in isotypic coordinates.  The group-agnostic `core`
entry points (`extract_independent_generators`, `stream_isotypic_data_tree`) remain
available for advanced use.

Construction selects independent elements over a prime field; pass a prime
`Options(modulus=p)` with `p > max_degree`, or let it auto-select.  See
[docs/usage.md](docs/usage.md) for the full API and modulus-selection guidance.

## Layout

- `src/equivariant_polynomials/core/` contains the group-agnostic types,
  protocols, combinatorics, evaluators, isotypic data-tree construction, and
  abstract tensor-basis and independent-generator extraction.
- `src/equivariant_polynomials/groups/so2/` and
  `src/equivariant_polynomials/groups/so3/` contain group-specific
  representation rules, Clebsch-Gordan tensors, and Hilbert-series utilities.
- `tests/` contains lightweight regression and smoke tests.
- `docs/` contains installation, usage, and theory notes, plus a worked
  example and profiling notebook (`examples.ipynb`).
