# Usage

The main package is `equivariant_polynomials`.  The recommended entry point is the
high-level API: describe the input and output representations by their isotypic
decomposition, then ask for bases or minimal generators.

## High-level API

```python
import numpy as np
from equivariant_polynomials import (
    SO3RepresentationTheory,
    Representation,
    invariant_generators,
    covariant_generators,
    invariant_hilbert_series,
)

theory = SO3RepresentationTheory()

# X = two copies of the l=2 irrep plus one l=3 irrep;  Y = the l=4 irrep.
X = Representation(theory, [(2, 2), (3, 1)], name="X")
Y = Representation.irrep(theory, 4, name="Y")

# Minimal C-algebra generators of the invariant algebra R_G(X)...
invariants = invariant_generators(X, max_degree=6)
# ...and minimal R_G(X)-module generators of the covariant module M_G(X, Y).
covariants = covariant_generators(X, Y, max_degree=6)

print(invariants.counts_by_degree())          # generators per degree
print(invariant_hilbert_series(X, 6))         # dim R_G(X)_d for each d
```

The returned `Covariant` objects are callable.  A point of `X` is given in
*isotypic coordinates*: one array per component, of shape
`(multiplicity, dim H_irrep)`, optionally with a leading batch axis.  A
single-component representation may be passed as a bare array.

```python
vector = Representation.irrep(theory, 1)                  # the l=1 representation
m = covariant_generators(vector, vector, max_degree=1)[0] # the identity covariant
m(np.array([1.0, 2.0, 3.0]))                              # -> array, the value in H_1

invs = invariant_generators(vector, max_degree=4)
r = np.concatenate(invs.evaluate(np.array([1.0, 2.0, 3.0])), axis=-1)  # invariant features
```

For the learning ansatz `F(x) = sum_i N_i(r(x)) m_i(x)`, evaluate the covariant
generators and scatter them into the codomain with `combine`/`assemble`:

```python
gens = covariant_generators(vector, vector, max_degree=4)
coefficients = np.ones(len(gens))          # e.g. the outputs N_i(r(x)) of a network
y = gens.combine(coefficients).evaluate(np.array([1.0, 2.0, 3.0]))   # value in Y
```

Use the optional `to_isotypic` / `from_isotypic` maps on a `Representation` to work
in a user ambient basis (then pass `coordinates="ambient"` / `output="ambient"`).

### Distinctions

* `invariant_generators(X)` returns **algebra** generators of `R_G(X)`.  It is *not*
  the same as `covariant_generators(X, trivial)`, which returns the single module
  generator `1` of `R_G(X)` as a module over itself.
* `invariant_basis` / `covariant_basis` return **vector-space** bases (one degree
  via `degree=d`, or all degrees `<= D` via `max_degree=D`).
* `*_dimension` / `*_hilbert_series` report graded dimensions; they are computed
  combinatorially and need no group-specific Molien series.

### Options

`Options(modulus=..., seed=..., probe_overshoot=...)` controls the randomized
finite-field rank selection used during construction (evaluation is always exact
over `C`).  `modulus` must be prime; when omitted it is auto-selected as a prime
greater than the degree bound, in the `1000 < p < 10000` range recommended in
`docs/theory.tex`.  `2521` is a typical explicit choice.  Construction is
deterministic given `(modulus, seed)`.  Call `collection.verify()` to re-check
linear independence over a fresh prime field.

## Low-level pipeline

The group-agnostic `core` entry points remain available for advanced use:

```python
from equivariant_polynomials import (
    SO3RepresentationTheory,
    extract_independent_generators,
    hilbert_series_so3,
    stream_isotypic_data_tree,
)

theory = SO3RepresentationTheory()
generators = extract_independent_generators(
    theory,
    input_irreps=(1,),
    input_multiplicities=(1,),
    output_irrep=0,
    max_degree=3,
    probe_target=lambda dimensions, _output_dimension: dimensions,
    degree_limit=lambda degree: degree // 2,
    random_seed=12345,
    modulus=2521,
    first_generator_degree=1,
)
assert tuple(map(len, generators)) == hilbert_series_so3((1,), (1,), 0, 3)
```

For profiling-style checks, time the high-level `invariant_generators` /
`covariant_generators` calls directly; see `docs/examples.ipynb` for a worked
SO(3) example.  For finite-field arithmetic,
choose a prime modulus `p` with `p > max_degree`; for a single-degree call, use
that degree as the maximum.  The Waring grid imposes no root-of-unity congruence
on `p`, but very small primes can still be bad for randomized finite-field rank
probes.  The current suggested heuristic is `1000 < p < 10000`; `2521` is a
typical choice.
