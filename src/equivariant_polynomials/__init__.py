"""Equivariant-polynomial representation-theory algorithms.

The recommended entry point is the high-level :mod:`equivariant_polynomials.api`,
re-exported here.  Specify input/output representations by their isotypic
decomposition with :class:`Representation`, then call :func:`covariant_basis`,
:func:`covariant_generators`, :func:`invariant_generators`, and friends.  The
returned :class:`Covariant` objects are callable and evaluate the equivariant
polynomials at points given in isotypic coordinates::

    from equivariant_polynomials import (
        SO3RepresentationTheory, Representation,
        invariant_generators, covariant_generators,
    )

    theory = SO3RepresentationTheory()
    vector = Representation.irrep(theory, 1)              # the l=1 representation
    invariants = invariant_generators(vector, max_degree=4)
    covariants = covariant_generators(vector, vector, max_degree=4)

Underneath, a group ``RepresentationTheory`` backend (``groups/``) drives the
group-agnostic ``core`` pipeline: stream an isotypic data tree (``isotypic``),
build abstract tensor bases (``bases``), evaluate them with random probes
(``evaluators``), and extract minimal homogeneous generators from the syndromes
(``generators``).  Those low-level entry points (``stream_isotypic_data_tree``,
``extract_independent_generators``) remain available for advanced use.
"""

from .api import (
    Covariant,
    CovariantCollection,
    CovariantCombination,
    IsotypicComponent,
    Options,
    Representation,
    covariant_basis,
    covariant_dimension,
    covariant_generators,
    covariant_hilbert_series,
    invariant_basis,
    invariant_dimension,
    invariant_generators,
    invariant_hilbert_series,
    irreducible_representation,
    trivial_representation,
)
from .core import (
    Irrep,
    IsotypicLeaf,
    Partition,
    RepresentationTheory,
    SSYT,
    TensorTrain,
    TensorTrainCore,
    TensorTree,
    extract_independent_generators,
    stream_isotypic_data_tree,
    weak_compositions,
)
from .groups.so2 import SO2RepresentationTheory, hilbert_series_so2
from .groups.so3 import (
    SO3RepresentationTheory,
    hilbert_series_so3,
    hilbert_series_so3_multigraded,
)

__all__ = (
    # high-level API
    "Representation",
    "IsotypicComponent",
    "Options",
    "Covariant",
    "CovariantCollection",
    "CovariantCombination",
    "trivial_representation",
    "irreducible_representation",
    "covariant_basis",
    "invariant_basis",
    "covariant_generators",
    "invariant_generators",
    "covariant_dimension",
    "invariant_dimension",
    "covariant_hilbert_series",
    "invariant_hilbert_series",
    # group backends
    "RepresentationTheory",
    "SO2RepresentationTheory",
    "SO3RepresentationTheory",
    "hilbert_series_so2",
    "hilbert_series_so3",
    "hilbert_series_so3_multigraded",
    # low-level pipeline
    "extract_independent_generators",
    "stream_isotypic_data_tree",
    "weak_compositions",
    "Irrep",
    "Partition",
    "SSYT",
    "TensorTrain",
    "TensorTrainCore",
    "TensorTree",
    "IsotypicLeaf",
)
