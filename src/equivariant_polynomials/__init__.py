"""Equivariant-polynomial representation-theory algorithms.

A group ``RepresentationTheory`` backend (``groups/``) drives the group-agnostic
``core`` pipeline: stream an isotypic data tree (``isotypic``), build abstract
tensor bases (``bases``), evaluate them with random probes (``evaluators``), and
extract minimal homogeneous generators from the syndromes (``generators``). The
main entry points are ``stream_isotypic_data_tree`` and
``extract_independent_generators``.
"""

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
    "RepresentationTheory",
    "SO2RepresentationTheory",
    "SO3RepresentationTheory",
    "extract_independent_generators",
    "stream_isotypic_data_tree",
    "hilbert_series_so2",
    "hilbert_series_so3",
    "hilbert_series_so3_multigraded",
    "weak_compositions",
    "Irrep",
    "Partition",
    "SSYT",
    "TensorTrain",
    "TensorTrainCore",
    "TensorTree",
    "IsotypicLeaf",
)
