"""Equivariant-polynomial representation-theory algorithms."""

from . import core as _core
from .groups import so2 as _so2
from .groups import so3 as _so3
from .core import *
from .groups.so2 import *
from .groups.so3 import *

_CORE_PRIVATE_EXPORTS = {
    "compute_syndromes",
    "pivot_columns",
    "ragged_multi_index",
    "row_kronecker_product",
}
for _name in _CORE_PRIVATE_EXPORTS:
    globals().pop(_name, None)

__all__ = (
    *_so2.__all__,
    *_so3.__all__,
    *(name for name in _core.__all__ if name not in _CORE_PRIVATE_EXPORTS),
)
