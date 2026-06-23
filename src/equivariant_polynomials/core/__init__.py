"""Group-agnostic building blocks for equivariant polynomial bases."""

from . import bases as _bases
from . import combinatorics as _combinatorics
from . import evaluators as _evaluators
from . import generators as _generators
from . import isotypic as _isotypic
from . import protocols as _protocols
from . import types as _types
from .bases import *
from .combinatorics import *
from .evaluators import *
from .generators import *
from .isotypic import *
from .protocols import *
from .types import *

_INTERNAL_EXPORTS = {"DegreeLimit", "ProbeTarget"}
for _name in _INTERNAL_EXPORTS:
    globals().pop(_name, None)

__all__ = tuple(
    dict.fromkeys(
        name
        for name in (
            *_types.__all__,
            *_protocols.__all__,
            *_combinatorics.__all__,
            *_evaluators.__all__,
            *_generators.__all__,
            *_bases.__all__,
            *_isotypic.__all__,
        )
        if name not in _INTERNAL_EXPORTS
    )
)
