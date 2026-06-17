from __future__ import annotations

from dataclasses import FrozenInstanceError, is_dataclass

import pytest

from equivariant_polynomials.core.types import TensorTrainCore


def test_tensor_train_core_is_frozen_slots_dataclass() -> None:
    core = TensorTrainCore(1, 2, 3, 4)

    assert is_dataclass(core)
    assert (core.left, core.right, core.out, core.multiplicity) == (1, 2, 3, 4)
    assert not hasattr(core, "__dict__")
    with pytest.raises(FrozenInstanceError):
        setattr(core, "left", 0)
