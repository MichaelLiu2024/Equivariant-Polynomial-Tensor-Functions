from __future__ import annotations

import numpy as np

from equivariant_polynomials.core.streaming import (
    stream_batches,
    stream_independent_candidates,
)


def test_stream_independent_candidates_stops_after_target_rank() -> None:
    calls = []

    def evaluate_batch(batch: tuple[int, ...]) -> np.ndarray:
        calls.append(batch)
        return np.asarray(
            [[1, 1], [batch[0] + 1, batch[1] + 1]],
            dtype=np.uint64,
        )

    selected, rank = stream_independent_candidates(
        stream_batches(range(10), batch_size=2),
        evaluate_batch,
        dimension=2,
        row_count=2,
        modulus=17,
    )

    assert len(calls) == 1
    assert selected == calls[0]
    assert rank == 2
