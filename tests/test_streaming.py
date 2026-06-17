from __future__ import annotations

import numpy as np

from equivariant_polynomials.core.streaming import stream_independent_candidates


def test_stream_independent_candidates_stops_after_target_rank() -> None:
    calls = []

    def evaluate_batch(batch: tuple[int, ...]) -> np.ndarray:
        calls.append(batch)
        return np.asarray(
            [[1, 1], [batch[0] + 1, batch[1] + 1]],
            dtype=np.uint64,
        )

    selected, rank = stream_independent_candidates(
        tuple(range(10)),
        evaluate_batch,
        dimension=2,
        row_count=2,
        modulus=17,
        random_seed=0,
        batch_size=2,
    )

    assert len(calls) == 1
    assert selected == calls[0]
    assert rank == 2
