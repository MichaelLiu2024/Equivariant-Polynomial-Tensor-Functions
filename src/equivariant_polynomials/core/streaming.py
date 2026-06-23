"""Shared batched streaming helpers for randomized basis selection."""

from __future__ import annotations

from collections.abc import Callable, Iterable, Iterator, Sequence
from dataclasses import dataclass
from itertools import islice
from typing import TypeVar

import numpy as np

from .combinatorics import arithmetic_dtype, pivot_columns

STREAM_BATCH_SIZE = 64

_T = TypeVar("_T")


@dataclass(frozen=True, slots=True)
class StreamedSelection:
    indices: tuple[int, ...]
    rank: int


def stream_batches(
    items: Iterable[_T],
    batch_size: int = STREAM_BATCH_SIZE,
) -> Iterator[tuple[_T, ...]]:
    if batch_size <= 0:
        raise ValueError("batch_size must be positive")

    item_iterator = iter(items)
    while batch := tuple(islice(item_iterator, batch_size)):
        yield batch


def shuffled_stream_batches(
    items: Sequence[_T],
    random_seed: int,
    batch_size: int = STREAM_BATCH_SIZE,
) -> Iterator[tuple[_T, ...]]:
    order = np.random.default_rng(random_seed).permutation(len(items))
    yield from stream_batches((items[int(index)] for index in order), batch_size)


def independent_column_indices(
    basis: np.ndarray,
    columns: np.ndarray,
    limit: int,
    modulus: int,
) -> StreamedSelection:
    if columns.shape[1] == 0 or limit == 0:
        return StreamedSelection((), basis.shape[1])

    start = basis.shape[1]
    matrix = columns if start == 0 else np.concatenate((basis, columns), axis=1)
    pivots = pivot_columns(matrix, modulus)
    indices = tuple(pivot - start for pivot in pivots if pivot >= start)[:limit]
    return StreamedSelection(indices, len(pivots))


def stream_independent_candidates(
    candidates: Sequence[_T],
    evaluate_batch: Callable[[tuple[_T, ...]], np.ndarray],
    dimension: int,
    row_count: int,
    modulus: int,
    random_seed: int,
    batch_size: int = STREAM_BATCH_SIZE,
) -> tuple[tuple[_T, ...], int]:
    basis = np.empty((row_count, 0), dtype=arithmetic_dtype(modulus))
    selected: list[_T] = []
    last_rank = 0

    for candidate_batch in shuffled_stream_batches(
        candidates,
        random_seed,
        batch_size,
    ):
        columns = evaluate_batch(candidate_batch)
        selection = independent_column_indices(
            basis,
            columns,
            dimension - len(selected),
            modulus,
        )
        last_rank = max(last_rank, selection.rank)
        if not selection.indices:
            continue

        selected.extend(candidate_batch[index] for index in selection.indices)
        if len(selected) < dimension:
            basis = np.concatenate(
                (basis, columns[:, selection.indices]),
                axis=1,
            )
        if len(selected) == dimension:
            break

    return tuple(selected), last_rank


__all__ = (
    "STREAM_BATCH_SIZE",
    "StreamedSelection",
    "stream_batches",
    "shuffled_stream_batches",
    "independent_column_indices",
    "stream_independent_candidates",
)
