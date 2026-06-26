"""Evaluators for abstract isotypic basis elements."""

from __future__ import annotations

from collections.abc import Hashable
from functools import cache
from itertools import product
from math import comb, factorial, prod

import numpy as np

from .combinatorics import arithmetic_dtype, reduce_modulo
from .protocols import RepresentationTheory
from .types import Irrep, IsotypicLeaf, SSYT, TensorTrain, TensorTrainCore, TensorTree

_INTEGER_PROBE_BOUND = 2**16


def _sample_probe_array(
    rng: np.random.Generator,
    shape: tuple[int, ...],
    modulus: int,
) -> np.ndarray:
    high = modulus if modulus != 0 else _INTEGER_PROBE_BOUND
    probe = rng.integers(0, high, size=shape, dtype=np.uint64)
    return probe.astype(arithmetic_dtype(modulus), copy=False)


@cache
def _clebsch_gordan_matrices(
    theory: RepresentationTheory,
    core: TensorTrainCore,
    modulus: int,
) -> tuple[tuple[int, int, int], np.ndarray, np.ndarray]:
    tensor = theory.clebsch_gordan_tensor(core, modulus)
    i, j, k = tensor.shape
    return (
        tensor.shape,
        tensor.reshape(i, j * k),
        tensor.transpose(1, 0, 2).reshape(j, i * k),
    )


@cache
def _fused_clebsch_gordan_matrices(
    theory: RepresentationTheory,
    cores: tuple[TensorTrainCore, ...],
    modulus: int,
) -> tuple[tuple[int, int, int], np.ndarray, np.ndarray, tuple[int, ...]]:
    """Clebsch-Gordan matrices for several couplings that share ``left``/``right``.

    The per-coupling tensors are concatenated along the output axis so one
    contraction produces every child at once; the returned output dimensions say
    where to split the fused result.
    """
    if len(cores) == 1:
        clebsch_gordan_shape, left_matrix, right_matrix = _clebsch_gordan_matrices(theory, cores[0], modulus)
        return clebsch_gordan_shape, left_matrix, right_matrix, (clebsch_gordan_shape[2],)
    tensors = [theory.clebsch_gordan_tensor(core, modulus) for core in cores]
    combined = np.concatenate(tensors, axis=2)
    i, j, k = combined.shape
    return (
        (i, j, k),
        combined.reshape(i, j * k),
        combined.transpose(1, 0, 2).reshape(j, i * k),
        tuple(tensor.shape[2] for tensor in tensors),
    )


def _partial_contraction(
    vectors: np.ndarray,
    matrix: np.ndarray,
    shape: tuple[int, int],
) -> np.ndarray:
    return (vectors.reshape(-1, vectors.shape[-1]) @ matrix).reshape(
        *vectors.shape[:-1],
        *shape,
    )


def _prepend_unit_factor_axes(
    values: np.ndarray,
    count: int,
) -> np.ndarray:
    if count <= 0:
        return values
    return values.reshape((values.shape[0],) + (1,) * count + values.shape[1:])


def _evaluate_tensor_train_batch_multi(
    theory: RepresentationTheory,
    tensor_train: TensorTrain,
    vectors: tuple[np.ndarray, ...],
    modulus: int,
) -> np.ndarray:
    result = vectors[0]
    for i, core in enumerate(tensor_train):
        a = result
        b = vectors[i + 1]
        clebsch_gordan_shape, left_matrix, right_matrix = _clebsch_gordan_matrices(theory, core, modulus)
        num_probes = a.shape[0]
        a_shape = a.shape[1:-1]
        b_shape = b.shape[1:-1]
        # Outer product of the two factor blocks over the shared probe axis:
        # ``a`` gets a trailing singleton standing in for ``b``'s factors and
        # vice versa, so the shared ``"batch"`` primitive broadcasts them apart.
        contracted = _contract_batch(
            a.reshape(num_probes, -1, 1, a.shape[-1]),
            b.reshape(num_probes, 1, -1, b.shape[-1]),
            clebsch_gordan_shape,
            left_matrix,
            right_matrix,
            modulus,
        )
        result = contracted.reshape(num_probes, *a_shape, *b_shape, clebsch_gordan_shape[2])
    return result


def _contract_batch(
    a: np.ndarray,
    b: np.ndarray,
    clebsch_gordan_shape: tuple[int, int, int],
    left_matrix: np.ndarray,
    right_matrix: np.ndarray,
    modulus: int,
) -> np.ndarray:
    """Contract one ``"batch"`` coupling of ``a`` and ``b`` through its Clebsch-
    Gordan matrices, choosing the cheaper of the two contraction orders."""
    ndim_delta = a.ndim - b.ndim
    a_size = a.size // a.shape[-1]
    b_size = b.size // b.shape[-1]
    if b_size * clebsch_gordan_shape[0] < a_size * clebsch_gordan_shape[1]:
        b = _prepend_unit_factor_axes(b, ndim_delta)
        tmp = _partial_contraction(b, right_matrix, (clebsch_gordan_shape[0], clebsch_gordan_shape[2]))
        a = _prepend_unit_factor_axes(a, -ndim_delta)
        result = np.matmul(a[..., None, :], tmp).squeeze(-2)
    else:
        tmp = _partial_contraction(a, left_matrix, (clebsch_gordan_shape[1], clebsch_gordan_shape[2]))
        b = _prepend_unit_factor_axes(b, ndim_delta)
        result = np.matmul(b[..., None, :], tmp).squeeze(-2)
    return reduce_modulo(result, modulus)


def _evaluate_tensor_train_batch(
    theory: RepresentationTheory,
    tensor_train: TensorTrain,
    vectors: tuple[np.ndarray, ...],
    modulus: int,
) -> np.ndarray:
    result = vectors[0]
    for i, core in enumerate(tensor_train):
        clebsch_gordan_shape, left_matrix, right_matrix = _clebsch_gordan_matrices(theory, core, modulus)
        result = _contract_batch(
            result, vectors[i + 1], clebsch_gordan_shape, left_matrix, right_matrix, modulus
        )
    return result


def evaluate_tensor_train(
    theory: RepresentationTheory,
    tensor_train: TensorTrain,
    vectors: tuple[np.ndarray, ...],
    modulus: int,
    mode: str,
) -> np.ndarray:
    """Evaluate a left-associated tensor train on probe batches.

    Raises:
        ValueError: If ``mode`` is not ``"batch"`` or ``"batch_multi"``.
    """
    if mode == "batch":
        evaluate = _evaluate_tensor_train_batch
    elif mode == "batch_multi":
        evaluate = _evaluate_tensor_train_batch_multi
    else:
        raise ValueError(f"unknown core evaluation mode {mode}")
    if not tensor_train:
        return (
            vectors[0].astype(arithmetic_dtype(modulus), copy=False)
            if modulus == 0
            else reduce_modulo(vectors[0], modulus)
        )
    return evaluate(theory, tensor_train, vectors, modulus)


def evaluate_antisymmetrized_tensor_train(
    theory: RepresentationTheory,
    tensor_train: TensorTrain,
    vectors: tuple[np.ndarray, ...],
    modulus: int,
    mode: str,
) -> np.ndarray:
    """Explicitly evaluate the alternating sum of tensor-train contractions."""
    if mode == "batch":
        evaluate = _evaluate_antisymmetrized_tensor_train_batch
    elif mode == "batch_multi":
        evaluate = _evaluate_antisymmetrized_tensor_train_batch_multi
    else:
        raise ValueError(f"unknown core evaluation mode {mode}")

    degree = len(tensor_train) + 1
    if degree == 1:
        return evaluate_tensor_train(theory, tensor_train, vectors, modulus, mode)

    vectors = vectors[:degree]
    permutations = _signed_permutations(degree)
    return evaluate(theory, tensor_train, vectors, permutations, modulus)


def evaluate_tensor_train_batch_dag(
    theory: RepresentationTheory,
    tensor_trains: tuple[TensorTrain, ...],
    factors: tuple[np.ndarray, ...],
    modulus: int,
) -> list[np.ndarray]:
    """Evaluate many left-associated trains in ``"batch"`` mode, sharing prefixes.

    The trains are organized into a prefix trie so each distinct core prefix is
    contracted exactly once; ``factors[i]`` is the ``i``-th input factor (shared
    leading axes, last axis the irrep dimension).  Returns one
    ``(leading..., out_dim)`` array per train, in input order.
    """
    results: list[np.ndarray | None] = [None] * len(tensor_trains)

    def descend(indices: list[int], value: np.ndarray, depth: int) -> None:
        groups: dict[TensorTrainCore, list[int]] = {}
        for index in indices:
            tensor_train = tensor_trains[index]
            if len(tensor_train) == depth:
                results[index] = value
            else:
                groups.setdefault(tensor_train[depth], []).append(index)
        if not groups:
            return
        # Children share ``value`` and the same factor, differing only in their
        # coupling.  Fuse their Clebsch-Gordan tensors into one contraction
        # (concatenated on the output axis), then split the result per child.
        factor = factors[depth + 1]
        cores = tuple(groups)
        clebsch_gordan_shape, left_matrix, right_matrix, output_dimensions = _fused_clebsch_gordan_matrices(
            theory, cores, modulus
        )
        fused = _contract_batch(value, factor, clebsch_gordan_shape, left_matrix, right_matrix, modulus)
        offset = 0
        for core, output_dimension in zip(cores, output_dimensions):
            child = fused[..., offset : offset + output_dimension]
            offset += output_dimension
            descend(groups[core], child, depth + 1)

    if tensor_trains:
        descend(list(range(len(tensor_trains))), factors[0], 0)
    return results  # type: ignore[return-value]


def evaluate_power_basis_batch(
    theory: RepresentationTheory,
    batch: tuple[TensorTrain, ...],
    probe_vectors: tuple[np.ndarray, ...],
    modulus: int,
    antisymmetric: bool,
) -> np.ndarray:
    """Evaluate a batch of symmetric/exterior power trains as syndrome columns.

    Trains share core prefixes via :func:`evaluate_tensor_train_batch_dag`; the
    exterior case antisymmetrizes once over factor order for the whole batch
    rather than per train.  Returns ``(num_probes * out_dim, len(batch))``.
    """
    if antisymmetric and len(probe_vectors) > 1:
        permutations = _signed_permutations(len(probe_vectors))
        factors = tuple(
            np.stack([probe_vectors[permutation[i]] for _, permutation in permutations], axis=1)
            for i in range(len(probe_vectors))
        )
        weights = np.fromiter(
            (sign if sign > 0 else modulus - 1 for sign, _ in permutations),
            dtype=arithmetic_dtype(modulus),
            count=len(permutations),
        )
        values = evaluate_tensor_train_batch_dag(theory, batch, factors, modulus)
        columns = [
            reduce_modulo(np.tensordot(value, weights, axes=((1,), (0,))), modulus)
            for value in values
        ]
    else:
        columns = evaluate_tensor_train_batch_dag(theory, batch, probe_vectors, modulus)
    return np.stack([column.reshape(-1) for column in columns], axis=1)


def _transpose_permuted_factors(
    value: np.ndarray,
    permutation: tuple[int, ...],
    factor_ndims: tuple[int, ...],
) -> np.ndarray:
    groups: dict[int, tuple[int, ...]] = {}
    axis = 1
    for index in permutation:
        width = factor_ndims[index]
        groups[index] = tuple(range(axis, axis + width))
        axis += width
    axes = (0,) + tuple(
        axis for index in range(len(permutation)) for axis in groups[index]
    ) + (value.ndim - 1,)
    return value if axes == tuple(range(value.ndim)) else np.transpose(value, axes)


def _batch_multi_permutation_groups(
    vectors: tuple[np.ndarray, ...],
    permutations: tuple[tuple[int, tuple[int, ...]], ...],
) -> tuple[tuple[tuple[int, tuple[int, ...]], ...], ...]:
    groups = {}
    for sign, permutation in permutations:
        key = tuple(vectors[index].shape[1:] for index in permutation)
        groups.setdefault(key, []).append((sign, permutation))
    return tuple(tuple(group) for group in groups.values())


def _evaluate_antisymmetrized_tensor_train_batch(
    theory: RepresentationTheory,
    tensor_train: TensorTrain,
    vectors: tuple[np.ndarray, ...],
    permutations: tuple[tuple[int, tuple[int, ...]], ...],
    modulus: int,
) -> np.ndarray:
    stacked = tuple(
        np.stack([vectors[permutation[i]] for _, permutation in permutations], axis=1)
        for i in range(len(vectors))
    )
    values = evaluate_tensor_train(theory, tensor_train, stacked, modulus, "batch")
    weights = np.fromiter(
        (sign if sign > 0 else modulus - 1 for sign, _ in permutations),
        dtype=values.dtype,
        count=len(permutations),
    )
    return reduce_modulo(np.tensordot(values, weights, axes=((1,), (0,))), modulus)


def _evaluate_antisymmetrized_tensor_train_batch_multi(
    theory: RepresentationTheory,
    tensor_train: TensorTrain,
    vectors: tuple[np.ndarray, ...],
    permutations: tuple[tuple[int, tuple[int, ...]], ...],
    modulus: int,
) -> np.ndarray:
    num_probes = vectors[0].shape[0]
    factor_ndims = tuple(vector.ndim - 2 for vector in vectors)
    result = None
    for group in _batch_multi_permutation_groups(vectors, permutations):
        permutation_count = len(group)
        stacked = tuple(
            np.stack([vectors[permutation[i]] for _, permutation in group], axis=1)
            .reshape(num_probes * permutation_count, *vectors[group[0][1][i]].shape[1:])
            for i in range(len(vectors))
        )
        values = evaluate_tensor_train(theory, tensor_train, stacked, modulus, "batch_multi")
        values = values.reshape(num_probes, permutation_count, *values.shape[1:])
        if result is None:
            result = np.zeros(
                (
                    num_probes,
                    *(
                        axis
                        for vector in vectors
                        for axis in vector.shape[1:-1]
                    ),
                    values.shape[-1],
                ),
                dtype=values.dtype,
            )
        for i, (sign, permutation) in enumerate(group):
            value = _transpose_permuted_factors(
                values[:, i],
                permutation,
                factor_ndims,
            )
            np.add(result, value if sign > 0 else modulus - value, out=result)
        result = reduce_modulo(result, modulus)
    if result is None:
        raise ValueError("antisymmetrizer has no permutations")
    return result


def sample_tensor_power_probes(
    theory: RepresentationTheory,
    irrep: Irrep,
    degree: int,
    num_probes: int,
    modulus: int,
    random_seed: int,
    antisymmetric: bool,
) -> tuple[np.ndarray, ...]:
    """Sample random probes for the tensor power of an irrep."""
    rng = np.random.default_rng(random_seed)
    irrep_dimension = theory.irrep_dimension(irrep)
    if antisymmetric:
        return tuple(
            _sample_probe_array(
                rng,
                (degree, num_probes, irrep_dimension),
                modulus,
            )
        )
    probe = _sample_probe_array(rng, (num_probes, irrep_dimension), modulus)
    return (probe,) * degree


def sample_isotypic_input_probes(
    theory: RepresentationTheory,
    input_irreps: tuple[Irrep, ...],
    input_multiplicities: tuple[int, ...],
    num_probes: int,
    modulus: int,
    random_seed: int,
) -> tuple[np.ndarray, ...]:
    """Sample random probes for the input representation."""
    rng = np.random.default_rng(random_seed)
    return tuple(
        _sample_probe_array(
            rng,
            (num_probes, multiplicity, theory.irrep_dimension(irrep)),
            modulus,
        )
        for irrep, multiplicity in zip(input_irreps, input_multiplicities)
    )


@cache
def _signed_permutations(
    degree: int,
) -> tuple[tuple[int, tuple[int, ...]], ...]:
    if degree == 0:
        return ((1, ()),)
    last = degree - 1
    return tuple(
        (
            sign if (last - i) % 2 == 0 else -sign,
            permutation[:i] + (last,) + permutation[i:],
        )
        for sign, permutation in _signed_permutations(last)
        for i in range(last, -1, -1)
    )


@cache
def monomial_waring_data(
    powers: tuple[int, ...],
    modulus: int,
) -> tuple[np.ndarray, np.ndarray]:
    """Finite-difference CP grid and coefficients for one monomial."""
    dtype = arithmetic_dtype(modulus)
    rows = tuple(product(*(range(degree + 1) for degree in powers)))
    coefficients = []
    for row in rows:
        coefficient = 1
        for degree, value in zip(powers, row):
            coefficient *= comb(degree, value)
            if (degree - value) % 2:
                coefficient = -coefficient
        coefficients.append(coefficient if modulus == 0 else coefficient % modulus)

    grid = np.asarray(rows, dtype=dtype)
    coefficients = np.asarray(coefficients, dtype=dtype)
    grid.setflags(write=False)
    coefficients.setflags(write=False)
    return grid, coefficients


@cache
def _young_row_waring_data(
    powers: tuple[int, ...],
    modulus: int,
) -> tuple[np.ndarray, np.ndarray]:
    if len(powers) != 1:
        return monomial_waring_data(powers, modulus)

    dtype = arithmetic_dtype(modulus)
    grid = np.ones((1, 1), dtype=dtype)
    coefficient = factorial(powers[0])
    coefficients = np.asarray(
        [coefficient if modulus == 0 else coefficient % modulus],
        dtype=dtype,
    )
    grid.setflags(write=False)
    coefficients.setflags(write=False)
    return grid, coefficients


def _align_row_axes(
    values: np.ndarray,
    axes: tuple[int, ...],
    target_axes: tuple[int, ...],
) -> np.ndarray:
    if axes == target_axes:
        return values
    axis_sizes = dict(zip(axes, values.shape[1:-1]))
    return values.reshape(
        values.shape[0],
        *(axis_sizes.get(axis, 1) for axis in target_axes),
        values.shape[-1],
    )


def _contract_expired_row_axes(
    values: np.ndarray,
    active_axes: tuple[int, ...],
    next_height: int,
    row_coeffs: tuple[np.ndarray, ...],
    modulus: int,
) -> tuple[np.ndarray, tuple[int, ...]]:
    active = list(active_axes)
    for position in range(len(active) - 1, -1, -1):
        axis = active[position]
        if axis < next_height:
            continue
        values = np.tensordot(values, row_coeffs[axis], axes=((position + 1,), (0,)))
        values = reduce_modulo(values, modulus)
        del active[position]
    return values, tuple(active)


def _sum_weighted_tensor_tree_grid(
    theory: RepresentationTheory,
    tensor_tree: TensorTree,
    leaves: tuple[np.ndarray, ...],
    leaf_heights: tuple[int, ...],
    row_coeffs: tuple[np.ndarray, ...],
    modulus: int,
) -> np.ndarray:
    result = leaves[0]
    active_axes = tuple(range(leaf_heights[0]))
    next_height = max(leaf_heights[1:], default=0)
    result, active_axes = _contract_expired_row_axes(
        result,
        active_axes,
        next_height,
        row_coeffs,
        modulus,
    )

    for i, core in enumerate(tensor_tree.interior_tensor_train):
        leaf = leaves[i + 1]
        leaf_axes = tuple(range(leaf_heights[i + 1]))
        target_axes = tuple(sorted(set(active_axes).union(leaf_axes)))
        result = evaluate_tensor_train(
            theory,
            (core,),
            (
                _align_row_axes(result, active_axes, target_axes),
                _align_row_axes(leaf, leaf_axes, target_axes),
            ),
            modulus,
            "batch",
        )
        active_axes = target_axes
        next_height = max(leaf_heights[i + 2 :], default=0)
        result, active_axes = _contract_expired_row_axes(
            result,
            active_axes,
            next_height,
            row_coeffs,
            modulus,
        )
    return result


def evaluate_young_symmetrized_tensor_tree(
    theory: RepresentationTheory,
    tensor_tree: TensorTree,
    ssyt: SSYT,
    probe_batches: np.ndarray,
    modulus: int,
) -> np.ndarray:
    if not ssyt.entries_by_row:
        return np.ones((probe_batches.shape[0], 1), dtype=arithmetic_dtype(modulus))

    row_waring_data = tuple(
        _young_row_waring_data(copies, modulus) for copies in ssyt.copies_by_row
    )
    grids = tuple(grid for grid, _coefficients in row_waring_data)
    symmetrized_rows = tuple(
        reduce_modulo(np.matmul(grid[None, :, :], probe_batches[:, entries, :]), modulus)
        for entries, grid in zip(ssyt.entries_by_row, grids)
    )
    row_coeffs = tuple(coefficients for _grid, coefficients in row_waring_data)

    antisymmetrized_leaves = []
    leaf_heights = []
    for tensor_train in tensor_tree.leaf_tensor_trains:
        if not tensor_train:
            antisymmetrized_leaves.append(symmetrized_rows[0])
            leaf_heights.append(1)
            continue
        antisymmetrized_leaves.append(
            evaluate_antisymmetrized_tensor_train(
                theory,
                tensor_train,
                symmetrized_rows,
                modulus,
                "batch_multi",
            )
        )
        leaf_heights.append(len(tensor_train) + 1)

    return _sum_weighted_tensor_tree_grid(
        theory,
        tensor_tree,
        tuple(antisymmetrized_leaves),
        tuple(leaf_heights),
        row_coeffs,
        modulus,
    )


def evaluate_basis(
    theory: RepresentationTheory,
    leaf: IsotypicLeaf,
    probe_batches_by_input_irrep: tuple[np.ndarray, ...],
    modulus: int,
    young_tree_cache: dict[Hashable, np.ndarray] | None = None,
    probe_window_keys: tuple[Hashable, ...] | None = None,
) -> np.ndarray:
    """Evaluate one isotypic leaf as ``probe x output x column``.

    When ``young_tree_cache`` is supplied, ``probe_window_keys`` must hold one
    hashable identity per input-irrep probe batch (e.g. ``(irrep_index, start)``)
    so Young-tree evaluations can be reused across leaves and probe windows.  A
    cached value computed on more probe rows than requested is sliced to fit.
    """
    if probe_window_keys is None:
        probe_window_keys = (None,) * len(probe_batches_by_input_irrep)
    per_input_irrep_blocks = []
    for trees, ssyts, probe_batch, window_key in zip(
        leaf.leaf_tensor_trees,
        leaf.semistandard_young_tableaux,
        probe_batches_by_input_irrep,
        probe_window_keys,
    ):
        leaf_factor = None
        leaf_column_count = len(trees) * len(ssyts)
        for tree_index, tensor_tree in enumerate(trees):
            for tableau_index, tableau in enumerate(ssyts):
                cache_key = (modulus, window_key, tensor_tree, tableau)
                cached = (
                    young_tree_cache.get(cache_key)
                    if young_tree_cache is not None
                    else None
                )
                if cached is not None and cached.shape[0] >= probe_batch.shape[0]:
                    value = cached[: probe_batch.shape[0]]
                else:
                    value = evaluate_young_symmetrized_tensor_tree(
                        theory,
                        tensor_tree,
                        tableau,
                        probe_batch,
                        modulus,
                    )
                    if young_tree_cache is not None:
                        young_tree_cache[cache_key] = value
                if leaf_factor is None:
                    leaf_factor = np.empty(
                        (value.shape[0], leaf_column_count, value.shape[-1]),
                        dtype=value.dtype,
                    )
                leaf_factor[:, tree_index * len(ssyts) + tableau_index, :] = value
        if leaf_factor is None:
            leaf_factor = np.empty(
                (probe_batch.shape[0], leaf_column_count, 0),
                dtype=arithmetic_dtype(modulus),
            )
        per_input_irrep_blocks.append(leaf_factor)

    out = None
    column_offset = 0
    for tensor_train in leaf.interior_tensor_trains:
        value = evaluate_tensor_train(
            theory,
            tensor_train,
            tuple(per_input_irrep_blocks),
            modulus,
            "batch_multi",
        )
        num_probes = value.shape[0]
        output_dimension = value.shape[-1]
        column_count = prod(value.shape[1:-1])
        if out is None:
            out = np.empty(
                (
                    num_probes,
                    output_dimension,
                    len(leaf.interior_tensor_trains) * column_count,
                ),
                dtype=value.dtype,
            )
        out[:, :, column_offset : column_offset + column_count] = value.reshape(
            num_probes,
            column_count,
            output_dimension,
        ).transpose(0, 2, 1)
        column_offset += column_count

    if out is None:
        return np.empty((0,), dtype=arithmetic_dtype(modulus))
    return out


__all__ = (
    "sample_tensor_power_probes",
    "sample_isotypic_input_probes",
    "evaluate_tensor_train",
    "evaluate_antisymmetrized_tensor_train",
    "evaluate_power_basis_batch",
    "evaluate_young_symmetrized_tensor_tree",
    "evaluate_basis",
    "monomial_waring_data",
)
