"""Evaluators for abstract isotypic basis elements."""

from __future__ import annotations

from collections.abc import Hashable
from functools import cache
from itertools import product
from math import comb, factorial, prod

import numpy as np

from .combinatorics import arithmetic_dtype, cond_mod
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
    cores: TensorTrain,
    vectors: tuple[np.ndarray, ...],
    modulus: int,
) -> np.ndarray:
    result = vectors[0]
    for i, core in enumerate(cores):
        a = result
        b = vectors[i + 1]
        cg_shape, left_mat, right_mat = _clebsch_gordan_matrices(theory, core, modulus)
        probe_count = a.shape[0]
        a_shape = a.shape[1:-1]
        b_shape = b.shape[1:-1]
        a = a.reshape(probe_count, -1, a.shape[-1])
        b = b.reshape(probe_count, -1, b.shape[-1])

        if b.shape[1] * cg_shape[0] < a.shape[1] * cg_shape[1]:
            tmp = _partial_contraction(b, right_mat, (cg_shape[0], cg_shape[2]))
            result = np.matmul(
                a[:, :, None, None, :],
                tmp[:, None, :, :, :],
            )[:, :, :, 0, :]
        else:
            tmp = _partial_contraction(a, left_mat, (cg_shape[1], cg_shape[2]))
            result = np.matmul(
                b[:, None, :, None, :],
                tmp[:, :, None, :, :],
            )[:, :, :, 0, :]

        result = result.reshape(probe_count, *a_shape, *b_shape, cg_shape[2])
        result = cond_mod(result, modulus)
    return result


def _evaluate_tensor_train_batch(
    theory: RepresentationTheory,
    cores: TensorTrain,
    vectors: tuple[np.ndarray, ...],
    modulus: int,
) -> np.ndarray:
    result = vectors[0]
    for i, core in enumerate(cores):
        a = result
        b = vectors[i + 1]
        cg_shape, left_mat, right_mat = _clebsch_gordan_matrices(theory, core, modulus)
        ndim_delta = a.ndim - b.ndim

        a_size = a.size // a.shape[-1]
        b_size = b.size // b.shape[-1]
        if b_size * cg_shape[0] < a_size * cg_shape[1]:
            b = _prepend_unit_factor_axes(b, ndim_delta)
            tmp = _partial_contraction(b, right_mat, (cg_shape[0], cg_shape[2]))
            a = _prepend_unit_factor_axes(a, -ndim_delta)
            result = np.matmul(a[..., None, :], tmp).squeeze(-2)
        else:
            tmp = _partial_contraction(a, left_mat, (cg_shape[1], cg_shape[2]))
            b = _prepend_unit_factor_axes(b, ndim_delta)
            result = np.matmul(b[..., None, :], tmp).squeeze(-2)
        result = cond_mod(result, modulus)
    return result


def evaluate_tensor_train(
    theory: RepresentationTheory,
    cores: TensorTrain,
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
    if not cores:
        return (
            vectors[0].astype(arithmetic_dtype(modulus), copy=False)
            if modulus == 0
            else cond_mod(vectors[0], modulus)
        )
    return evaluate(theory, cores, vectors, modulus)


def evaluate_antisymmetrized_tensor_train(
    theory: RepresentationTheory,
    cores: TensorTrain,
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

    degree = len(cores) + 1
    if degree == 1:
        return evaluate_tensor_train(theory, cores, vectors, modulus, mode)

    vectors = vectors[:degree]
    permutations = _signed_permutations(degree)
    return evaluate(theory, cores, vectors, permutations, modulus)


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
    cores: TensorTrain,
    vectors: tuple[np.ndarray, ...],
    permutations: tuple[tuple[int, tuple[int, ...]], ...],
    modulus: int,
) -> np.ndarray:
    stacked = tuple(
        np.stack([vectors[permutation[i]] for _, permutation in permutations], axis=1)
        for i in range(len(vectors))
    )
    values = evaluate_tensor_train(theory, cores, stacked, modulus, "batch")
    weights = np.fromiter(
        (sign if sign > 0 else modulus - 1 for sign, _ in permutations),
        dtype=values.dtype,
        count=len(permutations),
    )
    return cond_mod(np.tensordot(values, weights, axes=((1,), (0,))), modulus)


def _evaluate_antisymmetrized_tensor_train_batch_multi(
    theory: RepresentationTheory,
    cores: TensorTrain,
    vectors: tuple[np.ndarray, ...],
    permutations: tuple[tuple[int, tuple[int, ...]], ...],
    modulus: int,
) -> np.ndarray:
    probe_count = vectors[0].shape[0]
    factor_ndims = tuple(vector.ndim - 2 for vector in vectors)
    result = None
    for group in _batch_multi_permutation_groups(vectors, permutations):
        permutation_count = len(group)
        stacked = tuple(
            np.stack([vectors[permutation[i]] for _, permutation in group], axis=1)
            .reshape(probe_count * permutation_count, *vectors[group[0][1][i]].shape[1:])
            for i in range(len(vectors))
        )
        values = evaluate_tensor_train(theory, cores, stacked, modulus, "batch_multi")
        values = values.reshape(probe_count, permutation_count, *values.shape[1:])
        if result is None:
            result = np.zeros(
                (
                    probe_count,
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
        result = cond_mod(result, modulus)
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
    coeff = np.asarray(coefficients, dtype=dtype)
    grid.setflags(write=False)
    coeff.setflags(write=False)
    return grid, coeff


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
    coeff = np.asarray(
        [coefficient if modulus == 0 else coefficient % modulus],
        dtype=dtype,
    )
    grid.setflags(write=False)
    coeff.setflags(write=False)
    return grid, coeff


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
        values = cond_mod(values, modulus)
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
        cond_mod(np.matmul(grid[None, :, :], probe_batches[:, entries, :]), modulus)
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


def _young_tree_cache_key(
    modulus: int,
    probes: np.ndarray,
    tensor_tree: TensorTree,
    tableau: SSYT,
) -> tuple[Hashable, ...]:
    base = probes
    while isinstance(base.base, np.ndarray):
        base = base.base
    offset = probes.ctypes.data - base.ctypes.data
    row_stride = probes.strides[0] if probes.ndim else 1
    row_offset = (
        offset // row_stride
        if row_stride and offset % row_stride == 0
        else offset
    )
    return (
        modulus,
        base.ctypes.data,
        row_offset,
        base.shape,
        probes.shape[1:],
        probes.strides,
        probes.dtype.str,
        tensor_tree,
        tableau,
    )


def evaluate_basis(
    theory: RepresentationTheory,
    leaf: IsotypicLeaf,
    probe_batches_by_input_irrep: tuple[np.ndarray, ...],
    modulus: int,
    young_tree_cache: dict[Hashable, np.ndarray] | None = None,
) -> np.ndarray:
    """Evaluate one isotypic leaf as ``probe x output x column``."""
    per_input_irrep_blocks = []
    for trees, ssyts, probes in zip(
        leaf.leaf_tensor_trees,
        leaf.semi_standard_young_tableaux,
        probe_batches_by_input_irrep,
    ):
        leaf_factor = None
        leaf_column_count = len(trees) * len(ssyts)
        for tree_index, tensor_tree in enumerate(trees):
            for tableau_index, tableau in enumerate(ssyts):
                cache_key = _young_tree_cache_key(
                    modulus,
                    probes,
                    tensor_tree,
                    tableau,
                )
                cached = (
                    young_tree_cache.get(cache_key)
                    if young_tree_cache is not None
                    else None
                )
                if cached is not None and cached.shape[0] >= probes.shape[0]:
                    value = cached[: probes.shape[0]]
                else:
                    value = evaluate_young_symmetrized_tensor_tree(
                        theory,
                        tensor_tree,
                        tableau,
                        probes,
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
                (probes.shape[0], leaf_column_count, 0),
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
        probe_count = value.shape[0]
        output_dim = value.shape[-1]
        column_count = prod(value.shape[1:-1])
        if out is None:
            out = np.empty(
                (
                    probe_count,
                    output_dim,
                    len(leaf.interior_tensor_trains) * column_count,
                ),
                dtype=value.dtype,
            )
        out[:, :, column_offset : column_offset + column_count] = value.reshape(
            probe_count,
            column_count,
            output_dim,
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
    "evaluate_young_symmetrized_tensor_tree",
    "evaluate_basis",
    "monomial_waring_data",
)
