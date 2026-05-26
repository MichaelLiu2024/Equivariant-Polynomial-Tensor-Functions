"""Evaluators for abstract isotypic basis elements."""

from __future__ import annotations

from collections.abc import Hashable
from functools import cache, reduce
from itertools import product
from math import prod

import numpy as np
import sympy as sp

from .protocols import RepresentationTheory
from .types import Irrep, IsotypicLeaf, SSYT, TensorTrain, TensorTree

_INTEGER_PROBE_BOUND = 2**16
_UINT64_MAX = np.iinfo(np.uint64).max


def _reduce_mod(
    values: np.ndarray,
    modulus: int,
) -> np.ndarray:
    """Reduce values modulo modulus, modifying the input array in-place if possible."""
    if modulus == 0:
        return values
    return (
        np.remainder(values, modulus, out=values)
        if values.flags.writeable
        else values % modulus
    )


def _prepare_clebsch_gordan_tensor(
    values: np.ndarray,
    modulus: int,
) -> np.ndarray:
    """Prepare a cached complex128 Clebsch-Gordan tensor for arithmetic."""
    if modulus == 0:
        return values
    return np.remainder(np.rint(values.real), modulus).astype(np.uint64)


def _partial_contraction_may_overflow(
    core: np.ndarray,
    modulus: int,
) -> bool:
    if modulus == 0:
        return False
    max_value = modulus - 1
    contraction_bound = core.shape[0] * core.shape[1] * max_value ** 3
    return contraction_bound > _UINT64_MAX


def _left_partial_contraction(
    vectors: np.ndarray,
    core: np.ndarray,
) -> np.ndarray:
    """Contract left vectors into ``core`` while preserving factor axes."""
    i, j, k = core.shape
    leading_shape = vectors.shape[:-1]
    matrix = core.reshape(i, j * k)
    flat_vectors = vectors.reshape(-1, vectors.shape[-1])
    return (flat_vectors @ matrix).reshape(*leading_shape, j, k)


def _right_partial_contraction(
    vectors: np.ndarray,
    core: np.ndarray,
) -> np.ndarray:
    """Contract right vectors into ``core`` while preserving factor axes."""
    i, j, k = core.shape
    leading_shape = vectors.shape[:-1]
    matrix = core.transpose(1, 0, 2).reshape(j, i * k)
    flat_vectors = vectors.reshape(-1, vectors.shape[-1])
    return (flat_vectors @ matrix).reshape(*leading_shape, i, k)


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
        tensor = _prepare_clebsch_gordan_tensor(
            theory.clebsch_gordan_tensor(core),
            modulus,
        )
        probe_count = a.shape[0]
        a_shape = a.shape[1:-1]
        b_shape = b.shape[1:-1]
        a = a.reshape(probe_count, -1, a.shape[-1])
        b = b.reshape(probe_count, -1, b.shape[-1])

        reduce_partial = _partial_contraction_may_overflow(tensor, modulus)
        if b.shape[1] * tensor.shape[0] < a.shape[1] * tensor.shape[1]:
            tmp = _right_partial_contraction(b, tensor)
            if reduce_partial:
                tmp = _reduce_mod(tmp, modulus)
            result = np.matmul(
                a[:, :, None, None, :],
                tmp[:, None, :, :, :],
            )[:, :, :, 0, :]
        else:
            tmp = _left_partial_contraction(a, tensor)
            if reduce_partial:
                tmp = _reduce_mod(tmp, modulus)
            result = np.matmul(
                b[:, None, :, None, :],
                tmp[:, :, None, :, :],
            )[:, :, :, 0, :]

        result = _reduce_mod(
            result.reshape(probe_count, *a_shape, *b_shape, tensor.shape[2]),
            modulus,
        )
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
        tensor = _prepare_clebsch_gordan_tensor(
            theory.clebsch_gordan_tensor(core),
            modulus,
        )
        ndim_delta = a.ndim - b.ndim
        reduce_partial = _partial_contraction_may_overflow(tensor, modulus)

        a_size = a.size // a.shape[-1]
        b_size = b.size // b.shape[-1]
        if b_size * tensor.shape[0] < a_size * tensor.shape[1]:
            b = _prepend_unit_factor_axes(b, ndim_delta)
            tmp = _right_partial_contraction(b, tensor)
            if reduce_partial:
                tmp = _reduce_mod(tmp, modulus)
            a = _prepend_unit_factor_axes(a, -ndim_delta)
            result = _reduce_mod(
                np.matmul(a[..., None, :], tmp).squeeze(-2),
                modulus,
            )
        else:
            tmp = _left_partial_contraction(a, tensor)
            if reduce_partial:
                tmp = _reduce_mod(tmp, modulus)
            b = _prepend_unit_factor_axes(b, ndim_delta)
            result = _reduce_mod(
                np.matmul(b[..., None, :], tmp).squeeze(-2),
                modulus,
            )
    return result


def evaluate_tensor_train(
    theory: RepresentationTheory,
    cores: TensorTrain,
    vectors: tuple[np.ndarray, ...],
    modulus: int,
    mode: str,
) -> np.ndarray:
    """Evaluate a left-associated tensor train on probe batches.

    Let ``cores = (c_0, ..., c_{n-1})`` and
    ``vectors = (V_0, ..., V_n)``. Axis ``p`` is the probe axis shared by every
    ``V_j``. Each ``V_j`` has shape ``(P, *F_j, d_j)``: ``F_j`` is the tuple of
    factor axes for choices such as multiplicities or Waring-grid rows, and
    the final axis ``a_j`` is a coordinate axis for the corresponding irrep.

    For core ``c_i``, write
    ``C_i[x_i, y_i, z_i] = theory.clebsch_gordan_tensor(c_i)``. The axes are:
    ``x_i`` for ``c_i.left``, ``y_i`` for ``c_i.right``, and ``z_i`` for
    ``c_i.out``. Starting from ``A_0 = V_0``, the left-associated recurrence is

    ``A_{i+1}[p, ..., z_i] =
    sum_{x_i, y_i} A_i[p, ..., x_i] V_{i+1}[p, ..., y_i] C_i[x_i, y_i, z_i]``.

    In ``"batch"`` mode, the omitted factor multi-indices are aligned and
    broadcast at each multiplication, so the output has axes
    ``(p, *broadcast(F_0, ..., F_n), z_{n-1})``. In ``"batch_multi"`` mode, the
    factor axes stay independent and ordered by input vector, giving
    ``(p, *F_0, *F_1, ..., *F_n, z_{n-1})``.

    Arithmetic is unreduced when ``modulus == 0`` and is reduced modulo
    ``modulus`` otherwise. If ``n == 0``, the tensor train is the identity and
    ``V_0`` is returned, cast to ``complex128`` in characteristic zero.

    Raises:
        ValueError: If ``mode`` is not ``"batch"`` or ``"batch_multi"``.
    """
    if mode not in {"batch", "batch_multi"}:
        raise ValueError(f"unknown core evaluation mode {mode}")
    if not cores:
        return (
            vectors[0].astype(np.complex128, copy=False)
            if modulus == 0
            else vectors[0]
        )

    if mode == "batch_multi":
        return _evaluate_tensor_train_batch_multi(theory, cores, vectors, modulus)
    return _evaluate_tensor_train_batch(theory, cores, vectors, modulus)


def evaluate_antisymmetrized_tensor_train(
    theory: RepresentationTheory,
    cores: TensorTrain,
    vectors: tuple[np.ndarray, ...],
    modulus: int,
    mode: str,
) -> np.ndarray:
    """Explicitly evaluate the alternating sum of tensor-train contractions."""
    value = evaluate_tensor_train(theory, cores, vectors, modulus, mode)
    result = np.zeros_like(value)
    result += value
    _reduce_mod(result, modulus)

    for sign, permutation in _signed_permutations(len(cores) + 1)[1:]:
        value = evaluate_tensor_train(
            theory,
            cores,
            tuple(vectors[i] for i in permutation),
            modulus,
            mode,
        )
        if cores and mode == "batch_multi" and len(permutation) > 1:
            axes = (0,) + tuple(
                permutation.index(i) + 1 for i in range(len(permutation))
            ) + (value.ndim - 1,)
            value = np.transpose(value, axes)
        result += value if sign > 0 else (-value if modulus == 0 else modulus - value)
        _reduce_mod(result, modulus)
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
    high = modulus if modulus != 0 else _INTEGER_PROBE_BOUND
    dtype = np.uint64 if modulus != 0 else np.complex128
    if antisymmetric:
        probes = tuple(
            rng.integers(
                0,
                high,
                size=(degree, num_probes, irrep_dimension),
                dtype=np.uint64,
            )
        )
        return tuple(probe.astype(dtype, copy=False) for probe in probes)
    return (
        rng.integers(
            0,
            high,
            size=(num_probes, irrep_dimension),
            dtype=np.uint64,
        ).astype(dtype, copy=False),
    ) * degree


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
    high = modulus if modulus != 0 else _INTEGER_PROBE_BOUND
    dtype = np.uint64 if modulus != 0 else np.complex128
    return tuple(
        rng.integers(
            0,
            high,
            size=(num_probes, multiplicity, theory.irrep_dimension(irrep)),
            dtype=np.uint64,
        ).astype(dtype, copy=False)
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
def monomial_waring_grid(
    powers: tuple[int, ...],
    modulus: int,
) -> np.ndarray:
    """CP grid for the Waring decomposition of one monomial."""
    columns = ()
    if powers:
        omitted = min(range(len(powers)), key=powers.__getitem__)
        if modulus == 0:
            columns = tuple(
                (1,)
                if i == omitted
                else tuple(
                    np.exp(2j * np.pi * exponent / (degree + 1))
                    for exponent in range(degree + 1)
                )
                for i, degree in enumerate(powers)
            )
        else:
            primitive = sp.primitive_root(modulus)
            columns = tuple(
                (1,)
                if i == omitted
                else tuple(
                    pow(
                        primitive,
                        exponent * ((modulus - 1) // (degree + 1)),
                        modulus,
                    )
                    for exponent in range(degree + 1)
                )
                for i, degree in enumerate(powers)
            )

    dtype = np.complex128 if modulus == 0 else np.uint64
    out = np.asarray(tuple(product(*columns)), dtype=dtype)
    out.setflags(write=False)
    return out


def evaluate_young_symmetrized_tensor_tree(
    theory: RepresentationTheory,
    tensor_tree: TensorTree,
    ssyt: SSYT,
    probe_batches: np.ndarray,
    modulus: int,
) -> np.ndarray:
    if not ssyt.entries_by_row:
        dtype = np.complex128 if modulus == 0 else np.uint64
        return np.ones((probe_batches.shape[0], 1), dtype=dtype)

    grids = tuple(
        monomial_waring_grid(copies, modulus) for copies in ssyt.copies_by_row
    )
    symmetrized_rows = tuple(
        _reduce_mod(
            np.matmul(grid[None, :, :], probe_batches[:, entries, :]),
            modulus,
        )
        for entries, grid in zip(ssyt.entries_by_row, grids)
    )
    row_coeffs = tuple(
        _reduce_mod(
            np.prod(
                grid,
                axis=1,
            ),
            modulus,
        )
        for grid in grids
    )
    coeff = reduce(
        lambda left, right: _reduce_mod(
            np.multiply.outer(left, right).reshape(-1),
            modulus,
        ),
        row_coeffs,
    )

    antisymmetrized_leaves = tuple(
        evaluate_antisymmetrized_tensor_train(
            theory,
            tensor_train,
            symmetrized_rows,
            modulus,
            "batch_multi",
        )
        for tensor_train in tensor_tree.leaf_tensor_trains
    )
    leaf_heights = tuple(
        1 if not tensor_train else len(tensor_train) + 1
        for tensor_train in tensor_tree.leaf_tensor_trains
    )

    grid_shape = tuple(grid.shape[0] for grid in grids)
    if not grid_shape:
        dtype = np.complex128 if modulus == 0 else np.uint64
        return np.empty((probe_batches.shape[0], 0), dtype=dtype)

    vectors = tuple(
        leaf.reshape(
            leaf.shape[0],
            *leaf.shape[1:-1],
            *((1,) * (len(grid_shape) - height)),
            leaf.shape[-1],
        )
        for leaf, height in zip(antisymmetrized_leaves, leaf_heights)
    )
    values = evaluate_tensor_train(
        theory,
        tensor_tree.interior_tensor_train,
        vectors,
        modulus,
        "batch",
    )
    weighted = values * coeff.reshape((1, *grid_shape, 1))
    weighted = _reduce_mod(weighted, modulus)
    summed = np.sum(
        weighted,
        axis=tuple(range(1, len(grid_shape) + 1)),
    )
    return _reduce_mod(summed, modulus)


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
        for tableau_index, tableau in enumerate(ssyts):
            for tree_index, tensor_tree in enumerate(trees):
                cache_key = (
                    modulus,
                    probes.ctypes.data,
                    probes.shape,
                    probes.strides,
                    probes.dtype.str,
                    tensor_tree,
                    tableau,
                )
                if young_tree_cache is not None and cache_key in young_tree_cache:
                    value = young_tree_cache[cache_key]
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
            dtype = np.complex128 if modulus == 0 else np.uint64
            leaf_factor = np.empty(
                (probes.shape[0], leaf_column_count, 0),
                dtype=dtype,
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
        dtype = np.complex128 if modulus == 0 else np.uint64
        return np.empty((0,), dtype=dtype)
    return out


__all__ = (
    "sample_tensor_power_probes",
    "sample_isotypic_input_probes",
    "evaluate_tensor_train",
    "evaluate_antisymmetrized_tensor_train",
    "evaluate_young_symmetrized_tensor_tree",
    "evaluate_basis",
    "monomial_waring_grid",
)
