"""Group-agnostic independent algebra and module generator extraction."""

from __future__ import annotations

import math
from collections.abc import Hashable, Iterable, Iterator, Mapping
from dataclasses import dataclass, replace
from functools import cache
from itertools import product
from typing import Callable

import numpy as np

from .combinatorics import (
    _validate_input_metadata,
    arithmetic_dtype,
    pivot_columns,
    row_kronecker_product,
    validate_modulus,
    weak_compositions,
)
from .evaluators import evaluate_basis, sample_isotypic_input_probes
from .bases import extract, schur_functor_basis
from .isotypic import _IsotypicBlock, stream_isotypic_data_tree
from .protocols import RepresentationTheory
from .streaming import (
    independent_column_indices,
    stream_batches,
)
from .types import Irrep, IsotypicLeaf, SSYT


ProbeTarget = Callable[[tuple[int, ...], int], tuple[int, ...]]
DegreeLimit = Callable[[int], int]
MultidegreeDimensions = Mapping[tuple[int, ...], int]
Content = tuple[int, ...]
ContentGroupsByDegree = tuple[dict[Content, tuple[int, Iterable[IsotypicLeaf]]], ...]


@dataclass(frozen=True, slots=True)
class _LazyContentLeaves:
    theory: RepresentationTheory
    input_irreps: tuple[Irrep, ...]
    sources: tuple[_IsotypicBlock, ...]
    random_seed: int
    modulus: int

    def __iter__(self) -> Iterator[IsotypicLeaf]:
        for source in self.sources:
            yield IsotypicLeaf(
                source.interior_tensor_trains,
                tuple(
                    schur_functor_basis(
                        self.theory,
                        input_irrep,
                        partition,
                        intermediate_irrep,
                        self.random_seed,
                        self.modulus,
                    )
                    for input_irrep, partition, intermediate_irrep in zip(
                        self.input_irreps,
                        source.partitions,
                        source.intermediate_irreps,
                    )
                ),
                source.semistandard_young_tableaux,
            )


def _compute_syndromes(
    theory: RepresentationTheory,
    polynomials: tuple[IsotypicLeaf, ...],
    probe_batches: tuple[np.ndarray, ...],
    modulus: int,
    output_dimension: int,
    young_tree_cache: dict[Hashable, np.ndarray] | None = None,
    probe_window_keys: tuple[Hashable, ...] | None = None,
) -> np.ndarray:
    """Evaluate isotypic leaves as ``probe x output x column`` blocks.

    Empty polynomial sets still use the same rank-3 syndrome convention, with
    zero basis columns.
    """
    if not polynomials:
        return _empty_syndromes((probe_batches[0].shape[0], output_dimension, 0), modulus)

    if young_tree_cache is None:
        young_tree_cache = {}
    blocks = [
        evaluate_basis(
            theory,
            leaf,
            probe_batches,
            modulus,
            young_tree_cache,
            probe_window_keys,
        )
        for leaf in polynomials
    ]
    return blocks[0] if len(blocks) == 1 else np.concatenate(blocks, axis=-1)


def extract_independent_generators(
    theory: RepresentationTheory,
    input_irreps: tuple[Irrep, ...],
    input_multiplicities: tuple[int, ...],
    output_irrep: Irrep,
    max_degree: int,
    probe_target: ProbeTarget,
    degree_limit: DegreeLimit,
    random_seed: int,
    *,
    modulus: int,
    first_generator_degree: int = 0,
    target_dimensions_by_multidegree: MultidegreeDimensions | None = None,
) -> tuple[tuple[IsotypicLeaf, ...], ...]:
    """Extract minimal homogeneous generators from evaluated basis syndromes.

    The pivoting machinery is independent of the concrete group.  Target
    leaves are split by copy-content, with ``target_dimensions_by_multidegree``
    used as an optional multidegree support filter.
    """
    _validate_input_metadata(
        input_irreps,
        input_multiplicities,
        max_degree=max_degree,
    )
    if first_generator_degree < 0:
        raise ValueError("first_generator_degree must be nonnegative")
    if theory.irrep_dimension(theory.trivial_irrep) != 1:
        raise ValueError("theory.trivial_irrep must be one-dimensional")

    validate_modulus(modulus, max_degree=max_degree, allow_complex=False)
    trivial_irrep = theory.trivial_irrep
    output_dimension = theory.irrep_dimension(output_irrep)

    def content_groups_by_degree(
        current_output_irrep: Irrep,
        dimensions_by_multidegree: MultidegreeDimensions | None,
    ) -> ContentGroupsByDegree:
        return tuple(
            _content_leaf_groups(
                theory,
                input_irreps,
                input_multiplicities,
                current_output_irrep,
                degree,
                dimensions_by_multidegree,
                random_seed,
                modulus,
            )
            for degree in range(max_degree + 1)
        )

    covariant_content_groups = content_groups_by_degree(
        output_irrep,
        target_dimensions_by_multidegree,
    )

    content_dimensions = {
        content: dimension
        for content_groups in covariant_content_groups
        for content, (dimension, _leaves) in content_groups.items()
    }
    target_num_probes_by_content = dict(
        zip(
            content_dimensions,
            probe_target(
                tuple(content_dimensions.values()),
                output_dimension,
            ),
        )
    )
    max_probes = max(target_num_probes_by_content.values(), default=1)
    probe_batches = sample_isotypic_input_probes(
        theory,
        input_irreps,
        input_multiplicities,
        max_probes,
        modulus,
        random_seed,
    )
    young_tree_cache: dict[Hashable, np.ndarray] = {}
    # Every probe window is a row-slice of ``probe_batches``; identify each input
    # axis by its index with the leading row 0 so cached Young-tree evaluations
    # are reused across leaves, contents, and the covariant/invariant passes.
    probe_window_keys = tuple((axis, 0) for axis, _batch in enumerate(probe_batches))

    covariant_generators: list[tuple[IsotypicLeaf, ...]] = []
    invariant_content_groups = (
        covariant_content_groups
        if trivial_irrep == output_irrep
        else content_groups_by_degree(trivial_irrep, None)
    )
    invariant_content_group_map = {
        content: group
        for content_groups in invariant_content_groups
        for content, group in content_groups.items()
    }

    @cache
    def invariant_syndromes(content: Content) -> np.ndarray:
        group = invariant_content_group_map.get(content)
        if group is None:
            return _empty_syndromes((max_probes, 1, 0), modulus)
        blocks = [
            syndromes
            for _leaf_batch, syndromes in _syndrome_batches(
                theory,
                group[1],
                probe_batches,
                modulus,
                1,
                young_tree_cache,
                probe_window_keys,
            )
        ]
        return (
            np.concatenate(blocks, axis=-1)
            if blocks
            else _empty_syndromes((probe_batches[0].shape[0], 1, 0), modulus)
        )

    covariant_syndromes_by_content: dict[Content, np.ndarray] = {}

    for degree, content_groups in enumerate(covariant_content_groups):
        degree_generators: list[IsotypicLeaf] = []
        max_generator_degree = degree_limit(degree)

        for content, (content_dimension, leaves) in content_groups.items():
            num_probes = target_num_probes_by_content[content]
            previous_basis = _previous_content_product_basis(
                content,
                covariant_syndromes_by_content,
                invariant_syndromes,
                first_generator_degree,
                max_generator_degree,
                num_probes,
                output_dimension,
                modulus,
            )
            needed = content_dimension - previous_basis.shape[1]
            if needed < 0:
                raise RuntimeError(
                    "previous-generator product rank exceeds the Hilbert "
                    f"dimension for copy-content {content}"
                )
            if needed == 0:
                continue

            (
                content_generators,
                covariant_syndromes,
            ) = _stream_content_generators(
                theory,
                leaves,
                previous_basis,
                needed,
                probe_batches,
                num_probes,
                max_probes,
                modulus,
                output_dimension,
                young_tree_cache,
                probe_window_keys,
            )
            degree_generators.extend(content_generators)

            if covariant_syndromes.shape[-1] > 0:
                covariant_syndromes_by_content[content] = covariant_syndromes
        covariant_generators.append(tuple(degree_generators))
    return tuple(covariant_generators)


def _content_leaf_groups(
    theory: RepresentationTheory,
    input_irreps: tuple[Irrep, ...],
    input_multiplicities: tuple[int, ...],
    output_irrep: Irrep,
    degree: int,
    target_dimensions_by_multidegree: MultidegreeDimensions | None,
    random_seed: int,
    modulus: int,
) -> dict[Content, tuple[int, Iterable[IsotypicLeaf]]]:
    grouped: dict[Content, tuple[int, list[_IsotypicBlock]]] = {}
    for multidegree in weak_compositions(degree, len(input_irreps)):
        if (
            target_dimensions_by_multidegree is not None
            and target_dimensions_by_multidegree.get(multidegree, 0) == 0
        ):
            continue
        for source in stream_isotypic_data_tree(
            theory,
            input_irreps,
            input_multiplicities,
            output_irrep,
            multidegree,
            random_seed=random_seed,
        ):
            tableau_groups_by_input = tuple(
                _tableaux_by_content(tableaux, multiplicity)
                for tableaux, multiplicity in zip(
                    source.semistandard_young_tableaux,
                    input_multiplicities,
                )
            )
            for content_parts in product(*tableau_groups_by_input):
                content_counts, content_tableaux = zip(*content_parts)
                content = tuple(
                    count for counts in content_counts for count in counts
                )
                dimension = len(source.interior_tensor_trains) * math.prod(
                    tree_count * len(tableaux)
                    for tree_count, tableaux in zip(
                        source.leaf_tree_counts,
                        content_tableaux,
                    )
                )
                if dimension == 0:
                    continue
                group_dimension, sources = grouped.setdefault(content, (0, []))
                sources.append(
                    replace(
                        source,
                        semistandard_young_tableaux=content_tableaux,
                    )
                )
                grouped[content] = (group_dimension + dimension, sources)

    return {
        content: (
            dimension,
            _LazyContentLeaves(
                theory,
                input_irreps,
                tuple(sources),
                random_seed,
                modulus,
            ),
        )
        for content, (dimension, sources) in grouped.items()
    }


def _tableaux_by_content(
    tableaux: tuple[SSYT, ...],
    multiplicity: int,
) -> tuple[tuple[Content, tuple[SSYT, ...]], ...]:
    grouped: dict[Content, list[SSYT]] = {}
    for ssyt in tableaux:
        grouped.setdefault(_ssyt_content(ssyt, multiplicity), []).append(ssyt)
    return tuple((content, tuple(ssyts)) for content, ssyts in grouped.items())


def _ssyt_content(
    ssyt: SSYT,
    multiplicity: int,
) -> tuple[int, ...]:
    counts = [0] * multiplicity
    for entries, row_copies in zip(ssyt.entries_by_row, ssyt.copies_by_row):
        for entry, copies in zip(entries, row_copies):
            counts[entry] += copies
    return tuple(counts)


def _previous_content_product_basis(
    content: Content,
    covariant_syndromes_by_content: dict[Content, np.ndarray],
    invariant_syndromes: Callable[[Content], np.ndarray],
    first_generator_degree: int,
    max_generator_degree: int,
    num_probes: int,
    output_dimension: int,
    modulus: int,
) -> np.ndarray:
    row_count = num_probes * output_dimension
    previous_blocks = []
    for generator_content, cov_syn in covariant_syndromes_by_content.items():
        generator_degree = sum(generator_content)
        if (
            generator_degree < first_generator_degree
            or generator_degree > max_generator_degree
        ):
            continue
        invariant_content = tuple(
            content_entry - generator_entry
            for content_entry, generator_entry in zip(content, generator_content)
        )
        if any(entry < 0 for entry in invariant_content) or sum(invariant_content) <= 0:
            continue
        inv_syn = invariant_syndromes(invariant_content)
        if inv_syn.shape[-1] > 0:
            previous_blocks.append(
                row_kronecker_product(
                    inv_syn[:num_probes],
                    cov_syn[:num_probes],
                    modulus,
                )
            )

    if not previous_blocks or row_count == 0:
        return _empty_syndromes((row_count, 0), modulus)

    previous = np.concatenate(previous_blocks, axis=-1).reshape(row_count, -1)
    pivots = pivot_columns(previous, modulus)
    return previous[:, pivots] if pivots else _empty_syndromes((row_count, 0), modulus)


def _stream_content_generators(
    theory: RepresentationTheory,
    leaves: Iterable[IsotypicLeaf],
    previous_basis: np.ndarray,
    needed: int,
    probe_batches: tuple[np.ndarray, ...],
    num_probes: int,
    max_probes: int,
    modulus: int,
    output_dimension: int,
    young_tree_cache: dict[Hashable, np.ndarray],
    probe_window_keys: tuple[Hashable, ...],
) -> tuple[tuple[IsotypicLeaf, ...], np.ndarray]:
    selected_generators: list[IsotypicLeaf] = []
    selected_syndrome_blocks: list[np.ndarray] = []
    current_basis = previous_basis
    probe_prefix = tuple(batch[:num_probes, :, :] for batch in probe_batches)
    # The trailing probe rows form a distinct window starting at ``num_probes``.
    suffix_window_keys = tuple((axis, num_probes) for axis, _key in enumerate(probe_batches))

    for leaf_batch, batch_syndromes in _syndrome_batches(
        theory,
        leaves,
        probe_prefix,
        modulus,
        output_dimension,
        young_tree_cache,
        probe_window_keys,
    ):
        linear_indices = independent_column_indices(
            current_basis,
            batch_syndromes.reshape((-1, batch_syndromes.shape[-1])),
            needed - len(selected_generators),
            modulus,
        ).indices
        if not linear_indices:
            continue

        new_generators = extract(linear_indices, leaf_batch)
        selected_generators.extend(new_generators)
        selected_syndromes = batch_syndromes[..., linear_indices]
        if len(selected_generators) < needed:
            current_basis = np.concatenate(
                (
                    current_basis,
                    selected_syndromes[:num_probes].reshape(
                        -1,
                        len(linear_indices),
                    ),
                ),
                axis=1,
            )

        if max_probes != num_probes:
            extra = _compute_syndromes(
                theory,
                new_generators,
                tuple(batch[num_probes:, :, :] for batch in probe_batches),
                modulus,
                output_dimension,
                young_tree_cache,
                suffix_window_keys,
            )
            selected_syndromes = np.concatenate((selected_syndromes, extra), axis=0)
        selected_syndrome_blocks.append(selected_syndromes)
        if len(selected_generators) == needed:
            break

    if len(selected_generators) != needed:
        raise RuntimeError(
            f"streamed {len(selected_generators)} generators, expected {needed}"
        )

    return (
        tuple(selected_generators),
        np.concatenate(selected_syndrome_blocks, axis=-1),
    )


def _syndrome_batches(
    theory: RepresentationTheory,
    leaves: Iterable[IsotypicLeaf],
    probe_batches: tuple[np.ndarray, ...],
    modulus: int,
    output_dimension: int,
    young_tree_cache: dict[Hashable, np.ndarray],
    probe_window_keys: tuple[Hashable, ...],
) -> Iterator[tuple[tuple[IsotypicLeaf, ...], np.ndarray]]:
    for leaf_batch in stream_batches(leaves):
        syndromes = _compute_syndromes(
            theory,
            leaf_batch,
            probe_batches,
            modulus,
            output_dimension,
            young_tree_cache,
            probe_window_keys,
        )
        if syndromes.shape[-1] > 0:
            yield leaf_batch, syndromes


def _empty_syndromes(shape: tuple[int, ...], modulus: int) -> np.ndarray:
    """Zero-column syndrome array; ``shape`` ends in ``0`` (flat or probe x output)."""
    return np.empty(shape, dtype=arithmetic_dtype(modulus))


__all__ = ("DegreeLimit", "ProbeTarget", "extract_independent_generators")
