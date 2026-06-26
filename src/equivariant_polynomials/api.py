"""High-level public API for equivariant-polynomial computations.

This module is the recommended entry point.  It wraps the low-level group-agnostic
``core`` pipeline in a small, declarative surface organized around the objects in
``docs/theory.tex``:

* A :class:`Representation` is a finite-dimensional representation, given by its
  *isotypic decomposition* ``X = sum_lambda H_lambda (x) X_lambda`` -- a list of
  :class:`IsotypicComponent` records ``(irrep, multiplicity)``.  Representations
  carry their group backend (a ``RepresentationTheory``), so the computation
  functions never take a separate ``theory=`` argument.

* :func:`covariant_basis` / :func:`invariant_basis` return *vector-space* bases of
  the covariant module ``M_G(X, Y)_d = (Sym^d(X*) (x) Y)^G`` (Corollary
  ``cor:arbitrary-output-basis``).

* :func:`covariant_generators` returns minimal homogeneous ``R_G(X)``-*module*
  generators of ``M_G(X, Y)`` (Theorem ``thm:module-generator-reduction``), while
  :func:`invariant_generators` returns minimal ``C``-*algebra* generators of the
  invariant algebra ``R_G(X) = Sym(X*)^G`` (Lemma ``lem:algebra-generators``).
  These are genuinely different reductions of the same extraction routine; see
  ``alg:extract-independent-generators``.

* :func:`covariant_dimension` / :func:`covariant_hilbert_series` report graded
  dimensions.  They are computed combinatorially from the isotypic data tree and
  therefore work for any backend, with no group-specific Molien series.

The returned :class:`Covariant` objects are *callable*: ``f(x)`` evaluates the
equivariant polynomial at a point (or a batch of points) given in isotypic
coordinates, using the evaluation scheme of ``alg:evaluate-basis``.

Coordinate conventions
----------------------
*Isotypic coordinates* are canonical.  A point of ``X`` is a tuple with one array
per component; component ``(irrep, multiplicity)`` is an array of shape
``(multiplicity, dim H_irrep)``, optionally with a leading batch axis
``(batch, multiplicity, dim H_irrep)``.  A single-component domain may be given as
a bare array.  Evaluating a :class:`Covariant` returns its value in the output
irrep ``H_nu`` (shape ``(dim H_nu,)`` or ``(batch, dim H_nu)``); ``output_irrep``
and ``output_copy`` say where that value sits inside the codomain ``Y``.

Optional ``to_isotypic`` / ``from_isotypic`` maps on a :class:`Representation`
convert to and from a user's ambient basis (Assumption ``ass:explicit-isotypic``),
enabling ``coordinates="ambient"`` on evaluation.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import Any, Callable, Iterator, Literal, Sequence

import numpy as np
import sympy as sp

from .core.bases import extract
from .core.combinatorics import (
    pivot_columns,
    weak_compositions,
)
from .core.evaluators import evaluate_basis, sample_isotypic_input_probes
from .core.generators import _content_leaf_groups, extract_independent_generators
from .core.isotypic import stream_isotypic_data_tree
from .core.protocols import RepresentationTheory
from .core.types import Irrep, IsotypicLeaf

Array = np.ndarray
CoordinateSystem = Literal["isotypic", "ambient"]
CollectionKind = Literal["basis", "generators"]


# =============================================================================
# Options
# =============================================================================


@dataclass(frozen=True)
class Options:
    """Algorithmic options for the randomized finite-field construction.

    Generator and basis construction selects independent elements by evaluating
    candidates on random finite-field probes (Proposition ``prop:random-rank-test``).
    Evaluation of the resulting objects is always exact over ``C``.

    Attributes:
        modulus: Prime field used for the rank-selection arithmetic.  ``None``
            auto-selects a prime with ``modulus > max_degree`` in the
            ``1000 < p < 10000`` range recommended in ``docs/theory.tex``.
        seed: Seed for the randomized probe sampling and candidate ordering.
        probe_overshoot: Extra random probes beyond the ``ceil(dim / dim H_nu)``
            minimum, trading a small amount of work for a lower rank-test failure
            probability.
    """

    modulus: int | None = None
    seed: int = 0
    probe_overshoot: int = 2


_DEFAULT_OPTIONS = Options()


def _default_modulus(max_degree: int) -> int:
    """Smallest prime that is both ``> max_degree`` and ``> 1000``."""
    return int(sp.nextprime(max(max_degree, 1000)))


def _resolve_modulus(options: Options, max_degree: int) -> int:
    return options.modulus if options.modulus is not None else _default_modulus(max_degree)


def _probe_target(overshoot: int) -> Callable[[tuple[int, ...], int], tuple[int, ...]]:
    return lambda dimensions, output_dimension: tuple(
        (math.ceil(dimension / output_dimension) + overshoot) if dimension else 0
        for dimension in dimensions
    )


# =============================================================================
# Representation data
# =============================================================================


@dataclass(frozen=True)
class IsotypicComponent:
    """One isotypic summand ``H_irrep (x) C^multiplicity`` of a representation."""

    irrep: Irrep
    multiplicity: int = 1

    def __post_init__(self) -> None:
        if self.multiplicity <= 0:
            raise ValueError("multiplicity must be a positive integer")


def _normalize_components(
    components: Sequence[Any],
) -> tuple[IsotypicComponent, ...]:
    """Accept components, ``(irrep, multiplicity)`` pairs, or bare irreps.

    Repeated irreps are merged by summing their multiplicities, so the result is
    a genuine isotypic decomposition with one summand per irrep.
    """
    order: list[Irrep] = []
    multiplicities: dict[Any, int] = {}
    for entry in components:
        if isinstance(entry, IsotypicComponent):
            irrep, multiplicity = entry.irrep, entry.multiplicity
        elif isinstance(entry, tuple) and len(entry) == 2:
            irrep, multiplicity = entry
        else:
            irrep, multiplicity = entry, 1
        if multiplicity <= 0:
            raise ValueError("multiplicity must be a positive integer")
        if irrep not in multiplicities:
            order.append(irrep)
            multiplicities[irrep] = 0
        multiplicities[irrep] += int(multiplicity)
    return tuple(IsotypicComponent(irrep, multiplicities[irrep]) for irrep in order)


@dataclass(frozen=True)
class Representation:
    """A finite-dimensional representation, given by its isotypic decomposition.

    The ``components`` argument is normalized in ``__post_init__`` to a canonical
    tuple of :class:`IsotypicComponent` with one summand per distinct irrep; for
    example ``Representation(theory, [1, (1, 2)])`` becomes
    ``(IsotypicComponent(1, 3),)`` (the two entries for irrep ``1`` are merged).

    Args:
        theory: The group representation-theory backend.
        components: An isotypic decomposition.  Each entry may be an
            :class:`IsotypicComponent`, an ``(irrep, multiplicity)`` pair, or a
            bare irrep label (multiplicity ``1``).  Repeated irreps are merged by
            summing their multiplicities, keeping first-appearance order.
        name: Optional human-readable label.
        to_isotypic: Optional map from a user ambient array to isotypic
            coordinates (a tuple with one array per component).
        from_isotypic: Optional map from isotypic coordinates back to the user
            ambient array.
    """

    theory: RepresentationTheory
    components: tuple[IsotypicComponent, ...]
    name: str | None = None
    to_isotypic: Callable[[Array], tuple[Array, ...]] | None = None
    from_isotypic: Callable[[tuple[Array, ...]], Array] | None = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "components", _normalize_components(self.components))
        if not self.components:
            raise ValueError("a representation needs at least one isotypic component")

    # -- constructors ---------------------------------------------------------

    @classmethod
    def irrep(
        cls,
        theory: RepresentationTheory,
        irrep: Irrep,
        multiplicity: int = 1,
        *,
        name: str | None = None,
        to_isotypic: Callable[[Array], tuple[Array, ...]] | None = None,
        from_isotypic: Callable[[tuple[Array, ...]], Array] | None = None,
    ) -> "Representation":
        """A single isotypic component ``H_irrep (x) C^multiplicity``."""
        return cls(
            theory,
            (IsotypicComponent(irrep, multiplicity),),
            name=name,
            to_isotypic=to_isotypic,
            from_isotypic=from_isotypic,
        )

    @classmethod
    def trivial(
        cls,
        theory: RepresentationTheory,
        *,
        name: str = "trivial",
    ) -> "Representation":
        """The one-dimensional trivial representation."""
        return cls.irrep(theory, theory.trivial_irrep, name=name)

    # -- accessors ------------------------------------------------------------

    @property
    def irreps(self) -> tuple[Irrep, ...]:
        return tuple(component.irrep for component in self.components)

    @property
    def multiplicities(self) -> tuple[int, ...]:
        return tuple(component.multiplicity for component in self.components)

    @property
    def dimension(self) -> int:
        """Ambient vector-space dimension ``sum_lambda m_lambda dim H_lambda``."""
        return sum(
            component.multiplicity * self.theory.irrep_dimension(component.irrep)
            for component in self.components
        )

    @property
    def is_trivial(self) -> bool:
        return self.components == (IsotypicComponent(self.theory.trivial_irrep, 1),)

    # -- coordinates ----------------------------------------------------------

    def to_isotypic_coords(self, x: Array) -> tuple[Array, ...]:
        if self.to_isotypic is None:
            raise ValueError(
                f"{self._label()} has no ambient -> isotypic map; "
                "construct it with to_isotypic=... to use ambient coordinates"
            )
        return self.to_isotypic(x)

    def from_isotypic_coords(self, coords: tuple[Array, ...]) -> Array:
        if self.from_isotypic is None:
            raise ValueError(
                f"{self._label()} has no isotypic -> ambient map; "
                "construct it with from_isotypic=... to use ambient coordinates"
            )
        return self.from_isotypic(coords)

    def _label(self) -> str:
        return self.name or "representation"

    def __repr__(self) -> str:
        body = " + ".join(
            f"{component.multiplicity}*H[{component.irrep!r}]"
            if component.multiplicity != 1
            else f"H[{component.irrep!r}]"
            for component in self.components
        )
        tag = f" {self.name!r}" if self.name else ""
        return f"Representation({body}, dim={self.dimension}{tag})"


def trivial_representation(theory: RepresentationTheory) -> Representation:
    """Shortcut for :meth:`Representation.trivial`."""
    return Representation.trivial(theory)


def irreducible_representation(
    theory: RepresentationTheory,
    irrep: Irrep,
    multiplicity: int = 1,
) -> Representation:
    """Shortcut for :meth:`Representation.irrep`."""
    return Representation.irrep(theory, irrep, multiplicity)


# =============================================================================
# Covariant objects
# =============================================================================


def _as_isotypic_probes(
    domain: Representation,
    x: Array | tuple[Array, ...],
    coordinates: CoordinateSystem,
) -> tuple[tuple[Array, ...], bool]:
    """Normalize an input point to ``(num_probes, mult, dim)`` arrays.

    Returns the per-component probe arrays and whether the input carried a batch
    axis (so the caller can squeeze the leading axis off the result).
    """
    if coordinates == "ambient":
        coords: Any = domain.to_isotypic_coords(x)
    elif coordinates == "isotypic":
        coords = x
    else:
        raise ValueError(f"unknown coordinate system {coordinates!r}")

    if isinstance(coords, (tuple, list)):
        coords = tuple(coords)
    else:
        if len(domain.components) != 1:
            raise ValueError(
                "isotypic coordinates for a multi-component representation must be "
                "a sequence with one array per component"
            )
        coords = (coords,)
    if len(coords) != len(domain.components):
        raise ValueError(
            f"expected {len(domain.components)} coordinate arrays, got {len(coords)}"
        )

    theory = domain.theory
    probes: list[Array] = []
    batched: bool | None = None
    for component, array in zip(domain.components, coords):
        values = np.asarray(array, dtype=np.complex128)
        dim = theory.irrep_dimension(component.irrep)
        if values.ndim == 1 and component.multiplicity == 1:
            values, is_batched = values.reshape(1, 1, dim), False
        elif values.ndim == 2:
            values, is_batched = values.reshape(1, *values.shape), False
        elif values.ndim == 3:
            is_batched = True
        else:
            raise ValueError(
                f"component H[{component.irrep!r}] expects shape "
                f"({component.multiplicity}, {dim}) or "
                f"(batch, {component.multiplicity}, {dim})"
            )
        if values.shape[-2:] != (component.multiplicity, dim):
            raise ValueError(
                f"component H[{component.irrep!r}] expects shape "
                f"(..., {component.multiplicity}, {dim}), got {tuple(np.shape(array))}"
            )
        if batched is None:
            batched = is_batched
        elif batched != is_batched:
            raise ValueError("all components must share the same batch layout")
        probes.append(values)

    assert batched is not None
    return tuple(probes), batched


@dataclass(frozen=True)
class Covariant:
    """One homogeneous equivariant polynomial ``X -> H_nu``.

    Calling the object (or :meth:`evaluate`) returns the value in the output irrep
    ``H_nu``.  ``output_irrep`` and ``output_copy`` locate that value within the
    codomain ``Y``: it occupies copy ``output_copy`` of the isotypic component for
    ``output_irrep``.  Use :meth:`CovariantCollection.combine` (or
    :meth:`CovariantCollection.assemble`) to scatter values into a full
    codomain-valued result, e.g. for the learning ansatz of ``docs/theory.tex``.
    """

    domain: Representation
    codomain: Representation
    degree: int
    output_irrep: Irrep
    output_copy: int
    leaf: IsotypicLeaf = field(repr=False)
    name: str | None = None

    def evaluate(
        self,
        x: Array | tuple[Array, ...],
        *,
        coordinates: CoordinateSystem = "isotypic",
    ) -> Array:
        """Evaluate the covariant at ``x``.

        Args:
            x: A point of the domain in isotypic coordinates (or ambient
                coordinates if ``coordinates="ambient"``), with an optional leading
                batch axis.
            coordinates: Coordinate system of ``x``.

        Returns:
            The value in ``H_output_irrep`` with shape ``(dim H_nu,)``, or
            ``(batch, dim H_nu)`` for batched input.
        """
        probes, batched = _as_isotypic_probes(self.domain, x, coordinates)
        values = evaluate_basis(self.domain.theory, self.leaf, probes, 0)[:, :, 0]
        return values if batched else values[0]

    def __call__(
        self,
        x: Array | tuple[Array, ...],
        *,
        coordinates: CoordinateSystem = "isotypic",
    ) -> Array:
        """Shortcut for :meth:`evaluate`."""
        return self.evaluate(x, coordinates=coordinates)

    def __repr__(self) -> str:
        tag = f" {self.name!r}" if self.name else ""
        return (
            f"Covariant(degree={self.degree}, output=H[{self.output_irrep!r}]"
            f"#{self.output_copy}{tag})"
        )


@dataclass(frozen=True)
class CovariantCombination:
    """A linear combination ``sum_i c_i m_i`` of covariants from a collection.

    Evaluating yields a codomain-valued result: each term is scattered into its
    ``(output_irrep, output_copy)`` slot of ``Y`` and summed.  This realizes the
    inner sum of the equivariant ansatz ``F(x) = sum_i N_i(r(x)) m_i(x)`` for a
    fixed coefficient vector.
    """

    collection: "CovariantCollection"
    coefficients: Array

    def evaluate(
        self,
        x: Array | tuple[Array, ...],
        *,
        coordinates: CoordinateSystem = "isotypic",
        output: CoordinateSystem = "isotypic",
    ) -> Array | tuple[Array, ...]:
        values, batched = self.collection._evaluate_elements(x, coordinates)
        batched = batched or self.coefficients.ndim > 1
        return self.collection._scatter(
            values, self.coefficients, batched=batched, output=output
        )

    def __call__(
        self,
        x: Array | tuple[Array, ...],
        *,
        coordinates: CoordinateSystem = "isotypic",
        output: CoordinateSystem = "isotypic",
    ) -> Array | tuple[Array, ...]:
        """Shortcut for :meth:`evaluate`."""
        return self.evaluate(x, coordinates=coordinates, output=output)


@dataclass(frozen=True)
class CovariantCollection:
    """An ordered collection of covariants sharing a domain and codomain.

    With ``kind="basis"`` the elements form a vector-space basis of
    ``M_G(X, Y)`` (in one degree, or across all degrees up to ``max_degree``).
    With ``kind="generators"`` the elements are minimal homogeneous generators:
    ``R_G(X)``-module generators of ``M_G(X, Y)`` when ``is_module`` is true, and
    ``C``-algebra generators of ``R_G(X)`` otherwise.
    """

    kind: CollectionKind
    domain: Representation
    codomain: Representation
    elements: tuple[Covariant, ...]
    modulus: int
    seed: int
    is_module: bool = True
    degree: int | None = None
    max_degree: int | None = None

    # -- sequence protocol ----------------------------------------------------

    def __len__(self) -> int:
        return len(self.elements)

    def __iter__(self) -> Iterator[Covariant]:
        return iter(self.elements)

    def __getitem__(self, index: int) -> Covariant:
        return self.elements[index]

    # -- structure ------------------------------------------------------------

    @property
    def dimension(self) -> int:
        return len(self.elements)

    def degrees(self) -> tuple[int, ...]:
        return tuple(sorted({element.degree for element in self.elements}))

    def by_degree(self) -> dict[int, tuple[Covariant, ...]]:
        grouped: dict[int, list[Covariant]] = {}
        for element in self.elements:
            grouped.setdefault(element.degree, []).append(element)
        return {degree: tuple(grouped[degree]) for degree in sorted(grouped)}

    def counts_by_degree(self) -> tuple[int, ...]:
        """Number of elements in each degree ``0 .. D``.

        ``D`` is the degree bound the collection was built with (``max_degree`` or
        ``degree``), so the tuple keeps its trailing zeros, e.g. minimal generators
        computed up to degree ``4`` report a length-``5`` tuple.
        """
        top = max((element.degree for element in self.elements), default=-1)
        bound = self.max_degree if self.max_degree is not None else self.degree
        length = max(top, bound if bound is not None else top) + 1
        counts = [0] * length
        for element in self.elements:
            counts[element.degree] += 1
        return tuple(counts)

    # -- evaluation -----------------------------------------------------------

    def _evaluate_elements(
        self,
        x: Array | tuple[Array, ...],
        coordinates: CoordinateSystem,
    ) -> tuple[list[Array], bool]:
        probes, batched = _as_isotypic_probes(self.domain, x, coordinates)
        theory = self.domain.theory
        values = [
            evaluate_basis(theory, element.leaf, probes, 0)[:, :, 0]
            for element in self.elements
        ]
        if not batched:
            values = [value[0] for value in values]
        return values, batched

    def evaluate(
        self,
        x: Array | tuple[Array, ...],
        *,
        coordinates: CoordinateSystem = "isotypic",
    ) -> list[Array]:
        """Evaluate every element, returning one ``H_nu`` value per element.

        Each value has shape ``(dim H_nu,)`` (or ``(batch, dim H_nu)`` for batched
        input).  For an invariant collection (all ``H_nu`` one-dimensional) the
        values stack into the invariant feature vector via
        ``numpy.concatenate(collection.evaluate(x), axis=-1)``.
        """
        values, _batched = self._evaluate_elements(x, coordinates)
        return values

    def combine(self, coefficients: Sequence[Any] | Array) -> CovariantCombination:
        """Bind a fixed coefficient vector, giving an evaluable combination."""
        coeffs = np.asarray(coefficients, dtype=np.complex128)
        if coeffs.shape[-1] != len(self.elements):
            raise ValueError(
                f"expected {len(self.elements)} coefficients, got {coeffs.shape[-1]}"
            )
        return CovariantCombination(self, coeffs)

    # backwards-compatible alias
    linear_combination = combine

    def assemble(
        self,
        values: Sequence[Array],
        coefficients: Array,
        *,
        output: CoordinateSystem = "isotypic",
    ) -> Array | tuple[Array, ...]:
        """Scatter precomputed per-element values into the codomain ``Y``.

        This is the geometry half of the ansatz ``sum_i c_i m_i(x)``: ``values``
        are the ``m_i(x)`` (from :meth:`evaluate`) and ``coefficients`` are the
        ``c_i = N_i(r(x))``.  ``coefficients`` has shape ``(M,)`` or, for batched
        evaluation, ``(batch, M)``.
        """
        coeffs = np.asarray(coefficients, dtype=np.complex128)
        if coeffs.shape[-1] != len(self.elements):
            raise ValueError(
                f"expected {len(self.elements)} coefficients, got {coeffs.shape[-1]}"
            )
        batched = coeffs.ndim > 1 or (len(values) > 0 and np.asarray(values[0]).ndim > 1)
        return self._scatter(list(values), coeffs, batched=batched, output=output)

    def _scatter(
        self,
        values: list[Array],
        coefficients: Array,
        *,
        batched: bool,
        output: CoordinateSystem,
    ) -> Array | tuple[Array, ...]:
        theory = self.domain.theory
        coeffs = np.asarray(coefficients, dtype=np.complex128)
        value_batch = (
            np.asarray(values[0]).shape[:-1]
            if values and np.asarray(values[0]).ndim > 1
            else None
        )
        if batched and coeffs.ndim > 1:
            batch_shape = coeffs.shape[:-1]
            if value_batch is not None and value_batch != batch_shape:
                raise ValueError(
                    f"coefficient batch shape {batch_shape} does not match value "
                    f"batch shape {value_batch}"
                )
        elif batched and value_batch is not None:
            batch_shape = value_batch
        else:
            batch_shape = ()

        component_index = {
            component.irrep: k for k, component in enumerate(self.codomain.components)
        }
        blocks = [
            np.zeros(
                (*batch_shape, component.multiplicity, theory.irrep_dimension(component.irrep)),
                dtype=np.complex128,
            )
            for component in self.codomain.components
        ]

        for index, element in enumerate(self.elements):
            value = np.asarray(values[index], dtype=np.complex128)
            scalar = coeffs[..., index]
            if scalar.ndim > 0:  # one coefficient per batch element
                scalar = scalar[..., None]
            block = blocks[component_index[element.output_irrep]]
            block[..., element.output_copy, :] += scalar * value

        coords = tuple(blocks)
        if output == "ambient":
            return self.codomain.from_isotypic_coords(coords)
        if output != "isotypic":
            raise ValueError(f"unknown coordinate system {output!r}")
        return coords[0] if len(coords) == 1 else coords

    # -- verification ---------------------------------------------------------

    def verify(self, *, options: Options | None = None) -> bool:
        """Check that the collection is linearly independent over a fresh field.

        Independence is the defining property of a basis and a necessary property
        of minimal homogeneous generators (generation and minimality are
        guaranteed by construction).  Elements that are copies of the same
        ``M_G(X, H_nu)`` element in different output slots are independent by
        construction, so independence is tested per ``(output_irrep, output_copy)``
        group; the test uses an independent prime field to guard against an
        unlucky construction probe batch.
        """
        options = options or _default_options_for(self)
        modulus = int(sp.nextprime(max(self.modulus, _construction_max_degree(self))))
        theory = self.domain.theory

        groups: dict[tuple[Any, int], list[IsotypicLeaf]] = {}
        for element in self.elements:
            groups.setdefault((element.output_irrep, element.output_copy), []).append(
                element.leaf
            )

        for (output_irrep, _copy), leaves in groups.items():
            if not _leaves_independent(
                theory,
                self.domain,
                output_irrep,
                tuple(leaves),
                modulus,
                options.seed,
                options.probe_overshoot,
            ):
                return False
        return True

    def __repr__(self) -> str:
        if self.kind == "generators":
            flavor = "module" if self.is_module else "algebra"
            head = f"CovariantCollection(generators[{flavor}]"
        else:
            head = "CovariantCollection(basis"
        return f"{head}, n={len(self.elements)}, counts={self.counts_by_degree()})"


def _default_options_for(collection: CovariantCollection) -> Options:
    return Options(modulus=collection.modulus, seed=collection.seed)


def _construction_max_degree(collection: CovariantCollection) -> int:
    return max((element.degree for element in collection.elements), default=0)


def _leaves_independent(
    theory: RepresentationTheory,
    domain: Representation,
    output_irrep: Irrep,
    leaves: tuple[IsotypicLeaf, ...],
    modulus: int,
    seed: int,
    overshoot: int,
) -> bool:
    output_dimension = theory.irrep_dimension(output_irrep)
    num_probes = math.ceil(len(leaves) / output_dimension) + overshoot
    probes = sample_isotypic_input_probes(
        theory,
        domain.irreps,
        domain.multiplicities,
        num_probes,
        modulus,
        seed,
    )
    columns = np.stack(
        [evaluate_basis(theory, leaf, probes, modulus)[:, :, 0].reshape(-1) for leaf in leaves],
        axis=1,
    )
    return len(pivot_columns(columns, modulus)) == len(leaves)


# =============================================================================
# Graded dimensions (combinatorial, backend-agnostic)
# =============================================================================


def _block_dimension(block: Any) -> int:
    return len(block.interior_tensor_trains) * math.prod(
        tree_count * len(tableaux)
        for tree_count, tableaux in zip(
            block.leaf_tree_counts,
            block.semistandard_young_tableaux,
        )
    )


def _irreducible_dimension(
    theory: RepresentationTheory,
    irreps: tuple[Irrep, ...],
    multiplicities: tuple[int, ...],
    output_irrep: Irrep,
    degree: int,
) -> int:
    """``dim M_G^degree(X, H_output_irrep)`` from the isotypic data tree."""
    return sum(
        _block_dimension(block)
        for multidegree in weak_compositions(degree, len(irreps))
        for block in stream_isotypic_data_tree(
            theory,
            irreps,
            multiplicities,
            output_irrep,
            multidegree,
            random_seed=0,
        )
    )


def covariant_dimension(
    domain: Representation,
    codomain: Representation,
    degree: int,
) -> int:
    """Return ``dim M_G(domain, codomain)_degree``."""
    _check_compatible(domain, codomain)
    if degree < 0:
        raise ValueError("degree must be nonnegative")
    theory = domain.theory
    return sum(
        component.multiplicity
        * _irreducible_dimension(
            theory, domain.irreps, domain.multiplicities, component.irrep, degree
        )
        for component in codomain.components
    )


def invariant_dimension(domain: Representation, degree: int) -> int:
    """Return ``dim R_G(domain)_degree``."""
    return covariant_dimension(domain, Representation.trivial(domain.theory), degree)


def covariant_hilbert_series(
    domain: Representation,
    codomain: Representation,
    max_degree: int,
) -> tuple[int, ...]:
    """Graded dimensions of ``M_G(domain, codomain)`` for degrees ``0..max_degree``."""
    if max_degree < 0:
        raise ValueError("max_degree must be nonnegative")
    return tuple(
        covariant_dimension(domain, codomain, degree)
        for degree in range(max_degree + 1)
    )


def invariant_hilbert_series(
    domain: Representation,
    max_degree: int,
) -> tuple[int, ...]:
    """Graded dimensions of ``R_G(domain)`` for degrees ``0..max_degree``."""
    return covariant_hilbert_series(
        domain, Representation.trivial(domain.theory), max_degree
    )


# =============================================================================
# Vector-space bases
# =============================================================================


def _check_compatible(domain: Representation, codomain: Representation) -> None:
    # ``!=`` falls back to identity when a backend defines no custom equality, so
    # this accepts either the same object or an equal one.
    if domain.theory != codomain.theory:
        raise ValueError("domain and codomain must share the same group backend")


def _resolve_degree_range(
    degree: int | None,
    max_degree: int | None,
) -> range:
    if (degree is None) == (max_degree is None):
        raise ValueError("supply exactly one of degree=... or max_degree=...")
    if degree is not None:
        if degree < 0:
            raise ValueError("degree must be nonnegative")
        return range(degree, degree + 1)
    assert max_degree is not None
    if max_degree < 0:
        raise ValueError("max_degree must be nonnegative")
    return range(max_degree + 1)


def _irreducible_basis_leaves(
    theory: RepresentationTheory,
    irreps: tuple[Irrep, ...],
    multiplicities: tuple[int, ...],
    output_irrep: Irrep,
    degree: int,
    modulus: int,
    seed: int,
) -> tuple[IsotypicLeaf, ...]:
    """Materialize a basis of ``M_G^degree(X, H_output_irrep)`` as single-column leaves.

    Reuses the core content-grouping (which lazily materializes the Schur-functor
    tensor trees) and then explodes every grouped block into one leaf per basis
    column via ``core.bases.extract``.
    """
    groups = _content_leaf_groups(
        theory, irreps, multiplicities, output_irrep, degree, None, seed, modulus
    )
    leaves = tuple(leaf for _content, (_dim, lazy) in groups.items() for leaf in lazy)
    total = sum(dim for _content, (dim, _lazy) in groups.items())
    return extract(tuple(range(total)), leaves)


def covariant_basis(
    domain: Representation,
    codomain: Representation,
    *,
    degree: int | None = None,
    max_degree: int | None = None,
    options: Options | None = None,
) -> CovariantCollection:
    """Return a vector-space basis of the covariant module ``M_G(domain, codomain)``.

    Supply exactly one of ``degree`` (one homogeneous degree) or ``max_degree``
    (all degrees ``0..max_degree``).  For an arbitrary codomain ``Y``, the basis is
    the union over output components ``(nu, m_nu)`` of a basis of
    ``M_G(X, H_nu)`` tensored with the ``m_nu`` output copies of ``Y_nu``
    (Corollary ``cor:arbitrary-output-basis``).
    """
    _check_compatible(domain, codomain)
    options = options or _DEFAULT_OPTIONS
    degree_range = _resolve_degree_range(degree, max_degree)
    modulus = _resolve_modulus(options, degree_range.stop - 1)
    theory = domain.theory

    elements: list[Covariant] = []
    for component in codomain.components:
        for current_degree in degree_range:
            leaves = _irreducible_basis_leaves(
                theory,
                domain.irreps,
                domain.multiplicities,
                component.irrep,
                current_degree,
                modulus,
                options.seed,
            )
            for leaf in leaves:
                for copy in range(component.multiplicity):
                    elements.append(
                        Covariant(
                            domain,
                            codomain,
                            current_degree,
                            component.irrep,
                            copy,
                            leaf,
                        )
                    )
    return CovariantCollection(
        kind="basis",
        domain=domain,
        codomain=codomain,
        elements=tuple(elements),
        modulus=modulus,
        seed=options.seed,
        degree=degree,
        max_degree=max_degree,
    )


def invariant_basis(
    domain: Representation,
    *,
    degree: int | None = None,
    max_degree: int | None = None,
    options: Options | None = None,
) -> CovariantCollection:
    """Return a vector-space basis of the invariant algebra ``R_G(domain)``.

    Equivalent to :func:`covariant_basis` with a trivial codomain.
    """
    return covariant_basis(
        domain,
        Representation.trivial(domain.theory),
        degree=degree,
        max_degree=max_degree,
        options=options,
    )


# =============================================================================
# Minimal generators
# =============================================================================


def covariant_generators(
    domain: Representation,
    codomain: Representation,
    *,
    max_degree: int,
    options: Options | None = None,
) -> CovariantCollection:
    """Return minimal ``R_G(domain)``-module generators of ``M_G(domain, codomain)``.

    Uses the graded Nakayama lemma degree by degree (``alg:extract-independent-generators``
    in module mode).  For an arbitrary codomain ``Y``, generators are computed for
    each output irrep ``H_nu`` and lifted across the ``m_nu`` output copies
    (Theorem ``thm:module-generator-reduction``).
    """
    _check_compatible(domain, codomain)
    if max_degree < 0:
        raise ValueError("max_degree must be nonnegative")
    options = options or _DEFAULT_OPTIONS
    modulus = _resolve_modulus(options, max_degree)
    theory = domain.theory
    probe_target = _probe_target(options.probe_overshoot)

    elements: list[Covariant] = []
    for component in codomain.components:
        generators_by_degree = extract_independent_generators(
            theory,
            domain.irreps,
            domain.multiplicities,
            component.irrep,
            max_degree,
            probe_target,
            lambda degree: degree - 1,
            options.seed,
            modulus=modulus,
            first_generator_degree=0,
        )
        for current_degree, leaves in enumerate(generators_by_degree):
            for leaf in leaves:
                for copy in range(component.multiplicity):
                    elements.append(
                        Covariant(
                            domain,
                            codomain,
                            current_degree,
                            component.irrep,
                            copy,
                            leaf,
                        )
                    )
    return CovariantCollection(
        kind="generators",
        domain=domain,
        codomain=codomain,
        elements=tuple(elements),
        modulus=modulus,
        seed=options.seed,
        is_module=True,
        max_degree=max_degree,
    )


def invariant_generators(
    domain: Representation,
    *,
    max_degree: int,
    options: Options | None = None,
) -> CovariantCollection:
    """Return minimal ``C``-algebra generators of the invariant algebra ``R_G(domain)``.

    This is the *algebra* reduction (``lem:algebra-generators``): a degree-``D``
    invariant is redundant when it lies in ``(R_{G,+})^2``.  It is **not** the same
    as :func:`covariant_generators` with a trivial codomain, which would return the
    single module generator ``1`` of ``R_G(X)`` over itself.  The returned set
    includes the degree-``0`` constant (faithful to ``alg:extract-independent-generators``);
    the positive-degree elements are the integrity basis used in the learning
    ansatz of ``docs/theory.tex``.
    """
    if max_degree < 0:
        raise ValueError("max_degree must be nonnegative")
    options = options or _DEFAULT_OPTIONS
    modulus = _resolve_modulus(options, max_degree)
    theory = domain.theory
    codomain = Representation.trivial(theory)
    probe_target = _probe_target(options.probe_overshoot)

    generators_by_degree = extract_independent_generators(
        theory,
        domain.irreps,
        domain.multiplicities,
        theory.trivial_irrep,
        max_degree,
        probe_target,
        lambda degree: degree // 2,
        options.seed,
        modulus=modulus,
        first_generator_degree=1,
    )
    elements: list[Covariant] = []
    for current_degree, leaves in enumerate(generators_by_degree):
        for leaf in leaves:
            elements.append(
                Covariant(
                    domain,
                    codomain,
                    current_degree,
                    theory.trivial_irrep,
                    0,
                    leaf,
                )
            )
    return CovariantCollection(
        kind="generators",
        domain=domain,
        codomain=codomain,
        elements=tuple(elements),
        modulus=modulus,
        seed=options.seed,
        is_module=False,
        max_degree=max_degree,
    )


__all__ = (
    # representation data
    "IsotypicComponent",
    "Representation",
    "trivial_representation",
    "irreducible_representation",
    # options
    "Options",
    # covariant objects
    "Covariant",
    "CovariantCombination",
    "CovariantCollection",
    # bases
    "covariant_basis",
    "invariant_basis",
    # generators
    "covariant_generators",
    "invariant_generators",
    # graded dimensions
    "covariant_dimension",
    "invariant_dimension",
    "covariant_hilbert_series",
    "invariant_hilbert_series",
)
