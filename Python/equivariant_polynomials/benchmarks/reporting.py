"""Reporting helpers for benchmark summaries."""

from __future__ import annotations

from collections.abc import Iterable

from .benchmark import BenchmarkSummary

__all__ = ("format_benchmark_markdown",)


def format_benchmark_markdown(
    summaries: BenchmarkSummary | Iterable[BenchmarkSummary],
) -> str:
    """Format benchmark summaries as compact Markdown tables."""
    if isinstance(summaries, dict):
        summaries = (summaries,)
    summaries = tuple(summaries)

    def module_value(summary: BenchmarkSummary, key: str) -> object:
        module = summary["module"]
        return None if module is None else module[key]

    def counts(value: object) -> str:
        return "n/a" if value is None else f"`{value}`"

    def seconds(value: object) -> str:
        return "n/a" if value is None else f"{value:.3f}"

    def checks(summary: BenchmarkSummary) -> str:
        values = [summary["algebra"]["matches_hilbert"]]
        if summary["module"] is not None:
            values.append(summary["module"]["matches_hilbert"])
        return "passed" if all(values) else "failed"

    def table(headers: tuple[str, ...], rows: Iterable[tuple[object, ...]]) -> str:
        lines = [
            "| " + " | ".join(headers) + " |",
            "| " + " | ".join("---" for _ in headers) + " |",
        ]
        lines.extend("| " + " | ".join(map(str, row)) + " |" for row in rows)
        return "\n".join(lines)

    count_rows = (
        (
            summary["scenario"]["output_irrep"],
            counts(summary["algebra"]["candidate_dimensions"]),
            counts(summary["algebra"]["generator_counts"]),
            counts(module_value(summary, "candidate_dimensions")),
            counts(module_value(summary, "generator_counts")),
            checks(summary),
        )
        for summary in summaries
    )
    timing_rows = (
        (
            summary["scenario"]["output_irrep"],
            seconds(summary["algebra"]["tree_seconds"]),
            seconds(summary["algebra"]["generator_seconds"]),
            seconds(module_value(summary, "tree_seconds")),
            seconds(module_value(summary, "generator_seconds")),
            seconds(summary["total_seconds"]),
        )
        for summary in summaries
    )

    return (
        "### Generator counts\n\n"
        + table(
            (
                "output irrep",
                "candidate algebra",
                "independent algebra",
                "candidate module",
                "independent module",
                "checks",
            ),
            count_rows,
        )
        + "\n\n### Timings (seconds)\n\n"
        + table(
            (
                "output irrep",
                "invariant tree",
                "algebra basis",
                "covariant tree",
                "module basis",
                "total",
            ),
            timing_rows,
        )
    )
