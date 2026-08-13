"""Generic Lean diagnostic coaching for NP-hard authoring repair loops.

This module only knows about Lean error *shapes*, not about any particular
benchmark family, so the same coaching applies to every authoring lane.
"""

from __future__ import annotations

import re
from typing import Iterable, Mapping

_LINTER_NOISE_PREFIXES = (
    "Try this:",
    "Note: This linter",
    "This linter can be disabled",
)
_LINTER_NOISE_PATTERNS = (
    re.compile(r"^'?[\w .()]*'? tactic does nothing"),
    re.compile(r"^try 'simp' instead of 'simpa'"),
    re.compile(r"^warning: declaration uses"),
)
_ERROR_PATTERNS: tuple[tuple[re.Pattern[str], str], ...] = (
    (
        re.compile(
            r"Invalid projection",
            re.IGNORECASE,
        ),
        "the checked theorem has function type: apply it to its argument "
        "first, then select a direction with `.mp`/`.mpr` (or `.1`/`.2` on "
        "the applied term). Never project the bare theorem.",
    ),
    (
        re.compile(
            r"Projections cannot be used on functions",
            re.IGNORECASE,
        ),
        "the theorem is a function: apply it to its argument first, then "
        "project the resulting iff with `.mp`/`.mpr` (or `.1`/`.2`).",
    ),
    (
        re.compile(r"Unknown identifier `([^`]*)`", re.IGNORECASE),
        "the name is not in the public surface: use only declarations shown "
        "in public_sources, allowed_primitive_exact_types, and "
        "accepted_dependency_bodies. Do not guess namespaces or names.",
    ),
    (
        re.compile(r"Tactic `rcases` failed", re.DOTALL),
        "destructure an iff hypothesis only after applying it to its "
        "argument: `rcases (theorem x) with ⟨forward, reverse⟩`.",
    ),
    (
        re.compile(r"unsolved goals", re.IGNORECASE),
        "the tactic sequence left goals open: close the displayed goal with "
        "an accepted dependency or a checked semantic-plan lemma, not by "
        "re-proving from scratch.",
    ),
    (
        re.compile(r"(?:Application )?type mismatch", re.IGNORECASE),
        "check argument order and explicit type arguments against the exact "
        "types listed in allowed_primitive_exact_types.",
    ),
    (
        re.compile(
            r"failed to synthesize instance",
            re.IGNORECASE,
        ),
        "a type-class instance was expected: use the fully-qualified "
        "predicate applications shown in the public sources instead of "
        "`∈` notation; do not assume hidden instances.",
    ),
    (
        re.compile(r"axiom gate rejected[^\n]*forbidden axiom sorryAx"),
        "the final artifact still depends on a placeholder (sorryAx). This "
        "is a downstream symptom: fix the earlier error in this diagnostic "
        "and remove every placeholder.",
    ),
)


def _matched_pattern(line: str) -> tuple[re.Pattern[str], str] | None:
    for pattern, hint in _ERROR_PATTERNS:
        if pattern.search(line):
            return (pattern, hint)
    return None


def _is_linter_noise(line: str) -> bool:
    stripped = line.strip()
    if not stripped:
        return False
    if stripped.startswith(_LINTER_NOISE_PREFIXES):
        return True
    return any(pattern.search(stripped) for pattern in _LINTER_NOISE_PATTERNS)


def coach_lean_diagnostic_text(
    diagnostic: str, *, max_coached_chars: int = 4_000
) -> str:
    """Rewrite one raw Lean diagnostic into a deduplicated, coached repair text."""

    if not diagnostic or not diagnostic.strip():
        return ""
    lines = [line for line in diagnostic.splitlines() if line.strip()]
    unique: list[str] = []
    for line in lines:
        if line not in unique:
            unique.append(line)
    hints: list[str] = []
    consumed: set[str] = set()
    remaining: list[str] = []
    swallow = False
    for line in unique:
        stripped = line.strip()
        if swallow and (line.startswith((" ", "\t")) or not stripped):
            continue
        swallow = False
        match = _matched_pattern(line)
        if match:
            _, hint = match
            if hint not in consumed:
                consumed.add(hint)
                hints.append(hint)
            if "axiom gate rejected" in line:
                swallow = False
            else:
                swallow = True
            continue
        if "axiom gate rejected" in line:
            continue
        if _is_linter_noise(line):
            continue
        remaining.append(line)
    parts: list[str] = []
    if hints:
        parts.append("Repair hints from the last Lean diagnostics:")
        parts.extend(f"- {hint}" for hint in hints)
    if remaining:
        if parts:
            parts.append("Raw errors:")
        parts.extend(remaining)
    if any(_is_linter_noise(line) for line in unique):
        parts.append(
            "(linter style suggestions from the diagnostics were removed)"
        )
    return "\n".join(parts)[:max_coached_chars]


def coach_lean_worker_diagnostics(
    items: Iterable[Mapping[str, object]],
    *,
    max_coached_chars: int = 4_000,
) -> str:
    """Coach structured Lean worker diagnostics, prioritizing errors."""

    ordered: list[str] = []
    for item in items:
        message = item.get("message")
        if not isinstance(message, str) or not message.strip():
            continue
        severity = item.get("severity")
        if severity == 1:
            ordered.insert(0, message)
        else:
            ordered.append(message)
    return coach_lean_diagnostic_text(
        "\n".join(ordered), max_coached_chars=max_coached_chars
    )
