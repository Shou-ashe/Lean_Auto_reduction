"""Stable Lean-diagnostic classification and synthesis repair bookkeeping."""

from __future__ import annotations

from dataclasses import dataclass, replace
import re

from ..models import stable_sha256
from .designs import SynthesisDesign


@dataclass(frozen=True)
class LeanDiagnostic:
    code: str
    normalized: str
    fingerprint: str
    source_line: int | None = None


_CLASSIFIERS: tuple[tuple[str, tuple[str, ...]], ...] = (
    ("forbidden_source", ("forbidden declaration", "authoring fence", "crossed the authoring fence")),
    ("placeholder_or_axiom", ("declaration uses 'sorry'", "contains sorry", "axiom ", "admit")),
    ("unknown_identifier", ("unknown identifier", "unknown constant", "invalid field notation")),
    ("invalid_field_or_constructor", ("invalid constructor", "invalid field", "invalid {...} notation")),
    ("typeclass_synthesis_failed", ("failed to synthesize", "type class instance problem is stuck")),
    ("unsolved_goals", ("unsolved goals", "no goals to be solved")),
    ("termination_or_recursion", ("failed to show termination", "decreasing argument", "declaration has metavariables")),
    ("parser_error", ("unexpected token", "parser", "expected token")),
    ("timeout", ("timed out", "timeout", "maximum heartbeats")),
    ("type_mismatch", ("type mismatch", "application type mismatch", "has type", "but is expected to have type")),
)
_LINE_RE = re.compile(r":(\d+):(\d+):\s*(?:error|warning):")


def classify_lean_diagnostic(diagnostic: str) -> LeanDiagnostic:
    normalized = " ".join(diagnostic.strip().split())[-6000:]
    lowered = normalized.lower()
    code = "other_elaboration_error"
    for candidate, markers in _CLASSIFIERS:
        if any(marker in lowered for marker in markers):
            code = candidate
            break
    line_match = _LINE_RE.search(diagnostic)
    fingerprint = stable_sha256({"code": code, "diagnostic": normalized})
    return LeanDiagnostic(
        code=code,
        normalized=normalized,
        fingerprint=fingerprint,
        source_line=(int(line_match.group(1)) if line_match else None),
    )


def source_window(source: str, diagnostic: LeanDiagnostic, *, radius: int = 8) -> str:
    lines = source.splitlines()
    if diagnostic.source_line is None:
        return "\n".join(lines[-min(len(lines), 40) :])
    center = max(0, diagnostic.source_line - 1)
    start = max(0, center - radius)
    stop = min(len(lines), center + radius + 1)
    return "\n".join(
        f"{ordinal + 1}: {lines[ordinal]}" for ordinal in range(start, stop)
    )


def record_diagnostic(
    design: SynthesisDesign, diagnostic: str | LeanDiagnostic
) -> SynthesisDesign:
    classified = (
        diagnostic
        if isinstance(diagnostic, LeanDiagnostic)
        else classify_lean_diagnostic(diagnostic)
    )
    return replace(
        design,
        diagnostic_history=(*design.diagnostic_history, classified.normalized),
        diagnostic_fingerprints=(
            *design.diagnostic_fingerprints,
            classified.fingerprint,
        ),
        diagnostics=(*design.diagnostics, classified.normalized[-4000:]),
        stage="lean-failed",
        status="repairing",
        estimated_cost=design.estimated_cost + 0.5,
    )


__all__ = [
    "LeanDiagnostic",
    "classify_lean_diagnostic",
    "record_diagnostic",
    "source_window",
]
