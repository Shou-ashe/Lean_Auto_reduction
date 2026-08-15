"""Safe job-local source materialization helpers."""

from __future__ import annotations

from dataclasses import replace
from pathlib import Path

from agent.hardness.lean_runner import assert_generated_source_is_safe

from .designs import SynthesisDesign


def validate_editable_fence(source: str, *, expected_signature: str) -> None:
    assert_generated_source_is_safe(source)
    if expected_signature not in source:
        raise ValueError("generated source changed or omitted the frozen declaration signature")
    forbidden = ("import Evaluation", "import Benchmark.Hardness.Oracles", "axiom ")
    if any(marker in source for marker in forbidden):
        raise ValueError("generated source crossed the authoring fence")


def materialize(
    design: SynthesisDesign,
    *,
    path: Path,
    source: str,
    expected_signature: str,
) -> SynthesisDesign:
    validate_editable_fence(source, expected_signature=expected_signature)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source, encoding="utf-8")
    return replace(
        design,
        generated_files=(*design.generated_files, str(path)),
        materialization_attempts=design.materialization_attempts + 1,
        stage="materializing",
        status="materializing",
    )


__all__ = ["materialize", "validate_editable_fence"]
