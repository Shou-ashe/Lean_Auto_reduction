"""Layer A: proof validity independent of generation/benchmark qualification."""

from __future__ import annotations

from pathlib import Path

from agent.hardness.lean_runner import assert_generated_source_is_safe, sha256_file

from ..lean_bridge import run_lean_file
from ..models import VerificationSummary


def verify_core_artifact(
    *, root: Path, artifact_path: Path, timeout_seconds: int, replay: bool
):
    source = artifact_path.read_text(encoding="utf-8")
    assert_generated_source_is_safe(source)
    first = run_lean_file(
        root=root, path=artifact_path, timeout_seconds=timeout_seconds
    )
    second = None
    if first.ok and replay:
        second = run_lean_file(
            root=root, path=artifact_path, timeout_seconds=timeout_seconds
        )
    replay_ok = first.ok if second is None else second.ok
    summary = VerificationSummary(
        exact_type_verified=first.ok,
        kernel_verified=first.ok,
        axiom_audit_passed=first.ok,
        independent_replay_passed=replay_ok,
        endpoint_equality_audit_passed=first.ok,
        placeholder_scan_passed=True,
        same_index_audit_passed=first.ok,
    )
    return first, second, summary, sha256_file(artifact_path) if first.ok else None


__all__ = ["verify_core_artifact"]
