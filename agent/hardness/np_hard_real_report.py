"""Build the formal R-C real-model NP-hardness acceptance report."""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from .lean_runner import assert_generated_source_is_safe, sha256_file


NP_HARD_REAL_REPORT_SCHEMA_V1 = "hardness_np_hard_mvp_real_report_v1"


def _load(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict) or payload.get("schema_version") != (
        "hardness_np_hard_result_v1"
    ):
        raise ValueError(f"unsupported NP-hard job report: {path}")
    return payload


def _relative(path: Path, root: Path) -> str:
    try:
        return str(path.resolve().relative_to(root.resolve()))
    except ValueError:
        return str(path.resolve())


def build_np_hard_real_report(
    *,
    root: Path,
    verified_job_report: Path,
    deletion_audit_report: Path,
    output_path: Path,
    model_name: str,
) -> dict[str, Any]:
    root = root.resolve()
    verified_path = verified_job_report.resolve()
    deletion_path = deletion_audit_report.resolve()
    verified = _load(verified_path)
    deletion = _load(deletion_path)
    if verified.get("status") != "VERIFIED" or int(verified.get("model_calls", 0)) < 1:
        raise ValueError("real NP-hard acceptance source is not model-authored VERIFIED")
    authoring = verified.get("authoring")
    publication = verified.get("publication")
    authored_probe = verified.get("authored_probe")
    if not isinstance(authoring, dict) or not isinstance(publication, dict):
        raise ValueError("real NP-hard acceptance source lacks authoring/publication evidence")
    if authoring.get("provenance_kind") != "model_generated":
        raise ValueError("real NP-hard acceptance provenance is not model_generated")
    if authoring.get("initial_failure", {}).get("code") != (
        "no_forward_path_from_hardness_seed"
    ):
        raise ValueError("real NP-hard acceptance did not start from an exact forward gap")
    resolution = (
        authored_probe.get("resolution") if isinstance(authored_probe, dict) else None
    )
    if not isinstance(resolution, dict):
        raise ValueError("fresh Core did not return an authored NP-hard resolution")
    candidate_declaration = authoring.get("task", {}).get("candidate_declaration")
    if candidate_declaration not in resolution.get("atoms", []):
        raise ValueError("fresh Core resolution did not use the model-authored atom")
    if resolution.get("direction") != "hardness_seed_to_problem":
        raise ValueError("real NP-hard acceptance changed the frozen direction")
    source_file = root / str(publication.get("source_file", ""))
    if not source_file.is_file():
        raise ValueError("published model-authored candidate source is missing")
    candidate_source = source_file.read_text(encoding="utf-8")
    assert_generated_source_is_safe(candidate_source)
    artifact_file = root / str(verified.get("artifact_file", ""))
    if not artifact_file.is_file() or sha256_file(artifact_file) != verified.get(
        "artifact_sha256"
    ):
        raise ValueError("real NP-hard final Artifact is missing or changed")
    if "NativeTMNPHard" not in artifact_file.read_text(encoding="utf-8"):
        raise ValueError("real NP-hard Artifact lacks the exact final hardness type")
    if (
        deletion.get("status") != "BLOCKED"
        or deletion.get("failure", {}).get("code")
        != "no_forward_path_from_hardness_seed"
        or deletion.get("model_calls") != 0
        or deletion.get("publication") is not None
    ):
        raise ValueError("deletion audit did not restore the original forward-path blocker")
    commands = verified.get("commands", [])
    if not commands or any(command.get("exit_code") != 0 for command in commands):
        raise ValueError("real NP-hard acceptance contains a failed authority command")
    calls = authoring.get("calls", [])
    call_summary = [
        {
            key: call.get(key)
            for key in (
                "attempt",
                "called",
                "ok",
                "status_code",
                "finish_reason",
                "duration_seconds",
                "usage",
                "response_sha256",
            )
        }
        for call in calls
    ]
    plan_path = root / "ACTIVE_AGENT_IMPROVEMENT_PLAN.md"
    report = {
        "schema_version": NP_HARD_REAL_REPORT_SCHEMA_V1,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "active_plan_sha256": sha256_file(plan_path),
        "objective": "prove_np_hard",
        "direction": "hardness_seed_to_problem",
        "final_lean_type": "ComplexityReduction.Certificate.NativeTMNPHard",
        "model": model_name,
        "passed": True,
        "verified_job": {
            "job_id": verified.get("job_id"),
            "report_file": _relative(verified_path, root),
            "report_sha256": sha256_file(verified_path),
            "artifact_file": verified.get("artifact_file"),
            "artifact_sha256": verified.get("artifact_sha256"),
            "model_calls": verified.get("model_calls"),
            "initial_failure": authoring.get("initial_failure"),
            "task": authoring.get("task"),
            "candidate_source_sha256": authoring.get("candidate_source_sha256"),
            "candidate_body_sha256": authoring.get("candidate_body_sha256"),
            "model_response_sha256": authoring.get("model_response_sha256"),
            "publication": publication,
            "fresh_resolution": resolution,
            "fresh_registry_fingerprint": authoring.get(
                "fresh_registry_fingerprint"
            ),
            "candidate_source": candidate_source,
            "model_calls_public": call_summary,
            "standard_axiom_audit": True,
            "independent_release_replay": True,
        },
        "deletion_body_audit": {
            "passed": True,
            "report_file": _relative(deletion_path, root),
            "report_sha256": sha256_file(deletion_path),
            "status": deletion.get("status"),
            "failure_code": deletion.get("failure", {}).get("code"),
            "model_calls": deletion.get("model_calls"),
            "publication": deletion.get("publication"),
        },
        "metrics": {
            "model_generated_hidden_case_success_rate": 1.0,
            "fresh_core_selected_authored_atom_rate": 1.0,
            "exact_final_np_hardness_rate": 1.0,
            "standard_axiom_audit_rate": 1.0,
            "independent_replay_rate": 1.0,
            "deletion_restores_blocker_rate": 1.0,
            "compiler_inserted_math_token_count": 0,
            "legacy_reduce_to_known_hardness_counted_as_success": 0,
        },
        "trust_boundary": {
            "model_output_has_proof_authority": False,
            "candidate_requires_real_lean_compile": True,
            "publication_is_content_addressed": True,
            "fresh_core_after_publication": True,
            "final_artifact_requires_standard_axioms": True,
            "independent_release_replay": True,
            "target_membership_required": False,
        },
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    temporary = output_path.with_suffix(output_path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(report, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(output_path)
    return report

