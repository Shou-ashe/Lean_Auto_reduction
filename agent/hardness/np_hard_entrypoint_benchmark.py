"""G-E qualification for input normalization and the model-auto entrypoint."""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from .lean_runner import build_module_command, run_command, sha256_file
from .model_client import ModelResponse
from .np_hard import NPHardAgentConfigV1, NPHardAgentV1
from .np_hard_generalization import load_np_hard_generalization_suite


NP_HARD_ENTRYPOINT_REPORT_SCHEMA_V1 = "hardness_np_hard_entrypoint_report_v2"


def _write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


class _TaggedThreeSATModel:
    def __init__(self):
        self.calls = 0

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        assert "no proof authority" in system
        self.calls += 1
        payload = json.loads(prompt)
        response = dict(payload["response_template"])
        response["replacement_body"] = """by
  refine
    { program :=
        Benchmark.Hardness.Inputs.NPHardMVP.ModelAuthoredTaggedThreeSAT.forwardProgram
      correct := ?_ }
  intro input
  rfl
"""
        return ModelResponse(
            called=True,
            ok=True,
            content=json.dumps(response),
            error=None,
            status_code=200,
            duration_seconds=0.0,
            usage={"fixture_tokens": 0},
            attempts=1,
            finish_reason="stop",
        )


def _run(
    *, root: Path, output: Path, module: str, problem: str, model=None
):
    return NPHardAgentV1(
        NPHardAgentConfigV1(
            root=root,
            input_module=module,
            problem_declaration=problem,
            output_dir=output,
            lean_timeout_seconds=600,
            authoring_mode="model-auto",
            runtime_prebuilt=True,
        ),
        model_client=model,
    ).run()


def run_np_hard_entrypoint_benchmark(
    *, root: Path, suite_path: Path, output_root: Path, report_path: Path
) -> dict[str, Any]:
    root = root.resolve()
    output_root = output_root.resolve()
    report_path = report_path.resolve()
    if output_root.exists() and any(output_root.iterdir()):
        raise ValueError(f"G-E output must be fresh: {output_root}")
    output_root.mkdir(parents=True, exist_ok=True)
    suite = load_np_hard_generalization_suite(suite_path.resolve(), root=root)
    existing = [case for case in suite.cases if case.kind == "existing_route"]
    modules = {case.module for case in existing} | {
        "ComplexityReduction.Certificate.NativeCookLevin",
        "Benchmark.Hardness.Inputs.NPHardGeneralization.InputNormalization",
        "Benchmark.Hardness.Inputs.NPHardMVP.ModelAuthoredTaggedThreeSAT",
    }
    prebuild = run_command(
        build_module_command(modules), cwd=root / "Lean", timeout_seconds=900
    )
    if not prebuild.ok:
        raise ValueError("G-E prebuild failed")

    existing_rows: list[dict[str, Any]] = []
    for case in existing:
        result = _run(
            root=root,
            output=output_root / "existing" / case.id,
            module=case.module,
            problem=case.problem,
        )
        payload = result.to_dict()
        matched = (
            result.status == "VERIFIED"
            and result.model_calls == 0
            and payload["input_identity"] is not None
            and payload["route"] is not None
            and payload["selected_hub"] is not None
            and payload["model_call_ledger"] == []
            and payload["certificates"].get("replay", {}).get("passed") is True
        )
        existing_rows.append(
            {
                "case_id": case.id,
                "status": result.status,
                "model_calls": result.model_calls,
                "input_identity": payload["input_identity"],
                "selected_hub": payload["selected_hub"],
                "route": payload["route"],
                "certificates": payload["certificates"],
                "matched": matched,
            }
        )

    normalization_specs = (
        (
            "exact",
            "ComplexityReduction.Certificate.NativeCookLevin",
            "canonical-three-sat-exact",
        ),
        (
            "alias",
            "Benchmark.Hardness.Inputs.Completeness.RegisteredThreeSAT",
            "canonical-three-sat",
        ),
        (
            "wrapper",
            "Benchmark.Hardness.Inputs.NPHardGeneralization.InputNormalization",
            "canonical-three-sat-wrapper",
        ),
    )
    normalization_rows: list[dict[str, Any]] = []
    for kind, module, stable_id in normalization_specs:
        result = _run(
            root=root,
            output=output_root / "normalization" / kind,
            module=module,
            problem=stable_id,
        )
        identity = result.input_identity or {}
        normalization_rows.append(
            {
                "kind": kind,
                "stable_id": stable_id,
                "status": result.status,
                "model_calls": result.model_calls,
                "identity": identity,
                "matched": (
                    result.status == "VERIFIED"
                    and result.model_calls == 0
                    and identity.get("normalization_kind") == kind
                    and identity.get("normalization_certificate") == "lean-checked-artifact"
                ),
            }
        )

    bare = _run(
        root=root,
        output=output_root / "normalization" / "bare",
        module="Benchmark.Hardness.Inputs.NPHardGeneralization.InputNormalization",
        problem="canonical-three-sat-bare-encoding",
    )
    bare_identity = bare.input_identity or {}
    bare_matched = (
        bare.status == "VERIFIED"
        and bare.model_calls == 0
        and bare_identity.get("normalization_kind") == "encoding"
        and bare_identity.get("normalization_certificate")
        == "lean-checked-artifact"
        and bare_identity.get("canonical_problem")
        == "ComplexityReduction.Certificate.NativeCookLevin.threeSATProblem"
    )
    author_model = _TaggedThreeSATModel()
    authored = _run(
        root=root,
        output=output_root / "authoring",
        module="Benchmark.Hardness.Inputs.NPHardMVP.ModelAuthoredTaggedThreeSAT",
        problem="Benchmark.Hardness.Inputs.NPHardMVP.ModelAuthoredTaggedThreeSAT.source",
        model=author_model,
    )
    authored_payload = authored.to_dict()
    authoring_matched = (
        authored.status == "VERIFIED"
        and authored.model_calls == author_model.calls == 1
        and authored.probe is not None
        and authored.probe.failure is not None
        and authored.probe.failure.code == "no_forward_path_from_hardness_seed"
        and authored_payload["input_identity"] is not None
        and authored_payload["selected_hub"] is not None
        and authored_payload["route"] is not None
        and len(authored_payload["model_call_ledger"]) == 1
        and authored_payload["certificates"].get("replay", {}).get("passed") is True
    )
    metrics = {
        "normalization_case_count": len(normalization_rows),
        "normalization_verified_count": sum(row["matched"] for row in normalization_rows),
        "existing_route_count": len(existing_rows),
        "existing_route_verified_count": sum(row["matched"] for row in existing_rows),
        "existing_route_model_calls": sum(row["model_calls"] for row in existing_rows),
        "unique_lawful_presentation_count": int(bare_matched),
        "authoring_after_deterministic_blocker_count": int(authoring_matched),
        "fixture_model_calls": authored.model_calls,
    }
    passed = (
        prebuild.ok
        and all(row["matched"] for row in existing_rows)
        and all(row["matched"] for row in normalization_rows)
        and metrics["unique_lawful_presentation_count"] == 1
        and authoring_matched
    )
    report = {
        "schema_version": NP_HARD_ENTRYPOINT_REPORT_SCHEMA_V1,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "stage": "G-E",
        "passed": passed,
        "suite_sha256": sha256_file(suite_path),
        "input_registry_sha256": sha256_file(
            root / "Benchmark" / "Hardness" / "np_hard_input_registry.json"
        ),
        "active_plan_sha256": sha256_file(root / "ACTIVE_AGENT_IMPROVEMENT_PLAN.md"),
        "prebuild": prebuild.to_dict(),
        "metrics": metrics,
        "normalization_cases": normalization_rows,
        "existing_route_cases": existing_rows,
        "bare_encoding": bare.to_dict(),
        "authoring_case": authored_payload,
    }
    _write_json(report_path, report)
    _write_json(output_root / "report.json", report)
    return report
