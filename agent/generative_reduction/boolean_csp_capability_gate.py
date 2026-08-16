"""Run one isolated Boolean-CSP generation-capability gate over all 20 cases."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Mapping

from .boolean_csp_regression import run_recursive_boolean_csp_regression


ROOT = Path(__file__).resolve().parents[2]
HARDNESS = "ComplexityReduction.Domain.BooleanCSP.Hardness."

# These declarations are legitimate packaging/search routes, but selecting
# them directly leaves an unconstrained PresentedProblem binder and tests route
# guessing instead of the requested local generation capability.  They remain
# legal transitive dependencies of the explicit transport packager.
TRANSPORT_CANDIDATE_EXCLUSIONS = (
    "ComplexityReduction.Agent.GenerativeReduction.FinalCheck.exactEndpoint",
    "ComplexityReduction.Agent.GenerativeReduction.ProofReconstruction.exactEndpoint",
    "ComplexityReduction.Agent.GenerativeReduction.RuleKernel.completenessProjection",
    "ComplexityReduction.Agent.GenerativeReduction.RuleKernel.exactHardness",
    "ComplexityReduction.Certificate.NativeTMNPComplete.nativeHardness",
    "ComplexityReduction.Protocol.TypedNPHardEvidenceV1.toNativeHardness",
    "ComplexityReduction.Protocol.TypedNPHardResultV1.extractNativeHardness",
    "ComplexityReduction.Agent.GenerativeReduction.RuleKernel.completenessAlongPath",
    "ComplexityReduction.Agent.GenerativeReduction.RuleKernel.hardnessAlongPath",
    "ComplexityReduction.Certificate.NativeTMNPHard.alongPath",
    "ComplexityReduction.Certificate.NativeTMNPHard.ofCompleteAlongPath",
)

SHARED_TRANSPORT_FORBIDDEN = (
    HARDNESS + "nPHard_of_interpretation_auto",
    HARDNESS + "certifiedReduction_of_interpretation_auto",
    HARDNESS + "nPHard_of_interpretsHardCore",
    HARDNESS + "nPHard_oneInThree_of_exactlyTwo3",
    HARDNESS + "nPHard_exactlyTwo3_of_oneInThree",
    HARDNESS + "exactlyTwo3CoreNPHard_of_oneInThree",
    HARDNESS + "exactlyTwo3CoreNPHard",
)

DIRECT_TM_FORBIDDEN = (
    *SHARED_TRANSPORT_FORBIDDEN,
    HARDNESS + "interpretation_tmPolyTime",
)

SEMANTIC_FORBIDDEN = (
    *SHARED_TRANSPORT_FORBIDDEN,
    HARDNESS + "nPHard_of_interpretation",
    HARDNESS + "certifiedReduction_of_interpretation",
    HARDNESS + "interpret_satisfiable_iff",
    HARDNESS + "interpret_satisfies_forward",
    HARDNESS + "interpret_satisfies_reverse",
    HARDNESS + "oneInThree_satisfiable_iff_exactlyTwo3",
    HARDNESS + "exactlyTwo3_satisfiable_iff_oneInThree",
)


def _artifact_uses(artifact: object, declaration: object) -> bool:
    if not isinstance(artifact, str) or not isinstance(declaration, str):
        return False
    path = Path(artifact)
    if not path.is_file():
        return False
    return declaration in path.read_text(encoding="utf-8")


def _matches_gate(gate: str, capability: Mapping[str, Any]) -> bool:
    exact_type = str(capability.get("exact_type") or "")
    if gate == "direct-tm":
        return "ComplexityReduction.TMPolyTimeMap" in exact_type
    return (
        "ExecutableSemanticProof" in exact_type
        or "ProgramSemanticProof" in exact_type
        or "CertifiedReduction" in exact_type
        or ("Satisfiable" in exact_type and ("↔" in exact_type or "Iff" in exact_type))
        or ("accepts" in exact_type and ("↔" in exact_type or "Iff" in exact_type))
    )


def evaluate_capability_gate(
    report: Mapping[str, Any], gate: str
) -> dict[str, Any]:
    matched: list[dict[str, Any]] = []
    final_used: list[dict[str, Any]] = []
    verified_with_final_used: set[str] = set()
    target_specific_plan_cases: set[str] = set()
    context_ready_plan_cases: set[str] = set()
    executable_typed_plan_cases: set[str] = set()
    capability_budget_reserved_cases: set[str] = set()
    final_used_contributions: list[dict[str, Any]] = []
    for row in report.get("cases", ()):
        if not isinstance(row, dict):
            continue
        for capability in row.get("generated_capabilities", ()):
            if not isinstance(capability, dict) or not _matches_gate(gate, capability):
                continue
            item = {
                "case": row.get("case"),
                "proof_status": row.get("proof_status"),
                "declaration": capability.get("declaration"),
                "exact_type": capability.get("exact_type"),
                "used_by_final_artifact": _artifact_uses(
                    row.get("artifact"), capability.get("declaration")
                ),
            }
            matched.append(item)
            if item["used_by_final_artifact"]:
                final_used.append(item)
                if item["proof_status"] == "VERIFIED" and isinstance(
                    item["case"], str
                ):
                    verified_with_final_used.add(item["case"])
        for plan in row.get("typed_capability_plans", ()):
            if not isinstance(plan, dict):
                continue
            plan_id = str(plan.get("plan_id") or "")
            matches_plan = (
                (gate == "direct-tm" and plan_id.startswith("direct-tm-plan-"))
                or (gate == "semantic" and plan_id.startswith("semantic-plan-"))
            )
            if matches_plan and isinstance(row.get("case"), str):
                case = str(row["case"])
                target_specific_plan_cases.add(case)
                exact_goal = " ".join(str(plan.get("exact_goal") or "").split())
                capsules = row.get("context_capsules", ())
                if any(
                    isinstance(capsule, dict)
                    and bool(capsule.get("generation_context_ready"))
                    and " ".join(str(capsule.get("exact_goal") or "").split())
                    == exact_goal
                    for capsule in capsules
                ):
                    context_ready_plan_cases.add(case)
                if gate == "direct-tm":
                    nodes = tuple(
                        node
                        for node in plan.get("nodes", ())
                        if isinstance(node, dict)
                    )
                    node_ids = {str(node.get("node_id") or "") for node in nodes}
                    if (
                        nodes
                        and str(plan.get("final_node_id") or "") in node_ids
                        and all(
                            all(
                                str(dependency) in node_ids
                                for dependency in node.get("dependency_node_ids", ())
                            )
                            for node in nodes
                        )
                    ):
                        executable_typed_plan_cases.add(case)
                else:
                    forward = plan.get("forward")
                    reverse = plan.get("reverse")
                    if (
                        isinstance(forward, dict)
                        and forward.get("direction") == "forward"
                        and bool(forward.get("witness_schema"))
                        and isinstance(reverse, dict)
                        and reverse.get("direction") == "reverse"
                        and bool(reverse.get("witness_schema"))
                    ):
                        executable_typed_plan_cases.add(case)
        for receipt in row.get("contribution_receipts", ()):
            if not isinstance(receipt, dict):
                continue
            if receipt.get("capability_kind") != gate:
                continue
            if not receipt.get("final_artifact_used"):
                continue
            final_used_contributions.append(
                {
                    "case": row.get("case"),
                    "capability_declaration": receipt.get(
                        "capability_declaration"
                    ),
                    "plan_id": receipt.get("plan_id"),
                    "brief_id": receipt.get("brief_id"),
                    "contribution_class": receipt.get("contribution_class"),
                    "forbidden_audit_passed": receipt.get(
                        "forbidden_audit_passed"
                    ),
                    "independent_lean_passed": receipt.get(
                        "independent_lean_passed"
                    ),
                }
            )
        for reservation in row.get("capability_budget_reservations", ()):
            if not isinstance(reservation, dict):
                continue
            hierarchy = tuple(str(item) for item in reservation.get("hierarchy", ()))
            expected_prefix = (
                "capability:direct-tm-plan-"
                if gate == "direct-tm"
                else "capability:semantic-plan-"
            )
            if (
                reservation.get("status")
                == "reserved-for-immediate-sequential-execution"
                and any(item.startswith(expected_prefix) for item in hierarchy)
                and isinstance(row.get("case"), str)
            ):
                capability_budget_reserved_cases.add(str(row["case"]))
    completed_case_count = int((report.get("suite") or {}).get("completed_case_count", 0))
    verified_case_count = int((report.get("results") or {}).get("verified_case_count", 0))
    validation = report.get("validation") if isinstance(report.get("validation"), dict) else {}
    real_api = report.get("real_api") if isinstance(report.get("real_api"), dict) else {}
    required_nonreuse_cases = 17
    receipt_consistency = all(
        item["forbidden_audit_passed"]
        and item["independent_lean_passed"]
        and item["plan_id"]
        and item["brief_id"]
        for item in final_used_contributions
    )
    hard_checks = {
        "all_20_cases_completed": completed_case_count == 20,
        "all_20_cases_verified": verified_case_count == 20,
        "real_api_was_called": int(real_api.get("total_calls", 0)) > 0,
        "all_called_requests_http_200": bool(
            validation.get("all_called_requests_http_200")
        ),
        "forbidden_dependency_count_is_zero": int(
            validation.get("forbidden_direct_or_transitive_dependency_count", 0)
        )
        == 0,
        "unresolved_probe_handle_count_is_zero": bool(
            validation.get("unresolved_probe_handle_count_is_zero")
        ),
        "empty_context_generator_call_count_is_zero": bool(
            validation.get("empty_context_generator_call_count_is_zero")
        ),
        "target_specific_plan_coverage": (
            len(target_specific_plan_cases) >= required_nonreuse_cases
        ),
        "typed_plan_is_executable": (
            len(executable_typed_plan_cases) >= required_nonreuse_cases
        ),
        "typed_context_coverage": (
            len(context_ready_plan_cases) >= required_nonreuse_cases
        ),
        "capability_budget_reservation_coverage": (
            len(capability_budget_reserved_cases) >= required_nonreuse_cases
        ),
        "generated_capability_final_use_coverage": (
            len(verified_with_final_used) >= required_nonreuse_cases
        ),
        "contribution_receipt_final_use_coverage": (
            len({str(item.get("case")) for item in final_used_contributions})
            >= required_nonreuse_cases
        ),
        "receipt_consistency": receipt_consistency,
    }
    gate_passed = all(hard_checks.values())
    return {
        "gate": gate,
        "required_generated_shape": (
            "TMPolyTimeMap exact capability"
            if gate == "direct-tm"
            else "semantic iff or semantic-bearing CertifiedReduction capability"
        ),
        "matched_generated_capability_count": len(matched),
        "final_used_matched_capability_count": len(final_used),
        "verified_case_count_with_final_used_match": len(verified_with_final_used),
        "verified_cases_with_final_used_match": sorted(verified_with_final_used),
        "capability_generation_observed": bool(final_used),
        "target_specific_plan_case_count": len(target_specific_plan_cases),
        "target_specific_plan_cases": sorted(target_specific_plan_cases),
        "context_ready_plan_case_count": len(context_ready_plan_cases),
        "context_ready_plan_cases": sorted(context_ready_plan_cases),
        "executable_typed_plan_case_count": len(executable_typed_plan_cases),
        "executable_typed_plan_cases": sorted(executable_typed_plan_cases),
        "capability_budget_reserved_case_count": len(
            capability_budget_reserved_cases
        ),
        "capability_budget_reserved_cases": sorted(
            capability_budget_reserved_cases
        ),
        "required_nonreuse_case_count": required_nonreuse_cases,
        "final_used_contribution_count": len(final_used_contributions),
        "final_used_contributions": final_used_contributions,
        "receipt_consistency_passed": receipt_consistency,
        "hard_checks": hard_checks,
        "gate_passed": gate_passed,
        "matched_capabilities": matched,
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Run one direct-TM or semantic generation gate on Boolean CSP 20"
    )
    parser.add_argument("--gate", choices=("direct-tm", "semantic"), required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--report-path", type=Path, required=True)
    parser.add_argument("--env-file", type=Path, default=ROOT / ".env")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--lean-timeout", type=int, default=600)
    parser.add_argument("--model", default=None)
    parser.add_argument("--model-timeout", type=int, default=180)
    parser.add_argument("--model-max-tokens", type=int, default=12000)
    parser.add_argument("--model-max-retries", type=int, default=0)
    parser.add_argument("--reasoning-effort", default="low")
    return parser


def main() -> int:
    arguments = build_parser().parse_args()
    gate_forbidden = (
        DIRECT_TM_FORBIDDEN if arguments.gate == "direct-tm" else SEMANTIC_FORBIDDEN
    )
    report = run_recursive_boolean_csp_regression(
        root=ROOT,
        output_root=arguments.output_root,
        env_file=arguments.env_file,
        jobs=arguments.jobs,
        profile="benchmark",
        lean_timeout_seconds=arguments.lean_timeout,
        model=arguments.model,
        model_timeout_seconds=arguments.model_timeout,
        model_max_tokens=arguments.model_max_tokens,
        model_max_retries=arguments.model_max_retries,
        reasoning_effort=arguments.reasoning_effort,
        report_path=None,
        extra_forbidden_declarations=gate_forbidden,
        excluded_candidate_declarations=TRANSPORT_CANDIDATE_EXCLUSIONS,
    )
    report["capability_gate_evaluation"] = evaluate_capability_gate(
        report, arguments.gate
    )
    report["route_policy"]["capability_gate"] = arguments.gate
    arguments.report_path.parent.mkdir(parents=True, exist_ok=True)
    arguments.report_path.write_text(
        json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (arguments.output_root / "summary.json").write_text(
        json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True))
    return 0 if report["capability_gate_evaluation"]["gate_passed"] else 2


if __name__ == "__main__":
    raise SystemExit(main())


__all__ = [
    "DIRECT_TM_FORBIDDEN",
    "SEMANTIC_FORBIDDEN",
    "TRANSPORT_CANDIDATE_EXCLUSIONS",
    "evaluate_capability_gate",
    "main",
]
