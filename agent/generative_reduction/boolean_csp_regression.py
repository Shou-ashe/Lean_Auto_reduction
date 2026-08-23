"""Full recursive-agent regression over the frozen Boolean-CSP suite.

This driver intentionally lives outside ``scripts/`` so the repository keeps
one public benchmark runner.  It reads only the answer-free public suite while
cases are running and writes a separate recursive-agent report.
"""

from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import asdict, replace
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import time
from typing import Any, Mapping, Sequence

from agent.hardness.boolean_csp_np_hard_benchmark import BooleanCSPSuite, load_suite
from agent.hardness.model_client import DeepSeekConfig

from .budgets import SearchBudget
from .capability_gate_policy import CapabilityGatePolicy, gadget_authoring_policy
from .gadget_authoring_freeze import validate_gadget_authoring_freeze
from .model.gadget_authoring import (
    GADGET_AUTHORING_BASE_TOKEN_PROFILE,
    GADGET_AUTHORING_ESCALATED_TOKEN_PROFILE,
)
from .models import ContributionClass, ModelPolicy, Strategy, stable_sha256
from .orchestrator import GenerativeReductionConfig, GenerativeReductionOrchestrator
from .plugins import load_plugin


FORBIDDEN_DICHOTOMY_DECLARATIONS = (
    "ComplexityReduction.Domain.BooleanCSP.Hardness.NativeTMNPHard_of_notSchaeferTractable",
    "ComplexityReduction.Domain.BooleanCSP.Hardness.NativeTMNPHard_of_notSchaeferTractable_with_oneInThree",
    "ComplexityReduction.Domain.BooleanCSP.schaefer_dichotomy",
    "ComplexityReduction.Domain.BooleanCSP.Hardness.CanonicalHardCores.oneInThreeInterpretation",
    "ComplexityReduction.Domain.BooleanCSP.Hardness.CanonicalHardCores.naeInterpretation",
    "ComplexityReduction.Domain.BooleanCSP.Hardness.CanonicalDatabase.gadget",
    "ComplexityReduction.Domain.BooleanCSP.Hardness.CanonicalHardCores.exactlyOne_closed_of_notSchaeferTractable",
    "ComplexityReduction.Domain.BooleanCSP.Hardness.CanonicalHardCores.nae_closed_of_notSchaeferTractable",
)
DEFAULT_REPORT_NAME = "GENERAL_AGENT_BOOLEAN_CSP_DETERMINISTIC_BASELINE_REAL_API_REPORT.json"
BASELINE_POLICY_NAME = "deterministic-baseline"
BASELINE_POLICY_VERSION = "2026-08-20"


def recursive_benchmark_budget() -> SearchBudget:
    return SearchBudget(
        max_search_rounds=120,
        max_search_depth=16,
        max_expanded_states=512,
        max_frontier_width=24,
        max_capability_plans=512,
        max_exact_closure_candidates=16,
        max_guidance_candidates_per_goal=12,
        max_guidance_plans_per_goal=8,
        max_actions_per_provider=16,
        max_theorem_expansions_before_synthesis=4,
        min_synthesis_action_expansions=1,
        min_synthesis_materializations=1,
        synthesis_activation_deadline=2,
        stagnation_window=8,
        max_lean_checks=320,
        max_model_calls=32,
        max_strategy_calls=8,
        max_authoring_calls=24,
        max_synthesis_designs=8,
        max_authoring_attempts_per_stage=2,
        max_generated_files=24,
        max_branching_per_expansion=3,
        max_application_frames=64,
        max_data_witness_candidates=7,
        max_dependent_reinstantiations=160,
        max_action_failures_per_goal=32,
        max_frame_verification_checks=80,
        max_reconstruction_repairs=4,
        max_repairs_per_design=5,
        max_requeues_per_state=320,
        max_recursive_substep_plans=240,
        wall_clock_timeout_seconds=3600,
    )


def _read_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object at {path}")
    return value


def _write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def _case_label(module: str) -> str:
    return module.rsplit(".", 1)[-1]


def _workspace_revision(root: Path) -> dict[str, Any]:
    def git(*arguments: str) -> str:
        completed = subprocess.run(
            ("git", *arguments),
            cwd=root,
            text=True,
            capture_output=True,
            check=False,
        )
        return completed.stdout.strip() if completed.returncode == 0 else ""

    source_roots = (
        root / "agent" / "generative_reduction",
        root / "agent" / "hardness",
        root / "Benchmark" / "Hardness",
        root / "Lean" / "Reference" / "ComplexityReduction",
        root / "Lean" / "Reference" / "Benchmark" / "Hardness",
    )
    source_files: list[Path] = []
    for source_root in source_roots:
        if not source_root.exists():
            continue
        source_files.extend(
            path
            for path in source_root.rglob("*")
            if path.is_file()
            and path.suffix in {".json", ".lean", ".md", ".py", ".toml"}
            and "__pycache__" not in path.parts
        )
    source_files.extend(
        path
        for path in (
            root / "ACTIVE_AGENT_IMPROVEMENT_PLAN.md",
            root / "scripts" / "run_hardness_benchmark.py",
        )
        if path.is_file()
    )
    digest = hashlib.sha256()
    for path in sorted(set(source_files)):
        relative = path.relative_to(root).as_posix().encode("utf-8")
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        payload = path.read_bytes()
        digest.update(len(payload).to_bytes(8, "big"))
        digest.update(payload)
    status = git("status", "--short")
    return {
        "git_commit": git("rev-parse", "HEAD") or None,
        "git_dirty": bool(status),
        "git_status_sha256": stable_sha256(status.splitlines()),
        "workspace_source_sha256": "sha256:" + digest.hexdigest(),
    }


def _boolean_csp_plugin_inventory() -> dict[str, Any]:
    plugin = load_plugin("boolean_csp")
    finite_plugins = tuple(plugin.finite_synthesis_plugins)
    return {
        "configured_domain_plugins": [plugin.name],
        "installed_finite_synthesis_plugins": [item.name for item in finite_plugins],
        "runtime_finite_synthesis_plugins": [item.name for item in finite_plugins],
        "disabled_finite_synthesis_plugins": [],
        "finite_synthesis_plugin_classes": {
            item.name: str(getattr(item, "candidate_class", "unknown"))
            for item in finite_plugins
        },
    }


def _is_structured_gadget_receipt(value: object) -> bool:
    if not isinstance(value, Mapping):
        return False
    schema = value.get("schema_version")
    return isinstance(schema, str) and schema.startswith(
        "boolean_csp_gadget_authoring_receipt_v"
    )


def _sha256_with_prefix(value: object) -> str:
    text = str(value or "")
    if not text:
        return ""
    return text if text.startswith("sha256:") else "sha256:" + text


def _model_gadget_contributions(
    rows: Sequence[Mapping[str, Any]],
) -> tuple[tuple[Mapping[str, Any], Mapping[str, Any]], ...]:
    return tuple(
        (row, receipt)
        for row in rows
        for receipt in row.get("contribution_receipts", ())
        if isinstance(receipt, Mapping)
        and receipt.get("contribution_class")
        == ContributionClass.MODEL_GENERATED_CAPABILITY.value
        and receipt.get("capability_kind") in {"gadget", "language-interpretation"}
    )


def _verified_structured_receipt(
    row: Mapping[str, Any], contribution: Mapping[str, Any]
) -> Mapping[str, Any] | None:
    declaration = contribution.get("capability_declaration")
    source_hashes = set(contribution.get("model_generated_source_hashes", ()))
    return next(
        (
            item
            for item in row.get("typed_capability_plans", ())
            if _is_structured_gadget_receipt(item)
            and item.get("status") == "lean-verified"
            and item.get("declaration") == declaration
            and item.get("source_sha256") in source_hashes
        ),
        None,
    )


def _structured_repair_payload_hashes(
    row: Mapping[str, Any], verified: Mapping[str, Any]
) -> tuple[str, ...]:
    design_id = verified.get("design_id")
    verified_attempt = int(verified.get("attempt", 0))
    repairs = sorted(
        (
            item
            for item in row.get("typed_capability_plans", ())
            if _is_structured_gadget_receipt(item)
            and item.get("design_id") == design_id
            and item.get("kind") == "repair"
            and int(item.get("attempt", 0)) <= verified_attempt
        ),
        key=lambda item: (
            int(item.get("attempt", 0)),
            int(item.get("transport_attempt", 1)),
        ),
    )
    return tuple(
        str((item.get("model_attempt") or {}).get("response_payload_sha256") or "")
        for item in repairs
    )


def _repair_prompts_have_matching_base_hash(rows: Sequence[Mapping[str, Any]]) -> bool:
    """Audit that every repair prompt is bound to its immediately prior payload.

    A provider transport failure cannot echo the requested base hash, so the
    request-side hash and response-side echo are deliberately separate fields.
    The request must always match the previous receipt; a returned echo, when
    present, must match the request as well.
    """

    for row in rows:
        structured = [
            item
            for item in row.get("typed_capability_plans", ())
            if _is_structured_gadget_receipt(item)
        ]
        grouped: dict[tuple[str, int], list[Mapping[str, Any]]] = {}
        legacy_attempts_by_design: Counter[str] = Counter()
        for item in structured:
            design_id = str(item.get("design_id") or "")
            raw_attempt = item.get("logical_attempt", item.get("attempt"))
            if raw_attempt is None:
                legacy_attempts_by_design[design_id] += 1
                logical_attempt = legacy_attempts_by_design[design_id]
            else:
                logical_attempt = int(raw_attempt)
            if not design_id or logical_attempt < 1:
                return False
            grouped.setdefault((design_id, logical_attempt), []).append(item)
        previous_by_design: dict[str, str] = {}
        for (design_id, _), group in sorted(
            grouped.items(), key=lambda entry: (entry[0][0], entry[0][1])
        ):
            ordered = sorted(
                group, key=lambda item: int(item.get("transport_attempt", 1))
            )
            kinds = {str(item.get("kind") or "") for item in ordered}
            if len(kinds) != 1:
                return False
            for item in ordered:
                model_attempt = item.get("model_attempt")
                if not isinstance(model_attempt, Mapping):
                    return False
                requested = model_attempt.get("requested_base_sha256")
                returned = model_attempt.get("returned_base_sha256")
                if item.get("kind") == "repair":
                    if not isinstance(requested, str) or not requested:
                        return False
                    if previous_by_design.get(design_id) != requested:
                        return False
                    if returned is not None and returned != requested:
                        return False
            terminal_attempt = ordered[-1].get("model_attempt")
            if not isinstance(terminal_attempt, Mapping):
                return False
            response_payload = terminal_attempt.get("response_payload_sha256")
            if not isinstance(response_payload, str) or not response_payload:
                return False
            previous_by_design[design_id] = response_payload

        for item in row.get("repair_lineage", ()):
            if not isinstance(item, Mapping) or item.get("kind") != "repair":
                continue
            if item.get("protocol") == "structured-gadget-authoring":
                requested = item.get("requested_base_sha256")
                returned = item.get("returned_base_sha256")
                if not isinstance(requested, str) or not requested:
                    return False
                if returned is not None and returned != requested:
                    return False
            elif not bool(item.get("base_sha256")):
                return False
    return True


def _adaptive_gadget_token_audit(
    rows: Sequence[Mapping[str, Any]], policy: CapabilityGatePolicy | None
) -> dict[str, Any]:
    if policy is None or policy.name != "gadget-authoring":
        return {
            "profile_calls": {},
            "base_profile_call_count": 0,
            "escalated_profile_call_count": 0,
            "length_exhaustion_call_count": 0,
            "successful_escalation_count": 0,
            "terminal_nonconvergence_count": 0,
            "semantic_repair_nonconvergence_count": 0,
            "source_core_call_counts": {},
            "violations": [],
            "token_profiles_match_policy": True,
            "escalations_follow_length_on_same_prompt": True,
            "escalation_lineage_complete": True,
            "nonconvergence_receipts_complete": True,
            "source_route_attribution_complete": True,
        }

    violations: list[dict[str, Any]] = []
    gadget_calls: list[tuple[str, Mapping[str, Any]]] = []
    structured_by_call: dict[
        tuple[str, str, int, int, str], Mapping[str, Any]
    ] = {}
    for row in rows:
        case_id = str(row.get("case_id") or "")
        for receipt in row.get("typed_capability_plans", ()):
            if not _is_structured_gadget_receipt(receipt):
                continue
            model_attempt = receipt.get("model_attempt")
            if not isinstance(model_attempt, Mapping):
                continue
            key = (
                case_id,
                str(receipt.get("authoring_context_key") or ""),
                int(receipt.get("logical_attempt", receipt.get("attempt", 0))),
                int(receipt.get("transport_attempt", 1)),
                str(model_attempt.get("purpose") or ""),
            )
            structured_by_call[key] = receipt
        for call in row.get("model_calls", ()):
            if (
                isinstance(call, Mapping)
                and str(call.get("purpose") or "").startswith(
                    "gadget-authoring"
                )
            ):
                gadget_calls.append((case_id, call))

    grouped: dict[
        tuple[str, str, int, str], list[Mapping[str, Any]]
    ] = {}
    profile_counts: Counter[str] = Counter()
    source_counts: Counter[str] = Counter()
    for case_id, call in gadget_calls:
        profile = str(call.get("token_profile") or "")
        source_core = str(call.get("source_core") or "")
        context_key = str(call.get("authoring_context_key") or "")
        logical_attempt = int(call.get("logical_attempt") or 0)
        transport_attempt = int(call.get("transport_attempt") or 0)
        purpose = str(call.get("purpose") or "")
        profile_counts[profile] += 1
        source_counts[source_core] += 1
        if not context_key or not source_core or logical_attempt < 1:
            violations.append(
                {
                    "case_id": case_id,
                    "code": "missing_source_route_attribution",
                    "purpose": purpose,
                }
            )
        expected_tokens = None
        if profile == GADGET_AUTHORING_BASE_TOKEN_PROFILE:
            expected_tokens = policy.gadget_authoring_base_max_tokens
            if transport_attempt != 1:
                violations.append(
                    {
                        "case_id": case_id,
                        "code": "base_profile_transport_ordinal_invalid",
                        "logical_attempt": logical_attempt,
                    }
                )
        elif profile == GADGET_AUTHORING_ESCALATED_TOKEN_PROFILE:
            expected_tokens = policy.gadget_authoring_escalated_max_tokens
            if transport_attempt != 2:
                violations.append(
                    {
                        "case_id": case_id,
                        "code": "escalated_profile_transport_ordinal_invalid",
                        "logical_attempt": logical_attempt,
                    }
                )
        else:
            violations.append(
                {
                    "case_id": case_id,
                    "code": "unknown_gadget_token_profile",
                    "token_profile": profile,
                }
            )
        if call.get("requested_max_tokens") != expected_tokens:
            violations.append(
                {
                    "case_id": case_id,
                    "code": "token_profile_budget_mismatch",
                    "token_profile": profile,
                }
            )
        if call.get("reasoning_effort") != policy.gadget_authoring_reasoning_effort:
            violations.append(
                {
                    "case_id": case_id,
                    "code": "token_profile_reasoning_effort_mismatch",
                    "token_profile": profile,
                }
            )
        receipt_key = (
            case_id,
            context_key,
            logical_attempt,
            transport_attempt,
            purpose,
        )
        if receipt_key not in structured_by_call:
            violations.append(
                {
                    "case_id": case_id,
                    "code": "model_call_missing_structured_receipt",
                    "logical_attempt": logical_attempt,
                    "transport_attempt": transport_attempt,
                }
            )
        grouped.setdefault(
            (case_id, context_key, logical_attempt, purpose), []
        ).append(call)

    successful_escalations = 0
    terminal_nonconvergence = 0
    semantic_repair_nonconvergence = 0
    for (case_id, _, logical_attempt, purpose), calls in grouped.items():
        ordered = sorted(calls, key=lambda call: int(call.get("transport_attempt") or 0))
        if len(ordered) > 2:
            violations.append(
                {
                    "case_id": case_id,
                    "code": "too_many_token_escalations",
                    "logical_attempt": logical_attempt,
                }
            )
        high_calls = [
            call
            for call in ordered
            if call.get("token_profile")
            == GADGET_AUTHORING_ESCALATED_TOKEN_PROFILE
        ]
        if not high_calls:
            continue
        high = high_calls[0]
        base = next(
            (
                call
                for call in ordered
                if call.get("token_profile")
                == GADGET_AUTHORING_BASE_TOKEN_PROFILE
            ),
            None,
        )
        if base is None:
            violations.append(
                {
                    "case_id": case_id,
                    "code": "escalation_missing_base_call",
                    "logical_attempt": logical_attempt,
                }
            )
            continue
        same_prompt = (
            bool(base.get("request_payload_sha256"))
            and base.get("request_payload_sha256")
            == high.get("request_payload_sha256")
        )
        linked = high.get("escalation_of_response_sha256") == _sha256_with_prefix(
            base.get("response_sha256")
        )
        if base.get("finish_reason") != "length" or not same_prompt or not linked:
            violations.append(
                {
                    "case_id": case_id,
                    "code": "escalation_not_bound_to_same_prompt_length_result",
                    "logical_attempt": logical_attempt,
                    "purpose": purpose,
                }
            )
        high_key = (
            case_id,
            str(high.get("authoring_context_key") or ""),
            logical_attempt,
            int(high.get("transport_attempt") or 0),
            purpose,
        )
        high_receipt = structured_by_call.get(high_key)
        if high.get("finish_reason") == "length":
            expected_statuses = {
                "transport-escalation-exhausted",
                "semantic-repair-escalation-exhausted",
            }
            if not isinstance(high_receipt, Mapping) or high_receipt.get(
                "status"
            ) not in expected_statuses:
                violations.append(
                    {
                        "case_id": case_id,
                        "code": "terminal_nonconvergence_receipt_missing",
                        "logical_attempt": logical_attempt,
                    }
                )
            else:
                terminal_nonconvergence += 1
                if high_receipt.get("status") == (
                    "semantic-repair-escalation-exhausted"
                ):
                    semantic_repair_nonconvergence += 1
        elif high_receipt is not None and bool(high.get("ok")):
            successful_escalations += 1

    violation_codes = {str(item.get("code") or "") for item in violations}
    profile_codes = {
        "base_profile_transport_ordinal_invalid",
        "escalated_profile_transport_ordinal_invalid",
        "unknown_gadget_token_profile",
        "token_profile_budget_mismatch",
        "token_profile_reasoning_effort_mismatch",
    }
    return {
        "profile_calls": dict(sorted(profile_counts.items())),
        "base_profile_call_count": profile_counts[
            GADGET_AUTHORING_BASE_TOKEN_PROFILE
        ],
        "escalated_profile_call_count": profile_counts[
            GADGET_AUTHORING_ESCALATED_TOKEN_PROFILE
        ],
        "length_exhaustion_call_count": sum(
            call.get("finish_reason") == "length" for _, call in gadget_calls
        ),
        "successful_escalation_count": successful_escalations,
        "terminal_nonconvergence_count": terminal_nonconvergence,
        "semantic_repair_nonconvergence_count": (
            semantic_repair_nonconvergence
        ),
        "source_core_call_counts": dict(sorted(source_counts.items())),
        "violations": violations,
        "token_profiles_match_policy": not bool(violation_codes & profile_codes),
        "escalations_follow_length_on_same_prompt": (
            "escalation_not_bound_to_same_prompt_length_result"
            not in violation_codes
            and "escalation_missing_base_call" not in violation_codes
            and "too_many_token_escalations" not in violation_codes
        ),
        "escalation_lineage_complete": (
            "model_call_missing_structured_receipt" not in violation_codes
        ),
        "nonconvergence_receipts_complete": (
            "terminal_nonconvergence_receipt_missing" not in violation_codes
        ),
        "source_route_attribution_complete": (
            "missing_source_route_attribution" not in violation_codes
        ),
    }


def _proof_step_row(step: Any) -> dict[str, Any]:
    return {
        "action_id": step.action_id,
        "provider": step.provider.value,
        "disposition": step.disposition.value,
        "goal_id": step.goal_id,
        "exact_type": step.exact_type,
        "declaration": step.declaration,
        "solver": step.solver,
        "status": step.status,
    }


def _baseline_attribution(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    case_rows: list[dict[str, Any]] = []
    contribution_counts: Counter[str] = Counter()
    finite_plugin_counts: Counter[str] = Counter()
    canonical_route_case_ids: list[str] = []
    exact_reuse_case_ids: list[str] = []
    nonreuse_without_model_call: list[str] = []
    for row in rows:
        final_receipts = tuple(
            receipt
            for receipt in row.get("contribution_receipts", ())
            if isinstance(receipt, Mapping) and receipt.get("final_artifact_used")
        )
        contribution_classes = tuple(
            dict.fromkeys(
                str(receipt.get("contribution_class"))
                for receipt in final_receipts
                if receipt.get("contribution_class")
            )
        )
        exact_reuse = row.get("solution_classification") == "VERIFIED_REUSE"
        if not contribution_classes and exact_reuse:
            contribution_classes = (ContributionClass.THEOREM_REUSE.value,)
        for contribution_class in contribution_classes:
            contribution_counts[contribution_class] += 1

        executed_plugins = tuple(
            sorted(
                {
                    str(step.get("solver"))
                    for step in row.get("proof_tree", ())
                    if isinstance(step, Mapping)
                    and step.get("provider") == "plugin"
                    and step.get("solver")
                }
            )
        )
        for plugin_name in executed_plugins:
            finite_plugin_counts[plugin_name] += 1
        route_declarations = tuple(
            dict.fromkeys(
                (
                    *(
                        str(item)
                        for item in row.get("selected_proof_route", ())
                        if item
                    ),
                    *(
                        str(step.get("declaration"))
                        for step in row.get("proof_tree", ())
                        if isinstance(step, Mapping) and step.get("declaration")
                    ),
                )
            )
        )
        used_canonical_route = any("Canonical" in item for item in route_declarations)
        if used_canonical_route:
            canonical_route_case_ids.append(str(row.get("case_id")))
        if exact_reuse:
            exact_reuse_case_ids.append(str(row.get("case_id")))
        called_real_model = any(
            bool(call.get("called"))
            for call in row.get("model_calls", ())
            if isinstance(call, Mapping)
        )
        if not exact_reuse and not called_real_model:
            nonreuse_without_model_call.append(str(row.get("case_id")))
        case_rows.append(
            {
                "case_id": row.get("case_id"),
                "proof_status": row.get("proof_status"),
                "solution_classification": row.get("solution_classification"),
                "final_contribution_classes": list(contribution_classes),
                "final_contribution_declarations": [
                    receipt.get("capability_declaration") for receipt in final_receipts
                ],
                "executed_finite_plugins": list(executed_plugins),
                "selected_route_declarations": list(route_declarations),
                "used_canonical_route": used_canonical_route,
                "used_exact_reuse": exact_reuse,
                "real_model_called": called_real_model,
            }
        )
    return {
        "case_count": len(case_rows),
        "contribution_class_case_counts": dict(sorted(contribution_counts.items())),
        "finite_plugin_case_counts": dict(sorted(finite_plugin_counts.items())),
        "exact_reuse_case_count": len(exact_reuse_case_ids),
        "exact_reuse_case_ids": sorted(exact_reuse_case_ids),
        "canonical_route_case_count": len(canonical_route_case_ids),
        "canonical_route_case_ids": sorted(canonical_route_case_ids),
        "nonreuse_without_real_model_call_count": len(nonreuse_without_model_call),
        "nonreuse_without_real_model_call_case_ids": sorted(
            nonreuse_without_model_call
        ),
        "cases": case_rows,
    }


def _policy_enforcement(
    rows: Sequence[Mapping[str, Any]], policy: CapabilityGatePolicy
) -> dict[str, Any]:
    required = set(policy.required_case_ids)
    disabled = set(policy.disabled_finite_synthesis_plugins)
    violations: list[dict[str, Any]] = []
    required_receipt_case_ids: list[str] = []
    for row in rows:
        case_id = str(row.get("case_id") or "")
        receipt = row.get("gate_policy_runtime")
        if case_id in required:
            if not isinstance(receipt, Mapping):
                violations.append(
                    {"case_id": case_id, "code": "missing_gate_policy_runtime_receipt"}
                )
            else:
                required_receipt_case_ids.append(case_id)
                if (receipt.get("policy") or {}).get("policy_sha256") != policy.policy_sha256:
                    violations.append(
                        {"case_id": case_id, "code": "gate_policy_hash_mismatch"}
                    )
                if receipt.get("case_id") != case_id:
                    violations.append(
                        {"case_id": case_id, "code": "gate_policy_case_binding_mismatch"}
                    )
                if receipt.get("case_role") != "required":
                    violations.append(
                        {"case_id": case_id, "code": "gate_policy_case_role_mismatch"}
                    )
                if not receipt.get("structured_gadget_authoring_enabled"):
                    violations.append(
                        {
                            "case_id": case_id,
                            "code": "structured_gadget_authoring_not_enabled",
                        }
                    )
                runtime_names = set(receipt.get("runtime_finite_synthesis_plugins", ()))
                disabled_names = set(
                    receipt.get("disabled_finite_synthesis_plugins", ())
                )
                if disabled.intersection(runtime_names):
                    violations.append(
                        {"case_id": case_id, "code": "disabled_plugin_visible_to_runtime"}
                    )
                if disabled_names != disabled:
                    violations.append(
                        {"case_id": case_id, "code": "disabled_plugin_set_mismatch"}
                    )
                for required_compiler in (
                    "boolean-csp-direct-tm-compiler",
                    "boolean-csp-semantic-compiler",
                ):
                    if required_compiler not in runtime_names:
                        violations.append(
                            {
                                "case_id": case_id,
                                "code": "required_compiler_missing",
                                "plugin": required_compiler,
                            }
                        )
        executed_plugins = {
            str(step.get("solver"))
            for step in row.get("proof_tree", ())
            if isinstance(step, Mapping)
            and step.get("provider") == "plugin"
            and step.get("solver")
        }
        for plugin_name in sorted(disabled.intersection(executed_plugins)):
            violations.append(
                {
                    "case_id": case_id,
                    "code": "disabled_plugin_executed",
                    "plugin": plugin_name,
                }
            )
    return {
        "policy_name": policy.name,
        "policy_version": policy.policy_version,
        "policy_sha256": policy.policy_sha256,
        "required_case_count": len(policy.required_case_ids),
        "anchor_case_count": len(policy.anchor_case_ids),
        "required_case_runtime_receipt_count": len(required_receipt_case_ids),
        "required_case_runtime_receipt_case_ids": sorted(required_receipt_case_ids),
        "policy_violation_count": len(violations),
        "policy_violations": violations,
        "integrity_passed": not violations,
    }


def _run_case(
    *,
    root: Path,
    output_root: Path,
    case,
    deepseek: DeepSeekConfig,
    profile: str,
    lean_timeout_seconds: int,
    forbidden_declarations: Sequence[str],
    excluded_candidate_declarations: Sequence[str],
    gate_policy: CapabilityGatePolicy | None,
) -> dict[str, Any]:
    label = _case_label(case.module)
    case_output = output_root / "cases" / label
    started = time.monotonic()
    result = GenerativeReductionOrchestrator(
        GenerativeReductionConfig(
            root=root,
            input_module=case.module,
            problem_declaration=case.problem,
            output_dir=case_output,
            strategy=Strategy.BALANCED,
            profile=profile,
            model_policy=ModelPolicy.REQUIRED,
            plugins=("boolean_csp",),
            forbidden_declarations=tuple(forbidden_declarations),
            excluded_candidate_declarations=tuple(
                excluded_candidate_declarations
            ),
            budget=recursive_benchmark_budget(),
            lean_timeout_seconds=lean_timeout_seconds,
            deepseek=deepseek,
            runtime_prebuilt=True,
            gate_policy=gate_policy,
            capability_gate_case_id=(case.case_id if gate_policy is not None else None),
        )
    ).run()
    elapsed = time.monotonic() - started
    report_path = case_output / "report.json"
    search_path = case_output / "planner" / "search-outcome.json"
    gate_policy_path = case_output / "planner" / "gate-policy.json"
    search = _read_json(search_path) if search_path.is_file() else {}
    gate_policy_runtime = (
        _read_json(gate_policy_path) if gate_policy_path.is_file() else None
    )
    best_state = search.get("best_state") if isinstance(search.get("best_state"), dict) else {}
    generated_capabilities = (
        best_state.get("generated_capabilities", ())
        if isinstance(best_state, dict)
        else ()
    )
    capability_metrics = result.capability_metrics()
    return {
        "case_id": case.case_id,
        "case": label,
        "split": case.split,
        "module": case.module,
        "problem": case.problem,
        "proof_status": result.proof_status.value,
        "solution_classification": result.solution_classification.value,
        "qualification_status": result.qualification_status.value,
        "selected_proof_route": list(result.selected_proof_route),
        "proof_tree": [_proof_step_row(step) for step in result.proof_tree],
        "gate_policy_runtime": gate_policy_runtime,
        "report": str(report_path),
        "artifact": result.artifact_file,
        "wall_seconds": elapsed,
        "expanded_state_count": result.expanded_state_count,
        "requeued_failure_state_count": result.requeued_failure_state_count,
        "pruned_cycle_count": result.pruned_cycle_count,
        "max_observed_search_depth": result.max_observed_search_depth,
        "application_frame_count": result.application_frame_count,
        "verified_application_frame_count": result.verified_application_frame_count,
        "data_binding_count": result.data_binding_count,
        "dependent_goal_activation_count": result.dependent_goal_activation_count,
        "recursive_substep_plan_count": result.recursive_substep_plan_count,
        "generated_capability_count": result.generated_capability_count,
        "strategy_valid_proposal_count": result.strategy_valid_proposal_count,
        "strategy_applied_decision_count": result.strategy_applied_decision_count,
        "strategy_fallback_count": result.strategy_fallback_count,
        "strategy_rejected_count": result.strategy_rejected_count,
        "unused_strategy_call_count": result.unused_strategy_call_count,
        "strategy_effect_receipts": [
            receipt.__dict__ for receipt in result.strategy_effect_receipts
        ],
        "finite_candidate_count": result.finite_candidate_count,
        "finite_counterexample_count": result.finite_counterexample_count,
        "finite_certificate_count": result.finite_certificate_count,
        "capability_compiler_candidate_count": (
            result.capability_compiler_candidate_count
        ),
        "capability_compiler_certificate_count": (
            result.capability_compiler_certificate_count
        ),
        "generated_lean_check_count": result.generated_lean_check_count,
        "generated_lean_success_count": result.generated_lean_success_count,
        "capability_registration_count": result.capability_registration_count,
        "synthesis_design_count": result.synthesis_design_count,
        "context_expansion_count": result.context_expansion_count,
        "repair_authoring_count": result.repair_authoring_count,
        "duplicate_candidate_rejection_count": (
            result.duplicate_candidate_rejection_count
        ),
        "repeated_diagnostic_count": result.repeated_diagnostic_count,
        "context_insufficient_count": result.context_insufficient_count,
        "unresolved_probe_handle_count": result.unresolved_probe_handle_count,
        "rejected_nonexecutable_design_count": (
            result.rejected_nonexecutable_design_count
        ),
        "synthesis_designs": list(result.synthesis_designs),
        "context_capsule_ids": [
            item.get("capsule_id")
            for item in result.context_capsules
            if isinstance(item, dict)
        ],
        "context_capsules": list(result.context_capsules),
        "generation_context_ready_count": sum(
            bool(item.get("generation_context_ready"))
            for item in result.context_capsules
            if isinstance(item, dict)
        ),
        "repair_lineage": list(result.repair_lineage),
        "capability_plans": [asdict(item) for item in result.capability_plans],
        "theorem_application_plans": [
            asdict(item) for item in result.theorem_application_plans
        ],
        "generator_briefs": [asdict(item) for item in result.generator_briefs],
        "generator_results": [asdict(item) for item in result.generator_results],
        "contribution_receipts": [
            asdict(item) for item in result.contribution_receipts
        ],
        "planner_effect_receipts": [
            asdict(item) for item in result.planner_effect_receipts
        ],
        "typed_capability_plans": list(result.typed_capability_plans),
        "capability_budget_reservations": list(
            ((search.get("budget") or {}).get("capacity_reservations") or ())
            if isinstance(search.get("budget"), dict)
            else ()
        ),
        "frontier_exhaustion_receipt": result.frontier_exhaustion_receipt,
        "blocker": result.blocker,
        "model_calls": [
            {
                "purpose": call.purpose,
                "provider": call.provider,
                "model": call.model,
                "called": call.called,
                "ok": call.ok,
                "status_code": call.status_code,
                "attempts": call.attempts,
                "duration_seconds": call.duration_seconds,
                "usage": call.usage,
                "response_sha256": call.response_sha256,
                "error": call.error,
                "proposal_id": call.proposal_id,
                "finish_reason": call.finish_reason,
                "token_profile": call.token_profile,
                "requested_max_tokens": call.requested_max_tokens,
                "reasoning_effort": call.reasoning_effort,
                "request_payload_sha256": call.request_payload_sha256,
                "authoring_context_key": call.authoring_context_key,
                "source_core": call.source_core,
                "logical_attempt": call.logical_attempt,
                "transport_attempt": call.transport_attempt,
                "escalation_of_response_sha256": (
                    call.escalation_of_response_sha256
                ),
            }
            for call in result.model_calls
        ],
        "generated_capabilities": [
            {
                "declaration": item.get("declaration"),
                "exact_type": item.get("exact_type"),
                "source_hash": item.get("source_hash"),
                "action_id": item.get("action_id"),
                "provenance": item.get("provenance"),
            }
            for item in generated_capabilities
            if isinstance(item, dict)
        ],
        "generated_declaration_used_by_final_artifact": bool(
            result.generation_evidence.generated_edge_used_by_final_artifact
            or (
                result.proof_status.value == "VERIFIED"
                and result.generated_capability_count > 0
            )
        ),
        "verification": result.verification.__dict__,
        "final_route_audit_receipt": result.final_route_audit_receipt,
        "capability_metrics": capability_metrics,
        **capability_metrics,
        "model_call_accounting_complete": True,
    }


def _exception_case_row(*, output_root: Path, case, error: Exception) -> dict[str, Any]:
    label = _case_label(case.module)
    return {
        "case_id": case.case_id,
        "case": label,
        "split": case.split,
        "module": case.module,
        "problem": case.problem,
        "proof_status": "INTERNAL_ERROR",
        "solution_classification": "NONE",
        "qualification_status": "NOT_RUN",
        "selected_proof_route": [],
        "proof_tree": [],
        "gate_policy_runtime": None,
        "report": str(output_root / "cases" / label / "report.json"),
        "artifact": None,
        "wall_seconds": 0.0,
        "expanded_state_count": 0,
        "requeued_failure_state_count": 0,
        "pruned_cycle_count": 0,
        "max_observed_search_depth": 0,
        "application_frame_count": 0,
        "verified_application_frame_count": 0,
        "data_binding_count": 0,
        "dependent_goal_activation_count": 0,
        "recursive_substep_plan_count": 0,
        "generated_capability_count": 0,
        "strategy_valid_proposal_count": 0,
        "strategy_applied_decision_count": 0,
        "strategy_fallback_count": 0,
        "strategy_rejected_count": 0,
        "unused_strategy_call_count": 0,
        "strategy_effect_receipts": [],
        "finite_candidate_count": 0,
        "finite_counterexample_count": 0,
        "finite_certificate_count": 0,
        "capability_compiler_candidate_count": 0,
        "capability_compiler_certificate_count": 0,
        "generated_lean_check_count": 0,
        "generated_lean_success_count": 0,
        "capability_registration_count": 0,
        "synthesis_design_count": 0,
        "context_expansion_count": 0,
        "repair_authoring_count": 0,
        "duplicate_candidate_rejection_count": 0,
        "repeated_diagnostic_count": 0,
        "context_insufficient_count": 0,
        "unresolved_probe_handle_count": 0,
        "rejected_nonexecutable_design_count": 0,
        "synthesis_designs": [],
        "context_capsule_ids": [],
        "context_capsules": [],
        "generation_context_ready_count": 0,
        "repair_lineage": [],
        "capability_plans": [],
        "theorem_application_plans": [],
        "generator_briefs": [],
        "generator_results": [],
        "contribution_receipts": [],
        "planner_effect_receipts": [],
        "typed_capability_plans": [],
        "capability_budget_reservations": [],
        "frontier_exhaustion_receipt": None,
        "blocker": f"{type(error).__name__}: {error}",
        "model_calls": [],
        "generated_capabilities": [],
        "generated_declaration_used_by_final_artifact": False,
        "verification": {
            "exact_type_verified": False,
            "kernel_verified": False,
            "independent_replay_passed": False,
            "axiom_audit_passed": False,
            "placeholder_scan_passed": False,
            "endpoint_equality_audit_passed": False,
            "same_index_audit_passed": False,
        },
        "final_route_audit_receipt": None,
        "capability_metrics": {},
        "model_call_accounting_complete": False,
        "exception_type": type(error).__name__,
    }


def _usage_totals(rows: Sequence[Mapping[str, Any]]) -> dict[str, int]:
    totals: Counter[str] = Counter()
    for row in rows:
        for call in row.get("model_calls", ()):
            usage = call.get("usage") if isinstance(call, dict) else None
            if not isinstance(usage, dict):
                continue
            for key, value in usage.items():
                if isinstance(value, int):
                    totals[str(key)] += value
    return dict(totals)


def run_recursive_boolean_csp_regression(
    *,
    root: Path,
    output_root: Path,
    env_file: Path,
    jobs: int = 4,
    profile: str = "benchmark",
    lean_timeout_seconds: int = 600,
    model: str | None = None,
    model_timeout_seconds: int | None = None,
    model_max_tokens: int | None = None,
    model_max_retries: int | None = None,
    reasoning_effort: str | None = None,
    report_path: Path | None = None,
    extra_forbidden_declarations: Sequence[str] = (),
    excluded_candidate_declarations: Sequence[str] = (),
    gate_policy: CapabilityGatePolicy | None = None,
    suite: BooleanCSPSuite | None = None,
    freeze_manifest: Path | None = None,
    freeze_case_set: str | None = None,
    evaluation_protocol: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    if jobs < 1 or jobs > 4:
        raise ValueError("jobs must be in 1..4")
    root = root.resolve()
    output_root = output_root.resolve()
    if suite is None:
        suite_path = (
            root
            / "Benchmark"
            / "Hardness"
            / "Suites"
            / "boolean_csp_np_hard_public_v1.json"
        )
        suite = load_suite(suite_path)
    if gate_policy is not None:
        gate_policy.validate_case_ids(tuple(case.case_id for case in suite.cases))
    configured = DeepSeekConfig.from_environment(env_file=env_file)
    deepseek = replace(
        configured,
        **{
            key: value
            for key, value in {
                "model": model,
                "timeout_seconds": model_timeout_seconds,
                "max_tokens": model_max_tokens,
                "max_retries": model_max_retries,
                "reasoning_effort": reasoning_effort,
            }.items()
            if value is not None
        },
    )
    protocol = dict(evaluation_protocol or {})
    requires_configuration_freeze = bool(
        protocol.get("requires_configuration_freeze")
    )
    if (freeze_manifest is None) != (freeze_case_set is None):
        raise ValueError(
            "freeze_manifest and freeze_case_set must be provided together"
        )
    if requires_configuration_freeze and freeze_manifest is None:
        raise ValueError("evaluation protocol requires a configuration freeze")
    freeze_receipt: dict[str, Any] | None = None
    if freeze_manifest is not None:
        if gate_policy is None:
            raise ValueError("configuration freeze requires a capability gate policy")
        suite_path = suite.path.resolve()
        try:
            suite_path_label = str(suite_path.relative_to(root))
        except ValueError:
            suite_path_label = str(suite_path)
        freeze_receipt = validate_gadget_authoring_freeze(
            root=root,
            manifest_path=freeze_manifest,
            policy=gate_policy,
            case_set_name=str(freeze_case_set),
            selected_case_ids=tuple(case.case_id for case in suite.cases),
            suite_identity={
                "suite_id": suite.suite_id,
                "suite_sha256": suite.sha256,
                "path": suite_path_label,
            },
            model_config=deepseek.to_public_dict(),
            runtime_config={
                "profile": profile,
                "jobs": jobs,
                "lean_timeout_seconds": lean_timeout_seconds,
            },
            budget=asdict(recursive_benchmark_budget()),
        )
    if not deepseek.api_key:
        raise ValueError("real API regression requires DEEPSEEK_API_KEY")
    forbidden_declarations = tuple(
        dict.fromkeys(
            (
                *FORBIDDEN_DICHOTOMY_DECLARATIONS,
                *extra_forbidden_declarations,
                *(
                    gate_policy.forbidden_declarations
                    if gate_policy is not None
                    else ()
                ),
            )
        )
    )
    excluded_candidate_declarations = tuple(
        dict.fromkeys(
            (
                *excluded_candidate_declarations,
                *(
                    gate_policy.excluded_candidate_declarations
                    if gate_policy is not None
                    else ()
                ),
            )
        )
    )
    plugin_inventory = _boolean_csp_plugin_inventory()
    if gate_policy is None:
        route_policy = {
            "name": BASELINE_POLICY_NAME,
            "policy_version": BASELINE_POLICY_VERSION,
            "forbidden_declarations": list(forbidden_declarations),
            "excluded_candidate_declarations": list(excluded_candidate_declarations),
            "runtime_finite_synthesis_plugins": plugin_inventory[
                "runtime_finite_synthesis_plugins"
            ],
            "model_policy": ModelPolicy.REQUIRED.value,
            "profile": profile,
        }
        route_policy["policy_sha256"] = stable_sha256(route_policy)
    else:
        installed = tuple(plugin_inventory["installed_finite_synthesis_plugins"])
        disabled = set(gate_policy.disabled_finite_synthesis_plugins)
        plugin_inventory["disabled_finite_synthesis_plugins"] = [
            name for name in installed if name in disabled
        ]
        plugin_inventory["runtime_finite_synthesis_plugins"] = [
            name for name in installed if name not in disabled
        ]
        route_policy = gate_policy.to_report_dict()
    output_root.mkdir(parents=True, exist_ok=True)
    started_at = datetime.now(timezone.utc)
    started = time.monotonic()
    rows: list[dict[str, Any]] = []
    with ThreadPoolExecutor(max_workers=jobs) as executor:
        futures = {
            executor.submit(
                _run_case,
                root=root,
                output_root=output_root,
                case=case,
                deepseek=deepseek,
                profile=profile,
                lean_timeout_seconds=lean_timeout_seconds,
                forbidden_declarations=forbidden_declarations,
                excluded_candidate_declarations=excluded_candidate_declarations,
                gate_policy=gate_policy,
            ): case
            for case in suite.cases
        }
        for future in as_completed(futures):
            case = futures[future]
            try:
                row = future.result()
            except Exception as error:
                row = _exception_case_row(
                    output_root=output_root,
                    case=case,
                    error=error,
                )
            rows.append(row)
            rows.sort(key=lambda item: item["case_id"])
            _write_json(
                output_root / "progress.json",
                {
                    "schema_version": "general_recursive_boolean_csp_progress_v1",
                    "completed_case_count": len(rows),
                    "selected_case_count": len(suite.cases),
                    "cases": rows,
                },
            )
    completed_at = datetime.now(timezone.utc)
    model_calls = [call for row in rows for call in row["model_calls"]]
    structured_gadget_receipts = [
        item
        for row in rows
        for item in row.get("typed_capability_plans", ())
        if _is_structured_gadget_receipt(item)
    ]
    semantic_checker_receipts = [
        checker
        for item in structured_gadget_receipts
        if isinstance((checker := item.get("semantic_checker")), Mapping)
    ]
    adaptive_token_audit = _adaptive_gadget_token_audit(rows, gate_policy)
    model_gadget_contributions = _model_gadget_contributions(rows)
    status_counts = Counter(row["proof_status"] for row in rows)
    http_counts = Counter(
        str(call["status_code"])
        for call in model_calls
        if call.get("status_code") is not None
    )
    report = {
        "schema_version": "general_agent_boolean_csp_recursive_real_api_report_v1",
        "date": completed_at.date().isoformat(),
        "suite": {
            "suite_id": suite.suite_id,
            "suite_sha256": suite.sha256,
            "selected_case_count": len(suite.cases),
            "completed_case_count": len(rows),
            "selected_case_ids": [case.case_id for case in suite.cases],
            "completed_case_ids": [row["case_id"] for row in rows],
            "oracle_accessed_during_run": False,
        },
        "evaluation_protocol": protocol,
        "configuration_freeze": freeze_receipt,
        "source_revision": _workspace_revision(root),
        "route_policy": {
            **route_policy,
            "forbidden_declarations": list(forbidden_declarations),
            "excluded_candidate_declarations": list(
                excluded_candidate_declarations
            ),
            "final_transitive_dependency_audit_enabled": True,
            **plugin_inventory,
        },
        "real_api": {
            **deepseek.to_public_dict(),
            "provider": "deepseek",
            "total_calls": sum(bool(call["called"]) for call in model_calls),
            "http_200_calls": sum(call.get("status_code") == 200 for call in model_calls),
            "accepted_response_count": sum(bool(call["ok"]) for call in model_calls),
            "http_status_counts": dict(http_counts),
            "call_purposes": dict(Counter(call["purpose"] for call in model_calls)),
            "usage": _usage_totals(rows),
            "call_accounting_complete": all(
                row.get("model_call_accounting_complete", True) for row in rows
            ),
            "adaptive_gadget_token_protocol": adaptive_token_audit,
            "external_payload_classes": [
                "exact Lean child goals",
                "candidate theorem names",
                "Lean diagnostics",
                "local construction contracts",
                *(
                    [
                        "complete public source and target truth tables",
                        "single structured BooleanCSPGadgetPlanV1 payloads",
                        (
                            "schema failure, finite semantic counterexample, or Lean "
                            "repair feedback for the same case"
                        ),
                    ]
                    if gate_policy is not None
                    and gate_policy.name == "gadget-authoring"
                    else []
                ),
            ],
        },
        "results": {
            "status_counts": dict(status_counts),
            "verified_case_count": status_counts.get("VERIFIED", 0),
            "generated_capability_case_count": sum(
                row["generated_capability_count"] > 0 for row in rows
            ),
            "generated_capability_used_case_count": sum(
                row["generated_declaration_used_by_final_artifact"] for row in rows
            ),
            "total_expanded_states": sum(row["expanded_state_count"] for row in rows),
            "total_requeues": sum(row["requeued_failure_state_count"] for row in rows),
            "total_application_frames": sum(row["application_frame_count"] for row in rows),
            "total_verified_frames": sum(
                row["verified_application_frame_count"] for row in rows
            ),
            "total_data_bindings": sum(row["data_binding_count"] for row in rows),
            "total_dependent_goal_activations": sum(
                row["dependent_goal_activation_count"] for row in rows
            ),
            "total_strategy_valid_proposals": sum(
                row["strategy_valid_proposal_count"] for row in rows
            ),
            "total_strategy_applied_decisions": sum(
                row["strategy_applied_decision_count"] for row in rows
            ),
            "total_strategy_fallbacks": sum(
                row["strategy_fallback_count"] for row in rows
            ),
            "total_strategy_rejections": sum(
                row["strategy_rejected_count"] for row in rows
            ),
            "total_unused_strategy_calls": sum(
                row["unused_strategy_call_count"] for row in rows
            ),
            "total_finite_candidates": sum(
                row["finite_candidate_count"] for row in rows
            ),
            "total_finite_counterexamples": sum(
                row["finite_counterexample_count"] for row in rows
            ),
            "total_finite_certificates": sum(
                row["finite_certificate_count"] for row in rows
            ),
            "total_capability_compiler_candidates": sum(
                row["capability_compiler_candidate_count"] for row in rows
            ),
            "total_capability_compiler_certificates": sum(
                row["capability_compiler_certificate_count"] for row in rows
            ),
            "total_generated_lean_checks": sum(
                row["generated_lean_check_count"] for row in rows
            ),
            "total_generated_lean_successes": sum(
                row["generated_lean_success_count"] for row in rows
            ),
            "total_capability_registrations": sum(
                row["capability_registration_count"] for row in rows
            ),
            "total_synthesis_designs": sum(
                row["synthesis_design_count"] for row in rows
            ),
            "total_context_expansions": sum(
                row["context_expansion_count"] for row in rows
            ),
            "total_repair_authoring_calls": sum(
                row["repair_authoring_count"] for row in rows
            ),
            "total_gadget_authoring_initial_calls": sum(
                call.get("purpose") == "gadget-authoring-initial"
                and bool(call.get("called"))
                for call in model_calls
            ),
            "total_gadget_authoring_repair_calls": sum(
                call.get("purpose") == "gadget-authoring-repair"
                and bool(call.get("called"))
                for call in model_calls
            ),
            "total_gadget_authoring_base_profile_calls": (
                adaptive_token_audit["base_profile_call_count"]
            ),
            "total_gadget_authoring_escalated_profile_calls": (
                adaptive_token_audit["escalated_profile_call_count"]
            ),
            "total_gadget_authoring_length_exhaustions": (
                adaptive_token_audit["length_exhaustion_call_count"]
            ),
            "total_gadget_authoring_successful_escalations": (
                adaptive_token_audit["successful_escalation_count"]
            ),
            "total_gadget_authoring_terminal_nonconvergence": (
                adaptive_token_audit["terminal_nonconvergence_count"]
            ),
            "total_gadget_semantic_repair_nonconvergence": (
                adaptive_token_audit[
                    "semantic_repair_nonconvergence_count"
                ]
            ),
            "total_gadget_semantic_checks": len(semantic_checker_receipts),
            "total_gadget_semantic_check_successes": sum(
                bool(item.get("success")) for item in semantic_checker_receipts
            ),
            "total_gadget_semantic_counterexamples": sum(
                not bool(item.get("success")) for item in semantic_checker_receipts
            ),
            "total_gadget_semantic_source_rows_checked": sum(
                int(item.get("source_rows_checked", 0))
                for item in semantic_checker_receipts
            ),
            "total_gadget_semantic_auxiliary_assignments_checked": sum(
                int(item.get("auxiliary_assignments_checked", 0))
                for item in semantic_checker_receipts
            ),
            "total_authorship_evidence_count": sum(
                isinstance(receipt.get("authorship_evidence"), Mapping)
                for _, receipt in model_gadget_contributions
            ),
            "total_duplicate_candidate_rejections": sum(
                row["duplicate_candidate_rejection_count"] for row in rows
            ),
            "total_repeated_diagnostics": sum(
                row["repeated_diagnostic_count"] for row in rows
            ),
            "total_context_insufficient_events": sum(
                row["context_insufficient_count"] for row in rows
            ),
            "total_unresolved_probe_handles": sum(
                row["unresolved_probe_handle_count"] for row in rows
            ),
            "total_rejected_nonexecutable_designs": sum(
                row["rejected_nonexecutable_design_count"] for row in rows
            ),
            "maximum_recursive_depth": max(
                (row["max_observed_search_depth"] for row in rows), default=0
            ),
        },
        "timing": {
            "jobs": jobs,
            "started_at_utc": started_at.isoformat(),
            "completed_at_utc": completed_at.isoformat(),
            "wall_seconds": time.monotonic() - started,
        },
        "cases": rows,
    }
    report["baseline_attribution"] = _baseline_attribution(rows)
    if gate_policy is not None:
        report["policy_enforcement"] = _policy_enforcement(rows, gate_policy)
    blocked_without_receipt = [
        row["case_id"]
        for row in rows
        if row["proof_status"] == "BLOCKED"
        and not row.get("frontier_exhaustion_receipt")
    ]
    failed_verified_audits = [
        row["case_id"]
        for row in rows
        if row["proof_status"] == "VERIFIED"
        and not bool((row.get("final_route_audit_receipt") or {}).get("passed"))
    ]
    forbidden_dependency_cases = [
        row["case_id"]
        for row in rows
        if (
            isinstance(row.get("final_route_audit_receipt"), Mapping)
            and (
                row["final_route_audit_receipt"].get("passed") is False
                or row["final_route_audit_receipt"].get(
                    "forbidden_dependencies_passed"
                )
                is False
            )
        )
        or "forbidden dependency"
        in json.dumps(row.get("blocker"), ensure_ascii=False).lower()
        or "route audit rejected"
        in json.dumps(row.get("blocker"), ensure_ascii=False).lower()
    ]
    authorship_bindings = tuple(
        (
            row,
            receipt,
            receipt.get("authorship_evidence"),
            _verified_structured_receipt(row, receipt),
        )
        for row, receipt in model_gadget_contributions
    )
    report["validation"] = {
        "all_cases_completed": len(rows) == len(suite.cases),
        "configuration_freeze_integrity_passed": (
            not requires_configuration_freeze
            or bool((freeze_receipt or {}).get("integrity_passed"))
        ),
        "blocked_frontier_receipts_complete": not blocked_without_receipt,
        "blocked_cases_missing_frontier_receipt": blocked_without_receipt,
        "verified_route_audits_passed": not failed_verified_audits,
        "verified_cases_with_failed_route_audit": failed_verified_audits,
        "all_called_requests_http_200": (
            report["real_api"]["total_calls"]
            == report["real_api"]["http_200_calls"]
        ),
        "forbidden_direct_or_transitive_dependency_count": len(
            forbidden_dependency_cases
        ),
        "forbidden_dependency_case_ids": forbidden_dependency_cases,
        "unused_strategy_call_count_is_zero": not any(
            row["unused_strategy_call_count"] for row in rows
        ),
        "strategy_accounting_complete": all(
            sum(
                bool(call.get("called")) and call.get("purpose") == "strategy-proposal"
                for call in row.get("model_calls", ())
            )
            == row["strategy_applied_decision_count"]
            + row["strategy_fallback_count"]
            + row["strategy_rejected_count"]
            for row in rows
        ),
        "repair_prompts_have_matching_base_hash": (
            _repair_prompts_have_matching_base_hash(rows)
        ),
        "structured_gadget_token_profiles_match_policy": (
            adaptive_token_audit["token_profiles_match_policy"]
        ),
        "structured_gadget_escalations_follow_length_on_same_prompt": (
            adaptive_token_audit[
                "escalations_follow_length_on_same_prompt"
            ]
        ),
        "structured_gadget_escalation_lineage_complete": (
            adaptive_token_audit["escalation_lineage_complete"]
        ),
        "structured_gadget_nonconvergence_receipts_complete": (
            adaptive_token_audit["nonconvergence_receipts_complete"]
        ),
        "structured_gadget_source_route_attribution_complete": (
            adaptive_token_audit["source_route_attribution_complete"]
        ),
        "context_capsule_receipts_present_for_authoring": all(
            not any(
                bool(call.get("called"))
                and call.get("purpose", "").startswith("lean-authoring-")
                for call in row.get("model_calls", ())
            )
            or bool(row.get("context_capsule_ids"))
            for row in rows
        ),
        "structured_gadget_briefs_are_answer_free": all(
            all(
                bool(item.get("answer_free"))
                and bool((item.get("gadget_brief") or {}).get("answer_free"))
                for item in row.get("typed_capability_plans", ())
                if _is_structured_gadget_receipt(item)
            )
            for row in rows
        ),
        "structured_gadget_renderer_added_zero_semantic_atoms": all(
            all(
                not isinstance(item.get("renderer"), Mapping)
                or item["renderer"].get("renderer_added_semantic_atom_count") == 0
                for item in row.get("typed_capability_plans", ())
                if _is_structured_gadget_receipt(item)
            )
            for row in rows
        ),
        "structured_gadget_receipts_are_case_bound": all(
            all(
                item.get("case_id") == row.get("case_id")
                and item.get("policy_sha256") == gate_policy.policy_sha256
                for item in row.get("typed_capability_plans", ())
                if _is_structured_gadget_receipt(item)
            )
            for row in rows
        )
        if gate_policy is not None
        else True,
        "structured_gadget_source_cores_match_policy": (
            gate_policy is None
            or all(
                (
                    (item.get("gadget_brief") or {})
                    .get("authoring_context", {})
                    .get("source", {})
                    .get("handle")
                )
                in set(gate_policy.allowed_gadget_source_declarations)
                for item in structured_gadget_receipts
            )
        ),
        "structured_gadget_unique_plans_have_semantic_checker_receipts": all(
            item.get("status") == "duplicate-semantic-payload-rejected"
            or not isinstance(item.get("gadget_plan"), Mapping)
            or isinstance(item.get("semantic_checker"), Mapping)
            for item in structured_gadget_receipts
        ),
        "structured_gadget_lean_attempts_passed_semantic_checker": all(
            item.get("status") not in {"lean-failed", "lean-verified"}
            or (
                isinstance(item.get("semantic_checker"), Mapping)
                and bool(item["semantic_checker"].get("success"))
            )
            for item in structured_gadget_receipts
        ),
        "structured_gadget_semantic_failures_skipped_lean": all(
            item.get("status") != "semantic-failed"
            or (
                isinstance(item.get("semantic_checker"), Mapping)
                and not bool(item["semantic_checker"].get("success"))
                and item.get("generated_file") is None
                and item.get("source_sha256") is None
                and item.get("renderer") is None
            )
            for item in structured_gadget_receipts
        ),
        "structured_gadget_checker_versions_match_policy": (
            gate_policy is None
            or all(
                item.get("checker_name") == gate_policy.checker_name
                and item.get("checker_version") == gate_policy.checker_version
                for item in semantic_checker_receipts
            )
        ),
        "structured_gadget_checker_inputs_are_hash_bound": all(
            isinstance(item.get("checker_input_sha256"), str)
            and str(item.get("checker_input_sha256")).startswith("sha256:")
            and isinstance(item.get("semantic_payload_sha256"), str)
            and str(item.get("semantic_payload_sha256")).startswith("sha256:")
            for item in semantic_checker_receipts
        ),
        "structured_gadget_counterexamples_are_direction_complete": all(
            bool(item.get("success"))
            or (
                isinstance(item.get("counterexample"), Mapping)
                and item["counterexample"].get("direction")
                in {"false-positive", "false-negative"}
                and bool(item["counterexample"].get("expected_relation_holds"))
                != bool(item["counterexample"].get("formula_has_extension"))
            )
            for item in semantic_checker_receipts
        ),
        "structured_gadget_authorship_evidence_present": all(
            isinstance(evidence, Mapping)
            for _, _, evidence, _ in authorship_bindings
        ),
        "structured_gadget_authorship_evidence_is_model_origin": (
            gate_policy is None
            or all(
                isinstance(evidence, Mapping)
                and evidence.get("origin") == "model"
                and evidence.get("semantic_payload_schema")
                == gate_policy.semantic_payload_schema
                and evidence.get("renderer_name") == gate_policy.renderer_name
                and evidence.get("renderer_version") == gate_policy.renderer_version
                and evidence.get("renderer_added_semantic_atom_count") == 0
                for _, _, evidence, _ in authorship_bindings
            )
        ),
        "structured_gadget_authorship_hashes_are_case_bound": all(
            isinstance(evidence, Mapping)
            and isinstance(verified, Mapping)
            and str(evidence.get("model_response_sha256") or "").startswith(
                "sha256:"
            )
            and evidence.get("model_response_sha256")
            in {
                _sha256_with_prefix(call.get("response_sha256"))
                for call in row.get("model_calls", ())
                if isinstance(call, Mapping)
                and str(call.get("purpose") or "").startswith(
                    "gadget-authoring"
                )
            }
            and verified.get("case_id") == row.get("case_id")
            and verified.get("source_sha256")
            in set(receipt.get("model_generated_source_hashes", ()))
            for row, receipt, evidence, verified in authorship_bindings
        ),
        "structured_gadget_authorship_semantic_hashes_match": all(
            isinstance(evidence, Mapping)
            and isinstance(verified, Mapping)
            and isinstance(verified.get("model_attempt"), Mapping)
            and isinstance(verified.get("semantic_checker"), Mapping)
            and isinstance(verified.get("renderer"), Mapping)
            and isinstance(verified.get("gadget_plan"), Mapping)
            and evidence.get("semantic_payload_sha256")
            == verified["model_attempt"].get("semantic_payload_sha256")
            == verified["semantic_checker"].get("semantic_payload_sha256")
            == verified["renderer"].get("semantic_payload_sha256_before")
            == verified["renderer"].get("semantic_payload_sha256_after")
            == verified["gadget_plan"].get("semantic_payload_sha256")
            for _, _, evidence, verified in authorship_bindings
        ),
        "structured_gadget_authorship_repair_hashes_match": all(
            isinstance(evidence, Mapping)
            and isinstance(verified, Mapping)
            and tuple(evidence.get("repair_payload_hashes", ()))
            == _structured_repair_payload_hashes(row, verified)
            for row, _, evidence, verified in authorship_bindings
        ),
        "structured_gadget_final_use_is_kernel_dependency_audited": all(
            isinstance(verified, Mapping)
            and bool(receipt.get("final_artifact_used"))
            and bool(receipt.get("independent_lean_passed"))
            and bool((row.get("verification") or {}).get("kernel_verified"))
            and bool(
                (row.get("verification") or {}).get(
                    "independent_replay_passed"
                )
            )
            and bool(
                (row.get("final_route_audit_receipt") or {}).get(
                    "required_dependency_audit_emitted"
                )
            )
            and bool(
                (row.get("final_route_audit_receipt") or {}).get(
                    "required_dependencies_passed"
                )
            )
            and receipt.get("capability_declaration")
            in set(
                (row.get("final_route_audit_receipt") or {}).get(
                    "required_dependencies", ()
                )
            )
            for row, receipt, _, verified in authorship_bindings
        ),
        "unresolved_probe_handle_count_is_zero": not any(
            row["unresolved_probe_handle_count"] for row in rows
        ),
        "empty_context_generator_call_count_is_zero": not any(
            row["context_insufficient_count"]
            and any(
                call.get("purpose", "").startswith("lean-authoring-")
                for call in row.get("model_calls", ())
            )
            for row in rows
        ),
        "planner_effect_receipts_cover_generator_briefs": all(
            {
                item.get("brief_id")
                for item in row.get("generator_briefs", ())
                if isinstance(item, dict)
            }
            <= {
                item.get("generated_brief_id")
                for item in row.get("planner_effect_receipts", ())
                if isinstance(item, dict)
            }
            for row in rows
        ),
        "planner_accounting_consistent": all(
            bool(row.get("planner_accounting_consistent", True)) for row in rows
        ),
        "generated_capability_accounting_consistent": all(
            bool(row.get("generated_capability_accounting_consistent", True))
            for row in rows
        ),
        "all_nonreuse_cases_called_real_api": not report["baseline_attribution"][
            "nonreuse_without_real_model_call_case_ids"
        ],
    }
    metric_names = tuple(
        key
        for key, value in (rows[0].get("capability_metrics", {}) if rows else {}).items()
        if isinstance(value, int) and not isinstance(value, bool)
    )
    report["capability_metrics"] = {
        key: sum(int(row.get(key, 0)) for row in rows) for key in metric_names
    }
    _write_json(output_root / "summary.json", report)
    if report_path is not None:
        _write_json(report_path.resolve(), report)
    return report


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Run the recursive general agent on all public Boolean-CSP cases"
    )
    root = Path(__file__).resolve().parents[2]
    parser.add_argument("--root", type=Path, default=root)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--env-file", type=Path, default=root / ".env")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--profile", choices=("research", "strict-release", "benchmark"), default="benchmark")
    parser.add_argument("--lean-timeout", type=int, default=600)
    parser.add_argument("--model", default=None)
    parser.add_argument("--model-timeout", type=int, default=900)
    parser.add_argument("--model-max-tokens", type=int, default=64000)
    parser.add_argument("--model-max-retries", type=int, default=0)
    parser.add_argument("--reasoning-effort", default="low")
    parser.add_argument(
        "--gate-policy",
        choices=("none", "gadget-authoring"),
        default="none",
        help="apply a hash-bound capability gate policy to all suite cases",
    )
    parser.add_argument(
        "--forbid-declaration",
        action="append",
        default=[],
        help=(
            "additional fully-qualified Lean declaration forbidden from the selected "
            "or elaborated transitive proof route; may be repeated"
        ),
    )
    parser.add_argument(
        "--exclude-candidate-declaration",
        action="append",
        default=[],
        help=(
            "additional declaration excluded only from proof-search choices; "
            "may be repeated"
        ),
    )
    parser.add_argument(
        "--report-path",
        type=Path,
        default=root / "Reports" / DEFAULT_REPORT_NAME,
    )
    return parser


def main() -> int:
    arguments = build_parser().parse_args()
    gate_policy = (
        gadget_authoring_policy()
        if arguments.gate_policy == "gadget-authoring"
        else None
    )
    report = run_recursive_boolean_csp_regression(
        root=arguments.root,
        output_root=arguments.output_root,
        env_file=arguments.env_file,
        jobs=arguments.jobs,
        profile=arguments.profile,
        lean_timeout_seconds=arguments.lean_timeout,
        model=arguments.model,
        model_timeout_seconds=arguments.model_timeout,
        model_max_tokens=arguments.model_max_tokens,
        model_max_retries=arguments.model_max_retries,
        reasoning_effort=arguments.reasoning_effort,
        report_path=arguments.report_path,
        extra_forbidden_declarations=tuple(arguments.forbid_declaration),
        excluded_candidate_declarations=tuple(
            arguments.exclude_candidate_declaration
        ),
        gate_policy=gate_policy,
    )
    print(json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True))
    return 0 if (
        report["suite"]["completed_case_count"]
        == report["suite"]["selected_case_count"]
    ) else 2


if __name__ == "__main__":
    raise SystemExit(main())


__all__ = [
    "BASELINE_POLICY_NAME",
    "BASELINE_POLICY_VERSION",
    "FORBIDDEN_DICHOTOMY_DECLARATIONS",
    "DEFAULT_REPORT_NAME",
    "recursive_benchmark_budget",
    "run_recursive_boolean_csp_regression",
]
