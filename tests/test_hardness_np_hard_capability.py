from __future__ import annotations

from copy import deepcopy
from dataclasses import replace
import hashlib
import json
from pathlib import Path
import threading
import time

import pytest

import agent.hardness.np_hard_capability as capability_runner
from agent.hardness.model_client import DeepSeekConfig
from agent.hardness.models import CommandResult, sha256_id
from agent.hardness.np_hard_capability import (
    CAPABILITY_BENCHMARK_ID,
    CAPABILITY_BENCHMARK_ID_V2,
    CAPABILITY_MANIFEST_SCHEMA_V2,
    CAPABILITY_ORACLE_SCHEMA_V2,
    CAPABILITY_RUN_SCHEMA_V2,
    CAPABILITY_SCORE_SCHEMA_V2,
    CAPABILITY_SUITE_SCHEMA_V2,
    CAPABILITY_WORKSPACE_PREFLIGHT_BUILD_TIMEOUT_SECONDS,
    FORMAL_PUBLIC_PROFILE,
    CapabilityBudgetProfile,
    CapabilityCase,
    CapabilityOracleCase,
    NPHardCapabilityError,
    _boundary,
    _case_evidence_payload,
    _identity_conflict_code,
    _parse_contract_counts,
    _public_status,
    _required_verified_authoring_motif,
    _run_case_tasks,
    _strict_case_success,
    _validate_formal_profile,
    _validate_required_authoring_motif_evidence,
    _validate_run_case,
    _validate_run_id,
    build_capability_isolated_workspace,
    load_capability_bundle,
    load_capability_manifest,
    load_capability_oracle,
    load_capability_suite,
    run_capability_r0_mutation_audit,
)
from agent.hardness.np_hard_authoring import build_np_hard_authoring_tasks_v2
from agent.hardness.np_hard_scope_policy import load_np_hard_scope_policy
from scripts.build_np_hard_capability_v2 import REQUIRED_AUTHORING_MOTIFS


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "Archive/CAPABILITY_MANIFEST.json"
V2_MANIFEST = ROOT / "Benchmark/Hardness/CAPABILITY_MANIFEST_V2.json"
GENERALIZATION_SUITE = (
    ROOT / "Gate/Suites/np_hard_generalization.json"
)


def _json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _write(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def _formal_config(**changes: object) -> DeepSeekConfig:
    config = DeepSeekConfig(
        api_key="test-only-key",
        base_url="https://api.deepseek.com",
        model="deepseek-v4-flash",
        timeout_seconds=300,
        temperature=0.0,
        max_tokens=16_000,
        max_retries=0,
        reasoning_effort="low",
    )
    return replace(config, **changes)


@pytest.fixture
def motif_task():
    return build_np_hard_authoring_tasks_v2(
        root=ROOT, suite_path=GENERALIZATION_SUITE
    )[0]


def _task_motif(task) -> dict[str, object]:
    return {
        "task_class": task.task_class,
        "nodes": [
            {
                "node_id": node.node_id,
                "capability": node.capability,
                "depends_on": list(node.depends_on),
            }
            for node in task.gap_nodes
        ],
        "terminal_node_id": task.terminal_node_id,
        "final_program_node_id": task.final_program_node_id,
    }


def _motif_raw(task, case_output: Path) -> dict[str, object]:
    accepted = [node.node_id for node in task.gap_nodes]
    deletion_nodes: list[dict[str, object]] = []
    for node in task.gap_nodes:
        audit_file = case_output / f"without-{node.node_id}.lean"
        audit_file.parent.mkdir(parents=True, exist_ok=True)
        audit_file.write_text(f"-- delete {node.declaration}\n", encoding="utf-8")
        deletion_nodes.append(
            {
                "node_id": node.node_id,
                "declaration": node.declaration,
                "body_sha256": "sha256:" + "1" * 64,
                "audit_file": str(audit_file),
                "audit_file_sha256": "sha256:"
                + hashlib.sha256(audit_file.read_bytes()).hexdigest(),
                "command": {
                    "timed_out": False,
                    "exit_code": 1,
                    "stdout": "",
                    "stderr": (
                        "error(lean.unknownIdentifier): Unknown identifier "
                        f"`{node.declaration}`"
                    ),
                },
                "diagnostic_matched": True,
                "passed": True,
            }
        )
    runtime = {
        "status": "VERIFIED",
        "task_request_id": task.request_id,
        "accepted_nodes": accepted,
        "fresh_core_rediscoveries": len(accepted),
        "result": {"accepted_nodes": accepted},
        "deletion_audits": deletion_nodes,
    }
    return {
        "status": "VERIFIED",
        "capability_dag": task.to_dict(),
        "authoring_runtime": runtime,
        "fresh_core": {"count": len(accepted), "passed": True},
        "deletion_audit": {
            "passed": True,
            "node_count": len(deletion_nodes),
            "nodes": deletion_nodes,
        },
    }


def test_frozen_public_bundle_is_answer_free_and_identity_disjoint() -> None:
    bundle = load_capability_bundle(MANIFEST, root=ROOT, verify_oracle=False)
    assert len(bundle.cases) == 34
    assert {split: len(suite.cases) for split, suite in bundle.suites.items()} == {
        "dev": 8,
        "validation": 8,
        "heldout": 16,
        "frontier": 2,
    }
    identities = [bundle.case_identity[case.case_id]["identity_id"] for case in bundle.cases]
    assert len(identities) == len(set(identities))
    assert "other" not in {case.family for case in bundle.suites["dev"].cases}
    assert "other" not in {case.family for case in bundle.suites["validation"].cases}
    assert {case.family for case in bundle.suites["heldout"].cases} == {
        "graph",
        "numeric",
        "set-system",
        "sat-csp",
        "other",
    }


def test_public_suite_rejects_oracle_field(tmp_path: Path) -> None:
    source = ROOT / "Gate/Suites/np_hard_capability_dev_v1.json"
    suite = _json(source)
    suite["cases"][0]["expected_status"] = "VERIFIED"  # type: ignore[index]
    path = tmp_path / "leaked-suite.json"
    _write(path, suite)
    with pytest.raises(NPHardCapabilityError) as caught:
        load_capability_suite(path, expected_split="dev")
    assert caught.value.code == "oracle_field_in_public_suite"


def test_public_suite_rejects_fixture_module(tmp_path: Path) -> None:
    source = ROOT / "Gate/Suites/np_hard_capability_dev_v1.json"
    suite = _json(source)
    suite["cases"][0]["module"] = "Benchmark.Hardness.Inputs.ThreeSAT"  # type: ignore[index]
    path = tmp_path / "fixture-suite.json"
    _write(path, suite)
    with pytest.raises(NPHardCapabilityError) as caught:
        load_capability_suite(path, expected_split="dev")
    assert caught.value.code == "fixture_in_capability_suite"


def test_runner_side_bundle_never_opens_oracle(monkeypatch: pytest.MonkeyPatch) -> None:
    manifest = _json(MANIFEST)
    oracle = (ROOT / str(manifest["oracle"]["file"])).resolve()  # type: ignore[index]
    original = Path.read_text

    def guarded(path: Path, *args: object, **kwargs: object) -> str:
        if path.resolve() == oracle:
            raise AssertionError("runner opened scorer-only oracle")
        return original(path, *args, **kwargs)

    monkeypatch.setattr(Path, "read_text", guarded)
    bundle = load_capability_bundle(MANIFEST, root=ROOT, verify_oracle=False)
    assert len(bundle.cases) == 34


def test_scorer_verifies_oracle_and_frozen_tier_counts() -> None:
    bundle = load_capability_bundle(MANIFEST, root=ROOT, verify_oracle=True)
    oracle = load_capability_oracle(bundle.manifest.oracle.path, bundle=bundle)
    counts: dict[str, int] = {}
    for case in oracle.values():
        counts[case.tier] = counts.get(case.tier, 0) + 1
    assert counts == {
        "C0-existing": 12,
        "C0-authoring": 12,
        "C0-safety": 8,
        "F0-frontier": 2,
    }


def test_v2_oracle_freezes_exactly_eight_required_authoring_motifs() -> None:
    v1_bundle = load_capability_bundle(MANIFEST, root=ROOT, verify_oracle=True)
    v1_oracle = load_capability_oracle(
        v1_bundle.manifest.oracle.path, bundle=v1_bundle
    )
    assert all(case.required_authoring_motif is None for case in v1_oracle.values())

    v2_bundle = load_capability_bundle(V2_MANIFEST, root=ROOT, verify_oracle=True)
    v2_oracle = load_capability_oracle(
        v2_bundle.manifest.oracle.path, bundle=v2_bundle
    )
    observed = {
        case_id: dict(case.required_authoring_motif)
        for case_id, case in v2_oracle.items()
        if case.required_authoring_motif is not None
    }
    assert observed == REQUIRED_AUTHORING_MOTIFS
    assert {
        case_id: (
            motif["task_class"],
            len(motif["nodes"]),
            motif["terminal_node_id"],
            motif["final_program_node_id"],
        )
        for case_id, motif in observed.items()
    } == {
        "cdev-au-01-tagged-three-sat-adapter": (
            "typed_capability_dag",
            4,
            "semantic-iff",
            "representation-adapter",
        ),
        "cval-au-03-seeing-set": (
            "typed_tmkarp_program_indexed_composition_dag",
            10,
            "composed-semantic-iff",
            "composed-program",
        ),
        "chld-au-01-feedback-node-set": (
            "typed_tmkarp_admission_dag",
            3,
            "tmkarp-semantic-iff",
            "tmkarp-program",
        ),
        "chld-au-06-hitting-set": (
            "typed_tmkarp_dependent_composition_dag",
            5,
            "composed-semantic-iff",
            "composed-program",
        ),
        "chld-au-07-set-covering": (
            "typed_tmkarp_admission_dag",
            3,
            "tmkarp-semantic-iff",
            "tmkarp-program",
        ),
        "chld-au-08-set-packing": (
            "typed_tmkarp_admission_dag",
            3,
            "tmkarp-semantic-iff",
            "tmkarp-program",
        ),
        "chld-au-09-feedback-arc-set": (
            "typed_tmkarp_dependent_composition_dag",
            5,
            "composed-semantic-iff",
            "composed-program",
        ),
        "chld-au-10-three-dimensional-matching": (
            "typed_tmkarp_admission_dag",
            3,
            "tmkarp-semantic-iff",
            "tmkarp-program",
        ),
    }


def test_exact_required_authoring_motif_evidence_is_accepted(
    tmp_path: Path, motif_task
) -> None:
    case_output = tmp_path / "case"
    raw = _motif_raw(motif_task, case_output)
    _validate_required_authoring_motif_evidence(
        raw=raw,
        required_authoring_motif=_task_motif(motif_task),
        case_output=case_output,
        require_files=True,
    )


@pytest.mark.parametrize(
    ("mutation", "expected_code"),
    [
        ("motif", "candidate_dependency_stale"),
        ("accepted", "candidate_dependency_stale"),
        ("fresh", "fresh_core_resolve_failed"),
        ("deletion-node", "deletion_audit_failed"),
        ("deletion-diagnostic", "deletion_audit_failed"),
    ],
)
def test_required_authoring_motif_mutations_fail_closed(
    tmp_path: Path, motif_task, mutation: str, expected_code: str
) -> None:
    case_output = tmp_path / "case"
    raw = _motif_raw(motif_task, case_output)
    required = _task_motif(motif_task)
    if mutation == "motif":
        required["nodes"][0]["capability"] = "substituted_capability"  # type: ignore[index]
    elif mutation == "accepted":
        raw["authoring_runtime"]["accepted_nodes"] = []  # type: ignore[index]
    elif mutation == "fresh":
        raw["fresh_core"]["count"] = 0  # type: ignore[index]
        raw["authoring_runtime"]["fresh_core_rediscoveries"] = 0  # type: ignore[index]
    elif mutation == "deletion-node":
        raw["deletion_audit"]["nodes"][0]["node_id"] = "substituted"  # type: ignore[index]
    else:
        audit = raw["deletion_audit"]["nodes"][0]  # type: ignore[index]
        audit["command"]["stderr"] = (  # type: ignore[index]
            "error(lean.unknownIdentifier): Unknown identifier "
            f"`{str(audit['declaration']).rsplit('.', 1)[-1]}`; "
            f"while checking `{audit['declaration']}`"
        )

    with pytest.raises(NPHardCapabilityError) as caught:
        _validate_required_authoring_motif_evidence(
            raw=raw,
            required_authoring_motif=required,
            case_output=case_output,
            require_files=True,
        )
    assert caught.value.code == expected_code


def test_v2_verified_authoring_without_a_frozen_motif_fails_closed() -> None:
    oracle = _oracle("C0-authoring")
    with pytest.raises(NPHardCapabilityError) as caught:
        _required_verified_authoring_motif(
            oracle_schema_version=CAPABILITY_ORACLE_SCHEMA_V2,
            oracle_case=oracle,
            raw_result={"status": "VERIFIED"},
        )
    assert caught.value.code == "candidate_dependency_stale"

    assert (
        _required_verified_authoring_motif(
            oracle_schema_version="hardness_np_hard_capability_oracle_v1",
            oracle_case=oracle,
            raw_result={"status": "VERIFIED"},
        )
        is None
    )


def _v2_contract_counts() -> dict[str, object]:
    return {
        "case_count": 34,
        "unique_identity_count": 34,
        "split_counts": {
            "dev": 8,
            "validation": 8,
            "heldout": 16,
            "frontier": 2,
        },
        "expected_case_buckets": [
            {
                "split": "dev",
                "tier": "C0-existing",
                "outcome_class": "existing_route",
                "scored": True,
                "count": 4,
            },
            {
                "split": "dev",
                "tier": "C0-authoring",
                "outcome_class": "first_authoring",
                "scored": True,
                "count": 2,
            },
            {
                "split": "dev",
                "tier": "C0-safety",
                "outcome_class": "safety",
                "scored": True,
                "count": 2,
            },
            {
                "split": "validation",
                "tier": "C0-existing",
                "outcome_class": "existing_route",
                "scored": True,
                "count": 5,
            },
            {
                "split": "validation",
                "tier": "C0-authoring",
                "outcome_class": "first_authoring",
                "scored": True,
                "count": 1,
            },
            {
                "split": "validation",
                "tier": "C0-safety",
                "outcome_class": "safety",
                "scored": True,
                "count": 2,
            },
            {
                "split": "heldout",
                "tier": "C0-existing",
                "outcome_class": "existing_route",
                "scored": True,
                "count": 4,
            },
            {
                "split": "heldout",
                "tier": "C0-authoring",
                "outcome_class": "first_authoring",
                "scored": True,
                "count": 8,
            },
            {
                "split": "heldout",
                "tier": "C0-safety",
                "outcome_class": "safety",
                "scored": True,
                "count": 4,
            },
            {
                "split": "frontier",
                "tier": "F0-frontier",
                "outcome_class": "frontier",
                "scored": False,
                "count": 2,
            },
        ],
        "blocker_bucket_counts": {"encoding_complexity_boundary": 2},
    }


def test_v2_contract_freezes_the_migrated_32_plus_2_denominator() -> None:
    contract = _parse_contract_counts(_v2_contract_counts())
    tier_counts: dict[str, int] = {}
    scored_counts = {True: 0, False: 0}
    for (_split, tier, _outcome, scored), count in contract.expected_case_buckets.items():
        tier_counts[tier] = tier_counts.get(tier, 0) + count
        scored_counts[scored] += count
    assert contract.case_count == contract.unique_identity_count == 34
    assert tier_counts == {
        "C0-existing": 13,
        "C0-authoring": 11,
        "C0-safety": 8,
        "F0-frontier": 2,
    }
    assert scored_counts == {True: 32, False: 2}
    assert contract.blocker_bucket_counts == {"encoding_complexity_boundary": 2}


def test_v2_contract_rejects_unscored_blocker_count_drift() -> None:
    contract = _v2_contract_counts()
    contract["blocker_bucket_counts"] = {"encoding_complexity_boundary": 1}
    with pytest.raises(NPHardCapabilityError) as caught:
        _parse_contract_counts(contract)
    assert caught.value.code == "invalid_capability_schema"


def test_v2_schema_names_are_content_addressing_distinct_from_v1() -> None:
    assert CAPABILITY_BENCHMARK_ID_V2 == "np-hard-capability-v2"
    assert CAPABILITY_MANIFEST_SCHEMA_V2.endswith("_v2")
    assert CAPABILITY_SUITE_SCHEMA_V2.endswith("_v2")
    assert CAPABILITY_ORACLE_SCHEMA_V2.endswith("_v2")
    assert CAPABILITY_RUN_SCHEMA_V2.endswith("_v2")
    assert CAPABILITY_SCORE_SCHEMA_V2.endswith("_v2")


def test_alias_and_cross_split_identity_conflicts_fail_closed() -> None:
    identity = "sha256:" + "1" * 64
    assert _identity_conflict_code(
        [(identity, "dev", "canonical"), (identity, "dev", "alias")]
    ) == "duplicate_canonical_identity"
    assert _identity_conflict_code(
        [(identity, "dev", "canonical"), (identity, "heldout", "alias")]
    ) == "capability_split_overlap"


def test_formal_profile_is_fail_closed_without_freezing_api_key() -> None:
    _validate_formal_profile(
        deepseek=_formal_config(), required_profile=FORMAL_PUBLIC_PROFILE
    )
    with pytest.raises(NPHardCapabilityError) as missing_key:
        _validate_formal_profile(
            deepseek=replace(_formal_config(), api_key=None),
            required_profile=FORMAL_PUBLIC_PROFILE,
        )
    assert missing_key.value.code == "model_provider_unavailable"
    with pytest.raises(NPHardCapabilityError) as wrong_model:
        _validate_formal_profile(
            deepseek=_formal_config(model="deepseek-chat"),
            required_profile=FORMAL_PUBLIC_PROFILE,
        )
    assert wrong_model.value.code == "qualification_model_profile_mismatch"


def test_manifest_rejects_public_api_key_flag(tmp_path: Path) -> None:
    manifest = _json(MANIFEST)
    manifest["required_model_profile"]["api_key_configured"] = True  # type: ignore[index]
    path = tmp_path / "manifest.json"
    _write(path, manifest)
    with pytest.raises(NPHardCapabilityError) as caught:
        load_capability_manifest(path, root=ROOT)
    assert caught.value.code == "invalid_capability_schema"


def test_manifest_content_addresses_the_scope_policy() -> None:
    manifest = load_capability_manifest(MANIFEST, root=ROOT)
    assert manifest.scope_policy.file == "agent/hardness/data/np_hard_scope_policy.json"
    assert manifest.scope_policy.path == (
        ROOT / "agent/hardness/data/np_hard_scope_policy.json"
    ).resolve()
    assert manifest.scope_policy.sha256.startswith("sha256:")


def test_scope_policy_registers_the_three_internal_catalog_helpers() -> None:
    policy = load_np_hard_scope_policy(root=ROOT)
    by_declaration = {
        entry.canonical_declaration: entry for entry in policy.entries
    }
    expected = {
        "ComplexityReduction.Domain.GraphIR.wellFormedProblem",
        "ComplexityReduction.Domain.ModifiedExactCoverInput.modifiedProblem",
        "ComplexityReduction.Domain.RoleGraphIR.roleAssignedGraphProblem",
    }
    assert expected <= set(by_declaration)
    assert {
        by_declaration[declaration].category for declaration in expected
    } == {"internal_catalog_helper"}


def test_case_parallelism_reports_peak_and_returns_to_zero() -> None:
    barrier = threading.Barrier(4)

    def task(index: int) -> dict[str, object]:
        barrier.wait(timeout=2)
        time.sleep(0.01)
        return {"index": index}

    results, parallel = _run_case_tasks(
        [(f"case-{index}", lambda index=index: task(index)) for index in range(4)],
        jobs=4,
    )
    assert len(results) == 4
    assert parallel["maximum_concurrent_case_tasks"] == 4
    assert parallel["final_active_case_tasks"] == 0
    assert parallel["observed_parallelism"] is True


def test_workspace_preflight_build_timeout_is_independent_of_case_budget(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    captured: dict[str, object] = {}

    def fake_run_command(
        command: list[str], *, cwd: Path, timeout_seconds: int
    ) -> CommandResult:
        captured.update(
            command=command,
            cwd=cwd,
            timeout_seconds=timeout_seconds,
        )
        return CommandResult(
            command=tuple(command),
            exit_code=124,
            stdout="",
            stderr="",
            duration_seconds=0.0,
            timed_out=True,
        )

    monkeypatch.setattr(capability_runner, "run_command", fake_run_command)
    monkeypatch.setattr(
        capability_runner,
        "build_capability_isolated_workspace",
        lambda **_kwargs: {"passed": True},
    )

    report = capability_runner.run_np_hard_capability_benchmark(
        root=ROOT,
        manifest_path=MANIFEST,
        output_root=tmp_path / "output",
        report_path=tmp_path / "report.json",
        deepseek=_formal_config(),
        selected_splits=("dev",),
        jobs=1,
    )

    bundle = load_capability_bundle(MANIFEST, root=ROOT, verify_oracle=False)
    case_timeout = max(
        case.budget_profile.lean_timeout_seconds
        for case in bundle.suites["dev"].cases
    )
    assert case_timeout == 600
    assert captured["timeout_seconds"] == (
        CAPABILITY_WORKSPACE_PREFLIGHT_BUILD_TIMEOUT_SECONDS
    )
    assert CAPABILITY_WORKSPACE_PREFLIGHT_BUILD_TIMEOUT_SECONDS == 1200
    assert captured["timeout_seconds"] != case_timeout
    assert report["run_valid"] is False
    assert report["preflight"]["timed_out"] is True


def test_isolated_workspace_excludes_plan_oracle_and_archive_copies(
    tmp_path: Path,
) -> None:
    source = tmp_path / "source"
    lean = source / "Lean"
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        path = lean / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("{}\n" if name.endswith(".json") else "test\n", encoding="utf-8")
    public = lean / "Reference/ComplexityReduction"
    (public / "Domain").mkdir(parents=True)
    (public / "Domain/Public.lean").write_text("def public := True\n", encoding="utf-8")
    (public / "Evaluation").mkdir()
    (public / "Evaluation/oracle.json").write_text("{}\n", encoding="utf-8")
    (public / "Evaluation-copy").mkdir()
    (public / "Evaluation-copy/oracle.json").write_text("{}\n", encoding="utf-8")
    (public / "problems").mkdir()
    (public / "problems/problems_clean.json").write_text("{}\n", encoding="utf-8")
    (public / "problems_archive").mkdir()
    (public / "problems_archive/solution.md").write_text("secret\n", encoding="utf-8")
    _write(
        source / "Gate/np_hard_input_registry.json",
        {"schema_version": "test"},
    )
    matrix = source / "Reports/matrix.json"
    _write(matrix, {"schema_version": "test"})
    scope_policy = source / "frozen-inputs/scope-policy.json"
    _write(scope_policy, {"schema_version": "manifest-selected-test-policy"})
    (source / "ACTIVE_AGENT_IMPROVEMENT_PLAN.md").write_text("secret", encoding="utf-8")
    (source / "problems.7z").write_bytes(b"secret")

    destination = tmp_path / "isolated"
    report = build_capability_isolated_workspace(
        root=source,
        destination=destination,
        target_matrix_path=matrix,
        scope_policy_path=scope_policy,
    )
    assert report["passed"] is True
    assert (destination / "Lean/Reference/ComplexityReduction/Domain/Public.lean").is_file()
    assert not (destination / "Lean/Reference/ComplexityReduction/Evaluation").exists()
    assert not (destination / "Lean/Reference/ComplexityReduction/Evaluation-copy").exists()
    assert not (destination / "Lean/Reference/ComplexityReduction/problems").exists()
    assert not (destination / "Lean/Reference/ComplexityReduction/problems_archive").exists()
    assert not (destination / "ACTIVE_AGENT_IMPROVEMENT_PLAN.md").exists()
    assert not (destination / "problems.7z").exists()
    assert _json(
        destination / "agent/hardness/data/np_hard_scope_policy.json"
    ) == {"schema_version": "manifest-selected-test-policy"}


@pytest.mark.parametrize(
    ("field", "forged_value"),
    [
        ("suite_id", "substituted-suite"),
        ("budget_profile", "frontier-default"),
        ("canonical_module", "ComplexityReduction.Substituted"),
        ("model_calls", 1),
        ("token_usage", {"prompt_tokens": 1}),
        ("first_attempt_verified", True),
        ("failure_code", "substituted_failure"),
        ("protocol_valid", True),
    ],
)
def test_scorer_recomputes_case_summary_fields_from_raw_result(
    tmp_path: Path, field: str, forged_value: object
) -> None:
    budget = CapabilityBudgetProfile(
        name="formal-default",
        attempt_budget=4,
        call_budget=None,
        lean_timeout_seconds=600,
    )
    case = CapabilityCase(
        case_id="summary-integrity",
        module="ComplexityReduction.Example",
        problem="ComplexityReduction.Example.problem",
        family="other",
        budget_profile=budget,
        split="dev",
        suite_id="np-hard-capability-dev-v1",
    )
    identity = {
        "identity_id": "sha256:" + "1" * 64,
        "canonical_declaration": case.problem,
        "canonical_module": case.module,
    }
    output_root = tmp_path / "output"
    case_output = output_root / "cases" / case.case_id
    case_output.mkdir(parents=True)
    raw = {
        "schema_version": "hardness_np_hard_capability_case_error_v1",
        "status": "FAILED",
        "failure_code": "capability_runner_exception",
        "explanation": "synthetic scorer-only validation row",
        "input_identity": None,
        "model_calls": 0,
        "model_call_ledger": [],
    }
    row: dict[str, object] = {
        "case_id": case.case_id,
        "suite_id": case.suite_id,
        "split": case.split,
        "module": case.module,
        "problem": case.problem,
        "family": case.family,
        "budget_profile": budget.to_public_value(),
        "canonical_identity_id": identity["identity_id"],
        "canonical_problem": identity["canonical_declaration"],
        "canonical_module": identity["canonical_module"],
        "output_dir": str(case_output),
        "wall_duration_seconds": 0.0,
        "internal_status": "FAILED",
        "public_status": _public_status(
            status="FAILED",
            failure_code="capability_runner_exception",
            model_calls=0,
        ),
        "failure_code": "capability_runner_exception",
        "model_calls": 0,
        "token_usage": {},
        "first_attempt_verified": False,
        "protocol_valid": False,
        "result_file": None,
        "result_file_sha256": None,
        "raw_result": raw,
    }
    row["evidence_sha256"] = sha256_id(_case_evidence_payload(row))
    _validate_run_case(
        row=row,
        case=case,
        identity=identity,
        output_root=output_root,
    )

    forged = deepcopy(row)
    forged[field] = forged_value
    forged["evidence_sha256"] = sha256_id(_case_evidence_payload(forged))
    with pytest.raises(NPHardCapabilityError) as caught:
        _validate_run_case(
            row=forged,
            case=case,
            identity=identity,
            output_root=output_root,
        )
    assert caught.value.code == "result_forgery"


def test_r0_mutation_audit_exercises_all_eight_fail_closed_contracts() -> None:
    bundle = load_capability_bundle(MANIFEST, root=ROOT, verify_oracle=False)
    audit = run_capability_r0_mutation_audit(bundle)
    assert audit["audit_count"] == 8
    assert audit["passed_count"] == 8
    assert audit["passed"] is True


def _oracle(tier: str, *, route_length: int | None = None) -> CapabilityOracleCase:
    outcomes = {
        "C0-existing": "existing_route",
        "C0-authoring": "first_authoring",
        "C0-safety": "safety",
        "F0-frontier": "frontier",
    }
    return CapabilityOracleCase(
        case_id="case",
        tier=tier,
        outcome_class=outcomes[tier],
        canonical_identity="identity",
        level="L2",
        scored=tier != "F0-frontier",
        requires_model=tier == "C0-authoring",
        expected_public_status=(
            "BLOCKED_NOT_TARGET" if tier == "C0-safety" else "VERIFIED"
        ),
        expected_failure_codes=("auxiliary_or_non_target",),
        route_length=route_length,
        metadata={},
    )


def _verified_row(*, calls: int, route_length: int) -> dict[str, object]:
    canonical = "ComplexityReduction.Example.problem"
    return {
        "public_status": "VERIFIED",
        "failure_code": None,
        "canonical_problem": canonical,
        "model_calls": calls,
        "protocol_valid": True,
        "raw_result": {
            "artifact": {"endpoint": canonical},
            "independent_replay": {"passed": True},
            "axiom_audit": {"passed": True},
            "deterministic_result": {
                "route": {"atoms": [f"edge-{index}" for index in range(route_length)]}
            },
        },
    }


def test_existing_authoring_and_safety_scoring_are_separate() -> None:
    existing = _verified_row(calls=0, route_length=2)
    assert _strict_case_success(existing, _oracle("C0-existing", route_length=2)) == (
        True,
        True,
    )
    assert _strict_case_success(existing, _oracle("C0-authoring")) == (False, False)
    authored = _verified_row(calls=1, route_length=0)
    assert _strict_case_success(authored, _oracle("C0-authoring")) == (True, True)
    safety = {
        "public_status": "BLOCKED_NOT_TARGET",
        "failure_code": "auxiliary_or_non_target",
        "model_calls": 0,
        "canonical_problem": "ComplexityReduction.Example.problem",
        "raw_result": {},
    }
    assert _strict_case_success(safety, _oracle("C0-safety")) == (True, True)


def test_v2_encoding_frontier_scores_the_precise_zero_model_blocker() -> None:
    oracle = CapabilityOracleCase(
        case_id="frontier-01-knapsack-unary-encoding",
        tier="F0-frontier",
        outcome_class="frontier",
        canonical_identity="sha256:" + "1" * 64,
        level="L6",
        scored=False,
        requires_model=False,
        expected_public_status="BLOCKED_MISSING_PREREQUISITE",
        expected_failure_codes=(
            "encoding_polynomial_reverse_bridge_unavailable",
        ),
        route_length=None,
        metadata={},
        blocker_bucket="encoding_complexity_boundary",
    )
    blocked = {
        "public_status": "BLOCKED_MISSING_PREREQUISITE",
        "failure_code": "encoding_polynomial_reverse_bridge_unavailable",
        "model_calls": 0,
        "protocol_valid": True,
        "canonical_problem": "ComplexityReduction.Presentation.Knapsack.structuredProblem",
        "raw_result": {},
    }
    assert _strict_case_success(blocked, oracle) == (True, True)
    assert _strict_case_success(
        {**blocked, "public_status": "VERIFIED", "failure_code": None}, oracle
    ) == (False, False)
    assert _strict_case_success({**blocked, "model_calls": 1}, oracle) == (
        False,
        False,
    )


def test_boundary_reports_stable_and_first_failure_layers() -> None:
    rows = [
        {
            "scored": True,
            "outcome_class": "existing_route",
            "level": "L1",
            "capability_success": True,
            "public_status": "VERIFIED",
            "failure_code": None,
        },
        {
            "scored": True,
            "outcome_class": "first_authoring",
            "level": "L4",
            "capability_success": False,
            "public_status": "FAILED_MODEL",
            "failure_code": "authoring_gap_budget_exhausted",
        },
    ]
    boundary = _boundary(rows)
    assert boundary["highest_stable_level"] == "L1"
    assert boundary["first_significant_failure_level"] == "L4"
    assert boundary["failure_layer_distribution"] == {"budget": 1}


def test_content_addressed_run_report_rejects_forgery() -> None:
    report = {
        "schema_version": "hardness_np_hard_capability_run_v1",
        "benchmark_id": CAPABILITY_BENCHMARK_ID,
        "run_valid": True,
    }
    report["run_id"] = sha256_id(report)
    _validate_run_id(report)
    forged = deepcopy(report)
    forged["run_valid"] = False
    with pytest.raises(NPHardCapabilityError) as caught:
        _validate_run_id(forged)
    assert caught.value.code == "result_forgery"
