from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path

import pytest

import scripts.build_np_hard_h_j_full_report as h_j_report
from agent.hardness.np_hard_authoring import build_np_hard_authoring_tasks_v2
from agent.hardness.np_hard_authoring import NPHardAuthoringContractError
from scripts.build_np_hard_h_j_full_report import (
    CAPABILITY_RUN_SCHEMA_BY_EPOCH,
    CAPABILITY_SCORE_SCHEMA_BY_EPOCH,
    CAPABILITY_SPLITS,
    H_J_4_V2_MANIFEST_SHA256,
    H_J_4_V2_MIGRATION_SHA256,
    H_J_4_V2_ORACLE_SHA256,
    MIGRATION_BOUNDARY_FAILURE,
    STAGE_CONTRACT_EPOCH,
    STAGE_CONTRACT_VERSION,
    STAGE_LABELS,
    V2_REFINEMENT_CASE_IDS,
    V2_REFINEMENT_REQUIRED_MOTIF_IDS,
    V2_REFINEMENT_REQUIRED_MOTIFS,
    HJReportError,
    StaticEvidencePaths,
    _assert_no_secret,
    _canonical_content_hash,
    _deletion_command_matches_declaration,
    _parse_labeled_paths,
    _scorecard_from_rows,
    _validate_authored_run_evidence,
    _validate_http_calls,
    _validate_v2_oracle_refinement,
    build_parser,
    migrate_h_i_baseline_to_v2,
    validate_optional_stage_regressions,
    validate_static_assets,
)


ROOT = Path(__file__).resolve().parents[1]
HARDNESS = ROOT / "Benchmark/Hardness"
GENERALIZATION_SUITE = ROOT / "Gate/Suites/np_hard_generalization.json"


def _static_paths() -> StaticEvidencePaths:
    return StaticEvidencePaths(
        h_i_report=ROOT / "Reports/MAIN_H_I_FULL_REPORT.json",
        plan=ROOT / "ACTIVE_AGENT_IMPROVEMENT_PLAN.md",
        v1_capability_manifest=ROOT / "Archive/CAPABILITY_MANIFEST.json",
        v1_capability_oracle=(
            ROOT / "Evaluation/np_hard_capability_oracle_v1.json"
        ),
        v1_target_matrix=ROOT / "Gate/NP_HARD_TARGET_MATRIX.json",
        v1_r1_suite=(
            ROOT / "Gate/Suites/np_hard_public_r1_coverage_v1.json"
        ),
        v2_capability_manifest=HARDNESS / "CAPABILITY_MANIFEST_V2.json",
        v2_capability_oracle=(
            ROOT / "Evaluation/np_hard_capability_oracle_v2.json"
        ),
        v2_target_matrix=ROOT / "Gate/NP_HARD_TARGET_MATRIX_V2.json",
        v2_r1_suite=(
            ROOT / "Gate/Suites/np_hard_public_r1_coverage_v2.json"
        ),
        v2_h_j_4_capability_manifest=(
            ROOT / "Archive/History/CAPABILITY_MANIFEST_V2_H_J_4.json"
        ),
        v2_h_j_4_capability_oracle=(
            ROOT / "Evaluation/History/np_hard_capability_oracle_v2_h_j_4.json"
        ),
        v2_h_j_4_migration_report=(
            ROOT / "Archive/History/H_I_TO_H_J_CAPABILITY_MIGRATION_REPORT_H_J_4.json"
        ),
    )


def test_static_h_j_contract_binds_the_frozen_h_i_denominator() -> None:
    evidence = validate_static_assets(_static_paths())

    contracts = evidence["public"]["capability_contracts"]
    subversions = evidence["public"]["v2_content_addressed_subversions"]
    assert contracts["v1"]["selected_splits"] == list(CAPABILITY_SPLITS)
    assert contracts["v2"]["selected_splits"] == list(CAPABILITY_SPLITS)
    assert subversions["v2a"]["selected_splits"] == list(CAPABILITY_SPLITS)
    assert subversions["v2b"]["selected_splits"] == list(CAPABILITY_SPLITS)
    assert (
        subversions["v2a"]["manifest"]["sha256"]
        == H_J_4_V2_MANIFEST_SHA256
    )
    assert subversions["v2a"]["oracle"]["sha256"] == H_J_4_V2_ORACLE_SHA256
    assert (
        evidence["public"]["h_j_4_v2a_migration_archive"]["sha256"]
        == H_J_4_V2_MIGRATION_SHA256
    )
    assert contracts["v1"]["case_count"] == contracts["v2"]["case_count"] == 34
    assert (
        contracts["v1"]["unique_identity_count"]
        == contracts["v2"]["unique_identity_count"]
        == 34
    )
    assert evidence["public"]["h_i_baseline"][
        "verified_authoring_identity_count"
    ] == 0
    assert evidence["public"]["h_i_baseline"][
        "family_macro_verified_at_budget"
    ] == 0.554286
    assert all(
        value == 0
        for value in evidence["public"]["h_i_baseline"]["safety"].values()
    )
    assert evidence["public"]["h_i_baseline"]["evidence_mode"] == (
        "original_content_addressed_h_i_v1_score_rows"
    )


def test_v1_v2_migration_is_content_addressed_and_conserves_44_identities() -> None:
    evidence = validate_static_assets(_static_paths())
    audit = evidence["migration"]

    assert audit["passed"] is True
    assert audit["stage_contract_epochs"] == STAGE_CONTRACT_EPOCH
    assert audit["stage_contract_versions"] == STAGE_CONTRACT_VERSION
    assert audit["identity_universe"]["count"] == 44
    assert audit["identity_universe"]["unchanged_count"] == 37
    assert audit["identity_universe"]["approved_transition_count"] == 7
    assert len(audit["identity_universe"]["crosswalk"]) == 44
    assert audit["capability_denominator"][
        "canonical_identity_crosswalk_count"
    ] == 34
    assert len(audit["capability_denominator"]["canonical_identity_crosswalk"]) == 34
    assert audit["r1_zero_weight_partition"]["v1_count"] == 10
    assert audit["r1_zero_weight_partition"]["v2_count"] == 10
    assert len(audit["accepted_unary_numeric_demotions"]) == 3
    assert all(
        row["reason"] == MIGRATION_BOUNDARY_FAILURE
        and row["accepted_without_failure"] is True
        for row in audit["accepted_unary_numeric_demotions"]
    )
    assert audit["audit_id"] == _canonical_content_hash(audit, field="audit_id")


def test_h_i_rows_are_reindexed_not_rewritten_for_v2_comparison() -> None:
    evidence = validate_static_assets(_static_paths())
    baseline = migrate_h_i_baseline_to_v2(evidence)

    assert baseline["native_contract_epoch"] == "v1"
    assert baseline["comparison_contract_epoch"] == "v2"
    assert baseline["verified_authoring_identity_count"] == 0
    assert baseline["safety_correct_count"] == baseline["safety_case_count"] == 8
    assert len(baseline["migration_sources"]) == 34
    assert sum(
        row["source"] == "v1_r1_zero_weight_existing_route_control"
        for row in baseline["migration_sources"]
    ) == 1


def test_all_five_h_j_stage_labels_are_mandatory() -> None:
    assert STAGE_LABELS == (
        "h-j.1-adapter",
        "h-j.2-tmkarp",
        "h-j.3-dependent",
        "h-j.4-direct-tm",
        "h-j.5-gadget",
    )
    with pytest.raises(HJReportError) as caught:
        _parse_labeled_paths(
            ["h-j.1-adapter=tmp/one.json"],
            expected=STAGE_LABELS,
            option="--stage-run",
        )
    assert caught.value.code == "h_j_partial_evidence"


def test_stage_contract_epochs_select_native_run_and_score_schemas() -> None:
    assert CAPABILITY_RUN_SCHEMA_BY_EPOCH == {
        "v1": "hardness_np_hard_capability_run_v1",
        "v2": "hardness_np_hard_capability_run_v2",
    }
    assert CAPABILITY_SCORE_SCHEMA_BY_EPOCH == {
        "v1": "hardness_np_hard_capability_score_v1",
        "v2": "hardness_np_hard_capability_score_v2",
    }
    assert STAGE_CONTRACT_VERSION == {
        "h-j.1-adapter": "v1",
        "h-j.2-tmkarp": "v1",
        "h-j.3-dependent": "v1",
        "h-j.4-direct-tm": "v2a",
        "h-j.5-gadget": "v2b",
    }


def test_h_j_cli_keeps_legacy_aliases_and_adds_explicit_v2a_paths() -> None:
    option_strings = {
        option
        for action in build_parser()._actions
        for option in action.option_strings
    }
    assert {
        "--capability-manifest",
        "--capability-oracle",
        "--target-matrix",
        "--h-j-4-v2-capability-manifest",
        "--h-j-4-v2-capability-oracle",
        "--h-j-4-v2-migration-report",
        "--v2a-capability-manifest",
        "--v2a-capability-oracle",
        "--v2a-migration-report",
    } <= option_strings


def test_h_j_static_contract_refines_only_the_two_maxcut_motifs() -> None:
    static = validate_static_assets(_static_paths())
    v1_contract = static["contracts"]["v1"]["contract"]
    v2a_contract = static["contracts"]["v2a"]["contract"]
    v2b_contract = static["contracts"]["v2b"]["contract"]
    assert all(
        row["required_authoring_motif"] is None
        for row in v1_contract.values()
    )
    observed = {
        case_id: (
            row["required_authoring_motif"]["task_class"],
            len(row["required_authoring_motif"]["nodes"]),
        )
        for case_id, row in v2a_contract.items()
        if row["required_authoring_motif"] is not None
    }
    assert observed == {
        "cdev-au-01-tagged-three-sat-adapter": ("typed_capability_dag", 4),
        "cval-au-03-seeing-set": (
            "typed_tmkarp_program_indexed_composition_dag",
            10,
        ),
        "chld-au-01-feedback-node-set": ("typed_tmkarp_admission_dag", 3),
        "chld-au-06-hitting-set": (
            "typed_tmkarp_dependent_composition_dag",
            5,
        ),
        "chld-au-07-set-covering": ("typed_tmkarp_admission_dag", 3),
        "chld-au-08-set-packing": ("typed_tmkarp_admission_dag", 3),
        "chld-au-09-feedback-arc-set": (
            "typed_tmkarp_dependent_composition_dag",
            5,
        ),
        "chld-au-10-three-dimensional-matching": (
            "typed_tmkarp_admission_dag",
            3,
        ),
    }
    assert {
        case_id
        for case_id in v2b_contract
        if v2a_contract[case_id]["required_authoring_motif"]
        != v2b_contract[case_id]["required_authoring_motif"]
    } == set(V2_REFINEMENT_CASE_IDS)
    assert all(
        v2a_contract[case_id]["required_authoring_motif"] is None
        and isinstance(v2b_contract[case_id]["required_authoring_motif"], dict)
        for case_id in V2_REFINEMENT_CASE_IDS
    )
    refinement = static["v2_refinement"]
    assert refinement["passed"] is True
    assert {
        row["case_id"] for row in refinement["hidden_oracle_refinements"]
    } == set(V2_REFINEMENT_CASE_IDS)


def _synthetic_v2b_oracle() -> tuple[dict[str, object], dict[str, object]]:
    path = (
        ROOT / "Evaluation/History/np_hard_capability_oracle_v2_h_j_4.json"
    )
    v2a = json.loads(path.read_text(encoding="utf-8"))
    v2b = copy.deepcopy(v2a)
    by_id = {row["case_id"]: row for row in v2b["cases"]}
    for case_id in V2_REFINEMENT_CASE_IDS:
        by_id[case_id]["required_authoring_motif"] = copy.deepcopy(
            V2_REFINEMENT_REQUIRED_MOTIFS[case_id]
        )
    return v2a, v2b


def test_v2_oracle_refinement_accepts_only_two_strict_hidden_motifs() -> None:
    v2a, v2b = _synthetic_v2b_oracle()
    changes = _validate_v2_oracle_refinement(v2a, v2b)
    assert {row["case_id"] for row in changes} == set(V2_REFINEMENT_CASE_IDS)
    assert V2_REFINEMENT_REQUIRED_MOTIF_IDS == {
        "chld-au-03-max-cut-structured": (
            "sha256:a8f9f22e12bbf688a4285a649e26b927cda69726dee970c359d22b3fc5ca327e"
        ),
        "chld-au-04-max-cut-binary": (
            "sha256:05c700d517e36b38bf9da8527de0472961ff2b0ce04a4391e902dbea850dff20"
        ),
    }


@pytest.mark.parametrize(
    "mutation",
    ["missing", "third-case", "public-field", "shape", "foreign-motif"],
)
def test_v2_oracle_refinement_mutations_fail_closed(mutation: str) -> None:
    v2a, v2b = _synthetic_v2b_oracle()
    by_id = {row["case_id"]: row for row in v2b["cases"]}
    if mutation == "missing":
        by_id[V2_REFINEMENT_CASE_IDS[0]].pop("required_authoring_motif")
    elif mutation == "third-case":
        third = next(
            row
            for row in v2b["cases"]
            if row["case_id"] not in V2_REFINEMENT_CASE_IDS
            and row.get("required_authoring_motif") is None
        )
        third["required_authoring_motif"] = copy.deepcopy(
            by_id[V2_REFINEMENT_CASE_IDS[0]]["required_authoring_motif"]
        )
    elif mutation == "public-field":
        by_id[V2_REFINEMENT_CASE_IDS[0]]["level"] = "L0"
    elif mutation == "shape":
        by_id[V2_REFINEMENT_CASE_IDS[0]]["required_authoring_motif"] = {
            "task_class": "typed_capability_dag",
            "nodes": [],
            "terminal_node_id": "missing",
            "final_program_node_id": None,
        }
    else:
        by_id[V2_REFINEMENT_CASE_IDS[0]]["required_authoring_motif"] = copy.deepcopy(
            V2_REFINEMENT_REQUIRED_MOTIFS[V2_REFINEMENT_CASE_IDS[1]]
        )
    with pytest.raises(HJReportError) as caught:
        _validate_v2_oracle_refinement(v2a, v2b)
    assert caught.value.code == "h_j_v2_refinement_invalid"


def _authoring_motif(task) -> dict[str, object]:
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


def _authored_evidence_fixture(tmp_path: Path):
    task = build_np_hard_authoring_tasks_v2(
        root=ROOT, suite_path=GENERALIZATION_SUITE
    )[0]
    case_id = "fixture-authored-case"
    case_output = tmp_path / "case"
    case_output.mkdir(parents=True, exist_ok=True)
    accepted = [node.node_id for node in task.gap_nodes]
    deletion_nodes: list[dict[str, object]] = []
    for node in task.gap_nodes:
        audit_file = case_output / f"without-{node.node_id}.lean"
        audit_file.write_text(f"-- delete {node.declaration}\n", encoding="utf-8")
        deletion_nodes.append(
            {
                "node_id": node.node_id,
                "declaration": node.declaration,
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
    raw = {
        "status": "VERIFIED",
        "artifact": {"endpoint": task.target_problem.term},
        "independent_replay": {"passed": True},
        "axiom_audit": {"passed": True},
        "fresh_core": {"count": len(accepted), "passed": True},
        "deletion_audit": {
            "passed": True,
            "node_count": len(deletion_nodes),
            "nodes": deletion_nodes,
        },
        "capability_dag": task.to_dict(),
        "authoring_runtime": {
            "status": "VERIFIED",
            "task_request_id": task.request_id,
            "accepted_nodes": accepted,
            "fresh_core_rediscoveries": len(accepted),
            "deletion_audits": deletion_nodes,
            "result": {"accepted_nodes": accepted},
        },
    }
    run_rows = {
        case_id: {
            "output_dir": str(case_output),
            "raw_result": raw,
        }
    }
    scorecard = {"verified_authoring": [{"case_id": case_id}]}
    contract = {
        case_id: {
            "canonical_problem": task.target_problem.term,
            "required_authoring_motif": _authoring_motif(task),
        }
    }
    return run_rows, scorecard, contract


def test_v2_deletion_diagnostic_requires_full_declaration_or_projection() -> None:
    declaration = "Generated.NPHardV2.Cfixture.Authoring.tmKarpProgram"

    def command(line: str) -> dict[str, object]:
        return {
            "timed_out": False,
            "exit_code": 1,
            "stdout": line,
            "stderr": "",
        }

    assert _deletion_command_matches_declaration(
        command(
            "error(lean.unknownIdentifier): Unknown identifier "
            f"`{declaration}`"
        ),
        declaration,
    )
    assert _deletion_command_matches_declaration(
        command(
            "error(lean.unknownIdentifier): Unknown identifier "
            f"`{declaration}.run`"
        ),
        declaration,
    )
    assert _deletion_command_matches_declaration(
        command(f"error: unknown constant '{declaration}'"),
        declaration,
    )
    assert _deletion_command_matches_declaration(
        command(
            "/tmp/without-node.lean:12:7: "
            "error(lean.unknownIdentifier): Unknown identifier "
            f"`{declaration}`"
        ),
        declaration,
    )
    rejected = (
        "error(lean.unknownIdentifier): Unknown identifier `tmKarpProgram`",
        (
            "error(lean.unknownIdentifier): Unknown identifier `tmKarpProgram`; "
            f"while checking `{declaration}`"
        ),
        (
            "error(lean.unknownIdentifier): Unknown identifier `tmKarpProgram`\n"
            f"note: full declaration `{declaration}`"
        ),
        (
            "warning: Unknown identifier "
            f"`{declaration}`"
        ),
        (
            "warning: quoted diagnostic: "
            "error(lean.unknownIdentifier): Unknown identifier "
            f"`{declaration}`"
        ),
        f"note: error: unknown constant '{declaration}'",
        (
            "error(lean.unknownIdentifier): Unknown identifier "
            f"`{declaration}Suffix`"
        ),
    )
    assert all(
        not _deletion_command_matches_declaration(command(line), declaration)
        for line in rejected
    )


def test_h_j_authored_audit_keeps_v1_history_but_is_strict_in_v2(
    tmp_path: Path,
) -> None:
    run_rows, scorecard, contract = _authored_evidence_fixture(tmp_path)
    legacy = copy.deepcopy(run_rows)
    legacy_nodes = [{"passed": True}]
    raw = legacy["fixture-authored-case"]["raw_result"]
    raw["deletion_audit"] = {
        "passed": True,
        "node_count": 1,
        "nodes": legacy_nodes,
    }
    raw["authoring_runtime"]["deletion_audits"] = legacy_nodes
    historical_contract = {
        "fixture-authored-case": {
            "canonical_problem": contract["fixture-authored-case"][
                "canonical_problem"
            ],
            "required_authoring_motif": None,
        }
    }

    _validate_authored_run_evidence(
        legacy,
        scorecard=scorecard,
        contract=historical_contract,
        contract_epoch="v1",
        label="historical fixture",
    )
    with pytest.raises(HJReportError) as caught:
        _validate_authored_run_evidence(
            legacy,
            scorecard=scorecard,
            contract=contract,
            contract_epoch="v2",
            label="strict fixture",
        )
    assert caught.value.code == "h_j_authoring_audit_invalid"


def test_h_j_v2_authored_audit_accepts_exact_motif_and_ledgers(
    tmp_path: Path,
) -> None:
    run_rows, scorecard, contract = _authored_evidence_fixture(tmp_path)
    _validate_authored_run_evidence(
        run_rows,
        scorecard=scorecard,
        contract=contract,
        contract_epoch="v2",
        label="strict fixture",
    )


def test_h_j_v2_authored_audit_invokes_authoritative_validator(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    run_rows, scorecard, contract = _authored_evidence_fixture(tmp_path)
    observed: dict[str, object] = {}

    def validate(**kwargs):
        observed.update(kwargs)
        return ()

    monkeypatch.setattr(
        h_j_report,
        "validate_successor_only_authoritative_evidence_v2",
        validate,
    )
    _validate_authored_run_evidence(
        run_rows,
        scorecard=scorecard,
        contract=contract,
        contract_epoch="v2",
        label="authoritative fixture",
    )
    raw = run_rows["fixture-authored-case"]["raw_result"]
    assert observed["runtime"] is raw["authoring_runtime"]
    assert observed["require_files"] is True
    assert Path(str(observed["case_output"])) == Path(
        run_rows["fixture-authored-case"]["output_dir"]
    ).resolve()


def test_h_j_v2_authored_audit_rejects_authoritative_validator_failure(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    run_rows, scorecard, contract = _authored_evidence_fixture(tmp_path)

    def reject(**_kwargs):
        raise NPHardAuthoringContractError(
            "candidate_dependency_stale",
            "fixture authoritative evidence drifted",
        )

    monkeypatch.setattr(
        h_j_report,
        "validate_successor_only_authoritative_evidence_v2",
        reject,
    )
    with pytest.raises(HJReportError) as caught:
        _validate_authored_run_evidence(
            run_rows,
            scorecard=scorecard,
            contract=contract,
            contract_epoch="v2",
            label="authoritative fixture",
        )
    assert caught.value.code == "h_j_authoring_audit_invalid"


@pytest.mark.parametrize(
    "mutation",
    [
        "missing-motif",
        "motif",
        "accepted",
        "fresh",
        "deletion-diagnostic",
        "deletion-short-only",
        "deletion-command",
    ],
)
def test_h_j_v2_authored_audit_mutations_fail_closed(
    tmp_path: Path, mutation: str
) -> None:
    run_rows, scorecard, contract = _authored_evidence_fixture(tmp_path)
    raw = run_rows["fixture-authored-case"]["raw_result"]
    if mutation == "missing-motif":
        contract["fixture-authored-case"]["required_authoring_motif"] = None
    elif mutation == "motif":
        contract["fixture-authored-case"]["required_authoring_motif"]["nodes"][0][
            "capability"
        ] = "substituted_capability"
    elif mutation == "accepted":
        raw["authoring_runtime"]["accepted_nodes"] = []
    elif mutation == "fresh":
        raw["fresh_core"]["count"] = 0
        raw["authoring_runtime"]["fresh_core_rediscoveries"] = 0
    elif mutation == "deletion-diagnostic":
        raw["deletion_audit"]["nodes"][0]["diagnostic_matched"] = False
    elif mutation == "deletion-short-only":
        audit = raw["deletion_audit"]["nodes"][0]
        short_name = str(audit["declaration"]).rsplit(".", 1)[-1]
        audit["command"]["stderr"] = (
            "error(lean.unknownIdentifier): Unknown identifier "
            f"`{short_name}`"
        )
    else:
        audit = raw["deletion_audit"]["nodes"][0]
        audit["command"]["stderr"] = (
            f"warning: checked declaration {audit['declaration']}\n"
            "error(lean.unknownIdentifier): Unknown identifier `OtherDeclaration`"
        )

    with pytest.raises(HJReportError) as caught:
        _validate_authored_run_evidence(
            run_rows,
            scorecard=scorecard,
            contract=contract,
            contract_epoch="v2",
            label="strict fixture",
        )
    assert caught.value.code == "h_j_authoring_audit_invalid"


def test_optional_regression_is_all_five_or_absent() -> None:
    assert validate_optional_stage_regressions(None) == {
        "provided": False,
        "capability_weight": 0,
        "note": "optional unified all regression evidence was not supplied",
        "reports": [],
    }
    with pytest.raises(HJReportError) as caught:
        _parse_labeled_paths(
            ["h-j.1-adapter=tmp/one.json"],
            expected=STAGE_LABELS,
            option="--stage-regression",
        )
    assert caught.value.code == "h_j_partial_evidence"


def _live_call(index: int) -> dict[str, object]:
    return {
        "called": True,
        "ok": True,
        "status_code": 200,
        "provider_attempts": 1,
        "duration_seconds": 1.25,
        "request_id": "sha256:" + f"{index:064x}",
        "prompt_sha256": "sha256:" + f"{index + 100:064x}",
        "response_sha256": "sha256:" + f"{index + 200:064x}",
        "usage": {"prompt_tokens": 10, "completion_tokens": 5, "total_tokens": 15},
    }


def test_each_substage_requires_positive_real_http_200_evidence() -> None:
    calls = [_live_call(1), _live_call(2)]
    assert len(_validate_http_calls(calls, label="fixture")) == 2

    with pytest.raises(HJReportError) as caught:
        _validate_http_calls([], label="fixture")
    assert caught.value.code == "h_j_deepseek_http_evidence_missing"

    reused = [_live_call(1), _live_call(1)]
    with pytest.raises(HJReportError) as caught:
        _validate_http_calls(reused, label="fixture")
    assert caught.value.code == "h_j_deepseek_http_evidence_reused"

    failed = copy.deepcopy(calls)
    failed[0]["status_code"] = 503
    with pytest.raises(HJReportError) as caught:
        _validate_http_calls(failed, label="fixture")
    assert caught.value.code == "h_j_deepseek_http_evidence_invalid"


def _scorer_rows(
    contract: dict[str, dict[str, object]], successful_authoring: set[str]
) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for case_id, expected in contract.items():
        tier = expected["tier"]
        if tier == "C0-existing":
            status, failure, calls, success, first = "VERIFIED", None, 0, True, True
        elif tier == "C0-authoring" and case_id in successful_authoring:
            status, failure, calls, success, first = "VERIFIED", None, 1, True, True
        elif tier == "C0-authoring":
            status = "BLOCKED_MISSING_PREREQUISITE"
            failure, calls, success, first = "precise_missing_capability", 0, False, False
        elif tier == "C0-safety":
            status = expected["expected_public_status"]
            failure = expected["expected_failure_codes"][0]
            calls, success, first = 0, True, False
        else:
            status = "BLOCKED_MISSING_PREREQUISITE"
            failure, calls, success, first = "frontier_blocker", 0, False, False
        rows.append(
            {
                "case_id": case_id,
                "split": expected["split"],
                "family": expected["family"],
                "tier": tier,
                "outcome_class": expected["outcome_class"],
                "scored": expected["scored"],
                "requires_model": expected["requires_model"],
                "public_status": status,
                "failure_code": failure,
                "model_calls": calls,
                "first_attempt_verified": first,
                "capability_success": success,
            }
        )
    return rows


def test_v2_rows_establish_eight_heldout_and_four_overall_authoring_families() -> None:
    static = validate_static_assets(_static_paths())
    contract = static["case_contract"]
    successful = {
        "cdev-au-01-tagged-three-sat-adapter",
        "chld-au-01-feedback-node-set",
        "chld-au-03-max-cut-structured",
        "chld-au-04-max-cut-binary",
        "chld-au-06-hitting-set",
        "chld-au-07-set-covering",
        "chld-au-08-set-packing",
        "chld-au-09-feedback-arc-set",
        "chld-au-10-three-dimensional-matching",
    }
    scorecard = _scorecard_from_rows(
        _scorer_rows(contract, successful),
        contract=contract,
        label="fixture",
    )

    assert scorecard["case_count"] == scorecard["unique_identity_count"] == 34
    assert scorecard["verified_authoring_identity_count"] == 9
    assert scorecard["heldout_verified_authoring_identity_count"] == 8
    assert scorecard["verified_authoring_family_count"] == 4
    assert scorecard["verified_authoring_families"] == [
        "graph",
        "other",
        "sat-csp",
        "set-system",
    ]
    assert scorecard["family_macro_verified_at_budget"] > 0.554286
    assert scorecard["safety_correct_count"] == scorecard["safety_case_count"] == 8
    assert len(scorecard["frontier"]) == 2


def test_forged_authoring_success_without_a_model_call_is_not_counted() -> None:
    static = validate_static_assets(_static_paths())
    contract = static["case_contract"]
    case_id = "cdev-au-01-tagged-three-sat-adapter"
    rows = _scorer_rows(contract, {case_id})
    row = next(row for row in rows if row["case_id"] == case_id)
    row["model_calls"] = 0

    scorecard = _scorecard_from_rows(rows, contract=contract, label="fixture")
    assert scorecard["verified_authoring_identity_count"] == 0


def test_secret_scanner_allows_guards_but_rejects_credentials() -> None:
    _assert_no_secret(
        {
            "api_key_configured": True,
            "api_key_or_authorization_absent": True,
            "secret_absent": True,
        },
        label="safe",
    )
    with pytest.raises(HJReportError) as caught:
        _assert_no_secret(
            {"authorization": "Bearer definitely-not-reportable"},
            label="unsafe",
        )
    assert caught.value.code == "h_j_secret_leak"


def test_content_addressed_raw_and_score_mutation_is_detectable() -> None:
    report = {"schema_version": "fixture", "run_valid": True, "cases": []}
    report["run_id"] = _canonical_content_hash(report, field="run_id")
    assert report["run_id"] == _canonical_content_hash(report, field="run_id")

    report["run_valid"] = False
    assert report["run_id"] != _canonical_content_hash(report, field="run_id")
