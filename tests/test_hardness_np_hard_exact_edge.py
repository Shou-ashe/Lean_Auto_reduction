from __future__ import annotations

import hashlib
import json
import threading
import time
from pathlib import Path

import pytest

from agent.hardness.authoring import MODEL_AUTO_MODE
from agent.hardness.models import sha256_id
from agent.hardness.np_hard_exact_edge import (
    EXACT_EDGE_CASE_RESULT_SCHEMA_V1,
    EXACT_EDGE_CAPABILITY_DECLARATION,
    EXACT_EDGE_ORACLE_SCHEMA_V1,
    EXACT_EDGE_RUN_REPORT_SCHEMA_V1,
    EXACT_EDGE_SUITE_SCHEMA_V1,
    ExactEdgeBudgetProfile,
    ExactEdgeContractError,
    ExactEdgeManifest,
    ExactEdgeOracle,
    ExactEdgeOracleCase,
    build_exact_edge_artifact_source,
    load_exact_edge_oracle,
    load_exact_edge_manifest,
    load_exact_edge_suite,
    run_exact_reduction_edge_benchmark,
    score_exact_reduction_edge_run,
    _endpoint_preflight_payload,
    _existing_route_declaration_audit,
    _selected_existing_path_evidence,
    _workspace_quarantine_violations,
)


ROOT = Path(__file__).resolve().parents[1]


def _suite_payload(*, cases: list[dict[str, object]] | None = None) -> dict[str, object]:
    return {
        "schema_version": EXACT_EDGE_SUITE_SCHEMA_V1,
        "split": "dev",
        "cases": cases
        or [
            {
                "case_id": "edge-dev-one",
                "module": "ComplexityReduction.Routes.Production",
                "source": (
                    "ComplexityReduction.Problems.Karp21.Satisfiability."
                    "threeSATStructuredProblem"
                ),
                "target": (
                    "ComplexityReduction.Problems.Karp21.GraphAtoms."
                    "cliqueStructuredProblem"
                ),
                "statement": "Construct a polynomial reduction from structured 3SAT to Clique.",
                "statement_hash": sha256_id(
                    {
                        "statement": (
                            "Construct a polynomial reduction from structured 3SAT to Clique."
                        )
                    }
                ),
                "budget_profile": "default",
                "construction_policy": {
                    "mode": "existing_edge_reconstruction",
                    "allow_composition": True,
                    "require_new_primitive": False,
                },
                "endpoint_contract_version": "exact-edge-endpoint-v1",
            }
        ],
    }


def _write_json(path: Path, value: object) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value), encoding="utf-8")
    return path


def _tagged_file(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def _content_hash(value: dict[str, object]) -> str:
    payload = dict(value)
    payload.pop("content_sha256", None)
    return sha256_id(payload)


def _direct_case_result(
    case, *, status: str = "VERIFIED", evidence_root: Path | None = None
) -> dict[str, object]:
    verified = status == "VERIFIED"
    row: dict[str, object] = {
        "schema_version": EXACT_EDGE_CASE_RESULT_SCHEMA_V1,
        "case_id": case.case_id,
        "split": case.split,
        "edge_id": case.edge_id,
        "source": case.source,
        "target": case.target,
        "status": status,
        "producer_status": status,
        "outcome_class": "existing_edge_reconstructed" if verified else "blocked",
        "failure_code": None if verified else "exact_edge_authoring_dag_unavailable",
        "original_failure_code": None,
        "protocol_valid": True,
        "accepted_capability_head": (
            "ComplexityReduction.Certificate.CertifiedReduction" if verified else None
        ),
        "accepted_capability_declaration": (
            EXACT_EDGE_CAPABILITY_DECLARATION if verified else None
        ),
        "exact_artifact_generated": verified,
        "selected_route_id": "sha256:" + "1" * 64 if verified else None,
        "selected_route_atoms": ["ComplexityReduction.Routes.Example.finalRoute"] if verified else [],
        "route_atom_count": 1 if verified else 0,
        "artifact_imports": ["ComplexityReduction.Routes.Production"] if verified else [],
        "artifact_file": None,
        "artifact_sha256": None,
        "producer_artifact_file": None,
        "producer_artifact_sha256": None,
        "authored_candidate_declaration": None,
        "authored_route_declaration": None,
        "public_context": {
            "declared_module": case.module,
            "statement_sha256": sha256_id({"statement": case.statement}),
            "statement_hash": case.statement_hash,
            "construction_policy": case.construction_policy.to_dict(),
            "endpoint_contract_version": case.endpoint_contract_version,
        },
        "budget": {
            "profile": "default",
            "authoring_mode": MODEL_AUTO_MODE,
            "authoring_attempt_budget": 4,
            "lean_timeout_seconds": 60,
            "attempts_used": 0,
            "model_calls_used": 0,
            "http_attempts_used": 0,
        },
        "authoring_attempt_ledger": [],
        "first_accepted_attempt": None,
        "model_calls": 0,
        "http_ok_model_calls": 0,
        "model_call_ledger": [],
        "model_call_ledger_file": None,
        "model_call_ledger_sha256": None,
        "model_call_ledger_content_sha256": None,
        "token_usage": {},
        "audits": {},
        "security": {
            "quarantined_material_detected": False,
            "secret_detected": False,
            "archive_solution_accessed": False,
            "cross_job_artifact": False,
        },
        "blocker": None,
        "producer_payload_file": None,
        "producer_payload_sha256": None,
        "raw_result_sha256": None,
    }
    if evidence_root is None:
        row["audits"] = {
            name: {"status": "passed", "ok": True}
            for name in (
                "kernel",
                "replay",
                "axiom",
                "endpoint",
                "dependency",
                "program_direct_tm_coherence",
                "semantic_iff",
                "polynomial_bound",
            )
        }
        return row

    case_dir = evidence_root / "cases" / case.case_id
    case_dir.mkdir(parents=True, exist_ok=True)
    row["case_dir"] = str(case_dir.resolve())
    producer_payload = _write_json(
        case_dir / "producer-payload.json", {"case_id": case.case_id}
    )
    row["producer_payload_file"] = str(producer_payload.resolve())
    row["producer_payload_sha256"] = _tagged_file(producer_payload)
    row["raw_result_sha256"] = _tagged_file(producer_payload)
    ledger_payload = {
        "schema_version": "hardness_exact_edge_model_ledger_v1",
        "case_id": case.case_id,
        "edge_id": case.edge_id,
        "budget": row["budget"],
        "attempts": [],
        "calls": [],
        "token_usage": {},
        "issues": [],
    }
    ledger = _write_json(case_dir / "exact-edge-model-ledger.json", ledger_payload)
    row["model_call_ledger_file"] = str(ledger.resolve())
    row["model_call_ledger_sha256"] = _tagged_file(ledger)
    row["model_call_ledger_content_sha256"] = sha256_id(ledger_payload)
    if verified:
        artifact = case_dir / "ExactEdge.lean"
        artifact.write_text("exact artifact", encoding="utf-8")
        producer = case_dir / "Artifact.lean"
        producer.write_text("producer artifact", encoding="utf-8")
        row["artifact_file"] = str(artifact.resolve())
        row["artifact_sha256"] = _tagged_file(artifact)
        row["producer_artifact_file"] = str(producer.resolve())
        row["producer_artifact_sha256"] = _tagged_file(producer)
    audits: dict[str, object] = {}
    for name in (
        "kernel",
        "replay",
        "axiom",
        "endpoint",
        "dependency",
        "program_direct_tm_coherence",
        "semantic_iff",
        "polynomial_bound",
    ):
        evidence = _write_json(case_dir / "commands" / f"{name}.json", {"ok": verified})
        audits[name] = {
            "status": "passed" if verified else "unsupported",
            "ok": verified,
            "evidence_file": str(evidence.resolve()) if verified else None,
            "evidence_sha256": _tagged_file(evidence) if verified else None,
            "audit_artifact_file": None,
            "audit_artifact_sha256": None,
            "blocker": None if verified else "not_verified",
        }
    row["audits"] = audits
    return row


def _oracle_for_suite(suite, *, evidence_root: Path) -> ExactEdgeOracle:
    cases = {
        case.case_id: ExactEdgeOracleCase(
            case_id=case.case_id,
            split=case.split,
            archive_id="05-007",
            canonical_source=case.source,
            canonical_target=case.target,
            status="ready",
            allow_composition=True,
            require_new_primitive=False,
            forbidden_route_imports=(),
            required_audits=(
                "kernel",
                "replay",
                "axiom",
                "endpoint",
                "dependency",
                "program_direct_tm_coherence",
                "semantic_iff",
                "polynomial_bound",
            ),
            existing_route="ComplexityReduction.Routes.Example.finalRoute",
        )
        for case in suite.cases
    }
    oracle_file = _write_json(
        evidence_root / "oracle.json", {"case_ids": sorted(cases)}
    )
    return ExactEdgeOracle(
        cases=cases,
        file=oracle_file,
        sha256=_tagged_file(oracle_file),
    )


def _manifest_for_suite(
    suite, oracle: ExactEdgeOracle, *, evidence_root: Path
) -> ExactEdgeManifest:
    manifest_file = _write_json(
        evidence_root / "manifest.json", {"oracle_sha256": oracle.sha256}
    )
    return ExactEdgeManifest(
        benchmark_id="exact-edge-test",
        suites={suite.split: suite},
        budget_profiles={
            "default": ExactEdgeBudgetProfile("default", MODEL_AUTO_MODE, 4, 60)
        },
        max_jobs=1,
        isolate_workspace=True,
        runtime_prebuilt=True,
        oracle_sha256=oracle.sha256,
        file=manifest_file,
        sha256=_tagged_file(manifest_file),
    )


def test_exact_edge_artifact_promotes_selected_path_to_exact_reduction() -> None:
    source = (
        "ComplexityReduction.Problems.Karp21.Satisfiability."
        "threeSATStructuredProblem"
    )
    target = (
        "ComplexityReduction.Problems.Karp21.GraphAtoms.cliqueStructuredProblem"
    )
    producer = (
        "import ComplexityReduction.Agent.Hardness.Runtime\n"
        "#check ComplexityReduction.Agent.Hardness.GeneratedArtifact.selectedPath\n"
    )
    artifact = build_exact_edge_artifact_source(
        producer_source=producer, source=source, target=target
    )
    assert f"CertifiedReduction\n      {source}\n      {target}" in artifact
    assert ".selectedPath.toCertifiedReduction" in artifact
    assert f"assert_standard_axioms {EXACT_EDGE_CAPABILITY_DECLARATION}" in artifact


def _run_report(
    suite,
    rows: list[dict[str, object]],
    *,
    output_root: Path,
    manifest: ExactEdgeManifest,
) -> dict[str, object]:
    run_id = "sha256:" + "8" * 64
    for row in rows:
        row["run_id"] = run_id
        row["content_sha256"] = _content_hash(row)
    report: dict[str, object] = {
        "schema_version": EXACT_EDGE_RUN_REPORT_SCHEMA_V1,
        "run_id": run_id,
        "run_valid": True,
        "output_root": str(output_root.resolve()),
        "report_file": str((output_root / "report.json").resolve()),
        "manifest_sha256": manifest.sha256,
        "expected_oracle_sha256": manifest.oracle_sha256,
        "suite": {"sha256": suite.sha256},
        "cases": rows,
    }
    report["content_sha256"] = _content_hash(report)
    _write_json(output_root / "report.json", report)
    return report


def test_public_exact_edge_suite_is_strictly_answer_free(tmp_path: Path) -> None:
    suite = load_exact_edge_suite(_write_json(tmp_path / "suite.json", _suite_payload()))
    assert len(suite.cases) == 1
    assert suite.cases[0].edge_id.startswith("sha256:")

    leaked = _suite_payload()
    leaked["cases"][0]["solution"] = "Use the archived gadget."  # type: ignore[index]
    with pytest.raises(ExactEdgeContractError) as error:
        load_exact_edge_suite(_write_json(tmp_path / "leaked.json", leaked))
    assert error.value.code in {
        "exact_edge_schema_invalid",
        "oracle_field_in_public_suite",
    }


@pytest.mark.parametrize(
    "statement",
    (
        "Read problems.7z and construct the reduction.",
        "Solution: use the complement graph.",
        "See Evaluation/exact_reduction_edge_oracle_v1.json.",
    ),
)
def test_public_exact_edge_statement_rejects_archive_or_oracle_material(
    tmp_path: Path, statement: str
) -> None:
    payload = _suite_payload()
    payload["cases"][0]["statement"] = statement  # type: ignore[index]
    with pytest.raises(ExactEdgeContractError):
        load_exact_edge_suite(_write_json(tmp_path / "suite.json", payload))


def test_oracle_schema_freezes_edge_policy_separately(tmp_path: Path) -> None:
    suite = load_exact_edge_suite(_write_json(tmp_path / "suite.json", _suite_payload()))
    case = suite.cases[0]
    payload = {
        "schema_version": EXACT_EDGE_ORACLE_SCHEMA_V1,
        "cases": [
            {
                "case_id": case.case_id,
                "split": case.split,
                "archive_id": "05-007",
                "canonical_direction": {"source": case.source, "target": case.target},
                "status": "ready",
                "allow_composition": True,
                "require_new_primitive": False,
                "forbidden_route_imports": [],
                "required_audits": [
                    "kernel",
                    "replay",
                    "axiom",
                    "endpoint",
                    "dependency",
                    "program_direct_tm_coherence",
                    "semantic_iff",
                    "polynomial_bound",
                ],
                "existing_route": "ComplexityReduction.Routes.ThreeSATToClique.finalRoute",
            }
        ],
    }
    oracle = load_exact_edge_oracle(_write_json(tmp_path / "oracle.json", payload))
    assert oracle.cases[case.case_id].canonical_target == case.target


@pytest.mark.parametrize(
    "mutation",
    (
        "wrong-statement-hash",
        "new-mode-without-primitive",
        "reconstruction-with-primitive",
        "bad-endpoint-contract",
        "missing-policy",
    ),
)
def test_public_exact_edge_case_rejects_policy_and_hash_mutations(
    tmp_path: Path, mutation: str
) -> None:
    payload = _suite_payload()
    case = payload["cases"][0]  # type: ignore[index]
    if mutation == "wrong-statement-hash":
        case["statement_hash"] = "sha256:" + "0" * 64  # type: ignore[index]
    elif mutation == "new-mode-without-primitive":
        case["construction_policy"] = {  # type: ignore[index]
            "mode": "direct_new_edge",
            "allow_composition": False,
            "require_new_primitive": False,
        }
    elif mutation == "reconstruction-with-primitive":
        case["construction_policy"] = {  # type: ignore[index]
            "mode": "existing_edge_reconstruction",
            "allow_composition": True,
            "require_new_primitive": True,
        }
    elif mutation == "bad-endpoint-contract":
        case["endpoint_contract_version"] = "some-other-version"  # type: ignore[index]
    else:
        del case["construction_policy"]  # type: ignore[index]
    with pytest.raises(ExactEdgeContractError):
        load_exact_edge_suite(_write_json(tmp_path / "suite.json", payload))


def test_runner_preserves_boundary_failures_and_observes_parallelism(tmp_path: Path) -> None:
    cases = []
    for index in range(2):
        case = _suite_payload()["cases"][0].copy()  # type: ignore[index,union-attr]
        case["case_id"] = f"edge-dev-{index}"
        case["target"] = (
            "ComplexityReduction.Problems.Karp21.GraphAtoms.cliqueStructuredProblem"
            if index == 0
            else "ComplexityReduction.Presentation.ZeroOneIP.structuredProblem"
        )
        cases.append(case)
    suite = load_exact_edge_suite(
        _write_json(tmp_path / "suite.json", _suite_payload(cases=cases))
    )
    profile = ExactEdgeBudgetProfile("default", MODEL_AUTO_MODE, 4, 60)
    active = 0
    maximum = 0
    lock = threading.Lock()

    def execute(**kwargs):
        nonlocal active, maximum
        with lock:
            active += 1
            maximum = max(maximum, active)
        try:
            time.sleep(0.05)
            case = kwargs["case"]
            return _direct_case_result(
                case,
                status="VERIFIED" if case.case_id.endswith("0") else "BLOCKED",
            )
        finally:
            with lock:
                active -= 1

    report = run_exact_reduction_edge_benchmark(
        root=ROOT,
        suite=suite,
        budget_profiles={"default": profile},
        output_root=tmp_path / "out",
        jobs=2,
        isolate_workspace=False,
        case_executor=execute,
    )
    assert report["run_valid"] is True
    assert report["metrics"]["verified_count"] == 1
    assert report["metrics"]["blocked_count"] == 1
    assert report["parallel_execution"]["maximum_concurrent_case_tasks"] >= 2
    assert maximum >= 2
    assert report["cases"][0]["public_context"]["statement_sha256"] == sha256_id(
        {"statement": suite.cases[0].statement}
    )


def test_missing_uhc_to_dhc_authoring_dag_blocks_without_fake_model_call(
    tmp_path: Path,
) -> None:
    payload = _suite_payload()
    payload["cases"][0].update(  # type: ignore[index]
        {
            "case_id": "edge-dev-undirected-to-directed-hc",
            "source": (
                "ComplexityReduction.Presentation.UndirectedHamiltonianCircuit."
                "structuredProblem"
            ),
            "target": (
                "ComplexityReduction.Presentation.DirectedHamiltonianCircuit."
                "structuredProblem"
            ),
        }
    )
    suite = load_exact_edge_suite(_write_json(tmp_path / "suite.json", payload))
    profile = ExactEdgeBudgetProfile("default", MODEL_AUTO_MODE, 4, 60)

    def execute(**kwargs):
        case = kwargs["case"]
        return {
            "schema_version": "hardness_agent_result_v1",
            "status": "BLOCKED",
            "goal": {
                "objective": "reduce_to",
                "source_declaration": case.source,
                "target_declaration": case.target,
            },
            "selected_route": None,
            "authoring_attempts": [],
            "model_calls": [],
            "authored_candidate_declaration": None,
            "authored_route_declaration": None,
            "artifact_file": None,
            "failures": [
                {
                    "phase": "gap_planning",
                    "code": "missing_primitive",
                    "retryable": False,
                    "evidence": "no safe authoring skeleton",
                }
            ],
        }

    report = run_exact_reduction_edge_benchmark(
        root=ROOT,
        suite=suite,
        budget_profiles={"default": profile},
        output_root=tmp_path / "out",
        jobs=1,
        isolate_workspace=False,
        case_executor=execute,
    )
    row = report["cases"][0]
    assert report["run_valid"] is True
    assert row["failure_code"] == "exact_edge_authoring_dag_unavailable"
    assert row["model_calls"] == 0
    assert row["status"] == "BLOCKED"


def test_missing_public_endpoint_is_a_protocol_blocker_not_infra_error() -> None:
    case = type(
        "Case",
        (),
        {
            "source": "ComplexityReduction.Presentation.MissingSource.structuredProblem",
            "target": "ComplexityReduction.Presentation.MissingTarget.structuredProblem",
        },
    )()
    payload = _endpoint_preflight_payload(
        case=case,
        context={
            "missing_endpoint_modules": [
                "ComplexityReduction.Presentation.MissingSource",
                "ComplexityReduction.Presentation.MissingTarget",
            ],
            "wrapper_compile_ok": False,
        },
    )
    assert payload["status"] == "BLOCKED"
    assert payload["failures"][0]["code"] == "exact_edge_endpoint_unavailable"


def test_staged_executor_is_dispatched_for_direct_new_edge_policy(tmp_path: Path) -> None:
    payload = _suite_payload()
    payload["cases"][0].update(  # type: ignore[index]
        {
            "case_id": "edge-dev-undirected-to-directed-hc",
            "source": (
                "ComplexityReduction.Presentation.UndirectedHamiltonianCircuit."
                "structuredProblem"
            ),
            "target": (
                "ComplexityReduction.Presentation.DirectedHamiltonianCircuit."
                "structuredProblem"
            ),
            "statement_hash": sha256_id(
                {
                    "statement": (
                        "Construct a polynomial reduction from structured 3SAT to Clique."
                    )
                }
            ),
            "construction_policy": {
                "mode": "direct_new_edge",
                "allow_composition": False,
                "require_new_primitive": True,
            },
        }
    )
    suite = load_exact_edge_suite(_write_json(tmp_path / "suite.json", payload))
    profile = ExactEdgeBudgetProfile("default", MODEL_AUTO_MODE, 4, 60)
    staged_calls = {"count": 0}

    def staged_executor(**kwargs):
        staged_calls["count"] += 1
        return {
            "schema_version": "hardness_exact_edge_staged_result_v1",
            "task_class": "typed_exact_edge_construction_dag",
            "status": "BLOCKED",
            "goal": {
                "objective": "reduce_to",
                "source_declaration": kwargs["case"].source,
                "target_declaration": kwargs["case"].target,
            },
            "selected_route": None,
            "authoring_attempts": [],
            "model_calls": [],
            "authored_candidate_declaration": None,
            "authored_route_declaration": None,
            "artifact_file": None,
            "node_count": 11,
            "accepted_nodes": [],
            "audits": {},
            "failure_code": "model_provider_unavailable",
            "failure_message": "no model client",
        }

    def execute(**kwargs):
        assert kwargs["case"].construction_policy.mode == "direct_new_edge"
        return staged_executor(**kwargs)

    report = run_exact_reduction_edge_benchmark(
        root=ROOT,
        suite=suite,
        budget_profiles={"default": profile},
        output_root=tmp_path / "out",
        jobs=1,
        isolate_workspace=False,
        case_executor=execute,
    )
    row = report["cases"][0]
    assert report["run_valid"] is True
    assert row["authoring_protocol"] == "typed_exact_edge_construction_dag"
    assert row["status"] == "FAILED"
    assert row["outcome_class"] == "failed"
    assert row["model_calls"] == 0
    assert staged_calls["count"] == 1
    assert row["public_context"]["statement_hash"] == suite.cases[0].statement_hash
    assert row["public_context"]["construction_policy"] == {
        "mode": "direct_new_edge",
        "allow_composition": False,
        "require_new_primitive": True,
    }


def test_workspace_quarantine_allows_only_generated_exact_edge_benchmark(
    tmp_path: Path,
) -> None:
    (tmp_path / "Lean/Reference/ComplexityReduction").mkdir(parents=True)
    generated = tmp_path / "Lean/Reference/Benchmark/ExactEdgePublic"
    generated.mkdir(parents=True)
    (generated / "Case.lean").write_text("", encoding="utf-8")
    public_build = tmp_path / "Lean/.lake/build/lib/lean/ComplexityReduction"
    public_build.mkdir(parents=True)
    generated_build = tmp_path / "Lean/.lake/build/lib/lean/Benchmark/ExactEdgePublic"
    generated_build.mkdir(parents=True)
    (generated_build / "Case.olean").write_bytes(b"")
    assert _workspace_quarantine_violations(tmp_path) == []
    forbidden = tmp_path / "Lean/Reference/Benchmark/Hardness/Evaluation"
    forbidden.mkdir(parents=True)
    assert _workspace_quarantine_violations(tmp_path)


def test_existing_route_accepts_kernel_checked_component_expansion(
    tmp_path: Path,
) -> None:
    atoms = [
        "ComplexityReduction.Domain.ThreeSATToGraphColoringStandardTM.sharedGadget",
        "ComplexityReduction.Domain.GraphColoringToChromaticNumberAdapter.targetAdapter",
    ]
    exact = tmp_path / "ExactEdge.lean"
    producer = tmp_path / "Artifact.lean"
    materialized = "\n".join(atoms)
    exact.write_text(materialized, encoding="utf-8")
    producer.write_text(materialized, encoding="utf-8")
    evidence = _selected_existing_path_evidence(
        {
            "selected_route_id": "sha256:" + "1" * 64,
            "selected_route_atoms": atoms,
            "artifact_file": str(exact),
            "producer_artifact_file": str(producer),
            "authored_candidate_declaration": None,
            "authored_route_declaration": None,
            "outcome_class": "existing_edge_reconstructed",
        }
    )
    assert evidence["ok"] is True
    producer.write_text(atoms[0], encoding="utf-8")
    assert _selected_existing_path_evidence(
        {
            "selected_route_id": "sha256:" + "1" * 64,
            "selected_route_atoms": atoms,
            "artifact_file": str(exact),
            "producer_artifact_file": str(producer),
            "authored_candidate_declaration": None,
            "authored_route_declaration": None,
            "outcome_class": "existing_edge_reconstructed",
        }
    )["ok"] is False


def test_existing_route_declaration_has_exact_oracle_endpoints() -> None:
    manifest = load_exact_edge_manifest(
        ROOT / "Benchmark/Hardness/EXACT_REDUCTION_EDGE_MANIFEST.json"
    )
    case = manifest.suites["dev"].cases[1]
    audit = _existing_route_declaration_audit(
        manifest=manifest,
        case=case,
        declaration="ComplexityReduction.Routes.ThreeSATToZeroOneIP.finalRoute",
    )
    assert audit["ok"] is True


@pytest.mark.parametrize(
    ("mutation", "expected_issue"),
    (
        ("target-hardness", "target_hardness_only_not_exact_edge"),
        ("reverse", "candidate_wrong_direction"),
        ("endpoint", "candidate_wrong_endpoint"),
        ("missing-exact-artifact", "candidate_exact_artifact_missing"),
        ("forbidden-import", "forbidden_route_import"),
        ("archive-solution", "archive_solution_access"),
        ("artifact-hash", "exact_artifact_file_binding_invalid"),
        ("ledger-count", "model_call_count_mismatch"),
        ("shared-audit", "required_audits_share_evidence"),
    ),
)
def test_independent_scorer_rejects_exact_edge_mutations(
    tmp_path: Path, mutation: str, expected_issue: str
) -> None:
    suite = load_exact_edge_suite(_write_json(tmp_path / "suite.json", _suite_payload()))
    case = suite.cases[0]
    output_root = tmp_path / "run"
    row = _direct_case_result(case, evidence_root=output_root)
    oracle = _oracle_for_suite(suite, evidence_root=tmp_path)
    if mutation == "target-hardness":
        row["accepted_capability_head"] = (
            "ComplexityReduction.Certificate.NativeTMNPHard"
        )
    elif mutation == "reverse":
        row["source"], row["target"] = row["target"], row["source"]
    elif mutation == "endpoint":
        row["target"] = "ComplexityReduction.Presentation.ZeroOneIP.structuredProblem"
    elif mutation == "missing-exact-artifact":
        row["exact_artifact_generated"] = False
    elif mutation == "forbidden-import":
        oracle_case = oracle.cases[case.case_id]
        oracle = ExactEdgeOracle(
            cases={
                case.case_id: ExactEdgeOracleCase(
                    **{
                        **oracle_case.__dict__,
                        "forbidden_route_imports": (
                            "ComplexityReduction.Routes.Example",
                        ),
                    }
                )
            },
            file=oracle.file,
            sha256=oracle.sha256,
        )
    elif mutation == "archive-solution":
        row["security"]["archive_solution_accessed"] = True  # type: ignore[index]
    elif mutation == "artifact-hash":
        row["artifact_sha256"] = "sha256:" + "0" * 64
    elif mutation == "ledger-count":
        row["model_calls"] = 1
    elif mutation == "shared-audit":
        audits = row["audits"]  # type: ignore[assignment]
        audits["replay"]["evidence_file"] = audits["kernel"]["evidence_file"]  # type: ignore[index]
        audits["replay"]["evidence_sha256"] = audits["kernel"]["evidence_sha256"]  # type: ignore[index]
    manifest = _manifest_for_suite(suite, oracle, evidence_root=tmp_path)
    score = score_exact_reduction_edge_run(
        manifest=manifest,
        suite=suite,
        oracle=oracle,
        run_report=_run_report(
            suite, [row], output_root=output_root, manifest=manifest
        ),
    )
    assert score["run_valid"] is False
    assert score["scorecard"]["mutation_rejection_counts"][expected_issue] == 1


def test_scorer_rejects_forged_in_memory_six_of_six_report(tmp_path: Path) -> None:
    suite = load_exact_edge_suite(_write_json(tmp_path / "suite.json", _suite_payload()))
    oracle = _oracle_for_suite(suite, evidence_root=tmp_path)
    manifest = _manifest_for_suite(
        suite, oracle, evidence_root=tmp_path
    )
    output_root = tmp_path / "run"
    row = _direct_case_result(suite.cases[0], evidence_root=output_root)
    report = _run_report(
        suite, [row], output_root=output_root, manifest=manifest
    )
    report["cases"][0]["artifact_sha256"] = "sha256:" + "0" * 64  # type: ignore[index]
    score = score_exact_reduction_edge_run(
        manifest=manifest,
        suite=suite,
        oracle=oracle,
        run_report=report,
    )
    assert score["run_valid"] is False
    assert score["scorecard"]["mutation_rejection_counts"][
        "run_report_persistence_mismatch"
    ] == 1
