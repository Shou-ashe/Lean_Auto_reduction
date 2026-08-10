from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest

import scripts.build_np_hard_h_k_full_report as h_k_report
from agent.hardness.models import sha256_id
from scripts.build_np_hard_h_k_full_report import (
    DIRECT_REUSE_CASES,
    PUBLICATION_AUDIT_SCHEMA,
    PUBLICATION_CATALOG_SCHEMA,
    PUBLICATION_MANIFEST_SCHEMA,
    REUSE_CASES,
    REUSE_STAGE_LABELS,
    STAGE_LABELS,
    TRANSITIVE_REUSE_CASES,
    HKReportError,
    _assert_no_secret,
    _canonical_content_hash,
    _parse_labeled_paths,
    _route_signature,
    _validate_http_calls,
    build_parser,
    validate_h_j_and_candidates,
    validate_publication_audits,
    validate_publication_catalog,
    validate_reuse,
)


ROOT = Path(__file__).resolve().parents[1]
HARDNESS = ROOT / "Benchmark/Hardness"


def _hash_file(path: Path) -> str:
    import hashlib

    return f"sha256:{hashlib.sha256(path.read_bytes()).hexdigest()}"


def _write_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def _seal(value: dict, field: str) -> dict:
    value[field] = _canonical_content_hash(value, field=field)
    return value


def _route(source: str, target: str) -> dict:
    return {
        "task_class": "typed_tmkarp_admission_dag",
        "source": source,
        "target": target,
        "direction": "source_to_target",
        "selected_hub": source,
        "terminal_node_id": "semantic-iff",
        "final_program_node_id": "program",
        "model_nodes": [
            {"node_id": "program", "capability": "program", "depends_on": []},
            {
                "node_id": "semantic-iff",
                "capability": "semantic_iff",
                "depends_on": ["program"],
            },
        ],
    }


def test_h_k_stage_and_reuse_interfaces_are_fixed() -> None:
    assert STAGE_LABELS == (
        "h-k.1-contract",
        "h-k.2-publication-activation",
        "h-k.3-publication-reuse",
        "h-k.4-drift-revalidation",
    )
    assert REUSE_STAGE_LABELS == STAGE_LABELS[-2:]
    assert len(DIRECT_REUSE_CASES) == 4
    assert TRANSITIVE_REUSE_CASES == {
        "chld-au-06-hitting-set": (
            "ComplexityReduction.Presentation.SetSystem."
            "hittingSetStructuredProblem"
        )
    }
    assert set(REUSE_CASES) == set(DIRECT_REUSE_CASES) | set(
        TRANSITIVE_REUSE_CASES
    )


def test_h_k_cli_requires_all_four_distinct_stage_labels() -> None:
    with pytest.raises(HKReportError) as error:
        _parse_labeled_paths(
            ["h-k.1-contract=tmp/one.json"],
            expected=STAGE_LABELS,
            option="--stage-run",
        )
    assert error.value.code == "h_k_partial_evidence"

    with pytest.raises(HKReportError) as error:
        _parse_labeled_paths(
            ["h-k.1-contract=tmp/a.json", "h-k.1-contract=tmp/b.json"],
            expected=("h-k.1-contract",),
            option="--stage-score",
        )
    assert error.value.code == "h_k_cli_evidence_invalid"


def test_h_k_cli_exposes_publication_catalog_audit_and_aggregate_inputs() -> None:
    options = {
        option
        for action in build_parser()._actions
        for option in action.option_strings
    }
    assert {
        "--h-j-report",
        "--publication-review",
        "--activation-report",
        "--publication-catalog",
        "--publication-manifest",
        "--publication-audit",
        "--aggregate",
        "--stage-run",
        "--stage-score",
    } <= options


def test_current_h_j_review_binds_exactly_four_content_addressed_candidates() -> None:
    evidence = validate_h_j_and_candidates(
        h_j_report_path=ROOT / "Reports/MAIN_H_J_FULL_REPORT.json",
        review_path=ROOT / "tmp/h-k-1-publication-candidates-v1/review-report.json",
    )
    assert set(evidence["candidates"]) == set(DIRECT_REUSE_CASES)
    assert all(
        row["canonical_endpoint"] == DIRECT_REUSE_CASES[case_id]
        for case_id, row in evidence["candidates"].items()
    )


def _live_call(index: int) -> dict:
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


def test_http_evidence_is_real_unique_200_and_secret_free() -> None:
    assert len(_validate_http_calls([_live_call(1), _live_call(2)], label="ok")) == 2
    with pytest.raises(HKReportError) as error:
        _validate_http_calls([_live_call(1), _live_call(1)], label="reuse")
    assert error.value.code == "h_k_deepseek_http_evidence_reused"

    failed = _live_call(3)
    failed["status_code"] = 503
    with pytest.raises(HKReportError) as error:
        _validate_http_calls([failed], label="failed")
    assert error.value.code == "h_k_deepseek_http_evidence_invalid"

    _assert_no_secret(
        {"api_key_configured": True, "api_key_or_authorization_absent": True},
        label="safe",
    )
    with pytest.raises(HKReportError) as error:
        _assert_no_secret({"authorization": "Bearer forbidden-value"}, label="bad")
    assert error.value.code == "h_k_secret_leak"


def _synthetic_catalog_tree(tmp_path: Path, monkeypatch: pytest.MonkeyPatch):
    monkeypatch.setattr(h_k_report, "ROOT", tmp_path)
    aggregate = tmp_path / "Lean/Generated/Aggregate.lean"
    aggregate.parent.mkdir(parents=True)
    candidates: dict[str, dict] = {}
    manifest_paths: list[Path] = []
    entries: list[dict] = []
    for index, (case_id, endpoint) in enumerate(DIRECT_REUSE_CASES.items(), 1):
        source_hub = f"Fixture.Source{index}"
        route = _route(source_hub, endpoint)
        candidate_id = "sha256:" + f"{100 + index:064x}"
        candidate_manifest_id = "sha256:" + f"{200 + index:064x}"
        identity_id = "sha256:" + f"{300 + index:064x}"
        candidates[case_id] = {
            "case_id": case_id,
            "canonical_identity_id": identity_id,
            "canonical_endpoint": endpoint,
            "source_hub": source_hub,
            "candidate_content_id": candidate_id,
            "candidate_manifest": {"manifest_id": candidate_manifest_id},
            "route": _route_signature(route),
        }
        root = tmp_path / f"assets/C{index}"
        root.mkdir(parents=True)
        source = root / "Reduction.lean"
        source.write_text(f"-- {case_id}\n")
        manifest = {
            "schema_version": PUBLICATION_MANIFEST_SCHEMA,
            "state": "active",
            "case_id": case_id,
            "candidate_id": candidate_id,
            "candidate_manifest_id": candidate_manifest_id,
            "canonical_identity_id": identity_id,
            "canonical_endpoint": endpoint,
            "source_hub": source_hub,
            "route": route,
            "asset": {
                "module": f"Fixture.C{index}",
                "declaration": f"Fixture.C{index}.reduction",
                "source_file": "Reduction.lean",
                "source_sha256": _hash_file(source),
            },
            "dependency_snapshot": {
                "snapshot_id": "sha256:" + f"{400 + index:064x}"
            },
            "catalog_commit": "fixture",
        }
        _seal(manifest, "publication_id")
        manifest_path = root / "manifest.json"
        _write_json(manifest_path, manifest)
        manifest_paths.append(manifest_path)
        entries.append(
            {
                "case_id": case_id,
                "publication_id": manifest["publication_id"],
                "canonical_identity_id": identity_id,
                "canonical_endpoint": endpoint,
                "status": "active",
                "superseded_by": None,
                "stale_reasons": [],
                "manifest_file": str(manifest_path.relative_to(tmp_path)),
                "manifest_sha256": _hash_file(manifest_path),
                "asset_source_sha256": _hash_file(source),
            }
        )
    aggregate.write_text(
        "".join(f"import Fixture.C{index}\n" for index in range(1, 5))
    )
    catalog = {
        "schema_version": PUBLICATION_CATALOG_SCHEMA,
        "active_publication_count": 4,
        "entries": entries,
        "aggregate": {
            "file": str(aggregate.relative_to(tmp_path)),
            "sha256": _hash_file(aggregate),
        },
    }
    _seal(catalog, "catalog_id")
    catalog_path = tmp_path / "catalog.json"
    _write_json(catalog_path, catalog)
    return candidates, catalog_path, aggregate, manifest_paths


def test_active_catalog_binds_four_manifests_sources_dependencies_and_aggregate(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    candidates, catalog_path, aggregate, manifests = _synthetic_catalog_tree(
        tmp_path, monkeypatch
    )
    evidence = validate_publication_catalog(
        catalog_path=catalog_path,
        aggregate_path=aggregate,
        manifest_paths=manifests,
        candidates=candidates,
    )
    assert evidence["catalog"]["active_publication_count"] == 4
    assert set(evidence["publications"]) == set(DIRECT_REUSE_CASES)


@pytest.mark.parametrize("mutation", ["manifest", "source", "aggregate", "dependency"])
def test_content_address_mutations_fail_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, mutation: str
) -> None:
    candidates, catalog_path, aggregate, manifests = _synthetic_catalog_tree(
        tmp_path, monkeypatch
    )
    if mutation == "manifest":
        value = json.loads(manifests[0].read_text())
        value["canonical_endpoint"] = "Fixture.WrongTarget"
        _write_json(manifests[0], value)
    elif mutation == "source":
        manifests[0].with_name("Reduction.lean").write_text("-- changed\n")
    elif mutation == "aggregate":
        aggregate.write_text("-- changed\n")
    else:
        value = json.loads(manifests[0].read_text())
        value["dependency_snapshot"] = {"snapshot_id": "not-a-hash"}
        _seal(value, "publication_id")
        _write_json(manifests[0], value)
    with pytest.raises(HKReportError):
        validate_publication_catalog(
            catalog_path=catalog_path,
            aggregate_path=aggregate,
            manifest_paths=manifests,
            candidates=candidates,
        )


def _audit() -> dict:
    audit = {
        "schema_version": PUBLICATION_AUDIT_SCHEMA,
        "passed": True,
        "clean_replay": {
            "passed": True,
            "case_count": 4,
            "passed_count": 4,
            "cases": [{"passed": True} for _ in range(4)],
        },
        "mutation_audit": {
            "passed": True,
            "audit_count": 4,
            "rejected_count": 4,
            "audits": [
                {"target_kind": kind, "rejected": True}
                for kind in ("manifest", "source", "aggregate", "dependency")
            ],
        },
        "stale_audit": {
            "passed": True,
            "audit_count": 1,
            "rejected_count": 1,
            "silent_reuse_count": 0,
            "audits": [{"rejected": True}],
        },
        "revalidation_audit": {
            "passed": True,
            "revalidated_count": 1,
            "audits": [
                {
                    "passed": True,
                    "old_publication_id": "sha256:" + "1" * 64,
                    "new_publication_id": "sha256:" + "2" * 64,
                }
            ],
        },
    }
    return _seal(audit, "audit_id")


def test_clean_replay_mutation_stale_and_revalidation_audits_are_all_required(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(h_k_report, "ROOT", tmp_path)
    path = tmp_path / "audit.json"
    _write_json(path, _audit())
    result = validate_publication_audits(
        audit_path=path, stages={"reports": []}
    )
    assert result["clean_replay_count"] == 4
    assert result["mutation_targets"] == [
        "aggregate",
        "dependency",
        "manifest",
        "source",
    ]
    assert result["silent_stale_reuse_count"] == 0
    assert result["revalidation_count"] == 1


@pytest.mark.parametrize(
    ("mutator", "code"),
    [
        (
            lambda value: value["mutation_audit"]["audits"].pop(),
            "h_k_mutation_audit_invalid",
        ),
        (
            lambda value: value["stale_audit"].update(silent_reuse_count=1),
            "h_k_stale_audit_invalid",
        ),
        (
            lambda value: value["revalidation_audit"]["audits"][0].update(
                new_publication_id="sha256:" + "1" * 64
            ),
            "h_k_revalidation_audit_invalid",
        ),
        (
            lambda value: value["clean_replay"].update(passed_count=3),
            "h_k_clean_replay_invalid",
        ),
    ],
)
def test_publication_audit_mutations_fail_closed(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    mutator,
    code: str,
) -> None:
    monkeypatch.setattr(h_k_report, "ROOT", tmp_path)
    value = _audit()
    mutator(value)
    _seal(value, "audit_id")
    path = tmp_path / "audit.json"
    _write_json(path, value)
    with pytest.raises(HKReportError) as error:
        validate_publication_audits(audit_path=path, stages={"reports": []})
    assert error.value.code == code


def _reuse_stage(stage: str, publications: dict[str, dict]) -> dict:
    run_rows: dict[str, dict] = {}
    score_rows: dict[str, dict] = {}
    for case_id, endpoint in REUSE_CASES.items():
        bucket = (
            "direct_publication_reuse"
            if case_id in DIRECT_REUSE_CASES
            else "transitive_publication_reuse"
        )
        if case_id in DIRECT_REUSE_CASES:
            route = copy.deepcopy(publications[case_id]["route"])
        else:
            route = _route("Fixture.SourceHitting", endpoint)
        run_rows[case_id] = {
            "canonical_problem": endpoint,
            "model_calls": 0,
            "public_status": "VERIFIED",
            "failure_code": None,
            "publication_bucket": bucket,
            "raw_result": {"publication_reuse": {"bucket": bucket, "route": route}},
        }
        score_rows[case_id] = {
            "model_calls": 0,
            "public_status": "VERIFIED",
            "failure_code": None,
            "capability_success": True,
            "expected_outcome_matched": True,
            "publication_bucket": bucket,
            "route_atoms": (
                [publications[case_id]["asset"]["declaration"]]
                if case_id in DIRECT_REUSE_CASES
                else [
                    publications["chld-au-07-set-covering"]["asset"][
                        "declaration"
                    ],
                    h_k_report.TRANSITIVE_CONSUMER_DECLARATION,
                ]
            ),
        }
    run_rows["remaining-real-api"] = {"model_calls": 1}
    return {
        "stage": stage,
        "run_rows": run_rows,
        "score_rows": score_rows,
        "run_object": {
            "reuse_execution": {
                "direct_count": 4,
                "transitive_count": 1,
                "zero_call_count": 5,
            }
        },
        "score_object": {
            "reuse_scorecard": {
                "direct": {
                    "case_count": 4,
                    "zero_call_count": 4,
                    "success_count": 4,
                    "zero_call_rate": 1.0,
                },
                "transitive": {
                    "case_count": 1,
                    "zero_call_count": 1,
                    "success_count": 1,
                    "zero_call_rate": 1.0,
                },
                "combined": {
                    "case_count": 5,
                    "zero_call_count": 5,
                    "success_count": 5,
                    "zero_call_rate": 1.0,
                },
            },
            "first_authoring_scorecard": {"groups": {}},
        },
    }


def test_direct_and_transitive_reuse_are_zero_call_and_route_stable() -> None:
    publications = {
        case_id: {
            "route": _route_signature(_route(f"Fixture.S{index}", endpoint)),
            "asset": {"declaration": f"Fixture.Published{index}"},
        }
        for index, (case_id, endpoint) in enumerate(DIRECT_REUSE_CASES.items())
    }
    stages = {
        "reports": [
            _reuse_stage(REUSE_STAGE_LABELS[0], publications),
            _reuse_stage(REUSE_STAGE_LABELS[1], publications),
        ]
    }
    result = validate_reuse(stages, catalog={"publications": publications})
    assert result["zero_call_count"] == 10
    assert result["zero_call_rate"] == 1.0
    assert len(result["canonical_route_fingerprints"]) == 5


def test_reuse_call_or_route_mutation_fails_closed() -> None:
    publications = {
        case_id: {
            "route": _route_signature(_route(f"Fixture.S{index}", endpoint)),
            "asset": {"declaration": f"Fixture.Published{index}"},
        }
        for index, (case_id, endpoint) in enumerate(DIRECT_REUSE_CASES.items())
    }
    first = _reuse_stage(REUSE_STAGE_LABELS[0], publications)
    second = _reuse_stage(REUSE_STAGE_LABELS[1], publications)
    first["run_rows"][next(iter(DIRECT_REUSE_CASES))]["model_calls"] = 1
    with pytest.raises(HKReportError) as error:
        validate_reuse(
            {"reports": [first, second]}, catalog={"publications": publications}
        )
    assert error.value.code == "h_k_zero_call_reuse_invalid"

    first = _reuse_stage(REUSE_STAGE_LABELS[0], publications)
    second = _reuse_stage(REUSE_STAGE_LABELS[1], publications)
    hitting = next(iter(TRANSITIVE_REUSE_CASES))
    second["score_rows"][hitting]["route_atoms"] = ["Fixture.changed"]
    with pytest.raises(HKReportError) as error:
        validate_reuse(
            {"reports": [first, second]}, catalog={"publications": publications}
        )
    assert error.value.code == "h_k_route_drift"


def test_report_content_hash_detects_mutation() -> None:
    report = {"schema_version": "fixture", "passed": True, "gates": {"x": True}}
    report["report_id"] = _canonical_content_hash(report, field="report_id")
    assert report["report_id"] == _canonical_content_hash(report, field="report_id")
    report["gates"]["x"] = False
    assert report["report_id"] != _canonical_content_hash(report, field="report_id")
