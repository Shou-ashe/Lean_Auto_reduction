import json
from types import SimpleNamespace

from scripts.run_hardness_benchmark import _case_result, _remove_job_local_candidate


def test_candidate_removal_receipt_moves_source_and_stale_olean(tmp_path) -> None:
    output_dir = tmp_path / "job"
    module = "Generated.Hardness.J1234567890abcdef.ClosedFamily"
    module_path = output_dir / "work" / "Generated" / "Hardness" / "J1234567890abcdef"
    module_path.mkdir(parents=True)
    source = module_path / "ClosedFamily.lean"
    olean = module_path / "ClosedFamily.olean"
    source.write_text("candidate\n", encoding="utf-8")
    olean.write_bytes(b"olean")

    receipt_path, backup_source = _remove_job_local_candidate(
        output_dir=output_dir,
        candidate_module=module,
    )

    assert not source.exists()
    assert not olean.exists()
    assert backup_source.read_text(encoding="utf-8") == "candidate\n"
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    assert receipt["source_absent"] is True
    assert receipt["olean_absent"] is True
    assert receipt["backup_olean"] is not None


def test_resume_coverage_requires_verified_missing_candidate_checkpoint() -> None:
    expected = SimpleNamespace(
        final_status="BLOCKED",
        final_failure_code="unresolved_family_premise",
    )
    case = SimpleNamespace(
        id="resume-audit",
        suite_id="authoring",
        group_id="group",
        objective="reduce_to",
        expected=expected,
        coverage={"require_resume_candidate_invalidation": True},
        is_positive=False,
        requires_authoring=False,
    )
    gap = SimpleNamespace(
        reason="unresolvedFamilyPremise",
        expected_capability_head="FamilyObservation",
        failure_code="unresolved_family_premise",
        gap_id="sha256:gap",
    )
    failure = SimpleNamespace(code="unresolved_family_premise")
    result = SimpleNamespace(
        failures=[failure],
        status="BLOCKED",
        selected_route=None,
        gap=gap,
        authoring_task=None,
        authoring_attempts=[],
        authored_candidate_file=None,
        authored_candidate_declaration=None,
        authored_candidate_module=None,
        authored_route_declaration=None,
        authored_capability_head=None,
        resume_requested=True,
        resumed_from_status="VERIFIED",
        resume_candidate_integrity="missing",
        commands=[],
        planner=None,
        report_file="report.json",
    )

    row = _case_result(case, result, planner="deterministic")
    assert row["passed"] is True
    assert row["coverage_failures"] == []

    result.resume_candidate_integrity = "changed"
    changed = _case_result(case, result, planner="deterministic")
    assert changed["passed"] is False
    assert changed["coverage_failures"] == [
        "resume did not observe the job-local candidate as missing"
    ]
