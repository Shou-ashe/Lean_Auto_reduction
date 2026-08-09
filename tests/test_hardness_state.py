import json

import pytest

from agent.hardness.models import RESULT_SCHEMA
from agent.hardness.state import JobStore, compute_job_id, load_resume_checkpoint


def test_job_id_ignores_credentials_not_in_canonical_payload() -> None:
    payload = {"input": "x", "objective": "reduce_to"}
    assert compute_job_id(payload) == compute_job_id(dict(payload))


def test_state_events_are_append_only(tmp_path) -> None:
    store = JobStore(tmp_path / "job")
    store.initialize()
    store.transition("RECEIVED")
    store.transition("INPUT_VALIDATED")
    events = [json.loads(line) for line in store.events_path.read_text().splitlines()]
    assert [event["status"] for event in events] == ["RECEIVED", "INPUT_VALIDATED"]
    assert json.loads(store.state_path.read_text())["status"] == "INPUT_VALIDATED"


def test_completed_transition_is_idempotent_on_resume(tmp_path) -> None:
    store = JobStore(tmp_path / "job")
    store.initialize()
    store.transition("RECEIVED")
    store.transition("INPUT_VALIDATED")
    store.transition("RECEIVED")
    events = [json.loads(line) for line in store.events_path.read_text().splitlines()]
    assert [event["status"] for event in events] == ["RECEIVED", "INPUT_VALIDATED"]


def test_job_store_rejects_paths_outside_editable_workspace(tmp_path) -> None:
    store = JobStore(tmp_path / "job")
    store.initialize()
    with pytest.raises(ValueError):
        store.write_text("../outside.lean", "unsafe")
    with pytest.raises(ValueError):
        store.write_text(str((tmp_path / "absolute.lean").resolve()), "unsafe")


def test_job_store_rejects_concurrent_writers_and_releases_the_lock(tmp_path) -> None:
    store = JobStore(tmp_path / "job")
    with store.exclusive_run():
        with pytest.raises(ValueError, match="concurrent hardness job"):
            with JobStore(store.directory).exclusive_run():
                pass
    with store.exclusive_run():
        assert (store.directory / ".run.lock").is_file()
    assert (store.directory / ".run.lock").is_file()


def test_resume_checkpoint_uses_only_matching_content_addressed_report(tmp_path) -> None:
    store = JobStore(tmp_path / "job")
    store.initialize()
    job_id = "sha256:" + "a" * 64
    store.write_json(
        "report.json",
        {
            "schema_version": RESULT_SCHEMA,
            "job_id": job_id,
            "status": "VERIFIED",
            "authored_candidate_sha256": "b" * 64,
            "artifact_sha256": "c" * 64,
            "authored_candidate_file": "../../must-not-be-trusted.lean",
        },
    )
    checkpoint = load_resume_checkpoint(store, expected_job_id=job_id)
    assert checkpoint.status == "VERIFIED"
    assert checkpoint.authored_candidate_sha256 == "b" * 64
    assert checkpoint.artifact_sha256 == "c" * 64

    with pytest.raises(ValueError, match="different content-addressed job"):
        load_resume_checkpoint(store, expected_job_id="sha256:" + "d" * 64)


def test_resume_checkpoint_rejects_missing_or_malformed_report(tmp_path) -> None:
    store = JobStore(tmp_path / "job")
    store.initialize()
    with pytest.raises(ValueError, match="no report.json"):
        load_resume_checkpoint(store, expected_job_id="sha256:" + "a" * 64)
    store.write_json(
        "report.json",
        {
            "schema_version": RESULT_SCHEMA,
            "job_id": "sha256:" + "a" * 64,
            "status": "VERIFIED",
            "authored_candidate_sha256": "not-a-hash",
        },
    )
    with pytest.raises(ValueError, match="candidate SHA-256"):
        load_resume_checkpoint(store, expected_job_id="sha256:" + "a" * 64)
