from __future__ import annotations

from agent.hardness.stage_p_candidate_validation import validate_stage_p_candidate
from agent.hardness.stage_p_fixture import build_stage_p_offline_fixture


def test_offline_fixture_is_generic_valid_and_patch_bound() -> None:
    fixture = build_stage_p_offline_fixture(17)
    fixture.request.validate()
    fixture.gap.validate(fixture.request)
    fixture.task.validate()
    fixture.candidate.validate()
    receipt = validate_stage_p_candidate(
        expectation=fixture.expectation,
        observation=fixture.observation,
    )
    session = fixture.repair_session()
    action = session.accept_model_response(fixture.submit_patch_content())
    assert action.action == "submit_patch"
    assert receipt.gap_id == fixture.gap.gap_id
    assert "p-single" not in session.build_prompt()
