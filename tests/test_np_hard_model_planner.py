from __future__ import annotations

import json

from agent.hardness.model_client import ModelResponse
from agent.reduction.model_planner import choose_candidate, confirm_existing_route
from agent.reduction.models import TheoremCandidate


class FakeModel:
    def __init__(self, payload: dict[str, object]):
        self.payload = payload
        self.calls = 0
        self.prompts: list[str] = []

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        self.calls += 1
        self.prompts.append(prompt)
        return ModelResponse(
            called=True,
            ok=True,
            content=json.dumps(self.payload),
            error=None,
            status_code=200,
            duration_seconds=0.01,
            usage={"total_tokens": 7},
            attempts=1,
        )


def _candidate() -> TheoremCandidate:
    return TheoremCandidate(
        declaration="Example.Rules.hard",
        module="Example.Rules",
        premise_count=0,
        declaration_type="NativeTMNPHard target",
        premises=(),
        result_type="NativeTMNPHard Example.problem",
        result_fingerprint="lean:example",
    )


def test_model_can_only_select_a_lean_indexed_declaration() -> None:
    model = FakeModel(
        {"action": "select_candidate", "candidate_id": "candidate-999", "reason": "x"}
    )
    selected, record = choose_candidate(
        model=model,
        goal="NativeTMNPHard Example.problem",
        candidates=(_candidate(),),
        failures=(),
    )
    assert selected is None
    assert record.called is True
    assert record.ok is False
    assert "outside" in record.error
    assert "Example.Rules.hard" not in model.prompts[0]
    assert "NativeTMNPHard Example.problem" not in model.prompts[0]


def test_required_fast_path_review_is_observational() -> None:
    model = FakeModel(
        {
            "action": "select_candidate",
            "candidate_id": "existing-route",
            "reason": "Lean resolved it",
        }
    )
    record = confirm_existing_route(
        model=model,
        goal="NativeTMNPHard Example.problem",
        resolver_result={"evidence_kind": "registered_hardness"},
    )
    assert model.calls == 1
    assert record.called is record.ok is True
    assert record.selected_candidate_id == "existing-route"
    assert "registered_hardness" not in model.prompts[0]
    assert "Example.problem" not in model.prompts[0]
