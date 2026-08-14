"""Typed control data for the NP-hard-first research core.

These records describe Lean-checked search observations.  They are never proof
objects: successful results always point at a standalone Lean artifact.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass, field
from typing import Any


ROOT_GOAL_HEAD = "ComplexityReduction.Certificate.NativeTMNPHard"


@dataclass(frozen=True)
class SearchBudget:
    max_search_depth: int = 6
    max_expanded_states: int = 128
    max_candidates_per_goal: int = 16
    max_lean_checks: int = 48
    max_model_calls: int = 2
    max_synthesis_rounds: int = 2
    wall_clock_timeout_seconds: int = 600

    def validate(self) -> None:
        for name, value in asdict(self).items():
            if not isinstance(value, int) or value < 0:
                raise ValueError(f"{name} must be a non-negative integer")
        if self.max_search_depth == 0 or self.max_candidates_per_goal == 0:
            raise ValueError("search depth and candidate count must be positive")


@dataclass(frozen=True)
class RootGoal:
    input_module: str
    problem_declaration: str
    proposition: str
    endpoint_fingerprint: str

    @classmethod
    def for_problem(
        cls, *, input_module: str, problem_declaration: str, endpoint_fingerprint: str
    ) -> "RootGoal":
        return cls(
            input_module=input_module,
            problem_declaration=problem_declaration,
            proposition=f"{ROOT_GOAL_HEAD} {problem_declaration}",
            endpoint_fingerprint=endpoint_fingerprint,
        )


@dataclass(frozen=True)
class TheoremCandidate:
    declaration: str
    module: str
    premise_count: int
    declaration_type: str
    premises: tuple[str, ...]
    result_type: str
    result_fingerprint: str

    @property
    def is_schaefer_schema(self) -> bool:
        return (
            self.premise_count == 2
            and any(".Nonempty" in premise for premise in self.premises)
            and any("IsSchaeferTractable" in premise for premise in self.premises)
        )


@dataclass(frozen=True)
class ProofStep:
    action: str
    goal: str
    declaration: str | None = None
    solver: str | None = None
    status: str = "verified"


@dataclass(frozen=True)
class ModelCallRecord:
    purpose: str
    called: bool
    ok: bool
    status_code: int | None
    duration_seconds: float
    usage: dict[str, Any] | None
    attempts: int
    response_sha256: str
    selected_candidate_id: str | None = None
    error: str | None = None


@dataclass
class ReductionResult:
    status: str
    profile: str
    root_goal: RootGoal
    output_dir: str
    failure_code: str | None = None
    explanation: str | None = None
    artifact_file: str | None = None
    artifact_sha256: str | None = None
    theorem_candidates: tuple[TheoremCandidate, ...] = ()
    selected_theorem: str | None = None
    selected_theorem_module: str | None = None
    proof_tree: tuple[ProofStep, ...] = ()
    commands: tuple[dict[str, Any], ...] = ()
    model_calls: tuple[ModelCallRecord, ...] = ()
    input_identity: dict[str, Any] | None = None
    deterministic_result: dict[str, Any] | None = None
    exact_type_verified: bool = False
    kernel_verified: bool = False
    axiom_audit_passed: bool = False
    independent_replay_passed: bool = False
    endpoint_equality_audit_passed: bool = False
    schema_version: str = "np_hard_reduction_result_v1"

    @property
    def verified(self) -> bool:
        return self.status == "VERIFIED" and self.kernel_verified

    @property
    def model_call_count(self) -> int:
        return sum(record.called for record in self.model_calls)

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "status": self.status,
            "profile": self.profile,
            "root_goal": asdict(self.root_goal),
            "output_dir": self.output_dir,
            "failure_code": self.failure_code,
            "explanation": self.explanation,
            "artifact_file": self.artifact_file,
            "artifact_sha256": self.artifact_sha256,
            "theorem_candidates": [asdict(candidate) for candidate in self.theorem_candidates],
            "selected_theorem": self.selected_theorem,
            "selected_theorem_module": self.selected_theorem_module,
            "proof_tree": [asdict(step) for step in self.proof_tree],
            "commands": list(self.commands),
            "model_calls": [asdict(record) for record in self.model_calls],
            "model_call_count": self.model_call_count,
            "input_identity": self.input_identity,
            "deterministic_result": self.deterministic_result,
            "exact_type_verified": self.exact_type_verified,
            "kernel_verified": self.kernel_verified,
            "axiom_audit_passed": self.axiom_audit_passed,
            "independent_replay_passed": self.independent_replay_passed,
            "endpoint_equality_audit_passed": self.endpoint_equality_audit_passed,
            "trust_boundary": {
                "python_and_model_are_observational": True,
                "external_model_payload": "opaque-candidate-metadata-only",
                "typed_unification_runs_in_lean": True,
                "final_authority": "lean-kernel",
                "forbidden_placeholders": True,
            },
        }


@dataclass
class SearchTrace:
    candidates: list[TheoremCandidate] = field(default_factory=list)
    steps: list[ProofStep] = field(default_factory=list)
    commands: list[dict[str, Any]] = field(default_factory=list)
    model_calls: list[ModelCallRecord] = field(default_factory=list)
