"""Typed protocol for proof-producing finite witness synthesis plugins.

Executable checks are search filters, never proof authority.  A materialized
candidate becomes a capability only after the generic runtime independently
elaborates it with Lean and applies the normal axiom/source/route fences.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import re
from typing import Mapping, Protocol, Sequence

from .models import (
    CapabilityPlan,
    ContributionReceipt,
    GeneratorBrief,
    GeneratorResult,
    OpenGoal,
    stable_sha256,
)


@dataclass(frozen=True)
class FiniteSupportReceipt:
    plugin: str
    supported: bool
    confidence: float
    reason: str
    goal_fingerprint: str
    witness_grammar: str
    receipt_hash: str

    @classmethod
    def create(
        cls,
        *,
        plugin: str,
        goal: OpenGoal,
        supported: bool,
        confidence: float,
        reason: str,
        witness_grammar: str,
    ) -> "FiniteSupportReceipt":
        payload = {
            "plugin": plugin,
            "goal": goal.key.fingerprint,
            "supported": supported,
            "confidence": confidence,
            "reason": reason,
            "witness_grammar": witness_grammar,
        }
        return cls(
            plugin=plugin,
            supported=supported,
            confidence=max(0.0, min(1.0, confidence)),
            reason=reason,
            goal_fingerprint=goal.key.fingerprint,
            witness_grammar=witness_grammar,
            receipt_hash=stable_sha256(payload),
        )


@dataclass(frozen=True)
class FiniteCapabilityStage:
    """One independently checkable node/direction before final assembly."""

    stage_id: str
    declaration_name: str
    exact_type: str
    implementation: str
    imports: tuple[str, ...] = ()
    dependency_stage_ids: tuple[str, ...] = ()
    check_receipt: Mapping[str, object] = field(default_factory=dict)
    capability_plan: CapabilityPlan | None = None
    generator_brief: GeneratorBrief | None = None
    generator_result: GeneratorResult | None = None


@dataclass(frozen=True)
class FiniteCandidateWitness:
    witness_id: str
    implementation: str
    imports: tuple[str, ...]
    executable_status: str
    check_receipt: Mapping[str, object]
    counterexample: Mapping[str, object] | None = None
    candidate_class: str = "finite-enumeration"
    authoritative_typed_compiler: bool = False
    capability_plan: CapabilityPlan | None = None
    generator_brief: GeneratorBrief | None = None
    generator_result: GeneratorResult | None = None
    contribution_receipt: ContributionReceipt | None = None
    typed_plan_receipt: Mapping[str, object] | None = None
    stages: tuple[FiniteCapabilityStage, ...] = ()


class FiniteSynthesisPlugin(Protocol):
    name: str
    candidate_class: str
    authoritative_typed_compiler: bool

    def supports(self, goal: OpenGoal) -> FiniteSupportReceipt: ...

    def enumerate(
        self,
        goal: OpenGoal,
        *,
        declaration_name: str,
        limit: int,
        counterexamples: Sequence[Mapping[str, object]] = (),
    ) -> Sequence[FiniteCandidateWitness]: ...


_TRUTH_TABLE_COUNTEREXAMPLE = re.compile(
    r"some\s*\{\s*tuple\s*:=\s*\[(?P<tuple>[^\]]*)\],\s*"
    r"expectedRelation\s*:=\s*(?P<expected>true|false),\s*"
    r"formulaSatisfiable\s*:=\s*(?P<actual>true|false)\s*\}",
    re.DOTALL,
)


def parse_finite_counterexample_output(
    *, stdout: str, stderr: str, schema: str
) -> Mapping[str, object] | None:
    """Parse a plugin-owned `#reduce` receipt into the generic CEGIS schema."""

    if schema != "finite-truth-table-counterexample-v1":
        return None
    match = _TRUTH_TABLE_COUNTEREXAMPLE.search(stdout + "\n" + stderr)
    if match is None:
        return None
    raw_tuple = tuple(
        item.strip() for item in match.group("tuple").split(",") if item.strip()
    )
    if any(item not in {"true", "false"} for item in raw_tuple):
        return None
    return {
        "kind": "finite-truth-table-counterexample",
        "source_tuple": tuple(item == "true" for item in raw_tuple),
        "expected_source_relation_value": match.group("expected") == "true",
        "formula_satisfiability": match.group("actual") == "true",
        "schema_version": schema,
    }


__all__ = [
    "FiniteCandidateWitness",
    "FiniteCapabilityStage",
    "FiniteSupportReceipt",
    "FiniteSynthesisPlugin",
    "parse_finite_counterexample_output",
]
