"""Versioned, observational plans for general hardness automation.

The core schema is intentionally objective- and backend-neutral.  Concrete
benchmark or execution profiles may restrict action kinds and outputs, but
those restrictions do not become limitations of the Agent's persistent plan.
Nothing in this module grants Lean proof authority.
"""

from __future__ import annotations

import json
import re
from collections.abc import Mapping
from dataclasses import dataclass, field
from typing import Any

from .models import sha256_id


PLAN_SCHEMA = "hardness_plan_v1"
PLAN_STEP_SCHEMA = "hardness_plan_step_v1"
PLAN_OUTPUT_SCHEMA = "hardness_plan_output_v1"

LOCAL_ID_RE = re.compile(r"[A-Za-z][A-Za-z0-9_.-]*")
KIND_RE = re.compile(r"[a-z][a-z0-9_.-]*")


class PlanValidationError(ValueError):
    """A structural or versioning hardness-plan rejection."""


def _json_copy(value: Any, *, label: str) -> Any:
    try:
        return json.loads(json.dumps(value, ensure_ascii=True, sort_keys=True))
    except (TypeError, ValueError) as error:
        raise PlanValidationError(f"{label} must be JSON-serializable") from error


def _required_string(raw: Mapping[str, Any], key: str, *, label: str) -> str:
    value = raw.get(key)
    if not isinstance(value, str) or not value.strip():
        raise PlanValidationError(f"{label}.{key} must be a non-empty string")
    return value.strip()


def _optional_string(raw: Mapping[str, Any], key: str, *, label: str) -> str | None:
    value = raw.get(key)
    if value is None:
        return None
    if not isinstance(value, str) or not value.strip():
        raise PlanValidationError(f"{label}.{key} must be null or a non-empty string")
    return value.strip()


def _string_tuple(raw: Mapping[str, Any], key: str, *, label: str) -> tuple[str, ...]:
    value = raw.get(key, [])
    if not isinstance(value, list) or any(
        not isinstance(item, str) or not item.strip() for item in value
    ):
        raise PlanValidationError(f"{label}.{key} must be a string list")
    return tuple(item.strip() for item in value)


def _mapping(raw: Mapping[str, Any], key: str, *, label: str) -> dict[str, Any]:
    value = raw.get(key, {})
    if not isinstance(value, dict):
        raise PlanValidationError(f"{label}.{key} must be an object")
    return _json_copy(value, label=f"{label}.{key}")


def _validate_schema(
    raw: Mapping[str, Any], *, expected: str, label: str
) -> None:
    schema = raw.get("schema_version", expected)
    if schema != expected:
        raise PlanValidationError(
            f"unsupported {label} schema: {schema!r}; expected {expected!r}"
        )


@dataclass(frozen=True)
class PlanStep:
    """One dependency-aware semantic action in a hardness plan.

    ``action_kind`` is namespaced but deliberately open.  Examples include
    ``reuse.certified_reduction``, ``reuse.certified_equiv``,
    ``instantiate.family``, ``evidence.native_membership``, and
    ``author.local_lemma``.  Profiles decide which kinds they can execute.
    """

    step_id: str
    action_kind: str
    capability_kind: str | None = None
    declaration: str | None = None
    argument_declarations: tuple[str, ...] = ()
    depends_on: tuple[str, ...] = ()
    input_handles: tuple[str, ...] = ()
    output_handles: tuple[str, ...] = ()
    role: str | None = None
    source_fingerprint: str | None = None
    target_fingerprint: str | None = None
    expected_type: str | None = None
    parameters: Mapping[str, Any] = field(default_factory=dict)
    extensions: Mapping[str, Any] = field(default_factory=dict)
    schema_version: str = PLAN_STEP_SCHEMA

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "step_id": self.step_id,
            "action_kind": self.action_kind,
            "capability_kind": self.capability_kind,
            "declaration": self.declaration,
            "argument_declarations": list(self.argument_declarations),
            "depends_on": list(self.depends_on),
            "input_handles": list(self.input_handles),
            "output_handles": list(self.output_handles),
            "role": self.role,
            "source_fingerprint": self.source_fingerprint,
            "target_fingerprint": self.target_fingerprint,
            "expected_type": self.expected_type,
            "parameters": _json_copy(self.parameters, label="step.parameters"),
            "extensions": _json_copy(self.extensions, label="step.extensions"),
        }


@dataclass(frozen=True)
class PlanOutput:
    """A requested backend artifact or evidence product of one or more steps."""

    output_id: str
    output_kind: str
    producer_steps: tuple[str, ...]
    expected_type: str | None = None
    lean_code: str | None = None
    declaration_name: str | None = None
    metadata: Mapping[str, Any] = field(default_factory=dict)
    extensions: Mapping[str, Any] = field(default_factory=dict)
    schema_version: str = PLAN_OUTPUT_SCHEMA

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "output_id": self.output_id,
            "output_kind": self.output_kind,
            "producer_steps": list(self.producer_steps),
            "expected_type": self.expected_type,
            "lean_code": self.lean_code,
            "declaration_name": self.declaration_name,
            "metadata": _json_copy(self.metadata, label="output.metadata"),
            "extensions": _json_copy(self.extensions, label="output.extensions"),
        }


@dataclass(frozen=True)
class HardnessPlan:
    """A general, non-authoritative plan from a hardness goal to backend outputs."""

    objective: str
    source_declaration: str
    target_declaration: str | None
    steps: tuple[PlanStep, ...]
    outputs: tuple[PlanOutput, ...]
    registry_fingerprint: str | None = None
    catalog_id: str | None = None
    problem_catalog_id: str | None = None
    connection_catalog_id: str | None = None
    goal_id: str | None = None
    matched_problem_declaration: str | None = None
    problem_match: Mapping[str, Any] = field(default_factory=dict)
    target_evidence: Mapping[str, Any] = field(default_factory=dict)
    metadata: Mapping[str, Any] = field(default_factory=dict)
    extensions: Mapping[str, Any] = field(default_factory=dict)
    schema_version: str = PLAN_SCHEMA

    @property
    def plan_id(self) -> str:
        return sha256_id(self.to_dict(include_plan_id=False))

    def to_dict(self, *, include_plan_id: bool = True) -> dict[str, Any]:
        value = {
            "schema_version": self.schema_version,
            "objective": self.objective,
            "source_declaration": self.source_declaration,
            "target_declaration": self.target_declaration,
            "registry_fingerprint": self.registry_fingerprint,
            "catalog_id": self.catalog_id,
            "problem_catalog_id": self.problem_catalog_id,
            "connection_catalog_id": self.connection_catalog_id,
            "goal_id": self.goal_id,
            "matched_problem_declaration": self.matched_problem_declaration,
            "problem_match": _json_copy(
                self.problem_match, label="plan.problem_match"
            ),
            "target_evidence": _json_copy(
                self.target_evidence, label="plan.target_evidence"
            ),
            "steps": [step.to_dict() for step in self.steps],
            "outputs": [output.to_dict() for output in self.outputs],
            "metadata": _json_copy(self.metadata, label="plan.metadata"),
            "extensions": _json_copy(self.extensions, label="plan.extensions"),
        }
        if include_plan_id:
            value["plan_id"] = self.plan_id
        return value


def _parse_step(value: Any, *, index: int) -> PlanStep:
    if not isinstance(value, dict):
        raise PlanValidationError(f"plan.steps[{index}] must be an object")
    label = f"plan.steps[{index}]"
    _validate_schema(value, expected=PLAN_STEP_SCHEMA, label=label)
    step_id = _required_string(value, "step_id", label=label)
    action_kind = _required_string(value, "action_kind", label=label)
    if not LOCAL_ID_RE.fullmatch(step_id):
        raise PlanValidationError(f"{label}.step_id is not a valid local identifier")
    if not KIND_RE.fullmatch(action_kind):
        raise PlanValidationError(f"{label}.action_kind is not a valid namespaced kind")
    known = {
        "schema_version",
        "step_id",
        "action_kind",
        "capability_kind",
        "declaration",
        "argument_declarations",
        "depends_on",
        "input_handles",
        "output_handles",
        "role",
        "source_fingerprint",
        "target_fingerprint",
        "expected_type",
        "parameters",
        "extensions",
    }
    extensions = _mapping(value, "extensions", label=label)
    extensions.update(
        _json_copy(
            {key: item for key, item in value.items() if key not in known},
            label=f"{label}.unknown_fields",
        )
    )
    return PlanStep(
        step_id=step_id,
        action_kind=action_kind,
        capability_kind=_optional_string(value, "capability_kind", label=label),
        declaration=_optional_string(value, "declaration", label=label),
        argument_declarations=_string_tuple(
            value, "argument_declarations", label=label
        ),
        depends_on=_string_tuple(value, "depends_on", label=label),
        input_handles=_string_tuple(value, "input_handles", label=label),
        output_handles=_string_tuple(value, "output_handles", label=label),
        role=_optional_string(value, "role", label=label),
        source_fingerprint=_optional_string(
            value, "source_fingerprint", label=label
        ),
        target_fingerprint=_optional_string(
            value, "target_fingerprint", label=label
        ),
        expected_type=_optional_string(value, "expected_type", label=label),
        parameters=_mapping(value, "parameters", label=label),
        extensions=extensions,
    )


def _parse_output(value: Any, *, index: int) -> PlanOutput:
    if not isinstance(value, dict):
        raise PlanValidationError(f"plan.outputs[{index}] must be an object")
    label = f"plan.outputs[{index}]"
    _validate_schema(value, expected=PLAN_OUTPUT_SCHEMA, label=label)
    output_id = _required_string(value, "output_id", label=label)
    output_kind = _required_string(value, "output_kind", label=label)
    if not LOCAL_ID_RE.fullmatch(output_id):
        raise PlanValidationError(f"{label}.output_id is not a valid local identifier")
    if not KIND_RE.fullmatch(output_kind):
        raise PlanValidationError(f"{label}.output_kind is not a valid namespaced kind")
    known = {
        "schema_version",
        "output_id",
        "output_kind",
        "producer_steps",
        "expected_type",
        "lean_code",
        "declaration_name",
        "metadata",
        "extensions",
    }
    extensions = _mapping(value, "extensions", label=label)
    extensions.update(
        _json_copy(
            {key: item for key, item in value.items() if key not in known},
            label=f"{label}.unknown_fields",
        )
    )
    return PlanOutput(
        output_id=output_id,
        output_kind=output_kind,
        producer_steps=_string_tuple(value, "producer_steps", label=label),
        expected_type=_optional_string(value, "expected_type", label=label),
        lean_code=_optional_string(value, "lean_code", label=label),
        declaration_name=_optional_string(value, "declaration_name", label=label),
        metadata=_mapping(value, "metadata", label=label),
        extensions=extensions,
    )


def parse_hardness_plan(value: Any) -> HardnessPlan:
    """Parse and structurally validate the open hardness-plan schema."""

    if not isinstance(value, dict):
        raise PlanValidationError("plan must be an object")
    _validate_schema(value, expected=PLAN_SCHEMA, label="plan")
    raw_steps = value.get("steps")
    raw_outputs = value.get("outputs")
    if not isinstance(raw_steps, list):
        raise PlanValidationError("plan.steps must be a list")
    if not isinstance(raw_outputs, list):
        raise PlanValidationError("plan.outputs must be a list")
    steps = tuple(_parse_step(item, index=index) for index, item in enumerate(raw_steps))
    outputs = tuple(
        _parse_output(item, index=index) for index, item in enumerate(raw_outputs)
    )
    known = {
        "schema_version",
        "plan_id",
        "objective",
        "source_declaration",
        "target_declaration",
        "registry_fingerprint",
        "catalog_id",
        "problem_catalog_id",
        "connection_catalog_id",
        "goal_id",
        "matched_problem_declaration",
        "problem_match",
        "target_evidence",
        "steps",
        "outputs",
        "metadata",
        "extensions",
    }
    extensions = _mapping(value, "extensions", label="plan")
    extensions.update(
        _json_copy(
            {key: item for key, item in value.items() if key not in known},
            label="plan.unknown_fields",
        )
    )
    plan = HardnessPlan(
        objective=_required_string(value, "objective", label="plan"),
        source_declaration=_required_string(
            value, "source_declaration", label="plan"
        ),
        target_declaration=_optional_string(
            value, "target_declaration", label="plan"
        ),
        registry_fingerprint=_optional_string(
            value, "registry_fingerprint", label="plan"
        ),
        catalog_id=_optional_string(value, "catalog_id", label="plan"),
        problem_catalog_id=_optional_string(
            value, "problem_catalog_id", label="plan"
        ),
        connection_catalog_id=_optional_string(
            value, "connection_catalog_id", label="plan"
        ),
        goal_id=_optional_string(value, "goal_id", label="plan"),
        matched_problem_declaration=_optional_string(
            value, "matched_problem_declaration", label="plan"
        ),
        problem_match=_mapping(value, "problem_match", label="plan"),
        target_evidence=_mapping(value, "target_evidence", label="plan"),
        steps=steps,
        outputs=outputs,
        metadata=_mapping(value, "metadata", label="plan"),
        extensions=extensions,
    )
    _validate_plan_graph(plan)
    supplied_plan_id = value.get("plan_id")
    if supplied_plan_id is not None:
        if not isinstance(supplied_plan_id, str) or not supplied_plan_id:
            raise PlanValidationError("plan.plan_id must be a non-empty string")
        if supplied_plan_id != plan.plan_id:
            raise PlanValidationError("plan.plan_id does not match normalized content")
    return plan


def _validate_plan_graph(plan: HardnessPlan) -> None:
    step_ids = [step.step_id for step in plan.steps]
    if len(step_ids) != len(set(step_ids)):
        raise PlanValidationError("plan step IDs must be unique")
    output_ids = [output.output_id for output in plan.outputs]
    if len(output_ids) != len(set(output_ids)):
        raise PlanValidationError("plan output IDs must be unique")
    known_steps = set(step_ids)
    dependencies = {step.step_id: set(step.depends_on) for step in plan.steps}
    for step in plan.steps:
        if len(step.depends_on) != len(set(step.depends_on)):
            raise PlanValidationError(
                f"plan step {step.step_id} repeats a dependency"
            )
    for step_id, required in dependencies.items():
        if step_id in required:
            raise PlanValidationError(f"plan step {step_id} depends on itself")
        unknown = required - known_steps
        if unknown:
            raise PlanValidationError(
                f"plan step {step_id} has unknown dependencies: {sorted(unknown)}"
            )
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(step_id: str) -> None:
        if step_id in visited:
            return
        if step_id in visiting:
            raise PlanValidationError("plan step dependency graph contains a cycle")
        visiting.add(step_id)
        for dependency in dependencies[step_id]:
            visit(dependency)
        visiting.remove(step_id)
        visited.add(step_id)

    for step_id in step_ids:
        visit(step_id)
    for output in plan.outputs:
        if len(output.producer_steps) != len(set(output.producer_steps)):
            raise PlanValidationError(
                f"plan output {output.output_id} repeats a producer"
            )
        unknown = set(output.producer_steps) - known_steps
        if unknown:
            raise PlanValidationError(
                f"plan output {output.output_id} has unknown producers: {sorted(unknown)}"
            )
