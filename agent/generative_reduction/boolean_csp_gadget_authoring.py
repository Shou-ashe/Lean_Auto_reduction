"""Answer-free structured authoring protocol for explicit Boolean-CSP gadgets.

The module deliberately exposes no gadget search or candidate enumeration API.
It performs five deterministic, validation-only operations:

* build public source/target truth-table context for one benchmark case;
* validate one model-supplied ``BooleanCSPGadgetPlanV1``;
* hash the plan's canonical semantic payload;
* check that one supplied plan against the public finite truth tables; and
* serialize that payload one-for-one into a Lean ``Spec.toGadget`` proof.

Truth tables below are public benchmark inputs, not oracle answers.  The
renderer never adds, chooses, or repairs a mathematical constraint.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, Mapping, Sequence
import re

from .models import stable_sha256


GADGET_PLAN_SCHEMA = "boolean_csp_gadget_plan_v1"
GADGET_AUTHORING_BRIEF_SCHEMA = "boolean_csp_gadget_authoring_brief_v1"
GADGET_AUTHORING_RECEIPT_SCHEMA = "boolean_csp_gadget_authoring_receipt_v3"
GADGET_AUTHORING_GENERATOR_NAME = "boolean-csp-gadget-authoring-generator"
GADGET_AUTHORING_GENERATOR_VERSION = "boolean-csp-gadget-authoring-generator-v3"
GADGET_RENDERER_NAME = "render-boolean-csp-gadget-plan"
GADGET_RENDERER_VERSION = "render-boolean-csp-gadget-plan-v1"
GADGET_SEMANTIC_CHECK_RECEIPT_SCHEMA = (
    "boolean_csp_gadget_semantic_check_receipt_v1"
)
GADGET_SEMANTIC_CHECKER_NAME = "check-explicit-boolean-csp-gadget-plan"
GADGET_SEMANTIC_CHECKER_VERSION = (
    "check-explicit-boolean-csp-gadget-plan-v1"
)
GADGET_TRUTH_TABLE_CONTEXT_VERSION = "boolean-csp-public-truth-tables-v1"

HARDNESS = "ComplexityReduction.Domain.BooleanCSP.Hardness"
FINITE_GADGET = (
    "ComplexityReduction.Agent.GenerativeReduction.Plugins."
    "BooleanCSPFiniteGadget"
)
COMMON = "Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common"
ONE_IN_THREE_CORE = HARDNESS + ".oneInThreeCore"
NAE3_CORE = HARDNESS + ".nae3Core"
GADGET_AUTHORING_ALLOWED_SOURCE_CORES = (ONE_IN_THREE_CORE, NAE3_CORE)
GADGET = HARDNESS + ".Gadget"
INTERPRETATION = HARDNESS + ".LanguageInterpretation"

PP_DEFINITION_SEMANTICS = (
    "For every Boolean tuple on the source relation's output coordinates, the "
    "source relation holds if and only if there exists an assignment to all "
    "declared variables that agrees with those outputs and satisfies every "
    "listed target-language constraint. Repeated variables inside a constraint "
    "are allowed; output coordinates must be pairwise distinct."
)

SPEC_CORRECT_DEFINITION = (
    "def Spec.Correct (spec : Spec Gamma relation variableCount) : Prop := "
    "forall tuple : BooleanTuple relation.arity, relation.Holds tuple iff "
    "exists assignment : Fin variableCount -> Bool, "
    "spec.formula.Satisfies assignment and "
    "forall index, assignment (spec.outputs index) = tuple index"
)


class BooleanCSPGadgetProtocolError(ValueError):
    """A stable protocol/validation failure suitable for repair feedback."""

    def __init__(self, code: str, message: str):
        super().__init__(message)
        self.code = code
        self.message = message

    def to_dict(self) -> dict[str, str]:
        return {"code": self.code, "message": self.message}


def _tuple_for_index(index: int, arity: int) -> tuple[bool, ...]:
    return tuple(
        bool(index & (1 << (arity - coordinate - 1)))
        for coordinate in range(arity)
    )


def _mask_from_predicate(
    arity: int, predicate: Callable[[tuple[bool, ...]], bool]
) -> int:
    mask = 0
    for index in range(1 << arity):
        if predicate(_tuple_for_index(index, arity)):
            mask |= 1 << index
    return mask


def _exactly(arity: int, count: int) -> tuple[int, int]:
    return arity, _mask_from_predicate(arity, lambda row: sum(row) == count)


def _nae(arity: int) -> tuple[int, int]:
    return arity, _mask_from_predicate(
        arity, lambda row: any(bit != row[0] for bit in row[1:])
    )


_EXACT_CASES = {
    "q-b04-positive-exactly-one3": (3, 1),
    "q-b07-positive-exactly-two3": (3, 2),
    "q-b08-positive-exactly-one4": (4, 1),
    "q-b09-positive-exactly-two4": (4, 2),
    "q-b10-positive-exactly-three4": (4, 3),
    "q-b11-positive-exactly-one5": (5, 1),
    "q-b12-positive-exactly-two5": (5, 2),
    "q-b13-positive-exactly-three5": (5, 3),
    "q-b14-positive-exactly-four5": (5, 4),
    "q-b15-positive-exactly-one6": (6, 1),
    "q-b16-positive-exactly-two6": (6, 2),
    "q-b17-positive-exactly-three6": (6, 3),
    "q-b18-positive-exactly-four6": (6, 4),
    "q-b19-positive-exactly-five6": (6, 5),
}

_RANDOM_CASES = {
    "q-b21-random-table-a": ((4, 0x14E4),),
    "q-b22-random-table-b": ((5, 0x5AE4ED46),),
    "q-b23-random-table-c": ((4, 0x6890),),
    "q-b24-random-table-d": ((5, 0x6C2A2F22),),
    "q-b25-random-table-e": ((4, 0x69C6),),
    "q-b26-random-table-f": ((3, 0x21), (3, 0xE6)),
    "q-b27-random-table-g": ((3, 0x71), (4, 0x8CF8)),
    "q-b28-random-table-h": ((4, 0x6AC7), (4, 0x96E2)),
    "q-b29-random-table-i": ((4, 0x0C39), (5, 0x8DF51404)),
    "q-b30-random-table-j": ((5, 0x64ADBF05), (3, 0xCA)),
}

_DEV_CASES = {
    "ga-dev-random-hard4": ((4, 0x135E),),
    "ga-dev-dual-exactly-five7": (_exactly(7, 5),),
    "ga-dev-mixed-nand2-or3": ((2, 0x7), (3, 0xFE)),
}


@dataclass(frozen=True)
class BooleanRelationTruthTable:
    symbol_id: str
    lean_symbol_term: str
    lean_symbol_type: str
    arity: int
    mask: int

    def __post_init__(self) -> None:
        if self.arity < 1:
            raise ValueError("relation arity must be positive")
        if self.mask < 0 or self.mask >= 1 << (1 << self.arity):
            raise ValueError("truth-table mask does not fit relation arity")

    @property
    def values(self) -> tuple[bool, ...]:
        return tuple(
            bool(self.mask & (1 << index)) for index in range(1 << self.arity)
        )

    def holds(self, row: Sequence[bool]) -> bool:
        if len(row) != self.arity:
            raise ValueError("truth-table row arity mismatch")
        index = 0
        for bit in row:
            index = index * 2 + int(bool(bit))
        return bool(self.mask & (1 << index))

    def prompt_dict(self) -> dict[str, Any]:
        rows = [
            {
                "row_index": index,
                "tuple": list(_tuple_for_index(index, self.arity)),
                "holds": value,
            }
            for index, value in enumerate(self.values)
        ]
        return {
            "symbol_id": self.symbol_id,
            "arity": self.arity,
            "rows": rows,
            "truth_table_sha256": stable_sha256(rows),
        }


@dataclass(frozen=True)
class BooleanGammaTruthTable:
    handle: str
    constructor_declaration: str
    relations: tuple[BooleanRelationTruthTable, ...]

    def __post_init__(self) -> None:
        if not self.relations:
            raise ValueError("Gamma truth table needs at least one relation")
        ids = tuple(relation.symbol_id for relation in self.relations)
        if len(ids) != len(set(ids)):
            raise ValueError("Gamma truth table repeats a symbol ID")

    @property
    def by_symbol_id(self) -> dict[str, BooleanRelationTruthTable]:
        return {relation.symbol_id: relation for relation in self.relations}

    def prompt_dict(self) -> dict[str, Any]:
        payload = {
            "handle": self.handle,
            "symbols": [relation.prompt_dict() for relation in self.relations],
        }
        return {**payload, "truth_table_sha256": stable_sha256(payload)}


@dataclass(frozen=True)
class BooleanCSPGadgetContext:
    case_id: str
    input_module: str
    exact_goal: str
    pointwise: bool
    source_core: str
    source: BooleanGammaTruthTable
    target: BooleanGammaTruthTable
    policy_sha256: str
    max_variable_count: int
    max_constraint_count: int
    context_sha256: str

    @classmethod
    def create(
        cls,
        *,
        case_id: str,
        input_module: str,
        exact_goal: str,
        policy_sha256: str,
        max_variable_count: int,
        max_constraint_count: int,
    ) -> "BooleanCSPGadgetContext":
        endpoints = gadget_endpoints(exact_goal)
        if endpoints is None:
            raise BooleanCSPGadgetProtocolError(
                "unsupported_gadget_goal",
                "exact goal is not a supported Gadget/LanguageInterpretation type",
            )
        source_handle, target_handle, pointwise = endpoints
        expected_target = input_module + ".gamma"
        if target_handle != expected_target:
            raise BooleanCSPGadgetProtocolError(
                "target_gamma_mismatch",
                f"gadget target {target_handle!r} differs from case target "
                f"{expected_target!r}",
            )
        source_core, source = _source_table(source_handle)
        target = _target_table(case_id, target_handle)
        payload = {
            "schema_version": GADGET_TRUTH_TABLE_CONTEXT_VERSION,
            "case_id": case_id,
            "input_module": input_module,
            "exact_goal": " ".join(exact_goal.split()),
            "pointwise": pointwise,
            "source_core": source_core,
            "source": source.prompt_dict(),
            "target": target.prompt_dict(),
            "policy_sha256": policy_sha256,
            "max_variable_count": max_variable_count,
            "max_constraint_count": max_constraint_count,
        }
        return cls(
            case_id=case_id,
            input_module=input_module,
            exact_goal=exact_goal,
            pointwise=pointwise,
            source_core=source_core,
            source=source,
            target=target,
            policy_sha256=policy_sha256,
            max_variable_count=max_variable_count,
            max_constraint_count=max_constraint_count,
            context_sha256=stable_sha256(payload),
        )

    def prompt_dict(self) -> dict[str, Any]:
        return {
            "schema_version": GADGET_TRUTH_TABLE_CONTEXT_VERSION,
            "case_id": self.case_id,
            "input_module": self.input_module,
            "exact_goal": " ".join(self.exact_goal.split()),
            "pointwise": self.pointwise,
            "source_core": self.source_core,
            "source": self.source.prompt_dict(),
            "target": self.target.prompt_dict(),
            "policy_sha256": self.policy_sha256,
            "resource_limits": {
                "max_variable_count": self.max_variable_count,
                "max_constraint_count_per_gadget": self.max_constraint_count,
            },
            "context_sha256": self.context_sha256,
        }


def _source_table(handle: str) -> tuple[str, BooleanGammaTruthTable]:
    if handle == ONE_IN_THREE_CORE:
        arity, mask = _exactly(3, 1)
        core = "one_in_three3"
    elif handle == NAE3_CORE:
        arity, mask = _nae(3)
        core = "nae3"
    else:
        raise BooleanCSPGadgetProtocolError(
            "source_core_not_allowed", f"unsupported source core: {handle}"
        )
    relation = BooleanRelationTruthTable("source-0", "()", "Unit", arity, mask)
    return core, BooleanGammaTruthTable(handle, handle, (relation,))


def _target_specs(case_id: str) -> tuple[tuple[int, int], ...]:
    if case_id in _EXACT_CASES:
        return (_exactly(*_EXACT_CASES[case_id]),)
    if case_id in _RANDOM_CASES:
        return _RANDOM_CASES[case_id]
    if case_id in _DEV_CASES:
        return _DEV_CASES[case_id]
    if case_id in {
        "q-b02-positive-nae4",
        "q-b03-positive-nae3",
        "q-b06-positive-nae5",
    }:
        arity = {
            "q-b02-positive-nae4": 4,
            "q-b03-positive-nae3": 3,
            "q-b06-positive-nae5": 5,
        }[case_id]
        return (_nae(arity),)
    if case_id == "q-b05-or2-even-parity3":
        return (
            (2, _mask_from_predicate(2, any)),
            (3, _mask_from_predicate(3, lambda row: sum(row) % 2 == 0)),
        )
    if case_id == "q-b20-or3-xor2":
        return (
            (3, _mask_from_predicate(3, any)),
            (2, _mask_from_predicate(2, lambda row: row[0] != row[1])),
        )
    raise BooleanCSPGadgetProtocolError(
        "unsupported_target_case", f"no public truth table registered for {case_id}"
    )


def _target_table(case_id: str, handle: str) -> BooleanGammaTruthTable:
    specs = _target_specs(case_id)
    symbol_type = "Unit" if len(specs) == 1 else "Bool"
    constructor = COMMON + (".singletonGamma" if len(specs) == 1 else ".pairGamma")
    relations = tuple(
        BooleanRelationTruthTable(
            symbol_id=f"target-{index}",
            lean_symbol_term=(
                "()" if len(specs) == 1 else ("false" if index == 0 else "true")
            ),
            lean_symbol_type=symbol_type,
            arity=arity,
            mask=mask,
        )
        for index, (arity, mask) in enumerate(specs)
    )
    return BooleanGammaTruthTable(handle, constructor, relations)


_POINTWISE = re.compile(
    rf"^\((?P<binder>[A-Za-z_][A-Za-z0-9_']*) : "
    rf"(?P<source>\S+)\.Symbol\) (?:→|->) "
    rf"{re.escape(GADGET)} (?P<target>\S+) "
    rf"\((?P=source)\.relationOf (?P=binder)\)$"
)
_INTERPRETATION = re.compile(
    rf"^{re.escape(INTERPRETATION)} (?P<source>\S+) (?P<target>\S+)$"
)


def gadget_endpoints(exact_type: str) -> tuple[str, str, bool] | None:
    compact = " ".join(exact_type.split())
    match = _POINTWISE.fullmatch(compact)
    if match is not None:
        return match.group("source"), match.group("target"), True
    match = _INTERPRETATION.fullmatch(compact)
    if match is not None:
        return match.group("source"), match.group("target"), False
    return None


def _strict_keys(value: Mapping[str, Any], expected: set[str], label: str) -> None:
    actual = set(value)
    if actual != expected:
        raise BooleanCSPGadgetProtocolError(
            "gadget_plan_schema_invalid",
            f"{label} keys differ: missing={sorted(expected - actual)!r}, "
            f"extra={sorted(actual - expected)!r}",
        )


def _integer(value: Any, label: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise BooleanCSPGadgetProtocolError(
            "gadget_plan_schema_invalid", f"{label} must be an integer"
        )
    return value


@dataclass(frozen=True)
class BooleanCSPGadgetConstraintV1:
    target_symbol: str
    vars: tuple[int, ...]

    def to_dict(self) -> dict[str, Any]:
        return {"target_symbol": self.target_symbol, "vars": list(self.vars)}


@dataclass(frozen=True)
class BooleanCSPGadgetSpecV1:
    source_symbol: str
    variable_count: int
    outputs: tuple[int, ...]
    constraints: tuple[BooleanCSPGadgetConstraintV1, ...]

    def to_dict(self) -> dict[str, Any]:
        return {
            "source_symbol": self.source_symbol,
            "variable_count": self.variable_count,
            "outputs": list(self.outputs),
            "constraints": [constraint.to_dict() for constraint in self.constraints],
        }


@dataclass(frozen=True)
class BooleanCSPGadgetPlanV1:
    source_core: str
    gadgets: tuple[BooleanCSPGadgetSpecV1, ...]
    mathematical_rationale: str

    @property
    def semantic_payload(self) -> dict[str, Any]:
        return {
            "schema": GADGET_PLAN_SCHEMA,
            "source_core": self.source_core,
            "gadgets": [gadget.to_dict() for gadget in self.gadgets],
        }

    @property
    def semantic_payload_sha256(self) -> str:
        return stable_sha256(self.semantic_payload)

    @property
    def plan_id(self) -> str:
        return "gadget-plan-" + self.semantic_payload_sha256.removeprefix(
            "sha256:"
        )[:24]

    @property
    def constraint_count(self) -> int:
        return sum(len(gadget.constraints) for gadget in self.gadgets)

    @property
    def maximum_variable_count(self) -> int:
        return max(gadget.variable_count for gadget in self.gadgets)

    def to_dict(self) -> dict[str, Any]:
        return {
            **self.semantic_payload,
            "mathematical_rationale": self.mathematical_rationale,
        }

    def receipt_dict(self) -> dict[str, Any]:
        return {
            **self.to_dict(),
            "plan_id": self.plan_id,
            "semantic_payload_sha256": self.semantic_payload_sha256,
            "constraint_count": self.constraint_count,
            "maximum_variable_count": self.maximum_variable_count,
        }

    @classmethod
    def from_mapping(
        cls, value: Mapping[str, Any], context: BooleanCSPGadgetContext
    ) -> "BooleanCSPGadgetPlanV1":
        _strict_keys(
            value,
            {"schema", "source_core", "gadgets", "mathematical_rationale"},
            "gadget plan",
        )
        if value.get("schema") != GADGET_PLAN_SCHEMA:
            raise BooleanCSPGadgetProtocolError(
                "gadget_plan_schema_invalid", "unsupported gadget plan schema"
            )
        if value.get("source_core") != context.source_core:
            raise BooleanCSPGadgetProtocolError(
                "gadget_plan_schema_invalid",
                "source_core does not match the typed goal",
            )
        rationale = value.get("mathematical_rationale")
        if not isinstance(rationale, str) or not rationale.strip():
            raise BooleanCSPGadgetProtocolError(
                "gadget_plan_schema_invalid",
                "mathematical_rationale must be nonempty",
            )
        raw_gadgets = value.get("gadgets")
        if not isinstance(raw_gadgets, list) or not raw_gadgets:
            raise BooleanCSPGadgetProtocolError(
                "gadget_plan_schema_invalid", "gadgets must be a nonempty list"
            )
        source_by_id = context.source.by_symbol_id
        target_by_id = context.target.by_symbol_id
        gadgets: list[BooleanCSPGadgetSpecV1] = []
        for ordinal, raw in enumerate(raw_gadgets):
            if not isinstance(raw, Mapping):
                raise BooleanCSPGadgetProtocolError(
                    "gadget_plan_schema_invalid",
                    f"gadget {ordinal} must be an object",
                )
            _strict_keys(
                raw,
                {"source_symbol", "variable_count", "outputs", "constraints"},
                f"gadget {ordinal}",
            )
            source_symbol = raw.get("source_symbol")
            if not isinstance(source_symbol, str) or source_symbol not in source_by_id:
                raise BooleanCSPGadgetProtocolError(
                    "gadget_plan_schema_invalid",
                    f"gadget {ordinal} has unknown source_symbol",
                )
            variable_count = _integer(raw.get("variable_count"), "variable_count")
            if not 1 <= variable_count <= context.max_variable_count:
                raise BooleanCSPGadgetProtocolError(
                    "gadget_plan_schema_invalid",
                    "variable_count exceeds resource bounds",
                )
            raw_outputs = raw.get("outputs")
            if not isinstance(raw_outputs, list):
                raise BooleanCSPGadgetProtocolError(
                    "gadget_plan_schema_invalid", "outputs must be a list"
                )
            outputs = tuple(_integer(item, "output index") for item in raw_outputs)
            source_relation = source_by_id[source_symbol]
            if len(outputs) != source_relation.arity:
                raise BooleanCSPGadgetProtocolError(
                    "gadget_plan_schema_invalid",
                    "outputs length differs from source arity",
                )
            if len(outputs) != len(set(outputs)):
                raise BooleanCSPGadgetProtocolError(
                    "gadget_plan_schema_invalid", "outputs must be injective"
                )
            if any(index < 0 or index >= variable_count for index in outputs):
                raise BooleanCSPGadgetProtocolError(
                    "gadget_plan_schema_invalid",
                    "output variable index is out of range",
                )
            raw_constraints = raw.get("constraints")
            if not isinstance(raw_constraints, list) or not raw_constraints:
                raise BooleanCSPGadgetProtocolError(
                    "gadget_plan_schema_invalid",
                    "constraints must be a nonempty list",
                )
            if len(raw_constraints) > context.max_constraint_count:
                raise BooleanCSPGadgetProtocolError(
                    "gadget_plan_schema_invalid",
                    "constraint count exceeds resource bounds",
                )
            constraints: list[BooleanCSPGadgetConstraintV1] = []
            for constraint_ordinal, constraint in enumerate(raw_constraints):
                if not isinstance(constraint, Mapping):
                    raise BooleanCSPGadgetProtocolError(
                        "gadget_plan_schema_invalid",
                        "constraint must be an object",
                    )
                _strict_keys(
                    constraint,
                    {"target_symbol", "vars"},
                    f"constraint {constraint_ordinal}",
                )
                target_symbol = constraint.get("target_symbol")
                if (
                    not isinstance(target_symbol, str)
                    or target_symbol not in target_by_id
                ):
                    raise BooleanCSPGadgetProtocolError(
                        "gadget_plan_schema_invalid",
                        "constraint has unknown target_symbol",
                    )
                raw_vars = constraint.get("vars")
                if not isinstance(raw_vars, list):
                    raise BooleanCSPGadgetProtocolError(
                        "gadget_plan_schema_invalid",
                        "constraint vars must be a list",
                    )
                variables = tuple(
                    _integer(item, "constraint variable") for item in raw_vars
                )
                if len(variables) != target_by_id[target_symbol].arity:
                    raise BooleanCSPGadgetProtocolError(
                        "gadget_plan_schema_invalid", "constraint arity mismatch"
                    )
                if any(
                    index < 0 or index >= variable_count for index in variables
                ):
                    raise BooleanCSPGadgetProtocolError(
                        "gadget_plan_schema_invalid",
                        "constraint variable is out of range",
                    )
                constraints.append(
                    BooleanCSPGadgetConstraintV1(target_symbol, variables)
                )
            gadgets.append(
                BooleanCSPGadgetSpecV1(
                    source_symbol,
                    variable_count,
                    outputs,
                    tuple(constraints),
                )
            )
        actual_source_ids = tuple(gadget.source_symbol for gadget in gadgets)
        expected_source_ids = tuple(
            relation.symbol_id for relation in context.source.relations
        )
        if (
            len(actual_source_ids) != len(set(actual_source_ids))
            or set(actual_source_ids) != set(expected_source_ids)
        ):
            raise BooleanCSPGadgetProtocolError(
                "gadget_plan_schema_invalid",
                "gadgets must cover each source symbol exactly once",
            )
        return cls(context.source_core, tuple(gadgets), rationale.strip())


@dataclass(frozen=True)
class BooleanCSPGadgetSemanticCounterexample:
    source_symbol: str
    source_row_index: int
    source_tuple: tuple[bool, ...]
    expected_relation_holds: bool
    formula_has_extension: bool
    direction: str

    def to_dict(self) -> dict[str, Any]:
        return {
            "source_symbol": self.source_symbol,
            "source_row_index": self.source_row_index,
            "source_tuple": list(self.source_tuple),
            "expected_relation_holds": self.expected_relation_holds,
            "formula_has_extension": self.formula_has_extension,
            "direction": self.direction,
        }


@dataclass(frozen=True)
class BooleanCSPGadgetSemanticCheckReceipt:
    success: bool
    source_rows_checked: int
    auxiliary_assignments_checked: int
    semantic_payload_sha256: str
    checker_input_sha256: str
    checker_name: str
    checker_version: str
    counterexample: BooleanCSPGadgetSemanticCounterexample | None = None
    schema_version: str = GADGET_SEMANTIC_CHECK_RECEIPT_SCHEMA

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "success": self.success,
            "source_rows_checked": self.source_rows_checked,
            "auxiliary_assignments_checked": self.auxiliary_assignments_checked,
            "semantic_payload_sha256": self.semantic_payload_sha256,
            "checker_input_sha256": self.checker_input_sha256,
            "checker_name": self.checker_name,
            "checker_version": self.checker_version,
            "counterexample": (
                None if self.counterexample is None else self.counterexample.to_dict()
            ),
        }


def _formula_has_extension(
    *,
    gadget: BooleanCSPGadgetSpecV1,
    source_tuple: Sequence[bool],
    target_by_id: Mapping[str, BooleanRelationTruthTable],
) -> tuple[bool, int]:
    """Check one fixed source tuple without searching over gadget plans."""

    output_positions = set(gadget.outputs)
    auxiliary_positions = tuple(
        index
        for index in range(gadget.variable_count)
        if index not in output_positions
    )
    checked = 0
    for auxiliary_index in range(1 << len(auxiliary_positions)):
        auxiliary_tuple = _tuple_for_index(
            auxiliary_index, len(auxiliary_positions)
        )
        assignment = [False] * gadget.variable_count
        for coordinate, variable in enumerate(gadget.outputs):
            assignment[variable] = bool(source_tuple[coordinate])
        for coordinate, variable in enumerate(auxiliary_positions):
            assignment[variable] = auxiliary_tuple[coordinate]
        checked += 1
        if all(
            target_by_id[constraint.target_symbol].holds(
                tuple(assignment[variable] for variable in constraint.vars)
            )
            for constraint in gadget.constraints
        ):
            return True, checked
    return False, checked


def check_explicit_gadget_plan(
    *,
    plan: BooleanCSPGadgetPlanV1,
    context: BooleanCSPGadgetContext,
) -> BooleanCSPGadgetSemanticCheckReceipt:
    """Validate one explicit plan and return the first stable counterexample.

    The checker enumerates only Boolean assignments for the supplied plan.  It
    never enumerates, chooses, repairs, or otherwise generates a gadget plan.
    Lean remains the final proof authority after this diagnostic pre-check.
    """

    if plan.source_core != context.source_core:
        raise BooleanCSPGadgetProtocolError(
            "gadget_checker_context_mismatch",
            "plan source_core differs from the semantic checker context",
        )
    checker_input_sha256 = stable_sha256(
        {
            "checker_name": GADGET_SEMANTIC_CHECKER_NAME,
            "checker_version": GADGET_SEMANTIC_CHECKER_VERSION,
            "plan": plan.semantic_payload,
            "source": context.source.prompt_dict(),
            "target": context.target.prompt_dict(),
        }
    )
    gadget_by_source = {
        gadget.source_symbol: gadget for gadget in plan.gadgets
    }
    target_by_id = context.target.by_symbol_id
    source_rows_checked = 0
    auxiliary_assignments_checked = 0
    for source_relation in context.source.relations:
        gadget = gadget_by_source.get(source_relation.symbol_id)
        if gadget is None:
            raise BooleanCSPGadgetProtocolError(
                "gadget_checker_context_mismatch",
                "plan does not cover every source relation in checker context",
            )
        for source_row_index in range(1 << source_relation.arity):
            source_tuple = _tuple_for_index(
                source_row_index, source_relation.arity
            )
            expected = source_relation.holds(source_tuple)
            actual, checked = _formula_has_extension(
                gadget=gadget,
                source_tuple=source_tuple,
                target_by_id=target_by_id,
            )
            source_rows_checked += 1
            auxiliary_assignments_checked += checked
            if expected != actual:
                counterexample = BooleanCSPGadgetSemanticCounterexample(
                    source_symbol=source_relation.symbol_id,
                    source_row_index=source_row_index,
                    source_tuple=source_tuple,
                    expected_relation_holds=expected,
                    formula_has_extension=actual,
                    direction=("false-positive" if actual else "false-negative"),
                )
                return BooleanCSPGadgetSemanticCheckReceipt(
                    success=False,
                    source_rows_checked=source_rows_checked,
                    auxiliary_assignments_checked=(
                        auxiliary_assignments_checked
                    ),
                    semantic_payload_sha256=plan.semantic_payload_sha256,
                    checker_input_sha256=checker_input_sha256,
                    checker_name=GADGET_SEMANTIC_CHECKER_NAME,
                    checker_version=GADGET_SEMANTIC_CHECKER_VERSION,
                    counterexample=counterexample,
                )
    return BooleanCSPGadgetSemanticCheckReceipt(
        success=True,
        source_rows_checked=source_rows_checked,
        auxiliary_assignments_checked=auxiliary_assignments_checked,
        semantic_payload_sha256=plan.semantic_payload_sha256,
        checker_input_sha256=checker_input_sha256,
        checker_name=GADGET_SEMANTIC_CHECKER_NAME,
        checker_version=GADGET_SEMANTIC_CHECKER_VERSION,
    )


def gadget_plan_schema_description() -> dict[str, Any]:
    """Return a schema description without any example formula or candidate."""

    return {
        "top_level_exact_keys": [
            "schema",
            "source_core",
            "gadgets",
            "mathematical_rationale",
        ],
        "schema_constant": GADGET_PLAN_SCHEMA,
        "source_core": "must equal authoring_context.source_core",
        "gadgets": {
            "coverage": "exactly one item for every source symbol_id",
            "item_exact_keys": [
                "source_symbol",
                "variable_count",
                "outputs",
                "constraints",
            ],
            "source_symbol": "stable source symbol_id",
            "variable_count": "positive integer within resource limits",
            "outputs": (
                "integer variable indices, one per source coordinate, pairwise distinct"
            ),
            "constraints": {
                "nonempty": True,
                "item_exact_keys": ["target_symbol", "vars"],
                "target_symbol": "stable target symbol_id",
                "vars": "integer variable indices matching target relation arity",
            },
        },
        "mathematical_rationale": "short nonempty audit explanation",
        "candidate_lists_allowed": False,
    }


@dataclass(frozen=True)
class BooleanCSPGadgetAuthoringBrief:
    brief_id: str
    brief_sha256: str
    context: BooleanCSPGadgetContext
    forbidden_declarations: tuple[str, ...]
    allowed_neutral_declaration_signatures: tuple[str, ...]
    prior_failure: Mapping[str, Any] | None = None
    schema_version: str = GADGET_AUTHORING_BRIEF_SCHEMA

    @classmethod
    def create(
        cls,
        *,
        context: BooleanCSPGadgetContext,
        forbidden_declarations: Sequence[str],
        allowed_neutral_declaration_signatures: Sequence[str],
        prior_failure: Mapping[str, Any] | None = None,
    ) -> "BooleanCSPGadgetAuthoringBrief":
        payload = {
            "schema_version": GADGET_AUTHORING_BRIEF_SCHEMA,
            "answer_free": True,
            "authoring_context": context.prompt_dict(),
            "pp_definition_semantics": PP_DEFINITION_SEMANTICS,
            "spec_correct_definition": SPEC_CORRECT_DEFINITION,
            "required_output_schema": gadget_plan_schema_description(),
            "forbidden_declarations": tuple(dict.fromkeys(forbidden_declarations)),
            "allowed_neutral_declaration_signatures": tuple(
                dict.fromkeys(allowed_neutral_declaration_signatures)
            ),
            "prior_failure": None if prior_failure is None else dict(prior_failure),
            "prohibited_context_classes": (
                "known gadget formulas",
                "candidate formula lists",
                "deterministic search results",
                "other benchmark case solutions",
                "oracle or gold proof fields",
            ),
        }
        digest = stable_sha256(payload)
        return cls(
            brief_id="gadget-brief-" + digest.removeprefix("sha256:")[:24],
            brief_sha256=digest,
            context=context,
            forbidden_declarations=tuple(payload["forbidden_declarations"]),
            allowed_neutral_declaration_signatures=tuple(
                payload["allowed_neutral_declaration_signatures"]
            ),
            prior_failure=(
                None if prior_failure is None else dict(prior_failure)
            ),
        )

    def prompt_dict(self) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "brief_id": self.brief_id,
            "brief_sha256": self.brief_sha256,
            "answer_free": True,
            "authoring_context": self.context.prompt_dict(),
            "pp_definition_semantics": PP_DEFINITION_SEMANTICS,
            "spec_correct_definition": SPEC_CORRECT_DEFINITION,
            "required_output_schema": gadget_plan_schema_description(),
            "forbidden_declarations": list(self.forbidden_declarations),
            "allowed_neutral_declaration_signatures": list(
                self.allowed_neutral_declaration_signatures
            ),
            "prior_failure": (
                None if self.prior_failure is None else dict(self.prior_failure)
            ),
            "prohibited_context_classes": [
                "known gadget formulas",
                "candidate formula lists",
                "deterministic search results",
                "other benchmark case solutions",
                "oracle or gold proof fields",
            ],
        }


@dataclass(frozen=True)
class BooleanCSPGadgetRenderReceipt:
    declaration_name: str
    proof_body: str
    implementation: str
    semantic_payload_sha256_before: str
    semantic_payload_sha256_after: str
    renderer_name: str
    renderer_version: str
    model_constraint_count: int
    rendered_constraint_count: int
    renderer_added_semantic_atom_count: int

    def to_dict(self) -> dict[str, Any]:
        return {
            "declaration_name": self.declaration_name,
            "semantic_payload_sha256_before": self.semantic_payload_sha256_before,
            "semantic_payload_sha256_after": self.semantic_payload_sha256_after,
            "renderer_name": self.renderer_name,
            "renderer_version": self.renderer_version,
            "model_constraint_count": self.model_constraint_count,
            "rendered_constraint_count": self.rendered_constraint_count,
            "renderer_added_semantic_atom_count": (
                self.renderer_added_semantic_atom_count
            ),
        }


def _lean_vector(
    values: Sequence[int], domain_arity: int, variable_count: int
) -> str:
    entries = ", ".join(f"({value} : Fin {variable_count})" for value in values)
    return f"(![{entries}] : Fin {domain_arity} → Fin {variable_count})"


def render_boolean_csp_gadget_plan(
    *,
    plan: BooleanCSPGadgetPlanV1,
    context: BooleanCSPGadgetContext,
    declaration_name: str,
) -> BooleanCSPGadgetRenderReceipt:
    """Serialize one validated plan without changing any semantic atom."""

    if len(plan.gadgets) != 1 or len(context.source.relations) != 1:
        raise BooleanCSPGadgetProtocolError(
            "renderer_source_language_unsupported",
            "renderer currently requires a one-symbol source hard core",
        )
    gadget = plan.gadgets[0]
    source_relation = context.source.by_symbol_id[gadget.source_symbol]
    target_by_id = context.target.by_symbol_id
    lines = ["classical"]
    if not context.pointwise:
        lines.append("refine { gadgetOf := ?_ }")
    lines.extend(("intro sourceSymbol", f"let spec : {FINITE_GADGET}.Spec"))
    lines.append(f"    {context.target.handle}")
    lines.append(
        f"    ({context.source.handle}.relationOf sourceSymbol) "
        f"{gadget.variable_count} := {{"
    )
    lines.append("  formula := [")
    rendered_constraints: list[dict[str, Any]] = []
    for ordinal, constraint in enumerate(gadget.constraints):
        relation = target_by_id[constraint.target_symbol]
        rendered_constraints.append(constraint.to_dict())
        lines.extend(
            (
                "    {",
                "      symbol := by",
                f"        simpa only [{context.target.handle}, "
                f"{context.target.constructor_declaration}] using",
                f"          ({relation.lean_symbol_term} : "
                f"{relation.lean_symbol_type})",
                "      vars := by",
                f"        simpa only [{context.target.handle}, "
                f"{context.target.constructor_declaration}] using",
                "          "
                + _lean_vector(
                    constraint.vars, relation.arity, gadget.variable_count
                ),
                "    }" + ("," if ordinal + 1 < len(gadget.constraints) else ""),
            )
        )
    lines.extend(
        (
            "  ]",
            "  outputs := by",
            f"    simpa only [{context.source.handle}] using",
            "      "
            + _lean_vector(
                gadget.outputs, source_relation.arity, gadget.variable_count
            ),
            "  outputs_injective := by",
            f"    simp only [{context.source.handle}]",
            "    decide",
            "}",
            f"exact {FINITE_GADGET}.Spec.toGadget spec (by",
            f"  simp [{FINITE_GADGET}.Spec.Correct, spec, "
            f"{context.source.handle},",
            f"    {context.target.handle}, "
            f"{context.target.constructor_declaration}] <;> decide)",
        )
    )
    proof_body = "\n".join(lines)
    implementation = (
        f"noncomputable def {declaration_name} : "
        f"{' '.join(context.exact_goal.split())} := by\n"
        + "\n".join("  " + line if line else "" for line in lines)
    )
    rendered_semantic_payload = {
        "schema": GADGET_PLAN_SCHEMA,
        "source_core": plan.source_core,
        "gadgets": [
            {
                "source_symbol": gadget.source_symbol,
                "variable_count": gadget.variable_count,
                "outputs": list(gadget.outputs),
                "constraints": rendered_constraints,
            }
        ],
    }
    before = plan.semantic_payload_sha256
    after = stable_sha256(rendered_semantic_payload)
    if before != after:
        raise RuntimeError("canonical renderer changed the semantic payload")
    rendered_count = len(rendered_constraints)
    if rendered_count != plan.constraint_count:
        raise RuntimeError("canonical renderer changed the constraint count")
    return BooleanCSPGadgetRenderReceipt(
        declaration_name=declaration_name,
        proof_body=proof_body,
        implementation=implementation,
        semantic_payload_sha256_before=before,
        semantic_payload_sha256_after=after,
        renderer_name=GADGET_RENDERER_NAME,
        renderer_version=GADGET_RENDERER_VERSION,
        model_constraint_count=plan.constraint_count,
        rendered_constraint_count=rendered_count,
        renderer_added_semantic_atom_count=0,
    )


__all__ = [
    "BooleanCSPGadgetAuthoringBrief",
    "BooleanCSPGadgetConstraintV1",
    "BooleanCSPGadgetContext",
    "BooleanCSPGadgetPlanV1",
    "BooleanCSPGadgetProtocolError",
    "BooleanCSPGadgetRenderReceipt",
    "BooleanCSPGadgetSemanticCheckReceipt",
    "BooleanCSPGadgetSemanticCounterexample",
    "BooleanCSPGadgetSpecV1",
    "BooleanGammaTruthTable",
    "BooleanRelationTruthTable",
    "GADGET_AUTHORING_BRIEF_SCHEMA",
    "GADGET_AUTHORING_GENERATOR_NAME",
    "GADGET_AUTHORING_GENERATOR_VERSION",
    "GADGET_AUTHORING_ALLOWED_SOURCE_CORES",
    "GADGET_AUTHORING_RECEIPT_SCHEMA",
    "GADGET_PLAN_SCHEMA",
    "GADGET_RENDERER_NAME",
    "GADGET_RENDERER_VERSION",
    "GADGET_SEMANTIC_CHECKER_NAME",
    "GADGET_SEMANTIC_CHECKER_VERSION",
    "GADGET_SEMANTIC_CHECK_RECEIPT_SCHEMA",
    "GADGET_TRUTH_TABLE_CONTEXT_VERSION",
    "NAE3_CORE",
    "ONE_IN_THREE_CORE",
    "PP_DEFINITION_SEMANTICS",
    "SPEC_CORRECT_DEFINITION",
    "gadget_endpoints",
    "gadget_plan_schema_description",
    "check_explicit_gadget_plan",
    "render_boolean_csp_gadget_plan",
]
