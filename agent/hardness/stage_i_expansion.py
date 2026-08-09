"""Contract validation for the first Stage-I expansion batch."""

from __future__ import annotations

from collections import Counter
from collections.abc import Mapping

from .benchmark import BenchmarkCase, BenchmarkSuite
from .open_target import (
    COVERAGE_FORBIDDEN_KEYS,
    _declaration_values,
    _forbidden_key_paths,
)


STAGE_I_SUITE_ID = "stage-i-expansion"
STAGE_I_CASE_COUNT = 8
STAGE_I_POSITIVE_COUNT = 4
STAGE_I_NEGATIVE_COUNT = 4
STAGE_I_MODULE = "Benchmark.Hardness.Inputs.StageIExpansion"

EXPECTED_CASES: Mapping[
    str,
    tuple[str, str, int, int, int, str | None],
] = {
    "stage-i-tagged-presented-long-hardness": (
        f"{STAGE_I_MODULE}.taggedPresented",
        "presented_problem",
        5,
        5,
        16,
        None,
    ),
    "stage-i-tagged-predicate-long-hardness": (
        f"{STAGE_I_MODULE}.taggedPredicate",
        "predicate",
        5,
        5,
        16,
        None,
    ),
    "stage-i-set-covering-presented-long-hardness": (
        f"{STAGE_I_MODULE}.setCoveringPresented",
        "presented_problem",
        5,
        6,
        16,
        None,
    ),
    "stage-i-set-covering-predicate-long-hardness": (
        f"{STAGE_I_MODULE}.setCoveringPredicate",
        "predicate",
        5,
        6,
        16,
        None,
    ),
    "stage-i-no-eligible-transport-dependency-limit": (
        f"{STAGE_I_MODULE}.taggedPresented",
        "presented_problem",
        5,
        5,
        2,
        "no_eligible_hardness_target",
    ),
    "stage-i-forward-route-absent": (
        f"{STAGE_I_MODULE}.disconnectedGraphPresented",
        "presented_problem",
        1,
        6,
        16,
        "eligible_target_has_no_existing_route",
    ),
    "stage-i-reverse-only-hard-target": (
        f"{STAGE_I_MODULE}.reverseOnlyHardPresented",
        "presented_problem",
        1,
        6,
        16,
        "eligible_target_has_no_existing_route",
    ),
    "stage-i-ambiguous-predicate-presentation": (
        f"{STAGE_I_MODULE}.ambiguousPartitionPredicate",
        "predicate",
        1,
        6,
        16,
        "ambiguous_predicate_presentation",
    ),
}


def validate_stage_i_expansion_suite(
    suite: BenchmarkSuite,
) -> tuple[BenchmarkCase, ...]:
    cases = suite.cases
    if suite.id != STAGE_I_SUITE_ID:
        raise ValueError(f"expected suite {STAGE_I_SUITE_ID}, got {suite.id}")
    if len(cases) != STAGE_I_CASE_COUNT:
        raise ValueError(f"Stage I suite must contain {STAGE_I_CASE_COUNT} cases")
    if {case.id for case in cases} != set(EXPECTED_CASES):
        raise ValueError("Stage I suite case IDs drifted from its contract")
    counts = Counter(case.expected.final_status for case in cases)
    if (
        counts["VERIFIED"] != STAGE_I_POSITIVE_COUNT
        or counts["BLOCKED"] != STAGE_I_NEGATIVE_COUNT
    ):
        raise ValueError("Stage I suite must contain four positives and four negatives")

    for case in cases:
        declaration, input_kind, minimum, maximum, dependencies, failure = (
            EXPECTED_CASES[case.id]
        )
        if (
            case.module != STAGE_I_MODULE
            or case.source != declaration
            or case.effective_input_declaration != declaration
            or case.input_kind != input_kind
            or case.membership is not None
            or case.target is not None
            or case.objective != "reduce_to_known_hardness"
            or case.objective_direction != "source_to_target"
            or case.target_policy != "open"
            or case.required_hardness != "native_np_hard"
            or case.allowed_target_evidence
            != ("transported_native_hardness",)
            or case.minimum_route_atoms != minimum
            or case.maximum_route_atoms != maximum
            or case.maximum_dependencies != dependencies
            or case.allow_reflexive_target
            or not case.require_simple_path
            or case.catalog_mode != "full"
            or case.execution_layer != "core_reuse"
            or case.verification_profile != "core"
            or case.evaluation_lane != "stage_i_expansion"
            or case.authoring_policy != {"enabled": False, "mode": "disabled"}
            or case.group_id is not None
            or case.matched_pair_id is not None
            or case.comparison_group_id is not None
            or case.family_id is not None
            or case.source_form_id is not None
            or case.target_form_id is not None
            or case.hub_ids
        ):
            raise ValueError(f"case {case.id} is outside the Stage I expansion ABI")
        if case.resources.get("max_model_calls") != 14:
            raise ValueError(f"case {case.id} must declare max_model_calls=14")
        leaked_keys = _forbidden_key_paths(
            case.coverage,
            forbidden=COVERAGE_FORBIDDEN_KEYS,
        )
        leaked_declarations = _declaration_values(case.coverage)
        if leaked_keys or leaked_declarations:
            raise ValueError(
                f"case {case.id} coverage contains target/route oracle data: "
                + ", ".join(sorted(leaked_keys | leaked_declarations))
            )
        if failure is None:
            if (
                case.expected.final_status != "VERIFIED"
                or case.expected.final_failure_code is not None
            ):
                raise ValueError(f"case {case.id} must be a positive case")
        elif (
            case.expected.final_status != "BLOCKED"
            or case.expected.final_failure_code != failure
        ):
            raise ValueError(f"case {case.id} must expect {failure}")
        if (
            case.expected.baseline_status is not None
            or case.expected.baseline_failure_code is not None
        ):
            raise ValueError("Stage I Expected records may contain only final outcome")
    return cases

