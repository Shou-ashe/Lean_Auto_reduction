"""Stage H predicate-input benchmark boundary and oracle isolation.

The suite exposes only the input declaration and public open-target policy.
It never records the PresentedProblem selected for a predicate, a preferred
hardness target, a route, or candidate declarations in ``coverage``.  Those
facts must come from nonce-bound Lean observations and bounded catalog queries.
"""

from __future__ import annotations

from typing import Any, Mapping

from .benchmark import BenchmarkCase, BenchmarkSuite


PREDICATE_INPUT_SUITE_ID = "predicate-input"
PREDICATE_INPUT_CASE_COUNT = 8
PREDICATE_INPUT_POSITIVE_COUNT = 4
PREDICATE_INPUT_NEGATIVE_COUNT = 4
PREDICATE_INPUT_MODULE = "Benchmark.Hardness.Inputs.PredicateInput"

PREDICATE_ACCEPTS_NOT_DEFINITIONALLY_EQUAL = (
    "predicate_accepts_not_definitionally_equal"
)
AMBIGUOUS_PREDICATE_PRESENTATION = "ambiguous_predicate_presentation"
CLOSED_PROP_HAS_NO_PROBLEM_ENCODING = "closed_prop_has_no_problem_encoding"
PREDICATE_HAS_NO_LAWFUL_PRESENTATION = "predicate_has_no_lawful_presentation"

PREDICATE_INPUT_FAILURE_CODES = frozenset(
    {
        PREDICATE_ACCEPTS_NOT_DEFINITIONALLY_EQUAL,
        AMBIGUOUS_PREDICATE_PRESENTATION,
        CLOSED_PROP_HAS_NO_PROBLEM_ENCODING,
        PREDICATE_HAS_NO_LAWFUL_PRESENTATION,
    }
)

EXPECTED_CASE_DECLARATIONS: Mapping[str, str] = {
    "predicate-input-exact-accepts": f"{PREDICATE_INPUT_MODULE}.directCNFAccepts",
    "predicate-input-notation-expanded": (
        f"{PREDICATE_INPUT_MODULE}.notationExpandedCNFAccepts"
    ),
    "predicate-input-reducible-wrapper": (
        f"{PREDICATE_INPUT_MODULE}.reducibleWrappedCNFAccepts"
    ),
    "predicate-input-same-carrier-different-predicate": (
        f"{PREDICATE_INPUT_MODULE}.sameCarrierDifferentPredicate"
    ),
    "predicate-input-same-predicate-incompatible-codec": (
        f"{PREDICATE_INPUT_MODULE}.representationIncompatiblePartitionAccepts"
    ),
    "predicate-input-closed-prop": f"{PREDICATE_INPUT_MODULE}.closedProposition",
    "predicate-input-missing-presentation": (
        f"{PREDICATE_INPUT_MODULE}.missingPresentationPredicate"
    ),
    "predicate-input-multiple-candidates-unique-codec": (
        f"{PREDICATE_INPUT_MODULE}.uniqueThreeSATAccepts"
    ),
}

EXPECTED_CASE_SCENARIOS: Mapping[str, str] = {
    "predicate-input-exact-accepts": "exact_accepts",
    "predicate-input-notation-expanded": "notation_expansion",
    "predicate-input-reducible-wrapper": "reducible_wrapper",
    "predicate-input-same-carrier-different-predicate": (
        "same_carrier_different_predicate"
    ),
    "predicate-input-same-predicate-incompatible-codec": (
        "same_predicate_incompatible_codec"
    ),
    "predicate-input-closed-prop": "closed_prop",
    "predicate-input-missing-presentation": "missing_presentation",
    "predicate-input-multiple-candidates-unique-codec": (
        "multiple_candidates_unique_correct_codec"
    ),
}

EXPECTED_NEGATIVE_FAILURES: Mapping[str, str] = {
    "predicate-input-same-carrier-different-predicate": (
        PREDICATE_ACCEPTS_NOT_DEFINITIONALLY_EQUAL
    ),
    "predicate-input-same-predicate-incompatible-codec": (
        AMBIGUOUS_PREDICATE_PRESENTATION
    ),
    "predicate-input-closed-prop": CLOSED_PROP_HAS_NO_PROBLEM_ENCODING,
    "predicate-input-missing-presentation": PREDICATE_HAS_NO_LAWFUL_PRESENTATION,
}

# Public target-certificate policy.  This table deliberately contains neither
# a chosen PresentedProblem nor a target/route declaration.
EXPECTED_CASE_POLICIES: Mapping[
    str, tuple[str, tuple[str, ...], int, int, bool]
] = {
    case_id: (
        (
            "native_np_complete",
            ("native_completeness",),
            2,
            8,
            True,
        )
        if case_id == "predicate-input-multiple-candidates-unique-codec"
        else ("native_np", ("native_membership",), 3, 8, False)
    )
    for case_id in EXPECTED_CASE_DECLARATIONS
}

# These fields are benchmark answers and must never enter a model prompt.
PROMPT_FORBIDDEN_KEYS = frozenset(
    {
        "acceptable_candidate",
        "acceptable_candidates",
        "acceptable_presentation",
        "acceptable_presentations",
        "acceptable_target",
        "acceptable_targets",
        "benchmark_candidate",
        "benchmark_presentation",
        "benchmark_target",
        "case_id",
        "coverage",
        "expected",
        "expected_candidate",
        "expected_failure_code",
        "expected_presentation",
        "expected_route",
        "expected_target",
        "final_failure_code",
        "gold_candidate",
        "gold_presentation",
        "gold_route",
        "gold_target",
        "hidden_candidate",
        "hidden_presentation",
        "hidden_target",
        "oracle_candidate",
        "oracle_presentation",
        "oracle_route",
        "oracle_target",
        "preferred_candidate",
        "preferred_presentation",
        "preferred_target",
        "suite_id",
        "tags",
    }
)

# Candidate declarations are legitimate only after bounded retrieval.  The
# initial request may specify the predicate and public policy, but no selected
# presentation, candidate, target, or route.
REQUEST_FORBIDDEN_KEYS = frozenset(
    {
        "candidate",
        "candidate_declaration",
        "candidate_declarations",
        "fixed_target",
        "matched_problem",
        "matched_problem_declaration",
        "presentation",
        "presentation_declaration",
        "route",
        "route_declaration",
        "route_declarations",
        "selected_candidate",
        "selected_presentation",
        "target",
        "target_declaration",
        "target_node_id",
    }
)

COVERAGE_FORBIDDEN_KEYS = frozenset(
    {
        *PROMPT_FORBIDDEN_KEYS,
        *REQUEST_FORBIDDEN_KEYS,
        "candidate_declarations",
        "candidate_node_ids",
        "matched_problem_declaration",
        "presentation_declarations",
        "problem_declaration",
        "problem_declarations",
        "required_candidate_declaration",
        "required_candidate_declarations",
        "required_presentation_declaration",
        "required_presentation_declarations",
        "required_route_declaration",
        "required_route_declarations",
        "required_target_declaration",
        "required_target_declarations",
        "route_declarations",
        "selected_problem_declaration",
        "source_problem_declaration",
    }
)


def _forbidden_key_paths(
    value: Any,
    *,
    forbidden: frozenset[str],
    prefix: str = "",
) -> set[str]:
    paths: set[str] = set()
    if isinstance(value, Mapping):
        for raw_key, item in value.items():
            key = str(raw_key)
            path = f"{prefix}.{key}" if prefix else key
            if key in forbidden:
                paths.add(path)
            paths.update(_forbidden_key_paths(item, forbidden=forbidden, prefix=path))
    elif isinstance(value, (list, tuple)):
        for index, item in enumerate(value):
            path = f"{prefix}[{index}]"
            paths.update(_forbidden_key_paths(item, forbidden=forbidden, prefix=path))
    return paths


def _declaration_value_paths(value: Any, *, prefix: str = "") -> set[str]:
    paths: set[str] = set()
    if isinstance(value, Mapping):
        for raw_key, item in value.items():
            key = str(raw_key)
            path = f"{prefix}.{key}" if prefix else key
            paths.update(_declaration_value_paths(item, prefix=path))
    elif isinstance(value, (list, tuple)):
        for index, item in enumerate(value):
            paths.update(
                _declaration_value_paths(item, prefix=f"{prefix}[{index}]")
            )
    elif isinstance(value, str) and value.startswith(
        ("ComplexityReduction.", "Benchmark.Hardness.")
    ):
        paths.add(prefix)
    return paths


def find_predicate_input_prompt_forbidden_keys(
    payload: Mapping[str, Any],
) -> tuple[str, ...]:
    """Return benchmark-answer fields forbidden from a Stage H model prompt."""

    leaked = _forbidden_key_paths(payload, forbidden=PROMPT_FORBIDDEN_KEYS)
    request = payload.get("request")
    if isinstance(request, Mapping):
        leaked.update(
            f"request.{key}" for key in set(request) & REQUEST_FORBIDDEN_KEYS
        )
    return tuple(sorted(leaked))


def audit_predicate_input_prompt(payload: Mapping[str, Any]) -> None:
    """Reject fixed answers while permitting candidates returned by retrieval."""

    leaked = find_predicate_input_prompt_forbidden_keys(payload)
    if leaked:
        raise ValueError(
            "predicate-input prompt contains benchmark answer fields: "
            + ", ".join(leaked)
        )


def find_predicate_input_coverage_oracles(
    coverage: Mapping[str, Any],
) -> tuple[str, ...]:
    """Return target, route, or candidate declarations leaked by coverage."""

    leaked = _forbidden_key_paths(coverage, forbidden=COVERAGE_FORBIDDEN_KEYS)
    leaked.update(_declaration_value_paths(coverage))
    return tuple(sorted(leaked))


def validate_predicate_input_suite(
    suite: BenchmarkSuite,
) -> tuple[BenchmarkCase, ...]:
    """Enforce the strict eight-case Stage H predicate-input contract."""

    cases = suite.cases
    positives = tuple(case for case in cases if case.is_positive)
    negatives = tuple(case for case in cases if not case.is_positive)
    if suite.id != PREDICATE_INPUT_SUITE_ID:
        raise ValueError(
            f"expected suite {PREDICATE_INPUT_SUITE_ID}, got {suite.id}"
        )
    if len(cases) != PREDICATE_INPUT_CASE_COUNT:
        raise ValueError(
            f"predicate-input suite must contain {PREDICATE_INPUT_CASE_COUNT} cases"
        )
    if (
        len(positives) != PREDICATE_INPUT_POSITIVE_COUNT
        or len(negatives) != PREDICATE_INPUT_NEGATIVE_COUNT
    ):
        raise ValueError(
            "predicate-input suite must contain exactly 4 positive and 4 negative cases"
        )
    if {case.id for case in cases} != set(EXPECTED_CASE_DECLARATIONS):
        raise ValueError(
            "predicate-input suite case IDs drifted from the Stage H contract"
        )

    seen_scenarios: set[str] = set()
    for case in cases:
        expected_declaration = EXPECTED_CASE_DECLARATIONS[case.id]
        expected_input_kind = (
            "closed_prop" if case.id == "predicate-input-closed-prop" else "predicate"
        )
        if (
            case.module != PREDICATE_INPUT_MODULE
            or case.source != expected_declaration
            or case.effective_input_declaration != expected_declaration
            or case.input_kind != expected_input_kind
            or case.membership is not None
            or case.target is not None
            or case.objective != "reduce_to_known_np"
            or case.objective_direction != "source_to_target"
            or case.target_policy != "open"
            or case.catalog_mode != "full"
            or case.execution_layer != "core_reuse"
            or case.verification_profile != "core"
            or case.evaluation_lane != "predicate_open_target"
            or case.authoring_policy != {"enabled": False, "mode": "disabled"}
            or case.group_id is not None
            or case.matched_pair_id is not None
            or case.comparison_group_id is not None
            or case.family_id is not None
            or case.source_form_id is not None
            or case.target_form_id is not None
            or case.hub_ids
        ):
            raise ValueError(
                f"case {case.id} is outside the predicate-input study ABI"
            )

        expected_policy = EXPECTED_CASE_POLICIES[case.id]
        actual_policy = (
            case.required_hardness,
            case.allowed_target_evidence,
            case.maximum_route_atoms,
            case.maximum_dependencies,
            case.allow_reflexive_target,
        )
        if actual_policy != expected_policy:
            raise ValueError(f"case {case.id} changed its public target policy")
        if case.resources.get("max_model_calls") != 14:
            raise ValueError(f"case {case.id} must declare max_model_calls=14")

        scenario = case.coverage.get("predicate_input_scenario")
        if scenario != EXPECTED_CASE_SCENARIOS[case.id]:
            raise ValueError(
                f"case {case.id} changed its predicate-input scenario"
            )
        seen_scenarios.add(str(scenario))
        leaked = find_predicate_input_coverage_oracles(case.coverage)
        if leaked:
            raise ValueError(
                f"case {case.id} coverage contains target/route/candidate oracle data: "
                + ", ".join(leaked)
            )

        expected_failure = EXPECTED_NEGATIVE_FAILURES.get(case.id)
        if expected_failure is None:
            if case.expected.final_status != "VERIFIED" or (
                case.expected.final_failure_code is not None
            ):
                raise ValueError(f"case {case.id} must be an expected VERIFIED case")
        elif (
            case.expected.final_status != "BLOCKED"
            or case.expected.final_failure_code != expected_failure
        ):
            raise ValueError(
                f"case {case.id} must expect blocker {expected_failure}"
            )
        if (
            case.expected.baseline_status is not None
            or case.expected.baseline_failure_code is not None
        ):
            raise ValueError(
                f"case {case.id} Expected may contain only final status/failure code"
            )

    if seen_scenarios != set(EXPECTED_CASE_SCENARIOS.values()):
        raise ValueError(
            "predicate-input suite must cover each Stage H scenario exactly once"
        )
    return cases
