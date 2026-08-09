"""Stage G open-target benchmark boundary and prompt-oracle audit.

The suite describes public target-certificate policy only.  It deliberately
contains no preferred target, acceptable-target list, or gold route.  A model
may see target declarations only after they are returned by the bounded
``search_hardness_targets`` protocol.
"""

from __future__ import annotations

from collections import Counter
from typing import Any, Mapping

from .benchmark import BenchmarkCase, BenchmarkSuite


OPEN_TARGET_SUITE_ID = "open-target"
OPEN_TARGET_CASE_COUNT = 7
OPEN_TARGET_POSITIVE_COUNT = 3
OPEN_TARGET_NEGATIVE_COUNT = 4

GRAPH_SOURCE = "Benchmark.Hardness.Inputs.InputGrounding.Graph.direct"
STRUCTURED_CNF_SOURCE = (
    "Benchmark.Hardness.Inputs.InputGrounding.Clause.structuredCNFDirect"
)
TWO_CNF_SOURCE = "Benchmark.Hardness.Inputs.InputGrounding.Clause.twoCNFDirect"
THREE_SAT_SOURCE = "Benchmark.Hardness.Inputs.InputGrounding.Clause.threeSATDirect"
EXACT_COVER_SOURCE = (
    "Benchmark.Hardness.Inputs.InputGrounding.Incidence.exactCoverDirect"
)
MODIFIED_EXACT_COVER_SOURCE = (
    "Benchmark.Hardness.Inputs.InputGrounding.Incidence.modifiedExactCoverDirect"
)

EXPECTED_SOURCE_COUNTS = Counter(
    {
        STRUCTURED_CNF_SOURCE: 2,
        GRAPH_SOURCE: 1,
        TWO_CNF_SOURCE: 1,
        THREE_SAT_SOURCE: 1,
        EXACT_COVER_SOURCE: 1,
        MODIFIED_EXACT_COVER_SOURCE: 1,
    }
)

# These fields define the public ambiguity/resource policy, never a selected
# target.  Keeping the table target-free lets the validator catch accidental
# drift without creating an oracle for the model or evaluator.
EXPECTED_CASE_POLICIES: Mapping[str, tuple[str, tuple[str, ...], int, int, bool]] = {
    "open-target-structured-cnf-native-np": (
        "native_np",
        ("native_membership",),
        3,
        8,
        False,
    ),
    "open-target-two-cnf-native-np-hard": (
        "native_np_hard",
        ("native_completeness",),
        3,
        8,
        False,
    ),
    "open-target-three-sat-native-np-complete": (
        "native_np_complete",
        ("native_completeness",),
        2,
        8,
        True,
    ),
    "open-target-graph-no-route": (
        "native_np",
        ("native_membership",),
        3,
        8,
        False,
    ),
    "open-target-exact-cover-reverse-only": (
        "native_np_complete",
        ("native_completeness",),
        3,
        8,
        False,
    ),
    "open-target-modified-exact-cover-no-route": (
        "native_np",
        ("native_membership",),
        3,
        8,
        False,
    ),
    "open-target-structured-cnf-no-eligible-target": (
        "native_np",
        ("native_membership",),
        3,
        0,
        False,
    ),
}

EXPECTED_CASE_SOURCES: Mapping[str, str] = {
    "open-target-structured-cnf-native-np": STRUCTURED_CNF_SOURCE,
    "open-target-two-cnf-native-np-hard": TWO_CNF_SOURCE,
    "open-target-three-sat-native-np-complete": THREE_SAT_SOURCE,
    "open-target-graph-no-route": GRAPH_SOURCE,
    "open-target-exact-cover-reverse-only": EXACT_COVER_SOURCE,
    "open-target-modified-exact-cover-no-route": MODIFIED_EXACT_COVER_SOURCE,
    "open-target-structured-cnf-no-eligible-target": STRUCTURED_CNF_SOURCE,
}

EXPECTED_NEGATIVE_FAILURES: Mapping[str, str] = {
    "open-target-graph-no-route": "eligible_target_has_no_existing_route",
    "open-target-exact-cover-reverse-only": (
        "eligible_target_has_no_existing_route"
    ),
    "open-target-modified-exact-cover-no-route": (
        "eligible_target_has_no_existing_route"
    ),
    "open-target-structured-cnf-no-eligible-target": (
        "no_eligible_hardness_target"
    ),
}

PROMPT_FORBIDDEN_KEYS = frozenset(
    {
        "acceptable_target",
        "acceptable_targets",
        "acceptable_target_declarations",
        "benchmark_target",
        "case_id",
        "coverage",
        "expected",
        "expected_failure_code",
        "expected_route",
        "expected_target",
        "final_failure_code",
        "fixed_target",
        "gold_route",
        "gold_route_declarations",
        "gold_target",
        "gold_target_declaration",
        "hidden_target",
        "oracle_route",
        "oracle_target",
        "preferred_target",
        "required_route_declaration",
        "required_route_declarations",
        "required_target",
        "required_target_declaration",
        "suite_id",
        "tags",
    }
)

# Candidate target fields are legitimate inside bounded search results.  They
# are forbidden only in the initial public request, where they would recreate
# the fixed-target benchmark.
REQUEST_FORBIDDEN_KEYS = frozenset(
    {"target", "target_declaration", "target_node_id", "fixed_target"}
)

COVERAGE_FORBIDDEN_KEYS = frozenset(
    {
        "acceptable_target",
        "acceptable_targets",
        "acceptable_target_declarations",
        "expected_route",
        "expected_target",
        "gold_route",
        "gold_route_declarations",
        "gold_target",
        "gold_target_declaration",
        "preferred_target",
        "required_route_declaration",
        "required_route_declarations",
        "required_target",
        "required_target_declaration",
        "route_declaration",
        "route_declarations",
        "target",
        "target_declaration",
        "target_node_id",
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


def _declaration_values(value: Any, *, prefix: str = "") -> set[str]:
    paths: set[str] = set()
    if isinstance(value, Mapping):
        for raw_key, item in value.items():
            key = str(raw_key)
            path = f"{prefix}.{key}" if prefix else key
            paths.update(_declaration_values(item, prefix=path))
    elif isinstance(value, (list, tuple)):
        for index, item in enumerate(value):
            paths.update(_declaration_values(item, prefix=f"{prefix}[{index}]"))
    elif isinstance(value, str) and value.startswith(
        ("ComplexityReduction.", "Benchmark.Hardness.")
    ):
        paths.add(prefix)
    return paths


def find_open_target_prompt_forbidden_keys(
    payload: Mapping[str, Any],
) -> tuple[str, ...]:
    """Return oracle/fixed-target fields that must not reach the model."""

    leaked = _forbidden_key_paths(payload, forbidden=PROMPT_FORBIDDEN_KEYS)
    request = payload.get("request")
    if isinstance(request, Mapping):
        leaked.update(
            f"request.{key}" for key in set(request) & REQUEST_FORBIDDEN_KEYS
        )
    return tuple(sorted(leaked))


def audit_open_target_prompt(payload: Mapping[str, Any]) -> None:
    """Reject a prompt that contains benchmark answers or a fixed target."""

    leaked = find_open_target_prompt_forbidden_keys(payload)
    if leaked:
        raise ValueError(
            "open-target prompt contains benchmark answer fields: "
            + ", ".join(leaked)
        )


def validate_open_target_suite(suite: BenchmarkSuite) -> tuple[BenchmarkCase, ...]:
    """Enforce the target-free seven-case Stage G benchmark contract."""

    cases = suite.cases
    positives = tuple(case for case in cases if case.is_positive)
    negatives = tuple(case for case in cases if not case.is_positive)
    if suite.id != OPEN_TARGET_SUITE_ID:
        raise ValueError(f"expected suite {OPEN_TARGET_SUITE_ID}, got {suite.id}")
    if len(cases) != OPEN_TARGET_CASE_COUNT:
        raise ValueError(f"open-target suite must contain {OPEN_TARGET_CASE_COUNT} cases")
    if (
        len(positives) != OPEN_TARGET_POSITIVE_COUNT
        or len(negatives) != OPEN_TARGET_NEGATIVE_COUNT
    ):
        raise ValueError(
            "open-target suite must contain exactly 3 positive and 4 negative cases"
        )
    if {case.id for case in cases} != set(EXPECTED_CASE_POLICIES):
        raise ValueError("open-target suite case IDs drifted from the Stage G contract")
    if Counter(case.source for case in cases) != EXPECTED_SOURCE_COUNTS:
        raise ValueError("open-target suite must cover the six direct sources exactly")

    for case in cases:
        if (
            case.source != EXPECTED_CASE_SOURCES[case.id]
            or case.effective_input_declaration != case.source
            or case.input_kind != "presented_problem"
            or case.membership is not None
            or case.target is not None
            or case.objective != "reduce_to_known_np"
            or case.objective_direction != "source_to_target"
            or case.target_policy != "open"
            or case.catalog_mode != "full"
            or case.execution_layer != "core_reuse"
            or case.verification_profile != "core"
            or case.evaluation_lane != "open_target"
            or case.authoring_policy != {"enabled": False, "mode": "disabled"}
            or case.group_id is not None
            or case.matched_pair_id is not None
            or case.comparison_group_id is not None
            or case.family_id is not None
            or case.source_form_id is not None
            or case.target_form_id is not None
            or case.hub_ids
        ):
            raise ValueError(f"case {case.id} is outside the open-target study ABI")

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

        max_model_calls = case.resources.get("max_model_calls")
        if max_model_calls != 14:
            raise ValueError(f"case {case.id} must declare max_model_calls=14")

        forbidden_coverage = _forbidden_key_paths(
            case.coverage, forbidden=COVERAGE_FORBIDDEN_KEYS
        )
        declaration_coverage = _declaration_values(case.coverage)
        if forbidden_coverage or declaration_coverage:
            leaked = sorted(forbidden_coverage | declaration_coverage)
            raise ValueError(
                f"case {case.id} coverage contains target/route oracle data: "
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

    return cases

