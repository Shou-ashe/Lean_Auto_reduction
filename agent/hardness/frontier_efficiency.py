"""Independent Stage-J contract for reducing ineffective frontier queries."""

from __future__ import annotations

import json
from collections import Counter
from collections.abc import Mapping, Sequence
from typing import Any

from .benchmark import BenchmarkCase, BenchmarkSuite
from .frontier_guidance import frontier_guidance_errors
from .model_client import ModelResponse, extract_json_object
from .open_target import (
    COVERAGE_FORBIDDEN_KEYS,
    _declaration_values,
    _forbidden_key_paths,
)


FRONTIER_EFFICIENCY_SUITE_ID = "frontier-efficiency"
FRONTIER_EFFICIENCY_CASE_COUNT = 8
FRONTIER_EFFICIENCY_POSITIVE_COUNT = 4
FRONTIER_EFFICIENCY_NEGATIVE_COUNT = 4
FRONTIER_EFFICIENCY_MODULE = "Benchmark.Hardness.Inputs.StageIExpansion"
FRONTIER_EFFICIENCY_MAX_MODEL_CALLS = 12

EXPECTED_CASES: Mapping[
    str,
    tuple[str, str, int, int, int, str | None],
] = {
    "frontier-tagged-presented-long-hardness": (
        f"{FRONTIER_EFFICIENCY_MODULE}.taggedPresented",
        "presented_problem",
        5,
        5,
        16,
        None,
    ),
    "frontier-tagged-predicate-long-hardness": (
        f"{FRONTIER_EFFICIENCY_MODULE}.taggedPredicate",
        "predicate",
        5,
        5,
        16,
        None,
    ),
    "frontier-set-covering-presented-long-hardness": (
        f"{FRONTIER_EFFICIENCY_MODULE}.setCoveringPresented",
        "presented_problem",
        5,
        6,
        16,
        None,
    ),
    "frontier-set-covering-predicate-long-hardness": (
        f"{FRONTIER_EFFICIENCY_MODULE}.setCoveringPredicate",
        "predicate",
        5,
        6,
        16,
        None,
    ),
    "frontier-no-eligible-transport-dependency-limit": (
        f"{FRONTIER_EFFICIENCY_MODULE}.taggedPresented",
        "presented_problem",
        5,
        5,
        2,
        "no_eligible_hardness_target",
    ),
    "frontier-forward-route-absent": (
        f"{FRONTIER_EFFICIENCY_MODULE}.disconnectedGraphPresented",
        "presented_problem",
        1,
        6,
        16,
        "eligible_target_has_no_existing_route",
    ),
    "frontier-reverse-only-hard-target": (
        f"{FRONTIER_EFFICIENCY_MODULE}.reverseOnlyHardPresented",
        "presented_problem",
        1,
        6,
        16,
        "eligible_target_has_no_existing_route",
    ),
    "frontier-ambiguous-predicate-presentation": (
        f"{FRONTIER_EFFICIENCY_MODULE}.ambiguousPartitionPredicate",
        "predicate",
        1,
        6,
        16,
        "ambiguous_predicate_presentation",
    ),
}


def validate_frontier_efficiency_suite(
    suite: BenchmarkSuite,
) -> tuple[BenchmarkCase, ...]:
    """Enforce a target-free, route-free matched workload for Stage J."""

    cases = suite.cases
    if suite.id != FRONTIER_EFFICIENCY_SUITE_ID:
        raise ValueError(
            f"expected suite {FRONTIER_EFFICIENCY_SUITE_ID}, got {suite.id}"
        )
    if len(cases) != FRONTIER_EFFICIENCY_CASE_COUNT:
        raise ValueError(
            "frontier-efficiency suite must contain exactly eight cases"
        )
    if {case.id for case in cases} != set(EXPECTED_CASES):
        raise ValueError("frontier-efficiency case IDs drifted from the Stage-J contract")
    counts = Counter(case.expected.final_status for case in cases)
    if (
        counts["VERIFIED"] != FRONTIER_EFFICIENCY_POSITIVE_COUNT
        or counts["BLOCKED"] != FRONTIER_EFFICIENCY_NEGATIVE_COUNT
    ):
        raise ValueError(
            "frontier-efficiency suite must contain four positives and four negatives"
        )

    for case in cases:
        declaration, input_kind, minimum, maximum, dependencies, failure = (
            EXPECTED_CASES[case.id]
        )
        if (
            case.module != FRONTIER_EFFICIENCY_MODULE
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
            or case.evaluation_lane != "frontier_efficiency"
            or case.authoring_policy != {"enabled": False, "mode": "disabled"}
            or case.group_id is not None
            or case.matched_pair_id is not None
            or case.comparison_group_id is not None
            or case.family_id is not None
            or case.source_form_id is not None
            or case.target_form_id is not None
            or case.hub_ids
        ):
            raise ValueError(f"case {case.id} is outside the Stage-J public ABI")
        if case.resources.get("max_model_calls") != FRONTIER_EFFICIENCY_MAX_MODEL_CALLS:
            raise ValueError(
                f"case {case.id} must declare max_model_calls="
                f"{FRONTIER_EFFICIENCY_MAX_MODEL_CALLS}"
            )
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
            raise ValueError("Stage-J Expected records may contain only final outcome")
    return cases


def _normalize_action(payload: dict[str, Any]) -> dict[str, Any]:
    if isinstance(payload.get("action"), str):
        return payload
    candidates: list[dict[str, Any]] = []
    for action in (
        "inspect_architecture",
        "search_problems",
        "search_connections",
        "search_hardness_targets",
        "search_reductions",
        "finish",
        "stop",
    ):
        nested = payload.get(action)
        if isinstance(nested, dict):
            candidate = dict(nested)
            candidate.setdefault("action", action)
            candidates.append(candidate)
    return candidates[0] if len(candidates) == 1 else payload


def _search_signature(search: Mapping[str, Any]) -> str:
    return json.dumps(search, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def analyze_frontier_interactions(
    *,
    prompts: Sequence[str],
    responses: Sequence[ModelResponse],
) -> dict[str, Any]:
    """Measure whether model actions used the public Stage-J guidance."""

    if len(prompts) != len(responses):
        raise ValueError("frontier interaction prompt/response counts differ")
    guidance_errors: list[str] = []
    seen_searches: set[str] = set()
    repeated_searches = 0
    guidance_rounds = 0
    suggested_rounds = 0
    followed_rounds = 0
    source_only_actions = 0
    target_filtered_actions = 0
    terminal_counts: Counter[str] = Counter()
    terminal_followed: Counter[str] = Counter()
    terminal_ignored = 0

    for turn, (prompt, response) in enumerate(
        zip(prompts, responses, strict=True), start=1
    ):
        payload = json.loads(prompt)
        if not isinstance(payload, dict):
            raise ValueError("frontier interaction prompt is not an object")
        guidance_errors.extend(
            f"turn {turn}: {error}" for error in frontier_guidance_errors(payload)
        )
        guidance = payload.get("frontier_guidance")
        suggested_nodes: set[str] = set()
        if isinstance(guidance, Mapping):
            guidance_rounds += 1
            raw_suggestions = guidance.get("suggested_searches")
            if isinstance(raw_suggestions, list) and raw_suggestions:
                suggested_rounds += 1
                for search in raw_suggestions:
                    if not isinstance(search, Mapping):
                        continue
                    nodes = search.get("source_node_ids")
                    if isinstance(nodes, list):
                        suggested_nodes.update(
                            str(node) for node in nodes if isinstance(node, str)
                        )

        raw_action = extract_json_object(response.content)
        action_payload = _normalize_action(raw_action) if raw_action is not None else {}
        action = action_payload.get("action")
        terminal = payload.get("terminal_guidance")
        if isinstance(terminal, Mapping) and isinstance(terminal.get("mode"), str):
            mode = str(terminal["mode"])
            terminal_counts[mode] += 1
            expected_action = "finish" if mode == "finish_now" else "stop"
            if action == expected_action:
                terminal_followed[mode] += 1
            else:
                terminal_ignored += 1

        if action != "search_reductions":
            continue
        searches = action_payload.get("searches")
        if not isinstance(searches, list):
            continue
        requested_nodes: set[str] = set()
        all_source_only = bool(searches)
        action_target_filtered = False
        for search in searches:
            if not isinstance(search, Mapping):
                all_source_only = False
                continue
            signature = _search_signature(search)
            if signature in seen_searches:
                repeated_searches += 1
            seen_searches.add(signature)
            sources = search.get("source_node_ids")
            if isinstance(sources, list):
                requested_nodes.update(
                    str(node) for node in sources if isinstance(node, str)
                )
            targets = search.get("target_node_ids")
            if isinstance(targets, list) and targets:
                action_target_filtered = True
            if any(
                search.get(field)
                for field in (
                    "target_node_ids",
                    "terms",
                    "namespace_prefixes",
                    "roles",
                    "representation_terms",
                    "semantic_terms",
                )
            ):
                all_source_only = False
        if all_source_only:
            source_only_actions += 1
        if action_target_filtered:
            target_filtered_actions += 1
        if suggested_nodes and requested_nodes and requested_nodes.issubset(suggested_nodes):
            followed_rounds += 1

    return {
        "frontier_guidance_round_count": guidance_rounds,
        "frontier_guidance_error_count": len(guidance_errors),
        "frontier_guidance_errors": guidance_errors,
        "frontier_suggestion_round_count": suggested_rounds,
        "frontier_suggestion_followed_round_count": followed_rounds,
        "source_only_reduction_search_action_count": source_only_actions,
        "target_filtered_reduction_search_action_count": target_filtered_actions,
        "repeated_reduction_search_count": repeated_searches,
        "terminal_guidance_counts": dict(sorted(terminal_counts.items())),
        "terminal_guidance_followed_counts": dict(sorted(terminal_followed.items())),
        "terminal_guidance_ignored_count": terminal_ignored,
    }
