"""Planning entry points over validated Lean capability snapshots.

``HardnessPlan`` is the extensible planning record.  The route selector and
``generate_lean_path_with_deepseek`` remain narrow compatibility/execution
adapters for the current existing-reduction benchmark profile; they are not the
core Agent ABI.  Model output carries no proof authority.
"""

from __future__ import annotations

import json
import re
from collections.abc import Mapping
from dataclasses import dataclass
from typing import Any

from .catalog import FLAT_API_CATALOG
from .model_client import DeepSeekClient, ModelResponse, extract_json_object
from .models import PlannerDecision, RouteCandidate, TypedCatalog, TypedInventoryEntry
from .plan import (
    PLAN_OUTPUT_SCHEMA,
    PLAN_SCHEMA,
    PLAN_STEP_SCHEMA,
    HardnessPlan,
    PlanValidationError,
    parse_hardness_plan,
)
from .plan_profiles import (
    EXISTING_REDUCTION_OUTPUT_ID,
    EXISTING_REDUCTION_PROFILE,
    validate_existing_reduction_profile,
)
from .retrieval import (
    MAX_ARCHITECTURE_QUERIES_PER_ROUND,
    MAX_ARCHITECTURE_RESULTS_PER_QUERY,
    MAX_ARCHITECTURE_RESULTS_PER_ROUND,
    MAX_NODE_IDS_PER_SEARCH,
    MAX_PREFIXES_PER_SEARCH,
    MAX_RESULTS_PER_ROUND,
    MAX_RESULTS_PER_SEARCH,
    MAX_ROLES_PER_SEARCH,
    MAX_SEARCHES_PER_ROUND,
    MAX_TERMS_PER_SEARCH,
    RetrievalValidationError,
    analyze_retrieved_connectivity,
    build_library_architecture,
    build_navigation_hints,
    entry_summary,
    inspect_library_architecture,
    parse_architecture_queries,
    parse_theorem_searches,
    search_catalog,
)


DETERMINISTIC_PLANNER = "deterministic"
DEEPSEEK_PLANNER = "deepseek"
PLANNER_MODES = {DETERMINISTIC_PLANNER, DEEPSEEK_PLANNER}
MAX_MODEL_ROUTE_ATOMS = 8
MAX_MODEL_LEAN_TERM_CHARS = 12000
MAX_MODEL_RETRIEVAL_ROUNDS = 4
MAX_RETRIEVED_DECLARATIONS = 20
MAX_MODEL_PROTOCOL_REPAIRS = 2

DEEPSEEK_ROUTE_SYSTEM_PROMPT = """You select a reduction path from a closed allowlist.
Return one JSON object only. Never invent declarations, Lean code, proofs, adapters,
or reversed edges. The returned declaration order must form a source-to-target path.
Lean will independently reject any invalid composition."""

DEEPSEEK_LEAN_SYSTEM_PROMPT = """You navigate a compiled Lean theorem index and
write one Lean CertifiedPath expression. Return one JSON object only. The prompt gives
a compact library overview and focused namespace directions near the current frontier
and target, not the full library topology. You decide what to retrieve. If the focused
hints are insufficient, use inspect_architecture to ask the agent for a few additional
namespace transitions; those results are navigation facts, not theorem declarations.
Then use search to retrieve real compiled declarations. Never guess or use an
unretrieved declaration. A search object's source_node_ids and target_node_ids
constrain the two endpoints of each single returned theorem, not the endpoints of an
entire multi-edge route. To find a multi-edge route, search from the request source or
current frontier and follow equal endpoint node IDs. Namespace, role, and node fields
are hard filters, so omit uncertain filters. Finish only with one declaration sequence
listed in retrieved_connectivity.complete_paths. Return that sequence plus a Lean
term; do not repeat a general plan schema. Every CertifiedReduction must be wrapped
with CertifiedPath.step, including a one-edge path. Do not use sorry, admit, axioms,
imports, commands, new definitions, reversed edges, or new mathematical reductions.
Lean checks the combined artifact once at the end."""

BANNED_MODEL_TERM_RE = re.compile(
    r"(?:\b(?:sorry|admit|sorryAx|axiom)\b|--|/-|-/|"
    r"(?im:^\s*(?:import|namespace|section|end|open|set_option|"
    r"def|theorem|lemma|example|#)))"
)


@dataclass(frozen=True)
class PlannerResult:
    route: RouteCandidate | None
    decision: PlannerDecision
    model_prompt: str | None = None
    model_response: ModelResponse | None = None
    protocol_accepted: bool = False


@dataclass(frozen=True)
class LeanCodePlannerResult:
    lean_term: str | None
    declarations: tuple[str, ...]
    plan: HardnessPlan | None
    decision: PlannerDecision
    model_prompt: str
    model_response: ModelResponse
    protocol_accepted: bool = False
    model_prompts: tuple[str, ...] = ()
    model_responses: tuple[ModelResponse, ...] = ()
    retrieval_trace: tuple[Mapping[str, Any], ...] = ()
    retrieved_declarations: tuple[str, ...] = ()
    model_lean_term: str | None = None
    lean_term_normalized: bool = False


def build_deepseek_route_prompt(
    *,
    catalog: TypedCatalog,
    source_declaration: str,
    source_display: str,
    source_node_id: str = "",
    target_declaration: str,
    target_display: str,
    target_node_id: str = "",
) -> str:
    entries = [
        {
            "declaration": entry.declaration,
            "role": entry.component_role,
            "source": entry.source_display,
            "target": entry.target_display,
            "source_fingerprint": entry.source_fingerprint,
            "target_fingerprint": entry.target_fingerprint,
        }
        for entry in catalog.entries
        if entry.capability_kind == "certified_reduction"
    ]
    payload = {
        "task": "select_existing_certified_reduction_path",
        "catalog_mode": catalog.mode,
        "catalog_id": catalog.catalog_id,
        "registry_fingerprint": catalog.registry_fingerprint,
        "request": {
            "source_declaration": source_declaration,
            "source_display": source_display,
            "source_node_id": source_node_id,
            "target_declaration": target_declaration,
            "target_display": target_display,
            "target_node_id": target_node_id,
        },
        "constraints": {
            "ordered_source_to_target": True,
            "declarations_must_come_from_catalog": True,
            "maximum_atoms": MAX_MODEL_ROUTE_ATOMS,
            "flat_api_requires_exactly_one_atom": catalog.mode == FLAT_API_CATALOG,
            "definitionally_equal_aliases_may_have_different_names": True,
        },
        "catalog_entries": entries,
        "response_schema": {
            "atoms": ["Fully.Qualified.Declaration"],
            "reason": "short explanation",
        },
    }
    return json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def build_deepseek_lean_prompt(
    *,
    catalog: TypedCatalog,
    source_declaration: str,
    source_display: str,
    source_node_id: str = "",
    target_declaration: str,
    target_display: str,
    target_node_id: str = "",
    benchmark_context: Mapping[str, Any] | None = None,
    retrieved_entries: tuple[TypedInventoryEntry, ...] = (),
    search_history: tuple[Mapping[str, Any], ...] = (),
    round_index: int = 1,
    maximum_rounds: int = MAX_MODEL_RETRIEVAL_ROUNDS,
    search_rounds_used: int = 0,
    protocol_feedback: tuple[Mapping[str, Any], ...] = (),
) -> str:
    """Build one model turn for search-driven Lean code generation."""

    expected_type = (
        "ComplexityReduction.Certificate.CertifiedPath "
        f"{source_declaration} {target_declaration}"
    )
    connectivity = analyze_retrieved_connectivity(
        retrieved_entries,
        source_node_id=source_node_id,
        target_node_id=target_node_id,
    )
    frontier_node_ids = tuple(connectivity.get("frontier_node_ids", ()))
    if not frontier_node_ids and not retrieved_entries and source_node_id:
        frontier_node_ids = (source_node_id,)
    payload = {
        "task": "retrieve_existing_reductions_and_write_lean_path",
        "execution_profile": {
            "profile_id": EXISTING_REDUCTION_PROFILE,
            "scope": "reuse compiled certified reductions only",
            "model_output": "ordered declarations plus one Lean term",
            "internal_record": (
                "the agent converts an accepted response to HardnessPlan; "
                "do not output the general plan schema"
            ),
        },
        "catalog_mode": catalog.mode,
        "catalog_id": catalog.catalog_id,
        "registry_fingerprint": catalog.registry_fingerprint,
        "expected_type": expected_type,
        "request": {
            "source_declaration": source_declaration,
            "source_display": source_display,
            "source_node_id": source_node_id,
            "target_declaration": target_declaration,
            "target_display": target_display,
            "target_node_id": target_node_id,
        },
        "benchmark_context": dict(benchmark_context or {}),
        "library_architecture": build_library_architecture(catalog),
        "navigation_hints": build_navigation_hints(
            catalog,
            frontier_node_ids=frontier_node_ids,
            target_node_id=target_node_id,
        ),
        "retrieval_state": {
            "model_turn": round_index,
            "maximum_query_rounds": maximum_rounds,
            "query_rounds_used": search_rounds_used,
            "query_rounds_remaining": maximum_rounds - search_rounds_used,
            "architecture_inspection_and_theorem_search_share_this_budget": True,
            "a_finish_turn_is_allowed_after_the_last_query": True,
            "retrieved_declaration_count": len(retrieved_entries),
            "maximum_retrieved_declarations": MAX_RETRIEVED_DECLARATIONS,
            "maximum_results_per_search_round": MAX_RESULTS_PER_ROUND,
            "must_search_before_finish": not retrieved_entries,
            "may_finish_if_the_retrieved_path_is_complete": bool(
                connectivity.get("complete_paths")
            ),
            "only_retrieved_declarations_may_appear_in_the_final_output": True,
            "search_index_scope": (
                "certified reduction declarations under ComplexityReduction only"
            ),
            "benchmark_or_input_definitions_are_not_searchable": True,
        },
        "protocol_feedback": list(protocol_feedback),
        "search_history": list(search_history),
        "retrieved_entries": [entry_summary(entry) for entry in retrieved_entries],
        "retrieved_connectivity": connectivity,
        "search_api": {
            "architecture_inspection": {
                "maximum_query_objects_per_turn": (
                    MAX_ARCHITECTURE_QUERIES_PER_ROUND
                ),
                "maximum_results_per_query": MAX_ARCHITECTURE_RESULTS_PER_QUERY,
                "maximum_results_per_turn": MAX_ARCHITECTURE_RESULTS_PER_ROUND,
                "returns_theorem_declarations": False,
            },
            "theorem_search": {
                "maximum_search_objects_per_turn": MAX_SEARCHES_PER_ROUND,
                "maximum_results_per_search": MAX_RESULTS_PER_SEARCH,
                "maximum_results_per_turn": MAX_RESULTS_PER_ROUND,
                "returns_theorem_declarations": True,
            },
            "maximum_search_objects_per_turn": MAX_SEARCHES_PER_ROUND,
            "maximum_terms_per_search": MAX_TERMS_PER_SEARCH,
            "maximum_namespace_prefixes_per_search": MAX_PREFIXES_PER_SEARCH,
            "maximum_roles_per_search": MAX_ROLES_PER_SEARCH,
            "maximum_source_or_target_node_ids_per_search": (
                MAX_NODE_IDS_PER_SEARCH
            ),
            "maximum_results_per_search": MAX_RESULTS_PER_SEARCH,
            "filter_semantics": {
                "namespace_prefixes_roles_and_node_ids": "hard AND filters",
                "terms": (
                    "text ranking hints when structural filters are present; "
                    "otherwise at least one term must match"
                ),
                "source_and_target_together": (
                    "request a single direct theorem with exactly those endpoints"
                ),
                "multi_edge_route": (
                    "use separate search objects or successive turns, following "
                    "the frontier node IDs"
                ),
            },
        },
        "lean_syntax_examples": {
            "one_edge": (
                "ComplexityReduction.Certificate.CertifiedPath.step "
                "FIRST_REDUCTION_DECLARATION"
            ),
            "multiple_edges_correct": (
                "ComplexityReduction.Certificate.CertifiedPath.cons "
                "(ComplexityReduction.Certificate.CertifiedPath.step "
                "FIRST_REDUCTION_DECLARATION) SECOND_REDUCTION_DECLARATION"
            ),
            "multiple_edges_wrong": (
                "Do not wrap SECOND_REDUCTION_DECLARATION with "
                "CertifiedPath.step; cons expects a CertifiedReduction there"
            ),
        },
        "constraints": {
            "return_ordered_declarations_and_one_term": True,
            "ordered_source_to_target": True,
            "declarations_must_have_been_returned_by_search": True,
            "maximum_declarations": MAX_MODEL_ROUTE_ATOMS,
            "flat_api_requires_exactly_one_declaration": (
                catalog.mode == FLAT_API_CATALOG
            ),
            "new_reductions_forbidden": True,
            "sorry_admit_axiom_forbidden": True,
            "definitionally_equal_endpoint_aliases_are_allowed": True,
            "use_the_literal_fully_qualified_constructor_names_from_examples": True,
            "one_edge_and_append_edge_are_not_lean_identifiers": True,
            "finish_requires_a_listed_complete_path_when_topology_is_available": True,
            "single_edge_still_requires_CertifiedPath_step": True,
            "only_the_first_edge_is_wrapped_with_step": True,
            "later_cons_arguments_are_raw_reduction_declarations": True,
        },
        "response_options": {
            "inspect_architecture": {
                "action": "inspect_architecture",
                "queries": [
                    {
                        "terms": ["optional semantic namespace words"],
                        "namespace_prefixes": ["optional library root or namespace"],
                        "roles": ["optional reduction roles"],
                        "source_node_ids": ["optional exact transition source nodes"],
                        "target_node_ids": ["optional exact transition target nodes"],
                        "limit": 8,
                    }
                ],
                "reason": (
                    "why the compact overview and focused hints are insufficient"
                ),
            },
            "search": {
                "action": "search",
                "searches": [
                    {
                        "terms": ["semantic words chosen by you"],
                        "namespace_prefixes": [
                            "narrow namespace copied from focused or inspected hints"
                        ],
                        "roles": [
                            "optional ingress/sharedGadget/egress/finalComposition"
                        ],
                        "source_node_ids": [
                            "optional exact node IDs, especially request/frontier nodes"
                        ],
                        "target_node_ids": ["optional exact destination node IDs"],
                        "limit": 8,
                    }
                ],
                "reason": "why these searches may reveal every edge of a complete path",
            },
            "finish": {
                "action": "finish",
                "declarations": [
                    "copy one complete path from retrieved_connectivity.complete_paths"
                ],
                "lean_term": "Lean expression of the exact expected_type",
                "reason": "why the retrieved declarations form the complete path",
            },
        },
    }
    return json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def _normalize_model_action_payload(payload: dict[str, Any]) -> dict[str, Any]:
    """Accept one harmless extra wrapper around a supported model action."""

    if payload.get("action") is not None:
        return payload
    candidates: list[dict[str, Any]] = []
    for action in ("inspect_architecture", "search", "finish"):
        nested = payload.get(action)
        if isinstance(nested, dict):
            normalized = dict(nested)
            normalized.setdefault("action", action)
            candidates.append(normalized)
    return candidates[0] if len(candidates) == 1 else payload


def _deepseek_failure(
    *, prompt: str, response: ModelResponse, error: str
) -> PlannerResult:
    return PlannerResult(
        route=None,
        decision=PlannerDecision(
            mode=DEEPSEEK_PLANNER,
            selected_route_id=None,
            reason="DeepSeek did not return an accepted allowlisted route",
            model_called=response.called,
            model_ok=False,
            model_error=error,
            model_usage=response.usage,
        ),
        model_prompt=prompt,
        model_response=response,
        protocol_accepted=False,
    )


def choose_route_with_deepseek(
    *,
    catalog: TypedCatalog,
    source_declaration: str,
    source_display: str,
    target_declaration: str,
    target_display: str,
    client: DeepSeekClient,
) -> PlannerResult:
    """Ask DeepSeek to select only existing catalog declarations.

    This validates the response protocol and allowlist membership only.  Exact
    endpoint composition remains a Lean-kernel obligation of the emitted path.
    """

    prompt = build_deepseek_route_prompt(
        catalog=catalog,
        source_declaration=source_declaration,
        source_display=source_display,
        target_declaration=target_declaration,
        target_display=target_display,
    )
    response = client.complete_json(
        system=DEEPSEEK_ROUTE_SYSTEM_PROMPT,
        prompt=prompt,
    )
    if not response.ok:
        return _deepseek_failure(
            prompt=prompt,
            response=response,
            error=response.error or "DeepSeek request failed",
        )

    payload = extract_json_object(response.content)
    if payload is None:
        return _deepseek_failure(
            prompt=prompt,
            response=response,
            error="DeepSeek response is not a JSON object",
        )
    atoms_value = payload.get("atoms")
    if (
        not isinstance(atoms_value, list)
        or not atoms_value
        or any(not isinstance(atom, str) or not atom for atom in atoms_value)
    ):
        return _deepseek_failure(
            prompt=prompt,
            response=response,
            error="DeepSeek response must contain a non-empty string atoms list",
        )
    atoms = tuple(atoms_value)
    if len(atoms) > MAX_MODEL_ROUTE_ATOMS:
        return _deepseek_failure(
            prompt=prompt,
            response=response,
            error=f"DeepSeek route exceeds the {MAX_MODEL_ROUTE_ATOMS}-atom limit",
        )
    if len(set(atoms)) != len(atoms):
        return _deepseek_failure(
            prompt=prompt,
            response=response,
            error="DeepSeek route repeats a declaration",
        )
    if catalog.mode == FLAT_API_CATALOG and len(atoms) != 1:
        return _deepseek_failure(
            prompt=prompt,
            response=response,
            error="flat_api route selection requires exactly one declaration",
        )

    entries = {
        entry.declaration: entry
        for entry in catalog.entries
        if entry.capability_kind == "certified_reduction"
    }
    unknown = [atom for atom in atoms if atom not in entries]
    if unknown:
        return _deepseek_failure(
            prompt=prompt,
            response=response,
            error="DeepSeek selected a declaration outside the catalog allowlist",
        )

    roles = tuple(entries[atom].component_role for atom in atoms)
    route = RouteCandidate(
        target_declaration=target_declaration,
        membership_declaration=None,
        atoms=atoms,
        roles=roles,
        final_composition_edges=sum(role == "finalComposition" for role in roles),
        registry_fingerprint=catalog.registry_fingerprint,
        probe_route_key="deepseek_catalog_selection",
        evidence_kind="reduction",
    )
    reason = payload.get("reason")
    rendered_reason = (
        reason.strip()[:1000]
        if isinstance(reason, str) and reason.strip()
        else "DeepSeek selected an allowlisted route"
    )
    return PlannerResult(
        route=route,
        decision=PlannerDecision(
            mode=DEEPSEEK_PLANNER,
            selected_route_id=route.route_id,
            reason=rendered_reason,
            model_called=response.called,
            model_ok=True,
            model_error=None,
            model_usage=response.usage,
        ),
        model_prompt=prompt,
        model_response=response,
        protocol_accepted=True,
    )


def _aggregate_response_usage(
    responses: tuple[ModelResponse, ...],
) -> dict[str, int] | None:
    totals: dict[str, int] = {}
    for response in responses:
        if not isinstance(response.usage, dict):
            continue
        for key, value in response.usage.items():
            if isinstance(value, int) and not isinstance(value, bool):
                totals[key] = totals.get(key, 0) + value
    return dict(sorted(totals.items())) or None


def _lean_code_failure(
    *,
    prompt: str,
    response: ModelResponse,
    error: str,
    prompts: tuple[str, ...] = (),
    responses: tuple[ModelResponse, ...] = (),
    retrieval_trace: tuple[Mapping[str, Any], ...] = (),
    retrieved_declarations: tuple[str, ...] = (),
) -> LeanCodePlannerResult:
    recorded_prompts = prompts or (prompt,)
    recorded_responses = responses or (response,)
    return LeanCodePlannerResult(
        lean_term=None,
        declarations=(),
        plan=None,
        decision=PlannerDecision(
            mode=DEEPSEEK_PLANNER,
            selected_route_id=None,
            reason="DeepSeek did not return an accepted Lean CertifiedPath term",
            model_called=any(item.called for item in recorded_responses),
            model_ok=False,
            model_error=error,
            model_usage=_aggregate_response_usage(recorded_responses),
        ),
        model_prompt=prompt,
        model_response=response,
        protocol_accepted=False,
        model_prompts=recorded_prompts,
        model_responses=recorded_responses,
        retrieval_trace=retrieval_trace,
        retrieved_declarations=retrieved_declarations,
    )


def _build_existing_reduction_plan_payload(
    *,
    catalog: TypedCatalog,
    source_declaration: str,
    target_declaration: str,
    declarations: list[str],
    lean_term: str,
    adapter_source: str,
) -> dict[str, Any]:
    """Adapt the small codegen response into the general internal plan record."""

    entries = {entry.declaration: entry for entry in catalog.entries}
    return {
        "schema_version": PLAN_SCHEMA,
        "objective": "reduce_to",
        "source_declaration": source_declaration,
        "target_declaration": target_declaration,
        "registry_fingerprint": catalog.registry_fingerprint,
        "catalog_id": catalog.catalog_id,
        "metadata": {"adapted_from": adapter_source},
        "steps": [
            {
                "schema_version": PLAN_STEP_SCHEMA,
                "step_id": f"s{index}",
                "action_kind": "reuse.certified_reduction",
                "capability_kind": "certified_reduction",
                "declaration": declaration,
                "depends_on": [] if index == 1 else [f"s{index - 1}"],
                "role": (
                    entries[declaration].component_role
                    if declaration in entries
                    else None
                ),
            }
            for index, declaration in enumerate(declarations, start=1)
        ],
        "outputs": [
            {
                "schema_version": PLAN_OUTPUT_SCHEMA,
                "output_id": EXISTING_REDUCTION_OUTPUT_ID,
                "output_kind": "lean.term",
                "producer_steps": [
                    f"s{index}" for index in range(1, len(declarations) + 1)
                ],
                "expected_type": (
                    "ComplexityReduction.Certificate.CertifiedPath "
                    f"{source_declaration} {target_declaration}"
                ),
                "lean_code": lean_term,
            }
        ],
    }


def _declarations_appear_in_order(lean_term: str, declarations: list[str]) -> bool:
    position = 0
    for declaration in declarations:
        next_position = lean_term.find(declaration, position)
        if next_position < 0:
            return False
        position = next_position + len(declaration)
    return True


def _lean_term_mentions_declaration(lean_term: str, declaration: str) -> bool:
    return bool(
        re.search(
            rf"(?<![A-Za-z0-9_.']){re.escape(declaration)}(?![A-Za-z0-9_.'])",
            lean_term,
        )
    )


def _canonical_certified_path_term(declarations: tuple[str, ...]) -> str:
    term = (
        "ComplexityReduction.Certificate.CertifiedPath.step "
        f"{declarations[0]}"
    )
    for declaration in declarations[1:]:
        term = (
            "ComplexityReduction.Certificate.CertifiedPath.cons "
            f"({term}) {declaration}"
        )
    return term


def _all_edges_wrapped_path_term(declarations: tuple[str, ...]) -> str:
    term = (
        "ComplexityReduction.Certificate.CertifiedPath.step "
        f"{declarations[0]}"
    )
    for declaration in declarations[1:]:
        term = (
            "ComplexityReduction.Certificate.CertifiedPath.cons "
            f"({term}) "
            "(ComplexityReduction.Certificate.CertifiedPath.step "
            f"{declaration})"
        )
    return term


def _normalize_path_constructor_shape(
    lean_term: str, declarations: tuple[str, ...]
) -> tuple[str, bool]:
    """Repair only the exact redundant-step wrapper shape."""

    if len(declarations) < 2:
        return lean_term, False
    compact = re.sub(r"\s+", " ", lean_term).strip()
    redundant = re.sub(
        r"\s+", " ", _all_edges_wrapped_path_term(declarations)
    ).strip()
    if compact != redundant:
        return lean_term, False
    return _canonical_certified_path_term(declarations), True


def generate_lean_path_with_deepseek(
    *,
    catalog: TypedCatalog,
    source_declaration: str,
    source_display: str,
    source_node_id: str = "",
    target_declaration: str,
    target_display: str,
    target_node_id: str = "",
    client: DeepSeekClient,
    benchmark_context: Mapping[str, Any] | None = None,
    maximum_retrieval_rounds: int = MAX_MODEL_RETRIEVAL_ROUNDS,
) -> LeanCodePlannerResult:
    """Let DeepSeek retrieve declarations and then author the Lean path term.

    This function deliberately does not invoke Lean.  The complete benchmark
    artifact is elaborated exactly once after every model call has completed.
    """
    if not 1 <= maximum_retrieval_rounds <= 8:
        raise ValueError("maximum_retrieval_rounds must be in 1..8")

    prompts: list[str] = []
    responses: list[ModelResponse] = []
    search_history: list[Mapping[str, Any]] = []
    protocol_feedback: list[Mapping[str, Any]] = []
    retrieved: dict[str, TypedInventoryEntry] = {}
    payload: dict[str, Any] | None = None
    prompt = ""
    response: ModelResponse | None = None
    search_rounds_used = 0
    protocol_repair_count = 0
    maximum_model_turns = (
        maximum_retrieval_rounds + MAX_MODEL_PROTOCOL_REPAIRS + 1
    )

    def record_protocol_error(*, model_turn: int, message: str) -> bool:
        nonlocal protocol_repair_count
        protocol_repair_count += 1
        row = {
            "model_turn": model_turn,
            "status": "rejected_model_action",
            "validation_error": message,
        }
        protocol_feedback.append(row)
        search_history.append(row)
        return protocol_repair_count <= MAX_MODEL_PROTOCOL_REPAIRS

    for model_turn in range(1, maximum_model_turns + 1):
        prompt = build_deepseek_lean_prompt(
            catalog=catalog,
            source_declaration=source_declaration,
            source_display=source_display,
            source_node_id=source_node_id,
            target_declaration=target_declaration,
            target_display=target_display,
            target_node_id=target_node_id,
            benchmark_context=benchmark_context,
            retrieved_entries=tuple(retrieved.values()),
            search_history=tuple(search_history),
            round_index=model_turn,
            maximum_rounds=maximum_retrieval_rounds,
            search_rounds_used=search_rounds_used,
            protocol_feedback=tuple(protocol_feedback),
        )
        response = client.complete_json(
            system=DEEPSEEK_LEAN_SYSTEM_PROMPT, prompt=prompt
        )
        prompts.append(prompt)
        responses.append(response)
        recorded_prompts = tuple(prompts)
        recorded_responses = tuple(responses)
        recorded_trace = tuple(search_history)
        retrieved_names = tuple(retrieved)
        if not response.ok:
            return _lean_code_failure(
                prompt=prompt,
                response=response,
                error=response.error or "DeepSeek request failed",
                prompts=recorded_prompts,
                responses=recorded_responses,
                retrieval_trace=recorded_trace,
                retrieved_declarations=retrieved_names,
            )
        candidate_payload = extract_json_object(response.content)
        if candidate_payload is None:
            message = "response is not a JSON object"
            if record_protocol_error(model_turn=model_turn, message=message):
                continue
            return _lean_code_failure(
                prompt=prompt,
                response=response,
                error=f"DeepSeek {message}",
                prompts=recorded_prompts,
                responses=recorded_responses,
                retrieval_trace=recorded_trace,
                retrieved_declarations=retrieved_names,
            )
        candidate_payload = _normalize_model_action_payload(candidate_payload)
        action = candidate_payload.get("action")
        if action == "inspect_architecture":
            if search_rounds_used >= maximum_retrieval_rounds:
                message = (
                    "the retrieval-query budget is exhausted; submit Lean code "
                    "from a listed complete path instead of requesting more architecture"
                )
                if record_protocol_error(model_turn=model_turn, message=message):
                    continue
                return _lean_code_failure(
                    prompt=prompt,
                    response=response,
                    error=f"DeepSeek {message}",
                    prompts=recorded_prompts,
                    responses=recorded_responses,
                    retrieval_trace=tuple(search_history),
                    retrieved_declarations=retrieved_names,
                )
            try:
                queries = parse_architecture_queries(candidate_payload)
            except RetrievalValidationError as error:
                message = f"architecture query rejected: {error}"
                if record_protocol_error(model_turn=model_turn, message=message):
                    continue
                return _lean_code_failure(
                    prompt=prompt,
                    response=response,
                    error=f"DeepSeek {message}",
                    prompts=recorded_prompts,
                    responses=recorded_responses,
                    retrieval_trace=tuple(search_history),
                    retrieved_declarations=retrieved_names,
                )
            search_rounds_used += 1
            namespace_results = inspect_library_architecture(catalog, queries)
            search_history.append(
                {
                    "round": search_rounds_used,
                    "model_turn": model_turn,
                    "status": "architecture_inspection_completed",
                    "queries": [query.to_dict() for query in queries],
                    "namespace_results": list(namespace_results),
                    "contains_declaration_names": False,
                    "reason": (
                        candidate_payload.get("reason")[:1000]
                        if isinstance(candidate_payload.get("reason"), str)
                        else None
                    ),
                }
            )
            continue
        if action == "search":
            if search_rounds_used >= maximum_retrieval_rounds:
                message = (
                    "the retrieval-query budget is exhausted; submit Lean code "
                    "from a listed complete path instead of requesting another search"
                )
                if record_protocol_error(model_turn=model_turn, message=message):
                    continue
                return _lean_code_failure(
                    prompt=prompt,
                    response=response,
                    error=f"DeepSeek {message}",
                    prompts=recorded_prompts,
                    responses=recorded_responses,
                    retrieval_trace=tuple(search_history),
                    retrieved_declarations=retrieved_names,
                )
            try:
                searches = parse_theorem_searches(candidate_payload)
            except RetrievalValidationError as error:
                message = f"theorem search rejected: {error}"
                if record_protocol_error(model_turn=model_turn, message=message):
                    continue
                return _lean_code_failure(
                    prompt=prompt,
                    response=response,
                    error=f"DeepSeek {message}",
                    prompts=recorded_prompts,
                    responses=recorded_responses,
                    retrieval_trace=recorded_trace,
                    retrieved_declarations=retrieved_names,
                )
            search_rounds_used += 1
            results = search_catalog(catalog, searches)
            room = MAX_RETRIEVED_DECLARATIONS - len(retrieved)
            added: list[str] = []
            for entry in results:
                if entry.declaration in retrieved or room <= 0:
                    continue
                retrieved[entry.declaration] = entry
                added.append(entry.declaration)
                room -= 1
            search_history.append(
                {
                    "round": search_rounds_used,
                    "model_turn": model_turn,
                    "status": "search_completed",
                    "searches": [search.to_dict() for search in searches],
                    "returned_declarations": [
                        entry.declaration for entry in results
                    ],
                    "new_declarations": added,
                    "reason": (
                        candidate_payload.get("reason")[:1000]
                        if isinstance(candidate_payload.get("reason"), str)
                        else None
                    ),
                }
            )
            continue
        if action not in {None, "finish"}:
            message = (
                "response action must be inspect_architecture, search, or finish"
            )
            if record_protocol_error(model_turn=model_turn, message=message):
                continue
            return _lean_code_failure(
                prompt=prompt,
                response=response,
                error=f"DeepSeek {message}",
                prompts=recorded_prompts,
                responses=recorded_responses,
                retrieval_trace=recorded_trace,
                retrieved_declarations=retrieved_names,
            )
        if not retrieved:
            message = (
                "must retrieve real declarations before finishing; search the "
                "namespace transitions shown in navigation_hints"
            )
            if record_protocol_error(model_turn=model_turn, message=message):
                continue
            return _lean_code_failure(
                prompt=prompt,
                response=response,
                error=f"DeepSeek {message}",
                prompts=recorded_prompts,
                responses=recorded_responses,
                retrieval_trace=recorded_trace,
                retrieved_declarations=retrieved_names,
            )
        payload = candidate_payload
        break

    if response is None:
        raise AssertionError("retrieval loop did not issue a model request")
    if payload is None:
        return _lean_code_failure(
            prompt=prompt,
            response=response,
            error=(
                "DeepSeek used all allowed retrieval-query and response-repair turns "
                "without submitting Lean code from a complete retrieved path"
            ),
            prompts=tuple(prompts),
            responses=tuple(responses),
            retrieval_trace=tuple(search_history),
            retrieved_declarations=tuple(retrieved),
        )

    raw_plan = payload.get("plan")
    if raw_plan is None:
        # The current benchmark keeps the model-facing response small.  The
        # general HardnessPlan remains an internal, backend-neutral record.
        declarations_value = payload.get("declarations")
        lean_term_value = payload.get("lean_term")
        if (
            not isinstance(declarations_value, list)
            or not declarations_value
            or any(
                not isinstance(declaration, str) or not declaration
                for declaration in declarations_value
            )
            or not isinstance(lean_term_value, str)
            or not lean_term_value.strip()
        ):
            return _lean_code_failure(
                prompt=prompt,
                response=response,
                error=(
                    "DeepSeek finish response must contain a non-empty ordered "
                    "declarations list and one Lean term"
                ),
                prompts=tuple(prompts),
                responses=tuple(responses),
                retrieval_trace=tuple(search_history),
                retrieved_declarations=tuple(retrieved),
            )
        raw_plan = _build_existing_reduction_plan_payload(
            catalog=catalog,
            source_declaration=source_declaration,
            target_declaration=target_declaration,
            declarations=declarations_value,
            lean_term=lean_term_value,
            adapter_source="existing_reduction_codegen_response_v1",
        )
    elif isinstance(raw_plan, dict):
        # Some models put the whole Lean expression into a plan step's
        # declaration field.  If the expression itself uniquely names one
        # complete retrieved path, normalize only that response-shape mistake.
        raw_steps = raw_plan.get("steps")
        known_declarations = {entry.declaration for entry in catalog.entries}
        malformed_step_declaration = (
            isinstance(raw_steps, list)
            and bool(raw_steps)
            and any(
                not isinstance(step, dict)
                or step.get("declaration") not in known_declarations
                for step in raw_steps
            )
        )
        raw_outputs = raw_plan.get("outputs")
        output_terms = (
            [
                output["lean_code"]
                for output in raw_outputs
                if isinstance(output, dict)
                and isinstance(output.get("lean_code"), str)
                and output["lean_code"].strip()
            ]
            if isinstance(raw_outputs, list)
            else []
        )
        if malformed_step_declaration and len(output_terms) == 1:
            connectivity = analyze_retrieved_connectivity(
                tuple(retrieved.values()),
                source_node_id=source_node_id,
                target_node_id=target_node_id,
            )
            matching_paths = [
                path
                for path in connectivity.get("complete_paths", [])
                if _declarations_appear_in_order(output_terms[0], path)
            ]
            if len(matching_paths) == 1:
                raw_plan = _build_existing_reduction_plan_payload(
                    catalog=catalog,
                    source_declaration=source_declaration,
                    target_declaration=target_declaration,
                    declarations=matching_paths[0],
                    lean_term=output_terms[0],
                    adapter_source="normalized_model_plan_declaration_field",
                )
    try:
        plan = parse_hardness_plan(raw_plan)
    except PlanValidationError as error:
        return _lean_code_failure(
            prompt=prompt,
            response=response,
            error=f"DeepSeek hardness plan rejected: {error}",
            prompts=tuple(prompts),
            responses=tuple(responses),
            retrieval_trace=tuple(search_history),
            retrieved_declarations=tuple(retrieved),
        )
    proposed_lean_terms = tuple(
        output.lean_code.strip()
        for output in plan.outputs
        if output.lean_code is not None
    )
    if any(len(term) > MAX_MODEL_LEAN_TERM_CHARS for term in proposed_lean_terms):
        return _lean_code_failure(
            prompt=prompt,
            response=response,
            error="DeepSeek Lean term exceeds the audit size limit",
            prompts=tuple(prompts),
            responses=tuple(responses),
            retrieval_trace=tuple(search_history),
            retrieved_declarations=tuple(retrieved),
        )
    if any(BANNED_MODEL_TERM_RE.search(term) for term in proposed_lean_terms):
        return _lean_code_failure(
            prompt=prompt,
            response=response,
            error="DeepSeek Lean term contains a forbidden command or placeholder",
            prompts=tuple(prompts),
            responses=tuple(responses),
            retrieval_trace=tuple(search_history),
            retrieved_declarations=tuple(retrieved),
        )
    try:
        view = validate_existing_reduction_profile(
            plan,
            catalog=catalog,
            source_declaration=source_declaration,
            target_declaration=target_declaration,
            maximum_steps=MAX_MODEL_ROUTE_ATOMS,
            require_single_step=catalog.mode == FLAT_API_CATALOG,
        )
    except PlanValidationError as error:
        return _lean_code_failure(
            prompt=prompt,
            response=response,
            error=f"DeepSeek hardness plan rejected: {error}",
            prompts=tuple(prompts),
            responses=tuple(responses),
            retrieval_trace=tuple(search_history),
            retrieved_declarations=tuple(retrieved),
        )
    not_retrieved = [
        declaration
        for declaration in view.declarations
        if declaration not in retrieved
    ]
    if not_retrieved:
        return _lean_code_failure(
            prompt=prompt,
            response=response,
            error="DeepSeek used a declaration that was not returned by its searches",
            prompts=tuple(prompts),
            responses=tuple(responses),
            retrieval_trace=tuple(search_history),
            retrieved_declarations=tuple(retrieved),
        )
    selected_entries = {
        entry.declaration: entry for entry in catalog.entries
    }
    if source_node_id and target_node_id:
        path_entries = [selected_entries[declaration] for declaration in view.declarations]
        topology_error: str | None = None
        if any(not entry.source_node_id or not entry.target_node_id for entry in path_entries):
            topology_error = "selected declarations have no compiled endpoint topology"
        elif path_entries[0].source_node_id != source_node_id:
            topology_error = "selected path does not start at the requested source endpoint"
        elif path_entries[-1].target_node_id != target_node_id:
            topology_error = "selected path does not reach the requested target endpoint"
        else:
            for left, right in zip(path_entries, path_entries[1:]):
                if left.target_node_id != right.source_node_id:
                    topology_error = (
                        "selected declarations are not endpoint-compatible in order"
                    )
                    break
        if topology_error is not None:
            return _lean_code_failure(
                prompt=prompt,
                response=response,
                error=f"DeepSeek hardness plan rejected: {topology_error}",
                prompts=tuple(prompts),
                responses=tuple(responses),
                retrieval_trace=tuple(search_history),
                retrieved_declarations=tuple(retrieved),
            )
    lean_term = view.lean_term.strip()
    model_lean_term = lean_term
    extra_catalog_references = [
        declaration
        for declaration in selected_entries
        if declaration not in view.declarations
        and _lean_term_mentions_declaration(lean_term, declaration)
    ]
    if extra_catalog_references:
        return _lean_code_failure(
            prompt=prompt,
            response=response,
            error=(
                "DeepSeek Lean term references catalog declarations that were not "
                "listed in its selected path"
            ),
            prompts=tuple(prompts),
            responses=tuple(responses),
            retrieval_trace=tuple(search_history),
            retrieved_declarations=tuple(retrieved),
        )
    lean_term, lean_term_normalized = _normalize_path_constructor_shape(
        lean_term, view.declarations
    )
    if len(view.declarations) == 1 and lean_term == view.declarations[0]:
        lean_term = (
            "ComplexityReduction.Certificate.CertifiedPath.step "
            f"{view.declarations[0]}"
        )
        lean_term_normalized = True
    reason = payload.get("reason")
    rendered_reason = (
        reason.strip()[:1000]
        if isinstance(reason, str) and reason.strip()
        else "DeepSeek authored an allowlisted Lean CertifiedPath term"
    )
    return LeanCodePlannerResult(
        lean_term=lean_term,
        declarations=view.declarations,
        plan=plan,
        decision=PlannerDecision(
            mode=DEEPSEEK_PLANNER,
            selected_route_id=plan.plan_id,
            reason=rendered_reason,
            model_called=any(item.called for item in responses),
            model_ok=True,
            model_error=None,
            model_usage=_aggregate_response_usage(tuple(responses)),
        ),
        model_prompt=prompt,
        model_response=response,
        protocol_accepted=True,
        model_prompts=tuple(prompts),
        model_responses=tuple(responses),
        retrieval_trace=tuple(search_history),
        retrieved_declarations=tuple(retrieved),
        model_lean_term=model_lean_term,
        lean_term_normalized=lean_term_normalized,
    )


def deterministic_routes(
    routes: tuple[RouteCandidate, ...], target_declaration: str | None = None
) -> tuple[RouteCandidate, ...]:
    """Return validated routes in the stable cost order fixed by ``RouteCandidate``."""

    selected = routes
    if target_declaration:
        selected = tuple(
            route for route in selected if route.target_declaration == target_declaration
        )
    return tuple(sorted(selected, key=lambda route: route.cost))


def choose_route(
    *,
    routes: tuple[RouteCandidate, ...],
    target_declaration: str | None,
    mode: str = DETERMINISTIC_PLANNER,
) -> PlannerResult:
    """Choose the stable minimum-cost validated route, or preserve the exact gap.

    ``mode`` remains in the API so old callers fail with an explicit migration
    error instead of silently changing semantics.  No model client or model
    response can enter this function.
    """

    if mode != DETERMINISTIC_PLANNER:
        raise ValueError(
            "route planning is deterministic; model route reranking was removed"
        )
    allowed = deterministic_routes(routes, target_declaration)
    if not allowed:
        return PlannerResult(
            route=None,
            decision=PlannerDecision(
                mode=DETERMINISTIC_PLANNER,
                selected_route_id=None,
                reason="no validated route matches the requested target",
            ),
        )
    selected = allowed[0]
    return PlannerResult(
        route=selected,
        decision=PlannerDecision(
            mode=DETERMINISTIC_PLANNER,
            selected_route_id=selected.route_id,
            reason="minimum deterministic route cost",
        ),
    )
