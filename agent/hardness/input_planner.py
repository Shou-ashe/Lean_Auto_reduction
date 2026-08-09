"""Model-driven planning from a Lean-observed input to a fixed target.

The model chooses every query, problem match, connection, and reduction.  This
module only executes bounded searches and checks that the submitted path uses
retrieved, Lean-emitted facts with compatible endpoint nodes.  It never calls
Lean during the model conversation; final elaboration remains a separate step.
"""

from __future__ import annotations

import json
import re
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from typing import Any

from .connection_catalog import (
    ConnectionCatalog,
    ConnectionCatalogEntry,
    ConnectionCatalogError,
    build_initial_connection_hints,
    connected_problem_match,
    connection_search_result,
    parse_connection_searches,
    search_connections,
)
from .input_observation import LeanInputObservation
from .model_client import DeepSeekClient, ModelResponse, extract_json_object
from .models import TypedCatalog, TypedInventoryEntry
from .plan import (
    PLAN_OUTPUT_SCHEMA,
    PLAN_SCHEMA,
    PLAN_STEP_SCHEMA,
    HardnessPlan,
    parse_hardness_plan,
)
from .planner import BANNED_MODEL_TERM_RE, MAX_MODEL_LEAN_TERM_CHARS
from .problem_catalog import (
    ProblemCatalog,
    ProblemCatalogEntry,
    ProblemCatalogError,
    ProblemMatch,
    build_initial_problem_hints,
    exact_predicate_problem_match,
    exact_problem_match,
    parse_problem_searches,
    predicate_exact_candidates,
    predicate_presentation_groups,
    problem_search_result,
    search_problems,
)
from .retrieval import (
    RetrievalValidationError,
    build_library_architecture,
    entry_summary,
    inspect_library_architecture,
    parse_architecture_queries,
    parse_theorem_searches,
    search_catalog,
)


MAX_INPUT_QUERY_ROUNDS = 8
MAX_INPUT_MODEL_TURNS = 12
MAX_INPUT_PROTOCOL_FEEDBACK = 3
MAX_RETRIEVED_PROBLEMS = 20
MAX_RETRIEVED_CONNECTIONS = 20
MAX_RETRIEVED_REDUCTIONS = 24
MAX_SELECTED_REDUCTIONS = 8

FULL_DECLARATION_RE = re.compile(
    r"(?<![A-Za-z0-9_'])"
    r"(?:[A-Z][A-Za-z0-9_']*\.)+[A-Za-z_][A-Za-z0-9_']*"
    r"(?![A-Za-z0-9_'])"
)

STATIC_PATH_DECLARATIONS = {
    "ComplexityReduction.Certificate.CertifiedPath.refl",
    "ComplexityReduction.Certificate.CertifiedPath.step",
    "ComplexityReduction.Certificate.CertifiedPath.cons",
}

RELATION_ACTION_KIND = {
    "existing_reduction": "reuse.certified_reduction",
    "certified_equiv_forward": "reuse.certified_equiv.forward",
    "certified_equiv_backward": "reuse.certified_equiv.backward",
    "presentation_change_forward": "reuse.presentation_change.forward",
    "presentation_change_backward": "reuse.presentation_change.backward",
}

OBSERVED_INPUT_SYSTEM_PROMPT = """You are planning a reduction using an already
compiled Lean library. Each API turn is stateless, so read query_history and
protocol_feedback in the current prompt before deciding the next action. Decide
what to query and write the complete Lean CertifiedPath term yourself. The
agent only returns bounded observations, search results, and legality feedback.
Return exactly one JSON object matching one response option on every turn.
Never invent a declaration, reverse a one-way reduction, add a new mathematical
reduction, or use sorry, admit, axioms, imports, commands, or new definitions.
Finish only with a problem and every connection/reduction that was returned by
your own searches. Lean will check all tasks together once at the end. To claim
that no problem match exists, first query both the exact input node in the
problem catalog and outgoing connections from that node. To claim that no route
exists after matching a problem, first query reductions from the matched node.
If those bounded searches establish either absence, submit the auditable stop
action instead of inventing a proof."""


class InputPlanningError(ValueError):
    """A stable failure code plus a concrete natural-language explanation."""

    def __init__(self, failure_code: str, explanation: str):
        super().__init__(explanation)
        self.failure_code = failure_code
        self.explanation = explanation

    def to_dict(self) -> dict[str, str]:
        return {
            "failure_code": self.failure_code,
            "explanation": self.explanation,
        }


@dataclass(frozen=True)
class ObservedInputPlannerResult:
    plan: HardnessPlan | None
    lean_term: str | None
    problem_match: ProblemMatch | None
    selected_connection: ConnectionCatalogEntry | None
    reduction_declarations: tuple[str, ...]
    explanation: str
    failure_code: str | None = None
    model_prompts: tuple[str, ...] = ()
    model_responses: tuple[ModelResponse, ...] = ()
    query_trace: tuple[Mapping[str, Any], ...] = ()

    @property
    def protocol_accepted(self) -> bool:
        return self.failure_code is None and self.plan is not None


def _require_catalog_fingerprints(
    observation: LeanInputObservation,
    target: LeanInputObservation,
    problem_catalog: ProblemCatalog,
    connection_catalog: ConnectionCatalog,
    reduction_catalog: TypedCatalog,
) -> None:
    fingerprints = {
        observation.registry_fingerprint,
        target.registry_fingerprint,
        problem_catalog.registry_fingerprint,
        connection_catalog.registry_fingerprint,
        reduction_catalog.registry_fingerprint,
    }
    if len(fingerprints) != 1:
        raise InputPlanningError(
            "stale_catalog_fingerprint",
            "输入观察、固定目标和三个检索目录不是由同一个 Lean registry 环境生成的，"
            "因此不能安全地把它们连接成一条证明路径；请重新生成这些快照。",
        )


def _require_supported_input(observation: LeanInputObservation, *, target: bool) -> None:
    if target:
        if (
            observation.supported
            and observation.input_kind == "presented_problem"
            and observation.normalized_problem_node_id
        ):
            return
        raise InputPlanningError(
            "target_declaration_not_presented_problem",
            "固定目标没有被 Lean 确认为一个封闭的 PresentedProblem，因此无法作为归约终点。",
        )
    if (
        observation.supported
        and observation.input_kind == "presented_problem"
        and observation.normalized_problem_node_id
    ):
        return
    if (
        observation.supported
        and observation.input_kind == "predicate"
        and observation.predicate_node_id
        and observation.predicate_domain_node_id
    ):
        return
    raise InputPlanningError(
        observation.failure_code or "input_declaration_not_supported",
        observation.explanation
        or "Lean 没有把输入声明确认为一个可用于复杂度归约的 "
        "PresentedProblem 或封闭一元谓词。",
    )


def _normalize_action(payload: dict[str, Any]) -> dict[str, Any]:
    if isinstance(payload.get("action"), str):
        return payload
    candidates: list[dict[str, Any]] = []
    for action in (
        "inspect_architecture",
        "search_problems",
        "search_connections",
        "search_reductions",
        "finish",
        "stop",
    ):
        nested = payload.get(action)
        if isinstance(nested, dict):
            normalized = dict(nested)
            normalized.setdefault("action", action)
            candidates.append(normalized)
    return candidates[0] if len(candidates) == 1 else payload


def _required_string(payload: Mapping[str, Any], key: str) -> str:
    value = payload.get(key)
    if not isinstance(value, str) or not value.strip():
        raise InputPlanningError(
            "invalid_model_finish",
            f"模型的 finish 回答缺少非空字段 {key}。",
        )
    return value.strip()


def _string_list(payload: Mapping[str, Any], key: str) -> tuple[str, ...]:
    value = payload.get(key)
    if not isinstance(value, list) or any(
        not isinstance(item, str) or not item.strip() for item in value
    ):
        raise InputPlanningError(
            "invalid_model_finish",
            f"模型的 finish 回答中 {key} 必须是字符串列表。",
        )
    return tuple(item.strip() for item in value)


def _compact(value: str) -> str:
    return re.sub(r"\s+", " ", value).strip()


class ObservedInputPlanningSession:
    """One auditable, bounded query session for an observed input."""

    def __init__(
        self,
        *,
        observation: LeanInputObservation,
        target_observation: LeanInputObservation,
        problem_catalog: ProblemCatalog,
        connection_catalog: ConnectionCatalog,
        reduction_catalog: TypedCatalog,
        maximum_query_rounds: int = MAX_INPUT_QUERY_ROUNDS,
    ) -> None:
        if not 1 <= maximum_query_rounds <= MAX_INPUT_QUERY_ROUNDS:
            raise ValueError(
                f"maximum_query_rounds must be in 1..{MAX_INPUT_QUERY_ROUNDS}"
            )
        _require_supported_input(observation, target=False)
        _require_supported_input(target_observation, target=True)
        _require_catalog_fingerprints(
            observation,
            target_observation,
            problem_catalog,
            connection_catalog,
            reduction_catalog,
        )
        self.observation = observation
        self.target_observation = target_observation
        self.problem_catalog = problem_catalog
        self.connection_catalog = connection_catalog
        self.reduction_catalog = reduction_catalog
        self.maximum_query_rounds = maximum_query_rounds
        self.query_rounds_used = 0
        self.retrieved_problems: dict[str, ProblemCatalogEntry] = {}
        self.retrieved_connections: dict[str, ConnectionCatalogEntry] = {}
        self.retrieved_reductions: dict[str, TypedInventoryEntry] = {}
        self.queried_problem_node_ids: set[str] = set()
        self.queried_problem_accepts_node_ids: set[str] = set()
        self.queried_problem_domain_node_ids: set[str] = set()
        self.queried_connection_source_node_ids: set[str] = set()
        self.queried_reduction_source_node_ids: set[str] = set()
        self.trace: list[Mapping[str, Any]] = []
        self.protocol_feedback: list[dict[str, str]] = []

    @property
    def predicate_input(self) -> bool:
        return self.observation.input_kind == "predicate"

    def _input_lookup_node_id(self) -> str:
        if self.predicate_input:
            return self.observation.predicate_node_id or ""
        return self.observation.normalized_problem_node_id or ""

    def _path_source_declaration(self, match: ProblemMatch) -> str:
        if self.predicate_input:
            return match.route_source_declaration
        return self.observation.input_declaration

    def _retrieved_predicate_route_source(self) -> ProblemCatalogEntry | None:
        """Return the one retrieved codec representative, never choose a codec."""

        if not self.predicate_input:
            return None
        exact_ids = {
            entry.entry_id
            for entry in predicate_exact_candidates(
                self.observation,
                self.problem_catalog,
            )
        }
        retrieved = [
            entry
            for entry in self.retrieved_problems.values()
            if entry.entry_id in exact_ids
        ]
        codec_groups = {entry.codec_group_id for entry in retrieved}
        if len(codec_groups) != 1 or not retrieved:
            return None
        return min(retrieved, key=lambda entry: (not entry.registered, entry.declaration))

    def _prompt_path_source_declaration(self) -> str:
        if not self.predicate_input:
            return self.observation.input_declaration
        selected = self._retrieved_predicate_route_source()
        if selected is not None:
            return selected.declaration
        return "<selected PresentedProblem returned by search_problems>"

    def _deduplicate_predicate_aliases(
        self,
        entries: Sequence[ProblemCatalogEntry],
    ) -> tuple[ProblemCatalogEntry, ...]:
        """Expose at most one Lean-confirmed alias for each codec identity."""

        if not self.predicate_input:
            return tuple(entries)
        exact_ids = {
            entry.entry_id
            for entry in predicate_exact_candidates(
                self.observation,
                self.problem_catalog,
            )
        }
        seen_codec_groups: set[str] = set()
        selected: list[ProblemCatalogEntry] = []
        for entry in entries:
            if entry.entry_id not in exact_ids or not entry.codec_group_id:
                selected.append(entry)
                continue
            if entry.codec_group_id in seen_codec_groups:
                continue
            seen_codec_groups.add(entry.codec_group_id)
            aliases = [
                candidate
                for candidate in entries
                if candidate.entry_id in exact_ids
                and candidate.codec_group_id == entry.codec_group_id
            ]
            selected.append(
                min(
                    aliases,
                    key=lambda candidate: (
                        not candidate.registered,
                        candidate.declaration,
                    ),
                )
            )
        # A representative can occur later than the alias that nominated it.
        # Preserve the bounded search order while removing that second copy.
        deduplicated: dict[str, ProblemCatalogEntry] = {}
        for entry in selected:
            deduplicated.setdefault(entry.entry_id, entry)
        return tuple(deduplicated.values())

    def record_protocol_feedback(self, error: InputPlanningError) -> None:
        """Expose a bounded non-Lean legality error to the next stateless turn."""

        feedback = {
            "failure_code": error.failure_code,
            "explanation": error.explanation[:2000],
        }
        self.protocol_feedback.append(feedback)
        self.trace.append(
            {
                "action": "protocol_feedback",
                "status": "returned_to_model",
                **feedback,
            }
        )

    def query_history(self) -> list[dict[str, Any]]:
        """Summarize completed queries, including searches that returned nothing."""

        history: list[dict[str, Any]] = []
        for row in self.trace:
            action = row.get("action")
            if row.get("status") == "started" or action == "protocol_feedback":
                continue
            results = row.get("results")
            if not isinstance(results, list):
                continue
            summary: dict[str, Any] = {
                "action": action,
                "result_count": len(results),
            }
            if "searches" in row:
                summary["searches"] = row["searches"]
            if "queries" in row:
                summary["queries"] = row["queries"]
            if action == "inspect_architecture":
                summary["results"] = results
            history.append(summary)
        return history

    def _consume_query_round(self, action: str) -> None:
        if self.query_rounds_used >= self.maximum_query_rounds:
            raise InputPlanningError(
                "query_budget_exhausted",
                "模型已经用完本题允许的检索轮数，不能继续查询；它只能根据已经返回的"
                "问题、连接和归约提交完整 Lean 代码，或者明确说明现有结果不足。",
            )
        self.query_rounds_used += 1
        self.trace.append(
            {
                "round": self.query_rounds_used,
                "action": action,
                "status": "started",
            }
        )

    def inspect_architecture(self, payload: Mapping[str, Any]) -> dict[str, Any]:
        self._consume_query_round("inspect_architecture")
        try:
            queries = parse_architecture_queries(payload)
            results = inspect_library_architecture(self.reduction_catalog, queries)
        except RetrievalValidationError as error:
            raise InputPlanningError(
                "invalid_architecture_query",
                f"模型请求的库结构查询不符合范围限制：{error}",
            ) from error
        result = {
            "action": "inspect_architecture",
            "queries": [query.to_dict() for query in queries],
            "results": list(results),
            "contains_declaration_names": False,
        }
        self.trace.append(result)
        return result

    def search_problems(self, payload: Mapping[str, Any]) -> dict[str, Any]:
        self._consume_query_round("search_problems")
        # Open-target sessions historically initialized the shared protocol
        # state explicitly rather than calling this class's constructor.
        if not hasattr(self, "queried_problem_accepts_node_ids"):
            self.queried_problem_accepts_node_ids = set()
        if not hasattr(self, "queried_problem_domain_node_ids"):
            self.queried_problem_domain_node_ids = set()
        try:
            searches = parse_problem_searches(payload)
            results = self._deduplicate_predicate_aliases(
                search_problems(self.problem_catalog, searches)
            )
        except (ProblemCatalogError, ValueError) as error:
            raise InputPlanningError(
                "invalid_problem_search",
                f"模型请求的问题查询不符合范围限制：{error}",
            ) from error
        for search in searches:
            self.queried_problem_node_ids.update(search.node_ids)
            self.queried_problem_accepts_node_ids.update(search.accepts_node_ids)
            self.queried_problem_domain_node_ids.update(search.domain_node_ids)
        room = MAX_RETRIEVED_PROBLEMS - len(self.retrieved_problems)
        for entry in results:
            if room <= 0:
                break
            if entry.entry_id not in self.retrieved_problems:
                self.retrieved_problems[entry.entry_id] = entry
                room -= 1
        result = {
            "action": "search_problems",
            "searches": [search.to_dict() for search in searches],
            "results": [
                problem_search_result(
                    entry,
                    input_node_id=self.observation.normalized_problem_node_id or "",
                    observation=self.observation,
                )
                for entry in results
            ],
        }
        self.trace.append(result)
        return result

    def search_connections(self, payload: Mapping[str, Any]) -> dict[str, Any]:
        if self.predicate_input:
            raise InputPlanningError(
                "predicate_connection_not_applicable",
                "predicate 输入必须先通过 Lean-confirmed accepts_exact_defeq "
                "选定现有 PresentedProblem；原始 predicate node 不是归约图端点，"
                "因此不允许查询或选择从它出发的连接。",
            )
        self._consume_query_round("search_connections")
        try:
            searches = parse_connection_searches(payload)
            results = search_connections(self.connection_catalog, searches)
        except (ConnectionCatalogError, ValueError) as error:
            raise InputPlanningError(
                "invalid_connection_search",
                f"模型请求的已有连接查询不符合范围限制：{error}",
            ) from error
        for search in searches:
            self.queried_connection_source_node_ids.update(search.source_node_ids)
        room = MAX_RETRIEVED_CONNECTIONS - len(self.retrieved_connections)
        for entry in results:
            if room <= 0:
                break
            if entry.entry_id not in self.retrieved_connections:
                self.retrieved_connections[entry.entry_id] = entry
                room -= 1
        result = {
            "action": "search_connections",
            "searches": [search.to_dict() for search in searches],
            "results": [connection_search_result(entry) for entry in results],
        }
        self.trace.append(result)
        return result

    def search_reductions(self, payload: Mapping[str, Any]) -> dict[str, Any]:
        self._consume_query_round("search_reductions")
        try:
            searches = parse_theorem_searches(payload)
            results = search_catalog(self.reduction_catalog, searches)
        except RetrievalValidationError as error:
            raise InputPlanningError(
                "invalid_reduction_search",
                f"模型请求的归约定理查询不符合范围限制：{error}",
            ) from error
        for search in searches:
            self.queried_reduction_source_node_ids.update(search.source_node_ids)
        retrieval_limit = getattr(
            self,
            "maximum_retrieved_reductions",
            MAX_RETRIEVED_REDUCTIONS,
        )
        room = retrieval_limit - len(self.retrieved_reductions)
        for entry in results:
            if room <= 0:
                break
            if entry.declaration not in self.retrieved_reductions:
                self.retrieved_reductions[entry.declaration] = entry
                room -= 1
        result = {
            "action": "search_reductions",
            "searches": [search.to_dict() for search in searches],
            "results": [entry_summary(entry) for entry in results],
        }
        self.trace.append(result)
        return result

    def execute_query(self, payload: Mapping[str, Any]) -> dict[str, Any]:
        action = payload.get("action")
        if action == "inspect_architecture":
            return self.inspect_architecture(payload)
        if action == "search_problems":
            return self.search_problems(payload)
        if action == "search_connections":
            return self.search_connections(payload)
        if action == "search_reductions":
            return self.search_reductions(payload)
        raise InputPlanningError(
            "invalid_model_action",
            "模型动作必须是 inspect_architecture、search_problems、"
            "search_connections、search_reductions、finish 或 stop。",
        )

    def _has_existing_reduction_route(self, source_node: str, target_node: str) -> bool:
        """Check absence claims without choosing a route for the model."""

        if source_node == target_node:
            return True
        adjacency: dict[str, set[str]] = {}
        for entry in self.reduction_catalog.entries:
            adjacency.setdefault(entry.source_node_id, set()).add(entry.target_node_id)
        seen = {source_node}
        frontier = [source_node]
        while frontier:
            current = frontier.pop()
            for next_node in adjacency.get(current, set()):
                if next_node == target_node:
                    return True
                if next_node not in seen:
                    seen.add(next_node)
                    frontier.append(next_node)
        return False

    def _predicate_presentation_failure_code(self) -> str | None:
        """Classify only from Lean-confirmed matches and the public catalog."""

        if not self.predicate_input:
            return None
        groups = predicate_presentation_groups(
            self.observation,
            self.problem_catalog,
        )
        if len(groups) > 1:
            return "ambiguous_predicate_presentation"
        if len(groups) == 1:
            return None
        domain_node = self.observation.predicate_domain_node_id or ""
        same_domain_candidates = [
            entry
            for entry in self.problem_catalog.entries
            if domain_node and entry.domain_node_id == domain_node
        ]
        if same_domain_candidates:
            return "predicate_accepts_not_definitionally_equal"
        return "predicate_has_no_lawful_presentation"

    def _stop_for_predicate_presentation(
        self,
        *,
        failure_code: str,
        model_explanation: str,
    ) -> ObservedInputPlannerResult:
        allowed_codes = {
            "predicate_accepts_not_definitionally_equal",
            "ambiguous_predicate_presentation",
            "predicate_has_no_lawful_presentation",
        }
        if failure_code not in allowed_codes:
            raise InputPlanningError(
                "wrong_model_stop_category",
                "封闭谓词输入必须根据 Lean 确认的 accepts 匹配和 codec "
                "分组使用专用的 predicate 阻塞类别。",
            )
        predicate_node = self.observation.predicate_node_id or ""
        domain_node = self.observation.predicate_domain_node_id or ""
        queried_accepts = getattr(self, "queried_problem_accepts_node_ids", set())
        queried_domains = getattr(self, "queried_problem_domain_node_ids", set())
        if predicate_node not in queried_accepts:
            raise InputPlanningError(
                "model_stop_not_auditable",
                "模型尚未用真实 predicate node 查询问题目录的 accepts 索引，"
                "不能断言谓词无匹配、无表示或表示歧义。",
            )
        if domain_node not in queried_domains:
            raise InputPlanningError(
                "model_stop_not_auditable",
                "模型尚未用 Lean 确认的 predicate domain node 查询问题目录，"
                "因此无法区分 accepts 不等价与完全缺少合法表示。",
            )
        actual_code = self._predicate_presentation_failure_code()
        if actual_code is None:
            raise InputPlanningError(
                "model_stop_contradicted_by_catalog",
                "Lean 观察与同指纹问题目录确认了唯一 codec 的合法 "
                "PresentedProblem；模型应选择已检索候选并继续查询归约。",
            )
        if failure_code != actual_code:
            raise InputPlanningError(
                "wrong_model_stop_category",
                f"模型选择的 predicate 阻塞类别与 Lean 证据不符；当前应为 "
                f"{actual_code}。",
            )
        explanations = {
            "predicate_accepts_not_definitionally_equal": (
                "Lean 确认该谓词的输入 carrier 与目录中至少一个问题一致，"
                "但 nonce 绑定的 isDefEq 检查没有确认其与任何候选 accepts "
                "定义等价；仅凭相同 carrier 不能选择问题。"
            ),
            "ambiguous_predicate_presentation": (
                "Lean 确认该谓词同时匹配多个不同 encoder-bound identity "
                "的合法表示；原始 predicate 没有足够信息在这些 codec 之间"
                "做出可审计选择。"
            ),
            "predicate_has_no_lawful_presentation": (
                "Lean 确认输入是封闭一元谓词，但同指纹公开目录中既没有"
                "匹配的 accepts，也没有具有该 domain 的现有合法 PresentedProblem。"
            ),
        }
        accepted_explanation = (
            explanations[failure_code]
            + " 继续需要在 Lean 库中先提供唯一、合法且可验证的问题表示。"
            + f" 模型说明：{model_explanation}"
        )
        self.trace.append(
            {"action": "stop", "status": "accepted", "failure_code": failure_code}
        )
        return ObservedInputPlannerResult(
            plan=None,
            lean_term=None,
            problem_match=None,
            selected_connection=None,
            reduction_declarations=(),
            explanation=accepted_explanation,
            failure_code=failure_code,
            query_trace=tuple(self.trace),
        )

    def stop(self, payload: Mapping[str, Any]) -> ObservedInputPlannerResult:
        """Accept only a model stop reason contradicted by no compiled catalog fact."""

        failure_code = payload.get("failure_code")
        explanation = payload.get("explanation")
        if not isinstance(failure_code, str) or not failure_code.strip():
            raise InputPlanningError(
                "invalid_model_stop",
                "模型的 stop 回答必须说明稳定的 failure_code。",
            )
        if not isinstance(explanation, str) or not explanation.strip():
            raise InputPlanningError(
                "invalid_model_stop",
                "模型的 stop 回答必须用自然语言说明它查询了什么以及缺少什么。",
            )
        failure_code = failure_code.strip()
        model_explanation = explanation.strip()[:2000]
        input_node = self.observation.normalized_problem_node_id or ""

        if self.predicate_input and failure_code != "no_existing_reduction_route":
            return self._stop_for_predicate_presentation(
                failure_code=failure_code,
                model_explanation=model_explanation,
            )

        if failure_code == "no_lean_verified_problem_match":
            if input_node not in self.queried_problem_node_ids:
                raise InputPlanningError(
                    "model_stop_not_auditable",
                    "模型没有按真实输入的 Lean node 查询问题目录，因此还不能断言库中没有"
                    "可验证的对应问题。",
                )
            if input_node not in self.queried_connection_source_node_ids:
                raise InputPlanningError(
                    "model_stop_not_auditable",
                    "模型没有查询从真实输入 Lean node 出发的已有连接，因此还不能断言输入"
                    "无法连接到库中的问题。",
                )
            problem_nodes = {entry.problem_node_id for entry in self.problem_catalog.entries}
            exact_candidates = [
                entry for entry in self.problem_catalog.entries
                if entry.problem_node_id == input_node
            ]
            connecting_candidates = [
                entry for entry in self.connection_catalog.entries
                if entry.source_node_id == input_node
                and entry.target_node_id in problem_nodes
            ]
            if exact_candidates or connecting_candidates:
                raise InputPlanningError(
                    "model_stop_contradicted_by_catalog",
                    "模型声称找不到可验证的问题，但同一指纹的 Lean 目录仍包含定义等价的"
                    "问题或从输入出发的已有连接；它应继续选择并提交这些检索结果。",
                )
            accepted_explanation = (
                "Lean 已确认该输入是一个封闭的 PresentedProblem，但同一 registry 指纹下"
                "既没有与其规范化 node 相同的公开问题，也没有从该 node 指向目录问题的"
                "已有 CertifiedReduction、CertifiedEquiv 或表示转换连接。因此当前库无法"
                "把这个输入接入已有归约图；继续需要先在 Lean 库中加入可验证的问题连接。"
                f" 模型说明：{model_explanation}"
            )
            self.trace.append(
                {"action": "stop", "status": "accepted", "failure_code": failure_code}
            )
            return ObservedInputPlannerResult(
                plan=None,
                lean_term=None,
                problem_match=None,
                selected_connection=None,
                reduction_declarations=(),
                explanation=accepted_explanation,
                failure_code=failure_code,
                query_trace=tuple(self.trace),
            )

        if failure_code == "no_existing_reduction_route":
            matched_problem = payload.get("matched_problem")
            relation = payload.get("match_relation")
            raw_connection_id = payload.get("connection_entry_id")
            if not isinstance(matched_problem, str) or not matched_problem.strip():
                raise InputPlanningError(
                    "invalid_model_stop",
                    "模型声称没有路线时，必须指出已经由 search_problems 找到的输入问题。",
                )
            if not isinstance(relation, str) or not relation.strip():
                raise InputPlanningError(
                    "invalid_model_stop",
                    "模型声称没有路线时，必须说明输入与所选问题之间的 Lean 验证关系。",
                )
            if raw_connection_id is not None and (
                not isinstance(raw_connection_id, str) or not raw_connection_id.strip()
            ):
                raise InputPlanningError(
                    "invalid_model_stop",
                    "connection_entry_id 必须是 null 或 search_connections 返回的非空 ID。",
                )
            candidate = self._selected_problem(matched_problem.strip())
            connection_id = (
                raw_connection_id.strip() if isinstance(raw_connection_id, str) else None
            )
            connection = self._selected_connection(connection_id)
            match = self._problem_match(
                candidate=candidate,
                relation=relation.strip(),
                connection=connection,
            )
            current_node = match.route_source_node_id
            if connection is not None:
                if connection.source_node_id != input_node:
                    raise InputPlanningError(
                        "connection_wrong_start",
                        "所选输入连接没有从真实输入的 Lean node 开始。",
                    )
                if connection.target_node_id != current_node:
                    raise InputPlanningError(
                        "connection_wrong_target",
                        "输入连接没有到达 ProblemMatch 记录的路线源 node。",
                    )
            if current_node != match.candidate_node_id:
                raise InputPlanningError(
                    "connection_wrong_target",
                    "ProblemMatch 的路线源与模型所选库问题的 Lean node 不一致。",
                )
            if current_node not in self.queried_reduction_source_node_ids:
                raise InputPlanningError(
                    "model_stop_not_auditable",
                    "模型尚未从已经确认的库问题 node 查询已有归约，不能断言没有到固定目标"
                    "的路线。",
                )
            target_node = self.target_observation.normalized_problem_node_id or ""
            if self._has_existing_reduction_route(current_node, target_node):
                raise InputPlanningError(
                    "model_stop_contradicted_by_catalog",
                    "模型声称没有已有路线，但同一指纹的归约目录中仍存在从所选问题到固定"
                    "目标的有向路径；它应继续检索并提交路径。",
                )
            reverse_exists = self._has_existing_reduction_route(target_node, current_node)
            direction_detail = (
                "目录中可以观察到相反方向的路线，但单向归约不能反向使用。"
                if reverse_exists
                else "目录中也没有能够组合成该方向路径的注册归约。"
            )
            accepted_explanation = (
                "Lean 已确认输入对应所选库问题，固定目标也已确认，但从该问题的 Lean node"
                " 出发，当前已注册 CertifiedReduction 的有向图无法到达目标 node。"
                f"{direction_detail}继续需要在 Lean 库中已有一条方向正确的归约，不能由"
                f" Agent 猜测或反转现有定理。模型说明：{model_explanation}"
            )
            self.trace.append(
                {"action": "stop", "status": "accepted", "failure_code": failure_code}
            )
            return ObservedInputPlannerResult(
                plan=None,
                lean_term=None,
                problem_match=match,
                selected_connection=connection,
                reduction_declarations=(),
                explanation=accepted_explanation,
                failure_code=failure_code,
                query_trace=tuple(self.trace),
            )

        raise InputPlanningError(
            "invalid_model_stop",
            "模型只允许在没有 Lean 可验证的问题匹配，或确认问题后没有已有有向归约路线"
            "这两种情况下停止。",
        )

    def _selected_problem(
        self, selector: str | Mapping[str, Any]
    ) -> ProblemCatalogEntry:
        selectors: list[str] = []
        if isinstance(selector, str) and selector.strip():
            selectors.append(selector.strip())
        elif isinstance(selector, Mapping):
            for field in ("entry_id", "declaration"):
                if field not in selector:
                    continue
                value = selector.get(field)
                if not isinstance(value, str) or not value.strip():
                    selectors = []
                    break
                selectors.append(value.strip())

        resolved: dict[str, ProblemCatalogEntry] = {}
        for value in selectors:
            candidates = {
                entry.entry_id: entry
                for entry in self.retrieved_problems.values()
                if entry.entry_id == value or entry.declaration == value
            }
            if len(candidates) != 1:
                resolved = {}
                break
            candidate = next(iter(candidates.values()))
            resolved[candidate.entry_id] = candidate

        if not selectors or len(resolved) != 1:
            raise InputPlanningError(
                "problem_not_retrieved",
                "模型选择的问题不是本会话 search_problems 返回的唯一精确 entry_id "
                "或 declaration；如果对象同时提供两者，它们也必须指向同一已检索"
                "条目。因此 Agent 无法确认这是模型实际检索过的库问题。",
            )
        return next(iter(resolved.values()))

    def _selected_connection(
        self, entry_id: str | None
    ) -> ConnectionCatalogEntry | None:
        if entry_id is None:
            return None
        connection = self.retrieved_connections.get(entry_id)
        if connection is None:
            raise InputPlanningError(
                "connection_not_retrieved",
                "模型选择的连接没有由本会话的 search_connections 返回，因此不能作为"
                "输入与库问题之间的依据。",
            )
        return connection

    def _problem_match(
        self,
        *,
        candidate: ProblemCatalogEntry,
        relation: str,
        connection: ConnectionCatalogEntry | None,
    ) -> ProblemMatch:
        try:
            if self.predicate_input:
                if connection is not None:
                    raise InputPlanningError(
                        "predicate_connection_not_allowed",
                        "原始 predicate 不是 PresentedProblem 端点，不能伪造或复用"
                        "一条从 predicate node 出发的归约/表示连接。只能使用 Lean "
                        "确认的 accepts_exact_defeq 选中现有 PresentedProblem。",
                    )
                if relation != "accepts_exact_defeq":
                    raise InputPlanningError(
                        "predicate_match_relation_required",
                        "predicate 输入的匹配关系必须是 search_problems 由 "
                        "nonce 绑定 Lean 证据标记的 accepts_exact_defeq，不能使用"
                        " exact_defeq 或文本相似度。",
                    )
                groups = predicate_presentation_groups(
                    self.observation,
                    self.problem_catalog,
                )
                if len(groups) > 1:
                    raise InputPlanningError(
                        "ambiguous_predicate_presentation",
                        "Lean 确认的 accepts 匹配落入多个不同 encoder-bound "
                        "identity；Agent 不能按声明顺序或路线优劣替用户选 codec。",
                    )
                if not groups:
                    failure_code = self._predicate_presentation_failure_code()
                    raise InputPlanningError(
                        failure_code or "predicate_has_no_lawful_presentation",
                        "所选问题没有与真实 predicate 一致的 Lean-confirmed "
                        "accepts 证据，因此不能作为路径源。",
                    )
                exact_ids = {entry.entry_id for entry in groups[0].entries}
                if candidate.entry_id not in exact_ids:
                    raise InputPlanningError(
                        "predicate_accepts_not_definitionally_equal",
                        "所选问题虽由搜索返回，但 observation 中没有 Lean 确认的"
                        " predicate 与 candidate.accepts 定义等价记录。",
                    )
                return exact_predicate_problem_match(
                    observation=self.observation,
                    catalog=self.problem_catalog,
                    candidate=candidate,
                    retrieved_entries=tuple(self.retrieved_problems.values()),
                )

            input_node = self.observation.normalized_problem_node_id or ""
            if candidate.problem_node_id == input_node and relation != "exact_defeq":
                raise InputPlanningError(
                    "exact_match_must_not_use_connection",
                    "search_problems 已把所选问题标记为 exact_defeq=true。此时匹配关系必须"
                    "写成 exact_defeq，connection_entry_id 必须是 JSON null；输入匹配不需要"
                    "也不允许额外连接。归约路线应另行通过 search_reductions 查询。",
                )
            if relation == "exact_defeq":
                if connection is not None:
                    raise InputPlanningError(
                        "unexpected_connection_for_exact_match",
                        "输入与所选问题已经由 Lean 确认为定义等价，不应再提交一个虚构或"
                        "多余的连接。",
                    )
                return exact_problem_match(
                    observation=self.observation,
                    catalog=self.problem_catalog,
                    candidate=candidate,
                    retrieved_entries=tuple(self.retrieved_problems.values()),
                )
            if connection is None:
                raise InputPlanningError(
                    "missing_connection_for_problem_match",
                    "输入与所选库问题并非定义等价；模型必须选择一个由"
                    " search_connections 返回、方向正确的已有证书。",
                )
            if connection.relation != relation:
                raise InputPlanningError(
                    "connection_relation_mismatch",
                    "模型声明的匹配关系与所选 Lean 连接实际导出的方向不一致。",
                )
            return connected_problem_match(
                observation=self.observation,
                problem_catalog=self.problem_catalog,
                candidate=candidate,
                retrieved_problem_entries=tuple(self.retrieved_problems.values()),
                connection_catalog=self.connection_catalog,
                connection=connection,
                retrieved_connections=tuple(self.retrieved_connections.values()),
            )
        except (ProblemCatalogError, ConnectionCatalogError) as error:
            raise InputPlanningError(
                "problem_match_not_verified",
                f"模型选择的问题无法由 Lean 目录事实连接到真实输入：{error}",
            ) from error

    def _selected_reductions(
        self, declarations: Sequence[str]
    ) -> tuple[TypedInventoryEntry, ...]:
        if len(declarations) > MAX_SELECTED_REDUCTIONS:
            raise InputPlanningError(
                "selected_path_too_long",
                f"模型选择了超过 {MAX_SELECTED_REDUCTIONS} 条归约；当前协议拒绝这条过长路径。",
            )
        if len(declarations) != len(set(declarations)):
            raise InputPlanningError(
                "repeated_reduction_declaration",
                "模型在同一条路径中重复使用了同一个归约声明。",
            )
        selected: list[TypedInventoryEntry] = []
        for declaration in declarations:
            entry = self.retrieved_reductions.get(declaration)
            if entry is None:
                raise InputPlanningError(
                    "reduction_not_retrieved",
                    "模型引用了没有由本会话 search_reductions 返回的归约声明。",
                )
            selected.append(entry)
        return tuple(selected)

    def _validate_topology(
        self,
        *,
        match: ProblemMatch,
        connection: ConnectionCatalogEntry | None,
        reductions: Sequence[TypedInventoryEntry],
    ) -> None:
        current = match.route_source_node_id
        if connection is not None:
            input_node = self.observation.normalized_problem_node_id or ""
            if connection.source_node_id != input_node:
                raise InputPlanningError(
                    "connection_wrong_start",
                    "所选连接没有从真实输入的 Lean node 开始。",
                )
            if connection.target_node_id != match.route_source_node_id:
                raise InputPlanningError(
                    "connection_wrong_target",
                    "输入匹配连接没有到达 ProblemMatch 记录的路线源 node。",
                )
        if current != match.candidate_node_id:
            raise InputPlanningError(
                "connection_wrong_target",
                "ProblemMatch 的路线源与模型所选库问题的 Lean node 不一致。",
            )
        for entry in reductions:
            if entry.source_node_id != current:
                raise InputPlanningError(
                    "reduction_path_disconnected",
                    "模型给出的归约顺序中，相邻两条定理的 Lean 端点不能连接；"
                    f"在 {entry.declaration} 之前已经到达的 node 与该定理起点不同。",
                )
            current = entry.target_node_id
        target_node = self.target_observation.normalized_problem_node_id or ""
        if current != target_node:
            raise InputPlanningError(
                "reduction_path_does_not_reach_target",
                "模型选择的已有连接和归约结束后没有到达固定目标的 Lean node。",
            )

    def _validate_lean_term(
        self,
        *,
        lean_term: str,
        candidate: ProblemCatalogEntry,
        connection: ConnectionCatalogEntry | None,
        reductions: Sequence[TypedInventoryEntry],
    ) -> str:
        lean_term = lean_term.strip()
        if not lean_term:
            raise InputPlanningError(
                "missing_lean_term", "模型没有给出最终 CertifiedPath Lean 表达式。"
            )
        if len(lean_term) > MAX_MODEL_LEAN_TERM_CHARS:
            raise InputPlanningError(
                "lean_term_too_large", "模型给出的 Lean 表达式超过审计长度上限。"
            )
        if BANNED_MODEL_TERM_RE.search(lean_term):
            raise InputPlanningError(
                "forbidden_lean_syntax",
                "模型给出的 Lean 内容含有禁止的占位符、命令、导入或新声明。",
            )
        expected_atoms: list[str] = []
        if connection is not None:
            expected_atoms.append(connection.lean_term)
        expected_atoms.extend(entry.declaration for entry in reductions)
        compact_term = _compact(lean_term)
        position = 0
        for atom in expected_atoms:
            compact_atom = _compact(atom)
            next_position = compact_term.find(compact_atom, position)
            if next_position < 0:
                raise InputPlanningError(
                    "lean_term_missing_selected_fact",
                    "最终 Lean 表达式没有按顺序引用所有选中的连接和归约。",
                )
            position = next_position + len(compact_atom)

        edge_count = len(reductions) + (1 if connection is not None else 0)
        step_constructor = "ComplexityReduction.Certificate.CertifiedPath.step"
        cons_constructor = "ComplexityReduction.Certificate.CertifiedPath.cons"
        refl_constructor = "ComplexityReduction.Certificate.CertifiedPath.refl"
        if edge_count == 0 and refl_constructor not in compact_term:
            raise InputPlanningError(
                "lean_term_missing_path_constructor",
                "所选端点之间没有归约边时，lean_term 必须显式使用 "
                "ComplexityReduction.Certificate.CertifiedPath.refl 构造路径；不能直接"
                "提交问题或其他对象。",
            )
        if edge_count > 0 and step_constructor not in compact_term:
            raise InputPlanningError(
                "lean_term_missing_path_constructor",
                "lean_term 直接写了 CertifiedReduction 声明，但目标类型是 CertifiedPath。"
                "必须用 ComplexityReduction.Certificate.CertifiedPath.step 包住第一条"
                "归约边；Agent 不会替模型自动添加这个构造器。",
            )
        if edge_count > 1 and compact_term.count(cons_constructor) < edge_count - 1:
            raise InputPlanningError(
                "lean_term_missing_path_constructor",
                "lean_term 含有多条有向边，但没有用足够的 "
                "ComplexityReduction.Certificate.CertifiedPath.cons 按顺序追加后续边。",
            )

        used_declarations = set(FULL_DECLARATION_RE.findall(lean_term))
        if (
            self.predicate_input
            and self.observation.input_declaration in used_declarations
        ):
            raise InputPlanningError(
                "predicate_used_as_path_source",
                "模型把原始 predicate 声明写入了 CertifiedPath term。predicate 只用于"
                "最终 grounding 审计；路径必须从 Lean 确认且已选中的现有 "
                "PresentedProblem 开始。",
            )
        allowed = set(STATIC_PATH_DECLARATIONS)
        allowed.update(
            {
                (
                    candidate.declaration
                    if self.predicate_input
                    else self.observation.input_declaration
                ),
                self.target_observation.input_declaration,
                candidate.declaration,
            }
        )
        allowed.update(entry.declaration for entry in reductions)
        if connection is not None:
            allowed.add(connection.certificate_declaration)
            allowed.add(connection.projection_declaration)
        unexpected = sorted(
            declaration
            for declaration in used_declarations
            if declaration not in allowed
        )
        if unexpected:
            raise InputPlanningError(
                "lean_term_uses_unselected_declaration",
                "最终 Lean 表达式引用了没有被选择或没有通过本会话检索授权的声明："
                + ", ".join(unexpected[:4]),
            )
        return lean_term

    def _build_plan(
        self,
        *,
        match: ProblemMatch,
        candidate: ProblemCatalogEntry,
        connection: ConnectionCatalogEntry | None,
        reductions: Sequence[TypedInventoryEntry],
        lean_term: str,
        explanation: str,
    ) -> HardnessPlan:
        steps: list[dict[str, Any]] = []
        if connection is None:
            if self.predicate_input:
                steps.append(
                    {
                        "schema_version": PLAN_STEP_SCHEMA,
                        "step_id": "s1",
                        "action_kind": "select.existing_problem_presentation",
                        "output_handles": ["matched_problem"],
                        "parameters": {
                            "problem_declaration": candidate.declaration,
                            "problem_match_id": match.match_id,
                            "problem_node_id": match.route_source_node_id,
                            "relation": match.relation,
                        },
                    }
                )
            else:
                steps.append(
                    {
                        "schema_version": PLAN_STEP_SCHEMA,
                        "step_id": "s1",
                        "action_kind": "reuse.exact_endpoint",
                        "output_handles": ["matched_problem"],
                        "parameters": {
                            "input_declaration": self.observation.input_declaration,
                            "problem_declaration": candidate.declaration,
                            "problem_match_id": match.match_id,
                            "problem_node_id": candidate.problem_node_id,
                        },
                    }
                )
        else:
            steps.append(
                {
                    "schema_version": PLAN_STEP_SCHEMA,
                    "step_id": "s1",
                    "action_kind": RELATION_ACTION_KIND[connection.relation],
                    "capability_kind": connection.capability_kind,
                    "declaration": connection.certificate_declaration,
                    "output_handles": ["matched_problem"],
                    "role": connection.component_role,
                    "source_fingerprint": connection.source_fingerprint,
                    "target_fingerprint": connection.target_fingerprint,
                    "parameters": {
                        "connection_entry_id": connection.entry_id,
                        "projection_declaration": connection.projection_declaration,
                        "executable_lean_term": connection.lean_term,
                        "relation": connection.relation,
                        "problem_match_id": match.match_id,
                    },
                }
            )
        steps.append(
            {
                "schema_version": PLAN_STEP_SCHEMA,
                "step_id": "s2",
                "action_kind": "select.existing_hardness_target",
                "depends_on": ["s1"],
                "output_handles": ["selected_target"],
                "parameters": {
                    "target_declaration": self.target_observation.input_declaration,
                    "target_node_id": self.target_observation.normalized_problem_node_id,
                    "selection_policy": "fixed_target",
                },
            }
        )
        previous = "s2"
        for index, entry in enumerate(reductions, start=3):
            step_id = f"s{index}"
            steps.append(
                {
                    "schema_version": PLAN_STEP_SCHEMA,
                    "step_id": step_id,
                    "action_kind": "reuse.certified_reduction",
                    "capability_kind": "certified_reduction",
                    "declaration": entry.declaration,
                    "depends_on": [previous],
                    "role": entry.component_role,
                    "source_fingerprint": entry.source_fingerprint,
                    "target_fingerprint": entry.target_fingerprint,
                    "parameters": {"catalog_entry_id": entry.entry_id},
                }
            )
            previous = step_id
        emit_id = f"s{len(steps) + 1}"
        path_source_declaration = self._path_source_declaration(match)
        expected_type = (
            "ComplexityReduction.Certificate.CertifiedPath "
            f"{path_source_declaration} "
            f"{self.target_observation.input_declaration}"
        )
        steps.append(
            {
                "schema_version": PLAN_STEP_SCHEMA,
                "step_id": emit_id,
                "action_kind": "emit.certified_path",
                "depends_on": [previous],
                "expected_type": expected_type,
            }
        )
        payload = {
            "schema_version": PLAN_SCHEMA,
            "objective": "reduce_to",
            "source_declaration": path_source_declaration,
            "target_declaration": self.target_observation.input_declaration,
            "registry_fingerprint": self.problem_catalog.registry_fingerprint,
            "catalog_id": self.reduction_catalog.catalog_id,
            "problem_catalog_id": self.problem_catalog.catalog_id,
            "connection_catalog_id": self.connection_catalog.catalog_id,
            "matched_problem_declaration": candidate.declaration,
            "problem_match": match.to_dict(),
            "target_evidence": {
                "policy": "fixed_target",
                "declaration": self.target_observation.input_declaration,
                "node_id": self.target_observation.normalized_problem_node_id,
                "validation_source": "lean_input_observation",
                "observation_id": self.target_observation.observation_id,
            },
            "metadata": {
                "input_observation_id": self.observation.observation_id,
                "model_explanation": explanation,
                "query_rounds_used": self.query_rounds_used,
            },
            "steps": steps,
            "outputs": [
                {
                    "schema_version": PLAN_OUTPUT_SCHEMA,
                    "output_id": "selected_path",
                    "output_kind": "lean.term",
                    "producer_steps": [step["step_id"] for step in steps],
                    "expected_type": expected_type,
                    "lean_code": lean_term,
                    "metadata": {
                        "connection_entry_id": (
                            connection.entry_id if connection is not None else None
                        ),
                        "reduction_declarations": [
                            entry.declaration for entry in reductions
                        ],
                    },
                }
            ],
        }
        return parse_hardness_plan(payload)

    def finish(self, payload: Mapping[str, Any]) -> ObservedInputPlannerResult:
        matched_problem = _required_string(payload, "matched_problem")
        relation = _required_string(payload, "match_relation")
        target_declaration = _required_string(payload, "target_declaration")
        lean_term = _required_string(payload, "lean_term")
        explanation = _required_string(payload, "explanation")[:2000]
        reductions = _string_list(payload, "reduction_declarations")
        if target_declaration != self.target_observation.input_declaration:
            raise InputPlanningError(
                "wrong_fixed_target",
                "模型提交的目标声明不是本题由 Lean 观察确认的固定目标。",
            )
        raw_connection_id = payload.get("connection_entry_id")
        if raw_connection_id is not None and (
            not isinstance(raw_connection_id, str) or not raw_connection_id.strip()
        ):
            raise InputPlanningError(
                "invalid_model_finish",
                "connection_entry_id 必须是 null 或 search_connections 返回的非空 ID。",
            )
        connection_id = raw_connection_id.strip() if isinstance(raw_connection_id, str) else None
        candidate = self._selected_problem(matched_problem)
        if relation in {"exact_defeq", "accepts_exact_defeq"} and connection_id is not None:
            raise InputPlanningError(
                "unexpected_connection_for_exact_match",
                "模型选择的问题由 search_problems 标记为 exact_defeq 或 "
                "accepts_exact_defeq 时，"
                "connection_entry_id 必须使用 JSON null，而不是说明文字、定理名或 ID。"
                "随后应只把 search_reductions 返回的声明列入归约路线。",
            )
        connection = self._selected_connection(connection_id)
        match = self._problem_match(
            candidate=candidate,
            relation=relation,
            connection=connection,
        )
        selected_reductions = self._selected_reductions(reductions)
        self._validate_topology(
            match=match,
            connection=connection,
            reductions=selected_reductions,
        )
        checked_term = self._validate_lean_term(
            lean_term=lean_term,
            candidate=candidate,
            connection=connection,
            reductions=selected_reductions,
        )
        plan = self._build_plan(
            match=match,
            candidate=candidate,
            connection=connection,
            reductions=selected_reductions,
            lean_term=checked_term,
            explanation=explanation,
        )
        result = ObservedInputPlannerResult(
            plan=plan,
            lean_term=checked_term,
            problem_match=match,
            selected_connection=connection,
            reduction_declarations=tuple(
                entry.declaration for entry in selected_reductions
            ),
            explanation=explanation,
            query_trace=tuple(self.trace),
        )
        self.trace.append(
            {
                "action": "finish",
                "status": "accepted",
                "plan_id": plan.plan_id,
            }
        )
        return result

    def prompt_payload(self) -> dict[str, Any]:
        path_source_declaration = self._prompt_path_source_declaration()
        expected_lean_type = (
            "ComplexityReduction.Certificate.CertifiedPath "
            f"{path_source_declaration} "
            f"{self.target_observation.input_declaration}"
        )
        input_node = self._input_lookup_node_id()
        problem_hints = build_initial_problem_hints(
            self.problem_catalog,
            input_node_id=input_node,
            observation=self.observation,
        )
        if self.predicate_input:
            connection_hints = {
                "contains_declaration_names": False,
                "input_node_id": input_node,
                "deferred": True,
                "not_applicable": True,
                "reason": (
                    "A raw predicate is not a PresentedProblem endpoint. Retrieve a "
                    "Lean-confirmed accepts_exact_defeq presentation with search_problems; "
                    "that grounding uses no reduction or presentation-change edge."
                ),
                "full_connection_catalog_included": False,
            }
        elif problem_hints["exact_candidate_count"]:
            connection_hints: dict[str, Any] = {
                "contains_declaration_names": False,
                "input_node_id": input_node,
                "deferred": True,
                "reason": (
                    "An exact-node problem candidate exists. First retrieve it with "
                    "search_problems; an exact_defeq match does not use an input "
                    "connection."
                ),
                "full_connection_catalog_included": False,
            }
        else:
            connection_hints = build_initial_connection_hints(
                self.connection_catalog,
                input_node_id=input_node,
            )
        if self.predicate_input:
            problem_search_example = [
                {
                    "accepts_node_ids": [self.observation.predicate_node_id],
                    "domain_node_ids": [self.observation.predicate_domain_node_id],
                    "limit": 8,
                },
                {
                    "domain_node_ids": [self.observation.predicate_domain_node_id],
                    "limit": 8,
                },
            ]
            workflow_rules = [
                (
                    "Query search_problems with the observed predicate node as an "
                    "accepts_node_id and the observed domain node. Also query the domain "
                    "alone so an accepts mismatch can be distinguished from a missing "
                    "lawful presentation."
                ),
                (
                    "Treat a candidate as exact only when its returned row has "
                    "accepts_exact_defeq=true. That flag comes only from the nonce-bound "
                    "Lean observation, never from node hashes or text similarity."
                ),
                (
                    "Aliases with one codec identity are one presentation. If the prompt "
                    "reports multiple codec groups, stop with "
                    "ambiguous_predicate_presentation; never choose a codec by route "
                    "quality or declaration order."
                ),
                (
                    "For the one lawful presentation, use match_relation "
                    "accepts_exact_defeq and JSON null connection_entry_id. The route "
                    "starts at that selected PresentedProblem, not at the raw predicate."
                ),
                (
                    "After the problem match, retrieve every directed route edge from the "
                    "selected problem_node_id with search_reductions and submit the "
                    "connected declarations in order."
                ),
            ]
            stop_failure_codes = (
                "predicate_accepts_not_definitionally_equal, "
                "ambiguous_predicate_presentation, "
                "predicate_has_no_lawful_presentation, or "
                "no_existing_reduction_route"
            )
            stop_audit_requirements = {
                "predicate_accepts_not_definitionally_equal": [
                    "search_problems with the predicate node as accepts_node_id",
                    "search_problems with the predicate domain node",
                ],
                "ambiguous_predicate_presentation": [
                    "search_problems with the predicate node as accepts_node_id",
                    "search_problems with the predicate domain node",
                ],
                "predicate_has_no_lawful_presentation": [
                    "search_problems with the predicate node as accepts_node_id",
                    "search_problems with the predicate domain node",
                ],
                "no_existing_reduction_route": [
                    "select the unique-codec problem returned by search_problems",
                    "search_reductions from ProblemMatch.route_source_node_id",
                ],
            }
            match_relation_rule = "string: accepts_exact_defeq"
            connection_otherwise_rule = (
                "not applicable to predicate grounding; use JSON null"
            )
        else:
            problem_search_example = [
                {
                    "node_ids": ["optional exact input node"],
                    "terms": ["optional semantic words"],
                    "limit": 8,
                }
            ]
            workflow_rules = [
                (
                    "First retrieve problem candidates with search_problems using the "
                    "exact input node."
                ),
                (
                    "If a returned problem has exact_defeq=true, choose that problem, "
                    "set match_relation to exact_defeq, set connection_entry_id to JSON "
                    "null, and do not use search_connections for that match."
                ),
                (
                    "Only when no exact_defeq problem was returned may search_connections "
                    "supply an input-to-problem match; then use the returned relation and "
                    "entry_id."
                ),
                (
                    "After the problem match, retrieve every directed route edge with "
                    "search_reductions. A declaration seen only in search_connections is "
                    "not authorized in reduction_declarations."
                ),
                (
                    "For a direct route, search_reductions with the matched problem node "
                    "as source and the fixed target node as target. For a multi-edge "
                    "route, expand outgoing reductions from every returned frontier node."
                ),
            ]
            stop_failure_codes = (
                "no_lean_verified_problem_match or no_existing_reduction_route"
            )
            stop_audit_requirements = {
                "no_lean_verified_problem_match": [
                    "search_problems with the exact input node",
                    "search_connections with the exact input node as source",
                ],
                "no_existing_reduction_route": [
                    "select a problem returned by search_problems",
                    "search_reductions from the matched problem node",
                ],
            }
            match_relation_rule = (
                "string: exact_defeq, or the exact relation of a selected "
                "search_connections result"
            )
            connection_otherwise_rule = (
                "the exact entry_id string returned by search_connections"
            )
        return {
            "task": "identify_input_problem_and_reuse_existing_reductions",
            "expected_lean_type": expected_lean_type,
            "catalog_view": {
                "mode": self.reduction_catalog.mode,
                "catalog_id": self.reduction_catalog.catalog_id,
                "visible_reduction_count": len(self.reduction_catalog.entries),
                "comparison_semantics": (
                    "flat_api exposes existing end-to-end/final-facade reductions; "
                    "ir_components is the legacy non-facade-only feasibility view; "
                    "component_catalog preserves every flat_api reduction and also "
                    "exposes existing ingress, shared-gadget, and egress reductions; "
                    "full exposes the complete registered view"
                ),
                "same_registry_fingerprint": True,
                "view_is_a_role_based_catalog_filter": self.reduction_catalog.mode
                != "full",
                "all_reductions_in_this_view_remain_queryable": True,
            },
            "input_observation": {
                "input_module": self.observation.input_module,
                "input_declaration": self.observation.input_declaration,
                "input_kind": self.observation.input_kind,
                "elaborated_type": self.observation.elaborated_type,
                "normalized_problem_node_id": self.observation.normalized_problem_node_id,
                "predicate_node_id": self.observation.predicate_node_id,
                "predicate_domain": self.observation.predicate_domain,
                "predicate_domain_node_id": self.observation.predicate_domain_node_id,
                "referenced_constants": list(self.observation.referenced_constants),
                "semantic_summary": self.observation.semantic_summary,
                "representation_summary": self.observation.representation_summary,
                "predicate_summary": self.observation.predicate_summary,
                "accepts_summary": self.observation.accepts_summary,
            },
            "fixed_target": {
                "declaration": self.target_observation.input_declaration,
                "node_id": self.target_observation.normalized_problem_node_id,
                "semantic_summary": self.target_observation.semantic_summary,
                "representation_summary": self.target_observation.representation_summary,
            },
            "problem_hints": problem_hints,
            "connection_hints": connection_hints,
            "library_architecture": build_library_architecture(
                self.reduction_catalog
            ),
            "query_budget": {
                "used": self.query_rounds_used,
                "maximum": self.maximum_query_rounds,
                "remaining": self.maximum_query_rounds - self.query_rounds_used,
            },
            "query_history": self.query_history(),
            "protocol_feedback": list(self.protocol_feedback[-3:]),
            "retrieved": {
                "problems": [
                    problem_search_result(
                        entry,
                        input_node_id=self.observation.normalized_problem_node_id or "",
                        observation=self.observation,
                    )
                    for entry in self.retrieved_problems.values()
                ],
                "connections": [
                    connection_search_result(entry)
                    for entry in self.retrieved_connections.values()
                ],
                "reductions": [
                    entry_summary(entry)
                    for entry in self.retrieved_reductions.values()
                ],
            },
            "lean_path_api": {
                "one_edge": (
                    "ComplexityReduction.Certificate.CertifiedPath.step reduction"
                ),
                "append_edge": (
                    "ComplexityReduction.Certificate.CertifiedPath.cons priorPath reduction"
                ),
                "composition_rule": (
                    "Start with step on the first selected directed edge, then append each "
                    "later selected edge with cons in exactly the selected order. An "
                    "exact_defeq or accepts_exact_defeq problem match needs no adapter edge."
                ),
                "term_only": (
                    "lean_term must be one expression of expected_lean_type, not a command "
                    "or declaration"
                ),
                "constructor_requirement": (
                    "A CertifiedReduction declaration alone is not a CertifiedPath. With "
                    "one selected edge, lean_term must use CertifiedPath.step. With later "
                    "edges, append each one using CertifiedPath.cons."
                ),
            },
            "workflow_rules": workflow_rules,
            "response_options": {
                "inspect_architecture": {
                    "action": "inspect_architecture",
                    "queries": [
                        {
                            "terms": ["optional words"],
                            "source_node_ids": ["optional node"],
                            "limit": 8,
                        }
                    ],
                },
                "search_problems": {
                    "action": "search_problems",
                    "searches": problem_search_example,
                },
                "search_connections": {
                    "action": "search_connections",
                    "searches": [
                        {
                            "source_node_ids": ["input or current node"],
                            "target_node_ids": ["selected problem node"],
                            "limit": 8,
                        }
                    ],
                },
                "search_reductions": {
                    "action": "search_reductions",
                    "searches": [
                        {
                            "source_node_ids": ["current path node"],
                            "target_node_ids": ["optional next or final node"],
                            "limit": 8,
                        }
                    ],
                },
                "finish": {
                    "action_literal": "finish",
                    "required_fields": [
                        "action",
                        "matched_problem",
                        "match_relation",
                        "connection_entry_id",
                        "reduction_declarations",
                        "target_declaration",
                        "lean_term",
                        "explanation",
                    ],
                    "field_rules": {
                        "matched_problem": (
                            "string: one exact declaration returned by search_problems"
                        ),
                        "match_relation": (
                            match_relation_rule
                        ),
                        "connection_entry_id": {
                            "type": "string or null",
                            "when_exact_defeq": None,
                            "when_accepts_exact_defeq": None,
                            "otherwise": connection_otherwise_rule,
                        },
                        "reduction_declarations": (
                            "array of strings returned by search_reductions, in path order"
                        ),
                        "target_declaration": self.target_observation.input_declaration,
                        "lean_term": (
                            "string containing one complete expression of expected_lean_type"
                        ),
                        "explanation": "short natural-language reason",
                    },
                },
                "stop": {
                    "action_literal": "stop",
                    "required_fields": ["action", "failure_code", "explanation"],
                    "field_rules": {
                        "failure_code": (
                            stop_failure_codes
                        ),
                        "matched_problem": (
                            "required only for no_existing_reduction_route"
                        ),
                        "match_relation": (
                            "required only for no_existing_reduction_route"
                        ),
                        "connection_entry_id": {
                            "type": "string or null",
                            "when_exact_defeq": None,
                            "when_accepts_exact_defeq": None,
                        },
                        "explanation": (
                            "what was queried, what is absent, and why proof cannot continue"
                        ),
                    },
                },
            },
            "stop_audit_requirements": stop_audit_requirements,
            "constraints": {
                "llm_selects_problem_connection_and_route": True,
                "all_selected_facts_must_have_been_retrieved": True,
                "full_catalogs_are_not_included": True,
                "new_mathematical_reductions_forbidden": True,
                "lean_runs_only_after_all_model_tasks_finish": True,
            },
        }

    def build_prompt(self) -> str:
        return json.dumps(
            self.prompt_payload(),
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        )


def generate_lean_path_from_observed_input(
    *,
    observation: LeanInputObservation,
    target_observation: LeanInputObservation,
    problem_catalog: ProblemCatalog,
    connection_catalog: ConnectionCatalog,
    reduction_catalog: TypedCatalog,
    client: DeepSeekClient,
    maximum_query_rounds: int = MAX_INPUT_QUERY_ROUNDS,
) -> ObservedInputPlannerResult:
    """Run the bounded query protocol without invoking Lean between model turns."""

    try:
        session = ObservedInputPlanningSession(
            observation=observation,
            target_observation=target_observation,
            problem_catalog=problem_catalog,
            connection_catalog=connection_catalog,
            reduction_catalog=reduction_catalog,
            maximum_query_rounds=maximum_query_rounds,
        )
    except InputPlanningError as error:
        return ObservedInputPlannerResult(
            plan=None,
            lean_term=None,
            problem_match=None,
            selected_connection=None,
            reduction_declarations=(),
            explanation=error.explanation,
            failure_code=error.failure_code,
        )
    prompts: list[str] = []
    responses: list[ModelResponse] = []
    for _ in range(MAX_INPUT_MODEL_TURNS):
        prompt = session.build_prompt()
        response = client.complete_json(
            system=OBSERVED_INPUT_SYSTEM_PROMPT,
            prompt=prompt,
        )
        prompts.append(prompt)
        responses.append(response)
        if not response.ok:
            return ObservedInputPlannerResult(
                plan=None,
                lean_term=None,
                problem_match=None,
                selected_connection=None,
                reduction_declarations=(),
                explanation=response.error or "模型 API 调用失败，未得到可处理的回答。",
                failure_code="model_api_failure",
                model_prompts=tuple(prompts),
                model_responses=tuple(responses),
                query_trace=tuple(session.trace),
            )
        payload = extract_json_object(response.content)
        if payload is None:
            error = InputPlanningError(
                "invalid_model_json",
                "模型回答不是一个 JSON 对象，无法判断它要查询什么或提交什么。",
            )
            session.record_protocol_feedback(error)
            if len(session.protocol_feedback) >= MAX_INPUT_PROTOCOL_FEEDBACK:
                return ObservedInputPlannerResult(
                    plan=None,
                    lean_term=None,
                    problem_match=None,
                    selected_connection=None,
                    reduction_declarations=(),
                    explanation=error.explanation,
                    failure_code=error.failure_code,
                    model_prompts=tuple(prompts),
                    model_responses=tuple(responses),
                    query_trace=tuple(session.trace),
                )
            continue
        payload = _normalize_action(payload)
        try:
            if payload.get("action") == "finish":
                result = session.finish(payload)
                return ObservedInputPlannerResult(
                    plan=result.plan,
                    lean_term=result.lean_term,
                    problem_match=result.problem_match,
                    selected_connection=result.selected_connection,
                    reduction_declarations=result.reduction_declarations,
                    explanation=result.explanation,
                    model_prompts=tuple(prompts),
                    model_responses=tuple(responses),
                    query_trace=tuple(session.trace),
                )
            if payload.get("action") == "stop":
                result = session.stop(payload)
                return ObservedInputPlannerResult(
                    plan=None,
                    lean_term=None,
                    problem_match=result.problem_match,
                    selected_connection=result.selected_connection,
                    reduction_declarations=(),
                    explanation=result.explanation,
                    failure_code=result.failure_code,
                    model_prompts=tuple(prompts),
                    model_responses=tuple(responses),
                    query_trace=tuple(session.trace),
                )
            session.execute_query(payload)
        except InputPlanningError as error:
            session.record_protocol_feedback(error)
            if len(session.protocol_feedback) >= MAX_INPUT_PROTOCOL_FEEDBACK:
                return ObservedInputPlannerResult(
                    plan=None,
                    lean_term=None,
                    problem_match=None,
                    selected_connection=None,
                    reduction_declarations=(),
                    explanation=error.explanation,
                    failure_code=error.failure_code,
                    model_prompts=tuple(prompts),
                    model_responses=tuple(responses),
                    query_trace=tuple(session.trace),
                )
    return ObservedInputPlannerResult(
        plan=None,
        lean_term=None,
        problem_match=None,
        selected_connection=None,
        reduction_declarations=(),
        explanation=(
            "模型在允许的会话轮数内没有提交完整路径和 Lean 表达式。"
            + (
                " 最后一次协议反馈："
                + session.protocol_feedback[-1]["explanation"]
                if session.protocol_feedback
                else ""
            )
        ),
        failure_code="model_did_not_finish",
        model_prompts=tuple(prompts),
        model_responses=tuple(responses),
        query_trace=tuple(session.trace),
    )
