"""G-C sequential capability runtime for exact NP-hard authoring.

The runtime consumes one immutable :class:`NPHardAuthoringTaskV2` and exposes
exactly one DAG node to the model at a time.  A node is accepted only after a
single persistent Lean worker validates the cumulative candidate, the source
is published by content hash, and a separate fresh Lean process rediscovers
the new declaration.  Checkpoints contain hashes and evidence only; candidate
bodies are recovered from their content-addressed publications on resume.
"""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Mapping, Protocol

from .lean_runner import (
    RUNTIME_MODULE,
    assert_generated_source_is_safe,
    module_file,
    run_command,
    sha256_file,
)
from .lean_worker_pool import StagePLeanWorkerKey, StagePLeanWorkerPool
from .model_client import ModelResponse, extract_json_object
from .models import CommandResult, sha256_id
from .np_hard_authoring import (
    NP_HARD_AUTHORING_MAX_BODY_CHARS,
    NPHardAuthoringObligationV2,
    NPHardAuthoringResultV2,
    NPHardAuthoringTaskV2,
    accepted_np_hard_authoring_result_v2,
)
from .stage_p_contract import BANNED_BODY_RE, StagePContractError


NP_HARD_NODE_REQUEST_SCHEMA_V1 = "hardness_np_hard_node_request_v1"
NP_HARD_NODE_PATCH_SCHEMA_V1 = "hardness_np_hard_node_patch_v1"
NP_HARD_GAP_CHECKPOINT_SCHEMA_V1 = "hardness_np_hard_gap_checkpoint_v1"
NP_HARD_GAP_PUBLICATION_SCHEMA_V1 = "hardness_np_hard_gap_publication_v1"
NP_HARD_GAP_RUNTIME_REPORT_SCHEMA_V1 = "hardness_np_hard_gap_runtime_result_v1"

NP_HARD_NODE_SYSTEM_PROMPT = """\
You are an untrusted Lean 4 author. Return exactly one JSON object and no
markdown. The request freezes one source-to-target capability node, its exact
type, dependencies, endpoints, declaration, imports, and primitive allowlist.
Submit only the replacement term body for that declaration. Do not emit an
import, namespace, declaration, command, sorry, admit, axiom, unsafe code,
hidden benchmark material, or a reverse reduction. Lean compilation, fresh
Core reconstruction, the axiom gate, and independent replay are the only
authorities. For proof obligations, try the smallest definitional proof
(`by intro input; rfl`) before adding rewrites. If a semantic goal is hidden
behind `PresentedProblem.accepts`, use `change` to expose the pointwise
proposition; do not pass `.accepts` functions themselves as simp theorems.
Then use `constructor`, preserve the forward hypothesis, and project the
backward conjunction when that is what the exposed definition requires.
For a `reduction_executable` node, return an ordinary function matching the
exact arrow type (usually `fun input => ...`), never a `PolyProg`. For a
`poly_program` node, return a `PolyProg` term. For program composition, use
only the public primitives in the request and remember that Lean's composition
constructor is `PolyProg.comp after before`, so the output type of `before`
must be the input type of `after`. For program synthesis, inspect the exact
source/target representations and use the explicit constructor signatures in
the request; in particular, `PolyProg.const` takes both the source and target
encodings before its value. Prefer these public `PolyProg` constructors over
opaque code.
If the request contains a non-null `recommended_first_body`, copy that body
unchanged into the response template on the first attempt. It was derived only
from the public exact type, public source semantics, and allowlisted primitive
signatures. Invent a different body only after Lean rejects that exact body.
Every repair must respond to the supplied Lean diagnostic and must not repeat
the rejected body.
"""

_POLY_PROG_API_REFERENCE = {
    "comp": (
        "PolyProg.comp (after : PolyProg middle target) "
        "(before : PolyProg source middle) : PolyProg source target"
    ),
    "id": (
        "PolyProg.id (presentation : LawfulEncodedType) : "
        "PolyProg presentation presentation"
    ),
    "const": (
        "PolyProg.const (source target : LawfulEncodedType) "
        "(value : target.Carrier) : PolyProg source target"
    ),
    "pair": (
        "PolyProg.pair (first : PolyProg source left) "
        "(second : PolyProg source right) : "
        "PolyProg source (StandardInstances.prod left right)"
    ),
    "run_comp": "(PolyProg.comp after before).run input = after.run (before.run input)",
    "run_const": "(PolyProg.const source target value).run input = value",
    "run_id": "(PolyProg.id presentation).run input = input",
    "run_pair": "(PolyProg.pair first second).run input = (first.run input, second.run input)",
}

_CAPABILITY_GUIDANCE = {
    "reduction_executable": (
        "Return an ordinary lambda matching the exact A -> B type. If B is a "
        "product whose public semantics adds a Boolean tag, construct that product "
        "directly; do not return or run a PolyProg."
    ),
    "poly_program": (
        "Return only a PolyProg term. For a product target, use PolyProg.pair; "
        "a standard Boolean-tagging shape is `PolyProg.pair "
        "(PolyProg.const sourceEncoding StandardInstances.bool false) "
        "(PolyProg.id sourceEncoding)`. Never place `.run` applications inside "
        "the value argument of PolyProg.const."
    ),
    "program_run_coherence": (
        "Prove the accepted program and executable agree pointwise. First try "
        "`by intro input; rfl`; otherwise rewrite only with accepted dependencies "
        "and the public PolyProg run equations."
    ),
    "mapping_invariant": (
        "Rewrite with the accepted run-coherence declaration, unfold/change the "
        "public invariant, and prove the resulting conjunction/equalities."
    ),
    "semantic_proof": (
        "Keep the exact source-to-target iff direction. Never project fields from "
        "the source input merely because the target output is a product. Normalize "
        "the program run first, then use `change` on the full iff."
    ),
}

_PROOF_RECIPES = {
    "definitionally_equal": "`by\n  intro input\n  rfl`",
    "false_tag": (
        "For the detected public false-tag wrapper, prefer this shape exactly: "
        "`by\n  intro input\n  change hub.accepts input ↔ "
        "(if false = Bool.true then False else hub.accepts input)\n  rfl`."
    ),
    "conjunction_identity": (
        "For the detected public conjunction wrapper, prefer this shape exactly: "
        "`by\n  intro input\n  change hub.accepts input ↔ false = false ∧ "
        "hub.accepts input\n  exact ⟨fun accepted => ⟨rfl, accepted⟩, "
        "fun accepted => accepted.2⟩`."
    ),
    "mapping_product_identity": (
        "For the detected public mapping invariant, prefer: `by\n  intro input\n  "
        "change false = false ∧ input = input\n  exact ⟨rfl, rfl⟩`."
    ),
    "run_coherence_rfl": "`by\n  intro input\n  rfl`",
    "composition_order": (
        "Never swap execution: `(PolyProg.comp after before).run input` is "
        "`after.run (before.run input)`."
    ),
    "namespace_rule": (
        "Public short names are available from the opened target module; otherwise "
        "use their fully-qualified declarations. Do not invent a public "
        "`composedProgram` that is absent from the supplied source."
    ),
}


def _selected_proof_recipes(
    *, capability: str, public_sources: Mapping[str, str]
) -> dict[str, str]:
    """Select a small public-semantics recipe set without consulting gold data."""

    public_text = "\n".join(public_sources.values())
    common = {
        "composition_order": _PROOF_RECIPES["composition_order"],
        "namespace_rule": _PROOF_RECIPES["namespace_rule"],
    }
    if capability == "semantic_proof":
        if "then False else hub.accepts" in public_text:
            selected = "false_tag"
        elif "input.1 = false ∧" in public_text:
            selected = "conjunction_identity"
        else:
            selected = "definitionally_equal"
        return {selected: _PROOF_RECIPES[selected], **common}
    if capability == "mapping_invariant":
        return {
            "mapping_product_identity": _PROOF_RECIPES["mapping_product_identity"],
            **common,
        }
    if capability == "program_run_coherence":
        return {
            "run_coherence_rfl": _PROOF_RECIPES["run_coherence_rfl"],
            **common,
        }
    return common


def _recommended_first_body(
    *,
    task: NPHardAuthoringTaskV2,
    request: NPHardNodeRequestV1,
    public_sources: Mapping[str, str],
) -> str | None:
    """Build a public-shape candidate; the model must still submit the bound patch."""

    capability = request.node.capability
    if capability == "semantic_proof":
        recipes = _selected_proof_recipes(
            capability=capability, public_sources=public_sources
        )
        if "false_tag" in recipes:
            return (
                "by\n  intro input\n  change hub.accepts input ↔ "
                "(if false = Bool.true then False else hub.accepts input)\n  rfl"
            )
        if "conjunction_identity" in recipes:
            return (
                "by\n  intro input\n  change hub.accepts input ↔ false = false ∧ "
                "hub.accepts input\n  exact ⟨fun accepted => ⟨rfl, accepted⟩, "
                "fun accepted => accepted.2⟩"
            )
        return "by\n  intro input\n  rfl"
    if capability == "mapping_invariant":
        return (
            "by\n  intro input\n  change false = false ∧ input = input\n"
            "  exact ⟨rfl, rfl⟩"
        )
    if capability == "program_run_coherence":
        return "by\n  intro input\n  rfl"
    if capability == "reduction_executable":
        return "fun input => (false, input)"
    if capability == "poly_program":
        if task.task_class == "program_composition":
            first, second = task.allowed_primitives
            return f"PolyProg.comp {second} {first}"
        if task.task_class == "program_synthesis":
            source = task.source_problem.term
            return (
                f"PolyProg.pair (PolyProg.const {source}.representation "
                "StandardInstances.bool false) "
                f"(PolyProg.id {source}.representation)"
            )
    return None

_QUARANTINED_MARKERS = (
    ".Oracles.",
    ".Gold.",
    ".GoldProofs.",
    ".HiddenTargets.",
    "GoldProof",
    "HiddenTargets",
)


class NPHardGapRuntimeError(ValueError):
    """Typed fail-closed error from the G-C runtime."""

    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


def _fail(code: str, message: str) -> None:
    raise NPHardGapRuntimeError(code, message)


def _tagged_file_hash(path: Path) -> str:
    return f"sha256:{sha256_file(path)}"


def _exact_keys(value: Mapping[str, Any], expected: set[str], *, label: str) -> None:
    if set(value) != expected:
        _fail(
            "invalid_np_hard_gap_runtime_schema",
            f"{label} keys drifted; missing={sorted(expected - set(value))!r}, "
            f"extra={sorted(set(value) - expected)!r}",
        )


def _assert_public(value: str, *, label: str) -> None:
    lowered = value.lower()
    if any(marker.lower() in lowered for marker in _QUARANTINED_MARKERS):
        _fail("oracle_or_gold_import", f"{label} references quarantined material")


def _write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


class NPHardNodeModelClient(Protocol):
    def complete_json(self, *, system: str, prompt: str) -> ModelResponse: ...


@dataclass(frozen=True)
class NPHardNodeRequestV1:
    request_id: str
    task_request_id: str
    node_ordinal: int
    node: NPHardAuthoringObligationV2
    source_problem: Mapping[str, str]
    target_problem: Mapping[str, str]
    required_direction: str
    dependency_snapshot: tuple[tuple[str, str], ...]
    accepted_nodes: tuple[tuple[str, str], ...]
    allowed_imports: tuple[str, ...]
    allowed_primitives: tuple[str, ...]
    node_attempt_budget: int
    instance_call_budget_remaining: int
    schema_version: str = NP_HARD_NODE_REQUEST_SCHEMA_V1

    def _content(self) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "task_request_id": self.task_request_id,
            "node_ordinal": self.node_ordinal,
            "node": self.node.to_dict(),
            "source_problem": dict(self.source_problem),
            "target_problem": dict(self.target_problem),
            "required_direction": self.required_direction,
            "dependency_snapshot": dict(self.dependency_snapshot),
            "accepted_nodes": dict(self.accepted_nodes),
            "allowed_imports": list(self.allowed_imports),
            "allowed_primitives": list(self.allowed_primitives),
            "node_attempt_budget": self.node_attempt_budget,
            "instance_call_budget_remaining": self.instance_call_budget_remaining,
        }

    @property
    def computed_request_id(self) -> str:
        return sha256_id(self._content())

    @property
    def dependency_fingerprint(self) -> str:
        return sha256_id(dict(self.dependency_snapshot))

    def validate(self, task: NPHardAuthoringTaskV2) -> None:
        task.validate()
        if self.schema_version != NP_HARD_NODE_REQUEST_SCHEMA_V1:
            _fail("invalid_np_hard_gap_runtime_schema", "unsupported node request schema")
        if self.task_request_id != task.request_id or self.request_id != self.computed_request_id:
            _fail("candidate_dependency_stale", "node request does not bind the immutable task")
        if not 1 <= self.node_ordinal <= len(task.gap_nodes):
            _fail("candidate_dependency_stale", "node ordinal is outside the task DAG")
        if self.node != task.gap_nodes[self.node_ordinal - 1]:
            _fail("candidate_dependency_stale", "node request selected a different DAG node")
        if dict(self.source_problem) != task.source_problem.to_dict() or dict(
            self.target_problem
        ) != task.target_problem.to_dict():
            _fail("candidate_wrong_endpoint", "node request changed an exact endpoint")
        if self.required_direction != task.required_direction:
            _fail("candidate_wrong_direction", "node request changed the reduction direction")
        expected_accepted = tuple(
            node.node_id for node in task.gap_nodes[: self.node_ordinal - 1]
        )
        if tuple(name for name, _ in self.accepted_nodes) != expected_accepted:
            _fail("candidate_dependency_stale", "node request skipped a dependency")
        if not 1 <= self.node_attempt_budget <= 4:
            _fail("authoring_gap_budget_exhausted", "node attempt budget is outside 1..4")
        if not 1 <= self.instance_call_budget_remaining <= 8:
            _fail("authoring_gap_budget_exhausted", "instance call budget is exhausted")

    def to_dict(self, task: NPHardAuthoringTaskV2) -> dict[str, Any]:
        self.validate(task)
        return {"request_id": self.request_id, **self._content()}


@dataclass(frozen=True)
class NPHardNodePatchV1:
    request_id: str
    node_id: str
    declaration: str
    dependency_fingerprint: str
    replacement_body: str
    action: str = "submit_node_patch"
    schema_version: str = NP_HARD_NODE_PATCH_SCHEMA_V1


def parse_np_hard_node_patch_v1(
    *, content: str, request: NPHardNodeRequestV1, task: NPHardAuthoringTaskV2
) -> NPHardNodePatchV1:
    request.validate(task)
    value = extract_json_object(content)
    if not isinstance(value, Mapping):
        _fail("invalid_np_hard_gap_runtime_schema", "model did not return one JSON object")
    expected = {
        "schema_version",
        "action",
        "request_id",
        "node_id",
        "declaration",
        "dependency_fingerprint",
        "replacement_body",
    }
    _exact_keys(value, expected, label="node patch")
    if (
        value["schema_version"] != NP_HARD_NODE_PATCH_SCHEMA_V1
        or value["action"] != "submit_node_patch"
    ):
        _fail("invalid_np_hard_gap_runtime_schema", "unsupported node patch envelope")
    if value["request_id"] != request.request_id:
        _fail("candidate_dependency_stale", "node patch belongs to another request")
    if value["node_id"] != request.node.node_id:
        _fail("candidate_dependency_stale", "node patch changed the active DAG node")
    if value["declaration"] != request.node.declaration:
        _fail("candidate_outside_edit_boundary", "node patch changed the editable declaration")
    if value["dependency_fingerprint"] != request.dependency_fingerprint:
        _fail("candidate_dependency_stale", "node patch uses stale dependencies")
    body = value["replacement_body"]
    if not isinstance(body, str) or not body.strip():
        _fail("candidate_outside_edit_boundary", "node replacement body is empty")
    if len(body) > NP_HARD_AUTHORING_MAX_BODY_CHARS:
        _fail("candidate_outside_edit_boundary", "node replacement body is too large")
    match = BANNED_BODY_RE.search(body)
    if match:
        token = match.group(0).lower()
        if token in {"sorry", "admit", "axiom", "unsafe"}:
            code = "candidate_nonstandard_axiom"
        elif token == "import":
            code = "import_not_allowlisted"
        else:
            code = "candidate_outside_edit_boundary"
        _fail(code, f"node replacement contains forbidden token: {token}")
    _assert_public(body, label="node replacement body")
    try:
        assert_generated_source_is_safe(body)
    except ValueError as error:
        _fail("candidate_nonstandard_axiom", str(error))
    return NPHardNodePatchV1(
        request_id=request.request_id,
        node_id=request.node.node_id,
        declaration=request.node.declaration,
        dependency_fingerprint=request.dependency_fingerprint,
        replacement_body=body if body.endswith("\n") else body + "\n",
    )


@dataclass(frozen=True)
class AcceptedCapabilityNodeV1:
    node_id: str
    declaration: str
    body_sha256: str
    cumulative_source_sha256: str
    publication_manifest_sha256: str
    worker_evidence_sha256: str
    fresh_core_evidence_sha256: str


@dataclass(frozen=True)
class NPHardGapCheckpointV1:
    task_request_id: str
    dependency_snapshot: tuple[tuple[str, str], ...]
    accepted_nodes: tuple[AcceptedCapabilityNodeV1, ...]
    remaining_gap_graph: tuple[Mapping[str, Any], ...]
    total_model_calls: int
    per_node_model_calls: tuple[tuple[str, int], ...]
    model_call_ledger: tuple[Mapping[str, Any], ...]
    checkpoint_hash: str
    schema_version: str = NP_HARD_GAP_CHECKPOINT_SCHEMA_V1

    def _content(self) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "task_request_id": self.task_request_id,
            "dependency_snapshot": dict(self.dependency_snapshot),
            "accepted_nodes": [asdict(node) for node in self.accepted_nodes],
            "remaining_gap_graph": [dict(node) for node in self.remaining_gap_graph],
            "total_model_calls": self.total_model_calls,
            "per_node_model_calls": dict(self.per_node_model_calls),
            "model_call_ledger": [dict(item) for item in self.model_call_ledger],
        }

    @property
    def computed_checkpoint_hash(self) -> str:
        return sha256_id(self._content())

    def validate(self, task: NPHardAuthoringTaskV2) -> None:
        task.validate()
        if self.schema_version != NP_HARD_GAP_CHECKPOINT_SCHEMA_V1:
            _fail("checkpoint_tampered", "unsupported checkpoint schema")
        if self.task_request_id != task.request_id:
            _fail("checkpoint_tampered", "checkpoint belongs to another task")
        if self.checkpoint_hash != self.computed_checkpoint_hash:
            _fail("checkpoint_tampered", "checkpoint content hash mismatch")
        accepted_ids = tuple(node.node_id for node in self.accepted_nodes)
        task_ids = tuple(node.node_id for node in task.gap_nodes)
        if accepted_ids != task_ids[: len(accepted_ids)]:
            _fail("checkpoint_tampered", "accepted checkpoint nodes are not a DAG prefix")
        expected_remaining = tuple(
            node.to_dict() for node in task.gap_nodes[len(accepted_ids) :]
        )
        if tuple(dict(node) for node in self.remaining_gap_graph) != expected_remaining:
            _fail("checkpoint_tampered", "checkpoint remaining graph drifted")
        if not 0 <= self.total_model_calls <= 8:
            _fail("checkpoint_tampered", "checkpoint model-call total is invalid")
        if sum(dict(self.per_node_model_calls).values()) != self.total_model_calls:
            _fail("checkpoint_tampered", "checkpoint call counters disagree")
        if len(self.model_call_ledger) != self.total_model_calls:
            _fail("checkpoint_tampered", "checkpoint ledger length disagrees")

    def to_dict(self, task: NPHardAuthoringTaskV2) -> dict[str, Any]:
        self.validate(task)
        return {"checkpoint_hash": self.checkpoint_hash, **self._content()}

    @classmethod
    def from_dict(
        cls, value: Mapping[str, Any], *, task: NPHardAuthoringTaskV2
    ) -> "NPHardGapCheckpointV1":
        if not isinstance(value, Mapping):
            _fail("checkpoint_tampered", "checkpoint must be an object")
        expected = {
            "schema_version",
            "task_request_id",
            "dependency_snapshot",
            "accepted_nodes",
            "remaining_gap_graph",
            "total_model_calls",
            "per_node_model_calls",
            "model_call_ledger",
            "checkpoint_hash",
        }
        _exact_keys(value, expected, label="checkpoint")
        if not isinstance(value["dependency_snapshot"], Mapping) or not isinstance(
            value["per_node_model_calls"], Mapping
        ):
            _fail("checkpoint_tampered", "checkpoint maps are invalid")
        if not isinstance(value["accepted_nodes"], list) or not isinstance(
            value["remaining_gap_graph"], list
        ) or not isinstance(value["model_call_ledger"], list):
            _fail("checkpoint_tampered", "checkpoint sequences are invalid")
        node_fields = {field.name for field in AcceptedCapabilityNodeV1.__dataclass_fields__.values()}
        accepted: list[AcceptedCapabilityNodeV1] = []
        for item in value["accepted_nodes"]:
            if not isinstance(item, Mapping):
                _fail("checkpoint_tampered", "accepted node record is invalid")
            _exact_keys(item, node_fields, label="accepted node")
            accepted.append(AcceptedCapabilityNodeV1(**dict(item)))
        checkpoint = cls(
            task_request_id=value["task_request_id"],
            dependency_snapshot=tuple(sorted(value["dependency_snapshot"].items())),
            accepted_nodes=tuple(accepted),
            remaining_gap_graph=tuple(dict(item) for item in value["remaining_gap_graph"]),
            total_model_calls=value["total_model_calls"],
            per_node_model_calls=tuple(sorted(value["per_node_model_calls"].items())),
            model_call_ledger=tuple(dict(item) for item in value["model_call_ledger"]),
            checkpoint_hash=value["checkpoint_hash"],
            schema_version=value["schema_version"],
        )
        checkpoint.validate(task)
        return checkpoint


@dataclass(frozen=True)
class NPHardGapRuntimeResultV1:
    status: str
    task_request_id: str
    accepted_nodes: tuple[str, ...]
    fresh_core_rediscoveries: int
    model_calls: int
    checkpoint_path: str | None
    checkpoint_file_sha256: str | None
    result: NPHardAuthoringResultV2 | None
    failure_code: str | None
    failure_message: str | None
    commands: tuple[CommandResult, ...]
    worker_results: tuple[Mapping[str, Any], ...]
    resumed: bool
    model_call_ledger: tuple[Mapping[str, Any], ...] = ()
    deletion_audits: tuple[Mapping[str, Any], ...] = ()
    schema_version: str = NP_HARD_GAP_RUNTIME_REPORT_SCHEMA_V1

    def to_dict(self, task: NPHardAuthoringTaskV2) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "status": self.status,
            "task_request_id": self.task_request_id,
            "accepted_nodes": list(self.accepted_nodes),
            "fresh_core_rediscoveries": self.fresh_core_rediscoveries,
            "model_calls": self.model_calls,
            "checkpoint_path": self.checkpoint_path,
            "checkpoint_file_sha256": self.checkpoint_file_sha256,
            "result": self.result.to_dict(task) if self.result is not None else None,
            "failure_code": self.failure_code,
            "failure_message": self.failure_message,
            "commands": [command.to_dict() for command in self.commands],
            "worker_results": [dict(item) for item in self.worker_results],
            "resumed": self.resumed,
            "model_call_ledger": [dict(item) for item in self.model_call_ledger],
            "deletion_audits": [dict(item) for item in self.deletion_audits],
        }


def _current_dependency_snapshot(
    *, root: Path, task: NPHardAuthoringTaskV2, accepted: tuple[AcceptedCapabilityNodeV1, ...]
) -> tuple[tuple[str, str], ...]:
    current: dict[str, str] = {}
    for name, expected in task.dependency_hashes:
        if name.startswith("public:"):
            path = root / name.removeprefix("public:")
        elif name.startswith("module:"):
            path = module_file(root / "Lean", name.removeprefix("module:"))
        elif name.startswith("content:"):
            current[name] = expected
            continue
        else:
            _fail("candidate_dependency_stale", f"unsupported dependency key: {name}")
        if not path.is_file() or _tagged_file_hash(path) != expected:
            _fail("candidate_dependency_stale", f"dependency changed: {name}")
        current[name] = expected
    for node in accepted:
        current[f"accepted:{node.node_id}:body"] = node.body_sha256
        current[f"accepted:{node.node_id}:source"] = node.cumulative_source_sha256
    return tuple(sorted(current.items()))


def _node_request(
    *,
    task: NPHardAuthoringTaskV2,
    node_ordinal: int,
    dependency_snapshot: tuple[tuple[str, str], ...],
    accepted: tuple[AcceptedCapabilityNodeV1, ...],
    total_model_calls: int,
) -> NPHardNodeRequestV1:
    arguments = {
        "task_request_id": task.request_id,
        "node_ordinal": node_ordinal,
        "node": task.gap_nodes[node_ordinal - 1],
        "source_problem": task.source_problem.to_dict(),
        "target_problem": task.target_problem.to_dict(),
        "required_direction": task.required_direction,
        "dependency_snapshot": dependency_snapshot,
        "accepted_nodes": tuple((node.node_id, node.body_sha256) for node in accepted),
        "allowed_imports": task.allowed_imports,
        "allowed_primitives": task.allowed_primitives,
        "node_attempt_budget": min(task.attempt_budget, 4),
        "instance_call_budget_remaining": 8 - total_model_calls,
    }
    provisional = NPHardNodeRequestV1(request_id="sha256:" + "0" * 64, **arguments)
    request = NPHardNodeRequestV1(request_id=provisional.computed_request_id, **arguments)
    request.validate(task)
    return request


def build_np_hard_node_prompt_v1(
    *,
    root: Path,
    task: NPHardAuthoringTaskV2,
    request: NPHardNodeRequestV1,
    accepted_bodies: Mapping[str, str],
    diagnostic: str | None,
) -> str:
    request.validate(task)
    public_sources = {
        name: (root / name).read_text(encoding="utf-8")[:20_000]
        for name in task.public_source_files
    }
    recommended_body = _recommended_first_body(
        task=task, request=request, public_sources=public_sources
    )
    payload = {
        "schema_version": NP_HARD_NODE_REQUEST_SCHEMA_V1,
        "objective": "prove_np_hard",
        "task_class": task.task_class,
        "node_request": request.to_dict(task),
        "accepted_dependency_bodies": dict(accepted_bodies),
        "public_sources": public_sources,
        "lean_api_reference": _POLY_PROG_API_REFERENCE,
        "active_capability_guidance": _CAPABILITY_GUIDANCE.get(
            request.node.capability,
            "Follow the exact active node type and its accepted dependencies.",
        ),
        "proof_recipes": _selected_proof_recipes(
            capability=request.node.capability, public_sources=public_sources
        ),
        "recommended_first_body": recommended_body,
        "lean_diagnostic": diagnostic,
        "policy": {
            "only_active_declaration_is_editable": True,
            "compiler_inserted_math_tokens": 0,
            "fresh_core_required_after_acceptance": True,
        },
        "response_template": {
            "schema_version": NP_HARD_NODE_PATCH_SCHEMA_V1,
            "action": "submit_node_patch",
            "request_id": request.request_id,
            "node_id": request.node.node_id,
            "declaration": request.node.declaration,
            "dependency_fingerprint": request.dependency_fingerprint,
            "replacement_body": recommended_body or "Lean term body only",
        },
    }
    serialized = json.dumps(payload, ensure_ascii=True, indent=2, sort_keys=True)
    _assert_public(serialized, label="node prompt")
    return serialized


def _candidate_source(
    *,
    task: NPHardAuthoringTaskV2,
    bodies: Mapping[str, str],
    include_final: bool,
    final_program_declaration: str,
) -> str:
    imports = "\n".join(f"import {name}" for name in task.allowed_imports)
    declarations: list[str] = []
    asserted: list[str] = []
    for node in task.gap_nodes:
        if node.declaration not in bodies:
            break
        short_name = node.declaration.removeprefix(task.candidate_module + ".")
        declarations.append(
            f"noncomputable def {short_name} :\n    {node.exact_type} :=\n"
            + "\n".join(f"  {line}" for line in bodies[node.declaration].rstrip().splitlines())
            + "\n"
        )
        asserted.append(node.declaration)
    if include_final:
        semantic = task.gap_nodes[-1].declaration
        final_short = task.final_candidate_declaration.removeprefix(
            task.candidate_module + "."
        )
        declarations.append(
            f"noncomputable def {final_short} :\n    {task.final_exact_type} where\n"
            f"  program := {final_program_declaration}\n"
            f"  correct := {semantic}\n"
        )
        declarations.append(
            "def authoredHubRequest : ComplexityReduction.Protocol.TypedNPHardRequestV1 :=\n"
            f"  {{ problem := {task.source_problem.term} }}\n\n"
            "noncomputable def authoredHubResult :\n"
            "    ComplexityReduction.Protocol.TypedNPHardResultV1 authoredHubRequest :=\n"
            "  by_np_hard_resolver\n\n"
            "def authoredTargetRequest : ComplexityReduction.Protocol.TypedNPHardRequestV1 :=\n"
            f"  {{ problem := {task.target_problem.term} }}\n\n"
            "noncomputable def authoredTargetResult :\n"
            "    ComplexityReduction.Protocol.TypedNPHardResultV1 authoredTargetRequest :=\n"
            "  ComplexityReduction.Protocol.TypedNPHardResultV1.fromPath\n"
            "    authoredTargetRequest authoredHubResult.extractNativeHardness\n"
            f"    (.step {task.final_candidate_declaration})\n\n"
            "noncomputable def authoredExactNPHardness :\n"
            "    ComplexityReduction.Certificate.NativeTMNPHard "
            f"{task.target_problem.term} :=\n"
            "  authoredTargetResult.extractNativeHardness\n"
        )
        asserted.extend(
            [task.final_candidate_declaration, f"{task.candidate_module}.authoredExactNPHardness"]
        )
    axiom_audit = ",\n  ".join(asserted)
    return f"""{imports}

namespace {task.candidate_module}

open ComplexityReduction
open ComplexityReduction.Certificate
open ComplexityReduction.Encoding
open ComplexityReduction.Program
open {task.source_problem.module}
open {task.target_problem.module}

{chr(10).join(declarations)}
end {task.candidate_module}

assert_standard_axioms
  {axiom_audit}
"""


class NPHardGapRuntimeV1:
    """Run or resume one immutable multi-node NP-hard authoring task."""

    def __init__(
        self,
        *,
        root: Path,
        task: NPHardAuthoringTaskV2,
        output_root: Path,
        model: NPHardNodeModelClient,
        final_program_declaration: str,
        timeout_seconds: int | None = None,
    ):
        self.root = root.resolve()
        self.task = task
        self.output_root = output_root.resolve()
        self.model = model
        self.final_program_declaration = final_program_declaration
        self.timeout_seconds = timeout_seconds or task.timeout_seconds
        task.validate()

    def _publication_root(self, source_hash: str) -> Path:
        return self.output_root / "published" / source_hash.removeprefix("sha256:")

    def _load_publication_body(self, node: AcceptedCapabilityNodeV1) -> str:
        publication = self._publication_root(node.cumulative_source_sha256)
        source_path = publication / "Candidate.lean"
        body_path = publication / "body.lean"
        manifest_path = publication / "manifest.json"
        if not source_path.is_file() or not body_path.is_file() or not manifest_path.is_file():
            _fail("checkpoint_tampered", f"publication is missing for {node.node_id}")
        source = source_path.read_text(encoding="utf-8")
        body = body_path.read_text(encoding="utf-8")
        if sha256_id(source) != node.cumulative_source_sha256:
            _fail("candidate_tampered", f"published source changed for {node.node_id}")
        if sha256_id(body) != node.body_sha256:
            _fail("candidate_tampered", f"published body changed for {node.node_id}")
        if _tagged_file_hash(manifest_path) != node.publication_manifest_sha256:
            _fail("checkpoint_tampered", f"publication manifest changed for {node.node_id}")
        return body

    def _checkpoint(
        self,
        *,
        accepted: tuple[AcceptedCapabilityNodeV1, ...],
        total_model_calls: int,
        per_node_calls: Mapping[str, int],
        ledger: tuple[Mapping[str, Any], ...],
    ) -> NPHardGapCheckpointV1:
        arguments = {
            "task_request_id": self.task.request_id,
            "dependency_snapshot": _current_dependency_snapshot(
                root=self.root, task=self.task, accepted=accepted
            ),
            "accepted_nodes": accepted,
            "remaining_gap_graph": tuple(
                node.to_dict() for node in self.task.gap_nodes[len(accepted) :]
            ),
            "total_model_calls": total_model_calls,
            "per_node_model_calls": tuple(sorted(per_node_calls.items())),
            "model_call_ledger": ledger,
        }
        provisional = NPHardGapCheckpointV1(
            checkpoint_hash="sha256:" + "0" * 64, **arguments
        )
        checkpoint = NPHardGapCheckpointV1(
            checkpoint_hash=provisional.computed_checkpoint_hash, **arguments
        )
        checkpoint.validate(self.task)
        return checkpoint

    def _write_checkpoint(self, checkpoint: NPHardGapCheckpointV1) -> tuple[Path, str]:
        path = self.output_root / "checkpoint.json"
        _write_json(path, checkpoint.to_dict(self.task))
        return path, _tagged_file_hash(path)

    def _load_checkpoint(
        self, *, checkpoint_path: Path, expected_file_sha256: str
    ) -> tuple[NPHardGapCheckpointV1, dict[str, str]]:
        checkpoint_path = checkpoint_path.resolve()
        if not checkpoint_path.is_file() or _tagged_file_hash(checkpoint_path) != expected_file_sha256:
            _fail("checkpoint_tampered", "checkpoint file bytes changed")
        try:
            value = json.loads(checkpoint_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            _fail("checkpoint_tampered", str(error))
        checkpoint = NPHardGapCheckpointV1.from_dict(value, task=self.task)
        current = _current_dependency_snapshot(
            root=self.root, task=self.task, accepted=checkpoint.accepted_nodes
        )
        if current != checkpoint.dependency_snapshot:
            _fail("candidate_dependency_stale", "checkpoint dependency snapshot changed")
        bodies: dict[str, str] = {}
        for accepted in checkpoint.accepted_nodes:
            bodies[accepted.declaration] = self._load_publication_body(accepted)
        return checkpoint, bodies

    @staticmethod
    def _call_record(
        response: ModelResponse,
        *,
        request: NPHardNodeRequestV1,
        prompt: str,
        attempt: int,
        prompt_file: Path,
        response_file: Path,
    ) -> dict[str, Any]:
        return {
            "request_id": request.request_id,
            "node_id": request.node.node_id,
            "attempt": attempt,
            "prompt_sha256": sha256_id(prompt),
            "prompt_file": str(prompt_file),
            "called": response.called,
            "ok": response.ok,
            "status_code": response.status_code,
            "duration_seconds": response.duration_seconds,
            "usage": response.usage,
            "provider_attempts": response.attempts,
            "finish_reason": response.finish_reason,
            "response_sha256": sha256_id(response.content),
            "response_file": str(response_file),
            "error": response.error,
        }

    def run(
        self,
        *,
        resume_checkpoint_path: Path | None = None,
        expected_checkpoint_file_sha256: str | None = None,
        max_new_nodes: int | None = None,
    ) -> NPHardGapRuntimeResultV1:
        if self.output_root.exists() and resume_checkpoint_path is None and any(
            self.output_root.iterdir()
        ):
            _fail("checkpoint_tampered", "new G-C output directory must be fresh")
        self.output_root.mkdir(parents=True, exist_ok=True)
        resumed = resume_checkpoint_path is not None
        if resumed:
            if expected_checkpoint_file_sha256 is None:
                _fail("checkpoint_tampered", "resume requires the expected checkpoint file hash")
            checkpoint, bodies = self._load_checkpoint(
                checkpoint_path=resume_checkpoint_path,
                expected_file_sha256=expected_checkpoint_file_sha256,
            )
            accepted = list(checkpoint.accepted_nodes)
            total_model_calls = checkpoint.total_model_calls
            per_node_calls = dict(checkpoint.per_node_model_calls)
            ledger = list(checkpoint.model_call_ledger)
        else:
            bodies = {}
            accepted = []
            total_model_calls = 0
            per_node_calls = {}
            ledger = []

        commands: list[CommandResult] = []
        worker_results: list[Mapping[str, Any]] = []
        fresh_rediscoveries = 0

        # A resume is not trusted until a fresh process reconstructs every
        # previously accepted cumulative publication.
        if resumed:
            for node in accepted:
                source_path = self._publication_root(node.cumulative_source_sha256) / "Candidate.lean"
                command = run_command(
                    ["lake", "env", "lean", str(source_path)],
                    cwd=self.root / "Lean",
                    timeout_seconds=self.timeout_seconds,
                )
                commands.append(command)
                if not command.ok:
                    _fail("fresh_core_resolve_failed", f"resume could not rediscover {node.node_id}")
                fresh_rediscoveries += 1

        service_parent = self.output_root / "worker-services"
        service_parent.mkdir(parents=True, exist_ok=True)
        service_index = 1
        while (service_parent / f"run-{service_index:03d}").exists():
            service_index += 1
        service_root = service_parent / f"run-{service_index:03d}"
        pool = StagePLeanWorkerPool(
            lean_root=self.root / "Lean",
            workspace_root=self.output_root,
            service_root=service_root,
            maximum_workers=1,
            timeout_seconds=self.timeout_seconds,
        )
        session_id = pool.start_session(
            owner=self.task.request_id, namespace=self.task.candidate_module
        )
        candidate_path = self.output_root / "work" / "Candidate.lean"
        candidate_path.parent.mkdir(parents=True, exist_ok=True)
        new_nodes = 0
        checkpoint_path: Path | None = resume_checkpoint_path
        checkpoint_file_hash: str | None = expected_checkpoint_file_sha256
        failure_code: str | None = None
        failure_message: str | None = None
        final_result: NPHardAuthoringResultV2 | None = None
        deletion_audits: list[Mapping[str, Any]] = []
        try:
            for ordinal in range(len(accepted) + 1, len(self.task.gap_nodes) + 1):
                if max_new_nodes is not None and new_nodes >= max_new_nodes:
                    break
                node = self.task.gap_nodes[ordinal - 1]
                dependency_snapshot = _current_dependency_snapshot(
                    root=self.root, task=self.task, accepted=tuple(accepted)
                )
                request = _node_request(
                    task=self.task,
                    node_ordinal=ordinal,
                    dependency_snapshot=dependency_snapshot,
                    accepted=tuple(accepted),
                    total_model_calls=total_model_calls,
                )
                diagnostic: str | None = None
                seen_bodies: set[str] = set()
                accepted_this_node = False
                for attempt in range(1, request.node_attempt_budget + 1):
                    if total_model_calls >= 8:
                        failure_code = "authoring_gap_budget_exhausted"
                        failure_message = "instance model-call budget exhausted"
                        break
                    accepted_bodies = {
                        declaration: body for declaration, body in bodies.items()
                    }
                    prompt = build_np_hard_node_prompt_v1(
                        root=self.root,
                        task=self.task,
                        request=request,
                        accepted_bodies=accepted_bodies,
                        diagnostic=diagnostic,
                    )
                    response = self.model.complete_json(
                        system=NP_HARD_NODE_SYSTEM_PROMPT, prompt=prompt
                    )
                    model_root = self.output_root / "model-calls"
                    prompt_path = model_root / f"{node.node_id}-attempt-{attempt:02d}-prompt.json"
                    response_path = model_root / f"{node.node_id}-attempt-{attempt:02d}-response.json"
                    prompt_path.parent.mkdir(parents=True, exist_ok=True)
                    prompt_path.write_text(prompt, encoding="utf-8")
                    _write_json(
                        response_path,
                        {
                            "called": response.called,
                            "ok": response.ok,
                            "status_code": response.status_code,
                            "duration_seconds": response.duration_seconds,
                            "usage": response.usage,
                            "attempts": response.attempts,
                            "finish_reason": response.finish_reason,
                            "content": response.content,
                            "error": response.error,
                        },
                    )
                    if not response.called:
                        failure_code = "model_provider_unavailable"
                        failure_message = response.error or "model provider did not execute"
                        break
                    total_model_calls += 1
                    per_node_calls[node.node_id] = per_node_calls.get(node.node_id, 0) + 1
                    ledger.append(
                        self._call_record(
                            response,
                            request=request,
                            prompt=prompt,
                            attempt=attempt,
                            prompt_file=prompt_path,
                            response_file=response_path,
                        )
                    )
                    if not response.ok:
                        failure_code = "model_provider_unavailable"
                        failure_message = response.error or "model request failed"
                        break
                    try:
                        patch = parse_np_hard_node_patch_v1(
                            content=response.content, request=request, task=self.task
                        )
                    except NPHardGapRuntimeError as error:
                        failure_code = error.code
                        failure_message = error.message
                        if error.code == "invalid_np_hard_gap_runtime_schema":
                            diagnostic = (
                                "Response envelope was invalid. Return the exact response_template "
                                f"with every frozen field unchanged: {error.message}"
                            )
                            continue
                        break
                    body_hash = sha256_id(patch.replacement_body)
                    if body_hash in seen_bodies:
                        failure_code = "authoring_gap_budget_exhausted"
                        failure_message = "model repeated the same rejected candidate"
                        diagnostic = (
                            "The replacement body exactly repeated a rejected candidate. "
                            "Return a materially different body that addresses the last Lean diagnostic."
                        )
                        continue
                    seen_bodies.add(body_hash)
                    current_bodies = {**bodies, node.declaration: patch.replacement_body}
                    source = _candidate_source(
                        task=self.task,
                        bodies=current_bodies,
                        include_final=False,
                        final_program_declaration=self.final_program_declaration,
                    )
                    candidate_path.write_text(source, encoding="utf-8")
                    dependencies = tuple(
                        dict.fromkeys(
                            [
                                *(digest for _, digest in dependency_snapshot),
                                body_hash,
                            ]
                        )
                    )
                    key = StagePLeanWorkerKey(
                        toolchain=(self.root / "Lean" / "lean-toolchain").read_text(
                            encoding="utf-8"
                        ).strip(),
                        lake_manifest_sha256=_tagged_file_hash(
                            self.root / "Lean" / "lake-manifest.json"
                        ),
                        base_registry_fingerprint=self.task.dependency_fingerprint,
                        complete_source_sha256=sha256_id(source),
                        dependency_sha256=dependencies,
                        namespace=self.task.candidate_module,
                        session_id=session_id,
                        editable_allowlist=(node.declaration,),
                    )
                    try:
                        worker = pool.validate(
                            session_id=session_id,
                            owner=self.task.request_id,
                            key=key,
                            source_path=candidate_path,
                            dependency_sha256=dependencies,
                            use_cache=False,
                            allow_cold_fallback=False,
                        )
                    except StagePContractError as error:
                        failure_code = "lean_infrastructure_error"
                        failure_message = f"{error.code}: {error.message}"
                        break
                    worker_results.append(worker.to_dict())
                    if not worker.verified:
                        diagnostic = "\n".join(
                            str(item.get("message", "Lean rejected candidate"))
                            for item in worker.diagnostics
                        )[:8_000]
                        failure_code = (
                            "semantic_proof_failed"
                            if node.capability in {"semantic_proof", "mapping_invariant"}
                            else "program_synthesis_failed"
                        )
                        failure_message = diagnostic
                        continue

                    source_hash = sha256_id(source)
                    publication = self._publication_root(source_hash)
                    publication.mkdir(parents=True, exist_ok=False)
                    published_source = publication / "Candidate.lean"
                    body_path = publication / "body.lean"
                    manifest_path = publication / "manifest.json"
                    published_source.write_text(source, encoding="utf-8")
                    body_path.write_text(patch.replacement_body, encoding="utf-8")
                    fresh_path = publication / "FreshCore.lean"
                    fresh_path.write_text(
                        source + f"\n#check {node.declaration}\n", encoding="utf-8"
                    )
                    fresh = run_command(
                        ["lake", "env", "lean", str(fresh_path)],
                        cwd=self.root / "Lean",
                        timeout_seconds=self.timeout_seconds,
                    )
                    commands.append(fresh)
                    if not fresh.ok:
                        failure_code = "fresh_core_resolve_failed"
                        failure_message = f"fresh Core did not rediscover {node.node_id}"
                        break
                    fresh_rediscoveries += 1
                    manifest = {
                        "schema_version": NP_HARD_GAP_PUBLICATION_SCHEMA_V1,
                        "task_request_id": self.task.request_id,
                        "node_request_id": request.request_id,
                        "node_id": node.node_id,
                        "declaration": node.declaration,
                        "body_sha256": body_hash,
                        "cumulative_source_sha256": source_hash,
                        "worker_evidence_sha256": sha256_id(worker.to_dict()),
                        "fresh_core_evidence_sha256": sha256_id(fresh.to_dict()),
                        "dependency_snapshot": dict(dependency_snapshot),
                        "compiler_inserted_math_token_count": 0,
                    }
                    _write_json(manifest_path, manifest)
                    record = AcceptedCapabilityNodeV1(
                        node_id=node.node_id,
                        declaration=node.declaration,
                        body_sha256=body_hash,
                        cumulative_source_sha256=source_hash,
                        publication_manifest_sha256=_tagged_file_hash(manifest_path),
                        worker_evidence_sha256=sha256_id(worker.to_dict()),
                        fresh_core_evidence_sha256=sha256_id(fresh.to_dict()),
                    )
                    accepted.append(record)
                    bodies[node.declaration] = patch.replacement_body
                    checkpoint = self._checkpoint(
                        accepted=tuple(accepted),
                        total_model_calls=total_model_calls,
                        per_node_calls=per_node_calls,
                        ledger=tuple(ledger),
                    )
                    checkpoint_path, checkpoint_file_hash = self._write_checkpoint(checkpoint)
                    accepted_this_node = True
                    failure_code = None
                    failure_message = None
                    new_nodes += 1
                    break
                if not accepted_this_node:
                    break

            all_accepted = len(accepted) == len(self.task.gap_nodes)
            paused = not all_accepted and failure_code is None
            if all_accepted:
                final_source = _candidate_source(
                    task=self.task,
                    bodies=bodies,
                    include_final=True,
                    final_program_declaration=self.final_program_declaration,
                )
                final_path = self.output_root / "Final.lean"
                replay_path = self.output_root / "Replay.lean"
                final_path.write_text(final_source, encoding="utf-8")
                replay_path.write_text(final_source, encoding="utf-8")
                final_command = run_command(
                    ["lake", "env", "lean", str(final_path)],
                    cwd=self.root / "Lean",
                    timeout_seconds=self.timeout_seconds,
                )
                replay_command = run_command(
                    ["lake", "env", "lean", str(replay_path)],
                    cwd=self.root / "Lean",
                    timeout_seconds=self.timeout_seconds,
                )
                commands.extend((final_command, replay_command))
                if not final_command.ok:
                    failure_code = "final_lean_failed"
                    failure_message = "exact NativeTMNPHard finalization failed"
                elif not replay_command.ok:
                    failure_code = "independent_replay_failed"
                    failure_message = "independent NativeTMNPHard replay failed"
                else:
                    audit_root = self.output_root / "deletion-audits"
                    audit_root.mkdir(parents=True, exist_ok=True)
                    for deleted in self.task.gap_nodes:
                        audit_bodies = {
                            declaration: body
                            for declaration, body in bodies.items()
                            if declaration != deleted.declaration
                        }
                        audit_source = _candidate_source(
                            task=self.task,
                            bodies=audit_bodies,
                            include_final=True,
                            final_program_declaration=self.final_program_declaration,
                        )
                        audit_path = audit_root / f"without-{deleted.node_id}.lean"
                        audit_path.write_text(audit_source, encoding="utf-8")
                        audit_command = run_command(
                            ["lake", "env", "lean", str(audit_path)],
                            cwd=self.root / "Lean",
                            timeout_seconds=self.timeout_seconds,
                        )
                        deletion_audits.append(
                            {
                                "node_id": deleted.node_id,
                                "declaration": deleted.declaration,
                                "body_sha256": dict(
                                    (node.node_id, node.body_sha256) for node in accepted
                                )[deleted.node_id],
                                "audit_file": str(audit_path),
                                "audit_file_sha256": _tagged_file_hash(audit_path),
                                "command": audit_command.to_dict(),
                                "passed": not audit_command.ok,
                            }
                        )
                    if not all(item["passed"] for item in deletion_audits):
                        failure_code = "deletion_audit_failed"
                        failure_message = (
                            "a final artifact remained valid after deleting a model-generated node"
                        )
                    else:
                        final_result = accepted_np_hard_authoring_result_v2(
                            task=self.task,
                            candidate_hashes={
                                node.node_id: node.body_sha256 for node in accepted
                            },
                            final_certificate=sha256_id(final_command.to_dict()),
                            replay_certificate=sha256_id(replay_command.to_dict()),
                            lean_diagnostics=(
                                "every node accepted by the persistent worker and fresh Core",
                                "exact NativeTMNPHard target finalized and replayed",
                            ),
                            policy_diagnostics=(
                                "source-to-target direction and exact endpoints remained frozen",
                                "every generated capability node is required by deletion audit",
                            ),
                            model_calls=tuple(ledger),
                        )
            status = (
                "VERIFIED"
                if final_result is not None
                else "CHECKPOINTED"
                if paused
                else "FAILED"
            )
            return NPHardGapRuntimeResultV1(
                status=status,
                task_request_id=self.task.request_id,
                accepted_nodes=tuple(node.node_id for node in accepted),
                fresh_core_rediscoveries=fresh_rediscoveries,
                model_calls=total_model_calls,
                checkpoint_path=str(checkpoint_path) if checkpoint_path else None,
                checkpoint_file_sha256=checkpoint_file_hash,
                result=final_result,
                failure_code=failure_code,
                failure_message=failure_message,
                commands=tuple(commands),
                worker_results=tuple(worker_results),
                resumed=resumed,
                model_call_ledger=tuple(ledger),
                deletion_audits=tuple(deletion_audits),
            )
        finally:
            try:
                pool.close_session(session_id=session_id, owner=self.task.request_id)
            finally:
                pool.close()
