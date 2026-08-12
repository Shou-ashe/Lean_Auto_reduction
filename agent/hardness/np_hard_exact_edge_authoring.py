"""Multi-stage exact-edge construction authoring for direct-new-edge cases.

For ``direct_new_edge`` public policy cases the exact-edge lane must not reuse
the generic ``HardnessAgent`` reduce-to retrieval path.  Instead the runner
freezes a typed exact-edge construction DAG from public endpoint data and
construction policy, then calls the model once per node (serial within the
case), compiles and audits each single-node body, and checkpoints only fully
accepted prefixes.

Prompt discipline (ACTIVE_AGENT_IMPROVEMENT_PLAN.md 3.4):

- prompts contain only the answer-free statement, exact endpoint
  declarations, the current node signature, the construction policy, the
  public API allowlist, accepted dependency signatures, the previous minimal
  Lean/policy diagnostics, and the remaining budget;
- no ``recommended_first_body``, no pre-filled replacement body, no solution,
  hint, PDF proof, conversion plan, hidden oracle, gold route, or other case
  answer material is ever placed in a prompt or an output artifact;
- every model call records request/case/node/attempt identity, HTTP status,
  token usage, prompt hash, response hash, workspace hash and final status.

The final artifact is the exact ``CertifiedReduction source target`` produced
from the LLM-written program and the semantic iff over that program's run.
"""

from __future__ import annotations

import hashlib
import json
import re
import threading
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

from .lean_runner import run_command, sha256_file
from .models import CommandResult, sha256_id
from .np_hard_authoring import (
    NPHardAuthoringObligationV2,
    NPHardAuthoringTaskV2,
    build_np_hard_authoring_task_v2,
)
from .np_hard_authoring_planner import exact_edge_construction_gap_nodes


EXACT_EDGE_STAGED_RESULT_SCHEMA_V1 = "hardness_exact_edge_staged_result_v1"
EXACT_EDGE_NODE_PROMPT_SCHEMA_V1 = "hardness_exact_edge_node_prompt_v1"
EXACT_EDGE_NODE_PATCH_SCHEMA_V1 = "hardness_exact_edge_node_patch_v1"
EXACT_EDGE_NODE_CHECKPOINT_SCHEMA_V1 = "hardness_exact_edge_node_checkpoint_v1"
EXACT_EDGE_AUTHORING_TASK_CLASS = "typed_exact_edge_construction_dag"
EXACT_EDGE_MAX_NODE_ATTEMPTS = 4
EXACT_EDGE_RUNTIME_MODULE = (
    "ComplexityReduction.Agent.Hardness.ExactEdgeRuntime"
)
_GENERIC_EXACT_EDGE_PUBLIC_SOURCES = (
    "Lean/Reference/ComplexityReduction/Legacy/ComplexityReduction/Bridges/TMPolyTime.lean",
    "Lean/Reference/ComplexityReduction/Legacy/ComplexityReduction/Bridges/CostedToTM/Maps/Part1.lean",
    "Lean/Reference/ComplexityReduction/Program/Primitive.lean",
    "Lean/Reference/ComplexityReduction/Program/Syntax.lean",
    "Lean/Reference/ComplexityReduction/Certificate/Reduction.lean",
    "Lean/Reference/ComplexityReduction/Presentation/GraphTM.lean",
)

_HASH_RE = re.compile(r"sha256:[0-9a-f]{64}\Z")
_FORBIDDEN_ROUTE_IMPORT_PREFIXES = (
    "ComplexityReduction.Routes.",
    "ComplexityReduction.Agent.Hardness.GeneratedArtifact",
)
_FORBIDDEN_PROMPT_TEXT = (
    '"recommended_first_body":',
    '"solution":',
    '"hint":',
    '"gold":',
    '"oracle":',
    "problems.7z",
    "problems_clean.json",
    "transform_plan",
)
_EXACT_EDGE_SYSTEM_PROMPT = """\
You are an untrusted Lean 4 reduction author for one exact node of a
certified-reduction construction.  Return exactly one JSON object matching
the response template, with only the `replacement_body` Lean term body that
fills the single active declaration after `:=`, and no markdown.  The runner
has frozen the endpoints, direction, construction policy, node signature, and
public API allowlist; you may not change them and you may not import routes,
solutions, or benchmark material.  On a repair turn, never repeat the last
rejected body.  Do not emit imports, namespaces, declarations, commands,
markdown, sorry, admit, axioms, unsafe code, filesystem operations, or any
reduction in the opposite direction.  The Lean compiler and the runner's
independent audits decide acceptance; your response has no proof authority.
Keep the JSON and Lean body concise and within the prompt's output-token budget.
For a polynomial-bound node, immediately compose the named public
`TMPolyTimeMap` and route-free structural witnesses; do not unfold Turing
machines, encoders, or implementation proofs unless a Lean diagnostic requires
it.  Spend the response budget on the JSON body, not exploratory prose.
"""

_PUBLIC_SOURCE_INDEX_LOCK = threading.Lock()
_PUBLIC_SOURCE_INDEX: dict[str, tuple[tuple[Path, tuple[str, ...]], ...]] = {}


class ExactEdgeAuthoringError(ValueError):
    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


def _fail(code: str, message: str) -> None:
    raise ExactEdgeAuthoringError(code, message)


def _tagged_file_hash(path: Path) -> str:
    return "sha256:" + sha256_file(path)


def _write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def _hash_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


@dataclass(frozen=True)
class ExactEdgeNodeAttempt:
    """One immutable record of one model call for one DAG node."""

    call: int
    node: str
    attempt: int
    model: str | None
    called: bool
    ok: bool
    protocol_accepted: bool
    status_code: int | None
    http_attempts: int | None
    finish_reason: str | None
    duration_seconds: float | None
    usage: Mapping[str, int] | None
    prompt_sha256: str
    response_sha256: str
    patch_sha256: str | None
    diagnostics_sha256: str | None
    prompt_file: str
    response_file: str
    patch_file: str | None
    workspace_sha256: str | None
    request_id: str | None = None
    case_id: str | None = None
    task_id: str | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "call": self.call,
            "request_id": self.request_id,
            "case_id": self.case_id,
            "node_id": self.node,
            "attempt": self.attempt,
            "stage": self.node,
            "editable_file": None,
            "task_id": self.task_id,
            "model": self.model,
            "called": self.called,
            "ok": self.ok,
            "protocol_accepted": self.protocol_accepted,
            "status_code": self.status_code,
            "http_attempts": self.http_attempts,
            "finish_reason": self.finish_reason,
            "duration_seconds": self.duration_seconds,
            "usage": dict(self.usage) if self.usage is not None else None,
            "prompt_sha256": self.prompt_sha256,
            "response_sha256": self.response_sha256,
            "patch_sha256": self.patch_sha256,
            "diagnostics_sha256": self.diagnostics_sha256,
            "prompt_file": self.prompt_file,
            "response_file": self.response_file,
            "patch_file": self.patch_file,
            "workspace_sha256": self.workspace_sha256,
        }


def _assert_answer_free_prompt(value: Mapping[str, Any]) -> None:
    serialized = json.dumps(value, ensure_ascii=False, sort_keys=True).lower()
    marker = next(
        (token for token in _FORBIDDEN_PROMPT_TEXT if token in serialized), None
    )
    if marker is not None:
        _fail("oracle_or_gold_import", f"exact-edge prompt contains forbidden text: {marker}")


def _node_by_id(task: NPHardAuthoringTaskV2, node_id: str) -> NPHardAuthoringObligationV2:
    matched = [node for node in task.gap_nodes if node.node_id == node_id]
    if len(matched) != 1:
        _fail("candidate_dependency_stale", f"exact-edge DAG lacks node {node_id!r}")
    return matched[0]


def build_typed_exact_edge_task(
    *,
    root: Path,
    input_module: str,
    source_declaration: str,
    target_declaration: str,
    policy: Mapping[str, Any],
    public_source_files: tuple[str, ...],
    attempt_budget: int = EXACT_EDGE_MAX_NODE_ATTEMPTS,
    timeout_seconds: int = 600,
    max_output_tokens: int = 4_000,
) -> NPHardAuthoringTaskV2:
    """Build the frozen typed exact-edge task from public case data only."""

    mode = policy.get("mode")
    if mode != "direct_new_edge":
        _fail(
            "exact_edge_policy_mismatch",
            "typed exact-edge construction is restricted to direct-new-edge policy",
        )
    gap_nodes = exact_edge_construction_gap_nodes()
    target_module = target_declaration.rsplit(".", 1)[0]
    task = build_np_hard_authoring_task_v2(
        root=root,
        input_module=target_module,
        input_problem_declaration=target_declaration,
        hub_module=source_declaration.rsplit(".", 1)[0],
        hub_declaration=source_declaration,
        task_class=EXACT_EDGE_AUTHORING_TASK_CLASS,
        gap_nodes=gap_nodes,
        public_source_files=tuple(
            dict.fromkeys((*public_source_files, *_GENERIC_EXACT_EDGE_PUBLIC_SOURCES))
        ),
        allowed_primitives=(),
        program_reference=None,
        mapping_invariant=None,
        attempt_budget=attempt_budget,
        timeout_seconds=timeout_seconds,
        max_output_tokens=max_output_tokens,
        runtime_module=EXACT_EDGE_RUNTIME_MODULE,
        additional_allowed_imports=(
            (input_module,) if input_module != target_module else ()
        ),
    )
    task.validate()
    return task


def _exact_edge_package_structure(*, task: NPHardAuthoringTaskV2) -> str:
    source = task.source_problem.term
    target = task.target_problem.term
    return (
        f"structure CertifiedReductionPackage where\n"
        f"  normalization : {source}.Instance → {source}.Instance\n"
        f"  primitive : {source}.Instance → {target}.Instance\n"
        f"  gadget : {source}.Instance → {target}.Instance\n"
        f"  wellformed : (input : {source}.Instance) →\n"
        f"    {target}.accepts (gadget input) → {target}.accepts (primitive input)\n"
        f"  polyBound : ComplexityReduction.TMPolyTimeMap\n"
        f"    {source}.representation.encodedType\n"
        f"    {target}.representation.encodedType primitive\n"
        f"  program : ComplexityReduction.Program.PolyProg\n"
        f"    {source}.representation {target}.representation\n"
        f"  coherence : (input : {source}.Instance) →\n"
        f"    program.run input = primitive input\n"
        f"  forward : (input : {source}.Instance) →\n"
        f"    {source}.accepts input → {target}.accepts (program.run input)\n"
        f"  reverse : (input : {source}.Instance) →\n"
        f"    {target}.accepts (program.run input) → {source}.accepts input\n"
        f"  iff : (input : {source}.Instance) →\n"
        f"    {source}.accepts input ↔ {target}.accepts (program.run input)\n"
    )


def exact_edge_candidate_source(
    *,
    task: NPHardAuthoringTaskV2,
    bodies: Mapping[str, str],
    include_final: bool,
    deletion_audit_deleted_declaration: str | None = None,
) -> str:
    """Render accepted node bodies plus the exact certified-reduction artifact.

    The runner generates the public package structure and the final exact
    ``CertifiedReduction source target`` wrapper; the LLM writes only the
    per-node bodies.  The package record literal binds every node, so the
    deletion audit can prove that each generated node is required.
    """

    if deletion_audit_deleted_declaration is not None and all(
        node.declaration != deletion_audit_deleted_declaration
        for node in task.gap_nodes
    ):
        _fail(
            "candidate_dependency_stale",
            "deletion audit selected a declaration outside the exact-edge DAG",
        )
    imports = "\n".join(f"import {name}" for name in task.allowed_imports)
    declarations: list[str] = []
    asserted: list[str] = []
    for node in task.gap_nodes:
        if node.declaration == deletion_audit_deleted_declaration:
            continue
        if node.declaration not in bodies:
            break
        short_name = node.declaration.removeprefix(task.candidate_module + ".")
        declarations.append(
            f"noncomputable def {short_name} :\n    {node.exact_type} :=\n"
            + "\n".join(f"  {line}" for line in bodies[node.declaration].rstrip().splitlines())
            + "\n"
        )
        asserted.append(node.declaration)
    if include_final and len(declarations) != len(task.gap_nodes) and (
        deletion_audit_deleted_declaration is None
    ):
        _fail("candidate_dependency_stale", "final artifact requires every accepted body")
    if include_final:
        source = task.source_problem.term
        target = task.target_problem.term
        declarations.append(
            f"noncomputable def {task.final_candidate_declaration.removeprefix(task.candidate_module + '.')} :\n"
            f"    ComplexityReduction.Certificate.CertifiedReduction\n"
            f"      {source}\n"
            f"      {target} :=\n"
            f"  ⟨certifiedReduction.program, certifiedReduction.iff⟩\n"
        )
        asserted.append(task.final_candidate_declaration)
    axiom_audit = ",\n  ".join(asserted)
    return f"""{imports}

namespace {task.candidate_module}

open ComplexityReduction
open ComplexityReduction.Certificate
open ComplexityReduction.Encoding
open ComplexityReduction.Program
open ComplexityReduction.Combinatorics.Graph
open ComplexityReduction.Presentation
open {task.source_problem.module}
open {task.target_problem.module}

{_exact_edge_package_structure(task=task)}
{chr(10).join(declarations)}
end {task.candidate_module}

assert_standard_axioms
  {axiom_audit}
"""


def build_exact_edge_node_prompt(
    *,
    task: NPHardAuthoringTaskV2,
    node: NPHardAuthoringObligationV2,
    accepted_bodies: Mapping[str, str],
    policy: Mapping[str, Any],
    statement: str,
    statement_hash: str,
    diagnostic: str | None,
    attempt: int,
    remaining_attempts: int,
    timeout_seconds: int,
    public_endpoint_interfaces: Sequence[Mapping[str, Any]] = (),
    public_complexity_interfaces: Sequence[Mapping[str, Any]] = (),
) -> str:
    """Build the minimal answer-free prompt for exactly one active node."""

    accepted_signatures = tuple(
        (accepted.declaration, accepted.exact_type)
        for accepted in task.gap_nodes
        if accepted.declaration in accepted_bodies
    )
    transitive_dependency_ids: set[str] = set()
    pending_dependency_ids = list(node.depends_on)
    while pending_dependency_ids:
        dependency_id = pending_dependency_ids.pop()
        if dependency_id in transitive_dependency_ids:
            continue
        transitive_dependency_ids.add(dependency_id)
        pending_dependency_ids.extend(_node_by_id(task, dependency_id).depends_on)
    capability = node.capability
    if capability in {"reduction_primitive", "polynomial_bound"}:
        relevant_prefixes = (
            "ComplexityReduction.TMPolyTimeMap",
            "ComplexityReduction.Presentation.GraphTM",
        )
    elif capability in {
        "poly_program",
        "program_direct_tm_coherence",
        "certified_reduction",
    }:
        relevant_prefixes = (
            "ComplexityReduction.Program.",
            "ComplexityReduction.Certificate.CertifiedReduction",
            "ComplexityReduction.TMPolyTimeMap",
        )
    else:
        relevant_prefixes = ()
    relevant_complexity_interfaces = [
        {
            **dict(interface),
            "answer_free_public_signatures": [
                dict(signature)
                for signature in interface.get("answer_free_public_signatures", ())
                if isinstance(signature, Mapping)
                and isinstance(signature.get("declaration"), str)
                and str(signature["declaration"]).startswith(relevant_prefixes)
            ],
        }
        for interface in public_complexity_interfaces
    ]
    relevant_complexity_interfaces = [
        interface
        for interface in relevant_complexity_interfaces
        if interface["answer_free_public_signatures"]
    ]
    semantic_capability = capability in {
        "semantic_forward",
        "semantic_reverse",
        "semantic_iff",
        "certified_reduction",
    }
    relevant_endpoint_interfaces = []
    for interface in public_endpoint_interfaces:
        exposed = dict(interface)
        if not semantic_capability:
            exposed.pop("semantic_interfaces", None)
        relevant_endpoint_interfaces.append(exposed)
    payload = {
        "schema_version": EXACT_EDGE_NODE_PROMPT_SCHEMA_V1,
        "objective": "construct_certified_reduction",
        "task_class": EXACT_EDGE_AUTHORING_TASK_CLASS,
        "case": {
            "source": task.source_problem.term,
            "target": task.target_problem.term,
            "statement": statement,
            "statement_hash": statement_hash,
            "construction_policy": policy,
        },
        "node": node.to_dict(),
        "accepted_dependency_signatures": [
            {"declaration": declaration, "exact_type": exact_type}
            for declaration, exact_type in accepted_signatures
        ],
        "public_api_allowlist": list(task.allowed_imports),
        "public_endpoint_interfaces": relevant_endpoint_interfaces,
        "public_complexity_interfaces": [
            dict(item) for item in relevant_complexity_interfaces
        ],
        "accepted_dependency_bodies": [
            {
                "declaration": dependency.declaration,
                "exact_type": dependency.exact_type,
                "body": accepted_bodies[dependency.declaration],
            }
            for dependency in task.gap_nodes
            if dependency.node_id in transitive_dependency_ids
            and dependency.declaration in accepted_bodies
        ],
        "lean_diagnostic": diagnostic,
        "budget": {
            "attempt": attempt,
            "remaining_attempts": remaining_attempts,
            "lean_timeout_seconds": timeout_seconds,
            "max_output_tokens": task.max_output_tokens,
        },
        "policy": {
            "only_active_declaration_is_editable": True,
            "route_import_forbidden": True,
            "composition_forbidden": not bool(policy.get("allow_composition")),
            "require_new_primitive": bool(policy.get("require_new_primitive")),
            "no_answer_material_in_prompt": True,
            "prefer_named_public_capabilities_over_unfolding": True,
            "return_json_before_token_limit": True,
        },
        "response_template": {
            "schema_version": EXACT_EDGE_NODE_PATCH_SCHEMA_V1,
            "action": "submit_node_patch",
            "request_id": task.request_id,
            "node_id": node.node_id,
            "declaration": node.declaration,
            "dependency_fingerprint": task.dependency_fingerprint,
            "replacement_body": "Lean term body only",
        },
    }
    _assert_answer_free_prompt(payload)
    return json.dumps(payload, ensure_ascii=True, indent=2, sort_keys=True)


def _public_complexity_interfaces(
    *, workspace_root: Path, task: NPHardAuthoringTaskV2
) -> tuple[dict[str, Any], ...]:
    """Return source-bound, route-free signatures for the generic authoring API."""

    specifications = (
        (
            _GENERIC_EXACT_EDGE_PUBLIC_SOURCES[0],
            (
                ("TMPolyTimeMap", "ComplexityReduction.TMPolyTimeMap"),
                ("id", "ComplexityReduction.TMPolyTimeMap.id"),
            ),
        ),
        (
            _GENERIC_EXACT_EDGE_PUBLIC_SOURCES[1],
            tuple(
                (name, f"ComplexityReduction.TMPolyTimeMap.{name}")
                for name in (
                    "of_encodingEquiv",
                    "const",
                    "comp",
                    "fst",
                    "snd",
                    "prod_mk",
                    "list_append",
                    "list_singleton",
                    "list_map",
                )
            ),
        ),
        (
            _GENERIC_EXACT_EDGE_PUBLIC_SOURCES[2],
            (
                ("Primitive", "ComplexityReduction.Program.Primitive"),
                (
                    "ofTMPolyTime",
                    "ComplexityReduction.Program.Primitive.ofTMPolyTime",
                ),
            ),
        ),
        (
            _GENERIC_EXACT_EDGE_PUBLIC_SOURCES[3],
            (("PolyProg", "ComplexityReduction.Program.PolyProg"),),
        ),
        (
            _GENERIC_EXACT_EDGE_PUBLIC_SOURCES[4],
            (
                (
                    "CertifiedReduction",
                    "ComplexityReduction.Certificate.CertifiedReduction",
                ),
            ),
        ),
        (
            _GENERIC_EXACT_EDGE_PUBLIC_SOURCES[5],
            tuple(
                (name, f"ComplexityReduction.Presentation.GraphTM.{name}")
                for name in (
                    "toTuple",
                    "ofTuple",
                    "vertices",
                    "edges",
                    "directed",
                    "edgeSwap",
                    "appendMapEdges",
                    "mk",
                )
            ),
        ),
    )
    allowed_files = set(task.public_source_files)
    interfaces: list[dict[str, Any]] = []

    def signature(lines: Sequence[str], short_name: str) -> str:
        declaration = re.compile(
            rf"^(?:noncomputable\s+)?(?:def|theorem|structure|inductive)\s+"
            rf"{re.escape(short_name)}\b"
        )
        matches = [index for index, line in enumerate(lines) if declaration.match(line.strip())]
        if len(matches) != 1:
            _fail(
                "candidate_dependency_stale",
                f"public complexity declaration {short_name!r} is not unique",
            )
        start = matches[0]
        first = lines[start].strip()
        structural = first.startswith(("structure ", "inductive "))
        captured: list[str] = []
        for line in lines[start : start + 90]:
            stripped = line.rstrip()
            if captured and structural and re.match(
                r"^(?:namespace|end)\b", stripped.strip()
            ):
                break
            captured.append(stripped)
            if not structural and ":=" in stripped:
                prefix = "\n".join(captured).split(":=", 1)[0].rstrip()
                return prefix + " := <implementation omitted>"
        rendered = "\n".join(captured).strip()
        if not rendered or len(rendered) > 12_000:
            _fail(
                "candidate_dependency_stale",
                f"public complexity signature {short_name!r} is not bounded",
            )
        return rendered

    for relative, declarations in specifications:
        if relative not in allowed_files:
            _fail(
                "candidate_dependency_stale",
                f"public complexity API is outside the dependency set: {relative}",
            )
        path = (workspace_root / relative).resolve()
        try:
            path.relative_to(workspace_root.resolve())
            lines = path.read_text(encoding="utf-8").splitlines()
        except (ValueError, OSError, UnicodeError) as error:
            _fail("candidate_dependency_stale", f"complexity API is unreadable: {error}")
        interfaces.append(
            {
                "source_file": relative,
                "source_sha256": _tagged_file_hash(path),
                "answer_free_public_signatures": [
                    {
                        "declaration": qualified,
                        "signature": signature(lines, short_name),
                    }
                    for short_name, qualified in declarations
                ],
            }
        )
    return tuple(interfaces)


def _public_endpoint_interfaces(
    *, workspace_root: Path, task: NPHardAuthoringTaskV2
) -> tuple[dict[str, Any], ...]:
    """Expose bounded source excerpts around the two public endpoint declarations."""

    allowed_files = set(task.public_source_files)
    interfaces: list[dict[str, Any]] = []

    index_key = str(workspace_root.resolve())
    with _PUBLIC_SOURCE_INDEX_LOCK:
        public_index = _PUBLIC_SOURCE_INDEX.get(index_key)
        if public_index is None:
            public_index = tuple(
                (path, tuple(path.read_text(encoding="utf-8").splitlines()))
                for path in sorted(
                    (workspace_root / "Lean/Reference/ComplexityReduction").rglob("*.lean")
                )
                if path.is_file()
            )
            _PUBLIC_SOURCE_INDEX[index_key] = public_index

    def namespace_at(lines: Sequence[str], stop: int) -> tuple[str, ...]:
        stack: list[str] = []
        for line in lines[:stop]:
            stripped = line.strip()
            matched = re.fullmatch(r"namespace\s+([A-Za-z0-9_.']+)", stripped)
            if matched:
                stack.extend(matched.group(1).split("."))
            elif re.fullmatch(r"end(?:\s+[A-Za-z0-9_.']+)?", stripped) and stack:
                stack.pop()
        return tuple(stack)

    def declaration_block(
        kind: str, short_name: str
    ) -> tuple[str, str, str] | None:
        matched: list[tuple[Path, tuple[str, ...], int]] = []
        pattern = re.compile(rf"\b{kind}\s+{re.escape(short_name)}\b")
        for source_path, source_lines in public_index:
            for ordinal, source_line in enumerate(source_lines):
                if pattern.search(source_line):
                    matched.append((source_path, source_lines, ordinal))
        if len(matched) != 1:
            return None
        source_path, source_lines, ordinal = matched[0]
        namespace = namespace_at(source_lines, ordinal)
        qualified = ".".join((*namespace, short_name))
        # Endpoint semantics are needed verbatim, but an arbitrary line window also
        # leaks many unrelated declarations into the prompt and can dominate the
        # model's output budget.  Lean's public declarations here are top-level, so
        # stop at the next top-level declaration/doc block while retaining every
        # indented continuation line of the selected declaration.
        stop = min(len(source_lines), ordinal + 90)
        next_top_level = re.compile(
            r"^(?:/--|/-!|namespace\b|end\b|"
            r"(?:@\[[^]]+\]\s*)?(?:noncomputable\s+)?"
            r"(?:abbrev|class|def|inductive|instance|lemma|structure|theorem)\b)"
        )
        for candidate in range(ordinal + 1, stop):
            line = source_lines[candidate]
            if line and not line[0].isspace() and next_top_level.match(line):
                stop = candidate
                break
        block = "\n".join(source_lines[ordinal:stop]).rstrip()
        return qualified, str(source_path.relative_to(workspace_root)), block

    def carrier_interfaces(excerpt: str) -> list[dict[str, str]]:
        carrier_names = set(re.findall(r"carrier_eq_([A-Za-z0-9_]+)", excerpt))
        encoded_names = set(
            name.rsplit(".", 1)[-1]
            for name in re.findall(
                r"encodedType\s*:=\s*([A-Za-z0-9_.]+)", excerpt
            )
        )
        for encoded_name in encoded_names:
            encoded = declaration_block("def", encoded_name)
            if encoded is None:
                continue
            carrier_names.update(
                name.rsplit(".", 1)[-1]
                for name in re.findall(r"Carrier\s*:=\s*([A-Za-z0-9_.]+)", encoded[2])
            )
        pending = list(sorted(carrier_names))
        seen: set[str] = set()
        result: list[dict[str, str]] = []
        while pending and len(result) < 8:
            carrier_name = pending.pop(0)
            if carrier_name in seen:
                continue
            seen.add(carrier_name)
            structure = declaration_block("structure", carrier_name)
            if structure is None:
                continue
            qualified, source_file, block = structure
            result.append(
                {
                    "declaration": qualified,
                    "source_file": source_file,
                    "answer_free_public_structure": block,
                }
            )
            pending.extend(
                name
                for name in re.findall(r"\b([A-Z][A-Za-z0-9_]*Input)\b", block)
                if name not in seen
            )
        return result

    def semantic_interfaces(excerpt: str) -> list[dict[str, str]]:
        pending = [
            name.rsplit(".", 1)[-1]
            for name in re.findall(
                r"\bisYes\s*:=\s*([A-Za-z][A-Za-z0-9_.']+)", excerpt
            )
        ]
        seen: set[str] = set()
        result: list[dict[str, str]] = []
        while pending and len(result) < 16:
            name = pending.pop(0)
            if name in seen:
                continue
            seen.add(name)
            declaration = declaration_block("def", name)
            if declaration is None:
                continue
            qualified, source_file, block = declaration
            result.append(
                {
                    "declaration": qualified,
                    "source_file": source_file,
                    "answer_free_public_semantics": block,
                }
            )
            pending.extend(
                token
                for token in re.findall(r"\b([A-Z][A-Za-z0-9_']+)\b", block)
                if token not in seen
            )
        return result
    for declaration in (task.source_problem.term, task.target_problem.term):
        module = declaration.rsplit(".", 1)[0]
        relative = f"Lean/Reference/{module.replace('.', '/')}.lean"
        if relative not in allowed_files:
            _fail(
                "candidate_dependency_stale",
                f"endpoint interface file is outside the public dependency set: {relative}",
            )
        path = (workspace_root / relative).resolve()
        try:
            path.relative_to(workspace_root.resolve())
            lines = path.read_text(encoding="utf-8").splitlines()
        except (ValueError, OSError, UnicodeError) as error:
            _fail("candidate_dependency_stale", f"endpoint interface is unreadable: {error}")
        short_name = declaration.rsplit(".", 1)[-1]
        matches = [
            index
            for index, line in enumerate(lines)
            if re.search(
                rf"\b(?:def|abbrev)\s+{re.escape(short_name)}\b",
                line,
            )
        ]
        if len(matches) != 1:
            _fail(
                "candidate_dependency_stale",
                f"endpoint declaration {declaration!r} is not uniquely visible",
            )
        index = matches[0]
        excerpt = "\n".join(lines[max(0, index - 120) : index + 81])
        if len(excerpt) > 16_000:
            excerpt = excerpt[-16_000:]
        interfaces.append(
            {
                "declaration": declaration,
                "source_file": relative,
                "source_sha256": _tagged_file_hash(path),
                "answer_free_public_excerpt": excerpt,
                "carrier_interfaces": carrier_interfaces(excerpt),
                "semantic_interfaces": semantic_interfaces(excerpt),
            }
        )
    return tuple(interfaces)


def parse_exact_edge_node_patch(
    *, content: str, task: NPHardAuthoringTaskV2, node: NPHardAuthoringObligationV2
) -> str:
    """Parse a single-node patch and return the exact replacement body."""

    try:
        raw = json.loads(content)
    except (json.JSONDecodeError, UnicodeError) as error:
        _fail("invalid_np_hard_exact_edge_schema", f"node patch is not JSON: {error}")
    if not isinstance(raw, Mapping):
        _fail("invalid_np_hard_exact_edge_schema", "node patch must be an object")
    expected_keys = {
        "schema_version",
        "action",
        "request_id",
        "node_id",
        "declaration",
        "dependency_fingerprint",
        "replacement_body",
    }
    if set(raw) != expected_keys:
        _fail(
            "invalid_np_hard_exact_edge_schema",
            "node patch fields drifted",
        )
    if raw.get("schema_version") != EXACT_EDGE_NODE_PATCH_SCHEMA_V1:
        _fail("invalid_np_hard_exact_edge_schema", "unsupported node patch schema")
    if raw.get("action") != "submit_node_patch":
        _fail("invalid_np_hard_exact_edge_schema", "unsupported node patch action")
    if raw.get("request_id") != task.request_id:
        _fail("candidate_dependency_stale", "node patch request identity drifted")
    if raw.get("node_id") != node.node_id or raw.get("declaration") != node.declaration:
        _fail("candidate_dependency_stale", "node patch targets a different active node")
    if raw.get("dependency_fingerprint") != task.dependency_fingerprint:
        _fail("candidate_dependency_stale", "node patch dependency fingerprint drifted")
    body = raw.get("replacement_body")
    if not isinstance(body, str) or not body.strip():
        _fail("invalid_np_hard_exact_edge_schema", "node patch has no replacement body")
    lowered = body.lower()
    marker = next(
        (token for token in ("sorry", "admit", "axiom", "unsafe") if token in lowered),
        None,
    )
    if marker is not None:
        _fail("candidate_nonstandard_axiom", f"node body contains {marker}")
    if len(body) > 12_000:
        _fail("invalid_np_hard_exact_edge_schema", "node body exceeds 12,000 characters")
    return body


def _policy_route_violation(source: str) -> str | None:
    for prefix in _FORBIDDEN_ROUTE_IMPORT_PREFIXES:
        if prefix in source:
            return prefix
    return None


def _policy_composition_violation(source: str) -> bool:
    return "CertifiedReduction.comp" in source


def _compile_source(
    *,
    workspace_root: Path,
    task: NPHardAuthoringTaskV2,
    bodies: Mapping[str, str],
    include_final: bool,
    filename: str,
    timeout_seconds: int,
) -> tuple[CommandResult, str]:
    source = exact_edge_candidate_source(
        task=task, bodies=bodies, include_final=include_final
    )
    target = workspace_root / filename
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(source, encoding="utf-8")
    command = run_command(
        ["lake", "env", "lean", str(target)],
        cwd=workspace_root / "Lean",
        timeout_seconds=timeout_seconds,
    )
    return command, source


@dataclass(frozen=True)
class ExactEdgeAcceptedNode:
    node_id: str
    declaration: str
    body_sha256: str
    cumulative_source_sha256: str
    workspace_sha256: str
    command_exit_code: int

    def to_dict(self) -> dict[str, Any]:
        return {
            "node_id": self.node_id,
            "declaration": self.declaration,
            "body_sha256": self.body_sha256,
            "cumulative_source_sha256": self.cumulative_source_sha256,
            "workspace_sha256": self.workspace_sha256,
            "command_exit_code": self.command_exit_code,
        }


def _checkpoint_content(
    *,
    task: NPHardAuthoringTaskV2,
    accepted: Sequence[ExactEdgeAcceptedNode],
    bodies: Mapping[str, str],
    calls: Sequence[ExactEdgeNodeAttempt],
) -> dict[str, Any]:
    return {
        "schema_version": EXACT_EDGE_NODE_CHECKPOINT_SCHEMA_V1,
        "request_id": task.request_id,
        "accepted_nodes": [node.to_dict() for node in accepted],
        "accepted_bodies": {
            node.node_id: bodies[node.declaration] for node in accepted
        },
        "model_call_ledger": [call.to_dict() for call in calls],
    }


def write_exact_edge_checkpoint(
    *,
    path: Path,
    task: NPHardAuthoringTaskV2,
    accepted: Sequence[ExactEdgeAcceptedNode],
    bodies: Mapping[str, str],
    calls: Sequence[ExactEdgeNodeAttempt],
) -> str:
    payload = _checkpoint_content(task=task, accepted=accepted, bodies=bodies, calls=calls)
    digest = sha256_id(payload)
    payload["checkpoint_sha256"] = digest
    _write_json(path, payload)
    return digest


def load_exact_edge_checkpoint(
    *, path: Path, task: NPHardAuthoringTaskV2
) -> tuple[
    tuple[ExactEdgeAcceptedNode, ...],
    dict[str, str],
    tuple[ExactEdgeNodeAttempt, ...],
]:
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        _fail("checkpoint_tampered", f"exact-edge checkpoint is unreadable: {error}")
    if not isinstance(raw, Mapping) or raw.get("schema_version") != (
        EXACT_EDGE_NODE_CHECKPOINT_SCHEMA_V1
    ):
        _fail("checkpoint_tampered", "exact-edge checkpoint schema drifted")
    if raw.get("request_id") != task.request_id:
        _fail("checkpoint_tampered", "exact-edge checkpoint belongs to another task")
    digest_payload = {key: value for key, value in raw.items() if key != "checkpoint_sha256"}
    if raw.get("checkpoint_sha256") != sha256_id(digest_payload):
        _fail("checkpoint_tampered", "exact-edge checkpoint content hash mismatch")
    accepted: list[ExactEdgeAcceptedNode] = []
    for item in raw.get("accepted_nodes", []):
        if not isinstance(item, Mapping):
            _fail("checkpoint_tampered", "accepted node record is invalid")
        accepted.append(
            ExactEdgeAcceptedNode(
                node_id=str(item["node_id"]),
                declaration=str(item["declaration"]),
                body_sha256=str(item["body_sha256"]),
                cumulative_source_sha256=str(item["cumulative_source_sha256"]),
                workspace_sha256=str(item.get("workspace_sha256")),
                command_exit_code=int(item["command_exit_code"]),
            )
        )
    expected_ids = [node.node_id for node in task.gap_nodes]
    observed_ids = [node.node_id for node in accepted]
    if observed_ids != expected_ids[: len(observed_ids)]:
        _fail("checkpoint_tampered", "accepted checkpoint nodes are not a DAG prefix")
    raw_bodies = raw.get("accepted_bodies")
    if not isinstance(raw_bodies, Mapping):
        _fail("checkpoint_tampered", "checkpoint accepted bodies are missing")
    bodies: dict[str, str] = {}
    for record in accepted:
        body = raw_bodies.get(record.node_id)
        if not isinstance(body, str):
            _fail("checkpoint_tampered", "checkpoint body is missing for an accepted node")
        node = _node_by_id(task, record.node_id)
        if sha256_id(body) != record.body_sha256:
            _fail("checkpoint_tampered", "checkpoint body hash drifted")
        bodies[node.declaration] = body
    calls: list[ExactEdgeNodeAttempt] = []
    for index, item in enumerate(raw.get("model_call_ledger", []), start=1):
        if not isinstance(item, Mapping):
            _fail("checkpoint_tampered", "checkpoint ledger row is invalid")
        call_usage = item.get("usage")
        if not isinstance(call_usage, Mapping):
            response_value = item.get("response_file")
            if isinstance(response_value, str) and response_value:
                response_path = Path(response_value).resolve()
                try:
                    response_path.relative_to(path.parent.resolve())
                    response_payload = json.loads(response_path.read_text(encoding="utf-8"))
                except (ValueError, OSError, UnicodeError, json.JSONDecodeError):
                    response_payload = None
                if isinstance(response_payload, Mapping):
                    call_usage = _usage_safe(response_payload.get("usage"))
        calls.append(
            ExactEdgeNodeAttempt(
                call=int(item.get("call", index)),
                node=str(item["stage"]),
                attempt=int(item.get("attempt", 1)),
                model=item.get("model"),
                called=item.get("called") is True,
                ok=item.get("ok") is True,
                protocol_accepted=item.get("protocol_accepted") is True,
                status_code=item.get("status_code"),
                http_attempts=item.get("http_attempts"),
                finish_reason=item.get("finish_reason"),
                duration_seconds=item.get("duration_seconds"),
                usage=_usage_safe(call_usage),
                prompt_sha256=str(item.get("prompt_sha256") or ""),
                response_sha256=str(item.get("response_sha256") or ""),
                patch_sha256=item.get("patch_sha256"),
                diagnostics_sha256=item.get("diagnostics_sha256"),
                prompt_file=str(item.get("prompt_file") or ""),
                response_file=str(item.get("response_file") or ""),
                patch_file=item.get("patch_file"),
                workspace_sha256=item.get("workspace_sha256"),
                request_id=(
                    str(item["request_id"])
                    if isinstance(item.get("request_id"), str)
                    else None
                ),
                case_id=(
                    str(item["case_id"])
                    if isinstance(item.get("case_id"), str)
                    else None
                ),
                task_id=(
                    str(item["task_id"])
                    if isinstance(item.get("task_id"), str)
                    else None
                ),
            )
        )
    return tuple(accepted), bodies, tuple(calls)


def _replay_resumed_prefix(
    *,
    workspace_root: Path,
    case_output: Path,
    task: NPHardAuthoringTaskV2,
    accepted: Sequence[ExactEdgeAcceptedNode],
    bodies: Mapping[str, str],
    policy: Mapping[str, Any],
    timeout_seconds: int,
) -> None:
    """Independently compile every resumed prefix before trusting it."""

    replay_bodies: dict[str, str] = {}
    evidence_root = case_output / "commands" / "resume-prefix"
    evidence_root.mkdir(parents=True, exist_ok=True)
    for ordinal, record in enumerate(accepted, start=1):
        node = task.gap_nodes[ordinal - 1]
        if record.node_id != node.node_id or record.declaration != node.declaration:
            _fail("checkpoint_tampered", "resumed node identity drifted")
        body = bodies.get(node.declaration)
        if body is None or sha256_id(body) != record.body_sha256:
            _fail("checkpoint_tampered", "resumed node body binding drifted")
        replay_bodies[node.declaration] = body
        command, source = _compile_source(
            workspace_root=workspace_root,
            task=task,
            bodies=replay_bodies,
            include_final=False,
            filename=f"work/resume-prefix-{ordinal:02d}.lean",
            timeout_seconds=timeout_seconds,
        )
        source_hash = "sha256:" + _hash_text(source)
        route_violation = _policy_route_violation(source)
        composition_violation = (
            _policy_composition_violation(source)
            if not bool(policy.get("allow_composition"))
            else False
        )
        _write_json(
            evidence_root / f"{ordinal:02d}-{node.node_id}.json",
            {
                "node_id": node.node_id,
                "source_sha256": source_hash,
                "command": command.to_dict(),
                "route_violation": route_violation,
                "composition_violation": composition_violation,
            },
        )
        if (
            not command.ok
            or route_violation is not None
            or composition_violation
            or record.command_exit_code != 0
            or record.cumulative_source_sha256 != source_hash
            or record.workspace_sha256 != source_hash
        ):
            _fail(
                "candidate_dependency_stale",
                f"independent replay rejected resumed node {node.node_id!r}",
            )


def _usage_safe(usage: Mapping[str, Any] | None) -> Mapping[str, int] | None:
    if not isinstance(usage, Mapping):
        return None
    safe = {
        str(name): value
        for name, value in usage.items()
        if isinstance(name, str)
        and isinstance(value, int)
        and not isinstance(value, bool)
        and value >= 0
    }
    # Providers may add nested token-detail objects.  The benchmark freezes the
    # auditable top-level integer counters and intentionally drops only those
    # nested explanatory fields.
    return safe or None


def run_exact_edge_staged_construction(
    *,
    workspace_root: Path,
    case_output: Path,
    task: NPHardAuthoringTaskV2,
    policy: Mapping[str, Any],
    statement: str,
    statement_hash: str,
    model_client: Any,
    model_name: str | None,
    timeout_seconds: int,
    case_id: str | None = None,
    attempt_budget: int = EXACT_EDGE_MAX_NODE_ATTEMPTS,
    resume_checkpoint: Path | None = None,
    max_new_nodes: int | None = None,
) -> dict[str, Any]:
    """Execute the typed exact-edge DAG serially, one model call per node attempt.

    Returns a ``hardness_exact_edge_staged_result_v1`` payload that the
    exact-edge case auditor re-validates independently.
    """

    workspace_root = workspace_root.resolve()
    case_output = case_output.resolve()
    bodies: dict[str, str] = {}
    accepted: list[ExactEdgeAcceptedNode] = []
    ledger: list[ExactEdgeNodeAttempt] = []
    call_number = 0
    endpoint_interfaces = _public_endpoint_interfaces(
        workspace_root=workspace_root, task=task
    )
    complexity_interfaces = _public_complexity_interfaces(
        workspace_root=workspace_root, task=task
    )
    if resume_checkpoint is not None:
        resumed_nodes, resumed_bodies, resumed_calls = load_exact_edge_checkpoint(
            path=resume_checkpoint, task=task
        )
        accepted = list(resumed_nodes)
        bodies = dict(resumed_bodies)
        ledger = list(resumed_calls)
        call_number = len(ledger)
        _replay_resumed_prefix(
            workspace_root=workspace_root,
            case_output=case_output,
            task=task,
            accepted=accepted,
            bodies=bodies,
            policy=policy,
            timeout_seconds=timeout_seconds,
        )

    failure_code: str | None = None
    failure_message: str | None = None
    new_nodes = 0

    def persist_checkpoint() -> None:
        write_exact_edge_checkpoint(
            path=case_output / "checkpoint.json",
            task=task,
            accepted=accepted,
            bodies=bodies,
            calls=ledger,
        )

    for ordinal in range(len(accepted) + 1, len(task.gap_nodes) + 1):
        if max_new_nodes is not None and new_nodes >= max_new_nodes:
            break
        node = task.gap_nodes[ordinal - 1]
        diagnostic: str | None = None
        accepted_this_node = False
        prior_attempts = max(
            (call.attempt for call in ledger if call.node == node.node_id),
            default=0,
        )
        for attempt in range(prior_attempts + 1, attempt_budget + 1):
            if model_client is None:
                failure_code = "model_provider_unavailable"
                failure_message = "no model client configured"
                break
            prompt = build_exact_edge_node_prompt(
                task=task,
                node=node,
                accepted_bodies=bodies,
                policy=policy,
                statement=statement,
                statement_hash=statement_hash,
                diagnostic=diagnostic,
                attempt=attempt,
                remaining_attempts=attempt_budget - attempt,
                timeout_seconds=timeout_seconds,
                public_endpoint_interfaces=endpoint_interfaces,
                public_complexity_interfaces=complexity_interfaces,
            )
            call_request_id = sha256_id(
                {
                    "task_request_id": task.request_id,
                    "case_id": case_id,
                    "node_id": node.node_id,
                    "attempt": attempt,
                }
            )
            response = model_client.complete_json(
                system=_EXACT_EDGE_SYSTEM_PROMPT, prompt=prompt
            )
            model_root = case_output / "model-calls"
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
            call_number += 1
            prompt_hash = _hash_text(prompt)
            response_hash = _hash_text(str(response.content or ""))
            if not response.called:
                ledger.append(
                    ExactEdgeNodeAttempt(
                        call=call_number,
                        node=node.node_id,
                        attempt=attempt,
                        model=model_name,
                        called=False,
                        ok=False,
                        protocol_accepted=False,
                        status_code=response.status_code,
                        http_attempts=response.attempts,
                        finish_reason=response.finish_reason,
                        duration_seconds=response.duration_seconds,
                        usage=_usage_safe(response.usage),
                        prompt_sha256=prompt_hash,
                        response_sha256=response_hash,
                        patch_sha256=None,
                        diagnostics_sha256=None,
                        prompt_file=str(prompt_path.resolve()),
                        response_file=str(response_path.resolve()),
                        patch_file=None,
                        workspace_sha256=None,
                        request_id=call_request_id,
                        case_id=case_id,
                        task_id=task.request_id,
                    )
                )
                persist_checkpoint()
                failure_code = "model_provider_unavailable"
                failure_message = response.error or "model provider did not execute"
                break
            if not response.ok:
                ledger.append(
                    ExactEdgeNodeAttempt(
                        call=call_number,
                        node=node.node_id,
                        attempt=attempt,
                        model=model_name,
                        called=True,
                        ok=False,
                        protocol_accepted=False,
                        status_code=response.status_code,
                        http_attempts=response.attempts,
                        finish_reason=response.finish_reason,
                        duration_seconds=response.duration_seconds,
                        usage=_usage_safe(response.usage),
                        prompt_sha256=prompt_hash,
                        response_sha256=response_hash,
                        patch_sha256=None,
                        diagnostics_sha256=None,
                        prompt_file=str(prompt_path.resolve()),
                        response_file=str(response_path.resolve()),
                        patch_file=None,
                        workspace_sha256=None,
                        request_id=call_request_id,
                        case_id=case_id,
                        task_id=task.request_id,
                    )
                )
                persist_checkpoint()
                retryable_provider_failure = (
                    response.status_code is None
                    or response.status_code == 429
                    or response.status_code >= 500
                )
                if response.status_code == 200 or retryable_provider_failure:
                    diagnostic = response.error or (
                        "model returned no complete JSON body; produce a shorter single-node body"
                    )
                    continue
                failure_code = "model_provider_unavailable"
                failure_message = response.error or "model request failed"
                break
            try:
                body = parse_exact_edge_node_patch(
                    content=response.content, task=task, node=node
                )
            except ExactEdgeAuthoringError as error:
                ledger.append(
                    ExactEdgeNodeAttempt(
                        call=call_number,
                        node=node.node_id,
                        attempt=attempt,
                        model=model_name,
                        called=True,
                        ok=True,
                        protocol_accepted=False,
                        status_code=response.status_code,
                        http_attempts=response.attempts,
                        finish_reason=response.finish_reason,
                        duration_seconds=response.duration_seconds,
                        usage=_usage_safe(response.usage),
                        prompt_sha256=prompt_hash,
                        response_sha256=response_hash,
                        patch_sha256=None,
                        diagnostics_sha256=sha256_id({"diagnostic": error.message}),
                        prompt_file=str(prompt_path.resolve()),
                        response_file=str(response_path.resolve()),
                        patch_file=None,
                        workspace_sha256=None,
                        request_id=call_request_id,
                        case_id=case_id,
                        task_id=task.request_id,
                    )
                )
                persist_checkpoint()
                diagnostic = error.message
                continue
            body_hash = sha256_id(body)
            patch_hash = _hash_text(body)
            patch_path = model_root / f"{node.node_id}-attempt-{attempt:02d}-patch.json"
            _write_json(
                patch_path,
                {
                    "schema_version": EXACT_EDGE_NODE_PATCH_SCHEMA_V1,
                    "action": "submit_node_patch",
                    "request_id": task.request_id,
                    "node_id": node.node_id,
                    "declaration": node.declaration,
                    "dependency_fingerprint": task.dependency_fingerprint,
                    "replacement_body": body,
                },
            )
            trial_bodies = {**bodies, node.declaration: body}
            command, source = _compile_source(
                workspace_root=workspace_root,
                task=task,
                bodies=trial_bodies,
                include_final=False,
                filename="work/Candidate.lean",
                timeout_seconds=timeout_seconds,
            )
            route_violation = _policy_route_violation(source)
            composition_violation = (
                _policy_composition_violation(source)
                if not bool(policy.get("allow_composition"))
                else False
            )
            accepted_attempt = (
                command.ok and route_violation is None and not composition_violation
            )
            workspace_hash = "sha256:" + _hash_text(source)
            diagnostics = "\n".join(
                line
                for stream in (command.stdout, command.stderr)
                for line in stream.splitlines()
                if line.strip()
            )[:8_000]
            ledger.append(
                ExactEdgeNodeAttempt(
                    call=call_number,
                    node=node.node_id,
                    attempt=attempt,
                    model=model_name,
                    called=True,
                    ok=True,
                    protocol_accepted=accepted_attempt,
                    status_code=response.status_code,
                    http_attempts=response.attempts,
                    finish_reason=response.finish_reason,
                    duration_seconds=response.duration_seconds,
                    usage=_usage_safe(response.usage),
                    prompt_sha256=prompt_hash,
                    response_sha256=response_hash,
                    patch_sha256=patch_hash,
                    diagnostics_sha256=sha256_id({"diagnostic": diagnostics}),
                    prompt_file=str(prompt_path.resolve()),
                    response_file=str(response_path.resolve()),
                    patch_file=str(patch_path.resolve()),
                    workspace_sha256=workspace_hash,
                    request_id=call_request_id,
                    case_id=case_id,
                    task_id=task.request_id,
                )
            )
            if not accepted_attempt:
                persist_checkpoint()
                if route_violation is not None:
                    failure_code = "exact_edge_route_import_forbidden"
                    failure_message = f"route import blocked: {route_violation}"
                    break
                if composition_violation:
                    failure_code = "exact_edge_composition_forbidden"
                    failure_message = "composition of existing reductions is forbidden"
                    break
                diagnostic = (
                    (f"Lean rejected the active body:\n{diagnostics}" if diagnostics else "")
                ).strip() or "Lean rejected the active body"
                continue
            accepted.append(
                ExactEdgeAcceptedNode(
                    node_id=node.node_id,
                    declaration=node.declaration,
                    body_sha256=body_hash,
                    cumulative_source_sha256="sha256:" + _hash_text(source),
                    workspace_sha256=workspace_hash,
                    command_exit_code=command.exit_code,
                )
            )
            bodies[node.declaration] = body
            accepted_this_node = True
            new_nodes += 1
            persist_checkpoint()
            break
        if not accepted_this_node and failure_code is None:
            failure_code = "exact_edge_node_attempt_budget_exhausted"
            failure_message = f"node {node.node_id} consumed its attempt budget"
        if not accepted_this_node:
            break

    all_accepted = len(accepted) == len(task.gap_nodes)
    audits: dict[str, dict[str, Any]] = {}
    artifact_path: Path | None = None
    artifact_source = ""
    if all_accepted and failure_code is None:
        artifact_command, artifact_source = _compile_source(
            workspace_root=workspace_root,
            task=task,
            bodies=bodies,
            include_final=True,
            filename="Final.lean",
            timeout_seconds=timeout_seconds,
        )
        replay_command, _ = _compile_source(
            workspace_root=workspace_root,
            task=task,
            bodies=bodies,
            include_final=True,
            filename="Replay.lean",
            timeout_seconds=timeout_seconds,
        )
        evidence_root = case_output / "commands"
        evidence_root.mkdir(parents=True, exist_ok=True)
        _write_json(evidence_root / "exact-edge-staged-final.json", artifact_command.to_dict())
        _write_json(evidence_root / "exact-edge-staged-replay.json", replay_command.to_dict())
        audit_root = case_output / "deletion-audits"
        audit_root.mkdir(parents=True, exist_ok=True)
        deletion_audits: list[dict[str, Any]] = []
        for deleted in task.gap_nodes:
            audit_bodies = {
                declaration: body
                for declaration, body in bodies.items()
                if declaration != deleted.declaration
            }
            audit_source = exact_edge_candidate_source(
                task=task,
                bodies=audit_bodies,
                include_final=True,
                deletion_audit_deleted_declaration=deleted.declaration,
            )
            audit_path = audit_root / f"without-{deleted.node_id}.lean"
            audit_path.write_text(audit_source, encoding="utf-8")
            audit_command = run_command(
                ["lake", "env", "lean", str(audit_path)],
                cwd=workspace_root / "Lean",
                timeout_seconds=timeout_seconds,
            )
            deletion_audits.append(
                {
                    "node_id": deleted.node_id,
                    "declaration": deleted.declaration,
                    "audit_file": str(audit_path),
                    "audit_file_sha256": _tagged_file_hash(audit_path),
                    "command": audit_command.to_dict(),
                    "passed": (
                        not audit_command.ok
                        and deleted.declaration
                        in (audit_command.stdout + audit_command.stderr)
                    ),
                }
            )
        _write_json(evidence_root / "exact-edge-staged-deletion.json", {"audits": deletion_audits})
        artifact_evidence = case_output / "ExactEdge.lean"
        artifact_evidence.write_text(artifact_source, encoding="utf-8")
        artifact_path = artifact_evidence
        deletion_passed = bool(deletion_audits) and all(
            item["passed"] for item in deletion_audits
        )
        if artifact_command.ok and replay_command.ok and deletion_passed:
            audits = {}
            for name, command, source_file in (
                ("kernel", artifact_command, artifact_evidence),
                ("replay", replay_command, artifact_evidence),
                ("axiom", artifact_command, artifact_evidence),
                ("endpoint", artifact_command, artifact_evidence),
                ("dependency", artifact_command, artifact_evidence),
                ("program_direct_tm_coherence", artifact_command, artifact_evidence),
                ("semantic_iff", artifact_command, artifact_evidence),
                ("polynomial_bound", artifact_command, artifact_evidence),
            ):
                evidence = evidence_root / f"exact-edge-staged-{name}.json"
                _write_json(evidence, command.to_dict())
                audits[name] = {
                    "status": "passed",
                    "ok": True,
                    "evidence_file": str(evidence.resolve()),
                    "evidence_sha256": _tagged_file_hash(evidence),
                    "audit_artifact_file": str(source_file.resolve()),
                    "audit_artifact_sha256": _tagged_file_hash(source_file),
                    "blocker": None,
                }
        else:
            failure_code = "exact_edge_final_artifact_failed"
            failure_message = (
                "final certified-reduction artifact failed to compile, replay, "
                "or pass its deletion audits"
            )
    status = (
        "VERIFIED"
        if all_accepted and audits and failure_code is None
        else "CHECKPOINTED"
        if not all_accepted and failure_code is None
        else "FAILED"
    )
    return {
        "schema_version": EXACT_EDGE_STAGED_RESULT_SCHEMA_V1,
        "task_class": EXACT_EDGE_AUTHORING_TASK_CLASS,
        "case_id": case_id,
        "status": status,
        "goal": {
            "objective": "reduce_to",
            "source_declaration": task.source_problem.term,
            "target_declaration": task.target_problem.term,
        },
        "selected_route": None,
        "authoring_attempts": [],
        "model_calls": [call.to_dict() for call in ledger],
        "authored_candidate_declaration": (
            task.final_candidate_declaration if status == "VERIFIED" else None
        ),
        "authored_route_declaration": None,
        "artifact_file": str(artifact_path.resolve()) if artifact_path is not None else None,
        "artifact_source_sha256": (
            "sha256:" + _hash_text(artifact_source) if artifact_source else None
        ),
        "node_count": len(task.gap_nodes),
        "resumed": resume_checkpoint is not None,
        "resumed_node_count": len(accepted) - new_nodes,
        "new_node_count": new_nodes,
        "accepted_nodes": [record.to_dict() for record in accepted],
        "audits": audits,
        "failure_code": failure_code,
        "failure_message": failure_message,
    }
