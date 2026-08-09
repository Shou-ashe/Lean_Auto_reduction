"""Stage-M typed optional-authoring ABI, prompt, suite, and batch artifact."""

from __future__ import annotations

import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

from .benchmark import BenchmarkCase
from .certificate_dag import CertificateDAG
from .models import sha256_id
from .typed_packets import PacketIndex, PacketValidationError


TYPED_AUTHORING_REQUEST_SCHEMA = "hardness_typed_authoring_request_v1"
PACKET_SELECTION_SCHEMA = "hardness_packet_selection_v1"
TYPED_AUTHORING_REPORT_SCHEMA = "hardness_typed_authoring_report_v1"
TYPED_AUTHORING_SYSTEM_PROMPT = """You are an untrusted typed packet selector for Lean 4 optional authoring.
The orchestrator has already fixed opaque source/target endpoint IDs, the objective, active
certificate node, capability kind, packet index, editable boundary, and attempt budget. Select
exactly one packet already present in the supplied public index and copy its immutable candidate_id
and template_kind into bindings. You may not invent a packet, declaration, endpoint, direction,
import, theorem, axiom, proof, or source edit. Return exactly one JSON object matching
hardness_packet_selection_v1 and no markdown fence. If no packet is listed, do not fabricate one."""

ORACLE_MARKERS = (
    ".Oracles.",
    ".Gold.",
    ".GoldProofs.",
    ".HiddenTargets.",
    ".Legacy.",
)


@dataclass(frozen=True)
class TypedAuthoringRequest:
    source_declaration: str
    target_declaration: str
    objective: str
    active_node: str
    expected_capability_head: str
    allowed_packet_kinds: tuple[str, ...]
    required_checker_combinators: tuple[str, ...]
    witness_shape: str
    model_selection_required: bool
    attempt_budget: int
    authoring_mode: str
    schema_version: str = TYPED_AUTHORING_REQUEST_SCHEMA

    @property
    def request_id(self) -> str:
        return sha256_id({"schema_version": self.schema_version, **asdict(self)})

    @classmethod
    def from_case(cls, case: BenchmarkCase) -> "TypedAuthoringRequest":
        value = case.typed_authoring
        return cls(
            source_declaration=case.source,
            target_declaration=case.target or case.source,
            objective=case.objective,
            active_node=str(value["active_node"]),
            expected_capability_head=str(value["expected_capability_head"]),
            allowed_packet_kinds=tuple(value["allowed_packet_kinds"]),
            required_checker_combinators=tuple(value["required_checker_combinators"]),
            witness_shape=str(value["witness_shape"]),
            model_selection_required=bool(value["model_selection_required"]),
            attempt_budget=int(case.authoring_policy.get("attempt_budget", 1)),
            authoring_mode=str(case.authoring_policy.get("mode", "disabled")),
        )

    def to_dict(self) -> dict[str, object]:
        value = asdict(self)
        value["request_id"] = self.request_id
        return value


def _endpoint_id(declaration: str) -> str:
    """Return a stable prompt-safe identity for one exact Lean endpoint."""

    return sha256_id(
        {
            "schema_version": "hardness_prompt_endpoint_v1",
            "declaration": declaration,
        }
    )


def _capability_kind(capability_head: str) -> str:
    mapping = {
        "ComplexityReduction.Encoding.PresentedProblem": "presented_problem",
        (
            "ComplexityReduction.Encoding.StructuralRepresentationCertificate"
        ): "lawful_presentation",
        "ComplexityReduction.Certificate.CertifiedReduction": "certified_reduction",
        "ComplexityReduction.Certificate.NativeTMInNP": "native_tm_membership",
        "ComplexityReduction.Certificate.NativeTMNPComplete": "native_tm_completeness",
        "ComplexityReduction.Protocol.TypedAutoReductionResult": "typed_final_result",
    }
    try:
        return mapping[capability_head]
    except KeyError as error:
        raise ValueError("typed-authoring prompt contains an unsupported capability head") from error


def _public_request_view(request: TypedAuthoringRequest) -> dict[str, object]:
    source_id = _endpoint_id(request.source_declaration)
    target_id = _endpoint_id(request.target_declaration)
    return {
        "schema_version": "hardness_typed_authoring_request_public_v1",
        "request_id": request.request_id,
        "source_endpoint_id": source_id,
        "target_endpoint_id": target_id,
        "same_endpoint": source_id == target_id,
        "objective": request.objective,
        "active_node": request.active_node,
        "expected_capability_kind": _capability_kind(request.expected_capability_head),
        "allowed_packet_kinds": list(request.allowed_packet_kinds),
        "required_checker_combinators": list(request.required_checker_combinators),
        "witness_shape": request.witness_shape,
        "model_selection_required": request.model_selection_required,
        "attempt_budget": request.attempt_budget,
        "authoring_mode": request.authoring_mode,
    }


def _public_gap_view(gap: Mapping[str, Any]) -> dict[str, object]:
    source = str(gap.get("source_declaration", ""))
    target = str(gap.get("target_declaration", source))
    capability_head = str(gap.get("expected_capability_head", ""))
    return {
        "schema_version": "hardness_typed_gap_public_v1",
        "gap_id": str(gap.get("gap_id", "")),
        "failure_code": str(gap.get("failure_code", "")),
        "role": str(gap.get("role", "")),
        "source_endpoint_id": _endpoint_id(source),
        "target_endpoint_id": _endpoint_id(target),
        "same_endpoint": source == target,
        "expected_capability_kind": _capability_kind(capability_head),
        "registry_fingerprint": str(gap.get("registry_fingerprint", "")),
    }


def _public_dag_view(dag: CertificateDAG) -> dict[str, object]:
    return {
        "schema_version": "hardness_certificate_dag_public_v1",
        "dag_id": dag.dag_id,
        "source_endpoint_id": _endpoint_id(dag.source_declaration),
        "target_endpoint_id": _endpoint_id(dag.target_declaration),
        "same_endpoint": dag.source_declaration == dag.target_declaration,
        "objective": dag.objective,
        "active_node": dag.active_node,
        "nodes": [
            {
                "node_id": node.node_id,
                "kind": node.kind,
                "input_endpoint_id": _endpoint_id(node.input_type),
                "output_endpoint_id": _endpoint_id(node.output_type),
                "same_endpoint": node.input_type == node.output_type,
                "direction": node.direction,
                "capability_kind": _capability_kind(node.capability_head),
                "preconditions": list(node.preconditions),
                "candidate_source_hash": node.candidate_source_hash,
                "verification_status": node.verification_status,
            }
            for node in dag.nodes
        ],
    }


def _public_packet_index_view(index: PacketIndex) -> dict[str, object]:
    return {
        "schema_version": "hardness_packet_index_public_v1",
        "index_id": index.index_id,
        "dag_id": index.dag_id,
        "registry_fingerprint": index.registry_fingerprint,
        "packets": [
            {
                "packet_id": packet.packet_id,
                "packet_kind": packet.packet_kind,
                "source_endpoint_id": _endpoint_id(packet.source_declaration),
                "target_endpoint_id": _endpoint_id(packet.target_declaration),
                "same_endpoint": packet.source_declaration == packet.target_declaration,
                "direction": packet.direction,
                "capability_kind": _capability_kind(packet.capability_head),
                "candidate_id": packet.candidate_id,
                "template_kind": packet.template_kind,
                "required_combinators": list(packet.required_combinators),
                "candidate_source_hash": packet.candidate_source_hash,
            }
            for packet in index.packets
        ],
    }


@dataclass(frozen=True)
class PacketSelection:
    task_id: str
    packet_id: str
    candidate_id: str
    template_kind: str
    explanation: str
    schema_version: str = PACKET_SELECTION_SCHEMA

    def to_dict(self) -> dict[str, str]:
        return asdict(self)


def typed_authoring_task_id(
    *, request: TypedAuthoringRequest, gap_id: str, dag: CertificateDAG, index: PacketIndex
) -> str:
    return sha256_id(
        {
            "schema_version": "hardness_typed_authoring_task_v1",
            "request_id": request.request_id,
            "gap_id": gap_id,
            "dag_id": dag.dag_id,
            "packet_index_id": index.index_id,
        }
    )


def _all_strings(value: Any) -> list[str]:
    if isinstance(value, str):
        return [value]
    if isinstance(value, Mapping):
        return [item for nested in value.values() for item in _all_strings(nested)]
    if isinstance(value, (list, tuple)):
        return [item for nested in value for item in _all_strings(nested)]
    return []


def audit_packet_selection_prompt(payload: Mapping[str, Any]) -> None:
    if set(payload) != {
        "schema_version",
        "task_id",
        "request",
        "typed_gap",
        "certificate_dag",
        "packet_index",
        "last_protocol_error",
        "return_exact_json_shape",
    }:
        raise ValueError("typed-authoring prompt keys do not match the public ABI")
    if payload.get("schema_version") != "hardness_packet_selection_request_v1":
        raise ValueError("typed-authoring prompt uses an unsupported schema")
    forbidden_keys = {
        "expected",
        "coverage",
        "gold",
        "gold_proof",
        "case_id",
        "final_status",
        "final_failure_code",
        "source_declaration",
        "target_declaration",
        "expected_capability_head",
        "provider_declaration",
        "component_declarations",
        "allowed_imports",
        "declared_axioms",
        "source_display",
        "target_display",
    }

    def keys(value: Any) -> set[str]:
        if isinstance(value, Mapping):
            return {str(key) for key in value} | {
                item for nested in value.values() for item in keys(nested)
            }
        if isinstance(value, list):
            return {item for nested in value for item in keys(nested)}
        return set()

    leaked = keys(payload) & forbidden_keys
    if leaked:
        raise ValueError(f"typed-authoring prompt leaks evaluation fields: {sorted(leaked)}")
    for value in _all_strings(payload):
        if any(marker in value for marker in ORACLE_MARKERS):
            raise ValueError("typed-authoring prompt references quarantined oracle data")


def build_packet_selection_prompt(
    *,
    task_id: str,
    request: TypedAuthoringRequest,
    gap: Mapping[str, Any],
    dag: CertificateDAG,
    index: PacketIndex,
    last_protocol_error: str = "",
) -> str:
    response_shape = {
        "schema_version": PACKET_SELECTION_SCHEMA,
        "action": "select_packet",
        "task_id": task_id,
        "packet_id": "sha256:<copy one packet_id from packet_index>",
        "bindings": {
            "candidate_id": "sha256:<copy the selected packet candidate_id>",
            "template_kind": "<copy the selected packet template_kind>",
        },
        "explanation": "One short public-data-only reason for this typed selection.",
    }
    payload = {
        "schema_version": "hardness_packet_selection_request_v1",
        "task_id": task_id,
        "request": _public_request_view(request),
        "typed_gap": _public_gap_view(gap),
        "certificate_dag": _public_dag_view(dag),
        "packet_index": _public_packet_index_view(index),
        "last_protocol_error": last_protocol_error[-2000:],
        "return_exact_json_shape": response_shape,
    }
    audit_packet_selection_prompt(payload)
    return json.dumps(payload, ensure_ascii=False, sort_keys=True)


def parse_packet_selection(
    content: str, *, task_id: str, index: PacketIndex
) -> PacketSelection:
    try:
        payload = json.loads(content.strip())
    except json.JSONDecodeError as error:
        raise PacketValidationError(
            "packet_selection_protocol_error", "response must be exactly one JSON object"
        ) from error
    if not isinstance(payload, dict) or set(payload) != {
        "schema_version",
        "action",
        "task_id",
        "packet_id",
        "bindings",
        "explanation",
    }:
        raise PacketValidationError(
            "packet_selection_protocol_error", "response keys do not match the selection ABI"
        )
    if payload.get("schema_version") != PACKET_SELECTION_SCHEMA:
        raise PacketValidationError(
            "packet_selection_protocol_error", "response uses an unsupported selection schema"
        )
    if payload.get("action") != "select_packet" or payload.get("task_id") != task_id:
        raise PacketValidationError(
            "packet_selection_protocol_error", "response changed the fixed action or task id"
        )
    packet_id = payload.get("packet_id")
    if not isinstance(packet_id, str):
        raise PacketValidationError(
            "packet_selection_protocol_error", "packet_id must be a string"
        )
    packet = index.packet(packet_id)
    bindings = payload.get("bindings")
    if not isinstance(bindings, dict) or set(bindings) != {"candidate_id", "template_kind"}:
        raise PacketValidationError(
            "packet_selection_protocol_error", "bindings must copy exactly two packet fields"
        )
    if (
        bindings.get("candidate_id") != packet.candidate_id
        or bindings.get("template_kind") != packet.template_kind
    ):
        raise PacketValidationError(
            "packet_selection_protocol_error", "bindings do not match the selected immutable packet"
        )
    explanation = payload.get("explanation")
    if not isinstance(explanation, str) or not explanation.strip():
        raise PacketValidationError(
            "packet_selection_protocol_error", "selection explanation must be non-empty"
        )
    return PacketSelection(
        task_id=task_id,
        packet_id=packet.packet_id,
        candidate_id=packet.candidate_id,
        template_kind=packet.template_kind,
        explanation=explanation.strip(),
    )


EXPECTED_CASE_IDS = (
    "authoring-lawful-presentation",
    "authoring-semantic-proof",
    "authoring-single-edge-program",
    "authoring-bounded-subset-membership",
    "authoring-pair-list-membership",
    "authoring-missing-direct-tm",
    "authoring-unsupported-checker",
    "authoring-wrong-endpoint-or-axiom",
)


def validate_typed_authoring_suite(cases: Sequence[BenchmarkCase]) -> None:
    if tuple(case.id for case in cases) != EXPECTED_CASE_IDS:
        raise ValueError("typed-authoring suite IDs/order differ from the frozen Stage-M matrix")
    if sum(case.is_positive for case in cases) != 5:
        raise ValueError("typed-authoring suite must contain exactly five positives")
    if sum(not case.is_positive for case in cases) != 3:
        raise ValueError("typed-authoring suite must contain exactly three negatives")
    for case in cases:
        request = TypedAuthoringRequest.from_case(case)
        if request.schema_version != TYPED_AUTHORING_REQUEST_SCHEMA:
            raise ValueError(f"{case.id} has the wrong typed-authoring request schema")
        if case.execution_layer != "optional_authoring":
            raise ValueError(f"{case.id} is not isolated in optional_authoring")
        if case.verification_profile != "strict-release":
            raise ValueError(f"{case.id} does not request strict release verification")
        if case.expected.baseline_status != "BLOCKED" or not case.expected.baseline_failure_code:
            raise ValueError(f"{case.id} does not freeze one Core baseline blocker")
        if case.coverage.get("expected_gap_closure_count", 1 if case.is_positive else 0) not in {0, 1}:
            raise ValueError(f"{case.id} has an invalid gap-closure count")


@dataclass(frozen=True)
class TypedAuthoringArtifactCase:
    case_id: str
    input_module: str
    objective: str
    source_declaration: str
    target_declaration: str
    route_atoms: tuple[str, ...] = ()
    membership_declaration: str | None = None
    hub_declaration: str | None = None
    completeness_declaration: str | None = None
    candidate_modules: tuple[str, ...] = ()


def _lean_identifier(case_id: str) -> str:
    value = re.sub(r"[^A-Za-z0-9_]", "_", case_id)
    if not value or value[0].isdigit():
        value = "case_" + value
    return value


def _path_term(source: str, atoms: Sequence[str]) -> str:
    if not atoms:
        return f"ComplexityReduction.Certificate.CertifiedPath.refl {source}"
    term = f"ComplexityReduction.Certificate.CertifiedPath.step ({atoms[0]})"
    for atom in atoms[1:]:
        term = (
            "ComplexityReduction.Certificate.CertifiedPath.cons\n"
            f"      ({term})\n"
            f"      ({atom})"
        )
    return term


def build_typed_authoring_batch_artifact_source(
    cases: Sequence[TypedAuthoringArtifactCase],
) -> str:
    imports = {
        "ComplexityReduction.Agent.Hardness.Runtime",
        "ComplexityReduction.AxiomGate",
        "ComplexityReduction.Certificate.CompletenessTransport",
    }
    for case in cases:
        imports.add(case.input_module)
        imports.update(case.candidate_modules)
    body: list[str] = [
        *(f"import {module}" for module in sorted(imports)),
        "",
        "namespace Benchmark.Hardness.TypedAuthoring.Final",
        "",
        "noncomputable section",
        "",
        "def policy : ComplexityReduction.Protocol.AutoReductionTrustPolicy :=",
        "  { presentation := .exactUser, requireNativeNP := true }",
        "",
    ]
    audited: list[str] = []
    for case in cases:
        name = _lean_identifier(case.case_id)
        if case.objective == "reduce_to":
            if not case.route_atoms:
                raise ValueError(f"{case.case_id} has no selected reduction atoms")
            body.extend(
                [
                    f"noncomputable def {name}_path :",
                    "    ComplexityReduction.Certificate.CertifiedPath",
                    f"      {case.source_declaration} {case.target_declaration} :=",
                    f"  {_path_term(case.source_declaration, case.route_atoms)}",
                    "",
                    f"def {name}_request : ComplexityReduction.Protocol.TypedAutoReductionRequest where",
                    f"  source := .fromPresented {case.source_declaration}",
                    "  policy := policy",
                    f"  objective := .reduceTo {case.source_declaration} {case.target_declaration}",
                    "",
                    "@[complexity_reduction_ir_typed_final_result]",
                    f"noncomputable def {name}_result :",
                    f"    ComplexityReduction.Protocol.TypedAutoReductionResult {name}_request := by",
                    f"  simpa [{name}_request] using",
                    "    ComplexityReduction.Protocol.TypedAutoReductionResult.reduceToPath",
                    f"      policy (by rfl) {name}_path",
                    "",
                ]
            )
            audited.extend(
                [
                    f"Benchmark.Hardness.TypedAuthoring.Final.{name}_path",
                    f"Benchmark.Hardness.TypedAuthoring.Final.{name}_result",
                ]
            )
        elif case.objective == "prove_in_np":
            if not case.membership_declaration:
                raise ValueError(f"{case.case_id} has no selected native membership")
            body.extend(
                [
                    f"theorem {name}_membership :",
                    f"    ComplexityReduction.Certificate.NativeTMInNP {case.source_declaration} :=",
                    f"  {case.membership_declaration}",
                    "",
                    f"def {name}_request : ComplexityReduction.Protocol.TypedAutoReductionRequest where",
                    f"  source := .fromPresented {case.source_declaration}",
                    "  policy := policy",
                    f"  objective := .proveInNP {case.source_declaration}",
                    "",
                    "@[complexity_reduction_ir_typed_final_result]",
                    f"noncomputable def {name}_result :",
                    f"    ComplexityReduction.Protocol.TypedAutoReductionResult {name}_request := by",
                    f"  simpa [{name}_request] using",
                    "    ComplexityReduction.Protocol.TypedAutoReductionResult.proveInNP",
                    f"      policy (by rfl) {name}_membership",
                    "",
                ]
            )
            audited.extend(
                [
                    f"Benchmark.Hardness.TypedAuthoring.Final.{name}_membership",
                    f"Benchmark.Hardness.TypedAuthoring.Final.{name}_result",
                ]
            )
        elif case.objective == "prove_np_complete":
            if not case.membership_declaration:
                raise ValueError(f"{case.case_id} has no selected native membership")
            if not case.hub_declaration or not case.completeness_declaration:
                raise ValueError(f"{case.case_id} has no selected completeness hub")
            body.extend(
                [
                    f"noncomputable def {name}_path :",
                    "    ComplexityReduction.Certificate.CertifiedPath",
                    f"      {case.hub_declaration} {case.source_declaration} :=",
                    f"  {_path_term(case.hub_declaration, case.route_atoms)}",
                    "",
                    f"theorem {name}_membership :",
                    f"    ComplexityReduction.Certificate.NativeTMInNP {case.source_declaration} :=",
                    f"  {case.membership_declaration}",
                    "",
                    f"noncomputable def {name}_completeness :",
                    f"    ComplexityReduction.Certificate.NativeTMNPComplete {case.source_declaration} :=",
                    "  ComplexityReduction.Certificate.CompletenessTransport.alongPath",
                    f"    {case.completeness_declaration}",
                    f"    {name}_path",
                    f"    {name}_membership",
                    "",
                    f"def {name}_request : ComplexityReduction.Protocol.TypedAutoReductionRequest where",
                    f"  source := .fromPresented {case.source_declaration}",
                    "  policy := policy",
                    f"  objective := .proveNPComplete {case.source_declaration}",
                    "",
                    "@[complexity_reduction_ir_typed_final_result]",
                    f"noncomputable def {name}_result :",
                    f"    ComplexityReduction.Protocol.TypedAutoReductionResult {name}_request := by",
                    f"  simpa [{name}_request] using",
                    "    ComplexityReduction.Protocol.TypedAutoReductionResult.proveNPComplete",
                    f"      policy (by rfl) {name}_completeness",
                    "",
                ]
            )
            audited.extend(
                [
                    f"Benchmark.Hardness.TypedAuthoring.Final.{name}_path",
                    f"Benchmark.Hardness.TypedAuthoring.Final.{name}_membership",
                    f"Benchmark.Hardness.TypedAuthoring.Final.{name}_completeness",
                    f"Benchmark.Hardness.TypedAuthoring.Final.{name}_result",
                ]
            )
        else:
            raise ValueError(f"unsupported typed-authoring objective: {case.objective}")
    body.extend(
        [
            "end",
            "",
            "end Benchmark.Hardness.TypedAuthoring.Final",
            "",
            "assert_standard_axioms",
            "  " + ",\n  ".join(audited),
            "",
        ]
    )
    return "\n".join(body)


def typed_authoring_report_skeleton(*, suite_file: Path, output_root: Path) -> dict[str, Any]:
    return {
        "schema_version": TYPED_AUTHORING_REPORT_SCHEMA,
        "stage": "M",
        "suite_file": str(suite_file.resolve()),
        "output_root": str(output_root.resolve()),
        "published": False,
        "status": "RUNNING",
        "cases": [],
        "process_counts": {
            "core_baseline": 0,
            "authoring_local": 0,
            "final_combined_lean": 0,
            "release_replay": 0,
        },
    }
