"""Versioned certificate DAG for fail-closed Stage-M optional authoring."""

from __future__ import annotations

from dataclasses import asdict, dataclass, replace
from typing import Iterable

from .models import sha256_id


CERTIFICATE_DAG_SCHEMA = "hardness_certificate_dag_v2"
CERTIFICATE_NODE_SCHEMA = "hardness_certificate_node_v2"
NODE_KINDS = (
    "problem_match",
    "presentation_capability",
    "reduction_capability",
    "membership_capability",
    "completeness_transport",
    "final_request",
)
NODE_STATUSES = {"verified", "pending", "blocked", "rejected", "not_required"}
DIRECTIONS = {"identity", "source_to_target"}


class CertificateDAGValidationError(ValueError):
    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


@dataclass(frozen=True)
class CertificateNode:
    kind: str
    input_type: str
    output_type: str
    direction: str
    capability_head: str
    preconditions: tuple[str, ...]
    producer: str
    candidate_source_hash: str
    verification_status: str
    schema_version: str = CERTIFICATE_NODE_SCHEMA

    @property
    def dependency_hash(self) -> str:
        return sha256_id(
            {
                "schema_version": self.schema_version,
                "preconditions": list(self.preconditions),
            }
        )

    @property
    def node_id(self) -> str:
        return sha256_id(
            {
                "schema_version": self.schema_version,
                "kind": self.kind,
                "input_type": self.input_type,
                "output_type": self.output_type,
                "direction": self.direction,
                "capability_head": self.capability_head,
                "dependency_hash": self.dependency_hash,
                "producer": self.producer,
                "candidate_source_hash": self.candidate_source_hash,
                "verification_status": self.verification_status,
            }
        )

    def to_dict(self) -> dict[str, object]:
        value = asdict(self)
        value["dependency_hash"] = self.dependency_hash
        value["node_id"] = self.node_id
        return value


@dataclass(frozen=True)
class CertificateDAG:
    source_declaration: str
    target_declaration: str
    objective: str
    active_node: str
    nodes: tuple[CertificateNode, ...]
    producer: str = "stage_m_certificate_dag_builder"
    schema_version: str = CERTIFICATE_DAG_SCHEMA

    @property
    def dag_id(self) -> str:
        return sha256_id(
            {
                "schema_version": self.schema_version,
                "source_declaration": self.source_declaration,
                "target_declaration": self.target_declaration,
                "objective": self.objective,
                "active_node": self.active_node,
                "node_ids": [node.node_id for node in self.nodes],
                "producer": self.producer,
            }
        )

    def to_dict(self) -> dict[str, object]:
        return {
            "schema_version": self.schema_version,
            "dag_id": self.dag_id,
            "source_declaration": self.source_declaration,
            "target_declaration": self.target_declaration,
            "objective": self.objective,
            "active_node": self.active_node,
            "producer": self.producer,
            "nodes": [node.to_dict() for node in self.nodes],
        }

    def node(self, kind: str) -> CertificateNode:
        for node in self.nodes:
            if node.kind == kind:
                return node
        raise KeyError(kind)


HEADS = {
    "problem_match": "ComplexityReduction.Encoding.PresentedProblem",
    "presentation_capability": (
        "ComplexityReduction.Encoding.StructuralRepresentationCertificate"
    ),
    "reduction_capability": "ComplexityReduction.Certificate.CertifiedReduction",
    "membership_capability": "ComplexityReduction.Certificate.NativeTMInNP",
    "completeness_transport": "ComplexityReduction.Certificate.NativeTMNPComplete",
    "final_request": "ComplexityReduction.Protocol.TypedAutoReductionResult",
}


def _node(
    *,
    kind: str,
    input_type: str,
    output_type: str,
    direction: str,
    preconditions: Iterable[str],
    status: str,
    candidate_source_hash: str = "none",
    producer: str = "stage_m_certificate_dag_builder",
) -> CertificateNode:
    return CertificateNode(
        kind=kind,
        input_type=input_type,
        output_type=output_type,
        direction=direction,
        capability_head=HEADS[kind],
        preconditions=tuple(preconditions),
        producer=producer,
        candidate_source_hash=candidate_source_hash,
        verification_status=status,
    )


def build_certificate_dag(
    *,
    source_declaration: str,
    target_declaration: str | None,
    objective: str,
    active_node: str,
    candidate_source_hash: str,
) -> CertificateDAG:
    target = target_declaration or source_declaration
    nodes: list[CertificateNode] = []
    problem = _node(
        kind="problem_match",
        input_type=source_declaration,
        output_type=source_declaration,
        direction="identity",
        preconditions=(),
        status="verified",
        producer="lean_input_gate",
    )
    nodes.append(problem)
    presentation = _node(
        kind="presentation_capability",
        input_type=source_declaration,
        output_type=(target if active_node == "presentation_capability" else source_declaration),
        direction=("source_to_target" if active_node == "presentation_capability" else "identity"),
        preconditions=(problem.node_id,),
        status="pending" if active_node == "presentation_capability" else "verified",
        candidate_source_hash=(
            candidate_source_hash if active_node == "presentation_capability" else "none"
        ),
        producer=(
            "lean_exact_authoring_template_matcher"
            if active_node == "presentation_capability"
            else "lean_input_gate"
        ),
    )
    nodes.append(presentation)
    reduction = _node(
        kind="reduction_capability",
        input_type=source_declaration,
        output_type=target if objective == "reduce_to" else source_declaration,
        direction="source_to_target" if objective == "reduce_to" else "identity",
        preconditions=(problem.node_id, presentation.node_id),
        status="pending" if active_node == "reduction_capability" else "not_required",
        candidate_source_hash=(
            candidate_source_hash if active_node == "reduction_capability" else "none"
        ),
        producer="lean_exact_authoring_template_matcher",
    )
    nodes.append(reduction)
    membership_endpoint = source_declaration if objective == "prove_in_np" else target
    membership = _node(
        kind="membership_capability",
        input_type=membership_endpoint,
        output_type=membership_endpoint,
        direction="identity",
        preconditions=(problem.node_id, presentation.node_id),
        status="pending" if active_node == "membership_capability" else "not_required",
        candidate_source_hash=(
            candidate_source_hash if active_node == "membership_capability" else "none"
        ),
        producer="lean_exact_authoring_template_matcher",
    )
    nodes.append(membership)
    completeness = _node(
        kind="completeness_transport",
        input_type=target,
        output_type=target,
        direction="identity",
        preconditions=(),
        status="not_required",
    )
    nodes.append(completeness)
    active = next(node for node in nodes if node.kind == active_node)
    final = _node(
        kind="final_request",
        input_type=source_declaration,
        output_type=target if objective == "reduce_to" else source_declaration,
        direction="source_to_target" if objective == "reduce_to" else "identity",
        preconditions=(active.node_id,),
        status="pending",
    )
    nodes.append(final)
    dag = CertificateDAG(
        source_declaration=source_declaration,
        target_declaration=target,
        objective=objective,
        active_node=active_node,
        nodes=tuple(nodes),
    )
    validate_certificate_dag(dag)
    return dag


def validate_certificate_dag(dag: CertificateDAG) -> None:
    if dag.schema_version != CERTIFICATE_DAG_SCHEMA:
        raise CertificateDAGValidationError("unsupported_schema", "unsupported DAG schema")
    if tuple(node.kind for node in dag.nodes) != NODE_KINDS:
        raise CertificateDAGValidationError(
            "invalid_node_set", "certificate DAG must contain the six canonical nodes in order"
        )
    by_id: dict[str, CertificateNode] = {}
    for node in dag.nodes:
        if node.direction not in DIRECTIONS:
            raise CertificateDAGValidationError("wrong_direction", f"{node.kind} direction is invalid")
        if node.verification_status not in NODE_STATUSES:
            raise CertificateDAGValidationError(
                "invalid_verification_status", f"{node.kind} has an invalid status"
            )
        if node.capability_head != HEADS[node.kind]:
            raise CertificateDAGValidationError(
                "wrong_capability_head", f"{node.kind} has the wrong capability head"
            )
        for dependency in node.preconditions:
            if dependency not in by_id:
                raise CertificateDAGValidationError(
                    "unmet_precondition", f"{node.kind} references an unknown or later dependency"
                )
        by_id[node.node_id] = node

    source = dag.source_declaration
    target = dag.target_declaration
    expected_endpoints = {
        "problem_match": (source, source, "identity"),
        "presentation_capability": (
            source,
            target if dag.active_node == "presentation_capability" else source,
            "source_to_target" if dag.active_node == "presentation_capability" else "identity",
        ),
        "reduction_capability": (
            source,
            target if dag.objective == "reduce_to" else source,
            "source_to_target" if dag.objective == "reduce_to" else "identity",
        ),
        "membership_capability": (
            source if dag.objective == "prove_in_np" else target,
            source if dag.objective == "prove_in_np" else target,
            "identity",
        ),
        "completeness_transport": (target, target, "identity"),
        "final_request": (
            source,
            target if dag.objective == "reduce_to" else source,
            "source_to_target" if dag.objective == "reduce_to" else "identity",
        ),
    }
    for node in dag.nodes:
        expected = expected_endpoints[node.kind]
        if (node.input_type, node.output_type) != expected[:2]:
            raise CertificateDAGValidationError(
                "endpoint_mismatch", f"{node.kind} does not preserve the exact request endpoints"
            )
        if node.direction != expected[2]:
            raise CertificateDAGValidationError(
                "wrong_direction", f"{node.kind} has the wrong endpoint direction"
            )

    if dag.active_node not in {
        "presentation_capability",
        "reduction_capability",
        "membership_capability",
    }:
        raise CertificateDAGValidationError("invalid_active_node", "active node is not authorable")
    active = dag.node(dag.active_node)
    if active.verification_status not in {"pending", "verified"}:
        raise CertificateDAGValidationError(
            "invalid_active_node", "the one authoring node must be pending or verified"
        )
    for dependency in active.preconditions:
        if by_id[dependency].verification_status != "verified":
            raise CertificateDAGValidationError(
                "unmet_precondition", "active authoring node has an unverified precondition"
            )
    final = dag.node("final_request")
    if final.preconditions != (active.node_id,):
        raise CertificateDAGValidationError(
            "final_request_bypass", "final request must depend only on the exact active capability"
        )
    if active.verification_status == "pending" and final.verification_status != "pending":
        raise CertificateDAGValidationError(
            "final_request_bypass", "an unresolved capability cannot yield a verified final request"
        )
    if active.verification_status == "verified" and final.verification_status != "verified":
        raise CertificateDAGValidationError(
            "final_request_incomplete", "a completed authoring DAG must verify its final request"
        )


def complete_certificate_dag(
    dag: CertificateDAG, *, candidate_source_hash: str
) -> CertificateDAG:
    active = dag.node(dag.active_node)
    nodes: list[CertificateNode] = []
    rewritten_ids: dict[str, str] = {}
    completed_active: CertificateNode | None = None
    for node in dag.nodes:
        rewritten_preconditions = tuple(
            rewritten_ids.get(dependency, dependency)
            for dependency in node.preconditions
        )
        if node.kind == dag.active_node:
            rewritten = replace(
                node,
                preconditions=rewritten_preconditions,
                candidate_source_hash=candidate_source_hash,
                verification_status="verified",
                producer="lean_candidate_bundle_validator",
            )
            completed_active = rewritten
        elif node.kind == "final_request":
            if completed_active is None:
                raise CertificateDAGValidationError(
                    "invalid_active_node", "final request precedes the active capability"
                )
            rewritten = replace(
                node,
                preconditions=(completed_active.node_id,),
                candidate_source_hash=candidate_source_hash,
                verification_status="verified",
                producer="stage_m_packet_compiler",
            )
        else:
            rewritten = replace(node, preconditions=rewritten_preconditions)
        nodes.append(rewritten)
        rewritten_ids[node.node_id] = rewritten.node_id
    completed = replace(dag, nodes=tuple(nodes))
    validate_certificate_dag(completed)
    return completed
