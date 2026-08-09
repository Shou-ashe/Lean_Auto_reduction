"""Lean-bound packet index and compiler for Stage-M optional authoring."""

from __future__ import annotations

from dataclasses import asdict, dataclass, replace
from pathlib import Path
from typing import Any, Iterable

from .certificate_dag import CertificateDAG, CertificateDAGValidationError
from .finite_witness import missing_combinators
from .lean_runner import module_file, sha256_file
from .models import ExactAuthoringTemplateCandidate, ProbeResult, sha256_id


PACKET_SCHEMA = "hardness_capability_packet_v1"
PACKET_INDEX_SCHEMA = "hardness_packet_index_v1"
PACKET_KINDS = {
    "route_packet",
    "gadget_packet",
    "membership_packet",
    "tm_certificate_packet",
}
ORACLE_MARKERS = (".Oracles.", ".Gold.", ".GoldProofs.", ".HiddenTargets.", ".Legacy.")
FORBIDDEN_AXIOMS = {"Classical.choice", "propext", "Quot.sound", "admit", "sorryAx"}


class PacketValidationError(ValueError):
    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


@dataclass(frozen=True)
class CapabilityPacket:
    packet_kind: str
    source_declaration: str
    target_declaration: str
    direction: str
    capability_head: str
    candidate_id: str
    template_kind: str
    provider_declaration: str
    component_declarations: tuple[str, ...]
    required_combinators: tuple[str, ...]
    allowed_imports: tuple[str, ...]
    declared_axioms: tuple[str, ...]
    candidate_source_hash: str
    producer: str
    schema_version: str = PACKET_SCHEMA

    @property
    def packet_id(self) -> str:
        return sha256_id({"schema_version": self.schema_version, **asdict(self)})

    def to_dict(self) -> dict[str, object]:
        value = asdict(self)
        value["packet_id"] = self.packet_id
        return value


@dataclass(frozen=True)
class PacketIndex:
    dag_id: str
    registry_fingerprint: str
    packets: tuple[CapabilityPacket, ...]
    producer: str = "stage_m_packet_index_builder"
    schema_version: str = PACKET_INDEX_SCHEMA

    @property
    def index_id(self) -> str:
        return sha256_id(
            {
                "schema_version": self.schema_version,
                "dag_id": self.dag_id,
                "registry_fingerprint": self.registry_fingerprint,
                "packet_ids": [packet.packet_id for packet in self.packets],
                "producer": self.producer,
            }
        )

    def packet(self, packet_id: str) -> CapabilityPacket:
        for packet in self.packets:
            if packet.packet_id == packet_id:
                return packet
        raise PacketValidationError("unknown_packet", "selected packet is absent from the index")

    def to_dict(self) -> dict[str, object]:
        return {
            "schema_version": self.schema_version,
            "index_id": self.index_id,
            "dag_id": self.dag_id,
            "registry_fingerprint": self.registry_fingerprint,
            "producer": self.producer,
            "packets": [packet.to_dict() for packet in self.packets],
        }


TEMPLATE_PACKET_KIND = {
    "lawful_presentation": "gadget_packet",
    "primitive_admission": "gadget_packet",
    "program_indexed_model": "gadget_packet",
    "program_indexed_reduction": "tm_certificate_packet",
    "native_membership": "membership_packet",
}


def _provider_source_hash(root: Path, provider_declaration: str) -> str:
    module = provider_declaration.rsplit(".", 1)[0]
    path = module_file(root / "Lean", module)
    return f"sha256:{sha256_file(path)}"


def candidate_set_source_hash(
    *, root: Path, probe: ProbeResult, allowed_packet_kinds: Iterable[str]
) -> str:
    allowed = set(allowed_packet_kinds)
    hashes = sorted(
        {
            _provider_source_hash(root, candidate.provider_declaration)
            for candidate in probe.authoring_templates
            if TEMPLATE_PACKET_KIND.get(candidate.template_kind) in allowed
        }
    )
    if not hashes:
        return "none"
    return sha256_id(
        {
            "schema_version": "hardness_packet_candidate_source_set_v1",
            "source_hashes": hashes,
        }
    )


def _template_packet(
    *,
    root: Path,
    candidate: ExactAuthoringTemplateCandidate,
    required_combinators: tuple[str, ...],
) -> CapabilityPacket:
    try:
        kind = TEMPLATE_PACKET_KIND[candidate.template_kind]
    except KeyError as error:
        raise PacketValidationError(
            "unsupported_template", f"unsupported template kind {candidate.template_kind}"
        ) from error
    return CapabilityPacket(
        packet_kind=kind,
        source_declaration=candidate.source_declaration,
        target_declaration=candidate.target_declaration,
        direction=(
            "identity"
            if candidate.source_declaration == candidate.target_declaration
            else "source_to_target"
        ),
        capability_head=(
            "ComplexityReduction.Encoding.StructuralRepresentationCertificate"
            if candidate.template_kind == "lawful_presentation"
            else (
                "ComplexityReduction.Certificate.NativeTMInNP"
                if candidate.template_kind == "native_membership"
                else "ComplexityReduction.Certificate.CertifiedReduction"
            )
        ),
        candidate_id=candidate.candidate_id,
        template_kind=candidate.template_kind,
        provider_declaration=candidate.provider_declaration,
        component_declarations=candidate.component_declarations,
        required_combinators=(
            required_combinators if candidate.template_kind == "native_membership" else ()
        ),
        allowed_imports=(candidate.provider_declaration.rsplit(".", 1)[0],),
        declared_axioms=(),
        candidate_source_hash=_provider_source_hash(root, candidate.provider_declaration),
        producer=candidate.producer,
    )


def build_packet_index(
    *,
    root: Path,
    dag: CertificateDAG,
    probe: ProbeResult,
    allowed_packet_kinds: Iterable[str],
    required_combinators: Iterable[str],
) -> PacketIndex:
    allowed = tuple(allowed_packet_kinds)
    if not set(allowed).issubset(PACKET_KINDS):
        raise PacketValidationError("unsupported_packet_kind", "request contains an unknown packet kind")
    required = tuple(required_combinators)
    packets = tuple(
        packet
        for packet in (
            _template_packet(root=root, candidate=candidate, required_combinators=required)
            for candidate in probe.authoring_templates
        )
        if packet.packet_kind in allowed
    )
    index = PacketIndex(
        dag_id=dag.dag_id,
        registry_fingerprint=probe.registry_fingerprint,
        packets=tuple(sorted(packets, key=lambda packet: packet.packet_id)),
    )
    for packet in index.packets:
        validate_packet(packet, dag=dag)
    return index


def validate_packet(packet: CapabilityPacket, *, dag: CertificateDAG) -> None:
    if packet.schema_version != PACKET_SCHEMA or packet.packet_kind not in PACKET_KINDS:
        raise PacketValidationError("unsupported_packet_kind", "packet kind or schema is unsupported")
    active = dag.node(dag.active_node)
    if (
        packet.source_declaration != active.input_type
        or packet.target_declaration != active.output_type
    ):
        raise PacketValidationError(
            "endpoint_mismatch", "packet endpoints do not equal the active certificate node"
        )
    if packet.direction != active.direction:
        raise PacketValidationError("wrong_direction", "packet direction does not match the request")
    if packet.capability_head != active.capability_head:
        raise PacketValidationError(
            "wrong_capability_head", "packet capability head does not match the active node"
        )
    if any(marker in value for value in packet.allowed_imports for marker in ORACLE_MARKERS):
        raise PacketValidationError(
            "oracle_import_forbidden", "packet import allowlist references quarantined data"
        )
    if set(packet.declared_axioms) & FORBIDDEN_AXIOMS or packet.declared_axioms:
        raise PacketValidationError(
            "nonstandard_axiom_forbidden", "packet declares an untrusted or nonstandard axiom"
        )
    missing = missing_combinators(packet.required_combinators)
    if missing:
        raise PacketValidationError(
            f"missing_checker_combinator:{missing[0]}",
            f"packet requires unavailable checker combinator {missing[0]}",
        )


def adversarial_packet(packet: CapabilityPacket, mutation: str) -> CapabilityPacket:
    if mutation == "endpoint_mismatch":
        return replace(packet, target_declaration=packet.source_declaration)
    if mutation == "wrong_direction":
        return replace(
            packet,
            direction="identity" if packet.direction == "source_to_target" else "source_to_target",
        )
    if mutation == "oracle_import_forbidden":
        return replace(
            packet,
            allowed_imports=(*packet.allowed_imports, "Benchmark.Hardness.Oracles.Gold.Answer"),
        )
    if mutation == "nonstandard_axiom_forbidden":
        return replace(packet, declared_axioms=("StageM.untrustedAxiom",))
    raise ValueError(f"unsupported adversarial packet mutation: {mutation}")


@dataclass(frozen=True)
class CompiledPacketSelection:
    packet_id: str
    candidate_id: str
    template_kind: str
    packet_kind: str
    active_node_id: str
    compiler_insertions: tuple[str, ...]

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def compile_packet_selection(
    *, dag: CertificateDAG, index: PacketIndex, packet_id: str
) -> CompiledPacketSelection:
    if index.dag_id != dag.dag_id:
        raise PacketValidationError("stale_packet_index", "packet index belongs to another DAG")
    packet = index.packet(packet_id)
    validate_packet(packet, dag=dag)
    insertions = (
        "exact_endpoint_coercion",
        "canonical_candidate_bundle_shell",
        "fresh_registry_revalidation",
        "final_request_constructor",
    )
    if packet.packet_kind == "route_packet":
        insertions = ("certified_path_trans", *insertions)
    elif packet.packet_kind == "membership_packet":
        insertions = ("native_membership_shell", *insertions)
    elif packet.packet_kind == "tm_certificate_packet":
        insertions = ("program_indexed_reduction_shell", *insertions)
    else:
        insertions = ("typed_gadget_shell", *insertions)
    return CompiledPacketSelection(
        packet_id=packet.packet_id,
        candidate_id=packet.candidate_id,
        template_kind=packet.template_kind,
        packet_kind=packet.packet_kind,
        active_node_id=dag.node(dag.active_node).node_id,
        compiler_insertions=insertions,
    )


def candidate_bundle_integrity(
    paths: Iterable[Path], expected_sha256: Iterable[str]
) -> bool:
    path_values = tuple(paths)
    expected_values = tuple(expected_sha256)
    if len(path_values) != len(expected_values) or not path_values:
        return False
    return all(
        path.is_file() and sha256_file(path) == expected
        for path, expected in zip(path_values, expected_values, strict=True)
    )
