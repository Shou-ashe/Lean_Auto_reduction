"""Immutable run-local publication for Stage P authored capabilities."""

from __future__ import annotations

import json
import os
import re
import shutil
from contextlib import contextmanager
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Iterator

from .lean_runner import (
    ORACLE_SOURCE_MARKERS,
    assert_generated_source_is_safe,
    validate_declaration_name,
    validate_module_name,
)
from .models import sha256_id
from .stage_p_contract import (
    CAPABILITY_HEADS,
    SHA256_RE,
    STAGE_P_PUBLICATION_SCHEMA,
    StagePContractError,
)
from .stage_p_runtime import StagePGapCheckpoint


STAGE_P_PUBLISHED_CATALOG_SCHEMA = "hardness_stage_p_published_catalog_v1"
STAGE_P_PROVENANCE_KINDS = frozenset(
    {"model_generated", "deterministic_fixture", "existing_reuse"}
)
STAGE_P_PUBLICATION_ROLES = frozenset({"case_local", "producer"})
IMPORT_RE = re.compile(r"(?m)^\s*import\s+([A-Z][A-Za-z0-9_']*(?:\.[A-ZA-Za-z0-9_']+)*)\s*$")
EXTRA_UNSAFE_SOURCE_RE = re.compile(
    r"\b(?:unsafe|run_tac|include_str|include_bytes|unsafeCast|implemented_by)\b"
)


def _require_hash(value: str, *, label: str, code: str = "capability_publication_failed") -> None:
    if not isinstance(value, str) or not SHA256_RE.fullmatch(value):
        raise StagePContractError(code, f"{label} is not a content hash")


@dataclass(frozen=True)
class StagePPublicationManifest:
    run_id: str
    request_id: str
    gap_id: str
    gap_ordinal: int
    parent_checkpoint_hash: str
    checkpoint_prepublication_sha256: str
    toolchain: str
    lake_manifest_sha256: str
    base_registry_fingerprint: str
    publication_catalog_before_sha256: str
    input_source_sha256: str
    dependency_fingerprint: str
    dependency_sha256: tuple[str, ...]
    model_response_sha256: str
    patch_sha256: str
    candidate_source_sha256: str
    diagnostics_sha256: str
    bundle_sha256: str
    axiom_audit_sha256: str
    fresh_core_precheck_sha256: str
    candidate_module: str
    declaration: str
    exact_type_sha256: str
    capability_head: str
    source_endpoint_id: str
    target_endpoint_id: str
    direction: str
    allowed_imports: tuple[str, ...]
    provenance_kind: str
    compiler_inserted_math_token_count: int
    publication_role: str
    schema_version: str = STAGE_P_PUBLICATION_SCHEMA

    def validate(self) -> None:
        if self.schema_version != STAGE_P_PUBLICATION_SCHEMA:
            raise StagePContractError(
                "capability_publication_failed", "unsupported Stage P publication schema"
            )
        if not self.run_id.strip() or not self.toolchain.strip():
            raise StagePContractError(
                "capability_publication_failed", "publication run/toolchain identity is empty"
            )
        if isinstance(self.gap_ordinal, bool) or not 1 <= self.gap_ordinal <= 4:
            raise StagePContractError("gap_count_exceeded", "publication gap ordinal is invalid")
        for label, value in {
            "request_id": self.request_id,
            "gap_id": self.gap_id,
            "parent_checkpoint_hash": self.parent_checkpoint_hash,
            "checkpoint_prepublication_sha256": self.checkpoint_prepublication_sha256,
            "lake_manifest_sha256": self.lake_manifest_sha256,
            "base_registry_fingerprint": self.base_registry_fingerprint,
            "publication_catalog_before_sha256": self.publication_catalog_before_sha256,
            "input_source_sha256": self.input_source_sha256,
            "dependency_fingerprint": self.dependency_fingerprint,
            "model_response_sha256": self.model_response_sha256,
            "patch_sha256": self.patch_sha256,
            "candidate_source_sha256": self.candidate_source_sha256,
            "diagnostics_sha256": self.diagnostics_sha256,
            "bundle_sha256": self.bundle_sha256,
            "axiom_audit_sha256": self.axiom_audit_sha256,
            "fresh_core_precheck_sha256": self.fresh_core_precheck_sha256,
            "exact_type_sha256": self.exact_type_sha256,
            "source_endpoint_id": self.source_endpoint_id,
            "target_endpoint_id": self.target_endpoint_id,
            **{
                f"dependency_sha256[{index}]": dependency
                for index, dependency in enumerate(self.dependency_sha256)
            },
        }.items():
            _require_hash(value, label=label)
        if len(set(self.dependency_sha256)) != len(self.dependency_sha256):
            raise StagePContractError(
                "candidate_dependency_stale", "publication dependencies contain duplicates"
            )
        if not self.dependency_sha256:
            raise StagePContractError(
                "candidate_dependency_stale", "publication dependency list is empty"
            )
        try:
            validate_module_name(self.candidate_module)
            validate_declaration_name(self.declaration, label="published declaration")
            for module in self.allowed_imports:
                validate_module_name(module)
        except ValueError as error:
            raise StagePContractError("capability_publication_failed", str(error)) from error
        if len(set(self.allowed_imports)) != len(self.allowed_imports):
            raise StagePContractError(
                "import_not_allowlisted", "publication import allowlist contains duplicates"
            )
        if self.capability_head not in CAPABILITY_HEADS:
            raise StagePContractError(
                "candidate_canonical_head_mismatch", "published capability head is unsupported"
            )
        if self.direction != "source_to_target":
            raise StagePContractError(
                "candidate_wrong_direction", "published capability direction is not exact"
            )
        if self.provenance_kind not in STAGE_P_PROVENANCE_KINDS:
            raise StagePContractError(
                "capability_publication_failed", "publication provenance kind is unsupported"
            )
        if self.publication_role not in STAGE_P_PUBLICATION_ROLES:
            raise StagePContractError(
                "capability_publication_failed", "publication role is unsupported"
            )
        if self.compiler_inserted_math_token_count != 0:
            raise StagePContractError(
                "compiler_math_insertion_detected", "publication contains compiler-authored math"
            )

    @property
    def capability_hash(self) -> str:
        self.validate()
        return sha256_id({"schema_version": self.schema_version, **asdict(self)})

    def assert_matches_checkpoint(self, checkpoint: StagePGapCheckpoint) -> None:
        checkpoint.validate()
        if checkpoint.publication_hash is not None:
            raise StagePContractError(
                "capability_publication_failed", "checkpoint was already published"
            )
        exact_bindings = {
            "request_id": checkpoint.request_id,
            "gap_id": checkpoint.gap_id,
            "gap_ordinal": checkpoint.ordinal,
            "parent_checkpoint_hash": checkpoint.parent_checkpoint_hash,
            "checkpoint_prepublication_sha256": checkpoint.checkpoint_hash,
            "base_registry_fingerprint": checkpoint.registry_fingerprint,
            "dependency_fingerprint": checkpoint.dependency_hash,
            "model_response_sha256": checkpoint.model_response_sha256,
            "patch_sha256": checkpoint.patch_sha256,
            "candidate_source_sha256": checkpoint.candidate_source_sha256,
            "diagnostics_sha256": checkpoint.diagnostics_sha256,
            "bundle_sha256": checkpoint.bundle_sha256,
            "axiom_audit_sha256": checkpoint.axiom_audit_sha256,
        }
        actual = {
            "request_id": self.request_id,
            "gap_id": self.gap_id,
            "gap_ordinal": self.gap_ordinal,
            "parent_checkpoint_hash": self.parent_checkpoint_hash,
            "checkpoint_prepublication_sha256": self.checkpoint_prepublication_sha256,
            "base_registry_fingerprint": self.base_registry_fingerprint,
            "dependency_fingerprint": self.dependency_fingerprint,
            "model_response_sha256": self.model_response_sha256,
            "patch_sha256": self.patch_sha256,
            "candidate_source_sha256": self.candidate_source_sha256,
            "diagnostics_sha256": self.diagnostics_sha256,
            "bundle_sha256": self.bundle_sha256,
            "axiom_audit_sha256": self.axiom_audit_sha256,
        }
        if actual != exact_bindings:
            raise StagePContractError(
                "candidate_dependency_stale",
                "publication manifest differs from the validated gap checkpoint",
            )


@dataclass(frozen=True)
class StagePPublishedCapability:
    capability_hash: str
    pack_root: Path
    source_file: Path
    manifest_file: Path
    manifest: StagePPublicationManifest

    def public_view(self) -> dict[str, Any]:
        return {
            "capability_hash": self.capability_hash,
            "request_id": self.manifest.request_id,
            "gap_id": self.manifest.gap_id,
            "gap_ordinal": self.manifest.gap_ordinal,
            "module": self.manifest.candidate_module,
            "declaration": self.manifest.declaration,
            "capability_head": self.manifest.capability_head,
            "source_endpoint_id": self.manifest.source_endpoint_id,
            "target_endpoint_id": self.manifest.target_endpoint_id,
            "direction": self.manifest.direction,
            "candidate_source_sha256": self.manifest.candidate_source_sha256,
            "dependency_sha256": list(self.manifest.dependency_sha256),
            "axiom_audit_sha256": self.manifest.axiom_audit_sha256,
            "provenance_kind": self.manifest.provenance_kind,
            "publication_role": self.manifest.publication_role,
        }


@dataclass
class StagePPromotionWaveBarrier:
    active_jobs: dict[str, str] = field(default_factory=dict)
    producer_wave_sealed: bool = False
    events: list[dict[str, Any]] = field(default_factory=list)

    def start(self, *, job_id: str, wave: str) -> None:
        if not job_id or job_id in self.active_jobs:
            raise StagePContractError(
                "capability_publication_failed", "promotion job identity is empty or active"
            )
        if wave not in {"producer", "consumer", "independent"}:
            raise StagePContractError("capability_publication_failed", "unknown promotion wave")
        if wave == "producer" and self.producer_wave_sealed:
            raise StagePContractError(
                "capability_publication_failed", "producer wave has already been sealed"
            )
        if wave == "consumer" and (not self.producer_wave_sealed or self.active_jobs):
            raise StagePContractError(
                "published_capability_not_visible",
                "consumer started before the producer wave reached an empty sealed barrier",
            )
        self.active_jobs[job_id] = wave
        self.events.append({"event": "start", "job_id": job_id, "wave": wave})

    def finish(self, *, job_id: str) -> None:
        try:
            wave = self.active_jobs.pop(job_id)
        except KeyError as error:
            raise StagePContractError(
                "capability_publication_failed", "promotion job is not active"
            ) from error
        self.events.append({"event": "finish", "job_id": job_id, "wave": wave})

    def seal_producer_wave(self) -> None:
        if self.active_jobs:
            raise StagePContractError(
                "capability_publication_failed", "producer wave cannot seal with active jobs"
            )
        if self.producer_wave_sealed:
            raise StagePContractError(
                "capability_publication_failed", "producer wave was sealed twice"
            )
        self.producer_wave_sealed = True
        self.events.append({"event": "seal", "wave": "producer", "active_job_count": 0})

    @contextmanager
    def job(self, *, job_id: str, wave: str) -> Iterator[None]:
        self.start(job_id=job_id, wave=wave)
        try:
            yield
        finally:
            self.finish(job_id=job_id)

    @staticmethod
    def assert_consumer_zero_authoring(*, model_calls: int, authoring_attempts: int) -> None:
        if model_calls != 0 or authoring_attempts != 0:
            raise StagePContractError(
                "consumer_authoring_forbidden", "consumer attempted model authoring"
            )

    def to_dict(self) -> dict[str, Any]:
        return {
            "active_jobs": dict(sorted(self.active_jobs.items())),
            "producer_wave_sealed": self.producer_wave_sealed,
            "events": list(self.events),
        }


class StagePRunLocalPublishedRegistry:
    """Content-addressed publication catalog scoped to one full Stage P run."""

    def __init__(self, root: Path, *, run_id: str, base_registry_fingerprint: str):
        if not run_id.strip():
            raise ValueError("run_id must be non-empty")
        _require_hash(base_registry_fingerprint, label="base_registry_fingerprint")
        self.root = root.resolve()
        self.run_id = run_id
        self.base_registry_fingerprint = base_registry_fingerprint
        self.root.mkdir(parents=True, exist_ok=False)
        self._published: dict[str, StagePPublishedCapability] = {}
        self._published_gap_ids: set[str] = set()
        self._unpublished_candidate_hashes: set[str] = set()

    @property
    def catalog_fingerprint(self) -> str:
        payload = {
            "schema_version": STAGE_P_PUBLISHED_CATALOG_SCHEMA,
            "run_id": self.run_id,
            "base_registry_fingerprint": self.base_registry_fingerprint,
            "entries": [
                capability.public_view()
                for _, capability in sorted(self._published.items())
            ],
        }
        return sha256_id(payload)

    def register_job_local_candidate(self, candidate_source_sha256: str) -> None:
        _require_hash(candidate_source_sha256, label="candidate_source_sha256")
        self._unpublished_candidate_hashes.add(candidate_source_sha256)

    def assert_unpublished_isolation(self, candidate_source_sha256: str) -> None:
        if candidate_source_sha256 not in self._unpublished_candidate_hashes:
            raise StagePContractError(
                "published_capability_not_visible", "unknown job-local candidate entered audit"
            )
        if any(
            capability.manifest.candidate_source_sha256 == candidate_source_sha256
            for capability in self._published.values()
        ):
            raise StagePContractError(
                "published_capability_not_visible",
                "job-local candidate became visible without explicit publication",
            )

    def _audit_source(self, *, manifest: StagePPublicationManifest, source_text: str) -> None:
        if sha256_id(source_text) != manifest.candidate_source_sha256:
            raise StagePContractError(
                "capability_publication_failed", "candidate source differs from manifest hash"
            )
        if EXTRA_UNSAFE_SOURCE_RE.search(source_text):
            raise StagePContractError(
                "sorry_axiom_or_unsafe_candidate", "candidate source contains an unsafe token"
            )
        if any(marker in source_text for marker in ORACLE_SOURCE_MARKERS):
            raise StagePContractError(
                "oracle_or_gold_import", "candidate source imports quarantined data"
            )
        try:
            assert_generated_source_is_safe(source_text)
        except ValueError as error:
            message = str(error)
            code = (
                "oracle_or_gold_import"
                if "quarantined" in message
                else "sorry_axiom_or_unsafe_candidate"
            )
            raise StagePContractError(code, message) from error
        imported = set(IMPORT_RE.findall(source_text))
        declared_import_lines = sum(
            1 for line in source_text.splitlines() if line.lstrip().startswith("import ")
        )
        if declared_import_lines != len(imported):
            raise StagePContractError("import_not_allowlisted", "candidate has a malformed import")
        if not imported.issubset(manifest.allowed_imports):
            raise StagePContractError("import_not_allowlisted", "candidate imports an unlisted module")

    def publish(
        self,
        *,
        manifest: StagePPublicationManifest,
        checkpoint: StagePGapCheckpoint,
        candidate_source: Path,
    ) -> StagePPublishedCapability:
        manifest.validate()
        manifest.assert_matches_checkpoint(checkpoint)
        if manifest.run_id != self.run_id:
            raise StagePContractError(
                "capability_publication_failed", "manifest belongs to another full run"
            )
        if manifest.publication_catalog_before_sha256 != self.catalog_fingerprint:
            raise StagePContractError(
                "candidate_dependency_stale", "publication catalog changed before commit"
            )
        if manifest.gap_id in self._published_gap_ids:
            raise StagePContractError(
                "capability_publication_failed", "gap was already published"
            )
        source_path = candidate_source.resolve()
        if not source_path.is_file():
            raise StagePContractError("capability_publication_failed", "candidate source is missing")
        source_text = source_path.read_text(encoding="utf-8")
        self._audit_source(manifest=manifest, source_text=source_text)
        capability_hash = manifest.capability_hash
        if capability_hash in self._published:
            raise StagePContractError(
                "capability_publication_failed", "capability hash was already published"
            )
        digest = capability_hash.removeprefix("sha256:")
        pack_root = self.root / digest
        temporary_root = self.root / f".{digest}.tmp"
        if pack_root.exists() or temporary_root.exists():
            raise StagePContractError(
                "capability_publication_failed", "publication destination already exists"
            )
        try:
            source_root = temporary_root / "src"
            destination = source_root / Path(*manifest.candidate_module.split(".")).with_suffix(
                ".lean"
            )
            destination.parent.mkdir(parents=True, exist_ok=False)
            shutil.copy2(source_path, destination)
            manifest_file = temporary_root / "manifest.json"
            manifest_payload = {
                **asdict(manifest),
                "dependency_sha256": list(manifest.dependency_sha256),
                "allowed_imports": list(manifest.allowed_imports),
                "capability_hash": capability_hash,
                "source_relative_path": str(destination.relative_to(temporary_root)),
            }
            manifest_file.write_text(
                json.dumps(manifest_payload, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            for path in (destination, manifest_file):
                path.chmod(0o444)
            for directory in reversed((destination.parent, source_root, temporary_root)):
                directory.chmod(0o555)
            os.replace(temporary_root, pack_root)
        except Exception:
            if temporary_root.exists():
                shutil.rmtree(temporary_root, ignore_errors=True)
            raise
        published = StagePPublishedCapability(
            capability_hash=capability_hash,
            pack_root=pack_root,
            source_file=pack_root
            / "src"
            / Path(*manifest.candidate_module.split(".")).with_suffix(".lean"),
            manifest_file=pack_root / "manifest.json",
            manifest=manifest,
        )
        self._published[capability_hash] = published
        self._published_gap_ids.add(manifest.gap_id)
        self._unpublished_candidate_hashes.discard(manifest.candidate_source_sha256)
        return published

    def _assert_intact(self, capability: StagePPublishedCapability) -> None:
        if not capability.source_file.is_file() or not capability.manifest_file.is_file():
            raise StagePContractError(
                "published_capability_not_visible", "published pack is missing from disk"
            )
        source_text = capability.source_file.read_text(encoding="utf-8")
        self._audit_source(manifest=capability.manifest, source_text=source_text)
        payload = json.loads(capability.manifest_file.read_text(encoding="utf-8"))
        if payload.get("capability_hash") != capability.capability_hash:
            raise StagePContractError(
                "published_capability_not_visible", "published manifest no longer matches catalog"
            )

    def capability(self, capability_hash: str) -> StagePPublishedCapability:
        try:
            capability = self._published[capability_hash]
        except KeyError as error:
            raise StagePContractError(
                "published_capability_not_visible", "capability is absent from the run-local catalog"
            ) from error
        self._assert_intact(capability)
        return capability

    def catalog_snapshot(self, *, excluded: frozenset[str] = frozenset()) -> dict[str, Any]:
        entries: list[dict[str, Any]] = []
        for capability_hash, capability in sorted(self._published.items()):
            if capability_hash in excluded:
                continue
            self._assert_intact(capability)
            entries.append(capability.public_view())
        payload = {
            "schema_version": STAGE_P_PUBLISHED_CATALOG_SCHEMA,
            "run_id": self.run_id,
            "base_registry_fingerprint": self.base_registry_fingerprint,
            "entries": entries,
        }
        return {**payload, "catalog_fingerprint": sha256_id(payload)}

    def require_visible(self, capability_hash: str) -> StagePPublishedCapability:
        capability = self.capability(capability_hash)
        visible = {
            entry["capability_hash"] for entry in self.catalog_snapshot()["entries"]
        }
        if capability_hash not in visible:
            raise StagePContractError(
                "published_capability_not_visible", "capability is not visible to the consumer"
            )
        return capability

    def to_dict(self) -> dict[str, Any]:
        snapshot = self.catalog_snapshot()
        provenance_counts = {
            kind: sum(entry["provenance_kind"] == kind for entry in snapshot["entries"])
            for kind in sorted(STAGE_P_PROVENANCE_KINDS)
        }
        return {
            "root": str(self.root),
            "run_id": self.run_id,
            "published_count": len(self._published),
            "unpublished_candidate_count": len(self._unpublished_candidate_hashes),
            "provenance_counts": provenance_counts,
            "catalog": snapshot,
        }
