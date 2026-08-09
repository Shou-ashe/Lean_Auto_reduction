"""Run-local immutable capability promotion and ordered wave barriers."""

from __future__ import annotations

import json
import os
import re
import shutil
from contextlib import contextmanager
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Iterator, Mapping

from .lean_runner import BANNED_SOURCE_RE, ORACLE_SOURCE_MARKERS, sha256_file, validate_module_name
from .models import sha256_id
from .stage_o_contract import CapabilityPromotionManifest, StageOContractError


PUBLISHED_CATALOG_SCHEMA = "hardness_stage_o_published_catalog_v1"
LEAN_DECLARATION_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


@dataclass(frozen=True)
class PublishedCapability:
    capability_hash: str
    module: str
    declaration: str
    pack_root: Path
    source_file: Path
    manifest_file: Path
    manifest: CapabilityPromotionManifest

    def public_view(self) -> dict[str, Any]:
        return {
            "capability_hash": self.capability_hash,
            "module": self.module,
            "declaration": self.declaration,
            "source_endpoint_id": self.manifest.source_endpoint_id,
            "target_endpoint_id": self.manifest.target_endpoint_id,
            "direction": self.manifest.direction,
            "capability_head": self.manifest.capability_head,
            "source_sha256": self.manifest.source_sha256,
            "dependency_sha256": list(self.manifest.dependency_sha256),
            "axiom_audit_sha256": self.manifest.axiom_audit_sha256,
        }


@dataclass
class PromotionWaveBarrier:
    """Deterministic producer/consumer barrier independent of thread completion order."""

    current_wave: str = "producer"
    active_jobs: set[str] = field(default_factory=set)
    producer_wave_sealed: bool = False
    events: list[dict[str, Any]] = field(default_factory=list)

    def start(self, *, job_id: str, wave: str) -> None:
        if not job_id or job_id in self.active_jobs:
            raise StageOContractError("capability_promotion_failed", "job identity is empty or active")
        if wave not in {"producer", "consumer", "independent"}:
            raise StageOContractError("capability_promotion_failed", "unknown promotion wave")
        if wave == "consumer" and (not self.producer_wave_sealed or self.active_jobs):
            raise StageOContractError(
                "published_capability_not_visible",
                "consumer started before the producer wave reached an empty barrier",
            )
        if wave == "producer" and self.producer_wave_sealed:
            raise StageOContractError("capability_promotion_failed", "producer wave was already sealed")
        self.active_jobs.add(job_id)
        self.current_wave = wave
        self.events.append({"event": "start", "job_id": job_id, "wave": wave})

    def finish(self, *, job_id: str) -> None:
        if job_id not in self.active_jobs:
            raise StageOContractError("capability_promotion_failed", "finished job is not active")
        self.active_jobs.remove(job_id)
        self.events.append({"event": "finish", "job_id": job_id, "wave": self.current_wave})

    def seal_producer_wave(self) -> None:
        if self.active_jobs:
            raise StageOContractError(
                "capability_promotion_failed", "producer wave cannot seal with active jobs"
            )
        self.producer_wave_sealed = True
        self.current_wave = "barrier"
        self.events.append({"event": "seal", "wave": "producer", "active_job_count": 0})

    @contextmanager
    def job(self, *, job_id: str, wave: str) -> Iterator[None]:
        self.start(job_id=job_id, wave=wave)
        try:
            yield
        finally:
            self.finish(job_id=job_id)

    def to_dict(self) -> dict[str, Any]:
        return {
            "current_wave": self.current_wave,
            "active_jobs": sorted(self.active_jobs),
            "producer_wave_sealed": self.producer_wave_sealed,
            "events": list(self.events),
        }


class RunLocalPublishedRegistry:
    """Content-addressed, read-only registry scoped to one full benchmark run."""

    def __init__(self, root: Path, *, run_id: str):
        if not run_id:
            raise ValueError("run_id must be non-empty")
        self.root = root.resolve()
        self.run_id = run_id
        self.root.mkdir(parents=True, exist_ok=False)
        self._published: dict[str, PublishedCapability] = {}
        self._unpublished_candidate_hashes: set[str] = set()

    def register_job_local_candidate(self, candidate_hash: str) -> None:
        self._unpublished_candidate_hashes.add(candidate_hash)

    def assert_unpublished_isolation(self, candidate_hash: str) -> None:
        if candidate_hash not in self._unpublished_candidate_hashes:
            raise StageOContractError(
                "unpublished_candidate_visible", "unknown job-local candidate entered visibility audit"
            )
        if any(
            published.manifest.candidate_sha256 == candidate_hash
            for published in self._published.values()
        ):
            raise StageOContractError(
                "unpublished_candidate_visible", "job-local candidate became visible without promotion"
            )

    def publish(
        self,
        *,
        manifest: CapabilityPromotionManifest,
        module: str,
        candidate_source: Path,
    ) -> PublishedCapability:
        manifest.validate()
        validate_module_name(module)
        if manifest.producer_run_id != self.run_id:
            raise StageOContractError(
                "capability_promotion_failed", "promotion manifest belongs to another full run"
            )
        if not LEAN_DECLARATION_RE.fullmatch(manifest.declaration):
            raise StageOContractError("capability_promotion_failed", "invalid promoted declaration")
        source_path = candidate_source.resolve()
        if not source_path.is_file():
            raise StageOContractError("capability_promotion_failed", "candidate source is missing")
        source_text = source_path.read_text(encoding="utf-8")
        if BANNED_SOURCE_RE.search(source_text):
            raise StageOContractError(
                "oracle_or_nonstandard_axiom", "candidate source contains sorry/admit/axiom"
            )
        if any(marker in source_text for marker in ORACLE_SOURCE_MARKERS):
            raise StageOContractError(
                "oracle_or_nonstandard_axiom", "candidate source imports quarantined data"
            )
        actual_hash = f"sha256:{sha256_file(source_path)}"
        if actual_hash not in {manifest.source_sha256, manifest.candidate_sha256}:
            raise StageOContractError(
                "capability_promotion_failed", "candidate source hash differs from manifest"
            )
        capability_hash = manifest.capability_hash
        if capability_hash in self._published:
            raise StageOContractError("capability_promotion_failed", "capability was already published")
        digest = capability_hash.removeprefix("sha256:")
        pack_root = self.root / digest
        source_root = pack_root / "src"
        destination = source_root / Path(*module.split(".")).with_suffix(".lean")
        destination.parent.mkdir(parents=True, exist_ok=False)
        shutil.copy2(source_path, destination)
        manifest_file = pack_root / "manifest.json"
        manifest_payload = {
            **asdict(manifest),
            "capability_hash": capability_hash,
            "module": module,
            "source_relative_path": str(destination.relative_to(pack_root)),
        }
        manifest_file.write_text(
            json.dumps(manifest_payload, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        for path in (destination, manifest_file):
            path.chmod(0o444)
        for directory in reversed((destination.parent, source_root, pack_root)):
            directory.chmod(0o555)
        published = PublishedCapability(
            capability_hash=capability_hash,
            module=module,
            declaration=manifest.declaration,
            pack_root=pack_root,
            source_file=destination,
            manifest_file=manifest_file,
            manifest=manifest,
        )
        self._published[capability_hash] = published
        return published

    def capability(self, capability_hash: str) -> PublishedCapability:
        try:
            return self._published[capability_hash]
        except KeyError as error:
            raise StageOContractError(
                "published_capability_not_visible", "requested capability is not published"
            ) from error

    def catalog_snapshot(self, *, excluded: frozenset[str] = frozenset()) -> dict[str, Any]:
        entries = [
            capability.public_view()
            for capability_hash, capability in sorted(self._published.items())
            if capability_hash not in excluded
        ]
        payload = {
            "schema_version": PUBLISHED_CATALOG_SCHEMA,
            "run_id": self.run_id,
            "entries": entries,
        }
        return {**payload, "catalog_fingerprint": sha256_id(payload)}

    def require_visible(self, capability_hash: str, *, excluded: frozenset[str] = frozenset()) -> None:
        snapshot = self.catalog_snapshot(excluded=excluded)
        visible = {entry["capability_hash"] for entry in snapshot["entries"]}
        if capability_hash not in visible:
            raise StageOContractError(
                "published_capability_not_visible", "consumer catalog does not contain the promoted pack"
            )

    def to_dict(self) -> dict[str, Any]:
        return {
            "root": str(self.root),
            "run_id": self.run_id,
            "published_count": len(self._published),
            "unpublished_candidate_count": len(self._unpublished_candidate_hashes),
            "catalog": self.catalog_snapshot(),
        }
