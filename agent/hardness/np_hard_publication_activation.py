"""H-K reviewed-candidate activation and production publication catalog.

The H-K.1 reviewer deliberately writes only a shadow candidate pack.  This
module is the separate, explicit commit boundary.  Activation is content
addressed and append-only: reviewed ``Reduction.lean`` files are copied under
``Generated/Hardness/Assets``; older assets are retained and are represented
as ``superseded`` or ``stale`` catalog entries rather than being deleted.

Nothing in this module is run implicitly by import.  In particular, merely
adding the module to the repository cannot modify the generated Lean tree or
the production registry aggregate.
"""

from __future__ import annotations

import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
from copy import deepcopy
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

from .connection_catalog import (
    ConnectionCatalog,
    ConnectionCatalogError,
    load_connection_catalog_snapshot,
)
from .models import sha256_id
from .np_hard_publication import (
    NPHardPublicationError,
    PUBLICATION_CANDIDATE_MANIFEST_SCHEMA,
    PUBLICATION_REVIEW_REPORT_SCHEMA,
    validate_candidate_manifest,
)


PUBLICATION_MANIFEST_SCHEMA = "hardness_np_hard_publication_manifest_v1"
PUBLICATION_CATALOG_SCHEMA = "hardness_np_hard_publication_catalog_v1"
PUBLICATION_AUDIT_SCHEMA = "hardness_np_hard_publication_audit_v1"
PUBLICATION_ACTIVATION_REPORT_SCHEMA = (
    "hardness_np_hard_publication_activation_report_v1"
)

PUBLICATION_CATALOG_RELATIVE = Path(
    "Publications/NP_HARD_PUBLICATION_CATALOG.json"
)
PUBLICATION_MANIFEST_ROOT_RELATIVE = Path("Publications")
GENERATED_ASSET_ROOT_RELATIVE = Path(
    "Lean/Reference/ComplexityReduction/Generated/Hardness/Assets"
)
GENERATED_AGGREGATE_RELATIVE = Path(
    "Lean/Reference/ComplexityReduction/Generated/Hardness/Aggregate.lean"
)
HARDNESS_AGGREGATE_RELATIVE = Path(
    "Lean/Reference/ComplexityReduction/Registry/HardnessAggregate.lean"
)
PRODUCTION_PROBLEM_CATALOG_RELATIVE = Path(
    ".reduction-agent/problem-catalog.json"
)
PRODUCTION_CONNECTION_CATALOG_RELATIVE = Path(
    ".reduction-agent/connection-catalog.json"
)
PRODUCTION_TARGET_CATALOG_RELATIVE = Path(
    ".reduction-agent/hardness-target-catalog.json"
)

GENERATED_AGGREGATE_MODULE = (
    "ComplexityReduction.Generated.Hardness.Aggregate"
)
GENERATED_AGGREGATE_IMPORT = f"import {GENERATED_AGGREGATE_MODULE}"
ASSET_MODULE_PREFIX = "ComplexityReduction.Generated.Hardness.Assets"
ACTIVE_STATE = "active"
STALE_STATE = "stale"
SUPERSEDED_STATE = "superseded"
PUBLICATION_STATES = frozenset({ACTIVE_STATE, STALE_STATE, SUPERSEDED_STATE})

TAGGED_SHA256_RE = re.compile(r"sha256:[0-9a-f]{64}\Z")
CASE_ID_RE = re.compile(r"[a-z0-9][a-z0-9._-]*\Z")
MODULE_RE = re.compile(r"[A-Z][A-Za-z0-9_']*(?:\.[A-Za-z0-9_']+)*\Z")
DECLARATION_RE = re.compile(
    r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z"
)


class NPHardPublicationActivationError(ValueError):
    """Stable fail-closed error raised at the publication commit boundary."""

    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


def _fail(code: str, message: str) -> None:
    raise NPHardPublicationActivationError(code, message)


def _expect(condition: bool, code: str, message: str) -> None:
    if not condition:
        _fail(code, message)


def _read_json(path: Path, *, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        _fail("publication_file_missing", f"{label} is missing: {path}")
    except json.JSONDecodeError as error:
        _fail(
            "publication_json_invalid",
            f"{label} is invalid JSON at {error.lineno}:{error.colno}",
        )
    if not isinstance(value, dict):
        _fail("publication_schema_invalid", f"{label} must be an object")
    return value


def _write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def _raw_sha256(data: bytes) -> str:
    return f"sha256:{hashlib.sha256(data).hexdigest()}"


def _file_sha256(path: Path) -> str:
    return _raw_sha256(path.read_bytes())


def _text_sha256(value: str) -> str:
    return _raw_sha256(value.encode("utf-8"))


def _content_id(value: Mapping[str, Any], *, field: str) -> str:
    payload = deepcopy(dict(value))
    payload.pop(field, None)
    return sha256_id(payload)


def _publication_content_id(value: Mapping[str, Any]) -> str:
    payload = deepcopy(dict(value))
    payload.pop("publication_id", None)
    payload.pop("activated_at", None)
    return sha256_id(payload)


def _catalog_content_id(value: Mapping[str, Any]) -> str:
    payload = deepcopy(dict(value))
    payload.pop("catalog_id", None)
    payload.pop("generated_at", None)
    return sha256_id(payload)


def _json_bytes(value: Mapping[str, Any]) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")


def _path_within(path: Path, root: Path) -> bool:
    try:
        path.resolve().relative_to(root.resolve())
    except (OSError, ValueError):
        return False
    return True


def _relative_path(path: Path, *, root: Path, label: str) -> str:
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except (OSError, ValueError):
        _fail("publication_path_escape", f"{label} escaped the repository")


def _asset_segment(candidate_id: str) -> str:
    _expect(
        isinstance(candidate_id, str)
        and TAGGED_SHA256_RE.fullmatch(candidate_id) is not None,
        "publication_candidate_id_invalid",
        "candidate ID must be a tagged SHA-256 content identity",
    )
    return "C" + candidate_id.removeprefix("sha256:")[:24]


def _asset_module(candidate_id: str) -> str:
    return f"{ASSET_MODULE_PREFIX}.{_asset_segment(candidate_id)}.Reduction"


def _asset_relative(candidate_id: str) -> Path:
    return GENERATED_ASSET_ROOT_RELATIVE / _asset_segment(candidate_id) / "Reduction.lean"


def _publication_manifest_relative(publication_id: str) -> Path:
    return (
        PUBLICATION_MANIFEST_ROOT_RELATIVE
        / f"{publication_id.removeprefix('sha256:')}.json"
    )


@dataclass(frozen=True)
class ReviewedCandidate:
    review_root: Path
    review_id: str
    row: Mapping[str, Any]
    pack_root: Path
    manifest_path: Path
    manifest: Mapping[str, Any]
    source_path: Path

    @property
    def candidate_id(self) -> str:
        return str(self.manifest["candidate_content_id"])


@dataclass(frozen=True)
class PublicationCatalogSnapshot:
    path: Path
    value: Mapping[str, Any]

    @property
    def catalog_id(self) -> str:
        return str(self.value["catalog_id"])

    @property
    def entries(self) -> tuple[Mapping[str, Any], ...]:
        return tuple(self.value["entries"])


def _candidate_manifest_paths(review_root: Path, case_id: str) -> list[Path]:
    root = review_root / "candidates" / case_id
    if not root.is_dir():
        return []
    return sorted(root.glob("*/manifest.json"))


def load_reviewed_candidates(
    *, review_report: Path, candidate_ids: Sequence[str], lean_root: Path
) -> tuple[Mapping[str, Any], tuple[ReviewedCandidate, ...]]:
    """Load the exact explicitly selected H-K.1 candidate set.

    Selection uses ``candidate_content_id`` rather than a case label or file
    path, so a later review of the same endpoint cannot be committed by an old
    command line accidentally.
    """

    selected = list(candidate_ids)
    _expect(
        selected and len(selected) == len(set(selected)),
        "publication_candidate_selection_invalid",
        "candidate IDs must be non-empty and unique",
    )
    for candidate_id in selected:
        _asset_segment(candidate_id)

    review_path = review_report.resolve()
    review_root = review_path.parent
    review = _read_json(review_path, label="publication review report")
    _expect(
        review.get("schema_version") == PUBLICATION_REVIEW_REPORT_SCHEMA
        and review.get("passed") is True
        and review.get("formal_h_j_complete") is True
        and review.get("publication_eligible") is True
        and review.get("publication_activation_performed") is False
        and review.get("public_generated_tree_modified") is False,
        "publication_review_not_eligible",
        "review report is not an eligible non-activating H-K.1 review",
    )
    _expect(
        review.get("review_id") == _content_id(review, field="review_id"),
        "publication_review_hash_mismatch",
        "review report content identity drifted",
    )
    rows = review.get("cases")
    _expect(
        isinstance(rows, list) and rows,
        "publication_review_invalid",
        "review report has no candidate rows",
    )
    by_id: dict[str, Mapping[str, Any]] = {}
    for row in rows:
        _expect(
            isinstance(row, Mapping)
            and row.get("publication_eligible") is True
            and row.get("publication_activation_performed") is False,
            "publication_review_invalid",
            "review contains an ineligible or already activated row",
        )
        candidate_id = row.get("candidate_content_id")
        _expect(
            isinstance(candidate_id, str)
            and TAGGED_SHA256_RE.fullmatch(candidate_id) is not None
            and candidate_id not in by_id,
            "publication_review_invalid",
            "review candidate identities are missing or duplicated",
        )
        by_id[candidate_id] = row
    _expect(
        set(selected).issubset(by_id),
        "publication_candidate_not_reviewed",
        "one or more selected candidate IDs are absent from this review",
    )

    candidates: list[ReviewedCandidate] = []
    for candidate_id in selected:
        row = by_id[candidate_id]
        case_id = row.get("case_id")
        _expect(
            isinstance(case_id, str) and CASE_ID_RE.fullmatch(case_id) is not None,
            "publication_review_invalid",
            "review case ID is invalid",
        )
        paths = _candidate_manifest_paths(review_root, case_id)
        _expect(
            len(paths) == 1,
            "publication_candidate_ambiguous",
            f"{case_id} does not have exactly one reviewed manifest",
        )
        manifest_path = paths[0]
        pack_root = manifest_path.parent
        manifest = _read_json(manifest_path, label=f"{case_id} candidate manifest")
        _expect(
            manifest.get("schema_version") == PUBLICATION_CANDIDATE_MANIFEST_SCHEMA
            and manifest.get("candidate_content_id") == candidate_id
            and manifest.get("manifest_id") == row.get("manifest_id")
            and _file_sha256(manifest_path) == row.get("manifest_sha256"),
            "publication_candidate_hash_mismatch",
            f"{case_id} reviewed manifest differs from its review row",
        )
        try:
            validate_candidate_manifest(
                manifest,
                pack_root=pack_root,
                lean_root=lean_root.resolve(),
            )
        except NPHardPublicationError as error:
            _fail(error.code, error.message)
        source_path = pack_root / str(manifest["candidate"]["source_file"])
        candidates.append(
            ReviewedCandidate(
                review_root=review_root,
                review_id=str(review["review_id"]),
                row=row,
                pack_root=pack_root,
                manifest_path=manifest_path,
                manifest=manifest,
                source_path=source_path,
            )
        )
    return review, tuple(candidates)


def _empty_catalog() -> dict[str, Any]:
    value: dict[str, Any] = {
        "schema_version": PUBLICATION_CATALOG_SCHEMA,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "active_publication_count": 0,
        "stale_publication_count": 0,
        "superseded_publication_count": 0,
        "entries": [],
        "aggregate": {
            "file": GENERATED_AGGREGATE_RELATIVE.as_posix(),
            "sha256": _text_sha256(_render_generated_aggregate([])),
        },
        "production_registry": None,
    }
    value["catalog_id"] = _catalog_content_id(value)
    return value


def validate_publication_manifest(value: Mapping[str, Any]) -> None:
    _expect(
        value.get("schema_version") == PUBLICATION_MANIFEST_SCHEMA,
        "publication_manifest_invalid",
        "unsupported active publication manifest schema",
    )
    state = value.get("state")
    _expect(
        state in PUBLICATION_STATES,
        "publication_manifest_invalid",
        "publication state is invalid",
    )
    for field in (
        "publication_id",
        "candidate_id",
        "candidate_manifest_id",
        "canonical_identity_id",
        "review_id",
    ):
        _expect(
            isinstance(value.get(field), str)
            and TAGGED_SHA256_RE.fullmatch(str(value[field])) is not None,
            "publication_manifest_invalid",
            f"{field} is not a tagged SHA-256 identity",
        )
    asset = value.get("asset")
    route = value.get("route")
    _expect(
        isinstance(asset, Mapping)
        and isinstance(asset.get("module"), str)
        and MODULE_RE.fullmatch(str(asset["module"])) is not None
        and isinstance(asset.get("declaration"), str)
        and DECLARATION_RE.fullmatch(str(asset["declaration"])) is not None
        and isinstance(asset.get("source_file"), str)
        and not Path(str(asset["source_file"])).is_absolute()
        and isinstance(asset.get("source_sha256"), str)
        and TAGGED_SHA256_RE.fullmatch(str(asset["source_sha256"])) is not None,
        "publication_manifest_invalid",
        "publication asset metadata is invalid",
    )
    runner_owned = (
        route.get("runner_owned_reduction")
        if isinstance(route, Mapping)
        else None
    )
    _expect(
        isinstance(route, Mapping)
        and route.get("source") == value.get("source_hub")
        and route.get("target") == value.get("canonical_endpoint")
        and route.get("direction") == value.get("direction")
        and isinstance(runner_owned, Mapping)
        and runner_owned.get("published_declaration") == asset.get("declaration")
        and runner_owned.get("attributes") == asset.get("attributes"),
        "publication_manifest_invalid",
        "publication endpoint/route/asset bindings drifted",
    )
    candidate_id = str(value.get("candidate_id"))
    _expect(
        asset.get("module") == _asset_module(candidate_id)
        and asset.get("source_file") == _asset_relative(candidate_id).as_posix(),
        "publication_manifest_invalid",
        "publication asset location is not derived from its candidate ID",
    )
    _expect(
        value.get("publication_id") == _publication_content_id(value),
        "publication_manifest_hash_mismatch",
        "publication manifest content identity drifted",
    )


def _validate_catalog_entry(entry: Mapping[str, Any]) -> None:
    _expect(
        entry.get("status") in PUBLICATION_STATES,
        "publication_catalog_invalid",
        "catalog entry has an invalid status",
    )
    for field in (
        "publication_id",
        "candidate_id",
        "canonical_identity_id",
        "manifest_sha256",
    ):
        _expect(
            isinstance(entry.get(field), str)
            and TAGGED_SHA256_RE.fullmatch(str(entry[field])) is not None,
            "publication_catalog_invalid",
            f"catalog entry {field} is invalid",
        )
    _expect(
        isinstance(entry.get("asset_module"), str)
        and MODULE_RE.fullmatch(str(entry["asset_module"])) is not None
        and isinstance(entry.get("asset_declaration"), str)
        and DECLARATION_RE.fullmatch(str(entry["asset_declaration"])) is not None
        and isinstance(entry.get("manifest_file"), str)
        and not Path(str(entry["manifest_file"])).is_absolute(),
        "publication_catalog_invalid",
        "catalog entry asset or manifest location is invalid",
    )
    stale_reasons = entry.get("stale_reasons")
    _expect(
        isinstance(stale_reasons, list)
        and all(isinstance(reason, str) and reason for reason in stale_reasons)
        and ((entry["status"] == STALE_STATE) == bool(stale_reasons)),
        "publication_catalog_invalid",
        "catalog stale status and reasons differ",
    )
    superseded_by = entry.get("superseded_by")
    _expect(
        (entry["status"] == SUPERSEDED_STATE)
        == (
            isinstance(superseded_by, str)
            and TAGGED_SHA256_RE.fullmatch(superseded_by) is not None
        ),
        "publication_catalog_invalid",
        "catalog superseded status and replacement differ",
    )


def load_publication_catalog(path: Path) -> PublicationCatalogSnapshot:
    value = _read_json(path.resolve(), label="publication catalog")
    _expect(
        value.get("schema_version") == PUBLICATION_CATALOG_SCHEMA,
        "publication_catalog_invalid",
        "unsupported publication catalog schema",
    )
    entries = value.get("entries")
    aggregate = value.get("aggregate")
    _expect(
        isinstance(entries, list)
        and isinstance(aggregate, Mapping)
        and aggregate.get("file") == GENERATED_AGGREGATE_RELATIVE.as_posix()
        and isinstance(aggregate.get("sha256"), str)
        and TAGGED_SHA256_RE.fullmatch(str(aggregate["sha256"])) is not None,
        "publication_catalog_invalid",
        "publication catalog entries/aggregate binding are invalid",
    )
    for entry in entries:
        _expect(
            isinstance(entry, Mapping),
            "publication_catalog_invalid",
            "publication catalog entry must be an object",
        )
        _validate_catalog_entry(entry)
    _expect(
        aggregate.get("sha256") == _text_sha256(_render_generated_aggregate(entries)),
        "publication_catalog_invalid",
        "publication aggregate hash differs from active catalog entries",
    )
    publication_ids = [entry["publication_id"] for entry in entries]
    _expect(
        len(publication_ids) == len(set(publication_ids)),
        "publication_catalog_invalid",
        "publication catalog repeats a publication identity",
    )
    expected_counts = {
        ACTIVE_STATE: sum(entry["status"] == ACTIVE_STATE for entry in entries),
        STALE_STATE: sum(entry["status"] == STALE_STATE for entry in entries),
        SUPERSEDED_STATE: sum(
            entry["status"] == SUPERSEDED_STATE for entry in entries
        ),
    }
    _expect(
        value.get("active_publication_count") == expected_counts[ACTIVE_STATE]
        and value.get("stale_publication_count") == expected_counts[STALE_STATE]
        and value.get("superseded_publication_count")
        == expected_counts[SUPERSEDED_STATE],
        "publication_catalog_invalid",
        "publication catalog status counts drifted",
    )
    _expect(
        value.get("catalog_id") == _catalog_content_id(value),
        "publication_catalog_hash_mismatch",
        "publication catalog content identity drifted",
    )
    return PublicationCatalogSnapshot(path=path.resolve(), value=value)


def _load_existing_catalog(path: Path) -> dict[str, Any]:
    if not path.is_file():
        return _empty_catalog()
    return deepcopy(dict(load_publication_catalog(path).value))


def _render_generated_aggregate(entries: Iterable[Mapping[str, Any]]) -> str:
    modules = sorted(
        {
            str(entry["asset_module"])
            for entry in entries
            if entry.get("status") == ACTIVE_STATE
        }
    )
    imports = "\n".join(f"import {module}" for module in modules)
    return (
        "/-\n"
        "Generated by publish_np_hard_publication.py.\n"
        "Only active, dependency-current, reviewed hardness assets are imported.\n"
        "Do not edit this file by hand.\n"
        "-/\n\n"
        + (imports + "\n" if imports else "")
    )


def _render_registry_aggregate(source: str) -> str:
    if GENERATED_AGGREGATE_IMPORT in source.splitlines():
        return source
    import_lines = list(re.finditer(r"(?m)^import\s+[^\n]+$", source))
    _expect(
        bool(import_lines),
        "publication_registry_activation_failed",
        "HardnessAggregate has no import insertion point",
    )
    position = import_lines[-1].end()
    return source[:position] + "\n" + GENERATED_AGGREGATE_IMPORT + source[position:]


def _candidate_publication_manifest(
    *, candidate: ReviewedCandidate, repo_root: Path
) -> dict[str, Any]:
    manifest = candidate.manifest
    candidate_payload = manifest["candidate"]
    candidate_id = candidate.candidate_id
    asset_relative = _asset_relative(candidate_id)
    value: dict[str, Any] = {
        "schema_version": PUBLICATION_MANIFEST_SCHEMA,
        "state": ACTIVE_STATE,
        "candidate_id": candidate_id,
        "candidate_manifest_id": manifest["manifest_id"],
        "candidate_manifest_sha256": _file_sha256(candidate.manifest_path),
        "review_id": candidate.review_id,
        "case_id": manifest["case_id"],
        "label": manifest["label"],
        "canonical_identity_id": manifest["canonical_identity_id"],
        "canonical_endpoint": manifest["canonical_endpoint"],
        "source_hub": manifest["source_hub"],
        "direction": manifest["direction"],
        "route": deepcopy(manifest["route"]),
        "model_evidence": deepcopy(manifest["model_evidence"]),
        "audit_evidence": {
            "fresh_core": deepcopy(manifest["fresh_core_evidence"]),
            "deletion": deepcopy(manifest["deletion_evidence"]),
            "axiom": deepcopy(manifest["axiom_evidence"]),
            "endpoint": deepcopy(manifest["endpoint_evidence"]),
            "shadow": deepcopy(manifest["shadow_audits"]),
        },
        "asset": {
            "module": _asset_module(candidate_id),
            "declaration": candidate_payload["declaration"],
            "source_file": asset_relative.as_posix(),
            "source_sha256": candidate_payload["source_sha256"],
            "reviewed_namespace": candidate_payload["namespace"],
            "reviewed_module": candidate_payload["module"],
            "attributes": deepcopy(candidate_payload["attributes"]),
        },
        "dependency_snapshot": deepcopy(manifest["dependencies"]),
        "source_provenance": {
            "h_j": deepcopy(manifest["h_j_evidence"]),
            "review_report_sha256": _file_sha256(
                candidate.review_root / "review-report.json"
            ),
        },
    }
    value["publication_id"] = _publication_content_id(value)
    validate_publication_manifest(value)
    return value


def _catalog_entry(publication: Mapping[str, Any]) -> dict[str, Any]:
    publication_id = str(publication["publication_id"])
    manifest_relative = _publication_manifest_relative(publication_id)
    return {
        "publication_id": publication_id,
        "candidate_id": publication["candidate_id"],
        "case_id": publication["case_id"],
        "label": publication["label"],
        "canonical_identity_id": publication["canonical_identity_id"],
        "canonical_endpoint": publication["canonical_endpoint"],
        "source_hub": publication["source_hub"],
        "direction": publication["direction"],
        "asset_module": publication["asset"]["module"],
        "asset_declaration": publication["asset"]["declaration"],
        "asset_source_file": publication["asset"]["source_file"],
        "asset_source_sha256": publication["asset"]["source_sha256"],
        "manifest_file": manifest_relative.as_posix(),
        "manifest_sha256": _raw_sha256(_json_bytes(publication)),
        "status": ACTIVE_STATE,
        "stale_reasons": [],
        "superseded_by": None,
    }


def _status_counts(entries: Sequence[Mapping[str, Any]]) -> dict[str, int]:
    return {
        ACTIVE_STATE: sum(entry.get("status") == ACTIVE_STATE for entry in entries),
        STALE_STATE: sum(entry.get("status") == STALE_STATE for entry in entries),
        SUPERSEDED_STATE: sum(
            entry.get("status") == SUPERSEDED_STATE for entry in entries
        ),
    }


def _seal_catalog(
    *, entries: Sequence[Mapping[str, Any]], production_registry: Mapping[str, Any] | None
) -> dict[str, Any]:
    ordered = sorted(
        (deepcopy(dict(entry)) for entry in entries),
        key=lambda entry: (
            str(entry["canonical_identity_id"]),
            str(entry["publication_id"]),
        ),
    )
    counts = _status_counts(ordered)
    value: dict[str, Any] = {
        "schema_version": PUBLICATION_CATALOG_SCHEMA,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "active_publication_count": counts[ACTIVE_STATE],
        "stale_publication_count": counts[STALE_STATE],
        "superseded_publication_count": counts[SUPERSEDED_STATE],
        "entries": ordered,
        "aggregate": {
            "file": GENERATED_AGGREGATE_RELATIVE.as_posix(),
            "sha256": _text_sha256(_render_generated_aggregate(ordered)),
        },
        "production_registry": (
            deepcopy(dict(production_registry))
            if production_registry is not None
            else None
        ),
    }
    value["catalog_id"] = _catalog_content_id(value)
    return value


def _run(
    command: Sequence[str], *, cwd: Path, timeout_seconds: int
) -> dict[str, Any]:
    try:
        result = subprocess.run(
            list(command),
            cwd=cwd,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout_seconds,
            check=False,
        )
        return {
            "command": list(command),
            "exit_code": result.returncode,
            "timed_out": False,
            "stdout_sha256": _text_sha256(result.stdout),
            "stderr_sha256": _text_sha256(result.stderr),
            "stdout": result.stdout,
            "stderr": result.stderr,
        }
    except subprocess.TimeoutExpired as error:
        stdout = error.stdout if isinstance(error.stdout, str) else ""
        stderr = error.stderr if isinstance(error.stderr, str) else ""
        return {
            "command": list(command),
            "exit_code": None,
            "timed_out": True,
            "stdout_sha256": _text_sha256(stdout),
            "stderr_sha256": _text_sha256(stderr),
            "stdout": stdout,
            "stderr": stderr,
        }


def _command_evidence(command: Mapping[str, Any]) -> dict[str, Any]:
    return {
        key: deepcopy(command[key])
        for key in (
            "command",
            "exit_code",
            "timed_out",
            "stdout_sha256",
            "stderr_sha256",
        )
    }


def _install_generated_view(
    *,
    root: Path,
    candidates: Sequence[ReviewedCandidate],
    publications: Sequence[Mapping[str, Any]],
    entries: Sequence[Mapping[str, Any]],
) -> None:
    for candidate, publication in zip(candidates, publications, strict=True):
        destination = root / str(publication["asset"]["source_file"])
        destination.parent.mkdir(parents=True, exist_ok=True)
        source_bytes = candidate.source_path.read_bytes()
        if destination.exists():
            _expect(
                destination.read_bytes() == source_bytes,
                "publication_content_address_collision",
                f"existing asset differs at {destination}",
            )
        else:
            destination.write_bytes(source_bytes)
    aggregate = root / GENERATED_AGGREGATE_RELATIVE
    aggregate.parent.mkdir(parents=True, exist_ok=True)
    aggregate.write_text(_render_generated_aggregate(entries), encoding="utf-8")
    registry = root / HARDNESS_AGGREGATE_RELATIVE
    registry.write_text(
        _render_registry_aggregate(registry.read_text(encoding="utf-8")),
        encoding="utf-8",
    )


def _shadow_activation_audit(
    *,
    repo_root: Path,
    candidates: Sequence[ReviewedCandidate],
    publications: Sequence[Mapping[str, Any]],
    entries: Sequence[Mapping[str, Any]],
    timeout_seconds: int,
) -> dict[str, Any]:
    lean_root = repo_root / "Lean"
    with tempfile.TemporaryDirectory(prefix="np-hard-publication-") as directory:
        shadow_repo = Path(directory) / "repo"
        shadow_lean = shadow_repo / "Lean"
        shadow_lean.mkdir(parents=True)
        shutil.copytree(lean_root / "Reference", shadow_lean / "Reference")
        for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
            shutil.copy2(lean_root / name, shadow_lean / name)
        package_cache = lean_root / ".lake/packages"
        _expect(
            package_cache.is_dir(),
            "publication_dependency_stale",
            "Lean package cache is unavailable for the clean activation audit",
        )
        (shadow_lean / ".lake").mkdir()
        (shadow_lean / ".lake/packages").symlink_to(
            package_cache, target_is_directory=True
        )
        _install_generated_view(
            root=shadow_repo,
            candidates=candidates,
            publications=publications,
            entries=entries,
        )
        modules = [str(publication["asset"]["module"]) for publication in publications]
        build = _run(
            [
                "lake",
                "build",
                "ComplexityReduction.Registry.HardnessAggregate",
                "ComplexityReduction.Agent.Hardness.ProblemCatalog",
                *modules,
            ],
            cwd=shadow_lean,
            timeout_seconds=timeout_seconds,
        )
        _expect(
            build["exit_code"] == 0 and build["timed_out"] is False,
            "publication_activation_shadow_build_failed",
            "clean activation shadow failed to build",
        )
        audit_relative = Path("PublicationActivationAudit.lean")
        declarations = [str(publication["asset"]["declaration"]) for publication in publications]
        audit_source = (
            "import ComplexityReduction.Agent.Hardness.ProblemCatalog\n\n"
            "assert_standard_axioms\n  "
            + ",\n  ".join(declarations)
            + "\n\nrun_cmd\n"
            + "  let environment ← Lean.getEnv\n"
            + "  for declaration in ["
            + ", ".join(f"``{declaration}" for declaration in declarations)
            + "] do\n"
            + "    unless ComplexityReduction.Registry.isCandidateName environment declaration do\n"
            + "      throwError \"published declaration is absent from production discovery\"\n"
            + "    unless (ComplexityReduction.Registry.validateAttributedDeclaration environment declaration).isSome do\n"
            + "      throwError \"published declaration failed production type validation\"\n"
        )
        (shadow_lean / audit_relative).write_text(audit_source, encoding="utf-8")
        audit = _run(
            ["lake", "env", "lean", audit_relative.as_posix()],
            cwd=shadow_lean,
            timeout_seconds=timeout_seconds,
        )
        _expect(
            audit["exit_code"] == 0 and audit["timed_out"] is False,
            "publication_activation_registry_audit_failed",
            "clean activation shadow did not expose every published typed edge",
        )
        return {
            "schema_version": PUBLICATION_AUDIT_SCHEMA,
            "passed": True,
            "clean_workspace": True,
            "old_project_olean_absent_before_build": True,
            "asset_count": len(publications),
            "asset_modules": modules,
            "declarations": declarations,
            "build": _command_evidence(build),
            "registry_discovery": {
                "passed": True,
                "source_sha256": _text_sha256(audit_source),
                **_command_evidence(audit),
            },
        }


def _build_production_catalogs(
    *, repo_root: Path, timeout_seconds: int
) -> tuple[dict[str, Any], ConnectionCatalog]:
    command = [
        sys.executable,
        str(repo_root / "scripts/build_problem_catalog_snapshot.py"),
        "--output",
        str(repo_root / PRODUCTION_PROBLEM_CATALOG_RELATIVE),
        "--connection-output",
        str(repo_root / PRODUCTION_CONNECTION_CATALOG_RELATIVE),
        "--target-output",
        str(repo_root / PRODUCTION_TARGET_CATALOG_RELATIVE),
        "--lean-timeout",
        str(timeout_seconds),
    ]
    result = _run(command, cwd=repo_root, timeout_seconds=timeout_seconds + 120)
    _expect(
        result["exit_code"] == 0 and result["timed_out"] is False,
        "publication_catalog_rebuild_failed",
        "production problem/connection catalog rebuild failed",
    )
    try:
        catalog = load_connection_catalog_snapshot(
            repo_root / PRODUCTION_CONNECTION_CATALOG_RELATIVE
        )
    except ConnectionCatalogError as error:
        _fail("publication_catalog_rebuild_failed", str(error))
    return _command_evidence(result), catalog


def _production_registry_record(catalog: ConnectionCatalog) -> dict[str, Any]:
    return {
        "registry_fingerprint": catalog.registry_fingerprint,
        "connection_catalog_id": catalog.catalog_id,
        "connection_catalog_file": PRODUCTION_CONNECTION_CATALOG_RELATIVE.as_posix(),
        "connection_catalog_sha256": _file_sha256(
            Path.cwd() / PRODUCTION_CONNECTION_CATALOG_RELATIVE
        ),
        "toolchain": catalog.toolchain,
        "lake_manifest_sha256": catalog.lake_manifest_sha256,
    }


def _assert_catalog_discovers(
    catalog: ConnectionCatalog, publications: Sequence[Mapping[str, Any]]
) -> None:
    declarations = {entry.certificate_declaration for entry in catalog.entries}
    missing = sorted(
        str(publication["asset"]["declaration"])
        for publication in publications
        if publication["asset"]["declaration"] not in declarations
    )
    _expect(
        not missing,
        "publication_catalog_discovery_failed",
        f"production connection catalog missed published declarations: {missing!r}",
    )


def publish_reviewed_candidates(
    *,
    review_report: Path,
    candidate_ids: Sequence[str],
    repo_root: Path,
    output_report: Path,
    timeout_seconds: int = 1200,
    rebuild_production_catalogs: bool = True,
) -> dict[str, Any]:
    """Explicitly commit reviewed candidates and activate their typed edges.

    The caller must name every exact candidate content ID.  The function first
    performs a clean shadow build and discovery audit.  It never deletes an
    older asset; same-identity predecessors become ``superseded`` entries.
    """

    root = repo_root.resolve()
    lean_root = root / "Lean"
    review, candidates = load_reviewed_candidates(
        review_report=review_report,
        candidate_ids=candidate_ids,
        lean_root=lean_root,
    )
    catalog_path = root / PUBLICATION_CATALOG_RELATIVE
    existing = _load_existing_catalog(catalog_path)
    existing_entries = [deepcopy(dict(entry)) for entry in existing["entries"]]
    existing_candidate_ids = {str(entry["candidate_id"]) for entry in existing_entries}
    _expect(
        not existing_candidate_ids.intersection(candidate_ids),
        "publication_candidate_already_committed",
        "one or more selected candidate IDs already exist in the publication catalog",
    )

    publications = [
        _candidate_publication_manifest(candidate=candidate, repo_root=root)
        for candidate in candidates
    ]
    replacement_by_identity = {
        str(publication["canonical_identity_id"]): str(publication["publication_id"])
        for publication in publications
    }
    for entry in existing_entries:
        replacement = replacement_by_identity.get(str(entry["canonical_identity_id"]))
        if replacement is not None and entry.get("status") == ACTIVE_STATE:
            entry["status"] = SUPERSEDED_STATE
            entry["superseded_by"] = replacement
            entry["stale_reasons"] = []

    new_entries = [_catalog_entry(publication) for publication in publications]
    provisional_entries = [*existing_entries, *new_entries]
    shadow_audit = _shadow_activation_audit(
        repo_root=root,
        candidates=candidates,
        publications=publications,
        entries=provisional_entries,
        timeout_seconds=timeout_seconds,
    )

    # Only this point crosses the public activation boundary.
    for publication in publications:
        manifest_path = root / _publication_manifest_relative(
            str(publication["publication_id"])
        )
        if manifest_path.exists():
            _expect(
                manifest_path.read_bytes() == _json_bytes(publication),
                "publication_manifest_collision",
                f"existing publication manifest differs: {manifest_path}",
            )
        else:
            _write_json(manifest_path, publication)
    _install_generated_view(
        root=root,
        candidates=candidates,
        publications=publications,
        entries=provisional_entries,
    )
    rebuild_evidence: Mapping[str, Any] | None = None
    registry_record: Mapping[str, Any] | None = None
    if rebuild_production_catalogs:
        rebuild_evidence, connection_catalog = _build_production_catalogs(
            repo_root=root, timeout_seconds=timeout_seconds
        )
        _assert_catalog_discovers(connection_catalog, publications)
        registry_record = {
            "registry_fingerprint": connection_catalog.registry_fingerprint,
            "connection_catalog_id": connection_catalog.catalog_id,
            "connection_catalog_file": PRODUCTION_CONNECTION_CATALOG_RELATIVE.as_posix(),
            "connection_catalog_sha256": _file_sha256(
                root / PRODUCTION_CONNECTION_CATALOG_RELATIVE
            ),
            "toolchain": connection_catalog.toolchain,
            "lake_manifest_sha256": connection_catalog.lake_manifest_sha256,
        }
    catalog = _seal_catalog(
        entries=provisional_entries,
        production_registry=registry_record,
    )
    _write_json(catalog_path, catalog)
    load_publication_catalog(catalog_path)

    report: dict[str, Any] = {
        "schema_version": PUBLICATION_ACTIVATION_REPORT_SCHEMA,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "stage": "h-k.2-publication-activation",
        "passed": True,
        "review": {
            "file": _relative_path(review_report, root=root, label="review report"),
            "sha256": _file_sha256(review_report.resolve()),
            "review_id": review["review_id"],
        },
        "explicit_candidate_ids": list(candidate_ids),
        "published_count": len(publications),
        "publications": [
            {
                "publication_id": publication["publication_id"],
                "candidate_id": publication["candidate_id"],
                "case_id": publication["case_id"],
                "canonical_identity_id": publication["canonical_identity_id"],
                "canonical_endpoint": publication["canonical_endpoint"],
                "asset_module": publication["asset"]["module"],
                "asset_declaration": publication["asset"]["declaration"],
                "manifest_file": _publication_manifest_relative(
                    str(publication["publication_id"])
                ).as_posix(),
            }
            for publication in publications
        ],
        "publication_catalog": {
            "file": PUBLICATION_CATALOG_RELATIVE.as_posix(),
            "sha256": _file_sha256(catalog_path),
            "catalog_id": catalog["catalog_id"],
            "active_publication_count": catalog["active_publication_count"],
        },
        "generated_aggregate": {
            "file": GENERATED_AGGREGATE_RELATIVE.as_posix(),
            "sha256": _file_sha256(root / GENERATED_AGGREGATE_RELATIVE),
        },
        "production_catalog_rebuild": rebuild_evidence,
        "audits": {
            "shadow_activation": shadow_audit,
            "content_addressed_append_only": True,
            "reviewed_candidate_ids_exact": True,
            "production_resolver_discovery": rebuild_production_catalogs,
        },
        "publication_activation_performed": True,
    }
    report["report_id"] = sha256_id(report)
    _write_json(output_report.resolve(), report)
    return report


def _current_dependency_staleness(
    *, publication: Mapping[str, Any], repo_root: Path
) -> list[str]:
    reasons: list[str] = []
    dependency = publication.get("dependency_snapshot")
    if not isinstance(dependency, Mapping):
        return ["dependency_snapshot_missing"]
    toolchain = dependency.get("toolchain")
    if not isinstance(toolchain, Mapping):
        reasons.append("toolchain_snapshot_missing")
    else:
        expected_files = {
            "lean_toolchain_sha256": repo_root / "Lean/lean-toolchain",
            "lake_manifest_sha256": repo_root / "Lean/lake-manifest.json",
            "lakefile_sha256": repo_root / "Lean/lakefile.toml",
        }
        for field, path in expected_files.items():
            if not path.is_file() or toolchain.get(field) != _file_sha256(path):
                reasons.append(field)
    for section, field in (
        ("task_public_source_files", "task_public_source_files"),
        ("closure", "project_source_files"),
    ):
        container = dependency if section == "task_public_source_files" else dependency.get("closure")
        files = container.get(field) if isinstance(container, Mapping) else None
        if not isinstance(files, Mapping):
            reasons.append(f"{section}_missing")
            continue
        for relative, expected_hash in files.items():
            path = repo_root / str(relative)
            if not path.is_file() or _file_sha256(path) != expected_hash:
                reasons.append(f"dependency:{relative}")
    return sorted(set(reasons))


def _entry_manifest_mismatches(
    entry: Mapping[str, Any], publication: Mapping[str, Any]
) -> list[str]:
    asset = publication.get("asset")
    expected = {
        "publication_id": publication.get("publication_id"),
        "candidate_id": publication.get("candidate_id"),
        "case_id": publication.get("case_id"),
        "canonical_identity_id": publication.get("canonical_identity_id"),
        "canonical_endpoint": publication.get("canonical_endpoint"),
        "source_hub": publication.get("source_hub"),
        "direction": publication.get("direction"),
        "asset_module": asset.get("module") if isinstance(asset, Mapping) else None,
        "asset_declaration": (
            asset.get("declaration") if isinstance(asset, Mapping) else None
        ),
        "asset_source_file": (
            asset.get("source_file") if isinstance(asset, Mapping) else None
        ),
        "asset_source_sha256": (
            asset.get("source_sha256") if isinstance(asset, Mapping) else None
        ),
    }
    return sorted(
        f"catalog_manifest:{field}"
        for field, value in expected.items()
        if entry.get(field) != value
    )


def revalidate_publication_catalog(
    *, repo_root: Path, catalog_path: Path, output_report: Path
) -> dict[str, Any]:
    """Mark dependency-drifted publications stale without deleting assets."""

    root = repo_root.resolve()
    snapshot = load_publication_catalog(catalog_path.resolve())
    entries = [deepcopy(dict(entry)) for entry in snapshot.entries]
    rows: list[dict[str, Any]] = []
    for entry in entries:
        manifest_path = root / str(entry["manifest_file"])
        reasons: list[str]
        if not manifest_path.is_file() or _file_sha256(manifest_path) != entry["manifest_sha256"]:
            reasons = ["publication_manifest_missing_or_tampered"]
        else:
            publication = _read_json(
                manifest_path, label=f"publication {entry['publication_id']}"
            )
            try:
                validate_publication_manifest(publication)
            except NPHardPublicationActivationError as error:
                reasons = [error.code]
            else:
                asset_path = root / str(entry["asset_source_file"])
                reasons = _entry_manifest_mismatches(entry, publication)
                if not asset_path.is_file() or _file_sha256(asset_path) != entry["asset_source_sha256"]:
                    reasons.append("publication_asset_missing_or_tampered")
                reasons.extend(
                    _current_dependency_staleness(
                        publication=publication, repo_root=root
                    )
                )
        previous = str(entry["status"])
        if previous != SUPERSEDED_STATE:
            entry["status"] = STALE_STATE if reasons else ACTIVE_STATE
            entry["stale_reasons"] = reasons
            entry["superseded_by"] = None
        rows.append(
            {
                "publication_id": entry["publication_id"],
                "previous_status": previous,
                "current_status": entry["status"],
                "stale_reasons": deepcopy(entry["stale_reasons"]),
            }
        )
    catalog = _seal_catalog(
        entries=entries,
        production_registry=snapshot.value.get("production_registry"),
    )
    _write_json(catalog_path.resolve(), catalog)
    aggregate_path = root / GENERATED_AGGREGATE_RELATIVE
    if aggregate_path.is_file():
        aggregate_path.write_text(
            _render_generated_aggregate(entries), encoding="utf-8"
        )
    report: dict[str, Any] = {
        "schema_version": PUBLICATION_AUDIT_SCHEMA,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "stage": "h-k.4-drift-revalidation",
        "passed": True,
        "previous_catalog_id": snapshot.catalog_id,
        "publication_catalog": {
            "file": _relative_path(catalog_path, root=root, label="publication catalog"),
            "sha256": _file_sha256(catalog_path.resolve()),
            "catalog_id": catalog["catalog_id"],
        },
        "rows": rows,
        "stale_count": catalog["stale_publication_count"],
        "superseded_count": catalog["superseded_publication_count"],
        "active_count": catalog["active_publication_count"],
        "non_destructive": True,
    }
    report["report_id"] = sha256_id(report)
    _write_json(output_report.resolve(), report)
    return report


def resolve_active_publication(
    *,
    catalog: PublicationCatalogSnapshot,
    canonical_identity_id: str,
    repo_root: Path | None = None,
) -> Mapping[str, Any] | None:
    """Return the unique active production publication for one identity."""

    matches = [
        entry
        for entry in catalog.entries
        if entry.get("canonical_identity_id") == canonical_identity_id
        and entry.get("status") == ACTIVE_STATE
    ]
    _expect(
        len(matches) <= 1,
        "publication_catalog_ambiguous",
        "multiple active publications claim the same canonical identity",
    )
    if not matches:
        return None
    entry = matches[0]
    if repo_root is not None:
        root = repo_root.resolve()
        manifest_path = root / str(entry["manifest_file"])
        _expect(
            manifest_path.is_file()
            and _file_sha256(manifest_path) == entry["manifest_sha256"],
            "publication_dependency_stale",
            "active publication manifest is missing or tampered",
        )
        publication = _read_json(
            manifest_path, label=f"publication {entry['publication_id']}"
        )
        validate_publication_manifest(publication)
        mismatches = _entry_manifest_mismatches(entry, publication)
        _expect(
            not mismatches,
            "publication_catalog_stale",
            f"active catalog entry differs from its manifest: {mismatches!r}",
        )
        asset_path = root / str(entry["asset_source_file"])
        reasons = _current_dependency_staleness(
            publication=publication, repo_root=root
        )
        if not asset_path.is_file() or _file_sha256(asset_path) != entry["asset_source_sha256"]:
            reasons.append("publication_asset_missing_or_tampered")
        _expect(
            not reasons,
            "publication_dependency_stale",
            f"active publication is stale: {sorted(set(reasons))!r}",
        )
    return entry


def validate_publication_catalog_current(
    *,
    catalog: PublicationCatalogSnapshot,
    repo_root: Path,
    require_production_registry: bool = True,
) -> None:
    """Validate aggregate, active assets, dependencies, and resolver discovery."""

    root = repo_root.resolve()
    aggregate = catalog.value.get("aggregate")
    _expect(
        isinstance(aggregate, Mapping),
        "publication_catalog_stale",
        "publication catalog lacks an aggregate binding",
    )
    aggregate_path = root / str(aggregate.get("file"))
    _expect(
        aggregate_path.is_file()
        and _file_sha256(aggregate_path) == aggregate.get("sha256")
        and aggregate.get("sha256")
        == _text_sha256(_render_generated_aggregate(catalog.entries)),
        "publication_catalog_stale",
        "generated aggregate is missing, tampered, or differs from active entries",
    )
    active_entries = [
        entry for entry in catalog.entries if entry.get("status") == ACTIVE_STATE
    ]
    for entry in active_entries:
        resolve_active_publication(
            catalog=catalog,
            canonical_identity_id=str(entry["canonical_identity_id"]),
            repo_root=root,
        )
    production = catalog.value.get("production_registry")
    if not require_production_registry and production is None:
        return
    _expect(
        isinstance(production, Mapping),
        "publication_catalog_stale",
        "publication catalog lacks production resolver provenance",
    )
    connection_path = root / str(production.get("connection_catalog_file"))
    _expect(
        connection_path.is_file()
        and _file_sha256(connection_path)
        == production.get("connection_catalog_sha256"),
        "publication_catalog_stale",
        "production connection catalog is missing or tampered",
    )
    try:
        connection = load_connection_catalog_snapshot(connection_path)
    except ConnectionCatalogError as error:
        _fail("publication_catalog_stale", str(error))
    _expect(
        connection.catalog_id == production.get("connection_catalog_id")
        and connection.registry_fingerprint == production.get("registry_fingerprint"),
        "publication_catalog_stale",
        "production connection catalog identity drifted",
    )
    discovered = {entry.certificate_declaration for entry in connection.entries}
    expected = {str(entry["asset_declaration"]) for entry in active_entries}
    _expect(
        expected.issubset(discovered),
        "publication_catalog_stale",
        "production resolver no longer discovers every active publication",
    )


__all__ = [
    "ACTIVE_STATE",
    "GENERATED_AGGREGATE_MODULE",
    "GENERATED_AGGREGATE_RELATIVE",
    "NPHardPublicationActivationError",
    "PUBLICATION_ACTIVATION_REPORT_SCHEMA",
    "PUBLICATION_AUDIT_SCHEMA",
    "PUBLICATION_CATALOG_RELATIVE",
    "PUBLICATION_CATALOG_SCHEMA",
    "PUBLICATION_MANIFEST_SCHEMA",
    "PUBLICATION_STATES",
    "PublicationCatalogSnapshot",
    "ReviewedCandidate",
    "load_publication_catalog",
    "load_reviewed_candidates",
    "publish_reviewed_candidates",
    "resolve_active_publication",
    "revalidate_publication_catalog",
    "validate_publication_manifest",
    "validate_publication_catalog_current",
]
