"""Safe, answer-isolated audit support for the bundled reduction archive.

The archive is untrusted benchmark provenance.  It is never extracted with
archive-owned paths.  Members are listed with ``bsdtar`` and streamed either
into memory with an explicit byte limit or into a caller-owned temporary
directory after every member path has passed traversal checks.

The generated audit intentionally records hashes and metadata, not statements,
hints, or solutions.  A separate scorer-only selection annotation may add
endpoint readiness and split decisions without changing the archived source.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
from contextlib import contextmanager
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath
from typing import Any, BinaryIO, Iterator, Mapping, Sequence

from .models import sha256_id


PROBLEM_ARCHIVE_AUDIT_SCHEMA_V1 = "hardness_np_hard_problem_archive_audit_v1"
PROBLEM_ARCHIVE_SELECTION_SCHEMA_V1 = "hardness_np_hard_problem_archive_selection_v1"
ARCHIVE_DIRECTION_SCHEMA_V1 = "hardness_np_hard_archive_direction_v1"
EXPECTED_CLEAN_PROBLEM_COUNT = 63
EXPECTED_UNIQUE_DIRECTION_COUNT = 60
EXPECTED_UNIQUE_PROBLEM_COUNT = 57
EXPECTED_RAW_PROBLEM_COUNT = 102
EXPECTED_SELECTION_COUNT = 24
EXPECTED_PDF_ONLY_SOURCE_COUNT = 7
EXPECTED_PDF_ONLY_CANDIDATE_COUNT = 16
EXPECTED_SELECTION_SPLIT_COUNTS = {"dev": 6, "validation": 6, "heldout": 12}
EXPECTED_SELECTION_STATUS_COUNTS = {
    "ready": 7,
    "blocked_endpoint_formalization": 17,
}
DEFAULT_MAX_JSON_BYTES = 32 * 1024 * 1024
DEFAULT_MAX_MEMBER_BYTES = 256 * 1024 * 1024

_HASH_RE = re.compile(r"sha256:[0-9a-f]{64}\Z")
_SOURCE_FILE_RE = re.compile(r"([0-9]{2})\.md\Z")

# These are source-data defects, not benchmark outcomes.  Keeping the known
# corrections here makes the archive audit reproducible without silently
# rewriting ``problems_clean.json``.
KNOWN_DATA_QUALITY: Mapping[str, Mapping[str, Any]] = {
    "03-004c": {
        "data_quality_status": "quarantined_source_error",
        "reason": "metadata says 3SAT -> TILING while the statement says PARTITION -> TILING",
    },
    "03-004d": {
        "data_quality_status": "source_metadata_correction_required",
        "reason": "metadata says VERTEX COVER -> HITTING SET while the statement says SET COVER -> HITTING SET",
        "corrected_source_label": "SET COVER",
    },
    "02-003": {
        "data_quality_status": "quarantined_source_error",
        "reason": "the archived solution does not establish the stated source-to-target transformation",
    },
    "06-009": {
        "data_quality_status": "quarantined_source_error",
        "reason": "the target specification and archived construction use different equation semantics",
    },
    "06-025": {
        "data_quality_status": "incomplete_source_statement",
        "reason": "the entry defines the target but does not give a source construction task",
    },
    "03-022e": {
        "data_quality_status": "provenance_unverified",
        "reason": "the direction was manually supplied and lacks the geometric restrictions needed for a formal endpoint",
    },
}


class ProblemArchiveAuditError(ValueError):
    """Stable failure from archive validation or extraction."""

    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


def _fail(code: str, message: str) -> None:
    raise ProblemArchiveAuditError(code, message)


def _tagged_sha256_bytes(value: bytes) -> str:
    return "sha256:" + hashlib.sha256(value).hexdigest()


def _tagged_sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return "sha256:" + digest.hexdigest()


def _tagged_sha256_text(value: str) -> str:
    return _tagged_sha256_bytes(value.encode("utf-8"))


def _bsdtar_command(bsdtar: str | Path | None) -> str:
    if bsdtar is not None:
        command = str(bsdtar)
    else:
        command = shutil.which("bsdtar") or ""
    if not command:
        _fail("archive_tool_unavailable", "bsdtar is required to inspect problems.7z")
    return command


def _safe_member_name(raw: str) -> str:
    if not raw or "\x00" in raw or "\\" in raw:
        _fail("unsafe_archive_member", f"invalid archive member name: {raw!r}")
    path = PurePosixPath(raw)
    if path.is_absolute() or any(part in {"", ".", ".."} for part in path.parts):
        _fail("unsafe_archive_member", f"archive member escapes its root: {raw!r}")
    normalized = path.as_posix() + ("/" if raw.endswith("/") else "")
    if raw != normalized:
        _fail("unsafe_archive_member", f"archive member is not canonical: {raw!r}")
    return normalized


def list_archive_members(
    archive_path: Path, *, bsdtar: str | Path | None = None
) -> tuple[str, ...]:
    """List and traversal-check every archive member without extracting it."""

    archive = archive_path.resolve()
    if not archive.is_file():
        _fail("archive_missing", f"archive does not exist: {archive}")
    command = _bsdtar_command(bsdtar)
    completed = subprocess.run(
        [command, "-tf", str(archive)],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode != 0:
        _fail(
            "archive_list_failed",
            completed.stderr.decode("utf-8", errors="replace")[:4000],
        )
    try:
        raw_members = completed.stdout.decode("utf-8").splitlines()
    except UnicodeDecodeError as error:
        _fail("archive_member_encoding_invalid", str(error))
    members = tuple(_safe_member_name(name) for name in raw_members)
    if not members or len(set(members)) != len(members):
        _fail("archive_member_manifest_invalid", "archive is empty or repeats a member path")
    return members


def _stream_member_to_handle(
    *,
    archive_path: Path,
    member: str,
    handle: BinaryIO | None,
    capture: bool,
    max_bytes: int,
    bsdtar: str | Path | None,
) -> tuple[int, str, bytes | None]:
    if max_bytes <= 0:
        _fail("archive_member_limit_invalid", "member byte limit must be positive")
    safe_member = _safe_member_name(member)
    command = _bsdtar_command(bsdtar)
    process = subprocess.Popen(
        [command, "-xOf", str(archive_path.resolve()), safe_member],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if process.stdout is None or process.stderr is None:
        process.kill()
        _fail("archive_stream_failed", "bsdtar pipes were not created")
    digest = hashlib.sha256()
    captured = bytearray() if capture else None
    total = 0
    try:
        while True:
            chunk = process.stdout.read(1024 * 1024)
            if not chunk:
                break
            total += len(chunk)
            if total > max_bytes:
                process.kill()
                process.wait()
                _fail(
                    "archive_member_too_large",
                    f"{safe_member} exceeded the {max_bytes}-byte audit limit",
                )
            digest.update(chunk)
            if captured is not None:
                captured.extend(chunk)
            if handle is not None:
                handle.write(chunk)
        stderr = process.stderr.read().decode("utf-8", errors="replace")
        return_code = process.wait()
    finally:
        process.stdout.close()
        process.stderr.close()
    if return_code != 0:
        _fail("archive_stream_failed", f"{safe_member}: {stderr[:4000]}")
    return total, "sha256:" + digest.hexdigest(), bytes(captured) if captured is not None else None


def read_archive_member(
    archive_path: Path,
    member: str,
    *,
    max_bytes: int = DEFAULT_MAX_JSON_BYTES,
    bsdtar: str | Path | None = None,
) -> bytes:
    """Read one validated member through stdout with a hard size bound."""

    _, _, value = _stream_member_to_handle(
        archive_path=archive_path,
        member=member,
        handle=None,
        capture=True,
        max_bytes=max_bytes,
        bsdtar=bsdtar,
    )
    assert value is not None
    return value


def hash_archive_member(
    archive_path: Path,
    member: str,
    *,
    max_bytes: int = DEFAULT_MAX_MEMBER_BYTES,
    bsdtar: str | Path | None = None,
) -> tuple[int, str]:
    size, digest, _ = _stream_member_to_handle(
        archive_path=archive_path,
        member=member,
        handle=None,
        capture=False,
        max_bytes=max_bytes,
        bsdtar=bsdtar,
    )
    return size, digest


@contextmanager
def materialize_archive_members_temporarily(
    archive_path: Path,
    members: Sequence[str],
    *,
    max_member_bytes: int = DEFAULT_MAX_MEMBER_BYTES,
    bsdtar: str | Path | None = None,
) -> Iterator[Path]:
    """Safely materialize selected members under a new temporary directory.

    ``bsdtar`` never receives a destination path.  It streams each member to
    stdout, and this function writes the bytes to a traversal-checked caller
    path.  The directory is removed when the context exits.
    """

    listed = set(list_archive_members(archive_path, bsdtar=bsdtar))
    safe_members = tuple(_safe_member_name(member) for member in members)
    if len(set(safe_members)) != len(safe_members):
        _fail("archive_member_manifest_invalid", "temporary extraction repeats a member")
    missing = sorted(set(safe_members) - listed)
    if missing:
        _fail("archive_member_missing", f"archive members are absent: {missing!r}")
    with tempfile.TemporaryDirectory(prefix="np-hard-problem-archive-") as directory:
        root = Path(directory).resolve()
        for member in safe_members:
            if member.endswith("/"):
                continue
            destination = (root / PurePosixPath(member)).resolve()
            try:
                destination.relative_to(root)
            except ValueError:
                _fail("unsafe_archive_member", f"member escaped temporary root: {member}")
            destination.parent.mkdir(parents=True, exist_ok=True)
            flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
            descriptor = os.open(destination, flags, 0o600)
            try:
                with os.fdopen(descriptor, "wb") as handle:
                    _stream_member_to_handle(
                        archive_path=archive_path,
                        member=member,
                        handle=handle,
                        capture=False,
                        max_bytes=max_member_bytes,
                        bsdtar=bsdtar,
                    )
            except Exception:
                destination.unlink(missing_ok=True)
                raise
        yield root


@dataclass(frozen=True)
class ArchiveSelectionAnnotation:
    case_id: str | None
    split: str | None
    status: str
    canonical_source: str | None
    canonical_target: str | None
    endpoint_readiness: str
    formalization_cost: str | None
    selection_reason: str | None


@dataclass(frozen=True)
class ArchiveSelectionBundle:
    annotations: Mapping[str, ArchiveSelectionAnnotation]
    pdf_only_sources: tuple[Mapping[str, Any], ...]
    pdf_only_candidates: tuple[Mapping[str, Any], ...]
    source_file: str
    source_sha256: str


def _require_nonempty_string(entry: Mapping[str, Any], name: str) -> str:
    value = entry.get(name)
    if not isinstance(value, str) or not value.strip():
        _fail("archive_selection_schema_invalid", f"selection {name} must be non-empty")
    return value


def _reject_answer_fields(value: Any) -> None:
    if isinstance(value, Mapping):
        forbidden = {"statement", "hint", "solution", "answer", "construction"}
        leaked = sorted(forbidden & set(value))
        if leaked:
            _fail(
                "archive_selection_answer_leak",
                f"selection payload contains answer-bearing fields: {leaked!r}",
            )
        for nested in value.values():
            _reject_answer_fields(nested)
    elif isinstance(value, list):
        for nested in value:
            _reject_answer_fields(nested)


def load_archive_selection_bundle(path: Path) -> ArchiveSelectionBundle:
    raw = json.loads(path.read_text(encoding="utf-8"))
    expected_top = {
        "schema_version",
        "entries",
        "pdf_only_sources",
        "pdf_only_candidates",
    }
    if not isinstance(raw, dict) or set(raw) != expected_top:
        _fail("archive_selection_schema_invalid", "selection file keys drifted")
    _reject_answer_fields(raw)
    if raw["schema_version"] != PROBLEM_ARCHIVE_SELECTION_SCHEMA_V1:
        _fail("archive_selection_schema_invalid", "unsupported selection schema")
    entries = raw["entries"]
    if not isinstance(entries, list) or len(entries) != EXPECTED_SELECTION_COUNT:
        _fail(
            "archive_selection_schema_invalid",
            f"selection must contain {EXPECTED_SELECTION_COUNT} exact-edge entries",
        )
    expected = {
        "archive_id",
        "case_id",
        "split",
        "status",
        "canonical_source",
        "canonical_target",
        "endpoint_readiness",
        "formalization_cost",
        "selection_reason",
    }
    annotations: dict[str, ArchiveSelectionAnnotation] = {}
    case_ids: set[str] = set()
    split_counts: dict[str, int] = {}
    status_counts: dict[str, int] = {}
    for entry in entries:
        if not isinstance(entry, dict) or set(entry) != expected:
            _fail("archive_selection_schema_invalid", "selection entry keys drifted")
        archive_id = _require_nonempty_string(entry, "archive_id")
        case_id = _require_nonempty_string(entry, "case_id")
        split = _require_nonempty_string(entry, "split")
        status = _require_nonempty_string(entry, "status")
        canonical_source = _require_nonempty_string(entry, "canonical_source")
        canonical_target = _require_nonempty_string(entry, "canonical_target")
        readiness = _require_nonempty_string(entry, "endpoint_readiness")
        cost = _require_nonempty_string(entry, "formalization_cost")
        reason = _require_nonempty_string(entry, "selection_reason")
        if archive_id in annotations or case_id in case_ids:
            _fail(
                "archive_selection_schema_invalid",
                "selection archive IDs and case IDs must be unique",
            )
        if split not in EXPECTED_SELECTION_SPLIT_COUNTS:
            _fail("archive_selection_schema_invalid", f"unsupported split: {split}")
        prefix = {"dev": "edge-dev-", "validation": "edge-val-", "heldout": "edge-held-"}[split]
        if not case_id.startswith(prefix):
            _fail(
                "archive_selection_schema_invalid",
                f"case {case_id} is inconsistent with split {split}",
            )
        if status not in EXPECTED_SELECTION_STATUS_COUNTS or readiness != status:
            _fail(
                "archive_selection_schema_invalid",
                f"case {case_id} has an unsupported status/readiness pair",
            )
        if status == "ready" and cost not in {
            "existing-edge-reconstruction",
            "new-primitive-high",
        }:
            _fail("archive_selection_schema_invalid", f"ready case {case_id} has invalid cost")
        if status != "ready" and cost != "endpoint-formalization-required":
            _fail("archive_selection_schema_invalid", f"blocked case {case_id} has invalid cost")
        if canonical_source == canonical_target:
            _fail("archive_selection_schema_invalid", f"case {case_id} is reflexive")
        case_ids.add(case_id)
        split_counts[split] = split_counts.get(split, 0) + 1
        status_counts[status] = status_counts.get(status, 0) + 1
        annotations[archive_id] = ArchiveSelectionAnnotation(
            case_id=case_id,
            split=split,
            status=status,
            canonical_source=canonical_source,
            canonical_target=canonical_target,
            endpoint_readiness=readiness,
            formalization_cost=cost,
            selection_reason=reason,
        )
    if split_counts != EXPECTED_SELECTION_SPLIT_COUNTS:
        _fail("archive_selection_schema_invalid", "selection split counts drifted")
    if status_counts != EXPECTED_SELECTION_STATUS_COUNTS:
        _fail("archive_selection_schema_invalid", "selection status counts drifted")

    source_fields = {
        "source_member",
        "status",
        "endpoint_readiness",
        "formalization_cost",
        "selection_reason",
        "capability_weight",
    }
    pdf_sources = raw["pdf_only_sources"]
    if not isinstance(pdf_sources, list) or len(pdf_sources) != EXPECTED_PDF_ONLY_SOURCE_COUNT:
        _fail("archive_selection_schema_invalid", "PDF-only source count drifted")
    normalized_sources: list[Mapping[str, Any]] = []
    expected_members = {f"problems/{number:02d}.pdf" for number in range(8, 15)}
    observed_members: set[str] = set()
    for source in pdf_sources:
        if not isinstance(source, dict) or set(source) != source_fields:
            _fail("archive_selection_schema_invalid", "PDF-only source keys drifted")
        member = _require_nonempty_string(source, "source_member")
        if member in observed_members:
            _fail("archive_selection_schema_invalid", "PDF-only source is repeated")
        observed_members.add(member)
        if (
            source["status"] != "unstructured_pdf_only"
            or source["endpoint_readiness"] != "unassessed_answer_free_problemization"
            or source["formalization_cost"] != "unknown_until_problemization"
            or type(source["capability_weight"]) is not int
            or source["capability_weight"] != 0
        ):
            _fail("archive_selection_schema_invalid", f"invalid PDF-only source policy: {member}")
        _require_nonempty_string(source, "selection_reason")
        normalized_sources.append(dict(source))
    if observed_members != expected_members:
        _fail("archive_selection_schema_invalid", "PDF-only sources must be exactly 08.pdf through 14.pdf")

    candidate_fields = {
        "candidate_id",
        "source_members",
        "canonical_source_label",
        "canonical_target_label",
        "split",
        "status",
        "endpoint_readiness",
        "formalization_cost",
        "selection_reason",
        "capability_weight",
    }
    pdf_candidates = raw["pdf_only_candidates"]
    if not isinstance(pdf_candidates, list) or len(pdf_candidates) != EXPECTED_PDF_ONLY_CANDIDATE_COUNT:
        _fail("archive_selection_schema_invalid", "PDF-only candidate count drifted")
    normalized_candidates: list[Mapping[str, Any]] = []
    candidate_ids: set[str] = set()
    for candidate in pdf_candidates:
        if not isinstance(candidate, dict) or set(candidate) != candidate_fields:
            _fail("archive_selection_schema_invalid", "PDF-only candidate keys drifted")
        candidate_id = _require_nonempty_string(candidate, "candidate_id")
        if candidate_id in candidate_ids:
            _fail("archive_selection_schema_invalid", "PDF-only candidate ID is repeated")
        candidate_ids.add(candidate_id)
        source_members = candidate["source_members"]
        if (
            not isinstance(source_members, list)
            or not source_members
            or any(not isinstance(member, str) or member not in expected_members for member in source_members)
            or len(source_members) != len(set(source_members))
        ):
            _fail("archive_selection_schema_invalid", f"invalid source members for {candidate_id}")
        source = _require_nonempty_string(candidate, "canonical_source_label")
        target = _require_nonempty_string(candidate, "canonical_target_label")
        if source == target:
            _fail("archive_selection_schema_invalid", f"PDF candidate {candidate_id} is reflexive")
        split = _require_nonempty_string(candidate, "split")
        cost = _require_nonempty_string(candidate, "formalization_cost")
        status = _require_nonempty_string(candidate, "status")
        readiness = _require_nonempty_string(candidate, "endpoint_readiness")
        if split not in {"reserve", "frontier"} or cost not in {"high", "very_high"}:
            _fail("archive_selection_schema_invalid", f"invalid PDF candidate bucket: {candidate_id}")
        if split != ("frontier" if cost == "very_high" else "reserve"):
            _fail("archive_selection_schema_invalid", f"PDF candidate cost/split drifted: {candidate_id}")
        expected_status = (
            "blocked_answer_free_problemization"
            if readiness == "endpoints_ready_pending_identity_audit"
            else "blocked_endpoint_formalization"
        )
        if status != expected_status:
            _fail("archive_selection_schema_invalid", f"PDF candidate status drifted: {candidate_id}")
        if type(candidate["capability_weight"]) is not int or candidate["capability_weight"] != 0:
            _fail("archive_selection_schema_invalid", f"PDF candidate entered the denominator: {candidate_id}")
        _require_nonempty_string(candidate, "selection_reason")
        normalized_candidates.append(dict(candidate))
    return ArchiveSelectionBundle(
        annotations=annotations,
        pdf_only_sources=tuple(normalized_sources),
        pdf_only_candidates=tuple(normalized_candidates),
        source_file=path.name,
        source_sha256=_tagged_sha256_file(path.resolve()),
    )


def load_archive_selection_annotations(
    path: Path | None,
) -> dict[str, ArchiveSelectionAnnotation]:
    if path is None:
        return {}
    return dict(load_archive_selection_bundle(path).annotations)


def _decode_json_member(archive_path: Path, member: str, *, bsdtar: str | Path | None) -> Any:
    payload = read_archive_member(
        archive_path, member, max_bytes=DEFAULT_MAX_JSON_BYTES, bsdtar=bsdtar
    )
    try:
        return json.loads(payload.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        _fail("archive_json_invalid", f"{member}: {error}")


def _decode_text_member(
    archive_path: Path, member: str, *, bsdtar: str | Path | None
) -> str:
    payload = read_archive_member(
        archive_path, member, max_bytes=DEFAULT_MAX_JSON_BYTES, bsdtar=bsdtar
    )
    try:
        return payload.decode("utf-8")
    except UnicodeDecodeError as error:
        _fail("archive_text_invalid", f"{member}: {error}")


def _validated_structured_metadata(
    clean: Mapping[str, Any], raw: Mapping[str, Any]
) -> dict[str, Any]:
    clean_meta = clean.get("_meta")
    raw_meta = raw.get("_meta")
    clean_rows = clean.get("problems")
    raw_rows = raw.get("problems")
    if (
        not isinstance(clean_meta, Mapping)
        or set(clean_meta)
        != {"original_total", "cleaned_at", "total", "unique_directions", "unique_problems"}
        or not isinstance(raw_meta, Mapping)
        or set(raw_meta) != {"extracted_at", "total"}
        or not isinstance(clean_rows, list)
        or not isinstance(raw_rows, list)
    ):
        _fail("archive_metadata_invalid", "structured archive metadata schema drifted")
    directions: set[tuple[str, str]] = set()
    problem_labels: set[str] = set()
    for row in clean_rows:
        if not isinstance(row, Mapping):
            _fail("archive_clean_schema_invalid", "clean problem row must be an object")
        source = row.get("reduction_source")
        target = row.get("reduction_target")
        if not isinstance(source, str) or not source or not isinstance(target, str) or not target:
            _fail("archive_clean_schema_invalid", "clean problem lacks a direction")
        directions.add((source, target))
        problem_labels.update((source, target))
    computed = {
        "raw_total": len(raw_rows),
        "total": len(clean_rows),
        "unique_directions": len(directions),
        "unique_problems": len(problem_labels),
    }
    expected = {
        "raw_total": EXPECTED_RAW_PROBLEM_COUNT,
        "total": EXPECTED_CLEAN_PROBLEM_COUNT,
        "unique_directions": EXPECTED_UNIQUE_DIRECTION_COUNT,
        "unique_problems": EXPECTED_UNIQUE_PROBLEM_COUNT,
    }
    declared = {
        "raw_total": raw_meta.get("total"),
        "total": clean_meta.get("total"),
        "unique_directions": clean_meta.get("unique_directions"),
        "unique_problems": clean_meta.get("unique_problems"),
    }
    if computed != expected or declared != expected:
        _fail(
            "archive_metadata_mismatch",
            f"declared/computed archive metadata drifted: declared={declared!r}, computed={computed!r}",
        )
    if clean_meta.get("original_total") != computed["raw_total"]:
        _fail("archive_metadata_mismatch", "clean original_total does not match raw rows")
    if not isinstance(clean_meta.get("cleaned_at"), str) or not isinstance(
        raw_meta.get("extracted_at"), str
    ):
        _fail("archive_metadata_invalid", "archive timestamps are invalid")
    return {
        "valid": True,
        "declared": declared,
        "computed": computed,
        "clean_original_total_matches_raw": True,
    }


def _direction_record(source: str, target: str) -> dict[str, str]:
    value = {
        "schema_version": ARCHIVE_DIRECTION_SCHEMA_V1,
        "source_label": source,
        "target_label": target,
    }
    return {**value, "direction_id": sha256_id(value)}


def _member_hash_manifest(
    archive_path: Path,
    members: Sequence[str],
    *,
    bsdtar: str | Path | None,
) -> tuple[dict[str, Any], ...]:
    rows: list[dict[str, Any]] = []
    for member in members:
        if member.endswith("/"):
            rows.append({"path": member, "kind": "directory", "size": 0, "sha256": None})
            continue
        size, digest = hash_archive_member(archive_path, member, bsdtar=bsdtar)
        rows.append({"path": member, "kind": "file", "size": size, "sha256": digest})
    return tuple(rows)


def _archive_audit_binding_payload(report: Mapping[str, Any]) -> dict[str, Any]:
    """Return the deterministic content bound by ``audit_id``.

    In particular, this includes the scorer selection file hash and every
    split/endpoint/readiness/cost/reason annotation copied into the report.
    ``generated_at`` is intentionally excluded.
    """

    return {
        "schema_version": report.get("schema_version"),
        "archive_sha256": report.get("archive", {}).get("sha256"),
        "structured_source": report.get("structured_source"),
        "documentation_drift": report.get("documentation_drift"),
        "selection_source": report.get("selection_source"),
        "problems": report.get("problems"),
        "pdf_only_sources": report.get("pdf_only_sources"),
        "pdf_only_candidates": report.get("pdf_only_candidates"),
        "answer_isolation": report.get("answer_isolation"),
    }


def build_problem_archive_audit(
    *,
    archive_path: Path,
    selection_path: Path | None = None,
    bsdtar: str | Path | None = None,
) -> dict[str, Any]:
    """Build the complete 63-problem hash/provenance audit in memory."""

    archive = archive_path.resolve()
    members = list_archive_members(archive, bsdtar=bsdtar)
    required = {
        "problems/problems_clean.json",
        "problems/problems.json",
        "problems/README.md",
        "problems/cleaning.md",
        "problems/sources.md",
    }
    missing = sorted(required - set(members))
    if missing:
        _fail("archive_member_missing", f"required members are absent: {missing!r}")
    clean = _decode_json_member(
        archive, "problems/problems_clean.json", bsdtar=bsdtar
    )
    if not isinstance(clean, dict) or set(clean) != {"_meta", "problems"}:
        _fail("archive_clean_schema_invalid", "problems_clean.json keys drifted")
    raw_source = _decode_json_member(archive, "problems/problems.json", bsdtar=bsdtar)
    if not isinstance(raw_source, dict) or set(raw_source) != {"_meta", "problems"}:
        _fail("archive_raw_schema_invalid", "problems.json keys drifted")
    meta_validation = _validated_structured_metadata(clean, raw_source)
    raw_problems = clean["problems"]
    if not isinstance(raw_problems, list) or len(raw_problems) != EXPECTED_CLEAN_PROBLEM_COUNT:
        _fail(
            "archive_problem_count_mismatch",
            f"expected {EXPECTED_CLEAN_PROBLEM_COUNT} clean problems, got "
            f"{len(raw_problems) if isinstance(raw_problems, list) else 'non-list'}",
        )
    if selection_path is None:
        _fail(
            "archive_selection_required",
            "the frozen scorer-only selection is required for the formal archive audit",
        )
    selection = load_archive_selection_bundle(selection_path)
    annotations = dict(selection.annotations)
    problems_by_id: dict[str, Mapping[str, Any]] = {}
    direction_groups: dict[str, list[str]] = {}
    for raw in raw_problems:
        if not isinstance(raw, dict):
            _fail("archive_clean_schema_invalid", "clean problem row must be an object")
        archive_id = raw.get("id")
        source = raw.get("reduction_source")
        target = raw.get("reduction_target")
        if not all(isinstance(value, str) and value for value in (archive_id, source, target)):
            _fail("archive_clean_schema_invalid", "clean problem lacks an ID or direction")
        if archive_id in problems_by_id:
            _fail("archive_clean_schema_invalid", f"duplicate archive ID: {archive_id}")
        problems_by_id[archive_id] = raw
        direction_id = _direction_record(source, target)["direction_id"]
        direction_groups.setdefault(direction_id, []).append(archive_id)
    if len(direction_groups) != EXPECTED_UNIQUE_DIRECTION_COUNT:
        _fail(
            "archive_direction_count_mismatch",
            f"expected {EXPECTED_UNIQUE_DIRECTION_COUNT} unique directions, got {len(direction_groups)}",
        )
    unknown_annotations = sorted(set(annotations) - set(problems_by_id))
    if unknown_annotations:
        _fail(
            "archive_selection_unknown_id",
            f"selection references unknown archive IDs: {unknown_annotations!r}",
        )
    if len(annotations) != EXPECTED_SELECTION_COUNT:
        _fail("archive_selection_schema_invalid", "archive selection count drifted")
    duplicate_groups = {
        direction_id: sorted(group)
        for direction_id, group in direction_groups.items()
        if len(group) > 1
    }
    if len(duplicate_groups) != 3 or any(len(group) != 2 for group in duplicate_groups.values()):
        _fail("archive_duplicate_direction_mismatch", "expected three two-row direction variants")
    selected_duplicate_groups = 0
    for group in duplicate_groups.values():
        selected_members = sorted(set(group) & set(annotations))
        if len(selected_members) != 1 or selected_members[0] != group[0]:
            _fail(
                "archive_selection_duplicate_direction_invalid",
                f"duplicate direction must select exactly its canonical first row: {group!r}",
            )
        selected_duplicate_groups += 1

    member_rows = _member_hash_manifest(archive, members, bsdtar=bsdtar)
    member_hashes = {
        row["path"]: row["sha256"] for row in member_rows if row["sha256"] is not None
    }
    problem_rows: list[dict[str, Any]] = []
    for archive_id, raw in sorted(problems_by_id.items()):
        source = str(raw["reduction_source"])
        target = str(raw["reduction_target"])
        direction = _direction_record(source, target)
        group_ids = sorted(direction_groups[direction["direction_id"]])
        statement = raw.get("statement")
        hint = raw.get("hint")
        solution = raw.get("solution")
        if not isinstance(statement, str) or not statement.strip():
            _fail("archive_clean_schema_invalid", f"{archive_id} has no statement")
        source_file = raw.get("source_file")
        if not isinstance(source_file, str) or not _SOURCE_FILE_RE.fullmatch(source_file):
            _fail("archive_clean_schema_invalid", f"{archive_id} has an invalid source file")
        source_member = f"problems/{source_file}"
        pdf_member = f"problems/{source_file.removesuffix('.md')}.pdf"
        quality = dict(
            KNOWN_DATA_QUALITY.get(
                archive_id,
                {
                    "data_quality_status": (
                        "manual_review_required"
                        if raw.get("cleaned_from") == "manual_fix"
                        else "extracted"
                    ),
                    "reason": None,
                },
            )
        )
        annotation = annotations.get(archive_id)
        corrected_source = quality.get("corrected_source_label")
        canonical_archive_direction = _direction_record(
            str(corrected_source or source), target
        )
        row = {
            "archive_id": archive_id,
            "record_sha256": sha256_id(raw),
            "statement_sha256": _tagged_sha256_text(statement),
            "hint_sha256": _tagged_sha256_text(hint) if isinstance(hint, str) else None,
            "solution_sha256": (
                _tagged_sha256_text(solution) if isinstance(solution, str) else None
            ),
            "has_hint": isinstance(hint, str) and bool(hint.strip()),
            "has_solution": isinstance(solution, str) and bool(solution.strip()),
            "source_file": source_file,
            "source_name": raw.get("source_name"),
            "source_document_sha256": member_hashes.get(source_member),
            "source_pdf_sha256": member_hashes.get(pdf_member),
            "cleaned_from": raw.get("cleaned_from"),
            "archive_direction": direction,
            "canonical_archive_direction": canonical_archive_direction,
            "duplicate_group_id": (
                direction["direction_id"] if len(group_ids) > 1 else None
            ),
            "duplicate_group_members": group_ids,
            "capability_weight": 1 if len(group_ids) == 1 or archive_id == group_ids[0] else 0,
            "data_quality_status": quality["data_quality_status"],
            "data_quality_reason": quality.get("reason"),
            "selected_case_id": annotation.case_id if annotation else None,
            "split": annotation.split if annotation else None,
            "selection_status": annotation.status if annotation else "unselected",
            "canonical_source": annotation.canonical_source if annotation else None,
            "canonical_target": annotation.canonical_target if annotation else None,
            "endpoint_readiness": (
                annotation.endpoint_readiness if annotation else "unassessed"
            ),
            "formalization_cost": annotation.formalization_cost if annotation else None,
            "selection_reason": annotation.selection_reason if annotation else None,
        }
        problem_rows.append(row)

    pdf_only_candidates: list[dict[str, Any]] = []
    for candidate in sorted(
        selection.pdf_only_candidates, key=lambda row: str(row["candidate_id"])
    ):
        source_hashes = []
        for member in candidate["source_members"]:
            digest = member_hashes.get(member)
            if not isinstance(digest, str):
                _fail("archive_member_missing", f"PDF candidate source is absent: {member}")
            source_hashes.append({"source_member": member, "sha256": digest})
        pdf_only_candidates.append({**dict(candidate), "source_hashes": source_hashes})
    pdf_only = []
    for source in sorted(
        selection.pdf_only_sources, key=lambda row: str(row["source_member"])
    ):
        member = str(source["source_member"])
        digest = member_hashes.get(member)
        if not isinstance(digest, str):
            _fail("archive_member_missing", f"PDF-only source is absent: {member}")
        candidate_ids = sorted(
            str(candidate["candidate_id"])
            for candidate in pdf_only_candidates
            if member in candidate["source_members"]
        )
        pdf_only.append(
            {**dict(source), "sha256": digest, "candidate_ids": candidate_ids}
        )
    selected = [row for row in problem_rows if row["selected_case_id"] is not None]
    selected_direction_ids = {
        row["archive_direction"]["direction_id"] for row in selected
    }
    if len(selected_direction_ids) != EXPECTED_SELECTION_COUNT:
        _fail(
            "archive_selection_duplicate_direction_invalid",
            "selected exact-edge entries do not represent 24 unique directions",
        )
    data_quality_counts: dict[str, int] = {}
    for row in problem_rows:
        status = str(row["data_quality_status"])
        data_quality_counts[status] = data_quality_counts.get(status, 0) + 1
    clean_member_hash = member_hashes["problems/problems_clean.json"]
    raw_member_hash = member_hashes["problems/problems.json"]
    readme_member_hash = member_hashes["problems/README.md"]
    assert (
        isinstance(clean_member_hash, str)
        and isinstance(raw_member_hash, str)
        and isinstance(readme_member_hash, str)
    )
    readme_text = _decode_text_member(archive, "problems/README.md", bsdtar=bsdtar)
    readme_63_claims = len(re.findall(r"(?<![0-9])63(?![0-9])", readme_text))
    readme_64_claims = len(re.findall(r"(?<![0-9])64(?![0-9])", readme_text))
    selection_status_counts = {
        status: sum(row["selection_status"] == status for row in selected)
        for status in EXPECTED_SELECTION_STATUS_COUNTS
    }
    selection_split_counts = {
        split: sum(row["split"] == split for row in selected)
        for split in EXPECTED_SELECTION_SPLIT_COUNTS
    }
    report = {
        "schema_version": PROBLEM_ARCHIVE_AUDIT_SCHEMA_V1,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "archive": {
            "file": archive.name,
            "sha256": _tagged_sha256_file(archive),
            "member_count": len(members),
            "members": list(member_rows),
        },
        "structured_source": {
            "member": "problems/problems_clean.json",
            "sha256": clean_member_hash,
            "raw_member": "problems/problems.json",
            "raw_sha256": raw_member_hash,
            "meta": clean["_meta"],
            "raw_meta": raw_source["_meta"],
            "meta_validation": meta_validation,
        },
        "documentation_drift": {
            "member": "problems/README.md",
            "sha256": readme_member_hash,
            "authoritative_member": "problems/problems_clean.json",
            "authoritative_total": EXPECTED_CLEAN_PROBLEM_COUNT,
            "observed_numeric_claims": {
                "63": readme_63_claims,
                "64": readme_64_claims,
            },
            "status": (
                "stale_64_claim_recorded"
                if readme_64_claims > 0
                else "no_stale_64_claim_observed"
            ),
            "affects_authoritative_metrics": False,
        },
        "selection_source": {
            "file": selection.source_file,
            "sha256": selection.source_sha256,
            "schema_version": PROBLEM_ARCHIVE_SELECTION_SCHEMA_V1,
            "entry_count": len(selection.annotations),
            "pdf_only_source_count": len(selection.pdf_only_sources),
            "pdf_only_candidate_count": len(selection.pdf_only_candidates),
        },
        "metrics": {
            "raw_problem_count": EXPECTED_RAW_PROBLEM_COUNT,
            "problem_count": len(problem_rows),
            "unique_direction_count": len(direction_groups),
            "unique_problem_count": EXPECTED_UNIQUE_PROBLEM_COUNT,
            "solution_count": sum(row["has_solution"] for row in problem_rows),
            "hint_count": sum(row["has_hint"] for row in problem_rows),
            "manual_fix_count": sum(
                row["cleaned_from"] == "manual_fix" for row in problem_rows
            ),
            "duplicate_direction_count": sum(
                len(group) > 1 for group in direction_groups.values()
            ),
            "duplicate_statement_variant_count": len(problem_rows) - len(direction_groups),
            "structured_capability_weight": sum(
                row["capability_weight"] for row in problem_rows
            ),
            "selected_case_count": len(selected),
            "selected_unique_direction_count": len(selected_direction_ids),
            "selected_duplicate_direction_count": selected_duplicate_groups,
            "selection_split_counts": selection_split_counts,
            "selection_status_counts": selection_status_counts,
            "endpoint_ready_selected_count": selection_status_counts["ready"],
            "pdf_only_source_count": len(pdf_only),
            "pdf_only_candidate_count": len(pdf_only_candidates),
            "pdf_only_capability_weight": sum(
                source["capability_weight"] for source in pdf_only
            )
            + sum(candidate["capability_weight"] for candidate in pdf_only_candidates),
            "data_quality_counts": dict(sorted(data_quality_counts.items())),
        },
        "problems": problem_rows,
        "pdf_only_sources": pdf_only,
        "pdf_only_candidates": pdf_only_candidates,
        "answer_isolation": {
            "statements_embedded": False,
            "hints_embedded": False,
            "solutions_embedded": False,
            "pdf_content_embedded": False,
            "solution_hashes_scorer_only": True,
            "selection_annotations_scorer_only": True,
            "archive_must_not_enter_runner_workspace": True,
        },
    }
    report["audit_id"] = sha256_id(_archive_audit_binding_payload(report))
    return report


def write_problem_archive_audit(path: Path, report: Mapping[str, Any]) -> None:
    if report.get("schema_version") != PROBLEM_ARCHIVE_AUDIT_SCHEMA_V1:
        _fail("archive_audit_schema_invalid", "refusing to write an unsupported audit")
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def validate_problem_archive_audit(report: Mapping[str, Any]) -> None:
    """Fail closed on archive counts, selection rules, hashes, and answer isolation."""

    expected_top = {
        "schema_version",
        "generated_at",
        "archive",
        "structured_source",
        "documentation_drift",
        "selection_source",
        "metrics",
        "problems",
        "pdf_only_sources",
        "pdf_only_candidates",
        "answer_isolation",
        "audit_id",
    }
    if set(report) != expected_top or report.get("schema_version") != PROBLEM_ARCHIVE_AUDIT_SCHEMA_V1:
        _fail("archive_audit_schema_invalid", "archive audit top-level schema drifted")
    _reject_answer_fields(report)
    metrics = report["metrics"]
    problems = report["problems"]
    pdf_sources = report["pdf_only_sources"]
    pdf_candidates = report["pdf_only_candidates"]
    if (
        not isinstance(metrics, Mapping)
        or not isinstance(problems, list)
        or not isinstance(pdf_sources, list)
        or not isinstance(pdf_candidates, list)
    ):
        _fail("archive_audit_schema_invalid", "archive audit lacks typed metrics or rows")
    if len(problems) != EXPECTED_CLEAN_PROBLEM_COUNT:
        _fail("archive_problem_count_mismatch", "archive audit row count drifted")

    ids: list[str] = []
    directions: dict[str, list[Mapping[str, Any]]] = {}
    selected: list[Mapping[str, Any]] = []
    data_quality_counts: dict[str, int] = {}
    expected_problem_fields = {
        "archive_id",
        "record_sha256",
        "statement_sha256",
        "hint_sha256",
        "solution_sha256",
        "has_hint",
        "has_solution",
        "source_file",
        "source_name",
        "source_document_sha256",
        "source_pdf_sha256",
        "cleaned_from",
        "archive_direction",
        "canonical_archive_direction",
        "duplicate_group_id",
        "duplicate_group_members",
        "capability_weight",
        "data_quality_status",
        "data_quality_reason",
        "selected_case_id",
        "split",
        "selection_status",
        "canonical_source",
        "canonical_target",
        "endpoint_readiness",
        "formalization_cost",
        "selection_reason",
    }
    for row in problems:
        if not isinstance(row, Mapping) or set(row) != expected_problem_fields:
            _fail("archive_audit_schema_invalid", "archive audit problem-row schema drifted")
        if any(key in row for key in ("statement", "hint", "solution", "answer", "construction")):
            _fail("archive_answer_leak", "archive audit embeds answer-bearing source text")
        archive_id = row["archive_id"]
        if not isinstance(archive_id, str) or not archive_id:
            _fail("archive_audit_schema_invalid", "archive audit has an invalid problem ID")
        ids.append(archive_id)
        for name in ("record_sha256", "statement_sha256"):
            value = row[name]
            if not isinstance(value, str) or not _HASH_RE.fullmatch(value):
                _fail("archive_audit_schema_invalid", f"invalid {name} in archive audit")
        for name in ("hint_sha256", "solution_sha256", "source_document_sha256", "source_pdf_sha256"):
            value = row[name]
            if value is not None and (not isinstance(value, str) or not _HASH_RE.fullmatch(value)):
                _fail("archive_audit_schema_invalid", f"invalid optional {name} in archive audit")
        direction = row["archive_direction"]
        if (
            not isinstance(direction, Mapping)
            or direction.get("schema_version") != ARCHIVE_DIRECTION_SCHEMA_V1
            or not isinstance(direction.get("direction_id"), str)
            or not _HASH_RE.fullmatch(str(direction["direction_id"]))
        ):
            _fail("archive_audit_schema_invalid", f"invalid direction for {archive_id}")
        direction_id = str(direction["direction_id"])
        directions.setdefault(direction_id, []).append(row)
        if type(row["capability_weight"]) is not int or row["capability_weight"] not in {0, 1}:
            _fail("archive_audit_schema_invalid", f"invalid capability weight for {archive_id}")
        quality = row["data_quality_status"]
        if not isinstance(quality, str) or not quality:
            _fail("archive_audit_schema_invalid", f"invalid data-quality status for {archive_id}")
        data_quality_counts[quality] = data_quality_counts.get(quality, 0) + 1
        if row["selected_case_id"] is not None:
            selected.append(row)
            required_strings = (
                "selected_case_id",
                "split",
                "selection_status",
                "canonical_source",
                "canonical_target",
                "endpoint_readiness",
                "formalization_cost",
                "selection_reason",
            )
            if any(not isinstance(row[name], str) or not row[name] for name in required_strings):
                _fail("archive_audit_schema_invalid", f"selected row lacks annotations: {archive_id}")
            if row["split"] not in EXPECTED_SELECTION_SPLIT_COUNTS:
                _fail("archive_audit_schema_invalid", f"selected row has invalid split: {archive_id}")
            if (
                row["selection_status"] not in EXPECTED_SELECTION_STATUS_COUNTS
                or row["endpoint_readiness"] != row["selection_status"]
            ):
                _fail("archive_audit_schema_invalid", f"selected row status drifted: {archive_id}")
        elif any(
            row[name] is not None
            for name in (
                "split",
                "canonical_source",
                "canonical_target",
                "formalization_cost",
                "selection_reason",
            )
        ) or row["selection_status"] != "unselected" or row["endpoint_readiness"] != "unassessed":
            _fail("archive_audit_schema_invalid", f"unselected row has scorer annotations: {archive_id}")
    if len(ids) != len(set(ids)):
        _fail("archive_audit_schema_invalid", "archive audit repeats a problem ID")
    if len(directions) != EXPECTED_UNIQUE_DIRECTION_COUNT:
        _fail("archive_direction_count_mismatch", "archive audit does not contain 60 directions")
    duplicate_groups = [rows for rows in directions.values() if len(rows) > 1]
    if len(duplicate_groups) != 3 or any(len(rows) != 2 for rows in duplicate_groups):
        _fail("archive_duplicate_direction_mismatch", "duplicate direction groups drifted")
    for rows in duplicate_groups:
        group_ids = sorted(str(row["archive_id"]) for row in rows)
        if sum(int(row["capability_weight"]) for row in rows) != 1:
            _fail("archive_duplicate_direction_mismatch", f"duplicate group is double counted: {group_ids!r}")
        if any(row["duplicate_group_members"] != group_ids for row in rows):
            _fail("archive_duplicate_direction_mismatch", f"duplicate group membership drifted: {group_ids!r}")
        selected_ids = [str(row["archive_id"]) for row in rows if row["selected_case_id"] is not None]
        if selected_ids != [group_ids[0]]:
            _fail("archive_selection_duplicate_direction_invalid", f"duplicate selection drifted: {group_ids!r}")

    selected_directions = {
        str(row["archive_direction"]["direction_id"]) for row in selected
    }
    split_counts = {
        split: sum(row["split"] == split for row in selected)
        for split in EXPECTED_SELECTION_SPLIT_COUNTS
    }
    status_counts = {
        status: sum(row["selection_status"] == status for row in selected)
        for status in EXPECTED_SELECTION_STATUS_COUNTS
    }
    if (
        len(selected) != EXPECTED_SELECTION_COUNT
        or len(selected_directions) != EXPECTED_SELECTION_COUNT
        or split_counts != EXPECTED_SELECTION_SPLIT_COUNTS
        or status_counts != EXPECTED_SELECTION_STATUS_COUNTS
    ):
        _fail("archive_selection_schema_invalid", "selected exact-edge metrics drifted")

    expected_pdf_members = {f"problems/{number:02d}.pdf" for number in range(8, 15)}
    observed_pdf_members: set[str] = set()
    candidate_ids: set[str] = set()
    expected_pdf_source_fields = {
        "source_member",
        "status",
        "endpoint_readiness",
        "formalization_cost",
        "selection_reason",
        "capability_weight",
        "sha256",
        "candidate_ids",
    }
    for source in pdf_sources:
        if not isinstance(source, Mapping) or set(source) != expected_pdf_source_fields:
            _fail("archive_audit_schema_invalid", "PDF-only source row is invalid")
        member = source.get("source_member")
        if not isinstance(member, str) or member in observed_pdf_members:
            _fail("archive_audit_schema_invalid", "PDF-only source member drifted")
        observed_pdf_members.add(member)
        if (
            source.get("status") != "unstructured_pdf_only"
            or source.get("endpoint_readiness") != "unassessed_answer_free_problemization"
            or source.get("formalization_cost") != "unknown_until_problemization"
            or source.get("capability_weight") != 0
            or not isinstance(source.get("sha256"), str)
            or not _HASH_RE.fullmatch(str(source["sha256"]))
        ):
            _fail("archive_audit_schema_invalid", f"PDF-only source policy drifted: {member}")
    if len(pdf_sources) != EXPECTED_PDF_ONLY_SOURCE_COUNT or observed_pdf_members != expected_pdf_members:
        _fail("archive_audit_schema_invalid", "PDF-only source coverage drifted")
    expected_pdf_candidate_fields = {
        "candidate_id",
        "source_members",
        "canonical_source_label",
        "canonical_target_label",
        "split",
        "status",
        "endpoint_readiness",
        "formalization_cost",
        "selection_reason",
        "capability_weight",
        "source_hashes",
    }
    for candidate in pdf_candidates:
        if not isinstance(candidate, Mapping) or set(candidate) != expected_pdf_candidate_fields:
            _fail("archive_audit_schema_invalid", "PDF-only candidate row is invalid")
        candidate_id = candidate.get("candidate_id")
        if not isinstance(candidate_id, str) or candidate_id in candidate_ids:
            _fail("archive_audit_schema_invalid", "PDF-only candidate ID drifted")
        candidate_ids.add(candidate_id)
        readiness = candidate.get("endpoint_readiness")
        expected_status = (
            "blocked_answer_free_problemization"
            if readiness == "endpoints_ready_pending_identity_audit"
            else "blocked_endpoint_formalization"
        )
        cost = candidate.get("formalization_cost")
        if (
            candidate.get("capability_weight") != 0
            or candidate.get("status") != expected_status
            or cost not in {"high", "very_high"}
            or candidate.get("split") != ("frontier" if cost == "very_high" else "reserve")
        ):
            _fail("archive_audit_schema_invalid", f"PDF candidate entered denominator: {candidate_id}")
        source_members = candidate.get("source_members")
        source_hashes = candidate.get("source_hashes")
        if (
            not isinstance(source_members, list)
            or not isinstance(source_hashes, list)
            or {row.get("source_member") for row in source_hashes if isinstance(row, Mapping)}
            != set(source_members)
            or any(
                not isinstance(row, Mapping)
                or not isinstance(row.get("sha256"), str)
                or not _HASH_RE.fullmatch(str(row["sha256"]))
                for row in source_hashes
            )
        ):
            _fail("archive_audit_schema_invalid", f"PDF candidate source hashes drifted: {candidate_id}")
    if len(pdf_candidates) != EXPECTED_PDF_ONLY_CANDIDATE_COUNT:
        _fail("archive_audit_schema_invalid", "PDF-only candidate count drifted")
    for source in pdf_sources:
        member = str(source["source_member"])
        expected_candidate_ids = sorted(
            str(candidate["candidate_id"])
            for candidate in pdf_candidates
            if member in candidate["source_members"]
        )
        if source["candidate_ids"] != expected_candidate_ids:
            _fail("archive_audit_schema_invalid", f"PDF candidate links drifted: {member}")

    structured = report["structured_source"]
    drift = report["documentation_drift"]
    selection_source = report["selection_source"]
    if (
        not isinstance(structured, Mapping)
        or structured.get("meta_validation", {}).get("valid") is not True
        or structured.get("meta_validation", {}).get("declared", {}).get("total")
        != EXPECTED_CLEAN_PROBLEM_COUNT
        or structured.get("meta_validation", {}).get("computed", {}).get("total")
        != EXPECTED_CLEAN_PROBLEM_COUNT
        or structured.get("meta_validation", {}).get("computed", {}).get("unique_directions")
        != EXPECTED_UNIQUE_DIRECTION_COUNT
        or not isinstance(drift, Mapping)
        or drift.get("authoritative_total") != EXPECTED_CLEAN_PROBLEM_COUNT
        or drift.get("affects_authoritative_metrics") is not False
        or drift.get("observed_numeric_claims", {}).get("64", 0) < 1
        or not isinstance(selection_source, Mapping)
        or selection_source.get("entry_count") != EXPECTED_SELECTION_COUNT
        or selection_source.get("pdf_only_source_count") != EXPECTED_PDF_ONLY_SOURCE_COUNT
        or selection_source.get("pdf_only_candidate_count") != EXPECTED_PDF_ONLY_CANDIDATE_COUNT
        or not isinstance(selection_source.get("sha256"), str)
        or not _HASH_RE.fullmatch(str(selection_source["sha256"]))
    ):
        _fail("archive_audit_schema_invalid", "metadata/selection binding drifted")

    expected_metrics = {
        "raw_problem_count": EXPECTED_RAW_PROBLEM_COUNT,
        "problem_count": EXPECTED_CLEAN_PROBLEM_COUNT,
        "unique_direction_count": EXPECTED_UNIQUE_DIRECTION_COUNT,
        "unique_problem_count": EXPECTED_UNIQUE_PROBLEM_COUNT,
        "solution_count": sum(bool(row["has_solution"]) for row in problems),
        "hint_count": sum(bool(row["has_hint"]) for row in problems),
        "manual_fix_count": sum(row["cleaned_from"] == "manual_fix" for row in problems),
        "duplicate_direction_count": len(duplicate_groups),
        "duplicate_statement_variant_count": len(problems) - len(directions),
        "structured_capability_weight": sum(int(row["capability_weight"]) for row in problems),
        "selected_case_count": len(selected),
        "selected_unique_direction_count": len(selected_directions),
        "selected_duplicate_direction_count": len(duplicate_groups),
        "selection_split_counts": split_counts,
        "selection_status_counts": status_counts,
        "endpoint_ready_selected_count": status_counts["ready"],
        "pdf_only_source_count": len(pdf_sources),
        "pdf_only_candidate_count": len(pdf_candidates),
        "pdf_only_capability_weight": 0,
        "data_quality_counts": dict(sorted(data_quality_counts.items())),
    }
    if dict(metrics) != expected_metrics:
        _fail("archive_audit_metrics_invalid", "archive audit metrics do not match its rows")
    isolation = report["answer_isolation"]
    if not isinstance(isolation, Mapping) or any(
        isolation.get(name) is not False
        for name in ("statements_embedded", "hints_embedded", "solutions_embedded", "pdf_content_embedded")
    ) or any(
        isolation.get(name) is not True
        for name in (
            "solution_hashes_scorer_only",
            "selection_annotations_scorer_only",
            "archive_must_not_enter_runner_workspace",
        )
    ):
        _fail("archive_answer_leak", "archive answer-isolation declaration drifted")
    audit_id = report["audit_id"]
    expected_audit_id = sha256_id(_archive_audit_binding_payload(report))
    if audit_id != expected_audit_id:
        _fail("archive_audit_id_mismatch", "audit_id does not bind complete selection annotations")
