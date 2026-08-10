#!/usr/bin/env python3
"""Build the fail-closed H-K publication/reuse capability report.

The builder is deliberately evidence-only: it never runs Lean, pytest, or a
model.  It binds the passing H-J report, the reviewed publication candidates,
the active content-addressed publication catalog, four distinct 34-case formal
DeepSeek run/score pairs, and the clean-replay/drift/mutation/revalidation
audits.  Publication reuse is recomputed from case rows; aggregate scorecard
claims are not trusted on their own.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.models import sha256_id  # noqa: E402


REPORT_SCHEMA = "hardness_main_h_k_full_report_v1"
REPORT_PATH = ROOT / "Reports/MAIN_H_K_FULL_REPORT.json"
H_J_REPORT_SCHEMA = "hardness_main_h_j_full_report_v2"
PUBLICATION_CANDIDATE_SCHEMA = (
    "hardness_np_hard_publication_candidate_manifest_v1"
)
PUBLICATION_REVIEW_SCHEMA = "hardness_np_hard_publication_review_v1"
PUBLICATION_MANIFEST_SCHEMA = "hardness_np_hard_publication_manifest_v1"
PUBLICATION_CATALOG_SCHEMA = "hardness_np_hard_publication_catalog_v1"
PUBLICATION_AUDIT_SCHEMA = "hardness_np_hard_publication_audit_v1"
PUBLICATION_ACTIVATION_REPORT_SCHEMA = (
    "hardness_np_hard_publication_activation_report_v1"
)
CAPABILITY_RUN_SCHEMAS = {
    "hardness_np_hard_capability_run_v2",
    "hardness_np_hard_publication_reuse_run_v3",
}
CAPABILITY_SCORE_SCHEMAS = {
    "hardness_np_hard_capability_score_v2",
    "hardness_np_hard_publication_reuse_score_v3",
}
CAPABILITY_SPLITS = ("dev", "validation", "heldout", "frontier")
STAGE_LABELS = (
    "h-k.1-contract",
    "h-k.2-publication-activation",
    "h-k.3-publication-reuse",
    "h-k.4-drift-revalidation",
)
REUSE_STAGE_LABELS = (
    "h-k.3-publication-reuse",
    "h-k.4-drift-revalidation",
)
DIRECT_REUSE_CASES: Mapping[str, str] = {
    "cdev-au-01-tagged-three-sat-adapter": (
        "ComplexityReduction.Routes.ThreeSATToClique.IngressAdapters."
        "taggedThreeSATProblem"
    ),
    "chld-au-07-set-covering": (
        "ComplexityReduction.Presentation.SetSystem."
        "setCoveringStructuredProblem"
    ),
    "chld-au-09-feedback-arc-set": (
        "ComplexityReduction.Presentation.FeedbackArcSet.structuredProblem"
    ),
    "chld-au-10-three-dimensional-matching": (
        "ComplexityReduction.Presentation.ThreeDimensionalMatching."
        "structuredProblem"
    ),
}
TRANSITIVE_REUSE_CASES: Mapping[str, str] = {
    "chld-au-06-hitting-set": (
        "ComplexityReduction.Presentation.SetSystem.hittingSetStructuredProblem"
    ),
}
TRANSITIVE_CONSUMER_DECLARATION = (
    "ComplexityReduction.Routes.SetCoveringToHittingSet.certifiedReduction"
)
REUSE_CASES = {**DIRECT_REUSE_CASES, **TRANSITIVE_REUSE_CASES}
FORMAL_MODEL = {
    "api_key_configured": True,
    "base_url": "https://api.deepseek.com",
    "max_retries": 0,
    "max_tokens": 16000,
    "model": "deepseek-v4-flash",
    "reasoning_effort": "low",
    "temperature": 0.0,
    "timeout_seconds": 300,
}
TAGGED_HASH_RE = re.compile(r"sha256:[0-9a-f]{64}\Z")
SECRET_VALUE_RE = re.compile(
    r"(?:Bearer\s+[A-Za-z0-9._~+/=-]{8,}|"
    r"\bsk-[A-Za-z0-9_-]{16,}|"
    r"DEEPSEEK_API_KEY\s*=\s*[^\s\"']+)",
    re.IGNORECASE,
)
SENSITIVE_KEY_RE = re.compile(
    r"(?:^|_)(?:api_?key|authorization|bearer|password|secret)(?:$|_)",
    re.IGNORECASE,
)


class HKReportError(ValueError):
    """Stable fail-closed H-K report-builder error."""

    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


def _fail(code: str, message: str) -> None:
    raise HKReportError(code, message)


def _expect(condition: bool, code: str, message: str) -> None:
    if not condition:
        _fail(code, message)


def _sha256(path: Path) -> str:
    return f"sha256:{hashlib.sha256(path.read_bytes()).hexdigest()}"


def _canonical_content_hash(value: Mapping[str, Any], *, field: str) -> str:
    payload = dict(value)
    payload.pop(field, None)
    return sha256_id(payload)


def _publication_content_hash(value: Mapping[str, Any]) -> str:
    """Mirror the activation boundary's stable, timestamp-free identity."""

    payload = dict(value)
    payload.pop("publication_id", None)
    payload.pop("activated_at", None)
    return sha256_id(payload)


def _catalog_content_hash(value: Mapping[str, Any]) -> str:
    """Mirror the catalog's stable, timestamp-free identity."""

    payload = dict(value)
    payload.pop("catalog_id", None)
    payload.pop("generated_at", None)
    return sha256_id(payload)


def _assert_no_secret(value: Any, *, label: str) -> None:
    """Reject credential material while allowing boolean absence guards."""

    def walk(item: Any, trail: str) -> None:
        if isinstance(item, Mapping):
            for key, child in item.items():
                key_text = str(key)
                if (
                    SENSITIVE_KEY_RE.search(key_text)
                    and isinstance(child, str)
                    and child.strip()
                ):
                    _fail(
                        "h_k_secret_leak",
                        f"{label}:{trail}.{key_text} contains a secret",
                    )
                walk(child, f"{trail}.{key_text}")
        elif isinstance(item, list):
            for index, child in enumerate(item):
                walk(child, f"{trail}[{index}]")
        elif isinstance(item, str) and SECRET_VALUE_RE.search(item):
            _fail(
                "h_k_secret_leak",
                f"{label}:{trail} contains credential material",
            )

    walk(value, "$")


def _read_json(path: Path, *, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        _fail("h_k_evidence_unreadable", f"{label}: {error}")
    _expect(
        isinstance(value, dict),
        "h_k_evidence_schema_invalid",
        f"{label} is not a JSON object",
    )
    _assert_no_secret(value, label=label)
    return value


def _repo_path(path: Path, *, label: str, require_file: bool = True) -> Path:
    resolved = path.resolve()
    try:
        resolved.relative_to(ROOT)
    except ValueError:
        _fail("h_k_path_escape", f"{label} is outside the repository: {resolved}")
    if require_file:
        _expect(
            resolved.is_file(),
            "h_k_evidence_missing",
            f"{label} does not exist: {resolved}",
        )
    return resolved


def _reference_path(
    value: Any,
    *,
    label: str,
    relative_to: Path | None = None,
) -> Path:
    _expect(
        isinstance(value, str) and value.strip(),
        "h_k_evidence_schema_invalid",
        f"{label} path is absent",
    )
    raw = Path(value)
    if raw.is_absolute():
        candidate = raw
    elif relative_to is not None and (relative_to / raw).exists():
        candidate = relative_to / raw
    else:
        candidate = ROOT / raw
    return _repo_path(candidate, label=label)


def _parse_timestamp(value: Any, *, label: str) -> datetime:
    _expect(
        isinstance(value, str),
        "h_k_evidence_schema_invalid",
        f"{label} timestamp is missing",
    )
    try:
        parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        _fail("h_k_evidence_schema_invalid", f"{label} timestamp is invalid")
    _expect(
        parsed.tzinfo is not None,
        "h_k_evidence_schema_invalid",
        f"{label} timestamp has no timezone",
    )
    return parsed


def _parse_labeled_paths(
    values: Sequence[str], *, expected: Sequence[str], option: str
) -> dict[str, Path]:
    result: dict[str, Path] = {}
    for value in values:
        label, separator, raw_path = value.partition("=")
        if separator != "=" or not label or not raw_path:
            _fail("h_k_cli_evidence_invalid", f"{option} must use LABEL=PATH")
        if label in result:
            _fail("h_k_cli_evidence_invalid", f"{option} repeats {label}")
        result[label] = Path(raw_path)
    if set(result) != set(expected):
        _fail(
            "h_k_partial_evidence",
            f"{option} labels differ; missing={sorted(set(expected) - set(result))}, "
            f"extra={sorted(set(result) - set(expected))}",
        )
    return {label: result[label] for label in expected}


def _tagged_hash(value: Any) -> bool:
    return isinstance(value, str) and TAGGED_HASH_RE.fullmatch(value) is not None


def _record_file(path: Path, **extra: Any) -> dict[str, Any]:
    return {"file": str(path), "sha256": _sha256(path), **extra}


def _model_calls_from_run(report: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    calls: list[Mapping[str, Any]] = []
    for row in report.get("cases", []):
        if not isinstance(row, Mapping):
            continue
        raw = row.get("raw_result")
        ledgers: list[Any] = [row.get("model_call_ledger")]
        if isinstance(raw, Mapping):
            ledgers.extend(
                [
                    raw.get("model_call_ledger"),
                    raw.get("model_calls"),
                ]
            )
        ledger = next((value for value in ledgers if isinstance(value, list)), [])
        calls.extend(call for call in ledger if isinstance(call, Mapping))
    return calls


def _case_model_calls(row: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    raw = row.get("raw_result")
    values: list[Any] = [row.get("model_call_ledger")]
    if isinstance(raw, Mapping):
        values.extend([raw.get("model_call_ledger"), raw.get("model_calls")])
    ledger = next((value for value in values if isinstance(value, list)), [])
    return [call for call in ledger if isinstance(call, Mapping)]


def _validate_http_calls(
    calls: Sequence[Mapping[str, Any]], *, label: str, require_positive: bool = True
) -> tuple[str, ...]:
    if require_positive:
        _expect(
            bool(calls),
            "h_k_deepseek_http_evidence_missing",
            f"{label} has no real DeepSeek HTTP evidence",
        )
    request_ids: list[str] = []
    for index, call in enumerate(calls):
        usage = call.get("usage")
        request_id = call.get("request_id")
        _expect(
            call.get("called") is True
            and call.get("ok") is True
            and call.get("status_code") == 200
            and call.get("provider_attempts") == 1
            and isinstance(call.get("duration_seconds"), (int, float))
            and not isinstance(call.get("duration_seconds"), bool)
            and float(call["duration_seconds"]) > 0
            and _tagged_hash(request_id)
            and _tagged_hash(call.get("prompt_sha256"))
            and _tagged_hash(call.get("response_sha256"))
            and isinstance(usage, Mapping)
            and isinstance(usage.get("total_tokens"), int)
            and not isinstance(usage.get("total_tokens"), bool)
            and int(usage["total_tokens"]) > 0,
            "h_k_deepseek_http_evidence_invalid",
            f"{label} call {index} is not a successful live HTTP response",
        )
        request_ids.append(str(request_id))
    _expect(
        len(request_ids) == len(set(request_ids)),
        "h_k_deepseek_http_evidence_reused",
        f"{label} repeats a request identity",
    )
    return tuple(request_ids)


def _token_usage(calls: Iterable[Mapping[str, Any]]) -> dict[str, int]:
    totals: dict[str, int] = {}
    for call in calls:
        usage = call.get("usage")
        if not isinstance(usage, Mapping):
            continue
        for key, value in usage.items():
            if isinstance(value, int) and not isinstance(value, bool):
                totals[str(key)] = totals.get(str(key), 0) + value
    return dict(sorted(totals.items()))


def _hash_record(
    value: Any,
    *,
    label: str,
    relative_to: Path | None = None,
) -> Path:
    _expect(
        isinstance(value, Mapping) and _tagged_hash(value.get("sha256")),
        "h_k_hash_binding_mismatch",
        f"{label} lacks a tagged content hash",
    )
    path = _reference_path(value.get("file"), label=label, relative_to=relative_to)
    _expect(
        value.get("sha256") == _sha256(path),
        "h_k_hash_binding_mismatch",
        f"{label} content hash drifted",
    )
    return path


def _route_signature(route: Any) -> dict[str, Any]:
    _expect(
        isinstance(route, Mapping),
        "h_k_route_invalid",
        "publication route is absent",
    )
    atoms_value = route.get("route_atoms", route.get("atoms"))
    if not isinstance(atoms_value, list):
        atoms_value = route.get("model_nodes", [])
    atoms: list[Any] = []
    for atom in atoms_value if isinstance(atoms_value, list) else []:
        if isinstance(atom, Mapping):
            atoms.append(
                {
                    key: atom.get(key)
                    for key in ("node_id", "capability", "depends_on", "role")
                    if key in atom
                }
            )
        elif isinstance(atom, str):
            atoms.append(atom)
    signature = {
        "task_class": route.get("task_class"),
        "source": route.get("source", route.get("source_hub")),
        "target": route.get("target", route.get("canonical_endpoint")),
        "direction": route.get("direction"),
        "selected_hub": route.get("selected_hub", route.get("source_hub")),
        "terminal_node_id": route.get("terminal_node_id"),
        "final_program_node_id": route.get("final_program_node_id"),
        "atoms": atoms,
    }
    _expect(
        isinstance(signature["source"], str)
        and isinstance(signature["target"], str)
        and signature["direction"] == "source_to_target"
        and bool(atoms),
        "h_k_route_invalid",
        "publication route lacks a stable endpoint/direction/atom sequence",
    )
    return signature


def _candidate_manifest_paths(review_path: Path, review: Mapping[str, Any]) -> list[Path]:
    paths: list[Path] = []
    for row in review.get("cases", []):
        if not isinstance(row, Mapping):
            continue
        explicit = row.get("manifest_file")
        if isinstance(explicit, str) and explicit.strip():
            paths.append(
                _reference_path(
                    explicit,
                    label=f"{row.get('case_id')} candidate manifest",
                    relative_to=review_path.parent,
                )
            )
            continue
        matches = sorted(
            (review_path.parent / "candidates" / str(row.get("case_id"))).glob(
                "*/manifest.json"
            )
        )
        _expect(
            len(matches) == 1,
            "h_k_candidate_manifest_missing",
            f"{row.get('case_id')} candidate manifest is not unique",
        )
        paths.append(_repo_path(matches[0], label="candidate manifest"))
    return paths


def validate_h_j_and_candidates(
    *, h_j_report_path: Path, review_path: Path
) -> dict[str, Any]:
    h_j_path = _repo_path(h_j_report_path, label="MAIN_H_J_FULL_REPORT")
    review_file = _repo_path(review_path, label="publication review")
    h_j = _read_json(h_j_path, label="MAIN_H_J_FULL_REPORT")
    review = _read_json(review_file, label="publication review")
    _expect(
        h_j.get("schema_version") == H_J_REPORT_SCHEMA
        and h_j.get("passed") is True
        and h_j.get("report_id")
        == _canonical_content_hash(h_j, field="report_id")
        and isinstance(h_j.get("gates"), Mapping)
        and bool(h_j["gates"])
        and all(value is True for value in h_j["gates"].values()),
        "h_k_h_j_incomplete",
        "MAIN_H_J_FULL_REPORT is not passing and content-addressed",
    )
    review_cases = review.get("cases")
    _expect(
        review.get("schema_version") == PUBLICATION_REVIEW_SCHEMA
        and review.get("passed") is True
        and review.get("formal_h_j_complete") is True
        and review.get("publication_eligible") is True
        and review.get("publication_activation_performed") is False
        and review.get("candidate_count") == 4
        and review.get("review_id")
        == _canonical_content_hash(review, field="review_id")
        and isinstance(review.get("gates"), Mapping)
        and bool(review["gates"])
        and all(value is True for value in review["gates"].values())
        and isinstance(review_cases, list)
        and len(review_cases) == 4,
        "h_k_publication_review_invalid",
        "publication review is not the passing four-candidate H-J review",
    )
    review_by_id = {
        str(row.get("case_id")): row
        for row in review_cases
        if isinstance(row, Mapping)
    }
    _expect(
        set(review_by_id) == set(DIRECT_REUSE_CASES),
        "h_k_publication_interface_invalid",
        "publication review differs from the fixed four-target interface",
    )

    candidates: dict[str, dict[str, Any]] = {}
    paths = _candidate_manifest_paths(review_file, review)
    for path in paths:
        manifest = _read_json(path, label=f"candidate manifest {path}")
        case_id = manifest.get("case_id")
        _expect(
            isinstance(case_id, str)
            and case_id in review_by_id
            and case_id not in candidates,
            "h_k_candidate_manifest_invalid",
            "candidate manifest repeats or invents a publication case",
        )
        row = review_by_id[case_id]
        candidate = manifest.get("candidate")
        route = manifest.get("route")
        _expect(
            manifest.get("schema_version") == PUBLICATION_CANDIDATE_SCHEMA
            and manifest.get("state") == "shadow_review_only"
            and manifest.get("publication_eligible") is True
            and manifest.get("publication_activation_performed") is False
            and manifest.get("canonical_endpoint") == DIRECT_REUSE_CASES[case_id]
            and manifest.get("canonical_endpoint") == row.get("canonical_endpoint")
            and manifest.get("source_hub") == row.get("source_hub")
            and manifest.get("manifest_id")
            == _canonical_content_hash(manifest, field="manifest_id")
            and row.get("manifest_id") == manifest.get("manifest_id")
            and row.get("manifest_sha256") == _sha256(path)
            and row.get("candidate_content_id")
            == manifest.get("candidate_content_id")
            and _tagged_hash(manifest.get("candidate_content_id"))
            and _tagged_hash(manifest.get("canonical_identity_id"))
            and isinstance(candidate, Mapping),
            "h_k_candidate_manifest_invalid",
            f"{case_id} candidate manifest/review binding drifted",
        )
        source_path = _reference_path(
            candidate.get("source_file"),
            label=f"{case_id} candidate source",
            relative_to=path.parent,
        )
        _expect(
            candidate.get("source_sha256") == _sha256(source_path)
            and candidate.get("native_hardness_tail_present") is False,
            "h_k_candidate_source_invalid",
            f"{case_id} candidate source hash or reduction-only gate failed",
        )
        candidates[case_id] = {
            "case_id": case_id,
            "canonical_identity_id": manifest["canonical_identity_id"],
            "canonical_endpoint": manifest["canonical_endpoint"],
            "source_hub": manifest["source_hub"],
            "candidate_content_id": manifest["candidate_content_id"],
            "candidate_manifest": _record_file(
                path, manifest_id=manifest["manifest_id"]
            ),
            "candidate_source": _record_file(source_path),
            "route": _route_signature(route),
        }
    _expect(
        set(candidates) == set(DIRECT_REUSE_CASES),
        "h_k_candidate_manifest_missing",
        "not all four reviewed candidate manifests were bound",
    )
    return {
        "h_j": _record_file(h_j_path, report_id=h_j["report_id"]),
        "review": _record_file(
            review_file,
            review_id=review["review_id"],
            candidate_count=4,
        ),
        "candidates": candidates,
    }


def _manifest_asset_path(path: Path, asset: Mapping[str, Any]) -> Path:
    return _reference_path(
        asset.get("source_file", asset.get("file")),
        label=f"{path.name} published asset",
        relative_to=path.parent,
    )


def _dependency_snapshot_id(manifest: Mapping[str, Any]) -> str | None:
    snapshot = manifest.get("dependency_snapshot")
    if isinstance(snapshot, str) and _tagged_hash(snapshot):
        return snapshot
    if isinstance(snapshot, Mapping):
        for key in (
            "snapshot_id",
            "dependency_snapshot_id",
            "task_dependency_snapshot_sha256",
            "sha256",
            "closure_sha256",
        ):
            value = snapshot.get(key)
            if _tagged_hash(value):
                return str(value)
    dependencies = manifest.get("dependencies")
    if isinstance(dependencies, Mapping):
        for key in (
            "dependency_snapshot_id",
            "task_dependency_snapshot_sha256",
            "closure_sha256",
        ):
            value = dependencies.get(key)
            if _tagged_hash(value):
                return str(value)
    return None


def _discover_active_manifest_paths(
    catalog_path: Path,
    catalog: Mapping[str, Any],
    explicit_paths: Sequence[Path],
) -> list[Path]:
    if explicit_paths:
        return [_repo_path(path, label="active publication manifest") for path in explicit_paths]
    paths: list[Path] = []
    for row in catalog.get("entries", []):
        if not isinstance(row, Mapping) or row.get("status") != "active":
            continue
        value = row.get("manifest_file", row.get("publication_manifest_file"))
        if isinstance(value, str) and value.strip():
            paths.append(
                _reference_path(
                    value,
                    label="catalog publication manifest",
                    relative_to=catalog_path.parent,
                )
            )
    if paths:
        return paths
    generated = ROOT / "Lean/Reference/ComplexityReduction/Generated/Hardness"
    return sorted(generated.glob("Assets/*/manifest.json"))


def validate_publication_catalog(
    *,
    catalog_path: Path,
    aggregate_path: Path | None,
    manifest_paths: Sequence[Path],
    candidates: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any]:
    catalog_file = _repo_path(catalog_path, label="publication catalog")
    catalog = _read_json(catalog_file, label="publication catalog")
    _expect(
        catalog.get("schema_version") == PUBLICATION_CATALOG_SCHEMA
        and catalog.get("catalog_id") == _catalog_content_hash(catalog)
        and isinstance(catalog.get("entries"), list),
        "h_k_publication_catalog_invalid",
        "publication catalog is not content-addressed",
    )
    resolved_manifest_paths = _discover_active_manifest_paths(
        catalog_file, catalog, manifest_paths
    )
    _expect(
        len(resolved_manifest_paths) >= 4,
        "h_k_active_asset_count_low",
        "fewer than four active publication manifests were supplied",
    )
    publications: dict[str, dict[str, Any]] = {}
    by_publication_id: dict[str, dict[str, Any]] = {}
    for path in resolved_manifest_paths:
        resolved = _repo_path(path, label="active publication manifest")
        value = _read_json(resolved, label=f"active publication manifest {resolved}")
        case_id = value.get("case_id")
        publication_id = value.get("publication_id")
        asset = value.get("asset")
        _expect(
            value.get("schema_version") == PUBLICATION_MANIFEST_SCHEMA
            and value.get("state") == "active"
            and isinstance(case_id, str)
            and case_id in candidates
            and case_id not in publications
            and _tagged_hash(publication_id)
            and publication_id == _publication_content_hash(value)
            and value.get("candidate_id")
            == candidates[case_id]["candidate_content_id"]
            and value.get("candidate_manifest_id")
            == candidates[case_id]["candidate_manifest"]["manifest_id"]
            and value.get("canonical_identity_id")
            == candidates[case_id]["canonical_identity_id"]
            and value.get("canonical_endpoint")
            == candidates[case_id]["canonical_endpoint"]
            and value.get("source_hub") == candidates[case_id]["source_hub"]
            and isinstance(asset, Mapping),
            "h_k_publication_manifest_invalid",
            f"active publication manifest {case_id!r} drifted from review",
        )
        asset_path = _manifest_asset_path(resolved, asset)
        asset_hash = asset.get("source_sha256", asset.get("sha256"))
        dependency_id = _dependency_snapshot_id(value)
        _expect(
            asset_hash == _sha256(asset_path) and _tagged_hash(dependency_id),
            "h_k_publication_manifest_invalid",
            f"{case_id} source/dependency content address is invalid",
        )
        route = _route_signature(value.get("route"))
        _expect(
            route == candidates[case_id]["route"],
            "h_k_route_drift",
            f"{case_id} route atoms changed during activation",
        )
        normalized = {
            "case_id": case_id,
            "publication_id": publication_id,
            "canonical_identity_id": value["canonical_identity_id"],
            "canonical_endpoint": value["canonical_endpoint"],
            "source_hub": value["source_hub"],
            "manifest": _record_file(resolved),
            "asset": _record_file(
                asset_path,
                module=asset.get("module"),
                declaration=asset.get("declaration"),
            ),
            "dependency_snapshot_id": dependency_id,
            "route": route,
        }
        publications[case_id] = normalized
        by_publication_id[str(publication_id)] = normalized

    active_entries = [
        row
        for row in catalog["entries"]
        if isinstance(row, Mapping) and row.get("status") == "active"
    ]
    _expect(
        catalog.get("active_publication_count") == len(active_entries)
        and len(active_entries) >= 4,
        "h_k_active_asset_count_low",
        "catalog active publication count is inconsistent or below four",
    )
    entry_ids = [row.get("publication_id") for row in active_entries]
    _expect(
        len(entry_ids) == len(set(entry_ids))
        and set(by_publication_id).issubset(set(entry_ids)),
        "h_k_publication_catalog_invalid",
        "active manifests are not uniquely registered in the catalog",
    )
    for entry in active_entries:
        publication = by_publication_id.get(str(entry.get("publication_id")))
        if publication is None:
            continue
        _expect(
            entry.get("case_id") == publication["case_id"]
            and entry.get("canonical_identity_id")
            == publication["canonical_identity_id"]
            and entry.get("canonical_endpoint")
            == publication["canonical_endpoint"]
            and entry.get("superseded_by") is None
            and not entry.get("stale_reasons"),
            "h_k_publication_catalog_invalid",
            f"catalog entry {entry.get('publication_id')} drifted from its manifest",
        )
        _expect(
            entry.get("manifest_sha256") == publication["manifest"]["sha256"]
            and entry.get("asset_source_sha256")
            == publication["asset"]["sha256"],
            "h_k_hash_binding_mismatch",
            f"catalog entry {entry.get('publication_id')} hash bindings drifted",
        )

    aggregate_record = catalog.get("aggregate")
    if aggregate_path is not None:
        aggregate_file = _repo_path(aggregate_path, label="publication aggregate")
        if isinstance(aggregate_record, Mapping):
            _expect(
                aggregate_record.get("sha256") == _sha256(aggregate_file),
                "h_k_aggregate_hash_mismatch",
                "catalog aggregate hash differs from the active Lean aggregate",
            )
    else:
        _expect(
            isinstance(aggregate_record, Mapping),
            "h_k_aggregate_hash_mismatch",
            "publication catalog lacks an aggregate content record",
        )
        aggregate_file = _hash_record(
            aggregate_record,
            label="publication aggregate",
            relative_to=catalog_file.parent,
        )

    aggregate_source = aggregate_file.read_text(encoding="utf-8")
    _expect(
        all(
            f"import {publication['asset']['module']}" in aggregate_source
            for publication in publications.values()
        ),
        "h_k_aggregate_hash_mismatch",
        "generated aggregate does not import every active publication asset",
    )

    return {
        "catalog": _record_file(
            catalog_file,
            catalog_id=catalog["catalog_id"],
            active_publication_count=len(active_entries),
        ),
        "aggregate": _record_file(aggregate_file),
        "publications": publications,
    }


def validate_activation_report(
    *,
    activation_path: Path | None,
    static: Mapping[str, Any],
    catalog: Mapping[str, Any],
) -> dict[str, Any] | None:
    if activation_path is None:
        return None
    path = _repo_path(activation_path, label="publication activation report")
    value = _read_json(path, label="publication activation report")
    publications = value.get("publications")
    review = value.get("review")
    catalog_record = value.get("publication_catalog")
    aggregate_record = value.get("generated_aggregate")
    audits = value.get("audits")
    _expect(
        value.get("schema_version") == PUBLICATION_ACTIVATION_REPORT_SCHEMA
        and value.get("stage") == "h-k.2-publication-activation"
        and value.get("passed") is True
        and value.get("publication_activation_performed") is True
        and value.get("report_id")
        == _canonical_content_hash(value, field="report_id")
        and value.get("published_count") == 4
        and isinstance(publications, list)
        and len(publications) == 4
        and isinstance(review, Mapping)
        and review.get("review_id") == static["review"]["review_id"]
        and review.get("sha256") == static["review"]["sha256"]
        and isinstance(catalog_record, Mapping)
        and catalog_record.get("catalog_id") == catalog["catalog"]["catalog_id"]
        and catalog_record.get("sha256") == catalog["catalog"]["sha256"]
        and isinstance(aggregate_record, Mapping)
        and aggregate_record.get("sha256") == catalog["aggregate"]["sha256"]
        and isinstance(audits, Mapping)
        and isinstance(audits.get("shadow_activation"), Mapping)
        and audits["shadow_activation"].get("passed") is True
        and audits["shadow_activation"].get("clean_workspace") is True
        and audits["shadow_activation"].get("asset_count") == 4,
        "h_k_activation_report_invalid",
        "publication activation report is not bound to the four active assets",
    )
    expected = {
        row["publication_id"] for row in catalog["publications"].values()
    }
    observed = {
        row.get("publication_id")
        for row in publications
        if isinstance(row, Mapping)
    }
    _expect(
        observed == expected,
        "h_k_activation_report_invalid",
        "activation report publication IDs differ from the active catalog",
    )
    return {
        "file": str(path),
        "sha256": _sha256(path),
        "report_id": value["report_id"],
        "clean_replay_count": 4,
    }


def _case_bucket(row: Mapping[str, Any]) -> str | None:
    for key in (
        "execution_class",
        "publication_bucket",
        "reuse_bucket",
        "bucket",
    ):
        value = row.get(key)
        if isinstance(value, str):
            return value
    raw = row.get("raw_result")
    if isinstance(raw, Mapping):
        for container_key in ("publication_reuse", "reuse", "route_reuse"):
            container = raw.get(container_key)
            if isinstance(container, Mapping):
                for key in ("publication_bucket", "reuse_bucket", "bucket"):
                    value = container.get(key)
                    if isinstance(value, str):
                        return value
    outcome = row.get("outcome_class")
    return str(outcome) if outcome in {
        "direct_publication_reuse",
        "transitive_publication_reuse",
    } else None


def _reuse_payload(row: Mapping[str, Any]) -> Mapping[str, Any]:
    raw = row.get("raw_result")
    if isinstance(raw, Mapping):
        for key in ("publication_reuse", "reuse", "route_reuse"):
            value = raw.get(key)
            if isinstance(value, Mapping):
                return value
    value = row.get("publication_reuse")
    return value if isinstance(value, Mapping) else {}


def _reuse_route_signature(row: Mapping[str, Any]) -> dict[str, Any]:
    payload = _reuse_payload(row)
    route = payload.get("route", row.get("route"))
    return _route_signature(route)


def _validate_run_static_records(run: Mapping[str, Any], *, label: str) -> None:
    manifest = run.get("manifest")
    target = run.get("target_matrix")
    scope = run.get("scope_policy")
    suites = run.get("suites")
    _hash_record(manifest, label=f"{label}.manifest")
    _hash_record(target, label=f"{label}.target_matrix")
    _hash_record(scope, label=f"{label}.scope_policy")
    _expect(
        isinstance(suites, Mapping) and set(suites) == set(CAPABILITY_SPLITS),
        "h_k_hash_binding_mismatch",
        f"{label} does not bind all four suites",
    )
    for split in CAPABILITY_SPLITS:
        _hash_record(suites[split], label=f"{label}.suite.{split}")


def _validate_stage_pair(
    *,
    label: str,
    run_path: Path,
    score_path: Path,
    catalog: Mapping[str, Any],
) -> dict[str, Any]:
    run_file = _repo_path(run_path, label=f"{label} run")
    score_file = _repo_path(score_path, label=f"{label} score")
    run = _read_json(run_file, label=f"{label} run")
    score = _read_json(score_file, label=f"{label} score")
    run_cases = run.get("cases")
    score_cases = score.get("cases")
    is_v3 = run.get("schema_version") == (
        "hardness_np_hard_publication_reuse_run_v3"
    )
    _expect(
        run.get("schema_version") in CAPABILITY_RUN_SCHEMAS
        and run.get("run_valid") is True
        and run.get("selected_splits") == list(CAPABILITY_SPLITS)
        and run.get("model") == FORMAL_MODEL
        and isinstance(run_cases, list)
        and len(run_cases) == 34
        and run.get("run_id") == _canonical_content_hash(run, field="run_id"),
        "h_k_capability_run_invalid",
        f"{label} is not a valid 34-case formal DeepSeek run",
    )
    _expect(
        score.get("schema_version") in CAPABILITY_SCORE_SCHEMAS
        and score.get("run_valid") is True
        and score.get("score_valid") is True
        and score.get("run_id") == run.get("run_id")
        and isinstance(score_cases, list)
        and len(score_cases) == 34
        and score.get("score_id")
        == _canonical_content_hash(score, field="score_id"),
        "h_k_capability_score_invalid",
        f"{label} is not a valid matching 34-case score",
    )

    if is_v3:
        _expect(
            score.get("schema_version")
            == "hardness_np_hard_publication_reuse_score_v3",
            "h_k_capability_score_invalid",
            f"{label} V3 run has a non-V3 score",
        )
        manifest_path = _hash_record(run.get("manifest"), label=f"{label}.manifest")
        reuse_manifest = _read_json(manifest_path, label=f"{label} reuse manifest")
        _expect(
            reuse_manifest.get("schema_version")
            == "hardness_np_hard_publication_reuse_manifest_v3"
            and reuse_manifest.get("manifest_id")
            == _canonical_content_hash(reuse_manifest, field="manifest_id")
            and run["manifest"].get("manifest_id")
            == reuse_manifest.get("manifest_id"),
            "h_k_hash_binding_mismatch",
            f"{label} V3 reuse manifest drifted",
        )
        base_record = run.get("base_run")
        _expect(
            isinstance(base_record, Mapping),
            "h_k_capability_run_invalid",
            f"{label} V3 run lacks its base V2 report",
        )
        base_path = _reference_path(
            base_record.get("file"), label=f"{label}.base_run"
        )
        _expect(
            base_record.get("sha256") == _sha256(base_path),
            "h_k_hash_binding_mismatch",
            f"{label} base V2 report hash drifted",
        )
        effective_run = _read_json(base_path, label=f"{label} base V2 run")
        effective_cases = effective_run.get("cases")
        _expect(
            effective_run.get("schema_version")
            == "hardness_np_hard_capability_run_v2"
            and effective_run.get("run_valid") is True
            and effective_run.get("run_id") == base_record.get("run_id")
            and effective_run.get("run_id")
            == _canonical_content_hash(effective_run, field="run_id")
            and isinstance(effective_cases, list)
            and len(effective_cases) == 34
            and run.get("model") == effective_run.get("model")
            and run.get("preflight") == effective_run.get("preflight")
            and run.get("isolation") == effective_run.get("isolation")
            and run.get("parallel_execution")
            == effective_run.get("parallel_execution"),
            "h_k_capability_run_invalid",
            f"{label} base V2 evidence is invalid",
        )
        _validate_run_static_records(effective_run, label=f"{label}.base_v2")
    else:
        _expect(
            score.get("schema_version")
            == "hardness_np_hard_capability_score_v2",
            "h_k_capability_score_invalid",
            f"{label} V2 run has a non-V2 score",
        )
        effective_run = run
        effective_cases = run_cases
        _validate_run_static_records(run, label=label)

    preflight = run.get("preflight")
    isolation = run.get("isolation")
    parallel = run.get("parallel_execution")
    security = run.get("security")
    _expect(
        isinstance(preflight, Mapping)
        and preflight.get("exit_code") == 0
        and preflight.get("timed_out") is False,
        "h_k_capability_run_invalid",
        f"{label} preflight failed",
    )
    _expect(
        isinstance(isolation, Mapping)
        and isolation.get("passed") is True
        and isolation.get("forbidden_paths") == []
        and isolation.get("evaluation_oracle_present") is False
        and isolation.get("active_plan_present") is False,
        "h_k_isolation_invalid",
        f"{label} isolation failed closed",
    )
    _expect(
        isinstance(parallel, Mapping)
        and parallel.get("configured_jobs") == 4
        and parallel.get("submitted_case_tasks") == 34
        and parallel.get("maximum_concurrent_case_tasks") == 4
        and parallel.get("final_active_case_tasks") == 0
        and parallel.get("observed_parallelism") is True,
        "h_k_concurrency_not_drained",
        f"{label} does not prove jobs=4 and final active=0",
    )
    _expect(
        isinstance(security, Mapping)
        and security.get("formal_model_profile_matched") is True
        and security.get("api_key_or_authorization_absent") is True
        and security.get("fixture_model_used") is False
        and security.get("cached_or_recorded_response_used") is False
        and security.get("oracle_opened_by_runner") is False
        and security.get("oracle_passed_to_orchestrator") is False
        and security.get("evaluation_present_in_isolation") is False
        and security.get("active_plan_present_in_isolation") is False,
        "h_k_security_invalid",
        f"{label} secret/oracle/model security gates failed",
    )

    effective_by_id = {
        str(row.get("case_id")): row
        for row in effective_cases
        if isinstance(row, Mapping)
    }
    _expect(
        len(effective_by_id) == 34,
        "h_k_capability_run_invalid",
        f"{label} effective run does not contain 34 cases",
    )
    run_by_id: dict[str, Mapping[str, Any]] = {}
    identities: set[str] = set()
    for row in run_cases:
        base_row = effective_by_id.get(str(row.get("case_id"))) if isinstance(row, Mapping) else None
        _expect(
            isinstance(row, Mapping)
            and isinstance(row.get("case_id"), str)
            and row.get("case_id") not in run_by_id
            and _tagged_hash(row.get("canonical_identity_id"))
            and isinstance(base_row, Mapping)
            and base_row.get("protocol_valid") is True
            and row.get("canonical_identity_id")
            == base_row.get("canonical_identity_id")
            and row.get("canonical_problem") == base_row.get("canonical_problem")
            and row.get("model_calls") == base_row.get("model_calls"),
            "h_k_capability_run_invalid",
            f"{label} repeats/invents an invalid case row",
        )
        case_id = str(row["case_id"])
        if is_v3:
            request = row.get("publication_request")
            _expect(
                row.get("execution_class")
                in {
                    "direct_publication_reuse",
                    "transitive_publication_reuse",
                    "base_v2",
                }
                and isinstance(request, Mapping)
                and request.get("case_id") == case_id
                and request.get("canonical_identity_id")
                == row.get("canonical_identity_id")
                and request.get("request_id")
                == _canonical_content_hash(request, field="request_id"),
                "h_k_capability_run_invalid",
                f"{label}:{case_id} V3 request binding is invalid",
            )
        row_calls = _case_model_calls(base_row)
        _expect(
            isinstance(row.get("model_calls"), int)
            and not isinstance(row.get("model_calls"), bool)
            and row.get("model_calls") == len(row_calls),
            "h_k_deepseek_http_evidence_invalid",
            f"{label}:{case_id} model-call count differs from its HTTP ledger",
        )
        _validate_http_calls(
            row_calls, label=f"{label}:{case_id}", require_positive=False
        )
        run_by_id[case_id] = row
        identities.add(str(row["canonical_identity_id"]))
    _expect(
        len(run_by_id) == len(identities) == 34,
        "h_k_capability_run_invalid",
        f"{label} does not contain 34 unique identities",
    )
    all_calls = _model_calls_from_run(effective_run)
    request_ids = _validate_http_calls(all_calls, label=label)
    metrics = run.get("metrics")
    _expect(
        isinstance(metrics, Mapping)
        and metrics.get("case_count") == 34
        and metrics.get("model_calls") == len(all_calls)
        and metrics.get("token_usage") == _token_usage(all_calls),
        "h_k_deepseek_http_evidence_invalid",
        f"{label} metrics differ from real HTTP ledgers",
    )

    score_by_id: dict[str, Mapping[str, Any]] = {}
    for row in score_cases:
        case_id = row.get("case_id") if isinstance(row, Mapping) else None
        evidence_matches = (
            row.get("model_calls") == run_by_id[str(case_id)].get("model_calls")
            if isinstance(case_id, str) and case_id in run_by_id
            else False
        )
        if not is_v3 and evidence_matches:
            evidence_matches = (
                row.get("evidence_sha256")
                == run_by_id[str(case_id)].get("evidence_sha256")
            )
        if is_v3 and evidence_matches:
            evidence_matches = (
                row.get("public_status")
                == run_by_id[str(case_id)].get("public_status")
                and row.get("failure_code")
                == run_by_id[str(case_id)].get("failure_code")
                and row.get("publication_request_id")
                == run_by_id[str(case_id)]
                .get("publication_request", {})
                .get("request_id")
            )
        _expect(
            isinstance(row, Mapping)
            and isinstance(case_id, str)
            and case_id in run_by_id
            and case_id not in score_by_id
            and evidence_matches,
            "h_k_capability_score_invalid",
            f"{label} score rows drifted from the raw run",
        )
        score_by_id[case_id] = row
    _expect(
        set(score_by_id) == set(run_by_id),
        "h_k_capability_score_invalid",
        f"{label} score does not cover all run identities",
    )
    integrity = score.get("integrity")
    mutations = score.get("r0_mutation_audit")
    provenance = score.get("provenance")
    _expect(
        isinstance(integrity, Mapping)
        and bool(integrity)
        and all(value is True for value in integrity.values())
        and (
            is_v3
            or (
                isinstance(mutations, Mapping)
                and mutations.get("passed") is True
                and mutations.get("audit_count") == mutations.get("passed_count")
                and isinstance(mutations.get("audit_count"), int)
                and mutations.get("audit_count") >= 8
            )
        ),
        "h_k_capability_score_invalid",
        f"{label} scorer integrity/mutation audit failed",
    )
    _expect(
        isinstance(provenance, Mapping)
        and isinstance(provenance.get("run_report"), Mapping)
        and provenance["run_report"].get("sha256") == _sha256(run_file)
        and _reference_path(
            provenance["run_report"].get("file"),
            label=f"{label}.score.run_report",
        )
        == run_file,
        "h_k_hash_binding_mismatch",
        f"{label} score is not content-addressed to its raw run",
    )

    catalog_record = run.get("publication_catalog")
    if label != STAGE_LABELS[0]:
        _expect(
            isinstance(catalog_record, Mapping)
            and catalog_record.get("catalog_id") == catalog["catalog"]["catalog_id"]
            and catalog_record.get("sha256") == catalog["catalog"]["sha256"],
            "h_k_catalog_binding_mismatch",
            f"{label} does not bind the active publication catalog",
        )
        score_catalog = score.get("publication_catalog")
        _expect(
            isinstance(score_catalog, Mapping)
            and score_catalog.get("catalog_id") == catalog["catalog"]["catalog_id"]
            and score_catalog.get("sha256") == catalog["catalog"]["sha256"],
            "h_k_catalog_binding_mismatch",
            f"{label} score does not bind the active publication catalog",
        )

    return {
        "stage": label,
        "generated_at": run.get("generated_at"),
        "score_generated_at": score.get("generated_at"),
        "run": _record_file(run_file, run_id=run["run_id"]),
        "score": _record_file(score_file, score_id=score["score_id"]),
        "run_object": run,
        "score_object": score,
        "run_rows": run_by_id,
        "score_rows": score_by_id,
        "model_calls": len(all_calls),
        "request_ids": request_ids,
        "token_usage": _token_usage(all_calls),
        "jobs": parallel.get("configured_jobs"),
        "final_active_case_tasks": parallel.get("final_active_case_tasks"),
    }


def validate_stage_reports(
    *,
    run_paths: Mapping[str, Path],
    score_paths: Mapping[str, Path],
    catalog: Mapping[str, Any],
) -> dict[str, Any]:
    reports: list[dict[str, Any]] = []
    seen_paths: set[Path] = set()
    seen_hashes: set[str] = set()
    seen_request_ids: set[str] = set()
    previous: datetime | None = None
    total_calls = 0
    total_usage: dict[str, int] = {}
    for label in STAGE_LABELS:
        row = _validate_stage_pair(
            label=label,
            run_path=run_paths[label],
            score_path=score_paths[label],
            catalog=catalog,
        )
        run_time = _parse_timestamp(row["generated_at"], label=f"{label}.run")
        score_time = _parse_timestamp(
            row["score_generated_at"], label=f"{label}.score"
        )
        _expect(
            (previous is None or run_time > previous) and score_time >= run_time,
            "h_k_stage_evidence_order_invalid",
            "H-K run timestamps must increase and scores cannot predate runs",
        )
        previous = run_time
        for record in (row["run"], row["score"]):
            path = Path(str(record["file"])).resolve()
            digest = str(record["sha256"])
            _expect(
                path not in seen_paths and digest not in seen_hashes,
                "h_k_stage_evidence_reused",
                f"{label} reuses another stage report",
            )
            seen_paths.add(path)
            seen_hashes.add(digest)
        overlap = seen_request_ids.intersection(row["request_ids"])
        _expect(
            not overlap,
            "h_k_deepseek_http_evidence_reused",
            f"{label} reuses HTTP request identities from another stage",
        )
        seen_request_ids.update(row["request_ids"])
        total_calls += int(row["model_calls"])
        for key, value in row["token_usage"].items():
            total_usage[key] = total_usage.get(key, 0) + value
        reports.append(row)
    return {
        "stage_count": 4,
        "required_stages": list(STAGE_LABELS),
        "case_executions": 136,
        "real_deepseek_http_calls": total_calls,
        "http_200_count": total_calls,
        "request_identity_count": len(seen_request_ids),
        "token_usage": dict(sorted(total_usage.items())),
        "all_runs_valid": True,
        "all_scores_valid": True,
        "all_concurrency_drained": True,
        "all_secret_and_oracle_guards_clean": True,
        "reports": reports,
    }


def validate_reuse(
    stages: Mapping[str, Any], *, catalog: Mapping[str, Any]
) -> dict[str, Any]:
    route_fingerprints: dict[str, str] = {}
    rows: list[dict[str, Any]] = []
    for stage in stages["reports"]:
        if stage["stage"] not in REUSE_STAGE_LABELS:
            continue
        run_rows = stage["run_rows"]
        score_rows = stage["score_rows"]
        observed_direct = 0
        observed_transitive = 0
        for case_id, endpoint in REUSE_CASES.items():
            run_row = run_rows.get(case_id)
            score_row = score_rows.get(case_id)
            expected_bucket = (
                "direct_publication_reuse"
                if case_id in DIRECT_REUSE_CASES
                else "transitive_publication_reuse"
            )
            _expect(
                isinstance(run_row, Mapping)
                and isinstance(score_row, Mapping)
                and run_row.get("canonical_problem") == endpoint
                and run_row.get("model_calls") == 0
                and run_row.get("public_status") == "VERIFIED"
                and run_row.get("failure_code") is None
                and _case_bucket(run_row) == expected_bucket
                and score_row.get("model_calls") == 0
                and score_row.get("public_status") == "VERIFIED"
                and score_row.get("failure_code") is None
                and score_row.get("capability_success") is True
                and score_row.get("expected_outcome_matched", True) is True
                and _case_bucket(score_row) == expected_bucket,
                "h_k_zero_call_reuse_invalid",
                f"{stage['stage']}:{case_id} is not a successful zero-call reuse",
            )
            atoms = score_row.get("route_atoms")
            _expect(
                isinstance(atoms, list)
                and bool(atoms)
                and all(isinstance(atom, str) and atom for atom in atoms),
                "h_k_route_drift",
                f"{stage['stage']}:{case_id} lacks canonical route atoms",
            )
            digest = sha256_id(atoms)
            previous = route_fingerprints.setdefault(case_id, digest)
            _expect(
                previous == digest,
                "h_k_route_drift",
                f"{case_id} route atoms changed across reuse/revalidation",
            )
            if case_id in DIRECT_REUSE_CASES:
                publication = catalog["publications"].get(case_id)
                _expect(
                    publication is not None
                    and publication["asset"]["declaration"] in atoms,
                    "h_k_route_drift",
                    f"{case_id} route omits its active publication declaration",
                )
                observed_direct += 1
            else:
                publisher = catalog["publications"].get(
                    "chld-au-07-set-covering"
                )
                _expect(
                    publisher is not None
                    and publisher["asset"]["declaration"] in atoms
                    and TRANSITIVE_CONSUMER_DECLARATION in atoms,
                    "h_k_route_drift",
                    "HittingSet route omits publisher or consumer declaration",
                )
                observed_transitive += 1
            rows.append(
                {
                    "stage": stage["stage"],
                    "case_id": case_id,
                    "bucket": expected_bucket,
                    "canonical_endpoint": endpoint,
                    "model_calls": 0,
                    "route_fingerprint": digest,
                }
            )
        execution = stage["run_object"].get("reuse_execution")
        _expect(
            isinstance(execution, Mapping)
            and execution.get("direct_count") == observed_direct == 4
            and execution.get("transitive_count") == observed_transitive == 1
            and execution.get(
                "zero_model_call_count", execution.get("zero_call_count")
            )
            == 5
            and execution.get("zero_model_call_rate", 1.0) == 1.0,
            "h_k_reuse_scorecard_invalid",
            f"{stage['stage']} raw reuse execution summary drifted",
        )
        scorecard = stage["score_object"].get("reuse_scorecard")
        _expect(
            isinstance(scorecard, Mapping),
            "h_k_reuse_scorecard_invalid",
            f"{stage['stage']} lacks a separated reuse scorecard",
        )
        for key, expected_count in (("direct", 4), ("transitive", 1), ("combined", 5)):
            group = scorecard.get(key)
            _expect(
                isinstance(group, Mapping)
                and group.get("case_count", group.get("count")) == expected_count
                and group.get(
                    "zero_model_calls", group.get("zero_call_count")
                )
                == expected_count
                and group.get(
                    "correct", group.get("success_count", group.get("success"))
                )
                == expected_count,
                "h_k_reuse_scorecard_invalid",
                f"{stage['stage']} {key} reuse score is not 100%",
            )
        _expect(
            isinstance(stage["score_object"].get("first_authoring_scorecard"), Mapping),
            "h_k_reuse_scorecard_invalid",
            f"{stage['stage']} does not separate first authoring from reuse",
        )
        non_reuse_calls = sum(
            int(row.get("model_calls", 0))
            for case_id, row in run_rows.items()
            if case_id not in REUSE_CASES
        )
        _expect(
            non_reuse_calls > 0,
            "h_k_deepseek_http_evidence_missing",
            f"{stage['stage']} remaining lanes have no real DeepSeek calls",
        )
    return {
        "direct_target_count": 4,
        "transitive_consumer_count": 1,
        "reuse_stage_count": 2,
        "case_executions": len(rows),
        "zero_call_count": len(rows),
        "zero_call_rate": 1.0,
        "canonical_route_fingerprints": dict(sorted(route_fingerprints.items())),
        "cases": rows,
    }


def _audit_section(audit: Mapping[str, Any], *names: str) -> Mapping[str, Any]:
    for name in names:
        value = audit.get(name)
        if isinstance(value, Mapping):
            return value
    return {}


def _audit_rows(section: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    for key in ("audits", "cases", "rows", "mutations"):
        value = section.get(key)
        if isinstance(value, list):
            return [row for row in value if isinstance(row, Mapping)]
    return []


def validate_publication_audits(
    *,
    audit_path: Path | None,
    stages: Mapping[str, Any],
    activation: Mapping[str, Any] | None = None,
    catalog: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    if audit_path is not None:
        path = _repo_path(audit_path, label="publication audit")
        audit = _read_json(path, label="publication audit")
        record: dict[str, Any] = _record_file(path)
    else:
        final = stages["reports"][-1]
        value = final["run_object"].get("audits")
        if not isinstance(value, Mapping):
            value = final["score_object"].get("audits")
        _expect(
            isinstance(value, Mapping),
            "h_k_publication_audit_missing",
            "H-K.4 has no embedded or external publication audit",
        )
        audit = dict(value)
        record = {"embedded_in": final["run"]["file"]}
    _expect(
        audit.get("schema_version", PUBLICATION_AUDIT_SCHEMA)
        == PUBLICATION_AUDIT_SCHEMA
        and audit.get("passed") is True,
        "h_k_publication_audit_invalid",
        "publication audit is not passing",
    )
    if catalog is not None:
        catalog_record = audit.get("publication_catalog")
        _expect(
            isinstance(catalog_record, Mapping)
            and catalog_record.get("catalog_id")
            == catalog["catalog"]["catalog_id"]
            and catalog_record.get("sha256") == catalog["catalog"]["sha256"],
            "h_k_catalog_binding_mismatch",
            "publication audit does not bind the final publication catalog",
        )
    if "audit_id" in audit:
        _expect(
            audit.get("audit_id")
            == _canonical_content_hash(audit, field="audit_id"),
            "h_k_hash_binding_mismatch",
            "publication audit_id drifted",
        )
        record["audit_id"] = audit["audit_id"]
    if "report_id" in audit:
        _expect(
            audit.get("report_id")
            == _canonical_content_hash(audit, field="report_id"),
            "h_k_hash_binding_mismatch",
            "publication audit report_id drifted",
        )
        record["report_id"] = audit["report_id"]

    replay = _audit_section(
        audit, "clean_replay", "clean_dependency_replay", "replay_audit"
    )
    replay_rows = _audit_rows(replay)
    activation_replay_count = (
        activation.get("clean_replay_count")
        if isinstance(activation, Mapping)
        else None
    )
    replay_count = replay.get(
        "case_count",
        replay.get(
            "audit_count",
            activation_replay_count
            if isinstance(activation_replay_count, int)
            else len(replay_rows),
        ),
    )
    replay_passed = replay.get(
        "passed_count",
        replay.get(
            "replayed_count",
            activation_replay_count
            if isinstance(activation_replay_count, int)
            else len(replay_rows),
        ),
    )
    _expect(
        (replay.get("passed") is True or activation_replay_count == replay_count)
        and isinstance(replay_count, int)
        and replay_count >= 4
        and replay_passed == replay_count
        and all(row.get("passed") is True for row in replay_rows),
        "h_k_clean_replay_invalid",
        "clean dependency replay does not pass for all published assets",
    )

    mutations = _audit_section(audit, "mutation_audit", "mutations", "mutation")
    mutation_rows = _audit_rows(mutations)
    targets = {
        str(row.get("target_kind", row.get("target", row.get("kind"))))
        for row in mutation_rows
        if row.get("rejected") is True
    }
    required_targets = {"manifest", "source", "aggregate", "dependency"}
    mutation_count = mutations.get("audit_count", len(mutation_rows))
    rejected_count = mutations.get("rejected_count", mutation_count)
    _expect(
        mutations.get("passed") is True
        and isinstance(mutation_count, int)
        and mutation_count >= 4
        and rejected_count == mutation_count
        and len(mutation_rows) == mutation_count
        and required_targets.issubset(targets)
        and all(row.get("rejected") is True for row in mutation_rows),
        "h_k_mutation_audit_invalid",
        "manifest/source/aggregate/dependency mutations were not all rejected",
    )

    stale = _audit_section(
        audit, "stale_audit", "stale_detection", "staleness_audit"
    )
    stale_rows = _audit_rows(stale)
    stale_count = stale.get("audit_count", len(stale_rows))
    stale_rejected = stale.get("rejected_count", stale_count)
    _expect(
        stale.get("passed") is True
        and isinstance(stale_count, int)
        and stale_count >= 1
        and stale_rejected == stale_count
        and len(stale_rows) == stale_count
        and stale.get("silent_reuse_count", 0) == 0
        and all(row.get("rejected") is True for row in stale_rows),
        "h_k_stale_audit_invalid",
        "stale publication reuse did not fail closed",
    )

    revalidation = _audit_section(
        audit, "revalidation_audit", "revalidation", "fresh_revalidation"
    )
    revalidation_rows = _audit_rows(revalidation)
    revalidated_count = revalidation.get(
        "revalidated_count", revalidation.get("passed_count", len(revalidation_rows))
    )
    _expect(
        revalidation.get("passed") is True
        and isinstance(revalidated_count, int)
        and revalidated_count >= 1
        and len(revalidation_rows) >= revalidated_count
        and all(row.get("passed") is True for row in revalidation_rows)
        and all(
            not row.get("old_publication_id")
            or (
                _tagged_hash(row.get("old_publication_id"))
                and _tagged_hash(row.get("new_publication_id"))
                and row.get("old_publication_id") != row.get("new_publication_id")
            )
            for row in revalidation_rows
        ),
        "h_k_revalidation_audit_invalid",
        "fresh revalidation did not mint new content addresses",
    )
    return {
        "record": record,
        "clean_replay_count": replay_count,
        "mutation_rejection_count": mutation_count,
        "mutation_targets": sorted(targets),
        "stale_rejection_count": stale_count,
        "silent_stale_reuse_count": 0,
        "revalidation_count": revalidated_count,
    }


def _source_control(files: Iterable[Path]) -> dict[str, Any]:
    unique = sorted({path.resolve() for path in files if path.resolve().is_file()})
    rows = [
        {"path": str(path.relative_to(ROOT)), "sha256": _sha256(path)}
        for path in unique
    ]
    toolchain = ROOT / "Lean/lean-toolchain"
    lake_manifest = ROOT / "Lean/lake-manifest.json"
    return {
        "files": rows,
        "combined_sha256": sha256_id(rows),
        "lean_toolchain": toolchain.read_text(encoding="utf-8").strip(),
        "lean_toolchain_sha256": _sha256(toolchain),
        "lake_manifest_sha256": _sha256(lake_manifest),
    }


@dataclass(frozen=True)
class HKReportInputs:
    h_j_report: Path
    plan: Path
    publication_review: Path
    activation_report: Path | None
    publication_catalog: Path
    aggregate: Path | None
    publication_manifests: Sequence[Path]
    publication_audit: Path | None


def build_full_report(
    *,
    inputs: HKReportInputs,
    stage_run_paths: Mapping[str, Path],
    stage_score_paths: Mapping[str, Path],
) -> dict[str, Any]:
    plan = _repo_path(inputs.plan, label="active improvement plan")
    plan_text = plan.read_text(encoding="utf-8")
    _expect(
        "H-K：证明资产发布、登记与跨任务零调用复用" in plan_text,
        "h_k_plan_invalid",
        "active plan does not contain the H-K contract",
    )
    static = validate_h_j_and_candidates(
        h_j_report_path=inputs.h_j_report,
        review_path=inputs.publication_review,
    )
    catalog = validate_publication_catalog(
        catalog_path=inputs.publication_catalog,
        aggregate_path=inputs.aggregate,
        manifest_paths=inputs.publication_manifests,
        candidates=static["candidates"],
    )
    activation = validate_activation_report(
        activation_path=inputs.activation_report,
        static=static,
        catalog=catalog,
    )
    stages = validate_stage_reports(
        run_paths=stage_run_paths,
        score_paths=stage_score_paths,
        catalog=catalog,
    )
    reuse = validate_reuse(stages, catalog=catalog)
    audits = validate_publication_audits(
        audit_path=inputs.publication_audit,
        stages=stages,
        activation=activation,
        catalog=catalog,
    )

    public_stage_rows = []
    source_files: list[Path] = [
        plan,
        Path(static["h_j"]["file"]),
        Path(static["review"]["file"]),
        Path(catalog["catalog"]["file"]),
        Path(catalog["aggregate"]["file"]),
    ]
    for candidate in static["candidates"].values():
        source_files.extend(
            [
                Path(candidate["candidate_manifest"]["file"]),
                Path(candidate["candidate_source"]["file"]),
            ]
        )
    for publication in catalog["publications"].values():
        source_files.extend(
            [Path(publication["manifest"]["file"]), Path(publication["asset"]["file"])]
        )
    if inputs.publication_audit is not None:
        source_files.append(_repo_path(inputs.publication_audit, label="publication audit"))
    if inputs.activation_report is not None:
        source_files.append(
            _repo_path(inputs.activation_report, label="publication activation report")
        )
    for stage in stages["reports"]:
        source_files.extend([Path(stage["run"]["file"]), Path(stage["score"]["file"])])
        public_stage_rows.append(
            {
                key: stage[key]
                for key in (
                    "stage",
                    "generated_at",
                    "score_generated_at",
                    "run",
                    "score",
                    "model_calls",
                    "token_usage",
                    "jobs",
                    "final_active_case_tasks",
                )
            }
        )

    gates = {
        "active_h_k_plan_bound": True,
        "main_h_j_report_bound_and_passing": True,
        "four_reviewed_candidates_content_addressed": len(static["candidates"]) == 4,
        "at_least_four_active_publication_assets": len(catalog["publications"]) >= 4,
        "publication_catalog_and_aggregate_content_addressed": True,
        "all_source_and_dependency_snapshots_content_addressed": True,
        "four_distinct_full_34_case_runs_and_scores": stages["stage_count"] == 4,
        "every_stage_formal_deepseek_http_200_positive": all(
            stage["model_calls"] > 0 for stage in stages["reports"]
        ),
        "every_stage_jobs_4_and_final_active_0": all(
            stage["jobs"] == 4 and stage["final_active_case_tasks"] == 0
            for stage in stages["reports"]
        ),
        "every_stage_secret_and_oracle_guards_clean": True,
        "four_direct_and_hitting_set_transitive_zero_call_rate_100_percent": (
            reuse["zero_call_rate"] == 1.0
            and reuse["direct_target_count"] == 4
            and reuse["transitive_consumer_count"] == 1
        ),
        "remaining_lanes_retain_real_deepseek_calls": True,
        "first_authoring_and_publication_reuse_scorecards_separated": True,
        "canonical_endpoint_and_route_atoms_stable": True,
        "clean_dependency_replay_all_passed": audits["clean_replay_count"] >= 4,
        "manifest_source_aggregate_dependency_mutations_all_rejected": set(
            audits["mutation_targets"]
        ) >= {"manifest", "source", "aggregate", "dependency"},
        "stale_assets_rejected_without_silent_reuse": (
            audits["stale_rejection_count"] >= 1
            and audits["silent_stale_reuse_count"] == 0
        ),
        "fresh_revalidation_mints_new_content_addresses": (
            audits["revalidation_count"] >= 1
        ),
    }
    _expect(
        all(gates.values()),
        "h_k_gate_failed",
        "one or more H-K completion gates failed",
    )
    report: dict[str, Any] = {
        "schema_version": REPORT_SCHEMA,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "stage": "H-K-publication-registration-and-cross-task-zero-call-reuse",
        "passed": True,
        "active_plan": _record_file(plan, h_k_contract_present=True),
        "h_j_evidence": static["h_j"],
        "publication_review": static["review"],
        "publication_activation": activation,
        "publication_candidates": {
            "count": len(static["candidates"]),
            "cases": [static["candidates"][key] for key in sorted(static["candidates"])],
        },
        "publication_catalog": catalog["catalog"],
        "publication_aggregate": catalog["aggregate"],
        "active_publications": {
            "count": len(catalog["publications"]),
            "cases": [
                catalog["publications"][key]
                for key in sorted(catalog["publications"])
            ],
        },
        "substage_capability_evidence": {
            **{key: value for key, value in stages.items() if key != "reports"},
            "reports": public_stage_rows,
        },
        "publication_reuse_capability": reuse,
        "publication_audits": audits,
        "gates": gates,
        "source_control": _source_control(
            [
                *source_files,
                Path(__file__).resolve(),
                ROOT / "agent/hardness/np_hard_publication.py",
            ]
        ),
    }
    _assert_no_secret(report, label="final H-K report")
    report["report_id"] = sha256_id(report)
    return report


def _write_json(path: Path, value: Mapping[str, Any]) -> None:
    resolved = path.resolve()
    _expect(
        resolved == REPORT_PATH.resolve(),
        "h_k_output_path_invalid",
        f"H-K report must be written to {REPORT_PATH}",
    )
    temporary = resolved.with_suffix(resolved.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(resolved)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Build MAIN_H_K_FULL_REPORT.json from publication assets and four "
            "full H-K capability stages"
        )
    )
    parser.add_argument(
        "--h-j-report",
        type=Path,
        default=ROOT / "Reports/MAIN_H_J_FULL_REPORT.json",
    )
    parser.add_argument(
        "--plan", type=Path, default=ROOT / "ACTIVE_AGENT_IMPROVEMENT_PLAN.md"
    )
    parser.add_argument("--publication-review", type=Path, required=True)
    parser.add_argument(
        "--activation-report",
        type=Path,
        help="optional H-K.2 activation report binding catalog and aggregate",
    )
    parser.add_argument(
        "--publication-catalog",
        type=Path,
        default=ROOT / "Publications/NP_HARD_PUBLICATION_CATALOG.json",
    )
    parser.add_argument(
        "--aggregate",
        type=Path,
        default=(
            ROOT
            / "Lean/Reference/ComplexityReduction/Generated/Hardness/Aggregate.lean"
        ),
    )
    parser.add_argument(
        "--publication-manifest",
        action="append",
        type=Path,
        default=[],
        help="optional explicit active manifest; otherwise discover from catalog",
    )
    parser.add_argument(
        "--publication-audit",
        type=Path,
        default=ROOT / "Publications/H_K_4_PUBLICATION_AUDIT_REPORT.json",
        help="optional standalone audit; otherwise use H-K.4 embedded audits",
    )
    parser.add_argument(
        "--stage-run",
        action="append",
        required=True,
        metavar="STAGE=PATH",
        help="repeat for all four 34-case H-K raw reports",
    )
    parser.add_argument(
        "--stage-score",
        action="append",
        required=True,
        metavar="STAGE=PATH",
        help="repeat for all four 34-case H-K score reports",
    )
    parser.add_argument("--output", type=Path, default=REPORT_PATH)
    return parser


def main() -> int:
    arguments = build_parser().parse_args()
    try:
        runs = _parse_labeled_paths(
            arguments.stage_run, expected=STAGE_LABELS, option="--stage-run"
        )
        scores = _parse_labeled_paths(
            arguments.stage_score, expected=STAGE_LABELS, option="--stage-score"
        )
        report = build_full_report(
            inputs=HKReportInputs(
                h_j_report=arguments.h_j_report,
                plan=arguments.plan,
                publication_review=arguments.publication_review,
                activation_report=arguments.activation_report,
                publication_catalog=arguments.publication_catalog,
                aggregate=arguments.aggregate,
                publication_manifests=arguments.publication_manifest,
                publication_audit=arguments.publication_audit,
            ),
            stage_run_paths=runs,
            stage_score_paths=scores,
        )
        _write_json(arguments.output, report)
    except (HKReportError, OSError, UnicodeError, ValueError) as error:
        print(
            json.dumps(
                {
                    "passed": False,
                    "output_written": False,
                    "failure_code": getattr(
                        error, "code", "h_k_report_build_failed"
                    ),
                    "error": str(error),
                },
                ensure_ascii=False,
            )
        )
        return 1
    print(
        json.dumps(
            {
                "passed": True,
                "output_written": True,
                "report": str(arguments.output.resolve()),
                "report_id": report["report_id"],
                "gate_count": len(report["gates"]),
                "active_publications": report["active_publications"]["count"],
                "reuse_zero_call_rate": report["publication_reuse_capability"][
                    "zero_call_rate"
                ],
            },
            ensure_ascii=False,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
