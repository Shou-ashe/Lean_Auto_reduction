#!/usr/bin/env python3
"""Build the fail-closed H-I capability-boundary report.

The builder is deliberately evidence-only: it never runs Lean, pytest, or a
model.  Every input path is supplied explicitly, all content-addressed inputs
are rebound to their current bytes, and the final report is written only after
every gate succeeds.  In particular, unified R0/R1 regression evidence is kept
separate from the C0/F0 capability scorecards and always has weight zero.
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

from agent.hardness.models import canonical_json, sha256_id  # noqa: E402
from agent.hardness.np_hard_archive_audit import (  # noqa: E402
    validate_problem_archive_audit,
)
from agent.hardness.np_hard_capability import (  # noqa: E402
    CAPABILITY_RUN_SCHEMA_V1,
    CAPABILITY_SCORE_SCHEMA_V1,
    CAPABILITY_SPLITS,
    load_capability_bundle,
    load_capability_oracle,
)
from agent.hardness.np_hard_exact_edge import (  # noqa: E402
    EXACT_EDGE_RUN_REPORT_SCHEMA_V1,
    EXACT_EDGE_SCORE_REPORT_SCHEMA_V1,
    load_exact_edge_manifest,
    load_exact_edge_oracle,
)
from agent.hardness.np_hard_unified_benchmark import (  # noqa: E402
    load_public_r1_coverage_suite,
    load_unified_registry,
    load_unified_taxonomy,
)


REPORT_SCHEMA = "hardness_main_h_i_full_report_v1"
REPORT_PATH = ROOT / "Reports/MAIN_H_I_FULL_REPORT.json"
UNIFIED_REPORT_SCHEMA = "hardness_np_hard_unified_benchmark_report_v1"
RELEASE_REPORT_SCHEMA = "hardness_np_hard_release_real_run_v2"
PUBLIC_R1_REPORT_SCHEMA = "hardness_np_hard_public_r1_coverage_report_v1"
LEGACY_REPORT_SCHEMA = "hardness_benchmark_result_v2"
CAPABILITY_EXPECTED_COUNTS = {
    "dev": 8,
    "validation": 8,
    "heldout": 16,
    "frontier": 2,
}
STAGE_LABELS = (
    "h-i.1-registry",
    "h-i.2-capability",
    "h-i.3-scoring",
    "h-i.4-exact-edge",
    "h-i.5-freeze",
)
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
FORMAL_MANIFEST_MODEL = {"provider": "DeepSeek", **FORMAL_MODEL}
FORMAL_MANIFEST_MODEL.pop("api_key_configured")
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


class HIReportError(ValueError):
    """Stable fail-closed error emitted by the H-I report builder."""

    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


def _fail(code: str, message: str) -> None:
    raise HIReportError(code, message)


def _sha256(path: Path, *, tagged: bool = False) -> str:
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    return f"sha256:{digest}" if tagged else digest


def _read_json(path: Path, *, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        _fail("h_i_evidence_unreadable", f"{label}: {error}")
    if not isinstance(value, dict):
        _fail("h_i_evidence_schema_invalid", f"{label} is not a JSON object")
    _assert_no_secret(value, label=label)
    return value


def _repo_file(path: Path, *, label: str) -> Path:
    resolved = path.resolve()
    try:
        resolved.relative_to(ROOT)
    except ValueError:
        _fail("h_i_path_escape", f"{label} is outside the repository: {resolved}")
    if not resolved.is_file():
        _fail("h_i_evidence_missing", f"{label} does not exist: {resolved}")
    return resolved


def _repo_reference(value: Any, *, label: str) -> Path:
    if not isinstance(value, str) or not value.strip():
        _fail("h_i_evidence_schema_invalid", f"{label} is not a path")
    candidate = Path(value)
    return _repo_file(candidate if candidate.is_absolute() else ROOT / candidate, label=label)


def _expect(condition: bool, code: str, message: str) -> None:
    if not condition:
        _fail(code, message)


def _assert_no_secret(value: Any, *, label: str) -> None:
    """Reject credentials while allowing boolean `*_configured/absent` evidence."""

    def walk(item: Any, trail: str) -> None:
        if isinstance(item, Mapping):
            for key, child in item.items():
                key_text = str(key)
                if (
                    SENSITIVE_KEY_RE.search(key_text)
                    and isinstance(child, str)
                    and child.strip()
                ):
                    _fail("h_i_secret_leak", f"{label}:{trail}.{key_text} contains a secret")
                walk(child, f"{trail}.{key_text}")
        elif isinstance(item, list):
            for index, child in enumerate(item):
                walk(child, f"{trail}[{index}]")
        elif isinstance(item, str) and SECRET_VALUE_RE.search(item):
            _fail("h_i_secret_leak", f"{label}:{trail} contains credential material")

    walk(value, "$")


def _parse_timestamp(value: Any, *, label: str) -> datetime:
    if not isinstance(value, str):
        _fail("h_i_evidence_schema_invalid", f"{label} timestamp is missing")
    try:
        parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        _fail("h_i_evidence_schema_invalid", f"{label} timestamp is invalid")
    if parsed.tzinfo is None:
        _fail("h_i_evidence_schema_invalid", f"{label} timestamp has no timezone")
    return parsed


def _parse_labeled_paths(
    values: Sequence[str], *, expected: Sequence[str], option: str
) -> dict[str, Path]:
    result: dict[str, Path] = {}
    for value in values:
        label, separator, raw_path = value.partition("=")
        if separator != "=" or not label or not raw_path:
            _fail("h_i_cli_evidence_invalid", f"{option} must use LABEL=PATH")
        if label in result:
            _fail("h_i_cli_evidence_invalid", f"{option} repeats {label}")
        result[label] = Path(raw_path)
    if set(result) != set(expected):
        _fail(
            "h_i_partial_evidence",
            f"{option} labels differ; missing={sorted(set(expected) - set(result))}, "
            f"extra={sorted(set(result) - set(expected))}",
        )
    return {label: result[label] for label in expected}


def _canonical_content_hash(value: Mapping[str, Any], *, field: str) -> str:
    payload = dict(value)
    payload.pop(field, None)
    return sha256_id(payload)


def _token_usage(calls: Iterable[Mapping[str, Any]]) -> dict[str, int]:
    totals: dict[str, int] = {}
    for call in calls:
        usage = call.get("usage")
        if not isinstance(usage, Mapping):
            continue
        for name, amount in usage.items():
            if isinstance(amount, int) and not isinstance(amount, bool):
                totals[name] = totals.get(name, 0) + amount
    return dict(sorted(totals.items()))


def _model_calls(report: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    calls: list[Mapping[str, Any]] = []
    rows = report.get("cases")
    if not isinstance(rows, list):
        return calls
    for row in rows:
        if not isinstance(row, Mapping):
            continue
        ledger = row.get("model_call_ledger")
        if not isinstance(ledger, list):
            continue
        calls.extend(call for call in ledger if isinstance(call, Mapping))
    return calls


def _validate_http_calls(
    calls: Sequence[Mapping[str, Any]], *, expected_count: int, label: str
) -> tuple[str, ...]:
    _expect(
        len(calls) == expected_count,
        "h_i_deepseek_http_evidence_invalid",
        f"{label} expected {expected_count} call ledgers, found {len(calls)}",
    )
    request_ids: list[str] = []
    for index, call in enumerate(calls):
        request_id = call.get("request_id")
        usage = call.get("usage")
        _expect(
            call.get("called") is True
            and call.get("ok") is True
            and call.get("status_code") == 200
            and call.get("provider_attempts") == 1
            and isinstance(call.get("duration_seconds"), (int, float))
            and float(call["duration_seconds"]) > 0
            and isinstance(request_id, str)
            and TAGGED_HASH_RE.fullmatch(request_id) is not None
            and isinstance(usage, Mapping)
            and isinstance(usage.get("total_tokens"), int)
            and not isinstance(usage.get("total_tokens"), bool)
            and int(usage["total_tokens"]) > 0,
            "h_i_deepseek_http_evidence_invalid",
            f"{label} call {index} is not a successful live HTTP response",
        )
        request_ids.append(request_id)
    _expect(
        len(set(request_ids)) == len(request_ids),
        "h_i_deepseek_http_evidence_reused",
        f"{label} repeats a model request identity",
    )
    return tuple(request_ids)


@dataclass(frozen=True)
class StaticEvidencePaths:
    plan: Path
    registry: Path
    taxonomy: Path
    capability_manifest: Path
    capability_oracle: Path
    target_matrix: Path
    public_r1_suite: Path
    exact_edge_manifest: Path
    exact_edge_oracle: Path
    problem_archive: Path
    archive_selection: Path
    archive_audit: Path


def validate_static_assets(paths: StaticEvidencePaths) -> dict[str, Any]:
    """Validate all frozen, non-runtime H-I assets and their cross-bindings."""

    resolved = {
        name: _repo_file(path, label=name)
        for name, path in paths.__dict__.items()
    }
    plan_text = resolved["plan"].read_text(encoding="utf-8")
    _expect(
        "H-I 已由 `Reports/MAIN_H_I_FULL_REPORT.json` 证明通过" in plan_text
        and "MAIN_H_I_FULL_REPORT.json" in plan_text
        and "44 个公共 identity" in plan_text
        and "24 个唯一方向" in plan_text,
        "h_i_active_plan_drift",
        "the active plan no longer contains the frozen H-I contract",
    )
    if SECRET_VALUE_RE.search(plan_text):
        _fail("h_i_secret_leak", "active plan contains credential material")

    registry = load_unified_registry(resolved["registry"], root=ROOT)
    taxonomy = load_unified_taxonomy(
        resolved["taxonomy"], registry=registry, root=ROOT
    )
    _expect(
        len(registry.cases) == 59
        and registry.default_jobs == 4
        and all(case.capability_weight == 0 for case in registry.cases),
        "h_i_registry_contract_invalid",
        "unified registry must contain 59 zero-weight logical cases at jobs=4",
    )
    taxonomy_registry = _repo_reference(taxonomy.get("registry"), label="taxonomy.registry")
    _expect(
        taxonomy_registry == resolved["registry"],
        "h_i_hash_binding_mismatch",
        "taxonomy points at another registry",
    )
    assets = taxonomy.get("assets")
    _expect(
        isinstance(assets, list)
        and len(assets) == 3
        and all(
            isinstance(asset, Mapping)
            and asset.get("capability_weight") == 0
            and asset.get("public_capability_case_count") == 0
            for asset in assets
        ),
        "h_i_taxonomy_weight_invalid",
        "legacy/public R1 taxonomy assets must all have capability weight zero",
    )

    capability_bundle = load_capability_bundle(
        resolved["capability_manifest"], root=ROOT, verify_oracle=True
    )
    _expect(
        capability_bundle.manifest.oracle.path == resolved["capability_oracle"],
        "h_i_hash_binding_mismatch",
        "capability oracle path differs from the explicit input",
    )
    _expect(
        capability_bundle.manifest.target_matrix.path == resolved["target_matrix"],
        "h_i_hash_binding_mismatch",
        "capability target matrix path differs from the explicit input",
    )
    _expect(
        capability_bundle.manifest.required_model_profile == FORMAL_MANIFEST_MODEL,
        "h_i_model_profile_invalid",
        "capability manifest is not frozen to the formal DeepSeek profile",
    )
    capability_oracle = load_capability_oracle(
        resolved["capability_oracle"], bundle=capability_bundle
    )
    capability_cases: dict[str, tuple[str, str, str]] = {}
    capability_tier_counts = {"C0": 0, "F0": 0}
    for split in CAPABILITY_SPLITS:
        suite = capability_bundle.suites[split]
        _expect(
            len(suite.cases) == CAPABILITY_EXPECTED_COUNTS[split],
            "h_i_identity_partition_invalid",
            f"capability {split} count drifted",
        )
        for case in suite.cases:
            oracle_case = capability_oracle[case.case_id]
            tier = "F0" if oracle_case.tier == "F0-frontier" else "C0"
            capability_tier_counts[tier] += 1
            capability_cases[case.case_id] = (case.problem, tier, split)
    _expect(
        capability_tier_counts == {"C0": 32, "F0": 2},
        "h_i_identity_partition_invalid",
        f"expected C0=32/F0=2, found {capability_tier_counts}",
    )

    public_r1 = load_public_r1_coverage_suite(resolved["public_r1_suite"])
    r1_cases = {
        case["case_id"]: (case["problem"], "R1", "public-r1")
        for case in public_r1
    }
    _expect(
        len(r1_cases) == 10,
        "h_i_identity_partition_invalid",
        "public R1 suite must contain ten unique identities",
    )

    target_matrix = _read_json(resolved["target_matrix"], label="target matrix")
    matrix_rows = target_matrix.get("identities")
    _expect(
        target_matrix.get("identity_count") == 44
        and isinstance(matrix_rows, list)
        and len(matrix_rows) == 44,
        "h_i_identity_partition_invalid",
        "target matrix must contain exactly 44 identities",
    )
    matrix_identities = {
        row.get("canonical_declaration")
        for row in matrix_rows
        if isinstance(row, Mapping) and isinstance(row.get("canonical_declaration"), str)
    }
    owned = {value[0] for value in capability_cases.values()}
    r1_owned = {value[0] for value in r1_cases.values()}
    _expect(
        len(owned) == 34
        and len(r1_owned) == 10
        and owned.isdisjoint(r1_owned)
        and owned | r1_owned == matrix_identities,
        "h_i_identity_partition_invalid",
        "32 C0 + 2 F0 + 10 R1 does not exactly partition the 44 target identities",
    )
    ownership = taxonomy.get("public_identity_ownership")
    taxonomy_ownership = {
        row.get("case_id"): (row.get("public_identity"), row.get("tier"))
        for row in ownership
        if isinstance(row, Mapping)
    } if isinstance(ownership, list) else {}
    expected_ownership = {
        case_id: (identity, tier)
        for case_id, (identity, tier, _) in {**capability_cases, **r1_cases}.items()
    }
    _expect(
        taxonomy_ownership == expected_ownership,
        "h_i_identity_partition_invalid",
        "taxonomy ownership differs from the frozen 44-identity partition",
    )

    exact_manifest = load_exact_edge_manifest(resolved["exact_edge_manifest"])
    exact_oracle = load_exact_edge_oracle(resolved["exact_edge_oracle"])
    _expect(
        exact_manifest.oracle_sha256 == exact_oracle.sha256,
        "h_i_hash_binding_mismatch",
        "exact-edge manifest/oracle hash binding drifted",
    )
    exact_cases = {
        case.case_id: case
        for suite in exact_manifest.suites.values()
        for case in suite.cases
    }
    _expect(
        len(exact_cases) == len(exact_oracle.cases) == 24
        and set(exact_cases) == set(exact_oracle.cases)
        and {split: len(exact_manifest.suites[split].cases) for split in ("dev", "validation", "heldout")}
        == {"dev": 6, "validation": 6, "heldout": 12},
        "h_i_exact_edge_partition_invalid",
        "exact-edge cases must be split 6/6/12 over 24 unique directions",
    )
    status_counts: dict[str, int] = {}
    for case_id, policy in exact_oracle.cases.items():
        public = exact_cases[case_id]
        _expect(
            policy.split == public.split
            and policy.canonical_source == public.source
            and policy.canonical_target == public.target,
            "h_i_exact_edge_partition_invalid",
            f"exact-edge endpoint drift for {case_id}",
        )
        status_counts[policy.status] = status_counts.get(policy.status, 0) + 1
    _expect(
        all(exact_oracle.cases[case.case_id].status == "ready" for case in exact_manifest.suites["dev"].cases),
        "h_i_exact_edge_partition_invalid",
        "all six exact-edge development endpoints must be ready",
    )

    archive = _read_json(resolved["archive_audit"], label="problem archive audit")
    validate_problem_archive_audit(archive)
    archive_binding = archive.get("archive")
    selection_binding = archive.get("selection_source")
    _expect(
        isinstance(archive_binding, Mapping)
        and _repo_reference(archive_binding.get("file"), label="problem archive")
        == resolved["problem_archive"]
        and archive_binding.get("sha256")
        == _sha256(resolved["problem_archive"], tagged=True),
        "h_i_hash_binding_mismatch",
        "problem archive bytes differ from PROBLEM_ARCHIVE_AUDIT.json",
    )
    _expect(
        isinstance(selection_binding, Mapping)
        and Path(str(selection_binding.get("file"))).name
        == resolved["archive_selection"].name
        and selection_binding.get("sha256")
        == _sha256(resolved["archive_selection"], tagged=True),
        "h_i_hash_binding_mismatch",
        "archive selection bytes differ from PROBLEM_ARCHIVE_AUDIT.json",
    )
    archive_metrics = archive.get("metrics")
    _expect(
        isinstance(archive_metrics, Mapping)
        and archive_metrics.get("problem_count") == 63
        and archive_metrics.get("unique_direction_count") == 60
        and archive_metrics.get("duplicate_direction_count") == 3
        and archive_metrics.get("duplicate_statement_variant_count") == 3
        and archive_metrics.get("selected_case_count") == 24
        and archive_metrics.get("selected_unique_direction_count") == 24
        and archive_metrics.get("pdf_only_source_count") == 7
        and archive_metrics.get("pdf_only_capability_weight") == 0,
        "h_i_archive_contract_invalid",
        "archive counts, duplicates, selection, or PDF weight drifted",
    )
    selected = {
        row.get("selected_case_id"): row
        for row in archive.get("problems", [])
        if isinstance(row, Mapping) and isinstance(row.get("selected_case_id"), str)
    }
    _expect(
        set(selected) == set(exact_cases),
        "h_i_archive_contract_invalid",
        "archive selected cases differ from the 24 exact-edge cases",
    )
    selection_rows = {
        str(entry.get("case_id")): entry
        for entry in _read_json(
            resolved["archive_selection"], label="archive selection"
        ).get("entries", [])
        if isinstance(entry, Mapping) and isinstance(entry.get("case_id"), str)
    }
    for case_id, row in selected.items():
        initial = selection_rows.get(case_id)
        _expect(
            initial is not None
            and row.get("split") == initial.get("split")
            and row.get("selection_status") == initial.get("status")
            and row.get("canonical_source") == initial.get("canonical_source")
            and row.get("canonical_target") == initial.get("canonical_target"),
            "h_i_archive_contract_invalid",
            f"archive exact-edge annotation drift for {case_id}",
        )
    duplicate_rows = [
        row
        for row in archive.get("problems", [])
        if isinstance(row, Mapping) and row.get("duplicate_group_id") is not None
    ]
    duplicate_groups = {
        row["duplicate_group_id"] for row in duplicate_rows
    }
    _expect(
        len(duplicate_groups) == 3
        and len(duplicate_rows) == 6
        and all(
            sum(
                int(row.get("capability_weight") == 1)
                for row in duplicate_rows
                if row.get("duplicate_group_id") == group
            ) == 1
            and sum(
                int(row.get("capability_weight") == 0)
                for row in duplicate_rows
                if row.get("duplicate_group_id") == group
            ) == 1
            for group in duplicate_groups
        ),
        "h_i_archive_contract_invalid",
        "the three duplicate directions must each have one scored canonical and one zero-weight variant",
    )
    _expect(
        all(
            isinstance(row, Mapping) and row.get("capability_weight") == 0
            for row in archive.get("pdf_only_sources", [])
        )
        and all(
            isinstance(row, Mapping) and row.get("capability_weight") == 0
            for row in archive.get("pdf_only_candidates", [])
        ),
        "h_i_archive_contract_invalid",
        "PDF-only sources or candidates entered a capability denominator",
    )

    return {
        "active_plan": {
            "file": str(resolved["plan"]),
            "sha256": _sha256(resolved["plan"]),
            "h_i_contract_present": True,
        },
        "registry_taxonomy": {
            "registry": {
                "file": str(resolved["registry"]),
                "sha256": _sha256(resolved["registry"]),
                "logical_cases": len(registry.cases),
                "capability_weight": 0,
                "default_jobs": registry.default_jobs,
            },
            "taxonomy": {
                "file": str(resolved["taxonomy"]),
                "sha256": _sha256(resolved["taxonomy"]),
                "suite_count": len(taxonomy.get("suite_inventory", [])),
                "owned_public_identities": len(taxonomy_ownership),
                "legacy_assets_capability_weight": 0,
            },
        },
        "identity_partition": {
            "target_matrix": {
                "file": str(resolved["target_matrix"]),
                "sha256": _sha256(resolved["target_matrix"]),
                "matrix_id": target_matrix.get("matrix_id"),
            },
            "c0": 32,
            "f0": 2,
            "r1_public": 10,
            "total": 44,
            "canonical_identity_disjoint": True,
            "matrix_exhaustive": True,
        },
        "capability_contract": {
            "manifest": {
                "file": str(resolved["capability_manifest"]),
                "sha256": _sha256(resolved["capability_manifest"], tagged=True),
            },
            "oracle": {
                "file": str(resolved["capability_oracle"]),
                "sha256": _sha256(resolved["capability_oracle"], tagged=True),
                "runner_access": "forbidden",
            },
            "split_counts": CAPABILITY_EXPECTED_COUNTS,
            "formal_model_profile": FORMAL_MANIFEST_MODEL,
        },
        "exact_edge_archive": {
            "manifest": {
                "file": str(resolved["exact_edge_manifest"]),
                "sha256": exact_manifest.sha256,
            },
            "oracle": {
                "file": str(resolved["exact_edge_oracle"]),
                "sha256": exact_oracle.sha256,
            },
            "archive_audit": {
                "file": str(resolved["archive_audit"]),
                "sha256": _sha256(resolved["archive_audit"], tagged=True),
                "audit_id": archive.get("audit_id"),
            },
            "problem_archive": {
                "file": str(resolved["problem_archive"]),
                "sha256": _sha256(resolved["problem_archive"], tagged=True),
            },
            "archive_selection": {
                "file": str(resolved["archive_selection"]),
                "sha256": _sha256(resolved["archive_selection"], tagged=True),
            },
            "unique_directions": 24,
            "split_counts": {"dev": 6, "validation": 6, "heldout": 12},
            "status_counts": dict(sorted(status_counts.items())),
            "duplicate_direction_count": 3,
            "duplicate_statement_variant_count": 3,
            "pdf_only_source_count": 7,
            "pdf_only_capability_weight": 0,
        },
        "source_files": resolved,
        "capability_bundle": capability_bundle,
        "exact_manifest_object": exact_manifest,
    }


def validate_stage_benchmarks(
    paths: Mapping[str, Path], *, registry_path: Path, taxonomy_path: Path
) -> dict[str, Any]:
    """Validate five fresh, non-reused DeepSeek unified `all` runs."""

    expected_http_records = 12 * len(STAGE_LABELS)
    expected_registry_hash = _sha256(registry_path)
    expected_taxonomy_hash = _sha256(taxonomy_path)
    rows: list[dict[str, Any]] = []
    report_paths: set[Path] = set()
    report_hashes: set[str] = set()
    production_paths: set[Path] = set()
    production_hashes: set[str] = set()
    previous_time: datetime | None = None
    total_tokens: dict[str, int] = {}
    http_evidence_records = 0

    for label in STAGE_LABELS:
        path = _repo_file(paths[label], label=f"stage benchmark {label}")
        report = _read_json(path, label=f"stage benchmark {label}")
        report_hash = _sha256(path, tagged=True)
        generated_at = _parse_timestamp(report.get("generated_at"), label=label)
        _expect(
            previous_time is None or generated_at > previous_time,
            "h_i_stage_evidence_order_invalid",
            "stage benchmark timestamps must be strictly increasing",
        )
        previous_time = generated_at
        _expect(
            path not in report_paths and report_hash not in report_hashes,
            "h_i_stage_evidence_reused",
            f"{label} reuses another stage benchmark report",
        )
        report_paths.add(path)
        report_hashes.add(report_hash)

        counts = report.get("counts")
        parallel = report.get("parallel_execution")
        trust = report.get("trust_boundary")
        reproducibility = report.get("reproducibility")
        _expect(
            report.get("schema_version") == UNIFIED_REPORT_SCHEMA
            and report.get("benchmark_id") == "np-hard-regression-v2"
            and report.get("selector") == "all"
            and report.get("run_valid") is True
            and report.get("passed") is True
            and report.get("formal_profile_matched") is True,
            "h_i_stage_benchmark_invalid",
            f"{label} is not a valid unified all run",
        )
        _expect(
            isinstance(counts, Mapping)
            and counts.get("logical_cases") == 59
            and counts.get("case_executions") == 59
            and counts.get("matched_executions") == 59
            and counts.get("failed_executions") == 0
            and counts.get("model_calls") == 12
            and counts.get("capability_weight") == 0,
            "h_i_stage_benchmark_invalid",
            f"{label} did not execute the de-duplicated 59/59 regression registry",
        )
        _expect(
            report.get("model_configuration") == FORMAL_MODEL,
            "h_i_model_profile_invalid",
            f"{label} model profile drifted",
        )
        _expect(
            isinstance(parallel, Mapping)
            and parallel.get("configured_jobs") == 4
            and parallel.get("maximum_concurrent_case_tasks") == 4
            and all(
                value == 0
                for key, value in parallel.items()
                if key.endswith("final_active_case_tasks")
            ),
            "h_i_concurrency_not_drained",
            f"{label} concurrency did not return to zero",
        )
        _expect(
            isinstance(trust, Mapping)
            and trust.get("capability_weight_zero") is True
            and trust.get("compatibility_views_are_aliases_only") is True
            and trust.get("component_reports_passed") is True
            and trust.get("formal_model_profile_fail_closed") is True
            and trust.get("logical_case_deduplication") is True
            and trust.get("production_round_count") == 1
            and trust.get("public_r1_identity_count") == 10
            and trust.get("public_r1_zero_model_calls") is True,
            "h_i_stage_benchmark_invalid",
            f"{label} trust-boundary gates did not all pass",
        )
        _expect(
            isinstance(reproducibility, Mapping)
            and reproducibility.get("registry_sha256") == expected_registry_hash
            and reproducibility.get("taxonomy_sha256") == expected_taxonomy_hash,
            "h_i_hash_binding_mismatch",
            f"{label} was run against stale registry/taxonomy bytes",
        )

        components = report.get("component_reports")
        _expect(
            isinstance(components, Mapping)
            and set(components) == {"legacy", "production", "public_r1"},
            "h_i_stage_benchmark_invalid",
            f"{label} component report bindings are incomplete",
        )
        component_paths = {
            name: _repo_reference(value, label=f"{label}.{name}")
            for name, value in components.items()
        }
        legacy = _read_json(component_paths["legacy"], label=f"{label}.legacy")
        production = _read_json(
            component_paths["production"], label=f"{label}.production"
        )
        public_r1 = _read_json(
            component_paths["public_r1"], label=f"{label}.public_r1"
        )
        _expect(
            legacy.get("schema_version") == LEGACY_REPORT_SCHEMA
            and legacy.get("passed") == legacy.get("total") == 37
            and legacy.get("failed") == 0,
            "h_i_stage_benchmark_invalid",
            f"{label} legacy de-duplicated component is invalid",
        )
        public_metrics = public_r1.get("metrics")
        public_parallel = public_r1.get("parallel_execution")
        _expect(
            public_r1.get("schema_version") == PUBLIC_R1_REPORT_SCHEMA
            and public_r1.get("passed") is True
            and public_r1.get("fresh_output") is True
            and public_r1.get("resume") is False
            and isinstance(public_metrics, Mapping)
            and public_metrics.get("case_count") == public_metrics.get("matched_case_count") == 10
            and public_metrics.get("model_calls") == 0
            and isinstance(public_parallel, Mapping)
            and public_parallel.get("final_active_case_tasks") == 0
            and public_parallel.get("observed_parallelism") is True,
            "h_i_stage_benchmark_invalid",
            f"{label} public R1 component is invalid",
        )

        production_path = component_paths["production"]
        production_hash = _sha256(production_path, tagged=True)
        _expect(
            production_path not in production_paths
            and production_hash not in production_hashes,
            "h_i_stage_evidence_reused",
            f"{label} reuses another production component",
        )
        production_paths.add(production_path)
        production_hashes.add(production_hash)
        metrics = production.get("metrics")
        production_parallel = production.get("parallel_execution")
        security = production.get("security")
        _expect(
            production.get("schema_version") == RELEASE_REPORT_SCHEMA
            and production.get("passed") is True
            and production.get("fresh_output") is True
            and production.get("resume") is False
            and production.get("round") == 1
            and production.get("model") == FORMAL_MODEL,
            "h_i_stage_benchmark_invalid",
            f"{label} production component is not a fresh formal run",
        )
        _expect(
            isinstance(metrics, Mapping)
            and metrics.get("case_count") == metrics.get("matched_case_count") == 12
            and metrics.get("real_api_calls") == 12,
            "h_i_deepseek_http_evidence_invalid",
            f"{label} production metrics do not record 12 real calls",
        )
        _expect(
            isinstance(production_parallel, Mapping)
            and production_parallel.get("configured_jobs") == 4
            and production_parallel.get("submitted_case_tasks") == 12
            and production_parallel.get("maximum_concurrent_case_tasks") == 4
            and production_parallel.get("final_active_case_tasks") == 0
            and production_parallel.get("observed_parallelism") is True,
            "h_i_concurrency_not_drained",
            f"{label} production concurrency evidence is invalid",
        )
        _expect(
            isinstance(security, Mapping)
            and security.get("secret_absent") is True
            and security.get("nonstandard_axiom_acceptance_count") == 0
            and security.get("oracle_or_gold_prompt_acceptance_count") == 0,
            "h_i_secret_leak",
            f"{label} production security gates failed",
        )
        calls = _model_calls(production)
        request_ids = _validate_http_calls(calls, expected_count=12, label=label)
        # request_id is a deterministic request-content identity, so the same
        # frozen prompt legitimately has the same ID in another fresh run.
        # Freshness across stages is instead bound by distinct aggregate and
        # production report paths/hashes plus fresh_output/resume evidence.
        http_evidence_records += len(request_ids)
        usage = _token_usage(calls)
        _expect(
            metrics.get("token_usage") == usage,
            "h_i_deepseek_http_evidence_invalid",
            f"{label} token totals differ from its call ledgers",
        )
        for key, amount in usage.items():
            total_tokens[key] = total_tokens.get(key, 0) + amount
        rows.append(
            {
                "stage": label,
                "file": str(path),
                "sha256": report_hash,
                "generated_at": report["generated_at"],
                "logical_cases": 59,
                "case_executions": 59,
                "matched_executions": 59,
                "capability_weight": 0,
                "real_deepseek_http_calls": len(calls),
                "http_200_count": len(calls),
                "token_usage": usage,
                "maximum_concurrent_case_tasks": 4,
                "final_active_case_tasks": 0,
                "component_hashes": {
                    name: _sha256(component_path, tagged=True)
                    for name, component_path in component_paths.items()
                },
            }
        )

    _expect(
        http_evidence_records == expected_http_records,
        "h_i_deepseek_http_evidence_invalid",
        f"H-I stage benchmarks must provide {expected_http_records} live HTTP evidence records",
    )
    return {
        "required_stages": list(STAGE_LABELS),
        "stage_count": len(STAGE_LABELS),
        "reports": rows,
        "logical_case_executions": 59 * len(STAGE_LABELS),
        "real_deepseek_http_calls": expected_http_records,
        "http_200_count": expected_http_records,
        "http_evidence_record_count": http_evidence_records,
        "request_identity_count_per_stage": 12,
        "token_usage": dict(sorted(total_tokens.items())),
        "all_concurrency_drained": True,
        "capability_weight": 0,
    }


def validate_capability_reports(
    run_paths: Mapping[str, Path],
    score_paths: Mapping[str, Path],
    *,
    static: Mapping[str, Any],
) -> dict[str, Any]:
    bundle = static["capability_bundle"]
    manifest_path = bundle.manifest.path
    manifest_hash = _sha256(manifest_path, tagged=True)
    oracle_path = bundle.manifest.oracle.path
    oracle_hash = _sha256(oracle_path, tagged=True)
    split_rows: list[dict[str, Any]] = []
    outcome_totals: dict[str, dict[str, int]] = {}
    total_model_calls = 0
    total_tokens: dict[str, int] = {}
    all_case_ids: set[str] = set()

    for split in CAPABILITY_SPLITS:
        run_path = _repo_file(run_paths[split], label=f"capability {split} run")
        score_path = _repo_file(score_paths[split], label=f"capability {split} score")
        run = _read_json(run_path, label=f"capability {split} run")
        score = _read_json(score_path, label=f"capability {split} score")
        expected_ids = {case.case_id for case in bundle.suites[split].cases}
        run_cases = run.get("cases")
        score_cases = score.get("cases")
        run_ids = {
            row.get("case_id")
            for row in run_cases
            if isinstance(row, Mapping) and isinstance(row.get("case_id"), str)
        } if isinstance(run_cases, list) else set()
        score_ids = {
            row.get("case_id")
            for row in score_cases
            if isinstance(row, Mapping) and isinstance(row.get("case_id"), str)
        } if isinstance(score_cases, list) else set()
        _expect(
            run.get("schema_version") == CAPABILITY_RUN_SCHEMA_V1
            and run.get("benchmark_id") == "np-hard-capability-v1"
            and run.get("run_valid") is True
            and run.get("selected_splits") == [split]
            and run.get("model") == FORMAL_MODEL
            and run_ids == expected_ids
            and len(run_cases) == len(expected_ids),
            "h_i_capability_run_invalid",
            f"capability {split} run is invalid or incomplete",
        )
        _expect(
            run.get("run_id") == _canonical_content_hash(run, field="run_id"),
            "h_i_hash_binding_mismatch",
            f"capability {split} run_id does not bind its content",
        )
        manifest_record = run.get("manifest")
        parallel = run.get("parallel_execution")
        security = run.get("security")
        metrics = run.get("metrics")
        _expect(
            isinstance(manifest_record, Mapping)
            and manifest_record.get("sha256") == manifest_hash
            and _repo_reference(manifest_record.get("file"), label=f"{split}.manifest") == manifest_path
            and manifest_record.get("oracle_opened_by_runner") is False,
            "h_i_hash_binding_mismatch",
            f"capability {split} manifest binding drifted",
        )
        _expect(
            isinstance(metrics, Mapping)
            and metrics.get("case_count") == CAPABILITY_EXPECTED_COUNTS[split],
            "h_i_capability_run_invalid",
            f"capability {split} metrics count drifted",
        )
        _expect(
            isinstance(parallel, Mapping)
            and parallel.get("configured_jobs") == 4
            and parallel.get("submitted_case_tasks") == CAPABILITY_EXPECTED_COUNTS[split]
            and parallel.get("final_active_case_tasks") == 0
            and parallel.get("observed_parallelism") is True,
            "h_i_concurrency_not_drained",
            f"capability {split} concurrency did not drain",
        )
        _expect(
            isinstance(security, Mapping)
            and security.get("formal_model_profile_matched") is True
            and security.get("api_key_or_authorization_absent") is True
            and security.get("fixture_model_used") is False
            and security.get("cached_or_recorded_response_used") is False
            and security.get("oracle_opened_by_runner") is False
            and security.get("oracle_passed_to_orchestrator") is False
            and security.get("active_plan_present_in_isolation") is False
            and security.get("evaluation_present_in_isolation") is False
            and security.get("problem_archive_present_in_isolation") is False,
            "h_i_capability_security_invalid",
            f"capability {split} security/isolation gates failed",
        )
        _expect(
            score.get("schema_version") == CAPABILITY_SCORE_SCHEMA_V1
            and score.get("benchmark_id") == "np-hard-capability-v1"
            and score.get("run_valid") is True
            and score.get("score_valid") is True
            and score.get("run_id") == run.get("run_id")
            and score_ids == expected_ids
            and len(score_cases) == len(expected_ids),
            "h_i_capability_score_invalid",
            f"capability {split} score is invalid or incomplete",
        )
        _expect(
            score.get("score_id") == _canonical_content_hash(score, field="score_id"),
            "h_i_hash_binding_mismatch",
            f"capability {split} score_id does not bind its content",
        )
        integrity = score.get("integrity")
        mutations = score.get("r0_mutation_audit")
        safety = score.get("safety")
        provenance = score.get("provenance")
        _expect(
            isinstance(integrity, Mapping)
            and integrity
            and all(value is True for value in integrity.values())
            and isinstance(mutations, Mapping)
            and mutations.get("passed") is True
            and mutations.get("audit_count") == mutations.get("passed_count") == 8,
            "h_i_capability_score_invalid",
            f"capability {split} integrity or R0 mutation audit failed",
        )
        _expect(
            isinstance(safety, Mapping)
            and safety.get("wrong_direction_acceptance_count") == 0
            and safety.get("wrong_endpoint_acceptance_count") == 0
            and safety.get("nonstandard_axiom_acceptance_count") == 0
            and safety.get("oracle_leakage_count") == 0,
            "h_i_capability_safety_regression",
            f"capability {split} accepted unsafe evidence",
        )
        _expect(
            isinstance(provenance, Mapping)
            and isinstance(provenance.get("manifest"), Mapping)
            and provenance["manifest"].get("sha256") == manifest_hash
            and isinstance(provenance.get("oracle"), Mapping)
            and provenance["oracle"].get("sha256") == oracle_hash
            and isinstance(provenance.get("run_report"), Mapping)
            and _repo_reference(provenance["run_report"].get("file"), label=f"{split}.run_report") == run_path
            and provenance["run_report"].get("sha256") == _sha256(run_path, tagged=True),
            "h_i_hash_binding_mismatch",
            f"capability {split} scorer provenance drifted",
        )
        score_metrics = score.get("metrics")
        _expect(
            isinstance(score_metrics, Mapping),
            "h_i_capability_score_invalid",
            f"capability {split} score metrics are absent",
        )
        total_model_calls += int(score_metrics.get("model_calls") or 0)
        usage = score_metrics.get("token_usage")
        if isinstance(usage, Mapping):
            for key, amount in usage.items():
                if isinstance(amount, int) and not isinstance(amount, bool):
                    total_tokens[key] = total_tokens.get(key, 0) + amount
        outcome = score.get("outcome_matrix")
        if isinstance(outcome, Mapping):
            for tier, statuses in outcome.items():
                if not isinstance(statuses, Mapping):
                    continue
                bucket = outcome_totals.setdefault(str(tier), {})
                for status, amount in statuses.items():
                    if isinstance(amount, int) and not isinstance(amount, bool):
                        bucket[str(status)] = bucket.get(str(status), 0) + amount
        all_case_ids.update(expected_ids)
        split_rows.append(
            {
                "split": split,
                "run": {
                    "file": str(run_path),
                    "sha256": _sha256(run_path, tagged=True),
                    "run_id": run.get("run_id"),
                    "run_valid": True,
                    "case_count": len(expected_ids),
                    "parallel_execution": parallel,
                    "public_outcomes": {
                        key: value
                        for key, value in metrics.items()
                        if key.endswith("_count")
                    },
                },
                "score": {
                    "file": str(score_path),
                    "sha256": _sha256(score_path, tagged=True),
                    "score_id": score.get("score_id"),
                    "score_valid": True,
                    "metrics": score_metrics,
                    "boundary": score.get("boundary"),
                    "safety": safety,
                },
            }
        )

    _expect(
        len(all_case_ids)
        == sum(CAPABILITY_EXPECTED_COUNTS[split] for split in CAPABILITY_SPLITS),
        "h_i_identity_partition_invalid",
        "capability reports did not cover every selected C0/F0 identity exactly once",
    )
    return {
        "scoring_source": "independent C0/F0 scorer only",
        "regression_scores_used": False,
        "run_valid": True,
        "score_valid": True,
        "case_count": len(all_case_ids),
        "split_reports": split_rows,
        "outcome_matrix": {
            tier: dict(sorted(statuses.items()))
            for tier, statuses in sorted(outcome_totals.items())
        },
        "model_calls": total_model_calls,
        "token_usage": dict(sorted(total_tokens.items())),
        "security_guardrails": {
            "wrong_direction_acceptance_count": 0,
            "wrong_endpoint_acceptance_count": 0,
            "nonstandard_axiom_acceptance_count": 0,
            "oracle_leakage_count": 0,
        },
        "all_concurrency_drained": True,
        "all_r0_mutations_passed": True,
    }


def validate_exact_edge_dev_reports(
    run_path: Path, score_path: Path, *, static: Mapping[str, Any]
) -> dict[str, Any]:
    manifest = static["exact_manifest_object"]
    run_file = _repo_file(run_path, label="exact-edge dev run")
    score_file = _repo_file(score_path, label="exact-edge dev score")
    run = _read_json(run_file, label="exact-edge dev run")
    score = _read_json(score_file, label="exact-edge dev score")
    dev_suite = manifest.suites["dev"]
    expected_ids = {case.case_id for case in dev_suite.cases}
    run_cases = run.get("cases")
    score_cases = score.get("cases")
    run_ids = {
        row.get("case_id")
        for row in run_cases
        if isinstance(row, Mapping) and isinstance(row.get("case_id"), str)
    } if isinstance(run_cases, list) else set()
    score_ids = {
        row.get("case_id")
        for row in score_cases
        if isinstance(row, Mapping) and isinstance(row.get("case_id"), str)
    } if isinstance(score_cases, list) else set()
    _expect(
        run.get("schema_version") == EXACT_EDGE_RUN_REPORT_SCHEMA_V1
        and run.get("benchmark_lane") == "exact-reduction-edge"
        and run.get("run_valid") is True
        and run.get("formal_model_configuration") is True
        and run.get("model") == FORMAL_MODEL
        and run_ids == expected_ids
        and len(run_cases) == 6,
        "h_i_exact_edge_run_invalid",
        "exact-edge development run is invalid or incomplete",
    )
    _expect(
        run.get("content_sha256") == _canonical_content_hash(run, field="content_sha256"),
        "h_i_hash_binding_mismatch",
        "exact-edge run content hash is invalid",
    )
    _expect(
        run.get("manifest_sha256") == manifest.sha256
        and run.get("expected_oracle_sha256") == manifest.oracle_sha256
        and isinstance(run.get("suite"), Mapping)
        and run["suite"].get("split") == "dev"
        and run["suite"].get("sha256") == dev_suite.sha256
        and run["suite"].get("case_count") == 6
        and run["suite"].get("answer_free") is True,
        "h_i_hash_binding_mismatch",
        "exact-edge run manifest/suite/oracle binding drifted",
    )
    parallel = run.get("parallel_execution")
    isolation = run.get("isolation")
    metrics = run.get("metrics")
    _expect(
        isinstance(parallel, Mapping)
        and parallel.get("configured_jobs") == 4
        and parallel.get("submitted_case_tasks") == 6
        and parallel.get("final_active_case_tasks") == 0
        and parallel.get("observed_parallelism") is True,
        "h_i_concurrency_not_drained",
        "exact-edge development concurrency did not drain",
    )
    _expect(
        isinstance(isolation, Mapping)
        and isolation.get("enabled") is True
        and isolation.get("valid") is True
        and isolation.get("physical_copy") is True
        and isolation.get("lean_root_symlink") is False
        and isolation.get("archive_present") is False
        and isolation.get("plan_present") is False
        and isolation.get("oracle_present") is False,
        "h_i_exact_edge_isolation_invalid",
        "exact-edge isolated workspace is invalid",
    )
    _expect(
        isinstance(metrics, Mapping)
        and metrics.get("case_count") == 6
        and metrics.get("unique_directions") == 6,
        "h_i_exact_edge_run_invalid",
        "exact-edge development metrics drifted",
    )
    _expect(
        all(
            isinstance(row, Mapping)
            and isinstance(row.get("security"), Mapping)
            and row["security"].get("secret_detected") is False
            and row.get("protocol_valid") is True
            for row in run_cases
        ),
        "h_i_secret_leak",
        "exact-edge development case security/protocol evidence failed",
    )
    calls = _model_calls(run)
    if calls:
        _validate_http_calls(calls, expected_count=len(calls), label="exact-edge dev")
        _expect(
            metrics.get("model_calls") == len(calls)
            and metrics.get("http_ok_model_calls") == len(calls),
            "h_i_deepseek_http_evidence_invalid",
            "exact-edge model-call metrics differ from their ledgers",
        )

    _expect(
        score.get("schema_version") == EXACT_EDGE_SCORE_REPORT_SCHEMA_V1
        and score.get("run_valid") is True
        and score.get("run_id") == run.get("run_id")
        and score.get("manifest_sha256") == manifest.sha256
        and score.get("suite_sha256") == dev_suite.sha256
        and score.get("oracle_sha256") == manifest.oracle_sha256
        and score_ids == expected_ids
        and len(score_cases) == 6,
        "h_i_exact_edge_score_invalid",
        "exact-edge development score is invalid or incomplete",
    )
    scorecard = score.get("scorecard")
    _expect(
        isinstance(scorecard, Mapping)
        and scorecard.get("unique_directions") == 6
        and scorecard.get("endpoint_ready") == 6
        and scorecard.get("mutation_rejection_counts") == {}
        and all(
            isinstance(row, Mapping) and row.get("mutation_rejections") == []
            for row in score_cases
        ),
        "h_i_exact_edge_score_invalid",
        "exact-edge scorer integrity/mutation checks failed",
    )
    return {
        "run": {
            "file": str(run_file),
            "sha256": _sha256(run_file, tagged=True),
            "run_id": run.get("run_id"),
            "run_valid": True,
            "metrics": metrics,
            "parallel_execution": parallel,
        },
        "score": {
            "file": str(score_file),
            "sha256": _sha256(score_file, tagged=True),
            "run_valid": True,
            "scorecard": scorecard,
        },
        "unique_directions": 6,
        "endpoint_ready": 6,
        "model_calls": len(calls),
        "http_200_model_calls": len(calls),
        "all_concurrency_drained": True,
        "secret_absent": True,
    }


def _source_control(files: Iterable[Path]) -> dict[str, Any]:
    unique = sorted({path.resolve() for path in files}, key=str)
    hashes = {
        str(path.relative_to(ROOT)): _sha256(path)
        for path in unique
    }
    return {
        "files": hashes,
        "combined_sha256": hashlib.sha256(
            canonical_json(hashes).encode("utf-8")
        ).hexdigest(),
        "lean_toolchain": (ROOT / "Lean/lean-toolchain").read_text(encoding="utf-8").strip(),
        "lean_toolchain_sha256": _sha256(ROOT / "Lean/lean-toolchain"),
        "lake_manifest_sha256": _sha256(ROOT / "Lean/lake-manifest.json"),
    }


def build_full_report(
    *,
    static_paths: StaticEvidencePaths,
    stage_benchmark_paths: Mapping[str, Path],
    capability_run_paths: Mapping[str, Path],
    capability_score_paths: Mapping[str, Path],
    exact_edge_dev_run: Path,
    exact_edge_dev_score: Path,
) -> dict[str, Any]:
    static = validate_static_assets(static_paths)
    stages = validate_stage_benchmarks(
        stage_benchmark_paths,
        registry_path=static["source_files"]["registry"],
        taxonomy_path=static["source_files"]["taxonomy"],
    )
    capability = validate_capability_reports(
        capability_run_paths, capability_score_paths, static=static
    )
    exact = validate_exact_edge_dev_reports(
        exact_edge_dev_run, exact_edge_dev_score, static=static
    )
    gates = {
        "active_h_i_plan_bound": True,
        "taxonomy_covers_all_suites_and_cases": True,
        "legacy_and_r1_capability_weight_zero": True,
        "target_identity_partition_32_c0_2_f0_10_r1": True,
        "target_identity_partition_disjoint_and_exhaustive_44": True,
        "capability_manifest_oracle_hashes_valid": True,
        "capability_all_four_splits_run_valid": capability["run_valid"],
        "capability_all_four_scores_valid": capability["score_valid"],
        "capability_r0_mutations_fail_closed": capability["all_r0_mutations_passed"],
        "capability_security_guardrails_clean": all(
            value == 0 for value in capability["security_guardrails"].values()
        ),
        "archive_63_problems_60_unique_directions": True,
        "archive_24_exact_edges_status_bound": True,
        "archive_three_duplicate_variants_zero_weight": True,
        "pdf_only_capability_weight_zero": True,
        "exact_edge_six_dev_run_valid": exact["run"]["run_valid"],
        "exact_edge_six_dev_score_valid": exact["score"]["run_valid"],
        "five_stage_full_benchmarks_distinct": stages["stage_count"] == 5,
        "five_stage_deepseek_http_200_evidence": (
            stages["real_deepseek_http_calls"]
            == stages["http_200_count"]
            == stages["http_evidence_record_count"]
            == 60
        ),
        "all_concurrency_counters_returned_to_zero": (
            stages["all_concurrency_drained"]
            and capability["all_concurrency_drained"]
            and exact["all_concurrency_drained"]
        ),
        "no_api_key_authorization_or_secret_in_evidence": exact["secret_absent"],
        "regression_not_used_as_capability_score": (
            stages["capability_weight"] == 0
            and capability["regression_scores_used"] is False
        ),
    }
    _expect(
        all(value is True for value in gates.values()),
        "h_i_final_gate_failed",
        "one or more H-I final report gates did not pass",
    )
    static_source_files = list(static["source_files"].values())
    runtime_files = [
        *(_repo_file(path, label=f"stage {label}") for label, path in stage_benchmark_paths.items()),
        *(_repo_file(path, label=f"capability run {split}") for split, path in capability_run_paths.items()),
        *(_repo_file(path, label=f"capability score {split}") for split, path in capability_score_paths.items()),
        _repo_file(exact_edge_dev_run, label="exact-edge dev run"),
        _repo_file(exact_edge_dev_score, label="exact-edge dev score"),
        Path(__file__).resolve(),
        ROOT / "tests/test_hardness_np_hard_h_i_full_report.py",
    ]
    _expect(
        all(path.is_file() for path in runtime_files),
        "h_i_evidence_missing",
        "report builder or its static test is missing",
    )
    report: dict[str, Any] = {
        "schema_version": REPORT_SCHEMA,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "stage": "H-I-benchmark-capability-boundary-and-regression-downgrade",
        "passed": True,
        "active_plan": static["active_plan"],
        "registry_taxonomy": static["registry_taxonomy"],
        "identity_partition": static["identity_partition"],
        "capability_contract": static["capability_contract"],
        "capability_baseline": capability,
        "exact_edge_archive": static["exact_edge_archive"],
        "exact_edge_dev_baseline": exact,
        "stage_benchmarks": stages,
        "gates": gates,
        "source_control": _source_control([*static_source_files, *runtime_files]),
    }
    _assert_no_secret(report, label="final H-I report")
    report["report_id"] = sha256_id(report)
    return report


def _write_json(path: Path, value: Mapping[str, Any]) -> None:
    resolved = path.resolve()
    _expect(
        resolved == REPORT_PATH.resolve(),
        "h_i_output_path_invalid",
        f"H-I report must be written to {REPORT_PATH}",
    )
    temporary = resolved.with_suffix(resolved.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(resolved)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Build MAIN_H_I_FULL_REPORT.json from explicit frozen evidence"
    )
    parser.add_argument("--plan", type=Path, required=True)
    parser.add_argument("--registry", type=Path, required=True)
    parser.add_argument("--taxonomy", type=Path, required=True)
    parser.add_argument("--capability-manifest", type=Path, required=True)
    parser.add_argument("--capability-oracle", type=Path, required=True)
    parser.add_argument("--target-matrix", type=Path, required=True)
    parser.add_argument("--public-r1-suite", type=Path, required=True)
    parser.add_argument("--exact-edge-manifest", type=Path, required=True)
    parser.add_argument("--exact-edge-oracle", type=Path, required=True)
    parser.add_argument("--problem-archive", type=Path, required=True)
    parser.add_argument("--archive-selection", type=Path, required=True)
    parser.add_argument("--archive-audit", type=Path, required=True)
    parser.add_argument(
        "--stage-benchmark",
        action="append",
        required=True,
        metavar="STAGE=PATH",
        help="repeat for all five frozen H-I stage labels",
    )
    parser.add_argument(
        "--capability-run",
        action="append",
        required=True,
        metavar="SPLIT=PATH",
        help="repeat for dev/validation/heldout/frontier raw reports",
    )
    parser.add_argument(
        "--capability-score",
        action="append",
        required=True,
        metavar="SPLIT=PATH",
        help="repeat for dev/validation/heldout/frontier scorer reports",
    )
    parser.add_argument("--exact-edge-dev-run", type=Path, required=True)
    parser.add_argument("--exact-edge-dev-score", type=Path, required=True)
    parser.add_argument("--output", type=Path, default=REPORT_PATH)
    return parser


def main() -> int:
    arguments = build_parser().parse_args()
    try:
        stage_paths = _parse_labeled_paths(
            arguments.stage_benchmark,
            expected=STAGE_LABELS,
            option="--stage-benchmark",
        )
        capability_runs = _parse_labeled_paths(
            arguments.capability_run,
            expected=CAPABILITY_SPLITS,
            option="--capability-run",
        )
        capability_scores = _parse_labeled_paths(
            arguments.capability_score,
            expected=CAPABILITY_SPLITS,
            option="--capability-score",
        )
        report = build_full_report(
            static_paths=StaticEvidencePaths(
                plan=arguments.plan,
                registry=arguments.registry,
                taxonomy=arguments.taxonomy,
                capability_manifest=arguments.capability_manifest,
                capability_oracle=arguments.capability_oracle,
                target_matrix=arguments.target_matrix,
                public_r1_suite=arguments.public_r1_suite,
                exact_edge_manifest=arguments.exact_edge_manifest,
                exact_edge_oracle=arguments.exact_edge_oracle,
                problem_archive=arguments.problem_archive,
                archive_selection=arguments.archive_selection,
                archive_audit=arguments.archive_audit,
            ),
            stage_benchmark_paths=stage_paths,
            capability_run_paths=capability_runs,
            capability_score_paths=capability_scores,
            exact_edge_dev_run=arguments.exact_edge_dev_run,
            exact_edge_dev_score=arguments.exact_edge_dev_score,
        )
        _write_json(arguments.output, report)
    except (HIReportError, OSError, UnicodeError, ValueError) as error:
        print(
            json.dumps(
                {
                    "passed": False,
                    "output_written": False,
                    "failure_code": getattr(error, "code", "h_i_report_build_failed"),
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
                "deepseek_http_calls": report["stage_benchmarks"][
                    "real_deepseek_http_calls"
                ],
            },
            ensure_ascii=False,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
