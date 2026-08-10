"""H-K.3 full capability benchmark with publication-catalog reuse.

The V3 runner delegates the same 34 answer-free jobs to the production V2
entrypoint after publication activation.  Its extra contract is intentionally
small: every job identity binds the exact publication catalog ID, direct and
transitive reuse cases must be solved by the registered typed route with zero
model calls, and the remaining cases retain the V2 authoring/safety/frontier
semantics.  This preserves the historical V1/V2 formats unchanged.
"""

from __future__ import annotations

import hashlib
import json
from copy import deepcopy
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping, Sequence

from .connection_catalog import load_connection_catalog_snapshot
from .model_client import DeepSeekConfig
from .models import sha256_id
from .np_hard_capability import (
    CAPABILITY_RUN_SCHEMA_V2,
    CAPABILITY_SPLITS,
    CapabilityBundle,
    NPHardCapabilityError,
    _required_verified_authoring_motif,
    _strict_case_success,
    _validate_run_case,
    load_capability_bundle,
    load_capability_oracle,
    run_np_hard_capability_benchmark,
)
from .np_hard_publication_activation import (
    ACTIVE_STATE,
    NPHardPublicationActivationError,
    PublicationCatalogSnapshot,
    load_publication_catalog,
    resolve_active_publication,
)


PUBLICATION_REUSE_MANIFEST_SCHEMA = (
    "hardness_np_hard_publication_reuse_manifest_v3"
)
PUBLICATION_REUSE_RUN_SCHEMA = "hardness_np_hard_publication_reuse_run_v3"
PUBLICATION_REUSE_SCORE_SCHEMA = "hardness_np_hard_publication_reuse_score_v3"
PUBLICATION_REUSE_REQUEST_SCHEMA = (
    "hardness_np_hard_publication_reuse_request_v3"
)
PUBLICATION_REUSE_BENCHMARK_ID = "np-hard-publication-reuse-v3"
DIRECT_REUSE = "direct_publication_reuse"
TRANSITIVE_REUSE = "transitive_publication_reuse"
FIRST_AUTHORING = "first_authoring"
EXISTING_ROUTE = "existing_route"
SAFETY = "safety"
FRONTIER = "frontier"
FULL_CASE_COUNT = 34
TRANSITIVE_HITTING_SET_CASE = "chld-au-06-hitting-set"
TRANSITIVE_PUBLISHER_CASE = "chld-au-07-set-covering"
TRANSITIVE_CONSUMER_DECLARATION = (
    "ComplexityReduction.Routes.SetCoveringToHittingSet.certifiedReduction"
)


class NPHardPublicationReuseError(ValueError):
    """Stable fail-closed publication-reuse benchmark error."""

    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


def _fail(code: str, message: str) -> None:
    raise NPHardPublicationReuseError(code, message)


def _expect(condition: bool, code: str, message: str) -> None:
    if not condition:
        _fail(code, message)


def _read_json(path: Path, *, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        _fail("publication_reuse_file_missing", f"{label} is missing: {path}")
    except json.JSONDecodeError as error:
        _fail(
            "publication_reuse_json_invalid",
            f"{label} is invalid JSON at {error.lineno}:{error.colno}",
        )
    if not isinstance(value, dict):
        _fail("publication_reuse_schema_invalid", f"{label} must be an object")
    return value


def _write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def _file_sha256(path: Path) -> str:
    return f"sha256:{hashlib.sha256(path.read_bytes()).hexdigest()}"


def _content_id(value: Mapping[str, Any], *, field: str) -> str:
    payload = deepcopy(dict(value))
    payload.pop(field, None)
    return sha256_id(payload)


def _relative(path: Path, *, root: Path, label: str) -> str:
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except (OSError, ValueError):
        _fail("publication_reuse_path_escape", f"{label} escaped the repository")


def _resolve(root: Path, value: Any, *, label: str) -> Path:
    _expect(
        isinstance(value, str) and value and not Path(value).is_absolute(),
        "publication_reuse_schema_invalid",
        f"{label} must be repository-relative",
    )
    path = (root / value).resolve()
    try:
        path.relative_to(root.resolve())
    except ValueError:
        _fail("publication_reuse_path_escape", f"{label} escaped the repository")
    return path


def _route_atoms(row: Mapping[str, Any]) -> tuple[str, ...]:
    raw = row.get("raw_result")
    deterministic = raw.get("deterministic_result") if isinstance(raw, Mapping) else None
    route = deterministic.get("route") if isinstance(deterministic, Mapping) else None
    atoms = route.get("atoms") if isinstance(route, Mapping) else None
    if not isinstance(atoms, list) or not all(isinstance(atom, str) for atom in atoms):
        return ()
    return tuple(atoms)


def _case_by_id(bundle: CapabilityBundle) -> dict[str, Any]:
    return {case.case_id: case for case in bundle.cases}


def _validate_production_catalog_binding(
    *, catalog: PublicationCatalogSnapshot, root: Path
) -> Mapping[str, Any]:
    aggregate = catalog.value.get("aggregate")
    _expect(
        isinstance(aggregate, Mapping),
        "publication_catalog_stale",
        "publication catalog lacks its generated aggregate binding",
    )
    aggregate_path = _resolve(
        root, aggregate.get("file"), label="generated hardness aggregate"
    )
    _expect(
        aggregate_path.is_file()
        and _file_sha256(aggregate_path) == aggregate.get("sha256"),
        "publication_catalog_stale",
        "generated hardness aggregate file/hash drifted",
    )
    production = catalog.value.get("production_registry")
    _expect(
        isinstance(production, Mapping),
        "publication_catalog_not_activated",
        "publication catalog lacks a production registry rebuild",
    )
    connection_path = _resolve(
        root, production.get("connection_catalog_file"), label="connection catalog"
    )
    _expect(
        connection_path.is_file()
        and _file_sha256(connection_path)
        == production.get("connection_catalog_sha256"),
        "publication_catalog_stale",
        "production connection catalog file/hash drifted",
    )
    connection = load_connection_catalog_snapshot(connection_path)
    _expect(
        connection.catalog_id == production.get("connection_catalog_id")
        and connection.registry_fingerprint == production.get("registry_fingerprint"),
        "publication_catalog_stale",
        "production connection catalog identity drifted",
    )
    active_declarations = {
        str(entry["asset_declaration"])
        for entry in catalog.entries
        if entry.get("status") == ACTIVE_STATE
    }
    discovered = {entry.certificate_declaration for entry in connection.entries}
    _expect(
        active_declarations.issubset(discovered),
        "publication_catalog_stale",
        "production resolver no longer discovers every active publication",
    )
    return production


def build_publication_reuse_manifest(
    *,
    root: Path,
    base_manifest_path: Path,
    publication_catalog_path: Path,
    output_path: Path,
) -> dict[str, Any]:
    """Freeze the 34-case V3 denominator against one active catalog ID."""

    root = root.resolve()
    bundle = load_capability_bundle(
        base_manifest_path.resolve(), root=root, verify_oracle=False
    )
    _expect(
        len(bundle.cases) == FULL_CASE_COUNT,
        "publication_reuse_denominator_invalid",
        "base capability manifest is not the full 34-case denominator",
    )
    catalog = load_publication_catalog(publication_catalog_path.resolve())
    _validate_production_catalog_binding(catalog=catalog, root=root)
    cases = _case_by_id(bundle)
    direct: list[dict[str, Any]] = []
    for entry in catalog.entries:
        if entry.get("status") != ACTIVE_STATE:
            continue
        case_id = str(entry["case_id"])
        _expect(
            case_id in cases
            and bundle.case_identity[case_id].get("identity_id")
            == entry.get("canonical_identity_id"),
            "publication_reuse_identity_mismatch",
            f"active publication {case_id} differs from the 34-case denominator",
        )
        resolve_active_publication(
            catalog=catalog,
            canonical_identity_id=str(entry["canonical_identity_id"]),
            repo_root=root,
        )
        direct.append(
            {
                "case_id": case_id,
                "publication_id": entry["publication_id"],
                "candidate_id": entry["candidate_id"],
                "canonical_identity_id": entry["canonical_identity_id"],
                "canonical_endpoint": entry["canonical_endpoint"],
                "asset_module": entry["asset_module"],
                "asset_declaration": entry["asset_declaration"],
            }
        )
    _expect(
        len(direct) >= 4
        and TRANSITIVE_PUBLISHER_CASE in {row["case_id"] for row in direct},
        "publication_reuse_denominator_invalid",
        "V3 requires four direct assets including SetCovering",
    )
    publisher = next(
        row for row in direct if row["case_id"] == TRANSITIVE_PUBLISHER_CASE
    )
    _expect(
        TRANSITIVE_HITTING_SET_CASE in cases,
        "publication_reuse_denominator_invalid",
        "HittingSet transitive consumer is absent",
    )
    manifest: dict[str, Any] = {
        "schema_version": PUBLICATION_REUSE_MANIFEST_SCHEMA,
        "benchmark_id": PUBLICATION_REUSE_BENCHMARK_ID,
        "objective": "target-hardness-publication-reuse",
        "case_count": FULL_CASE_COUNT,
        "selected_splits": list(CAPABILITY_SPLITS),
        "base_capability_manifest": {
            "file": _relative(base_manifest_path, root=root, label="base manifest"),
            "sha256": _file_sha256(base_manifest_path.resolve()),
            "schema_version": bundle.manifest.schema_version,
            "benchmark_id": bundle.manifest.benchmark_id,
        },
        "publication_catalog": {
            "file": _relative(
                publication_catalog_path, root=root, label="publication catalog"
            ),
            "sha256": _file_sha256(publication_catalog_path.resolve()),
            "catalog_id": catalog.catalog_id,
            "active_publication_count": catalog.value["active_publication_count"],
        },
        "reuse_policy": {
            "direct": sorted(direct, key=lambda row: row["case_id"]),
            "transitive": [
                {
                    "case_id": TRANSITIVE_HITTING_SET_CASE,
                    "canonical_identity_id": bundle.case_identity[
                        TRANSITIVE_HITTING_SET_CASE
                    ]["identity_id"],
                    "canonical_endpoint": bundle.case_identity[
                        TRANSITIVE_HITTING_SET_CASE
                    ]["canonical_declaration"],
                    "publisher_case_id": TRANSITIVE_PUBLISHER_CASE,
                    "publisher_publication_id": publisher["publication_id"],
                    "publisher_declaration": publisher["asset_declaration"],
                    "consumer_declaration": TRANSITIVE_CONSUMER_DECLARATION,
                }
            ],
            "reuse_requires_zero_model_calls": True,
            "remaining_cases_use_base_v2_production": True,
        },
        "required_model_profile": deepcopy(
            bundle.manifest.required_model_profile
        ),
    }
    manifest["manifest_id"] = _content_id(manifest, field="manifest_id")
    _write_json(output_path.resolve(), manifest)
    return manifest


def load_publication_reuse_manifest(
    path: Path, *, root: Path
) -> tuple[dict[str, Any], CapabilityBundle, PublicationCatalogSnapshot]:
    root = root.resolve()
    value = _read_json(path.resolve(), label="publication reuse manifest")
    _expect(
        value.get("schema_version") == PUBLICATION_REUSE_MANIFEST_SCHEMA
        and value.get("benchmark_id") == PUBLICATION_REUSE_BENCHMARK_ID
        and value.get("objective") == "target-hardness-publication-reuse"
        and value.get("case_count") == FULL_CASE_COUNT
        and value.get("selected_splits") == list(CAPABILITY_SPLITS)
        and value.get("manifest_id") == _content_id(value, field="manifest_id"),
        "publication_reuse_manifest_invalid",
        "V3 publication reuse manifest contract drifted",
    )
    base = value.get("base_capability_manifest")
    publication = value.get("publication_catalog")
    policy = value.get("reuse_policy")
    _expect(
        isinstance(base, Mapping)
        and isinstance(publication, Mapping)
        and isinstance(policy, Mapping),
        "publication_reuse_manifest_invalid",
        "V3 manifest provenance/policy is absent",
    )
    base_path = _resolve(root, base.get("file"), label="base manifest")
    catalog_path = _resolve(
        root, publication.get("file"), label="publication catalog"
    )
    _expect(
        base_path.is_file()
        and _file_sha256(base_path) == base.get("sha256")
        and catalog_path.is_file()
        and _file_sha256(catalog_path) == publication.get("sha256"),
        "publication_reuse_manifest_stale",
        "base manifest or publication catalog hash drifted",
    )
    bundle = load_capability_bundle(base_path, root=root, verify_oracle=False)
    catalog = load_publication_catalog(catalog_path)
    _expect(
        catalog.catalog_id == publication.get("catalog_id")
        and len(bundle.cases) == FULL_CASE_COUNT,
        "publication_reuse_manifest_stale",
        "base denominator or publication catalog identity drifted",
    )
    _validate_production_catalog_binding(catalog=catalog, root=root)
    direct = policy.get("direct")
    transitive = policy.get("transitive")
    _expect(
        isinstance(direct, list)
        and len(direct) >= 4
        and isinstance(transitive, list)
        and len(transitive) == 1
        and policy.get("reuse_requires_zero_model_calls") is True
        and policy.get("remaining_cases_use_base_v2_production") is True,
        "publication_reuse_manifest_invalid",
        "V3 reuse policy is incomplete",
    )
    direct_ids: set[str] = set()
    for row in direct:
        _expect(
            isinstance(row, Mapping)
            and isinstance(row.get("case_id"), str)
            and row["case_id"] not in direct_ids,
            "publication_reuse_manifest_invalid",
            "direct reuse rows are malformed or duplicated",
        )
        direct_ids.add(str(row["case_id"]))
        active = resolve_active_publication(
            catalog=catalog,
            canonical_identity_id=str(row.get("canonical_identity_id")),
            repo_root=root,
        )
        _expect(
            active is not None
            and active.get("publication_id") == row.get("publication_id")
            and active.get("asset_declaration") == row.get("asset_declaration"),
            "publication_reuse_manifest_stale",
            "direct reuse row no longer selects the active publication",
        )
    transitive_row = transitive[0]
    _expect(
        isinstance(transitive_row, Mapping)
        and transitive_row.get("case_id") == TRANSITIVE_HITTING_SET_CASE
        and transitive_row.get("publisher_case_id") == TRANSITIVE_PUBLISHER_CASE
        and TRANSITIVE_HITTING_SET_CASE not in direct_ids,
        "publication_reuse_manifest_invalid",
        "transitive HittingSet policy drifted",
    )
    return value, bundle, catalog


def _request(
    *,
    case_id: str,
    canonical_identity_id: str,
    catalog_id: str,
    base_manifest_sha256: str,
    execution_class: str,
) -> dict[str, Any]:
    value: dict[str, Any] = {
        "schema_version": PUBLICATION_REUSE_REQUEST_SCHEMA,
        "case_id": case_id,
        "canonical_identity_id": canonical_identity_id,
        "publication_catalog_id": catalog_id,
        "base_capability_manifest_sha256": base_manifest_sha256,
        "execution_class": execution_class,
    }
    value["request_id"] = sha256_id(value)
    return value


def _execution_maps(manifest: Mapping[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    policy = manifest["reuse_policy"]
    direct = {str(row["case_id"]): row for row in policy["direct"]}
    transitive = {str(row["case_id"]): row for row in policy["transitive"]}
    return direct, transitive


def run_publication_reuse_benchmark(
    *,
    root: Path,
    manifest_path: Path,
    output_root: Path,
    report_path: Path,
    deepseek: DeepSeekConfig,
    jobs: int = 4,
) -> dict[str, Any]:
    """Run the full 34-case production benchmark against one catalog ID."""

    root = root.resolve()
    manifest, bundle, catalog = load_publication_reuse_manifest(
        manifest_path.resolve(), root=root
    )
    base_report_path = output_root.resolve() / "base-v2-report.json"
    base_report = run_np_hard_capability_benchmark(
        root=root,
        manifest_path=bundle.manifest.path,
        output_root=output_root.resolve(),
        report_path=base_report_path,
        deepseek=deepseek,
        selected_splits=CAPABILITY_SPLITS,
        jobs=jobs,
    )
    direct, transitive = _execution_maps(manifest)
    wrapped_cases: list[dict[str, Any]] = []
    for row in base_report["cases"]:
        case_id = str(row["case_id"])
        if case_id in direct:
            execution_class = DIRECT_REUSE
            reuse = direct[case_id]
        elif case_id in transitive:
            execution_class = TRANSITIVE_REUSE
            reuse = transitive[case_id]
        else:
            execution_class = "base_v2"
            reuse = None
        request = _request(
            case_id=case_id,
            canonical_identity_id=str(row["canonical_identity_id"]),
            catalog_id=catalog.catalog_id,
            base_manifest_sha256=str(manifest["base_capability_manifest"]["sha256"]),
            execution_class=execution_class,
        )
        wrapped_cases.append(
            {
                "case_id": case_id,
                "split": row["split"],
                "family": row["family"],
                "canonical_identity_id": row["canonical_identity_id"],
                "canonical_problem": row["canonical_problem"],
                "execution_class": execution_class,
                "publication_request": request,
                "reuse_evidence": deepcopy(reuse),
                "public_status": row["public_status"],
                "failure_code": row["failure_code"],
                "model_calls": row["model_calls"],
                "token_usage": deepcopy(row["token_usage"]),
                "base_case_evidence_sha256": row["evidence_sha256"],
            }
        )
    reuse_rows = [
        row
        for row in wrapped_cases
        if row["execution_class"] in {DIRECT_REUSE, TRANSITIVE_REUSE}
    ]
    reuse_zero = all(row["model_calls"] == 0 for row in reuse_rows)
    payload: dict[str, Any] = {
        "schema_version": PUBLICATION_REUSE_RUN_SCHEMA,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "benchmark_id": PUBLICATION_REUSE_BENCHMARK_ID,
        "run_valid": bool(
            base_report.get("run_valid") is True
            and len(wrapped_cases) == FULL_CASE_COUNT
            and reuse_zero
        ),
        "output_root": str(output_root.resolve()),
        "selected_splits": list(CAPABILITY_SPLITS),
        "manifest": {
            "file": str(manifest_path.resolve()),
            "sha256": _file_sha256(manifest_path.resolve()),
            "manifest_id": manifest["manifest_id"],
            "oracle_opened_by_runner": False,
        },
        "publication_catalog": {
            "file": str(catalog.path),
            "sha256": _file_sha256(catalog.path),
            "catalog_id": catalog.catalog_id,
        },
        "base_run": {
            "file": str(base_report_path),
            "sha256": _file_sha256(base_report_path),
            "run_id": base_report["run_id"],
            "schema_version": base_report["schema_version"],
        },
        "model": deepcopy(base_report["model"]),
        "preflight": deepcopy(base_report["preflight"]),
        "isolation": deepcopy(base_report["isolation"]),
        "parallel_execution": deepcopy(base_report["parallel_execution"]),
        "security": {
            **deepcopy(base_report["security"]),
            "publication_catalog_bound_to_every_job": True,
            "publication_catalog_id": catalog.catalog_id,
        },
        "reuse_execution": {
            "direct_count": len(direct),
            "transitive_count": len(transitive),
            "zero_model_call_count": sum(row["model_calls"] == 0 for row in reuse_rows),
            "zero_model_call_rate": (
                round(sum(row["model_calls"] == 0 for row in reuse_rows) / len(reuse_rows), 6)
                if reuse_rows
                else None
            ),
        },
        "metrics": {
            **deepcopy(base_report["metrics"]),
            "publication_reuse_case_count": len(reuse_rows),
            "publication_reuse_model_calls": sum(
                int(row["model_calls"]) for row in reuse_rows
            ),
        },
        "cases": wrapped_cases,
    }
    payload["run_id"] = sha256_id(payload)
    _write_json(report_path.resolve(), payload)
    canonical = output_root.resolve() / "report.json"
    if canonical != report_path.resolve():
        _write_json(canonical, payload)
    return payload


def _validate_wrapper_case(
    *,
    wrapper: Mapping[str, Any],
    base_row: Mapping[str, Any],
    expected_request: Mapping[str, Any],
    execution_class: str,
    expected_reuse_evidence: Mapping[str, Any] | None,
) -> None:
    _expect(
        wrapper.get("case_id") == base_row.get("case_id")
        and wrapper.get("split") == base_row.get("split")
        and wrapper.get("family") == base_row.get("family")
        and wrapper.get("canonical_identity_id")
        == base_row.get("canonical_identity_id")
        and wrapper.get("canonical_problem") == base_row.get("canonical_problem")
        and wrapper.get("execution_class") == execution_class
        and wrapper.get("publication_request") == expected_request
        and wrapper.get("reuse_evidence") == expected_reuse_evidence
        and wrapper.get("public_status") == base_row.get("public_status")
        and wrapper.get("failure_code") == base_row.get("failure_code")
        and wrapper.get("model_calls") == base_row.get("model_calls")
        and wrapper.get("token_usage") == base_row.get("token_usage")
        and wrapper.get("base_case_evidence_sha256")
        == base_row.get("evidence_sha256"),
        "publication_reuse_result_forgery",
        "V3 wrapper case differs from the bound V2 evidence",
    )


def score_publication_reuse_benchmark(
    *,
    root: Path,
    manifest_path: Path,
    run_report_path: Path,
    score_report_path: Path,
) -> dict[str, Any]:
    """Verify V2 evidence, then separately score reuse and first authoring."""

    root = root.resolve()
    manifest, bundle, catalog = load_publication_reuse_manifest(
        manifest_path.resolve(), root=root
    )
    report = _read_json(run_report_path.resolve(), label="publication reuse run")
    _expect(
        report.get("schema_version") == PUBLICATION_REUSE_RUN_SCHEMA
        and report.get("benchmark_id") == PUBLICATION_REUSE_BENCHMARK_ID
        and report.get("run_id") == _content_id(report, field="run_id"),
        "publication_reuse_result_forgery",
        "V3 run schema or content identity drifted",
    )
    manifest_record = report.get("manifest")
    catalog_record = report.get("publication_catalog")
    base_record = report.get("base_run")
    _expect(
        isinstance(manifest_record, Mapping)
        and manifest_record.get("sha256") == _file_sha256(manifest_path.resolve())
        and manifest_record.get("manifest_id") == manifest["manifest_id"]
        and manifest_record.get("oracle_opened_by_runner") is False
        and isinstance(catalog_record, Mapping)
        and catalog_record.get("sha256") == _file_sha256(catalog.path)
        and catalog_record.get("catalog_id") == catalog.catalog_id
        and isinstance(base_record, Mapping),
        "publication_reuse_result_forgery",
        "V3 manifest/catalog/base-run binding drifted",
    )
    base_path = Path(str(base_record.get("file"))).resolve()
    output_root = Path(str(report.get("output_root"))).resolve()
    _expect(
        base_path.is_file()
        and base_path.parent == output_root
        and _file_sha256(base_path) == base_record.get("sha256"),
        "publication_reuse_result_forgery",
        "base V2 run escaped or drifted from the V3 job",
    )
    base = _read_json(base_path, label="base V2 capability run")
    _expect(
        base.get("schema_version") == CAPABILITY_RUN_SCHEMA_V2
        and base.get("run_id") == base_record.get("run_id")
        and base.get("run_id") == sha256_id(
            {key: deepcopy(value) for key, value in base.items() if key != "run_id"}
        )
        and base.get("run_valid") is True
        and base.get("selected_splits") == list(CAPABILITY_SPLITS),
        "publication_reuse_result_forgery",
        "base V2 full run is invalid",
    )
    oracle = load_capability_oracle(bundle.manifest.oracle.path, bundle=bundle)
    cases = _case_by_id(bundle)
    base_rows = {
        str(row.get("case_id")): row
        for row in base.get("cases", [])
        if isinstance(row, Mapping)
    }
    wrappers = {
        str(row.get("case_id")): row
        for row in report.get("cases", [])
        if isinstance(row, Mapping)
    }
    _expect(
        len(base_rows) == len(wrappers) == FULL_CASE_COUNT
        and set(base_rows) == set(wrappers) == set(cases),
        "publication_reuse_result_forgery",
        "V3 run did not bind exactly the full 34-case denominator",
    )
    direct, transitive = _execution_maps(manifest)
    scored_rows: list[dict[str, Any]] = []
    for case_id, case in cases.items():
        row = base_rows[case_id]
        if case_id in direct:
            execution_class = DIRECT_REUSE
            reuse = direct[case_id]
        elif case_id in transitive:
            execution_class = TRANSITIVE_REUSE
            reuse = transitive[case_id]
        else:
            execution_class = "base_v2"
            reuse = None
        request = _request(
            case_id=case_id,
            canonical_identity_id=str(row["canonical_identity_id"]),
            catalog_id=catalog.catalog_id,
            base_manifest_sha256=str(manifest["base_capability_manifest"]["sha256"]),
            execution_class=execution_class,
        )
        _validate_wrapper_case(
            wrapper=wrappers[case_id],
            base_row=row,
            expected_request=request,
            execution_class=execution_class,
            expected_reuse_evidence=reuse,
        )
        oracle_case = oracle[case_id]
        motif = None
        if execution_class == "base_v2":
            motif = _required_verified_authoring_motif(
                oracle_schema_version=bundle.manifest.oracle_schema_version,
                oracle_case=oracle_case,
                raw_result=row.get("raw_result"),
            )
        try:
            _validate_run_case(
                row=row,
                case=case,
                identity=bundle.case_identity[case_id],
                output_root=output_root,
                strict_deletion_diagnostics=True,
                required_authoring_motif=motif,
            )
        except NPHardCapabilityError as error:
            _fail(error.code, error.message)
        atoms = _route_atoms(row)
        if execution_class == DIRECT_REUSE:
            capability_success = bool(
                row["public_status"] == "VERIFIED"
                and row["failure_code"] is None
                and row["model_calls"] == 0
                and reuse["asset_declaration"] in atoms
            )
            outcome_class = DIRECT_REUSE
        elif execution_class == TRANSITIVE_REUSE:
            capability_success = bool(
                row["public_status"] == "VERIFIED"
                and row["failure_code"] is None
                and row["model_calls"] == 0
                and reuse["publisher_declaration"] in atoms
                and reuse["consumer_declaration"] in atoms
                and len(atoms) >= 2
            )
            outcome_class = TRANSITIVE_REUSE
        else:
            capability_success, _ = _strict_case_success(row, oracle_case)
            outcome_class = oracle_case.outcome_class
        scored_rows.append(
            {
                "case_id": case_id,
                "split": case.split,
                "family": case.family,
                "tier": oracle_case.tier,
                "outcome_class": outcome_class,
                "scored": oracle_case.scored,
                "public_status": row["public_status"],
                "failure_code": row["failure_code"],
                "model_calls": row["model_calls"],
                "capability_success": capability_success,
                "publication_request_id": request["request_id"],
                "route_atoms": list(atoms),
            }
        )

    direct_rows = [row for row in scored_rows if row["outcome_class"] == DIRECT_REUSE]
    transitive_rows = [
        row for row in scored_rows if row["outcome_class"] == TRANSITIVE_REUSE
    ]
    reuse_rows = [*direct_rows, *transitive_rows]
    authoring_rows = [
        row for row in scored_rows if row["outcome_class"] == FIRST_AUTHORING
    ]
    safety_rows = [row for row in scored_rows if row["outcome_class"] == SAFETY]
    remaining_model_calls = sum(
        int(row["model_calls"])
        for row in scored_rows
        if row["outcome_class"] not in {DIRECT_REUSE, TRANSITIVE_REUSE}
    )
    reuse_success = sum(bool(row["capability_success"]) for row in reuse_rows)
    direct_success = sum(bool(row["capability_success"]) for row in direct_rows)
    transitive_success = sum(
        bool(row["capability_success"]) for row in transitive_rows
    )
    zero_calls = sum(row["model_calls"] == 0 for row in reuse_rows)
    security = report.get("security")
    integrity = {
        "run_id_valid": True,
        "manifest_hash_valid": True,
        "publication_catalog_hash_and_id_valid": True,
        "base_v2_evidence_valid": True,
        "publication_request_bound_to_every_job": True,
        "reuse_zero_model_calls": zero_calls == len(reuse_rows),
        "full_34_case_denominator": len(scored_rows) == FULL_CASE_COUNT,
        "formal_deepseek_profile": bool(
            isinstance(security, Mapping)
            and security.get("formal_model_profile_matched") is True
            and security.get("fixture_model_used") is False
            and security.get("cached_or_recorded_response_used") is False
        ),
        "real_api_used_outside_reuse": remaining_model_calls > 0,
    }
    score_valid = all(integrity.values())
    score: dict[str, Any] = {
        "schema_version": PUBLICATION_REUSE_SCORE_SCHEMA,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "benchmark_id": PUBLICATION_REUSE_BENCHMARK_ID,
        "run_id": report["run_id"],
        "run_valid": bool(report.get("run_valid")),
        "score_valid": score_valid,
        "integrity": integrity,
        "publication_catalog": {
            "file": str(catalog.path),
            "sha256": _file_sha256(catalog.path),
            "catalog_id": catalog.catalog_id,
        },
        "metrics": {
            "case_count": len(scored_rows),
            "direct_publication_reuse_count": len(direct_rows),
            "transitive_publication_reuse_count": len(transitive_rows),
            "publication_reuse_success_count": reuse_success,
            "publication_reuse_zero_model_call_count": zero_calls,
            "publication_reuse_zero_model_call_rate": (
                round(zero_calls / len(reuse_rows), 6) if reuse_rows else None
            ),
            "remaining_first_authoring_count": len(authoring_rows),
            "remaining_first_authoring_verified_count": sum(
                bool(row["capability_success"]) for row in authoring_rows
            ),
            "safety_correct_count": sum(
                bool(row["capability_success"]) for row in safety_rows
            ),
            "remaining_model_calls": remaining_model_calls,
        },
        "reuse_scorecard": {
            "direct": {
                "count": len(direct_rows),
                "correct": direct_success,
                "zero_model_calls": sum(row["model_calls"] == 0 for row in direct_rows),
            },
            "transitive": {
                "count": len(transitive_rows),
                "correct": transitive_success,
                "zero_model_calls": sum(
                    row["model_calls"] == 0 for row in transitive_rows
                ),
            },
            "combined": {
                "count": len(reuse_rows),
                "correct": reuse_success,
                "zero_model_calls": zero_calls,
            },
        },
        "first_authoring_scorecard": {
            "count": len(authoring_rows),
            "verified": sum(bool(row["capability_success"]) for row in authoring_rows),
            "model_calls": sum(int(row["model_calls"]) for row in authoring_rows),
        },
        "cases": scored_rows,
        "provenance": {
            "manifest": {
                "file": str(manifest_path.resolve()),
                "sha256": _file_sha256(manifest_path.resolve()),
            },
            "run_report": {
                "file": str(run_report_path.resolve()),
                "sha256": _file_sha256(run_report_path.resolve()),
            },
            "base_oracle": {
                "file": str(bundle.manifest.oracle.path),
                "sha256": bundle.manifest.oracle.sha256,
                "opened_by": "independent V3 scorer only",
            },
        },
    }
    score["score_id"] = sha256_id(score)
    _write_json(score_report_path.resolve(), score)
    return score


__all__ = [
    "DIRECT_REUSE",
    "NPHardPublicationReuseError",
    "PUBLICATION_REUSE_BENCHMARK_ID",
    "PUBLICATION_REUSE_MANIFEST_SCHEMA",
    "PUBLICATION_REUSE_REQUEST_SCHEMA",
    "PUBLICATION_REUSE_RUN_SCHEMA",
    "PUBLICATION_REUSE_SCORE_SCHEMA",
    "TRANSITIVE_REUSE",
    "build_publication_reuse_manifest",
    "load_publication_reuse_manifest",
    "run_publication_reuse_benchmark",
    "score_publication_reuse_benchmark",
]
