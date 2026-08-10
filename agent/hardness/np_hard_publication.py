"""Fail-closed H-K shadow publication for model-authored NP-hard reductions.

This module deliberately stops before public registry activation.  It consumes
the final H-J evidence (or an explicitly labelled temporary run/score probe),
extracts only the authored reduction, and rebuilds that candidate in a clean
shadow Lean workspace.  The resulting manifest is portable: it contains
content hashes and repository-relative dependency names, never paths into the
authoring job or the shadow workspace.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import textwrap
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

from .models import canonical_json, sha256_id
from .np_hard_authoring import (
    NPHardAuthoringContractError,
    NPHardAuthoringTaskV2,
)


PUBLICATION_CANDIDATE_MANIFEST_SCHEMA = (
    "hardness_np_hard_publication_candidate_manifest_v1"
)
PUBLICATION_REVIEW_REPORT_SCHEMA = "hardness_np_hard_publication_review_v1"
H_J_FULL_REPORT_SCHEMA = "hardness_main_h_j_full_report_v2"
H_J_FINAL_STAGE = "h-j.5-gadget"
CAPABILITY_RUN_SCHEMA = "hardness_np_hard_capability_run_v2"
CAPABILITY_SCORE_SCHEMA = "hardness_np_hard_capability_score_v2"
PUBLICATION_STATE = "shadow_review_only"
TYPED_EDGE_ATTRIBUTE = "complexity_reduction_ir_typed_edge"
FINAL_COMPOSITION_ATTRIBUTE = (
    "complexity_reduction_ir_component_final_composition"
)
ANNOTATIONS_MODULE = "ComplexityReduction.Annotations.Attributes"
CERTIFIED_REDUCTION_MODULE = "ComplexityReduction.Certificate.Reduction"
AXIOM_GATE_MODULE = "ComplexityReduction.AxiomGate"
PUBLICATION_SUPPORT_IMPORTS = (
    CERTIFIED_REDUCTION_MODULE,
    ANNOTATIONS_MODULE,
    AXIOM_GATE_MODULE,
)

SUPPORTED_PUBLICATION_CASES: Mapping[str, Mapping[str, str]] = {
    "cdev-au-01-tagged-three-sat-adapter": {
        "label": "Tagged3SAT",
        "target": (
            "ComplexityReduction.Routes.ThreeSATToClique.IngressAdapters."
            "taggedThreeSATProblem"
        ),
    },
    "chld-au-07-set-covering": {
        "label": "SetCovering",
        "target": (
            "ComplexityReduction.Presentation.SetSystem."
            "setCoveringStructuredProblem"
        ),
    },
    "chld-au-09-feedback-arc-set": {
        "label": "FeedbackArcSet",
        "target": (
            "ComplexityReduction.Presentation.FeedbackArcSet.structuredProblem"
        ),
    },
    "chld-au-10-three-dimensional-matching": {
        "label": "ThreeDimensionalMatching",
        "target": (
            "ComplexityReduction.Presentation.ThreeDimensionalMatching."
            "structuredProblem"
        ),
    },
}

TAGGED_SHA256_RE = re.compile(r"sha256:[0-9a-f]{64}\Z")
IMPORT_RE = re.compile(
    r"(?m)^\s*import\s+([A-Z][A-Za-z0-9_']*(?:\.[A-Za-z0-9_']+)*)\s*$"
)
NAMESPACE_RE = re.compile(
    r"(?m)^namespace\s+([A-Z][A-Za-z0-9_']*(?:\.[A-Za-z0-9_']+)*)\s*$"
)
TOP_LEVEL_DECL_RE = re.compile(
    r"(?m)^(?:(?:noncomputable|private|protected)\s+)*"
    r"(?:def|theorem|abbrev|lemma|opaque)\s+([A-Za-z_][A-Za-z0-9_']*)\b"
)
ABSOLUTE_PATH_RE = re.compile(
    r"(?:^|[\s\"'`(])(?:/[A-Za-z0-9_.-]+){2,}|"
    r"[A-Za-z]:[\\/][^\s\"']+",
    re.MULTILINE,
)
TMP_PATH_RE = re.compile(r"(?:^|[/\\])(?:tmp|private/tmp)(?:[/\\]|$)")
FORBIDDEN_IMPORT_RE = re.compile(
    r"(?:^|\.)(?:Runtime|HardnessAggregate)(?:\.|$)"
)
FORBIDDEN_SOURCE_MARKERS = (
    "by_np_hard_resolver",
    "NativeTMNPHard",
    "TypedNPHardResultV1",
    "authoredHubRequest",
    "authoredHubResult",
    "authoredTargetRequest",
    "authoredTargetResult",
    "authoredExactNPHardness",
    "Generated.NPHardV2",
    "Benchmark.Hardness",
)


class NPHardPublicationError(ValueError):
    """Stable fail-closed H-K publication error."""

    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


def _fail(code: str, message: str) -> None:
    raise NPHardPublicationError(code, message)


def _expect(condition: bool, code: str, message: str) -> None:
    if not condition:
        _fail(code, message)


def _read_json(path: Path, *, label: str) -> dict[str, Any]:
    _expect(path.is_file(), "publication_evidence_missing", f"{label} is missing")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        _fail("publication_evidence_invalid", f"{label} is not valid JSON: {error}")
    _expect(
        isinstance(value, dict),
        "publication_evidence_invalid",
        f"{label} must be a JSON object",
    )
    return value


def _raw_sha256(data: bytes) -> str:
    return f"sha256:{hashlib.sha256(data).hexdigest()}"


def _file_sha256(path: Path) -> str:
    return _raw_sha256(path.read_bytes())


def _text_sha256(text: str) -> str:
    return _raw_sha256(text.encode("utf-8"))


def _content_hash(value: Mapping[str, Any], *, field: str) -> str:
    payload = dict(value)
    payload.pop(field, None)
    return sha256_id(payload)


def _write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def _normalized_command(command: Mapping[str, Any]) -> dict[str, Any]:
    stdout = command.get("stdout")
    stderr = command.get("stderr")
    return {
        "exit_code": command.get("exit_code"),
        "timed_out": command.get("timed_out"),
        "stdout_sha256": _text_sha256(stdout if isinstance(stdout, str) else ""),
        "stderr_sha256": _text_sha256(stderr if isinstance(stderr, str) else ""),
    }


def _path_within(path: Path, root: Path) -> bool:
    try:
        path.resolve().relative_to(root.resolve())
    except (OSError, ValueError):
        return False
    return True


def _evidence_file(
    value: Any,
    *,
    root: Path,
    label: str,
    expected_hash: str | None = None,
) -> Path:
    _expect(
        isinstance(value, str) and value.strip(),
        "publication_evidence_invalid",
        f"{label} path is absent",
    )
    path = Path(value).resolve()
    _expect(
        _path_within(path, root),
        "publication_evidence_path_escape",
        f"{label} escaped its case output root",
    )
    _expect(path.is_file(), "publication_evidence_missing", f"{label} is missing")
    if expected_hash is not None:
        _expect(
            expected_hash == _file_sha256(path),
            "publication_evidence_hash_mismatch",
            f"{label} hash drifted",
        )
    return path


def _portable_strings(value: Any) -> Iterable[str]:
    if isinstance(value, str):
        yield value
    elif isinstance(value, Mapping):
        for key, item in value.items():
            yield str(key)
            yield from _portable_strings(item)
    elif isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray)):
        for item in value:
            yield from _portable_strings(item)


def _assert_portable_manifest(value: Mapping[str, Any]) -> None:
    for text in _portable_strings(value):
        if ABSOLUTE_PATH_RE.search(text) or TMP_PATH_RE.search(text):
            _fail(
                "publication_manifest_path_forbidden",
                "publication manifest contains an absolute or temporary path",
            )


def _assert_candidate_source_safe(source: str) -> tuple[str, ...]:
    if ABSOLUTE_PATH_RE.search(source) or TMP_PATH_RE.search(source):
        _fail(
            "publication_candidate_path_forbidden",
            "candidate source contains an absolute or temporary path",
        )
    imports = tuple(IMPORT_RE.findall(source))
    _expect(
        imports,
        "publication_candidate_import_invalid",
        "candidate source has no imports",
    )
    if any(FORBIDDEN_IMPORT_RE.search(module) for module in imports):
        _fail(
            "publication_candidate_import_forbidden",
            "candidate imports Runtime or HardnessAggregate",
        )
    for marker in FORBIDDEN_SOURCE_MARKERS:
        if marker in source:
            _fail(
                "publication_candidate_tail_forbidden",
                f"candidate source retained forbidden hardness tail marker {marker}",
            )
    attribute = (
        f"@[{TYPED_EDGE_ATTRIBUTE}, {FINAL_COMPOSITION_ATTRIBUTE}]"
    )
    _expect(
        source.count(attribute) == 1,
        "publication_candidate_attribute_missing",
        "final reduction lacks the exact typed-edge/finalComposition attributes",
    )
    return imports


@dataclass(frozen=True)
class HJPublicationEvidence:
    run_path: Path
    score_path: Path
    run: Mapping[str, Any]
    score: Mapping[str, Any]
    evidence_mode: str
    h_j_report_id: str | None
    formal_h_j_complete: bool


@dataclass(frozen=True)
class ExtractedCaseEvidence:
    case_id: str
    label: str
    run_row: Mapping[str, Any]
    score_row: Mapping[str, Any]
    task: NPHardAuthoringTaskV2
    task_payload: Mapping[str, Any]
    plan_payload: Mapping[str, Any]
    final_source: str
    replay_source: str
    final_path: Path
    replay_path: Path
    task_path: Path
    plan_path: Path
    checkpoint_path: Path
    source_evidence: Mapping[str, Any]
    model_evidence: Mapping[str, Any]
    deletion_evidence: Mapping[str, Any]
    fresh_evidence: Mapping[str, Any]
    axiom_evidence: Mapping[str, Any]
    endpoint_evidence: Mapping[str, Any]


def load_h_j_publication_evidence(
    *,
    h_j_report: Path | None = None,
    run_report: Path | None = None,
    score_report: Path | None = None,
) -> HJPublicationEvidence:
    """Load the final H-J run/score pair or an explicit shadow-only probe.

    The main-report path is the only mode that can claim H-J completion.  The
    explicit pair is intentionally marked non-publishable and exists so H-K.1
    extraction and clean-shadow mechanics can be exercised before H-J closes.
    """

    if h_j_report is not None:
        _expect(
            run_report is None and score_report is None,
            "publication_evidence_mode_conflict",
            "main H-J evidence cannot be mixed with an explicit run/score pair",
        )
        report_path = h_j_report.resolve()
        report = _read_json(report_path, label="MAIN_H_J_FULL_REPORT")
        _expect(
            report.get("schema_version") == H_J_FULL_REPORT_SCHEMA
            and report.get("passed") is True,
            "publication_h_j_incomplete",
            "MAIN_H_J_FULL_REPORT is not the passing H-J report",
        )
        _expect(
            report.get("report_id") == _content_hash(report, field="report_id"),
            "publication_evidence_hash_mismatch",
            "MAIN_H_J_FULL_REPORT report_id drifted",
        )
        gates = report.get("gates")
        _expect(
            isinstance(gates, Mapping)
            and bool(gates)
            and all(value is True for value in gates.values()),
            "publication_h_j_incomplete",
            "MAIN_H_J_FULL_REPORT gates are not all passing",
        )
        capability = report.get("substage_capability_evidence")
        reports = capability.get("reports") if isinstance(capability, Mapping) else None
        _expect(
            isinstance(reports, list) and len(reports) == 5,
            "publication_h_j_incomplete",
            "MAIN_H_J_FULL_REPORT lacks five substage reports",
        )
        final = reports[-1]
        _expect(
            isinstance(final, Mapping)
            and final.get("stage") == H_J_FINAL_STAGE
            and final.get("contract_epoch") == "v2"
            and final.get("contract_version") == "v2b",
            "publication_h_j_incomplete",
            "MAIN_H_J_FULL_REPORT final evidence is not H-J.5/v2b",
        )
        run_record = final.get("run")
        score_record = final.get("score")
        _expect(
            isinstance(run_record, Mapping) and isinstance(score_record, Mapping),
            "publication_evidence_invalid",
            "H-J.5 run/score provenance is absent",
        )
        run_path = Path(str(run_record.get("file", ""))).resolve()
        score_path = Path(str(score_record.get("file", ""))).resolve()
        _expect(
            run_record.get("sha256") == _file_sha256(run_path)
            and score_record.get("sha256") == _file_sha256(score_path),
            "publication_evidence_hash_mismatch",
            "H-J.5 run/score files drifted from MAIN_H_J_FULL_REPORT",
        )
        mode = "main_h_j_full_report"
        h_j_report_id = str(report["report_id"])
        formal_h_j_complete = True
    else:
        _expect(
            run_report is not None and score_report is not None,
            "publication_evidence_missing",
            "provide MAIN_H_J_FULL_REPORT or an explicit run/score probe",
        )
        run_path = run_report.resolve()
        score_path = score_report.resolve()
        mode = "explicit_shadow_probe"
        h_j_report_id = None
        formal_h_j_complete = False

    run = _read_json(run_path, label="H-J capability run")
    score = _read_json(score_path, label="H-J capability score")
    _expect(
        run.get("schema_version") == CAPABILITY_RUN_SCHEMA
        and run.get("run_valid") is True,
        "publication_evidence_invalid",
        "publication source run is not a valid v2 capability run",
    )
    _expect(
        run.get("run_id") == _content_hash(run, field="run_id"),
        "publication_evidence_hash_mismatch",
        "publication source run_id drifted",
    )
    _expect(
        score.get("schema_version") == CAPABILITY_SCORE_SCHEMA
        and score.get("run_valid") is True
        and score.get("score_valid") is True
        and score.get("run_id") == run.get("run_id"),
        "publication_evidence_invalid",
        "publication source score is not a valid matching v2 score",
    )
    _expect(
        score.get("score_id") == _content_hash(score, field="score_id"),
        "publication_evidence_hash_mismatch",
        "publication source score_id drifted",
    )
    model = run.get("model")
    security = run.get("security")
    _expect(
        isinstance(model, Mapping)
        and model.get("model") == "deepseek-v4-flash"
        and model.get("base_url") == "https://api.deepseek.com"
        and model.get("max_retries") == 0
        and model.get("reasoning_effort") == "low"
        and model.get("temperature") == 0.0
        and model.get("timeout_seconds") == 300
        and model.get("max_tokens") == 16000,
        "publication_model_evidence_invalid",
        "publication source is not the formal DeepSeek profile",
    )
    _expect(
        isinstance(security, Mapping)
        and security.get("formal_model_profile_matched") is True
        and security.get("api_key_or_authorization_absent") is True
        and security.get("fixture_model_used") is False
        and security.get("cached_or_recorded_response_used") is False,
        "publication_model_evidence_invalid",
        "publication source model/security evidence is invalid",
    )
    provenance = score.get("provenance")
    _expect(
        isinstance(provenance, Mapping)
        and isinstance(provenance.get("run_report"), Mapping)
        and provenance["run_report"].get("sha256") == _file_sha256(run_path),
        "publication_evidence_hash_mismatch",
        "score provenance does not bind the run report",
    )
    return HJPublicationEvidence(
        run_path=run_path,
        score_path=score_path,
        run=run,
        score=score,
        evidence_mode=mode,
        h_j_report_id=h_j_report_id,
        formal_h_j_complete=formal_h_j_complete,
    )


def _case_rows(
    evidence: HJPublicationEvidence, case_id: str
) -> tuple[Mapping[str, Any], Mapping[str, Any]]:
    run_rows = [
        row
        for row in evidence.run.get("cases", [])
        if isinstance(row, Mapping) and row.get("case_id") == case_id
    ]
    score_rows = [
        row
        for row in evidence.score.get("cases", [])
        if isinstance(row, Mapping) and row.get("case_id") == case_id
    ]
    _expect(
        len(run_rows) == len(score_rows) == 1,
        "publication_case_evidence_missing",
        f"{case_id} is not unique in the run and score",
    )
    return run_rows[0], score_rows[0]


def _validate_model_evidence(
    raw: Mapping[str, Any],
    task: NPHardAuthoringTaskV2,
    *,
    case_root: Path,
) -> dict[str, Any]:
    calls = raw.get("model_call_ledger")
    _expect(
        isinstance(calls, list) and calls,
        "publication_model_evidence_invalid",
        "authored case lacks model call evidence",
    )
    node_ids = {node.node_id for node in task.gap_nodes}
    observed: set[str] = set()
    normalized: list[dict[str, Any]] = []
    for index, call in enumerate(calls):
        _expect(
            isinstance(call, Mapping),
            "publication_model_evidence_invalid",
            f"model call {index} is not an object",
        )
        node_id = call.get("node_id")
        _expect(
            node_id in node_ids
            and call.get("called") is True
            and call.get("ok") is True
            and call.get("status_code") == 200
            and call.get("provider_attempts") == 1
            and call.get("error") is None,
            "publication_model_evidence_invalid",
            f"model call {index} is not a successful HTTP 200 node call",
        )
        prompt = _evidence_file(
            call.get("prompt_file"),
            root=case_root,
            label=f"{node_id} prompt",
        )
        response = _evidence_file(
            call.get("response_file"),
            root=case_root,
            label=f"{node_id} response",
        )
        response_payload = _read_json(response, label=f"{node_id} response")
        _expect(
            call.get("prompt_sha256")
            == sha256_id(prompt.read_text(encoding="utf-8"))
            and isinstance(response_payload.get("content"), str)
            and call.get("response_sha256")
            == sha256_id(response_payload["content"]),
            "publication_model_evidence_invalid",
            f"{node_id} prompt/response content hash drifted",
        )
        request_id = call.get("request_id")
        _expect(
            isinstance(request_id, str) and TAGGED_SHA256_RE.fullmatch(request_id),
            "publication_model_evidence_invalid",
            f"{node_id} request identity is invalid",
        )
        observed.add(str(node_id))
        normalized.append(
            {
                "node_id": node_id,
                "attempt": call.get("attempt"),
                "request_id": request_id,
                "prompt_sha256": call.get("prompt_sha256"),
                "prompt_file_sha256": _file_sha256(prompt),
                "response_sha256": call.get("response_sha256"),
                "response_file_sha256": _file_sha256(response),
                "status_code": 200,
                "finish_reason": call.get("finish_reason"),
                "usage": call.get("usage"),
            }
        )
    _expect(
        observed == node_ids,
        "publication_model_evidence_invalid",
        "model ledger does not cover every authored DAG node",
    )
    return {
        "provider": "DeepSeek",
        "model": "deepseek-v4-flash",
        "call_count": len(normalized),
        "node_count": len(node_ids),
        "calls": normalized,
        "evidence_id": sha256_id(normalized),
    }


def _validate_publication_nodes(
    raw: Mapping[str, Any],
    runtime: Mapping[str, Any],
    task: NPHardAuthoringTaskV2,
    *,
    case_root: Path,
    final_source: str,
) -> tuple[dict[str, Any], dict[str, Any]]:
    expected_nodes = [node.node_id for node in task.gap_nodes]
    publications = raw.get("candidate_publication")
    fresh = raw.get("fresh_core")
    _expect(
        isinstance(publications, list)
        and len(publications) == len(expected_nodes)
        and isinstance(fresh, Mapping)
        and fresh.get("passed") is True
        and fresh.get("count") == len(expected_nodes)
        and runtime.get("fresh_core_rediscoveries") == len(expected_nodes),
        "publication_fresh_core_invalid",
        "fresh-core publication coverage differs from the authored DAG",
    )
    normalized_publications: list[dict[str, Any]] = []
    body_hashes: dict[str, str] = {}
    publication_by_node = {
        str(publication.get("node_id")): publication
        for publication in publications
        if isinstance(publication, Mapping)
    }
    _expect(
        set(publication_by_node) == set(expected_nodes),
        "publication_fresh_core_invalid",
        "fresh-core publication identities differ from the authored DAG",
    )
    for expected_node in expected_nodes:
        publication = publication_by_node[expected_node]
        _expect(
            isinstance(publication, Mapping)
            and publication.get("node_id") == expected_node,
            "publication_fresh_core_invalid",
            f"publication node identity drifted at {expected_node}",
        )
        manifest_path = _evidence_file(
            publication.get("manifest_file"),
            root=case_root,
            label=f"{expected_node} publication manifest",
            expected_hash=publication.get("manifest_sha256"),
        )
        manifest = _read_json(manifest_path, label=f"{expected_node} publication manifest")
        body_path = manifest_path.parent / "body.lean"
        _expect(
            body_path.is_file()
            and manifest.get("node_id") == expected_node
            and manifest.get("declaration")
            == next(node.declaration for node in task.gap_nodes if node.node_id == expected_node)
            and manifest.get("body_sha256") == sha256_id(body_path.read_text(encoding="utf-8"))
            and manifest.get("body_sha256") == publication.get("body_sha256")
            and manifest.get("fresh_core_evidence_sha256")
            == publication.get("fresh_core_evidence_sha256")
            and manifest.get("compiler_inserted_math_token_count") == 0,
            "publication_fresh_core_invalid",
            f"{expected_node} publication manifest/body drifted",
        )
        body_text = body_path.read_text(encoding="utf-8")
        _expect(
            body_text in final_source or textwrap.indent(body_text.rstrip(), "  ") in final_source,
            "publication_model_node_drifted",
            f"{expected_node} accepted body is absent from Final.lean",
        )
        body_hashes[expected_node] = str(manifest["body_sha256"])
        normalized_publications.append(
            {
                "node_id": expected_node,
                "declaration": manifest["declaration"],
                "body_sha256": manifest["body_sha256"],
                "cumulative_source_sha256": manifest["cumulative_source_sha256"],
                "manifest_sha256": _file_sha256(manifest_path),
                "fresh_core_evidence_sha256": manifest[
                    "fresh_core_evidence_sha256"
                ],
                "worker_evidence_sha256": manifest["worker_evidence_sha256"],
            }
        )

    deletion = raw.get("deletion_audit")
    deletion_nodes = deletion.get("nodes") if isinstance(deletion, Mapping) else None
    _expect(
        isinstance(deletion, Mapping)
        and deletion.get("passed") is True
        and deletion.get("node_count") == len(expected_nodes)
        and isinstance(deletion_nodes, list)
        and len(deletion_nodes) == len(expected_nodes)
        and runtime.get("deletion_audits") == deletion_nodes,
        "publication_deletion_audit_invalid",
        "deletion audit does not cover the authored DAG",
    )
    normalized_deletions: list[dict[str, Any]] = []
    for expected_node, deletion_node in zip(expected_nodes, deletion_nodes, strict=True):
        _expect(
            isinstance(deletion_node, Mapping)
            and deletion_node.get("node_id") == expected_node
            and deletion_node.get("body_sha256") == body_hashes[expected_node]
            and deletion_node.get("passed") is True
            and deletion_node.get("diagnostic_matched") is True,
            "publication_deletion_audit_invalid",
            f"deletion audit failed closed binding for {expected_node}",
        )
        audit_path = _evidence_file(
            deletion_node.get("audit_file"),
            root=case_root,
            label=f"{expected_node} deletion audit",
            expected_hash=deletion_node.get("audit_file_sha256"),
        )
        command = deletion_node.get("command")
        _expect(
            isinstance(command, Mapping)
            and command.get("timed_out") is False
            and isinstance(command.get("exit_code"), int)
            and command.get("exit_code") != 0,
            "publication_deletion_audit_invalid",
            f"{expected_node} deletion command did not fail",
        )
        normalized_deletions.append(
            {
                "node_id": expected_node,
                "declaration": deletion_node.get("declaration"),
                "body_sha256": deletion_node.get("body_sha256"),
                "audit_file_sha256": _file_sha256(audit_path),
                "diagnostic_matched": True,
                "command": _normalized_command(command),
            }
        )
    return (
        {
            "node_count": len(normalized_publications),
            "nodes": normalized_publications,
            "evidence_id": sha256_id(normalized_publications),
        },
        {
            "node_count": len(normalized_deletions),
            "nodes": normalized_deletions,
            "evidence_id": sha256_id(normalized_deletions),
        },
    )


def extract_h_j_publication_case(
    evidence: HJPublicationEvidence,
    case_id: str,
    *,
    repo_root: Path,
) -> ExtractedCaseEvidence:
    """Extract and independently bind one supported H-J authored case."""

    specification = SUPPORTED_PUBLICATION_CASES.get(case_id)
    _expect(
        specification is not None,
        "publication_case_unsupported",
        f"{case_id} is not in the first H-K publication interface",
    )
    run_row, score_row = _case_rows(evidence, case_id)
    _expect(
        run_row.get("protocol_valid") is True
        and run_row.get("public_status") == "VERIFIED"
        and run_row.get("internal_status") == "VERIFIED"
        and score_row.get("capability_success") is True
        and score_row.get("expected_outcome_matched") is True
        and score_row.get("outcome_class") == "first_authoring"
        and score_row.get("public_status") == "VERIFIED"
        and score_row.get("evidence_sha256") == run_row.get("evidence_sha256"),
        "publication_case_not_verified",
        f"{case_id} is not a verified first-authoring case",
    )
    raw = run_row.get("raw_result")
    _expect(
        isinstance(raw, Mapping) and raw.get("status") == "VERIFIED",
        "publication_case_evidence_invalid",
        f"{case_id} lacks a verified raw result",
    )
    task_payload = raw.get("capability_dag")
    try:
        task = NPHardAuthoringTaskV2.from_dict(task_payload)
    except NPHardAuthoringContractError as error:
        _fail(
            "publication_task_invalid",
            f"{case_id} task failed the v2 contract: {error.code}",
        )
    _expect(
        task.target_problem.term == specification["target"]
        and task.target_problem.term == run_row.get("canonical_problem")
        and task.required_direction == "source_to_target",
        "publication_endpoint_mismatch",
        f"{case_id} endpoint/direction differs from the supported interface",
    )
    case_root_value = run_row.get("output_dir")
    _expect(
        isinstance(case_root_value, str) and case_root_value.strip(),
        "publication_case_evidence_invalid",
        f"{case_id} output root is absent",
    )
    case_root = Path(case_root_value).resolve()
    _expect(
        case_root.is_dir(),
        "publication_evidence_missing",
        f"{case_id} output root is missing",
    )
    artifact = raw.get("artifact")
    replay = raw.get("independent_replay")
    runtime = raw.get("authoring_runtime")
    _expect(
        isinstance(artifact, Mapping)
        and artifact.get("authority") == "independent-lean-process"
        and artifact.get("endpoint") == task.target_problem.term
        and isinstance(replay, Mapping)
        and replay.get("passed") is True
        and replay.get("authority") == "independent-lean-process"
        and isinstance(runtime, Mapping)
        and runtime.get("status") == "VERIFIED"
        and runtime.get("task_request_id") == task.request_id,
        "publication_case_evidence_invalid",
        f"{case_id} artifact/replay/runtime evidence is invalid",
    )
    final_path = _evidence_file(
        artifact.get("file"),
        root=case_root,
        label=f"{case_id} Final.lean",
        expected_hash=artifact.get("sha256"),
    )
    replay_path = _evidence_file(
        replay.get("file"),
        root=case_root,
        label=f"{case_id} Replay.lean",
        expected_hash=replay.get("sha256"),
    )
    final_source = final_path.read_text(encoding="utf-8")
    replay_source = replay_path.read_text(encoding="utf-8")
    _expect(
        final_source == replay_source,
        "publication_replay_mismatch",
        f"{case_id} Replay.lean differs from Final.lean",
    )
    task_path = case_root / "authoring/task.json"
    plan_path = case_root / "planning/plan.json"
    checkpoint_value = runtime.get("checkpoint_path")
    checkpoint_path = _evidence_file(
        checkpoint_value,
        root=case_root,
        label=f"{case_id} authoring checkpoint",
        expected_hash=runtime.get("checkpoint_file_sha256"),
    )
    task_file_payload = _read_json(task_path, label=f"{case_id} task")
    plan_payload = _read_json(plan_path, label=f"{case_id} plan")
    _expect(
        task_file_payload == task_payload
        and plan_payload.get("task") == task_payload
        and plan_payload.get("status") == "PLANNED"
        and plan_payload.get("terminal_node_id") == task.terminal_node_id
        and plan_payload.get("final_program_node_id") == task.final_program_node_id,
        "publication_task_invalid",
        f"{case_id} task/plan/DAG evidence drifted",
    )
    expected_ids = [node.node_id for node in task.gap_nodes]
    _expect(
        runtime.get("accepted_nodes") == expected_ids,
        "publication_task_invalid",
        f"{case_id} accepted-node order differs from the task DAG",
    )
    fresh_evidence, deletion_evidence = _validate_publication_nodes(
        raw,
        runtime,
        task,
        case_root=case_root,
        final_source=final_source,
    )
    model_evidence = _validate_model_evidence(
        raw, task, case_root=case_root
    )
    axiom = raw.get("axiom_audit")
    commands = runtime.get("commands")
    _expect(
        isinstance(axiom, Mapping)
        and axiom.get("passed") is True
        and axiom.get("authority") == "Lean assert_standard_axioms"
        and "assert_standard_axioms" in final_source
        and isinstance(commands, list)
        and len(commands) >= 2,
        "publication_axiom_audit_invalid",
        f"{case_id} lacks passing standard-axiom evidence",
    )
    final_commands = [
        command
        for command in commands
        if isinstance(command, Mapping)
        and isinstance(command.get("command"), list)
        and command["command"]
        and Path(str(command["command"][-1])).name in {"Final.lean", "Replay.lean"}
    ]
    _expect(
        len(final_commands) == 2
        and all(
            command.get("exit_code") == 0 and command.get("timed_out") is False
            for command in final_commands
        ),
        "publication_axiom_audit_invalid",
        f"{case_id} final/replay Lean commands did not both pass",
    )
    axiom_evidence = {
        "authority": "Lean assert_standard_axioms",
        "passed": True,
        "commands": [_normalized_command(command) for command in final_commands],
        "evidence_id": sha256_id(
            [_normalized_command(command) for command in final_commands]
        ),
    }
    endpoint_evidence = {
        "direction": "source_to_target",
        "source": task.source_problem.term,
        "target": task.target_problem.term,
        "exact_reduction_type": task.final_exact_type,
        "selected_hub": raw.get("selected_hub"),
        "artifact_endpoint": artifact.get("endpoint"),
    }
    _expect(
        endpoint_evidence["selected_hub"] == task.source_problem.term,
        "publication_endpoint_mismatch",
        f"{case_id} selected hub differs from the exact task source",
    )
    source_evidence = {
        "run_id": evidence.run.get("run_id"),
        "run_report_sha256": _file_sha256(evidence.run_path),
        "score_id": evidence.score.get("score_id"),
        "score_report_sha256": _file_sha256(evidence.score_path),
        "case_evidence_sha256": run_row.get("evidence_sha256"),
        "final_sha256": _file_sha256(final_path),
        "replay_sha256": _file_sha256(replay_path),
        "task_sha256": _file_sha256(task_path),
        "plan_sha256": _file_sha256(plan_path),
        "plan_id": plan_payload.get("plan_id"),
        "checkpoint_sha256": _file_sha256(checkpoint_path),
        "task_request_id": task.request_id,
    }
    return ExtractedCaseEvidence(
        case_id=case_id,
        label=str(specification["label"]),
        run_row=run_row,
        score_row=score_row,
        task=task,
        task_payload=task_payload,
        plan_payload=plan_payload,
        final_source=final_source,
        replay_source=replay_source,
        final_path=final_path,
        replay_path=replay_path,
        task_path=task_path,
        plan_path=plan_path,
        checkpoint_path=checkpoint_path,
        source_evidence=source_evidence,
        model_evidence=model_evidence,
        deletion_evidence=deletion_evidence,
        fresh_evidence=fresh_evidence,
        axiom_evidence=axiom_evidence,
        endpoint_evidence=endpoint_evidence,
    )


def _extract_declaration_block(source: str, short_name: str) -> str:
    matches = [
        match
        for match in TOP_LEVEL_DECL_RE.finditer(source)
        if match.group(1) == short_name
    ]
    _expect(
        len(matches) == 1,
        "publication_candidate_render_failed",
        f"Final.lean does not contain exactly one declaration {short_name}",
    )
    start = matches[0].start()
    later = TOP_LEVEL_DECL_RE.search(source, matches[0].end())
    namespace = NAMESPACE_RE.search(source)
    _expect(
        namespace is not None,
        "publication_candidate_render_failed",
        "Final.lean has no generated namespace",
    )
    end_namespace = source.find(f"\nend {namespace.group(1)}", matches[0].end())
    _expect(
        end_namespace >= 0,
        "publication_candidate_render_failed",
        "Final.lean generated namespace is not closed",
    )
    end = min(
        [
            position
            for position in (
                later.start() if later is not None else -1,
                end_namespace,
            )
            if position >= 0
        ]
    )
    return source[start:end].strip() + "\n"


def _declaration_body(block: str) -> str:
    _expect(
        ":=" in block,
        "publication_candidate_render_failed",
        "authored declaration block has no body",
    )
    return textwrap.dedent(block.split(":=", 1)[1]).lstrip("\n").rstrip() + "\n"


def _render_candidate_source(
    extracted: ExtractedCaseEvidence,
) -> tuple[str, dict[str, Any]]:
    task = extracted.task
    namespace_match = NAMESPACE_RE.search(extracted.final_source)
    _expect(
        namespace_match is not None,
        "publication_candidate_render_failed",
        "Final.lean has no generated namespace",
    )
    old_namespace = namespace_match.group(1)
    evidence_seed = sha256_id(
        {
            "case_id": extracted.case_id,
            "task_request_id": task.request_id,
            "final_sha256": extracted.source_evidence["final_sha256"],
            "replay_sha256": extracted.source_evidence["replay_sha256"],
        }
    ).removeprefix("sha256:")[:20]
    new_module = (
        f"ComplexityReduction.Generated.Hardness.C{evidence_seed}.Reduction"
    )
    new_namespace = new_module
    imports = list(IMPORT_RE.findall(extracted.final_source))
    _expect(
        all(module in task.allowed_imports for module in imports),
        "publication_candidate_import_invalid",
        "Final.lean imports differ from the task allowlist",
    )
    imports = [module for module in imports if not FORBIDDEN_IMPORT_RE.search(module)]
    for support_module in PUBLICATION_SUPPORT_IMPORTS:
        if support_module not in imports:
            imports.append(support_module)
    imports = list(dict.fromkeys(imports))

    first_decl = TOP_LEVEL_DECL_RE.search(extracted.final_source)
    _expect(
        first_decl is not None,
        "publication_candidate_render_failed",
        "Final.lean has no authored declarations",
    )
    namespace_end = namespace_match.end()
    prelude = extracted.final_source[namespace_end:first_decl.start()].strip()
    model_blocks: list[str] = []
    model_nodes: list[dict[str, Any]] = []
    publication_by_node = {
        str(row["node_id"]): row for row in extracted.fresh_evidence["nodes"]
    }
    for node in task.gap_nodes:
        short_name = node.declaration.rsplit(".", 1)[-1]
        block = _extract_declaration_block(extracted.final_source, short_name)
        body = _declaration_body(block)
        _expect(
            sha256_id(body) == publication_by_node[node.node_id]["body_sha256"],
            "publication_model_node_drifted",
            f"Final.lean body for {node.node_id} differs from its accepted publication",
        )
        rendered = block.replace(old_namespace, new_namespace)
        model_blocks.append(rendered.rstrip())
        model_nodes.append(
            {
                "node_id": node.node_id,
                "capability": node.capability,
                "depends_on": list(node.depends_on),
                "original_declaration": node.declaration,
                "published_declaration": node.declaration.replace(
                    old_namespace, new_namespace, 1
                ),
                "accepted_body_sha256": sha256_id(body),
                "rendered_body_sha256": sha256_id(
                    _declaration_body(rendered)
                ),
                "exact_type_sha256": sha256_id(node.exact_type),
            }
        )

    final_short = task.final_candidate_declaration.rsplit(".", 1)[-1]
    final_block = _extract_declaration_block(extracted.final_source, final_short)
    _expect(
        task.final_exact_type in " ".join(final_block.split()),
        "publication_endpoint_mismatch",
        "runner-owned CertifiedReduction does not have the task exact type",
    )
    rendered_final = final_block.replace(old_namespace, new_namespace).rstrip()
    final_attribute = f"@[{TYPED_EDGE_ATTRIBUTE}, {FINAL_COMPOSITION_ATTRIBUTE}]"
    rendered_final = f"{final_attribute}\n{rendered_final}"
    published_final = task.final_candidate_declaration.replace(
        old_namespace, new_namespace, 1
    )
    assertion_declarations = [
        row["published_declaration"] for row in model_nodes
    ] + [published_final]
    assertion = "assert_standard_axioms\n  " + ",\n  ".join(assertion_declarations)
    source = (
        "/-\n"
        "H-K shadow publication candidate.  This module contains only the\n"
        "model-authored reduction DAG and runner-owned CertifiedReduction.\n"
        "It intentionally provides no native hardness theorem.\n"
        "-/\n\n"
        + "\n".join(f"import {module}" for module in imports)
        + f"\n\nnamespace {new_namespace}\n\n"
        + (prelude + "\n\n" if prelude else "")
        + "\n\n".join(model_blocks)
        + "\n\n"
        + rendered_final
        + f"\n\nend {new_namespace}\n\n"
        + assertion
        + "\n"
    )
    _assert_candidate_source_safe(source)
    _expect(
        all(
            row["published_declaration"] in source
            for row in model_nodes
        )
        and published_final in source,
        "publication_candidate_render_failed",
        "rendered candidate lost a model node or the final reduction",
    )
    route = {
        "task_class": task.task_class,
        "source": task.source_problem.term,
        "target": task.target_problem.term,
        "direction": task.required_direction,
        "selected_hub": extracted.endpoint_evidence["selected_hub"],
        "terminal_node_id": task.terminal_node_id,
        "final_program_node_id": task.final_program_node_id,
        "model_nodes": model_nodes,
        "runner_owned_reduction": {
            "original_declaration": task.final_candidate_declaration,
            "published_declaration": published_final,
            "exact_type": task.final_exact_type,
            "exact_type_sha256": sha256_id(task.final_exact_type),
            "attributes": [TYPED_EDGE_ATTRIBUTE, FINAL_COMPOSITION_ATTRIBUTE],
        },
        "original_planner_dag_sha256": sha256_id(
            extracted.plan_payload.get("capability_dag")
        ),
    }
    return source, {
        "module": new_module,
        "namespace": new_namespace,
        "declaration": published_final,
        "imports": imports,
        "route": route,
    }


def _module_source(lean_root: Path, module: str) -> Path | None:
    path = lean_root / "Reference" / Path(*module.split(".")).with_suffix(".lean")
    return path if path.is_file() else None


def _project_dependency_closure(
    lean_root: Path,
    root_imports: Sequence[str],
    *,
    candidate_module: str,
) -> dict[str, Any]:
    visited: set[str] = set()
    visiting: set[str] = set()
    project_files: dict[str, str] = {}
    external_imports: set[str] = set()
    graph: dict[str, list[str]] = {}
    cycles: list[list[str]] = []
    forbidden_modules: set[str] = set()

    def visit(module: str, stack: list[str]) -> None:
        if FORBIDDEN_IMPORT_RE.search(module):
            forbidden_modules.add(module)
            return
        if module == candidate_module:
            cycles.append([*stack, module])
            return
        if module in visiting:
            try:
                start = stack.index(module)
            except ValueError:
                start = 0
            cycles.append([*stack[start:], module])
            return
        if module in visited:
            return
        source_path = _module_source(lean_root, module)
        if source_path is None:
            external_imports.add(module)
            visited.add(module)
            return
        visiting.add(module)
        source = source_path.read_text(encoding="utf-8")
        imports = list(IMPORT_RE.findall(source))
        graph[module] = imports
        relative = source_path.relative_to(lean_root.parent).as_posix()
        project_files[relative] = _file_sha256(source_path)
        for dependency in imports:
            visit(dependency, [*stack, module])
        visiting.remove(module)
        visited.add(module)

    for root in root_imports:
        visit(root, [candidate_module])
    _expect(
        not cycles,
        "publication_import_cycle",
        "candidate dependency graph contains an import cycle",
    )
    _expect(
        not forbidden_modules,
        "publication_candidate_import_forbidden",
        "candidate dependency closure reaches Runtime or HardnessAggregate",
    )
    return {
        "project_source_files": dict(sorted(project_files.items())),
        "project_source_file_count": len(project_files),
        "external_import_roots": sorted(external_imports),
        "graph_sha256": sha256_id(
            {key: graph[key] for key in sorted(graph)}
        ),
        "closure_sha256": sha256_id(dict(sorted(project_files.items()))),
        "candidate_cycle_absent": True,
        "runtime_or_hardness_aggregate_import_absent": True,
    }


def _validate_task_dependency_snapshot(
    task: NPHardAuthoringTaskV2,
    *,
    repo_root: Path,
    lean_root: Path,
) -> dict[str, str]:
    dependencies = dict(task.dependency_hashes)
    expected_static = {
        "content:lake-manifest": _file_sha256(lean_root / "lake-manifest.json"),
        "content:lean-toolchain": _file_sha256(lean_root / "lean-toolchain"),
    }
    for key, observed in expected_static.items():
        _expect(
            dependencies.get(key) == observed,
            "publication_dependency_stale",
            f"task dependency {key} drifted",
        )
    public_hashes: dict[str, str] = {}
    for key, expected in dependencies.items():
        if not key.startswith("public:"):
            continue
        relative = key.removeprefix("public:")
        path = (repo_root / relative).resolve()
        _expect(
            _path_within(path, repo_root) and path.is_file(),
            "publication_dependency_stale",
            f"task public dependency {relative} is missing",
        )
        observed = _file_sha256(path)
        _expect(
            observed == expected,
            "publication_dependency_stale",
            f"task public dependency {relative} hash drifted",
        )
        public_hashes[relative] = observed
    _expect(
        public_hashes,
        "publication_dependency_stale",
        "task exposes no public source dependencies",
    )
    return dict(sorted(public_hashes.items()))


def _toolchain_evidence(lean_root: Path) -> dict[str, Any]:
    toolchain = lean_root / "lean-toolchain"
    manifest = lean_root / "lake-manifest.json"
    lakefile = lean_root / "lakefile.toml"
    _expect(
        toolchain.is_file() and manifest.is_file() and lakefile.is_file(),
        "publication_dependency_stale",
        "Lean toolchain/lake files are incomplete",
    )
    return {
        "lean_toolchain": toolchain.read_text(encoding="utf-8").strip(),
        "lean_toolchain_sha256": _file_sha256(toolchain),
        "lake_manifest_sha256": _file_sha256(manifest),
        "lakefile_sha256": _file_sha256(lakefile),
    }


def _candidate_content_payload(manifest: Mapping[str, Any]) -> dict[str, Any]:
    candidate = manifest["candidate"]
    dependencies = manifest["dependencies"]
    return {
        "schema_version": manifest["schema_version"],
        "case_id": manifest["case_id"],
        "canonical_identity_id": manifest["canonical_identity_id"],
        "source_hub": manifest["source_hub"],
        "canonical_endpoint": manifest["canonical_endpoint"],
        "route": manifest["route"],
        "candidate": {
            "module": candidate["module"],
            "declaration": candidate["declaration"],
            "source_sha256": candidate["source_sha256"],
            "attributes": candidate["attributes"],
        },
        "dependencies": {
            "toolchain": dependencies["toolchain"],
            "closure_sha256": dependencies["closure"]["closure_sha256"],
            "graph_sha256": dependencies["closure"]["graph_sha256"],
        },
    }


def reseal_candidate_manifest(manifest: Mapping[str, Any]) -> dict[str, Any]:
    """Recompute deterministic content and manifest IDs after a controlled edit.

    This is primarily useful to exercise fail-closed security mutations: a
    mutation can be content-addressed correctly and must still be rejected for
    its semantic policy violation.
    """

    value = json.loads(json.dumps(manifest))
    value["candidate_content_id"] = sha256_id(_candidate_content_payload(value))
    value.pop("manifest_id", None)
    value["manifest_id"] = sha256_id(value)
    return value


def _audit_source(manifest: Mapping[str, Any]) -> str:
    candidate = manifest["candidate"]
    route = manifest["route"]
    declarations = [
        node["published_declaration"] for node in route["model_nodes"]
    ] + [candidate["declaration"]]
    exact_type = route["runner_owned_reduction"]["exact_type"]
    attribute_decl = candidate["declaration"]
    return (
        f"import {candidate['module']}\n\n"
        "open ComplexityReduction\n\n"
        f"noncomputable example : {exact_type} :=\n"
        f"  {candidate['declaration']}\n\n"
        "assert_standard_axioms\n  "
        + ",\n  ".join(declarations)
        + "\n\n"
        + "run_cmd\n"
        + "  let environment ← Lean.getEnv\n"
        + "  unless ComplexityReduction.Annotations.typedEdgeAttr.hasTag "
        + f"environment ``{attribute_decl} do\n"
        + "    throwError \"published reduction lacks typed-edge attribute\"\n"
        + "  unless ComplexityReduction.Annotations.componentFinalCompositionAttr.hasTag "
        + f"environment ``{attribute_decl} do\n"
        + "    throwError \"published reduction lacks finalComposition attribute\"\n"
    )


def _prepare_shadow_workspace(lean_root: Path, shadow_root: Path) -> Path:
    _expect(
        not shadow_root.exists(),
        "publication_output_not_empty",
        "shadow workspace already exists; choose a fresh output root",
    )
    shadow_lean = shadow_root / "Lean"
    shadow_lean.mkdir(parents=True)
    shutil.copytree(lean_root / "Reference", shadow_lean / "Reference")
    for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
        shutil.copy2(lean_root / name, shadow_lean / name)
    _expect(
        not any((shadow_lean / "Reference").rglob("*.olean"))
        and not (shadow_lean / ".lake/build").exists(),
        "publication_shadow_not_clean",
        "shadow workspace contains an old project .olean/build cache",
    )
    packages = lean_root / ".lake/packages"
    _expect(
        packages.is_dir(),
        "publication_dependency_stale",
        "declared Lake package cache is unavailable",
    )
    (shadow_lean / ".lake").mkdir()
    os.symlink(packages, shadow_lean / ".lake/packages", target_is_directory=True)
    return shadow_lean


def _run_command(
    command: Sequence[str], *, cwd: Path, timeout_seconds: int
) -> dict[str, Any]:
    try:
        completed = subprocess.run(
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
            "exit_code": completed.returncode,
            "timed_out": False,
            "stdout_sha256": _text_sha256(completed.stdout),
            "stderr_sha256": _text_sha256(completed.stderr),
            "stdout": completed.stdout,
            "stderr": completed.stderr,
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


def _manifest_without_command_output(command: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "command": command["command"],
        "exit_code": command["exit_code"],
        "timed_out": command["timed_out"],
        "stdout_sha256": command["stdout_sha256"],
        "stderr_sha256": command["stderr_sha256"],
    }


def _build_manifest_skeleton(
    *,
    evidence: HJPublicationEvidence,
    extracted: ExtractedCaseEvidence,
    source: str,
    rendered: Mapping[str, Any],
    public_dependency_hashes: Mapping[str, str],
    closure: Mapping[str, Any],
    toolchain: Mapping[str, Any],
) -> dict[str, Any]:
    return {
        "schema_version": PUBLICATION_CANDIDATE_MANIFEST_SCHEMA,
        "state": PUBLICATION_STATE,
        "publication_eligible": evidence.formal_h_j_complete,
        "publication_activation_performed": False,
        "case_id": extracted.case_id,
        "label": extracted.label,
        "canonical_identity_id": extracted.run_row.get("canonical_identity_id"),
        "canonical_endpoint": extracted.task.target_problem.term,
        "source_hub": extracted.task.source_problem.term,
        "direction": "source_to_target",
        "h_j_evidence": {
            "mode": evidence.evidence_mode,
            "formal_h_j_complete": evidence.formal_h_j_complete,
            "h_j_report_id": evidence.h_j_report_id,
            **dict(extracted.source_evidence),
        },
        "route": rendered["route"],
        "model_evidence": extracted.model_evidence,
        "fresh_core_evidence": extracted.fresh_evidence,
        "deletion_evidence": extracted.deletion_evidence,
        "axiom_evidence": extracted.axiom_evidence,
        "endpoint_evidence": extracted.endpoint_evidence,
        "candidate": {
            "module": rendered["module"],
            "namespace": rendered["namespace"],
            "declaration": rendered["declaration"],
            "source_file": "Reduction.lean",
            "source_sha256": _text_sha256(source),
            "imports": list(rendered["imports"]),
            "attributes": [TYPED_EDGE_ATTRIBUTE, FINAL_COMPOSITION_ATTRIBUTE],
            "native_hardness_tail_present": False,
        },
        "dependencies": {
            "toolchain": dict(toolchain),
            "task_public_source_files": dict(public_dependency_hashes),
            "task_dependency_snapshot_sha256": sha256_id(
                dict(extracted.task.dependency_hashes)
            ),
            "closure": dict(closure),
        },
    }


def validate_candidate_manifest(
    manifest: Mapping[str, Any],
    *,
    pack_root: Path,
    lean_root: Path,
) -> None:
    """Revalidate a shadow candidate and all current dependency hashes."""

    h_j_evidence = manifest.get("h_j_evidence")
    _expect(
        manifest.get("schema_version") == PUBLICATION_CANDIDATE_MANIFEST_SCHEMA
        and manifest.get("state") == PUBLICATION_STATE
        and isinstance(h_j_evidence, Mapping)
        and isinstance(manifest.get("publication_eligible"), bool)
        and manifest.get("publication_eligible")
        is (
            h_j_evidence.get("formal_h_j_complete") is True
            and h_j_evidence.get("mode") == "main_h_j_full_report"
        )
        and manifest.get("publication_activation_performed") is False,
        "publication_manifest_invalid",
        "candidate manifest is not the non-activating H-K shadow schema",
    )
    _expect(
        manifest.get("case_id") in SUPPORTED_PUBLICATION_CASES,
        "publication_case_unsupported",
        "candidate manifest case is unsupported",
    )
    candidate = manifest.get("candidate")
    dependencies = manifest.get("dependencies")
    audits = manifest.get("shadow_audits")
    _expect(
        isinstance(candidate, Mapping)
        and isinstance(dependencies, Mapping)
        and isinstance(audits, Mapping),
        "publication_manifest_invalid",
        "candidate/dependency/audit sections are absent",
    )
    source_file = candidate.get("source_file")
    _expect(
        source_file == "Reduction.lean",
        "publication_manifest_path_forbidden",
        "candidate source path is not pack-relative",
    )
    source_path = pack_root / str(source_file)
    _expect(
        source_path.is_file(),
        "publication_candidate_missing",
        "candidate Reduction.lean is missing",
    )
    source = source_path.read_text(encoding="utf-8")
    _assert_candidate_source_safe(source)
    _expect(
        candidate.get("source_sha256") == _text_sha256(source),
        "publication_candidate_hash_mismatch",
        "candidate source hash drifted",
    )
    _expect(
        list(IMPORT_RE.findall(source)) == candidate.get("imports"),
        "publication_candidate_import_invalid",
        "candidate imports differ from its manifest",
    )
    _expect(
        candidate.get("attributes")
        == [TYPED_EDGE_ATTRIBUTE, FINAL_COMPOSITION_ATTRIBUTE],
        "publication_candidate_attribute_missing",
        "candidate manifest lacks exact final-reduction attributes",
    )
    toolchain = dependencies.get("toolchain")
    _expect(
        toolchain == _toolchain_evidence(lean_root),
        "publication_dependency_stale",
        "toolchain or Lake lock files drifted",
    )
    public_files = dependencies.get("task_public_source_files")
    closure = dependencies.get("closure")
    _expect(
        isinstance(public_files, Mapping) and isinstance(closure, Mapping),
        "publication_manifest_invalid",
        "dependency source maps are absent",
    )
    for relative, expected_hash in public_files.items():
        path = lean_root.parent / str(relative)
        _expect(
            path.is_file() and _file_sha256(path) == expected_hash,
            "publication_dependency_stale",
            f"task dependency {relative} drifted",
        )
    project_files = closure.get("project_source_files")
    _expect(
        isinstance(project_files, Mapping)
        and closure.get("project_source_file_count") == len(project_files),
        "publication_manifest_invalid",
        "dependency closure is malformed",
    )
    for relative, expected_hash in project_files.items():
        path = lean_root.parent / str(relative)
        _expect(
            path.is_file() and _file_sha256(path) == expected_hash,
            "publication_dependency_stale",
            f"closure dependency {relative} drifted",
        )
    _expect(
        closure.get("closure_sha256") == sha256_id(dict(sorted(project_files.items())))
        and closure.get("candidate_cycle_absent") is True
        and closure.get("runtime_or_hardness_aggregate_import_absent") is True,
        "publication_dependency_stale",
        "dependency closure hash or import-cycle guard drifted",
    )
    _expect(
        isinstance(audits.get("clean_shadow_build"), Mapping)
        and audits["clean_shadow_build"].get("passed") is True
        and audits.get("axiom_endpoint_attribute") is not None
        and audits["axiom_endpoint_attribute"].get("passed") is True
        and audits.get("import_cycle", {}).get("passed") is True,
        "publication_shadow_audit_failed",
        "one or more clean-shadow audits did not pass",
    )
    _assert_portable_manifest(manifest)
    _expect(
        manifest.get("candidate_content_id")
        == sha256_id(_candidate_content_payload(manifest)),
        "publication_candidate_content_id_mismatch",
        "candidate content ID drifted",
    )
    _expect(
        manifest.get("manifest_id") == _content_hash(manifest, field="manifest_id"),
        "publication_manifest_hash_mismatch",
        "candidate manifest ID drifted",
    )


def review_publication_candidates(
    *,
    evidence: HJPublicationEvidence,
    case_ids: Sequence[str],
    output_root: Path,
    repo_root: Path,
    lean_root: Path,
    timeout_seconds: int = 900,
) -> dict[str, Any]:
    """Render, clean-build, and audit H-K candidates without publishing them."""

    requested = list(case_ids)
    _expect(
        requested and len(set(requested)) == len(requested),
        "publication_case_invalid",
        "candidate case list is empty or duplicated",
    )
    _expect(
        all(case_id in SUPPORTED_PUBLICATION_CASES for case_id in requested),
        "publication_case_unsupported",
        "candidate case list includes an unsupported target",
    )
    output_root = output_root.resolve()
    _expect(
        not output_root.exists(),
        "publication_output_not_empty",
        "publication review output already exists; choose a fresh path",
    )
    output_root.mkdir(parents=True)
    shadow_lean = _prepare_shadow_workspace(lean_root.resolve(), output_root / "shadow")

    prepared: list[dict[str, Any]] = []
    modules: list[str] = []
    for case_id in requested:
        extracted = extract_h_j_publication_case(
            evidence, case_id, repo_root=repo_root.resolve()
        )
        source, rendered = _render_candidate_source(extracted)
        public_hashes = _validate_task_dependency_snapshot(
            extracted.task,
            repo_root=repo_root.resolve(),
            lean_root=lean_root.resolve(),
        )
        closure = _project_dependency_closure(
            lean_root.resolve(),
            rendered["imports"],
            candidate_module=rendered["module"],
        )
        toolchain = _toolchain_evidence(lean_root.resolve())
        manifest = _build_manifest_skeleton(
            evidence=evidence,
            extracted=extracted,
            source=source,
            rendered=rendered,
            public_dependency_hashes=public_hashes,
            closure=closure,
            toolchain=toolchain,
        )
        segment = rendered["module"].split(".")[-2]
        pack_root = output_root / "candidates" / case_id / segment
        pack_root.mkdir(parents=True)
        (pack_root / "Reduction.lean").write_text(source, encoding="utf-8")
        shadow_source = (
            shadow_lean
            / "Reference"
            / Path(*rendered["module"].split(".")).with_suffix(".lean")
        )
        shadow_source.parent.mkdir(parents=True, exist_ok=True)
        shadow_source.write_text(source, encoding="utf-8")
        modules.append(str(rendered["module"]))
        prepared.append(
            {
                "case_id": case_id,
                "pack_root": pack_root,
                "manifest": manifest,
                "shadow_source": shadow_source,
            }
        )

    build_command = _run_command(
        ["lake", "build", *modules],
        cwd=shadow_lean,
        timeout_seconds=timeout_seconds,
    )
    if build_command["exit_code"] != 0 or build_command["timed_out"] is True:
        _fail(
            "publication_shadow_build_failed",
            "clean shadow candidate build failed; stdout/stderr hashes are "
            f"{build_command['stdout_sha256']}/{build_command['stderr_sha256']}",
        )

    rows: list[dict[str, Any]] = []
    for entry in prepared:
        manifest = entry["manifest"]
        module = manifest["candidate"]["module"]
        segment = module.split(".")[-2]
        audit_relative = Path("PublicationAudits") / f"{segment}.lean"
        audit_path = shadow_lean / audit_relative
        audit_path.parent.mkdir(parents=True, exist_ok=True)
        audit_source = _audit_source(manifest)
        audit_path.write_text(audit_source, encoding="utf-8")
        audit_command = _run_command(
            ["lake", "env", "lean", audit_relative.as_posix()],
            cwd=shadow_lean,
            timeout_seconds=timeout_seconds,
        )
        if audit_command["exit_code"] != 0 or audit_command["timed_out"] is True:
            _fail(
                "publication_shadow_audit_failed",
                f"{entry['case_id']} axiom/endpoint/attribute audit failed; "
                f"stdout/stderr hashes are {audit_command['stdout_sha256']}/"
                f"{audit_command['stderr_sha256']}",
            )
        manifest["shadow_audits"] = {
            "clean_shadow_build": {
                "passed": True,
                "old_project_olean_absent_before_build": True,
                "old_project_build_cache_absent_before_build": True,
                "declared_package_cache_reused": True,
                **_manifest_without_command_output(build_command),
            },
            "axiom_endpoint_attribute": {
                "passed": True,
                "audit_source_sha256": _text_sha256(audit_source),
                **_manifest_without_command_output(audit_command),
            },
            "import_cycle": {
                "passed": True,
                "candidate_cycle_absent": True,
                "runtime_or_hardness_aggregate_import_absent": True,
                "graph_sha256": manifest["dependencies"]["closure"][
                    "graph_sha256"
                ],
            },
        }
        sealed = reseal_candidate_manifest(manifest)
        manifest_path = entry["pack_root"] / "manifest.json"
        _write_json(manifest_path, sealed)
        validate_candidate_manifest(
            sealed,
            pack_root=entry["pack_root"],
            lean_root=lean_root.resolve(),
        )
        rows.append(
            {
                "case_id": entry["case_id"],
                "label": sealed["label"],
                "canonical_endpoint": sealed["canonical_endpoint"],
                "source_hub": sealed["source_hub"],
                "candidate_module": sealed["candidate"]["module"],
                "candidate_declaration": sealed["candidate"]["declaration"],
                "candidate_content_id": sealed["candidate_content_id"],
                "manifest_id": sealed["manifest_id"],
                "manifest_sha256": _file_sha256(manifest_path),
                "model_node_count": len(sealed["route"]["model_nodes"]),
                "model_call_count": sealed["model_evidence"]["call_count"],
                "clean_shadow_build_passed": True,
                "axiom_endpoint_attribute_audit_passed": True,
                "import_cycle_audit_passed": True,
                "publication_eligible": sealed["publication_eligible"],
                "publication_activation_performed": False,
            }
        )

    report: dict[str, Any] = {
        "schema_version": PUBLICATION_REVIEW_REPORT_SCHEMA,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "state": PUBLICATION_STATE,
        "passed": True,
        "evidence_mode": evidence.evidence_mode,
        "formal_h_j_complete": evidence.formal_h_j_complete,
        "publication_eligible": evidence.formal_h_j_complete,
        "publication_activation_performed": False,
        "public_generated_tree_modified": False,
        "candidate_count": len(rows),
        "supported_interface": list(SUPPORTED_PUBLICATION_CASES),
        "cases": rows,
        "gates": {
            "all_candidates_reduction_only": True,
            "all_model_nodes_preserved": True,
            "all_runner_certified_reductions_preserved": True,
            "all_native_hardness_tails_removed": True,
            "all_manifests_content_addressed": True,
            "all_dependency_hashes_bound": True,
            "all_clean_shadow_builds_passed": True,
            "all_axiom_endpoint_attribute_audits_passed": True,
            "all_import_cycle_audits_passed": True,
            "no_public_registry_activation": True,
            "no_public_generated_tree_write": True,
        },
    }
    report["review_id"] = sha256_id(report)
    _write_json(output_root / "review-report.json", report)
    return report


__all__ = [
    "CAPABILITY_RUN_SCHEMA",
    "CAPABILITY_SCORE_SCHEMA",
    "FINAL_COMPOSITION_ATTRIBUTE",
    "HJPublicationEvidence",
    "H_J_FINAL_STAGE",
    "H_J_FULL_REPORT_SCHEMA",
    "NPHardPublicationError",
    "PUBLICATION_CANDIDATE_MANIFEST_SCHEMA",
    "PUBLICATION_REVIEW_REPORT_SCHEMA",
    "PUBLICATION_STATE",
    "SUPPORTED_PUBLICATION_CASES",
    "TYPED_EDGE_ATTRIBUTE",
    "extract_h_j_publication_case",
    "load_h_j_publication_evidence",
    "reseal_candidate_manifest",
    "review_publication_candidates",
    "validate_candidate_manifest",
]
