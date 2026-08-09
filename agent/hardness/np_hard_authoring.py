"""Fenced model authoring for one exact forward NP-hardness reduction gap.

The model may replace only the term body of a runner-owned declaration whose
type is ``CertifiedReduction hardnessHub request.problem``.  Candidate Lean,
fresh resolver reconstruction, the axiom gate, and release replay remain the
authorities; model output is never interpreted as evidence by Python.
"""

from __future__ import annotations

import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Mapping, Protocol

from .lean_runner import (
    RUNTIME_MODULE,
    assert_generated_source_is_safe,
    module_file,
    run_command,
    sha256_file,
    validate_declaration_name,
    validate_module_name,
)
from .lean_worker_pool import (
    StagePLeanWorkerKey,
    StagePLeanWorkerPool,
    StagePLeanWorkerResult,
)
from .model_client import ModelResponse, extract_json_object
from .models import CommandResult, sha256_id
from .stage_p_contract import BANNED_BODY_RE
from .stage_p_model_authoring import StagePCandidateSource


NP_HARD_AUTHORING_TASK_SCHEMA_V1 = "hardness_np_hard_authoring_task_v1"
NP_HARD_AUTHORING_PATCH_SCHEMA_V1 = "hardness_np_hard_authoring_patch_v1"
NP_HARD_AUTHORING_TRACE_SCHEMA_V1 = "hardness_np_hard_authoring_trace_v1"
NP_HARD_AUTHORING_PUBLICATION_SCHEMA_V1 = (
    "hardness_np_hard_authoring_publication_v1"
)
NP_HARD_AUTHORING_DIRECTION = "hardness_seed_to_problem"
NP_HARD_AUTHORING_MAX_BODY_CHARS = 12_000

NP_HARD_AUTHORING_TASK_SCHEMA_V2 = "hardness_np_hard_authoring_task_v2"
NP_HARD_AUTHORING_PATCH_SCHEMA_V2 = "hardness_np_hard_authoring_patch_v2"
NP_HARD_AUTHORING_RESULT_SCHEMA_V2 = "hardness_np_hard_authoring_result_v2"
NP_HARD_AUTHORING_REQUIRED_DIRECTION_V2 = "source_to_target"
NP_HARD_AUTHORING_TASK_CLASSES_V2 = frozenset(
    {"semantic_proof", "program_composition", "program_synthesis"}
)
NP_HARD_AUTHORING_OUTCOMES_V2 = frozenset(
    {"accepted", "rejected", "budget_exhausted", "infra_error"}
)

_NP_HARD_V2_HASH_RE = re.compile(r"sha256:[0-9a-f]{64}\Z")
_NP_HARD_V2_NODE_RE = re.compile(r"[a-z][a-z0-9-]*\Z")
_NP_HARD_V2_FORBIDDEN_MARKERS = (
    ".Oracles.",
    ".Gold.",
    ".GoldProofs.",
    ".HiddenTargets.",
    "GoldProof",
    "HiddenTargets",
)

NP_HARD_AUTHORING_SYSTEM_PROMPT = """\
You are an untrusted Lean 4 term author. Return exactly one JSON object with
only `candidate_declaration` and `replacement_body`, and no markdown. The
orchestrator has frozen the request, source hardness hub, target
problem, direction, declaration, imports, and exact CertifiedReduction type.
You may submit only the Lean term body that fills the declaration after `:=`.
This is a small local construction: keep internal reasoning minimal and emit
the JSON answer immediately. On the first candidate, you MUST try the simplest
kernel-checkable correctness proof, `by intro input; rfl`, whenever the supplied
program run and target acceptance are definitionally equal; do not introduce
`unfold`, `simp`, or a manual iff proof before Lean has rejected that `rfl`
candidate. On a repair turn, never repeat the current rejected body. A target
semantic definition cannot be unfolded inside a source-side hypothesis. Prefer
a fully-qualified public PolyProg already supplied by the input module over
rebuilding that executable.
Do not emit imports, namespaces, declarations, commands, markdown, sorry,
admit, axioms, unsafe code, filesystem operations, or a reduction in the
opposite direction. Use the public input source and Lean diagnostics only.
The Lean compiler, exact resolver, axiom audit, and independent replay decide
whether the candidate is accepted; your response has no proof authority.
"""


class NPHardModelClient(Protocol):
    def complete_json(self, *, system: str, prompt: str) -> ModelResponse: ...


@dataclass(frozen=True)
class NPHardAuthoringTaskV1:
    request_id: str
    registry_fingerprint: str
    input_module: str
    input_problem_declaration: str
    hub_declaration: str
    seed_evidence_declaration: str
    seed_evidence_kind: str
    candidate_module: str
    candidate_declaration: str
    exact_type: str
    input_source_sha256: str
    max_attempts: int
    direction: str = NP_HARD_AUTHORING_DIRECTION
    schema_version: str = NP_HARD_AUTHORING_TASK_SCHEMA_V1

    def validate(self) -> None:
        if self.schema_version != NP_HARD_AUTHORING_TASK_SCHEMA_V1:
            raise ValueError("unsupported NP-hard authoring task schema")
        validate_module_name(self.input_module)
        validate_module_name(self.candidate_module)
        for label, declaration in {
            "input problem": self.input_problem_declaration,
            "hardness hub": self.hub_declaration,
            "seed evidence": self.seed_evidence_declaration,
            "candidate": self.candidate_declaration,
        }.items():
            validate_declaration_name(declaration, label=label)
        if self.direction != NP_HARD_AUTHORING_DIRECTION:
            raise ValueError("NP-hard authoring task changed the frozen direction")
        if not self.request_id.startswith("lean:"):
            raise ValueError("NP-hard authoring task has an invalid request ID")
        if not self.registry_fingerprint.startswith("lean:"):
            raise ValueError("NP-hard authoring task has an invalid registry fingerprint")
        if not self.exact_type.strip():
            raise ValueError("NP-hard authoring task has an empty exact type")
        if not 1 <= self.max_attempts <= 4:
            raise ValueError("NP-hard authoring attempts must be between one and four")

    @property
    def gap_id(self) -> str:
        self.validate()
        return sha256_id({"schema_version": self.schema_version, **asdict(self)})

    def to_dict(self) -> dict[str, Any]:
        return {**asdict(self), "gap_id": self.gap_id}


@dataclass(frozen=True)
class NPHardAuthoredCandidateV1:
    task: NPHardAuthoringTaskV1
    source: str
    source_sha256: str
    body_sha256: str
    model_response_sha256: str
    attempt: int
    model_calls: int
    commands: tuple[CommandResult, ...]
    worker_results: tuple[StagePLeanWorkerResult, ...]
    call_records: tuple[dict[str, Any], ...]


@dataclass(frozen=True)
class NPHardAuthoringFailureV1:
    code: str
    explanation: str
    model_calls: int
    commands: tuple[CommandResult, ...]
    worker_results: tuple[StagePLeanWorkerResult, ...]
    call_records: tuple[dict[str, Any], ...]


def _tagged_content_hash(value: str) -> str:
    """Normalize raw SHA-256 values for the strict worker-key contract."""

    if value.startswith("sha256:") and len(value) == 71:
        return value
    if len(value) == 64 and all(character in "0123456789abcdef" for character in value):
        return f"sha256:{value}"
    return sha256_id(value)


def _worker_diagnostic(result: StagePLeanWorkerResult) -> str:
    messages: list[str] = []
    for item in result.diagnostics:
        message = str(item.get("message", "Lean rejected candidate")).strip()
        if message:
            messages.append(message)
    return "\n".join(messages[:12])[:4_000] or "Lean rejected candidate"


def build_np_hard_authoring_task(
    *,
    request_id: str,
    registry_fingerprint: str,
    input_module: str,
    input_problem_declaration: str,
    hub_declaration: str,
    seed_evidence_declaration: str,
    seed_evidence_kind: str,
    input_source_sha256: str,
    job_id: str,
    max_attempts: int,
) -> NPHardAuthoringTaskV1:
    segment = job_id.removeprefix("sha256:")[:16]
    candidate_module = f"Generated.NPHard.C{segment}.AuthoredForward"
    candidate_declaration = f"{candidate_module}.authoredForwardReduction"
    exact_type = (
        "ComplexityReduction.Certificate.CertifiedReduction "
        f"{hub_declaration} {input_problem_declaration}"
    )
    task = NPHardAuthoringTaskV1(
        request_id=request_id,
        registry_fingerprint=registry_fingerprint,
        input_module=input_module,
        input_problem_declaration=input_problem_declaration,
        hub_declaration=hub_declaration,
        seed_evidence_declaration=seed_evidence_declaration,
        seed_evidence_kind=seed_evidence_kind,
        candidate_module=candidate_module,
        candidate_declaration=candidate_declaration,
        exact_type=exact_type,
        input_source_sha256=input_source_sha256,
        max_attempts=max_attempts,
    )
    task.validate()
    return task


def build_np_hard_candidate(
    task: NPHardAuthoringTaskV1, *, body: str = "by\n  contradiction\n"
) -> StagePCandidateSource:
    task.validate()
    candidate = StagePCandidateSource(
        fixed_header=(
            f"import {task.input_module}\n"
            f"import {RUNTIME_MODULE}\n\n"
            f"namespace {task.candidate_module}\n\n"
            "open ComplexityReduction\n"
            "open ComplexityReduction.Certificate\n\n"
            "@[complexity_reduction_ir_typed_edge, "
            "complexity_reduction_ir_component_shared_gadget]\n"
            "noncomputable def authoredForwardReduction :\n"
            f"    {task.exact_type} :=\n"
        ),
        editable_body=body if body.endswith("\n") else body + "\n",
        fixed_footer=(
            f"\nend {task.candidate_module}\n\n"
            f"assert_standard_axioms {task.candidate_declaration}\n"
        ),
        allowed_imports=(task.input_module, RUNTIME_MODULE),
    )
    candidate.validate()
    return candidate


def _response_record(response: ModelResponse, *, attempt: int) -> dict[str, Any]:
    return {
        "attempt": attempt,
        "called": response.called,
        "ok": response.ok,
        "status_code": response.status_code,
        "duration_seconds": response.duration_seconds,
        "usage": response.usage,
        "attempts": response.attempts,
        "finish_reason": response.finish_reason,
        "response_sha256": sha256_id(response.content),
        "response_content": response.content[:20_000],
        "error": response.error,
    }


def _prompt(
    *,
    task: NPHardAuthoringTaskV1,
    input_source: str,
    current_body: str,
    diagnostic: str | None,
) -> str:
    payload: dict[str, Any] = {
        "schema_version": NP_HARD_AUTHORING_TASK_SCHEMA_V1,
        "request_id": task.request_id,
        "gap_id": task.gap_id,
        "registry_fingerprint": task.registry_fingerprint,
        "objective": "prove_np_hard",
        "direction": task.direction,
        "source_hardness_hub": task.hub_declaration,
        "target_problem": task.input_problem_declaration,
        "seed_evidence": task.seed_evidence_declaration,
        "seed_evidence_kind": task.seed_evidence_kind,
        "candidate_declaration": task.candidate_declaration,
        "declaration_signature": task.exact_type,
        "public_type_summary": (
            "CertifiedReduction is a structure with exactly two fields: "
            "program : PolyProg source.representation target.representation; "
            "correct : forall input, source.accepts input iff "
            "target.accepts (program.run input). Construct it with a structure "
            "literal with program and correct on separate lines; indent every "
            "tactic under `correct := by` farther than the correct field. Do not unfold "
            "the structure type. Private declarations in the input source cannot "
            "be named from the candidate module."
        ),
        "current_editable_body": current_body,
        "validation_strategy": {
            "initial_candidate": (
                "Use the public program and set correct := by; intro input; rfl. "
                "Do not use unfold/simp/manual constructor unless Lean first rejects rfl."
            ),
            "repair_candidate": (
                "The replacement_body must differ from current_editable_body. "
                "Never unfold a target-only semantic definition inside a source-side hypothesis."
            ),
            "compiler_inserted_math_tokens": 0,
        },
        "public_input_source": input_source[:20_000],
        "lean_diagnostic": diagnostic[:4_000] if diagnostic else None,
        "response_template": {
            "candidate_declaration": task.candidate_declaration,
            "replacement_body": "Lean term body only",
        },
    }
    return json.dumps(payload, ensure_ascii=True, indent=2, sort_keys=True)


def parse_np_hard_authoring_body(
    *, content: str, task: NPHardAuthoringTaskV1
) -> str:
    task.validate()
    payload = extract_json_object(content)
    if not isinstance(payload, dict):
        raise ValueError("model did not return one JSON object")
    expected = {
        "schema_version": NP_HARD_AUTHORING_PATCH_SCHEMA_V1,
        "action": "submit_patch",
        "request_id": task.request_id,
        "gap_id": task.gap_id,
        "direction": task.direction,
        "source_declaration": task.hub_declaration,
        "target_declaration": task.input_problem_declaration,
        "candidate_declaration": task.candidate_declaration,
        "declaration_signature": task.exact_type,
    }
    allowed_keys = {*expected, "replacement_body"}
    if not set(payload).issubset(allowed_keys) or not {
        "candidate_declaration",
        "replacement_body",
    }.issubset(payload):
        raise ValueError("model response changed the closed NP-hard patch schema")
    for key, value in expected.items():
        if key in payload and payload[key] != value:
            raise ValueError(f"model response mutated frozen field: {key}")
    body = payload.get("replacement_body")
    if not isinstance(body, str) or not body.strip():
        raise ValueError("model response has an empty Lean term body")
    if len(body) > NP_HARD_AUTHORING_MAX_BODY_CHARS:
        raise ValueError("model response exceeded the Lean body size fence")
    if BANNED_BODY_RE.search(body):
        raise ValueError("model response contains a forbidden Lean command or trust token")
    assert_generated_source_is_safe(body)
    return body if body.endswith("\n") else body + "\n"


def _authoring_error_code(error: ValueError) -> str:
    message = str(error)
    if "direction" in message:
        return "candidate_wrong_direction"
    if any(
        field in message
        for field in (
            "source_declaration",
            "target_declaration",
            "candidate_declaration",
            "declaration_signature",
        )
    ):
        return "candidate_wrong_endpoint"
    if "forbidden Lean command or trust token" in message:
        return "candidate_nonstandard_axiom"
    return "authoring_budget_exhausted"


def author_exact_np_hard_reduction(
    *,
    task: NPHardAuthoringTaskV1,
    input_source: str,
    model: NPHardModelClient | None,
    lean_root: Path,
    candidate_path: Path,
    timeout_seconds: int,
    worker_pool: StagePLeanWorkerPool | None = None,
    worker_session_id: str | None = None,
    worker_owner: str | None = None,
    toolchain: str | None = None,
    lake_manifest_sha256: str | None = None,
) -> NPHardAuthoredCandidateV1 | NPHardAuthoringFailureV1:
    """Run bounded model/Lean repair for one immutable forward reduction."""

    task.validate()
    if model is None:
        return NPHardAuthoringFailureV1(
            code="model_provider_unavailable",
            explanation="prove_np_hard authoring requires a configured model client",
            model_calls=0,
            commands=(),
            worker_results=(),
            call_records=(),
        )
    worker_arguments = (
        worker_session_id,
        worker_owner,
        toolchain,
        lake_manifest_sha256,
    )
    if worker_pool is not None and any(value is None for value in worker_arguments):
        raise ValueError("persistent NP-hard candidate validation is missing worker metadata")
    if worker_pool is None and any(value is not None for value in worker_arguments):
        raise ValueError("NP-hard worker metadata was supplied without a worker pool")
    candidate = build_np_hard_candidate(task)
    diagnostic: str | None = None
    seen_bodies: set[str] = set()
    seen_diagnostics: set[str] = set()
    last_lean_diagnostic: str | None = None
    commands: list[CommandResult] = []
    worker_results: list[StagePLeanWorkerResult] = []
    calls: list[dict[str, Any]] = []
    model_calls = 0
    last_error = "authoring attempts were exhausted"
    last_failure_code = "authoring_budget_exhausted"
    for attempt in range(1, task.max_attempts + 1):
        response = model.complete_json(
            system=NP_HARD_AUTHORING_SYSTEM_PROMPT,
            prompt=_prompt(
                task=task,
                input_source=input_source,
                current_body=candidate.editable_body,
                diagnostic=diagnostic,
            ),
        )
        calls.append(_response_record(response, attempt=attempt))
        model_calls += int(response.called)
        if not response.called:
            return NPHardAuthoringFailureV1(
                code="model_provider_unavailable",
                explanation=response.error or "the configured model was not called",
                model_calls=model_calls,
                commands=tuple(commands),
                worker_results=tuple(worker_results),
                call_records=tuple(calls),
            )
        if not response.ok:
            return NPHardAuthoringFailureV1(
                code="model_provider_unavailable",
                explanation=response.error or "model request failed",
                model_calls=model_calls,
                commands=tuple(commands),
                worker_results=tuple(worker_results),
                call_records=tuple(calls),
            )
        try:
            body = parse_np_hard_authoring_body(content=response.content, task=task)
            body_hash = sha256_id(body)
            if body_hash in seen_bodies:
                raise ValueError("model repeated an authored Lean body")
            seen_bodies.add(body_hash)
            candidate = candidate.replace_body(body)
        except ValueError as error:
            last_error = str(error)
            last_failure_code = _authoring_error_code(error)
            diagnostic = (
                f"Patch protocol error: {last_error}\n"
                + (
                    f"Last Lean diagnostic (still authoritative):\n{last_lean_diagnostic}"
                    if last_lean_diagnostic
                    else ""
                )
            )
            continue
        candidate_path.parent.mkdir(parents=True, exist_ok=True)
        temporary = candidate_path.with_suffix(candidate_path.suffix + ".tmp")
        temporary.write_text(candidate.source, encoding="utf-8")
        temporary.replace(candidate_path)
        if worker_pool is None:
            compile_result = run_command(
                ["lake", "env", "lean", str(candidate_path)],
                cwd=lean_root,
                timeout_seconds=timeout_seconds,
            )
            commands.append(compile_result)
            candidate_verified = compile_result.ok
            candidate_diagnostic = (
                compile_result.stderr or compile_result.stdout or "Lean rejected candidate"
            )[:4_000]
        else:
            assert worker_session_id is not None
            assert worker_owner is not None
            assert toolchain is not None
            assert lake_manifest_sha256 is not None
            dependency_hash = sha256_id(
                {
                    "input_source_sha256": task.input_source_sha256,
                    "registry_fingerprint": task.registry_fingerprint,
                    "exact_type": task.exact_type,
                }
            )
            worker_result = worker_pool.validate(
                session_id=worker_session_id,
                owner=worker_owner,
                key=StagePLeanWorkerKey(
                    toolchain=toolchain,
                    lake_manifest_sha256=_tagged_content_hash(lake_manifest_sha256),
                    base_registry_fingerprint=sha256_id(task.registry_fingerprint),
                    complete_source_sha256=candidate.source_sha256,
                    dependency_sha256=(dependency_hash,),
                    namespace=task.candidate_module,
                    session_id=worker_session_id,
                    editable_allowlist=("replacement_body",),
                ),
                source_path=candidate_path,
                dependency_sha256=(dependency_hash,),
                use_cache=False,
                allow_cold_fallback=False,
            )
            worker_results.append(worker_result)
            candidate_verified = worker_result.verified
            candidate_diagnostic = _worker_diagnostic(worker_result)
        if candidate_verified:
            return NPHardAuthoredCandidateV1(
                task=task,
                source=candidate.source,
                source_sha256=candidate.source_sha256,
                body_sha256=body_hash,
                model_response_sha256=sha256_id(response.content),
                attempt=attempt,
                model_calls=model_calls,
                commands=tuple(commands),
                worker_results=tuple(worker_results),
                call_records=tuple(calls),
            )
        diagnostic = candidate_diagnostic
        last_lean_diagnostic = diagnostic
        diagnostic_hash = sha256_id(diagnostic)
        if diagnostic_hash in seen_diagnostics:
            last_error = "Lean diagnostics repeated without authoring progress"
            break
        seen_diagnostics.add(diagnostic_hash)
        last_error = diagnostic
        last_failure_code = "authoring_budget_exhausted"
    return NPHardAuthoringFailureV1(
        code=(
            "semantic_proof_failed"
            if last_failure_code == "authoring_budget_exhausted"
            else last_failure_code
        ),
        explanation=last_error,
        model_calls=model_calls,
        commands=tuple(commands),
        worker_results=tuple(worker_results),
        call_records=tuple(calls),
    )


def publish_np_hard_candidate(
    *, root: Path, candidate: NPHardAuthoredCandidateV1
) -> tuple[Path, dict[str, Any]]:
    """Publish an immutable, content-addressed copy scoped to this job."""

    digest = candidate.source_sha256.removeprefix("sha256:")
    pack_root = root / "published" / digest
    source_path = (
        pack_root
        / "src"
        / Path(*candidate.task.candidate_module.split(".")).with_suffix(".lean")
    )
    manifest_path = pack_root / "manifest.json"
    if pack_root.exists():
        raise ValueError("NP-hard candidate publication already exists")
    source_path.parent.mkdir(parents=True, exist_ok=False)
    source_path.write_text(candidate.source, encoding="utf-8")
    manifest = {
        "schema_version": NP_HARD_AUTHORING_PUBLICATION_SCHEMA_V1,
        "task": candidate.task.to_dict(),
        "source_sha256": candidate.source_sha256,
        "body_sha256": candidate.body_sha256,
        "model_response_sha256": candidate.model_response_sha256,
        "model_calls": candidate.model_calls,
        "attempt": candidate.attempt,
        "provenance_kind": "model_generated",
        "direction": candidate.task.direction,
        "source_declaration": candidate.task.hub_declaration,
        "target_declaration": candidate.task.input_problem_declaration,
        "compiler_inserted_math_token_count": 0,
        "source_relative_path": str(source_path.relative_to(pack_root)),
    }
    manifest_path.write_text(
        json.dumps(manifest, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    source_path.chmod(0o444)
    manifest_path.chmod(0o444)
    return source_path, manifest


class NPHardAuthoringContractError(ValueError):
    """Stable, machine-readable rejection from the v2 NP-hard contract."""

    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


def _v2_fail(code: str, message: str) -> None:
    raise NPHardAuthoringContractError(code, message)


def _v2_require_hash(value: str, *, label: str) -> None:
    if not isinstance(value, str) or not _NP_HARD_V2_HASH_RE.fullmatch(value):
        _v2_fail("candidate_dependency_stale", f"{label} is not a tagged SHA-256")


def _v2_contains_quarantined_text(value: str) -> bool:
    lowered = value.lower()
    return any(marker.lower() in lowered for marker in _NP_HARD_V2_FORBIDDEN_MARKERS)


def _v2_require_public_text(value: str, *, label: str) -> None:
    if _v2_contains_quarantined_text(value):
        _v2_fail("oracle_or_gold_import", f"{label} references quarantined proof material")


def _v2_exact_keys(value: Mapping[str, Any], expected: set[str], *, label: str) -> None:
    actual = set(value)
    if actual != expected:
        missing = sorted(expected - actual)
        extra = sorted(actual - expected)
        _v2_fail(
            "invalid_np_hard_authoring_v2_schema",
            f"{label} keys drifted; missing={missing!r}, extra={extra!r}",
        )


@dataclass(frozen=True)
class NPHardAuthoringEndpointV2:
    module: str
    term: str

    def validate(self) -> None:
        try:
            validate_module_name(self.module)
            validate_declaration_name(self.term, label="NP-hard v2 endpoint")
        except ValueError as error:
            _v2_fail("candidate_wrong_endpoint", str(error))
        _v2_require_public_text(self.module, label="endpoint module")
        _v2_require_public_text(self.term, label="endpoint declaration")

    def to_dict(self) -> dict[str, str]:
        self.validate()
        return {"module": self.module, "term": self.term}

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "NPHardAuthoringEndpointV2":
        if not isinstance(value, Mapping):
            _v2_fail("candidate_wrong_endpoint", "endpoint must be an object")
        _v2_exact_keys(value, {"module", "term"}, label="endpoint")
        if not isinstance(value["module"], str) or not isinstance(value["term"], str):
            _v2_fail("candidate_wrong_endpoint", "endpoint fields must be strings")
        endpoint = cls(module=value["module"], term=value["term"])
        endpoint.validate()
        return endpoint


@dataclass(frozen=True)
class NPHardAuthoringObligationV2:
    node_id: str
    declaration: str
    capability: str
    exact_type: str
    depends_on: tuple[str, ...]

    def validate(self) -> None:
        if not _NP_HARD_V2_NODE_RE.fullmatch(self.node_id):
            _v2_fail("invalid_np_hard_authoring_v2_schema", "invalid gap node ID")
        try:
            validate_declaration_name(self.declaration, label="v2 editable declaration")
        except ValueError as error:
            _v2_fail("candidate_outside_edit_boundary", str(error))
        if self.capability not in {
            "reduction_executable",
            "poly_program",
            "program_run_coherence",
            "mapping_invariant",
            "semantic_proof",
        }:
            _v2_fail(
                "invalid_np_hard_authoring_v2_schema",
                f"unsupported v2 obligation capability: {self.capability}",
            )
        if not self.exact_type.strip() or len(self.exact_type) > 12_000:
            _v2_fail("candidate_exact_type_mismatch", "v2 obligation exact type is invalid")
        if len(set(self.depends_on)) != len(self.depends_on):
            _v2_fail("candidate_dependency_stale", "v2 obligation repeats a dependency")
        _v2_require_public_text(self.declaration, label="editable declaration")
        _v2_require_public_text(self.exact_type, label="obligation exact type")

    def to_dict(self) -> dict[str, Any]:
        self.validate()
        return {
            "node_id": self.node_id,
            "declaration": self.declaration,
            "capability": self.capability,
            "exact_type": self.exact_type,
            "depends_on": list(self.depends_on),
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "NPHardAuthoringObligationV2":
        if not isinstance(value, Mapping):
            _v2_fail("invalid_np_hard_authoring_v2_schema", "gap node must be an object")
        _v2_exact_keys(
            value,
            {"node_id", "declaration", "capability", "exact_type", "depends_on"},
            label="gap node",
        )
        dependencies = value["depends_on"]
        if not isinstance(dependencies, list) or not all(
            isinstance(dependency, str) for dependency in dependencies
        ):
            _v2_fail("candidate_dependency_stale", "gap dependencies must be strings")
        for key in ("node_id", "declaration", "capability", "exact_type"):
            if not isinstance(value[key], str):
                _v2_fail("invalid_np_hard_authoring_v2_schema", f"gap field {key} is invalid")
        obligation = cls(
            node_id=value["node_id"],
            declaration=value["declaration"],
            capability=value["capability"],
            exact_type=value["exact_type"],
            depends_on=tuple(dependencies),
        )
        obligation.validate()
        return obligation


@dataclass(frozen=True)
class NPHardAuthoringTaskV2:
    request_id: str
    task_class: str
    source_problem: NPHardAuthoringEndpointV2
    target_problem: NPHardAuthoringEndpointV2
    candidate_module: str
    final_candidate_declaration: str
    final_exact_type: str
    gap_nodes: tuple[NPHardAuthoringObligationV2, ...]
    editable_declarations: tuple[str, ...]
    allowed_imports: tuple[str, ...]
    allowed_primitives: tuple[str, ...]
    forbidden_axioms: tuple[str, ...]
    dependency_hashes: tuple[tuple[str, str], ...]
    public_source_files: tuple[str, ...]
    attempt_budget: int
    timeout_seconds: int
    max_output_tokens: int
    required_direction: str = NP_HARD_AUTHORING_REQUIRED_DIRECTION_V2
    schema_version: str = NP_HARD_AUTHORING_TASK_SCHEMA_V2

    @property
    def dependency_fingerprint(self) -> str:
        return sha256_id(dict(self.dependency_hashes))

    def _content_payload(self) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "task_class": self.task_class,
            "source_problem": {"module": self.source_problem.module, "term": self.source_problem.term},
            "target_problem": {"module": self.target_problem.module, "term": self.target_problem.term},
            "required_direction": self.required_direction,
            "candidate_module": self.candidate_module,
            "final_candidate_declaration": self.final_candidate_declaration,
            "final_exact_type": self.final_exact_type,
            "gap_nodes": [node.to_dict() for node in self.gap_nodes],
            "editable_declarations": list(self.editable_declarations),
            "allowed_imports": list(self.allowed_imports),
            "allowed_primitives": list(self.allowed_primitives),
            "forbidden_axioms": list(self.forbidden_axioms),
            "dependency_hashes": dict(self.dependency_hashes),
            "public_source_files": list(self.public_source_files),
            "attempt_budget": self.attempt_budget,
            "timeout_seconds": self.timeout_seconds,
            "max_output_tokens": self.max_output_tokens,
        }

    @property
    def computed_request_id(self) -> str:
        return sha256_id(self._content_payload())

    def validate(self) -> None:
        if self.schema_version != NP_HARD_AUTHORING_TASK_SCHEMA_V2:
            _v2_fail("invalid_np_hard_authoring_v2_schema", "unsupported v2 task schema")
        _v2_require_hash(self.request_id, label="request_id")
        if self.task_class not in NP_HARD_AUTHORING_TASK_CLASSES_V2:
            _v2_fail("invalid_np_hard_authoring_v2_schema", "unsupported v2 task class")
        self.source_problem.validate()
        self.target_problem.validate()
        if self.source_problem.term == self.target_problem.term:
            _v2_fail("candidate_wrong_endpoint", "v2 source and target endpoints are identical")
        if self.required_direction != NP_HARD_AUTHORING_REQUIRED_DIRECTION_V2:
            _v2_fail("candidate_wrong_direction", "v2 task changed source-to-target direction")
        try:
            validate_module_name(self.candidate_module)
            validate_declaration_name(
                self.final_candidate_declaration, label="v2 final candidate declaration"
            )
        except ValueError as error:
            _v2_fail("candidate_outside_edit_boundary", str(error))
        if not self.final_candidate_declaration.startswith(self.candidate_module + "."):
            _v2_fail(
                "candidate_outside_edit_boundary",
                "final declaration escaped the generated candidate module",
            )
        expected_final_type = (
            "ComplexityReduction.Certificate.CertifiedReduction "
            f"{self.source_problem.term} {self.target_problem.term}"
        )
        if self.final_exact_type != expected_final_type:
            _v2_fail("candidate_exact_type_mismatch", "v2 final CertifiedReduction type drifted")
        if not self.gap_nodes:
            _v2_fail("invalid_np_hard_authoring_v2_schema", "v2 task has no gap nodes")
        node_ids: set[str] = set()
        node_declarations: list[str] = []
        for node in self.gap_nodes:
            node.validate()
            if node.node_id in node_ids:
                _v2_fail("candidate_dependency_stale", "v2 task repeats a gap node")
            if any(dependency not in node_ids for dependency in node.depends_on):
                _v2_fail("candidate_dependency_stale", "v2 gap DAG is not topologically ordered")
            if not node.declaration.startswith(self.candidate_module + "."):
                _v2_fail(
                    "candidate_outside_edit_boundary",
                    "editable declaration escaped the generated candidate module",
                )
            node_ids.add(node.node_id)
            node_declarations.append(node.declaration)
        if tuple(node_declarations) != self.editable_declarations:
            _v2_fail(
                "candidate_outside_edit_boundary",
                "editable declaration allowlist differs from the exact gap declarations",
            )
        if len(set(self.allowed_imports)) != len(self.allowed_imports):
            _v2_fail("import_not_allowlisted", "v2 task repeats an allowed import")
        if self.target_problem.module not in self.allowed_imports:
            _v2_fail("import_not_allowlisted", "target input module is not allowlisted")
        for imported in self.allowed_imports:
            try:
                validate_module_name(imported)
            except ValueError as error:
                _v2_fail("import_not_allowlisted", str(error))
            _v2_require_public_text(imported, label="allowed import")
        if len(set(self.allowed_primitives)) != len(self.allowed_primitives):
            _v2_fail("fabricated_declaration_handle", "v2 primitive allowlist has duplicates")
        for primitive in self.allowed_primitives:
            try:
                validate_declaration_name(primitive, label="allowed primitive")
            except ValueError as error:
                _v2_fail("fabricated_declaration_handle", str(error))
            _v2_require_public_text(primitive, label="allowed primitive")
        if not self.forbidden_axioms or not {"sorryAx", "axiom", "unsafe"}.issubset(
            set(self.forbidden_axioms)
        ):
            _v2_fail("candidate_nonstandard_axiom", "v2 forbidden-axiom policy is incomplete")
        if len(set(self.forbidden_axioms)) != len(self.forbidden_axioms):
            _v2_fail("candidate_nonstandard_axiom", "v2 forbidden-axiom list has duplicates")
        if not self.dependency_hashes or len(dict(self.dependency_hashes)) != len(
            self.dependency_hashes
        ):
            _v2_fail("candidate_dependency_stale", "v2 dependency map is empty or duplicated")
        for name, digest in self.dependency_hashes:
            if not name:
                _v2_fail("candidate_dependency_stale", "v2 dependency name is empty")
            _v2_require_public_text(name, label="dependency name")
            _v2_require_hash(digest, label=f"dependency {name}")
        if not self.public_source_files or len(set(self.public_source_files)) != len(
            self.public_source_files
        ):
            _v2_fail("candidate_dependency_stale", "v2 public source list is empty or duplicated")
        for source in self.public_source_files:
            path = Path(source)
            if path.is_absolute() or ".." in path.parts:
                _v2_fail("candidate_dependency_stale", "v2 public source path is unsafe")
            _v2_require_public_text(source, label="public source path")
        if not 1 <= self.attempt_budget <= 4:
            _v2_fail("authoring_gap_budget_exhausted", "v2 attempt budget is outside 1..4")
        if not 1 <= self.timeout_seconds <= 600:
            _v2_fail("authoring_gap_budget_exhausted", "v2 timeout is outside 1..600 seconds")
        if not 1 <= self.max_output_tokens <= 16_000:
            _v2_fail("authoring_gap_budget_exhausted", "v2 output token budget is invalid")
        _v2_require_public_text(self.final_exact_type, label="final exact type")
        if self.request_id != self.computed_request_id:
            _v2_fail("candidate_dependency_stale", "v2 request ID does not bind its payload")

    def to_dict(self) -> dict[str, Any]:
        self.validate()
        return {"request_id": self.request_id, **self._content_payload()}

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "NPHardAuthoringTaskV2":
        if not isinstance(value, Mapping):
            _v2_fail("invalid_np_hard_authoring_v2_schema", "v2 task must be an object")
        expected = {
            "schema_version",
            "request_id",
            "task_class",
            "source_problem",
            "target_problem",
            "required_direction",
            "candidate_module",
            "final_candidate_declaration",
            "final_exact_type",
            "gap_nodes",
            "editable_declarations",
            "allowed_imports",
            "allowed_primitives",
            "forbidden_axioms",
            "dependency_hashes",
            "public_source_files",
            "attempt_budget",
            "timeout_seconds",
            "max_output_tokens",
        }
        _v2_exact_keys(value, expected, label="v2 task")
        if value["schema_version"] != NP_HARD_AUTHORING_TASK_SCHEMA_V2:
            _v2_fail("invalid_np_hard_authoring_v2_schema", "unsupported v2 task schema")
        gap_values = value["gap_nodes"]
        dependency_values = value["dependency_hashes"]
        sequence_fields = {
            "editable_declarations": value["editable_declarations"],
            "allowed_imports": value["allowed_imports"],
            "allowed_primitives": value["allowed_primitives"],
            "forbidden_axioms": value["forbidden_axioms"],
            "public_source_files": value["public_source_files"],
        }
        if not isinstance(gap_values, list) or not isinstance(dependency_values, Mapping):
            _v2_fail("invalid_np_hard_authoring_v2_schema", "v2 task collection fields are invalid")
        for label, items in sequence_fields.items():
            if not isinstance(items, list) or not all(isinstance(item, str) for item in items):
                _v2_fail("invalid_np_hard_authoring_v2_schema", f"v2 field {label} is invalid")
        string_fields = (
            "request_id",
            "task_class",
            "required_direction",
            "candidate_module",
            "final_candidate_declaration",
            "final_exact_type",
        )
        if not all(isinstance(value[field], str) for field in string_fields):
            _v2_fail("invalid_np_hard_authoring_v2_schema", "v2 task string field is invalid")
        if not all(isinstance(value[field], int) for field in (
            "attempt_budget", "timeout_seconds", "max_output_tokens"
        )):
            _v2_fail("invalid_np_hard_authoring_v2_schema", "v2 task budget field is invalid")
        if not all(isinstance(name, str) and isinstance(digest, str)
                   for name, digest in dependency_values.items()):
            _v2_fail("candidate_dependency_stale", "v2 dependency map is invalid")
        task = cls(
            request_id=value["request_id"],
            task_class=value["task_class"],
            source_problem=NPHardAuthoringEndpointV2.from_dict(value["source_problem"]),
            target_problem=NPHardAuthoringEndpointV2.from_dict(value["target_problem"]),
            candidate_module=value["candidate_module"],
            final_candidate_declaration=value["final_candidate_declaration"],
            final_exact_type=value["final_exact_type"],
            gap_nodes=tuple(
                NPHardAuthoringObligationV2.from_dict(item) for item in gap_values
            ),
            editable_declarations=tuple(sequence_fields["editable_declarations"]),
            allowed_imports=tuple(sequence_fields["allowed_imports"]),
            allowed_primitives=tuple(sequence_fields["allowed_primitives"]),
            forbidden_axioms=tuple(sequence_fields["forbidden_axioms"]),
            dependency_hashes=tuple(sorted(dependency_values.items())),
            public_source_files=tuple(sequence_fields["public_source_files"]),
            attempt_budget=value["attempt_budget"],
            timeout_seconds=value["timeout_seconds"],
            max_output_tokens=value["max_output_tokens"],
            required_direction=value["required_direction"],
            schema_version=value["schema_version"],
        )
        task.validate()
        return task


def _v2_obligations(
    *,
    task_class: str,
    candidate_module: str,
    source_term: str,
    target_term: str,
    program_reference: str | None,
    mapping_invariant: str | None,
    manifest_nodes: tuple[Mapping[str, Any], ...],
) -> tuple[NPHardAuthoringObligationV2, ...]:
    node_dependencies = {
        str(node["id"]): tuple(str(item) for item in node["depends_on"])
        for node in manifest_nodes
    }
    if task_class == "semantic_proof":
        if program_reference is None:
            _v2_fail("invalid_np_hard_authoring_v2_schema", "proof-only task lacks a public program")
        obligations: list[NPHardAuthoringObligationV2] = []
        if mapping_invariant is not None:
            obligations.append(
                NPHardAuthoringObligationV2(
                    node_id="mapping-invariant",
                    declaration=f"{candidate_module}.mappingInvariantProof",
                    capability="mapping_invariant",
                    exact_type=(
                        f"∀ input : {source_term}.Instance, {mapping_invariant} input "
                        f"({program_reference}.run input)"
                    ),
                    depends_on=node_dependencies.get("mapping-invariant", ()),
                )
            )
            semantic_id = "semantic-iff"
        else:
            semantic_id = "semantic-proof"
        obligations.append(
            NPHardAuthoringObligationV2(
                node_id=semantic_id,
                declaration=f"{candidate_module}.semanticCorrect",
                capability="semantic_proof",
                exact_type=(
                    f"∀ input : {source_term}.Instance, {source_term}.accepts input ↔ "
                    f"{target_term}.accepts ({program_reference}.run input)"
                ),
                depends_on=node_dependencies.get(semantic_id, ()),
            )
        )
    elif task_class == "program_composition":
        program = f"{candidate_module}.composedProgram"
        obligations = [
            NPHardAuthoringObligationV2(
                node_id="composed-program",
                declaration=program,
                capability="poly_program",
                exact_type=(
                    "ComplexityReduction.Program.PolyProg "
                    f"{source_term}.representation {target_term}.representation"
                ),
                depends_on=node_dependencies.get("composed-program", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="semantic-proof",
                declaration=f"{candidate_module}.semanticCorrect",
                capability="semantic_proof",
                exact_type=(
                    f"∀ input : {source_term}.Instance, {source_term}.accepts input ↔ "
                    f"{target_term}.accepts ({program}.run input)"
                ),
                depends_on=node_dependencies.get("semantic-proof", ()),
            ),
        ]
    elif task_class == "program_synthesis":
        executable = f"{candidate_module}.synthesizedExecutable"
        program = f"{candidate_module}.synthesizedProgram"
        if mapping_invariant is None:
            _v2_fail("invalid_np_hard_authoring_v2_schema", "synthesis task lacks its invariant")
        obligations = [
            NPHardAuthoringObligationV2(
                node_id="reduction-executable",
                declaration=executable,
                capability="reduction_executable",
                exact_type=f"{source_term}.Instance → {target_term}.Instance",
                depends_on=node_dependencies.get("reduction-executable", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="poly-program",
                declaration=program,
                capability="poly_program",
                exact_type=(
                    "ComplexityReduction.Program.PolyProg "
                    f"{source_term}.representation {target_term}.representation"
                ),
                depends_on=node_dependencies.get("poly-program", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="program-run-coherence",
                declaration=f"{candidate_module}.programRunCoherence",
                capability="program_run_coherence",
                exact_type=f"∀ input : {source_term}.Instance, {program}.run input = {executable} input",
                depends_on=node_dependencies.get("program-run-coherence", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="mapping-invariant",
                declaration=f"{candidate_module}.mappingInvariantProof",
                capability="mapping_invariant",
                exact_type=(
                    f"∀ input : {source_term}.Instance, {mapping_invariant} input "
                    f"({program}.run input)"
                ),
                depends_on=node_dependencies.get("mapping-invariant", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="semantic-iff",
                declaration=f"{candidate_module}.semanticCorrect",
                capability="semantic_proof",
                exact_type=(
                    f"∀ input : {source_term}.Instance, {source_term}.accepts input ↔ "
                    f"{target_term}.accepts ({program}.run input)"
                ),
                depends_on=node_dependencies.get("semantic-iff", ()),
            ),
        ]
    else:
        _v2_fail("invalid_np_hard_authoring_v2_schema", "unsupported v2 task class")
    expected_ids = tuple(str(node["id"]) for node in manifest_nodes)
    actual_ids = tuple(node.node_id for node in obligations)
    if actual_ids != expected_ids:
        _v2_fail(
            "candidate_dependency_stale",
            f"manifest gap nodes do not match v2 obligations: {expected_ids!r} != {actual_ids!r}",
        )
    return tuple(obligations)


def build_np_hard_authoring_task_v2(
    *,
    root: Path,
    input_module: str,
    input_problem_declaration: str,
    hub_module: str,
    hub_declaration: str,
    task_class: str,
    gap_nodes: tuple[Mapping[str, Any], ...],
    public_source_files: tuple[str, ...],
    allowed_primitives: tuple[str, ...],
    program_reference: str | None,
    mapping_invariant: str | None,
    additional_dependency_hashes: Mapping[str, str] | None = None,
    attempt_budget: int = 4,
    timeout_seconds: int = 60,
    max_output_tokens: int = 3_000,
) -> NPHardAuthoringTaskV2:
    root = root.resolve()
    source = NPHardAuthoringEndpointV2(module=hub_module, term=hub_declaration)
    target = NPHardAuthoringEndpointV2(
        module=input_module, term=input_problem_declaration
    )
    source.validate()
    target.validate()
    dependency_hashes: dict[str, str] = {}
    for relative_name in public_source_files:
        path = (root / relative_name).resolve()
        try:
            path.relative_to(root)
        except ValueError:
            _v2_fail("candidate_dependency_stale", "public source escaped the workspace")
        if not path.is_file():
            _v2_fail("candidate_dependency_stale", f"public source is missing: {relative_name}")
        _v2_require_public_text(relative_name, label="public source")
        source_text = path.read_text(encoding="utf-8")
        _v2_require_public_text(source_text, label=f"public source {relative_name}")
        dependency_hashes[f"public:{relative_name}"] = _tagged_content_hash(sha256_file(path))
    for imported in (input_module, hub_module, RUNTIME_MODULE):
        path = module_file(root / "Lean", imported)
        dependency_hashes[f"module:{imported}"] = _tagged_content_hash(sha256_file(path))
    for dependency_name, dependency_hash in sorted(
        (additional_dependency_hashes or {}).items()
    ):
        if dependency_name in dependency_hashes:
            _v2_fail(
                "candidate_dependency_stale",
                f"additional dependency shadows an existing binding: {dependency_name}",
            )
        _v2_require_public_text(dependency_name, label="additional dependency name")
        _v2_require_hash(dependency_hash, label=f"additional dependency {dependency_name}")
        dependency_hashes[dependency_name] = dependency_hash
    stable_seed = sha256_id(
        {
            "schema_version": NP_HARD_AUTHORING_TASK_SCHEMA_V2,
            "source": source.to_dict(),
            "target": target.to_dict(),
            "task_class": task_class,
            "gap_nodes": list(gap_nodes),
            "dependency_hashes": dependency_hashes,
        }
    ).removeprefix("sha256:")[:16]
    candidate_module = f"Generated.NPHardV2.C{stable_seed}.Authoring"
    obligations = _v2_obligations(
        task_class=task_class,
        candidate_module=candidate_module,
        source_term=hub_declaration,
        target_term=input_problem_declaration,
        program_reference=program_reference,
        mapping_invariant=mapping_invariant,
        manifest_nodes=gap_nodes,
    )
    final_declaration = f"{candidate_module}.authoredForwardReduction"
    task_arguments = {
        "task_class": task_class,
        "source_problem": source,
        "target_problem": target,
        "candidate_module": candidate_module,
        "final_candidate_declaration": final_declaration,
        "final_exact_type": (
            "ComplexityReduction.Certificate.CertifiedReduction "
            f"{hub_declaration} {input_problem_declaration}"
        ),
        "gap_nodes": obligations,
        "editable_declarations": tuple(node.declaration for node in obligations),
        "allowed_imports": tuple(dict.fromkeys((input_module, hub_module, RUNTIME_MODULE))),
        "allowed_primitives": tuple(allowed_primitives),
        "forbidden_axioms": ("sorryAx", "admit", "axiom", "unsafe"),
        "dependency_hashes": tuple(sorted(dependency_hashes.items())),
        "public_source_files": public_source_files,
        "attempt_budget": attempt_budget,
        "timeout_seconds": timeout_seconds,
        "max_output_tokens": max_output_tokens,
    }
    provisional = NPHardAuthoringTaskV2(
        request_id="sha256:" + "0" * 64, **task_arguments
    )
    task = NPHardAuthoringTaskV2(
        request_id=provisional.computed_request_id, **task_arguments
    )
    task.validate()
    return task


def build_np_hard_authoring_tasks_v2(
    *, root: Path, suite_path: Path
) -> tuple[NPHardAuthoringTaskV2, ...]:
    from .np_hard_generalization import load_np_hard_generalization_suite

    suite = load_np_hard_generalization_suite(suite_path, root=root)
    tasks: list[NPHardAuthoringTaskV2] = []
    for case in suite.cases:
        if case.kind != "model_authoring" or case.authoring is None:
            continue
        authoring = case.authoring
        tasks.append(
            build_np_hard_authoring_task_v2(
                root=root,
                input_module=case.module,
                input_problem_declaration=case.problem,
                hub_module=str(authoring["hub_module"]),
                hub_declaration=str(authoring["hub"]),
                task_class=str(authoring["task_class"]),
                gap_nodes=tuple(authoring["gap_nodes"]),
                public_source_files=case.public_source_files,
                allowed_primitives=tuple(authoring["allowed_primitives"]),
                program_reference=authoring.get("program_reference"),
                mapping_invariant=authoring.get("mapping_invariant"),
            )
        )
    return tuple(tasks)


def build_np_hard_authoring_prompt_v2(
    *, task: NPHardAuthoringTaskV2, root: Path
) -> str:
    task.validate()
    public_sources: dict[str, str] = {}
    for relative_name in task.public_source_files:
        source = (root / relative_name).read_text(encoding="utf-8")
        _v2_require_public_text(source, label=f"prompt source {relative_name}")
        public_sources[relative_name] = source[:20_000]
    payload = {
        "schema_version": NP_HARD_AUTHORING_TASK_SCHEMA_V2,
        "objective": "prove_np_hard",
        "task": task.to_dict(),
        "public_sources": public_sources,
        "policy": {
            "only_edit_exact_declarations": True,
            "compiler_inserted_math_tokens": 0,
            "lean_kernel_is_authority": True,
            "model_may_not_choose_endpoints_or_direction": True,
        },
        "response_template": {
            "schema_version": NP_HARD_AUTHORING_PATCH_SCHEMA_V2,
            "action": "submit_patch",
            "request_id": task.request_id,
            "task_class": task.task_class,
            "required_direction": task.required_direction,
            "source_problem": task.source_problem.to_dict(),
            "target_problem": task.target_problem.to_dict(),
            "dependency_fingerprint": task.dependency_fingerprint,
            "replacement_bodies": {
                declaration: "Lean term body only"
                for declaration in task.editable_declarations
            },
        },
    }
    serialized = json.dumps(payload, ensure_ascii=True, indent=2, sort_keys=True)
    _v2_require_public_text(serialized, label="v2 prompt")
    for forbidden_key in ('"case_id"', '"expected"', '"gold"', '"hidden_gold"'):
        if forbidden_key in serialized.lower():
            _v2_fail("oracle_or_gold_import", "v2 prompt contains benchmark-only metadata")
    return serialized


@dataclass(frozen=True)
class NPHardAuthoringPatchV2:
    request_id: str
    task_class: str
    required_direction: str
    source_problem: NPHardAuthoringEndpointV2
    target_problem: NPHardAuthoringEndpointV2
    dependency_fingerprint: str
    replacement_bodies: tuple[tuple[str, str], ...]
    action: str = "submit_patch"
    schema_version: str = NP_HARD_AUTHORING_PATCH_SCHEMA_V2

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "action": self.action,
            "request_id": self.request_id,
            "task_class": self.task_class,
            "required_direction": self.required_direction,
            "source_problem": self.source_problem.to_dict(),
            "target_problem": self.target_problem.to_dict(),
            "dependency_fingerprint": self.dependency_fingerprint,
            "replacement_bodies": dict(self.replacement_bodies),
        }


def parse_np_hard_authoring_patch_v2(
    *, content: str, task: NPHardAuthoringTaskV2
) -> NPHardAuthoringPatchV2:
    task.validate()
    try:
        value = extract_json_object(content)
    except ValueError as error:
        _v2_fail("invalid_np_hard_authoring_v2_schema", str(error))
    if not isinstance(value, Mapping):
        _v2_fail("invalid_np_hard_authoring_v2_schema", "v2 patch must be an object")
    expected_keys = {
        "schema_version",
        "action",
        "request_id",
        "task_class",
        "required_direction",
        "source_problem",
        "target_problem",
        "dependency_fingerprint",
        "replacement_bodies",
    }
    _v2_exact_keys(value, expected_keys, label="v2 patch")
    if value["schema_version"] != NP_HARD_AUTHORING_PATCH_SCHEMA_V2 or value["action"] != "submit_patch":
        _v2_fail("invalid_np_hard_authoring_v2_schema", "unsupported v2 patch envelope")
    if value["request_id"] != task.request_id or value["task_class"] != task.task_class:
        _v2_fail("candidate_dependency_stale", "v2 patch belongs to another task")
    if value["required_direction"] != task.required_direction:
        _v2_fail("candidate_wrong_direction", "v2 patch mutated the frozen direction")
    source = NPHardAuthoringEndpointV2.from_dict(value["source_problem"])
    target = NPHardAuthoringEndpointV2.from_dict(value["target_problem"])
    if source != task.source_problem or target != task.target_problem:
        _v2_fail("candidate_wrong_endpoint", "v2 patch mutated an exact endpoint")
    if value["dependency_fingerprint"] != task.dependency_fingerprint:
        _v2_fail("candidate_dependency_stale", "v2 patch uses stale dependencies")
    raw_bodies = value["replacement_bodies"]
    if not isinstance(raw_bodies, Mapping):
        _v2_fail("candidate_outside_edit_boundary", "v2 replacement bodies must be an object")
    if set(raw_bodies) != set(task.editable_declarations):
        _v2_fail(
            "candidate_outside_edit_boundary",
            "v2 patch omitted or added an editable declaration",
        )
    bodies: list[tuple[str, str]] = []
    for declaration in task.editable_declarations:
        body = raw_bodies[declaration]
        if not isinstance(body, str) or not body.strip():
            _v2_fail("candidate_outside_edit_boundary", "v2 replacement body is empty")
        if len(body) > NP_HARD_AUTHORING_MAX_BODY_CHARS:
            _v2_fail("candidate_outside_edit_boundary", "v2 replacement body is too large")
        match = BANNED_BODY_RE.search(body)
        if match:
            token = match.group(0).lower()
            if token in {"sorry", "admit", "axiom", "unsafe"}:
                code = "candidate_nonstandard_axiom"
            elif token == "import":
                code = "import_not_allowlisted"
            else:
                code = "candidate_outside_edit_boundary"
            _v2_fail(code, f"v2 body contains forbidden token: {token}")
        _v2_require_public_text(body, label="v2 replacement body")
        try:
            assert_generated_source_is_safe(body)
        except ValueError as error:
            code = (
                "oracle_or_gold_import"
                if "quarantined" in str(error)
                else "candidate_nonstandard_axiom"
            )
            _v2_fail(code, str(error))
        bodies.append((declaration, body if body.endswith("\n") else body + "\n"))
    return NPHardAuthoringPatchV2(
        request_id=task.request_id,
        task_class=task.task_class,
        required_direction=task.required_direction,
        source_problem=source,
        target_problem=target,
        dependency_fingerprint=task.dependency_fingerprint,
        replacement_bodies=tuple(bodies),
    )


@dataclass(frozen=True)
class NPHardAuthoringResultV2:
    request_id: str
    outcome: str
    accepted_nodes: tuple[str, ...]
    remaining_nodes: tuple[str, ...]
    candidate_hashes: tuple[tuple[str, str], ...]
    lean_diagnostics: tuple[str, ...]
    policy_diagnostics: tuple[str, ...]
    model_calls: tuple[Mapping[str, Any], ...]
    final_certificate: str | None
    replay_certificate: str | None
    schema_version: str = NP_HARD_AUTHORING_RESULT_SCHEMA_V2

    def validate(self, task: NPHardAuthoringTaskV2) -> None:
        task.validate()
        if self.schema_version != NP_HARD_AUTHORING_RESULT_SCHEMA_V2:
            _v2_fail("invalid_np_hard_authoring_v2_schema", "unsupported v2 result schema")
        if self.request_id != task.request_id:
            _v2_fail("candidate_dependency_stale", "v2 result belongs to another request")
        if self.outcome not in NP_HARD_AUTHORING_OUTCOMES_V2:
            _v2_fail("invalid_np_hard_authoring_v2_schema", "unsupported v2 result outcome")
        all_nodes = tuple(node.node_id for node in task.gap_nodes)
        if len(set(self.accepted_nodes)) != len(self.accepted_nodes) or len(
            set(self.remaining_nodes)
        ) != len(self.remaining_nodes):
            _v2_fail("candidate_dependency_stale", "v2 result repeats a node")
        if set(self.accepted_nodes) & set(self.remaining_nodes) or set(
            self.accepted_nodes + self.remaining_nodes
        ) != set(all_nodes):
            _v2_fail("candidate_dependency_stale", "v2 result does not partition gap nodes")
        if self.accepted_nodes != all_nodes[: len(self.accepted_nodes)]:
            _v2_fail("candidate_dependency_stale", "v2 accepted nodes are not a DAG prefix")
        candidate_hashes = dict(self.candidate_hashes)
        if len(candidate_hashes) != len(self.candidate_hashes) or set(candidate_hashes) != set(
            self.accepted_nodes
        ):
            _v2_fail("candidate_dependency_stale", "v2 result candidate hashes do not match accepted nodes")
        for node_id, digest in self.candidate_hashes:
            _v2_require_hash(digest, label=f"candidate hash {node_id}")
        if self.outcome == "accepted":
            if self.accepted_nodes != all_nodes or self.remaining_nodes:
                _v2_fail("candidate_dependency_stale", "accepted v2 result has remaining nodes")
            if self.final_certificate is None or self.replay_certificate is None:
                _v2_fail("independent_replay_failed", "accepted v2 result lacks final certificates")
            _v2_require_hash(self.final_certificate, label="final certificate")
            _v2_require_hash(self.replay_certificate, label="replay certificate")
        elif self.final_certificate is not None or self.replay_certificate is not None:
            _v2_fail("independent_replay_failed", "non-accepted v2 result claims final authority")
        if not all(isinstance(item, str) for item in self.lean_diagnostics + self.policy_diagnostics):
            _v2_fail("invalid_np_hard_authoring_v2_schema", "v2 result diagnostics are invalid")
        if not all(isinstance(item, Mapping) for item in self.model_calls):
            _v2_fail("invalid_np_hard_authoring_v2_schema", "v2 result model calls are invalid")

    def to_dict(self, task: NPHardAuthoringTaskV2) -> dict[str, Any]:
        self.validate(task)
        return {
            "schema_version": self.schema_version,
            "request_id": self.request_id,
            "outcome": self.outcome,
            "accepted_nodes": list(self.accepted_nodes),
            "remaining_nodes": list(self.remaining_nodes),
            "candidate_hashes": dict(self.candidate_hashes),
            "lean_diagnostics": list(self.lean_diagnostics),
            "policy_diagnostics": list(self.policy_diagnostics),
            "model_calls": [dict(item) for item in self.model_calls],
            "final_certificate": self.final_certificate,
            "replay_certificate": self.replay_certificate,
        }

    @classmethod
    def from_dict(
        cls, value: Mapping[str, Any], *, task: NPHardAuthoringTaskV2
    ) -> "NPHardAuthoringResultV2":
        if not isinstance(value, Mapping):
            _v2_fail("invalid_np_hard_authoring_v2_schema", "v2 result must be an object")
        expected = {
            "schema_version",
            "request_id",
            "outcome",
            "accepted_nodes",
            "remaining_nodes",
            "candidate_hashes",
            "lean_diagnostics",
            "policy_diagnostics",
            "model_calls",
            "final_certificate",
            "replay_certificate",
        }
        _v2_exact_keys(value, expected, label="v2 result")
        if value["schema_version"] != NP_HARD_AUTHORING_RESULT_SCHEMA_V2:
            _v2_fail("invalid_np_hard_authoring_v2_schema", "unsupported v2 result schema")
        for key in ("accepted_nodes", "remaining_nodes", "lean_diagnostics", "policy_diagnostics"):
            if not isinstance(value[key], list) or not all(isinstance(item, str) for item in value[key]):
                _v2_fail("invalid_np_hard_authoring_v2_schema", f"v2 result field {key} is invalid")
        if not isinstance(value["candidate_hashes"], Mapping) or not all(
            isinstance(name, str) and isinstance(digest, str)
            for name, digest in value["candidate_hashes"].items()
        ):
            _v2_fail("invalid_np_hard_authoring_v2_schema", "v2 result candidate hashes are invalid")
        if not isinstance(value["model_calls"], list) or not all(
            isinstance(item, Mapping) for item in value["model_calls"]
        ):
            _v2_fail("invalid_np_hard_authoring_v2_schema", "v2 result model calls are invalid")
        if not isinstance(value["request_id"], str) or not isinstance(value["outcome"], str):
            _v2_fail("invalid_np_hard_authoring_v2_schema", "v2 result identity is invalid")
        for key in ("final_certificate", "replay_certificate"):
            if value[key] is not None and not isinstance(value[key], str):
                _v2_fail("invalid_np_hard_authoring_v2_schema", f"v2 result field {key} is invalid")
        result = cls(
            request_id=value["request_id"],
            outcome=value["outcome"],
            accepted_nodes=tuple(value["accepted_nodes"]),
            remaining_nodes=tuple(value["remaining_nodes"]),
            candidate_hashes=tuple(sorted(value["candidate_hashes"].items())),
            lean_diagnostics=tuple(value["lean_diagnostics"]),
            policy_diagnostics=tuple(value["policy_diagnostics"]),
            model_calls=tuple(dict(item) for item in value["model_calls"]),
            final_certificate=value["final_certificate"],
            replay_certificate=value["replay_certificate"],
            schema_version=value["schema_version"],
        )
        result.validate(task)
        return result


def accepted_np_hard_authoring_result_v2(
    *,
    task: NPHardAuthoringTaskV2,
    candidate_hashes: Mapping[str, str],
    final_certificate: str,
    replay_certificate: str,
    lean_diagnostics: tuple[str, ...] = (),
    policy_diagnostics: tuple[str, ...] = (),
    model_calls: tuple[Mapping[str, Any], ...] = (),
) -> NPHardAuthoringResultV2:
    result = NPHardAuthoringResultV2(
        request_id=task.request_id,
        outcome="accepted",
        accepted_nodes=tuple(node.node_id for node in task.gap_nodes),
        remaining_nodes=(),
        candidate_hashes=tuple(sorted(candidate_hashes.items())),
        lean_diagnostics=lean_diagnostics,
        policy_diagnostics=policy_diagnostics,
        model_calls=model_calls,
        final_certificate=final_certificate,
        replay_certificate=replay_certificate,
    )
    result.validate(task)
    return result
