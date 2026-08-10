"""Versioned existing-route runner for exact native NP-hardness requests."""

from __future__ import annotations

import json
import secrets
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

from .lean_runner import (
    RUNTIME_MODULE,
    assert_generated_source_is_safe,
    build_module_command,
    module_file,
    run_command,
    sha256_file,
    validate_declaration_name,
    validate_module_name,
)
from .models import CommandResult, sha256_id
from .lean_worker_pool import StagePLeanWorkerPool
from .model_client import DeepSeekClient, DeepSeekConfig
from .np_hard_authoring import (
    NP_HARD_AUTHORING_DIRECTION,
    NPHardAuthoredCandidateV1,
    NPHardAuthoringFailureV1,
    NPHardModelClient,
    author_exact_np_hard_reduction,
    build_np_hard_authoring_task,
    publish_np_hard_candidate,
)
from .np_hard_input import (
    NPHardInputError,
    NPHardInputReferenceV1,
    certify_np_hard_input,
    resolve_np_hard_input_reference,
)
from .state import JobStore, compute_job_id


NP_HARD_GOAL_SCHEMA_V1 = "hardness_np_hard_goal_ir_v1"
NP_HARD_REQUEST_ABI_V1 = "typed_np_hard_request_v1"
NP_HARD_PROBE_SCHEMA_V1 = "hardness_np_hard_probe_v1"
NP_HARD_RESULT_SCHEMA_V1 = "hardness_np_hard_result_v1"
NP_HARD_SEED_CATALOG_SCHEMA_V1 = "hardness_np_hard_seed_catalog_v1"
NP_HARD_DIRECTION = "hardness_seed_to_problem"
NP_HARD_OBJECTIVE = "prove_np_hard"
NP_HARD_MARKER = "HARDNESS_NP_HARD"
NP_HARD_EVIDENCE_KINDS = {"registered_hardness", "transported_hardness"}
NP_HARD_SEED_KINDS = {"native_hardness", "native_completeness_projection"}


@dataclass(frozen=True)
class NPHardGoalV1:
    input_module: str
    problem_declaration: str
    registry_fingerprint: str
    toolchain: str
    input_sha256: str
    lake_manifest_sha256: str
    schema_version: str = NP_HARD_GOAL_SCHEMA_V1
    request_abi: str = NP_HARD_REQUEST_ABI_V1
    objective: str = NP_HARD_OBJECTIVE
    direction: str = NP_HARD_DIRECTION

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class NPHardSeedV1:
    problem_declaration: str
    normalized_problem_node: str
    evidence_declaration: str
    evidence_kind: str
    registry_fingerprint: str

    @property
    def entry_id(self) -> str:
        return sha256_id(
            {
                "schema_version": NP_HARD_SEED_CATALOG_SCHEMA_V1,
                "problem_declaration": self.problem_declaration,
                "normalized_problem_node": self.normalized_problem_node,
                "evidence_declaration": self.evidence_declaration,
                "evidence_kind": self.evidence_kind,
                "registry_fingerprint": self.registry_fingerprint,
            }
        )

    def to_dict(self) -> dict[str, Any]:
        return {**asdict(self), "entry_id": self.entry_id}


@dataclass(frozen=True)
class NPHardResolutionV1:
    request_id: str
    evidence_kind: str
    hub_declaration: str
    hardness_declaration: str | None
    completeness_declaration: str | None
    atoms: tuple[str, ...]
    roles: tuple[str, ...]
    final_composition_count: int
    unique_dependency_count: int
    registry_fingerprint: str
    direction: str = NP_HARD_DIRECTION

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class NPHardFailureV1:
    request_id: str
    code: str
    declaration_handles: tuple[str, ...]
    stable_gap_id: str | None
    explanation: str
    registry_fingerprint: str

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class NPHardProbeV1:
    nonce: str
    registry_fingerprint: str
    problem_declaration: str
    problem_node: str
    problem_display: str
    seeds: tuple[NPHardSeedV1, ...]
    reverse_only: bool
    resolution: NPHardResolutionV1 | None = None
    failure: NPHardFailureV1 | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": NP_HARD_PROBE_SCHEMA_V1,
            "nonce": self.nonce,
            "registry_fingerprint": self.registry_fingerprint,
            "input": {
                "problem_declaration": self.problem_declaration,
                "normalized_problem_node": self.problem_node,
                "display": self.problem_display,
            },
            "seeds": [seed.to_dict() for seed in self.seeds],
            "reverse_only": self.reverse_only,
            "resolution": self.resolution.to_dict() if self.resolution else None,
            "failure": self.failure.to_dict() if self.failure else None,
        }


@dataclass
class NPHardAgentResultV1:
    job_id: str
    status: str
    output_dir: str
    goal: NPHardGoalV1 | None = None
    probe: NPHardProbeV1 | None = None
    commands: list[CommandResult] = field(default_factory=list)
    failure: NPHardFailureV1 | None = None
    artifact_file: str | None = None
    artifact_sha256: str | None = None
    report_file: str | None = None
    model_calls: int = 0
    input_identity: dict[str, Any] | None = None
    certificates: dict[str, Any] = field(default_factory=dict)
    authored_probe: NPHardProbeV1 | None = None
    hub_selection: dict[str, Any] | None = None
    authoring: dict[str, Any] | None = None
    publication: dict[str, Any] | None = None
    candidate_worker: dict[str, Any] | None = None
    schema_version: str = NP_HARD_RESULT_SCHEMA_V1

    @property
    def verified(self) -> bool:
        return self.status == "VERIFIED"

    def to_dict(self) -> dict[str, Any]:
        effective_probe = self.authored_probe or self.probe
        resolution = effective_probe.resolution if effective_probe else None
        authoring_calls = (self.authoring or {}).get("calls") or []
        selected_hub = resolution.hub_declaration if resolution else None
        if selected_hub is None and self.hub_selection:
            selected = (self.hub_selection.get("result") or {}).get("selected_candidate")
            selected_hub = selected.get("seed_problem") if selected else None
        return {
            "schema_version": self.schema_version,
            "job_id": self.job_id,
            "status": self.status,
            "output_dir": self.output_dir,
            "goal": self.goal.to_dict() if self.goal else None,
            "probe": self.probe.to_dict() if self.probe else None,
            "failure": self.failure.to_dict() if self.failure else None,
            "commands": [command.to_dict() for command in self.commands],
            "artifact_file": self.artifact_file,
            "artifact_sha256": self.artifact_sha256,
            "report_file": self.report_file,
            "model_calls": self.model_calls,
            "input_identity": self.input_identity,
            "selected_hub": selected_hub,
            "route": {
                "direction": resolution.direction,
                "atoms": list(resolution.atoms),
                "roles": list(resolution.roles),
            } if resolution else None,
            "model_call_ledger": list(authoring_calls),
            "certificates": self.certificates,
            "authored_probe": self.authored_probe.to_dict() if self.authored_probe else None,
            "hub_selection": self.hub_selection,
            "authoring": self.authoring,
            "publication": self.publication,
            "candidate_worker": self.candidate_worker,
            "trust_boundary": {
                "request_is_exact_presented_problem": True,
                "direction_is_frozen": NP_HARD_DIRECTION,
                "lean_selects_seed_and_forward_path": True,
                "python_probe_data_is_observational": True,
                "target_membership_required": False,
                "final_type": "ComplexityReduction.Certificate.NativeTMNPHard",
                "standard_axiom_audit": True,
                "independent_release_replay": True,
                "legacy_reduce_to_known_hardness_counted": False,
                "model_output_has_proof_authority": False,
                "model_selected_hardness_hub": False,
                "authored_gap_direction": NP_HARD_AUTHORING_DIRECTION,
                "fresh_core_after_publication": bool(self.publication),
                "candidate_validation_authority": (
                    "persistent_lean_worker" if self.candidate_worker else "cold_lean_process"
                ),
                "final_artifact_authority": "independent_lean_process",
                "release_replay_authority": "independent_lean_process",
                "candidate_worker_has_final_authority": False,
            },
        }


@dataclass(frozen=True)
class NPHardAgentConfigV1:
    root: Path
    input_module: str
    problem_declaration: str
    output_dir: Path | None = None
    lean_timeout_seconds: int = 300
    planner_mode: str = "deterministic"
    authoring_mode: str = "disabled"
    authoring_attempt_budget: int = 4
    deepseek: DeepSeekConfig | None = None
    runtime_prebuilt: bool = False
    candidate_validation_mode: str = "persistent-worker"
    input_reference: NPHardInputReferenceV1 | None = None


def _split_csv(value: str) -> tuple[str, ...]:
    return tuple(part for part in value.split(",") if part)


def _parse_nonnegative_int(value: str, *, label: str) -> int:
    if not value.isdigit():
        raise ValueError(f"NP-hard probe has invalid {label}")
    return int(value)


def parse_np_hard_probe_output(
    *, stdout: str, stderr: str, nonce: str, problem_declaration: str
) -> NPHardProbeV1:
    """Parse only nonce-bound rows emitted by the Lean V1 probe."""

    rows: list[list[str]] = []
    prefix = NP_HARD_MARKER + "\t"
    for raw_line in (stdout + "\n" + stderr).splitlines():
        marker_at = raw_line.find(prefix)
        if marker_at < 0:
            continue
        fields = raw_line[marker_at:].split("\t")
        if len(fields) < 4:
            raise ValueError("NP-hard probe emitted a truncated row")
        if fields[1] != NP_HARD_PROBE_SCHEMA_V1:
            raise ValueError("NP-hard probe emitted an unsupported schema")
        if fields[2] != nonce:
            continue
        rows.append(fields)
    if not rows:
        raise ValueError("NP-hard probe emitted no nonce-bound rows")

    by_kind: dict[str, list[list[str]]] = {}
    for row in rows:
        by_kind.setdefault(row[3], []).append(row)
    for singleton in ("registry", "input", "reverse_audit"):
        if len(by_kind.get(singleton, ())) != 1:
            raise ValueError(f"NP-hard probe requires exactly one {singleton} row")
    registry_row = by_kind["registry"][0]
    if len(registry_row) != 5 or not registry_row[4].startswith("lean:"):
        raise ValueError("NP-hard probe has an invalid registry row")
    fingerprint = registry_row[4]
    input_row = by_kind["input"][0]
    if len(input_row) != 8:
        raise ValueError("NP-hard probe has an invalid input row")
    if input_row[4] != problem_declaration:
        raise ValueError("NP-hard probe changed the requested problem declaration")
    if input_row[7] != fingerprint:
        raise ValueError("NP-hard probe input row changed the registry fingerprint")

    seeds: list[NPHardSeedV1] = []
    for row in by_kind.get("seed", ()):
        if len(row) != 9:
            raise ValueError("NP-hard probe has an invalid seed row")
        if row[7] not in NP_HARD_SEED_KINDS or row[8] != fingerprint:
            raise ValueError("NP-hard probe has an invalid seed capability")
        seeds.append(
            NPHardSeedV1(
                problem_declaration=validate_declaration_name(row[4], label="seed problem"),
                normalized_problem_node=row[5],
                evidence_declaration=validate_declaration_name(
                    row[6], label="seed evidence"
                ),
                evidence_kind=row[7],
                registry_fingerprint=row[8],
            )
        )

    resolved_rows = by_kind.get("resolved", ())
    failure_rows = by_kind.get("failure", ())
    if (len(resolved_rows), len(failure_rows)) not in {(1, 0), (0, 1)}:
        raise ValueError("NP-hard probe must emit exactly one resolution or typed failure")
    reverse_row = by_kind["reverse_audit"][0]
    if len(reverse_row) != 7 or reverse_row[5] not in {"true", "false"}:
        raise ValueError("NP-hard probe has an invalid reverse audit")
    if reverse_row[6] != fingerprint:
        raise ValueError("NP-hard reverse audit changed the registry fingerprint")
    reverse_only = reverse_row[5] == "true"

    resolution: NPHardResolutionV1 | None = None
    failure: NPHardFailureV1 | None = None
    if resolved_rows:
        row = resolved_rows[0]
        if len(row) != 15:
            raise ValueError("NP-hard probe has an invalid resolution row")
        evidence_kind = row[5]
        atoms = _split_csv(row[9])
        roles = _split_csv(row[10])
        hardness = row[7] or None
        completeness = row[8] or None
        if evidence_kind not in NP_HARD_EVIDENCE_KINDS:
            raise ValueError("NP-hard probe has an unsupported evidence kind")
        if row[14] != NP_HARD_DIRECTION:
            raise ValueError("NP-hard probe changed the frozen direction")
        if row[13] != fingerprint or reverse_only:
            raise ValueError("successful NP-hard resolution has inconsistent audit data")
        if len(atoms) != len(roles):
            raise ValueError("NP-hard route lost atom-role alignment")
        for declaration in atoms:
            validate_declaration_name(declaration, label="route atom")
        final_count = _parse_nonnegative_int(row[11], label="final-composition count")
        unique_count = _parse_nonnegative_int(row[12], label="dependency count")
        if final_count != sum(role == "finalComposition" for role in roles):
            raise ValueError("NP-hard route final-composition count is inconsistent")
        if unique_count != len(set(atoms)):
            raise ValueError("NP-hard route dependency count is inconsistent")
        if evidence_kind == "registered_hardness":
            if not hardness or completeness or atoms:
                raise ValueError("registered NP-hardness has invalid provenance")
            hub = validate_declaration_name(
                row[6] or problem_declaration, label="hardness hub"
            )
        elif bool(hardness) == bool(completeness):
            raise ValueError("transported NP-hardness must select one exact seed declaration")
        else:
            hub = validate_declaration_name(row[6], label="hardness hub")
        if hardness:
            validate_declaration_name(hardness, label="hardness evidence")
        if completeness:
            validate_declaration_name(completeness, label="completeness evidence")
        resolution = NPHardResolutionV1(
            request_id=row[4],
            evidence_kind=evidence_kind,
            hub_declaration=hub,
            hardness_declaration=hardness,
            completeness_declaration=completeness,
            atoms=atoms,
            roles=roles,
            final_composition_count=final_count,
            unique_dependency_count=unique_count,
            registry_fingerprint=row[13],
            direction=row[14],
        )
    else:
        row = failure_rows[0]
        if len(row) != 10 or row[9] != fingerprint:
            raise ValueError("NP-hard probe has an invalid failure row")
        handles = _split_csv(row[6])
        for declaration in handles:
            validate_declaration_name(declaration, label="failure declaration")
        failure = NPHardFailureV1(
            request_id=row[4],
            code=row[5],
            declaration_handles=handles,
            stable_gap_id=row[7] or None,
            explanation=row[8],
            registry_fingerprint=row[9],
        )
        if reverse_only != (failure.code == "wrong_direction_only"):
            raise ValueError("NP-hard typed failure disagrees with reverse audit")
    request_id = resolution.request_id if resolution else failure.request_id  # type: ignore[union-attr]
    if reverse_row[4] != request_id:
        raise ValueError("NP-hard reverse audit changed the request ID")
    return NPHardProbeV1(
        nonce=nonce,
        registry_fingerprint=fingerprint,
        problem_declaration=input_row[4],
        problem_node=input_row[5],
        problem_display=input_row[6],
        seeds=tuple(sorted(seeds, key=lambda seed: seed.entry_id)),
        reverse_only=reverse_only,
        resolution=resolution,
        failure=failure,
    )


def build_np_hard_goal_source(*, input_module: str, problem_declaration: str) -> str:
    module = validate_module_name(input_module)
    problem = validate_declaration_name(problem_declaration, label="problem")
    return f"""import ComplexityReduction.Protocol.NPHard
import {module}

namespace ComplexityReduction.Agent.Hardness.GeneratedNPHardGoal

def request : ComplexityReduction.Protocol.TypedNPHardRequestV1 where
  problem := {problem}

example : ComplexityReduction.Encoding.PresentedProblem := request.problem

end ComplexityReduction.Agent.Hardness.GeneratedNPHardGoal
"""


def build_np_hard_probe_source(
    *, input_module: str, problem_declaration: str, nonce: str
) -> str:
    module = validate_module_name(input_module)
    problem = validate_declaration_name(problem_declaration, label="problem")
    if not nonce or any(character in nonce for character in "\r\n\t\""):
        raise ValueError("probe nonce is not a safe string literal")
    return (
        f"import {module}\n"
        f"import {RUNTIME_MODULE}\n\n"
        f"#hardness_agent_probe_np_hard_v1 {json.dumps(nonce)} {problem}\n"
    )


def _path_term(atoms: tuple[str, ...], hub: str) -> str:
    if not atoms:
        return f"ComplexityReduction.Certificate.CertifiedPath.refl {hub}"
    term = f"ComplexityReduction.Certificate.CertifiedPath.step {atoms[0]}"
    for atom in atoms[1:]:
        term = (
            "ComplexityReduction.Certificate.CertifiedPath.cons\n"
            f"      ({term})\n"
            f"      {atom}"
        )
    return term


def build_np_hard_artifact_source(
    *, input_module: str, problem_declaration: str, resolution: NPHardResolutionV1
) -> str:
    module = validate_module_name(input_module)
    problem = validate_declaration_name(problem_declaration, label="problem")
    hub = validate_declaration_name(resolution.hub_declaration, label="hardness hub")
    if resolution.direction != NP_HARD_DIRECTION:
        raise ValueError("artifact resolution changed the frozen NP-hardness direction")
    for atom in resolution.atoms:
        validate_declaration_name(atom, label="route atom")
    if resolution.evidence_kind == "registered_hardness":
        evidence = validate_declaration_name(
            resolution.hardness_declaration or "", label="hardness evidence"
        )
        evidence_block = f"""noncomputable def selectedHubHardness :
    ComplexityReduction.Certificate.NativeTMNPHard {problem} :=
  {evidence}

"""
        path_block = ""
        result_body = (
            "ComplexityReduction.Protocol.TypedNPHardResultV1.fromRegistered\n"
            "    request selectedHubHardness"
        )
        audited = ["selectedHubHardness", "result", "problemIsNPHard", "resolverResult"]
    elif resolution.evidence_kind == "transported_hardness":
        if resolution.completeness_declaration:
            completeness = validate_declaration_name(
                resolution.completeness_declaration, label="completeness evidence"
            )
            evidence_term = (
                "ComplexityReduction.Certificate.NativeTMNPComplete.nativeHardness\n"
                f"    {completeness}"
            )
        else:
            evidence_term = validate_declaration_name(
                resolution.hardness_declaration or "", label="hardness evidence"
            )
        evidence_block = f"""noncomputable def selectedHubHardness :
    ComplexityReduction.Certificate.NativeTMNPHard {hub} :=
  {evidence_term}

"""
        path_block = f"""noncomputable def selectedPath :
    ComplexityReduction.Certificate.CertifiedPath {hub} {problem} :=
  {_path_term(resolution.atoms, hub)}

"""
        result_body = (
            "ComplexityReduction.Protocol.TypedNPHardResultV1.fromPath\n"
            "    request selectedHubHardness selectedPath"
        )
        audited = [
            "selectedHubHardness",
            "selectedPath",
            "result",
            "problemIsNPHard",
            "resolverResult",
        ]
    else:
        raise ValueError("artifact has an unsupported NP-hardness evidence kind")
    audit = ",\n  ".join(
        f"ComplexityReduction.Agent.Hardness.GeneratedNPHard.{name}" for name in audited
    )
    return f"""import {module}
import {RUNTIME_MODULE}
import ComplexityReduction.Protocol.NPHard

namespace ComplexityReduction.Agent.Hardness.GeneratedNPHard

noncomputable section

def request : ComplexityReduction.Protocol.TypedNPHardRequestV1 where
  problem := {problem}

{evidence_block}{path_block}@[complexity_reduction_ir_typed_final_result]
noncomputable def result :
    ComplexityReduction.Protocol.TypedNPHardResultV1 request :=
  {result_body}

theorem problemIsNPHard :
    ComplexityReduction.Certificate.NativeTMNPHard {problem} :=
  result.extractNativeHardness

noncomputable def resolverResult :
    ComplexityReduction.Protocol.TypedNPHardResultV1 request :=
  by_np_hard_resolver

end

end ComplexityReduction.Agent.Hardness.GeneratedNPHard

assert_standard_axioms
  {audit}
"""


def build_np_hard_artifact_declarations_source(
    *, input_module: str, problem_declaration: str, resolution: NPHardResolutionV1
) -> str:
    """Return the final declarations without imports for a combined authored file."""

    source = build_np_hard_artifact_source(
        input_module=input_module,
        problem_declaration=problem_declaration,
        resolution=resolution,
    )
    marker = "namespace ComplexityReduction.Agent.Hardness.GeneratedNPHard\n"
    marker_at = source.find(marker)
    if marker_at < 0:
        raise ValueError("NP-hard artifact declaration marker is missing")
    return source[marker_at:]


def _display(path: Path, root: Path) -> str:
    try:
        return str(path.resolve().relative_to(root.resolve()))
    except ValueError:
        return str(path.resolve())


class NPHardAgentV1:
    def __init__(
        self,
        config: NPHardAgentConfigV1,
        *,
        model_client: NPHardModelClient | None = None,
    ):
        self.config = config
        self.root = config.root.resolve()
        self.lean_root = self.root / "Lean"
        self.model_client = model_client or (
            DeepSeekClient(config.deepseek) if config.deepseek is not None else None
        )

    def _write_report(self, store: JobStore, result: NPHardAgentResultV1) -> None:
        report = store.path("report.json")
        result.report_file = _display(report, self.root)
        store.write_json("report.json", result.to_dict())

    def _write_seed_catalog(
        self, store: JobStore, *, probe: NPHardProbeV1, goal: NPHardGoalV1
    ) -> None:
        payload = {
            "schema_version": NP_HARD_SEED_CATALOG_SCHEMA_V1,
            "registry_fingerprint": probe.registry_fingerprint,
            "toolchain": goal.toolchain,
            "lake_manifest_sha256": goal.lake_manifest_sha256,
            "entries": [seed.to_dict() for seed in probe.seeds],
        }
        store.write_json("np-hard-seed-catalog.json", payload)
        catalog_path = self.root / ".reduction-agent" / "np-hard-seed-catalog.json"
        catalog_path.parent.mkdir(parents=True, exist_ok=True)
        temporary = catalog_path.with_name(
            f".{catalog_path.name}.{secrets.token_hex(16)}.tmp"
        )
        try:
            temporary.write_text(
                json.dumps(payload, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            temporary.replace(catalog_path)
        finally:
            temporary.unlink(missing_ok=True)

    def _validate(self) -> tuple[NPHardInputReferenceV1, Path, str, str, str]:
        reference = self.config.input_reference or resolve_np_hard_input_reference(
            root=self.root,
            input_module=self.config.input_module,
            requested_term=self.config.problem_declaration,
            timeout_seconds=self.config.lean_timeout_seconds,
        )
        if self.config.planner_mode != "deterministic":
            raise ValueError("prove-np-hard requires the deterministic planner")
        if self.config.authoring_mode not in {"disabled", "model-auto", "model-required"}:
            raise ValueError("prove-np-hard supports disabled or fenced model authoring")
        if not 1 <= self.config.authoring_attempt_budget <= 4:
            raise ValueError("prove-np-hard authoring attempts must be between one and four")
        if self.config.candidate_validation_mode not in {
            "persistent-worker",
            "cold-process",
        }:
            raise ValueError("prove-np-hard has an unsupported candidate validation mode")
        input_path = module_file(self.lean_root, reference.input_module)
        toolchain = (self.lean_root / "lean-toolchain").read_text(encoding="utf-8").strip()
        manifest_hash = sha256_file(self.lean_root / "lake-manifest.json")
        return reference, input_path, sha256_file(input_path), toolchain, manifest_hash

    def run(self) -> NPHardAgentResultV1:
        reference, input_path, input_hash, toolchain, manifest_hash = self._validate()
        input_module = reference.input_module
        problem_declaration = reference.problem_declaration
        job_id = compute_job_id(
            {
                "schema_version": NP_HARD_GOAL_SCHEMA_V1,
                "requested_term": reference.requested_term,
                "input_module": input_module,
                "problem_declaration": problem_declaration,
                "objective": NP_HARD_OBJECTIVE,
                "direction": NP_HARD_DIRECTION,
                "input_sha256": input_hash,
                "toolchain": toolchain,
                "lake_manifest_sha256": manifest_hash,
                "authoring_mode": self.config.authoring_mode,
                "authoring_model": (
                    self.config.deepseek.to_public_dict()
                    if self.config.deepseek is not None
                    else None
                ),
                "candidate_validation_mode": self.config.candidate_validation_mode,
            }
        )
        output_dir = (
            self.config.output_dir.resolve()
            if self.config.output_dir
            else self.root
            / ".reduction-agent"
            / "jobs"
            / job_id.removeprefix("sha256:")
        )
        store = JobStore(output_dir)
        with store.exclusive_run():
            result = NPHardAgentResultV1(
                job_id=job_id,
                status="RECEIVED",
                output_dir=_display(output_dir, self.root),
            )
            store.transition("RECEIVED", details={"job_id": job_id})
            goal_source = build_np_hard_goal_source(
                input_module=input_module,
                problem_declaration=problem_declaration,
            )
            goal_path = store.write_text("Goal.lean", goal_source)
            if not self.config.runtime_prebuilt:
                build = run_command(
                    build_module_command([input_module]),
                    cwd=self.lean_root,
                    timeout_seconds=self.config.lean_timeout_seconds,
                )
                result.commands.append(build)
                store.write_json("commands/build-runtime.json", build.to_dict())
                if not build.ok:
                    result.status = "FAILED"
                    store.transition("FAILED", details={"code": "runtime_build_failed"})
                    self._write_report(store, result)
                    return result
            try:
                identity, input_gate = certify_np_hard_input(
                    root=self.root,
                    reference=reference,
                    certificate_path=store.path("InputNormalization.lean"),
                    toolchain=toolchain,
                    lake_manifest_sha256=manifest_hash,
                    timeout_seconds=self.config.lean_timeout_seconds,
                )
            except NPHardInputError as error:
                if error.command is not None:
                    result.commands.append(error.command)
                    store.write_json("commands/input-normalization.json", error.command.to_dict())
                failure = NPHardFailureV1(
                    request_id=sha256_id({
                        "schema_version": NP_HARD_GOAL_SCHEMA_V1,
                        "requested_term": reference.requested_term,
                        "input_module": input_module,
                    }),
                    code=error.code,
                    declaration_handles=(error.candidates or (problem_declaration,)),
                    stable_gap_id=None,
                    explanation=error.message,
                    registry_fingerprint="lean:input-normalization",
                )
                result.failure = failure
                result.status = (
                    "BLOCKED"
                    if error.code in {
                        "input_problem_not_found",
                        "input_not_presented_problem",
                        "missing_lawful_presentation",
                        "ambiguous_lawful_presentation",
                        "candidate_dependency_stale",
                    }
                    else "FAILED"
                )
                store.transition(result.status, details={"code": error.code})
                self._write_report(store, result)
                return result
            result.commands.append(input_gate)
            result.input_identity = identity.to_dict()
            result.certificates["normalization"] = {
                "file": _display(store.path("InputNormalization.lean"), self.root),
                "sha256": identity.normalization_certificate_sha256,
                "authority": "lean-checked-artifact",
            }
            store.write_json("input-identity.json", result.input_identity)
            store.write_json("commands/input-normalization.json", input_gate.to_dict())
            store.transition("INPUT_VALIDATED")

            nonce = secrets.token_hex(16)
            probe_path = store.write_text(
                "Probe.lean",
                build_np_hard_probe_source(
                    input_module=input_module,
                    problem_declaration=problem_declaration,
                    nonce=nonce,
                ),
            )
            probe_command = run_command(
                ["lake", "env", "lean", str(probe_path)],
                cwd=self.lean_root,
                timeout_seconds=self.config.lean_timeout_seconds,
            )
            result.commands.append(probe_command)
            store.write_json("commands/probe.json", probe_command.to_dict())
            if not probe_command.ok:
                result.status = "FAILED"
                store.transition("FAILED", details={"code": "probe_execution_failed"})
                self._write_report(store, result)
                return result
            try:
                probe = parse_np_hard_probe_output(
                    stdout=probe_command.stdout,
                    stderr=probe_command.stderr,
                    nonce=nonce,
                    problem_declaration=problem_declaration,
                )
            except ValueError:
                result.status = "FAILED"
                store.transition("FAILED", details={"code": "probe_protocol_error"})
                self._write_report(store, result)
                return result
            result.probe = probe
            goal = NPHardGoalV1(
                input_module=input_module,
                problem_declaration=problem_declaration,
                registry_fingerprint=probe.registry_fingerprint,
                toolchain=toolchain,
                input_sha256=input_hash,
                lake_manifest_sha256=manifest_hash,
            )
            result.goal = goal
            store.write_json("goal.json", goal.to_dict())
            store.write_json("probe.json", probe.to_dict())
            self._write_seed_catalog(store, probe=probe, goal=goal)
            store.transition(
                "CAPABILITIES_SCANNED",
                details={"registry_fingerprint": probe.registry_fingerprint},
            )
            authored_candidate: NPHardAuthoredCandidateV1 | None = None
            if probe.failure:
                can_author = (
                    self.config.authoring_mode in {"model-auto", "model-required"}
                    and probe.failure.code == "no_forward_path_from_hardness_seed"
                    and bool(probe.seeds)
                )
                if not can_author:
                    result.failure = probe.failure
                    result.status = "BLOCKED"
                    store.transition("BLOCKED", details={"code": probe.failure.code})
                    self._write_report(store, result)
                    return result
                from .np_hard_hub_selection import (
                    build_np_hard_hub_selection_request,
                    project_np_hard_hub_candidates,
                    rank_np_hard_hub_candidates,
                )

                hub_candidates = project_np_hard_hub_candidates(
                    seeds=probe.seeds,
                    target_problem=problem_declaration,
                )
                hub_request = build_np_hard_hub_selection_request(
                    target_problem=problem_declaration,
                    registry_fingerprint=probe.registry_fingerprint,
                    candidates=hub_candidates,
                )
                hub_result = rank_np_hard_hub_candidates(hub_request)
                result.hub_selection = {
                    "request": hub_request.to_dict(),
                    "result": hub_result.to_dict(hub_request),
                }
                store.write_json("authoring/hub-selection.json", result.hub_selection)
                if hub_result.selected_candidate_id is None:
                    failure = NPHardFailureV1(
                        request_id=probe.failure.request_id,
                        code="no_authorable_hardness_hub",
                        declaration_handles=tuple(
                            candidate.seed_problem for candidate in hub_candidates
                        ),
                        stable_gap_id=probe.failure.stable_gap_id,
                        explanation=(
                            "all Lean-observed native-hardness seeds were rejected "
                            "by the deterministic hub selector"
                        ),
                        registry_fingerprint=probe.registry_fingerprint,
                    )
                    result.failure = failure
                    result.status = "BLOCKED"
                    store.transition("BLOCKED", details={"code": failure.code})
                    self._write_report(store, result)
                    return result
                selected = next(
                    candidate
                    for candidate in hub_candidates
                    if candidate.candidate_id == hub_result.selected_candidate_id
                )
                seed = next(
                    item for item in probe.seeds if item.entry_id == selected.stable_seed_id
                )
                task = build_np_hard_authoring_task(
                    request_id=probe.failure.request_id,
                    registry_fingerprint=probe.registry_fingerprint,
                    input_module=input_module,
                    input_problem_declaration=problem_declaration,
                    hub_declaration=seed.problem_declaration,
                    seed_evidence_declaration=seed.evidence_declaration,
                    seed_evidence_kind=seed.evidence_kind,
                    input_source_sha256=input_hash,
                    job_id=job_id,
                    max_attempts=self.config.authoring_attempt_budget,
                )
                store.write_json("authoring/task.json", task.to_dict())
                store.transition(
                    "PLAN_SELECTED",
                    details={
                        "request_id": probe.failure.request_id,
                        "stable_gap_id": task.gap_id,
                        "direction": task.direction,
                    },
                )
                store.transition("AUTHORING", details={"stable_gap_id": task.gap_id})
                worker_pool: StagePLeanWorkerPool | None = None
                worker_session_id: str | None = None
                worker_owner: str | None = None
                try:
                    if self.config.candidate_validation_mode == "persistent-worker":
                        worker_pool = StagePLeanWorkerPool(
                            lean_root=self.lean_root,
                            workspace_root=output_dir,
                            service_root=store.path("authoring/lean-worker-service"),
                            maximum_workers=1,
                            timeout_seconds=self.config.lean_timeout_seconds,
                        )
                        worker_owner = f"np-hard-{job_id.removeprefix('sha256:')[:16]}"
                        worker_session_id = worker_pool.start_session(
                            owner=worker_owner,
                            namespace=task.candidate_module,
                        )
                    authored = author_exact_np_hard_reduction(
                        task=task,
                        input_source=input_path.read_text(encoding="utf-8"),
                        model=self.model_client,
                        lean_root=self.lean_root,
                        candidate_path=store.path("authoring/Candidate.lean"),
                        timeout_seconds=self.config.lean_timeout_seconds,
                        worker_pool=worker_pool,
                        worker_session_id=worker_session_id,
                        worker_owner=worker_owner,
                        toolchain=toolchain if worker_pool is not None else None,
                        lake_manifest_sha256=(
                            manifest_hash if worker_pool is not None else None
                        ),
                    )
                    worker_during_authoring = (
                        worker_pool.to_dict() if worker_pool is not None else None
                    )
                finally:
                    if (
                        worker_pool is not None
                        and worker_session_id is not None
                        and worker_owner is not None
                    ):
                        worker_pool.close_session(
                            session_id=worker_session_id, owner=worker_owner
                        )
                    if worker_pool is not None:
                        worker_pool.close()
                if worker_pool is not None:
                    result.candidate_worker = {
                        "validation_authority": "persistent_lean_worker",
                        "final_authority": False,
                        "allow_cold_fallback": False,
                        "during_authoring": worker_during_authoring,
                        "after_close": worker_pool.to_dict(),
                        "results": [item.to_dict() for item in authored.worker_results],
                    }
                    store.write_json("authoring/worker.json", result.candidate_worker)
                result.commands.extend(authored.commands)
                result.model_calls = authored.model_calls
                store.write_json("authoring/model-calls.json", list(authored.call_records))
                for index, command in enumerate(authored.commands, start=1):
                    store.write_json(
                        f"commands/authoring-candidate-{index}.json", command.to_dict()
                    )
                if isinstance(authored, NPHardAuthoringFailureV1):
                    result.failure = NPHardFailureV1(
                        request_id=probe.failure.request_id,
                        code=authored.code,
                        declaration_handles=(
                            seed.evidence_declaration,
                            problem_declaration,
                        ),
                        stable_gap_id=task.gap_id,
                        explanation=authored.explanation,
                        registry_fingerprint=probe.registry_fingerprint,
                    )
                    result.authoring = {
                        "schema_version": "hardness_np_hard_authoring_trace_v1",
                        "task": task.to_dict(),
                        "initial_failure": probe.failure.to_dict(),
                        "status": "BLOCKED",
                        "failure_code": authored.code,
                        "calls": list(authored.call_records),
                        "candidate_validation_authority": (
                            "persistent_lean_worker" if result.candidate_worker else "cold_lean_process"
                        ),
                    }
                    result.status = "BLOCKED"
                    store.transition("BLOCKED", details={"code": authored.code})
                    self._write_report(store, result)
                    return result
                authored_candidate = authored
                store.transition(
                    "CANDIDATE_COMPILED",
                    details={"candidate_source_sha256": authored.source_sha256},
                )
                published_source, publication = publish_np_hard_candidate(
                    root=output_dir, candidate=authored
                )
                result.publication = {
                    **publication,
                    "source_file": _display(published_source, self.root),
                }
                store.write_json("authoring/publication.json", result.publication)

                fresh_nonce = secrets.token_hex(16)
                fresh_source = (
                    authored.source
                    + "\n"
                    + "#hardness_agent_probe_np_hard_v1 "
                    + json.dumps(fresh_nonce)
                    + " "
                    + problem_declaration
                    + "\n"
                )
                fresh_path = store.write_text("authoring/FreshCore.lean", fresh_source)
                fresh_command = run_command(
                    ["lake", "env", "lean", str(fresh_path)],
                    cwd=self.lean_root,
                    timeout_seconds=self.config.lean_timeout_seconds,
                )
                result.commands.append(fresh_command)
                store.write_json("commands/authoring-fresh-core.json", fresh_command.to_dict())
                fresh_probe: NPHardProbeV1 | None = None
                if fresh_command.ok:
                    try:
                        fresh_probe = parse_np_hard_probe_output(
                            stdout=fresh_command.stdout,
                            stderr=fresh_command.stderr,
                            nonce=fresh_nonce,
                            problem_declaration=problem_declaration,
                        )
                    except ValueError:
                        fresh_probe = None
                fresh_valid = bool(
                    fresh_probe
                    and fresh_probe.resolution
                    and not fresh_probe.failure
                    and fresh_probe.resolution.direction == NP_HARD_DIRECTION
                    and fresh_probe.resolution.hub_declaration == task.hub_declaration
                    and task.candidate_declaration in fresh_probe.resolution.atoms
                    and fresh_probe.registry_fingerprint != probe.registry_fingerprint
                )
                if not fresh_valid:
                    result.failure = NPHardFailureV1(
                        request_id=probe.failure.request_id,
                        code="final_np_hard_resolution_failed",
                        declaration_handles=(
                            task.candidate_declaration,
                            seed.evidence_declaration,
                        ),
                        stable_gap_id=task.gap_id,
                        explanation=(
                            fresh_command.stderr
                            or fresh_command.stdout
                            or "fresh Core did not select the authored forward reduction"
                        ),
                        registry_fingerprint=probe.registry_fingerprint,
                    )
                    result.status = "FAILED"
                    store.transition(
                        "FAILED", details={"code": "final_np_hard_resolution_failed"}
                    )
                    self._write_report(store, result)
                    return result
                assert fresh_probe is not None and fresh_probe.resolution is not None
                result.authored_probe = fresh_probe
                store.write_json("authoring/fresh-probe.json", fresh_probe.to_dict())
                result.authoring = {
                    "schema_version": "hardness_np_hard_authoring_trace_v1",
                    "task": task.to_dict(),
                    "initial_failure": probe.failure.to_dict(),
                    "status": "CANDIDATE_PUBLISHED_AND_RESOLVED",
                    "candidate_source_sha256": authored.source_sha256,
                    "candidate_body_sha256": authored.body_sha256,
                    "model_response_sha256": authored.model_response_sha256,
                    "attempt": authored.attempt,
                    "model_calls": authored.model_calls,
                    "calls": list(authored.call_records),
                    "candidate_validation_authority": (
                        "persistent_lean_worker" if result.candidate_worker else "cold_lean_process"
                    ),
                    "worker_results": [
                        item.to_dict() for item in authored.worker_results
                    ],
                    "fresh_registry_fingerprint": fresh_probe.registry_fingerprint,
                    "authored_atom_selected": True,
                    "provenance_kind": "model_generated",
                }
                store.write_json("authoring/trace.json", result.authoring)
                store.transition(
                    "REGISTRY_REVALIDATED",
                    details={
                        "registry_fingerprint": fresh_probe.registry_fingerprint,
                        "candidate": task.candidate_declaration,
                    },
                )
                probe_for_resolution = fresh_probe
            else:
                probe_for_resolution = probe
            if not probe_for_resolution.resolution:
                result.status = "FAILED"
                store.transition("FAILED", details={"code": "final_np_hard_resolution_failed"})
                self._write_report(store, result)
                return result
            if authored_candidate is None:
                store.transition(
                    "PLAN_SELECTED",
                    details={"request_id": probe_for_resolution.resolution.request_id},
                )
                artifact_source = build_np_hard_artifact_source(
                    input_module=input_module,
                    problem_declaration=problem_declaration,
                    resolution=probe_for_resolution.resolution,
                )
            else:
                artifact_source = authored_candidate.source + "\n" + (
                    build_np_hard_artifact_declarations_source(
                        input_module=input_module,
                        problem_declaration=problem_declaration,
                        resolution=probe_for_resolution.resolution,
                    )
                )
            assert_generated_source_is_safe(artifact_source)
            artifact_path = store.write_text("Artifact.lean", artifact_source)
            result.artifact_file = _display(artifact_path, self.root)
            result.certificates["final"] = {
                "file": result.artifact_file,
                "authority": "independent-lean-process",
            }
            artifact = run_command(
                ["lake", "env", "lean", str(artifact_path)],
                cwd=self.lean_root,
                timeout_seconds=self.config.lean_timeout_seconds,
            )
            result.commands.append(artifact)
            store.write_json("commands/artifact.json", artifact.to_dict())
            if not artifact.ok:
                result.status = "FAILED"
                store.transition("FAILED", details={"code": "final_np_hard_resolution_failed"})
                self._write_report(store, result)
                return result
            store.transition("REGISTRY_REVALIDATED")
            store.transition("FINAL_RESOLVED")
            store.transition("AXIOM_AUDITED")
            release_replay = run_command(
                ["lake", "env", "lean", str(artifact_path)],
                cwd=self.lean_root,
                timeout_seconds=self.config.lean_timeout_seconds,
            )
            result.commands.append(release_replay)
            store.write_json("commands/independent-release-replay.json", release_replay.to_dict())
            result.certificates["replay"] = {
                "command_file": _display(
                    store.path("commands/independent-release-replay.json"), self.root
                ),
                "authority": "independent-lean-process",
                "passed": release_replay.ok,
            }
            if not release_replay.ok:
                result.status = "FAILED"
                failure = NPHardFailureV1(
                    request_id=probe_for_resolution.resolution.request_id,
                    code="independent_replay_failed",
                    declaration_handles=probe_for_resolution.resolution.atoms,
                    stable_gap_id=(
                        authored_candidate.task.gap_id if authored_candidate else None
                    ),
                    explanation=release_replay.stderr or release_replay.stdout,
                    registry_fingerprint=probe_for_resolution.registry_fingerprint,
                )
                result.failure = failure
                store.transition("FAILED", details={"code": failure.code})
                self._write_report(store, result)
                return result
            result.artifact_sha256 = sha256_file(artifact_path)
            result.status = "VERIFIED"
            store.transition(
                "VERIFIED",
                details={
                    "artifact_sha256": result.artifact_sha256,
                    "registry_fingerprint": probe_for_resolution.registry_fingerprint,
                },
            )
            self._write_report(store, result)
            return result
