"""Lean command execution and declaration-only source generation."""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import time
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path

from .catalog import (
    CATALOG_MODES,
    COMPONENT_CATALOG,
    FLAT_API_CATALOG,
    FULL_CATALOG,
    IR_COMPONENTS_CATALOG,
)
from .models import CommandResult, RouteCandidate


RUNTIME_MODULE = "ComplexityReduction.Agent.Hardness.Runtime"
INPUT_INSPECTION_MODULE = "ComplexityReduction.Agent.Hardness.InputInspection"
PROBLEM_CATALOG_MODULE = "ComplexityReduction.Agent.Hardness.ProblemCatalog"
TARGET_CATALOG_MODULE = "ComplexityReduction.Agent.Hardness.TargetCatalog"
AUTHORING_MODULE = "ComplexityReduction.Agent.Hardness.Authoring"
MODEL_AUTHORING_MODULE = "ComplexityReduction.Agent.Hardness.ModelAuthoring"
AXIOM_GATE_MODULE = "ComplexityReduction.AxiomGate"
DECLARATION_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
MODULE_RE = re.compile(r"[A-Z][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
BANNED_SOURCE_RE = re.compile(r"\b(?:sorry|admit|sorryAx|axiom)\b")
ORACLE_SOURCE_MARKERS = (
    ".Oracles.",
    ".Gold.",
    ".GoldProofs.",
    ".HiddenTargets.",
    ".Legacy.",
)
EDITABLE_BODY_BEGIN = "-- HARDNESS_EDITABLE_BODY_BEGIN\n"
EDITABLE_BODY_END = "-- HARDNESS_EDITABLE_BODY_END\n"


@dataclass(frozen=True)
class CandidateSource:
    source: str
    fixed_header: str
    editable_body: str
    fixed_footer: str

    @property
    def fixed_header_sha256(self) -> str:
        return hashlib.sha256(self.fixed_header.encode("utf-8")).hexdigest()

    @property
    def fixed_footer_sha256(self) -> str:
        return hashlib.sha256(self.fixed_footer.encode("utf-8")).hexdigest()


PROGRAM_INDEXED_REDUCTION_STAGES = (
    "executable",
    "executable_direct_tm",
    "primitive",
    "program",
    "semantic_proof",
    "direct_tm",
    "certified_reduction",
)

NATIVE_MEMBERSHIP_STAGES = (
    "verifier",
    "witness_presentation",
    "discipline",
    "native_membership",
)


@dataclass(frozen=True)
class CandidateStageSource:
    stage: str
    module: str
    declaration: str
    candidate: CandidateSource


def validate_declaration_name(value: str, *, label: str) -> str:
    if not DECLARATION_RE.fullmatch(value):
        raise ValueError(f"{label} must be a fully-qualified Lean declaration name")
    return value


def validate_module_name(value: str) -> str:
    if not MODULE_RE.fullmatch(value):
        raise ValueError("module must be a fully-qualified Lean module name")
    return value


def build_module_command(input_modules: Iterable[str]) -> list[str]:
    """Build runtime plus exact inputs before generated files import them.

    `lake env lean Generated.lean` consumes an existing `.olean` and does not
    rebuild a local imported module after its source changes.  Including every
    input module in preflight keeps source-hashed jobs from observing stale
    compiled benchmark declarations.
    """

    modules = sorted({validate_module_name(module) for module in input_modules})
    return ["lake", "build", RUNTIME_MODULE, *modules]


def module_file(lean_root: Path, module: str) -> Path:
    validate_module_name(module)
    path = lean_root / "Reference" / Path(*module.split(".")).with_suffix(".lean")
    if not path.is_file():
        raise ValueError(f"input module is not a local importable module: {module}")
    return path


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def trim_output(value: str, limit: int = 16000) -> str:
    if len(value) <= limit:
        return value
    half = limit // 2
    return value[:half] + "\n... output trimmed ...\n" + value[-half:]


def run_command(
    command: list[str],
    *,
    cwd: Path,
    timeout_seconds: int,
    env_overrides: dict[str, str] | None = None,
    output_limit: int = 16000,
) -> CommandResult:
    started = time.monotonic()
    environment = None
    if env_overrides:
        environment = os.environ.copy()
        environment.update(env_overrides)
    try:
        completed = subprocess.run(
            command,
            cwd=cwd,
            env=environment,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout_seconds,
            check=False,
        )
        return CommandResult(
            command=tuple(command),
            exit_code=completed.returncode,
            stdout=trim_output(completed.stdout, output_limit),
            stderr=trim_output(completed.stderr, output_limit),
            duration_seconds=round(time.monotonic() - started, 3),
        )
    except subprocess.TimeoutExpired as error:
        stdout = error.stdout if isinstance(error.stdout, str) else ""
        stderr = error.stderr if isinstance(error.stderr, str) else ""
        return CommandResult(
            command=tuple(command),
            exit_code=124,
            stdout=trim_output(stdout, output_limit),
            stderr=trim_output(stderr, output_limit),
            duration_seconds=round(time.monotonic() - started, 3),
            timed_out=True,
        )


def _imports(input_module: str, extra_imports: Iterable[str] = ()) -> str:
    validate_module_name(input_module)
    modules = [RUNTIME_MODULE, input_module]
    for module in extra_imports:
        validate_module_name(module)
        if module not in modules:
            modules.append(module)
    return "".join(f"import {module}\n" for module in modules)


def _authoring_imports(input_module: str) -> str:
    """Import only the ABI needed by staged candidate checkpoints.

    The full runtime also imports the aggregate registry, probe, and resolver.
    Those are needed for discovery and final reconstruction, but not while a
    job-local declaration is checked behind its own axiom gate.
    """

    validate_module_name(input_module)
    return "".join(
        f"import {module}\n"
        for module in (AUTHORING_MODULE, AXIOM_GATE_MODULE, input_module)
    )


def _model_authoring_imports(context_module: str) -> str:
    validate_module_name(context_module)
    return "".join(
        f"import {module}\n"
        for module in (MODEL_AUTHORING_MODULE, AXIOM_GATE_MODULE, context_module)
    )


def _goal_imports(input_module: str) -> str:
    validate_module_name(input_module)
    return (
        "import ComplexityReduction.Agent.Hardness.InputGate\n"
        f"import {input_module}\n"
    )


def build_input_observation_source(
    *,
    input_module: str,
    nonce: str,
    input_declaration: str,
) -> str:
    """Build one read-only input-inspection command over compiled declarations."""

    return build_input_observation_batch_source(
        input_module=input_module,
        requests=((nonce, input_declaration),),
    )


def build_input_observation_batch_source(
    *,
    input_module: str,
    requests: Iterable[tuple[str, str]],
) -> str:
    """Build multiple nonce-isolated observations in one Lean process."""

    validate_module_name(input_module)
    validated: list[tuple[str, str]] = []
    seen_nonces: set[str] = set()
    for nonce, input_declaration in requests:
        if not nonce or nonce in seen_nonces:
            raise ValueError("input observation nonces must be non-empty and unique")
        seen_nonces.add(nonce)
        declaration = validate_declaration_name(
            input_declaration,
            label="input declaration",
        )
        validated.append((nonce, declaration))
    if not validated:
        raise ValueError("at least one input observation request is required")
    commands = "".join(
        f"#hardness_inspect_input {json.dumps(nonce, ensure_ascii=True)} {declaration}\n"
        for nonce, declaration in validated
    )
    return (
        f"import {INPUT_INSPECTION_MODULE}\n"
        f"import {input_module}\n\n"
        f"{commands}"
    )


def build_problem_catalog_source(
    *,
    nonce: str,
    additional_modules: Sequence[str] = (),
    registered_only: bool = False,
) -> str:
    """Build one fingerprint-coherent catalog export over the compiled library."""

    if not nonce:
        raise ValueError("problem catalog nonce must be non-empty")
    modules = tuple(
        dict.fromkeys(validate_module_name(module) for module in additional_modules)
    )
    additional_imports = "".join(f"import {module}\n" for module in modules)
    export_command = (
        "#hardness_export_registered_problem_catalog"
        if registered_only
        else "#hardness_export_problem_catalog"
    )
    return (
        f"import {PROBLEM_CATALOG_MODULE}\n"
        f"import {TARGET_CATALOG_MODULE}\n"
        f"{additional_imports}\n"
        f"{export_command} {json.dumps(nonce, ensure_ascii=True)}\n"
        f"#hardness_export_target_catalog {json.dumps(nonce, ensure_ascii=True)}\n"
    )


def build_goal_source(
    *,
    input_module: str,
    source_declaration: str,
    membership_declaration: str | None,
    target_declaration: str | None = None,
) -> str:
    source = validate_declaration_name(source_declaration, label="source")
    membership = (
        validate_declaration_name(membership_declaration, label="membership")
        if membership_declaration
        else None
    )
    target = (
        validate_declaration_name(target_declaration, label="target")
        if target_declaration
        else None
    )
    membership_check = ""
    if membership:
        membership_check = (
            "example : ComplexityReduction.Certificate.NativeTMInNP "
            f"{source} := {membership}\n"
        )
    target_check = ""
    if target:
        target_check = (
            "example : ComplexityReduction.Encoding.PresentedProblem := "
            f"{target}\n"
        )
    return f"""{_goal_imports(input_module)}
namespace ComplexityReduction.Agent.Hardness.GeneratedGoal

noncomputable section

example : ComplexityReduction.Encoding.PresentedProblem := {source}
{target_check}{membership_check}
end

end ComplexityReduction.Agent.Hardness.GeneratedGoal
"""


def build_probe_source(
    *,
    input_module: str,
    nonce: str,
    source_declaration: str,
    membership_declaration: str | None,
    objective: str,
    target_declaration: str | None,
    catalog_mode: str = FULL_CATALOG,
    extra_imports: Iterable[str] = (),
) -> str:
    source = validate_declaration_name(source_declaration, label="source")
    target = (
        validate_declaration_name(target_declaration, label="target")
        if target_declaration
        else None
    )
    membership_root = ""
    if membership_declaration:
        membership = validate_declaration_name(membership_declaration, label="membership")
        if objective in {"reduce_to", "reduce_to_known_np"}:
            membership_root = (
                "namespace ComplexityReduction.Agent.Hardness.GeneratedProbe\n"
                "example : ComplexityReduction.Certificate.NativeTMInNP "
                f"{source} := {membership}\n"
                "@[complexity_reduction_ir_typed_edge, "
                "complexity_reduction_ir_component_ingress]\n"
                "noncomputable def nativeCookLevinRoot : "
                "ComplexityReduction.Certificate.CertifiedReduction "
                f"{source} ComplexityReduction.Certificate.NativeCookLevin.canonicalThreeSAT :=\n"
                "  ComplexityReduction.Certificate.NativeCookLevin.reduce "
                f"{membership}\n"
                "end ComplexityReduction.Agent.Hardness.GeneratedProbe\n\n"
            )
        else:
            membership_root = (
                "namespace ComplexityReduction.Agent.Hardness.GeneratedProbe\n"
                "@[complexity_reduction_ir_typed_native_membership]\n"
                "theorem providedNativeMembership : "
                "ComplexityReduction.Certificate.NativeTMInNP "
                f"{source} := {membership}\n"
                "end ComplexityReduction.Agent.Hardness.GeneratedProbe\n\n"
            )
    nonce_literal = json.dumps(nonce, ensure_ascii=True)
    if catalog_mode not in CATALOG_MODES:
        raise ValueError(f"unsupported typed catalog mode: {catalog_mode}")
    if objective == "reduce_to":
        if not target:
            raise ValueError("reduce-to requires --target")
        probe_commands = {
            FULL_CATALOG: "#hardness_probe_to",
            FLAT_API_CATALOG: "#hardness_probe_to_flat",
            IR_COMPONENTS_CATALOG: "#hardness_probe_to_ir",
            # The Stage-F component catalog is filtered in Python from the
            # complete fingerprint-bound Lean inventory so it remains a strict
            # query superset of flat_api.
            COMPONENT_CATALOG: "#hardness_probe_to",
        }
        command = f"{probe_commands[catalog_mode]} {nonce_literal} {source} {target}"
    elif objective == "reduce_to_known_np" and target:
        if catalog_mode != FULL_CATALOG:
            raise ValueError(
                "non-full catalog modes currently require fixed-target reduce-to"
            )
        command = f"#hardness_probe_to_known_np {nonce_literal} {source} {target}"
    elif objective == "reduce_to_known_np":
        if catalog_mode != FULL_CATALOG:
            raise ValueError(
                "non-full catalog modes currently require fixed-target reduce-to"
            )
        command = f"#hardness_probe {nonce_literal} {source}"
    elif objective == "prove_in_np":
        if catalog_mode != FULL_CATALOG:
            raise ValueError(
                "non-full catalog modes currently require fixed-target reduce-to"
            )
        if target:
            raise ValueError("prove-in-np uses --source as its exact problem and accepts no target")
        command = f"#hardness_probe_in_np {nonce_literal} {source}"
    elif objective == "prove_np_complete":
        if catalog_mode != FULL_CATALOG:
            raise ValueError(
                "non-full catalog modes currently require fixed-target reduce-to"
            )
        if target:
            raise ValueError(
                "prove-np-complete uses --source as its exact problem and accepts no target"
            )
        command = f"#hardness_probe_np_complete {nonce_literal} {source}"
    else:
        raise ValueError(f"objective is not implemented in the current runtime: {objective}")
    return f"{_imports(input_module, extra_imports)}\n{membership_root}{command}\n"


def build_artifact_source(
    *,
    input_module: str,
    source_declaration: str,
    membership_declaration: str | None,
    objective: str,
    route: RouteCandidate,
    extra_imports: Iterable[str] = (),
) -> str:
    if not isinstance(route, RouteCandidate):
        raise TypeError(
            "artifact emission requires a validated RouteCandidate, not HardnessGap metadata"
        )
    source = validate_declaration_name(source_declaration, label="source")
    target = validate_declaration_name(route.target_declaration, label="target")
    if len(route.atoms) != len(route.roles):
        raise ValueError("validated route must retain one component role per atom")
    if route.final_composition_edges != sum(
        1 for role in route.roles if role == "finalComposition"
    ):
        raise ValueError("validated route final-composition count does not match its roles")

    selected_atoms = tuple(
        validate_declaration_name(atom, label="route atom") for atom in route.atoms
    )
    if membership_declaration:
        probe_root = (
            "ComplexityReduction.Agent.Hardness.GeneratedProbe.nativeCookLevinRoot"
        )
        artifact_root = (
            "ComplexityReduction.Agent.Hardness.GeneratedArtifact.nativeCookLevinRoot"
        )
        selected_atoms = tuple(
            artifact_root if atom == probe_root else atom for atom in selected_atoms
        )

    if selected_atoms:
        selected_path_term = (
            "ComplexityReduction.Certificate.CertifiedPath.step " + selected_atoms[0]
        )
        for atom in selected_atoms[1:]:
            selected_path_term = (
                "ComplexityReduction.Certificate.CertifiedPath.cons\n"
                f"      ({selected_path_term})\n"
                f"      {atom}"
            )
    else:
        selected_path_term = (
            "ComplexityReduction.Certificate.CertifiedPath.refl " + source
        )
    if objective == "reduce_to":
        if route.evidence_kind != "reduction":
            raise ValueError("reduce-to artifact requires reduction evidence")
        objective_term = f".reduceTo {source} {target}"
    elif objective == "reduce_to_known_np":
        if not route.membership_declaration:
            raise ValueError("known-NP artifact route has no native membership declaration")
        if route.evidence_kind not in {"reduction", "reduction_with_membership"}:
            raise ValueError("known-NP artifact requires reduction-plus-membership evidence")
        objective_term = f".reduceToKnownNP {source} {target}"
    elif objective == "prove_in_np":
        if route.evidence_kind != "native_membership":
            raise ValueError("prove-in-np artifact requires exact native-membership evidence")
        objective_term = f".proveInNP {source}"
    elif objective == "prove_np_complete":
        if route.evidence_kind not in {
            "registered_completeness",
            "transported_completeness",
        }:
            raise ValueError("prove-np-complete artifact requires exact native completeness")
        objective_term = f".proveNPComplete {source}"
    else:
        raise ValueError(f"objective is not implemented in the current runtime: {objective}")
    membership_root = ""
    audited_declarations = [
        "ComplexityReduction.Agent.Hardness.GeneratedArtifact.result"
    ]
    if membership_declaration:
        membership = validate_declaration_name(membership_declaration, label="membership")
        if objective in {"reduce_to", "reduce_to_known_np"}:
            membership_root = (
                "@[complexity_reduction_ir_typed_edge, "
                "complexity_reduction_ir_component_ingress]\n"
                "noncomputable def nativeCookLevinRoot : "
                "ComplexityReduction.Certificate.CertifiedReduction "
                f"{source} ComplexityReduction.Certificate.NativeCookLevin.canonicalThreeSAT :=\n"
                "  ComplexityReduction.Certificate.NativeCookLevin.reduce "
                f"{membership}\n\n"
            )
            audited_declarations.insert(
                0, "ComplexityReduction.Agent.Hardness.GeneratedArtifact.nativeCookLevinRoot"
            )
        else:
            membership_root = (
                "@[complexity_reduction_ir_typed_native_membership]\n"
                "theorem providedNativeMembership : "
                "ComplexityReduction.Certificate.NativeTMInNP "
                f"{source} := {membership}\n\n"
            )
            audited_declarations.insert(
                0,
                "ComplexityReduction.Agent.Hardness.GeneratedArtifact.providedNativeMembership",
            )
    result_projection = ""
    selected_path = ""
    result_body = "  by_hardness_resolver"
    if objective in {"reduce_to", "reduce_to_known_np"}:
        selected_path = (
            "noncomputable def selectedPath : "
            "ComplexityReduction.Certificate.CertifiedPath "
            f"{source} {target} :=\n"
            f"  {selected_path_term}\n\n"
        )
        audited_declarations.insert(
            0, "ComplexityReduction.Agent.Hardness.GeneratedArtifact.selectedPath"
        )
        if objective == "reduce_to":
            result_body = (
                "  ComplexityReduction.Protocol.TypedAutoReductionResult.reduceToPath\n"
                "    policy (by rfl) selectedPath"
            )
        else:
            membership_name = validate_declaration_name(
                route.membership_declaration or "", label="route membership"
            )
            result_body = (
                "  ComplexityReduction.Protocol.TypedAutoReductionResult.reduceToKnownNPPath\n"
                f"    policy (by rfl) selectedPath {membership_name}"
            )
    if objective == "prove_in_np":
        result_projection = (
            "\nnoncomputable def membershipEvidence : "
            f"ComplexityReduction.Certificate.NativeTMInNP {source} :=\n"
            "  ComplexityReduction.Protocol.TypedAutoReductionResult."
            "extractNativeMembership result\n"
        )
        audited_declarations.append(
            "ComplexityReduction.Agent.Hardness.GeneratedArtifact.membershipEvidence"
        )
    elif objective == "prove_np_complete":
        result_projection = (
            "\nnoncomputable def completenessEvidence : "
            f"ComplexityReduction.Certificate.NativeTMNPComplete {source} :=\n"
            "  ComplexityReduction.Protocol.TypedAutoReductionResult."
            "extractNativeCompleteness result\n"
        )
        audited_declarations.append(
            "ComplexityReduction.Agent.Hardness.GeneratedArtifact.completenessEvidence"
        )
    audit = ",\n  ".join(audited_declarations)
    return f"""{_imports(input_module, extra_imports)}
namespace ComplexityReduction.Agent.Hardness.GeneratedArtifact

noncomputable section

{membership_root}def policy : ComplexityReduction.Protocol.AutoReductionTrustPolicy :=
  {{ presentation := .exactUser, requireNativeNP := true }}

def request : ComplexityReduction.Protocol.TypedAutoReductionRequest where
  source := .fromPresented {source}
  policy := policy
  objective := {objective_term}

{selected_path}@[complexity_reduction_ir_typed_final_result]
noncomputable def result : ComplexityReduction.Protocol.TypedAutoReductionResult request :=
{result_body}
{result_projection}

end

end ComplexityReduction.Agent.Hardness.GeneratedArtifact

assert_standard_axioms
  {audit}
"""


def _role_attribute(role: str) -> str:
    attributes = {
        "ingress": "complexity_reduction_ir_component_ingress",
        "sharedGadget": "complexity_reduction_ir_component_shared_gadget",
        "egress": "complexity_reduction_ir_component_egress",
        "finalComposition": "complexity_reduction_ir_component_final_composition",
    }
    try:
        return attributes[role]
    except KeyError as error:
        raise ValueError(f"unsupported candidate component role: {role}") from error


def build_closed_family_candidate_source(
    *,
    input_module: str,
    candidate_module: str,
    candidate_declaration: str,
    source_declaration: str,
    target_declaration: str,
    family_declaration: str,
    argument_declarations: Iterable[str],
    role: str,
) -> CandidateSource:
    validate_module_name(candidate_module)
    candidate = validate_declaration_name(candidate_declaration, label="candidate")
    expected_candidate = f"{candidate_module}.capability"
    if candidate != expected_candidate:
        raise ValueError(f"candidate declaration must be {expected_candidate}")
    source = validate_declaration_name(source_declaration, label="source")
    target = validate_declaration_name(target_declaration, label="target")
    family = validate_declaration_name(family_declaration, label="family")
    arguments = [
        validate_declaration_name(argument, label="family argument")
        for argument in argument_declarations
    ]
    application = " ".join((f"@{family}", *arguments))
    role_attribute = _role_attribute(role)
    fixed_header = f"""{_imports(input_module)}
namespace {candidate_module}

@[complexity_reduction_ir_typed_edge, {role_attribute}]
noncomputable def capability :
    ComplexityReduction.Certificate.CertifiedReduction {source} {target} :=
{EDITABLE_BODY_BEGIN}"""
    editable_body = f"  {application}\n"
    fixed_footer = f"""{EDITABLE_BODY_END}
end {candidate_module}

assert_standard_axioms {candidate}
"""
    return CandidateSource(
        source=fixed_header + editable_body + fixed_footer,
        fixed_header=fixed_header,
        editable_body=editable_body,
        fixed_footer=fixed_footer,
    )


def _bundle_declarations(
    *, candidate_module: str, candidate_declaration: str, route_declaration: str
) -> tuple[str, str]:
    validate_module_name(candidate_module)
    candidate = validate_declaration_name(candidate_declaration, label="candidate")
    route = validate_declaration_name(route_declaration, label="candidate route")
    expected_candidate = f"{candidate_module}.capability"
    expected_route = f"{candidate_module}.route"
    if candidate != expected_candidate:
        raise ValueError(f"candidate declaration must be {expected_candidate}")
    if route != expected_route:
        raise ValueError(f"candidate route declaration must be {expected_route}")
    return candidate, route


def build_lawful_presentation_candidate_source(
    *,
    input_module: str,
    candidate_module: str,
    candidate_declaration: str,
    route_declaration: str,
    source_declaration: str,
    target_declaration: str,
    provider_declaration: str,
    role: str,
) -> CandidateSource:
    candidate, route = _bundle_declarations(
        candidate_module=candidate_module,
        candidate_declaration=candidate_declaration,
        route_declaration=route_declaration,
    )
    source = validate_declaration_name(source_declaration, label="source")
    target = validate_declaration_name(target_declaration, label="target")
    provider = validate_declaration_name(provider_declaration, label="template provider")
    role_attribute = _role_attribute(role)
    fixed_header = f"""{_imports(input_module)}
namespace {candidate_module}

@[complexity_reduction_ir_typed_presentation]
def capability :
    ComplexityReduction.Encoding.StructuralRepresentationCertificate
      {source}.representation.encodedType {source}.representation.representation :=
{EDITABLE_BODY_BEGIN}"""
    editable_body = f"  {provider}.toStructuralCertificate\n"
    fixed_footer = f"""{EDITABLE_BODY_END}
@[complexity_reduction_ir_typed_edge, {role_attribute}]
noncomputable def route :
    ComplexityReduction.Certificate.CertifiedReduction {source} {target} :=
  {provider}.toReduction capability

end {candidate_module}

assert_standard_axioms
  {candidate},
  {route}
"""
    return CandidateSource(
        source=fixed_header + editable_body + fixed_footer,
        fixed_header=fixed_header,
        editable_body=editable_body,
        fixed_footer=fixed_footer,
    )


def build_primitive_admission_candidate_source(
    *,
    input_module: str,
    candidate_module: str,
    candidate_declaration: str,
    route_declaration: str,
    source_declaration: str,
    target_declaration: str,
    provider_declaration: str,
    role: str,
) -> CandidateSource:
    candidate, route = _bundle_declarations(
        candidate_module=candidate_module,
        candidate_declaration=candidate_declaration,
        route_declaration=route_declaration,
    )
    source = validate_declaration_name(source_declaration, label="source")
    target = validate_declaration_name(target_declaration, label="target")
    provider = validate_declaration_name(provider_declaration, label="template provider")
    role_attribute = _role_attribute(role)
    fixed_header = f"""{_imports(input_module)}
namespace {candidate_module}

@[complexity_reduction_ir_typed_primitive]
noncomputable def capability :
    ComplexityReduction.Program.Primitive
      {source}.representation {target}.representation :=
{EDITABLE_BODY_BEGIN}"""
    editable_body = f"  {provider}.toPrimitive\n"
    fixed_footer = f"""{EDITABLE_BODY_END}
@[complexity_reduction_ir_typed_edge, {role_attribute}]
noncomputable def route :
    ComplexityReduction.Certificate.CertifiedReduction {source} {target} :=
  {provider}.toReduction capability rfl

end {candidate_module}

assert_standard_axioms
  {candidate},
  {route}
"""
    return CandidateSource(
        source=fixed_header + editable_body + fixed_footer,
        fixed_header=fixed_header,
        editable_body=editable_body,
        fixed_footer=fixed_footer,
    )


def program_indexed_reduction_stage_modules(candidate_base_module: str) -> dict[str, str]:
    base = validate_module_name(candidate_base_module)
    suffixes = {
        "executable": "Executable",
        "executable_direct_tm": "ExecutableDirectTM",
        "primitive": "Primitive",
        "program": "Program",
        "semantic_proof": "SemanticProof",
        "direct_tm": "DirectTM",
        "certified_reduction": "Reduction",
    }
    return {stage: f"{base}.{suffixes[stage]}" for stage in PROGRAM_INDEXED_REDUCTION_STAGES}


def _staged_candidate(
    *, stage: str, module: str, fixed_header: str, editable_body: str, fixed_footer: str
) -> CandidateStageSource:
    return CandidateStageSource(
        stage=stage,
        module=module,
        declaration=f"{module}.capability",
        candidate=CandidateSource(
            source=fixed_header + editable_body + fixed_footer,
            fixed_header=fixed_header,
            editable_body=editable_body,
            fixed_footer=fixed_footer,
        ),
    )


def build_program_indexed_reduction_candidate_sources(
    *,
    input_module: str,
    candidate_base_module: str,
    source_declaration: str,
    target_declaration: str,
    provider_declaration: str,
    component_declarations: tuple[str, ...],
    role: str,
    model_semantic_body: bool = False,
) -> tuple[CandidateStageSource, ...]:
    """Build seven independently fenced program-indexed checkpoints.

    Deterministic fixtures provide an executable, its direct-TM witness, and
    an already-proved semantic theorem.  Phase 7 model templates intentionally
    omit that third declaration: the fixed semantic checkpoint starts with an
    incomplete proof body and only that fenced body may be replaced by the
    model-authoring protocol.
    """

    validate_module_name(input_module)
    modules = program_indexed_reduction_stage_modules(candidate_base_module)
    source = validate_declaration_name(source_declaration, label="source")
    target = validate_declaration_name(target_declaration, label="target")
    validate_declaration_name(provider_declaration, label="template provider")
    expected_components = 2 if model_semantic_body else 3
    if len(component_declarations) != expected_components:
        raise ValueError(
            f"program-indexed template requires exactly {expected_components} "
            "component declarations"
        )
    checked_components = tuple(
        validate_declaration_name(value, label=f"template component {index}")
        for index, value in enumerate(component_declarations, start=1)
    )
    executable_provider, executable_tm_provider = checked_components[:2]
    semantic_provider = checked_components[2] if not model_semantic_body else None
    context_module = validate_module_name(executable_provider.rsplit(".", 1)[0])
    first_imports = (
        _model_authoring_imports(context_module)
        if model_semantic_body
        else _authoring_imports(input_module)
    )
    role_attribute = _role_attribute(role)

    executable_module = modules["executable"]
    executable_header = f"""{first_imports}
namespace {executable_module}

def capability :
    {source}.representation.Carrier → {target}.representation.Carrier :=
{EDITABLE_BODY_BEGIN}"""
    executable_body = f"  {executable_provider}\n"
    executable_footer = f"""{EDITABLE_BODY_END}
end {executable_module}

assert_standard_axioms {executable_module}.capability
"""

    executable_tm_module = modules["executable_direct_tm"]
    executable_tm_header = f"""import {executable_module}

namespace {executable_tm_module}

def capability :
    ComplexityReduction.Agent.Hardness.Authoring.ExecutableDirectTMEvidence
      {source} {target} {executable_module}.capability :=
{EDITABLE_BODY_BEGIN}"""
    if model_semantic_body:
        executable_tm_body = (
            "  ComplexityReduction.Agent.Hardness.Authoring."
            "ProgramIndexedModelTemplate.toExecutableDirectTM\n"
            f"    {executable_tm_provider} {executable_module}.capability rfl\n"
        )
    else:
        executable_tm_body = (
            "  ComplexityReduction.Agent.Hardness.Authoring."
            "ProgramIndexedReductionTemplate.toExecutableDirectTM\n"
            f"    {executable_tm_provider} {executable_module}.capability rfl\n"
        )
    executable_tm_footer = f"""{EDITABLE_BODY_END}
end {executable_tm_module}

assert_standard_axioms {executable_tm_module}.capability
"""

    primitive_module = modules["primitive"]
    primitive_header = f"""import {executable_tm_module}

namespace {primitive_module}

@[complexity_reduction_ir_typed_primitive]
noncomputable def capability :
    ComplexityReduction.Program.Primitive
      {source}.representation {target}.representation :=
{EDITABLE_BODY_BEGIN}"""
    if model_semantic_body:
        primitive_body = (
            "  ComplexityReduction.Agent.Hardness.Authoring."
            "ProgramIndexedModelTemplate.toPrimitive\n"
            f"    {executable_module}.capability {executable_tm_module}.capability\n"
        )
    else:
        primitive_body = (
            "  ComplexityReduction.Agent.Hardness.Authoring."
            "ProgramIndexedReductionTemplate.toPrimitive\n"
            f"    {executable_module}.capability {executable_tm_module}.capability\n"
        )
    primitive_footer = f"""{EDITABLE_BODY_END}
end {primitive_module}

assert_standard_axioms {primitive_module}.capability
"""

    program_module = modules["program"]
    program_header = f"""import {primitive_module}

namespace {program_module}

noncomputable def capability :
    ComplexityReduction.Program.PolyProg
      {source}.representation {target}.representation :=
{EDITABLE_BODY_BEGIN}"""
    if model_semantic_body:
        program_body = (
            "  ComplexityReduction.Agent.Hardness.Authoring."
            "ProgramIndexedModelTemplate.toProgram\n"
            f"    {primitive_module}.capability\n"
        )
    else:
        program_body = (
            "  ComplexityReduction.Agent.Hardness.Authoring."
            "ProgramIndexedReductionTemplate.toProgram\n"
            f"    {primitive_module}.capability\n"
        )
    program_footer = f"""{EDITABLE_BODY_END}
end {program_module}

assert_standard_axioms {program_module}.capability
"""

    semantic_module = modules["semantic_proof"]
    semantic_header = f"""import {program_module}

namespace {semantic_module}

def capability :
    ComplexityReduction.Agent.Hardness.Authoring.ProgramSemanticProof
      {source} {target} {program_module}.capability :=
{EDITABLE_BODY_BEGIN}"""
    if model_semantic_body:
        semantic_body = "  by\n    intro input\n"
    else:
        semantic_body = (
            "  ComplexityReduction.Agent.Hardness.Authoring."
            "ProgramIndexedReductionTemplate.toSemanticProof\n"
            f"    {semantic_provider} {program_module}.capability rfl\n"
        )
    semantic_footer = f"""{EDITABLE_BODY_END}
end {semantic_module}

assert_standard_axioms {semantic_module}.capability
"""

    direct_tm_module = modules["direct_tm"]
    direct_tm_header = f"""import {semantic_module}

namespace {direct_tm_module}

def capability :
    ComplexityReduction.Agent.Hardness.Authoring.ProgramDirectTMEvidence
      {source} {target} {program_module}.capability :=
{EDITABLE_BODY_BEGIN}"""
    if model_semantic_body:
        direct_tm_body = (
            "  ComplexityReduction.Agent.Hardness.Authoring."
            "ProgramIndexedModelTemplate.toProgramDirectTM\n"
            f"    {executable_tm_module}.capability {program_module}.capability rfl\n"
        )
    else:
        direct_tm_body = (
            "  ComplexityReduction.Agent.Hardness.Authoring."
            "ProgramIndexedReductionTemplate.toProgramDirectTM\n"
            f"    {program_module}.capability\n"
        )
    direct_tm_footer = f"""{EDITABLE_BODY_END}
end {direct_tm_module}

assert_standard_axioms {direct_tm_module}.capability
"""

    reduction_module = modules["certified_reduction"]
    reduction_header = f"""import {direct_tm_module}

namespace {reduction_module}

@[complexity_reduction_ir_typed_edge, {role_attribute}]
noncomputable def capability :
    ComplexityReduction.Certificate.CertifiedReduction {source} {target} :=
{EDITABLE_BODY_BEGIN}"""
    if model_semantic_body:
        reduction_body = (
            "  ComplexityReduction.Agent.Hardness.Authoring."
            "ProgramIndexedModelTemplate.toReduction\n"
            f"    {program_module}.capability {semantic_module}.capability\n"
        )
    else:
        reduction_body = (
            "  ComplexityReduction.Agent.Hardness.Authoring."
            "ProgramIndexedReductionTemplate.toReduction\n"
            f"    {program_module}.capability {semantic_module}.capability\n"
        )
    reduction_footer = f"""{EDITABLE_BODY_END}
end {reduction_module}

assert_standard_axioms {reduction_module}.capability
"""

    candidates = (
        _staged_candidate(
            stage="executable",
            module=executable_module,
            fixed_header=executable_header,
            editable_body=executable_body,
            fixed_footer=executable_footer,
        ),
        _staged_candidate(
            stage="executable_direct_tm",
            module=executable_tm_module,
            fixed_header=executable_tm_header,
            editable_body=executable_tm_body,
            fixed_footer=executable_tm_footer,
        ),
        _staged_candidate(
            stage="primitive",
            module=primitive_module,
            fixed_header=primitive_header,
            editable_body=primitive_body,
            fixed_footer=primitive_footer,
        ),
        _staged_candidate(
            stage="program",
            module=program_module,
            fixed_header=program_header,
            editable_body=program_body,
            fixed_footer=program_footer,
        ),
        _staged_candidate(
            stage="semantic_proof",
            module=semantic_module,
            fixed_header=semantic_header,
            editable_body=semantic_body,
            fixed_footer=semantic_footer,
        ),
        _staged_candidate(
            stage="direct_tm",
            module=direct_tm_module,
            fixed_header=direct_tm_header,
            editable_body=direct_tm_body,
            fixed_footer=direct_tm_footer,
        ),
        _staged_candidate(
            stage="certified_reduction",
            module=reduction_module,
            fixed_header=reduction_header,
            editable_body=reduction_body,
            fixed_footer=reduction_footer,
        ),
    )
    if tuple(candidate.stage for candidate in candidates) != PROGRAM_INDEXED_REDUCTION_STAGES:
        raise AssertionError("program-indexed reduction stages are out of canonical order")
    return candidates


def native_membership_stage_modules(candidate_base_module: str) -> dict[str, str]:
    base = validate_module_name(candidate_base_module)
    suffixes = {
        "verifier": "Verifier",
        "witness_presentation": "WitnessPresentation",
        "discipline": "Discipline",
        "native_membership": "Membership",
    }
    return {stage: f"{base}.{suffixes[stage]}" for stage in NATIVE_MEMBERSHIP_STAGES}


def build_native_membership_candidate_sources(
    *,
    input_module: str,
    candidate_base_module: str,
    problem_declaration: str,
    provider_declaration: str,
    component_declarations: tuple[str, ...],
) -> tuple[CandidateStageSource, ...]:
    """Build four independently fenced Phase-6 membership checkpoints."""

    validate_module_name(input_module)
    modules = native_membership_stage_modules(candidate_base_module)
    problem = validate_declaration_name(problem_declaration, label="problem")
    validate_declaration_name(provider_declaration, label="template provider")
    if len(component_declarations) != 3:
        raise ValueError("native-membership template requires exactly three component declarations")
    verifier_provider, witness_provider, discipline_provider = (
        validate_declaration_name(value, label=f"template component {index}")
        for index, value in enumerate(component_declarations, start=1)
    )

    verifier_module = modules["verifier"]
    verifier_header = f"""{_authoring_imports(input_module)}
namespace {verifier_module}

@[complexity_reduction_ir_typed_verifier]
noncomputable def capability :
    ComplexityReduction.Certificate.CertifiedVerifier {problem} :=
{EDITABLE_BODY_BEGIN}"""
    verifier_body = (
        "  ComplexityReduction.Agent.Hardness.Authoring."
        "NativeMembershipTemplate.toVerifier\n"
        f"    {verifier_provider}\n"
    )
    verifier_footer = f"""{EDITABLE_BODY_END}
end {verifier_module}

assert_standard_axioms {verifier_module}.capability
"""

    witness_module = modules["witness_presentation"]
    witness_header = f"""import {verifier_module}

namespace {witness_module}

@[complexity_reduction_ir_typed_presentation]
def capability :
    ComplexityReduction.Encoding.StructuralRepresentationCertificate
      {verifier_module}.capability.witness.encodedType
      {verifier_module}.capability.witness.representation :=
{EDITABLE_BODY_BEGIN}"""
    witness_body = (
        "  ComplexityReduction.Agent.Hardness.Authoring."
        "NativeMembershipTemplate.toWitnessPresentation\n"
        f"    {witness_provider} {verifier_module}.capability rfl\n"
    )
    witness_footer = f"""{EDITABLE_BODY_END}
end {witness_module}

assert_standard_axioms {witness_module}.capability
"""

    discipline_module = modules["discipline"]
    discipline_header = f"""import {witness_module}

namespace {discipline_module}

@[complexity_reduction_ir_typed_verifier_discipline]
noncomputable def capability :
    ComplexityReduction.Certificate.CertifiedVerifierEncodingDiscipline
      {verifier_module}.capability :=
{EDITABLE_BODY_BEGIN}"""
    discipline_body = (
        "  ComplexityReduction.Agent.Hardness.Authoring."
        "NativeMembershipTemplate.toDiscipline\n"
        f"    {discipline_provider} {verifier_module}.capability rfl\n"
    )
    discipline_footer = f"""{EDITABLE_BODY_END}
end {discipline_module}

assert_standard_axioms {discipline_module}.capability
"""

    membership_module = modules["native_membership"]
    membership_header = f"""import {discipline_module}

namespace {membership_module}

@[complexity_reduction_ir_typed_native_membership]
theorem capability : ComplexityReduction.Certificate.NativeTMInNP {problem} :=
{EDITABLE_BODY_BEGIN}"""
    membership_body = (
        "  ComplexityReduction.Agent.Hardness.Authoring."
        "NativeMembershipTemplate.toNativeMembership\n"
        f"    {verifier_module}.capability {witness_module}.capability\n"
        f"    {discipline_module}.capability\n"
    )
    membership_footer = f"""{EDITABLE_BODY_END}
end {membership_module}

assert_standard_axioms {membership_module}.capability
"""

    candidates = (
        _staged_candidate(
            stage="verifier",
            module=verifier_module,
            fixed_header=verifier_header,
            editable_body=verifier_body,
            fixed_footer=verifier_footer,
        ),
        _staged_candidate(
            stage="witness_presentation",
            module=witness_module,
            fixed_header=witness_header,
            editable_body=witness_body,
            fixed_footer=witness_footer,
        ),
        _staged_candidate(
            stage="discipline",
            module=discipline_module,
            fixed_header=discipline_header,
            editable_body=discipline_body,
            fixed_footer=discipline_footer,
        ),
        _staged_candidate(
            stage="native_membership",
            module=membership_module,
            fixed_header=membership_header,
            editable_body=membership_body,
            fixed_footer=membership_footer,
        ),
    )
    if tuple(candidate.stage for candidate in candidates) != NATIVE_MEMBERSHIP_STAGES:
        raise AssertionError("native-membership stages are out of canonical order")
    return candidates


def assert_candidate_source_fences(actual: str, expected: CandidateSource) -> None:
    begin_position = actual.find(EDITABLE_BODY_BEGIN)
    end_position = actual.find(EDITABLE_BODY_END)
    if begin_position < 0 or end_position < 0 or end_position < begin_position:
        raise ValueError("candidate source is missing its fixed editable-body fences")
    actual_header_end = begin_position + len(EDITABLE_BODY_BEGIN)
    actual_header = actual[:actual_header_end]
    actual_footer = actual[end_position:]
    if actual_header != expected.fixed_header:
        raise ValueError("candidate fixed header changed outside the editable region")
    if actual_footer != expected.fixed_footer:
        raise ValueError("candidate fixed footer changed outside the editable region")


def build_candidate_validation_source(
    *,
    candidate_module: str,
    nonce: str,
    candidate_declaration: str,
    route_declaration: str | None = None,
    template_kind: str = "closed_family_instantiation",
    stage_declarations: Mapping[str, str] | None = None,
    source_declaration: str,
    target_declaration: str,
) -> str:
    module = validate_module_name(candidate_module)
    candidate = validate_declaration_name(candidate_declaration, label="candidate")
    source = validate_declaration_name(source_declaration, label="source")
    target = validate_declaration_name(target_declaration, label="target")
    nonce_literal = json.dumps(nonce, ensure_ascii=True)
    if template_kind == "closed_family_instantiation":
        command = f"#hardness_validate_candidate {nonce_literal} {candidate} {source} {target}"
    elif template_kind in {"program_indexed_reduction", "program_indexed_model"}:
        if stage_declarations is None:
            raise ValueError("program-indexed validation requires every stage declaration")
        required = {
            "executable",
            "executable_direct_tm",
            "primitive",
            "program",
            "semantic_proof",
            "direct_tm",
            "certified_reduction",
        }
        if set(stage_declarations) != required:
            raise ValueError("program-indexed validation received an incomplete stage map")
        declarations = {
            stage: validate_declaration_name(value, label=f"{stage} declaration")
            for stage, value in stage_declarations.items()
        }
        command = (
            f"#hardness_validate_program_reduction_candidate {nonce_literal} "
            f"{declarations['executable']} {declarations['executable_direct_tm']} "
            f"{declarations['primitive']} {declarations['program']} "
            f"{declarations['semantic_proof']} {declarations['direct_tm']} "
            f"{declarations['certified_reduction']} {source} {target}"
        )
    elif template_kind == "native_membership":
        if stage_declarations is None:
            raise ValueError("native-membership validation requires every stage declaration")
        required = set(NATIVE_MEMBERSHIP_STAGES)
        if set(stage_declarations) != required:
            raise ValueError("native-membership validation received an incomplete stage map")
        declarations = {
            stage: validate_declaration_name(value, label=f"{stage} declaration")
            for stage, value in stage_declarations.items()
        }
        command = (
            f"#hardness_validate_native_membership_candidate {nonce_literal} "
            f"{declarations['verifier']} {declarations['witness_presentation']} "
            f"{declarations['discipline']} {declarations['native_membership']} {source}"
        )
    else:
        if route_declaration is None:
            raise ValueError("candidate bundle validation requires a route declaration")
        route = validate_declaration_name(route_declaration, label="candidate route")
        commands = {
            "lawful_presentation": "#hardness_validate_lawful_candidate",
            "primitive_admission": "#hardness_validate_primitive_candidate",
        }
        try:
            validation_command = commands[template_kind]
        except KeyError as error:
            raise ValueError(f"unsupported candidate template kind: {template_kind}") from error
        command = (
            f"{validation_command} {nonce_literal} {candidate} {route} {source} {target}"
        )
    return (
        f"import {AUTHORING_MODULE}\n"
        f"import {module}\n\n"
        f"{command}\n"
    )


def assert_generated_source_is_safe(source: str) -> None:
    match = BANNED_SOURCE_RE.search(source)
    if match:
        raise ValueError(f"generated source contains forbidden token: {match.group(0)}")
    if any(marker in source for marker in ORACLE_SOURCE_MARKERS):
        raise ValueError("generated source references a quarantined oracle or legacy module")
