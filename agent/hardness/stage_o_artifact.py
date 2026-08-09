"""Lean source generation and independent authority checks for Stage O."""

from __future__ import annotations

import hashlib
import shutil
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .lean_runner import run_command, validate_declaration_name, validate_module_name
from .models import CommandResult


def _module_namespace(module: str) -> str:
    validate_module_name(module)
    return module.rsplit(".", 1)[0]


def build_producer_capability_source(*, module: str, declaration_name: str = "capability") -> str:
    namespace = _module_namespace(module)
    if not declaration_name or "." in declaration_name:
        raise ValueError("declaration_name must be one local Lean identifier")
    declaration = f"{namespace}.{declaration_name}"
    return f"""import Benchmark.Hardness.Inputs.StageO.Inputs
import ComplexityReduction.AxiomGate
import ComplexityReduction.Routes.ThreeSATToClique.Unified

namespace {namespace}

open ComplexityReduction
open ComplexityReduction.Certificate

noncomputable def {declaration_name} :
    CertifiedReduction
      Benchmark.Hardness.Inputs.StageO.Inputs.capabilityProducerSource
      Benchmark.Hardness.Inputs.StageO.Inputs.capabilityProducerTarget :=
  Routes.ThreeSATToClique.sharedGadget

end {namespace}

assert_standard_axioms {declaration}
"""


def build_final_artifact_source(
    *, published_module: str, published_declaration: str, namespace: str
) -> str:
    validate_module_name(published_module)
    validate_declaration_name(published_declaration, label="published declaration")
    validate_module_name(namespace)
    return f"""import Benchmark.Hardness.Inputs.StageO.Regression
import ComplexityReduction.Protocol.Result
import {published_module}

namespace {namespace}

open ComplexityReduction
open ComplexityReduction.Certificate
open ComplexityReduction.Protocol

noncomputable def promotedProducerCapability :
    CertifiedReduction
      Benchmark.Hardness.Inputs.StageO.Inputs.capabilityProducerSource
      Benchmark.Hardness.Inputs.StageO.Inputs.capabilityProducerTarget :=
  {published_declaration}

noncomputable def consumerCompleteness :
    NativeTMNPComplete Benchmark.Hardness.Inputs.StageO.Inputs.capabilityConsumerProblem :=
  CompletenessTransport.alongPath
    NativeCookLevin.canonicalThreeSATNativeCompleteness
    (CertifiedPath.step promotedProducerCapability)
    Problems.Karp21.CliqueNativeVerifier.nativeTMInNP

def policy : AutoReductionTrustPolicy :=
  {{ presentation := .exactUser, requireNativeNP := true }}

noncomputable def consumerResult : TypedAutoReductionResult
    {{ source := .fromPresented
         Benchmark.Hardness.Inputs.StageO.Inputs.capabilityConsumerProblem,
       policy := policy,
       objective := .proveNPComplete
         Benchmark.Hardness.Inputs.StageO.Inputs.capabilityConsumerProblem }} :=
  TypedAutoReductionResult.proveNPComplete policy (by rfl) consumerCompleteness

#check Benchmark.Hardness.Inputs.StageO.Regression.predicateAdapter_exact
#check Benchmark.Hardness.Inputs.StageO.Regression.parameterizedPredicateThree_exact
#check Benchmark.Hardness.Inputs.StageO.Regression.twoGapPresentation_exact
#check Benchmark.Hardness.Inputs.StageO.Regression.fixedTargetRoute
#check Benchmark.Hardness.Inputs.StageO.Regression.autoTargetCompleteness
#check Benchmark.Hardness.Inputs.StageO.Regression.predicateAdapterRoute
#check Benchmark.Hardness.Inputs.StageO.Regression.parameterizedMembership
#check Benchmark.Hardness.Inputs.StageO.Regression.twoGapPresentationRoute
#check Benchmark.Hardness.Inputs.StageO.Regression.twoGapCheckerDirectTM
#check Benchmark.Hardness.Inputs.StageO.Regression.twoGapCheckerMembership
#check Benchmark.Hardness.Inputs.StageO.Regression.twoGapCheckerCompleteness

end {namespace}

assert_standard_axioms
  {namespace}.promotedProducerCapability,
  {namespace}.consumerCompleteness,
  {namespace}.consumerResult
"""


@dataclass(frozen=True)
class StageOArtifactExecution:
    producer_compile: CommandResult
    final_combined_lean: CommandResult
    replay_producer_compile: CommandResult
    release_replay: CommandResult
    producer_source_sha256: str
    final_source_sha256: str
    replay_source_sha256: str

    @property
    def verified(self) -> bool:
        return all(
            command.exit_code == 0 and not command.timed_out
            for command in (
                self.producer_compile,
                self.final_combined_lean,
                self.replay_producer_compile,
                self.release_replay,
            )
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "verified": self.verified,
            "producer_compile": self.producer_compile.to_dict(),
            "final_combined_lean": self.final_combined_lean.to_dict(),
            "replay_producer_compile": self.replay_producer_compile.to_dict(),
            "release_replay": self.release_replay.to_dict(),
            "producer_source_sha256": self.producer_source_sha256,
            "final_source_sha256": self.final_source_sha256,
            "replay_source_sha256": self.replay_source_sha256,
        }


def _sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _compile_module(
    *, lean_root: Path, source_root: Path, build_root: Path, module: str, timeout_seconds: int
) -> CommandResult:
    source = source_root / Path(*module.split(".")).with_suffix(".lean")
    output = build_root / Path(*module.split(".")).with_suffix(".olean")
    output.parent.mkdir(parents=True, exist_ok=True)
    return run_command(
        ["lake", "env", "lean", "-R", str(source_root), "-o", str(output), str(source)],
        cwd=lean_root,
        timeout_seconds=timeout_seconds,
    )


def _base_lean_path(*, lean_root: Path, timeout_seconds: int) -> str:
    result = run_command(
        ["lake", "env", "printenv", "LEAN_PATH"],
        cwd=lean_root,
        timeout_seconds=timeout_seconds,
    )
    if result.exit_code != 0 or not result.stdout.strip():
        raise RuntimeError("cannot resolve Lake LEAN_PATH")
    return result.stdout.strip()


def _compile_final(
    *, lean_root: Path, generated_build_root: Path, source_file: Path, timeout_seconds: int
) -> CommandResult:
    lean_path = f"{generated_build_root}:{_base_lean_path(lean_root=lean_root, timeout_seconds=timeout_seconds)}"
    return run_command(
        ["lake", "env", "env", f"LEAN_PATH={lean_path}", "lean", str(source_file)],
        cwd=lean_root,
        timeout_seconds=timeout_seconds,
    )


def execute_stage_o_artifacts(
    *,
    lean_root: Path,
    output_root: Path,
    published_source_root: Path,
    published_module: str,
    published_declaration: str,
    timeout_seconds: int,
) -> StageOArtifactExecution:
    lean_root = lean_root.resolve()
    output_root = output_root.resolve()
    final_root = output_root / "final-authority"
    final_build = final_root / "build"
    final_root.mkdir(parents=True, exist_ok=False)
    producer_compile = _compile_module(
        lean_root=lean_root,
        source_root=published_source_root,
        build_root=final_build,
        module=published_module,
        timeout_seconds=timeout_seconds,
    )
    final_source = build_final_artifact_source(
        published_module=published_module,
        published_declaration=published_declaration,
        namespace="Benchmark.Hardness.StageO.FinalAuthority",
    )
    final_file = final_root / "StageOFinal.lean"
    final_file.write_text(final_source, encoding="utf-8")
    final_command = _compile_final(
        lean_root=lean_root,
        generated_build_root=final_build,
        source_file=final_file,
        timeout_seconds=timeout_seconds,
    )

    replay_root = output_root / "release-replay"
    replay_source_root = replay_root / "published-src"
    replay_build = replay_root / "build"
    replay_source = replay_source_root / Path(*published_module.split(".")).with_suffix(".lean")
    replay_source.parent.mkdir(parents=True, exist_ok=False)
    original_source = published_source_root / Path(*published_module.split(".")).with_suffix(".lean")
    shutil.copy2(original_source, replay_source)
    replay_compile = _compile_module(
        lean_root=lean_root,
        source_root=replay_source_root,
        build_root=replay_build,
        module=published_module,
        timeout_seconds=timeout_seconds,
    )
    replay_text = build_final_artifact_source(
        published_module=published_module,
        published_declaration=published_declaration,
        namespace="Benchmark.Hardness.StageO.ReleaseReplay",
    )
    replay_file = replay_root / "StageOReleaseReplay.lean"
    replay_file.write_text(replay_text, encoding="utf-8")
    release_command = _compile_final(
        lean_root=lean_root,
        generated_build_root=replay_build,
        source_file=replay_file,
        timeout_seconds=timeout_seconds,
    )
    return StageOArtifactExecution(
        producer_compile=producer_compile,
        final_combined_lean=final_command,
        replay_producer_compile=replay_compile,
        release_replay=release_command,
        producer_source_sha256=_sha256_file(original_source),
        final_source_sha256=_sha256_file(final_file),
        replay_source_sha256=_sha256_file(replay_file),
    )
