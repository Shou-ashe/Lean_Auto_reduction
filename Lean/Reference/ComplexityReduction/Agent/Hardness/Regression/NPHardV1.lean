/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Benchmark.Hardness.Inputs.Completeness.WrongDirection
import ComplexityReduction.Agent.Hardness.Runtime
import Lean.Elab.Command

/-!
Regression coverage for the versioned native NP-hardness request lane.

The checks cover a zero-length completeness seed, an existing one-atom
forward route, rejection of a reverse-only route, exact registered hardness,
the final term elaborator, and the standard-axiom gate.
-/

namespace ComplexityReduction.Agent.Hardness.Regression.NPHardV1

open Lean Elab Command Meta
open Encoding Certificate Protocol
open NPHardResolver

def npHardRequest (problem : PresentedProblem) : TypedNPHardRequestV1 where
  problem := problem

private def resolveRequest (environment : Environment) (problem : Name) :
    TermElabM (Except NPHardFailureV1 ResolvedNPHardRequestV1) := do
  let request ← mkAppM ``npHardRequest #[Lean.mkConst problem]
  resolveNPHardRequestV1 environment request

run_cmd do
  let environment ← getEnv
  Command.liftTermElabM do
    match ← resolveRequest environment
        ``Problems.Karp21.Satisfiability.threeSATStructuredProblem with
    | .ok resolved =>
        unless resolved.evidenceKind == .transportedHardness do
          throwError "zero-length completeness seed returned {repr resolved.evidenceKind}"
        let some path := resolved.path?
          | throwError "zero-length completeness seed omitted its path"
        unless path.atoms.isEmpty do
          throwError "zero-length completeness seed used {path.atoms.length} atoms"
        unless resolved.completenessDeclaration? == some
            ``Certificate.NativeCookLevin.canonicalThreeSATNativeCompleteness do
          throwError "zero-length completeness seed selected the wrong declaration"
    | .error resolverFailure =>
        throwError "zero-length NP-hardness resolution failed: {repr resolverFailure}"

    match ← resolveRequest environment
        ``Problems.Karp21.GraphAtoms.cliqueStructuredProblem with
    | .ok resolved =>
        unless resolved.evidenceKind == .transportedHardness do
          throwError "Clique NP-hardness returned {repr resolved.evidenceKind}"
        let some path := resolved.path?
          | throwError "Clique NP-hardness omitted its forward path"
        unless path.atoms.length == 1 do
          throwError "Clique NP-hardness used {path.atoms.length} atoms"
        let some provenance := path.atomicProvenance.head?
          | throwError "Clique NP-hardness omitted atomic provenance"
        unless provenance.declaration == ``Routes.ThreeSATToClique.sharedGadget do
          throwError "Clique NP-hardness selected {provenance.declaration}"
        unless provenance.role? == some .sharedGadget do
          throwError "Clique NP-hardness selected the wrong component role"
        unless resolved.completenessDeclaration? == some
            ``Certificate.NativeCookLevin.canonicalThreeSATNativeCompleteness do
          throwError "Clique NP-hardness selected the wrong hardness seed"
    | .error resolverFailure =>
        throwError "Clique NP-hardness resolution failed: {repr resolverFailure}"

    match ← resolveRequest environment
        ``Benchmark.Hardness.Inputs.Completeness.WrongDirection.source with
    | .error resolverFailure =>
        unless resolverFailure.code == .wrongDirectionOnly do
          throwError "reverse-only request returned {resolverFailure.code.label}"
    | .ok _ =>
        throwError "request.problem → hardness-seed route was accepted as NP-hardness evidence"

def cliqueRequest : TypedNPHardRequestV1 :=
  npHardRequest Problems.Karp21.GraphAtoms.cliqueStructuredProblem

noncomputable def cliqueResult : TypedNPHardResultV1 cliqueRequest :=
  by_np_hard_resolver

theorem cliqueIsNPHard :
    NativeTMNPHard Problems.Karp21.GraphAtoms.cliqueStructuredProblem :=
  cliqueResult.extractNativeHardness

@[complexity_reduction_ir_typed_native_hardness]
theorem registeredCliqueHardness :
    NativeTMNPHard Problems.Karp21.GraphAtoms.cliqueStructuredProblem :=
  cliqueIsNPHard

run_cmd do
  let environment ← getEnv
  Command.liftTermElabM do
    match ← resolveRequest environment
        ``Problems.Karp21.GraphAtoms.cliqueStructuredProblem with
    | .ok resolved =>
        unless resolved.evidenceKind == .registeredHardness do
          throwError "exact registered hardness returned {repr resolved.evidenceKind}"
        unless resolved.path?.isNone do
          throwError "exact registered hardness unexpectedly returned a path"
        unless resolved.hardnessDeclaration? == some ``registeredCliqueHardness do
          throwError "exact registered hardness selected the wrong declaration"
    | .error resolverFailure =>
        throwError "exact registered hardness resolution failed: {repr resolverFailure}"

axiom poisonedNativeHardness :
  NativeTMNPHard Problems.Karp21.GraphAtoms.cliqueStructuredProblem

noncomputable def poisonedResult : TypedNPHardResultV1 cliqueRequest :=
  TypedNPHardResultV1.fromRegistered cliqueRequest poisonedNativeHardness

theorem poisonedArtifact :
    NativeTMNPHard Problems.Karp21.GraphAtoms.cliqueStructuredProblem :=
  poisonedResult.extractNativeHardness

/--
error: axiom gate rejected ComplexityReduction.Agent.Hardness.Regression.NPHardV1.poisonedArtifact: forbidden axiom ComplexityReduction.Agent.Hardness.Regression.NPHardV1.poisonedNativeHardness
-/
#guard_msgs in
assert_standard_axioms poisonedArtifact

end ComplexityReduction.Agent.Hardness.Regression.NPHardV1

assert_standard_axioms
  ComplexityReduction.Agent.Hardness.Regression.NPHardV1.cliqueResult,
  ComplexityReduction.Agent.Hardness.Regression.NPHardV1.cliqueIsNPHard,
  ComplexityReduction.Agent.Hardness.Regression.NPHardV1.registeredCliqueHardness
