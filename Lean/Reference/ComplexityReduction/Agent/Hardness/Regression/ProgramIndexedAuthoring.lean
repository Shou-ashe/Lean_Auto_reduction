import Benchmark.Hardness.Inputs.Authoring.ProgramIndexedReduction
import ComplexityReduction.Agent.Hardness.Runtime
import Lean.Elab.Command

/-!
Phase-5 regressions for a complete staged, program-indexed reduction bundle.
The negative checks use valid declarations at the wrong program index, so
their rejection cannot be attributed merely to malformed Lean source.
-/

namespace ComplexityReduction.Agent.Hardness.Regression.ProgramIndexedAuthoring

open Lean Elab Command Meta
open Encoding Certificate

private noncomputable abbrev source : PresentedProblem :=
  Benchmark.Hardness.Inputs.Authoring.ProgramIndexedReduction.source

private noncomputable abbrev target : PresentedProblem :=
  Benchmark.Hardness.Inputs.Authoring.ProgramIndexedReduction.target

def executable : source.Instance → target.Instance :=
  Benchmark.Hardness.Inputs.Authoring.ProgramIndexedReduction.executable

def executableDirectTM : Agent.Hardness.Authoring.ExecutableDirectTMEvidence
    source target executable :=
  Agent.Hardness.Authoring.ProgramIndexedReductionTemplate.toExecutableDirectTM
    Benchmark.Hardness.Inputs.Authoring.ProgramIndexedReduction.executableDirectTM executable rfl

@[complexity_reduction_ir_typed_primitive]
noncomputable def primitive : Program.Primitive source.representation target.representation :=
  Agent.Hardness.Authoring.ProgramIndexedReductionTemplate.toPrimitive
    executable executableDirectTM

noncomputable def program : Program.PolyProg source.representation target.representation :=
  Agent.Hardness.Authoring.ProgramIndexedReductionTemplate.toProgram primitive

def semantic : Agent.Hardness.Authoring.ProgramSemanticProof source target program :=
  Agent.Hardness.Authoring.ProgramIndexedReductionTemplate.toSemanticProof
    Benchmark.Hardness.Inputs.Authoring.ProgramIndexedReduction.executableCorrect program rfl

def directTM : Agent.Hardness.Authoring.ProgramDirectTMEvidence source target program :=
  Agent.Hardness.Authoring.ProgramIndexedReductionTemplate.toProgramDirectTM program

@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def route : CertifiedReduction source target :=
  Agent.Hardness.Authoring.ProgramIndexedReductionTemplate.toReduction program semantic

run_cmd do
  let environment ← getEnv
  Command.liftTermElabM do
    let observations ← Agent.Hardness.Authoring.programIndexedReductionTemplates environment
      .sharedGadget (mkConst ``source) (mkConst ``target)
    unless observations.any fun observation =>
        observation.templateDeclaration ==
          ``Benchmark.Hardness.Inputs.Authoring.ProgramIndexedReduction.template &&
        observation.componentDeclarations == [
          ``Benchmark.Hardness.Inputs.Authoring.ProgramIndexedReduction.executable,
          ``Benchmark.Hardness.Inputs.Authoring.ProgramIndexedReduction.executableDirectTM,
          ``Benchmark.Hardness.Inputs.Authoring.ProgramIndexedReduction.executableCorrect] do
      throwError "program-indexed reduction template was not discovered"
    let wrongRole ← Agent.Hardness.Authoring.programIndexedReductionTemplates environment
      .ingress (mkConst ``source) (mkConst ``target)
    unless wrongRole.isEmpty do
      throwError "program-indexed reduction template was accepted at the wrong role"
    match ← Agent.Hardness.Authoring.validateProgramIndexedReductionBundle environment
        ``executable ``executableDirectTM ``primitive ``program ``semantic ``directTM ``route
        (mkConst ``source) (mkConst ``target) with
    | .ok () => pure ()
    | .error failure =>
        throwError "valid program-indexed reduction bundle was rejected: {repr failure}"

private noncomputable def secondProgram :
    Program.PolyProg source.representation target.representation :=
  .id source.representation

private def secondSemantic :
    Agent.Hardness.Authoring.ProgramSemanticProof source target secondProgram := by
  intro input
  change input = input ↔ True
  simp

private def secondDirectTM :
    Agent.Hardness.Authoring.ProgramDirectTMEvidence source target secondProgram :=
  Agent.Hardness.Authoring.ProgramIndexedReductionTemplate.toProgramDirectTM secondProgram

private noncomputable def costOnly : ComplexityReduction.CostedMap
    source.representation.encodedType target.representation.encodedType program.run :=
  program.compile.costed

@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
private noncomputable def secondRoute : CertifiedReduction source target :=
  Agent.Hardness.Authoring.ProgramIndexedReductionTemplate.toReduction
    secondProgram secondSemantic

run_cmd do
  let environment ← getEnv
  Command.liftTermElabM do
    match ← Agent.Hardness.Authoring.validateProgramIndexedReductionBundle environment
        ``executable ``executableDirectTM ``primitive ``program ``secondSemantic ``directTM ``route
        (mkConst ``source) (mkConst ``target) with
    | .error (.semanticProgramMismatch _) => pure ()
    | .error failure => throwError "second-map semantics returned the wrong failure: {repr failure}"
    | .ok () => throwError "semantic proof for a second program passed bundle validation"
    match ← Agent.Hardness.Authoring.validateProgramIndexedReductionBundle environment
        ``executable ``executableDirectTM ``primitive ``program ``semantic ``secondDirectTM ``route
        (mkConst ``source) (mkConst ``target) with
    | .error (.directTMProgramMismatch _) => pure ()
    | .error failure => throwError "second-program direct-TM returned the wrong failure: {repr failure}"
    | .ok () => throwError "direct-TM evidence for a second program passed bundle validation"
    match ← Agent.Hardness.Authoring.validateProgramIndexedReductionBundle environment
        ``executable ``executableDirectTM ``primitive ``program ``semantic ``costOnly ``route
        (mkConst ``source) (mkConst ``target) with
    | .error (.directTMHeadMismatch _) => pure ()
    | .error failure => throwError "cost-only facade returned the wrong failure: {repr failure}"
    | .ok () => throwError "cost-only facade passed the direct-TM checkpoint"
    match ← Agent.Hardness.Authoring.validateProgramIndexedReductionBundle environment
        ``executable ``executableDirectTM ``primitive ``program ``semantic ``directTM ``secondRoute
        (mkConst ``source) (mkConst ``target) with
    | .error (.routeProgramMismatch _) => pure ()
    | .error failure => throwError "second-program route returned the wrong failure: {repr failure}"
    | .ok () => throwError "route storing a second program passed bundle validation"

end ComplexityReduction.Agent.Hardness.Regression.ProgramIndexedAuthoring

assert_standard_axioms
  ComplexityReduction.Agent.Hardness.Regression.ProgramIndexedAuthoring.executableDirectTM,
  ComplexityReduction.Agent.Hardness.Regression.ProgramIndexedAuthoring.primitive,
  ComplexityReduction.Agent.Hardness.Regression.ProgramIndexedAuthoring.program,
  ComplexityReduction.Agent.Hardness.Regression.ProgramIndexedAuthoring.semantic,
  ComplexityReduction.Agent.Hardness.Regression.ProgramIndexedAuthoring.directTM,
  ComplexityReduction.Agent.Hardness.Regression.ProgramIndexedAuthoring.route
