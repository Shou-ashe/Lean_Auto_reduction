/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.Reductions
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Reduction
import ComplexityReduction.Presentation.Satisfiability
import ComplexityReduction.Problems.Karp21.Satisfiability
import ComplexityReduction.Protocol.ComponentResolver

/-!
The canonical structured-CNF-to-structured-3SAT hub component.

This leaf owns the V2 admission of CR's already standard-audited structured
split executable.  The legacy theorem supplies the direct-TM realization;
the typed primitive, program, semantic certificate, and component resolution
all remain indexed by the two exact encoder-bound SAT hubs.  No final route,
wrapper-specific adapter, packet, provider, or descriptor is introduced here.
-/

namespace ComplexityReduction
namespace Domain
namespace CNFToThreeSATStandardTM

open Certificate Encoding Program

/-- The canonical structured CNF/SAT hub. -/
abbrev sourceProblem : PresentedProblem :=
  Presentation.Satisfiability.structuredProblem

/-- The canonical structured bundled-3SAT hub. -/
abbrev targetProblem : PresentedProblem :=
  Problems.Karp21.Satisfiability.threeSATStructuredProblem

/-- The exact role-indexed endpoint of the reusable split gadget. -/
abbrev SharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget sourceProblem targetProblem

/-- The only exact request for this hub-to-hub component. -/
def request : SharedGadgetRequest := .exact

/-- CR's faithful structured split reduction at the exact V2 hub endpoints. -/
noncomputable def legacyReduction :
    ComplexityReduction.TMKarpReduction sourceProblem.toEncodedDecisionProblem
      targetProblem.toEncodedDecisionProblem := by
  simpa [sourceProblem, targetProblem,
    Presentation.Satisfiability.structuredProblem,
    Presentation.Satisfiability.structuredPresentation,
    Problems.Karp21.Satisfiability.threeSATStructuredProblem,
    Problems.Karp21.Satisfiability.threeSATStructuredPresentation] using
    ComplexityReduction.Karp21.cnfSATToThreeSATStructuredTMKarpReduction

/-- The standard-audited primitive is indexed by the exact split executable. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def sharedGadgetPrimitive :
    Primitive sourceProblem.representation targetProblem.representation :=
  Primitive.ofTMPolyTime legacyReduction.f legacyReduction.polytime

/-- The shared computation has one primitive atom and no parallel executable. -/
noncomputable def sharedGadgetProgram :
    PolyProg sourceProblem.representation targetProblem.representation :=
  .atom sharedGadgetPrimitive

@[simp] theorem sharedGadgetProgram_run (input : sourceProblem.Instance) :
    sharedGadgetProgram.run input = legacyReduction.f input :=
  rfl

@[simp] theorem sharedGadgetProgram_directTM :
    sharedGadgetProgram.compileTM = legacyReduction.polytime :=
  rfl

/-- The authoritative certificate stores the same direct-TM-backed primitive program. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def sharedGadget : CertifiedReduction sourceProblem targetProblem where
  program := sharedGadgetProgram
  correct := by
    intro input
    exact legacyReduction.correct input

@[simp] theorem sharedGadget_program :
    sharedGadget.program = sharedGadgetProgram :=
  rfl

@[simp] theorem sharedGadget_directTM :
    sharedGadget.directTM = sharedGadget.program.compileTM :=
  rfl

/-- The semantic law is indexed by the same split program. -/
theorem sharedGadget_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔ targetProblem.accepts (sharedGadgetProgram.run input) :=
  sharedGadget.correct input

/-- Only the exact role-indexed request receives this component. -/
noncomputable def resolution :
    Protocol.ComponentResolution .sharedGadget sourceProblem targetProblem :=
  Protocol.ComponentResolver.accept request sharedGadget

@[simp] theorem resolution_exact :
    resolution = .accepted sharedGadget :=
  rfl

end CNFToThreeSATStandardTM
end Domain
end ComplexityReduction
