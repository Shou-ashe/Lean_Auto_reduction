/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.GraphColoringToIncidenceBlockInputs
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Reduction
import ComplexityReduction.Protocol.ComponentResolver

/-!
The canonical shared GraphColoringIR-to-IncidenceIR gadget.

The construction is closed at the two typed hubs.  Its one `PolyProg` embeds
the direct-TM executable from `GraphColoringToIncidenceBlockInputs`; semantic
correctness is transported only through the wrapper-independent hub theorem.
No concrete Chromatic Number or Exact Cover wrapper, route, registry, or
legacy assembly is imported here.
-/

namespace ComplexityReduction
namespace Domain
namespace GraphColoringToIncidenceGadget

open Certificate
open Encoding
open Program

/-- The canonical source endpoint retaining a graph and its colour bound. -/
abbrev sourceProblem : PresentedProblem :=
  GraphColoringIR.chromaticNumberProblem

/-- The canonical target endpoint retaining incidence identities explicitly. -/
abbrev targetProblem : PresentedProblem :=
  IncidenceIR.exactCoverProblem

/-- The role-indexed exact endpoint for this reusable hub gadget. -/
abbrev SharedGadgetEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .sharedGadget sourceProblem targetProblem

/-- The one exact component request at the canonical hub endpoints. -/
abbrev SharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget sourceProblem targetProblem

/-- Request the closed GraphColoringIR-to-IncidenceIR component. -/
def request : SharedGadgetRequest := .exact

/-- The only accepted program type is fixed by the two encoder-bound hub representations. -/
abbrev SharedGadgetProgram : Type 2 :=
  PolyProg sourceProblem.representation targetProblem.representation

/-- The direct-TM primitive is indexed by the exact closed hub executable. -/
def sharedGadgetPrimitive :
    Primitive sourceProblem.representation targetProblem.representation :=
  Primitive.ofTMPolyTime GraphColoringToIncidence.runExecutable (by
    simpa [sourceProblem, targetProblem, GraphColoringIR.chromaticNumberProblem,
      IncidenceIR.exactCoverProblem, GraphColoringIR.lawfulRepresentation,
      IncidenceIR.lawfulRepresentation, GraphColoringToIncidence.incidenceEncoding]
      using GraphColoringToIncidence.runExecutable_tmPolyTime)

/-- The canonical shared computation is one atom, never a concrete route primitive. -/
def sharedGadgetProgram : SharedGadgetProgram :=
  .atom sharedGadgetPrimitive

@[simp] theorem sharedGadgetProgram_run (input : sourceProblem.Instance) :
    sharedGadgetProgram.run input = GraphColoringToIncidence.runExecutable input :=
  rfl

@[simp] theorem sharedGadgetProgram_directTM :
    sharedGadgetProgram.compileTM = sharedGadgetPrimitive.tmPolyTime :=
  rfl

/-- The semantic hub theorem and executable equality establish the exact program iff. -/
theorem sharedGadgetProgram_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔
      targetProblem.accepts (sharedGadgetProgram.run input) := by
  rw [sharedGadgetProgram_run, GraphColoringToIncidence.runExecutable_eq_core]
  exact GraphColoringToIncidence.isColorable_iff_run_exactCover input

/-- The authoritative reusable GraphColoringIR-to-IncidenceIR certificate. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
def sharedGadget : CertifiedReduction sourceProblem targetProblem where
  program := sharedGadgetProgram
  correct := sharedGadgetProgram_correct

/-- The resolver result is fixed by the exact component role and endpoints. -/
abbrev ComponentOutcome : Type 2 :=
  Protocol.ComponentResolution .sharedGadget sourceProblem targetProblem

/-- This exact shared hub capability is accepted without consulting metadata. -/
def resolution : ComponentOutcome :=
  Protocol.ComponentResolver.accept request sharedGadget

@[simp] theorem request_endpoint_exact :
    request.endpoint =
      (show Protocol.ComponentEndpoint .sharedGadget sourceProblem targetProblem from .exact) :=
  rfl

@[simp] theorem resolution_eq_accepted :
    resolution = .accepted sharedGadget :=
  rfl

end GraphColoringToIncidenceGadget
end Domain
end ComplexityReduction
