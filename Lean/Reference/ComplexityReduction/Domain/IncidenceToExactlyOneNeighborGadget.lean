/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.IncidenceToExactlyOneNeighborProgram
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.ExactlyOneNeighbor
import ComplexityReduction.Program.CompileTM
import ComplexityReduction.Protocol.ComponentResolver

/-!
Canonical shared-gadget boundary from the canonical incidence exact-cover hub
to the existential Exactly-One-Neighbor endpoint.

The executable, direct-TM realization, and semantic theorem are indexed by the
same `PolyProg`.  This module owns the one accepted hub component; it imports
no concrete source wrapper, route, registry, or legacy route assembly.
-/

namespace ComplexityReduction
namespace Domain
namespace IncidenceToExactlyOneNeighborGadget

open Encoding
open Program
open Certificate

/-- The canonical incidence exact-cover hub endpoint. -/
abbrev hubProblem : PresentedProblem :=
  IncidenceIR.exactCoverProblem

/-- The selected existential Exactly-One-Neighbor target endpoint. -/
abbrev targetProblem : PresentedProblem :=
  Presentation.ExactlyOneNeighbor.presentedProblem

/-- The canonical incidence construction preserves exactly the two hub predicates. -/
theorem run_correct (input : hubProblem.Instance) :
    hubProblem.accepts input ↔
      targetProblem.accepts (IncidenceToExactlyOneNeighbor.run input) :=
  IncidenceToExactlyOneNeighbor.existsExactCover_iff_run input

/--
The exact shared-gadget endpoint, indexed by its architectural role and the
two canonical presented problems.  This is an abbreviation of the Protocol
owner rather than a route-local endpoint vocabulary.
-/
abbrev SharedGadgetEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .sharedGadget hubProblem targetProblem

/-- The one exact request for the incidence-to-EON shared component. -/
abbrev SharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget hubProblem targetProblem

/-- Request the canonical hub-level shared gadget. -/
def request : SharedGadgetRequest :=
  .exact

/-- An executable candidate can only be a V2 program at the exact hub and target representations. -/
abbrev SharedGadgetProgram : Type 2 :=
  PolyProg hubProblem.representation targetProblem.representation

/-- The sole direct-TM-backed primitive realizes the closed hub executable. -/
def sharedGadgetPrimitive : Primitive hubProblem.representation targetProblem.representation :=
  Primitive.ofTMPolyTime IncidenceToExactlyOneNeighbor.programRun (by
    simpa [hubProblem, targetProblem, IncidenceIR.exactCoverProblem,
      Presentation.ExactlyOneNeighbor.presentedProblem,
      Presentation.ExactlyOneNeighbor.structuredPresentation,
      IncidenceIR.lawfulRepresentation, IncidenceToExactlyOneNeighbor.incidenceEncoding]
      using IncidenceToExactlyOneNeighbor.programRun_tmPolyTime)

/-- The one canonical shared-gadget program contains no source-wrapper computation. -/
def sharedGadgetProgram : SharedGadgetProgram :=
  .atom sharedGadgetPrimitive

/-- The stored program executes exactly the closed incidence hub construction. -/
@[simp] theorem sharedGadgetProgram_run (input : hubProblem.Instance) :
    sharedGadgetProgram.run input = IncidenceToExactlyOneNeighbor.programRun input :=
  rfl

/-- The program compiler is the sole direct-TM witness for the exact stored executable. -/
@[simp] theorem sharedGadgetProgram_directTM :
    sharedGadgetProgram.compileTM = sharedGadgetPrimitive.tmPolyTime :=
  rfl

/-- Hub-level semantic correctness uses only the incidence/EON theorem, never a source wrapper. -/
theorem sharedGadgetProgram_correct (input : hubProblem.Instance) :
    hubProblem.accepts input ↔ targetProblem.accepts (sharedGadgetProgram.run input) := by
  rw [sharedGadgetProgram_run, IncidenceToExactlyOneNeighbor.programRun_eq_run]
  exact run_correct input

/-- The accepted shared component stores the one closed program and its hub theorem. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
def sharedGadget : CertifiedReduction hubProblem targetProblem where
  program := sharedGadgetProgram
  correct := sharedGadgetProgram_correct

/-- The canonical typed result for this exact shared-gadget request. -/
abbrev ComponentOutcome : Type 2 :=
  Protocol.ComponentResolution .sharedGadget hubProblem targetProblem

/-- The component resolver accepts precisely the canonical certified shared gadget. -/
def resolution : ComponentOutcome :=
  Protocol.ComponentResolver.accept request sharedGadget

/-- The request itself retains the exact shared-gadget endpoint. -/
@[simp] theorem request_endpoint_exact :
    request.endpoint =
      (show Protocol.ComponentEndpoint .sharedGadget hubProblem targetProblem from .exact) :=
  rfl

/-- The resolution carries the exact accepted component, not metadata-only readiness. -/
@[simp] theorem resolution_eq_accepted :
    resolution = .accepted sharedGadget :=
  rfl

end IncidenceToExactlyOneNeighborGadget
end Domain
end ComplexityReduction
