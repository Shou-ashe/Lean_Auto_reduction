/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.CliqueCover
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Provenance
import ComplexityReduction.Presentation.ChromaticNumber
import ComplexityReduction.Presentation.CliqueCover
import ComplexityReduction.Protocol.ComponentRequest

/-!
Component-first Chromatic Number to Clique Cover route.

The CR construction complements the input graph while preserving its bound.
It is therefore a reusable graph-and-bound to clique-cover-hub gadget, rather
than authority for a fused concrete-route primitive.  The structured
Chromatic Number and Clique Cover presentations are presently their selected
hubs, so ingress and egress are exact endpoint identities.  The final public
certificate is assembled only with `CertifiedReduction.comp`, and typed
provenance exposes that composition without inspecting a declaration body.

The old CR `TMKarpReduction` is kept only as the read-only direct-TM source
for the hub gadget.  No route-local TM, cost witness, provider, packet, slot,
or descriptor is added here.
-/

namespace ComplexityReduction
namespace Routes
namespace ChromaticNumberToCliqueCover

open Annotations Certificate Encoding Program

/-- The original structured Chromatic Number source endpoint. -/
abbrev originalChromaticNumberProblem : PresentedProblem :=
  Presentation.ChromaticNumber.structuredProblem

/--
The canonical graph-colouring hub keeps the complete graph-and-colour-bound
carrier.  It cannot be replaced by bare `Graph`, which would lose the bound.
-/
abbrev graphColoringHubProblem : PresentedProblem :=
  Presentation.ChromaticNumber.structuredProblem

/-- The canonical clique-cover hub keeps the complete graph-and-block-bound carrier. -/
abbrev cliqueCoverHubProblem : PresentedProblem :=
  Presentation.CliqueCover.structuredProblem

/-- The public structured Clique Cover target. -/
abbrev originalCliqueCoverProblem : PresentedProblem :=
  Presentation.CliqueCover.structuredProblem

/-- The exact source ingress endpoint. -/
abbrev GraphColoringIngressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .ingress originalChromaticNumberProblem graphColoringHubProblem

/-- The unique source ingress request. -/
def graphColoringIngressRequest : GraphColoringIngressEndpoint :=
  .exact

/-- Ingress identity is justified only by exact equality of complete endpoints. -/
theorem graphColoringIngress_endpoints_eq :
    originalChromaticNumberProblem = graphColoringHubProblem :=
  rfl

/-- The exact reusable graph-colouring-to-clique-cover hub-gadget endpoint. -/
abbrev SharedGadgetEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .sharedGadget graphColoringHubProblem cliqueCoverHubProblem

/-- The unique complement-graph gadget request. -/
def sharedGadgetRequest : SharedGadgetEndpoint :=
  .exact

/-- The exact hub-to-public-target egress endpoint. -/
abbrev CliqueCoverEgressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .egress cliqueCoverHubProblem originalCliqueCoverProblem

/-- The unique egress request. -/
def cliqueCoverEgressRequest : CliqueCoverEgressEndpoint :=
  .exact

/-- Egress identity is justified only by exact equality of complete endpoints. -/
theorem cliqueCoverEgress_endpoints_eq :
    cliqueCoverHubProblem = originalCliqueCoverProblem :=
  rfl

/-- A read-only projection of CR's old endpoint-specific direct-TM record. -/
noncomputable def legacyOneOffTMKarpReduction :
    ComplexityReduction.TMKarpReduction
      graphColoringHubProblem.toEncodedDecisionProblem
      cliqueCoverHubProblem.toEncodedDecisionProblem := by
  simpa using
    ComplexityReduction.Karp21.CliqueCover.chromaticNumberToCliqueCoverStructuredTMKarpReduction

/-- The legacy projection is exactly CR's existing structured theorem. -/
@[simp] theorem legacyOneOffTMKarpReduction_eq_CR :
    legacyOneOffTMKarpReduction =
      ComplexityReduction.Karp21.CliqueCover.chromaticNumberToCliqueCoverStructuredTMKarpReduction :=
  rfl

/-- The exact direct-TM primitive for the reusable complement-graph gadget. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def complementGraphGadgetPrimitive :
    Primitive graphColoringHubProblem.representation cliqueCoverHubProblem.representation :=
  Primitive.ofTMPolyTime ComplexityReduction.Karp21.CliqueCover.textbookMap
    ComplexityReduction.Karp21.CliqueCover.chromaticNumberToCliqueCoverStructured_tm_polytime

/-- The shared gadget's program is the one direct-TM atom. -/
noncomputable def complementGraphGadgetProgram :
    PolyProg graphColoringHubProblem.representation cliqueCoverHubProblem.representation :=
  .atom complementGraphGadgetPrimitive

/-- The direct primitive computes CR's named complement-graph construction. -/
@[simp] theorem complementGraphGadgetProgram_run (input : graphColoringHubProblem.Instance) :
    complementGraphGadgetProgram.run input =
      ComplexityReduction.Karp21.CliqueCover.textbookMap input :=
  rfl

/-- The semantic theorem is indexed by the same executable stored in the gadget program. -/
theorem complementGraphGadget_correct (input : graphColoringHubProblem.Instance) :
    graphColoringHubProblem.accepts input ↔
      cliqueCoverHubProblem.accepts (complementGraphGadgetProgram.run input) := by
  simpa only [Presentation.ChromaticNumber.structuredProblem_accepts,
    Presentation.CliqueCover.structuredProblem_accepts,
    complementGraphGadgetProgram_run] using
    ComplexityReduction.Karp21.CliqueCover.textbookMap_correct input

/-- The identity ingress is a typed component certificate, not a bare endpoint equality. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_ingress]
noncomputable def ingress : CertifiedReduction originalChromaticNumberProblem graphColoringHubProblem :=
  .refl graphColoringHubProblem

/-- The reusable complement-graph construction is the sole shared-gadget certificate. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def sharedGadget : CertifiedReduction graphColoringHubProblem cliqueCoverHubProblem where
  program := complementGraphGadgetProgram
  correct := complementGraphGadget_correct

/-- The public route is the thin composition of the ingress and shared gadget. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def finalRoute :
    CertifiedReduction originalChromaticNumberProblem originalCliqueCoverProblem :=
  CertifiedReduction.comp sharedGadget ingress

/-- The identity egress is recorded by the exact endpoint equality, not a second primitive. -/
@[complexity_reduction_ir_typed_edge]
noncomputable def finalRouteProvenance :
    CertifiedRouteProvenance ingress sharedGadget .identity finalRoute :=
  CertifiedRouteProvenance.identityEgress ingress sharedGadget

/-- The final program is definitionally the required component composition. -/
@[simp] theorem finalRoute_program :
    finalRoute.program = PolyProg.comp sharedGadget.program ingress.program :=
  rfl

/-- The final semantic law is inherited from the one shared-gadget executable. -/
theorem finalRoute_correct (input : originalChromaticNumberProblem.Instance) :
    originalChromaticNumberProblem.accepts input ↔
      originalCliqueCoverProblem.accepts (finalRoute.program.run input) :=
  finalRoute.correct input

/-- All direct-TM evidence of the final route is compiler output for its composite program. -/
@[simp] theorem finalRoute_directTM :
    finalRoute.directTM = finalRoute.program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM finalRoute

/-- The final compatibility cost is compiler-derived from that same composite program. -/
@[simp] theorem finalRoute_compatibilityCost :
    finalRoute.compatibilityCost = finalRoute.program.compatibilityCost :=
  CertifiedReduction.compatibilityCost_eq_program_compatibilityCost finalRoute

/-- The shared gadget's compiler output is exactly the direct-TM primitive witness. -/
@[simp] theorem sharedGadget_compileTM :
    sharedGadget.program.compileTM = complementGraphGadgetPrimitive.tmPolyTime :=
  rfl

/-- The legacy direct-TM record remains a read-only equality check, not planner authority. -/
theorem sharedGadget_directTM_eq_legacy :
    sharedGadget.directTM = legacyOneOffTMKarpReduction.polytime := by
  apply Subsingleton.elim

end ChromaticNumberToCliqueCover
end Routes
end ComplexityReduction
