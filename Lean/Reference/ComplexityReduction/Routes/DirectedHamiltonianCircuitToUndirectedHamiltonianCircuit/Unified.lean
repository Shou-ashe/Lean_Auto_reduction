/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.UndirectedHamiltonianCircuitStructuredTM
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Provenance
import ComplexityReduction.Presentation.DirectedHamiltonianCircuit
import ComplexityReduction.Presentation.UndirectedHamiltonianCircuit
import ComplexityReduction.Protocol.ComponentRequest

/-!
Component-first structured Directed-to-Undirected-Hamiltonian-Circuit route.

CR supplies a standard-axiom checked direct-TM Karp construction at the exact
structured Directed- and Undirected-Hamiltonian-Circuit endpoints.  V2
exposes it only as the reusable DHC-hub-to-UHC-hub component.  The public
route is the thin composition of a typed ingress identity with that shared
gadget; its identity egress is represented by `CertifiedRouteProvenance`.

No route-wide certificate authority, route-local machine, cost map, legacy
certificate facade, resolver, or metadata capability is introduced.  The one
shared-gadget program is the common identity for execution, semantics,
direct-TM, and cost.
-/

namespace ComplexityReduction
namespace Routes
namespace DirectedHamiltonianCircuitToUndirectedHamiltonianCircuit

open Annotations Certificate Encoding Program

/-- The original exact structured DHC source endpoint. -/
abbrev originalDirectedHamiltonianCircuitProblem : PresentedProblem :=
  Presentation.DirectedHamiltonianCircuit.structuredProblem

/-- The canonical structured DHC hub is the full original source endpoint. -/
abbrev directedHamiltonianCircuitHubProblem : PresentedProblem :=
  Presentation.DirectedHamiltonianCircuit.structuredProblem

/-- The canonical structured UHC hub reached by CR's direct-TM construction. -/
abbrev undirectedHamiltonianCircuitHubProblem : PresentedProblem :=
  Presentation.UndirectedHamiltonianCircuit.structuredProblem

/-- The public structured UHC target is already the complete canonical hub. -/
abbrev originalUndirectedHamiltonianCircuitProblem : PresentedProblem :=
  Presentation.UndirectedHamiltonianCircuit.structuredProblem

/-- The exact identity-eligible ingress endpoint into the DHC hub. -/
abbrev DirectedHamiltonianCircuitIngressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .ingress originalDirectedHamiltonianCircuitProblem
    directedHamiltonianCircuitHubProblem

/-- The unique ingress request fixes its complete presented endpoints. -/
def directedHamiltonianCircuitIngressRequest : DirectedHamiltonianCircuitIngressEndpoint :=
  .exact

/-- Ingress is identity-eligible only because the complete endpoints agree. -/
theorem directedHamiltonianCircuitIngress_endpoints_eq :
    originalDirectedHamiltonianCircuitProblem = directedHamiltonianCircuitHubProblem :=
  rfl

/-- The exact reusable DHC-to-UHC shared-gadget endpoint. -/
abbrev SharedGadgetEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .sharedGadget directedHamiltonianCircuitHubProblem
    undirectedHamiltonianCircuitHubProblem

/-- The unique request for the standard direct-TM shared gadget. -/
def sharedGadgetRequest : SharedGadgetEndpoint :=
  .exact

/-- The exact identity-eligible UHC-hub-to-public-target egress endpoint. -/
abbrev UndirectedHamiltonianCircuitEgressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .egress undirectedHamiltonianCircuitHubProblem
    originalUndirectedHamiltonianCircuitProblem

/-- The unique egress request fixes its complete presented endpoints. -/
def undirectedHamiltonianCircuitEgressRequest : UndirectedHamiltonianCircuitEgressEndpoint :=
  .exact

/-- Egress is identity-eligible only because the complete endpoints agree. -/
theorem undirectedHamiltonianCircuitEgress_endpoints_eq :
    undirectedHamiltonianCircuitHubProblem = originalUndirectedHamiltonianCircuitProblem :=
  rfl

/--
Read-only CR direct-TM Karp witness at the reusable hub endpoints.  It is an
audit source only: V2's certificate below starts from its executable and
direct-TM field, never from a legacy cost map or certificate facade.
-/
noncomputable def legacySharedGadgetTMKarpReduction :
    ComplexityReduction.TMKarpReduction directedHamiltonianCircuitHubProblem.toEncodedDecisionProblem
      undirectedHamiltonianCircuitHubProblem.toEncodedDecisionProblem := by
  simpa [directedHamiltonianCircuitHubProblem, undirectedHamiltonianCircuitHubProblem] using
    ComplexityReduction.Karp21.UndirectedHamiltonianCircuit.directedToUndirectedHamiltonianCircuitStructuredTMKarpReduction

/-- The read-only audit projection is exactly CR's named structured direct-TM record. -/
@[simp] theorem legacySharedGadgetTMKarpReduction_eq_CR :
    legacySharedGadgetTMKarpReduction =
      ComplexityReduction.Karp21.UndirectedHamiltonianCircuit.directedToUndirectedHamiltonianCircuitStructuredTMKarpReduction :=
  rfl

/-- The sole primitive for the reusable shared gadget reuses CR's executable and TM evidence. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def sharedGadgetPrimitive :
    Primitive directedHamiltonianCircuitHubProblem.representation
      undirectedHamiltonianCircuitHubProblem.representation :=
  Primitive.ofTMPolyTime legacySharedGadgetTMKarpReduction.f
    legacySharedGadgetTMKarpReduction.polytime

/-- The shared gadget owns one direct-TM atom program. -/
noncomputable def sharedGadgetProgram :
    PolyProg directedHamiltonianCircuitHubProblem.representation
      undirectedHamiltonianCircuitHubProblem.representation :=
  .atom sharedGadgetPrimitive

/-- The shared program executes CR's checked structured map. -/
@[simp] theorem sharedGadgetProgram_run (input : directedHamiltonianCircuitHubProblem.Instance) :
    sharedGadgetProgram.run input = legacySharedGadgetTMKarpReduction.f input :=
  rfl

/-- The semantic law is indexed by that same shared-gadget executable. -/
theorem sharedGadget_correct (input : directedHamiltonianCircuitHubProblem.Instance) :
    directedHamiltonianCircuitHubProblem.accepts input ↔
      undirectedHamiltonianCircuitHubProblem.accepts (sharedGadgetProgram.run input) := by
  simpa only [sharedGadgetProgram_run] using legacySharedGadgetTMKarpReduction.correct input

/-- The exact source ingress is a typed certificate, not a bare endpoint equality. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_ingress]
noncomputable def ingress :
    CertifiedReduction originalDirectedHamiltonianCircuitProblem directedHamiltonianCircuitHubProblem :=
  .refl directedHamiltonianCircuitHubProblem

/-- The CR construction is the sole reusable DHC-to-UHC shared-gadget certificate. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def sharedGadget :
    CertifiedReduction directedHamiltonianCircuitHubProblem undirectedHamiltonianCircuitHubProblem where
  program := sharedGadgetProgram
  correct := sharedGadget_correct

/-- The public route is only the required composition of ingress and shared gadget. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def finalRoute :
    CertifiedReduction originalDirectedHamiltonianCircuitProblem
      originalUndirectedHamiltonianCircuitProblem :=
  CertifiedReduction.comp sharedGadget ingress

/-- Typed provenance records that the UHC egress is the exact identity endpoint. -/
@[complexity_reduction_ir_typed_edge]
noncomputable def finalRouteProvenance :
    CertifiedRouteProvenance ingress sharedGadget .identity finalRoute :=
  CertifiedRouteProvenance.identityEgress ingress sharedGadget

/-- The final program is definitionally the mandated component composition. -/
@[simp] theorem finalRoute_program :
    finalRoute.program = PolyProg.comp sharedGadget.program ingress.program :=
  rfl

/-- The final executable is the sequential execution of the component programs. -/
@[simp] theorem finalRoute_run (input : originalDirectedHamiltonianCircuitProblem.Instance) :
    finalRoute.program.run input =
      sharedGadget.program.run (ingress.program.run input) :=
  rfl

/-- The final semantic law is inherited from the composed component certificates. -/
theorem finalRoute_correct (input : originalDirectedHamiltonianCircuitProblem.Instance) :
    originalDirectedHamiltonianCircuitProblem.accepts input ↔
      originalUndirectedHamiltonianCircuitProblem.accepts (finalRoute.program.run input) :=
  finalRoute.correct input

/-- Final direct-TM evidence is compiler output for the composite program. -/
@[simp] theorem finalRoute_directTM :
    finalRoute.directTM = finalRoute.program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM finalRoute

/-- Final cost is compiler-derived from that same composite program. -/
@[simp] theorem finalRoute_compatibilityCost :
    finalRoute.compatibilityCost = finalRoute.program.compatibilityCost :=
  CertifiedReduction.compatibilityCost_eq_program_compatibilityCost finalRoute

/-- The shared-gadget program is exactly its direct-TM primitive atom. -/
@[simp] theorem sharedGadget_program :
    sharedGadget.program = PolyProg.atom sharedGadgetPrimitive :=
  rfl

/-- Shared direct-TM evidence is compiler output for its one atom program. -/
@[simp] theorem sharedGadget_directTM :
    sharedGadget.directTM = sharedGadget.program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM sharedGadget

/-- The shared gadget's compiler output is exactly CR's checked direct-TM witness. -/
@[simp] theorem sharedGadget_compileTM_eq_legacy :
    sharedGadget.program.compileTM = legacySharedGadgetTMKarpReduction.polytime :=
  rfl

/-- The shared gadget retains CR's exact named direct-TM provenance. -/
@[simp] theorem sharedGadget_directTM_eq_legacy :
    sharedGadget.directTM = legacySharedGadgetTMKarpReduction.polytime :=
  sharedGadget_directTM.trans sharedGadget_compileTM_eq_legacy

/-- The compiler comparison reaches CR's named structured direct-TM Karp record. -/
@[simp] theorem sharedGadget_compileTM_eq_namedCRStructuredTMKarpReduction :
    sharedGadget.program.compileTM =
      ComplexityReduction.Karp21.UndirectedHamiltonianCircuit.directedToUndirectedHamiltonianCircuitStructuredTMKarpReduction.polytime :=
  Subsingleton.elim _ _

/-- The shared gadget's direct-TM field has the same exact named CR provenance. -/
@[simp] theorem sharedGadget_directTM_eq_namedCRStructuredTMKarpReduction :
    sharedGadget.directTM =
      ComplexityReduction.Karp21.UndirectedHamiltonianCircuit.directedToUndirectedHamiltonianCircuitStructuredTMKarpReduction.polytime :=
  sharedGadget_directTM.trans sharedGadget_compileTM_eq_namedCRStructuredTMKarpReduction

end DirectedHamiltonianCircuitToUndirectedHamiltonianCircuit
end Routes
end ComplexityReduction
