/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.StructuredChains
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Provenance
import ComplexityReduction.Problems.Karp21.GraphAtoms
import ComplexityReduction.Problems.Karp21.Satisfiability
import ComplexityReduction.Protocol.ComponentRequest

/-!
Component-first structured 3SAT-to-Clique route.

CR supplies a standard-axiom checked direct-TM Karp construction at the exact
structured 3SAT and Clique endpoints.  V2 exposes it only as the reusable
3SAT-hub-to-Clique-hub component.  The public route is the thin composition
of a typed ingress identity with that shared gadget, and its identity egress
is represented by `CertifiedRouteProvenance`.

No whole-route primitive, named route program, route-wide certificate,
route-local machine, cost map, resolver, legacy certificate facade, or
metadata capability is introduced.  The shared gadget program is the common
identity for execution, semantics, direct-TM, and cost.
-/

namespace ComplexityReduction
namespace Routes
namespace ThreeSATToClique

open Annotations Certificate Encoding Program

/-- The original exact structured 3SAT source endpoint. -/
abbrev originalThreeSATProblem : PresentedProblem :=
  Problems.Karp21.Satisfiability.threeSATStructuredProblem

/-- The canonical structured 3SAT hub is the full original source endpoint. -/
abbrev threeSATHubProblem : PresentedProblem :=
  Problems.Karp21.Satisfiability.threeSATStructuredProblem

/-- The canonical structured Clique hub reached by CR's direct-TM construction. -/
abbrev cliqueHubProblem : PresentedProblem :=
  Problems.Karp21.GraphAtoms.cliqueStructuredProblem

/-- The public structured Clique target is already the complete canonical hub. -/
abbrev originalCliqueProblem : PresentedProblem :=
  Problems.Karp21.GraphAtoms.cliqueStructuredProblem

/-- The exact identity-eligible ingress endpoint into the 3SAT hub. -/
abbrev ThreeSATIngressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .ingress originalThreeSATProblem threeSATHubProblem

/-- The unique ingress request fixes its complete presented endpoints. -/
def threeSATIngressRequest : ThreeSATIngressEndpoint :=
  .exact

/-- Ingress is identity-eligible only because the complete endpoints agree. -/
theorem threeSATIngress_endpoints_eq :
    originalThreeSATProblem = threeSATHubProblem :=
  rfl

/-- The exact reusable 3SAT-to-Clique shared-gadget endpoint. -/
abbrev SharedGadgetEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .sharedGadget threeSATHubProblem cliqueHubProblem

/-- The unique request for the standard direct-TM shared gadget. -/
def sharedGadgetRequest : SharedGadgetEndpoint :=
  .exact

/-- The exact identity-eligible Clique-hub-to-public-target egress endpoint. -/
abbrev CliqueEgressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .egress cliqueHubProblem originalCliqueProblem

/-- The unique egress request fixes its complete presented endpoints. -/
def cliqueEgressRequest : CliqueEgressEndpoint :=
  .exact

/-- Egress is identity-eligible only because the complete endpoints agree. -/
theorem cliqueEgress_endpoints_eq : cliqueHubProblem = originalCliqueProblem :=
  rfl

/--
Read-only CR direct-TM Karp witness at the reusable hub endpoints.  It is an
audit source only: V2's certificate below starts from its executable and
direct-TM field, never from a legacy cost map or certificate facade.
-/
noncomputable def legacySharedGadgetTMKarpReduction :
    ComplexityReduction.TMKarpReduction threeSATHubProblem.toEncodedDecisionProblem
      cliqueHubProblem.toEncodedDecisionProblem := by
  simpa [threeSATHubProblem, cliqueHubProblem] using
    ComplexityReduction.Karp21.Clique.threeSATToCliqueStructuredTMKarpReduction

/-- The read-only audit projection is exactly CR's named structured direct-TM record. -/
@[simp] theorem legacySharedGadgetTMKarpReduction_eq_CR :
    legacySharedGadgetTMKarpReduction =
      ComplexityReduction.Karp21.Clique.threeSATToCliqueStructuredTMKarpReduction :=
  rfl

/-- The sole primitive for the reusable shared gadget reuses CR's executable and TM evidence. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def sharedGadgetPrimitive :
    Primitive threeSATHubProblem.representation cliqueHubProblem.representation :=
  Primitive.ofTMPolyTime legacySharedGadgetTMKarpReduction.f
    legacySharedGadgetTMKarpReduction.polytime

/-- The shared gadget owns one direct-TM atom program. -/
noncomputable def sharedGadgetProgram :
    PolyProg threeSATHubProblem.representation cliqueHubProblem.representation :=
  .atom sharedGadgetPrimitive

/-- The shared program executes CR's checked structured map. -/
@[simp] theorem sharedGadgetProgram_run (input : threeSATHubProblem.Instance) :
    sharedGadgetProgram.run input = legacySharedGadgetTMKarpReduction.f input :=
  rfl

/-- The semantic law is indexed by that same shared-gadget executable. -/
theorem sharedGadget_correct (input : threeSATHubProblem.Instance) :
    threeSATHubProblem.accepts input ↔
      cliqueHubProblem.accepts (sharedGadgetProgram.run input) := by
  simpa only [sharedGadgetProgram_run] using legacySharedGadgetTMKarpReduction.correct input

/-- The exact source ingress is a typed certificate, not a bare endpoint equality. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_ingress]
noncomputable def ingress : CertifiedReduction originalThreeSATProblem threeSATHubProblem :=
  .refl threeSATHubProblem

/-- The CR construction is the sole reusable 3SAT-to-Clique shared-gadget certificate. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def sharedGadget : CertifiedReduction threeSATHubProblem cliqueHubProblem where
  program := sharedGadgetProgram
  correct := sharedGadget_correct

/-- The public route is only the required composition of ingress and shared gadget. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def finalRoute :
    CertifiedReduction originalThreeSATProblem originalCliqueProblem :=
  CertifiedReduction.comp sharedGadget ingress

/-- Typed provenance records that the Clique egress is the exact identity endpoint. -/
@[complexity_reduction_ir_typed_edge]
noncomputable def finalRouteProvenance :
    CertifiedRouteProvenance ingress sharedGadget .identity finalRoute :=
  CertifiedRouteProvenance.identityEgress ingress sharedGadget

/-- The final program is definitionally the mandated component composition. -/
@[simp] theorem finalRoute_program :
    finalRoute.program = PolyProg.comp sharedGadget.program ingress.program :=
  rfl

/-- The final executable is the sequential execution of the component programs. -/
@[simp] theorem finalRoute_run (input : originalThreeSATProblem.Instance) :
    finalRoute.program.run input =
      sharedGadget.program.run (ingress.program.run input) :=
  rfl

/-- The final semantic law is inherited from the composed component certificates. -/
theorem finalRoute_correct (input : originalThreeSATProblem.Instance) :
    originalThreeSATProblem.accepts input ↔
      originalCliqueProblem.accepts (finalRoute.program.run input) :=
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
      ComplexityReduction.Karp21.Clique.threeSATToCliqueStructuredTMKarpReduction.polytime :=
  Subsingleton.elim _ _

/-- The shared gadget's direct-TM field has the same exact named CR provenance. -/
@[simp] theorem sharedGadget_directTM_eq_namedCRStructuredTMKarpReduction :
    sharedGadget.directTM =
      ComplexityReduction.Karp21.Clique.threeSATToCliqueStructuredTMKarpReduction.polytime :=
  sharedGadget_directTM.trans sharedGadget_compileTM_eq_namedCRStructuredTMKarpReduction

end ThreeSATToClique
end Routes
end ComplexityReduction
