/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Clique.Part10
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Provenance
import ComplexityReduction.Problems.Karp21.GraphAtoms
import ComplexityReduction.Problems.Karp21.Satisfiability
import ComplexityReduction.Protocol.ComponentResolver

/-!
Component-first structured CNF-Satisfiability-to-Clique route.

CR supplies one checked direct-TM Karp construction at the exact structured
CNF-SAT and Clique hubs.  V2 admits that existing construction once through
the shared certificate adapter.  The public route is only a typed ingress
composition; identity egress is carried by `CertifiedRouteProvenance`.
No route-local primitive, program, machine, cost, metadata authority, or
whole-route request language is declared here.
-/

namespace ComplexityReduction
namespace Routes
namespace SatisfiabilityToClique

open Annotations Certificate Encoding Program

/-- The original exact structured CNF-SAT source endpoint. -/
abbrev originalSatisfiabilityProblem : PresentedProblem :=
  Problems.Karp21.Satisfiability.cnfSATStructuredProblem

/-- The canonical structured CNF-SAT hub is the full original source endpoint. -/
abbrev cnfSATHubProblem : PresentedProblem :=
  Problems.Karp21.Satisfiability.cnfSATStructuredProblem

/-- The canonical structured Clique hub reached by the direct CR construction. -/
abbrev cliqueHubProblem : PresentedProblem :=
  Problems.Karp21.GraphAtoms.cliqueStructuredProblem

/-- The public structured Clique target is already the complete Clique hub. -/
abbrev originalCliqueProblem : PresentedProblem :=
  Problems.Karp21.GraphAtoms.cliqueStructuredProblem

/-- The exact identity-eligible ingress endpoint into the CNF-SAT hub. -/
abbrev SatisfiabilityIngressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .ingress originalSatisfiabilityProblem cnfSATHubProblem

/-- The canonical request for the exact CNF-SAT ingress component. -/
abbrev SatisfiabilityIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress originalSatisfiabilityProblem cnfSATHubProblem

/-- The unique request for the exact CNF-SAT ingress. -/
def satisfiabilityIngressRequest : SatisfiabilityIngressRequest :=
  .exact

/-- Ingress is identity-eligible only because the complete endpoints agree. -/
theorem satisfiabilityIngress_endpoints_eq :
    originalSatisfiabilityProblem = cnfSATHubProblem :=
  rfl

/-- The exact reusable CNF-SAT-to-Clique shared-gadget endpoint. -/
abbrev SharedGadgetEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .sharedGadget cnfSATHubProblem cliqueHubProblem

/-- The canonical request for the reusable CNF-SAT-to-Clique shared gadget. -/
abbrev SharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget cnfSATHubProblem cliqueHubProblem

/-- The unique request for the standard direct-TM shared gadget. -/
def sharedGadgetRequest : SharedGadgetRequest :=
  .exact

/-- The exact identity-eligible Clique-hub-to-public-target egress endpoint. -/
abbrev CliqueEgressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .egress cliqueHubProblem originalCliqueProblem

/-- The canonical request for the exact Clique egress component. -/
abbrev CliqueEgressRequest : Type 2 :=
  Protocol.ComponentRequest .egress cliqueHubProblem originalCliqueProblem

/-- The unique Clique egress request. -/
def cliqueEgressRequest : CliqueEgressRequest :=
  .exact

/-- Egress is identity-eligible only because the complete endpoints agree. -/
theorem cliqueEgress_endpoints_eq : cliqueHubProblem = originalCliqueProblem :=
  rfl

/-- The exact request for the final component composition endpoint. -/
abbrev FinalCompositionRequest : Type 2 :=
  Protocol.ComponentRequest .finalComposition originalSatisfiabilityProblem originalCliqueProblem

/-- The final request fixes endpoints only; it carries no executable authority. -/
def finalCompositionRequest : FinalCompositionRequest :=
  .exact

/--
Read-only CR direct-TM Karp witness at the reusable hub endpoints.

This is the only direct-TM source admitted by the shared certificate; its
legacy cost facade is not an input to V2 route authority.
-/
noncomputable def legacySharedGadgetTMKarpReduction :
    ComplexityReduction.TMKarpReduction cnfSATHubProblem.toEncodedDecisionProblem
      cliqueHubProblem.toEncodedDecisionProblem := by
  simpa [cnfSATHubProblem, cliqueHubProblem] using
    ComplexityReduction.Karp21.Clique.satisfiabilityToCliqueStructuredTMKarpReduction

/-- The audit alias is exactly CR's named structured direct-TM record. -/
@[simp] theorem legacySharedGadgetTMKarpReduction_eq_CR :
    legacySharedGadgetTMKarpReduction =
      ComplexityReduction.Karp21.Clique.satisfiabilityToCliqueStructuredTMKarpReduction :=
  rfl

/-- The CR construction is the sole reusable CNF-SAT-to-Clique hub primitive. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def sharedGadgetPrimitive :
    Primitive cnfSATHubProblem.representation cliqueHubProblem.representation :=
  Primitive.ofTMPolyTime legacySharedGadgetTMKarpReduction.f
    legacySharedGadgetTMKarpReduction.polytime

/-- The one shared-gadget program is precisely the direct-TM hub primitive atom. -/
noncomputable def sharedGadgetProgram :
    PolyProg cnfSATHubProblem.representation cliqueHubProblem.representation :=
  .atom sharedGadgetPrimitive

/-- The shared program executes exactly CR's direct-TM Karp map. -/
@[simp] theorem sharedGadgetProgram_run (input : cnfSATHubProblem.Instance) :
    sharedGadgetProgram.run input = legacySharedGadgetTMKarpReduction.f input :=
  rfl

/-- The CR semantic iff is indexed by the exact shared-gadget executable. -/
theorem sharedGadgetProgram_correct (input : cnfSATHubProblem.Instance) :
    cnfSATHubProblem.accepts input ↔
      cliqueHubProblem.accepts (sharedGadgetProgram.run input) :=
  legacySharedGadgetTMKarpReduction.correct input

/-- The shared direct-TM compiler output is the exact CR witness. -/
@[simp] theorem sharedGadgetProgram_compileTM_eq_legacy :
    sharedGadgetProgram.compileTM = legacySharedGadgetTMKarpReduction.polytime :=
  rfl

/-- The CR construction is the sole reusable CNF-SAT-to-Clique shared certificate. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def sharedGadget : CertifiedReduction cnfSATHubProblem cliqueHubProblem where
  program := sharedGadgetProgram
  correct := sharedGadgetProgram_correct

/-- The shared certificate stores exactly CR's direct-TM atom. -/
@[simp] theorem sharedGadget_program :
    sharedGadget.program = PolyProg.atom sharedGadgetPrimitive :=
  rfl

/-- The shared program executes CR's checked structured map. -/
@[simp] theorem sharedGadget_run (input : cnfSATHubProblem.Instance) :
    sharedGadget.program.run input = legacySharedGadgetTMKarpReduction.f input :=
  rfl

/-- The semantic law is indexed by that same shared-gadget executable. -/
theorem sharedGadget_correct (input : cnfSATHubProblem.Instance) :
    cnfSATHubProblem.accepts input ↔
      cliqueHubProblem.accepts (sharedGadget.program.run input) :=
  sharedGadgetProgram_correct input

/-- The shared direct-TM field is compiler output for its one stored program. -/
@[simp] theorem sharedGadget_directTM :
    sharedGadget.directTM = sharedGadget.program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM sharedGadget

/-- The shared compiler retains exactly CR's existing direct-TM witness. -/
@[simp] theorem sharedGadget_compileTM_eq_legacy :
    sharedGadget.program.compileTM = legacySharedGadgetTMKarpReduction.polytime :=
  rfl

/-- The shared direct-TM field has the exact audited CR provenance. -/
@[simp] theorem sharedGadget_directTM_eq_legacy :
    sharedGadget.directTM = legacySharedGadgetTMKarpReduction.polytime :=
  rfl

/-- The compiler reaches CR's named structured direct-TM Karp record. -/
@[simp] theorem sharedGadget_compileTM_eq_namedCRStructuredTMKarpReduction :
    sharedGadget.program.compileTM =
      ComplexityReduction.Karp21.Clique.satisfiabilityToCliqueStructuredTMKarpReduction.polytime :=
  rfl

/-- The shared direct-TM field has the same exact named CR provenance. -/
@[simp] theorem sharedGadget_directTM_eq_namedCRStructuredTMKarpReduction :
    sharedGadget.directTM =
      ComplexityReduction.Karp21.Clique.satisfiabilityToCliqueStructuredTMKarpReduction.polytime :=
  rfl

/-- The CR construction is accepted only at its exact shared-gadget endpoint. -/
noncomputable def satisfiabilityToCliqueSharedGadgetResolution :
    Protocol.ComponentResolution .sharedGadget cnfSATHubProblem cliqueHubProblem :=
  Protocol.ComponentResolver.accept sharedGadgetRequest sharedGadget

/-- The exact source ingress is a typed certificate, not a bare endpoint equality. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_ingress]
noncomputable def ingress : CertifiedReduction originalSatisfiabilityProblem cnfSATHubProblem :=
  .refl cnfSATHubProblem

/-- The public route is only the required composition of ingress and shared gadget. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def finalRoute :
    CertifiedReduction originalSatisfiabilityProblem originalCliqueProblem :=
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
@[simp] theorem finalRoute_run (input : originalSatisfiabilityProblem.Instance) :
    finalRoute.program.run input =
      sharedGadget.program.run (ingress.program.run input) :=
  rfl

/-- The final semantic law is inherited from the composed component certificates. -/
theorem finalRoute_correct (input : originalSatisfiabilityProblem.Instance) :
    originalSatisfiabilityProblem.accepts input ↔
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

/-- The resolver path reifies exactly the accepted shared-gadget capability. -/
noncomputable def resolveComponentPath :
    Protocol.ResolverOutcome originalSatisfiabilityProblem originalCliqueProblem :=
  Protocol.ComponentResolver.resolveSingle satisfiabilityToCliqueSharedGadgetResolution

/-- The component resolution retains exactly the canonical shared certificate. -/
@[simp] theorem satisfiabilityToCliqueSharedGadgetResolution_exact :
    satisfiabilityToCliqueSharedGadgetResolution = .accepted sharedGadget :=
  rfl

/-- The component path yields precisely the accepted shared-gadget certificate. -/
@[simp] theorem resolveComponentPath_exact :
    resolveComponentPath = .accepted sharedGadget :=
  rfl

end SatisfiabilityToClique
end Routes
end ComplexityReduction
