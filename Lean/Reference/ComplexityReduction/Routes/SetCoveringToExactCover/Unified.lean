/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.CNFToThreeSATStandardTM
import ComplexityReduction.Domain.GraphColoringToIncidenceGadget
import ComplexityReduction.Domain.IncidenceIRToStructuredExactCoverStandardTM
import ComplexityReduction.Domain.SetCoveringToSatisfiabilityStandardTM
import ComplexityReduction.Domain.ThreeSATToGraphColoringStandardTM
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.SetSystem
import ComplexityReduction.Certificate.Provenance
import ComplexityReduction.Protocol.ComponentResolver

/-!
Component-first boundary for structured Set Covering to Exact Cover.

The source's bound-preserving Set-Covering hub reaches the canonical typed
incidence Exact-Cover hub through four independently reusable components:
compact CNF, CNF-to-3SAT, 3SAT-to-graph-colouring, and graph-colouring-to-
incidence.  The public route contains only their `CertifiedReduction.comp`
composition with the independently owned IncidenceIR-to-structured-Exact-Cover
egress.  No source-to-target primitive, route-local TM, cost map, packet,
provider, slot, or descriptor is introduced.
-/

namespace ComplexityReduction
namespace Routes
namespace SetCoveringToExactCover

open Certificate Encoding Program

/-- The original structured Set-Covering endpoint. -/
abbrev originalSetCoveringProblem : PresentedProblem :=
  Presentation.SetSystem.setCoveringStructuredProblem

/-- The bound-preserving canonical Set-Covering hub. -/
abbrev setCoveringHubProblem : PresentedProblem :=
  Presentation.SetSystem.setCoveringStructuredProblem

/-- The canonical structured CNF/SAT hub. -/
abbrev cnfHubProblem : PresentedProblem :=
  Presentation.Satisfiability.structuredProblem

/-- The canonical structured bundled-3SAT hub. -/
abbrev threeSATHubProblem : PresentedProblem :=
  Problems.Karp21.Satisfiability.threeSATStructuredProblem

/-- The canonical graph-and-colour-bound hub. -/
abbrev graphColoringHubProblem : PresentedProblem :=
  Domain.GraphColoringIR.chromaticNumberProblem

/-- The canonical typed incidence Exact-Cover hub. -/
abbrev incidenceHubProblem : PresentedProblem :=
  Domain.IncidenceIR.exactCoverProblem

/-- The public structured Exact-Cover endpoint. -/
abbrev originalExactCoverProblem : PresentedProblem :=
  Presentation.SetSystem.exactCoverStructuredProblem

abbrev SetCoveringIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress originalSetCoveringProblem setCoveringHubProblem
abbrev SetCoveringCNFRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget setCoveringHubProblem cnfHubProblem
abbrev CNFThreeSATRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget cnfHubProblem threeSATHubProblem
abbrev ThreeSATGraphRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget threeSATHubProblem graphColoringHubProblem
abbrev GraphIncidenceRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget graphColoringHubProblem incidenceHubProblem
abbrev ExactCoverEgressRequest : Type 2 :=
  Protocol.ComponentRequest .egress incidenceHubProblem originalExactCoverProblem
abbrev FinalCompositionRequest : Type 2 :=
  Protocol.ComponentRequest .finalComposition originalSetCoveringProblem originalExactCoverProblem

def setCoveringIngressRequest : SetCoveringIngressRequest := .exact
def setCoveringCNFRequest : SetCoveringCNFRequest := .exact
def cnfThreeSATRequest : CNFThreeSATRequest := .exact
def threeSATGraphRequest : ThreeSATGraphRequest := .exact
def graphIncidenceRequest : GraphIncidenceRequest := .exact
def exactCoverEgressRequest : ExactCoverEgressRequest := .exact
def finalCompositionRequest : FinalCompositionRequest := .exact

theorem setCoveringIngress_endpoints_eq :
    originalSetCoveringProblem = setCoveringHubProblem := rfl

/-- Exact ingress is structural identity only because its complete endpoints coincide. -/
noncomputable def ingress : CertifiedReduction originalSetCoveringProblem setCoveringHubProblem :=
  .refl setCoveringHubProblem

/-- The reusable compact Set-Covering-to-CNF hub gadget. -/
noncomputable def setCoveringToCNF : CertifiedReduction setCoveringHubProblem cnfHubProblem :=
  Domain.SetCoveringToSatisfiabilityStandardTM.sharedGadget

/-- The reusable standard-audited structured CNF-to-3SAT hub gadget. -/
noncomputable def cnfToThreeSAT : CertifiedReduction cnfHubProblem threeSATHubProblem :=
  Domain.CNFToThreeSATStandardTM.sharedGadget

/-- The reusable standard-audited structured 3SAT-to-graph-colouring hub gadget. -/
noncomputable def threeSATToGraph :
    CertifiedReduction threeSATHubProblem graphColoringHubProblem :=
  Domain.ThreeSATToGraphColoringStandardTM.sharedGadget

/-- The reusable graph-colouring-to-incidence Exact-Cover hub gadget. -/
def graphToIncidence : CertifiedReduction graphColoringHubProblem incidenceHubProblem :=
  Domain.GraphColoringToIncidenceGadget.sharedGadget

/-- The only accepted Set-Covering ingress component. -/
noncomputable def setCoveringIngressResolution :
    Protocol.ComponentResolution .ingress originalSetCoveringProblem setCoveringHubProblem :=
  Protocol.ComponentResolver.accept setCoveringIngressRequest ingress

/-- Each interior edge is resolved at its own exact typed hubs. -/
noncomputable def setCoveringCNFResolution :
    Protocol.ComponentResolution .sharedGadget setCoveringHubProblem cnfHubProblem :=
  Protocol.ComponentResolver.accept setCoveringCNFRequest setCoveringToCNF

noncomputable def cnfThreeSATResolution :
    Protocol.ComponentResolution .sharedGadget cnfHubProblem threeSATHubProblem :=
  Protocol.ComponentResolver.accept cnfThreeSATRequest cnfToThreeSAT

noncomputable def threeSATGraphResolution :
    Protocol.ComponentResolution .sharedGadget threeSATHubProblem graphColoringHubProblem :=
  Protocol.ComponentResolver.accept threeSATGraphRequest threeSATToGraph

def graphIncidenceResolution :
    Protocol.ComponentResolution .sharedGadget graphColoringHubProblem incidenceHubProblem :=
  Protocol.ComponentResolver.accept graphIncidenceRequest graphToIncidence

/-- The completed shared prefix is only a composition of independently owned components. -/
noncomputable def sharedHubPath : CertifiedReduction setCoveringHubProblem incidenceHubProblem :=
  CertifiedReduction.comp graphToIncidence
    (CertifiedReduction.comp threeSATToGraph
      (CertifiedReduction.comp cnfToThreeSAT setCoveringToCNF))

@[simp] theorem sharedHubPath_program :
    sharedHubPath.program =
      PolyProg.comp graphToIncidence.program
        (PolyProg.comp threeSATToGraph.program
          (PolyProg.comp cnfToThreeSAT.program setCoveringToCNF.program)) :=
  rfl

@[simp] theorem sharedHubPath_directTM :
    sharedHubPath.directTM = sharedHubPath.program.compileTM :=
  rfl

/-- This resolver result merely packages the completed composed prefix; it grants no new atom. -/
noncomputable def sharedHubPathResolution :
    Protocol.ComponentResolution .sharedGadget setCoveringHubProblem incidenceHubProblem :=
  .accepted sharedHubPath

/-- The independently reusable incidence-hub target realization. -/
def egress : CertifiedReduction incidenceHubProblem originalExactCoverProblem :=
  Domain.IncidenceIRToStructuredExactCoverStandardTM.egress

def exactCoverEgressResolution :
    Protocol.ComponentResolution .egress incidenceHubProblem originalExactCoverProblem :=
  Protocol.ComponentResolver.accept exactCoverEgressRequest egress

/-- The public route is only the completed prefix composed with the egress component. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def finalRoute :
    CertifiedReduction originalSetCoveringProblem originalExactCoverProblem :=
  CertifiedReduction.comp egress (CertifiedReduction.comp sharedHubPath ingress)

/-- Typed provenance records the outer ingress, shared hub path, and egress declarations. -/
@[complexity_reduction_ir_typed_edge]
noncomputable def finalRouteProvenance :
    CertifiedRouteProvenance ingress sharedHubPath (.explicit egress) finalRoute :=
  CertifiedRouteProvenance.explicitEgress ingress sharedHubPath egress

abbrev RouteResolution : Type 2 :=
  Protocol.ResolverOutcome originalSetCoveringProblem originalExactCoverProblem

/-- The final resolver composes the accepted egress after the completed shared path. -/
noncomputable def resolveComponentRoute : RouteResolution :=
  Protocol.ComponentResolver.composeIngressSharedEgress finalCompositionRequest
    setCoveringIngressResolution sharedHubPathResolution exactCoverEgressResolution

@[simp] theorem setCoveringIngressResolution_exact :
    setCoveringIngressResolution = .accepted ingress := rfl
@[simp] theorem setCoveringCNFResolution_exact :
    setCoveringCNFResolution = .accepted setCoveringToCNF := rfl
@[simp] theorem cnfThreeSATResolution_exact :
    cnfThreeSATResolution = .accepted cnfToThreeSAT := rfl
@[simp] theorem threeSATGraphResolution_exact :
    threeSATGraphResolution = .accepted threeSATToGraph := rfl
@[simp] theorem graphIncidenceResolution_exact :
    graphIncidenceResolution = .accepted graphToIncidence := rfl
@[simp] theorem sharedHubPathResolution_exact :
    sharedHubPathResolution = .accepted sharedHubPath := rfl
@[simp] theorem exactCoverEgressResolution_exact :
    exactCoverEgressResolution = .accepted egress := rfl
@[simp] theorem finalRoute_program :
    finalRoute.program =
      PolyProg.comp egress.program
        (PolyProg.comp sharedHubPath.program ingress.program) := rfl
@[simp] theorem finalRoute_directTM :
    finalRoute.directTM = finalRoute.program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM finalRoute
@[simp] theorem resolveComponentRoute_exact :
    resolveComponentRoute = .accepted finalRoute := rfl

end SetCoveringToExactCover
end Routes
end ComplexityReduction
