/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.GraphColoringToChromaticNumberAdapter
import ComplexityReduction.Domain.ThreeSATToGraphColoringStandardTM
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Provenance
import ComplexityReduction.Problems.Karp21.Satisfiability
import ComplexityReduction.Protocol.ComponentResolver

/-!
Component-first structured 3SAT-to-Chromatic-Number route.

The standard-audited Clause-to-GraphColoring direct-TM gadget is owned by its
domain leaf; this public route only composes the exact source ingress, that
shared hub certificate, and the explicit GraphColoring-to-ChromaticNumber
egress.  It declares no whole-route primitive or route-local machine.
-/

namespace ComplexityReduction
namespace Routes
namespace ThreeSATToChromaticNumber

open Certificate Encoding Program

abbrev originalThreeSATProblem : PresentedProblem :=
  Problems.Karp21.Satisfiability.threeSATStructuredProblem
abbrev clauseHubProblem : PresentedProblem :=
  Problems.Karp21.Satisfiability.threeSATStructuredProblem
abbrev graphColoringHubProblem : PresentedProblem :=
  Domain.GraphColoringIR.chromaticNumberProblem
abbrev finalChromaticNumberProblem : PresentedProblem :=
  Domain.GraphColoringToChromaticNumberAdapter.targetProblem

abbrev ThreeSATIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress originalThreeSATProblem clauseHubProblem
abbrev SharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget clauseHubProblem graphColoringHubProblem
abbrev ChromaticNumberEgressRequest : Type 2 :=
  Protocol.ComponentRequest .egress graphColoringHubProblem finalChromaticNumberProblem
abbrev FinalCompositionRequest : Type 2 :=
  Protocol.ComponentRequest .finalComposition originalThreeSATProblem finalChromaticNumberProblem

def threeSATIngressRequest : ThreeSATIngressRequest := .exact
def sharedGadgetRequest : SharedGadgetRequest := .exact
def chromaticNumberEgressRequest : ChromaticNumberEgressRequest := .exact
def finalCompositionRequest : FinalCompositionRequest := .exact

theorem threeSATIngress_endpoints_eq : originalThreeSATProblem = clauseHubProblem := rfl
theorem chromaticNumberEgress_endpoints_eq :
    graphColoringHubProblem = Domain.GraphColoringToChromaticNumberAdapter.hubProblem := rfl
theorem threeSATIngressRequest_endpoint_exact :
    threeSATIngressRequest.endpoint =
      (show Protocol.ComponentEndpoint .ingress originalThreeSATProblem clauseHubProblem from .exact) := rfl
theorem sharedGadgetRequest_endpoint_exact :
    sharedGadgetRequest.endpoint =
      (show Protocol.ComponentEndpoint .sharedGadget clauseHubProblem graphColoringHubProblem from .exact) := rfl
theorem chromaticNumberEgressRequest_endpoint_exact :
    chromaticNumberEgressRequest.endpoint =
      (show Protocol.ComponentEndpoint .egress graphColoringHubProblem finalChromaticNumberProblem from .exact) := rfl
theorem finalCompositionRequest_endpoint_exact :
    finalCompositionRequest.endpoint =
      (show Protocol.ComponentEndpoint .finalComposition
        originalThreeSATProblem finalChromaticNumberProblem from .exact) := rfl

noncomputable def ingress : CertifiedReduction originalThreeSATProblem clauseHubProblem :=
  .refl clauseHubProblem
noncomputable def egress : CertifiedReduction graphColoringHubProblem finalChromaticNumberProblem :=
  Domain.GraphColoringToChromaticNumberAdapter.targetAdapter
noncomputable def threeSATIngressResolution :
    Protocol.ComponentResolution .ingress originalThreeSATProblem clauseHubProblem :=
  Protocol.ComponentResolver.accept threeSATIngressRequest ingress
noncomputable def chromaticNumberEgressResolution :
    Protocol.ComponentResolution .egress graphColoringHubProblem finalChromaticNumberProblem :=
  Protocol.ComponentResolver.accept chromaticNumberEgressRequest egress

/-- The route reuses the sole standard-audited Clause-to-GraphColoring hub certificate. -/
noncomputable def sharedGadget :
    CertifiedReduction clauseHubProblem graphColoringHubProblem :=
  Domain.ThreeSATToGraphColoringStandardTM.sharedGadget

noncomputable def sharedGadgetResolution :
    Protocol.ComponentResolution .sharedGadget clauseHubProblem graphColoringHubProblem :=
  Protocol.ComponentResolver.accept sharedGadgetRequest sharedGadget

/-- The public route is exactly the ingress/shared/explicit-egress composition. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def finalRoute :
    CertifiedReduction originalThreeSATProblem finalChromaticNumberProblem :=
  CertifiedReduction.comp egress (CertifiedReduction.comp sharedGadget ingress)

@[complexity_reduction_ir_typed_edge]
noncomputable def finalRouteProvenance :
    CertifiedRouteProvenance ingress sharedGadget (.explicit egress) finalRoute :=
  CertifiedRouteProvenance.explicitEgress ingress sharedGadget egress

noncomputable def resolveComponentPath :
    Protocol.ResolverOutcome originalThreeSATProblem finalChromaticNumberProblem :=
  Protocol.ComponentResolver.composeIngressSharedEgress finalCompositionRequest
    threeSATIngressResolution sharedGadgetResolution chromaticNumberEgressResolution

@[simp] theorem threeSATIngressResolution_exact :
    threeSATIngressResolution = .accepted ingress := rfl
@[simp] theorem chromaticNumberEgressResolution_exact :
    chromaticNumberEgressResolution = .accepted egress := rfl
@[simp] theorem sharedGadgetResolution_exact :
    sharedGadgetResolution = .accepted sharedGadget := rfl
@[simp] theorem finalRoute_program :
    finalRoute.program =
      PolyProg.comp egress.program (PolyProg.comp sharedGadget.program ingress.program) := rfl
@[simp] theorem finalRoute_directTM :
    finalRoute.directTM = finalRoute.program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM finalRoute
@[simp] theorem finalRoute_compatibilityCost :
    finalRoute.compatibilityCost = finalRoute.program.compatibilityCost :=
  CertifiedReduction.compatibilityCost_eq_program_compatibilityCost finalRoute
@[simp] theorem resolveComponentPath_exact :
    resolveComponentPath = .accepted finalRoute := rfl

end ThreeSATToChromaticNumber
end Routes
end ComplexityReduction
