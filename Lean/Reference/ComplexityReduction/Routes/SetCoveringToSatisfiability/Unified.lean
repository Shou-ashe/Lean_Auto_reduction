/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.SetCoveringToSatisfiabilityStandardTM
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Provenance
import ComplexityReduction.Protocol.ComponentResolver

/-!
Component-first structured Set-Covering-to-Satisfiability route.

The compact CNF construction is owned by the domain leaf at the exact
bound-preserving Set-Covering and structured-CNF hubs.  This public route
contains no whole-route primitive, map, cost witness, or machine; it only
composes the two exact endpoint identities with that shared certificate.
-/

namespace ComplexityReduction
namespace Routes
namespace SetCoveringToSatisfiability

open Certificate Encoding Program

/-- The original structured Set-Covering endpoint. -/
abbrev originalSetCoveringProblem : PresentedProblem :=
  Presentation.SetSystem.setCoveringStructuredProblem

/-- The canonical set-system source hub retains the complete source input and bound. -/
abbrev setCoveringHubProblem : PresentedProblem :=
  Presentation.SetSystem.setCoveringStructuredProblem

/-- The canonical structured CNF/SAT target hub. -/
abbrev clauseHubProblem : PresentedProblem :=
  Presentation.Satisfiability.structuredProblem

/-- The public structured SAT target is already the canonical Clause hub. -/
abbrev originalSatisfiabilityProblem : PresentedProblem :=
  Presentation.Satisfiability.structuredProblem

abbrev SetCoveringIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress originalSetCoveringProblem setCoveringHubProblem
abbrev SharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget setCoveringHubProblem clauseHubProblem
abbrev SatisfiabilityEgressRequest : Type 2 :=
  Protocol.ComponentRequest .egress clauseHubProblem originalSatisfiabilityProblem
abbrev FinalCompositionRequest : Type 2 :=
  Protocol.ComponentRequest .finalComposition originalSetCoveringProblem originalSatisfiabilityProblem

def setCoveringIngressRequest : SetCoveringIngressRequest := .exact
def sharedGadgetRequest : SharedGadgetRequest := .exact
def satisfiabilityEgressRequest : SatisfiabilityEgressRequest := .exact
def finalCompositionRequest : FinalCompositionRequest := .exact

theorem setCoveringIngress_endpoints_eq :
    originalSetCoveringProblem = setCoveringHubProblem := rfl
theorem satisfiabilityEgress_endpoints_eq :
    clauseHubProblem = originalSatisfiabilityProblem := rfl
theorem setCoveringIngressRequest_endpoint_exact :
    setCoveringIngressRequest.endpoint =
      (show Protocol.ComponentEndpoint .ingress
        originalSetCoveringProblem setCoveringHubProblem from .exact) := rfl
theorem sharedGadgetRequest_endpoint_exact :
    sharedGadgetRequest.endpoint =
      (show Protocol.ComponentEndpoint .sharedGadget
        setCoveringHubProblem clauseHubProblem from .exact) := rfl
theorem satisfiabilityEgressRequest_endpoint_exact :
    satisfiabilityEgressRequest.endpoint =
      (show Protocol.ComponentEndpoint .egress
        clauseHubProblem originalSatisfiabilityProblem from .exact) := rfl
theorem finalCompositionRequest_endpoint_exact :
    finalCompositionRequest.endpoint =
      (show Protocol.ComponentEndpoint .finalComposition
        originalSetCoveringProblem originalSatisfiabilityProblem from .exact) := rfl

/-- Exact ingress is eligible only because the full source endpoints coincide. -/
noncomputable def ingress :
    CertifiedReduction originalSetCoveringProblem setCoveringHubProblem :=
  .refl setCoveringHubProblem

/-- Exact egress is eligible only because the full target endpoints coincide. -/
noncomputable def egress :
    CertifiedReduction clauseHubProblem originalSatisfiabilityProblem :=
  .refl clauseHubProblem

noncomputable def setCoveringIngressResolution :
    Protocol.ComponentResolution .ingress originalSetCoveringProblem setCoveringHubProblem :=
  Protocol.ComponentResolver.accept setCoveringIngressRequest ingress

noncomputable def satisfiabilityEgressResolution :
    Protocol.ComponentResolution .egress clauseHubProblem originalSatisfiabilityProblem :=
  Protocol.ComponentResolver.accept satisfiabilityEgressRequest egress

/-- The public route reuses the one standard-audited compact hub certificate. -/
noncomputable def sharedGadget :
    CertifiedReduction setCoveringHubProblem clauseHubProblem :=
  Domain.SetCoveringToSatisfiabilityStandardTM.sharedGadget

noncomputable def sharedGadgetResolution :
    Protocol.ComponentResolution .sharedGadget setCoveringHubProblem clauseHubProblem :=
  Protocol.ComponentResolver.accept sharedGadgetRequest sharedGadget

/-- The public route is exactly the ingress/shared/egress certificate composition. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def finalRoute :
    CertifiedReduction originalSetCoveringProblem originalSatisfiabilityProblem :=
  CertifiedReduction.comp egress (CertifiedReduction.comp sharedGadget ingress)

/-- Typed provenance fixes the independently reusable three-component path. -/
@[complexity_reduction_ir_typed_edge]
noncomputable def finalRouteProvenance :
    CertifiedRouteProvenance ingress sharedGadget (.explicit egress) finalRoute :=
  CertifiedRouteProvenance.explicitEgress ingress sharedGadget egress

/-- Resolve the exact component path into its request-indexed accepted result. -/
noncomputable def resolveComponentRoute :
    Protocol.ResolverOutcome originalSetCoveringProblem originalSatisfiabilityProblem :=
  Protocol.ComponentResolver.composeIngressSharedEgress finalCompositionRequest
    setCoveringIngressResolution sharedGadgetResolution satisfiabilityEgressResolution

@[simp] theorem setCoveringIngressResolution_exact :
    setCoveringIngressResolution = .accepted ingress := rfl
@[simp] theorem satisfiabilityEgressResolution_exact :
    satisfiabilityEgressResolution = .accepted egress := rfl
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
@[simp] theorem resolveComponentRoute_exact :
    resolveComponentRoute = .accepted finalRoute := rfl

end SetCoveringToSatisfiability
end Routes
end ComplexityReduction
