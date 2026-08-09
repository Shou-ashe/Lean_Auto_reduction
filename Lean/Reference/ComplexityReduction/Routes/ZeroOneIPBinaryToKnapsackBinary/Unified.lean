/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.ZeroOneIPBinaryToKnapsackBinaryStandardTM
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Provenance
import ComplexityReduction.Protocol.ComponentResolver

/-!
Component-first binary structured 0-1-Integer-Programming-to-Knapsack route.

The standard-audited binary numeric shared gadget is owned by its domain leaf.
This public route contains no whole-route primitive or route-local machine: it
only composes exact ingress, shared-gadget, and egress certificates at the
complete encoder-bound binary endpoints.
-/

namespace ComplexityReduction
namespace Routes
namespace ZeroOneIPBinaryToKnapsackBinary

open Certificate Encoding Program

/-- The original exact binary structured 0-1-IP endpoint. -/
abbrev originalZeroOneIPBinaryProblem : PresentedProblem :=
  Presentation.ZeroOneIPBinary.binaryStructuredProblem

/-- The canonical source hub retains the full binary 0-1-IP representation. -/
abbrev zeroOneIPBinaryHubProblem : PresentedProblem :=
  Presentation.ZeroOneIPBinary.binaryStructuredProblem

/-- The canonical target hub retains the full binary Knapsack representation. -/
abbrev knapsackBinaryHubProblem : PresentedProblem :=
  Presentation.KnapsackBinary.structuredProblem

/-- The public final binary Knapsack endpoint is the target hub itself. -/
abbrev finalKnapsackBinaryProblem : PresentedProblem :=
  Presentation.KnapsackBinary.structuredProblem

abbrev ZeroOneIPBinaryIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress originalZeroOneIPBinaryProblem zeroOneIPBinaryHubProblem
abbrev SharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget zeroOneIPBinaryHubProblem knapsackBinaryHubProblem
abbrev KnapsackBinaryEgressRequest : Type 2 :=
  Protocol.ComponentRequest .egress knapsackBinaryHubProblem finalKnapsackBinaryProblem
abbrev FinalCompositionRequest : Type 2 :=
  Protocol.ComponentRequest .finalComposition originalZeroOneIPBinaryProblem finalKnapsackBinaryProblem

def zeroOneIPBinaryIngressRequest : ZeroOneIPBinaryIngressRequest := .exact
def sharedGadgetRequest : SharedGadgetRequest := .exact
def knapsackBinaryEgressRequest : KnapsackBinaryEgressRequest := .exact
def finalCompositionRequest : FinalCompositionRequest := .exact

theorem zeroOneIPBinaryIngress_endpoints_eq :
    originalZeroOneIPBinaryProblem = zeroOneIPBinaryHubProblem := rfl
theorem knapsackBinaryEgress_endpoints_eq :
    knapsackBinaryHubProblem = finalKnapsackBinaryProblem := rfl
theorem zeroOneIPBinaryIngressRequest_endpoint_exact :
    zeroOneIPBinaryIngressRequest.endpoint =
      (show Protocol.ComponentEndpoint .ingress
        originalZeroOneIPBinaryProblem zeroOneIPBinaryHubProblem from .exact) := rfl
theorem sharedGadgetRequest_endpoint_exact :
    sharedGadgetRequest.endpoint =
      (show Protocol.ComponentEndpoint .sharedGadget
        zeroOneIPBinaryHubProblem knapsackBinaryHubProblem from .exact) := rfl
theorem knapsackBinaryEgressRequest_endpoint_exact :
    knapsackBinaryEgressRequest.endpoint =
      (show Protocol.ComponentEndpoint .egress
        knapsackBinaryHubProblem finalKnapsackBinaryProblem from .exact) := rfl
theorem finalCompositionRequest_endpoint_exact :
    finalCompositionRequest.endpoint =
      (show Protocol.ComponentEndpoint .finalComposition
        originalZeroOneIPBinaryProblem finalKnapsackBinaryProblem from .exact) := rfl

/-- Exact ingress is a typed identity only because the complete endpoints coincide. -/
noncomputable def ingress :
    CertifiedReduction originalZeroOneIPBinaryProblem zeroOneIPBinaryHubProblem :=
  .refl zeroOneIPBinaryHubProblem

/-- Exact egress is a typed identity only because the complete endpoints coincide. -/
noncomputable def egress :
    CertifiedReduction knapsackBinaryHubProblem finalKnapsackBinaryProblem :=
  .refl knapsackBinaryHubProblem

noncomputable def zeroOneIPBinaryIngressResolution :
    Protocol.ComponentResolution .ingress originalZeroOneIPBinaryProblem zeroOneIPBinaryHubProblem :=
  Protocol.ComponentResolver.accept zeroOneIPBinaryIngressRequest ingress

noncomputable def knapsackBinaryEgressResolution :
    Protocol.ComponentResolution .egress knapsackBinaryHubProblem finalKnapsackBinaryProblem :=
  Protocol.ComponentResolver.accept knapsackBinaryEgressRequest egress

/-- The route reuses the sole standard-audited binary numeric hub certificate. -/
noncomputable def sharedGadget :
    CertifiedReduction zeroOneIPBinaryHubProblem knapsackBinaryHubProblem :=
  Domain.ZeroOneIPBinaryToKnapsackBinaryStandardTM.sharedGadget

noncomputable def sharedGadgetResolution :
    Protocol.ComponentResolution .sharedGadget zeroOneIPBinaryHubProblem knapsackBinaryHubProblem :=
  Protocol.ComponentResolver.accept sharedGadgetRequest sharedGadget

/-- The public route is exactly ingress/shared/egress certificate composition. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def finalRoute :
    CertifiedReduction originalZeroOneIPBinaryProblem finalKnapsackBinaryProblem :=
  CertifiedReduction.comp egress (CertifiedReduction.comp sharedGadget ingress)

/-- Typed provenance fixes the route's three independently reusable components. -/
@[complexity_reduction_ir_typed_edge]
noncomputable def finalRouteProvenance :
    CertifiedRouteProvenance ingress sharedGadget (.explicit egress) finalRoute :=
  CertifiedRouteProvenance.explicitEgress ingress sharedGadget egress

/-- Resolve the exact component path into its request-indexed accepted route result. -/
noncomputable def resolveComponentPath :
    Protocol.ResolverOutcome originalZeroOneIPBinaryProblem finalKnapsackBinaryProblem :=
  Protocol.ComponentResolver.composeIngressSharedEgress finalCompositionRequest
    zeroOneIPBinaryIngressResolution sharedGadgetResolution knapsackBinaryEgressResolution

@[simp] theorem zeroOneIPBinaryIngressResolution_exact :
    zeroOneIPBinaryIngressResolution = .accepted ingress := rfl
@[simp] theorem knapsackBinaryEgressResolution_exact :
    knapsackBinaryEgressResolution = .accepted egress := rfl
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

end ZeroOneIPBinaryToKnapsackBinary
end Routes
end ComplexityReduction
