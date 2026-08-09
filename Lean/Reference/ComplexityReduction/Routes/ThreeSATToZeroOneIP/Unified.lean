/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Presentation.ZeroOneIP
import ComplexityReduction.Problems.Karp21.Satisfiability
import ComplexityReduction.Domain.ThreeSATToZeroOneIPStandardTM
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Provenance
import ComplexityReduction.Protocol.ComponentResolver

/-!
Component-first structured 3SAT-to-0-1-Integer-Programming route.

The reusable direct-TM primitive, executable, semantic proof, and certificate
are owned by `V2.Domain.ThreeSATToZeroOneIPStandardTM`.  That domain leaf
reconstructs the two closed fold bounds with kernel `decide`, rather than CR's
nonstandard `native_decide` evidence.  This route contains no whole-route
primitive: its public certificate is only ingress, shared-gadget, and egress
composition at the exact canonical endpoints.
-/

namespace ComplexityReduction
namespace Routes
namespace ThreeSATToZeroOneIP

open Certificate Encoding Program

/-- The original exact structured 3SAT endpoint. -/
abbrev originalThreeSATProblem : PresentedProblem :=
  Problems.Karp21.Satisfiability.threeSATStructuredProblem
/-- The canonical 3SAT hub is the same exact presented endpoint. -/
abbrev threeSATHubProblem : PresentedProblem :=
  Problems.Karp21.Satisfiability.threeSATStructuredProblem
/-- The selected reusable shared-gadget target hub. -/
abbrev zeroOneIPHubProblem : PresentedProblem :=
  Presentation.ZeroOneIP.structuredProblem
/-- The final exact structured 0-1-IP endpoint is the same endpoint as its hub. -/
abbrev finalZeroOneIPProblem : PresentedProblem :=
  Presentation.ZeroOneIP.structuredProblem

abbrev ThreeSATIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress originalThreeSATProblem threeSATHubProblem
abbrev SharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget threeSATHubProblem zeroOneIPHubProblem
abbrev ZeroOneIPEgressRequest : Type 2 :=
  Protocol.ComponentRequest .egress zeroOneIPHubProblem finalZeroOneIPProblem
abbrev FinalCompositionRequest : Type 2 :=
  Protocol.ComponentRequest .finalComposition originalThreeSATProblem finalZeroOneIPProblem

def threeSATIngressRequest : ThreeSATIngressRequest := .exact
def sharedGadgetRequest : SharedGadgetRequest := .exact
def zeroOneIPEgressRequest : ZeroOneIPEgressRequest := .exact
def finalCompositionRequest : FinalCompositionRequest := .exact

theorem threeSATIngress_endpoints_eq : originalThreeSATProblem = threeSATHubProblem := rfl
theorem zeroOneIPEgress_endpoints_eq : zeroOneIPHubProblem = finalZeroOneIPProblem := rfl
theorem threeSATIngressRequest_endpoint_exact :
    threeSATIngressRequest.endpoint =
      (show Protocol.ComponentEndpoint .ingress originalThreeSATProblem threeSATHubProblem from .exact) := rfl
theorem sharedGadgetRequest_endpoint_exact :
    sharedGadgetRequest.endpoint =
      (show Protocol.ComponentEndpoint .sharedGadget threeSATHubProblem zeroOneIPHubProblem from .exact) := rfl
theorem zeroOneIPEgressRequest_endpoint_exact :
    zeroOneIPEgressRequest.endpoint =
      (show Protocol.ComponentEndpoint .egress zeroOneIPHubProblem finalZeroOneIPProblem from .exact) := rfl
theorem finalCompositionRequest_endpoint_exact :
    finalCompositionRequest.endpoint =
      (show Protocol.ComponentEndpoint .finalComposition originalThreeSATProblem finalZeroOneIPProblem from .exact) := rfl

/-- The structural 3SAT ingress is an exact typed identity certificate. -/
noncomputable def ingress : CertifiedReduction originalThreeSATProblem threeSATHubProblem :=
  .refl threeSATHubProblem
/-- The structural 0-1-IP egress is an exact typed identity certificate. -/
noncomputable def egress : CertifiedReduction zeroOneIPHubProblem finalZeroOneIPProblem :=
  .refl zeroOneIPHubProblem

noncomputable def threeSATIngressResolution :
    Protocol.ComponentResolution .ingress originalThreeSATProblem threeSATHubProblem :=
  Protocol.ComponentResolver.accept threeSATIngressRequest ingress
noncomputable def zeroOneIPEgressResolution :
    Protocol.ComponentResolution .egress zeroOneIPHubProblem finalZeroOneIPProblem :=
  Protocol.ComponentResolver.accept zeroOneIPEgressRequest egress

/-- The route reuses the sole standard-audited domain shared-gadget certificate. -/
noncomputable def sharedGadget :
    CertifiedReduction threeSATHubProblem zeroOneIPHubProblem :=
  Domain.ThreeSATToZeroOneIPStandardTM.sharedGadget

/-- The exact reusable shared component is accepted only through that domain certificate. -/
noncomputable def sharedGadgetResolution :
    Protocol.ComponentResolution .sharedGadget threeSATHubProblem zeroOneIPHubProblem :=
  Protocol.ComponentResolver.accept sharedGadgetRequest sharedGadget

/-- The public route is exactly the ingress/shared/egress certificate composition. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def finalRoute :
    CertifiedReduction originalThreeSATProblem finalZeroOneIPProblem :=
  CertifiedReduction.comp egress (CertifiedReduction.comp sharedGadget ingress)

/-- Typed provenance fixes the three components and the composed public certificate. -/
@[complexity_reduction_ir_typed_edge]
noncomputable def finalRouteProvenance :
    CertifiedRouteProvenance ingress sharedGadget (.explicit egress) finalRoute :=
  CertifiedRouteProvenance.explicitEgress ingress sharedGadget egress

/-- The final request-indexed outcome composes ingress/shared/egress in construction order. -/
noncomputable def resolveComponentPath :
    Protocol.ResolverOutcome originalThreeSATProblem finalZeroOneIPProblem :=
  Protocol.ComponentResolver.composeIngressSharedEgress finalCompositionRequest
    threeSATIngressResolution sharedGadgetResolution zeroOneIPEgressResolution

@[simp] theorem threeSATIngressResolution_exact :
    threeSATIngressResolution = .accepted ingress := rfl
@[simp] theorem zeroOneIPEgressResolution_exact :
    zeroOneIPEgressResolution = .accepted egress := rfl
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

end ThreeSATToZeroOneIP
end Routes
end ComplexityReduction
