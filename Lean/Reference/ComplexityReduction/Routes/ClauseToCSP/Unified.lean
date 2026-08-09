/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.CNFToThreeSATStandardTM
import ComplexityReduction.Domain.ThreeSATToThreeSATLikeStandardTM
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Provenance
import ComplexityReduction.Presentation.Satisfiability
import ComplexityReduction.Protocol.ComponentResolver

/-!
Canonical Clause/CNF to CSP composition.

The public structured-CNF source first enters the canonical bundled-3SAT hub
through the independently owned CNF splitter.  The sole reusable middle gadget
is the fixed 3SAT-like CSP component, whose executable, semantic law, raw
encoder layout, and direct-TM compiler are all indexed by one typed program.
The final target is the same CSP hub.  This leaf therefore owns only component
composition and provenance; it introduces no route-wide primitive or machine.
-/

namespace ComplexityReduction
namespace Routes
namespace ClauseToCSP

open Certificate Encoding Program

/-- The original public structured CNF/SAT source endpoint. -/
abbrev originalClauseCNFProblem : PresentedProblem :=
  Presentation.Satisfiability.structuredProblem

/-- The canonical Clause/CNF hub is the structured bundled-3SAT endpoint. -/
abbrev clauseCNFHubProblem : PresentedProblem :=
  Domain.ThreeSATToThreeSATLikeStandardTM.sourceProblem

/-- The explicit fixed-language CSP hub shared by the Clause family. -/
noncomputable abbrev canonicalCSPProblem : PresentedProblem :=
  Domain.ThreeSATToThreeSATLikeStandardTM.targetProblem

/-- The public CSP target is the selected canonical CSP hub itself. -/
noncomputable abbrev originalCSPProblem : PresentedProblem :=
  canonicalCSPProblem

/-- Exact ingress request from structured CNF to the bundled-3SAT hub. -/
abbrev ClauseCNFIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress originalClauseCNFProblem clauseCNFHubProblem

/-- Exact request for the reusable bundled-3SAT-to-CSP shared gadget. -/
noncomputable abbrev SharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget clauseCNFHubProblem canonicalCSPProblem

/-- Exact egress request from the CSP hub to its public endpoint. -/
noncomputable abbrev CSPEgressRequest : Type 2 :=
  Protocol.ComponentRequest .egress canonicalCSPProblem originalCSPProblem

/-- Exact public route request. -/
noncomputable abbrev FinalCompositionRequest : Type 2 :=
  Protocol.ComponentRequest .finalComposition originalClauseCNFProblem originalCSPProblem

/-- The one structured-CNF ingress request. -/
def clauseCNFIngressRequest : ClauseCNFIngressRequest := .exact

/-- The one bundled-3SAT-to-CSP shared request. -/
noncomputable def sharedGadgetRequest : SharedGadgetRequest := .exact

/-- The one CSP identity egress request. -/
noncomputable def cspEgressRequest : CSPEgressRequest := .exact

/-- The final request supplies endpoints only. -/
noncomputable def finalCompositionRequest : FinalCompositionRequest := .exact

/-- The CNF splitter is reused solely as the Clause-family ingress adapter. -/
noncomputable abbrev ingress :
    CertifiedReduction originalClauseCNFProblem clauseCNFHubProblem :=
  Domain.CNFToThreeSATStandardTM.sharedGadget

/-- The fixed 3SAT-like CSP transformation is the one shared hub gadget. -/
noncomputable abbrev sharedGadget :
    CertifiedReduction clauseCNFHubProblem canonicalCSPProblem :=
  Domain.ThreeSATToThreeSATLikeStandardTM.sharedGadget

/-- The public target needs no additional computation after the canonical CSP hub. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_egress]
noncomputable def egress : CertifiedReduction canonicalCSPProblem originalCSPProblem :=
  .refl canonicalCSPProblem

/-- The CNF ingress resolution accepts only the existing splitter certificate. -/
noncomputable def clauseCNFIngressResolution :
    Protocol.ComponentResolution .ingress originalClauseCNFProblem clauseCNFHubProblem :=
  Protocol.ComponentResolver.accept clauseCNFIngressRequest ingress

/-- The shared resolution accepts only the exact direct-TM-backed hub gadget. -/
noncomputable def sharedGadgetResolution :
    Protocol.ComponentResolution .sharedGadget clauseCNFHubProblem canonicalCSPProblem :=
  Protocol.ComponentResolver.accept sharedGadgetRequest sharedGadget

/-- The egress resolution accepts only the canonical identity certificate. -/
noncomputable def cspEgressResolution :
    Protocol.ComponentResolution .egress canonicalCSPProblem originalCSPProblem :=
  Protocol.ComponentResolver.accept cspEgressRequest egress

/-- The public route is exactly ingress, shared hub gadget, and egress composition. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def finalRoute : CertifiedReduction originalClauseCNFProblem originalCSPProblem :=
  CertifiedReduction.comp egress (CertifiedReduction.comp sharedGadget ingress)

/-- Typed provenance records the independently owned ingress, gadget, egress, and composite. -/
@[complexity_reduction_ir_typed_edge]
noncomputable def finalRouteProvenance :
    CertifiedRouteProvenance ingress Domain.ThreeSATToThreeSATLikeStandardTM.sharedGadget
      (.explicit egress) finalRoute :=
  CertifiedRouteProvenance.explicitEgress ingress
    Domain.ThreeSATToThreeSATLikeStandardTM.sharedGadget egress

/-- The resolver composes the three accepted typed components. -/
noncomputable def resolveComponentRoute :
    Protocol.ResolverOutcome originalClauseCNFProblem originalCSPProblem :=
  Protocol.ComponentResolver.composeIngressSharedEgress finalCompositionRequest
    clauseCNFIngressResolution sharedGadgetResolution cspEgressResolution

@[simp] theorem clauseCNFIngressRequest_endpoint_exact :
    clauseCNFIngressRequest.endpoint =
      (show Protocol.ComponentEndpoint .ingress
        originalClauseCNFProblem clauseCNFHubProblem from .exact) :=
  rfl

@[simp] theorem sharedGadgetRequest_endpoint_exact :
    sharedGadgetRequest.endpoint =
      (show Protocol.ComponentEndpoint .sharedGadget
        clauseCNFHubProblem canonicalCSPProblem from .exact) :=
  rfl

@[simp] theorem cspEgressRequest_endpoint_exact :
    cspEgressRequest.endpoint =
      (show Protocol.ComponentEndpoint .egress
        canonicalCSPProblem originalCSPProblem from .exact) :=
  rfl

@[simp] theorem finalCompositionRequest_endpoint_exact :
    finalCompositionRequest.endpoint =
      (show Protocol.ComponentEndpoint .finalComposition
        originalClauseCNFProblem originalCSPProblem from .exact) :=
  rfl

@[simp] theorem clauseCNFIngressResolution_exact :
    clauseCNFIngressResolution = .accepted ingress :=
  rfl

@[simp] theorem sharedGadgetResolution_exact :
    sharedGadgetResolution = .accepted sharedGadget :=
  rfl

@[simp] theorem cspEgressResolution_exact :
    cspEgressResolution = .accepted egress :=
  rfl

/-- The final executable is the required nested typed-program composition. -/
@[simp] theorem finalRoute_program :
    finalRoute.program =
      PolyProg.comp egress.program (PolyProg.comp sharedGadget.program ingress.program) :=
  rfl

/-- Direct-TM evidence is compiled from the same final program. -/
@[simp] theorem finalRoute_directTM :
    finalRoute.directTM = finalRoute.program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM finalRoute

/-- All accepted component resolutions elaborate to exactly the final route certificate. -/
@[simp] theorem resolveComponentRoute_exact :
    resolveComponentRoute = .accepted finalRoute :=
  rfl

end ClauseToCSP
end Routes
end ComplexityReduction
