/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.GraphColoringToIncidenceGadget
import ComplexityReduction.Domain.ChromaticNumberToGraphColoringAdapter
import ComplexityReduction.Domain.IncidenceIRToStructuredExactCoverStandardTM
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.ChromaticNumber
import ComplexityReduction.Presentation.SetSystem
import ComplexityReduction.Certificate.Provenance
import ComplexityReduction.Protocol.ComponentResolver

/-!
Component-first boundary for Chromatic Number to Exact Cover.

The structured Chromatic Number wrapper is normalized by its one concrete
ingress adapter into a wrapper-independent canonical graph-colouring hub that
retains the complete graph and colour bound.  The intended reusable
computation is from that graph-colouring hub to canonical
`Domain.IncidenceIR.exactCoverProblem`; the independently owned egress realizes
that incidence endpoint as structured Exact Cover.

The shared GraphColoringIR-to-IncidenceIR gadget and the distinct
IncidenceIR-to-structured-Exact-Cover egress are closed typed components.
This route never introduces a fused source-to-Exact-Cover primitive,
route-local machine/cost proof, packet, provider, or slot.
-/

namespace ComplexityReduction
namespace Routes
namespace ChromaticNumberToExactCover

open Certificate Encoding

/-- The original structured Chromatic Number endpoint. -/
abbrev originalChromaticNumberProblem : PresentedProblem :=
  Presentation.ChromaticNumber.structuredProblem

/-- The wrapper-independent canonical graph-and-colour-bound hub. -/
abbrev graphColoringHubProblem : PresentedProblem :=
  Domain.GraphColoringIR.chromaticNumberProblem

/-- The canonical typed incidence exact-cover hub. -/
abbrev incidenceHubProblem : PresentedProblem :=
  Domain.IncidenceIR.exactCoverProblem

/-- The public structured Exact Cover endpoint. -/
abbrev originalExactCoverProblem : PresentedProblem :=
  Presentation.SetSystem.exactCoverStructuredProblem

/-- Exact ingress request from structured Chromatic Number to its graph-colouring hub. -/
abbrev GraphColoringIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress originalChromaticNumberProblem graphColoringHubProblem

/-- Exact request for the Graph-to-Incidence shared gadget. -/
abbrev SharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget graphColoringHubProblem incidenceHubProblem

/-- Exact later egress request from canonical incidence Exact Cover to structured Exact Cover. -/
abbrev ExactCoverEgressRequest : Type 2 :=
  Protocol.ComponentRequest .egress incidenceHubProblem originalExactCoverProblem

/-- Exact request that fixes the public composed endpoints only. -/
abbrev FinalCompositionRequest : Type 2 :=
  Protocol.ComponentRequest .finalComposition originalChromaticNumberProblem originalExactCoverProblem

/-- The unique graph-colouring ingress request. -/
def graphColoringIngressRequest : GraphColoringIngressRequest := .exact

/-- The unique Graph-to-Incidence shared-gadget request. -/
def sharedGadgetRequest : SharedGadgetRequest := .exact

/-- The unique eventual Exact Cover realization request. -/
def exactCoverEgressRequest : ExactCoverEgressRequest := .exact

/-- The final request carries no executable authority. -/
def finalCompositionRequest : FinalCompositionRequest := .exact

/-- The ingress request retains exact graph-colouring endpoints. -/
theorem graphColoringIngressRequest_endpoint_exact :
    graphColoringIngressRequest.endpoint =
      (show Protocol.ComponentEndpoint .ingress
        originalChromaticNumberProblem graphColoringHubProblem from .exact) :=
  rfl

/-- The shared-gadget request retains exact Graph-to-Incidence hub endpoints. -/
theorem sharedGadgetRequest_endpoint_exact :
    sharedGadgetRequest.endpoint =
      (show Protocol.ComponentEndpoint .sharedGadget graphColoringHubProblem incidenceHubProblem from .exact) :=
  rfl

/-- The egress request retains exact incidence-to-structured-Exact-Cover endpoints. -/
theorem exactCoverEgressRequest_endpoint_exact :
    exactCoverEgressRequest.endpoint =
      (show Protocol.ComponentEndpoint .egress incidenceHubProblem originalExactCoverProblem from .exact) :=
  rfl

/-- The final request retains exact public endpoints. -/
theorem finalCompositionRequest_endpoint_exact :
    finalCompositionRequest.endpoint =
      (show Protocol.ComponentEndpoint .finalComposition
        originalChromaticNumberProblem originalExactCoverProblem from .exact) :=
  rfl

/-- The exact graph-colouring ingress is the canonical wrapper-normalization certificate. -/
noncomputable def ingress : CertifiedReduction originalChromaticNumberProblem graphColoringHubProblem :=
  Domain.ChromaticNumberToGraphColoringAdapter.sourceAdapter

/-- The route exposes the canonical shared hub theorem without reauthoring it. -/
theorem graphToIncidence_semanticCorrect (input : graphColoringHubProblem.Instance) :
    graphColoringHubProblem.accepts input ↔
      incidenceHubProblem.accepts (Domain.GraphColoringToIncidence.run input) :=
  Domain.GraphColoringToIncidence.isColorable_iff_run_exactCover input

/-- The ingress identity component is accepted only at its exact request. -/
noncomputable def graphColoringIngressResolution :
    Protocol.ComponentResolution .ingress originalChromaticNumberProblem graphColoringHubProblem :=
  Protocol.ComponentResolver.accept graphColoringIngressRequest ingress

/-- The route reuses the one canonical GraphColoringIR-to-IncidenceIR component. -/
def sharedGadget : CertifiedReduction graphColoringHubProblem incidenceHubProblem :=
  Domain.GraphColoringToIncidenceGadget.sharedGadget

/-- The distinct target realization is the one canonical IncidenceIR egress component. -/
def egress : CertifiedReduction incidenceHubProblem originalExactCoverProblem :=
  Domain.IncidenceIRToStructuredExactCoverStandardTM.egress

/-- The completed ingress/shared prefix is a certificate composition, not a new primitive. -/
noncomputable def ingressThenShared :
    CertifiedReduction originalChromaticNumberProblem incidenceHubProblem :=
  CertifiedReduction.comp sharedGadget ingress

@[simp] theorem ingressThenShared_program :
    ingressThenShared.program =
      Program.PolyProg.comp sharedGadget.program ingress.program :=
  rfl

@[simp] theorem ingressThenShared_directTM :
    ingressThenShared.directTM = ingressThenShared.program.compileTM :=
  rfl

/-- The Graph-to-Incidence request has an exact typed component outcome. -/
abbrev SharedGadgetResolution : Type 2 :=
  Protocol.ComponentResolution .sharedGadget graphColoringHubProblem incidenceHubProblem

/-- The incidence-to-structured-Exact-Cover request has its own typed outcome. -/
abbrev ExactCoverEgressResolution : Type 2 :=
  Protocol.ComponentResolution .egress incidenceHubProblem originalExactCoverProblem

/-- The shared capability is accepted only through its canonical typed declaration. -/
def sharedGadgetResolution : SharedGadgetResolution :=
  Protocol.ComponentResolver.accept sharedGadgetRequest sharedGadget

/-- Resolve the separately owned Exact-Cover egress independently of the shared gadget. -/
def exactCoverEgressResolution : ExactCoverEgressResolution :=
  Protocol.ComponentResolver.accept exactCoverEgressRequest egress

/-- The public route is the thin ingress/shared/egress certificate composition. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def finalRoute :
    CertifiedReduction originalChromaticNumberProblem originalExactCoverProblem :=
  CertifiedReduction.comp egress ingressThenShared

/-- Typed provenance fixes the three independently owned component declarations. -/
@[complexity_reduction_ir_typed_edge]
noncomputable def finalRouteProvenance :
    CertifiedRouteProvenance ingress sharedGadget (.explicit egress) finalRoute :=
  CertifiedRouteProvenance.explicitEgress ingress sharedGadget egress

/-- The final route resolver is indexed by public endpoints and accepted components. -/
abbrev RouteResolution : Type 2 :=
  Protocol.ResolverOutcome originalChromaticNumberProblem originalExactCoverProblem

/-- All three exact role-indexed components resolve to the public certificate. -/
noncomputable def resolveComponentRoute : RouteResolution :=
  Protocol.ComponentResolver.composeIngressSharedEgress finalCompositionRequest
    graphColoringIngressResolution sharedGadgetResolution exactCoverEgressResolution

/-- The ingress resolution stores exactly the wrapper-normalization certificate. -/
@[simp] theorem graphColoringIngressResolution_exact :
    graphColoringIngressResolution = .accepted ingress :=
  rfl

/-- The Graph-to-Incidence resolution is definitionally its accepted typed component. -/
@[simp] theorem sharedGadgetResolution_eq_accepted :
    sharedGadgetResolution = .accepted sharedGadget :=
  rfl

/-- The egress resolution is definitionally its exact typed component. -/
@[simp] theorem exactCoverEgressResolution_eq_accepted :
    exactCoverEgressResolution = .accepted egress :=
  rfl

@[simp] theorem finalRoute_program :
    finalRoute.program =
      Program.PolyProg.comp egress.program
        (Program.PolyProg.comp sharedGadget.program ingress.program) :=
  rfl

@[simp] theorem finalRoute_directTM :
    finalRoute.directTM = finalRoute.program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM finalRoute

@[simp] theorem resolveComponentRoute_exact :
    resolveComponentRoute = .accepted finalRoute :=
  rfl

end ChromaticNumberToExactCover
end Routes
end ComplexityReduction
