/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.ModifiedExactCoverInput
import ComplexityReduction.Domain.IncidenceIRToStructuredExactCoverStandardTM
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Provenance
import ComplexityReduction.Protocol.ComponentResolver

/-!
Modified Exact-Cover input reuse through the canonical incidence hub.

The Boolean-tagged source contributes only its existing metadata-erasure and
source-to-IncidenceIR ingress composition.  The target is realized by the
already shared IncidenceIR-to-structured-Exact-Cover egress.  The intervening
identity is the core certified identity at the canonical hub: it introduces no
primitive, executable, local TM, or alternate hub construction.  Thus the
public route is a typed composition of existing components, not a modified
source-to-target primitive.
-/

namespace ComplexityReduction
namespace Routes
namespace ModifiedExactCoverToExactCover

open Certificate Encoding Program

/-- The Boolean-tagged Exact-Cover input presentation used by the reuse pilot. -/
abbrev sourceProblem : PresentedProblem :=
  Domain.ModifiedExactCoverInput.modifiedProblem

/-- The canonical IncidenceIR Exact-Cover hub reused without modification. -/
abbrev incidenceHubProblem : PresentedProblem :=
  Domain.ModifiedExactCoverInput.hubProblem

/-- The existing structured Exact-Cover target of the reusable egress component. -/
abbrev targetProblem : PresentedProblem :=
  Domain.IncidenceIRToStructuredExactCoverStandardTM.targetProblem

/-- Exact ingress request from the modified presentation to the canonical hub. -/
abbrev IngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress sourceProblem incidenceHubProblem

/-- Exact structural identity request at the canonical hub. -/
abbrev HubIdentityRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget incidenceHubProblem incidenceHubProblem

/-- Exact request for the existing IncidenceIR-to-Exact-Cover egress. -/
abbrev EgressRequest : Type 2 :=
  Protocol.ComponentRequest .egress incidenceHubProblem targetProblem

/-- Exact public request for the modified-input final composition. -/
abbrev FinalCompositionRequest : Type 2 :=
  Protocol.ComponentRequest .finalComposition sourceProblem targetProblem

/-- The one modified-input ingress request. -/
def ingressRequest : IngressRequest :=
  Domain.ModifiedExactCoverInput.modifiedIngressRequest

/-- The identity request retains the same canonical hub at both endpoints. -/
def hubIdentityRequest : HubIdentityRequest := .exact

/-- The existing egress's exact component request. -/
def egressRequest : EgressRequest :=
  Domain.IncidenceIRToStructuredExactCoverStandardTM.request

/-- The one final request contains endpoints only, never executable authority. -/
def finalCompositionRequest : FinalCompositionRequest := .exact

/-- The source adapter is the previously certified modified-input ingress. -/
noncomputable abbrev ingress : CertifiedReduction sourceProblem incidenceHubProblem :=
  Domain.ModifiedExactCoverInput.modifiedSourceAdapter

/--
The only middle component is the generic core identity at the already
canonical hub.  It is deliberately unannotated: no route-local component is
introduced for discovery or for trusted computation.
-/
noncomputable def hubIdentity : CertifiedReduction incidenceHubProblem incidenceHubProblem :=
  .refl incidenceHubProblem

/-- The target realization is the shared typed IncidenceIR egress. -/
abbrev egress : CertifiedReduction incidenceHubProblem targetProblem :=
  Domain.IncidenceIRToStructuredExactCoverStandardTM.egress

/-- The ingress resolution is accepted solely with the pre-existing source adapter. -/
noncomputable def ingressResolution :
    Protocol.ComponentResolution .ingress sourceProblem incidenceHubProblem :=
  .accepted ingress

/-- The core identity is accepted only at its exact canonical hub endpoint. -/
noncomputable def hubIdentityResolution :
    Protocol.ComponentResolution .sharedGadget incidenceHubProblem incidenceHubProblem :=
  .accepted hubIdentity

/-- The egress resolution is accepted solely with the existing egress certificate. -/
noncomputable def exactCoverEgressResolution :
    Protocol.ComponentResolution .egress incidenceHubProblem targetProblem :=
  .accepted egress

/-- The public route is the explicit egress after the modified ingress and core hub identity. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def finalRoute : CertifiedReduction sourceProblem targetProblem :=
  CertifiedReduction.comp egress (CertifiedReduction.comp hubIdentity ingress)

/--
Typed provenance retains the exact existing ingress and egress declarations,
the core hub identity, and the one final composite certificate.
-/
@[complexity_reduction_ir_typed_edge]
noncomputable def finalRouteProvenance :
    CertifiedRouteProvenance ingress hubIdentity (.explicit egress) finalRoute :=
  CertifiedRouteProvenance.explicitEgress ingress hubIdentity egress

/-- Resolve the public request only by composing its typed component outcomes. -/
noncomputable def resolveComponentRoute : Protocol.ResolverOutcome sourceProblem targetProblem :=
  Protocol.ComponentResolver.composeIngressSharedEgress finalCompositionRequest
    ingressResolution hubIdentityResolution exactCoverEgressResolution

/-- The ingress request preserves the distinct product source identity and canonical hub. -/
@[simp] theorem ingressRequest_endpoint_exact :
    ingressRequest.endpoint =
      (show Protocol.ComponentEndpoint .ingress sourceProblem incidenceHubProblem from .exact) :=
  rfl

/-- The identity request is confined to the one canonical hub endpoint. -/
@[simp] theorem hubIdentityRequest_endpoint_exact :
    hubIdentityRequest.endpoint =
      (show Protocol.ComponentEndpoint .sharedGadget
        incidenceHubProblem incidenceHubProblem from .exact) :=
  rfl

/-- The egress request preserves its exact typed IncidenceIR and Exact-Cover endpoints. -/
@[simp] theorem egressRequest_endpoint_exact :
    egressRequest.endpoint =
      (show Protocol.ComponentEndpoint .egress incidenceHubProblem targetProblem from .exact) :=
  rfl

/-- The public request preserves the exact modified source and structured target. -/
@[simp] theorem finalCompositionRequest_endpoint_exact :
    finalCompositionRequest.endpoint =
      (show Protocol.ComponentEndpoint .finalComposition sourceProblem targetProblem from .exact) :=
  rfl

/-- The ingress outcome contains exactly the existing modified-input adapter. -/
@[simp] theorem ingressResolution_exact :
    ingressResolution = .accepted ingress :=
  rfl

/-- The middle outcome contains only the core certified identity. -/
@[simp] theorem hubIdentityResolution_exact :
    hubIdentityResolution = .accepted hubIdentity :=
  rfl

/-- The egress outcome contains exactly the existing shared egress certificate. -/
@[simp] theorem exactCoverEgressResolution_exact :
    exactCoverEgressResolution = .accepted egress :=
  rfl

/-- The final program is precisely the required ingress/identity/egress composition. -/
@[simp] theorem finalRoute_program :
    finalRoute.program =
      PolyProg.comp egress.program (PolyProg.comp hubIdentity.program ingress.program) :=
  rfl

/-- The final direct-TM evidence is compilation of that same composite program. -/
@[simp] theorem finalRoute_directTM :
    finalRoute.directTM = finalRoute.program.compileTM :=
  Certificate.CertifiedReduction.directTM_eq_compileTM _

/-- All accepted components compose to exactly the typed final certificate. -/
@[simp] theorem resolveComponentRoute_exact :
    resolveComponentRoute = .accepted finalRoute :=
  rfl

end ModifiedExactCoverToExactCover
end Routes
end ComplexityReduction
