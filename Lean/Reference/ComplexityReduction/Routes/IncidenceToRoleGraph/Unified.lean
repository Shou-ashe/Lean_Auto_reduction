/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.IncidenceToExactlyOneNeighborGadget
import ComplexityReduction.Domain.ModifiedExactCoverInput
import ComplexityReduction.Domain.SetSystemToIncidenceAdapter
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Provenance
import ComplexityReduction.Presentation.RoleGraph
import ComplexityReduction.Protocol.ComponentResolver
import ComplexityReduction.Legacy.IR.Domains.Graph.Combinatorics.ExactlyOneNeighbor.ExactCover

/-!
Component-first boundary for the legacy Incidence-to-RoleGraph route family.

The original structured Exact-Cover source first enters the canonical
incidence hub through one program-indexed ingress certificate.  One shared
hub construction then reaches the selected existential Exactly-One-Neighbor
endpoint.  The public routes are the corresponding thin certificate
compositions; this module declares neither a whole-route primitive nor a
route-local machine.

The legacy fixed-role target is retained only as an eventual explicit-egress
endpoint.  It is not treated as the same endpoint as the existential EON
target.
-/

namespace ComplexityReduction
namespace Routes
namespace IncidenceToRoleGraph

open Encoding
open Program
open Certificate
open Annotations

/-- The original structured Exact-Cover source endpoint. -/
abbrev originalSourceProblem : PresentedProblem :=
  Domain.SetSystemToIncidenceAdapter.sourceProblem

/-- The canonical typed incidence hub endpoint. -/
abbrev incidenceHubProblem : PresentedProblem :=
  Domain.SetSystemToIncidenceAdapter.hubProblem

/-- The selected existential Exactly-One-Neighbor endpoint of the shared gadget. -/
abbrev sharedGadgetTargetProblem : PresentedProblem :=
  Domain.IncidenceToExactlyOneNeighborGadget.targetProblem

/-- The retained fixed-role endpoint requires a separate explicit egress component. -/
abbrev fixedRoleTargetProblem : PresentedProblem :=
  Presentation.RoleGraph.exactlyOneNeighborPresentedProblem

/-- The Boolean-tagged Exact-Cover source used by the modified-input reuse pilot. -/
abbrev modifiedSourceProblem : PresentedProblem :=
  Domain.ModifiedExactCoverInput.modifiedProblem

/-- The existential target is already the identity-eligible final endpoint of the shared gadget. -/
abbrev existentialFinalTargetProblem : PresentedProblem :=
  sharedGadgetTargetProblem

/-- The exact original Exact-Cover-to-incidence ingress request. -/
abbrev OriginalIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress originalSourceProblem incidenceHubProblem

/-- The exact modified Exact-Cover-to-incidence ingress request. -/
abbrev ModifiedIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress modifiedSourceProblem incidenceHubProblem

/-- The exact incidence-hub-to-existential-EON shared-gadget request. -/
abbrev IncidenceSharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget incidenceHubProblem sharedGadgetTargetProblem

/-- The exact request for the identity-eligible existential egress. -/
abbrev IdentityEgressRequest : Type 2 :=
  Protocol.ComponentRequest .egress sharedGadgetTargetProblem existentialFinalTargetProblem

/-- The exact request for the still-unavailable explicit EON-to-fixed-role egress. -/
abbrev ExplicitEgressRequest : Type 2 :=
  Protocol.ComponentRequest .egress sharedGadgetTargetProblem fixedRoleTargetProblem

/-- The exact public request for the original-input existential final route. -/
abbrev OriginalExistentialFinalRequest : Type 2 :=
  Protocol.ComponentRequest .finalComposition originalSourceProblem existentialFinalTargetProblem

/-- The exact public request for the modified-input existential final route. -/
abbrev ModifiedExistentialFinalRequest : Type 2 :=
  Protocol.ComponentRequest .finalComposition modifiedSourceProblem existentialFinalTargetProblem

/-- The unique original ingress request. -/
def originalIngressRequest : OriginalIngressRequest :=
  Domain.SetSystemToIncidenceAdapter.request

/-- The unique modified-input ingress request. -/
def modifiedIngressRequest : ModifiedIngressRequest := .exact

/-- The unique incidence shared-gadget request. -/
def incidenceSharedGadgetRequest : IncidenceSharedGadgetRequest :=
  Domain.IncidenceToExactlyOneNeighborGadget.request

/-- The unique identity-eligible egress request. -/
def identityEgressRequest : IdentityEgressRequest := .exact

/-- The unique explicit fixed-role egress request. -/
def explicitEgressRequest : ExplicitEgressRequest := .exact

/-- The unique original-input existential final request. -/
def originalExistentialFinalRequest : OriginalExistentialFinalRequest := .exact

/-- The unique modified-input existential final request. -/
def modifiedExistentialFinalRequest : ModifiedExistentialFinalRequest := .exact

/-- The original ingress request retains its exact source and incidence-hub endpoints. -/
theorem originalIngressRequest_endpoint_exact :
    originalIngressRequest.endpoint =
      (show Protocol.ComponentEndpoint .ingress originalSourceProblem incidenceHubProblem from .exact) :=
  rfl

/-- The modified ingress request retains its distinct product source identity and incidence hub. -/
theorem modifiedIngressRequest_endpoint_exact :
    modifiedIngressRequest.endpoint =
      (show Protocol.ComponentEndpoint .ingress modifiedSourceProblem incidenceHubProblem from .exact) :=
  rfl

/-- The shared-gadget request retains its exact canonical incidence/EON hubs. -/
theorem incidenceSharedGadgetRequest_endpoint_exact :
    incidenceSharedGadgetRequest.endpoint =
      (show Protocol.ComponentEndpoint .sharedGadget incidenceHubProblem sharedGadgetTargetProblem from .exact) :=
  rfl

/-- The identity egress is eligible only at the definitionally identical existential endpoint. -/
theorem identityEgressRequest_endpoint_exact :
    identityEgressRequest.endpoint =
      (show Protocol.ComponentEndpoint .egress sharedGadgetTargetProblem existentialFinalTargetProblem from .exact) :=
  rfl

/-- The fixed-role egress remains an explicit, distinct request. -/
theorem explicitEgressRequest_endpoint_exact :
    explicitEgressRequest.endpoint =
      (show Protocol.ComponentEndpoint .egress sharedGadgetTargetProblem fixedRoleTargetProblem from .exact) :=
  rfl

/-- The original final request retains its exact structured Exact-Cover and EON endpoints. -/
theorem originalExistentialFinalRequest_endpoint_exact :
    originalExistentialFinalRequest.endpoint =
      (show Protocol.ComponentEndpoint .finalComposition originalSourceProblem
        existentialFinalTargetProblem from .exact) :=
  rfl

/-- The modified final request retains its distinct product source endpoint. -/
theorem modifiedExistentialFinalRequest_endpoint_exact :
    modifiedExistentialFinalRequest.endpoint =
      (show Protocol.ComponentEndpoint .finalComposition modifiedSourceProblem
        existentialFinalTargetProblem from .exact) :=
  rfl

/-- The original ingress is the accepted canonical source-to-hub certificate. -/
noncomputable def originalIngressComponentResolution :
    Protocol.ComponentResolution .ingress originalSourceProblem incidenceHubProblem :=
  Domain.SetSystemToIncidenceAdapter.resolve

/-- The modified ingress is the composition of metadata erasure and the same original ingress. -/
noncomputable def modifiedIngressComponentResolution :
    Protocol.ComponentResolution .ingress modifiedSourceProblem incidenceHubProblem :=
  .accepted Domain.ModifiedExactCoverInput.modifiedSourceAdapter

/-- The shared incidence gadget is the one accepted canonical hub component. -/
def incidenceSharedGadgetComponentResolution :
    Protocol.ComponentResolution .sharedGadget incidenceHubProblem sharedGadgetTargetProblem :=
  .accepted Domain.IncidenceToExactlyOneNeighborGadget.sharedGadget

/-- The explicit fixed-role egress is blocked at its own exact egress component. -/
def explicitEgressComponentResolution :
    Protocol.ComponentResolution .egress sharedGadgetTargetProblem fixedRoleTargetProblem :=
  .blocked (explicitEgressRequest.missing .directTM)

/-- The existential endpoint has a typed identity egress without a program or certificate. -/
def identityEgress : OptionalEgress sharedGadgetTargetProblem existentialFinalTargetProblem :=
  .identity

/-- The sole shared hub certificate is independent of either concrete source wrapper. -/
abbrev sharedIncidenceGadget :
    CertifiedReduction incidenceHubProblem sharedGadgetTargetProblem :=
  Domain.IncidenceToExactlyOneNeighborGadget.sharedGadget

/-- The original public route is exactly ingress followed by the one shared hub gadget. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def originalRoute :
    CertifiedReduction originalSourceProblem existentialFinalTargetProblem :=
  CertifiedReduction.comp Domain.IncidenceToExactlyOneNeighborGadget.sharedGadget
    Domain.SetSystemToIncidenceAdapter.sourceAdapter

/-- The modified public route differs only in its composed ingress adapter. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def modifiedRoute :
    CertifiedReduction modifiedSourceProblem existentialFinalTargetProblem :=
  CertifiedReduction.comp Domain.IncidenceToExactlyOneNeighborGadget.sharedGadget
    Domain.ModifiedExactCoverInput.modifiedSourceAdapter

/-- Provenance shape available once the original ingress and shared gadget are certified. -/
abbrev OriginalIdentityRouteProvenance
    (ingress : CertifiedReduction originalSourceProblem incidenceHubProblem)
    (sharedGadget : CertifiedReduction incidenceHubProblem sharedGadgetTargetProblem) : Type 2 :=
  CertifiedRouteProvenance ingress sharedGadget .identity (CertifiedReduction.comp sharedGadget ingress)

/-- Provenance shape available once the modified ingress and shared gadget are certified. -/
abbrev ModifiedIdentityRouteProvenance
    (ingress : CertifiedReduction modifiedSourceProblem incidenceHubProblem)
    (sharedGadget : CertifiedReduction incidenceHubProblem sharedGadgetTargetProblem) : Type 2 :=
  CertifiedRouteProvenance ingress sharedGadget .identity (CertifiedReduction.comp sharedGadget ingress)

/-- Typed provenance for the original thin two-component route. -/
@[complexity_reduction_ir_typed_edge]
noncomputable def originalRouteProvenance :
    CertifiedRouteProvenance Domain.SetSystemToIncidenceAdapter.sourceAdapter
      Domain.IncidenceToExactlyOneNeighborGadget.sharedGadget .identity originalRoute :=
  CertifiedRouteProvenance.identityEgress Domain.SetSystemToIncidenceAdapter.sourceAdapter
    Domain.IncidenceToExactlyOneNeighborGadget.sharedGadget

/-- Typed provenance for the modified thin two-component route. -/
@[complexity_reduction_ir_typed_edge]
noncomputable def modifiedRouteProvenance :
    CertifiedRouteProvenance Domain.ModifiedExactCoverInput.modifiedSourceAdapter
      Domain.IncidenceToExactlyOneNeighborGadget.sharedGadget .identity modifiedRoute :=
  CertifiedRouteProvenance.identityEgress Domain.ModifiedExactCoverInput.modifiedSourceAdapter
    Domain.IncidenceToExactlyOneNeighborGadget.sharedGadget

/-- Provenance shape for a later explicit fixed-role egress certificate. -/
abbrev ExplicitRoleGraphRouteProvenance
    {source : PresentedProblem}
    (ingress : CertifiedReduction source incidenceHubProblem)
    (sharedGadget : CertifiedReduction incidenceHubProblem sharedGadgetTargetProblem)
    (egress : CertifiedReduction sharedGadgetTargetProblem fixedRoleTargetProblem) : Type 2 :=
  CertifiedRouteProvenance ingress sharedGadget (.explicit egress)
    (CertifiedReduction.comp egress (CertifiedReduction.comp sharedGadget ingress))

/-- The original-input existential route composes its ingress with the shared gadget. -/
noncomputable def resolveOriginalToExistential :
    Protocol.ResolverOutcome originalSourceProblem existentialFinalTargetProblem :=
  Protocol.ComponentResolver.composeTwoStage incidenceSharedGadgetComponentResolution
    originalIngressComponentResolution

/-- The modified-input route composes its distinct ingress with that same shared gadget. -/
noncomputable def resolveModifiedToExistential :
    Protocol.ResolverOutcome modifiedSourceProblem existentialFinalTargetProblem :=
  Protocol.ComponentResolver.composeTwoStage incidenceSharedGadgetComponentResolution
    modifiedIngressComponentResolution

/-- From the incidence hub, the accepted shared gadget reaches the distinct fixed-role egress blocker. -/
def resolveIncidenceToFixedRole :
    Protocol.ResolverOutcome incidenceHubProblem fixedRoleTargetProblem :=
  Protocol.ComponentResolver.composeTwoStage explicitEgressComponentResolution
    incidenceSharedGadgetComponentResolution

/- Both final source variants resolve to their exact thin compositions. -/
@[simp] theorem resolveOriginalToExistential_eq_originalIngress :
    resolveOriginalToExistential = .accepted originalRoute :=
  rfl

/- The modified route reuses that same shared-gadget certificate. -/
@[simp] theorem resolveModifiedToExistential_eq_modifiedIngress :
    resolveModifiedToExistential = .accepted modifiedRoute :=
  rfl

/-- The hub-level fixed-role diagnostic retains its distinct explicit egress blocker. -/
@[simp] theorem resolveIncidenceToFixedRole_eq_sharedGadget :
    resolveIncidenceToFixedRole = .blocked (explicitEgressRequest.missing .directTM) :=
  rfl

/- The original ingress is accepted at its exact source/hub endpoint. -/
@[simp] theorem originalIngressComponentResolution_eq_accepted :
    originalIngressComponentResolution =
      .accepted Domain.SetSystemToIncidenceAdapter.sourceAdapter :=
  rfl

/- The modified ingress is accepted only as the explicit composed source adapter. -/
@[simp] theorem modifiedIngressComponentResolution_eq_accepted :
    modifiedIngressComponentResolution =
      .accepted Domain.ModifiedExactCoverInput.modifiedSourceAdapter :=
  rfl

/- The shared incidence gadget is accepted at its exact reusable component endpoint. -/
@[simp] theorem incidenceSharedGadgetComponentResolution_eq_accepted :
    incidenceSharedGadgetComponentResolution =
      .accepted sharedIncidenceGadget :=
  rfl

/-- The fixed-role egress remains a distinct exact component blocker. -/
@[simp] theorem explicitEgressComponentResolution_eq_missing :
    explicitEgressComponentResolution = .blocked (explicitEgressRequest.missing .directTM) :=
  rfl

/-- The original final certificate stores exactly the two-component program composition. -/
@[simp] theorem originalRoute_eq_componentComposition :
    originalRoute =
      CertifiedReduction.comp sharedIncidenceGadget Domain.SetSystemToIncidenceAdapter.sourceAdapter :=
  rfl

/-- The modified final certificate stores exactly the same gadget after its own ingress. -/
@[simp] theorem modifiedRoute_eq_componentComposition :
    modifiedRoute =
      CertifiedReduction.comp sharedIncidenceGadget Domain.ModifiedExactCoverInput.modifiedSourceAdapter :=
  rfl

/-- The original final certificate stores exactly the two-component program composition. -/
@[simp] theorem originalRoute_program :
    originalRoute.program =
      PolyProg.comp sharedIncidenceGadget.program Domain.SetSystemToIncidenceAdapter.sourceAdapter.program :=
  rfl

/-- The modified final certificate differs only in the reused composed ingress program. -/
@[simp] theorem modifiedRoute_program :
    modifiedRoute.program =
      PolyProg.comp sharedIncidenceGadget.program Domain.ModifiedExactCoverInput.modifiedSourceAdapter.program :=
  rfl

/-- The fixed-role path cannot be promoted while its distinct explicit egress remains blocked. -/
theorem resolveIncidenceToFixedRole_not_accepted
    (certificate : CertifiedReduction incidenceHubProblem fixedRoleTargetProblem) :
    resolveIncidenceToFixedRole ≠ .accepted certificate := by
  intro equality
  cases equality

end IncidenceToRoleGraph
end Routes
end ComplexityReduction
