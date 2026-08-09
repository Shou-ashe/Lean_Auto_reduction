/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Provenance
import ComplexityReduction.Domain.GraphToGraphIRAdapter
import ComplexityReduction.Domain.GraphIRRoleAssignmentGadget
import ComplexityReduction.Protocol.ComponentResolver

/-!
Canonical component composition from structured graphs to the RoleGraphIR hub.

`GraphInput` enters only through the dedicated Graph-to-GraphIR ingress
adapter.  The reusable GraphIR-to-RoleGraphIR role-assignment gadget is a
separate closed structural program.  This public route is exactly their
`CertifiedReduction.comp` composition: it introduces no whole-route
primitive, machine, cost map, packet, provider, slot, boundary, descriptor,
or erased-interchange detour.
-/

namespace ComplexityReduction
namespace Routes
namespace GraphToRoleGraph

open Certificate Encoding Program

/-- The concrete structured graph wrapper endpoint. -/
abbrev originalSourceProblem : PresentedProblem :=
  Domain.GraphToGraphIRAdapter.sourceProblem

/-- The canonical wrapper-independent GraphIR hub endpoint. -/
abbrev graphHubProblem : PresentedProblem :=
  Domain.GraphToGraphIRAdapter.hubProblem

/-- The canonical fixed-role RoleGraphIR target endpoint. -/
abbrev roleGraphTargetProblem : PresentedProblem :=
  Domain.GraphIRRoleAssignmentGadget.targetProblem

abbrev GraphHubIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress originalSourceProblem graphHubProblem
abbrev SharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget graphHubProblem roleGraphTargetProblem
abbrev FinalRequest : Type 2 :=
  Protocol.ComponentRequest .finalComposition originalSourceProblem roleGraphTargetProblem

def graphHubIngressRequest : GraphHubIngressRequest := .exact
def sharedGadgetRequest : SharedGadgetRequest := .exact
def finalRequest : FinalRequest := .exact

theorem graphHubIngressRequest_endpoint_exact :
    graphHubIngressRequest.endpoint =
      (show Protocol.ComponentEndpoint .ingress originalSourceProblem graphHubProblem from .exact) :=
  rfl

theorem sharedGadgetRequest_endpoint_exact :
    sharedGadgetRequest.endpoint =
      (show Protocol.ComponentEndpoint .sharedGadget graphHubProblem roleGraphTargetProblem from .exact) :=
  rfl

theorem finalRequest_endpoint_exact :
    finalRequest.endpoint =
      (show Protocol.ComponentEndpoint .finalComposition originalSourceProblem roleGraphTargetProblem from
        .exact) :=
  rfl

/-- The authoritative structured GraphInput ingress component. -/
noncomputable def ingress : CertifiedReduction originalSourceProblem graphHubProblem :=
  Domain.GraphToGraphIRAdapter.sourceAdapter

/-- The one reusable GraphIR-to-RoleGraphIR role-assignment component. -/
noncomputable def sharedGadget : CertifiedReduction graphHubProblem roleGraphTargetProblem :=
  Domain.GraphIRRoleAssignmentGadget.sharedGadget

abbrev IngressResolution : Type 2 :=
  Protocol.ComponentResolution .ingress originalSourceProblem graphHubProblem
abbrev SharedGadgetResolution : Type 2 :=
  Protocol.ComponentResolution .sharedGadget graphHubProblem roleGraphTargetProblem

noncomputable def graphHubIngressResolution : IngressResolution :=
  Protocol.ComponentResolver.accept graphHubIngressRequest ingress

noncomputable def sharedGadgetResolution : SharedGadgetResolution :=
  Protocol.ComponentResolver.accept sharedGadgetRequest sharedGadget

@[simp] theorem graphHubIngressResolution_exact :
    graphHubIngressResolution = .accepted ingress :=
  rfl

@[simp] theorem sharedGadgetResolution_exact :
    sharedGadgetResolution = .accepted sharedGadget :=
  rfl

/-- The only public GraphInput-to-RoleGraphIR certificate is component composition. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def finalRoute : CertifiedReduction originalSourceProblem roleGraphTargetProblem :=
  CertifiedReduction.comp sharedGadget ingress

/-- Typed provenance records the exact ingress/shared-gadget composition of the public route. -/
@[complexity_reduction_ir_typed_edge]
noncomputable def finalRouteProvenance :
    CertifiedRouteProvenance ingress sharedGadget .identity finalRoute :=
  CertifiedRouteProvenance.identityEgress ingress sharedGadget

/-- The route resolver preserves the two component resolutions in construction order. -/
noncomputable def resolve : Protocol.ResolverOutcome originalSourceProblem roleGraphTargetProblem :=
  Protocol.ComponentResolver.composeTwoStage sharedGadgetResolution graphHubIngressResolution

@[simp] theorem resolve_exact : resolve = .accepted finalRoute :=
  rfl

/-- The final executable is definitionally the composition of the two component programs. -/
@[simp] theorem finalRoute_program :
    finalRoute.program = PolyProg.comp sharedGadget.program ingress.program :=
  rfl

/-- The final semantic law is inherited from the two typed component certificates. -/
theorem finalRoute_correct (input : originalSourceProblem.Instance) :
    originalSourceProblem.accepts input ↔
      roleGraphTargetProblem.accepts (finalRoute.program.run input) :=
  finalRoute.correct input

/-- The final direct-TM witness is obtained only by compiling the composite program. -/
theorem finalRoute_directTM :
    finalRoute.directTM = finalRoute.program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM finalRoute

end GraphToRoleGraph
end Routes
end ComplexityReduction
