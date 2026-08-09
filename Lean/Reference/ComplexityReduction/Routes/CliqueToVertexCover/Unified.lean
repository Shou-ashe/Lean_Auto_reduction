/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Provenance
import ComplexityReduction.Problems.Karp21.GraphAtoms
import ComplexityReduction.Protocol.ComponentResolver

/-!
Canonical structured Clique-to-Vertex-Cover shared gadget.

`GraphAtoms.cliqueToVertexCoverEndpointPrimitive` is the unique canonical
hub-level direct-TM primitive for CR's graph-complement construction.  This
route introduces neither a second primitive nor a named route-local program:
the reusable certificate stores exactly that hub primitive's atom.  The public
route is the thin composition of a typed ingress with this shared component.
-/

namespace ComplexityReduction
namespace Routes
namespace CliqueToVertexCover

open Certificate Encoding Program

/-- The exact faithful structured Clique representation used by this route. -/
abbrev sourcePresentation : LawfulEncodedType :=
  Problems.Karp21.GraphAtoms.sourcePresentation .cliqueToVertexCover

/-- The exact faithful structured Vertex-Cover representation used by this route. -/
abbrev targetPresentation : LawfulEncodedType :=
  Problems.Karp21.GraphAtoms.targetPresentation .cliqueToVertexCover

/-- The exact V2 structured Clique endpoint. -/
abbrev sourceProblem : PresentedProblem :=
  Problems.Karp21.GraphAtoms.cliqueStructuredProblem

/-- The exact V2 structured Vertex-Cover endpoint. -/
abbrev targetProblem : PresentedProblem :=
  Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem

/-- The original structured Clique endpoint is the canonical source hub. -/
abbrev originalCliqueProblem : PresentedProblem :=
  sourceProblem

/-- The canonical Clique hub retains the complete source representation. -/
abbrev cliqueHubProblem : PresentedProblem :=
  sourceProblem

/-- The canonical Vertex-Cover hub is the target of the reusable shared gadget. -/
abbrev vertexCoverHubProblem : PresentedProblem :=
  targetProblem

/-- The final structured Vertex-Cover endpoint is already the target hub. -/
abbrev finalVertexCoverProblem : PresentedProblem :=
  targetProblem

/-- The exact identity-eligible ingress endpoint into the Clique hub. -/
abbrev CliqueIngressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .ingress originalCliqueProblem cliqueHubProblem

/-- The canonical request for the exact Clique ingress component. -/
abbrev CliqueIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress originalCliqueProblem cliqueHubProblem

/-- The unique request for the exact Clique ingress. -/
def cliqueIngressRequest : CliqueIngressRequest :=
  .exact

/-- Ingress identity is eligible only because the complete endpoints coincide. -/
theorem cliqueIngress_endpoints_eq :
    originalCliqueProblem = cliqueHubProblem :=
  rfl

/-- The exact reusable Clique-to-Vertex-Cover shared-gadget endpoint. -/
abbrev CliqueToVertexCoverSharedGadgetEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .sharedGadget cliqueHubProblem vertexCoverHubProblem

/-- The canonical request for the Clique-to-Vertex-Cover shared gadget. -/
abbrev CliqueToVertexCoverSharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget cliqueHubProblem vertexCoverHubProblem

/-- The unique request for the canonical GraphAtoms shared gadget. -/
def cliqueToVertexCoverSharedGadgetRequest : CliqueToVertexCoverSharedGadgetRequest :=
  .exact

/-- The exact identity-eligible egress endpoint from the Vertex-Cover hub. -/
abbrev VertexCoverEgressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .egress vertexCoverHubProblem finalVertexCoverProblem

/-- The canonical request for the exact Vertex-Cover egress component. -/
abbrev VertexCoverEgressRequest : Type 2 :=
  Protocol.ComponentRequest .egress vertexCoverHubProblem finalVertexCoverProblem

/-- The unique Vertex-Cover egress request. -/
def vertexCoverEgressRequest : VertexCoverEgressRequest :=
  .exact

/-- Egress identity is eligible only because the complete endpoints coincide. -/
theorem vertexCoverEgress_endpoints_eq :
    vertexCoverHubProblem = finalVertexCoverProblem :=
  rfl

/-- The exact request for the final component composition endpoint. -/
abbrev FinalCompositionRequest : Type 2 :=
  Protocol.ComponentRequest .finalComposition originalCliqueProblem finalVertexCoverProblem

/-- The final request fixes endpoints only; it carries no executable authority. -/
def finalCompositionRequest : FinalCompositionRequest :=
  .exact

/--
The existing CR structured direct-TM Karp record at exactly the public V2 endpoints.

This is a read-only audit anchor.  The certificate below stores the canonical
GraphAtoms hub primitive instead of reconstructing an executable, TM, or cost
from this record.
-/
noncomputable def legacyStructuredReduction :
    ComplexityReduction.TMKarpReduction sourceProblem.toEncodedDecisionProblem
      targetProblem.toEncodedDecisionProblem := by
  simpa [sourceProblem, targetProblem] using
    ComplexityReduction.Karp21.VertexCover.cliqueToVertexCoverStructuredTMKarpReduction

/-- The endpoint-local audit alias is exactly CR's named structured direct-TM edge. -/
@[simp]
theorem legacyStructuredReduction_eq_cliqueToVertexCoverStructuredTMKarpReduction :
    legacyStructuredReduction =
      ComplexityReduction.Karp21.VertexCover.cliqueToVertexCoverStructuredTMKarpReduction :=
  rfl

/--
The sole reusable Clique-to-Vertex-Cover shared-gadget certificate.

Its public declaration deliberately retains the exact `sourceProblem` and
`targetProblem` expressions required by registry validation.  It stores the
canonical GraphAtoms hub primitive directly, so there is no route-local
primitive or program authority.
-/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def certifiedReduction : CertifiedReduction sourceProblem targetProblem where
  program := .atom Problems.Karp21.GraphAtoms.cliqueToVertexCoverEndpointPrimitive
  correct := by
    intro input
    simpa only [Problems.Karp21.GraphAtoms.cliqueStructuredProblem_accepts,
      Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem_accepts] using
      ComplexityReduction.Karp21.VertexCover.map_correct input

/-- The component program is precisely the canonical GraphAtoms hub primitive atom. -/
@[simp]
theorem certifiedReduction_program_eq_endpointPrimitive :
    certifiedReduction.program =
      PolyProg.atom Problems.Karp21.GraphAtoms.cliqueToVertexCoverEndpointPrimitive :=
  rfl

/-- Compatibility name for the certificate's one stored shared-gadget program. -/
@[simp]
theorem certifiedReduction_program :
    certifiedReduction.program =
      PolyProg.atom Problems.Karp21.GraphAtoms.cliqueToVertexCoverEndpointPrimitive :=
  certifiedReduction_program_eq_endpointPrimitive

/-- The shared component executes exactly CR's graph-complement map. -/
@[simp]
theorem certifiedReduction_run (input : sourceProblem.Instance) :
    certifiedReduction.program.run input = ComplexityReduction.Karp21.VertexCover.map input :=
  rfl

/-- The semantic iff is indexed by the shared certificate's exact executable. -/
theorem certifiedReduction_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔
      targetProblem.accepts (certifiedReduction.program.run input) :=
  certifiedReduction.correct input

/-- The semantic facade is exactly the certificate's stored component program. -/
@[simp]
theorem certifiedReduction_semantic_run (input : sourceProblem.Instance) :
    certifiedReduction.toEncodedSemanticReduction.f input =
      ComplexityReduction.Karp21.VertexCover.map input := by
  rw [CertifiedReduction.toEncodedSemanticReduction_f]
  exact certifiedReduction_run input

/-- Direct-TM evidence is derived by compiling the shared component program. -/
theorem certifiedReduction_directTM :
    ComplexityReduction.TMPolyTimeMap sourcePresentation.encodedType targetPresentation.encodedType
      certifiedReduction.program.run :=
  certifiedReduction.directTM

/-- The compiler is the direct-TM field of the canonical GraphAtoms primitive. -/
@[simp]
theorem certifiedReduction_compileTM_eq_endpointPrimitive_directTM :
    certifiedReduction.program.compileTM =
      Problems.Karp21.GraphAtoms.cliqueToVertexCoverEndpointPrimitive.tmPolyTime :=
  rfl

/-- The component compiler is CR's existing structured direct-TM proposition. -/
theorem certifiedReduction_compileTM_eq_legacyStructuredDirectTM :
    certifiedReduction.program.compileTM =
      ComplexityReduction.Karp21.VertexCover.cliqueToVertexCoverStructured_tm_polytime := by
  apply Subsingleton.elim

/-- The component direct-TM projection has the same named CR provenance. -/
theorem certifiedReduction_directTM_eq_legacyStructuredDirectTM :
    certifiedReduction.directTM =
      ComplexityReduction.Karp21.VertexCover.cliqueToVertexCoverStructured_tm_polytime :=
  CertifiedReduction.directTM_eq_compileTM certifiedReduction |>.trans
    certifiedReduction_compileTM_eq_legacyStructuredDirectTM

/-- The direct-TM Karp facade preserves the executable of the stored component program. -/
@[simp]
theorem certifiedReduction_tmKarpReduction_run_is_program :
    certifiedReduction.toTMKarpReduction.f = certifiedReduction.program.run :=
  CertifiedReduction.toTMKarpReduction_f certifiedReduction

/-- The direct-TM Karp facade is compiled from the same stored component program. -/
@[simp]
theorem certifiedReduction_tmKarpReduction_directTM_is_program_compileTM :
    certifiedReduction.toTMKarpReduction.polytime = certifiedReduction.program.compileTM := by
  rw [CertifiedReduction.toTMKarpReduction_polytime,
    CertifiedReduction.directTM_eq_compileTM]

/-- The TM-Karp facade reaches CR's exact structured direct-TM witness. -/
theorem certifiedReduction_tmKarpReduction_directTM_eq_legacyStructuredDirectTM :
    certifiedReduction.toTMKarpReduction.polytime =
      ComplexityReduction.Karp21.VertexCover.cliqueToVertexCoverStructured_tm_polytime :=
  certifiedReduction_tmKarpReduction_directTM_is_program_compileTM.trans
    certifiedReduction_compileTM_eq_legacyStructuredDirectTM

/-- The certificate's one-way CR facade is exactly the named direct-TM Karp record. -/
@[simp]
theorem certifiedReduction_tmKarpReduction_eq_cliqueToVertexCoverStructuredTMKarpReduction :
    certifiedReduction.toTMKarpReduction =
      ComplexityReduction.Karp21.VertexCover.cliqueToVertexCoverStructuredTMKarpReduction :=
  rfl

/-- Exact endpoint coherence with CR's structured direct-TM Karp record. -/
theorem certifiedReduction_endpointExact_legacyStructuredTMKarpCoherence :
    sourceProblem.toEncodedDecisionProblem =
        ComplexityReduction.Combinatorics.Graph.cliqueStructuredDecisionProblem ∧
      targetProblem.toEncodedDecisionProblem =
        ComplexityReduction.Combinatorics.Graph.vertexCoverStructuredDecisionProblem ∧
      certifiedReduction.toTMKarpReduction =
        ComplexityReduction.Karp21.VertexCover.cliqueToVertexCoverStructuredTMKarpReduction ∧
      certifiedReduction.directTM =
        ComplexityReduction.Karp21.VertexCover.cliqueToVertexCoverStructuredTMKarpReduction.polytime ∧
      certifiedReduction.program.compileTM =
        ComplexityReduction.Karp21.VertexCover.cliqueToVertexCoverStructuredTMKarpReduction.polytime :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The compatibility map is derived from the component program compiler. -/
@[simp]
theorem certifiedReduction_tmBackedCostedMap :
    certifiedReduction.toTMBackedCostedMap = certifiedReduction.program.compile :=
  CertifiedReduction.toTMBackedCostedMap_eq_compile certifiedReduction

/-- The compatibility cost is only the component compiler projection. -/
@[simp]
theorem certifiedReduction_compatibilityCost :
    certifiedReduction.compatibilityCost = certifiedReduction.program.compatibilityCost :=
  CertifiedReduction.compatibilityCost_eq_program_compatibilityCost certifiedReduction

/-- The complete shared component has one canonical primitive/program/TM/cost chain. -/
theorem certifiedReduction_oneProgramChain :
    (∀ input,
      sourceProblem.accepts input ↔ targetProblem.accepts (certifiedReduction.program.run input)) ∧
      certifiedReduction.program =
        PolyProg.atom Problems.Karp21.GraphAtoms.cliqueToVertexCoverEndpointPrimitive ∧
      certifiedReduction.directTM = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM =
        Problems.Karp21.GraphAtoms.cliqueToVertexCoverEndpointPrimitive.tmPolyTime ∧
      certifiedReduction.compatibilityCost = certifiedReduction.program.compatibilityCost := by
  refine ⟨certifiedReduction.correct, certifiedReduction_program_eq_endpointPrimitive, ?_, ?_, ?_⟩
  · exact CertifiedReduction.directTM_eq_compileTM certifiedReduction
  · exact CertifiedReduction.directTM_eq_compileTM certifiedReduction |>.trans
      certifiedReduction_compileTM_eq_endpointPrimitive_directTM
  · exact CertifiedReduction.compatibilityCost_eq_program_compatibilityCost certifiedReduction

/-- The GraphAtoms direct-TM primitive is accepted only at its exact shared-gadget endpoint. -/
noncomputable def cliqueToVertexCoverSharedGadgetResolution :
    Protocol.ComponentResolution .sharedGadget cliqueHubProblem vertexCoverHubProblem :=
  Protocol.ComponentResolver.accept cliqueToVertexCoverSharedGadgetRequest certifiedReduction

/-- The exact source ingress is a typed certificate, not a bare endpoint equality. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_ingress]
noncomputable def ingress : CertifiedReduction originalCliqueProblem cliqueHubProblem :=
  .refl cliqueHubProblem

/-- The public route is only the required ingress/shared-gadget composition. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def finalRoute :
    CertifiedReduction originalCliqueProblem finalVertexCoverProblem :=
  CertifiedReduction.comp certifiedReduction ingress

/-- Typed provenance records the identity egress and the exact component composition. -/
@[complexity_reduction_ir_typed_edge]
noncomputable def finalRouteProvenance :
    CertifiedRouteProvenance ingress certifiedReduction .identity finalRoute :=
  CertifiedRouteProvenance.identityEgress ingress certifiedReduction

/-- The final program is definitionally the component program composition. -/
@[simp] theorem finalRoute_program :
    finalRoute.program = PolyProg.comp certifiedReduction.program ingress.program :=
  rfl

/-- The resolver outcome reifies the exact reusable shared-gadget capability. -/
noncomputable def resolveComponentPath :
    Protocol.ResolverOutcome originalCliqueProblem finalVertexCoverProblem :=
  Protocol.ComponentResolver.resolveSingle cliqueToVertexCoverSharedGadgetResolution

/-- The component resolution retains exactly the canonical shared certificate. -/
@[simp] theorem cliqueToVertexCoverSharedGadgetResolution_exact :
    cliqueToVertexCoverSharedGadgetResolution = .accepted certifiedReduction :=
  rfl

/-- The component path yields precisely the accepted shared-gadget certificate. -/
@[simp] theorem resolveComponentPath_exact :
    resolveComponentPath = .accepted certifiedReduction :=
  rfl

end CliqueToVertexCover
end Routes
end ComplexityReduction
