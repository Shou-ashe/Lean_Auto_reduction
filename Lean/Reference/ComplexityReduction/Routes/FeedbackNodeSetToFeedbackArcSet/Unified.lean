/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.FeedbackArcSetStructuredTM
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Provenance
import ComplexityReduction.Presentation.FeedbackArcSet
import ComplexityReduction.Presentation.FeedbackNodeSet
import ComplexityReduction.Protocol.ComponentResolver

/-!
The canonical structured Feedback-Node-Set-to-Feedback-Arc-Set V2 route.

`ComplexityReduction` already provides the textbook node-splitting construction
as one faithful structured executable, semantic theorem, and direct-TM theorem.
This leaf admits that exact executable only as one V2 `Primitive`, then derives
the `CertifiedReduction`, compiler, and compatibility-cost evidence from its
one stored `PolyProg`.  The legacy `TMKarpReduction` below is retained solely
as a read-only endpoint/evidence comparison; it is not a V2 constructor input.
-/

namespace ComplexityReduction
namespace Routes
namespace FeedbackNodeSetToFeedbackArcSet

open Certificate Encoding Program
open ComplexityReduction.Karp21

/-- The exact faithful structured Feedback Node Set presentation used by this route. -/
abbrev sourcePresentation : LawfulEncodedType :=
  Presentation.FeedbackNodeSet.structuredPresentation

/-- The exact faithful structured Feedback Arc Set presentation used by this route. -/
abbrev targetPresentation : LawfulEncodedType :=
  Presentation.FeedbackArcSet.structuredPresentation

/-- The exact V2 structured Feedback Node Set endpoint. -/
abbrev sourceProblem : PresentedProblem :=
  Presentation.FeedbackNodeSet.structuredProblem

/-- The exact V2 structured Feedback Arc Set endpoint. -/
abbrev targetProblem : PresentedProblem :=
  Presentation.FeedbackArcSet.structuredProblem

/-- The original structured Feedback Node Set endpoint is the canonical source hub. -/
abbrev originalFeedbackNodeSetProblem : PresentedProblem :=
  sourceProblem

/-- The canonical Feedback Node Set hub retains the full source instance. -/
abbrev feedbackNodeSetHubProblem : PresentedProblem :=
  sourceProblem

/-- The canonical Feedback Arc Set hub is the target of the node-splitting gadget. -/
abbrev feedbackArcSetHubProblem : PresentedProblem :=
  targetProblem

/-- The final Feedback Arc Set endpoint is already the canonical target hub. -/
abbrev finalFeedbackArcSetProblem : PresentedProblem :=
  targetProblem

/-- The exact identity-eligible ingress endpoint into the Feedback Node Set hub. -/
abbrev FeedbackNodeSetIngressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .ingress originalFeedbackNodeSetProblem feedbackNodeSetHubProblem

/-- The canonical request for the Feedback Node Set ingress component. -/
abbrev FeedbackNodeSetIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress originalFeedbackNodeSetProblem feedbackNodeSetHubProblem

/-- The unique Feedback Node Set ingress request. -/
def feedbackNodeSetIngressRequest : FeedbackNodeSetIngressRequest :=
  .exact

/-- Ingress identity is eligible only because the complete endpoints coincide. -/
theorem feedbackNodeSetIngress_endpoints_eq :
    originalFeedbackNodeSetProblem = feedbackNodeSetHubProblem :=
  rfl

/-- The exact reusable canonical node-splitting shared-gadget endpoint. -/
abbrev SharedGadgetEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .sharedGadget feedbackNodeSetHubProblem feedbackArcSetHubProblem

/-- The canonical request for the Feedback Node Set to Feedback Arc Set gadget. -/
abbrev SharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget feedbackNodeSetHubProblem feedbackArcSetHubProblem

/-- The unique request for the standard-audited node-splitting gadget. -/
def sharedGadgetRequest : SharedGadgetRequest :=
  .exact

/-- The exact identity-eligible egress endpoint from the Feedback Arc Set hub. -/
abbrev FeedbackArcSetEgressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .egress feedbackArcSetHubProblem finalFeedbackArcSetProblem

/-- The canonical request for the Feedback Arc Set egress component. -/
abbrev FeedbackArcSetEgressRequest : Type 2 :=
  Protocol.ComponentRequest .egress feedbackArcSetHubProblem finalFeedbackArcSetProblem

/-- The unique Feedback Arc Set egress request. -/
def feedbackArcSetEgressRequest : FeedbackArcSetEgressRequest :=
  .exact

/-- Egress identity is eligible only because the complete endpoints coincide. -/
theorem feedbackArcSetEgress_endpoints_eq :
    feedbackArcSetHubProblem = finalFeedbackArcSetProblem :=
  rfl

/--
The exact standard-audited direct-TM primitive for the structured node-splitting map.

Its source and target are the canonical V2 presentations, and its executable is
the CR construction itself.  A cost map, legacy packet, provider, slot, or
TM-Karp facade cannot enter this primitive declaration.
-/
@[complexity_reduction_ir_typed_primitive]
noncomputable def feedbackNodeSetToFeedbackArcSetPrimitive :
    Primitive sourcePresentation targetPresentation :=
  Primitive.ofTMPolyTime
    FeedbackArcSet.feedbackNodeSetToFeedbackArcSetStructuredTMMap
    FeedbackArcSet.feedbackNodeSetToFeedbackArcSetStructured_tm_polytime

/-- The direct primitive executes exactly CR's structured node-splitting construction. -/
@[simp]
theorem feedbackNodeSetToFeedbackArcSetPrimitive_run (input : sourceProblem.Instance) :
    feedbackNodeSetToFeedbackArcSetPrimitive.run input =
      FeedbackArcSet.feedbackNodeSetToFeedbackArcSetStructuredTMMap input :=
  rfl

/-- The route has one program: the atom for its exact direct-TM primitive. -/
noncomputable def feedbackNodeSetToFeedbackArcSetProgram :
    PolyProg sourcePresentation targetPresentation :=
  .atom feedbackNodeSetToFeedbackArcSetPrimitive

/-- The route program is definitionally the exact direct-TM primitive atom. -/
@[simp]
theorem feedbackNodeSetToFeedbackArcSetProgram_eq_atom :
    feedbackNodeSetToFeedbackArcSetProgram =
      PolyProg.atom feedbackNodeSetToFeedbackArcSetPrimitive :=
  rfl

/-- The one stored program executes exactly CR's structured construction. -/
@[simp]
theorem feedbackNodeSetToFeedbackArcSetProgram_run (input : sourceProblem.Instance) :
    feedbackNodeSetToFeedbackArcSetProgram.run input =
      FeedbackArcSet.feedbackNodeSetToFeedbackArcSetStructuredTMMap input :=
  rfl

/-- The CR semantic theorem is tied to the same executable stored by the V2 primitive atom. -/
theorem feedbackNodeSetToFeedbackArcSetProgram_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔
      targetProblem.accepts (feedbackNodeSetToFeedbackArcSetProgram.run input) := by
  change ComplexityReduction.Combinatorics.Graph.FeedbackNodeSet input ↔
    ComplexityReduction.Combinatorics.Graph.FeedbackArcSet
      (FeedbackArcSet.feedbackNodeSetToFeedbackArcSetStructuredTMMap input)
  exact FeedbackArcSet.feedbackNodeSetToFeedbackArcSetStructuredTMMap_correct input

/--
The existing direct-TM Karp reduction at exactly the two V2 endpoints.

The simplification unfolds only the lawful V2 endpoint projections; it does
not transport an encoder, rebuild the direct machine, or admit a bare cost
map.
-/
noncomputable def legacyStructuredReduction :
    ComplexityReduction.TMKarpReduction sourceProblem.toEncodedDecisionProblem
      targetProblem.toEncodedDecisionProblem := by
  simpa [sourceProblem, sourcePresentation, targetProblem, targetPresentation] using
    FeedbackArcSet.feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction

/--
The endpoint-local comparison alias is definitionally CR's one named
structured direct-TM record.  This is only a read-only equality: it does not
reconstruct its machine, polynomial bound, or cost projection.
-/
@[simp]
theorem legacyStructuredReduction_eq_namedCRStructuredTMKarpReduction :
    legacyStructuredReduction =
      FeedbackArcSet.feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction :=
  rfl

/--
The sole canonical V2 Feedback-Node-Set-to-Feedback-Arc-Set certificate.
Every executable, semantic, direct-TM, compiler, and cost projection below is
derived from `feedbackNodeSetToFeedbackArcSetProgram`; the legacy reduction is
not an input to this certificate.
-/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def certifiedReduction : CertifiedReduction sourceProblem targetProblem :=
  { program := feedbackNodeSetToFeedbackArcSetProgram
    correct := feedbackNodeSetToFeedbackArcSetProgram_correct }

/-- The certificate stores exactly the one direct-TM primitive atom. -/
@[simp]
theorem certifiedReduction_program :
    certifiedReduction.program =
      PolyProg.atom
        feedbackNodeSetToFeedbackArcSetPrimitive :=
  rfl

/-- The stored V2 program runs exactly CR's structured textbook construction. -/
@[simp]
theorem certifiedReduction_run (input : sourceProblem.Instance) :
    certifiedReduction.program.run input =
      FeedbackArcSet.feedbackNodeSetToFeedbackArcSetStructuredTMMap input :=
  rfl

/-- The route's semantic iff is indexed by the certified program's exact executable. -/
theorem certifiedReduction_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔ targetProblem.accepts (certifiedReduction.program.run input) :=
  certifiedReduction.correct input

/-- Direct-TM evidence is derived by compiling the certified route's one program. -/
theorem certifiedReduction_directTM :
    ComplexityReduction.TMPolyTimeMap sourcePresentation.encodedType targetPresentation.encodedType
      certifiedReduction.program.run :=
  certifiedReduction.directTM

/-- The program compiler retains exactly the direct-TM witness from the legacy reduction. -/
@[simp]
theorem certifiedReduction_compileTM_eq_legacy :
    certifiedReduction.program.compileTM = legacyStructuredReduction.polytime :=
  rfl

/-- The program compiler is exactly the direct-TM witness stored by the canonical primitive. -/
@[simp]
theorem certifiedReduction_compileTM_eq_primitive :
    certifiedReduction.program.compileTM = feedbackNodeSetToFeedbackArcSetPrimitive.tmPolyTime :=
  rfl

/-- The certificate direct-TM facade is the compiler output of the same program. -/
@[simp]
theorem certifiedReduction_directTM_eq_legacy :
    certifiedReduction.directTM = legacyStructuredReduction.polytime :=
  CertifiedReduction.directTM_eq_compileTM certifiedReduction |>.trans
    certifiedReduction_compileTM_eq_legacy

/-- The TM-Karp facade preserves the executable of the certificate's one program. -/
@[simp]
theorem certifiedReduction_tmKarpReduction_run_is_program :
    certifiedReduction.toTMKarpReduction.f = certifiedReduction.program.run :=
  CertifiedReduction.toTMKarpReduction_f certifiedReduction

/-- The TM-Karp facade derives its direct-TM witness by compiling that one program. -/
@[simp]
theorem certifiedReduction_tmKarpReduction_directTM_is_program_compileTM :
    certifiedReduction.toTMKarpReduction.polytime = certifiedReduction.program.compileTM := by
  rw [CertifiedReduction.toTMKarpReduction_polytime,
    CertifiedReduction.directTM_eq_compileTM]

/--
At fixed endpoints, direct-TM Karp reductions are determined by their
executable; all remaining fields are proofs.  This is used only to compare
the certificate projection with the already-audited CR record.
-/
private theorem tmKarpReduction_eq_of_f_eq
    {A B : ComplexityReduction.EncodedDecisionProblem}
    (first second : ComplexityReduction.TMKarpReduction A B)
    (h : first.f = second.f) : first = second := by
  cases first
  cases second
  cases h
  rfl

/--
The one-way TM-Karp projection of the typed certificate recovers exactly the
existing structured CR reduction.  It does not construct a new machine or
promote a cost map into direct-TM evidence.
-/
@[simp]
theorem certifiedReduction_tmKarpReduction_eq_legacyStructuredReduction :
    certifiedReduction.toTMKarpReduction = legacyStructuredReduction := by
  apply tmKarpReduction_eq_of_f_eq
  rw [certifiedReduction_tmKarpReduction_run_is_program]
  funext input
  exact certifiedReduction_run input

/--
The typed certificate's one-way TM-Karp facade is exactly CR's named
structured Feedback-Node-Set-to-Feedback-Arc-Set record at these endpoints.
-/
theorem
    certifiedReduction_tmKarpReduction_eq_feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction :
    certifiedReduction.toTMKarpReduction =
      FeedbackArcSet.feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction :=
  certifiedReduction_tmKarpReduction_eq_legacyStructuredReduction.trans
    legacyStructuredReduction_eq_namedCRStructuredTMKarpReduction

/-- The compiled program carries the direct-TM field of CR's named record. -/
theorem
    certifiedReduction_compileTM_eq_feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction_polytime :
    certifiedReduction.program.compileTM =
      FeedbackArcSet.feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction.polytime :=
  certifiedReduction_compileTM_eq_legacy.trans (by rfl)

/-- The certificate's direct-TM facade carries that same named CR witness. -/
theorem
    certifiedReduction_directTM_eq_feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction_polytime :
    certifiedReduction.directTM =
      FeedbackArcSet.feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction.polytime :=
  certifiedReduction_directTM_eq_legacy.trans (by rfl)

/--
The canonical V2 certificate, its stored program/compiler, and its legacy
TM-Karp projection all denote the same existing structured node-splitting
edge at the exact V2 endpoints.
-/
theorem certifiedReduction_legacyStructuredTMKarpCoherence :
    certifiedReduction.toTMKarpReduction = legacyStructuredReduction ∧
      certifiedReduction.toTMKarpReduction.f = certifiedReduction.program.run ∧
      certifiedReduction.toTMKarpReduction.polytime = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM = legacyStructuredReduction.polytime ∧
      certifiedReduction.program.compileTM = legacyStructuredReduction.polytime := by
  exact ⟨certifiedReduction_tmKarpReduction_eq_legacyStructuredReduction,
    certifiedReduction_tmKarpReduction_run_is_program,
    certifiedReduction_tmKarpReduction_directTM_is_program_compileTM,
    certifiedReduction_directTM_eq_legacy,
    certifiedReduction_compileTM_eq_legacy⟩

/--
Endpoint-exact coherence with CR's named structured node-splitting record.
The certified program, compiler, direct-TM field, and one-way TM-Karp facade
all remain projections of the same primitive atom and CR evidence.
-/
theorem certifiedReduction_endpointExact_namedCRStructuredTMKarpCoherence :
    sourceProblem.toEncodedDecisionProblem =
        ComplexityReduction.Combinatorics.Graph.feedbackNodeSetStructuredDecisionProblem ∧
      targetProblem.toEncodedDecisionProblem =
        ComplexityReduction.Combinatorics.Graph.feedbackArcSetStructuredDecisionProblem ∧
      certifiedReduction.program =
        PolyProg.atom feedbackNodeSetToFeedbackArcSetPrimitive ∧
      certifiedReduction.toTMKarpReduction =
        FeedbackArcSet.feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction ∧
      certifiedReduction.toTMKarpReduction.f = certifiedReduction.program.run ∧
      certifiedReduction.toTMKarpReduction.f =
        FeedbackArcSet.feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction.f ∧
      certifiedReduction.toTMKarpReduction.polytime =
        certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM = certifiedReduction.program.compileTM ∧
      certifiedReduction.program.compileTM =
        feedbackNodeSetToFeedbackArcSetPrimitive.tmPolyTime ∧
      feedbackNodeSetToFeedbackArcSetPrimitive.tmPolyTime =
        FeedbackArcSet.feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction.polytime ∧
      certifiedReduction.directTM =
        FeedbackArcSet.feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction.polytime ∧
      certifiedReduction.program.compileTM =
        FeedbackArcSet.feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction.polytime := by
  refine ⟨rfl, rfl, certifiedReduction_program,
    certifiedReduction_tmKarpReduction_eq_feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction,
    certifiedReduction_tmKarpReduction_run_is_program, ?_,
    certifiedReduction_tmKarpReduction_directTM_is_program_compileTM,
    CertifiedReduction.directTM_eq_compileTM certifiedReduction,
    certifiedReduction_compileTM_eq_primitive, ?_,
    certifiedReduction_directTM_eq_feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction_polytime,
    certifiedReduction_compileTM_eq_feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction_polytime⟩
  · exact congrArg ComplexityReduction.TMKarpReduction.f
      certifiedReduction_tmKarpReduction_eq_feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction
  · exact certifiedReduction_compileTM_eq_primitive.symm.trans
      certifiedReduction_compileTM_eq_feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction_polytime

/--
Complete endpoint-exact provenance for the canonical Feedback-Node-Set to
Feedback-Arc-Set certificate.  The exact presentations, sole direct-TM atom,
executable, compiler evidence, compatibility cost, and one-way CR facade all
derive from the same checked structured node-splitting construction.
-/
theorem certifiedReduction_exactProgramCertificateProvenance :
    certifiedReduction.program.endpointIdentities =
        ⟨sourceProblem.representationIdentity, targetProblem.representationIdentity⟩ ∧
      certifiedReduction.program =
        PolyProg.atom feedbackNodeSetToFeedbackArcSetPrimitive ∧
      certifiedReduction.program.run =
        FeedbackArcSet.feedbackNodeSetToFeedbackArcSetStructuredTMMap ∧
      certifiedReduction.program.compileTM =
        FeedbackArcSet.feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction.polytime ∧
      certifiedReduction.directTM = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM = feedbackNodeSetToFeedbackArcSetPrimitive.tmPolyTime ∧
      feedbackNodeSetToFeedbackArcSetPrimitive.tmPolyTime =
        FeedbackArcSet.feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction.polytime ∧
      certifiedReduction.compatibilityCost = certifiedReduction.program.compatibilityCost ∧
      certifiedReduction.toTMKarpReduction =
        FeedbackArcSet.feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction := by
  exact ⟨rfl, certifiedReduction_program, rfl,
    certifiedReduction_compileTM_eq_feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction_polytime,
    CertifiedReduction.directTM_eq_compileTM certifiedReduction,
    certifiedReduction_directTM_eq_legacy.trans
      certifiedReduction_compileTM_eq_primitive.symm,
    certifiedReduction_compileTM_eq_primitive.symm.trans
      certifiedReduction_compileTM_eq_feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction_polytime,
    rfl,
    certifiedReduction_tmKarpReduction_eq_feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction⟩

/-- The compatible TM-backed map is derived from program compilation, never from a bare cost. -/
@[simp]
theorem certifiedReduction_tmBackedCostedMap :
    certifiedReduction.toTMBackedCostedMap = certifiedReduction.program.compile :=
  rfl

/-- The route compatibility cost is only the compiler projection of the stored program. -/
@[simp]
theorem certifiedReduction_compatibilityCost :
    certifiedReduction.compatibilityCost = certifiedReduction.program.compatibilityCost :=
  rfl

/-- The route cost follows only from the compiled direct-TM output-size theorem. -/
@[simp]
theorem certifiedReduction_compatibilityCost_eq_outputSizeBound :
    certifiedReduction.compatibilityCost =
      ComplexityReduction.CostedMap.of_encodedPolynomialSizeBound
        (ComplexityReduction.TMPolyTimeMap.outputSizeBound certifiedReduction.program.compileTM) :=
  certifiedReduction.program.compatibilityCost_eq_outputSizeBound

/--
The semantic theorem, executable, direct-TM realization, and cost projection
of the concrete route all pass through the one stored primitive atom.
-/
theorem certifiedReduction_oneProgramChain :
    (∀ input,
      sourceProblem.accepts input ↔
        targetProblem.accepts (certifiedReduction.program.run input)) ∧
      certifiedReduction.program = PolyProg.atom feedbackNodeSetToFeedbackArcSetPrimitive ∧
      certifiedReduction.directTM = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM = feedbackNodeSetToFeedbackArcSetPrimitive.tmPolyTime ∧
      certifiedReduction.compatibilityCost = certifiedReduction.program.compatibilityCost := by
  refine ⟨certifiedReduction.correct, certifiedReduction_program, ?_, ?_, ?_⟩
  · exact CertifiedReduction.directTM_eq_compileTM certifiedReduction
  · exact certifiedReduction_compileTM_eq_primitive
  · exact CertifiedReduction.compatibilityCost_eq_program_compatibilityCost certifiedReduction

/-- The direct-TM node-splitting certificate is accepted only at its shared-gadget endpoint. -/
noncomputable def feedbackNodeSetToFeedbackArcSetSharedGadgetResolution :
    Protocol.ComponentResolution .sharedGadget feedbackNodeSetHubProblem feedbackArcSetHubProblem :=
  Protocol.ComponentResolver.accept sharedGadgetRequest certifiedReduction

/-- The identity ingress is a typed component certificate, not a bare endpoint equality. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_ingress]
noncomputable def ingress :
    CertifiedReduction originalFeedbackNodeSetProblem feedbackNodeSetHubProblem :=
  .refl feedbackNodeSetHubProblem

/-- The public route is the thin composition of the ingress and shared node-splitting gadget. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def finalRoute :
    CertifiedReduction originalFeedbackNodeSetProblem finalFeedbackArcSetProblem :=
  CertifiedReduction.comp certifiedReduction ingress

/-- Typed provenance records the identity egress and final component composition. -/
@[complexity_reduction_ir_typed_edge]
noncomputable def finalRouteProvenance :
    CertifiedRouteProvenance ingress certifiedReduction .identity finalRoute :=
  CertifiedRouteProvenance.identityEgress ingress certifiedReduction

/-- The final program is definitionally the component composition. -/
@[simp] theorem finalRoute_program :
    finalRoute.program = PolyProg.comp certifiedReduction.program ingress.program :=
  rfl

/-- The resolver outcome reifies the exact shared-gadget component capability. -/
noncomputable def resolveComponentPath :
    Protocol.ResolverOutcome originalFeedbackNodeSetProblem finalFeedbackArcSetProblem :=
  Protocol.ComponentResolver.resolveSingle feedbackNodeSetToFeedbackArcSetSharedGadgetResolution

/-- The shared-gadget resolution retains exactly the canonical certificate. -/
@[simp] theorem feedbackNodeSetToFeedbackArcSetSharedGadgetResolution_exact :
    feedbackNodeSetToFeedbackArcSetSharedGadgetResolution = .accepted certifiedReduction :=
  rfl

/-- The component path yields precisely the accepted shared-gadget certificate. -/
@[simp] theorem resolveComponentPath_exact :
    resolveComponentPath = .accepted certifiedReduction :=
  rfl

end FeedbackNodeSetToFeedbackArcSet
end Routes
end ComplexityReduction
