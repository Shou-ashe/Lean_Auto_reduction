/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.MaxCut.StructuredTM.Assembly
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.MaxCut
import ComplexityReduction.Presentation.Partition
import ComplexityReduction.Protocol.ComponentResolver

/-!
The canonical structured Partition-to-Max-Cut V2 route.

`ComplexityReduction` already supplies the faithful textbook construction as
one structured executable, semantic theorem, and direct-TM theorem.  This leaf
admits the exact executable as one V2 `Primitive`, then derives its certificate,
compiler, and compatibility-cost projections from one stored `PolyProg`.
-/

namespace ComplexityReduction
namespace Routes
namespace PartitionToMaxCut

open Certificate Encoding Program

/-- The exact faithful structured Partition presentation used by this route. -/
abbrev sourcePresentation : LawfulEncodedType :=
  Presentation.Partition.structuredPresentation

/-- The exact faithful structured Max-Cut presentation used by this route. -/
abbrev targetPresentation : LawfulEncodedType :=
  Presentation.MaxCut.structuredPresentation

/-- The exact V2 structured Partition endpoint. -/
abbrev sourceProblem : PresentedProblem :=
  Presentation.Partition.structuredProblem

/-- The exact V2 structured Max-Cut endpoint. -/
abbrev targetProblem : PresentedProblem :=
  Presentation.MaxCut.structuredProblem

/-- The original structured Partition endpoint is already the canonical source hub. -/
abbrev originalPartitionProblem : PresentedProblem :=
  sourceProblem

/-- The canonical Partition hub retains the complete source representation. -/
abbrev partitionHubProblem : PresentedProblem :=
  sourceProblem

/-- The canonical Max-Cut hub is the target of the shared gadget. -/
abbrev maxCutHubProblem : PresentedProblem :=
  targetProblem

/-- The final structured Max-Cut endpoint is already the target hub. -/
abbrev finalMaxCutProblem : PresentedProblem :=
  targetProblem

/-- The exact identity-eligible ingress endpoint into the Partition hub. -/
abbrev PartitionIngressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .ingress originalPartitionProblem partitionHubProblem

/-- The canonical request for the exact Partition ingress component. -/
abbrev PartitionIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress originalPartitionProblem partitionHubProblem

/-- The unique Partition ingress request. -/
def partitionIngressRequest : PartitionIngressRequest :=
  .exact

/-- The ingress request fixes its exact original and canonical Partition endpoints. -/
theorem partitionIngressRequest_endpoint_exact :
    partitionIngressRequest.endpoint =
      (show PartitionIngressEndpoint from .exact) :=
  rfl

/-- Ingress identity is eligible only because the complete endpoints coincide. -/
theorem partitionIngress_endpoints_eq :
    originalPartitionProblem = partitionHubProblem :=
  rfl

/-- The exact reusable canonical shared-gadget endpoint. -/
abbrev SharedGadgetEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .sharedGadget partitionHubProblem maxCutHubProblem

/-- The canonical request for the Partition-to-Max-Cut shared gadget. -/
abbrev SharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget partitionHubProblem maxCutHubProblem

/-- The unique request for the standard-audited shared gadget. -/
def sharedGadgetRequest : SharedGadgetRequest :=
  .exact

/-- The shared-gadget request fixes exactly the canonical Partition and Max-Cut hubs. -/
theorem sharedGadgetRequest_endpoint_exact :
    sharedGadgetRequest.endpoint =
      (show SharedGadgetEndpoint from .exact) :=
  rfl

/-- The exact identity-eligible egress endpoint from the Max-Cut hub. -/
abbrev MaxCutEgressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .egress maxCutHubProblem finalMaxCutProblem

/-- The canonical request for the exact Max-Cut egress component. -/
abbrev MaxCutEgressRequest : Type 2 :=
  Protocol.ComponentRequest .egress maxCutHubProblem finalMaxCutProblem

/-- The unique Max-Cut egress request. -/
def maxCutEgressRequest : MaxCutEgressRequest :=
  .exact

/-- The egress request fixes its exact Max-Cut hub endpoint. -/
theorem maxCutEgressRequest_endpoint_exact :
    maxCutEgressRequest.endpoint =
      (show MaxCutEgressEndpoint from .exact) :=
  rfl

/-- Egress identity is eligible only because the complete endpoints coincide. -/
theorem maxCutEgress_endpoints_eq :
    maxCutHubProblem = finalMaxCutProblem :=
  rfl

/--
The exact standard-audited direct-TM primitive for the structured textbook map.
It has the canonical V2 presentations and CR executable as dependent indices,
so no cost-only map, packet, provider, slot, or TM-Karp facade can be a
constructor input.
-/
@[complexity_reduction_ir_typed_primitive]
noncomputable def partitionToMaxCutPrimitive : Primitive sourcePresentation targetPresentation :=
  Primitive.ofTMPolyTime
    ComplexityReduction.Karp21.MaxCut.partitionToMaxCutStructuredTMMap
    ComplexityReduction.Karp21.MaxCut.partitionToMaxCutStructured_tm_polytime

/-- The direct primitive executes exactly CR's structured textbook construction. -/
@[simp]
theorem partitionToMaxCutPrimitive_run (input : sourceProblem.Instance) :
    partitionToMaxCutPrimitive.run input =
      ComplexityReduction.Karp21.MaxCut.partitionToMaxCutStructuredTMMap input :=
  rfl

/-- The primitive retains exactly CR's named structured direct-TM witness. -/
@[simp]
theorem partitionToMaxCutPrimitive_directTM :
    partitionToMaxCutPrimitive.tmPolyTime =
      ComplexityReduction.Karp21.MaxCut.partitionToMaxCutStructured_tm_polytime :=
  rfl

/-- The route has exactly one program: the direct primitive atom. -/
noncomputable def partitionToMaxCutProgram : PolyProg sourcePresentation targetPresentation :=
  .atom partitionToMaxCutPrimitive

/-- The route program is definitionally the exact direct-TM primitive atom. -/
@[simp]
theorem partitionToMaxCutProgram_eq_atom :
    partitionToMaxCutProgram = PolyProg.atom partitionToMaxCutPrimitive :=
  rfl

/-- The one stored program executes exactly CR's structured construction. -/
@[simp]
theorem partitionToMaxCutProgram_run (input : sourceProblem.Instance) :
    partitionToMaxCutProgram.run input =
      ComplexityReduction.Karp21.MaxCut.partitionToMaxCutStructuredTMMap input :=
  rfl

/-- The route program compiler is exactly the direct-TM witness of its primitive atom. -/
@[simp]
theorem partitionToMaxCutProgram_compileTM_eq_primitive_directTM :
    partitionToMaxCutProgram.compileTM = partitionToMaxCutPrimitive.tmPolyTime :=
  rfl

/-- The CR semantic theorem is tied to the same executable stored by the primitive atom. -/
theorem partitionToMaxCutProgram_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔ targetProblem.accepts (partitionToMaxCutProgram.run input) := by
  change ComplexityReduction.Combinatorics.Partition input ↔
    ComplexityReduction.Combinatorics.Graph.MaxCut
      (ComplexityReduction.Karp21.MaxCut.partitionToMaxCutStructuredTMMap input)
  exact ComplexityReduction.Karp21.MaxCut.partitionToMaxCutStructuredTMMap_correct input

/--
The existing direct-TM Karp reduction at exactly the two V2 endpoints.

The simplification unfolds only the two lawful presentation projections; it
does not re-encode inputs, rebuild a machine, or promote a bare cost map.
-/
noncomputable def legacyStructuredReduction :
    ComplexityReduction.TMKarpReduction sourceProblem.toEncodedDecisionProblem
      targetProblem.toEncodedDecisionProblem := by
  simpa [sourceProblem, sourcePresentation, targetProblem, targetPresentation] using
    ComplexityReduction.Karp21.MaxCut.partitionToMaxCutStructuredTMKarpReduction

/--
The sole canonical V2 Partition-to-Max-Cut certificate.  Every executable,
semantic, direct-TM, compiler, and compatibility-cost fact below comes from
`partitionToMaxCutProgram`; the legacy reduction below is only a read-only
endpoint/evidence comparison and not a certificate constructor input.
-/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def certifiedReduction : CertifiedReduction sourceProblem targetProblem where
  program := partitionToMaxCutProgram
  correct := partitionToMaxCutProgram_correct

/-- The certificate stores exactly the one direct-TM primitive atom. -/
@[simp]
theorem certifiedReduction_program :
    certifiedReduction.program =
      PolyProg.atom partitionToMaxCutPrimitive :=
  rfl

/-- The stored V2 program runs exactly CR's structured Partition construction. -/
@[simp]
theorem certifiedReduction_run (input : sourceProblem.Instance) :
    certifiedReduction.program.run input = legacyStructuredReduction.f input :=
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

/-- The compiler is exactly the direct-TM witness stored by the primitive atom. -/
@[simp]
theorem certifiedReduction_compileTM_eq_primitive :
    certifiedReduction.program.compileTM = partitionToMaxCutPrimitive.tmPolyTime :=
  rfl

/-- The certificate direct-TM field is exactly CR's structured direct-TM witness. -/
@[simp]
theorem certifiedReduction_directTM_eq_legacy :
    certifiedReduction.directTM = legacyStructuredReduction.polytime := by
  rw [CertifiedReduction.directTM_eq_compileTM]
  exact certifiedReduction_compileTM_eq_legacy

/-- The direct-TM Karp facade preserves the executable of the one stored program. -/
@[simp]
theorem certifiedReduction_tmKarpReduction_run_is_program :
    certifiedReduction.toTMKarpReduction.f = certifiedReduction.program.run :=
  CertifiedReduction.toTMKarpReduction_f certifiedReduction

/-- The direct-TM Karp facade is compiled from that same stored program. -/
@[simp]
theorem certifiedReduction_tmKarpReduction_directTM_is_program_compileTM :
    certifiedReduction.toTMKarpReduction.polytime = certifiedReduction.program.compileTM := by
  rw [CertifiedReduction.toTMKarpReduction_polytime,
    CertifiedReduction.directTM_eq_compileTM]

/--
Two direct-TM Karp reductions at fixed endpoints are equal once their
executables agree.  Their remaining fields are propositions, so this does
not identify arbitrary machines or manufacture any TM evidence.
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
Projecting the canonical V2 certificate back to CR recovers the exact existing
structured direct-TM Karp record.  This is a one-way typed-certificate
projection, not a fresh machine or cost-only reconstruction.
-/
theorem certifiedReduction_tmKarpReduction_eq_legacyStructuredReduction :
    certifiedReduction.toTMKarpReduction = legacyStructuredReduction := by
  apply tmKarpReduction_eq_of_f_eq
  rw [certifiedReduction_tmKarpReduction_run_is_program]
  funext input
  exact certifiedReduction_run input

/-- The certificate's TM-Karp facade is CR's named Partition-to-Max-Cut structured edge. -/
theorem certifiedReduction_tmKarpReduction_eq_partitionToMaxCutStructuredTMKarpReduction :
    certifiedReduction.toTMKarpReduction =
      ComplexityReduction.Karp21.MaxCut.partitionToMaxCutStructuredTMKarpReduction := by
  rw [certifiedReduction_tmKarpReduction_eq_legacyStructuredReduction]
  rfl

/-- The exact endpoints and all direct-TM projections name one CR structured edge. -/
theorem certifiedReduction_endpointExact_namedCRStructuredTMKarpCoherence :
    sourceProblem.toEncodedDecisionProblem =
        ComplexityReduction.Combinatorics.partitionStructuredDecisionProblem ∧
      targetProblem.toEncodedDecisionProblem =
        ComplexityReduction.Combinatorics.Graph.maxCutStructuredDecisionProblem ∧
      certifiedReduction.toTMKarpReduction =
        ComplexityReduction.Karp21.MaxCut.partitionToMaxCutStructuredTMKarpReduction ∧
      certifiedReduction.toTMKarpReduction.f = certifiedReduction.program.run ∧
      certifiedReduction.toTMKarpReduction.polytime = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM =
        ComplexityReduction.Karp21.MaxCut.partitionToMaxCutStructuredTMKarpReduction.polytime ∧
      certifiedReduction.program.compileTM =
        ComplexityReduction.Karp21.MaxCut.partitionToMaxCutStructuredTMKarpReduction.polytime := by
  exact ⟨rfl, rfl,
    certifiedReduction_tmKarpReduction_eq_partitionToMaxCutStructuredTMKarpReduction,
    certifiedReduction_tmKarpReduction_run_is_program,
    certifiedReduction_tmKarpReduction_directTM_is_program_compileTM,
    certifiedReduction_directTM_eq_legacy.trans (by rfl),
    certifiedReduction_compileTM_eq_legacy.trans (by rfl)⟩

/--
The exact V2 endpoints, program compiler, and legacy TM-Karp facade all name
the same pre-existing structured Partition-to-Max-Cut reduction.
-/
theorem certifiedReduction_endpointExact_legacyStructuredTMKarpCoherence :
    sourceProblem.toEncodedDecisionProblem =
        ComplexityReduction.Combinatorics.partitionStructuredDecisionProblem ∧
      targetProblem.toEncodedDecisionProblem =
        ComplexityReduction.Combinatorics.Graph.maxCutStructuredDecisionProblem ∧
      certifiedReduction.toTMKarpReduction = legacyStructuredReduction ∧
      certifiedReduction.toTMKarpReduction.f = certifiedReduction.program.run ∧
      certifiedReduction.toTMKarpReduction.polytime = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM = legacyStructuredReduction.polytime ∧
      certifiedReduction.program.compileTM = legacyStructuredReduction.polytime := by
  exact ⟨rfl, rfl,
    certifiedReduction_tmKarpReduction_eq_legacyStructuredReduction,
    certifiedReduction_tmKarpReduction_run_is_program,
    certifiedReduction_tmKarpReduction_directTM_is_program_compileTM,
    CertifiedReduction.directTM_eq_compileTM certifiedReduction |>.trans
      certifiedReduction_compileTM_eq_legacy,
    certifiedReduction_compileTM_eq_legacy⟩

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

/-- The compatibility cost follows only from the compiled direct-TM output-size theorem. -/
@[simp]
theorem certifiedReduction_compatibilityCost_eq_outputSizeBound :
    certifiedReduction.compatibilityCost =
      ComplexityReduction.CostedMap.of_encodedPolynomialSizeBound
        (ComplexityReduction.TMPolyTimeMap.outputSizeBound certifiedReduction.program.compileTM) :=
  certifiedReduction.program.compatibilityCost_eq_outputSizeBound

/-- All semantic, executable, TM, and cost evidence has one primitive-program identity. -/
theorem certifiedReduction_oneProgramChain :
    (∀ input,
      sourceProblem.accepts input ↔ targetProblem.accepts (certifiedReduction.program.run input)) ∧
      certifiedReduction.program = PolyProg.atom partitionToMaxCutPrimitive ∧
      certifiedReduction.directTM = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM = partitionToMaxCutPrimitive.tmPolyTime ∧
      certifiedReduction.compatibilityCost = certifiedReduction.program.compatibilityCost := by
  refine ⟨certifiedReduction.correct, certifiedReduction_program, ?_, ?_, ?_⟩
  · exact CertifiedReduction.directTM_eq_compileTM certifiedReduction
  · exact certifiedReduction_compileTM_eq_primitive
  · exact CertifiedReduction.compatibilityCost_eq_program_compatibilityCost certifiedReduction

/--
The direct-TM certificate is admitted only at the exact canonical
shared-gadget endpoint.  No whole-route request/resolver can replace the
component boundary; identity ingress and egress are endpoint facts only.
-/
noncomputable def partitionToMaxCutSharedGadgetResolution :
    Protocol.ComponentResolution .sharedGadget partitionHubProblem maxCutHubProblem :=
  Protocol.ComponentResolver.accept sharedGadgetRequest certifiedReduction

/-- The canonical component path is the accepted shared gadget after identity ingress/egress. -/
noncomputable def resolveComponentPath :
    Protocol.ResolverOutcome originalPartitionProblem finalMaxCutProblem :=
  Protocol.ComponentResolver.resolveSingle partitionToMaxCutSharedGadgetResolution

/-- The shared-gadget resolution retains exactly the canonical certificate. -/
@[simp] theorem partitionToMaxCutSharedGadgetResolution_exact :
    partitionToMaxCutSharedGadgetResolution = .accepted certifiedReduction :=
  rfl

/-- The component path yields precisely the existing shared-gadget certificate. -/
@[simp] theorem resolveComponentPath_exact :
    resolveComponentPath = .accepted certifiedReduction :=
  rfl

end PartitionToMaxCut
end Routes
end ComplexityReduction
