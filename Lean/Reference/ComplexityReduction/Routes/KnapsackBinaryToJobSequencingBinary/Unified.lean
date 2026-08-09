/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.JobSequencingBinaryStructuredTM
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.JobSequencingBinary
import ComplexityReduction.Presentation.KnapsackBinary
import ComplexityReduction.Protocol.ComponentResolver

/-!
Canonical binary Knapsack-hub to Job-Sequencing-hub shared gadget.

`ComplexityReduction` already supplies this textbook construction as one
structured `TMKarpReduction`.  The source and target below are canonical
binary numeric hubs, not route-local endpoint copies.  This leaf projects the
direct-TM evidence into one shared-gadget `CertifiedReduction`, retaining one
program for its executable, semantic law, compiler, and compatibility-cost
projections.
-/

namespace ComplexityReduction
namespace Routes
namespace KnapsackBinaryToJobSequencingBinary

open Certificate Encoding Program

/-- The exact binary structured Knapsack presentation used by this route. -/
abbrev sourcePresentation : LawfulEncodedType :=
  Presentation.KnapsackBinary.structuredPresentation

/-- The exact binary structured Job Sequencing presentation used by this route. -/
abbrev targetPresentation : LawfulEncodedType :=
  Presentation.JobSequencingBinary.binaryStructuredPresentation

/-- The exact V2 binary structured Knapsack endpoint. -/
abbrev sourceProblem : PresentedProblem :=
  Presentation.KnapsackBinary.structuredProblem

/-- The exact V2 binary structured Job Sequencing endpoint. -/
abbrev targetProblem : PresentedProblem :=
  Presentation.JobSequencingBinary.binaryStructuredProblem

/-- The original binary Knapsack endpoint is definitionally the source hub. -/
abbrev originalKnapsackBinaryProblem : PresentedProblem :=
  sourceProblem

/-- The canonical binary Knapsack hub retains the complete source representation. -/
abbrev knapsackBinaryHubProblem : PresentedProblem :=
  sourceProblem

/-- The canonical binary Job-Sequencing hub is the target of the shared gadget. -/
abbrev jobSequencingBinaryHubProblem : PresentedProblem :=
  targetProblem

/-- The final binary Job-Sequencing endpoint is the target hub itself. -/
abbrev finalJobSequencingBinaryProblem : PresentedProblem :=
  targetProblem

/-- The exact identity-eligible ingress endpoint into the binary Knapsack hub. -/
abbrev KnapsackBinaryIngressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .ingress originalKnapsackBinaryProblem knapsackBinaryHubProblem

/-- The canonical request for the exact binary Knapsack ingress endpoint. -/
abbrev KnapsackBinaryIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress originalKnapsackBinaryProblem knapsackBinaryHubProblem

/-- The unique binary Knapsack ingress request. -/
def knapsackBinaryIngressRequest : KnapsackBinaryIngressRequest :=
  .exact

/-- The ingress request fixes its exact original and canonical binary Knapsack endpoints. -/
theorem knapsackBinaryIngressRequest_endpoint_exact :
    knapsackBinaryIngressRequest.endpoint =
      (show KnapsackBinaryIngressEndpoint from .exact) :=
  rfl

/-- Ingress identity is eligible only because the complete endpoints coincide. -/
theorem knapsackBinaryIngress_endpoints_eq :
    originalKnapsackBinaryProblem = knapsackBinaryHubProblem :=
  rfl

/-- The exact reusable binary-hub shared-gadget endpoint. -/
abbrev SharedGadgetEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .sharedGadget knapsackBinaryHubProblem jobSequencingBinaryHubProblem

/-- The canonical request for the binary Knapsack-to-Job-Sequencing gadget. -/
abbrev SharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget knapsackBinaryHubProblem jobSequencingBinaryHubProblem

/-- The unique request for the standard-audited shared gadget. -/
def sharedGadgetRequest : SharedGadgetRequest :=
  .exact

/-- The shared-gadget request fixes exactly the two canonical binary hubs. -/
theorem sharedGadgetRequest_endpoint_exact :
    sharedGadgetRequest.endpoint =
      (show SharedGadgetEndpoint from .exact) :=
  rfl

/-- The exact identity-eligible egress endpoint from the Job-Sequencing hub. -/
abbrev JobSequencingBinaryEgressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .egress jobSequencingBinaryHubProblem finalJobSequencingBinaryProblem

/-- The canonical request for the exact binary Job-Sequencing egress endpoint. -/
abbrev JobSequencingBinaryEgressRequest : Type 2 :=
  Protocol.ComponentRequest .egress jobSequencingBinaryHubProblem finalJobSequencingBinaryProblem

/-- The unique binary Job-Sequencing egress request. -/
def jobSequencingBinaryEgressRequest : JobSequencingBinaryEgressRequest :=
  .exact

/-- The egress request fixes its exact binary Job-Sequencing hub endpoint. -/
theorem jobSequencingBinaryEgressRequest_endpoint_exact :
    jobSequencingBinaryEgressRequest.endpoint =
      (show JobSequencingBinaryEgressEndpoint from .exact) :=
  rfl

/-- Egress identity is eligible only because the complete endpoints coincide. -/
theorem jobSequencingBinaryEgress_endpoints_eq :
    jobSequencingBinaryHubProblem = finalJobSequencingBinaryProblem :=
  rfl

/--
The existing direct-TM Karp reduction at exactly the two V2 endpoints.

The simplification unfolds only the two lawful presentation aliases; it does
not re-encode inputs, rebuild a machine, or promote a bare cost map.
-/
noncomputable def legacyStructuredReduction :
    ComplexityReduction.TMKarpReduction sourceProblem.toEncodedDecisionProblem
      targetProblem.toEncodedDecisionProblem := by
  simpa [sourceProblem, sourcePresentation, targetProblem, targetPresentation] using
    ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingBinaryStructuredTMKarpReduction

/--
The one typed primitive for the shared gadget. Its executable and direct-TM
proof are CR's named binary structured map and direct theorem; no legacy cost
map or route-local machine is an input to this declaration.
-/
@[complexity_reduction_ir_typed_primitive]
noncomputable def directTMPrimitive : Primitive sourcePresentation targetPresentation :=
  Primitive.ofTMPolyTime
    ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingBinaryStructuredTMMap
    ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingBinaryStructured_tm_polytime

/-- The primitive executes exactly CR's named binary structured construction. -/
@[simp]
theorem directTMPrimitive_run (input : sourceProblem.Instance) :
    directTMPrimitive.run input = legacyStructuredReduction.f input :=
  rfl

/-- The primitive preserves CR's direct-TM theorem exactly. -/
@[simp]
theorem directTMPrimitive_directTM_eq_standardDirectTM :
    directTMPrimitive.tmPolyTime =
      ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingBinaryStructured_tm_polytime :=
  rfl

/-- The primitive and the read-only Karp record have the same fixed-endpoint witness. -/
@[simp]
theorem directTMPrimitive_directTM :
    directTMPrimitive.tmPolyTime = legacyStructuredReduction.polytime :=
  Subsingleton.elim _ _

/-- The route has one executable program: the exact direct-TM primitive atom. -/
noncomputable def program : PolyProg sourcePresentation targetPresentation :=
  .atom directTMPrimitive

/-- The named route program is definitionally the primitive atom. -/
@[simp]
theorem program_eq_atom : program = PolyProg.atom directTMPrimitive :=
  rfl

/-- The named program executes precisely CR's binary structured map. -/
@[simp]
theorem program_run (input : sourceProblem.Instance) :
    program.run input = legacyStructuredReduction.f input :=
  rfl

/-- Compiling the named program preserves the primitive's same direct-TM witness. -/
@[simp]
theorem program_compileTM_eq_directTMPrimitive_directTM :
    program.compileTM = directTMPrimitive.tmPolyTime :=
  rfl

/--
The canonical V2 binary Knapsack-to-Job-Sequencing shared-gadget certificate.
Every executable, semantic, direct-TM, compiler, and compatibility-cost
projection below comes from `program` and its one direct-TM primitive atom.
The CR Karp record remains a read-only endpoint/evidence comparison.
-/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def certifiedReduction : CertifiedReduction sourceProblem targetProblem where
  program := program
  correct := legacyStructuredReduction.correct

/--
The gadget is accepted only at its exact canonical shared-gadget component
endpoint.  This result stores the existing certificate and creates neither a
second program nor a route-local certificate.
-/
noncomputable def knapsackToJobSequencingSharedGadgetResolution :
    Protocol.ComponentResolution .sharedGadget knapsackBinaryHubProblem
      jobSequencingBinaryHubProblem :=
  Protocol.ComponentResolver.accept sharedGadgetRequest certifiedReduction

/-- The canonical component path is the one accepted shared gadget after identity ingress. -/
noncomputable def resolveComponentPath :
    Protocol.ResolverOutcome originalKnapsackBinaryProblem finalJobSequencingBinaryProblem :=
  Protocol.ComponentResolver.resolveSingle knapsackToJobSequencingSharedGadgetResolution

/-- The component resolver retains exactly the canonical shared-gadget certificate. -/
@[simp] theorem knapsackToJobSequencingSharedGadgetResolution_exact :
    knapsackToJobSequencingSharedGadgetResolution = .accepted certifiedReduction :=
  rfl

/-- The component path yields precisely the existing shared-gadget certificate. -/
@[simp] theorem resolveComponentPath_exact :
    resolveComponentPath = .accepted certifiedReduction :=
  rfl

/-- The certificate stores the one program atom projected from the legacy executable. -/
@[simp]
theorem certifiedReduction_program :
    certifiedReduction.program =
      PolyProg.atom directTMPrimitive :=
  rfl

/-- The certificate stores the route's one named direct-TM primitive program. -/
@[simp]
theorem certifiedReduction_program_eq_program :
    certifiedReduction.program = program :=
  rfl

/-- The stored V2 program runs exactly CR's binary structured textbook construction. -/
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
  Subsingleton.elim _ _

/--
The direct-TM field retained by the certificate is the exact witness from the
audited binary structured route, never a cost-only compatibility substitute.
-/
@[simp]
theorem certifiedReduction_directTM_eq_legacy :
    certifiedReduction.directTM = legacyStructuredReduction.polytime :=
  CertifiedReduction.directTM_eq_compileTM certifiedReduction |>.trans
    certifiedReduction_compileTM_eq_legacy

/-- The certificate compiler is the direct-TM component of its exact primitive atom. -/
@[simp]
theorem certifiedReduction_compileTM_eq_directTMPrimitive_directTM :
    certifiedReduction.program.compileTM = directTMPrimitive.tmPolyTime :=
  rfl

/-- The shared-gadget certificate's direct-TM field is CR's direct theorem. -/
theorem certifiedReduction_directTM_eq_standardDirectTM :
    certifiedReduction.directTM =
      ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingBinaryStructured_tm_polytime :=
  (CertifiedReduction.directTM_eq_compileTM certifiedReduction).trans
    (program_compileTM_eq_directTMPrimitive_directTM.trans
      directTMPrimitive_directTM_eq_standardDirectTM)

/-- The direct-TM Karp facade preserves the executable of the stored program. -/
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
Projecting the canonical certificate back to CR recovers the exact existing
binary structured direct-TM Karp record.  This only observes the one-way
certificate adapter; it neither builds a machine nor promotes a bare cost map.
-/
@[simp]
private theorem tmKarpReduction_eq_of_f_eq
    {A B : ComplexityReduction.EncodedDecisionProblem}
    (first second : ComplexityReduction.TMKarpReduction A B)
    (h : first.f = second.f) : first = second := by
  cases first
  cases second
  cases h
  rfl

theorem certifiedReduction_tmKarpReduction_eq_legacyStructuredReduction :
    certifiedReduction.toTMKarpReduction = legacyStructuredReduction := by
  apply tmKarpReduction_eq_of_f_eq
  rw [CertifiedReduction.toTMKarpReduction_f]
  funext input
  exact certifiedReduction_run input

/--
The V2 certificate's TM-Karp facade is CR's named binary structured
Knapsack-to-Job-Sequencing edge at the same encoded endpoints.
-/
theorem certifiedReduction_tmKarpReduction_eq_knapsackToJobSequencingBinaryStructuredTMKarpReduction :
    certifiedReduction.toTMKarpReduction =
      ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingBinaryStructuredTMKarpReduction := by
  rw [certifiedReduction_tmKarpReduction_eq_legacyStructuredReduction]
  rfl

/-- The compiler output is the direct-TM witness of CR's named binary structured route. -/
theorem certifiedReduction_compileTM_eq_knapsackToJobSequencingBinaryStructuredTMKarpReduction_polytime :
    certifiedReduction.program.compileTM =
      ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingBinaryStructuredTMKarpReduction.polytime := by
  rw [certifiedReduction_compileTM_eq_legacy]
  rfl

/--
The endpoint-fixed certificate, its stored program, compiler, and legacy
TM-Karp facade all describe one pre-existing binary structured reduction.
-/
theorem certifiedReduction_endpointExact_legacyStructuredTMKarpCoherence :
    sourceProblem.toEncodedDecisionProblem =
        ComplexityReduction.Combinatorics.knapsackBinaryStructuredDecisionProblem ∧
      targetProblem.toEncodedDecisionProblem =
        ComplexityReduction.Combinatorics.jobSequencingBinaryStructuredDecisionProblem ∧
      certifiedReduction.toTMKarpReduction = legacyStructuredReduction ∧
      certifiedReduction.toTMKarpReduction.f = certifiedReduction.program.run ∧
      certifiedReduction.toTMKarpReduction.polytime = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM = legacyStructuredReduction.polytime ∧
      certifiedReduction.program.compileTM = legacyStructuredReduction.polytime :=
  ⟨rfl, rfl,
    certifiedReduction_tmKarpReduction_eq_legacyStructuredReduction,
    certifiedReduction_tmKarpReduction_run_is_program,
    certifiedReduction_tmKarpReduction_directTM_is_program_compileTM,
    certifiedReduction_directTM_eq_legacy,
    certifiedReduction_compileTM_eq_legacy⟩

/--
The same one-program chain stated directly against CR's named binary
structured TM-Karp record, not merely the local endpoint alias.
-/
theorem certifiedReduction_endpointExact_namedCRStructuredTMKarpCoherence :
    sourceProblem.toEncodedDecisionProblem =
        ComplexityReduction.Combinatorics.knapsackBinaryStructuredDecisionProblem ∧
      targetProblem.toEncodedDecisionProblem =
        ComplexityReduction.Combinatorics.jobSequencingBinaryStructuredDecisionProblem ∧
      certifiedReduction.toTMKarpReduction =
        ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingBinaryStructuredTMKarpReduction ∧
      certifiedReduction.toTMKarpReduction.f = certifiedReduction.program.run ∧
      certifiedReduction.toTMKarpReduction.polytime = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM =
        ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingBinaryStructuredTMKarpReduction.polytime ∧
      certifiedReduction.program.compileTM =
        ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingBinaryStructuredTMKarpReduction.polytime := by
  exact ⟨rfl, rfl,
    certifiedReduction_tmKarpReduction_eq_knapsackToJobSequencingBinaryStructuredTMKarpReduction,
    certifiedReduction_tmKarpReduction_run_is_program,
    certifiedReduction_tmKarpReduction_directTM_is_program_compileTM,
    certifiedReduction_directTM_eq_legacy.trans (by rfl),
    certifiedReduction_compileTM_eq_knapsackToJobSequencingBinaryStructuredTMKarpReduction_polytime⟩

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

/-- Every semantic, direct-TM, and cost projection shares the exact primitive atom. -/
theorem certifiedReduction_oneProgramChain :
    (∀ input,
      sourceProblem.accepts input ↔ targetProblem.accepts (certifiedReduction.program.run input)) ∧
      certifiedReduction.program = PolyProg.atom directTMPrimitive ∧
      certifiedReduction.directTM = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM = directTMPrimitive.tmPolyTime ∧
      certifiedReduction.compatibilityCost = certifiedReduction.program.compatibilityCost := by
  refine ⟨certifiedReduction.correct, certifiedReduction_program, ?_, ?_, ?_⟩
  · exact CertifiedReduction.directTM_eq_compileTM certifiedReduction
  · rfl
  · exact CertifiedReduction.compatibilityCost_eq_program_compatibilityCost certifiedReduction

end KnapsackBinaryToJobSequencingBinary
end Routes
end ComplexityReduction
