/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.JobSequencingStructuredTM
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.JobSequencing
import ComplexityReduction.Presentation.Knapsack
import ComplexityReduction.Protocol.ComponentResolver

/-!
The canonical structured Knapsack-to-Job-Sequencing V2 route.

`ComplexityReduction` already supplies the unary textbook construction as one
faithful structured `TMKarpReduction`.  This leaf projects that direct-TM
evidence into a V2 `CertifiedReduction`; its executable, semantic law,
compiler, and compatibility cost are all indexed by one stored `PolyProg`.
-/

namespace ComplexityReduction
namespace Routes
namespace KnapsackToJobSequencing

open Certificate Encoding Program

/-- The exact faithful structured Knapsack presentation used by this route. -/
abbrev sourcePresentation : LawfulEncodedType :=
  Presentation.Knapsack.structuredPresentation

/-- The exact faithful structured Job Sequencing presentation used by this route. -/
abbrev targetPresentation : LawfulEncodedType :=
  Presentation.JobSequencing.structuredPresentation

/-- The exact V2 structured Knapsack endpoint. -/
abbrev sourceProblem : PresentedProblem :=
  Presentation.Knapsack.structuredProblem

/-- The exact V2 structured Job Sequencing endpoint. -/
abbrev targetProblem : PresentedProblem :=
  Presentation.JobSequencing.structuredProblem

/--
The existing direct-TM Karp reduction at exactly the two V2 endpoints.

The simplification unfolds only the lawful endpoint aliases.  It neither
rebuilds the textbook machine nor promotes a bare compatibility cost map.
-/
noncomputable def legacyStructuredReduction :
    ComplexityReduction.TMKarpReduction sourceProblem.toEncodedDecisionProblem
      targetProblem.toEncodedDecisionProblem := by
  simpa [sourceProblem, sourcePresentation, targetProblem, targetPresentation] using
    ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingStructuredTMKarpReduction

/-- The source endpoint alias is exactly CR's faithful structured Knapsack problem. -/
@[simp]
theorem sourceProblem_toEncodedDecisionProblem_eq_knapsackStructuredDecisionProblem :
    sourceProblem.toEncodedDecisionProblem =
      ComplexityReduction.Combinatorics.knapsackStructuredDecisionProblem :=
  rfl

/-- The target endpoint alias is exactly CR's faithful structured Job-Sequencing problem. -/
@[simp]
theorem targetProblem_toEncodedDecisionProblem_eq_jobSequencingStructuredDecisionProblem :
    targetProblem.toEncodedDecisionProblem =
      ComplexityReduction.Combinatorics.jobSequencingStructuredDecisionProblem :=
  rfl

/--
The endpoint-local compatibility alias is CR's named structured direct-TM
record.  It is retained only for one-way comparison after the typed primitive
has been admitted from CR's direct-TM theorem below.
-/
@[simp]
theorem legacyStructuredReduction_eq_knapsackToJobSequencingStructuredTMKarpReduction :
    legacyStructuredReduction =
      ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingStructuredTMKarpReduction :=
  rfl

/-- The original structured Knapsack endpoint is already the canonical source hub. -/
abbrev originalKnapsackProblem : PresentedProblem :=
  sourceProblem

/-- The canonical structured Knapsack hub retains the complete source representation. -/
abbrev knapsackHubProblem : PresentedProblem :=
  sourceProblem

/-- The canonical structured Job-Sequencing hub is the target of the shared gadget. -/
abbrev jobSequencingHubProblem : PresentedProblem :=
  targetProblem

/-- The final structured Job-Sequencing endpoint is already the target hub. -/
abbrev finalJobSequencingProblem : PresentedProblem :=
  targetProblem

/-- The exact identity-eligible ingress endpoint into the canonical Knapsack hub. -/
abbrev KnapsackIngressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .ingress originalKnapsackProblem knapsackHubProblem

/-- The canonical request for the exact Knapsack ingress component. -/
abbrev KnapsackIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress originalKnapsackProblem knapsackHubProblem

/-- The unique Knapsack ingress request. -/
def knapsackIngressRequest : KnapsackIngressRequest :=
  .exact

/-- The ingress request fixes its exact original and canonical Knapsack endpoints. -/
theorem knapsackIngressRequest_endpoint_exact :
    knapsackIngressRequest.endpoint =
      (show KnapsackIngressEndpoint from .exact) :=
  rfl

/-- Ingress identity is eligible only because the complete endpoints coincide. -/
theorem knapsackIngress_endpoints_eq :
    originalKnapsackProblem = knapsackHubProblem :=
  rfl

/-- The exact reusable canonical shared-gadget endpoint. -/
abbrev SharedGadgetEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .sharedGadget knapsackHubProblem jobSequencingHubProblem

/-- The canonical request for the Knapsack-to-Job-Sequencing shared gadget. -/
abbrev SharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget knapsackHubProblem jobSequencingHubProblem

/-- The unique request for the standard-audited shared gadget. -/
def sharedGadgetRequest : SharedGadgetRequest :=
  .exact

/-- The shared-gadget request fixes the canonical Knapsack and Job-Sequencing hubs. -/
theorem sharedGadgetRequest_endpoint_exact :
    sharedGadgetRequest.endpoint =
      (show SharedGadgetEndpoint from .exact) :=
  rfl

/-- The exact identity-eligible egress endpoint from the Job-Sequencing hub. -/
abbrev JobSequencingEgressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .egress jobSequencingHubProblem finalJobSequencingProblem

/-- The canonical request for the exact Job-Sequencing egress component. -/
abbrev JobSequencingEgressRequest : Type 2 :=
  Protocol.ComponentRequest .egress jobSequencingHubProblem finalJobSequencingProblem

/-- The unique Job-Sequencing egress request. -/
def jobSequencingEgressRequest : JobSequencingEgressRequest :=
  .exact

/-- The egress request fixes its exact Job-Sequencing hub endpoint. -/
theorem jobSequencingEgressRequest_endpoint_exact :
    jobSequencingEgressRequest.endpoint =
      (show JobSequencingEgressEndpoint from .exact) :=
  rfl

/-- Egress identity is eligible only because the complete endpoints coincide. -/
theorem jobSequencingEgress_endpoints_eq :
    jobSequencingHubProblem = finalJobSequencingProblem :=
  rfl

/--
The sole typed primitive for this edge.  It is admitted directly from CR's
existing structured executable and standard direct-TM theorem, before any
legacy Karp facade is observed.  No cost map or route-local TM is an input to
this declaration.
-/
@[complexity_reduction_ir_typed_primitive]
noncomputable def directTMPrimitive : Primitive sourcePresentation targetPresentation :=
  Primitive.ofTMPolyTime
    ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingStructuredTMMap
    ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingStructured_tm_polytime

/-- The typed primitive runs CR's one existing structured textbook map. -/
@[simp]
theorem directTMPrimitive_run_standard (input : sourceProblem.Instance) :
    directTMPrimitive.run input =
      ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingStructuredTMMap input :=
  rfl

/-- The typed primitive carries CR's standard direct-TM witness exactly. -/
@[simp]
theorem directTMPrimitive_directTM_eq_standardDirectTM :
    directTMPrimitive.tmPolyTime =
      ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingStructured_tm_polytime :=
  rfl

/-- The primitive runs exactly the CR structured reduction executable. -/
@[simp]
theorem directTMPrimitive_run (input : sourceProblem.Instance) :
    directTMPrimitive.run input = legacyStructuredReduction.f input :=
  rfl

/-- The primitive retains precisely CR's direct-TM witness. -/
@[simp]
theorem directTMPrimitive_directTM :
    directTMPrimitive.tmPolyTime = legacyStructuredReduction.polytime :=
  Subsingleton.elim _ _

/-- The named route program is the exact direct-TM primitive atom. -/
noncomputable def program : PolyProg sourcePresentation targetPresentation :=
  .atom directTMPrimitive

/-- The named route program is exactly its direct-TM primitive atom. -/
@[simp]
theorem program_eq_atom : program = PolyProg.atom directTMPrimitive :=
  rfl

/-- The named one program executes precisely CR's structured map. -/
@[simp]
theorem program_run (input : sourceProblem.Instance) :
    program.run input = legacyStructuredReduction.f input :=
  rfl

/-- The one program executes CR's exact named structured textbook map. -/
@[simp]
theorem program_run_standard (input : sourceProblem.Instance) :
    program.run input =
      ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingStructuredTMMap input :=
  rfl

/-- CR's existing semantic theorem proves the exact typed one-program route correct. -/
theorem program_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔ targetProblem.accepts (program.run input) := by
  change ComplexityReduction.Combinatorics.Knapsack input ↔
    ComplexityReduction.Combinatorics.JobSequencing
      (ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingStructuredTMMap input)
  exact ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingStructuredTMMap_correct input

/--
The sole canonical V2 Knapsack-to-Job-Sequencing certificate.  Every
executable, semantic, direct-TM, compiler, and compatibility-cost projection
below is derived from `program`, whose atom carries CR's existing standard
direct-TM theorem.  `legacyStructuredReduction` is only the read-only
comparison point for the one-way TM-Karp facade.
-/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def certifiedReduction : CertifiedReduction sourceProblem targetProblem where
  program := program
  correct := program_correct

/-- The certificate stores the one program atom projected from the legacy executable. -/
@[simp]
theorem certifiedReduction_program :
    certifiedReduction.program =
      PolyProg.atom directTMPrimitive :=
  rfl

/-- The stored V2 program runs exactly CR's structured textbook construction. -/
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
The certificate compiler is exactly CR's named standard structured direct-TM
theorem used by its stored primitive atom.
-/
@[simp]
theorem certifiedReduction_compileTM_eq_standardDirectTM :
    certifiedReduction.program.compileTM =
      ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingStructured_tm_polytime :=
  rfl

/-- The certificate direct-TM field is compilation of the stored primitive atom. -/
@[simp]
theorem certifiedReduction_directTM_eq_primitive :
    certifiedReduction.directTM = directTMPrimitive.tmPolyTime :=
  CertifiedReduction.directTM_eq_compileTM certifiedReduction |>.trans rfl

/--
The certificate's direct-TM evidence is CR's standard structured direct-TM
theorem, not a lift from a compatibility-cost map.
-/
@[simp]
theorem certifiedReduction_directTM_eq_standardDirectTM :
    certifiedReduction.directTM =
      ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingStructured_tm_polytime :=
  certifiedReduction_directTM_eq_primitive.trans directTMPrimitive_directTM_eq_standardDirectTM

/-- The certificate's direct-TM field is exactly CR's structured route witness. -/
@[simp]
theorem certifiedReduction_directTM_eq_legacy :
    certifiedReduction.directTM = legacyStructuredReduction.polytime :=
  CertifiedReduction.directTM_eq_compileTM certifiedReduction |>.trans
    certifiedReduction_compileTM_eq_legacy

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
structured direct-TM Karp record.  This only observes the one-way adapter;
it neither builds a new machine nor upgrades a bare compatibility cost map.
-/
@[simp]
theorem certifiedReduction_tmKarpReduction_eq_legacyStructuredReduction :
    certifiedReduction.toTMKarpReduction = legacyStructuredReduction :=
  rfl

/--
The V2 certificate's TM-Karp facade is CR's named structured Knapsack-to-Job-
Sequencing edge at the same two encoded endpoints.
-/
theorem certifiedReduction_tmKarpReduction_eq_knapsackToJobSequencingStructuredTMKarpReduction :
    certifiedReduction.toTMKarpReduction =
      ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingStructuredTMKarpReduction := by
  rw [certifiedReduction_tmKarpReduction_eq_legacyStructuredReduction]
  rfl

/-- The compiler reaches the direct-TM field of CR's exact named structured Karp record. -/
@[simp]
theorem certifiedReduction_compileTM_eq_namedCRStructuredTMKarpReduction :
    certifiedReduction.program.compileTM =
      ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingStructuredTMKarpReduction.polytime :=
  Subsingleton.elim _ _

/--
The certificate's direct-TM facade is the compiler-derived field of CR's
exact named structured Karp record.
-/
@[simp]
theorem certifiedReduction_directTM_eq_namedCRStructuredTMKarpReduction :
    certifiedReduction.directTM =
      ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingStructuredTMKarpReduction.polytime :=
  CertifiedReduction.directTM_eq_compileTM certifiedReduction |>.trans
    certifiedReduction_compileTM_eq_namedCRStructuredTMKarpReduction

/--
The V2 endpoints, stored program, compiler, and named CR TM-Karp record are
one exact direct-TM route.  In particular, semantic, executable, and cost
facades cannot silently point at different route-local evidence.
-/
theorem certifiedReduction_endpointExact_namedCRStructuredTMKarpCoherence :
    sourceProblem.toEncodedDecisionProblem =
        ComplexityReduction.Combinatorics.knapsackStructuredDecisionProblem ∧
      targetProblem.toEncodedDecisionProblem =
        ComplexityReduction.Combinatorics.jobSequencingStructuredDecisionProblem ∧
      certifiedReduction.toTMKarpReduction =
        ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingStructuredTMKarpReduction ∧
      certifiedReduction.toTMKarpReduction.f = certifiedReduction.program.run ∧
      certifiedReduction.toTMKarpReduction.polytime = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM =
        ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingStructuredTMKarpReduction.polytime ∧
      certifiedReduction.program.compileTM =
        ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingStructuredTMKarpReduction.polytime := by
  exact ⟨rfl, rfl,
    certifiedReduction_tmKarpReduction_eq_knapsackToJobSequencingStructuredTMKarpReduction,
    certifiedReduction_tmKarpReduction_run_is_program,
    certifiedReduction_tmKarpReduction_directTM_is_program_compileTM,
    certifiedReduction_directTM_eq_namedCRStructuredTMKarpReduction,
    certifiedReduction_compileTM_eq_namedCRStructuredTMKarpReduction⟩

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
The direct-TM certificate is admitted only at the exact canonical
shared-gadget endpoint.  There is no whole-route primitive request or resolver:
the identity ingress and egress are endpoint facts, not replacement authority.
-/
noncomputable def knapsackToJobSequencingSharedGadgetResolution :
    Protocol.ComponentResolution .sharedGadget knapsackHubProblem jobSequencingHubProblem :=
  Protocol.ComponentResolver.accept sharedGadgetRequest certifiedReduction

/-- The canonical component path is the accepted shared gadget after identity ingress/egress. -/
noncomputable def resolveComponentPath :
    Protocol.ResolverOutcome originalKnapsackProblem finalJobSequencingProblem :=
  Protocol.ComponentResolver.resolveSingle knapsackToJobSequencingSharedGadgetResolution

/-- The shared-gadget resolution retains exactly the canonical certificate. -/
@[simp] theorem knapsackToJobSequencingSharedGadgetResolution_exact :
    knapsackToJobSequencingSharedGadgetResolution = .accepted certifiedReduction :=
  rfl

/-- The component path yields precisely the existing shared-gadget certificate. -/
@[simp] theorem resolveComponentPath_exact :
    resolveComponentPath = .accepted certifiedReduction :=
  rfl

/-- The concrete route keeps semantic, executable, TM, and cost evidence on one primitive atom. -/
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

/--
The accepted shared-gadget component, its one primitive atom, direct compiler
output, and one-way CR Karp facade all share a single standard direct-TM
source.  The legacy record is only a post-construction comparison, so it
cannot promote a bare cost map or a route-local TM into a V2 capability.
-/
theorem certifiedReduction_completeStandardDirectTMProvenance :
    knapsackToJobSequencingSharedGadgetResolution = .accepted certifiedReduction ∧
      resolveComponentPath = .accepted certifiedReduction ∧
      certifiedReduction.program = PolyProg.atom directTMPrimitive ∧
      certifiedReduction.program.run =
        ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingStructuredTMMap ∧
      directTMPrimitive.tmPolyTime =
        ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingStructured_tm_polytime ∧
      certifiedReduction.program.compileTM =
        ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingStructured_tm_polytime ∧
      certifiedReduction.directTM = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM =
        ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingStructured_tm_polytime ∧
      certifiedReduction.compatibilityCost = certifiedReduction.program.compatibilityCost ∧
      certifiedReduction.toTMKarpReduction =
        ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencingStructuredTMKarpReduction := by
  exact ⟨knapsackToJobSequencingSharedGadgetResolution_exact,
    resolveComponentPath_exact,
    certifiedReduction_program,
    funext fun input => program_run_standard input,
    directTMPrimitive_directTM_eq_standardDirectTM,
    certifiedReduction_compileTM_eq_standardDirectTM,
    CertifiedReduction.directTM_eq_compileTM certifiedReduction,
    certifiedReduction_directTM_eq_standardDirectTM,
    CertifiedReduction.compatibilityCost_eq_program_compatibilityCost certifiedReduction,
    certifiedReduction_tmKarpReduction_eq_knapsackToJobSequencingStructuredTMKarpReduction⟩

end KnapsackToJobSequencing
end Routes
end ComplexityReduction
