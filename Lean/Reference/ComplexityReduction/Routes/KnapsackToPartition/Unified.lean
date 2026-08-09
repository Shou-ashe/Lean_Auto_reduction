/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.Part3
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.Knapsack
import ComplexityReduction.Presentation.Partition
import ComplexityReduction.Protocol.ComponentResolver

/-!
The canonical structured Knapsack-to-Partition V2 route.

`ComplexityReduction` already provides the textbook balancing construction as
one standard-axiom audited structured `TMKarpReduction`.  This leaf projects
that direct-TM evidence into a V2 `CertifiedReduction`; its executable,
semantic iff, compiler, and compatibility cost remain indexed by the one
stored `PolyProg`.
-/

namespace ComplexityReduction
namespace Routes
namespace KnapsackToPartition

open Certificate Encoding Program

/-- The exact faithful structured Knapsack presentation used by this route. -/
abbrev sourcePresentation : LawfulEncodedType :=
  Presentation.Knapsack.structuredPresentation

/-- The exact faithful structured Partition presentation used by this route. -/
abbrev targetPresentation : LawfulEncodedType :=
  Presentation.Partition.structuredPresentation

/-- The exact V2 structured Knapsack endpoint. -/
abbrev sourceProblem : PresentedProblem :=
  Presentation.Knapsack.structuredProblem

/-- The exact V2 structured Partition endpoint. -/
abbrev targetProblem : PresentedProblem :=
  Presentation.Partition.structuredProblem

/-- The original structured Knapsack endpoint is already the canonical source hub. -/
abbrev originalKnapsackProblem : PresentedProblem :=
  sourceProblem

/-- The canonical structured Knapsack hub retains the complete source representation. -/
abbrev knapsackHubProblem : PresentedProblem :=
  sourceProblem

/-- The canonical structured Partition hub is the target of the balancing gadget. -/
abbrev partitionHubProblem : PresentedProblem :=
  targetProblem

/-- The public structured Partition endpoint is already the target hub. -/
abbrev finalPartitionProblem : PresentedProblem :=
  targetProblem

/-- The exact identity-eligible ingress endpoint into the canonical Knapsack hub. -/
abbrev KnapsackIngressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .ingress originalKnapsackProblem knapsackHubProblem

/-- The exact request for the identity-eligible Knapsack ingress endpoint. -/
abbrev KnapsackIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress originalKnapsackProblem knapsackHubProblem

/-- The unique exact Knapsack ingress request. -/
def knapsackIngressRequest : KnapsackIngressRequest :=
  .exact

/-- The ingress is identity-eligible only because its complete endpoints coincide. -/
theorem knapsackIngress_endpoints_eq :
    originalKnapsackProblem = knapsackHubProblem :=
  rfl

/-- The exact reusable canonical shared-gadget endpoint. -/
abbrev SharedGadgetEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .sharedGadget knapsackHubProblem partitionHubProblem

/-- The exact request for the Knapsack-to-Partition balancing gadget. -/
abbrev SharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget knapsackHubProblem partitionHubProblem

/-- The unique exact shared-gadget request. -/
def sharedGadgetRequest : SharedGadgetRequest :=
  .exact

/-- The exact identity-eligible egress endpoint from the Partition hub. -/
abbrev PartitionEgressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .egress partitionHubProblem finalPartitionProblem

/-- The exact request for the identity-eligible Partition egress endpoint. -/
abbrev PartitionEgressRequest : Type 2 :=
  Protocol.ComponentRequest .egress partitionHubProblem finalPartitionProblem

/-- The unique exact Partition egress request. -/
def partitionEgressRequest : PartitionEgressRequest :=
  .exact

/-- The egress is identity-eligible only because its complete endpoints coincide. -/
theorem partitionEgress_endpoints_eq :
    partitionHubProblem = finalPartitionProblem :=
  rfl

/-- The ingress request fixes its exact original and canonical Knapsack endpoints. -/
theorem knapsackIngressRequest_endpoint_exact :
    knapsackIngressRequest.endpoint =
      (show KnapsackIngressEndpoint from .exact) :=
  rfl

/-- The shared-gadget request fixes exactly the canonical Knapsack and Partition hubs. -/
theorem sharedGadgetRequest_endpoint_exact :
    sharedGadgetRequest.endpoint =
      (show SharedGadgetEndpoint from .exact) :=
  rfl

/-- The egress request fixes its exact Partition hub endpoint. -/
theorem partitionEgressRequest_endpoint_exact :
    partitionEgressRequest.endpoint =
      (show PartitionEgressEndpoint from .exact) :=
  rfl

/--
The existing direct-TM Karp reduction at exactly the two V2 endpoints.

The simplification unfolds only the faithful endpoint aliases; it neither
reconstructs the balancing machine nor accepts a bare legacy cost map.
-/
noncomputable def legacyStructuredReduction :
    ComplexityReduction.TMKarpReduction sourceProblem.toEncodedDecisionProblem
      targetProblem.toEncodedDecisionProblem := by
  simpa [sourceProblem, sourcePresentation, targetProblem, targetPresentation] using
    ComplexityReduction.Karp21.Partition.knapsackToPartitionStructuredTMKarpReduction

/-- The source endpoint alias is exactly CR's faithful structured Knapsack problem. -/
@[simp]
theorem sourceProblem_toEncodedDecisionProblem_eq_knapsackStructuredDecisionProblem :
    sourceProblem.toEncodedDecisionProblem =
      ComplexityReduction.Combinatorics.knapsackStructuredDecisionProblem :=
  rfl

/-- The target endpoint alias is exactly CR's faithful structured Partition problem. -/
@[simp]
theorem targetProblem_toEncodedDecisionProblem_eq_partitionStructuredDecisionProblem :
    targetProblem.toEncodedDecisionProblem =
      ComplexityReduction.Combinatorics.partitionStructuredDecisionProblem :=
  rfl

/--
The endpoint-local legacy alias is precisely CR's named structured direct-TM
record.  This observes the imported evidence only; it does not rebuild a TM
or derive one from a bare cost map.
-/
@[simp]
theorem legacyStructuredReduction_eq_knapsackToPartitionStructuredTMKarpReduction :
    legacyStructuredReduction =
      ComplexityReduction.Karp21.Partition.knapsackToPartitionStructuredTMKarpReduction :=
  rfl

/--
The single direct-TM primitive used by the typed route.

Its executable is CR's textbook balancing map and its evidence is CR's
standard structured direct-TM theorem.  In particular the legacy
`TMKarpReduction` below is only a read-only comparison target: this primitive
is not constructed from a cost map or a route-local machine.
-/
@[complexity_reduction_ir_typed_primitive]
noncomputable def directTMPrimitive : Primitive sourcePresentation targetPresentation :=
  Primitive.ofTMPolyTime ComplexityReduction.Karp21.Partition.textbookMap
    ComplexityReduction.Karp21.Partition.knapsackToPartitionStructured_tm_polytime

/-- The direct primitive executes CR's existing textbook balancing map. -/
@[simp]
theorem directTMPrimitive_run (input : sourceProblem.Instance) :
    directTMPrimitive.run input = ComplexityReduction.Karp21.Partition.textbookMap input :=
  rfl

/-- The direct primitive carries CR's standard direct-TM witness exactly. -/
@[simp]
theorem directTMPrimitive_directTM :
    directTMPrimitive.tmPolyTime =
      ComplexityReduction.Karp21.Partition.knapsackToPartitionStructured_tm_polytime :=
  rfl

/-- The route has one actual program: the atom of its direct-TM primitive. -/
noncomputable def program : PolyProg sourcePresentation targetPresentation :=
  .atom directTMPrimitive

/-- The named route program is exactly that one primitive atom. -/
@[simp]
theorem program_eq_atom : program = PolyProg.atom directTMPrimitive :=
  rfl

/-- The stored program runs CR's textbook balancing map. -/
@[simp]
theorem program_run (input : sourceProblem.Instance) :
    program.run input = ComplexityReduction.Karp21.Partition.textbookMap input :=
  rfl

/-- CR's existing semantic theorem proves the exact typed program correct. -/
theorem program_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔ targetProblem.accepts (program.run input) := by
  change ComplexityReduction.Combinatorics.Knapsack input ↔
    ComplexityReduction.Combinatorics.Partition
      (ComplexityReduction.Karp21.Partition.textbookMap input)
  exact ComplexityReduction.Karp21.Partition.textbookMap_correct input

/-
The sole canonical V2 Knapsack-to-Partition certificate.  Every executable,
semantic, direct-TM, compiler, and compatibility-cost projection below is
derived from `program`, whose atom carries CR's standard direct-TM theorem.
`legacyStructuredReduction` is retained solely as a read-only comparison of
the certificate's compatibility projection with the existing CR route.
-/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def certifiedReduction : CertifiedReduction sourceProblem targetProblem where
  program := program
  correct := program_correct

/-- The balancing construction is accepted only at its exact shared-gadget endpoint. -/
noncomputable def knapsackToPartitionSharedGadgetResolution :
    Protocol.ComponentResolution .sharedGadget knapsackHubProblem partitionHubProblem :=
  Protocol.ComponentResolver.accept sharedGadgetRequest certifiedReduction

/-- The final component path is this shared gadget because both outer endpoints are hubs. -/
noncomputable def resolveComponentPath :
    Protocol.ResolverOutcome originalKnapsackProblem finalPartitionProblem :=
  Protocol.ComponentResolver.resolveSingle knapsackToPartitionSharedGadgetResolution

/-- The shared-gadget resolver retains exactly the canonical certificate. -/
@[simp] theorem knapsackToPartitionSharedGadgetResolution_exact :
    knapsackToPartitionSharedGadgetResolution = .accepted certifiedReduction :=
  rfl

/-- The component path yields precisely the accepted shared-gadget certificate. -/
@[simp] theorem resolveComponentPath_exact :
    resolveComponentPath = .accepted certifiedReduction :=
  rfl

/-- The certificate stores the one standard direct-TM primitive atom. -/
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

/-
The program compiler retains exactly CR's standard direct-TM theorem used to
construct `directTMPrimitive`.
-/
@[simp]
theorem certifiedReduction_compileTM_eq_standardDirectTM :
    certifiedReduction.program.compileTM =
      ComplexityReduction.Karp21.Partition.knapsackToPartitionStructured_tm_polytime :=
  rfl

/-- The program compiler has the same direct-TM witness as CR's existing route. -/
@[simp]
theorem certifiedReduction_compileTM_eq_legacy :
    certifiedReduction.program.compileTM = legacyStructuredReduction.polytime :=
  Subsingleton.elim _ _

/-- The certificate direct-TM field is the compiler output of its actual program. -/
@[simp]
theorem certifiedReduction_directTM_eq_primitive :
    certifiedReduction.directTM = directTMPrimitive.tmPolyTime :=
  CertifiedReduction.directTM_eq_compileTM certifiedReduction |>.trans rfl

/--
The certificate's program-derived direct-TM projection is CR's standard
structured theorem used by the stored primitive atom.
-/
@[simp]
theorem certifiedReduction_directTM_eq_standardDirectTM :
    certifiedReduction.directTM =
      ComplexityReduction.Karp21.Partition.knapsackToPartitionStructured_tm_polytime :=
  certifiedReduction_directTM_eq_primitive.trans directTMPrimitive_directTM

/--
The certified direct-TM field is precisely CR's standard structured witness,
not a cost-only lift.
-/
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
Projecting the canonical certificate back to CR recovers exactly the
endpoint-local direct-TM record.  This is a one-way certificate projection,
not a construction of a new machine or a cost-only lift.
-/
@[simp]
theorem certifiedReduction_tmKarpReduction_eq_legacyStructuredReduction :
    certifiedReduction.toTMKarpReduction = legacyStructuredReduction :=
  rfl

/--
The certificate facade is precisely CR's named Knapsack-to-Partition
structured direct-TM reduction at its two faithful endpoints.
-/
theorem certifiedReduction_tmKarpReduction_eq_knapsackToPartitionStructuredTMKarpReduction :
    certifiedReduction.toTMKarpReduction =
      ComplexityReduction.Karp21.Partition.knapsackToPartitionStructuredTMKarpReduction := by
  rw [certifiedReduction_tmKarpReduction_eq_legacyStructuredReduction]
  exact legacyStructuredReduction_eq_knapsackToPartitionStructuredTMKarpReduction

/-- The stored program compiler is exactly CR's named structured direct-TM witness. -/
theorem certifiedReduction_compileTM_eq_knapsackToPartitionStructuredTMKarpReduction_polytime :
    certifiedReduction.program.compileTM =
      ComplexityReduction.Karp21.Partition.knapsackToPartitionStructuredTMKarpReduction.polytime := by
  rw [certifiedReduction_compileTM_eq_legacy]
  rfl

/-- The certificate direct-TM field is exactly the same named CR structured witness. -/
theorem certifiedReduction_directTM_eq_knapsackToPartitionStructuredTMKarpReduction_polytime :
    certifiedReduction.directTM =
      ComplexityReduction.Karp21.Partition.knapsackToPartitionStructuredTMKarpReduction.polytime :=
  certifiedReduction_directTM_eq_standardDirectTM.trans (by rfl)

/--
The endpoint aliases, stored executable, compiler, direct-TM field, and named
CR TM-Karp facade are one exact route.  In particular no semantic, cost, or
machine projection can silently refer to a parallel route-local construction.
-/
theorem certifiedReduction_endpointExact_namedCRStructuredTMKarpCoherence :
    sourceProblem.toEncodedDecisionProblem =
        ComplexityReduction.Combinatorics.knapsackStructuredDecisionProblem ∧
      targetProblem.toEncodedDecisionProblem =
        ComplexityReduction.Combinatorics.partitionStructuredDecisionProblem ∧
      certifiedReduction.toTMKarpReduction =
        ComplexityReduction.Karp21.Partition.knapsackToPartitionStructuredTMKarpReduction ∧
      certifiedReduction.toTMKarpReduction.f = certifiedReduction.program.run ∧
      certifiedReduction.toTMKarpReduction.polytime = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM =
        ComplexityReduction.Karp21.Partition.knapsackToPartitionStructuredTMKarpReduction.polytime ∧
      certifiedReduction.program.compileTM =
        ComplexityReduction.Karp21.Partition.knapsackToPartitionStructuredTMKarpReduction.polytime := by
  exact ⟨sourceProblem_toEncodedDecisionProblem_eq_knapsackStructuredDecisionProblem,
    targetProblem_toEncodedDecisionProblem_eq_partitionStructuredDecisionProblem,
    certifiedReduction_tmKarpReduction_eq_knapsackToPartitionStructuredTMKarpReduction,
    certifiedReduction_tmKarpReduction_run_is_program,
    certifiedReduction_tmKarpReduction_directTM_is_program_compileTM,
    certifiedReduction_directTM_eq_knapsackToPartitionStructuredTMKarpReduction_polytime,
    certifiedReduction_compileTM_eq_knapsackToPartitionStructuredTMKarpReduction_polytime⟩

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

/-- The compatibility cost follows only from the output-size theorem of the compiled direct TM. -/
@[simp]
theorem certifiedReduction_compatibilityCost_eq_outputSizeBound :
    certifiedReduction.compatibilityCost =
      ComplexityReduction.CostedMap.of_encodedPolynomialSizeBound
        (ComplexityReduction.TMPolyTimeMap.outputSizeBound certifiedReduction.program.compileTM) :=
  certifiedReduction.program.compatibilityCost_eq_outputSizeBound

end KnapsackToPartition
end Routes
end ComplexityReduction
