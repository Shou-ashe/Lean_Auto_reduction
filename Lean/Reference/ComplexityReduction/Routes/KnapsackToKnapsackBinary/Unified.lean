/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.UnaryToBinary
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.Knapsack
import ComplexityReduction.Presentation.KnapsackBinary
import ComplexityReduction.Protocol.ComponentResolver

/-!
Canonical ingress adapter from structured unary to structured binary Knapsack.

`ComplexityReduction` already supplies this representation conversion as one
structured `TMKarpReduction`.  The unary and binary presentations share their
custom carrier but have distinct encoder-bound identities, so this is not a
structural layout isomorphism.  This leaf projects the exact direct-TM
evidence into one canonical ingress-adapter certificate, retaining one
program for its executable, semantic law, compiler, and compatibility-cost
projections.
-/

namespace ComplexityReduction
namespace Routes
namespace KnapsackToKnapsackBinary

open Certificate Encoding Program

/-- The exact unary structured Knapsack presentation used by this route. -/
abbrev sourcePresentation : LawfulEncodedType :=
  Presentation.Knapsack.structuredPresentation

/-- The exact binary structured Knapsack presentation used by this route. -/
abbrev targetPresentation : LawfulEncodedType :=
  Presentation.KnapsackBinary.structuredPresentation

/-- The exact V2 unary structured Knapsack endpoint. -/
abbrev sourceProblem : PresentedProblem :=
  Presentation.Knapsack.structuredProblem

/-- The exact V2 binary structured Knapsack endpoint. -/
abbrev targetProblem : PresentedProblem :=
  Presentation.KnapsackBinary.structuredProblem

/-- The original unary numeric endpoint is the source of the canonical ingress adapter. -/
abbrev originalKnapsackProblem : PresentedProblem :=
  sourceProblem

/-- The canonical binary numeric hub retains the complete binary Knapsack representation. -/
abbrev knapsackBinaryHubProblem : PresentedProblem :=
  targetProblem

/-- The public target is the binary hub itself, so no nontrivial egress is required. -/
abbrev finalKnapsackBinaryProblem : PresentedProblem :=
  targetProblem

/-- The exact ingress endpoint of the one representation-changing adapter. -/
abbrev KnapsackUnaryToBinaryIngressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .ingress originalKnapsackProblem knapsackBinaryHubProblem

/-- The canonical request for the exact unary-to-binary Knapsack ingress adapter. -/
abbrev KnapsackUnaryToBinaryIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress originalKnapsackProblem knapsackBinaryHubProblem

/-- The unique request for the standard-audited unary-to-binary adapter. -/
def knapsackUnaryToBinaryIngressRequest : KnapsackUnaryToBinaryIngressRequest :=
  .exact

/-- The ingress request fixes the exact unary source and binary-hub endpoint. -/
theorem knapsackUnaryToBinaryIngressRequest_endpoint_exact :
    knapsackUnaryToBinaryIngressRequest.endpoint =
      (show KnapsackUnaryToBinaryIngressEndpoint from .exact) :=
  rfl

/-- The target hub is definitionally the final public endpoint. -/
theorem knapsackBinaryHub_finalTarget_endpoints_eq :
    knapsackBinaryHubProblem = finalKnapsackBinaryProblem :=
  rfl

/-- The optional binary-hub egress endpoint is identity-eligible only at these equal endpoints. -/
abbrev KnapsackBinaryHubEgressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .egress knapsackBinaryHubProblem finalKnapsackBinaryProblem

/-- The canonical request for the identity-eligible binary-hub egress. -/
abbrev KnapsackBinaryHubEgressRequest : Type 2 :=
  Protocol.ComponentRequest .egress knapsackBinaryHubProblem finalKnapsackBinaryProblem

/-- The unique exact binary-hub egress request. -/
def knapsackBinaryHubEgressRequest : KnapsackBinaryHubEgressRequest :=
  .exact

/-- The optional egress request fixes the definitionally equal binary endpoints. -/
theorem knapsackBinaryHubEgressRequest_endpoint_exact :
    knapsackBinaryHubEgressRequest.endpoint =
      (show KnapsackBinaryHubEgressEndpoint from .exact) :=
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
    ComplexityReduction.Karp21.Knapsack.knapsackStructuredToBinaryStructuredTMKarpReduction

/--
The one direct-TM primitive of the structured unary-to-binary ingress adapter.
Its executable is CR's representation-changing identity and its witness is
CR's direct theorem; the read-only Karp record is not an input to this typed
primitive and no bare compatibility-cost map participates.
-/
@[complexity_reduction_ir_typed_primitive]
noncomputable def directTMPrimitive : Primitive sourcePresentation targetPresentation :=
  Primitive.ofTMPolyTime id
    ComplexityReduction.Karp21.Knapsack.knapsackStructuredToBinary_tm_polytime

/-- The trusted adapter primitive executes exactly the existing structured conversion. -/
@[simp]
theorem directTMPrimitive_run (input : sourceProblem.Instance) :
    directTMPrimitive.run input = legacyStructuredReduction.f input :=
  rfl

/-- The primitive retains CR's standard direct-TM theorem exactly. -/
@[simp]
theorem directTMPrimitive_directTM_eq_standardDirectTM :
    directTMPrimitive.tmPolyTime =
      ComplexityReduction.Karp21.Knapsack.knapsackStructuredToBinary_tm_polytime :=
  rfl

/-- The direct primitive and read-only CR Karp record have the same fixed-endpoint witness. -/
@[simp]
theorem directTMPrimitive_directTM :
    directTMPrimitive.tmPolyTime = legacyStructuredReduction.polytime :=
  Subsingleton.elim _ _

/--
The sole route program.  The certificate below stores this one atom, so the
executable, semantic law, compiler, and compatibility-cost projections cannot
refer to parallel route-local constructions.
-/
noncomputable def program : PolyProg sourcePresentation targetPresentation :=
  .atom directTMPrimitive

/-- The sole program is precisely the atom built from the trusted adapter primitive. -/
@[simp]
theorem program_eq_atom : program = PolyProg.atom directTMPrimitive :=
  rfl

/-- The stored adapter program executes CR's representation-changing identity. -/
@[simp]
theorem program_run_eq_identity (input : sourceProblem.Instance) :
    program.run input = input :=
  rfl

/-- The representation change preserves the shared Knapsack predicate. -/
theorem program_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔ targetProblem.accepts (program.run input) := by
  change ComplexityReduction.Combinatorics.Knapsack input ↔
    ComplexityReduction.Combinatorics.Knapsack input
  rfl

/--
The canonical V2 unary-to-binary Knapsack ingress adapter certificate. Every
executable, semantic, direct-TM, compiler, and compatibility-cost fact below
comes from `program` and its one direct-TM primitive atom.  The CR Karp record
below is a read-only endpoint/evidence comparison.
-/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_ingress]
noncomputable def certifiedReduction : CertifiedReduction sourceProblem targetProblem where
  program := program
  correct := program_correct

/--
The adapter is accepted only at its exact canonical ingress component
endpoint.  This result stores the existing certificate and creates neither a
second program nor a route-local certificate.
-/
noncomputable def knapsackUnaryToBinaryIngressResolution :
    Protocol.ComponentResolution .ingress originalKnapsackProblem knapsackBinaryHubProblem :=
  Protocol.ComponentResolver.accept knapsackUnaryToBinaryIngressRequest certifiedReduction

/-- The canonical component path is the one accepted Knapsack ingress adapter. -/
noncomputable def resolveComponentPath :
    Protocol.ResolverOutcome originalKnapsackProblem finalKnapsackBinaryProblem :=
  Protocol.ComponentResolver.resolveSingle knapsackUnaryToBinaryIngressResolution

/-- The component resolver retains exactly the canonical ingress certificate. -/
@[simp] theorem knapsackUnaryToBinaryIngressResolution_exact :
    knapsackUnaryToBinaryIngressResolution = .accepted certifiedReduction :=
  rfl

/-- The component path yields precisely the existing adapter certificate. -/
@[simp] theorem resolveComponentPath_exact :
    resolveComponentPath = .accepted certifiedReduction :=
  rfl

/-- The certificate stores the one program atom projected from the trusted adapter primitive. -/
@[simp]
theorem certifiedReduction_program :
    certifiedReduction.program = PolyProg.atom directTMPrimitive :=
  rfl

/-- The adapter program records its exact unary and binary encoder identities. -/
theorem certifiedReduction_program_endpointIdentities :
    certifiedReduction.program.endpointIdentities =
      ⟨sourcePresentation.representation, targetPresentation.representation⟩ :=
  rfl

/-- The same carrier cannot erase the distinct unary and binary codec identities. -/
theorem certifiedReduction_program_endpointIdentities_ne :
    certifiedReduction.program.endpointIdentities.source ≠
      certifiedReduction.program.endpointIdentities.target := by
  simpa only [certifiedReduction_program_endpointIdentities,
    Presentation.Knapsack.structuredPresentation_representation,
    Presentation.KnapsackBinary.structuredPresentation_representation] using
    Presentation.KnapsackBinary.structuredPresentation_representation_ne_unary.symm

/-- The stored V2 program runs exactly CR's structured unary-to-binary conversion. -/
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

/-- The certificate direct-TM projection is exactly the primitive's direct-TM witness. -/
@[simp]
theorem certifiedReduction_directTM_eq_primitive :
    certifiedReduction.directTM = directTMPrimitive.tmPolyTime :=
  rfl

/-- The certificate's direct-TM projection is CR's named direct theorem. -/
theorem certifiedReduction_directTM_eq_standardDirectTM :
    certifiedReduction.directTM =
      ComplexityReduction.Karp21.Knapsack.knapsackStructuredToBinary_tm_polytime :=
  certifiedReduction_directTM_eq_primitive.trans
    directTMPrimitive_directTM_eq_standardDirectTM

/-- The certificate direct-TM projection is exactly the audited legacy witness. -/
@[simp]
theorem certifiedReduction_directTM_eq_legacy :
    certifiedReduction.directTM = legacyStructuredReduction.polytime :=
  certifiedReduction_directTM_eq_primitive.trans directTMPrimitive_directTM

/-- The direct-TM Karp facade retains the exact legacy executable. -/
@[simp]
theorem certifiedReduction_tmKarpReduction_run :
    certifiedReduction.toTMKarpReduction.f = legacyStructuredReduction.f :=
  rfl

/-- The direct-TM Karp facade retains the exact audited legacy witness. -/
@[simp]
theorem certifiedReduction_tmKarpReduction_directTM :
    certifiedReduction.toTMKarpReduction.polytime = legacyStructuredReduction.polytime :=
  Subsingleton.elim _ _

/-- Two fixed-endpoint TM Karp reductions are equal once their executables agree. -/
private theorem tmKarpReduction_eq_of_f_eq
    {A B : ComplexityReduction.EncodedDecisionProblem}
    (first second : ComplexityReduction.TMKarpReduction A B)
    (h : first.f = second.f) : first = second := by
  cases first
  cases second
  cases h
  rfl

/--
Projecting the canonical certificate back to CR recovers the exact existing
structured direct-TM Karp record.  This is the one-way certificate adapter
applied to the route's sole program, not a newly assembled machine or a
cost-only reconstruction.
-/
@[simp]
theorem certifiedReduction_tmKarpReduction_eq_legacyStructuredReduction :
    certifiedReduction.toTMKarpReduction = legacyStructuredReduction := by
  apply tmKarpReduction_eq_of_f_eq
  rw [CertifiedReduction.toTMKarpReduction_f]
  funext input
  exact certifiedReduction_run input

/-- The one-way facade is exactly CR's named structured unary-to-binary Karp record. -/
theorem certifiedReduction_tmKarpReduction_eq_knapsackStructuredToBinaryStructuredTMKarpReduction :
    certifiedReduction.toTMKarpReduction =
      ComplexityReduction.Karp21.Knapsack.knapsackStructuredToBinaryStructuredTMKarpReduction := by
  rw [certifiedReduction_tmKarpReduction_eq_legacyStructuredReduction]
  rfl

/-- The stored program compiler is precisely the named CR reduction's direct-TM field. -/
theorem certifiedReduction_compileTM_eq_knapsackStructuredToBinaryStructuredTMKarpReduction_polytime :
    certifiedReduction.program.compileTM =
      ComplexityReduction.Karp21.Knapsack.knapsackStructuredToBinaryStructuredTMKarpReduction.polytime := by
  rw [certifiedReduction_compileTM_eq_legacy]
  rfl

/-- The certificate direct-TM field is the exact named CR structured witness. -/
theorem certifiedReduction_directTM_eq_knapsackStructuredToBinaryStructuredTMKarpReduction_polytime :
    certifiedReduction.directTM =
      ComplexityReduction.Karp21.Knapsack.knapsackStructuredToBinaryStructuredTMKarpReduction.polytime := by
  rw [certifiedReduction_directTM_eq_legacy]
  rfl

/--
The certificate, its compiled program, and its CR TM-Karp projection all
refer to the same endpoint-fixed structured unary-to-binary reduction.
-/
theorem certifiedReduction_legacyStructuredTMKarpCoherence :
    certifiedReduction.toTMKarpReduction = legacyStructuredReduction ∧
      certifiedReduction.toTMKarpReduction.f = certifiedReduction.program.run ∧
      certifiedReduction.toTMKarpReduction.polytime = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM = legacyStructuredReduction.polytime ∧
      certifiedReduction.program.compileTM = legacyStructuredReduction.polytime := by
  exact ⟨certifiedReduction_tmKarpReduction_eq_legacyStructuredReduction,
    CertifiedReduction.toTMKarpReduction_f certifiedReduction, by
      rw [CertifiedReduction.toTMKarpReduction_polytime,
        CertifiedReduction.directTM_eq_compileTM],
    certifiedReduction_directTM_eq_legacy,
    certifiedReduction_compileTM_eq_legacy⟩

/--
Complete exact provenance for the canonical unary-to-binary Knapsack route.

Its representation identities, one atom program, executable, compiler proof,
direct-TM field, compatibility cost and CR facade are all projections of the
same reused structured `TMKarpReduction`.  No additional machine, cost-only
promotion, or independently assembled route evidence occurs here.
-/
theorem certifiedReduction_exactProgramCertificateProvenance :
    certifiedReduction.program.endpointIdentities =
        ⟨sourceProblem.representationIdentity, targetProblem.representationIdentity⟩ ∧
      certifiedReduction.program = PolyProg.atom directTMPrimitive ∧
      certifiedReduction.program.run =
        ComplexityReduction.Karp21.Knapsack.knapsackStructuredToBinaryStructuredTMKarpReduction.f ∧
      certifiedReduction.program.compileTM =
        ComplexityReduction.Karp21.Knapsack.knapsackStructuredToBinaryStructuredTMKarpReduction.polytime ∧
      certifiedReduction.directTM = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM = directTMPrimitive.tmPolyTime ∧
      certifiedReduction.directTM =
        ComplexityReduction.Karp21.Knapsack.knapsackStructuredToBinaryStructuredTMKarpReduction.polytime ∧
      certifiedReduction.compatibilityCost = certifiedReduction.program.compatibilityCost ∧
      certifiedReduction.toTMKarpReduction =
        ComplexityReduction.Karp21.Knapsack.knapsackStructuredToBinaryStructuredTMKarpReduction := by
  exact ⟨rfl, certifiedReduction_program, by
    funext input
    rw [← CertifiedReduction.toTMKarpReduction_f certifiedReduction,
      certifiedReduction_tmKarpReduction_eq_knapsackStructuredToBinaryStructuredTMKarpReduction],
    certifiedReduction_compileTM_eq_knapsackStructuredToBinaryStructuredTMKarpReduction_polytime,
    CertifiedReduction.directTM_eq_compileTM certifiedReduction,
    certifiedReduction_directTM_eq_primitive,
    certifiedReduction_directTM_eq_knapsackStructuredToBinaryStructuredTMKarpReduction_polytime,
    rfl,
    certifiedReduction_tmKarpReduction_eq_knapsackStructuredToBinaryStructuredTMKarpReduction⟩

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

end KnapsackToKnapsackBinary
end Routes
end ComplexityReduction
