/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.MaxCut.StructuredTM.UnaryToBinary
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.MaxCut
import ComplexityReduction.Presentation.MaxCutBinary
import ComplexityReduction.Protocol.ComponentResolver

/-!
Canonical ingress adapter from structured unary to structured binary Max-Cut.

`ComplexityReduction` already supplies the representation-changing identity
executable, its semantic law, and a direct-TM theorem.  This leaf admits that
one exact adapter into the binary Max-Cut hub.  The unary and binary
presentations share their custom carrier but have distinct encoder-bound
identities, so this is neither a structural layout isomorphism nor a
whole-route primitive.
-/

namespace ComplexityReduction
namespace Routes
namespace MaxCutToMaxCutBinary

open Certificate Encoding Program

/-- The exact unary-threshold structured Max-Cut presentation used by this adapter. -/
abbrev sourcePresentation : LawfulEncodedType :=
  Presentation.MaxCut.structuredPresentation

/-- The exact binary-threshold structured Max-Cut presentation used by this adapter. -/
abbrev targetPresentation : LawfulEncodedType :=
  Presentation.MaxCutBinary.binaryStructuredPresentation

/-- The exact V2 unary-threshold structured Max-Cut endpoint. -/
abbrev sourceProblem : PresentedProblem :=
  Presentation.MaxCut.structuredProblem

/-- The exact V2 binary-threshold structured Max-Cut endpoint. -/
abbrev targetProblem : PresentedProblem :=
  Presentation.MaxCutBinary.binaryStructuredProblem

/-- The original unary endpoint is the source of the canonical ingress adapter. -/
abbrev originalMaxCutProblem : PresentedProblem :=
  sourceProblem

/-- The canonical binary Max-Cut hub is the adapter's target. -/
abbrev maxCutBinaryHubProblem : PresentedProblem :=
  targetProblem

/-- The public target is already the binary Max-Cut hub. -/
abbrev finalMaxCutBinaryProblem : PresentedProblem :=
  targetProblem

/-- The exact ingress endpoint of the representation-changing adapter. -/
abbrev MaxCutUnaryToBinaryIngressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .ingress originalMaxCutProblem maxCutBinaryHubProblem

/-- The canonical request for the unary-to-binary Max-Cut ingress adapter. -/
abbrev MaxCutUnaryToBinaryIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress originalMaxCutProblem maxCutBinaryHubProblem

/-- The unique exact request for CR's standard direct-TM representation adapter. -/
def maxCutUnaryToBinaryIngressRequest : MaxCutUnaryToBinaryIngressRequest :=
  .exact

/-- The request fixes the source and binary-hub endpoint rather than a route-local key. -/
theorem maxCutUnaryToBinaryIngressRequest_endpoint_exact :
    maxCutUnaryToBinaryIngressRequest.endpoint =
      (show MaxCutUnaryToBinaryIngressEndpoint from .exact) :=
  rfl

/-- The binary hub is definitionally the public final endpoint. -/
theorem maxCutBinaryHub_finalTarget_endpoints_eq :
    maxCutBinaryHubProblem = finalMaxCutBinaryProblem :=
  rfl

/-- The optional egress endpoint is identity-eligible only at the equal binary endpoints. -/
abbrev MaxCutBinaryHubEgressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .egress maxCutBinaryHubProblem finalMaxCutBinaryProblem

/-- The request for the definitionally identity-eligible binary-hub egress. -/
abbrev MaxCutBinaryHubEgressRequest : Type 2 :=
  Protocol.ComponentRequest .egress maxCutBinaryHubProblem finalMaxCutBinaryProblem

/-- The unique exact request for the optional binary-hub egress. -/
def maxCutBinaryHubEgressRequest : MaxCutBinaryHubEgressRequest :=
  .exact

/--
The existing CR direct-TM Karp reduction at the exact V2 endpoints.

This read-only compatibility projection unfolds only lawful presentation
aliases; it neither rebuilds the executable nor supplies an independent cost.
-/
noncomputable def legacyStructuredReduction :
    ComplexityReduction.TMKarpReduction sourceProblem.toEncodedDecisionProblem
      targetProblem.toEncodedDecisionProblem := by
  simpa [sourceProblem, sourcePresentation, targetProblem, targetPresentation] using
    ComplexityReduction.Karp21.MaxCut.maxCutStructuredToBinaryStructuredTMKarpReduction

/--
The exact direct-TM primitive of the unary-to-binary ingress adapter.

Its executable and machine witness are CR's existing representation change;
the named Karp reduction above remains a read-only projection, never an input
to a second V2 constructor.
-/
@[complexity_reduction_ir_typed_primitive]
noncomputable def maxCutStructuredToBinaryPrimitive :
    Primitive sourcePresentation targetPresentation :=
  Primitive.ofTMPolyTime id
    ComplexityReduction.Karp21.MaxCut.maxCutStructuredToBinary_tm_polytime

/-- The typed primitive executes CR's exact representation-changing identity. -/
@[simp]
theorem maxCutStructuredToBinaryPrimitive_run (input : sourceProblem.Instance) :
    maxCutStructuredToBinaryPrimitive.run input = input :=
  rfl

/-- The primitive retains CR's direct-TM theorem exactly. -/
@[simp]
theorem maxCutStructuredToBinaryPrimitive_directTM_eq_standardDirectTM :
    maxCutStructuredToBinaryPrimitive.tmPolyTime =
      ComplexityReduction.Karp21.MaxCut.maxCutStructuredToBinary_tm_polytime :=
  rfl

/-- The ingress adapter program is precisely the direct primitive atom. -/
noncomputable def maxCutStructuredToBinaryProgram :
    PolyProg sourcePresentation targetPresentation :=
  .atom maxCutStructuredToBinaryPrimitive

/-- The adapter stores exactly one direct-TM primitive atom. -/
@[simp]
theorem maxCutStructuredToBinaryProgram_eq_atom :
    maxCutStructuredToBinaryProgram =
      PolyProg.atom maxCutStructuredToBinaryPrimitive :=
  rfl

/-- The one stored program executes the exact CR representation conversion. -/
@[simp]
theorem maxCutStructuredToBinaryProgram_run (input : sourceProblem.Instance) :
    maxCutStructuredToBinaryProgram.run input = input :=
  rfl

/-- The adapter preserves the shared Max-Cut semantic predicate. -/
theorem maxCutStructuredToBinaryProgram_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔
      targetProblem.accepts (maxCutStructuredToBinaryProgram.run input) := by
  change ComplexityReduction.Combinatorics.Graph.MaxCut input ↔
    ComplexityReduction.Combinatorics.Graph.MaxCut input
  rfl

/--
The canonical unary-to-binary Max-Cut ingress certificate.  Every executable,
semantic, compiler, direct-TM, and compatibility-cost projection below is
indexed by `maxCutStructuredToBinaryProgram`.
-/
@[complexity_reduction_ir_typed_edge]
noncomputable def certifiedReduction : CertifiedReduction sourceProblem targetProblem where
  program := maxCutStructuredToBinaryProgram
  correct := maxCutStructuredToBinaryProgram_correct

/-- The adapter is accepted only at its exact canonical ingress component endpoint. -/
noncomputable def maxCutUnaryToBinaryIngressResolution :
    Protocol.ComponentResolution .ingress originalMaxCutProblem maxCutBinaryHubProblem :=
  Protocol.ComponentResolver.accept maxCutUnaryToBinaryIngressRequest certifiedReduction

/-- The final component path is the ingress adapter because the binary hub is final. -/
noncomputable def resolveComponentPath :
    Protocol.ResolverOutcome originalMaxCutProblem finalMaxCutBinaryProblem :=
  Protocol.ComponentResolver.resolveSingle maxCutUnaryToBinaryIngressResolution

/-- The component resolver retains exactly the canonical ingress certificate. -/
@[simp] theorem maxCutUnaryToBinaryIngressResolution_exact :
    maxCutUnaryToBinaryIngressResolution = .accepted certifiedReduction :=
  rfl

/-- The component path yields precisely the accepted ingress adapter. -/
@[simp] theorem resolveComponentPath_exact :
    resolveComponentPath = .accepted certifiedReduction :=
  rfl

/-- The certificate stores the sole direct primitive atom. -/
@[simp]
theorem certifiedReduction_program :
    certifiedReduction.program = PolyProg.atom maxCutStructuredToBinaryPrimitive :=
  rfl

/-- The stored V2 program runs exactly CR's structured representation conversion. -/
@[simp]
theorem certifiedReduction_run (input : sourceProblem.Instance) :
    certifiedReduction.program.run input = legacyStructuredReduction.f input :=
  rfl

/-- The representation change is extensionally identity without erasing endpoint identities. -/
@[simp]
theorem certifiedReduction_run_eq_identity (input : sourceProblem.Instance) :
    certifiedReduction.program.run input = input :=
  rfl

/-- The route's semantic iff is indexed by the certified program's executable. -/
theorem certifiedReduction_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔ targetProblem.accepts (certifiedReduction.program.run input) :=
  certifiedReduction.correct input

/-- Direct-TM evidence is derived by compiling the certificate's stored program. -/
theorem certifiedReduction_directTM :
    ComplexityReduction.TMPolyTimeMap sourcePresentation.encodedType targetPresentation.encodedType
      certifiedReduction.program.run :=
  certifiedReduction.directTM

/-- The compiler is exactly the primitive's direct-TM witness. -/
@[simp]
theorem certifiedReduction_compileTM_eq_primitive :
    certifiedReduction.program.compileTM = maxCutStructuredToBinaryPrimitive.tmPolyTime :=
  rfl

/-- The compiler reaches CR's standard direct-TM theorem at these exact endpoints. -/
theorem certifiedReduction_compileTM_eq_standardDirectTM :
    certifiedReduction.program.compileTM =
      ComplexityReduction.Karp21.MaxCut.maxCutStructuredToBinary_tm_polytime :=
  certifiedReduction_compileTM_eq_primitive.trans
    maxCutStructuredToBinaryPrimitive_directTM_eq_standardDirectTM

/-- The direct-TM certificate field is compiler-derived. -/
@[simp]
theorem certifiedReduction_directTM_eq_compileTM :
    certifiedReduction.directTM = certifiedReduction.program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM certifiedReduction

/-- The direct-TM certificate field is CR's standard unary-to-binary witness. -/
theorem certifiedReduction_directTM_eq_standardDirectTM :
    certifiedReduction.directTM =
      ComplexityReduction.Karp21.MaxCut.maxCutStructuredToBinary_tm_polytime :=
  certifiedReduction_directTM_eq_compileTM.trans
    certifiedReduction_compileTM_eq_standardDirectTM

/-- The direct-TM Karp facade preserves the certificate's exact program executable. -/
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

/-- Two fixed-endpoint TM Karp reductions are equal when their executables agree. -/
private theorem tmKarpReduction_eq_of_f_eq
    {A B : ComplexityReduction.EncodedDecisionProblem}
    (first second : ComplexityReduction.TMKarpReduction A B)
    (h : first.f = second.f) : first = second := by
  cases first
  cases second
  cases h
  rfl

/-- The one-way certificate projection recovers the local CR reduction alias. -/
theorem certifiedReduction_tmKarpReduction_eq_legacyStructuredReduction :
    certifiedReduction.toTMKarpReduction = legacyStructuredReduction := by
  apply tmKarpReduction_eq_of_f_eq
  rw [certifiedReduction_tmKarpReduction_run_is_program]
  funext input
  exact certifiedReduction_run input

/-- The one-way certificate projection recovers CR's named structured reduction. -/
theorem certifiedReduction_tmKarpReduction_eq_maxCutStructuredToBinaryStructuredTMKarpReduction :
    certifiedReduction.toTMKarpReduction =
      ComplexityReduction.Karp21.MaxCut.maxCutStructuredToBinaryStructuredTMKarpReduction := by
  apply tmKarpReduction_eq_of_f_eq
  rw [certifiedReduction_tmKarpReduction_run_is_program]
  funext input
  exact certifiedReduction_run_eq_identity input

/-- The adapter's program retains its exact, distinct unary/binary identities. -/
theorem certifiedReduction_program_endpointIdentities :
    certifiedReduction.program.endpointIdentities =
      ⟨sourcePresentation.representation, targetPresentation.representation⟩ :=
  rfl

/-- Same carrier does not collapse the two codec-bound representation identities. -/
theorem certifiedReduction_program_endpointIdentities_ne :
    certifiedReduction.program.endpointIdentities.source ≠
      certifiedReduction.program.endpointIdentities.target := by
  simpa only [certifiedReduction_program_endpointIdentities,
    Presentation.MaxCut.structuredPresentation_representation,
    Presentation.MaxCutBinary.binaryStructuredPresentation_representation] using
    Presentation.MaxCutBinary.binaryStructuredShape_identity_ne_structuredShape_identity.symm

/-- The compatible TM-backed map is derived from program compilation, never a bare cost. -/
@[simp]
theorem certifiedReduction_tmBackedCostedMap :
    certifiedReduction.toTMBackedCostedMap = certifiedReduction.program.compile :=
  rfl

/-- The route compatibility cost is only the compiler projection of the stored program. -/
@[simp]
theorem certifiedReduction_compatibilityCost :
    certifiedReduction.compatibilityCost = certifiedReduction.program.compatibilityCost :=
  rfl

/-- The compatibility cost follows only from compiled direct-TM output-size evidence. -/
@[simp]
theorem certifiedReduction_compatibilityCost_eq_outputSizeBound :
    certifiedReduction.compatibilityCost =
      ComplexityReduction.CostedMap.of_encodedPolynomialSizeBound
        (ComplexityReduction.TMPolyTimeMap.outputSizeBound certifiedReduction.program.compileTM) :=
  certifiedReduction.program.compatibilityCost_eq_outputSizeBound

/-- The full standard direct-TM provenance is carried by the ingress adapter's one atom. -/
theorem certifiedReduction_completeStandardDirectTMProvenance :
    certifiedReduction.program = PolyProg.atom maxCutStructuredToBinaryPrimitive ∧
      certifiedReduction.program.endpointIdentities =
        ⟨sourcePresentation.representation, targetPresentation.representation⟩ ∧
      certifiedReduction.program.endpointIdentities.source ≠
        certifiedReduction.program.endpointIdentities.target ∧
      certifiedReduction.program.run = id ∧
      maxCutStructuredToBinaryPrimitive.tmPolyTime =
        ComplexityReduction.Karp21.MaxCut.maxCutStructuredToBinary_tm_polytime ∧
      certifiedReduction.program.compileTM =
        ComplexityReduction.Karp21.MaxCut.maxCutStructuredToBinary_tm_polytime ∧
      certifiedReduction.directTM = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM =
        ComplexityReduction.Karp21.MaxCut.maxCutStructuredToBinary_tm_polytime ∧
      certifiedReduction.compatibilityCost = certifiedReduction.program.compatibilityCost ∧
      certifiedReduction.toTMKarpReduction =
        ComplexityReduction.Karp21.MaxCut.maxCutStructuredToBinaryStructuredTMKarpReduction := by
  exact ⟨certifiedReduction_program,
    certifiedReduction_program_endpointIdentities,
    certifiedReduction_program_endpointIdentities_ne,
    rfl,
    maxCutStructuredToBinaryPrimitive_directTM_eq_standardDirectTM,
    certifiedReduction_compileTM_eq_standardDirectTM,
    certifiedReduction_directTM_eq_compileTM,
    certifiedReduction_directTM_eq_standardDirectTM,
    CertifiedReduction.compatibilityCost_eq_program_compatibilityCost certifiedReduction,
    certifiedReduction_tmKarpReduction_eq_maxCutStructuredToBinaryStructuredTMKarpReduction⟩

/-- The ingress certificate is the only final component because the binary hub is final. -/
theorem canonicalIngressAdapter_oneProgramChain :
    maxCutUnaryToBinaryIngressResolution = .accepted certifiedReduction ∧
      (∀ input,
        sourceProblem.accepts input ↔ targetProblem.accepts (certifiedReduction.program.run input)) ∧
      certifiedReduction.program = PolyProg.atom maxCutStructuredToBinaryPrimitive ∧
      certifiedReduction.directTM = certifiedReduction.program.compileTM ∧
      certifiedReduction.compatibilityCost = certifiedReduction.program.compatibilityCost :=
  ⟨maxCutUnaryToBinaryIngressResolution_exact, certifiedReduction.correct,
    certifiedReduction_program, certifiedReduction_directTM_eq_compileTM,
    CertifiedReduction.compatibilityCost_eq_program_compatibilityCost certifiedReduction⟩

end MaxCutToMaxCutBinary
end Routes
end ComplexityReduction
