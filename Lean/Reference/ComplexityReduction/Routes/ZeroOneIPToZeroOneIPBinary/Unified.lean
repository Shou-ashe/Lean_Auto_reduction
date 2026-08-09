/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ZeroOneIP.StructuredTM.UnaryToBinary
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Reduction
import ComplexityReduction.Presentation.ZeroOneIP
import ComplexityReduction.Presentation.ZeroOneIPBinary
import ComplexityReduction.Protocol.ComponentResolver

/-!
Canonical component adapter from structured unary to structured binary 0-1-IP.

`ComplexityReduction` already supplies the identity executable, semantic law,
and direct-TM theorem for this representation-changing conversion.  The
unary and binary presentations have the same custom carrier but different
encoder-bound identities, so this is not a structural layout isomorphism.
It is one exact ingress adapter into the canonical binary numeric hub, not a
whole-route primitive.  Its program, certificate, and direct-TM projection
all share that one adapter construction.
-/

namespace ComplexityReduction
namespace Routes
namespace ZeroOneIPToZeroOneIPBinary

open Certificate Encoding Program

/-- The exact unary structured 0-1-IP presentation used by this route. -/
abbrev sourcePresentation : LawfulEncodedType :=
  Presentation.ZeroOneIP.structuredPresentation

/-- The exact binary structured 0-1-IP presentation used by this route. -/
abbrev targetPresentation : LawfulEncodedType :=
  Presentation.ZeroOneIPBinary.binaryStructuredPresentation

/-- The exact V2 unary structured 0-1-IP endpoint. -/
abbrev sourceProblem : PresentedProblem :=
  Presentation.ZeroOneIP.structuredProblem

/-- The exact V2 binary structured 0-1-IP endpoint. -/
abbrev targetProblem : PresentedProblem :=
  Presentation.ZeroOneIPBinary.binaryStructuredProblem

/-- The original unary numeric endpoint is the source of the canonical ingress adapter. -/
abbrev originalZeroOneIPProblem : PresentedProblem :=
  sourceProblem

/-- The canonical binary numeric hub retains the complete binary 0-1-IP presentation. -/
abbrev zeroOneIPBinaryHubProblem : PresentedProblem :=
  targetProblem

/-- The public target is the binary hub itself, so no nontrivial egress is required. -/
abbrev finalZeroOneIPBinaryProblem : PresentedProblem :=
  targetProblem

/-- The exact ingress endpoint of the one representation-changing adapter. -/
abbrev UnaryToBinaryIngressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .ingress originalZeroOneIPProblem zeroOneIPBinaryHubProblem

/-- The canonical request for the exact unary-to-binary ingress adapter. -/
abbrev UnaryToBinaryIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress originalZeroOneIPProblem zeroOneIPBinaryHubProblem

/-- The unique request for the standard-audited unary-to-binary adapter. -/
def unaryToBinaryIngressRequest : UnaryToBinaryIngressRequest :=
  .exact

/-- The ingress request fixes the representation-changing adapter's exact endpoint. -/
theorem unaryToBinaryIngressRequest_endpoint_exact :
    unaryToBinaryIngressRequest.endpoint =
      (show UnaryToBinaryIngressEndpoint from .exact) :=
  rfl

/-- The target hub is definitionally the final public endpoint. -/
theorem binaryHub_finalTarget_endpoints_eq :
    zeroOneIPBinaryHubProblem = finalZeroOneIPBinaryProblem :=
  rfl

/-- The exact optional egress endpoint is identity-eligible only at those equal endpoints. -/
abbrev BinaryHubEgressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .egress zeroOneIPBinaryHubProblem finalZeroOneIPBinaryProblem

/-- The canonical request for the identity-eligible binary-hub egress. -/
abbrev BinaryHubEgressRequest : Type 2 :=
  Protocol.ComponentRequest .egress zeroOneIPBinaryHubProblem finalZeroOneIPBinaryProblem

/-- The unique exact binary-hub egress request. -/
def binaryHubEgressRequest : BinaryHubEgressRequest :=
  .exact

/--
The existing direct-TM Karp reduction at exactly the two V2 endpoints.

The simplification unfolds only the lawful presentation aliases; it does not
re-encode inputs, rebuild a machine, or promote a bare compatibility cost.
-/
noncomputable def legacyStructuredReduction :
    ComplexityReduction.TMKarpReduction sourceProblem.toEncodedDecisionProblem
      targetProblem.toEncodedDecisionProblem := by
  simpa [sourceProblem, sourcePresentation, targetProblem, targetPresentation] using
    ComplexityReduction.Karp21.ZeroOneIP.zeroOneIPStructuredToBinaryStructuredTMKarpReduction

/-- The source endpoint alias is exactly CR's unary structured 0-1-IP problem. -/
@[simp]
theorem sourceProblem_toEncodedDecisionProblem_eq_zeroOneIntegerProgrammingStructuredDecisionProblem :
    sourceProblem.toEncodedDecisionProblem =
      ComplexityReduction.Combinatorics.zeroOneIntegerProgrammingStructuredDecisionProblem :=
  rfl

/-- The target endpoint alias is exactly CR's binary structured 0-1-IP problem. -/
@[simp]
theorem targetProblem_toEncodedDecisionProblem_eq_zeroOneIntegerProgrammingBinaryStructuredDecisionProblem :
    targetProblem.toEncodedDecisionProblem =
      ComplexityReduction.Combinatorics.zeroOneIntegerProgrammingBinaryStructuredDecisionProblem :=
  rfl

/--
The endpoint-local Karp alias is CR's one named structured bridge record. It
is used only as a read-only comparison after the typed direct-TM primitive is
constructed from CR's actual direct-TM theorem.
-/
@[simp]
theorem legacyStructuredReduction_eq_zeroOneIPStructuredToBinaryStructuredTMKarpReduction :
    legacyStructuredReduction =
      ComplexityReduction.Karp21.ZeroOneIP.zeroOneIPStructuredToBinaryStructuredTMKarpReduction :=
  rfl

/--
The exact standard-audited primitive of the unary-to-binary ingress adapter.
It uses CR's identity executable and direct-TM theorem directly; the legacy
Karp reduction is only a read-only comparison.
-/
@[complexity_reduction_ir_typed_primitive]
noncomputable def zeroOneIPStructuredToBinaryPrimitive :
    Primitive sourcePresentation targetPresentation :=
  Primitive.ofTMPolyTime id
    ComplexityReduction.Karp21.ZeroOneIP.integerProgrammingStructuredToBinary_tm_polytime

/-- The direct primitive executes CR's exact identity conversion. -/
@[simp]
theorem zeroOneIPStructuredToBinaryPrimitive_run (input : sourceProblem.Instance) :
    zeroOneIPStructuredToBinaryPrimitive.run input = input :=
  rfl

/-- The typed primitive retains CR's standard unary-to-binary direct-TM theorem exactly. -/
@[simp]
theorem zeroOneIPStructuredToBinaryPrimitive_directTM_eq_standardDirectTM :
    zeroOneIPStructuredToBinaryPrimitive.tmPolyTime =
      ComplexityReduction.Karp21.ZeroOneIP.integerProgrammingStructuredToBinary_tm_polytime :=
  rfl

/-- The ingress adapter program is precisely the direct primitive atom. -/
noncomputable def zeroOneIPStructuredToBinaryProgram :
    PolyProg sourcePresentation targetPresentation :=
  .atom zeroOneIPStructuredToBinaryPrimitive

/-- The ingress adapter stores exactly one direct-TM primitive atom. -/
@[simp]
theorem zeroOneIPStructuredToBinaryProgram_eq_atom :
    zeroOneIPStructuredToBinaryProgram =
      PolyProg.atom zeroOneIPStructuredToBinaryPrimitive :=
  rfl

/-- The one stored program executes CR's exact identity conversion. -/
@[simp]
theorem zeroOneIPStructuredToBinaryProgram_run (input : sourceProblem.Instance) :
    zeroOneIPStructuredToBinaryProgram.run input = input :=
  rfl

/-- The representation change preserves the one shared 0-1-IP predicate. -/
theorem zeroOneIPStructuredToBinaryProgram_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔
      targetProblem.accepts (zeroOneIPStructuredToBinaryProgram.run input) := by
  change ComplexityReduction.Combinatorics.ZeroOneIntegerProgramming input ↔
    ComplexityReduction.Combinatorics.ZeroOneIntegerProgramming input
  rfl

/--
The canonical V2 unary-to-binary ingress adapter certificate. Every
executable, semantic, direct-TM, compiler, and compatibility-cost projection
below comes from `zeroOneIPStructuredToBinaryProgram`; the legacy reduction
is only a read-only endpoint/evidence comparison.
-/
@[complexity_reduction_ir_typed_edge]
noncomputable def certifiedReduction : CertifiedReduction sourceProblem targetProblem where
  program := zeroOneIPStructuredToBinaryProgram
  correct := zeroOneIPStructuredToBinaryProgram_correct

/--
The adapter is accepted only at its exact canonical ingress component
endpoint.  This result stores the existing certificate and creates neither a
second program nor a route-local certificate.
-/
noncomputable def unaryToBinaryIngressResolution :
    Protocol.ComponentResolution .ingress originalZeroOneIPProblem zeroOneIPBinaryHubProblem :=
  Protocol.ComponentResolver.accept unaryToBinaryIngressRequest certifiedReduction

/-- The canonical component path is the one accepted ingress adapter. -/
noncomputable def resolveComponentPath :
    Protocol.ResolverOutcome originalZeroOneIPProblem finalZeroOneIPBinaryProblem :=
  Protocol.ComponentResolver.resolveSingle unaryToBinaryIngressResolution

/-- The component resolver retains exactly the canonical ingress certificate. -/
@[simp] theorem unaryToBinaryIngressResolution_exact :
    unaryToBinaryIngressResolution = .accepted certifiedReduction :=
  rfl

/-- The component path yields precisely the existing adapter certificate. -/
@[simp] theorem resolveComponentPath_exact :
    resolveComponentPath = .accepted certifiedReduction :=
  rfl

/-- The certificate stores the sole direct primitive atom. -/
@[simp]
theorem certifiedReduction_program :
    certifiedReduction.program =
      PolyProg.atom
        zeroOneIPStructuredToBinaryPrimitive :=
  rfl

/-- The typed identity program exposes the exact selected unary/binary representation pair. -/
theorem certifiedReduction_program_endpointIdentities :
    certifiedReduction.program.endpointIdentities =
      ⟨sourcePresentation.representation, targetPresentation.representation⟩ :=
  rfl

/--
Although the executable is extensionally `id`, its source and target codec
identities remain distinct; a shared carrier cannot erase this boundary.
-/
theorem certifiedReduction_program_endpointIdentities_ne :
    certifiedReduction.program.endpointIdentities.source ≠
      certifiedReduction.program.endpointIdentities.target := by
  simpa only [certifiedReduction_program_endpointIdentities,
    Presentation.ZeroOneIP.structuredPresentation_representation,
    Presentation.ZeroOneIPBinary.binaryStructuredPresentation_representation] using
    Presentation.ZeroOneIPBinary.binaryStructuredPresentation_representation_ne_structuredPresentation.symm

/-- The stored V2 program runs exactly CR's structured representation conversion. -/
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

/-- The compiler is exactly the direct-TM witness stored by the primitive atom. -/
@[simp]
theorem certifiedReduction_compileTM_eq_primitive :
    certifiedReduction.program.compileTM =
      zeroOneIPStructuredToBinaryPrimitive.tmPolyTime :=
  rfl

/-- The compiler output is exactly CR's standard unary-to-binary direct-TM theorem. -/
@[simp]
theorem certifiedReduction_compileTM_eq_standardDirectTM :
    certifiedReduction.program.compileTM =
      ComplexityReduction.Karp21.ZeroOneIP.integerProgrammingStructuredToBinary_tm_polytime :=
  certifiedReduction_compileTM_eq_primitive.trans
    zeroOneIPStructuredToBinaryPrimitive_directTM_eq_standardDirectTM

/-- The certificate's direct-TM projection is the compiler output of its one atom. -/
@[simp]
theorem certifiedReduction_directTM_eq_primitive :
    certifiedReduction.directTM = zeroOneIPStructuredToBinaryPrimitive.tmPolyTime :=
  CertifiedReduction.directTM_eq_compileTM certifiedReduction |>.trans
    certifiedReduction_compileTM_eq_primitive

/-- The certificate direct-TM field is CR's standard direct-TM theorem through program compilation. -/
@[simp]
theorem certifiedReduction_directTM_eq_standardDirectTM :
    certifiedReduction.directTM =
      ComplexityReduction.Karp21.ZeroOneIP.integerProgrammingStructuredToBinary_tm_polytime :=
  certifiedReduction_directTM_eq_primitive.trans
    zeroOneIPStructuredToBinaryPrimitive_directTM_eq_standardDirectTM

/-- The certificate's direct-TM projection is CR's existing structured bridge witness. -/
@[simp]
theorem certifiedReduction_directTM_eq_legacy :
    certifiedReduction.directTM = legacyStructuredReduction.polytime :=
  CertifiedReduction.directTM_eq_compileTM certifiedReduction |>.trans
    certifiedReduction_compileTM_eq_legacy

/-- The primitive itself retains the direct-TM witness of CR's named bridge record. -/
@[simp]
theorem zeroOneIPStructuredToBinaryPrimitive_directTM_eq_legacy :
    zeroOneIPStructuredToBinaryPrimitive.tmPolyTime = legacyStructuredReduction.polytime :=
  certifiedReduction_directTM_eq_primitive.symm.trans certifiedReduction_directTM_eq_legacy

/-- The TM-Karp facade preserves the executable of the certificate's one program. -/
@[simp]
theorem certifiedReduction_tmKarpReduction_run_is_program :
    certifiedReduction.toTMKarpReduction.f = certifiedReduction.program.run :=
  CertifiedReduction.toTMKarpReduction_f certifiedReduction

/-- The TM-Karp facade derives direct-TM evidence by compiling that same program. -/
@[simp]
theorem certifiedReduction_tmKarpReduction_directTM_is_program_compileTM :
    certifiedReduction.toTMKarpReduction.polytime = certifiedReduction.program.compileTM := by
  rw [CertifiedReduction.toTMKarpReduction_polytime,
    CertifiedReduction.directTM_eq_compileTM]

/-- At fixed endpoints, a CR TM-Karp record is determined by its executable. -/
private theorem tmKarpReduction_eq_of_f_eq
    {A B : ComplexityReduction.EncodedDecisionProblem}
    (first second : ComplexityReduction.TMKarpReduction A B)
    (h : first.f = second.f) : first = second := by
  cases first
  cases second
  cases h
  rfl

/-- The one-way typed projection recovers CR's existing structured bridge record. -/
@[simp]
theorem certifiedReduction_tmKarpReduction_eq_legacyStructuredReduction :
    certifiedReduction.toTMKarpReduction = legacyStructuredReduction := by
  apply tmKarpReduction_eq_of_f_eq
  rw [certifiedReduction_tmKarpReduction_run_is_program]
  funext input
  exact certifiedReduction_run input

/-- The projected facade is CR's named unary-to-binary structured 0-1-IP record. -/
@[simp]
theorem certifiedReduction_tmKarpReduction_eq_zeroOneIPStructuredToBinaryStructuredTMKarpReduction :
    certifiedReduction.toTMKarpReduction =
      ComplexityReduction.Karp21.ZeroOneIP.zeroOneIPStructuredToBinaryStructuredTMKarpReduction := by
  rw [certifiedReduction_tmKarpReduction_eq_legacyStructuredReduction]
  rfl

/-- The compiler reaches the exact direct-TM field of CR's named bridge record. -/
@[simp]
theorem certifiedReduction_compileTM_eq_namedCRStructuredTMKarpReduction :
    certifiedReduction.program.compileTM =
      ComplexityReduction.Karp21.ZeroOneIP.zeroOneIPStructuredToBinaryStructuredTMKarpReduction.polytime :=
  Subsingleton.elim _ _

/-- The certificate direct-TM facade is compiler-derived and has the same named CR provenance. -/
@[simp]
theorem certifiedReduction_directTM_eq_namedCRStructuredTMKarpReduction :
    certifiedReduction.directTM =
      ComplexityReduction.Karp21.ZeroOneIP.zeroOneIPStructuredToBinaryStructuredTMKarpReduction.polytime :=
  CertifiedReduction.directTM_eq_compileTM certifiedReduction |>.trans
    certifiedReduction_compileTM_eq_namedCRStructuredTMKarpReduction

/-- The direct primitive's standard witness is the exact direct-TM field of CR's named bridge. -/
@[simp]
theorem zeroOneIPStructuredToBinaryPrimitive_directTM_eq_namedCRStructuredTMKarpReduction :
    zeroOneIPStructuredToBinaryPrimitive.tmPolyTime =
      ComplexityReduction.Karp21.ZeroOneIP.zeroOneIPStructuredToBinaryStructuredTMKarpReduction.polytime :=
  Subsingleton.elim _ _

/--
The exact endpoints, one stored program, compiler, primitive, and named CR
TM-Karp bridge are one route.  This is a read-only comparison of the typed
certificate projection with CR evidence; no second TM or cost construction is
introduced.
-/
theorem certifiedReduction_endpointExact_namedCRStructuredTMKarpCoherence :
    sourceProblem.toEncodedDecisionProblem =
        ComplexityReduction.Combinatorics.zeroOneIntegerProgrammingStructuredDecisionProblem ∧
      targetProblem.toEncodedDecisionProblem =
        ComplexityReduction.Combinatorics.zeroOneIntegerProgrammingBinaryStructuredDecisionProblem ∧
      certifiedReduction.toTMKarpReduction =
        ComplexityReduction.Karp21.ZeroOneIP.zeroOneIPStructuredToBinaryStructuredTMKarpReduction ∧
      certifiedReduction.toTMKarpReduction.f = certifiedReduction.program.run ∧
      certifiedReduction.toTMKarpReduction.polytime = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM =
        ComplexityReduction.Karp21.ZeroOneIP.zeroOneIPStructuredToBinaryStructuredTMKarpReduction.polytime ∧
      zeroOneIPStructuredToBinaryPrimitive.tmPolyTime =
        ComplexityReduction.Karp21.ZeroOneIP.zeroOneIPStructuredToBinaryStructuredTMKarpReduction.polytime ∧
      certifiedReduction.program.compileTM =
        ComplexityReduction.Karp21.ZeroOneIP.zeroOneIPStructuredToBinaryStructuredTMKarpReduction.polytime := by
  exact ⟨sourceProblem_toEncodedDecisionProblem_eq_zeroOneIntegerProgrammingStructuredDecisionProblem,
    targetProblem_toEncodedDecisionProblem_eq_zeroOneIntegerProgrammingBinaryStructuredDecisionProblem,
    certifiedReduction_tmKarpReduction_eq_zeroOneIPStructuredToBinaryStructuredTMKarpReduction,
    certifiedReduction_tmKarpReduction_run_is_program,
    certifiedReduction_tmKarpReduction_directTM_is_program_compileTM,
    certifiedReduction_directTM_eq_namedCRStructuredTMKarpReduction,
    zeroOneIPStructuredToBinaryPrimitive_directTM_eq_namedCRStructuredTMKarpReduction,
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
      certifiedReduction.program = PolyProg.atom zeroOneIPStructuredToBinaryPrimitive ∧
      certifiedReduction.directTM = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM = zeroOneIPStructuredToBinaryPrimitive.tmPolyTime ∧
      certifiedReduction.compatibilityCost = certifiedReduction.program.compatibilityCost := by
  refine ⟨certifiedReduction.correct, certifiedReduction_program, ?_, ?_, ?_⟩
  · exact CertifiedReduction.directTM_eq_compileTM certifiedReduction
  · exact certifiedReduction_compileTM_eq_primitive
  · exact CertifiedReduction.compatibilityCost_eq_program_compatibilityCost certifiedReduction

/--
The exact ingress component, compilation, semantic correctness, and the
one-way CR facade all retain the same standard direct-TM primitive atom. The
representation-changing identity executable therefore cannot be mistaken for
a typed representation identity or promoted from a bare cost map.
-/
theorem certifiedReduction_completeStandardDirectTMProvenance :
    certifiedReduction.program = PolyProg.atom zeroOneIPStructuredToBinaryPrimitive ∧
      certifiedReduction.program.endpointIdentities =
        ⟨sourcePresentation.representation, targetPresentation.representation⟩ ∧
      certifiedReduction.program.endpointIdentities.source ≠
        certifiedReduction.program.endpointIdentities.target ∧
      certifiedReduction.program.run = id ∧
      zeroOneIPStructuredToBinaryPrimitive.tmPolyTime =
        ComplexityReduction.Karp21.ZeroOneIP.integerProgrammingStructuredToBinary_tm_polytime ∧
      certifiedReduction.program.compileTM =
        ComplexityReduction.Karp21.ZeroOneIP.integerProgrammingStructuredToBinary_tm_polytime ∧
      certifiedReduction.directTM = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM =
        ComplexityReduction.Karp21.ZeroOneIP.integerProgrammingStructuredToBinary_tm_polytime ∧
      certifiedReduction.compatibilityCost = certifiedReduction.program.compatibilityCost ∧
      certifiedReduction.toTMKarpReduction =
        ComplexityReduction.Karp21.ZeroOneIP.zeroOneIPStructuredToBinaryStructuredTMKarpReduction := by
  exact ⟨certifiedReduction_program,
    certifiedReduction_program_endpointIdentities,
    certifiedReduction_program_endpointIdentities_ne,
    rfl,
    zeroOneIPStructuredToBinaryPrimitive_directTM_eq_standardDirectTM,
    certifiedReduction_compileTM_eq_standardDirectTM,
    CertifiedReduction.directTM_eq_compileTM certifiedReduction,
    certifiedReduction_directTM_eq_standardDirectTM,
    CertifiedReduction.compatibilityCost_eq_program_compatibilityCost certifiedReduction,
    certifiedReduction_tmKarpReduction_eq_zeroOneIPStructuredToBinaryStructuredTMKarpReduction⟩

end ZeroOneIPToZeroOneIPBinary
end Routes
end ComplexityReduction
