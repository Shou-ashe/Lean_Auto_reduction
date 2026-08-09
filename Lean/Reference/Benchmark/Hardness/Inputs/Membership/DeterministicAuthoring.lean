import ComplexityReduction.Agent.Hardness.Authoring
import ComplexityReduction.Agent.Hardness.Gap
import ComplexityReduction.Problems.Karp21.ThreeSATNativeVerifier

/-!
Phase-6 native-membership authoring fixture.

The public module exposes three independent, closed component declarations:
an exact verifier, the structural certificate for that verifier's witness
presentation, and a checked-decoder discipline indexed by the same verifier.
It deliberately does not register `NativeTMInNP problem`; the agent must emit
and validate the four-stage job-local membership bundle.
-/

namespace Benchmark.Hardness.Inputs.Membership.DeterministicAuthoring

open ComplexityReduction
open ComplexityReduction.Encoding
open ComplexityReduction.Certificate
open ComplexityReduction.Program

private def semantic : ComplexityReduction.DecisionProblem where
  Instance := Bool
  isYes := fun _ => True

@[complexity_reduction_ir_typed_problem]
def problem : PresentedProblem where
  semantic := semantic
  representation := StandardInstances.bool
  carrier_eq := rfl

abbrev source : PresentedProblem := problem

abbrev witness : LawfulEncodedType :=
  ComplexityReduction.Problems.Karp21.Satisfiability.finiteAssignmentPresentation

def checker :
    PolyProg (StandardInstances.prod problem.representation witness) StandardInstances.bool :=
  .const (StandardInstances.prod problem.representation witness) StandardInstances.bool true

def verifier : CertifiedVerifier problem where
  witness := witness
  checker := checker
  witnessBound := fun _ => 0
  witnessBoundPoly := ComplexityReduction.PolynomialTimeBound.intro_with 0 0 0 (by
    intro input
    simp)
  correct := by
    intro input
    constructor
    · intro _
      refine ⟨[], ?_, ?_⟩
      · simp [witness]
      · simp [checker]
    · intro _
      trivial
  checkerSound := by
    intro input candidate accepted
    trivial

def witnessPresentation : verifier.witness.StructuralCertificate := by
  exact ComplexityReduction.Problems.Karp21.Satisfiability.finiteAssignmentStructuralCertificate

noncomputable def encodedSuffixDecoder :
    ComplexityReduction.SAT.TMVerifierXOnlyEncodedSuffixDecoder verifier.toTMVerifier :=
  ComplexityReduction.SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofCertificateDecoder
    verifier.toTMVerifier
    ComplexityReduction.SAT.finiteAssignmentCertDecode
    (by
      intro symbols bits decoded
      exact ComplexityReduction.SAT.finiteAssignmentCertDecode_sound decoded)
    ComplexityReduction.SAT.finiteAssignmentCertDecode_complete

theorem finiteBoolCertificateSymbols_eq_encode (bits : List Bool) :
    ComplexityReduction.SAT.tmVerifierFiniteBoolCertificateSymbols
        (V := verifier.toTMVerifier) (fun bit : Bool => some bit) none bits =
      ComplexityReduction.SAT.finiteAssignmentCertEncodedType.encode bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      change
        some bit :: none ::
            ComplexityReduction.SAT.tmVerifierFiniteBoolCertificateSymbols
              (V := verifier.toTMVerifier) (fun bit : Bool => some bit) none bits =
          some bit :: none :: ComplexityReduction.SAT.finiteAssignmentCertEncodedType.encode bits
      rw [ih]

theorem certificateInputSuffixEncoded_eq_finiteBoolSymbols (bits : List Bool) :
    ComplexityReduction.SAT.tmVerifierCertificateInputSuffixEncoded verifier.toTMVerifier bits =
      (ComplexityReduction.SAT.tmVerifierFiniteBoolCertificateSymbols
        (V := verifier.toTMVerifier) (fun bit : Bool => some bit) none bits).map
        (fun symbol => some (Sum.inr symbol)) := by
  change
    (ComplexityReduction.SAT.finiteAssignmentCertEncodedType.encode bits).map
        (fun symbol => some (Sum.inr symbol)) =
      (ComplexityReduction.SAT.tmVerifierFiniteBoolCertificateSymbols
        (V := verifier.toTMVerifier) (fun bit : Bool => some bit) none bits).map
        (fun symbol => some (Sum.inr symbol))
  rw [finiteBoolCertificateSymbols_eq_encode]
  rfl

noncomputable def discipline : CertifiedVerifierEncodingDiscipline verifier :=
  CheckedDecoderNativeDiscipline.ofBackend
    (ComplexityReduction.SAT.TMVerifierEncodingDiscipline.ofBoolListCertificate
      verifier.toTMVerifier
      (fun bit : Bool => some bit) none
      encodedSuffixDecoder
      id id
      certificateInputSuffixEncoded_eq_finiteBoolSymbols
      certificateInputSuffixEncoded_eq_finiteBoolSymbols)

@[complexity_reduction_ir_typed_gap]
def gap : ComplexityReduction.Agent.Hardness.Gap.DeclaredComponentGap
    .verifierProgram .finalComposition problem problem :=
  .exact

@[complexity_reduction_ir_hardness_native_membership_template]
def template : ComplexityReduction.Agent.Hardness.Authoring.NativeMembershipTemplate
    problem verifier witnessPresentation discipline :=
  ⟨True.intro⟩

end Benchmark.Hardness.Inputs.Membership.DeterministicAuthoring
