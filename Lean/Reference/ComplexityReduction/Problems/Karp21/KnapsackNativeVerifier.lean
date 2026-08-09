/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipKnapsackBinary
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.Part3
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.UnaryToBinary
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeSATSuffixDecoderTM
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.TMEncodingDisciplineTemplates
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.CheckedDecoderDiscipline
import ComplexityReduction.Presentation.Knapsack
import ComplexityReduction.Presentation.KnapsackBinary
import ComplexityReduction.Presentation.Satisfiability
import ComplexityReduction.Protocol.TrustPolicy

/-!
Standard-axiom native verifier for the canonical unary structured Knapsack
presentation.

The legacy binary Knapsack membership construction has one `native_decide`
proof in the accumulator-initialization size bound.  This leaf reconstructs
the same checker TM chain with that closed arithmetic fact proved in Lean,
then composes the standard unary-to-binary normalization with the checker.
The resulting `CertifiedVerifier`, its compiled direct-TM witness, and its
checked suffix discipline are all indexed by the one V2 checker program.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace KnapsackNativeVerifier

open Encoding Certificate Program

namespace StandardBinary

open ComplexityReduction
open ComplexityReduction.Combinatorics
open ComplexityReduction.Karp21.Knapsack

/-- The binary fold accumulator has a kernel-checked constant initial size. -/
theorem foldRunnerInit_inputSize_le_twenty :
    foldAccEncodedType.inputSize foldRunnerInit ≤ 20 := by
  simp [foldAccEncodedType, foldRunnerInit, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat]
  rw [SAT.boolList_inputSize_eq_two_mul_length]
  norm_num

/--
The legacy fold proof with its sole `native_decide` call replaced by the
closed arithmetic theorem above.
-/
theorem foldAcc_tm_polytime :
    TMPolyTimeMap foldInstructionListEncodedType foldAccEncodedType
      (fun xs : foldInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc x => foldStep (acc, x)) foldRunnerInit) := by
  rcases foldStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      foldInstructionEncodedType foldAccEncodedType
      foldStep foldRunnerInit hStep
      (Polynomial.C 20) (Polynomial.C 10 * Polynomial.X + Polynomial.C 50) ?_ ?_
  · intro xs
    change foldAccEncodedType.inputSize foldRunnerInit ≤
      (Polynomial.C 20).eval (foldInstructionEncodedType.list.inputSize xs)
    simpa using foldRunnerInit_inputSize_le_twenty
  · intro source acc instr hInstr
    have hInstr' :
        foldInstructionEncodedType.inputSize instr ≤
          foldInstructionListEncodedType.inputSize source := by
      simpa [foldInstructionListEncodedType] using hInstr
    simpa [foldInstructionListEncodedType] using foldStep_growth source acc instr hInstr'

/-- Standard direct-TM realization of the binary fold projection. -/
theorem foldFromInstructions_tm_polytime :
    TMPolyTimeMap foldInstructionListEncodedType
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      foldFromInstructions := by
  have hFold := foldAcc_tm_polytime
  let Rest := EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
  have hRest :
      TMPolyTimeMap foldAccEncodedType Rest (fun acc : FoldAcc => acc.2) := by
    simpa [foldAccEncodedType, Rest] using
      TMPolyTimeMap.snd knapsackBinaryCertificateEncodedType Rest
  have hSums :
      TMPolyTimeMap Rest (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun rest : Nat × (Nat × Nat) => rest.2) := by
    simpa [Rest] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
  have hProjection := TMPolyTimeMap.comp hSums hRest
  have hComp := TMPolyTimeMap.comp hProjection hFold
  simpa [Function.comp, foldFromInstructions, foldAccEncodedType, Rest] using hComp

/-- Standard direct-TM realization of the binary certificate sums. -/
theorem certificateSums_tm_polytime :
    TMPolyTimeMap foldInputEncodedType
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      certificateSums := by
  have hComp := TMPolyTimeMap.comp foldFromInstructions_tm_polytime
    foldInstructions_tm_polytime
  simpa [Function.comp, certificateSums] using hComp

/--
The exact existing binary Knapsack checker executable, now with a
standard-axiom direct-TM realization.
-/
theorem finiteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod knapsackBinaryStructuredEncodedType
        knapsackBinaryCertificateEncodedType)
      EncodedType.bool
      (fun p : KnapsackInput × KnapsackBinaryCertificate =>
        knapsackBinaryStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod knapsackBinaryStructuredEncodedType
    knapsackBinaryCertificateEncodedType
  have hInstance :
      TMPolyTimeMap X knapsackBinaryStructuredEncodedType
        (fun p : KnapsackInput × KnapsackBinaryCertificate => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst knapsackBinaryStructuredEncodedType
        knapsackBinaryCertificateEncodedType
  have hBits :
      TMPolyTimeMap X knapsackBinaryCertificateEncodedType
        (fun p : KnapsackInput × KnapsackBinaryCertificate => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd knapsackBinaryStructuredEncodedType
        knapsackBinaryCertificateEncodedType
  have hItems :
      TMPolyTimeMap X knapsackItemListBinaryStructuredEncodedType
        (fun p : KnapsackInput × KnapsackBinaryCertificate => p.1.items) := by
    have hComp := TMPolyTimeMap.comp knapsackBinaryItemsTMBackedMap.tm_polytime hInstance
    simpa [Function.comp, knapsackBinaryItemsForMembership, X] using hComp
  have hBounds :
      TMPolyTimeMap X knapsackBoundsBinaryStructuredEncodedType
        (fun p : KnapsackInput × KnapsackBinaryCertificate =>
          (p.1.capacity, p.1.targetValue)) := by
    have hComp := TMPolyTimeMap.comp knapsackBinaryBoundsTMBackedMap.tm_polytime hInstance
    simpa [Function.comp, knapsackBinaryBoundsForMembership, X] using hComp
  have hCapacity : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : KnapsackInput × KnapsackBinaryCertificate => p.1.capacity) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hFst hBounds
    simpa [Function.comp, knapsackBoundsBinaryStructuredEncodedType, X] using hComp
  have hTarget : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : KnapsackInput × KnapsackBinaryCertificate => p.1.targetValue) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hSnd hBounds
    simpa [Function.comp, knapsackBoundsBinaryStructuredEncodedType, X] using hComp
  have hSumsInput :
      TMPolyTimeMap X foldInputEncodedType
        (fun p : KnapsackInput × KnapsackBinaryCertificate => (p.1.items, p.2)) :=
    TMPolyTimeMap.prod_mk hItems hBits
  have hSums :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : KnapsackInput × KnapsackBinaryCertificate =>
          certificateSums (p.1.items, p.2)) := by
    have hComp := TMPolyTimeMap.comp certificateSums_tm_polytime hSumsInput
    simpa [Function.comp, foldInputEncodedType, X] using hComp
  have hWeightSum : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : KnapsackInput × KnapsackBinaryCertificate =>
        (certificateSums (p.1.items, p.2)).1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hFst hSums
    simpa [Function.comp, X] using hComp
  have hValueSum : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : KnapsackInput × KnapsackBinaryCertificate =>
        (certificateSums (p.1.items, p.2)).2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hSnd hSums
    simpa [Function.comp, X] using hComp
  have hWeightOKInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : KnapsackInput × KnapsackBinaryCertificate =>
          ((certificateSums (p.1.items, p.2)).1, p.1.capacity)) :=
    TMPolyTimeMap.prod_mk hWeightSum hCapacity
  have hWeightOK :
      TMPolyTimeMap X EncodedType.bool
        (fun p : KnapsackInput × KnapsackBinaryCertificate =>
          binaryNatLeBool ((certificateSums (p.1.items, p.2)).1, p.1.capacity)) := by
    have hComp := TMPolyTimeMap.comp binaryNatLeBool_tm_polytime hWeightOKInput
    simpa [Function.comp, X] using hComp
  have hValueOKInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : KnapsackInput × KnapsackBinaryCertificate =>
          (p.1.targetValue, (certificateSums (p.1.items, p.2)).2)) :=
    TMPolyTimeMap.prod_mk hTarget hValueSum
  have hValueOK :
      TMPolyTimeMap X EncodedType.bool
        (fun p : KnapsackInput × KnapsackBinaryCertificate =>
          binaryNatLeBool (p.1.targetValue, (certificateSums (p.1.items, p.2)).2)) := by
    have hComp := TMPolyTimeMap.comp binaryNatLeBool_tm_polytime hValueOKInput
    simpa [Function.comp, X] using hComp
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : KnapsackInput × KnapsackBinaryCertificate =>
          (binaryNatLeBool ((certificateSums (p.1.items, p.2)).1, p.1.capacity),
            binaryNatLeBool (p.1.targetValue, (certificateSums (p.1.items, p.2)).2))) :=
    TMPolyTimeMap.prod_mk hWeightOK hValueOK
  have hAnd := TMPolyTimeMap.comp ComplexityReduction.Karp21.Clique.boolAndPair_tm_polytime hAndInput
  simpa [Function.comp, knapsackBinaryStructuredFiniteVerify, X] using hAnd

end StandardBinary

/-- The V2 witness representation for finite Boolean selections. -/
abbrev structuredWitnessPresentation : LawfulEncodedType :=
  Presentation.Satisfiability.finiteAssignmentPresentation

/-- The canonical V2 Knapsack checker, after unary-to-binary normalization. -/
@[complexity_reduction_ir_typed_primitive]
def structuredCheckerPrimitive :
    Primitive
      (StandardInstances.prod Presentation.Knapsack.structuredPresentation
        structuredWitnessPresentation)
      StandardInstances.bool :=
  Primitive.ofTMPolyTime
    (fun input =>
      ComplexityReduction.Karp21.Knapsack.knapsackBinaryStructuredFiniteVerify input.1 input.2)
    (by
      let X := ComplexityReduction.EncodedType.prod Presentation.Knapsack.structuredPresentation.encodedType
        structuredWitnessPresentation.encodedType
      have hInstance :
          ComplexityReduction.TMPolyTimeMap X
            Presentation.Knapsack.structuredPresentation.encodedType
            (fun input : X.Carrier => input.1) := by
        simpa [X] using ComplexityReduction.TMPolyTimeMap.fst
          Presentation.Knapsack.structuredPresentation.encodedType
          structuredWitnessPresentation.encodedType
      have hWitness :
          ComplexityReduction.TMPolyTimeMap X structuredWitnessPresentation.encodedType
            (fun input : X.Carrier => input.2) := by
        simpa [X] using ComplexityReduction.TMPolyTimeMap.snd
          Presentation.Knapsack.structuredPresentation.encodedType
          structuredWitnessPresentation.encodedType
      have hNormalized :
          ComplexityReduction.TMPolyTimeMap X
            Presentation.KnapsackBinary.structuredPresentation.encodedType
            (fun input : X.Carrier => input.1) := by
        have hComp := ComplexityReduction.TMPolyTimeMap.comp
          ComplexityReduction.Karp21.Knapsack.knapsackStructuredToBinary_tm_polytime hInstance
        simpa [Function.comp, X] using hComp
      have hPair :
          ComplexityReduction.TMPolyTimeMap X
            (ComplexityReduction.EncodedType.prod Presentation.KnapsackBinary.structuredPresentation.encodedType
              structuredWitnessPresentation.encodedType)
            (fun input : X.Carrier => (input.1, input.2)) :=
        ComplexityReduction.TMPolyTimeMap.prod_mk hNormalized hWitness
      have hComp := ComplexityReduction.TMPolyTimeMap.comp
        StandardBinary.finiteVerify_tm_polytime hPair
      simpa [Function.comp, X] using hComp)

/-- The one typed checker program used by all V2 Knapsack verifier evidence. -/
def structuredChecker :
    PolyProg
      (StandardInstances.prod Presentation.Knapsack.structuredPresentation
        structuredWitnessPresentation)
      StandardInstances.bool :=
  .atom structuredCheckerPrimitive

@[simp]
theorem structuredChecker_run
    (input : (StandardInstances.prod Presentation.Knapsack.structuredPresentation
      structuredWitnessPresentation).Carrier) :
    structuredChecker.run input =
      ComplexityReduction.Karp21.Knapsack.knapsackBinaryStructuredFiniteVerify input.1 input.2 :=
  rfl

/-- The direct-TM realization is compiled from the exact V2 checker program. -/
theorem structuredChecker_directTM :
    ComplexityReduction.TMPolyTimeMap
      (StandardInstances.prod Presentation.Knapsack.structuredPresentation
        structuredWitnessPresentation).encodedType
      StandardInstances.bool.encodedType
      (fun input =>
        ComplexityReduction.Karp21.Knapsack.knapsackBinaryStructuredFiniteVerify input.1 input.2) := by
  simpa only [structuredChecker_run] using structuredChecker.compileTM

/-- The native V2 verifier for the exact unary structured Knapsack endpoint. -/
@[complexity_reduction_ir_typed_verifier]
def structuredVerifier : CertifiedVerifier Presentation.Knapsack.structuredProblem where
  witness := structuredWitnessPresentation
  checker := structuredChecker
  witnessBound := fun input =>
    2 * Presentation.Knapsack.structuredPresentation.encodedType.inputSize input
  witnessBoundPoly := ComplexityReduction.PolynomialTimeBound.intro_with 1 2 0 (by
    intro input
    change 2 * ComplexityReduction.Combinatorics.knapsackStructuredEncodedType.inputSize input ≤
      2 * ComplexityReduction.Combinatorics.knapsackStructuredEncodedType.inputSize input ^ 1 + 0
    simp)
  correct := by
    intro input
    change ComplexityReduction.Combinatorics.Knapsack input ↔
      ∃ candidate : List Bool,
        ComplexityReduction.SAT.finiteAssignmentCertEncodedType.inputSize candidate ≤
            2 * ComplexityReduction.Combinatorics.knapsackStructuredEncodedType.inputSize input ∧
          ComplexityReduction.Karp21.Knapsack.knapsackBinaryStructuredFiniteVerify input candidate = true
    constructor
    · rintro ⟨selected, hLength, hWeight, hValue⟩
      refine ⟨selected, ?_, ?_⟩
      · calc
          ComplexityReduction.SAT.finiteAssignmentCertEncodedType.inputSize selected =
              2 * selected.length := by
                rw [ComplexityReduction.SAT.boolList_inputSize_eq_two_mul_length]
          _ = 2 * input.items.length := by rw [hLength]
          _ ≤ 2 * ComplexityReduction.Combinatorics.knapsackStructuredEncodedType.inputSize input :=
            Nat.mul_le_mul_left 2
              (ComplexityReduction.Karp21.Partition.itemLength_le_knapsackStructured_inputSize input)
      · have hSelection :=
          ComplexityReduction.Karp21.Knapsack.selectionFrom_self_of_length
            input.items selected hLength
        have hWeightFrom :=
          ComplexityReduction.Karp21.Knapsack.selectedWeightFrom_eq_selectedWeight_selectionFrom
            input.items selected 0 input.capacity input.targetValue
        have hValueFrom :=
          ComplexityReduction.Karp21.Knapsack.selectedValueFrom_eq_selectedValue_selectionFrom
            input.items selected 0 input.capacity input.targetValue
        rw [hSelection] at hWeightFrom hValueFrom
        exact
          (ComplexityReduction.Karp21.Knapsack.knapsackBinaryStructuredFiniteVerify_eq_true_iff
            input selected).2
            ⟨by simpa [hWeightFrom] using hWeight,
              by simpa [hValueFrom] using hValue⟩
    · rintro ⟨bits, _, accepted⟩
      let selected := ComplexityReduction.Karp21.Knapsack.selectionFrom input.items bits 0
      have hLength : selected.length = input.items.length := by
        simp [selected]
      have hWeightFrom :=
        ComplexityReduction.Karp21.Knapsack.selectedWeightFrom_eq_selectedWeight_selectionFrom
          input.items bits 0 input.capacity input.targetValue
      have hValueFrom :=
        ComplexityReduction.Karp21.Knapsack.selectedValueFrom_eq_selectedValue_selectionFrom
          input.items bits 0 input.capacity input.targetValue
      rcases
          (ComplexityReduction.Karp21.Knapsack.knapsackBinaryStructuredFiniteVerify_eq_true_iff
            input bits).1 accepted with
        ⟨hWeight, hValue⟩
      exact ⟨selected, hLength,
        by simpa [selected, hWeightFrom] using hWeight,
        by simpa [selected, hValueFrom] using hValue⟩
  checkerSound := by
    intro input bits accepted
    let selected := ComplexityReduction.Karp21.Knapsack.selectionFrom input.items bits 0
    have hLength : selected.length = input.items.length := by
      simp [selected]
    have hWeightFrom :=
      ComplexityReduction.Karp21.Knapsack.selectedWeightFrom_eq_selectedWeight_selectionFrom
        input.items bits 0 input.capacity input.targetValue
    have hValueFrom :=
      ComplexityReduction.Karp21.Knapsack.selectedValueFrom_eq_selectedValue_selectionFrom
        input.items bits 0 input.capacity input.targetValue
    rcases
        (ComplexityReduction.Karp21.Knapsack.knapsackBinaryStructuredFiniteVerify_eq_true_iff
          input bits).1 accepted with
      ⟨hWeight, hValue⟩
    exact ⟨selected, hLength,
      by simpa [selected, hWeightFrom] using hWeight,
      by simpa [selected, hValueFrom] using hValue⟩

/-- Explicit decoder for the exact certificate encoding of `structuredVerifier`. -/
noncomputable def structuredEncodedSuffixDecoder :
    ComplexityReduction.SAT.TMVerifierXOnlyEncodedSuffixDecoder structuredVerifier.toTMVerifier :=
  ComplexityReduction.SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofCertificateDecoder
    structuredVerifier.toTMVerifier
    ComplexityReduction.SAT.finiteAssignmentCertDecode
    (by
      intro symbols bits h
      exact ComplexityReduction.SAT.finiteAssignmentCertDecode_sound h)
    ComplexityReduction.SAT.finiteAssignmentCertDecode_complete

theorem structuredFiniteBoolCertificateSymbols_eq_encode (bits : List Bool) :
    ComplexityReduction.SAT.tmVerifierFiniteBoolCertificateSymbols
        (V := structuredVerifier.toTMVerifier) (fun bit : Bool => some bit) none bits =
      ComplexityReduction.SAT.finiteAssignmentCertEncodedType.encode bits := by
  induction bits with
  | nil =>
      rfl
  | cons bit bits ih =>
      change
        some bit :: none ::
            ComplexityReduction.SAT.tmVerifierFiniteBoolCertificateSymbols
              (V := structuredVerifier.toTMVerifier) (fun bit : Bool => some bit) none bits =
          some bit :: none :: ComplexityReduction.SAT.finiteAssignmentCertEncodedType.encode bits
      rw [ih]

/-- The checker verifier has exactly the standard finite-Boolean suffix layout. -/
theorem structuredCertificateInputSuffixEncoded_eq_finiteBoolSymbols (bits : List Bool) :
    ComplexityReduction.SAT.tmVerifierCertificateInputSuffixEncoded structuredVerifier.toTMVerifier bits =
      (ComplexityReduction.SAT.tmVerifierFiniteBoolCertificateSymbols
        (V := structuredVerifier.toTMVerifier) (fun bit : Bool => some bit) none bits).map
        (fun symbol => some (Sum.inr symbol)) := by
  change
    (ComplexityReduction.SAT.finiteAssignmentCertEncodedType.encode bits).map
        (fun symbol => some (Sum.inr symbol)) =
      (ComplexityReduction.SAT.tmVerifierFiniteBoolCertificateSymbols
        (V := structuredVerifier.toTMVerifier) (fun bit : Bool => some bit) none bits).map
        (fun symbol => some (Sum.inr symbol))
  rw [structuredFiniteBoolCertificateSymbols_eq_encode]
  rfl

/-- Checked-decoder discipline indexed by the exact V2 verifier. -/
@[complexity_reduction_ir_typed_verifier_discipline]
noncomputable def structuredCheckedDecoderDiscipline :
    CertifiedVerifierEncodingDiscipline structuredVerifier :=
  CheckedDecoderNativeDiscipline.ofBackend
    (ComplexityReduction.SAT.TMVerifierEncodingDiscipline.ofBoolListCertificate
      structuredVerifier.toTMVerifier
      (fun bit : Bool => some bit) none
      structuredEncodedSuffixDecoder
      id id
      (by
        intro bits
        exact structuredCertificateInputSuffixEncoded_eq_finiteBoolSymbols bits)
      (by
        intro bits
        exact structuredCertificateInputSuffixEncoded_eq_finiteBoolSymbols bits))

/-- Native capability made only from the exact checker and checked decoder. -/
@[complexity_reduction_ir_typed_verifier]
noncomputable def structuredNativeCapability :
    NativeVerifierCapability Presentation.Knapsack.structuredProblem :=
  CheckedDecoderNativeDiscipline.toNativeVerifierCapability structuredCheckedDecoderDiscipline

/-- The standard checker supplies the safe backend membership projection. -/
@[complexity_reduction_ir_typed_verifier]
theorem structured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      Presentation.Knapsack.structuredProblem.toEncodedDecisionProblem :=
  structuredVerifier.toBackendTMInNP

/-- Native Knapsack membership is introduced from the exact paired capability. -/
@[complexity_reduction_ir_typed_native_membership]
theorem structured_nativeTMInNP : NativeTMInNP Presentation.Knapsack.structuredProblem :=
  NativeTMInNP.ofCapability structuredNativeCapability

/-- The accepted native request exposes the exact V2 capability. -/
noncomputable def structuredNativeVerifierOutcome :
    Protocol.TrustedNativeVerifierOutcome Presentation.Knapsack.structuredProblem :=
  Protocol.acceptNativeVerifier structuredNativeCapability

#print axioms StandardBinary.foldAcc_tm_polytime
#print axioms StandardBinary.finiteVerify_tm_polytime
#print axioms structuredChecker_directTM
#print axioms structuredVerifier
#print axioms structuredCheckedDecoderDiscipline
#print axioms structuredNativeCapability

end KnapsackNativeVerifier
end Karp21
end Problems
end ComplexityReduction
