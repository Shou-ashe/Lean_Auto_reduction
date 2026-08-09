/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.FiniteBoolSuffixDecodersTM

/-!
Checked finite-Boolean suffix decoders for reduction-pullback verifiers.

The ordinary `TMInNP.of_reduction` theorem proves membership after composing a
source instance map with a target verifier.  This file names the same verifier
shape for the `List Bool` certificate branches and equips those concrete
pullback verifiers with checked suffix decoders.  It does not claim that
arbitrary ordinary `TMInNP` witnesses carry such decoders.
-/

namespace ComplexityReduction

namespace TMKarpReduction

/-- Pull back a concrete verifier along a direct TM Karp reduction. -/
noncomputable def pullbackVerifier {A B : EncodedDecisionProblem}
    (rAB : TMKarpReduction A B) (VB : TMVerifier B) : TMVerifier A where
  Cert := VB.Cert
  verify := fun x c => VB.verify (rAB.f x) c
  verifier_polytime := by
    let X := EncodedType.prod A.Instance VB.Cert
    have hFst : TMPolyTimeMap X A.Instance
        (fun p : A.Instance.Carrier × VB.Cert.Carrier => p.1) := by
      simpa [X] using TMPolyTimeMap.fst A.Instance VB.Cert
    have hRed : TMPolyTimeMap X B.Instance
        (fun p : A.Instance.Carrier × VB.Cert.Carrier => rAB.f p.1) := by
      have hComp := TMPolyTimeMap.comp rAB.polytime hFst
      simpa [Function.comp, X] using hComp
    have hSnd : TMPolyTimeMap X VB.Cert
        (fun p : A.Instance.Carrier × VB.Cert.Carrier => p.2) := by
      simpa [X] using TMPolyTimeMap.snd A.Instance VB.Cert
    have hPair : TMPolyTimeMap X (EncodedType.prod B.Instance VB.Cert)
        (fun p : A.Instance.Carrier × VB.Cert.Carrier => (rAB.f p.1, p.2)) :=
      TMPolyTimeMap.prod_mk hRed hSnd
    have hComp := TMPolyTimeMap.comp VB.verifier_polytime hPair
    simpa [Function.comp, X] using hComp
  cert_bound := by
    rcases VB.cert_bound with ⟨degreeB, coeffB, constB, hCertB⟩
    rcases rAB.polytime.outputSizeBound with ⟨degreeR, coeffR, constR, hRedSize⟩
    let q : Polynomial Nat :=
      Polynomial.C coeffB *
        ((Polynomial.C coeffR * Polynomial.X ^ degreeR + Polynomial.C constR) ^ degreeB) +
          Polynomial.C constB
    rcases TM2Programs.polynomialNat_eval_polynomialSizeBound q with
      ⟨degree, coeff, const, hq⟩
    refine ⟨degree, coeff, const, ?_⟩
    intro x hx
    have hxB : B.isYes (rAB.f x) := (rAB.correct x).1 hx
    rcases hCertB (rAB.f x) hxB with ⟨c, hcSize, hcVerify⟩
    refine ⟨c, ?_, hcVerify⟩
    let n := A.Instance.inputSize x
    have hRed :
        B.Instance.inputSize (rAB.f x) ≤ coeffR * n ^ degreeR + constR := by
      simpa [n] using hRedSize x
    have hPow :
        (B.Instance.inputSize (rAB.f x)) ^ degreeB ≤
          (coeffR * n ^ degreeR + constR) ^ degreeB :=
      Nat.pow_le_pow_left hRed degreeB
    have hToQ : VB.Cert.inputSize c ≤ q.eval n := by
      calc
        VB.Cert.inputSize c
            ≤ coeffB * (B.Instance.inputSize (rAB.f x)) ^ degreeB + constB := hcSize
        _ ≤ coeffB * (coeffR * n ^ degreeR + constR) ^ degreeB + constB := by
              exact Nat.add_le_add_right (Nat.mul_le_mul_left coeffB hPow) constB
        _ = q.eval n := by
              simp [q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
                Polynomial.eval_X]
    exact hToQ.trans (hq n)
  sound := by
    intro x c hVerify
    exact (rAB.correct x).2 (VB.sound (rAB.f x) c hVerify)

end TMKarpReduction

namespace Karp21

open ComplexityReduction.Combinatorics

/-! ### Pullback verifiers with finite-Boolean certificates -/

/--
Binary-structured 0-1 IP verifier obtained by pulling back the binary Knapsack
finite verifier along the direct compact reduction.
-/
noncomputable def zeroOneIPBinaryStructuredFiniteTMVerifier :
    TMVerifier zeroOneIntegerProgrammingBinaryStructuredDecisionProblem :=
  TMKarpReduction.pullbackVerifier
    Knapsack.zeroOneIPToKnapsackBinaryStructuredTMKarpReduction
    knapsackBinaryStructuredFiniteTMVerifier

/--
Structured 0-1 IP verifier obtained by changing numeric payloads to binary and
then reusing the binary-structured pullback verifier.
-/
noncomputable def zeroOneIPStructuredFiniteTMVerifier :
    TMVerifier zeroOneIntegerProgrammingStructuredDecisionProblem :=
  TMKarpReduction.pullbackVerifier
    ZeroOneIP.zeroOneIPStructuredToBinaryStructuredTMKarpReduction
    zeroOneIPBinaryStructuredFiniteTMVerifier

/--
Structured Knapsack verifier obtained by changing numeric payloads to binary and
then reusing the binary Knapsack verifier.
-/
noncomputable def knapsackStructuredFiniteTMVerifier :
    TMVerifier knapsackStructuredDecisionProblem :=
  TMKarpReduction.pullbackVerifier
    Knapsack.knapsackStructuredToBinaryStructuredTMKarpReduction
    knapsackBinaryStructuredFiniteTMVerifier

/-! ### Binary 0-1 IP -/

theorem zeroOneIPBinaryStructuredFiniteBoolCertificateSymbols_eq_encode
    (bits : List Bool) :
    SAT.tmVerifierFiniteBoolCertificateSymbols
        (V := zeroOneIPBinaryStructuredFiniteTMVerifier) (fun b : Bool => some b) none bits =
      SAT.finiteAssignmentCertEncodedType.encode bits := by
  induction bits with
  | nil =>
      rfl
  | cons b bits ih =>
      change
        some b :: none ::
            SAT.tmVerifierFiniteBoolCertificateSymbols
              (V := zeroOneIPBinaryStructuredFiniteTMVerifier)
              (fun b : Bool => some b) none bits =
          some b :: none :: SAT.finiteAssignmentCertEncodedType.encode bits
      rw [ih]

theorem zeroOneIPBinaryStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols
    (bits : List Bool) :
    SAT.tmVerifierCertificateInputSuffixEncoded zeroOneIPBinaryStructuredFiniteTMVerifier bits =
      (SAT.tmVerifierFiniteBoolCertificateSymbols
          (V := zeroOneIPBinaryStructuredFiniteTMVerifier)
          (fun b : Bool => some b) none bits).map (fun s => some (Sum.inr s)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded,
    zeroOneIPBinaryStructuredFiniteTMVerifier, TMKarpReduction.pullbackVerifier,
    knapsackBinaryStructuredFiniteTMVerifier, Knapsack.knapsackBinaryCertificateEncodedType]
    using
      congrArg
        (fun xs : List SAT.finiteAssignmentCertEncodedType.Symbol =>
          xs.map (fun s =>
            (some (Sum.inr s) :
              (SAT.tmVerifierInputEncodedType
                zeroOneIPBinaryStructuredFiniteTMVerifier).Symbol)))
        (zeroOneIPBinaryStructuredFiniteBoolCertificateSymbols_eq_encode bits).symm

noncomputable def zeroOneIPBinaryStructuredFiniteEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder zeroOneIPBinaryStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofCertificateDecoder
    zeroOneIPBinaryStructuredFiniteTMVerifier
    SAT.finiteAssignmentCertDecode
    (by
      intro symbols bits h
      exact SAT.finiteAssignmentCertDecode_sound h)
    SAT.finiteAssignmentCertDecode_complete

noncomputable def zeroOneIPBinaryStructuredFiniteCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder zeroOneIPBinaryStructuredFiniteTMVerifier :=
  SAT.tmVerifierFiniteBoolCheckedSuffixDecoder
    zeroOneIPBinaryStructuredFiniteTMVerifier
    (fun b : Bool => some b) none
    zeroOneIPBinaryStructuredFiniteEncodedSuffixDecoder
    (fun bits : List Bool => bits)
    (fun bits : List Bool => bits)
    (by
      intro bits
      exact zeroOneIPBinaryStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols bits)
    (by
      intro bits
      exact zeroOneIPBinaryStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols bits)

theorem zeroOneIPBinaryStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder
      zeroOneIntegerProgrammingBinaryStructuredDecisionProblem :=
  ⟨⟨zeroOneIPBinaryStructuredFiniteTMVerifier,
      zeroOneIPBinaryStructuredFiniteCheckedSuffixDecoder⟩⟩

/-! ### Structured 0-1 IP -/

theorem zeroOneIPStructuredFiniteBoolCertificateSymbols_eq_encode (bits : List Bool) :
    SAT.tmVerifierFiniteBoolCertificateSymbols
        (V := zeroOneIPStructuredFiniteTMVerifier) (fun b : Bool => some b) none bits =
      SAT.finiteAssignmentCertEncodedType.encode bits := by
  induction bits with
  | nil =>
      rfl
  | cons b bits ih =>
      change
        some b :: none ::
            SAT.tmVerifierFiniteBoolCertificateSymbols
              (V := zeroOneIPStructuredFiniteTMVerifier) (fun b : Bool => some b) none bits =
          some b :: none :: SAT.finiteAssignmentCertEncodedType.encode bits
      rw [ih]

theorem zeroOneIPStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols
    (bits : List Bool) :
    SAT.tmVerifierCertificateInputSuffixEncoded zeroOneIPStructuredFiniteTMVerifier bits =
      (SAT.tmVerifierFiniteBoolCertificateSymbols
          (V := zeroOneIPStructuredFiniteTMVerifier)
          (fun b : Bool => some b) none bits).map (fun s => some (Sum.inr s)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded, zeroOneIPStructuredFiniteTMVerifier,
    zeroOneIPBinaryStructuredFiniteTMVerifier, TMKarpReduction.pullbackVerifier,
    knapsackBinaryStructuredFiniteTMVerifier, Knapsack.knapsackBinaryCertificateEncodedType]
    using
      congrArg
        (fun xs : List SAT.finiteAssignmentCertEncodedType.Symbol =>
          xs.map (fun s =>
            (some (Sum.inr s) :
              (SAT.tmVerifierInputEncodedType zeroOneIPStructuredFiniteTMVerifier).Symbol)))
        (zeroOneIPStructuredFiniteBoolCertificateSymbols_eq_encode bits).symm

noncomputable def zeroOneIPStructuredFiniteEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder zeroOneIPStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofCertificateDecoder
    zeroOneIPStructuredFiniteTMVerifier
    SAT.finiteAssignmentCertDecode
    (by
      intro symbols bits h
      exact SAT.finiteAssignmentCertDecode_sound h)
    SAT.finiteAssignmentCertDecode_complete

noncomputable def zeroOneIPStructuredFiniteCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder zeroOneIPStructuredFiniteTMVerifier :=
  SAT.tmVerifierFiniteBoolCheckedSuffixDecoder
    zeroOneIPStructuredFiniteTMVerifier
    (fun b : Bool => some b) none
    zeroOneIPStructuredFiniteEncodedSuffixDecoder
    (fun bits : List Bool => bits)
    (fun bits : List Bool => bits)
    (by
      intro bits
      exact zeroOneIPStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols bits)
    (by
      intro bits
      exact zeroOneIPStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols bits)

theorem zeroOneIPStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder
      zeroOneIntegerProgrammingStructuredDecisionProblem :=
  ⟨⟨zeroOneIPStructuredFiniteTMVerifier,
      zeroOneIPStructuredFiniteCheckedSuffixDecoder⟩⟩

/-! ### Structured Knapsack -/

theorem knapsackStructuredFiniteBoolCertificateSymbols_eq_encode (bits : List Bool) :
    SAT.tmVerifierFiniteBoolCertificateSymbols
        (V := knapsackStructuredFiniteTMVerifier) (fun b : Bool => some b) none bits =
      SAT.finiteAssignmentCertEncodedType.encode bits := by
  induction bits with
  | nil =>
      rfl
  | cons b bits ih =>
      change
        some b :: none ::
            SAT.tmVerifierFiniteBoolCertificateSymbols
              (V := knapsackStructuredFiniteTMVerifier) (fun b : Bool => some b) none bits =
          some b :: none :: SAT.finiteAssignmentCertEncodedType.encode bits
      rw [ih]

theorem knapsackStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols
    (bits : List Bool) :
    SAT.tmVerifierCertificateInputSuffixEncoded knapsackStructuredFiniteTMVerifier bits =
      (SAT.tmVerifierFiniteBoolCertificateSymbols
          (V := knapsackStructuredFiniteTMVerifier)
          (fun b : Bool => some b) none bits).map (fun s => some (Sum.inr s)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded, knapsackStructuredFiniteTMVerifier,
    TMKarpReduction.pullbackVerifier, knapsackBinaryStructuredFiniteTMVerifier,
    Knapsack.knapsackBinaryCertificateEncodedType] using
      congrArg
        (fun xs : List SAT.finiteAssignmentCertEncodedType.Symbol =>
          xs.map (fun s =>
            (some (Sum.inr s) :
              (SAT.tmVerifierInputEncodedType knapsackStructuredFiniteTMVerifier).Symbol)))
        (knapsackStructuredFiniteBoolCertificateSymbols_eq_encode bits).symm

noncomputable def knapsackStructuredFiniteEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder knapsackStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofCertificateDecoder
    knapsackStructuredFiniteTMVerifier
    SAT.finiteAssignmentCertDecode
    (by
      intro symbols bits h
      exact SAT.finiteAssignmentCertDecode_sound h)
    SAT.finiteAssignmentCertDecode_complete

noncomputable def knapsackStructuredFiniteCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder knapsackStructuredFiniteTMVerifier :=
  SAT.tmVerifierFiniteBoolCheckedSuffixDecoder
    knapsackStructuredFiniteTMVerifier
    (fun b : Bool => some b) none
    knapsackStructuredFiniteEncodedSuffixDecoder
    (fun bits : List Bool => bits)
    (fun bits : List Bool => bits)
    (by
      intro bits
      exact knapsackStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols bits)
    (by
      intro bits
      exact knapsackStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols bits)

theorem knapsackStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder knapsackStructuredDecisionProblem :=
  ⟨⟨knapsackStructuredFiniteTMVerifier,
      knapsackStructuredFiniteCheckedSuffixDecoder⟩⟩

end Karp21
end ComplexityReduction
