/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.FiniteWitness
import ComplexityReduction.Certificate.CheckedDecoderDiscipline
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.TMEncodingDisciplineTemplates
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactEncodedSuffixDecodersTM

/-!
Checked-decoder infrastructure for the canonical `List Nat` finite witness.
The helper fixes the witness presentation before constructing a verifier, so
the native discipline remains indexed by that exact verifier and cannot be
reused at a different witness encoding.
-/

namespace ComplexityReduction.Agent.Hardness.FiniteWitnessNative

open ComplexityReduction
open ComplexityReduction.Encoding
open ComplexityReduction.Certificate
open ComplexityReduction.Program
open ComplexityReduction.Agent.Hardness.FiniteWitness

/-- Verifier data with the canonical `List Nat` witness fixed in the type. -/
structure NatListVerifierData (problem : PresentedProblem) where
  checker : PolyProg
    (StandardInstances.prod problem.representation natListPresentation)
    StandardInstances.bool
  witnessBound : problem.Instance → Nat
  witnessBoundPoly : ComplexityReduction.PolynomialTimeBound
    (fun input => problem.representation.encodedType.inputSize input) witnessBound
  correct : ∀ input, problem.accepts input ↔
    ∃ candidate : List Nat,
      natListPresentation.encodedType.inputSize candidate ≤ witnessBound input ∧
        checker.run (input, candidate) = true
  checkerSound : ∀ input (candidate : List Nat),
    checker.run (input, candidate) = true → problem.accepts input

namespace NatListVerifierData

/-- Close the exact certified verifier without allowing a second witness representation. -/
def toCertifiedVerifier {problem : PresentedProblem}
    (data : NatListVerifierData problem) : CertifiedVerifier problem where
  witness := natListPresentation
  checker := data.checker
  witnessBound := data.witnessBound
  witnessBoundPoly := data.witnessBoundPoly
  correct := data.correct
  checkerSound := data.checkerSound

end NatListVerifierData

private def natListEncodingEntry (n : Nat) : List (Option Bool) :=
  (ComplexityReduction.EncodedType.nat.encode n).map some ++ [none]

private theorem natListEncodingEntry_eq_symbols (n : Nat) :
    natListEncodingEntry n =
      List.replicate n (some true) ++ [some false, none] := by
  simpa only [natListEncodingEntry, ComplexityReduction.EncodedType.nat,
    List.map_append, List.map_replicate, List.map_cons, List.map_nil] using
    List.append_assoc (List.replicate n (some true)) [some false] [none]

private theorem natList_encode_cons (n : Nat) (xs : List Nat) :
    (show List (Option Bool) from natListPresentation.encodedType.encode (n :: xs)) =
      natListEncodingEntry n ++
        (show List (Option Bool) from natListPresentation.encodedType.encode xs) := by
  simp [natListEncodingEntry, natListPresentation,
    ComplexityReduction.EncodedType.list]
  exact (List.append_assoc
    (List.map some (ComplexityReduction.EncodedType.nat.encode n))
    ([none] : List (Option Bool))
    (List.flatMap
      (fun x => List.map some (ComplexityReduction.EncodedType.nat.encode x) ++ [none]) xs)).symm

/-- Exact x-only suffix decoder obtained from the lawful nat-list encoding. -/
noncomputable def encodedSuffixDecoder {problem : PresentedProblem}
    (data : NatListVerifierData problem) :
    ComplexityReduction.SAT.TMVerifierXOnlyEncodedSuffixDecoder
      data.toCertifiedVerifier.toTMVerifier :=
  ComplexityReduction.SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofInjectiveCertificateEncoding
    data.toCertifiedVerifier.toTMVerifier
    natListPresentation.faithful.encode_injective

theorem natListCertificateSymbols_eq_encode {problem : PresentedProblem}
    (data : NatListVerifierData problem) (xs : List Nat) :
    ComplexityReduction.SAT.tmVerifierNatListCertificateSymbols
      (V := data.toCertifiedVerifier.toTMVerifier) (some true) (some false) none xs =
      natListPresentation.encodedType.encode xs := by
  induction xs with
  | nil => rfl
  | cons n xs ih =>
      rw [ComplexityReduction.SAT.tmVerifierNatListCertificateSymbols_cons, ih]
      exact (congrArg
        (fun symbols : List (Option Bool) =>
          symbols ++
            (show List (Option Bool) from natListPresentation.encodedType.encode xs))
        (natListEncodingEntry_eq_symbols n).symm).trans
        (natList_encode_cons n xs).symm

theorem certificateInputSuffixEncoded_eq_natListSymbols
    {problem : PresentedProblem} (data : NatListVerifierData problem) (xs : List Nat) :
    ComplexityReduction.SAT.tmVerifierCertificateInputSuffixEncoded
        data.toCertifiedVerifier.toTMVerifier xs =
      (ComplexityReduction.SAT.tmVerifierNatListCertificateSymbols
        (V := data.toCertifiedVerifier.toTMVerifier) (some true) (some false) none xs).map
        (ComplexityReduction.SAT.tmVerifierInputRightSymbol
          (V := data.toCertifiedVerifier.toTMVerifier)) := by
  simpa [ComplexityReduction.SAT.tmVerifierCertificateInputSuffixEncoded,
    NatListVerifierData.toCertifiedVerifier, natListPresentation,
    CertifiedVerifier.toTMVerifier] using
    congrArg
      (fun symbols : List natListPresentation.encodedType.Symbol =>
        symbols.map (fun symbol =>
          (some (Sum.inr symbol) :
            (ComplexityReduction.SAT.tmVerifierInputEncodedType
              data.toCertifiedVerifier.toTMVerifier).Symbol)))
      (natListCertificateSymbols_eq_encode data xs).symm

/-- Checked native encoding discipline for the exact nat-list verifier. -/
noncomputable def discipline {problem : PresentedProblem}
    (data : NatListVerifierData problem) :
    CertifiedVerifierEncodingDiscipline data.toCertifiedVerifier :=
  CheckedDecoderNativeDiscipline.ofBackend
    (ComplexityReduction.SAT.TMVerifierEncodingDiscipline.ofNatListCertificate
      data.toCertifiedVerifier.toTMVerifier
      (some true) (some false) none
      (by intro equality; cases equality)
      (by intro equality; cases equality)
      (by intro equality; cases equality)
      (encodedSuffixDecoder data)
      (fun xs : List Nat => xs)
      (fun xs : List Nat => xs)
      (certificateInputSuffixEncoded_eq_natListSymbols data)
      (certificateInputSuffixEncoded_eq_natListSymbols data))

end ComplexityReduction.Agent.Hardness.FiniteWitnessNative
