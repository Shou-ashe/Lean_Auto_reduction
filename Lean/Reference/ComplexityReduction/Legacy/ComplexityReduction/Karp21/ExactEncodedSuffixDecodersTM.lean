/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipClique
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipCliqueCover
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipCliqueCoverFlat
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipChromaticNumberFlat
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipDirectedHamiltonianCircuit
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipExactCover
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipFeedbackArcSet
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipFeedbackArcSetFlat
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetPacking
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSteinerTree
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSteinerTreeFlat
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipFeedbackNodeSetFlat
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipThreeDimensionalMatching
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipThreeDimensionalMatchingIndex
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipUndirectedHamiltonianCircuit
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeSATTMRootDecoding
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyNatListSuffixCompletenessTM
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyRawNormalizationTM

/-!
Exact encoded certificate-suffix decoders from injective certificate encodings.

This file supplies encoding-level suffix decoders, plus checked nat-list suffix
CNFs for the concrete Karp21 verifiers whose certificate encoding is exactly
the project nat-list/set encoding.  It does not construct raw accepting-run
normalizers or any conversion from ordinary `TMInNP` to a suffix-decoder
package.
-/

namespace ComplexityReduction

namespace EncodedType

/--
Noncomputable exact decoder for an encoded type with injective encoding.

This is a semantic inverse on the image of `X.encode`; no polynomial-time or
machine-level claim is attached to this decoder.
-/
noncomputable def exactDecodeOfInjective (X : EncodedType)
    (_hX : Function.Injective X.encode) :
    List X.Symbol → Option X.Carrier := by
  classical
  exact fun symbols =>
    if h : ∃ x : X.Carrier, X.encode x = symbols then
      some (Classical.choose h)
    else
      none

theorem exactDecodeOfInjective_complete (X : EncodedType)
    (hX : Function.Injective X.encode) (x : X.Carrier) :
    exactDecodeOfInjective X hX (X.encode x) = some x := by
  classical
  have hExists : ∃ y : X.Carrier, X.encode y = X.encode x := ⟨x, rfl⟩
  have hChoose : Classical.choose hExists = x :=
    hX (Classical.choose_spec hExists)
  simp [exactDecodeOfInjective, hExists, hChoose]

theorem exactDecodeOfInjective_sound (X : EncodedType)
    (hX : Function.Injective X.encode)
    {symbols : List X.Symbol} {x : X.Carrier}
    (hDecode : exactDecodeOfInjective X hX symbols = some x) :
    symbols = X.encode x := by
  classical
  by_cases hExists : ∃ y : X.Carrier, X.encode y = symbols
  · have hSome : some (Classical.choose hExists) = some x := by
      simpa [exactDecodeOfInjective, hExists] using hDecode
    have hChoose : Classical.choose hExists = x := Option.some.inj hSome
    have hSpec := Classical.choose_spec hExists
    rw [hChoose] at hSpec
    exact hSpec.symm
  · simp [exactDecodeOfInjective, hExists] at hDecode

end EncodedType

namespace SAT
namespace TMVerifierXOnlyEncodedSuffixDecoder

/--
Build an encoded suffix decoder from a proof that the certificate encoding is
injective.  This is only a semantic exact decoder for well-formed certificate
suffix images.
-/
noncomputable def ofInjectiveCertificateEncoding
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (hCert : Function.Injective V.Cert.encode) :
    TMVerifierXOnlyEncodedSuffixDecoder V :=
  ofCertificateDecoder V
    (EncodedType.exactDecodeOfInjective V.Cert hCert)
    (by
      intro symbols c h
      exact EncodedType.exactDecodeOfInjective_sound V.Cert hCert h)
    (by
      intro c
      exact EncodedType.exactDecodeOfInjective_complete V.Cert hCert c)

end TMVerifierXOnlyEncodedSuffixDecoder
end SAT

namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-! ### Set-structured certificate decoders -/

noncomputable def hittingSetStructuredEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder hittingSetStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofInjectiveCertificateEncoding
    hittingSetStructuredFiniteTMVerifier
    setStructuredEncodedType_encode_injective

theorem hittingSetStructuredNatListCertificateSymbols_eq_encode (xs : List Nat) :
    SAT.tmVerifierNatListCertificateSymbols
        (V := hittingSetStructuredFiniteTMVerifier) (some true) (some false) none xs =
      setStructuredEncodedType.encode xs := by
  induction xs with
  | nil =>
      rfl
  | cons n xs ih =>
      rw [SAT.tmVerifierNatListCertificateSymbols_cons, ih]
      simp [setStructuredEncodedType, EncodedType.list, EncodedType.nat, List.map_append,
        List.map_replicate, List.append_assoc]
      rfl

theorem hittingSetStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    (xs : List Nat) :
    SAT.tmVerifierCertificateInputSuffixEncoded hittingSetStructuredFiniteTMVerifier xs =
      (SAT.tmVerifierNatListCertificateSymbols
          (V := hittingSetStructuredFiniteTMVerifier)
          (some true) (some false) none xs).map
        (SAT.tmVerifierInputRightSymbol (V := hittingSetStructuredFiniteTMVerifier)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded, hittingSetStructuredFiniteTMVerifier]
    using congrArg
      (fun syms : List setStructuredEncodedType.Symbol =>
        syms.map (fun s =>
          (some (Sum.inr s) :
            (SAT.tmVerifierInputEncodedType hittingSetStructuredFiniteTMVerifier).Symbol)))
      (hittingSetStructuredNatListCertificateSymbols_eq_encode xs).symm

noncomputable def hittingSetStructuredCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder hittingSetStructuredFiniteTMVerifier :=
    SAT.tmVerifierNatListCheckedSuffixDecoderComplete
    hittingSetStructuredFiniteTMVerifier
    (some true) (some false) none
    (by intro h; cases h)
    (by intro h; cases h)
    (by intro h; cases h)
    hittingSetStructuredEncodedSuffixDecoder
    (fun xs : List Nat => xs)
    (fun xs : List Nat => xs)
    hittingSetStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    hittingSetStructuredCertificateInputSuffixEncoded_eq_natListSymbols

theorem hittingSetStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder hittingSetStructuredDecisionProblem :=
  ⟨⟨hittingSetStructuredFiniteTMVerifier, hittingSetStructuredCheckedSuffixDecoder⟩⟩

noncomputable def setCoveringStructuredEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder setCoveringStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofInjectiveCertificateEncoding
    setCoveringStructuredFiniteTMVerifier
    setStructuredEncodedType_encode_injective

theorem setCoveringStructuredNatListCertificateSymbols_eq_encode (xs : List Nat) :
    SAT.tmVerifierNatListCertificateSymbols
        (V := setCoveringStructuredFiniteTMVerifier) (some true) (some false) none xs =
      setStructuredEncodedType.encode xs := by
  simpa [setCoveringStructuredFiniteTMVerifier] using
    hittingSetStructuredNatListCertificateSymbols_eq_encode xs

theorem setCoveringStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    (xs : List Nat) :
    SAT.tmVerifierCertificateInputSuffixEncoded setCoveringStructuredFiniteTMVerifier xs =
      (SAT.tmVerifierNatListCertificateSymbols
          (V := setCoveringStructuredFiniteTMVerifier)
          (some true) (some false) none xs).map
        (SAT.tmVerifierInputRightSymbol (V := setCoveringStructuredFiniteTMVerifier)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded, setCoveringStructuredFiniteTMVerifier]
    using congrArg
      (fun syms : List setStructuredEncodedType.Symbol =>
        syms.map (fun s =>
          (some (Sum.inr s) :
            (SAT.tmVerifierInputEncodedType setCoveringStructuredFiniteTMVerifier).Symbol)))
      (setCoveringStructuredNatListCertificateSymbols_eq_encode xs).symm

noncomputable def setCoveringStructuredCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder setCoveringStructuredFiniteTMVerifier :=
  SAT.tmVerifierNatListCheckedSuffixDecoderComplete
    setCoveringStructuredFiniteTMVerifier
    (some true) (some false) none
    (by intro h; cases h)
    (by intro h; cases h)
    (by intro h; cases h)
    setCoveringStructuredEncodedSuffixDecoder
    (fun xs : List Nat => xs)
    (fun xs : List Nat => xs)
    setCoveringStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    setCoveringStructuredCertificateInputSuffixEncoded_eq_natListSymbols

theorem setCoveringStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder setCoveringStructuredDecisionProblem :=
  ⟨⟨setCoveringStructuredFiniteTMVerifier, setCoveringStructuredCheckedSuffixDecoder⟩⟩

noncomputable def vertexCoverStructuredEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder vertexCoverStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofInjectiveCertificateEncoding
    vertexCoverStructuredFiniteTMVerifier
    setStructuredEncodedType_encode_injective

theorem vertexCoverStructuredNatListCertificateSymbols_eq_encode (xs : List Nat) :
    SAT.tmVerifierNatListCertificateSymbols
        (V := vertexCoverStructuredFiniteTMVerifier) (some true) (some false) none xs =
      setStructuredEncodedType.encode xs := by
  simpa [vertexCoverStructuredFiniteTMVerifier] using
    hittingSetStructuredNatListCertificateSymbols_eq_encode xs

theorem vertexCoverStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    (xs : List Nat) :
    SAT.tmVerifierCertificateInputSuffixEncoded vertexCoverStructuredFiniteTMVerifier xs =
      (SAT.tmVerifierNatListCertificateSymbols
          (V := vertexCoverStructuredFiniteTMVerifier)
          (some true) (some false) none xs).map
        (SAT.tmVerifierInputRightSymbol (V := vertexCoverStructuredFiniteTMVerifier)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded, vertexCoverStructuredFiniteTMVerifier]
    using congrArg
      (fun syms : List setStructuredEncodedType.Symbol =>
        syms.map (fun s =>
          (some (Sum.inr s) :
            (SAT.tmVerifierInputEncodedType vertexCoverStructuredFiniteTMVerifier).Symbol)))
      (vertexCoverStructuredNatListCertificateSymbols_eq_encode xs).symm

noncomputable def vertexCoverStructuredCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder vertexCoverStructuredFiniteTMVerifier :=
  SAT.tmVerifierNatListCheckedSuffixDecoderComplete
    vertexCoverStructuredFiniteTMVerifier
    (some true) (some false) none
    (by intro h; cases h)
    (by intro h; cases h)
    (by intro h; cases h)
    vertexCoverStructuredEncodedSuffixDecoder
    (fun xs : List Nat => xs)
    (fun xs : List Nat => xs)
    vertexCoverStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    vertexCoverStructuredCertificateInputSuffixEncoded_eq_natListSymbols

theorem vertexCoverStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder vertexCoverStructuredDecisionProblem :=
  ⟨⟨vertexCoverStructuredFiniteTMVerifier, vertexCoverStructuredCheckedSuffixDecoder⟩⟩

noncomputable def cliqueStructuredEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder cliqueStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofInjectiveCertificateEncoding
    cliqueStructuredFiniteTMVerifier
    setStructuredEncodedType_encode_injective

theorem cliqueStructuredNatListCertificateSymbols_eq_encode (xs : List Nat) :
    SAT.tmVerifierNatListCertificateSymbols
        (V := cliqueStructuredFiniteTMVerifier) (some true) (some false) none xs =
      setStructuredEncodedType.encode xs := by
  simpa [cliqueStructuredFiniteTMVerifier] using
    hittingSetStructuredNatListCertificateSymbols_eq_encode xs

theorem cliqueStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    (xs : List Nat) :
    SAT.tmVerifierCertificateInputSuffixEncoded cliqueStructuredFiniteTMVerifier xs =
      (SAT.tmVerifierNatListCertificateSymbols
          (V := cliqueStructuredFiniteTMVerifier)
          (some true) (some false) none xs).map
        (SAT.tmVerifierInputRightSymbol (V := cliqueStructuredFiniteTMVerifier)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded, cliqueStructuredFiniteTMVerifier]
    using congrArg
      (fun syms : List setStructuredEncodedType.Symbol =>
        syms.map (fun s =>
          (some (Sum.inr s) :
            (SAT.tmVerifierInputEncodedType cliqueStructuredFiniteTMVerifier).Symbol)))
      (cliqueStructuredNatListCertificateSymbols_eq_encode xs).symm

noncomputable def cliqueStructuredCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder cliqueStructuredFiniteTMVerifier :=
  SAT.tmVerifierNatListCheckedSuffixDecoderComplete
    cliqueStructuredFiniteTMVerifier
    (some true) (some false) none
    (by intro h; cases h)
    (by intro h; cases h)
    (by intro h; cases h)
    cliqueStructuredEncodedSuffixDecoder
    (fun xs : List Nat => xs)
    (fun xs : List Nat => xs)
    cliqueStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    cliqueStructuredCertificateInputSuffixEncoded_eq_natListSymbols

theorem cliqueStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder cliqueStructuredDecisionProblem :=
  ⟨⟨cliqueStructuredFiniteTMVerifier, cliqueStructuredCheckedSuffixDecoder⟩⟩

noncomputable def exactCoverStructuredEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder exactCoverStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofInjectiveCertificateEncoding
    exactCoverStructuredFiniteTMVerifier
    setStructuredEncodedType_encode_injective

theorem exactCoverStructuredNatListCertificateSymbols_eq_encode (xs : List Nat) :
    SAT.tmVerifierNatListCertificateSymbols
        (V := exactCoverStructuredFiniteTMVerifier) (some true) (some false) none xs =
      setStructuredEncodedType.encode xs := by
  simpa [exactCoverStructuredFiniteTMVerifier] using
    hittingSetStructuredNatListCertificateSymbols_eq_encode xs

theorem exactCoverStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    (xs : List Nat) :
    SAT.tmVerifierCertificateInputSuffixEncoded exactCoverStructuredFiniteTMVerifier xs =
      (SAT.tmVerifierNatListCertificateSymbols
          (V := exactCoverStructuredFiniteTMVerifier)
          (some true) (some false) none xs).map
        (SAT.tmVerifierInputRightSymbol (V := exactCoverStructuredFiniteTMVerifier)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded, exactCoverStructuredFiniteTMVerifier]
    using congrArg
      (fun syms : List setStructuredEncodedType.Symbol =>
        syms.map (fun s =>
          (some (Sum.inr s) :
            (SAT.tmVerifierInputEncodedType exactCoverStructuredFiniteTMVerifier).Symbol)))
      (exactCoverStructuredNatListCertificateSymbols_eq_encode xs).symm

noncomputable def exactCoverStructuredCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder exactCoverStructuredFiniteTMVerifier :=
  SAT.tmVerifierNatListCheckedSuffixDecoderComplete
    exactCoverStructuredFiniteTMVerifier
    (some true) (some false) none
    (by intro h; cases h)
    (by intro h; cases h)
    (by intro h; cases h)
    exactCoverStructuredEncodedSuffixDecoder
    (fun xs : List Nat => xs)
    (fun xs : List Nat => xs)
    exactCoverStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    exactCoverStructuredCertificateInputSuffixEncoded_eq_natListSymbols

theorem exactCoverStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder exactCoverStructuredDecisionProblem :=
  ⟨⟨exactCoverStructuredFiniteTMVerifier, exactCoverStructuredCheckedSuffixDecoder⟩⟩

/-! ### Set-family and triple-list certificate decoders -/

noncomputable def setPackingStructuredEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder setPackingStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofInjectiveCertificateEncoding
    setPackingStructuredFiniteTMVerifier
    setFamilyStructuredEncodedType_encode_injective

noncomputable def setPackingIndexStructuredEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder setPackingIndexStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofInjectiveCertificateEncoding
    setPackingIndexStructuredFiniteTMVerifier
    setStructuredEncodedType_encode_injective

theorem setPackingIndexStructuredNatListCertificateSymbols_eq_encode (xs : List Nat) :
    SAT.tmVerifierNatListCertificateSymbols
        (V := setPackingIndexStructuredFiniteTMVerifier) (some true) (some false) none xs =
      SetPackingMembership.setPackingIndexCertificateEncodedType.encode xs := by
  simpa [SetPackingMembership.setPackingIndexCertificateEncodedType,
    setPackingIndexStructuredFiniteTMVerifier] using
    hittingSetStructuredNatListCertificateSymbols_eq_encode xs

theorem setPackingIndexStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    (xs : List Nat) :
    SAT.tmVerifierCertificateInputSuffixEncoded setPackingIndexStructuredFiniteTMVerifier xs =
      (SAT.tmVerifierNatListCertificateSymbols
          (V := setPackingIndexStructuredFiniteTMVerifier)
          (some true) (some false) none xs).map
        (SAT.tmVerifierInputRightSymbol (V := setPackingIndexStructuredFiniteTMVerifier)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded,
    setPackingIndexStructuredFiniteTMVerifier,
    SetPackingMembership.setPackingIndexCertificateEncodedType]
    using congrArg
      (fun syms : List SetPackingMembership.setPackingIndexCertificateEncodedType.Symbol =>
        syms.map (fun s =>
          (some (Sum.inr s) :
            (SAT.tmVerifierInputEncodedType setPackingIndexStructuredFiniteTMVerifier).Symbol)))
      (setPackingIndexStructuredNatListCertificateSymbols_eq_encode xs).symm

noncomputable def setPackingStructuredCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder setPackingIndexStructuredFiniteTMVerifier :=
  SAT.tmVerifierNatListCheckedSuffixDecoderComplete
    setPackingIndexStructuredFiniteTMVerifier
    (some true) (some false) none
    (by intro h; cases h)
    (by intro h; cases h)
    (by intro h; cases h)
    setPackingIndexStructuredEncodedSuffixDecoder
    (fun xs : List Nat => xs)
    (fun xs : List Nat => xs)
    setPackingIndexStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    setPackingIndexStructuredCertificateInputSuffixEncoded_eq_natListSymbols

theorem setPackingStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder setPackingStructuredDecisionProblem :=
  ⟨⟨setPackingIndexStructuredFiniteTMVerifier,
      setPackingStructuredCheckedSuffixDecoder⟩⟩

noncomputable def threeDimensionalMatchingStructuredEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder
      threeDimensionalMatchingStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofInjectiveCertificateEncoding
    threeDimensionalMatchingStructuredFiniteTMVerifier
    tripleListStructuredEncodedType_encode_injective

noncomputable def threeDimensionalMatchingIndexStructuredEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder
      threeDimensionalMatchingIndexStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofInjectiveCertificateEncoding
    threeDimensionalMatchingIndexStructuredFiniteTMVerifier
    setStructuredEncodedType_encode_injective

theorem threeDimensionalMatchingIndexStructuredNatListCertificateSymbols_eq_encode
    (xs : List Nat) :
    SAT.tmVerifierNatListCertificateSymbols
        (V := threeDimensionalMatchingIndexStructuredFiniteTMVerifier)
        (some true) (some false) none xs =
      ThreeDimensionalMatchingMembership.threeDMIndexCertificateEncodedType.encode xs := by
  simpa [ThreeDimensionalMatchingMembership.threeDMIndexCertificateEncodedType,
    threeDimensionalMatchingIndexStructuredFiniteTMVerifier] using
    hittingSetStructuredNatListCertificateSymbols_eq_encode xs

theorem threeDimensionalMatchingIndexStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    (xs : List Nat) :
    SAT.tmVerifierCertificateInputSuffixEncoded
        threeDimensionalMatchingIndexStructuredFiniteTMVerifier xs =
      (SAT.tmVerifierNatListCertificateSymbols
          (V := threeDimensionalMatchingIndexStructuredFiniteTMVerifier)
          (some true) (some false) none xs).map
        (SAT.tmVerifierInputRightSymbol
          (V := threeDimensionalMatchingIndexStructuredFiniteTMVerifier)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded,
    threeDimensionalMatchingIndexStructuredFiniteTMVerifier,
    ThreeDimensionalMatchingMembership.threeDMIndexCertificateEncodedType]
    using congrArg
      (fun syms : List
          ThreeDimensionalMatchingMembership.threeDMIndexCertificateEncodedType.Symbol =>
        syms.map (fun s =>
          (some (Sum.inr s) :
            (SAT.tmVerifierInputEncodedType
              threeDimensionalMatchingIndexStructuredFiniteTMVerifier).Symbol)))
      (threeDimensionalMatchingIndexStructuredNatListCertificateSymbols_eq_encode xs).symm

noncomputable def threeDimensionalMatchingIndexStructuredCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder
      threeDimensionalMatchingIndexStructuredFiniteTMVerifier :=
  SAT.tmVerifierNatListCheckedSuffixDecoderComplete
    threeDimensionalMatchingIndexStructuredFiniteTMVerifier
    (some true) (some false) none
    (by intro h; cases h)
    (by intro h; cases h)
    (by intro h; cases h)
    threeDimensionalMatchingIndexStructuredEncodedSuffixDecoder
    (fun xs : List Nat => xs)
    (fun xs : List Nat => xs)
    threeDimensionalMatchingIndexStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    threeDimensionalMatchingIndexStructuredCertificateInputSuffixEncoded_eq_natListSymbols

theorem threeDimensionalMatchingStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder threeDimensionalMatchingStructuredDecisionProblem :=
  ⟨⟨threeDimensionalMatchingIndexStructuredFiniteTMVerifier,
      threeDimensionalMatchingIndexStructuredCheckedSuffixDecoder⟩⟩

/-! ### Hamiltonian-cycle certificate decoders -/

noncomputable def directedHamiltonianCircuitStructuredEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder
      directedHamiltonianCircuitStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofInjectiveCertificateEncoding
    directedHamiltonianCircuitStructuredFiniteTMVerifier
    setStructuredEncodedType_encode_injective

theorem directedHamiltonianCircuitStructuredNatListCertificateSymbols_eq_encode
    (xs : List Nat) :
    SAT.tmVerifierNatListCertificateSymbols
        (V := directedHamiltonianCircuitStructuredFiniteTMVerifier)
        (some true) (some false) none xs =
      DirectedHamiltonianCircuitMembership.directedHamiltonianCircuitCertificateEncodedType.encode
        xs := by
  simpa [DirectedHamiltonianCircuitMembership.directedHamiltonianCircuitCertificateEncodedType,
    directedHamiltonianCircuitStructuredFiniteTMVerifier] using
    hittingSetStructuredNatListCertificateSymbols_eq_encode xs

theorem directedHamiltonianCircuitStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    (xs : List Nat) :
    SAT.tmVerifierCertificateInputSuffixEncoded
        directedHamiltonianCircuitStructuredFiniteTMVerifier xs =
      (SAT.tmVerifierNatListCertificateSymbols
          (V := directedHamiltonianCircuitStructuredFiniteTMVerifier)
          (some true) (some false) none xs).map
        (SAT.tmVerifierInputRightSymbol
          (V := directedHamiltonianCircuitStructuredFiniteTMVerifier)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded,
    directedHamiltonianCircuitStructuredFiniteTMVerifier,
    DirectedHamiltonianCircuitMembership.directedHamiltonianCircuitCertificateEncodedType]
    using congrArg
      (fun syms : List
          DirectedHamiltonianCircuitMembership.directedHamiltonianCircuitCertificateEncodedType.Symbol =>
        syms.map (fun s =>
          (some (Sum.inr s) :
            (SAT.tmVerifierInputEncodedType
              directedHamiltonianCircuitStructuredFiniteTMVerifier).Symbol)))
      (directedHamiltonianCircuitStructuredNatListCertificateSymbols_eq_encode xs).symm

noncomputable def directedHamiltonianCircuitStructuredCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder
      directedHamiltonianCircuitStructuredFiniteTMVerifier :=
  SAT.tmVerifierNatListCheckedSuffixDecoderComplete
    directedHamiltonianCircuitStructuredFiniteTMVerifier
    (some true) (some false) none
    (by intro h; cases h)
    (by intro h; cases h)
    (by intro h; cases h)
    directedHamiltonianCircuitStructuredEncodedSuffixDecoder
    (fun xs : List Nat => xs)
    (fun xs : List Nat => xs)
    directedHamiltonianCircuitStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    directedHamiltonianCircuitStructuredCertificateInputSuffixEncoded_eq_natListSymbols

theorem directedHamiltonianCircuitStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder directedHamiltonianCircuitStructuredDecisionProblem :=
  ⟨⟨directedHamiltonianCircuitStructuredFiniteTMVerifier,
      directedHamiltonianCircuitStructuredCheckedSuffixDecoder⟩⟩

noncomputable def undirectedHamiltonianCircuitStructuredEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder
      undirectedHamiltonianCircuitStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofInjectiveCertificateEncoding
    undirectedHamiltonianCircuitStructuredFiniteTMVerifier
    setStructuredEncodedType_encode_injective

theorem undirectedHamiltonianCircuitStructuredNatListCertificateSymbols_eq_encode
    (xs : List Nat) :
    SAT.tmVerifierNatListCertificateSymbols
        (V := undirectedHamiltonianCircuitStructuredFiniteTMVerifier)
        (some true) (some false) none xs =
      UndirectedHamiltonianCircuitMembership.undirectedHamiltonianCircuitCertificateEncodedType.encode
        xs := by
  simpa [UndirectedHamiltonianCircuitMembership.undirectedHamiltonianCircuitCertificateEncodedType,
    undirectedHamiltonianCircuitStructuredFiniteTMVerifier] using
    hittingSetStructuredNatListCertificateSymbols_eq_encode xs

theorem undirectedHamiltonianCircuitStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    (xs : List Nat) :
    SAT.tmVerifierCertificateInputSuffixEncoded
        undirectedHamiltonianCircuitStructuredFiniteTMVerifier xs =
      (SAT.tmVerifierNatListCertificateSymbols
          (V := undirectedHamiltonianCircuitStructuredFiniteTMVerifier)
          (some true) (some false) none xs).map
        (SAT.tmVerifierInputRightSymbol
          (V := undirectedHamiltonianCircuitStructuredFiniteTMVerifier)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded,
    undirectedHamiltonianCircuitStructuredFiniteTMVerifier,
    UndirectedHamiltonianCircuitMembership.undirectedHamiltonianCircuitCertificateEncodedType]
    using congrArg
      (fun syms : List
          UndirectedHamiltonianCircuitMembership.undirectedHamiltonianCircuitCertificateEncodedType.Symbol =>
        syms.map (fun s =>
          (some (Sum.inr s) :
            (SAT.tmVerifierInputEncodedType
              undirectedHamiltonianCircuitStructuredFiniteTMVerifier).Symbol)))
      (undirectedHamiltonianCircuitStructuredNatListCertificateSymbols_eq_encode xs).symm

noncomputable def undirectedHamiltonianCircuitStructuredCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder
      undirectedHamiltonianCircuitStructuredFiniteTMVerifier :=
  SAT.tmVerifierNatListCheckedSuffixDecoderComplete
    undirectedHamiltonianCircuitStructuredFiniteTMVerifier
    (some true) (some false) none
    (by intro h; cases h)
    (by intro h; cases h)
    (by intro h; cases h)
    undirectedHamiltonianCircuitStructuredEncodedSuffixDecoder
    (fun xs : List Nat => xs)
    (fun xs : List Nat => xs)
    undirectedHamiltonianCircuitStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    undirectedHamiltonianCircuitStructuredCertificateInputSuffixEncoded_eq_natListSymbols

theorem undirectedHamiltonianCircuitStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder undirectedHamiltonianCircuitStructuredDecisionProblem :=
  ⟨⟨undirectedHamiltonianCircuitStructuredFiniteTMVerifier,
      undirectedHamiltonianCircuitStructuredCheckedSuffixDecoder⟩⟩

/-! ### Chromatic-style certificate decoders -/

namespace ChromaticNumber

theorem chromaticCertificateEncodedType_encode_injective :
    Function.Injective chromaticCertificateEncodedType.encode := by
  simpa [chromaticCertificateEncodedType] using
    EncodedType.prod_encode_injective
      setStructuredEncodedType_encode_injective
      setStructuredEncodedType_encode_injective

end ChromaticNumber

noncomputable def chromaticNumberStructuredEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder
      chromaticNumberStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofInjectiveCertificateEncoding
    chromaticNumberStructuredFiniteTMVerifier
    ChromaticNumber.chromaticCertificateEncodedType_encode_injective

noncomputable def chromaticNumberFlatStructuredEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder
      chromaticNumberFlatStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofInjectiveCertificateEncoding
    chromaticNumberFlatStructuredFiniteTMVerifier
    setStructuredEncodedType_encode_injective

theorem chromaticNumberFlatStructuredNatListCertificateSymbols_eq_encode
    (xs : List Nat) :
    SAT.tmVerifierNatListCertificateSymbols
        (V := chromaticNumberFlatStructuredFiniteTMVerifier)
        (some true) (some false) none xs =
      ChromaticNumber.chromaticFlatCertificateEncodedType.encode xs := by
  simpa [ChromaticNumber.chromaticFlatCertificateEncodedType,
    chromaticNumberFlatStructuredFiniteTMVerifier] using
    hittingSetStructuredNatListCertificateSymbols_eq_encode xs

theorem chromaticNumberFlatStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    (xs : List Nat) :
    SAT.tmVerifierCertificateInputSuffixEncoded
        chromaticNumberFlatStructuredFiniteTMVerifier xs =
      (SAT.tmVerifierNatListCertificateSymbols
          (V := chromaticNumberFlatStructuredFiniteTMVerifier)
          (some true) (some false) none xs).map
        (SAT.tmVerifierInputRightSymbol
          (V := chromaticNumberFlatStructuredFiniteTMVerifier)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded,
    chromaticNumberFlatStructuredFiniteTMVerifier,
    ChromaticNumber.chromaticFlatCertificateEncodedType]
    using congrArg
      (fun syms : List ChromaticNumber.chromaticFlatCertificateEncodedType.Symbol =>
        syms.map (fun s =>
          (some (Sum.inr s) :
            (SAT.tmVerifierInputEncodedType
              chromaticNumberFlatStructuredFiniteTMVerifier).Symbol)))
      (chromaticNumberFlatStructuredNatListCertificateSymbols_eq_encode xs).symm

noncomputable def chromaticNumberFlatStructuredCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder
      chromaticNumberFlatStructuredFiniteTMVerifier :=
  SAT.tmVerifierNatListCheckedSuffixDecoderComplete
    chromaticNumberFlatStructuredFiniteTMVerifier
    (some true) (some false) none
    (by intro h; cases h)
    (by intro h; cases h)
    (by intro h; cases h)
    chromaticNumberFlatStructuredEncodedSuffixDecoder
    (fun xs : List Nat => xs)
    (fun xs : List Nat => xs)
    chromaticNumberFlatStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    chromaticNumberFlatStructuredCertificateInputSuffixEncoded_eq_natListSymbols

theorem chromaticNumberStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder chromaticNumberStructuredDecisionProblem :=
  ⟨⟨chromaticNumberFlatStructuredFiniteTMVerifier,
      chromaticNumberFlatStructuredCheckedSuffixDecoder⟩⟩

noncomputable def cliqueCoverStructuredEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder cliqueCoverStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofInjectiveCertificateEncoding
    cliqueCoverStructuredFiniteTMVerifier
    ChromaticNumber.chromaticCertificateEncodedType_encode_injective

noncomputable def cliqueCoverFlatStructuredEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder
      cliqueCoverFlatStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofInjectiveCertificateEncoding
    cliqueCoverFlatStructuredFiniteTMVerifier
    setStructuredEncodedType_encode_injective

theorem cliqueCoverFlatStructuredNatListCertificateSymbols_eq_encode
    (xs : List Nat) :
    SAT.tmVerifierNatListCertificateSymbols
        (V := cliqueCoverFlatStructuredFiniteTMVerifier)
        (some true) (some false) none xs =
      ChromaticNumber.chromaticFlatCertificateEncodedType.encode xs := by
  simpa [ChromaticNumber.chromaticFlatCertificateEncodedType,
    cliqueCoverFlatStructuredFiniteTMVerifier] using
    hittingSetStructuredNatListCertificateSymbols_eq_encode xs

theorem cliqueCoverFlatStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    (xs : List Nat) :
    SAT.tmVerifierCertificateInputSuffixEncoded
        cliqueCoverFlatStructuredFiniteTMVerifier xs =
      (SAT.tmVerifierNatListCertificateSymbols
          (V := cliqueCoverFlatStructuredFiniteTMVerifier)
          (some true) (some false) none xs).map
        (SAT.tmVerifierInputRightSymbol
          (V := cliqueCoverFlatStructuredFiniteTMVerifier)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded,
    cliqueCoverFlatStructuredFiniteTMVerifier,
    ChromaticNumber.chromaticFlatCertificateEncodedType]
    using congrArg
      (fun syms : List ChromaticNumber.chromaticFlatCertificateEncodedType.Symbol =>
        syms.map (fun s =>
          (some (Sum.inr s) :
            (SAT.tmVerifierInputEncodedType
              cliqueCoverFlatStructuredFiniteTMVerifier).Symbol)))
      (cliqueCoverFlatStructuredNatListCertificateSymbols_eq_encode xs).symm

noncomputable def cliqueCoverFlatStructuredCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder
      cliqueCoverFlatStructuredFiniteTMVerifier :=
  SAT.tmVerifierNatListCheckedSuffixDecoderComplete
    cliqueCoverFlatStructuredFiniteTMVerifier
    (some true) (some false) none
    (by intro h; cases h)
    (by intro h; cases h)
    (by intro h; cases h)
    cliqueCoverFlatStructuredEncodedSuffixDecoder
    (fun xs : List Nat => xs)
    (fun xs : List Nat => xs)
    cliqueCoverFlatStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    cliqueCoverFlatStructuredCertificateInputSuffixEncoded_eq_natListSymbols

theorem cliqueCoverStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder cliqueCoverStructuredDecisionProblem :=
  ⟨⟨cliqueCoverFlatStructuredFiniteTMVerifier,
      cliqueCoverFlatStructuredCheckedSuffixDecoder⟩⟩

/-! ### Feedback-set certificate decoders -/

namespace FeedbackNodeSetMembership

theorem feedbackNodeSetCertificateEncodedType_encode_injective :
    Function.Injective feedbackNodeSetCertificateEncodedType.encode := by
  simpa [feedbackNodeSetCertificateEncodedType] using
    EncodedType.prod_encode_injective
      setStructuredEncodedType_encode_injective
      partitionWeightsStructuredEncodedType_encode_injective

end FeedbackNodeSetMembership

namespace FeedbackArcSetMembership

theorem feedbackArcSetCertificateEncodedType_encode_injective :
    Function.Injective feedbackArcSetCertificateEncodedType.encode := by
  simpa [feedbackArcSetCertificateEncodedType] using
    EncodedType.prod_encode_injective
      edgeListStructuredEncodedType_encode_injective
      partitionWeightsStructuredEncodedType_encode_injective

end FeedbackArcSetMembership

noncomputable def feedbackNodeSetStructuredEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder
      feedbackNodeSetStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofInjectiveCertificateEncoding
    feedbackNodeSetStructuredFiniteTMVerifier
    FeedbackNodeSetMembership.feedbackNodeSetCertificateEncodedType_encode_injective

noncomputable def feedbackNodeSetFlatStructuredEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder
      feedbackNodeSetFlatStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofInjectiveCertificateEncoding
    feedbackNodeSetFlatStructuredFiniteTMVerifier
    setStructuredEncodedType_encode_injective

theorem feedbackNodeSetFlatStructuredNatListCertificateSymbols_eq_encode
    (xs : List Nat) :
    SAT.tmVerifierNatListCertificateSymbols
        (V := feedbackNodeSetFlatStructuredFiniteTMVerifier)
        (some true) (some false) none xs =
      FeedbackNodeSetMembership.feedbackNodeSetFlatCertificateEncodedType.encode xs := by
  simpa [FeedbackNodeSetMembership.feedbackNodeSetFlatCertificateEncodedType,
    feedbackNodeSetFlatStructuredFiniteTMVerifier] using
    hittingSetStructuredNatListCertificateSymbols_eq_encode xs

theorem feedbackNodeSetFlatStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    (xs : List Nat) :
    SAT.tmVerifierCertificateInputSuffixEncoded
        feedbackNodeSetFlatStructuredFiniteTMVerifier xs =
      (SAT.tmVerifierNatListCertificateSymbols
          (V := feedbackNodeSetFlatStructuredFiniteTMVerifier)
          (some true) (some false) none xs).map
        (SAT.tmVerifierInputRightSymbol
          (V := feedbackNodeSetFlatStructuredFiniteTMVerifier)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded,
    feedbackNodeSetFlatStructuredFiniteTMVerifier,
    FeedbackNodeSetMembership.feedbackNodeSetFlatCertificateEncodedType]
    using congrArg
      (fun syms : List
          FeedbackNodeSetMembership.feedbackNodeSetFlatCertificateEncodedType.Symbol =>
        syms.map (fun s =>
          (some (Sum.inr s) :
            (SAT.tmVerifierInputEncodedType
              feedbackNodeSetFlatStructuredFiniteTMVerifier).Symbol)))
      (feedbackNodeSetFlatStructuredNatListCertificateSymbols_eq_encode xs).symm

noncomputable def feedbackNodeSetFlatStructuredCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder
      feedbackNodeSetFlatStructuredFiniteTMVerifier :=
  SAT.tmVerifierNatListCheckedSuffixDecoderComplete
    feedbackNodeSetFlatStructuredFiniteTMVerifier
    (some true) (some false) none
    (by intro h; cases h)
    (by intro h; cases h)
    (by intro h; cases h)
    feedbackNodeSetFlatStructuredEncodedSuffixDecoder
    (fun xs : List Nat => xs)
    (fun xs : List Nat => xs)
    feedbackNodeSetFlatStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    feedbackNodeSetFlatStructuredCertificateInputSuffixEncoded_eq_natListSymbols

theorem feedbackNodeSetStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder feedbackNodeSetStructuredDecisionProblem :=
  ⟨⟨feedbackNodeSetFlatStructuredFiniteTMVerifier,
      feedbackNodeSetFlatStructuredCheckedSuffixDecoder⟩⟩

noncomputable def feedbackArcSetStructuredEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder feedbackArcSetStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofInjectiveCertificateEncoding
    feedbackArcSetStructuredFiniteTMVerifier
    FeedbackArcSetMembership.feedbackArcSetCertificateEncodedType_encode_injective

noncomputable def feedbackArcSetFlatStructuredEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder
      feedbackArcSetFlatStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofInjectiveCertificateEncoding
    feedbackArcSetFlatStructuredFiniteTMVerifier
    setStructuredEncodedType_encode_injective

theorem feedbackArcSetFlatStructuredNatListCertificateSymbols_eq_encode
    (xs : List Nat) :
    SAT.tmVerifierNatListCertificateSymbols
        (V := feedbackArcSetFlatStructuredFiniteTMVerifier)
        (some true) (some false) none xs =
      FeedbackArcSetMembership.feedbackArcSetFlatCertificateEncodedType.encode xs := by
  simpa [FeedbackArcSetMembership.feedbackArcSetFlatCertificateEncodedType,
    feedbackArcSetFlatStructuredFiniteTMVerifier] using
    hittingSetStructuredNatListCertificateSymbols_eq_encode xs

theorem feedbackArcSetFlatStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    (xs : List Nat) :
    SAT.tmVerifierCertificateInputSuffixEncoded
        feedbackArcSetFlatStructuredFiniteTMVerifier xs =
      (SAT.tmVerifierNatListCertificateSymbols
          (V := feedbackArcSetFlatStructuredFiniteTMVerifier)
          (some true) (some false) none xs).map
        (SAT.tmVerifierInputRightSymbol
          (V := feedbackArcSetFlatStructuredFiniteTMVerifier)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded,
    feedbackArcSetFlatStructuredFiniteTMVerifier,
    FeedbackArcSetMembership.feedbackArcSetFlatCertificateEncodedType]
    using congrArg
      (fun syms : List
          FeedbackArcSetMembership.feedbackArcSetFlatCertificateEncodedType.Symbol =>
        syms.map (fun s =>
          (some (Sum.inr s) :
            (SAT.tmVerifierInputEncodedType
              feedbackArcSetFlatStructuredFiniteTMVerifier).Symbol)))
      (feedbackArcSetFlatStructuredNatListCertificateSymbols_eq_encode xs).symm

noncomputable def feedbackArcSetFlatStructuredCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder
      feedbackArcSetFlatStructuredFiniteTMVerifier :=
  SAT.tmVerifierNatListCheckedSuffixDecoderComplete
    feedbackArcSetFlatStructuredFiniteTMVerifier
    (some true) (some false) none
    (by intro h; cases h)
    (by intro h; cases h)
    (by intro h; cases h)
    feedbackArcSetFlatStructuredEncodedSuffixDecoder
    (fun xs : List Nat => xs)
    (fun xs : List Nat => xs)
    feedbackArcSetFlatStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    feedbackArcSetFlatStructuredCertificateInputSuffixEncoded_eq_natListSymbols

theorem feedbackArcSetStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder feedbackArcSetStructuredDecisionProblem :=
  ⟨⟨feedbackArcSetFlatStructuredFiniteTMVerifier,
      feedbackArcSetFlatStructuredCheckedSuffixDecoder⟩⟩

/-! ### Steiner Tree certificate decoder -/

namespace SteinerTreeMembership

theorem steinerPathEntryEncodedType_encode_injective :
    Function.Injective steinerPathEntryEncodedType.encode := by
  simpa [steinerPathEntryEncodedType] using
    EncodedType.prod_encode_injective
      EncodedType.nat_encode_injective
      (EncodedType.list_encode_injective EncodedType.nat_encode_injective)

theorem steinerPathEntryListEncodedType_encode_injective :
    Function.Injective steinerPathEntryListEncodedType.encode := by
  simpa [steinerPathEntryListEncodedType] using
    EncodedType.list_encode_injective steinerPathEntryEncodedType_encode_injective

theorem steinerTreeCertificateEncodedType_encode_injective :
    Function.Injective steinerTreeCertificateEncodedType.encode := by
  simpa [steinerTreeCertificateEncodedType] using
    EncodedType.prod_encode_injective
      EncodedType.nat_encode_injective
      (EncodedType.prod_encode_injective
        weightedEdgeListStructuredEncodedType_encode_injective
        steinerPathEntryListEncodedType_encode_injective)

end SteinerTreeMembership

noncomputable def steinerTreeStructuredEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder
      SteinerTreeMembership.steinerTreeStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofInjectiveCertificateEncoding
    SteinerTreeMembership.steinerTreeStructuredFiniteTMVerifier
    SteinerTreeMembership.steinerTreeCertificateEncodedType_encode_injective

noncomputable def steinerTreeFlatStructuredEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder
      steinerTreeFlatStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofInjectiveCertificateEncoding
    steinerTreeFlatStructuredFiniteTMVerifier
    setStructuredEncodedType_encode_injective

theorem steinerTreeFlatStructuredNatListCertificateSymbols_eq_encode
    (xs : List Nat) :
    SAT.tmVerifierNatListCertificateSymbols
        (V := steinerTreeFlatStructuredFiniteTMVerifier)
        (some true) (some false) none xs =
      SteinerTreeMembership.steinerTreeFlatCertificateEncodedType.encode xs := by
  simpa [SteinerTreeMembership.steinerTreeFlatCertificateEncodedType,
    steinerTreeFlatStructuredFiniteTMVerifier] using
    hittingSetStructuredNatListCertificateSymbols_eq_encode xs

theorem steinerTreeFlatStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    (xs : List Nat) :
    SAT.tmVerifierCertificateInputSuffixEncoded
        steinerTreeFlatStructuredFiniteTMVerifier xs =
      (SAT.tmVerifierNatListCertificateSymbols
          (V := steinerTreeFlatStructuredFiniteTMVerifier)
          (some true) (some false) none xs).map
        (SAT.tmVerifierInputRightSymbol
          (V := steinerTreeFlatStructuredFiniteTMVerifier)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded,
    steinerTreeFlatStructuredFiniteTMVerifier,
    SteinerTreeMembership.steinerTreeFlatCertificateEncodedType]
    using congrArg
      (fun syms : List
          SteinerTreeMembership.steinerTreeFlatCertificateEncodedType.Symbol =>
        syms.map (fun s =>
          (some (Sum.inr s) :
            (SAT.tmVerifierInputEncodedType
              steinerTreeFlatStructuredFiniteTMVerifier).Symbol)))
      (steinerTreeFlatStructuredNatListCertificateSymbols_eq_encode xs).symm

noncomputable def steinerTreeFlatStructuredCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder
      steinerTreeFlatStructuredFiniteTMVerifier :=
  SAT.tmVerifierNatListCheckedSuffixDecoderComplete
    steinerTreeFlatStructuredFiniteTMVerifier
    (some true) (some false) none
    (by intro h; cases h)
    (by intro h; cases h)
    (by intro h; cases h)
    steinerTreeFlatStructuredEncodedSuffixDecoder
    (fun xs : List Nat => xs)
    (fun xs : List Nat => xs)
    steinerTreeFlatStructuredCertificateInputSuffixEncoded_eq_natListSymbols
    steinerTreeFlatStructuredCertificateInputSuffixEncoded_eq_natListSymbols

theorem steinerTreeStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder steinerTreeStructuredDecisionProblem :=
  ⟨⟨steinerTreeFlatStructuredFiniteTMVerifier,
      steinerTreeFlatStructuredCheckedSuffixDecoder⟩⟩

end Karp21
end ComplexityReduction
