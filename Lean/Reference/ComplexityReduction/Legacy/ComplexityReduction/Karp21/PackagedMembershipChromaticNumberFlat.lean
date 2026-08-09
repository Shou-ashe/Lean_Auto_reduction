/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipChromaticNumber
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.NatListSplitTM

/-!
Alternative unary nat-list certificate verifier for faithful structured
Chromatic Number.

The existing verifier uses a pair of nat lists: colors for declared vertices
and fallback colors for raw edge endpoints outside the declared vertex range.
This file flattens the pair into a single nat list, split at `graph.vertices`,
so the checked nat-list suffix CNF can cover the certificate encoding directly.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace ChromaticNumber

abbrev chromaticFlatCertificateEncodedType : EncodedType :=
  setStructuredEncodedType

def chromaticFlatCertificatePair
    (I : ChromaticNumberInput) (xs : List Nat) : ChromaticCertificate :=
  NatListSplit.split (I.graph.vertices, xs)

def chromaticNumberFlatStructuredFiniteVerify
    (I : ChromaticNumberInput) (xs : List Nat) : Bool :=
  chromaticNumberStructuredFiniteVerify I (chromaticFlatCertificatePair I xs)

theorem chromaticFlatCertificatePair_eq_splitAt
    (I : ChromaticNumberInput) (xs : List Nat) :
    chromaticFlatCertificatePair I xs =
      (xs.take I.graph.vertices, xs.drop I.graph.vertices) := by
  simpa [chromaticFlatCertificatePair] using
    NatListSplit.split_eq_splitAt I.graph.vertices xs

def flatCertificateOfColoring
    (I : ChromaticNumberInput) (colorOf : Nat → Nat) : List Nat :=
  boundedColorTable I colorOf ++ edgeColorTable I colorOf

theorem chromaticFlatCertificatePair_flatCertificateOfColoring
    (I : ChromaticNumberInput) (colorOf : Nat → Nat) :
    chromaticFlatCertificatePair I (flatCertificateOfColoring I colorOf) =
      certificateOfColoring I colorOf := by
  rw [chromaticFlatCertificatePair_eq_splitAt]
  have hLen : (boundedColorTable I colorOf).length = I.graph.vertices := by
    simp [boundedColorTable]
  simp [flatCertificateOfColoring, certificateOfColoring, hLen]

theorem chromaticNumberFlatStructuredFiniteVerify_complete
    (I : ChromaticNumberInput) {colorOf : Nat → Nat}
    (hProper : ProperColoring I.graph I.colors colorOf) :
    chromaticNumberFlatStructuredFiniteVerify I (flatCertificateOfColoring I colorOf) = true := by
  rw [chromaticNumberFlatStructuredFiniteVerify,
    chromaticFlatCertificatePair_flatCertificateOfColoring]
  exact chromaticNumberStructuredFiniteVerify_complete I hProper

theorem chromaticNumberFlatStructuredFiniteVerify_sound
    (I : ChromaticNumberInput) (xs : List Nat)
    (hVerify : chromaticNumberFlatStructuredFiniteVerify I xs = true) :
    ChromaticNumber I := by
  exact chromaticNumberStructuredFiniteVerify_sound I (chromaticFlatCertificatePair I xs) hVerify

theorem flatCertificateOfColoring_inputSize_le_poly
    (I : ChromaticNumberInput) (colorOf : Nat → Nat)
    (hProper : ProperColoring I.graph I.colors colorOf) :
    chromaticFlatCertificateEncodedType.inputSize (flatCertificateOfColoring I colorOf) ≤
      20 * (chromaticNumberStructuredEncodedType.inputSize I) ^ 3 + 100 := by
  have hAppend :
      chromaticFlatCertificateEncodedType.inputSize (flatCertificateOfColoring I colorOf) =
        setStructuredEncodedType.inputSize (boundedColorTable I colorOf) +
          setStructuredEncodedType.inputSize (edgeColorTable I colorOf) := by
    simpa [chromaticFlatCertificateEncodedType, flatCertificateOfColoring,
      setStructuredEncodedType] using
      Clique.encodedList_inputSize_append EncodedType.nat
        (boundedColorTable I colorOf) (edgeColorTable I colorOf)
  have hPair :
      setStructuredEncodedType.inputSize (boundedColorTable I colorOf) +
          setStructuredEncodedType.inputSize (edgeColorTable I colorOf) ≤
        chromaticCertificateEncodedType.inputSize (certificateOfColoring I colorOf) := by
    simp [chromaticCertificateEncodedType, certificateOfColoring,
      EncodedType.inputSize_prod]
  calc
    chromaticFlatCertificateEncodedType.inputSize (flatCertificateOfColoring I colorOf)
        =
          setStructuredEncodedType.inputSize (boundedColorTable I colorOf) +
            setStructuredEncodedType.inputSize (edgeColorTable I colorOf) := hAppend
    _ ≤ chromaticCertificateEncodedType.inputSize (certificateOfColoring I colorOf) := hPair
    _ ≤ 20 * (chromaticNumberStructuredEncodedType.inputSize I) ^ 3 + 100 :=
      certificateOfColoring_inputSize_le_poly I colorOf hProper

theorem chromaticNumberFlatStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod chromaticNumberStructuredEncodedType chromaticFlatCertificateEncodedType)
      EncodedType.bool
      (fun p : ChromaticNumberInput × List Nat =>
        chromaticNumberFlatStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod chromaticNumberStructuredEncodedType chromaticFlatCertificateEncodedType
  have hInstance :
      TMPolyTimeMap X chromaticNumberStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, chromaticFlatCertificateEncodedType] using
      TMPolyTimeMap.fst chromaticNumberStructuredEncodedType setStructuredEncodedType
  have hCert :
      TMPolyTimeMap X chromaticFlatCertificateEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, chromaticFlatCertificateEncodedType] using
      TMPolyTimeMap.snd chromaticNumberStructuredEncodedType setStructuredEncodedType
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType (fun p : X.Carrier => p.1.graph) := by
    have hComp := TMPolyTimeMap.comp chromaticNumberGraphTMBackedMap.tm_polytime hInstance
    simpa [Function.comp, X] using hComp
  have hVertices :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp graphVerticesTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hSplitInput :
      TMPolyTimeMap X NatListSplit.inputEncodedType
        (fun p : X.Carrier => (p.1.graph.vertices, p.2)) := by
    have hPair :
        TMPolyTimeMap X (EncodedType.prod EncodedType.nat setStructuredEncodedType)
          (fun p : X.Carrier => (p.1.graph.vertices, p.2)) :=
      TMPolyTimeMap.prod_mk hVertices hCert
    simpa [NatListSplit.inputEncodedType, EncodedListLookup.inputEncodedType,
      chromaticFlatCertificateEncodedType, setStructuredEncodedType] using hPair
  have hPair :
      TMPolyTimeMap X NatListSplit.outputEncodedType
        (fun p : X.Carrier => chromaticFlatCertificatePair p.1 p.2) := by
    have hComp := TMPolyTimeMap.comp NatListSplit.split_tm_polytime hSplitInput
    simpa [Function.comp, chromaticFlatCertificatePair, NatListSplit.outputEncodedType]
      using hComp
  have hVerifyInput :
      TMPolyTimeMap X
        (EncodedType.prod chromaticNumberStructuredEncodedType chromaticCertificateEncodedType)
        (fun p : X.Carrier => (p.1, chromaticFlatCertificatePair p.1 p.2)) :=
    TMPolyTimeMap.prod_mk hInstance hPair
  have hComp := TMPolyTimeMap.comp chromaticNumberStructuredFiniteVerify_tm_polytime
    hVerifyInput
  simpa [Function.comp, chromaticNumberFlatStructuredFiniteVerify,
    chromaticFlatCertificateEncodedType, X] using hComp

end ChromaticNumber

/--
Alternative direct finite-certificate TM verifier for faithful structured
Chromatic Number whose certificate is one unary nat list.
-/
noncomputable def chromaticNumberFlatStructuredFiniteTMVerifier :
    TMVerifier chromaticNumberStructuredDecisionProblem where
  Cert := ChromaticNumber.chromaticFlatCertificateEncodedType
  verify := ChromaticNumber.chromaticNumberFlatStructuredFiniteVerify
  verifier_polytime :=
    ChromaticNumber.chromaticNumberFlatStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨3, 20, 100, ?_⟩
    intro I hYes
    rcases hYes with ⟨colorOf, hProper⟩
    refine ⟨ChromaticNumber.flatCertificateOfColoring I colorOf, ?_, ?_⟩
    · exact ChromaticNumber.flatCertificateOfColoring_inputSize_le_poly I colorOf hProper
    · exact ChromaticNumber.chromaticNumberFlatStructuredFiniteVerify_complete I hProper
  sound := by
    intro I xs hVerify
    exact ChromaticNumber.chromaticNumberFlatStructuredFiniteVerify_sound I xs hVerify

theorem chromaticNumberStructured_TMInNP_flat :
    TMInNP chromaticNumberStructuredDecisionProblem :=
  TMInNP.intro chromaticNumberFlatStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
