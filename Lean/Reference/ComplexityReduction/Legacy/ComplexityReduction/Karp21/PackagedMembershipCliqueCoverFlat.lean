/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipChromaticNumberFlat
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipCliqueCover

/-!
Alternative unary nat-list certificate verifier for faithful structured Clique
Cover.

This is the flat-certificate analogue of `cliqueCoverStructuredFiniteTMVerifier`:
it maps the instance to the complement Chromatic Number instance and then uses
the flat Chromatic verifier, so the checked nat-list suffix CNF can cover the
certificate encoding directly.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace CliqueCover

noncomputable def cliqueCoverFlatStructuredFiniteVerify
    (I : CliqueCoverInput) (xs : List Nat) : Bool :=
  ChromaticNumber.chromaticNumberFlatStructuredFiniteVerify (complementChromaticInput I) xs

theorem cliqueCoverFlatStructuredFiniteVerify_sound
    (I : CliqueCoverInput) (xs : List Nat) :
    cliqueCoverFlatStructuredFiniteVerify I xs = true → CliqueCover I := by
  intro hVerify
  exact (cliqueCover_iff_complementChromaticInput I).2
    (ChromaticNumber.chromaticNumberFlatStructuredFiniteVerify_sound
      (complementChromaticInput I) xs hVerify)

theorem cliqueCoverFlatStructuredFiniteVerify_complete
    (I : CliqueCoverInput) {colorOf : Nat → Nat}
    (hProper : ProperColoring (complementChromaticInput I).graph
      (complementChromaticInput I).colors colorOf) :
    cliqueCoverFlatStructuredFiniteVerify I
      (ChromaticNumber.flatCertificateOfColoring (complementChromaticInput I) colorOf) =
        true := by
  exact ChromaticNumber.chromaticNumberFlatStructuredFiniteVerify_complete
    (complementChromaticInput I) hProper

theorem cliqueCoverFlatStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod cliqueCoverStructuredEncodedType
        ChromaticNumber.chromaticFlatCertificateEncodedType)
      EncodedType.bool
      (fun p : CliqueCoverInput × List Nat =>
        cliqueCoverFlatStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod cliqueCoverStructuredEncodedType
    ChromaticNumber.chromaticFlatCertificateEncodedType
  have hInstance :
      TMPolyTimeMap X cliqueCoverStructuredEncodedType
        (fun p : X.Carrier => p.1) := by
    simpa [X, ChromaticNumber.chromaticFlatCertificateEncodedType] using
      TMPolyTimeMap.fst cliqueCoverStructuredEncodedType setStructuredEncodedType
  have hCert :
      TMPolyTimeMap X ChromaticNumber.chromaticFlatCertificateEncodedType
        (fun p : X.Carrier => p.2) := by
    simpa [X, ChromaticNumber.chromaticFlatCertificateEncodedType] using
      TMPolyTimeMap.snd cliqueCoverStructuredEncodedType setStructuredEncodedType
  have hMapped :
      TMPolyTimeMap X chromaticNumberStructuredEncodedType
        (fun p : X.Carrier => complementChromaticInput p.1) := by
    have hComp := TMPolyTimeMap.comp complementChromaticInput_tm_polytime hInstance
    simpa [Function.comp, X] using hComp
  have hInput :
      TMPolyTimeMap X
        (EncodedType.prod chromaticNumberStructuredEncodedType
          ChromaticNumber.chromaticFlatCertificateEncodedType)
        (fun p : X.Carrier => (complementChromaticInput p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hMapped hCert
  have hComp := TMPolyTimeMap.comp
    ChromaticNumber.chromaticNumberFlatStructuredFiniteVerify_tm_polytime hInput
  simpa [Function.comp, cliqueCoverFlatStructuredFiniteVerify, X] using hComp

theorem cliqueCoverFlatCertificate_inputSize_le_poly
    (I : CliqueCoverInput) (colorOf : Nat → Nat)
    (hProper : ProperColoring (complementChromaticInput I).graph
      (complementChromaticInput I).colors colorOf) :
    ChromaticNumber.chromaticFlatCertificateEncodedType.inputSize
        (ChromaticNumber.flatCertificateOfColoring (complementChromaticInput I) colorOf) ≤
      160000000000 * (cliqueCoverStructuredEncodedType.inputSize I) ^ 9 + 100 := by
  let C := chromaticNumberStructuredEncodedType.inputSize (complementChromaticInput I)
  let S := cliqueCoverStructuredEncodedType.inputSize I
  have hCert := ChromaticNumber.flatCertificateOfColoring_inputSize_le_poly
    (complementChromaticInput I) colorOf hProper
  have hCBase : C ≤ 1000 * S ^ 3 + 1000 := by
    simpa [C, S] using complementChromaticInput_inputSize_le_cliqueCover_poly I
  have hSpos : 1 ≤ S := by
    simp [S, cliqueCoverStructured_inputSize_eq]
  have hC : C ≤ 2000 * S ^ 3 := by
    calc
      C ≤ 1000 * S ^ 3 + 1000 := hCBase
      _ ≤ 1000 * S ^ 3 + 1000 * S ^ 3 := by
            have hPow : 1 ≤ S ^ 3 := Nat.pow_le_pow_left hSpos 3
            have hThousand : 1000 ≤ 1000 * S ^ 3 := by
              exact Nat.mul_le_mul_left 1000 hPow
            omega
      _ = 2000 * S ^ 3 := by ring
  calc
    ChromaticNumber.chromaticFlatCertificateEncodedType.inputSize
        (ChromaticNumber.flatCertificateOfColoring (complementChromaticInput I) colorOf)
        ≤ 20 * C ^ 3 + 100 := by simpa [C] using hCert
    _ ≤ 20 * (2000 * S ^ 3) ^ 3 + 100 := by
          exact Nat.add_le_add_right
            (Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left hC 3)) 100
    _ = 160000000000 * S ^ 9 + 100 := by ring

end CliqueCover

/--
Alternative direct finite-certificate TM verifier for faithful structured
Clique Cover whose certificate is one unary nat list.
-/
noncomputable def cliqueCoverFlatStructuredFiniteTMVerifier :
    TMVerifier cliqueCoverStructuredDecisionProblem where
  Cert := ChromaticNumber.chromaticFlatCertificateEncodedType
  verify := CliqueCover.cliqueCoverFlatStructuredFiniteVerify
  verifier_polytime := CliqueCover.cliqueCoverFlatStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨9, 160000000000, 100, ?_⟩
    intro I hYes
    rcases (CliqueCover.cliqueCover_iff_complementChromaticInput I).1 hYes with
      ⟨colorOf, hProper⟩
    refine ⟨
      ChromaticNumber.flatCertificateOfColoring
        (CliqueCover.complementChromaticInput I) colorOf, ?_, ?_⟩
    · exact CliqueCover.cliqueCoverFlatCertificate_inputSize_le_poly I colorOf hProper
    · exact CliqueCover.cliqueCoverFlatStructuredFiniteVerify_complete I hProper
  sound := by
    intro I xs hVerify
    exact CliqueCover.cliqueCoverFlatStructuredFiniteVerify_sound I xs hVerify

theorem cliqueCoverStructured_TMInNP_flat :
    TMInNP cliqueCoverStructuredDecisionProblem :=
  TMInNP.intro cliqueCoverFlatStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
