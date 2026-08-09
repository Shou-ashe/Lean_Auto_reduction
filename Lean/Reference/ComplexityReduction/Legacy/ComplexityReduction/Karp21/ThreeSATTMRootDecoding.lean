/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeSATTMRoot
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeSATSuffixDecoderTM
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMRootStandard
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyCheckedSuffixDecoderTM

/-!
Language-level package for the decoder-shaped raw-suffix normalizer.

`TMVerifierXOnlyRawSuffixDecodingNormalizer` splits the remaining x-only
Cook-Levin obligation into an encoded certificate-suffix decoder and a
machine-specific accepting-run decode proof.  This file exposes the same split
at the NP-package/root layer, without deriving it from ordinary `TMInNP`.
-/

namespace ComplexityReduction
namespace SAT

/--
A language has an NP verifier equipped with a checked suffix CNF that proves
membership in an explicit encoded certificate-suffix decoder.
-/
def TMInNPWithCheckedSuffixDecoder (L : EncodedDecisionProblem) : Prop :=
  Nonempty (Σ V : TMVerifier L, TMVerifierXOnlyCheckedSuffixDecoder V)

namespace TMInNPWithCheckedSuffixDecoder

/-- Forgetting the checked-decoder package recovers ordinary direct TM `NP`. -/
theorem toTMInNP {L : EncodedDecisionProblem}
    (h : TMInNPWithCheckedSuffixDecoder L) : TMInNP L := by
  rcases h with ⟨⟨V, _G⟩⟩
  exact ⟨V⟩

/-- A checked-decoder package supplies the existing checked suffix-validity package. -/
noncomputable def toCheckedSuffixValidity {L : EncodedDecisionProblem}
    (h : TMInNPWithCheckedSuffixDecoder L) : TMInNPWithCheckedSuffixValidity L := by
  rcases h with ⟨⟨V, G⟩⟩
  exact ⟨⟨V, G.toCheckedSuffixValidity⟩⟩

/-- A checked decoder is exactly the current standard-TM encoding discipline package. -/
theorem toEncodingDiscipline {L : EncodedDecisionProblem}
    (h : TMInNPWithCheckedSuffixDecoder L) : TMInNPWithEncodingDiscipline L := by
  rcases h with ⟨⟨V, G⟩⟩
  exact ⟨⟨V, TMVerifierEncodingDiscipline.ofCheckedSuffixDecoder G⟩⟩

end TMInNPWithCheckedSuffixDecoder

namespace TMInNPWithEncodingDiscipline

/-- Forget encoding discipline to the older checked-suffix-decoder package. -/
theorem toCheckedSuffixDecoder {L : EncodedDecisionProblem}
    (h : TMInNPWithEncodingDiscipline L) : TMInNPWithCheckedSuffixDecoder L := by
  rcases h with ⟨⟨V, D⟩⟩
  exact ⟨⟨V, D.toCheckedSuffixDecoder⟩⟩

end TMInNPWithEncodingDiscipline

/-! ### 3SAT checked-decoder witnesses -/

/--
Faithful structured 3SAT has a direct finite verifier equipped with the checked
finite-Boolean suffix decoder package.
-/
theorem threeSATStructured_TMInNPWithCheckedSuffixDecoder :
    TMInNPWithCheckedSuffixDecoder Karp21.threeSATStructuredDecisionProblem :=
  ⟨⟨threeSATStructuredFiniteTMVerifier, threeSATStructuredFiniteCheckedSuffixDecoder⟩⟩

/-- Faithful structured 3SAT carries the standard-TM encoding discipline package. -/
theorem threeSATStructured_TMInNPWithEncodingDiscipline :
    TMInNPWithEncodingDiscipline Karp21.threeSATStructuredDecisionProblem :=
  threeSATStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

/--
Historical bundled 3SAT has a direct finite verifier equipped with the checked
finite-Boolean suffix decoder package.
-/
theorem threeSAT_TMInNPWithCheckedSuffixDecoder :
    TMInNPWithCheckedSuffixDecoder threeSATDecisionProblem :=
  ⟨⟨threeSATFiniteTMVerifier, threeSATFiniteCheckedSuffixDecoder⟩⟩

/-- Historical bundled 3SAT carries the standard-TM encoding discipline package. -/
theorem threeSAT_TMInNPWithEncodingDiscipline :
    TMInNPWithEncodingDiscipline threeSATDecisionProblem :=
  threeSAT_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

/--
Bundled 3SAT is ordinary direct-TM `NP` and hard for the class of direct-TM NP
languages carrying a checked suffix CNF tied to an explicit suffix decoder.
-/
def TMNPCompleteEncWithCheckedSuffixDecoder
    (K : EncodedDecisionProblem) : Prop :=
  TMInNP K ∧ ∀ L, TMInNPWithCheckedSuffixDecoder L → TMPolyReducible L K

namespace TMNPCompleteEncWithCheckedSuffixDecoder

theorem mem_np {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithCheckedSuffixDecoder K) : TMInNP K :=
  h.1

theorem hard {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithCheckedSuffixDecoder K)
    (L : EncodedDecisionProblem) (hL : TMInNPWithCheckedSuffixDecoder L) :
    TMPolyReducible L K :=
  h.2 L hL

/--
Transfer checked-decoder packaged NP-completeness along a direct TM many-one
reduction.  The target membership hypothesis remains explicit.
-/
theorem transfer {A B : EncodedDecisionProblem}
    (hA : TMNPCompleteEncWithCheckedSuffixDecoder A)
    (hAB : TMPolyReducible A B)
    (hB : TMInNP B) :
    TMNPCompleteEncWithCheckedSuffixDecoder B := by
  constructor
  · exact hB
  · intro L hL
    exact TMPolyReducible.trans (hA.hard L hL) hAB

/-- Checked-decoder hardness is the same as encoding-discipline hardness. -/
theorem toEncodingDiscipline {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithCheckedSuffixDecoder K) :
    TMNPCompleteEncWithEncodingDiscipline K := by
  constructor
  · exact h.mem_np
  · intro L hL
    exact h.hard L hL.toCheckedSuffixDecoder

end TMNPCompleteEncWithCheckedSuffixDecoder

namespace TMNPCompleteEncWithEncodingDiscipline

/-- Encoding-discipline hardness can be used by checked-decoder callers. -/
theorem toCheckedSuffixDecoder {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithEncodingDiscipline K) :
    TMNPCompleteEncWithCheckedSuffixDecoder K := by
  constructor
  · exact h.mem_np
  · intro L hL
    exact h.hard L hL.toEncodingDiscipline

end TMNPCompleteEncWithEncodingDiscipline

namespace TMNPCompleteEncWithCheckedSuffixValidity

/--
Checked-suffix-validity hardness covers the stronger checked-decoder package,
because a checked decoder forgets to ordinary checked suffix validity.
-/
theorem toCheckedSuffixDecoder {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithCheckedSuffixValidity K) :
    TMNPCompleteEncWithCheckedSuffixDecoder K := by
  constructor
  · exact h.mem_np
  · intro L hL
    exact h.hard L hL.toCheckedSuffixValidity

end TMNPCompleteEncWithCheckedSuffixValidity

/-! ### Language-level package for decoder-shaped raw-suffix normalizers -/

/--
A language has an NP verifier equipped with the decoder-shaped raw-suffix
normalizer: an encoded certificate-suffix decoder plus the machine-specific
proof that every accepting raw suffix run is accepted by that decoder.
-/
def TMInNPWithRawSuffixDecodingNormalizer (L : EncodedDecisionProblem) : Prop :=
  Nonempty (Σ V : TMVerifier L, TMVerifierXOnlyRawSuffixDecodingNormalizer V)

namespace TMInNPWithRawSuffixDecodingNormalizer

/-- Forgetting the decoding-normalizer package recovers ordinary direct TM `NP`. -/
theorem toTMInNP {L : EncodedDecisionProblem}
    (h : TMInNPWithRawSuffixDecodingNormalizer L) : TMInNP L := by
  rcases h with ⟨⟨V, _D⟩⟩
  exact ⟨V⟩

/-- A decoding normalizer supplies the existing raw-suffix normalizer package. -/
def toRawSuffixNormalizer {L : EncodedDecisionProblem}
    (h : TMInNPWithRawSuffixDecodingNormalizer L) : TMInNPWithRawSuffixNormalizer L := by
  rcases h with ⟨⟨V, D⟩⟩
  exact ⟨⟨V, D.toRawSuffixNormalizer⟩⟩

/-- A decoding normalizer is in particular raw-input normalizing. -/
def toRawInputNormalizer {L : EncodedDecisionProblem}
    (h : TMInNPWithRawSuffixDecodingNormalizer L) : TMInNPWithRawInputNormalizer L :=
  h.toRawSuffixNormalizer.toRawInputNormalizer

/-- A decoding normalizer is in particular raw-input sound. -/
def toRawInputSound {L : EncodedDecisionProblem}
    (h : TMInNPWithRawSuffixDecodingNormalizer L) : TMInNPWithRawInputSound L :=
  h.toRawSuffixNormalizer.toRawInputSound

/--
A decoding normalizer also supplies the checked-decoder package using the same
encoded suffix decoder and the empty suffix CNF.
-/
noncomputable def toCheckedSuffixDecoder {L : EncodedDecisionProblem}
    (h : TMInNPWithRawSuffixDecodingNormalizer L) : TMInNPWithCheckedSuffixDecoder L := by
  rcases h with ⟨⟨V, D⟩⟩
  exact ⟨⟨V, D.toCheckedSuffixDecoder⟩⟩

/--
A decoding normalizer also supplies checked suffix validity through the
raw-suffix normalizer bridge.
-/
noncomputable def toCheckedSuffixValidity {L : EncodedDecisionProblem}
    (h : TMInNPWithRawSuffixDecodingNormalizer L) : TMInNPWithCheckedSuffixValidity L :=
  h.toRawSuffixNormalizer.toCheckedSuffixValidity

end TMInNPWithRawSuffixDecodingNormalizer

/--
Bundled 3SAT is ordinary direct-TM `NP` and hard for the class of direct-TM NP
languages carrying an explicit decoder-shaped raw-suffix normalizer.
-/
def TMNPCompleteEncWithRawSuffixDecodingNormalizer
    (K : EncodedDecisionProblem) : Prop :=
  TMInNP K ∧ ∀ L, TMInNPWithRawSuffixDecodingNormalizer L → TMPolyReducible L K

namespace TMNPCompleteEncWithRawSuffixDecodingNormalizer

theorem mem_np {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithRawSuffixDecodingNormalizer K) : TMInNP K :=
  h.1

theorem hard {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithRawSuffixDecodingNormalizer K)
    (L : EncodedDecisionProblem) (hL : TMInNPWithRawSuffixDecodingNormalizer L) :
    TMPolyReducible L K :=
  h.2 L hL

/--
Transfer decoding-normalizer packaged NP-completeness along a direct TM many-one
reduction.  The target membership hypothesis remains explicit.
-/
theorem transfer {A B : EncodedDecisionProblem}
    (hA : TMNPCompleteEncWithRawSuffixDecodingNormalizer A)
    (hAB : TMPolyReducible A B)
    (hB : TMInNP B) :
    TMNPCompleteEncWithRawSuffixDecodingNormalizer B := by
  constructor
  · exact hB
  · intro L hL
    exact TMPolyReducible.trans (hA.hard L hL) hAB

end TMNPCompleteEncWithRawSuffixDecodingNormalizer

namespace TMNPCompleteEncWithCheckedSuffixValidity

/--
Checked-suffix-validity hardness covers decoder-shaped raw-suffix normalizers,
because such a normalizer supplies checked suffix validity.
-/
theorem toRawSuffixDecodingNormalizer {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithCheckedSuffixValidity K) :
    TMNPCompleteEncWithRawSuffixDecodingNormalizer K := by
  constructor
  · exact h.mem_np
  · intro L hL
    exact h.hard L hL.toCheckedSuffixValidity

end TMNPCompleteEncWithCheckedSuffixValidity

namespace TMNPCompleteEncWithRawInputSound

/--
Raw-input-sound hardness covers decoder-shaped raw-suffix normalizers, since
those normalizers are raw-input sound.
-/
theorem toRawSuffixDecodingNormalizer {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithRawInputSound K) :
    TMNPCompleteEncWithRawSuffixDecodingNormalizer K := by
  constructor
  · exact h.mem_np
  · intro L hL
    exact h.hard L hL.toRawInputSound

end TMNPCompleteEncWithRawInputSound

namespace TMNPCompleteEncWithRawInputNormalizer

/--
Raw-input-normalizer hardness covers decoder-shaped raw-suffix normalizers,
since those normalizers recover raw-input normalizers.
-/
theorem toRawSuffixDecodingNormalizer {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithRawInputNormalizer K) :
    TMNPCompleteEncWithRawSuffixDecodingNormalizer K := by
  constructor
  · exact h.mem_np
  · intro L hL
    exact h.hard L hL.toRawInputNormalizer

end TMNPCompleteEncWithRawInputNormalizer

namespace TMNPCompleteEncWithCheckedSuffixDecoder

/--
Checked-decoder hardness covers decoder-shaped raw-suffix normalizers, because
the latter package supplies the checked-decoder witness with the same decoder.
-/
theorem toRawSuffixDecodingNormalizer {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithCheckedSuffixDecoder K) :
    TMNPCompleteEncWithRawSuffixDecodingNormalizer K := by
  constructor
  · exact h.mem_np
  · intro L hL
    exact h.hard L hL.toCheckedSuffixDecoder

end TMNPCompleteEncWithCheckedSuffixDecoder

namespace TMNPCompleteEncWithRawSuffixNormalizer

/--
Raw-suffix-normalizer hardness covers the narrower decoder-shaped package,
since a decoding normalizer converts to a raw-suffix normalizer.
-/
theorem toRawSuffixDecodingNormalizer {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithRawSuffixNormalizer K) :
    TMNPCompleteEncWithRawSuffixDecodingNormalizer K := by
  constructor
  · exact h.mem_np
  · intro L hL
    exact h.hard L hL.toRawSuffixNormalizer

end TMNPCompleteEncWithRawSuffixNormalizer

/--
If every direct-TM NP language admits some decoder-shaped raw-suffix-normalizing
verifier, bundled 3SAT is standard-TM NP-complete through the suffix route.
-/
theorem threeSAT_TMNPComplete_of_rawXOnlySuffixDecodingNormalizer_witnessed
    (hNormalize :
      {L : EncodedDecisionProblem} →
        TMInNP L → TMInNPWithRawSuffixDecodingNormalizer L) :
    TMNPCompleteEnc threeSATDecisionProblem :=
  threeSAT_TMNPComplete_of_rawXOnlySuffixNormalizer_witnessed
    (fun hL => (hNormalize hL).toRawSuffixNormalizer)

/--
The existing raw-suffix Cook-Levin route gives an unconditional complete root
for the explicitly packaged decoder-shaped raw-suffix NP class.
-/
theorem threeSAT_TMNPComplete_with_rawSuffixDecodingNormalizer :
    TMNPCompleteEncWithRawSuffixDecodingNormalizer threeSATDecisionProblem :=
  threeSAT_TMNPComplete_with_rawSuffixNormalizer.toRawSuffixDecodingNormalizer

/--
The existing checked Cook-Levin route gives an unconditional complete root for
the explicitly packaged checked-decoder NP class.
-/
theorem threeSAT_TMNPComplete_with_checkedSuffixDecoder :
    TMNPCompleteEncWithCheckedSuffixDecoder threeSATDecisionProblem :=
  threeSAT_TMNPComplete_with_checkedSuffixValidity.toCheckedSuffixDecoder

/--
Bundled 3SAT is complete for the standard-TM encoding-discipline NP class.
-/
theorem threeSAT_TMNPComplete_with_encodingDiscipline_from_checkedDecoder :
    TMNPCompleteEncWithEncodingDiscipline threeSATDecisionProblem :=
  threeSAT_TMNPComplete_with_checkedSuffixDecoder.toEncodingDiscipline

/--
Faithful structured 3SAT is ordinary direct-TM `NP` and hard for the explicitly
packaged decoder-shaped raw-suffix NP class.
-/
theorem threeSATStructured_TMNPComplete_with_rawSuffixDecodingNormalizer :
    TMNPCompleteEncWithRawSuffixDecodingNormalizer
      Karp21.threeSATStructuredDecisionProblem :=
  threeSATStructured_TMNPComplete_with_rawSuffixNormalizer.toRawSuffixDecodingNormalizer

/--
Faithful structured 3SAT is ordinary direct-TM `NP` and hard for the explicitly
packaged checked-decoder NP class.
-/
theorem threeSATStructured_TMNPComplete_with_checkedSuffixDecoder :
    TMNPCompleteEncWithCheckedSuffixDecoder
      Karp21.threeSATStructuredDecisionProblem :=
  threeSATStructured_TMNPComplete_with_checkedSuffixValidity.toCheckedSuffixDecoder

/--
Faithful structured 3SAT is complete for the standard-TM encoding-discipline
NP class.
-/
theorem threeSATStructured_TMNPComplete_with_encodingDiscipline :
    TMNPCompleteEncWithEncodingDiscipline Karp21.threeSATStructuredDecisionProblem :=
  threeSATStructured_TMNPComplete_with_checkedSuffixDecoder.toEncodingDiscipline

#check TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline
#check TMInNPWithEncodingDiscipline.toCheckedSuffixDecoder
#check threeSATStructured_TMInNPWithEncodingDiscipline
#check threeSAT_TMInNPWithEncodingDiscipline
#check TMNPCompleteEncWithCheckedSuffixDecoder.toEncodingDiscipline
#check TMNPCompleteEncWithEncodingDiscipline.toCheckedSuffixDecoder
#check threeSAT_TMNPComplete_with_encodingDiscipline_from_checkedDecoder
#check threeSATStructured_TMNPComplete_with_encodingDiscipline

end SAT
end ComplexityReduction
