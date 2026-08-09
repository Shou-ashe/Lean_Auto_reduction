/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.TMPolyTime

namespace ComplexityReduction

namespace EncodedLanguage

/-- The string-language view has the same predicate after conversion to a problem. -/
@[simp] theorem toProblem_isYes (L : EncodedLanguage) (w : List L.Alphabet) :
    L.toProblem.isYes w ↔ L.accepts w :=
  Iff.rfl

/--
Converting a finite-alphabet language to an encoded problem and back preserves
the accepted strings.
-/
@[simp] theorem toProblem_toEncodedLanguage_accepts
    (L : EncodedLanguage) (w : List L.Alphabet) :
    L.toProblem.toEncodedLanguage.accepts w ↔ L.accepts w := by
  constructor
  · rintro ⟨x, hx, hxYes⟩
    have hx' : x = w := by
      simpa [EncodedLanguage.toProblem, EncodedType.ofAlphabet] using hx
    simpa [hx'] using hxYes
  · intro hw
    exact ⟨w, rfl, hw⟩

end EncodedLanguage

namespace EncodedDecisionProblem

/--
The image language of an encoded decision problem accepts exactly strings that
are encodings of yes instances.
-/
@[simp] theorem toEncodedLanguage_accepts_iff
    (L : EncodedDecisionProblem) (w : List L.Instance.Symbol) :
    L.toEncodedLanguage.accepts w ↔ ∃ x, L.Instance.encode x = w ∧ L.isYes x :=
  Iff.rfl

/--
A problem predicate respects its encoding when equal encodings cannot change
yes/no status.
-/
def PredicateRespectsEncoding (L : EncodedDecisionProblem) : Prop :=
  ∀ ⦃x y : L.Instance.Carrier⦄,
    L.Instance.encode x = L.Instance.encode y → (L.isYes x ↔ L.isYes y)

/-- A faithful instance encoding separates distinct formal instances. -/
structure FaithfulEncoding (L : EncodedDecisionProblem) where
  injective : Function.Injective L.Instance.encode

/-- A concrete witness that the encoding collapses two different formal instances. -/
def EncodingCollision (L : EncodedDecisionProblem) : Prop :=
  ∃ x y : L.Instance.Carrier, x ≠ y ∧ L.Instance.encode x = L.Instance.encode y

/-- A faithful encoding is enough to make the predicate respect encodings. -/
theorem FaithfulEncoding.predicateRespects {L : EncodedDecisionProblem}
    (h : L.FaithfulEncoding) : L.PredicateRespectsEncoding := by
  intro x y hxy
  have hEq : x = y := h.injective hxy
  subst hEq
  exact Iff.rfl

/-- Encoding collisions rule out faithful encodings. -/
theorem EncodingCollision.not_faithful {L : EncodedDecisionProblem}
    (h : L.EncodingCollision) : ¬ L.FaithfulEncoding := by
  rintro ⟨hinj⟩
  rcases h with ⟨x, y, hne, henc⟩
  exact hne (hinj henc)

/--
Under predicate-respecting encodings, the image language reflects yes status on
encoded instances.
-/
theorem toEncodedLanguage_accepts_encode_iff_of_respectsEncoding
    (L : EncodedDecisionProblem) (hL : L.PredicateRespectsEncoding)
    (x : L.Instance.Carrier) :
    L.toEncodedLanguage.accepts (L.Instance.encode x) ↔ L.isYes x := by
  constructor
  · rintro ⟨y, hyEnc, hyYes⟩
    exact (hL hyEnc).1 hyYes
  · intro hx
    exact L.accepts_encode_of_yes hx

/--
Injective encodings are a sufficient condition for the image language to reflect
yes status on encoded instances.
-/
theorem toEncodedLanguage_accepts_encode_iff_of_injective
    (L : EncodedDecisionProblem) (hL : Function.Injective L.Instance.encode)
    (x : L.Instance.Carrier) :
    L.toEncodedLanguage.accepts (L.Instance.encode x) ↔ L.isYes x := by
  refine L.toEncodedLanguage_accepts_encode_iff_of_respectsEncoding ?_ x
  intro y z hyz
  have hyz' : y = z := hL hyz
  subst hyz'
  exact Iff.rfl

/-- Faithful encodings reflect yes status on encoded instances. -/
theorem FaithfulEncoding.toEncodedLanguage_accepts_encode_iff
    {L : EncodedDecisionProblem} (h : L.FaithfulEncoding) (x : L.Instance.Carrier) :
    L.toEncodedLanguage.accepts (L.Instance.encode x) ↔ L.isYes x :=
  L.toEncodedLanguage_accepts_encode_iff_of_respectsEncoding h.predicateRespects x

end EncodedDecisionProblem

/-- A deterministic polynomial-time TM2 decider for an encoded decision problem. -/
structure TMPolyTimeDecider (L : EncodedDecisionProblem) where
  decide : L.Instance.Carrier → Bool
  polytime : TMPolyTimeMap L.Instance EncodedType.bool decide
  correct : ∀ x, decide x = true ↔ L.isYes x

/-- Deterministic polynomial time using mathlib's finite-control TM2 model. -/
def TMInP (L : EncodedDecisionProblem) : Prop :=
  Nonempty (TMPolyTimeDecider L)

namespace TMInP

/-- Build direct TM `P` membership from an explicit TM2 polynomial-time decider. -/
theorem intro {L : EncodedDecisionProblem} (decide : L.Instance.Carrier → Bool)
    (hPoly : TMPolyTimeMap L.Instance EncodedType.bool decide)
    (hCorrect : ∀ x, decide x = true ↔ L.isYes x) :
    TMInP L :=
  ⟨{ decide := decide, polytime := hPoly, correct := hCorrect }⟩

end TMInP

/-- A polynomial-time TM2 verifier with polynomially bounded certificates. -/
structure TMVerifier (L : EncodedDecisionProblem) where
  Cert : EncodedType
  verify : L.Instance.Carrier → Cert.Carrier → Bool
  verifier_polytime :
    TMPolyTimeMap (EncodedType.prod L.Instance Cert) EncodedType.bool
      (fun p => verify p.1 p.2)
  cert_bound :
    ∃ degree coeff const : Nat,
      ∀ x, L.isYes x →
        ∃ c, Cert.inputSize c ≤
          coeff * (L.Instance.inputSize x) ^ degree + const ∧
          verify x c = true
  sound : ∀ x c, verify x c = true → L.isYes x

namespace TMVerifier

/-- A TM verifier is semantically correct after forgetting the size bound. -/
theorem correct_iff {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) :
    L.isYes x ↔ ∃ c, V.verify x c = true := by
  constructor
  · intro hx
    rcases V.cert_bound with ⟨degree, coeff, const, hBound⟩
    rcases hBound x hx with ⟨c, _hSize, hVerify⟩
    exact ⟨c, hVerify⟩
  · rintro ⟨c, hVerify⟩
    exact V.sound x c hVerify

end TMVerifier

/-- Nondeterministic polynomial time using direct TM2 verifier semantics. -/
def TMInNP (L : EncodedDecisionProblem) : Prop :=
  Nonempty (TMVerifier L)

namespace TMInNP

/-- Build direct TM `NP` membership from an explicit TM2 verifier. -/
theorem intro {L : EncodedDecisionProblem} (V : TMVerifier L) : TMInNP L :=
  ⟨V⟩

end TMInNP

/-- TM2-semantics encoded NP-completeness. -/
def TMNPCompleteEnc (L : EncodedDecisionProblem) : Prop :=
  TMInNP L ∧ ∀ L', TMInNP L' → TMPolyReducible L' L

namespace TMNPCompleteEnc

theorem mem_np {L : EncodedDecisionProblem} (h : TMNPCompleteEnc L) : TMInNP L :=
  h.1

theorem hard {L : EncodedDecisionProblem} (h : TMNPCompleteEnc L)
    (L' : EncodedDecisionProblem) (hL' : TMInNP L') : TMPolyReducible L' L :=
  h.2 L' hL'

end TMNPCompleteEnc

end ComplexityReduction
