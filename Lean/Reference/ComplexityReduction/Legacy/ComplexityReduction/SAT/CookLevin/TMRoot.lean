/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.TMComplexityClasses
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin

/-!
Standard-TM Cook-Levin root boundary.

This file does not prove Cook-Levin for arbitrary `TMVerifier`s.  It records the
direct theorem surface that such a proof must inhabit, keeping it separate from
the project-local `CostedPolyTimeModel` Cook-Levin theorem.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Extracting the concrete verifier-machine witness -/

/-- Encoded input type for a direct `TMVerifier`: an instance paired with a certificate. -/
abbrev tmVerifierInputEncodedType {L : EncodedDecisionProblem} (V : TMVerifier L) :
    EncodedType :=
  EncodedType.prod L.Instance V.Cert

/--
Choose the concrete mathlib TM2 polynomial-time witness carried by a
`TMVerifier`'s `verifier_polytime` field.
-/
noncomputable def tmVerifierComputableWitness {L : EncodedDecisionProblem}
    (V : TMVerifier L) :
    Turing.TM2ComputableInPolyTime
      (tmVerifierInputEncodedType V).encode
      EncodedType.bool.encode
      (fun p : L.Instance.Carrier × V.Cert.Carrier => V.verify p.1 p.2) :=
  Classical.choice V.verifier_polytime

/-- The extracted verifier machine has exactly the output guaranteed by `verifier_polytime`. -/
noncomputable def tmVerifierComputableWitness_outputs {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) :
    Turing.TM2OutputsInTime (tmVerifierComputableWitness V).tm
      (List.map (tmVerifierComputableWitness V).inputAlphabet.invFun
        ((tmVerifierInputEncodedType V).encode p))
      (some (List.map (tmVerifierComputableWitness V).outputAlphabet.invFun
        (EncodedType.bool.encode (V.verify p.1 p.2))))
      ((tmVerifierComputableWitness V).time.eval
        (((tmVerifierInputEncodedType V).encode p).length)) :=
  (tmVerifierComputableWitness V).outputsFun p

/-- If the verifier accepts, the extracted machine outputs the encoding of `true`. -/
noncomputable def tmVerifierComputableWitness_outputs_true_of_verify_eq_true
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (h : V.verify x c = true) :
    Turing.TM2OutputsInTime (tmVerifierComputableWitness V).tm
      (List.map (tmVerifierComputableWitness V).inputAlphabet.invFun
        ((tmVerifierInputEncodedType V).encode (x, c)))
      (some (List.map (tmVerifierComputableWitness V).outputAlphabet.invFun
        (EncodedType.bool.encode true)))
      ((tmVerifierComputableWitness V).time.eval
        (((tmVerifierInputEncodedType V).encode (x, c)).length)) := by
  simpa [h] using tmVerifierComputableWitness_outputs V (x, c)

/-- If the verifier rejects, the extracted machine outputs the encoding of `false`. -/
noncomputable def tmVerifierComputableWitness_outputs_false_of_verify_eq_false
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (h : V.verify x c = false) :
    Turing.TM2OutputsInTime (tmVerifierComputableWitness V).tm
      (List.map (tmVerifierComputableWitness V).inputAlphabet.invFun
        ((tmVerifierInputEncodedType V).encode (x, c)))
      (some (List.map (tmVerifierComputableWitness V).outputAlphabet.invFun
        (EncodedType.bool.encode false)))
      ((tmVerifierComputableWitness V).time.eval
        (((tmVerifierInputEncodedType V).encode (x, c)).length)) := by
  simpa [h] using tmVerifierComputableWitness_outputs V (x, c)

/--
Direct standard-TM Cook-Levin output for one `TMVerifier`.

The polynomial-time field is a direct `TMPolyTimeMap`; it is intentionally not a
`CostedPolyTimeModel` or `CostedTMSound` transport.
-/
structure TMCookLevinVerifierReduction {L : EncodedDecisionProblem}
    (V : TMVerifier L) where
  cookTableauThreeCNF : L.Instance.Carrier → ThreeCNF
  cookTableauThreeCNF_polytime :
    TMPolyTimeMap L.Instance threeSATDecisionProblem.Instance cookTableauThreeCNF
  cookTableauThreeCNF_correct :
    ∀ x, L.isYes x ↔ ThreeCNF.Satisfiable (cookTableauThreeCNF x)

namespace TMCookLevinVerifierReduction

/-- View a direct TM Cook-Levin verifier reduction as a direct TM Karp reduction. -/
def toTMKarpReduction {L : EncodedDecisionProblem} {V : TMVerifier L}
    (R : TMCookLevinVerifierReduction V) :
    TMKarpReduction L threeSATDecisionProblem where
  f := R.cookTableauThreeCNF
  polytime := R.cookTableauThreeCNF_polytime
  correct := R.cookTableauThreeCNF_correct

end TMCookLevinVerifierReduction

/--
The missing standard-TM Cook-Levin root theorem as an explicit proof object.

A value of this structure must reduce every concrete direct `TMVerifier` to
bundled 3SAT by a direct TM polynomial-time map.
-/
structure TMCookLevinTheorem where
  reduceVerifier :
    {L : EncodedDecisionProblem} →
      (V : TMVerifier L) → TMCookLevinVerifierReduction V

namespace TMCookLevinTheorem

/-- A supplied TM Cook-Levin theorem reduces one explicit verifier to bundled 3SAT. -/
theorem reduction_of_TMVerifier (H : TMCookLevinTheorem)
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyReducible L threeSATDecisionProblem :=
  ⟨(H.reduceVerifier V).toTMKarpReduction⟩

/-- A supplied TM Cook-Levin theorem reduces every direct-TM NP problem to bundled 3SAT. -/
theorem reduction_of_TMInNP (H : TMCookLevinTheorem)
    {L : EncodedDecisionProblem} (hL : TMInNP L) :
    TMPolyReducible L threeSATDecisionProblem := by
  rcases hL with ⟨V⟩
  exact H.reduction_of_TMVerifier V

/--
A supplied TM Cook-Levin theorem plus direct 3SAT membership proves standard-TM
NP-completeness of bundled 3SAT.
-/
theorem threeSAT_TMNPComplete_of_membership (H : TMCookLevinTheorem)
    (h3SAT : TMInNP threeSATDecisionProblem) :
    TMNPCompleteEnc threeSATDecisionProblem := by
  constructor
  · exact h3SAT
  · intro L hL
    exact H.reduction_of_TMInNP hL

end TMCookLevinTheorem

end SAT
end ComplexityReduction
