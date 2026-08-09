/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.TMComplexityClasses
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps

namespace ComplexityReduction

namespace TM2Programs

/--
Evaluation of a natural-number polynomial is bounded by one coarse monomial.

The extra `+ 1` in the exponent and constant handles the `n = 0` case uniformly,
including the constant term.
-/
theorem polynomialNat_eval_le_monomial_bound (p : Polynomial Nat) (n : Nat) :
    p.eval n ≤
      (Finset.range (p.natDegree + 1)).sum p.coeff * n ^ (p.natDegree + 1) +
        (Finset.range (p.natDegree + 1)).sum p.coeff := by
  rw [Polynomial.eval_eq_sum_range]
  let S := (Finset.range (p.natDegree + 1)).sum p.coeff
  have hTerm :
      ∀ i ∈ Finset.range (p.natDegree + 1),
        p.coeff i * n ^ i ≤ p.coeff i * (n ^ (p.natDegree + 1) + 1) := by
    intro i hi
    have hiLe : i ≤ p.natDegree + 1 := Nat.le_of_lt (Finset.mem_range.mp hi)
    have hPow : n ^ i ≤ n ^ (p.natDegree + 1) + 1 := by
      cases n with
      | zero =>
          cases i <;> simp
      | succ n =>
          have hn : 1 ≤ Nat.succ n := Nat.succ_le_succ (Nat.zero_le n)
          exact (pow_le_pow_right' hn hiLe).trans (Nat.le_add_right _ _)
    exact Nat.mul_le_mul_left (p.coeff i) hPow
  calc
    ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * n ^ i
        ≤ ∑ i ∈ Finset.range (p.natDegree + 1),
            p.coeff i * (n ^ (p.natDegree + 1) + 1) := Finset.sum_le_sum hTerm
    _ = S * n ^ (p.natDegree + 1) + S := by
          simp [S, Nat.mul_add, Finset.sum_add_distrib, Finset.sum_mul]

/-- Every natural-number polynomial has a coarse `coeff * n^degree + const` bound. -/
theorem polynomialNat_eval_polynomialSizeBound (p : Polynomial Nat) :
    ∃ degree coeff const : Nat,
      ∀ n, p.eval n ≤ coeff * n ^ degree + const :=
  ⟨p.natDegree + 1, (Finset.range (p.natDegree + 1)).sum p.coeff,
    (Finset.range (p.natDegree + 1)).sum p.coeff,
    polynomialNat_eval_le_monomial_bound p⟩

end TM2Programs

namespace TMPolyTimeMap

/-- A direct TM2 polynomial-time map has polynomially bounded output length. -/
theorem outputSizeBound {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
    (h : TMPolyTimeMap X Y f) :
    PolynomialSizeBound (fun x => X.inputSize x) (fun y => Y.inputSize y) f := by
  rcases h with ⟨h⟩
  let q : Polynomial Nat :=
    Polynomial.X + h.time * Polynomial.C (TM2Programs.finTM2StepPushBound h.tm)
  rcases TM2Programs.polynomialNat_eval_polynomialSizeBound q with
    ⟨degree, coeff, const, hq⟩
  refine ⟨degree, coeff, const, ?_⟩
  intro x
  have hOut := TM2Programs.tm2ComputableInPolyTime_output_length_le h x
  have hEval :
      X.inputSize x + h.time.eval (X.inputSize x) *
          TM2Programs.finTM2StepPushBound h.tm =
        q.eval (X.inputSize x) := by
    simp [q, EncodedType.inputSize, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X]
  have hEvalLen :
      (X.encode x).length + h.time.eval (X.encode x).length *
          TM2Programs.finTM2StepPushBound h.tm =
        q.eval (X.encode x).length := by
    simpa [EncodedType.inputSize] using hEval
  have hOutQ : Y.inputSize (f x) ≤ q.eval (X.inputSize x) := by
    change (Y.encode (f x)).length ≤ q.eval (X.encode x).length
    exact hOut.trans (Nat.le_of_eq hEvalLen)
  exact hOutQ.trans (hq (X.inputSize x))

end TMPolyTimeMap

namespace TMKarpReduction

/-- Direct TM-backed Karp reductions compose. -/
def comp {A B C : EncodedDecisionProblem}
    (rBC : TMKarpReduction B C) (rAB : TMKarpReduction A B) :
    TMKarpReduction A C where
  f := rBC.f ∘ rAB.f
  polytime := TMPolyTimeMap.comp rBC.polytime rAB.polytime
  correct := fun x => Iff.trans (rAB.correct x) (rBC.correct (rAB.f x))

end TMKarpReduction

namespace TMPolyReducible

/-- Direct TM many-one reducibility is transitive. -/
theorem trans {A B C : EncodedDecisionProblem}
    (hAB : TMPolyReducible A B) (hBC : TMPolyReducible B C) :
    TMPolyReducible A C := by
  rcases hAB with ⟨rAB⟩
  rcases hBC with ⟨rBC⟩
  exact ⟨TMKarpReduction.comp rBC rAB⟩

end TMPolyReducible

namespace TMInP

/-- Deterministic TM `P` is downward closed under direct TM many-one reductions. -/
theorem of_reduction {A B : EncodedDecisionProblem}
    (hAB : TMPolyReducible A B) (hB : TMInP B) : TMInP A := by
  rcases hAB with ⟨rAB⟩
  rcases hB with ⟨dB⟩
  exact intro (fun x => dB.decide (rAB.f x))
    (TMPolyTimeMap.comp dB.polytime rAB.polytime)
    (fun x => Iff.trans (dB.correct (rAB.f x)) (rAB.correct x).symm)

end TMInP

namespace TMInNP

/-- Direct TM `NP` is downward closed under direct TM many-one reductions. -/
theorem of_reduction {A B : EncodedDecisionProblem}
    (hAB : TMPolyReducible A B) (hB : TMInNP B) : TMInNP A := by
  rcases hAB with ⟨rAB⟩
  rcases hB with ⟨VB⟩
  refine intro
    { Cert := VB.Cert
      verify := fun x c => VB.verify (rAB.f x) c
      verifier_polytime := ?_
      cert_bound := ?_
      sound := ?_ }
  · let X := EncodedType.prod A.Instance VB.Cert
    have hFst : TMPolyTimeMap X A.Instance (fun p : A.Instance.Carrier × VB.Cert.Carrier => p.1) :=
      by simpa [X] using TMPolyTimeMap.fst A.Instance VB.Cert
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
  · rcases VB.cert_bound with ⟨degreeB, coeffB, constB, hCertB⟩
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
  · intro x c hVerify
    exact (rAB.correct x).2 (VB.sound (rAB.f x) c hVerify)

end TMInNP

namespace TMNPCompleteEnc

/--
Transfer standard TM NP-completeness along a direct TM many-one reduction.

The target membership hypothesis is explicit: a hardness route does not by
itself manufacture the target's TM verifier.
-/
theorem transfer {A B : EncodedDecisionProblem}
    (hA : TMNPCompleteEnc A)
    (hAB : TMPolyReducible A B)
    (hB : TMInNP B) :
    TMNPCompleteEnc B := by
  constructor
  · exact hB
  · intro L hL
    exact TMPolyReducible.trans (hA.hard L hL) hAB

end TMNPCompleteEnc

end ComplexityReduction
