/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatRange
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyBounds

/-!
Direct standard-TM witnesses for the numeric x-only Cook-Levin bounds.

These lemmas are the first machine-facing layer of the x-only generator proof:
they show that the certificate-size and input-length bounds used by the emitted
CNF are computable directly by standard TM2 polynomial-time maps from `x`.
-/

namespace ComplexityReduction
namespace SAT

/-- The chosen x-only certificate-size bound is direct standard-TM polynomial-time. -/
theorem tmVerifierCertificateSizeBound_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap L.Instance EncodedType.nat
      (fun x : L.Instance.Carrier => tmVerifierCertificateSizeBound V x) := by
  have hSize :
      TMPolyTimeMap L.Instance EncodedType.nat
        (fun x : L.Instance.Carrier => L.Instance.inputSize x) :=
    (encodedInputSizeNatTMBackedMap L.Instance).tm_polytime
  have hPoly :
      TMPolyTimeMap EncodedType.nat EncodedType.nat
        (fun n : Nat =>
          tmVerifierCertificateBoundCoeff V *
            n ^ tmVerifierCertificateBoundDegree V +
          tmVerifierCertificateBoundConst V) :=
    nat_poly_monomial_tm_polytime
      (tmVerifierCertificateBoundDegree V)
      (tmVerifierCertificateBoundCoeff V)
      (tmVerifierCertificateBoundConst V)
  have hComp := TMPolyTimeMap.comp hPoly hSize
  simpa [Function.comp, tmVerifierCertificateSizeBound] using hComp

/-- The x-only verifier input-length bound is direct standard-TM polynomial-time. -/
theorem tmVerifierXOnlyInputLengthBound_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap L.Instance EncodedType.nat
      (fun x : L.Instance.Carrier => tmVerifierXOnlyInputLengthBound V x) := by
  have hSize :
      TMPolyTimeMap L.Instance EncodedType.nat
        (fun x : L.Instance.Carrier => L.Instance.inputSize x) :=
    (encodedInputSizeNatTMBackedMap L.Instance).tm_polytime
  have hPrefix :
      TMPolyTimeMap L.Instance EncodedType.nat
        (fun x : L.Instance.Carrier => L.Instance.inputSize x + 1) := by
    have hAddOne := nat_add_const_tm_polytime 1
    have hComp := TMPolyTimeMap.comp hAddOne hSize
    simpa [Function.comp] using hComp
  have hCert := tmVerifierCertificateSizeBound_tm_polytime V
  have hAddInput :
      TMPolyTimeMap L.Instance natAddInputEncodedType
        (fun x : L.Instance.Carrier =>
          (L.Instance.inputSize x + 1, tmVerifierCertificateSizeBound V x)) :=
    TMPolyTimeMap.prod_mk hPrefix hCert
  have hAdd := TMPolyTimeMap.comp natAdd_tm_polytime hAddInput
  simpa [Function.comp, natAddInputEncodedType, tmVerifierXOnlyInputLengthBound] using hAdd

/-- The x-only verifier time bound is direct standard-TM polynomial-time. -/
theorem tmVerifierXOnlyTimeBound_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap L.Instance EncodedType.nat
      (fun x : L.Instance.Carrier => tmVerifierXOnlyTimeBound V x) := by
  have hInput := tmVerifierXOnlyInputLengthBound_tm_polytime V
  have hEval := nat_polynomial_eval_tm_polytime (tmVerifierComputableWitness V).time
  have hComp := TMPolyTimeMap.comp hEval hInput
  simpa [Function.comp, natPolynomialEval, tmVerifierXOnlyTimeBound] using hComp

/-- The x-only verifier cell bound is direct standard-TM polynomial-time. -/
theorem tmVerifierXOnlyCellBound_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap L.Instance EncodedType.nat
      (fun x : L.Instance.Carrier => tmVerifierXOnlyCellBound V x) := by
  let pushBound := TM2Programs.finTM2StepPushBound (tmVerifierTM V)
  let outputLen := (tmVerifierBoolOutputWord V true).length
  have hInput := tmVerifierXOnlyInputLengthBound_tm_polytime V
  have hTime := tmVerifierXOnlyTimeBound_tm_polytime V
  have hPushConst :
      TMPolyTimeMap L.Instance EncodedType.nat (fun _ : L.Instance.Carrier => pushBound) :=
    TMPolyTimeMap.const L.Instance EncodedType.nat pushBound
  have hMulInput :
      TMPolyTimeMap L.Instance
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun x : L.Instance.Carrier => (tmVerifierXOnlyTimeBound V x, pushBound)) :=
    TMPolyTimeMap.prod_mk hTime hPushConst
  have hMul :
      TMPolyTimeMap L.Instance EncodedType.nat
        (fun x : L.Instance.Carrier => tmVerifierXOnlyTimeBound V x * pushBound) := by
    have hComp := TMPolyTimeMap.comp GenericNatTM.natMul_tm_polytime hMulInput
    simpa [Function.comp] using hComp
  have hFirstAddInput :
      TMPolyTimeMap L.Instance natAddInputEncodedType
        (fun x : L.Instance.Carrier =>
          (tmVerifierXOnlyInputLengthBound V x, tmVerifierXOnlyTimeBound V x * pushBound)) :=
    TMPolyTimeMap.prod_mk hInput hMul
  have hFirstAdd :
      TMPolyTimeMap L.Instance EncodedType.nat
        (fun x : L.Instance.Carrier =>
          tmVerifierXOnlyInputLengthBound V x + tmVerifierXOnlyTimeBound V x * pushBound) := by
    have hComp := TMPolyTimeMap.comp natAdd_tm_polytime hFirstAddInput
    simpa [Function.comp, natAddInputEncodedType] using hComp
  have hAddOutputLen :
      TMPolyTimeMap L.Instance EncodedType.nat
        (fun x : L.Instance.Carrier =>
          tmVerifierXOnlyInputLengthBound V x +
              tmVerifierXOnlyTimeBound V x * pushBound +
            outputLen) := by
    have hAddConst := nat_add_const_tm_polytime outputLen
    have hComp := TMPolyTimeMap.comp hAddConst hFirstAdd
    simpa [Function.comp] using hComp
  have hAddOne :
      TMPolyTimeMap L.Instance EncodedType.nat
        (fun x : L.Instance.Carrier =>
          tmVerifierXOnlyInputLengthBound V x +
              tmVerifierXOnlyTimeBound V x * pushBound +
            outputLen + 1) := by
    have hAddConst := nat_add_const_tm_polytime 1
    have hComp := TMPolyTimeMap.comp hAddConst hAddOutputLen
    simpa [Function.comp] using hComp
  simpa [tmVerifierXOnlyCellBound, pushBound, outputLen] using hAddOne

/-- X-only tableau time rows are direct standard-TM polynomial-time generated. -/
theorem tmVerifierXOnlyTableauTimeRange_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap L.Instance (EncodedType.list EncodedType.nat)
      (fun x : L.Instance.Carrier => tmVerifierXOnlyTableauTimeRange V x) := by
  have hTime := tmVerifierXOnlyTimeBound_tm_polytime V
  have hSucc :
      TMPolyTimeMap L.Instance EncodedType.nat
        (fun x : L.Instance.Carrier => tmVerifierXOnlyTimeBound V x + 1) := by
    have hAddOne := nat_add_const_tm_polytime 1
    have hComp := TMPolyTimeMap.comp hAddOne hTime
    simpa [Function.comp] using hComp
  have hRange := TMPolyTimeMap.comp natRange_tm_polytime hSucc
  simpa [Function.comp, tmVerifierXOnlyTableauTimeRange] using hRange

/-- X-only transition time rows are direct standard-TM polynomial-time generated. -/
theorem tmVerifierXOnlyTransitionTimeRange_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap L.Instance (EncodedType.list EncodedType.nat)
      (fun x : L.Instance.Carrier => tmVerifierXOnlyTransitionTimeRange V x) := by
  have hTime := tmVerifierXOnlyTimeBound_tm_polytime V
  have hRange := TMPolyTimeMap.comp natRange_tm_polytime hTime
  simpa [Function.comp, tmVerifierXOnlyTransitionTimeRange] using hRange

/-- X-only cell coordinates are direct standard-TM polynomial-time generated. -/
theorem tmVerifierXOnlyCellRange_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap L.Instance (EncodedType.list EncodedType.nat)
      (fun x : L.Instance.Carrier => tmVerifierXOnlyCellRange V x) := by
  have hCell := tmVerifierXOnlyCellBound_tm_polytime V
  have hSucc :
      TMPolyTimeMap L.Instance EncodedType.nat
        (fun x : L.Instance.Carrier => tmVerifierXOnlyCellBound V x + 1) := by
    have hAddOne := nat_add_const_tm_polytime 1
    have hComp := TMPolyTimeMap.comp hAddOne hCell
    simpa [Function.comp] using hComp
  have hRange := TMPolyTimeMap.comp natRange_tm_polytime hSucc
  simpa [Function.comp, tmVerifierXOnlyCellRange] using hRange

/-- X-only cell-successor coordinates are direct standard-TM polynomial-time generated. -/
theorem tmVerifierXOnlyCellSuccessorRange_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap L.Instance (EncodedType.list EncodedType.nat)
      (fun x : L.Instance.Carrier => tmVerifierXOnlyCellSuccessorRange V x) := by
  have hCell := tmVerifierXOnlyCellBound_tm_polytime V
  have hRange := TMPolyTimeMap.comp natRange_tm_polytime hCell
  simpa [Function.comp, tmVerifierXOnlyCellSuccessorRange] using hRange

end SAT
end ComplexityReduction
