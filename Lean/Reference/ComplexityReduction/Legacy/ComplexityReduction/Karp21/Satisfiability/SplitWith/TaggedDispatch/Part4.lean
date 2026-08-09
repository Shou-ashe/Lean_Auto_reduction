import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.SplitWith.TaggedDispatch.Part3

namespace ComplexityReduction
namespace Karp21
open ComplexityReduction
open Turing.TM2.Stmt

/--
Direct TM2 polynomial-time closure for a tagged branch dispatcher whose two
branch encodings share the same payload alphabet.  The public input is
`false :: left-payload` or `true :: right-payload`; only the selected branch
machine is run, and its output is retagged into the common codomain alphabet.
-/

noncomputable def taggedBranchDispatchComputableInPolyTime
    {βLeft βRight δ α γ : Type} [Fintype α] [Fintype γ]
    {encodeLeft : βLeft → List α} {encodeRight : βRight → List α}
    {encodeOut : δ → List γ}
    {fLeft : βLeft → δ} {fRight : βRight → δ}
    (hLeft : Turing.TM2ComputableInPolyTime encodeLeft encodeOut fLeft)
    (hRight : Turing.TM2ComputableInPolyTime encodeRight encodeOut fRight) :
    Turing.TM2ComputableInPolyTime
      (fun q : βLeft ⊕ βRight =>
        match q with
        | Sum.inl x => Sum.inl false :: (encodeLeft x).map Sum.inr
        | Sum.inr y => Sum.inl true :: (encodeRight y).map Sum.inr)
      encodeOut
      (fun q =>
        match q with
        | Sum.inl x => fLeft x
        | Sum.inr y => fRight y) where
  tm := by
    letI : Fintype (hLeft.tm.Γ hLeft.tm.k₀) := hLeft.tm.Γk₀Fin
    letI : Fintype (hRight.tm.Γ hRight.tm.k₀) := hRight.tm.Γk₀Fin
    letI : Fintype (hLeft.tm.Γ hLeft.tm.k₁) :=
      Fintype.ofEquiv γ hLeft.outputAlphabet.symm
    letI : Fintype (hRight.tm.Γ hRight.tm.k₁) :=
      Fintype.ofEquiv γ hRight.outputAlphabet.symm
    exact
      taggedBranchDispatchMachine α γ hLeft.tm hRight.tm
        (fun a => hLeft.inputAlphabet.invFun a)
        (fun a => hRight.inputAlphabet.invFun a)
        (fun b => hLeft.outputAlphabet b)
        (fun c => hRight.outputAlphabet c)
  inputAlphabet := Equiv.refl (Bool ⊕ α)
  outputAlphabet := Equiv.refl γ
  time := taggedBranchDispatchTimePolynomial hLeft.tm hRight.tm hLeft.time hRight.time
  outputsFun q := by
    letI : Fintype (hLeft.tm.Γ hLeft.tm.k₀) := hLeft.tm.Γk₀Fin
    letI : Fintype (hRight.tm.Γ hRight.tm.k₀) := hRight.tm.Γk₀Fin
    letI : Fintype (hLeft.tm.Γ hLeft.tm.k₁) :=
      Fintype.ofEquiv γ hLeft.outputAlphabet.symm
    letI : Fintype (hRight.tm.Γ hRight.tm.k₁) :=
      Fintype.ofEquiv γ hRight.outputAlphabet.symm
    cases q with
    | inl x =>
        let payload := encodeLeft x
        let leftOutput : List (hLeft.tm.Γ hLeft.tm.k₁) :=
          (encodeOut (fLeft x)).map hLeft.outputAlphabet.invFun
        let writeLeft : hLeft.tm.Γ hLeft.tm.k₁ → γ := fun b => hLeft.outputAlphabet b
        let writeRight : hRight.tm.Γ hRight.tm.k₁ → γ := fun c => hRight.outputAlphabet c
        have hBranch : Turing.TM2OutputsInTime hLeft.tm
            (payload.map (fun a => hLeft.inputAlphabet.invFun a))
            (some leftOutput) (hLeft.time.eval payload.length) := by
          simpa [payload, leftOutput] using hLeft.outputsFun x
        have hRun :=
          taggedBranchDispatch_outputs_left α γ hLeft.tm hRight.tm
            (fun a => hLeft.inputAlphabet.invFun a)
            (fun a => hRight.inputAlphabet.invFun a)
            writeLeft writeRight payload leftOutput (hLeft.time.eval payload.length) hBranch
        have hRun' : Turing.TM2OutputsInTime
            (taggedBranchDispatchMachine α γ hLeft.tm hRight.tm
              (fun a => hLeft.inputAlphabet.invFun a)
              (fun a => hRight.inputAlphabet.invFun a) writeLeft writeRight)
            (List.map (Equiv.refl (Bool ⊕ α)).invFun
              (Sum.inl false :: (encodeLeft x).map Sum.inr))
            (some (List.map (Equiv.refl γ).invFun (encodeOut (fLeft x))))
            (hLeft.time.eval payload.length + 4 * payload.length +
              4 * leftOutput.length + 6) := by
          convert hRun using 1
          · simp [payload]
          · apply congrArg some
            simp [leftOutput, writeLeft, List.map_map]
        refine TM2Programs.evalsToInTime_mono
          (m := hLeft.time.eval payload.length + 4 * payload.length +
            4 * leftOutput.length + 6) ?_ ?_
        · simpa [Turing.TM2OutputsInTime, writeLeft, writeRight] using hRun'
        · let n := (Sum.inl false :: (encodeLeft x).map Sum.inr).length
          have hPayloadLe : payload.length ≤ n := by
            simp [payload, n]
          have hTimeMono :
              hLeft.time.eval payload.length ≤ hLeft.time.eval n :=
            TM2Programs.polynomialNat_eval_mono hLeft.time hPayloadLe
          have hOutBound :
              leftOutput.length ≤
                payload.length +
                  hLeft.time.eval payload.length *
                    TM2Programs.finTM2StepPushBound hLeft.tm := by
            have h := TM2Programs.tm2ComputableInPolyTime_output_length_le hLeft x
            simpa [leftOutput, payload] using h
          have hTimeMul :
              hLeft.time.eval payload.length *
                  TM2Programs.finTM2StepPushBound hLeft.tm ≤
                hLeft.time.eval n *
                  TM2Programs.finTM2StepPushBound hLeft.tm :=
            Nat.mul_le_mul_right _ hTimeMono
          have hBound :
              hLeft.time.eval payload.length + 4 * payload.length +
                  4 * leftOutput.length + 6 ≤
                hLeft.time.eval n *
                    (4 * TM2Programs.finTM2StepPushBound hLeft.tm + 1) +
                  hRight.time.eval n *
                    (4 * TM2Programs.finTM2StepPushBound hRight.tm + 1) +
                    8 * n + 6 := by
            nlinarith
          simpa [taggedBranchDispatchTimePolynomial_eval, n, payload] using hBound
    | inr y =>
        let payload := encodeRight y
        let rightOutput : List (hRight.tm.Γ hRight.tm.k₁) :=
          (encodeOut (fRight y)).map hRight.outputAlphabet.invFun
        let writeLeft : hLeft.tm.Γ hLeft.tm.k₁ → γ := fun b => hLeft.outputAlphabet b
        let writeRight : hRight.tm.Γ hRight.tm.k₁ → γ := fun c => hRight.outputAlphabet c
        have hBranch : Turing.TM2OutputsInTime hRight.tm
            (payload.map (fun a => hRight.inputAlphabet.invFun a))
            (some rightOutput) (hRight.time.eval payload.length) := by
          simpa [payload, rightOutput] using hRight.outputsFun y
        have hRun :=
          taggedBranchDispatch_outputs_right α γ hLeft.tm hRight.tm
            (fun a => hLeft.inputAlphabet.invFun a)
            (fun a => hRight.inputAlphabet.invFun a)
            writeLeft writeRight payload rightOutput (hRight.time.eval payload.length) hBranch
        have hRun' : Turing.TM2OutputsInTime
            (taggedBranchDispatchMachine α γ hLeft.tm hRight.tm
              (fun a => hLeft.inputAlphabet.invFun a)
              (fun a => hRight.inputAlphabet.invFun a) writeLeft writeRight)
            (List.map (Equiv.refl (Bool ⊕ α)).invFun
              (Sum.inl true :: (encodeRight y).map Sum.inr))
            (some (List.map (Equiv.refl γ).invFun (encodeOut (fRight y))))
            (hRight.time.eval payload.length + 4 * payload.length +
              4 * rightOutput.length + 6) := by
          convert hRun using 1
          · simp [payload]
          · apply congrArg some
            simp [rightOutput, writeRight, List.map_map]
        refine TM2Programs.evalsToInTime_mono
          (m := hRight.time.eval payload.length + 4 * payload.length +
            4 * rightOutput.length + 6) ?_ ?_
        · simpa [Turing.TM2OutputsInTime, writeLeft, writeRight] using hRun'
        · let n := (Sum.inl true :: (encodeRight y).map Sum.inr).length
          have hPayloadLe : payload.length ≤ n := by
            simp [payload, n]
          have hTimeMono :
              hRight.time.eval payload.length ≤ hRight.time.eval n :=
            TM2Programs.polynomialNat_eval_mono hRight.time hPayloadLe
          have hOutBound :
              rightOutput.length ≤
                payload.length +
                  hRight.time.eval payload.length *
                    TM2Programs.finTM2StepPushBound hRight.tm := by
            have h := TM2Programs.tm2ComputableInPolyTime_output_length_le hRight y
            simpa [rightOutput, payload] using h
          have hTimeMul :
              hRight.time.eval payload.length *
                  TM2Programs.finTM2StepPushBound hRight.tm ≤
                hRight.time.eval n *
                  TM2Programs.finTM2StepPushBound hRight.tm :=
            Nat.mul_le_mul_right _ hTimeMono
          have hBound :
              hRight.time.eval payload.length + 4 * payload.length +
                  4 * rightOutput.length + 6 ≤
                hLeft.time.eval n *
                    (4 * TM2Programs.finTM2StepPushBound hLeft.tm + 1) +
                  hRight.time.eval n *
                    (4 * TM2Programs.finTM2StepPushBound hRight.tm + 1) +
                    8 * n + 6 := by
            nlinarith
          simpa [taggedBranchDispatchTimePolynomial_eval, n, payload] using hBound

end Karp21
end ComplexityReduction
