import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.ListMap.Part2

namespace ComplexityReduction
namespace TM2Programs
open Turing.TM2.Stmt

lemma listMap_initList_eq_cfg (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (input : List (Option α)) :
    Turing.initList (listMapMachine α β tm readInput writeOutput) input =
      listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
        (ListMapState.copy ListMapCopyState.endInput) input (listMapEmptyWork tm) [] [] [] := by
  simp [Turing.initList, listMapMachine, listMapCfg, listMapEmptyWork]
  congr
  funext stack
  cases stack <;> simp

lemma listMap_haltList_eq_cfg (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (output : List (Option β)) :
    Turing.haltList (listMapMachine α β tm readInput writeOutput) output =
      listMapCfg α β tm readInput writeOutput none
        (ListMapState.copy ListMapCopyState.endInput)
        [] (listMapEmptyWork tm) [] output [] := by
  simp [Turing.haltList, listMapMachine, listMapCfg, listMapEmptyWork]
  congr
  funext stack
  cases stack <;> simp

noncomputable def listMap_outputsInTime {δ α β : Type} (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (payload : δ → List α) (mapped : δ → List (tm.Γ tm.k₁)) (elemTime : δ → Nat)
    (hRun : ∀ x,
      StateTransition.EvalsToInTime tm.step
        (Turing.initList tm ((payload x).map readInput))
        (some (Turing.haltList tm (mapped x))) (elemTime x))
    (xs : List δ) :
    Turing.TM2OutputsInTime (listMapMachine α β tm readInput writeOutput)
      (xs.flatMap fun x => (payload x).map some ++ [none])
      (some (listMapLoopAcc writeOutput mapped xs).reverse)
      ((2 * (listMapLoopAcc writeOutput mapped xs).length + 2) +
        listMapLoopTime tm payload mapped elemTime xs) := by
  let input := xs.flatMap fun x => (payload x).map some ++ [none]
  let acc := listMapLoopAcc writeOutput mapped xs
  let cStart := listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
    (ListMapState.copy ListMapCopyState.endInput) input (listMapEmptyWork tm) [] [] []
  let cLoopDone := listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
    (ListMapState.copy ListMapCopyState.endInput) [] (listMapEmptyWork tm) acc [] []
  let cDrain := listMapCfg α β tm readInput writeOutput (some ListMapLabel.finalDrain)
    (ListMapState.final none) [] (listMapEmptyWork tm) acc [] []
  let cHalt := listMapCfg α β tm readInput writeOutput none
    (ListMapState.copy ListMapCopyState.endInput) [] (listMapEmptyWork tm) [] acc.reverse []
  have hLoop : StateTransition.EvalsToInTime
      (listMapMachine α β tm readInput writeOutput).step cStart (some cLoopDone)
      (listMapLoopTime tm payload mapped elemTime xs) := by
    have hRaw :=
      listMap_loop_run tm readInput writeOutput payload mapped elemTime [] [] [] hRun xs
    simpa [cStart, cLoopDone, input, acc] using hRaw
  have hReadNil : StateTransition.EvalsToInTime
      (listMapMachine α β tm readInput writeOutput).step cLoopDone (some cDrain) 1 := by
    simpa [cLoopDone, cDrain, acc] using
      evalsToInTimeOne
        (listMap_readSource_step_nil α β tm readInput writeOutput
          (ListMapState.copy ListMapCopyState.endInput) (listMapEmptyWork tm) acc [] [])
  have hDrain : StateTransition.EvalsToInTime
      (listMapMachine α β tm readInput writeOutput).step cDrain (some cHalt)
      (2 * acc.length + 1) := by
    simpa [cDrain, cHalt, acc] using
      listMap_finalDrain_run α β tm readInput writeOutput (ListMapState.final none)
        [] (listMapEmptyWork tm) acc [] []
  have hFinal : StateTransition.EvalsToInTime
      (listMapMachine α β tm readInput writeOutput).step cLoopDone (some cHalt)
      (2 * acc.length + 2) := by
    have hRaw :=
      StateTransition.EvalsToInTime.trans
        (listMapMachine α β tm readInput writeOutput).step 1 (2 * acc.length + 1)
        cLoopDone cDrain (some cHalt) hReadNil hDrain
    convert hRaw using 1
  have hAll : StateTransition.EvalsToInTime
      (listMapMachine α β tm readInput writeOutput).step cStart (some cHalt)
      ((2 * acc.length + 2) + listMapLoopTime tm payload mapped elemTime xs) :=
    StateTransition.EvalsToInTime.trans
      (listMapMachine α β tm readInput writeOutput).step
      (listMapLoopTime tm payload mapped elemTime xs) (2 * acc.length + 2)
      cStart cLoopDone (some cHalt) hLoop hFinal
  simpa [Turing.TM2OutputsInTime, cStart, cHalt, input, acc,
    listMap_initList_eq_cfg, listMap_haltList_eq_cfg] using hAll

/-- Coefficient used by the list-map polynomial loop-time bound. -/
noncomputable def listMapLoopTimeCoeff (tm : Turing.FinTM2) : Nat :=
  (listMapAllWorkStacks tm).card + 2 * finTM2StepPushBound tm + 20

/-- Polynomial bound used by arbitrary list-map TM2 witnesses. -/
noncomputable def listMapTimePolynomial (tm : Turing.FinTM2)
    (p : Polynomial Nat) : Polynomial Nat :=
  Polynomial.C (listMapLoopTimeCoeff tm + 2 * (finTM2StepPushBound tm + 2) + 2) *
    (Polynomial.X + 1) * (p + Polynomial.X + 1)

@[simp] lemma listMapTimePolynomial_eval (tm : Turing.FinTM2)
    (p : Polynomial Nat) (n : Nat) :
    (listMapTimePolynomial tm p).eval n =
      (listMapLoopTimeCoeff tm + 2 * (finTM2StepPushBound tm + 2) + 2) *
        (n + 1) * (p.eval n + n + 1) := by
  simp [listMapTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Nat.add_assoc]

lemma listMapLoopAcc_length_le {δ α γ β : Type}
    (tm : Turing.FinTM2) (p : Polynomial Nat)
    (payload : δ → List α) (mapped : δ → List γ) (writeOutput : γ → β)
    (B : Nat)
    (hOutLen : ∀ x, (mapped x).length ≤
      (payload x).length + p.eval (payload x).length * B) :
    ∀ xs : List δ,
      (listMapLoopAcc writeOutput mapped xs).length ≤
        (B + 2) * listMapSourceLength payload xs *
          (p.eval (listMapSourceLength payload xs) +
            listMapSourceLength payload xs + 1)
  | [] => by
      simp [listMapLoopAcc]
  | x :: xs => by
      let nTail := listMapSourceLength payload xs
      let len := (payload x).length
      let n := listMapSourceLength payload (x :: xs)
      let pTail := p.eval nTail
      let pHead := p.eval len
      let pN := p.eval n
      have hnTail : nTail ≤ n := by
        simp [n, nTail, listMapSourceLength]
      have hlen : len ≤ n := by
        simp [n, len, listMapSourceLength]
        omega
      have hpTail : pTail ≤ pN := by
        exact polynomialNat_eval_mono p hnTail
      have hpHead : pHead ≤ pN := by
        exact polynomialNat_eval_mono p hlen
      have hTail := listMapLoopAcc_length_le tm p payload mapped writeOutput B hOutLen xs
      have hTailMono :
          (B + 2) * nTail * (pTail + nTail + 1) ≤
            (B + 2) * nTail * (pN + n + 1) := by
        exact Nat.mul_le_mul_left ((B + 2) * nTail) (by omega)
      have hTail' :
          (listMapLoopAcc writeOutput mapped xs).length ≤
            (B + 2) * nTail * (pN + n + 1) :=
        hTail.trans hTailMono
      have hBlock :
          (listMapReverseBlock writeOutput (mapped x)).length ≤
            (B + 2) * (len + 1) * (pN + n + 1) := by
        have hOut := hOutLen x
        simp [listMapReverseBlock, len] at hOut ⊢
        nlinarith [hpHead, Nat.zero_le (B * pHead * len),
          Nat.zero_le (B * pN * len), Nat.zero_le (B * len)]
      calc
        (listMapLoopAcc writeOutput mapped (x :: xs)).length
            = (listMapLoopAcc writeOutput mapped xs).length +
                (listMapReverseBlock writeOutput (mapped x)).length := by
                  simp [listMapLoopAcc]
        _ ≤ (B + 2) * nTail * (pN + n + 1) +
              (B + 2) * (len + 1) * (pN + n + 1) :=
                  Nat.add_le_add hTail' hBlock
        _ ≤ (B + 2) * n * (pN + n + 1) := by
                  simp [n, nTail, len, listMapSourceLength]
                  nlinarith

lemma listMapLoopTime_le {δ α γ : Type}
    (tm : Turing.FinTM2) (p : Polynomial Nat)
    (payload : δ → List α) (mapped : δ → List γ)
    (B C : Nat)
    (hCoeff : (listMapAllWorkStacks tm).card + 2 * B + 20 ≤ C)
    (hOutLen : ∀ x, (mapped x).length ≤
      (payload x).length + p.eval (payload x).length * B) :
    ∀ xs : List δ,
      listMapLoopTime tm payload mapped (fun x => p.eval (payload x).length) xs ≤
        C * listMapSourceLength payload xs *
          (p.eval (listMapSourceLength payload xs) +
            listMapSourceLength payload xs + 1)
  | [] => by
      simp [listMapLoopTime]
  | x :: xs => by
      let nTail := listMapSourceLength payload xs
      let len := (payload x).length
      let n := listMapSourceLength payload (x :: xs)
      let pTail := p.eval nTail
      let pHead := p.eval len
      let pN := p.eval n
      have hnTail : nTail ≤ n := by
        simp [n, nTail, listMapSourceLength]
      have hlen : len ≤ n := by
        simp [n, len, listMapSourceLength]
        omega
      have hpTail : pTail ≤ pN := by
        exact polynomialNat_eval_mono p hnTail
      have hpHead : pHead ≤ pN := by
        exact polynomialNat_eval_mono p hlen
      have hTail := listMapLoopTime_le tm p payload mapped B C hCoeff hOutLen xs
      have hTailMono :
          C * nTail * (pTail + nTail + 1) ≤
            C * nTail * (pN + n + 1) := by
        exact Nat.mul_le_mul_left (C * nTail) (by omega)
      have hTail' :
          listMapLoopTime tm payload mapped (fun x => p.eval (payload x).length) xs ≤
            C * nTail * (pN + n + 1) :=
        hTail.trans hTailMono
      have hBlock :
          listMapBlockTime tm len (mapped x).length pHead ≤
            C * (len + 1) * (pN + n + 1) := by
        have hOut := hOutLen x
        simp [listMapBlockTime, len, pHead] at hOut ⊢
        nlinarith [hCoeff, hpHead, Nat.zero_le (B * pHead * len),
          Nat.zero_le (B * pN * len), Nat.zero_le (C * len * pN),
          Nat.zero_le (C * len * n), Nat.zero_le ((listMapAllWorkStacks tm).card * len),
          Nat.zero_le (B * len)]
      calc
        listMapLoopTime tm payload mapped (fun x => p.eval (payload x).length) (x :: xs)
            = listMapLoopTime tm payload mapped
                (fun x => p.eval (payload x).length) xs +
              listMapBlockTime tm len (mapped x).length pHead := by
                  simp [listMapLoopTime, len, pHead]
        _ ≤ C * nTail * (pN + n + 1) +
              C * (len + 1) * (pN + n + 1) :=
                  Nat.add_le_add hTail' hBlock
        _ ≤ C * n * (pN + n + 1) := by
                  simp [n, nTail, len, listMapSourceLength]
                  nlinarith

lemma listMap_totalTime_le {δ α γ β : Type}
    (tm : Turing.FinTM2) (p : Polynomial Nat)
    (payload : δ → List α) (mapped : δ → List γ) (writeOutput : γ → β)
    (B : Nat)
    (hB : B = finTM2StepPushBound tm)
    (hOutLen : ∀ x, (mapped x).length ≤
      (payload x).length + p.eval (payload x).length * B)
    (xs : List δ) :
    (2 * (listMapLoopAcc writeOutput mapped xs).length + 2) +
        listMapLoopTime tm payload mapped (fun x => p.eval (payload x).length) xs ≤
      (listMapTimePolynomial tm p).eval (listMapSourceLength payload xs) := by
  let n := listMapSourceLength payload xs
  let pN := p.eval n
  let C := listMapLoopTimeCoeff tm
  let D := listMapLoopTimeCoeff tm + 2 * (finTM2StepPushBound tm + 2) + 2
  have hCoeff : (listMapAllWorkStacks tm).card + 2 * B + 20 ≤ C := by
    subst B
    simp [C, listMapLoopTimeCoeff]
  have hAcc := listMapLoopAcc_length_le tm p payload mapped writeOutput B hOutLen xs
  have hLoop := listMapLoopTime_le tm p payload mapped B C hCoeff hOutLen xs
  have hAcc' :
      (listMapLoopAcc writeOutput mapped xs).length ≤
        (B + 2) * n * (pN + n + 1) := by
    simpa [n, pN] using hAcc
  have hLoop' :
      listMapLoopTime tm payload mapped (fun x => p.eval (payload x).length) xs ≤
        C * n * (pN + n + 1) := by
    simpa [n, pN] using hLoop
  rw [listMapTimePolynomial_eval]
  subst B
  simp
  nlinarith [hAcc', hLoop']

noncomputable def listMapComputableInPolyTime
    {α β αΓ βΓ : Type} [Fintype αΓ] [Fintype βΓ]
    {eα : α → List αΓ} {eβ : β → List βΓ} {f : α → β}
    (h : Turing.TM2ComputableInPolyTime eα eβ f) :
    Turing.TM2ComputableInPolyTime
      (fun xs : List α => xs.flatMap fun x => (eα x).map some ++ [none])
      (fun ys : List β => ys.flatMap fun y => (eβ y).map some ++ [none])
      (fun xs => xs.map f) where
  tm := by
    letI : Fintype (h.tm.Γ h.tm.k₀) := h.tm.Γk₀Fin
    exact listMapMachine αΓ βΓ h.tm h.inputAlphabet.invFun h.outputAlphabet
  inputAlphabet := Equiv.refl (Option αΓ)
  outputAlphabet := Equiv.refl (Option βΓ)
  time := listMapTimePolynomial h.tm h.time
  outputsFun xs := by
    letI : Fintype (h.tm.Γ h.tm.k₀) := h.tm.Γk₀Fin
    let payload : α → List αΓ := eα
    let mapped : α → List (h.tm.Γ h.tm.k₁) :=
      fun x => (eβ (f x)).map h.outputAlphabet.invFun
    let readInput : αΓ → h.tm.Γ h.tm.k₀ := h.inputAlphabet.invFun
    let writeOutput : h.tm.Γ h.tm.k₁ → βΓ := h.outputAlphabet
    have hRun : ∀ x,
        StateTransition.EvalsToInTime h.tm.step
          (Turing.initList h.tm ((payload x).map readInput))
          (some (Turing.haltList h.tm (mapped x)))
          (h.time.eval (payload x).length) := by
      intro x
      simpa [Turing.TM2OutputsInTime, payload, mapped, readInput] using h.outputsFun x
    have hOutput :
        (listMapLoopAcc writeOutput mapped xs).reverse =
          (xs.map f).flatMap fun y => (eβ y).map some ++ [none] := by
      rw [listMapLoopAcc_reverse]
      induction xs with
      | nil =>
          simp
      | cons x xs ih =>
          have hHead :
              (mapped x).map (fun b => some (writeOutput b)) =
                (eβ (f x)).map some := by
            simp only [mapped, writeOutput, List.map_map]
            apply List.map_congr_left
            intro b
            simp
          simp [hHead, ih]
    have hRaw :=
      listMap_outputsInTime h.tm readInput writeOutput payload mapped
        (fun x => h.time.eval (payload x).length) hRun xs
    have hOutLen : ∀ x, (mapped x).length ≤
        (payload x).length +
          h.time.eval (payload x).length * finTM2StepPushBound h.tm := by
      intro x
      have hBound := tm2ComputableInPolyTime_output_length_le h x
      simpa [payload, mapped] using hBound
    have hTime :
        (2 * (listMapLoopAcc writeOutput mapped xs).length + 2) +
            listMapLoopTime h.tm payload mapped
              (fun x => h.time.eval (payload x).length) xs ≤
          (listMapTimePolynomial h.tm h.time).eval
            (((fun xs : List α =>
              xs.flatMap fun x => (eα x).map some ++ [none]) xs).length) := by
      simpa [payload, listMapSourceLength] using
        listMap_totalTime_le h.tm h.time payload mapped writeOutput
          (finTM2StepPushBound h.tm) rfl hOutLen xs
    have hPadded := evalsToInTime_mono hRaw hTime
    unfold Turing.TM2OutputsInTime
    convert hPadded using 1
    · congr
      change List.map (fun x : Option αΓ => x)
          (List.flatMap (fun x => (eα x).map some ++ [none]) xs) =
        List.flatMap (fun x => (payload x).map some ++ [none]) xs
      simp [payload]
    · rw [hOutput]
      congr
      change List.map (fun x : Option βΓ => x)
          (List.flatMap (fun y => (eβ y).map some ++ [none]) (xs.map f)) =
        List.flatMap (fun y => (eβ y).map some ++ [none]) (xs.map f)
      simp

end TM2Programs
end ComplexityReduction
