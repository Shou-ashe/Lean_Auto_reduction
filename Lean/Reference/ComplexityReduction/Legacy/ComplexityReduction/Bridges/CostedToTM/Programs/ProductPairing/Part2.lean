import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.ProductPairing.Part1

namespace ComplexityReduction
namespace TM2Programs
open Turing.TM2.Stmt

lemma prodMkMachine_right_step (α δ : Type) (tm₁ tm₂ : Turing.FinTM2)
    [Fintype α] [Fintype (tm₁.Γ tm₁.k₀)] [Fintype (tm₂.Γ tm₂.k₀)] [Fintype δ]
    (copyLeft : α → tm₁.Γ tm₁.k₀) (copyRight : α → tm₂.Γ tm₂.k₀)
    (writeLeft : tm₁.Γ tm₁.k₁ → δ) (writeRight : tm₂.Γ tm₂.k₁ → δ)
    (delimiter : δ)
    (cfg next : tm₂.Cfg) (left : (k : tm₁.K) → List (tm₁.Γ k))
    (output : List δ) (outputTemp : List δ) (hStep : tm₂.step cfg = some next) :
    (prodMkMachine α δ tm₁ tm₂ copyLeft copyRight writeLeft writeRight delimiter).step
        (prodMkRightCfg α δ tm₁ tm₂ cfg left output outputTemp) =
      some (prodMkRightCfg α δ tm₁ tm₂ next left output outputTemp) := by
  cases cfg with
  | mk label var stk =>
      cases label with
      | none =>
          simp [Turing.FinTM2.step, Turing.TM2.step] at hStep
      | some label =>
          have hNext : next = Turing.TM2.stepAux (tm₂.m label) var stk := by
            have hSome :
                some (Turing.TM2.stepAux (tm₂.m label) var stk) = some next := by
              simpa [Turing.FinTM2.step, Turing.TM2.step] using hStep
            exact (Option.some.inj hSome).symm
          subst next
          change
            (prodMkMachine α δ tm₁ tm₂ copyLeft copyRight writeLeft writeRight delimiter).step
                (prodMkCfg α δ tm₁ tm₂ (some (ProdMkLabel.right label))
                  (ProdMkState.right var) [] left stk output [] [] outputTemp) =
              some
                (prodMkRightCfg α δ tm₁ tm₂
                  (Turing.TM2.stepAux (tm₂.m label) var stk) left output outputTemp)
          simp [prodMkMachine, prodMkCfg, Turing.FinTM2.step, Turing.TM2.step]
          exact congrArg some
            (prodMkRightStmt_stepAux α δ tm₁ tm₂ (tm₂.m label) var left stk output outputTemp)

def prodMkLeft_evalsToInTime (α δ : Type) (tm₁ tm₂ : Turing.FinTM2)
    [Fintype α] [Fintype (tm₁.Γ tm₁.k₀)] [Fintype (tm₂.Γ tm₂.k₀)] [Fintype δ]
    (copyLeft : α → tm₁.Γ tm₁.k₀) (copyRight : α → tm₂.Γ tm₂.k₀)
    (writeLeft : tm₁.Γ tm₁.k₁ → δ) (writeRight : tm₂.Γ tm₂.k₁ → δ)
    (delimiter : δ)
    {cfg next : tm₁.Cfg} (right : (k : tm₂.K) → List (tm₂.Γ k))
    (output : List δ) (outputTemp : List δ) {time : Nat}
    (h : StateTransition.EvalsToInTime tm₁.step cfg (some next) time) :
    StateTransition.EvalsToInTime
      (prodMkMachine α δ tm₁ tm₂ copyLeft copyRight writeLeft writeRight delimiter).step
      (prodMkLeftCfg α δ tm₁ tm₂ cfg right output outputTemp)
      (some (prodMkLeftCfg α δ tm₁ tm₂ next right output outputTemp)) time := by
  simpa using
    evalsToInTime_map_some (fun cfg => prodMkLeftCfg α δ tm₁ tm₂ cfg right output outputTemp)
      (fun s s' hStep =>
        prodMkMachine_left_step α δ tm₁ tm₂ copyLeft copyRight writeLeft writeRight
          delimiter s s' right output outputTemp hStep)
      h

def prodMkRight_evalsToInTime (α δ : Type) (tm₁ tm₂ : Turing.FinTM2)
    [Fintype α] [Fintype (tm₁.Γ tm₁.k₀)] [Fintype (tm₂.Γ tm₂.k₀)] [Fintype δ]
    (copyLeft : α → tm₁.Γ tm₁.k₀) (copyRight : α → tm₂.Γ tm₂.k₀)
    (writeLeft : tm₁.Γ tm₁.k₁ → δ) (writeRight : tm₂.Γ tm₂.k₁ → δ)
    (delimiter : δ)
    {cfg next : tm₂.Cfg} (left : (k : tm₁.K) → List (tm₁.Γ k))
    (output : List δ) (outputTemp : List δ) {time : Nat}
    (h : StateTransition.EvalsToInTime tm₂.step cfg (some next) time) :
    StateTransition.EvalsToInTime
      (prodMkMachine α δ tm₁ tm₂ copyLeft copyRight writeLeft writeRight delimiter).step
      (prodMkRightCfg α δ tm₁ tm₂ cfg left output outputTemp)
      (some (prodMkRightCfg α δ tm₁ tm₂ next left output outputTemp)) time := by
  simpa using
    evalsToInTime_map_some (fun cfg => prodMkRightCfg α δ tm₁ tm₂ cfg left output outputTemp)
      (fun s s' hStep =>
        prodMkMachine_right_step α δ tm₁ tm₂ copyLeft copyRight writeLeft writeRight
          delimiter s s' left output outputTemp hStep)
      h

lemma prodMkMachine_write_step (α δ : Type) (tm₁ tm₂ : Turing.FinTM2)
    [Fintype α] [Fintype (tm₁.Γ tm₁.k₀)] [Fintype (tm₂.Γ tm₂.k₀)]
    [Fintype (tm₁.Γ tm₁.k₁)] [Fintype (tm₂.Γ tm₂.k₁)] [Fintype δ]
    (copyLeft : α → tm₁.Γ tm₁.k₀) (copyRight : α → tm₂.Γ tm₂.k₀)
    (writeLeft : tm₁.Γ tm₁.k₁ → δ) (writeRight : tm₂.Γ tm₂.k₁ → δ)
    (delimiter : δ)
    (cfg next :
      (pairOutputWriteMachine (tm₁.Γ tm₁.k₁) (tm₂.Γ tm₂.k₁) δ
        writeLeft writeRight delimiter).Cfg)
    (left : (k : tm₁.K) → List (tm₁.Γ k))
    (right : (k : tm₂.K) → List (tm₂.Γ k))
    (hStep :
      (pairOutputWriteMachine (tm₁.Γ tm₁.k₁) (tm₂.Γ tm₂.k₁) δ
        writeLeft writeRight delimiter).step cfg = some next) :
    (prodMkMachine α δ tm₁ tm₂ copyLeft copyRight writeLeft writeRight delimiter).step
        (prodMkWriteCfg α δ tm₁ tm₂ writeLeft writeRight delimiter cfg left right) =
      some (prodMkWriteCfg α δ tm₁ tm₂ writeLeft writeRight delimiter next left right) := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  cases cfg with
  | mk label var stk =>
      cases label with
      | none =>
          simp [Turing.FinTM2.step, Turing.TM2.step] at hStep
      | some label =>
          cases label with
          | readRight =>
              cases hRight : stk PairOutputWriteStack.rightSource with
              | nil =>
                  simp [prodMkMachine, prodMkWriteCfg, prodMkCfg, pairOutputWriteMachine,
                    Turing.FinTM2.step, Turing.TM2.step, prodMkWriteState, hRight,
                    Function.update] at hStep ⊢
                  cases hStep
                  congr
                  funext s
                  cases s with
                  | input => rfl
                  | left k =>
                      by_cases hk : k = tm₁.k₁
                      · subst k
                        simp [Function.update]
                      · simp [Function.update, hk]
                  | right k =>
                      by_cases hk : k = tm₂.k₁
                      · subst k
                        simp [Function.update]
                      · simp [Function.update, hk]
                  | output => rfl
                  | copyLeftTemp => rfl
                  | copyRightTemp => rfl
                  | outputTemp => rfl
              | cons c rightSource =>
                  simp [prodMkMachine, prodMkWriteCfg, prodMkCfg, pairOutputWriteMachine,
                    Turing.FinTM2.step, Turing.TM2.step, prodMkWriteState, hRight,
                    Function.update] at hStep ⊢
                  cases hStep
                  congr
                  funext s
                  cases s with
                  | input => rfl
                  | left k =>
                      by_cases hk : k = tm₁.k₁
                      · subst k
                        simp [Function.update]
                      · simp [Function.update, hk]
                  | right k =>
                      by_cases hk : k = tm₂.k₁
                      · subst k
                        simp [Function.update]
                      · simp [Function.update, hk]
                  | output => rfl
                  | copyLeftTemp => rfl
                  | copyRightTemp => rfl
                  | outputTemp => rfl
          | pushRightTemp d =>
              simp [prodMkMachine, prodMkWriteCfg, prodMkCfg, pairOutputWriteMachine,
                Turing.FinTM2.step, Turing.TM2.step, Function.update] at hStep ⊢
              cases hStep
              simp
              congr
              funext s
              cases s with
              | input => rfl
              | left k =>
                  by_cases hk : k = tm₁.k₁
                  · subst k
                    simp [Function.update]
                  · simp [Function.update, hk]
              | right k =>
                  by_cases hk : k = tm₂.k₁
                  · subst k
                    simp [Function.update]
                  · simp [Function.update, hk]
              | output => rfl
              | copyLeftTemp => rfl
              | copyRightTemp => rfl
              | outputTemp => simp [Function.update]
          | drainRight =>
              cases hTemp : stk PairOutputWriteStack.temp with
              | nil =>
                  simp [prodMkMachine, prodMkWriteCfg, prodMkCfg, pairOutputWriteMachine,
                    Turing.FinTM2.step, Turing.TM2.step, prodMkWriteState, hTemp,
                    Function.update] at hStep ⊢
                  cases hStep
                  congr
              | cons d temp =>
                  simp [prodMkMachine, prodMkWriteCfg, prodMkCfg, pairOutputWriteMachine,
                    Turing.FinTM2.step, Turing.TM2.step, prodMkWriteState, hTemp,
                    Function.update] at hStep ⊢
                  cases hStep
                  congr
                  funext s
                  cases s with
                  | input => rfl
                  | left k =>
                      by_cases hk : k = tm₁.k₁
                      · subst k
                        simp [Function.update]
                      · simp [Function.update, hk]
                  | right k =>
                      by_cases hk : k = tm₂.k₁
                      · subst k
                        simp [Function.update]
                      · simp [Function.update, hk]
                  | output => rfl
                  | copyLeftTemp => rfl
                  | copyRightTemp => rfl
                  | outputTemp => simp [Function.update]
          | pushRightOutput d =>
              simp [prodMkMachine, prodMkWriteCfg, prodMkCfg, pairOutputWriteMachine,
                Turing.FinTM2.step, Turing.TM2.step, Function.update] at hStep ⊢
              cases hStep
              simp
              congr
              funext s
              cases s with
              | input => rfl
              | left k =>
                  by_cases hk : k = tm₁.k₁
                  · subst k
                    simp [Function.update]
                  · simp [Function.update, hk]
              | right k =>
                  by_cases hk : k = tm₂.k₁
                  · subst k
                    simp [Function.update]
                  · simp [Function.update, hk]
              | output => simp [Function.update]
              | copyLeftTemp => rfl
              | copyRightTemp => rfl
              | outputTemp => rfl
          | writeDelimiter =>
              simp [prodMkMachine, prodMkWriteCfg, prodMkCfg, pairOutputWriteMachine,
                Turing.FinTM2.step, Turing.TM2.step, Function.update] at hStep ⊢
              cases hStep
              simp
              congr
              funext s
              cases s with
              | input => rfl
              | left k =>
                  by_cases hk : k = tm₁.k₁
                  · subst k
                    simp [Function.update]
                  · simp [Function.update, hk]
              | right k =>
                  by_cases hk : k = tm₂.k₁
                  · subst k
                    simp [Function.update]
                  · simp [Function.update, hk]
              | output => simp [Function.update]
              | copyLeftTemp => rfl
              | copyRightTemp => rfl
              | outputTemp => rfl
          | readLeft =>
              cases hLeft : stk PairOutputWriteStack.leftSource with
              | nil =>
                  simp [prodMkMachine, prodMkWriteCfg, prodMkCfg, pairOutputWriteMachine,
                    Turing.FinTM2.step, Turing.TM2.step, prodMkWriteState, hLeft,
                    Function.update] at hStep ⊢
                  cases hStep
                  congr
                  funext s
                  cases s with
                  | input => rfl
                  | left k =>
                      by_cases hk : k = tm₁.k₁
                      · subst k
                        simp [Function.update]
                      · simp [Function.update, hk]
                  | right k =>
                      by_cases hk : k = tm₂.k₁
                      · subst k
                        simp [Function.update]
                      · simp [Function.update, hk]
                  | output => rfl
                  | copyLeftTemp => rfl
                  | copyRightTemp => rfl
                  | outputTemp => rfl
              | cons b leftSource =>
                  simp [prodMkMachine, prodMkWriteCfg, prodMkCfg, pairOutputWriteMachine,
                    Turing.FinTM2.step, Turing.TM2.step, prodMkWriteState, hLeft,
                    Function.update] at hStep ⊢
                  cases hStep
                  congr
                  funext s
                  cases s with
                  | input => rfl
                  | left k =>
                      by_cases hk : k = tm₁.k₁
                      · subst k
                        simp [Function.update]
                      · simp [Function.update, hk]
                  | right k =>
                      by_cases hk : k = tm₂.k₁
                      · subst k
                        simp [Function.update]
                      · simp [Function.update, hk]
                  | output => rfl
                  | copyLeftTemp => rfl
                  | copyRightTemp => rfl
                  | outputTemp => rfl
          | pushLeftTemp d =>
              simp [prodMkMachine, prodMkWriteCfg, prodMkCfg, pairOutputWriteMachine,
                Turing.FinTM2.step, Turing.TM2.step, Function.update] at hStep ⊢
              cases hStep
              simp
              congr
              funext s
              cases s with
              | input => rfl
              | left k =>
                  by_cases hk : k = tm₁.k₁
                  · subst k
                    simp [Function.update]
                  · simp [Function.update, hk]
              | right k =>
                  by_cases hk : k = tm₂.k₁
                  · subst k
                    simp [Function.update]
                  · simp [Function.update, hk]
              | output => rfl
              | copyLeftTemp => rfl
              | copyRightTemp => rfl
              | outputTemp => simp [Function.update]
          | drainLeft =>
              cases hTemp : stk PairOutputWriteStack.temp with
              | nil =>
                  simp [prodMkMachine, prodMkWriteCfg, prodMkCfg, pairOutputWriteMachine,
                    Turing.FinTM2.step, Turing.TM2.step, prodMkWriteState, hTemp,
                    Function.update] at hStep ⊢
                  cases hStep
                  congr
              | cons d temp =>
                  simp [prodMkMachine, prodMkWriteCfg, prodMkCfg, pairOutputWriteMachine,
                    Turing.FinTM2.step, Turing.TM2.step, prodMkWriteState, hTemp,
                    Function.update] at hStep ⊢
                  cases hStep
                  congr
                  funext s
                  cases s with
                  | input => rfl
                  | left k =>
                      by_cases hk : k = tm₁.k₁
                      · subst k
                        simp [Function.update]
                      · simp [Function.update, hk]
                  | right k =>
                      by_cases hk : k = tm₂.k₁
                      · subst k
                        simp [Function.update]
                      · simp [Function.update, hk]
                  | output => rfl
                  | copyLeftTemp => rfl
                  | copyRightTemp => rfl
                  | outputTemp => simp [Function.update]
          | pushLeftOutput d =>
              simp [prodMkMachine, prodMkWriteCfg, prodMkCfg, pairOutputWriteMachine,
                Turing.FinTM2.step, Turing.TM2.step, Function.update] at hStep ⊢
              cases hStep
              simp
              congr
              funext s
              cases s with
              | input => rfl
              | left k =>
                  by_cases hk : k = tm₁.k₁
                  · subst k
                    simp [Function.update]
                  · simp [Function.update, hk]
              | right k =>
                  by_cases hk : k = tm₂.k₁
                  · subst k
                    simp [Function.update]
                  · simp [Function.update, hk]
              | output => simp [Function.update]
              | copyLeftTemp => rfl
              | copyRightTemp => rfl
              | outputTemp => rfl

def prodMkWrite_evalsToInTime (α δ : Type) (tm₁ tm₂ : Turing.FinTM2)
    [Fintype α] [Fintype (tm₁.Γ tm₁.k₀)] [Fintype (tm₂.Γ tm₂.k₀)]
    [Fintype (tm₁.Γ tm₁.k₁)] [Fintype (tm₂.Γ tm₂.k₁)] [Fintype δ]
    (copyLeft : α → tm₁.Γ tm₁.k₀) (copyRight : α → tm₂.Γ tm₂.k₀)
    (writeLeft : tm₁.Γ tm₁.k₁ → δ) (writeRight : tm₂.Γ tm₂.k₁ → δ)
    (delimiter : δ)
    {cfg next :
      (pairOutputWriteMachine (tm₁.Γ tm₁.k₁) (tm₂.Γ tm₂.k₁) δ
        writeLeft writeRight delimiter).Cfg}
    (left : (k : tm₁.K) → List (tm₁.Γ k))
    (right : (k : tm₂.K) → List (tm₂.Γ k)) {time : Nat}
    (h :
      StateTransition.EvalsToInTime
        (pairOutputWriteMachine (tm₁.Γ tm₁.k₁) (tm₂.Γ tm₂.k₁) δ
          writeLeft writeRight delimiter).step cfg (some next) time) :
    StateTransition.EvalsToInTime
      (prodMkMachine α δ tm₁ tm₂ copyLeft copyRight writeLeft writeRight delimiter).step
      (prodMkWriteCfg α δ tm₁ tm₂ writeLeft writeRight delimiter cfg left right)
      (some (prodMkWriteCfg α δ tm₁ tm₂ writeLeft writeRight delimiter next left right))
      time := by
  simpa using
    evalsToInTime_map_some
      (fun cfg => prodMkWriteCfg α δ tm₁ tm₂ writeLeft writeRight delimiter cfg left right)
      (fun s s' hStep =>
        prodMkMachine_write_step α δ tm₁ tm₂ copyLeft copyRight writeLeft writeRight
          delimiter s s' left right hStep)
      h

lemma prodMk_initList (α δ : Type) (tm₁ tm₂ : Turing.FinTM2)
    [Fintype α] [Fintype (tm₁.Γ tm₁.k₀)] [Fintype (tm₂.Γ tm₂.k₀)] [Fintype δ]
    (copyLeft : α → tm₁.Γ tm₁.k₀) (copyRight : α → tm₂.Γ tm₂.k₀)
    (writeLeft : tm₁.Γ tm₁.k₁ → δ) (writeRight : tm₂.Γ tm₂.k₁ → δ)
    (delimiter : δ) (input : List α) :
    Turing.initList
        (prodMkMachine α δ tm₁ tm₂ copyLeft copyRight writeLeft writeRight delimiter) input =
      prodMkCopyCfg α δ tm₁ tm₂ copyLeft copyRight
        (pairStackCopyMapCfg α (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) copyLeft copyRight
          PairStackCopyMapLabel.readSource PairStackCopyMapState.none input [] [] [] [])
        (fun _ => []) (fun _ => []) [] [] := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  simp [prodMkMachine, prodMkCopyCfg, prodMkCfg, pairStackCopyMapCfg, Turing.initList]
  congr
  funext s
  cases s with
  | input => rfl
  | left k =>
      by_cases hk : k = tm₁.k₀
      · subst k
        simp
      · simp
  | right k =>
      by_cases hk : k = tm₂.k₀
      · subst k
        simp
      · simp
  | output => rfl
  | copyLeftTemp => rfl
  | copyRightTemp => rfl
  | outputTemp => rfl

lemma prodMkCopy_done_eq_left_init (α δ : Type) (tm₁ tm₂ : Turing.FinTM2)
    [Fintype α] [Fintype (tm₁.Γ tm₁.k₀)] [Fintype (tm₂.Γ tm₂.k₀)]
    (copyLeft : α → tm₁.Γ tm₁.k₀) (copyRight : α → tm₂.Γ tm₂.k₀)
    (leftInput : List (tm₁.Γ tm₁.k₀)) (rightInput : List (tm₂.Γ tm₂.k₀)) :
    prodMkCopyCfg α δ tm₁ tm₂ copyLeft copyRight
        (pairStackCopyMapHalt α (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀)
          copyLeft copyRight leftInput rightInput)
        (fun _ => []) (fun _ => []) [] [] =
      prodMkLeftCfg α δ tm₁ tm₂ (Turing.initList tm₁ leftInput)
        (Turing.initList tm₂ rightInput).stk [] [] := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  simp [prodMkCopyCfg, prodMkLeftCfg, prodMkCfg, pairStackCopyMapHalt, Turing.initList]
  funext s
  cases s with
  | input => rfl
  | left k =>
      by_cases hk : k = tm₁.k₀
      · subst k
        simp [Function.update]
      · simp [Function.update, hk]
  | right k =>
      by_cases hk : k = tm₂.k₀
      · subst k
        simp [Function.update]
      · simp [Function.update, hk]
  | output => rfl
  | copyLeftTemp => rfl
  | copyRightTemp => rfl
  | outputTemp => rfl

lemma prodMkLeft_halt_eq_right_init (α δ : Type) (tm₁ tm₂ : Turing.FinTM2)
    (leftOutput : List (tm₁.Γ tm₁.k₁)) (rightInput : List (tm₂.Γ tm₂.k₀))
    (output : List δ) (outputTemp : List δ) :
    prodMkLeftCfg α δ tm₁ tm₂ (Turing.haltList tm₁ leftOutput)
        (Turing.initList tm₂ rightInput).stk output outputTemp =
      prodMkRightCfg α δ tm₁ tm₂ (Turing.initList tm₂ rightInput)
        (Turing.haltList tm₁ leftOutput).stk output outputTemp := by
  simp [prodMkLeftCfg, prodMkRightCfg, prodMkCfg, Turing.haltList, Turing.initList]

lemma prodMk_haltList_clear_output_eq_empty (tm : Turing.FinTM2)
    (output : List (tm.Γ tm.k₁)) :
    Function.update (Turing.haltList tm output).stk tm.k₁ [] =
      fun k => ([] : List (tm.Γ k)) := by
  letI := tm.kDecidableEq
  funext k
  by_cases hk : k = tm.k₁
  · subst k
    simp [Function.update]
  · simp [Function.update, Turing.haltList, hk]

lemma prodMkRight_halt_eq_write_start (α δ : Type) (tm₁ tm₂ : Turing.FinTM2)
    [Fintype (tm₁.Γ tm₁.k₁)] [Fintype (tm₂.Γ tm₂.k₁)] [Fintype δ]
    (writeLeft : tm₁.Γ tm₁.k₁ → δ) (writeRight : tm₂.Γ tm₂.k₁ → δ)
    (delimiter : δ)
    (leftOutput : List (tm₁.Γ tm₁.k₁)) (rightOutput : List (tm₂.Γ tm₂.k₁))
    (output : List δ) (outputTemp : List δ) :
    prodMkRightCfg α δ tm₁ tm₂ (Turing.haltList tm₂ rightOutput)
        (Turing.haltList tm₁ leftOutput).stk output outputTemp =
      prodMkWriteCfg α δ tm₁ tm₂ writeLeft writeRight delimiter
        (pairOutputWriteCfg (tm₁.Γ tm₁.k₁) (tm₂.Γ tm₂.k₁) δ
          writeLeft writeRight delimiter PairOutputWriteLabel.readRight none
          leftOutput rightOutput output outputTemp)
        (Turing.haltList tm₁ leftOutput).stk (Turing.haltList tm₂ rightOutput).stk := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  simp [prodMkRightCfg, prodMkWriteCfg, prodMkCfg, pairOutputWriteCfg, Turing.haltList,
    Function.update]
  funext s
  cases s with
  | input => rfl
  | left k =>
      by_cases hk : k = tm₁.k₁
      · subst k
        simp
      · simp [hk]
  | right k =>
      by_cases hk : k = tm₂.k₁
      · subst k
        simp
      · simp [hk]
  | output => rfl
  | copyLeftTemp => rfl
  | copyRightTemp => rfl
  | outputTemp => rfl

lemma prodMkWrite_halt_eq_haltList (α δ : Type) (tm₁ tm₂ : Turing.FinTM2)
    [Fintype α] [Fintype (tm₁.Γ tm₁.k₀)] [Fintype (tm₂.Γ tm₂.k₀)]
    [Fintype (tm₁.Γ tm₁.k₁)] [Fintype (tm₂.Γ tm₂.k₁)] [Fintype δ]
    (copyLeft : α → tm₁.Γ tm₁.k₀) (copyRight : α → tm₂.Γ tm₂.k₀)
    (writeLeft : tm₁.Γ tm₁.k₁ → δ) (writeRight : tm₂.Γ tm₂.k₁ → δ)
    (delimiter : δ)
    (leftOutput : List (tm₁.Γ tm₁.k₁)) (rightOutput : List (tm₂.Γ tm₂.k₁))
    (output : List δ) :
    prodMkWriteCfg α δ tm₁ tm₂ writeLeft writeRight delimiter
        (pairOutputWriteHalt (tm₁.Γ tm₁.k₁) (tm₂.Γ tm₂.k₁) δ
          writeLeft writeRight delimiter output)
        (Turing.haltList tm₁ leftOutput).stk (Turing.haltList tm₂ rightOutput).stk =
      Turing.haltList
        (prodMkMachine α δ tm₁ tm₂ copyLeft copyRight writeLeft writeRight delimiter)
        output := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  simp [prodMkWriteCfg, prodMkCfg, pairOutputWriteHalt, prodMkMachine, Turing.haltList]
  funext s
  cases s with
  | input => simp
  | left k =>
      have hClear := congrFun (prodMk_haltList_clear_output_eq_empty tm₁ leftOutput) k
      simpa [Turing.haltList] using hClear
  | right k =>
      have hClear := congrFun (prodMk_haltList_clear_output_eq_empty tm₂ rightOutput) k
      simpa [Turing.haltList] using hClear
  | output => simp
  | copyLeftTemp => simp
  | copyRightTemp => simp
  | outputTemp =>
      change ([] : List δ) = []
      rfl

def prodMk_outputsInTime (α δ : Type) (tm₁ tm₂ : Turing.FinTM2)
    [Fintype α] [Fintype (tm₁.Γ tm₁.k₀)] [Fintype (tm₂.Γ tm₂.k₀)]
    [Fintype (tm₁.Γ tm₁.k₁)] [Fintype (tm₂.Γ tm₂.k₁)] [Fintype δ]
    (copyLeft : α → tm₁.Γ tm₁.k₀) (copyRight : α → tm₂.Γ tm₂.k₀)
    (writeLeft : tm₁.Γ tm₁.k₁ → δ) (writeRight : tm₂.Γ tm₂.k₁ → δ)
    (delimiter : δ)
    (input : List α) (leftOutput : List (tm₁.Γ tm₁.k₁))
    (rightOutput : List (tm₂.Γ tm₂.k₁)) (time₁ time₂ : Nat)
    (h₁ : Turing.TM2OutputsInTime tm₁ (input.map copyLeft) (some leftOutput) time₁)
    (h₂ : Turing.TM2OutputsInTime tm₂ (input.map copyRight) (some rightOutput) time₂) :
    Turing.TM2OutputsInTime
      (prodMkMachine α δ tm₁ tm₂ copyLeft copyRight writeLeft writeRight delimiter)
      input
      (some (leftOutput.map writeLeft ++ delimiter :: rightOutput.map writeRight))
      ((4 * leftOutput.length + 4 * rightOutput.length + 5) +
        (time₂ + (time₁ + (7 * input.length + 3)))) := by
  let tm := prodMkMachine α δ tm₁ tm₂ copyLeft copyRight writeLeft writeRight delimiter
  let leftInput := input.map copyLeft
  let rightInput := input.map copyRight
  let copyStart :=
    prodMkCopyCfg α δ tm₁ tm₂ copyLeft copyRight
      (pairStackCopyMapCfg α (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) copyLeft copyRight
        PairStackCopyMapLabel.readSource PairStackCopyMapState.none input [] [] [] [])
      (fun _ => []) (fun _ => []) [] []
  let leftStart :=
    prodMkLeftCfg α δ tm₁ tm₂ (Turing.initList tm₁ leftInput)
      (Turing.initList tm₂ rightInput).stk [] []
  let rightStart :=
    prodMkRightCfg α δ tm₁ tm₂ (Turing.initList tm₂ rightInput)
      (Turing.haltList tm₁ leftOutput).stk [] []
  let writeStart :=
    prodMkWriteCfg α δ tm₁ tm₂ writeLeft writeRight delimiter
      (pairOutputWriteCfg (tm₁.Γ tm₁.k₁) (tm₂.Γ tm₂.k₁) δ
        writeLeft writeRight delimiter PairOutputWriteLabel.readRight none
        leftOutput rightOutput [] [])
      (Turing.haltList tm₁ leftOutput).stk (Turing.haltList tm₂ rightOutput).stk
  let finalOutput := leftOutput.map writeLeft ++ delimiter :: rightOutput.map writeRight
  let finalCfg := Turing.haltList tm finalOutput
  have hCopyRaw :
      StateTransition.EvalsToInTime
        (pairStackCopyMapMachine α (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀)
          copyLeft copyRight).step
        (pairStackCopyMapCfg α (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀)
          copyLeft copyRight PairStackCopyMapLabel.readSource
          PairStackCopyMapState.none input [] [] [] [])
        (some
          (pairStackCopyMapHalt α (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀)
            copyLeft copyRight leftInput rightInput))
        (7 * input.length + 3) := by
    simpa [leftInput, rightInput] using
      pairStackCopyMap_run α (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀)
        copyLeft copyRight input [] []
  have hCopy : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some leftStart) (7 * input.length + 3) := by
    have hMapped :=
      prodMkCopy_evalsToInTime α δ tm₁ tm₂ copyLeft copyRight writeLeft writeRight
        delimiter (fun _ => []) (fun _ => []) [] [] hCopyRaw
    simpa [tm, copyStart, leftStart, prodMk_initList,
      prodMkCopy_done_eq_left_init, leftInput, rightInput] using hMapped
  have hLeft : StateTransition.EvalsToInTime tm.step leftStart (some rightStart) time₁ := by
    have hMapped :=
      prodMkLeft_evalsToInTime α δ tm₁ tm₂ copyLeft copyRight writeLeft writeRight
        delimiter (Turing.initList tm₂ rightInput).stk [] [] h₁
    simpa [tm, leftStart, rightStart, prodMkLeft_halt_eq_right_init] using hMapped
  have hRight : StateTransition.EvalsToInTime tm.step rightStart (some writeStart) time₂ := by
    have hMapped :=
      prodMkRight_evalsToInTime α δ tm₁ tm₂ copyLeft copyRight writeLeft writeRight
        delimiter (Turing.haltList tm₁ leftOutput).stk [] [] h₂
    rw [prodMkRight_halt_eq_write_start α δ tm₁ tm₂ writeLeft writeRight delimiter
      leftOutput rightOutput [] []] at hMapped
    rw [show rightStart =
        prodMkRightCfg α δ tm₁ tm₂ (Turing.initList tm₂ (input.map copyRight))
          (Turing.haltList tm₁ leftOutput).stk [] [] by
        simp [rightStart, rightInput]]
    rw [show writeStart =
        prodMkWriteCfg α δ tm₁ tm₂ writeLeft writeRight delimiter
          (pairOutputWriteCfg (tm₁.Γ tm₁.k₁) (tm₂.Γ tm₂.k₁) δ
            writeLeft writeRight delimiter PairOutputWriteLabel.readRight none
            leftOutput rightOutput [] [])
          (Turing.haltList tm₁ leftOutput).stk (Turing.haltList tm₂ rightOutput).stk by
        simp [writeStart]]
    simpa [tm] using hMapped
  have hWriteRaw :
      StateTransition.EvalsToInTime
        (pairOutputWriteMachine (tm₁.Γ tm₁.k₁) (tm₂.Γ tm₂.k₁) δ
          writeLeft writeRight delimiter).step
        (pairOutputWriteCfg (tm₁.Γ tm₁.k₁) (tm₂.Γ tm₂.k₁) δ
          writeLeft writeRight delimiter PairOutputWriteLabel.readRight none
          leftOutput rightOutput [] [])
        (some
          (pairOutputWriteHalt (tm₁.Γ tm₁.k₁) (tm₂.Γ tm₂.k₁) δ
            writeLeft writeRight delimiter finalOutput))
        (4 * leftOutput.length + 4 * rightOutput.length + 5) := by
    simpa [finalOutput, List.append_assoc] using
      pairOutputWrite_run (tm₁.Γ tm₁.k₁) (tm₂.Γ tm₂.k₁) δ
        writeLeft writeRight delimiter leftOutput rightOutput []
  have hWrite : StateTransition.EvalsToInTime tm.step writeStart (some finalCfg)
      (4 * leftOutput.length + 4 * rightOutput.length + 5) := by
    have hMapped :=
      prodMkWrite_evalsToInTime α δ tm₁ tm₂ copyLeft copyRight writeLeft writeRight
        delimiter (Turing.haltList tm₁ leftOutput).stk (Turing.haltList tm₂ rightOutput).stk
        hWriteRaw
    rw [prodMkWrite_halt_eq_haltList α δ tm₁ tm₂ copyLeft copyRight writeLeft writeRight
      delimiter leftOutput rightOutput
      (leftOutput.map writeLeft ++ delimiter :: rightOutput.map writeRight)] at hMapped
    rw [show writeStart =
        prodMkWriteCfg α δ tm₁ tm₂ writeLeft writeRight delimiter
          (pairOutputWriteCfg (tm₁.Γ tm₁.k₁) (tm₂.Γ tm₂.k₁) δ
            writeLeft writeRight delimiter PairOutputWriteLabel.readRight none
            leftOutput rightOutput [] [])
          (Turing.haltList tm₁ leftOutput).stk (Turing.haltList tm₂ rightOutput).stk by
        simp [writeStart]]
    rw [show finalCfg =
        Turing.haltList
          (prodMkMachine α δ tm₁ tm₂ copyLeft copyRight writeLeft writeRight delimiter)
          (leftOutput.map writeLeft ++ delimiter :: rightOutput.map writeRight) by
        simp [finalCfg, finalOutput, tm]]
    simpa [tm, finalOutput] using hMapped
  have hCopyLeft : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some rightStart) (time₁ + (7 * input.length + 3)) :=
    StateTransition.EvalsToInTime.trans tm.step (7 * input.length + 3) time₁
      (Turing.initList tm input) leftStart (some rightStart) hCopy hLeft
  have hBeforeWrite : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some writeStart)
      (time₂ + (time₁ + (7 * input.length + 3))) :=
    StateTransition.EvalsToInTime.trans tm.step
      (time₁ + (7 * input.length + 3)) time₂
      (Turing.initList tm input) rightStart (some writeStart) hCopyLeft hRight
  simpa [Turing.TM2OutputsInTime, tm, finalCfg, finalOutput] using
    StateTransition.EvalsToInTime.trans tm.step
      (time₂ + (time₁ + (7 * input.length + 3)))
      (4 * leftOutput.length + 4 * rightOutput.length + 5)
      (Turing.initList tm input) writeStart (some finalCfg) hBeforeWrite hWrite

/-- Polynomial bound used by the arbitrary product-pairing TM2 witness. -/
noncomputable def prodMkTimePolynomial (tm₁ tm₂ : Turing.FinTM2)
    (p₁ p₂ : Polynomial Nat) : Polynomial Nat :=
  let bound₁ := Polynomial.X + p₁ * Polynomial.C (finTM2StepPushBound tm₁)
  let bound₂ := Polynomial.X + p₂ * Polynomial.C (finTM2StepPushBound tm₂)
  (Polynomial.C 4 * bound₁ + Polynomial.C 4 * bound₂ + Polynomial.C 5) +
    p₂ + p₁ + (Polynomial.C 7 * Polynomial.X + Polynomial.C 3)

@[simp] lemma prodMkTimePolynomial_eval (tm₁ tm₂ : Turing.FinTM2)
    (p₁ p₂ : Polynomial Nat) (n : Nat) :
    (prodMkTimePolynomial tm₁ tm₂ p₁ p₂).eval n =
      (4 * (n + p₁.eval n * finTM2StepPushBound tm₁) +
          4 * (n + p₂.eval n * finTM2StepPushBound tm₂) + 5) +
        p₂.eval n + p₁.eval n + (7 * n + 3) := by
  simp [prodMkTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Nat.add_assoc]

/--
Constructive arbitrary product-pairing closure for bundled polynomial-time TM2
witnesses with a shared input encoding.

The orchestrating machine copies the input into the two supplied machines, runs
them sequentially, and writes their outputs into the standard product encoding.
-/
noncomputable def prodMkComputableInPolyTime
    {α β γ αΓ βΓ γΓ : Type} [Fintype αΓ] [Fintype βΓ] [Fintype γΓ]
    {eα : α → List αΓ} {eβ : β → List βΓ} {eγ : γ → List γΓ}
    {f : α → β} {g : α → γ}
    (h₁ : Turing.TM2ComputableInPolyTime eα eβ f)
    (h₂ : Turing.TM2ComputableInPolyTime eα eγ g) :
    Turing.TM2ComputableInPolyTime eα
      (fun p : β × γ =>
        (eβ p.1).map (fun b => some (Sum.inl b : βΓ ⊕ γΓ)) ++ [none] ++
          (eγ p.2).map (fun c => some (Sum.inr c : βΓ ⊕ γΓ)))
      (fun a => (f a, g a)) where
  tm := by
    letI : Fintype (h₁.tm.Γ h₁.tm.k₀) := h₁.tm.Γk₀Fin
    letI : Fintype (h₂.tm.Γ h₂.tm.k₀) := h₂.tm.Γk₀Fin
    letI : Fintype (h₁.tm.Γ h₁.tm.k₁) := Fintype.ofEquiv βΓ h₁.outputAlphabet.symm
    letI : Fintype (h₂.tm.Γ h₂.tm.k₁) := Fintype.ofEquiv γΓ h₂.outputAlphabet.symm
    exact
      prodMkMachine αΓ (Option (βΓ ⊕ γΓ)) h₁.tm h₂.tm
        (fun a => h₁.inputAlphabet.invFun a)
        (fun a => h₂.inputAlphabet.invFun a)
        (fun b => some (Sum.inl (h₁.outputAlphabet b)))
        (fun c => some (Sum.inr (h₂.outputAlphabet c)))
        none
  inputAlphabet := Equiv.refl αΓ
  outputAlphabet := Equiv.refl (Option (βΓ ⊕ γΓ))
  time := prodMkTimePolynomial h₁.tm h₂.tm h₁.time h₂.time
  outputsFun a := by
    letI : Fintype (h₁.tm.Γ h₁.tm.k₀) := h₁.tm.Γk₀Fin
    letI : Fintype (h₂.tm.Γ h₂.tm.k₀) := h₂.tm.Γk₀Fin
    letI : Fintype (h₁.tm.Γ h₁.tm.k₁) := Fintype.ofEquiv βΓ h₁.outputAlphabet.symm
    letI : Fintype (h₂.tm.Γ h₂.tm.k₁) := Fintype.ofEquiv γΓ h₂.outputAlphabet.symm
    let input : List αΓ := List.map (Equiv.refl αΓ).invFun (eα a)
    let leftOutput : List (h₁.tm.Γ h₁.tm.k₁) :=
      List.map h₁.outputAlphabet.invFun (eβ (f a))
    let rightOutput : List (h₂.tm.Γ h₂.tm.k₁) :=
      List.map h₂.outputAlphabet.invFun (eγ (g a))
    let writeLeft : h₁.tm.Γ h₁.tm.k₁ → Option (βΓ ⊕ γΓ) :=
      fun b => some (Sum.inl (h₁.outputAlphabet b))
    let writeRight : h₂.tm.Γ h₂.tm.k₁ → Option (βΓ ⊕ γΓ) :=
      fun c => some (Sum.inr (h₂.outputAlphabet c))
    have hLeft : Turing.TM2OutputsInTime h₁.tm (input.map h₁.inputAlphabet.invFun)
        (some leftOutput) (h₁.time.eval (eα a).length) := by
      simpa [input, leftOutput] using h₁.outputsFun a
    have hRight : Turing.TM2OutputsInTime h₂.tm (input.map h₂.inputAlphabet.invFun)
        (some rightOutput) (h₂.time.eval (eα a).length) := by
      simpa [input, rightOutput] using h₂.outputsFun a
    have hRun :=
      prodMk_outputsInTime αΓ (Option (βΓ ⊕ γΓ)) h₁.tm h₂.tm
        (fun a => h₁.inputAlphabet.invFun a)
        (fun a => h₂.inputAlphabet.invFun a)
        writeLeft writeRight none input leftOutput rightOutput
        (h₁.time.eval (eα a).length) (h₂.time.eval (eα a).length)
        hLeft hRight
    refine
      { steps := hRun.steps
        evals_in_steps := by
          have hLeftMap :
              leftOutput.map writeLeft =
                (eβ (f a)).map (fun b => some (Sum.inl b : βΓ ⊕ γΓ)) := by
            unfold leftOutput writeLeft
            simp only [List.map_map]
            apply List.map_congr_left
            intro b
            simp
          have hRightMap :
              rightOutput.map writeRight =
                (eγ (g a)).map (fun c => some (Sum.inr c : βΓ ⊕ γΓ)) := by
            unfold rightOutput writeRight
            simp only [List.map_map]
            apply List.map_congr_left
            intro c
            simp
          convert hRun.evals_in_steps using 1
          · apply congrArg
            rw [hLeftMap, hRightMap]
            change
              some
                  (List.map (fun x : Option (βΓ ⊕ γΓ) => x)
                    (List.map (fun b => some (Sum.inl b : βΓ ⊕ γΓ)) (eβ (f a)) ++
                      [none] ++
                        List.map (fun c => some (Sum.inr c : βΓ ⊕ γΓ)) (eγ (g a)))) =
                some
                  (List.map (fun b => some (Sum.inl b : βΓ ⊕ γΓ)) (eβ (f a)) ++
                    none :: List.map (fun c => some (Sum.inr c : βΓ ⊕ γΓ)) (eγ (g a)))
            simp only [List.map_id', List.singleton_append, List.append_assoc]
        steps_le_m := ?_ }
    have hRunSteps := hRun.steps_le_m
    let n := (eα a).length
    have hInputLen : input.length = n := by
      simp [input, n]
    have hInputLen' : input.length = (eα a).length := by
      simpa [n] using hInputLen
    have hLeftBound :
        leftOutput.length ≤ n + h₁.time.eval n * finTM2StepPushBound h₁.tm := by
      have hOut := tm2ComputableInPolyTime_output_length_le h₁ a
      simpa [leftOutput, n] using hOut
    have hRightBound :
        rightOutput.length ≤ n + h₂.time.eval n * finTM2StepPushBound h₂.tm := by
      have hOut := tm2ComputableInPolyTime_output_length_le h₂ a
      simpa [rightOutput, n] using hOut
    have hActualLe :
        (4 * leftOutput.length + 4 * rightOutput.length + 5) +
            (h₂.time.eval (eα a).length +
              (h₁.time.eval (eα a).length + (7 * input.length + 3))) ≤
          (prodMkTimePolynomial h₁.tm h₂.tm h₁.time h₂.time).eval (eα a).length := by
      have hLeftBound' :
          leftOutput.length ≤
            (eα a).length +
              h₁.time.eval (eα a).length * finTM2StepPushBound h₁.tm := by
        simpa [n] using hLeftBound
      have hRightBound' :
          rightOutput.length ≤
            (eα a).length +
              h₂.time.eval (eα a).length * finTM2StepPushBound h₂.tm := by
        simpa [n] using hRightBound
      rw [prodMkTimePolynomial_eval]
      simp [hInputLen']
      omega
    exact hRunSteps.trans hActualLe

end TM2Programs
end ComplexityReduction
