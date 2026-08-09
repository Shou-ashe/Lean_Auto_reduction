import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.SplitWith.TaggedDispatch.Part2

namespace ComplexityReduction
namespace Karp21
open ComplexityReduction
open Turing.TM2.Stmt

lemma taggedBranchLeftStmt_stepAux
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (q : Turing.TM2.Stmt tmLeft.Γ tmLeft.Λ tmLeft.σ)
    (v : tmLeft.σ)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    @Turing.TM2.stepAux (TaggedBranchDispatchStack tmLeft.K tmRight.K)
        (taggedBranchDispatchAlphabet α γ tmLeft tmRight)
        (TaggedBranchDispatchLabel tmLeft.Λ tmRight.Λ
          (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
        (TaggedBranchDispatchState tmLeft.σ tmRight.σ
          (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
        (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight writeLeft
          writeRight).kDecidableEq
        (taggedBranchLeftStmt α γ tmLeft tmRight writeLeft q) (.leftRun v)
        (taggedBranchDispatchStacks α γ tmLeft tmRight source left right leftTemp
          rightTemp output outputTemp) =
      taggedBranchDispatchLeftRunCfg α γ tmLeft tmRight readLeft readRight writeLeft
        writeRight (@Turing.TM2.stepAux tmLeft.K tmLeft.Γ tmLeft.Λ tmLeft.σ
          tmLeft.kDecidableEq q v left) source right leftTemp rightTemp output outputTemp := by
  letI := tmLeft.kDecidableEq
  letI := tmRight.kDecidableEq
  letI dispatchDec : DecidableEq (TaggedBranchDispatchStack tmLeft.K tmRight.K) :=
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight writeLeft
      writeRight).kDecidableEq
  induction q generalizing v left with
  | push k f q ih =>
      have hstk :
          @Function.update (TaggedBranchDispatchStack tmLeft.K tmRight.K)
              (fun s => List (taggedBranchDispatchAlphabet α γ tmLeft tmRight s))
              (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight writeLeft
                writeRight).kDecidableEq
              (taggedBranchDispatchStacks α γ tmLeft tmRight source left right leftTemp
                rightTemp output outputTemp)
              (TaggedBranchDispatchStack.left k) (f v :: left k) =
            taggedBranchDispatchStacks α γ tmLeft tmRight source
              (@Function.update tmLeft.K (fun k => List (tmLeft.Γ k))
                tmLeft.kDecidableEq left k (f v :: left k))
              right leftTemp rightTemp output outputTemp := by
        funext s
        cases s with
        | source => rfl
        | left k' =>
            by_cases hk : k' = k
            · subst k'
              simp [Function.update]
            · simp [Function.update, hk]
        | right k' => rfl
        | leftInputTemp => rfl
        | rightInputTemp => rfl
        | output => rfl
        | outputTemp => rfl
      simpa [taggedBranchLeftStmt, taggedBranchDispatchLeftRunState, hstk] using
        ih v (@Function.update tmLeft.K (fun k => List (tmLeft.Γ k))
          tmLeft.kDecidableEq left k (f v :: left k))
  | peek k f q ih =>
      simpa [taggedBranchLeftStmt, taggedBranchDispatchLeftRunState] using
        ih (f v (left k).head?) left
  | pop k f q ih =>
      have hstk :
          @Function.update (TaggedBranchDispatchStack tmLeft.K tmRight.K)
              (fun s => List (taggedBranchDispatchAlphabet α γ tmLeft tmRight s))
              (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight writeLeft
                writeRight).kDecidableEq
              (taggedBranchDispatchStacks α γ tmLeft tmRight source left right leftTemp
                rightTemp output outputTemp)
              (TaggedBranchDispatchStack.left k) (left k).tail =
            taggedBranchDispatchStacks α γ tmLeft tmRight source
              (@Function.update tmLeft.K (fun k => List (tmLeft.Γ k))
                tmLeft.kDecidableEq left k (left k).tail)
              right leftTemp rightTemp output outputTemp := by
        funext s
        cases s with
        | source => rfl
        | left k' =>
            by_cases hk : k' = k
            · subst k'
              simp [Function.update]
            · simp [Function.update, hk]
        | right k' => rfl
        | leftInputTemp => rfl
        | rightInputTemp => rfl
        | output => rfl
        | outputTemp => rfl
      simpa [taggedBranchLeftStmt, taggedBranchDispatchLeftRunState, hstk] using
        ih (f v (left k).head?) (@Function.update tmLeft.K (fun k => List (tmLeft.Γ k))
          tmLeft.kDecidableEq left k (left k).tail)
  | load f q ih =>
      simpa [taggedBranchLeftStmt, taggedBranchDispatchLeftRunState] using
        ih (f v) left
  | branch f qTrue qFalse ihTrue ihFalse =>
      by_cases hf : f v
      · simpa [taggedBranchLeftStmt, taggedBranchDispatchLeftRunState, hf] using
          ihTrue v left
      · simpa [taggedBranchLeftStmt, taggedBranchDispatchLeftRunState, hf] using
          ihFalse v left
  | goto f =>
      simp [taggedBranchLeftStmt, taggedBranchDispatchLeftRunCfg,
        taggedBranchDispatchCfg, taggedBranchDispatchLeftRunState]
      rfl
  | halt =>
      simp [taggedBranchLeftStmt, taggedBranchDispatchLeftRunCfg,
        taggedBranchDispatchCfg]
      rfl

lemma taggedBranchDispatchMachine_left_step
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (cfg next : tmLeft.Cfg)
    (source : List (Bool ⊕ α))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ)
    (hStep : tmLeft.step cfg = some next) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).step
        (taggedBranchDispatchLeftRunCfg α γ tmLeft tmRight readLeft readRight writeLeft
          writeRight cfg source right leftTemp rightTemp output outputTemp) =
      some
        (taggedBranchDispatchLeftRunCfg α γ tmLeft tmRight readLeft readRight writeLeft
          writeRight next source right leftTemp rightTemp output outputTemp) := by
  letI := tmLeft.kDecidableEq
  letI := tmRight.kDecidableEq
  letI dispatchDec : DecidableEq (TaggedBranchDispatchStack tmLeft.K tmRight.K) :=
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight writeLeft
      writeRight).kDecidableEq
  cases cfg with
  | mk label var stk =>
      cases label with
      | none =>
          simp [Turing.FinTM2.step, Turing.TM2.step] at hStep
      | some label =>
          have hNext :
              next = @Turing.TM2.stepAux tmLeft.K tmLeft.Γ tmLeft.Λ tmLeft.σ
                tmLeft.kDecidableEq (tmLeft.m label) var stk := by
            have hSome :
                some (@Turing.TM2.stepAux tmLeft.K tmLeft.Γ tmLeft.Λ tmLeft.σ
                  tmLeft.kDecidableEq (tmLeft.m label) var stk) = some next := by
              simpa [Turing.FinTM2.step, Turing.TM2.step] using hStep
            exact (Option.some.inj hSome).symm
          subst next
          change
            (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
              writeLeft writeRight).step
                (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft
                  writeRight (.runLeft label) (.leftRun var) source stk right leftTemp
                  rightTemp output outputTemp) =
              some
                (taggedBranchDispatchLeftRunCfg α γ tmLeft tmRight readLeft readRight
                  writeLeft writeRight
                  (@Turing.TM2.stepAux tmLeft.K tmLeft.Γ tmLeft.Λ tmLeft.σ
                    tmLeft.kDecidableEq (tmLeft.m label) var stk)
                  source right leftTemp rightTemp output outputTemp)
          simp only [taggedBranchDispatchMachine, taggedBranchDispatchCfg,
            Turing.FinTM2.step, Turing.TM2.step]
          apply congrArg some
          convert
            taggedBranchLeftStmt_stepAux α γ tmLeft tmRight readLeft readRight writeLeft
              writeRight (tmLeft.m label) var source stk right leftTemp rightTemp output
              outputTemp using 1

def taggedBranchDispatch_left_evalsToInTime
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    {cfg next : tmLeft.Cfg}
    (source : List (Bool ⊕ α))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ)
    {time : Nat}
    (h : StateTransition.EvalsToInTime tmLeft.step cfg (some next) time) :
    StateTransition.EvalsToInTime
      (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight).step
      (taggedBranchDispatchLeftRunCfg α γ tmLeft tmRight readLeft readRight writeLeft
        writeRight cfg source right leftTemp rightTemp output outputTemp)
      (some
        (taggedBranchDispatchLeftRunCfg α γ tmLeft tmRight readLeft readRight writeLeft
          writeRight next source right leftTemp rightTemp output outputTemp))
      time := by
  simpa using
    TM2Programs.evalsToInTime_map_some
      (fun cfg => taggedBranchDispatchLeftRunCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight cfg source right leftTemp rightTemp output outputTemp)
      (fun s s' hStep =>
        taggedBranchDispatchMachine_left_step α γ tmLeft tmRight readLeft readRight
          writeLeft writeRight s s' source right leftTemp rightTemp output outputTemp hStep)
      h

def taggedBranchDispatchRightRunCfg
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (cfg : tmRight.Cfg)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).Cfg :=
  match cfg.l with
  | some label =>
      taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
        (.runRight label) (.rightRun cfg.var) source left cfg.stk leftTemp rightTemp output
        outputTemp
  | none =>
      taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
        .readRightOutput (.output none) source left cfg.stk leftTemp rightTemp output outputTemp

lemma taggedBranchRightStmt_stepAux
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (q : Turing.TM2.Stmt tmRight.Γ tmRight.Λ tmRight.σ)
    (v : tmRight.σ)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    @Turing.TM2.stepAux (TaggedBranchDispatchStack tmLeft.K tmRight.K)
        (taggedBranchDispatchAlphabet α γ tmLeft tmRight)
        (TaggedBranchDispatchLabel tmLeft.Λ tmRight.Λ
          (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
        (TaggedBranchDispatchState tmLeft.σ tmRight.σ
          (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
        (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
          writeLeft writeRight).kDecidableEq
        (taggedBranchRightStmt α γ tmLeft tmRight writeRight q) (.rightRun v)
        (taggedBranchDispatchStacks α γ tmLeft tmRight source left right leftTemp
          rightTemp output outputTemp) =
      taggedBranchDispatchRightRunCfg α γ tmLeft tmRight readLeft readRight writeLeft
        writeRight (@Turing.TM2.stepAux tmRight.K tmRight.Γ tmRight.Λ tmRight.σ
          tmRight.kDecidableEq q v right) source left leftTemp rightTemp output outputTemp := by
  letI := tmLeft.kDecidableEq
  letI := tmRight.kDecidableEq
  letI dispatchDec : DecidableEq (TaggedBranchDispatchStack tmLeft.K tmRight.K) :=
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight writeLeft
      writeRight).kDecidableEq
  induction q generalizing v right with
  | push k f q ih =>
      have hstk :
          @Function.update (TaggedBranchDispatchStack tmLeft.K tmRight.K)
              (fun s => List (taggedBranchDispatchAlphabet α γ tmLeft tmRight s))
              (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight writeLeft
                writeRight).kDecidableEq
              (taggedBranchDispatchStacks α γ tmLeft tmRight source left right leftTemp
                rightTemp output outputTemp)
              (TaggedBranchDispatchStack.right k) (f v :: right k) =
            taggedBranchDispatchStacks α γ tmLeft tmRight source left
              (@Function.update tmRight.K (fun k => List (tmRight.Γ k))
                tmRight.kDecidableEq right k (f v :: right k))
              leftTemp rightTemp output outputTemp := by
        funext s
        cases s with
        | source => rfl
        | left k' => rfl
        | right k' =>
            by_cases hk : k' = k
            · subst k'
              simp [Function.update]
            · simp [Function.update, hk]
        | leftInputTemp => rfl
        | rightInputTemp => rfl
        | output => rfl
        | outputTemp => rfl
      simpa [taggedBranchRightStmt, taggedBranchDispatchRightRunState, hstk] using
        ih v (@Function.update tmRight.K (fun k => List (tmRight.Γ k))
          tmRight.kDecidableEq right k (f v :: right k))
  | peek k f q ih =>
      simpa [taggedBranchRightStmt, taggedBranchDispatchRightRunState] using
        ih (f v (right k).head?) right
  | pop k f q ih =>
      have hstk :
          @Function.update (TaggedBranchDispatchStack tmLeft.K tmRight.K)
              (fun s => List (taggedBranchDispatchAlphabet α γ tmLeft tmRight s))
              (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight writeLeft
                writeRight).kDecidableEq
              (taggedBranchDispatchStacks α γ tmLeft tmRight source left right leftTemp
                rightTemp output outputTemp)
              (TaggedBranchDispatchStack.right k) (right k).tail =
            taggedBranchDispatchStacks α γ tmLeft tmRight source left
              (@Function.update tmRight.K (fun k => List (tmRight.Γ k))
                tmRight.kDecidableEq right k (right k).tail)
              leftTemp rightTemp output outputTemp := by
        funext s
        cases s with
        | source => rfl
        | left k' => rfl
        | right k' =>
            by_cases hk : k' = k
            · subst k'
              simp [Function.update]
            · simp [Function.update, hk]
        | leftInputTemp => rfl
        | rightInputTemp => rfl
        | output => rfl
        | outputTemp => rfl
      simpa [taggedBranchRightStmt, taggedBranchDispatchRightRunState, hstk] using
        ih (f v (right k).head?) (@Function.update tmRight.K (fun k => List (tmRight.Γ k))
          tmRight.kDecidableEq right k (right k).tail)
  | load f q ih =>
      simpa [taggedBranchRightStmt, taggedBranchDispatchRightRunState] using
        ih (f v) right
  | branch f qTrue qFalse ihTrue ihFalse =>
      by_cases hf : f v
      · simpa [taggedBranchRightStmt, taggedBranchDispatchRightRunState, hf] using
          ihTrue v right
      · simpa [taggedBranchRightStmt, taggedBranchDispatchRightRunState, hf] using
          ihFalse v right
  | goto f =>
      simp [taggedBranchRightStmt, taggedBranchDispatchRightRunCfg,
        taggedBranchDispatchCfg, taggedBranchDispatchRightRunState]
      rfl
  | halt =>
      simp [taggedBranchRightStmt, taggedBranchDispatchRightRunCfg,
        taggedBranchDispatchCfg]
      rfl

lemma taggedBranchDispatchMachine_right_step
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (cfg next : tmRight.Cfg)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ)
    (hStep : tmRight.step cfg = some next) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).step
        (taggedBranchDispatchRightRunCfg α γ tmLeft tmRight readLeft readRight writeLeft
          writeRight cfg source left leftTemp rightTemp output outputTemp) =
      some
        (taggedBranchDispatchRightRunCfg α γ tmLeft tmRight readLeft readRight writeLeft
          writeRight next source left leftTemp rightTemp output outputTemp) := by
  letI := tmLeft.kDecidableEq
  letI := tmRight.kDecidableEq
  letI dispatchDec : DecidableEq (TaggedBranchDispatchStack tmLeft.K tmRight.K) :=
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight writeLeft
      writeRight).kDecidableEq
  cases cfg with
  | mk label var stk =>
      cases label with
      | none =>
          simp [Turing.FinTM2.step, Turing.TM2.step] at hStep
      | some label =>
          have hNext :
              next = @Turing.TM2.stepAux tmRight.K tmRight.Γ tmRight.Λ tmRight.σ
                tmRight.kDecidableEq (tmRight.m label) var stk := by
            have hSome :
                some (@Turing.TM2.stepAux tmRight.K tmRight.Γ tmRight.Λ tmRight.σ
                  tmRight.kDecidableEq (tmRight.m label) var stk) = some next := by
              simpa [Turing.FinTM2.step, Turing.TM2.step] using hStep
            exact (Option.some.inj hSome).symm
          subst next
          change
            (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
              writeLeft writeRight).step
                (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft
                  writeRight (.runRight label) (.rightRun var) source left stk leftTemp
                  rightTemp output outputTemp) =
              some
                (taggedBranchDispatchRightRunCfg α γ tmLeft tmRight readLeft readRight
                  writeLeft writeRight
                  (@Turing.TM2.stepAux tmRight.K tmRight.Γ tmRight.Λ tmRight.σ
                    tmRight.kDecidableEq (tmRight.m label) var stk)
                  source left leftTemp rightTemp output outputTemp)
          simp only [taggedBranchDispatchMachine, taggedBranchDispatchCfg,
            Turing.FinTM2.step, Turing.TM2.step]
          apply congrArg some
          convert
            taggedBranchRightStmt_stepAux α γ tmLeft tmRight readLeft readRight writeLeft
              writeRight (tmRight.m label) var source left stk leftTemp rightTemp output
              outputTemp using 1

def taggedBranchDispatch_right_evalsToInTime
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    {cfg next : tmRight.Cfg}
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ)
    {time : Nat}
    (h : StateTransition.EvalsToInTime tmRight.step cfg (some next) time) :
    StateTransition.EvalsToInTime
      (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight).step
      (taggedBranchDispatchRightRunCfg α γ tmLeft tmRight readLeft readRight writeLeft
        writeRight cfg source left leftTemp rightTemp output outputTemp)
      (some
        (taggedBranchDispatchRightRunCfg α γ tmLeft tmRight readLeft readRight writeLeft
          writeRight next source left leftTemp rightTemp output outputTemp))
      time := by
  simpa using
    TM2Programs.evalsToInTime_map_some
      (fun cfg => taggedBranchDispatchRightRunCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight cfg source left leftTemp rightTemp output outputTemp)
      (fun s s' hStep =>
        taggedBranchDispatchMachine_right_step α γ tmLeft tmRight readLeft readRight
          writeLeft writeRight s s' source left leftTemp rightTemp output outputTemp hStep)
      h

def taggedBranchDispatch_outputs_left
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (payload : List α)
    (leftOutput : List (tmLeft.Γ tmLeft.k₁))
    (time : Nat)
    (hLeft :
      Turing.TM2OutputsInTime tmLeft (payload.map readLeft) (some leftOutput) time) :
    Turing.TM2OutputsInTime
      (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight)
      (Sum.inl false :: payload.map Sum.inr)
      (some (leftOutput.map writeLeft))
      (time + 4 * payload.length + 4 * leftOutput.length + 6) := by
  let tm := taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
    writeLeft writeRight
  let emptyLeft : (k : tmLeft.K) → List (tmLeft.Γ k) := fun _ => []
  let emptyRight : (k : tmRight.K) → List (tmRight.Γ k) := fun _ => []
  let input : List (Bool ⊕ α) := Sum.inl false :: payload.map Sum.inr
  let leftInput := payload.map readLeft
  let c₁ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft
    writeRight .readLeftPayload (.tag (some false)) (payload.map Sum.inr) emptyLeft
    emptyRight [] [] [] []
  let c₂ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft
    writeRight .drainLeftInput (.leftInput none) [] emptyLeft emptyRight leftInput.reverse [] [] []
  let c₃ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft
    writeRight (.runLeft tmLeft.main) (.leftRun tmLeft.initialState) []
    (Function.update emptyLeft tmLeft.k₀ leftInput) emptyRight [] [] [] []
  let c₄ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft
    writeRight .readLeftOutput (.output none) []
    (Function.update emptyLeft tmLeft.k₁ leftOutput) emptyRight [] [] [] []
  let c₅ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft
    writeRight .drainOutput (.output none) []
    (Function.update emptyLeft tmLeft.k₁ []) emptyRight [] [] []
    (leftOutput.map writeLeft).reverse
  let done := taggedBranchDispatchHalt α γ tmLeft tmRight readLeft readRight writeLeft
    writeRight (leftOutput.map writeLeft)
  have hReadTag : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some c₁) 1 := by
    simpa [tm, input, c₁, emptyLeft, emptyRight, taggedBranchDispatch_initList] using
      TM2Programs.evalsToInTimeOne
        (taggedBranchDispatch_readTag_step_false α γ tmLeft tmRight readLeft readRight
          writeLeft writeRight (payload.map Sum.inr) emptyLeft emptyRight [] [] [] [])
  have hReadPayload : StateTransition.EvalsToInTime tm.step c₁ (some c₂)
      (2 * payload.length + 1) := by
    simpa [tm, c₁, c₂, emptyLeft, emptyRight, leftInput] using
      taggedBranchDispatch_readLeftPayload_run α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight (.tag (some false)) payload emptyLeft emptyRight [] [] [] []
  have hDrainInput : StateTransition.EvalsToInTime tm.step c₂ (some c₃)
      (2 * leftInput.reverse.length + 1) := by
    simpa [tm, c₂, c₃, emptyLeft, emptyRight, leftInput, List.reverse_reverse] using
      taggedBranchDispatch_drainLeftInput_run α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight [] emptyLeft emptyRight (.leftInput none) leftInput.reverse [] [] []
  have hRunLeft : StateTransition.EvalsToInTime tm.step c₃ (some c₄) time := by
    have hInitStk :
        (Turing.initList tmLeft leftInput).stk =
          Function.update emptyLeft tmLeft.k₀ leftInput := by
      funext k
      by_cases hk : k = tmLeft.k₀
      · subst k
        simp [Turing.initList, Function.update]
      · simp [Turing.initList, emptyLeft, Function.update, hk]
    have hHaltStk :
        (Turing.haltList tmLeft leftOutput).stk =
          Function.update emptyLeft tmLeft.k₁ leftOutput := by
      funext k
      by_cases hk : k = tmLeft.k₁
      · subst k
        simp [Turing.haltList, Function.update]
      · simp [Turing.haltList, emptyLeft, Function.update, hk]
    have hLift :=
      taggedBranchDispatch_left_evalsToInTime α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight (source := []) (right := emptyRight) (leftTemp := [])
        (rightTemp := []) (output := []) (outputTemp := []) hLeft
    simpa [Turing.TM2OutputsInTime, c₃, c₄, leftInput, emptyRight,
      taggedBranchDispatchLeftRunCfg, hInitStk, hHaltStk] using hLift
  have hReadOutput : StateTransition.EvalsToInTime tm.step c₄ (some c₅)
      (2 * leftOutput.length + 1) := by
    simpa [tm, c₄, c₅, emptyLeft, emptyRight] using
      taggedBranchDispatch_readLeftOutput_run α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight [] emptyLeft emptyRight (.output none) leftOutput [] [] [] []
  have hDrainOutput : StateTransition.EvalsToInTime tm.step c₅ (some done)
      (2 * (leftOutput.map writeLeft).reverse.length + 2) := by
    have hEmptyLeft :
        Function.update emptyLeft tmLeft.k₁ ([] : List (tmLeft.Γ tmLeft.k₁)) =
          emptyLeft := by
      funext k
      by_cases hk : k = tmLeft.k₁
      · subst k
        simp [emptyLeft, Function.update]
      · simp [emptyLeft, Function.update, hk]
    have hFinal :
        taggedBranchDispatchFinalCfg α γ tmLeft tmRight readLeft readRight writeLeft
            writeRight [] emptyLeft emptyRight [] [] (leftOutput.map writeLeft) [] =
          done := by
      simp [taggedBranchDispatchFinalCfg, taggedBranchDispatchHalt,
        done, emptyLeft, emptyRight]
      congr
      funext k
      cases k <;> rfl
    simpa [tm, c₅, done, emptyLeft, emptyRight, hEmptyLeft, hFinal,
      List.reverse_reverse, taggedBranchDispatch_haltList] using
      taggedBranchDispatch_drainOutput_run α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight [] emptyLeft emptyRight (.output none) [] [] []
        (leftOutput.map writeLeft).reverse
  have hTagPayload : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some c₂) ((2 * payload.length + 1) + 1) :=
    StateTransition.EvalsToInTime.trans tm.step 1 (2 * payload.length + 1)
      (Turing.initList tm input) c₁ (some c₂) hReadTag hReadPayload
  have hToRun : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some c₃) ((2 * leftInput.reverse.length + 1) + ((2 * payload.length + 1) + 1)) :=
    StateTransition.EvalsToInTime.trans tm.step ((2 * payload.length + 1) + 1)
      (2 * leftInput.reverse.length + 1) (Turing.initList tm input) c₂ (some c₃)
      hTagPayload hDrainInput
  have hThroughRun : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some c₄) (time + ((2 * leftInput.reverse.length + 1) + ((2 * payload.length + 1) + 1))) :=
    StateTransition.EvalsToInTime.trans tm.step
      ((2 * leftInput.reverse.length + 1) + ((2 * payload.length + 1) + 1)) time
      (Turing.initList tm input) c₃ (some c₄) hToRun hRunLeft
  have hToDrainOutput : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some c₅)
      ((2 * leftOutput.length + 1) +
        (time + ((2 * leftInput.reverse.length + 1) + ((2 * payload.length + 1) + 1)))) :=
    StateTransition.EvalsToInTime.trans tm.step
      (time + ((2 * leftInput.reverse.length + 1) + ((2 * payload.length + 1) + 1)))
      (2 * leftOutput.length + 1) (Turing.initList tm input) c₄ (some c₅)
      hThroughRun hReadOutput
  have hAll : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some done)
      ((2 * (leftOutput.map writeLeft).reverse.length + 2) +
        ((2 * leftOutput.length + 1) +
          (time + ((2 * leftInput.reverse.length + 1) + ((2 * payload.length + 1) + 1))))) :=
    StateTransition.EvalsToInTime.trans tm.step
      ((2 * leftOutput.length + 1) +
        (time + ((2 * leftInput.reverse.length + 1) + ((2 * payload.length + 1) + 1))))
      (2 * (leftOutput.map writeLeft).reverse.length + 2)
      (Turing.initList tm input) c₅ (some done) hToDrainOutput hDrainOutput
  change StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
    (some (Turing.haltList tm (leftOutput.map writeLeft)))
    (time + 4 * payload.length + 4 * leftOutput.length + 6)
  rw [taggedBranchDispatch_haltList]
  exact TM2Programs.evalsToInTime_mono hAll (by
    simp [leftInput, List.length_reverse]
    omega)

def taggedBranchDispatch_outputs_right
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (payload : List α)
    (rightOutput : List (tmRight.Γ tmRight.k₁))
    (time : Nat)
    (hRight :
      Turing.TM2OutputsInTime tmRight (payload.map readRight) (some rightOutput) time) :
    Turing.TM2OutputsInTime
      (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight)
      (Sum.inl true :: payload.map Sum.inr)
      (some (rightOutput.map writeRight))
      (time + 4 * payload.length + 4 * rightOutput.length + 6) := by
  let tm := taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
    writeLeft writeRight
  let emptyLeft : (k : tmLeft.K) → List (tmLeft.Γ k) := fun _ => []
  let emptyRight : (k : tmRight.K) → List (tmRight.Γ k) := fun _ => []
  let input : List (Bool ⊕ α) := Sum.inl true :: payload.map Sum.inr
  let rightInput := payload.map readRight
  let c₁ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft
    writeRight .readRightPayload (.tag (some true)) (payload.map Sum.inr) emptyLeft
    emptyRight [] [] [] []
  let c₂ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft
    writeRight .drainRightInput (.rightInput none) [] emptyLeft emptyRight []
    rightInput.reverse [] []
  let c₃ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft
    writeRight (.runRight tmRight.main) (.rightRun tmRight.initialState) [] emptyLeft
    (Function.update emptyRight tmRight.k₀ rightInput) [] [] [] []
  let c₄ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft
    writeRight .readRightOutput (.output none) [] emptyLeft
    (Function.update emptyRight tmRight.k₁ rightOutput) [] [] [] []
  let c₅ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft
    writeRight .drainOutput (.output none) [] emptyLeft
    (Function.update emptyRight tmRight.k₁ []) [] [] []
    (rightOutput.map writeRight).reverse
  let done := taggedBranchDispatchHalt α γ tmLeft tmRight readLeft readRight writeLeft
    writeRight (rightOutput.map writeRight)
  have hReadTag : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some c₁) 1 := by
    simpa [tm, input, c₁, emptyLeft, emptyRight, taggedBranchDispatch_initList] using
      TM2Programs.evalsToInTimeOne
        (taggedBranchDispatch_readTag_step_true α γ tmLeft tmRight readLeft readRight
          writeLeft writeRight (payload.map Sum.inr) emptyLeft emptyRight [] [] [] [])
  have hReadPayload : StateTransition.EvalsToInTime tm.step c₁ (some c₂)
      (2 * payload.length + 1) := by
    simpa [tm, c₁, c₂, emptyLeft, emptyRight, rightInput] using
      taggedBranchDispatch_readRightPayload_run α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight (.tag (some true)) payload emptyLeft emptyRight [] [] [] []
  have hDrainInput : StateTransition.EvalsToInTime tm.step c₂ (some c₃)
      (2 * rightInput.reverse.length + 1) := by
    simpa [tm, c₂, c₃, emptyLeft, emptyRight, rightInput, List.reverse_reverse] using
      taggedBranchDispatch_drainRightInput_run α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight [] emptyLeft emptyRight (.rightInput none) [] rightInput.reverse [] []
  have hRunRight : StateTransition.EvalsToInTime tm.step c₃ (some c₄) time := by
    have hInitStk :
        (Turing.initList tmRight rightInput).stk =
          Function.update emptyRight tmRight.k₀ rightInput := by
      funext k
      by_cases hk : k = tmRight.k₀
      · subst k
        simp [Turing.initList, Function.update]
      · simp [Turing.initList, emptyRight, Function.update, hk]
    have hHaltStk :
        (Turing.haltList tmRight rightOutput).stk =
          Function.update emptyRight tmRight.k₁ rightOutput := by
      funext k
      by_cases hk : k = tmRight.k₁
      · subst k
        simp [Turing.haltList, Function.update]
      · simp [Turing.haltList, emptyRight, Function.update, hk]
    have hLift :=
      taggedBranchDispatch_right_evalsToInTime α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight (source := []) (left := emptyLeft) (leftTemp := [])
        (rightTemp := []) (output := []) (outputTemp := []) hRight
    simpa [Turing.TM2OutputsInTime, c₃, c₄, rightInput, emptyLeft,
      taggedBranchDispatchRightRunCfg, hInitStk, hHaltStk] using hLift
  have hReadOutput : StateTransition.EvalsToInTime tm.step c₄ (some c₅)
      (2 * rightOutput.length + 1) := by
    simpa [tm, c₄, c₅, emptyLeft, emptyRight] using
      taggedBranchDispatch_readRightOutput_run α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight [] emptyLeft emptyRight (.output none) rightOutput [] [] [] []
  have hDrainOutput : StateTransition.EvalsToInTime tm.step c₅ (some done)
      (2 * (rightOutput.map writeRight).reverse.length + 2) := by
    have hEmptyRight :
        Function.update emptyRight tmRight.k₁ ([] : List (tmRight.Γ tmRight.k₁)) =
          emptyRight := by
      funext k
      by_cases hk : k = tmRight.k₁
      · subst k
        simp [emptyRight, Function.update]
      · simp [emptyRight, Function.update, hk]
    have hFinal :
        taggedBranchDispatchFinalCfg α γ tmLeft tmRight readLeft readRight writeLeft
            writeRight [] emptyLeft emptyRight [] [] (rightOutput.map writeRight) [] =
          done := by
      simp [taggedBranchDispatchFinalCfg, taggedBranchDispatchHalt,
        done, emptyLeft, emptyRight]
      congr
      funext k
      cases k <;> rfl
    simpa [tm, c₅, done, emptyLeft, emptyRight, hEmptyRight, hFinal,
      List.reverse_reverse, taggedBranchDispatch_haltList] using
      taggedBranchDispatch_drainOutput_run α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight [] emptyLeft emptyRight (.output none) [] [] []
        (rightOutput.map writeRight).reverse
  have hTagPayload : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some c₂) ((2 * payload.length + 1) + 1) :=
    StateTransition.EvalsToInTime.trans tm.step 1 (2 * payload.length + 1)
      (Turing.initList tm input) c₁ (some c₂) hReadTag hReadPayload
  have hToRun : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some c₃) ((2 * rightInput.reverse.length + 1) + ((2 * payload.length + 1) + 1)) :=
    StateTransition.EvalsToInTime.trans tm.step ((2 * payload.length + 1) + 1)
      (2 * rightInput.reverse.length + 1) (Turing.initList tm input) c₂ (some c₃)
      hTagPayload hDrainInput
  have hThroughRun : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some c₄)
      (time + ((2 * rightInput.reverse.length + 1) + ((2 * payload.length + 1) + 1))) :=
    StateTransition.EvalsToInTime.trans tm.step
      ((2 * rightInput.reverse.length + 1) + ((2 * payload.length + 1) + 1)) time
      (Turing.initList tm input) c₃ (some c₄) hToRun hRunRight
  have hToDrainOutput : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some c₅)
      ((2 * rightOutput.length + 1) +
        (time + ((2 * rightInput.reverse.length + 1) + ((2 * payload.length + 1) + 1)))) :=
    StateTransition.EvalsToInTime.trans tm.step
      (time + ((2 * rightInput.reverse.length + 1) + ((2 * payload.length + 1) + 1)))
      (2 * rightOutput.length + 1) (Turing.initList tm input) c₄ (some c₅)
      hThroughRun hReadOutput
  have hAll : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some done)
      ((2 * (rightOutput.map writeRight).reverse.length + 2) +
        ((2 * rightOutput.length + 1) +
          (time + ((2 * rightInput.reverse.length + 1) + ((2 * payload.length + 1) + 1))))) :=
    StateTransition.EvalsToInTime.trans tm.step
      ((2 * rightOutput.length + 1) +
        (time + ((2 * rightInput.reverse.length + 1) + ((2 * payload.length + 1) + 1))))
      (2 * (rightOutput.map writeRight).reverse.length + 2)
      (Turing.initList tm input) c₅ (some done) hToDrainOutput hDrainOutput
  change StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
    (some (Turing.haltList tm (rightOutput.map writeRight)))
    (time + 4 * payload.length + 4 * rightOutput.length + 6)
  rw [taggedBranchDispatch_haltList]
  exact TM2Programs.evalsToInTime_mono hAll (by
    simp [rightInput, List.length_reverse]
    omega)

/-- Polynomial bound for the shared-payload tagged branch dispatcher. -/
noncomputable def taggedBranchDispatchTimePolynomial
    (tmLeft tmRight : Turing.FinTM2) (pLeft pRight : Polynomial Nat) : Polynomial Nat :=
  pLeft * Polynomial.C (4 * TM2Programs.finTM2StepPushBound tmLeft + 1) +
    pRight * Polynomial.C (4 * TM2Programs.finTM2StepPushBound tmRight + 1) +
      Polynomial.C 8 * Polynomial.X + Polynomial.C 6

@[simp] lemma taggedBranchDispatchTimePolynomial_eval
    (tmLeft tmRight : Turing.FinTM2) (pLeft pRight : Polynomial Nat) (n : Nat) :
    (taggedBranchDispatchTimePolynomial tmLeft tmRight pLeft pRight).eval n =
      pLeft.eval n * (4 * TM2Programs.finTM2StepPushBound tmLeft + 1) +
        pRight.eval n * (4 * TM2Programs.finTM2StepPushBound tmRight + 1) +
          8 * n + 6 := by
  simp [taggedBranchDispatchTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Nat.add_assoc]


end Karp21
end ComplexityReduction
