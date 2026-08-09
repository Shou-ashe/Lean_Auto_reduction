import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.SplitWith.TaggedDispatch.Part1

namespace ComplexityReduction
namespace Karp21
open ComplexityReduction
open Turing.TM2.Stmt

def taggedBranchDispatch_readRightPayload_run
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (state : TaggedBranchDispatchState tmLeft.σ tmRight.σ
      (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
    (payload : List α)
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    StateTransition.EvalsToInTime
      (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight).step
      (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
        .readRightPayload state (payload.map Sum.inr) left right
        leftTemp rightTemp output outputTemp)
      (some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .drainRightInput (.rightInput none) [] left right leftTemp
          ((payload.map readRight).reverse ++ rightTemp) output outputTemp))
      (2 * payload.length + 1) := by
  induction payload generalizing state rightTemp with
  | nil =>
      simpa using
        TM2Programs.evalsToInTimeOne
          (taggedBranchDispatch_readRightPayload_step_nil α γ tmLeft tmRight readLeft
            readRight writeLeft writeRight state left right leftTemp rightTemp output outputTemp)
  | cons a payload ih =>
      let tm := taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight
      let b := readRight a
      let c₀ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight .readRightPayload state
        (Sum.inr a :: payload.map Sum.inr) left right leftTemp rightTemp output outputTemp
      let c₁ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight (.pushRightTemp b) (.rightInput (some b))
        (payload.map Sum.inr) left right leftTemp rightTemp output outputTemp
      let c₂ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight .readRightPayload (.rightInput (some b))
        (payload.map Sum.inr) left right leftTemp (b :: rightTemp) output outputTemp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne
          (taggedBranchDispatch_readRightPayload_step_cons α γ tmLeft tmRight readLeft
            readRight writeLeft writeRight state a (payload.map Sum.inr) left right
            leftTemp rightTemp output outputTemp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        TM2Programs.evalsToInTimeOne
          (taggedBranchDispatch_pushRightTemp_step α γ tmLeft tmRight readLeft readRight
            writeLeft writeRight b (payload.map Sum.inr) left right leftTemp rightTemp
            output outputTemp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some
            (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft
              writeRight .drainRightInput (.rightInput none) [] left right leftTemp
              ((payload.map readRight).reverse ++ (b :: rightTemp)) output outputTemp))
          (2 * payload.length + 1) :=
        by simpa [tm, c₂] using ih (.rightInput (some b)) (b :: rightTemp)
      simpa [tm, c₀, c₁, c₂, b, List.map_cons, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * payload.length + 1)
          c₀ c₂
          (some
            (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft
              writeRight .drainRightInput (.rightInput none) [] left right leftTemp
              ((payload.map readRight).reverse ++ (b :: rightTemp)) output outputTemp))
          h₁₂ hTail

lemma taggedBranchDispatch_drainRightInput_step_cons
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (b : tmRight.Γ tmRight.k₀)
    (state : TaggedBranchDispatchState tmLeft.σ tmRight.σ
      (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).step
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .drainRightInput state source left right leftTemp (b :: rightTemp)
          output outputTemp) =
      some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          (.pushRightInput b) (.rightInput (some b)) source left right leftTemp rightTemp
          output outputTemp) := by
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg,
    taggedBranchDispatchRightInputState]
  congr
  funext k
  cases k <;> rfl

lemma taggedBranchDispatch_drainRightInput_step_nil
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (state : TaggedBranchDispatchState tmLeft.σ tmRight.σ
      (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (output outputTemp : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).step
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .drainRightInput state source left right leftTemp [] output outputTemp) =
      some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          (.runRight tmRight.main) (.rightRun tmRight.initialState) source left right leftTemp
          [] output outputTemp) := by
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg,
    taggedBranchDispatchRightInputState]
  congr
  funext k
  cases k <;> rfl

lemma taggedBranchDispatch_pushRightInput_step
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (b : tmRight.Γ tmRight.k₀)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).step
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          (.pushRightInput b) (.rightInput (some b)) source left right leftTemp rightTemp
          output outputTemp) =
      some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .drainRightInput (.rightInput (some b)) source left
          (Function.update right tmRight.k₀ (b :: right tmRight.k₀)) leftTemp rightTemp
          output outputTemp) := by
  letI := tmRight.kDecidableEq
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg]
  congr
  funext k
  cases k with
  | source => rfl
  | left k => rfl
  | right k =>
      by_cases hk : k = tmRight.k₀
      · subst k
        simp [Function.update]
      · simp [Function.update, hk]
  | leftInputTemp => rfl
  | rightInputTemp => rfl
  | output => rfl
  | outputTemp => rfl

def taggedBranchDispatch_drainRightInput_run
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (state : TaggedBranchDispatchState tmLeft.σ tmRight.σ
      (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    StateTransition.EvalsToInTime
      (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight).step
      (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
        .drainRightInput state source left right leftTemp rightTemp output outputTemp)
      (some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          (.runRight tmRight.main) (.rightRun tmRight.initialState) source left
          (Function.update right tmRight.k₀ (rightTemp.reverse ++ right tmRight.k₀)) leftTemp
          [] output outputTemp))
      (2 * rightTemp.length + 1) := by
  letI := tmRight.kDecidableEq
  induction rightTemp generalizing right state with
  | nil =>
      simpa [Function.update] using
        TM2Programs.evalsToInTimeOne
          (taggedBranchDispatch_drainRightInput_step_nil α γ tmLeft tmRight readLeft
            readRight writeLeft writeRight state source left right leftTemp output outputTemp)
  | cons b rightTemp ih =>
      let tm := taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight
      let c₀ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight .drainRightInput state source left right leftTemp
        (b :: rightTemp) output outputTemp
      let c₁ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight (.pushRightInput b) (.rightInput (some b)) source left right
        leftTemp rightTemp output outputTemp
      let right' := Function.update right tmRight.k₀ (b :: right tmRight.k₀)
      let c₂ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight .drainRightInput (.rightInput (some b)) source left right'
        leftTemp rightTemp output outputTemp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne
          (taggedBranchDispatch_drainRightInput_step_cons α γ tmLeft tmRight readLeft
            readRight writeLeft writeRight b state source left right leftTemp rightTemp output
            outputTemp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        TM2Programs.evalsToInTimeOne
          (taggedBranchDispatch_pushRightInput_step α γ tmLeft tmRight readLeft readRight
            writeLeft writeRight b source left right leftTemp rightTemp output outputTemp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some
            (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft
              writeRight (.runRight tmRight.main) (.rightRun tmRight.initialState) source left
              (Function.update right' tmRight.k₀ (rightTemp.reverse ++ right' tmRight.k₀))
              leftTemp [] output outputTemp))
          (2 * rightTemp.length + 1) := by
        simpa [tm, c₂, right'] using
          ih right' (.rightInput (some b))
      simpa [tm, c₀, c₁, c₂, right', Function.update, List.reverse_cons,
        List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * rightTemp.length + 1)
          c₀ c₂
          (some
            (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft
              writeRight (.runRight tmRight.main) (.rightRun tmRight.initialState) source left
              (Function.update right' tmRight.k₀ (rightTemp.reverse ++ right' tmRight.k₀))
              leftTemp [] output outputTemp))
          h₁₂ hTail

def taggedBranchDispatchFinalCfg (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).Cfg where
  l := none
  var := .tag none
  stk :=
    taggedBranchDispatchStacks α γ tmLeft tmRight source left right leftTemp rightTemp
      output outputTemp

lemma taggedBranchDispatch_drainOutput_step_cons
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (b : γ)
    (state : TaggedBranchDispatchState tmLeft.σ tmRight.σ
      (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).step
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .drainOutput state source left right leftTemp rightTemp output
          (b :: outputTemp)) =
      some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          (.pushOutput b) (.output (some b)) source left right leftTemp rightTemp output
          outputTemp) := by
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg,
    taggedBranchDispatchOutputState]
  congr
  funext k
  cases k <;> rfl

lemma taggedBranchDispatch_pushOutput_step
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (b : γ)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).step
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          (.pushOutput b) (.output (some b)) source left right leftTemp rightTemp output
          outputTemp) =
      some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .drainOutput (.output (some b)) source left right leftTemp rightTemp (b :: output)
          outputTemp) := by
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg]
  congr
  funext k
  cases k <;> rfl

lemma taggedBranchDispatch_drainOutput_step_nil
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (state : TaggedBranchDispatchState tmLeft.σ tmRight.σ
      (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).step
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .drainOutput state source left right leftTemp rightTemp output []) =
      some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .invalid (.output none) source left right leftTemp rightTemp output []) := by
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg,
    taggedBranchDispatchOutputState]
  congr
  funext k
  cases k <;> rfl

lemma taggedBranchDispatch_invalid_step
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).step
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .invalid (.output none) source left right leftTemp rightTemp output outputTemp) =
      some
        (taggedBranchDispatchFinalCfg α γ tmLeft tmRight readLeft readRight writeLeft
          writeRight source left right leftTemp rightTemp output outputTemp) := by
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg, taggedBranchDispatchFinalCfg]
  rfl

def taggedBranchDispatch_drainOutput_run
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (state : TaggedBranchDispatchState tmLeft.σ tmRight.σ
      (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    StateTransition.EvalsToInTime
      (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight).step
      (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
        .drainOutput state source left right leftTemp rightTemp output outputTemp)
      (some
        (taggedBranchDispatchFinalCfg α γ tmLeft tmRight readLeft readRight writeLeft
          writeRight source left right leftTemp rightTemp (outputTemp.reverse ++ output) []))
      (2 * outputTemp.length + 2) := by
  induction outputTemp generalizing output state with
  | nil =>
      let tm := taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight
      let c₀ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight .drainOutput state source left right leftTemp rightTemp
        output []
      let c₁ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight .invalid (.output none) source left right leftTemp rightTemp output []
      let done := taggedBranchDispatchFinalCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight source left right leftTemp rightTemp output []
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne
          (taggedBranchDispatch_drainOutput_step_nil α γ tmLeft tmRight readLeft
            readRight writeLeft writeRight state source left right leftTemp rightTemp output)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some done) 1 :=
        TM2Programs.evalsToInTimeOne
          (taggedBranchDispatch_invalid_step α γ tmLeft tmRight readLeft readRight
            writeLeft writeRight source left right leftTemp rightTemp output [])
      simpa [tm, c₀, c₁, done] using
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some done) h₁ h₂
  | cons b outputTemp ih =>
      let tm := taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight
      let c₀ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight .drainOutput state source left right leftTemp rightTemp
        output (b :: outputTemp)
      let c₁ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight (.pushOutput b) (.output (some b)) source left right leftTemp
        rightTemp output outputTemp
      let c₂ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight .drainOutput (.output (some b)) source left right leftTemp
        rightTemp (b :: output) outputTemp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne
          (taggedBranchDispatch_drainOutput_step_cons α γ tmLeft tmRight readLeft
            readRight writeLeft writeRight b state source left right leftTemp rightTemp output
            outputTemp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        TM2Programs.evalsToInTimeOne
          (taggedBranchDispatch_pushOutput_step α γ tmLeft tmRight readLeft readRight
            writeLeft writeRight b source left right leftTemp rightTemp output outputTemp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some
            (taggedBranchDispatchFinalCfg α γ tmLeft tmRight readLeft readRight writeLeft
              writeRight source left right leftTemp rightTemp
              (outputTemp.reverse ++ (b :: output)) []))
          (2 * outputTemp.length + 2) := by
        simpa [tm, c₂] using ih (.output (some b)) (b :: output)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * outputTemp.length + 2)
          c₀ c₂
          (some
            (taggedBranchDispatchFinalCfg α γ tmLeft tmRight readLeft readRight writeLeft
              writeRight source left right leftTemp rightTemp
              (outputTemp.reverse ++ (b :: output)) []))
          h₁₂ hTail

lemma taggedBranchDispatch_readLeftOutput_step_cons
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (b : tmLeft.Γ tmLeft.k₁)
    (state : TaggedBranchDispatchState tmLeft.σ tmRight.σ
      (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftOutput : List (tmLeft.Γ tmLeft.k₁))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).step
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .readLeftOutput state source
          (Function.update left tmLeft.k₁ (b :: leftOutput)) right leftTemp rightTemp output
          outputTemp) =
      some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          (.pushLeftOutputTemp (writeLeft b)) (.output (some (writeLeft b))) source
          (Function.update left tmLeft.k₁ leftOutput) right leftTemp rightTemp output
          outputTemp) := by
  letI := tmLeft.kDecidableEq
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg,
    taggedBranchDispatchOutputState]
  congr
  funext k
  cases k with
  | source => rfl
  | left k =>
      by_cases hk : k = tmLeft.k₁
      · subst k
        simp [Function.update]
      · simp [Function.update, hk]
  | right k => rfl
  | leftInputTemp => rfl
  | rightInputTemp => rfl
  | output => rfl
  | outputTemp => rfl

lemma taggedBranchDispatch_readLeftOutput_step_nil
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (state : TaggedBranchDispatchState tmLeft.σ tmRight.σ
      (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).step
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .readLeftOutput state source (Function.update left tmLeft.k₁ []) right leftTemp
          rightTemp output outputTemp) =
      some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .drainOutput (.output none) source (Function.update left tmLeft.k₁ []) right
          leftTemp rightTemp output outputTemp) := by
  letI := tmLeft.kDecidableEq
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg,
    taggedBranchDispatchOutputState]
  congr
  funext k
  cases k with
  | source => rfl
  | left k =>
      by_cases hk : k = tmLeft.k₁
      · subst k
        simp [Function.update]
      · simp [Function.update, hk]
  | right k => rfl
  | leftInputTemp => rfl
  | rightInputTemp => rfl
  | output => rfl
  | outputTemp => rfl

lemma taggedBranchDispatch_pushLeftOutputTemp_step
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (b : γ)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).step
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          (.pushLeftOutputTemp b) (.output (some b)) source left right leftTemp rightTemp
          output outputTemp) =
      some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .readLeftOutput (.output (some b)) source left right leftTemp rightTemp output
          (b :: outputTemp)) := by
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg]
  congr
  funext k
  cases k <;> rfl

def taggedBranchDispatch_readLeftOutput_run
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (state : TaggedBranchDispatchState tmLeft.σ tmRight.σ
      (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
    (leftOutput : List (tmLeft.Γ tmLeft.k₁))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    StateTransition.EvalsToInTime
      (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight).step
      (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
        .readLeftOutput state source (Function.update left tmLeft.k₁ leftOutput) right
        leftTemp rightTemp output outputTemp)
      (some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .drainOutput (.output none) source (Function.update left tmLeft.k₁ []) right
          leftTemp rightTemp output ((leftOutput.map writeLeft).reverse ++ outputTemp)))
      (2 * leftOutput.length + 1) := by
  letI := tmLeft.kDecidableEq
  induction leftOutput generalizing state outputTemp with
  | nil =>
      simpa using
        TM2Programs.evalsToInTimeOne
          (taggedBranchDispatch_readLeftOutput_step_nil α γ tmLeft tmRight readLeft
            readRight writeLeft writeRight state source left right leftTemp rightTemp output
            outputTemp)
  | cons b leftOutput ih =>
      let tm := taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight
      let c₀ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight .readLeftOutput state source
        (Function.update left tmLeft.k₁ (b :: leftOutput)) right leftTemp rightTemp output
        outputTemp
      let c₁ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight (.pushLeftOutputTemp (writeLeft b)) (.output (some (writeLeft b)))
        source (Function.update left tmLeft.k₁ leftOutput) right leftTemp rightTemp output
        outputTemp
      let c₂ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight .readLeftOutput (.output (some (writeLeft b))) source
        (Function.update left tmLeft.k₁ leftOutput) right leftTemp rightTemp output
        (writeLeft b :: outputTemp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne
          (taggedBranchDispatch_readLeftOutput_step_cons α γ tmLeft tmRight readLeft
            readRight writeLeft writeRight b state source left right leftOutput leftTemp
            rightTemp output outputTemp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        TM2Programs.evalsToInTimeOne
          (taggedBranchDispatch_pushLeftOutputTemp_step α γ tmLeft tmRight readLeft
            readRight writeLeft writeRight (writeLeft b) source
            (Function.update left tmLeft.k₁ leftOutput) right leftTemp rightTemp output
            outputTemp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some
            (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft
              writeRight .drainOutput (.output none) source (Function.update left tmLeft.k₁ [])
              right leftTemp rightTemp output
              ((leftOutput.map writeLeft).reverse ++ (writeLeft b :: outputTemp))))
          (2 * leftOutput.length + 1) := by
        simpa [tm, c₂] using ih (.output (some (writeLeft b))) (writeLeft b :: outputTemp)
      simpa [tm, c₀, c₁, c₂, List.map_cons, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * leftOutput.length + 1)
          c₀ c₂
          (some
            (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft
              writeRight .drainOutput (.output none) source (Function.update left tmLeft.k₁ [])
              right leftTemp rightTemp output
              ((leftOutput.map writeLeft).reverse ++ (writeLeft b :: outputTemp))))
          h₁₂ hTail

lemma taggedBranchDispatch_readRightOutput_step_cons
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (b : tmRight.Γ tmRight.k₁)
    (state : TaggedBranchDispatchState tmLeft.σ tmRight.σ
      (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (rightOutput : List (tmRight.Γ tmRight.k₁))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).step
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .readRightOutput state source left
          (Function.update right tmRight.k₁ (b :: rightOutput)) leftTemp rightTemp output
          outputTemp) =
      some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          (.pushRightOutputTemp (writeRight b)) (.output (some (writeRight b))) source left
          (Function.update right tmRight.k₁ rightOutput) leftTemp rightTemp output
          outputTemp) := by
  letI := tmRight.kDecidableEq
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg,
    taggedBranchDispatchOutputState]
  congr
  funext k
  cases k with
  | source => rfl
  | left k => rfl
  | right k =>
      by_cases hk : k = tmRight.k₁
      · subst k
        simp [Function.update]
      · simp [Function.update, hk]
  | leftInputTemp => rfl
  | rightInputTemp => rfl
  | output => rfl
  | outputTemp => rfl

lemma taggedBranchDispatch_readRightOutput_step_nil
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (state : TaggedBranchDispatchState tmLeft.σ tmRight.σ
      (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).step
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .readRightOutput state source left (Function.update right tmRight.k₁ []) leftTemp
          rightTemp output outputTemp) =
      some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .drainOutput (.output none) source left (Function.update right tmRight.k₁ [])
          leftTemp rightTemp output outputTemp) := by
  letI := tmRight.kDecidableEq
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg,
    taggedBranchDispatchOutputState]
  congr
  funext k
  cases k with
  | source => rfl
  | left k => rfl
  | right k =>
      by_cases hk : k = tmRight.k₁
      · subst k
        simp [Function.update]
      · simp [Function.update, hk]
  | leftInputTemp => rfl
  | rightInputTemp => rfl
  | output => rfl
  | outputTemp => rfl

lemma taggedBranchDispatch_pushRightOutputTemp_step
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (b : γ)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).step
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          (.pushRightOutputTemp b) (.output (some b)) source left right leftTemp rightTemp
          output outputTemp) =
      some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .readRightOutput (.output (some b)) source left right leftTemp rightTemp output
          (b :: outputTemp)) := by
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg]
  congr
  funext k
  cases k <;> rfl

def taggedBranchDispatch_readRightOutput_run
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (state : TaggedBranchDispatchState tmLeft.σ tmRight.σ
      (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
    (rightOutput : List (tmRight.Γ tmRight.k₁))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    StateTransition.EvalsToInTime
      (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight).step
      (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
        .readRightOutput state source left (Function.update right tmRight.k₁ rightOutput)
        leftTemp rightTemp output outputTemp)
      (some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .drainOutput (.output none) source left (Function.update right tmRight.k₁ [])
          leftTemp rightTemp output ((rightOutput.map writeRight).reverse ++ outputTemp)))
      (2 * rightOutput.length + 1) := by
  letI := tmRight.kDecidableEq
  induction rightOutput generalizing state outputTemp with
  | nil =>
      simpa using
        TM2Programs.evalsToInTimeOne
          (taggedBranchDispatch_readRightOutput_step_nil α γ tmLeft tmRight readLeft
            readRight writeLeft writeRight state source left right leftTemp rightTemp output
            outputTemp)
  | cons b rightOutput ih =>
      let tm := taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight
      let c₀ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight .readRightOutput state source left
        (Function.update right tmRight.k₁ (b :: rightOutput)) leftTemp rightTemp output
        outputTemp
      let c₁ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight (.pushRightOutputTemp (writeRight b)) (.output (some (writeRight b)))
        source left (Function.update right tmRight.k₁ rightOutput) leftTemp rightTemp output
        outputTemp
      let c₂ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight .readRightOutput (.output (some (writeRight b))) source left
        (Function.update right tmRight.k₁ rightOutput) leftTemp rightTemp output
        (writeRight b :: outputTemp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne
          (taggedBranchDispatch_readRightOutput_step_cons α γ tmLeft tmRight readLeft
            readRight writeLeft writeRight b state source left right rightOutput leftTemp
            rightTemp output outputTemp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        TM2Programs.evalsToInTimeOne
          (taggedBranchDispatch_pushRightOutputTemp_step α γ tmLeft tmRight readLeft
            readRight writeLeft writeRight (writeRight b) source left
            (Function.update right tmRight.k₁ rightOutput) leftTemp rightTemp output
            outputTemp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some
            (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft
              writeRight .drainOutput (.output none) source left
              (Function.update right tmRight.k₁ []) leftTemp rightTemp output
              ((rightOutput.map writeRight).reverse ++ (writeRight b :: outputTemp))))
          (2 * rightOutput.length + 1) := by
        simpa [tm, c₂] using ih (.output (some (writeRight b))) (writeRight b :: outputTemp)
      simpa [tm, c₀, c₁, c₂, List.map_cons, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * rightOutput.length + 1)
          c₀ c₂
          (some
            (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft
              writeRight .drainOutput (.output none) source left
              (Function.update right tmRight.k₁ []) leftTemp rightTemp output
              ((rightOutput.map writeRight).reverse ++ (writeRight b :: outputTemp))))
          h₁₂ hTail

def taggedBranchDispatchLeftRunCfg
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (cfg : tmLeft.Cfg)
    (source : List (Bool ⊕ α))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).Cfg :=
  match cfg.l with
  | some label =>
      taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
        (.runLeft label) (.leftRun cfg.var) source cfg.stk right leftTemp rightTemp output
        outputTemp
  | none =>
      taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
        .readLeftOutput (.output none) source cfg.stk right leftTemp rightTemp output outputTemp

end Karp21
end ComplexityReduction
