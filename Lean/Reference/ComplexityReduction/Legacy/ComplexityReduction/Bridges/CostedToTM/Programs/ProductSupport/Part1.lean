/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.PrefixSuffix

namespace ComplexityReduction
namespace TM2Programs

open Turing.TM2.Stmt

/-- Stack indices for a reusable input-copy subroutine for future product runners. -/
inductive PairInputCopyStack where
  | input
  | output
  | leftTemp
  | rightTemp
  deriving DecidableEq, Fintype

/-- Stack alphabets for the input-copy subroutine. -/
abbrev pairInputCopyAlphabet (α δ : Type) : PairInputCopyStack → Type
  | PairInputCopyStack.input => α
  | PairInputCopyStack.output => δ
  | PairInputCopyStack.leftTemp => α
  | PairInputCopyStack.rightTemp => α

/-- Control labels for the input-copy subroutine. -/
inductive PairInputCopyLabel (α : Type) where
  | readInput
  | pushLeft (a : α)
  | pushRight (a : α)
  deriving DecidableEq, Fintype

/--
A small TM2 subroutine that copies the input stack into two temporary stacks.

This is an internal building block for an eventual arbitrary product-pairing
runner; by itself it does not compute a public output and does not discharge
`prodMkMap`.
-/
def pairInputCopyMachine (α δ : Type) [Fintype α] [Fintype δ] : Turing.FinTM2 where
  K := PairInputCopyStack
  k₀ := PairInputCopyStack.input
  k₁ := PairInputCopyStack.output
  Γ := pairInputCopyAlphabet α δ
  Λ := PairInputCopyLabel α
  main := PairInputCopyLabel.readInput
  σ := Option α
  initialState := none
  Γk₀Fin := by
    dsimp [pairInputCopyAlphabet]
    infer_instance
  m
    | PairInputCopyLabel.readInput =>
        pop PairInputCopyStack.input (fun _ head => head)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some a => PairInputCopyLabel.pushLeft a
              | none => PairInputCopyLabel.readInput)
            (load (fun _ => none) halt))
    | PairInputCopyLabel.pushLeft a =>
        push PairInputCopyStack.leftTemp (fun _ => a)
          (goto fun _ => PairInputCopyLabel.pushRight a)
    | PairInputCopyLabel.pushRight a =>
        push PairInputCopyStack.rightTemp (fun _ => a)
          (goto fun _ => PairInputCopyLabel.readInput)

def pairInputCopyCfg (α δ : Type) [Fintype α] [Fintype δ]
    (label : PairInputCopyLabel α) (state : Option α)
    (input : List α) (output : List δ) (leftTemp rightTemp : List α) :
    (pairInputCopyMachine α δ).Cfg where
  l := some label
  var := state
  stk
    | PairInputCopyStack.input => input
    | PairInputCopyStack.output => output
    | PairInputCopyStack.leftTemp => leftTemp
    | PairInputCopyStack.rightTemp => rightTemp

def pairInputCopyHalt (α δ : Type) [Fintype α] [Fintype δ]
    (output : List δ) (leftTemp rightTemp : List α) :
    (pairInputCopyMachine α δ).Cfg where
  l := none
  var := none
  stk
    | PairInputCopyStack.input => []
    | PairInputCopyStack.output => output
    | PairInputCopyStack.leftTemp => leftTemp
    | PairInputCopyStack.rightTemp => rightTemp

lemma pairInputCopy_readInput_step_cons (α δ : Type) [Fintype α] [Fintype δ]
    (state : Option α) (a : α) (input : List α) (output : List δ)
    (leftTemp rightTemp : List α) :
    (pairInputCopyMachine α δ).step
        (pairInputCopyCfg α δ PairInputCopyLabel.readInput state (a :: input)
          output leftTemp rightTemp) =
      some (pairInputCopyCfg α δ (PairInputCopyLabel.pushLeft a) (some a)
        input output leftTemp rightTemp) := by
  simp [pairInputCopyMachine, pairInputCopyCfg]
  congr
  funext k
  cases k <;> rfl

lemma pairInputCopy_readInput_step_nil (α δ : Type) [Fintype α] [Fintype δ]
    (state : Option α) (output : List δ) (leftTemp rightTemp : List α) :
    (pairInputCopyMachine α δ).step
        (pairInputCopyCfg α δ PairInputCopyLabel.readInput state []
          output leftTemp rightTemp) =
      some (pairInputCopyHalt α δ output leftTemp rightTemp) := by
  simp [pairInputCopyMachine, pairInputCopyCfg, pairInputCopyHalt]
  congr

lemma pairInputCopy_pushLeft_step (α δ : Type) [Fintype α] [Fintype δ]
    (state : Option α) (a : α) (input : List α) (output : List δ)
    (leftTemp rightTemp : List α) :
    (pairInputCopyMachine α δ).step
        (pairInputCopyCfg α δ (PairInputCopyLabel.pushLeft a) state input
          output leftTemp rightTemp) =
      some (pairInputCopyCfg α δ (PairInputCopyLabel.pushRight a) state input
        output (a :: leftTemp) rightTemp) := by
  simp [pairInputCopyMachine, pairInputCopyCfg]
  congr
  funext k
  cases k <;> rfl

lemma pairInputCopy_pushRight_step (α δ : Type) [Fintype α] [Fintype δ]
    (state : Option α) (a : α) (input : List α) (output : List δ)
    (leftTemp rightTemp : List α) :
    (pairInputCopyMachine α δ).step
        (pairInputCopyCfg α δ (PairInputCopyLabel.pushRight a) state input
          output leftTemp rightTemp) =
      some (pairInputCopyCfg α δ PairInputCopyLabel.readInput state input
        output leftTemp (a :: rightTemp)) := by
  simp [pairInputCopyMachine, pairInputCopyCfg]
  congr
  funext k
  cases k <;> rfl

def pairInputCopy_run (α δ : Type) [Fintype α] [Fintype δ]
    (state : Option α) (input : List α) (output : List δ)
    (leftTemp rightTemp : List α) :
    StateTransition.EvalsToInTime (pairInputCopyMachine α δ).step
      (pairInputCopyCfg α δ PairInputCopyLabel.readInput state input output leftTemp rightTemp)
      (some (pairInputCopyHalt α δ output
        (input.reverse ++ leftTemp) (input.reverse ++ rightTemp)))
      (3 * input.length + 1) := by
  induction input generalizing state leftTemp rightTemp with
  | nil =>
      simpa using
        evalsToInTimeOne
          (pairInputCopy_readInput_step_nil α δ state output leftTemp rightTemp)
  | cons a input ih =>
      let tm := pairInputCopyMachine α δ
      let c₀ := pairInputCopyCfg α δ PairInputCopyLabel.readInput state
        (a :: input) output leftTemp rightTemp
      let c₁ := pairInputCopyCfg α δ (PairInputCopyLabel.pushLeft a) (some a)
        input output leftTemp rightTemp
      let c₂ := pairInputCopyCfg α δ (PairInputCopyLabel.pushRight a) (some a)
        input output (a :: leftTemp) rightTemp
      let c₃ := pairInputCopyCfg α δ PairInputCopyLabel.readInput (some a)
        input output (a :: leftTemp) (a :: rightTemp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (pairInputCopy_readInput_step_cons α δ state a input output leftTemp rightTemp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (pairInputCopy_pushLeft_step α δ (some a) a input output leftTemp rightTemp)
      have h₃ : StateTransition.EvalsToInTime tm.step c₂ (some c₃) 1 :=
        evalsToInTimeOne
          (pairInputCopy_pushRight_step α δ (some a) a input output (a :: leftTemp) rightTemp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have h₁₂₃ : StateTransition.EvalsToInTime tm.step c₀ (some c₃) (1 + (1 + 1)) :=
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) 1 c₀ c₂ (some c₃) h₁₂ h₃
      have hTail : StateTransition.EvalsToInTime tm.step c₃
          (some (pairInputCopyHalt α δ output
            (input.reverse ++ (a :: leftTemp)) (input.reverse ++ (a :: rightTemp))))
          (3 * input.length + 1) :=
        ih (some a) (a :: leftTemp) (a :: rightTemp)
      simpa [tm, c₀, c₁, c₂, c₃, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + (1 + 1))
          (3 * input.length + 1) c₀ c₃
          (some (pairInputCopyHalt α δ output
            (input.reverse ++ (a :: leftTemp)) (input.reverse ++ (a :: rightTemp))))
          h₁₂₃ hTail

/-- Stack indices for a reusable mapped stack-copy subroutine. -/
inductive StackCopyMapStack where
  | source
  | target
  | temp
  deriving DecidableEq, Fintype

/-- Stack alphabets for the mapped stack-copy subroutine. -/
abbrev stackCopyMapAlphabet (α β : Type) : StackCopyMapStack → Type
  | StackCopyMapStack.source => α
  | StackCopyMapStack.target => β
  | StackCopyMapStack.temp => β

/-- Control labels for the mapped stack-copy subroutine. -/
inductive StackCopyMapLabel (β : Type) where
  | readSource
  | pushTemp (b : β)
  | drainTemp
  | pushTarget (b : β)
  deriving DecidableEq, Fintype

/--
A generic stack-copy subroutine that maps source symbols, preserves order, and
pushes the copied block in front of the existing target stack.

This is an internal building block for future arbitrary TM2 composition/product
runners: it can copy one machine's output stack into another machine's input
stack after applying the alphabet equivalences.
-/
def stackCopyMapMachine (α β : Type) [Fintype α] [Fintype β]
    (mapSym : α → β) : Turing.FinTM2 where
  K := StackCopyMapStack
  k₀ := StackCopyMapStack.source
  k₁ := StackCopyMapStack.target
  Γ := stackCopyMapAlphabet α β
  Λ := StackCopyMapLabel β
  main := StackCopyMapLabel.readSource
  σ := Option β
  initialState := none
  Γk₀Fin := by
    dsimp [stackCopyMapAlphabet]
    infer_instance
  m
    | StackCopyMapLabel.readSource =>
        pop StackCopyMapStack.source (fun _ head => head.map mapSym)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some b => StackCopyMapLabel.pushTemp b
              | none => StackCopyMapLabel.readSource)
            (goto fun _ => StackCopyMapLabel.drainTemp))
    | StackCopyMapLabel.pushTemp b =>
        push StackCopyMapStack.temp (fun _ => b)
          (goto fun _ => StackCopyMapLabel.readSource)
    | StackCopyMapLabel.drainTemp =>
        pop StackCopyMapStack.temp (fun _ head => head)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some b => StackCopyMapLabel.pushTarget b
              | none => StackCopyMapLabel.drainTemp)
            (load (fun _ => none) halt))
    | StackCopyMapLabel.pushTarget b =>
        push StackCopyMapStack.target (fun _ => b)
          (goto fun _ => StackCopyMapLabel.drainTemp)

def stackCopyMapCfg (α β : Type) [Fintype α] [Fintype β]
    (mapSym : α → β) (label : StackCopyMapLabel β) (state : Option β)
    (source : List α) (target temp : List β) :
    (stackCopyMapMachine α β mapSym).Cfg where
  l := some label
  var := state
  stk
    | StackCopyMapStack.source => source
    | StackCopyMapStack.target => target
    | StackCopyMapStack.temp => temp

def stackCopyMapHalt (α β : Type) [Fintype α] [Fintype β]
    (mapSym : α → β) (target : List β) :
    (stackCopyMapMachine α β mapSym).Cfg where
  l := none
  var := none
  stk
    | StackCopyMapStack.source => []
    | StackCopyMapStack.target => target
    | StackCopyMapStack.temp => []

lemma stackCopyMap_readSource_step_cons (α β : Type) [Fintype α] [Fintype β]
    (mapSym : α → β) (state : Option β) (a : α)
    (source : List α) (target temp : List β) :
    (stackCopyMapMachine α β mapSym).step
        (stackCopyMapCfg α β mapSym StackCopyMapLabel.readSource state
          (a :: source) target temp) =
      some (stackCopyMapCfg α β mapSym (StackCopyMapLabel.pushTemp (mapSym a))
        (some (mapSym a)) source target temp) := by
  simp [stackCopyMapMachine, stackCopyMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma stackCopyMap_readSource_step_nil (α β : Type) [Fintype α] [Fintype β]
    (mapSym : α → β) (state : Option β) (target temp : List β) :
    (stackCopyMapMachine α β mapSym).step
        (stackCopyMapCfg α β mapSym StackCopyMapLabel.readSource state []
          target temp) =
      some (stackCopyMapCfg α β mapSym StackCopyMapLabel.drainTemp none []
        target temp) := by
  simp [stackCopyMapMachine, stackCopyMapCfg]
  rfl

lemma stackCopyMap_pushTemp_step (α β : Type) [Fintype α] [Fintype β]
    (mapSym : α → β) (state : Option β) (b : β)
    (source : List α) (target temp : List β) :
    (stackCopyMapMachine α β mapSym).step
        (stackCopyMapCfg α β mapSym (StackCopyMapLabel.pushTemp b) state
          source target temp) =
      some (stackCopyMapCfg α β mapSym StackCopyMapLabel.readSource state
        source target (b :: temp)) := by
  simp [stackCopyMapMachine, stackCopyMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma stackCopyMap_drainTemp_step_cons (α β : Type) [Fintype α] [Fintype β]
    (mapSym : α → β) (state : Option β) (b : β)
    (target temp : List β) :
    (stackCopyMapMachine α β mapSym).step
        (stackCopyMapCfg α β mapSym StackCopyMapLabel.drainTemp state []
          target (b :: temp)) =
      some (stackCopyMapCfg α β mapSym (StackCopyMapLabel.pushTarget b) (some b)
        [] target temp) := by
  simp [stackCopyMapMachine, stackCopyMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma stackCopyMap_drainTemp_step_nil (α β : Type) [Fintype α] [Fintype β]
    (mapSym : α → β) (state : Option β) (target : List β) :
    (stackCopyMapMachine α β mapSym).step
        (stackCopyMapCfg α β mapSym StackCopyMapLabel.drainTemp state []
          target []) =
      some (stackCopyMapHalt α β mapSym target) := by
  simp [stackCopyMapMachine, stackCopyMapCfg, stackCopyMapHalt]
  congr

lemma stackCopyMap_pushTarget_step (α β : Type) [Fintype α] [Fintype β]
    (mapSym : α → β) (state : Option β) (b : β)
    (target temp : List β) :
    (stackCopyMapMachine α β mapSym).step
        (stackCopyMapCfg α β mapSym (StackCopyMapLabel.pushTarget b) state []
          target temp) =
      some (stackCopyMapCfg α β mapSym StackCopyMapLabel.drainTemp state []
        (b :: target) temp) := by
  simp [stackCopyMapMachine, stackCopyMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma initList_stackCopyMapMachine (α β : Type) [Fintype α] [Fintype β]
    (mapSym : α → β) (input : List α) :
    Turing.initList (stackCopyMapMachine α β mapSym) input =
      stackCopyMapCfg α β mapSym StackCopyMapLabel.readSource none input [] [] := by
  simp [stackCopyMapMachine, stackCopyMapCfg, Turing.initList]
  congr
  funext k
  cases k <;> rfl

lemma haltList_stackCopyMapMachine (α β : Type) [Fintype α] [Fintype β]
    (mapSym : α → β) (output : List β) :
    Turing.haltList (stackCopyMapMachine α β mapSym) output =
      stackCopyMapHalt α β mapSym output := by
  simp [stackCopyMapMachine, stackCopyMapHalt, Turing.haltList]
  congr
  funext k
  cases k <;> rfl

def stackCopyMap_fillTemp_run (α β : Type) [Fintype α] [Fintype β]
    (mapSym : α → β) (state : Option β) (source : List α)
    (target temp : List β) :
    StateTransition.EvalsToInTime (stackCopyMapMachine α β mapSym).step
      (stackCopyMapCfg α β mapSym StackCopyMapLabel.readSource state source target temp)
      (some (stackCopyMapCfg α β mapSym StackCopyMapLabel.drainTemp none []
        target ((source.map mapSym).reverse ++ temp)))
      (2 * source.length + 1) := by
  induction source generalizing state temp with
  | nil =>
      simpa using
        evalsToInTimeOne
          (stackCopyMap_readSource_step_nil α β mapSym state target temp)
  | cons a source ih =>
      let tm := stackCopyMapMachine α β mapSym
      let c₀ := stackCopyMapCfg α β mapSym StackCopyMapLabel.readSource state
        (a :: source) target temp
      let c₁ := stackCopyMapCfg α β mapSym (StackCopyMapLabel.pushTemp (mapSym a))
        (some (mapSym a)) source target temp
      let c₂ := stackCopyMapCfg α β mapSym StackCopyMapLabel.readSource
        (some (mapSym a)) source target (mapSym a :: temp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (stackCopyMap_readSource_step_cons α β mapSym state a source target temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (stackCopyMap_pushTemp_step α β mapSym (some (mapSym a)) (mapSym a)
            source target temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (stackCopyMapCfg α β mapSym StackCopyMapLabel.drainTemp none []
            target ((source.map mapSym).reverse ++ (mapSym a :: temp))))
          (2 * source.length + 1) :=
        ih (some (mapSym a)) (mapSym a :: temp)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1)
          (2 * source.length + 1) c₀ c₂
          (some (stackCopyMapCfg α β mapSym StackCopyMapLabel.drainTemp none []
            target ((source.map mapSym).reverse ++ (mapSym a :: temp))))
          h₁₂ hTail

def stackCopyMap_drainTemp_run (α β : Type) [Fintype α] [Fintype β]
    (mapSym : α → β) (state : Option β) (target temp : List β) :
    StateTransition.EvalsToInTime (stackCopyMapMachine α β mapSym).step
      (stackCopyMapCfg α β mapSym StackCopyMapLabel.drainTemp state [] target temp)
      (some (stackCopyMapHalt α β mapSym (temp.reverse ++ target)))
      (2 * temp.length + 1) := by
  induction temp generalizing state target with
  | nil =>
      simpa using
        evalsToInTimeOne
          (stackCopyMap_drainTemp_step_nil α β mapSym state target)
  | cons b temp ih =>
      let tm := stackCopyMapMachine α β mapSym
      let c₀ := stackCopyMapCfg α β mapSym StackCopyMapLabel.drainTemp state []
        target (b :: temp)
      let c₁ := stackCopyMapCfg α β mapSym (StackCopyMapLabel.pushTarget b) (some b)
        [] target temp
      let c₂ := stackCopyMapCfg α β mapSym StackCopyMapLabel.drainTemp (some b)
        [] (b :: target) temp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (stackCopyMap_drainTemp_step_cons α β mapSym state b target temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (stackCopyMap_pushTarget_step α β mapSym (some b) b target temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (stackCopyMapHalt α β mapSym (temp.reverse ++ (b :: target))))
          (2 * temp.length + 1) :=
        ih (some b) (b :: target)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1)
          (2 * temp.length + 1) c₀ c₂
          (some (stackCopyMapHalt α β mapSym (temp.reverse ++ (b :: target))))
          h₁₂ hTail

def stackCopyMap_run (α β : Type) [Fintype α] [Fintype β]
    (mapSym : α → β) (source : List α) (target : List β) :
    StateTransition.EvalsToInTime (stackCopyMapMachine α β mapSym).step
      (stackCopyMapCfg α β mapSym StackCopyMapLabel.readSource none source target [])
      (some (stackCopyMapHalt α β mapSym (source.map mapSym ++ target)))
      (4 * source.length + 2) := by
  let tm := stackCopyMapMachine α β mapSym
  let mid := stackCopyMapCfg α β mapSym StackCopyMapLabel.drainTemp none []
    target (source.map mapSym).reverse
  have hFill : StateTransition.EvalsToInTime tm.step
      (stackCopyMapCfg α β mapSym StackCopyMapLabel.readSource none source target [])
      (some mid)
      (2 * source.length + 1) := by
    simpa [tm, mid] using
      stackCopyMap_fillTemp_run α β mapSym none source target []
  have hDrain : StateTransition.EvalsToInTime tm.step mid
      (some (stackCopyMapHalt α β mapSym ((source.map mapSym).reverse.reverse ++ target)))
      (2 * (source.map mapSym).reverse.length + 1) := by
    simpa [tm, mid] using
      stackCopyMap_drainTemp_run α β mapSym none target (source.map mapSym).reverse
  have hAll : StateTransition.EvalsToInTime tm.step
      (stackCopyMapCfg α β mapSym StackCopyMapLabel.readSource none source target [])
      (some (stackCopyMapHalt α β mapSym ((source.map mapSym).reverse.reverse ++ target)))
      ((2 * (source.map mapSym).reverse.length + 1) + (2 * source.length + 1)) :=
    StateTransition.EvalsToInTime.trans tm.step
      (2 * source.length + 1)
      (2 * (source.map mapSym).reverse.length + 1)
      (stackCopyMapCfg α β mapSym StackCopyMapLabel.readSource none source target [])
      mid
      (some (stackCopyMapHalt α β mapSym
        ((source.map mapSym).reverse.reverse ++ target)))
      hFill hDrain
  refine
    { steps := hAll.steps
      evals_in_steps := by
        simpa [tm, mid] using hAll.evals_in_steps
      steps_le_m := ?_ }
  have hSteps := hAll.steps_le_m
  simp [List.length_reverse] at hSteps
  omega

/--
As a standalone TM2 program, the mapped stack-copy subroutine computes
`input.map mapSym` in linear time.  The stronger `stackCopyMap_run` theorem
above keeps the target-tail form needed by future composition/product runners.
-/
def stackCopyMap_outputs (α β : Type) [Fintype α] [Fintype β]
    (mapSym : α → β) (input : List α) :
    Turing.TM2OutputsInTime (stackCopyMapMachine α β mapSym)
      input (some (input.map mapSym)) (4 * input.length + 2) := by
  change StateTransition.EvalsToInTime (stackCopyMapMachine α β mapSym).step
    (Turing.initList (stackCopyMapMachine α β mapSym) input)
    (some (Turing.haltList (stackCopyMapMachine α β mapSym) (input.map mapSym)))
    (4 * input.length + 2)
  rw [initList_stackCopyMapMachine, haltList_stackCopyMapMachine]
  simpa using
    stackCopyMap_run α β mapSym input []

/-- Stack indices for copying one source stack into two mapped target stacks. -/
inductive PairStackCopyMapStack where
  | source
  | leftTarget
  | rightTarget
  | leftTemp
  | rightTemp
  deriving DecidableEq, Fintype

/-- Alphabets for the two-target mapped stack-copy subroutine. -/
abbrev pairStackCopyMapAlphabet (α β γ : Type) : PairStackCopyMapStack → Type
  | PairStackCopyMapStack.source => α
  | PairStackCopyMapStack.leftTarget => β
  | PairStackCopyMapStack.rightTarget => γ
  | PairStackCopyMapStack.leftTemp => β
  | PairStackCopyMapStack.rightTemp => γ

/-- Control labels for the two-target mapped stack-copy subroutine. -/
inductive PairStackCopyMapLabel (β γ : Type) where
  | readSource
  | pushLeftTemp (b : β) (c : γ)
  | pushRightTemp (c : γ)
  | drainLeft
  | pushLeftTarget (b : β)
  | drainRight
  | pushRightTarget (c : γ)
  deriving DecidableEq, Fintype

/-- Finite control state for the two-target mapped stack-copy subroutine. -/
inductive PairStackCopyMapState (β γ : Type) where
  | none
  | pair (b : β) (c : γ)
  | left (b : β)
  | right (c : γ)
  deriving DecidableEq, Fintype

namespace PairStackCopyMapState

def isPair {β γ : Type} : PairStackCopyMapState β γ → Bool
  | pair _ _ => true
  | _ => false

def isLeft {β γ : Type} : PairStackCopyMapState β γ → Bool
  | left _ => true
  | _ => false

def isRight {β γ : Type} : PairStackCopyMapState β γ → Bool
  | right _ => true
  | _ => false

end PairStackCopyMapState

/--
Copy a source stack through two symbol maps into two target stacks, preserving
the source order on both targets.
-/
def pairStackCopyMapMachine (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
    (mapLeft : α → β) (mapRight : α → γ) : Turing.FinTM2 where
  K := PairStackCopyMapStack
  k₀ := PairStackCopyMapStack.source
  k₁ := PairStackCopyMapStack.leftTarget
  Γ := pairStackCopyMapAlphabet α β γ
  Λ := PairStackCopyMapLabel β γ
  main := PairStackCopyMapLabel.readSource
  σ := PairStackCopyMapState β γ
  initialState := PairStackCopyMapState.none
  Γk₀Fin := by
    dsimp [pairStackCopyMapAlphabet]
    infer_instance
  m
    | PairStackCopyMapLabel.readSource =>
        pop PairStackCopyMapStack.source
          (fun _ head =>
            match head with
            | some a => PairStackCopyMapState.pair (mapLeft a) (mapRight a)
            | none => PairStackCopyMapState.none)
          (branch PairStackCopyMapState.isPair
            (goto fun state =>
              match state with
              | PairStackCopyMapState.pair b c => PairStackCopyMapLabel.pushLeftTemp b c
              | _ => PairStackCopyMapLabel.drainLeft)
            (goto fun _ => PairStackCopyMapLabel.drainLeft))
    | PairStackCopyMapLabel.pushLeftTemp b c =>
        push PairStackCopyMapStack.leftTemp (fun _ => b)
          (goto fun _ => PairStackCopyMapLabel.pushRightTemp c)
    | PairStackCopyMapLabel.pushRightTemp c =>
        push PairStackCopyMapStack.rightTemp (fun _ => c)
          (goto fun _ => PairStackCopyMapLabel.readSource)
    | PairStackCopyMapLabel.drainLeft =>
        pop PairStackCopyMapStack.leftTemp
          (fun _ head =>
            match head with
            | some b => PairStackCopyMapState.left b
            | none => PairStackCopyMapState.none)
          (branch PairStackCopyMapState.isLeft
            (goto fun state =>
              match state with
              | PairStackCopyMapState.left b => PairStackCopyMapLabel.pushLeftTarget b
              | _ => PairStackCopyMapLabel.drainRight)
            (goto fun _ => PairStackCopyMapLabel.drainRight))
    | PairStackCopyMapLabel.pushLeftTarget b =>
        push PairStackCopyMapStack.leftTarget (fun _ => b)
          (goto fun _ => PairStackCopyMapLabel.drainLeft)
    | PairStackCopyMapLabel.drainRight =>
        pop PairStackCopyMapStack.rightTemp
          (fun _ head =>
            match head with
            | some c => PairStackCopyMapState.right c
            | none => PairStackCopyMapState.none)
          (branch PairStackCopyMapState.isRight
            (goto fun state =>
              match state with
              | PairStackCopyMapState.right c => PairStackCopyMapLabel.pushRightTarget c
              | _ => PairStackCopyMapLabel.drainRight)
            (load (fun _ => PairStackCopyMapState.none) halt))
    | PairStackCopyMapLabel.pushRightTarget c =>
        push PairStackCopyMapStack.rightTarget (fun _ => c)
          (goto fun _ => PairStackCopyMapLabel.drainRight)

def pairStackCopyMapCfg (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
    (mapLeft : α → β) (mapRight : α → γ)
    (label : PairStackCopyMapLabel β γ) (state : PairStackCopyMapState β γ)
    (source : List α) (leftTarget : List β) (rightTarget : List γ)
    (leftTemp : List β) (rightTemp : List γ) :
    (pairStackCopyMapMachine α β γ mapLeft mapRight).Cfg where
  l := some label
  var := state
  stk
    | PairStackCopyMapStack.source => source
    | PairStackCopyMapStack.leftTarget => leftTarget
    | PairStackCopyMapStack.rightTarget => rightTarget
    | PairStackCopyMapStack.leftTemp => leftTemp
    | PairStackCopyMapStack.rightTemp => rightTemp

def pairStackCopyMapHalt (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
    (mapLeft : α → β) (mapRight : α → γ)
    (leftTarget : List β) (rightTarget : List γ) :
    (pairStackCopyMapMachine α β γ mapLeft mapRight).Cfg where
  l := none
  var := PairStackCopyMapState.none
  stk
    | PairStackCopyMapStack.source => []
    | PairStackCopyMapStack.leftTarget => leftTarget
    | PairStackCopyMapStack.rightTarget => rightTarget
    | PairStackCopyMapStack.leftTemp => []
    | PairStackCopyMapStack.rightTemp => []

lemma pairStackCopyMap_readSource_step_cons
    (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
    (mapLeft : α → β) (mapRight : α → γ)
    (state : PairStackCopyMapState β γ) (a : α) (source : List α)
    (leftTarget : List β) (rightTarget : List γ) (leftTemp : List β)
    (rightTemp : List γ) :
    (pairStackCopyMapMachine α β γ mapLeft mapRight).step
        (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.readSource
          state (a :: source) leftTarget rightTarget leftTemp rightTemp) =
      some
        (pairStackCopyMapCfg α β γ mapLeft mapRight
          (PairStackCopyMapLabel.pushLeftTemp (mapLeft a) (mapRight a))
          (PairStackCopyMapState.pair (mapLeft a) (mapRight a))
          source leftTarget rightTarget leftTemp rightTemp) := by
  simp [pairStackCopyMapMachine, pairStackCopyMapCfg, PairStackCopyMapState.isPair]
  congr
  funext k
  cases k <;> rfl

lemma pairStackCopyMap_readSource_step_nil
    (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
    (mapLeft : α → β) (mapRight : α → γ)
    (state : PairStackCopyMapState β γ) (leftTarget : List β) (rightTarget : List γ)
    (leftTemp : List β) (rightTemp : List γ) :
    (pairStackCopyMapMachine α β γ mapLeft mapRight).step
        (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.readSource
          state [] leftTarget rightTarget leftTemp rightTemp) =
      some
        (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.drainLeft
          PairStackCopyMapState.none [] leftTarget rightTarget leftTemp rightTemp) := by
  simp [pairStackCopyMapMachine, pairStackCopyMapCfg, PairStackCopyMapState.isPair]
  congr

lemma pairStackCopyMap_pushLeftTemp_step
    (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
    (mapLeft : α → β) (mapRight : α → γ)
    (state : PairStackCopyMapState β γ) (b : β) (c : γ) (source : List α)
    (leftTarget : List β) (rightTarget : List γ) (leftTemp : List β)
    (rightTemp : List γ) :
    (pairStackCopyMapMachine α β γ mapLeft mapRight).step
        (pairStackCopyMapCfg α β γ mapLeft mapRight
          (PairStackCopyMapLabel.pushLeftTemp b c) state source leftTarget rightTarget
          leftTemp rightTemp) =
      some
        (pairStackCopyMapCfg α β γ mapLeft mapRight
          (PairStackCopyMapLabel.pushRightTemp c) state source leftTarget rightTarget
          (b :: leftTemp) rightTemp) := by
  simp [pairStackCopyMapMachine, pairStackCopyMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma pairStackCopyMap_pushRightTemp_step
    (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
    (mapLeft : α → β) (mapRight : α → γ)
    (state : PairStackCopyMapState β γ) (c : γ) (source : List α)
    (leftTarget : List β) (rightTarget : List γ) (leftTemp : List β)
    (rightTemp : List γ) :
    (pairStackCopyMapMachine α β γ mapLeft mapRight).step
        (pairStackCopyMapCfg α β γ mapLeft mapRight
          (PairStackCopyMapLabel.pushRightTemp c) state source leftTarget rightTarget
          leftTemp rightTemp) =
      some
        (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.readSource
          state source leftTarget rightTarget leftTemp (c :: rightTemp)) := by
  simp [pairStackCopyMapMachine, pairStackCopyMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma pairStackCopyMap_drainLeft_step_cons
    (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
    (mapLeft : α → β) (mapRight : α → γ)
    (state : PairStackCopyMapState β γ) (b : β) (leftTemp : List β)
    (leftTarget : List β) (rightTarget : List γ) (rightTemp : List γ) :
    (pairStackCopyMapMachine α β γ mapLeft mapRight).step
        (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.drainLeft
          state [] leftTarget rightTarget (b :: leftTemp) rightTemp) =
      some
        (pairStackCopyMapCfg α β γ mapLeft mapRight
          (PairStackCopyMapLabel.pushLeftTarget b) (PairStackCopyMapState.left b)
          [] leftTarget rightTarget leftTemp rightTemp) := by
  simp [pairStackCopyMapMachine, pairStackCopyMapCfg, PairStackCopyMapState.isLeft]
  congr
  funext k
  cases k <;> rfl

lemma pairStackCopyMap_drainLeft_step_nil
    (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
    (mapLeft : α → β) (mapRight : α → γ)
    (state : PairStackCopyMapState β γ) (leftTarget : List β) (rightTarget : List γ)
    (rightTemp : List γ) :
    (pairStackCopyMapMachine α β γ mapLeft mapRight).step
        (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.drainLeft
          state [] leftTarget rightTarget [] rightTemp) =
      some
        (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.drainRight
          PairStackCopyMapState.none [] leftTarget rightTarget [] rightTemp) := by
  simp [pairStackCopyMapMachine, pairStackCopyMapCfg, PairStackCopyMapState.isLeft]
  congr

lemma pairStackCopyMap_pushLeftTarget_step
    (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
    (mapLeft : α → β) (mapRight : α → γ)
    (state : PairStackCopyMapState β γ) (b : β) (leftTarget : List β)
    (rightTarget : List γ) (leftTemp : List β) (rightTemp : List γ) :
    (pairStackCopyMapMachine α β γ mapLeft mapRight).step
        (pairStackCopyMapCfg α β γ mapLeft mapRight
          (PairStackCopyMapLabel.pushLeftTarget b) state [] leftTarget rightTarget
          leftTemp rightTemp) =
      some
        (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.drainLeft
          state [] (b :: leftTarget) rightTarget leftTemp rightTemp) := by
  simp [pairStackCopyMapMachine, pairStackCopyMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma pairStackCopyMap_drainRight_step_cons
    (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
    (mapLeft : α → β) (mapRight : α → γ)
    (state : PairStackCopyMapState β γ) (c : γ) (leftTarget : List β)
    (rightTarget : List γ) (rightTemp : List γ) :
    (pairStackCopyMapMachine α β γ mapLeft mapRight).step
        (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.drainRight
          state [] leftTarget rightTarget [] (c :: rightTemp)) =
      some
        (pairStackCopyMapCfg α β γ mapLeft mapRight
          (PairStackCopyMapLabel.pushRightTarget c) (PairStackCopyMapState.right c)
          [] leftTarget rightTarget [] rightTemp) := by
  simp [pairStackCopyMapMachine, pairStackCopyMapCfg, PairStackCopyMapState.isRight]
  congr
  funext k
  cases k <;> rfl

lemma pairStackCopyMap_drainRight_step_nil
    (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
    (mapLeft : α → β) (mapRight : α → γ)
    (state : PairStackCopyMapState β γ) (leftTarget : List β) (rightTarget : List γ) :
    (pairStackCopyMapMachine α β γ mapLeft mapRight).step
        (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.drainRight
          state [] leftTarget rightTarget [] []) =
      some (pairStackCopyMapHalt α β γ mapLeft mapRight leftTarget rightTarget) := by
  simp [pairStackCopyMapMachine, pairStackCopyMapCfg, pairStackCopyMapHalt,
    PairStackCopyMapState.isRight]
  congr

lemma pairStackCopyMap_pushRightTarget_step
    (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
    (mapLeft : α → β) (mapRight : α → γ)
    (state : PairStackCopyMapState β γ) (c : γ) (leftTarget : List β)
    (rightTarget : List γ) (rightTemp : List γ) :
    (pairStackCopyMapMachine α β γ mapLeft mapRight).step
        (pairStackCopyMapCfg α β γ mapLeft mapRight
          (PairStackCopyMapLabel.pushRightTarget c) state [] leftTarget rightTarget []
          rightTemp) =
      some
        (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.drainRight
          state [] leftTarget (c :: rightTarget) [] rightTemp) := by
  simp [pairStackCopyMapMachine, pairStackCopyMapCfg]
  congr
  funext k
  cases k <;> rfl

def pairStackCopyMap_fillTemps_run
    (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
    (mapLeft : α → β) (mapRight : α → γ)
    (state : PairStackCopyMapState β γ) (source : List α)
    (leftTarget : List β) (rightTarget : List γ) (leftTemp : List β)
    (rightTemp : List γ) :
    StateTransition.EvalsToInTime (pairStackCopyMapMachine α β γ mapLeft mapRight).step
      (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.readSource
        state source leftTarget rightTarget leftTemp rightTemp)
      (some
        (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.drainLeft
          PairStackCopyMapState.none [] leftTarget rightTarget
          ((source.map mapLeft).reverse ++ leftTemp)
          ((source.map mapRight).reverse ++ rightTemp)))
      (3 * source.length + 1) := by
  induction source generalizing state leftTemp rightTemp with
  | nil =>
      simpa using
        evalsToInTimeOne
          (pairStackCopyMap_readSource_step_nil α β γ mapLeft mapRight state
            leftTarget rightTarget leftTemp rightTemp)
  | cons a source ih =>
      let tm := pairStackCopyMapMachine α β γ mapLeft mapRight
      let nextState := PairStackCopyMapState.pair (mapLeft a) (mapRight a)
      let c₀ := pairStackCopyMapCfg α β γ mapLeft mapRight
        PairStackCopyMapLabel.readSource state (a :: source) leftTarget rightTarget
        leftTemp rightTemp
      let c₁ := pairStackCopyMapCfg α β γ mapLeft mapRight
        (PairStackCopyMapLabel.pushLeftTemp (mapLeft a) (mapRight a)) nextState
        source leftTarget rightTarget leftTemp rightTemp
      let c₂ := pairStackCopyMapCfg α β γ mapLeft mapRight
        (PairStackCopyMapLabel.pushRightTemp (mapRight a)) nextState
        source leftTarget rightTarget (mapLeft a :: leftTemp) rightTemp
      let c₃ := pairStackCopyMapCfg α β γ mapLeft mapRight
        PairStackCopyMapLabel.readSource nextState source leftTarget rightTarget
        (mapLeft a :: leftTemp) (mapRight a :: rightTemp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (pairStackCopyMap_readSource_step_cons α β γ mapLeft mapRight state a
            source leftTarget rightTarget leftTemp rightTemp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (pairStackCopyMap_pushLeftTemp_step α β γ mapLeft mapRight nextState
            (mapLeft a) (mapRight a) source leftTarget rightTarget leftTemp rightTemp)
      have h₃ : StateTransition.EvalsToInTime tm.step c₂ (some c₃) 1 :=
        evalsToInTimeOne
          (pairStackCopyMap_pushRightTemp_step α β γ mapLeft mapRight nextState
            (mapRight a) source leftTarget rightTarget (mapLeft a :: leftTemp) rightTemp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have h₁₂₃ : StateTransition.EvalsToInTime tm.step c₀ (some c₃) (1 + (1 + 1)) :=
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) 1 c₀ c₂ (some c₃) h₁₂ h₃
      have hTail : StateTransition.EvalsToInTime tm.step c₃
          (some
            (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.drainLeft
              PairStackCopyMapState.none [] leftTarget rightTarget
              ((source.map mapLeft).reverse ++ (mapLeft a :: leftTemp))
              ((source.map mapRight).reverse ++ (mapRight a :: rightTemp))))
          (3 * source.length + 1) :=
        ih nextState (mapLeft a :: leftTemp) (mapRight a :: rightTemp)
      simpa [tm, c₀, c₁, c₂, c₃, nextState, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + (1 + 1))
          (3 * source.length + 1) c₀ c₃
          (some
            (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.drainLeft
              PairStackCopyMapState.none [] leftTarget rightTarget
              ((source.map mapLeft).reverse ++ (mapLeft a :: leftTemp))
              ((source.map mapRight).reverse ++ (mapRight a :: rightTemp))))
          h₁₂₃ hTail

end TM2Programs
end ComplexityReduction
