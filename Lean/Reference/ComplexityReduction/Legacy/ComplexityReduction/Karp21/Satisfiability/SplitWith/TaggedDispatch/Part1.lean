/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.SplitWith.BranchInputChoice

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction
open Turing.TM2.Stmt

inductive TaggedBranchDispatchStack (KLeft KRight : Type) where
  | source
  | left (k : KLeft)
  | right (k : KRight)
  | leftInputTemp
  | rightInputTemp
  | output
  | outputTemp
  deriving DecidableEq, Fintype

abbrev taggedBranchDispatchAlphabet (α γ : Type) (tmLeft tmRight : Turing.FinTM2) :
    TaggedBranchDispatchStack tmLeft.K tmRight.K → Type
  | .source => Bool ⊕ α
  | .left k => tmLeft.Γ k
  | .right k => tmRight.Γ k
  | .leftInputTemp => tmLeft.Γ tmLeft.k₀
  | .rightInputTemp => tmRight.Γ tmRight.k₀
  | .output => γ
  | .outputTemp => γ

inductive TaggedBranchDispatchLabel
    (ΛLeft ΛRight leftInput rightInput γ : Type) where
  | readTag
  | readLeftPayload
  | pushLeftTemp (b : leftInput)
  | drainLeftInput
  | pushLeftInput (b : leftInput)
  | runLeft (label : ΛLeft)
  | readLeftOutput
  | pushLeftOutputTemp (b : γ)
  | readRightPayload
  | pushRightTemp (b : rightInput)
  | drainRightInput
  | pushRightInput (b : rightInput)
  | runRight (label : ΛRight)
  | readRightOutput
  | pushRightOutputTemp (b : γ)
  | drainOutput
  | pushOutput (b : γ)
  | invalid
  deriving DecidableEq, Fintype

inductive TaggedBranchDispatchState
    (σLeft σRight leftInput rightInput γ : Type) where
  | tag (head : Option Bool)
  | leftInput (head : Option leftInput)
  | rightInput (head : Option rightInput)
  | leftRun (state : σLeft)
  | rightRun (state : σRight)
  | output (head : Option γ)
  deriving Fintype

def taggedBranchDispatchTagState {σLeft σRight leftInput rightInput γ : Type} :
    TaggedBranchDispatchState σLeft σRight leftInput rightInput γ → Option Bool
  | .tag head => head
  | _ => none

def taggedBranchDispatchLeftInputState {σLeft σRight leftInput rightInput γ : Type} :
    TaggedBranchDispatchState σLeft σRight leftInput rightInput γ → Option leftInput
  | .leftInput head => head
  | _ => none

def taggedBranchDispatchRightInputState {σLeft σRight leftInput rightInput γ : Type} :
    TaggedBranchDispatchState σLeft σRight leftInput rightInput γ → Option rightInput
  | .rightInput head => head
  | _ => none

def taggedBranchDispatchLeftRunState (tmLeft tmRight : Turing.FinTM2)
    {leftInput rightInput γ : Type} :
    TaggedBranchDispatchState tmLeft.σ tmRight.σ leftInput rightInput γ → tmLeft.σ
  | .leftRun state => state
  | _ => tmLeft.initialState

def taggedBranchDispatchRightRunState (tmLeft tmRight : Turing.FinTM2)
    {leftInput rightInput γ : Type} :
    TaggedBranchDispatchState tmLeft.σ tmRight.σ leftInput rightInput γ → tmRight.σ
  | .rightRun state => state
  | _ => tmRight.initialState

def taggedBranchDispatchOutputState {σLeft σRight leftInput rightInput γ : Type} :
    TaggedBranchDispatchState σLeft σRight leftInput rightInput γ → Option γ
  | .output head => head
  | _ => none

def taggedBranchLeftStmt (α γ : Type) (tmLeft tmRight : Turing.FinTM2)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ) :
    Turing.TM2.Stmt tmLeft.Γ tmLeft.Λ tmLeft.σ →
      Turing.TM2.Stmt (taggedBranchDispatchAlphabet α γ tmLeft tmRight)
        (TaggedBranchDispatchLabel tmLeft.Λ tmRight.Λ
          (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
        (TaggedBranchDispatchState tmLeft.σ tmRight.σ
          (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
  | push k f q =>
      push (.left k)
        (fun state => f (taggedBranchDispatchLeftRunState tmLeft tmRight state))
        (taggedBranchLeftStmt α γ tmLeft tmRight writeLeft q)
  | peek k f q =>
      peek (.left k)
        (fun state head =>
          .leftRun (f (taggedBranchDispatchLeftRunState tmLeft tmRight state) head))
        (taggedBranchLeftStmt α γ tmLeft tmRight writeLeft q)
  | pop k f q =>
      pop (.left k)
        (fun state head =>
          .leftRun (f (taggedBranchDispatchLeftRunState tmLeft tmRight state) head))
        (taggedBranchLeftStmt α γ tmLeft tmRight writeLeft q)
  | load f q =>
      load (fun state =>
          .leftRun (f (taggedBranchDispatchLeftRunState tmLeft tmRight state)))
        (taggedBranchLeftStmt α γ tmLeft tmRight writeLeft q)
  | branch f qTrue qFalse =>
      branch (fun state => f (taggedBranchDispatchLeftRunState tmLeft tmRight state))
        (taggedBranchLeftStmt α γ tmLeft tmRight writeLeft qTrue)
        (taggedBranchLeftStmt α γ tmLeft tmRight writeLeft qFalse)
  | goto f =>
      goto fun state =>
        .runLeft (f (taggedBranchDispatchLeftRunState tmLeft tmRight state))
  | halt =>
      load (fun _ => .output none) (goto fun _ => .readLeftOutput)

def taggedBranchRightStmt (α γ : Type) (tmLeft tmRight : Turing.FinTM2)
    (writeRight : tmRight.Γ tmRight.k₁ → γ) :
    Turing.TM2.Stmt tmRight.Γ tmRight.Λ tmRight.σ →
      Turing.TM2.Stmt (taggedBranchDispatchAlphabet α γ tmLeft tmRight)
        (TaggedBranchDispatchLabel tmLeft.Λ tmRight.Λ
          (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
        (TaggedBranchDispatchState tmLeft.σ tmRight.σ
          (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
  | push k f q =>
      push (.right k)
        (fun state => f (taggedBranchDispatchRightRunState tmLeft tmRight state))
        (taggedBranchRightStmt α γ tmLeft tmRight writeRight q)
  | peek k f q =>
      peek (.right k)
        (fun state head =>
          .rightRun (f (taggedBranchDispatchRightRunState tmLeft tmRight state) head))
        (taggedBranchRightStmt α γ tmLeft tmRight writeRight q)
  | pop k f q =>
      pop (.right k)
        (fun state head =>
          .rightRun (f (taggedBranchDispatchRightRunState tmLeft tmRight state) head))
        (taggedBranchRightStmt α γ tmLeft tmRight writeRight q)
  | load f q =>
      load (fun state =>
          .rightRun (f (taggedBranchDispatchRightRunState tmLeft tmRight state)))
        (taggedBranchRightStmt α γ tmLeft tmRight writeRight q)
  | branch f qTrue qFalse =>
      branch (fun state => f (taggedBranchDispatchRightRunState tmLeft tmRight state))
        (taggedBranchRightStmt α γ tmLeft tmRight writeRight qTrue)
        (taggedBranchRightStmt α γ tmLeft tmRight writeRight qFalse)
  | goto f =>
      goto fun state =>
        .runRight (f (taggedBranchDispatchRightRunState tmLeft tmRight state))
  | halt =>
      load (fun _ => .output none) (goto fun _ => .readRightOutput)

/--
Tagged branch dispatcher skeleton.  It consumes a leading Boolean tag and shared
payload alphabet, copies the payload to the selected branch machine, runs only
that branch, and copies its output to the common public output stack.
-/
def taggedBranchDispatchMachine (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ) : Turing.FinTM2 := by
  letI := tmLeft.kDecidableEq
  letI := tmRight.kDecidableEq
  letI := tmLeft.kFin
  letI := tmRight.kFin
  letI := tmLeft.ΛFin
  letI := tmRight.ΛFin
  letI := tmLeft.σFin
  letI := tmRight.σFin
  letI := tmLeft.Γk₀Fin
  letI := tmRight.Γk₀Fin
  exact
    { K := TaggedBranchDispatchStack tmLeft.K tmRight.K
      k₀ := .source
      k₁ := .output
      Γ := taggedBranchDispatchAlphabet α γ tmLeft tmRight
      Λ := TaggedBranchDispatchLabel tmLeft.Λ tmRight.Λ
        (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ
      main := .readTag
      σ := TaggedBranchDispatchState tmLeft.σ tmRight.σ
        (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ
      initialState := .tag none
      Γk₀Fin := by
        dsimp [taggedBranchDispatchAlphabet]
        infer_instance
      m := fun
        | .readTag =>
            pop .source
              (fun _ head =>
                match head with
                | some (Sum.inl tag) => .tag (some tag)
                | _ => .tag none)
              (goto fun state =>
                match taggedBranchDispatchTagState state with
                | some false => .readLeftPayload
                | some true => .readRightPayload
                | none => .invalid)
        | .readLeftPayload =>
            pop .source
              (fun _ head =>
                match head with
                | some (Sum.inr a) => .leftInput (some (readLeft a))
                | _ => .leftInput none)
              (goto fun state =>
                match taggedBranchDispatchLeftInputState state with
                | some b => .pushLeftTemp b
                | none => .drainLeftInput)
        | .pushLeftTemp b =>
            push .leftInputTemp (fun _ => b) (goto fun _ => .readLeftPayload)
        | .drainLeftInput =>
            pop .leftInputTemp (fun _ head => .leftInput head)
              (branch (fun state => (taggedBranchDispatchLeftInputState state).isSome)
                (goto fun state =>
                  match taggedBranchDispatchLeftInputState state with
                  | some b => .pushLeftInput b
                  | none => .invalid)
                (load (fun _ => .leftRun tmLeft.initialState)
                  (goto fun _ => .runLeft tmLeft.main)))
        | .pushLeftInput b =>
            push (.left tmLeft.k₀) (fun _ => b) (goto fun _ => .drainLeftInput)
        | .runLeft label =>
            taggedBranchLeftStmt α γ tmLeft tmRight writeLeft (tmLeft.m label)
        | .readLeftOutput =>
            pop (.left tmLeft.k₁) (fun _ head => .output (head.map writeLeft))
              (goto fun state =>
                match taggedBranchDispatchOutputState state with
                | some b => .pushLeftOutputTemp b
                | none => .drainOutput)
        | .pushLeftOutputTemp b =>
            push .outputTemp (fun _ => b) (goto fun _ => .readLeftOutput)
        | .readRightPayload =>
            pop .source
              (fun _ head =>
                match head with
                | some (Sum.inr a) => .rightInput (some (readRight a))
                | _ => .rightInput none)
              (goto fun state =>
                match taggedBranchDispatchRightInputState state with
                | some b => .pushRightTemp b
                | none => .drainRightInput)
        | .pushRightTemp b =>
            push .rightInputTemp (fun _ => b) (goto fun _ => .readRightPayload)
        | .drainRightInput =>
            pop .rightInputTemp (fun _ head => .rightInput head)
              (branch (fun state => (taggedBranchDispatchRightInputState state).isSome)
                (goto fun state =>
                  match taggedBranchDispatchRightInputState state with
                  | some b => .pushRightInput b
                  | none => .invalid)
                (load (fun _ => .rightRun tmRight.initialState)
                  (goto fun _ => .runRight tmRight.main)))
        | .pushRightInput b =>
            push (.right tmRight.k₀) (fun _ => b) (goto fun _ => .drainRightInput)
        | .runRight label =>
            taggedBranchRightStmt α γ tmLeft tmRight writeRight (tmRight.m label)
        | .readRightOutput =>
            pop (.right tmRight.k₁) (fun _ head => .output (head.map writeRight))
              (goto fun state =>
                match taggedBranchDispatchOutputState state with
                | some b => .pushRightOutputTemp b
                | none => .drainOutput)
        | .pushRightOutputTemp b =>
            push .outputTemp (fun _ => b) (goto fun _ => .readRightOutput)
        | .drainOutput =>
            pop .outputTemp (fun _ head => .output head)
              (goto fun state =>
                match taggedBranchDispatchOutputState state with
                | some b => .pushOutput b
                | none => .invalid)
        | .pushOutput b =>
            push .output (fun _ => b) (goto fun _ => .drainOutput)
        | .invalid =>
            load (fun _ => .tag none) halt }

@[simp]
def taggedBranchDispatchStacks (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    (s : TaggedBranchDispatchStack tmLeft.K tmRight.K) →
      List (taggedBranchDispatchAlphabet α γ tmLeft tmRight s)
  | .source => source
  | .left k => left k
  | .right k => right k
  | .leftInputTemp => leftTemp
  | .rightInputTemp => rightTemp
  | .output => output
  | .outputTemp => outputTemp

def taggedBranchDispatchCfg (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (label : TaggedBranchDispatchLabel tmLeft.Λ tmRight.Λ
      (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
    (state : TaggedBranchDispatchState tmLeft.σ tmRight.σ
      (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).Cfg where
  l := some label
  var := state
  stk :=
    taggedBranchDispatchStacks α γ tmLeft tmRight source left right leftTemp rightTemp
      output outputTemp

def taggedBranchDispatchHalt (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (output : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).Cfg where
  l := none
  var := .tag none
  stk
    | .source => []
    | .left _ => []
    | .right _ => []
    | .leftInputTemp => []
    | .rightInputTemp => []
    | .output => output
    | .outputTemp => []

lemma taggedBranchDispatch_initList (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (input : List (Bool ⊕ α)) :
    Turing.initList
        (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
          writeLeft writeRight) input =
      taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
        .readTag (.tag none) input (fun _ => []) (fun _ => []) [] [] [] [] := by
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg, Turing.initList]
  congr
  funext k
  cases k <;> rfl

lemma taggedBranchDispatch_haltList (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (output : List γ) :
    Turing.haltList
        (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
          writeLeft writeRight) output =
      taggedBranchDispatchHalt α γ tmLeft tmRight readLeft readRight writeLeft writeRight
        output := by
  simp [taggedBranchDispatchMachine, taggedBranchDispatchHalt, Turing.haltList]
  congr
  funext k
  cases k <;> rfl

lemma taggedBranchDispatch_readTag_step_false (α γ : Type) [Fintype α] [Fintype γ]
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
          .readTag (.tag none) (Sum.inl false :: source) left right leftTemp rightTemp
          output outputTemp) =
      some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .readLeftPayload (.tag (some false)) source left right leftTemp rightTemp
          output outputTemp) := by
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg,
    taggedBranchDispatchTagState]
  congr
  funext k
  cases k <;> rfl

lemma taggedBranchDispatch_readTag_step_true (α γ : Type) [Fintype α] [Fintype γ]
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
          .readTag (.tag none) (Sum.inl true :: source) left right leftTemp rightTemp
          output outputTemp) =
      some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .readRightPayload (.tag (some true)) source left right leftTemp rightTemp
          output outputTemp) := by
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg,
    taggedBranchDispatchTagState]
  congr
  funext k
  cases k <;> rfl

lemma taggedBranchDispatch_readLeftPayload_step_cons
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (state : TaggedBranchDispatchState tmLeft.σ tmRight.σ
      (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
    (a : α) (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).step
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .readLeftPayload state (Sum.inr a :: source) left right
          leftTemp rightTemp output outputTemp) =
      some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          (.pushLeftTemp (readLeft a)) (.leftInput (some (readLeft a))) source left right
          leftTemp rightTemp output outputTemp) := by
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg,
    taggedBranchDispatchLeftInputState]
  congr
  funext k
  cases k <;> rfl

lemma taggedBranchDispatch_readLeftPayload_step_nil
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (state : TaggedBranchDispatchState tmLeft.σ tmRight.σ
      (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).step
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .readLeftPayload state [] left right leftTemp rightTemp output
          outputTemp) =
      some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .drainLeftInput (.leftInput none) [] left right leftTemp rightTemp output
          outputTemp) := by
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg,
    taggedBranchDispatchLeftInputState]
  congr
  funext k
  cases k <;> rfl

lemma taggedBranchDispatch_pushLeftTemp_step
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (b : tmLeft.Γ tmLeft.k₀) (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).step
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          (.pushLeftTemp b) (.leftInput (some b)) source left right leftTemp rightTemp
          output outputTemp) =
      some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .readLeftPayload (.leftInput (some b)) source left right (b :: leftTemp)
          rightTemp output outputTemp) := by
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg]
  congr
  funext k
  cases k <;> rfl

def taggedBranchDispatch_readLeftPayload_run
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
        .readLeftPayload state (payload.map Sum.inr) left right
        leftTemp rightTemp output outputTemp)
      (some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .drainLeftInput (.leftInput none) [] left right
          ((payload.map readLeft).reverse ++ leftTemp) rightTemp output outputTemp))
      (2 * payload.length + 1) := by
  induction payload generalizing state leftTemp with
  | nil =>
      simpa using
        TM2Programs.evalsToInTimeOne
          (taggedBranchDispatch_readLeftPayload_step_nil α γ tmLeft tmRight readLeft
            readRight writeLeft writeRight state left right leftTemp rightTemp output outputTemp)
  | cons a payload ih =>
      let tm := taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight
      let b := readLeft a
      let c₀ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight .readLeftPayload state
        (Sum.inr a :: payload.map Sum.inr) left right leftTemp rightTemp output outputTemp
      let c₁ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight (.pushLeftTemp b) (.leftInput (some b))
        (payload.map Sum.inr) left right leftTemp rightTemp output outputTemp
      let c₂ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight .readLeftPayload (.leftInput (some b))
        (payload.map Sum.inr) left right (b :: leftTemp) rightTemp output outputTemp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne
          (taggedBranchDispatch_readLeftPayload_step_cons α γ tmLeft tmRight readLeft
            readRight writeLeft writeRight state a (payload.map Sum.inr) left right
            leftTemp rightTemp output outputTemp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        TM2Programs.evalsToInTimeOne
          (taggedBranchDispatch_pushLeftTemp_step α γ tmLeft tmRight readLeft readRight
            writeLeft writeRight b (payload.map Sum.inr) left right leftTemp rightTemp
            output outputTemp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some
            (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft
              writeRight .drainLeftInput (.leftInput none) [] left right
              ((payload.map readLeft).reverse ++ (b :: leftTemp)) rightTemp output
              outputTemp))
          (2 * payload.length + 1) :=
        by simpa [tm, c₂] using ih (.leftInput (some b)) (b :: leftTemp)
      simpa [tm, c₀, c₁, c₂, b, List.map_cons, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * payload.length + 1)
          c₀ c₂
          (some
            (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft
              writeRight .drainLeftInput (.leftInput none) [] left right
              ((payload.map readLeft).reverse ++ (b :: leftTemp)) rightTemp output
              outputTemp))
          h₁₂ hTail

lemma taggedBranchDispatch_drainLeftInput_step_cons
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (b : tmLeft.Γ tmLeft.k₀)
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
          .drainLeftInput state source left right (b :: leftTemp) rightTemp
          output outputTemp) =
      some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          (.pushLeftInput b) (.leftInput (some b)) source left right leftTemp rightTemp
          output outputTemp) := by
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg,
    taggedBranchDispatchLeftInputState]
  congr
  funext k
  cases k <;> rfl

lemma taggedBranchDispatch_drainLeftInput_step_nil
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
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).step
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .drainLeftInput state source left right [] rightTemp output outputTemp) =
      some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          (.runLeft tmLeft.main) (.leftRun tmLeft.initialState) source left right [] rightTemp
          output outputTemp) := by
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg,
    taggedBranchDispatchLeftInputState]
  congr
  funext k
  cases k <;> rfl

lemma taggedBranchDispatch_pushLeftInput_step
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (b : tmLeft.Γ tmLeft.k₀)
    (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).step
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          (.pushLeftInput b) (.leftInput (some b)) source left right leftTemp rightTemp
          output outputTemp) =
      some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .drainLeftInput (.leftInput (some b)) source
          (Function.update left tmLeft.k₀ (b :: left tmLeft.k₀)) right leftTemp rightTemp
          output outputTemp) := by
  letI := tmLeft.kDecidableEq
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg]
  congr
  funext k
  cases k with
  | source => rfl
  | left k =>
      by_cases hk : k = tmLeft.k₀
      · subst k
        simp [Function.update]
      · simp [Function.update, hk]
  | right k => rfl
  | leftInputTemp => rfl
  | rightInputTemp => rfl
  | output => rfl
  | outputTemp => rfl

def taggedBranchDispatch_drainLeftInput_run
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
        .drainLeftInput state source left right leftTemp rightTemp output outputTemp)
      (some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          (.runLeft tmLeft.main) (.leftRun tmLeft.initialState) source
          (Function.update left tmLeft.k₀ (leftTemp.reverse ++ left tmLeft.k₀)) right []
          rightTemp output outputTemp))
      (2 * leftTemp.length + 1) := by
  letI := tmLeft.kDecidableEq
  induction leftTemp generalizing left state with
  | nil =>
      simpa [Function.update] using
        TM2Programs.evalsToInTimeOne
          (taggedBranchDispatch_drainLeftInput_step_nil α γ tmLeft tmRight readLeft
            readRight writeLeft writeRight state source left right rightTemp output outputTemp)
  | cons b leftTemp ih =>
      let tm := taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight
      let c₀ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight .drainLeftInput state source left right
        (b :: leftTemp) rightTemp output outputTemp
      let c₁ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight (.pushLeftInput b) (.leftInput (some b)) source left right
        leftTemp rightTemp output outputTemp
      let left' := Function.update left tmLeft.k₀ (b :: left tmLeft.k₀)
      let c₂ := taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight
        writeLeft writeRight .drainLeftInput (.leftInput (some b)) source left' right
        leftTemp rightTemp output outputTemp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne
          (taggedBranchDispatch_drainLeftInput_step_cons α γ tmLeft tmRight readLeft
            readRight writeLeft writeRight b state source left right leftTemp rightTemp output
            outputTemp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        TM2Programs.evalsToInTimeOne
          (taggedBranchDispatch_pushLeftInput_step α γ tmLeft tmRight readLeft readRight
            writeLeft writeRight b source left right leftTemp rightTemp output outputTemp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some
            (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft
              writeRight (.runLeft tmLeft.main) (.leftRun tmLeft.initialState) source
              (Function.update left' tmLeft.k₀ (leftTemp.reverse ++ left' tmLeft.k₀))
              right [] rightTemp output outputTemp))
          (2 * leftTemp.length + 1) := by
        simpa [tm, c₂, left'] using
          ih left' (.leftInput (some b))
      simpa [tm, c₀, c₁, c₂, left', Function.update, List.reverse_cons,
        List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * leftTemp.length + 1)
          c₀ c₂
          (some
            (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft
              writeRight (.runLeft tmLeft.main) (.leftRun tmLeft.initialState) source
              (Function.update left' tmLeft.k₀ (leftTemp.reverse ++ left' tmLeft.k₀))
              right [] rightTemp output outputTemp))
          h₁₂ hTail

lemma taggedBranchDispatch_readRightPayload_step_cons
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (state : TaggedBranchDispatchState tmLeft.σ tmRight.σ
      (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
    (a : α) (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).step
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .readRightPayload state (Sum.inr a :: source) left right
          leftTemp rightTemp output outputTemp) =
      some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          (.pushRightTemp (readRight a)) (.rightInput (some (readRight a))) source left right
          leftTemp rightTemp output outputTemp) := by
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg,
    taggedBranchDispatchRightInputState]
  congr
  funext k
  cases k <;> rfl

lemma taggedBranchDispatch_readRightPayload_step_nil
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (state : TaggedBranchDispatchState tmLeft.σ tmRight.σ
      (tmLeft.Γ tmLeft.k₀) (tmRight.Γ tmRight.k₀) γ)
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).step
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .readRightPayload state [] left right leftTemp rightTemp output outputTemp) =
      some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .drainRightInput (.rightInput none) [] left right leftTemp rightTemp output
          outputTemp) := by
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg,
    taggedBranchDispatchRightInputState]
  congr
  funext k
  cases k <;> rfl

lemma taggedBranchDispatch_pushRightTemp_step
    (α γ : Type) [Fintype α] [Fintype γ]
    (tmLeft tmRight : Turing.FinTM2)
    (readLeft : α → tmLeft.Γ tmLeft.k₀)
    (readRight : α → tmRight.Γ tmRight.k₀)
    (writeLeft : tmLeft.Γ tmLeft.k₁ → γ)
    (writeRight : tmRight.Γ tmRight.k₁ → γ)
    (b : tmRight.Γ tmRight.k₀) (source : List (Bool ⊕ α))
    (left : (k : tmLeft.K) → List (tmLeft.Γ k))
    (right : (k : tmRight.K) → List (tmRight.Γ k))
    (leftTemp : List (tmLeft.Γ tmLeft.k₀))
    (rightTemp : List (tmRight.Γ tmRight.k₀))
    (output outputTemp : List γ) :
    (taggedBranchDispatchMachine α γ tmLeft tmRight readLeft readRight
      writeLeft writeRight).step
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          (.pushRightTemp b) (.rightInput (some b)) source left right leftTemp rightTemp
          output outputTemp) =
      some
        (taggedBranchDispatchCfg α γ tmLeft tmRight readLeft readRight writeLeft writeRight
          .readRightPayload (.rightInput (some b)) source left right leftTemp (b :: rightTemp)
          output outputTemp) := by
  simp [taggedBranchDispatchMachine, taggedBranchDispatchCfg]
  congr
  funext k
  cases k <;> rfl

end Karp21
end ComplexityReduction
