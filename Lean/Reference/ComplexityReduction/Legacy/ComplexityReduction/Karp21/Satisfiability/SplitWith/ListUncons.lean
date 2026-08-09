/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.SplitWith.Core

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction
open Turing.TM2.Stmt

/-!
The next parser component is a typed nonempty-list uncons machine.  It is kept
local to the SAT splitter because the first use is the long-clause
decomposition parser: repeated uncons steps expose `l₁,l₂,l₃,l₄,rest`.
-/

def listUnconsLeftSymbol {α : Type} (a : α) : Option (α ⊕ Option α) :=
  some (Sum.inl a)

def listUnconsRightSymbol {α : Type} (s : Option α) : Option (α ⊕ Option α) :=
  some (Sum.inr s)

inductive ListUnconsStack where
  | input
  | output
  | headTemp
  | restTemp
  deriving DecidableEq, Fintype

inductive ListUnconsLabel where
  | readHead
  | pushHeadTemp
  | readRest
  | pushRestTemp
  | drainRest
  | pushRestOutput
  | writeDelimiter
  | drainHead
  | pushHeadOutput
  | finish
  deriving DecidableEq, Fintype

inductive ListUnconsState (α : Type) where
  | none
  | head (a : α)
  | out (s : Option (α ⊕ Option α))
  deriving DecidableEq, Fintype

def listUnconsAlphabet (α : Type) : ListUnconsStack → Type
  | .input => Option α
  | .output => Option (α ⊕ Option α)
  | .headTemp => α
  | .restTemp => Option (α ⊕ Option α)

instance (α : Type) [Fintype α] (k : ListUnconsStack) :
    Fintype (listUnconsAlphabet α k) := by
  cases k
  · exact inferInstanceAs (Fintype (Option α))
  · exact inferInstanceAs (Fintype (Option (α ⊕ Option α)))
  · exact inferInstanceAs (Fintype α)
  · exact inferInstanceAs (Fintype (Option (α ⊕ Option α)))

def listUnconsReadHeadState {α : Type} (_ : ListUnconsState α) :
    Option (Option α) → ListUnconsState α
  | some (some a) => .head a
  | _ => .none

def listUnconsReadHeadLabel {α : Type} : ListUnconsState α → ListUnconsLabel
  | .head _ => .pushHeadTemp
  | _ => .readRest

def listUnconsReadRestState {α : Type} (_ : ListUnconsState α) :
    Option (Option α) → ListUnconsState α
  | some s => .out (listUnconsRightSymbol s)
  | none => .none

def listUnconsReadRestLabel {α : Type} : ListUnconsState α → ListUnconsLabel
  | .out _ => .pushRestTemp
  | _ => .drainRest

def listUnconsDrainRestState {α : Type} (_ : ListUnconsState α) :
    Option (Option (α ⊕ Option α)) → ListUnconsState α
  | some s => .out s
  | none => .none

def listUnconsDrainRestLabel {α : Type} : ListUnconsState α → ListUnconsLabel
  | .out _ => .pushRestOutput
  | _ => .writeDelimiter

def listUnconsDrainHeadState {α : Type} (_ : ListUnconsState α) :
    Option α → ListUnconsState α
  | some a => .head a
  | none => .none

def listUnconsDrainHeadLabel {α : Type} : ListUnconsState α → ListUnconsLabel
  | .head _ => .pushHeadOutput
  | _ => .finish

def listUnconsHeadPayload {α : Type} [Inhabited α] : ListUnconsState α → α
  | .head a => a
  | _ => default

def listUnconsOutputSymbol {α : Type} : ListUnconsState α → Option (α ⊕ Option α)
  | .head a => listUnconsLeftSymbol a
  | .out s => s
  | .none => none

open Turing.TM2.Stmt in
def listUnconsMachine (α : Type) [Fintype α] [Inhabited α] : Turing.FinTM2 where
  K := ListUnconsStack
  k₀ := .input
  k₁ := .output
  Γ := listUnconsAlphabet α
  Λ := ListUnconsLabel
  main := .readHead
  σ := ListUnconsState α
  initialState := .none
  m
    | .readHead =>
        pop .input listUnconsReadHeadState
          (goto listUnconsReadHeadLabel)
    | .pushHeadTemp =>
        push .headTemp listUnconsHeadPayload
          (load (fun _ => ListUnconsState.none) (goto fun _ => .readHead))
    | .readRest =>
        pop .input listUnconsReadRestState
          (goto listUnconsReadRestLabel)
    | .pushRestTemp =>
        push .restTemp listUnconsOutputSymbol
          (load (fun _ => ListUnconsState.none) (goto fun _ => .readRest))
    | .drainRest =>
        pop .restTemp listUnconsDrainRestState
          (goto listUnconsDrainRestLabel)
    | .pushRestOutput =>
        push .output listUnconsOutputSymbol
          (load (fun _ => ListUnconsState.none) (goto fun _ => .drainRest))
    | .writeDelimiter =>
        push .output (fun _ => none)
          (load (fun _ => ListUnconsState.none) (goto fun _ => .drainHead))
    | .drainHead =>
        pop .headTemp listUnconsDrainHeadState
          (goto listUnconsDrainHeadLabel)
    | .pushHeadOutput =>
        push .output listUnconsOutputSymbol
          (load (fun _ => ListUnconsState.none) (goto fun _ => .drainHead))
    | .finish => halt

def listUnconsCfg (α : Type) [Fintype α] [Inhabited α]
    (label : Option ListUnconsLabel) (state : ListUnconsState α)
    (input : List (Option α)) (output : List (Option (α ⊕ Option α)))
    (headTemp : List α) (restTemp : List (Option (α ⊕ Option α))) :
    (listUnconsMachine α).Cfg where
  l := label
  var := state
  stk
    | .input => input
    | .output => output
    | .headTemp => headTemp
    | .restTemp => restTemp

def listUnconsHalt (α : Type) [Fintype α] [Inhabited α]
    (output : List (Option (α ⊕ Option α))) :
    (listUnconsMachine α).Cfg :=
  listUnconsCfg α none .none [] output [] []

lemma listUncons_initList (α : Type) [Fintype α] [Inhabited α]
    (input : List (Option α)) :
    Turing.initList (listUnconsMachine α) input =
      listUnconsCfg α (some .readHead) .none input [] [] [] := by
  simp [Turing.initList, listUnconsMachine, listUnconsCfg]
  congr
  funext k
  cases k <;> rfl

lemma listUncons_haltList (α : Type) [Fintype α] [Inhabited α]
    (output : List (Option (α ⊕ Option α))) :
    Turing.haltList (listUnconsMachine α) output =
      listUnconsHalt α output := by
  simp [Turing.haltList, listUnconsMachine, listUnconsHalt, listUnconsCfg]
  congr
  funext k
  cases k <;> rfl

lemma listUncons_readHead_step_payload (α : Type) [Fintype α] [Inhabited α]
    (a : α) (input : List (Option α)) (output : List (Option (α ⊕ Option α)))
    (headTemp : List α) (restTemp : List (Option (α ⊕ Option α))) :
    (listUnconsMachine α).step
        (listUnconsCfg α (some .readHead) .none (some a :: input) output headTemp restTemp) =
      some (listUnconsCfg α (some .pushHeadTemp) (.head a) input output headTemp restTemp) := by
  simp [listUnconsMachine, listUnconsCfg, listUnconsReadHeadState,
    listUnconsReadHeadLabel]
  congr
  funext k
  cases k <;> rfl

lemma listUncons_readHead_step_delimiter (α : Type) [Fintype α] [Inhabited α]
    (input : List (Option α)) (output : List (Option (α ⊕ Option α)))
    (headTemp : List α) (restTemp : List (Option (α ⊕ Option α))) :
    (listUnconsMachine α).step
        (listUnconsCfg α (some .readHead) .none (none :: input) output headTemp restTemp) =
      some (listUnconsCfg α (some .readRest) .none input output headTemp restTemp) := by
  simp [listUnconsMachine, listUnconsCfg, listUnconsReadHeadState,
    listUnconsReadHeadLabel]
  congr
  funext k
  cases k <;> rfl

lemma listUncons_pushHeadTemp_step (α : Type) [Fintype α] [Inhabited α]
    (a : α) (input : List (Option α)) (output : List (Option (α ⊕ Option α)))
    (headTemp : List α) (restTemp : List (Option (α ⊕ Option α))) :
    (listUnconsMachine α).step
        (listUnconsCfg α (some .pushHeadTemp) (.head a) input output headTemp restTemp) =
      some (listUnconsCfg α (some .readHead) .none input output (a :: headTemp) restTemp) := by
  simp [listUnconsMachine, listUnconsCfg, listUnconsHeadPayload]
  congr
  funext k
  cases k <;> rfl

def listUncons_readHead_run (α : Type) [Fintype α] [Inhabited α]
    (payload : List α) (rest : List (Option α))
    (output : List (Option (α ⊕ Option α)))
    (headTemp : List α) (restTemp : List (Option (α ⊕ Option α))) :
    StateTransition.EvalsToInTime (listUnconsMachine α).step
      (listUnconsCfg α (some .readHead) .none
        (payload.map some ++ none :: rest) output headTemp restTemp)
      (some
        (listUnconsCfg α (some .readRest) .none rest output
          (payload.reverse ++ headTemp) restTemp))
      (2 * payload.length + 1) := by
  induction payload generalizing headTemp with
  | nil =>
      simpa using
        TM2Programs.evalsToInTimeOne
          (listUncons_readHead_step_delimiter α rest output headTemp restTemp)
  | cons a payload ih =>
      let c₀ := listUnconsCfg α (some .readHead) .none
        (some a :: (payload.map some ++ none :: rest)) output headTemp restTemp
      let c₁ := listUnconsCfg α (some .pushHeadTemp) (.head a)
        (payload.map some ++ none :: rest) output headTemp restTemp
      let c₂ := listUnconsCfg α (some .readHead) .none
        (payload.map some ++ none :: rest) output (a :: headTemp) restTemp
      let done := listUnconsCfg α (some .readRest) .none rest output
        (payload.reverse ++ a :: headTemp) restTemp
      have h₁ : StateTransition.EvalsToInTime (listUnconsMachine α).step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne
          (listUncons_readHead_step_payload α a
            (payload.map some ++ none :: rest) output headTemp restTemp)
      have h₂ : StateTransition.EvalsToInTime (listUnconsMachine α).step c₁ (some c₂) 1 :=
        TM2Programs.evalsToInTimeOne
          (listUncons_pushHeadTemp_step α a
            (payload.map some ++ none :: rest) output headTemp restTemp)
      have h₁₂ : StateTransition.EvalsToInTime (listUnconsMachine α).step c₀ (some c₂)
          (1 + 1) :=
        StateTransition.EvalsToInTime.trans (listUnconsMachine α).step 1 1
          c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime (listUnconsMachine α).step c₂
          (some done) (2 * payload.length + 1) := by
        simpa [c₂, done] using ih (a :: headTemp)
      have hAll : StateTransition.EvalsToInTime (listUnconsMachine α).step c₀
          (some done) ((2 * payload.length + 1) + (1 + 1)) :=
        StateTransition.EvalsToInTime.trans (listUnconsMachine α).step (1 + 1)
          (2 * payload.length + 1) c₀ c₂ (some done) h₁₂ hTail
      simpa [c₀, done, List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using hAll

lemma listUncons_readRest_step_cons (α : Type) [Fintype α] [Inhabited α]
    (s : Option α) (input : List (Option α)) (output : List (Option (α ⊕ Option α)))
    (headTemp : List α) (restTemp : List (Option (α ⊕ Option α))) :
    (listUnconsMachine α).step
        (listUnconsCfg α (some .readRest) .none (s :: input) output headTemp restTemp) =
      some
        (listUnconsCfg α (some .pushRestTemp) (.out (listUnconsRightSymbol s)) input
          output headTemp restTemp) := by
  simp [listUnconsMachine, listUnconsCfg, listUnconsReadRestState,
    listUnconsReadRestLabel]
  congr
  funext k
  cases k <;> rfl

lemma listUncons_readRest_step_nil (α : Type) [Fintype α] [Inhabited α]
    (output : List (Option (α ⊕ Option α))) (headTemp : List α)
    (restTemp : List (Option (α ⊕ Option α))) :
    (listUnconsMachine α).step
        (listUnconsCfg α (some .readRest) .none [] output headTemp restTemp) =
      some (listUnconsCfg α (some .drainRest) .none [] output headTemp restTemp) := by
  simp [listUnconsMachine, listUnconsCfg, listUnconsReadRestState,
    listUnconsReadRestLabel]
  congr
  funext k
  cases k <;> rfl

lemma listUncons_pushRestTemp_step (α : Type) [Fintype α] [Inhabited α]
    (s : Option α) (input : List (Option α)) (output : List (Option (α ⊕ Option α)))
    (headTemp : List α) (restTemp : List (Option (α ⊕ Option α))) :
    (listUnconsMachine α).step
        (listUnconsCfg α (some .pushRestTemp) (.out (listUnconsRightSymbol s)) input
          output headTemp restTemp) =
      some
        (listUnconsCfg α (some .readRest) .none input output headTemp
          (listUnconsRightSymbol s :: restTemp)) := by
  simp [listUnconsMachine, listUnconsCfg, listUnconsOutputSymbol]
  congr
  funext k
  cases k <;> rfl

def listUncons_readRest_run (α : Type) [Fintype α] [Inhabited α]
    (input : List (Option α)) (output : List (Option (α ⊕ Option α)))
    (headTemp : List α) (restTemp : List (Option (α ⊕ Option α))) :
    StateTransition.EvalsToInTime (listUnconsMachine α).step
      (listUnconsCfg α (some .readRest) .none input output headTemp restTemp)
      (some
        (listUnconsCfg α (some .drainRest) .none [] output headTemp
          ((input.map listUnconsRightSymbol).reverse ++ restTemp)))
      (2 * input.length + 1) := by
  induction input generalizing restTemp with
  | nil =>
      simpa using
        TM2Programs.evalsToInTimeOne
          (listUncons_readRest_step_nil α output headTemp restTemp)
  | cons s input ih =>
      let c₀ := listUnconsCfg α (some .readRest) .none (s :: input)
        output headTemp restTemp
      let c₁ := listUnconsCfg α (some .pushRestTemp) (.out (listUnconsRightSymbol s))
        input output headTemp restTemp
      let c₂ := listUnconsCfg α (some .readRest) .none input output headTemp
        (listUnconsRightSymbol s :: restTemp)
      let done := listUnconsCfg α (some .drainRest) .none [] output headTemp
        ((input.map listUnconsRightSymbol).reverse ++
          listUnconsRightSymbol s :: restTemp)
      have h₁ : StateTransition.EvalsToInTime (listUnconsMachine α).step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne
          (listUncons_readRest_step_cons α s input output headTemp restTemp)
      have h₂ : StateTransition.EvalsToInTime (listUnconsMachine α).step c₁ (some c₂) 1 :=
        TM2Programs.evalsToInTimeOne
          (listUncons_pushRestTemp_step α s input output headTemp restTemp)
      have h₁₂ : StateTransition.EvalsToInTime (listUnconsMachine α).step c₀ (some c₂)
          (1 + 1) :=
        StateTransition.EvalsToInTime.trans (listUnconsMachine α).step 1 1
          c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime (listUnconsMachine α).step c₂
          (some done) (2 * input.length + 1) := by
        simpa [c₂, done] using ih (listUnconsRightSymbol s :: restTemp)
      have hAll : StateTransition.EvalsToInTime (listUnconsMachine α).step c₀
          (some done) ((2 * input.length + 1) + (1 + 1)) :=
        StateTransition.EvalsToInTime.trans (listUnconsMachine α).step (1 + 1)
          (2 * input.length + 1) c₀ c₂ (some done) h₁₂ hTail
      simpa [c₀, done, List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using hAll

lemma listUncons_drainRest_step_cons (α : Type) [Fintype α] [Inhabited α]
    (s : Option (α ⊕ Option α)) (output : List (Option (α ⊕ Option α)))
    (headTemp : List α) (restTemp : List (Option (α ⊕ Option α))) :
    (listUnconsMachine α).step
        (listUnconsCfg α (some .drainRest) .none [] output headTemp (s :: restTemp)) =
      some (listUnconsCfg α (some .pushRestOutput) (.out s) [] output headTemp restTemp) := by
  simp [listUnconsMachine, listUnconsCfg, listUnconsDrainRestState,
    listUnconsDrainRestLabel]
  congr
  funext k
  cases k <;> rfl

lemma listUncons_drainRest_step_nil (α : Type) [Fintype α] [Inhabited α]
    (output : List (Option (α ⊕ Option α))) (headTemp : List α) :
    (listUnconsMachine α).step
        (listUnconsCfg α (some .drainRest) .none [] output headTemp []) =
      some (listUnconsCfg α (some .writeDelimiter) .none [] output headTemp []) := by
  simp [listUnconsMachine, listUnconsCfg, listUnconsDrainRestState,
    listUnconsDrainRestLabel]
  congr
  funext k
  cases k <;> rfl

lemma listUncons_pushRestOutput_step (α : Type) [Fintype α] [Inhabited α]
    (s : Option (α ⊕ Option α)) (output : List (Option (α ⊕ Option α)))
    (headTemp : List α) (restTemp : List (Option (α ⊕ Option α))) :
    (listUnconsMachine α).step
        (listUnconsCfg α (some .pushRestOutput) (.out s) [] output headTemp restTemp) =
      some (listUnconsCfg α (some .drainRest) .none [] (s :: output) headTemp restTemp) := by
  simp [listUnconsMachine, listUnconsCfg, listUnconsOutputSymbol]
  congr
  funext k
  cases k <;> rfl

def listUncons_drainRest_run (α : Type) [Fintype α] [Inhabited α]
    (restTemp : List (Option (α ⊕ Option α))) (output : List (Option (α ⊕ Option α)))
    (headTemp : List α) :
    StateTransition.EvalsToInTime (listUnconsMachine α).step
      (listUnconsCfg α (some .drainRest) .none [] output headTemp restTemp)
      (some
        (listUnconsCfg α (some .writeDelimiter) .none [] (restTemp.reverse ++ output)
          headTemp []))
      (2 * restTemp.length + 1) := by
  induction restTemp generalizing output with
  | nil =>
      simpa using
        TM2Programs.evalsToInTimeOne
          (listUncons_drainRest_step_nil α output headTemp)
  | cons s restTemp ih =>
      let c₀ := listUnconsCfg α (some .drainRest) .none [] output headTemp (s :: restTemp)
      let c₁ := listUnconsCfg α (some .pushRestOutput) (.out s) [] output headTemp restTemp
      let c₂ := listUnconsCfg α (some .drainRest) .none [] (s :: output) headTemp restTemp
      let done := listUnconsCfg α (some .writeDelimiter) .none []
        (restTemp.reverse ++ s :: output) headTemp []
      have h₁ : StateTransition.EvalsToInTime (listUnconsMachine α).step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne
          (listUncons_drainRest_step_cons α s output headTemp restTemp)
      have h₂ : StateTransition.EvalsToInTime (listUnconsMachine α).step c₁ (some c₂) 1 :=
        TM2Programs.evalsToInTimeOne
          (listUncons_pushRestOutput_step α s output headTemp restTemp)
      have h₁₂ : StateTransition.EvalsToInTime (listUnconsMachine α).step c₀ (some c₂)
          (1 + 1) :=
        StateTransition.EvalsToInTime.trans (listUnconsMachine α).step 1 1
          c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime (listUnconsMachine α).step c₂
          (some done) (2 * restTemp.length + 1) := by
        simpa [c₂, done] using ih (s :: output)
      have hAll : StateTransition.EvalsToInTime (listUnconsMachine α).step c₀
          (some done) ((2 * restTemp.length + 1) + (1 + 1)) :=
        StateTransition.EvalsToInTime.trans (listUnconsMachine α).step (1 + 1)
          (2 * restTemp.length + 1) c₀ c₂ (some done) h₁₂ hTail
      simpa [c₀, done, List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using hAll

lemma listUncons_writeDelimiter_step (α : Type) [Fintype α] [Inhabited α]
    (output : List (Option (α ⊕ Option α))) (headTemp : List α) :
    (listUnconsMachine α).step
        (listUnconsCfg α (some .writeDelimiter) .none [] output headTemp []) =
      some (listUnconsCfg α (some .drainHead) .none [] (none :: output) headTemp []) := by
  simp [listUnconsMachine, listUnconsCfg]
  congr
  funext k
  cases k <;> rfl

lemma listUncons_drainHead_step_cons (α : Type) [Fintype α] [Inhabited α]
    (a : α) (headTemp : List α) (output : List (Option (α ⊕ Option α))) :
    (listUnconsMachine α).step
        (listUnconsCfg α (some .drainHead) .none [] output (a :: headTemp) []) =
      some (listUnconsCfg α (some .pushHeadOutput) (.head a) [] output headTemp []) := by
  simp [listUnconsMachine, listUnconsCfg, listUnconsDrainHeadState,
    listUnconsDrainHeadLabel]
  congr
  funext k
  cases k <;> rfl

lemma listUncons_drainHead_step_nil (α : Type) [Fintype α] [Inhabited α]
    (output : List (Option (α ⊕ Option α))) :
    (listUnconsMachine α).step
        (listUnconsCfg α (some .drainHead) .none [] output [] []) =
      some (listUnconsCfg α (some .finish) .none [] output [] []) := by
  simp [listUnconsMachine, listUnconsCfg, listUnconsDrainHeadState,
    listUnconsDrainHeadLabel]
  congr
  funext k
  cases k <;> rfl

lemma listUncons_pushHeadOutput_step (α : Type) [Fintype α] [Inhabited α]
    (a : α) (headTemp : List α) (output : List (Option (α ⊕ Option α))) :
    (listUnconsMachine α).step
        (listUnconsCfg α (some .pushHeadOutput) (.head a) [] output headTemp []) =
      some
        (listUnconsCfg α (some .drainHead) .none []
          (listUnconsLeftSymbol a :: output) headTemp []) := by
  simp [listUnconsMachine, listUnconsCfg, listUnconsOutputSymbol]
  congr
  funext k
  cases k <;> rfl

lemma listUncons_finish_step (α : Type) [Fintype α] [Inhabited α]
    (output : List (Option (α ⊕ Option α))) :
    (listUnconsMachine α).step
        (listUnconsCfg α (some .finish) .none [] output [] []) =
      some (listUnconsHalt α output) := by
  rfl

def listUncons_drainHead_run (α : Type) [Fintype α] [Inhabited α]
    (headTemp : List α) (output : List (Option (α ⊕ Option α))) :
    StateTransition.EvalsToInTime (listUnconsMachine α).step
      (listUnconsCfg α (some .drainHead) .none [] output headTemp [])
      (some (listUnconsHalt α (headTemp.reverse.map listUnconsLeftSymbol ++ output)))
      (2 * headTemp.length + 2) := by
  induction headTemp generalizing output with
  | nil =>
      let c₀ := listUnconsCfg α (some .drainHead) .none [] output [] []
      let c₁ := listUnconsCfg α (some .finish) .none [] output [] []
      have h₁ : StateTransition.EvalsToInTime (listUnconsMachine α).step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne
          (listUncons_drainHead_step_nil α output)
      have h₂ : StateTransition.EvalsToInTime (listUnconsMachine α).step c₁
          (some (listUnconsHalt α output)) 1 :=
        TM2Programs.evalsToInTimeOne
          (listUncons_finish_step α output)
      have hAll : StateTransition.EvalsToInTime (listUnconsMachine α).step c₀
          (some (listUnconsHalt α output)) (1 + 1) :=
        StateTransition.EvalsToInTime.trans (listUnconsMachine α).step 1 1
          c₀ c₁ (some (listUnconsHalt α output)) h₁ h₂
      simpa [c₀, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAll
  | cons a headTemp ih =>
      let c₀ := listUnconsCfg α (some .drainHead) .none [] output (a :: headTemp) []
      let c₁ := listUnconsCfg α (some .pushHeadOutput) (.head a) [] output headTemp []
      let c₂ := listUnconsCfg α (some .drainHead) .none []
        (listUnconsLeftSymbol a :: output) headTemp []
      let done := listUnconsHalt α
        (headTemp.reverse.map listUnconsLeftSymbol ++ listUnconsLeftSymbol a :: output)
      have h₁ : StateTransition.EvalsToInTime (listUnconsMachine α).step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne
          (listUncons_drainHead_step_cons α a headTemp output)
      have h₂ : StateTransition.EvalsToInTime (listUnconsMachine α).step c₁ (some c₂) 1 :=
        TM2Programs.evalsToInTimeOne
          (listUncons_pushHeadOutput_step α a headTemp output)
      have h₁₂ : StateTransition.EvalsToInTime (listUnconsMachine α).step c₀ (some c₂)
          (1 + 1) :=
        StateTransition.EvalsToInTime.trans (listUnconsMachine α).step 1 1
          c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime (listUnconsMachine α).step c₂
          (some done) (2 * headTemp.length + 2) := by
        simpa [c₂, done] using ih (listUnconsLeftSymbol a :: output)
      have hAll : StateTransition.EvalsToInTime (listUnconsMachine α).step c₀
          (some done) ((2 * headTemp.length + 2) + (1 + 1)) :=
        StateTransition.EvalsToInTime.trans (listUnconsMachine α).step (1 + 1)
          (2 * headTemp.length + 2) c₀ c₂ (some done) h₁₂ hTail
      simpa [c₀, done, List.reverse_cons, List.map_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using hAll

def listUncons_outputs (α : Type) [Fintype α] [Inhabited α]
    (payload : List α) (rest : List (Option α)) :
    Turing.TM2OutputsInTime (listUnconsMachine α)
      (payload.map some ++ none :: rest)
      (some
        (payload.map listUnconsLeftSymbol ++
          none :: rest.map listUnconsRightSymbol))
      (4 * (payload.map some ++ none :: rest).length + 6) := by
  let rightTemp := (rest.map listUnconsRightSymbol).reverse
  let rightOutput := rest.map listUnconsRightSymbol
  let afterHead := listUnconsCfg α (some .readRest) .none rest [] payload.reverse []
  let afterReadRest := listUnconsCfg α (some .drainRest) .none [] []
    payload.reverse rightTemp
  let afterDrainRest := listUnconsCfg α (some .writeDelimiter) .none []
    rightOutput payload.reverse []
  let afterDelimiter := listUnconsCfg α (some .drainHead) .none []
    (none :: rightOutput) payload.reverse []
  let finalOutput :=
    payload.map listUnconsLeftSymbol ++ none :: rightOutput
  have hHead : StateTransition.EvalsToInTime (listUnconsMachine α).step
      (Turing.initList (listUnconsMachine α) (payload.map some ++ none :: rest))
      (some afterHead) (2 * payload.length + 1) := by
    simpa [afterHead, listUncons_initList] using
      listUncons_readHead_run α payload rest [] [] []
  have hReadRest : StateTransition.EvalsToInTime (listUnconsMachine α).step
      afterHead (some afterReadRest) (2 * rest.length + 1) := by
    simpa [afterHead, afterReadRest, rightTemp] using
      listUncons_readRest_run α rest [] payload.reverse []
  have hDrainRest : StateTransition.EvalsToInTime (listUnconsMachine α).step
      afterReadRest (some afterDrainRest) (2 * rightTemp.length + 1) := by
    have h := listUncons_drainRest_run α rightTemp [] payload.reverse
    simpa [afterReadRest, afterDrainRest, rightTemp, rightOutput] using h
  have hDelimiter : StateTransition.EvalsToInTime (listUnconsMachine α).step
      afterDrainRest (some afterDelimiter) 1 := by
    simpa [afterDrainRest, afterDelimiter] using
      TM2Programs.evalsToInTimeOne
        (listUncons_writeDelimiter_step α rightOutput payload.reverse)
  have hDrainHead : StateTransition.EvalsToInTime (listUnconsMachine α).step
      afterDelimiter (some (listUnconsHalt α finalOutput))
      (2 * payload.reverse.length + 2) := by
    have h := listUncons_drainHead_run α payload.reverse (none :: rightOutput)
    simpa [afterDelimiter, finalOutput, rightOutput, List.map_reverse, List.reverse_reverse,
      List.map_map, Function.comp_def, List.append_assoc] using h
  have hHeadRead : StateTransition.EvalsToInTime (listUnconsMachine α).step
      (Turing.initList (listUnconsMachine α) (payload.map some ++ none :: rest))
      (some afterReadRest) ((2 * rest.length + 1) + (2 * payload.length + 1)) :=
    StateTransition.EvalsToInTime.trans (listUnconsMachine α).step
      (2 * payload.length + 1) (2 * rest.length + 1)
      (Turing.initList (listUnconsMachine α) (payload.map some ++ none :: rest))
      afterHead (some afterReadRest) hHead hReadRest
  have hHeadReadDrain : StateTransition.EvalsToInTime (listUnconsMachine α).step
      (Turing.initList (listUnconsMachine α) (payload.map some ++ none :: rest))
      (some afterDrainRest)
      ((2 * rightTemp.length + 1) + ((2 * rest.length + 1) + (2 * payload.length + 1))) :=
    StateTransition.EvalsToInTime.trans (listUnconsMachine α).step
      ((2 * rest.length + 1) + (2 * payload.length + 1)) (2 * rightTemp.length + 1)
      (Turing.initList (listUnconsMachine α) (payload.map some ++ none :: rest))
      afterReadRest (some afterDrainRest) hHeadRead hDrainRest
  have hBeforeHeadDrain : StateTransition.EvalsToInTime (listUnconsMachine α).step
      (Turing.initList (listUnconsMachine α) (payload.map some ++ none :: rest))
      (some afterDelimiter)
      (1 + ((2 * rightTemp.length + 1) +
        ((2 * rest.length + 1) + (2 * payload.length + 1)))) :=
    StateTransition.EvalsToInTime.trans (listUnconsMachine α).step
      ((2 * rightTemp.length + 1) + ((2 * rest.length + 1) + (2 * payload.length + 1)))
      1
      (Turing.initList (listUnconsMachine α) (payload.map some ++ none :: rest))
      afterDrainRest (some afterDelimiter) hHeadReadDrain hDelimiter
  have hAllExact : StateTransition.EvalsToInTime (listUnconsMachine α).step
      (Turing.initList (listUnconsMachine α) (payload.map some ++ none :: rest))
      (some (listUnconsHalt α finalOutput))
      ((2 * payload.reverse.length + 2) +
        (1 + ((2 * rightTemp.length + 1) +
          ((2 * rest.length + 1) + (2 * payload.length + 1))))) :=
    StateTransition.EvalsToInTime.trans (listUnconsMachine α).step
      (1 + ((2 * rightTemp.length + 1) +
        ((2 * rest.length + 1) + (2 * payload.length + 1))))
      (2 * payload.reverse.length + 2)
      (Turing.initList (listUnconsMachine α) (payload.map some ++ none :: rest))
      afterDelimiter (some (listUnconsHalt α finalOutput)) hBeforeHeadDrain hDrainHead
  change StateTransition.EvalsToInTime (listUnconsMachine α).step
    (Turing.initList (listUnconsMachine α) (payload.map some ++ none :: rest))
    (some
      (Turing.haltList (listUnconsMachine α)
        (payload.map listUnconsLeftSymbol ++ none :: rest.map listUnconsRightSymbol)))
    (4 * (payload.map some ++ none :: rest).length + 6)
  rw [listUncons_haltList]
  exact TM2Programs.evalsToInTime_mono (by simpa [finalOutput] using hAllExact) (by
    simp [rightTemp]
    omega)

def nonemptyClauseEncodedType : EncodedType where
  Carrier := { c : SAT.Clause // 0 < c.length }
  Symbol := clauseStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun c => clauseStructuredEncodedType.encode c.1

def clauseHeadTailEncodedType : EncodedType :=
  EncodedType.prod literalStructuredEncodedType clauseStructuredEncodedType

def nonemptyClauseUncons
    (c : nonemptyClauseEncodedType.Carrier) : clauseHeadTailEncodedType.Carrier :=
  match c with
  | ⟨[], h⟩ => False.elim (Nat.not_lt_zero 0 h)
  | ⟨l :: rest, _⟩ => (l, rest)

theorem nonemptyClauseUncons_encode_cons (l : SAT.Literal) (rest : SAT.Clause)
    (h : 0 < (l :: rest).length) :
    clauseHeadTailEncodedType.encode (nonemptyClauseUncons ⟨l :: rest, h⟩) =
      (literalStructuredEncodedType.encode l).map listUnconsLeftSymbol ++
        none :: (clauseStructuredEncodedType.encode rest).map listUnconsRightSymbol := by
  dsimp [clauseHeadTailEncodedType, nonemptyClauseUncons, EncodedType.prod]
  dsimp [clauseStructuredEncodedType, listUnconsLeftSymbol, listUnconsRightSymbol]
  have hLeft :
      (literalStructuredEncodedType.encode l).map listUnconsLeftSymbol =
        (literalStructuredEncodedType.encode l).map (fun s => some (Sum.inl s)) := by
    induction literalStructuredEncodedType.encode l with
    | nil => rfl
    | cons s xs ih =>
        change listUnconsLeftSymbol s :: xs.map listUnconsLeftSymbol =
          some (Sum.inl s) :: xs.map (fun s => some (Sum.inl s))
        rw [show listUnconsLeftSymbol s = some (Sum.inl s) from rfl, ih]
  have hRight :
      (literalStructuredEncodedType.list.encode rest).map listUnconsRightSymbol =
        (literalStructuredEncodedType.list.encode rest).map (fun s => some (Sum.inr s)) := by
    induction literalStructuredEncodedType.list.encode rest with
    | nil => rfl
    | cons s xs ih =>
        change listUnconsRightSymbol s :: xs.map listUnconsRightSymbol =
          some (Sum.inr s) :: xs.map (fun s => some (Sum.inr s))
        rw [show listUnconsRightSymbol s = some (Sum.inr s) from rfl, ih]
        rfl
  rw [hLeft, hRight]
  have hAppend
      (xs ys : List (Option (literalStructuredEncodedType.Symbol ⊕ Option
        literalStructuredEncodedType.Symbol))) :
      xs ++ [none] ++ ys = xs ++ none :: ys := by
    induction xs with
    | nil => rfl
    | cons s xs ih =>
        simp [ih]
  exact hAppend _ _

noncomputable def nonemptyClauseUnconsTMBackedMap :
    TMBackedCostedMap
      nonemptyClauseEncodedType clauseHeadTailEncodedType nonemptyClauseUncons where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := nonemptyClauseEncodedType)
      (Y := clauseHeadTailEncodedType)
      (LinearSizeBound.intro_with 1 0 (by
        intro c
        rcases c with ⟨c, hc⟩
        cases c with
        | nil =>
            exact False.elim (Nat.not_lt_zero 0 hc)
        | cons l rest =>
            change
              clauseHeadTailEncodedType.inputSize (l, rest) ≤
                1 * nonemptyClauseEncodedType.inputSize ⟨l :: rest, hc⟩ + 0
            have hSize :
                nonemptyClauseEncodedType.inputSize ⟨l :: rest, hc⟩ =
                  literalStructuredEncodedType.inputSize l + 1 +
                    clauseStructuredEncodedType.inputSize rest := by
              change
                (EncodedType.list literalStructuredEncodedType).inputSize (l :: rest) =
                  literalStructuredEncodedType.inputSize l + 1 +
                    (EncodedType.list literalStructuredEncodedType).inputSize rest
              rw [EncodedType.inputSize_list_cons]
            simp [clauseHeadTailEncodedType, hSize]))
  tm_polytime :=
    ⟨{ tm := listUnconsMachine literalStructuredEncodedType.Symbol
       inputAlphabet := Equiv.refl clauseStructuredEncodedType.Symbol
       outputAlphabet := Equiv.refl clauseHeadTailEncodedType.Symbol
       time := 4 * Polynomial.X + 6
       outputsFun := by
        intro c
        rcases c with ⟨c, hc⟩
        cases c with
        | nil =>
            exact False.elim (Nat.not_lt_zero 0 hc)
        | cons l rest =>
            have hInput :
                nonemptyClauseEncodedType.encode ⟨l :: rest, hc⟩ =
                  (literalStructuredEncodedType.encode l).map some ++
                    none :: clauseStructuredEncodedType.encode rest := by
              dsimp [nonemptyClauseEncodedType, clauseStructuredEncodedType, EncodedType.list]
              change ((literalStructuredEncodedType.encode l).map some ++ [none]) ++
                  List.flatMap
                    (fun x => (literalStructuredEncodedType.encode x).map some ++ [none])
                    rest =
                (literalStructuredEncodedType.encode l).map some ++
                  none :: List.flatMap
                    (fun x => (literalStructuredEncodedType.encode x).map some ++ [none])
                    rest
              simp [List.append_assoc]
            have hOutput :
                clauseHeadTailEncodedType.encode
                    (nonemptyClauseUncons ⟨l :: rest, hc⟩) =
                  (literalStructuredEncodedType.encode l).map listUnconsLeftSymbol ++
                    none :: (clauseStructuredEncodedType.encode rest).map
                      listUnconsRightSymbol :=
              nonemptyClauseUncons_encode_cons l rest hc
            convert
              listUncons_outputs literalStructuredEncodedType.Symbol
                (literalStructuredEncodedType.encode l)
                (clauseStructuredEncodedType.encode rest) using 1
            · rw [hInput]
              change
                List.map id
                    ((literalStructuredEncodedType.encode l).map some ++
                      none :: clauseStructuredEncodedType.encode rest) =
                  (literalStructuredEncodedType.encode l).map some ++
                    none :: clauseStructuredEncodedType.encode rest
              simp
            · rw [hOutput]
              change
                some (List.map id
                    ((literalStructuredEncodedType.encode l).map listUnconsLeftSymbol ++
                      none :: (clauseStructuredEncodedType.encode rest).map
                        listUnconsRightSymbol)) =
                  some
                    ((literalStructuredEncodedType.encode l).map listUnconsLeftSymbol ++
                      none :: (clauseStructuredEncodedType.encode rest).map
                        listUnconsRightSymbol)
              simp
            · rw [hInput]
              simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
              have hLen (xs : List literalStructuredEncodedType.Symbol)
                  (ys : List clauseStructuredEncodedType.Symbol) :
                  (xs.map some ++ none :: ys).length = xs.length + (ys.length + 1) := by
                induction xs with
                | nil =>
                    simp
                    rfl
                | cons s xs ih =>
                    simp [ih]
                    omega
              exact hLen (literalStructuredEncodedType.encode l)
                (clauseStructuredEncodedType.encode rest) }⟩

/-- Structured clauses carrying a lower bound on their list length. -/
def clauseMinLengthEncodedType (n : Nat) : EncodedType where
  Carrier := { c : SAT.Clause // n ≤ c.length }
  Symbol := clauseStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun c => clauseStructuredEncodedType.encode c.1

/-- Forget the length proof on a bounded structured clause without changing its encoding. -/
noncomputable def clauseMinLengthForgetTMBackedMap (n : Nat) :
    TMBackedCostedMap (clauseMinLengthEncodedType n) clauseStructuredEncodedType
      (fun c => c.1) :=
  TMBackedCostedMap.ofEncodingEquiv
    (clauseMinLengthEncodedType n) clauseStructuredEncodedType
    (fun c => c.1) (Equiv.refl clauseStructuredEncodedType.Symbol) (by
      intro c
      change clauseStructuredEncodedType.encode c.1 =
        List.map id (clauseStructuredEncodedType.encode c.1)
      simp)

/--
Typed delimiter-list uncons for clauses known to have length at least `n + 1`.
The tail keeps the residual lower bound `n ≤ tail.length`, which is what the
four-literal payload parser needs for repeated uncons.
-/
def clauseMinLengthUncons (n : Nat)
    (c : (clauseMinLengthEncodedType (n + 1)).Carrier) :
    (EncodedType.prod literalStructuredEncodedType (clauseMinLengthEncodedType n)).Carrier :=
  match c with
  | ⟨[], h⟩ => by
      simp at h
  | ⟨l :: rest, h⟩ => (l, ⟨rest, by simp at h; omega⟩)

theorem clauseMinLengthUncons_encode_cons (n : Nat) (l : SAT.Literal) (rest : SAT.Clause)
    (h : n + 1 ≤ (l :: rest).length) :
    (EncodedType.prod literalStructuredEncodedType (clauseMinLengthEncodedType n)).encode
        (clauseMinLengthUncons n ⟨l :: rest, h⟩) =
      (literalStructuredEncodedType.encode l).map listUnconsLeftSymbol ++
        none :: (clauseStructuredEncodedType.encode rest).map listUnconsRightSymbol := by
  simpa [clauseMinLengthUncons, clauseMinLengthEncodedType, clauseHeadTailEncodedType] using
    nonemptyClauseUncons_encode_cons l rest (by simp)

/-- Direct TM-backed typed uncons for clauses with an explicit lower length bound. -/
noncomputable def clauseMinLengthUnconsTMBackedMap (n : Nat) :
    TMBackedCostedMap
      (clauseMinLengthEncodedType (n + 1))
      (EncodedType.prod literalStructuredEncodedType (clauseMinLengthEncodedType n))
      (clauseMinLengthUncons n) where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := clauseMinLengthEncodedType (n + 1))
      (Y := EncodedType.prod literalStructuredEncodedType (clauseMinLengthEncodedType n))
      (LinearSizeBound.intro_with 1 0 (by
        intro c
        rcases c with ⟨c, hc⟩
        cases c with
        | nil =>
            simp at hc
        | cons l rest =>
            have hInput :
                (clauseMinLengthEncodedType (n + 1)).inputSize ⟨l :: rest, hc⟩ =
                  literalStructuredEncodedType.inputSize l + 1 +
                    clauseStructuredEncodedType.inputSize rest := by
              change
                (EncodedType.list literalStructuredEncodedType).inputSize (l :: rest) =
                  literalStructuredEncodedType.inputSize l + 1 +
                    (EncodedType.list literalStructuredEncodedType).inputSize rest
              rw [EncodedType.inputSize_list_cons]
            rw [hInput]
            simp [clauseMinLengthUncons]
            change clauseStructuredEncodedType.inputSize rest ≤
              clauseStructuredEncodedType.inputSize rest
            rfl))
  tm_polytime :=
    ⟨{ tm := listUnconsMachine literalStructuredEncodedType.Symbol
       inputAlphabet := Equiv.refl clauseStructuredEncodedType.Symbol
       outputAlphabet :=
        Equiv.refl
          (EncodedType.prod literalStructuredEncodedType
            (clauseMinLengthEncodedType n)).Symbol
       time := 4 * Polynomial.X + 6
       outputsFun := by
        intro c
        rcases c with ⟨c, hc⟩
        cases c with
        | nil =>
            simp at hc
        | cons l rest =>
            have hInput :
                (clauseMinLengthEncodedType (n + 1)).encode ⟨l :: rest, hc⟩ =
                  (literalStructuredEncodedType.encode l).map some ++
                    none :: clauseStructuredEncodedType.encode rest := by
              dsimp [clauseMinLengthEncodedType, clauseStructuredEncodedType, EncodedType.list]
              change ((literalStructuredEncodedType.encode l).map some ++ [none]) ++
                  List.flatMap
                    (fun x => (literalStructuredEncodedType.encode x).map some ++ [none])
                    rest =
                (literalStructuredEncodedType.encode l).map some ++
                  none :: List.flatMap
                    (fun x => (literalStructuredEncodedType.encode x).map some ++ [none])
                    rest
              simp [List.append_assoc]
            have hOutput :
                (EncodedType.prod literalStructuredEncodedType
                    (clauseMinLengthEncodedType n)).encode
                    (clauseMinLengthUncons n ⟨l :: rest, hc⟩) =
                  (literalStructuredEncodedType.encode l).map listUnconsLeftSymbol ++
                    none :: (clauseStructuredEncodedType.encode rest).map
                      listUnconsRightSymbol :=
              clauseMinLengthUncons_encode_cons n l rest hc
            convert
              listUncons_outputs literalStructuredEncodedType.Symbol
                (literalStructuredEncodedType.encode l)
                (clauseStructuredEncodedType.encode rest) using 1
            · rw [hInput]
              change
                List.map id
                    ((literalStructuredEncodedType.encode l).map some ++
                      none :: clauseStructuredEncodedType.encode rest) =
                  (literalStructuredEncodedType.encode l).map some ++
                    none :: clauseStructuredEncodedType.encode rest
              simp
            · rw [hOutput]
              change
                some (List.map id
                    ((literalStructuredEncodedType.encode l).map listUnconsLeftSymbol ++
                      none :: (clauseStructuredEncodedType.encode rest).map
                        listUnconsRightSymbol)) =
                  some
                    ((literalStructuredEncodedType.encode l).map listUnconsLeftSymbol ++
                      none :: (clauseStructuredEncodedType.encode rest).map
                        listUnconsRightSymbol)
              simp
            · rw [hInput]
              simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
              have hLen (xs : List literalStructuredEncodedType.Symbol)
                  (ys : List clauseStructuredEncodedType.Symbol) :
                  (xs.map some ++ none :: ys).length = xs.length + (ys.length + 1) := by
                induction xs with
                | nil =>
                    simp
                    rfl
                | cons s xs ih =>
                    simp [ih]
                    omega
              exact hLen (literalStructuredEncodedType.encode l)
                (clauseStructuredEncodedType.encode rest) }⟩


end Karp21
end ComplexityReduction
