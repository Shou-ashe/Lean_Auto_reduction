/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.Base

namespace ComplexityReduction

namespace TM2Programs

open Turing.TM2.Stmt

/-! ### Unary natural-number subtraction -/

inductive NatSubStack where
  | input
  | work
  | output
  deriving DecidableEq, Fintype

abbrev natSubAlphabet : NatSubStack → Type
  | NatSubStack.input => Option (Bool ⊕ Bool)
  | NatSubStack.work => Unit
  | NatSubStack.output => Bool

instance (k : NatSubStack) : Fintype (natSubAlphabet k) := by
  cases k
  · exact inferInstanceAs (Fintype (Option (Bool ⊕ Bool)))
  · exact inferInstanceAs (Fintype Unit)
  · exact inferInstanceAs (Fintype Bool)

inductive NatSubLabel where
  | readLeft
  | pushLeft
  | skipDelim
  | readRight
  | cancelRight
  | drainRight
  | writeFalseFirst
  | writeTrues
  | pushTrue
  | done
  deriving DecidableEq, Fintype

inductive NatSubState where
  | readLeft
  | pushLeft
  | skipDelim
  | readRight
  | cancelRight
  | drainRight
  | writeFalseFirst
  | writeTrues
  | pushTrue
  | done
  deriving DecidableEq, Fintype

def NatSubState.label : NatSubState → NatSubLabel
  | .readLeft => .readLeft
  | .pushLeft => .pushLeft
  | .skipDelim => .skipDelim
  | .readRight => .readRight
  | .cancelRight => .cancelRight
  | .drainRight => .drainRight
  | .writeFalseFirst => .writeFalseFirst
  | .writeTrues => .writeTrues
  | .pushTrue => .pushTrue
  | .done => .done

def NatSubState.output : NatSubState → Bool
  | .pushTrue => true
  | _ => false

def natSubLeftTrue : Option (Bool ⊕ Bool) := some (Sum.inl true)
def natSubLeftFalse : Option (Bool ⊕ Bool) := some (Sum.inl false)
def natSubRightTrue : Option (Bool ⊕ Bool) := some (Sum.inr true)
def natSubRightFalse : Option (Bool ⊕ Bool) := some (Sum.inr false)

def natSubReadLeftAfterPop :
    NatSubState → Option (Option (Bool ⊕ Bool)) → NatSubState
  | .readLeft, some (some (Sum.inl true)) => .pushLeft
  | .readLeft, some (some (Sum.inl false)) => .skipDelim
  | .readLeft, _ => .readLeft
  | state, _ => state

def natSubAfterPushLeft : NatSubState → NatSubState
  | .pushLeft => .readLeft
  | state => state

def natSubAfterSkipDelim :
    NatSubState → Option (Option (Bool ⊕ Bool)) → NatSubState
  | .skipDelim, _ => .readRight
  | state, _ => state

def natSubReadRightAfterPop :
    NatSubState → Option (Option (Bool ⊕ Bool)) → NatSubState
  | .readRight, some (some (Sum.inr true)) => .cancelRight
  | .readRight, some (some (Sum.inr false)) => .writeFalseFirst
  | .readRight, none => .writeFalseFirst
  | .readRight, _ => .readRight
  | state, _ => state

def natSubAfterCancelRight : NatSubState → Option Unit → NatSubState
  | .cancelRight, some _ => .readRight
  | .cancelRight, none => .drainRight
  | state, _ => state

def natSubAfterDrainRight :
    NatSubState → Option (Option (Bool ⊕ Bool)) → NatSubState
  | .drainRight, some (some (Sum.inr false)) => .writeFalseFirst
  | .drainRight, none => .writeFalseFirst
  | .drainRight, _ => .drainRight
  | state, _ => state

def natSubAfterWriteFalseFirst : NatSubState → NatSubState
  | .writeFalseFirst => .writeTrues
  | state => state

def natSubAfterWriteTrues : NatSubState → Option Unit → NatSubState
  | .writeTrues, some _ => .pushTrue
  | .writeTrues, none => .done
  | state, _ => state

def natSubAfterPushTrue : NatSubState → NatSubState
  | .pushTrue => .writeTrues
  | state => state

def natSubAfterDone : NatSubState → NatSubState
  | .done => .readLeft
  | state => state

def natSubMachine : Turing.FinTM2 where
  K := NatSubStack
  k₀ := .input
  k₁ := .output
  Γ := natSubAlphabet
  Λ := NatSubLabel
  main := .readLeft
  σ := NatSubState
  initialState := .readLeft
  m
    | .readLeft =>
        pop .input natSubReadLeftAfterPop (goto NatSubState.label)
    | .pushLeft =>
        push .work (fun _ => ()) (load natSubAfterPushLeft (goto NatSubState.label))
    | .skipDelim =>
        pop .input natSubAfterSkipDelim (goto NatSubState.label)
    | .readRight =>
        pop .input natSubReadRightAfterPop (goto NatSubState.label)
    | .cancelRight =>
        pop .work natSubAfterCancelRight (goto NatSubState.label)
    | .drainRight =>
        pop .input natSubAfterDrainRight (goto NatSubState.label)
    | .writeFalseFirst =>
        push .output NatSubState.output
          (load natSubAfterWriteFalseFirst (goto NatSubState.label))
    | .writeTrues =>
        pop .work natSubAfterWriteTrues (goto NatSubState.label)
    | .pushTrue =>
        push .output NatSubState.output
          (load natSubAfterPushTrue (goto NatSubState.label))
    | .done =>
        load natSubAfterDone halt

def natSubCfg
    (label : Option NatSubLabel) (state : NatSubState)
    (input : List (Option (Bool ⊕ Bool))) (work : List Unit) (output : List Bool) :
    natSubMachine.Cfg where
  l := label
  var := state
  stk
    | .input => input
    | .work => work
    | .output => output

lemma natSub_initList (input : List (Option (Bool ⊕ Bool))) :
    Turing.initList natSubMachine input =
      natSubCfg (some .readLeft) .readLeft input [] [] := by
  simp [Turing.initList, natSubMachine, natSubCfg]
  congr
  funext k
  cases k <;> rfl

lemma natSub_haltList (output : List Bool) :
    Turing.haltList natSubMachine output =
      natSubCfg none .readLeft [] [] output := by
  simp [Turing.haltList, natSubMachine, natSubCfg]
  congr
  funext k
  cases k <;> rfl

lemma natSub_readLeft_true_step (input : List (Option (Bool ⊕ Bool)))
    (work : List Unit) (output : List Bool) :
    natSubMachine.step
        (natSubCfg (some .readLeft) .readLeft (natSubLeftTrue :: input) work output) =
      some (natSubCfg (some .pushLeft) .pushLeft input work output) := by
  simp [natSubMachine, natSubCfg, natSubLeftTrue, natSubReadLeftAfterPop,
    NatSubState.label]
  congr
  funext k
  cases k <;> rfl

lemma natSub_pushLeft_step (input : List (Option (Bool ⊕ Bool)))
    (work : List Unit) (output : List Bool) :
    natSubMachine.step
        (natSubCfg (some .pushLeft) .pushLeft input work output) =
      some (natSubCfg (some .readLeft) .readLeft input (() :: work) output) := by
  simp [natSubMachine, natSubCfg, natSubAfterPushLeft, NatSubState.label]
  congr
  funext k
  cases k <;> rfl

lemma natSub_readLeft_false_step (input : List (Option (Bool ⊕ Bool)))
    (work : List Unit) (output : List Bool) :
    natSubMachine.step
        (natSubCfg (some .readLeft) .readLeft (natSubLeftFalse :: input) work output) =
      some (natSubCfg (some .skipDelim) .skipDelim input work output) := by
  simp [natSubMachine, natSubCfg, natSubLeftFalse, natSubReadLeftAfterPop,
    NatSubState.label]
  congr
  funext k
  cases k <;> rfl

lemma natSub_skipDelim_step (input : List (Option (Bool ⊕ Bool)))
    (work : List Unit) (output : List Bool) :
    natSubMachine.step
        (natSubCfg (some .skipDelim) .skipDelim (none :: input) work output) =
      some (natSubCfg (some .readRight) .readRight input work output) := by
  simp [natSubMachine, natSubCfg, natSubAfterSkipDelim, NatSubState.label]
  congr
  funext k
  cases k <;> rfl

lemma natSub_readRight_true_step (input : List (Option (Bool ⊕ Bool)))
    (work : List Unit) (output : List Bool) :
    natSubMachine.step
        (natSubCfg (some .readRight) .readRight (natSubRightTrue :: input) work output) =
      some (natSubCfg (some .cancelRight) .cancelRight input work output) := by
  simp [natSubMachine, natSubCfg, natSubRightTrue, natSubReadRightAfterPop,
    NatSubState.label]
  congr
  funext k
  cases k <;> rfl

lemma natSub_cancelRight_cons_step (input : List (Option (Bool ⊕ Bool)))
    (work : List Unit) (output : List Bool) :
    natSubMachine.step
        (natSubCfg (some .cancelRight) .cancelRight input (() :: work) output) =
      some (natSubCfg (some .readRight) .readRight input work output) := by
  simp [natSubMachine, natSubCfg, natSubAfterCancelRight, NatSubState.label]
  congr
  funext k
  cases k <;> rfl

lemma natSub_cancelRight_nil_step (input : List (Option (Bool ⊕ Bool)))
    (output : List Bool) :
    natSubMachine.step
        (natSubCfg (some .cancelRight) .cancelRight input [] output) =
      some (natSubCfg (some .drainRight) .drainRight input [] output) := by
  simp [natSubMachine, natSubCfg, natSubAfterCancelRight, NatSubState.label]
  rfl

lemma natSub_readRight_false_step (work : List Unit) (output : List Bool) :
    natSubMachine.step
        (natSubCfg (some .readRight) .readRight [natSubRightFalse] work output) =
      some (natSubCfg (some .writeFalseFirst) .writeFalseFirst [] work output) := by
  simp [natSubMachine, natSubCfg, natSubRightFalse, natSubReadRightAfterPop,
    NatSubState.label]
  congr
  funext k
  cases k <;> rfl

lemma natSub_drainRight_true_step (input : List (Option (Bool ⊕ Bool)))
    (output : List Bool) :
    natSubMachine.step
        (natSubCfg (some .drainRight) .drainRight (natSubRightTrue :: input) [] output) =
      some (natSubCfg (some .drainRight) .drainRight input [] output) := by
  simp [natSubMachine, natSubCfg, natSubRightTrue, natSubAfterDrainRight,
    NatSubState.label]
  congr
  funext k
  cases k <;> rfl

lemma natSub_drainRight_false_step (output : List Bool) :
    natSubMachine.step
        (natSubCfg (some .drainRight) .drainRight [natSubRightFalse] [] output) =
      some (natSubCfg (some .writeFalseFirst) .writeFalseFirst [] [] output) := by
  simp [natSubMachine, natSubCfg, natSubRightFalse, natSubAfterDrainRight,
    NatSubState.label]
  congr
  funext k
  cases k <;> rfl

lemma natSub_writeFalseFirst_step (work : List Unit) (output : List Bool) :
    natSubMachine.step
        (natSubCfg (some .writeFalseFirst) .writeFalseFirst [] work output) =
      some (natSubCfg (some .writeTrues) .writeTrues [] work (false :: output)) := by
  simp [natSubMachine, natSubCfg, natSubAfterWriteFalseFirst, NatSubState.label,
    NatSubState.output]
  congr
  funext k
  cases k <;> rfl

lemma natSub_writeTrues_cons_step (work : List Unit) (output : List Bool) :
    natSubMachine.step
        (natSubCfg (some .writeTrues) .writeTrues [] (() :: work) output) =
      some (natSubCfg (some .pushTrue) .pushTrue [] work output) := by
  simp [natSubMachine, natSubCfg, natSubAfterWriteTrues, NatSubState.label]
  congr
  funext k
  cases k <;> rfl

lemma natSub_pushTrue_step (work : List Unit) (output : List Bool) :
    natSubMachine.step
        (natSubCfg (some .pushTrue) .pushTrue [] work output) =
      some (natSubCfg (some .writeTrues) .writeTrues [] work (true :: output)) := by
  simp [natSubMachine, natSubCfg, natSubAfterPushTrue, NatSubState.label,
    NatSubState.output]
  congr
  funext k
  cases k <;> rfl

lemma natSub_writeTrues_nil_step (output : List Bool) :
    natSubMachine.step
        (natSubCfg (some .writeTrues) .writeTrues [] [] output) =
      some (natSubCfg (some .done) .done [] [] output) := by
  simp [natSubMachine, natSubCfg, natSubAfterWriteTrues, NatSubState.label]
  rfl

lemma natSub_done_step (output : List Bool) :
    natSubMachine.step
        (natSubCfg (some .done) .done [] [] output) =
      some (natSubCfg none .readLeft [] [] output) := by
  simp [natSubMachine, natSubCfg, natSubAfterDone]
  rfl

lemma natSub_replicateUnit_append_cons (n : Nat) (work : List Unit) :
    List.replicate n () ++ () :: work = () :: (List.replicate n () ++ work) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [List.replicate_succ, List.append_assoc] using
        congrArg (fun xs => () :: xs) ih

lemma natSub_replicateTrue_append_cons (n : Nat) (output : List Bool) :
    List.replicate n true ++ true :: output =
      true :: (List.replicate n true ++ output) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [List.replicate_succ, List.append_assoc] using
        congrArg (fun xs => true :: xs) ih

def natSub_readLeftTrues_run (n : Nat)
    (input : List (Option (Bool ⊕ Bool))) (work : List Unit) (output : List Bool) :
    StateTransition.EvalsToInTime natSubMachine.step
      (natSubCfg (some .readLeft) .readLeft
        (List.replicate n natSubLeftTrue ++ input) work output)
      (some
        (natSubCfg (some .readLeft) .readLeft input
          (List.replicate n () ++ work) output))
      (2 * n) := by
  induction n generalizing work with
  | zero =>
      simpa using
        StateTransition.EvalsToInTime.refl natSubMachine.step
          (natSubCfg (some .readLeft) .readLeft input work output)
  | succ n ih =>
      let c₀ := natSubCfg (some .readLeft) .readLeft
        (natSubLeftTrue :: (List.replicate n natSubLeftTrue ++ input)) work output
      let c₁ := natSubCfg (some .pushLeft) .pushLeft
        (List.replicate n natSubLeftTrue ++ input) work output
      let c₂ := natSubCfg (some .readLeft) .readLeft
        (List.replicate n natSubLeftTrue ++ input) (() :: work) output
      let cDone := natSubCfg (some .readLeft) .readLeft input
        (List.replicate (n + 1) () ++ work) output
      have h₁ : StateTransition.EvalsToInTime natSubMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne (natSub_readLeft_true_step
          (List.replicate n natSubLeftTrue ++ input) work output)
      have h₂ : StateTransition.EvalsToInTime natSubMachine.step c₁ (some c₂) 1 :=
        evalsToInTimeOne (natSub_pushLeft_step
          (List.replicate n natSubLeftTrue ++ input) work output)
      have h₁₂ : StateTransition.EvalsToInTime natSubMachine.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans natSubMachine.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail :
          StateTransition.EvalsToInTime natSubMachine.step c₂ (some cDone) (2 * n) := by
        simpa [c₂, cDone, List.replicate_succ, List.append_assoc,
          natSub_replicateUnit_append_cons] using ih (() :: work)
      have hAll :
          StateTransition.EvalsToInTime natSubMachine.step c₀ (some cDone)
            ((1 + 1) + 2 * n) :=
        evalsToInTime_mono
          (StateTransition.EvalsToInTime.trans natSubMachine.step (1 + 1) (2 * n)
            c₀ c₂ (some cDone) h₁₂ hTail)
          (by omega)
      simpa [c₀, cDone, List.replicate_succ, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hAll

def natSub_readLeftPrefix_run (n m : Nat) :
    StateTransition.EvalsToInTime natSubMachine.step
      (natSubCfg (some .readLeft) .readLeft
        (List.replicate n natSubLeftTrue ++
          natSubLeftFalse :: none :: (List.replicate m natSubRightTrue ++ [natSubRightFalse]))
        [] [])
      (some
        (natSubCfg (some .readRight) .readRight
          (List.replicate m natSubRightTrue ++ [natSubRightFalse])
          (List.replicate n ()) []))
      (2 * n + 2) := by
  let right := List.replicate m natSubRightTrue ++ [natSubRightFalse]
  let rest := natSubLeftFalse :: none :: right
  let c₀ := natSubCfg (some .readLeft) .readLeft
    (List.replicate n natSubLeftTrue ++ rest) [] []
  let c₁ := natSubCfg (some .readLeft) .readLeft rest (List.replicate n ()) []
  let c₂ := natSubCfg (some .skipDelim) .skipDelim (none :: right) (List.replicate n ()) []
  let c₃ := natSubCfg (some .readRight) .readRight right (List.replicate n ()) []
  have hLeft : StateTransition.EvalsToInTime natSubMachine.step c₀ (some c₁) (2 * n) := by
    simpa [c₀, c₁, rest] using natSub_readLeftTrues_run n rest [] []
  have hFalse : StateTransition.EvalsToInTime natSubMachine.step c₁ (some c₂) 1 := by
    simpa [c₁, c₂, rest] using
      evalsToInTimeOne
        (natSub_readLeft_false_step (none :: right) (List.replicate n ()) [])
  have hDelim : StateTransition.EvalsToInTime natSubMachine.step c₂ (some c₃) 1 := by
    simpa [c₂, c₃] using
      evalsToInTimeOne (natSub_skipDelim_step right (List.replicate n ()) [])
  have hPrefix :
      StateTransition.EvalsToInTime natSubMachine.step c₀ (some c₂) (2 * n + 1) :=
    evalsToInTime_mono
      (StateTransition.EvalsToInTime.trans natSubMachine.step (2 * n) 1 c₀ c₁
        (some c₂) hLeft hFalse)
      (by omega)
  have hAll :
      StateTransition.EvalsToInTime natSubMachine.step c₀ (some c₃) ((2 * n + 1) + 1) :=
    evalsToInTime_mono
      (StateTransition.EvalsToInTime.trans natSubMachine.step (2 * n + 1) 1 c₀ c₂
        (some c₃) hPrefix hDelim)
      (by omega)
  simpa [c₀, c₃, rest, right, Nat.add_assoc] using hAll

def natSub_drainRight_run (m : Nat) (output : List Bool) :
    StateTransition.EvalsToInTime natSubMachine.step
      (natSubCfg (some .drainRight) .drainRight
        (List.replicate m natSubRightTrue ++ [natSubRightFalse]) [] output)
      (some (natSubCfg (some .writeFalseFirst) .writeFalseFirst [] [] output))
      (m + 1) := by
  induction m with
  | zero =>
      simpa using evalsToInTimeOne (natSub_drainRight_false_step output)
  | succ m ih =>
      let rest := List.replicate m natSubRightTrue ++ [natSubRightFalse]
      let c₀ := natSubCfg (some .drainRight) .drainRight (natSubRightTrue :: rest) [] output
      let c₁ := natSubCfg (some .drainRight) .drainRight rest [] output
      let cDone := natSubCfg (some .writeFalseFirst) .writeFalseFirst [] [] output
      have h₁ : StateTransition.EvalsToInTime natSubMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne (natSub_drainRight_true_step rest output)
      have hTail :
          StateTransition.EvalsToInTime natSubMachine.step c₁ (some cDone) (m + 1) := by
        simpa [c₁, cDone, rest] using ih
      have hAll :
          StateTransition.EvalsToInTime natSubMachine.step c₀ (some cDone) (1 + (m + 1)) :=
        evalsToInTime_mono
          (StateTransition.EvalsToInTime.trans natSubMachine.step 1 (m + 1)
            c₀ c₁ (some cDone) h₁ hTail)
          (by omega)
      simpa [c₀, cDone, rest, List.replicate_succ, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hAll

def natSub_readRight_run (n m : Nat) (output : List Bool) :
    StateTransition.EvalsToInTime natSubMachine.step
      (natSubCfg (some .readRight) .readRight
        (List.replicate m natSubRightTrue ++ [natSubRightFalse])
        (List.replicate n ()) output)
      (some
        (natSubCfg (some .writeFalseFirst) .writeFalseFirst []
          (List.replicate (n - m) ()) output))
      (2 * n + 2 * m + 1) := by
  induction n generalizing m output with
  | zero =>
      cases m with
      | zero =>
          exact evalsToInTimeOne (natSub_readRight_false_step [] output)
      | succ m =>
          let rest := List.replicate m natSubRightTrue ++ [natSubRightFalse]
          let c₀ := natSubCfg (some .readRight) .readRight (natSubRightTrue :: rest) [] output
          let c₁ := natSubCfg (some .cancelRight) .cancelRight rest [] output
          let c₂ := natSubCfg (some .drainRight) .drainRight rest [] output
          let cDone := natSubCfg (some .writeFalseFirst) .writeFalseFirst [] [] output
          have h₁ : StateTransition.EvalsToInTime natSubMachine.step c₀ (some c₁) 1 :=
            evalsToInTimeOne (natSub_readRight_true_step rest [] output)
          have h₂ : StateTransition.EvalsToInTime natSubMachine.step c₁ (some c₂) 1 :=
            evalsToInTimeOne (natSub_cancelRight_nil_step rest output)
          have hDrain :
              StateTransition.EvalsToInTime natSubMachine.step c₂ (some cDone) (m + 1) := by
            simpa [c₂, cDone, rest] using natSub_drainRight_run m output
          have h₁₂ : StateTransition.EvalsToInTime natSubMachine.step c₀ (some c₂) (1 + 1) :=
            StateTransition.EvalsToInTime.trans natSubMachine.step 1 1 c₀ c₁ (some c₂) h₁ h₂
          have hAll :
              StateTransition.EvalsToInTime natSubMachine.step c₀ (some cDone)
                ((1 + 1) + (m + 1)) :=
            evalsToInTime_mono
              (StateTransition.EvalsToInTime.trans natSubMachine.step (1 + 1) (m + 1)
                c₀ c₂ (some cDone) h₁₂ hDrain)
              (by omega)
          exact evalsToInTime_mono (by
            simpa [c₀, cDone, rest, List.replicate_succ] using hAll) (by omega)
  | succ n ih =>
      cases m with
      | zero =>
          exact evalsToInTime_mono
            (evalsToInTimeOne (natSub_readRight_false_step (List.replicate (n + 1) ()) output))
            (by omega)
      | succ m =>
          let rest := List.replicate m natSubRightTrue ++ [natSubRightFalse]
          let c₀ := natSubCfg (some .readRight) .readRight (natSubRightTrue :: rest)
            (List.replicate (n + 1) ()) output
          let c₁ := natSubCfg (some .cancelRight) .cancelRight rest
            (List.replicate (n + 1) ()) output
          let c₂ := natSubCfg (some .readRight) .readRight rest (List.replicate n ()) output
          let cDone := natSubCfg (some .writeFalseFirst) .writeFalseFirst []
            (List.replicate (n - m) ()) output
          have h₁ : StateTransition.EvalsToInTime natSubMachine.step c₀ (some c₁) 1 :=
            evalsToInTimeOne
              (natSub_readRight_true_step rest (List.replicate (n + 1) ()) output)
          have h₂ : StateTransition.EvalsToInTime natSubMachine.step c₁ (some c₂) 1 := by
            simpa [c₁, c₂, List.replicate_succ] using
              evalsToInTimeOne (natSub_cancelRight_cons_step rest (List.replicate n ()) output)
          have hTail :
              StateTransition.EvalsToInTime natSubMachine.step c₂ (some cDone)
                (2 * n + 2 * m + 1) := by
            simpa [c₂, cDone, rest] using ih m output
          have h₁₂ : StateTransition.EvalsToInTime natSubMachine.step c₀ (some c₂) (1 + 1) :=
            StateTransition.EvalsToInTime.trans natSubMachine.step 1 1 c₀ c₁ (some c₂) h₁ h₂
          have hAll :
              StateTransition.EvalsToInTime natSubMachine.step c₀ (some cDone)
                ((1 + 1) + (2 * n + 2 * m + 1)) :=
            evalsToInTime_mono
              (StateTransition.EvalsToInTime.trans natSubMachine.step (1 + 1)
                (2 * n + 2 * m + 1) c₀ c₂ (some cDone) h₁₂ hTail)
              (by omega)
          exact evalsToInTime_mono (by
            simpa [c₀, cDone, rest, List.replicate_succ, Nat.succ_sub_succ_eq_sub]
              using hAll) (by omega)

def natSub_writeTrues_run (n : Nat) (output : List Bool) :
    StateTransition.EvalsToInTime natSubMachine.step
      (natSubCfg (some .writeTrues) .writeTrues [] (List.replicate n ()) output)
      (some (natSubCfg (some .done) .done [] [] (List.replicate n true ++ output)))
      (2 * n + 1) := by
  induction n generalizing output with
  | zero =>
      simpa using evalsToInTimeOne (natSub_writeTrues_nil_step output)
  | succ n ih =>
      let c₀ := natSubCfg (some .writeTrues) .writeTrues [] (() :: List.replicate n ()) output
      let c₁ := natSubCfg (some .pushTrue) .pushTrue [] (List.replicate n ()) output
      let c₂ := natSubCfg (some .writeTrues) .writeTrues [] (List.replicate n ())
        (true :: output)
      let cDone := natSubCfg (some .done) .done [] []
        (List.replicate (n + 1) true ++ output)
      have h₁ : StateTransition.EvalsToInTime natSubMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne (natSub_writeTrues_cons_step (List.replicate n ()) output)
      have h₂ : StateTransition.EvalsToInTime natSubMachine.step c₁ (some c₂) 1 :=
        evalsToInTimeOne (natSub_pushTrue_step (List.replicate n ()) output)
      have hTail :
          StateTransition.EvalsToInTime natSubMachine.step c₂ (some cDone) (2 * n + 1) := by
        have hOut :
            List.replicate n true ++ true :: output =
              true :: (List.replicate n true ++ output) :=
          natSub_replicateTrue_append_cons n output
        simpa [c₂, cDone, List.replicate_succ, List.append_assoc, hOut] using
          ih (true :: output)
      have h₁₂ : StateTransition.EvalsToInTime natSubMachine.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans natSubMachine.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hAll :
          StateTransition.EvalsToInTime natSubMachine.step c₀ (some cDone)
            ((1 + 1) + (2 * n + 1)) :=
        evalsToInTime_mono
          (StateTransition.EvalsToInTime.trans natSubMachine.step (1 + 1) (2 * n + 1)
            c₀ c₂ (some cDone) h₁₂ hTail)
          (by omega)
      exact evalsToInTime_mono (by
        simpa [c₀, cDone, List.replicate_succ, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hAll) (by omega)

def natSub_writeAll_run (n : Nat) :
    StateTransition.EvalsToInTime natSubMachine.step
      (natSubCfg (some .writeFalseFirst) .writeFalseFirst [] (List.replicate n ()) [])
      (some (natSubCfg none .readLeft [] [] (List.replicate n true ++ [false])))
      (2 * n + 3) := by
  let c₀ := natSubCfg (some .writeFalseFirst) .writeFalseFirst [] (List.replicate n ()) []
  let c₁ := natSubCfg (some .writeTrues) .writeTrues [] (List.replicate n ()) [false]
  let c₂ := natSubCfg (some .done) .done [] [] (List.replicate n true ++ [false])
  let cDone := natSubCfg none .readLeft [] [] (List.replicate n true ++ [false])
  have hFalse : StateTransition.EvalsToInTime natSubMachine.step c₀ (some c₁) 1 :=
    evalsToInTimeOne (natSub_writeFalseFirst_step (List.replicate n ()) [])
  have hTrues : StateTransition.EvalsToInTime natSubMachine.step c₁ (some c₂) (2 * n + 1) := by
    simpa [c₁, c₂] using natSub_writeTrues_run n [false]
  have hDone : StateTransition.EvalsToInTime natSubMachine.step c₂ (some cDone) 1 :=
    evalsToInTimeOne (natSub_done_step (List.replicate n true ++ [false]))
  have hPrefix :
      StateTransition.EvalsToInTime natSubMachine.step c₀ (some c₂) (1 + (2 * n + 1)) :=
    evalsToInTime_mono
      (StateTransition.EvalsToInTime.trans natSubMachine.step 1 (2 * n + 1)
        c₀ c₁ (some c₂) hFalse hTrues)
      (by omega)
  have hAll :
      StateTransition.EvalsToInTime natSubMachine.step c₀ (some cDone)
        ((1 + (2 * n + 1)) + 1) :=
    evalsToInTime_mono
      (StateTransition.EvalsToInTime.trans natSubMachine.step (1 + (2 * n + 1)) 1
        c₀ c₂ (some cDone) hPrefix hDone)
      (by omega)
  exact evalsToInTime_mono (by
    simpa [c₀, cDone, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAll) (by omega)

noncomputable def natSubMachine_outputs (n m : Nat) :
    Turing.TM2OutputsInTime natSubMachine
      ((EncodedType.prod EncodedType.nat EncodedType.nat).encode (n, m))
      (some (EncodedType.nat.encode (n - m)))
      ((10 * Polynomial.X + 50).eval
        (((EncodedType.prod EncodedType.nat EncodedType.nat).encode (n, m)).length)) := by
  let encodedInput := (EncodedType.prod EncodedType.nat EncodedType.nat).encode (n, m)
  let right := List.replicate m natSubRightTrue ++ [natSubRightFalse]
  let cRight := natSubCfg (some .readRight) .readRight right (List.replicate n ()) []
  let cWrite := natSubCfg (some .writeFalseFirst) .writeFalseFirst []
    (List.replicate (n - m) ()) []
  let cHalt := natSubCfg none .readLeft [] [] (List.replicate (n - m) true ++ [false])
  have hInput :
      encodedInput =
        List.replicate n natSubLeftTrue ++ natSubLeftFalse :: none :: right := by
    simp [encodedInput, right, natSubLeftTrue, natSubLeftFalse, natSubRightTrue,
      natSubRightFalse, EncodedType.prod, EncodedType.nat]
  have hLeft : StateTransition.EvalsToInTime natSubMachine.step
      (Turing.initList natSubMachine encodedInput) (some cRight) (2 * n + 2) := by
    rw [hInput, natSub_initList]
    simpa [cRight, right] using natSub_readLeftPrefix_run n m
  have hRight : StateTransition.EvalsToInTime natSubMachine.step cRight (some cWrite)
      (2 * n + 2 * m + 1) := by
    simpa [cRight, cWrite, right] using natSub_readRight_run n m []
  have hWrite : StateTransition.EvalsToInTime natSubMachine.step cWrite (some cHalt)
      (2 * (n - m) + 3) := by
    simpa [cWrite, cHalt] using natSub_writeAll_run (n - m)
  have hLeftRight : StateTransition.EvalsToInTime natSubMachine.step
      (Turing.initList natSubMachine encodedInput) (some cWrite)
      ((2 * n + 2) + (2 * n + 2 * m + 1)) :=
    evalsToInTime_mono
      (StateTransition.EvalsToInTime.trans natSubMachine.step (2 * n + 2)
        (2 * n + 2 * m + 1) (Turing.initList natSubMachine encodedInput) cRight
        (some cWrite) hLeft hRight)
      (by omega)
  have hAll : StateTransition.EvalsToInTime natSubMachine.step
      (Turing.initList natSubMachine encodedInput) (some cHalt)
      (((2 * n + 2) + (2 * n + 2 * m + 1)) + (2 * (n - m) + 3)) :=
    evalsToInTime_mono
      (StateTransition.EvalsToInTime.trans natSubMachine.step
        ((2 * n + 2) + (2 * n + 2 * m + 1)) (2 * (n - m) + 3)
        (Turing.initList natSubMachine encodedInput) cWrite (some cHalt) hLeftRight hWrite)
      (by omega)
  unfold Turing.TM2OutputsInTime
  change StateTransition.EvalsToInTime natSubMachine.step
    (Turing.initList natSubMachine encodedInput)
    (some (Turing.haltList natSubMachine (EncodedType.nat.encode (n - m))))
    ((10 * Polynomial.X + 50).eval encodedInput.length)
  rw [natSub_haltList]
  refine evalsToInTime_mono (by
    simpa [encodedInput, cHalt, EncodedType.nat] using hAll) ?_
  simp [encodedInput, EncodedType.prod, EncodedType.nat, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_X]
  omega

/-- Unary natural-number subtraction is directly TM2 polynomial-time computable. -/
noncomputable def natSubComputableInPolyTime :
    Turing.TM2ComputableInPolyTime
      (EncodedType.prod EncodedType.nat EncodedType.nat).encode
      EncodedType.nat.encode
      (fun p : Nat × Nat => p.1 - p.2) where
  tm := natSubMachine
  inputAlphabet := Equiv.refl (Option (Bool ⊕ Bool))
  outputAlphabet := Equiv.refl Bool
  time := 10 * Polynomial.X + 50
  outputsFun p := by
    rcases p with ⟨(n : Nat), (m : Nat)⟩
    have h := natSubMachine_outputs n m
    have hMapReflInv :
        ∀ {α : Type} (xs : List α), List.map (Equiv.refl α).invFun xs = xs := by
      intro α xs
      induction xs with
      | nil => rfl
      | cons a as ih =>
          rw [List.map_cons, ih]
          rfl
    have hInput :
        List.map (Equiv.refl (Option (Bool ⊕ Bool))).invFun
            ((EncodedType.prod EncodedType.nat EncodedType.nat).encode (n, m)) =
          (EncodedType.prod EncodedType.nat EncodedType.nat).encode (n, m) :=
      hMapReflInv ((EncodedType.prod EncodedType.nat EncodedType.nat).encode (n, m))
    have hOutput :
        List.map (Equiv.refl Bool).invFun
            (EncodedType.nat.encode ((((n, m) : Nat × Nat).1 - ((n, m) : Nat × Nat).2))) =
          EncodedType.nat.encode (n - m) := by
      simp
    unfold Turing.TM2OutputsInTime at h ⊢
    convert h using 1
    · exact congrArg (Turing.initList natSubMachine) hInput
    · exact congrArg (fun xs => Option.map (Turing.haltList natSubMachine) (some xs)) hOutput

end TM2Programs
end ComplexityReduction
