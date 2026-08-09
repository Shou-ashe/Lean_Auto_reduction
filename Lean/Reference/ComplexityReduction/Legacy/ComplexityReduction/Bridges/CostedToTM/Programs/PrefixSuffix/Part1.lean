/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.Base

namespace ComplexityReduction
namespace TM2Programs

open Turing.TM2.Stmt

/-- Stack indices for the prefix-map program used by sum injections. -/
inductive PrefixMapStack where
  | input
  | output
  | temp
  deriving DecidableEq, Fintype

/-- Stack alphabets for a program that maps input symbols and prepends one output tag. -/
abbrev prefixMapAlphabet (α β : Type) : PrefixMapStack → Type
  | PrefixMapStack.input => α
  | PrefixMapStack.output => β
  | PrefixMapStack.temp => β

/-- Control labels for the prefix-map program. -/
inductive PrefixMapLabel (β : Type) where
  | readInput
  | pushTemp (b : β)
  | moveTemp
  | pushOutput (b : β)
  | writePrefix
  deriving DecidableEq, Fintype

/--
A concrete TM2 program for `input ↦ pref :: input.map mapSym`.

The program first pops and maps the input stack into a temporary stack, then
moves the temporary stack back to the output stack so the original order is
restored, and finally pushes the fixed prefix/tag.
-/
def prefixMapMachine (α β : Type) [Fintype α] [Fintype β]
    (pref : β) (mapSym : α → β) : Turing.FinTM2 where
  K := PrefixMapStack
  k₀ := PrefixMapStack.input
  k₁ := PrefixMapStack.output
  Γ := prefixMapAlphabet α β
  Λ := PrefixMapLabel β
  main := PrefixMapLabel.readInput
  σ := Option β
  initialState := none
  Γk₀Fin := by
    dsimp [prefixMapAlphabet]
    infer_instance
  m
    | PrefixMapLabel.readInput =>
        pop PrefixMapStack.input (fun _ head => head.map mapSym)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some b => PrefixMapLabel.pushTemp b
              | none => PrefixMapLabel.moveTemp)
            (goto fun _ => PrefixMapLabel.moveTemp))
    | PrefixMapLabel.pushTemp b =>
        push PrefixMapStack.temp (fun _ => b) (goto fun _ => PrefixMapLabel.readInput)
    | PrefixMapLabel.moveTemp =>
        pop PrefixMapStack.temp (fun _ head => head)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some b => PrefixMapLabel.pushOutput b
              | none => PrefixMapLabel.writePrefix)
            (goto fun _ => PrefixMapLabel.writePrefix))
    | PrefixMapLabel.pushOutput b =>
        push PrefixMapStack.output (fun _ => b) (goto fun _ => PrefixMapLabel.moveTemp)
    | PrefixMapLabel.writePrefix =>
        push PrefixMapStack.output (fun _ => pref) (load (fun _ => none) halt)

/-- A named configuration for the prefix-map program. -/
def prefixMapCfg (α β : Type) [Fintype α] [Fintype β]
    (pref : β) (mapSym : α → β) (label : PrefixMapLabel β) (state : Option β)
    (input : List α) (output temp : List β) :
    (prefixMapMachine α β pref mapSym).Cfg where
  l := some label
  var := state
  stk
    | PrefixMapStack.input => input
    | PrefixMapStack.output => output
    | PrefixMapStack.temp => temp

/-- A named halt configuration for the prefix-map program. -/
def prefixMapHalt (α β : Type) [Fintype α] [Fintype β]
    (pref : β) (mapSym : α → β) (output : List β) :
    (prefixMapMachine α β pref mapSym).Cfg where
  l := none
  var := none
  stk
    | PrefixMapStack.input => []
    | PrefixMapStack.output => output
    | PrefixMapStack.temp => []

/--
An upper bound on the number of stack symbols that one TM2 statement can push
while executing a single `FinTM2.step`.

This deliberately ignores stack identities and branches by taking a coarse max;
it is a machine-independent ingredient for later sequential composition and
arbitrary product/list runners.
-/
def stmtPushCount {K : Type} {Γ : K → Type} {Λ σ : Type} :
    Turing.TM2.Stmt Γ Λ σ → Nat
  | Turing.TM2.Stmt.push _ _ q => stmtPushCount q + 1
  | Turing.TM2.Stmt.peek _ _ q => stmtPushCount q
  | Turing.TM2.Stmt.pop _ _ q => stmtPushCount q
  | Turing.TM2.Stmt.load _ q => stmtPushCount q
  | Turing.TM2.Stmt.branch _ qTrue qFalse =>
      max (stmtPushCount qTrue) (stmtPushCount qFalse)
  | Turing.TM2.Stmt.goto _ => 0
  | Turing.TM2.Stmt.halt => 0

/-- A coarse per-step push bound for a bundled finite TM2 machine. -/
def finTM2StepPushBound (tm : Turing.FinTM2) : Nat := by
  letI := tm.ΛFin
  exact Finset.univ.sup (fun label : tm.Λ => stmtPushCount (tm.m label))

lemma stmtPushCount_le_finTM2StepPushBound (tm : Turing.FinTM2) (label : tm.Λ) :
    stmtPushCount (tm.m label) ≤ finTM2StepPushBound tm := by
  unfold finTM2StepPushBound
  letI := tm.ΛFin
  exact Finset.le_sup (f := fun label : tm.Λ => stmtPushCount (tm.m label))
    (Finset.mem_univ label)

lemma stepAux_stack_length_le {K : Type} [DecidableEq K] {Γ : K → Type}
    {Λ σ : Type} (q : Turing.TM2.Stmt Γ Λ σ) (v : σ)
    (stk : (k : K) → List (Γ k)) (k : K) :
    ((Turing.TM2.stepAux q v stk).stk k).length ≤
      (stk k).length + stmtPushCount q := by
  induction q generalizing v stk with
  | push k' f q ih =>
      have hTail :=
        ih v (Function.update stk k' (f v :: stk k'))
      by_cases hk : k = k'
      · subst k'
        calc
          ((Turing.TM2.stepAux q v (Function.update stk k (f v :: stk k))).stk k).length
              ≤ (stk k).length + 1 + stmtPushCount q := by
                simpa [Function.update] using hTail
          _ ≤ (stk k).length + (stmtPushCount q + 1) := by omega
      · have hUpdate :
            (Function.update stk k' (f v :: stk k') k).length = (stk k).length := by
          simp [Function.update, hk]
        calc
          ((Turing.TM2.stepAux q v (Function.update stk k' (f v :: stk k'))).stk k).length
              ≤ (Function.update stk k' (f v :: stk k') k).length + stmtPushCount q :=
                hTail
          _ = (stk k).length + stmtPushCount q := by rw [hUpdate]
          _ ≤ (stk k).length + (stmtPushCount q + 1) := by omega
  | peek k' f q ih =>
      simpa [stmtPushCount] using ih (f v (stk k').head?) stk
  | pop k' f q ih =>
      have hTail :=
        ih (f v (stk k').head?) (Function.update stk k' (stk k').tail)
      by_cases hk : k = k'
      · subst k'
        have hTailLen : (stk k).tail.length ≤ (stk k).length := by
          cases stk k <;> simp
        calc
          ((Turing.TM2.stepAux q (f v (stk k).head?)
              (Function.update stk k (stk k).tail)).stk k).length
              ≤ (Function.update stk k (stk k).tail k).length + stmtPushCount q :=
                hTail
          _ = (stk k).tail.length + stmtPushCount q := by simp [Function.update]
          _ ≤ (stk k).length + stmtPushCount q := by
                exact Nat.add_le_add_right hTailLen _
      · have hUpdate :
            (Function.update stk k' (stk k').tail k).length = (stk k).length := by
          simp [Function.update, hk]
        calc
          ((Turing.TM2.stepAux q (f v (stk k').head?)
              (Function.update stk k' (stk k').tail)).stk k).length
              ≤ (Function.update stk k' (stk k').tail k).length + stmtPushCount q :=
                hTail
          _ = (stk k).length + stmtPushCount q := by rw [hUpdate]
  | load f q ih =>
      simpa [stmtPushCount] using ih (f v) stk
  | branch f qTrue qFalse ihTrue ihFalse =>
      by_cases hf : f v
      · have h := ihTrue v stk
        have h' :
            ((Turing.TM2.stepAux qTrue v stk).stk k).length ≤
              (stk k).length + max (stmtPushCount qTrue) (stmtPushCount qFalse) :=
          h.trans (Nat.add_le_add_left (Nat.le_max_left _ _) _)
        simpa [stmtPushCount, hf] using h'
      · have h := ihFalse v stk
        have h' :
            ((Turing.TM2.stepAux qFalse v stk).stk k).length ≤
              (stk k).length + max (stmtPushCount qTrue) (stmtPushCount qFalse) :=
          h.trans (Nat.add_le_add_left (Nat.le_max_right _ _) _)
        simpa [stmtPushCount, hf] using h'
  | goto f =>
      simp [stmtPushCount]
  | halt =>
      simp [stmtPushCount]

lemma finTM2_step_output_length_le (tm : Turing.FinTM2)
    {cfg next : tm.Cfg} (hStep : tm.step cfg = some next) :
    (next.stk tm.k₁).length ≤
      (cfg.stk tm.k₁).length + finTM2StepPushBound tm := by
  cases cfg with
  | mk label var stk =>
      cases label with
      | none =>
          simp [Turing.FinTM2.step, Turing.TM2.step] at hStep
      | some label =>
          have hAux :
              next =
                Turing.TM2.stepAux (tm.m label) var stk := by
            have hSome :
                some (Turing.TM2.stepAux (tm.m label) var stk) = some next := by
              simpa [Turing.FinTM2.step, Turing.TM2.step] using hStep
            exact (Option.some.inj hSome).symm
          rw [hAux]
          exact (stepAux_stack_length_le (tm.m label) var stk tm.k₁).trans
            (Nat.add_le_add_left (stmtPushCount_le_finTM2StepPushBound tm label)
              (stk tm.k₁).length)

lemma optionBind_iterate_none {σ : Type} (f : σ → Option σ) (n : Nat) :
    (flip Option.bind f)^[n] (none : Option σ) = none := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] (none : Option σ) = none
      exact ih

lemma option_map_iterate_bind {σ τ : Type} (f : σ → Option σ) (g : τ → Option τ)
    (embed : σ → τ) (hstep : ∀ s, g (embed s) = Option.map embed (f s))
    (n : Nat) (s : σ) :
    (flip Option.bind g)^[n] (some (embed s)) =
      Option.map embed ((flip Option.bind f)^[n] (some s)) := by
  induction n generalizing s with
  | zero =>
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind g)^[n] (g (embed s)) =
        Option.map embed ((flip Option.bind f)^[n] (f s))
      rw [hstep s]
      cases hs : f s with
      | none =>
          simp [optionBind_iterate_none]
      | some s' =>
          simp
          exact ih s'

def evalsToInTime_map {σ τ : Type} {f : σ → Option σ} {g : τ → Option τ}
    (embed : σ → τ) (hstep : ∀ s, g (embed s) = Option.map embed (f s))
    {a : σ} {b : Option σ} {time : Nat}
    (h : StateTransition.EvalsToInTime f a b time) :
    StateTransition.EvalsToInTime g (embed a) (Option.map embed b) time where
  steps := h.steps
  evals_in_steps := by
    have hIter := option_map_iterate_bind f g embed hstep h.steps a
    have hEval : (flip Option.bind f)^[h.steps] (some a) = b := by
      simpa using h.evals_in_steps
    rw [hEval] at hIter
    simpa using hIter
  steps_le_m := h.steps_le_m

lemma option_map_iterate_bind_some {σ τ : Type} (f : σ → Option σ) (g : τ → Option τ)
    (embed : σ → τ)
    (hstep : ∀ s s', f s = some s' → g (embed s) = some (embed s'))
    {n : Nat} {s t : σ}
    (hEval : (flip Option.bind f)^[n] (some s) = some t) :
    (flip Option.bind g)^[n] (some (embed s)) = some (embed t) := by
  induction n generalizing s with
  | zero =>
      simp at hEval
      subst hEval
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hEval ⊢
      change (flip Option.bind f)^[n] (f s) = some t at hEval
      change (flip Option.bind g)^[n] (g (embed s)) = some (embed t)
      cases hs : f s with
      | none =>
          rw [hs] at hEval
          rw [optionBind_iterate_none] at hEval
          cases hEval
      | some s' =>
          rw [hs] at hEval
          rw [hstep s s' hs]
          exact ih hEval

def evalsToInTime_map_some {σ τ : Type} {f : σ → Option σ} {g : τ → Option τ}
    (embed : σ → τ)
    (hstep : ∀ s s', f s = some s' → g (embed s) = some (embed s'))
    {a b : σ} {time : Nat}
    (h : StateTransition.EvalsToInTime f a (some b) time) :
    StateTransition.EvalsToInTime g (embed a) (some (embed b)) time where
  steps := h.steps
  evals_in_steps := by
    have hEval : (flip Option.bind f)^[h.steps] (some a) = some b := by
      simpa using h.evals_in_steps
    simpa using option_map_iterate_bind_some f g embed hstep hEval
  steps_le_m := h.steps_le_m

lemma outputStackLength_iterate_le (tm : Turing.FinTM2) (n : Nat)
    {cfg next : tm.Cfg}
    (hEval : (flip bind tm.step)^[n] cfg = some next) :
    (next.stk tm.k₁).length ≤
      (cfg.stk tm.k₁).length + n * finTM2StepPushBound tm := by
  induction n generalizing cfg with
  | zero =>
      simp at hEval
      subst hEval
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hEval
      change (flip Option.bind tm.step)^[n] (tm.step cfg) = some next at hEval
      change (flip Option.bind (Turing.TM2.step tm.m))^[n]
        (Turing.TM2.step tm.m cfg) = some next at hEval
      cases hStep : Turing.TM2.step tm.m cfg with
      | none =>
          rw [hStep] at hEval
          have hNone :=
            optionBind_iterate_none (Turing.TM2.step tm.m) n
          have hContr : (none : Option tm.Cfg) = some next :=
            hNone.symm.trans hEval
          cases hContr
      | some mid =>
          have hTail : (next.stk tm.k₁).length ≤
              (mid.stk tm.k₁).length + n * finTM2StepPushBound tm :=
            ih (by simpa [hStep] using hEval)
          have hHead : (mid.stk tm.k₁).length ≤
              (cfg.stk tm.k₁).length + finTM2StepPushBound tm :=
            finTM2_step_output_length_le tm (by
              simpa [Turing.FinTM2.step] using hStep)
          calc
            (next.stk tm.k₁).length
                ≤ (mid.stk tm.k₁).length + n * finTM2StepPushBound tm := hTail
            _ ≤ ((cfg.stk tm.k₁).length + finTM2StepPushBound tm) +
                  n * finTM2StepPushBound tm := by
                exact Nat.add_le_add_right hHead _
            _ ≤ (cfg.stk tm.k₁).length + (n + 1) * finTM2StepPushBound tm := by
                rw [Nat.add_mul, one_mul]
                omega

lemma list_length_cast {α β : Type} (h : α = β) (xs : List α) :
    (cast (congrArg List h) xs : List β).length = xs.length := by
  cases h
  rfl

lemma initList_output_length_le_input_length (tm : Turing.FinTM2)
    (input : List (tm.Γ tm.k₀)) :
    ((Turing.initList tm input).stk tm.k₁).length ≤ input.length := by
  by_cases h : tm.k₁ = tm.k₀
  · have hLen := list_length_cast (congrArg tm.Γ h.symm) input
    simp [Turing.initList, h]
    exact Nat.le_of_eq hLen
  · simp [Turing.initList, h]

/--
Any TM2 computation that halts within `time` steps can output only linearly many
symbols in `time`, with a machine-dependent constant.  This is the output-size
bound needed before composing polynomial-time TM2 witnesses.
-/
theorem tm2OutputsInTime_output_length_le (tm : Turing.FinTM2)
    (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (time : Nat)
    (h : Turing.TM2OutputsInTime tm input (some output) time) :
    output.length ≤ input.length + time * finTM2StepPushBound tm := by
  have hIter := outputStackLength_iterate_le tm h.steps h.evals_in_steps
  have hSteps : h.steps * finTM2StepPushBound tm ≤ time * finTM2StepPushBound tm :=
    Nat.mul_le_mul_right _ h.steps_le_m
  have hInit := initList_output_length_le_input_length tm input
  have hHalt :
      output.length = ((Turing.haltList tm output).stk tm.k₁).length := by
    simp [Turing.haltList]
  rw [hHalt]
  calc
    ((Turing.haltList tm output).stk tm.k₁).length
        ≤ ((Turing.initList tm input).stk tm.k₁).length +
            h.steps * finTM2StepPushBound tm := hIter
    _ ≤ input.length + h.steps * finTM2StepPushBound tm := by
          exact Nat.add_le_add_right hInit _
    _ ≤ input.length + time * finTM2StepPushBound tm := by
          exact Nat.add_le_add_left hSteps _

/--
Output-size consequence of a bundled polynomial-time TM2 witness.

This does not prove composition by itself; it supplies the missing polynomial
intermediate-output bound needed by a future constructive composition runner.
-/
theorem tm2ComputableInPolyTime_output_length_le
    {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f : α → β} (h : Turing.TM2ComputableInPolyTime ea eb f) (a : α) :
    (eb (f a)).length ≤
      (ea a).length + h.time.eval (ea a).length * finTM2StepPushBound h.tm := by
  have hOut :=
    tm2OutputsInTime_output_length_le h.tm
      (List.map h.inputAlphabet.invFun (ea a))
      (List.map h.outputAlphabet.invFun (eb (f a)))
      (h.time.eval (ea a).length)
      (h.outputsFun a)
  simpa using hOut

lemma prefixMap_readInput_step_cons (α β : Type) [Fintype α] [Fintype β]
    (pref : β) (mapSym : α → β) (state : Option β)
    (a : α) (input : List α) (output temp : List β) :
    (prefixMapMachine α β pref mapSym).step
        (prefixMapCfg α β pref mapSym PrefixMapLabel.readInput state
          (a :: input) output temp) =
      some (prefixMapCfg α β pref mapSym (PrefixMapLabel.pushTemp (mapSym a))
        (some (mapSym a)) input output temp) := by
  simp [prefixMapMachine, prefixMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma prefixMap_readInput_step_nil (α β : Type) [Fintype α] [Fintype β]
    (pref : β) (mapSym : α → β) (state : Option β) (output temp : List β) :
    (prefixMapMachine α β pref mapSym).step
        (prefixMapCfg α β pref mapSym PrefixMapLabel.readInput state [] output temp) =
      some (prefixMapCfg α β pref mapSym PrefixMapLabel.moveTemp none [] output temp) := by
  simp [prefixMapMachine, prefixMapCfg]
  congr

lemma prefixMap_pushTemp_step (α β : Type) [Fintype α] [Fintype β]
    (pref : β) (mapSym : α → β) (state : Option β)
    (b : β) (input : List α) (output temp : List β) :
    (prefixMapMachine α β pref mapSym).step
        (prefixMapCfg α β pref mapSym (PrefixMapLabel.pushTemp b) state
          input output temp) =
      some (prefixMapCfg α β pref mapSym PrefixMapLabel.readInput state input output
        (b :: temp)) := by
  simp [prefixMapMachine, prefixMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma prefixMap_moveTemp_step_cons (α β : Type) [Fintype α] [Fintype β]
    (pref : β) (mapSym : α → β) (state : Option β)
    (input : List α) (output : List β) (b : β) (temp : List β) :
    (prefixMapMachine α β pref mapSym).step
        (prefixMapCfg α β pref mapSym PrefixMapLabel.moveTemp state input output
          (b :: temp)) =
      some (prefixMapCfg α β pref mapSym (PrefixMapLabel.pushOutput b) (some b)
        input output temp) := by
  simp [prefixMapMachine, prefixMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma prefixMap_moveTemp_step_nil (α β : Type) [Fintype α] [Fintype β]
    (pref : β) (mapSym : α → β) (state : Option β) (input : List α)
    (output : List β) :
    (prefixMapMachine α β pref mapSym).step
        (prefixMapCfg α β pref mapSym PrefixMapLabel.moveTemp state input output []) =
      some (prefixMapCfg α β pref mapSym PrefixMapLabel.writePrefix none input output []) := by
  simp [prefixMapMachine, prefixMapCfg]
  congr

lemma prefixMap_pushOutput_step (α β : Type) [Fintype α] [Fintype β]
    (pref : β) (mapSym : α → β) (state : Option β)
    (input : List α) (output : List β) (b : β) (temp : List β) :
    (prefixMapMachine α β pref mapSym).step
        (prefixMapCfg α β pref mapSym (PrefixMapLabel.pushOutput b) state input output
          temp) =
      some (prefixMapCfg α β pref mapSym PrefixMapLabel.moveTemp state input
        (b :: output) temp) := by
  simp [prefixMapMachine, prefixMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma prefixMap_writePrefix_step (α β : Type) [Fintype α] [Fintype β]
    (pref : β) (mapSym : α → β) (state : Option β) (output : List β) :
    (prefixMapMachine α β pref mapSym).step
        (prefixMapCfg α β pref mapSym PrefixMapLabel.writePrefix state [] output []) =
      some (prefixMapHalt α β pref mapSym (pref :: output)) := by
  simp [prefixMapMachine, prefixMapCfg, prefixMapHalt]
  congr
  funext k
  cases k <;> rfl

lemma initList_prefixMapMachine (α β : Type) [Fintype α] [Fintype β]
    (pref : β) (mapSym : α → β) (input : List α) :
    Turing.initList (prefixMapMachine α β pref mapSym) input =
      prefixMapCfg α β pref mapSym PrefixMapLabel.readInput none input [] [] := by
  simp [prefixMapMachine, prefixMapCfg, Turing.initList]
  congr
  funext k
  cases k <;> rfl

lemma haltList_prefixMapMachine (α β : Type) [Fintype α] [Fintype β]
    (pref : β) (mapSym : α → β) (output : List β) :
    Turing.haltList (prefixMapMachine α β pref mapSym) output =
      prefixMapHalt α β pref mapSym output := by
  simp [prefixMapMachine, prefixMapHalt, Turing.haltList]
  congr
  funext k
  cases k <;> rfl

def prefixMap_readInput_run (α β : Type) [Fintype α] [Fintype β]
    (pref : β) (mapSym : α → β) (state : Option β)
    (input : List α) (output temp : List β) :
    StateTransition.EvalsToInTime (prefixMapMachine α β pref mapSym).step
      (prefixMapCfg α β pref mapSym PrefixMapLabel.readInput state input output temp)
      (some (prefixMapCfg α β pref mapSym PrefixMapLabel.moveTemp none [] output
        ((input.map mapSym).reverse ++ temp)))
      (2 * input.length + 1) := by
  induction input generalizing state temp with
  | nil =>
      simpa using
        evalsToInTimeOne
          (prefixMap_readInput_step_nil α β pref mapSym state output temp)
  | cons a input ih =>
      let tm := prefixMapMachine α β pref mapSym
      let c₀ := prefixMapCfg α β pref mapSym PrefixMapLabel.readInput state
        (a :: input) output temp
      let c₁ := prefixMapCfg α β pref mapSym (PrefixMapLabel.pushTemp (mapSym a))
        (some (mapSym a)) input output temp
      let c₂ := prefixMapCfg α β pref mapSym PrefixMapLabel.readInput (some (mapSym a))
        input output (mapSym a :: temp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (prefixMap_readInput_step_cons α β pref mapSym state a input output temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (prefixMap_pushTemp_step α β pref mapSym (some (mapSym a))
            (mapSym a) input output temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (prefixMapCfg α β pref mapSym PrefixMapLabel.moveTemp none [] output
            ((input.map mapSym).reverse ++ (mapSym a :: temp))))
          (2 * input.length + 1) :=
        ih (some (mapSym a)) (mapSym a :: temp)
      simpa [tm, c₀, c₁, c₂, List.map_cons, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * input.length + 1)
          c₀ c₂
          (some (prefixMapCfg α β pref mapSym PrefixMapLabel.moveTemp none [] output
            ((input.map mapSym).reverse ++ (mapSym a :: temp))))
          h₁₂ hTail

def prefixMap_moveTemp_run (α β : Type) [Fintype α] [Fintype β]
    (pref : β) (mapSym : α → β) (state : Option β)
    (input : List α) (output temp : List β) :
    StateTransition.EvalsToInTime (prefixMapMachine α β pref mapSym).step
      (prefixMapCfg α β pref mapSym PrefixMapLabel.moveTemp state input output temp)
      (some (prefixMapCfg α β pref mapSym PrefixMapLabel.writePrefix none input
        (temp.reverse ++ output) []))
      (2 * temp.length + 1) := by
  induction temp generalizing state output with
  | nil =>
      simpa using
        evalsToInTimeOne
          (prefixMap_moveTemp_step_nil α β pref mapSym state input output)
  | cons b temp ih =>
      let tm := prefixMapMachine α β pref mapSym
      let c₀ := prefixMapCfg α β pref mapSym PrefixMapLabel.moveTemp state input output
        (b :: temp)
      let c₁ := prefixMapCfg α β pref mapSym (PrefixMapLabel.pushOutput b) (some b)
        input output temp
      let c₂ := prefixMapCfg α β pref mapSym PrefixMapLabel.moveTemp (some b) input
        (b :: output) temp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (prefixMap_moveTemp_step_cons α β pref mapSym state input output b temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (prefixMap_pushOutput_step α β pref mapSym (some b) input output b temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (prefixMapCfg α β pref mapSym PrefixMapLabel.writePrefix none input
            (temp.reverse ++ (b :: output)) []))
          (2 * temp.length + 1) :=
        ih (some b) (b :: output)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * temp.length + 1)
          c₀ c₂
          (some (prefixMapCfg α β pref mapSym PrefixMapLabel.writePrefix none input
            (temp.reverse ++ (b :: output)) []))
          h₁₂ hTail

def prefixMap_writePrefix_run (α β : Type) [Fintype α] [Fintype β]
    (pref : β) (mapSym : α → β) (state : Option β) (output : List β) :
    StateTransition.EvalsToInTime (prefixMapMachine α β pref mapSym).step
      (prefixMapCfg α β pref mapSym PrefixMapLabel.writePrefix state [] output [])
      (some (prefixMapHalt α β pref mapSym (pref :: output))) 1 :=
  evalsToInTimeOne (prefixMap_writePrefix_step α β pref mapSym state output)

/--
The prefix-map program computes `input ↦ pref :: input.map mapSym` in linear
TM2 time.
-/
def prefixMap_outputs (α β : Type) [Fintype α] [Fintype β]
    (pref : β) (mapSym : α → β) (input : List α) :
    Turing.TM2OutputsInTime (prefixMapMachine α β pref mapSym)
      input (some (pref :: input.map mapSym)) (4 * input.length + 3) := by
  let tm := prefixMapMachine α β pref mapSym
  let mapped := input.map mapSym
  let mid₁ := prefixMapCfg α β pref mapSym PrefixMapLabel.moveTemp none [] []
    mapped.reverse
  let mid₂ := prefixMapCfg α β pref mapSym PrefixMapLabel.writePrefix none [] mapped []
  let done := prefixMapHalt α β pref mapSym (pref :: mapped)
  have hRead : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some mid₁) (2 * input.length + 1) := by
    simpa [tm, mid₁, mapped, initList_prefixMapMachine] using
      prefixMap_readInput_run α β pref mapSym none input [] []
  have hMove : StateTransition.EvalsToInTime tm.step mid₁
      (some mid₂) (2 * input.length + 1) := by
    simpa [tm, mid₁, mid₂, mapped, List.length_reverse] using
      prefixMap_moveTemp_run α β pref mapSym none [] [] mapped.reverse
  have hWrite : StateTransition.EvalsToInTime tm.step mid₂ (some done) 1 := by
    simpa [tm, mid₂, done, mapped] using
      prefixMap_writePrefix_run α β pref mapSym none mapped
  have hReadMove : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some mid₂) ((2 * input.length + 1) + (2 * input.length + 1)) :=
    StateTransition.EvalsToInTime.trans tm.step (2 * input.length + 1)
      (2 * input.length + 1) (Turing.initList tm input) mid₁ (some mid₂)
      hRead hMove
  have hAll : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some done) (1 + ((2 * input.length + 1) + (2 * input.length + 1))) :=
    StateTransition.EvalsToInTime.trans tm.step
      ((2 * input.length + 1) + (2 * input.length + 1)) 1
      (Turing.initList tm input) mid₂ (some done) hReadMove hWrite
  change StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
    (some (Turing.haltList tm (pref :: mapped))) (4 * input.length + 3)
  rw [haltList_prefixMapMachine]
  convert hAll using 1
  omega

/-- Add a fixed list of output symbols to the output stack in a prefix-map machine. -/
def pushAllPrefixMapOutput {α β : Type} :
    List β →
      Turing.TM2.Stmt (prefixMapAlphabet α β) (PrefixMapLabel β) (Option β) →
      Turing.TM2.Stmt (prefixMapAlphabet α β) (PrefixMapLabel β) (Option β)
  | [], q => q
  | b :: bs, q =>
      push PrefixMapStack.output (fun _ => b) (pushAllPrefixMapOutput bs q)

/--
Executing the nested fixed-prefix statement prepends the fixed prefix to the
current output stack and halts.
-/
lemma stepAux_pushAllPrefixMapOutput {α β : Type} (prefList : List β)
    (state : Option β)
    (stk : (k : PrefixMapStack) → List (prefixMapAlphabet α β k)) :
    Turing.TM2.stepAux (K := PrefixMapStack)
      (pushAllPrefixMapOutput (α := α) (β := β) prefList.reverse
        (load (fun _ : Option β => none) halt))
      state stk =
    { l := none, var := none,
      stk := Function.update stk PrefixMapStack.output (prefList ++ stk PrefixMapStack.output) } := by
  induction prefList using List.reverseRecOn generalizing stk with
  | nil =>
      simp [pushAllPrefixMapOutput]
  | append_singleton xs x ih =>
      simp [pushAllPrefixMapOutput, List.reverse_append, ih, List.append_assoc]

/--
A concrete TM2 program for `input ↦ prefList ++ input.map mapSym`, where `prefList`
is fixed in the machine.
-/
def prefixListMapMachine (α β : Type) [Fintype α] [Fintype β]
    (prefList : List β) (mapSym : α → β) : Turing.FinTM2 where
  K := PrefixMapStack
  k₀ := PrefixMapStack.input
  k₁ := PrefixMapStack.output
  Γ := prefixMapAlphabet α β
  Λ := PrefixMapLabel β
  main := PrefixMapLabel.readInput
  σ := Option β
  initialState := none
  Γk₀Fin := by
    dsimp [prefixMapAlphabet]
    infer_instance
  m
    | PrefixMapLabel.readInput =>
        pop PrefixMapStack.input (fun _ head => head.map mapSym)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some b => PrefixMapLabel.pushTemp b
              | none => PrefixMapLabel.moveTemp)
            (goto fun _ => PrefixMapLabel.moveTemp))
    | PrefixMapLabel.pushTemp b =>
        push PrefixMapStack.temp (fun _ => b) (goto fun _ => PrefixMapLabel.readInput)
    | PrefixMapLabel.moveTemp =>
        pop PrefixMapStack.temp (fun _ head => head)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some b => PrefixMapLabel.pushOutput b
              | none => PrefixMapLabel.writePrefix)
            (goto fun _ => PrefixMapLabel.writePrefix))
    | PrefixMapLabel.pushOutput b =>
        push PrefixMapStack.output (fun _ => b) (goto fun _ => PrefixMapLabel.moveTemp)
    | PrefixMapLabel.writePrefix =>
        pushAllPrefixMapOutput prefList.reverse (load (fun _ => none) halt)

/-- A named configuration for the fixed-prefList map program. -/
def prefixListMapCfg (α β : Type) [Fintype α] [Fintype β]
    (prefList : List β) (mapSym : α → β) (label : PrefixMapLabel β) (state : Option β)
    (input : List α) (output temp : List β) :
    (prefixListMapMachine α β prefList mapSym).Cfg where
  l := some label
  var := state
  stk
    | PrefixMapStack.input => input
    | PrefixMapStack.output => output
    | PrefixMapStack.temp => temp

/-- A named halt configuration for the fixed-prefList map program. -/
def prefixListMapHalt (α β : Type) [Fintype α] [Fintype β]
    (prefList : List β) (mapSym : α → β) (output : List β) :
    (prefixListMapMachine α β prefList mapSym).Cfg where
  l := none
  var := none
  stk
    | PrefixMapStack.input => []
    | PrefixMapStack.output => output
    | PrefixMapStack.temp => []

lemma prefixListMap_readInput_step_cons (α β : Type) [Fintype α] [Fintype β]
    (prefList : List β) (mapSym : α → β) (state : Option β)
    (a : α) (input : List α) (output temp : List β) :
    (prefixListMapMachine α β prefList mapSym).step
        (prefixListMapCfg α β prefList mapSym PrefixMapLabel.readInput state
          (a :: input) output temp) =
      some (prefixListMapCfg α β prefList mapSym (PrefixMapLabel.pushTemp (mapSym a))
        (some (mapSym a)) input output temp) := by
  simp [prefixListMapMachine, prefixListMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma prefixListMap_readInput_step_nil (α β : Type) [Fintype α] [Fintype β]
    (prefList : List β) (mapSym : α → β) (state : Option β) (output temp : List β) :
    (prefixListMapMachine α β prefList mapSym).step
        (prefixListMapCfg α β prefList mapSym PrefixMapLabel.readInput state [] output temp) =
      some (prefixListMapCfg α β prefList mapSym PrefixMapLabel.moveTemp none [] output temp) := by
  simp [prefixListMapMachine, prefixListMapCfg]
  congr

lemma prefixListMap_pushTemp_step (α β : Type) [Fintype α] [Fintype β]
    (prefList : List β) (mapSym : α → β) (state : Option β)
    (b : β) (input : List α) (output temp : List β) :
    (prefixListMapMachine α β prefList mapSym).step
        (prefixListMapCfg α β prefList mapSym (PrefixMapLabel.pushTemp b) state
          input output temp) =
      some (prefixListMapCfg α β prefList mapSym PrefixMapLabel.readInput state input output
        (b :: temp)) := by
  simp [prefixListMapMachine, prefixListMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma prefixListMap_moveTemp_step_cons (α β : Type) [Fintype α] [Fintype β]
    (prefList : List β) (mapSym : α → β) (state : Option β)
    (input : List α) (output : List β) (b : β) (temp : List β) :
    (prefixListMapMachine α β prefList mapSym).step
        (prefixListMapCfg α β prefList mapSym PrefixMapLabel.moveTemp state input output
          (b :: temp)) =
      some (prefixListMapCfg α β prefList mapSym (PrefixMapLabel.pushOutput b) (some b)
        input output temp) := by
  simp [prefixListMapMachine, prefixListMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma prefixListMap_moveTemp_step_nil (α β : Type) [Fintype α] [Fintype β]
    (prefList : List β) (mapSym : α → β) (state : Option β) (input : List α)
    (output : List β) :
    (prefixListMapMachine α β prefList mapSym).step
        (prefixListMapCfg α β prefList mapSym PrefixMapLabel.moveTemp state input output []) =
      some (prefixListMapCfg α β prefList mapSym PrefixMapLabel.writePrefix none input output []) := by
  simp [prefixListMapMachine, prefixListMapCfg]
  congr

lemma prefixListMap_pushOutput_step (α β : Type) [Fintype α] [Fintype β]
    (prefList : List β) (mapSym : α → β) (state : Option β)
    (input : List α) (output : List β) (b : β) (temp : List β) :
    (prefixListMapMachine α β prefList mapSym).step
        (prefixListMapCfg α β prefList mapSym (PrefixMapLabel.pushOutput b) state input output
          temp) =
      some (prefixListMapCfg α β prefList mapSym PrefixMapLabel.moveTemp state input
        (b :: output) temp) := by
  simp [prefixListMapMachine, prefixListMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma prefixListMap_writePrefix_step (α β : Type) [Fintype α] [Fintype β]
    (prefList : List β) (mapSym : α → β) (state : Option β) (output : List β) :
    (prefixListMapMachine α β prefList mapSym).step
        (prefixListMapCfg α β prefList mapSym PrefixMapLabel.writePrefix state [] output []) =
      some (prefixListMapHalt α β prefList mapSym (prefList ++ output)) := by
  simp [prefixListMapMachine, prefixListMapCfg]
  congr
  have hStep :
      Turing.TM2.stepAux
          (pushAllPrefixMapOutput prefList.reverse (load (fun x : Option β => none) halt))
          state
          (fun
            | PrefixMapStack.input => []
            | PrefixMapStack.output => output
            | PrefixMapStack.temp => []) =
        (⟨none, none,
          Function.update
            (fun
              | PrefixMapStack.input => []
              | PrefixMapStack.output => output
              | PrefixMapStack.temp => [])
            PrefixMapStack.output (prefList ++ output)⟩ :
          (prefixListMapMachine α β prefList mapSym).Cfg) := by
    convert
      stepAux_pushAllPrefixMapOutput (α := α) (β := β) prefList state
        (fun
          | PrefixMapStack.input => []
          | PrefixMapStack.output => output
          | PrefixMapStack.temp => []) using 1
    · congr
      funext k
      cases k <;> rfl
  have hCfg :
      (⟨none, none,
        Function.update
          (fun
            | PrefixMapStack.input => []
            | PrefixMapStack.output => output
            | PrefixMapStack.temp => [])
          PrefixMapStack.output (prefList ++ output)⟩ :
        (prefixListMapMachine α β prefList mapSym).Cfg) =
      prefixListMapHalt α β prefList mapSym (prefList ++ output) := by
    dsimp [prefixListMapHalt]
    congr
    funext k
    cases k <;> simp [Function.update]
  convert hStep.trans hCfg using 1
  · congr
    funext k
    cases k <;> rfl

lemma initList_prefixListMapMachine (α β : Type) [Fintype α] [Fintype β]
    (prefList : List β) (mapSym : α → β) (input : List α) :
    Turing.initList (prefixListMapMachine α β prefList mapSym) input =
      prefixListMapCfg α β prefList mapSym PrefixMapLabel.readInput none input [] [] := by
  simp [prefixListMapMachine, prefixListMapCfg, Turing.initList]
  congr
  funext k
  cases k <;> rfl

lemma haltList_prefixListMapMachine (α β : Type) [Fintype α] [Fintype β]
    (prefList : List β) (mapSym : α → β) (output : List β) :
    Turing.haltList (prefixListMapMachine α β prefList mapSym) output =
      prefixListMapHalt α β prefList mapSym output := by
  simp [prefixListMapMachine, prefixListMapHalt, Turing.haltList]
  congr
  funext k
  cases k <;> rfl

end TM2Programs
end ComplexityReduction
