/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.ProductPairing

namespace ComplexityReduction
namespace TM2Programs

open Turing.TM2.Stmt

/--
Alphabet for embedding a TM2 machine into a larger stack space with additional
right-hand work stacks.
-/
abbrev tm2LeftLiftAlphabet {K Extra : Type} (Γ : K → Type) (Δ : Extra → Type) :
    K ⊕ Extra → Type
  | Sum.inl k => Γ k
  | Sum.inr e => Δ e

/-- Relabel every stack reference in a TM2 statement into the left side of a sum. -/
def liftLeftStmt {K Extra Λ σ : Type} {Γ : K → Type} {Δ : Extra → Type} :
    Turing.TM2.Stmt Γ Λ σ → Turing.TM2.Stmt (tm2LeftLiftAlphabet Γ Δ) Λ σ
  | push k f q => push (Sum.inl k) f (liftLeftStmt q)
  | peek k f q => peek (Sum.inl k) f (liftLeftStmt q)
  | pop k f q => pop (Sum.inl k) f (liftLeftStmt q)
  | load f q => load f (liftLeftStmt q)
  | branch f qTrue qFalse => branch f (liftLeftStmt qTrue) (liftLeftStmt qFalse)
  | goto f => goto f
  | halt => halt

/-- Lift an original TM2 configuration while carrying extra stacks unchanged. -/
def liftLeftCfg {K Extra Λ σ : Type} {Γ : K → Type} {Δ : Extra → Type}
    (cfg : Turing.TM2.Cfg Γ Λ σ) (extra : (e : Extra) → List (Δ e)) :
    Turing.TM2.Cfg (tm2LeftLiftAlphabet Γ Δ) Λ σ where
  l := cfg.l
  var := cfg.var
  stk
    | Sum.inl k => cfg.stk k
    | Sum.inr e => extra e

lemma liftLeftStmt_stepAux {K Extra Λ σ : Type} [DecidableEq K] [DecidableEq Extra]
    {Γ : K → Type} {Δ : Extra → Type}
    (q : Turing.TM2.Stmt Γ Λ σ) (v : σ)
    (stk : (k : K) → List (Γ k)) (extra : (e : Extra) → List (Δ e)) :
    Turing.TM2.stepAux (liftLeftStmt (Extra := Extra) (Δ := Δ) q) v
        (fun
          | Sum.inl k => stk k
          | Sum.inr e => extra e) =
      liftLeftCfg (Turing.TM2.stepAux q v stk) extra := by
  induction q generalizing v stk with
  | push k f q ih =>
      have hstk :
          Function.update
              ((fun
                | Sum.inl k' => stk k'
                | Sum.inr e => extra e) :
                (s : K ⊕ Extra) → List (tm2LeftLiftAlphabet Γ Δ s))
              (Sum.inl k) (f v :: stk k) =
            ((fun
              | Sum.inl k' => Function.update stk k (f v :: stk k) k'
              | Sum.inr e => extra e) :
              (s : K ⊕ Extra) → List (tm2LeftLiftAlphabet Γ Δ s)) := by
        funext s
        cases s with
        | inl k' =>
            by_cases hk : k' = k
            · subst k'
              simp [Function.update]
            · simp [Function.update, hk]
        | inr e =>
            simp [Function.update]
      simpa [liftLeftStmt, hstk] using ih v (Function.update stk k (f v :: stk k))
  | peek k f q ih =>
      simpa [liftLeftStmt] using ih (f v (stk k).head?) stk
  | pop k f q ih =>
      have hstk :
          Function.update
              ((fun
                | Sum.inl k' => stk k'
                | Sum.inr e => extra e) :
                (s : K ⊕ Extra) → List (tm2LeftLiftAlphabet Γ Δ s))
              (Sum.inl k) (stk k).tail =
            ((fun
              | Sum.inl k' => Function.update stk k (stk k).tail k'
              | Sum.inr e => extra e) :
              (s : K ⊕ Extra) → List (tm2LeftLiftAlphabet Γ Δ s)) := by
        funext s
        cases s with
        | inl k' =>
            by_cases hk : k' = k
            · subst k'
              simp [Function.update]
            · simp [Function.update, hk]
        | inr e =>
            simp [Function.update]
      simpa [liftLeftStmt, hstk] using
        ih (f v (stk k).head?) (Function.update stk k (stk k).tail)
  | load f q ih =>
      simpa [liftLeftStmt] using ih (f v) stk
  | branch f qTrue qFalse ihTrue ihFalse =>
      by_cases hf : f v
      · simpa [liftLeftStmt, hf] using ihTrue v stk
      · simpa [liftLeftStmt, hf] using ihFalse v stk
  | goto f =>
      rfl
  | halt =>
      rfl

/--
Embed a bundled finite TM2 machine into a larger stack index type, preserving
its input/output stacks on the left side of a sum and leaving extra stacks for
future orchestration.
-/
def liftLeftFinTM2 (tm : Turing.FinTM2) (Extra : Type)
    [DecidableEq Extra] [Fintype Extra] (Δ : Extra → Type) : Turing.FinTM2 := by
  letI := tm.kDecidableEq
  letI := tm.kFin
  letI := tm.ΛFin
  letI := tm.σFin
  exact
    { K := tm.K ⊕ Extra
      k₀ := Sum.inl tm.k₀
      k₁ := Sum.inl tm.k₁
      Γ := tm2LeftLiftAlphabet tm.Γ Δ
      Λ := tm.Λ
      main := tm.main
      σ := tm.σ
      initialState := tm.initialState
      Γk₀Fin := by
        dsimp [tm2LeftLiftAlphabet]
        exact tm.Γk₀Fin
      m := fun label => liftLeftStmt (Extra := Extra) (Δ := Δ) (tm.m label) }

lemma liftLeftFinTM2_step (tm : Turing.FinTM2) (Extra : Type)
    [DecidableEq Extra] [Fintype Extra] (Δ : Extra → Type)
    (cfg : tm.Cfg) (extra : (e : Extra) → List (Δ e)) :
    (liftLeftFinTM2 tm Extra Δ).step (liftLeftCfg cfg extra) =
      Option.map (fun next => liftLeftCfg next extra) (tm.step cfg) := by
  letI := tm.kDecidableEq
  letI := tm.kFin
  cases cfg with
  | mk label var stk =>
      cases label with
      | none =>
          simp [liftLeftFinTM2, liftLeftCfg, Turing.FinTM2.step, Turing.TM2.step]
      | some label =>
          simp [liftLeftFinTM2, liftLeftCfg, Turing.FinTM2.step, Turing.TM2.step]
          exact congrArg some (liftLeftStmt_stepAux (tm.m label) var stk extra)

def liftLeftFinTM2_evalsToInTime (tm : Turing.FinTM2) (Extra : Type)
    [DecidableEq Extra] [Fintype Extra] (Δ : Extra → Type)
    {cfg next : tm.Cfg} (extra : (e : Extra) → List (Δ e)) {time : Nat}
    (h : StateTransition.EvalsToInTime tm.step cfg (some next) time) :
    StateTransition.EvalsToInTime (liftLeftFinTM2 tm Extra Δ).step
      (liftLeftCfg cfg extra) (some (liftLeftCfg next extra)) time := by
  simpa using
    evalsToInTime_map (fun cfg => liftLeftCfg cfg extra)
      (liftLeftFinTM2_step tm Extra Δ · extra) h

/--
Alphabet for embedding a TM2 machine into the right side of a larger stack
space, leaving left-hand stacks for previously run machines or orchestration.
-/
abbrev tm2RightLiftAlphabet {Extra K : Type} (Δ : Extra → Type) (Γ : K → Type) :
    Extra ⊕ K → Type
  | Sum.inl e => Δ e
  | Sum.inr k => Γ k

/-- Relabel every stack reference in a TM2 statement into the right side of a sum. -/
def liftRightStmt {Extra K Λ σ : Type} {Δ : Extra → Type} {Γ : K → Type} :
    Turing.TM2.Stmt Γ Λ σ → Turing.TM2.Stmt (tm2RightLiftAlphabet Δ Γ) Λ σ
  | push k f q => push (Sum.inr k) f (liftRightStmt q)
  | peek k f q => peek (Sum.inr k) f (liftRightStmt q)
  | pop k f q => pop (Sum.inr k) f (liftRightStmt q)
  | load f q => load f (liftRightStmt q)
  | branch f qTrue qFalse => branch f (liftRightStmt qTrue) (liftRightStmt qFalse)
  | goto f => goto f
  | halt => halt

/-- Right-lift an original TM2 configuration while carrying extra stacks unchanged. -/
def liftRightCfg {Extra K Λ σ : Type} {Δ : Extra → Type} {Γ : K → Type}
    (extra : (e : Extra) → List (Δ e)) (cfg : Turing.TM2.Cfg Γ Λ σ) :
    Turing.TM2.Cfg (tm2RightLiftAlphabet Δ Γ) Λ σ where
  l := cfg.l
  var := cfg.var
  stk
    | Sum.inl e => extra e
    | Sum.inr k => cfg.stk k

lemma liftRightStmt_stepAux {Extra K Λ σ : Type} [DecidableEq Extra] [DecidableEq K]
    {Δ : Extra → Type} {Γ : K → Type}
    (q : Turing.TM2.Stmt Γ Λ σ) (v : σ)
    (extra : (e : Extra) → List (Δ e)) (stk : (k : K) → List (Γ k)) :
    Turing.TM2.stepAux (liftRightStmt (Extra := Extra) (Δ := Δ) q) v
        (fun
          | Sum.inl e => extra e
          | Sum.inr k => stk k) =
      liftRightCfg extra (Turing.TM2.stepAux q v stk) := by
  induction q generalizing v stk with
  | push k f q ih =>
      have hstk :
          Function.update
              ((fun
                | Sum.inl e => extra e
                | Sum.inr k' => stk k') :
                (s : Extra ⊕ K) → List (tm2RightLiftAlphabet Δ Γ s))
              (Sum.inr k) (f v :: stk k) =
            ((fun
              | Sum.inl e => extra e
              | Sum.inr k' => Function.update stk k (f v :: stk k) k') :
              (s : Extra ⊕ K) → List (tm2RightLiftAlphabet Δ Γ s)) := by
        funext s
        cases s with
        | inl e =>
            simp [Function.update]
        | inr k' =>
            by_cases hk : k' = k
            · subst k'
              simp [Function.update]
            · simp [Function.update, hk]
      simpa [liftRightStmt, hstk] using ih v (Function.update stk k (f v :: stk k))
  | peek k f q ih =>
      simpa [liftRightStmt] using ih (f v (stk k).head?) stk
  | pop k f q ih =>
      have hstk :
          Function.update
              ((fun
                | Sum.inl e => extra e
                | Sum.inr k' => stk k') :
                (s : Extra ⊕ K) → List (tm2RightLiftAlphabet Δ Γ s))
              (Sum.inr k) (stk k).tail =
            ((fun
              | Sum.inl e => extra e
              | Sum.inr k' => Function.update stk k (stk k).tail k') :
              (s : Extra ⊕ K) → List (tm2RightLiftAlphabet Δ Γ s)) := by
        funext s
        cases s with
        | inl e =>
            simp [Function.update]
        | inr k' =>
            by_cases hk : k' = k
            · subst k'
              simp [Function.update]
            · simp [Function.update, hk]
      simpa [liftRightStmt, hstk] using
        ih (f v (stk k).head?) (Function.update stk k (stk k).tail)
  | load f q ih =>
      simpa [liftRightStmt] using ih (f v) stk
  | branch f qTrue qFalse ihTrue ihFalse =>
      by_cases hf : f v
      · simpa [liftRightStmt, hf] using ihTrue v stk
      · simpa [liftRightStmt, hf] using ihFalse v stk
  | goto f =>
      rfl
  | halt =>
      rfl

/--
Embed a bundled finite TM2 machine into the right side of a larger stack index
type.  This is the symmetric counterpart to `liftLeftFinTM2`.
-/
def liftRightFinTM2 (tm : Turing.FinTM2) (Extra : Type)
    [DecidableEq Extra] [Fintype Extra] (Δ : Extra → Type) : Turing.FinTM2 := by
  letI := tm.kDecidableEq
  letI := tm.kFin
  letI := tm.ΛFin
  letI := tm.σFin
  exact
    { K := Extra ⊕ tm.K
      k₀ := Sum.inr tm.k₀
      k₁ := Sum.inr tm.k₁
      Γ := tm2RightLiftAlphabet Δ tm.Γ
      Λ := tm.Λ
      main := tm.main
      σ := tm.σ
      initialState := tm.initialState
      Γk₀Fin := by
        dsimp [tm2RightLiftAlphabet]
        exact tm.Γk₀Fin
      m := fun label => liftRightStmt (Extra := Extra) (Δ := Δ) (tm.m label) }

lemma liftRightFinTM2_step (tm : Turing.FinTM2) (Extra : Type)
    [DecidableEq Extra] [Fintype Extra] (Δ : Extra → Type)
    (extra : (e : Extra) → List (Δ e)) (cfg : tm.Cfg) :
    (liftRightFinTM2 tm Extra Δ).step (liftRightCfg extra cfg) =
      Option.map (fun next => liftRightCfg extra next) (tm.step cfg) := by
  letI := tm.kDecidableEq
  letI := tm.kFin
  cases cfg with
  | mk label var stk =>
      cases label with
      | none =>
          simp [liftRightFinTM2, liftRightCfg, Turing.FinTM2.step, Turing.TM2.step]
      | some label =>
          simp [liftRightFinTM2, liftRightCfg, Turing.FinTM2.step, Turing.TM2.step]
          exact congrArg some (liftRightStmt_stepAux (tm.m label) var extra stk)

def liftRightFinTM2_evalsToInTime (tm : Turing.FinTM2) (Extra : Type)
    [DecidableEq Extra] [Fintype Extra] (Δ : Extra → Type)
    (extra : (e : Extra) → List (Δ e)) {cfg next : tm.Cfg} {time : Nat}
    (h : StateTransition.EvalsToInTime tm.step cfg (some next) time) :
    StateTransition.EvalsToInTime (liftRightFinTM2 tm Extra Δ).step
      (liftRightCfg extra cfg) (some (liftRightCfg extra next)) time := by
  simpa using
    evalsToInTime_map (fun cfg => liftRightCfg extra cfg)
      (liftRightFinTM2_step tm Extra Δ extra) h

/-- Stack layout for an orchestrating sequential composition machine. -/
inductive SeqCompStack (K₁ K₂ : Type) where
  | left (k : K₁)
  | right (k : K₂)
  | copyTemp
  deriving DecidableEq, Fintype

/-- Stack alphabets for the sequential composition machine. -/
abbrev seqCompAlphabet (tm₁ tm₂ : Turing.FinTM2) :
    SeqCompStack tm₁.K tm₂.K → Type
  | SeqCompStack.left k => tm₁.Γ k
  | SeqCompStack.right k => tm₂.Γ k
  | SeqCompStack.copyTemp => tm₂.Γ tm₂.k₀

/-- Control labels for a two-machine sequential composition runner. -/
inductive SeqCompLabel (Λ₁ Λ₂ β : Type) where
  | first (label : Λ₁)
  | copyRead
  | copyPushTemp (b : β)
  | copyDrain
  | copyPushTarget (b : β)
  | second (label : Λ₂)
  deriving DecidableEq, Fintype

/-- Phase-indexed finite state for the sequential composition runner. -/
inductive SeqCompState (σ₁ σ₂ β : Type) where
  | first (state : σ₁)
  | copy (state : Option β)
  | second (state : σ₂)
  deriving Fintype

def seqCompFirstState (tm₁ tm₂ : Turing.FinTM2) :
    SeqCompState tm₁.σ tm₂.σ (tm₂.Γ tm₂.k₀) → tm₁.σ
  | SeqCompState.first state => state
  | _ => tm₁.initialState

def seqCompCopyState (tm₁ tm₂ : Turing.FinTM2) :
    SeqCompState tm₁.σ tm₂.σ (tm₂.Γ tm₂.k₀) → Option (tm₂.Γ tm₂.k₀)
  | SeqCompState.copy state => state
  | _ => none

def seqCompSecondState (tm₁ tm₂ : Turing.FinTM2) :
    SeqCompState tm₁.σ tm₂.σ (tm₂.Γ tm₂.k₀) → tm₂.σ
  | SeqCompState.second state => state
  | _ => tm₂.initialState

/--
Relabel the first machine into the left stack block.  A source `halt` does not
halt the orchestrating machine; it transfers control to the copy phase.
-/
def seqFirstStmt (tm₁ tm₂ : Turing.FinTM2) :
    Turing.TM2.Stmt tm₁.Γ tm₁.Λ tm₁.σ →
      Turing.TM2.Stmt (seqCompAlphabet tm₁ tm₂)
        (SeqCompLabel tm₁.Λ tm₂.Λ (tm₂.Γ tm₂.k₀))
        (SeqCompState tm₁.σ tm₂.σ (tm₂.Γ tm₂.k₀))
  | push k f q =>
      push (SeqCompStack.left k) (fun state => f (seqCompFirstState tm₁ tm₂ state))
        (seqFirstStmt tm₁ tm₂ q)
  | peek k f q =>
      peek (SeqCompStack.left k)
        (fun state head => SeqCompState.first (f (seqCompFirstState tm₁ tm₂ state) head))
        (seqFirstStmt tm₁ tm₂ q)
  | pop k f q =>
      pop (SeqCompStack.left k)
        (fun state head => SeqCompState.first (f (seqCompFirstState tm₁ tm₂ state) head))
        (seqFirstStmt tm₁ tm₂ q)
  | load f q =>
      load (fun state => SeqCompState.first (f (seqCompFirstState tm₁ tm₂ state)))
        (seqFirstStmt tm₁ tm₂ q)
  | branch f qTrue qFalse =>
      branch (fun state => f (seqCompFirstState tm₁ tm₂ state))
        (seqFirstStmt tm₁ tm₂ qTrue) (seqFirstStmt tm₁ tm₂ qFalse)
  | goto f =>
      goto fun state => SeqCompLabel.first (f (seqCompFirstState tm₁ tm₂ state))
  | halt =>
      load (fun _ => SeqCompState.copy none) (goto fun _ => SeqCompLabel.copyRead)

/--
Relabel the second machine into the right stack block.  A source `halt` becomes
the real halt of the orchestrating machine with the orchestrator's initial
state, matching `Turing.haltList`.
-/
def seqSecondStmt (tm₁ tm₂ : Turing.FinTM2) :
    Turing.TM2.Stmt tm₂.Γ tm₂.Λ tm₂.σ →
      Turing.TM2.Stmt (seqCompAlphabet tm₁ tm₂)
        (SeqCompLabel tm₁.Λ tm₂.Λ (tm₂.Γ tm₂.k₀))
        (SeqCompState tm₁.σ tm₂.σ (tm₂.Γ tm₂.k₀))
  | push k f q =>
      push (SeqCompStack.right k) (fun state => f (seqCompSecondState tm₁ tm₂ state))
        (seqSecondStmt tm₁ tm₂ q)
  | peek k f q =>
      peek (SeqCompStack.right k)
        (fun state head => SeqCompState.second (f (seqCompSecondState tm₁ tm₂ state) head))
        (seqSecondStmt tm₁ tm₂ q)
  | pop k f q =>
      pop (SeqCompStack.right k)
        (fun state head => SeqCompState.second (f (seqCompSecondState tm₁ tm₂ state) head))
        (seqSecondStmt tm₁ tm₂ q)
  | load f q =>
      load (fun state => SeqCompState.second (f (seqCompSecondState tm₁ tm₂ state)))
        (seqSecondStmt tm₁ tm₂ q)
  | branch f qTrue qFalse =>
      branch (fun state => f (seqCompSecondState tm₁ tm₂ state))
        (seqSecondStmt tm₁ tm₂ qTrue) (seqSecondStmt tm₁ tm₂ qFalse)
  | goto f =>
      goto fun state => SeqCompLabel.second (f (seqCompSecondState tm₁ tm₂ state))
  | halt =>
      load (fun _ => SeqCompState.first tm₁.initialState) halt

/--
Orchestrating `FinTM2` for two supplied machines.  It runs the first machine,
copies its output stack through `mapSym` into the second machine's input stack,
then runs the second machine.
-/
def seqCompMachine (tm₁ tm₂ : Turing.FinTM2)
    (mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀) : Turing.FinTM2 := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  letI := tm₁.kFin
  letI := tm₂.kFin
  letI := tm₁.ΛFin
  letI := tm₂.ΛFin
  letI := tm₁.σFin
  letI := tm₂.σFin
  letI := tm₂.Γk₀Fin
  exact
    { K := SeqCompStack tm₁.K tm₂.K
      k₀ := SeqCompStack.left tm₁.k₀
      k₁ := SeqCompStack.right tm₂.k₁
      Γ := seqCompAlphabet tm₁ tm₂
      Λ := SeqCompLabel tm₁.Λ tm₂.Λ (tm₂.Γ tm₂.k₀)
      main := SeqCompLabel.first tm₁.main
      σ := SeqCompState tm₁.σ tm₂.σ (tm₂.Γ tm₂.k₀)
      initialState := SeqCompState.first tm₁.initialState
      Γk₀Fin := by
        dsimp [seqCompAlphabet]
        exact tm₁.Γk₀Fin
      m := fun
        | SeqCompLabel.first label => seqFirstStmt tm₁ tm₂ (tm₁.m label)
        | SeqCompLabel.copyRead =>
            pop (SeqCompStack.left tm₁.k₁)
              (fun _ head => SeqCompState.copy (head.map mapSym))
              (branch (fun state => (seqCompCopyState tm₁ tm₂ state).isSome)
                (goto fun state =>
                  match seqCompCopyState tm₁ tm₂ state with
                  | some b => SeqCompLabel.copyPushTemp b
                  | none => SeqCompLabel.copyDrain)
                (goto fun _ => SeqCompLabel.copyDrain))
        | SeqCompLabel.copyPushTemp b =>
            push SeqCompStack.copyTemp (fun _ => b)
              (goto fun _ => SeqCompLabel.copyRead)
        | SeqCompLabel.copyDrain =>
            pop SeqCompStack.copyTemp (fun _ head => SeqCompState.copy head)
              (branch (fun state => (seqCompCopyState tm₁ tm₂ state).isSome)
                (goto fun state =>
                  match seqCompCopyState tm₁ tm₂ state with
                  | some b => SeqCompLabel.copyPushTarget b
                  | none => SeqCompLabel.copyDrain)
                (load (fun _ => SeqCompState.second tm₂.initialState)
                  (goto fun _ => SeqCompLabel.second tm₂.main)))
        | SeqCompLabel.copyPushTarget b =>
            push (SeqCompStack.right tm₂.k₀) (fun _ => b)
              (goto fun _ => SeqCompLabel.copyDrain)
        | SeqCompLabel.second label => seqSecondStmt tm₁ tm₂ (tm₂.m label) }

/-- A named configuration for the sequential composition machine. -/
def seqCompCfg (tm₁ tm₂ : Turing.FinTM2)
    (_mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (label : Option (SeqCompLabel tm₁.Λ tm₂.Λ (tm₂.Γ tm₂.k₀)))
    (state : SeqCompState tm₁.σ tm₂.σ (tm₂.Γ tm₂.k₀))
    (left : (k : tm₁.K) → List (tm₁.Γ k))
    (right : (k : tm₂.K) → List (tm₂.Γ k))
    (temp : List (tm₂.Γ tm₂.k₀)) :
    Turing.TM2.Cfg (seqCompAlphabet tm₁ tm₂)
      (SeqCompLabel tm₁.Λ tm₂.Λ (tm₂.Γ tm₂.k₀))
      (SeqCompState tm₁.σ tm₂.σ (tm₂.Γ tm₂.k₀)) where
  l := label
  var := state
  stk
    | SeqCompStack.left k => left k
    | SeqCompStack.right k => right k
    | SeqCompStack.copyTemp => temp

/-- Embed a first-machine configuration into the sequential composition machine. -/
def seqFirstCfg (tm₁ tm₂ : Turing.FinTM2)
    (mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (cfg : tm₁.Cfg) (right : (k : tm₂.K) → List (tm₂.Γ k))
    (temp : List (tm₂.Γ tm₂.k₀)) :
    Turing.TM2.Cfg (seqCompAlphabet tm₁ tm₂)
      (SeqCompLabel tm₁.Λ tm₂.Λ (tm₂.Γ tm₂.k₀))
      (SeqCompState tm₁.σ tm₂.σ (tm₂.Γ tm₂.k₀)) :=
  match cfg.l with
  | some label =>
      seqCompCfg tm₁ tm₂ mapSym (some (SeqCompLabel.first label))
        (SeqCompState.first cfg.var) cfg.stk right temp
  | none =>
      seqCompCfg tm₁ tm₂ mapSym (some SeqCompLabel.copyRead)
        (SeqCompState.copy none) cfg.stk right temp

/-- Embed a second-machine configuration into the sequential composition machine. -/
def seqSecondCfg (tm₁ tm₂ : Turing.FinTM2)
    (mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (cfg : tm₂.Cfg) (left : (k : tm₁.K) → List (tm₁.Γ k))
    (temp : List (tm₂.Γ tm₂.k₀)) :
    Turing.TM2.Cfg (seqCompAlphabet tm₁ tm₂)
      (SeqCompLabel tm₁.Λ tm₂.Λ (tm₂.Γ tm₂.k₀))
      (SeqCompState tm₁.σ tm₂.σ (tm₂.Γ tm₂.k₀)) :=
  match cfg.l with
  | some label =>
      seqCompCfg tm₁ tm₂ mapSym (some (SeqCompLabel.second label))
        (SeqCompState.second cfg.var) left cfg.stk temp
  | none =>
      seqCompCfg tm₁ tm₂ mapSym none (SeqCompState.first tm₁.initialState)
        left cfg.stk temp

/-- A named copy-phase configuration exposing source, target, and temporary stacks. -/
def seqCopyCfg (tm₁ tm₂ : Turing.FinTM2)
    (mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (label : SeqCompLabel tm₁.Λ tm₂.Λ (tm₂.Γ tm₂.k₀))
    (state : Option (tm₂.Γ tm₂.k₀))
    (source : List (tm₁.Γ tm₁.k₁)) (target : List (tm₂.Γ tm₂.k₀))
    (left : (k : tm₁.K) → List (tm₁.Γ k))
    (right : (k : tm₂.K) → List (tm₂.Γ k))
    (temp : List (tm₂.Γ tm₂.k₀)) :
    Turing.TM2.Cfg (seqCompAlphabet tm₁ tm₂)
      (SeqCompLabel tm₁.Λ tm₂.Λ (tm₂.Γ tm₂.k₀))
      (SeqCompState tm₁.σ tm₂.σ (tm₂.Γ tm₂.k₀)) := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  exact
    seqCompCfg tm₁ tm₂ mapSym (some label) (SeqCompState.copy state)
      (Function.update left tm₁.k₁ source)
      (Function.update right tm₂.k₀ target)
      temp

lemma seqFirstStmt_stepAux (tm₁ tm₂ : Turing.FinTM2)
    (mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (q : Turing.TM2.Stmt tm₁.Γ tm₁.Λ tm₁.σ) (v : tm₁.σ)
    (left : (k : tm₁.K) → List (tm₁.Γ k))
    (right : (k : tm₂.K) → List (tm₂.Γ k))
    (temp : List (tm₂.Γ tm₂.k₀)) :
    Turing.TM2.stepAux (seqFirstStmt tm₁ tm₂ q) (SeqCompState.first v)
        (fun
          | SeqCompStack.left k => left k
          | SeqCompStack.right k => right k
          | SeqCompStack.copyTemp => temp) =
      seqFirstCfg tm₁ tm₂ mapSym (Turing.TM2.stepAux q v left) right temp := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  induction q generalizing v left with
  | push k f q ih =>
      have hstk :
          Function.update
              ((fun
                | SeqCompStack.left k' => left k'
                | SeqCompStack.right k' => right k'
                | SeqCompStack.copyTemp => temp) :
                (s : SeqCompStack tm₁.K tm₂.K) → List (seqCompAlphabet tm₁ tm₂ s))
              (SeqCompStack.left k) (f v :: left k) =
            ((fun
              | SeqCompStack.left k' => Function.update left k (f v :: left k) k'
              | SeqCompStack.right k' => right k'
              | SeqCompStack.copyTemp => temp) :
              (s : SeqCompStack tm₁.K tm₂.K) → List (seqCompAlphabet tm₁ tm₂ s)) := by
        funext s
        cases s with
        | left k' =>
            by_cases hk : k' = k
            · subst k'
              simp [Function.update]
            · simp [Function.update, hk]
        | right k' =>
            simp [Function.update]
        | copyTemp =>
            simp [Function.update]
      simpa [seqFirstStmt, seqCompFirstState, hstk] using
        ih v (Function.update left k (f v :: left k))
  | peek k f q ih =>
      simpa [seqFirstStmt, seqCompFirstState] using ih (f v (left k).head?) left
  | pop k f q ih =>
      have hstk :
          Function.update
              ((fun
                | SeqCompStack.left k' => left k'
                | SeqCompStack.right k' => right k'
                | SeqCompStack.copyTemp => temp) :
                (s : SeqCompStack tm₁.K tm₂.K) → List (seqCompAlphabet tm₁ tm₂ s))
              (SeqCompStack.left k) (left k).tail =
            ((fun
              | SeqCompStack.left k' => Function.update left k (left k).tail k'
              | SeqCompStack.right k' => right k'
              | SeqCompStack.copyTemp => temp) :
              (s : SeqCompStack tm₁.K tm₂.K) → List (seqCompAlphabet tm₁ tm₂ s)) := by
        funext s
        cases s with
        | left k' =>
            by_cases hk : k' = k
            · subst k'
              simp [Function.update]
            · simp [Function.update, hk]
        | right k' =>
            simp [Function.update]
        | copyTemp =>
            simp [Function.update]
      simpa [seqFirstStmt, seqCompFirstState, hstk] using
        ih (f v (left k).head?) (Function.update left k (left k).tail)
  | load f q ih =>
      simpa [seqFirstStmt, seqCompFirstState] using ih (f v) left
  | branch f qTrue qFalse ihTrue ihFalse =>
      by_cases hf : f v
      · simpa [seqFirstStmt, seqCompFirstState, hf] using ihTrue v left
      · simpa [seqFirstStmt, seqCompFirstState, hf] using ihFalse v left
  | goto f =>
      simp [seqFirstStmt, seqFirstCfg, seqCompCfg, seqCompFirstState]
  | halt =>
      simp [seqFirstStmt, seqFirstCfg, seqCompCfg]

lemma seqSecondStmt_stepAux (tm₁ tm₂ : Turing.FinTM2)
    (mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (q : Turing.TM2.Stmt tm₂.Γ tm₂.Λ tm₂.σ) (v : tm₂.σ)
    (left : (k : tm₁.K) → List (tm₁.Γ k))
    (right : (k : tm₂.K) → List (tm₂.Γ k))
    (temp : List (tm₂.Γ tm₂.k₀)) :
    Turing.TM2.stepAux (seqSecondStmt tm₁ tm₂ q) (SeqCompState.second v)
        (fun
          | SeqCompStack.left k => left k
          | SeqCompStack.right k => right k
          | SeqCompStack.copyTemp => temp) =
      seqSecondCfg tm₁ tm₂ mapSym (Turing.TM2.stepAux q v right) left temp := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  induction q generalizing v right with
  | push k f q ih =>
      have hstk :
          Function.update
              ((fun
                | SeqCompStack.left k' => left k'
                | SeqCompStack.right k' => right k'
                | SeqCompStack.copyTemp => temp) :
                (s : SeqCompStack tm₁.K tm₂.K) → List (seqCompAlphabet tm₁ tm₂ s))
              (SeqCompStack.right k) (f v :: right k) =
            ((fun
              | SeqCompStack.left k' => left k'
              | SeqCompStack.right k' => Function.update right k (f v :: right k) k'
              | SeqCompStack.copyTemp => temp) :
              (s : SeqCompStack tm₁.K tm₂.K) → List (seqCompAlphabet tm₁ tm₂ s)) := by
        funext s
        cases s with
        | left k' =>
            simp [Function.update]
        | right k' =>
            by_cases hk : k' = k
            · subst k'
              simp [Function.update]
            · simp [Function.update, hk]
        | copyTemp =>
            simp [Function.update]
      simpa [seqSecondStmt, seqCompSecondState, hstk] using
        ih v (Function.update right k (f v :: right k))
  | peek k f q ih =>
      simpa [seqSecondStmt, seqCompSecondState] using ih (f v (right k).head?) right
  | pop k f q ih =>
      have hstk :
          Function.update
              ((fun
                | SeqCompStack.left k' => left k'
                | SeqCompStack.right k' => right k'
                | SeqCompStack.copyTemp => temp) :
                (s : SeqCompStack tm₁.K tm₂.K) → List (seqCompAlphabet tm₁ tm₂ s))
              (SeqCompStack.right k) (right k).tail =
            ((fun
              | SeqCompStack.left k' => left k'
              | SeqCompStack.right k' => Function.update right k (right k).tail k'
              | SeqCompStack.copyTemp => temp) :
              (s : SeqCompStack tm₁.K tm₂.K) → List (seqCompAlphabet tm₁ tm₂ s)) := by
        funext s
        cases s with
        | left k' =>
            simp [Function.update]
        | right k' =>
            by_cases hk : k' = k
            · subst k'
              simp [Function.update]
            · simp [Function.update, hk]
        | copyTemp =>
            simp [Function.update]
      simpa [seqSecondStmt, seqCompSecondState, hstk] using
        ih (f v (right k).head?) (Function.update right k (right k).tail)
  | load f q ih =>
      simpa [seqSecondStmt, seqCompSecondState] using ih (f v) right
  | branch f qTrue qFalse ihTrue ihFalse =>
      by_cases hf : f v
      · simpa [seqSecondStmt, seqCompSecondState, hf] using ihTrue v right
      · simpa [seqSecondStmt, seqCompSecondState, hf] using ihFalse v right
  | goto f =>
      simp [seqSecondStmt, seqSecondCfg, seqCompCfg, seqCompSecondState]
  | halt =>
      simp [seqSecondStmt, seqSecondCfg, seqCompCfg]

lemma seqCompMachine_first_step (tm₁ tm₂ : Turing.FinTM2)
    (mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (cfg next : tm₁.Cfg) (right : (k : tm₂.K) → List (tm₂.Γ k))
    (temp : List (tm₂.Γ tm₂.k₀)) (hStep : tm₁.step cfg = some next) :
    (seqCompMachine tm₁ tm₂ mapSym).step (seqFirstCfg tm₁ tm₂ mapSym cfg right temp) =
      some (seqFirstCfg tm₁ tm₂ mapSym next right temp) := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  cases cfg with
  | mk label var stk =>
      cases label with
      | none =>
          simp [Turing.FinTM2.step, Turing.TM2.step] at hStep
      | some label =>
          have hNext :
              next = Turing.TM2.stepAux (tm₁.m label) var stk := by
            have hSome :
                some (Turing.TM2.stepAux (tm₁.m label) var stk) = some next := by
              simpa [Turing.FinTM2.step, Turing.TM2.step] using hStep
            exact (Option.some.inj hSome).symm
          subst next
          change
            (seqCompMachine tm₁ tm₂ mapSym).step
                (seqCompCfg tm₁ tm₂ mapSym (some (SeqCompLabel.first label))
                  (SeqCompState.first var) stk right temp) =
              some
                (seqFirstCfg tm₁ tm₂ mapSym
                  (Turing.TM2.stepAux (tm₁.m label) var stk) right temp)
          simp [seqCompMachine, seqCompCfg, Turing.FinTM2.step, Turing.TM2.step]
          have hAux :=
            seqFirstStmt_stepAux tm₁ tm₂ mapSym (tm₁.m label) var stk right temp
          change
            (some
                (Turing.TM2.stepAux (seqFirstStmt tm₁ tm₂ (tm₁.m label))
                  (SeqCompState.first var)
                  (fun
                    | SeqCompStack.left k => stk k
                    | SeqCompStack.right k => right k
                    | SeqCompStack.copyTemp => temp)) :
              Option
                (Turing.TM2.Cfg (seqCompAlphabet tm₁ tm₂)
                  (SeqCompLabel tm₁.Λ tm₂.Λ (tm₂.Γ tm₂.k₀))
                  (SeqCompState tm₁.σ tm₂.σ (tm₂.Γ tm₂.k₀)))) =
              some
                (seqFirstCfg tm₁ tm₂ mapSym
                  (Turing.TM2.stepAux (tm₁.m label) var stk) right temp)
          exact congrArg some hAux

def seqFirstFinTM2_evalsToInTime (tm₁ tm₂ : Turing.FinTM2)
    (mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    {cfg next : tm₁.Cfg} (right : (k : tm₂.K) → List (tm₂.Γ k))
    (temp : List (tm₂.Γ tm₂.k₀)) {time : Nat}
    (h : StateTransition.EvalsToInTime tm₁.step cfg (some next) time) :
    StateTransition.EvalsToInTime (seqCompMachine tm₁ tm₂ mapSym).step
      (seqFirstCfg tm₁ tm₂ mapSym cfg right temp)
      (some (seqFirstCfg tm₁ tm₂ mapSym next right temp)) time := by
  simpa using
    evalsToInTime_map_some (fun cfg => seqFirstCfg tm₁ tm₂ mapSym cfg right temp)
      (fun s s' hStep => seqCompMachine_first_step tm₁ tm₂ mapSym s s' right temp hStep)
      h

lemma seqCompMachine_second_step (tm₁ tm₂ : Turing.FinTM2)
    (mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (cfg : tm₂.Cfg) (left : (k : tm₁.K) → List (tm₁.Γ k))
    (temp : List (tm₂.Γ tm₂.k₀)) :
    (seqCompMachine tm₁ tm₂ mapSym).step (seqSecondCfg tm₁ tm₂ mapSym cfg left temp) =
      Option.map (fun next => seqSecondCfg tm₁ tm₂ mapSym next left temp) (tm₂.step cfg) := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  cases cfg with
  | mk label var stk =>
      cases label with
      | none =>
          rfl
      | some label =>
          change
            (seqCompMachine tm₁ tm₂ mapSym).step
                (seqCompCfg tm₁ tm₂ mapSym (some (SeqCompLabel.second label))
                  (SeqCompState.second var) left stk temp) =
              some
                (seqSecondCfg tm₁ tm₂ mapSym
                  (Turing.TM2.stepAux (tm₂.m label) var stk) left temp)
          simp [seqCompMachine, seqCompCfg, Turing.FinTM2.step, Turing.TM2.step]
          have hAux :=
            seqSecondStmt_stepAux tm₁ tm₂ mapSym (tm₂.m label) var left stk temp
          change
            (some
                (Turing.TM2.stepAux (seqSecondStmt tm₁ tm₂ (tm₂.m label))
                  (SeqCompState.second var)
                  (fun
                    | SeqCompStack.left k => left k
                    | SeqCompStack.right k => stk k
                    | SeqCompStack.copyTemp => temp)) :
              Option
                (Turing.TM2.Cfg (seqCompAlphabet tm₁ tm₂)
                  (SeqCompLabel tm₁.Λ tm₂.Λ (tm₂.Γ tm₂.k₀))
                  (SeqCompState tm₁.σ tm₂.σ (tm₂.Γ tm₂.k₀)))) =
              some
                (seqSecondCfg tm₁ tm₂ mapSym
                  (Turing.TM2.stepAux (tm₂.m label) var stk) left temp)
          exact congrArg some hAux

def seqSecondFinTM2_evalsToInTime (tm₁ tm₂ : Turing.FinTM2)
    (mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (left : (k : tm₁.K) → List (tm₁.Γ k)) (temp : List (tm₂.Γ tm₂.k₀))
    {cfg next : tm₂.Cfg} {time : Nat}
    (h : StateTransition.EvalsToInTime tm₂.step cfg (some next) time) :
    StateTransition.EvalsToInTime (seqCompMachine tm₁ tm₂ mapSym).step
      (seqSecondCfg tm₁ tm₂ mapSym cfg left temp)
      (some (seqSecondCfg tm₁ tm₂ mapSym next left temp)) time := by
  simpa using
    evalsToInTime_map (fun cfg => seqSecondCfg tm₁ tm₂ mapSym cfg left temp)
      (seqCompMachine_second_step tm₁ tm₂ mapSym · left temp) h

lemma seqCopy_read_step_cons (tm₁ tm₂ : Turing.FinTM2)
    (mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (state : Option (tm₂.Γ tm₂.k₀)) (a : tm₁.Γ tm₁.k₁)
    (source : List (tm₁.Γ tm₁.k₁)) (target : List (tm₂.Γ tm₂.k₀))
    (left : (k : tm₁.K) → List (tm₁.Γ k))
    (right : (k : tm₂.K) → List (tm₂.Γ k))
    (temp : List (tm₂.Γ tm₂.k₀)) :
    (seqCompMachine tm₁ tm₂ mapSym).step
        (seqCopyCfg tm₁ tm₂ mapSym SeqCompLabel.copyRead state
          (a :: source) target left right temp) =
      some
        (seqCopyCfg tm₁ tm₂ mapSym (SeqCompLabel.copyPushTemp (mapSym a))
          (some (mapSym a)) source target left right temp) := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  simp [seqCompMachine, seqCopyCfg, seqCompCfg, Function.update, seqCompCopyState]
  congr
  funext x
  cases x with
  | left k =>
      by_cases hk : k = tm₁.k₁
      · subst k
        simp [Function.update]
      · simp [Function.update, hk]
  | right k =>
      by_cases hk : k = tm₂.k₀
      · subst k
        simp [Function.update]
      · simp [Function.update, hk]
  | copyTemp =>
      simp [Function.update]

lemma seqCopy_read_step_nil (tm₁ tm₂ : Turing.FinTM2)
    (mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (state : Option (tm₂.Γ tm₂.k₀)) (target : List (tm₂.Γ tm₂.k₀))
    (left : (k : tm₁.K) → List (tm₁.Γ k))
    (right : (k : tm₂.K) → List (tm₂.Γ k))
    (temp : List (tm₂.Γ tm₂.k₀)) :
    (seqCompMachine tm₁ tm₂ mapSym).step
        (seqCopyCfg tm₁ tm₂ mapSym SeqCompLabel.copyRead state
          [] target left right temp) =
      some
        (seqCopyCfg tm₁ tm₂ mapSym SeqCompLabel.copyDrain none
          [] target left right temp) := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  simp [seqCompMachine, seqCopyCfg, seqCompCfg, Function.update, seqCompCopyState]
  congr
  funext x
  cases x with
  | left k =>
      by_cases hk : k = tm₁.k₁
      · subst k
        simp [Function.update]
      · simp [Function.update, hk]
  | right k =>
      by_cases hk : k = tm₂.k₀
      · subst k
        simp [Function.update]
      · simp [Function.update, hk]
  | copyTemp =>
      simp [Function.update]

end TM2Programs
end ComplexityReduction
