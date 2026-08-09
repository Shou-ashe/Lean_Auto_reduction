/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.ListMap

namespace ComplexityReduction
namespace TM2Programs

open Turing.TM2.Stmt

/--
Stack layout for the arbitrary list-fold runner.  The public output stack is
also the live accumulator stack; during each element step the old accumulator is
consumed to build the supplied product input, then the supplied output is copied
back as the new accumulator.
-/
inductive ListFoldStack (K : Type) where
  | source
  | work (k : K)
  | acc
  | payloadTemp
  | accTemp
  | outputTemp
  deriving DecidableEq, Fintype

/-- Stack alphabets for the arbitrary list-fold runner. -/
abbrev listFoldAlphabet (α β : Type) (tm : Turing.FinTM2) :
    ListFoldStack tm.K → Type
  | ListFoldStack.source => Option α
  | ListFoldStack.work k => tm.Γ k
  | ListFoldStack.acc => β
  | ListFoldStack.payloadTemp => tm.Γ tm.k₀
  | ListFoldStack.accTemp => tm.Γ tm.k₀
  | ListFoldStack.outputTemp => β

/-- Copy/scan state for the arbitrary list-fold runner. -/
inductive ListFoldScanState (γ : Type) where
  | payload (a : γ)
  | delimiter
  | endInput
  deriving DecidableEq, Fintype

namespace ListFoldScanState

def isPayload {γ : Type} : ListFoldScanState γ → Bool
  | payload _ => true
  | _ => false

def isDelimiter {γ : Type} : ListFoldScanState γ → Bool
  | delimiter => true
  | _ => false

end ListFoldScanState

/-- Control labels for the arbitrary list-fold runner. -/
inductive ListFoldLabel (K Λ γ β : Type) where
  | init
  | readSource
  | pushPayloadTemp (a : γ)
  | drainPayload
  | pushPayloadInput (a : γ)
  | pushDelimiter
  | readAcc
  | pushAccTemp (a : γ)
  | drainAcc
  | pushAccInput (a : γ)
  | run (label : Λ)
  | readOutput
  | pushOutputTemp (b : β)
  | drainOutput
  | pushAcc (b : β)
  | reset (remaining : Finset K)
  deriving DecidableEq, Fintype

/-- Phase-indexed finite state for the arbitrary list-fold runner. -/
inductive ListFoldState (σ γ β : Type) where
  | scan (state : ListFoldScanState γ)
  | run (state : σ)
  | output (state : Option β)
  | reset (hadValue : Bool)
  deriving Fintype

def listFoldScanState {σ γ β : Type} :
    ListFoldState σ γ β → ListFoldScanState γ
  | ListFoldState.scan state => state
  | _ => ListFoldScanState.endInput

def listFoldRunState (tm : Turing.FinTM2) {γ β : Type} :
    ListFoldState tm.σ γ β → tm.σ
  | ListFoldState.run state => state
  | _ => tm.initialState

def listFoldOutputState {σ γ β : Type} : ListFoldState σ γ β → Option β
  | ListFoldState.output state => state
  | _ => none

def listFoldResetState {σ γ β : Type} : ListFoldState σ γ β → Bool
  | ListFoldState.reset state => state
  | _ => false

/-- Add a fixed initial accumulator string to the accumulator/output stack. -/
def pushAllListFoldAcc {α β : Type} (tm : Turing.FinTM2) :
    List β →
      Turing.TM2.Stmt (listFoldAlphabet α β tm)
        (ListFoldLabel tm.K tm.Λ (tm.Γ tm.k₀) β)
        (ListFoldState tm.σ (tm.Γ tm.k₀) β) →
      Turing.TM2.Stmt (listFoldAlphabet α β tm)
        (ListFoldLabel tm.K tm.Λ (tm.Γ tm.k₀) β)
        (ListFoldState tm.σ (tm.Γ tm.k₀) β)
  | [], q => q
  | b :: bs, q => push ListFoldStack.acc (fun _ => b) (pushAllListFoldAcc tm bs q)

/--
Executing the nested initial-accumulator writer prepends the fixed accumulator
to the live accumulator/output stack before continuing with `q`.
-/
lemma stepAux_pushAllListFoldAcc {α β : Type} (tm : Turing.FinTM2)
    (initialAcc : List β)
    (q :
      Turing.TM2.Stmt (listFoldAlphabet α β tm)
        (ListFoldLabel tm.K tm.Λ (tm.Γ tm.k₀) β)
        (ListFoldState tm.σ (tm.Γ tm.k₀) β))
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (stk : (k : ListFoldStack tm.K) → List (listFoldAlphabet α β tm k)) :
    Turing.TM2.stepAux (K := ListFoldStack tm.K)
      (pushAllListFoldAcc tm initialAcc.reverse q) state stk =
    Turing.TM2.stepAux q state
      (Function.update stk ListFoldStack.acc (initialAcc ++ stk ListFoldStack.acc)) := by
  induction initialAcc using List.reverseRecOn generalizing stk with
  | nil =>
      simp [pushAllListFoldAcc]
  | append_singleton xs x ih =>
      simp [pushAllListFoldAcc, List.reverse_append, ih, List.append_assoc]

/--
Relabel the supplied step machine into the work-stack block of the list-fold
runner.  A source `halt` transfers control to the output-to-accumulator copy.
-/
def listFoldRunStmt (α β : Type) (tm : Turing.FinTM2) :
    Turing.TM2.Stmt tm.Γ tm.Λ tm.σ →
      Turing.TM2.Stmt (listFoldAlphabet α β tm)
        (ListFoldLabel tm.K tm.Λ (tm.Γ tm.k₀) β)
        (ListFoldState tm.σ (tm.Γ tm.k₀) β)
  | push k f q =>
      push (ListFoldStack.work k) (fun state => f (listFoldRunState tm state))
        (listFoldRunStmt α β tm q)
  | peek k f q =>
      peek (ListFoldStack.work k)
        (fun state head => ListFoldState.run (f (listFoldRunState tm state) head))
        (listFoldRunStmt α β tm q)
  | pop k f q =>
      pop (ListFoldStack.work k)
        (fun state head => ListFoldState.run (f (listFoldRunState tm state) head))
        (listFoldRunStmt α β tm q)
  | load f q =>
      load (fun state => ListFoldState.run (f (listFoldRunState tm state)))
        (listFoldRunStmt α β tm q)
  | branch f qTrue qFalse =>
      branch (fun state => f (listFoldRunState tm state))
        (listFoldRunStmt α β tm qTrue) (listFoldRunStmt α β tm qFalse)
  | goto f =>
      goto fun state => ListFoldLabel.run (f (listFoldRunState tm state))
  | halt =>
      load (fun _ => ListFoldState.output (none : Option β))
        (goto fun _ => ListFoldLabel.readOutput)

noncomputable def listFoldAllWorkStacks (tm : Turing.FinTM2) : Finset tm.K := by
  letI := tm.kDecidableEq
  letI := tm.kFin
  exact Finset.univ

def listFoldEmptyWork (tm : Turing.FinTM2) : (k : tm.K) → List (tm.Γ k) :=
  fun _ => []

/-- The arbitrary list-fold orchestration machine. -/
noncomputable def listFoldMachine (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β] (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β) : Turing.FinTM2 := by
  letI := tm.kDecidableEq
  letI := tm.kFin
  letI := tm.ΛFin
  letI := tm.σFin
  letI := tm.Γk₀Fin
  exact
    { K := ListFoldStack tm.K
      k₀ := ListFoldStack.source
      k₁ := ListFoldStack.acc
      Γ := listFoldAlphabet α β tm
      Λ := ListFoldLabel tm.K tm.Λ (tm.Γ tm.k₀) β
      main := ListFoldLabel.init
      σ := ListFoldState tm.σ (tm.Γ tm.k₀) β
      initialState := ListFoldState.scan ListFoldScanState.endInput
      Γk₀Fin := by
        dsimp [listFoldAlphabet]
        infer_instance
      m := fun
        | ListFoldLabel.init =>
            pushAllListFoldAcc tm initialAcc.reverse
              (goto fun _ => ListFoldLabel.readSource)
        | ListFoldLabel.readSource =>
            pop ListFoldStack.source
              (fun _ head =>
                match head with
                | some (some a) =>
                    ListFoldState.scan
                      (ListFoldScanState.payload (readInput (some (Sum.inr a))))
                | some none => ListFoldState.scan ListFoldScanState.delimiter
                | none => ListFoldState.scan ListFoldScanState.endInput)
              (branch (fun state => (listFoldScanState state).isPayload)
                (goto fun state =>
                  match listFoldScanState state with
                  | ListFoldScanState.payload a => ListFoldLabel.pushPayloadTemp a
                  | _ => ListFoldLabel.drainPayload)
                (branch (fun state => (listFoldScanState state).isDelimiter)
                  (goto fun _ => ListFoldLabel.drainPayload)
                  (load (fun _ => ListFoldState.scan ListFoldScanState.endInput) halt)))
        | ListFoldLabel.pushPayloadTemp a =>
            push ListFoldStack.payloadTemp (fun _ => a)
              (goto fun _ => ListFoldLabel.readSource)
        | ListFoldLabel.drainPayload =>
            pop ListFoldStack.payloadTemp
              (fun _ head =>
                match head with
                | some a => ListFoldState.scan (ListFoldScanState.payload a)
                | none => ListFoldState.scan ListFoldScanState.delimiter)
              (branch (fun state => (listFoldScanState state).isPayload)
                (goto fun state =>
                  match listFoldScanState state with
                  | ListFoldScanState.payload a => ListFoldLabel.pushPayloadInput a
                  | _ => ListFoldLabel.pushDelimiter)
                (goto fun _ => ListFoldLabel.pushDelimiter))
        | ListFoldLabel.pushPayloadInput a =>
            push (ListFoldStack.work tm.k₀) (fun _ => a)
              (goto fun _ => ListFoldLabel.drainPayload)
        | ListFoldLabel.pushDelimiter =>
            push (ListFoldStack.work tm.k₀) (fun _ => readInput none)
              (goto fun _ => ListFoldLabel.readAcc)
        | ListFoldLabel.readAcc =>
            pop ListFoldStack.acc
              (fun _ head =>
                match head with
                | some b =>
                    ListFoldState.scan
                      (ListFoldScanState.payload (readInput (some (Sum.inl b))))
                | none => ListFoldState.scan ListFoldScanState.delimiter)
              (branch (fun state => (listFoldScanState state).isPayload)
                (goto fun state =>
                  match listFoldScanState state with
                  | ListFoldScanState.payload a => ListFoldLabel.pushAccTemp a
                  | _ => ListFoldLabel.drainAcc)
                (goto fun _ => ListFoldLabel.drainAcc))
        | ListFoldLabel.pushAccTemp a =>
            push ListFoldStack.accTemp (fun _ => a)
              (goto fun _ => ListFoldLabel.readAcc)
        | ListFoldLabel.drainAcc =>
            pop ListFoldStack.accTemp
              (fun _ head =>
                match head with
                | some a => ListFoldState.scan (ListFoldScanState.payload a)
                | none => ListFoldState.scan ListFoldScanState.delimiter)
              (branch (fun state => (listFoldScanState state).isPayload)
                (goto fun state =>
                  match listFoldScanState state with
                  | ListFoldScanState.payload a => ListFoldLabel.pushAccInput a
                  | _ => ListFoldLabel.run tm.main)
                (load (fun _ => ListFoldState.run tm.initialState)
                  (goto fun _ => ListFoldLabel.run tm.main)))
        | ListFoldLabel.pushAccInput a =>
            push (ListFoldStack.work tm.k₀) (fun _ => a)
              (goto fun _ => ListFoldLabel.drainAcc)
        | ListFoldLabel.run label =>
            listFoldRunStmt α β tm (tm.m label)
        | ListFoldLabel.readOutput =>
            pop (ListFoldStack.work tm.k₁)
              (fun _ head => ListFoldState.output (head.map writeOutput))
              (branch (fun state => (listFoldOutputState state).isSome)
                (goto fun state =>
                  match listFoldOutputState state with
                  | some b => ListFoldLabel.pushOutputTemp b
                  | none => ListFoldLabel.drainOutput)
                (goto fun _ => ListFoldLabel.drainOutput))
        | ListFoldLabel.pushOutputTemp b =>
            push ListFoldStack.outputTemp (fun _ => b)
              (goto fun _ => ListFoldLabel.readOutput)
        | ListFoldLabel.drainOutput =>
            pop ListFoldStack.outputTemp
              (fun _ head => ListFoldState.output head)
              (branch (fun state => (listFoldOutputState state).isSome)
                (goto fun state =>
                  match listFoldOutputState state with
                  | some b => ListFoldLabel.pushAcc b
                  | none => ListFoldLabel.reset (listFoldAllWorkStacks tm))
                (goto fun _ => ListFoldLabel.reset (listFoldAllWorkStacks tm)))
        | ListFoldLabel.pushAcc b =>
            push ListFoldStack.acc (fun _ => b)
              (goto fun _ => ListFoldLabel.drainOutput)
        | ListFoldLabel.reset remaining =>
            match remaining.toList with
            | [] =>
                load (fun _ => ListFoldState.scan ListFoldScanState.endInput)
                  (goto fun _ => ListFoldLabel.readSource)
            | k :: _ =>
                pop (ListFoldStack.work k)
                  (fun _ head => ListFoldState.reset head.isSome)
                  (branch listFoldResetState
                    (goto fun _ => ListFoldLabel.reset remaining)
                    (goto fun _ => ListFoldLabel.reset (remaining.erase k))) }

def listFoldCfg (α β : Type) (tm : Turing.FinTM2) [Fintype α] [Fintype β]
    (_readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (_writeOutput : tm.Γ tm.k₁ → β) (_initialAcc : List β)
    (label : Option (ListFoldLabel tm.K tm.Λ (tm.Γ tm.k₀) β))
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀))
    (outputTemp : List β) :
    Turing.TM2.Cfg (listFoldAlphabet α β tm)
      (ListFoldLabel tm.K tm.Λ (tm.Γ tm.k₀) β)
      (ListFoldState tm.σ (tm.Γ tm.k₀) β) where
  l := label
  var := state
  stk
    | ListFoldStack.source => source
    | ListFoldStack.work k => work k
    | ListFoldStack.acc => acc
    | ListFoldStack.payloadTemp => payloadTemp
    | ListFoldStack.accTemp => accTemp
    | ListFoldStack.outputTemp => outputTemp

def listFoldRunCfg (α β : Type) (tm : Turing.FinTM2) [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (cfg : tm.Cfg) (source : List (Option α)) (acc : List β)
    (payloadTemp accTemp : List (tm.Γ tm.k₀)) (outputTemp : List β) :
    Turing.TM2.Cfg (listFoldAlphabet α β tm)
      (ListFoldLabel tm.K tm.Λ (tm.Γ tm.k₀) β)
      (ListFoldState tm.σ (tm.Γ tm.k₀) β) :=
  match cfg.l with
  | some label =>
      listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.run label)) (ListFoldState.run cfg.var) source cfg.stk
        acc payloadTemp accTemp outputTemp
  | none =>
      listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readOutput) (ListFoldState.output none) source cfg.stk
        acc payloadTemp accTemp outputTemp

lemma listFoldRunStmt_stepAux (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) (var : tm.σ)
    (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀))
    (outputTemp : List β) :
    Turing.TM2.stepAux (listFoldRunStmt α β tm q) (ListFoldState.run var)
      (fun
        | ListFoldStack.source => source
        | ListFoldStack.work k => work k
        | ListFoldStack.acc => acc
        | ListFoldStack.payloadTemp => payloadTemp
        | ListFoldStack.accTemp => accTemp
        | ListFoldStack.outputTemp => outputTemp) =
      listFoldRunCfg α β tm readInput writeOutput initialAcc
        (Turing.TM2.stepAux q var work) source acc payloadTemp accTemp outputTemp := by
  induction q generalizing var work with
  | push k f q ih =>
      have hUpdate :
          Function.update
              (fun
                | ListFoldStack.source => source
                | ListFoldStack.work k => work k
                | ListFoldStack.acc => acc
                | ListFoldStack.payloadTemp => payloadTemp
                | ListFoldStack.accTemp => accTemp
                | ListFoldStack.outputTemp => outputTemp)
              (ListFoldStack.work k) (f var :: work k) =
            ((fun
              | ListFoldStack.source => source
              | ListFoldStack.work k' => (Function.update work k (f var :: work k)) k'
              | ListFoldStack.acc => acc
              | ListFoldStack.payloadTemp => payloadTemp
              | ListFoldStack.accTemp => accTemp
              | ListFoldStack.outputTemp => outputTemp) :
              (s : ListFoldStack tm.K) → List (listFoldAlphabet α β tm s)) := by
        funext s
        cases s with
        | source => rfl
        | work k' =>
            by_cases hk : k' = k
            · subst k'
              simp [Function.update]
            · simp [Function.update, hk]
        | acc => rfl
        | payloadTemp => rfl
        | accTemp => rfl
        | outputTemp => rfl
      simpa [listFoldRunStmt, listFoldRunState, hUpdate] using
        ih var (Function.update work k (f var :: work k))
  | peek k f q ih =>
      simpa [listFoldRunStmt, listFoldRunState] using
        ih (f var (work k).head?) work
  | pop k f q ih =>
      have hUpdate :
          Function.update
              (fun
                | ListFoldStack.source => source
                | ListFoldStack.work k => work k
                | ListFoldStack.acc => acc
                | ListFoldStack.payloadTemp => payloadTemp
                | ListFoldStack.accTemp => accTemp
                | ListFoldStack.outputTemp => outputTemp)
              (ListFoldStack.work k) (work k).tail =
            ((fun
              | ListFoldStack.source => source
              | ListFoldStack.work k' => (Function.update work k (work k).tail) k'
              | ListFoldStack.acc => acc
              | ListFoldStack.payloadTemp => payloadTemp
              | ListFoldStack.accTemp => accTemp
              | ListFoldStack.outputTemp => outputTemp) :
              (s : ListFoldStack tm.K) → List (listFoldAlphabet α β tm s)) := by
        funext s
        cases s with
        | source => rfl
        | work k' =>
            by_cases hk : k' = k
            · subst k'
              simp [Function.update]
            · simp [Function.update, hk]
        | acc => rfl
        | payloadTemp => rfl
        | accTemp => rfl
        | outputTemp => rfl
      simpa [listFoldRunStmt, listFoldRunState, hUpdate] using
        ih (f var (work k).head?) (Function.update work k (work k).tail)
  | load f q ih =>
      simpa [listFoldRunStmt, listFoldRunState] using ih (f var) work
  | branch f qTrue qFalse ihTrue ihFalse =>
      by_cases hf : f var = true
      · simp [listFoldRunStmt, listFoldRunState, hf, ihTrue, listFoldRunCfg,
          listFoldCfg]
      · simp [listFoldRunStmt, listFoldRunState, hf, ihFalse, listFoldRunCfg,
          listFoldCfg]
  | goto f =>
      simp [listFoldRunStmt, listFoldRunState, listFoldRunCfg, listFoldCfg]
  | halt =>
      simp [listFoldRunStmt, listFoldRunCfg, listFoldCfg]

lemma listFoldMachine_run_step (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    {cfg next : tm.Cfg} (source : List (Option α)) (acc : List β)
    (payloadTemp accTemp : List (tm.Γ tm.k₀)) (outputTemp : List β)
    (hStep : tm.step cfg = some next) :
    (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldRunCfg α β tm readInput writeOutput initialAcc cfg source acc payloadTemp
          accTemp outputTemp) =
      some (listFoldRunCfg α β tm readInput writeOutput initialAcc next source acc
        payloadTemp accTemp outputTemp) := by
  cases cfg with
  | mk label var work =>
      cases label with
      | none =>
          simp [Turing.FinTM2.step, Turing.TM2.step] at hStep
      | some label =>
          have hNext :
              next = Turing.TM2.stepAux (tm.m label) var work := by
            have hSome :
                some (Turing.TM2.stepAux (tm.m label) var work) = some next := by
              simpa [Turing.FinTM2.step, Turing.TM2.step] using hStep
            exact (Option.some.inj hSome).symm
          subst next
          simp [listFoldRunCfg, listFoldCfg, listFoldMachine, Turing.FinTM2.step,
            Turing.TM2.step]
          have hAux :=
            listFoldRunStmt_stepAux α β tm readInput writeOutput initialAcc (tm.m label)
              var source work acc payloadTemp accTemp outputTemp
          congr

noncomputable def listFoldRun_evalsToInTime (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    {cfg next : tm.Cfg} (source : List (Option α)) (acc : List β)
    (payloadTemp accTemp : List (tm.Γ tm.k₀)) (outputTemp : List β) {time : Nat}
    (h : StateTransition.EvalsToInTime tm.step cfg (some next) time) :
    StateTransition.EvalsToInTime
      (listFoldMachine α β tm readInput writeOutput initialAcc).step
      (listFoldRunCfg α β tm readInput writeOutput initialAcc cfg source acc payloadTemp
        accTemp outputTemp)
      (some (listFoldRunCfg α β tm readInput writeOutput initialAcc next source acc
        payloadTemp accTemp outputTemp))
      time := by
  simpa using
    evalsToInTime_map_some
      (fun cfg =>
        listFoldRunCfg α β tm readInput writeOutput initialAcc cfg source acc payloadTemp
          accTemp outputTemp)
      (fun s s' hStep =>
        listFoldMachine_run_step α β tm readInput writeOutput initialAcc source acc
          payloadTemp accTemp outputTemp hStep)
      h

lemma listFold_readSource_step_payload (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (a : α) (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀))
    (outputTemp : List β) :
    (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldCfg α β tm readInput writeOutput initialAcc
          (some ListFoldLabel.readSource) state (some a :: source) work acc
          payloadTemp accTemp outputTemp) =
      some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.pushPayloadTemp (readInput (some (Sum.inr a)))))
        (ListFoldState.scan (ListFoldScanState.payload (readInput (some (Sum.inr a)))))
        source work acc payloadTemp accTemp outputTemp) := by
  simp [listFoldMachine, listFoldCfg, listFoldScanState, ListFoldScanState.isPayload]
  congr
  funext k
  cases k <;> rfl

lemma listFold_readSource_step_delimiter (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀))
    (outputTemp : List β) :
    (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldCfg α β tm readInput writeOutput initialAcc
          (some ListFoldLabel.readSource) state (none :: source) work acc
          payloadTemp accTemp outputTemp) =
      some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.drainPayload)
        (ListFoldState.scan ListFoldScanState.delimiter)
        source work acc payloadTemp accTemp outputTemp) := by
  simp [listFoldMachine, listFoldCfg, listFoldScanState, ListFoldScanState.isPayload,
    ListFoldScanState.isDelimiter]
  congr
  funext k
  cases k <;> rfl

lemma listFold_readSource_step_nil (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀))
    (outputTemp : List β) :
    (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldCfg α β tm readInput writeOutput initialAcc
          (some ListFoldLabel.readSource) state [] work acc payloadTemp accTemp
          outputTemp) =
      some (listFoldCfg α β tm readInput writeOutput initialAcc none
        (ListFoldState.scan ListFoldScanState.endInput)
        [] work acc payloadTemp accTemp outputTemp) := by
  simp [listFoldMachine, listFoldCfg, listFoldScanState, ListFoldScanState.isPayload,
    ListFoldScanState.isDelimiter]

lemma listFold_pushPayloadTemp_step (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (a : tm.Γ tm.k₀) (source : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀))
    (outputTemp : List β) :
    (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldCfg α β tm readInput writeOutput initialAcc
          (some (ListFoldLabel.pushPayloadTemp a)) state source work acc
          payloadTemp accTemp outputTemp) =
      some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readSource) state source work acc
        (a :: payloadTemp) accTemp outputTemp) := by
  simp [listFoldMachine, listFoldCfg]
  congr
  funext k
  cases k <;> rfl

lemma listFold_drainPayload_step_cons (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (a : tm.Γ tm.k₀) (source : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀))
    (outputTemp : List β) :
    (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldCfg α β tm readInput writeOutput initialAcc
          (some ListFoldLabel.drainPayload) state source work acc
          (a :: payloadTemp) accTemp outputTemp) =
      some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.pushPayloadInput a))
        (ListFoldState.scan (ListFoldScanState.payload a))
        source work acc payloadTemp accTemp outputTemp) := by
  simp [listFoldMachine, listFoldCfg, listFoldScanState, ListFoldScanState.isPayload]
  congr
  funext k
  cases k <;> rfl

lemma listFold_drainPayload_step_nil (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (accTemp : List (tm.Γ tm.k₀)) (outputTemp : List β) :
    (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldCfg α β tm readInput writeOutput initialAcc
          (some ListFoldLabel.drainPayload) state source work acc [] accTemp
          outputTemp) =
      some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.pushDelimiter)
        (ListFoldState.scan ListFoldScanState.delimiter)
        source work acc [] accTemp outputTemp) := by
  simp [listFoldMachine, listFoldCfg, listFoldScanState, ListFoldScanState.isPayload]

lemma listFold_pushPayloadInput_step (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (a : tm.Γ tm.k₀) (source : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀))
    (outputTemp : List β) :
    (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldCfg α β tm readInput writeOutput initialAcc
          (some (ListFoldLabel.pushPayloadInput a)) state source work acc
          payloadTemp accTemp outputTemp) =
      some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.drainPayload) state source
        (Function.update work tm.k₀ (a :: work tm.k₀)) acc payloadTemp accTemp
        outputTemp) := by
  simp [listFoldMachine, listFoldCfg]
  congr
  funext stack
  cases stack with
  | source => rfl
  | work k =>
      by_cases hk : k = tm.k₀
      · subst k
        simp [Function.update]
      · simp [Function.update, hk]
  | acc => rfl
  | payloadTemp => rfl
  | accTemp => rfl
  | outputTemp => rfl

lemma listFold_pushDelimiter_step (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀))
    (outputTemp : List β) :
    (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldCfg α β tm readInput writeOutput initialAcc
          (some ListFoldLabel.pushDelimiter) state source work acc payloadTemp
          accTemp outputTemp) =
      some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readAcc) state source
        (Function.update work tm.k₀ (readInput none :: work tm.k₀)) acc
        payloadTemp accTemp outputTemp) := by
  simp [listFoldMachine, listFoldCfg]
  congr
  funext stack
  cases stack with
  | source => rfl
  | work k =>
      by_cases hk : k = tm.k₀
      · subst k
        simp [Function.update]
      · simp [Function.update, hk]
  | acc => rfl
  | payloadTemp => rfl
  | accTemp => rfl
  | outputTemp => rfl

noncomputable def listFold_drainPayload_run (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀))
    (outputTemp : List β) :
    StateTransition.EvalsToInTime (listFoldMachine α β tm readInput writeOutput initialAcc).step
      (listFoldCfg α β tm readInput writeOutput initialAcc (some ListFoldLabel.drainPayload)
        state source work acc payloadTemp accTemp outputTemp)
      (some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.pushDelimiter) (ListFoldState.scan ListFoldScanState.delimiter)
        source (Function.update work tm.k₀ (payloadTemp.reverse ++ work tm.k₀))
        acc [] accTemp outputTemp))
      (2 * payloadTemp.length + 1) := by
  induction payloadTemp generalizing state work with
  | nil =>
      simpa using
        evalsToInTimeOne
          (listFold_drainPayload_step_nil α β tm readInput writeOutput initialAcc state
            source work acc accTemp outputTemp)
  | cons a payloadTemp ih =>
      let workTail := Function.update work tm.k₀ (a :: work tm.k₀)
      let c₀ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.drainPayload) state source work acc (a :: payloadTemp)
        accTemp outputTemp
      let c₁ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.pushPayloadInput a))
        (ListFoldState.scan (ListFoldScanState.payload a))
        source work acc payloadTemp accTemp outputTemp
      let c₂ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.drainPayload)
        (ListFoldState.scan (ListFoldScanState.payload a))
        source workTail acc payloadTemp accTemp outputTemp
      let c₃ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.pushDelimiter) (ListFoldState.scan ListFoldScanState.delimiter)
        source (Function.update work tm.k₀ ((a :: payloadTemp).reverse ++ work tm.k₀))
        acc [] accTemp outputTemp
      have h₁ : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (listFold_drainPayload_step_cons α β tm readInput writeOutput initialAcc state a
            source work acc payloadTemp accTemp outputTemp)
      have h₂ : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (listFold_pushPayloadInput_step α β tm readInput writeOutput initialAcc
            (ListFoldState.scan (ListFoldScanState.payload a)) a source work acc payloadTemp
            accTemp outputTemp)
      have h₁₂ : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans
          (listFoldMachine α β tm readInput writeOutput initialAcc).step 1 1 c₀ c₁
          (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₂ (some c₃)
          (2 * payloadTemp.length + 1) := by
        have hRaw :=
          ih (ListFoldState.scan (ListFoldScanState.payload a)) workTail
        simpa [c₂, c₃, workTail, Function.update, List.reverse_cons, List.append_assoc] using
          hRaw
      have hAll :=
        StateTransition.EvalsToInTime.trans
          (listFoldMachine α β tm readInput writeOutput initialAcc).step (1 + 1)
          (2 * payloadTemp.length + 1) c₀ c₂ (some c₃) h₁₂ hTail
      exact evalsToInTime_mono (by simpa [c₀, c₃] using hAll) (by
        simp
        omega)

noncomputable def listFold_readSourcePayload_runFromTemp (α β : Type)
    (tm : Turing.FinTM2) [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (payload : List α) (sourceRest : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀))
    (outputTemp : List β) :
    StateTransition.EvalsToInTime (listFoldMachine α β tm readInput writeOutput initialAcc).step
      (listFoldCfg α β tm readInput writeOutput initialAcc (some ListFoldLabel.readSource)
        state (payload.map some ++ none :: sourceRest) work acc payloadTemp accTemp
        outputTemp)
      (some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.pushDelimiter) (ListFoldState.scan ListFoldScanState.delimiter)
        sourceRest
        (Function.update work tm.k₀
          (payloadTemp.reverse ++ payload.map (fun a => readInput (some (Sum.inr a))) ++
            work tm.k₀))
        acc [] accTemp outputTemp))
      (4 * payload.length + 2 * payloadTemp.length + 2) := by
  induction payload generalizing state work payloadTemp with
  | nil =>
      let c₀ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readSource) state (none :: sourceRest) work acc payloadTemp
        accTemp outputTemp
      let c₁ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.drainPayload) (ListFoldState.scan ListFoldScanState.delimiter)
        sourceRest work acc payloadTemp accTemp outputTemp
      let c₂ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.pushDelimiter) (ListFoldState.scan ListFoldScanState.delimiter)
        sourceRest (Function.update work tm.k₀ (payloadTemp.reverse ++ work tm.k₀))
        acc [] accTemp outputTemp
      have h₁ : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (listFold_readSource_step_delimiter α β tm readInput writeOutput initialAcc state
            sourceRest work acc payloadTemp accTemp outputTemp)
      have h₂ : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₁ (some c₂)
          (2 * payloadTemp.length + 1) := by
        simpa [c₁, c₂] using
          listFold_drainPayload_run α β tm readInput writeOutput initialAcc
            (ListFoldState.scan ListFoldScanState.delimiter) sourceRest work acc payloadTemp
            accTemp outputTemp
      have hAll :=
        StateTransition.EvalsToInTime.trans
          (listFoldMachine α β tm readInput writeOutput initialAcc).step 1
          (2 * payloadTemp.length + 1) c₀ c₁ (some c₂) h₁ h₂
      exact evalsToInTime_mono (by simpa [c₀, c₁, c₂] using hAll) (by simp)
  | cons a payload ih =>
      let inputSym := readInput (some (Sum.inr a))
      let c₀ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readSource) state ((a :: payload).map some ++ none :: sourceRest)
        work acc payloadTemp accTemp outputTemp
      let c₁ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.pushPayloadTemp inputSym))
        (ListFoldState.scan (ListFoldScanState.payload inputSym))
        (payload.map some ++ none :: sourceRest) work acc payloadTemp accTemp outputTemp
      let c₂ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readSource)
        (ListFoldState.scan (ListFoldScanState.payload inputSym))
        (payload.map some ++ none :: sourceRest) work acc (inputSym :: payloadTemp)
        accTemp outputTemp
      let c₃ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.pushDelimiter) (ListFoldState.scan ListFoldScanState.delimiter)
        sourceRest
        (Function.update work tm.k₀
          (payloadTemp.reverse ++
            (a :: payload).map (fun a => readInput (some (Sum.inr a))) ++ work tm.k₀))
        acc [] accTemp outputTemp
      have h₁ : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₀ (some c₁) 1 := by
        simpa [c₀, c₁, inputSym, List.map_cons] using
          evalsToInTimeOne
            (listFold_readSource_step_payload α β tm readInput writeOutput initialAcc state a
              (payload.map some ++ none :: sourceRest) work acc payloadTemp accTemp outputTemp)
      have h₂ : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (listFold_pushPayloadTemp_step α β tm readInput writeOutput initialAcc
            (ListFoldState.scan (ListFoldScanState.payload inputSym)) inputSym
            (payload.map some ++ none :: sourceRest) work acc payloadTemp accTemp outputTemp)
      have h₁₂ : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans
          (listFoldMachine α β tm readInput writeOutput initialAcc).step 1 1 c₀ c₁
          (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₂ (some c₃)
          (4 * payload.length + 2 * (inputSym :: payloadTemp).length + 2) := by
        have hRaw :=
          ih (ListFoldState.scan (ListFoldScanState.payload inputSym)) work
            (inputSym :: payloadTemp)
        simpa [c₂, c₃, inputSym, List.map_cons, List.reverse_cons, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hRaw
      have hAll :=
        StateTransition.EvalsToInTime.trans
          (listFoldMachine α β tm readInput writeOutput initialAcc).step (1 + 1)
          (4 * payload.length + 2 * (inputSym :: payloadTemp).length + 2)
          c₀ c₂ (some c₃) h₁₂ hTail
      convert hAll using 1
      simp only [List.length_cons]
      omega

noncomputable def listFold_readSourcePayload_run (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (payload : List α) (sourceRest : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (accTemp : List (tm.Γ tm.k₀)) (outputTemp : List β) :
    StateTransition.EvalsToInTime (listFoldMachine α β tm readInput writeOutput initialAcc).step
      (listFoldCfg α β tm readInput writeOutput initialAcc (some ListFoldLabel.readSource)
        (ListFoldState.scan ListFoldScanState.endInput)
        (payload.map some ++ none :: sourceRest) work acc [] accTemp outputTemp)
      (some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.pushDelimiter) (ListFoldState.scan ListFoldScanState.delimiter)
        sourceRest
        (Function.update work tm.k₀
          (payload.map (fun a => readInput (some (Sum.inr a))) ++ work tm.k₀))
        acc [] accTemp outputTemp))
      (4 * payload.length + 2) := by
  simpa using
    listFold_readSourcePayload_runFromTemp α β tm readInput writeOutput initialAcc
      (ListFoldState.scan ListFoldScanState.endInput) payload sourceRest work acc [] accTemp
      outputTemp

end TM2Programs
end ComplexityReduction
