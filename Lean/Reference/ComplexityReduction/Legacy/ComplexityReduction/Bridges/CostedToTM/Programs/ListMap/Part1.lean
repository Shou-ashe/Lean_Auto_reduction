/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.ProductAndListPrimitives

namespace ComplexityReduction
namespace TM2Programs

open Turing.TM2.Stmt

/-!
The next arbitrary `list_map_map` runner needs a reusable block-copy phase:
read one delimiter-terminated source element block, reverse it through a temp
stack, then drain it into the supplied element machine's input stack in the
original order while leaving the unread list suffix on the source stack.
-/

inductive ListBlockCopyStack where
  | source
  | target
  | temp
  deriving DecidableEq, Fintype

abbrev listBlockCopyAlphabet (α : Type) : ListBlockCopyStack → Type
  | ListBlockCopyStack.source => Option α
  | ListBlockCopyStack.target => α
  | ListBlockCopyStack.temp => α

inductive ListBlockCopyLabel (α : Type) where
  | readSource
  | pushTemp (a : α)
  | drainTemp
  | pushTarget (a : α)
  deriving DecidableEq, Fintype

def listBlockCopyMachine (α : Type) [Fintype α] : Turing.FinTM2 where
  K := ListBlockCopyStack
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := ListBlockCopyStack.source
  k₁ := ListBlockCopyStack.target
  Γ := listBlockCopyAlphabet α
  Λ := ListBlockCopyLabel α
  main := ListBlockCopyLabel.readSource
  σ := Option α
  initialState := none
  σFin := inferInstance
  Γk₀Fin := by
    dsimp [listBlockCopyAlphabet]
    infer_instance
  m
    | ListBlockCopyLabel.readSource =>
        pop ListBlockCopyStack.source
          (fun _ head =>
            match head with
            | some (some a) => some a
            | _ => none)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some a => ListBlockCopyLabel.pushTemp a
              | none => ListBlockCopyLabel.drainTemp)
            (goto fun _ => ListBlockCopyLabel.drainTemp))
    | ListBlockCopyLabel.pushTemp a =>
        push ListBlockCopyStack.temp (fun _ => a)
          (goto fun _ => ListBlockCopyLabel.readSource)
    | ListBlockCopyLabel.drainTemp =>
        pop ListBlockCopyStack.temp (fun _ head => head)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some a => ListBlockCopyLabel.pushTarget a
              | none => ListBlockCopyLabel.drainTemp)
            (load (fun _ => none) halt))
    | ListBlockCopyLabel.pushTarget a =>
        push ListBlockCopyStack.target (fun _ => a)
          (goto fun _ => ListBlockCopyLabel.drainTemp)

def listBlockCopyCfg (α : Type) [Fintype α]
    (label : Option (ListBlockCopyLabel α)) (state : Option α)
    (source : List (Option α)) (target temp : List α) :
    (listBlockCopyMachine α).Cfg where
  l := label
  var := state
  stk
    | ListBlockCopyStack.source => source
    | ListBlockCopyStack.target => target
    | ListBlockCopyStack.temp => temp

def listBlockCopyHalt (α : Type) [Fintype α]
    (source : List (Option α)) (target : List α) :
    (listBlockCopyMachine α).Cfg :=
  listBlockCopyCfg α none none source target []

lemma listBlockCopy_readSource_step_payload (α : Type) [Fintype α]
    (state : Option α) (a : α) (source : List (Option α)) (target temp : List α) :
    (listBlockCopyMachine α).step
        (listBlockCopyCfg α (some ListBlockCopyLabel.readSource) state
          (some a :: source) target temp) =
      some (listBlockCopyCfg α (some (ListBlockCopyLabel.pushTemp a)) (some a)
        source target temp) := by
  simp [listBlockCopyMachine, listBlockCopyCfg]
  congr
  funext k
  cases k <;> rfl

lemma listBlockCopy_readSource_step_delimiter (α : Type) [Fintype α]
    (state : Option α) (source : List (Option α)) (target temp : List α) :
    (listBlockCopyMachine α).step
        (listBlockCopyCfg α (some ListBlockCopyLabel.readSource) state
          (none :: source) target temp) =
      some (listBlockCopyCfg α (some ListBlockCopyLabel.drainTemp) none
        source target temp) := by
  simp [listBlockCopyMachine, listBlockCopyCfg]
  congr
  funext k
  cases k <;> rfl

lemma listBlockCopy_readSource_step_nil (α : Type) [Fintype α]
    (state : Option α) (target temp : List α) :
    (listBlockCopyMachine α).step
        (listBlockCopyCfg α (some ListBlockCopyLabel.readSource) state [] target temp) =
      some (listBlockCopyCfg α (some ListBlockCopyLabel.drainTemp) none
        [] target temp) := by
  simp [listBlockCopyMachine, listBlockCopyCfg]
  congr

lemma listBlockCopy_pushTemp_step (α : Type) [Fintype α]
    (state : Option α) (a : α) (source : List (Option α)) (target temp : List α) :
    (listBlockCopyMachine α).step
        (listBlockCopyCfg α (some (ListBlockCopyLabel.pushTemp a)) state
          source target temp) =
      some (listBlockCopyCfg α (some ListBlockCopyLabel.readSource) state
        source target (a :: temp)) := by
  simp [listBlockCopyMachine, listBlockCopyCfg]
  congr
  funext k
  cases k <;> rfl

lemma listBlockCopy_drainTemp_step_cons (α : Type) [Fintype α]
    (state : Option α) (source : List (Option α)) (target : List α)
    (a : α) (temp : List α) :
    (listBlockCopyMachine α).step
        (listBlockCopyCfg α (some ListBlockCopyLabel.drainTemp) state
          source target (a :: temp)) =
      some (listBlockCopyCfg α (some (ListBlockCopyLabel.pushTarget a)) (some a)
        source target temp) := by
  simp [listBlockCopyMachine, listBlockCopyCfg]
  congr
  funext k
  cases k <;> rfl

lemma listBlockCopy_drainTemp_step_nil (α : Type) [Fintype α]
    (state : Option α) (source : List (Option α)) (target : List α) :
    (listBlockCopyMachine α).step
        (listBlockCopyCfg α (some ListBlockCopyLabel.drainTemp) state
          source target []) =
      some (listBlockCopyHalt α source target) := by
  simp [listBlockCopyMachine, listBlockCopyCfg, listBlockCopyHalt]
  congr

lemma listBlockCopy_pushTarget_step (α : Type) [Fintype α]
    (state : Option α) (source : List (Option α)) (target : List α)
    (a : α) (temp : List α) :
    (listBlockCopyMachine α).step
        (listBlockCopyCfg α (some (ListBlockCopyLabel.pushTarget a)) state
          source target temp) =
      some (listBlockCopyCfg α (some ListBlockCopyLabel.drainTemp) state
        source (a :: target) temp) := by
  simp [listBlockCopyMachine, listBlockCopyCfg]
  congr
  funext k
  cases k <;> rfl

def listBlockCopy_readPayload_run (α : Type) [Fintype α]
    (payload : List α) (rest : List (Option α)) (state : Option α)
    (target temp : List α) :
    StateTransition.EvalsToInTime (listBlockCopyMachine α).step
      (listBlockCopyCfg α (some ListBlockCopyLabel.readSource) state
        (payload.map some ++ none :: rest) target temp)
      (some (listBlockCopyCfg α (some ListBlockCopyLabel.drainTemp) none
        rest target (payload.reverse ++ temp)))
      (2 * payload.length + 1) := by
  induction payload generalizing state temp with
  | nil =>
      simpa using
        evalsToInTimeOne
          (listBlockCopy_readSource_step_delimiter α state rest target temp)
  | cons a payload ih =>
      let tm := listBlockCopyMachine α
      let c₀ := listBlockCopyCfg α (some ListBlockCopyLabel.readSource) state
        (some a :: (payload.map some ++ none :: rest)) target temp
      let c₁ := listBlockCopyCfg α (some (ListBlockCopyLabel.pushTemp a)) (some a)
        (payload.map some ++ none :: rest) target temp
      let c₂ := listBlockCopyCfg α (some ListBlockCopyLabel.readSource) (some a)
        (payload.map some ++ none :: rest) target (a :: temp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (listBlockCopy_readSource_step_payload α state a
            (payload.map some ++ none :: rest) target temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (listBlockCopy_pushTemp_step α (some a) a
            (payload.map some ++ none :: rest) target temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (listBlockCopyCfg α (some ListBlockCopyLabel.drainTemp) none
            rest target (payload.reverse ++ (a :: temp))))
          (2 * payload.length + 1) :=
        ih (some a) (a :: temp)
      have hCombined :=
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * payload.length + 1)
          c₀ c₂
          (some (listBlockCopyCfg α (some ListBlockCopyLabel.drainTemp) none
            rest target (payload.reverse ++ (a :: temp))))
          h₁₂ hTail
      simpa [tm, List.reverse_cons, List.append_assoc] using hCombined

def listBlockCopy_drainTemp_run (α : Type) [Fintype α]
    (state : Option α) (source : List (Option α)) (target temp : List α) :
    StateTransition.EvalsToInTime (listBlockCopyMachine α).step
      (listBlockCopyCfg α (some ListBlockCopyLabel.drainTemp) state source target temp)
      (some (listBlockCopyHalt α source (temp.reverse ++ target)))
      (2 * temp.length + 1) := by
  induction temp generalizing state target with
  | nil =>
      simpa using
        evalsToInTimeOne (listBlockCopy_drainTemp_step_nil α state source target)
  | cons a temp ih =>
      let tm := listBlockCopyMachine α
      let c₀ := listBlockCopyCfg α (some ListBlockCopyLabel.drainTemp) state
        source target (a :: temp)
      let c₁ := listBlockCopyCfg α (some (ListBlockCopyLabel.pushTarget a)) (some a)
        source target temp
      let c₂ := listBlockCopyCfg α (some ListBlockCopyLabel.drainTemp) (some a)
        source (a :: target) temp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (listBlockCopy_drainTemp_step_cons α state source target a temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (listBlockCopy_pushTarget_step α (some a) source target a temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (listBlockCopyHalt α source (temp.reverse ++ (a :: target))))
          (2 * temp.length + 1) :=
        ih (some a) (a :: target)
      have hCombined :=
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * temp.length + 1)
          c₀ c₂ (some (listBlockCopyHalt α source (temp.reverse ++ (a :: target))))
          h₁₂ hTail
      simpa [tm, List.reverse_cons, List.append_assoc] using hCombined

def listBlockCopy_run (α : Type) [Fintype α]
    (payload : List α) (rest : List (Option α)) (target : List α) :
    StateTransition.EvalsToInTime (listBlockCopyMachine α).step
      (listBlockCopyCfg α (some ListBlockCopyLabel.readSource) none
        (payload.map some ++ none :: rest) target [])
      (some (listBlockCopyHalt α rest (payload ++ target)))
      (4 * payload.length + 2) := by
  let tm := listBlockCopyMachine α
  let mid := listBlockCopyCfg α (some ListBlockCopyLabel.drainTemp) none
    rest target payload.reverse
  have hRead : StateTransition.EvalsToInTime tm.step
      (listBlockCopyCfg α (some ListBlockCopyLabel.readSource) none
        (payload.map some ++ none :: rest) target [])
      (some mid) (2 * payload.length + 1) := by
    simpa [tm, mid] using
      listBlockCopy_readPayload_run α payload rest none target []
  have hDrain : StateTransition.EvalsToInTime tm.step mid
      (some (listBlockCopyHalt α rest (payload ++ target)))
      (2 * payload.length + 1) := by
    have hRaw :=
      listBlockCopy_drainTemp_run α none rest target payload.reverse
    simpa [tm, mid, List.length_reverse] using hRaw
  have hAll : StateTransition.EvalsToInTime tm.step
      (listBlockCopyCfg α (some ListBlockCopyLabel.readSource) none
        (payload.map some ++ none :: rest) target [])
      (some (listBlockCopyHalt α rest (payload ++ target)))
      ((2 * payload.length + 1) + (2 * payload.length + 1)) :=
    StateTransition.EvalsToInTime.trans tm.step (2 * payload.length + 1)
      (2 * payload.length + 1)
      (listBlockCopyCfg α (some ListBlockCopyLabel.readSource) none
        (payload.map some ++ none :: rest) target [])
      mid (some (listBlockCopyHalt α rest (payload ++ target))) hRead hDrain
  convert hAll using 1
  omega

inductive ListBlockOutputStack where
  | source
  | target
  deriving DecidableEq, Fintype

abbrev listBlockOutputAlphabet (β : Type) : ListBlockOutputStack → Type
  | ListBlockOutputStack.source => β
  | ListBlockOutputStack.target => Option β

inductive ListBlockOutputLabel (β : Type) where
  | readSource
  | pushPayload (b : β)
  | pushDelimiter
  deriving DecidableEq, Fintype

def listBlockOutputMachine (β : Type) [Fintype β] : Turing.FinTM2 where
  K := ListBlockOutputStack
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := ListBlockOutputStack.source
  k₁ := ListBlockOutputStack.target
  Γ := listBlockOutputAlphabet β
  Λ := ListBlockOutputLabel β
  main := ListBlockOutputLabel.readSource
  σ := Option β
  initialState := none
  σFin := inferInstance
  Γk₀Fin := by
    dsimp [listBlockOutputAlphabet]
    infer_instance
  m
    | ListBlockOutputLabel.readSource =>
        pop ListBlockOutputStack.source (fun _ head => head)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some b => ListBlockOutputLabel.pushPayload b
              | none => ListBlockOutputLabel.pushDelimiter)
            (goto fun _ => ListBlockOutputLabel.pushDelimiter))
    | ListBlockOutputLabel.pushPayload b =>
        push ListBlockOutputStack.target (fun _ => some b)
          (goto fun _ => ListBlockOutputLabel.readSource)
    | ListBlockOutputLabel.pushDelimiter =>
        push ListBlockOutputStack.target (fun _ => none)
          (load (fun _ => none) halt)

def listBlockOutputCfg (β : Type) [Fintype β]
    (label : Option (ListBlockOutputLabel β)) (state : Option β)
    (source : List β) (target : List (Option β)) :
    (listBlockOutputMachine β).Cfg where
  l := label
  var := state
  stk
    | ListBlockOutputStack.source => source
    | ListBlockOutputStack.target => target

def listBlockOutputHalt (β : Type) [Fintype β] (target : List (Option β)) :
    (listBlockOutputMachine β).Cfg :=
  listBlockOutputCfg β none none [] target

lemma listBlockOutput_readSource_step_cons (β : Type) [Fintype β]
    (state : Option β) (b : β) (source : List β) (target : List (Option β)) :
    (listBlockOutputMachine β).step
        (listBlockOutputCfg β (some ListBlockOutputLabel.readSource) state
          (b :: source) target) =
      some (listBlockOutputCfg β (some (ListBlockOutputLabel.pushPayload b)) (some b)
        source target) := by
  simp [listBlockOutputMachine, listBlockOutputCfg]
  congr
  funext k
  cases k <;> rfl

lemma listBlockOutput_readSource_step_nil (β : Type) [Fintype β]
    (state : Option β) (target : List (Option β)) :
    (listBlockOutputMachine β).step
        (listBlockOutputCfg β (some ListBlockOutputLabel.readSource) state [] target) =
      some (listBlockOutputCfg β (some ListBlockOutputLabel.pushDelimiter) none [] target) := by
  simp [listBlockOutputMachine, listBlockOutputCfg]
  congr

lemma listBlockOutput_pushPayload_step (β : Type) [Fintype β]
    (state : Option β) (b : β) (source : List β) (target : List (Option β)) :
    (listBlockOutputMachine β).step
        (listBlockOutputCfg β (some (ListBlockOutputLabel.pushPayload b)) state
          source target) =
      some (listBlockOutputCfg β (some ListBlockOutputLabel.readSource) state
        source (some b :: target)) := by
  simp [listBlockOutputMachine, listBlockOutputCfg]
  congr
  funext k
  cases k <;> rfl

lemma listBlockOutput_pushDelimiter_step (β : Type) [Fintype β]
    (state : Option β) (target : List (Option β)) :
    (listBlockOutputMachine β).step
        (listBlockOutputCfg β (some ListBlockOutputLabel.pushDelimiter) state [] target) =
      some (listBlockOutputHalt β (none :: target)) := by
  simp [listBlockOutputMachine, listBlockOutputCfg, listBlockOutputHalt]
  congr
  funext k
  cases k <;> rfl

def listBlockOutput_runFromState (β : Type) [Fintype β]
    (source : List β) (target : List (Option β)) (state : Option β) :
    StateTransition.EvalsToInTime (listBlockOutputMachine β).step
      (listBlockOutputCfg β (some ListBlockOutputLabel.readSource) state source target)
      (some (listBlockOutputHalt β (none :: (source.map some).reverse ++ target)))
      (2 * source.length + 2) := by
  induction source generalizing target state with
  | nil =>
      let tm := listBlockOutputMachine β
      let c₀ := listBlockOutputCfg β (some ListBlockOutputLabel.readSource) state [] target
      let c₁ := listBlockOutputCfg β (some ListBlockOutputLabel.pushDelimiter) none [] target
      let done := listBlockOutputHalt β (none :: target)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne (listBlockOutput_readSource_step_nil β state target)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some done) 1 :=
        evalsToInTimeOne (listBlockOutput_pushDelimiter_step β none target)
      have hAll : StateTransition.EvalsToInTime tm.step c₀ (some done) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some done) h₁ h₂
      simpa [tm, c₀, c₁, done] using hAll
  | cons b source ih =>
      let tm := listBlockOutputMachine β
      let c₀ := listBlockOutputCfg β (some ListBlockOutputLabel.readSource) state
        (b :: source) target
      let c₁ := listBlockOutputCfg β (some (ListBlockOutputLabel.pushPayload b)) (some b)
        source target
      let c₂ := listBlockOutputCfg β (some ListBlockOutputLabel.readSource) (some b)
        source (some b :: target)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (listBlockOutput_readSource_step_cons β state b source target)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (listBlockOutput_pushPayload_step β (some b) b source target)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (listBlockOutputHalt β
            (none :: (source.map some).reverse ++ some b :: target)))
          (2 * source.length + 2) :=
        ih (some b :: target) (some b)
      have hCombined :=
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * source.length + 2)
          c₀ c₂
          (some (listBlockOutputHalt β
            (none :: (source.map some).reverse ++ some b :: target)))
          h₁₂ hTail
      simpa [tm, List.map_cons, List.reverse_cons, List.append_assoc] using hCombined

def listBlockOutput_run (β : Type) [Fintype β]
    (source : List β) (target : List (Option β)) :
    StateTransition.EvalsToInTime (listBlockOutputMachine β).step
      (listBlockOutputCfg β (some ListBlockOutputLabel.readSource) none source target)
      (some (listBlockOutputHalt β (none :: (source.map some).reverse ++ target)))
      (2 * source.length + 2) :=
  listBlockOutput_runFromState β source target none

/--
Stack layout for the arbitrary list-map runner.  The runner scans a source
encoded list over `Option α`, copies one delimiter-terminated block into the
supplied element machine, writes the element output into a reverse accumulator,
and finally reverses the accumulator to the public output stack.
-/
inductive ListMapStack (K : Type) where
  | source
  | work (k : K)
  | acc
  | output
  | blockTemp
  deriving DecidableEq, Fintype

/-- Stack alphabets for the arbitrary list-map runner. -/
abbrev listMapAlphabet (α β : Type) (tm : Turing.FinTM2) :
    ListMapStack tm.K → Type
  | ListMapStack.source => Option α
  | ListMapStack.work k => tm.Γ k
  | ListMapStack.acc => Option β
  | ListMapStack.output => Option β
  | ListMapStack.blockTemp => tm.Γ tm.k₀

/-- Copy-phase state for the arbitrary list-map runner. -/
inductive ListMapCopyState (α : Type) where
  | payload (a : α)
  | delimiter
  | endInput
  deriving DecidableEq, Fintype

namespace ListMapCopyState

def isPayload {α : Type} : ListMapCopyState α → Bool
  | payload _ => true
  | _ => false

def isDelimiter {α : Type} : ListMapCopyState α → Bool
  | delimiter => true
  | _ => false

end ListMapCopyState

/-- Control labels for the arbitrary list-map runner. -/
inductive ListMapLabel (K Λ α β : Type) where
  | readSource
  | pushBlockTemp (a : α)
  | drainBlockTemp
  | pushWorkInput (a : α)
  | run (label : Λ)
  | writeOutput
  | pushAccPayload (b : β)
  | pushAccDelimiter
  | reset (remaining : Finset K)
  | finalDrain
  | pushFinal (b : Option β)
  deriving DecidableEq, Fintype

/-- Phase-indexed finite state for the arbitrary list-map runner. -/
inductive ListMapState (σ α β : Type) where
  | copy (state : ListMapCopyState α)
  | run (state : σ)
  | write (state : Option β)
  | reset (hadValue : Bool)
  | final (state : Option (Option β))
  deriving Fintype

def listMapCopyState {σ α β : Type} :
    ListMapState σ α β → ListMapCopyState α
  | ListMapState.copy state => state
  | _ => ListMapCopyState.endInput

def listMapRunState (tm : Turing.FinTM2) {α β : Type} :
    ListMapState tm.σ α β → tm.σ
  | ListMapState.run state => state
  | _ => tm.initialState

def listMapWriteState {σ α β : Type} : ListMapState σ α β → Option β
  | ListMapState.write state => state
  | _ => none

def listMapResetState {σ α β : Type} : ListMapState σ α β → Bool
  | ListMapState.reset state => state
  | _ => false

def listMapFinalState {σ α β : Type} : ListMapState σ α β → Option (Option β)
  | ListMapState.final state => state
  | _ => none

/--
Relabel the supplied element machine into the work-stack block of the list-map
runner.  A source `halt` transfers control to the output-block writer rather
than halting the whole runner.
-/
def listMapRunStmt (α β : Type) (tm : Turing.FinTM2) :
    Turing.TM2.Stmt tm.Γ tm.Λ tm.σ →
      Turing.TM2.Stmt (listMapAlphabet α β tm)
        (ListMapLabel tm.K tm.Λ (tm.Γ tm.k₀) β)
        (ListMapState tm.σ (tm.Γ tm.k₀) β)
  | push k f q =>
      push (ListMapStack.work k) (fun state => f (listMapRunState tm state))
        (listMapRunStmt α β tm q)
  | peek k f q =>
      peek (ListMapStack.work k)
        (fun state head => ListMapState.run (f (listMapRunState tm state) head))
        (listMapRunStmt α β tm q)
  | pop k f q =>
      pop (ListMapStack.work k)
        (fun state head => ListMapState.run (f (listMapRunState tm state) head))
        (listMapRunStmt α β tm q)
  | load f q =>
      load (fun state => ListMapState.run (f (listMapRunState tm state)))
        (listMapRunStmt α β tm q)
  | branch f qTrue qFalse =>
      branch (fun state => f (listMapRunState tm state))
        (listMapRunStmt α β tm qTrue) (listMapRunStmt α β tm qFalse)
  | goto f =>
      goto fun state => ListMapLabel.run (f (listMapRunState tm state))
  | halt =>
      load (fun _ => ListMapState.write (none : Option β))
        (goto fun _ => ListMapLabel.writeOutput)

noncomputable def listMapAllWorkStacks (tm : Turing.FinTM2) : Finset tm.K := by
  letI := tm.kDecidableEq
  letI := tm.kFin
  exact Finset.univ

def listMapEmptyWork (tm : Turing.FinTM2) : (k : tm.K) → List (tm.Γ k) :=
  fun _ => []

lemma listMap_haltList_stk_eq_update_empty (tm : Turing.FinTM2)
    (output : List (tm.Γ tm.k₁)) :
    (Turing.haltList tm output).stk =
      Function.update (listMapEmptyWork tm) tm.k₁ output := by
  letI := tm.kDecidableEq
  funext k
  by_cases hk : k = tm.k₁
  · subst k
    simp [Function.update, Turing.haltList]
  · simp [Function.update, Turing.haltList, listMapEmptyWork, hk]

/-- The arbitrary list-map orchestration machine. -/
noncomputable def listMapMachine (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β] (readInput : α → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) : Turing.FinTM2 := by
  letI := tm.kDecidableEq
  letI := tm.kFin
  letI := tm.ΛFin
  letI := tm.σFin
  letI := tm.Γk₀Fin
  exact
    { K := ListMapStack tm.K
      k₀ := ListMapStack.source
      k₁ := ListMapStack.output
      Γ := listMapAlphabet α β tm
      Λ := ListMapLabel tm.K tm.Λ (tm.Γ tm.k₀) β
      main := ListMapLabel.readSource
      σ := ListMapState tm.σ (tm.Γ tm.k₀) β
      initialState := ListMapState.copy ListMapCopyState.endInput
      Γk₀Fin := by
        dsimp [listMapAlphabet]
        infer_instance
      m := fun
        | ListMapLabel.readSource =>
            pop ListMapStack.source
              (fun _ head =>
                match head with
                | some (some a) => ListMapState.copy (ListMapCopyState.payload (readInput a))
                | some none => ListMapState.copy ListMapCopyState.delimiter
                | none => ListMapState.copy ListMapCopyState.endInput)
              (branch (fun state => (listMapCopyState state).isPayload)
                (goto fun state =>
                  match listMapCopyState state with
                  | ListMapCopyState.payload a => ListMapLabel.pushBlockTemp a
                  | _ => ListMapLabel.finalDrain)
                (branch (fun state => (listMapCopyState state).isDelimiter)
                  (goto fun _ => ListMapLabel.drainBlockTemp)
                  (load (fun _ => ListMapState.final none)
                    (goto fun _ => ListMapLabel.finalDrain))))
        | ListMapLabel.pushBlockTemp a =>
            push ListMapStack.blockTemp (fun _ => a)
              (goto fun _ => ListMapLabel.readSource)
        | ListMapLabel.drainBlockTemp =>
            pop ListMapStack.blockTemp
              (fun _ head =>
                match head with
                | some a => ListMapState.copy (ListMapCopyState.payload a)
                | none => ListMapState.copy ListMapCopyState.delimiter)
              (branch (fun state => (listMapCopyState state).isPayload)
                (goto fun state =>
                  match listMapCopyState state with
                  | ListMapCopyState.payload a => ListMapLabel.pushWorkInput a
                  | _ => ListMapLabel.run tm.main)
                (load (fun _ => ListMapState.run tm.initialState)
                  (goto fun _ => ListMapLabel.run tm.main)))
        | ListMapLabel.pushWorkInput a =>
            push (ListMapStack.work tm.k₀) (fun _ => a)
              (goto fun _ => ListMapLabel.drainBlockTemp)
        | ListMapLabel.run label =>
            listMapRunStmt α β tm (tm.m label)
        | ListMapLabel.writeOutput =>
            pop (ListMapStack.work tm.k₁)
              (fun _ head => ListMapState.write (head.map writeOutput))
              (branch (fun state => (listMapWriteState state).isSome)
                (goto fun state =>
                  match listMapWriteState state with
                  | some b => ListMapLabel.pushAccPayload b
                  | none => ListMapLabel.pushAccDelimiter)
                (goto fun _ => ListMapLabel.pushAccDelimiter))
        | ListMapLabel.pushAccPayload b =>
            push ListMapStack.acc (fun _ => some b)
              (goto fun _ => ListMapLabel.writeOutput)
        | ListMapLabel.pushAccDelimiter =>
            push ListMapStack.acc (fun _ => (none : Option β))
              (goto fun _ => ListMapLabel.reset (listMapAllWorkStacks tm))
        | ListMapLabel.reset remaining =>
            match remaining.toList with
            | [] =>
                load (fun _ => ListMapState.copy ListMapCopyState.endInput)
                  (goto fun _ => ListMapLabel.readSource)
            | k :: _ =>
                pop (ListMapStack.work k)
                  (fun _ head => ListMapState.reset head.isSome)
                  (branch listMapResetState
                    (goto fun _ => ListMapLabel.reset remaining)
                    (goto fun _ => ListMapLabel.reset (remaining.erase k)))
        | ListMapLabel.finalDrain =>
            pop ListMapStack.acc (fun _ head => ListMapState.final head)
              (branch (fun state => (listMapFinalState state).isSome)
                (goto fun state =>
                  match listMapFinalState state with
                  | some b => ListMapLabel.pushFinal b
                  | none => ListMapLabel.finalDrain)
                (load (fun _ => ListMapState.copy ListMapCopyState.endInput) halt))
        | ListMapLabel.pushFinal b =>
            push ListMapStack.output (fun _ => b)
              (goto fun _ => ListMapLabel.finalDrain) }

def listMapCfg (α β : Type) (tm : Turing.FinTM2) [Fintype α] [Fintype β]
    (_readInput : α → tm.Γ tm.k₀) (_writeOutput : tm.Γ tm.k₁ → β)
    (label : Option (ListMapLabel tm.K tm.Λ (tm.Γ tm.k₀) β))
    (state : ListMapState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀)) :
    Turing.TM2.Cfg (listMapAlphabet α β tm)
      (ListMapLabel tm.K tm.Λ (tm.Γ tm.k₀) β)
      (ListMapState tm.σ (tm.Γ tm.k₀) β) where
  l := label
  var := state
  stk
    | ListMapStack.source => source
    | ListMapStack.work k => work k
    | ListMapStack.acc => acc
    | ListMapStack.output => output
    | ListMapStack.blockTemp => blockTemp

def listMapRunCfg (α β : Type) (tm : Turing.FinTM2) [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (cfg : tm.Cfg) (source : List (Option α))
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀)) :
    Turing.TM2.Cfg (listMapAlphabet α β tm)
      (ListMapLabel tm.K tm.Λ (tm.Γ tm.k₀) β)
      (ListMapState tm.σ (tm.Γ tm.k₀) β) :=
  match cfg.l with
  | some label =>
      listMapCfg α β tm readInput writeOutput (some (ListMapLabel.run label))
        (ListMapState.run cfg.var) source cfg.stk acc output blockTemp
  | none =>
      listMapCfg α β tm readInput writeOutput (some ListMapLabel.writeOutput)
        (ListMapState.write none) source cfg.stk acc output blockTemp

lemma listMapRunStmt_stepAux (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) (var : tm.σ)
    (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀)) :
    Turing.TM2.stepAux (listMapRunStmt α β tm q) (ListMapState.run var)
      (fun
        | ListMapStack.source => source
        | ListMapStack.work k => work k
        | ListMapStack.acc => acc
        | ListMapStack.output => output
        | ListMapStack.blockTemp => blockTemp) =
      listMapRunCfg α β tm readInput writeOutput
        (Turing.TM2.stepAux q var work) source acc output blockTemp := by
  induction q generalizing var work with
  | push k f q ih =>
      have hUpdate :
          Function.update
              (fun
                | ListMapStack.source => source
                | ListMapStack.work k => work k
                | ListMapStack.acc => acc
                | ListMapStack.output => output
                | ListMapStack.blockTemp => blockTemp)
              (ListMapStack.work k) (f var :: work k) =
            ((fun
              | ListMapStack.source => source
              | ListMapStack.work k' => (Function.update work k (f var :: work k)) k'
              | ListMapStack.acc => acc
              | ListMapStack.output => output
              | ListMapStack.blockTemp => blockTemp) :
              (s : ListMapStack tm.K) → List (listMapAlphabet α β tm s)) := by
        funext s
        cases s with
        | source => rfl
        | work k' =>
            by_cases hk : k' = k
            · subst k'
              simp [Function.update]
            · simp [Function.update, hk]
        | acc => rfl
        | output => rfl
        | blockTemp => rfl
      simpa [listMapRunStmt, listMapRunState, hUpdate] using
        ih var (Function.update work k (f var :: work k))
  | peek k f q ih =>
      simpa [listMapRunStmt, listMapRunState] using
        ih (f var (work k).head?) work
  | pop k f q ih =>
      have hUpdate :
          Function.update
              (fun
                | ListMapStack.source => source
                | ListMapStack.work k => work k
                | ListMapStack.acc => acc
                | ListMapStack.output => output
                | ListMapStack.blockTemp => blockTemp)
              (ListMapStack.work k) (work k).tail =
            ((fun
              | ListMapStack.source => source
              | ListMapStack.work k' => (Function.update work k (work k).tail) k'
              | ListMapStack.acc => acc
              | ListMapStack.output => output
              | ListMapStack.blockTemp => blockTemp) :
              (s : ListMapStack tm.K) → List (listMapAlphabet α β tm s)) := by
        funext s
        cases s with
        | source => rfl
        | work k' =>
            by_cases hk : k' = k
            · subst k'
              simp [Function.update]
            · simp [Function.update, hk]
        | acc => rfl
        | output => rfl
        | blockTemp => rfl
      simpa [listMapRunStmt, listMapRunState, hUpdate] using
        ih (f var (work k).head?) (Function.update work k (work k).tail)
  | load f q ih =>
      simpa [listMapRunStmt, listMapRunState] using ih (f var) work
  | branch f qTrue qFalse ihTrue ihFalse =>
      by_cases hf : f var = true
      · simp [listMapRunStmt, listMapRunState, hf, ihTrue, listMapRunCfg, listMapCfg]
      · simp [listMapRunStmt, listMapRunState, hf, ihFalse, listMapRunCfg, listMapCfg]
  | goto f =>
      simp [listMapRunStmt, listMapRunState, listMapRunCfg, listMapCfg]
  | halt =>
      simp [listMapRunStmt, listMapRunCfg, listMapCfg]

lemma listMapMachine_run_step (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    {cfg next : tm.Cfg} (source : List (Option α))
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀))
    (hStep : tm.step cfg = some next) :
    (listMapMachine α β tm readInput writeOutput).step
        (listMapRunCfg α β tm readInput writeOutput cfg source acc output blockTemp) =
      some (listMapRunCfg α β tm readInput writeOutput next source acc output blockTemp) := by
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
          simp [listMapRunCfg, listMapCfg, listMapMachine, Turing.FinTM2.step,
            Turing.TM2.step]
          have hAux :=
            listMapRunStmt_stepAux α β tm readInput writeOutput (tm.m label) var source work
              acc output blockTemp
          congr

noncomputable def listMapRun_evalsToInTime (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    {cfg next : tm.Cfg} (source : List (Option α))
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀)) {time : Nat}
    (h : StateTransition.EvalsToInTime tm.step cfg (some next) time) :
    StateTransition.EvalsToInTime (listMapMachine α β tm readInput writeOutput).step
      (listMapRunCfg α β tm readInput writeOutput cfg source acc output blockTemp)
      (some (listMapRunCfg α β tm readInput writeOutput next source acc output blockTemp))
      time := by
  simpa using
    evalsToInTime_map_some
      (fun cfg => listMapRunCfg α β tm readInput writeOutput cfg source acc output blockTemp)
      (fun s s' hStep =>
        listMapMachine_run_step α β tm readInput writeOutput source acc output blockTemp hStep)
      h

lemma listMap_readSource_step_payload (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (state : ListMapState tm.σ (tm.Γ tm.k₀) β)
    (a : α) (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀)) :
    (listMapMachine α β tm readInput writeOutput).step
        (listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource) state
          (some a :: source) work acc output blockTemp) =
      some (listMapCfg α β tm readInput writeOutput
        (some (ListMapLabel.pushBlockTemp (readInput a)))
        (ListMapState.copy (ListMapCopyState.payload (readInput a)))
        source work acc output blockTemp) := by
  simp [listMapMachine, listMapCfg, listMapCopyState, ListMapCopyState.isPayload]
  congr
  funext k
  cases k <;> rfl

lemma listMap_readSource_step_delimiter (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (state : ListMapState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀)) :
    (listMapMachine α β tm readInput writeOutput).step
        (listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource) state
          (none :: source) work acc output blockTemp) =
      some (listMapCfg α β tm readInput writeOutput (some ListMapLabel.drainBlockTemp)
        (ListMapState.copy ListMapCopyState.delimiter)
        source work acc output blockTemp) := by
  simp [listMapMachine, listMapCfg, listMapCopyState, ListMapCopyState.isPayload,
    ListMapCopyState.isDelimiter]
  congr
  funext k
  cases k <;> rfl

end TM2Programs
end ComplexityReduction
