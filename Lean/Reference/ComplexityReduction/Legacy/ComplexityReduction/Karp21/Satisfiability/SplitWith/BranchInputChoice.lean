/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.SplitWith.LongTrace

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction
open Turing.TM2.Stmt

/-- Splitter inputs whose current clause is already in the short/base branch. -/
def splitWithShortInputEncodedType : EncodedType where
  Carrier := { p : splitWithInputEncodedType.Carrier // p.2.length ≤ 3 }
  Symbol := splitWithInputEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun p => splitWithInputEncodedType.encode p.1

/-- Forget the short-branch proof without changing the splitter input encoding. -/
noncomputable def splitWithShortInputForgetTMBackedMap :
    TMBackedCostedMap splitWithShortInputEncodedType splitWithInputEncodedType
      (fun p => p.1) :=
  TMBackedCostedMap.ofEncodingEquiv
    splitWithShortInputEncodedType splitWithInputEncodedType
    (fun p => p.1) (Equiv.refl splitWithInputEncodedType.Symbol) (by
      intro p
      change splitWithInputEncodedType.encode p.1 =
        List.map id (splitWithInputEncodedType.encode p.1)
      simp)

/--
Custom encoded short/long input choice.  Both branches reuse the original
splitter-input payload encoding; only the leading Boolean tag records whether
the chosen input is short (`false`) or long (`true`).
-/
def splitWithBranchInputChoiceEncodedType : EncodedType where
  Carrier := splitWithShortInputEncodedType.Carrier ⊕ splitWithLongInputEncodedType.Carrier
  Symbol := Bool ⊕ splitWithInputEncodedType.Symbol
  finite_symbol := inferInstance
  encode
    | Sum.inl p => [Sum.inl false] ++ (splitWithInputEncodedType.encode p.1).map Sum.inr
    | Sum.inr p => [Sum.inl true] ++ (splitWithInputEncodedType.encode p.1).map Sum.inr

/--
The standard sum encoding of the same short/long branch choice.  The public
branch-choice encoding above deliberately shares the payload alphabet across
both branches; this standard view is the shape needed by a reusable future
`sum_cases` runner.
-/
def splitWithBranchInputChoiceStandardEncodedType : EncodedType :=
  EncodedType.sum splitWithShortInputEncodedType splitWithLongInputEncodedType

/-- Identity-on-carriers view from the custom shared-payload encoding to the standard sum encoding. -/
def splitWithBranchInputChoiceToStandard
    (q : splitWithBranchInputChoiceEncodedType.Carrier) :
    splitWithBranchInputChoiceStandardEncodedType.Carrier :=
  q

inductive TaggedPayloadRetagStack where
  | input
  | output
  | temp
  deriving DecidableEq, Fintype

abbrev taggedPayloadRetagAlphabet (α β : Type) : TaggedPayloadRetagStack → Type
  | .input => Bool ⊕ α
  | .output => β
  | .temp => β

inductive TaggedPayloadRetagLabel (β : Type) where
  | readTag
  | readPayload (tag : Bool)
  | pushTemp (tag : Bool) (b : β)
  | moveTemp (tag : Bool)
  | pushOutput (tag : Bool) (b : β)
  | writeTag (tag : Bool)
  | invalid
  deriving DecidableEq, Fintype

inductive TaggedPayloadRetagState (α β : Type) where
  | input (head : Option (Bool ⊕ α))
  | output (head : Option β)
  deriving Fintype

def taggedPayloadRetagInputState {α β : Type} :
    TaggedPayloadRetagState α β → Option (Bool ⊕ α)
  | .input head => head
  | _ => none

def taggedPayloadRetagOutputState {α β : Type} :
    TaggedPayloadRetagState α β → Option β
  | .output head => head
  | _ => none

def taggedPayloadRetagPayloadMap {α β : Type}
    (leftMap rightMap : α → β) (tag : Bool) (a : α) : β :=
  if tag then rightMap a else leftMap a

open Turing.TM2.Stmt

/--
Finite-state retagger for encodings of the shape `[tag] ++ payload.map inr`.
It remembers the leading Boolean tag, maps every payload symbol with the
tag-selected symbol map, restores the payload order through a temporary stack,
and finally writes the tag as the first output symbol.
-/
def taggedPayloadRetagMachine (α β : Type) [Fintype α] [Fintype β]
    (tagOut : Bool → β) (leftMap rightMap : α → β) : Turing.FinTM2 where
  K := TaggedPayloadRetagStack
  k₀ := .input
  k₁ := .output
  Γ := taggedPayloadRetagAlphabet α β
  Λ := TaggedPayloadRetagLabel β
  main := .readTag
  σ := TaggedPayloadRetagState α β
  initialState := .input none
  Γk₀Fin := by
    dsimp [taggedPayloadRetagAlphabet]
    infer_instance
  m
    | .readTag =>
        pop .input (fun _ head => .input head)
          (goto fun state =>
            match taggedPayloadRetagInputState state with
            | some (Sum.inl tag) => .readPayload tag
            | _ => .invalid)
    | .readPayload tag =>
        pop .input (fun _ head => .input head)
          (goto fun state =>
            match taggedPayloadRetagInputState state with
            | some (Sum.inr a) =>
                .pushTemp tag (taggedPayloadRetagPayloadMap leftMap rightMap tag a)
            | none => .moveTemp tag
            | some (Sum.inl _) => .invalid)
    | .pushTemp tag b =>
        push .temp (fun _ => b) (goto fun _ => .readPayload tag)
    | .moveTemp tag =>
        pop .temp (fun _ head => .output head)
          (goto fun state =>
            match taggedPayloadRetagOutputState state with
            | some b => .pushOutput tag b
            | none => .writeTag tag)
    | .pushOutput tag b =>
        push .output (fun _ => b) (goto fun _ => .moveTemp tag)
    | .writeTag tag =>
        push .output (fun _ => tagOut tag) (load (fun _ => .input none) halt)
    | .invalid =>
        halt

def taggedPayloadRetagCfg (α β : Type) [Fintype α] [Fintype β]
    (tagOut : Bool → β) (leftMap rightMap : α → β)
    (label : TaggedPayloadRetagLabel β) (state : TaggedPayloadRetagState α β)
    (input : List (Bool ⊕ α)) (output temp : List β) :
    (taggedPayloadRetagMachine α β tagOut leftMap rightMap).Cfg where
  l := some label
  var := state
  stk
    | .input => input
    | .output => output
    | .temp => temp

def taggedPayloadRetagHalt (α β : Type) [Fintype α] [Fintype β]
    (tagOut : Bool → β) (leftMap rightMap : α → β) (output : List β) :
    (taggedPayloadRetagMachine α β tagOut leftMap rightMap).Cfg where
  l := none
  var := .input none
  stk
    | .input => []
    | .output => output
    | .temp => []

lemma taggedPayloadRetag_readTag_step (α β : Type) [Fintype α] [Fintype β]
    (tagOut : Bool → β) (leftMap rightMap : α → β)
    (tag : Bool) (payload : List α) (output temp : List β) :
    (taggedPayloadRetagMachine α β tagOut leftMap rightMap).step
        (taggedPayloadRetagCfg α β tagOut leftMap rightMap .readTag (.input none)
          (Sum.inl tag :: payload.map Sum.inr) output temp) =
      some (taggedPayloadRetagCfg α β tagOut leftMap rightMap (.readPayload tag)
        (.input (some (Sum.inl tag))) (payload.map Sum.inr) output temp) := by
  simp [taggedPayloadRetagMachine, taggedPayloadRetagCfg, taggedPayloadRetagInputState]
  congr
  funext k
  cases k <;> rfl

lemma taggedPayloadRetag_readPayload_step_cons
    (α β : Type) [Fintype α] [Fintype β]
    (tagOut : Bool → β) (leftMap rightMap : α → β)
    (tag : Bool) (a : α) (payload : List α) (output temp : List β) :
    (taggedPayloadRetagMachine α β tagOut leftMap rightMap).step
        (taggedPayloadRetagCfg α β tagOut leftMap rightMap (.readPayload tag)
          (.input none) (Sum.inr a :: payload.map Sum.inr) output temp) =
      some (taggedPayloadRetagCfg α β tagOut leftMap rightMap
        (.pushTemp tag (taggedPayloadRetagPayloadMap leftMap rightMap tag a))
        (.input (some (Sum.inr a))) (payload.map Sum.inr) output temp) := by
  simp [taggedPayloadRetagMachine, taggedPayloadRetagCfg, taggedPayloadRetagInputState]
  congr
  funext k
  cases k <;> rfl

lemma taggedPayloadRetag_readPayload_step_nil
    (α β : Type) [Fintype α] [Fintype β]
    (tagOut : Bool → β) (leftMap rightMap : α → β)
    (tag : Bool) (state : TaggedPayloadRetagState α β) (output temp : List β) :
    (taggedPayloadRetagMachine α β tagOut leftMap rightMap).step
        (taggedPayloadRetagCfg α β tagOut leftMap rightMap (.readPayload tag)
          state [] output temp) =
      some (taggedPayloadRetagCfg α β tagOut leftMap rightMap (.moveTemp tag)
        (.input none) [] output temp) := by
  simp [taggedPayloadRetagMachine, taggedPayloadRetagCfg, taggedPayloadRetagInputState]
  congr

lemma taggedPayloadRetag_pushTemp_step
    (α β : Type) [Fintype α] [Fintype β]
    (tagOut : Bool → β) (leftMap rightMap : α → β)
    (tag : Bool) (b : β) (state : TaggedPayloadRetagState α β)
    (input : List (Bool ⊕ α)) (output temp : List β) :
    (taggedPayloadRetagMachine α β tagOut leftMap rightMap).step
        (taggedPayloadRetagCfg α β tagOut leftMap rightMap (.pushTemp tag b)
          state input output temp) =
      some (taggedPayloadRetagCfg α β tagOut leftMap rightMap (.readPayload tag)
        state input output (b :: temp)) := by
  simp [taggedPayloadRetagMachine, taggedPayloadRetagCfg]
  congr
  funext k
  cases k <;> rfl

lemma taggedPayloadRetag_moveTemp_step_cons
    (α β : Type) [Fintype α] [Fintype β]
    (tagOut : Bool → β) (leftMap rightMap : α → β)
    (tag : Bool) (b : β) (input : List (Bool ⊕ α)) (output temp : List β) :
    (taggedPayloadRetagMachine α β tagOut leftMap rightMap).step
        (taggedPayloadRetagCfg α β tagOut leftMap rightMap (.moveTemp tag)
          (.input none) input output (b :: temp)) =
      some (taggedPayloadRetagCfg α β tagOut leftMap rightMap (.pushOutput tag b)
        (.output (some b)) input output temp) := by
  simp [taggedPayloadRetagMachine, taggedPayloadRetagCfg, taggedPayloadRetagOutputState]
  congr
  funext k
  cases k <;> rfl

lemma taggedPayloadRetag_moveTemp_step_nil
    (α β : Type) [Fintype α] [Fintype β]
    (tagOut : Bool → β) (leftMap rightMap : α → β)
    (tag : Bool) (state : TaggedPayloadRetagState α β)
    (input : List (Bool ⊕ α)) (output : List β) :
    (taggedPayloadRetagMachine α β tagOut leftMap rightMap).step
        (taggedPayloadRetagCfg α β tagOut leftMap rightMap (.moveTemp tag)
          state input output []) =
      some (taggedPayloadRetagCfg α β tagOut leftMap rightMap (.writeTag tag)
        (.output none) input output []) := by
  simp [taggedPayloadRetagMachine, taggedPayloadRetagCfg, taggedPayloadRetagOutputState]
  congr

lemma taggedPayloadRetag_pushOutput_step
    (α β : Type) [Fintype α] [Fintype β]
    (tagOut : Bool → β) (leftMap rightMap : α → β)
    (tag : Bool) (b : β) (state : TaggedPayloadRetagState α β)
    (input : List (Bool ⊕ α)) (output temp : List β) :
    (taggedPayloadRetagMachine α β tagOut leftMap rightMap).step
        (taggedPayloadRetagCfg α β tagOut leftMap rightMap (.pushOutput tag b)
          state input output temp) =
      some (taggedPayloadRetagCfg α β tagOut leftMap rightMap (.moveTemp tag)
        state input (b :: output) temp) := by
  simp [taggedPayloadRetagMachine, taggedPayloadRetagCfg]
  congr
  funext k
  cases k <;> rfl

lemma taggedPayloadRetag_writeTag_step
    (α β : Type) [Fintype α] [Fintype β]
    (tagOut : Bool → β) (leftMap rightMap : α → β)
    (tag : Bool) (output : List β) :
    (taggedPayloadRetagMachine α β tagOut leftMap rightMap).step
        (taggedPayloadRetagCfg α β tagOut leftMap rightMap (.writeTag tag)
          (.output none) [] output []) =
      some (taggedPayloadRetagHalt α β tagOut leftMap rightMap (tagOut tag :: output)) := by
  simp [taggedPayloadRetagMachine, taggedPayloadRetagCfg, taggedPayloadRetagHalt]
  congr
  funext k
  cases k <;> rfl

lemma taggedPayloadRetag_initList
    (α β : Type) [Fintype α] [Fintype β]
    (tagOut : Bool → β) (leftMap rightMap : α → β)
    (tag : Bool) (payload : List α) :
    Turing.initList (taggedPayloadRetagMachine α β tagOut leftMap rightMap)
        (Sum.inl tag :: payload.map Sum.inr) =
      taggedPayloadRetagCfg α β tagOut leftMap rightMap .readTag (.input none)
        (Sum.inl tag :: payload.map Sum.inr) [] [] := by
  simp [taggedPayloadRetagMachine, taggedPayloadRetagCfg, Turing.initList]
  congr
  funext k
  cases k <;> rfl

lemma taggedPayloadRetag_haltList
    (α β : Type) [Fintype α] [Fintype β]
    (tagOut : Bool → β) (leftMap rightMap : α → β) (output : List β) :
    Turing.haltList (taggedPayloadRetagMachine α β tagOut leftMap rightMap) output =
      taggedPayloadRetagHalt α β tagOut leftMap rightMap output := by
  simp [taggedPayloadRetagMachine, taggedPayloadRetagHalt, Turing.haltList]
  congr
  funext k
  cases k <;> rfl

def taggedPayloadRetag_readPayload_run
    (α β : Type) [Fintype α] [Fintype β]
    (tagOut : Bool → β) (leftMap rightMap : α → β)
    (tag : Bool) (state : TaggedPayloadRetagState α β)
    (payload : List α) (output temp : List β) :
    StateTransition.EvalsToInTime
      (taggedPayloadRetagMachine α β tagOut leftMap rightMap).step
      (taggedPayloadRetagCfg α β tagOut leftMap rightMap (.readPayload tag)
        state (payload.map Sum.inr) output temp)
      (some (taggedPayloadRetagCfg α β tagOut leftMap rightMap (.moveTemp tag)
        (.input none) [] output
        ((payload.map (taggedPayloadRetagPayloadMap leftMap rightMap tag)).reverse ++ temp)))
      (2 * payload.length + 1) := by
  induction payload generalizing state temp with
  | nil =>
      simpa using
        TM2Programs.evalsToInTimeOne
          (taggedPayloadRetag_readPayload_step_nil α β tagOut leftMap rightMap tag state
            output temp)
  | cons a payload ih =>
      let tm := taggedPayloadRetagMachine α β tagOut leftMap rightMap
      let mapped := taggedPayloadRetagPayloadMap leftMap rightMap tag a
      let c₀ := taggedPayloadRetagCfg α β tagOut leftMap rightMap (.readPayload tag)
        state (Sum.inr a :: payload.map Sum.inr) output temp
      let c₁ := taggedPayloadRetagCfg α β tagOut leftMap rightMap (.pushTemp tag mapped)
        (.input (some (Sum.inr a))) (payload.map Sum.inr) output temp
      let c₂ := taggedPayloadRetagCfg α β tagOut leftMap rightMap (.readPayload tag)
        (.input (some (Sum.inr a))) (payload.map Sum.inr) output (mapped :: temp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne
          (taggedPayloadRetag_readPayload_step_cons α β tagOut leftMap rightMap tag a
            payload output temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        TM2Programs.evalsToInTimeOne
          (taggedPayloadRetag_pushTemp_step α β tagOut leftMap rightMap tag mapped
            (.input (some (Sum.inr a))) (payload.map Sum.inr) output temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (taggedPayloadRetagCfg α β tagOut leftMap rightMap (.moveTemp tag)
            (.input none) [] output
            ((payload.map (taggedPayloadRetagPayloadMap leftMap rightMap tag)).reverse ++
              (mapped :: temp))))
          (2 * payload.length + 1) :=
        ih (.input (some (Sum.inr a))) (mapped :: temp)
      simpa [tm, c₀, c₁, c₂, mapped, List.map_cons, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * payload.length + 1)
          c₀ c₂
          (some (taggedPayloadRetagCfg α β tagOut leftMap rightMap (.moveTemp tag)
            (.input none) [] output
            ((payload.map (taggedPayloadRetagPayloadMap leftMap rightMap tag)).reverse ++
              (mapped :: temp))))
          h₁₂ hTail

def taggedPayloadRetag_moveTemp_run
    (α β : Type) [Fintype α] [Fintype β]
    (tagOut : Bool → β) (leftMap rightMap : α → β)
    (tag : Bool) (state : TaggedPayloadRetagState α β)
    (input : List (Bool ⊕ α)) (output temp : List β) :
    StateTransition.EvalsToInTime
      (taggedPayloadRetagMachine α β tagOut leftMap rightMap).step
      (taggedPayloadRetagCfg α β tagOut leftMap rightMap (.moveTemp tag)
        state input output temp)
      (some (taggedPayloadRetagCfg α β tagOut leftMap rightMap (.writeTag tag)
        (.output none) input (temp.reverse ++ output) []))
      (2 * temp.length + 1) := by
  induction temp generalizing state output with
  | nil =>
      simpa using
        TM2Programs.evalsToInTimeOne
          (taggedPayloadRetag_moveTemp_step_nil α β tagOut leftMap rightMap tag state input
            output)
  | cons b temp ih =>
      let tm := taggedPayloadRetagMachine α β tagOut leftMap rightMap
      let c₀ := taggedPayloadRetagCfg α β tagOut leftMap rightMap (.moveTemp tag)
        state input output (b :: temp)
      let c₁ := taggedPayloadRetagCfg α β tagOut leftMap rightMap (.pushOutput tag b)
        (.output (some b)) input output temp
      let c₂ := taggedPayloadRetagCfg α β tagOut leftMap rightMap (.moveTemp tag)
        (.output (some b)) input (b :: output) temp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne
          (taggedPayloadRetag_moveTemp_step_cons α β tagOut leftMap rightMap tag b input
            output temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        TM2Programs.evalsToInTimeOne
          (taggedPayloadRetag_pushOutput_step α β tagOut leftMap rightMap tag b
            (.output (some b)) input output temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (taggedPayloadRetagCfg α β tagOut leftMap rightMap (.writeTag tag)
            (.output none) input (temp.reverse ++ (b :: output)) []))
          (2 * temp.length + 1) :=
        ih (.output (some b)) (b :: output)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * temp.length + 1)
          c₀ c₂
          (some (taggedPayloadRetagCfg α β tagOut leftMap rightMap (.writeTag tag)
            (.output none) input (temp.reverse ++ (b :: output)) []))
          h₁₂ hTail

def taggedPayloadRetag_outputs
    (α β : Type) [Fintype α] [Fintype β]
    (tagOut : Bool → β) (leftMap rightMap : α → β)
    (tag : Bool) (payload : List α) :
    Turing.TM2OutputsInTime
      (taggedPayloadRetagMachine α β tagOut leftMap rightMap)
      (Sum.inl tag :: payload.map Sum.inr)
      (some
        (tagOut tag ::
          payload.map (taggedPayloadRetagPayloadMap leftMap rightMap tag)))
      (4 * payload.length + 4) := by
  let tm := taggedPayloadRetagMachine α β tagOut leftMap rightMap
  let mapped := payload.map (taggedPayloadRetagPayloadMap leftMap rightMap tag)
  let c₁ := taggedPayloadRetagCfg α β tagOut leftMap rightMap (.readPayload tag)
    (.input (some (Sum.inl tag))) (payload.map Sum.inr) [] []
  let c₂ := taggedPayloadRetagCfg α β tagOut leftMap rightMap (.moveTemp tag)
    (.input none) [] [] mapped.reverse
  let c₃ := taggedPayloadRetagCfg α β tagOut leftMap rightMap (.writeTag tag)
    (.output none) [] mapped []
  let done := taggedPayloadRetagHalt α β tagOut leftMap rightMap (tagOut tag :: mapped)
  have hTag : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm (Sum.inl tag :: payload.map Sum.inr)) (some c₁) 1 := by
    simpa [tm, c₁, taggedPayloadRetag_initList] using
      TM2Programs.evalsToInTimeOne
        (taggedPayloadRetag_readTag_step α β tagOut leftMap rightMap tag payload [] [])
  have hRead : StateTransition.EvalsToInTime tm.step c₁ (some c₂)
      (2 * payload.length + 1) := by
    simpa [tm, c₁, c₂, mapped] using
      taggedPayloadRetag_readPayload_run α β tagOut leftMap rightMap tag
        (.input (some (Sum.inl tag))) payload [] []
  have hMove : StateTransition.EvalsToInTime tm.step c₂ (some c₃)
      (2 * mapped.reverse.length + 1) := by
    simpa [tm, c₂, c₃, mapped, List.reverse_reverse] using
      taggedPayloadRetag_moveTemp_run α β tagOut leftMap rightMap tag (.input none) []
        [] mapped.reverse
  have hWrite : StateTransition.EvalsToInTime tm.step c₃ (some done) 1 := by
    simpa [tm, c₃, done, mapped] using
      TM2Programs.evalsToInTimeOne
        (taggedPayloadRetag_writeTag_step α β tagOut leftMap rightMap tag mapped)
  have hTagRead : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm (Sum.inl tag :: payload.map Sum.inr)) (some c₂)
      ((2 * payload.length + 1) + 1) :=
    StateTransition.EvalsToInTime.trans tm.step 1 (2 * payload.length + 1)
      (Turing.initList tm (Sum.inl tag :: payload.map Sum.inr)) c₁ (some c₂)
      hTag hRead
  have hMoveWrite : StateTransition.EvalsToInTime tm.step c₂ (some done)
      (1 + (2 * mapped.reverse.length + 1)) :=
    StateTransition.EvalsToInTime.trans tm.step (2 * mapped.reverse.length + 1) 1
      c₂ c₃ (some done) hMove hWrite
  have hAll : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm (Sum.inl tag :: payload.map Sum.inr)) (some done)
      ((1 + (2 * mapped.reverse.length + 1)) + ((2 * payload.length + 1) + 1)) :=
    StateTransition.EvalsToInTime.trans tm.step ((2 * payload.length + 1) + 1)
      (1 + (2 * mapped.reverse.length + 1))
      (Turing.initList tm (Sum.inl tag :: payload.map Sum.inr)) c₂ (some done)
      hTagRead hMoveWrite
  change StateTransition.EvalsToInTime tm.step
    (Turing.initList tm (Sum.inl tag :: payload.map Sum.inr))
    (some (Turing.haltList tm (tagOut tag :: mapped))) (4 * payload.length + 4)
  rw [taggedPayloadRetag_haltList]
  exact
    TM2Programs.evalsToInTime_mono hAll (by
      simp [mapped, List.length_reverse]
      omega)

theorem splitWithBranchInputChoiceToStandard_encode_retag
    (q : splitWithBranchInputChoiceEncodedType.Carrier) :
    splitWithBranchInputChoiceStandardEncodedType.encode
        (splitWithBranchInputChoiceToStandard q) =
      match q with
      | Sum.inl p =>
          Sum.inl false ::
            (splitWithInputEncodedType.encode p.1).map (fun s => Sum.inr (Sum.inl s))
      | Sum.inr p =>
          Sum.inl true ::
            (splitWithInputEncodedType.encode p.1).map (fun s => Sum.inr (Sum.inr s)) := by
  cases q with
  | inl p =>
      rfl
  | inr p =>
      rfl

/-- Direct TM-backed retagging from the custom shared-payload branch encoding to standard sum. -/
noncomputable def splitWithBranchInputChoiceToStandardTMBackedMap :
    TMBackedCostedMap
      splitWithBranchInputChoiceEncodedType
      splitWithBranchInputChoiceStandardEncodedType
      splitWithBranchInputChoiceToStandard where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithBranchInputChoiceEncodedType)
      (Y := splitWithBranchInputChoiceStandardEncodedType)
      (LinearSizeBound.of_le (by
        intro q
        cases q with
        | inl p =>
            simp [splitWithBranchInputChoiceEncodedType,
              splitWithBranchInputChoiceStandardEncodedType,
              splitWithBranchInputChoiceToStandard, EncodedType.inputSize,
              EncodedType.sum, splitWithShortInputEncodedType]
        | inr p =>
            simp [splitWithBranchInputChoiceEncodedType,
              splitWithBranchInputChoiceStandardEncodedType,
              splitWithBranchInputChoiceToStandard, EncodedType.inputSize,
              EncodedType.sum, splitWithLongInputEncodedType]))
  tm_polytime :=
    ⟨{ tm :=
          taggedPayloadRetagMachine
            splitWithInputEncodedType.Symbol
            splitWithBranchInputChoiceStandardEncodedType.Symbol
            Sum.inl
            (fun s => Sum.inr (Sum.inl s))
            (fun s => Sum.inr (Sum.inr s))
       inputAlphabet := Equiv.refl _
       outputAlphabet := Equiv.refl _
       time := 4 * Polynomial.X + 4
       outputsFun := by
        intro q
        cases q with
        | inl p =>
            change Turing.TM2OutputsInTime
              (taggedPayloadRetagMachine
                splitWithInputEncodedType.Symbol
                splitWithBranchInputChoiceStandardEncodedType.Symbol
                Sum.inl
                (fun s => Sum.inr (Sum.inl s))
                (fun s => Sum.inr (Sum.inr s)))
              (List.map id
                (Sum.inl false :: (splitWithInputEncodedType.encode p.1).map Sum.inr))
              (some (List.map id
                (splitWithBranchInputChoiceStandardEncodedType.encode
                  (splitWithBranchInputChoiceToStandard (Sum.inl p)))))
              ((4 * Polynomial.X + 4).eval
                (Sum.inl false :: (splitWithInputEncodedType.encode p.1).map Sum.inr).length)
            have hOut :=
              taggedPayloadRetag_outputs
                splitWithInputEncodedType.Symbol
                splitWithBranchInputChoiceStandardEncodedType.Symbol
                Sum.inl
                (fun s => Sum.inr (Sum.inl s))
                (fun s => Sum.inr (Sum.inr s))
                false
                (splitWithInputEncodedType.encode p.1)
            exact
              TM2Programs.evalsToInTime_mono
                (by
                  simpa [splitWithBranchInputChoiceStandardEncodedType,
                    splitWithBranchInputChoiceToStandard, splitWithShortInputEncodedType,
                    EncodedType.sum, taggedPayloadRetagPayloadMap] using hOut)
                (by
                  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X])
        | inr p =>
            change Turing.TM2OutputsInTime
              (taggedPayloadRetagMachine
                splitWithInputEncodedType.Symbol
                splitWithBranchInputChoiceStandardEncodedType.Symbol
                Sum.inl
                (fun s => Sum.inr (Sum.inl s))
                (fun s => Sum.inr (Sum.inr s)))
              (List.map id
                (Sum.inl true :: (splitWithInputEncodedType.encode p.1).map Sum.inr))
              (some (List.map id
                (splitWithBranchInputChoiceStandardEncodedType.encode
                  (splitWithBranchInputChoiceToStandard (Sum.inr p)))))
              ((4 * Polynomial.X + 4).eval
                (Sum.inl true :: (splitWithInputEncodedType.encode p.1).map Sum.inr).length)
            have hOut :=
              taggedPayloadRetag_outputs
                splitWithInputEncodedType.Symbol
                splitWithBranchInputChoiceStandardEncodedType.Symbol
                Sum.inl
                (fun s => Sum.inr (Sum.inl s))
                (fun s => Sum.inr (Sum.inr s))
                true
                (splitWithInputEncodedType.encode p.1)
            exact
              TM2Programs.evalsToInTime_mono
                (by
                  simpa [splitWithBranchInputChoiceStandardEncodedType,
                    splitWithBranchInputChoiceToStandard, splitWithLongInputEncodedType,
                    EncodedType.sum, taggedPayloadRetagPayloadMap] using hOut)
                (by
                  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]) }⟩


end Karp21
end ComplexityReduction
