/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.SplitWith.TraceInstructions

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction
open Turing.TM2.Stmt

def splitWithTraceRunnerStepChoiceEncodedType : EncodedType where
  Carrier :=
    splitWithInputEncodedType.Carrier ⊕ splitWithTraceLoopAccEncodedType.Carrier
  Symbol := Bool ⊕ (splitWithInputEncodedType.Symbol ⊕ splitWithTraceLoopAccEncodedType.Symbol)
  finite_symbol := inferInstance
  encode
    | Sum.inl input =>
        [Sum.inl false] ++ (splitWithInputEncodedType.encode input).map
          (fun s => Sum.inr (Sum.inl s))
    | Sum.inr acc =>
        [Sum.inl true] ++ (splitWithTraceLoopAccEncodedType.encode acc).map
          (fun s => Sum.inr (Sum.inr s))

def splitWithTraceRunnerStepChoice
    (p : splitWithTraceLoopAccEncodedType.Carrier ×
      splitWithTraceRunnerInstructionEncodedType.Carrier) :
    splitWithTraceRunnerStepChoiceEncodedType.Carrier :=
  match p.2 with
  | Sum.inl input => Sum.inl input
  | Sum.inr _ => Sum.inr p.1

inductive SplitWithTraceRunnerStepChoiceStack where
  | input
  | output
  | temp
  deriving DecidableEq, Fintype

abbrev splitWithTraceRunnerStepChoiceInputSymbol :=
  (EncodedType.prod
    splitWithTraceLoopAccEncodedType
    splitWithTraceRunnerInstructionEncodedType).Symbol

abbrev splitWithTraceRunnerStepChoiceOutputSymbol :=
  splitWithTraceRunnerStepChoiceEncodedType.Symbol

abbrev splitWithTraceRunnerStepChoiceAlphabet :
    SplitWithTraceRunnerStepChoiceStack → Type
  | .input => splitWithTraceRunnerStepChoiceInputSymbol
  | .output => splitWithTraceRunnerStepChoiceOutputSymbol
  | .temp => splitWithTraceRunnerStepChoiceOutputSymbol

inductive SplitWithTraceRunnerStepChoiceLabel where
  | readAcc
  | pushAccTemp (s : splitWithTraceRunnerStepChoiceOutputSymbol)
  | readInstructionTag
  | clearAcc
  | readInputPayload
  | pushInputTemp (s : splitWithTraceRunnerStepChoiceOutputSymbol)
  | moveTemp (tag : Bool)
  | pushOutput (tag : Bool) (s : splitWithTraceRunnerStepChoiceOutputSymbol)
  | writeTag (tag : Bool)
  | invalid
  deriving Fintype

inductive SplitWithTraceRunnerStepChoiceState where
  | input (head : Option splitWithTraceRunnerStepChoiceInputSymbol)
  | output (head : Option splitWithTraceRunnerStepChoiceOutputSymbol)
  deriving Fintype

def splitWithTraceRunnerStepChoiceInputState :
    SplitWithTraceRunnerStepChoiceState →
      Option splitWithTraceRunnerStepChoiceInputSymbol
  | .input head => head
  | _ => none

def splitWithTraceRunnerStepChoiceOutputState :
    SplitWithTraceRunnerStepChoiceState →
      Option splitWithTraceRunnerStepChoiceOutputSymbol
  | .output head => head
  | _ => none

def splitWithTraceRunnerStepChoiceAccSymbol
    (s : splitWithTraceLoopAccEncodedType.Symbol) :
    splitWithTraceRunnerStepChoiceOutputSymbol :=
  Sum.inr (Sum.inr s)

def splitWithTraceRunnerStepChoiceInputPayloadSymbol
    (s : splitWithInputEncodedType.Symbol) :
    splitWithTraceRunnerStepChoiceOutputSymbol :=
  Sum.inr (Sum.inl s)

def splitWithTraceRunnerStepChoiceAccInputSymbol
    (s : splitWithTraceLoopAccEncodedType.Symbol) :
    splitWithTraceRunnerStepChoiceInputSymbol :=
  some (Sum.inl s)

def splitWithTraceRunnerStepChoiceInstructionTagInputSymbol
    (tag : Bool) :
    splitWithTraceRunnerStepChoiceInputSymbol :=
  some (Sum.inr (Sum.inl tag))

def splitWithTraceRunnerStepChoiceInputPayloadInputSymbol
    (s : splitWithInputEncodedType.Symbol) :
    splitWithTraceRunnerStepChoiceInputSymbol :=
  some (Sum.inr (Sum.inr (Sum.inl s)))

def splitWithTraceRunnerStepChoiceMachine : Turing.FinTM2 where
  K := SplitWithTraceRunnerStepChoiceStack
  k₀ := .input
  k₁ := .output
  Γ := splitWithTraceRunnerStepChoiceAlphabet
  Λ := SplitWithTraceRunnerStepChoiceLabel
  main := .readAcc
  σ := SplitWithTraceRunnerStepChoiceState
  initialState := .input none
  Γk₀Fin := inferInstance
  m
    | .readAcc =>
        pop .input (fun _ head => .input head)
          (goto fun state =>
            match splitWithTraceRunnerStepChoiceInputState state with
            | some (some (Sum.inl s)) =>
                .pushAccTemp (splitWithTraceRunnerStepChoiceAccSymbol s)
            | some none => .readInstructionTag
            | _ => .invalid)
    | .pushAccTemp s =>
        push .temp (fun _ => s) (goto fun _ => .readAcc)
    | .readInstructionTag =>
        pop .input (fun _ head => .input head)
          (goto fun state =>
            match splitWithTraceRunnerStepChoiceInputState state with
            | some (some (Sum.inr (Sum.inl false))) => .clearAcc
            | some (some (Sum.inr (Sum.inl true))) => .moveTemp true
            | _ => .invalid)
    | .clearAcc =>
        pop .temp (fun _ head => .output head)
          (goto fun state =>
            match splitWithTraceRunnerStepChoiceOutputState state with
            | some _ => .clearAcc
            | none => .readInputPayload)
    | .readInputPayload =>
        pop .input (fun _ head => .input head)
          (goto fun state =>
            match splitWithTraceRunnerStepChoiceInputState state with
            | some (some (Sum.inr (Sum.inr (Sum.inl s)))) =>
                .pushInputTemp (splitWithTraceRunnerStepChoiceInputPayloadSymbol s)
            | none => .moveTemp false
            | _ => .invalid)
    | .pushInputTemp s =>
        push .temp (fun _ => s) (goto fun _ => .readInputPayload)
    | .moveTemp tag =>
        pop .temp (fun _ head => .output head)
          (goto fun state =>
            match splitWithTraceRunnerStepChoiceOutputState state with
            | some s => .pushOutput tag s
            | none => .writeTag tag)
    | .pushOutput tag s =>
        push .output (fun _ => s) (goto fun _ => .moveTemp tag)
    | .writeTag tag =>
        push .output (fun _ => Sum.inl tag) (load (fun _ => .input none) halt)
    | .invalid =>
        halt

def splitWithTraceRunnerStepChoiceCfg
    (label : SplitWithTraceRunnerStepChoiceLabel)
    (state : SplitWithTraceRunnerStepChoiceState)
    (input : List splitWithTraceRunnerStepChoiceInputSymbol)
    (output temp : List splitWithTraceRunnerStepChoiceOutputSymbol) :
    splitWithTraceRunnerStepChoiceMachine.Cfg where
  l := some label
  var := state
  stk
    | .input => input
    | .output => output
    | .temp => temp

def splitWithTraceRunnerStepChoiceHalt
    (output : List splitWithTraceRunnerStepChoiceOutputSymbol) :
    splitWithTraceRunnerStepChoiceMachine.Cfg where
  l := none
  var := .input none
  stk
    | .input => []
    | .output => output
    | .temp => []

lemma splitWithTraceRunnerStepChoice_readAcc_step_cons
    (s : splitWithTraceLoopAccEncodedType.Symbol)
    (state : SplitWithTraceRunnerStepChoiceState)
    (input : List splitWithTraceRunnerStepChoiceInputSymbol)
    (output temp : List splitWithTraceRunnerStepChoiceOutputSymbol) :
    splitWithTraceRunnerStepChoiceMachine.step
        (splitWithTraceRunnerStepChoiceCfg .readAcc state
          (some (Sum.inl s) :: input) output temp) =
      some (splitWithTraceRunnerStepChoiceCfg
        (.pushAccTemp (splitWithTraceRunnerStepChoiceAccSymbol s))
        (.input (some (some (Sum.inl s)))) input output temp) := by
  simp [splitWithTraceRunnerStepChoiceMachine, splitWithTraceRunnerStepChoiceCfg,
    splitWithTraceRunnerStepChoiceInputState]
  congr
  funext k
  cases k <;> rfl

lemma splitWithTraceRunnerStepChoice_readAcc_step_delim
    (state : SplitWithTraceRunnerStepChoiceState)
    (input : List splitWithTraceRunnerStepChoiceInputSymbol)
    (output temp : List splitWithTraceRunnerStepChoiceOutputSymbol) :
    splitWithTraceRunnerStepChoiceMachine.step
        (splitWithTraceRunnerStepChoiceCfg .readAcc state
          (none :: input) output temp) =
      some (splitWithTraceRunnerStepChoiceCfg .readInstructionTag
        (.input (some none)) input output temp) := by
  simp [splitWithTraceRunnerStepChoiceMachine, splitWithTraceRunnerStepChoiceCfg,
    splitWithTraceRunnerStepChoiceInputState]
  congr
  funext k
  cases k <;> rfl

lemma splitWithTraceRunnerStepChoice_pushAccTemp_step
    (s : splitWithTraceRunnerStepChoiceOutputSymbol)
    (state : SplitWithTraceRunnerStepChoiceState)
    (input : List splitWithTraceRunnerStepChoiceInputSymbol)
    (output temp : List splitWithTraceRunnerStepChoiceOutputSymbol) :
    splitWithTraceRunnerStepChoiceMachine.step
        (splitWithTraceRunnerStepChoiceCfg (.pushAccTemp s) state input output temp) =
      some (splitWithTraceRunnerStepChoiceCfg .readAcc state input output (s :: temp)) := by
  simp [splitWithTraceRunnerStepChoiceMachine, splitWithTraceRunnerStepChoiceCfg]
  congr
  funext k
  cases k <;> rfl

lemma splitWithTraceRunnerStepChoice_readInstructionTag_step_left
    (input : List splitWithTraceRunnerStepChoiceInputSymbol)
    (output temp : List splitWithTraceRunnerStepChoiceOutputSymbol) :
    splitWithTraceRunnerStepChoiceMachine.step
        (splitWithTraceRunnerStepChoiceCfg .readInstructionTag (.input (some none))
          (some (Sum.inr (Sum.inl false)) :: input) output temp) =
      some (splitWithTraceRunnerStepChoiceCfg .clearAcc
        (.input (some (some (Sum.inr (Sum.inl false))))) input output temp) := by
  simp [splitWithTraceRunnerStepChoiceMachine, splitWithTraceRunnerStepChoiceCfg,
    splitWithTraceRunnerStepChoiceInputState]
  congr
  funext k
  cases k <;> rfl

lemma splitWithTraceRunnerStepChoice_readInstructionTag_step_right
    (input : List splitWithTraceRunnerStepChoiceInputSymbol)
    (output temp : List splitWithTraceRunnerStepChoiceOutputSymbol) :
    splitWithTraceRunnerStepChoiceMachine.step
        (splitWithTraceRunnerStepChoiceCfg .readInstructionTag (.input (some none))
          (some (Sum.inr (Sum.inl true)) :: input) output temp) =
      some (splitWithTraceRunnerStepChoiceCfg (.moveTemp true)
        (.input (some (some (Sum.inr (Sum.inl true))))) input output temp) := by
  simp [splitWithTraceRunnerStepChoiceMachine, splitWithTraceRunnerStepChoiceCfg,
    splitWithTraceRunnerStepChoiceInputState]
  congr
  funext k
  cases k <;> rfl

lemma splitWithTraceRunnerStepChoice_clearAcc_step_cons
    (s : splitWithTraceRunnerStepChoiceOutputSymbol)
    (state : SplitWithTraceRunnerStepChoiceState)
    (input : List splitWithTraceRunnerStepChoiceInputSymbol)
    (output temp : List splitWithTraceRunnerStepChoiceOutputSymbol) :
    splitWithTraceRunnerStepChoiceMachine.step
        (splitWithTraceRunnerStepChoiceCfg .clearAcc state input output (s :: temp)) =
      some (splitWithTraceRunnerStepChoiceCfg .clearAcc
        (.output (some s)) input output temp) := by
  simp [splitWithTraceRunnerStepChoiceMachine, splitWithTraceRunnerStepChoiceCfg,
    splitWithTraceRunnerStepChoiceOutputState]
  congr
  funext k
  cases k <;> rfl

lemma splitWithTraceRunnerStepChoice_clearAcc_step_nil
    (state : SplitWithTraceRunnerStepChoiceState)
    (input : List splitWithTraceRunnerStepChoiceInputSymbol)
    (output : List splitWithTraceRunnerStepChoiceOutputSymbol) :
    splitWithTraceRunnerStepChoiceMachine.step
        (splitWithTraceRunnerStepChoiceCfg .clearAcc state input output []) =
      some (splitWithTraceRunnerStepChoiceCfg .readInputPayload
        (.output none) input output []) := by
  simp [splitWithTraceRunnerStepChoiceMachine, splitWithTraceRunnerStepChoiceCfg,
    splitWithTraceRunnerStepChoiceOutputState]
  congr

lemma splitWithTraceRunnerStepChoice_readInputPayload_step_cons
    (s : splitWithInputEncodedType.Symbol)
    (state : SplitWithTraceRunnerStepChoiceState)
    (input : List splitWithTraceRunnerStepChoiceInputSymbol)
    (output temp : List splitWithTraceRunnerStepChoiceOutputSymbol) :
    splitWithTraceRunnerStepChoiceMachine.step
        (splitWithTraceRunnerStepChoiceCfg .readInputPayload state
          (some (Sum.inr (Sum.inr (Sum.inl s))) :: input) output temp) =
      some (splitWithTraceRunnerStepChoiceCfg
        (.pushInputTemp (splitWithTraceRunnerStepChoiceInputPayloadSymbol s))
        (.input (some (some (Sum.inr (Sum.inr (Sum.inl s)))))) input output temp) := by
  simp [splitWithTraceRunnerStepChoiceMachine, splitWithTraceRunnerStepChoiceCfg,
    splitWithTraceRunnerStepChoiceInputState]
  congr
  funext k
  cases k <;> rfl

lemma splitWithTraceRunnerStepChoice_readInputPayload_step_nil
    (state : SplitWithTraceRunnerStepChoiceState)
    (output temp : List splitWithTraceRunnerStepChoiceOutputSymbol) :
    splitWithTraceRunnerStepChoiceMachine.step
        (splitWithTraceRunnerStepChoiceCfg .readInputPayload state [] output temp) =
      some (splitWithTraceRunnerStepChoiceCfg (.moveTemp false)
        (.input none) [] output temp) := by
  simp [splitWithTraceRunnerStepChoiceMachine, splitWithTraceRunnerStepChoiceCfg,
    splitWithTraceRunnerStepChoiceInputState]
  congr

lemma splitWithTraceRunnerStepChoice_pushInputTemp_step
    (s : splitWithTraceRunnerStepChoiceOutputSymbol)
    (state : SplitWithTraceRunnerStepChoiceState)
    (input : List splitWithTraceRunnerStepChoiceInputSymbol)
    (output temp : List splitWithTraceRunnerStepChoiceOutputSymbol) :
    splitWithTraceRunnerStepChoiceMachine.step
        (splitWithTraceRunnerStepChoiceCfg (.pushInputTemp s) state input output temp) =
      some (splitWithTraceRunnerStepChoiceCfg .readInputPayload state input output (s :: temp)) := by
  simp [splitWithTraceRunnerStepChoiceMachine, splitWithTraceRunnerStepChoiceCfg]
  congr
  funext k
  cases k <;> rfl

lemma splitWithTraceRunnerStepChoice_moveTemp_step_cons
    (tag : Bool) (s : splitWithTraceRunnerStepChoiceOutputSymbol)
    (state : SplitWithTraceRunnerStepChoiceState)
    (input : List splitWithTraceRunnerStepChoiceInputSymbol)
    (output temp : List splitWithTraceRunnerStepChoiceOutputSymbol) :
    splitWithTraceRunnerStepChoiceMachine.step
        (splitWithTraceRunnerStepChoiceCfg (.moveTemp tag) state input output (s :: temp)) =
      some (splitWithTraceRunnerStepChoiceCfg (.pushOutput tag s)
        (.output (some s)) input output temp) := by
  simp [splitWithTraceRunnerStepChoiceMachine, splitWithTraceRunnerStepChoiceCfg,
    splitWithTraceRunnerStepChoiceOutputState]
  congr
  funext k
  cases k <;> rfl

lemma splitWithTraceRunnerStepChoice_moveTemp_step_nil
    (tag : Bool) (state : SplitWithTraceRunnerStepChoiceState)
    (input : List splitWithTraceRunnerStepChoiceInputSymbol)
    (output : List splitWithTraceRunnerStepChoiceOutputSymbol) :
    splitWithTraceRunnerStepChoiceMachine.step
        (splitWithTraceRunnerStepChoiceCfg (.moveTemp tag) state input output []) =
      some (splitWithTraceRunnerStepChoiceCfg (.writeTag tag)
        (.output none) input output []) := by
  simp [splitWithTraceRunnerStepChoiceMachine, splitWithTraceRunnerStepChoiceCfg,
    splitWithTraceRunnerStepChoiceOutputState]
  congr

lemma splitWithTraceRunnerStepChoice_pushOutput_step
    (tag : Bool) (s : splitWithTraceRunnerStepChoiceOutputSymbol)
    (state : SplitWithTraceRunnerStepChoiceState)
    (input : List splitWithTraceRunnerStepChoiceInputSymbol)
    (output temp : List splitWithTraceRunnerStepChoiceOutputSymbol) :
    splitWithTraceRunnerStepChoiceMachine.step
        (splitWithTraceRunnerStepChoiceCfg (.pushOutput tag s) state input output temp) =
      some (splitWithTraceRunnerStepChoiceCfg (.moveTemp tag)
        state input (s :: output) temp) := by
  simp [splitWithTraceRunnerStepChoiceMachine, splitWithTraceRunnerStepChoiceCfg]
  congr
  funext k
  cases k <;> rfl

lemma splitWithTraceRunnerStepChoice_writeTag_step
    (tag : Bool) (output : List splitWithTraceRunnerStepChoiceOutputSymbol) :
    splitWithTraceRunnerStepChoiceMachine.step
        (splitWithTraceRunnerStepChoiceCfg (.writeTag tag) (.output none) [] output []) =
      some (splitWithTraceRunnerStepChoiceHalt (Sum.inl tag :: output)) := by
  simp [splitWithTraceRunnerStepChoiceMachine, splitWithTraceRunnerStepChoiceCfg,
    splitWithTraceRunnerStepChoiceHalt]
  congr
  funext k
  cases k <;> rfl

lemma splitWithTraceRunnerStepChoice_initList
    (input : List splitWithTraceRunnerStepChoiceInputSymbol) :
    Turing.initList splitWithTraceRunnerStepChoiceMachine input =
      splitWithTraceRunnerStepChoiceCfg .readAcc (.input none) input [] [] := by
  simp [splitWithTraceRunnerStepChoiceMachine, splitWithTraceRunnerStepChoiceCfg,
    Turing.initList]
  congr
  funext k
  cases k <;> rfl

lemma splitWithTraceRunnerStepChoice_haltList
    (output : List splitWithTraceRunnerStepChoiceOutputSymbol) :
    Turing.haltList splitWithTraceRunnerStepChoiceMachine output =
      splitWithTraceRunnerStepChoiceHalt output := by
  simp [splitWithTraceRunnerStepChoiceMachine, splitWithTraceRunnerStepChoiceHalt,
    Turing.haltList]
  congr
  funext k
  cases k <;> rfl

def splitWithTraceRunnerStepChoice_readAcc_run
    (acc : List splitWithTraceLoopAccEncodedType.Symbol)
    (state : SplitWithTraceRunnerStepChoiceState)
    (rest : List splitWithTraceRunnerStepChoiceInputSymbol)
    (output temp : List splitWithTraceRunnerStepChoiceOutputSymbol) :
    StateTransition.EvalsToInTime
      splitWithTraceRunnerStepChoiceMachine.step
      (splitWithTraceRunnerStepChoiceCfg .readAcc state
        (acc.map (fun s => some (Sum.inl s)) ++ none :: rest) output temp)
      (some (splitWithTraceRunnerStepChoiceCfg .readInstructionTag (.input (some none))
        rest output ((acc.map splitWithTraceRunnerStepChoiceAccSymbol).reverse ++ temp)))
      (2 * acc.length + 1) := by
  induction acc generalizing state temp with
  | nil =>
      simpa using
        TM2Programs.evalsToInTimeOne
          (splitWithTraceRunnerStepChoice_readAcc_step_delim state rest output temp)
  | cons s acc ih =>
      let mapped := splitWithTraceRunnerStepChoiceAccSymbol s
      let tm := splitWithTraceRunnerStepChoiceMachine
      let c₀ := splitWithTraceRunnerStepChoiceCfg .readAcc state
        (some (Sum.inl s) :: acc.map (fun s => some (Sum.inl s)) ++ none :: rest)
        output temp
      let c₁ := splitWithTraceRunnerStepChoiceCfg (.pushAccTemp mapped)
        (.input (some (some (Sum.inl s))))
        (acc.map (fun s => some (Sum.inl s)) ++ none :: rest) output temp
      let c₂ := splitWithTraceRunnerStepChoiceCfg .readAcc
        (.input (some (some (Sum.inl s))))
        (acc.map (fun s => some (Sum.inl s)) ++ none :: rest) output (mapped :: temp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        by
          simpa [tm, c₀, c₁, mapped] using
            TM2Programs.evalsToInTimeOne
              (splitWithTraceRunnerStepChoice_readAcc_step_cons s
                state
                (acc.map (fun s => some (Sum.inl s)) ++ none :: rest) output temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        by
          simpa [tm, c₁, c₂] using
            TM2Programs.evalsToInTimeOne
              (splitWithTraceRunnerStepChoice_pushAccTemp_step mapped
                (.input (some (some (Sum.inl s))))
                (acc.map (fun s => some (Sum.inl s)) ++ none :: rest) output temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (splitWithTraceRunnerStepChoiceCfg .readInstructionTag (.input (some none))
            rest output
            ((acc.map splitWithTraceRunnerStepChoiceAccSymbol).reverse ++
              (mapped :: temp))))
          (2 * acc.length + 1) :=
        ih (.input (some (some (Sum.inl s)))) (mapped :: temp)
      simpa [tm, c₀, c₁, c₂, mapped, List.map_cons, List.reverse_cons,
        List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * acc.length + 1)
          c₀ c₂
          (some (splitWithTraceRunnerStepChoiceCfg .readInstructionTag (.input (some none))
            rest output
            ((acc.map splitWithTraceRunnerStepChoiceAccSymbol).reverse ++ (mapped :: temp))))
          h₁₂ hTail

def splitWithTraceRunnerStepChoice_clearAcc_run
    (state : SplitWithTraceRunnerStepChoiceState)
    (input : List splitWithTraceRunnerStepChoiceInputSymbol)
    (output temp : List splitWithTraceRunnerStepChoiceOutputSymbol) :
    StateTransition.EvalsToInTime
      splitWithTraceRunnerStepChoiceMachine.step
      (splitWithTraceRunnerStepChoiceCfg .clearAcc state input output temp)
      (some (splitWithTraceRunnerStepChoiceCfg .readInputPayload (.output none)
        input output []))
      (temp.length + 1) := by
  induction temp generalizing state with
  | nil =>
      simpa using
        TM2Programs.evalsToInTimeOne
          (splitWithTraceRunnerStepChoice_clearAcc_step_nil state input output)
  | cons s temp ih =>
      let tm := splitWithTraceRunnerStepChoiceMachine
      let c₀ := splitWithTraceRunnerStepChoiceCfg .clearAcc state input output (s :: temp)
      let c₁ := splitWithTraceRunnerStepChoiceCfg .clearAcc (.output (some s))
        input output temp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne
          (splitWithTraceRunnerStepChoice_clearAcc_step_cons s state input output temp)
      have hTail : StateTransition.EvalsToInTime tm.step c₁
          (some (splitWithTraceRunnerStepChoiceCfg .readInputPayload (.output none)
            input output []))
          (temp.length + 1) :=
        ih (.output (some s))
      simpa [tm, c₀, c₁, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step 1 (temp.length + 1)
          c₀ c₁
          (some (splitWithTraceRunnerStepChoiceCfg .readInputPayload (.output none)
            input output []))
          h₁ hTail

def splitWithTraceRunnerStepChoice_readInputPayload_run
    (payload : List splitWithInputEncodedType.Symbol)
    (state : SplitWithTraceRunnerStepChoiceState)
    (output temp : List splitWithTraceRunnerStepChoiceOutputSymbol) :
    StateTransition.EvalsToInTime
      splitWithTraceRunnerStepChoiceMachine.step
      (splitWithTraceRunnerStepChoiceCfg .readInputPayload state
        (payload.map (fun s => some (Sum.inr (Sum.inr (Sum.inl s))))) output temp)
      (some (splitWithTraceRunnerStepChoiceCfg (.moveTemp false) (.input none)
        [] output
        ((payload.map splitWithTraceRunnerStepChoiceInputPayloadSymbol).reverse ++ temp)))
      (2 * payload.length + 1) := by
  induction payload generalizing state temp with
  | nil =>
      simpa using
        TM2Programs.evalsToInTimeOne
          (splitWithTraceRunnerStepChoice_readInputPayload_step_nil state output temp)
  | cons s payload ih =>
      let mapped := splitWithTraceRunnerStepChoiceInputPayloadSymbol s
      let tm := splitWithTraceRunnerStepChoiceMachine
      let c₀ := splitWithTraceRunnerStepChoiceCfg .readInputPayload state
        (some (Sum.inr (Sum.inr (Sum.inl s))) ::
          payload.map (fun s => some (Sum.inr (Sum.inr (Sum.inl s))))) output temp
      let c₁ := splitWithTraceRunnerStepChoiceCfg (.pushInputTemp mapped)
        (.input (some (some (Sum.inr (Sum.inr (Sum.inl s))))))
        (payload.map (fun s => some (Sum.inr (Sum.inr (Sum.inl s))))) output temp
      let c₂ := splitWithTraceRunnerStepChoiceCfg .readInputPayload
        (.input (some (some (Sum.inr (Sum.inr (Sum.inl s))))))
        (payload.map (fun s => some (Sum.inr (Sum.inr (Sum.inl s))))) output
        (mapped :: temp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne
          (splitWithTraceRunnerStepChoice_readInputPayload_step_cons s
            state
            (payload.map (fun s => some (Sum.inr (Sum.inr (Sum.inl s))))) output temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        TM2Programs.evalsToInTimeOne
          (splitWithTraceRunnerStepChoice_pushInputTemp_step mapped
            (.input (some (some (Sum.inr (Sum.inr (Sum.inl s))))))
            (payload.map (fun s => some (Sum.inr (Sum.inr (Sum.inl s))))) output temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (splitWithTraceRunnerStepChoiceCfg (.moveTemp false) (.input none)
            [] output
            ((payload.map splitWithTraceRunnerStepChoiceInputPayloadSymbol).reverse ++
              (mapped :: temp))))
          (2 * payload.length + 1) :=
        ih (.input (some (some (Sum.inr (Sum.inr (Sum.inl s)))))) (mapped :: temp)
      simpa [tm, c₀, c₁, c₂, mapped, List.map_cons, List.reverse_cons,
        List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * payload.length + 1)
          c₀ c₂
          (some (splitWithTraceRunnerStepChoiceCfg (.moveTemp false) (.input none)
            [] output
            ((payload.map splitWithTraceRunnerStepChoiceInputPayloadSymbol).reverse ++
              (mapped :: temp))))
          h₁₂ hTail

def splitWithTraceRunnerStepChoice_moveTemp_run
    (tag : Bool) (state : SplitWithTraceRunnerStepChoiceState)
    (input : List splitWithTraceRunnerStepChoiceInputSymbol)
    (output temp : List splitWithTraceRunnerStepChoiceOutputSymbol) :
    StateTransition.EvalsToInTime
      splitWithTraceRunnerStepChoiceMachine.step
      (splitWithTraceRunnerStepChoiceCfg (.moveTemp tag) state input output temp)
      (some (splitWithTraceRunnerStepChoiceCfg (.writeTag tag) (.output none)
        input (temp.reverse ++ output) []))
      (2 * temp.length + 1) := by
  induction temp generalizing state output with
  | nil =>
      simpa using
        TM2Programs.evalsToInTimeOne
          (splitWithTraceRunnerStepChoice_moveTemp_step_nil tag state input output)
  | cons s temp ih =>
      let tm := splitWithTraceRunnerStepChoiceMachine
      let c₀ := splitWithTraceRunnerStepChoiceCfg (.moveTemp tag) state input output (s :: temp)
      let c₁ := splitWithTraceRunnerStepChoiceCfg (.pushOutput tag s)
        (.output (some s)) input output temp
      let c₂ := splitWithTraceRunnerStepChoiceCfg (.moveTemp tag)
        (.output (some s)) input (s :: output) temp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne
          (splitWithTraceRunnerStepChoice_moveTemp_step_cons tag s state input output temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        TM2Programs.evalsToInTimeOne
          (splitWithTraceRunnerStepChoice_pushOutput_step tag s
            (.output (some s)) input output temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (splitWithTraceRunnerStepChoiceCfg (.writeTag tag) (.output none)
            input (temp.reverse ++ (s :: output)) []))
          (2 * temp.length + 1) :=
        ih (.output (some s)) (s :: output)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * temp.length + 1)
          c₀ c₂
          (some (splitWithTraceRunnerStepChoiceCfg (.writeTag tag) (.output none)
            input (temp.reverse ++ (s :: output)) []))
          h₁₂ hTail

def splitWithTraceRunnerStepChoiceLeftInputStack
    (acc : List splitWithTraceLoopAccEncodedType.Symbol)
    (payload : List splitWithInputEncodedType.Symbol) :
    List splitWithTraceRunnerStepChoiceInputSymbol :=
  List.append
    (acc.map splitWithTraceRunnerStepChoiceAccInputSymbol)
    ((none : splitWithTraceRunnerStepChoiceInputSymbol) ::
      splitWithTraceRunnerStepChoiceInstructionTagInputSymbol false ::
        payload.map splitWithTraceRunnerStepChoiceInputPayloadInputSymbol)

def splitWithTraceRunnerStepChoiceRightInputStack
    (acc : List splitWithTraceLoopAccEncodedType.Symbol) :
    List splitWithTraceRunnerStepChoiceInputSymbol :=
  List.append
    (acc.map splitWithTraceRunnerStepChoiceAccInputSymbol)
    [(none : splitWithTraceRunnerStepChoiceInputSymbol),
      splitWithTraceRunnerStepChoiceInstructionTagInputSymbol true]

def splitWithTraceRunnerStepChoice_outputs_left
    (acc : List splitWithTraceLoopAccEncodedType.Symbol)
    (payload : List splitWithInputEncodedType.Symbol) :
    Turing.TM2OutputsInTime
      splitWithTraceRunnerStepChoiceMachine
      (splitWithTraceRunnerStepChoiceLeftInputStack acc payload)
      (some (Sum.inl false ::
        payload.map splitWithTraceRunnerStepChoiceInputPayloadSymbol))
      (4 * (splitWithTraceRunnerStepChoiceLeftInputStack acc payload).length + 8) := by
  let tm := splitWithTraceRunnerStepChoiceMachine
  let accMapped := acc.map splitWithTraceRunnerStepChoiceAccSymbol
  let payloadInput :=
    payload.map splitWithTraceRunnerStepChoiceInputPayloadInputSymbol
  let payloadMapped := payload.map splitWithTraceRunnerStepChoiceInputPayloadSymbol
  let rest : List splitWithTraceRunnerStepChoiceInputSymbol :=
    splitWithTraceRunnerStepChoiceInstructionTagInputSymbol false :: payloadInput
  let input := splitWithTraceRunnerStepChoiceLeftInputStack acc payload
  let cTag := splitWithTraceRunnerStepChoiceCfg .readInstructionTag (.input (some none))
    rest [] accMapped.reverse
  let cClear := splitWithTraceRunnerStepChoiceCfg .clearAcc
    (.input (some (some (Sum.inr (Sum.inl false))))) payloadInput [] accMapped.reverse
  let cPayload := splitWithTraceRunnerStepChoiceCfg .readInputPayload (.output none)
    payloadInput [] []
  let cMove := splitWithTraceRunnerStepChoiceCfg (.moveTemp false) (.input none)
    [] [] payloadMapped.reverse
  let cWrite := splitWithTraceRunnerStepChoiceCfg (.writeTag false) (.output none)
    [] payloadMapped []
  let done := splitWithTraceRunnerStepChoiceHalt (Sum.inl false :: payloadMapped)
  have hRead : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some cTag) (2 * acc.length + 1) := by
    simpa [tm, input, rest, cTag, accMapped,
      splitWithTraceRunnerStepChoiceAccInputSymbol,
      splitWithTraceRunnerStepChoiceInstructionTagInputSymbol,
      splitWithTraceRunnerStepChoiceLeftInputStack,
      splitWithTraceRunnerStepChoice_initList] using
      splitWithTraceRunnerStepChoice_readAcc_run acc (.input none) rest [] []
  have hTag : StateTransition.EvalsToInTime tm.step cTag (some cClear) 1 := by
    simpa [tm, cTag, cClear, rest, payloadInput, accMapped,
      splitWithTraceRunnerStepChoiceInstructionTagInputSymbol] using
      TM2Programs.evalsToInTimeOne
        (splitWithTraceRunnerStepChoice_readInstructionTag_step_left
          payloadInput [] accMapped.reverse)
  have hClear : StateTransition.EvalsToInTime tm.step cClear (some cPayload)
      (accMapped.reverse.length + 1) := by
    simpa [tm, cClear, cPayload] using
      splitWithTraceRunnerStepChoice_clearAcc_run
        (.input (some (some (Sum.inr (Sum.inl false))))) payloadInput [] accMapped.reverse
  have hPayload : StateTransition.EvalsToInTime tm.step cPayload (some cMove)
      (2 * payload.length + 1) := by
    simpa [tm, cPayload, cMove, payloadInput, payloadMapped,
      splitWithTraceRunnerStepChoiceInputPayloadInputSymbol] using
      splitWithTraceRunnerStepChoice_readInputPayload_run payload (.output none) [] []
  have hMove : StateTransition.EvalsToInTime tm.step cMove (some cWrite)
      (2 * payloadMapped.reverse.length + 1) := by
    simpa [tm, cMove, cWrite, payloadMapped, List.reverse_reverse] using
      splitWithTraceRunnerStepChoice_moveTemp_run false (.input none) [] []
        payloadMapped.reverse
  have hWrite : StateTransition.EvalsToInTime tm.step cWrite (some done) 1 := by
    simpa [tm, cWrite, done, payloadMapped] using
      TM2Programs.evalsToInTimeOne
        (splitWithTraceRunnerStepChoice_writeTag_step false payloadMapped)
  have hReadTag : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some cClear) (1 + (2 * acc.length + 1)) :=
    StateTransition.EvalsToInTime.trans tm.step (2 * acc.length + 1) 1
      (Turing.initList tm input) cTag (some cClear) hRead hTag
  have hToPayload : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some cPayload)
      ((accMapped.reverse.length + 1) + (1 + (2 * acc.length + 1))) :=
    StateTransition.EvalsToInTime.trans tm.step (1 + (2 * acc.length + 1))
      (accMapped.reverse.length + 1)
      (Turing.initList tm input) cClear (some cPayload) hReadTag hClear
  have hToMove : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some cMove)
      ((2 * payload.length + 1) +
        ((accMapped.reverse.length + 1) + (1 + (2 * acc.length + 1)))) :=
    StateTransition.EvalsToInTime.trans tm.step
      ((accMapped.reverse.length + 1) + (1 + (2 * acc.length + 1)))
      (2 * payload.length + 1)
      (Turing.initList tm input) cPayload (some cMove) hToPayload hPayload
  have hToWrite : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some cWrite)
      ((2 * payloadMapped.reverse.length + 1) +
        ((2 * payload.length + 1) +
          ((accMapped.reverse.length + 1) + (1 + (2 * acc.length + 1))))) :=
    StateTransition.EvalsToInTime.trans tm.step
      ((2 * payload.length + 1) +
        ((accMapped.reverse.length + 1) + (1 + (2 * acc.length + 1))))
      (2 * payloadMapped.reverse.length + 1)
      (Turing.initList tm input) cMove (some cWrite) hToMove hMove
  have hAll : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some done)
      (1 +
        ((2 * payloadMapped.reverse.length + 1) +
          ((2 * payload.length + 1) +
            ((accMapped.reverse.length + 1) + (1 + (2 * acc.length + 1)))))) :=
    StateTransition.EvalsToInTime.trans tm.step
      ((2 * payloadMapped.reverse.length + 1) +
        ((2 * payload.length + 1) +
          ((accMapped.reverse.length + 1) + (1 + (2 * acc.length + 1)))))
      1
      (Turing.initList tm input) cWrite (some done) hToWrite hWrite
  change StateTransition.EvalsToInTime tm.step
    (Turing.initList tm input)
    (some (Turing.haltList tm (Sum.inl false :: payloadMapped)))
    (4 * input.length + 8)
  exact
    TM2Programs.evalsToInTime_mono
      (by simpa [tm, done, splitWithTraceRunnerStepChoice_haltList] using hAll)
      (by
        simp [input, accMapped, payloadMapped,
          splitWithTraceRunnerStepChoiceLeftInputStack,
          splitWithTraceRunnerStepChoiceInstructionTagInputSymbol]
        omega)

def splitWithTraceRunnerStepChoice_outputs_right
    (acc : List splitWithTraceLoopAccEncodedType.Symbol) :
    Turing.TM2OutputsInTime
      splitWithTraceRunnerStepChoiceMachine
      (splitWithTraceRunnerStepChoiceRightInputStack acc)
      (some (Sum.inl true ::
        acc.map splitWithTraceRunnerStepChoiceAccSymbol))
      (4 * (splitWithTraceRunnerStepChoiceRightInputStack acc).length + 8) := by
  let tm := splitWithTraceRunnerStepChoiceMachine
  let accMapped := acc.map splitWithTraceRunnerStepChoiceAccSymbol
  let rest : List splitWithTraceRunnerStepChoiceInputSymbol :=
    [splitWithTraceRunnerStepChoiceInstructionTagInputSymbol true]
  let input := splitWithTraceRunnerStepChoiceRightInputStack acc
  let cTag := splitWithTraceRunnerStepChoiceCfg .readInstructionTag (.input (some none))
    rest [] accMapped.reverse
  let cMove := splitWithTraceRunnerStepChoiceCfg (.moveTemp true)
    (.input (some (some (Sum.inr (Sum.inl true))))) [] [] accMapped.reverse
  let cWrite := splitWithTraceRunnerStepChoiceCfg (.writeTag true) (.output none)
    [] accMapped []
  let done := splitWithTraceRunnerStepChoiceHalt (Sum.inl true :: accMapped)
  have hRead : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some cTag) (2 * acc.length + 1) := by
    simpa [tm, input, rest, cTag, accMapped,
      splitWithTraceRunnerStepChoiceAccInputSymbol,
      splitWithTraceRunnerStepChoiceInstructionTagInputSymbol,
      splitWithTraceRunnerStepChoiceRightInputStack,
      splitWithTraceRunnerStepChoice_initList] using
      splitWithTraceRunnerStepChoice_readAcc_run acc (.input none) rest [] []
  have hTag : StateTransition.EvalsToInTime tm.step cTag (some cMove) 1 := by
    simpa [tm, cTag, cMove, rest, accMapped,
      splitWithTraceRunnerStepChoiceInstructionTagInputSymbol] using
      TM2Programs.evalsToInTimeOne
        (splitWithTraceRunnerStepChoice_readInstructionTag_step_right [] [] accMapped.reverse)
  have hMove : StateTransition.EvalsToInTime tm.step cMove (some cWrite)
      (2 * accMapped.reverse.length + 1) := by
    simpa [tm, cMove, cWrite, accMapped, List.reverse_reverse] using
      splitWithTraceRunnerStepChoice_moveTemp_run true
        (.input (some (some (Sum.inr (Sum.inl true))))) [] [] accMapped.reverse
  have hWrite : StateTransition.EvalsToInTime tm.step cWrite (some done) 1 := by
    simpa [tm, cWrite, done, accMapped] using
      TM2Programs.evalsToInTimeOne
        (splitWithTraceRunnerStepChoice_writeTag_step true accMapped)
  have hReadTag : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some cMove) (1 + (2 * acc.length + 1)) :=
    StateTransition.EvalsToInTime.trans tm.step (2 * acc.length + 1) 1
      (Turing.initList tm input) cTag (some cMove) hRead hTag
  have hToWrite : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some cWrite)
      ((2 * accMapped.reverse.length + 1) + (1 + (2 * acc.length + 1))) :=
    StateTransition.EvalsToInTime.trans tm.step (1 + (2 * acc.length + 1))
      (2 * accMapped.reverse.length + 1)
      (Turing.initList tm input) cMove (some cWrite) hReadTag hMove
  have hAll : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some done)
      (1 + ((2 * accMapped.reverse.length + 1) + (1 + (2 * acc.length + 1)))) :=
    StateTransition.EvalsToInTime.trans tm.step
      ((2 * accMapped.reverse.length + 1) + (1 + (2 * acc.length + 1))) 1
      (Turing.initList tm input) cWrite (some done) hToWrite hWrite
  change StateTransition.EvalsToInTime tm.step
    (Turing.initList tm input)
    (some (Turing.haltList tm (Sum.inl true :: accMapped)))
    (4 * input.length + 8)
  exact
    TM2Programs.evalsToInTime_mono
      (by simpa [tm, done, splitWithTraceRunnerStepChoice_haltList] using hAll)
      (by
        simp [input, accMapped,
          splitWithTraceRunnerStepChoiceRightInputStack,
          splitWithTraceRunnerStepChoiceInstructionTagInputSymbol]
        omega)

theorem splitWithTraceRunnerStepChoice_inputSize_le
    (p : splitWithTraceLoopAccEncodedType.Carrier ×
      splitWithTraceRunnerInstructionEncodedType.Carrier) :
    splitWithTraceRunnerStepChoiceEncodedType.inputSize
        (splitWithTraceRunnerStepChoice p) ≤
      (EncodedType.prod
        splitWithTraceLoopAccEncodedType
        splitWithTraceRunnerInstructionEncodedType).inputSize p := by
  rcases p with ⟨acc, instr⟩
  cases instr with
  | inl input =>
      simp [splitWithTraceRunnerStepChoice, splitWithTraceRunnerStepChoiceEncodedType,
        splitWithTraceRunnerInstructionEncodedType, splitWithTraceRunnerFuelEncodedType,
        EncodedType.inputSize, EncodedType.prod, EncodedType.sum]
      omega
  | inr fuel =>
      cases fuel
      simp [splitWithTraceRunnerStepChoice, splitWithTraceRunnerStepChoiceEncodedType,
        splitWithTraceRunnerInstructionEncodedType, splitWithTraceRunnerFuelEncodedType,
        EncodedType.inputSize, EncodedType.prod, EncodedType.sum, EncodedType.raw]

end Karp21
end ComplexityReduction
