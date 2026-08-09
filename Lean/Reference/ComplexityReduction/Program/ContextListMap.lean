/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.InvariantFold
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.Sum
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatRange

/-!
Executable attachment of one retained context to every element of an ordered
list.

This is a generic direct-TM combinator, not a domain route.  The unloaded
sum accumulator avoids inventing a default value for the context carrier:
only a leading context instruction enables later element instructions.
-/

namespace ComplexityReduction
namespace Program

open ComplexityReduction

/-- The unloaded-or-context-and-output fold state. -/
def contextListMapAccumulatorEncodedType (C X : EncodedType) : EncodedType :=
  EncodedType.sum (EncodedType.raw Unit)
    (EncodedType.prod C (EncodedType.list (EncodedType.prod C X)))

/-- A stream starts with one context instruction and continues with elements. -/
def contextListMapInstructionEncodedType (C X : EncodedType) : EncodedType :=
  EncodedType.sum C X

/-- Exact encoding of a context-list-map instruction stream. -/
def contextListMapInstructionListEncodedType (C X : EncodedType) : EncodedType :=
  EncodedType.list (contextListMapInstructionEncodedType C X)

/-- The fixed unloaded initial fold state. -/
def contextListMapInitialAccumulator (C X : EncodedType) :
    (contextListMapAccumulatorEncodedType C X).Carrier :=
  Sum.inl ()

/-- Load a context, or append a context-indexed element once it is loaded. -/
def contextListMapStep {C X : EncodedType}
    (argument :
      (contextListMapAccumulatorEncodedType C X).Carrier ×
        (contextListMapInstructionEncodedType C X).Carrier) :
    (contextListMapAccumulatorEncodedType C X).Carrier :=
  match argument.2 with
  | Sum.inl context => Sum.inr (context, [])
  | Sum.inr element =>
      match argument.1 with
      | Sum.inl _ => Sum.inl ()
      | Sum.inr loaded =>
          Sum.inr (loaded.1,
            (show List (EncodedType.prod C X).Carrier from loaded.2) ++
              [show (EncodedType.prod C X).Carrier from (loaded.1, element)])

/-- Read the emitted list, treating an unloaded stream as the empty list. -/
def contextListMapOutput {C X : EncodedType}
    (accumulator : (contextListMapAccumulatorEncodedType C X).Carrier) :
    List (EncodedType.prod C X).Carrier :=
  match accumulator with
  | Sum.inl _ => []
  | Sum.inr loaded => loaded.2

/-- Reify one context and an element list as a checked instruction stream. -/
def contextListMapInstructions {C X : EncodedType}
    (context : C.Carrier) (elements : List X.Carrier) :
    List (contextListMapInstructionEncodedType C X).Carrier :=
  Sum.inl context :: elements.map Sum.inr

/-- The executable context attachment map. -/
def contextListMapExecutable {C X : EncodedType}
    (argument : C.Carrier × List X.Carrier) :
    List (EncodedType.prod C X).Carrier :=
  contextListMapOutput
    ((contextListMapInstructions argument.1 argument.2).foldl
      (fun accumulator instruction => contextListMapStep (accumulator, instruction))
      (contextListMapInitialAccumulator C X))

/-! ### Exact stream semantics -/

theorem contextListMapRightInstructions_eq {C X : EncodedType}
    (context : C.Carrier) (elements : List X.Carrier)
    (output : List (EncodedType.prod C X).Carrier) :
    (elements.map Sum.inr).foldl
        (fun accumulator instruction => contextListMapStep (accumulator, instruction))
        (Sum.inr (context, output) :
          (contextListMapAccumulatorEncodedType C X).Carrier) =
      Sum.inr (context,
        output ++ elements.map
          (fun element => show (EncodedType.prod C X).Carrier from (context, element))) := by
  induction elements generalizing output with
  | nil =>
      simpa using
        (show
          (Sum.inr (context, output) :
            (contextListMapAccumulatorEncodedType C X).Carrier) =
              Sum.inr (context, output) from rfl)
  | cons element elements inductionHypothesis =>
      simp only [List.map_cons]
      simpa [contextListMapStep, List.append_assoc] using
        inductionHypothesis
          (output ++ [show (EncodedType.prod C X).Carrier from (context, element)])

theorem contextListMapExecutable_eq_map {C X : EncodedType}
    (context : C.Carrier) (elements : List X.Carrier) :
    contextListMapExecutable (context, elements) =
      elements.map (fun element =>
        show (EncodedType.prod C X).Carrier from (context, element)) := by
  unfold contextListMapExecutable contextListMapInstructions
  simp only [List.foldl_cons]
  change contextListMapOutput
      ((elements.map Sum.inr).foldl
        (fun accumulator instruction => contextListMapStep (accumulator, instruction))
        (Sum.inr (context, []) : (contextListMapAccumulatorEncodedType C X).Carrier)) = _
  rw [contextListMapRightInstructions_eq]
  rfl

/-! ### Direct-TM building blocks -/

theorem contextListMapStep_tmPolyTime {C X : EncodedType} :
    TMPolyTimeMap
      (EncodedType.prod (contextListMapAccumulatorEncodedType C X)
        (contextListMapInstructionEncodedType C X))
      (contextListMapAccumulatorEncodedType C X)
      contextListMapStep := by
  let Acc := contextListMapAccumulatorEncodedType C X
  let Instr := contextListMapInstructionEncodedType C X
  let Pair := EncodedType.prod C X
  let Output := EncodedType.list Pair
  let Loaded := EncodedType.prod C Output
  have leftBranch :
      TMPolyTimeMap C Acc (fun context : C.Carrier => Sum.inr (context, [])) := by
    have empty : TMPolyTimeMap C Output
        (fun _ : C.Carrier => ([] : List Pair.Carrier)) :=
      TMPolyTimeMap.const C Output []
    have paired : TMPolyTimeMap C Loaded
        (fun context : C.Carrier => (context, ([] : List Pair.Carrier))) :=
      TMPolyTimeMap.prod_mk (TMPolyTimeMap.id C) empty
    have injected := TMPolyTimeMap.inr (EncodedType.raw Unit) Loaded
    have composed := TMPolyTimeMap.comp injected paired
    simpa [Acc, Loaded, Output, Pair, contextListMapAccumulatorEncodedType,
      Function.comp] using composed
  have rightBranch :
      TMPolyTimeMap (EncodedType.prod Acc X) Acc
        (fun argument : Acc.Carrier × X.Carrier =>
          match argument.1 with
          | Sum.inl _ => Sum.inl ()
          | Sum.inr loaded =>
              Sum.inr (loaded.1,
                (show List Pair.Carrier from loaded.2) ++
                  [show Pair.Carrier from (loaded.1, argument.2)])) := by
    let Q := EncodedType.prod Acc X
    have element : TMPolyTimeMap Q X (fun argument : Q.Carrier => argument.2) := by
      simpa [Q] using TMPolyTimeMap.snd Acc X
    have accumulator : TMPolyTimeMap Q Acc (fun argument : Q.Carrier => argument.1) := by
      simpa [Q] using TMPolyTimeMap.fst Acc X
    have swapped : TMPolyTimeMap Q (EncodedType.prod X Acc)
        (fun argument : Q.Carrier => (argument.2, argument.1)) :=
      TMPolyTimeMap.prod_mk element accumulator
    have dispatch := prodSumChoice_tm_polytime X (EncodedType.raw Unit) Loaded
    have unloaded : TMPolyTimeMap (EncodedType.raw Unit) Acc
        (fun _ : Unit => Sum.inl ()) := by
      simpa [Acc, contextListMapAccumulatorEncodedType] using
        TMPolyTimeMap.inl (EncodedType.raw Unit) Loaded
    have loaded : TMPolyTimeMap (EncodedType.prod X Loaded) Acc
        (fun argument : X.Carrier × Loaded.Carrier =>
          Sum.inr (argument.2.1,
            (show List Pair.Carrier from argument.2.2) ++
              [show Pair.Carrier from (argument.2.1, argument.1)])) := by
      let R := EncodedType.prod X Loaded
      have element : TMPolyTimeMap R X (fun argument : R.Carrier => argument.1) := by
        simpa [R] using TMPolyTimeMap.fst X Loaded
      have loadedInput : TMPolyTimeMap R Loaded
          (fun argument : R.Carrier => argument.2) := by
        simpa [R] using TMPolyTimeMap.snd X Loaded
      have context : TMPolyTimeMap R C (fun argument : R.Carrier => argument.2.1) := by
        have projected := TMPolyTimeMap.fst C Output
        have composed := TMPolyTimeMap.comp projected loadedInput
        simpa [Function.comp, R, Loaded] using composed
      have output : TMPolyTimeMap R Output (fun argument : R.Carrier => argument.2.2) := by
        have projected := TMPolyTimeMap.snd C Output
        have composed := TMPolyTimeMap.comp projected loadedInput
        simpa [Function.comp, R, Loaded] using composed
      have pairInput : TMPolyTimeMap R Pair
          (fun argument : R.Carrier => (argument.2.1, argument.1)) :=
        TMPolyTimeMap.prod_mk context element
      have singleton : TMPolyTimeMap R Output
          (fun argument : R.Carrier => [(argument.2.1, argument.1)]) := by
        have composed := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton Pair) pairInput
        simpa [Function.comp, Output] using composed
      have appendInput : TMPolyTimeMap R (EncodedType.prod Output Output)
          (fun argument : R.Carrier =>
            (argument.2.2, [(argument.2.1, argument.1)])) :=
        TMPolyTimeMap.prod_mk output singleton
      have appended : TMPolyTimeMap R Output
          (fun argument : R.Carrier =>
            (show List Pair.Carrier from argument.2.2) ++
              [show Pair.Carrier from (argument.2.1, argument.1)]) := by
        have composed := TMPolyTimeMap.comp (TMPolyTimeMap.list_append Pair) appendInput
        simpa [Function.comp, Output] using composed
      have paired : TMPolyTimeMap R Loaded
          (fun argument : R.Carrier =>
            (argument.2.1,
              (show List Pair.Carrier from argument.2.2) ++
                [show Pair.Carrier from (argument.2.1, argument.1)])) :=
        TMPolyTimeMap.prod_mk context appended
      have injected := TMPolyTimeMap.inr (EncodedType.raw Unit) Loaded
      have composed := TMPolyTimeMap.comp injected paired
      simpa [Function.comp, Acc, Loaded, Output, Pair,
        contextListMapAccumulatorEncodedType, R] using composed
    have branches := TMPolyTimeMap.sum_elim unloaded loaded
    have dispatched := TMPolyTimeMap.comp branches dispatch
    have composed := TMPolyTimeMap.comp dispatched swapped
    convert composed using 1
    funext argument
    rcases argument with ⟨accumulator, element⟩
    cases accumulator <;> rfl
  have dispatch := prodSumChoice_tm_polytime Acc C X
  have branches := TMPolyTimeMap.sum_elim leftBranch rightBranch
  have composed := TMPolyTimeMap.comp branches dispatch
  convert composed using 1
  funext argument
  rcases argument with ⟨accumulator, instruction⟩
  cases instruction <;> rfl

theorem contextListMapOutput_tmPolyTime (C X : EncodedType) :
    TMPolyTimeMap (contextListMapAccumulatorEncodedType C X)
      (EncodedType.list (EncodedType.prod C X))
      contextListMapOutput := by
  let Acc := contextListMapAccumulatorEncodedType C X
  let Output := EncodedType.list (EncodedType.prod C X)
  let Loaded := EncodedType.prod C Output
  have unloaded : TMPolyTimeMap (EncodedType.raw Unit) Output
      (fun _ : Unit => ([] : List (EncodedType.prod C X).Carrier)) :=
    TMPolyTimeMap.const (EncodedType.raw Unit) Output []
  have loaded : TMPolyTimeMap Loaded Output
      (fun value : Loaded.Carrier => value.2) := by
    simpa [Loaded] using TMPolyTimeMap.snd C Output
  have branches := TMPolyTimeMap.sum_elim unloaded loaded
  convert branches using 1
  funext accumulator
  cases accumulator <;> rfl

theorem contextListMapInstructions_tmPolyTime (C X : EncodedType) :
    TMPolyTimeMap (EncodedType.prod C (EncodedType.list X))
      (contextListMapInstructionListEncodedType C X)
      (fun argument : C.Carrier × List X.Carrier =>
        contextListMapInstructions argument.1 argument.2) := by
  let Input := EncodedType.prod C (EncodedType.list X)
  let Instr := contextListMapInstructionEncodedType C X
  let Instrs := contextListMapInstructionListEncodedType C X
  have context : TMPolyTimeMap Input C (fun argument : Input.Carrier => argument.1) := by
    simpa [Input] using TMPolyTimeMap.fst C (EncodedType.list X)
  have elements : TMPolyTimeMap Input (EncodedType.list X)
      (fun argument : Input.Carrier => argument.2) := by
    simpa [Input] using TMPolyTimeMap.snd C (EncodedType.list X)
  have head : TMPolyTimeMap Input Instr
      (fun argument : Input.Carrier => Sum.inl argument.1) := by
    have composed := TMPolyTimeMap.comp (TMPolyTimeMap.inl C X) context
    simpa [Function.comp, Instr, contextListMapInstructionEncodedType] using composed
  have rightInstruction : TMPolyTimeMap X Instr (fun element : X.Carrier => Sum.inr element) := by
    simpa [Instr, contextListMapInstructionEncodedType] using TMPolyTimeMap.inr C X
  have tail : TMPolyTimeMap Input Instrs
      (fun argument : Input.Carrier => argument.2.map Sum.inr) := by
    have mapped := TMPolyTimeMap.list_map rightInstruction
    have composed := TMPolyTimeMap.comp mapped elements
    simpa [Function.comp, Instrs, contextListMapInstructionListEncodedType] using composed
  have consInput : TMPolyTimeMap Input (EncodedType.prod Instr Instrs)
      (fun argument : Input.Carrier =>
        (Sum.inl argument.1, argument.2.map Sum.inr)) :=
    TMPolyTimeMap.prod_mk head tail
  have composed := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons Instr) consInput
  simpa [Function.comp, contextListMapInstructions, Instrs,
    contextListMapInstructionListEncodedType] using composed

/-! ### Bounded fold compilation -/

/-- The retained context is always bounded by the instruction-stream input. -/
def ContextListMapFoldInvariant (C X : EncodedType) (N : Nat)
    (accumulator : (contextListMapAccumulatorEncodedType C X).Carrier) : Prop :=
  match accumulator with
  | Sum.inl _ => True
  | Sum.inr loaded => C.inputSize loaded.1 ≤ N

noncomputable def contextListMapFoldBase : Polynomial Nat := Polynomial.C 4

noncomputable def contextListMapFoldGrow : Polynomial Nat :=
  Polynomial.C 10 * Polynomial.X + Polynomial.C 10

@[simp] theorem contextListMapFoldGrow_eval (N : Nat) :
    contextListMapFoldGrow.eval N = 10 * N + 10 := by
  simp [contextListMapFoldGrow, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

private theorem contextListMapAccumulator_inputSize_inr (C X : EncodedType)
    (context : C.Carrier) (output : List (EncodedType.prod C X).Carrier) :
    (contextListMapAccumulatorEncodedType C X).inputSize
        (Sum.inr (context, output) :
          (contextListMapAccumulatorEncodedType C X).Carrier) =
      C.inputSize context +
        (EncodedType.list (EncodedType.prod C X)).inputSize output + 2 := by
  simp [contextListMapAccumulatorEncodedType, EncodedType.inputSize,
    EncodedType.sum, EncodedType.prod]
  omega

theorem contextListMapInitialAccumulator_bound (C X : EncodedType)
    (source : List (contextListMapInstructionEncodedType C X).Carrier) :
    ContextListMapFoldInvariant C X
        ((contextListMapInstructionListEncodedType C X).inputSize source)
        (contextListMapInitialAccumulator C X) ∧
      (contextListMapAccumulatorEncodedType C X).inputSize
          (contextListMapInitialAccumulator C X) ≤
        contextListMapFoldBase.eval
          ((contextListMapInstructionListEncodedType C X).inputSize source) := by
  constructor
  · simp [ContextListMapFoldInvariant, contextListMapInitialAccumulator]
  · simp [contextListMapInitialAccumulator, contextListMapAccumulatorEncodedType,
      contextListMapFoldBase, EncodedType.inputSize, EncodedType.sum,
      EncodedType.raw]

theorem contextListMapStep_growth {C X : EncodedType}
    (source : List (contextListMapInstructionEncodedType C X).Carrier)
    (accumulator : (contextListMapAccumulatorEncodedType C X).Carrier)
    (instruction : (contextListMapInstructionEncodedType C X).Carrier)
    (invariant : ContextListMapFoldInvariant C X
      ((contextListMapInstructionListEncodedType C X).inputSize source) accumulator)
    (instructionBound : (contextListMapInstructionEncodedType C X).inputSize instruction ≤
      (contextListMapInstructionListEncodedType C X).inputSize source) :
    ContextListMapFoldInvariant C X
        ((contextListMapInstructionListEncodedType C X).inputSize source)
        (contextListMapStep (accumulator, instruction)) ∧
      (contextListMapAccumulatorEncodedType C X).inputSize
          (contextListMapStep (accumulator, instruction)) ≤
        (contextListMapAccumulatorEncodedType C X).inputSize accumulator +
          contextListMapFoldGrow.eval
            ((contextListMapInstructionListEncodedType C X).inputSize source) := by
  let N := (contextListMapInstructionListEncodedType C X).inputSize source
  let Acc := contextListMapAccumulatorEncodedType C X
  let Instr := contextListMapInstructionEncodedType C X
  let Pair := EncodedType.prod C X
  let Output := EncodedType.list Pair
  cases instruction with
  | inl context =>
      have contextBound : C.inputSize context ≤ N := by
        exact Nat.le_of_lt (by
          simpa [N, Instr, contextListMapInstructionEncodedType,
            EncodedType.inputSize, EncodedType.sum] using instructionBound)
      constructor
      · simpa [ContextListMapFoldInvariant, contextListMapStep, N, Acc,
          contextListMapAccumulatorEncodedType] using contextBound
      · have produced : Acc.inputSize
            (Sum.inr (context, ([] : List Pair.Carrier)) : Acc.Carrier) ≤ N + 2 := by
            dsimp only [Acc]
            rw [contextListMapAccumulator_inputSize_inr]
            rw [EncodedType.inputSize_list_nil]
            omega
        rw [contextListMapFoldGrow_eval]
        have increase : N + 2 ≤ Acc.inputSize accumulator + (10 * N + 10) := by
          have nonnegative : 0 ≤ Acc.inputSize accumulator := Nat.zero_le _
          omega
        simpa [contextListMapStep, N, Acc, Pair] using produced.trans increase
  | inr element =>
      have elementBound : X.inputSize element ≤ N := by
        exact Nat.le_of_lt (by
          simpa [N, Instr, contextListMapInstructionEncodedType,
            EncodedType.inputSize, EncodedType.sum] using instructionBound)
      cases accumulator with
      | inl unloaded =>
          constructor
          · simp [ContextListMapFoldInvariant, contextListMapStep]
          · simp [contextListMapStep]
            exact Nat.le_add_right _ _
      | inr loaded =>
          rcases loaded with ⟨context, output⟩
          have contextBound : C.inputSize context ≤ N := by
            simpa [ContextListMapFoldInvariant, N, Acc,
              contextListMapAccumulatorEncodedType] using invariant
          have appended : Output.inputSize
              ((show List Pair.Carrier from output) ++
                [show Pair.Carrier from (context, element)]) =
              Output.inputSize output + Pair.inputSize (context, element) + 1 := by
            simpa [Output, Pair] using
              list_inputSize_append Pair (show List Pair.Carrier from output)
                [show Pair.Carrier from (context, element)]
          constructor
          · simpa [ContextListMapFoldInvariant, contextListMapStep, N, Acc,
              contextListMapAccumulatorEncodedType] using contextBound
          · rw [contextListMapFoldGrow_eval]
            have pairBound : Pair.inputSize (context, element) ≤ 2 * N + 1 := by
              simp [Pair, EncodedType.inputSize_prod] at contextBound elementBound ⊢
              omega
            have increment : Pair.inputSize (context, element) + 1 ≤ 10 * N + 10 := by
              omega
            have accumulatorSize : Acc.inputSize
                (Sum.inr (context,
                  (show List Pair.Carrier from output) ++
                    [show Pair.Carrier from (context, element)]) : Acc.Carrier) =
                Acc.inputSize (Sum.inr (context, output) : Acc.Carrier) +
                  Pair.inputSize (context, element) + 1 := by
              dsimp only [Acc]
              rw [contextListMapAccumulator_inputSize_inr,
                contextListMapAccumulator_inputSize_inr, appended]
              dsimp only [Output, Pair] at appended ⊢
              omega
            change Acc.inputSize
                (Sum.inr (context,
                  (show List Pair.Carrier from output) ++
                    [show Pair.Carrier from (context, element)]) : Acc.Carrier) ≤
              Acc.inputSize (Sum.inr (context, output) : Acc.Carrier) + (10 * N + 10)
            rw [accumulatorSize]
            omega

theorem contextListMapFold_tmPolyTime (C X : EncodedType) :
    TMPolyTimeMap
      (contextListMapInstructionListEncodedType C X)
      (contextListMapAccumulatorEncodedType C X)
      (fun instructions : List (contextListMapInstructionEncodedType C X).Carrier =>
        instructions.foldl
          (fun accumulator instruction => contextListMapStep (accumulator, instruction))
          (contextListMapInitialAccumulator C X)) := by
  rcases contextListMapStep_tmPolyTime (C := C) (X := X) with ⟨stepTM⟩
  refine TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
    (contextListMapInstructionEncodedType C X)
    (contextListMapAccumulatorEncodedType C X)
    contextListMapStep (contextListMapInitialAccumulator C X)
    stepTM contextListMapFoldBase contextListMapFoldGrow
    (ContextListMapFoldInvariant C X) ?_ ?_
  · intro source
    exact contextListMapInitialAccumulator_bound C X source
  · intro source accumulator instruction invariant instructionBound
    exact contextListMapStep_growth source accumulator instruction invariant instructionBound

/-- Direct-TM realization of attaching one context to every list element. -/
theorem contextListMapExecutable_tmPolyTime (C X : EncodedType) :
    TMPolyTimeMap (EncodedType.prod C (EncodedType.list X))
      (EncodedType.list (EncodedType.prod C X))
      contextListMapExecutable := by
  let Input := EncodedType.prod C (EncodedType.list X)
  let Instrs := contextListMapInstructionListEncodedType C X
  have instructions : TMPolyTimeMap Input Instrs
      (fun argument : Input.Carrier => contextListMapInstructions argument.1 argument.2) := by
    simpa [Input] using contextListMapInstructions_tmPolyTime C X
  have folded : TMPolyTimeMap Input (contextListMapAccumulatorEncodedType C X)
      (fun argument : Input.Carrier =>
        (contextListMapInstructions argument.1 argument.2).foldl
          (fun accumulator instruction => contextListMapStep (accumulator, instruction))
          (contextListMapInitialAccumulator C X)) := by
    have composed := TMPolyTimeMap.comp (contextListMapFold_tmPolyTime C X) instructions
    simpa [Function.comp, Instrs] using composed
  have output := contextListMapOutput_tmPolyTime C X
  have composed := TMPolyTimeMap.comp output folded
  simpa [contextListMapExecutable, Function.comp] using composed

end Program
end ComplexityReduction
