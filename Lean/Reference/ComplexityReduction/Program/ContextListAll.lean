/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Program.ContextListMap
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.BoolDispatch

/-!
Generic direct-TM all-check over a list with one retained context.

The context is attached with `ContextListMap`, after which a fixed-size Boolean
accumulator folds a supplied direct-TM predicate over every attached item.
-/

namespace ComplexityReduction
namespace Program
namespace ContextListAll

open ComplexityReduction

/-- Boolean conjunction at the small generic combinator boundary. -/
def boolAnd (input : Bool × Bool) : Bool :=
  input.1 && input.2

theorem boolAnd_tmPolyTime :
    TMPolyTimeMap (EncodedType.prod EncodedType.bool EncodedType.bool)
      EncodedType.bool boolAnd := by
  let B := EncodedType.prod EncodedType.bool EncodedType.bool
  have first : TMPolyTimeMap B EncodedType.bool (fun input : B.Carrier => input.1) := by
    simpa [B] using TMPolyTimeMap.fst EncodedType.bool EncodedType.bool
  have second : TMPolyTimeMap B EncodedType.bool (fun input : B.Carrier => input.2) := by
    simpa [B] using TMPolyTimeMap.snd EncodedType.bool EncodedType.bool
  have falseBranch : TMPolyTimeMap B EncodedType.bool (fun _ : B.Carrier => false) :=
    TMPolyTimeMap.const B EncodedType.bool false
  have tagged : TMPolyTimeMap B (EncodedType.prod EncodedType.bool B)
      (fun input : B.Carrier => (input.1, input)) :=
    TMPolyTimeMap.prod_mk first (TMPolyTimeMap.id B)
  have branch : TMPolyTimeMap (EncodedType.prod EncodedType.bool B) EncodedType.bool
      (fun input : Bool × B.Carrier =>
        match input.1 with
        | true => input.2.2
        | false => false) :=
    boolProduct_dispatch_tm_polytime B EncodedType.bool
      (fFalse := fun _ => false) (fTrue := fun input => input.2)
      falseBranch second
  have composed := TMPolyTimeMap.comp branch tagged
  convert composed using 1
  funext input
  rcases input with ⟨first, second⟩
  cases first <;> rfl

/-- One all-fold step combines the retained result with the local predicate. -/
def step {C X : EncodedType}
    (predicate : (EncodedType.prod C X).Carrier → Bool)
    (input : Bool × (EncodedType.prod C X).Carrier) : Bool :=
  boolAnd (input.1, predicate input.2)

theorem step_tmPolyTime {C X : EncodedType}
    (predicate : (EncodedType.prod C X).Carrier → Bool)
    (predicateTM : TMPolyTimeMap (EncodedType.prod C X) EncodedType.bool predicate) :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.bool (EncodedType.prod C X))
      EncodedType.bool (step predicate) := by
  let Input := EncodedType.prod EncodedType.bool (EncodedType.prod C X)
  have accumulator : TMPolyTimeMap Input EncodedType.bool
      (fun input : Input.Carrier => input.1) := by
    simpa [Input] using
      TMPolyTimeMap.fst EncodedType.bool (EncodedType.prod C X)
  have item : TMPolyTimeMap Input (EncodedType.prod C X)
      (fun input : Input.Carrier => input.2) := by
    simpa [Input] using
      TMPolyTimeMap.snd EncodedType.bool (EncodedType.prod C X)
  have checked : TMPolyTimeMap Input EncodedType.bool
      (fun input : Input.Carrier => predicate input.2) := by
    have composed := TMPolyTimeMap.comp predicateTM item
    simpa [Function.comp, Input] using composed
  have pair : TMPolyTimeMap Input
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : Input.Carrier => (input.1, predicate input.2)) :=
    TMPolyTimeMap.prod_mk accumulator checked
  have composed := TMPolyTimeMap.comp boolAnd_tmPolyTime pair
  simpa [step, Function.comp, Input] using composed

/-- Attach the context and require the supplied predicate for every list item. -/
def executable {C X : EncodedType}
    (predicate : (EncodedType.prod C X).Carrier → Bool)
    (input : (EncodedType.prod C (EncodedType.list X)).Carrier) : Bool :=
  (contextListMapExecutable (C := C) (X := X) input).foldl
    (fun accumulator item => step predicate (accumulator, item)) true

private theorem mappedFold_eq {C X : EncodedType}
    (predicate : (EncodedType.prod C X).Carrier → Bool) (context : C.Carrier) :
    ∀ (items : List X.Carrier) (accumulator : Bool),
      (items.map fun item =>
          (show (EncodedType.prod C X).Carrier from (context, item))).foldl
          (fun current item => step predicate (current, item)) accumulator =
        boolAnd (accumulator, items.all fun item => predicate (context, item)) := by
  intro items
  induction items with
  | nil =>
      intro accumulator
      simp [boolAnd]
  | cons item items inductionHypothesis =>
      intro accumulator
      rw [List.map_cons, List.foldl_cons, inductionHypothesis]
      simp [step, boolAnd, Bool.and_assoc]

theorem executable_eq_true_iff {C X : EncodedType}
    (predicate : (EncodedType.prod C X).Carrier → Bool)
    (context : C.Carrier) (items : List X.Carrier) :
    executable predicate (context, items) = true ↔
      ∀ item ∈ items, predicate (context, item) = true := by
  change
    (contextListMapExecutable (C := C) (X := X) (context, items)).foldl
        (fun accumulator item => step predicate (accumulator, item)) true = true ↔ _
  rw [contextListMapExecutable_eq_map (C := C) (X := X) context items]
  rw [mappedFold_eq predicate context items true]
  simp [boolAnd, List.all_eq_true]

private theorem fold_tmPolyTime {C X : EncodedType}
    (predicate : (EncodedType.prod C X).Carrier → Bool)
    (predicateTM : TMPolyTimeMap (EncodedType.prod C X) EncodedType.bool predicate) :
    TMPolyTimeMap (EncodedType.list (EncodedType.prod C X)) EncodedType.bool
      (fun items : List (EncodedType.prod C X).Carrier =>
        items.foldl (fun accumulator item => step predicate (accumulator, item)) true) := by
  rcases step_tmPolyTime predicate predicateTM with ⟨stepTM⟩
  refine TMPolyTimeMap.list_foldl_typed_bounded
    (EncodedType.prod C X) EncodedType.bool (step predicate) true stepTM
    (Polynomial.C 1) ?_ ?_
  · intro items
    simp [EncodedType.inputSize_bool]
  · intro source accumulator item _accumulatorBound _itemBound
    simp [step, boolAnd, EncodedType.inputSize_bool]

theorem executable_tmPolyTime {C X : EncodedType}
    (predicate : (EncodedType.prod C X).Carrier → Bool)
    (predicateTM : TMPolyTimeMap (EncodedType.prod C X) EncodedType.bool predicate) :
    TMPolyTimeMap (EncodedType.prod C (EncodedType.list X)) EncodedType.bool
      (executable predicate) := by
  have attached := contextListMapExecutable_tmPolyTime C X
  have folded := fold_tmPolyTime predicate predicateTM
  have composed := TMPolyTimeMap.comp folded attached
  simpa [executable, Function.comp] using composed

end ContextListAll
end Program
end ComplexityReduction
