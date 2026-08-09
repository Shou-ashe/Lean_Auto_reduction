/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.Core.IncidenceIRValidation
import ComplexityReduction.Program.ContextListMap
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.BoolDispatch
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatPair

/-!
Direct-TM realization of the canonical `IncidenceIR` validation guard.

This is intentionally a hub-local building block: it has no target wrapper,
route, registry, or legacy import.  Egress adapters reuse its exact Boolean
executable to make their total source semantics fail closed on malformed raw
incidence tables.
-/

namespace ComplexityReduction
namespace Domain
namespace IncidenceIRValidation

open ComplexityReduction
open Program

/-- The canonical unary encoding shared by the retained hub indices. -/
abbrev natEncoding : EncodedType := EncodedType.nat

/-- The ordered encoding of one bound pair or one membership pair. -/
abbrev pairEncoding : EncodedType := EncodedType.prod natEncoding natEncoding

/-- The canonical encoding of the raw membership payload. -/
abbrev pairListEncoding : EncodedType := EncodedType.list pairEncoding

/-- One validation item retains the global bounds beside the current raw pair. -/
abbrev validationItemEncoding : EncodedType := EncodedType.prod pairEncoding pairEncoding

/-- The checked fold receives its Boolean accumulator and one retained item. -/
abbrev validationStepInputEncoding : EncodedType :=
  EncodedType.prod EncodedType.bool validationItemEncoding

/-- Boolean conjunction used by the closed validation fold. -/
def boolAnd (input : Bool × Bool) : Bool :=
  input.1 && input.2

/-- Direct-TM realization of Boolean conjunction without importing a graph gadget. -/
theorem boolAnd_tmPolyTime :
    TMPolyTimeMap (EncodedType.prod EncodedType.bool EncodedType.bool)
      EncodedType.bool boolAnd := by
  let X := EncodedType.prod EncodedType.bool EncodedType.bool
  have hFirst : TMPolyTimeMap X EncodedType.bool (fun input : X.Carrier => input.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.bool EncodedType.bool
  have hSecond : TMPolyTimeMap X EncodedType.bool (fun input : X.Carrier => input.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.bool EncodedType.bool
  have hFalse : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hTagged : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun input : X.Carrier => (input.1, input)) :=
    TMPolyTimeMap.prod_mk hFirst (TMPolyTimeMap.id X)
  have hBranch : TMPolyTimeMap (EncodedType.prod EncodedType.bool X) EncodedType.bool
      (fun input : Bool × X.Carrier =>
        match input.1 with
        | true => input.2.2
        | false => false) :=
    boolProduct_dispatch_tm_polytime X EncodedType.bool
      (fFalse := fun _ => false) (fTrue := fun input => input.2) hFalse hSecond
  have hOut := TMPolyTimeMap.comp hBranch hTagged
  convert hOut using 1
  funext input
  rcases input with ⟨first, second⟩
  cases first <;> rfl

/-- Check one raw pair against the two retained hub bounds. -/
def pairWithinBoundsBool (input : (Nat × Nat) × (Nat × Nat)) : Bool :=
  boolAnd
    (ComplexityReduction.natLtBool (input.2.1, input.1.1),
      ComplexityReduction.natLtBool (input.2.2, input.1.2))

/-- A pair passes the executable check exactly when both hub bounds hold. -/
theorem pairWithinBoundsBool_eq_true_iff (input : (Nat × Nat) × (Nat × Nat)) :
    pairWithinBoundsBool input = true ↔
      input.2.1 < input.1.1 ∧ input.2.2 < input.1.2 := by
  simp [pairWithinBoundsBool, boolAnd, ComplexityReduction.natLtBool_eq_true_iff]

/-- Direct-TM realization of the one-pair bound check. -/
theorem pairWithinBoundsBool_tmPolyTime :
    TMPolyTimeMap validationItemEncoding EncodedType.bool pairWithinBoundsBool := by
  let X := validationItemEncoding
  have hBounds : TMPolyTimeMap X pairEncoding (fun input : X.Carrier => input.1) := by
    simpa [X, validationItemEncoding] using TMPolyTimeMap.fst pairEncoding pairEncoding
  have hPair : TMPolyTimeMap X pairEncoding (fun input : X.Carrier => input.2) := by
    simpa [X, validationItemEncoding] using TMPolyTimeMap.snd pairEncoding pairEncoding
  have hLeftBound : TMPolyTimeMap X natEncoding (fun input : X.Carrier => input.1.1) := by
    have h := TMPolyTimeMap.comp (TMPolyTimeMap.fst natEncoding natEncoding) hBounds
    simpa [Function.comp, X] using h
  have hRightBound : TMPolyTimeMap X natEncoding (fun input : X.Carrier => input.1.2) := by
    have h := TMPolyTimeMap.comp (TMPolyTimeMap.snd natEncoding natEncoding) hBounds
    simpa [Function.comp, X] using h
  have hLeftPair : TMPolyTimeMap X natEncoding (fun input : X.Carrier => input.2.1) := by
    have h := TMPolyTimeMap.comp (TMPolyTimeMap.fst natEncoding natEncoding) hPair
    simpa [Function.comp, X] using h
  have hRightPair : TMPolyTimeMap X natEncoding (fun input : X.Carrier => input.2.2) := by
    have h := TMPolyTimeMap.comp (TMPolyTimeMap.snd natEncoding natEncoding) hPair
    simpa [Function.comp, X] using h
  have hLeftInput : TMPolyTimeMap X pairEncoding
      (fun input : X.Carrier => (input.2.1, input.1.1)) :=
    TMPolyTimeMap.prod_mk hLeftPair hLeftBound
  have hRightInput : TMPolyTimeMap X pairEncoding
      (fun input : X.Carrier => (input.2.2, input.1.2)) :=
    TMPolyTimeMap.prod_mk hRightPair hRightBound
  have hLeft : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier => ComplexityReduction.natLtBool (input.2.1, input.1.1)) := by
    have h := TMPolyTimeMap.comp ComplexityReduction.natLtBool_tm_polytime hLeftInput
    simpa [Function.comp, X] using h
  have hRight : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier => ComplexityReduction.natLtBool (input.2.2, input.1.2)) := by
    have h := TMPolyTimeMap.comp ComplexityReduction.natLtBool_tm_polytime hRightInput
    simpa [Function.comp, X] using h
  have hChecks : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : X.Carrier =>
        (ComplexityReduction.natLtBool (input.2.1, input.1.1),
          ComplexityReduction.natLtBool (input.2.2, input.1.2))) :=
    TMPolyTimeMap.prod_mk hLeft hRight
  have hOut := TMPolyTimeMap.comp boolAnd_tmPolyTime hChecks
  simpa [pairWithinBoundsBool, Function.comp] using hOut

/-- One fold step preserves a previous success only when the current pair is in bounds. -/
def validationStep (input : Bool × ((Nat × Nat) × (Nat × Nat))) : Bool :=
  boolAnd (input.1, pairWithinBoundsBool input.2)

/-- Direct-TM realization of the validation fold step. -/
theorem validationStep_tmPolyTime :
    TMPolyTimeMap validationStepInputEncoding EncodedType.bool validationStep := by
  let X := validationStepInputEncoding
  have hAcc : TMPolyTimeMap X EncodedType.bool (fun input : X.Carrier => input.1) := by
    simpa [X, validationStepInputEncoding] using
      TMPolyTimeMap.fst EncodedType.bool validationItemEncoding
  have hItem : TMPolyTimeMap X validationItemEncoding (fun input : X.Carrier => input.2) := by
    simpa [X, validationStepInputEncoding] using
      TMPolyTimeMap.snd EncodedType.bool validationItemEncoding
  have hPairCheck : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier => pairWithinBoundsBool input.2) := by
    have h := TMPolyTimeMap.comp pairWithinBoundsBool_tmPolyTime hItem
    simpa [Function.comp, X] using h
  have hInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : X.Carrier => (input.1, pairWithinBoundsBool input.2)) :=
    TMPolyTimeMap.prod_mk hAcc hPairCheck
  have hOut := TMPolyTimeMap.comp boolAnd_tmPolyTime hInput
  simpa [validationStep, Function.comp] using hOut

/-- Fold the retained global bounds through every raw membership pair. -/
def foldedWellFormedBool (input : (Nat × Nat) × List (Nat × Nat)) : Bool :=
  (Program.contextListMapExecutable (C := pairEncoding) (X := pairEncoding) input).foldl
    (fun accumulator item => validationStep (accumulator, item)) true

private theorem foldedWellFormedBool_aux (bounds : Nat × Nat) :
    ∀ (pairs : List (Nat × Nat)) (accumulator : Bool),
      (pairs.map fun pair => (bounds, pair)).foldl
          (fun current item => validationStep (current, item)) accumulator =
        boolAnd
          (accumulator,
            pairs.all fun pair =>
              decide (pair.1 < bounds.1 ∧ pair.2 < bounds.2)) := by
  intro pairs
  induction pairs with
  | nil =>
      intro accumulator
      simp [boolAnd]
  | cons pair pairs ih =>
      intro accumulator
      rw [List.map_cons, List.foldl_cons, ih]
      simp [validationStep, pairWithinBoundsBool, boolAnd,
        ComplexityReduction.natLtBool, Bool.and_assoc]

/-- The fold executable is extensionally the canonical hub validation guard. -/
theorem foldedWellFormedBool_eq_wellFormedBool (input : IncidenceIR) :
    foldedWellFormedBool ((input.leftSize, input.rightSize), input.membershipPairs) =
      wellFormedBool input := by
  unfold foldedWellFormedBool
  change List.foldl (fun accumulator item => validationStep (accumulator, item)) true
      (Program.contextListMapExecutable (C := pairEncoding) (X := pairEncoding)
        ((input.leftSize, input.rightSize), input.membershipPairs)) =
      wellFormedBool input
  have hMap := Program.contextListMapExecutable_eq_map
    (C := pairEncoding) (X := pairEncoding)
    (input.leftSize, input.rightSize) input.membershipPairs
  rw [hMap]
  simpa [wellFormedBool] using
    (foldedWellFormedBool_aux (input.leftSize, input.rightSize)
      input.membershipPairs true)

/-- The Boolean accumulator stays at the fixed one-symbol bound. -/
private theorem validationFold_tmPolyTime :
    TMPolyTimeMap (EncodedType.list validationItemEncoding) EncodedType.bool
      (fun items : List validationItemEncoding.Carrier =>
        items.foldl (fun accumulator item => validationStep (accumulator, item)) true) := by
  rcases validationStep_tmPolyTime with ⟨stepTM⟩
  refine TMPolyTimeMap.list_foldl_typed_bounded validationItemEncoding EncodedType.bool
    validationStep true stepTM (Polynomial.C 1) ?_ ?_
  · intro items
    simp [EncodedType.inputSize_bool]
  · intro source accumulator item _accumulatorBound _itemBound
    simp [validationStep, EncodedType.inputSize_bool]

/-- Direct-TM realization of the context-attached validation fold. -/
theorem foldedWellFormedBool_tmPolyTime :
    TMPolyTimeMap (EncodedType.prod pairEncoding pairListEncoding) EncodedType.bool
      foldedWellFormedBool := by
  have hAttached := Program.contextListMapExecutable_tmPolyTime pairEncoding pairEncoding
  have hOut := TMPolyTimeMap.comp validationFold_tmPolyTime hAttached
  simpa [foldedWellFormedBool, Function.comp, validationItemEncoding] using hOut

/-- Direct-TM evidence for the exact canonical hub guard. -/
theorem wellFormedBool_tmPolyTime :
    TMPolyTimeMap IncidenceIR.lawfulRepresentation.encodedType EncodedType.bool wellFormedBool := by
  let X := IncidenceIR.lawfulRepresentation.encodedType
  let Payload := EncodedType.prod natEncoding pairListEncoding
  have hPayload : TMPolyTimeMap X Payload (fun input : X.Carrier => input.2) := by
    simpa [X, Payload, IncidenceIR.lawfulRepresentation] using
      TMPolyTimeMap.snd natEncoding Payload
  have hLeft : TMPolyTimeMap X natEncoding (fun input : X.Carrier => input.1) := by
    simpa [X, Payload, IncidenceIR.lawfulRepresentation] using
      TMPolyTimeMap.fst natEncoding Payload
  have hRight : TMPolyTimeMap X natEncoding (fun input : X.Carrier => input.2.1) := by
    have h := TMPolyTimeMap.comp (TMPolyTimeMap.fst natEncoding pairListEncoding) hPayload
    simpa [Function.comp, X, Payload] using h
  have hPairs : TMPolyTimeMap X pairListEncoding (fun input : X.Carrier => input.2.2) := by
    have h := TMPolyTimeMap.comp (TMPolyTimeMap.snd natEncoding pairListEncoding) hPayload
    simpa [Function.comp, X, Payload] using h
  have hBounds : TMPolyTimeMap X pairEncoding
      (fun input : X.Carrier => (input.1, input.2.1)) :=
    TMPolyTimeMap.prod_mk hLeft hRight
  have hInput : TMPolyTimeMap X (EncodedType.prod pairEncoding pairListEncoding)
      (fun input : X.Carrier => ((input.1, input.2.1), input.2.2)) :=
    TMPolyTimeMap.prod_mk hBounds hPairs
  have hOut := TMPolyTimeMap.comp foldedWellFormedBool_tmPolyTime hInput
  convert hOut using 1
  funext input
  exact (foldedWellFormedBool_eq_wellFormedBool input).symm

end IncidenceIRValidation
end Domain
end ComplexityReduction
