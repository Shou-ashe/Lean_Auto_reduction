/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.Part1
import ComplexityReduction.Program.CompileTM

/-!
Shared list constructors for V2 programs.

Only the existing direct-TM structural machines are admitted here.  General list mapping and
append are syntax constructors and are compiled recursively in `CompileTM`; this leaf adds the
remaining direct structural atoms without creating route-local machines.
-/

namespace ComplexityReduction

namespace TMPolyTimeMap

/-! ### Generic direct-TM list assembly -/

/-- Build the empty encoded list, independently of the input. -/
theorem list_nil (X Y : EncodedType) :
    TMPolyTimeMap X (EncodedType.list Y) (fun _ : X.Carrier => []) :=
  TMPolyTimeMap.const X (EncodedType.list Y) []

/-- Put the output of any direct-TM map into a one-element encoded list. -/
theorem list_singleton_of {X Y : EncodedType} {value : X.Carrier → Y.Carrier}
    (hValue : TMPolyTimeMap X Y value) :
    TMPolyTimeMap X (EncodedType.list Y) (fun input => [value input]) := by
  have output := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton Y) hValue
  simpa [Function.comp] using output

/-- Prepend one direct-TM-produced value to one direct-TM-produced encoded list. -/
theorem list_cons_of {X Y : EncodedType}
    {head : X.Carrier → Y.Carrier}
    {tail : X.Carrier → List Y.Carrier}
    (hHead : TMPolyTimeMap X Y head)
    (hTail : TMPolyTimeMap X (EncodedType.list Y) tail) :
    TMPolyTimeMap X (EncodedType.list Y)
      (fun input => head input :: tail input) := by
  have pair := TMPolyTimeMap.prod_mk hHead hTail
  have output := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons Y) pair
  simpa [Function.comp] using output

end TMPolyTimeMap

namespace Program

open Encoding

/-! ### Direct-TM list flattening -/

/-- Append preserves the exact encoded input-size sum of two lists. -/
private theorem list_inputSize_append (element : ComplexityReduction.EncodedType) :
    ∀ (left right : List element.Carrier),
      (ComplexityReduction.EncodedType.list element).inputSize (left ++ right) =
        (ComplexityReduction.EncodedType.list element).inputSize left +
          (ComplexityReduction.EncodedType.list element).inputSize right
  | [], right => by
      simp [ComplexityReduction.EncodedType.inputSize_list_nil]
  | left :: rest, right => by
      rw [List.cons_append, ComplexityReduction.EncodedType.inputSize_list_cons,
        ComplexityReduction.EncodedType.inputSize_list_cons,
        list_inputSize_append element rest right]
      omega

/-- One direct-TM flattening step appends the current inner list. -/
def listFlattenStep (element : ComplexityReduction.EncodedType) :
    (List element.Carrier × List element.Carrier) → List element.Carrier :=
  fun input => input.1 ++ input.2

/-- The flattening step is exactly the existing direct-TM list append machine. -/
theorem listFlattenStep_tmPolyTime (element : ComplexityReduction.EncodedType) :
    ComplexityReduction.TMPolyTimeMap
      (ComplexityReduction.EncodedType.prod
        (ComplexityReduction.EncodedType.list element)
        (ComplexityReduction.EncodedType.list element))
      (ComplexityReduction.EncodedType.list element)
      (listFlattenStep element) := by
  simpa [listFlattenStep] using ComplexityReduction.TMPolyTimeMap.list_append element

private theorem listFlatten_fold_append (element : ComplexityReduction.EncodedType) :
    ∀ (lists : List (List element.Carrier)) (accumulator : List element.Carrier),
      lists.foldl (fun accumulator current => listFlattenStep element (accumulator, current))
          accumulator =
        accumulator ++ lists.flatten
  | [], accumulator => by simp [listFlattenStep]
  | current :: rest, accumulator => by
      simpa [listFlattenStep, List.append_assoc] using
        listFlatten_fold_append element rest (accumulator ++ current)

/--
Flatten one encoded list of encoded lists using only the shared append machine
and the reachable-fold compiler.  This is a generic program combinator, not a
route-local construction; the proof bounds every inner list by its original
outer-list input before the fold appends it.
-/
theorem listFlatten_tmPolyTime (element : ComplexityReduction.EncodedType) :
    ComplexityReduction.TMPolyTimeMap
      (ComplexityReduction.EncodedType.list
        (ComplexityReduction.EncodedType.list element))
      (ComplexityReduction.EncodedType.list element)
      List.flatten := by
  rcases listFlattenStep_tmPolyTime element with ⟨stepTM⟩
  have folded : ComplexityReduction.TMPolyTimeMap
      (ComplexityReduction.EncodedType.list
        (ComplexityReduction.EncodedType.list element))
      (ComplexityReduction.EncodedType.list element)
      (fun lists : List (List element.Carrier) =>
        lists.foldl (fun accumulator current => listFlattenStep element (accumulator, current)) []) := by
    refine ComplexityReduction.TMPolyTimeMap.list_foldl_typed_growth_bounded
      (ComplexityReduction.EncodedType.list element)
      (ComplexityReduction.EncodedType.list element)
      (listFlattenStep element) [] stepTM
      (Polynomial.C 0) Polynomial.X ?_ ?_
    · intro source
      simp [ComplexityReduction.EncodedType.inputSize_list_nil]
    · intro source accumulator current currentBound
      rw [listFlattenStep, list_inputSize_append]
      simp [Polynomial.eval_X]
      omega
  convert folded using 1
  funext lists
  simpa [listFlattenStep] using (listFlatten_fold_append element lists []).symm

namespace PolyProg

/-- Build a one-element list using the existing direct-TM list singleton machine. -/
def listSingleton (element : LawfulEncodedType) :
    PolyProg element (StandardInstances.list element) :=
  .atom <| Primitive.ofTMPolyTime (fun value => [value])
    (ComplexityReduction.TMPolyTimeMap.list_singleton element.encodedType)

/-- Prepend an element to a list using the existing direct-TM list-cons machine. -/
def listCons (element : LawfulEncodedType) :
    PolyProg (StandardInstances.prod element (StandardInstances.list element))
      (StandardInstances.list element) :=
  .atom <| Primitive.ofTMPolyTime (fun value => value.1 :: value.2)
    (ComplexityReduction.TMPolyTimeMap.list_cons element.encodedType)

@[simp]
theorem run_listSingleton (element : LawfulEncodedType) (input : element.Carrier) :
    (listSingleton element).run input = [input] :=
  rfl

@[simp]
theorem run_listCons (element : LawfulEncodedType)
    (input : (StandardInstances.prod element (StandardInstances.list element)).Carrier) :
    (listCons element).run input = input.1 :: input.2 :=
  rfl

/-- Singleton compilation retains the existing direct-TM singleton combinator exactly. -/
@[simp]
theorem compileTM_listSingleton (element : LawfulEncodedType) :
    (listSingleton element).compileTM =
      ComplexityReduction.TMPolyTimeMap.list_singleton element.encodedType :=
  rfl

/-- Cons compilation retains the existing direct-TM cons combinator exactly. -/
@[simp]
theorem compileTM_listCons (element : LawfulEncodedType) :
    (listCons element).compileTM =
      ComplexityReduction.TMPolyTimeMap.list_cons element.encodedType :=
  rfl

/-- The list singleton compatibility cost is projected only from its direct-TM compiler. -/
@[simp]
theorem compatibilityCost_listSingleton_eq_outputSizeBound (element : LawfulEncodedType) :
    (listSingleton element).compatibilityCost =
      ComplexityReduction.CostedMap.of_encodedPolynomialSizeBound
        (ComplexityReduction.TMPolyTimeMap.outputSizeBound (listSingleton element).compileTM) :=
  PolyProg.compatibilityCost_eq_outputSizeBound _

/-- The list cons compatibility cost is projected only from its direct-TM compiler. -/
@[simp]
theorem compatibilityCost_listCons_eq_outputSizeBound (element : LawfulEncodedType) :
    (listCons element).compatibilityCost =
      ComplexityReduction.CostedMap.of_encodedPolynomialSizeBound
        (ComplexityReduction.TMPolyTimeMap.outputSizeBound (listCons element).compileTM) :=
  PolyProg.compatibilityCost_eq_outputSizeBound _

end PolyProg
end Program
end ComplexityReduction
