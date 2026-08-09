/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.InvariantFold
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.Sum
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.Range
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.HittingSet.StructuredRoute

/-!
Wrapper-free direct-TM generation of one row of a natural-coordinate
rectangle.  The carrier declarations intentionally use the exact
`EncodedType.Carrier` shape throughout, matching the checked fold API rather
than introducing a representation alias between a program and its codec.
-/

namespace ComplexityReduction
namespace Domain
namespace RectangularCoordinates

open ComplexityReduction

/-- Exact structured codec for one `(left, right)` coordinate. -/
def coordinateEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.nat

/-- Exact structured codec for an ordered coordinate payload. -/
def coordinateListEncodedType : EncodedType :=
  EncodedType.list coordinateEncodedType

/-- The retained context for one row: a left coordinate and right bound. -/
def rowContextEncodedType : EncodedType := coordinateEncodedType

abbrev RowContext : Type := Nat × Nat

/-- A row instruction either installs context or emits one right coordinate. -/
def rowInstructionEncodedType : EncodedType :=
  EncodedType.sum rowContextEncodedType EncodedType.nat

/-- Exact codec for a row instruction stream. -/
def rowInstructionListEncodedType : EncodedType :=
  EncodedType.list rowInstructionEncodedType

/-- The row fold retains its context and the coordinates emitted so far. -/
def rowAccumulatorEncodedType : EncodedType :=
  EncodedType.prod rowContextEncodedType coordinateListEncodedType

/-- Safe zero context before the context instruction arrives. -/
def rowZeroContext : RowContext := (0, 0)

/-- Fixed empty fold state. -/
def rowInitAccumulator : rowAccumulatorEncodedType.Carrier :=
  (rowZeroContext, [])

/-- Install one row context. -/
def rowInitInstruction (context : RowContext) :
    rowInstructionEncodedType.Carrier :=
  Sum.inl context

/-- Emit one right coordinate. -/
def rowIndexInstruction (right : Nat) : rowInstructionEncodedType.Carrier :=
  Sum.inr right

/-- Closed instruction stream for one row. -/
def rowInstructions (context : RowContext) :
    List rowInstructionEncodedType.Carrier :=
  rowInitInstruction context :: (List.range context.2).map rowIndexInstruction

/-- Construct the next coordinate using the retained row context. -/
def coordinateOfRow (context : RowContext) (right : Nat) :
    coordinateEncodedType.Carrier := by
  change Nat × Nat
  exact (context.1, right)

/-- One row-fold transition. -/
def rowStep (argument : rowAccumulatorEncodedType.Carrier ×
    rowInstructionEncodedType.Carrier) : rowAccumulatorEncodedType.Carrier :=
  match argument.2 with
  | Sum.inl context => (context, [])
  | Sum.inr right =>
      (argument.1.1, (show List coordinateEncodedType.Carrier from argument.1.2) ++
        [coordinateOfRow argument.1.1 right])

/-- Extract the emitted coordinate payload from a completed row fold. -/
def rowFromInstructions (instructions : List rowInstructionEncodedType.Carrier) :
    List coordinateEncodedType.Carrier :=
  (instructions.foldl (fun accumulator instruction => rowStep (accumulator, instruction))
    rowInitAccumulator).2

/-- Direct executable for one row. -/
def rowExecutable (context : RowContext) :
    List coordinateEncodedType.Carrier :=
  rowFromInstructions (rowInstructions context)

/-! ### Row semantics -/

theorem rowIndexFold_eq_append_map
    (context : RowContext) (rights : List Nat)
    (output : List coordinateEncodedType.Carrier) :
    ((rights.map rowIndexInstruction).foldl
      (fun accumulator instruction => rowStep (accumulator, instruction))
      (context, output)).2 =
      output ++ rights.map (coordinateOfRow context) := by
  induction rights generalizing output with
  | nil => simp
  | cons right rights inductionHypothesis =>
      rw [List.map_cons, List.foldl_cons]
      simp [rowIndexInstruction, rowStep]
      have tail := inductionHypothesis (output ++ [coordinateOfRow context right])
      simpa [List.append_assoc] using tail

/-- The row executable is the exact ordered range/map presentation. -/
theorem rowExecutable_eq_map (context : RowContext) :
    rowExecutable context =
      (List.range context.2).map (coordinateOfRow context) := by
  change
    (((List.range context.2).map rowIndexInstruction).foldl
      (fun accumulator instruction => rowStep (accumulator, instruction))
      (context, [])).2 =
      (List.range context.2).map (coordinateOfRow context)
  simpa using rowIndexFold_eq_append_map context (List.range context.2) []

/-! ### Direct-TM witnesses -/

theorem rowInitInstruction_tmPolyTime :
    TMPolyTimeMap rowContextEncodedType rowInstructionEncodedType rowInitInstruction := by
  simpa [rowInstructionEncodedType, rowInitInstruction] using
    TMPolyTimeMap.inl rowContextEncodedType EncodedType.nat

theorem rowIndexInstruction_tmPolyTime :
    TMPolyTimeMap EncodedType.nat rowInstructionEncodedType rowIndexInstruction := by
  simpa [rowInstructionEncodedType, rowIndexInstruction] using
    TMPolyTimeMap.inr rowContextEncodedType EncodedType.nat

theorem rowInstructions_tmPolyTime :
    TMPolyTimeMap rowContextEncodedType rowInstructionListEncodedType rowInstructions := by
  let X := rowContextEncodedType
  have context : TMPolyTimeMap X X (fun context : X.Carrier => context) :=
    TMPolyTimeMap.id X
  have rightCount : TMPolyTimeMap X EncodedType.nat
      (fun context : X.Carrier => context.2) := by
    simpa [X, rowContextEncodedType, coordinateEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have init : TMPolyTimeMap X rowInstructionEncodedType
      (fun context : X.Carrier => rowInitInstruction context) := by
    have composed := TMPolyTimeMap.comp rowInitInstruction_tmPolyTime context
    simpa [Function.comp, X] using composed
  have range : TMPolyTimeMap X (EncodedType.list EncodedType.nat)
      (fun context : X.Carrier => List.range context.2) := by
    have composed := TMPolyTimeMap.comp ComplexityReduction.Karp21.natRange_tm_polytime rightCount
    simpa [Function.comp, X] using composed
  have indices : TMPolyTimeMap X rowInstructionListEncodedType
      (fun context : X.Carrier =>
        (List.range context.2).map rowIndexInstruction) := by
    have mapped := TMPolyTimeMap.list_map rowIndexInstruction_tmPolyTime
    have composed := TMPolyTimeMap.comp mapped range
    simpa [Function.comp, rowInstructionListEncodedType, X] using composed
  have consInput : TMPolyTimeMap X
      (EncodedType.prod rowInstructionEncodedType rowInstructionListEncodedType)
      (fun context : X.Carrier =>
        (rowInitInstruction context, (List.range context.2).map rowIndexInstruction)) :=
    TMPolyTimeMap.prod_mk init indices
  have output := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons rowInstructionEncodedType) consInput
  simpa [Function.comp, rowInstructions, rowInstructionListEncodedType, X] using output

theorem rowStepLeft_tmPolyTime :
    TMPolyTimeMap rowContextEncodedType rowAccumulatorEncodedType
      (fun context : RowContext =>
        (context, ([] : List coordinateEncodedType.Carrier))) := by
  have context := TMPolyTimeMap.id rowContextEncodedType
  have empty : TMPolyTimeMap rowContextEncodedType coordinateListEncodedType
      (fun _ : RowContext => ([] : List coordinateEncodedType.Carrier)) :=
    TMPolyTimeMap.const rowContextEncodedType coordinateListEncodedType []
  simpa [rowAccumulatorEncodedType] using TMPolyTimeMap.prod_mk context empty

theorem rowStepRight_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod rowAccumulatorEncodedType EncodedType.nat)
      rowAccumulatorEncodedType
      (fun argument : rowAccumulatorEncodedType.Carrier × Nat =>
        (argument.1.1, (show List coordinateEncodedType.Carrier from argument.1.2) ++
          [coordinateOfRow argument.1.1 argument.2])) := by
  let X := EncodedType.prod rowAccumulatorEncodedType EncodedType.nat
  have accumulator : TMPolyTimeMap X rowAccumulatorEncodedType
      (fun argument : X.Carrier => argument.1) := by
    simpa [X] using TMPolyTimeMap.fst rowAccumulatorEncodedType EncodedType.nat
  have right : TMPolyTimeMap X EncodedType.nat
      (fun argument : X.Carrier => argument.2) := by
    simpa [X] using TMPolyTimeMap.snd rowAccumulatorEncodedType EncodedType.nat
  have context : TMPolyTimeMap X rowContextEncodedType
      (fun argument : X.Carrier => argument.1.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst rowContextEncodedType coordinateListEncodedType) accumulator
    simpa [Function.comp, rowAccumulatorEncodedType, X] using composed
  have output : TMPolyTimeMap X coordinateListEncodedType
      (fun argument : X.Carrier => argument.1.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd rowContextEncodedType coordinateListEncodedType) accumulator
    simpa [Function.comp, rowAccumulatorEncodedType, X] using composed
  have left : TMPolyTimeMap X EncodedType.nat
      (fun argument : X.Carrier => argument.1.1.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst EncodedType.nat EncodedType.nat) context
    simpa [Function.comp, rowContextEncodedType, coordinateEncodedType, X] using composed
  have coordinate : TMPolyTimeMap X coordinateEncodedType
      (fun argument : X.Carrier => coordinateOfRow argument.1.1 argument.2) := by
    simpa [coordinateOfRow, coordinateEncodedType] using TMPolyTimeMap.prod_mk left right
  have singleton : TMPolyTimeMap X coordinateListEncodedType
      (fun argument : X.Carrier => [coordinateOfRow argument.1.1 argument.2]) := by
    have composed := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton coordinateEncodedType) coordinate
    simpa [Function.comp, coordinateListEncodedType] using composed
  have appendInput : TMPolyTimeMap X
      (EncodedType.prod coordinateListEncodedType coordinateListEncodedType)
      (fun argument : X.Carrier =>
        ((show List coordinateEncodedType.Carrier from argument.1.2),
          [coordinateOfRow argument.1.1 argument.2])) :=
    TMPolyTimeMap.prod_mk output singleton
  have appended : TMPolyTimeMap X coordinateListEncodedType
      (fun argument : X.Carrier =>
        (show List coordinateEncodedType.Carrier from argument.1.2) ++
          [coordinateOfRow argument.1.1 argument.2]) := by
    have composed := TMPolyTimeMap.comp (TMPolyTimeMap.list_append coordinateEncodedType) appendInput
    simpa [Function.comp, coordinateListEncodedType, X] using composed
  simpa [rowAccumulatorEncodedType] using TMPolyTimeMap.prod_mk context appended

theorem rowStep_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod rowAccumulatorEncodedType rowInstructionEncodedType)
      rowAccumulatorEncodedType rowStep := by
  have choice := ComplexityReduction.prodSumChoice_tm_polytime
    rowAccumulatorEncodedType rowContextEncodedType EncodedType.nat
  have branches := TMPolyTimeMap.sum_elim rowStepLeft_tmPolyTime rowStepRight_tmPolyTime
  have output := TMPolyTimeMap.comp branches choice
  convert output using 1
  funext argument
  rcases argument with ⟨accumulator, instruction⟩
  cases instruction <;> rfl

/-! ### Verified fold bound -/

def RowFoldInvariant (bound : Nat) (accumulator : rowAccumulatorEncodedType.Carrier) : Prop :=
  accumulator = rowInitAccumulator ∨
    accumulator.1 = rowZeroContext ∨
      rowContextEncodedType.inputSize accumulator.1 ≤ bound

noncomputable def rowFoldBase : Polynomial Nat := Polynomial.C 100

noncomputable def rowFoldGrow : Polynomial Nat :=
  Polynomial.C 20 * Polynomial.X + Polynomial.C 200

@[simp] theorem rowFoldGrow_eval (bound : Nat) :
    rowFoldGrow.eval bound = 20 * bound + 200 := by
  simp [rowFoldGrow, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]

theorem rowInitAccumulator_bound (source : List rowInstructionEncodedType.Carrier) :
    RowFoldInvariant (rowInstructionListEncodedType.inputSize source) rowInitAccumulator ∧
      rowAccumulatorEncodedType.inputSize rowInitAccumulator ≤
        rowFoldBase.eval (rowInstructionListEncodedType.inputSize source) := by
  constructor
  · exact Or.inl rfl
  · simp [rowFoldBase]
    decide

theorem coordinateOfRow_inputSize_le
    {bound : Nat} {context : RowContext} {right : Nat}
    (contextBound : rowContextEncodedType.inputSize context ≤ bound)
    (rightBound : EncodedType.nat.inputSize right ≤ bound) :
    coordinateEncodedType.inputSize (coordinateOfRow context right) ≤ 4 * bound + 10 := by
  rcases context with ⟨left, rightCount⟩
  simp [coordinateOfRow, coordinateEncodedType, rowContextEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_nat] at contextBound rightBound ⊢
  omega

theorem coordinateOfZeroRow_inputSize_le
    {bound right : Nat} (rightBound : EncodedType.nat.inputSize right ≤ bound) :
    coordinateEncodedType.inputSize (coordinateOfRow rowZeroContext right) ≤ 4 * bound + 10 := by
  simp [coordinateOfRow, rowZeroContext, coordinateEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_nat] at rightBound ⊢
  omega

theorem rowStep_growth
    (source : List rowInstructionEncodedType.Carrier)
    (accumulator : rowAccumulatorEncodedType.Carrier)
    (instruction : rowInstructionEncodedType.Carrier)
    (invariant : RowFoldInvariant (rowInstructionListEncodedType.inputSize source) accumulator)
    (instructionBound : rowInstructionEncodedType.inputSize instruction ≤
      rowInstructionListEncodedType.inputSize source) :
    RowFoldInvariant (rowInstructionListEncodedType.inputSize source)
        (rowStep (accumulator, instruction)) ∧
      rowAccumulatorEncodedType.inputSize (rowStep (accumulator, instruction)) ≤
        rowAccumulatorEncodedType.inputSize accumulator +
          rowFoldGrow.eval (rowInstructionListEncodedType.inputSize source) := by
  let bound := rowInstructionListEncodedType.inputSize source
  rcases accumulator with ⟨context, output⟩
  cases instruction with
  | inl newContext =>
      have contextBound : rowContextEncodedType.inputSize newContext ≤ bound := by
        exact Nat.le_of_lt (by
          simpa [bound, rowInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum] using instructionBound)
      constructor
      · exact Or.inr (Or.inr contextBound)
      · have newAccumulatorBound :
            rowAccumulatorEncodedType.inputSize
                (newContext, ([] : List coordinateEncodedType.Carrier)) ≤ bound + 1 := by
          simp [rowAccumulatorEncodedType, EncodedType.inputSize_prod,
            coordinateListEncodedType, EncodedType.inputSize_list_nil]
          omega
        have growth :
            bound + 1 ≤ rowAccumulatorEncodedType.inputSize (context, output) +
              rowFoldGrow.eval bound := by
          rw [rowFoldGrow_eval]
          omega
        simpa [rowStep, bound] using newAccumulatorBound.trans growth
  | inr right =>
      have rightBound : EncodedType.nat.inputSize right ≤ bound := by
        exact Nat.le_of_lt (by
          simpa [bound, rowInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum] using instructionBound)
      have coordinateBound :
          coordinateEncodedType.inputSize (coordinateOfRow context right) ≤ 4 * bound + 10 := by
        rcases invariant with initial | remainder
        · injection initial with contextEquality _outputEquality
          rw [contextEquality]
          exact coordinateOfZeroRow_inputSize_le rightBound
        · rcases remainder with zeroContext | contextBound
          · have contextEquality : context = rowZeroContext := by simpa using zeroContext
            rw [contextEquality]
            exact coordinateOfZeroRow_inputSize_le rightBound
          · exact coordinateOfRow_inputSize_le contextBound rightBound
      have singletonBound :
          coordinateListEncodedType.inputSize [coordinateOfRow context right] ≤ 4 * bound + 12 := by
        simp [coordinateListEncodedType, EncodedType.inputSize_list_cons,
          EncodedType.inputSize_list_nil] at coordinateBound ⊢
        omega
      have appendSize :
          coordinateListEncodedType.inputSize
              ((show List coordinateEncodedType.Carrier from output) ++
                [coordinateOfRow context right]) =
            coordinateListEncodedType.inputSize output +
              coordinateListEncodedType.inputSize [coordinateOfRow context right] := by
        simpa [coordinateListEncodedType] using
          ComplexityReduction.Karp21.list_inputSize_append coordinateEncodedType output
            [coordinateOfRow context right]
      constructor
      · rcases invariant with initial | remainder
        · injection initial with contextEquality _outputEquality
          exact Or.inr (Or.inl contextEquality)
        · exact Or.inr remainder
      · change
          rowAccumulatorEncodedType.inputSize
              (context, (show List coordinateEncodedType.Carrier from output) ++
                [coordinateOfRow context right]) ≤
            rowAccumulatorEncodedType.inputSize (context, output) + rowFoldGrow.eval bound
        simp [rowAccumulatorEncodedType, EncodedType.inputSize_prod] at appendSize ⊢
        rw [appendSize]
        omega

theorem rowFold_tmPolyTime :
    TMPolyTimeMap rowInstructionListEncodedType rowAccumulatorEncodedType
      (fun instructions : List rowInstructionEncodedType.Carrier =>
        instructions.foldl (fun accumulator instruction => rowStep (accumulator, instruction))
          rowInitAccumulator) := by
  rcases rowStep_tmPolyTime with ⟨stepTM⟩
  refine TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
    rowInstructionEncodedType rowAccumulatorEncodedType rowStep rowInitAccumulator stepTM
    rowFoldBase rowFoldGrow RowFoldInvariant ?_ ?_
  · intro source
    exact rowInitAccumulator_bound source
  · intro source accumulator instruction invariant instructionBound
    exact rowStep_growth source accumulator instruction invariant instructionBound

theorem rowFromInstructions_tmPolyTime :
    TMPolyTimeMap rowInstructionListEncodedType coordinateListEncodedType rowFromInstructions := by
  have outputProjection := TMPolyTimeMap.snd rowContextEncodedType coordinateListEncodedType
  have composed := TMPolyTimeMap.comp outputProjection rowFold_tmPolyTime
  simpa [Function.comp, rowFromInstructions, rowAccumulatorEncodedType] using composed

theorem rowExecutable_tmPolyTime :
    TMPolyTimeMap rowContextEncodedType coordinateListEncodedType rowExecutable := by
  have composed := TMPolyTimeMap.comp rowFromInstructions_tmPolyTime rowInstructions_tmPolyTime
  simpa [Function.comp, rowExecutable] using composed

theorem rowExecutable_inputSize_le {bound : Nat} {context : RowContext}
    (contextBound : rowContextEncodedType.inputSize context ≤ bound) :
    coordinateListEncodedType.inputSize (rowExecutable context) ≤
      (bound + 1) * (4 * bound + 12) := by
  rw [rowExecutable_eq_map]
  let row := (List.range context.2).map (coordinateOfRow context)
  have rightCountBound : context.2 ≤ bound := by
    rcases context with ⟨left, rightCount⟩
    simp [rowContextEncodedType, coordinateEncodedType,
      EncodedType.inputSize_prod, EncodedType.inputSize_nat] at contextBound
    change rightCount ≤ bound
    omega
  have lengthBound : row.length ≤ bound + 1 := by
    dsimp [row]
    simp
    omega
  have elementBound : ∀ coordinate ∈ row,
      coordinateEncodedType.inputSize coordinate ≤ 4 * bound + 10 := by
    intro coordinate coordinateMember
    dsimp [row] at coordinateMember
    rcases List.mem_map.mp coordinateMember with ⟨right, rightMember, rfl⟩
    have rightLess : right < context.2 := by simpa using List.mem_range.mp rightMember
    have rightBound : EncodedType.nat.inputSize right ≤ bound := by
      simp [EncodedType.inputSize_nat]
      omega
    exact coordinateOfRow_inputSize_le contextBound rightBound
  have listBound :=
    ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
      coordinateEncodedType row (4 * bound + 10) elementBound
  calc
    coordinateListEncodedType.inputSize row ≤ row.length * (4 * bound + 10 + 1) := by
      simpa [coordinateListEncodedType] using listBound
    _ ≤ (bound + 1) * (4 * bound + 12) :=
      Nat.mul_le_mul lengthBound (by omega)

/-! ### Complete row-major rectangular family -/

/-- Exact codec for a rectangle's left and right bounds. -/
def familyContextEncodedType : EncodedType := coordinateEncodedType

/-- Bounds retained while emitting a row-major rectangle. -/
abbrev FamilyContext : Type := Nat × Nat

/-- A family instruction installs bounds or emits one left coordinate. -/
def familyInstructionEncodedType : EncodedType :=
  EncodedType.sum familyContextEncodedType EncodedType.nat

/-- Exact codec for a family instruction stream. -/
def familyInstructionListEncodedType : EncodedType :=
  EncodedType.list familyInstructionEncodedType

/-- The family fold retains bounds and all emitted coordinates. -/
def familyAccumulatorEncodedType : EncodedType :=
  EncodedType.prod familyContextEncodedType coordinateListEncodedType

/-- Safe bounds before the family context arrives. -/
def familyZeroContext : FamilyContext := (0, 0)

/-- Fixed empty state for the rectangle fold. -/
def familyInitAccumulator : familyAccumulatorEncodedType.Carrier :=
  (familyZeroContext, [])

/-- Install rectangle bounds. -/
def familyInitInstruction (context : FamilyContext) : familyInstructionEncodedType.Carrier :=
  Sum.inl context

/-- Emit one left coordinate. -/
def familyIndexInstruction (left : Nat) : familyInstructionEncodedType.Carrier :=
  Sum.inr left

/-- Closed instruction stream for one rectangle. -/
def familyInstructions (context : FamilyContext) : List familyInstructionEncodedType.Carrier :=
  familyInitInstruction context :: (List.range context.1).map familyIndexInstruction

/-- Instantiate one reusable row context at the emitted left coordinate. -/
def rowContextOfFamily (context : FamilyContext) (left : Nat) :
    rowContextEncodedType.Carrier := by
  change Nat × Nat
  exact (left, context.2)

/-- One family transition appends the complete corresponding row. -/
def familyStep (argument : familyAccumulatorEncodedType.Carrier ×
    familyInstructionEncodedType.Carrier) : familyAccumulatorEncodedType.Carrier :=
  match argument.2 with
  | Sum.inl context => (context, [])
  | Sum.inr left =>
      (argument.1.1, (show List coordinateEncodedType.Carrier from argument.1.2) ++
        rowExecutable (rowContextOfFamily argument.1.1 left))

/-- Extract the emitted coordinates from a completed family fold. -/
def familyFromInstructions (instructions : List familyInstructionEncodedType.Carrier) :
    List coordinateEncodedType.Carrier :=
  (instructions.foldl (fun accumulator instruction => familyStep (accumulator, instruction))
    familyInitAccumulator).2

/-- Direct executable for the complete row-major rectangle. -/
def familyExecutable (context : FamilyContext) : List coordinateEncodedType.Carrier :=
  familyFromInstructions (familyInstructions context)

/-! ### Family semantics -/

theorem familyIndexFold_eq_append_flatMap
    (context : FamilyContext) (lefts : List Nat)
    (output : List coordinateEncodedType.Carrier) :
    ((lefts.map familyIndexInstruction).foldl
      (fun accumulator instruction => familyStep (accumulator, instruction))
      (context, output)).2 =
      output ++ lefts.flatMap (fun left => rowExecutable (rowContextOfFamily context left)) := by
  induction lefts generalizing output with
  | nil => simp
  | cons left lefts inductionHypothesis =>
      rw [List.map_cons, List.foldl_cons]
      simp [familyIndexInstruction, familyStep]
      have tail := inductionHypothesis
        (output ++ rowExecutable (rowContextOfFamily context left))
      simpa [List.append_assoc] using tail

/-- The family executable is exactly the ordered range/flatMap rectangle. -/
theorem familyExecutable_eq_flatMap (context : FamilyContext) :
    familyExecutable context =
      (List.range context.1).flatMap (fun left =>
        (List.range context.2).map (coordinateOfRow (left, context.2))) := by
  change
    (((List.range context.1).map familyIndexInstruction).foldl
      (fun accumulator instruction => familyStep (accumulator, instruction))
      (context, [])).2 =
      (List.range context.1).flatMap (fun left =>
        (List.range context.2).map (coordinateOfRow (left, context.2)))
  rw [familyIndexFold_eq_append_flatMap context (List.range context.1) []]
  apply List.flatMap_congr
  intro left _leftMember
  simpa [rowContextOfFamily] using rowExecutable_eq_map (rowContextOfFamily context left)

/-! ### Family direct-TM witnesses -/

theorem familyInitInstruction_tmPolyTime :
    TMPolyTimeMap familyContextEncodedType familyInstructionEncodedType familyInitInstruction := by
  simpa [familyInstructionEncodedType, familyInitInstruction] using
    TMPolyTimeMap.inl familyContextEncodedType EncodedType.nat

theorem familyIndexInstruction_tmPolyTime :
    TMPolyTimeMap EncodedType.nat familyInstructionEncodedType familyIndexInstruction := by
  simpa [familyInstructionEncodedType, familyIndexInstruction] using
    TMPolyTimeMap.inr familyContextEncodedType EncodedType.nat

theorem familyInstructions_tmPolyTime :
    TMPolyTimeMap familyContextEncodedType familyInstructionListEncodedType familyInstructions := by
  let X := familyContextEncodedType
  have context : TMPolyTimeMap X X (fun context : X.Carrier => context) :=
    TMPolyTimeMap.id X
  have leftCount : TMPolyTimeMap X EncodedType.nat
      (fun context : X.Carrier => context.1) := by
    simpa [X, familyContextEncodedType, coordinateEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have init : TMPolyTimeMap X familyInstructionEncodedType
      (fun context : X.Carrier => familyInitInstruction context) := by
    have composed := TMPolyTimeMap.comp familyInitInstruction_tmPolyTime context
    simpa [Function.comp, X] using composed
  have range : TMPolyTimeMap X (EncodedType.list EncodedType.nat)
      (fun context : X.Carrier => List.range context.1) := by
    have composed := TMPolyTimeMap.comp ComplexityReduction.Karp21.natRange_tm_polytime leftCount
    simpa [Function.comp, X] using composed
  have indices : TMPolyTimeMap X familyInstructionListEncodedType
      (fun context : X.Carrier =>
        (List.range context.1).map familyIndexInstruction) := by
    have mapped := TMPolyTimeMap.list_map familyIndexInstruction_tmPolyTime
    have composed := TMPolyTimeMap.comp mapped range
    simpa [Function.comp, familyInstructionListEncodedType, X] using composed
  have consInput : TMPolyTimeMap X
      (EncodedType.prod familyInstructionEncodedType familyInstructionListEncodedType)
      (fun context : X.Carrier =>
        (familyInitInstruction context, (List.range context.1).map familyIndexInstruction)) :=
    TMPolyTimeMap.prod_mk init indices
  have output := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons familyInstructionEncodedType) consInput
  simpa [Function.comp, familyInstructions, familyInstructionListEncodedType, X] using output

theorem familyStepLeft_tmPolyTime :
    TMPolyTimeMap familyContextEncodedType familyAccumulatorEncodedType
      (fun context : FamilyContext =>
        (context, ([] : List coordinateEncodedType.Carrier))) := by
  have context := TMPolyTimeMap.id familyContextEncodedType
  have empty : TMPolyTimeMap familyContextEncodedType coordinateListEncodedType
      (fun _ : FamilyContext => ([] : List coordinateEncodedType.Carrier)) :=
    TMPolyTimeMap.const familyContextEncodedType coordinateListEncodedType []
  simpa [familyAccumulatorEncodedType] using TMPolyTimeMap.prod_mk context empty

theorem familyStepRight_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod familyAccumulatorEncodedType EncodedType.nat)
      familyAccumulatorEncodedType
      (fun argument : familyAccumulatorEncodedType.Carrier × Nat =>
        (argument.1.1, (show List coordinateEncodedType.Carrier from argument.1.2) ++
          rowExecutable (rowContextOfFamily argument.1.1 argument.2))) := by
  let X := EncodedType.prod familyAccumulatorEncodedType EncodedType.nat
  have accumulator : TMPolyTimeMap X familyAccumulatorEncodedType
      (fun argument : X.Carrier => argument.1) := by
    simpa [X] using TMPolyTimeMap.fst familyAccumulatorEncodedType EncodedType.nat
  have left : TMPolyTimeMap X EncodedType.nat
      (fun argument : X.Carrier => argument.2) := by
    simpa [X] using TMPolyTimeMap.snd familyAccumulatorEncodedType EncodedType.nat
  have context : TMPolyTimeMap X familyContextEncodedType
      (fun argument : X.Carrier => argument.1.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst familyContextEncodedType coordinateListEncodedType) accumulator
    simpa [Function.comp, familyAccumulatorEncodedType, X] using composed
  have output : TMPolyTimeMap X coordinateListEncodedType
      (fun argument : X.Carrier => argument.1.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd familyContextEncodedType coordinateListEncodedType) accumulator
    simpa [Function.comp, familyAccumulatorEncodedType, X] using composed
  have rightCount : TMPolyTimeMap X EncodedType.nat
      (fun argument : X.Carrier => argument.1.1.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd EncodedType.nat EncodedType.nat) context
    simpa [Function.comp, familyContextEncodedType, coordinateEncodedType, X] using composed
  have rowContext : TMPolyTimeMap X rowContextEncodedType
      (fun argument : X.Carrier => rowContextOfFamily argument.1.1 argument.2) := by
    simpa [rowContextOfFamily, rowContextEncodedType, coordinateEncodedType] using
      TMPolyTimeMap.prod_mk left rightCount
  have row : TMPolyTimeMap X coordinateListEncodedType
      (fun argument : X.Carrier =>
        rowExecutable (rowContextOfFamily argument.1.1 argument.2)) := by
    have composed := TMPolyTimeMap.comp rowExecutable_tmPolyTime rowContext
    simpa [Function.comp, X] using composed
  have appendInput : TMPolyTimeMap X
      (EncodedType.prod coordinateListEncodedType coordinateListEncodedType)
      (fun argument : X.Carrier =>
        ((show List coordinateEncodedType.Carrier from argument.1.2),
          rowExecutable (rowContextOfFamily argument.1.1 argument.2))) :=
    TMPolyTimeMap.prod_mk output row
  have appended : TMPolyTimeMap X coordinateListEncodedType
      (fun argument : X.Carrier =>
        (show List coordinateEncodedType.Carrier from argument.1.2) ++
          rowExecutable (rowContextOfFamily argument.1.1 argument.2)) := by
    have composed := TMPolyTimeMap.comp (TMPolyTimeMap.list_append coordinateEncodedType) appendInput
    simpa [Function.comp, coordinateListEncodedType, X] using composed
  simpa [familyAccumulatorEncodedType] using TMPolyTimeMap.prod_mk context appended

theorem familyStep_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod familyAccumulatorEncodedType familyInstructionEncodedType)
      familyAccumulatorEncodedType familyStep := by
  have choice := ComplexityReduction.prodSumChoice_tm_polytime
    familyAccumulatorEncodedType familyContextEncodedType EncodedType.nat
  have branches := TMPolyTimeMap.sum_elim familyStepLeft_tmPolyTime familyStepRight_tmPolyTime
  have output := TMPolyTimeMap.comp branches choice
  convert output using 1
  funext argument
  rcases argument with ⟨accumulator, instruction⟩
  cases instruction <;> rfl

/-! ### Verified family-fold bound -/

def FamilyFoldInvariant (bound : Nat) (accumulator : familyAccumulatorEncodedType.Carrier) : Prop :=
  accumulator = familyInitAccumulator ∨
    accumulator.1 = familyZeroContext ∨
      familyContextEncodedType.inputSize accumulator.1 ≤ bound

noncomputable def familyFoldBase : Polynomial Nat := Polynomial.C 100

noncomputable def familyFoldGrow : Polynomial Nat :=
  Polynomial.C 1000 * (Polynomial.X * Polynomial.X) + Polynomial.C 10000

@[simp] theorem familyFoldGrow_eval (bound : Nat) :
    familyFoldGrow.eval bound = 1000 * (bound * bound) + 10000 := by
  simp [familyFoldGrow, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]

theorem familyInitAccumulator_bound (source : List familyInstructionEncodedType.Carrier) :
    FamilyFoldInvariant (familyInstructionListEncodedType.inputSize source) familyInitAccumulator ∧
      familyAccumulatorEncodedType.inputSize familyInitAccumulator ≤
        familyFoldBase.eval (familyInstructionListEncodedType.inputSize source) := by
  constructor
  · exact Or.inl rfl
  · simp [familyFoldBase]
    decide

theorem rowContextOfFamily_inputSize_le
    {bound : Nat} {context : FamilyContext} {left : Nat}
    (contextBound : familyContextEncodedType.inputSize context ≤ bound)
    (leftBound : EncodedType.nat.inputSize left ≤ bound) :
    rowContextEncodedType.inputSize (rowContextOfFamily context left) ≤ 2 * bound + 20 := by
  rcases context with ⟨leftCount, rightCount⟩
  simp [rowContextOfFamily, familyContextEncodedType, rowContextEncodedType,
    coordinateEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_nat] at contextBound leftBound ⊢
  omega

theorem rowContextOfZeroFamily_inputSize_le
    {bound left : Nat} (leftBound : EncodedType.nat.inputSize left ≤ bound) :
    rowContextEncodedType.inputSize (rowContextOfFamily familyZeroContext left) ≤ 2 * bound + 20 := by
  simp [rowContextOfFamily, familyZeroContext,
    rowContextEncodedType, coordinateEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat] at leftBound ⊢
  omega

theorem familyStep_growth
    (source : List familyInstructionEncodedType.Carrier)
    (accumulator : familyAccumulatorEncodedType.Carrier)
    (instruction : familyInstructionEncodedType.Carrier)
    (invariant : FamilyFoldInvariant (familyInstructionListEncodedType.inputSize source) accumulator)
    (instructionBound : familyInstructionEncodedType.inputSize instruction ≤
      familyInstructionListEncodedType.inputSize source) :
    FamilyFoldInvariant (familyInstructionListEncodedType.inputSize source)
        (familyStep (accumulator, instruction)) ∧
      familyAccumulatorEncodedType.inputSize (familyStep (accumulator, instruction)) ≤
        familyAccumulatorEncodedType.inputSize accumulator +
          familyFoldGrow.eval (familyInstructionListEncodedType.inputSize source) := by
  let bound := familyInstructionListEncodedType.inputSize source
  rcases accumulator with ⟨context, output⟩
  cases instruction with
  | inl newContext =>
      have contextBound : familyContextEncodedType.inputSize newContext ≤ bound := by
        exact Nat.le_of_lt (by
          simpa [bound, familyInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum] using instructionBound)
      constructor
      · exact Or.inr (Or.inr contextBound)
      · have newAccumulatorBound :
            familyAccumulatorEncodedType.inputSize
                (newContext, ([] : List coordinateEncodedType.Carrier)) ≤ bound + 1 := by
          simp [familyAccumulatorEncodedType, EncodedType.inputSize_prod,
            coordinateListEncodedType, EncodedType.inputSize_list_nil]
          omega
        have growth :
            bound + 1 ≤ familyAccumulatorEncodedType.inputSize (context, output) +
              familyFoldGrow.eval bound := by
          rw [familyFoldGrow_eval]
          nlinarith [Nat.zero_le (bound * bound),
            Nat.zero_le (familyAccumulatorEncodedType.inputSize (context, output))]
        simpa [familyStep, bound] using newAccumulatorBound.trans growth
  | inr left =>
      have leftBound : EncodedType.nat.inputSize left ≤ bound := by
        exact Nat.le_of_lt (by
          simpa [bound, familyInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum] using instructionBound)
      have rowContextBound :
          rowContextEncodedType.inputSize (rowContextOfFamily context left) ≤ 2 * bound + 20 := by
        rcases invariant with initial | remainder
        · injection initial with contextEquality _outputEquality
          rw [contextEquality]
          exact rowContextOfZeroFamily_inputSize_le leftBound
        · rcases remainder with zeroContext | contextBound
          · have contextEquality : context = familyZeroContext := by simpa using zeroContext
            rw [contextEquality]
            exact rowContextOfZeroFamily_inputSize_le leftBound
          · exact rowContextOfFamily_inputSize_le contextBound leftBound
      have rowBase := rowExecutable_inputSize_le rowContextBound
      have rowBound :
          coordinateListEncodedType.inputSize (rowExecutable (rowContextOfFamily context left)) ≤
            1000 * (bound * bound) + 9000 := by
        have nonnegative : 0 ≤ bound := Nat.zero_le bound
        nlinarith [rowBase]
      have appendSize :
          coordinateListEncodedType.inputSize
              ((show List coordinateEncodedType.Carrier from output) ++
                rowExecutable (rowContextOfFamily context left)) =
            coordinateListEncodedType.inputSize output +
              coordinateListEncodedType.inputSize
                (rowExecutable (rowContextOfFamily context left)) := by
        simpa [coordinateListEncodedType] using
          ComplexityReduction.Karp21.list_inputSize_append coordinateEncodedType output
            (rowExecutable (rowContextOfFamily context left))
      constructor
      · rcases invariant with initial | remainder
        · injection initial with contextEquality _outputEquality
          exact Or.inr (Or.inl contextEquality)
        · exact Or.inr remainder
      · change
          familyAccumulatorEncodedType.inputSize
              (context, (show List coordinateEncodedType.Carrier from output) ++
                rowExecutable (rowContextOfFamily context left)) ≤
            familyAccumulatorEncodedType.inputSize (context, output) + familyFoldGrow.eval bound
        simp [familyAccumulatorEncodedType, EncodedType.inputSize_prod] at appendSize ⊢
        rw [appendSize]
        omega

theorem familyFold_tmPolyTime :
    TMPolyTimeMap familyInstructionListEncodedType familyAccumulatorEncodedType
      (fun instructions : List familyInstructionEncodedType.Carrier =>
        instructions.foldl (fun accumulator instruction => familyStep (accumulator, instruction))
          familyInitAccumulator) := by
  rcases familyStep_tmPolyTime with ⟨stepTM⟩
  refine TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
    familyInstructionEncodedType familyAccumulatorEncodedType familyStep familyInitAccumulator stepTM
    familyFoldBase familyFoldGrow FamilyFoldInvariant ?_ ?_
  · intro source
    exact familyInitAccumulator_bound source
  · intro source accumulator instruction invariant instructionBound
    exact familyStep_growth source accumulator instruction invariant instructionBound

theorem familyFromInstructions_tmPolyTime :
    TMPolyTimeMap familyInstructionListEncodedType coordinateListEncodedType familyFromInstructions := by
  have outputProjection := TMPolyTimeMap.snd familyContextEncodedType coordinateListEncodedType
  have composed := TMPolyTimeMap.comp outputProjection familyFold_tmPolyTime
  simpa [Function.comp, familyFromInstructions, familyAccumulatorEncodedType] using composed

theorem familyExecutable_tmPolyTime :
    TMPolyTimeMap familyContextEncodedType coordinateListEncodedType familyExecutable := by
  have composed := TMPolyTimeMap.comp familyFromInstructions_tmPolyTime familyInstructions_tmPolyTime
  simpa [Function.comp, familyExecutable] using composed

end RectangularCoordinates
end Domain
end ComplexityReduction
