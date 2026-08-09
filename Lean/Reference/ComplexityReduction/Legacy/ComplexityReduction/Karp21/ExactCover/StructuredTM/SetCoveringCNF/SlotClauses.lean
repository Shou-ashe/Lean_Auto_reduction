import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.Literals
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.InvariantFold
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.StructuredTM.ProductSumChoice

namespace ComplexityReduction
namespace Karp21
namespace ExactCover

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
Executable slot-clause layer for the compact Set-Covering-to-CNF route.

This module starts with the at-least-one slot clauses.  For a row context
`(slot, choiceCount)`, it emits the pairs `(slot, 0), ..., (slot, choiceCount-1)`
by a checked fold and maps those pairs to positive CNF literals.
-/

def setCoveringChoicePairRowContextEncodedType : EncodedType :=
  vertexPairEncodedType

abbrev SetCoveringChoicePairRowContext := Nat × Nat

def setCoveringChoicePairListEncodedType : EncodedType :=
  vertexPairListEncodedType

def setCoveringChoicePairRowInstructionEncodedType : EncodedType :=
  EncodedType.sum setCoveringChoicePairRowContextEncodedType EncodedType.nat

def setCoveringChoicePairRowInstructionListEncodedType : EncodedType :=
  EncodedType.list setCoveringChoicePairRowInstructionEncodedType

def setCoveringChoicePairRowAccEncodedType : EncodedType :=
  EncodedType.prod setCoveringChoicePairRowContextEncodedType
    setCoveringChoicePairListEncodedType

def setCoveringChoicePairRowZeroContext : SetCoveringChoicePairRowContext :=
  (0, 0)

def setCoveringChoicePairRowInitAcc :
    setCoveringChoicePairRowAccEncodedType.Carrier :=
  (setCoveringChoicePairRowZeroContext, [])

def setCoveringChoicePairRowInitInstruction
    (ctx : SetCoveringChoicePairRowContext) :
    setCoveringChoicePairRowInstructionEncodedType.Carrier :=
  Sum.inl ctx

def setCoveringChoicePairRowIndexInstruction
    (choice : Nat) :
    setCoveringChoicePairRowInstructionEncodedType.Carrier :=
  Sum.inr choice

def setCoveringChoicePairRowInstructions
    (ctx : SetCoveringChoicePairRowContext) :
    List setCoveringChoicePairRowInstructionEncodedType.Carrier :=
  setCoveringChoicePairRowInitInstruction ctx ::
    (List.range ctx.2).map setCoveringChoicePairRowIndexInstruction

def setCoveringChoicePairOfRowContext
    (ctx : SetCoveringChoicePairRowContext) (choice : Nat) : Nat × Nat :=
  (ctx.1, choice)

def setCoveringChoicePairRowStep
    (p : setCoveringChoicePairRowAccEncodedType.Carrier ×
      setCoveringChoicePairRowInstructionEncodedType.Carrier) :
    setCoveringChoicePairRowAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl ctx => (ctx, [])
  | Sum.inr choice =>
      (p.1.1, (show List (Nat × Nat) from p.1.2) ++
        [setCoveringChoicePairOfRowContext p.1.1 choice])

def setCoveringChoicePairRowFromInstructions
    (xs : List setCoveringChoicePairRowInstructionEncodedType.Carrier) :
    List (Nat × Nat) :=
  (xs.foldl (fun acc instr => setCoveringChoicePairRowStep (acc, instr))
    setCoveringChoicePairRowInitAcc).2

def setCoveringChoicePairRowExecutable
    (ctx : SetCoveringChoicePairRowContext) : List (Nat × Nat) :=
  setCoveringChoicePairRowFromInstructions
    (setCoveringChoicePairRowInstructions ctx)

theorem setCoveringChoicePairRowIndexFold_eq_append_map
    (ctx : SetCoveringChoicePairRowContext) (xs : List Nat)
    (out : List (Nat × Nat)) :
    ((xs.map setCoveringChoicePairRowIndexInstruction).foldl
        (fun acc instr => setCoveringChoicePairRowStep (acc, instr)) (ctx, out)).2 =
      out ++ xs.map (setCoveringChoicePairOfRowContext ctx) := by
  induction xs generalizing out with
  | nil =>
      simp
  | cons choice rest ih =>
      rw [List.map_cons, List.foldl_cons]
      simp [setCoveringChoicePairRowIndexInstruction, setCoveringChoicePairRowStep]
      have hTail := ih (out ++ [setCoveringChoicePairOfRowContext ctx choice])
      simpa [List.append_assoc] using hTail

theorem setCoveringChoicePairRowExecutable_eq_map
    (ctx : SetCoveringChoicePairRowContext) :
    setCoveringChoicePairRowExecutable ctx =
      (List.range ctx.2).map (setCoveringChoicePairOfRowContext ctx) := by
  change
    (((List.range ctx.2).map setCoveringChoicePairRowIndexInstruction).foldl
        (fun acc instr => setCoveringChoicePairRowStep (acc, instr)) (ctx, [])).2 =
      (List.range ctx.2).map (setCoveringChoicePairOfRowContext ctx)
  simpa using
    setCoveringChoicePairRowIndexFold_eq_append_map ctx (List.range ctx.2) []

theorem setCoveringChoicePairRowInitInstruction_tm_polytime :
    TMPolyTimeMap
      setCoveringChoicePairRowContextEncodedType
      setCoveringChoicePairRowInstructionEncodedType
      setCoveringChoicePairRowInitInstruction := by
  simpa [setCoveringChoicePairRowInstructionEncodedType,
    setCoveringChoicePairRowInitInstruction] using
    TMPolyTimeMap.inl setCoveringChoicePairRowContextEncodedType EncodedType.nat

theorem setCoveringChoicePairRowIndexInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      setCoveringChoicePairRowInstructionEncodedType
      setCoveringChoicePairRowIndexInstruction := by
  simpa [setCoveringChoicePairRowInstructionEncodedType,
    setCoveringChoicePairRowIndexInstruction] using
    TMPolyTimeMap.inr setCoveringChoicePairRowContextEncodedType EncodedType.nat

theorem setCoveringChoicePairRowInstructions_tm_polytime :
    TMPolyTimeMap
      setCoveringChoicePairRowContextEncodedType
      setCoveringChoicePairRowInstructionListEncodedType
      setCoveringChoicePairRowInstructions := by
  let X := setCoveringChoicePairRowContextEncodedType
  have hCtx : TMPolyTimeMap X X (fun ctx : X.Carrier => ctx) := TMPolyTimeMap.id X
  have hChoiceCount : TMPolyTimeMap X EncodedType.nat (fun ctx : X.Carrier => ctx.2) := by
    simpa [X, setCoveringChoicePairRowContextEncodedType, vertexPairEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hInit :
      TMPolyTimeMap X setCoveringChoicePairRowInstructionEncodedType
        (fun ctx : X.Carrier => setCoveringChoicePairRowInitInstruction ctx) := by
    have hComp := TMPolyTimeMap.comp setCoveringChoicePairRowInitInstruction_tm_polytime hCtx
    simpa [Function.comp, X] using hComp
  have hRange :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun ctx : X.Carrier => List.range ctx.2) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hChoiceCount
    simpa [Function.comp, X] using hComp
  have hIndexInstructions :
      TMPolyTimeMap X setCoveringChoicePairRowInstructionListEncodedType
        (fun ctx : X.Carrier =>
          (List.range ctx.2).map setCoveringChoicePairRowIndexInstruction) := by
    have hMap := TMPolyTimeMap.list_map setCoveringChoicePairRowIndexInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, setCoveringChoicePairRowInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod setCoveringChoicePairRowInstructionEncodedType
          setCoveringChoicePairRowInstructionListEncodedType)
        (fun ctx : X.Carrier =>
          (setCoveringChoicePairRowInitInstruction ctx,
            (List.range ctx.2).map setCoveringChoicePairRowIndexInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hIndexInstructions
  have hCons :=
    TMPolyTimeMap.comp
      (TMPolyTimeMap.list_cons setCoveringChoicePairRowInstructionEncodedType)
      hConsInput
  simpa [Function.comp, setCoveringChoicePairRowInstructions,
    setCoveringChoicePairRowInstructionListEncodedType, X] using hCons

theorem setCoveringChoicePairRowStepLeft_tm_polytime :
    TMPolyTimeMap
      setCoveringChoicePairRowContextEncodedType
      setCoveringChoicePairRowAccEncodedType
      (fun ctx : SetCoveringChoicePairRowContext =>
        (ctx, ([] : List (Nat × Nat)))) := by
  have hCtx := TMPolyTimeMap.id setCoveringChoicePairRowContextEncodedType
  have hEmpty :
      TMPolyTimeMap setCoveringChoicePairRowContextEncodedType
        setCoveringChoicePairListEncodedType
        (fun _ : SetCoveringChoicePairRowContext => ([] : List (Nat × Nat))) :=
    TMPolyTimeMap.const setCoveringChoicePairRowContextEncodedType
      setCoveringChoicePairListEncodedType []
  simpa [setCoveringChoicePairRowAccEncodedType] using TMPolyTimeMap.prod_mk hCtx hEmpty

theorem setCoveringChoicePairRowStepRight_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setCoveringChoicePairRowAccEncodedType EncodedType.nat)
      setCoveringChoicePairRowAccEncodedType
      (fun p : setCoveringChoicePairRowAccEncodedType.Carrier × Nat =>
        (p.1.1, (show List (Nat × Nat) from p.1.2) ++
          [setCoveringChoicePairOfRowContext p.1.1 p.2])) := by
  let X := EncodedType.prod setCoveringChoicePairRowAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X setCoveringChoicePairRowAccEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst setCoveringChoicePairRowAccEncodedType EncodedType.nat
  have hChoice : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd setCoveringChoicePairRowAccEncodedType EncodedType.nat
  have hCtx :
      TMPolyTimeMap X setCoveringChoicePairRowContextEncodedType
        (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst setCoveringChoicePairRowContextEncodedType
      setCoveringChoicePairListEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, setCoveringChoicePairRowAccEncodedType, X] using hComp
  have hOut :
      TMPolyTimeMap X setCoveringChoicePairListEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd setCoveringChoicePairRowContextEncodedType
      setCoveringChoicePairListEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, setCoveringChoicePairRowAccEncodedType, X] using hComp
  have hSlot : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hCtx
    simpa [Function.comp, setCoveringChoicePairRowContextEncodedType,
      vertexPairEncodedType, X] using hComp
  have hElem :
      TMPolyTimeMap X vertexPairEncodedType
        (fun p : X.Carrier => setCoveringChoicePairOfRowContext p.1.1 p.2) := by
    simpa [setCoveringChoicePairOfRowContext, vertexPairEncodedType] using
      TMPolyTimeMap.prod_mk hSlot hChoice
  have hSingleton :
      TMPolyTimeMap X setCoveringChoicePairListEncodedType
        (fun p : X.Carrier => [setCoveringChoicePairOfRowContext p.1.1 p.2]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton vertexPairEncodedType) hElem
    simpa [Function.comp, setCoveringChoicePairListEncodedType,
      vertexPairListEncodedType] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod setCoveringChoicePairListEncodedType
          setCoveringChoicePairListEncodedType)
        (fun p : X.Carrier =>
          ((show List (Nat × Nat) from p.1.2),
            [setCoveringChoicePairOfRowContext p.1.1 p.2])) :=
    TMPolyTimeMap.prod_mk hOut hSingleton
  have hAppend :
      TMPolyTimeMap X setCoveringChoicePairListEncodedType
        (fun p : X.Carrier =>
          (show List (Nat × Nat) from p.1.2) ++
            [setCoveringChoicePairOfRowContext p.1.1 p.2]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append vertexPairEncodedType) hAppendInput
    simpa [Function.comp, setCoveringChoicePairListEncodedType,
      vertexPairListEncodedType, X] using hComp
  simpa [setCoveringChoicePairRowAccEncodedType] using TMPolyTimeMap.prod_mk hCtx hAppend

theorem setCoveringChoicePairRowStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setCoveringChoicePairRowAccEncodedType
        setCoveringChoicePairRowInstructionEncodedType)
      setCoveringChoicePairRowAccEncodedType
      setCoveringChoicePairRowStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      setCoveringChoicePairRowAccEncodedType
      setCoveringChoicePairRowContextEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim setCoveringChoicePairRowStepLeft_tm_polytime
      setCoveringChoicePairRowStepRight_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

def setCoveringChoicePairRowFoldInv (N : Nat)
    (acc : setCoveringChoicePairRowAccEncodedType.Carrier) : Prop :=
  acc = setCoveringChoicePairRowInitAcc ∨
    acc.1 = setCoveringChoicePairRowZeroContext ∨
    setCoveringChoicePairRowContextEncodedType.inputSize acc.1 ≤ N

noncomputable def setCoveringChoicePairRowFoldBase : Polynomial Nat :=
  Polynomial.C 20

noncomputable def setCoveringChoicePairRowFoldGrow : Polynomial Nat :=
  Polynomial.C 10 * Polynomial.X + Polynomial.C 50

@[simp] theorem setCoveringChoicePairRowFoldGrow_eval (N : Nat) :
    setCoveringChoicePairRowFoldGrow.eval N = 10 * N + 50 := by
  simp [setCoveringChoicePairRowFoldGrow, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

theorem setCoveringChoicePairRowInitAcc_bound
    (xs : List setCoveringChoicePairRowInstructionEncodedType.Carrier) :
    setCoveringChoicePairRowFoldInv
        (setCoveringChoicePairRowInstructionListEncodedType.inputSize xs)
        setCoveringChoicePairRowInitAcc ∧
      setCoveringChoicePairRowAccEncodedType.inputSize setCoveringChoicePairRowInitAcc ≤
        setCoveringChoicePairRowFoldBase.eval
          (setCoveringChoicePairRowInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · simp [setCoveringChoicePairRowFoldBase]
    native_decide

theorem setCoveringChoicePairOfRowContext_inputSize_le
    {N : Nat} {ctx : SetCoveringChoicePairRowContext} {choice : Nat}
    (hCtx : setCoveringChoicePairRowContextEncodedType.inputSize ctx ≤ N)
    (hChoice : EncodedType.nat.inputSize choice ≤ N) :
    vertexPairEncodedType.inputSize (setCoveringChoicePairOfRowContext ctx choice) ≤
      2 * N + 3 := by
  rcases ctx with ⟨slot, choiceCount⟩
  simp [setCoveringChoicePairOfRowContext, setCoveringChoicePairRowContextEncodedType,
    vertexPairEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_nat] at hCtx hChoice ⊢
  omega

theorem setCoveringChoicePairOfZeroRowContext_inputSize_le
    {N choice : Nat} (hChoice : EncodedType.nat.inputSize choice ≤ N) :
    vertexPairEncodedType.inputSize
        (setCoveringChoicePairOfRowContext setCoveringChoicePairRowZeroContext choice) ≤
      2 * N + 3 := by
  simp [setCoveringChoicePairOfRowContext, setCoveringChoicePairRowZeroContext,
    vertexPairEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_nat] at hChoice ⊢
  omega

theorem setCoveringChoicePairRowStep_growth
    (source : List setCoveringChoicePairRowInstructionEncodedType.Carrier)
    (acc : setCoveringChoicePairRowAccEncodedType.Carrier)
    (instr : setCoveringChoicePairRowInstructionEncodedType.Carrier)
    (hInv :
      setCoveringChoicePairRowFoldInv
        (setCoveringChoicePairRowInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      setCoveringChoicePairRowInstructionEncodedType.inputSize instr ≤
        setCoveringChoicePairRowInstructionListEncodedType.inputSize source) :
    setCoveringChoicePairRowFoldInv
        (setCoveringChoicePairRowInstructionListEncodedType.inputSize source)
        (setCoveringChoicePairRowStep (acc, instr)) ∧
      setCoveringChoicePairRowAccEncodedType.inputSize
          (setCoveringChoicePairRowStep (acc, instr)) ≤
        setCoveringChoicePairRowAccEncodedType.inputSize acc +
          setCoveringChoicePairRowFoldGrow.eval
            (setCoveringChoicePairRowInstructionListEncodedType.inputSize source) := by
  let N := setCoveringChoicePairRowInstructionListEncodedType.inputSize source
  rcases acc with ⟨ctx, out⟩
  cases instr with
  | inl newCtx =>
      have hNewCtx : setCoveringChoicePairRowContextEncodedType.inputSize newCtx ≤ N := by
        exact Nat.le_of_lt (by
          simpa [N, setCoveringChoicePairRowInstructionEncodedType,
            EncodedType.inputSize, EncodedType.sum] using hInstr)
      constructor
      · exact Or.inr (Or.inr hNewCtx)
      · have hNewAcc :
            setCoveringChoicePairRowAccEncodedType.inputSize
                (newCtx, ([] : List (Nat × Nat))) ≤ N + 1 := by
          have hEmpty :
              setCoveringChoicePairListEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
            change (EncodedType.list vertexPairEncodedType).inputSize ([] : List (Nat × Nat)) = 0
            exact EncodedType.inputSize_list_nil vertexPairEncodedType
          simp [setCoveringChoicePairRowAccEncodedType, EncodedType.inputSize_prod,
            hEmpty]
          omega
        have hPoly :
            N + 1 ≤ setCoveringChoicePairRowAccEncodedType.inputSize (ctx, out) +
              setCoveringChoicePairRowFoldGrow.eval N := by
          rw [setCoveringChoicePairRowFoldGrow_eval]
          omega
        simpa [setCoveringChoicePairRowStep, N] using hNewAcc.trans hPoly
  | inr choice =>
      have hChoice : EncodedType.nat.inputSize choice ≤ N := by
        exact Nat.le_of_lt (by
          simpa [N, setCoveringChoicePairRowInstructionEncodedType,
            EncodedType.inputSize, EncodedType.sum] using hInstr)
      have hElem :
          vertexPairEncodedType.inputSize
              (setCoveringChoicePairOfRowContext ctx choice) ≤ 2 * N + 3 := by
        rcases hInv with hInit | hRest
        · injection hInit with hCtxEq _hOut
          rw [hCtxEq]
          exact setCoveringChoicePairOfZeroRowContext_inputSize_le (N := N) hChoice
        · rcases hRest with hZero | hCtx
          · have hCtxZero : ctx = setCoveringChoicePairRowZeroContext := by
              simpa using hZero
            rw [hCtxZero]
            exact setCoveringChoicePairOfZeroRowContext_inputSize_le (N := N) hChoice
          · exact setCoveringChoicePairOfRowContext_inputSize_le hCtx hChoice
      have hSingleton :
          setCoveringChoicePairListEncodedType.inputSize
              [setCoveringChoicePairOfRowContext ctx choice] ≤ 2 * N + 5 := by
        simp [setCoveringChoicePairListEncodedType, vertexPairListEncodedType,
          EncodedType.inputSize_list_cons, EncodedType.inputSize_list_nil] at hElem ⊢
        omega
      have hAppend :
          setCoveringChoicePairListEncodedType.inputSize
              ((show List (Nat × Nat) from out) ++
                [setCoveringChoicePairOfRowContext ctx choice]) =
            setCoveringChoicePairListEncodedType.inputSize out +
              setCoveringChoicePairListEncodedType.inputSize
                [setCoveringChoicePairOfRowContext ctx choice] := by
        simpa [setCoveringChoicePairListEncodedType, vertexPairListEncodedType] using
          list_inputSize_append vertexPairEncodedType out
            [setCoveringChoicePairOfRowContext ctx choice]
      constructor
      ·
        rcases hInv with hInit | hRest
        · injection hInit with hCtxEq _hOut
          exact Or.inr (Or.inl hCtxEq)
        · exact Or.inr hRest
      · change
          setCoveringChoicePairRowAccEncodedType.inputSize
              (ctx, (show List (Nat × Nat) from out) ++
                [setCoveringChoicePairOfRowContext ctx choice]) ≤
            setCoveringChoicePairRowAccEncodedType.inputSize (ctx, out) +
              setCoveringChoicePairRowFoldGrow.eval N
        simp [setCoveringChoicePairRowAccEncodedType, EncodedType.inputSize_prod] at hAppend ⊢
        rw [hAppend]
        omega

theorem setCoveringChoicePairRowFold_tm_polytime :
    TMPolyTimeMap
      setCoveringChoicePairRowInstructionListEncodedType
      setCoveringChoicePairRowAccEncodedType
      (fun xs : List setCoveringChoicePairRowInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => setCoveringChoicePairRowStep (acc, instr))
          setCoveringChoicePairRowInitAcc) := by
  rcases setCoveringChoicePairRowStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      setCoveringChoicePairRowInstructionEncodedType setCoveringChoicePairRowAccEncodedType
      setCoveringChoicePairRowStep setCoveringChoicePairRowInitAcc hStep
      setCoveringChoicePairRowFoldBase setCoveringChoicePairRowFoldGrow
      setCoveringChoicePairRowFoldInv ?_ ?_
  · intro xs
    exact setCoveringChoicePairRowInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact setCoveringChoicePairRowStep_growth source acc instr hInv hInstr

theorem setCoveringChoicePairRowFromInstructions_tm_polytime :
    TMPolyTimeMap
      setCoveringChoicePairRowInstructionListEncodedType
      setCoveringChoicePairListEncodedType
      setCoveringChoicePairRowFromInstructions := by
  have hFold := setCoveringChoicePairRowFold_tm_polytime
  have hOut :=
    TMPolyTimeMap.snd setCoveringChoicePairRowContextEncodedType
      setCoveringChoicePairListEncodedType
  have hComp := TMPolyTimeMap.comp hOut hFold
  simpa [Function.comp, setCoveringChoicePairRowFromInstructions,
    setCoveringChoicePairRowAccEncodedType] using hComp

theorem setCoveringChoicePairRowExecutable_tm_polytime :
    TMPolyTimeMap
      setCoveringChoicePairRowContextEncodedType
      setCoveringChoicePairListEncodedType
      setCoveringChoicePairRowExecutable := by
  have hComp :=
    TMPolyTimeMap.comp setCoveringChoicePairRowFromInstructions_tm_polytime
      setCoveringChoicePairRowInstructions_tm_polytime
  simpa [Function.comp, setCoveringChoicePairRowExecutable] using hComp

def setCoveringSlotAtLeastClauseExecutable
    (ctx : SetCoveringChoicePairRowContext) : SAT.Clause :=
  (setCoveringChoicePairRowExecutable ctx).map setCoveringChoiceLitFromPair

theorem setCoveringSlotAtLeastClauseExecutable_eq
    (I : SetCoveringInput) (slot : Nat) :
    setCoveringSlotAtLeastClauseExecutable (slot, setCoveringChoiceCount I) =
      setCoveringSlotAtLeastClause I slot := by
  rw [setCoveringSlotAtLeastClauseExecutable, setCoveringChoicePairRowExecutable_eq_map]
  simp only [setCoveringSlotAtLeastClause]
  rw [List.map_map]
  apply List.map_congr_left
  intro choice _hchoice
  simp [setCoveringChoicePairOfRowContext, setCoveringChoiceLitFromPair,
    setCoveringChoiceLit, setCoveringChoiceVar]

theorem setCoveringSlotAtLeastClauseExecutable_tm_polytime :
    TMPolyTimeMap
      setCoveringChoicePairRowContextEncodedType
      clauseStructuredEncodedType
      setCoveringSlotAtLeastClauseExecutable := by
  have hPairs := setCoveringChoicePairRowExecutable_tm_polytime
  have hMap := TMPolyTimeMap.list_map setCoveringChoiceLitFromPair_tm_polytime
  have hComp := TMPolyTimeMap.comp hMap hPairs
  simpa [Function.comp, setCoveringSlotAtLeastClauseExecutable,
    setCoveringChoicePairListEncodedType, vertexPairListEncodedType,
    clauseStructuredEncodedType] using hComp

end ExactCover
end Karp21
end ComplexityReduction
