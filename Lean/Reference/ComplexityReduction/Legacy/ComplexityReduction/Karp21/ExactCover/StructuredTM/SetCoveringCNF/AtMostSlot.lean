import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.AtMostChoice

namespace ComplexityReduction
namespace Karp21
namespace ExactCover

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
Executable at-most-one clauses for one fixed set-covering slot.

For context `(slot, choiceCount)`, this runner scans
`choice ∈ List.range choiceCount` and appends the direct per-choice executable
from `AtMostChoice`.
-/

def setCoveringAtMostSlotInstructionEncodedType : EncodedType :=
  EncodedType.sum setCoveringChoicePairRowContextEncodedType EncodedType.nat

def setCoveringAtMostSlotInstructionListEncodedType : EncodedType :=
  EncodedType.list setCoveringAtMostSlotInstructionEncodedType

def setCoveringAtMostSlotAccEncodedType : EncodedType :=
  EncodedType.prod setCoveringChoicePairRowContextEncodedType cnfStructuredEncodedType

def setCoveringAtMostSlotZeroContext : SetCoveringChoicePairRowContext :=
  (0, 0)

def setCoveringAtMostSlotInitAcc :
    setCoveringAtMostSlotAccEncodedType.Carrier :=
  (setCoveringAtMostSlotZeroContext, [])

def setCoveringAtMostSlotInitInstruction
    (ctx : SetCoveringChoicePairRowContext) :
    setCoveringAtMostSlotInstructionEncodedType.Carrier :=
  Sum.inl ctx

def setCoveringAtMostSlotChoiceInstruction
    (choice : Nat) :
    setCoveringAtMostSlotInstructionEncodedType.Carrier :=
  Sum.inr choice

def setCoveringAtMostSlotInstructions
    (ctx : SetCoveringChoicePairRowContext) :
    List setCoveringAtMostSlotInstructionEncodedType.Carrier :=
  setCoveringAtMostSlotInitInstruction ctx ::
    (List.range ctx.2).map setCoveringAtMostSlotChoiceInstruction

def setCoveringAtMostSlotChoiceContext
    (ctx : SetCoveringChoicePairRowContext) (choice : Nat) :
    SetCoveringAtMostChoiceContext :=
  ((ctx.1, ctx.2), choice)

def setCoveringAtMostSlotStep
    (p : setCoveringAtMostSlotAccEncodedType.Carrier ×
      setCoveringAtMostSlotInstructionEncodedType.Carrier) :
    setCoveringAtMostSlotAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl ctx => (ctx, [])
  | Sum.inr choice =>
      (p.1.1, (show SAT.CNF from p.1.2) ++
        setCoveringAtMostChoiceExecutable
          (setCoveringAtMostSlotChoiceContext p.1.1 choice))

def setCoveringAtMostSlotFromInstructions
    (xs : List setCoveringAtMostSlotInstructionEncodedType.Carrier) :
    SAT.CNF :=
  (xs.foldl (fun acc instr => setCoveringAtMostSlotStep (acc, instr))
    setCoveringAtMostSlotInitAcc).2

def setCoveringAtMostSlotExecutable
    (ctx : SetCoveringChoicePairRowContext) : SAT.CNF :=
  setCoveringAtMostSlotFromInstructions (setCoveringAtMostSlotInstructions ctx)

/-! ### Semantics -/

theorem setCoveringAtMostSlotIndexFold_eq_append_flatMap
    (ctx : SetCoveringChoicePairRowContext) (xs : List Nat)
    (out : SAT.CNF) :
    ((xs.map setCoveringAtMostSlotChoiceInstruction).foldl
        (fun acc instr => setCoveringAtMostSlotStep (acc, instr)) (ctx, out)).2 =
      out ++ xs.flatMap fun choice =>
        setCoveringAtMostChoiceExecutable
          (setCoveringAtMostSlotChoiceContext ctx choice) := by
  induction xs generalizing out with
  | nil =>
      simp
  | cons choice rest ih =>
      rw [List.map_cons, List.foldl_cons]
      simpa [setCoveringAtMostSlotChoiceInstruction, setCoveringAtMostSlotStep,
        List.append_assoc] using
        ih (out ++
          setCoveringAtMostChoiceExecutable
            (setCoveringAtMostSlotChoiceContext ctx choice))

theorem setCoveringAtMostSlotExecutable_eq_flatMap
    (ctx : SetCoveringChoicePairRowContext) :
    setCoveringAtMostSlotExecutable ctx =
      (List.range ctx.2).flatMap fun choice =>
        setCoveringAtMostChoiceExecutable
          (setCoveringAtMostSlotChoiceContext ctx choice) := by
  change
    (((List.range ctx.2).map setCoveringAtMostSlotChoiceInstruction).foldl
        (fun acc instr => setCoveringAtMostSlotStep (acc, instr)) (ctx, [])).2 =
      (List.range ctx.2).flatMap fun choice =>
        setCoveringAtMostChoiceExecutable
          (setCoveringAtMostSlotChoiceContext ctx choice)
  simpa using
    setCoveringAtMostSlotIndexFold_eq_append_flatMap ctx (List.range ctx.2) []

theorem setCoveringAtMostSlotExecutable_eq
    (I : SetCoveringInput) (slot : Nat) :
    setCoveringAtMostSlotExecutable (slot, setCoveringChoiceCount I) =
      setCoveringSlotAtMostClauses I slot := by
  rw [setCoveringAtMostSlotExecutable_eq_flatMap, setCoveringSlotAtMostClauses]
  apply List.flatMap_congr
  intro choice _hchoice
  exact setCoveringAtMostChoiceExecutable_eq I slot choice

/-! ### TM witnesses -/

theorem setCoveringAtMostSlotInitInstruction_tm_polytime :
    TMPolyTimeMap
      setCoveringChoicePairRowContextEncodedType
      setCoveringAtMostSlotInstructionEncodedType
      setCoveringAtMostSlotInitInstruction := by
  simpa [setCoveringAtMostSlotInstructionEncodedType,
    setCoveringAtMostSlotInitInstruction] using
    TMPolyTimeMap.inl setCoveringChoicePairRowContextEncodedType EncodedType.nat

theorem setCoveringAtMostSlotChoiceInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      setCoveringAtMostSlotInstructionEncodedType
      setCoveringAtMostSlotChoiceInstruction := by
  simpa [setCoveringAtMostSlotInstructionEncodedType,
    setCoveringAtMostSlotChoiceInstruction] using
    TMPolyTimeMap.inr setCoveringChoicePairRowContextEncodedType EncodedType.nat

theorem setCoveringAtMostSlotInstructions_tm_polytime :
    TMPolyTimeMap
      setCoveringChoicePairRowContextEncodedType
      setCoveringAtMostSlotInstructionListEncodedType
      setCoveringAtMostSlotInstructions := by
  let X := setCoveringChoicePairRowContextEncodedType
  have hCtx : TMPolyTimeMap X X (fun ctx : X.Carrier => ctx) := TMPolyTimeMap.id X
  have hChoiceCount : TMPolyTimeMap X EncodedType.nat (fun ctx : X.Carrier => ctx.2) := by
    simpa [X, setCoveringChoicePairRowContextEncodedType, vertexPairEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hInit :
      TMPolyTimeMap X setCoveringAtMostSlotInstructionEncodedType
        (fun ctx : X.Carrier => setCoveringAtMostSlotInitInstruction ctx) := by
    have hComp := TMPolyTimeMap.comp setCoveringAtMostSlotInitInstruction_tm_polytime hCtx
    simpa [Function.comp, X] using hComp
  have hRange :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun ctx : X.Carrier => List.range ctx.2) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hChoiceCount
    simpa [Function.comp, X] using hComp
  have hChoiceInstructions :
      TMPolyTimeMap X setCoveringAtMostSlotInstructionListEncodedType
        (fun ctx : X.Carrier =>
          (List.range ctx.2).map setCoveringAtMostSlotChoiceInstruction) := by
    have hMap := TMPolyTimeMap.list_map setCoveringAtMostSlotChoiceInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, setCoveringAtMostSlotInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod setCoveringAtMostSlotInstructionEncodedType
          setCoveringAtMostSlotInstructionListEncodedType)
        (fun ctx : X.Carrier =>
          (setCoveringAtMostSlotInitInstruction ctx,
            (List.range ctx.2).map setCoveringAtMostSlotChoiceInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hChoiceInstructions
  have hCons :=
    TMPolyTimeMap.comp
      (TMPolyTimeMap.list_cons setCoveringAtMostSlotInstructionEncodedType)
      hConsInput
  simpa [Function.comp, setCoveringAtMostSlotInstructions,
    setCoveringAtMostSlotInstructionListEncodedType, X] using hCons

theorem setCoveringAtMostSlotStepLeft_tm_polytime :
    TMPolyTimeMap
      setCoveringChoicePairRowContextEncodedType
      setCoveringAtMostSlotAccEncodedType
      (fun ctx : SetCoveringChoicePairRowContext => (ctx, ([] : SAT.CNF))) := by
  have hCtx := TMPolyTimeMap.id setCoveringChoicePairRowContextEncodedType
  have hEmpty :
      TMPolyTimeMap setCoveringChoicePairRowContextEncodedType
        cnfStructuredEncodedType
        (fun _ : SetCoveringChoicePairRowContext => ([] : SAT.CNF)) :=
    TMPolyTimeMap.const setCoveringChoicePairRowContextEncodedType
      cnfStructuredEncodedType []
  simpa [setCoveringAtMostSlotAccEncodedType] using TMPolyTimeMap.prod_mk hCtx hEmpty

theorem setCoveringAtMostSlotStepRight_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setCoveringAtMostSlotAccEncodedType EncodedType.nat)
      setCoveringAtMostSlotAccEncodedType
      (fun p : setCoveringAtMostSlotAccEncodedType.Carrier × Nat =>
        (p.1.1, (show SAT.CNF from p.1.2) ++
          setCoveringAtMostChoiceExecutable
            (setCoveringAtMostSlotChoiceContext p.1.1 p.2))) := by
  let X := EncodedType.prod setCoveringAtMostSlotAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X setCoveringAtMostSlotAccEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst setCoveringAtMostSlotAccEncodedType EncodedType.nat
  have hChoice : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd setCoveringAtMostSlotAccEncodedType EncodedType.nat
  have hCtx :
      TMPolyTimeMap X setCoveringChoicePairRowContextEncodedType
        (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst setCoveringChoicePairRowContextEncodedType
      cnfStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, setCoveringAtMostSlotAccEncodedType, X] using hComp
  have hOut :
      TMPolyTimeMap X cnfStructuredEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd setCoveringChoicePairRowContextEncodedType
      cnfStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, setCoveringAtMostSlotAccEncodedType, X] using hComp
  have hSlot : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hCtx
    simpa [Function.comp, setCoveringChoicePairRowContextEncodedType,
      vertexPairEncodedType, X] using hComp
  have hChoiceCount :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, setCoveringChoicePairRowContextEncodedType,
      vertexPairEncodedType, X] using hComp
  have hRow :
      TMPolyTimeMap X vertexPairEncodedType
        (fun p : X.Carrier => (p.1.1.1, p.1.1.2)) := by
    simpa [vertexPairEncodedType] using TMPolyTimeMap.prod_mk hSlot hChoiceCount
  have hChoiceCtx :
      TMPolyTimeMap X setCoveringAtMostChoiceContextEncodedType
        (fun p : X.Carrier => setCoveringAtMostSlotChoiceContext p.1.1 p.2) := by
    simpa [setCoveringAtMostSlotChoiceContext, setCoveringAtMostChoiceContextEncodedType]
      using TMPolyTimeMap.prod_mk hRow hChoice
  have hBlock :
      TMPolyTimeMap X cnfStructuredEncodedType
        (fun p : X.Carrier =>
          setCoveringAtMostChoiceExecutable
            (setCoveringAtMostSlotChoiceContext p.1.1 p.2)) := by
    have hComp := TMPolyTimeMap.comp setCoveringAtMostChoiceExecutable_tm_polytime hChoiceCtx
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun p : X.Carrier =>
          ((show SAT.CNF from p.1.2),
            setCoveringAtMostChoiceExecutable
              (setCoveringAtMostSlotChoiceContext p.1.1 p.2))) :=
    TMPolyTimeMap.prod_mk hOut hBlock
  have hAppend :
      TMPolyTimeMap X cnfStructuredEncodedType
        (fun p : X.Carrier =>
          (show SAT.CNF from p.1.2) ++
            setCoveringAtMostChoiceExecutable
              (setCoveringAtMostSlotChoiceContext p.1.1 p.2)) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
      hAppendInput
    simpa [Function.comp, cnfStructuredEncodedType, X] using hComp
  simpa [setCoveringAtMostSlotAccEncodedType] using TMPolyTimeMap.prod_mk hCtx hAppend

theorem setCoveringAtMostSlotStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setCoveringAtMostSlotAccEncodedType
        setCoveringAtMostSlotInstructionEncodedType)
      setCoveringAtMostSlotAccEncodedType
      setCoveringAtMostSlotStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      setCoveringAtMostSlotAccEncodedType
      setCoveringChoicePairRowContextEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim setCoveringAtMostSlotStepLeft_tm_polytime
      setCoveringAtMostSlotStepRight_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

/-! ### Bounded fold certificate -/

def setCoveringAtMostSlotFoldInv (N : Nat)
    (acc : setCoveringAtMostSlotAccEncodedType.Carrier) : Prop :=
  acc = setCoveringAtMostSlotInitAcc ∨
    acc.1 = setCoveringAtMostSlotZeroContext ∨
    setCoveringChoicePairRowContextEncodedType.inputSize acc.1 ≤ N

noncomputable def setCoveringAtMostSlotFoldBase : Polynomial Nat :=
  Polynomial.C 30

noncomputable def setCoveringAtMostSlotFoldGrow : Polynomial Nat :=
  (Polynomial.C 2 * Polynomial.X + Polynomial.C 3) *
    (Polynomial.C 2 * (Polynomial.C 2 * Polynomial.X + Polynomial.C 3) ^ 2 +
      Polynomial.C 21)

@[simp] theorem setCoveringAtMostSlotFoldGrow_eval (N : Nat) :
    setCoveringAtMostSlotFoldGrow.eval N =
      (2 * N + 3) * (2 * (2 * N + 3) ^ 2 + 21) := by
  simp [setCoveringAtMostSlotFoldGrow, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X]

theorem setCoveringAtMostSlotInitAcc_bound
    (xs : List setCoveringAtMostSlotInstructionEncodedType.Carrier) :
    setCoveringAtMostSlotFoldInv
        (setCoveringAtMostSlotInstructionListEncodedType.inputSize xs)
        setCoveringAtMostSlotInitAcc ∧
      setCoveringAtMostSlotAccEncodedType.inputSize setCoveringAtMostSlotInitAcc ≤
        setCoveringAtMostSlotFoldBase.eval
          (setCoveringAtMostSlotInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · simp [setCoveringAtMostSlotFoldBase]
    native_decide

theorem setCoveringAtMostSlotChoiceContext_inputSize_le
    {N : Nat} {ctx : SetCoveringChoicePairRowContext} {choice : Nat}
    (hCtx : setCoveringChoicePairRowContextEncodedType.inputSize ctx ≤ N)
    (hChoice : EncodedType.nat.inputSize choice ≤ N) :
    setCoveringAtMostChoiceContextEncodedType.inputSize
        (setCoveringAtMostSlotChoiceContext ctx choice) ≤
      2 * N + 3 := by
  rcases ctx with ⟨slot, choiceCount⟩
  simp [setCoveringAtMostSlotChoiceContext, setCoveringAtMostChoiceContextEncodedType,
    setCoveringChoicePairRowContextEncodedType, vertexPairEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_nat] at hCtx hChoice ⊢
  omega

theorem setCoveringAtMostSlotChoiceContext_zero_inputSize_le
    {N choice : Nat} (hChoice : EncodedType.nat.inputSize choice ≤ N) :
    setCoveringAtMostChoiceContextEncodedType.inputSize
        (setCoveringAtMostSlotChoiceContext setCoveringAtMostSlotZeroContext choice) ≤
      2 * N + 3 := by
  simp [setCoveringAtMostSlotChoiceContext, setCoveringAtMostSlotZeroContext,
    setCoveringAtMostChoiceContextEncodedType, vertexPairEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_nat] at hChoice ⊢
  omega

theorem setCoveringAtMostSlotChoiceExecutable_inputSize_le
    {N : Nat} {ctx : SetCoveringChoicePairRowContext} {choice : Nat}
    (hCtx : setCoveringChoicePairRowContextEncodedType.inputSize ctx ≤ N)
    (hChoice : EncodedType.nat.inputSize choice ≤ N) :
    cnfStructuredEncodedType.inputSize
        (setCoveringAtMostChoiceExecutable
          (setCoveringAtMostSlotChoiceContext ctx choice)) ≤
      (2 * N + 3) * (2 * (2 * N + 3) ^ 2 + 21) := by
  have hChoiceCtx :=
    setCoveringAtMostSlotChoiceContext_inputSize_le (N := N) hCtx hChoice
  exact setCoveringAtMostChoiceExecutable_inputSize_le hChoiceCtx

theorem setCoveringAtMostSlotZeroChoiceExecutable_inputSize_le
    {N choice : Nat} (hChoice : EncodedType.nat.inputSize choice ≤ N) :
    cnfStructuredEncodedType.inputSize
        (setCoveringAtMostChoiceExecutable
          (setCoveringAtMostSlotChoiceContext setCoveringAtMostSlotZeroContext choice)) ≤
      (2 * N + 3) * (2 * (2 * N + 3) ^ 2 + 21) := by
  have hChoiceCtx :=
    setCoveringAtMostSlotChoiceContext_zero_inputSize_le (N := N) hChoice
  exact setCoveringAtMostChoiceExecutable_inputSize_le hChoiceCtx

theorem setCoveringAtMostSlotStep_growth
    (source : List setCoveringAtMostSlotInstructionEncodedType.Carrier)
    (acc : setCoveringAtMostSlotAccEncodedType.Carrier)
    (instr : setCoveringAtMostSlotInstructionEncodedType.Carrier)
    (hInv :
      setCoveringAtMostSlotFoldInv
        (setCoveringAtMostSlotInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      setCoveringAtMostSlotInstructionEncodedType.inputSize instr ≤
        setCoveringAtMostSlotInstructionListEncodedType.inputSize source) :
    setCoveringAtMostSlotFoldInv
        (setCoveringAtMostSlotInstructionListEncodedType.inputSize source)
        (setCoveringAtMostSlotStep (acc, instr)) ∧
      setCoveringAtMostSlotAccEncodedType.inputSize
          (setCoveringAtMostSlotStep (acc, instr)) ≤
        setCoveringAtMostSlotAccEncodedType.inputSize acc +
          setCoveringAtMostSlotFoldGrow.eval
            (setCoveringAtMostSlotInstructionListEncodedType.inputSize source) := by
  let N := setCoveringAtMostSlotInstructionListEncodedType.inputSize source
  rcases acc with ⟨ctx, out⟩
  cases instr with
  | inl newCtx =>
      have hNewCtx : setCoveringChoicePairRowContextEncodedType.inputSize newCtx ≤ N := by
        exact Nat.le_of_lt (by
          simpa [N, setCoveringAtMostSlotInstructionEncodedType,
            EncodedType.inputSize, EncodedType.sum] using hInstr)
      constructor
      · exact Or.inr (Or.inr hNewCtx)
      · have hEmpty :
            cnfStructuredEncodedType.inputSize ([] : SAT.CNF) = 0 := by
          change (EncodedType.list clauseStructuredEncodedType).inputSize ([] : SAT.CNF) = 0
          exact EncodedType.inputSize_list_nil clauseStructuredEncodedType
        have hNewAcc :
            setCoveringAtMostSlotAccEncodedType.inputSize (newCtx, ([] : SAT.CNF)) ≤
              N + 1 := by
          simp [setCoveringAtMostSlotAccEncodedType, EncodedType.inputSize_prod, hEmpty]
          omega
        have hPoly :
            N + 1 ≤ setCoveringAtMostSlotAccEncodedType.inputSize (ctx, out) +
              setCoveringAtMostSlotFoldGrow.eval N := by
          have hFirst : N + 1 ≤ 2 * N + 3 := by omega
          have hSecond : 0 < 2 * (2 * N + 3) ^ 2 + 21 := by
            have hNonneg : 0 ≤ 2 * (2 * N + 3) ^ 2 := Nat.zero_le _
            omega
          have hGrowLarge : N + 1 ≤ setCoveringAtMostSlotFoldGrow.eval N := by
            rw [setCoveringAtMostSlotFoldGrow_eval]
            exact hFirst.trans (Nat.le_mul_of_pos_right (2 * N + 3) hSecond)
          exact hGrowLarge.trans (Nat.le_add_left _ _)
        simpa [setCoveringAtMostSlotStep, N] using hNewAcc.trans hPoly
  | inr choice =>
      have hChoice : EncodedType.nat.inputSize choice ≤ N := by
        exact Nat.le_of_lt (by
          simpa [N, setCoveringAtMostSlotInstructionEncodedType,
            EncodedType.inputSize, EncodedType.sum] using hInstr)
      have hInvCtx :
          ctx = setCoveringAtMostSlotZeroContext ∨
            setCoveringChoicePairRowContextEncodedType.inputSize ctx ≤ N := by
        rcases hInv with hInit | hRest
        · injection hInit with hCtxEq _hOut
          exact Or.inl hCtxEq
        · exact hRest
      constructor
      · exact Or.inr hInvCtx
      · have hBlock :
            cnfStructuredEncodedType.inputSize
                (setCoveringAtMostChoiceExecutable
                  (setCoveringAtMostSlotChoiceContext ctx choice)) ≤
              (2 * N + 3) * (2 * (2 * N + 3) ^ 2 + 21) := by
          rcases hInvCtx with hZero | hCtxBound
          · rw [hZero]
            exact setCoveringAtMostSlotZeroChoiceExecutable_inputSize_le hChoice
          · exact setCoveringAtMostSlotChoiceExecutable_inputSize_le hCtxBound hChoice
        have hBlockGrow :
            cnfStructuredEncodedType.inputSize
                (setCoveringAtMostChoiceExecutable
                  (setCoveringAtMostSlotChoiceContext ctx choice)) ≤
              setCoveringAtMostSlotFoldGrow.eval N := by
          simpa [setCoveringAtMostSlotFoldGrow_eval] using hBlock
        have hAppend :
            cnfStructuredEncodedType.inputSize
                ((show SAT.CNF from out) ++
                  setCoveringAtMostChoiceExecutable
                    (setCoveringAtMostSlotChoiceContext ctx choice)) =
              cnfStructuredEncodedType.inputSize out +
                cnfStructuredEncodedType.inputSize
                  (setCoveringAtMostChoiceExecutable
                    (setCoveringAtMostSlotChoiceContext ctx choice)) := by
          simpa [cnfStructuredEncodedType] using
            list_inputSize_append clauseStructuredEncodedType out
              (setCoveringAtMostChoiceExecutable
                (setCoveringAtMostSlotChoiceContext ctx choice))
        change
          setCoveringAtMostSlotAccEncodedType.inputSize
              (ctx, (show SAT.CNF from out) ++
                setCoveringAtMostChoiceExecutable
                  (setCoveringAtMostSlotChoiceContext ctx choice)) ≤
            setCoveringAtMostSlotAccEncodedType.inputSize (ctx, out) +
              setCoveringAtMostSlotFoldGrow.eval N
        simp [setCoveringAtMostSlotAccEncodedType, EncodedType.inputSize_prod] at hAppend ⊢
        rw [hAppend]
        nlinarith [hBlockGrow]

theorem setCoveringAtMostSlotFold_tm_polytime :
    TMPolyTimeMap
      setCoveringAtMostSlotInstructionListEncodedType
      setCoveringAtMostSlotAccEncodedType
      (fun xs : List setCoveringAtMostSlotInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => setCoveringAtMostSlotStep (acc, instr))
          setCoveringAtMostSlotInitAcc) := by
  rcases setCoveringAtMostSlotStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      setCoveringAtMostSlotInstructionEncodedType setCoveringAtMostSlotAccEncodedType
      setCoveringAtMostSlotStep setCoveringAtMostSlotInitAcc hStep
      setCoveringAtMostSlotFoldBase setCoveringAtMostSlotFoldGrow
      setCoveringAtMostSlotFoldInv ?_ ?_
  · intro xs
    exact setCoveringAtMostSlotInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact setCoveringAtMostSlotStep_growth source acc instr hInv hInstr

theorem setCoveringAtMostSlotFromInstructions_tm_polytime :
    TMPolyTimeMap
      setCoveringAtMostSlotInstructionListEncodedType
      cnfStructuredEncodedType
      setCoveringAtMostSlotFromInstructions := by
  have hFold := setCoveringAtMostSlotFold_tm_polytime
  have hOut :=
    TMPolyTimeMap.snd setCoveringChoicePairRowContextEncodedType cnfStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hOut hFold
  simpa [Function.comp, setCoveringAtMostSlotFromInstructions,
    setCoveringAtMostSlotAccEncodedType] using hComp

theorem setCoveringAtMostSlotExecutable_tm_polytime :
    TMPolyTimeMap
      setCoveringChoicePairRowContextEncodedType
      cnfStructuredEncodedType
      setCoveringAtMostSlotExecutable := by
  have hComp :=
    TMPolyTimeMap.comp setCoveringAtMostSlotFromInstructions_tm_polytime
      setCoveringAtMostSlotInstructions_tm_polytime
  simpa [Function.comp, setCoveringAtMostSlotExecutable] using hComp

/-! ### Output-size lemmas for the next fold layer -/

theorem cnfStructured_inputSize_flatMap_le
    {α : Type*} {xs : List α} {f : α → SAT.CNF} {B : Nat}
    (hBlock : ∀ x ∈ xs, cnfStructuredEncodedType.inputSize (f x) ≤ B) :
    cnfStructuredEncodedType.inputSize (xs.flatMap f) ≤ xs.length * B := by
  induction xs with
  | nil =>
      simp [cnfStructuredEncodedType, EncodedType.inputSize_list_nil]
  | cons x rest ih =>
      have hx : cnfStructuredEncodedType.inputSize (f x) ≤ B := hBlock x (by simp)
      have hrest : ∀ y ∈ rest, cnfStructuredEncodedType.inputSize (f y) ≤ B := by
        intro y hy
        exact hBlock y (by simp [hy])
      have ih' := ih hrest
      have hAppend :
          cnfStructuredEncodedType.inputSize (f x ++ rest.flatMap f) =
            cnfStructuredEncodedType.inputSize (f x) +
              cnfStructuredEncodedType.inputSize (rest.flatMap f) := by
        simpa [cnfStructuredEncodedType] using
          list_inputSize_append clauseStructuredEncodedType (f x) (rest.flatMap f)
      change cnfStructuredEncodedType.inputSize (f x ++ rest.flatMap f) ≤
        (x :: rest).length * B
      calc
        cnfStructuredEncodedType.inputSize (f x ++ rest.flatMap f)
            = cnfStructuredEncodedType.inputSize (f x) +
                cnfStructuredEncodedType.inputSize (rest.flatMap f) := hAppend
        _ ≤ B + rest.length * B := Nat.add_le_add hx ih'
        _ = (x :: rest).length * B := by
          simp [Nat.succ_mul, Nat.add_comm]

theorem setCoveringAtMostSlotExecutable_inputSize_le
    {N : Nat} {ctx : SetCoveringChoicePairRowContext}
    (hCtx : setCoveringChoicePairRowContextEncodedType.inputSize ctx ≤ N) :
    cnfStructuredEncodedType.inputSize (setCoveringAtMostSlotExecutable ctx) ≤
      N * ((2 * N + 3) * (2 * (2 * N + 3) ^ 2 + 21)) := by
  have hCountN : ctx.2 ≤ N := by
    rcases ctx with ⟨slot, choiceCount⟩
    change choiceCount ≤ N
    simp [setCoveringChoicePairRowContextEncodedType, vertexPairEncodedType,
      EncodedType.inputSize_prod, EncodedType.inputSize_nat] at hCtx
    omega
  rw [setCoveringAtMostSlotExecutable_eq_flatMap]
  have hBlock :
      ∀ choice ∈ List.range ctx.2,
        cnfStructuredEncodedType.inputSize
            (setCoveringAtMostChoiceExecutable
              (setCoveringAtMostSlotChoiceContext ctx choice)) ≤
          (2 * N + 3) * (2 * (2 * N + 3) ^ 2 + 21) := by
    intro choice hChoiceMem
    have hChoiceLt : choice < ctx.2 := by
      simpa using List.mem_range.mp hChoiceMem
    have hChoice : EncodedType.nat.inputSize choice ≤ N := by
      simp [EncodedType.inputSize_nat]
      omega
    exact setCoveringAtMostSlotChoiceExecutable_inputSize_le hCtx hChoice
  have hSize :=
    cnfStructured_inputSize_flatMap_le
      (xs := List.range ctx.2)
      (f := fun choice =>
        setCoveringAtMostChoiceExecutable
          (setCoveringAtMostSlotChoiceContext ctx choice))
      hBlock
  have hLen : (List.range ctx.2).length ≤ N := by
    simpa using hCountN
  exact hSize.trans (Nat.mul_le_mul_right _ hLen)

end ExactCover
end Karp21
end ComplexityReduction
