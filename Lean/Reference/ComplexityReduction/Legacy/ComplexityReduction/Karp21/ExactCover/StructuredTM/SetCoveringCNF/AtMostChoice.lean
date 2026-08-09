import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.SlotClauses
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.SplitWith.Core

namespace ComplexityReduction
namespace Karp21
namespace ExactCover

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
Executable at-most-one clauses for one fixed `(slot, choice)`.

For context `((slot, choiceCount), choice)`, the runner scans all
`other ∈ List.range choiceCount` and appends the binary negative clause exactly
when `choice < other`.  The branch is implemented with the checked unary
`natLtBool` predicate and a bounded fold.
-/

def setCoveringAtMostChoiceContextEncodedType : EncodedType :=
  EncodedType.prod vertexPairEncodedType EncodedType.nat

abbrev SetCoveringAtMostChoiceContext := (Nat × Nat) × Nat

def setCoveringAtMostChoiceInstructionEncodedType : EncodedType :=
  EncodedType.sum setCoveringAtMostChoiceContextEncodedType EncodedType.nat

def setCoveringAtMostChoiceInstructionListEncodedType : EncodedType :=
  EncodedType.list setCoveringAtMostChoiceInstructionEncodedType

def setCoveringAtMostChoiceAccEncodedType : EncodedType :=
  EncodedType.prod setCoveringAtMostChoiceContextEncodedType cnfStructuredEncodedType

def setCoveringAtMostChoiceZeroContext : SetCoveringAtMostChoiceContext :=
  ((0, 0), 0)

def setCoveringAtMostChoiceInitAcc :
    setCoveringAtMostChoiceAccEncodedType.Carrier :=
  (setCoveringAtMostChoiceZeroContext, [])

def setCoveringAtMostChoiceInitInstruction
    (ctx : SetCoveringAtMostChoiceContext) :
    setCoveringAtMostChoiceInstructionEncodedType.Carrier :=
  Sum.inl ctx

def setCoveringAtMostChoiceIndexInstruction
    (other : Nat) :
    setCoveringAtMostChoiceInstructionEncodedType.Carrier :=
  Sum.inr other

def setCoveringAtMostChoiceInstructions
    (ctx : SetCoveringAtMostChoiceContext) :
    List setCoveringAtMostChoiceInstructionEncodedType.Carrier :=
  setCoveringAtMostChoiceInitInstruction ctx ::
    (List.range ctx.1.2).map setCoveringAtMostChoiceIndexInstruction

def setCoveringAtMostClauseFromContextOther
    (ctx : SetCoveringAtMostChoiceContext) (other : Nat) : SAT.Clause :=
  [setCoveringChoiceNegLitFromPair (ctx.1.1, ctx.2),
    setCoveringChoiceNegLitFromPair (ctx.1.1, other)]

def setCoveringAtMostChoiceStep
    (p : setCoveringAtMostChoiceAccEncodedType.Carrier ×
      setCoveringAtMostChoiceInstructionEncodedType.Carrier) :
    setCoveringAtMostChoiceAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl ctx => (ctx, [])
  | Sum.inr other =>
      if natLtBool (p.1.1.2, other) then
        (p.1.1, (show SAT.CNF from p.1.2) ++
          [setCoveringAtMostClauseFromContextOther p.1.1 other])
      else
        (p.1.1, p.1.2)

def setCoveringAtMostChoiceFromInstructions
    (xs : List setCoveringAtMostChoiceInstructionEncodedType.Carrier) :
    SAT.CNF :=
  (xs.foldl (fun acc instr => setCoveringAtMostChoiceStep (acc, instr))
    setCoveringAtMostChoiceInitAcc).2

def setCoveringAtMostChoiceExecutable
    (ctx : SetCoveringAtMostChoiceContext) : SAT.CNF :=
  setCoveringAtMostChoiceFromInstructions
    (setCoveringAtMostChoiceInstructions ctx)

/-! ### Semantics -/

theorem setCoveringAtMostChoiceIndexFold_eq_append_filter_map
    (ctx : SetCoveringAtMostChoiceContext) (xs : List Nat)
    (out : SAT.CNF) :
    ((xs.map setCoveringAtMostChoiceIndexInstruction).foldl
        (fun acc instr => setCoveringAtMostChoiceStep (acc, instr)) (ctx, out)).2 =
      out ++ ((xs.filter fun other => decide (ctx.2 < other)).map
        (setCoveringAtMostClauseFromContextOther ctx)) := by
  induction xs generalizing out with
  | nil =>
      simp
  | cons other rest ih =>
      rw [List.map_cons, List.foldl_cons]
      by_cases hlt : ctx.2 < other
      · have hTail := ih (out ++ [setCoveringAtMostClauseFromContextOther ctx other])
        simp [setCoveringAtMostChoiceIndexInstruction, setCoveringAtMostChoiceStep,
          natLtBool, hlt, List.append_assoc] at hTail ⊢
        exact hTail
      · have hTail := ih out
        simp [setCoveringAtMostChoiceIndexInstruction, setCoveringAtMostChoiceStep,
          natLtBool, hlt] at hTail ⊢
        exact hTail

theorem setCoveringAtMostChoiceExecutable_eq_filter_map
    (ctx : SetCoveringAtMostChoiceContext) :
    setCoveringAtMostChoiceExecutable ctx =
      ((List.range ctx.1.2).filter fun other => decide (ctx.2 < other)).map
        (setCoveringAtMostClauseFromContextOther ctx) := by
  change
    (((List.range ctx.1.2).map setCoveringAtMostChoiceIndexInstruction).foldl
        (fun acc instr => setCoveringAtMostChoiceStep (acc, instr)) (ctx, [])).2 =
      ((List.range ctx.1.2).filter fun other => decide (ctx.2 < other)).map
        (setCoveringAtMostClauseFromContextOther ctx)
  simpa using
    setCoveringAtMostChoiceIndexFold_eq_append_filter_map ctx (List.range ctx.1.2) []

theorem setCoveringAtMostChoiceExecutable_eq
    (I : SetCoveringInput) (slot choice : Nat) :
    setCoveringAtMostChoiceExecutable ((slot, setCoveringChoiceCount I), choice) =
      setCoveringSlotAtMostClausesFor I slot choice := by
  rw [setCoveringAtMostChoiceExecutable_eq_filter_map, setCoveringSlotAtMostClausesFor]
  apply List.map_congr_left
  intro other _hother
  simp [setCoveringAtMostClauseFromContextOther, setCoveringChoiceNegLitFromPair,
    setCoveringChoiceNegLit, setCoveringChoiceVar]

/-! ### TM witnesses -/

theorem setCoveringAtMostChoiceInitInstruction_tm_polytime :
    TMPolyTimeMap
      setCoveringAtMostChoiceContextEncodedType
      setCoveringAtMostChoiceInstructionEncodedType
      setCoveringAtMostChoiceInitInstruction := by
  simpa [setCoveringAtMostChoiceInstructionEncodedType,
    setCoveringAtMostChoiceInitInstruction] using
    TMPolyTimeMap.inl setCoveringAtMostChoiceContextEncodedType EncodedType.nat

theorem setCoveringAtMostChoiceIndexInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      setCoveringAtMostChoiceInstructionEncodedType
      setCoveringAtMostChoiceIndexInstruction := by
  simpa [setCoveringAtMostChoiceInstructionEncodedType,
    setCoveringAtMostChoiceIndexInstruction] using
    TMPolyTimeMap.inr setCoveringAtMostChoiceContextEncodedType EncodedType.nat

theorem setCoveringAtMostChoiceInstructions_tm_polytime :
    TMPolyTimeMap
      setCoveringAtMostChoiceContextEncodedType
      setCoveringAtMostChoiceInstructionListEncodedType
      setCoveringAtMostChoiceInstructions := by
  let X := setCoveringAtMostChoiceContextEncodedType
  have hCtx : TMPolyTimeMap X X (fun ctx : X.Carrier => ctx) := TMPolyTimeMap.id X
  have hPayload : TMPolyTimeMap X vertexPairEncodedType (fun ctx : X.Carrier => ctx.1) := by
    simpa [X, setCoveringAtMostChoiceContextEncodedType] using
      TMPolyTimeMap.fst vertexPairEncodedType EncodedType.nat
  have hChoiceCount : TMPolyTimeMap X EncodedType.nat (fun ctx : X.Carrier => ctx.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, vertexPairEncodedType, X] using hComp
  have hInit :
      TMPolyTimeMap X setCoveringAtMostChoiceInstructionEncodedType
        (fun ctx : X.Carrier => setCoveringAtMostChoiceInitInstruction ctx) := by
    have hComp := TMPolyTimeMap.comp setCoveringAtMostChoiceInitInstruction_tm_polytime hCtx
    simpa [Function.comp, X] using hComp
  have hRange :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun ctx : X.Carrier => List.range ctx.1.2) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hChoiceCount
    simpa [Function.comp, X] using hComp
  have hIndexInstructions :
      TMPolyTimeMap X setCoveringAtMostChoiceInstructionListEncodedType
        (fun ctx : X.Carrier =>
          (List.range ctx.1.2).map setCoveringAtMostChoiceIndexInstruction) := by
    have hMap := TMPolyTimeMap.list_map setCoveringAtMostChoiceIndexInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, setCoveringAtMostChoiceInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod setCoveringAtMostChoiceInstructionEncodedType
          setCoveringAtMostChoiceInstructionListEncodedType)
        (fun ctx : X.Carrier =>
          (setCoveringAtMostChoiceInitInstruction ctx,
            (List.range ctx.1.2).map setCoveringAtMostChoiceIndexInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hIndexInstructions
  have hCons :=
    TMPolyTimeMap.comp
      (TMPolyTimeMap.list_cons setCoveringAtMostChoiceInstructionEncodedType)
      hConsInput
  simpa [Function.comp, setCoveringAtMostChoiceInstructions,
    setCoveringAtMostChoiceInstructionListEncodedType, X] using hCons

theorem setCoveringAtMostClauseFromContextOther_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setCoveringAtMostChoiceContextEncodedType EncodedType.nat)
      clauseStructuredEncodedType
      (fun p : setCoveringAtMostChoiceContextEncodedType.Carrier × Nat =>
        setCoveringAtMostClauseFromContextOther p.1 p.2) := by
  let X := EncodedType.prod setCoveringAtMostChoiceContextEncodedType EncodedType.nat
  have hCtx : TMPolyTimeMap X setCoveringAtMostChoiceContextEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst setCoveringAtMostChoiceContextEncodedType EncodedType.nat
  have hOther : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd setCoveringAtMostChoiceContextEncodedType EncodedType.nat
  have hSlot : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.1) := by
    have hPayload := TMPolyTimeMap.fst vertexPairEncodedType EncodedType.nat
    have hCompPayload := TMPolyTimeMap.comp hPayload hCtx
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hCompPayload
    simpa [Function.comp, setCoveringAtMostChoiceContextEncodedType,
      vertexPairEncodedType, X] using hComp
  have hChoice : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd vertexPairEncodedType EncodedType.nat) hCtx
    simpa [Function.comp, setCoveringAtMostChoiceContextEncodedType, X] using hComp
  have hChoicePair :
      TMPolyTimeMap X vertexPairEncodedType
        (fun p : X.Carrier => (p.1.1.1, p.1.2)) := by
    simpa [vertexPairEncodedType] using TMPolyTimeMap.prod_mk hSlot hChoice
  have hOtherPair :
      TMPolyTimeMap X vertexPairEncodedType
        (fun p : X.Carrier => (p.1.1.1, p.2)) := by
    simpa [vertexPairEncodedType] using TMPolyTimeMap.prod_mk hSlot hOther
  have hChoiceLit :
      TMPolyTimeMap X literalStructuredEncodedType
        (fun p : X.Carrier => setCoveringChoiceNegLitFromPair (p.1.1.1, p.1.2)) := by
    have hComp := TMPolyTimeMap.comp setCoveringChoiceNegLitFromPair_tm_polytime hChoicePair
    simpa [Function.comp] using hComp
  have hOtherLit :
      TMPolyTimeMap X literalStructuredEncodedType
        (fun p : X.Carrier => setCoveringChoiceNegLitFromPair (p.1.1.1, p.2)) := by
    have hComp := TMPolyTimeMap.comp setCoveringChoiceNegLitFromPair_tm_polytime hOtherPair
    simpa [Function.comp] using hComp
  have hTail :
      TMPolyTimeMap X clauseStructuredEncodedType
        (fun p : X.Carrier => [setCoveringChoiceNegLitFromPair (p.1.1.1, p.2)]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton literalStructuredEncodedType) hOtherLit
    simpa [Function.comp, clauseStructuredEncodedType] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod literalStructuredEncodedType clauseStructuredEncodedType)
        (fun p : X.Carrier =>
          (setCoveringChoiceNegLitFromPair (p.1.1.1, p.1.2),
            [setCoveringChoiceNegLitFromPair (p.1.1.1, p.2)])) :=
    TMPolyTimeMap.prod_mk hChoiceLit hTail
  have hCons := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons literalStructuredEncodedType)
    hConsInput
  simpa [Function.comp, setCoveringAtMostClauseFromContextOther,
    clauseStructuredEncodedType, X] using hCons

theorem setCoveringAtMostChoiceStepLeft_tm_polytime :
    TMPolyTimeMap
      setCoveringAtMostChoiceContextEncodedType
      setCoveringAtMostChoiceAccEncodedType
      (fun ctx : SetCoveringAtMostChoiceContext => (ctx, ([] : SAT.CNF))) := by
  have hCtx := TMPolyTimeMap.id setCoveringAtMostChoiceContextEncodedType
  have hEmpty :
      TMPolyTimeMap setCoveringAtMostChoiceContextEncodedType cnfStructuredEncodedType
        (fun _ : SetCoveringAtMostChoiceContext => ([] : SAT.CNF)) :=
    TMPolyTimeMap.const setCoveringAtMostChoiceContextEncodedType cnfStructuredEncodedType []
  simpa [setCoveringAtMostChoiceAccEncodedType] using TMPolyTimeMap.prod_mk hCtx hEmpty

theorem setCoveringAtMostChoiceStepRight_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setCoveringAtMostChoiceAccEncodedType EncodedType.nat)
      setCoveringAtMostChoiceAccEncodedType
      (fun p : setCoveringAtMostChoiceAccEncodedType.Carrier × Nat =>
        if natLtBool (p.1.1.2, p.2) then
          (p.1.1, (show SAT.CNF from p.1.2) ++
            [setCoveringAtMostClauseFromContextOther p.1.1 p.2])
        else
          (p.1.1, p.1.2)) := by
  let X := EncodedType.prod setCoveringAtMostChoiceAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X setCoveringAtMostChoiceAccEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst setCoveringAtMostChoiceAccEncodedType EncodedType.nat
  have hOther : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd setCoveringAtMostChoiceAccEncodedType EncodedType.nat
  have hCtx : TMPolyTimeMap X setCoveringAtMostChoiceContextEncodedType
      (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst setCoveringAtMostChoiceContextEncodedType cnfStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, setCoveringAtMostChoiceAccEncodedType, X] using hComp
  have hOut : TMPolyTimeMap X cnfStructuredEncodedType
      (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd setCoveringAtMostChoiceContextEncodedType cnfStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, setCoveringAtMostChoiceAccEncodedType, X] using hComp
  have hChoice : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.2) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd vertexPairEncodedType EncodedType.nat) hCtx
    simpa [Function.comp, setCoveringAtMostChoiceContextEncodedType, X] using hComp
  have hLtInput :
      TMPolyTimeMap X vertexPairEncodedType
        (fun p : X.Carrier => (p.1.1.2, p.2)) := by
    simpa [vertexPairEncodedType] using TMPolyTimeMap.prod_mk hChoice hOther
  have hLt : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => natLtBool (p.1.1.2, p.2)) := by
    have hComp := TMPolyTimeMap.comp natLtBool_tm_polytime hLtInput
    simpa [Function.comp, vertexPairEncodedType] using hComp
  have hClauseInput :
      TMPolyTimeMap X
        (EncodedType.prod setCoveringAtMostChoiceContextEncodedType EncodedType.nat)
        (fun p : X.Carrier => (p.1.1, p.2)) :=
    TMPolyTimeMap.prod_mk hCtx hOther
  have hClause :
      TMPolyTimeMap X clauseStructuredEncodedType
        (fun p : X.Carrier => setCoveringAtMostClauseFromContextOther p.1.1 p.2) := by
    have hComp := TMPolyTimeMap.comp setCoveringAtMostClauseFromContextOther_tm_polytime
      hClauseInput
    simpa [Function.comp] using hComp
  have hSingleton :
      TMPolyTimeMap X cnfStructuredEncodedType
        (fun p : X.Carrier => [setCoveringAtMostClauseFromContextOther p.1.1 p.2]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton clauseStructuredEncodedType) hClause
    simpa [Function.comp, cnfStructuredEncodedType] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun p : X.Carrier =>
          ((show SAT.CNF from p.1.2),
            [setCoveringAtMostClauseFromContextOther p.1.1 p.2])) :=
    TMPolyTimeMap.prod_mk hOut hSingleton
  have hAppend :
      TMPolyTimeMap X cnfStructuredEncodedType
        (fun p : X.Carrier =>
          (show SAT.CNF from p.1.2) ++
            [setCoveringAtMostClauseFromContextOther p.1.1 p.2]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
    simpa [Function.comp, cnfStructuredEncodedType, X] using hComp
  have hKeep :
      TMPolyTimeMap X setCoveringAtMostChoiceAccEncodedType
        (fun p : X.Carrier => (p.1.1, p.1.2)) :=
    TMPolyTimeMap.prod_mk hCtx hOut
  have hAppendOut :
      TMPolyTimeMap X setCoveringAtMostChoiceAccEncodedType
        (fun p : X.Carrier =>
          (p.1.1, (show SAT.CNF from p.1.2) ++
            [setCoveringAtMostClauseFromContextOther p.1.1 p.2])) :=
    TMPolyTimeMap.prod_mk hCtx hAppend
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (natLtBool (p.1.1.2, p.2), p)) :=
    TMPolyTimeMap.prod_mk hLt (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool X)
        setCoveringAtMostChoiceAccEncodedType
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true =>
              (p.2.1.1, (show SAT.CNF from p.2.1.2) ++
                [setCoveringAtMostClauseFromContextOther p.2.1.1 p.2.2])
          | false => (p.2.1.1, p.2.1.2)) :=
    Clique.boolProduct_dispatch_tm_polytime X setCoveringAtMostChoiceAccEncodedType
      (fFalse := fun p : X.Carrier => (p.1.1, p.1.2))
      (fTrue := fun p : X.Carrier =>
        (p.1.1, (show SAT.CNF from p.1.2) ++
          [setCoveringAtMostClauseFromContextOther p.1.1 p.2]))
      hKeep hAppendOut
  have hComp := TMPolyTimeMap.comp hBranch hBranchInput
  convert hComp using 1
  funext p
  cases h : natLtBool (p.1.1.2, p.2) <;> simp [Function.comp, h]

theorem setCoveringAtMostChoiceStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setCoveringAtMostChoiceAccEncodedType
        setCoveringAtMostChoiceInstructionEncodedType)
      setCoveringAtMostChoiceAccEncodedType
      setCoveringAtMostChoiceStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      setCoveringAtMostChoiceAccEncodedType
      setCoveringAtMostChoiceContextEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim setCoveringAtMostChoiceStepLeft_tm_polytime
      setCoveringAtMostChoiceStepRight_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

/-! ### Bounded fold certificate -/

def setCoveringAtMostChoiceFoldInv (N : Nat)
    (acc : setCoveringAtMostChoiceAccEncodedType.Carrier) : Prop :=
  acc = setCoveringAtMostChoiceInitAcc ∨
    acc.1 = setCoveringAtMostChoiceZeroContext ∨
    setCoveringAtMostChoiceContextEncodedType.inputSize acc.1 ≤ N

noncomputable def setCoveringAtMostChoiceFoldBase : Polynomial Nat :=
  Polynomial.C 30

noncomputable def setCoveringAtMostChoiceFoldGrow : Polynomial Nat :=
  Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C 30

@[simp] theorem setCoveringAtMostChoiceFoldGrow_eval (N : Nat) :
    setCoveringAtMostChoiceFoldGrow.eval N = 2 * N ^ 2 + 30 := by
  simp [setCoveringAtMostChoiceFoldGrow, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X]

theorem setCoveringAtMostChoiceInitAcc_bound
    (xs : List setCoveringAtMostChoiceInstructionEncodedType.Carrier) :
    setCoveringAtMostChoiceFoldInv
        (setCoveringAtMostChoiceInstructionListEncodedType.inputSize xs)
        setCoveringAtMostChoiceInitAcc ∧
      setCoveringAtMostChoiceAccEncodedType.inputSize setCoveringAtMostChoiceInitAcc ≤
        setCoveringAtMostChoiceFoldBase.eval
          (setCoveringAtMostChoiceInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · simp [setCoveringAtMostChoiceFoldBase]
    native_decide

theorem setCoveringAtMostClauseFromContextOther_inputSize_le
    {N : Nat} {ctx : SetCoveringAtMostChoiceContext} {other : Nat}
    (hCtx : setCoveringAtMostChoiceContextEncodedType.inputSize ctx ≤ N)
    (hOther : EncodedType.nat.inputSize other ≤ N) :
    clauseStructuredEncodedType.inputSize
        (setCoveringAtMostClauseFromContextOther ctx other) ≤
      2 * N ^ 2 + 20 := by
  rcases ctx with ⟨⟨slot, _choiceCount⟩, choice⟩
  have hSlotN : slot + 1 ≤ N := by
    simp [setCoveringAtMostChoiceContextEncodedType, vertexPairEncodedType,
      EncodedType.inputSize_prod, EncodedType.inputSize_nat] at hCtx
    omega
  have hChoiceN : choice + 1 ≤ N := by
    simp [setCoveringAtMostChoiceContextEncodedType, vertexPairEncodedType,
      EncodedType.inputSize_prod, EncodedType.inputSize_nat] at hCtx
    omega
  have hOtherN : other + 1 ≤ N := by
    simpa [EncodedType.inputSize_nat] using hOther
  have hMaxChoice : max slot choice + 1 ≤ N := by omega
  have hMaxOther : max slot other + 1 ≤ N := by omega
  have hVarChoice : Nat.pair slot choice ≤ N ^ 2 := by
    exact (Nat.le_of_lt (Nat.pair_lt_max_add_one_sq slot choice)).trans
      (Nat.pow_le_pow_left hMaxChoice 2)
  have hVarOther : Nat.pair slot other ≤ N ^ 2 := by
    exact (Nat.le_of_lt (Nat.pair_lt_max_add_one_sq slot other)).trans
      (Nat.pow_le_pow_left hMaxOther 2)
  change
    (EncodedType.list literalStructuredEncodedType).inputSize
        [setCoveringChoiceNegLitFromPair (slot, choice),
          setCoveringChoiceNegLitFromPair (slot, other)] ≤
      2 * N ^ 2 + 20
  rw [EncodedType.inputSize_list_cons, EncodedType.inputSize_list_cons,
    EncodedType.inputSize_list_nil]
  rw [literalStructured_inputSize_eq, literalStructured_inputSize_eq]
  simp [setCoveringChoiceNegLitFromPair, SAT.Literal.negative]
  nlinarith [hVarChoice, hVarOther, Nat.zero_le N]

theorem setCoveringAtMostClauseFromZeroContextOther_inputSize_le
    {N other : Nat} (hOther : EncodedType.nat.inputSize other ≤ N) :
    clauseStructuredEncodedType.inputSize
        (setCoveringAtMostClauseFromContextOther setCoveringAtMostChoiceZeroContext other) ≤
      2 * N ^ 2 + 20 := by
  have hZeroN : 0 + 1 ≤ N := by
    have hOtherN : other + 1 ≤ N := by simpa [EncodedType.inputSize_nat] using hOther
    omega
  have hOtherN : other + 1 ≤ N := by
    simpa [EncodedType.inputSize_nat] using hOther
  have hMaxChoice : max 0 0 + 1 ≤ N := by omega
  have hMaxOther : max 0 other + 1 ≤ N := by omega
  have hVarChoice : Nat.pair 0 0 ≤ N ^ 2 := by
    exact (Nat.le_of_lt (Nat.pair_lt_max_add_one_sq 0 0)).trans
      (Nat.pow_le_pow_left hMaxChoice 2)
  have hVarOther : Nat.pair 0 other ≤ N ^ 2 := by
    exact (Nat.le_of_lt (Nat.pair_lt_max_add_one_sq 0 other)).trans
      (Nat.pow_le_pow_left hMaxOther 2)
  change
    (EncodedType.list literalStructuredEncodedType).inputSize
        [setCoveringChoiceNegLitFromPair (0, 0),
          setCoveringChoiceNegLitFromPair (0, other)] ≤
      2 * N ^ 2 + 20
  rw [EncodedType.inputSize_list_cons, EncodedType.inputSize_list_cons,
    EncodedType.inputSize_list_nil]
  rw [literalStructured_inputSize_eq, literalStructured_inputSize_eq]
  simp [setCoveringChoiceNegLitFromPair, SAT.Literal.negative]
  nlinarith [hVarChoice, hVarOther, Nat.zero_le N]

theorem setCoveringAtMostChoiceStep_growth
    (source : List setCoveringAtMostChoiceInstructionEncodedType.Carrier)
    (acc : setCoveringAtMostChoiceAccEncodedType.Carrier)
    (instr : setCoveringAtMostChoiceInstructionEncodedType.Carrier)
    (hInv :
      setCoveringAtMostChoiceFoldInv
        (setCoveringAtMostChoiceInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      setCoveringAtMostChoiceInstructionEncodedType.inputSize instr ≤
        setCoveringAtMostChoiceInstructionListEncodedType.inputSize source) :
    setCoveringAtMostChoiceFoldInv
        (setCoveringAtMostChoiceInstructionListEncodedType.inputSize source)
        (setCoveringAtMostChoiceStep (acc, instr)) ∧
      setCoveringAtMostChoiceAccEncodedType.inputSize
          (setCoveringAtMostChoiceStep (acc, instr)) ≤
        setCoveringAtMostChoiceAccEncodedType.inputSize acc +
          setCoveringAtMostChoiceFoldGrow.eval
            (setCoveringAtMostChoiceInstructionListEncodedType.inputSize source) := by
  let N := setCoveringAtMostChoiceInstructionListEncodedType.inputSize source
  rcases acc with ⟨ctx, out⟩
  cases instr with
  | inl newCtx =>
      have hNewCtx : setCoveringAtMostChoiceContextEncodedType.inputSize newCtx ≤ N := by
        exact Nat.le_of_lt (by
          simpa [N, setCoveringAtMostChoiceInstructionEncodedType,
            EncodedType.inputSize, EncodedType.sum] using hInstr)
      constructor
      · exact Or.inr (Or.inr hNewCtx)
      · have hEmpty :
            cnfStructuredEncodedType.inputSize ([] : SAT.CNF) = 0 := by
          change (EncodedType.list clauseStructuredEncodedType).inputSize ([] : SAT.CNF) = 0
          exact EncodedType.inputSize_list_nil clauseStructuredEncodedType
        have hNewAcc :
            setCoveringAtMostChoiceAccEncodedType.inputSize (newCtx, ([] : SAT.CNF)) ≤
              N + 1 := by
          simp [setCoveringAtMostChoiceAccEncodedType, EncodedType.inputSize_prod, hEmpty]
          omega
        have hPoly :
            N + 1 ≤ setCoveringAtMostChoiceAccEncodedType.inputSize (ctx, out) +
              setCoveringAtMostChoiceFoldGrow.eval N := by
          simp
          nlinarith [Nat.zero_le N]
        simpa [setCoveringAtMostChoiceStep, N] using hNewAcc.trans hPoly
  | inr other =>
      have hOther : EncodedType.nat.inputSize other ≤ N := by
        exact Nat.le_of_lt (by
          simpa [N, setCoveringAtMostChoiceInstructionEncodedType,
            EncodedType.inputSize, EncodedType.sum] using hInstr)
      have hInvCtx :
          ctx = setCoveringAtMostChoiceZeroContext ∨
            setCoveringAtMostChoiceContextEncodedType.inputSize ctx ≤ N := by
        rcases hInv with hInit | hRest
        · injection hInit with hCtxEq _hOut
          exact Or.inl hCtxEq
        · exact hRest
      constructor
      ·
        cases hlt : natLtBool (ctx.2, other) <;>
          simp [setCoveringAtMostChoiceStep, hlt] <;>
          exact Or.inr hInvCtx
      · cases hlt : natLtBool (ctx.2, other)
        · change
            setCoveringAtMostChoiceAccEncodedType.inputSize
                (if natLtBool (ctx.2, other) then
                  (ctx, (show SAT.CNF from out) ++
                    [setCoveringAtMostClauseFromContextOther ctx other])
                else (ctx, out)) ≤
              setCoveringAtMostChoiceAccEncodedType.inputSize (ctx, out) +
                setCoveringAtMostChoiceFoldGrow.eval N
          simp [hlt]
        · have hClause :
              clauseStructuredEncodedType.inputSize
                  (setCoveringAtMostClauseFromContextOther ctx other) ≤
                2 * N ^ 2 + 20 :=
            by
              rcases hInvCtx with hZero | hCtxBound
              · rw [hZero]
                exact setCoveringAtMostClauseFromZeroContextOther_inputSize_le hOther
              · exact setCoveringAtMostClauseFromContextOther_inputSize_le hCtxBound hOther
          have hSingleton :
              cnfStructuredEncodedType.inputSize
                  [setCoveringAtMostClauseFromContextOther ctx other] ≤
                2 * N ^ 2 + 21 := by
            change (EncodedType.list clauseStructuredEncodedType).inputSize
                [setCoveringAtMostClauseFromContextOther ctx other] ≤
              2 * N ^ 2 + 21
            rw [EncodedType.inputSize_list_cons]
            rw [EncodedType.inputSize_list_nil]
            omega
          have hAppend :
              cnfStructuredEncodedType.inputSize
                  ((show SAT.CNF from out) ++
                    [setCoveringAtMostClauseFromContextOther ctx other]) =
                cnfStructuredEncodedType.inputSize out +
                  cnfStructuredEncodedType.inputSize
                    [setCoveringAtMostClauseFromContextOther ctx other] := by
            simpa [cnfStructuredEncodedType] using
              list_inputSize_append clauseStructuredEncodedType out
                [setCoveringAtMostClauseFromContextOther ctx other]
          change
            setCoveringAtMostChoiceAccEncodedType.inputSize
                (if natLtBool (ctx.2, other) then
                  (ctx, (show SAT.CNF from out) ++
                    [setCoveringAtMostClauseFromContextOther ctx other])
                else (ctx, out)) ≤
              setCoveringAtMostChoiceAccEncodedType.inputSize (ctx, out) +
                setCoveringAtMostChoiceFoldGrow.eval N
          simp [hlt, setCoveringAtMostChoiceAccEncodedType, EncodedType.inputSize_prod] at hAppend ⊢
          rw [hAppend]
          nlinarith [hSingleton, Nat.zero_le N]

theorem setCoveringAtMostChoiceFold_tm_polytime :
    TMPolyTimeMap
      setCoveringAtMostChoiceInstructionListEncodedType
      setCoveringAtMostChoiceAccEncodedType
      (fun xs : List setCoveringAtMostChoiceInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => setCoveringAtMostChoiceStep (acc, instr))
          setCoveringAtMostChoiceInitAcc) := by
  rcases setCoveringAtMostChoiceStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      setCoveringAtMostChoiceInstructionEncodedType setCoveringAtMostChoiceAccEncodedType
      setCoveringAtMostChoiceStep setCoveringAtMostChoiceInitAcc hStep
      setCoveringAtMostChoiceFoldBase setCoveringAtMostChoiceFoldGrow
      setCoveringAtMostChoiceFoldInv ?_ ?_
  · intro xs
    exact setCoveringAtMostChoiceInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact setCoveringAtMostChoiceStep_growth source acc instr hInv hInstr

theorem setCoveringAtMostChoiceFromInstructions_tm_polytime :
    TMPolyTimeMap
      setCoveringAtMostChoiceInstructionListEncodedType
      cnfStructuredEncodedType
      setCoveringAtMostChoiceFromInstructions := by
  have hFold := setCoveringAtMostChoiceFold_tm_polytime
  have hOut :=
    TMPolyTimeMap.snd setCoveringAtMostChoiceContextEncodedType cnfStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hOut hFold
  simpa [Function.comp, setCoveringAtMostChoiceFromInstructions,
    setCoveringAtMostChoiceAccEncodedType] using hComp

theorem setCoveringAtMostChoiceExecutable_tm_polytime :
    TMPolyTimeMap
      setCoveringAtMostChoiceContextEncodedType
      cnfStructuredEncodedType
      setCoveringAtMostChoiceExecutable := by
  have hComp :=
    TMPolyTimeMap.comp setCoveringAtMostChoiceFromInstructions_tm_polytime
      setCoveringAtMostChoiceInstructions_tm_polytime
  simpa [Function.comp, setCoveringAtMostChoiceExecutable] using hComp

/-! ### Output-size lemmas for outer folds -/

theorem cnfStructured_inputSize_le_length_mul_of_clause_inputSize_le
    {φ : SAT.CNF} {B : Nat}
    (hClause : ∀ c ∈ φ, clauseStructuredEncodedType.inputSize c ≤ B) :
    cnfStructuredEncodedType.inputSize φ ≤ φ.length * (B + 1) := by
  induction φ with
  | nil =>
      change (EncodedType.list clauseStructuredEncodedType).inputSize ([] : SAT.CNF) ≤
        ([] : SAT.CNF).length * (B + 1)
      have hNil : (EncodedType.list clauseStructuredEncodedType).inputSize ([] : SAT.CNF) = 0 := by
        exact EncodedType.inputSize_list_nil clauseStructuredEncodedType
      rw [hNil]
      simp
  | cons c cs ih =>
      have hc : clauseStructuredEncodedType.inputSize c ≤ B := hClause c (by simp)
      have hcs : ∀ d ∈ cs, clauseStructuredEncodedType.inputSize d ≤ B := by
        intro d hd
        exact hClause d (by simp [hd])
      have ih' := ih hcs
      have ihList :
          (EncodedType.list clauseStructuredEncodedType).inputSize cs ≤ cs.length * (B + 1) := by
        simpa [cnfStructuredEncodedType] using ih'
      change (EncodedType.list clauseStructuredEncodedType).inputSize (c :: cs) ≤
        (c :: cs).length * (B + 1)
      rw [EncodedType.inputSize_list_cons]
      change
        clauseStructuredEncodedType.inputSize c + 1 +
            (EncodedType.list clauseStructuredEncodedType).inputSize cs ≤
          (cs.length + 1) * (B + 1)
      nlinarith [hc, ihList, Nat.zero_le B, Nat.zero_le cs.length]

theorem setCoveringAtMostClauseFromContextOther_inputSize_le_of_mem_range
    {N : Nat} {ctx : SetCoveringAtMostChoiceContext} {other : Nat}
    (hCtx : setCoveringAtMostChoiceContextEncodedType.inputSize ctx ≤ N)
    (hOtherMem : other ∈ List.range ctx.1.2) :
    clauseStructuredEncodedType.inputSize
        (setCoveringAtMostClauseFromContextOther ctx other) ≤
      2 * N ^ 2 + 20 := by
  rcases ctx with ⟨⟨slot, choiceCount⟩, choice⟩
  have hCountN : choiceCount + 1 ≤ N := by
    simp [setCoveringAtMostChoiceContextEncodedType, vertexPairEncodedType,
      EncodedType.inputSize_prod, EncodedType.inputSize_nat] at hCtx
    omega
  have hOtherLt : other < choiceCount := by
    simpa using List.mem_range.mp hOtherMem
  have hOther : EncodedType.nat.inputSize other ≤ N := by
    simp [EncodedType.inputSize_nat]
    omega
  exact
    setCoveringAtMostClauseFromContextOther_inputSize_le
      (ctx := ((slot, choiceCount), choice)) hCtx hOther

theorem setCoveringAtMostChoiceExecutable_inputSize_le
    {N : Nat} {ctx : SetCoveringAtMostChoiceContext}
    (hCtx : setCoveringAtMostChoiceContextEncodedType.inputSize ctx ≤ N) :
    cnfStructuredEncodedType.inputSize (setCoveringAtMostChoiceExecutable ctx) ≤
      N * (2 * N ^ 2 + 21) := by
  have hCountN : ctx.1.2 ≤ N := by
    rcases ctx with ⟨⟨slot, choiceCount⟩, choice⟩
    change choiceCount ≤ N
    simp [setCoveringAtMostChoiceContextEncodedType, vertexPairEncodedType,
      EncodedType.inputSize_prod, EncodedType.inputSize_nat] at hCtx
    omega
  rw [setCoveringAtMostChoiceExecutable_eq_filter_map]
  have hClause :
      ∀ c ∈
          ((List.range ctx.1.2).filter fun other => decide (ctx.2 < other)).map
            (setCoveringAtMostClauseFromContextOther ctx),
        clauseStructuredEncodedType.inputSize c ≤ 2 * N ^ 2 + 20 := by
    intro c hc
    rcases List.mem_map.mp hc with ⟨other, hOtherFilter, rfl⟩
    have hOtherMem : other ∈ List.range ctx.1.2 := (List.mem_filter.mp hOtherFilter).1
    exact setCoveringAtMostClauseFromContextOther_inputSize_le_of_mem_range hCtx hOtherMem
  have hSize :=
    cnfStructured_inputSize_le_length_mul_of_clause_inputSize_le
      (φ := ((List.range ctx.1.2).filter fun other => decide (ctx.2 < other)).map
        (setCoveringAtMostClauseFromContextOther ctx))
      (B := 2 * N ^ 2 + 20) hClause
  have hLen :
      (((List.range ctx.1.2).filter fun other => decide (ctx.2 < other)).map
        (setCoveringAtMostClauseFromContextOther ctx)).length ≤ N := by
    calc
      (((List.range ctx.1.2).filter fun other => decide (ctx.2 < other)).map
          (setCoveringAtMostClauseFromContextOther ctx)).length
          = ((List.range ctx.1.2).filter fun other => decide (ctx.2 < other)).length := by
              simp
      _ ≤ (List.range ctx.1.2).length := List.length_filter_le _ _
      _ = ctx.1.2 := by simp
      _ ≤ N := hCountN
  nlinarith [hSize, hLen, Nat.zero_le N]

end ExactCover
end Karp21
end ComplexityReduction
