import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.SlotFor

namespace ComplexityReduction
namespace Karp21
namespace ExactCover

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
Executable all-slot CNF block for the Set-Covering-to-CNF route.

This module folds over the executable `(slot, choiceCount)` context list and
appends the complete per-slot block from `SlotFor`.
-/

def setCoveringSlotClausesFoldStep
    (p : cnfStructuredEncodedType.Carrier × SetCoveringChoicePairRowContext) :
    SAT.CNF :=
  (show SAT.CNF from p.1) ++ setCoveringSlotClausesForExecutable p.2

def setCoveringSlotClausesFromContexts
    (xs : List SetCoveringChoicePairRowContext) : SAT.CNF :=
  xs.foldl (fun out ctx => setCoveringSlotClausesFoldStep (out, ctx)) []

def setCoveringSlotClausesExecutable (I : SetCoveringInput) : SAT.CNF :=
  setCoveringSlotClausesFromContexts (setCoveringSlotAtLeastContextsExecutable I)

/-! ### Semantics -/

theorem setCoveringSlotClausesFold_eq_append_flatMap
    (xs : List SetCoveringChoicePairRowContext) (out : SAT.CNF) :
    xs.foldl (fun acc ctx => setCoveringSlotClausesFoldStep (acc, ctx)) out =
      out ++ xs.flatMap setCoveringSlotClausesForExecutable := by
  induction xs generalizing out with
  | nil =>
      simp
  | cons ctx rest ih =>
      rw [List.foldl_cons]
      simpa [setCoveringSlotClausesFoldStep, List.append_assoc] using
        ih (out ++ setCoveringSlotClausesForExecutable ctx)

theorem setCoveringSlotClausesFromContexts_eq_flatMap
    (xs : List SetCoveringChoicePairRowContext) :
    setCoveringSlotClausesFromContexts xs =
      xs.flatMap setCoveringSlotClausesForExecutable := by
  simpa [setCoveringSlotClausesFromContexts] using
    setCoveringSlotClausesFold_eq_append_flatMap xs ([] : SAT.CNF)

theorem setCoveringSlotClausesExecutable_eq
    (I : SetCoveringInput) :
    setCoveringSlotClausesExecutable I = setCoveringSlotClauses I := by
  rw [setCoveringSlotClausesExecutable, setCoveringSlotClausesFromContexts_eq_flatMap,
    setCoveringSlotAtLeastContextsExecutable_eq, setCoveringSlotClauses]
  simp only [List.flatMap_map]
  apply List.flatMap_congr
  intro slot _hslot
  exact setCoveringSlotClausesForExecutable_eq I slot

/-! ### TM witnesses -/

theorem setCoveringSlotClausesFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod cnfStructuredEncodedType setCoveringChoicePairRowContextEncodedType)
      cnfStructuredEncodedType
      setCoveringSlotClausesFoldStep := by
  let X := EncodedType.prod cnfStructuredEncodedType setCoveringChoicePairRowContextEncodedType
  have hOut : TMPolyTimeMap X cnfStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst cnfStructuredEncodedType
      setCoveringChoicePairRowContextEncodedType
  have hCtx :
      TMPolyTimeMap X setCoveringChoicePairRowContextEncodedType
        (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd cnfStructuredEncodedType
      setCoveringChoicePairRowContextEncodedType
  have hBlock :
      TMPolyTimeMap X cnfStructuredEncodedType
        (fun p : X.Carrier => setCoveringSlotClausesForExecutable p.2) := by
    have hComp := TMPolyTimeMap.comp setCoveringSlotClausesForExecutable_tm_polytime hCtx
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun p : X.Carrier =>
          ((show SAT.CNF from p.1), setCoveringSlotClausesForExecutable p.2)) :=
    TMPolyTimeMap.prod_mk hOut hBlock
  have hAppend :
      TMPolyTimeMap X cnfStructuredEncodedType
        (fun p : X.Carrier =>
          (show SAT.CNF from p.1) ++ setCoveringSlotClausesForExecutable p.2) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
      hAppendInput
    simpa [Function.comp, cnfStructuredEncodedType, X] using hComp
  simpa [setCoveringSlotClausesFoldStep, X] using hAppend

noncomputable def setCoveringSlotClausesFoldGrow : Polynomial Nat :=
  Polynomial.X * (Polynomial.X ^ 2 + Polynomial.C 4) + Polynomial.C 1 +
    Polynomial.X *
      ((Polynomial.C 2 * Polynomial.X + Polynomial.C 3) *
        (Polynomial.C 2 * (Polynomial.C 2 * Polynomial.X + Polynomial.C 3) ^ 2 +
          Polynomial.C 21))

@[simp] theorem setCoveringSlotClausesFoldGrow_eval (N : Nat) :
    setCoveringSlotClausesFoldGrow.eval N =
      N * (N ^ 2 + 4) + 1 +
        N * ((2 * N + 3) * (2 * (2 * N + 3) ^ 2 + 21)) := by
  simp [setCoveringSlotClausesFoldGrow, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X]

theorem setCoveringSlotClausesFoldStep_growth
    (source : List setCoveringChoicePairRowContextEncodedType.Carrier)
    (acc : cnfStructuredEncodedType.Carrier)
    (ctx : setCoveringChoicePairRowContextEncodedType.Carrier)
    (_hAcc : True)
    (hCtx :
      setCoveringChoicePairRowContextEncodedType.inputSize ctx ≤
        setCoveringChoicePairListEncodedType.inputSize source) :
    True ∧
      cnfStructuredEncodedType.inputSize (setCoveringSlotClausesFoldStep (acc, ctx)) ≤
        cnfStructuredEncodedType.inputSize acc +
          setCoveringSlotClausesFoldGrow.eval
            (setCoveringChoicePairListEncodedType.inputSize source) := by
  let N := setCoveringChoicePairListEncodedType.inputSize source
  have hBlock :
      cnfStructuredEncodedType.inputSize (setCoveringSlotClausesForExecutable ctx) ≤
        setCoveringSlotClausesFoldGrow.eval N := by
    have hRaw := setCoveringSlotClausesForExecutable_inputSize_le (N := N) (ctx := ctx) hCtx
    simpa [N, setCoveringSlotClausesFoldGrow_eval] using hRaw
  have hAppend :
      cnfStructuredEncodedType.inputSize
          ((show SAT.CNF from acc) ++ setCoveringSlotClausesForExecutable ctx) =
        cnfStructuredEncodedType.inputSize acc +
          cnfStructuredEncodedType.inputSize (setCoveringSlotClausesForExecutable ctx) := by
    simpa [cnfStructuredEncodedType] using
      list_inputSize_append clauseStructuredEncodedType acc
        (setCoveringSlotClausesForExecutable ctx)
  constructor
  · trivial
  · change
      cnfStructuredEncodedType.inputSize
          ((show SAT.CNF from acc) ++ setCoveringSlotClausesForExecutable ctx) ≤
        cnfStructuredEncodedType.inputSize acc +
          setCoveringSlotClausesFoldGrow.eval N
    rw [hAppend]
    nlinarith [hBlock]

theorem setCoveringSlotClausesFromContexts_tm_polytime :
    TMPolyTimeMap
      setCoveringChoicePairListEncodedType
      cnfStructuredEncodedType
      setCoveringSlotClausesFromContexts := by
  rcases setCoveringSlotClausesFoldStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      setCoveringChoicePairRowContextEncodedType cnfStructuredEncodedType
      setCoveringSlotClausesFoldStep ([] : SAT.CNF) hStep
      (Polynomial.C 0) setCoveringSlotClausesFoldGrow
      (fun _ _ => True) ?_ ?_
  · intro xs
    constructor
    · trivial
    · have hNil : cnfStructuredEncodedType.inputSize ([] : SAT.CNF) = 0 := by
        change (EncodedType.list clauseStructuredEncodedType).inputSize ([] : SAT.CNF) = 0
        exact EncodedType.inputSize_list_nil clauseStructuredEncodedType
      simp [hNil]
  · intro source acc ctx hAcc hCtx
    simpa [setCoveringChoicePairListEncodedType, vertexPairListEncodedType] using
      setCoveringSlotClausesFoldStep_growth source acc ctx hAcc hCtx

theorem setCoveringSlotClausesExecutable_tm_polytime :
    TMPolyTimeMap
      setCoveringStructuredEncodedType
      cnfStructuredEncodedType
      setCoveringSlotClausesExecutable := by
  have hComp :=
    TMPolyTimeMap.comp setCoveringSlotClausesFromContexts_tm_polytime
      setCoveringSlotAtLeastContextsExecutable_tm_polytime
  simpa [Function.comp, setCoveringSlotClausesExecutable] using hComp

end ExactCover
end Karp21
end ComplexityReduction
