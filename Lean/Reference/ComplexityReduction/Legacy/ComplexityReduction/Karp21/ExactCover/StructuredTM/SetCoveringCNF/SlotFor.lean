import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.AtLeast
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.AtMostSlot

namespace ComplexityReduction
namespace Karp21
namespace ExactCover

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
Executable CNF block for one set-covering slot.

The block is exactly the at-least-one slot clause followed by all at-most-one
clauses for the same slot.
-/

def setCoveringSlotClausesForExecutable
    (ctx : SetCoveringChoicePairRowContext) : SAT.CNF :=
  setCoveringSlotAtLeastClauseExecutable ctx ::
    setCoveringAtMostSlotExecutable ctx

theorem setCoveringSlotClausesForExecutable_eq
    (I : SetCoveringInput) (slot : Nat) :
    setCoveringSlotClausesForExecutable (slot, setCoveringChoiceCount I) =
      setCoveringSlotClausesFor I slot := by
  simp [setCoveringSlotClausesForExecutable, setCoveringSlotClausesFor,
    setCoveringSlotAtLeastClauseExecutable_eq I slot,
    setCoveringAtMostSlotExecutable_eq I slot]

theorem setCoveringSlotClausesForExecutable_tm_polytime :
    TMPolyTimeMap
      setCoveringChoicePairRowContextEncodedType
      cnfStructuredEncodedType
      setCoveringSlotClausesForExecutable := by
  have hAtLeast := setCoveringSlotAtLeastClauseExecutable_tm_polytime
  have hAtMost := setCoveringAtMostSlotExecutable_tm_polytime
  have hInput :
      TMPolyTimeMap
        setCoveringChoicePairRowContextEncodedType
        (EncodedType.prod clauseStructuredEncodedType cnfStructuredEncodedType)
        (fun ctx : SetCoveringChoicePairRowContext =>
          (setCoveringSlotAtLeastClauseExecutable ctx,
            setCoveringAtMostSlotExecutable ctx)) :=
    TMPolyTimeMap.prod_mk hAtLeast hAtMost
  have hCons :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons clauseStructuredEncodedType) hInput
  simpa [Function.comp, setCoveringSlotClausesForExecutable,
    cnfStructuredEncodedType] using hCons

/-! ### Output-size lemmas for the all-slots fold -/

theorem setCoveringSlotAtLeastClauseExecutable_inputSize_le
    {N : Nat} {ctx : SetCoveringChoicePairRowContext}
    (hCtx : setCoveringChoicePairRowContextEncodedType.inputSize ctx ≤ N) :
    clauseStructuredEncodedType.inputSize
        (setCoveringSlotAtLeastClauseExecutable ctx) ≤
      N * (N ^ 2 + 4) := by
  rcases ctx with ⟨slot, choiceCount⟩
  have hSlotN : slot + 1 ≤ N := by
    simp [setCoveringChoicePairRowContextEncodedType, vertexPairEncodedType,
      EncodedType.inputSize_prod, EncodedType.inputSize_nat] at hCtx
    omega
  have hCountN : choiceCount ≤ N := by
    simp [setCoveringChoicePairRowContextEncodedType, vertexPairEncodedType,
      EncodedType.inputSize_prod, EncodedType.inputSize_nat] at hCtx
    omega
  rw [setCoveringSlotAtLeastClauseExecutable, setCoveringChoicePairRowExecutable_eq_map]
  let clause :=
    (List.range choiceCount).map
      (fun choice => setCoveringChoiceLitFromPair (slot, choice))
  have hVar : ∀ l ∈ clause, l.var ≤ N ^ 2 := by
    intro l hl
    dsimp [clause] at hl
    rcases List.mem_map.mp hl with ⟨choice, hChoiceMem, rfl⟩
    have hChoiceLt : choice < choiceCount := by
      simpa using List.mem_range.mp hChoiceMem
    have hChoiceN : choice + 1 ≤ N := by omega
    have hMax : max slot choice + 1 ≤ N := by omega
    exact (Nat.le_of_lt (Nat.pair_lt_max_add_one_sq slot choice)).trans
      (Nat.pow_le_pow_left hMax 2)
  have hClause :=
    clauseStructured_inputSize_le_length_mul_of_lit_var_le
      (c := clause) (V := N ^ 2) hVar
  have hLen : clause.length ≤ N := by
    dsimp [clause]
    simpa using hCountN
  rw [List.map_map]
  change clauseStructuredEncodedType.inputSize clause ≤ N * (N ^ 2 + 4)
  calc
    clauseStructuredEncodedType.inputSize clause
        ≤ clause.length * (N ^ 2 + 4) := hClause
    _ ≤ N * (N ^ 2 + 4) := Nat.mul_le_mul_right _ hLen

theorem setCoveringSlotClausesForExecutable_inputSize_le
    {N : Nat} {ctx : SetCoveringChoicePairRowContext}
    (hCtx : setCoveringChoicePairRowContextEncodedType.inputSize ctx ≤ N) :
    cnfStructuredEncodedType.inputSize
        (setCoveringSlotClausesForExecutable ctx) ≤
      N * (N ^ 2 + 4) + 1 +
        N * ((2 * N + 3) * (2 * (2 * N + 3) ^ 2 + 21)) := by
  have hAtLeast :=
    setCoveringSlotAtLeastClauseExecutable_inputSize_le (N := N) (ctx := ctx) hCtx
  have hAtMost :=
    setCoveringAtMostSlotExecutable_inputSize_le (N := N) (ctx := ctx) hCtx
  have hAtMostList :
      (EncodedType.list clauseStructuredEncodedType).inputSize
          (setCoveringAtMostSlotExecutable ctx) ≤
        N * ((2 * N + 3) * (2 * (2 * N + 3) ^ 2 + 21)) := by
    simpa [cnfStructuredEncodedType] using hAtMost
  change (EncodedType.list clauseStructuredEncodedType).inputSize
      (setCoveringSlotAtLeastClauseExecutable ctx ::
        setCoveringAtMostSlotExecutable ctx) ≤
    N * (N ^ 2 + 4) + 1 +
      N * ((2 * N + 3) * (2 * (2 * N + 3) ^ 2 + 21))
  rw [EncodedType.inputSize_list_cons]
  nlinarith [hAtLeast, hAtMostList]

end ExactCover
end Karp21
end ComplexityReduction
