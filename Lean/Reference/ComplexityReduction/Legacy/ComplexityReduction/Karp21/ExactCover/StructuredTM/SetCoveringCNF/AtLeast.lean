import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.SlotClauses

namespace ComplexityReduction
namespace Karp21
namespace ExactCover

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
Executable at-least-one slot-clause family for the compact
Set-Covering-to-CNF route.

The row runner in `SlotClauses` emits `(fixed, index)` pairs.  Passing
`(setCoveringChoiceCount I, I.k)` and swapping each pair gives the contexts
`(slot, setCoveringChoiceCount I)` needed by the per-slot clause writer.
-/

def setCoveringChoicePairSwap (p : Nat × Nat) : Nat × Nat :=
  (p.2, p.1)

def setCoveringSlotAtLeastContextInput
    (I : SetCoveringInput) : SetCoveringChoicePairRowContext :=
  (setCoveringChoiceCount I, I.k)

def setCoveringSlotAtLeastContextsExecutable
    (I : SetCoveringInput) : List SetCoveringChoicePairRowContext :=
  (setCoveringChoicePairRowExecutable (setCoveringSlotAtLeastContextInput I)).map
    setCoveringChoicePairSwap

def setCoveringSlotAtLeastClausesExecutable (I : SetCoveringInput) : SAT.CNF :=
  (setCoveringSlotAtLeastContextsExecutable I).map setCoveringSlotAtLeastClauseExecutable

theorem setCoveringChoicePairSwap_tm_polytime :
    TMPolyTimeMap
      vertexPairEncodedType
      vertexPairEncodedType
      setCoveringChoicePairSwap := by
  have hFst : TMPolyTimeMap vertexPairEncodedType EncodedType.nat
      (fun p : Nat × Nat => p.1) := by
    simpa [vertexPairEncodedType] using TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hSnd : TMPolyTimeMap vertexPairEncodedType EncodedType.nat
      (fun p : Nat × Nat => p.2) := by
    simpa [vertexPairEncodedType] using TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  simpa [setCoveringChoicePairSwap, vertexPairEncodedType] using TMPolyTimeMap.prod_mk hSnd hFst

theorem setCoveringSlotAtLeastContextInput_tm_polytime :
    TMPolyTimeMap
      setCoveringStructuredEncodedType
      setCoveringChoicePairRowContextEncodedType
      setCoveringSlotAtLeastContextInput := by
  let X := setCoveringStructuredEncodedType
  have hSourceTuple :
      TMPolyTimeMap X setCoveringTupleStructuredEncodedType
        HittingSet.setCoveringInputToTuple := by
    simpa [X] using HittingSet.setCoveringInputToTupleTMBackedMap.tm_polytime
  have hBudget :
      TMPolyTimeMap X EncodedType.nat
        (fun I : SetCoveringInput => I.k) := by
    have hSnd := TMPolyTimeMap.snd setSystemStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hSourceTuple
    simpa [Function.comp, HittingSet.setCoveringInputToTuple,
      setCoveringTupleStructuredEncodedType, X] using hComp
  have hChoiceCount := setCoveringChoiceCount_tm_polytime
  have hPair :
      TMPolyTimeMap X vertexPairEncodedType
        (fun I : SetCoveringInput => (setCoveringChoiceCount I, I.k)) := by
    simpa [vertexPairEncodedType] using TMPolyTimeMap.prod_mk hChoiceCount hBudget
  simpa [setCoveringSlotAtLeastContextInput, setCoveringChoicePairRowContextEncodedType,
    X] using hPair

theorem setCoveringSlotAtLeastContextsExecutable_eq
    (I : SetCoveringInput) :
    setCoveringSlotAtLeastContextsExecutable I =
      (List.range I.k).map fun slot => (slot, setCoveringChoiceCount I) := by
  rw [setCoveringSlotAtLeastContextsExecutable, setCoveringChoicePairRowExecutable_eq_map]
  rw [List.map_map]
  apply List.map_congr_left
  intro slot _hslot
  simp [setCoveringSlotAtLeastContextInput, setCoveringChoicePairOfRowContext,
    setCoveringChoicePairSwap]

theorem setCoveringSlotAtLeastClausesExecutable_eq
    (I : SetCoveringInput) :
    setCoveringSlotAtLeastClausesExecutable I =
      (List.range I.k).map (setCoveringSlotAtLeastClause I) := by
  rw [setCoveringSlotAtLeastClausesExecutable, setCoveringSlotAtLeastContextsExecutable_eq]
  rw [List.map_map]
  apply List.map_congr_left
  intro slot _hslot
  exact setCoveringSlotAtLeastClauseExecutable_eq I slot

theorem setCoveringSlotAtLeastContextsExecutable_tm_polytime :
    TMPolyTimeMap
      setCoveringStructuredEncodedType
      setCoveringChoicePairListEncodedType
      setCoveringSlotAtLeastContextsExecutable := by
  have hRows :=
    TMPolyTimeMap.comp setCoveringChoicePairRowExecutable_tm_polytime
      setCoveringSlotAtLeastContextInput_tm_polytime
  have hSwap := TMPolyTimeMap.list_map setCoveringChoicePairSwap_tm_polytime
  have hComp := TMPolyTimeMap.comp hSwap hRows
  simpa [Function.comp, setCoveringSlotAtLeastContextsExecutable,
    setCoveringChoicePairListEncodedType, vertexPairListEncodedType,
    setCoveringSlotAtLeastContextInput] using hComp

theorem setCoveringSlotAtLeastClausesExecutable_tm_polytime :
    TMPolyTimeMap
      setCoveringStructuredEncodedType
      cnfStructuredEncodedType
      setCoveringSlotAtLeastClausesExecutable := by
  have hContexts := setCoveringSlotAtLeastContextsExecutable_tm_polytime
  have hClauses := TMPolyTimeMap.list_map setCoveringSlotAtLeastClauseExecutable_tm_polytime
  have hComp := TMPolyTimeMap.comp hClauses hContexts
  simpa [Function.comp, setCoveringSlotAtLeastClausesExecutable,
    setCoveringChoicePairListEncodedType, vertexPairListEncodedType,
    setCoveringChoicePairRowContextEncodedType, cnfStructuredEncodedType] using hComp

end ExactCover
end Karp21
end ComplexityReduction
