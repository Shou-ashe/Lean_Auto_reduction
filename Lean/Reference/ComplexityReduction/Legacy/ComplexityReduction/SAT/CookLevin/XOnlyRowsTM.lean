/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.ContextCNFFoldTM
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyBlocksTM

/-!
Direct standard-TM witnesses for x-only Cook-Levin row aggregation.

The fixed-row witnesses in `XOnlyBlocksTM` hard-code the time coordinate.  This
file adds the variable-time versions needed to fold over the time range computed
from `x`.
-/

namespace ComplexityReduction
namespace SAT

def tmVerifierTimeCellEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.nat

/-! ### Variable-time atom constructors -/

theorem tmVerifierTableauVar_timeCell_tm_polytime
    (kind : TMVerifierTableauVarKind) (stack payload : Nat) :
    TMPolyTimeMap tmVerifierTimeCellEncodedType EncodedType.nat
      (fun p : Nat × Nat => tmVerifierTableauVar kind p.1 stack p.2 payload) := by
  let P := tmVerifierTimeCellEncodedType
  have hTime : TMPolyTimeMap P EncodedType.nat (fun p : Nat × Nat => p.1) := by
    simpa [P, tmVerifierTimeCellEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hCell : TMPolyTimeMap P EncodedType.nat (fun p : Nat × Nat => p.2) := by
    simpa [P, tmVerifierTimeCellEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hCellPayload :
      TMPolyTimeMap P EncodedType.nat (fun p : Nat × Nat => Nat.pair p.2 payload) := by
    have hComp := TMPolyTimeMap.comp (nat_pair_const_right_tm_polytime payload) hCell
    simpa [Function.comp, P] using hComp
  have hStackPayload :
      TMPolyTimeMap P EncodedType.nat
        (fun p : Nat × Nat => Nat.pair stack (Nat.pair p.2 payload)) := by
    have hComp := TMPolyTimeMap.comp (nat_pair_const_left_tm_polytime stack) hCellPayload
    simpa [Function.comp, P] using hComp
  have hTimePayloadInput :
      TMPolyTimeMap P (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × Nat => (p.1, Nat.pair stack (Nat.pair p.2 payload))) :=
    TMPolyTimeMap.prod_mk hTime hStackPayload
  have hTimePayload :
      TMPolyTimeMap P EncodedType.nat
        (fun p : Nat × Nat => Nat.pair p.1 (Nat.pair stack (Nat.pair p.2 payload))) := by
    have hComp := TMPolyTimeMap.comp natPair_tm_polytime hTimePayloadInput
    simpa [Function.comp, P] using hComp
  have hKind :
      TMPolyTimeMap P EncodedType.nat
        (fun p : Nat × Nat =>
          Nat.pair kind.tag (Nat.pair p.1 (Nat.pair stack (Nat.pair p.2 payload)))) := by
    have hComp := TMPolyTimeMap.comp (nat_pair_const_left_tm_polytime kind.tag) hTimePayload
    simpa [Function.comp, P] using hComp
  simpa [P, tmVerifierTimeCellEncodedType, tmVerifierTableauVar] using hKind

theorem tmVerifierTableauAtom_timeCell_tm_polytime
    (kind : TMVerifierTableauVarKind) (stack payload : Nat) :
    TMPolyTimeMap tmVerifierTimeCellEncodedType literalStructuredEncodedType
      (fun p : Nat × Nat => tmVerifierTableauAtom kind p.1 stack p.2 payload) := by
  have hVar := tmVerifierTableauVar_timeCell_tm_polytime kind stack payload
  have hComp := TMPolyTimeMap.comp literalPositiveTMBackedMap.tm_polytime hVar
  simpa [Function.comp, tmVerifierTableauAtom, Literal.positive] using hComp

theorem negTMVerifierTableauAtom_timeCell_tm_polytime
    (kind : TMVerifierTableauVarKind) (stack payload : Nat) :
    TMPolyTimeMap tmVerifierTimeCellEncodedType literalStructuredEncodedType
      (fun p : Nat × Nat => negTMVerifierTableauAtom kind p.1 stack p.2 payload) := by
  have hVar := tmVerifierTableauVar_timeCell_tm_polytime kind stack payload
  have hComp := TMPolyTimeMap.comp literalNegativeTMBackedMap.tm_polytime hVar
  simpa [Function.comp, negTMVerifierTableauAtom, Literal.negative] using hComp

theorem tmVerifierStackEmptyAtom_timeCell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap tmVerifierTimeCellEncodedType literalStructuredEncodedType
      (fun p : Nat × Nat => tmVerifierStackEmptyAtom V p.1 k p.2) := by
  simpa [tmVerifierStackEmptyAtom] using
    tmVerifierTableauAtom_timeCell_tm_polytime
      TMVerifierTableauVarKind.stackEmpty (tmVerifierStackCode V k) 0

theorem tmVerifierStackSymbolAtom_timeCell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (k : tmVerifierStackIndex V) (payload : Nat) :
    TMPolyTimeMap tmVerifierTimeCellEncodedType literalStructuredEncodedType
      (fun p : Nat × Nat => tmVerifierStackSymbolAtom V p.1 k p.2 payload) := by
  simpa [tmVerifierStackSymbolAtom] using
    tmVerifierTableauAtom_timeCell_tm_polytime
      TMVerifierTableauVarKind.stackSymbol (tmVerifierStackCode V k) payload

theorem negTMVerifierStackEmptyAtom_timeCell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap tmVerifierTimeCellEncodedType literalStructuredEncodedType
      (fun p : Nat × Nat => negTMVerifierStackEmptyAtom V p.1 k p.2) := by
  simpa [negTMVerifierStackEmptyAtom] using
    negTMVerifierTableauAtom_timeCell_tm_polytime
      TMVerifierTableauVarKind.stackEmpty (tmVerifierStackCode V k) 0

theorem tmVerifierStackReadChoice_atomAt_timeCell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (k : tmVerifierStackIndex V) (choice : TMVerifierStackReadChoice V k) :
    TMPolyTimeMap tmVerifierTimeCellEncodedType literalStructuredEncodedType
      (fun p : Nat × Nat =>
        TMVerifierStackReadChoice.atomAt (V := V) (k := k) p.1 p.2 choice) := by
  cases choice with
  | empty =>
      simpa [TMVerifierStackReadChoice.atomAt] using
        tmVerifierStackEmptyAtom_timeCell_tm_polytime V k
  | symbol payload symbol =>
      simpa [TMVerifierStackReadChoice.atomAt] using
        tmVerifierStackSymbolAtom_timeCell_tm_polytime V k payload

theorem tmVerifierStackReadChoice_negAtomAt_timeCell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (k : tmVerifierStackIndex V) (choice : TMVerifierStackReadChoice V k) :
    TMPolyTimeMap tmVerifierTimeCellEncodedType literalStructuredEncodedType
      (fun p : Nat × Nat =>
        Clause.negate (TMVerifierStackReadChoice.atomAt (V := V) (k := k) p.1 p.2 choice)) := by
  have hAtom := tmVerifierStackReadChoice_atomAt_timeCell_tm_polytime V k choice
  have hComp := TMPolyTimeMap.comp literalNegateTMBackedMap.tm_polytime hAtom
  simpa [Function.comp] using hComp

theorem tmVerifierStackReadChoiceLiteralsFor_timeCell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (k : tmVerifierStackIndex V) (choices : List (TMVerifierStackReadChoice V k)) :
    TMPolyTimeMap tmVerifierTimeCellEncodedType (EncodedType.list literalStructuredEncodedType)
      (fun p : Nat × Nat =>
        choices.map fun choice =>
          TMVerifierStackReadChoice.atomAt (V := V) (k := k) p.1 p.2 choice) := by
  induction choices with
  | nil =>
      exact TMPolyTimeMap.const tmVerifierTimeCellEncodedType
        (EncodedType.list literalStructuredEncodedType) []
  | cons choice choices ih =>
      have hHead := tmVerifierStackReadChoice_atomAt_timeCell_tm_polytime V k choice
      have hTail := ih
      have hConsInput :
          TMPolyTimeMap tmVerifierTimeCellEncodedType
            (EncodedType.prod literalStructuredEncodedType
              (EncodedType.list literalStructuredEncodedType))
            (fun p : Nat × Nat =>
              (TMVerifierStackReadChoice.atomAt (V := V) (k := k) p.1 p.2 choice,
                choices.map fun choice =>
                  TMVerifierStackReadChoice.atomAt (V := V) (k := k) p.1 p.2 choice)) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hCons := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons literalStructuredEncodedType)
        hConsInput
      simpa [Function.comp] using hCons

/-! ### Variable-time stack-cell CNF blocks -/

theorem tmVerifierStackReadChoiceAtMostOneWithCNF_timeCell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (k : tmVerifierStackIndex V)
    (head : TMVerifierStackReadChoice V k)
    (tail : List (TMVerifierStackReadChoice V k)) :
    TMPolyTimeMap tmVerifierTimeCellEncodedType cnfStructuredEncodedType
      (fun p : Nat × Nat =>
        CookLevin.atMostOneWithCNF
          (TMVerifierStackReadChoice.atomAt (V := V) (k := k) p.1 p.2 head)
          (tail.map fun choice =>
            TMVerifierStackReadChoice.atomAt (V := V) (k := k) p.1 p.2 choice)) := by
  induction tail with
  | nil =>
      exact TMPolyTimeMap.const tmVerifierTimeCellEncodedType cnfStructuredEncodedType []
  | cons choice tail ih =>
      have hHeadNeg := tmVerifierStackReadChoice_negAtomAt_timeCell_tm_polytime V k head
      have hChoiceNeg := tmVerifierStackReadChoice_negAtomAt_timeCell_tm_polytime V k choice
      have hPair :
          TMPolyTimeMap tmVerifierTimeCellEncodedType
            (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
            (fun p : Nat × Nat =>
              (Clause.negate
                  (TMVerifierStackReadChoice.atomAt (V := V) (k := k) p.1 p.2 head),
                Clause.negate
                  (TMVerifierStackReadChoice.atomAt (V := V) (k := k) p.1 p.2 choice))) :=
        TMPolyTimeMap.prod_mk hHeadNeg hChoiceNeg
      have hClause :
          TMPolyTimeMap tmVerifierTimeCellEncodedType clauseStructuredEncodedType
            (fun p : Nat × Nat =>
              [Clause.negate
                  (TMVerifierStackReadChoice.atomAt (V := V) (k := k) p.1 p.2 head),
                Clause.negate
                  (TMVerifierStackReadChoice.atomAt (V := V) (k := k) p.1 p.2 choice)]) := by
        have hComp := TMPolyTimeMap.comp literalPairClause_tm_polytime hPair
        simpa [Function.comp] using hComp
      have hTail := ih
      have hConsInput :
          TMPolyTimeMap tmVerifierTimeCellEncodedType
            (EncodedType.prod clauseStructuredEncodedType cnfStructuredEncodedType)
            (fun p : Nat × Nat =>
              ([Clause.negate
                  (TMVerifierStackReadChoice.atomAt (V := V) (k := k) p.1 p.2 head),
                Clause.negate
                  (TMVerifierStackReadChoice.atomAt (V := V) (k := k) p.1 p.2 choice)],
                CookLevin.atMostOneWithCNF
                  (TMVerifierStackReadChoice.atomAt (V := V) (k := k) p.1 p.2 head)
                  (tail.map fun choice =>
                    TMVerifierStackReadChoice.atomAt (V := V) (k := k) p.1 p.2 choice))) :=
        TMPolyTimeMap.prod_mk hClause hTail
      have hCons := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons clauseStructuredEncodedType)
        hConsInput
      simpa [Function.comp, CookLevin.atMostOneWithCNF, cnfStructuredEncodedType,
        clauseStructuredEncodedType] using hCons

theorem tmVerifierStackReadChoiceAtMostOneCNF_timeCell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (k : tmVerifierStackIndex V) (choices : List (TMVerifierStackReadChoice V k)) :
    TMPolyTimeMap tmVerifierTimeCellEncodedType cnfStructuredEncodedType
      (fun p : Nat × Nat =>
        CookLevin.atMostOneCNF
          (choices.map fun choice =>
            TMVerifierStackReadChoice.atomAt (V := V) (k := k) p.1 p.2 choice)) := by
  induction choices with
  | nil =>
      exact TMPolyTimeMap.const tmVerifierTimeCellEncodedType cnfStructuredEncodedType []
  | cons choice choices ih =>
      have hWith := tmVerifierStackReadChoiceAtMostOneWithCNF_timeCell_tm_polytime
        V k choice choices
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap tmVerifierTimeCellEncodedType
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun p : Nat × Nat =>
              (CookLevin.atMostOneWithCNF
                (TMVerifierStackReadChoice.atomAt (V := V) (k := k) p.1 p.2 choice)
                (choices.map fun choice =>
                  TMVerifierStackReadChoice.atomAt (V := V) (k := k) p.1 p.2 choice),
                CookLevin.atMostOneCNF
                  (choices.map fun choice =>
                    TMVerifierStackReadChoice.atomAt (V := V) (k := k) p.1 p.2 choice))) :=
        TMPolyTimeMap.prod_mk hWith hTail
      have hAppend := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
        hAppendInput
      simpa [Function.comp, CookLevin.atMostOneCNF, cnfStructuredEncodedType] using hAppend

theorem tmVerifierStackReadChoiceExactlyOneCNF_timeCell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (k : tmVerifierStackIndex V) (choices : List (TMVerifierStackReadChoice V k)) :
    TMPolyTimeMap tmVerifierTimeCellEncodedType cnfStructuredEncodedType
      (fun p : Nat × Nat =>
        CookLevin.exactlyOneCNF
          (choices.map fun choice =>
            TMVerifierStackReadChoice.atomAt (V := V) (k := k) p.1 p.2 choice)) := by
  have hAtoms := tmVerifierStackReadChoiceLiteralsFor_timeCell_tm_polytime V k choices
  have hAtLeast :
      TMPolyTimeMap tmVerifierTimeCellEncodedType cnfStructuredEncodedType
        (fun p : Nat × Nat =>
          CookLevin.atLeastOneCNF
            (choices.map fun choice =>
              TMVerifierStackReadChoice.atomAt (V := V) (k := k) p.1 p.2 choice)) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton clauseStructuredEncodedType)
      hAtoms
    simpa [Function.comp, CookLevin.atLeastOneCNF, cnfStructuredEncodedType,
      clauseStructuredEncodedType] using hComp
  have hAtMost := tmVerifierStackReadChoiceAtMostOneCNF_timeCell_tm_polytime V k choices
  have hAppendInput :
      TMPolyTimeMap tmVerifierTimeCellEncodedType
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun p : Nat × Nat =>
          (CookLevin.atLeastOneCNF
            (choices.map fun choice =>
              TMVerifierStackReadChoice.atomAt (V := V) (k := k) p.1 p.2 choice),
            CookLevin.atMostOneCNF
              (choices.map fun choice =>
                TMVerifierStackReadChoice.atomAt (V := V) (k := k) p.1 p.2 choice))) :=
    TMPolyTimeMap.prod_mk hAtLeast hAtMost
  have hAppend := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
    hAppendInput
  simpa [Function.comp, CookLevin.exactlyOneCNF, cnfStructuredEncodedType] using hAppend

theorem tmVerifierStackCellDomainCNFAt_timeCell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap tmVerifierTimeCellEncodedType cnfStructuredEncodedType
      (fun p : Nat × Nat => tmVerifierStackCellDomainCNFAt V p.1 k p.2) := by
  simpa [tmVerifierStackCellDomainCNFAt, tmVerifierStackReadChoiceDomainCNFAt,
    tmVerifierStackReadChoiceLiteralsAt] using
    tmVerifierStackReadChoiceExactlyOneCNF_timeCell_tm_polytime V k
      (tmVerifierStackReadChoices V k)

theorem tmVerifierStackEmptyTailClause_timeCell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap tmVerifierTimeCellEncodedType clauseStructuredEncodedType
      (fun p : Nat × Nat => tmVerifierStackEmptyTailClause V p.1 k p.2) := by
  let P := tmVerifierTimeCellEncodedType
  have hTime : TMPolyTimeMap P EncodedType.nat (fun p : Nat × Nat => p.1) := by
    simpa [P, tmVerifierTimeCellEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hCell : TMPolyTimeMap P EncodedType.nat (fun p : Nat × Nat => p.2) := by
    simpa [P, tmVerifierTimeCellEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hNeg := negTMVerifierStackEmptyAtom_timeCell_tm_polytime V k
  have hCellSucc :
      TMPolyTimeMap P EncodedType.nat (fun p : Nat × Nat => p.2 + 1) := by
    have hComp := TMPolyTimeMap.comp (nat_add_const_tm_polytime 1) hCell
    simpa [Function.comp, P] using hComp
  have hNextInput :
      TMPolyTimeMap P tmVerifierTimeCellEncodedType
        (fun p : Nat × Nat => (p.1, p.2 + 1)) :=
    TMPolyTimeMap.prod_mk hTime hCellSucc
  have hNext :
      TMPolyTimeMap P literalStructuredEncodedType
        (fun p : Nat × Nat => tmVerifierStackEmptyAtom V p.1 k (p.2 + 1)) := by
    have hComp := TMPolyTimeMap.comp (tmVerifierStackEmptyAtom_timeCell_tm_polytime V k)
      hNextInput
    simpa [Function.comp, P] using hComp
  have hPair :
      TMPolyTimeMap P
        (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
        (fun p : Nat × Nat =>
          (negTMVerifierStackEmptyAtom V p.1 k p.2,
            tmVerifierStackEmptyAtom V p.1 k (p.2 + 1))) :=
    TMPolyTimeMap.prod_mk hNeg hNext
  have hClause := TMPolyTimeMap.comp literalPairClause_tm_polytime hPair
  convert hClause using 1

/-! ### X-only row block witnesses with variable time -/

theorem tmVerifierXOnlyStackCellDomainsCNFAt_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        tmVerifierXOnlyStackCellDomainsCNFAt V p.1 p.2 k) := by
  let P := EncodedType.prod L.Instance EncodedType.nat
  have hX : TMPolyTimeMap P L.Instance (fun p : P.Carrier => p.1) := by
    simpa [P] using TMPolyTimeMap.fst L.Instance EncodedType.nat
  have hTime : TMPolyTimeMap P EncodedType.nat (fun p : P.Carrier => p.2) := by
    simpa [P] using TMPolyTimeMap.snd L.Instance EncodedType.nat
  have hCells :
      TMPolyTimeMap P (EncodedType.list EncodedType.nat)
        (fun p : P.Carrier => tmVerifierXOnlyCellRange V p.1) := by
    have hComp := TMPolyTimeMap.comp (tmVerifierXOnlyCellRange_tm_polytime V) hX
    simpa [Function.comp, P] using hComp
  have hInput :
      TMPolyTimeMap P (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
        (fun p : P.Carrier => (p.2, tmVerifierXOnlyCellRange V p.1)) :=
    TMPolyTimeMap.prod_mk hTime hCells
  have hFold := cnfContextFlatMap_tm_polytime
    (C := EncodedType.nat) (X := EncodedType.nat)
    (fun t cell => tmVerifierStackCellDomainCNFAt V t k cell)
    (tmVerifierStackCellDomainCNFAt_timeCell_tm_polytime V k)
  have hComp := TMPolyTimeMap.comp hFold hInput
  simpa [Function.comp, P, tmVerifierXOnlyStackCellDomainsCNFAt] using hComp

theorem tmVerifierXOnlyStackEmptyTailCNFAt_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        tmVerifierXOnlyStackEmptyTailCNFAt V p.1 p.2 k) := by
  let P := EncodedType.prod L.Instance EncodedType.nat
  have hX : TMPolyTimeMap P L.Instance (fun p : P.Carrier => p.1) := by
    simpa [P] using TMPolyTimeMap.fst L.Instance EncodedType.nat
  have hTime : TMPolyTimeMap P EncodedType.nat (fun p : P.Carrier => p.2) := by
    simpa [P] using TMPolyTimeMap.snd L.Instance EncodedType.nat
  have hCells :
      TMPolyTimeMap P (EncodedType.list EncodedType.nat)
        (fun p : P.Carrier => tmVerifierXOnlyCellSuccessorRange V p.1) := by
    have hComp := TMPolyTimeMap.comp (tmVerifierXOnlyCellSuccessorRange_tm_polytime V) hX
    simpa [Function.comp, P] using hComp
  have hInput :
      TMPolyTimeMap P (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
        (fun p : P.Carrier => (p.2, tmVerifierXOnlyCellSuccessorRange V p.1)) :=
    TMPolyTimeMap.prod_mk hTime hCells
  have hBlock :
      TMPolyTimeMap tmVerifierTimeCellEncodedType cnfStructuredEncodedType
        (fun p : Nat × Nat => [tmVerifierStackEmptyTailClause V p.1 k p.2]) := by
    have hClause := tmVerifierStackEmptyTailClause_timeCell_tm_polytime V k
    have hComp := TMPolyTimeMap.comp clauseSingletonTMBackedMap.tm_polytime hClause
    simpa [Function.comp] using hComp
  have hFold := cnfContextFlatMap_tm_polytime
    (C := EncodedType.nat) (X := EncodedType.nat)
    (fun t cell => [tmVerifierStackEmptyTailClause V t k cell]) hBlock
  have hComp := TMPolyTimeMap.comp hFold hInput
  convert hComp using 1
  funext p
  simp [Function.comp, tmVerifierXOnlyStackEmptyTailCNFAt, List.map_eq_flatMap]
  rfl

theorem tmVerifierXOnlyStackFinalEmptyCNFAt_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        tmVerifierXOnlyStackFinalEmptyCNFAt V p.1 p.2 k) := by
  let P := EncodedType.prod L.Instance EncodedType.nat
  have hX : TMPolyTimeMap P L.Instance (fun p : P.Carrier => p.1) := by
    simpa [P] using TMPolyTimeMap.fst L.Instance EncodedType.nat
  have hTime : TMPolyTimeMap P EncodedType.nat (fun p : P.Carrier => p.2) := by
    simpa [P] using TMPolyTimeMap.snd L.Instance EncodedType.nat
  have hBound :
      TMPolyTimeMap P EncodedType.nat (fun p : P.Carrier => tmVerifierXOnlyCellBound V p.1) := by
    have hComp := TMPolyTimeMap.comp (tmVerifierXOnlyCellBound_tm_polytime V) hX
    simpa [Function.comp, P] using hComp
  have hAtomInput :
      TMPolyTimeMap P tmVerifierTimeCellEncodedType
        (fun p : P.Carrier => (p.2, tmVerifierXOnlyCellBound V p.1)) :=
    TMPolyTimeMap.prod_mk hTime hBound
  have hAtom :
      TMPolyTimeMap P literalStructuredEncodedType
        (fun p : P.Carrier =>
          tmVerifierStackEmptyAtom V p.2 k (tmVerifierXOnlyCellBound V p.1)) := by
    have hComp := TMPolyTimeMap.comp (tmVerifierStackEmptyAtom_timeCell_tm_polytime V k)
      hAtomInput
    simpa [Function.comp, P] using hComp
  have hCNF := TMPolyTimeMap.comp tmVerifierUnitCNF_tm_polytime hAtom
  simpa [Function.comp, P, tmVerifierXOnlyStackFinalEmptyCNFAt, tmVerifierUnitCNF] using hCNF

theorem tmVerifierXOnlyStackWellFormedCNFAt_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        tmVerifierXOnlyStackWellFormedCNFAt V p.1 p.2 k) := by
  let P := EncodedType.prod L.Instance EncodedType.nat
  have hDomains := tmVerifierXOnlyStackCellDomainsCNFAt_pair_tm_polytime V k
  have hTail := tmVerifierXOnlyStackEmptyTailCNFAt_pair_tm_polytime V k
  have hFinal := tmVerifierXOnlyStackFinalEmptyCNFAt_pair_tm_polytime V k
  have hTailFinalInput :
      TMPolyTimeMap P
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun p : P.Carrier =>
          (tmVerifierXOnlyStackEmptyTailCNFAt V p.1 p.2 k,
            tmVerifierXOnlyStackFinalEmptyCNFAt V p.1 p.2 k)) :=
    TMPolyTimeMap.prod_mk hTail hFinal
  have hTailFinal :
      TMPolyTimeMap P cnfStructuredEncodedType
        (fun p : P.Carrier =>
          tmVerifierXOnlyStackEmptyTailCNFAt V p.1 p.2 k ++
            tmVerifierXOnlyStackFinalEmptyCNFAt V p.1 p.2 k) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
      hTailFinalInput
    simpa [Function.comp, cnfStructuredEncodedType, P] using hComp
  have hAllInput :
      TMPolyTimeMap P
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun p : P.Carrier =>
          (tmVerifierXOnlyStackCellDomainsCNFAt V p.1 p.2 k,
            tmVerifierXOnlyStackEmptyTailCNFAt V p.1 p.2 k ++
              tmVerifierXOnlyStackFinalEmptyCNFAt V p.1 p.2 k)) :=
    TMPolyTimeMap.prod_mk hDomains hTailFinal
  have hAll := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
    hAllInput
  simpa [Function.comp, tmVerifierXOnlyStackWellFormedCNFAt, cnfStructuredEncodedType, P]
    using hAll

theorem tmVerifierXOnlyStackWellFormedForList_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (ks : List (tmVerifierStackIndex V)) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        ks.flatMap fun k => tmVerifierXOnlyStackWellFormedCNFAt V p.1 p.2 k) := by
  induction ks with
  | nil =>
      exact TMPolyTimeMap.const (EncodedType.prod L.Instance EncodedType.nat)
        cnfStructuredEncodedType []
  | cons k ks ih =>
      have hHead := tmVerifierXOnlyStackWellFormedCNFAt_pair_tm_polytime V k
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat)
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun p : L.Instance.Carrier × Nat =>
              (tmVerifierXOnlyStackWellFormedCNFAt V p.1 p.2 k,
                ks.flatMap fun k => tmVerifierXOnlyStackWellFormedCNFAt V p.1 p.2 k)) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hAppend := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
        hAppendInput
      simpa [Function.comp, cnfStructuredEncodedType] using hAppend

theorem tmVerifierXOnlyAllStackWellFormedCNFAt_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat => tmVerifierXOnlyAllStackWellFormedCNFAt V p.1 p.2) := by
  simpa [tmVerifierXOnlyAllStackWellFormedCNFAt] using
    tmVerifierXOnlyStackWellFormedForList_pair_tm_polytime V (tmVerifierStackList V)

theorem tmVerifierXOnlyStackWellFormedRowsCNF_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier => tmVerifierXOnlyStackWellFormedRowsCNF V x) := by
  have hTimes := tmVerifierXOnlyTableauTimeRange_tm_polytime V
  have hInput :
      TMPolyTimeMap L.Instance (EncodedType.prod L.Instance (EncodedType.list EncodedType.nat))
        (fun x : L.Instance.Carrier => (x, tmVerifierXOnlyTableauTimeRange V x)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id L.Instance) hTimes
  have hFold := cnfContextFlatMap_tm_polytime
    (C := L.Instance) (X := EncodedType.nat)
    (fun x t => tmVerifierXOnlyAllStackWellFormedCNFAt V x t)
    (tmVerifierXOnlyAllStackWellFormedCNFAt_pair_tm_polytime V)
  have hComp := TMPolyTimeMap.comp hFold hInput
  simpa [Function.comp, tmVerifierXOnlyStackWellFormedRowsCNF] using hComp

end SAT
end ComplexityReduction
