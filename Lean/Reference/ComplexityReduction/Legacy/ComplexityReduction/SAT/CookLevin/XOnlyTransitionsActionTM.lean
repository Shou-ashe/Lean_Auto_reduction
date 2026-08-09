import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyTransitionsTM

/-!
Direct standard-TM witnesses for x-only transition action rows.

This file continues the generator-only development from `XOnlyTransitionsTM`,
keeping the lower-level literal/frame helpers separate from the larger
action/window aggregation witnesses.
-/

namespace ComplexityReduction
namespace SAT

theorem tmVerifierPushShiftCellCNF_actionCell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap
      (EncodedType.prod (tmVerifierXOnlyActionInputEncodedType L) EncodedType.nat)
      cnfStructuredEncodedType
      (fun q : TMVerifierXOnlyActionInput L × Nat =>
        tmVerifierPushShiftCellCNF V q.1.1.2.1 q.1.1.2.2 k q.2 q.1.2) := by
  let choices := tmVerifierStackReadChoices V k
  change TMPolyTimeMap
    (EncodedType.prod (tmVerifierXOnlyActionInputEncodedType L) EncodedType.nat)
    cnfStructuredEncodedType
    (fun q : TMVerifierXOnlyActionInput L × Nat =>
      choices.map fun choice =>
        tmVerifierPushShiftClause V q.1.1.2.1 q.1.1.2.2 k q.2 choice q.1.2)
  induction choices with
  | nil =>
      exact TMPolyTimeMap.const
        (EncodedType.prod (tmVerifierXOnlyActionInputEncodedType L) EncodedType.nat)
        cnfStructuredEncodedType []
  | cons choice choices ih =>
      have hHead := tmVerifierPushShiftClause_actionCell_tm_polytime V k choice
      have hTail := ih
      have hConsInput :
          TMPolyTimeMap
            (EncodedType.prod (tmVerifierXOnlyActionInputEncodedType L) EncodedType.nat)
            (EncodedType.prod clauseStructuredEncodedType cnfStructuredEncodedType)
            (fun q : TMVerifierXOnlyActionInput L × Nat =>
              (tmVerifierPushShiftClause V q.1.1.2.1 q.1.1.2.2 k q.2 choice q.1.2,
                choices.map fun choice =>
                  tmVerifierPushShiftClause V q.1.1.2.1 q.1.1.2.2 k q.2 choice
                    q.1.2)) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hCons := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_cons clauseStructuredEncodedType) hConsInput
      simpa [Function.comp, tmVerifierPushShiftCellCNF, cnfStructuredEncodedType]
        using hCons

theorem tmVerifierPopShiftCellCNF_actionCell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap
      (EncodedType.prod (tmVerifierXOnlyActionInputEncodedType L) EncodedType.nat)
      cnfStructuredEncodedType
      (fun q : TMVerifierXOnlyActionInput L × Nat =>
        tmVerifierPopShiftCellCNF V q.1.1.2.1 q.1.1.2.2 k q.2 q.1.2) := by
  let choices := tmVerifierStackReadChoices V k
  change TMPolyTimeMap
    (EncodedType.prod (tmVerifierXOnlyActionInputEncodedType L) EncodedType.nat)
    cnfStructuredEncodedType
    (fun q : TMVerifierXOnlyActionInput L × Nat =>
      choices.map fun choice =>
        tmVerifierPopShiftClause V q.1.1.2.1 q.1.1.2.2 k q.2 choice q.1.2)
  induction choices with
  | nil =>
      exact TMPolyTimeMap.const
        (EncodedType.prod (tmVerifierXOnlyActionInputEncodedType L) EncodedType.nat)
        cnfStructuredEncodedType []
  | cons choice choices ih =>
      have hHead := tmVerifierPopShiftClause_actionCell_tm_polytime V k choice
      have hTail := ih
      have hConsInput :
          TMPolyTimeMap
            (EncodedType.prod (tmVerifierXOnlyActionInputEncodedType L) EncodedType.nat)
            (EncodedType.prod clauseStructuredEncodedType cnfStructuredEncodedType)
            (fun q : TMVerifierXOnlyActionInput L × Nat =>
              (tmVerifierPopShiftClause V q.1.1.2.1 q.1.1.2.2 k q.2 choice q.1.2,
                choices.map fun choice =>
                  tmVerifierPopShiftClause V q.1.1.2.1 q.1.1.2.2 k q.2 choice
                    q.1.2)) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hCons := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_cons clauseStructuredEncodedType) hConsInput
      simpa [Function.comp, tmVerifierPopShiftCellCNF, cnfStructuredEncodedType]
        using hCons

theorem tmVerifierXOnlyFrameStacksForList_action_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (ks : List (tmVerifierStackIndex V)) :
    TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L) cnfStructuredEncodedType
      (fun q : TMVerifierXOnlyActionInput L =>
        ks.flatMap fun k =>
          tmVerifierXOnlyFrameStackCNFBetween V q.1.1 q.1.2.1 q.1.2.2 k q.2) := by
  induction ks with
  | nil =>
      exact TMPolyTimeMap.const (tmVerifierXOnlyActionInputEncodedType L)
        cnfStructuredEncodedType []
  | cons k ks ih =>
      have hHead := tmVerifierXOnlyFrameStackCNFBetween_action_tm_polytime V k
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L)
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun q : TMVerifierXOnlyActionInput L =>
              (tmVerifierXOnlyFrameStackCNFBetween V q.1.1 q.1.2.1 q.1.2.2 k q.2,
                ks.flatMap fun k =>
                  tmVerifierXOnlyFrameStackCNFBetween V q.1.1 q.1.2.1 q.1.2.2 k
                    q.2)) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hAppend := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
      simpa [Function.comp, cnfStructuredEncodedType] using hAppend

theorem tmVerifierXOnlyPushShiftCNF_action_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L) cnfStructuredEncodedType
      (fun q : TMVerifierXOnlyActionInput L =>
        (tmVerifierXOnlyCellRange V q.1.1).flatMap fun cell =>
          tmVerifierPushShiftCellCNF V q.1.2.1 q.1.2.2 k cell q.2) := by
  let P := tmVerifierXOnlyActionInputEncodedType L
  have hX := tmVerifierXOnlyActionInput_x_tm_polytime (L := L)
  have hCells :
      TMPolyTimeMap P (EncodedType.list EncodedType.nat)
        (fun q : P.Carrier => tmVerifierXOnlyCellRange V q.1.1) := by
    have hComp := TMPolyTimeMap.comp (tmVerifierXOnlyCellRange_tm_polytime V) hX
    simpa [Function.comp, P] using hComp
  have hInput :
      TMPolyTimeMap P (EncodedType.prod P (EncodedType.list EncodedType.nat))
        (fun q : P.Carrier => (q, tmVerifierXOnlyCellRange V q.1.1)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id P) hCells
  have hFold := cnfContextFlatMap_tm_polytime
    (C := P) (X := EncodedType.nat)
    (fun q cell => tmVerifierPushShiftCellCNF V q.1.2.1 q.1.2.2 k cell q.2)
    (tmVerifierPushShiftCellCNF_actionCell_tm_polytime V k)
  have hComp := TMPolyTimeMap.comp hFold hInput
  simpa [Function.comp, P] using hComp

theorem tmVerifierXOnlyPopShiftCNF_action_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L) cnfStructuredEncodedType
      (fun q : TMVerifierXOnlyActionInput L =>
        (tmVerifierXOnlyCellRange V q.1.1).flatMap fun cell =>
          tmVerifierPopShiftCellCNF V q.1.2.1 q.1.2.2 k cell q.2) := by
  let P := tmVerifierXOnlyActionInputEncodedType L
  have hX := tmVerifierXOnlyActionInput_x_tm_polytime (L := L)
  have hCells :
      TMPolyTimeMap P (EncodedType.list EncodedType.nat)
        (fun q : P.Carrier => tmVerifierXOnlyCellRange V q.1.1) := by
    have hComp := TMPolyTimeMap.comp (tmVerifierXOnlyCellRange_tm_polytime V) hX
    simpa [Function.comp, P] using hComp
  have hInput :
      TMPolyTimeMap P (EncodedType.prod P (EncodedType.list EncodedType.nat))
        (fun q : P.Carrier => (q, tmVerifierXOnlyCellRange V q.1.1)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id P) hCells
  have hFold := cnfContextFlatMap_tm_polytime
    (C := P) (X := EncodedType.nat)
    (fun q cell => tmVerifierPopShiftCellCNF V q.1.2.1 q.1.2.2 k cell q.2)
    (tmVerifierPopShiftCellCNF_actionCell_tm_polytime V k)
  have hComp := TMPolyTimeMap.comp hFold hInput
  simpa [Function.comp, P] using hComp

theorem tmVerifierXOnlyPushActionCNFBetween_action_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V) (raw : TMVerifierStackSymbol V) :
    TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L) cnfStructuredEncodedType
      (fun q : TMVerifierXOnlyActionInput L =>
        tmVerifierXOnlyPushActionCNFBetween V B q.1.1 q.1.2.1 q.1.2.2 raw q.2) := by
  let P := tmVerifierXOnlyActionInputEncodedType L
  have hTop := tmVerifierXOnlyPushTopCNF_action_tm_polytime V B raw
  have hShift := tmVerifierXOnlyPushShiftCNF_action_tm_polytime V raw.stack
  have hOther := tmVerifierXOnlyFrameStacksForList_action_tm_polytime V
    (tmVerifierOtherStacks V raw.stack)
  have hShiftOtherInput :
      TMPolyTimeMap P
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun q : P.Carrier =>
          ((tmVerifierXOnlyCellRange V q.1.1).flatMap fun cell =>
              tmVerifierPushShiftCellCNF V q.1.2.1 q.1.2.2 raw.stack cell q.2,
            (tmVerifierOtherStacks V raw.stack).flatMap fun k =>
              tmVerifierXOnlyFrameStackCNFBetween V q.1.1 q.1.2.1 q.1.2.2 k q.2)) :=
    TMPolyTimeMap.prod_mk hShift hOther
  have hShiftOther :
      TMPolyTimeMap P cnfStructuredEncodedType
        (fun q : P.Carrier =>
          ((tmVerifierXOnlyCellRange V q.1.1).flatMap fun cell =>
              tmVerifierPushShiftCellCNF V q.1.2.1 q.1.2.2 raw.stack cell q.2) ++
            ((tmVerifierOtherStacks V raw.stack).flatMap fun k =>
              tmVerifierXOnlyFrameStackCNFBetween V q.1.1 q.1.2.1 q.1.2.2 k q.2)) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
      hShiftOtherInput
    simpa [Function.comp, cnfStructuredEncodedType, P] using hComp
  have hAllInput :
      TMPolyTimeMap P
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun q : P.Carrier =>
          (tmVerifierPushTopCNF V B q.1.2.2 raw q.2,
            ((tmVerifierXOnlyCellRange V q.1.1).flatMap fun cell =>
                tmVerifierPushShiftCellCNF V q.1.2.1 q.1.2.2 raw.stack cell q.2) ++
              ((tmVerifierOtherStacks V raw.stack).flatMap fun k =>
                tmVerifierXOnlyFrameStackCNFBetween V q.1.1 q.1.2.1 q.1.2.2 k q.2))) :=
    TMPolyTimeMap.prod_mk hTop hShiftOther
  have hAll := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
    hAllInput
  simpa [Function.comp, tmVerifierXOnlyPushActionCNFBetween, cnfStructuredEncodedType, P]
    using hAll

theorem tmVerifierXOnlyPopActionCNFBetween_action_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L) cnfStructuredEncodedType
      (fun q : TMVerifierXOnlyActionInput L =>
        tmVerifierXOnlyPopActionCNFBetween V q.1.1 q.1.2.1 q.1.2.2 k q.2) := by
  let P := tmVerifierXOnlyActionInputEncodedType L
  have hShift := tmVerifierXOnlyPopShiftCNF_action_tm_polytime V k
  have hOther := tmVerifierXOnlyFrameStacksForList_action_tm_polytime V
    (tmVerifierOtherStacks V k)
  have hAppendInput :
      TMPolyTimeMap P
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun q : P.Carrier =>
          ((tmVerifierXOnlyCellRange V q.1.1).flatMap fun cell =>
              tmVerifierPopShiftCellCNF V q.1.2.1 q.1.2.2 k cell q.2,
            (tmVerifierOtherStacks V k).flatMap fun j =>
              tmVerifierXOnlyFrameStackCNFBetween V q.1.1 q.1.2.1 q.1.2.2 j q.2)) :=
    TMPolyTimeMap.prod_mk hShift hOther
  have hAppend := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
    hAppendInput
  simpa [Function.comp, tmVerifierXOnlyPopActionCNFBetween, cnfStructuredEncodedType, P]
    using hAppend

theorem tmVerifierXOnlyPreserveAllStacksActionCNFBetween_action_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L) cnfStructuredEncodedType
      (fun q : TMVerifierXOnlyActionInput L =>
        tmVerifierXOnlyPreserveAllStacksActionCNFBetween V q.1.1 q.1.2.1 q.1.2.2 q.2) := by
  simpa [tmVerifierXOnlyPreserveAllStacksActionCNFBetween] using
    tmVerifierXOnlyFrameAllStacksCNFBetween_action_tm_polytime V

theorem tmVerifierStackActionReadCNFAt_action_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (act : TMVerifierStackAction V) :
    TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L) cnfStructuredEncodedType
      (fun q : TMVerifierXOnlyActionInput L =>
        tmVerifierStackActionReadCNFAt q.1.2.1 q.2 act) := by
  cases act with
  | push raw =>
      exact TMPolyTimeMap.const (tmVerifierXOnlyActionInputEncodedType L)
        cnfStructuredEncodedType []
  | peek k choice =>
      have hAnt := tmVerifierXOnlyActionInput_antecedents_tm_polytime (L := L)
      have hTime := tmVerifierXOnlyActionInput_timeCell_tin_zero_tm_polytime (L := L)
      have hAtom :
          TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L)
            literalStructuredEncodedType
            (fun q : TMVerifierXOnlyActionInput L =>
              TMVerifierStackReadChoice.atomAt (V := V) (k := k) q.1.2.1 0 choice) := by
        have hComp := TMPolyTimeMap.comp
          (tmVerifierStackReadChoice_atomAt_timeCell_tm_polytime V k choice) hTime
        simpa [Function.comp] using hComp
      have hCNF := tmVerifierImplicationCNF_of_tm_polytime hAnt hAtom
      simpa [tmVerifierStackActionReadCNFAt] using hCNF
  | pop k choice =>
      have hAnt := tmVerifierXOnlyActionInput_antecedents_tm_polytime (L := L)
      have hTime := tmVerifierXOnlyActionInput_timeCell_tin_zero_tm_polytime (L := L)
      have hAtom :
          TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L)
            literalStructuredEncodedType
            (fun q : TMVerifierXOnlyActionInput L =>
              TMVerifierStackReadChoice.atomAt (V := V) (k := k) q.1.2.1 0 choice) := by
        have hComp := TMPolyTimeMap.comp
          (tmVerifierStackReadChoice_atomAt_timeCell_tm_polytime V k choice) hTime
        simpa [Function.comp] using hComp
      have hCNF := tmVerifierImplicationCNF_of_tm_polytime hAnt hAtom
      simpa [tmVerifierStackActionReadCNFAt] using hCNF
  | load =>
      exact TMPolyTimeMap.const (tmVerifierXOnlyActionInputEncodedType L)
        cnfStructuredEncodedType []
  | branch tag =>
      exact TMPolyTimeMap.const (tmVerifierXOnlyActionInputEncodedType L)
        cnfStructuredEncodedType []

theorem tmVerifierXOnlyStackActionEffectCNFBetween_action_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V) (act : TMVerifierStackAction V) :
    TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L) cnfStructuredEncodedType
      (fun q : TMVerifierXOnlyActionInput L =>
        tmVerifierXOnlyStackActionEffectCNFBetween V B q.1.1 q.1.2.1 q.1.2.2 q.2 act) := by
  cases act with
  | push raw =>
      simpa [tmVerifierXOnlyStackActionEffectCNFBetween] using
        tmVerifierXOnlyPushActionCNFBetween_action_tm_polytime V B raw
  | peek k choice =>
      simpa [tmVerifierXOnlyStackActionEffectCNFBetween] using
        tmVerifierXOnlyPreserveAllStacksActionCNFBetween_action_tm_polytime V
  | pop k choice =>
      simpa [tmVerifierXOnlyStackActionEffectCNFBetween] using
        tmVerifierXOnlyPopActionCNFBetween_action_tm_polytime V k
  | load =>
      simpa [tmVerifierXOnlyStackActionEffectCNFBetween] using
        tmVerifierXOnlyPreserveAllStacksActionCNFBetween_action_tm_polytime V
  | branch tag =>
      simpa [tmVerifierXOnlyStackActionEffectCNFBetween] using
        tmVerifierXOnlyPreserveAllStacksActionCNFBetween_action_tm_polytime V

theorem tmVerifierXOnlyStackActionCNFBetween_action_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V) (act : TMVerifierStackAction V) :
    TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L) cnfStructuredEncodedType
      (fun q : TMVerifierXOnlyActionInput L =>
        tmVerifierXOnlyStackActionCNFBetween V B q.1.1 q.1.2.1 q.1.2.2 q.2 act) := by
  let P := tmVerifierXOnlyActionInputEncodedType L
  have hEffect := tmVerifierXOnlyStackActionEffectCNFBetween_action_tm_polytime V B act
  have hRead := tmVerifierStackActionReadCNFAt_action_tm_polytime V act
  have hAppendInput :
      TMPolyTimeMap P
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun q : P.Carrier =>
          (tmVerifierXOnlyStackActionEffectCNFBetween V B q.1.1 q.1.2.1 q.1.2.2 q.2 act,
            tmVerifierStackActionReadCNFAt q.1.2.1 q.2 act)) :=
    TMPolyTimeMap.prod_mk hEffect hRead
  have hAppend := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
    hAppendInput
  simpa [Function.comp, tmVerifierXOnlyStackActionCNFBetween, cnfStructuredEncodedType, P]
    using hAppend

end SAT
end ComplexityReduction
