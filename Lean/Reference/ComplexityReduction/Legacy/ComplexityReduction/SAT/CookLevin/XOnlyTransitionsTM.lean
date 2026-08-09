import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.BoolDispatch
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyGlobalBaseTM
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyTransitions

/-!
Direct standard-TM witnesses for x-only transition/window rows.

This file is generator-only: it proves that the existing x-only transition CNF
surfaces are emitted by direct `TMPolyTimeMap`s, without changing the tableau
semantics in `XOnlyTransitions`.
-/

namespace ComplexityReduction
namespace SAT

def tmVerifierXOnlyActionInputEncodedType (L : EncodedDecisionProblem) : EncodedType :=
  EncodedType.prod
    (EncodedType.prod L.Instance
      (EncodedType.prod EncodedType.nat EncodedType.nat))
    (EncodedType.list literalStructuredEncodedType)

abbrev TMVerifierXOnlyActionInput (L : EncodedDecisionProblem) :=
  (L.Instance.Carrier × (Nat × Nat)) × List Literal

theorem tmVerifierImplicationClause_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod (EncodedType.list literalStructuredEncodedType)
        literalStructuredEncodedType)
      clauseStructuredEncodedType
      (fun p : List Literal × Literal => tmVerifierImplicationClause p.1 p.2) := by
  let P := EncodedType.prod (EncodedType.list literalStructuredEncodedType)
    literalStructuredEncodedType
  have hAnt :
      TMPolyTimeMap P (EncodedType.list literalStructuredEncodedType)
        (fun p : P.Carrier => p.1) := by
    simpa [P] using
      TMPolyTimeMap.fst (EncodedType.list literalStructuredEncodedType)
        literalStructuredEncodedType
  have hConcl : TMPolyTimeMap P literalStructuredEncodedType (fun p : P.Carrier => p.2) := by
    simpa [P] using
      TMPolyTimeMap.snd (EncodedType.list literalStructuredEncodedType)
        literalStructuredEncodedType
  have hNegs :
      TMPolyTimeMap P (EncodedType.list literalStructuredEncodedType)
        (fun p : P.Carrier => p.1.map Clause.negate) := by
    have hMap := TMPolyTimeMap.list_map literalNegateTMBackedMap.tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hAnt
    simpa [Function.comp, P] using hComp
  have hSingleton :
      TMPolyTimeMap P (EncodedType.list literalStructuredEncodedType)
        (fun p : P.Carrier => [p.2]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton literalStructuredEncodedType)
      hConcl
    simpa [Function.comp, P] using hComp
  have hAppendInput :
      TMPolyTimeMap P
        (EncodedType.prod (EncodedType.list literalStructuredEncodedType)
          (EncodedType.list literalStructuredEncodedType))
        (fun p : P.Carrier => (p.1.map Clause.negate, [p.2])) :=
    TMPolyTimeMap.prod_mk hNegs hSingleton
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append literalStructuredEncodedType) hAppendInput
  simpa [Function.comp, tmVerifierImplicationClause, clauseStructuredEncodedType, P]
    using hAppend

theorem clausePairCNF_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod clauseStructuredEncodedType clauseStructuredEncodedType)
      cnfStructuredEncodedType
      (fun p : Clause × Clause => [p.1, p.2]) := by
  let P := EncodedType.prod clauseStructuredEncodedType clauseStructuredEncodedType
  have hFirst : TMPolyTimeMap P clauseStructuredEncodedType (fun p : P.Carrier => p.1) := by
    simpa [P] using TMPolyTimeMap.fst clauseStructuredEncodedType clauseStructuredEncodedType
  have hSecond : TMPolyTimeMap P clauseStructuredEncodedType (fun p : P.Carrier => p.2) := by
    simpa [P] using TMPolyTimeMap.snd clauseStructuredEncodedType clauseStructuredEncodedType
  have hTail : TMPolyTimeMap P cnfStructuredEncodedType (fun p : P.Carrier => [p.2]) := by
    have hComp := TMPolyTimeMap.comp clauseSingletonTMBackedMap.tm_polytime hSecond
    simpa [Function.comp, cnfStructuredEncodedType, P] using hComp
  have hConsInput :
      TMPolyTimeMap P (EncodedType.prod clauseStructuredEncodedType cnfStructuredEncodedType)
        (fun p : P.Carrier => (p.1, [p.2])) :=
    TMPolyTimeMap.prod_mk hFirst hTail
  have hCons := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons clauseStructuredEncodedType)
    hConsInput
  simpa [Function.comp, cnfStructuredEncodedType, P] using hCons

theorem literal_append_singleton_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod (EncodedType.list literalStructuredEncodedType)
        literalStructuredEncodedType)
      (EncodedType.list literalStructuredEncodedType)
      (fun p : List Literal × Literal => p.1 ++ [p.2]) := by
  let P := EncodedType.prod (EncodedType.list literalStructuredEncodedType)
    literalStructuredEncodedType
  have hAnt :
      TMPolyTimeMap P (EncodedType.list literalStructuredEncodedType)
        (fun p : P.Carrier => p.1) := by
    simpa [P] using
      TMPolyTimeMap.fst (EncodedType.list literalStructuredEncodedType)
        literalStructuredEncodedType
  have hLit : TMPolyTimeMap P literalStructuredEncodedType (fun p : P.Carrier => p.2) := by
    simpa [P] using
      TMPolyTimeMap.snd (EncodedType.list literalStructuredEncodedType)
        literalStructuredEncodedType
  have hSingleton :
      TMPolyTimeMap P (EncodedType.list literalStructuredEncodedType)
        (fun p : P.Carrier => [p.2]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton literalStructuredEncodedType)
      hLit
    simpa [Function.comp, P] using hComp
  have hAppendInput :
      TMPolyTimeMap P
        (EncodedType.prod (EncodedType.list literalStructuredEncodedType)
          (EncodedType.list literalStructuredEncodedType))
        (fun p : P.Carrier => (p.1, [p.2])) :=
    TMPolyTimeMap.prod_mk hAnt hSingleton
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append literalStructuredEncodedType) hAppendInput
  simpa [Function.comp, P] using hAppend

theorem literal_append_singleton_of_tm_polytime
    {X : EncodedType} {ants : X.Carrier → List Literal} {lit : X.Carrier → Literal}
    (hAnts :
      TMPolyTimeMap X (EncodedType.list literalStructuredEncodedType) ants)
    (hLit : TMPolyTimeMap X literalStructuredEncodedType lit) :
    TMPolyTimeMap X (EncodedType.list literalStructuredEncodedType)
      (fun x : X.Carrier => ants x ++ [lit x]) := by
  have hInput :
      TMPolyTimeMap X
        (EncodedType.prod (EncodedType.list literalStructuredEncodedType)
          literalStructuredEncodedType)
        (fun x : X.Carrier => (ants x, lit x)) :=
    TMPolyTimeMap.prod_mk hAnts hLit
  have hComp := TMPolyTimeMap.comp literal_append_singleton_tm_polytime hInput
  simpa [Function.comp] using hComp

theorem tmVerifierImplicationClause_of_tm_polytime
    {X : EncodedType} {ants : X.Carrier → List Literal} {concl : X.Carrier → Literal}
    (hAnts :
      TMPolyTimeMap X (EncodedType.list literalStructuredEncodedType) ants)
    (hConcl : TMPolyTimeMap X literalStructuredEncodedType concl) :
    TMPolyTimeMap X clauseStructuredEncodedType
      (fun x : X.Carrier => tmVerifierImplicationClause (ants x) (concl x)) := by
  have hInput :
      TMPolyTimeMap X
        (EncodedType.prod (EncodedType.list literalStructuredEncodedType)
          literalStructuredEncodedType)
        (fun x : X.Carrier => (ants x, concl x)) :=
    TMPolyTimeMap.prod_mk hAnts hConcl
  have hComp := TMPolyTimeMap.comp tmVerifierImplicationClause_tm_polytime hInput
  simpa [Function.comp] using hComp

theorem tmVerifierImplicationCNF_of_tm_polytime
    {X : EncodedType} {ants : X.Carrier → List Literal} {concl : X.Carrier → Literal}
    (hAnts :
      TMPolyTimeMap X (EncodedType.list literalStructuredEncodedType) ants)
    (hConcl : TMPolyTimeMap X literalStructuredEncodedType concl) :
    TMPolyTimeMap X cnfStructuredEncodedType
      (fun x : X.Carrier => [tmVerifierImplicationClause (ants x) (concl x)]) := by
  have hClause := tmVerifierImplicationClause_of_tm_polytime hAnts hConcl
  have hComp := TMPolyTimeMap.comp clauseSingletonTMBackedMap.tm_polytime hClause
  simpa [Function.comp] using hComp

theorem tmVerifierXOnlyActionInput_x_tm_polytime
    {L : EncodedDecisionProblem} :
    TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L) L.Instance
      (fun q : TMVerifierXOnlyActionInput L => q.1.1) := by
  let P := tmVerifierXOnlyActionInputEncodedType L
  have hLeft :
      TMPolyTimeMap P
        (EncodedType.prod L.Instance
          (EncodedType.prod EncodedType.nat EncodedType.nat))
        (fun q : P.Carrier => q.1) := by
    simpa [P, tmVerifierXOnlyActionInputEncodedType] using
      TMPolyTimeMap.fst
        (EncodedType.prod L.Instance
          (EncodedType.prod EncodedType.nat EncodedType.nat))
        (EncodedType.list literalStructuredEncodedType)
  have hX := TMPolyTimeMap.fst L.Instance
    (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hComp := TMPolyTimeMap.comp hX hLeft
  simpa [Function.comp, P] using hComp

theorem tmVerifierXOnlyActionInput_times_tm_polytime
    {L : EncodedDecisionProblem} :
    TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L)
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun q : TMVerifierXOnlyActionInput L => q.1.2) := by
  let P := tmVerifierXOnlyActionInputEncodedType L
  have hLeft :
      TMPolyTimeMap P
        (EncodedType.prod L.Instance
          (EncodedType.prod EncodedType.nat EncodedType.nat))
        (fun q : P.Carrier => q.1) := by
    simpa [P, tmVerifierXOnlyActionInputEncodedType] using
      TMPolyTimeMap.fst
        (EncodedType.prod L.Instance
          (EncodedType.prod EncodedType.nat EncodedType.nat))
        (EncodedType.list literalStructuredEncodedType)
  have hTimes := TMPolyTimeMap.snd L.Instance
    (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hComp := TMPolyTimeMap.comp hTimes hLeft
  simpa [Function.comp, P] using hComp

theorem tmVerifierXOnlyActionInput_tin_tm_polytime
    {L : EncodedDecisionProblem} :
    TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L) EncodedType.nat
      (fun q : TMVerifierXOnlyActionInput L => q.1.2.1) := by
  have hTimes := tmVerifierXOnlyActionInput_times_tm_polytime (L := L)
  have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hComp := TMPolyTimeMap.comp hFst hTimes
  simpa [Function.comp] using hComp

theorem tmVerifierXOnlyActionInput_tout_tm_polytime
    {L : EncodedDecisionProblem} :
    TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L) EncodedType.nat
      (fun q : TMVerifierXOnlyActionInput L => q.1.2.2) := by
  have hTimes := tmVerifierXOnlyActionInput_times_tm_polytime (L := L)
  have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hComp := TMPolyTimeMap.comp hSnd hTimes
  simpa [Function.comp] using hComp

theorem tmVerifierXOnlyActionInput_antecedents_tm_polytime
    {L : EncodedDecisionProblem} :
    TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L)
      (EncodedType.list literalStructuredEncodedType)
      (fun q : TMVerifierXOnlyActionInput L => q.2) := by
  simpa [tmVerifierXOnlyActionInputEncodedType] using
    TMPolyTimeMap.snd
      (EncodedType.prod L.Instance
        (EncodedType.prod EncodedType.nat EncodedType.nat))
      (EncodedType.list literalStructuredEncodedType)

theorem tmVerifierXOnlyActionInput_timeCell_tin_zero_tm_polytime
    {L : EncodedDecisionProblem} :
    TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L)
      tmVerifierTimeCellEncodedType
      (fun q : TMVerifierXOnlyActionInput L => (q.1.2.1, (0 : Nat))) := by
  have hTin := tmVerifierXOnlyActionInput_tin_tm_polytime (L := L)
  have hZero :
      TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L) EncodedType.nat
        (fun _ : TMVerifierXOnlyActionInput L => (0 : Nat)) :=
    TMPolyTimeMap.const (tmVerifierXOnlyActionInputEncodedType L) EncodedType.nat
      (show Nat from 0)
  simpa [tmVerifierTimeCellEncodedType] using TMPolyTimeMap.prod_mk hTin hZero

theorem tmVerifierXOnlyActionInput_timeCell_tout_zero_tm_polytime
    {L : EncodedDecisionProblem} :
    TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L)
      tmVerifierTimeCellEncodedType
      (fun q : TMVerifierXOnlyActionInput L => (q.1.2.2, (0 : Nat))) := by
  have hTout := tmVerifierXOnlyActionInput_tout_tm_polytime (L := L)
  have hZero :
      TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L) EncodedType.nat
        (fun _ : TMVerifierXOnlyActionInput L => (0 : Nat)) :=
    TMPolyTimeMap.const (tmVerifierXOnlyActionInputEncodedType L) EncodedType.nat
      (show Nat from 0)
  simpa [tmVerifierTimeCellEncodedType] using TMPolyTimeMap.prod_mk hTout hZero

theorem tmVerifierXOnlyPushTopCNF_action_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V) (raw : TMVerifierStackSymbol V) :
    TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L) cnfStructuredEncodedType
      (fun q : TMVerifierXOnlyActionInput L =>
        tmVerifierPushTopCNF V B q.1.2.2 raw q.2) := by
  have hAnt := tmVerifierXOnlyActionInput_antecedents_tm_polytime (L := L)
  have hTime := tmVerifierXOnlyActionInput_timeCell_tout_zero_tm_polytime (L := L)
  have hAtomBase :=
    tmVerifierStackSymbolAtom_timeCell_tm_polytime V raw.stack (B.payload raw)
  have hAtom :
      TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L) literalStructuredEncodedType
        (fun q : TMVerifierXOnlyActionInput L =>
          tmVerifierStackSymbolAtom V q.1.2.2 raw.stack 0 (B.payload raw)) := by
    have hComp := TMPolyTimeMap.comp hAtomBase hTime
    simpa [Function.comp] using hComp
  have hCNF := tmVerifierImplicationCNF_of_tm_polytime hAnt hAtom
  simpa [tmVerifierPushTopCNF] using hCNF

theorem tmVerifierPushShiftClause_actionCell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (k : tmVerifierStackIndex V) (choice : TMVerifierStackReadChoice V k) :
    TMPolyTimeMap
      (EncodedType.prod (tmVerifierXOnlyActionInputEncodedType L) EncodedType.nat)
      clauseStructuredEncodedType
      (fun q : TMVerifierXOnlyActionInput L × Nat =>
        tmVerifierPushShiftClause V q.1.1.2.1 q.1.1.2.2 k q.2 choice q.1.2) := by
  let P := EncodedType.prod (tmVerifierXOnlyActionInputEncodedType L) EncodedType.nat
  have hCtx :
      TMPolyTimeMap P (tmVerifierXOnlyActionInputEncodedType L)
        (fun q : P.Carrier => q.1) := by
    simpa [P] using TMPolyTimeMap.fst (tmVerifierXOnlyActionInputEncodedType L)
      EncodedType.nat
  have hCell : TMPolyTimeMap P EncodedType.nat (fun q : P.Carrier => q.2) := by
    simpa [P] using TMPolyTimeMap.snd (tmVerifierXOnlyActionInputEncodedType L)
      EncodedType.nat
  have hTin : TMPolyTimeMap P EncodedType.nat (fun q : P.Carrier => q.1.1.2.1) := by
    have hComp := TMPolyTimeMap.comp
      (tmVerifierXOnlyActionInput_tin_tm_polytime (L := L)) hCtx
    simpa [Function.comp, P] using hComp
  have hTout : TMPolyTimeMap P EncodedType.nat (fun q : P.Carrier => q.1.1.2.2) := by
    have hComp := TMPolyTimeMap.comp
      (tmVerifierXOnlyActionInput_tout_tm_polytime (L := L)) hCtx
    simpa [Function.comp, P] using hComp
  have hAnt : TMPolyTimeMap P (EncodedType.list literalStructuredEncodedType)
      (fun q : P.Carrier => q.1.2) := by
    have hComp := TMPolyTimeMap.comp
      (tmVerifierXOnlyActionInput_antecedents_tm_polytime (L := L)) hCtx
    simpa [Function.comp, P] using hComp
  have hCellSucc : TMPolyTimeMap P EncodedType.nat
      (fun q : P.Carrier => (show Nat from q.2) + 1) := by
    have hComp := TMPolyTimeMap.comp (nat_add_const_tm_polytime 1) hCell
    simpa [Function.comp, P] using hComp
  have hInInput : TMPolyTimeMap P tmVerifierTimeCellEncodedType
      (fun q : P.Carrier => (q.1.1.2.1, q.2)) :=
    TMPolyTimeMap.prod_mk hTin hCell
  have hOutInput : TMPolyTimeMap P tmVerifierTimeCellEncodedType
      (fun q : P.Carrier => (q.1.1.2.2, (show Nat from q.2) + 1)) :=
    TMPolyTimeMap.prod_mk hTout hCellSucc
  have hAtomIn :
      TMPolyTimeMap P literalStructuredEncodedType
        (fun q : P.Carrier =>
          TMVerifierStackReadChoice.atomAt (V := V) (k := k) q.1.1.2.1 q.2 choice) := by
    have hComp := TMPolyTimeMap.comp
      (tmVerifierStackReadChoice_atomAt_timeCell_tm_polytime V k choice) hInInput
    simpa [Function.comp, P] using hComp
  have hAtomOut :
      TMPolyTimeMap P literalStructuredEncodedType
        (fun q : P.Carrier =>
          TMVerifierStackReadChoice.atomAt (V := V) (k := k) q.1.1.2.2
            ((show Nat from q.2) + 1) choice) := by
    have hComp := TMPolyTimeMap.comp
      (tmVerifierStackReadChoice_atomAt_timeCell_tm_polytime V k choice) hOutInput
    simpa [Function.comp, P] using hComp
  have hAntIn :=
    literal_append_singleton_of_tm_polytime hAnt hAtomIn
  have hClause := tmVerifierImplicationClause_of_tm_polytime hAntIn hAtomOut
  simpa [tmVerifierPushShiftClause, P] using hClause

theorem tmVerifierPopShiftClause_actionCell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (k : tmVerifierStackIndex V) (choice : TMVerifierStackReadChoice V k) :
    TMPolyTimeMap
      (EncodedType.prod (tmVerifierXOnlyActionInputEncodedType L) EncodedType.nat)
      clauseStructuredEncodedType
      (fun q : TMVerifierXOnlyActionInput L × Nat =>
        tmVerifierPopShiftClause V q.1.1.2.1 q.1.1.2.2 k q.2 choice q.1.2) := by
  let P := EncodedType.prod (tmVerifierXOnlyActionInputEncodedType L) EncodedType.nat
  have hCtx :
      TMPolyTimeMap P (tmVerifierXOnlyActionInputEncodedType L)
        (fun q : P.Carrier => q.1) := by
    simpa [P] using TMPolyTimeMap.fst (tmVerifierXOnlyActionInputEncodedType L)
      EncodedType.nat
  have hCell : TMPolyTimeMap P EncodedType.nat (fun q : P.Carrier => q.2) := by
    simpa [P] using TMPolyTimeMap.snd (tmVerifierXOnlyActionInputEncodedType L)
      EncodedType.nat
  have hTin : TMPolyTimeMap P EncodedType.nat (fun q : P.Carrier => q.1.1.2.1) := by
    have hComp := TMPolyTimeMap.comp
      (tmVerifierXOnlyActionInput_tin_tm_polytime (L := L)) hCtx
    simpa [Function.comp, P] using hComp
  have hTout : TMPolyTimeMap P EncodedType.nat (fun q : P.Carrier => q.1.1.2.2) := by
    have hComp := TMPolyTimeMap.comp
      (tmVerifierXOnlyActionInput_tout_tm_polytime (L := L)) hCtx
    simpa [Function.comp, P] using hComp
  have hAnt : TMPolyTimeMap P (EncodedType.list literalStructuredEncodedType)
      (fun q : P.Carrier => q.1.2) := by
    have hComp := TMPolyTimeMap.comp
      (tmVerifierXOnlyActionInput_antecedents_tm_polytime (L := L)) hCtx
    simpa [Function.comp, P] using hComp
  have hCellSucc : TMPolyTimeMap P EncodedType.nat
      (fun q : P.Carrier => (show Nat from q.2) + 1) := by
    have hComp := TMPolyTimeMap.comp (nat_add_const_tm_polytime 1) hCell
    simpa [Function.comp, P] using hComp
  have hInInput : TMPolyTimeMap P tmVerifierTimeCellEncodedType
      (fun q : P.Carrier => (q.1.1.2.1, (show Nat from q.2) + 1)) :=
    TMPolyTimeMap.prod_mk hTin hCellSucc
  have hOutInput : TMPolyTimeMap P tmVerifierTimeCellEncodedType
      (fun q : P.Carrier => (q.1.1.2.2, q.2)) :=
    TMPolyTimeMap.prod_mk hTout hCell
  have hAtomIn :
      TMPolyTimeMap P literalStructuredEncodedType
        (fun q : P.Carrier =>
          TMVerifierStackReadChoice.atomAt (V := V) (k := k) q.1.1.2.1
            ((show Nat from q.2) + 1) choice) := by
    have hComp := TMPolyTimeMap.comp
      (tmVerifierStackReadChoice_atomAt_timeCell_tm_polytime V k choice) hInInput
    simpa [Function.comp, P] using hComp
  have hAtomOut :
      TMPolyTimeMap P literalStructuredEncodedType
        (fun q : P.Carrier =>
          TMVerifierStackReadChoice.atomAt (V := V) (k := k) q.1.1.2.2 q.2 choice) := by
    have hComp := TMPolyTimeMap.comp
      (tmVerifierStackReadChoice_atomAt_timeCell_tm_polytime V k choice) hOutInput
    simpa [Function.comp, P] using hComp
  have hAntIn :=
    literal_append_singleton_of_tm_polytime hAnt hAtomIn
  have hClause := tmVerifierImplicationClause_of_tm_polytime hAntIn hAtomOut
  simpa [tmVerifierPopShiftClause, P] using hClause

theorem tmVerifierFrameChoiceCNFBetween_actionCell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (k : tmVerifierStackIndex V) (choice : TMVerifierStackReadChoice V k) :
    TMPolyTimeMap
      (EncodedType.prod (tmVerifierXOnlyActionInputEncodedType L) EncodedType.nat)
      cnfStructuredEncodedType
      (fun q : TMVerifierXOnlyActionInput L × Nat =>
        tmVerifierFrameChoiceCNFBetween V q.1.1.2.1 q.1.1.2.2 k q.2 choice q.1.2) := by
  let P := EncodedType.prod (tmVerifierXOnlyActionInputEncodedType L) EncodedType.nat
  have hCtx :
      TMPolyTimeMap P (tmVerifierXOnlyActionInputEncodedType L)
        (fun q : P.Carrier => q.1) := by
    simpa [P] using TMPolyTimeMap.fst (tmVerifierXOnlyActionInputEncodedType L)
      EncodedType.nat
  have hCell : TMPolyTimeMap P EncodedType.nat (fun q : P.Carrier => q.2) := by
    simpa [P] using TMPolyTimeMap.snd (tmVerifierXOnlyActionInputEncodedType L)
      EncodedType.nat
  have hLeft :
      TMPolyTimeMap P
        (EncodedType.prod L.Instance (EncodedType.prod EncodedType.nat EncodedType.nat))
        (fun q : P.Carrier => q.1.1) := by
    have hFst := TMPolyTimeMap.fst
      (EncodedType.prod L.Instance (EncodedType.prod EncodedType.nat EncodedType.nat))
      (EncodedType.list literalStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hCtx
    simpa [Function.comp, tmVerifierXOnlyActionInputEncodedType, P] using hComp
  have hTimes :
      TMPolyTimeMap P (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun q : P.Carrier => q.1.1.2) := by
    have hSnd := TMPolyTimeMap.snd L.Instance
      (EncodedType.prod EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hLeft
    simpa [Function.comp, P] using hComp
  have hTin : TMPolyTimeMap P EncodedType.nat (fun q : P.Carrier => q.1.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hTimes
    simpa [Function.comp, P] using hComp
  have hTout : TMPolyTimeMap P EncodedType.nat (fun q : P.Carrier => q.1.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hTimes
    simpa [Function.comp, P] using hComp
  have hAnt :
      TMPolyTimeMap P (EncodedType.list literalStructuredEncodedType)
        (fun q : P.Carrier => q.1.2) := by
    have hSnd := TMPolyTimeMap.snd
      (EncodedType.prod L.Instance (EncodedType.prod EncodedType.nat EncodedType.nat))
      (EncodedType.list literalStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, tmVerifierXOnlyActionInputEncodedType, P] using hComp
  have hInInput :
      TMPolyTimeMap P tmVerifierTimeCellEncodedType
        (fun q : P.Carrier => (q.1.1.2.1, q.2)) :=
    TMPolyTimeMap.prod_mk hTin hCell
  have hOutInput :
      TMPolyTimeMap P tmVerifierTimeCellEncodedType
        (fun q : P.Carrier => (q.1.1.2.2, q.2)) :=
    TMPolyTimeMap.prod_mk hTout hCell
  have hAtomIn :
      TMPolyTimeMap P literalStructuredEncodedType
        (fun q : P.Carrier =>
          TMVerifierStackReadChoice.atomAt (V := V) (k := k) q.1.1.2.1 q.2 choice) := by
    have hComp := TMPolyTimeMap.comp
      (tmVerifierStackReadChoice_atomAt_timeCell_tm_polytime V k choice) hInInput
    simpa [Function.comp, P] using hComp
  have hAtomOut :
      TMPolyTimeMap P literalStructuredEncodedType
        (fun q : P.Carrier =>
          TMVerifierStackReadChoice.atomAt (V := V) (k := k) q.1.1.2.2 q.2 choice) := by
    have hComp := TMPolyTimeMap.comp
      (tmVerifierStackReadChoice_atomAt_timeCell_tm_polytime V k choice) hOutInput
    simpa [Function.comp, P] using hComp
  have hForwardAntInput :
      TMPolyTimeMap P
        (EncodedType.prod (EncodedType.list literalStructuredEncodedType)
          literalStructuredEncodedType)
        (fun q : P.Carrier =>
          (q.1.2,
            TMVerifierStackReadChoice.atomAt (V := V) (k := k) q.1.1.2.1 q.2 choice)) :=
    TMPolyTimeMap.prod_mk hAnt hAtomIn
  have hForwardAnt :
      TMPolyTimeMap P (EncodedType.list literalStructuredEncodedType)
        (fun q : P.Carrier =>
          (show List Literal from q.1.2) ++
            [TMVerifierStackReadChoice.atomAt (V := V) (k := k) q.1.1.2.1 q.2 choice]) := by
    have hComp := TMPolyTimeMap.comp literal_append_singleton_tm_polytime hForwardAntInput
    simpa [Function.comp, P] using hComp
  have hForwardInput :
      TMPolyTimeMap P
        (EncodedType.prod (EncodedType.list literalStructuredEncodedType)
          literalStructuredEncodedType)
        (fun q : P.Carrier =>
          ((show List Literal from q.1.2) ++
              [TMVerifierStackReadChoice.atomAt (V := V) (k := k) q.1.1.2.1 q.2 choice],
            TMVerifierStackReadChoice.atomAt (V := V) (k := k) q.1.1.2.2 q.2 choice)) :=
    TMPolyTimeMap.prod_mk hForwardAnt hAtomOut
  have hForward :
      TMPolyTimeMap P clauseStructuredEncodedType
        (fun q : P.Carrier =>
          tmVerifierFrameForwardClause V q.1.1.2.1 q.1.1.2.2 k q.2 choice q.1.2) := by
    have hComp := TMPolyTimeMap.comp tmVerifierImplicationClause_tm_polytime hForwardInput
    simpa [Function.comp, tmVerifierFrameForwardClause, P] using hComp
  have hBackwardAntInput :
      TMPolyTimeMap P
        (EncodedType.prod (EncodedType.list literalStructuredEncodedType)
          literalStructuredEncodedType)
        (fun q : P.Carrier =>
          (q.1.2,
            TMVerifierStackReadChoice.atomAt (V := V) (k := k) q.1.1.2.2 q.2 choice)) :=
    TMPolyTimeMap.prod_mk hAnt hAtomOut
  have hBackwardAnt :
      TMPolyTimeMap P (EncodedType.list literalStructuredEncodedType)
        (fun q : P.Carrier =>
          (show List Literal from q.1.2) ++
            [TMVerifierStackReadChoice.atomAt (V := V) (k := k) q.1.1.2.2 q.2 choice]) := by
    have hComp := TMPolyTimeMap.comp literal_append_singleton_tm_polytime hBackwardAntInput
    simpa [Function.comp, P] using hComp
  have hBackwardInput :
      TMPolyTimeMap P
        (EncodedType.prod (EncodedType.list literalStructuredEncodedType)
          literalStructuredEncodedType)
        (fun q : P.Carrier =>
          ((show List Literal from q.1.2) ++
              [TMVerifierStackReadChoice.atomAt (V := V) (k := k) q.1.1.2.2 q.2 choice],
            TMVerifierStackReadChoice.atomAt (V := V) (k := k) q.1.1.2.1 q.2 choice)) :=
    TMPolyTimeMap.prod_mk hBackwardAnt hAtomIn
  have hBackward :
      TMPolyTimeMap P clauseStructuredEncodedType
        (fun q : P.Carrier =>
          tmVerifierFrameBackwardClause V q.1.1.2.1 q.1.1.2.2 k q.2 choice q.1.2) := by
    have hComp := TMPolyTimeMap.comp tmVerifierImplicationClause_tm_polytime hBackwardInput
    simpa [Function.comp, tmVerifierFrameBackwardClause, P] using hComp
  have hPair :
      TMPolyTimeMap P
        (EncodedType.prod clauseStructuredEncodedType clauseStructuredEncodedType)
        (fun q : P.Carrier =>
          (tmVerifierFrameForwardClause V q.1.1.2.1 q.1.1.2.2 k q.2 choice q.1.2,
            tmVerifierFrameBackwardClause V q.1.1.2.1 q.1.1.2.2 k q.2 choice q.1.2)) :=
    TMPolyTimeMap.prod_mk hForward hBackward
  have hCNF := TMPolyTimeMap.comp clausePairCNF_tm_polytime hPair
  simpa [Function.comp, tmVerifierFrameChoiceCNFBetween, P] using hCNF

theorem tmVerifierFrameCellCNFBetween_actionCell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap
      (EncodedType.prod (tmVerifierXOnlyActionInputEncodedType L) EncodedType.nat)
      cnfStructuredEncodedType
      (fun q : TMVerifierXOnlyActionInput L × Nat =>
        tmVerifierFrameCellCNFBetween V q.1.1.2.1 q.1.1.2.2 k q.2 q.1.2) := by
  let choices := tmVerifierStackReadChoices V k
  change TMPolyTimeMap
    (EncodedType.prod (tmVerifierXOnlyActionInputEncodedType L) EncodedType.nat)
    cnfStructuredEncodedType
    (fun q : TMVerifierXOnlyActionInput L × Nat =>
      choices.flatMap fun choice =>
        tmVerifierFrameChoiceCNFBetween V q.1.1.2.1 q.1.1.2.2 k q.2 choice q.1.2)
  induction choices with
  | nil =>
      exact TMPolyTimeMap.const
        (EncodedType.prod (tmVerifierXOnlyActionInputEncodedType L) EncodedType.nat)
        cnfStructuredEncodedType []
  | cons choice choices ih =>
      have hHead := tmVerifierFrameChoiceCNFBetween_actionCell_tm_polytime V k choice
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap
            (EncodedType.prod (tmVerifierXOnlyActionInputEncodedType L) EncodedType.nat)
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun q : TMVerifierXOnlyActionInput L × Nat =>
              (tmVerifierFrameChoiceCNFBetween V q.1.1.2.1 q.1.1.2.2 k q.2 choice q.1.2,
                choices.flatMap fun choice =>
                  tmVerifierFrameChoiceCNFBetween V q.1.1.2.1 q.1.1.2.2 k q.2 choice
                    q.1.2)) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hAppend := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
      simpa [Function.comp, tmVerifierFrameCellCNFBetween, cnfStructuredEncodedType]
        using hAppend

theorem tmVerifierXOnlyFrameStackCNFBetween_action_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L) cnfStructuredEncodedType
      (fun q : TMVerifierXOnlyActionInput L =>
        tmVerifierXOnlyFrameStackCNFBetween V q.1.1 q.1.2.1 q.1.2.2 k q.2) := by
  let P := tmVerifierXOnlyActionInputEncodedType L
  have hX : TMPolyTimeMap P L.Instance (fun q : P.Carrier => q.1.1) := by
    have hLeft := TMPolyTimeMap.fst
      (EncodedType.prod L.Instance (EncodedType.prod EncodedType.nat EncodedType.nat))
      (EncodedType.list literalStructuredEncodedType)
    have hCompLeft := TMPolyTimeMap.comp hLeft (TMPolyTimeMap.id P)
    have hFst := TMPolyTimeMap.fst L.Instance
      (EncodedType.prod EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hFst hCompLeft
    simpa [Function.comp, P, tmVerifierXOnlyActionInputEncodedType] using hComp
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
    (fun q cell => tmVerifierFrameCellCNFBetween V q.1.2.1 q.1.2.2 k cell q.2)
    (tmVerifierFrameCellCNFBetween_actionCell_tm_polytime V k)
  have hComp := TMPolyTimeMap.comp hFold hInput
  simpa [Function.comp, tmVerifierXOnlyFrameStackCNFBetween, P] using hComp

theorem tmVerifierXOnlyFrameAllStacksCNFBetween_action_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L) cnfStructuredEncodedType
      (fun q : TMVerifierXOnlyActionInput L =>
        tmVerifierXOnlyFrameAllStacksCNFBetween V q.1.1 q.1.2.1 q.1.2.2 q.2) := by
  let ksAll := tmVerifierStackList V
  change TMPolyTimeMap (tmVerifierXOnlyActionInputEncodedType L) cnfStructuredEncodedType
    (fun q : TMVerifierXOnlyActionInput L =>
      ksAll.flatMap fun k =>
        tmVerifierXOnlyFrameStackCNFBetween V q.1.1 q.1.2.1 q.1.2.2 k q.2)
  induction ksAll with
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
      simpa [Function.comp, tmVerifierXOnlyFrameAllStacksCNFBetween, cnfStructuredEncodedType]
        using hAppend

end SAT
end ComplexityReduction
