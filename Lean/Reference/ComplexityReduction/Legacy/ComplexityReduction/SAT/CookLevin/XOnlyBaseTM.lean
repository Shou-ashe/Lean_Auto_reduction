/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyRowsTM

/-!
Direct standard-TM witnesses for x-only Cook-Levin base blocks.

This file starts the aggregate base generator after stack-row aggregation.  The
first completed block is the finite-control domain over every x-only macro time
row.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Variable-time finite-control atoms -/

theorem tmVerifierLabelAtom_time_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (l : Option (tmVerifierTM V).Λ) :
    TMPolyTimeMap EncodedType.nat literalStructuredEncodedType
      (fun t : Nat => tmVerifierLabelAtom V t l) := by
  have hZero :
      TMPolyTimeMap EncodedType.nat EncodedType.nat (fun _ : Nat => (0 : Nat)) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.nat (0 : Nat)
  have hInput :
      TMPolyTimeMap EncodedType.nat tmVerifierTimeCellEncodedType
        (fun t : Nat => (t, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id EncodedType.nat) hZero
  have hAtom :=
    tmVerifierTableauAtom_timeCell_tm_polytime
      TMVerifierTableauVarKind.label 0 (tmVerifierLabelCode V l)
  have hComp := TMPolyTimeMap.comp hAtom hInput
  simpa [Function.comp, tmVerifierLabelAtom, tmVerifierTimeCellEncodedType] using hComp

theorem tmVerifierStateAtom_time_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (s : (tmVerifierTM V).σ) :
    TMPolyTimeMap EncodedType.nat literalStructuredEncodedType
      (fun t : Nat => tmVerifierStateAtom V t s) := by
  have hZero :
      TMPolyTimeMap EncodedType.nat EncodedType.nat (fun _ : Nat => (0 : Nat)) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.nat (0 : Nat)
  have hInput :
      TMPolyTimeMap EncodedType.nat tmVerifierTimeCellEncodedType
        (fun t : Nat => (t, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id EncodedType.nat) hZero
  have hAtom :=
    tmVerifierTableauAtom_timeCell_tm_polytime
      TMVerifierTableauVarKind.state 0 (tmVerifierStateCode V s)
  have hComp := TMPolyTimeMap.comp hAtom hInput
  simpa [Function.comp, tmVerifierStateAtom, tmVerifierTimeCellEncodedType] using hComp

theorem tmVerifierLabelAtom_neg_time_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (l : Option (tmVerifierTM V).Λ) :
    TMPolyTimeMap EncodedType.nat literalStructuredEncodedType
      (fun t : Nat => Clause.negate (tmVerifierLabelAtom V t l)) := by
  have hAtom := tmVerifierLabelAtom_time_tm_polytime V l
  have hComp := TMPolyTimeMap.comp literalNegateTMBackedMap.tm_polytime hAtom
  simpa [Function.comp] using hComp

theorem tmVerifierStateAtom_neg_time_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (s : (tmVerifierTM V).σ) :
    TMPolyTimeMap EncodedType.nat literalStructuredEncodedType
      (fun t : Nat => Clause.negate (tmVerifierStateAtom V t s)) := by
  have hAtom := tmVerifierStateAtom_time_tm_polytime V s
  have hComp := TMPolyTimeMap.comp literalNegateTMBackedMap.tm_polytime hAtom
  simpa [Function.comp] using hComp

/-! ### Exactly-one finite-control rows -/

theorem tmVerifierLabelAtomsFor_time_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (labels : List (Option (tmVerifierTM V).Λ)) :
    TMPolyTimeMap EncodedType.nat (EncodedType.list literalStructuredEncodedType)
      (fun t : Nat => labels.map fun l => tmVerifierLabelAtom V t l) := by
  induction labels with
  | nil =>
      exact TMPolyTimeMap.const EncodedType.nat
        (EncodedType.list literalStructuredEncodedType) []
  | cons l labels ih =>
      have hHead := tmVerifierLabelAtom_time_tm_polytime V l
      have hTail := ih
      have hConsInput :
          TMPolyTimeMap EncodedType.nat
            (EncodedType.prod literalStructuredEncodedType
              (EncodedType.list literalStructuredEncodedType))
            (fun t : Nat =>
              (tmVerifierLabelAtom V t l,
                labels.map fun l => tmVerifierLabelAtom V t l)) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hCons := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons literalStructuredEncodedType)
        hConsInput
      simpa [Function.comp] using hCons

theorem tmVerifierStateAtomsFor_time_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (states : List (tmVerifierTM V).σ) :
    TMPolyTimeMap EncodedType.nat (EncodedType.list literalStructuredEncodedType)
      (fun t : Nat => states.map fun s => tmVerifierStateAtom V t s) := by
  induction states with
  | nil =>
      exact TMPolyTimeMap.const EncodedType.nat
        (EncodedType.list literalStructuredEncodedType) []
  | cons s states ih =>
      have hHead := tmVerifierStateAtom_time_tm_polytime V s
      have hTail := ih
      have hConsInput :
          TMPolyTimeMap EncodedType.nat
            (EncodedType.prod literalStructuredEncodedType
              (EncodedType.list literalStructuredEncodedType))
            (fun t : Nat =>
              (tmVerifierStateAtom V t s,
                states.map fun s => tmVerifierStateAtom V t s)) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hCons := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons literalStructuredEncodedType)
        hConsInput
      simpa [Function.comp] using hCons

theorem tmVerifierLabelAtMostOneWithCNF_time_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (head : Option (tmVerifierTM V).Λ)
    (tail : List (Option (tmVerifierTM V).Λ)) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun t : Nat =>
        CookLevin.atMostOneWithCNF (tmVerifierLabelAtom V t head)
          (tail.map fun l => tmVerifierLabelAtom V t l)) := by
  induction tail with
  | nil =>
      exact TMPolyTimeMap.const EncodedType.nat cnfStructuredEncodedType []
  | cons l tail ih =>
      have hHeadNeg := tmVerifierLabelAtom_neg_time_tm_polytime V head
      have hLabelNeg := tmVerifierLabelAtom_neg_time_tm_polytime V l
      have hPair :
          TMPolyTimeMap EncodedType.nat
            (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
            (fun t : Nat =>
              (Clause.negate (tmVerifierLabelAtom V t head),
                Clause.negate (tmVerifierLabelAtom V t l))) :=
        TMPolyTimeMap.prod_mk hHeadNeg hLabelNeg
      have hClause :
          TMPolyTimeMap EncodedType.nat clauseStructuredEncodedType
            (fun t : Nat =>
              [Clause.negate (tmVerifierLabelAtom V t head),
                Clause.negate (tmVerifierLabelAtom V t l)]) := by
        have hComp := TMPolyTimeMap.comp literalPairClause_tm_polytime hPair
        simpa [Function.comp] using hComp
      have hTail := ih
      have hConsInput :
          TMPolyTimeMap EncodedType.nat
            (EncodedType.prod clauseStructuredEncodedType cnfStructuredEncodedType)
            (fun t : Nat =>
              ([Clause.negate (tmVerifierLabelAtom V t head),
                  Clause.negate (tmVerifierLabelAtom V t l)],
                CookLevin.atMostOneWithCNF (tmVerifierLabelAtom V t head)
                  (tail.map fun l => tmVerifierLabelAtom V t l))) :=
        TMPolyTimeMap.prod_mk hClause hTail
      have hCons := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons clauseStructuredEncodedType)
        hConsInput
      simpa [Function.comp, CookLevin.atMostOneWithCNF, cnfStructuredEncodedType,
        clauseStructuredEncodedType] using hCons

theorem tmVerifierStateAtMostOneWithCNF_time_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (head : (tmVerifierTM V).σ) (tail : List (tmVerifierTM V).σ) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun t : Nat =>
        CookLevin.atMostOneWithCNF (tmVerifierStateAtom V t head)
          (tail.map fun s => tmVerifierStateAtom V t s)) := by
  induction tail with
  | nil =>
      exact TMPolyTimeMap.const EncodedType.nat cnfStructuredEncodedType []
  | cons s tail ih =>
      have hHeadNeg := tmVerifierStateAtom_neg_time_tm_polytime V head
      have hStateNeg := tmVerifierStateAtom_neg_time_tm_polytime V s
      have hPair :
          TMPolyTimeMap EncodedType.nat
            (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
            (fun t : Nat =>
              (Clause.negate (tmVerifierStateAtom V t head),
                Clause.negate (tmVerifierStateAtom V t s))) :=
        TMPolyTimeMap.prod_mk hHeadNeg hStateNeg
      have hClause :
          TMPolyTimeMap EncodedType.nat clauseStructuredEncodedType
            (fun t : Nat =>
              [Clause.negate (tmVerifierStateAtom V t head),
                Clause.negate (tmVerifierStateAtom V t s)]) := by
        have hComp := TMPolyTimeMap.comp literalPairClause_tm_polytime hPair
        simpa [Function.comp] using hComp
      have hTail := ih
      have hConsInput :
          TMPolyTimeMap EncodedType.nat
            (EncodedType.prod clauseStructuredEncodedType cnfStructuredEncodedType)
            (fun t : Nat =>
              ([Clause.negate (tmVerifierStateAtom V t head),
                  Clause.negate (tmVerifierStateAtom V t s)],
                CookLevin.atMostOneWithCNF (tmVerifierStateAtom V t head)
                  (tail.map fun s => tmVerifierStateAtom V t s))) :=
        TMPolyTimeMap.prod_mk hClause hTail
      have hCons := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons clauseStructuredEncodedType)
        hConsInput
      simpa [Function.comp, CookLevin.atMostOneWithCNF, cnfStructuredEncodedType,
        clauseStructuredEncodedType] using hCons

theorem tmVerifierLabelAtMostOneCNF_time_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (labels : List (Option (tmVerifierTM V).Λ)) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun t : Nat =>
        CookLevin.atMostOneCNF (labels.map fun l => tmVerifierLabelAtom V t l)) := by
  induction labels with
  | nil =>
      exact TMPolyTimeMap.const EncodedType.nat cnfStructuredEncodedType []
  | cons l labels ih =>
      have hWith := tmVerifierLabelAtMostOneWithCNF_time_tm_polytime V l labels
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap EncodedType.nat
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun t : Nat =>
              (CookLevin.atMostOneWithCNF (tmVerifierLabelAtom V t l)
                (labels.map fun l => tmVerifierLabelAtom V t l),
                CookLevin.atMostOneCNF
                  (labels.map fun l => tmVerifierLabelAtom V t l))) :=
        TMPolyTimeMap.prod_mk hWith hTail
      have hAppend := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
        hAppendInput
      simpa [Function.comp, CookLevin.atMostOneCNF, cnfStructuredEncodedType] using hAppend

theorem tmVerifierStateAtMostOneCNF_time_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (states : List (tmVerifierTM V).σ) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun t : Nat =>
        CookLevin.atMostOneCNF (states.map fun s => tmVerifierStateAtom V t s)) := by
  induction states with
  | nil =>
      exact TMPolyTimeMap.const EncodedType.nat cnfStructuredEncodedType []
  | cons s states ih =>
      have hWith := tmVerifierStateAtMostOneWithCNF_time_tm_polytime V s states
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap EncodedType.nat
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun t : Nat =>
              (CookLevin.atMostOneWithCNF (tmVerifierStateAtom V t s)
                (states.map fun s => tmVerifierStateAtom V t s),
                CookLevin.atMostOneCNF
                  (states.map fun s => tmVerifierStateAtom V t s))) :=
        TMPolyTimeMap.prod_mk hWith hTail
      have hAppend := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
        hAppendInput
      simpa [Function.comp, CookLevin.atMostOneCNF, cnfStructuredEncodedType] using hAppend

theorem tmVerifierExactlyOneLabelFor_time_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (labels : List (Option (tmVerifierTM V).Λ)) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun t : Nat =>
        CookLevin.exactlyOneCNF (labels.map fun l => tmVerifierLabelAtom V t l)) := by
  have hAtoms := tmVerifierLabelAtomsFor_time_tm_polytime V labels
  have hAtLeast :
      TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
        (fun t : Nat =>
          CookLevin.atLeastOneCNF (labels.map fun l => tmVerifierLabelAtom V t l)) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton clauseStructuredEncodedType)
      hAtoms
    simpa [Function.comp, CookLevin.atLeastOneCNF, cnfStructuredEncodedType,
      clauseStructuredEncodedType] using hComp
  have hAtMost := tmVerifierLabelAtMostOneCNF_time_tm_polytime V labels
  have hAppendInput :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun t : Nat =>
          (CookLevin.atLeastOneCNF (labels.map fun l => tmVerifierLabelAtom V t l),
            CookLevin.atMostOneCNF (labels.map fun l => tmVerifierLabelAtom V t l))) :=
    TMPolyTimeMap.prod_mk hAtLeast hAtMost
  have hAppend := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
    hAppendInput
  simpa [Function.comp, CookLevin.exactlyOneCNF, cnfStructuredEncodedType] using hAppend

theorem tmVerifierExactlyOneStateFor_time_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (states : List (tmVerifierTM V).σ) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun t : Nat =>
        CookLevin.exactlyOneCNF (states.map fun s => tmVerifierStateAtom V t s)) := by
  have hAtoms := tmVerifierStateAtomsFor_time_tm_polytime V states
  have hAtLeast :
      TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
        (fun t : Nat =>
          CookLevin.atLeastOneCNF (states.map fun s => tmVerifierStateAtom V t s)) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton clauseStructuredEncodedType)
      hAtoms
    simpa [Function.comp, CookLevin.atLeastOneCNF, cnfStructuredEncodedType,
      clauseStructuredEncodedType] using hComp
  have hAtMost := tmVerifierStateAtMostOneCNF_time_tm_polytime V states
  have hAppendInput :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun t : Nat =>
          (CookLevin.atLeastOneCNF (states.map fun s => tmVerifierStateAtom V t s),
            CookLevin.atMostOneCNF (states.map fun s => tmVerifierStateAtom V t s))) :=
    TMPolyTimeMap.prod_mk hAtLeast hAtMost
  have hAppend := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
    hAppendInput
  simpa [Function.comp, CookLevin.exactlyOneCNF, cnfStructuredEncodedType] using hAppend

theorem tmVerifierExactlyOneLabelCNFAt_time_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun t : Nat => tmVerifierExactlyOneLabelCNFAt V t) := by
  classical
  letI : Fintype (tmVerifierTM V).Λ := (tmVerifierTM V).ΛFin
  letI : Fintype (Option (tmVerifierTM V).Λ) := inferInstance
  simpa [tmVerifierExactlyOneLabelCNFAt, tmVerifierLabelAtomsAt] using
    tmVerifierExactlyOneLabelFor_time_tm_polytime V
      ((Finset.univ : Finset (Option (tmVerifierTM V).Λ)).toList)

theorem tmVerifierExactlyOneStateCNFAt_time_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun t : Nat => tmVerifierExactlyOneStateCNFAt V t) := by
  classical
  letI : Fintype (tmVerifierTM V).σ := (tmVerifierTM V).σFin
  simpa [tmVerifierExactlyOneStateCNFAt, tmVerifierStateAtomsAt] using
    tmVerifierExactlyOneStateFor_time_tm_polytime V
      ((Finset.univ : Finset (tmVerifierTM V).σ).toList)

theorem tmVerifierControlDomainCNFAt_time_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun t : Nat => tmVerifierControlDomainCNFAt V t) := by
  have hLabel := tmVerifierExactlyOneLabelCNFAt_time_tm_polytime V
  have hState := tmVerifierExactlyOneStateCNFAt_time_tm_polytime V
  have hAppendInput :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun t : Nat =>
          (tmVerifierExactlyOneLabelCNFAt V t, tmVerifierExactlyOneStateCNFAt V t)) :=
    TMPolyTimeMap.prod_mk hLabel hState
  have hAppend := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
    hAppendInput
  simpa [Function.comp, tmVerifierControlDomainCNFAt, cnfStructuredEncodedType] using hAppend

theorem tmVerifierXOnlyControlDomainRowsCNF_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier =>
        (tmVerifierXOnlyTableauTimeRange V x).flatMap fun t =>
          tmVerifierControlDomainCNFAt V t) := by
  have hTimes := tmVerifierXOnlyTableauTimeRange_tm_polytime V
  have hFold := cnfContextFlatMap_tm_polytime
    (C := EncodedType.raw Unit) (X := EncodedType.nat)
    (fun _ t => tmVerifierControlDomainCNFAt V t)
    (by
      have hBlock := tmVerifierControlDomainCNFAt_time_tm_polytime V
      have hTime :
          TMPolyTimeMap
            (EncodedType.prod (EncodedType.raw Unit) EncodedType.nat)
            EncodedType.nat
            (fun p : Unit × Nat => p.2) := by
        simpa using TMPolyTimeMap.snd (EncodedType.raw Unit) EncodedType.nat
      have hComp := TMPolyTimeMap.comp hBlock hTime
      simpa [Function.comp] using hComp)
  have hUnit :
      TMPolyTimeMap L.Instance (EncodedType.raw Unit) (fun _ : L.Instance.Carrier => ()) :=
    TMPolyTimeMap.const L.Instance (EncodedType.raw Unit) ()
  have hInput :
      TMPolyTimeMap L.Instance
        (EncodedType.prod (EncodedType.raw Unit) (EncodedType.list EncodedType.nat))
        (fun x : L.Instance.Carrier => ((), tmVerifierXOnlyTableauTimeRange V x)) :=
    TMPolyTimeMap.prod_mk hUnit hTimes
  have hComp := TMPolyTimeMap.comp hFold hInput
  simpa [Function.comp] using hComp

/-! ### Initial and endpoint finite-control clauses -/

theorem tmVerifierInitialControlCNF_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun _ : L.Instance.Carrier => tmVerifierInitialControlCNF V) :=
  TMPolyTimeMap.const L.Instance cnfStructuredEncodedType (tmVerifierInitialControlCNF V)

theorem tmVerifierHaltingControlCNFAt_time_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun t : Nat => tmVerifierHaltingControlCNFAt V t) := by
  have hLabel := tmVerifierLabelAtom_time_tm_polytime V none
  have hComp := TMPolyTimeMap.comp tmVerifierUnitCNF_tm_polytime hLabel
  simpa [Function.comp, tmVerifierHaltingControlCNFAt] using hComp

theorem tmVerifierInitialStateUnitCNFAt_time_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun t : Nat =>
        tmVerifierUnitCNF (tmVerifierStateAtom V t (tmVerifierTM V).initialState)) := by
  have hState := tmVerifierStateAtom_time_tm_polytime V (tmVerifierTM V).initialState
  have hComp := TMPolyTimeMap.comp tmVerifierUnitCNF_tm_polytime hState
  simpa [Function.comp] using hComp

theorem tmVerifierXOnlyEndpointControlCNF_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier =>
        tmVerifierHaltingControlCNFAt V (tmVerifierXOnlyTimeBound V x) ++
          tmVerifierUnitCNF
            (tmVerifierStateAtom V (tmVerifierXOnlyTimeBound V x)
              (tmVerifierTM V).initialState)) := by
  have hTime := tmVerifierXOnlyTimeBound_tm_polytime V
  have hHaltAtTime := tmVerifierHaltingControlCNFAt_time_tm_polytime V
  have hHalt :
      TMPolyTimeMap L.Instance cnfStructuredEncodedType
        (fun x : L.Instance.Carrier =>
          tmVerifierHaltingControlCNFAt V (tmVerifierXOnlyTimeBound V x)) := by
    have hComp := TMPolyTimeMap.comp hHaltAtTime hTime
    simpa [Function.comp] using hComp
  have hStateAtTime := tmVerifierInitialStateUnitCNFAt_time_tm_polytime V
  have hState :
      TMPolyTimeMap L.Instance cnfStructuredEncodedType
        (fun x : L.Instance.Carrier =>
          tmVerifierUnitCNF
            (tmVerifierStateAtom V (tmVerifierXOnlyTimeBound V x)
              (tmVerifierTM V).initialState)) := by
    have hComp := TMPolyTimeMap.comp hStateAtTime hTime
    simpa [Function.comp] using hComp
  have hAppendInput :
      TMPolyTimeMap L.Instance
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun x : L.Instance.Carrier =>
          (tmVerifierHaltingControlCNFAt V (tmVerifierXOnlyTimeBound V x),
            tmVerifierUnitCNF
              (tmVerifierStateAtom V (tmVerifierXOnlyTimeBound V x)
                (tmVerifierTM V).initialState))) :=
    TMPolyTimeMap.prod_mk hHalt hState
  have hAppend := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
    hAppendInput
  simpa [Function.comp, cnfStructuredEncodedType] using hAppend

/-! ### Fixed micro-domain base rows -/

theorem tmVerifierXOnlyFixedMicroTime_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (micro : Nat) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) EncodedType.nat
      (fun p : L.Instance.Carrier × Nat =>
        tmVerifierXOnlyFixedMicroTime V p.1 p.2 micro) := by
  let P := EncodedType.prod L.Instance EncodedType.nat
  have hX : TMPolyTimeMap P L.Instance (fun p : P.Carrier => p.1) := by
    simpa [P] using TMPolyTimeMap.fst L.Instance EncodedType.nat
  have hT : TMPolyTimeMap P EncodedType.nat (fun p : P.Carrier => p.2) := by
    simpa [P] using TMPolyTimeMap.snd L.Instance EncodedType.nat
  have hTimeBound :
      TMPolyTimeMap P EncodedType.nat
        (fun p : P.Carrier => tmVerifierXOnlyTimeBound V p.1) := by
    have hComp := TMPolyTimeMap.comp (tmVerifierXOnlyTimeBound_tm_polytime V) hX
    simpa [Function.comp, P] using hComp
  have hBase :
      TMPolyTimeMap P EncodedType.nat
        (fun p : P.Carrier => tmVerifierXOnlyFixedMicroBase V p.1) := by
    have hAddOne := nat_add_const_tm_polytime 1
    have hComp := TMPolyTimeMap.comp hAddOne hTimeBound
    simpa [Function.comp, tmVerifierXOnlyFixedMicroBase, P] using hComp
  have hMicro : TMPolyTimeMap P EncodedType.nat (fun _ : P.Carrier => micro) :=
    TMPolyTimeMap.const P EncodedType.nat micro
  have hPairInput :
      TMPolyTimeMap P (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : P.Carrier => (p.2, micro)) :=
    TMPolyTimeMap.prod_mk hT hMicro
  have hPair :
      TMPolyTimeMap P EncodedType.nat (fun p : P.Carrier => Nat.pair p.2 micro) := by
    have hComp := TMPolyTimeMap.comp natPair_tm_polytime hPairInput
    simpa [Function.comp, P] using hComp
  have hAddInput :
      TMPolyTimeMap P natAddInputEncodedType
        (fun p : P.Carrier => (tmVerifierXOnlyFixedMicroBase V p.1, Nat.pair p.2 micro)) :=
    TMPolyTimeMap.prod_mk hBase hPair
  have hAdd := TMPolyTimeMap.comp natAdd_tm_polytime hAddInput
  simpa [Function.comp, tmVerifierXOnlyFixedMicroTime, natAddInputEncodedType, P] using hAdd

theorem tmVerifierXOnlyAllStackWellFormedCNFAt_fixedMicro_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (micro : Nat) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        tmVerifierXOnlyAllStackWellFormedCNFAt V p.1
          (tmVerifierXOnlyFixedMicroTime V p.1 p.2 micro)) := by
  let P := EncodedType.prod L.Instance EncodedType.nat
  have hX : TMPolyTimeMap P L.Instance (fun p : P.Carrier => p.1) := by
    simpa [P] using TMPolyTimeMap.fst L.Instance EncodedType.nat
  have hTime := tmVerifierXOnlyFixedMicroTime_pair_tm_polytime V micro
  have hInput :
      TMPolyTimeMap P (EncodedType.prod L.Instance EncodedType.nat)
        (fun p : P.Carrier =>
          (p.1, tmVerifierXOnlyFixedMicroTime V p.1 p.2 micro)) :=
    TMPolyTimeMap.prod_mk hX hTime
  have hComp := TMPolyTimeMap.comp
    (tmVerifierXOnlyAllStackWellFormedCNFAt_pair_tm_polytime V) hInput
  simpa [Function.comp, P] using hComp

theorem tmVerifierXOnlyFixedMicroDomainForList_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (micros : List Nat) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        micros.flatMap fun micro =>
          tmVerifierXOnlyAllStackWellFormedCNFAt V p.1
            (tmVerifierXOnlyFixedMicroTime V p.1 p.2 micro)) := by
  induction micros with
  | nil =>
      exact TMPolyTimeMap.const (EncodedType.prod L.Instance EncodedType.nat)
        cnfStructuredEncodedType []
  | cons micro micros ih =>
      have hHead := tmVerifierXOnlyAllStackWellFormedCNFAt_fixedMicro_pair_tm_polytime
        V micro
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat)
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun p : L.Instance.Carrier × Nat =>
              (tmVerifierXOnlyAllStackWellFormedCNFAt V p.1
                (tmVerifierXOnlyFixedMicroTime V p.1 p.2 micro),
                micros.flatMap fun micro =>
                  tmVerifierXOnlyAllStackWellFormedCNFAt V p.1
                    (tmVerifierXOnlyFixedMicroTime V p.1 p.2 micro))) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hAppend := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
      simpa [Function.comp, cnfStructuredEncodedType] using hAppend

theorem tmVerifierXOnlyWindowFixedMicroDomainCNFAt_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (w : TMVerifierStmtWindow V) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        tmVerifierXOnlyWindowFixedMicroDomainCNFAt V p.1 p.2 w) := by
  simpa [tmVerifierXOnlyWindowFixedMicroDomainCNFAt,
    tmVerifierXOnlyAllStackWellFormedCNFAt] using
    tmVerifierXOnlyFixedMicroDomainForList_pair_tm_polytime V
      (tmVerifierWindowMicroTimeRange V w)

theorem tmVerifierXOnlyWindowFixedMicroDomainCNFAt_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (w : TMVerifierStmtWindow V) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier => tmVerifierXOnlyWindowFixedMicroDomainCNFAt V x t w) := by
  have hT : TMPolyTimeMap L.Instance EncodedType.nat (fun _ : L.Instance.Carrier => t) :=
    TMPolyTimeMap.const L.Instance EncodedType.nat t
  have hInput :
      TMPolyTimeMap L.Instance (EncodedType.prod L.Instance EncodedType.nat)
        (fun x : L.Instance.Carrier => (x, t)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id L.Instance) hT
  have hComp := TMPolyTimeMap.comp
    (tmVerifierXOnlyWindowFixedMicroDomainCNFAt_pair_tm_polytime V w) hInput
  simpa [Function.comp] using hComp

theorem tmVerifierXOnlyWindowFixedMicroDomainForList_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (windows : List (TMVerifierStmtWindow V)) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier =>
        windows.flatMap fun w => tmVerifierXOnlyWindowFixedMicroDomainCNFAt V x t w) := by
  induction windows with
  | nil =>
      exact TMPolyTimeMap.const L.Instance cnfStructuredEncodedType []
  | cons w windows ih =>
      have hHead := tmVerifierXOnlyWindowFixedMicroDomainCNFAt_tm_polytime V t w
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap L.Instance
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun x : L.Instance.Carrier =>
              (tmVerifierXOnlyWindowFixedMicroDomainCNFAt V x t w,
                windows.flatMap fun w =>
                  tmVerifierXOnlyWindowFixedMicroDomainCNFAt V x t w)) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hAppend := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
      simpa [Function.comp, cnfStructuredEncodedType] using hAppend

theorem tmVerifierXOnlyTransitionFixedMicroDomainForStates_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (l : (tmVerifierTM V).Λ) (states : List (tmVerifierTM V).σ) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier =>
        states.flatMap fun s =>
          (tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s).flatMap fun w =>
            tmVerifierXOnlyWindowFixedMicroDomainCNFAt V x t w) := by
  induction states with
  | nil =>
      exact TMPolyTimeMap.const L.Instance cnfStructuredEncodedType []
  | cons s states ih =>
      have hHead := tmVerifierXOnlyWindowFixedMicroDomainForList_tm_polytime V t
        (tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap L.Instance
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun x : L.Instance.Carrier =>
              ((tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s).flatMap fun w =>
                tmVerifierXOnlyWindowFixedMicroDomainCNFAt V x t w,
                states.flatMap fun s =>
                  (tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s).flatMap fun w =>
                    tmVerifierXOnlyWindowFixedMicroDomainCNFAt V x t w)) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hAppend := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
      simpa [Function.comp, cnfStructuredEncodedType] using hAppend

theorem tmVerifierXOnlyTransitionFixedMicroDomainForLabels_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (labels : List (tmVerifierTM V).Λ) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier =>
        labels.flatMap fun l =>
          (tmVerifierStateList V).flatMap fun s =>
            (tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s).flatMap fun w =>
              tmVerifierXOnlyWindowFixedMicroDomainCNFAt V x t w) := by
  induction labels with
  | nil =>
      exact TMPolyTimeMap.const L.Instance cnfStructuredEncodedType []
  | cons l labels ih =>
      have hHead := tmVerifierXOnlyTransitionFixedMicroDomainForStates_tm_polytime V t l
        (tmVerifierStateList V)
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap L.Instance
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun x : L.Instance.Carrier =>
              ((tmVerifierStateList V).flatMap fun s =>
                (tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s).flatMap fun w =>
                  tmVerifierXOnlyWindowFixedMicroDomainCNFAt V x t w,
                labels.flatMap fun l =>
                  (tmVerifierStateList V).flatMap fun s =>
                    (tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s).flatMap fun w =>
                      tmVerifierXOnlyWindowFixedMicroDomainCNFAt V x t w)) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hAppend := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
      simpa [Function.comp, cnfStructuredEncodedType] using hAppend

theorem tmVerifierXOnlyTransitionFixedMicroDomainCNFAt_fixedTime_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier =>
        tmVerifierXOnlyTransitionFixedMicroDomainCNFAt V x t) := by
  simpa [tmVerifierXOnlyTransitionFixedMicroDomainCNFAt] using
    tmVerifierXOnlyTransitionFixedMicroDomainForLabels_tm_polytime V t (tmVerifierLabelList V)

end SAT
end ComplexityReduction
