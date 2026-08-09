import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyTransitionsActionTM

/-!
Direct standard-TM witnesses for x-only transition window and row aggregation.

The witnesses here build on the low-level action generators and keep the row
folding layer split out so no Lean file exceeds the 1000-line limit.
-/

namespace ComplexityReduction
namespace SAT

theorem tmVerifierStmtWindowsAt_flatMap_surface_eq_zero
    {L : EncodedDecisionProblem} (V : TMVerifier L) {α : Type}
    (G :
      List (TMVerifierStackAction V) → Option (tmVerifierTM V).Λ →
        (tmVerifierTM V).σ → List α)
    (stmt : (tmVerifierTM V).Stmt) (s : (tmVerifierTM V).σ) (t : Nat) :
    (tmVerifierStmtWindowsAt V t stmt s).flatMap
        (fun w => G w.actions w.nextLabel w.nextState) =
      (tmVerifierStmtWindowsAt V 0 stmt s).flatMap
        (fun w => G w.actions w.nextLabel w.nextState) := by
  induction stmt generalizing s G with
  | push k f q ih =>
      simpa [tmVerifierStmtWindowsAt, TMVerifierStmtWindow.consAction, List.flatMap_map]
        using ih (fun actions nextLabel nextState =>
          G (TMVerifierStackAction.push (V := V) { stack := k, symbol := f s } :: actions)
            nextLabel nextState) s
  | peek k f q ih =>
      let choices := tmVerifierStackReadChoices V k
      change
        List.flatMap (fun w => G w.actions w.nextLabel w.nextState)
            (choices.flatMap fun choice =>
              (tmVerifierStmtWindowsAt V t q (f s choice.toOption)).map fun w =>
                TMVerifierStmtWindow.consAction (TMVerifierStackAction.peek (V := V) k choice)
                  (TMVerifierStmtWindow.consGuard
                    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice) w)) =
          List.flatMap (fun w => G w.actions w.nextLabel w.nextState)
            (choices.flatMap fun choice =>
              (tmVerifierStmtWindowsAt V 0 q (f s choice.toOption)).map fun w =>
                TMVerifierStmtWindow.consAction (TMVerifierStackAction.peek (V := V) k choice)
                  (TMVerifierStmtWindow.consGuard
                    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) 0 0 choice) w))
      induction choices with
      | nil => simp
      | cons choice rest ihChoices =>
          simp [TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            List.flatMap_map]
          rw [ih (fun actions nextLabel nextState =>
            G (TMVerifierStackAction.peek (V := V) k choice :: actions)
              nextLabel nextState) (f s choice.toOption)]
          simpa [ihChoices]
  | pop k f q ih =>
      let choices := tmVerifierStackReadChoices V k
      change
        List.flatMap (fun w => G w.actions w.nextLabel w.nextState)
            (choices.flatMap fun choice =>
              (tmVerifierStmtWindowsAt V t q (f s choice.toOption)).map fun w =>
                TMVerifierStmtWindow.consAction (TMVerifierStackAction.pop (V := V) k choice)
                  (TMVerifierStmtWindow.consGuard
                    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice) w)) =
          List.flatMap (fun w => G w.actions w.nextLabel w.nextState)
            (choices.flatMap fun choice =>
              (tmVerifierStmtWindowsAt V 0 q (f s choice.toOption)).map fun w =>
                TMVerifierStmtWindow.consAction (TMVerifierStackAction.pop (V := V) k choice)
                  (TMVerifierStmtWindow.consGuard
                    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) 0 0 choice) w))
      induction choices with
      | nil => simp
      | cons choice rest ihChoices =>
          simp [TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            List.flatMap_map]
          rw [ih (fun actions nextLabel nextState =>
            G (TMVerifierStackAction.pop (V := V) k choice :: actions)
              nextLabel nextState) (f s choice.toOption)]
          simpa [ihChoices]
  | load f q ih =>
      simpa [tmVerifierStmtWindowsAt, TMVerifierStmtWindow.consAction, List.flatMap_map]
        using ih (fun actions nextLabel nextState =>
          G (TMVerifierStackAction.load (V := V) :: actions) nextLabel nextState) (f s)
  | branch f q₁ q₂ ih₁ ih₂ =>
      by_cases h : f s
      · simpa [tmVerifierStmtWindowsAt, h, TMVerifierStmtWindow.consAction, List.flatMap_map]
          using ih₁ (fun actions nextLabel nextState =>
            G (TMVerifierStackAction.branch (V := V) TMVerifierStmtTag.branchTrue :: actions)
              nextLabel nextState) s
      · simpa [tmVerifierStmtWindowsAt, h, TMVerifierStmtWindow.consAction, List.flatMap_map]
          using ih₂ (fun actions nextLabel nextState =>
            G (TMVerifierStackAction.branch (V := V) TMVerifierStmtTag.branchFalse :: actions)
              nextLabel nextState) s
  | goto f =>
      simp [tmVerifierStmtWindowsAt]
  | halt =>
      simp [tmVerifierStmtWindowsAt]

theorem literalPairList_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
      (EncodedType.list literalStructuredEncodedType)
      (fun p : Literal × Literal => [p.1, p.2]) := by
  let P := EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType
  have hFirst : TMPolyTimeMap P literalStructuredEncodedType (fun p : P.Carrier => p.1) := by
    simpa [P] using TMPolyTimeMap.fst literalStructuredEncodedType literalStructuredEncodedType
  have hSecond :
      TMPolyTimeMap P literalStructuredEncodedType (fun p : P.Carrier => p.2) := by
    simpa [P] using TMPolyTimeMap.snd literalStructuredEncodedType literalStructuredEncodedType
  have hTail :
      TMPolyTimeMap P (EncodedType.list literalStructuredEncodedType)
        (fun p : P.Carrier => [p.2]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton literalStructuredEncodedType) hSecond
    simpa [Function.comp, P] using hComp
  have hConsInput :
      TMPolyTimeMap P
        (EncodedType.prod literalStructuredEncodedType
          (EncodedType.list literalStructuredEncodedType))
        (fun p : P.Carrier => (p.1, [p.2])) :=
    TMPolyTimeMap.prod_mk hFirst hTail
  have hCons := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons literalStructuredEncodedType)
    hConsInput
  simpa [Function.comp, P] using hCons

theorem literalPairList_append_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod
        (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
        (EncodedType.list literalStructuredEncodedType))
      (EncodedType.list literalStructuredEncodedType)
      (fun p : (Literal × Literal) × List Literal => [p.1.1, p.1.2] ++ p.2) := by
  let P := EncodedType.prod
    (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
    (EncodedType.list literalStructuredEncodedType)
  have hPair :
      TMPolyTimeMap P (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
        (fun p : P.Carrier => p.1) := by
    simpa [P] using TMPolyTimeMap.fst
      (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
      (EncodedType.list literalStructuredEncodedType)
  have hRest :
      TMPolyTimeMap P (EncodedType.list literalStructuredEncodedType)
        (fun p : P.Carrier => p.2) := by
    simpa [P] using TMPolyTimeMap.snd
      (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
      (EncodedType.list literalStructuredEncodedType)
  have hPrefix :
      TMPolyTimeMap P (EncodedType.list literalStructuredEncodedType)
        (fun p : P.Carrier => [p.1.1, p.1.2]) := by
    have hComp := TMPolyTimeMap.comp literalPairList_tm_polytime hPair
    simpa [Function.comp, P] using hComp
  have hAppendInput :
      TMPolyTimeMap P
        (EncodedType.prod (EncodedType.list literalStructuredEncodedType)
          (EncodedType.list literalStructuredEncodedType))
        (fun p : P.Carrier => ([p.1.1, p.1.2], p.2)) :=
    TMPolyTimeMap.prod_mk hPrefix hRest
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append literalStructuredEncodedType) hAppendInput
  simpa [Function.comp, P] using hAppend

theorem tmVerifierXOnlyFixedReadGuardAt_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (actionIdx : Nat) (act : TMVerifierStackAction V) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat)
      (EncodedType.list literalStructuredEncodedType)
      (fun p : L.Instance.Carrier × Nat =>
        act.xOnlyFixedReadGuardAt p.1 p.2 actionIdx) := by
  let P := EncodedType.prod L.Instance EncodedType.nat
  cases act with
  | push raw =>
      exact TMPolyTimeMap.const P (EncodedType.list literalStructuredEncodedType) []
  | peek k choice =>
      have hTime := tmVerifierXOnlyFixedMicroTime_pair_tm_polytime V actionIdx
      have hZero : TMPolyTimeMap P EncodedType.nat (fun _ : P.Carrier => (0 : Nat)) :=
        TMPolyTimeMap.const P EncodedType.nat (show Nat from 0)
      have hInput :
          TMPolyTimeMap P tmVerifierTimeCellEncodedType
            (fun p : P.Carrier =>
              (tmVerifierXOnlyFixedMicroTime V p.1 p.2 actionIdx, (0 : Nat))) :=
        TMPolyTimeMap.prod_mk hTime hZero
      have hAtom :
          TMPolyTimeMap P literalStructuredEncodedType
            (fun p : P.Carrier =>
              TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                (tmVerifierXOnlyFixedMicroTime V p.1 p.2 actionIdx) 0 choice) := by
        have hComp := TMPolyTimeMap.comp
          (tmVerifierStackReadChoice_atomAt_timeCell_tm_polytime V k choice) hInput
        simpa [Function.comp, P] using hComp
      have hSingleton := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_singleton literalStructuredEncodedType) hAtom
      simpa [Function.comp, TMVerifierStackAction.xOnlyFixedReadGuardAt, P] using hSingleton
  | pop k choice =>
      have hTime := tmVerifierXOnlyFixedMicroTime_pair_tm_polytime V actionIdx
      have hZero : TMPolyTimeMap P EncodedType.nat (fun _ : P.Carrier => (0 : Nat)) :=
        TMPolyTimeMap.const P EncodedType.nat (show Nat from 0)
      have hInput :
          TMPolyTimeMap P tmVerifierTimeCellEncodedType
            (fun p : P.Carrier =>
              (tmVerifierXOnlyFixedMicroTime V p.1 p.2 actionIdx, (0 : Nat))) :=
        TMPolyTimeMap.prod_mk hTime hZero
      have hAtom :
          TMPolyTimeMap P literalStructuredEncodedType
            (fun p : P.Carrier =>
              TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                (tmVerifierXOnlyFixedMicroTime V p.1 p.2 actionIdx) 0 choice) := by
        have hComp := TMPolyTimeMap.comp
          (tmVerifierStackReadChoice_atomAt_timeCell_tm_polytime V k choice) hInput
        simpa [Function.comp, P] using hComp
      have hSingleton := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_singleton literalStructuredEncodedType) hAtom
      simpa [Function.comp, TMVerifierStackAction.xOnlyFixedReadGuardAt, P] using hSingleton
  | load =>
      exact TMPolyTimeMap.const P (EncodedType.list literalStructuredEncodedType) []
  | branch tag =>
      exact TMPolyTimeMap.const P (EncodedType.list literalStructuredEncodedType) []

theorem tmVerifierXOnlyWindowFixedActionReadGuardsFrom_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (actions : List (TMVerifierStackAction V)) (idx : Nat) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat)
      (EncodedType.list literalStructuredEncodedType)
      (fun p : L.Instance.Carrier × Nat =>
        tmVerifierXOnlyWindowFixedActionReadGuardsFrom p.1 p.2 actions idx) := by
  induction actions generalizing idx with
  | nil =>
      exact TMPolyTimeMap.const (EncodedType.prod L.Instance EncodedType.nat)
        (EncodedType.list literalStructuredEncodedType) []
  | cons act actions ih =>
      have hHead := tmVerifierXOnlyFixedReadGuardAt_pair_tm_polytime V idx act
      have hTail := ih (idx + 1)
      have hAppendInput :
          TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat)
            (EncodedType.prod (EncodedType.list literalStructuredEncodedType)
              (EncodedType.list literalStructuredEncodedType))
            (fun p : L.Instance.Carrier × Nat =>
              (act.xOnlyFixedReadGuardAt p.1 p.2 idx,
                tmVerifierXOnlyWindowFixedActionReadGuardsFrom p.1 p.2 actions
                  (idx + 1))) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hAppend := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append literalStructuredEncodedType) hAppendInput
      simpa [Function.comp, tmVerifierXOnlyWindowFixedActionReadGuardsFrom,
        List.zipIdx_cons, cnfStructuredEncodedType] using hAppend

theorem tmVerifierXOnlyWindowFixedActionReadGuards_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (w : TMVerifierStmtWindow V) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat)
      (EncodedType.list literalStructuredEncodedType)
      (fun p : L.Instance.Carrier × Nat =>
        tmVerifierXOnlyWindowFixedActionReadGuards p.1 p.2 w) := by
  simpa [tmVerifierXOnlyWindowFixedActionReadGuards] using
    tmVerifierXOnlyWindowFixedActionReadGuardsFrom_pair_tm_polytime V w.actions 0

theorem tmVerifierXOnlyWindowFixedAntecedents_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat)
      (EncodedType.list literalStructuredEncodedType)
      (fun p : L.Instance.Carrier × Nat =>
        tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w) := by
  let P := EncodedType.prod L.Instance EncodedType.nat
  have hTime : TMPolyTimeMap P EncodedType.nat (fun p : P.Carrier => p.2) := by
    simpa [P] using TMPolyTimeMap.snd L.Instance EncodedType.nat
  have hLabelAtTime := tmVerifierLabelAtom_time_tm_polytime V (some l)
  have hLabel :
      TMPolyTimeMap P literalStructuredEncodedType
        (fun p : P.Carrier => tmVerifierLabelAtom V p.2 (some l)) := by
    have hComp := TMPolyTimeMap.comp hLabelAtTime hTime
    simpa [Function.comp, P] using hComp
  have hStateAtTime := tmVerifierStateAtom_time_tm_polytime V s
  have hState :
      TMPolyTimeMap P literalStructuredEncodedType
        (fun p : P.Carrier => tmVerifierStateAtom V p.2 s) := by
    have hComp := TMPolyTimeMap.comp hStateAtTime hTime
    simpa [Function.comp, P] using hComp
  have hGuards := tmVerifierXOnlyWindowFixedActionReadGuards_pair_tm_polytime V w
  have hPair :
      TMPolyTimeMap P
        (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
        (fun p : P.Carrier =>
          (tmVerifierLabelAtom V p.2 (some l), tmVerifierStateAtom V p.2 s)) :=
    TMPolyTimeMap.prod_mk hLabel hState
  have hInput :
      TMPolyTimeMap P
        (EncodedType.prod
          (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
          (EncodedType.list literalStructuredEncodedType))
        (fun p : P.Carrier =>
          ((tmVerifierLabelAtom V p.2 (some l), tmVerifierStateAtom V p.2 s),
            tmVerifierXOnlyWindowFixedActionReadGuards p.1 p.2 w)) :=
    TMPolyTimeMap.prod_mk hPair hGuards
  have hAntecedents := TMPolyTimeMap.comp literalPairList_append_tm_polytime hInput
  simpa [Function.comp, tmVerifierXOnlyWindowFixedAntecedents, P] using hAntecedents

theorem tmVerifierXOnlyActionInput_pair_mk_tm_polytime
    {L : EncodedDecisionProblem}
    {tin tout : (EncodedType.prod L.Instance EncodedType.nat).Carrier → Nat}
    {antecedents :
      (EncodedType.prod L.Instance EncodedType.nat).Carrier → List Literal}
    (hTin :
      TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) EncodedType.nat tin)
    (hTout :
      TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) EncodedType.nat tout)
    (hAntecedents :
      TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat)
        (EncodedType.list literalStructuredEncodedType) antecedents) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat)
      (tmVerifierXOnlyActionInputEncodedType L)
      (fun p : (EncodedType.prod L.Instance EncodedType.nat).Carrier =>
        ((p.1, (tin p, tout p)), antecedents p)) := by
  let P := EncodedType.prod L.Instance EncodedType.nat
  have hX : TMPolyTimeMap P L.Instance (fun p : P.Carrier => p.1) := by
    simpa [P] using TMPolyTimeMap.fst L.Instance EncodedType.nat
  have hTimes :
      TMPolyTimeMap P (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : P.Carrier => (tin p, tout p)) :=
    TMPolyTimeMap.prod_mk hTin hTout
  have hLeft :
      TMPolyTimeMap P
        (EncodedType.prod L.Instance (EncodedType.prod EncodedType.nat EncodedType.nat))
        (fun p : P.Carrier => (p.1, (tin p, tout p))) :=
    TMPolyTimeMap.prod_mk hX hTimes
  simpa [P, tmVerifierXOnlyActionInputEncodedType] using
    TMPolyTimeMap.prod_mk hLeft hAntecedents

theorem tmVerifierXOnlyWindowFixedStackBoundaryCNFAt_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V p.1 p.2 l s w) := by
  let P := EncodedType.prod L.Instance EncodedType.nat
  have hT : TMPolyTimeMap P EncodedType.nat (fun p : P.Carrier => p.2) := by
    simpa [P] using TMPolyTimeMap.snd L.Instance EncodedType.nat
  have hAntecedents := tmVerifierXOnlyWindowFixedAntecedents_pair_tm_polytime V l s w
  have hMicroZero := tmVerifierXOnlyFixedMicroTime_pair_tm_polytime V 0
  have hMicroLen := tmVerifierXOnlyFixedMicroTime_pair_tm_polytime V w.actions.length
  have hTsucc : TMPolyTimeMap P EncodedType.nat
      (fun p : P.Carrier => (show Nat from p.2) + 1) := by
    have hComp := TMPolyTimeMap.comp (nat_add_const_tm_polytime 1) hT
    simpa [Function.comp, P] using hComp
  have hLeftInput :
      TMPolyTimeMap P (tmVerifierXOnlyActionInputEncodedType L)
        (fun p : P.Carrier =>
          ((p.1, (p.2, tmVerifierXOnlyFixedMicroTime V p.1 p.2 0)),
            tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w)) :=
    tmVerifierXOnlyActionInput_pair_mk_tm_polytime hT hMicroZero hAntecedents
  have hLeft :
      TMPolyTimeMap P cnfStructuredEncodedType
        (fun p : P.Carrier =>
          tmVerifierXOnlyFrameAllStacksCNFBetween V p.1 p.2
            (tmVerifierXOnlyFixedMicroTime V p.1 p.2 0)
            (tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w)) := by
    have hComp := TMPolyTimeMap.comp
      (tmVerifierXOnlyFrameAllStacksCNFBetween_action_tm_polytime V) hLeftInput
    simpa [Function.comp, P] using hComp
  have hRightInput :
      TMPolyTimeMap P (tmVerifierXOnlyActionInputEncodedType L)
        (fun p : P.Carrier =>
          ((p.1,
              (tmVerifierXOnlyFixedMicroTime V p.1 p.2 w.actions.length,
                (show Nat from p.2) + 1)),
            tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w)) :=
    tmVerifierXOnlyActionInput_pair_mk_tm_polytime hMicroLen hTsucc hAntecedents
  have hRight :
      TMPolyTimeMap P cnfStructuredEncodedType
        (fun p : P.Carrier =>
          tmVerifierXOnlyFrameAllStacksCNFBetween V p.1
            (tmVerifierXOnlyFixedMicroTime V p.1 p.2 w.actions.length)
            ((show Nat from p.2) + 1)
            (tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w)) := by
    have hComp := TMPolyTimeMap.comp
      (tmVerifierXOnlyFrameAllStacksCNFBetween_action_tm_polytime V) hRightInput
    simpa [Function.comp, P] using hComp
  have hAppendInput :
      TMPolyTimeMap P
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun p : P.Carrier =>
          (tmVerifierXOnlyFrameAllStacksCNFBetween V p.1 p.2
              (tmVerifierXOnlyFixedMicroTime V p.1 p.2 0)
              (tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w),
            tmVerifierXOnlyFrameAllStacksCNFBetween V p.1
              (tmVerifierXOnlyFixedMicroTime V p.1 p.2 w.actions.length)
              ((show Nat from p.2) + 1)
              (tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w))) :=
    TMPolyTimeMap.prod_mk hLeft hRight
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
  simpa [Function.comp, tmVerifierXOnlyWindowFixedStackBoundaryCNFAt,
    cnfStructuredEncodedType, P] using hAppend

theorem tmVerifierXOnlyWindowFixedStackActionCNFForEntries_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (entries : List (TMVerifierStackAction V × Nat)) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        entries.flatMap fun entry =>
          tmVerifierXOnlyStackActionCNFBetween V B p.1
            (tmVerifierXOnlyFixedMicroTime V p.1 p.2 entry.2)
            (tmVerifierXOnlyFixedMicroTime V p.1 p.2 (entry.2 + 1))
            (tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w) entry.1) := by
  induction entries with
  | nil =>
      exact TMPolyTimeMap.const (EncodedType.prod L.Instance EncodedType.nat)
        cnfStructuredEncodedType []
  | cons entry entries ih =>
      let P := EncodedType.prod L.Instance EncodedType.nat
      have hAntecedents := tmVerifierXOnlyWindowFixedAntecedents_pair_tm_polytime V l s w
      have hTin := tmVerifierXOnlyFixedMicroTime_pair_tm_polytime V entry.2
      have hTout := tmVerifierXOnlyFixedMicroTime_pair_tm_polytime V (entry.2 + 1)
      have hInput :
          TMPolyTimeMap P (tmVerifierXOnlyActionInputEncodedType L)
            (fun p : P.Carrier =>
              ((p.1,
                  (tmVerifierXOnlyFixedMicroTime V p.1 p.2 entry.2,
                    tmVerifierXOnlyFixedMicroTime V p.1 p.2 (entry.2 + 1))),
                tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w)) :=
        tmVerifierXOnlyActionInput_pair_mk_tm_polytime hTin hTout hAntecedents
      have hHead :
          TMPolyTimeMap P cnfStructuredEncodedType
            (fun p : P.Carrier =>
              tmVerifierXOnlyStackActionCNFBetween V B p.1
                (tmVerifierXOnlyFixedMicroTime V p.1 p.2 entry.2)
                (tmVerifierXOnlyFixedMicroTime V p.1 p.2 (entry.2 + 1))
                (tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w) entry.1) := by
        have hComp := TMPolyTimeMap.comp
          (tmVerifierXOnlyStackActionCNFBetween_action_tm_polytime V B entry.1) hInput
        simpa [Function.comp, P] using hComp
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap P
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun p : P.Carrier =>
              (tmVerifierXOnlyStackActionCNFBetween V B p.1
                  (tmVerifierXOnlyFixedMicroTime V p.1 p.2 entry.2)
                  (tmVerifierXOnlyFixedMicroTime V p.1 p.2 (entry.2 + 1))
                  (tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w) entry.1,
                entries.flatMap fun entry =>
                  tmVerifierXOnlyStackActionCNFBetween V B p.1
                    (tmVerifierXOnlyFixedMicroTime V p.1 p.2 entry.2)
                    (tmVerifierXOnlyFixedMicroTime V p.1 p.2 (entry.2 + 1))
                    (tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w)
                    entry.1)) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hAppend := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
      simpa [Function.comp, cnfStructuredEncodedType, P] using hAppend

theorem tmVerifierXOnlyWindowFixedStackActionCNFAt_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        tmVerifierXOnlyWindowFixedStackActionCNFAt V B p.1 p.2 w
          (tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w)) := by
  simpa [tmVerifierXOnlyWindowFixedStackActionCNFAt] using
    tmVerifierXOnlyWindowFixedStackActionCNFForEntries_pair_tm_polytime V B l s w
      w.actions.zipIdx

theorem tmVerifierXOnlyWindowFixedControlCNFAt_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        tmVerifierXOnlyWindowFixedControlCNFAt V p.1 p.2 l s w) := by
  let P := EncodedType.prod L.Instance EncodedType.nat
  have hT : TMPolyTimeMap P EncodedType.nat (fun p : P.Carrier => p.2) := by
    simpa [P] using TMPolyTimeMap.snd L.Instance EncodedType.nat
  have hTsucc : TMPolyTimeMap P EncodedType.nat
      (fun p : P.Carrier => (show Nat from p.2) + 1) := by
    have hComp := TMPolyTimeMap.comp (nat_add_const_tm_polytime 1) hT
    simpa [Function.comp, P] using hComp
  have hAntecedents := tmVerifierXOnlyWindowFixedAntecedents_pair_tm_polytime V l s w
  have hLabelAtTime := tmVerifierLabelAtom_time_tm_polytime V w.nextLabel
  have hLabel :
      TMPolyTimeMap P literalStructuredEncodedType
        (fun p : P.Carrier => tmVerifierLabelAtom V ((show Nat from p.2) + 1) w.nextLabel) := by
    have hComp := TMPolyTimeMap.comp hLabelAtTime hTsucc
    simpa [Function.comp, P] using hComp
  have hStateAtTime := tmVerifierStateAtom_time_tm_polytime V w.nextState
  have hState :
      TMPolyTimeMap P literalStructuredEncodedType
        (fun p : P.Carrier => tmVerifierStateAtom V ((show Nat from p.2) + 1) w.nextState) := by
    have hComp := TMPolyTimeMap.comp hStateAtTime hTsucc
    simpa [Function.comp, P] using hComp
  have hLabelClause := tmVerifierImplicationClause_of_tm_polytime hAntecedents hLabel
  have hStateClause := tmVerifierImplicationClause_of_tm_polytime hAntecedents hState
  have hPair :
      TMPolyTimeMap P
        (EncodedType.prod clauseStructuredEncodedType clauseStructuredEncodedType)
        (fun p : P.Carrier =>
          (tmVerifierImplicationClause
              (tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w)
              (tmVerifierLabelAtom V ((show Nat from p.2) + 1) w.nextLabel),
            tmVerifierImplicationClause
              (tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w)
              (tmVerifierStateAtom V ((show Nat from p.2) + 1) w.nextState))) :=
    TMPolyTimeMap.prod_mk hLabelClause hStateClause
  have hCNF := TMPolyTimeMap.comp clausePairCNF_tm_polytime hPair
  simpa [Function.comp, tmVerifierXOnlyWindowFixedControlCNFAt, P] using hCNF

theorem tmVerifierXOnlyTransitionFixedWindowStackForList_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (windows : List (TMVerifierStmtWindow V)) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        windows.flatMap fun w =>
          tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V p.1 p.2 l s w ++
            tmVerifierXOnlyWindowFixedStackActionCNFAt V B p.1 p.2 w
              (tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w)) := by
  induction windows with
  | nil =>
      exact TMPolyTimeMap.const (EncodedType.prod L.Instance EncodedType.nat)
        cnfStructuredEncodedType []
  | cons w windows ih =>
      let P := EncodedType.prod L.Instance EncodedType.nat
      have hBoundary := tmVerifierXOnlyWindowFixedStackBoundaryCNFAt_pair_tm_polytime V l s w
      have hAction := tmVerifierXOnlyWindowFixedStackActionCNFAt_pair_tm_polytime V B l s w
      have hHeadInput :
          TMPolyTimeMap P
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun p : P.Carrier =>
              (tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V p.1 p.2 l s w,
                tmVerifierXOnlyWindowFixedStackActionCNFAt V B p.1 p.2 w
                  (tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w))) :=
        TMPolyTimeMap.prod_mk hBoundary hAction
      have hHead :
          TMPolyTimeMap P cnfStructuredEncodedType
            (fun p : P.Carrier =>
              tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V p.1 p.2 l s w ++
                tmVerifierXOnlyWindowFixedStackActionCNFAt V B p.1 p.2 w
                  (tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w)) := by
        have hComp := TMPolyTimeMap.comp
          (TMPolyTimeMap.list_append clauseStructuredEncodedType) hHeadInput
        simpa [Function.comp, cnfStructuredEncodedType, P] using hComp
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap P
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun p : P.Carrier =>
              (tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V p.1 p.2 l s w ++
                  tmVerifierXOnlyWindowFixedStackActionCNFAt V B p.1 p.2 w
                    (tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w),
                windows.flatMap fun w =>
                  tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V p.1 p.2 l s w ++
                    tmVerifierXOnlyWindowFixedStackActionCNFAt V B p.1 p.2 w
                      (tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w))) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hAppend := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
      simpa [Function.comp, cnfStructuredEncodedType, P] using hAppend

theorem tmVerifierXOnlyTransitionFixedWindowStackForStates_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (l : (tmVerifierTM V).Λ) (states : List (tmVerifierTM V).σ) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        states.flatMap fun s =>
          (tmVerifierStmtWindowsAt V p.2 ((tmVerifierTM V).m l) s).flatMap fun w =>
            tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V p.1 p.2 l s w ++
              tmVerifierXOnlyWindowFixedStackActionCNFAt V B p.1 p.2 w
                (tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w)) := by
  induction states with
  | nil =>
      exact TMPolyTimeMap.const (EncodedType.prod L.Instance EncodedType.nat)
        cnfStructuredEncodedType []
  | cons s states ih =>
      let P := EncodedType.prod L.Instance EncodedType.nat
      have hHeadZero :=
        tmVerifierXOnlyTransitionFixedWindowStackForList_pair_tm_polytime V B l s
          (tmVerifierStmtWindowsAt V 0 ((tmVerifierTM V).m l) s)
      have hHead :
          TMPolyTimeMap P cnfStructuredEncodedType
            (fun p : P.Carrier =>
              (tmVerifierStmtWindowsAt V p.2 ((tmVerifierTM V).m l) s).flatMap fun w =>
                tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V p.1 p.2 l s w ++
                  tmVerifierXOnlyWindowFixedStackActionCNFAt V B p.1 p.2 w
                    (tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w)) := by
        convert hHeadZero using 1
        funext p
        exact tmVerifierStmtWindowsAt_flatMap_surface_eq_zero V
          (fun actions nextLabel nextState =>
            let w : TMVerifierStmtWindow V :=
              { guards := [], actions := actions, nextLabel := nextLabel,
                nextState := nextState }
            tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V p.1 p.2 l s w ++
              tmVerifierXOnlyWindowFixedStackActionCNFAt V B p.1 p.2 w
                (tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w))
          ((tmVerifierTM V).m l) s p.2
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap P
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun p : P.Carrier =>
              ((tmVerifierStmtWindowsAt V p.2 ((tmVerifierTM V).m l) s).flatMap fun w =>
                tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V p.1 p.2 l s w ++
                  tmVerifierXOnlyWindowFixedStackActionCNFAt V B p.1 p.2 w
                    (tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w),
                states.flatMap fun s =>
                  (tmVerifierStmtWindowsAt V p.2 ((tmVerifierTM V).m l) s).flatMap fun w =>
                    tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V p.1 p.2 l s w ++
                      tmVerifierXOnlyWindowFixedStackActionCNFAt V B p.1 p.2 w
                        (tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w))) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hAppend := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
      simpa [Function.comp, cnfStructuredEncodedType, P] using hAppend

theorem tmVerifierXOnlyTransitionFixedWindowStackForLabels_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (labels : List (tmVerifierTM V).Λ) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        labels.flatMap fun l =>
          (tmVerifierStateList V).flatMap fun s =>
            (tmVerifierStmtWindowsAt V p.2 ((tmVerifierTM V).m l) s).flatMap fun w =>
              tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V p.1 p.2 l s w ++
                tmVerifierXOnlyWindowFixedStackActionCNFAt V B p.1 p.2 w
                  (tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w)) := by
  induction labels with
  | nil =>
      exact TMPolyTimeMap.const (EncodedType.prod L.Instance EncodedType.nat)
        cnfStructuredEncodedType []
  | cons l labels ih =>
      let P := EncodedType.prod L.Instance EncodedType.nat
      have hHead :=
        tmVerifierXOnlyTransitionFixedWindowStackForStates_pair_tm_polytime V B l
          (tmVerifierStateList V)
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap P
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun p : P.Carrier =>
              ((tmVerifierStateList V).flatMap fun s =>
                (tmVerifierStmtWindowsAt V p.2 ((tmVerifierTM V).m l) s).flatMap fun w =>
                  tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V p.1 p.2 l s w ++
                    tmVerifierXOnlyWindowFixedStackActionCNFAt V B p.1 p.2 w
                      (tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w),
                labels.flatMap fun l =>
                  (tmVerifierStateList V).flatMap fun s =>
                    (tmVerifierStmtWindowsAt V p.2 ((tmVerifierTM V).m l) s).flatMap fun w =>
                      tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V p.1 p.2 l s w ++
                        tmVerifierXOnlyWindowFixedStackActionCNFAt V B p.1 p.2 w
                          (tmVerifierXOnlyWindowFixedAntecedents V p.1 p.2 l s w))) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hAppend := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
      simpa [Function.comp, cnfStructuredEncodedType, P] using hAppend

theorem tmVerifierXOnlyTransitionFixedWindowStackCNFAt_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        tmVerifierXOnlyTransitionFixedWindowStackCNFAt V B p.1 p.2) := by
  simpa [tmVerifierXOnlyTransitionFixedWindowStackCNFAt] using
    tmVerifierXOnlyTransitionFixedWindowStackForLabels_pair_tm_polytime V B
      (tmVerifierLabelList V)

theorem tmVerifierXOnlyTransitionFixedControlForList_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (windows : List (TMVerifierStmtWindow V)) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        windows.flatMap fun w => tmVerifierXOnlyWindowFixedControlCNFAt V p.1 p.2 l s w) := by
  induction windows with
  | nil =>
      exact TMPolyTimeMap.const (EncodedType.prod L.Instance EncodedType.nat)
        cnfStructuredEncodedType []
  | cons w windows ih =>
      let P := EncodedType.prod L.Instance EncodedType.nat
      have hHead := tmVerifierXOnlyWindowFixedControlCNFAt_pair_tm_polytime V l s w
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap P
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun p : P.Carrier =>
              (tmVerifierXOnlyWindowFixedControlCNFAt V p.1 p.2 l s w,
                windows.flatMap fun w =>
                  tmVerifierXOnlyWindowFixedControlCNFAt V p.1 p.2 l s w)) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hAppend := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
      simpa [Function.comp, cnfStructuredEncodedType, P] using hAppend

theorem tmVerifierXOnlyTransitionFixedControlForStates_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (l : (tmVerifierTM V).Λ) (states : List (tmVerifierTM V).σ) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        states.flatMap fun s =>
          (tmVerifierStmtWindowsAt V p.2 ((tmVerifierTM V).m l) s).flatMap fun w =>
            tmVerifierXOnlyWindowFixedControlCNFAt V p.1 p.2 l s w) := by
  induction states with
  | nil =>
      exact TMPolyTimeMap.const (EncodedType.prod L.Instance EncodedType.nat)
        cnfStructuredEncodedType []
  | cons s states ih =>
      let P := EncodedType.prod L.Instance EncodedType.nat
      have hHeadZero :=
        tmVerifierXOnlyTransitionFixedControlForList_pair_tm_polytime V l s
          (tmVerifierStmtWindowsAt V 0 ((tmVerifierTM V).m l) s)
      have hHead :
          TMPolyTimeMap P cnfStructuredEncodedType
            (fun p : P.Carrier =>
              (tmVerifierStmtWindowsAt V p.2 ((tmVerifierTM V).m l) s).flatMap fun w =>
                tmVerifierXOnlyWindowFixedControlCNFAt V p.1 p.2 l s w) := by
        convert hHeadZero using 1
        funext p
        exact tmVerifierStmtWindowsAt_flatMap_surface_eq_zero V
          (fun actions nextLabel nextState =>
            let w : TMVerifierStmtWindow V :=
              { guards := [], actions := actions, nextLabel := nextLabel,
                nextState := nextState }
            tmVerifierXOnlyWindowFixedControlCNFAt V p.1 p.2 l s w)
          ((tmVerifierTM V).m l) s p.2
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap P
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun p : P.Carrier =>
              ((tmVerifierStmtWindowsAt V p.2 ((tmVerifierTM V).m l) s).flatMap fun w =>
                tmVerifierXOnlyWindowFixedControlCNFAt V p.1 p.2 l s w,
                states.flatMap fun s =>
                  (tmVerifierStmtWindowsAt V p.2 ((tmVerifierTM V).m l) s).flatMap fun w =>
                    tmVerifierXOnlyWindowFixedControlCNFAt V p.1 p.2 l s w)) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hAppend := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
      simpa [Function.comp, cnfStructuredEncodedType, P] using hAppend

theorem tmVerifierXOnlyTransitionFixedControlForLabels_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (labels : List (tmVerifierTM V).Λ) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        labels.flatMap fun l =>
          (tmVerifierStateList V).flatMap fun s =>
            (tmVerifierStmtWindowsAt V p.2 ((tmVerifierTM V).m l) s).flatMap fun w =>
              tmVerifierXOnlyWindowFixedControlCNFAt V p.1 p.2 l s w) := by
  induction labels with
  | nil =>
      exact TMPolyTimeMap.const (EncodedType.prod L.Instance EncodedType.nat)
        cnfStructuredEncodedType []
  | cons l labels ih =>
      let P := EncodedType.prod L.Instance EncodedType.nat
      have hHead :=
        tmVerifierXOnlyTransitionFixedControlForStates_pair_tm_polytime V l
          (tmVerifierStateList V)
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap P
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun p : P.Carrier =>
              ((tmVerifierStateList V).flatMap fun s =>
                (tmVerifierStmtWindowsAt V p.2 ((tmVerifierTM V).m l) s).flatMap fun w =>
                  tmVerifierXOnlyWindowFixedControlCNFAt V p.1 p.2 l s w,
                labels.flatMap fun l =>
                  (tmVerifierStateList V).flatMap fun s =>
                    (tmVerifierStmtWindowsAt V p.2 ((tmVerifierTM V).m l) s).flatMap fun w =>
                      tmVerifierXOnlyWindowFixedControlCNFAt V p.1 p.2 l s w)) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hAppend := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
      simpa [Function.comp, cnfStructuredEncodedType, P] using hAppend

theorem tmVerifierXOnlyTransitionFixedControlCNFAt_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        tmVerifierXOnlyTransitionFixedControlCNFAt V p.1 p.2) := by
  simpa [tmVerifierXOnlyTransitionFixedControlCNFAt] using
    tmVerifierXOnlyTransitionFixedControlForLabels_pair_tm_polytime V
      (tmVerifierLabelList V)

theorem tmVerifierHaltedRowAntecedents_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (s : (tmVerifierTM V).σ) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat)
      (EncodedType.list literalStructuredEncodedType)
      (fun p : L.Instance.Carrier × Nat => tmVerifierHaltedRowAntecedents V p.2 s) := by
  let P := EncodedType.prod L.Instance EncodedType.nat
  have hT : TMPolyTimeMap P EncodedType.nat (fun p : P.Carrier => p.2) := by
    simpa [P] using TMPolyTimeMap.snd L.Instance EncodedType.nat
  have hLabelAtTime := tmVerifierLabelAtom_time_tm_polytime V none
  have hLabel :
      TMPolyTimeMap P literalStructuredEncodedType
        (fun p : P.Carrier => tmVerifierLabelAtom V p.2 none) := by
    have hComp := TMPolyTimeMap.comp hLabelAtTime hT
    simpa [Function.comp, P] using hComp
  have hStateAtTime := tmVerifierStateAtom_time_tm_polytime V s
  have hState :
      TMPolyTimeMap P literalStructuredEncodedType
        (fun p : P.Carrier => tmVerifierStateAtom V p.2 s) := by
    have hComp := TMPolyTimeMap.comp hStateAtTime hT
    simpa [Function.comp, P] using hComp
  have hPair :
      TMPolyTimeMap P
        (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
        (fun p : P.Carrier => (tmVerifierLabelAtom V p.2 none, tmVerifierStateAtom V p.2 s)) :=
    TMPolyTimeMap.prod_mk hLabel hState
  have hList := TMPolyTimeMap.comp literalPairList_tm_polytime hPair
  simpa [Function.comp, tmVerifierHaltedRowAntecedents, P] using hList

theorem tmVerifierXOnlyHaltedRowCNFAt_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (s : (tmVerifierTM V).σ) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat => tmVerifierXOnlyHaltedRowCNFAt V p.1 p.2 s) := by
  let P := EncodedType.prod L.Instance EncodedType.nat
  have hT : TMPolyTimeMap P EncodedType.nat (fun p : P.Carrier => p.2) := by
    simpa [P] using TMPolyTimeMap.snd L.Instance EncodedType.nat
  have hTsucc : TMPolyTimeMap P EncodedType.nat
      (fun p : P.Carrier => (show Nat from p.2) + 1) := by
    have hComp := TMPolyTimeMap.comp (nat_add_const_tm_polytime 1) hT
    simpa [Function.comp, P] using hComp
  have hAntecedents := tmVerifierHaltedRowAntecedents_pair_tm_polytime V s
  have hLabelAtTime := tmVerifierLabelAtom_time_tm_polytime V none
  have hLabelNext :
      TMPolyTimeMap P literalStructuredEncodedType
        (fun p : P.Carrier => tmVerifierLabelAtom V ((show Nat from p.2) + 1) none) := by
    have hComp := TMPolyTimeMap.comp hLabelAtTime hTsucc
    simpa [Function.comp, P] using hComp
  have hStateAtTime := tmVerifierStateAtom_time_tm_polytime V s
  have hStateNext :
      TMPolyTimeMap P literalStructuredEncodedType
        (fun p : P.Carrier => tmVerifierStateAtom V ((show Nat from p.2) + 1) s) := by
    have hComp := TMPolyTimeMap.comp hStateAtTime hTsucc
    simpa [Function.comp, P] using hComp
  have hLabelClause := tmVerifierImplicationClause_of_tm_polytime hAntecedents hLabelNext
  have hStateClause := tmVerifierImplicationClause_of_tm_polytime hAntecedents hStateNext
  have hPairClausesInput :
      TMPolyTimeMap P
        (EncodedType.prod clauseStructuredEncodedType clauseStructuredEncodedType)
        (fun p : P.Carrier =>
          (tmVerifierImplicationClause (tmVerifierHaltedRowAntecedents V p.2 s)
              (tmVerifierLabelAtom V ((show Nat from p.2) + 1) none),
            tmVerifierImplicationClause (tmVerifierHaltedRowAntecedents V p.2 s)
              (tmVerifierStateAtom V ((show Nat from p.2) + 1) s))) :=
    TMPolyTimeMap.prod_mk hLabelClause hStateClause
  have hPairClauses :
      TMPolyTimeMap P cnfStructuredEncodedType
        (fun p : P.Carrier =>
          [tmVerifierImplicationClause (tmVerifierHaltedRowAntecedents V p.2 s)
              (tmVerifierLabelAtom V ((show Nat from p.2) + 1) none),
            tmVerifierImplicationClause (tmVerifierHaltedRowAntecedents V p.2 s)
              (tmVerifierStateAtom V ((show Nat from p.2) + 1) s)]) := by
    have hComp := TMPolyTimeMap.comp clausePairCNF_tm_polytime hPairClausesInput
    simpa [Function.comp, P] using hComp
  have hActionInput :
      TMPolyTimeMap P (tmVerifierXOnlyActionInputEncodedType L)
        (fun p : P.Carrier =>
          ((p.1, (p.2, (show Nat from p.2) + 1)),
            tmVerifierHaltedRowAntecedents V p.2 s)) :=
    tmVerifierXOnlyActionInput_pair_mk_tm_polytime hT hTsucc hAntecedents
  have hFrame :
      TMPolyTimeMap P cnfStructuredEncodedType
        (fun p : P.Carrier =>
          tmVerifierXOnlyFrameAllStacksCNFBetween V p.1 p.2
            ((show Nat from p.2) + 1) (tmVerifierHaltedRowAntecedents V p.2 s)) := by
    have hComp := TMPolyTimeMap.comp
      (tmVerifierXOnlyFrameAllStacksCNFBetween_action_tm_polytime V) hActionInput
    simpa [Function.comp, P] using hComp
  have hAppendInput :
      TMPolyTimeMap P
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun p : P.Carrier =>
          ([tmVerifierImplicationClause (tmVerifierHaltedRowAntecedents V p.2 s)
              (tmVerifierLabelAtom V ((show Nat from p.2) + 1) none),
            tmVerifierImplicationClause (tmVerifierHaltedRowAntecedents V p.2 s)
              (tmVerifierStateAtom V ((show Nat from p.2) + 1) s)],
            tmVerifierXOnlyFrameAllStacksCNFBetween V p.1 p.2
              ((show Nat from p.2) + 1) (tmVerifierHaltedRowAntecedents V p.2 s))) :=
    TMPolyTimeMap.prod_mk hPairClauses hFrame
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
  simpa [Function.comp, tmVerifierXOnlyHaltedRowCNFAt, cnfStructuredEncodedType, P]
    using hAppend

theorem tmVerifierXOnlyHaltedRowsForStates_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (states : List (tmVerifierTM V).σ) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        states.flatMap fun s => tmVerifierXOnlyHaltedRowCNFAt V p.1 p.2 s) := by
  induction states with
  | nil =>
      exact TMPolyTimeMap.const (EncodedType.prod L.Instance EncodedType.nat)
        cnfStructuredEncodedType []
  | cons s states ih =>
      let P := EncodedType.prod L.Instance EncodedType.nat
      have hHead := tmVerifierXOnlyHaltedRowCNFAt_pair_tm_polytime V s
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap P
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun p : P.Carrier =>
              (tmVerifierXOnlyHaltedRowCNFAt V p.1 p.2 s,
                states.flatMap fun s => tmVerifierXOnlyHaltedRowCNFAt V p.1 p.2 s)) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hAppend := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
      simpa [Function.comp, cnfStructuredEncodedType, P] using hAppend

theorem tmVerifierXOnlyHaltedRowsCNFAt_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        tmVerifierXOnlyHaltedRowsCNFAt V p.1 p.2) := by
  simpa [tmVerifierXOnlyHaltedRowsCNFAt] using
    tmVerifierXOnlyHaltedRowsForStates_pair_tm_polytime V (tmVerifierStateList V)

theorem tmVerifierXOnlyTransitionFixedRowCNFAt_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        tmVerifierXOnlyTransitionFixedRowCNFAt V B p.1 p.2) := by
  let P := EncodedType.prod L.Instance EncodedType.nat
  have hControl := tmVerifierXOnlyTransitionFixedControlCNFAt_pair_tm_polytime V
  have hStack := tmVerifierXOnlyTransitionFixedWindowStackCNFAt_pair_tm_polytime V B
  have hHalted := tmVerifierXOnlyHaltedRowsCNFAt_pair_tm_polytime V
  have hStackHaltedInput :
      TMPolyTimeMap P
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun p : P.Carrier =>
          (tmVerifierXOnlyTransitionFixedWindowStackCNFAt V B p.1 p.2,
            tmVerifierXOnlyHaltedRowsCNFAt V p.1 p.2)) :=
    TMPolyTimeMap.prod_mk hStack hHalted
  have hStackHalted :
      TMPolyTimeMap P cnfStructuredEncodedType
        (fun p : P.Carrier =>
          tmVerifierXOnlyTransitionFixedWindowStackCNFAt V B p.1 p.2 ++
            tmVerifierXOnlyHaltedRowsCNFAt V p.1 p.2) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append clauseStructuredEncodedType) hStackHaltedInput
    simpa [Function.comp, cnfStructuredEncodedType, P] using hComp
  have hAllInput :
      TMPolyTimeMap P
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun p : P.Carrier =>
          (tmVerifierXOnlyTransitionFixedControlCNFAt V p.1 p.2,
            tmVerifierXOnlyTransitionFixedWindowStackCNFAt V B p.1 p.2 ++
              tmVerifierXOnlyHaltedRowsCNFAt V p.1 p.2)) :=
    TMPolyTimeMap.prod_mk hControl hStackHalted
  have hAll := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
    hAllInput
  simpa [Function.comp, tmVerifierXOnlyTransitionFixedRowCNFAt, cnfStructuredEncodedType, P]
    using hAll

theorem tmVerifierXOnlyTransitionFixedRowsCNF_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier => tmVerifierXOnlyTransitionFixedRowsCNF V B x) := by
  have hTimes := tmVerifierXOnlyTransitionTimeRange_tm_polytime V
  have hInput :
      TMPolyTimeMap L.Instance
        (EncodedType.prod L.Instance (EncodedType.list EncodedType.nat))
        (fun x : L.Instance.Carrier => (x, tmVerifierXOnlyTransitionTimeRange V x)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id L.Instance) hTimes
  have hFold := cnfContextFlatMap_tm_polytime
    (C := L.Instance) (X := EncodedType.nat)
    (fun x t => tmVerifierXOnlyTransitionFixedRowCNFAt V B x t)
    (tmVerifierXOnlyTransitionFixedRowCNFAt_pair_tm_polytime V B)
  have hComp := TMPolyTimeMap.comp hFold hInput
  simpa [Function.comp, tmVerifierXOnlyTransitionFixedRowsCNF] using hComp

end SAT
end ComplexityReduction
