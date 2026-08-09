import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyInputPrefixFoldTM

/-!
Direct standard-TM witnesses for the x-only global base CNF.

The transition fixed-micro-domain block enumerates statement windows whose guard
literals mention the macro time `t`.  The block proved here only emits stack
well-formed rows for the windows' action micro-times, so the generated CNF
depends on `t` through the explicit x-only micro-time coordinate and not through
the guard literals stored in the windows.
-/

namespace ComplexityReduction
namespace SAT

theorem list_append_six_flatMap_blocks
    {α : Type} (a b c d e f : List α) :
    (a :: b :: c :: d :: e :: f :: []).flatMap id =
      (((((a ++ b) ++ c) ++ d) ++ e) ++ f) := by
  simp [List.append_assoc]

theorem tmVerifierStmtWindowsAt_flatMap_actions_eq_zero
    {L : EncodedDecisionProblem} (V : TMVerifier L) {α : Type}
    (G : List (TMVerifierStackAction V) → List α)
    (stmt : (tmVerifierTM V).Stmt) (s : (tmVerifierTM V).σ) (t : Nat) :
    (tmVerifierStmtWindowsAt V t stmt s).flatMap (fun w => G w.actions) =
      (tmVerifierStmtWindowsAt V 0 stmt s).flatMap (fun w => G w.actions) := by
  induction stmt generalizing s G with
  | push k f q ih =>
      simpa [tmVerifierStmtWindowsAt, TMVerifierStmtWindow.consAction, List.flatMap_map]
        using ih (fun actions =>
          G (TMVerifierStackAction.push (V := V) { stack := k, symbol := f s } :: actions)) s
  | peek k f q ih =>
      let choices := tmVerifierStackReadChoices V k
      change
        List.flatMap (fun w => G w.actions)
            (choices.flatMap fun choice =>
              (tmVerifierStmtWindowsAt V t q (f s choice.toOption)).map fun w =>
                TMVerifierStmtWindow.consAction (TMVerifierStackAction.peek (V := V) k choice)
                  (TMVerifierStmtWindow.consGuard
                    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice) w)) =
          List.flatMap (fun w => G w.actions)
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
          rw [ih (fun actions => G (TMVerifierStackAction.peek (V := V) k choice :: actions))
            (f s choice.toOption)]
          simpa [ihChoices]
  | pop k f q ih =>
      let choices := tmVerifierStackReadChoices V k
      change
        List.flatMap (fun w => G w.actions)
            (choices.flatMap fun choice =>
              (tmVerifierStmtWindowsAt V t q (f s choice.toOption)).map fun w =>
                TMVerifierStmtWindow.consAction (TMVerifierStackAction.pop (V := V) k choice)
                  (TMVerifierStmtWindow.consGuard
                    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice) w)) =
          List.flatMap (fun w => G w.actions)
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
          rw [ih (fun actions => G (TMVerifierStackAction.pop (V := V) k choice :: actions))
            (f s choice.toOption)]
          simpa [ihChoices]
  | load f q ih =>
      simpa [tmVerifierStmtWindowsAt, TMVerifierStmtWindow.consAction, List.flatMap_map]
        using ih (fun actions => G (TMVerifierStackAction.load (V := V) :: actions)) (f s)
  | branch f q₁ q₂ ih₁ ih₂ =>
      by_cases h : f s
      · simpa [tmVerifierStmtWindowsAt, h, TMVerifierStmtWindow.consAction, List.flatMap_map]
          using ih₁
            (fun actions =>
              G (TMVerifierStackAction.branch (V := V) TMVerifierStmtTag.branchTrue :: actions))
            s
      · simpa [tmVerifierStmtWindowsAt, h, TMVerifierStmtWindow.consAction, List.flatMap_map]
          using ih₂
            (fun actions =>
              G (TMVerifierStackAction.branch (V := V) TMVerifierStmtTag.branchFalse :: actions))
            s
  | goto f =>
      simp [tmVerifierStmtWindowsAt]
  | halt =>
      simp [tmVerifierStmtWindowsAt]

theorem tmVerifierStmtWindowsAt_flatMap_fixedMicro_eq_zero
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat)
    (stmt : (tmVerifierTM V).Stmt) (s : (tmVerifierTM V).σ) :
    (tmVerifierStmtWindowsAt V t stmt s).flatMap
        (fun w => tmVerifierXOnlyWindowFixedMicroDomainCNFAt V x t w) =
      (tmVerifierStmtWindowsAt V 0 stmt s).flatMap
        (fun w => tmVerifierXOnlyWindowFixedMicroDomainCNFAt V x t w) := by
  let G : List (TMVerifierStackAction V) → CNF :=
    fun actions =>
      (0 :: actions.length ::
          (actions.zipIdx.flatMap fun entry => [entry.2, entry.2 + 1])).flatMap
        fun micro =>
          (tmVerifierStackList V).flatMap fun k =>
            tmVerifierXOnlyStackWellFormedCNFAt V x
              (tmVerifierXOnlyFixedMicroTime V x t micro) k
  have h := tmVerifierStmtWindowsAt_flatMap_actions_eq_zero V G stmt s t
  simpa [G, tmVerifierXOnlyWindowFixedMicroDomainCNFAt,
    tmVerifierWindowMicroTimeRange, tmVerifierWindowActionMicroTimeRange] using h

theorem tmVerifierXOnlyWindowFixedMicroDomainForList_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (windows : List (TMVerifierStmtWindow V)) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        windows.flatMap fun w => tmVerifierXOnlyWindowFixedMicroDomainCNFAt V p.1 p.2 w) := by
  induction windows with
  | nil =>
      exact TMPolyTimeMap.const (EncodedType.prod L.Instance EncodedType.nat)
        cnfStructuredEncodedType []
  | cons w windows ih =>
      have hHead := tmVerifierXOnlyWindowFixedMicroDomainCNFAt_pair_tm_polytime V w
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat)
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun p : L.Instance.Carrier × Nat =>
              (tmVerifierXOnlyWindowFixedMicroDomainCNFAt V p.1 p.2 w,
                windows.flatMap fun w =>
                  tmVerifierXOnlyWindowFixedMicroDomainCNFAt V p.1 p.2 w)) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hAppend := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
      simpa [Function.comp, cnfStructuredEncodedType] using hAppend

theorem tmVerifierXOnlyTransitionFixedMicroDomainForStates_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (l : (tmVerifierTM V).Λ) (states : List (tmVerifierTM V).σ) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        states.flatMap fun s =>
          (tmVerifierStmtWindowsAt V p.2 ((tmVerifierTM V).m l) s).flatMap fun w =>
            tmVerifierXOnlyWindowFixedMicroDomainCNFAt V p.1 p.2 w) := by
  induction states with
  | nil =>
      exact TMPolyTimeMap.const (EncodedType.prod L.Instance EncodedType.nat)
        cnfStructuredEncodedType []
  | cons s states ih =>
      have hHeadZero :=
        tmVerifierXOnlyWindowFixedMicroDomainForList_pair_tm_polytime V
          (tmVerifierStmtWindowsAt V 0 ((tmVerifierTM V).m l) s)
      have hHead :
          TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat)
            cnfStructuredEncodedType
            (fun p : L.Instance.Carrier × Nat =>
              (tmVerifierStmtWindowsAt V p.2 ((tmVerifierTM V).m l) s).flatMap fun w =>
                tmVerifierXOnlyWindowFixedMicroDomainCNFAt V p.1 p.2 w) := by
        convert hHeadZero using 1
        funext p
        exact tmVerifierStmtWindowsAt_flatMap_fixedMicro_eq_zero V p.1 p.2
          ((tmVerifierTM V).m l) s
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat)
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun p : L.Instance.Carrier × Nat =>
              ((tmVerifierStmtWindowsAt V p.2 ((tmVerifierTM V).m l) s).flatMap fun w =>
                tmVerifierXOnlyWindowFixedMicroDomainCNFAt V p.1 p.2 w,
                states.flatMap fun s =>
                  (tmVerifierStmtWindowsAt V p.2 ((tmVerifierTM V).m l) s).flatMap fun w =>
                    tmVerifierXOnlyWindowFixedMicroDomainCNFAt V p.1 p.2 w)) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hAppend := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
      simpa [Function.comp, cnfStructuredEncodedType] using hAppend

theorem tmVerifierXOnlyTransitionFixedMicroDomainForLabels_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (labels : List (tmVerifierTM V).Λ) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        labels.flatMap fun l =>
          (tmVerifierStateList V).flatMap fun s =>
            (tmVerifierStmtWindowsAt V p.2 ((tmVerifierTM V).m l) s).flatMap fun w =>
              tmVerifierXOnlyWindowFixedMicroDomainCNFAt V p.1 p.2 w) := by
  induction labels with
  | nil =>
      exact TMPolyTimeMap.const (EncodedType.prod L.Instance EncodedType.nat)
        cnfStructuredEncodedType []
  | cons l labels ih =>
      have hHead :=
        tmVerifierXOnlyTransitionFixedMicroDomainForStates_pair_tm_polytime V l
          (tmVerifierStateList V)
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat)
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun p : L.Instance.Carrier × Nat =>
              ((tmVerifierStateList V).flatMap fun s =>
                (tmVerifierStmtWindowsAt V p.2 ((tmVerifierTM V).m l) s).flatMap fun w =>
                  tmVerifierXOnlyWindowFixedMicroDomainCNFAt V p.1 p.2 w,
                labels.flatMap fun l =>
                  (tmVerifierStateList V).flatMap fun s =>
                    (tmVerifierStmtWindowsAt V p.2 ((tmVerifierTM V).m l) s).flatMap fun w =>
                      tmVerifierXOnlyWindowFixedMicroDomainCNFAt V p.1 p.2 w)) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hAppend := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
      simpa [Function.comp, cnfStructuredEncodedType] using hAppend

theorem tmVerifierXOnlyTransitionFixedMicroDomainCNFAt_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        tmVerifierXOnlyTransitionFixedMicroDomainCNFAt V p.1 p.2) := by
  simpa [tmVerifierXOnlyTransitionFixedMicroDomainCNFAt] using
    tmVerifierXOnlyTransitionFixedMicroDomainForLabels_pair_tm_polytime V
      (tmVerifierLabelList V)

theorem tmVerifierXOnlyTransitionFixedMicroDomainRowsCNF_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier =>
        tmVerifierXOnlyTransitionFixedMicroDomainRowsCNF V x) := by
  have hTimes := tmVerifierXOnlyTransitionTimeRange_tm_polytime V
  have hInput :
      TMPolyTimeMap L.Instance (EncodedType.prod L.Instance (EncodedType.list EncodedType.nat))
        (fun x : L.Instance.Carrier => (x, tmVerifierXOnlyTransitionTimeRange V x)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id L.Instance) hTimes
  have hFold := cnfContextFlatMap_tm_polytime
    (C := L.Instance) (X := EncodedType.nat)
    (fun x t => tmVerifierXOnlyTransitionFixedMicroDomainCNFAt V x t)
    (tmVerifierXOnlyTransitionFixedMicroDomainCNFAt_pair_tm_polytime V)
  have hComp := TMPolyTimeMap.comp hFold hInput
  simpa [Function.comp, tmVerifierXOnlyTransitionFixedMicroDomainRowsCNF] using hComp

theorem tmVerifierXOnlyGlobalTableauBaseCNF_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier => tmVerifierXOnlyGlobalTableauBaseCNF V x) := by
  have hControlRows := tmVerifierXOnlyControlDomainRowsCNF_tm_polytime V
  have hInitialControl := tmVerifierInitialControlCNF_tm_polytime V
  have hInitialStack := tmVerifierXOnlyInitialStackCNF_tm_polytime V
  have hStackRows := tmVerifierXOnlyStackWellFormedRowsCNF_tm_polytime V
  have hMicroRows := tmVerifierXOnlyTransitionFixedMicroDomainRowsCNF_tm_polytime V
  have hEndpoint := tmVerifierXOnlyEndpointCNF_tm_polytime V
  have h12Input :
      TMPolyTimeMap L.Instance
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun x : L.Instance.Carrier =>
          ((tmVerifierXOnlyTableauTimeRange V x).flatMap fun t =>
              tmVerifierControlDomainCNFAt V t,
            tmVerifierInitialControlCNF V)) :=
    TMPolyTimeMap.prod_mk hControlRows hInitialControl
  have h12 := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) h12Input
  have h123Input :
      TMPolyTimeMap L.Instance
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun x : L.Instance.Carrier =>
          (((tmVerifierXOnlyTableauTimeRange V x).flatMap fun t =>
              tmVerifierControlDomainCNFAt V t) ++
            tmVerifierInitialControlCNF V,
            tmVerifierXOnlyInitialStackCNF V x)) :=
    TMPolyTimeMap.prod_mk h12 hInitialStack
  have h123 := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) h123Input
  have h1234Input :
      TMPolyTimeMap L.Instance
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun x : L.Instance.Carrier =>
          ((((tmVerifierXOnlyTableauTimeRange V x).flatMap fun t =>
              tmVerifierControlDomainCNFAt V t) ++
            tmVerifierInitialControlCNF V) ++
            tmVerifierXOnlyInitialStackCNF V x,
            tmVerifierXOnlyStackWellFormedRowsCNF V x)) :=
    TMPolyTimeMap.prod_mk h123 hStackRows
  have h1234 := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) h1234Input
  have h12345Input :
      TMPolyTimeMap L.Instance
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun x : L.Instance.Carrier =>
          (((((tmVerifierXOnlyTableauTimeRange V x).flatMap fun t =>
              tmVerifierControlDomainCNFAt V t) ++
            tmVerifierInitialControlCNF V) ++
            tmVerifierXOnlyInitialStackCNF V x) ++
            tmVerifierXOnlyStackWellFormedRowsCNF V x,
            tmVerifierXOnlyTransitionFixedMicroDomainRowsCNF V x)) :=
    TMPolyTimeMap.prod_mk h1234 hMicroRows
  have h12345 := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) h12345Input
  have hAllInput :
      TMPolyTimeMap L.Instance
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun x : L.Instance.Carrier =>
          ((((((tmVerifierXOnlyTableauTimeRange V x).flatMap fun t =>
              tmVerifierControlDomainCNFAt V t) ++
            tmVerifierInitialControlCNF V) ++
            tmVerifierXOnlyInitialStackCNF V x) ++
            tmVerifierXOnlyStackWellFormedRowsCNF V x) ++
            tmVerifierXOnlyTransitionFixedMicroDomainRowsCNF V x,
            tmVerifierXOnlyEndpointCNF V x)) :=
    TMPolyTimeMap.prod_mk h12345 hEndpoint
  have hAll := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAllInput
  convert hAll using 1
  funext x
  exact list_append_six_flatMap_blocks
    ((tmVerifierXOnlyTableauTimeRange V x).flatMap fun t => tmVerifierControlDomainCNFAt V t)
    (tmVerifierInitialControlCNF V)
    (tmVerifierXOnlyInitialStackCNF V x)
    (tmVerifierXOnlyStackWellFormedRowsCNF V x)
    (tmVerifierXOnlyTransitionFixedMicroDomainRowsCNF V x)
    (tmVerifierXOnlyEndpointCNF V x)

end SAT
end ComplexityReduction
