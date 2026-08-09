/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauBlocks
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.ActionTrace

/-!
Fixed-pair global micro-row surface for verifier tableaux.

The older transition-window CNF uses a row-local micro-time coordinate.  That
coordinate is convenient for local lemmas, but it is not globally disjoint from
future macro rows in one fixed `(V,p)` tableau.  This file introduces parallel
CNF blocks whose micro rows are named by `tmVerifierFixedMicroTime V p t micro`,
which is outside the fixed macro tableau time range.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Global micro-row bookkeeping -/

theorem tmVerifierFixedMicroTime_ne_of_mem_tableauTimeRange
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    {u t micro : Nat} (hu : u ∈ tmVerifierTableauTimeRange V p) :
    tmVerifierFixedMicroTime V p t micro ≠ u := by
  have huLe : u ≤ tmVerifierTimeBound V p := by
    have huLt : u < tmVerifierTimeBound V p + 1 := by
      simpa [tmVerifierTableauTimeRange, List.mem_range] using hu
    exact Nat.le_of_lt_succ huLt
  exact tmVerifierFixedMicroTime_ne_macro_of_le_timeBound V p huLe

theorem tmVerifierFixedMicroTime_ne_of_mem_transitionTimeRange
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    {u t micro : Nat} (hu : u ∈ tmVerifierTransitionTimeRange V p) :
    tmVerifierFixedMicroTime V p t micro ≠ u := by
  have huLe : u ≤ tmVerifierTimeBound V p := by
    have huLt : u < tmVerifierTimeBound V p := by
      simpa [tmVerifierTransitionTimeRange, List.mem_range] using hu
    exact Nat.le_of_lt huLt
  exact tmVerifierFixedMicroTime_ne_macro_of_le_timeBound V p huLe

theorem tmVerifierFixedMicroTime_not_le_timeBound
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t micro : Nat) :
    ¬ tmVerifierFixedMicroTime V p t micro ≤ tmVerifierTimeBound V p := by
  intro hle
  have hbase := tmVerifierFixedMicroBase_le_time V p t micro
  simp [tmVerifierFixedMicroBase] at hbase
  omega

/-! ### Fixed-pair action read guards and stack-action rows -/

/-- The fixed-pair global micro-row read guard contributed by one indexed action. -/
noncomputable def TMVerifierStackAction.fixedReadGuardAt
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (p : L.Instance.Carrier × V.Cert.Carrier) (t actionIdx : Nat) :
    TMVerifierStackAction V → List Literal
  | TMVerifierStackAction.peek k choice =>
      [TMVerifierStackReadChoice.atomAt (V := V) (k := k)
        (tmVerifierFixedMicroTime V p t actionIdx) 0 choice]
  | TMVerifierStackAction.pop k choice =>
      [TMVerifierStackReadChoice.atomAt (V := V) (k := k)
        (tmVerifierFixedMicroTime V p t actionIdx) 0 choice]
  | _ => []

/-- Fixed-pair global micro-row read guards for actions starting at index `idx`. -/
noncomputable def tmVerifierWindowFixedActionReadGuardsFrom
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (actions : List (TMVerifierStackAction V)) (idx : Nat) : List Literal :=
  actions.zipIdx idx |>.flatMap fun entry =>
    entry.1.fixedReadGuardAt p t entry.2

/-- Fixed-pair global micro-row read guards for one generated statement window. -/
noncomputable def tmVerifierWindowFixedActionReadGuards
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) : List Literal :=
  tmVerifierWindowFixedActionReadGuardsFrom p t w.actions 0

/-- Antecedents for a fixed-pair window, using global micro-row read guards. -/
noncomputable def tmVerifierWindowFixedAntecedents
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) : List Literal :=
  [tmVerifierLabelAtom V t (some l), tmVerifierStateAtom V t s] ++
    tmVerifierWindowFixedActionReadGuards p t w

theorem tmVerifierWindowFixedAntecedents_label_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) :
    tmVerifierLabelAtom V t (some l) ∈
      tmVerifierWindowFixedAntecedents V p t l s w := by
  simp [tmVerifierWindowFixedAntecedents]

theorem tmVerifierWindowFixedAntecedents_state_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) :
    tmVerifierStateAtom V t s ∈ tmVerifierWindowFixedAntecedents V p t l s w := by
  simp [tmVerifierWindowFixedAntecedents]

theorem tmVerifierWindowFixedAntecedents_fixedGuard_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) {g : Literal}
    (hg : g ∈ tmVerifierWindowFixedActionReadGuards p t w) :
    g ∈ tmVerifierWindowFixedAntecedents V p t l s w := by
  rw [tmVerifierWindowFixedAntecedents]
  exact List.mem_append.mpr (Or.inr hg)

/-- Control clauses for one generated statement window using fixed-pair read guards. -/
noncomputable def tmVerifierWindowFixedControlCNFAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) : CNF :=
  let antecedents := tmVerifierWindowFixedAntecedents V p t l s w
  [ tmVerifierImplicationClause antecedents (tmVerifierLabelAtom V (t + 1) w.nextLabel)
  , tmVerifierImplicationClause antecedents (tmVerifierStateAtom V (t + 1) w.nextState)
  ]

theorem tmVerifierWindowFixedControlCNFAt_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment) {ant : Literal}
    (hmem : ant ∈ tmVerifierWindowFixedAntecedents V p t l s w)
    (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierWindowFixedControlCNFAt V p t l s w) a := by
  intro c hc
  have hc' :
      c =
          tmVerifierImplicationClause (tmVerifierWindowFixedAntecedents V p t l s w)
            (tmVerifierLabelAtom V (t + 1) w.nextLabel) ∨
        c =
          tmVerifierImplicationClause (tmVerifierWindowFixedAntecedents V p t l s w)
            (tmVerifierStateAtom V (t + 1) w.nextState) := by
    simpa [tmVerifierWindowFixedControlCNFAt] using hc
  rcases hc' with rfl | rfl
  · exact tmVerifierImplicationClause_satisfies_of_false_antecedent
      (tmVerifierWindowFixedAntecedents V p t l s w)
      (tmVerifierLabelAtom V (t + 1) w.nextLabel) ant a hmem hAnt
  · exact tmVerifierImplicationClause_satisfies_of_false_antecedent
      (tmVerifierWindowFixedAntecedents V p t l s w)
      (tmVerifierStateAtom V (t + 1) w.nextState) ant a hmem hAnt

/-- Clauses for the action sequence of one statement window using global micro rows. -/
noncomputable def tmVerifierWindowFixedStackActionCNFAt
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (antecedents : List Literal) : CNF :=
  w.actions.zipIdx.flatMap fun entry =>
    let tin := tmVerifierFixedMicroTime V p t entry.2
    let tout := tmVerifierFixedMicroTime V p t (entry.2 + 1)
    tmVerifierStackActionCNFBetween V B p tin tout antecedents entry.1

theorem tmVerifierWindowFixedStackActionCNFAt_satisfies_action
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (antecedents : List Literal)
    (a : Assignment)
    (h :
      CNF.Satisfies (tmVerifierWindowFixedStackActionCNFAt V B p t w antecedents) a)
    (entry : TMVerifierStackAction V × Nat)
    (hentry : entry ∈ w.actions.zipIdx) :
    CNF.Satisfies
      (tmVerifierStackActionCNFBetween V B p
        (tmVerifierFixedMicroTime V p t entry.2)
        (tmVerifierFixedMicroTime V p t (entry.2 + 1))
        antecedents entry.1) a := by
  intro c hc
  exact h c (by
    rw [tmVerifierWindowFixedStackActionCNFAt]
    exact List.mem_flatMap.mpr ⟨entry, hentry, hc⟩)

/-! ### Fixed-pair window boundaries and transition rows -/

/--
Stack-frame clauses connecting the macro input/output rows of a transition to
the first and final global micro rows of a selected statement window.
-/
noncomputable def tmVerifierWindowFixedStackBoundaryCNFAt
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) : CNF :=
  let antecedents := tmVerifierWindowFixedAntecedents V p t l s w
  tmVerifierFrameAllStacksCNFBetween V p t (tmVerifierFixedMicroTime V p t 0)
      antecedents ++
    tmVerifierFrameAllStacksCNFBetween V p
      (tmVerifierFixedMicroTime V p t w.actions.length) (t + 1) antecedents

theorem tmVerifierWindowFixedStackBoundaryCNFAt_satisfies_input_frame
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierWindowFixedStackBoundaryCNFAt V p t l s w) a)
    (hAntecedents :
      ∀ g ∈ tmVerifierWindowFixedAntecedents V p t l s w, g.eval a = true)
    (k : tmVerifierStackIndex V)
    (hIn : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a)
    (hOut :
      CNF.Satisfies
        (tmVerifierStackCellDomainsCNFAt V p (tmVerifierFixedMicroTime V p t 0) k)
        a) :
    TMVerifierDecodedFramePrefixEffect V p t (tmVerifierFixedMicroTime V p t 0) k
      a hIn hOut := by
  have hsplit := (CNF.satisfies_append
    (tmVerifierFrameAllStacksCNFBetween V p t (tmVerifierFixedMicroTime V p t 0)
      (tmVerifierWindowFixedAntecedents V p t l s w))
    (tmVerifierFrameAllStacksCNFBetween V p
      (tmVerifierFixedMicroTime V p t w.actions.length) (t + 1)
      (tmVerifierWindowFixedAntecedents V p t l s w)) a).1
      (by simpa [tmVerifierWindowFixedStackBoundaryCNFAt] using h)
  exact tmVerifierPreserveAllStacksActionCNFBetween_decoded_prefix_effect V p t
    (tmVerifierFixedMicroTime V p t 0) k
    (tmVerifierWindowFixedAntecedents V p t l s w) a
    (by simpa [tmVerifierPreserveAllStacksActionCNFBetween] using hsplit.1)
    hIn hOut (by
      classical
      simp [tmVerifierStackList]) hAntecedents

theorem tmVerifierWindowFixedStackBoundaryCNFAt_satisfies_output_frame
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierWindowFixedStackBoundaryCNFAt V p t l s w) a)
    (hAntecedents :
      ∀ g ∈ tmVerifierWindowFixedAntecedents V p t l s w, g.eval a = true)
    (k : tmVerifierStackIndex V)
    (hIn :
      CNF.Satisfies
        (tmVerifierStackCellDomainsCNFAt V p
          (tmVerifierFixedMicroTime V p t w.actions.length) k)
        a)
    (hOut : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p (t + 1) k) a) :
    TMVerifierDecodedFramePrefixEffect V p
      (tmVerifierFixedMicroTime V p t w.actions.length) (t + 1) k a hIn hOut := by
  have hsplit := (CNF.satisfies_append
    (tmVerifierFrameAllStacksCNFBetween V p t (tmVerifierFixedMicroTime V p t 0)
      (tmVerifierWindowFixedAntecedents V p t l s w))
    (tmVerifierFrameAllStacksCNFBetween V p
      (tmVerifierFixedMicroTime V p t w.actions.length) (t + 1)
      (tmVerifierWindowFixedAntecedents V p t l s w)) a).1
      (by simpa [tmVerifierWindowFixedStackBoundaryCNFAt] using h)
  exact tmVerifierPreserveAllStacksActionCNFBetween_decoded_prefix_effect V p
    (tmVerifierFixedMicroTime V p t w.actions.length) (t + 1) k
    (tmVerifierWindowFixedAntecedents V p t l s w) a
    (by simpa [tmVerifierPreserveAllStacksActionCNFBetween] using hsplit.2)
    hIn hOut (by
      classical
      simp [tmVerifierStackList]) hAntecedents

/-- Stack clauses for every fixed-pair global statement window in one transition row. -/
noncomputable def tmVerifierTransitionFixedWindowStackCNFAt
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) : CNF :=
  (tmVerifierLabelList V).flatMap fun l =>
    (tmVerifierStateList V).flatMap fun s =>
      (tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s).flatMap fun w =>
        tmVerifierWindowFixedStackBoundaryCNFAt V p t l s w ++
          tmVerifierWindowFixedStackActionCNFAt V B p t w
            (tmVerifierWindowFixedAntecedents V p t l s w)

theorem tmVerifierTransitionFixedWindowStackCNFAt_satisfies_window
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierTransitionFixedWindowStackCNFAt V B p t) a)
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s) :
    CNF.Satisfies
      (tmVerifierWindowFixedStackActionCNFAt V B p t w
        (tmVerifierWindowFixedAntecedents V p t l s w)) a := by
  intro c hc
  exact h c (by
    simp [tmVerifierTransitionFixedWindowStackCNFAt]
    exact ⟨l, hl, s, hs, w, hw, by simp [hc]⟩)

theorem tmVerifierTransitionFixedWindowStackCNFAt_satisfies_window_boundary
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierTransitionFixedWindowStackCNFAt V B p t) a)
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s) :
    CNF.Satisfies (tmVerifierWindowFixedStackBoundaryCNFAt V p t l s w) a := by
  intro c hc
  exact h c (by
    simp [tmVerifierTransitionFixedWindowStackCNFAt]
    exact ⟨l, hl, s, hs, w, hw, by simp [hc]⟩)

/-- Control clauses for every fixed-pair global statement window in one transition row. -/
noncomputable def tmVerifierTransitionFixedControlCNFAt
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) : CNF :=
  (tmVerifierLabelList V).flatMap fun l =>
    (tmVerifierStateList V).flatMap fun s =>
      (tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s).flatMap fun w =>
        tmVerifierWindowFixedControlCNFAt V p t l s w

/-- Transition row using fixed-pair global micro rows. -/
noncomputable def tmVerifierTransitionFixedRowCNFAt
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) : CNF :=
  tmVerifierTransitionFixedControlCNFAt V p t ++
    tmVerifierTransitionFixedWindowStackCNFAt V B p t ++
      tmVerifierHaltedRowsCNFAt V p t

theorem tmVerifierTransitionFixedRowCNFAt_satisfies_window_boundary
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierTransitionFixedRowCNFAt V B p t) a)
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s) :
    CNF.Satisfies (tmVerifierWindowFixedStackBoundaryCNFAt V p t l s w) a := by
  have hsplit := (CNF.satisfies_append
    (tmVerifierTransitionFixedControlCNFAt V p t)
    (tmVerifierTransitionFixedWindowStackCNFAt V B p t ++
      tmVerifierHaltedRowsCNFAt V p t) a).1
      (by simpa [tmVerifierTransitionFixedRowCNFAt] using h)
  have hstack := (CNF.satisfies_append
    (tmVerifierTransitionFixedWindowStackCNFAt V B p t)
    (tmVerifierHaltedRowsCNFAt V p t) a).1 hsplit.2 |>.1
  exact tmVerifierTransitionFixedWindowStackCNFAt_satisfies_window_boundary V B p t l s w
    a hstack hl hs hw

/-! ### Fixed-pair micro-domain rows -/

/-- Stack well-formed rows for all fixed-pair global micro rows touched by a window. -/
noncomputable def tmVerifierWindowFixedMicroDomainCNFAt
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) : CNF :=
  (tmVerifierWindowMicroTimeRange V w).flatMap fun micro =>
    (tmVerifierStackList V).flatMap fun k =>
      tmVerifierStackWellFormedCNFAt V p (tmVerifierFixedMicroTime V p t micro) k

theorem tmVerifierWindowFixedMicroDomainCNFAt_satisfies_wellFormed_of_microTime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (micro : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierWindowFixedMicroDomainCNFAt V p t w) a)
    (hmicro : micro ∈ tmVerifierWindowMicroTimeRange V w)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies
      (tmVerifierStackWellFormedCNFAt V p (tmVerifierFixedMicroTime V p t micro) k)
      a := by
  intro c hc
  exact h c (by
    rw [tmVerifierWindowFixedMicroDomainCNFAt]
    exact List.mem_flatMap.mpr
      ⟨micro, hmicro,
        List.mem_flatMap.mpr ⟨k, tmVerifierStackList_mem V k, hc⟩⟩)

theorem tmVerifierWindowFixedMicroDomainCNFAt_satisfies_domain_of_microTime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (micro : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierWindowFixedMicroDomainCNFAt V p t w) a)
    (hmicro : micro ∈ tmVerifierWindowMicroTimeRange V w)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies
      (tmVerifierStackCellDomainsCNFAt V p (tmVerifierFixedMicroTime V p t micro) k)
      a := by
  have hWF :=
    tmVerifierWindowFixedMicroDomainCNFAt_satisfies_wellFormed_of_microTime V p t w
      micro a h hmicro k
  exact tmVerifierStackWellFormedCNFAt_satisfies_domains V p
    (tmVerifierFixedMicroTime V p t micro) k a hWF

theorem tmVerifierWindowFixedMicroDomainCNFAt_satisfies_domain
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (micro : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierWindowFixedMicroDomainCNFAt V p t w) a)
    (hmicro : micro ∈ tmVerifierWindowActionMicroTimeRange V w)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies
      (tmVerifierStackCellDomainsCNFAt V p (tmVerifierFixedMicroTime V p t micro) k)
      a :=
  tmVerifierWindowFixedMicroDomainCNFAt_satisfies_domain_of_microTime V p t w micro a h
    (tmVerifierWindowActionMicroTimeRange_mem_microTimeRange V w hmicro) k

/-- Fixed-pair global micro-domain rows for every statement window of one row. -/
noncomputable def tmVerifierTransitionFixedMicroDomainCNFAt
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) : CNF :=
  (tmVerifierLabelList V).flatMap fun l =>
    (tmVerifierStateList V).flatMap fun s =>
      (tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s).flatMap fun w =>
        tmVerifierWindowFixedMicroDomainCNFAt V p t w

theorem tmVerifierTransitionFixedMicroDomainCNFAt_satisfies_window
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierTransitionFixedMicroDomainCNFAt V p t) a)
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s) :
    CNF.Satisfies (tmVerifierWindowFixedMicroDomainCNFAt V p t w) a := by
  intro c hc
  exact h c (by
    rw [tmVerifierTransitionFixedMicroDomainCNFAt]
    exact List.mem_flatMap.mpr
      ⟨l, hl, List.mem_flatMap.mpr
        ⟨s, hs, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩⟩)

/-- Fixed-pair global micro-domain rows for every transition row with a successor. -/
noncomputable def tmVerifierTransitionFixedMicroDomainRowsCNF
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) : CNF :=
  (tmVerifierTransitionTimeRange V p).flatMap fun t =>
    tmVerifierTransitionFixedMicroDomainCNFAt V p t

theorem tmVerifierTransitionFixedMicroDomainRowsCNF_satisfies_at
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierTransitionFixedMicroDomainRowsCNF V p) a)
    (ht : t ∈ tmVerifierTransitionTimeRange V p) :
    CNF.Satisfies (tmVerifierTransitionFixedMicroDomainCNFAt V p t) a := by
  intro c hc
  exact h c (by
    rw [tmVerifierTransitionFixedMicroDomainRowsCNF]
    exact List.mem_flatMap.mpr ⟨t, ht, hc⟩)

/-- Fixed-pair global transition rows for every macro row with a successor. -/
noncomputable def tmVerifierTransitionFixedRowsCNF
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) : CNF :=
  (tmVerifierTransitionTimeRange V p).flatMap fun t =>
    tmVerifierTransitionFixedRowCNFAt V B p t

theorem tmVerifierTransitionFixedRowsCNF_satisfies_at
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierTransitionFixedRowsCNF V B p) a)
    (ht : t ∈ tmVerifierTransitionTimeRange V p) :
    CNF.Satisfies (tmVerifierTransitionFixedRowCNFAt V B p t) a := by
  intro c hc
  exact h c (by
    rw [tmVerifierTransitionFixedRowsCNF]
    exact List.mem_flatMap.mpr ⟨t, ht, hc⟩)

/-! ### Global fixed-pair aggregate tableau -/

/-- Named component blocks of the fixed-pair tableau with global micro rows. -/
noncomputable def tmVerifierGlobalTableauBlocks
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) : List CNF :=
  [ tmVerifierControlDomainRowsCNF V p
  , tmVerifierInitialControlCNF V
  , tmVerifierInitialStackCNF V p
  , tmVerifierStackWellFormedRowsCNF V p
  , tmVerifierTransitionFixedMicroDomainRowsCNF V p
  , tmVerifierTransitionFixedRowsCNF V B p
  , tmVerifierEndpointCNF V p
  ]

/-- Aggregate fixed-pair tableau CNF using global micro rows. -/
noncomputable def tmVerifierGlobalTableauCNF
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) : CNF :=
  (tmVerifierGlobalTableauBlocks V B p).flatMap id

theorem tmVerifierGlobalTableauCNF_satisfies_block
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierGlobalTableauCNF V B p) a)
    {block : CNF} (hblock : block ∈ tmVerifierGlobalTableauBlocks V B p) :
    CNF.Satisfies block a := by
  intro c hc
  exact h c (by
    rw [tmVerifierGlobalTableauCNF]
    exact List.mem_flatMap.mpr ⟨block, hblock, hc⟩)

theorem tmVerifierGlobalTableauCNF_satisfies_transitionFixedRows
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierGlobalTableauCNF V B p) a) :
    CNF.Satisfies (tmVerifierTransitionFixedRowsCNF V B p) a :=
  tmVerifierGlobalTableauCNF_satisfies_block V B p a h (by
    simp [tmVerifierGlobalTableauBlocks])

theorem tmVerifierGlobalTableauCNF_satisfies_transitionFixedMicroDomainRows
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierGlobalTableauCNF V B p) a) :
    CNF.Satisfies (tmVerifierTransitionFixedMicroDomainRowsCNF V p) a :=
  tmVerifierGlobalTableauCNF_satisfies_block V B p a h (by
    simp [tmVerifierGlobalTableauBlocks])

theorem tmVerifierGlobalTableauCNF_satisfies_transitionFixedRow
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierGlobalTableauCNF V B p) a)
    (ht : t ∈ tmVerifierTransitionTimeRange V p) :
    CNF.Satisfies (tmVerifierTransitionFixedRowCNFAt V B p t) a :=
  tmVerifierTransitionFixedRowsCNF_satisfies_at V B p t a
    (tmVerifierGlobalTableauCNF_satisfies_transitionFixedRows V B p a h) ht

theorem tmVerifierGlobalTableauCNF_satisfies_transitionFixedMicroDomainRow
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierGlobalTableauCNF V B p) a)
    (ht : t ∈ tmVerifierTransitionTimeRange V p) :
    CNF.Satisfies (tmVerifierTransitionFixedMicroDomainCNFAt V p t) a :=
  tmVerifierTransitionFixedMicroDomainRowsCNF_satisfies_at V p t a
    (tmVerifierGlobalTableauCNF_satisfies_transitionFixedMicroDomainRows V B p a h) ht

/--
An x-only tableau seed using the global fixed-pair micro-row tableau.

This is the safe seed for the accepting-run completeness direction; the older
`TMVerifierXOnlyTableauSeed` remains available for existing extraction lemmas
until they are migrated.
-/
structure TMVerifierXOnlyGlobalTableauSeed
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (a : Assignment) : Type where
  cert : V.Cert.Carrier
  cert_size :
    V.Cert.inputSize cert ≤ tmVerifierCertificateSizeBound V x
  global_tableau :
    CNF.Satisfies (tmVerifierGlobalTableauCNF V B (x, cert)) a

namespace TMVerifierXOnlyGlobalTableauSeed

theorem nonempty_iff_exists
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (a : Assignment) :
    Nonempty (TMVerifierXOnlyGlobalTableauSeed V B x a) ↔
      ∃ c, V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x ∧
        CNF.Satisfies (tmVerifierGlobalTableauCNF V B (x, c)) a := by
  constructor
  · rintro ⟨w⟩
    exact ⟨w.cert, w.cert_size, w.global_tableau⟩
  · rintro ⟨c, hSize, hTableau⟩
    exact ⟨{ cert := c, cert_size := hSize, global_tableau := hTableau }⟩

theorem transitionFixedRow_satisfies
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyGlobalTableauSeed V B x a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V (x, w.cert)) :
    CNF.Satisfies (tmVerifierTransitionFixedRowCNFAt V B (x, w.cert) t) a :=
  tmVerifierGlobalTableauCNF_satisfies_transitionFixedRow V B (x, w.cert) t a
    w.global_tableau ht

end TMVerifierXOnlyGlobalTableauSeed

end SAT
end ComplexityReduction
