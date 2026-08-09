/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyBlocks

/-!
X-only transition-window CNF rows for the global Cook-Levin tableau.

This file mirrors the fixed-pair global transition rows, replacing every
fixed-pair range and micro-time coordinate by the certificate-independent
x-only versions.
-/

namespace ComplexityReduction
namespace SAT

/-! ### x-only action/read guards -/

/-- The x-only global micro-row read guard contributed by one indexed action. -/
noncomputable def TMVerifierStackAction.xOnlyFixedReadGuardAt
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (x : L.Instance.Carrier) (t actionIdx : Nat) :
    TMVerifierStackAction V → List Literal
  | TMVerifierStackAction.peek k choice =>
      [TMVerifierStackReadChoice.atomAt (V := V) (k := k)
        (tmVerifierXOnlyFixedMicroTime V x t actionIdx) 0 choice]
  | TMVerifierStackAction.pop k choice =>
      [TMVerifierStackReadChoice.atomAt (V := V) (k := k)
        (tmVerifierXOnlyFixedMicroTime V x t actionIdx) 0 choice]
  | _ => []

/-- X-only global micro-row read guards for actions starting at index `idx`. -/
noncomputable def tmVerifierXOnlyWindowFixedActionReadGuardsFrom
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (x : L.Instance.Carrier) (t : Nat)
    (actions : List (TMVerifierStackAction V)) (idx : Nat) : List Literal :=
  actions.zipIdx idx |>.flatMap fun entry =>
    entry.1.xOnlyFixedReadGuardAt x t entry.2

/-- X-only global micro-row read guards for one generated statement window. -/
noncomputable def tmVerifierXOnlyWindowFixedActionReadGuards
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (x : L.Instance.Carrier) (t : Nat) (w : TMVerifierStmtWindow V) : List Literal :=
  tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t w.actions 0

/-- Antecedents for an x-only window, using x-only global micro-row read guards. -/
noncomputable def tmVerifierXOnlyWindowFixedAntecedents
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) : List Literal :=
  [tmVerifierLabelAtom V t (some l), tmVerifierStateAtom V t s] ++
    tmVerifierXOnlyWindowFixedActionReadGuards x t w

theorem tmVerifierXOnlyWindowFixedAntecedents_label_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) :
    tmVerifierLabelAtom V t (some l) ∈
      tmVerifierXOnlyWindowFixedAntecedents V x t l s w := by
  simp [tmVerifierXOnlyWindowFixedAntecedents]

theorem tmVerifierXOnlyWindowFixedAntecedents_state_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) :
    tmVerifierStateAtom V t s ∈ tmVerifierXOnlyWindowFixedAntecedents V x t l s w := by
  simp [tmVerifierXOnlyWindowFixedAntecedents]

/-! ### x-only primitive action blocks -/

/-- Frame clauses for every x-only bounded cell of one stack. -/
noncomputable def tmVerifierXOnlyFrameStackCNFBetween
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (antecedents : List Literal) : CNF :=
  (tmVerifierXOnlyCellRange V x).flatMap fun cell =>
    tmVerifierFrameCellCNFBetween V tin tout k cell antecedents

/-- Frame clauses for every stack in the x-only bounded tableau. -/
noncomputable def tmVerifierXOnlyFrameAllStacksCNFBetween
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (tin tout : Nat) (antecedents : List Literal) : CNF :=
  (tmVerifierStackList V).flatMap fun k =>
    tmVerifierXOnlyFrameStackCNFBetween V x tin tout k antecedents

/-- Clauses for one x-only push micro-step. -/
noncomputable def tmVerifierXOnlyPushActionCNFBetween
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (antecedents : List Literal) : CNF :=
  tmVerifierPushTopCNF V B tout raw antecedents ++
    (tmVerifierXOnlyCellRange V x).flatMap
      (fun cell => tmVerifierPushShiftCellCNF V tin tout raw.stack cell antecedents) ++
    (tmVerifierOtherStacks V raw.stack).flatMap fun k =>
      tmVerifierXOnlyFrameStackCNFBetween V x tin tout k antecedents

/-- Clauses for one x-only pop micro-step. -/
noncomputable def tmVerifierXOnlyPopActionCNFBetween
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (antecedents : List Literal) : CNF :=
  (tmVerifierXOnlyCellRange V x).flatMap
      (fun cell => tmVerifierPopShiftCellCNF V tin tout k cell antecedents) ++
    (tmVerifierOtherStacks V k).flatMap fun j =>
      tmVerifierXOnlyFrameStackCNFBetween V x tin tout j antecedents

/-- Clauses for an x-only micro-step that preserves every stack. -/
noncomputable def tmVerifierXOnlyPreserveAllStacksActionCNFBetween
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (tin tout : Nat) (antecedents : List Literal) : CNF :=
  tmVerifierXOnlyFrameAllStacksCNFBetween V x tin tout antecedents

/-- Effect clauses for one x-only recorded stack/control action. -/
noncomputable def tmVerifierXOnlyStackActionEffectCNFBetween
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (tin tout : Nat)
    (antecedents : List Literal) : TMVerifierStackAction V → CNF
  | TMVerifierStackAction.push raw =>
      tmVerifierXOnlyPushActionCNFBetween V B x tin tout raw antecedents
  | TMVerifierStackAction.pop k _ =>
      tmVerifierXOnlyPopActionCNFBetween V x tin tout k antecedents
  | TMVerifierStackAction.peek _ _ =>
      tmVerifierXOnlyPreserveAllStacksActionCNFBetween V x tin tout antecedents
  | TMVerifierStackAction.load =>
      tmVerifierXOnlyPreserveAllStacksActionCNFBetween V x tin tout antecedents
  | TMVerifierStackAction.branch _ =>
      tmVerifierXOnlyPreserveAllStacksActionCNFBetween V x tin tout antecedents

/-- Primitive x-only clauses for one recorded stack/control action. -/
noncomputable def tmVerifierXOnlyStackActionCNFBetween
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (tin tout : Nat)
    (antecedents : List Literal) (act : TMVerifierStackAction V) : CNF :=
  tmVerifierXOnlyStackActionEffectCNFBetween V B x tin tout antecedents act ++
    tmVerifierStackActionReadCNFAt tin antecedents act

/-- Clauses for the action sequence of one statement window using x-only global micro rows. -/
noncomputable def tmVerifierXOnlyWindowFixedStackActionCNFAt
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (antecedents : List Literal) : CNF :=
  w.actions.zipIdx.flatMap fun entry =>
    let tin := tmVerifierXOnlyFixedMicroTime V x t entry.2
    let tout := tmVerifierXOnlyFixedMicroTime V x t (entry.2 + 1)
    tmVerifierXOnlyStackActionCNFBetween V B x tin tout antecedents entry.1

theorem tmVerifierXOnlyWindowFixedStackActionCNFAt_satisfies_action
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (antecedents : List Literal)
    (a : Assignment)
    (h :
      CNF.Satisfies
        (tmVerifierXOnlyWindowFixedStackActionCNFAt V B x t w antecedents) a)
    (entry : TMVerifierStackAction V × Nat)
    (hentry : entry ∈ w.actions.zipIdx) :
    CNF.Satisfies
      (tmVerifierXOnlyStackActionCNFBetween V B x
        (tmVerifierXOnlyFixedMicroTime V x t entry.2)
        (tmVerifierXOnlyFixedMicroTime V x t (entry.2 + 1))
        antecedents entry.1) a := by
  intro c hc
  exact h c (by
    rw [tmVerifierXOnlyWindowFixedStackActionCNFAt]
    exact List.mem_flatMap.mpr ⟨entry, hentry, hc⟩)

/-! ### x-only window and row aggregation -/

/-- Stack-frame clauses connecting macro rows to x-only global micro rows. -/
noncomputable def tmVerifierXOnlyWindowFixedStackBoundaryCNFAt
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) : CNF :=
  let antecedents := tmVerifierXOnlyWindowFixedAntecedents V x t l s w
  tmVerifierXOnlyFrameAllStacksCNFBetween V x t
      (tmVerifierXOnlyFixedMicroTime V x t 0) antecedents ++
    tmVerifierXOnlyFrameAllStacksCNFBetween V x
      (tmVerifierXOnlyFixedMicroTime V x t w.actions.length) (t + 1) antecedents

/-- Control clauses for one generated statement window using x-only read guards. -/
noncomputable def tmVerifierXOnlyWindowFixedControlCNFAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) : CNF :=
  let antecedents := tmVerifierXOnlyWindowFixedAntecedents V x t l s w
  [ tmVerifierImplicationClause antecedents (tmVerifierLabelAtom V (t + 1) w.nextLabel)
  , tmVerifierImplicationClause antecedents (tmVerifierStateAtom V (t + 1) w.nextState)
  ]

/-- Stack clauses for every x-only global statement window in one transition row. -/
noncomputable def tmVerifierXOnlyTransitionFixedWindowStackCNFAt
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (t : Nat) : CNF :=
  (tmVerifierLabelList V).flatMap fun l =>
    (tmVerifierStateList V).flatMap fun s =>
      (tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s).flatMap fun w =>
        tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V x t l s w ++
          tmVerifierXOnlyWindowFixedStackActionCNFAt V B x t w
            (tmVerifierXOnlyWindowFixedAntecedents V x t l s w)

theorem tmVerifierXOnlyTransitionFixedWindowStackCNFAt_satisfies_window
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyTransitionFixedWindowStackCNFAt V B x t) a)
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s) :
    CNF.Satisfies
      (tmVerifierXOnlyWindowFixedStackActionCNFAt V B x t w
        (tmVerifierXOnlyWindowFixedAntecedents V x t l s w)) a := by
  intro c hc
  exact h c (by
    simp [tmVerifierXOnlyTransitionFixedWindowStackCNFAt]
    exact ⟨l, hl, s, hs, w, hw, by simp [hc]⟩)

theorem tmVerifierXOnlyTransitionFixedWindowStackCNFAt_satisfies_window_boundary
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyTransitionFixedWindowStackCNFAt V B x t) a)
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s) :
    CNF.Satisfies (tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V x t l s w) a := by
  intro c hc
  exact h c (by
    simp [tmVerifierXOnlyTransitionFixedWindowStackCNFAt]
    exact ⟨l, hl, s, hs, w, hw, by simp [hc]⟩)

/-- Control clauses for every x-only global statement window in one transition row. -/
noncomputable def tmVerifierXOnlyTransitionFixedControlCNFAt
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) (t : Nat) : CNF :=
  (tmVerifierLabelList V).flatMap fun l =>
    (tmVerifierStateList V).flatMap fun s =>
      (tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s).flatMap fun w =>
        tmVerifierXOnlyWindowFixedControlCNFAt V x t l s w

/-- One x-only halted-row padding block. -/
noncomputable def tmVerifierXOnlyHaltedRowCNFAt
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (t : Nat) (s : (tmVerifierTM V).σ) : CNF :=
  let antecedents := tmVerifierHaltedRowAntecedents V t s
  [ tmVerifierImplicationClause antecedents (tmVerifierLabelAtom V (t + 1) none)
  , tmVerifierImplicationClause antecedents (tmVerifierStateAtom V (t + 1) s)
  ] ++
    tmVerifierXOnlyFrameAllStacksCNFBetween V x t (t + 1) antecedents

/-- X-only halted-row padding clauses for every finite internal state. -/
noncomputable def tmVerifierXOnlyHaltedRowsCNFAt
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) (t : Nat) : CNF :=
  (tmVerifierStateList V).flatMap fun s =>
    tmVerifierXOnlyHaltedRowCNFAt V x t s

/-- Transition row using x-only global micro rows. -/
noncomputable def tmVerifierXOnlyTransitionFixedRowCNFAt
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (t : Nat) : CNF :=
  tmVerifierXOnlyTransitionFixedControlCNFAt V x t ++
    tmVerifierXOnlyTransitionFixedWindowStackCNFAt V B x t ++
      tmVerifierXOnlyHaltedRowsCNFAt V x t

theorem tmVerifierXOnlyTransitionFixedRowCNFAt_satisfies_window_boundary
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyTransitionFixedRowCNFAt V B x t) a)
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s) :
    CNF.Satisfies (tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V x t l s w) a := by
  have hsplit := (CNF.satisfies_append
    (tmVerifierXOnlyTransitionFixedControlCNFAt V x t)
    (tmVerifierXOnlyTransitionFixedWindowStackCNFAt V B x t ++
      tmVerifierXOnlyHaltedRowsCNFAt V x t) a).1
      (by simpa [tmVerifierXOnlyTransitionFixedRowCNFAt] using h)
  have hstack := (CNF.satisfies_append
    (tmVerifierXOnlyTransitionFixedWindowStackCNFAt V B x t)
    (tmVerifierXOnlyHaltedRowsCNFAt V x t) a).1 hsplit.2 |>.1
  exact tmVerifierXOnlyTransitionFixedWindowStackCNFAt_satisfies_window_boundary V B x t
    l s w a hstack hl hs hw

/-- X-only global transition rows for every macro row with a successor. -/
noncomputable def tmVerifierXOnlyTransitionFixedRowsCNF
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) : CNF :=
  (tmVerifierXOnlyTransitionTimeRange V x).flatMap fun t =>
    tmVerifierXOnlyTransitionFixedRowCNFAt V B x t

theorem tmVerifierXOnlyTransitionFixedRowsCNF_satisfies_at
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyTransitionFixedRowsCNF V B x) a)
    (ht : t ∈ tmVerifierXOnlyTransitionTimeRange V x) :
    CNF.Satisfies (tmVerifierXOnlyTransitionFixedRowCNFAt V B x t) a := by
  intro c hc
  exact h c (by
    rw [tmVerifierXOnlyTransitionFixedRowsCNF]
    exact List.mem_flatMap.mpr ⟨t, ht, hc⟩)

/-! ### Full x-only aggregate surface -/

/-- Named component blocks of the x-only tableau with global micro rows. -/
noncomputable def tmVerifierXOnlyGlobalTableauBlocks
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) : List CNF :=
  [ (tmVerifierXOnlyTableauTimeRange V x).flatMap fun t =>
      tmVerifierControlDomainCNFAt V t
  , tmVerifierInitialControlCNF V
  , tmVerifierXOnlyInitialStackCNF V x
  , tmVerifierXOnlyStackWellFormedRowsCNF V x
  , tmVerifierXOnlyTransitionFixedMicroDomainRowsCNF V x
  , tmVerifierXOnlyTransitionFixedRowsCNF V B x
  , tmVerifierXOnlyEndpointCNF V x
  ]

/-- Aggregate x-only tableau CNF using global micro rows. -/
noncomputable def tmVerifierXOnlyGlobalTableauCNF
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) : CNF :=
  (tmVerifierXOnlyGlobalTableauBlocks V B x).flatMap id

theorem tmVerifierXOnlyGlobalTableauCNF_satisfies_block
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyGlobalTableauCNF V B x) a)
    {block : CNF} (hblock : block ∈ tmVerifierXOnlyGlobalTableauBlocks V B x) :
    CNF.Satisfies block a := by
  intro c hc
  exact h c (by
    rw [tmVerifierXOnlyGlobalTableauCNF]
    exact List.mem_flatMap.mpr ⟨block, hblock, hc⟩)

theorem tmVerifierXOnlyGlobalTableauCNF_satisfies_transitionFixedRows
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyGlobalTableauCNF V B x) a) :
    CNF.Satisfies (tmVerifierXOnlyTransitionFixedRowsCNF V B x) a :=
  tmVerifierXOnlyGlobalTableauCNF_satisfies_block V B x a h (by
    simp [tmVerifierXOnlyGlobalTableauBlocks])

theorem tmVerifierXOnlyGlobalTableauCNF_satisfies_transitionFixedRow
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyGlobalTableauCNF V B x) a)
    (ht : t ∈ tmVerifierXOnlyTransitionTimeRange V x) :
    CNF.Satisfies (tmVerifierXOnlyTransitionFixedRowCNFAt V B x t) a :=
  tmVerifierXOnlyTransitionFixedRowsCNF_satisfies_at V B x t a
    (tmVerifierXOnlyGlobalTableauCNF_satisfies_transitionFixedRows V B x a h) ht

end SAT
end ComplexityReduction
