/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyMacroSteps

/-!
X-only selected-window macro-row soundness.

This file connects the finite x-only action semantics to
`TMVerifierXOnlyGlobalTableauEvidence`, assuming a concrete statement window
and true read guards have already been selected.
-/

namespace ComplexityReduction
namespace SAT

/-! ### X-only window boundary frames -/

theorem tmVerifierXOnlyWindowFixedStackBoundaryCNFAt_satisfies_input_frame
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V x t l s w) a)
    (hAntecedents :
      ∀ g ∈ tmVerifierXOnlyWindowFixedAntecedents V x t l s w, g.eval a = true)
    (k : tmVerifierStackIndex V)
    (hIn : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t k) a)
    (hOut :
      CNF.Satisfies
        (tmVerifierXOnlyStackCellDomainsCNFAt V x (tmVerifierXOnlyFixedMicroTime V x t 0)
          k) a) :
    TMVerifierXOnlyDecodedFramePrefixEffect V x t (tmVerifierXOnlyFixedMicroTime V x t 0)
      k a hIn hOut := by
  have hsplit := (CNF.satisfies_append
    (tmVerifierXOnlyFrameAllStacksCNFBetween V x t
      (tmVerifierXOnlyFixedMicroTime V x t 0)
      (tmVerifierXOnlyWindowFixedAntecedents V x t l s w))
    (tmVerifierXOnlyFrameAllStacksCNFBetween V x
      (tmVerifierXOnlyFixedMicroTime V x t w.actions.length) (t + 1)
      (tmVerifierXOnlyWindowFixedAntecedents V x t l s w)) a).1
      (by simpa [tmVerifierXOnlyWindowFixedStackBoundaryCNFAt] using h)
  exact tmVerifierXOnlyPreserveAllStacksActionCNFBetween_decoded_prefix_effect V x t
    (tmVerifierXOnlyFixedMicroTime V x t 0) k
    (tmVerifierXOnlyWindowFixedAntecedents V x t l s w) a
    (by simpa [tmVerifierXOnlyPreserveAllStacksActionCNFBetween] using hsplit.1)
    hIn hOut (by
      classical
      simp [tmVerifierStackList]) hAntecedents

theorem tmVerifierXOnlyWindowFixedStackBoundaryCNFAt_satisfies_output_frame
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V x t l s w) a)
    (hAntecedents :
      ∀ g ∈ tmVerifierXOnlyWindowFixedAntecedents V x t l s w, g.eval a = true)
    (k : tmVerifierStackIndex V)
    (hIn :
      CNF.Satisfies
        (tmVerifierXOnlyStackCellDomainsCNFAt V x
          (tmVerifierXOnlyFixedMicroTime V x t w.actions.length) k) a)
    (hOut : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x (t + 1) k) a) :
    TMVerifierXOnlyDecodedFramePrefixEffect V x
      (tmVerifierXOnlyFixedMicroTime V x t w.actions.length) (t + 1) k a hIn hOut := by
  have hsplit := (CNF.satisfies_append
    (tmVerifierXOnlyFrameAllStacksCNFBetween V x t
      (tmVerifierXOnlyFixedMicroTime V x t 0)
      (tmVerifierXOnlyWindowFixedAntecedents V x t l s w))
    (tmVerifierXOnlyFrameAllStacksCNFBetween V x
      (tmVerifierXOnlyFixedMicroTime V x t w.actions.length) (t + 1)
      (tmVerifierXOnlyWindowFixedAntecedents V x t l s w)) a).1
      (by simpa [tmVerifierXOnlyWindowFixedStackBoundaryCNFAt] using h)
  exact tmVerifierXOnlyPreserveAllStacksActionCNFBetween_decoded_prefix_effect V x
    (tmVerifierXOnlyFixedMicroTime V x t w.actions.length) (t + 1) k
    (tmVerifierXOnlyWindowFixedAntecedents V x t l s w) a
    (by simpa [tmVerifierXOnlyPreserveAllStacksActionCNFBetween] using hsplit.2)
    hIn hOut (by
      classical
      simp [tmVerifierStackList]) hAntecedents

/-! ### Finite x-only row as a `stepAux` row -/

theorem TMVerifierXOnlyWindowFixedRowFiniteEffect.stepAux_next_control
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {B : TMVerifierPushPayloadBoundary V}
    {x : L.Instance.Carrier}
    {t : Nat} {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V} {a : Assignment}
    {hDomains : TMVerifierXOnlyWindowFixedActionDomainEvidence V x t w a}
    {stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k)}
    (hEff : TMVerifierXOnlyWindowFixedRowFiniteEffect V B x t l s w a hDomains)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (hMatch : tmVerifierWindowActionsMatchStacks w.actions stk) :
    (tmVerifierLabelAtom V (t + 1)
        (Turing.TM2.stepAux ((tmVerifierTM V).m l) s stk).l).eval a = true ∧
      (tmVerifierStateAtom V (t + 1)
        (Turing.TM2.stepAux ((tmVerifierTM V).m l) s stk).var).eval a = true ∧
        tmVerifierWindowActionsApplyStacks w.actions stk =
          (Turing.TM2.stepAux ((tmVerifierTM V).m l) s stk).stk := by
  have hStep := tmVerifierStmtWindowsAt_stepAux_agrees V t ((tmVerifierTM V).m l) s
    stk hw hMatch
  exact ⟨by simpa [hStep.1] using hEff.1,
    by simpa [hStep.2.1] using hEff.2.1,
    hStep.2.2⟩

namespace TMVerifierXOnlyGlobalTableauEvidence

theorem windowActionDomainEvidence
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {t : Nat} (ht : t ∈ tmVerifierXOnlyTransitionTimeRange V x)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s) :
    TMVerifierXOnlyWindowFixedActionDomainEvidence V x t w a := by
  intro entry hentry
  have hWindow :
      CNF.Satisfies (tmVerifierXOnlyWindowFixedMicroDomainCNFAt V x t w) a :=
    tmVerifierXOnlyTransitionFixedMicroDomainCNFAt_satisfies_window V x t l s w a
      (E.transitionFixedMicroDomainRow t ht) hl hs hw
  constructor
  · intro k
    exact tmVerifierXOnlyWindowFixedMicroDomainCNFAt_satisfies_domain V x t w
      entry.2 a hWindow (tmVerifierWindowActionMicroTimeRange_input_mem V w entry hentry) k
  · intro k
    exact tmVerifierXOnlyWindowFixedMicroDomainCNFAt_satisfies_domain V x t w
      (entry.2 + 1) a hWindow
      (tmVerifierWindowActionMicroTimeRange_output_mem V w entry hentry) k

theorem windowActionWellFormedEvidence
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {t : Nat} (ht : t ∈ tmVerifierXOnlyTransitionTimeRange V x)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s) :
    TMVerifierXOnlyWindowFixedActionWellFormedEvidence V x t w a := by
  intro entry hentry
  have hWindow :
      CNF.Satisfies (tmVerifierXOnlyWindowFixedMicroDomainCNFAt V x t w) a :=
    tmVerifierXOnlyTransitionFixedMicroDomainCNFAt_satisfies_window V x t l s w a
      (E.transitionFixedMicroDomainRow t ht) hl hs hw
  constructor
  · intro k
    exact tmVerifierXOnlyWindowFixedMicroDomainCNFAt_satisfies_wellFormed_of_microTime
      V x t w entry.2 a hWindow
      (tmVerifierWindowActionMicroTimeRange_mem_microTimeRange V w
        (tmVerifierWindowActionMicroTimeRange_input_mem V w entry hentry)) k
  · intro k
    exact tmVerifierXOnlyWindowFixedMicroDomainCNFAt_satisfies_wellFormed_of_microTime
      V x t w (entry.2 + 1) a hWindow
      (tmVerifierWindowActionMicroTimeRange_mem_microTimeRange V w
        (tmVerifierWindowActionMicroTimeRange_output_mem V w entry hentry)) k

theorem windowStartDomain
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {t : Nat} (ht : t ∈ tmVerifierXOnlyTransitionTimeRange V x)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies
      (tmVerifierXOnlyStackCellDomainsCNFAt V x
        (tmVerifierXOnlyFixedMicroTime V x t 0) k) a := by
  have hWindow :
      CNF.Satisfies (tmVerifierXOnlyWindowFixedMicroDomainCNFAt V x t w) a :=
    tmVerifierXOnlyTransitionFixedMicroDomainCNFAt_satisfies_window V x t l s w a
      (E.transitionFixedMicroDomainRow t ht) hl hs hw
  exact tmVerifierXOnlyWindowFixedMicroDomainCNFAt_satisfies_domain_of_microTime V x t w
    0 a hWindow (tmVerifierWindowMicroTimeRange_zero_mem V w) k

theorem windowStartWellFormed
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {t : Nat} (ht : t ∈ tmVerifierXOnlyTransitionTimeRange V x)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies
      (tmVerifierXOnlyStackWellFormedCNFAt V x
        (tmVerifierXOnlyFixedMicroTime V x t 0) k) a := by
  have hWindow :
      CNF.Satisfies (tmVerifierXOnlyWindowFixedMicroDomainCNFAt V x t w) a :=
    tmVerifierXOnlyTransitionFixedMicroDomainCNFAt_satisfies_window V x t l s w a
      (E.transitionFixedMicroDomainRow t ht) hl hs hw
  exact tmVerifierXOnlyWindowFixedMicroDomainCNFAt_satisfies_wellFormed_of_microTime
    V x t w 0 a hWindow (tmVerifierWindowMicroTimeRange_zero_mem V w) k

theorem windowFinalDomain
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {t : Nat} (ht : t ∈ tmVerifierXOnlyTransitionTimeRange V x)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies
      (tmVerifierXOnlyStackCellDomainsCNFAt V x
        (tmVerifierXOnlyFixedMicroTime V x t w.actions.length) k) a := by
  have hWindow :
      CNF.Satisfies (tmVerifierXOnlyWindowFixedMicroDomainCNFAt V x t w) a :=
    tmVerifierXOnlyTransitionFixedMicroDomainCNFAt_satisfies_window V x t l s w a
      (E.transitionFixedMicroDomainRow t ht) hl hs hw
  exact tmVerifierXOnlyWindowFixedMicroDomainCNFAt_satisfies_domain_of_microTime V x t w
    w.actions.length a hWindow (tmVerifierWindowMicroTimeRange_final_mem V w) k

theorem windowAntecedents_true
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {t : Nat} (ht : t ∈ tmVerifierXOnlyTransitionTimeRange V x)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hLabel :
      (E.controlRow t (tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht)).label =
        some l)
    (hState :
      (E.controlRow t (tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht)).state =
        s)
    (hGuards : ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuards x t w, g.eval a = true) :
    ∀ g ∈ tmVerifierXOnlyWindowFixedAntecedents V x t l s w, g.eval a = true := by
  intro g hg
  have hLabelTrue :
      (tmVerifierLabelAtom V t (some l)).eval a = true := by
    simpa [hLabel] using
      (E.controlRow t
        (tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht)).label_true
  have hStateTrue : (tmVerifierStateAtom V t s).eval a = true := by
    simpa [hState] using
      (E.controlRow t
        (tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht)).state_true
  have hg' :
      g = tmVerifierLabelAtom V t (some l) ∨
        g = tmVerifierStateAtom V t s ∨
          g ∈ tmVerifierXOnlyWindowFixedActionReadGuards x t w := by
    simpa [tmVerifierXOnlyWindowFixedAntecedents] using hg
  rcases hg' with rfl | hRest
  · exact hLabelTrue
  · rcases hRest with rfl | hGuard
    · exact hStateTrue
    · exact hGuards g hGuard

theorem transitionWindowFiniteRowEffect
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {t : Nat} (ht : t ∈ tmVerifierXOnlyTransitionTimeRange V x)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (hLabel :
      (E.controlRow t (tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht)).label =
        some l)
    (hState :
      (E.controlRow t (tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht)).state =
        s)
    (hGuards : ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuards x t w, g.eval a = true) :
    TMVerifierXOnlyWindowFixedRowFiniteEffect V B x t l s w a
      (E.windowActionDomainEvidence ht hl hs hw) := by
  let antecedents := tmVerifierXOnlyWindowFixedAntecedents V x t l s w
  have hRow := E.transitionFixedRow t ht
  have hControl :
      CNF.Satisfies (tmVerifierXOnlyWindowFixedControlCNFAt V x t l s w) a := by
    have hsplit := (CNF.satisfies_append
      (tmVerifierXOnlyTransitionFixedControlCNFAt V x t)
      (tmVerifierXOnlyTransitionFixedWindowStackCNFAt V B x t ++
        tmVerifierXOnlyHaltedRowsCNFAt V x t) a).1
        (by simpa [tmVerifierXOnlyTransitionFixedRowCNFAt] using hRow)
    intro c hc
    exact hsplit.1 c (by
      rw [tmVerifierXOnlyTransitionFixedControlCNFAt]
      exact List.mem_flatMap.mpr
        ⟨l, hl, List.mem_flatMap.mpr ⟨s, hs, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩⟩)
  have hNextControl :
      (tmVerifierLabelAtom V (t + 1) w.nextLabel).eval a = true ∧
        (tmVerifierStateAtom V (t + 1) w.nextState).eval a = true := by
    have hAntecedents := E.windowAntecedents_true ht hLabel hState hGuards
    let antecedents := tmVerifierXOnlyWindowFixedAntecedents V x t l s w
    have hLabelCNF :
        CNF.Satisfies
          [tmVerifierImplicationClause antecedents
            (tmVerifierLabelAtom V (t + 1) w.nextLabel)] a := by
      intro c hc
      have hc' :
          c = tmVerifierImplicationClause antecedents
            (tmVerifierLabelAtom V (t + 1) w.nextLabel) := by
        simpa using hc
      subst c
      exact hControl _ (by simp [tmVerifierXOnlyWindowFixedControlCNFAt, antecedents])
    have hStateCNF :
        CNF.Satisfies
          [tmVerifierImplicationClause antecedents
            (tmVerifierStateAtom V (t + 1) w.nextState)] a := by
      intro c hc
      have hc' :
          c = tmVerifierImplicationClause antecedents
            (tmVerifierStateAtom V (t + 1) w.nextState) := by
        simpa using hc
      subst c
      exact hControl _ (by simp [tmVerifierXOnlyWindowFixedControlCNFAt, antecedents])
    constructor
    · exact tmVerifierImplicationClause_satisfies_of_antecedents antecedents
        (tmVerifierLabelAtom V (t + 1) w.nextLabel) a hLabelCNF (by
          simpa [antecedents] using hAntecedents)
    · exact tmVerifierImplicationClause_satisfies_of_antecedents antecedents
        (tmVerifierStateAtom V (t + 1) w.nextState) a hStateCNF (by
          simpa [antecedents] using hAntecedents)
  have hStack :
      CNF.Satisfies
        (tmVerifierXOnlyWindowFixedStackActionCNFAt V B x t w
          (tmVerifierXOnlyWindowFixedAntecedents V x t l s w)) a := by
    have hsplit := (CNF.satisfies_append
      (tmVerifierXOnlyTransitionFixedControlCNFAt V x t)
      (tmVerifierXOnlyTransitionFixedWindowStackCNFAt V B x t ++
        tmVerifierXOnlyHaltedRowsCNFAt V x t) a).1
        (by simpa [tmVerifierXOnlyTransitionFixedRowCNFAt] using hRow)
    have hstack := (CNF.satisfies_append
      (tmVerifierXOnlyTransitionFixedWindowStackCNFAt V B x t)
      (tmVerifierXOnlyHaltedRowsCNFAt V x t) a).1 hsplit.2 |>.1
    exact tmVerifierXOnlyTransitionFixedWindowStackCNFAt_satisfies_window V B x t l s w a
      hstack hl hs hw
  refine ⟨hNextControl.1, hNextControl.2, ?_⟩
  intro entry hentry
  have hAction :
      CNF.Satisfies
        (tmVerifierXOnlyStackActionCNFBetween V B x
          (tmVerifierXOnlyFixedMicroTime V x t entry.2)
          (tmVerifierXOnlyFixedMicroTime V x t (entry.2 + 1))
          (tmVerifierXOnlyWindowFixedAntecedents V x t l s w) entry.1) a :=
    tmVerifierXOnlyWindowFixedStackActionCNFAt_satisfies_action V B x t w
      (tmVerifierXOnlyWindowFixedAntecedents V x t l s w) a hStack entry hentry
  exact tmVerifierXOnlyStackActionCNFBetween_satisfies_fixed_boundary_effect V B x t
    entry.2 (tmVerifierXOnlyWindowFixedAntecedents V x t l s w) a entry.1 hAction
    ((E.windowActionDomainEvidence ht hl hs hw) entry hentry).1
    ((E.windowActionDomainEvidence ht hl hs hw) entry hentry).2
    (E.windowAntecedents_true ht hLabel hState hGuards)

theorem transitionWindowFiniteReads
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {t : Nat} (ht : t ∈ tmVerifierXOnlyTransitionTimeRange V x)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (hLabel :
      (E.controlRow t (tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht)).label =
        some l)
    (hState :
      (E.controlRow t (tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht)).state =
        s)
    (hGuards : ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuards x t w, g.eval a = true) :
    TMVerifierXOnlyWindowFixedStackReadsFinite V x t w a
      (E.windowActionDomainEvidence ht hl hs hw) := by
  let antecedents := tmVerifierXOnlyWindowFixedAntecedents V x t l s w
  have hRow := E.transitionFixedRow t ht
  have hStack :
      CNF.Satisfies
        (tmVerifierXOnlyWindowFixedStackActionCNFAt V B x t w
          (tmVerifierXOnlyWindowFixedAntecedents V x t l s w)) a := by
    have hsplit := (CNF.satisfies_append
      (tmVerifierXOnlyTransitionFixedControlCNFAt V x t)
      (tmVerifierXOnlyTransitionFixedWindowStackCNFAt V B x t ++
        tmVerifierXOnlyHaltedRowsCNFAt V x t) a).1
        (by simpa [tmVerifierXOnlyTransitionFixedRowCNFAt] using hRow)
    have hstack := (CNF.satisfies_append
      (tmVerifierXOnlyTransitionFixedWindowStackCNFAt V B x t)
      (tmVerifierXOnlyHaltedRowsCNFAt V x t) a).1 hsplit.2 |>.1
    exact tmVerifierXOnlyTransitionFixedWindowStackCNFAt_satisfies_window V B x t l s w a
      hstack hl hs hw
  intro entry hentry
  have hAction :
      CNF.Satisfies
        (tmVerifierXOnlyStackActionCNFBetween V B x
          (tmVerifierXOnlyFixedMicroTime V x t entry.2)
          (tmVerifierXOnlyFixedMicroTime V x t (entry.2 + 1))
          (tmVerifierXOnlyWindowFixedAntecedents V x t l s w) entry.1) a :=
    tmVerifierXOnlyWindowFixedStackActionCNFAt_satisfies_action V B x t w
      (tmVerifierXOnlyWindowFixedAntecedents V x t l s w) a hStack entry hentry
  exact tmVerifierXOnlyStackActionCNFBetween_satisfies_fixed_boundary_read V B x t
    entry.2 (tmVerifierXOnlyWindowFixedAntecedents V x t l s w) a entry.1 hAction
    ((E.windowActionDomainEvidence ht hl hs hw) entry hentry).1
    (E.windowAntecedents_true ht hLabel hState hGuards)
    (tmVerifierStmtWindowsAt_zipIdx_action_readChoiceMem V t ((tmVerifierTM V).m l) s hw
      entry hentry)

theorem transitionWindowActionsMatchDecodedStackListsFrom
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {t : Nat} (ht : t ∈ tmVerifierXOnlyTransitionTimeRange V x)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (hLabel :
      (E.controlRow t (tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht)).label =
        some l)
    (hState :
      (E.controlRow t (tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht)).state =
        s)
    (hGuards : ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuards x t w, g.eval a = true) :
    tmVerifierWindowActionsMatchStacks w.actions
      (fun k => tmVerifierXOnlyDecodedStackList V x
        (tmVerifierXOnlyFixedMicroTime V x t 0) k a (E.windowStartDomain ht hl hs hw k)) := by
  have hEff := E.transitionWindowFiniteRowEffect ht hl hs hw hLabel hState hGuards
  have hPush :
      ∀ entry, ∀ _hentry : entry ∈ w.actions.zipIdx,
        TMVerifierStackActionPushSymbolMem (V := V) entry.1 := by
    intro entry hentry
    exact tmVerifierStmtWindowsAt_zipIdx_action_pushSymbolMem_of_label V t l s hw entry hentry
  exact TMVerifierXOnlyWindowFixedRowFiniteEffect.actionsMatch_decodedStackListsFrom hEff
    (E.transitionWindowFiniteReads ht hl hs hw hLabel hState hGuards)
    (E.windowActionWellFormedEvidence ht hl hs hw) hPush
    (E.windowStartDomain ht hl hs hw) (E.windowStartWellFormed ht hl hs hw)

theorem transitionWindowInputStackLists_eq_windowStart
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {t : Nat} (ht : t ∈ tmVerifierXOnlyTransitionTimeRange V x)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (hLabel :
      (E.controlRow t (tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht)).label =
        some l)
    (hState :
      (E.controlRow t (tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht)).state =
        s)
    (hGuards : ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuards x t w, g.eval a = true) :
    (fun k => tmVerifierXOnlyDecodedStackList V x (tmVerifierXOnlyFixedMicroTime V x t 0) k a
      (E.windowStartDomain ht hl hs hw k)) =
      (fun k => tmVerifierXOnlyDecodedStackList V x t k a
        (E.transitionStackCellDomainsAt ht k)) := by
  have hBoundary :
      CNF.Satisfies (tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V x t l s w) a :=
    tmVerifierXOnlyTransitionFixedRowCNFAt_satisfies_window_boundary V B x t l s w a
      (E.transitionFixedRow t ht) hl hs hw
  have hAntecedents := E.windowAntecedents_true ht hLabel hState hGuards
  funext k
  exact TMVerifierXOnlyDecodedFramePrefixEffect.decodedStackList_eq
    (tmVerifierXOnlyWindowFixedStackBoundaryCNFAt_satisfies_input_frame V x t l s w a
      hBoundary hAntecedents k (E.transitionStackCellDomainsAt ht k)
      (E.windowStartDomain ht hl hs hw k))

theorem transitionWindowOutputStackLists_eq_windowFinal
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {t : Nat} (ht : t ∈ tmVerifierXOnlyTransitionTimeRange V x)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (hLabel :
      (E.controlRow t (tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht)).label =
        some l)
    (hState :
      (E.controlRow t (tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht)).state =
        s)
    (hGuards : ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuards x t w, g.eval a = true) :
    (fun k => tmVerifierXOnlyDecodedStackList V x (t + 1) k a
      (E.stackCellDomainsAt (t + 1)
        (tmVerifierXOnlyTransitionTimeRange_succ_mem_tableauTimeRange V x ht) k)) =
      (fun k => tmVerifierXOnlyDecodedStackList V x
        (tmVerifierXOnlyFixedMicroTime V x t w.actions.length) k a
        (E.windowFinalDomain ht hl hs hw k)) := by
  have hBoundary :
      CNF.Satisfies (tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V x t l s w) a :=
    tmVerifierXOnlyTransitionFixedRowCNFAt_satisfies_window_boundary V B x t l s w a
      (E.transitionFixedRow t ht) hl hs hw
  have hAntecedents := E.windowAntecedents_true ht hLabel hState hGuards
  funext k
  exact TMVerifierXOnlyDecodedFramePrefixEffect.decodedStackList_eq
    (tmVerifierXOnlyWindowFixedStackBoundaryCNFAt_satisfies_output_frame V x t l s w a
      hBoundary hAntecedents k (E.windowFinalDomain ht hl hs hw k)
      (E.stackCellDomainsAt (t + 1)
        (tmVerifierXOnlyTransitionTimeRange_succ_mem_tableauTimeRange V x ht) k))

theorem transitionWindowActionsApply_eq_windowFinal
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {t : Nat} (ht : t ∈ tmVerifierXOnlyTransitionTimeRange V x)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (hLabel :
      (E.controlRow t (tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht)).label =
        some l)
    (hState :
      (E.controlRow t (tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht)).state =
        s)
    (hGuards : ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuards x t w, g.eval a = true) :
    tmVerifierWindowActionsApplyStacks w.actions
      (fun k => tmVerifierXOnlyDecodedStackList V x (tmVerifierXOnlyFixedMicroTime V x t 0) k a
        (E.windowStartDomain ht hl hs hw k)) =
      (fun k => tmVerifierXOnlyDecodedStackList V x
        (tmVerifierXOnlyFixedMicroTime V x t w.actions.length) k a
        (E.windowFinalDomain ht hl hs hw k)) := by
  have hEff := E.transitionWindowFiniteRowEffect ht hl hs hw hLabel hState hGuards
  have hPush :
      ∀ entry, ∀ _hentry : entry ∈ w.actions.zipIdx,
        TMVerifierStackActionPushSymbolMem (V := V) entry.1 := by
    intro entry hentry
    exact tmVerifierStmtWindowsAt_zipIdx_action_pushSymbolMem_of_label V t l s hw entry hentry
  exact TMVerifierXOnlyWindowFixedRowFiniteEffect.actionsApply_eq_decodedFinalFrom hEff
    (E.windowActionWellFormedEvidence ht hl hs hw) hPush
    (E.windowStartDomain ht hl hs hw) (E.windowStartWellFormed ht hl hs hw)
    (E.windowFinalDomain ht hl hs hw)

theorem transitionWindowFiniteStepAuxMacroRow
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {t : Nat} (ht : t ∈ tmVerifierXOnlyTransitionTimeRange V x)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (hLabel :
      (E.controlRow t (tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht)).label =
        some l)
    (hState :
      (E.controlRow t (tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht)).state =
        s)
    (hGuards : ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuards x t w, g.eval a = true) :
    (tmVerifierLabelAtom V (t + 1)
        (Turing.TM2.stepAux ((tmVerifierTM V).m l) s
          (fun k => tmVerifierXOnlyDecodedStackList V x t k a
            (E.transitionStackCellDomainsAt ht k))).l).eval a = true ∧
      (tmVerifierStateAtom V (t + 1)
        (Turing.TM2.stepAux ((tmVerifierTM V).m l) s
          (fun k => tmVerifierXOnlyDecodedStackList V x t k a
            (E.transitionStackCellDomainsAt ht k))).var).eval a = true ∧
        (fun k => tmVerifierXOnlyDecodedStackList V x (t + 1) k a
          (E.stackCellDomainsAt (t + 1)
            (tmVerifierXOnlyTransitionTimeRange_succ_mem_tableauTimeRange V x ht) k)) =
          (Turing.TM2.stepAux ((tmVerifierTM V).m l) s
            (fun k => tmVerifierXOnlyDecodedStackList V x t k a
              (E.transitionStackCellDomainsAt ht k))).stk := by
  let macroStacks :=
    fun k => tmVerifierXOnlyDecodedStackList V x t k a (E.transitionStackCellDomainsAt ht k)
  let startStacks :=
    fun k => tmVerifierXOnlyDecodedStackList V x (tmVerifierXOnlyFixedMicroTime V x t 0) k a
      (E.windowStartDomain ht hl hs hw k)
  let finalStacks :=
    fun k => tmVerifierXOnlyDecodedStackList V x
      (tmVerifierXOnlyFixedMicroTime V x t w.actions.length) k a
      (E.windowFinalDomain ht hl hs hw k)
  let outStacks :=
    fun k => tmVerifierXOnlyDecodedStackList V x (t + 1) k a
      (E.stackCellDomainsAt (t + 1)
        (tmVerifierXOnlyTransitionTimeRange_succ_mem_tableauTimeRange V x ht) k)
  have hInput : startStacks = macroStacks :=
    E.transitionWindowInputStackLists_eq_windowStart ht hl hs hw hLabel hState hGuards
  have hOutput : outStacks = finalStacks :=
    E.transitionWindowOutputStackLists_eq_windowFinal ht hl hs hw hLabel hState hGuards
  have hApply : tmVerifierWindowActionsApplyStacks w.actions startStacks = finalStacks :=
    E.transitionWindowActionsApply_eq_windowFinal ht hl hs hw hLabel hState hGuards
  have hEff := E.transitionWindowFiniteRowEffect ht hl hs hw hLabel hState hGuards
  have hStep :=
    hEff.stepAux_next_control hw
      (E.transitionWindowActionsMatchDecodedStackListsFrom ht hl hs hw hLabel hState hGuards)
  refine ⟨?_, ?_, ?_⟩
  · simpa [macroStacks, startStacks, hInput] using hStep.1
  · simpa [macroStacks, startStacks, hInput] using hStep.2.1
  · calc
      outStacks = finalStacks := hOutput
      _ = tmVerifierWindowActionsApplyStacks w.actions startStacks := hApply.symm
      _ = (Turing.TM2.stepAux ((tmVerifierTM V).m l) s startStacks).stk := hStep.2.2
      _ = (Turing.TM2.stepAux ((tmVerifierTM V).m l) s macroStacks).stk := by
        simp [hInput]

end TMVerifierXOnlyGlobalTableauEvidence

end SAT
end ComplexityReduction
