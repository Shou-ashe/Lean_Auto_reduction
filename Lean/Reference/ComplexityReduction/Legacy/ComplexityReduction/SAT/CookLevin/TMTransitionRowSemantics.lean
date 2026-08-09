/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMStackListEffects

/-!
Aggregate transition-row effect surface.

This file is the first layer above primitive action clauses.  It bundles the
control consequences of one statement window with the decoded-prefix effects of
each recorded micro action in that window.  It still does not claim a complete
`TM2.step` theorem: stack-domain rows are supplied as hypotheses, and the result
is an auditable row-effect boundary for later operational alignment.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Primitive action effects -/

noncomputable def TMVerifierStackActionEffect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t actionIdx : Nat)
    (_antecedents : List Literal) (a : Assignment)
    (hDomains :
      ∀ micro (k : tmVerifierStackIndex V),
        CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t micro) k) a) :
    TMVerifierStackAction V → Prop
  | TMVerifierStackAction.push raw =>
      (∀ _hraw : raw ∈ tmVerifierControlPushSymbols V,
        TMVerifierDecodedPushPrefixEffect V B p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          raw a (hDomains actionIdx raw.stack) (hDomains (actionIdx + 1) raw.stack)) ∧
      (∀ j, j ∈ tmVerifierOtherStacks V raw.stack →
        TMVerifierDecodedFramePrefixEffect V p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          j a (hDomains actionIdx j) (hDomains (actionIdx + 1) j))
  | TMVerifierStackAction.pop k _ =>
      TMVerifierDecodedPopPrefixEffect V p
        (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
        k a (hDomains actionIdx k) (hDomains (actionIdx + 1) k) ∧
      (∀ j, j ∈ tmVerifierOtherStacks V k →
        TMVerifierDecodedFramePrefixEffect V p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          j a (hDomains actionIdx j) (hDomains (actionIdx + 1) j))
  | TMVerifierStackAction.peek _ _ =>
      ∀ k, k ∈ tmVerifierStackList V →
        TMVerifierDecodedFramePrefixEffect V p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          k a (hDomains actionIdx k) (hDomains (actionIdx + 1) k)
  | TMVerifierStackAction.load =>
      ∀ k, k ∈ tmVerifierStackList V →
        TMVerifierDecodedFramePrefixEffect V p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          k a (hDomains actionIdx k) (hDomains (actionIdx + 1) k)
  | TMVerifierStackAction.branch _ =>
      ∀ k, k ∈ tmVerifierStackList V →
        TMVerifierDecodedFramePrefixEffect V p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          k a (hDomains actionIdx k) (hDomains (actionIdx + 1) k)

theorem tmVerifierStackActionEffectCNFBetween_satisfies_effect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t actionIdx : Nat)
    (antecedents : List Literal) (a : Assignment)
    (act : TMVerifierStackAction V)
    (hEffect :
      CNF.Satisfies
        (tmVerifierStackActionEffectCNFBetween V B p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          antecedents act) a)
    (hDomains :
      ∀ micro (k : tmVerifierStackIndex V),
        CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t micro) k) a)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    TMVerifierStackActionEffect V B p t actionIdx antecedents a hDomains act := by
  cases act with
  | push raw =>
      constructor
      · intro hraw
        exact tmVerifierPushActionCNFBetween_decoded_prefix_effect V B p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          raw antecedents a (by simpa [tmVerifierStackActionEffectCNFBetween] using hEffect)
          (hDomains actionIdx raw.stack) (hDomains (actionIdx + 1) raw.stack) hraw
          hAntecedents
      · intro j hj cell hcell
        exact tmVerifierPushActionCNFBetween_decoded_other_stack_choice_eq V B p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          raw j cell antecedents a (by simpa [tmVerifierStackActionEffectCNFBetween] using hEffect)
          (hDomains actionIdx j) (hDomains (actionIdx + 1) j) hj hcell hAntecedents
  | pop k choice =>
      constructor
      · exact tmVerifierPopActionCNFBetween_decoded_prefix_effect V p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          k antecedents a (by simpa [tmVerifierStackActionEffectCNFBetween] using hEffect)
          (hDomains actionIdx k) (hDomains (actionIdx + 1) k) hAntecedents
      · intro j hj cell hcell
        exact tmVerifierPopActionCNFBetween_decoded_other_stack_choice_eq V p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          k j cell antecedents a (by simpa [tmVerifierStackActionEffectCNFBetween] using hEffect)
          (hDomains actionIdx j) (hDomains (actionIdx + 1) j) hj hcell hAntecedents
  | peek k choice =>
      intro j hj
      exact tmVerifierPreserveAllStacksActionCNFBetween_decoded_prefix_effect V p
        (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
        j antecedents a (by simpa [tmVerifierStackActionEffectCNFBetween] using hEffect)
        (hDomains actionIdx j) (hDomains (actionIdx + 1) j) hj hAntecedents
  | load =>
      intro j hj
      exact tmVerifierPreserveAllStacksActionCNFBetween_decoded_prefix_effect V p
        (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
        j antecedents a (by simpa [tmVerifierStackActionEffectCNFBetween] using hEffect)
        (hDomains actionIdx j) (hDomains (actionIdx + 1) j) hj hAntecedents
  | branch tag =>
      intro j hj
      exact tmVerifierPreserveAllStacksActionCNFBetween_decoded_prefix_effect V p
        (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
        j antecedents a (by simpa [tmVerifierStackActionEffectCNFBetween] using hEffect)
        (hDomains actionIdx j) (hDomains (actionIdx + 1) j) hj hAntecedents

theorem tmVerifierStackActionCNFBetween_satisfies_effect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t actionIdx : Nat)
    (antecedents : List Literal) (a : Assignment)
    (act : TMVerifierStackAction V)
    (hAction :
      CNF.Satisfies
        (tmVerifierStackActionCNFBetween V B p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          antecedents act) a)
    (hDomains :
      ∀ micro (k : tmVerifierStackIndex V),
        CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t micro) k) a)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    TMVerifierStackActionEffect V B p t actionIdx antecedents a hDomains act :=
  tmVerifierStackActionEffectCNFBetween_satisfies_effect V B p t actionIdx antecedents a act
    (tmVerifierStackActionCNFBetween_satisfies_effect_cnf V B p
      (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
      antecedents act a hAction)
    hDomains hAntecedents

/-! ### Window stack-action effects -/

theorem tmVerifierWindowStackActionCNFAt_satisfies_action
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (antecedents : List Literal)
    (a : Assignment)
    (h :
      CNF.Satisfies (tmVerifierWindowStackActionCNFAt V B p t w antecedents) a)
    (entry : TMVerifierStackAction V × Nat)
    (hentry : entry ∈ w.actions.zipIdx) :
    CNF.Satisfies
      (tmVerifierStackActionCNFBetween V B p
        (tmVerifierMicroTime t entry.2) (tmVerifierMicroTime t (entry.2 + 1))
        antecedents entry.1) a := by
  intro c hc
  exact h c (by
    rw [tmVerifierWindowStackActionCNFAt]
    exact List.mem_flatMap.mpr ⟨entry, hentry, hc⟩)

noncomputable def TMVerifierWindowStackEffects
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (antecedents : List Literal)
    (a : Assignment)
    (hDomains :
      ∀ micro (k : tmVerifierStackIndex V),
        CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t micro) k) a) :
    Prop :=
  ∀ entry, ∀ _hentry : entry ∈ w.actions.zipIdx,
    TMVerifierStackActionEffect V B p t entry.2 antecedents a hDomains entry.1

theorem tmVerifierWindowStackActionCNFAt_satisfies_effects
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (antecedents : List Literal)
    (a : Assignment)
    (h :
      CNF.Satisfies (tmVerifierWindowStackActionCNFAt V B p t w antecedents) a)
    (hDomains :
      ∀ micro (k : tmVerifierStackIndex V),
        CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t micro) k) a)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    TMVerifierWindowStackEffects V B p t w antecedents a hDomains := by
  intro entry hentry
  exact tmVerifierStackActionCNFBetween_satisfies_effect V B p t entry.2 antecedents a
    entry.1
    (tmVerifierWindowStackActionCNFAt_satisfies_action V B p t w antecedents a h entry hentry)
    hDomains hAntecedents

/-! ### Aggregate transition-window and row effects -/

noncomputable def TMVerifierWindowRowEffect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (hDomains :
      ∀ micro (k : tmVerifierStackIndex V),
        CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t micro) k) a) :
    Prop :=
  (tmVerifierLabelAtom V (t + 1) w.nextLabel).eval a = true ∧
  (tmVerifierStateAtom V (t + 1) w.nextState).eval a = true ∧
  TMVerifierWindowStackEffects V B p t w (tmVerifierWindowAntecedents V t l s w) a hDomains

noncomputable def tmVerifierTransitionWindowCNFAt
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) : CNF :=
  tmVerifierWindowControlCNFAt V t l s w ++
    tmVerifierWindowStackActionCNFAt V B p t w (tmVerifierWindowAntecedents V t l s w)

/--
Stack-frame clauses connecting the macro input/output rows of a transition to
the first and final micro rows of a selected statement window.
-/
noncomputable def tmVerifierWindowStackBoundaryCNFAt
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) : CNF :=
  let antecedents := tmVerifierWindowAntecedents V t l s w
  tmVerifierFrameAllStacksCNFBetween V p t (tmVerifierMicroTime t 0) antecedents ++
    tmVerifierFrameAllStacksCNFBetween V p (tmVerifierMicroTime t w.actions.length)
      (t + 1) antecedents

theorem tmVerifierTransitionWindowCNFAt_satisfies_effect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierTransitionWindowCNFAt V B p t l s w) a)
    (hDomains :
      ∀ micro (k : tmVerifierStackIndex V),
        CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t micro) k) a)
    (hAntecedents :
      ∀ g ∈ tmVerifierWindowAntecedents V t l s w, g.eval a = true) :
    TMVerifierWindowRowEffect V B p t l s w a hDomains := by
  have hsplit := (CNF.satisfies_append
    (tmVerifierWindowControlCNFAt V t l s w)
    (tmVerifierWindowStackActionCNFAt V B p t w (tmVerifierWindowAntecedents V t l s w))
    a).1 (by simpa [tmVerifierTransitionWindowCNFAt] using h)
  have hControl :=
    tmVerifierWindowControlCNFAt_satisfies_next_control V t l s w a hsplit.1
      hAntecedents
  exact ⟨hControl.1, hControl.2,
    tmVerifierWindowStackActionCNFAt_satisfies_effects V B p t w
      (tmVerifierWindowAntecedents V t l s w) a hsplit.2 hDomains hAntecedents⟩

noncomputable def tmVerifierTransitionWindowStackCNFAt
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) : CNF :=
  (tmVerifierLabelList V).flatMap fun l =>
    (tmVerifierStateList V).flatMap fun s =>
      (tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s).flatMap fun w =>
        tmVerifierWindowStackBoundaryCNFAt V p t l s w ++
          tmVerifierWindowStackActionCNFAt V B p t w (tmVerifierWindowAntecedents V t l s w)

/-- Antecedents for the halted-row padding clauses. -/
noncomputable def tmVerifierHaltedRowAntecedents {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) (s : (tmVerifierTM V).σ) : List Literal :=
  [tmVerifierLabelAtom V t none, tmVerifierStateAtom V t s]

/--
Padding clauses for a row whose decoded label is already halted.

The transition-window clauses only enumerate nonhalting labels.  These clauses
make halted rows persistent so a tableau cannot halt early and then arbitrarily
rewrite the final accepting row.
-/
noncomputable def tmVerifierHaltedRowCNFAt {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (s : (tmVerifierTM V).σ) : CNF :=
  let antecedents := tmVerifierHaltedRowAntecedents V t s
  [ tmVerifierImplicationClause antecedents (tmVerifierLabelAtom V (t + 1) none)
  , tmVerifierImplicationClause antecedents (tmVerifierStateAtom V (t + 1) s)
  ] ++
    tmVerifierFrameAllStacksCNFBetween V p t (t + 1) antecedents

/-- Halted-row padding clauses for every finite internal state. -/
noncomputable def tmVerifierHaltedRowsCNFAt {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) : CNF :=
  (tmVerifierStateList V).flatMap fun s =>
    tmVerifierHaltedRowCNFAt V p t s

noncomputable def tmVerifierTransitionRowCNFAt
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) : CNF :=
  tmVerifierTransitionControlCNFAt V t ++
    tmVerifierTransitionWindowStackCNFAt V B p t ++
      tmVerifierHaltedRowsCNFAt V p t

theorem tmVerifierTransitionControlCNFAt_satisfies_window
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierTransitionControlCNFAt V t) a)
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s) :
    CNF.Satisfies (tmVerifierWindowControlCNFAt V t l s w) a := by
  intro c hc
  exact h c (by
    simp [tmVerifierTransitionControlCNFAt]
    exact ⟨l, hl, s, hs, w, hw, hc⟩)

theorem tmVerifierTransitionWindowStackCNFAt_satisfies_window
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierTransitionWindowStackCNFAt V B p t) a)
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s) :
  CNF.Satisfies
      (tmVerifierWindowStackActionCNFAt V B p t w
        (tmVerifierWindowAntecedents V t l s w)) a := by
  intro c hc
  exact h c (by
    simp [tmVerifierTransitionWindowStackCNFAt]
    exact ⟨l, hl, s, hs, w, hw, by simp [hc]⟩)

theorem tmVerifierTransitionWindowStackCNFAt_satisfies_window_boundary
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierTransitionWindowStackCNFAt V B p t) a)
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s) :
    CNF.Satisfies (tmVerifierWindowStackBoundaryCNFAt V p t l s w) a := by
  intro c hc
  exact h c (by
    simp [tmVerifierTransitionWindowStackCNFAt]
    exact ⟨l, hl, s, hs, w, hw, by simp [hc]⟩)

theorem tmVerifierHaltedRowsCNFAt_satisfies_state
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (s : (tmVerifierTM V).σ) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierHaltedRowsCNFAt V p t) a)
    (hs : s ∈ tmVerifierStateList V) :
    CNF.Satisfies (tmVerifierHaltedRowCNFAt V p t s) a := by
  intro c hc
  exact h c (by
    rw [tmVerifierHaltedRowsCNFAt]
    exact List.mem_flatMap.mpr ⟨s, hs, hc⟩)

theorem tmVerifierHaltedRowCNFAt_satisfies_next_control
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (s : (tmVerifierTM V).σ) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierHaltedRowCNFAt V p t s) a)
    (hAntecedents :
      ∀ g ∈ tmVerifierHaltedRowAntecedents V t s, g.eval a = true) :
    (tmVerifierLabelAtom V (t + 1) none).eval a = true ∧
      (tmVerifierStateAtom V (t + 1) s).eval a = true := by
  let antecedents := tmVerifierHaltedRowAntecedents V t s
  have hsplit := (CNF.satisfies_append
    ([ tmVerifierImplicationClause antecedents (tmVerifierLabelAtom V (t + 1) none)
     , tmVerifierImplicationClause antecedents (tmVerifierStateAtom V (t + 1) s) ])
    (tmVerifierFrameAllStacksCNFBetween V p t (t + 1) antecedents) a).1
      (by simpa [tmVerifierHaltedRowCNFAt, antecedents] using h)
  constructor
  · exact tmVerifierImplicationClause_satisfies_of_antecedents antecedents
      (tmVerifierLabelAtom V (t + 1) none) a
      (by
        intro c hc
        have hc' :
            c = tmVerifierImplicationClause antecedents
              (tmVerifierLabelAtom V (t + 1) none) := by
          simpa using hc
        subst c
        exact hsplit.1 _ (by simp))
      (by simpa [antecedents] using hAntecedents)
  · exact tmVerifierImplicationClause_satisfies_of_antecedents antecedents
      (tmVerifierStateAtom V (t + 1) s) a
      (by
        intro c hc
        have hc' :
            c = tmVerifierImplicationClause antecedents
              (tmVerifierStateAtom V (t + 1) s) := by
          simpa using hc
        subst c
        exact hsplit.1 _ (by simp))
      (by simpa [antecedents] using hAntecedents)

theorem tmVerifierHaltedRowCNFAt_satisfies_frame
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (s : (tmVerifierTM V).σ) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierHaltedRowCNFAt V p t s) a)
    (hAntecedents :
      ∀ g ∈ tmVerifierHaltedRowAntecedents V t s, g.eval a = true)
    (k : tmVerifierStackIndex V)
    (hIn : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a)
    (hOut : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p (t + 1) k) a) :
    TMVerifierDecodedFramePrefixEffect V p t (t + 1) k a hIn hOut := by
  let antecedents := tmVerifierHaltedRowAntecedents V t s
  have hsplit := (CNF.satisfies_append
    ([ tmVerifierImplicationClause antecedents (tmVerifierLabelAtom V (t + 1) none)
     , tmVerifierImplicationClause antecedents (tmVerifierStateAtom V (t + 1) s) ])
    (tmVerifierFrameAllStacksCNFBetween V p t (t + 1) antecedents) a).1
      (by simpa [tmVerifierHaltedRowCNFAt, antecedents] using h)
  exact tmVerifierPreserveAllStacksActionCNFBetween_decoded_prefix_effect V p t
    (t + 1) k antecedents a
    (by simpa [tmVerifierPreserveAllStacksActionCNFBetween] using hsplit.2)
    hIn hOut (by
      classical
      simp [tmVerifierStackList]) (by
      simpa [antecedents] using hAntecedents)

theorem tmVerifierTransitionRowCNFAt_satisfies_window_boundary
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierTransitionRowCNFAt V B p t) a)
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s) :
    CNF.Satisfies (tmVerifierWindowStackBoundaryCNFAt V p t l s w) a := by
  have hsplit := (CNF.satisfies_append
    (tmVerifierTransitionControlCNFAt V t)
    (tmVerifierTransitionWindowStackCNFAt V B p t ++
      tmVerifierHaltedRowsCNFAt V p t) a).1
      (by simpa [tmVerifierTransitionRowCNFAt] using h)
  have hstack := (CNF.satisfies_append
    (tmVerifierTransitionWindowStackCNFAt V B p t)
    (tmVerifierHaltedRowsCNFAt V p t) a).1 hsplit.2 |>.1
  exact tmVerifierTransitionWindowStackCNFAt_satisfies_window_boundary V B p t l s w a
    hstack hl hs hw

theorem tmVerifierWindowStackBoundaryCNFAt_satisfies_input_frame
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierWindowStackBoundaryCNFAt V p t l s w) a)
    (hAntecedents :
      ∀ g ∈ tmVerifierWindowAntecedents V t l s w, g.eval a = true)
    (k : tmVerifierStackIndex V)
    (hIn : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a)
    (hOut :
      CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t 0) k) a) :
    TMVerifierDecodedFramePrefixEffect V p t (tmVerifierMicroTime t 0) k a hIn hOut := by
  have hsplit := (CNF.satisfies_append
    (tmVerifierFrameAllStacksCNFBetween V p t (tmVerifierMicroTime t 0)
      (tmVerifierWindowAntecedents V t l s w))
    (tmVerifierFrameAllStacksCNFBetween V p (tmVerifierMicroTime t w.actions.length)
      (t + 1) (tmVerifierWindowAntecedents V t l s w)) a).1
      (by simpa [tmVerifierWindowStackBoundaryCNFAt] using h)
  exact tmVerifierPreserveAllStacksActionCNFBetween_decoded_prefix_effect V p t
    (tmVerifierMicroTime t 0) k (tmVerifierWindowAntecedents V t l s w) a
    (by simpa [tmVerifierPreserveAllStacksActionCNFBetween] using hsplit.1)
    hIn hOut (by
      classical
      simp [tmVerifierStackList]) hAntecedents

theorem tmVerifierWindowStackBoundaryCNFAt_satisfies_output_frame
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierWindowStackBoundaryCNFAt V p t l s w) a)
    (hAntecedents :
      ∀ g ∈ tmVerifierWindowAntecedents V t l s w, g.eval a = true)
    (k : tmVerifierStackIndex V)
    (hIn :
      CNF.Satisfies
        (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t w.actions.length) k)
        a)
    (hOut : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p (t + 1) k) a) :
    TMVerifierDecodedFramePrefixEffect V p (tmVerifierMicroTime t w.actions.length)
      (t + 1) k a hIn hOut := by
  have hsplit := (CNF.satisfies_append
    (tmVerifierFrameAllStacksCNFBetween V p t (tmVerifierMicroTime t 0)
      (tmVerifierWindowAntecedents V t l s w))
    (tmVerifierFrameAllStacksCNFBetween V p (tmVerifierMicroTime t w.actions.length)
      (t + 1) (tmVerifierWindowAntecedents V t l s w)) a).1
      (by simpa [tmVerifierWindowStackBoundaryCNFAt] using h)
  exact tmVerifierPreserveAllStacksActionCNFBetween_decoded_prefix_effect V p
    (tmVerifierMicroTime t w.actions.length) (t + 1) k
    (tmVerifierWindowAntecedents V t l s w) a
    (by simpa [tmVerifierPreserveAllStacksActionCNFBetween] using hsplit.2)
    hIn hOut (by
      classical
      simp [tmVerifierStackList]) hAntecedents

theorem tmVerifierTransitionRowCNFAt_satisfies_window_effect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierTransitionRowCNFAt V B p t) a)
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (hDomains :
      ∀ micro (k : tmVerifierStackIndex V),
        CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t micro) k) a)
    (hAntecedents :
      ∀ g ∈ tmVerifierWindowAntecedents V t l s w, g.eval a = true) :
    TMVerifierWindowRowEffect V B p t l s w a hDomains := by
  have hsplit := (CNF.satisfies_append
    (tmVerifierTransitionControlCNFAt V t)
    (tmVerifierTransitionWindowStackCNFAt V B p t ++
      tmVerifierHaltedRowsCNFAt V p t) a).1
      (by simpa [tmVerifierTransitionRowCNFAt] using h)
  have hstack := (CNF.satisfies_append
    (tmVerifierTransitionWindowStackCNFAt V B p t)
    (tmVerifierHaltedRowsCNFAt V p t) a).1 hsplit.2 |>.1
  have hControl :=
    tmVerifierTransitionControlCNFAt_satisfies_window V t l s w a hsplit.1 hl hs hw
  have hStack :=
    tmVerifierTransitionWindowStackCNFAt_satisfies_window V B p t l s w a hstack hl hs hw
  exact tmVerifierTransitionWindowCNFAt_satisfies_effect V B p t l s w a
    (by
      rw [tmVerifierTransitionWindowCNFAt]
      exact (CNF.satisfies_append
        (tmVerifierWindowControlCNFAt V t l s w)
        (tmVerifierWindowStackActionCNFAt V B p t w
          (tmVerifierWindowAntecedents V t l s w)) a).2
        ⟨hControl, hStack⟩)
    hDomains hAntecedents

end SAT
end ComplexityReduction
