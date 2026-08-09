/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.TransitionRows

namespace ComplexityReduction
namespace SAT

/-! ### Transition-row aggregation outside the active control row -/

theorem tmVerifierLabelAtom_eval_stackFamilyAssignment_false_of_ne
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (t : Nat) (label : Option (tmVerifierTM V).Λ)
    (hlabel : label ≠ (tmVerifierRunCfgAt V p t).l) :
    (tmVerifierLabelAtom V t label).eval (tmVerifierStackFamilyAssignment V p stkAt) =
      false := by
  by_cases hEval :
      (tmVerifierLabelAtom V t label).eval (tmVerifierStackFamilyAssignment V p stkAt) =
        true
  · have hRun : label = (tmVerifierRunCfgAt V p t).l := by
      have hBoundary :
          (tmVerifierLabelAtom V t label).eval (tmVerifierControlBoundaryAssignment V p) =
            true := by
        simpa [tmVerifierLabelAtom_eval_stackFamilyAssignment_controlBoundary] using hEval
      exact (tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff V p t label).1 hBoundary
    exact False.elim (hlabel hRun)
  · cases h :
      (tmVerifierLabelAtom V t label).eval (tmVerifierStackFamilyAssignment V p stkAt) <;>
        simp [h] at hEval ⊢

theorem tmVerifierStateAtom_eval_stackFamilyAssignment_false_of_ne
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (t : Nat) (state : (tmVerifierTM V).σ)
    (hstate : state ≠ (tmVerifierRunCfgAt V p t).var) :
    (tmVerifierStateAtom V t state).eval (tmVerifierStackFamilyAssignment V p stkAt) =
      false := by
  by_cases hEval :
      (tmVerifierStateAtom V t state).eval (tmVerifierStackFamilyAssignment V p stkAt) =
        true
  · have hRun : state = (tmVerifierRunCfgAt V p t).var := by
      have hBoundary :
          (tmVerifierStateAtom V t state).eval (tmVerifierControlBoundaryAssignment V p) =
            true := by
        simpa [tmVerifierStateAtom_eval_stackFamilyAssignment_controlBoundary] using hEval
      exact (tmVerifierStateAtom_eval_controlBoundaryAssignment_iff V p t state).1 hBoundary
    exact False.elim (hstate hRun)
  · cases h :
      (tmVerifierStateAtom V t state).eval (tmVerifierStackFamilyAssignment V p stkAt) <;>
        simp [h] at hEval ⊢

theorem tmVerifierWindowAntecedents_label_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) :
    tmVerifierLabelAtom V t (some l) ∈ tmVerifierWindowAntecedents V t l s w := by
  simp [tmVerifierWindowAntecedents]

theorem tmVerifierWindowAntecedents_state_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) :
    tmVerifierStateAtom V t s ∈ tmVerifierWindowAntecedents V t l s w := by
  simp [tmVerifierWindowAntecedents]

theorem tmVerifierWindowStackCNF_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment) {ant : Literal}
    (hmem : ant ∈ tmVerifierWindowAntecedents V t l s w)
    (hAnt : ant.eval a = false) :
    CNF.Satisfies
      (tmVerifierWindowStackBoundaryCNFAt V p t l s w ++
        tmVerifierWindowStackActionCNFAt V B p t w
          (tmVerifierWindowAntecedents V t l s w)) a := by
  rw [CNF.satisfies_append]
  exact ⟨tmVerifierWindowStackBoundaryCNFAt_satisfies_of_false_antecedent V p t l s w a
      hmem hAnt,
    tmVerifierWindowStackActionCNFAt_satisfies_of_false_antecedent V B p t w
      (tmVerifierWindowAntecedents V t l s w) a hmem hAnt⟩

theorem tmVerifierTransitionControlCNFAt_satisfies_current_label_state
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hl : (tmVerifierRunCfgAt V p t).l = some l)
    (hs : (tmVerifierRunCfgAt V p t).var = s)
    (hCurrent :
      ∀ w : TMVerifierStmtWindow V,
        w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s →
          CNF.Satisfies (tmVerifierWindowControlCNFAt V t l s w)
            (tmVerifierStackFamilyAssignment V p stkAt)) :
    CNF.Satisfies (tmVerifierTransitionControlCNFAt V t)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  intro c hc
  rw [tmVerifierTransitionControlCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨l', _hl', hc⟩
  rcases List.mem_flatMap.mp hc with ⟨s', _hs', hc⟩
  rcases List.mem_flatMap.mp hc with ⟨w, hw, hc⟩
  by_cases hLabelEq : l' = l
  · subst l'
    by_cases hStateEq : s' = s
    · subst s'
      exact hCurrent w hw c hc
    · have hFalse :
          (tmVerifierStateAtom V t s').eval
              (tmVerifierStackFamilyAssignment V p stkAt) = false := by
        exact tmVerifierStateAtom_eval_stackFamilyAssignment_false_of_ne V p stkAt t s'
          (by
            intro h
            exact hStateEq (by simpa [hs] using h))
      exact tmVerifierWindowControlCNFAt_satisfies_of_false_antecedent V t l s' w
        (tmVerifierStackFamilyAssignment V p stkAt)
        (tmVerifierWindowAntecedents_state_mem V t l s' w) hFalse c hc
  · have hFalse :
        (tmVerifierLabelAtom V t (some l')).eval
            (tmVerifierStackFamilyAssignment V p stkAt) = false := by
      exact tmVerifierLabelAtom_eval_stackFamilyAssignment_false_of_ne V p stkAt t
        (some l') (by
          intro h
          exact hLabelEq (Option.some.inj (by simpa [hl] using h)))
    exact tmVerifierWindowControlCNFAt_satisfies_of_false_antecedent V t l' s' w
      (tmVerifierStackFamilyAssignment V p stkAt)
      (tmVerifierWindowAntecedents_label_mem V t l' s' w) hFalse c hc

theorem tmVerifierTransitionWindowStackCNFAt_satisfies_current_label_state
    {L : EncodedDecisionProblem} (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hl : (tmVerifierRunCfgAt V p t).l = some l)
    (hs : (tmVerifierRunCfgAt V p t).var = s)
    (hCurrent :
      ∀ w : TMVerifierStmtWindow V,
        w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s →
          CNF.Satisfies
            (tmVerifierWindowStackBoundaryCNFAt V p t l s w ++
              tmVerifierWindowStackActionCNFAt V B p t w
                (tmVerifierWindowAntecedents V t l s w))
            (tmVerifierStackFamilyAssignment V p stkAt)) :
    CNF.Satisfies (tmVerifierTransitionWindowStackCNFAt V B p t)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  intro c hc
  rw [tmVerifierTransitionWindowStackCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨l', _hl', hc⟩
  rcases List.mem_flatMap.mp hc with ⟨s', _hs', hc⟩
  rcases List.mem_flatMap.mp hc with ⟨w, hw, hc⟩
  by_cases hLabelEq : l' = l
  · subst l'
    by_cases hStateEq : s' = s
    · subst s'
      exact hCurrent w hw c hc
    · have hFalse :
          (tmVerifierStateAtom V t s').eval
              (tmVerifierStackFamilyAssignment V p stkAt) = false := by
        exact tmVerifierStateAtom_eval_stackFamilyAssignment_false_of_ne V p stkAt t s'
          (by
            intro h
            exact hStateEq (by simpa [hs] using h))
      exact tmVerifierWindowStackCNF_satisfies_of_false_antecedent V B p t l s' w
        (tmVerifierStackFamilyAssignment V p stkAt)
        (tmVerifierWindowAntecedents_state_mem V t l s' w) hFalse c hc
  · have hFalse :
        (tmVerifierLabelAtom V t (some l')).eval
            (tmVerifierStackFamilyAssignment V p stkAt) = false := by
      exact tmVerifierLabelAtom_eval_stackFamilyAssignment_false_of_ne V p stkAt t
        (some l') (by
          intro h
          exact hLabelEq (Option.some.inj (by simpa [hl] using h)))
    exact tmVerifierWindowStackCNF_satisfies_of_false_antecedent V B p t l' s' w
      (tmVerifierStackFamilyAssignment V p stkAt)
      (tmVerifierWindowAntecedents_label_mem V t l' s' w) hFalse c hc

theorem tmVerifierHaltedRowCNFAt_satisfies_of_nonhalting_label
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (s : (tmVerifierTM V).σ)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    {l : (tmVerifierTM V).Λ}
    (hl : (tmVerifierRunCfgAt V p t).l = some l) :
    CNF.Satisfies (tmVerifierHaltedRowCNFAt V p t s)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  let antecedents := tmVerifierHaltedRowAntecedents V t s
  have hFalse :
      (tmVerifierLabelAtom V t none).eval
          (tmVerifierStackFamilyAssignment V p stkAt) = false := by
    exact tmVerifierLabelAtom_eval_stackFamilyAssignment_false_of_ne V p stkAt t none
      (by
        intro h
        simp [hl] at h)
  have hmem : tmVerifierLabelAtom V t none ∈ antecedents := by
    simp [antecedents, tmVerifierHaltedRowAntecedents]
  rw [tmVerifierHaltedRowCNFAt]
  change CNF.Satisfies
    ([tmVerifierImplicationClause antecedents (tmVerifierLabelAtom V (t + 1) none),
      tmVerifierImplicationClause antecedents (tmVerifierStateAtom V (t + 1) s)] ++
        tmVerifierFrameAllStacksCNFBetween V p t (t + 1) antecedents)
      (tmVerifierStackFamilyAssignment V p stkAt)
  rw [CNF.satisfies_append]
  constructor
  · intro c hc
    have hc' :
        c = tmVerifierImplicationClause antecedents (tmVerifierLabelAtom V (t + 1) none) ∨
          c = tmVerifierImplicationClause antecedents (tmVerifierStateAtom V (t + 1) s) := by
      simpa using hc
    rcases hc' with rfl | rfl
    · exact tmVerifierImplicationClause_satisfies_of_false_antecedent antecedents
        (tmVerifierLabelAtom V (t + 1) none) (tmVerifierLabelAtom V t none)
        (tmVerifierStackFamilyAssignment V p stkAt) hmem hFalse
    · exact tmVerifierImplicationClause_satisfies_of_false_antecedent antecedents
        (tmVerifierStateAtom V (t + 1) s) (tmVerifierLabelAtom V t none)
        (tmVerifierStackFamilyAssignment V p stkAt) hmem hFalse
  · exact tmVerifierFrameAllStacksCNFBetween_satisfies_of_false_antecedent V p t
      (t + 1) antecedents (tmVerifierStackFamilyAssignment V p stkAt) hmem hFalse

theorem tmVerifierHaltedRowsCNFAt_satisfies_of_nonhalting_label
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    {l : (tmVerifierTM V).Λ}
    (hl : (tmVerifierRunCfgAt V p t).l = some l) :
    CNF.Satisfies (tmVerifierHaltedRowsCNFAt V p t)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  intro c hc
  rw [tmVerifierHaltedRowsCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨s, _hs, hc⟩
  exact tmVerifierHaltedRowCNFAt_satisfies_of_nonhalting_label V p t s stkAt hl c hc

theorem tmVerifierTransitionRowCNFAt_satisfies_current_label_state
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hl : (tmVerifierRunCfgAt V p t).l = some l)
    (hs : (tmVerifierRunCfgAt V p t).var = s)
    (hControlCurrent :
      ∀ w : TMVerifierStmtWindow V,
        w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s →
          CNF.Satisfies (tmVerifierWindowControlCNFAt V t l s w)
            (tmVerifierStackFamilyAssignment V p stkAt))
    (hStackCurrent :
      ∀ w : TMVerifierStmtWindow V,
        w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s →
          CNF.Satisfies
            (tmVerifierWindowStackBoundaryCNFAt V p t l s w ++
              tmVerifierWindowStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
                p t w (tmVerifierWindowAntecedents V t l s w))
            (tmVerifierStackFamilyAssignment V p stkAt)) :
    CNF.Satisfies (tmVerifierTransitionRowCNFAt V (tmVerifierActivePushPayloadBoundary V) p t)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  rw [tmVerifierTransitionRowCNFAt, CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    exact ⟨tmVerifierTransitionControlCNFAt_satisfies_current_label_state V p t l s stkAt
        hl hs hControlCurrent,
      tmVerifierTransitionWindowStackCNFAt_satisfies_current_label_state V
        (tmVerifierActivePushPayloadBoundary V) p t l s stkAt hl hs hStackCurrent,
      ⟩
  · exact tmVerifierHaltedRowsCNFAt_satisfies_of_nonhalting_label V p t stkAt hl

end SAT
end ComplexityReduction
