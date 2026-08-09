/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.GlobalTransitionRowsAggregation
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.AcceptedRun

/-!
Accepted-run satisfaction for fixed-pair global transition rows.
-/

namespace ComplexityReduction
namespace SAT

theorem tmVerifierRunCfgAt_of_label_none_outputs_true
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    {t : Nat} (ht : t ≤ tmVerifierTimeBound V p)
    (hOut : tmVerifierOutputsBoolInTime V p true)
    (hLabel : (tmVerifierRunCfgAt V p t).l = none) :
    tmVerifierRunCfgAt V p t = tmVerifierOutputCfg V true := by
  unfold tmVerifierRunCfgAt
  cases hrun :
      (flip bind (tmVerifierTM V).step)^[t] (some (tmVerifierInitialCfg V p)) with
  | none =>
      rfl
  | some cfg =>
      have hCfgLabel : cfg.l = none := by
        rw [tmVerifierRunCfgAt, hrun] at hLabel
        exact hLabel
      have hCfgStop : (tmVerifierTM V).step cfg = none := by
        rcases cfg with ⟨label, state, stk⟩
        cases label with
        | none =>
            rfl
        | some l =>
            simp at hCfgLabel
      have hOutputStop : (tmVerifierTM V).step (tmVerifierOutputCfg V true) = none := by
        simp [tmVerifierOutputCfg, Turing.FinTM2.step, Turing.TM2.step, Turing.haltList]
        rfl
      have hCfgRun :
          StateTransition.EvalsToInTime (tmVerifierTM V).step (tmVerifierInitialCfg V p)
            (some cfg) (tmVerifierTimeBound V p) :=
        { steps := t
          evals_in_steps := by simpa using hrun
          steps_le_m := ht }
      have hOutRun :
          StateTransition.EvalsToInTime (tmVerifierTM V).step (tmVerifierInitialCfg V p)
            (some (tmVerifierOutputCfg V true)) (tmVerifierTimeBound V p) := by
        simpa [tmVerifierOutputsBoolInTime, tmVerifierInitialCfg, tmVerifierOutputCfg] using hOut
      exact evalsToInTime_some_unique_of_step_none hCfgStop hOutputStop hCfgRun hOutRun

theorem tmVerifierHaltedRowCNFAt_satisfies_acceptedRunGlobalStacks
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (hOut : tmVerifierOutputsBoolInTime V p true)
    {t : Nat} (ht : t < tmVerifierTimeBound V p)
    (s : (tmVerifierTM V).σ)
    (hLabel : (tmVerifierRunCfgAt V p t).l = none)
    (hs : (tmVerifierRunCfgAt V p t).var = s) :
    CNF.Satisfies (tmVerifierHaltedRowCNFAt V p t s)
      (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p)) := by
  let a := tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p)
  have htLe : t ≤ tmVerifierTimeBound V p := Nat.le_of_lt ht
  have htSuccLe : t + 1 ≤ tmVerifierTimeBound V p := Nat.succ_le_of_lt ht
  have hCfgT := tmVerifierRunCfgAt_of_label_none_outputs_true V p htLe hOut hLabel
  have hLabelSucc : (tmVerifierRunCfgAt V p (t + 1)).l = none := by
    rw [tmVerifierRunCfgAt, Function.iterate_succ_apply']
    cases hrun :
        (flip bind (tmVerifierTM V).step)^[t] (some (tmVerifierInitialCfg V p)) with
    | none =>
        rfl
    | some cfg =>
        have hcfg : tmVerifierRunCfgAt V p t = cfg := by
          rw [tmVerifierRunCfgAt, hrun]
        have hcfgLabel : cfg.l = none := by
          simpa [hcfg] using hLabel
        have hstep : (tmVerifierTM V).step cfg = none := by
          rcases cfg with ⟨label, state, stk⟩
          cases label with
          | none =>
              rfl
          | some l =>
              simp at hcfgLabel
        change (match (tmVerifierTM V).step cfg with
          | some cfg => cfg
          | none => tmVerifierOutputCfg V true).l = none
        rw [hstep]
        simp [tmVerifierOutputCfg, Turing.haltList]
  have hCfgSucc := tmVerifierRunCfgAt_of_label_none_outputs_true V p htSuccLe hOut hLabelSucc
  have hState : s = (tmVerifierOutputCfg V true).var := by
    rw [← hs, hCfgT]
  rw [tmVerifierHaltedRowCNFAt]
  let antecedents := tmVerifierHaltedRowAntecedents V t s
  change CNF.Satisfies
    ([tmVerifierImplicationClause antecedents (tmVerifierLabelAtom V (t + 1) none),
      tmVerifierImplicationClause antecedents (tmVerifierStateAtom V (t + 1) s)] ++
        tmVerifierFrameAllStacksCNFBetween V p t (t + 1) antecedents) a
  rw [CNF.satisfies_append]
  constructor
  · intro c hc
    have hc' :
        c = tmVerifierImplicationClause antecedents (tmVerifierLabelAtom V (t + 1) none) ∨
          c = tmVerifierImplicationClause antecedents (tmVerifierStateAtom V (t + 1) s) := by
      simpa using hc
    rcases hc' with rfl | rfl
    · exact tmVerifierImplicationClause_satisfies_of_conclusion antecedents
        (tmVerifierLabelAtom V (t + 1) none) a (by
          rw [tmVerifierLabelAtom_eval_stackFamilyAssignment_controlBoundary]
          rw [tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff]
          rw [hCfgSucc]
          simp [tmVerifierOutputCfg, Turing.haltList])
    · exact tmVerifierImplicationClause_satisfies_of_conclusion antecedents
        (tmVerifierStateAtom V (t + 1) s) a (by
          rw [tmVerifierStateAtom_eval_stackFamilyAssignment_controlBoundary]
          rw [tmVerifierStateAtom_eval_controlBoundaryAssignment_iff]
          rw [hState, hCfgSucc])
  · exact tmVerifierFrameAllStacksCNFBetween_satisfies_of_eval_eq V p t (t + 1)
      antecedents a (by
        intro k _hk cell _hcell choice _hchoice
        have hStack :
            tmVerifierAcceptedRunGlobalStacks V p (t + 1) k =
              tmVerifierAcceptedRunGlobalStacks V p t k := by
          rw [tmVerifierAcceptedRunGlobalStacks_at_macro V p htLe,
            tmVerifierAcceptedRunGlobalStacks_at_macro V p htSuccLe, hCfgT, hCfgSucc]
        exact TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_stack_eq
          V p (tmVerifierAcceptedRunGlobalStacks V p) t (t + 1) k cell choice hStack)

theorem tmVerifierHaltedRowsCNFAt_satisfies_acceptedRunGlobalStacks
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (hOut : tmVerifierOutputsBoolInTime V p true)
    {t : Nat} (ht : t < tmVerifierTimeBound V p)
    (hLabel : (tmVerifierRunCfgAt V p t).l = none) :
    CNF.Satisfies (tmVerifierHaltedRowsCNFAt V p t)
      (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p)) := by
  intro c hc
  rw [tmVerifierHaltedRowsCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨s, _hsMem, hc⟩
  by_cases hs : (tmVerifierRunCfgAt V p t).var = s
  · exact tmVerifierHaltedRowCNFAt_satisfies_acceptedRunGlobalStacks V p hOut ht s
      hLabel hs c hc
  · have hFalse :
        (tmVerifierStateAtom V t s).eval
            (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p)) =
          false := by
      exact tmVerifierStateAtom_eval_stackFamilyAssignment_false_of_ne V p
        (tmVerifierAcceptedRunGlobalStacks V p) t s (by
          intro h
          exact hs h.symm)
    let antecedents := tmVerifierHaltedRowAntecedents V t s
    rw [tmVerifierHaltedRowCNFAt] at hc
    have hmem : tmVerifierStateAtom V t s ∈ antecedents := by
      simp [antecedents, tmVerifierHaltedRowAntecedents]
    have hSatisfies :
        CNF.Satisfies (tmVerifierHaltedRowCNFAt V p t s)
          (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p)) := by
      rw [tmVerifierHaltedRowCNFAt]
      change CNF.Satisfies
        ([tmVerifierImplicationClause antecedents (tmVerifierLabelAtom V (t + 1) none),
          tmVerifierImplicationClause antecedents (tmVerifierStateAtom V (t + 1) s)] ++
            tmVerifierFrameAllStacksCNFBetween V p t (t + 1) antecedents)
          (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p))
      rw [CNF.satisfies_append]
      constructor
      · intro clause hclause
        have hclause' :
            clause = tmVerifierImplicationClause antecedents
                (tmVerifierLabelAtom V (t + 1) none) ∨
              clause = tmVerifierImplicationClause antecedents
                (tmVerifierStateAtom V (t + 1) s) := by
          simpa using hclause
        rcases hclause' with rfl | rfl
        · exact tmVerifierImplicationClause_satisfies_of_false_antecedent antecedents
            (tmVerifierLabelAtom V (t + 1) none) (tmVerifierStateAtom V t s)
            (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p))
            hmem hFalse
        · exact tmVerifierImplicationClause_satisfies_of_false_antecedent antecedents
            (tmVerifierStateAtom V (t + 1) s) (tmVerifierStateAtom V t s)
            (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p))
            hmem hFalse
      · exact tmVerifierFrameAllStacksCNFBetween_satisfies_of_false_antecedent V p t
          (t + 1) antecedents
          (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p))
          hmem hFalse
    exact hSatisfies c hc

theorem tmVerifierTransitionFixedRowCNFAt_satisfies_acceptedRunGlobalStacks
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (hOut : tmVerifierOutputsBoolInTime V p true)
    {t : Nat} (ht : t < tmVerifierTimeBound V p) :
    CNF.Satisfies (tmVerifierTransitionFixedRowCNFAt V
        (tmVerifierActivePushPayloadBoundary V) p t)
      (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p)) := by
  cases hLabel : (tmVerifierRunCfgAt V p t).l with
  | some l =>
      let s := (tmVerifierRunCfgAt V p t).var
      have hCurrent :=
        tmVerifierAcceptedRunGlobalStacks_sameControl_current V p ht hLabel rfl
      exact tmVerifierTransitionFixedRowCNFAt_satisfies_current_label_state V p t l s
        (tmVerifierAcceptedRunGlobalStacks V p) hLabel rfl hCurrent.1 hCurrent.2
  | none =>
      rw [tmVerifierTransitionFixedRowCNFAt, CNF.satisfies_append]
      constructor
      · rw [CNF.satisfies_append]
        constructor
        · intro c hc
          rw [tmVerifierTransitionFixedControlCNFAt] at hc
          rcases List.mem_flatMap.mp hc with ⟨l, _hl, hc⟩
          rcases List.mem_flatMap.mp hc with ⟨s, _hs, hc⟩
          rcases List.mem_flatMap.mp hc with ⟨w, _hw, hc⟩
          have hFalse :
              (tmVerifierLabelAtom V t (some l)).eval
                  (tmVerifierStackFamilyAssignment V p
                    (tmVerifierAcceptedRunGlobalStacks V p)) = false := by
            exact tmVerifierLabelAtom_eval_stackFamilyAssignment_false_of_ne V p
              (tmVerifierAcceptedRunGlobalStacks V p) t (some l) (by
                intro h
                simp [hLabel] at h)
          exact tmVerifierWindowFixedControlCNFAt_satisfies_of_false_antecedent V p t l s w
            (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p))
            (tmVerifierWindowFixedAntecedents_label_mem V p t l s w) hFalse c hc
        · intro c hc
          rw [tmVerifierTransitionFixedWindowStackCNFAt] at hc
          rcases List.mem_flatMap.mp hc with ⟨l, _hl, hc⟩
          rcases List.mem_flatMap.mp hc with ⟨s, _hs, hc⟩
          rcases List.mem_flatMap.mp hc with ⟨w, _hw, hc⟩
          have hFalse :
              (tmVerifierLabelAtom V t (some l)).eval
                  (tmVerifierStackFamilyAssignment V p
                    (tmVerifierAcceptedRunGlobalStacks V p)) = false := by
            exact tmVerifierLabelAtom_eval_stackFamilyAssignment_false_of_ne V p
              (tmVerifierAcceptedRunGlobalStacks V p) t (some l) (by
                intro h
                simp [hLabel] at h)
          exact tmVerifierWindowFixedStackCNF_satisfies_of_false_antecedent V
            (tmVerifierActivePushPayloadBoundary V) p t l s w
            (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p))
            (tmVerifierWindowFixedAntecedents_label_mem V p t l s w) hFalse c hc
      · exact tmVerifierHaltedRowsCNFAt_satisfies_acceptedRunGlobalStacks V p hOut ht
          hLabel

theorem tmVerifierTransitionFixedRowsCNF_satisfies_acceptedRunGlobalStacks
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (hOut : tmVerifierOutputsBoolInTime V p true) :
    CNF.Satisfies (tmVerifierTransitionFixedRowsCNF V
        (tmVerifierActivePushPayloadBoundary V) p)
      (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p)) := by
  intro c hc
  rw [tmVerifierTransitionFixedRowsCNF] at hc
  rcases List.mem_flatMap.mp hc with ⟨t, ht, hc⟩
  have htLt : t < tmVerifierTimeBound V p := by
    simpa [tmVerifierTransitionTimeRange, List.mem_range] using ht
  exact tmVerifierTransitionFixedRowCNFAt_satisfies_acceptedRunGlobalStacks V p hOut htLt
    c hc

end SAT
end ComplexityReduction
