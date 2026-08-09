/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyExtraction
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.GlobalTableauAccepted

/-!
Accepted-run assignments for the x-only Cook-Levin tableau.

The x-only tableau uses bounds and global micro-row coordinates depending only
on `x`.  This file constructs the corresponding assignment from a bounded
accepting certificate and proves the base blocks that do not yet require the
selected-window transition aggregation.
-/

namespace ComplexityReduction
namespace SAT

/-! ### X-only accepted-run stack family -/

noncomputable def tmVerifierXOnlyAcceptedRunGlobalStacks
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier) :
    Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k) := by
  classical
  exact fun u =>
    if h : u ≤ tmVerifierXOnlyTimeBound V x then
      (tmVerifierRunCfgAt V (x, c) u).stk
    else
      let decoded := Nat.unpair (tmVerifierXOnlyFixedMicroPayload V x u)
      tmVerifierWindowMicroStacks V (x, c) decoded.1
        (tmVerifierRunSelectedWindow V (x, c) decoded.1) decoded.2

theorem tmVerifierXOnlyAcceptedRunGlobalStacks_at_macro
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    {u : Nat} (hu : u ≤ tmVerifierXOnlyTimeBound V x) :
    tmVerifierXOnlyAcceptedRunGlobalStacks V x c u =
      (tmVerifierRunCfgAt V (x, c) u).stk := by
  simp [tmVerifierXOnlyAcceptedRunGlobalStacks, hu]

theorem tmVerifierXOnlyAcceptedRunGlobalStacks_at_fixed_micro
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (t micro : Nat) :
    tmVerifierXOnlyAcceptedRunGlobalStacks V x c
        (tmVerifierXOnlyFixedMicroTime V x t micro) =
      tmVerifierWindowMicroStacks V (x, c) t
        (tmVerifierRunSelectedWindow V (x, c) t) micro := by
  have hnot :
      ¬ tmVerifierXOnlyFixedMicroTime V x t micro ≤ tmVerifierXOnlyTimeBound V x := by
    intro hle
    have hbase := tmVerifierXOnlyFixedMicroBase_le_time V x t micro
    simp [tmVerifierXOnlyFixedMicroBase] at hbase
    omega
  simp [tmVerifierXOnlyAcceptedRunGlobalStacks, hnot]

noncomputable def tmVerifierXOnlyAcceptedRunAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier) : Assignment :=
  tmVerifierStackFamilyAssignment V (x, c) (tmVerifierXOnlyAcceptedRunGlobalStacks V x c)

/-! ### X-only stack-family well-formedness -/

theorem tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_stackFamilyAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (t : Nat) (hActive : tmVerifierStacksActive V (stkAt t))
    (k : tmVerifierStackIndex V) (x : L.Instance.Carrier) :
    CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t k)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  intro clause hclause
  rw [tmVerifierXOnlyStackCellDomainsCNFAt] at hclause
  rcases List.mem_flatMap.mp hclause with ⟨cell, _hcell, hclause⟩
  exact tmVerifierStackReadChoiceDomainCNFAt_satisfies_stackFamilyAssignment V p
    stkAt t hActive k cell clause hclause

theorem tmVerifierXOnlyStackEmptyTailCNFAt_satisfies_stackFamilyAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (t : Nat) (k : tmVerifierStackIndex V) (x : L.Instance.Carrier) :
    CNF.Satisfies (tmVerifierXOnlyStackEmptyTailCNFAt V x t k)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  intro clause hclause
  rw [tmVerifierXOnlyStackEmptyTailCNFAt] at hclause
  rcases List.mem_map.mp hclause with ⟨cell, _hcell, rfl⟩
  by_cases hselected : cell < (stkAt t k).length
  · refine ⟨Clause.negate (tmVerifierStackEmptyAtom V t k cell), ?_, ?_⟩
    · simp [tmVerifierStackEmptyTailClause, tmVerifierImplicationClause]
    · exact (Clause.negate_eval_true_iff (tmVerifierStackEmptyAtom V t k cell)
        (tmVerifierStackFamilyAssignment V p stkAt)).2
        (tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_selected V p stkAt t k
          hselected)
  · refine ⟨tmVerifierStackEmptyAtom V t k (cell + 1), ?_, ?_⟩
    · simp [tmVerifierStackEmptyTailClause, tmVerifierImplicationClause]
    · exact tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_not_selected V p stkAt
        (u := t) (j := k) (cell := cell + 1) (by
          intro h
          exact hselected (by omega))

theorem tmVerifierXOnlyStackFinalEmptyCNFAt_satisfies_stackFamilyAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (t : Nat) (k : tmVerifierStackIndex V) (x : L.Instance.Carrier)
    (hlen : (stkAt t k).length ≤ tmVerifierXOnlyCellBound V x) :
    CNF.Satisfies (tmVerifierXOnlyStackFinalEmptyCNFAt V x t k)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  intro clause hclause
  have hclause' :
      clause = [tmVerifierStackEmptyAtom V t k (tmVerifierXOnlyCellBound V x)] := by
    simpa [tmVerifierXOnlyStackFinalEmptyCNFAt] using hclause
  subst clause
  refine ⟨tmVerifierStackEmptyAtom V t k (tmVerifierXOnlyCellBound V x), by simp, ?_⟩
  exact tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_not_selected V p stkAt
    (u := t) (j := k) (cell := tmVerifierXOnlyCellBound V x) (by
      intro h
      omega)

theorem tmVerifierXOnlyStackWellFormedCNFAt_satisfies_stackFamilyAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (t : Nat) (k : tmVerifierStackIndex V) (x : L.Instance.Carrier)
    (hActive : tmVerifierStacksActive V (stkAt t))
    (hlen : (stkAt t k).length ≤ tmVerifierXOnlyCellBound V x) :
    CNF.Satisfies (tmVerifierXOnlyStackWellFormedCNFAt V x t k)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  rw [tmVerifierXOnlyStackWellFormedCNFAt, CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    exact
      ⟨tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_stackFamilyAssignment V p
          stkAt t hActive k x,
        tmVerifierXOnlyStackEmptyTailCNFAt_satisfies_stackFamilyAssignment V p stkAt
          t k x⟩
  · exact tmVerifierXOnlyStackFinalEmptyCNFAt_satisfies_stackFamilyAssignment V p
      stkAt t k x hlen

theorem tmVerifierXOnlyAllStackWellFormedCNFAt_satisfies_stackFamilyAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (t : Nat) (x : L.Instance.Carrier)
    (hActive : tmVerifierStacksActive V (stkAt t))
    (hlen : ∀ k : tmVerifierStackIndex V, (stkAt t k).length ≤ tmVerifierXOnlyCellBound V x) :
    CNF.Satisfies (tmVerifierXOnlyAllStackWellFormedCNFAt V x t)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  intro clause hclause
  rw [tmVerifierXOnlyAllStackWellFormedCNFAt] at hclause
  rcases List.mem_flatMap.mp hclause with ⟨k, _hk, hclause⟩
  exact tmVerifierXOnlyStackWellFormedCNFAt_satisfies_stackFamilyAssignment V p stkAt
    t k x hActive (hlen k) clause hclause

theorem tmVerifierRunCfgAt_stack_length_le_xOnlyCellBound_of_cert_size_le
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x)
    {t : Nat} (ht : t ≤ tmVerifierXOnlyTimeBound V x)
    (k : tmVerifierStackIndex V) :
    ((tmVerifierRunCfgAt V (x, c) t).stk k).length ≤ tmVerifierXOnlyCellBound V x := by
  have hRun := tmVerifierRunCfgAt_stack_length_le_input_prefix_output_slack V (x, c) t k
  have hInput := tmVerifierInputWord_length_le_xOnlyInputLengthBound_of_cert_size_le V x c hSize
  have hTime :
      t * TM2Programs.finTM2StepPushBound (tmVerifierTM V) ≤
        tmVerifierXOnlyTimeBound V x * TM2Programs.finTM2StepPushBound (tmVerifierTM V) :=
    Nat.mul_le_mul_right _ ht
  calc
    ((tmVerifierRunCfgAt V (x, c) t).stk k).length
        ≤ (tmVerifierInputWord V (x, c)).length +
            t * TM2Programs.finTM2StepPushBound (tmVerifierTM V) +
            (tmVerifierBoolOutputWord V true).length + 1 := hRun
    _ ≤ tmVerifierXOnlyInputLengthBound V x +
            tmVerifierXOnlyTimeBound V x * TM2Programs.finTM2StepPushBound (tmVerifierTM V) +
            (tmVerifierBoolOutputWord V true).length + 1 := by
          omega
    _ = tmVerifierXOnlyCellBound V x := by
          simp [tmVerifierXOnlyCellBound]

theorem tmVerifierRunCfgAt_of_outputs_true_ge_steps
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (hOut : tmVerifierOutputsBoolInTime V p true)
    {t : Nat} (ht : hOut.steps ≤ t) :
    tmVerifierRunCfgAt V p t = tmVerifierOutputCfg V true := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le ht
  have htEq : t = d + hOut.steps := by
    simpa [Nat.add_comm] using hd
  have hSteps :
      (flip bind (tmVerifierTM V).step)^[hOut.steps] (some (tmVerifierInitialCfg V p)) =
        some (tmVerifierOutputCfg V true) := by
    simpa [tmVerifierOutputsBoolInTime, tmVerifierInitialCfg, tmVerifierOutputCfg] using
      hOut.evals_in_steps
  rw [tmVerifierRunCfgAt, htEq, Function.iterate_add_apply, hSteps]
  cases d with
  | zero =>
      rfl
  | succ d =>
      have hStop : (tmVerifierTM V).step (tmVerifierOutputCfg V true) = none := by
        simp [tmVerifierOutputCfg, Turing.FinTM2.step, Turing.TM2.step, Turing.haltList]
        rfl
      have hNone :
          (flip bind (tmVerifierTM V).step)^[d.succ] (some (tmVerifierOutputCfg V true)) =
            none := by
        rw [Function.iterate_succ_apply]
        change (flip bind (tmVerifierTM V).step)^[d]
          ((tmVerifierTM V).step (tmVerifierOutputCfg V true)) = none
        rw [hStop]
        exact optionStep_iterate_none (tmVerifierTM V).step d
      rw [hNone]

theorem tmVerifierRunCfgAt_of_outputs_true_ge_timeBound
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (hOut : tmVerifierOutputsBoolInTime V p true)
    {t : Nat} (ht : tmVerifierTimeBound V p ≤ t) :
    tmVerifierRunCfgAt V p t = tmVerifierOutputCfg V true :=
  tmVerifierRunCfgAt_of_outputs_true_ge_steps V p hOut (le_trans hOut.steps_le_m ht)

theorem tmVerifierXOnlyAcceptedRunGlobalStacks_macro_stacksActive
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    {t : Nat} (ht : t ≤ tmVerifierXOnlyTimeBound V x) :
    tmVerifierStacksActive V (tmVerifierXOnlyAcceptedRunGlobalStacks V x c t) := by
  rw [tmVerifierXOnlyAcceptedRunGlobalStacks_at_macro V x c ht]
  exact tmVerifierRunCfgAt_stacksActive V (x, c) t

theorem tmVerifierXOnlyAcceptedRunGlobalStacks_macro_length_le
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x)
    {t : Nat} (ht : t ≤ tmVerifierXOnlyTimeBound V x)
    (k : tmVerifierStackIndex V) :
    (tmVerifierXOnlyAcceptedRunGlobalStacks V x c t k).length ≤
      tmVerifierXOnlyCellBound V x := by
  rw [tmVerifierXOnlyAcceptedRunGlobalStacks_at_macro V x c ht]
  exact tmVerifierRunCfgAt_stack_length_le_xOnlyCellBound_of_cert_size_le V x c hSize ht k

theorem tmVerifierXOnlyAcceptedRunGlobalStacks_fixedMicro_stacksActive_any
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (t micro : Nat) :
    tmVerifierStacksActive V
      (tmVerifierXOnlyAcceptedRunGlobalStacks V x c
        (tmVerifierXOnlyFixedMicroTime V x t micro)) := by
  cases hLabel : (tmVerifierRunCfgAt V (x, c) t).l with
  | none =>
      rw [tmVerifierXOnlyAcceptedRunGlobalStacks_at_fixed_micro]
      simpa [tmVerifierRunSelectedWindow, hLabel, tmVerifierWindowMicroStacks,
        tmVerifierWindowActionsApplyStacks] using tmVerifierRunCfgAt_stacksActive V (x, c) t
  | some l =>
      have hw := tmVerifierRunSelectedWindow_mem V (x, c) (t := t) hLabel rfl
      rw [tmVerifierXOnlyAcceptedRunGlobalStacks_at_fixed_micro]
      exact tmVerifierWindowMicroStacks_stacksActive V (x, c) t hw micro

theorem tmVerifierXOnlyAcceptedRunGlobalStacks_fixedMicro_length_le_any
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x)
    (hOut : tmVerifierOutputsBoolInTime V (x, c) true)
    {t : Nat} (ht : t < tmVerifierXOnlyTimeBound V x)
    (micro : Nat) (k : tmVerifierStackIndex V) :
    (tmVerifierXOnlyAcceptedRunGlobalStacks V x c
        (tmVerifierXOnlyFixedMicroTime V x t micro) k).length ≤
      tmVerifierXOnlyCellBound V x := by
  cases hLabel : (tmVerifierRunCfgAt V (x, c) t).l with
  | none =>
      rw [tmVerifierXOnlyAcceptedRunGlobalStacks_at_fixed_micro]
      have hRun :=
        tmVerifierRunCfgAt_stack_length_le_xOnlyCellBound_of_cert_size_le V x c hSize
          (Nat.le_of_lt ht) k
      simpa [tmVerifierRunSelectedWindow, hLabel, tmVerifierWindowMicroStacks,
        tmVerifierWindowActionsApplyStacks] using hRun
  | some l =>
      by_cases htFixed : t < tmVerifierTimeBound V (x, c)
      · have hw := tmVerifierRunSelectedWindow_mem V (x, c) (t := t) hLabel rfl
        rw [tmVerifierXOnlyAcceptedRunGlobalStacks_at_fixed_micro]
        exact (tmVerifierWindowMicroStacks_length_le V (x, c) htFixed hw micro k).trans
          (tmVerifierCellBound_le_xOnlyCellBound_of_cert_size_le V x c hSize)
      · have hcfg := tmVerifierRunCfgAt_of_outputs_true_ge_timeBound V (x, c) hOut
          (Nat.le_of_not_gt htFixed)
        rw [hcfg] at hLabel
        simp [tmVerifierOutputCfg, Turing.haltList] at hLabel

/-! ### Base x-only blocks -/

theorem tmVerifierXOnlyControlDomainCNFAt_satisfies_acceptedRun
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier) (t : Nat) :
    CNF.Satisfies (tmVerifierControlDomainCNFAt V t)
      (tmVerifierXOnlyAcceptedRunAssignment V x c) := by
  rw [tmVerifierControlDomainCNFAt, CNF.satisfies_append]
  constructor
  · let selected := (tmVerifierRunCfgAt V (x, c) t).l
    apply CookLevin.exactlyOneCNF_satisfies_of_exists_unique
    · exact tmVerifierLabelAtomsAt_nodup V t
    · exact ⟨tmVerifierLabelAtom V t selected, tmVerifierLabelAtomsAt_mem V t selected, by
        rw [tmVerifierXOnlyAcceptedRunAssignment]
        rw [tmVerifierLabelAtom_eval_stackFamilyAssignment_controlBoundary]
        exact (tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff V (x, c) t selected).2 rfl⟩
    · intro atom₁ hAtom₁ atom₂ hAtom₂ hTrue₁ hTrue₂
      rcases List.mem_map.mp hAtom₁ with ⟨label₁, _hlabel₁, rfl⟩
      rcases List.mem_map.mp hAtom₂ with ⟨label₂, _hlabel₂, rfl⟩
      have h₁ : label₁ = (tmVerifierRunCfgAt V (x, c) t).l := by
        have hBoundary :
            (tmVerifierLabelAtom V t label₁).eval
                (tmVerifierControlBoundaryAssignment V (x, c)) = true := by
          rw [← tmVerifierLabelAtom_eval_stackFamilyAssignment_controlBoundary]
          simpa [tmVerifierXOnlyAcceptedRunAssignment] using hTrue₁
        exact (tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff V (x, c) t label₁).1
          hBoundary
      have h₂ : label₂ = (tmVerifierRunCfgAt V (x, c) t).l := by
        have hBoundary :
            (tmVerifierLabelAtom V t label₂).eval
                (tmVerifierControlBoundaryAssignment V (x, c)) = true := by
          rw [← tmVerifierLabelAtom_eval_stackFamilyAssignment_controlBoundary]
          simpa [tmVerifierXOnlyAcceptedRunAssignment] using hTrue₂
        exact (tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff V (x, c) t label₂).1
          hBoundary
      subst label₁
      subst label₂
      rfl
  · let selected := (tmVerifierRunCfgAt V (x, c) t).var
    apply CookLevin.exactlyOneCNF_satisfies_of_exists_unique
    · exact tmVerifierStateAtomsAt_nodup V t
    · exact ⟨tmVerifierStateAtom V t selected, tmVerifierStateAtomsAt_mem V t selected, by
        rw [tmVerifierXOnlyAcceptedRunAssignment]
        rw [tmVerifierStateAtom_eval_stackFamilyAssignment_controlBoundary]
        exact (tmVerifierStateAtom_eval_controlBoundaryAssignment_iff V (x, c) t selected).2 rfl⟩
    · intro atom₁ hAtom₁ atom₂ hAtom₂ hTrue₁ hTrue₂
      rcases List.mem_map.mp hAtom₁ with ⟨state₁, _hstate₁, rfl⟩
      rcases List.mem_map.mp hAtom₂ with ⟨state₂, _hstate₂, rfl⟩
      have h₁ : state₁ = (tmVerifierRunCfgAt V (x, c) t).var := by
        have hBoundary :
            (tmVerifierStateAtom V t state₁).eval
                (tmVerifierControlBoundaryAssignment V (x, c)) = true := by
          rw [← tmVerifierStateAtom_eval_stackFamilyAssignment_controlBoundary]
          simpa [tmVerifierXOnlyAcceptedRunAssignment] using hTrue₁
        exact (tmVerifierStateAtom_eval_controlBoundaryAssignment_iff V (x, c) t state₁).1
          hBoundary
      have h₂ : state₂ = (tmVerifierRunCfgAt V (x, c) t).var := by
        have hBoundary :
            (tmVerifierStateAtom V t state₂).eval
                (tmVerifierControlBoundaryAssignment V (x, c)) = true := by
          rw [← tmVerifierStateAtom_eval_stackFamilyAssignment_controlBoundary]
          simpa [tmVerifierXOnlyAcceptedRunAssignment] using hTrue₂
        exact (tmVerifierStateAtom_eval_controlBoundaryAssignment_iff V (x, c) t state₂).1
          hBoundary
      subst state₁
      subst state₂
      rfl

theorem tmVerifierXOnlyControlDomainRowsCNF_satisfies_acceptedRun
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier) :
    CNF.Satisfies ((tmVerifierXOnlyTableauTimeRange V x).flatMap fun t =>
      tmVerifierControlDomainCNFAt V t)
      (tmVerifierXOnlyAcceptedRunAssignment V x c) := by
  intro clause hclause
  rcases List.mem_flatMap.mp hclause with ⟨t, _ht, hclause⟩
  exact tmVerifierXOnlyControlDomainCNFAt_satisfies_acceptedRun V x c t clause hclause

theorem tmVerifierXOnlyInitialControlCNF_satisfies_acceptedRun
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier) :
    CNF.Satisfies (tmVerifierInitialControlCNF V)
      (tmVerifierXOnlyAcceptedRunAssignment V x c) := by
  rw [tmVerifierInitialControlCNF, CNF.satisfies_append]
  constructor
  · exact (tmVerifierUnitCNF_satisfies
      (tmVerifierLabelAtom V 0 (some (tmVerifierTM V).main))
      (tmVerifierXOnlyAcceptedRunAssignment V x c)).2 (by
        rw [tmVerifierXOnlyAcceptedRunAssignment]
        rw [tmVerifierLabelAtom_eval_stackFamilyAssignment_controlBoundary]
        rw [tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff]
        simp [tmVerifierInitialCfg, Turing.initList])
  · exact (tmVerifierUnitCNF_satisfies
      (tmVerifierStateAtom V 0 (tmVerifierTM V).initialState)
      (tmVerifierXOnlyAcceptedRunAssignment V x c)).2 (by
        rw [tmVerifierXOnlyAcceptedRunAssignment]
        rw [tmVerifierStateAtom_eval_stackFamilyAssignment_controlBoundary]
        rw [tmVerifierStateAtom_eval_controlBoundaryAssignment_iff]
        simp [tmVerifierInitialCfg, Turing.initList])

theorem tmVerifierXOnlyInitialStackCNF_satisfies_acceptedRun
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x) :
    CNF.Satisfies (tmVerifierXOnlyInitialStackCNF V x)
      (tmVerifierXOnlyAcceptedRunAssignment V x c) := by
  rw [tmVerifierXOnlyInitialStackCNF_satisfies]
  constructor
  · intro l hl
    rw [List.mem_append] at hl
    rcases hl with hSymbol | hTail
    · rw [tmVerifierInstanceInputPrefixLiterals] at hSymbol
      rcases List.mem_map.mp hSymbol with ⟨entry, hentry, rfl⟩
      have hZip := List.mem_zipIdx hentry
      have hEntryLt : entry.2 < (tmVerifierInstanceInputPrefixWord V x).length := by
        simpa using hZip.2.1
      have hEntryEq : entry.1 = (tmVerifierInstanceInputPrefixWord V x)[entry.2] := by
        simpa using hZip.2.2
      have hInputLen :
          (tmVerifierInstanceInputPrefixWord V x).length ≤
            (tmVerifierInputWord V (x, c)).length := by
        rw [tmVerifierInputWord_eq_instancePrefix_append_certificateSuffix]
        simp
      have hEntryInputLt : entry.2 < (tmVerifierInputWord V (x, c)).length :=
        lt_of_lt_of_le hEntryLt hInputLen
      have hStack0 :
          tmVerifierXOnlyAcceptedRunGlobalStacks V x c 0 (tmVerifierTM V).k₀ =
            tmVerifierInputWord V (x, c) := by
        rw [tmVerifierXOnlyAcceptedRunGlobalStacks_at_macro V x c (by omega)]
        simp [tmVerifierInitialCfg, Turing.initList]
      have hcell : entry.2 <
          (tmVerifierXOnlyAcceptedRunGlobalStacks V x c 0 (tmVerifierTM V).k₀).length := by
        simpa [hStack0] using hEntryInputLt
      have hsym :
          ((tmVerifierXOnlyAcceptedRunGlobalStacks V x c 0
              (tmVerifierTM V).k₀)[entry.2]'hcell) = entry.1 := by
        have hInputSym :
            (tmVerifierInputWord V (x, c))[entry.2]'hEntryInputLt = entry.1 := by
          have hWordEq :=
            tmVerifierInputWord_eq_instancePrefix_append_certificateSuffix V x c
          have hAppendLt :
              entry.2 <
                (tmVerifierInstanceInputPrefixWord V x ++
                  tmVerifierCertificateInputSuffixWord V c).length := by
            simpa [← hWordEq] using hEntryInputLt
          have hAppendSym :
              ((tmVerifierInstanceInputPrefixWord V x ++
                  tmVerifierCertificateInputSuffixWord V c)[entry.2]'hAppendLt) =
                entry.1 := by
            have hget :
                ((tmVerifierInstanceInputPrefixWord V x ++
                    tmVerifierCertificateInputSuffixWord V c)[entry.2]'hAppendLt) =
                  (tmVerifierInstanceInputPrefixWord V x)[entry.2]'hEntryLt :=
              List.getElem_append_left (as := tmVerifierInstanceInputPrefixWord V x)
                (bs := tmVerifierCertificateInputSuffixWord V c) (i := entry.2) hEntryLt
                (h' := hAppendLt)
            exact hget.trans hEntryEq.symm
          simpa [hWordEq] using hAppendSym
        simpa [hStack0] using hInputSym
      simpa [tmVerifierXOnlyAcceptedRunAssignment, tmVerifierInputStackSymbolAtom, hsym]
        using
          tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_selected V (x, c)
            (tmVerifierXOnlyAcceptedRunGlobalStacks V x c) 0 (tmVerifierTM V).k₀ hcell
    · rw [tmVerifierXOnlyInputStackEmptyTailLiterals] at hTail
      rcases List.mem_map.mp hTail with ⟨cell, hcell, rfl⟩
      have hTailInfo :
          cell ∈ tmVerifierXOnlyCellRange V x ∧
            tmVerifierXOnlyInputLengthBound V x ≤ cell := by
        simpa using hcell
      have hInputWordLe :
          (tmVerifierInputWord V (x, c)).length ≤ tmVerifierXOnlyInputLengthBound V x :=
        tmVerifierInputWord_length_le_xOnlyInputLengthBound_of_cert_size_le V x c hSize
      have hStack0 :
          tmVerifierXOnlyAcceptedRunGlobalStacks V x c 0 (tmVerifierTM V).k₀ =
            tmVerifierInputWord V (x, c) := by
        rw [tmVerifierXOnlyAcceptedRunGlobalStacks_at_macro V x c (by omega)]
        simp [tmVerifierInitialCfg, Turing.initList]
      exact tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_not_selected V (x, c)
        (tmVerifierXOnlyAcceptedRunGlobalStacks V x c) (u := 0)
        (j := (tmVerifierTM V).k₀) (cell := cell) (by
          intro hlt
          have hlt' : cell < (tmVerifierInputWord V (x, c)).length := by
            simpa [hStack0] using hlt
          exact Nat.not_lt_of_ge (le_trans hInputWordLe hTailInfo.2) hlt')
  · intro l hl
    rw [tmVerifierXOnlyInitialNonInputEmptyLiterals] at hl
    rcases List.mem_flatMap.mp hl with ⟨k, hk, hcellLit⟩
    rcases List.mem_map.mp hcellLit with ⟨cell, _hcell, rfl⟩
    have hkNe : k ≠ (tmVerifierTM V).k₀ := by
      simpa [tmVerifierNonInputStacks] using hk
    have hlen : (tmVerifierXOnlyAcceptedRunGlobalStacks V x c 0 k).length = 0 := by
      rw [tmVerifierXOnlyAcceptedRunGlobalStacks_at_macro V x c (by omega)]
      simp [tmVerifierInitialCfg_noninput_stack_empty V (x, c) k hkNe]
    exact tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_not_selected V (x, c)
      (tmVerifierXOnlyAcceptedRunGlobalStacks V x c) (u := 0) (j := k) (cell := cell)
      (by omega)

theorem tmVerifierXOnlyStackWellFormedRowsCNF_satisfies_acceptedRun
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x) :
    CNF.Satisfies (tmVerifierXOnlyStackWellFormedRowsCNF V x)
      (tmVerifierXOnlyAcceptedRunAssignment V x c) := by
  intro clause hclause
  rw [tmVerifierXOnlyStackWellFormedRowsCNF] at hclause
  rcases List.mem_flatMap.mp hclause with ⟨t, ht, hclause⟩
  have htLe : t ≤ tmVerifierXOnlyTimeBound V x := by
    rw [tmVerifierXOnlyTableauTimeRange, List.mem_range] at ht
    omega
  simpa [tmVerifierXOnlyAcceptedRunAssignment] using
    tmVerifierXOnlyAllStackWellFormedCNFAt_satisfies_stackFamilyAssignment V (x, c)
      (tmVerifierXOnlyAcceptedRunGlobalStacks V x c) t x
      (tmVerifierXOnlyAcceptedRunGlobalStacks_macro_stacksActive V x c htLe)
      (fun k => tmVerifierXOnlyAcceptedRunGlobalStacks_macro_length_le V x c hSize htLe k)
      clause hclause

theorem tmVerifierXOnlyWindowFixedMicroDomainCNFAt_satisfies_acceptedRun
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x)
    (hOut : tmVerifierOutputsBoolInTime V (x, c) true)
    {t : Nat} (ht : t < tmVerifierXOnlyTimeBound V x)
    (w : TMVerifierStmtWindow V) :
    CNF.Satisfies (tmVerifierXOnlyWindowFixedMicroDomainCNFAt V x t w)
      (tmVerifierXOnlyAcceptedRunAssignment V x c) := by
  intro clause hclause
  rw [tmVerifierXOnlyWindowFixedMicroDomainCNFAt] at hclause
  rcases List.mem_flatMap.mp hclause with ⟨micro, _hmicro, hclause⟩
  rcases List.mem_flatMap.mp hclause with ⟨k, _hk, hclause⟩
  simpa [tmVerifierXOnlyAcceptedRunAssignment] using
    tmVerifierXOnlyStackWellFormedCNFAt_satisfies_stackFamilyAssignment V (x, c)
      (tmVerifierXOnlyAcceptedRunGlobalStacks V x c)
      (tmVerifierXOnlyFixedMicroTime V x t micro) k x
      (tmVerifierXOnlyAcceptedRunGlobalStacks_fixedMicro_stacksActive_any V x c t micro)
      (tmVerifierXOnlyAcceptedRunGlobalStacks_fixedMicro_length_le_any V x c hSize hOut
        ht micro k) clause hclause

theorem tmVerifierXOnlyTransitionFixedMicroDomainCNFAt_satisfies_acceptedRun
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x)
    (hOut : tmVerifierOutputsBoolInTime V (x, c) true)
    {t : Nat} (ht : t < tmVerifierXOnlyTimeBound V x) :
    CNF.Satisfies (tmVerifierXOnlyTransitionFixedMicroDomainCNFAt V x t)
      (tmVerifierXOnlyAcceptedRunAssignment V x c) := by
  intro clause hclause
  rw [tmVerifierXOnlyTransitionFixedMicroDomainCNFAt] at hclause
  rcases List.mem_flatMap.mp hclause with ⟨l, _hl, hclause⟩
  rcases List.mem_flatMap.mp hclause with ⟨s, _hs, hclause⟩
  rcases List.mem_flatMap.mp hclause with ⟨w, _hw, hclause⟩
  exact tmVerifierXOnlyWindowFixedMicroDomainCNFAt_satisfies_acceptedRun V x c
    hSize hOut ht w clause hclause

theorem tmVerifierXOnlyTransitionFixedMicroDomainRowsCNF_satisfies_acceptedRun
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x)
    (hOut : tmVerifierOutputsBoolInTime V (x, c) true) :
    CNF.Satisfies (tmVerifierXOnlyTransitionFixedMicroDomainRowsCNF V x)
      (tmVerifierXOnlyAcceptedRunAssignment V x c) := by
  intro clause hclause
  rw [tmVerifierXOnlyTransitionFixedMicroDomainRowsCNF] at hclause
  rcases List.mem_flatMap.mp hclause with ⟨t, ht, hclause⟩
  have htLt : t < tmVerifierXOnlyTimeBound V x := by
    simpa [tmVerifierXOnlyTransitionTimeRange, List.mem_range] using ht
  exact tmVerifierXOnlyTransitionFixedMicroDomainCNFAt_satisfies_acceptedRun V x c
    hSize hOut htLt clause hclause

theorem tmVerifierXOnlyOutputTrueCNFAt_satisfies_acceptedRun_of_cfg
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    {t : Nat} (ht : t ≤ tmVerifierXOnlyTimeBound V x)
    (hCfg : tmVerifierRunCfgAt V (x, c) t = tmVerifierOutputCfg V true) :
    CNF.Satisfies (tmVerifierXOnlyOutputTrueCNFAt V x t)
      (tmVerifierXOnlyAcceptedRunAssignment V x c) := by
  rw [tmVerifierXOnlyOutputTrueCNFAt_satisfies]
  constructor
  · intro l hl
    rw [List.mem_append] at hl
    rcases hl with hSymbol | hTail
    · rw [tmVerifierOutputTrueSymbolLiteralsAt] at hSymbol
      rcases List.mem_map.mp hSymbol with ⟨entry, hentry, rfl⟩
      have hZip := List.mem_zipIdx hentry
      have hEntryLt : entry.2 < (tmVerifierBoolOutputWord V true).length := by
        simpa using hZip.2.1
      have hEntryEq : entry.1 = (tmVerifierBoolOutputWord V true)[entry.2] := by
        simpa using hZip.2.2
      have hStackEnd :
          tmVerifierXOnlyAcceptedRunGlobalStacks V x c t (tmVerifierTM V).k₁ =
            tmVerifierBoolOutputWord V true := by
        rw [tmVerifierXOnlyAcceptedRunGlobalStacks_at_macro V x c ht, hCfg]
        simp [tmVerifierOutputCfg, Turing.haltList]
      have hcell : entry.2 <
          (tmVerifierXOnlyAcceptedRunGlobalStacks V x c t (tmVerifierTM V).k₁).length := by
        simpa [hStackEnd] using hEntryLt
      have hsym :
          ((tmVerifierXOnlyAcceptedRunGlobalStacks V x c t
              (tmVerifierTM V).k₁)[entry.2]'hcell) = entry.1 := by
        have hget :
            (tmVerifierXOnlyAcceptedRunGlobalStacks V x c t
                (tmVerifierTM V).k₁)[entry.2]'hcell =
              (tmVerifierBoolOutputWord V true)[entry.2] := by
          simp [hStackEnd]
        simpa [hEntryEq] using hget
      simpa [tmVerifierXOnlyAcceptedRunAssignment, tmVerifierOutputStackSymbolAtom, hsym]
        using
          tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_selected V (x, c)
            (tmVerifierXOnlyAcceptedRunGlobalStacks V x c) t (tmVerifierTM V).k₁ hcell
    · rw [tmVerifierXOnlyOutputTrueEmptyTailLiteralsAt] at hTail
      rcases List.mem_map.mp hTail with ⟨cell, hcell, rfl⟩
      have hTailInfo :
          cell ∈ tmVerifierXOnlyCellRange V x ∧
            (tmVerifierBoolOutputWord V true).length ≤ cell := by
        simpa using hcell
      have hStackEnd :
          tmVerifierXOnlyAcceptedRunGlobalStacks V x c t (tmVerifierTM V).k₁ =
            tmVerifierBoolOutputWord V true := by
        rw [tmVerifierXOnlyAcceptedRunGlobalStacks_at_macro V x c ht, hCfg]
        simp [tmVerifierOutputCfg, Turing.haltList]
      exact tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_not_selected V (x, c)
        (tmVerifierXOnlyAcceptedRunGlobalStacks V x c) (u := t)
        (j := (tmVerifierTM V).k₁) (cell := cell) (by
          intro hlt
          have hlt' : cell < (tmVerifierBoolOutputWord V true).length := by
            simpa [hStackEnd] using hlt
          exact Nat.not_lt_of_ge hTailInfo.2 hlt')
  · intro l hl
    rw [tmVerifierXOnlyOutputTrueNonOutputEmptyLiteralsAt] at hl
    rcases List.mem_flatMap.mp hl with ⟨k, hk, hcellLit⟩
    rcases List.mem_map.mp hcellLit with ⟨cell, _hcell, rfl⟩
    have hkNe : k ≠ (tmVerifierTM V).k₁ := by
      simpa [tmVerifierNonOutputStacks] using hk
    have hlen : (tmVerifierXOnlyAcceptedRunGlobalStacks V x c t k).length = 0 := by
      rw [tmVerifierXOnlyAcceptedRunGlobalStacks_at_macro V x c ht, hCfg]
      simp [tmVerifierOutputCfg_nonoutput_stack_empty V true k hkNe]
    exact tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_not_selected V (x, c)
      (tmVerifierXOnlyAcceptedRunGlobalStacks V x c) (u := t) (j := k) (cell := cell)
      (by omega)

theorem tmVerifierXOnlyEndpointCNF_satisfies_acceptedRun_of_outputs_true
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x)
    (hOut : tmVerifierOutputsBoolInTime V (x, c) true) :
    CNF.Satisfies (tmVerifierXOnlyEndpointCNF V x)
      (tmVerifierXOnlyAcceptedRunAssignment V x c) := by
  have hTime : tmVerifierTimeBound V (x, c) ≤ tmVerifierXOnlyTimeBound V x :=
    tmVerifierTimeBound_le_xOnlyTimeBound_of_cert_size_le V x c hSize
  have hCfgEnd :
      tmVerifierRunCfgAt V (x, c) (tmVerifierXOnlyTimeBound V x) =
        tmVerifierOutputCfg V true :=
    tmVerifierRunCfgAt_of_outputs_true_ge_timeBound V (x, c) hOut hTime
  rw [tmVerifierXOnlyEndpointCNF, CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    constructor
    · exact (tmVerifierUnitCNF_satisfies
        (tmVerifierLabelAtom V (tmVerifierXOnlyTimeBound V x) none)
        (tmVerifierXOnlyAcceptedRunAssignment V x c)).2 (by
          rw [tmVerifierXOnlyAcceptedRunAssignment]
          rw [tmVerifierLabelAtom_eval_stackFamilyAssignment_controlBoundary]
          rw [tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff]
          rw [hCfgEnd]
          simp [tmVerifierOutputCfg, Turing.haltList])
    · exact (tmVerifierUnitCNF_satisfies
        (tmVerifierStateAtom V (tmVerifierXOnlyTimeBound V x) (tmVerifierTM V).initialState)
        (tmVerifierXOnlyAcceptedRunAssignment V x c)).2 (by
          rw [tmVerifierXOnlyAcceptedRunAssignment]
          rw [tmVerifierStateAtom_eval_stackFamilyAssignment_controlBoundary]
          rw [tmVerifierStateAtom_eval_controlBoundaryAssignment_iff]
          rw [hCfgEnd]
          simp [tmVerifierOutputCfg, Turing.haltList])
  · exact tmVerifierXOnlyOutputTrueCNFAt_satisfies_acceptedRun_of_cfg V x c
      (le_rfl) hCfgEnd

end SAT
end ComplexityReduction
