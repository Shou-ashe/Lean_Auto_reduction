/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.StackActive

namespace ComplexityReduction
namespace SAT

/-! ### Concrete run stack-row assignment -/

theorem tmVerifierStep_stack_length_le
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    {cfg cfg' : (tmVerifierTM V).Cfg}
    (hstep : (tmVerifierTM V).step cfg = some cfg')
    (k : tmVerifierStackIndex V) :
    (cfg'.stk k).length ≤
      (cfg.stk k).length + TM2Programs.finTM2StepPushBound (tmVerifierTM V) := by
  rcases cfg with ⟨label, state, stk⟩
  cases label with
  | none =>
      simp [Turing.FinTM2.step, Turing.TM2.step] at hstep
  | some label =>
      have hcfg' :
          cfg' = Turing.TM2.stepAux ((tmVerifierTM V).m label) state stk := by
        have hSome :
            some cfg' = some (Turing.TM2.stepAux ((tmVerifierTM V).m label) state stk) := by
          simpa [Turing.FinTM2.step, Turing.TM2.step] using hstep.symm
        cases hSome
        rfl
      subst cfg'
      exact
        (TM2Programs.stepAux_stack_length_le ((tmVerifierTM V).m label) state stk k).trans
          (Nat.add_le_add_left
            (TM2Programs.stmtPushCount_le_finTM2StepPushBound (tmVerifierTM V) label)
            (stk k).length)

theorem tmVerifierInitialCfg_stack_length_le_inputWord_length
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (k : tmVerifierStackIndex V) :
    ((tmVerifierInitialCfg V p).stk k).length ≤ (tmVerifierInputWord V p).length := by
  by_cases hk : k = (tmVerifierTM V).k₀
  · subst k
    simp
  · simp [tmVerifierInitialCfg_noninput_stack_empty V p k hk]

theorem tmVerifierOutputCfg_stack_length_le_boolOutputWord_length
    {L : EncodedDecisionProblem} (V : TMVerifier L) (b : Bool)
    (k : tmVerifierStackIndex V) :
    ((tmVerifierOutputCfg V b).stk k).length ≤ (tmVerifierBoolOutputWord V b).length := by
  by_cases hk : k = (tmVerifierTM V).k₁
  · subst k
    simp
  · simp [tmVerifierOutputCfg_nonoutput_stack_empty V b k hk]

theorem tmVerifierRunOption_stack_length_le
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (k : tmVerifierStackIndex V) :
    match (flip bind (tmVerifierTM V).step)^[t] (some (tmVerifierInitialCfg V p)) with
    | some cfg =>
        (cfg.stk k).length ≤
          ((tmVerifierInitialCfg V p).stk k).length +
            t * TM2Programs.finTM2StepPushBound (tmVerifierTM V)
    | none => True := by
  induction t with
  | zero =>
      simp
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      cases hprev :
          (flip bind (tmVerifierTM V).step)^[t] (some (tmVerifierInitialCfg V p)) with
      | none =>
          change match Option.bind (none : Option (tmVerifierTM V).Cfg) (tmVerifierTM V).step with
            | some cfg =>
                (cfg.stk k).length ≤
                  ((tmVerifierInitialCfg V p).stk k).length +
                    (t + 1) * TM2Programs.finTM2StepPushBound (tmVerifierTM V)
            | none => True
          simp
      | some prev =>
          have hPrevLen :
              (prev.stk k).length ≤
                ((tmVerifierInitialCfg V p).stk k).length +
                  t * TM2Programs.finTM2StepPushBound (tmVerifierTM V) := by
            rw [hprev] at ih
            exact ih
          change match (tmVerifierTM V).step prev with
            | some cfg =>
                (cfg.stk k).length ≤
                  ((tmVerifierInitialCfg V p).stk k).length +
                    (t + 1) * TM2Programs.finTM2StepPushBound (tmVerifierTM V)
            | none => True
          cases hnext : (tmVerifierTM V).step prev with
          | none =>
              trivial
          | some next =>
              have hStepLen := tmVerifierStep_stack_length_le V hnext k
              exact calc
                (next.stk k).length
                    ≤ (prev.stk k).length +
                        TM2Programs.finTM2StepPushBound (tmVerifierTM V) := hStepLen
                _ ≤ (((tmVerifierInitialCfg V p).stk k).length +
                        t * TM2Programs.finTM2StepPushBound (tmVerifierTM V)) +
                      TM2Programs.finTM2StepPushBound (tmVerifierTM V) := by
                    exact Nat.add_le_add_right hPrevLen _
                _ ≤ ((tmVerifierInitialCfg V p).stk k).length +
                      (t + 1) * TM2Programs.finTM2StepPushBound (tmVerifierTM V) := by
                    rw [Nat.add_mul, one_mul]
                    omega

theorem tmVerifierRunCfgAt_stack_length_le_cellBound
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) {t : Nat}
    (ht : t ≤ tmVerifierTimeBound V p) (k : tmVerifierStackIndex V) :
    ((tmVerifierRunCfgAt V p t).stk k).length ≤ tmVerifierCellBound V p := by
  unfold tmVerifierRunCfgAt
  cases hopt :
      (flip bind (tmVerifierTM V).step)^[t] (some (tmVerifierInitialCfg V p)) with
  | none =>
      have hOut := tmVerifierOutputCfg_stack_length_le_boolOutputWord_length V true k
      calc
        ((tmVerifierOutputCfg V true).stk k).length
            ≤ (tmVerifierBoolOutputWord V true).length := hOut
        _ ≤ tmVerifierCellBound V p := by
            simp [tmVerifierCellBound]
            omega
  | some cfg =>
      have hRun := tmVerifierRunOption_stack_length_le V p t k
      have hRunLen :
          (cfg.stk k).length ≤
            ((tmVerifierInitialCfg V p).stk k).length +
              t * TM2Programs.finTM2StepPushBound (tmVerifierTM V) := by
        rw [hopt] at hRun
        exact hRun
      have hInit := tmVerifierInitialCfg_stack_length_le_inputWord_length V p k
      have hTime :
          t * TM2Programs.finTM2StepPushBound (tmVerifierTM V) ≤
            tmVerifierTimeBound V p * TM2Programs.finTM2StepPushBound (tmVerifierTM V) :=
        Nat.mul_le_mul_right _ ht
      calc
        (cfg.stk k).length
            ≤ ((tmVerifierInitialCfg V p).stk k).length +
                t * TM2Programs.finTM2StepPushBound (tmVerifierTM V) := hRunLen
        _ ≤ (tmVerifierInputWord V p).length +
              t * TM2Programs.finTM2StepPushBound (tmVerifierTM V) := by
            exact Nat.add_le_add_right hInit _
        _ ≤ (tmVerifierInputWord V p).length +
              tmVerifierTimeBound V p * TM2Programs.finTM2StepPushBound (tmVerifierTM V) := by
            exact Nat.add_le_add_left hTime _
        _ ≤ tmVerifierCellBound V p := by
            simp [tmVerifierCellBound]
            omega

theorem tmVerifierRunCfgAt_stack_length_le_input_prefix_output_slack
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (k : tmVerifierStackIndex V) :
    ((tmVerifierRunCfgAt V p t).stk k).length ≤
      (tmVerifierInputWord V p).length +
        t * TM2Programs.finTM2StepPushBound (tmVerifierTM V) +
        (tmVerifierBoolOutputWord V true).length + 1 := by
  unfold tmVerifierRunCfgAt
  cases hopt :
      (flip bind (tmVerifierTM V).step)^[t] (some (tmVerifierInitialCfg V p)) with
  | none =>
      have hOut := tmVerifierOutputCfg_stack_length_le_boolOutputWord_length V true k
      calc
        ((tmVerifierOutputCfg V true).stk k).length
            ≤ (tmVerifierBoolOutputWord V true).length := hOut
        _ ≤ (tmVerifierInputWord V p).length +
              t * TM2Programs.finTM2StepPushBound (tmVerifierTM V) +
              (tmVerifierBoolOutputWord V true).length + 1 := by
            omega
  | some cfg =>
      have hRun := tmVerifierRunOption_stack_length_le V p t k
      have hRunLen :
          (cfg.stk k).length ≤
            ((tmVerifierInitialCfg V p).stk k).length +
              t * TM2Programs.finTM2StepPushBound (tmVerifierTM V) := by
        rw [hopt] at hRun
        exact hRun
      have hInit := tmVerifierInitialCfg_stack_length_le_inputWord_length V p k
      calc
        (cfg.stk k).length
            ≤ ((tmVerifierInitialCfg V p).stk k).length +
                t * TM2Programs.finTM2StepPushBound (tmVerifierTM V) := hRunLen
        _ ≤ (tmVerifierInputWord V p).length +
              t * TM2Programs.finTM2StepPushBound (tmVerifierTM V) := by
            exact Nat.add_le_add_right hInit _
        _ ≤ (tmVerifierInputWord V p).length +
              t * TM2Programs.finTM2StepPushBound (tmVerifierTM V) +
              (tmVerifierBoolOutputWord V true).length + 1 := by
            omega

noncomputable def tmVerifierRunStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) : Assignment := by
  classical
  exact fun var =>
    if ∃ k cell, ∃ hcell : cell < ((tmVerifierRunCfgAt V p t).stk k).length,
        var =
          (tmVerifierStackSymbolAtom V t k cell
            (tmVerifierActiveStackSymbolPayload V k
              (((tmVerifierRunCfgAt V p t).stk k)[cell]'hcell))).var then
      true
    else if ∃ k cell, ∃ hcell : cell < ((tmVerifierRunCfgAt V p t).stk k).length,
        var = (tmVerifierStackEmptyAtom V t k cell).var then
      false
    else if ∃ u j cell, var = (tmVerifierStackEmptyAtom V u j cell).var then
      true
    else if ∃ u j cell payload,
        var = (tmVerifierStackSymbolAtom V u j cell payload).var then
      false
    else
      tmVerifierControlBoundaryAssignment V p var

theorem tmVerifierStackSymbolAtom_eval_runStackAssignment_of_selected
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (k : tmVerifierStackIndex V) {cell : Nat}
    (hcell : cell < ((tmVerifierRunCfgAt V p t).stk k).length) :
    (tmVerifierStackSymbolAtom V t k cell
        (tmVerifierActiveStackSymbolPayload V k
          (((tmVerifierRunCfgAt V p t).stk k)[cell]'hcell))).eval
      (tmVerifierRunStackAssignment V p t) = true := by
  classical
  change tmVerifierRunStackAssignment V p t
    (tmVerifierStackSymbolAtom V t k cell
      (tmVerifierActiveStackSymbolPayload V k
        (((tmVerifierRunCfgAt V p t).stk k)[cell]'hcell))).var = true
  have hSelected :
      ∃ j i, ∃ hi : i < ((tmVerifierRunCfgAt V p t).stk j).length,
        (tmVerifierStackSymbolAtom V t k cell
            (tmVerifierActiveStackSymbolPayload V k
              (((tmVerifierRunCfgAt V p t).stk k)[cell]'hcell))).var =
          (tmVerifierStackSymbolAtom V t j i
            (tmVerifierActiveStackSymbolPayload V j
              (((tmVerifierRunCfgAt V p t).stk j)[i]'hi))).var :=
    ⟨k, cell, hcell, rfl⟩
  rw [tmVerifierRunStackAssignment, if_pos hSelected]

theorem tmVerifierStackEmptyAtom_eval_runStackAssignment_of_selected
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (k : tmVerifierStackIndex V) {cell : Nat}
    (hcell : cell < ((tmVerifierRunCfgAt V p t).stk k).length) :
    (tmVerifierStackEmptyAtom V t k cell).eval
      (tmVerifierRunStackAssignment V p t) = false := by
  classical
  change tmVerifierRunStackAssignment V p t
    (tmVerifierStackEmptyAtom V t k cell).var = false
  have hNoSymbol :
      ¬ ∃ j i, ∃ hi : i < ((tmVerifierRunCfgAt V p t).stk j).length,
        (tmVerifierStackEmptyAtom V t k cell).var =
          (tmVerifierStackSymbolAtom V t j i
            (tmVerifierActiveStackSymbolPayload V j
              (((tmVerifierRunCfgAt V p t).stk j)[i]'hi))).var := by
    rintro ⟨j, i, hi, h⟩
    exact tmVerifierStackEmptyAtom_var_ne_stackSymbolAtom_var V t t k j cell i
      (tmVerifierActiveStackSymbolPayload V j
        (((tmVerifierRunCfgAt V p t).stk j)[i]'hi)) h
  have hSelectedEmpty :
      ∃ j i, ∃ hi : i < ((tmVerifierRunCfgAt V p t).stk j).length,
        (tmVerifierStackEmptyAtom V t k cell).var =
          (tmVerifierStackEmptyAtom V t j i).var :=
    ⟨k, cell, hcell, rfl⟩
  rw [tmVerifierRunStackAssignment, if_neg hNoSymbol, if_pos hSelectedEmpty]

theorem tmVerifierStackEmptyAtom_eval_runStackAssignment_of_not_selected
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    {u : Nat} {j : tmVerifierStackIndex V} {cell : Nat}
    (hnot : ¬ (u = t ∧ cell < ((tmVerifierRunCfgAt V p t).stk j).length)) :
    (tmVerifierStackEmptyAtom V u j cell).eval
      (tmVerifierRunStackAssignment V p t) = true := by
  classical
  change tmVerifierRunStackAssignment V p t
    (tmVerifierStackEmptyAtom V u j cell).var = true
  have hNoSymbol :
      ¬ ∃ k i, ∃ hi : i < ((tmVerifierRunCfgAt V p t).stk k).length,
        (tmVerifierStackEmptyAtom V u j cell).var =
          (tmVerifierStackSymbolAtom V t k i
            (tmVerifierActiveStackSymbolPayload V k
              (((tmVerifierRunCfgAt V p t).stk k)[i]'hi))).var := by
    rintro ⟨k, i, hi, h⟩
    exact tmVerifierStackEmptyAtom_var_ne_stackSymbolAtom_var V u t j k cell i
      (tmVerifierActiveStackSymbolPayload V k
        (((tmVerifierRunCfgAt V p t).stk k)[i]'hi)) h
  have hNoSelectedEmpty :
      ¬ ∃ k i, ∃ hi : i < ((tmVerifierRunCfgAt V p t).stk k).length,
        (tmVerifierStackEmptyAtom V u j cell).var =
          (tmVerifierStackEmptyAtom V t k i).var := by
    rintro ⟨k, i, hi, h⟩
    rcases tmVerifierStackEmptyAtom_var_eq V h with ⟨hut, hjk, hcelli⟩
    subst u
    subst k
    subst i
    exact hnot ⟨rfl, hi⟩
  have hAnyEmpty :
      ∃ u' j' cell',
        (tmVerifierStackEmptyAtom V u j cell).var =
          (tmVerifierStackEmptyAtom V u' j' cell').var := ⟨u, j, cell, rfl⟩
  rw [tmVerifierRunStackAssignment, if_neg hNoSymbol, if_neg hNoSelectedEmpty,
    if_pos hAnyEmpty]

theorem tmVerifierStackSymbolAtom_eval_runStackAssignment_of_not_selected
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    {u : Nat} {j : tmVerifierStackIndex V} {cell payload : Nat}
    (hnot : ¬ (u = t ∧ cell < ((tmVerifierRunCfgAt V p t).stk j).length)) :
    (tmVerifierStackSymbolAtom V u j cell payload).eval
      (tmVerifierRunStackAssignment V p t) = false := by
  classical
  change tmVerifierRunStackAssignment V p t
    (tmVerifierStackSymbolAtom V u j cell payload).var = false
  have hNoSelected :
      ¬ ∃ k i, ∃ hi : i < ((tmVerifierRunCfgAt V p t).stk k).length,
        (tmVerifierStackSymbolAtom V u j cell payload).var =
          (tmVerifierStackSymbolAtom V t k i
            (tmVerifierActiveStackSymbolPayload V k
              (((tmVerifierRunCfgAt V p t).stk k)[i]'hi))).var := by
    rintro ⟨k, i, hi, h⟩
    rcases tmVerifierStackSymbolAtom_var_eq V h with ⟨hut, hStack, hcelli, _hPayload⟩
    have hjk : j = k := tmVerifierStackCode_injective V hStack
    subst u
    subst k
    subst i
    exact hnot ⟨rfl, hi⟩
  have hNoSelectedEmpty :
      ¬ ∃ k i, ∃ hi : i < ((tmVerifierRunCfgAt V p t).stk k).length,
        (tmVerifierStackSymbolAtom V u j cell payload).var =
          (tmVerifierStackEmptyAtom V t k i).var := by
    rintro ⟨k, i, hi, h⟩
    exact tmVerifierStackSymbolAtom_var_ne_stackEmptyAtom_var V u t j k cell i payload h
  have hNoAnyEmpty :
      ¬ ∃ u' j' cell',
        (tmVerifierStackSymbolAtom V u j cell payload).var =
          (tmVerifierStackEmptyAtom V u' j' cell').var := by
    rintro ⟨u', j', cell', h⟩
    exact tmVerifierStackSymbolAtom_var_ne_stackEmptyAtom_var V u u' j j' cell cell'
      payload h
  have hAnySymbol :
      ∃ u' j' cell' payload',
        (tmVerifierStackSymbolAtom V u j cell payload).var =
          (tmVerifierStackSymbolAtom V u' j' cell' payload').var :=
    ⟨u, j, cell, payload, rfl⟩
  rw [tmVerifierRunStackAssignment, if_neg hNoSelected, if_neg hNoSelectedEmpty,
    if_neg hNoAnyEmpty, if_pos hAnySymbol]

theorem tmVerifierStackSymbolAtom_payload_eq_of_eval_runStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (k : tmVerifierStackIndex V) {cell payload : Nat}
    (hcell : cell < ((tmVerifierRunCfgAt V p t).stk k).length)
    (htrue :
      (tmVerifierStackSymbolAtom V t k cell payload).eval
        (tmVerifierRunStackAssignment V p t) = true) :
    payload =
      tmVerifierActiveStackSymbolPayload V k
        (((tmVerifierRunCfgAt V p t).stk k)[cell]'hcell) := by
  classical
  change tmVerifierRunStackAssignment V p t
    (tmVerifierStackSymbolAtom V t k cell payload).var = true at htrue
  by_cases hSelected :
      ∃ j i, ∃ hi : i < ((tmVerifierRunCfgAt V p t).stk j).length,
        (tmVerifierStackSymbolAtom V t k cell payload).var =
          (tmVerifierStackSymbolAtom V t j i
            (tmVerifierActiveStackSymbolPayload V j
              (((tmVerifierRunCfgAt V p t).stk j)[i]'hi))).var
  · rcases hSelected with ⟨j, i, hi, hvar⟩
    rcases tmVerifierStackSymbolAtom_var_eq V hvar with
      ⟨_ht, hStack, hcelli, hpayload⟩
    have hkj : k = j := tmVerifierStackCode_injective V hStack
    subst j
    subst i
    simpa using hpayload
  · have hNoSelectedEmpty :
        ¬ ∃ j i, ∃ hi : i < ((tmVerifierRunCfgAt V p t).stk j).length,
          (tmVerifierStackSymbolAtom V t k cell payload).var =
            (tmVerifierStackEmptyAtom V t j i).var := by
      rintro ⟨j, i, hi, h⟩
      exact tmVerifierStackSymbolAtom_var_ne_stackEmptyAtom_var V t t k j cell i payload h
    have hNoAnyEmpty :
        ¬ ∃ u' j' cell',
          (tmVerifierStackSymbolAtom V t k cell payload).var =
            (tmVerifierStackEmptyAtom V u' j' cell').var := by
      rintro ⟨u', j', cell', h⟩
      exact tmVerifierStackSymbolAtom_var_ne_stackEmptyAtom_var V t u' k j' cell cell'
        payload h
    have hAnySymbol :
        ∃ u' j' cell' payload',
          (tmVerifierStackSymbolAtom V t k cell payload).var =
            (tmVerifierStackSymbolAtom V u' j' cell' payload').var :=
      ⟨t, k, cell, payload, rfl⟩
    have hfalse :
        tmVerifierRunStackAssignment V p t
          (tmVerifierStackSymbolAtom V t k cell payload).var = false := by
      rw [tmVerifierRunStackAssignment, if_neg hSelected, if_neg hNoSelectedEmpty,
        if_neg hNoAnyEmpty, if_pos hAnySymbol]
    simp [hfalse] at htrue

theorem tmVerifierRunStack_word_payload_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (k : tmVerifierStackIndex V) :
    ∀ i, (hi : i < ((tmVerifierRunCfgAt V p t).stk k).length) →
      TMVerifierStackReadChoice.symbol (V := V) (k := k)
          (tmVerifierActiveStackSymbolPayload V k
            (((tmVerifierRunCfgAt V p t).stk k)[i]'hi))
          (((tmVerifierRunCfgAt V p t).stk k)[i]'hi) ∈
        tmVerifierStackReadChoices V k := by
  intro i hi
  have hget :
      ((tmVerifierRunCfgAt V p t).stk k)[i]? =
        some (((tmVerifierRunCfgAt V p t).stk k)[i]'hi) := by
    exact List.getElem?_eq_getElem hi
  exact tmVerifierActiveStackSymbolPayload_mem V k
    (((tmVerifierRunCfgAt V p t).stk k)[i]'hi)
    (tmVerifierRunStackSymbolActive V p t k i
      (((tmVerifierRunCfgAt V p t).stk k)[i]'hi) hget)

theorem tmVerifierStackReadChoiceDomainCNFAt_satisfies_runStackAssignment_of_lt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (k : tmVerifierStackIndex V) {cell : Nat}
    (hcell : cell < ((tmVerifierRunCfgAt V p t).stk k).length) :
    CNF.Satisfies (tmVerifierStackReadChoiceDomainCNFAt V t k cell)
      (tmVerifierRunStackAssignment V p t) := by
  let selected :=
    TMVerifierStackReadChoice.symbol (V := V) (k := k)
      (tmVerifierActiveStackSymbolPayload V k
        (((tmVerifierRunCfgAt V p t).stk k)[cell]'hcell))
      (((tmVerifierRunCfgAt V p t).stk k)[cell]'hcell)
  apply CookLevin.exactlyOneCNF_satisfies_of_exists_unique
  · exact tmVerifierStackReadChoiceLiteralsAt_nodup V t k cell
  · exact
      ⟨TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell selected, by
        rw [tmVerifierStackReadChoiceLiteralsAt]
        exact List.mem_map.mpr
          ⟨selected, tmVerifierRunStack_word_payload_mem V p t k cell hcell, rfl⟩, by
        simp [selected, TMVerifierStackReadChoice.atomAt,
          tmVerifierStackSymbolAtom_eval_runStackAssignment_of_selected V p t k hcell]⟩
  · intro x hx y hy hxTrue hyTrue
    rcases List.mem_map.mp hx with ⟨choice₁, hchoice₁, rfl⟩
    rcases List.mem_map.mp hy with ⟨choice₂, hchoice₂, rfl⟩
    cases choice₁ with
    | empty =>
        have hxFalse :=
          tmVerifierStackEmptyAtom_eval_runStackAssignment_of_selected V p t k hcell
        simp [TMVerifierStackReadChoice.atomAt, hxFalse] at hxTrue
    | symbol payload₁ symbol₁ =>
        cases choice₂ with
        | empty =>
            have hyFalse :=
              tmVerifierStackEmptyAtom_eval_runStackAssignment_of_selected V p t k hcell
            simp [TMVerifierStackReadChoice.atomAt, hyFalse] at hyTrue
        | symbol payload₂ symbol₂ =>
            have hp₁ :
                payload₁ =
                  tmVerifierActiveStackSymbolPayload V k
                    (((tmVerifierRunCfgAt V p t).stk k)[cell]'hcell) :=
              tmVerifierStackSymbolAtom_payload_eq_of_eval_runStackAssignment V p t k
                hcell hxTrue
            have hp₂ :
                payload₂ =
                  tmVerifierActiveStackSymbolPayload V k
                    (((tmVerifierRunCfgAt V p t).stk k)[cell]'hcell) :=
              tmVerifierStackSymbolAtom_payload_eq_of_eval_runStackAssignment V p t k
                hcell hyTrue
            subst payload₁
            subst payload₂
            have hsym :
                symbol₁ = symbol₂ :=
              tmVerifierStackReadChoice_symbol_eq_of_payloadUnique V
                (tmVerifierStackPayloadUnique V) k
                (tmVerifierActiveStackSymbolPayload V k
                  (((tmVerifierRunCfgAt V p t).stk k)[cell]'hcell))
                symbol₁ symbol₂ hchoice₁ hchoice₂
            subst symbol₂
            rfl

theorem tmVerifierStackReadChoiceDomainCNFAt_satisfies_runStackAssignment_of_tail
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (k : tmVerifierStackIndex V) {cell : Nat}
    (hcell : ((tmVerifierRunCfgAt V p t).stk k).length ≤ cell) :
    CNF.Satisfies (tmVerifierStackReadChoiceDomainCNFAt V t k cell)
      (tmVerifierRunStackAssignment V p t) := by
  rw [tmVerifierStackReadChoiceDomainCNFAt, tmVerifierStackReadChoiceLiteralsAt,
    tmVerifierStackReadChoices]
  apply CookLevin.exactlyOneCNF_satisfies_cons_of_head_true_tail_false
  · simp [TMVerifierStackReadChoice.atomAt,
      tmVerifierStackEmptyAtom_eval_runStackAssignment_of_not_selected V p t
        (u := t) (j := k) (cell := cell) (by omega)]
  · intro y hy
    rcases List.mem_map.mp hy with ⟨choice, hchoice, rfl⟩
    cases choice with
    | empty =>
        exfalso
        rw [tmVerifierActiveReadChoices] at hchoice
        rcases List.mem_filterMap.mp hchoice with ⟨named, _hNamed, hSome⟩
        unfold tmVerifierActiveReadChoiceOfNamed? at hSome
        split at hSome <;> simp at hSome
    | symbol payload symbol =>
        simp [TMVerifierStackReadChoice.atomAt,
          tmVerifierStackSymbolAtom_eval_runStackAssignment_of_not_selected V p t
            (u := t) (j := k) (cell := cell) (payload := payload) (by omega)]

theorem tmVerifierStackReadChoiceDomainCNFAt_satisfies_runStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (k : tmVerifierStackIndex V) (cell : Nat) :
    CNF.Satisfies (tmVerifierStackReadChoiceDomainCNFAt V t k cell)
      (tmVerifierRunStackAssignment V p t) := by
  by_cases hcell : cell < ((tmVerifierRunCfgAt V p t).stk k).length
  · exact tmVerifierStackReadChoiceDomainCNFAt_satisfies_runStackAssignment_of_lt V p t k
      hcell
  · exact tmVerifierStackReadChoiceDomainCNFAt_satisfies_runStackAssignment_of_tail V p t k
      (Nat.le_of_not_gt hcell)

theorem tmVerifierStackCellDomainsCNFAt_satisfies_runStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k)
      (tmVerifierRunStackAssignment V p t) := by
  intro c hc
  rw [tmVerifierStackCellDomainsCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨cell, _hcell, hc⟩
  exact tmVerifierStackReadChoiceDomainCNFAt_satisfies_runStackAssignment V p t k cell c hc

theorem tmVerifierStackEmptyTailCNFAt_satisfies_runStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierStackEmptyTailCNFAt V p t k)
      (tmVerifierRunStackAssignment V p t) := by
  intro c hc
  rw [tmVerifierStackEmptyTailCNFAt] at hc
  rcases List.mem_map.mp hc with ⟨cell, hcell, rfl⟩
  by_cases hselected : cell < ((tmVerifierRunCfgAt V p t).stk k).length
  · refine ⟨Clause.negate (tmVerifierStackEmptyAtom V t k cell), ?_, ?_⟩
    · simp [tmVerifierStackEmptyTailClause, tmVerifierImplicationClause]
    · exact (Clause.negate_eval_true_iff (tmVerifierStackEmptyAtom V t k cell)
        (tmVerifierRunStackAssignment V p t)).2
        (tmVerifierStackEmptyAtom_eval_runStackAssignment_of_selected V p t k hselected)
  · refine ⟨tmVerifierStackEmptyAtom V t k (cell + 1), ?_, ?_⟩
    · simp [tmVerifierStackEmptyTailClause, tmVerifierImplicationClause]
    · exact tmVerifierStackEmptyAtom_eval_runStackAssignment_of_not_selected V p t
        (u := t) (j := k) (cell := cell + 1) (by
          intro h
          exact hselected (by omega))

theorem tmVerifierStackFinalEmptyCNFAt_satisfies_runStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (k : tmVerifierStackIndex V)
    (hlen : ((tmVerifierRunCfgAt V p t).stk k).length ≤ tmVerifierCellBound V p) :
    CNF.Satisfies (tmVerifierStackFinalEmptyCNFAt V p t k)
      (tmVerifierRunStackAssignment V p t) := by
  intro c hc
  have hc' :
      c = [tmVerifierStackEmptyAtom V t k (tmVerifierCellBound V p)] := by
    simpa [tmVerifierStackFinalEmptyCNFAt] using hc
  subst c
  refine ⟨tmVerifierStackEmptyAtom V t k (tmVerifierCellBound V p), by simp, ?_⟩
  exact tmVerifierStackEmptyAtom_eval_runStackAssignment_of_not_selected V p t
    (u := t) (j := k) (cell := tmVerifierCellBound V p) (by
      intro h
      omega)

theorem tmVerifierStackWellFormedCNFAt_satisfies_runStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (k : tmVerifierStackIndex V)
    (hlen : ((tmVerifierRunCfgAt V p t).stk k).length ≤ tmVerifierCellBound V p) :
    CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p t k)
      (tmVerifierRunStackAssignment V p t) := by
  rw [tmVerifierStackWellFormedCNFAt, CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    exact
      ⟨tmVerifierStackCellDomainsCNFAt_satisfies_runStackAssignment V p t k,
        tmVerifierStackEmptyTailCNFAt_satisfies_runStackAssignment V p t k⟩
  · exact tmVerifierStackFinalEmptyCNFAt_satisfies_runStackAssignment V p t k hlen

theorem tmVerifierAllStackWellFormedCNFAt_satisfies_runStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) {t : Nat}
    (ht : t ≤ tmVerifierTimeBound V p) :
    CNF.Satisfies (tmVerifierAllStackWellFormedCNFAt V p t)
      (tmVerifierRunStackAssignment V p t) := by
  intro c hc
  rw [tmVerifierAllStackWellFormedCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨k, _hk, hc⟩
  exact tmVerifierStackWellFormedCNFAt_satisfies_runStackAssignment V p t k
    (tmVerifierRunCfgAt_stack_length_le_cellBound V p ht k) c hc

end SAT
end ComplexityReduction
