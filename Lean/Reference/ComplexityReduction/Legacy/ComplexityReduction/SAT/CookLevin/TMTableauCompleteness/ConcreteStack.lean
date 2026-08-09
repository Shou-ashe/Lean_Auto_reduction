/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.RunStack

namespace ComplexityReduction
namespace SAT

/-! ### Concrete stack-family row assignment -/

noncomputable def tmVerifierConcreteStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k)) :
    Assignment := by
  classical
  exact fun var =>
    if ∃ k cell, ∃ hcell : cell < (stk k).length,
        var =
          (tmVerifierStackSymbolAtom V t k cell
            (tmVerifierActiveStackSymbolPayload V k ((stk k)[cell]'hcell))).var then
      true
    else if ∃ k cell, ∃ hcell : cell < (stk k).length,
        var = (tmVerifierStackEmptyAtom V t k cell).var then
      false
    else if ∃ u j cell, var = (tmVerifierStackEmptyAtom V u j cell).var then
      true
    else if ∃ u j cell payload,
        var = (tmVerifierStackSymbolAtom V u j cell payload).var then
      false
    else
      tmVerifierControlBoundaryAssignment V p var

theorem tmVerifierStackSymbolAtom_eval_concreteStackAssignment_of_selected
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (k : tmVerifierStackIndex V) {cell : Nat}
    (hcell : cell < (stk k).length) :
    (tmVerifierStackSymbolAtom V t k cell
        (tmVerifierActiveStackSymbolPayload V k ((stk k)[cell]'hcell))).eval
      (tmVerifierConcreteStackAssignment V p t stk) = true := by
  classical
  change tmVerifierConcreteStackAssignment V p t stk
    (tmVerifierStackSymbolAtom V t k cell
      (tmVerifierActiveStackSymbolPayload V k ((stk k)[cell]'hcell))).var = true
  have hSelected :
      ∃ j i, ∃ hi : i < (stk j).length,
        (tmVerifierStackSymbolAtom V t k cell
            (tmVerifierActiveStackSymbolPayload V k ((stk k)[cell]'hcell))).var =
          (tmVerifierStackSymbolAtom V t j i
            (tmVerifierActiveStackSymbolPayload V j ((stk j)[i]'hi))).var :=
    ⟨k, cell, hcell, rfl⟩
  rw [tmVerifierConcreteStackAssignment, if_pos hSelected]

theorem tmVerifierStackEmptyAtom_eval_concreteStackAssignment_of_selected
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (k : tmVerifierStackIndex V) {cell : Nat}
    (hcell : cell < (stk k).length) :
    (tmVerifierStackEmptyAtom V t k cell).eval
      (tmVerifierConcreteStackAssignment V p t stk) = false := by
  classical
  change tmVerifierConcreteStackAssignment V p t stk
    (tmVerifierStackEmptyAtom V t k cell).var = false
  have hNoSymbol :
      ¬ ∃ j i, ∃ hi : i < (stk j).length,
        (tmVerifierStackEmptyAtom V t k cell).var =
          (tmVerifierStackSymbolAtom V t j i
            (tmVerifierActiveStackSymbolPayload V j ((stk j)[i]'hi))).var := by
    rintro ⟨j, i, hi, h⟩
    exact tmVerifierStackEmptyAtom_var_ne_stackSymbolAtom_var V t t k j cell i
      (tmVerifierActiveStackSymbolPayload V j ((stk j)[i]'hi)) h
  have hSelectedEmpty :
      ∃ j i, ∃ hi : i < (stk j).length,
        (tmVerifierStackEmptyAtom V t k cell).var =
          (tmVerifierStackEmptyAtom V t j i).var :=
    ⟨k, cell, hcell, rfl⟩
  rw [tmVerifierConcreteStackAssignment, if_neg hNoSymbol, if_pos hSelectedEmpty]

theorem tmVerifierStackEmptyAtom_eval_concreteStackAssignment_of_not_selected
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    {u : Nat} {j : tmVerifierStackIndex V} {cell : Nat}
    (hnot : ¬ (u = t ∧ cell < (stk j).length)) :
    (tmVerifierStackEmptyAtom V u j cell).eval
      (tmVerifierConcreteStackAssignment V p t stk) = true := by
  classical
  change tmVerifierConcreteStackAssignment V p t stk
    (tmVerifierStackEmptyAtom V u j cell).var = true
  have hNoSymbol :
      ¬ ∃ k i, ∃ hi : i < (stk k).length,
        (tmVerifierStackEmptyAtom V u j cell).var =
          (tmVerifierStackSymbolAtom V t k i
            (tmVerifierActiveStackSymbolPayload V k ((stk k)[i]'hi))).var := by
    rintro ⟨k, i, hi, h⟩
    exact tmVerifierStackEmptyAtom_var_ne_stackSymbolAtom_var V u t j k cell i
      (tmVerifierActiveStackSymbolPayload V k ((stk k)[i]'hi)) h
  have hNoSelectedEmpty :
      ¬ ∃ k i, ∃ hi : i < (stk k).length,
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
  rw [tmVerifierConcreteStackAssignment, if_neg hNoSymbol, if_neg hNoSelectedEmpty,
    if_pos hAnyEmpty]

theorem tmVerifierStackSymbolAtom_eval_concreteStackAssignment_of_not_selected
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    {u : Nat} {j : tmVerifierStackIndex V} {cell payload : Nat}
    (hnot : ¬ (u = t ∧ cell < (stk j).length)) :
    (tmVerifierStackSymbolAtom V u j cell payload).eval
      (tmVerifierConcreteStackAssignment V p t stk) = false := by
  classical
  change tmVerifierConcreteStackAssignment V p t stk
    (tmVerifierStackSymbolAtom V u j cell payload).var = false
  have hNoSelected :
      ¬ ∃ k i, ∃ hi : i < (stk k).length,
        (tmVerifierStackSymbolAtom V u j cell payload).var =
          (tmVerifierStackSymbolAtom V t k i
            (tmVerifierActiveStackSymbolPayload V k ((stk k)[i]'hi))).var := by
    rintro ⟨k, i, hi, h⟩
    rcases tmVerifierStackSymbolAtom_var_eq V h with ⟨hut, hStack, hcelli, _hPayload⟩
    have hjk : j = k := tmVerifierStackCode_injective V hStack
    subst u
    subst k
    subst i
    exact hnot ⟨rfl, hi⟩
  have hNoSelectedEmpty :
      ¬ ∃ k i, ∃ hi : i < (stk k).length,
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
  rw [tmVerifierConcreteStackAssignment, if_neg hNoSelected, if_neg hNoSelectedEmpty,
    if_neg hNoAnyEmpty, if_pos hAnySymbol]

theorem tmVerifierStackSymbolAtom_payload_eq_of_eval_concreteStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (k : tmVerifierStackIndex V) {cell payload : Nat}
    (hcell : cell < (stk k).length)
    (htrue :
      (tmVerifierStackSymbolAtom V t k cell payload).eval
        (tmVerifierConcreteStackAssignment V p t stk) = true) :
    payload =
      tmVerifierActiveStackSymbolPayload V k ((stk k)[cell]'hcell) := by
  classical
  change tmVerifierConcreteStackAssignment V p t stk
    (tmVerifierStackSymbolAtom V t k cell payload).var = true at htrue
  by_cases hSelected :
      ∃ j i, ∃ hi : i < (stk j).length,
        (tmVerifierStackSymbolAtom V t k cell payload).var =
          (tmVerifierStackSymbolAtom V t j i
            (tmVerifierActiveStackSymbolPayload V j ((stk j)[i]'hi))).var
  · rcases hSelected with ⟨j, i, hi, hvar⟩
    rcases tmVerifierStackSymbolAtom_var_eq V hvar with
      ⟨_ht, hStack, hcelli, hpayload⟩
    have hkj : k = j := tmVerifierStackCode_injective V hStack
    subst j
    subst i
    simpa using hpayload
  · have hNoSelectedEmpty :
        ¬ ∃ j i, ∃ hi : i < (stk j).length,
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
        tmVerifierConcreteStackAssignment V p t stk
          (tmVerifierStackSymbolAtom V t k cell payload).var = false := by
      rw [tmVerifierConcreteStackAssignment, if_neg hSelected, if_neg hNoSelectedEmpty,
        if_neg hNoAnyEmpty, if_pos hAnySymbol]
    simp [hfalse] at htrue

theorem tmVerifierConcreteStack_word_payload_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hActive : tmVerifierStacksActive V stk)
    (k : tmVerifierStackIndex V) :
    ∀ i, (hi : i < (stk k).length) →
      TMVerifierStackReadChoice.symbol (V := V) (k := k)
          (tmVerifierActiveStackSymbolPayload V k ((stk k)[i]'hi))
          ((stk k)[i]'hi) ∈
        tmVerifierStackReadChoices V k := by
  intro i hi
  have hget :
      (stk k)[i]? = some ((stk k)[i]'hi) := by
    exact List.getElem?_eq_getElem hi
  exact tmVerifierActiveStackSymbolPayload_mem V k ((stk k)[i]'hi)
    (hActive k i ((stk k)[i]'hi) hget)

theorem tmVerifierStackReadChoiceDomainCNFAt_satisfies_concreteStackAssignment_of_lt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hActive : tmVerifierStacksActive V stk)
    (k : tmVerifierStackIndex V) {cell : Nat}
    (hcell : cell < (stk k).length) :
    CNF.Satisfies (tmVerifierStackReadChoiceDomainCNFAt V t k cell)
      (tmVerifierConcreteStackAssignment V p t stk) := by
  let selected :=
    TMVerifierStackReadChoice.symbol (V := V) (k := k)
      (tmVerifierActiveStackSymbolPayload V k ((stk k)[cell]'hcell))
      ((stk k)[cell]'hcell)
  apply CookLevin.exactlyOneCNF_satisfies_of_exists_unique
  · exact tmVerifierStackReadChoiceLiteralsAt_nodup V t k cell
  · exact
      ⟨TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell selected, by
        rw [tmVerifierStackReadChoiceLiteralsAt]
        exact List.mem_map.mpr
          ⟨selected, tmVerifierConcreteStack_word_payload_mem V stk hActive k cell hcell,
            rfl⟩, by
        simp [selected, TMVerifierStackReadChoice.atomAt,
          tmVerifierStackSymbolAtom_eval_concreteStackAssignment_of_selected V p t stk k
            hcell]⟩
  · intro x hx y hy hxTrue hyTrue
    rcases List.mem_map.mp hx with ⟨choice₁, hchoice₁, rfl⟩
    rcases List.mem_map.mp hy with ⟨choice₂, hchoice₂, rfl⟩
    cases choice₁ with
    | empty =>
        have hxFalse :=
          tmVerifierStackEmptyAtom_eval_concreteStackAssignment_of_selected V p t stk k
            hcell
        simp [TMVerifierStackReadChoice.atomAt, hxFalse] at hxTrue
    | symbol payload₁ symbol₁ =>
        cases choice₂ with
        | empty =>
            have hyFalse :=
              tmVerifierStackEmptyAtom_eval_concreteStackAssignment_of_selected V p t stk
                k hcell
            simp [TMVerifierStackReadChoice.atomAt, hyFalse] at hyTrue
        | symbol payload₂ symbol₂ =>
            have hp₁ :
                payload₁ =
                  tmVerifierActiveStackSymbolPayload V k ((stk k)[cell]'hcell) :=
              tmVerifierStackSymbolAtom_payload_eq_of_eval_concreteStackAssignment V p t
                stk k hcell hxTrue
            have hp₂ :
                payload₂ =
                  tmVerifierActiveStackSymbolPayload V k ((stk k)[cell]'hcell) :=
              tmVerifierStackSymbolAtom_payload_eq_of_eval_concreteStackAssignment V p t
                stk k hcell hyTrue
            subst payload₁
            subst payload₂
            have hsym :
                symbol₁ = symbol₂ :=
              tmVerifierStackReadChoice_symbol_eq_of_payloadUnique V
                (tmVerifierStackPayloadUnique V) k
                (tmVerifierActiveStackSymbolPayload V k ((stk k)[cell]'hcell))
                symbol₁ symbol₂ hchoice₁ hchoice₂
            subst symbol₂
            rfl

theorem tmVerifierStackReadChoiceDomainCNFAt_satisfies_concreteStackAssignment_of_tail
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (k : tmVerifierStackIndex V) {cell : Nat}
    (hcell : (stk k).length ≤ cell) :
    CNF.Satisfies (tmVerifierStackReadChoiceDomainCNFAt V t k cell)
      (tmVerifierConcreteStackAssignment V p t stk) := by
  rw [tmVerifierStackReadChoiceDomainCNFAt, tmVerifierStackReadChoiceLiteralsAt,
    tmVerifierStackReadChoices]
  apply CookLevin.exactlyOneCNF_satisfies_cons_of_head_true_tail_false
  · simp [TMVerifierStackReadChoice.atomAt,
      tmVerifierStackEmptyAtom_eval_concreteStackAssignment_of_not_selected V p t stk
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
          tmVerifierStackSymbolAtom_eval_concreteStackAssignment_of_not_selected V p t stk
            (u := t) (j := k) (cell := cell) (payload := payload) (by omega)]

theorem tmVerifierStackReadChoiceDomainCNFAt_satisfies_concreteStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hActive : tmVerifierStacksActive V stk)
    (k : tmVerifierStackIndex V) (cell : Nat) :
    CNF.Satisfies (tmVerifierStackReadChoiceDomainCNFAt V t k cell)
      (tmVerifierConcreteStackAssignment V p t stk) := by
  by_cases hcell : cell < (stk k).length
  · exact tmVerifierStackReadChoiceDomainCNFAt_satisfies_concreteStackAssignment_of_lt V p t
      stk hActive k hcell
  · exact tmVerifierStackReadChoiceDomainCNFAt_satisfies_concreteStackAssignment_of_tail V p t
      stk k (Nat.le_of_not_gt hcell)

theorem tmVerifierStackCellDomainsCNFAt_satisfies_concreteStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hActive : tmVerifierStacksActive V stk)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k)
      (tmVerifierConcreteStackAssignment V p t stk) := by
  intro c hc
  rw [tmVerifierStackCellDomainsCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨cell, _hcell, hc⟩
  exact tmVerifierStackReadChoiceDomainCNFAt_satisfies_concreteStackAssignment V p t stk
    hActive k cell c hc

theorem tmVerifierStackEmptyTailCNFAt_satisfies_concreteStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierStackEmptyTailCNFAt V p t k)
      (tmVerifierConcreteStackAssignment V p t stk) := by
  intro c hc
  rw [tmVerifierStackEmptyTailCNFAt] at hc
  rcases List.mem_map.mp hc with ⟨cell, hcell, rfl⟩
  by_cases hselected : cell < (stk k).length
  · refine ⟨Clause.negate (tmVerifierStackEmptyAtom V t k cell), ?_, ?_⟩
    · simp [tmVerifierStackEmptyTailClause, tmVerifierImplicationClause]
    · exact (Clause.negate_eval_true_iff (tmVerifierStackEmptyAtom V t k cell)
        (tmVerifierConcreteStackAssignment V p t stk)).2
        (tmVerifierStackEmptyAtom_eval_concreteStackAssignment_of_selected V p t stk k
          hselected)
  · refine ⟨tmVerifierStackEmptyAtom V t k (cell + 1), ?_, ?_⟩
    · simp [tmVerifierStackEmptyTailClause, tmVerifierImplicationClause]
    · exact tmVerifierStackEmptyAtom_eval_concreteStackAssignment_of_not_selected V p t stk
        (u := t) (j := k) (cell := cell + 1) (by
          intro h
          exact hselected (by omega))

theorem tmVerifierStackFinalEmptyCNFAt_satisfies_concreteStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (k : tmVerifierStackIndex V)
    (hlen : (stk k).length ≤ tmVerifierCellBound V p) :
    CNF.Satisfies (tmVerifierStackFinalEmptyCNFAt V p t k)
      (tmVerifierConcreteStackAssignment V p t stk) := by
  intro c hc
  have hc' :
      c = [tmVerifierStackEmptyAtom V t k (tmVerifierCellBound V p)] := by
    simpa [tmVerifierStackFinalEmptyCNFAt] using hc
  subst c
  refine ⟨tmVerifierStackEmptyAtom V t k (tmVerifierCellBound V p), by simp, ?_⟩
  exact tmVerifierStackEmptyAtom_eval_concreteStackAssignment_of_not_selected V p t stk
    (u := t) (j := k) (cell := tmVerifierCellBound V p) (by
      intro h
      omega)

theorem tmVerifierStackWellFormedCNFAt_satisfies_concreteStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hActive : tmVerifierStacksActive V stk)
    (k : tmVerifierStackIndex V)
    (hlen : (stk k).length ≤ tmVerifierCellBound V p) :
    CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p t k)
      (tmVerifierConcreteStackAssignment V p t stk) := by
  rw [tmVerifierStackWellFormedCNFAt, CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    exact
      ⟨tmVerifierStackCellDomainsCNFAt_satisfies_concreteStackAssignment V p t stk
          hActive k,
        tmVerifierStackEmptyTailCNFAt_satisfies_concreteStackAssignment V p t stk k⟩
  · exact tmVerifierStackFinalEmptyCNFAt_satisfies_concreteStackAssignment V p t stk k
      hlen

theorem tmVerifierAllStackWellFormedCNFAt_satisfies_concreteStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hActive : tmVerifierStacksActive V stk)
    (hlen : ∀ k : tmVerifierStackIndex V, (stk k).length ≤ tmVerifierCellBound V p) :
    CNF.Satisfies (tmVerifierAllStackWellFormedCNFAt V p t)
      (tmVerifierConcreteStackAssignment V p t stk) := by
  intro c hc
  rw [tmVerifierAllStackWellFormedCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨k, _hk, hc⟩
  exact tmVerifierStackWellFormedCNFAt_satisfies_concreteStackAssignment V p t stk
    hActive k (hlen k) c hc

end SAT
end ComplexityReduction
