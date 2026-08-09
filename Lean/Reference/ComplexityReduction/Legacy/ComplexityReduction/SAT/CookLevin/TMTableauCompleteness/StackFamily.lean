/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.ConcreteStack

namespace ComplexityReduction
namespace SAT

/-! ### Stack-family assignments indexed by tableau time -/

noncomputable def tmVerifierStackFamilyAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k)) :
    Assignment := by
  classical
  exact fun var =>
    if ∃ u k cell, ∃ hcell : cell < (stkAt u k).length,
        var =
          (tmVerifierStackSymbolAtom V u k cell
            (tmVerifierActiveStackSymbolPayload V k ((stkAt u k)[cell]'hcell))).var then
      true
    else if ∃ u k cell, ∃ hcell : cell < (stkAt u k).length,
        var = (tmVerifierStackEmptyAtom V u k cell).var then
      false
    else if ∃ u k cell, var = (tmVerifierStackEmptyAtom V u k cell).var then
      true
    else if ∃ u k cell payload,
        var = (tmVerifierStackSymbolAtom V u k cell payload).var then
      false
    else
      tmVerifierControlBoundaryAssignment V p var

theorem tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_selected
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (t : Nat) (k : tmVerifierStackIndex V) {cell : Nat}
    (hcell : cell < (stkAt t k).length) :
    (tmVerifierStackSymbolAtom V t k cell
        (tmVerifierActiveStackSymbolPayload V k ((stkAt t k)[cell]'hcell))).eval
      (tmVerifierStackFamilyAssignment V p stkAt) = true := by
  classical
  change tmVerifierStackFamilyAssignment V p stkAt
    (tmVerifierStackSymbolAtom V t k cell
      (tmVerifierActiveStackSymbolPayload V k ((stkAt t k)[cell]'hcell))).var = true
  have hSelected :
      ∃ u j i, ∃ hi : i < (stkAt u j).length,
        (tmVerifierStackSymbolAtom V t k cell
            (tmVerifierActiveStackSymbolPayload V k ((stkAt t k)[cell]'hcell))).var =
          (tmVerifierStackSymbolAtom V u j i
            (tmVerifierActiveStackSymbolPayload V j ((stkAt u j)[i]'hi))).var :=
    ⟨t, k, cell, hcell, rfl⟩
  rw [tmVerifierStackFamilyAssignment, if_pos hSelected]

theorem tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_selected
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (t : Nat) (k : tmVerifierStackIndex V) {cell : Nat}
    (hcell : cell < (stkAt t k).length) :
    (tmVerifierStackEmptyAtom V t k cell).eval
      (tmVerifierStackFamilyAssignment V p stkAt) = false := by
  classical
  change tmVerifierStackFamilyAssignment V p stkAt
    (tmVerifierStackEmptyAtom V t k cell).var = false
  have hNoSymbol :
      ¬ ∃ u j i, ∃ hi : i < (stkAt u j).length,
        (tmVerifierStackEmptyAtom V t k cell).var =
          (tmVerifierStackSymbolAtom V u j i
            (tmVerifierActiveStackSymbolPayload V j ((stkAt u j)[i]'hi))).var := by
    rintro ⟨u, j, i, hi, h⟩
    exact tmVerifierStackEmptyAtom_var_ne_stackSymbolAtom_var V t u k j cell i
      (tmVerifierActiveStackSymbolPayload V j ((stkAt u j)[i]'hi)) h
  have hSelectedEmpty :
      ∃ u j i, ∃ hi : i < (stkAt u j).length,
        (tmVerifierStackEmptyAtom V t k cell).var =
          (tmVerifierStackEmptyAtom V u j i).var :=
    ⟨t, k, cell, hcell, rfl⟩
  rw [tmVerifierStackFamilyAssignment, if_neg hNoSymbol, if_pos hSelectedEmpty]

theorem tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_not_selected
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    {u : Nat} {j : tmVerifierStackIndex V} {cell : Nat}
    (hnot : ¬ cell < (stkAt u j).length) :
    (tmVerifierStackEmptyAtom V u j cell).eval
      (tmVerifierStackFamilyAssignment V p stkAt) = true := by
  classical
  change tmVerifierStackFamilyAssignment V p stkAt
    (tmVerifierStackEmptyAtom V u j cell).var = true
  have hNoSymbol :
      ¬ ∃ t k i, ∃ hi : i < (stkAt t k).length,
        (tmVerifierStackEmptyAtom V u j cell).var =
          (tmVerifierStackSymbolAtom V t k i
            (tmVerifierActiveStackSymbolPayload V k ((stkAt t k)[i]'hi))).var := by
    rintro ⟨t, k, i, hi, h⟩
    exact tmVerifierStackEmptyAtom_var_ne_stackSymbolAtom_var V u t j k cell i
      (tmVerifierActiveStackSymbolPayload V k ((stkAt t k)[i]'hi)) h
  have hNoSelectedEmpty :
      ¬ ∃ t k i, ∃ hi : i < (stkAt t k).length,
        (tmVerifierStackEmptyAtom V u j cell).var =
          (tmVerifierStackEmptyAtom V t k i).var := by
    rintro ⟨t, k, i, hi, h⟩
    rcases tmVerifierStackEmptyAtom_var_eq V h with ⟨hut, hjk, hcelli⟩
    subst t
    subst k
    subst i
    exact hnot hi
  have hAnyEmpty :
      ∃ t k i, (tmVerifierStackEmptyAtom V u j cell).var =
        (tmVerifierStackEmptyAtom V t k i).var :=
    ⟨u, j, cell, rfl⟩
  rw [tmVerifierStackFamilyAssignment, if_neg hNoSymbol, if_neg hNoSelectedEmpty,
    if_pos hAnyEmpty]

theorem tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_not_selected
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    {u : Nat} {j : tmVerifierStackIndex V} {cell payload : Nat}
    (hnot : ¬ cell < (stkAt u j).length) :
    (tmVerifierStackSymbolAtom V u j cell payload).eval
      (tmVerifierStackFamilyAssignment V p stkAt) = false := by
  classical
  change tmVerifierStackFamilyAssignment V p stkAt
    (tmVerifierStackSymbolAtom V u j cell payload).var = false
  have hNoSelected :
      ¬ ∃ t k i, ∃ hi : i < (stkAt t k).length,
        (tmVerifierStackSymbolAtom V u j cell payload).var =
          (tmVerifierStackSymbolAtom V t k i
            (tmVerifierActiveStackSymbolPayload V k ((stkAt t k)[i]'hi))).var := by
    rintro ⟨t, k, i, hi, h⟩
    rcases tmVerifierStackSymbolAtom_var_eq V h with ⟨hut, hStack, hcelli, _hPayload⟩
    have hjk : j = k := tmVerifierStackCode_injective V hStack
    subst t
    subst k
    subst i
    exact hnot hi
  have hNoSelectedEmpty :
      ¬ ∃ t k i, ∃ hi : i < (stkAt t k).length,
        (tmVerifierStackSymbolAtom V u j cell payload).var =
          (tmVerifierStackEmptyAtom V t k i).var := by
    rintro ⟨t, k, i, hi, h⟩
    exact tmVerifierStackSymbolAtom_var_ne_stackEmptyAtom_var V u t j k cell i payload h
  have hNoAnyEmpty :
      ¬ ∃ t k i,
        (tmVerifierStackSymbolAtom V u j cell payload).var =
          (tmVerifierStackEmptyAtom V t k i).var := by
    rintro ⟨t, k, i, h⟩
    exact tmVerifierStackSymbolAtom_var_ne_stackEmptyAtom_var V u t j k cell i payload h
  have hAnySymbol :
      ∃ t k i payload',
        (tmVerifierStackSymbolAtom V u j cell payload).var =
          (tmVerifierStackSymbolAtom V t k i payload').var :=
    ⟨u, j, cell, payload, rfl⟩
  rw [tmVerifierStackFamilyAssignment, if_neg hNoSelected, if_neg hNoSelectedEmpty,
    if_neg hNoAnyEmpty, if_pos hAnySymbol]

theorem tmVerifierStackSymbolAtom_payload_eq_of_eval_stackFamilyAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (t : Nat) (k : tmVerifierStackIndex V) {cell payload : Nat}
    (hcell : cell < (stkAt t k).length)
    (htrue :
      (tmVerifierStackSymbolAtom V t k cell payload).eval
        (tmVerifierStackFamilyAssignment V p stkAt) = true) :
    payload = tmVerifierActiveStackSymbolPayload V k ((stkAt t k)[cell]'hcell) := by
  classical
  change tmVerifierStackFamilyAssignment V p stkAt
    (tmVerifierStackSymbolAtom V t k cell payload).var = true at htrue
  by_cases hSelected :
      ∃ u j i, ∃ hi : i < (stkAt u j).length,
        (tmVerifierStackSymbolAtom V t k cell payload).var =
          (tmVerifierStackSymbolAtom V u j i
            (tmVerifierActiveStackSymbolPayload V j ((stkAt u j)[i]'hi))).var
  · rcases hSelected with ⟨u, j, i, hi, hvar⟩
    rcases tmVerifierStackSymbolAtom_var_eq V hvar with
      ⟨htu, hStack, hcelli, hpayload⟩
    have hkj : k = j := tmVerifierStackCode_injective V hStack
    subst u
    subst j
    subst i
    simpa using hpayload
  · have hNoSelectedEmpty :
        ¬ ∃ u j i, ∃ hi : i < (stkAt u j).length,
          (tmVerifierStackSymbolAtom V t k cell payload).var =
            (tmVerifierStackEmptyAtom V u j i).var := by
      rintro ⟨u, j, i, hi, h⟩
      exact tmVerifierStackSymbolAtom_var_ne_stackEmptyAtom_var V t u k j cell i payload h
    have hNoAnyEmpty :
        ¬ ∃ u j i,
          (tmVerifierStackSymbolAtom V t k cell payload).var =
            (tmVerifierStackEmptyAtom V u j i).var := by
      rintro ⟨u, j, i, h⟩
      exact tmVerifierStackSymbolAtom_var_ne_stackEmptyAtom_var V t u k j cell i payload h
    have hAnySymbol :
        ∃ u j i payload',
          (tmVerifierStackSymbolAtom V t k cell payload).var =
            (tmVerifierStackSymbolAtom V u j i payload').var :=
      ⟨t, k, cell, payload, rfl⟩
    have hfalse :
        tmVerifierStackFamilyAssignment V p stkAt
          (tmVerifierStackSymbolAtom V t k cell payload).var = false := by
      rw [tmVerifierStackFamilyAssignment, if_neg hSelected, if_neg hNoSelectedEmpty,
        if_neg hNoAnyEmpty, if_pos hAnySymbol]
    simp [hfalse] at htrue

theorem tmVerifierStackReadChoiceDomainCNFAt_satisfies_stackFamilyAssignment_of_lt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (t : Nat) (hActive : tmVerifierStacksActive V (stkAt t))
    (k : tmVerifierStackIndex V) {cell : Nat}
    (hcell : cell < (stkAt t k).length) :
    CNF.Satisfies (tmVerifierStackReadChoiceDomainCNFAt V t k cell)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  let selected :=
    TMVerifierStackReadChoice.symbol (V := V) (k := k)
      (tmVerifierActiveStackSymbolPayload V k ((stkAt t k)[cell]'hcell))
      ((stkAt t k)[cell]'hcell)
  apply CookLevin.exactlyOneCNF_satisfies_of_exists_unique
  · exact tmVerifierStackReadChoiceLiteralsAt_nodup V t k cell
  · exact
      ⟨TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell selected, by
        rw [tmVerifierStackReadChoiceLiteralsAt]
        exact List.mem_map.mpr
          ⟨selected, tmVerifierConcreteStack_word_payload_mem V (stkAt t) hActive k cell
            hcell, rfl⟩, by
        simp [selected, TMVerifierStackReadChoice.atomAt,
          tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_selected V p stkAt t k
            hcell]⟩
  · intro x hx y hy hxTrue hyTrue
    rcases List.mem_map.mp hx with ⟨choice₁, hchoice₁, rfl⟩
    rcases List.mem_map.mp hy with ⟨choice₂, hchoice₂, rfl⟩
    cases choice₁ with
    | empty =>
        have hxFalse :=
          tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_selected V p stkAt t k hcell
        simp [TMVerifierStackReadChoice.atomAt, hxFalse] at hxTrue
    | symbol payload₁ symbol₁ =>
        cases choice₂ with
        | empty =>
            have hyFalse :=
              tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_selected V p stkAt t k
                hcell
            simp [TMVerifierStackReadChoice.atomAt, hyFalse] at hyTrue
        | symbol payload₂ symbol₂ =>
            have hp₁ :
                payload₁ = tmVerifierActiveStackSymbolPayload V k
                  ((stkAt t k)[cell]'hcell) :=
              tmVerifierStackSymbolAtom_payload_eq_of_eval_stackFamilyAssignment V p stkAt t
                k hcell hxTrue
            have hp₂ :
                payload₂ = tmVerifierActiveStackSymbolPayload V k
                  ((stkAt t k)[cell]'hcell) :=
              tmVerifierStackSymbolAtom_payload_eq_of_eval_stackFamilyAssignment V p stkAt t
                k hcell hyTrue
            subst payload₁
            subst payload₂
            have hsym :
                symbol₁ = symbol₂ :=
              tmVerifierStackReadChoice_symbol_eq_of_payloadUnique V
                (tmVerifierStackPayloadUnique V) k
                (tmVerifierActiveStackSymbolPayload V k ((stkAt t k)[cell]'hcell))
                symbol₁ symbol₂ hchoice₁ hchoice₂
            subst symbol₂
            rfl

theorem tmVerifierStackReadChoiceDomainCNFAt_satisfies_stackFamilyAssignment_of_tail
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (t : Nat) (k : tmVerifierStackIndex V) {cell : Nat}
    (hcell : (stkAt t k).length ≤ cell) :
    CNF.Satisfies (tmVerifierStackReadChoiceDomainCNFAt V t k cell)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  rw [tmVerifierStackReadChoiceDomainCNFAt, tmVerifierStackReadChoiceLiteralsAt,
    tmVerifierStackReadChoices]
  apply CookLevin.exactlyOneCNF_satisfies_cons_of_head_true_tail_false
  · simp [TMVerifierStackReadChoice.atomAt,
      tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_not_selected V p stkAt
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
          tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_not_selected V p stkAt
            (u := t) (j := k) (cell := cell) (payload := payload) (by omega)]

theorem tmVerifierStackReadChoiceDomainCNFAt_satisfies_stackFamilyAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (t : Nat) (hActive : tmVerifierStacksActive V (stkAt t))
    (k : tmVerifierStackIndex V) (cell : Nat) :
    CNF.Satisfies (tmVerifierStackReadChoiceDomainCNFAt V t k cell)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  by_cases hcell : cell < (stkAt t k).length
  · exact tmVerifierStackReadChoiceDomainCNFAt_satisfies_stackFamilyAssignment_of_lt V p
      stkAt t hActive k hcell
  · exact tmVerifierStackReadChoiceDomainCNFAt_satisfies_stackFamilyAssignment_of_tail V p
      stkAt t k (Nat.le_of_not_gt hcell)

theorem tmVerifierStackCellDomainsCNFAt_satisfies_stackFamilyAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (t : Nat) (hActive : tmVerifierStacksActive V (stkAt t))
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  intro c hc
  rw [tmVerifierStackCellDomainsCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨cell, _hcell, hc⟩
  exact tmVerifierStackReadChoiceDomainCNFAt_satisfies_stackFamilyAssignment V p stkAt
    t hActive k cell c hc

theorem tmVerifierStackEmptyTailCNFAt_satisfies_stackFamilyAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (t : Nat) (k : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierStackEmptyTailCNFAt V p t k)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  intro c hc
  rw [tmVerifierStackEmptyTailCNFAt] at hc
  rcases List.mem_map.mp hc with ⟨cell, hcell, rfl⟩
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

theorem tmVerifierStackFinalEmptyCNFAt_satisfies_stackFamilyAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (t : Nat) (k : tmVerifierStackIndex V)
    (hlen : (stkAt t k).length ≤ tmVerifierCellBound V p) :
    CNF.Satisfies (tmVerifierStackFinalEmptyCNFAt V p t k)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  intro c hc
  have hc' :
      c = [tmVerifierStackEmptyAtom V t k (tmVerifierCellBound V p)] := by
    simpa [tmVerifierStackFinalEmptyCNFAt] using hc
  subst c
  refine ⟨tmVerifierStackEmptyAtom V t k (tmVerifierCellBound V p), by simp, ?_⟩
  exact tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_not_selected V p stkAt
    (u := t) (j := k) (cell := tmVerifierCellBound V p) (by
      intro h
      omega)

theorem tmVerifierStackWellFormedCNFAt_satisfies_stackFamilyAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (t : Nat) (k : tmVerifierStackIndex V)
    (hActive : tmVerifierStacksActive V (stkAt t))
    (hlen : (stkAt t k).length ≤ tmVerifierCellBound V p) :
    CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p t k)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  rw [tmVerifierStackWellFormedCNFAt, CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    exact
      ⟨tmVerifierStackCellDomainsCNFAt_satisfies_stackFamilyAssignment V p stkAt
          t hActive k,
        tmVerifierStackEmptyTailCNFAt_satisfies_stackFamilyAssignment V p stkAt t k⟩
  · exact tmVerifierStackFinalEmptyCNFAt_satisfies_stackFamilyAssignment V p stkAt t k
      hlen

theorem tmVerifierAllStackWellFormedCNFAt_satisfies_stackFamilyAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (t : Nat)
    (hActive : tmVerifierStacksActive V (stkAt t))
    (hlen : ∀ k : tmVerifierStackIndex V, (stkAt t k).length ≤ tmVerifierCellBound V p) :
    CNF.Satisfies (tmVerifierAllStackWellFormedCNFAt V p t)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  intro c hc
  rw [tmVerifierAllStackWellFormedCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨k, _hk, hc⟩
  exact tmVerifierStackWellFormedCNFAt_satisfies_stackFamilyAssignment V p stkAt t k
    hActive (hlen k) c hc

end SAT
end ComplexityReduction
