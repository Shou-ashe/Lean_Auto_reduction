/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.ControlBoundary

namespace ComplexityReduction
namespace SAT

/-! ### Empty-stack exact-one assignment -/

noncomputable def tmVerifierControlEmptyStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) : Assignment :=
  by
    classical
    exact fun var =>
      if ∃ t k cell, var = (tmVerifierStackEmptyAtom V t k cell).var then
        true
      else if ∃ t k cell payload, var = (tmVerifierStackSymbolAtom V t k cell payload).var then
        false
      else
        tmVerifierControlBoundaryAssignment V p var

theorem tmVerifierStackEmptyAtom_eval_controlEmptyStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) :
    (tmVerifierStackEmptyAtom V t k cell).eval
      (tmVerifierControlEmptyStackAssignment V p) = true := by
  classical
  change tmVerifierControlEmptyStackAssignment V p
    (tmVerifierStackEmptyAtom V t k cell).var = true
  have hEmpty : ∃ u j cell',
      (tmVerifierStackEmptyAtom V t k cell).var =
        (tmVerifierStackEmptyAtom V u j cell').var := ⟨t, k, cell, rfl⟩
  simp [tmVerifierControlEmptyStackAssignment, hEmpty]

theorem tmVerifierStackSymbolAtom_eval_controlEmptyStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (cell payload : Nat) :
    (tmVerifierStackSymbolAtom V t k cell payload).eval
      (tmVerifierControlEmptyStackAssignment V p) = false := by
  classical
  change tmVerifierControlEmptyStackAssignment V p
    (tmVerifierStackSymbolAtom V t k cell payload).var = false
  have hNoEmpty : ¬ ∃ u j cell',
      (tmVerifierStackSymbolAtom V t k cell payload).var =
        (tmVerifierStackEmptyAtom V u j cell').var := by
    rintro ⟨u, j, cell', h⟩
    exact tmVerifierStackSymbolAtom_var_ne_stackEmptyAtom_var V t u k j cell cell' payload h
  have hSymbol : ∃ u j cell' payload',
      (tmVerifierStackSymbolAtom V t k cell payload).var =
        (tmVerifierStackSymbolAtom V u j cell' payload').var :=
    ⟨t, k, cell, payload, rfl⟩
  simp [tmVerifierControlEmptyStackAssignment, hNoEmpty, hSymbol]

theorem tmVerifierLabelAtom_eval_controlEmptyStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (label : Option (tmVerifierTM V).Λ) :
    (tmVerifierLabelAtom V t label).eval (tmVerifierControlEmptyStackAssignment V p) =
      (tmVerifierLabelAtom V t label).eval (tmVerifierControlBoundaryAssignment V p) := by
  classical
  change tmVerifierControlEmptyStackAssignment V p (tmVerifierLabelAtom V t label).var =
    tmVerifierControlBoundaryAssignment V p (tmVerifierLabelAtom V t label).var
  have hNoEmpty : ¬ ∃ u k cell, (tmVerifierLabelAtom V t label).var =
      (tmVerifierStackEmptyAtom V u k cell).var := by
    rintro ⟨u, k, cell, h⟩
    exact tmVerifierStackEmptyAtom_var_ne_labelAtom_var V u t k cell label h.symm
  have hNoSymbol : ¬ ∃ u k cell payload, (tmVerifierLabelAtom V t label).var =
      (tmVerifierStackSymbolAtom V u k cell payload).var := by
    rintro ⟨u, k, cell, payload, h⟩
    exact tmVerifierStackSymbolAtom_var_ne_labelAtom_var V u t k cell payload label h.symm
  simp [tmVerifierControlEmptyStackAssignment, hNoEmpty, hNoSymbol]

theorem tmVerifierStateAtom_eval_controlEmptyStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (state : (tmVerifierTM V).σ) :
    (tmVerifierStateAtom V t state).eval (tmVerifierControlEmptyStackAssignment V p) =
      (tmVerifierStateAtom V t state).eval (tmVerifierControlBoundaryAssignment V p) := by
  classical
  change tmVerifierControlEmptyStackAssignment V p (tmVerifierStateAtom V t state).var =
    tmVerifierControlBoundaryAssignment V p (tmVerifierStateAtom V t state).var
  have hNoEmpty : ¬ ∃ u k cell, (tmVerifierStateAtom V t state).var =
      (tmVerifierStackEmptyAtom V u k cell).var := by
    rintro ⟨u, k, cell, h⟩
    exact tmVerifierStackEmptyAtom_var_ne_stateAtom_var V u t k cell state h.symm
  have hNoSymbol : ¬ ∃ u k cell payload, (tmVerifierStateAtom V t state).var =
      (tmVerifierStackSymbolAtom V u k cell payload).var := by
    rintro ⟨u, k, cell, payload, h⟩
    exact tmVerifierStackSymbolAtom_var_ne_stateAtom_var V u t k cell payload state h.symm
  simp [tmVerifierControlEmptyStackAssignment, hNoEmpty, hNoSymbol]

theorem tmVerifierActiveReadChoice_atom_eval_controlEmptyStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k)
    (hchoice : choice ∈ tmVerifierActiveReadChoices V k) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice).eval
      (tmVerifierControlEmptyStackAssignment V p) = false := by
  rw [tmVerifierActiveReadChoices] at hchoice
  rcases List.mem_filterMap.mp hchoice with ⟨named, _hNamed, hSome⟩
  unfold tmVerifierActiveReadChoiceOfNamed? at hSome
  by_cases hStack : named.stack = k
  · rw [dif_pos hStack] at hSome
    cases hStack
    cases hSome
    simp [TMVerifierStackReadChoice.atomAt,
      tmVerifierStackSymbolAtom_eval_controlEmptyStackAssignment]
  · rw [dif_neg hStack] at hSome
    simp at hSome

theorem tmVerifierStackReadChoiceDomainCNFAt_satisfies_controlEmptyStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) :
    CNF.Satisfies (tmVerifierStackReadChoiceDomainCNFAt V t k cell)
      (tmVerifierControlEmptyStackAssignment V p) := by
  rw [tmVerifierStackReadChoiceDomainCNFAt, tmVerifierStackReadChoiceLiteralsAt,
    tmVerifierStackReadChoices]
  apply CookLevin.exactlyOneCNF_satisfies_cons_of_head_true_tail_false
  · simp [TMVerifierStackReadChoice.atomAt,
      tmVerifierStackEmptyAtom_eval_controlEmptyStackAssignment]
  · intro y hy
    rcases List.mem_map.mp hy with ⟨choice, hchoice, rfl⟩
    exact tmVerifierActiveReadChoice_atom_eval_controlEmptyStackAssignment V p t k cell choice
      hchoice

theorem tmVerifierStackCellDomainCNFAt_satisfies_controlEmptyStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) :
    CNF.Satisfies (tmVerifierStackCellDomainCNFAt V t k cell)
      (tmVerifierControlEmptyStackAssignment V p) :=
  tmVerifierStackReadChoiceDomainCNFAt_satisfies_controlEmptyStackAssignment V p t k cell

theorem tmVerifierStackCellDomainsCNFAt_satisfies_controlEmptyStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k)
      (tmVerifierControlEmptyStackAssignment V p) := by
  intro c hc
  rw [tmVerifierStackCellDomainsCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨cell, _hcell, hc⟩
  exact tmVerifierStackCellDomainCNFAt_satisfies_controlEmptyStackAssignment V p t k cell c hc

theorem tmVerifierStackEmptyTailCNFAt_satisfies_controlEmptyStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierStackEmptyTailCNFAt V p t k)
      (tmVerifierControlEmptyStackAssignment V p) := by
  intro c hc
  rw [tmVerifierStackEmptyTailCNFAt] at hc
  rcases List.mem_map.mp hc with ⟨cell, _hcell, rfl⟩
  refine ⟨tmVerifierStackEmptyAtom V t k (cell + 1), ?_, ?_⟩
  · simp [tmVerifierStackEmptyTailClause, tmVerifierImplicationClause]
  · exact tmVerifierStackEmptyAtom_eval_controlEmptyStackAssignment V p t k (cell + 1)

theorem tmVerifierStackFinalEmptyCNFAt_satisfies_controlEmptyStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierStackFinalEmptyCNFAt V p t k)
      (tmVerifierControlEmptyStackAssignment V p) := by
  intro c hc
  have hc' :
      c = [tmVerifierStackEmptyAtom V t k (tmVerifierCellBound V p)] := by
    simpa [tmVerifierStackFinalEmptyCNFAt] using hc
  subst c
  exact ⟨tmVerifierStackEmptyAtom V t k (tmVerifierCellBound V p), by simp,
    tmVerifierStackEmptyAtom_eval_controlEmptyStackAssignment V p t k
      (tmVerifierCellBound V p)⟩

theorem tmVerifierStackWellFormedCNFAt_satisfies_controlEmptyStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p t k)
      (tmVerifierControlEmptyStackAssignment V p) := by
  rw [tmVerifierStackWellFormedCNFAt, CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    exact
      ⟨tmVerifierStackCellDomainsCNFAt_satisfies_controlEmptyStackAssignment V p t k,
        tmVerifierStackEmptyTailCNFAt_satisfies_controlEmptyStackAssignment V p t k⟩
  · exact tmVerifierStackFinalEmptyCNFAt_satisfies_controlEmptyStackAssignment V p t k

theorem tmVerifierAllStackWellFormedCNFAt_satisfies_controlEmptyStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) :
    CNF.Satisfies (tmVerifierAllStackWellFormedCNFAt V p t)
      (tmVerifierControlEmptyStackAssignment V p) := by
  intro c hc
  rw [tmVerifierAllStackWellFormedCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨k, _hk, hc⟩
  exact tmVerifierStackWellFormedCNFAt_satisfies_controlEmptyStackAssignment V p t k c hc

theorem tmVerifierControlDomainRowsCNF_satisfies_controlEmptyStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) :
    CNF.Satisfies (tmVerifierControlDomainRowsCNF V p)
      (tmVerifierControlEmptyStackAssignment V p) := by
  intro c hc
  rw [tmVerifierControlDomainRowsCNF] at hc
  rcases List.mem_flatMap.mp hc with ⟨t, _ht, hc⟩
  have hRow : CNF.Satisfies (tmVerifierControlDomainCNFAt V t)
      (tmVerifierControlEmptyStackAssignment V p) := by
    rw [tmVerifierControlDomainCNFAt, CNF.satisfies_append]
    constructor
    · let selected := (tmVerifierRunCfgAt V p t).l
      apply CookLevin.exactlyOneCNF_satisfies_of_exists_unique
      · exact tmVerifierLabelAtomsAt_nodup V t
      · exact ⟨tmVerifierLabelAtom V t selected, tmVerifierLabelAtomsAt_mem V t selected, by
          simpa [tmVerifierLabelAtom_eval_controlEmptyStackAssignment] using
            (tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff V p t selected).2 rfl⟩
      · intro x hx y hy hxTrue hyTrue
        rcases List.mem_map.mp hx with ⟨label₁, _hlabel₁, rfl⟩
        rcases List.mem_map.mp hy with ⟨label₂, _hlabel₂, rfl⟩
        have h₁ := (tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff V p t label₁).1
          (by
            rw [← tmVerifierLabelAtom_eval_controlEmptyStackAssignment]
            exact hxTrue)
        have h₂ := (tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff V p t label₂).1
          (by
            rw [← tmVerifierLabelAtom_eval_controlEmptyStackAssignment]
            exact hyTrue)
        exact congrArg (tmVerifierLabelAtom V t) (h₁.trans h₂.symm)
    · let selected := (tmVerifierRunCfgAt V p t).var
      apply CookLevin.exactlyOneCNF_satisfies_of_exists_unique
      · exact tmVerifierStateAtomsAt_nodup V t
      · exact ⟨tmVerifierStateAtom V t selected, tmVerifierStateAtomsAt_mem V t selected, by
          simpa [tmVerifierStateAtom_eval_controlEmptyStackAssignment] using
            (tmVerifierStateAtom_eval_controlBoundaryAssignment_iff V p t selected).2 rfl⟩
      · intro x hx y hy hxTrue hyTrue
        rcases List.mem_map.mp hx with ⟨state₁, _hstate₁, rfl⟩
        rcases List.mem_map.mp hy with ⟨state₂, _hstate₂, rfl⟩
        have h₁ := (tmVerifierStateAtom_eval_controlBoundaryAssignment_iff V p t state₁).1
          (by
            rw [← tmVerifierStateAtom_eval_controlEmptyStackAssignment]
            exact hxTrue)
        have h₂ := (tmVerifierStateAtom_eval_controlBoundaryAssignment_iff V p t state₂).1
          (by
            rw [← tmVerifierStateAtom_eval_controlEmptyStackAssignment]
            exact hyTrue)
        exact congrArg (tmVerifierStateAtom V t) (h₁.trans h₂.symm)
  exact hRow c hc

/-! ### One nonempty word stack row -/

noncomputable def tmVerifierControlWordStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V)
    (word : List ((tmVerifierTM V).Γ k))
    (payload : (tmVerifierTM V).Γ k → Nat) : Assignment :=
  by
    classical
    exact fun var =>
      if ∃ cell, ∃ hcell : cell < word.length,
          var = (tmVerifierStackSymbolAtom V t k cell (payload word[cell])).var then
        true
      else if ∃ cell, ∃ hcell : cell < word.length,
          var = (tmVerifierStackEmptyAtom V t k cell).var then
        false
      else if ∃ u j cell, var = (tmVerifierStackEmptyAtom V u j cell).var then
        true
      else if ∃ u j cell payload',
          var = (tmVerifierStackSymbolAtom V u j cell payload').var then
        false
      else
        tmVerifierControlBoundaryAssignment V p var

theorem tmVerifierStackEmptyAtom_eval_controlWordStackAssignment_of_selected
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V)
    (word : List ((tmVerifierTM V).Γ k))
    (payload : (tmVerifierTM V).Γ k → Nat)
    {cell : Nat} (hcell : cell < word.length) :
    (tmVerifierStackEmptyAtom V t k cell).eval
      (tmVerifierControlWordStackAssignment V p t k word payload) = false := by
  classical
  change tmVerifierControlWordStackAssignment V p t k word payload
    (tmVerifierStackEmptyAtom V t k cell).var = false
  have hNoSymbol : ¬ ∃ i, ∃ hi : i < word.length,
      (tmVerifierStackEmptyAtom V t k cell).var =
        (tmVerifierStackSymbolAtom V t k i (payload word[i])).var := by
    rintro ⟨i, hi, h⟩
    exact tmVerifierStackEmptyAtom_var_ne_stackSymbolAtom_var V t t k k cell i
      (payload word[i]) h
  have hSelectedEmpty : ∃ i, ∃ hi : i < word.length,
      (tmVerifierStackEmptyAtom V t k cell).var =
        (tmVerifierStackEmptyAtom V t k i).var := ⟨cell, hcell, rfl⟩
  rw [tmVerifierControlWordStackAssignment, if_neg hNoSymbol, if_pos hSelectedEmpty]

theorem tmVerifierStackEmptyAtom_eval_controlWordStackAssignment_of_not_selected
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V)
    (word : List ((tmVerifierTM V).Γ k))
    (payload : (tmVerifierTM V).Γ k → Nat)
    {u : Nat} {j : tmVerifierStackIndex V} {cell : Nat}
    (hnot : ¬ (u = t ∧ j = k ∧ cell < word.length)) :
    (tmVerifierStackEmptyAtom V u j cell).eval
      (tmVerifierControlWordStackAssignment V p t k word payload) = true := by
  classical
  change tmVerifierControlWordStackAssignment V p t k word payload
    (tmVerifierStackEmptyAtom V u j cell).var = true
  have hNoSymbol : ¬ ∃ i, ∃ hi : i < word.length,
      (tmVerifierStackEmptyAtom V u j cell).var =
        (tmVerifierStackSymbolAtom V t k i (payload word[i])).var := by
    rintro ⟨i, hi, h⟩
    exact tmVerifierStackEmptyAtom_var_ne_stackSymbolAtom_var V u t j k cell i
      (payload word[i]) h
  have hNoSelectedEmpty : ¬ ∃ i, ∃ hi : i < word.length,
      (tmVerifierStackEmptyAtom V u j cell).var =
        (tmVerifierStackEmptyAtom V t k i).var := by
    rintro ⟨i, hi, h⟩
    rcases tmVerifierStackEmptyAtom_var_eq V h with ⟨hut, hjk, hcelli⟩
    exact hnot ⟨hut, hjk, by simpa [hcelli] using hi⟩
  have hAnyEmpty : ∃ u' j' cell',
      (tmVerifierStackEmptyAtom V u j cell).var =
        (tmVerifierStackEmptyAtom V u' j' cell').var := ⟨u, j, cell, rfl⟩
  rw [tmVerifierControlWordStackAssignment, if_neg hNoSymbol, if_neg hNoSelectedEmpty,
    if_pos hAnyEmpty]

theorem tmVerifierStackSymbolAtom_eval_controlWordStackAssignment_of_selected
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V)
    (word : List ((tmVerifierTM V).Γ k))
    (payload : (tmVerifierTM V).Γ k → Nat)
    {cell : Nat} (hcell : cell < word.length) :
    (tmVerifierStackSymbolAtom V t k cell (payload word[cell])).eval
      (tmVerifierControlWordStackAssignment V p t k word payload) = true := by
  classical
  change tmVerifierControlWordStackAssignment V p t k word payload
    (tmVerifierStackSymbolAtom V t k cell (payload word[cell])).var = true
  have hSelected : ∃ i, ∃ hi : i < word.length,
      (tmVerifierStackSymbolAtom V t k cell (payload word[cell])).var =
        (tmVerifierStackSymbolAtom V t k i (payload word[i])).var :=
    ⟨cell, hcell, rfl⟩
  rw [tmVerifierControlWordStackAssignment, if_pos hSelected]

theorem tmVerifierStackSymbolAtom_eval_controlWordStackAssignment_of_not_selected
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V)
    (word : List ((tmVerifierTM V).Γ k))
    (payload : (tmVerifierTM V).Γ k → Nat)
    {u : Nat} {j : tmVerifierStackIndex V} {cell payload' : Nat}
    (hnot : ¬ (u = t ∧ j = k ∧ cell < word.length)) :
    (tmVerifierStackSymbolAtom V u j cell payload').eval
      (tmVerifierControlWordStackAssignment V p t k word payload) = false := by
  classical
  change tmVerifierControlWordStackAssignment V p t k word payload
    (tmVerifierStackSymbolAtom V u j cell payload').var = false
  have hNoSelected : ¬ ∃ i, ∃ hi : i < word.length,
      (tmVerifierStackSymbolAtom V u j cell payload').var =
        (tmVerifierStackSymbolAtom V t k i (payload word[i])).var := by
    rintro ⟨i, hi, h⟩
    rcases tmVerifierStackSymbolAtom_var_eq V h with ⟨hut, hStack, hcelli, _hPayload⟩
    have hjk : j = k := tmVerifierStackCode_injective V hStack
    exact hnot ⟨hut, hjk, by simpa [hcelli] using hi⟩
  have hNoEmpty : ¬ ∃ i, ∃ hi : i < word.length,
      (tmVerifierStackSymbolAtom V u j cell payload').var =
        (tmVerifierStackEmptyAtom V t k i).var := by
    rintro ⟨i, hi, h⟩
    exact tmVerifierStackSymbolAtom_var_ne_stackEmptyAtom_var V u t j k cell i payload' h
  have hNoAnyEmpty : ¬ ∃ u' j' cell',
      (tmVerifierStackSymbolAtom V u j cell payload').var =
        (tmVerifierStackEmptyAtom V u' j' cell').var := by
    rintro ⟨u', j', cell', h⟩
    exact tmVerifierStackSymbolAtom_var_ne_stackEmptyAtom_var V u u' j j' cell cell'
      payload' h
  have hAnySymbol : ∃ u' j' cell' payload'',
      (tmVerifierStackSymbolAtom V u j cell payload').var =
        (tmVerifierStackSymbolAtom V u' j' cell' payload'').var :=
    ⟨u, j, cell, payload', rfl⟩
  rw [tmVerifierControlWordStackAssignment, if_neg hNoSelected, if_neg hNoEmpty,
    if_neg hNoAnyEmpty, if_pos hAnySymbol]

theorem tmVerifierStackSymbolAtom_payload_eq_of_eval_controlWordStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V)
    (word : List ((tmVerifierTM V).Γ k))
    (payload : (tmVerifierTM V).Γ k → Nat)
    {cell payload' : Nat} (hcell : cell < word.length)
    (htrue :
      (tmVerifierStackSymbolAtom V t k cell payload').eval
        (tmVerifierControlWordStackAssignment V p t k word payload) = true) :
    payload' = payload word[cell] := by
  classical
  change tmVerifierControlWordStackAssignment V p t k word payload
    (tmVerifierStackSymbolAtom V t k cell payload').var = true at htrue
  by_cases hSelected : ∃ i, ∃ hi : i < word.length,
      (tmVerifierStackSymbolAtom V t k cell payload').var =
        (tmVerifierStackSymbolAtom V t k i (payload word[i])).var
  · rcases hSelected with ⟨i, hi, hvar⟩
    rcases tmVerifierStackSymbolAtom_var_eq V hvar with
      ⟨_ht, _hStack, hcelli, hpayload⟩
    subst i
    simpa using hpayload
  · have hNoEmpty : ¬ ∃ i, ∃ hi : i < word.length,
        (tmVerifierStackSymbolAtom V t k cell payload').var =
          (tmVerifierStackEmptyAtom V t k i).var := by
      rintro ⟨i, hi, h⟩
      exact tmVerifierStackSymbolAtom_var_ne_stackEmptyAtom_var V t t k k cell i payload' h
    have hNoAnyEmpty : ¬ ∃ u' j' cell',
        (tmVerifierStackSymbolAtom V t k cell payload').var =
          (tmVerifierStackEmptyAtom V u' j' cell').var := by
      rintro ⟨u', j', cell', h⟩
      exact tmVerifierStackSymbolAtom_var_ne_stackEmptyAtom_var V t u' k j' cell cell'
        payload' h
    have hAnySymbol : ∃ u' j' cell' payload'',
        (tmVerifierStackSymbolAtom V t k cell payload').var =
          (tmVerifierStackSymbolAtom V u' j' cell' payload'').var :=
      ⟨t, k, cell, payload', rfl⟩
    have hfalse :
        tmVerifierControlWordStackAssignment V p t k word payload
          (tmVerifierStackSymbolAtom V t k cell payload').var = false := by
      rw [tmVerifierControlWordStackAssignment, if_neg hSelected, if_neg hNoEmpty,
        if_neg hNoAnyEmpty, if_pos hAnySymbol]
    simp [hfalse] at htrue

theorem tmVerifierStackReadChoiceDomainCNFAt_satisfies_controlWordStackAssignment_of_lt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V)
    (word : List ((tmVerifierTM V).Γ k))
    (payload : (tmVerifierTM V).Γ k → Nat)
    (hPayloadMem :
      ∀ i, (hi : i < word.length) →
        TMVerifierStackReadChoice.symbol (V := V) (k := k) (payload (word[i]'hi))
            (word[i]'hi) ∈
          tmVerifierStackReadChoices V k)
    {cell : Nat} (hcell : cell < word.length) :
    CNF.Satisfies (tmVerifierStackReadChoiceDomainCNFAt V t k cell)
      (tmVerifierControlWordStackAssignment V p t k word payload) := by
  let selected :=
    TMVerifierStackReadChoice.symbol (V := V) (k := k)
      (payload (word[cell]'hcell)) (word[cell]'hcell)
  apply CookLevin.exactlyOneCNF_satisfies_of_exists_unique
  · exact tmVerifierStackReadChoiceLiteralsAt_nodup V t k cell
  · exact
      ⟨TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell selected, by
        rw [tmVerifierStackReadChoiceLiteralsAt]
        exact List.mem_map.mpr ⟨selected, hPayloadMem cell hcell, rfl⟩, by
        simp [selected, TMVerifierStackReadChoice.atomAt,
          tmVerifierStackSymbolAtom_eval_controlWordStackAssignment_of_selected V p t k word
            payload hcell]⟩
  · intro x hx y hy hxTrue hyTrue
    rcases List.mem_map.mp hx with ⟨choice₁, hchoice₁, rfl⟩
    rcases List.mem_map.mp hy with ⟨choice₂, hchoice₂, rfl⟩
    cases choice₁ with
    | empty =>
        have hxFalse :=
          tmVerifierStackEmptyAtom_eval_controlWordStackAssignment_of_selected V p t k word
            payload hcell
        simp [TMVerifierStackReadChoice.atomAt, hxFalse] at hxTrue
    | symbol payload₁ symbol₁ =>
        cases choice₂ with
        | empty =>
            have hyFalse :=
              tmVerifierStackEmptyAtom_eval_controlWordStackAssignment_of_selected V p t k word
                payload hcell
            simp [TMVerifierStackReadChoice.atomAt, hyFalse] at hyTrue
        | symbol payload₂ symbol₂ =>
            have hp₁ :
                payload₁ = payload word[cell] :=
              tmVerifierStackSymbolAtom_payload_eq_of_eval_controlWordStackAssignment V p t k
                word payload hcell hxTrue
            have hp₂ :
                payload₂ = payload word[cell] :=
              tmVerifierStackSymbolAtom_payload_eq_of_eval_controlWordStackAssignment V p t k
                word payload hcell hyTrue
            subst payload₁
            subst payload₂
            have hsym :
                symbol₁ = symbol₂ :=
              tmVerifierStackReadChoice_symbol_eq_of_payloadUnique V
                (tmVerifierStackPayloadUnique V) k (payload word[cell]) symbol₁ symbol₂
                hchoice₁ hchoice₂
            subst symbol₂
            rfl

theorem tmVerifierStackReadChoiceDomainCNFAt_satisfies_controlWordStackAssignment_of_tail
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V)
    (word : List ((tmVerifierTM V).Γ k))
    (payload : (tmVerifierTM V).Γ k → Nat)
    {cell : Nat} (hcell : word.length ≤ cell) :
    CNF.Satisfies (tmVerifierStackReadChoiceDomainCNFAt V t k cell)
      (tmVerifierControlWordStackAssignment V p t k word payload) := by
  rw [tmVerifierStackReadChoiceDomainCNFAt, tmVerifierStackReadChoiceLiteralsAt,
    tmVerifierStackReadChoices]
  apply CookLevin.exactlyOneCNF_satisfies_cons_of_head_true_tail_false
  · simp [TMVerifierStackReadChoice.atomAt,
      tmVerifierStackEmptyAtom_eval_controlWordStackAssignment_of_not_selected V p t k word
        payload (u := t) (j := k) (cell := cell) (by omega)]
  · intro y hy
    rcases List.mem_map.mp hy with ⟨choice, hchoice, rfl⟩
    cases choice with
    | empty =>
        exfalso
        rw [tmVerifierActiveReadChoices] at hchoice
        rcases List.mem_filterMap.mp hchoice with ⟨named, _hNamed, hSome⟩
        unfold tmVerifierActiveReadChoiceOfNamed? at hSome
        split at hSome <;> simp at hSome
    | symbol payload' symbol =>
        simp [TMVerifierStackReadChoice.atomAt,
          tmVerifierStackSymbolAtom_eval_controlWordStackAssignment_of_not_selected V p t k
            word payload (u := t) (j := k) (cell := cell) (payload' := payload')
            (by omega)]

theorem tmVerifierStackReadChoiceDomainCNFAt_satisfies_controlWordStackAssignment_other
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V)
    (word : List ((tmVerifierTM V).Γ k))
    (payload : (tmVerifierTM V).Γ k → Nat)
    (u : Nat) (j : tmVerifierStackIndex V) (cell : Nat)
    (hother : u ≠ t ∨ j ≠ k) :
    CNF.Satisfies (tmVerifierStackReadChoiceDomainCNFAt V u j cell)
      (tmVerifierControlWordStackAssignment V p t k word payload) := by
  rw [tmVerifierStackReadChoiceDomainCNFAt, tmVerifierStackReadChoiceLiteralsAt,
    tmVerifierStackReadChoices]
  apply CookLevin.exactlyOneCNF_satisfies_cons_of_head_true_tail_false
  · have hnot : ¬ (u = t ∧ j = k ∧ cell < word.length) := by
      intro h
      rcases hother with hu | hj
      · exact hu h.1
      · exact hj h.2.1
    simp [TMVerifierStackReadChoice.atomAt,
      tmVerifierStackEmptyAtom_eval_controlWordStackAssignment_of_not_selected V p t k word
        payload (u := u) (j := j) (cell := cell) hnot]
  · intro y hy
    rcases List.mem_map.mp hy with ⟨choice, hchoice, rfl⟩
    cases choice with
    | empty =>
        exfalso
        rw [tmVerifierActiveReadChoices] at hchoice
        rcases List.mem_filterMap.mp hchoice with ⟨named, _hNamed, hSome⟩
        unfold tmVerifierActiveReadChoiceOfNamed? at hSome
        split at hSome <;> simp at hSome
    | symbol payload' symbol =>
        have hnot : ¬ (u = t ∧ j = k ∧ cell < word.length) := by
          intro h
          rcases hother with hu | hj
          · exact hu h.1
          · exact hj h.2.1
        simp [TMVerifierStackReadChoice.atomAt,
          tmVerifierStackSymbolAtom_eval_controlWordStackAssignment_of_not_selected V p t k
            word payload (u := u) (j := j) (cell := cell) (payload' := payload') hnot]

theorem tmVerifierStackReadChoiceDomainCNFAt_satisfies_controlWordStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V)
    (word : List ((tmVerifierTM V).Γ k))
    (payload : (tmVerifierTM V).Γ k → Nat)
    (hPayloadMem :
      ∀ i, (hi : i < word.length) →
        TMVerifierStackReadChoice.symbol (V := V) (k := k) (payload (word[i]'hi))
            (word[i]'hi) ∈
          tmVerifierStackReadChoices V k)
    (u : Nat) (j : tmVerifierStackIndex V) (cell : Nat) :
    CNF.Satisfies (tmVerifierStackReadChoiceDomainCNFAt V u j cell)
      (tmVerifierControlWordStackAssignment V p t k word payload) := by
  by_cases hut : u = t
  · subst u
    by_cases hjk : j = k
    · subst j
      by_cases hcell : cell < word.length
      · exact tmVerifierStackReadChoiceDomainCNFAt_satisfies_controlWordStackAssignment_of_lt V
          p t k word payload hPayloadMem hcell
      · exact tmVerifierStackReadChoiceDomainCNFAt_satisfies_controlWordStackAssignment_of_tail V
          p t k word payload (Nat.le_of_not_gt hcell)
    · exact tmVerifierStackReadChoiceDomainCNFAt_satisfies_controlWordStackAssignment_other V p
        t k word payload t j cell (Or.inr hjk)
  · exact tmVerifierStackReadChoiceDomainCNFAt_satisfies_controlWordStackAssignment_other V p
      t k word payload u j cell (Or.inl hut)

theorem tmVerifierStackCellDomainsCNFAt_satisfies_controlWordStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V)
    (word : List ((tmVerifierTM V).Γ k))
    (payload : (tmVerifierTM V).Γ k → Nat)
    (hPayloadMem :
      ∀ i, (hi : i < word.length) →
        TMVerifierStackReadChoice.symbol (V := V) (k := k) (payload (word[i]'hi))
            (word[i]'hi) ∈
          tmVerifierStackReadChoices V k)
    (u : Nat) (j : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p u j)
      (tmVerifierControlWordStackAssignment V p t k word payload) := by
  intro c hc
  rw [tmVerifierStackCellDomainsCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨cell, _hcell, hc⟩
  exact tmVerifierStackReadChoiceDomainCNFAt_satisfies_controlWordStackAssignment V p t k
    word payload hPayloadMem u j cell c hc

theorem tmVerifierStackEmptyTailCNFAt_satisfies_controlWordStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V)
    (word : List ((tmVerifierTM V).Γ k))
    (payload : (tmVerifierTM V).Γ k → Nat)
    (u : Nat) (j : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierStackEmptyTailCNFAt V p u j)
      (tmVerifierControlWordStackAssignment V p t k word payload) := by
  intro c hc
  rw [tmVerifierStackEmptyTailCNFAt] at hc
  rcases List.mem_map.mp hc with ⟨cell, hcell, rfl⟩
  by_cases hselected : u = t ∧ j = k ∧ cell < word.length
  · rcases hselected with ⟨hut, hjk, hlt⟩
    subst u
    subst j
    refine ⟨Clause.negate (tmVerifierStackEmptyAtom V t k cell), ?_, ?_⟩
    · simp [tmVerifierStackEmptyTailClause, tmVerifierImplicationClause]
    · exact (Clause.negate_eval_true_iff (tmVerifierStackEmptyAtom V t k cell)
        (tmVerifierControlWordStackAssignment V p t k word payload)).2
        (tmVerifierStackEmptyAtom_eval_controlWordStackAssignment_of_selected V p t k word
          payload hlt)
  · refine ⟨tmVerifierStackEmptyAtom V u j (cell + 1), ?_, ?_⟩
    · simp [tmVerifierStackEmptyTailClause, tmVerifierImplicationClause]
    · have hcellLt : cell < tmVerifierCellBound V p := by
        simpa [tmVerifierCellSuccessorRange, List.mem_range] using hcell
      have hnotSucc : ¬ (u = t ∧ j = k ∧ cell + 1 < word.length) := by
        intro h
        exact hselected ⟨h.1, h.2.1, by omega⟩
      exact tmVerifierStackEmptyAtom_eval_controlWordStackAssignment_of_not_selected V p t k
        word payload hnotSucc

theorem tmVerifierStackFinalEmptyCNFAt_satisfies_controlWordStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V)
    (word : List ((tmVerifierTM V).Γ k))
    (payload : (tmVerifierTM V).Γ k → Nat)
    (hlen : word.length ≤ tmVerifierCellBound V p)
    (u : Nat) (j : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierStackFinalEmptyCNFAt V p u j)
      (tmVerifierControlWordStackAssignment V p t k word payload) := by
  intro c hc
  have hc' :
      c = [tmVerifierStackEmptyAtom V u j (tmVerifierCellBound V p)] := by
    simpa [tmVerifierStackFinalEmptyCNFAt] using hc
  subst c
  refine ⟨tmVerifierStackEmptyAtom V u j (tmVerifierCellBound V p), by simp, ?_⟩
  exact tmVerifierStackEmptyAtom_eval_controlWordStackAssignment_of_not_selected V p t k word
    payload (u := u) (j := j) (cell := tmVerifierCellBound V p) (by
      intro h
      omega)

theorem tmVerifierStackWellFormedCNFAt_satisfies_controlWordStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V)
    (word : List ((tmVerifierTM V).Γ k))
    (payload : (tmVerifierTM V).Γ k → Nat)
    (hPayloadMem :
      ∀ i, (hi : i < word.length) →
        TMVerifierStackReadChoice.symbol (V := V) (k := k) (payload (word[i]'hi))
            (word[i]'hi) ∈
          tmVerifierStackReadChoices V k)
    (hlen : word.length ≤ tmVerifierCellBound V p)
    (u : Nat) (j : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p u j)
      (tmVerifierControlWordStackAssignment V p t k word payload) := by
  rw [tmVerifierStackWellFormedCNFAt, CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    exact
      ⟨tmVerifierStackCellDomainsCNFAt_satisfies_controlWordStackAssignment V p t k word
          payload hPayloadMem u j,
        tmVerifierStackEmptyTailCNFAt_satisfies_controlWordStackAssignment V p t k word
          payload u j⟩
  · exact tmVerifierStackFinalEmptyCNFAt_satisfies_controlWordStackAssignment V p t k word
      payload hlen u j

theorem tmVerifierAllStackWellFormedCNFAt_satisfies_controlWordStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V)
    (word : List ((tmVerifierTM V).Γ k))
    (payload : (tmVerifierTM V).Γ k → Nat)
    (hPayloadMem :
      ∀ i, (hi : i < word.length) →
        TMVerifierStackReadChoice.symbol (V := V) (k := k) (payload (word[i]'hi))
            (word[i]'hi) ∈
          tmVerifierStackReadChoices V k)
    (hlen : word.length ≤ tmVerifierCellBound V p)
    (u : Nat) :
    CNF.Satisfies (tmVerifierAllStackWellFormedCNFAt V p u)
      (tmVerifierControlWordStackAssignment V p t k word payload) := by
  intro c hc
  rw [tmVerifierAllStackWellFormedCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨j, _hj, hc⟩
  exact tmVerifierStackWellFormedCNFAt_satisfies_controlWordStackAssignment V p t k word
    payload hPayloadMem hlen u j c hc

noncomputable def tmVerifierInitialInputStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) : Assignment :=
  tmVerifierControlWordStackAssignment V p 0 (tmVerifierTM V).k₀ (tmVerifierInputWord V p)
    (fun s => tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₀ s)

theorem tmVerifierInitialInputStack_word_payload_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) :
    ∀ i, (hi : i < (tmVerifierInputWord V p).length) →
      TMVerifierStackReadChoice.symbol (V := V) (k := (tmVerifierTM V).k₀)
          (tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₀
            ((tmVerifierInputWord V p)[i]'hi))
          ((tmVerifierInputWord V p)[i]'hi) ∈
        tmVerifierStackReadChoices V (tmVerifierTM V).k₀ := by
  intro i hi
  exact tmVerifierInputStackSymbol_choice_mem V ((tmVerifierInputWord V p)[i]'hi)

theorem tmVerifierInputWord_length_le_cellBound
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) :
    (tmVerifierInputWord V p).length ≤ tmVerifierCellBound V p := by
  simp [tmVerifierCellBound]
  omega

theorem tmVerifierAllStackWellFormedCNFAt_satisfies_initialInputStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (u : Nat) :
    CNF.Satisfies (tmVerifierAllStackWellFormedCNFAt V p u)
      (tmVerifierInitialInputStackAssignment V p) := by
  simpa [tmVerifierInitialInputStackAssignment] using
    tmVerifierAllStackWellFormedCNFAt_satisfies_controlWordStackAssignment V p 0
      (tmVerifierTM V).k₀ (tmVerifierInputWord V p)
      (fun s => tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₀ s)
      (tmVerifierInitialInputStack_word_payload_mem V p)
      (tmVerifierInputWord_length_le_cellBound V p) u

noncomputable def tmVerifierEndpointOutputStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) : Assignment :=
  tmVerifierControlWordStackAssignment V p (tmVerifierTimeBound V p) (tmVerifierTM V).k₁
    (tmVerifierBoolOutputWord V true)
    (fun s => tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₁ s)

theorem tmVerifierEndpointOutputStack_word_payload_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    ∀ i, (hi : i < (tmVerifierBoolOutputWord V true).length) →
      TMVerifierStackReadChoice.symbol (V := V) (k := (tmVerifierTM V).k₁)
          (tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₁
            ((tmVerifierBoolOutputWord V true)[i]'hi))
          ((tmVerifierBoolOutputWord V true)[i]'hi) ∈
        tmVerifierStackReadChoices V (tmVerifierTM V).k₁ := by
  intro i hi
  exact tmVerifierOutputStackSymbol_choice_mem V ((tmVerifierBoolOutputWord V true)[i]'hi)

theorem tmVerifierBoolOutputWord_true_length_le_cellBound
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) :
    (tmVerifierBoolOutputWord V true).length ≤ tmVerifierCellBound V p := by
  simp [tmVerifierCellBound]
  omega

theorem tmVerifierAllStackWellFormedCNFAt_satisfies_endpointOutputStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (u : Nat) :
    CNF.Satisfies (tmVerifierAllStackWellFormedCNFAt V p u)
      (tmVerifierEndpointOutputStackAssignment V p) := by
  simpa [tmVerifierEndpointOutputStackAssignment] using
    tmVerifierAllStackWellFormedCNFAt_satisfies_controlWordStackAssignment V p
      (tmVerifierTimeBound V p) (tmVerifierTM V).k₁ (tmVerifierBoolOutputWord V true)
      (fun s => tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₁ s)
      (tmVerifierEndpointOutputStack_word_payload_mem V)
      (tmVerifierBoolOutputWord_true_length_le_cellBound V p) u

theorem tmVerifierExactlyOneLabelCNFAt_satisfies_controlBoundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) :
    CNF.Satisfies (tmVerifierExactlyOneLabelCNFAt V t)
      (tmVerifierControlBoundaryAssignment V p) := by
  let selected := (tmVerifierRunCfgAt V p t).l
  apply CookLevin.exactlyOneCNF_satisfies_of_exists_unique
  · exact tmVerifierLabelAtomsAt_nodup V t
  · exact ⟨tmVerifierLabelAtom V t selected, tmVerifierLabelAtomsAt_mem V t selected,
      (tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff V p t selected).2 rfl⟩
  · intro x hx y hy hxTrue hyTrue
    rcases List.mem_map.mp hx with ⟨label₁, _hlabel₁, rfl⟩
    rcases List.mem_map.mp hy with ⟨label₂, _hlabel₂, rfl⟩
    have h₁ := (tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff V p t label₁).1 hxTrue
    have h₂ := (tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff V p t label₂).1 hyTrue
    subst label₁
    subst label₂
    rfl

theorem tmVerifierExactlyOneStateCNFAt_satisfies_controlBoundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) :
    CNF.Satisfies (tmVerifierExactlyOneStateCNFAt V t)
      (tmVerifierControlBoundaryAssignment V p) := by
  let selected := (tmVerifierRunCfgAt V p t).var
  apply CookLevin.exactlyOneCNF_satisfies_of_exists_unique
  · exact tmVerifierStateAtomsAt_nodup V t
  · exact ⟨tmVerifierStateAtom V t selected, tmVerifierStateAtomsAt_mem V t selected,
      (tmVerifierStateAtom_eval_controlBoundaryAssignment_iff V p t selected).2 rfl⟩
  · intro x hx y hy hxTrue hyTrue
    rcases List.mem_map.mp hx with ⟨state₁, _hstate₁, rfl⟩
    rcases List.mem_map.mp hy with ⟨state₂, _hstate₂, rfl⟩
    have h₁ := (tmVerifierStateAtom_eval_controlBoundaryAssignment_iff V p t state₁).1 hxTrue
    have h₂ := (tmVerifierStateAtom_eval_controlBoundaryAssignment_iff V p t state₂).1 hyTrue
    subst state₁
    subst state₂
    rfl

theorem tmVerifierControlDomainCNFAt_satisfies_controlBoundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) :
    CNF.Satisfies (tmVerifierControlDomainCNFAt V t)
      (tmVerifierControlBoundaryAssignment V p) := by
  rw [tmVerifierControlDomainCNFAt, CNF.satisfies_append]
  exact
    ⟨tmVerifierExactlyOneLabelCNFAt_satisfies_controlBoundaryAssignment V p t,
      tmVerifierExactlyOneStateCNFAt_satisfies_controlBoundaryAssignment V p t⟩

theorem tmVerifierControlDomainRowsCNF_satisfies_controlBoundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) :
    CNF.Satisfies (tmVerifierControlDomainRowsCNF V p)
      (tmVerifierControlBoundaryAssignment V p) := by
  intro c hc
  rw [tmVerifierControlDomainRowsCNF] at hc
  rcases List.mem_flatMap.mp hc with ⟨t, _ht, hc⟩
  exact tmVerifierControlDomainCNFAt_satisfies_controlBoundaryAssignment V p t c hc

theorem tmVerifierInitialStackCNF_satisfies_controlBoundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) :
    CNF.Satisfies (tmVerifierInitialStackCNF V p)
      (tmVerifierControlBoundaryAssignment V p) := by
  rw [tmVerifierInitialStackCNF_satisfies]
  constructor
  · intro l hl
    rw [List.mem_append] at hl
    rcases hl with hSymbol | hTail
    · rw [tmVerifierInputStackSymbolLiterals] at hSymbol
      rcases List.mem_map.mp hSymbol with ⟨entry, _hentry, rfl⟩
      simp [tmVerifierInputStackSymbolAtom_eval_controlBoundaryAssignment]
    · rw [tmVerifierInputStackEmptyTailLiterals] at hTail
      rcases List.mem_map.mp hTail with ⟨cell, _hcell, rfl⟩
      simp [tmVerifierStackEmptyAtom_eval_controlBoundaryAssignment]
  · intro l hl
    rw [tmVerifierInitialNonInputEmptyLiterals] at hl
    rcases List.mem_flatMap.mp hl with ⟨k, _hk, hcellLit⟩
    rcases List.mem_map.mp hcellLit with ⟨cell, _hcell, rfl⟩
    simp [tmVerifierStackEmptyAtom_eval_controlBoundaryAssignment]

theorem tmVerifierOutputTrueCNFAt_satisfies_controlBoundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) :
    CNF.Satisfies (tmVerifierOutputTrueCNFAt V p t)
      (tmVerifierControlBoundaryAssignment V p) := by
  rw [tmVerifierOutputTrueCNFAt_satisfies]
  constructor
  · intro l hl
    rw [List.mem_append] at hl
    rcases hl with hSymbol | hTail
    · rw [tmVerifierOutputTrueSymbolLiteralsAt] at hSymbol
      rcases List.mem_map.mp hSymbol with ⟨entry, _hentry, rfl⟩
      simp [tmVerifierOutputStackSymbolAtom_eval_controlBoundaryAssignment]
    · rw [tmVerifierOutputTrueEmptyTailLiteralsAt] at hTail
      rcases List.mem_map.mp hTail with ⟨cell, _hcell, rfl⟩
      simp [tmVerifierStackEmptyAtom_eval_controlBoundaryAssignment]
  · intro l hl
    rw [tmVerifierOutputTrueNonOutputEmptyLiteralsAt] at hl
    rcases List.mem_flatMap.mp hl with ⟨k, _hk, hcellLit⟩
    rcases List.mem_map.mp hcellLit with ⟨cell, _hcell, rfl⟩
    simp [tmVerifierStackEmptyAtom_eval_controlBoundaryAssignment]

end SAT
end ComplexityReduction
