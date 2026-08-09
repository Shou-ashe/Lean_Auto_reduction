/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauStepAux

/-!
Concrete stack-list projection from decoded tableau prefixes.

`TMTableauStepAux` states the operational theorem using concrete TM2 stack
lists.  This file starts the bridge from finite decoded stack-domain rows to
those concrete lists: a decoded read-choice prefix is projected to the list of
symbols before the first empty cell, and finite read-alignment evidence is
converted to the `tmVerifierStackActionReadsCurrent` predicate for each
indexed `peek`/`pop` action.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Decoded prefixes as concrete stack lists -/

/-- Project a decoded finite read-choice prefix to a concrete stack list. -/
def tmVerifierReadChoicePrefixToStack {L : EncodedDecisionProblem} {V : TMVerifier L}
    {k : tmVerifierStackIndex V} :
    List (TMVerifierStackReadChoice V k) → List ((tmVerifierTM V).Γ k)
  | [] => []
  | TMVerifierStackReadChoice.empty :: _ => []
  | TMVerifierStackReadChoice.symbol _ s :: rest => s :: tmVerifierReadChoicePrefixToStack rest

@[simp]
theorem tmVerifierReadChoicePrefixToStack_nil
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {k : tmVerifierStackIndex V} :
    tmVerifierReadChoicePrefixToStack ([] : List (TMVerifierStackReadChoice V k)) = [] :=
  rfl

@[simp]
theorem tmVerifierReadChoicePrefixToStack_empty_cons
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {k : tmVerifierStackIndex V} (rest : List (TMVerifierStackReadChoice V k)) :
    tmVerifierReadChoicePrefixToStack (TMVerifierStackReadChoice.empty :: rest) = [] :=
  rfl

@[simp]
theorem tmVerifierReadChoicePrefixToStack_symbol_cons
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {k : tmVerifierStackIndex V} (payload : Nat) (s : (tmVerifierTM V).Γ k)
    (rest : List (TMVerifierStackReadChoice V k)) :
    tmVerifierReadChoicePrefixToStack
        (TMVerifierStackReadChoice.symbol (V := V) (k := k) payload s :: rest) =
      s :: tmVerifierReadChoicePrefixToStack rest :=
  rfl

theorem tmVerifierReadChoicePrefixToStack_cons_head?
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {k : tmVerifierStackIndex V} (choice : TMVerifierStackReadChoice V k)
    (rest : List (TMVerifierStackReadChoice V k)) :
    (tmVerifierReadChoicePrefixToStack (choice :: rest)).head? = choice.toOption := by
  cases choice <;> rfl

theorem tmVerifierReadChoicePrefixToStack_head?_of_head?
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {k : tmVerifierStackIndex V} {choices : List (TMVerifierStackReadChoice V k)}
    {choice : TMVerifierStackReadChoice V k}
    (hhead : choices.head? = some choice) :
    (tmVerifierReadChoicePrefixToStack choices).head? = choice.toOption := by
  rcases List.head?_eq_some_iff.mp hhead with ⟨rest, rfl⟩
  exact tmVerifierReadChoicePrefixToStack_cons_head? choice rest

theorem tmVerifierReadChoicePrefixToStack_append_empty
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {k : tmVerifierStackIndex V}
    (choices : List (TMVerifierStackReadChoice V k)) :
    tmVerifierReadChoicePrefixToStack
        (choices ++ [TMVerifierStackReadChoice.empty]) =
      tmVerifierReadChoicePrefixToStack choices := by
  induction choices with
  | nil => rfl
  | cons choice rest ih =>
      cases choice <;> simp [tmVerifierReadChoicePrefixToStack, ih]

theorem tmVerifierReadChoicePrefixToStack_dropLast_of_getLast?_empty
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {k : tmVerifierStackIndex V}
    (choices : List (TMVerifierStackReadChoice V k))
    (hLast : choices.getLast? =
      some (TMVerifierStackReadChoice.empty : TMVerifierStackReadChoice V k)) :
    tmVerifierReadChoicePrefixToStack choices.dropLast =
      tmVerifierReadChoicePrefixToStack choices := by
  have hAppend :
      choices.dropLast ++ [TMVerifierStackReadChoice.empty] = choices :=
    List.dropLast_append_getLast? _ (by simp [hLast])
  calc
    tmVerifierReadChoicePrefixToStack choices.dropLast =
        tmVerifierReadChoicePrefixToStack
          (choices.dropLast ++ [TMVerifierStackReadChoice.empty]) :=
      (tmVerifierReadChoicePrefixToStack_append_empty choices.dropLast).symm
    _ = tmVerifierReadChoicePrefixToStack choices := by rw [hAppend]

theorem tmVerifierReadChoicePrefixToStack_symbol_cons_append_empty
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {k : tmVerifierStackIndex V} (payload : Nat) (s : (tmVerifierTM V).Γ k)
    (choices : List (TMVerifierStackReadChoice V k)) :
    tmVerifierReadChoicePrefixToStack
        (TMVerifierStackReadChoice.symbol (V := V) (k := k) payload s :: choices) =
      s :: tmVerifierReadChoicePrefixToStack
        (choices ++ [TMVerifierStackReadChoice.empty]) := by
  simp [tmVerifierReadChoicePrefixToStack_append_empty]

theorem tmVerifierReadChoicePrefixToStack_tail_eq_tail_of_cons
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {k : tmVerifierStackIndex V}
    (first second : TMVerifierStackReadChoice V k)
    (rest : List (TMVerifierStackReadChoice V k))
    (hEmpty : first = TMVerifierStackReadChoice.empty →
      second = TMVerifierStackReadChoice.empty) :
    tmVerifierReadChoicePrefixToStack (second :: rest) =
      (tmVerifierReadChoicePrefixToStack (first :: second :: rest)).tail := by
  cases first with
  | empty =>
      have hSecond := hEmpty rfl
      cases second <;> simp [tmVerifierReadChoicePrefixToStack] at hSecond ⊢
  | symbol payload s =>
      simp [tmVerifierReadChoicePrefixToStack]

theorem tmVerifierReadChoicePrefixToStack_tail_eq_tail_of_singleton
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {k : tmVerifierStackIndex V} (choice : TMVerifierStackReadChoice V k) :
    tmVerifierReadChoicePrefixToStack ([] : List (TMVerifierStackReadChoice V k)) =
      (tmVerifierReadChoicePrefixToStack [choice]).tail := by
  cases choice <;> rfl

theorem tmVerifierReadChoicePrefixToStack_tail_eq_tail_of_empty_successor
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {k : tmVerifierStackIndex V}
    (choices : List (TMVerifierStackReadChoice V k))
    (hEmpty :
      ∀ second rest, choices = TMVerifierStackReadChoice.empty :: second :: rest →
        second = TMVerifierStackReadChoice.empty) :
    tmVerifierReadChoicePrefixToStack choices.tail =
      (tmVerifierReadChoicePrefixToStack choices).tail := by
  cases choices with
  | nil => rfl
  | cons first tail =>
      cases tail with
      | nil =>
          exact tmVerifierReadChoicePrefixToStack_tail_eq_tail_of_singleton first
      | cons second rest =>
          exact tmVerifierReadChoicePrefixToStack_tail_eq_tail_of_cons first second rest (by
            intro hFirst
            exact hEmpty second rest (by simp [hFirst]))

private theorem rangePrefix_getLast?_aux {α : Type} (f : Nat → α) (n : Nat) :
    (f 0 :: (List.range n).map (fun i => f (i + 1))).getLast? = some (f n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.map_append]
      simpa using (List.getLast?_concat
        (l := f 0 :: List.map (fun i => f (i + 1)) (List.range n)) (a := f (n + 1)))

private theorem rangePrefix_dropLast_aux {α : Type} (f : Nat → α) (n : Nat) :
    (f 0 :: (List.range n).map (fun i => f (i + 1))).dropLast =
      (List.range n).map f := by
  apply List.ext_get
  · simp
  · intro i h₁ h₂
    change ((f 0 :: (List.range n).map (fun i => f (i + 1))).dropLast)[i] =
      ((List.range n).map f)[i]
    rw [List.getElem_dropLast]
    cases i with
    | zero => simp
    | succ i =>
        rw [List.getElem_cons_succ]
        simp

private theorem attach_range_map_self_aux {α : Type} (f : Nat → α) (n : Nat) :
    ((List.range n).attach.map fun cell => f cell.1) =
      (List.range n).map f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.map_append]
      simp

private theorem attach_range_map_succ_aux {α : Type} (f : Nat → α) (n : Nat) :
    ((List.range n).attach.map fun cell => f (cell.1 + 1)) =
      (List.range n).map fun i => f (i + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.map_append]
      simp

private theorem rangeAttachPrefix_getLast?_aux {α : Type} (f : Nat → α) (n : Nat) :
    (f 0 :: ((List.range n).attach.map fun cell => f (cell.1 + 1))).getLast? =
      some (f n) := by
  rw [attach_range_map_succ_aux f n]
  exact rangePrefix_getLast?_aux f n

private theorem rangeAttachPrefix_dropLast_aux {α : Type} (f : Nat → α) (n : Nat) :
    (f 0 :: ((List.range n).attach.map fun cell => f (cell.1 + 1))).dropLast =
      ((List.range n).attach.map fun cell => f cell.1) := by
  rw [attach_range_map_succ_aux f n]
  rw [rangePrefix_dropLast_aux f n]
  rw [attach_range_map_self_aux f n]

private theorem rangeAttachPrefix_getLast?_subtype_aux {α : Type} (n : Nat)
    (f : (i : Nat) → i < n + 1 → α) :
    (f 0 (by omega) :: ((List.range n).attach.map fun cell =>
        f (cell.1 + 1) (by
          have hcell : cell.1 < n := by simpa using cell.2
          omega))).getLast? =
      some (f n (by omega)) := by
  rw [List.getLast?_eq_getElem?]
  simp only [List.length_cons, List.length_map, List.length_attach, List.length_range,
    Nat.add_one_sub_one]
  cases n with
  | zero => simp
  | succ n =>
      rw [List.getElem?_cons_succ]
      rw [List.getElem?_map]
      simp

private theorem rangeAttachMap_succ_head?_subtype_aux {α : Type} (n : Nat)
    (f : (i : Nat) → i < n + 2 → α) :
    (((List.range (n + 1)).attach.map fun cell =>
        f (cell.1 + 1) (by
          have hcell : cell.1 < n + 1 := by simpa using cell.2
          omega))).head? =
      some (f 1 (by omega)) := by
  rw [List.head?_eq_getElem?]
  rw [List.getElem?_eq_some_iff]
  refine ⟨by simp, ?_⟩
  simp

private theorem rangeAttachPrefix_dropLast_subtype_aux {α : Type} (n : Nat)
    (f : (i : Nat) → i < n + 1 → α) :
    (f 0 (by omega) :: ((List.range n).attach.map fun cell =>
        f (cell.1 + 1) (by
          have hcell : cell.1 < n := by simpa using cell.2
          omega))).dropLast =
      ((List.range n).attach.map fun cell =>
        f cell.1 (by
          have hcell : cell.1 < n := by simpa using cell.2
          omega)) := by
  apply List.ext_get
  · simp
  · intro i h₁ h₂
    change
      ((f 0 (by omega) :: ((List.range n).attach.map fun cell =>
          f (cell.1 + 1) (by
            have hcell : cell.1 < n := by simpa using cell.2
            omega))).dropLast)[i] =
        (((List.range n).attach.map fun cell =>
          f cell.1 (by
            have hcell : cell.1 < n := by simpa using cell.2
            omega)))[i]
    rw [List.getElem_dropLast]
    cases i with
    | zero =>
        simp
    | succ i =>
        rw [List.getElem_cons_succ]
        rw [List.getElem_map]
        rw [List.getElem_map]
        simp

theorem tmVerifierCellBound_mem_cellRange
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) :
    tmVerifierCellBound V p ∈ tmVerifierCellRange V p := by
  simp [tmVerifierCellRange]

/-- Decode one satisfied stack-domain row into an explicit top-first finite prefix. -/
noncomputable def tmVerifierDecodedStackChoicePrefix
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a) :
    List (TMVerifierStackReadChoice V k) :=
  (tmVerifierDecodedStackCellOf V p t k 0 a h
      (tmVerifierCellRange_zero_mem V p)).choice ::
    ((tmVerifierCellSuccessorRange V p).attach.map fun cell =>
      (tmVerifierDecodedStackCellOf V p t k (cell.1 + 1) a h
        (tmVerifierCellSuccessorRange_succ_mem_cellRange V p cell.1 cell.2)).choice)

/-- Decode one satisfied stack-domain row into the concrete stack list it represents. -/
noncomputable def tmVerifierDecodedStackList
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a) :
    List ((tmVerifierTM V).Γ k) :=
  tmVerifierReadChoicePrefixToStack (tmVerifierDecodedStackChoicePrefix V p t k a h)

theorem tmVerifierDecodedStackList_head?
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a) :
    (tmVerifierDecodedStackList V p t k a h).head? =
      (tmVerifierDecodedStackCellOf V p t k 0 a h
        (tmVerifierCellRange_zero_mem V p)).choice.toOption := by
  simp [tmVerifierDecodedStackList, tmVerifierDecodedStackChoicePrefix,
    tmVerifierReadChoicePrefixToStack_cons_head?]

theorem tmVerifierDecodedStackList_eq_of_domain_proofs
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (h₁ h₂ : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a) :
    tmVerifierDecodedStackList V p t k a h₁ =
      tmVerifierDecodedStackList V p t k a h₂ := by
  simp [tmVerifierDecodedStackList, tmVerifierDecodedStackChoicePrefix]

theorem tmVerifierDecodedStackList_eq_of_time_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    {t₁ t₂ : Nat} (ht : t₁ = t₂) (k : tmVerifierStackIndex V) (a : Assignment)
    (h₁ : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t₁ k) a)
    (h₂ : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t₂ k) a) :
    tmVerifierDecodedStackList V p t₁ k a h₁ =
      tmVerifierDecodedStackList V p t₂ k a h₂ := by
  cases ht
  exact tmVerifierDecodedStackList_eq_of_domain_proofs V p t₁ k a h₁ h₂

theorem tmVerifierDecodedStackChoicePrefix_getLast?
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
  (h : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a) :
    (tmVerifierDecodedStackChoicePrefix V p t k a h).getLast? =
      some ((tmVerifierDecodedStackCellOf V p t k (tmVerifierCellBound V p) a h
        (tmVerifierCellBound_mem_cellRange V p)).choice) := by
  simpa [tmVerifierDecodedStackChoicePrefix, tmVerifierCellSuccessorRange, tmVerifierCellRange]
    using rangeAttachPrefix_getLast?_subtype_aux (tmVerifierCellBound V p)
    (fun cell _hcell =>
      (tmVerifierDecodedStackCellOf V p t k cell a h
        (by simpa [tmVerifierCellRange, List.mem_range] using _hcell)).choice)

theorem tmVerifierDecodedStackChoicePrefix_final_empty
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (hDomains : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a)
    (hWF : CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p t k) a) :
    (tmVerifierDecodedStackChoicePrefix V p t k a hDomains).getLast? =
      some (TMVerifierStackReadChoice.empty : TMVerifierStackReadChoice V k) := by
  rw [tmVerifierDecodedStackChoicePrefix_getLast?]
  let d :=
    tmVerifierDecodedStackCellOf V p t k (tmVerifierCellBound V p) a hDomains
      (tmVerifierCellBound_mem_cellRange V p)
  have hChoice :
      d.choice = (TMVerifierStackReadChoice.empty : TMVerifierStackReadChoice V k) := by
    exact tmVerifierStackCellDomainsCNFAt_satisfies_choice_eq V p t k
      (tmVerifierCellBound V p) a hDomains (tmVerifierCellBound_mem_cellRange V p)
      d.choice TMVerifierStackReadChoice.empty d.choice_mem
      (tmVerifierStackReadChoices_empty_mem V k) d.atom_true
      (by
        simpa [TMVerifierStackReadChoice.atomAt] using
          tmVerifierStackWellFormedCNFAt_satisfies_finalEmpty V p t k a hWF)
  simp [d, hChoice]

theorem tmVerifierDecodedStackChoicePrefix_dropLast
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a) :
    (tmVerifierDecodedStackChoicePrefix V p t k a h).dropLast =
      ((tmVerifierCellSuccessorRange V p).attach.map fun cell =>
        (tmVerifierDecodedStackCellOf V p t k cell.1 a h
          (tmVerifierCellSuccessorRange_mem_cellRange V p cell.1 cell.2)).choice) := by
  simpa [tmVerifierDecodedStackChoicePrefix, tmVerifierCellSuccessorRange, tmVerifierCellRange]
    using rangeAttachPrefix_dropLast_subtype_aux (tmVerifierCellBound V p)
      (fun cell _hcell =>
        (tmVerifierDecodedStackCellOf V p t k cell a h
          (by simpa [tmVerifierCellRange, List.mem_range] using _hcell)).choice)

theorem tmVerifierDecodedStackCellOf_choice_eq_of_cellRange_proofs
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a)
    (h₁ h₂ : cell ∈ tmVerifierCellRange V p) :
    (tmVerifierDecodedStackCellOf V p t k cell a h h₁).choice =
      (tmVerifierDecodedStackCellOf V p t k cell a h h₂).choice := by
  congr

theorem tmVerifierDecodedStackChoicePrefix_tail_toStack
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (hDomains : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a)
    (hWF : CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p t k) a) :
    tmVerifierReadChoicePrefixToStack
        (tmVerifierDecodedStackChoicePrefix V p t k a hDomains).tail =
      (tmVerifierReadChoicePrefixToStack
        (tmVerifierDecodedStackChoicePrefix V p t k a hDomains)).tail := by
  apply tmVerifierReadChoicePrefixToStack_tail_eq_tail_of_empty_successor
  intro second rest hPrefix
  cases hBound : tmVerifierCellBound V p with
  | zero =>
      simp [tmVerifierDecodedStackChoicePrefix, tmVerifierCellSuccessorRange, hBound] at hPrefix
      have hImpossible : False := by
        have hLen := congrArg List.length hPrefix.2
        simp [hBound] at hLen
      exact False.elim hImpossible
  | succ n =>
      have hzero : 0 ∈ tmVerifierCellSuccessorRange V p := by
        simp [tmVerifierCellSuccessorRange, hBound]
      let d0 :=
        tmVerifierDecodedStackCellOf V p t k 0 a hDomains
          (tmVerifierCellRange_zero_mem V p)
      let d1 :=
        tmVerifierDecodedStackCellOf V p t k 1 a hDomains
          (tmVerifierCellSuccessorRange_succ_mem_cellRange V p 0 hzero)
      have hEmptyNext : d0.choice = TMVerifierStackReadChoice.empty → d1.choice =
          (TMVerifierStackReadChoice.empty : TMVerifierStackReadChoice V k) := by
        intro hEmptyChoice
        have hEmpty0 : (tmVerifierStackEmptyAtom V t k 0).eval a = true :=
          d0.empty_atom_true hEmptyChoice
        have hEmpty1 :
            (tmVerifierStackEmptyAtom V t k (0 + 1)).eval a = true :=
          tmVerifierStackWellFormedCNFAt_satisfies_empty_successor V p t k 0 a hWF
            hzero hEmpty0
        exact tmVerifierStackCellDomainsCNFAt_satisfies_choice_eq V p t k 1 a hDomains
          (tmVerifierCellSuccessorRange_succ_mem_cellRange V p 0 hzero)
          d1.choice TMVerifierStackReadChoice.empty d1.choice_mem
          (tmVerifierStackReadChoices_empty_mem V k) d1.atom_true
          (by simpa [TMVerifierStackReadChoice.atomAt] using hEmpty1)
      have hRest :
          second :: rest =
            ((tmVerifierCellSuccessorRange V p).attach.map fun cell =>
              (tmVerifierDecodedStackCellOf V p t k (cell.1 + 1) a hDomains
                (tmVerifierCellSuccessorRange_succ_mem_cellRange V p cell.1 cell.2)).choice) := by
        have hCons := hPrefix
        simp only [tmVerifierDecodedStackChoicePrefix] at hCons
        exact (List.cons.inj hCons).2.symm
      have hTailHead :
          (((tmVerifierCellSuccessorRange V p).attach.map fun cell =>
            (tmVerifierDecodedStackCellOf V p t k (cell.1 + 1) a hDomains
              (tmVerifierCellSuccessorRange_succ_mem_cellRange V p cell.1 cell.2)).choice)).head? =
            some d1.choice := by
        simpa [tmVerifierCellSuccessorRange, hBound, d1, tmVerifierCellRange]
          using rangeAttachMap_succ_head?_subtype_aux n
            (fun cell _hcell =>
              (tmVerifierDecodedStackCellOf V p t k cell a hDomains
                (by
                  rw [tmVerifierCellRange, List.mem_range]
                  rw [hBound]
                  omega)).choice)
      have hSecond : second = d1.choice := by
        rw [← Option.some.injEq]
        calc
          some second = (second :: rest).head? := by simp
          _ = (((tmVerifierCellSuccessorRange V p).attach.map fun cell =>
                (tmVerifierDecodedStackCellOf V p t k (cell.1 + 1) a hDomains
                  (tmVerifierCellSuccessorRange_succ_mem_cellRange V p cell.1 cell.2)).choice)).head? := by
            rw [hRest]
          _ = some d1.choice := hTailHead
      rw [hSecond]
      exact hEmptyNext (by
        have hHead := List.cons.inj hPrefix |>.1
        simpa [d0] using hHead)

theorem TMVerifierDecodedPushPrefixEffect.choicePrefix_eq_cons_dropLast
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {B : TMVerifierPushPayloadBoundary V}
    {p : L.Instance.Carrier × V.Cert.Carrier} {tin tout : Nat}
    {raw : TMVerifierStackSymbol V} {a : Assignment}
    {hIn :
      CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tin raw.stack) a}
    {hOut :
      CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tout raw.stack) a}
    (hEff : TMVerifierDecodedPushPrefixEffect V B p tin tout raw a hIn hOut) :
    tmVerifierDecodedStackChoicePrefix V p tout raw.stack a hOut =
      TMVerifierStackReadChoice.symbol (V := V) (k := raw.stack) (B.payload raw) raw.symbol ::
        (tmVerifierDecodedStackChoicePrefix V p tin raw.stack a hIn).dropLast := by
  rcases hEff with ⟨hTop, hShift⟩
  rw [tmVerifierDecodedStackChoicePrefix_dropLast]
  simp only [tmVerifierDecodedStackChoicePrefix]
  exact List.cons_eq_cons.mpr ⟨hTop, by
    apply List.map_congr_left
    intro cell hcell
    exact hShift cell.1 cell.2⟩

theorem TMVerifierDecodedFramePrefixEffect.choicePrefix_eq
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {p : L.Instance.Carrier × V.Cert.Carrier} {tin tout : Nat}
    {k : tmVerifierStackIndex V} {a : Assignment}
    {hIn : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tin k) a}
    {hOut : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tout k) a}
    (hEff : TMVerifierDecodedFramePrefixEffect V p tin tout k a hIn hOut) :
    tmVerifierDecodedStackChoicePrefix V p tout k a hOut =
      tmVerifierDecodedStackChoicePrefix V p tin k a hIn := by
  simp only [tmVerifierDecodedStackChoicePrefix]
  exact List.cons_eq_cons.mpr ⟨hEff 0 (tmVerifierCellRange_zero_mem V p), by
    apply List.map_congr_left
    intro cell hcell
    exact hEff (cell.1 + 1)
      (tmVerifierCellSuccessorRange_succ_mem_cellRange V p cell.1 cell.2)⟩

theorem TMVerifierDecodedPopPrefixEffect.choicePrefix_dropLast_eq_tail
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {p : L.Instance.Carrier × V.Cert.Carrier} {tin tout : Nat}
    {k : tmVerifierStackIndex V} {a : Assignment}
    {hIn : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tin k) a}
    {hOut : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tout k) a}
    (hEff : TMVerifierDecodedPopPrefixEffect V p tin tout k a hIn hOut) :
    (tmVerifierDecodedStackChoicePrefix V p tout k a hOut).dropLast =
      (tmVerifierDecodedStackChoicePrefix V p tin k a hIn).tail := by
  rw [tmVerifierDecodedStackChoicePrefix_dropLast]
  simp only [tmVerifierDecodedStackChoicePrefix]
  apply List.map_congr_left
  intro cell hcell
  exact hEff cell.1 cell.2

theorem TMVerifierDecodedPushPrefixEffect.decodedStackList_eq_cons
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {B : TMVerifierPushPayloadBoundary V}
    {p : L.Instance.Carrier × V.Cert.Carrier} {tin tout : Nat}
    {raw : TMVerifierStackSymbol V} {a : Assignment}
    {hIn :
      CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tin raw.stack) a}
    {hOut :
      CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tout raw.stack) a}
    (hEff : TMVerifierDecodedPushPrefixEffect V B p tin tout raw a hIn hOut)
    (hInWF : CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p tin raw.stack) a) :
    tmVerifierDecodedStackList V p tout raw.stack a hOut =
      raw.symbol :: tmVerifierDecodedStackList V p tin raw.stack a hIn := by
  let inPrefix := tmVerifierDecodedStackChoicePrefix V p tin raw.stack a hIn
  have hLast : inPrefix.getLast? =
      some (TMVerifierStackReadChoice.empty : TMVerifierStackReadChoice V raw.stack) :=
    tmVerifierDecodedStackChoicePrefix_final_empty V p tin raw.stack a hIn hInWF
  calc
    tmVerifierDecodedStackList V p tout raw.stack a hOut =
        tmVerifierReadChoicePrefixToStack
          (TMVerifierStackReadChoice.symbol (V := V) (k := raw.stack)
            (B.payload raw) raw.symbol :: inPrefix.dropLast) := by
      simp [tmVerifierDecodedStackList, inPrefix,
        TMVerifierDecodedPushPrefixEffect.choicePrefix_eq_cons_dropLast hEff]
    _ = raw.symbol :: tmVerifierReadChoicePrefixToStack inPrefix.dropLast := rfl
    _ = raw.symbol :: tmVerifierReadChoicePrefixToStack inPrefix := by
      rw [tmVerifierReadChoicePrefixToStack_dropLast_of_getLast?_empty inPrefix hLast]
    _ = raw.symbol :: tmVerifierDecodedStackList V p tin raw.stack a hIn := rfl

theorem TMVerifierDecodedFramePrefixEffect.decodedStackList_eq
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {p : L.Instance.Carrier × V.Cert.Carrier} {tin tout : Nat}
    {k : tmVerifierStackIndex V} {a : Assignment}
    {hIn : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tin k) a}
    {hOut : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tout k) a}
    (hEff : TMVerifierDecodedFramePrefixEffect V p tin tout k a hIn hOut) :
    tmVerifierDecodedStackList V p tout k a hOut =
      tmVerifierDecodedStackList V p tin k a hIn := by
  simp [tmVerifierDecodedStackList, TMVerifierDecodedFramePrefixEffect.choicePrefix_eq hEff]

theorem TMVerifierDecodedPopPrefixEffect.decodedStackList_eq_tail
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {p : L.Instance.Carrier × V.Cert.Carrier} {tin tout : Nat}
    {k : tmVerifierStackIndex V} {a : Assignment}
    {hIn : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tin k) a}
    {hOut : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tout k) a}
    (hEff : TMVerifierDecodedPopPrefixEffect V p tin tout k a hIn hOut)
    (hInWF : CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p tin k) a)
    (hOutWF : CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p tout k) a) :
    tmVerifierDecodedStackList V p tout k a hOut =
      (tmVerifierDecodedStackList V p tin k a hIn).tail := by
  let outPrefix := tmVerifierDecodedStackChoicePrefix V p tout k a hOut
  let inPrefix := tmVerifierDecodedStackChoicePrefix V p tin k a hIn
  have hOutLast : outPrefix.getLast? =
      some (TMVerifierStackReadChoice.empty : TMVerifierStackReadChoice V k) :=
    tmVerifierDecodedStackChoicePrefix_final_empty V p tout k a hOut hOutWF
  calc
    tmVerifierDecodedStackList V p tout k a hOut =
        tmVerifierReadChoicePrefixToStack outPrefix := rfl
    _ = tmVerifierReadChoicePrefixToStack outPrefix.dropLast := by
      exact (tmVerifierReadChoicePrefixToStack_dropLast_of_getLast?_empty outPrefix
        hOutLast).symm
    _ = tmVerifierReadChoicePrefixToStack inPrefix.tail := by
      rw [TMVerifierDecodedPopPrefixEffect.choicePrefix_dropLast_eq_tail hEff]
    _ = (tmVerifierReadChoicePrefixToStack inPrefix).tail := by
      exact tmVerifierDecodedStackChoicePrefix_tail_toStack V p tin k a hIn hInWF
    _ = (tmVerifierDecodedStackList V p tin k a hIn).tail := rfl

end SAT
end ComplexityReduction
