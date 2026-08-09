/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.List.Sigma
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauSoundness

/-!
First completeness slice for the standard-TM verifier tableau.

This file only constructs the boundary part of an accepting-run assignment:
initial control, initial stack, final halted/output-true endpoint, and the
derived x-prefix block.  Transition rows and domain rows are intentionally left
to later slices.
-/

namespace ComplexityReduction
namespace SAT

namespace CookLevin

theorem atMostOneWithCNF_satisfies_of_not_both
    (x : Literal) (ys : List Literal) (a : Assignment)
    (h : ∀ y ∈ ys, x.eval a = true → y.eval a = true → False) :
    CNF.Satisfies (atMostOneWithCNF x ys) a := by
  induction ys with
  | nil =>
      simp [atMostOneWithCNF, CNF.Satisfies]
  | cons y ys ih =>
      intro c hc
      rcases List.mem_cons.mp hc with hcHead | hcTail
      · subst c
        by_cases hx : x.eval a = true
        · have hyFalse : y.eval a = false := by
            cases hy : y.eval a
            · rfl
            · exact False.elim (h y (by simp) hx hy)
          exact ⟨Clause.negate y, by simp, (Clause.negate_eval_true_iff y a).2 hyFalse⟩
        · have hxFalse : x.eval a = false := by
            cases hxv : x.eval a <;> simp [hxv] at hx ⊢
          exact ⟨Clause.negate x, by simp, (Clause.negate_eval_true_iff x a).2 hxFalse⟩
      · exact ih (by
          intro z hz hx hzTrue
          exact h z (by simp [hz]) hx hzTrue) c hcTail

theorem atMostOneCNF_satisfies_of_unique
    (xs : List Literal) (a : Assignment)
    (hNodup : xs.Nodup)
    (hUnique :
      ∀ x ∈ xs, ∀ y ∈ xs, x.eval a = true → y.eval a = true → x = y) :
    CNF.Satisfies (atMostOneCNF xs) a := by
  induction xs with
  | nil =>
      simp [atMostOneCNF, CNF.Satisfies]
  | cons x xs ih =>
      have hNodupTail : xs.Nodup := hNodup.of_cons
      have hxNotMem : x ∉ xs := hNodup.notMem
      rw [atMostOneCNF, CNF.satisfies_append]
      constructor
      · exact atMostOneWithCNF_satisfies_of_not_both x xs a (by
          intro y hy hxTrue hyTrue
          have hEq := hUnique x (by simp) y (by simp [hy]) hxTrue hyTrue
          exact hxNotMem (by simpa [hEq] using hy))
      · exact ih hNodupTail (by
          intro y hy z hz hyTrue hzTrue
          exact hUnique y (by simp [hy]) z (by simp [hz]) hyTrue hzTrue)

theorem exactlyOneCNF_satisfies_of_exists_unique
    (xs : List Literal) (a : Assignment)
    (hNodup : xs.Nodup)
    (hExists : ∃ x ∈ xs, x.eval a = true)
    (hUnique :
      ∀ x ∈ xs, ∀ y ∈ xs, x.eval a = true → y.eval a = true → x = y) :
    CNF.Satisfies (exactlyOneCNF xs) a := by
  rw [exactlyOneCNF, CNF.satisfies_append]
  exact
    ⟨(atLeastOneCNF_satisfies xs a).2 hExists,
      atMostOneCNF_satisfies_of_unique xs a hNodup hUnique⟩

theorem atMostOneCNF_satisfies_of_all_false
    (xs : List Literal) (a : Assignment)
    (h : ∀ x ∈ xs, x.eval a = false) :
    CNF.Satisfies (atMostOneCNF xs) a := by
  induction xs with
  | nil =>
      simp [atMostOneCNF, CNF.Satisfies]
  | cons x xs ih =>
      rw [atMostOneCNF, CNF.satisfies_append]
      constructor
      · exact atMostOneWithCNF_satisfies_of_not_both x xs a (by
          intro y _hy hx _hyTrue
          have hxFalse := h x (by simp)
          simp [hx] at hxFalse)
      · exact ih (by
          intro y hy
          exact h y (by simp [hy]))

theorem atMostOneCNF_satisfies_cons_of_head_true_tail_false
    (x : Literal) (xs : List Literal) (a : Assignment)
    (_hx : x.eval a = true)
    (hxs : ∀ y ∈ xs, y.eval a = false) :
    CNF.Satisfies (atMostOneCNF (x :: xs)) a := by
  rw [atMostOneCNF, CNF.satisfies_append]
  constructor
  · exact atMostOneWithCNF_satisfies_of_not_both x xs a (by
      intro y hy _hx hyTrue
      have hyFalse := hxs y hy
      simp [hyTrue] at hyFalse)
  · exact atMostOneCNF_satisfies_of_all_false xs a hxs

theorem exactlyOneCNF_satisfies_cons_of_head_true_tail_false
    (x : Literal) (xs : List Literal) (a : Assignment)
    (hx : x.eval a = true)
    (hxs : ∀ y ∈ xs, y.eval a = false) :
    CNF.Satisfies (exactlyOneCNF (x :: xs)) a := by
  rw [exactlyOneCNF, CNF.satisfies_append]
  exact
    ⟨(atLeastOneCNF_satisfies (x :: xs) a).2 ⟨x, by simp, hx⟩,
      atMostOneCNF_satisfies_cons_of_head_true_tail_false x xs a hx hxs⟩

end CookLevin

/-! ### Boundary assignment skeleton -/

/-- A trivial boundary assignment that makes every positive boundary atom true. -/
def tmVerifierBoundaryAssignment : Assignment :=
  fun _ => true

@[simp]
theorem tmVerifierTableauAtom_eval_boundaryAssignment
    (kind : TMVerifierTableauVarKind) (time stack cell payload : Nat) :
    (tmVerifierTableauAtom kind time stack cell payload).eval
      tmVerifierBoundaryAssignment = true := by
  rfl

@[simp]
theorem tmVerifierLabelAtom_eval_boundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (label : Option (tmVerifierTM V).Λ) :
    (tmVerifierLabelAtom V t label).eval tmVerifierBoundaryAssignment = true := by
  simp [tmVerifierLabelAtom]

@[simp]
theorem tmVerifierStateAtom_eval_boundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (state : (tmVerifierTM V).σ) :
    (tmVerifierStateAtom V t state).eval tmVerifierBoundaryAssignment = true := by
  simp [tmVerifierStateAtom]

@[simp]
theorem tmVerifierStackSymbolAtom_eval_boundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) (cell payload : Nat) :
    (tmVerifierStackSymbolAtom V t k cell payload).eval
      tmVerifierBoundaryAssignment = true := by
  simp [tmVerifierStackSymbolAtom]

@[simp]
theorem tmVerifierInputStackSymbolAtom_eval_boundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t cell : Nat) (s : (tmVerifierTM V).Γ (tmVerifierTM V).k₀) :
    (tmVerifierInputStackSymbolAtom V t cell s).eval
      tmVerifierBoundaryAssignment = true := by
  simp [tmVerifierInputStackSymbolAtom]

@[simp]
theorem tmVerifierOutputStackSymbolAtom_eval_boundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t cell : Nat) (s : (tmVerifierTM V).Γ (tmVerifierTM V).k₁) :
    (tmVerifierOutputStackSymbolAtom V t cell s).eval
      tmVerifierBoundaryAssignment = true := by
  simp [tmVerifierOutputStackSymbolAtom]

@[simp]
theorem tmVerifierStackEmptyAtom_eval_boundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) :
    (tmVerifierStackEmptyAtom V t k cell).eval tmVerifierBoundaryAssignment = true := by
  simp [tmVerifierStackEmptyAtom]

namespace TMVerifierAcceptedRun

/--
Boundary assignment associated to an accepting run.

At this slice the run parameter records the semantic source of the assignment,
while the assignment itself only covers positive boundary unit clauses.
-/
def boundaryAssignment
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (_run : TMVerifierAcceptedRun V x c) : Assignment :=
  tmVerifierBoundaryAssignment

end TMVerifierAcceptedRun

/-! ### Boundary block satisfaction -/

theorem tmVerifierInitialControlCNF_satisfies_boundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    CNF.Satisfies (tmVerifierInitialControlCNF V) tmVerifierBoundaryAssignment := by
  rw [tmVerifierInitialControlCNF, CNF.satisfies_append]
  constructor
  · exact (tmVerifierUnitCNF_satisfies
      (tmVerifierLabelAtom V 0 (some (tmVerifierTM V).main))
      tmVerifierBoundaryAssignment).2 (by simp)
  · exact (tmVerifierUnitCNF_satisfies
      (tmVerifierStateAtom V 0 (tmVerifierTM V).initialState)
      tmVerifierBoundaryAssignment).2 (by simp)

theorem tmVerifierInitialStackCNF_satisfies_boundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) :
    CNF.Satisfies (tmVerifierInitialStackCNF V p) tmVerifierBoundaryAssignment := by
  rw [tmVerifierInitialStackCNF_satisfies]
  constructor
  · intro l hl
    rw [List.mem_append] at hl
    rcases hl with hSymbol | hTail
    · rw [tmVerifierInputStackSymbolLiterals] at hSymbol
      rcases List.mem_map.mp hSymbol with ⟨entry, _hentry, rfl⟩
      simp
    · rw [tmVerifierInputStackEmptyTailLiterals] at hTail
      rcases List.mem_map.mp hTail with ⟨cell, _hcell, rfl⟩
      simp
  · intro l hl
    rw [tmVerifierInitialNonInputEmptyLiterals] at hl
    rcases List.mem_flatMap.mp hl with ⟨k, _hk, hcellLit⟩
    rcases List.mem_map.mp hcellLit with ⟨cell, _hcell, rfl⟩
    simp

theorem tmVerifierOutputTrueCNFAt_satisfies_boundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) :
    CNF.Satisfies (tmVerifierOutputTrueCNFAt V p t)
      tmVerifierBoundaryAssignment := by
  rw [tmVerifierOutputTrueCNFAt_satisfies]
  constructor
  · intro l hl
    rw [List.mem_append] at hl
    rcases hl with hSymbol | hTail
    · rw [tmVerifierOutputTrueSymbolLiteralsAt] at hSymbol
      rcases List.mem_map.mp hSymbol with ⟨entry, _hentry, rfl⟩
      simp
    · rw [tmVerifierOutputTrueEmptyTailLiteralsAt] at hTail
      rcases List.mem_map.mp hTail with ⟨cell, _hcell, rfl⟩
      simp
  · intro l hl
    rw [tmVerifierOutputTrueNonOutputEmptyLiteralsAt] at hl
    rcases List.mem_flatMap.mp hl with ⟨k, _hk, hcellLit⟩
    rcases List.mem_map.mp hcellLit with ⟨cell, _hcell, rfl⟩
    simp

theorem tmVerifierEndpointCNF_satisfies_boundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) :
    CNF.Satisfies (tmVerifierEndpointCNF V p) tmVerifierBoundaryAssignment := by
  rw [tmVerifierEndpointCNF, CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    constructor
    · exact (tmVerifierUnitCNF_satisfies
        (tmVerifierLabelAtom V (tmVerifierTimeBound V p) none)
        tmVerifierBoundaryAssignment).2 (by simp)
    · exact (tmVerifierUnitCNF_satisfies
        (tmVerifierStateAtom V (tmVerifierTimeBound V p) (tmVerifierTM V).initialState)
        tmVerifierBoundaryAssignment).2 (by simp)
  · exact tmVerifierOutputTrueCNFAt_satisfies_boundaryAssignment V p
      (tmVerifierTimeBound V p)

/-- Boundary-only CNF block for the fixed-pair verifier tableau. -/
noncomputable def tmVerifierFixedPairBoundaryCNF
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) : CNF :=
  tmVerifierInitialControlCNF V ++ tmVerifierInitialStackCNF V p ++
    tmVerifierEndpointCNF V p

theorem tmVerifierFixedPairBoundaryCNF_satisfies_boundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) :
    CNF.Satisfies (tmVerifierFixedPairBoundaryCNF V p)
      tmVerifierBoundaryAssignment := by
  rw [tmVerifierFixedPairBoundaryCNF, CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    exact
      ⟨tmVerifierInitialControlCNF_satisfies_boundaryAssignment V,
        tmVerifierInitialStackCNF_satisfies_boundaryAssignment V p⟩
  · exact tmVerifierEndpointCNF_satisfies_boundaryAssignment V p

theorem tmVerifierBoundaryAssignment_satisfies_instancePrefix
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier) :
    CNF.Satisfies (tmVerifierInstanceInputPrefixCNF V x)
      tmVerifierBoundaryAssignment :=
  tmVerifierInitialStackCNF_satisfies_instancePrefix V x c tmVerifierBoundaryAssignment
    (tmVerifierInitialStackCNF_satisfies_boundaryAssignment V (x, c))

theorem tmVerifierAcceptedRun_boundaryCNF_satisfies
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (run : TMVerifierAcceptedRun V x c) :
    CNF.Satisfies (tmVerifierFixedPairBoundaryCNF V (x, c))
      run.boundaryAssignment := by
  simpa [TMVerifierAcceptedRun.boundaryAssignment] using
    tmVerifierFixedPairBoundaryCNF_satisfies_boundaryAssignment V (x, c)

theorem tmVerifierAcceptedRun_instancePrefix_satisfies
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (run : TMVerifierAcceptedRun V x c) :
    CNF.Satisfies (tmVerifierInstanceInputPrefixCNF V x)
      run.boundaryAssignment := by
  simpa [TMVerifierAcceptedRun.boundaryAssignment] using
    tmVerifierBoundaryAssignment_satisfies_instancePrefix V x c

/-! ### Run-indexed finite-control assignment -/

/-- The tableau configuration selected at macro time `t` by iterating from the verifier input. -/
noncomputable def tmVerifierRunCfgAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) :
    (tmVerifierTM V).Cfg :=
  match (flip bind (tmVerifierTM V).step)^[t] (some (tmVerifierInitialCfg V p)) with
  | some cfg => cfg
  | none => tmVerifierOutputCfg V true

/--
Control assignment induced by the selected macro configurations.

It sets exactly the selected label and state atoms for each macro time to true.
Stack atoms are left false in this slice.
-/
noncomputable def tmVerifierControlRunAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) : Assignment :=
  by
    classical
    exact fun var =>
      decide
        (∃ t, var = (tmVerifierLabelAtom V t (tmVerifierRunCfgAt V p t).l).var ∨
          var = (tmVerifierStateAtom V t (tmVerifierRunCfgAt V p t).var).var)

theorem tmVerifierLabelAtom_var_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    {t u : Nat} {label₁ label₂ : Option (tmVerifierTM V).Λ}
    (h : (tmVerifierLabelAtom V t label₁).var =
        (tmVerifierLabelAtom V u label₂).var) :
    t = u ∧ label₁ = label₂ := by
  have hTail :
      Nat.pair t (Nat.pair 0 (Nat.pair 0 (tmVerifierLabelCode V label₁))) =
        Nat.pair u (Nat.pair 0 (Nat.pair 0 (tmVerifierLabelCode V label₂))) := by
    simpa [tmVerifierLabelAtom, tmVerifierTableauAtom, tmVerifierTableauVar,
      TMVerifierTableauVarKind.tag] using (Nat.pair_eq_pair.mp h).2
  have htu : t = u := (Nat.pair_eq_pair.mp hTail).1
  subst u
  have hPayload : tmVerifierLabelCode V label₁ = tmVerifierLabelCode V label₂ := by
    have hRest₁ := (Nat.pair_eq_pair.mp hTail).2
    have hRest₂ := (Nat.pair_eq_pair.mp hRest₁).2
    exact (Nat.pair_eq_pair.mp hRest₂).2
  have hLabel : label₁ = label₂ := by
    cases label₁ with
    | none =>
        cases label₂ with
        | none => rfl
        | some q =>
            simp [tmVerifierLabelCode] at hPayload
    | some q₁ =>
        cases label₂ with
        | none =>
            simp [tmVerifierLabelCode] at hPayload
        | some q₂ =>
            letI : Fintype (tmVerifierTM V).Λ := (tmVerifierTM V).ΛFin
            have hVal :
                ((Fintype.equivFin (tmVerifierTM V).Λ) q₁).val =
                  ((Fintype.equivFin (tmVerifierTM V).Λ) q₂).val := by
              exact Nat.succ.inj (by simpa [tmVerifierLabelCode] using hPayload)
            have hFin :
                (Fintype.equivFin (tmVerifierTM V).Λ) q₁ =
                  (Fintype.equivFin (tmVerifierTM V).Λ) q₂ := Fin.ext hVal
            exact congrArg some ((Fintype.equivFin (tmVerifierTM V).Λ).injective hFin)
  exact ⟨rfl, hLabel⟩

theorem tmVerifierStateAtom_var_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    {t u : Nat} {state₁ state₂ : (tmVerifierTM V).σ}
    (h : (tmVerifierStateAtom V t state₁).var =
        (tmVerifierStateAtom V u state₂).var) :
    t = u ∧ state₁ = state₂ := by
  have hTail :
      Nat.pair t (Nat.pair 0 (Nat.pair 0 (tmVerifierStateCode V state₁))) =
        Nat.pair u (Nat.pair 0 (Nat.pair 0 (tmVerifierStateCode V state₂))) := by
    simpa [tmVerifierStateAtom, tmVerifierTableauAtom, tmVerifierTableauVar,
      TMVerifierTableauVarKind.tag] using (Nat.pair_eq_pair.mp h).2
  have htu : t = u := (Nat.pair_eq_pair.mp hTail).1
  subst u
  have hPayload : tmVerifierStateCode V state₁ = tmVerifierStateCode V state₂ := by
    have hRest₁ := (Nat.pair_eq_pair.mp hTail).2
    have hRest₂ := (Nat.pair_eq_pair.mp hRest₁).2
    exact (Nat.pair_eq_pair.mp hRest₂).2
  have hState : state₁ = state₂ := by
    letI : Fintype (tmVerifierTM V).σ := (tmVerifierTM V).σFin
    have hVal :
        ((Fintype.equivFin (tmVerifierTM V).σ) state₁).val =
          ((Fintype.equivFin (tmVerifierTM V).σ) state₂).val := by
      simpa [tmVerifierStateCode] using hPayload
    have hFin :
        (Fintype.equivFin (tmVerifierTM V).σ) state₁ =
          (Fintype.equivFin (tmVerifierTM V).σ) state₂ := Fin.ext hVal
    exact (Fintype.equivFin (tmVerifierTM V).σ).injective hFin
  exact ⟨rfl, hState⟩

theorem tmVerifierLabelAtom_var_ne_stateAtom_var
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t u : Nat) (label : Option (tmVerifierTM V).Λ)
    (state : (tmVerifierTM V).σ) :
    (tmVerifierLabelAtom V t label).var ≠ (tmVerifierStateAtom V u state).var := by
  intro h
  have hTag : TMVerifierTableauVarKind.label.tag = TMVerifierTableauVarKind.state.tag := by
    simpa [tmVerifierLabelAtom, tmVerifierStateAtom, tmVerifierTableauAtom,
      tmVerifierTableauVar] using (Nat.pair_eq_pair.mp h).1
  simp [TMVerifierTableauVarKind.tag] at hTag

theorem tmVerifierStateAtom_var_ne_labelAtom_var
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t u : Nat) (state : (tmVerifierTM V).σ)
    (label : Option (tmVerifierTM V).Λ) :
    (tmVerifierStateAtom V t state).var ≠ (tmVerifierLabelAtom V u label).var := by
  intro h
  exact tmVerifierLabelAtom_var_ne_stateAtom_var V u t label state h.symm

theorem tmVerifierLabelAtom_eval_controlRunAssignment_iff
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (label : Option (tmVerifierTM V).Λ) :
    (tmVerifierLabelAtom V t label).eval (tmVerifierControlRunAssignment V p) = true ↔
      label = (tmVerifierRunCfgAt V p t).l := by
  constructor
  · intro h
    have hProp :
        ∃ u, (tmVerifierLabelAtom V t label).var =
            (tmVerifierLabelAtom V u (tmVerifierRunCfgAt V p u).l).var ∨
          (tmVerifierLabelAtom V t label).var =
            (tmVerifierStateAtom V u (tmVerifierRunCfgAt V p u).var).var := by
      simpa [tmVerifierControlRunAssignment, Literal.eval] using h
    rcases hProp with ⟨u, hLabel | hState⟩
    · rcases tmVerifierLabelAtom_var_eq V hLabel with ⟨htu, hEq⟩
      subst u
      exact hEq
    · exact False.elim (tmVerifierLabelAtom_var_ne_stateAtom_var V t u label
        (tmVerifierRunCfgAt V p u).var hState)
  · intro h
    subst label
    change tmVerifierControlRunAssignment V p
      (tmVerifierLabelAtom V t (tmVerifierRunCfgAt V p t).l).var = true
    classical
    exact decide_eq_true (by exact ⟨t, Or.inl rfl⟩)

theorem tmVerifierStateAtom_eval_controlRunAssignment_iff
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (state : (tmVerifierTM V).σ) :
    (tmVerifierStateAtom V t state).eval (tmVerifierControlRunAssignment V p) = true ↔
      state = (tmVerifierRunCfgAt V p t).var := by
  constructor
  · intro h
    have hProp :
        ∃ u, (tmVerifierStateAtom V t state).var =
            (tmVerifierLabelAtom V u (tmVerifierRunCfgAt V p u).l).var ∨
          (tmVerifierStateAtom V t state).var =
            (tmVerifierStateAtom V u (tmVerifierRunCfgAt V p u).var).var := by
      simpa [tmVerifierControlRunAssignment, Literal.eval] using h
    rcases hProp with ⟨u, hLabel | hState⟩
    · exact False.elim (tmVerifierStateAtom_var_ne_labelAtom_var V t u state
        (tmVerifierRunCfgAt V p u).l hLabel)
    · rcases tmVerifierStateAtom_var_eq V hState with ⟨htu, hEq⟩
      subst u
      exact hEq
  · intro h
    subst state
    change tmVerifierControlRunAssignment V p
      (tmVerifierStateAtom V t (tmVerifierRunCfgAt V p t).var).var = true
    classical
    exact decide_eq_true (by exact ⟨t, Or.inr rfl⟩)

theorem tmVerifierLabelAtomsAt_nodup
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat) :
    (tmVerifierLabelAtomsAt V t).Nodup := by
  classical
  letI : Fintype (tmVerifierTM V).Λ := (tmVerifierTM V).ΛFin
  letI : Fintype (Option (tmVerifierTM V).Λ) := inferInstance
  rw [tmVerifierLabelAtomsAt]
  exact (Finset.nodup_toList
    (Finset.univ : Finset (Option (tmVerifierTM V).Λ))).map
      (tmVerifierLabelAtom_injective V t)

theorem tmVerifierStateAtomsAt_nodup
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat) :
    (tmVerifierStateAtomsAt V t).Nodup := by
  classical
  letI : Fintype (tmVerifierTM V).σ := (tmVerifierTM V).σFin
  rw [tmVerifierStateAtomsAt]
  exact (Finset.nodup_toList
    (Finset.univ : Finset (tmVerifierTM V).σ)).map
      (tmVerifierStateAtom_injective V t)

theorem tmVerifierExactlyOneLabelCNFAt_satisfies_controlRunAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) :
    CNF.Satisfies (tmVerifierExactlyOneLabelCNFAt V t)
      (tmVerifierControlRunAssignment V p) := by
  let selected := (tmVerifierRunCfgAt V p t).l
  apply CookLevin.exactlyOneCNF_satisfies_of_exists_unique
  · exact tmVerifierLabelAtomsAt_nodup V t
  · exact ⟨tmVerifierLabelAtom V t selected, tmVerifierLabelAtomsAt_mem V t selected,
      (tmVerifierLabelAtom_eval_controlRunAssignment_iff V p t selected).2 rfl⟩
  · intro x hx y hy hxTrue hyTrue
    rcases List.mem_map.mp hx with ⟨label₁, _hlabel₁, rfl⟩
    rcases List.mem_map.mp hy with ⟨label₂, _hlabel₂, rfl⟩
    have h₁ := (tmVerifierLabelAtom_eval_controlRunAssignment_iff V p t label₁).1 hxTrue
    have h₂ := (tmVerifierLabelAtom_eval_controlRunAssignment_iff V p t label₂).1 hyTrue
    subst label₁
    subst label₂
    rfl

theorem tmVerifierExactlyOneStateCNFAt_satisfies_controlRunAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) :
    CNF.Satisfies (tmVerifierExactlyOneStateCNFAt V t)
      (tmVerifierControlRunAssignment V p) := by
  let selected := (tmVerifierRunCfgAt V p t).var
  apply CookLevin.exactlyOneCNF_satisfies_of_exists_unique
  · exact tmVerifierStateAtomsAt_nodup V t
  · exact ⟨tmVerifierStateAtom V t selected, tmVerifierStateAtomsAt_mem V t selected,
      (tmVerifierStateAtom_eval_controlRunAssignment_iff V p t selected).2 rfl⟩
  · intro x hx y hy hxTrue hyTrue
    rcases List.mem_map.mp hx with ⟨state₁, _hstate₁, rfl⟩
    rcases List.mem_map.mp hy with ⟨state₂, _hstate₂, rfl⟩
    have h₁ := (tmVerifierStateAtom_eval_controlRunAssignment_iff V p t state₁).1 hxTrue
    have h₂ := (tmVerifierStateAtom_eval_controlRunAssignment_iff V p t state₂).1 hyTrue
    subst state₁
    subst state₂
    rfl

theorem tmVerifierControlDomainCNFAt_satisfies_controlRunAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) :
    CNF.Satisfies (tmVerifierControlDomainCNFAt V t)
      (tmVerifierControlRunAssignment V p) := by
  rw [tmVerifierControlDomainCNFAt, CNF.satisfies_append]
  exact
    ⟨tmVerifierExactlyOneLabelCNFAt_satisfies_controlRunAssignment V p t,
      tmVerifierExactlyOneStateCNFAt_satisfies_controlRunAssignment V p t⟩

theorem tmVerifierControlDomainRowsCNF_satisfies_controlRunAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) :
    CNF.Satisfies (tmVerifierControlDomainRowsCNF V p)
      (tmVerifierControlRunAssignment V p) := by
  intro c hc
  rw [tmVerifierControlDomainRowsCNF] at hc
  rcases List.mem_flatMap.mp hc with ⟨t, _ht, hc⟩
  exact tmVerifierControlDomainCNFAt_satisfies_controlRunAssignment V p t c hc


end SAT
end ComplexityReduction
