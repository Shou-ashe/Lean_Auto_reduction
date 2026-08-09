/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMStackPayloadUniqueness

/-!
Uniqueness of decoded choices selected by stack-domain clauses.

The previous slice proves that active numeric payloads identify dependent
stack symbols.  This file combines that fact with the at-most-one half of the
per-cell domain CNF, yielding uniqueness of the decoded read choice for a
bounded stack cell.
-/

namespace ComplexityReduction
namespace SAT

namespace CookLevin

theorem atMostOneWithCNF_satisfies_no_tail_true
    (x : Literal) (ys : List Literal) (a : Assignment) :
    CNF.Satisfies (atMostOneWithCNF x ys) a →
      ∀ {y : Literal}, y ∈ ys → x.eval a = true → y.eval a = true → False := by
  induction ys generalizing a with
  | nil =>
      intro _ y hy
      cases hy
  | cons head tail ih =>
      intro h y hy hx hyTrue
      rcases List.mem_cons.mp hy with hEq | hyTail
      · have hClause : Clause.Satisfies [Clause.negate x, Clause.negate head] a := by
          exact h _ (by simp [atMostOneWithCNF])
        subst y
        rcases hClause with ⟨lit, hlit, heval⟩
        rcases List.mem_cons.mp hlit with hLit | hLit
        · have hfalse := (Clause.negate_eval_true_iff x a).1 (by simpa [hLit] using heval)
          simp [hx] at hfalse
        · have hLit' : lit = Clause.negate head := by simpa using hLit
          have hfalse := (Clause.negate_eval_true_iff head a).1
            (by simpa [hLit'] using heval)
          simp [hyTrue] at hfalse
      · have hTail : CNF.Satisfies (atMostOneWithCNF x tail) a := by
          intro c hc
          exact h c (by simp [atMostOneWithCNF, hc])
        exact ih a hTail hyTail hx hyTrue

theorem atMostOneCNF_satisfies_eq_of_mem_eval
    (xs : List Literal) (a : Assignment) :
    CNF.Satisfies (atMostOneCNF xs) a →
      ∀ {x y : Literal}, x ∈ xs → y ∈ xs → x.eval a = true → y.eval a = true → x = y := by
  induction xs generalizing a with
  | nil =>
      intro _ x _ hx
      cases hx
  | cons z zs ih =>
      intro h x y hx hy hxTrue hyTrue
      have hsplit :
          CNF.Satisfies (atMostOneWithCNF z zs) a ∧
            CNF.Satisfies (atMostOneCNF zs) a := by
        simpa [atMostOneCNF] using
          (CNF.satisfies_append (atMostOneWithCNF z zs) (atMostOneCNF zs) a).1 h
      rcases List.mem_cons.mp hx with rfl | hxTail
      · rcases List.mem_cons.mp hy with rfl | hyTail
        · rfl
        · exact False.elim
            (atMostOneWithCNF_satisfies_no_tail_true x zs a hsplit.1 hyTail hxTrue hyTrue)
      · rcases List.mem_cons.mp hy with rfl | hyTail
        · exact False.elim
            (atMostOneWithCNF_satisfies_no_tail_true y zs a hsplit.1 hxTail hyTrue hxTrue)
        · exact ih a hsplit.2 hxTail hyTail hxTrue hyTrue

end CookLevin

/-! ### Stack read-choice uniqueness -/

theorem tmVerifierStackReadChoice_atomAt_injective_of_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t cell : Nat) (k : tmVerifierStackIndex V)
    (choice₁ choice₂ : TMVerifierStackReadChoice V k)
    (hmem₁ : choice₁ ∈ tmVerifierStackReadChoices V k)
    (hmem₂ : choice₂ ∈ tmVerifierStackReadChoices V k)
    (hAtom :
      TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice₁ =
        TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice₂) :
    choice₁ = choice₂ := by
  cases choice₁ with
  | empty =>
      cases choice₂ with
      | empty => rfl
      | symbol payload₂ symbol₂ =>
          simp [TMVerifierStackReadChoice.atomAt, tmVerifierStackEmptyAtom,
            tmVerifierStackSymbolAtom, tmVerifierTableauAtom, tmVerifierTableauVar,
            TMVerifierTableauVarKind.tag, Nat.pair_eq_pair] at hAtom
  | symbol payload₁ symbol₁ =>
      cases choice₂ with
      | empty =>
          simp [TMVerifierStackReadChoice.atomAt, tmVerifierStackEmptyAtom,
            tmVerifierStackSymbolAtom, tmVerifierTableauAtom, tmVerifierTableauVar,
            TMVerifierTableauVarKind.tag, Nat.pair_eq_pair] at hAtom
      | symbol payload₂ symbol₂ =>
          have hPayload : payload₁ = payload₂ := by
            simpa [TMVerifierStackReadChoice.atomAt, tmVerifierStackSymbolAtom,
              tmVerifierTableauAtom, tmVerifierTableauVar, Nat.pair_eq_pair] using hAtom
          subst payload₂
          have hSymbol :
              symbol₁ = symbol₂ :=
            tmVerifierStackReadChoice_symbol_eq_of_payloadUnique V
              (tmVerifierStackPayloadUnique V) k payload₁ symbol₁ symbol₂ hmem₁ hmem₂
          subst symbol₂
          rfl

theorem tmVerifierStackReadChoiceDomainCNFAt_satisfies_choice_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackReadChoiceDomainCNFAt V t k cell) a)
    (choice₁ choice₂ : TMVerifierStackReadChoice V k)
    (hmem₁ : choice₁ ∈ tmVerifierStackReadChoices V k)
    (hmem₂ : choice₂ ∈ tmVerifierStackReadChoices V k)
    (htrue₁ :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice₁).eval a = true)
    (htrue₂ :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice₂).eval a = true) :
    choice₁ = choice₂ := by
  let atoms := tmVerifierStackReadChoiceLiteralsAt V t k cell
  have hAtMost : CNF.Satisfies (CookLevin.atMostOneCNF atoms) a := by
    exact (CNF.satisfies_append (CookLevin.atLeastOneCNF atoms)
      (CookLevin.atMostOneCNF atoms) a).1
        (by simpa [tmVerifierStackReadChoiceDomainCNFAt, CookLevin.exactlyOneCNF, atoms]
          using h) |>.2
  have hLitEq :
      TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice₁ =
        TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice₂ := by
    exact CookLevin.atMostOneCNF_satisfies_eq_of_mem_eval atoms a hAtMost
      (by
        dsimp [atoms, tmVerifierStackReadChoiceLiteralsAt]
        exact List.mem_map.mpr ⟨choice₁, hmem₁, rfl⟩)
      (by
        dsimp [atoms, tmVerifierStackReadChoiceLiteralsAt]
        exact List.mem_map.mpr ⟨choice₂, hmem₂, rfl⟩)
      htrue₁ htrue₂
  exact tmVerifierStackReadChoice_atomAt_injective_of_mem V t cell k choice₁ choice₂
    hmem₁ hmem₂ hLitEq

theorem tmVerifierStackCellDomainsCNFAt_satisfies_choice_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a)
    (hcell : cell ∈ tmVerifierCellRange V p)
    (choice₁ choice₂ : TMVerifierStackReadChoice V k)
    (hmem₁ : choice₁ ∈ tmVerifierStackReadChoices V k)
    (hmem₂ : choice₂ ∈ tmVerifierStackReadChoices V k)
    (htrue₁ :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice₁).eval a = true)
    (htrue₂ :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice₂).eval a = true) :
    choice₁ = choice₂ := by
  have hDomain : CNF.Satisfies (tmVerifierStackCellDomainCNFAt V t k cell) a := by
    intro c hc
    exact h c (by
      simp [tmVerifierStackCellDomainsCNFAt]
      exact ⟨cell, hcell, hc⟩)
  exact tmVerifierStackReadChoiceDomainCNFAt_satisfies_choice_eq V t k cell a hDomain
    choice₁ choice₂ hmem₁ hmem₂ htrue₁ htrue₂

theorem tmVerifierDecodedStackCell_choice_eq_of_domain
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a)
    (hcell : cell ∈ tmVerifierCellRange V p)
    (d₁ d₂ : TMVerifierDecodedStackCell V t k cell a) :
    d₁.choice = d₂.choice :=
  tmVerifierStackCellDomainsCNFAt_satisfies_choice_eq V p t k cell a h hcell
    d₁.choice d₂.choice d₁.choice_mem d₂.choice_mem d₁.atom_true d₂.atom_true

end SAT
end ComplexityReduction
