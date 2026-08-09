/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Order.Interval.Finset.Defs
import ComplexityReduction.Legacy.ComplexityReduction.CSP.FiniteDomain.Basic

/-!
Finite-variable support for finite-domain CSP formulas.

A finite-domain CSP formula is a finite conjunction of constraints over the
project-wide natural-number variable supply.  This module records the finite set
of variables read by a constraint or formula, and packages the standard fact
that satisfaction only depends on those variables.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain
namespace FiniteSupport

/-- Natural-number variables mentioned by one finite-domain CSP constraint. -/
def constraintVars {D : Type} {Γ : Language D} (c : Constraint Γ) : Finset Nat :=
  (Finset.univ : Finset (Fin (Γ.relationOf c.symbol).arity)).image c.vars

/-- Natural-number variables mentioned by a finite-domain CSP formula. -/
def formulaVars {D : Type} {Γ : Language D} : Formula Γ → Finset Nat
  | [] => ∅
  | c :: φ => constraintVars c ∪ formulaVars φ

@[simp]
theorem formulaVars_nil {D : Type} {Γ : Language D} :
    formulaVars ([] : Formula Γ) = ∅ :=
  rfl

@[simp]
theorem formulaVars_cons {D : Type} {Γ : Language D} (c : Constraint Γ) (φ : Formula Γ) :
    formulaVars (c :: φ) = constraintVars c ∪ formulaVars φ :=
  rfl

@[simp]
theorem formulaVars_append {D : Type} {Γ : Language D} (φ ψ : Formula Γ) :
    formulaVars (φ ++ ψ) = formulaVars φ ∪ formulaVars ψ := by
  induction φ with
  | nil =>
      simp [formulaVars]
  | cons c φ ih =>
      simp [formulaVars, ih, Finset.union_assoc]

/-- Every scoped variable of a constraint appears in its finite support. -/
theorem mem_constraintVars {D : Type} {Γ : Language D} (c : Constraint Γ)
    (i : Fin (Γ.relationOf c.symbol).arity) :
    c.vars i ∈ constraintVars c :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- Constraint support is included in formula support for constraints in the formula. -/
theorem constraintVars_subset_formulaVars_of_mem {D : Type} {Γ : Language D}
    {φ : Formula Γ} {c : Constraint Γ} (hc : c ∈ φ) :
    constraintVars c ⊆ formulaVars φ := by
  induction φ with
  | nil =>
      simp at hc
  | cons d ds ih =>
      simp [formulaVars] at hc ⊢
      rcases hc with hEq | hc
      · subst hEq
        intro x hx
        exact Finset.mem_union.mpr (Or.inl hx)
      · intro x hx
        exact Finset.mem_union.mpr (Or.inr (ih hc hx))

/-- Every scoped variable of a formula constraint appears in formula support. -/
theorem var_mem_formulaVars_of_constraint_mem {D : Type} {Γ : Language D}
    {φ : Formula Γ} {c : Constraint Γ} (hc : c ∈ φ)
    (i : Fin (Γ.relationOf c.symbol).arity) :
    c.vars i ∈ formulaVars φ :=
  constraintVars_subset_formulaVars_of_mem hc (mem_constraintVars c i)

/-- Largest variable in a finite support, or zero when the support is empty. -/
noncomputable def maxVar {D : Type} {Γ : Language D} (φ : Formula Γ) : Nat :=
  (formulaVars φ).sup id

/-- A strict upper bound for variables mentioned by a formula. -/
noncomputable def formulaVarBound {D : Type} {Γ : Language D} (φ : Formula Γ) : Nat :=
  maxVar φ + 1

/-- A common alias for the first auxiliary variable after a source formula. -/
noncomputable def auxBaseAfterFormula {D : Type} {Γ : Language D} (φ : Formula Γ) : Nat :=
  formulaVarBound φ

theorem var_le_maxVar {D : Type} {Γ : Language D} {φ : Formula Γ} {x : Nat}
    (hx : x ∈ formulaVars φ) :
    x ≤ maxVar φ := by
  exact Finset.le_sup (f := id) hx

theorem var_lt_formulaVarBound {D : Type} {Γ : Language D} {φ : Formula Γ} {x : Nat}
    (hx : x ∈ formulaVars φ) :
    x < formulaVarBound φ :=
  Nat.lt_succ_of_le (var_le_maxVar hx)

theorem constraint_var_lt_formulaVarBound_of_mem {D : Type} {Γ : Language D}
    {φ : Formula Γ} {c : Constraint Γ} (hc : c ∈ φ)
    (i : Fin (Γ.relationOf c.symbol).arity) :
    c.vars i < formulaVarBound φ :=
  var_lt_formulaVarBound (var_mem_formulaVars_of_constraint_mem hc i)

theorem sourceFresh_at_formulaVarBound {D : Type} {Γ : Language D} (φ : Formula Γ) :
    ∀ c ∈ φ, ∀ i : Fin (Γ.relationOf c.symbol).arity, c.vars i < formulaVarBound φ := by
  intro c hc i
  exact constraint_var_lt_formulaVarBound_of_mem hc i

/-- Satisfaction is invariant under changing variables outside formula support. -/
theorem formula_satisfies_iff_of_agree {D : Type} {Γ : Language D}
    {φ : Formula Γ} {a b : Assignment D}
    (hAgree : ∀ x ∈ formulaVars φ, a x = b x) :
    Formula.Satisfies φ a ↔ Formula.Satisfies φ b := by
  constructor
  · intro h c hc
    have hTuple : c.assignmentTuple a = c.assignmentTuple b := by
      funext i
      exact hAgree (c.vars i) (var_mem_formulaVars_of_constraint_mem hc i)
    change (Γ.relationOf c.symbol).Holds (c.assignmentTuple b)
    rw [← hTuple]
    exact h c hc
  · intro h c hc
    have hTuple : c.assignmentTuple a = c.assignmentTuple b := by
      funext i
      exact hAgree (c.vars i) (var_mem_formulaVars_of_constraint_mem hc i)
    change (Γ.relationOf c.symbol).Holds (c.assignmentTuple a)
    rw [hTuple]
    exact h c hc

/-- Turn a finite-support valuation into a total finite-domain assignment. -/
def assignmentOf {D : Type} [Inhabited D] {vars : Finset Nat}
    (values : {x : Nat // x ∈ vars} → D) : Assignment D :=
  fun x => if h : x ∈ vars then values ⟨x, h⟩ else default

@[simp]
theorem assignmentOf_eq_of_mem {D : Type} [Inhabited D] {vars : Finset Nat}
    (values : {x : Nat // x ∈ vars} → D) {x : Nat} (hx : x ∈ vars) :
    assignmentOf values x = values ⟨x, hx⟩ := by
  simp [assignmentOf, hx]

/-- A finite-support witness for satisfiability. -/
def SearchWitness {D : Type} [Inhabited D] {Γ : Language D} (φ : Formula Γ) : Prop :=
  ∃ values : {x : Nat // x ∈ formulaVars φ} → D,
    Formula.Satisfies φ (assignmentOf values)

/-- Noncomputable finite-support satisfiability search wrapper. -/
noncomputable def decide {D : Type} [Inhabited D] {Γ : Language D} (φ : Formula Γ) :
    Bool := by
  classical
  exact if SearchWitness φ then true else false

theorem searchWitness_iff_satisfiable {D : Type} [Inhabited D] {Γ : Language D}
    (φ : Formula Γ) :
    SearchWitness φ ↔ Formula.Satisfiable φ := by
  constructor
  · rintro ⟨values, hSat⟩
    exact ⟨assignmentOf values, hSat⟩
  · rintro ⟨a, hSat⟩
    refine ⟨fun x => a x.val, ?_⟩
    exact (formula_satisfies_iff_of_agree (φ := φ)
      (a := assignmentOf (fun x => a x.val)) (b := a) (by
        intro x hx
        simp [assignmentOf, hx])).2 hSat

theorem decide_eq_true_iff {D : Type} [Inhabited D] {Γ : Language D} (φ : Formula Γ) :
    decide φ = true ↔ Formula.Satisfiable φ := by
  classical
  unfold decide
  by_cases h : SearchWitness φ
  · simp [h, (searchWitness_iff_satisfiable φ).1 h]
  · have hUnsat : ¬ Formula.Satisfiable φ := by
      intro hSat
      exact h ((searchWitness_iff_satisfiable φ).2 hSat)
    simp [h, hUnsat]

end FiniteSupport
end FiniteDomain
end CSP
end ComplexityReduction
