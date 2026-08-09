/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.OfFn
import ComplexityReduction.Legacy.ComplexityReduction.Core.EncodedDecisionProblem

/-!
Finite-domain CSP syntax and semantics.

This module follows the variable-value definition used by Jeavons-Cohen-Gyssens
and by Feder-Vardi: a constraint has a scope, a relation over a finite domain,
and an assignment is a solution when every scoped tuple belongs to its relation.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain

/-- A tuple of arity `k` over domain `D`. -/
abbrev Tuple (D : Type) (k : Nat) : Type :=
  Fin k → D

/-- A total variable assignment over the project-wide natural-number variables. -/
abbrev Assignment (D : Type) : Type :=
  Nat → D

/-- A relation over a finite domain, represented extensionally as a predicate on tuples. -/
structure Rel (D : Type) where
  arity : Nat
  holds : Tuple D arity → Prop

namespace Rel

/-- Tuple membership is relation satisfaction. -/
def Holds {D : Type} (R : Rel D) (t : Tuple D R.arity) : Prop :=
  R.holds t

@[simp]
theorem holds_mk {D : Type} {k : Nat} {P : Tuple D k → Prop} (t : Tuple D k) :
    (Rel.mk k P).Holds t ↔ P t :=
  Iff.rfl

/-- A relation has at least one accepting tuple. -/
def Nonempty {D : Type} (R : Rel D) : Prop :=
  ∃ t : Tuple D R.arity, R.Holds t

end Rel

/-- A finite-domain CSP language: finite domain, finite relation symbols, and arities. -/
structure Language (D : Type) where
  finiteDomain : Fintype D
  Symbol : Type
  finiteSymbol : Fintype Symbol
  relationOf : Symbol → Rel D

namespace Language

instance {D : Type} (Γ : Language D) : Fintype Γ.Symbol :=
  Γ.finiteSymbol

instance {D : Type} (Γ : Language D) : Fintype D :=
  Γ.finiteDomain

/-- Every relation in the language has arity at most `n`. -/
def IsArityBounded {D : Type} (Γ : Language D) (n : Nat) : Prop :=
  ∀ s : Γ.Symbol, (Γ.relationOf s).arity ≤ n

end Language

/-- One constraint applies a language relation symbol to a scope of variables. -/
structure Constraint {D : Type} (Γ : Language D) where
  symbol : Γ.Symbol
  vars : Fin (Γ.relationOf symbol).arity → Nat

/-- A finite-domain CSP formula is a conjunction of constraints. -/
abbrev Formula {D : Type} (Γ : Language D) : Type :=
  List (Constraint Γ)

namespace Constraint

/-- The relation carried by a constraint. -/
def relation {D : Type} {Γ : Language D} (c : Constraint Γ) : Rel D :=
  Γ.relationOf c.symbol

/-- The variable tuple of a constraint as a list. -/
def varsList {D : Type} {Γ : Language D} (c : Constraint Γ) : List Nat :=
  List.ofFn c.vars

@[simp]
theorem varsList_length {D : Type} {Γ : Language D} (c : Constraint Γ) :
    c.varsList.length = c.relation.arity := by
  simp [varsList, relation]

/-- A conservative syntactic size for one finite-domain CSP constraint. -/
def size {D : Type} {Γ : Language D} (c : Constraint Γ) : Nat :=
  1 + c.varsList.length + c.varsList.sum

/-- The tuple induced by an assignment on the variables of this constraint. -/
def assignmentTuple {D : Type} {Γ : Language D} (c : Constraint Γ) (a : Assignment D) :
    Tuple D (Γ.relationOf c.symbol).arity :=
  fun i => a (c.vars i)

/-- A constraint is satisfied when its induced tuple is accepted by its relation. -/
def Satisfies {D : Type} {Γ : Language D} (c : Constraint Γ) (a : Assignment D) :
    Prop :=
  (Γ.relationOf c.symbol).Holds (c.assignmentTuple a)

/-- Rename all variables in one constraint. -/
def mapVars {D : Type} {Γ : Language D} (f : Nat → Nat)
    (c : Constraint Γ) : Constraint Γ where
  symbol := c.symbol
  vars := fun i => f (c.vars i)

@[simp]
theorem mapVars_satisfies_iff {D : Type} {Γ : Language D} (f : Nat → Nat)
    (c : Constraint Γ) (a : Assignment D) :
    Satisfies (mapVars f c) a ↔ Satisfies c (fun x => a (f x)) :=
  Iff.rfl

/-- Constraint satisfaction depends only on the variables in the constraint scope. -/
theorem satisfies_of_eq_on_vars {D : Type} {Γ : Language D} (c : Constraint Γ)
    {a b : Assignment D} (hEq : ∀ i, b (c.vars i) = a (c.vars i))
    (hSat : Satisfies c a) :
    Satisfies c b := by
  have hTuple : assignmentTuple c b = assignmentTuple c a := by
    funext i
    exact hEq i
  simpa [Satisfies, hTuple] using hSat

end Constraint

namespace Formula

/-- A conservative syntactic size for a finite-domain CSP formula. -/
def size {D : Type} {Γ : Language D} (φ : Formula Γ) : Nat :=
  (φ.map Constraint.size).sum

/-- A formula is satisfied when every constraint is satisfied. -/
def Satisfies {D : Type} {Γ : Language D} (φ : Formula Γ) (a : Assignment D) :
    Prop :=
  ∀ c ∈ φ, Constraint.Satisfies c a

/-- Existential satisfiability of a formula. -/
def Satisfiable {D : Type} {Γ : Language D} (φ : Formula Γ) : Prop :=
  ∃ a : Assignment D, Satisfies φ a

/-- Rename all variables in a formula. -/
def mapVars {D : Type} {Γ : Language D} (f : Nat → Nat)
    (φ : Formula Γ) : Formula Γ :=
  φ.map (Constraint.mapVars f)

@[simp]
theorem satisfies_nil {D : Type} {Γ : Language D} (a : Assignment D) :
    Satisfies ([] : Formula Γ) a := by
  simp [Satisfies]

@[simp]
theorem satisfies_cons {D : Type} {Γ : Language D} (c : Constraint Γ)
    (φ : Formula Γ) (a : Assignment D) :
    Satisfies (c :: φ) a ↔ Constraint.Satisfies c a ∧ Satisfies φ a := by
  simp [Satisfies]

@[simp]
theorem satisfies_append {D : Type} {Γ : Language D} (φ ψ : Formula Γ)
    (a : Assignment D) :
    Satisfies (φ ++ ψ) a ↔ Satisfies φ a ∧ Satisfies ψ a := by
  constructor
  · intro h
    constructor
    · intro c hc
      exact h c (List.mem_append.mpr (Or.inl hc))
    · intro c hc
      exact h c (List.mem_append.mpr (Or.inr hc))
  · intro h c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h.1 c hc
    · exact h.2 c hc

@[simp]
theorem mapVars_nil {D : Type} {Γ : Language D} (f : Nat → Nat) :
    mapVars f ([] : Formula Γ) = [] :=
  rfl

@[simp]
theorem mapVars_cons {D : Type} {Γ : Language D} (f : Nat → Nat)
    (c : Constraint Γ) (φ : Formula Γ) :
    mapVars f (c :: φ) = Constraint.mapVars f c :: mapVars f φ :=
  rfl

@[simp]
theorem mapVars_satisfies_iff {D : Type} {Γ : Language D} (f : Nat → Nat)
    (φ : Formula Γ) (a : Assignment D) :
    Satisfies (mapVars f φ) a ↔ Satisfies φ (fun x => a (f x)) := by
  induction φ with
  | nil =>
      simp
  | cons c φ ih =>
      simp [ih]

/-- Formula satisfaction depends only on variables read by its constraints. -/
theorem satisfies_of_eq_on_vars {D : Type} {Γ : Language D} (φ : Formula Γ)
    {a b : Assignment D} (hEq : ∀ c ∈ φ, ∀ i, b (c.vars i) = a (c.vars i))
    (hSat : Satisfies φ a) :
    Satisfies φ b := by
  intro c hc
  exact Constraint.satisfies_of_eq_on_vars c (hEq c hc) (hSat c hc)

end Formula

/-- Raw encoded instances for formulas over a fixed finite-domain CSP language. -/
def formulaEncodedType {D : Type} (Γ : Language D) : EncodedType :=
  EncodedType.raw (Formula Γ)

/-- The fixed-language finite-domain CSP decision problem. -/
def cspDecisionProblem {D : Type} (Γ : Language D) : EncodedDecisionProblem where
  Instance := formulaEncodedType Γ
  isYes := Formula.Satisfiable

end FiniteDomain
end CSP
end ComplexityReduction
