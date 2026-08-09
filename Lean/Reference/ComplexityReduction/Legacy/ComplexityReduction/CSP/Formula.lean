/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.CSP.Language
import ComplexityReduction.Legacy.ComplexityReduction.SAT.Literal

/-!
Boolean CSP formulas over a fixed finite language.
-/

namespace ComplexityReduction
namespace CSP

open SAT

/-- One constraint applies a language relation symbol to a tuple of variables. -/
structure Constraint (Γ : BoolLanguage) where
  symbol : Γ.Symbol
  vars : Fin (Γ.relationOf symbol).arity → Nat

/-- A CSP formula is a conjunction of constraints. -/
abbrev Formula (Γ : BoolLanguage) : Type :=
  List (Constraint Γ)

namespace Constraint

/-- The relation carried by a constraint. -/
def relation {Γ : BoolLanguage} (c : Constraint Γ) : BoolRel :=
  Γ.relationOf c.symbol

/-- The variable tuple of a constraint as a list. -/
def varsList {Γ : BoolLanguage} (c : Constraint Γ) : List Nat :=
  List.ofFn c.vars

/-- A conservative syntactic size for one CSP constraint. -/
def size {Γ : BoolLanguage} (c : Constraint Γ) : Nat :=
  1 + c.varsList.length + c.varsList.sum

/-- The largest variable name mentioned by one constraint, or zero for arity zero. -/
def maxVar {Γ : BoolLanguage} (c : Constraint Γ) : Nat :=
  c.varsList.foldl Nat.max 0

@[simp]
theorem varsList_length {Γ : BoolLanguage} (c : Constraint Γ) :
    c.varsList.length = c.relation.arity := by
  simp [varsList, relation]

/-- The tuple induced by an assignment on the variables of this constraint. -/
def assignmentTuple {Γ : BoolLanguage} (c : Constraint Γ) (a : Assignment) :
    BoolTuple (Γ.relationOf c.symbol).arity :=
  fun i => a (c.vars i)

/-- A constraint is satisfied when its induced tuple is accepted by its relation. -/
def Satisfies {Γ : BoolLanguage} (c : Constraint Γ) (a : Assignment) : Prop :=
  (Γ.relationOf c.symbol).Holds (c.assignmentTuple a)

end Constraint

namespace Formula

/-- A conservative syntactic size for a CSP formula. -/
def size {Γ : BoolLanguage} (φ : Formula Γ) : Nat :=
  (φ.map Constraint.size).sum

/-- The largest variable name mentioned by a formula, or zero for the empty formula. -/
def maxVar {Γ : BoolLanguage} (φ : Formula Γ) : Nat :=
  φ.foldl (fun acc c => Nat.max acc (Constraint.maxVar c)) 0

/-- A CSP formula is satisfied when every constraint is satisfied. -/
def Satisfies {Γ : BoolLanguage} (φ : Formula Γ) (a : Assignment) : Prop :=
  ∀ c ∈ φ, Constraint.Satisfies c a

/-- Existential satisfiability of a CSP formula. -/
def Satisfiable {Γ : BoolLanguage} (φ : Formula Γ) : Prop :=
  ∃ a : Assignment, Satisfies φ a

@[simp]
theorem satisfies_nil {Γ : BoolLanguage} (a : Assignment) :
    Satisfies ([] : Formula Γ) a :=
  by simp [Satisfies]

@[simp]
theorem size_nil {Γ : BoolLanguage} :
    size ([] : Formula Γ) = 0 :=
  rfl

@[simp]
theorem maxVar_nil {Γ : BoolLanguage} :
    maxVar ([] : Formula Γ) = 0 :=
  rfl

@[simp]
theorem satisfies_cons {Γ : BoolLanguage} (c : Constraint Γ) (φ : Formula Γ)
    (a : Assignment) :
    Satisfies (c :: φ) a ↔ Constraint.Satisfies c a ∧ Satisfies φ a := by
  simp [Satisfies]

@[simp]
theorem size_cons {Γ : BoolLanguage} (c : Constraint Γ) (φ : Formula Γ) :
    size (c :: φ) = Constraint.size c + size φ := by
  simp [size]

@[simp]
theorem maxVar_cons {Γ : BoolLanguage} (c : Constraint Γ) (φ : Formula Γ) :
    maxVar (c :: φ) =
      φ.foldl (fun acc d => Nat.max acc (Constraint.maxVar d)) (Constraint.maxVar c) := by
  rfl

@[simp]
theorem satisfies_append {Γ : BoolLanguage} (φ ψ : Formula Γ) (a : Assignment) :
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
theorem satisfiable_nil {Γ : BoolLanguage} :
    Satisfiable ([] : Formula Γ) := by
  exact ⟨fun _ => false, satisfies_nil _⟩

theorem satisfiable_of_satisfiable_append_left {Γ : BoolLanguage} {φ ψ : Formula Γ} :
    Satisfiable (φ ++ ψ) → Satisfiable φ := by
  rintro ⟨a, h⟩
  exact ⟨a, ((satisfies_append φ ψ a).1 h).1⟩

theorem satisfiable_of_satisfiable_append_right {Γ : BoolLanguage} {φ ψ : Formula Γ} :
    Satisfiable (φ ++ ψ) → Satisfiable ψ := by
  rintro ⟨a, h⟩
  exact ⟨a, ((satisfies_append φ ψ a).1 h).2⟩

end Formula

end CSP
end ComplexityReduction
