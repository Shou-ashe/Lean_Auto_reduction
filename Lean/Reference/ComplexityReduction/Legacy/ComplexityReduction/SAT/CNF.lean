/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.BooleanAlgebra
import ComplexityReduction.Legacy.ComplexityReduction.SAT.Literal

/-!
List-based CNF syntax and the local "3SAT" instance type.

The project-local 3CNF predicate uses clauses of length at most three. This is
the standard variant needed by the first Boolean-CSP upper-bound reduction and
allows empty clauses to represent immediate contradictions.
-/

namespace ComplexityReduction
namespace SAT

/-- A clause is a finite disjunction of literals. -/
abbrev Clause : Type :=
  List Literal

/-- A CNF formula is a finite conjunction of clauses. -/
abbrev CNF : Type :=
  List Clause

namespace Clause

/-- A clause is satisfied when at least one literal evaluates to true. -/
def Satisfies (c : Clause) (a : Assignment) : Prop :=
  ∃ l ∈ c, l.eval a = true

end Clause

namespace CNF

/-- A CNF formula is satisfied when every clause is satisfied. -/
def Satisfies (φ : CNF) (a : Assignment) : Prop :=
  ∀ c ∈ φ, Clause.Satisfies c a

/-- Existential satisfiability of a CNF formula. -/
def Satisfiable (φ : CNF) : Prop :=
  ∃ a : Assignment, Satisfies φ a

/-- Local 3CNF predicate: every clause has length at most three. -/
def IsThreeCNF (φ : CNF) : Prop :=
  ∀ c ∈ φ, c.length ≤ 3

@[simp]
theorem satisfies_nil (a : Assignment) :
    Satisfies ([] : CNF) a :=
  by simp [Satisfies]

@[simp]
theorem satisfies_append (φ ψ : CNF) (a : Assignment) :
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

end CNF

/-- A bundled 3CNF formula. -/
structure ThreeCNF where
  clauses : CNF
  isThree : CNF.IsThreeCNF clauses

namespace ThreeCNF

/-- Satisfaction of a bundled 3CNF formula. -/
def Satisfies (φ : ThreeCNF) (a : Assignment) : Prop :=
  CNF.Satisfies φ.clauses a

/-- Existential satisfiability of a bundled 3CNF formula. -/
def Satisfiable (φ : ThreeCNF) : Prop :=
  ∃ a : Assignment, Satisfies φ a

@[simp]
theorem satisfies_mk (φ : CNF) (h : CNF.IsThreeCNF φ) (a : Assignment) :
    Satisfies ({ clauses := φ, isThree := h } : ThreeCNF) a ↔ CNF.Satisfies φ a :=
  Iff.rfl

end ThreeCNF

end SAT
end ComplexityReduction
