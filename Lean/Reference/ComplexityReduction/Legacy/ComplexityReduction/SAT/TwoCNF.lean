/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Finset.Basic
import ComplexityReduction.Legacy.ComplexityReduction.SAT.Literal

/-!
Direct 2CNF syntax used by generic Boolean-CSP tractable routes.
-/

namespace ComplexityReduction
namespace SAT
namespace TwoCNF

/-- A direct 2CNF literal.  `positive = false` denotes negation. -/
structure Literal where
  var : Nat
  positive : Bool
  deriving DecidableEq, Repr

namespace Literal

/-- Literal evaluation under a SAT assignment. -/
def eval (l : Literal) (a : Assignment) : Bool :=
  if l.positive then a l.var else !(a l.var)

end Literal

/-- A 2CNF clause: empty, unit, or binary. -/
inductive Clause where
  | empty
  | unit (l : Literal)
  | binary (l₁ l₂ : Literal)
  deriving DecidableEq, Repr

namespace Clause

/-- Variables mentioned by a 2CNF clause. -/
def vars : Clause → Finset Nat
  | empty => ∅
  | unit l => {l.var}
  | binary l₁ l₂ => {l₁.var, l₂.var}

/-- Clause satisfaction. -/
def Satisfies : Clause → Assignment → Prop
  | empty, _ => False
  | unit l, a => l.eval a = true
  | binary l₁ l₂, a => l₁.eval a = true ∨ l₂.eval a = true

end Clause

/-- A direct 2CNF formula is a conjunction of direct 2CNF clauses. -/
abbrev CNF : Type :=
  List Clause

namespace CNF

/-- Variables mentioned by a direct 2CNF formula. -/
def vars : CNF → Finset Nat
  | [] => ∅
  | c :: cs => c.vars ∪ vars cs

/-- Satisfaction of a direct 2CNF formula. -/
def Satisfies (φ : CNF) (a : Assignment) : Prop :=
  ∀ c ∈ φ, c.Satisfies a

/-- Existential satisfiability of a direct 2CNF formula. -/
def Satisfiable (φ : CNF) : Prop :=
  ∃ a : Assignment, Satisfies φ a

end CNF
end TwoCNF
end SAT
end ComplexityReduction
