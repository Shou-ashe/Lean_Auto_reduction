/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
Basic Boolean SAT literals.

The local SAT layer uses natural-number variable names and total Boolean
assignments. This keeps the first CSP-to-3SAT bridge independent of any
particular finite-variable encoding.
-/

namespace ComplexityReduction
namespace SAT

/-- Boolean assignments for SAT-style formulas. -/
abbrev Assignment : Type :=
  Nat → Bool

/-- A literal is a variable together with a negation bit. -/
structure Literal where
  var : Nat
  neg : Bool
  deriving DecidableEq, Repr

namespace Literal

/-- Evaluate a literal under a Boolean assignment. -/
def eval (l : Literal) (a : Assignment) : Bool :=
  if l.neg then !(a l.var) else a l.var

/-- Positive literal `x_var`. -/
def positive (var : Nat) : Literal :=
  { var := var, neg := false }

/-- Negative literal `¬x_var`. -/
def negative (var : Nat) : Literal :=
  { var := var, neg := true }

@[simp]
theorem eval_positive (a : Assignment) (var : Nat) :
    eval (positive var) a = a var :=
  rfl

@[simp]
theorem eval_negative (a : Assignment) (var : Nat) :
    eval (negative var) a = !(a var) :=
  rfl

end Literal

end SAT
end ComplexityReduction
