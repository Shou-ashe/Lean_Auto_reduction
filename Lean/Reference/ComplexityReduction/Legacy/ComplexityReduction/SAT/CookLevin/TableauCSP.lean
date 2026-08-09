/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.Tableau
import ComplexityReduction.Legacy.ComplexityReduction.CSP.FiniteDomain.Basic

/-!
Finite-domain CSP view of local Cook-Levin tableau predicates.

Cook-Levin tableau clauses are local predicates over finitely many Boolean
tableau atoms.  This module exposes that local view as a one-relation
finite-domain CSP language over `Bool`.
-/

namespace ComplexityReduction
namespace SAT
namespace CookLevin
namespace TableauCSP

open ComplexityReduction.CSP.FiniteDomain

/-- A reference to one Boolean tableau atom. -/
structure TableauAtomRef where
  kind : TableauVarKind
  time : Nat
  cell : Nat
  payload : Nat
  deriving DecidableEq, Repr

namespace TableauAtomRef

/-- The SAT/CSP variable number associated with a tableau atom reference. -/
def var (ref : TableauAtomRef) : Nat :=
  tableauVar ref.kind ref.time ref.cell ref.payload

end TableauAtomRef

/-- A finite local tableau predicate over Boolean atom values. -/
structure LocalPredicate where
  arity : Nat
  accepts : Tuple Bool arity → Prop

namespace LocalPredicate

/-- Interpret a local tableau predicate as a finite-domain relation over `Bool`. -/
def rel (P : LocalPredicate) : Rel Bool where
  arity := P.arity
  holds := P.accepts

/-- One-symbol finite-domain language for a local tableau predicate. -/
def language (P : LocalPredicate) : Language Bool where
  finiteDomain := inferInstance
  Symbol := Unit
  finiteSymbol := inferInstance
  relationOf := fun _ => P.rel

/-- A CSP constraint applying the local tableau predicate to a variable scope. -/
def constraint (P : LocalPredicate) (scope : Fin P.arity → Nat) :
    Constraint P.language where
  symbol := ()
  vars := scope

/-- A singleton CSP formula for one local tableau predicate. -/
def formula (P : LocalPredicate) (scope : Fin P.arity → Nat) :
    Formula P.language :=
  [P.constraint scope]

/-- Scope obtained from concrete tableau atom references. -/
def atomScope (P : LocalPredicate) (refs : Fin P.arity → TableauAtomRef) :
    Fin P.arity → Nat :=
  fun i => (refs i).var

/-- Singleton formula whose variables are concrete tableau atom references. -/
def formulaOfRefs (P : LocalPredicate) (refs : Fin P.arity → TableauAtomRef) :
    Formula P.language :=
  P.formula (P.atomScope refs)

@[simp]
theorem constraint_satisfies_iff (P : LocalPredicate)
    (scope : Fin P.arity → Nat) (a : CSP.FiniteDomain.Assignment Bool) :
    Constraint.Satisfies (P.constraint scope) a ↔
      P.accepts (fun i => a (scope i)) := by
  rfl

@[simp]
theorem formula_satisfies_iff (P : LocalPredicate)
    (scope : Fin P.arity → Nat) (a : CSP.FiniteDomain.Assignment Bool) :
    Formula.Satisfies (P.formula scope) a ↔
      P.accepts (fun i => a (scope i)) := by
  simp [formula]

theorem formulaOfRefs_satisfies_iff (P : LocalPredicate)
    (refs : Fin P.arity → TableauAtomRef) (a : CSP.FiniteDomain.Assignment Bool) :
    Formula.Satisfies (P.formulaOfRefs refs) a ↔
      P.accepts (fun i => a ((refs i).var)) := by
  simp [formulaOfRefs, atomScope]

end LocalPredicate

end TableauCSP
end CookLevin
end SAT
end ComplexityReduction
