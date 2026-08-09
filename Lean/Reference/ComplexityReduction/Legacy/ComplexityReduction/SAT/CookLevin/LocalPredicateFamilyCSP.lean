/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.List.OfFn
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TableauCSP

/-!
Families of local Cook-Levin predicates as finite-domain CSP formulas.

`TableauCSP` exposes one local tableau predicate as a one-relation Boolean CSP.
This module packages a finite list of local predicate blocks into a single
finite-domain language whose symbols are block indices.
-/

namespace ComplexityReduction
namespace SAT
namespace CookLevin
namespace TableauCSP

open ComplexityReduction.CSP.FiniteDomain

/-- One occurrence of a local predicate with its concrete CSP variable scope. -/
structure LocalPredicateBlock where
  predicate : LocalPredicate
  scope : Fin predicate.arity → Nat

namespace LocalPredicateBlock

/-- Assignment-level satisfaction of one local predicate block. -/
def Satisfies (B : LocalPredicateBlock) (a : CSP.FiniteDomain.Assignment Bool) : Prop :=
  B.predicate.accepts (fun i => a (B.scope i))

/-- The singleton CSP formula associated to one local predicate block. -/
def formula (B : LocalPredicateBlock) : Formula B.predicate.language :=
  B.predicate.formula B.scope

@[simp]
theorem formula_satisfies_iff (B : LocalPredicateBlock)
    (a : CSP.FiniteDomain.Assignment Bool) :
    Formula.Satisfies B.formula a ↔ B.Satisfies a := by
  simp [formula, Satisfies]

end LocalPredicateBlock

/-- A finite family of local Cook-Levin predicate blocks. -/
structure LocalPredicateFamily where
  blocks : List LocalPredicateBlock

namespace LocalPredicateFamily

/-- The finite-domain language whose symbols are indices of local predicate blocks. -/
def language (F : LocalPredicateFamily) : Language Bool where
  finiteDomain := inferInstance
  Symbol := Fin F.blocks.length
  finiteSymbol := inferInstance
  relationOf := fun i => (F.blocks.get i).predicate.rel

/-- Assignment-level satisfaction of every local predicate block in the family. -/
def Satisfies (F : LocalPredicateFamily) (a : CSP.FiniteDomain.Assignment Bool) : Prop :=
  ∀ i : Fin F.blocks.length, (F.blocks.get i).Satisfies a

/-- The CSP constraint corresponding to one indexed family block. -/
def constraint (F : LocalPredicateFamily) (i : Fin F.blocks.length) :
    Constraint F.language where
  symbol := i
  vars := (F.blocks.get i).scope

/-- The finite-domain CSP formula containing one constraint per local block. -/
def formula (F : LocalPredicateFamily) : Formula F.language :=
  List.ofFn fun i : Fin F.blocks.length => F.constraint i

@[simp]
theorem constraint_satisfies_iff (F : LocalPredicateFamily) (i : Fin F.blocks.length)
    (a : CSP.FiniteDomain.Assignment Bool) :
    Constraint.Satisfies (F.constraint i) a ↔ (F.blocks.get i).Satisfies a := by
  rfl

/-- The family formula is satisfied exactly when every local block accepts. -/
theorem formula_satisfies_iff (F : LocalPredicateFamily)
    (a : CSP.FiniteDomain.Assignment Bool) :
    Formula.Satisfies F.formula a ↔ F.Satisfies a := by
  constructor
  · intro h i
    have hi : F.constraint i ∈ F.formula := by
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
    exact (F.constraint_satisfies_iff i a).1 (h (F.constraint i) hi)
  · intro h c hc
    rcases List.mem_ofFn.mp (by simpa [formula] using hc) with ⟨i, rfl⟩
    exact (F.constraint_satisfies_iff i a).2 (h i)

/-- The family formula has one CSP constraint per local predicate block. -/
@[simp]
theorem formula_length (F : LocalPredicateFamily) :
    F.formula.length = F.blocks.length := by
  simp [formula]

end LocalPredicateFamily

/-- Top-level family compiler used by route descriptors. -/
def formulaOfPredicateFamily (F : LocalPredicateFamily) : Formula F.language :=
  F.formula

/-- Correctness of the top-level local predicate family compiler. -/
theorem formulaOfPredicateFamily_satisfies_iff (F : LocalPredicateFamily)
    (a : CSP.FiniteDomain.Assignment Bool) :
    Formula.Satisfies (formulaOfPredicateFamily F) a ↔ F.Satisfies a := by
  simpa [formulaOfPredicateFamily] using F.formula_satisfies_iff a

end TableauCSP
end CookLevin
end SAT
end ComplexityReduction
