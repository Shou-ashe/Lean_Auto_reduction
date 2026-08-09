/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Order.Interval.Finset.Defs
import ComplexityReduction.Legacy.ComplexityReduction.CSP.FiniteDomain.FiniteSupport

/-!
Language and formula bounds for finite-domain CSPs.

These helpers expose finite arity and support lists to generated reductions.
They are deliberately small wrappers around the existing finite-support API.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain

namespace Language

/-- Arities of all relation symbols in a finite-domain language. -/
noncomputable def symbolArityList {D : Type} (Γ : Language D) : List Nat := by
  classical
  exact ((Finset.univ : Finset Γ.Symbol).toList).map fun s => (Γ.relationOf s).arity

/-- Maximum arity among relation symbols of a fixed finite-domain language. -/
noncomputable def maxArity {D : Type} (Γ : Language D) : Nat :=
  (Finset.univ : Finset Γ.Symbol).sup fun s => (Γ.relationOf s).arity

theorem arity_le_maxArity {D : Type} (Γ : Language D) (s : Γ.Symbol) :
    (Γ.relationOf s).arity ≤ Γ.maxArity := by
  classical
  exact Finset.le_sup
    (s := (Finset.univ : Finset Γ.Symbol))
    (f := fun s => (Γ.relationOf s).arity)
    (b := s)
    (Finset.mem_univ s)

theorem maxArity_isArityBound {D : Type} (Γ : Language D) :
    Γ.IsArityBounded Γ.maxArity := by
  intro s
  exact Γ.arity_le_maxArity s

theorem isArityBounded_maxArity {D : Type} (Γ : Language D) :
    Γ.IsArityBounded Γ.maxArity :=
  Γ.maxArity_isArityBound

end Language

namespace Formula

/-- The finite support of a formula as a list. -/
noncomputable def supportList {D : Type} {Γ : Language D} (φ : Formula Γ) : List Nat :=
  (FiniteSupport.formulaVars φ).toList

@[simp]
theorem mem_supportList {D : Type} {Γ : Language D} (φ : Formula Γ) (x : Nat) :
    x ∈ supportList φ ↔ x ∈ FiniteSupport.formulaVars φ := by
  simp [supportList]

end Formula

end FiniteDomain
end CSP
end ComplexityReduction
