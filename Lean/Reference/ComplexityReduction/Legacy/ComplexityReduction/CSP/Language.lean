/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.CSP.BoolRel
import Mathlib.Order.Interval.Finset.Defs

/-!
Finite Boolean CSP languages.

The language is represented as a finite family of relations. We keep symbols
abstract but finite so that the same development can later be instantiated with
named relation signatures or with a concrete enumeration.
-/

namespace ComplexityReduction
namespace CSP

/-- A finite Boolean CSP language. -/
structure BoolLanguage where
  Symbol : Type
  finiteSymbol : Fintype Symbol
  relationOf : Symbol → BoolRel

namespace BoolLanguage

instance (Γ : BoolLanguage) : Fintype Γ.Symbol :=
  Γ.finiteSymbol

/-- Every relation in the language has arity at most `n`. -/
def IsArityBounded (Γ : BoolLanguage) (n : Nat) : Prop :=
  ∀ s : Γ.Symbol, (Γ.relationOf s).arity ≤ n

/-- The MVP bound used by the first local 3SAT bridge. -/
abbrev IsThreeBounded (Γ : BoolLanguage) : Prop :=
  Γ.IsArityBounded 3

/-- Maximum arity among relation symbols of a fixed finite language. -/
noncomputable def maxArity (Γ : BoolLanguage) : Nat :=
  (Finset.univ : Finset Γ.Symbol).sup fun s => (Γ.relationOf s).arity

/-- Maximum falsifying truth-table block size among symbols of a fixed finite language. -/
noncomputable def maxFalsifyingTuples (Γ : BoolLanguage) : Nat :=
  (Finset.univ : Finset Γ.Symbol).sup fun s => (Γ.relationOf s).falsifyingTuples.card

theorem arity_le_maxArity (Γ : BoolLanguage) (s : Γ.Symbol) :
    (Γ.relationOf s).arity ≤ Γ.maxArity := by
  classical
  exact Finset.le_sup
    (s := (Finset.univ : Finset Γ.Symbol))
    (f := fun s => (Γ.relationOf s).arity)
    (b := s)
    (Finset.mem_univ s)

theorem isArityBounded_maxArity (Γ : BoolLanguage) :
    Γ.IsArityBounded Γ.maxArity := by
  intro s
  exact Γ.arity_le_maxArity s

theorem falsifyingTuples_card_le_maxFalsifyingTuples (Γ : BoolLanguage) (s : Γ.Symbol) :
    (Γ.relationOf s).falsifyingTuples.card ≤ Γ.maxFalsifyingTuples := by
  classical
  exact Finset.le_sup
    (s := (Finset.univ : Finset Γ.Symbol))
    (f := fun s => (Γ.relationOf s).falsifyingTuples.card)
    (b := s)
    (Finset.mem_univ s)

end BoolLanguage

end CSP
end ComplexityReduction
