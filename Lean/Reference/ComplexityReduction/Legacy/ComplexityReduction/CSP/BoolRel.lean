/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.BooleanAlgebra

/-!
Boolean relations used by the local CSP library.

A relation is a finite truth table over `Fin arity → Bool`. The arity is part
of the data so that two relations with the same table shape but different
domains remain distinct.
-/

namespace ComplexityReduction
namespace CSP

abbrev BoolTuple (k : Nat) : Type :=
  Fin k → Bool

instance (k : Nat) : Fintype (BoolTuple k) := by
  classical
  infer_instance

instance (k : Nat) : DecidableEq (BoolTuple k) := by
  classical
  infer_instance

/-- A Boolean relation is a finite acceptance table with a fixed arity. -/
structure BoolRel where
  arity : Nat
  accepts : Finset (BoolTuple arity)

namespace BoolRel

@[simp]
theorem mk_arity {k : Nat} (accepts : Finset (BoolTuple k)) :
    (BoolRel.mk k accepts).arity = k :=
  rfl

@[simp]
theorem mk_accepts {k : Nat} (accepts : Finset (BoolTuple k)) :
    (BoolRel.mk k accepts).accepts = accepts :=
  rfl

/-- Tuple membership is relation satisfaction. -/
def Holds (R : BoolRel) (t : BoolTuple R.arity) : Prop :=
  t ∈ R.accepts

/-- A relation has at least one accepting tuple. -/
def Nonempty (R : BoolRel) : Prop :=
  ∃ t : BoolTuple R.arity, R.Holds t

@[simp]
theorem holds_iff_mem (R : BoolRel) (t : BoolTuple R.arity) :
    R.Holds t ↔ t ∈ R.accepts :=
  Iff.rfl

noncomputable instance (R : BoolRel) (t : BoolTuple R.arity) : Decidable (R.Holds t) :=
  by
    classical
    infer_instance

/-- Explicit decidability witness for relation satisfaction. -/
noncomputable def holdsDecidable (R : BoolRel) (t : BoolTuple R.arity) :
    Decidable (R.Holds t) := by
  classical
  infer_instance

/-- Relation nonemptiness is exactly nonemptiness of its accepting truth table. -/
theorem nonempty_iff_accepts_nonempty (R : BoolRel) :
    R.Nonempty ↔ R.accepts.Nonempty := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, ht⟩

/-- The full relation of a given arity. -/
noncomputable def full (k : Nat) : BoolRel where
  arity := k
  accepts := Finset.univ

/-- The empty relation of a given arity. -/
noncomputable def empty (k : Nat) : BoolRel where
  arity := k
  accepts := ∅

/-- The falsifying tuples for a relation. -/
noncomputable def falsifyingTuples (R : BoolRel) : Finset (BoolTuple R.arity) :=
  Finset.univ.filter fun t => t ∉ R.accepts

@[simp]
theorem mem_falsifyingTuples_iff (R : BoolRel) (t : BoolTuple R.arity) :
    t ∈ R.falsifyingTuples ↔ t ∉ R.accepts := by
  classical
  constructor
  · intro h
    have h' : t ∈ (Finset.univ : Finset (BoolTuple R.arity)) ∧ t ∉ R.accepts := by
      simpa [falsifyingTuples] using h
    exact h'.2
  · intro h
    have h' : t ∈ (Finset.univ : Finset (BoolTuple R.arity)) ∧ t ∉ R.accepts := by
      exact ⟨Finset.mem_univ t, h⟩
    simpa [falsifyingTuples] using h'

@[simp]
theorem holds_full (k : Nat) (t : BoolTuple (full k).arity) :
    (full k).Holds t :=
  by
    classical
    change t ∈ (Finset.univ : Finset (BoolTuple k))
    exact Finset.mem_univ t

@[simp]
theorem not_holds_empty (k : Nat) (t : BoolTuple (empty k).arity) :
    ¬ (empty k).Holds t :=
  by
    classical
    change t ∉ (∅ : Finset (BoolTuple k))
    exact Finset.notMem_empty t

@[simp]
theorem nonempty_full (k : Nat) :
    (full k).Nonempty := by
  exact ⟨fun _ => false, holds_full k _⟩

@[simp]
theorem not_nonempty_empty (k : Nat) :
    ¬ (empty k).Nonempty := by
  rintro ⟨t, ht⟩
  exact not_holds_empty k t ht

/-- The complement relation on the same arity. -/
noncomputable def complement (R : BoolRel) : BoolRel where
  arity := R.arity
  accepts := R.falsifyingTuples

@[simp]
theorem holds_complement_iff (R : BoolRel) (t : BoolTuple R.arity) :
    R.complement.Holds t ↔ ¬ R.Holds t := by
  classical
  change t ∈ R.falsifyingTuples ↔ ¬ t ∈ R.accepts
  constructor
  · intro h
    exact (mem_falsifyingTuples_iff R t).1 h
  · intro h
    exact (mem_falsifyingTuples_iff R t).2 h

end BoolRel

end CSP
end ComplexityReduction
