/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP.Classes

/-!
Executable finite reflection for the proof obligations produced by Boolean-CSP
hardness theorems.

The domain structures deliberately expose finite truth tables, so their
deciders do not need `Classical.propDecidable`.  Keeping these deciders as
ordinary definitions lets generated artifacts use kernel-reduced `decide` while
the resulting theorem is still checked by the Lean kernel.
-/

namespace ComplexityReduction
namespace Agent
namespace Reduction
namespace Reflection

open CSP
open Domain.BooleanCSP

/-- Executable membership in a finite Boolean truth table. -/
def holdsDecidable (relation : BoolRel) (tuple : BoolTuple relation.arity) :
    Decidable (relation.Holds tuple) := by
  unfold BoolRel.Holds
  exact Finset.decidableMem tuple relation.accepts

/-- Executable nonemptiness of a finite Boolean relation. -/
def relationNonemptyDecidable (relation : BoolRel) : Decidable relation.Nonempty := by
  unfold BoolRel.Nonempty
  letI : ∀ tuple : BoolTuple relation.arity, Decidable (relation.Holds tuple) :=
    holdsDecidable relation
  infer_instance

def relationZeroValidDecidable (relation : BoolRel) :
    Decidable (BooleanRelation.IsZeroValid relation) := by
  unfold BooleanRelation.IsZeroValid
  exact holdsDecidable relation _

def relationOneValidDecidable (relation : BoolRel) :
    Decidable (BooleanRelation.IsOneValid relation) := by
  unfold BooleanRelation.IsOneValid
  exact holdsDecidable relation _

def relationHornDecidable (relation : BoolRel) :
    Decidable (BooleanRelation.IsHorn relation) := by
  unfold BooleanRelation.IsHorn
  letI : ∀ tuple : BoolTuple relation.arity, Decidable (relation.Holds tuple) :=
    holdsDecidable relation
  infer_instance

def relationDualHornDecidable (relation : BoolRel) :
    Decidable (BooleanRelation.IsDualHorn relation) := by
  unfold BooleanRelation.IsDualHorn
  letI : ∀ tuple : BoolTuple relation.arity, Decidable (relation.Holds tuple) :=
    holdsDecidable relation
  infer_instance

def relationBijunctiveDecidable (relation : BoolRel) :
    Decidable (BooleanRelation.IsBijunctive relation) := by
  unfold BooleanRelation.IsBijunctive
  letI : ∀ tuple : BoolTuple relation.arity, Decidable (relation.Holds tuple) :=
    holdsDecidable relation
  infer_instance

def relationAffineDecidable (relation : BoolRel) :
    Decidable (BooleanRelation.IsAffine relation) := by
  unfold BooleanRelation.IsAffine
  letI : ∀ tuple : BoolTuple relation.arity, Decidable (relation.Holds tuple) :=
    holdsDecidable relation
  infer_instance

/-- Executable test for the six relation-level Schaefer classes. -/
def relationSchaeferTractableDecidable (relation : BoolRel) : Decidable
    (BooleanRelation.IsZeroValid relation ∨ BooleanRelation.IsOneValid relation ∨
      BooleanRelation.IsHorn relation ∨ BooleanRelation.IsDualHorn relation ∨
      BooleanRelation.IsBijunctive relation ∨ BooleanRelation.IsAffine relation) :=
  @instDecidableOr _ _ (relationZeroValidDecidable relation) <|
  @instDecidableOr _ _ (relationOneValidDecidable relation) <|
  @instDecidableOr _ _ (relationHornDecidable relation) <|
  @instDecidableOr _ _ (relationDualHornDecidable relation) <|
  @instDecidableOr _ _ (relationBijunctiveDecidable relation)
    (relationAffineDecidable relation)

/-- Executable proof search for the theorem's relation-nonempty premise. -/
def gammaRelationsNonemptyDecidable (gamma : Gamma) : Decidable
    (∀ symbol : gamma.Symbol, (gamma.relationOf symbol).Nonempty) := by
  letI : ∀ symbol : gamma.Symbol, Decidable ((gamma.relationOf symbol).Nonempty) :=
    fun symbol => relationNonemptyDecidable (gamma.relationOf symbol)
  infer_instance

def gammaZeroValidDecidable (gamma : Gamma) : Decidable gamma.IsZeroValid := by
  unfold Gamma.IsZeroValid
  letI : ∀ symbol : gamma.Symbol,
      Decidable (BooleanRelation.IsZeroValid (gamma.relationOf symbol)) :=
    fun symbol => relationZeroValidDecidable (gamma.relationOf symbol)
  infer_instance

def gammaOneValidDecidable (gamma : Gamma) : Decidable gamma.IsOneValid := by
  unfold Gamma.IsOneValid
  letI : ∀ symbol : gamma.Symbol,
      Decidable (BooleanRelation.IsOneValid (gamma.relationOf symbol)) :=
    fun symbol => relationOneValidDecidable (gamma.relationOf symbol)
  infer_instance

def gammaHornDecidable (gamma : Gamma) : Decidable gamma.IsHorn := by
  unfold Gamma.IsHorn
  letI : ∀ symbol : gamma.Symbol,
      Decidable (BooleanRelation.IsHorn (gamma.relationOf symbol)) :=
    fun symbol => relationHornDecidable (gamma.relationOf symbol)
  infer_instance

def gammaDualHornDecidable (gamma : Gamma) : Decidable gamma.IsDualHorn := by
  unfold Gamma.IsDualHorn
  letI : ∀ symbol : gamma.Symbol,
      Decidable (BooleanRelation.IsDualHorn (gamma.relationOf symbol)) :=
    fun symbol => relationDualHornDecidable (gamma.relationOf symbol)
  infer_instance

def gammaBijunctiveDecidable (gamma : Gamma) : Decidable gamma.IsBijunctive := by
  unfold Gamma.IsBijunctive
  letI : ∀ symbol : gamma.Symbol,
      Decidable (BooleanRelation.IsBijunctive (gamma.relationOf symbol)) :=
    fun symbol => relationBijunctiveDecidable (gamma.relationOf symbol)
  infer_instance

def gammaAffineDecidable (gamma : Gamma) : Decidable gamma.IsAffine := by
  unfold Gamma.IsAffine
  letI : ∀ symbol : gamma.Symbol,
      Decidable (BooleanRelation.IsAffine (gamma.relationOf symbol)) :=
    fun symbol => relationAffineDecidable (gamma.relationOf symbol)
  infer_instance

/-- Executable finite classifier used by the generic premise solver. -/
def gammaSchaeferTractableDecidable (gamma : Gamma) :
    Decidable gamma.IsSchaeferTractable := by
  unfold Gamma.IsSchaeferTractable
  exact @instDecidableOr _ _ (gammaZeroValidDecidable gamma) <|
    @instDecidableOr _ _ (gammaOneValidDecidable gamma) <|
    @instDecidableOr _ _ (gammaHornDecidable gamma) <|
    @instDecidableOr _ _ (gammaDualHornDecidable gamma) <|
    @instDecidableOr _ _ (gammaBijunctiveDecidable gamma)
      (gammaAffineDecidable gamma)

/-- Reflect a positive nonemptiness decision into a kernel proof. -/
theorem gammaRelationsNonempty_of_decide_eq_true (gamma : Gamma)
    (checked : @decide
      (∀ symbol : gamma.Symbol, (gamma.relationOf symbol).Nonempty)
      (gammaRelationsNonemptyDecidable gamma) = true) :
    ∀ symbol : gamma.Symbol, (gamma.relationOf symbol).Nonempty :=
  of_decide_eq_true (inst := gammaRelationsNonemptyDecidable gamma) checked

/-- Reflect a negative six-class decision into a kernel proof. -/
theorem gammaNotSchaeferTractable_of_decide_eq_false (gamma : Gamma)
    (checked : @decide gamma.IsSchaeferTractable
      (gammaSchaeferTractableDecidable gamma) = false) :
    ¬ gamma.IsSchaeferTractable :=
  of_decide_eq_false (inst := gammaSchaeferTractableDecidable gamma) checked

end Reflection
end Reduction
end Agent
end ComplexityReduction
