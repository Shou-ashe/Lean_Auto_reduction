/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP.Gamma

/-! Schaefer's six tractable Boolean relation classes as closure properties. -/

namespace ComplexityReduction
namespace Domain
namespace BooleanCSP

open ComplexityReduction.CSP

namespace BooleanRelation

/-- The all-zero tuple is accepted. -/
def IsZeroValid (relation : BooleanRelation) : Prop :=
  relation.Holds (fun _ => false)

/-- The all-one tuple is accepted. -/
def IsOneValid (relation : BooleanRelation) : Prop :=
  relation.Holds (fun _ => true)

/-- Coordinatewise meet. -/
def meet {arity : Nat} (left right : BooleanTuple arity) : BooleanTuple arity :=
  fun index => left index && right index

/-- Coordinatewise join. -/
def join {arity : Nat} (left right : BooleanTuple arity) : BooleanTuple arity :=
  fun index => left index || right index

/-- Coordinatewise majority. -/
def majority {arity : Nat} (first second third : BooleanTuple arity) : BooleanTuple arity :=
  fun index => (first index && second index) ||
    (first index && third index) || (second index && third index)

/-- Coordinatewise affine ternary operation. -/
def affineOp {arity : Nat} (first second third : BooleanTuple arity) : BooleanTuple arity :=
  fun index => xor (xor (first index) (second index)) (third index)

/-- Horn relations are exactly the relations closed under meet. -/
def IsHorn (relation : BooleanRelation) : Prop :=
  ∀ left right, relation.Holds left → relation.Holds right →
    relation.Holds (meet left right)

/-- Dual-Horn relations are exactly the relations closed under join. -/
def IsDualHorn (relation : BooleanRelation) : Prop :=
  ∀ left right, relation.Holds left → relation.Holds right →
    relation.Holds (join left right)

/-- Bijunctive relations are exactly the relations closed under majority. -/
def IsBijunctive (relation : BooleanRelation) : Prop :=
  ∀ first second third, relation.Holds first → relation.Holds second →
    relation.Holds third → relation.Holds (majority first second third)

/-- Affine relations are exactly the relations closed under ternary XOR. -/
def IsAffine (relation : BooleanRelation) : Prop :=
  ∀ first second third, relation.Holds first → relation.Holds second →
    relation.Holds third → relation.Holds (affineOp first second third)

noncomputable instance (relation : BooleanRelation) : Decidable relation.IsZeroValid :=
  by classical exact inferInstance

noncomputable instance (relation : BooleanRelation) : Decidable relation.IsOneValid :=
  by classical exact inferInstance

noncomputable instance (relation : BooleanRelation) : Decidable relation.IsHorn :=
  by classical exact inferInstance

noncomputable instance (relation : BooleanRelation) : Decidable relation.IsDualHorn :=
  by classical exact inferInstance

noncomputable instance (relation : BooleanRelation) : Decidable relation.IsBijunctive :=
  by classical exact inferInstance

noncomputable instance (relation : BooleanRelation) : Decidable relation.IsAffine :=
  by classical exact inferInstance

end BooleanRelation

namespace Gamma

def IsZeroValid (Γ : Gamma) : Prop :=
  ∀ symbol, BooleanRelation.IsZeroValid (Γ.relationOf symbol)

def IsOneValid (Γ : Gamma) : Prop :=
  ∀ symbol, BooleanRelation.IsOneValid (Γ.relationOf symbol)

def IsHorn (Γ : Gamma) : Prop :=
  ∀ symbol, BooleanRelation.IsHorn (Γ.relationOf symbol)

def IsDualHorn (Γ : Gamma) : Prop :=
  ∀ symbol, BooleanRelation.IsDualHorn (Γ.relationOf symbol)

def IsBijunctive (Γ : Gamma) : Prop :=
  ∀ symbol, BooleanRelation.IsBijunctive (Γ.relationOf symbol)

def IsAffine (Γ : Gamma) : Prop :=
  ∀ symbol, BooleanRelation.IsAffine (Γ.relationOf symbol)

def IsSchaeferTractable (Γ : Gamma) : Prop :=
  Γ.IsZeroValid ∨ Γ.IsOneValid ∨ Γ.IsHorn ∨ Γ.IsDualHorn ∨ Γ.IsBijunctive ∨ Γ.IsAffine

noncomputable instance (Γ : Gamma) : Decidable Γ.IsZeroValid := by classical exact inferInstance
noncomputable instance (Γ : Gamma) : Decidable Γ.IsOneValid := by classical exact inferInstance
noncomputable instance (Γ : Gamma) : Decidable Γ.IsHorn := by classical exact inferInstance
noncomputable instance (Γ : Gamma) : Decidable Γ.IsDualHorn := by classical exact inferInstance
noncomputable instance (Γ : Gamma) : Decidable Γ.IsBijunctive := by classical exact inferInstance
noncomputable instance (Γ : Gamma) : Decidable Γ.IsAffine := by classical exact inferInstance
noncomputable instance (Γ : Gamma) : Decidable Γ.IsSchaeferTractable := by
  classical
  exact inferInstance

end Gamma

end BooleanCSP
end Domain
end ComplexityReduction
