/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import ComplexityReduction.Legacy.ComplexityReduction.CSP.FiniteDomain.Basic
import ComplexityReduction.Legacy.ComplexityReduction.CSP.Formula

/-!
Bridge from the existing Boolean CSP library to the generic finite-domain CSP
surface.  This keeps the Schaefer-facing Boolean API stable while allowing new
finite-domain infrastructure to reuse Boolean examples via the domain `Bool`.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain
namespace BoolBridge

/-- Encode Booleans as the two-element finite type. -/
def boolToFin2 : Bool → Fin 2
  | false => 0
  | true => 1

/-- Decode the two-element finite type as Booleans. -/
def fin2ToBool (x : Fin 2) : Bool :=
  x = (1 : Fin 2)

@[simp]
theorem fin2ToBool_boolToFin2 (b : Bool) :
    fin2ToBool (boolToFin2 b) = b := by
  cases b <;> simp [boolToFin2, fin2ToBool]

@[simp]
theorem boolToFin2_fin2ToBool (x : Fin 2) :
    boolToFin2 (fin2ToBool x) = x := by
  fin_cases x <;> simp [boolToFin2, fin2ToBool]

/-- Decode a tuple over `Fin 2` as a Boolean tuple. -/
def tupleFin2ToBool {k : Nat} (t : Tuple (Fin 2) k) : Tuple Bool k :=
  fun i => fin2ToBool (t i)

/-- Encode a Boolean tuple as a tuple over `Fin 2`. -/
def tupleBoolToFin2 {k : Nat} (t : Tuple Bool k) : Tuple (Fin 2) k :=
  fun i => boolToFin2 (t i)

@[simp]
theorem tupleFin2ToBool_tupleBoolToFin2 {k : Nat} (t : Tuple Bool k) :
    tupleFin2ToBool (tupleBoolToFin2 t) = t := by
  funext i
  simp [tupleFin2ToBool, tupleBoolToFin2]

@[simp]
theorem tupleBoolToFin2_tupleFin2ToBool {k : Nat} (t : Tuple (Fin 2) k) :
    tupleBoolToFin2 (tupleFin2ToBool t) = t := by
  funext i
  simp [tupleFin2ToBool, tupleBoolToFin2]

/-- View an existing Boolean truth-table relation as a finite-domain relation over `Bool`. -/
def relOfBoolRel (R : BoolRel) : Rel Bool where
  arity := R.arity
  holds := fun t => R.Holds t

@[simp]
theorem relOfBoolRel_holds_iff (R : BoolRel) (t : Tuple Bool R.arity) :
    (relOfBoolRel R).Holds t ↔ R.Holds t :=
  Iff.rfl

/-- View an existing Boolean truth-table relation as a finite-domain relation over `Fin 2`. -/
def relFin2OfBoolRel (R : BoolRel) : Rel (Fin 2) where
  arity := R.arity
  holds := fun t => R.Holds (tupleFin2ToBool t)

@[simp]
theorem relFin2OfBoolRel_holds_iff (R : BoolRel) (t : Tuple (Fin 2) R.arity) :
    (relFin2OfBoolRel R).Holds t ↔ R.Holds (tupleFin2ToBool t) :=
  Iff.rfl

/-- View an existing Boolean language as a finite-domain language over `Bool`. -/
def languageOfBoolLanguage (Γ : BoolLanguage) : Language Bool where
  finiteDomain := inferInstance
  Symbol := Γ.Symbol
  finiteSymbol := Γ.finiteSymbol
  relationOf := fun s => relOfBoolRel (Γ.relationOf s)

/-- View an existing Boolean language as a finite-domain language over `Fin 2`. -/
def languageFin2OfBoolLanguage (Γ : BoolLanguage) : Language (Fin 2) where
  finiteDomain := inferInstance
  Symbol := Γ.Symbol
  finiteSymbol := Γ.finiteSymbol
  relationOf := fun s => relFin2OfBoolRel (Γ.relationOf s)

/-- Decode an assignment over `Fin 2` as a Boolean assignment. -/
def assignmentFin2ToBool (a : Assignment (Fin 2)) : SAT.Assignment :=
  fun x => fin2ToBool (a x)

/-- Encode a Boolean assignment as an assignment over `Fin 2`. -/
def assignmentBoolToFin2 (a : SAT.Assignment) : Assignment (Fin 2) :=
  fun x => boolToFin2 (a x)

@[simp]
theorem assignmentFin2ToBool_assignmentBoolToFin2 (a : SAT.Assignment) :
    assignmentFin2ToBool (assignmentBoolToFin2 a) = a := by
  funext x
  simp [assignmentFin2ToBool, assignmentBoolToFin2]

@[simp]
theorem assignmentBoolToFin2_assignmentFin2ToBool (a : Assignment (Fin 2)) :
    assignmentBoolToFin2 (assignmentFin2ToBool a) = a := by
  funext x
  simp [assignmentFin2ToBool, assignmentBoolToFin2]

/-- Transport one Boolean CSP constraint into the finite-domain `Bool` surface. -/
def constraintOfBoolConstraint {Γ : BoolLanguage} (c : CSP.Constraint Γ) :
    Constraint (languageOfBoolLanguage Γ) where
  symbol := c.symbol
  vars := c.vars

/-- Transport one Boolean CSP constraint into the finite-domain `Fin 2` surface. -/
def constraintFin2OfBoolConstraint {Γ : BoolLanguage} (c : CSP.Constraint Γ) :
    Constraint (languageFin2OfBoolLanguage Γ) where
  symbol := c.symbol
  vars := c.vars

/-- Transport a Boolean CSP formula into the finite-domain `Bool` surface. -/
def formulaOfBoolFormula {Γ : BoolLanguage} (φ : CSP.Formula Γ) :
    Formula (languageOfBoolLanguage Γ) :=
  φ.map constraintOfBoolConstraint

/-- Transport a Boolean CSP formula into the finite-domain `Fin 2` surface. -/
def formulaFin2OfBoolFormula {Γ : BoolLanguage} (φ : CSP.Formula Γ) :
    Formula (languageFin2OfBoolLanguage Γ) :=
  φ.map constraintFin2OfBoolConstraint

@[simp]
theorem constraintOfBoolConstraint_satisfies_iff {Γ : BoolLanguage}
    (c : CSP.Constraint Γ) (a : Assignment Bool) :
    Constraint.Satisfies (constraintOfBoolConstraint c) a ↔ CSP.Constraint.Satisfies c a :=
  Iff.rfl

@[simp]
theorem constraintFin2OfBoolConstraint_satisfies_iff {Γ : BoolLanguage}
    (c : CSP.Constraint Γ) (a : Assignment (Fin 2)) :
    Constraint.Satisfies (constraintFin2OfBoolConstraint c) a ↔
      CSP.Constraint.Satisfies c (assignmentFin2ToBool a) :=
  Iff.rfl

@[simp]
theorem formulaOfBoolFormula_nil {Γ : BoolLanguage} :
    formulaOfBoolFormula ([] : CSP.Formula Γ) = [] :=
  rfl

@[simp]
theorem formulaOfBoolFormula_cons {Γ : BoolLanguage}
    (c : CSP.Constraint Γ) (φ : CSP.Formula Γ) :
    formulaOfBoolFormula (c :: φ) =
      constraintOfBoolConstraint c :: formulaOfBoolFormula φ :=
  rfl

@[simp]
theorem formulaFin2OfBoolFormula_nil {Γ : BoolLanguage} :
    formulaFin2OfBoolFormula ([] : CSP.Formula Γ) = [] :=
  rfl

@[simp]
theorem formulaFin2OfBoolFormula_cons {Γ : BoolLanguage}
    (c : CSP.Constraint Γ) (φ : CSP.Formula Γ) :
    formulaFin2OfBoolFormula (c :: φ) =
      constraintFin2OfBoolConstraint c :: formulaFin2OfBoolFormula φ :=
  rfl

@[simp]
theorem formulaOfBoolFormula_satisfies_iff {Γ : BoolLanguage}
    (φ : CSP.Formula Γ) (a : Assignment Bool) :
    Formula.Satisfies (formulaOfBoolFormula φ) a ↔ CSP.Formula.Satisfies φ a := by
  induction φ with
  | nil =>
      simp
  | cons c φ ih =>
      simp [ih]

@[simp]
theorem formulaFin2OfBoolFormula_satisfies_iff {Γ : BoolLanguage}
    (φ : CSP.Formula Γ) (a : Assignment (Fin 2)) :
    Formula.Satisfies (formulaFin2OfBoolFormula φ) a ↔
      CSP.Formula.Satisfies φ (assignmentFin2ToBool a) := by
  induction φ with
  | nil =>
      simp
  | cons c φ ih =>
      simp [ih]

@[simp]
theorem formulaOfBoolFormula_satisfiable_iff {Γ : BoolLanguage}
    (φ : CSP.Formula Γ) :
    Formula.Satisfiable (formulaOfBoolFormula φ) ↔ CSP.Formula.Satisfiable φ := by
  constructor
  · rintro ⟨a, h⟩
    exact ⟨a, (formulaOfBoolFormula_satisfies_iff φ a).1 h⟩
  · rintro ⟨a, h⟩
    exact ⟨a, (formulaOfBoolFormula_satisfies_iff φ a).2 h⟩

@[simp]
theorem formulaFin2OfBoolFormula_satisfiable_iff {Γ : BoolLanguage}
    (φ : CSP.Formula Γ) :
    Formula.Satisfiable (formulaFin2OfBoolFormula φ) ↔ CSP.Formula.Satisfiable φ := by
  constructor
  · rintro ⟨a, h⟩
    exact ⟨assignmentFin2ToBool a, (formulaFin2OfBoolFormula_satisfies_iff φ a).1 h⟩
  · rintro ⟨a, h⟩
    refine ⟨assignmentBoolToFin2 a, ?_⟩
    exact (formulaFin2OfBoolFormula_satisfies_iff φ (assignmentBoolToFin2 a)).2 (by
      simpa using h)

end BoolBridge
end FiniteDomain
end CSP
end ComplexityReduction
