/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP.Hardness.PPDefinability
import Mathlib.Tactic

/-!
Finite canonical-database pp definitions for Boolean constraint languages.

For a target relation `R`, variables are the Boolean columns on the accepting
rows of `R`.  For every relation symbol of `Γ` and every tuple of columns whose
rowwise evaluation belongs to that relation, the canonical database contains
the corresponding constraint.  Every satisfying assignment therefore induces
an operation on the row index type preserving every relation of `Γ`; conversely
every such operation is exactly a satisfying assignment.  Hence the database
defines `R` whenever every Γ-polymorphism on the accepting-row index preserves
`R` on its coordinate columns.
-/

namespace ComplexityReduction
namespace Domain
namespace BooleanCSP
namespace Hardness

open ComplexityReduction.CSP

namespace CanonicalDatabase

/-- The finite index type of accepting rows of a Boolean relation. -/
abbrev Row (relation : BooleanRelation) :=
  { tuple : BooleanTuple relation.arity // relation.Holds tuple }

/-- One Boolean column over the accepting rows. -/
abbrev Column (relation : BooleanRelation) := Row relation → Bool

/-- Coordinate projection as a canonical database column. -/
def coordinateColumn (relation : BooleanRelation) (index : Fin relation.arity) :
    Column relation :=
  fun row => row.1 index

/-- Numeric variable key of one column. -/
noncomputable def columnKey (relation : BooleanRelation) (column : Column relation) : Nat :=
  Fintype.equivFin (Column relation) column |>.val

theorem columnKey_injective (relation : BooleanRelation) :
    Function.Injective (columnKey relation) := by
  intro left right equality
  exact (Fintype.equivFin (Column relation)).injective (Fin.ext equality)

/-- Pointwise application of an operation to a tuple of canonical columns. -/
def applyColumns {relation : BooleanRelation} {k : Nat}
    (operation : Column relation → Bool) (columns : Fin k → Column relation) :
    BooleanTuple k :=
  fun index => operation (columns index)

/-- An operation on accepting rows preserves one Boolean relation. -/
def PreservesRelation (target : BooleanRelation) (operation : Column target → Bool)
    (relation : BooleanRelation) : Prop :=
  ∀ columns : Fin relation.arity → Column target,
    (∀ row : Row target, relation.Holds (fun index => columns index row)) →
      relation.Holds (applyColumns operation columns)

/-- An operation on accepting rows preserves every relation of `Γ`. -/
def PreservesLanguage (Γ : Gamma) (target : BooleanRelation)
    (operation : Column target → Bool) : Prop :=
  ∀ symbol : Γ.Symbol, PreservesRelation target operation (Γ.relationOf symbol)

/-- A tuple of columns is admitted as a canonical database constraint. -/
def Admissible (target : BooleanRelation) (relation : BooleanRelation)
    (columns : Fin relation.arity → Column target) : Prop :=
  ∀ row : Row target, relation.Holds (fun index => columns index row)

/-- One canonical database constraint. -/
noncomputable def canonicalConstraint (Γ : Gamma) (target : BooleanRelation)
    (symbol : Γ.Symbol)
    (columns : Fin (Γ.relationOf symbol).arity → Column target) : Constraint Γ where
  symbol := symbol
  vars := fun index => columnKey target (columns index)

/-- The finite canonical database formula for `target` over `Γ`. -/
noncomputable def formula (Γ : Gamma) (target : BooleanRelation) : Formula Γ := by
  classical
  exact (Finset.univ : Finset Γ.Symbol).toList.flatMap fun symbol =>
    ((Finset.univ : Finset
      (Fin (Γ.relationOf symbol).arity → Column target)).filter fun columns =>
        Admissible target (Γ.relationOf symbol) columns).toList.map fun columns =>
          canonicalConstraint Γ target symbol columns

theorem canonicalConstraint_mem_formula (Γ : Gamma) (target : BooleanRelation)
    (symbol : Γ.Symbol)
    (columns : Fin (Γ.relationOf symbol).arity → Column target)
    (admissible : Admissible target (Γ.relationOf symbol) columns) :
    canonicalConstraint Γ target symbol columns ∈ formula Γ target := by
  classical
  unfold formula
  apply List.mem_flatMap.mpr
  refine ⟨symbol, ?_, ?_⟩
  · simp
  · apply List.mem_map.mpr
    refine ⟨columns, ?_, rfl⟩
    simp [admissible]

/-- Evaluation at one accepting row is a satisfying canonical assignment. -/
noncomputable def rowAssignment (target : BooleanRelation) (row : Row target) :
    SAT.Assignment := by
  classical
  exact fun key =>
    if h : key < Fintype.card (Column target) then
      (Fintype.equivFin (Column target)).symm ⟨key, h⟩ row
    else false

theorem rowAssignment_columnKey (target : BooleanRelation) (row : Row target)
    (column : Column target) :
    rowAssignment target row (columnKey target column) = column row := by
  classical
  unfold rowAssignment columnKey
  rw [dif_pos (Fintype.equivFin (Column target) column).isLt]
  simp

theorem rowAssignment_satisfies (Γ : Gamma) (target : BooleanRelation)
    (row : Row target) :
    Formula.Satisfies (formula Γ target) (rowAssignment target row) := by
  intro constraint member
  unfold formula at member
  rcases List.mem_flatMap.mp member with ⟨symbol, symbolMember, constraintMember⟩
  rcases List.mem_map.mp constraintMember with ⟨columns, columnsMember, rfl⟩
  have admissible : Admissible target (Γ.relationOf symbol) columns := by
    simpa using columnsMember
  change (Γ.relationOf symbol).Holds
    (fun index => rowAssignment target row (columnKey target (columns index)))
  simpa [rowAssignment_columnKey] using admissible row

/-- A satisfying canonical assignment induces its operation on columns. -/
noncomputable def operationOfAssignment (target : BooleanRelation) (assignment : SAT.Assignment) :
    Column target → Bool :=
  fun column => assignment (columnKey target column)

theorem operationOfAssignment_preserves (Γ : Gamma) (target : BooleanRelation)
    (assignment : SAT.Assignment)
    (satisfies : Formula.Satisfies (formula Γ target) assignment) :
    PreservesLanguage Γ target (operationOfAssignment target assignment) := by
  intro symbol columns admissible
  have constraintMember := canonicalConstraint_mem_formula Γ target symbol columns admissible
  have constraintSatisfies := satisfies (canonicalConstraint Γ target symbol columns)
    constraintMember
  exact constraintSatisfies

/-- Coordinate columns are distinct whenever the target relation separates
the corresponding coordinates. -/
def SeparatesCoordinates (target : BooleanRelation) : Prop :=
  Function.Injective (coordinateColumn target)

/-- Every preserving operation maps the target coordinate columns to another
accepting target tuple. -/
def PreservingOperationsRespectTarget (Γ : Gamma) (target : BooleanRelation) : Prop :=
  ∀ operation : Column target → Bool,
    PreservesLanguage Γ target operation →
      target.Holds (fun index => operation (coordinateColumn target index))

/-- The canonical database gadget. -/
noncomputable def gadget (Γ : Gamma) (target : BooleanRelation)
    (separates : SeparatesCoordinates target)
    (closed : PreservingOperationsRespectTarget Γ target) : Gadget Γ target where
  formula := formula Γ target
  outputs := fun index => columnKey target (coordinateColumn target index)
  outputs_injective := columnKey_injective target |>.comp separates
  correct := by
    intro tuple
    constructor
    · intro holds
      let row : Row target := ⟨tuple, holds⟩
      refine ⟨rowAssignment target row, rowAssignment_satisfies Γ target row, ?_⟩
      intro index
      exact rowAssignment_columnKey target row (coordinateColumn target index)
    · rintro ⟨assignment, satisfies, outputs⟩
      let operation := operationOfAssignment target assignment
      have preserves : PreservesLanguage Γ target operation :=
        operationOfAssignment_preserves Γ target assignment satisfies
      have targetHolds := closed operation preserves
      have tupleEquality :
          (fun index => operation (coordinateColumn target index)) = tuple := by
        funext index
        exact outputs index
      rwa [tupleEquality] at targetHolds

/-- Canonical-database pp definability. -/
theorem ppDefines (Γ : Gamma) (target : BooleanRelation)
    (separates : SeparatesCoordinates target)
    (closed : PreservingOperationsRespectTarget Γ target) :
    PPDefines Γ target :=
  ⟨gadget Γ target separates closed⟩

assert_standard_axioms gadget, ppDefines

end CanonicalDatabase
end Hardness
end BooleanCSP
end Domain
end ComplexityReduction
