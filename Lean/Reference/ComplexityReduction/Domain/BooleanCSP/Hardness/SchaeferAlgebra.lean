/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP.Hardness.CanonicalDatabase
import ComplexityReduction.Domain.BooleanCSP.Classes
import Mathlib.Tactic

/-!
Finite Boolean operation algebra used by the Schaefer hardness proof.
-/

namespace ComplexityReduction
namespace Domain
namespace BooleanCSP
namespace Hardness
namespace SchaeferAlgebra

open ComplexityReduction.CSP

/-- An operation of arbitrary finite arity preserves every relation of Γ. -/
def Preserves {ι : Type} (Γ : Gamma) (operation : (ι → Bool) → Bool) : Prop :=
  ∀ symbol : Γ.Symbol, ∀ tuples : ι → BooleanTuple (Γ.relationOf symbol).arity,
    (∀ index, (Γ.relationOf symbol).Holds (tuples index)) →
      (Γ.relationOf symbol).Holds
        (fun coordinate => operation (fun index => tuples index coordinate))

theorem preserves_projection {ι : Type} (Γ : Gamma) (index : ι) :
    Preserves Γ (fun tuple => tuple index) := by
  intro symbol tuples holds
  simpa using holds index

theorem preserves_comp {ι κ : Type} {Γ : Gamma}
    {outer : (κ → Bool) → Bool} {inner : κ → (ι → Bool) → Bool}
    (outerPreserves : Preserves Γ outer)
    (innerPreserves : ∀ index, Preserves Γ (inner index)) :
    Preserves Γ (fun tuple => outer (fun index => inner index tuple)) := by
  intro symbol tuples holds
  apply outerPreserves symbol (fun index coordinate => inner index
    (fun input => tuples input coordinate))
  intro index
  exact innerPreserves index symbol tuples holds

theorem canonical_preserves_iff {ι : Type} [Fintype ι]
    (Γ : Gamma) (target : BooleanRelation) (operation : (ι → Bool) → Bool)
    (equiv : ι ≃ CanonicalDatabase.Row target) :
    Preserves Γ operation ↔
      CanonicalDatabase.PreservesLanguage Γ target
        (fun column => operation (fun index => column (equiv index))) := by
  constructor
  · intro preserves symbol columns admissible
    apply preserves symbol (fun index coordinate => columns coordinate (equiv index))
    intro index
    exact admissible (equiv index)
  · intro preserves symbol tuples holds
    let columns : Fin (Γ.relationOf symbol).arity → CanonicalDatabase.Column target :=
      fun coordinate row => tuples (equiv.symm row) coordinate
    have admissible : CanonicalDatabase.Admissible target
        (Γ.relationOf symbol) columns := by
      intro row
      exact holds (equiv.symm row)
    have output := preserves symbol columns admissible
    have outputTuple : CanonicalDatabase.applyColumns
        (fun column => operation (fun index => column (equiv index))) columns =
        (fun coordinate => operation (fun index => tuples index coordinate)) := by
      funext coordinate
      simp [CanonicalDatabase.applyColumns, columns]
    rwa [outputTuple] at output

/-! ### PP definitions are preserved by polymorphisms -/

theorem preserves_gadget {ι : Type} [Fintype ι]
    {Γ : Gamma} {relation : BooleanRelation}
    (operation : (ι → Bool) → Bool) (preserves : Preserves Γ operation)
    (gadget : Gadget Γ relation) :
    ∀ tuples : ι → BooleanTuple relation.arity,
      (∀ index, relation.Holds (tuples index)) →
      relation.Holds
          (fun coordinate => operation (fun index => tuples index coordinate)) := by
  classical
  intro tuples holds
  let witness : ι → SAT.Assignment := fun index =>
    Classical.choose ((gadget.correct (tuples index)).1 (holds index))
  have witnessSpec : ∀ index,
      Formula.Satisfies gadget.formula (witness index) ∧
        ∀ coordinate, witness index (gadget.outputs coordinate) =
          tuples index coordinate := by
    intro index
    exact Classical.choose_spec ((gadget.correct (tuples index)).1 (holds index))
  let combined : SAT.Assignment := fun key =>
    operation (fun index => witness index key)
  apply (gadget.correct
    (fun coordinate => operation (fun index => tuples index coordinate))).2
  refine ⟨combined, ?_, ?_⟩
  · intro constraint member
    apply preserves constraint.symbol
      (fun index coordinate => witness index (constraint.vars coordinate))
    intro index
    exact witnessSpec index |>.1 constraint member
  · intro coordinate
    change operation (fun index => witness index (gadget.outputs coordinate)) =
      operation (fun index => tuples index coordinate)
    congr 1
    funext index
    exact witnessSpec index |>.2 coordinate

theorem preserves_ppDefined {ι : Type} [Fintype ι]
    {Γ : Gamma} {relation : BooleanRelation}
    (operation : (ι → Bool) → Bool) (preserves : Preserves Γ operation)
    (defined : PPDefines Γ relation) :
    ∀ tuples : ι → BooleanTuple relation.arity,
      (∀ index, relation.Holds (tuples index)) →
        relation.Holds
          (fun coordinate => operation (fun index => tuples index coordinate)) := by
  rcases defined with ⟨gadget⟩
  exact preserves_gadget operation preserves gadget

/-! ### Diagonal operations -/

/-- Every relation of Γ is closed under pointwise Boolean complement. -/
def PreservesComplement (Γ : Gamma) : Prop :=
  ∀ symbol : Γ.Symbol, ∀ tuple : BooleanTuple (Γ.relationOf symbol).arity,
    (Γ.relationOf symbol).Holds tuple →
      (Γ.relationOf symbol).Holds (fun coordinate => !(tuple coordinate))

theorem isZeroValid_of_diagonal_false {ι : Type} {Γ : Gamma}
    (operation : (ι → Bool) → Bool) (preserves : Preserves Γ operation)
    (nonempty : ∀ symbol : Γ.Symbol, (Γ.relationOf symbol).Nonempty)
    (zero : operation (fun _ => false) = false)
    (one : operation (fun _ => true) = false) : Γ.IsZeroValid := by
  intro symbol
  rcases nonempty symbol with ⟨tuple, tupleHolds⟩
  have result := preserves symbol (fun _ : ι => tuple) (fun _ => tupleHolds)
  have outputEquality :
      (fun coordinate => operation (fun _ : ι => tuple coordinate)) =
        (fun _ => false) := by
    funext coordinate
    cases h : tuple coordinate
    · simpa [h] using zero
    · simpa [h] using one
  rwa [outputEquality] at result

theorem isOneValid_of_diagonal_true {ι : Type} {Γ : Gamma}
    (operation : (ι → Bool) → Bool) (preserves : Preserves Γ operation)
    (nonempty : ∀ symbol : Γ.Symbol, (Γ.relationOf symbol).Nonempty)
    (zero : operation (fun _ => false) = true)
    (one : operation (fun _ => true) = true) : Γ.IsOneValid := by
  intro symbol
  rcases nonempty symbol with ⟨tuple, tupleHolds⟩
  have result := preserves symbol (fun _ : ι => tuple) (fun _ => tupleHolds)
  have outputEquality :
      (fun coordinate => operation (fun _ : ι => tuple coordinate)) =
        (fun _ => true) := by
    funext coordinate
    cases h : tuple coordinate
    · simpa [h] using zero
    · simpa [h] using one
  rwa [outputEquality] at result

theorem preservesComplement_of_diagonal_not {ι : Type} {Γ : Gamma}
    (operation : (ι → Bool) → Bool) (preserves : Preserves Γ operation)
    (zero : operation (fun _ => false) = true)
    (one : operation (fun _ => true) = false) : PreservesComplement Γ := by
  intro symbol tuple tupleHolds
  have result := preserves symbol (fun _ : ι => tuple) (fun _ => tupleHolds)
  have outputEquality :
      (fun coordinate => operation (fun _ : ι => tuple coordinate)) =
        (fun coordinate => !(tuple coordinate)) := by
    funext coordinate
    cases h : tuple coordinate
    · simpa [h] using zero
    · simpa [h] using one
  rwa [outputEquality] at result

theorem complement_preserves {Γ : Gamma} (complement : PreservesComplement Γ) :
    Preserves Γ (fun tuple : Fin 1 → Bool => !(tuple ⟨0, by decide⟩)) := by
  intro symbol tuples holds
  exact complement symbol (tuples 0) (holds 0)

/-! ### Closed classification of idempotent ternary Boolean operations -/

abbrev TernaryOp := Bool → Bool → Bool → Bool

def firstProjection : TernaryOp := fun first _ _ => first
def secondProjection : TernaryOp := fun _ second _ => second
def thirdProjection : TernaryOp := fun _ _ third => third
def meetOp : TernaryOp := fun first second _ => first && second
def joinOp : TernaryOp := fun first second _ => first || second
def majorityOp : TernaryOp := fun first second third =>
  (first && second) || (first && third) || (second && third)
def affineOp : TernaryOp := fun first second third => xor (xor first second) third

inductive BasicTerm where
  | first
  | second
  | third
  | self
  deriving DecidableEq, Fintype

def BasicTerm.eval (operation : TernaryOp) : BasicTerm → TernaryOp
  | .first => firstProjection
  | .second => secondProjection
  | .third => thirdProjection
  | .self => operation

def GeneratesInOneComposition (operation target : TernaryOp) : Prop :=
  ∃ first second third : BasicTerm,
    ∀ x y z,
      operation (first.eval operation x y z) (second.eval operation x y z)
        (third.eval operation x y z) = target x y z

def Idempotent (operation : TernaryOp) : Prop :=
  operation false false false = false ∧ operation true true true = true

def IsProjection (operation : TernaryOp) : Prop :=
  operation = firstProjection ∨ operation = secondProjection ∨ operation = thirdProjection

/-- Explicit, computably enumerable truth table for a ternary Boolean
operation.  Using eight Boolean fields avoids the classical `Fintype` instance
for function spaces in the kernel-evaluated classification below. -/
structure TernaryTable where
  at000 : Bool
  at001 : Bool
  at010 : Bool
  at011 : Bool
  at100 : Bool
  at101 : Bool
  at110 : Bool
  at111 : Bool
  deriving DecidableEq

def TernaryTable.toFunction (table : TernaryTable) : Fin 8 → Bool
  | ⟨0, _⟩ => table.at000
  | ⟨1, _⟩ => table.at001
  | ⟨2, _⟩ => table.at010
  | ⟨3, _⟩ => table.at011
  | ⟨4, _⟩ => table.at100
  | ⟨5, _⟩ => table.at101
  | ⟨6, _⟩ => table.at110
  | ⟨7, _⟩ => table.at111

def TernaryTable.ofFunction (function : Fin 8 → Bool) : TernaryTable where
  at000 := function 0
  at001 := function 1
  at010 := function 2
  at011 := function 3
  at100 := function 4
  at101 := function 5
  at110 := function 6
  at111 := function 7

def TernaryTable.equivFunction : TernaryTable ≃ (Fin 8 → Bool) where
  toFun := TernaryTable.toFunction
  invFun := TernaryTable.ofFunction
  left_inv table := by cases table; rfl
  right_inv function := by
    funext index
    fin_cases index <;> rfl

instance : Fintype TernaryTable :=
  Fintype.ofEquiv (Fin 8 → Bool) TernaryTable.equivFunction.symm

def TernaryTable.eval (table : TernaryTable) : TernaryOp
  | false, false, false => table.at000
  | false, false, true => table.at001
  | false, true, false => table.at010
  | false, true, true => table.at011
  | true, false, false => table.at100
  | true, false, true => table.at101
  | true, true, false => table.at110
  | true, true, true => table.at111

def TernaryTable.ofOperation (operation : TernaryOp) : TernaryTable where
  at000 := operation false false false
  at001 := operation false false true
  at010 := operation false true false
  at011 := operation false true true
  at100 := operation true false false
  at101 := operation true false true
  at110 := operation true true false
  at111 := operation true true true

@[simp]
theorem TernaryTable.eval_ofOperation (operation : TernaryOp) :
    (TernaryTable.ofOperation operation).eval = operation := by
  funext first second third
  cases first <;> cases second <;> cases third <;> rfl

@[simp]
theorem TernaryTable.ofOperation_eval (table : TernaryTable) :
    TernaryTable.ofOperation table.eval = table := by
  cases table
  rfl

def BasicTerm.evalTable (operation : TernaryTable) (term : BasicTerm) : TernaryTable :=
  TernaryTable.ofOperation (term.eval operation.eval)

def composeTable (operation : TernaryTable)
    (first second third : BasicTerm) : TernaryTable :=
  TernaryTable.ofOperation fun x y z =>
    operation.eval (first.evalTable operation |>.eval x y z)
      (second.evalTable operation |>.eval x y z)
      (third.evalTable operation |>.eval x y z)

def TableGenerates (operation target : TernaryTable) : Prop :=
  ∃ first second third : BasicTerm,
    composeTable operation first second third = target

instance (operation target : TernaryTable) : Decidable (TableGenerates operation target) :=
  Fintype.decidableExistsFintype

def TableIdempotent (operation : TernaryTable) : Prop :=
  operation.at000 = false ∧ operation.at111 = true

instance (operation : TernaryTable) : Decidable (TableIdempotent operation) :=
  decidable_of_iff
    ((operation.at000 == false && operation.at111 == true) = true) (by
      simp [TableIdempotent])

def TableIsProjection (operation : TernaryTable) : Prop :=
  operation = TernaryTable.ofOperation firstProjection ∨
    operation = TernaryTable.ofOperation secondProjection ∨
    operation = TernaryTable.ofOperation thirdProjection

instance (operation : TernaryTable) : Decidable (TableIsProjection operation) :=
  decidable_of_iff
    ((operation == TernaryTable.ofOperation firstProjection ||
      operation == TernaryTable.ofOperation secondProjection ||
      operation == TernaryTable.ofOperation thirdProjection) = true) (by
        simp only [Bool.or_eq_true, beq_iff_eq]
        constructor
        · rintro ((first | second) | third)
          · exact Or.inl first
          · exact Or.inr (Or.inl second)
          · exact Or.inr (Or.inr third)
        · rintro (first | second | third)
          · exact Or.inl (Or.inl first)
          · exact Or.inl (Or.inr second)
          · exact Or.inr third)

theorem tableIsProjection_iff (operation : TernaryOp) :
    TableIsProjection (TernaryTable.ofOperation operation) ↔ IsProjection operation := by
  constructor
  · rintro (equality | equality | equality)
    · left
      have functions := congrArg TernaryTable.eval equality
      simpa using functions
    · right; left
      have functions := congrArg TernaryTable.eval equality
      simpa using functions
    · right; right
      have functions := congrArg TernaryTable.eval equality
      simpa using functions
  · rintro (rfl | rfl | rfl) <;> simp [TableIsProjection]

theorem tableGenerates_to_operation {operation target : TernaryOp}
    (generated : TableGenerates (TernaryTable.ofOperation operation)
      (TernaryTable.ofOperation target)) :
    GeneratesInOneComposition operation target := by
  rcases generated with ⟨first, second, third, equality⟩
  refine ⟨first, second, third, ?_⟩
  intro x y z
  have functions := congrArg TernaryTable.eval equality
  have values := congrFun (congrFun (congrFun functions x) y) z
  simpa [composeTable, BasicTerm.evalTable] using values

/-- Fully computable classification of the 256 explicit truth tables. -/
theorem table_idempotent_nonprojection_classification :
    ∀ operation : TernaryTable,
      TableIdempotent operation → ¬ TableIsProjection operation →
        TableGenerates operation (TernaryTable.ofOperation meetOp) ∨
        TableGenerates operation (TernaryTable.ofOperation joinOp) ∨
        TableGenerates operation (TernaryTable.ofOperation majorityOp) ∨
        TableGenerates operation (TernaryTable.ofOperation affineOp) := by
  set_option maxRecDepth 100000 in
    decide

/-- Kernel-evaluated truth-table classification of all 64 idempotent ternary
Boolean operations. -/
theorem idempotent_nonprojection_classification :
    ∀ operation : TernaryOp,
      Idempotent operation → ¬ IsProjection operation →
        GeneratesInOneComposition operation meetOp ∨
        GeneratesInOneComposition operation joinOp ∨
        GeneratesInOneComposition operation majorityOp ∨
        GeneratesInOneComposition operation affineOp := by
  intro operation idempotent notProjection
  have tableIdempotent : TableIdempotent (TernaryTable.ofOperation operation) := by
    exact idempotent
  have tableNotProjection :
      ¬ TableIsProjection (TernaryTable.ofOperation operation) := by
    rwa [tableIsProjection_iff]
  rcases table_idempotent_nonprojection_classification
      (TernaryTable.ofOperation operation) tableIdempotent tableNotProjection with
    generated | generated | generated | generated
  · exact Or.inl (tableGenerates_to_operation generated)
  · exact Or.inr (Or.inl (tableGenerates_to_operation generated))
  · exact Or.inr (Or.inr (Or.inl (tableGenerates_to_operation generated)))
  · exact Or.inr (Or.inr (Or.inr (tableGenerates_to_operation generated)))

def preservesTernary (Γ : Gamma) (operation : TernaryOp) : Prop :=
  Preserves Γ (fun tuple : Fin 3 → Bool =>
    operation (tuple ⟨0, by decide⟩) (tuple ⟨1, by decide⟩)
      (tuple ⟨2, by decide⟩))

theorem preservesTernary_projection (Γ : Gamma) :
    preservesTernary Γ firstProjection ∧ preservesTernary Γ secondProjection ∧
      preservesTernary Γ thirdProjection := by
  constructor
  · simpa [preservesTernary, firstProjection] using
      preserves_projection (ι := Fin 3) Γ ⟨0, by decide⟩
  constructor
  · simpa [preservesTernary, secondProjection] using
      preserves_projection (ι := Fin 3) Γ ⟨1, by decide⟩
  · simpa [preservesTernary, thirdProjection] using
      preserves_projection (ι := Fin 3) Γ ⟨2, by decide⟩

theorem preservesTernary_basic {Γ : Gamma} {operation : TernaryOp}
    (preserves : preservesTernary Γ operation) (term : BasicTerm) :
    preservesTernary Γ (term.eval operation) := by
  cases term
  · exact preservesTernary_projection Γ |>.1
  · exact preservesTernary_projection Γ |>.2.1
  · exact preservesTernary_projection Γ |>.2.2
  · exact preserves

theorem preservesTernary_generated {Γ : Gamma} {operation target : TernaryOp}
    (preserves : preservesTernary Γ operation)
    (generated : GeneratesInOneComposition operation target) :
    preservesTernary Γ target := by
  rcases generated with ⟨first, second, third, equality⟩
  intro symbol tuples holds
  let firstTuple : BooleanTuple (Γ.relationOf symbol).arity := fun coordinate =>
    first.eval operation (tuples 0 coordinate) (tuples 1 coordinate) (tuples 2 coordinate)
  let secondTuple : BooleanTuple (Γ.relationOf symbol).arity := fun coordinate =>
    second.eval operation (tuples 0 coordinate) (tuples 1 coordinate) (tuples 2 coordinate)
  let thirdTuple : BooleanTuple (Γ.relationOf symbol).arity := fun coordinate =>
    third.eval operation (tuples 0 coordinate) (tuples 1 coordinate) (tuples 2 coordinate)
  have firstHolds : (Γ.relationOf symbol).Holds firstTuple :=
    preservesTernary_basic preserves first symbol tuples holds
  have secondHolds : (Γ.relationOf symbol).Holds secondTuple :=
    preservesTernary_basic preserves second symbol tuples holds
  have thirdHolds : (Γ.relationOf symbol).Holds thirdTuple :=
    preservesTernary_basic preserves third symbol tuples holds
  have result := preserves symbol (fun
    | ⟨0, _⟩ => firstTuple
    | ⟨1, _⟩ => secondTuple
    | ⟨2, _⟩ => thirdTuple) (by
      intro index
      fin_cases index
      · exact firstHolds
      · exact secondHolds
      · exact thirdHolds)
  have pointwise : (fun coordinate =>
      operation
        (first.eval operation (tuples 0 coordinate) (tuples 1 coordinate)
          (tuples 2 coordinate))
        (second.eval operation (tuples 0 coordinate) (tuples 1 coordinate)
          (tuples 2 coordinate))
        (third.eval operation (tuples 0 coordinate) (tuples 1 coordinate)
          (tuples 2 coordinate))) =
      (fun coordinate => target (tuples 0 coordinate) (tuples 1 coordinate)
        (tuples 2 coordinate)) := by
    funext coordinate
    exact equality _ _ _
  simpa [firstTuple, secondTuple, thirdTuple] using (pointwise ▸ result)

theorem isHorn_of_preserves_meet {Γ : Gamma} (preserves : preservesTernary Γ meetOp) :
    Γ.IsHorn := by
  intro symbol left right holdsLeft holdsRight
  let tuples : Fin 3 → BooleanTuple (Γ.relationOf symbol).arity := fun
    | ⟨0, _⟩ => left
    | ⟨1, _⟩ => right
    | ⟨2, _⟩ => right
  have result := preserves symbol tuples (by
    intro index
    fin_cases index
    · exact holdsLeft
    · exact holdsRight
    · exact holdsRight)
  simpa [tuples, meetOp, BooleanRelation.meet] using result

theorem isDualHorn_of_preserves_join {Γ : Gamma} (preserves : preservesTernary Γ joinOp) :
    Γ.IsDualHorn := by
  intro symbol left right holdsLeft holdsRight
  let tuples : Fin 3 → BooleanTuple (Γ.relationOf symbol).arity := fun
    | ⟨0, _⟩ => left
    | ⟨1, _⟩ => right
    | ⟨2, _⟩ => right
  have result := preserves symbol tuples (by
    intro index
    fin_cases index
    · exact holdsLeft
    · exact holdsRight
    · exact holdsRight)
  simpa [tuples, joinOp, BooleanRelation.join] using result

theorem isBijunctive_of_preserves_majority {Γ : Gamma}
    (preserves : preservesTernary Γ majorityOp) : Γ.IsBijunctive := by
  intro symbol first second third holdsFirst holdsSecond holdsThird
  have result := preserves symbol (fun
    | ⟨0, _⟩ => first
    | ⟨1, _⟩ => second
    | ⟨2, _⟩ => third) (by
      intro index
      fin_cases index <;> assumption)
  simpa [majorityOp, BooleanRelation.majority] using result

theorem isAffine_of_preserves_affine {Γ : Gamma}
    (preserves : preservesTernary Γ affineOp) : Γ.IsAffine := by
  intro symbol first second third holdsFirst holdsSecond holdsThird
  have result := preserves symbol (fun
    | ⟨0, _⟩ => first
    | ⟨1, _⟩ => second
    | ⟨2, _⟩ => third) (by
      intro index
      fin_cases index <;> assumption)
  have tupleEquality : (fun coordinate =>
      affineOp (first coordinate) (second coordinate) (third coordinate)) =
      BooleanRelation.affineOp first second third := by
    rfl
  rwa [tupleEquality] at result

/-- A non-tractable language admits no nonprojection idempotent ternary
polymorphism. -/
theorem projection_of_idempotent_of_notSchaeferTractable {Γ : Gamma}
    {operation : TernaryOp} (preserves : preservesTernary Γ operation)
    (idempotent : Idempotent operation)
    (notTractable : ¬ Γ.IsSchaeferTractable) : IsProjection operation := by
  by_contra notProjection
  rcases idempotent_nonprojection_classification operation idempotent notProjection with
    generated | generated | generated | generated
  · exact notTractable (Or.inr (Or.inr (Or.inl
      (isHorn_of_preserves_meet (preservesTernary_generated preserves generated)))))
  · exact notTractable (Or.inr (Or.inr (Or.inr (Or.inl
      (isDualHorn_of_preserves_join (preservesTernary_generated preserves generated))))))
  · exact notTractable (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (isBijunctive_of_preserves_majority
        (preservesTernary_generated preserves generated)))))))
  · exact notTractable (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (isAffine_of_preserves_affine (preservesTernary_generated preserves generated)))))))

assert_standard_axioms
  preserves_gadget,
  table_idempotent_nonprojection_classification,
  idempotent_nonprojection_classification,
  projection_of_idempotent_of_notSchaeferTractable

end SchaeferAlgebra
end Hardness
end BooleanCSP
end Domain
end ComplexityReduction
