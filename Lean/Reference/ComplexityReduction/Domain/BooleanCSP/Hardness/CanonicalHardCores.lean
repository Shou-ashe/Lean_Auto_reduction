/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP.Hardness.SchaeferAlgebra
import ComplexityReduction.Domain.BooleanCSP.Hardness.ExpressivePower

/-!
Closed canonical-database construction of Schaefer hard-core interpretations.
-/

namespace ComplexityReduction
namespace Domain
namespace BooleanCSP
namespace Hardness
namespace CanonicalHardCores

set_option maxRecDepth 10000

open ComplexityReduction.CSP
open CanonicalDatabase
open SchaeferAlgebra

private noncomputable abbrev exactlyOneRel : BooleanRelation :=
  ⟨3, StandardRelations.exactlyOne3Rel.accepts⟩

private noncomputable abbrev naeRel : BooleanRelation :=
  ⟨3, StandardRelations.notAllEqual3Rel.accepts⟩

@[simp] private theorem exactlyOneRel_arity : exactlyOneRel.arity = 3 := rfl
@[simp] private theorem naeRel_arity : naeRel.arity = 3 := rfl

@[simp] private theorem exactlyOneRel_holds (tuple : BooleanTuple 3) :
    exactlyOneRel.Holds tuple ↔ StandardRelations.exactlyOne3Rel.Holds tuple :=
  Iff.rfl

@[simp] private theorem naeRel_holds (tuple : BooleanTuple 3) :
    naeRel.Holds tuple ↔ StandardRelations.notAllEqual3Rel.Holds tuple :=
  Iff.rfl

/-! ### Coordinate separation -/

theorem exactlyOne_separates :
    SeparatesCoordinates exactlyOneRel := by
  intro first second equality
  by_contra different
  have witness : exactlyOneRel.Holds
      (fun index => decide (index = first)) := by
    change StandardRelations.exactlyOne3Rel.Holds _
    rw [show (fun index : Fin 3 => decide (index = first)) =
        StandardRelations.tripleTuple (decide ((0 : Fin 3) = first))
          (decide ((1 : Fin 3) = first)) (decide ((2 : Fin 3) = first)) by
      funext index
      fin_cases index <;> rfl]
    rw [exactlyOne3Rel_holds_triple_iff]
    fin_cases first <;> decide
  let row : Row exactlyOneRel := ⟨_, witness⟩
  have values := congrFun equality row
  simp [coordinateColumn, row] at values
  exact different values.symm

theorem nae_separates :
    SeparatesCoordinates naeRel := by
  intro first second equality
  by_contra different
  have tupleHolds : naeRel.Holds
      (fun index => decide (index = first)) := by
    change StandardRelations.notAllEqual3Rel.Holds _
    rw [show (fun index : Fin 3 => decide (index = first)) =
        StandardRelations.tripleTuple (decide ((0 : Fin 3) = first))
          (decide ((1 : Fin 3) = first)) (decide ((2 : Fin 3) = first)) by
      funext index
      fin_cases index <;> rfl]
    rw [StandardRelations.notAllEqual3Rel_holds_triple_iff]
    fin_cases first <;> decide
  let row : Row naeRel := ⟨_, tupleHolds⟩
  have values := congrFun equality row
  simp [coordinateColumn, row] at values
  exact different values.symm

/-! ### Exactly-one columns and their ternary minor -/

noncomputable def exactlyOneSelector (first second third : Bool) :
    Column exactlyOneRel :=
  fun row => if row.1 ⟨0, by simpa using exactlyOneRel_arity⟩ then first else
    if row.1 ⟨1, by simpa using exactlyOneRel_arity⟩ then second else third

theorem exactlyOneSelector_false :
    exactlyOneSelector false false false = fun _ => false := by
  funext row
  simp [exactlyOneSelector]

theorem exactlyOneSelector_true :
    exactlyOneSelector true true true = fun _ => true := by
  funext row
  cases h0 : row.1 ⟨0, by simpa using exactlyOneRel_arity⟩ <;>
    simp [exactlyOneSelector, h0]

theorem exactlyOneSelector_first :
    exactlyOneSelector true false false =
      coordinateColumn exactlyOneRel ⟨0, by simpa using exactlyOneRel_arity⟩ := by
  funext row
  simp [exactlyOneSelector, coordinateColumn]

theorem exactlyOneSelector_second :
    exactlyOneSelector false true false =
      coordinateColumn exactlyOneRel ⟨1, by simpa using exactlyOneRel_arity⟩ := by
  funext row
  let i0 : Fin exactlyOneRel.arity := ⟨0, by simpa using exactlyOneRel_arity⟩
  let i1 : Fin exactlyOneRel.arity := ⟨1, by simpa using exactlyOneRel_arity⟩
  cases h0 : row.1 i0
  · change (if row.1 i0 then false else if row.1 i1 then true else false) = row.1 i1
    simp [h0]
  · change (if row.1 i0 then false else if row.1 i1 then true else false) = row.1 i1
    have rowHolds := row.2
    change StandardRelations.exactlyOne3Rel.Holds row.1 at rowHolds
    have tupleEquality : row.1 = StandardRelations.tripleTuple (row.1 i0)
        (row.1 i1) (row.1 ⟨2, by simpa using exactlyOneRel_arity⟩) := by
      funext index
      fin_cases index <;> rfl
    rw [tupleEquality, exactlyOne3Rel_holds_triple_iff] at rowHolds
    cases h1 : row.1 i1
    · simp [h0, h1]
    · exfalso
      simp [h0, h1] at rowHolds
      omega

theorem exactlyOneSelector_third :
    exactlyOneSelector false false true =
      coordinateColumn exactlyOneRel ⟨2, by simpa using exactlyOneRel_arity⟩ := by
  funext row
  rcases row with ⟨tuple, holds⟩
  let i0 : Fin exactlyOneRel.arity := ⟨0, by simpa using exactlyOneRel_arity⟩
  let i1 : Fin exactlyOneRel.arity := ⟨1, by simpa using exactlyOneRel_arity⟩
  let i2 : Fin exactlyOneRel.arity := ⟨2, by simpa using exactlyOneRel_arity⟩
  have tupleEquality : tuple = StandardRelations.tripleTuple (tuple i0) (tuple i1) (tuple i2) := by
    funext index
    fin_cases index <;> rfl
  rw [tupleEquality, exactlyOneRel_holds, exactlyOne3Rel_holds_triple_iff] at holds
  cases h0 : tuple i0 <;> cases h1 : tuple i1 <;> cases h2 : tuple i2
  all_goals try simp [h0, h1, h2] at holds
  all_goals simp [exactlyOneSelector, coordinateColumn, h0, h1, h2,
    show (0 : Fin 3) = i0 by rfl, show (1 : Fin 3) = i1 by rfl,
    show (2 : Fin 3) = i2 by rfl]

noncomputable def exactlyOneMinor
    (operation : Column exactlyOneRel → Bool) : TernaryOp :=
  fun first second third => operation (exactlyOneSelector first second third)

theorem exactlyOneMinor_preserves {Γ : Gamma}
    (operation : Column exactlyOneRel → Bool)
    (preserves : PreservesLanguage Γ exactlyOneRel operation) :
    preservesTernary Γ (exactlyOneMinor operation) := by
  intro symbol tuples holds
  let columns : Fin (Γ.relationOf symbol).arity →
      Column exactlyOneRel := fun coordinate row =>
    exactlyOneSelector (tuples 0 coordinate) (tuples 1 coordinate)
      (tuples 2 coordinate) row
  apply preserves symbol columns
  intro row
  rcases row with ⟨tuple, tupleHolds⟩
  let i0 : Fin exactlyOneRel.arity := ⟨0, by simpa using exactlyOneRel_arity⟩
  let i1 : Fin exactlyOneRel.arity := ⟨1, by simpa using exactlyOneRel_arity⟩
  let i2 : Fin exactlyOneRel.arity := ⟨2, by simpa using exactlyOneRel_arity⟩
  have tupleEquality : tuple = StandardRelations.tripleTuple (tuple i0) (tuple i1) (tuple i2) := by
    funext index
    fin_cases index <;> rfl
  rw [tupleEquality, exactlyOneRel_holds, exactlyOne3Rel_holds_triple_iff] at tupleHolds
  cases h0 : tuple i0 <;> cases h1 : tuple i1 <;> cases h2 : tuple i2
  all_goals try simp only [Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true,
    Nat.reduceAdd, Nat.reduceEqDiff] at tupleHolds
  all_goals simp [columns, exactlyOneSelector, h0, h1, h2,
    show (0 : Fin 3) = i0 by rfl, show (1 : Fin 3) = i1 by rfl,
    show (2 : Fin 3) = i2 by rfl]
  all_goals first | simpa using holds 0 | simpa using holds 1 | simpa using holds 2

theorem exactlyOne_closed_of_notSchaeferTractable {Γ : Gamma}
    (nonempty : ∀ symbol : Γ.Symbol, (Γ.relationOf symbol).Nonempty)
    (notTractable : ¬ Γ.IsSchaeferTractable)
    (notComplement : ¬ PreservesComplement Γ) :
    PreservingOperationsRespectTarget Γ exactlyOneRel := by
  intro operation preserves
  have operationPreserves : Preserves Γ operation := by
    intro symbol tuples holds
    exact preserves symbol (fun coordinate row => tuples row coordinate) holds
  have zero : operation (fun _ => false) = false := by
    cases hzero : operation (fun _ => false)
    · rfl
    cases hone : operation (fun _ => true)
    · exact False.elim (notComplement
        (preservesComplement_of_diagonal_not operation
          operationPreserves hzero hone))
    · exact False.elim (notTractable (Or.inr (Or.inl
        (isOneValid_of_diagonal_true operation
          operationPreserves nonempty hzero hone))))
  have one : operation (fun _ => true) = true := by
    cases hone : operation (fun _ => true)
    · exact False.elim (notTractable (Or.inl
        (isZeroValid_of_diagonal_false operation operationPreserves
          nonempty zero hone)))
    · rfl
  let minor := exactlyOneMinor operation
  have minorPreserves : preservesTernary Γ minor :=
    exactlyOneMinor_preserves operation preserves
  have minorIdempotent : Idempotent minor := by
    constructor
    · simpa [minor, exactlyOneMinor, exactlyOneSelector_false] using zero
    · simpa [minor, exactlyOneMinor, exactlyOneSelector_true] using one
  rcases projection_of_idempotent_of_notSchaeferTractable
      minorPreserves minorIdempotent notTractable with projection | projection | projection
  · have equality : (fun index => operation
        (coordinateColumn exactlyOneRel index)) =
        StandardRelations.tripleTuple true false false := by
      funext index
      fin_cases index
      · simpa [minor, exactlyOneMinor, firstProjection, exactlyOneSelector_first] using
          congrFun (congrFun (congrFun projection true) false) false
      · simpa [minor, exactlyOneMinor, firstProjection, exactlyOneSelector_second] using
          congrFun (congrFun (congrFun projection false) true) false
      · simpa [minor, exactlyOneMinor, firstProjection, exactlyOneSelector_third] using
          congrFun (congrFun (congrFun projection false) false) true
    rw [equality, exactlyOneRel_holds, exactlyOne3Rel_holds_triple_iff]
    decide
  · have equality : (fun index => operation
        (coordinateColumn exactlyOneRel index)) =
        StandardRelations.tripleTuple false true false := by
      funext index
      fin_cases index
      · simpa [minor, exactlyOneMinor, secondProjection, exactlyOneSelector_first] using
          congrFun (congrFun (congrFun projection true) false) false
      · simpa [minor, exactlyOneMinor, secondProjection, exactlyOneSelector_second] using
          congrFun (congrFun (congrFun projection false) true) false
      · simpa [minor, exactlyOneMinor, secondProjection, exactlyOneSelector_third] using
          congrFun (congrFun (congrFun projection false) false) true
    rw [equality, exactlyOneRel_holds, exactlyOne3Rel_holds_triple_iff]
    decide
  · have equality : (fun index => operation
        (coordinateColumn exactlyOneRel index)) =
        StandardRelations.tripleTuple false false true := by
      funext index
      fin_cases index
      · simpa [minor, exactlyOneMinor, thirdProjection, exactlyOneSelector_first] using
          congrFun (congrFun (congrFun projection true) false) false
      · simpa [minor, exactlyOneMinor, thirdProjection, exactlyOneSelector_second] using
          congrFun (congrFun (congrFun projection false) true) false
      · simpa [minor, exactlyOneMinor, thirdProjection, exactlyOneSelector_third] using
          congrFun (congrFun (congrFun projection false) false) true
    rw [equality, exactlyOneRel_holds, exactlyOne3Rel_holds_triple_iff]
    decide

noncomputable def oneInThreeInterpretation {Γ : Gamma}
    (nonempty : ∀ symbol : Γ.Symbol, (Γ.relationOf symbol).Nonempty)
    (notTractable : ¬ Γ.IsSchaeferTractable)
    (notComplement : ¬ PreservesComplement Γ) :
    LanguageInterpretation oneInThreeCore Γ where
  gadgetOf := fun _ => CanonicalDatabase.gadget Γ exactlyOneRel
    exactlyOne_separates
    (exactlyOne_closed_of_notSchaeferTractable nonempty notTractable notComplement)

/-! ### The self-dual NAE branch -/

theorem ppDefines_disequality_of_preservesComplement {Γ : Gamma}
    (nonempty : ∀ symbol : Γ.Symbol, (Γ.relationOf symbol).Nonempty)
    (notTractable : ¬ Γ.IsSchaeferTractable)
    (complement : PreservesComplement Γ) :
    ExpressivePower.PPDefinesDisequality Γ := by
  have notZero : ¬ Γ.IsZeroValid := fun zero => notTractable (Or.inl zero)
  have notOne : ¬ Γ.IsOneValid := fun one => notTractable (Or.inr (Or.inl one))
  rcases ExpressivePower.ppDefines_constants_or_disequality_of_not_zero_one_valid
      Γ nonempty notZero notOne with
    constants | disequality
  · rcases constants with ⟨⟨zeroGadget⟩, _⟩
    have preserved := preserves_gadget
      (fun tuple : Fin 1 → Bool => !(tuple ⟨0, by decide⟩))
      (complement_preserves complement) zeroGadget
    let zeroTuple : BooleanTuple 1 := fun _ => false
    have zeroHolds : ExpressivePower.const0Rel.Holds zeroTuple := by
      rw [ExpressivePower.const0Rel_holds_iff]
    have oneHolds := preserved (fun _ => zeroTuple) (fun _ => zeroHolds)
    rw [ExpressivePower.const0Rel_holds_iff] at oneHolds
    have : False := by simpa [zeroTuple] using oneHolds
    exact this.elim
  · exact disequality

noncomputable def naeSelector (first second third : Bool) : Column naeRel :=
  fun row =>
    if row.1 0 && !row.1 1 && !row.1 2 then first else
    if !row.1 0 && row.1 1 && !row.1 2 then second else
    if !row.1 0 && !row.1 1 && row.1 2 then third else
    if !row.1 0 && row.1 1 && row.1 2 then !first else
    if row.1 0 && !row.1 1 && row.1 2 then !second else !third

noncomputable def naeMinor (operation : Column naeRel → Bool) : TernaryOp :=
  fun first second third => operation (naeSelector first second third)

theorem naeSelector_complement (first second third : Bool) :
    naeSelector (!first) (!second) (!third) =
      fun row => !(naeSelector first second third row) := by
  funext row
  rcases row with ⟨tuple, holds⟩
  have tupleEquality : tuple = StandardRelations.tripleTuple (tuple 0) (tuple 1) (tuple 2) := by
    funext index
    fin_cases index <;> rfl
  change StandardRelations.notAllEqual3Rel.Holds tuple at holds
  rw [tupleEquality, StandardRelations.notAllEqual3Rel_holds_triple_iff] at holds
  cases h0 : tuple 0 <;> cases h1 : tuple 1 <;> cases h2 : tuple 2 <;>
    simp_all [naeSelector]

theorem naeSelector_first :
    naeSelector true false false = coordinateColumn naeRel 0 := by
  funext row
  rcases row with ⟨tuple, holds⟩
  have tupleEquality : tuple = StandardRelations.tripleTuple (tuple 0) (tuple 1) (tuple 2) := by
    funext index
    fin_cases index <;> rfl
  change StandardRelations.notAllEqual3Rel.Holds tuple at holds
  rw [tupleEquality, StandardRelations.notAllEqual3Rel_holds_triple_iff] at holds
  cases h0 : tuple 0 <;> cases h1 : tuple 1 <;> cases h2 : tuple 2 <;>
    simp_all [naeSelector, coordinateColumn]

theorem naeSelector_second :
    naeSelector false true false = coordinateColumn naeRel 1 := by
  funext row
  rcases row with ⟨tuple, holds⟩
  have tupleEquality : tuple = StandardRelations.tripleTuple (tuple 0) (tuple 1) (tuple 2) := by
    funext index
    fin_cases index <;> rfl
  change StandardRelations.notAllEqual3Rel.Holds tuple at holds
  rw [tupleEquality, StandardRelations.notAllEqual3Rel_holds_triple_iff] at holds
  cases h0 : tuple 0 <;> cases h1 : tuple 1 <;> cases h2 : tuple 2 <;>
    simp_all [naeSelector, coordinateColumn]

theorem naeSelector_third :
    naeSelector false false true = coordinateColumn naeRel 2 := by
  funext row
  rcases row with ⟨tuple, holds⟩
  have tupleEquality : tuple = StandardRelations.tripleTuple (tuple 0) (tuple 1) (tuple 2) := by
    funext index
    fin_cases index <;> rfl
  change StandardRelations.notAllEqual3Rel.Holds tuple at holds
  rw [tupleEquality, StandardRelations.notAllEqual3Rel_holds_triple_iff] at holds
  cases h0 : tuple 0 <;> cases h1 : tuple 1 <;> cases h2 : tuple 2 <;>
    simp_all [naeSelector, coordinateColumn]

theorem naeMinor_preserves {Γ : Gamma}
    (operation : Column naeRel → Bool)
    (preserves : PreservesLanguage Γ naeRel operation)
    (complement : PreservesComplement Γ) :
    preservesTernary Γ (naeMinor operation) := by
  intro symbol tuples holds
  have complementTuples : ∀ index : Fin 3,
      (Γ.relationOf symbol).Holds (fun coordinate => !(tuples index coordinate)) := by
    intro index
    exact complement symbol (tuples index) (holds index)
  let columns : Fin (Γ.relationOf symbol).arity → Column naeRel := fun coordinate row =>
    naeSelector (tuples 0 coordinate) (tuples 1 coordinate) (tuples 2 coordinate) row
  apply preserves symbol columns
  intro row
  rcases row with ⟨tuple, tupleHolds⟩
  have tupleEquality : tuple = StandardRelations.tripleTuple (tuple 0) (tuple 1) (tuple 2) := by
    funext index
    fin_cases index <;> rfl
  change StandardRelations.notAllEqual3Rel.Holds tuple at tupleHolds
  rw [tupleEquality, StandardRelations.notAllEqual3Rel_holds_triple_iff] at tupleHolds
  cases h0 : tuple 0 <;> cases h1 : tuple 1 <;> cases h2 : tuple 2 <;>
    simp_all [columns, naeSelector]

theorem operation_selfDual_of_ppDefines_disequality {Γ : Gamma}
    (operation : Column naeRel → Bool)
    (preserves : PreservesLanguage Γ naeRel operation)
    (defined : ExpressivePower.PPDefinesDisequality Γ) :
    ∀ column, operation (fun row => !(column row)) = !(operation column) := by
  intro column
  rcases defined with ⟨gadget⟩
  have operationPreserves : Preserves Γ operation := by
    intro symbol tuples holds
    exact preserves symbol (fun coordinate row => tuples row coordinate) holds
  have preserved := preserves_gadget operation operationPreserves gadget
  let tuples : Row naeRel → BooleanTuple 2 := fun row => fun
    | ⟨0, _⟩ => column row
    | ⟨1, _⟩ => !(column row)
  have holds : ∀ row, ExpressivePower.diseqRel.Holds (tuples row) := by
    intro row
    rw [ExpressivePower.diseqRel_holds_iff]
    change column row ≠ !(column row)
    cases column row <;> decide
  have output := preserved tuples holds
  rw [ExpressivePower.diseqRel_holds_iff] at output
  have different := output
  change operation column ≠ operation (fun row => !(column row)) at different
  cases h : operation column <;> cases hc : operation (fun row => !(column row)) <;>
    simp_all

theorem nae_closed_of_notSchaeferTractable {Γ : Gamma}
    (nonempty : ∀ symbol : Γ.Symbol, (Γ.relationOf symbol).Nonempty)
    (notTractable : ¬ Γ.IsSchaeferTractable)
    (complement : PreservesComplement Γ) :
    PreservingOperationsRespectTarget Γ naeRel := by
  intro operation preserves
  have defined := ppDefines_disequality_of_preservesComplement
    nonempty notTractable complement
  have selfDual := operation_selfDual_of_ppDefines_disequality operation preserves defined
  let raw := naeMinor operation
  have rawPreserves : preservesTernary Γ raw :=
    naeMinor_preserves operation preserves complement
  let normalized : TernaryOp :=
    if raw false false false then fun x y z => !(raw x y z) else raw
  have normalizedPreserves : preservesTernary Γ normalized := by
    dsimp [normalized]
    split <;> rename_i diagonal
    · intro symbol tuples holds
      exact complement symbol _ (rawPreserves symbol tuples holds)
    · exact rawPreserves
  have rawComplement : ∀ x y z, raw (!x) (!y) (!z) = !(raw x y z) := by
    intro x y z
    dsimp [raw, naeMinor]
    rw [naeSelector_complement, selfDual]
  have normalizedIdempotent : Idempotent normalized := by
    constructor
    · dsimp [normalized]
      split <;> simp_all
    · have diagonal := rawComplement false false false
      dsimp [normalized]
      split <;> simp_all
  rcases projection_of_idempotent_of_notSchaeferTractable
      normalizedPreserves normalizedIdempotent notTractable with
    projection | projection | projection
  all_goals
    have outputEquality : (fun index => operation (coordinateColumn naeRel index)) =
        (fun index => raw
          (StandardRelations.tripleTuple true false false index)
          (StandardRelations.tripleTuple false true false index)
          (StandardRelations.tripleTuple false false true index)) := by
      funext index
      fin_cases index
      · dsimp [raw, naeMinor]
        exact congrArg operation naeSelector_first.symm
      · dsimp [raw, naeMinor]
        exact congrArg operation naeSelector_second.symm
      · dsimp [raw, naeMinor]
        exact congrArg operation naeSelector_third.symm
    rw [outputEquality]
    have rawOutputEquality :
        (fun index => raw
          (StandardRelations.tripleTuple true false false index)
          (StandardRelations.tripleTuple false true false index)
          (StandardRelations.tripleTuple false false true index)) =
        StandardRelations.tripleTuple
          (raw true false false) (raw false true false) (raw false false true) := by
      funext index
      fin_cases index <;> rfl
    rw [rawOutputEquality]
  · dsimp [normalized] at projection
    split at projection <;> rename_i diagonal
    · have values := congrFun (congrFun (congrFun projection true) false) false
      have values2 := congrFun (congrFun (congrFun projection false) true) false
      have values3 := congrFun (congrFun (congrFun projection false) false) true
      rw [naeRel_holds, StandardRelations.notAllEqual3Rel_holds_triple_iff]
      simp_all [firstProjection]
    · rw [projection]
      rw [naeRel_holds, StandardRelations.notAllEqual3Rel_holds_triple_iff]
      decide
  · dsimp [normalized] at projection
    split at projection <;> rename_i diagonal
    · have values := congrFun (congrFun (congrFun projection true) false) false
      have values2 := congrFun (congrFun (congrFun projection false) true) false
      have values3 := congrFun (congrFun (congrFun projection false) false) true
      rw [naeRel_holds, StandardRelations.notAllEqual3Rel_holds_triple_iff]
      simp_all [secondProjection]
    · rw [projection]
      rw [naeRel_holds, StandardRelations.notAllEqual3Rel_holds_triple_iff]
      decide
  · dsimp [normalized] at projection
    split at projection <;> rename_i diagonal
    · have values := congrFun (congrFun (congrFun projection true) false) false
      have values2 := congrFun (congrFun (congrFun projection false) true) false
      have values3 := congrFun (congrFun (congrFun projection false) false) true
      rw [naeRel_holds, StandardRelations.notAllEqual3Rel_holds_triple_iff]
      simp_all [thirdProjection]
    · rw [projection]
      rw [naeRel_holds, StandardRelations.notAllEqual3Rel_holds_triple_iff]
      decide

noncomputable def naeInterpretation {Γ : Gamma}
    (nonempty : ∀ symbol : Γ.Symbol, (Γ.relationOf symbol).Nonempty)
    (notTractable : ¬ Γ.IsSchaeferTractable)
    (complement : PreservesComplement Γ) : LanguageInterpretation nae3Core Γ where
  gadgetOf := fun _ => CanonicalDatabase.gadget Γ naeRel nae_separates
    (nae_closed_of_notSchaeferTractable nonempty notTractable complement)

/-- Every non-Schaefer finite Boolean language pp-interprets either positive
1-IN-3 or positive NAE-3.  The split is exactly closure under complement. -/
theorem oneInThree_or_nae_interpretation {Γ : Gamma}
    (nonempty : ∀ symbol : Γ.Symbol, (Γ.relationOf symbol).Nonempty)
    (notTractable : ¬ Γ.IsSchaeferTractable) :
    Nonempty (LanguageInterpretation oneInThreeCore Γ) ∨
      Nonempty (LanguageInterpretation nae3Core Γ) := by
  classical
  by_cases complement : PreservesComplement Γ
  · exact Or.inr ⟨naeInterpretation nonempty notTractable complement⟩
  · exact Or.inl ⟨oneInThreeInterpretation nonempty notTractable complement⟩

assert_standard_axioms
  oneInThreeInterpretation,
  naeInterpretation,
  oneInThree_or_nae_interpretation

end CanonicalHardCores
end Hardness
end BooleanCSP
end Domain
end ComplexityReduction
