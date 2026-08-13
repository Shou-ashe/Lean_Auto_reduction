/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP.Relation
import ComplexityReduction.Domain.BooleanCSP.Gamma
import ComplexityReduction.Domain.BooleanCSP.CSPInstance
import ComplexityReduction.Legacy.ComplexityReduction.CSP.StandardRelations
import ComplexityReduction.Legacy.ComplexityReduction.CSP.Examples.ThreeSATLike
import ComplexityReduction.Legacy.ComplexityReduction.SAT.Literal

/-!
Schaefer's hard Boolean CSP cores.

The natural-language hardness proof of Schaefer's dichotomy reduces, for each
of the six tractability violations, to a finite set of canonical NP-hard
constraint languages.  This module fixes the core languages used by this
library's hardness development:

* `threeSATLikeCore`: the eight ternary clause relations with polarity flags
  (ordinary 3SAT), already connected to the canonical structured-3SAT endpoint
  by `Domain.ThreeSATToThreeSATLikeStandardTM`.
* `nae3Core`: the positive ternary not-all-equal relation.  NAE(x, y, y)
  expresses disequality, so signed literals are recovered by the standard
  complement gadget.
* `oneInThreeCore`: the positive ternary exactly-one relation.
* `exactlyTwo3Core`: the positive ternary exactly-two relation.

The two `exactly*` cores are primitive-positively interdefinable: exactly-one
with polarity complements is exactly-two, and each core expresses the
complement gadget by two constraints.  All gadget lemmas are proved at the
truth-table level.
-/

namespace ComplexityReduction
namespace Domain
namespace BooleanCSP
namespace Hardness

open ComplexityReduction.CSP

/-! ### The four core languages -/

/-- The 3SAT-like core: ternary clause relations over all eight polarity flags. -/
noncomputable def threeSATLikeCore : Gamma :=
  ComplexityReduction.CSP.Examples.threeSATLikeLanguage

/-- The positive not-all-equal-3 core. -/
noncomputable def nae3Core : Gamma where
  Symbol := Unit
  finiteSymbol := inferInstance
  relationOf := fun _ => StandardRelations.notAllEqual3Rel

/-- The positive exactly-one-of-3 core. -/
noncomputable def oneInThreeCore : Gamma where
  Symbol := Unit
  finiteSymbol := inferInstance
  relationOf := fun _ => StandardRelations.exactlyOne3Rel

/-- The positive exactly-two-of-3 core. -/
noncomputable def exactlyTwo3Core : Gamma where
  Symbol := Unit
  finiteSymbol := inferInstance
  relationOf := fun _ => StandardRelations.exactlyRel 3 2

/-! ### Truth-table meanings -/

/-- The number of true entries of an ordered triple. -/
@[simp]
theorem trueCount_tripleTuple (x y z : Bool) :
    StandardRelations.trueCount 3 (StandardRelations.tripleTuple x y z) =
      (if x then 1 else 0) + (if y then 1 else 0) + (if z then 1 else 0) := by
  classical
  unfold StandardRelations.trueCount
  have hUniv : (Finset.univ : Finset (Fin 3)) =
      {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩} := by
    ext i
    fin_cases i <;> simp
  rw [hUniv]
  cases x <;> cases y <;> cases z <;> decide

/-- Exactly-one-of-three is a Hamming-weight-one condition. -/
theorem exactlyOne3Rel_holds_triple_iff (x y z : Bool) :
    StandardRelations.exactlyOne3Rel.Holds
        (StandardRelations.tripleTuple x y z) ↔
      (if x then 1 else 0) + (if y then 1 else 0) + (if z then 1 else 0) = 1 := by
  classical
  unfold StandardRelations.exactlyOne3Rel StandardRelations.exactlyRel
  rw [BoolRel.holds_ofPredicate_iff]
  simp [trueCount_tripleTuple]

/-- Exactly-two-of-three is a Hamming-weight-two condition. -/
theorem exactlyTwo3Rel_holds_triple_iff (x y z : Bool) :
    (StandardRelations.exactlyRel 3 2).Holds
        (StandardRelations.tripleTuple x y z) ↔
      (if x then 1 else 0) + (if y then 1 else 0) + (if z then 1 else 0) = 2 := by
  classical
  unfold StandardRelations.exactlyRel
  rw [BoolRel.holds_ofPredicate_iff]
  simp [trueCount_tripleTuple]

/-! ### The positive NAE-3 core -/

/-- One positive ternary NAE constraint over three variable keys. -/
noncomputable def nae3Constraint (first second third : Nat) : Constraint nae3Core where
  symbol := ()
  vars := fun
    | ⟨0, _⟩ => first
    | ⟨1, _⟩ => second
    | ⟨2, _⟩ => third

/-- NAE satisfaction is exactly rejection of the constant tuple. -/
theorem nae3Constraint_satisfies_iff (first second third : Nat)
    (assignment : SAT.Assignment) :
    Constraint.Satisfies (nae3Constraint first second third) assignment ↔
      ¬ (assignment first = assignment second ∧
        assignment second = assignment third) := by
  let tuple := Constraint.assignmentTuple
    (nae3Constraint first second third) assignment
  have tupleEquality : tuple =
      StandardRelations.tripleTuple (assignment first) (assignment second)
        (assignment third) := by
    funext index
    fin_cases index <;> rfl
  change StandardRelations.notAllEqual3Rel.Holds tuple ↔ _
  rw [tupleEquality]
  exact StandardRelations.notAllEqual3Rel_holds_triple_iff _ _ _

/-- Two Boolean values differ exactly when the second is the first's complement. -/
theorem bool_ne_iff_eq_not (first second : Bool) :
    first ≠ second ↔ second = !first := by
  cases first <;> cases second <;> simp

/-! ### Pure Boolean helper laws for the gadget proofs -//-! ### Pure Boolean helper laws for the gadget proofs -/

/-- `x + y + u = 1` with `v + u + u = 1` forces `x ≠ y`. -/
theorem disequality_of_weightOne (x y u v : Bool) :
    (if x then 1 else 0) + (if y then 1 else 0) + (if u then 1 else 0) = 1 ∧
      (if v then 1 else 0) + (if u then 1 else 0) + (if u then 1 else 0) = 1 →
        x ≠ y := by
  cases x <;> cases y <;> cases u <;> cases v <;> decide

/-- The canonical witness `u = false, v = true` realizes the disequality gadget. -/
theorem disequality_witness_of_ne (x : Bool) :
    (if x then 1 else 0) + (if !x then 1 else 0) + (if false then 1 else 0) = 1 ∧
      (if true then 1 else 0) + (if false then 1 else 0) + (if false then 1 else 0) = 1 := by
  cases x <;> decide

/-- `v + u + u = 1` pins `u = false`. -/
theorem pinFalse_of_weightOne (v u : Bool) :
    (if v then 1 else 0) + (if u then 1 else 0) + (if u then 1 else 0) = 1 →
      u = false := by
  cases v <;> cases u <;> decide

/-- `u + v + v = 1` pins `u = true`. -/
theorem pinTrue_of_weightOne (u v : Bool) :
    (if u then 1 else 0) + (if v then 1 else 0) + (if v then 1 else 0) = 1 →
      u = true := by
  cases u <;> cases v <;> decide

/-- `x + y + c = 2` with `d + c + c = 2` forces `y = ¬x`. -/
theorem negation_of_weightTwo (x y c d : Bool) :
    (if x then 1 else 0) + (if y then 1 else 0) + (if c then 1 else 0) = 2 ∧
      (if d then 1 else 0) + (if c then 1 else 0) + (if c then 1 else 0) = 2 →
        y = !x := by
  cases x <;> cases y <;> cases c <;> cases d <;> decide

/-- The canonical witness `y = ¬x, c = true, d = false` realizes the negation gadget. -/
theorem negation_witness_of_weightTwo (x : Bool) :
    (if x then 1 else 0) + (if !x then 1 else 0) + (if true then 1 else 0) = 2 ∧
      (if false then 1 else 0) + (if true then 1 else 0) + (if true then 1 else 0) = 2 := by
  cases x <;> decide

/-- Complemented weight-two is weight-one. -/
theorem weightTwo_of_complements_iff_weightOne (x y z : Bool) :
    (if !x then 1 else 0) + (if !y then 1 else 0) + (if !z then 1 else 0) = 2 ↔
      (if x then 1 else 0) + (if y then 1 else 0) + (if z then 1 else 0) = 1 := by
  cases x <;> cases y <;> cases z <;> decide

/-- Complemented weight-one is weight-two. -/
theorem weightOne_of_complements_iff_weightTwo (x y z : Bool) :
    (if !x then 1 else 0) + (if !y then 1 else 0) + (if !z then 1 else 0) = 1 ↔
      (if x then 1 else 0) + (if y then 1 else 0) + (if z then 1 else 0) = 2 := by
  cases x <;> cases y <;> cases z <;> decide

/-- Pairwise disequalities plus complemented weight-one imply weight-two. -/
theorem weightOne_disequalities_to_weightTwo (x y z x' y' z' : Bool) :
    x ≠ x' ∧ y ≠ y' ∧ z ≠ z' ∧
      (if x' then 1 else 0) + (if y' then 1 else 0) + (if z' then 1 else 0) = 1 →
        (if x then 1 else 0) + (if y then 1 else 0) + (if z then 1 else 0) = 2 := by
  cases x <;> cases y <;> cases z <;>
    cases x' <;> cases y' <;> cases z' <;> decide

/-- `NAE(x, y, y)` expresses the disequality `x ≠ y`. -/
theorem nae3Constraint_repeat_satisfies_iff (first second : Nat)
    (assignment : SAT.Assignment) :
    Constraint.Satisfies (nae3Constraint first second second) assignment ↔
      assignment second = !assignment first := by
  rw [nae3Constraint_satisfies_iff]
  constructor
  · intro different
    apply (bool_ne_iff_eq_not _ _).1
    intro equal
    exact different ⟨equal, rfl⟩
  · intro complement equalities
    have different : assignment first ≠ assignment second :=
      (bool_ne_iff_eq_not _ _).2 complement
    exact different equalities.1

/-! ### The positive exactly-one core -/

/-- One positive ternary exactly-one constraint. -/
noncomputable def oneInThreeConstraint (first second third : Nat) : Constraint oneInThreeCore where
  symbol := ()
  vars := fun
    | ⟨0, _⟩ => first
    | ⟨1, _⟩ => second
    | ⟨2, _⟩ => third

/-- Exactly-one satisfaction is the Hamming-weight-one condition. -/
theorem oneInThreeConstraint_satisfies_iff (first second third : Nat)
    (assignment : SAT.Assignment) :
    Constraint.Satisfies (oneInThreeConstraint first second third) assignment ↔
      (if assignment first then 1 else 0) +
        (if assignment second then 1 else 0) +
        (if assignment third then 1 else 0) = 1 := by
  let tuple := Constraint.assignmentTuple
    (oneInThreeConstraint first second third) assignment
  have tupleEquality : tuple =
      StandardRelations.tripleTuple (assignment first) (assignment second)
        (assignment third) := by
    funext index
    fin_cases index <;> rfl
  change StandardRelations.exactlyOne3Rel.Holds tuple ↔ _
  rw [tupleEquality]
  exact exactlyOne3Rel_holds_triple_iff _ _ _

/-- The disequality gadget: `1in3(x, y, u)` with `1in3(v, u, u)` forces `x ≠ y`. -/
theorem oneInThree_disequality_iff (x y u v : Nat)
    (assignment : SAT.Assignment) :
    Constraint.Satisfies (oneInThreeConstraint x y u) assignment ∧
      Constraint.Satisfies (oneInThreeConstraint v u u) assignment →
        assignment x ≠ assignment y := by
  rw [oneInThreeConstraint_satisfies_iff, oneInThreeConstraint_satisfies_iff]
  exact disequality_of_weightOne (assignment x) (assignment y)
    (assignment u) (assignment v)

/-- Pin false: `1in3(v, u, u)` with fresh `v` forces `u = false`. -/
theorem oneInThree_pinFalse (u v : Nat) (assignment : SAT.Assignment) :
    Constraint.Satisfies (oneInThreeConstraint v u u) assignment →
      assignment u = false := by
  rw [oneInThreeConstraint_satisfies_iff]
  exact pinFalse_of_weightOne (assignment v) (assignment u)

/-- Pin true: `1in3(u, v, v)` with fresh `v` forces `u = true`. -/
theorem oneInThree_pinTrue (u v : Nat) (assignment : SAT.Assignment) :
    Constraint.Satisfies (oneInThreeConstraint u v v) assignment →
      assignment u = true := by
  rw [oneInThreeConstraint_satisfies_iff]
  exact pinTrue_of_weightOne (assignment u) (assignment v)

/-! ### The positive exactly-two core -/

/-- One positive ternary exactly-two constraint. -/
noncomputable def exactlyTwo3Constraint (first second third : Nat) :
    Constraint exactlyTwo3Core where
  symbol := ()
  vars := fun
    | ⟨0, _⟩ => first
    | ⟨1, _⟩ => second
    | ⟨2, _⟩ => third

/-- Exactly-two satisfaction is the Hamming-weight-two condition. -/
theorem exactlyTwo3Constraint_satisfies_iff (first second third : Nat)
    (assignment : SAT.Assignment) :
    Constraint.Satisfies (exactlyTwo3Constraint first second third) assignment ↔
      (if assignment first then 1 else 0) +
        (if assignment second then 1 else 0) +
        (if assignment third then 1 else 0) = 2 := by
  let tuple := Constraint.assignmentTuple
    (exactlyTwo3Constraint first second third) assignment
  have tupleEquality : tuple =
      StandardRelations.tripleTuple (assignment first) (assignment second)
        (assignment third) := by
    funext index
    fin_cases index <;> rfl
  change (StandardRelations.exactlyRel 3 2).Holds tuple ↔ _
  rw [tupleEquality]
  exact exactlyTwo3Rel_holds_triple_iff _ _ _

/-- The complement gadget: `E2O3(x, y, c)` with `E2O3(d, c, c)` forces `y = ¬x`. -/
theorem exactlyTwo3_negation (x y c d : Nat) (assignment : SAT.Assignment) :
    Constraint.Satisfies (exactlyTwo3Constraint x y c) assignment ∧
      Constraint.Satisfies (exactlyTwo3Constraint d c c) assignment →
        assignment y = !assignment x := by
  rw [exactlyTwo3Constraint_satisfies_iff, exactlyTwo3Constraint_satisfies_iff]
  exact negation_of_weightTwo (assignment x) (assignment y)
    (assignment c) (assignment d)

/-! ### Exactly-one and exactly-two are interdefinable -/

/-- The canonical witness assignment of the exactly-two gadget for one tuple. -/
noncomputable def oneInThreeTupleWitness (tuple : BooleanTuple 3) : SAT.Assignment :=
  fun var =>
    match var with
    | 0 => tuple ⟨0, by decide⟩
    | 1 => tuple ⟨1, by decide⟩
    | 2 => tuple ⟨2, by decide⟩
    | 3 => !(tuple ⟨0, by decide⟩)
    | 4 => !(tuple ⟨1, by decide⟩)
    | 5 => !(tuple ⟨2, by decide⟩)
    | 6 => true
    | 7 => false
    | 8 => true
    | 9 => false
    | 10 => true
    | 11 => false
    | _ => false

/--
Soundness of the seven-constraint exactly-two gadget: on any assignment that
satisfies the gadget at the canonical auxiliary keys, the three output keys
take a weight-one tuple.
-/
theorem exactlyOne3_of_exactlyTwo3_gadget
    (x y z x' y' z' c₁ d₁ c₂ d₂ c₃ d₃ : Nat) (assignment : SAT.Assignment) :
    Constraint.Satisfies (exactlyTwo3Constraint x x' c₁) assignment ∧
      Constraint.Satisfies (exactlyTwo3Constraint d₁ c₁ c₁) assignment ∧
      Constraint.Satisfies (exactlyTwo3Constraint y y' c₂) assignment ∧
      Constraint.Satisfies (exactlyTwo3Constraint d₂ c₂ c₂) assignment ∧
      Constraint.Satisfies (exactlyTwo3Constraint z z' c₃) assignment ∧
      Constraint.Satisfies (exactlyTwo3Constraint d₃ c₃ c₃) assignment ∧
      Constraint.Satisfies (exactlyTwo3Constraint x' y' z') assignment →
        StandardRelations.exactlyOne3Rel.Holds
          (StandardRelations.tripleTuple (assignment x) (assignment y)
            (assignment z)) := by
  rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have hx' : assignment x' = !assignment x :=
    exactlyTwo3_negation x x' c₁ d₁ assignment ⟨h1, h2⟩
  have hy' : assignment y' = !assignment y :=
    exactlyTwo3_negation y y' c₂ d₂ assignment ⟨h3, h4⟩
  have hz' : assignment z' = !assignment z :=
    exactlyTwo3_negation z z' c₃ d₃ assignment ⟨h5, h6⟩
  rw [exactlyOne3Rel_holds_triple_iff]
  have hsum : (if assignment x' then 1 else 0) +
      (if assignment y' then 1 else 0) +
      (if assignment z' then 1 else 0) = 2 :=
    (exactlyTwo3Constraint_satisfies_iff x' y' z' assignment).1 h7
  rw [hx', hy', hz'] at hsum
  exact (weightTwo_of_complements_iff_weightOne (assignment x)
    (assignment y) (assignment z)).1 hsum

/--
Completeness of the exactly-two gadget: every weight-one tuple has a witness
assignment satisfying the seven constraints at the canonical keys.
-/
theorem exactlyTwo3_gadget_witness {tuple : BooleanTuple 3}
    (tupleHolds : StandardRelations.exactlyOne3Rel.Holds tuple) :
    Constraint.Satisfies (exactlyTwo3Constraint 0 3 6) (oneInThreeTupleWitness tuple) ∧
      Constraint.Satisfies (exactlyTwo3Constraint 7 6 6) (oneInThreeTupleWitness tuple) ∧
      Constraint.Satisfies (exactlyTwo3Constraint 1 4 8) (oneInThreeTupleWitness tuple) ∧
      Constraint.Satisfies (exactlyTwo3Constraint 9 8 8) (oneInThreeTupleWitness tuple) ∧
      Constraint.Satisfies (exactlyTwo3Constraint 2 5 10) (oneInThreeTupleWitness tuple) ∧
      Constraint.Satisfies (exactlyTwo3Constraint 11 10 10) (oneInThreeTupleWitness tuple) ∧
      Constraint.Satisfies (exactlyTwo3Constraint 3 4 5) (oneInThreeTupleWitness tuple) := by
  have hsum : (if tuple ⟨0, by decide⟩ then 1 else 0) +
      (if tuple ⟨1, by decide⟩ then 1 else 0) +
      (if tuple ⟨2, by decide⟩ then 1 else 0) = 1 := by
    have htuple : StandardRelations.tripleTuple (tuple ⟨0, by decide⟩)
        (tuple ⟨1, by decide⟩) (tuple ⟨2, by decide⟩) = tuple := by
      funext i
      fin_cases i <;> rfl
    apply (exactlyOne3Rel_holds_triple_iff (tuple ⟨0, by decide⟩)
      (tuple ⟨1, by decide⟩) (tuple ⟨2, by decide⟩)).1
    rw [htuple]
    exact tupleHolds
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (exactlyTwo3Constraint_satisfies_iff 0 3 6 (oneInThreeTupleWitness tuple)).2
      (by simpa [oneInThreeTupleWitness] using
        (negation_witness_of_weightTwo (tuple ⟨0, by decide⟩)).1)
  · exact (exactlyTwo3Constraint_satisfies_iff 7 6 6 (oneInThreeTupleWitness tuple)).2
      (by simpa [oneInThreeTupleWitness] using
        (negation_witness_of_weightTwo (tuple ⟨0, by decide⟩)).2)
  · exact (exactlyTwo3Constraint_satisfies_iff 1 4 8 (oneInThreeTupleWitness tuple)).2
      (by simpa [oneInThreeTupleWitness] using
        (negation_witness_of_weightTwo (tuple ⟨1, by decide⟩)).1)
  · exact (exactlyTwo3Constraint_satisfies_iff 9 8 8 (oneInThreeTupleWitness tuple)).2
      (by simpa [oneInThreeTupleWitness] using
        (negation_witness_of_weightTwo (tuple ⟨1, by decide⟩)).2)
  · exact (exactlyTwo3Constraint_satisfies_iff 2 5 10 (oneInThreeTupleWitness tuple)).2
      (by simpa [oneInThreeTupleWitness] using
        (negation_witness_of_weightTwo (tuple ⟨2, by decide⟩)).1)
  · exact (exactlyTwo3Constraint_satisfies_iff 11 10 10 (oneInThreeTupleWitness tuple)).2
      (by simpa [oneInThreeTupleWitness] using
        (negation_witness_of_weightTwo (tuple ⟨2, by decide⟩)).2)
  · exact (exactlyTwo3Constraint_satisfies_iff 3 4 5 (oneInThreeTupleWitness tuple)).2
      (by simpa [oneInThreeTupleWitness] using
        (weightTwo_of_complements_iff_weightOne (tuple ⟨0, by decide⟩)
          (tuple ⟨1, by decide⟩) (tuple ⟨2, by decide⟩)).2 hsum)

/-- The canonical witness assignment of the exactly-one gadget for one tuple. -/
noncomputable def exactlyTwo3TupleWitness (tuple : BooleanTuple 3) : SAT.Assignment :=
  fun var =>
    match var with
    | 0 => tuple ⟨0, by decide⟩
    | 1 => tuple ⟨1, by decide⟩
    | 2 => tuple ⟨2, by decide⟩
    | 3 => !(tuple ⟨0, by decide⟩)
    | 4 => !(tuple ⟨1, by decide⟩)
    | 5 => !(tuple ⟨2, by decide⟩)
    | 6 => false
    | 7 => true
    | 8 => false
    | 9 => true
    | 10 => false
    | 11 => true
    | _ => false

/--
Soundness of the dual seven-constraint exactly-one gadget: any assignment
satisfying the gadget realizes a weight-two tuple on the output keys.
-/
theorem exactlyTwo3_of_oneInThree_gadget
    (x y z x' y' z' c₁ d₁ c₂ d₂ c₃ d₃ : Nat) (assignment : SAT.Assignment) :
    Constraint.Satisfies (oneInThreeConstraint x x' c₁) assignment ∧
      Constraint.Satisfies (oneInThreeConstraint d₁ c₁ c₁) assignment ∧
      Constraint.Satisfies (oneInThreeConstraint y y' c₂) assignment ∧
      Constraint.Satisfies (oneInThreeConstraint d₂ c₂ c₂) assignment ∧
      Constraint.Satisfies (oneInThreeConstraint z z' c₃) assignment ∧
      Constraint.Satisfies (oneInThreeConstraint d₃ c₃ c₃) assignment ∧
      Constraint.Satisfies (oneInThreeConstraint x' y' z') assignment →
        (StandardRelations.exactlyRel 3 2).Holds
          (StandardRelations.tripleTuple (assignment x) (assignment y)
            (assignment z)) := by
  rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have hx' : assignment x ≠ assignment x' :=
    oneInThree_disequality_iff x x' c₁ d₁ assignment ⟨h1, h2⟩
  have hy' : assignment y ≠ assignment y' :=
    oneInThree_disequality_iff y y' c₂ d₂ assignment ⟨h3, h4⟩
  have hz' : assignment z ≠ assignment z' :=
    oneInThree_disequality_iff z z' c₃ d₃ assignment ⟨h5, h6⟩
  rw [exactlyTwo3Rel_holds_triple_iff]
  have hsum : (if assignment x' then 1 else 0) +
      (if assignment y' then 1 else 0) +
      (if assignment z' then 1 else 0) = 1 :=
    (oneInThreeConstraint_satisfies_iff x' y' z' assignment).1 h7
  exact weightOne_disequalities_to_weightTwo (assignment x) (assignment y)
    (assignment z) (assignment x') (assignment y') (assignment z')
    ⟨hx', hy', hz', hsum⟩

/--
Completeness of the dual gadget: every weight-two tuple has a witness
assignment satisfying the seven exactly-one constraints at the canonical keys.
-/
theorem oneInThree_gadget_witness {tuple : BooleanTuple 3}
    (tupleHolds : (StandardRelations.exactlyRel 3 2).Holds tuple) :
    Constraint.Satisfies (oneInThreeConstraint 0 3 6) (exactlyTwo3TupleWitness tuple) ∧
      Constraint.Satisfies (oneInThreeConstraint 7 6 6) (exactlyTwo3TupleWitness tuple) ∧
      Constraint.Satisfies (oneInThreeConstraint 1 4 8) (exactlyTwo3TupleWitness tuple) ∧
      Constraint.Satisfies (oneInThreeConstraint 9 8 8) (exactlyTwo3TupleWitness tuple) ∧
      Constraint.Satisfies (oneInThreeConstraint 2 5 10) (exactlyTwo3TupleWitness tuple) ∧
      Constraint.Satisfies (oneInThreeConstraint 11 10 10) (exactlyTwo3TupleWitness tuple) ∧
      Constraint.Satisfies (oneInThreeConstraint 3 4 5) (exactlyTwo3TupleWitness tuple) := by
  have hsum : (if tuple ⟨0, by decide⟩ then 1 else 0) +
      (if tuple ⟨1, by decide⟩ then 1 else 0) +
      (if tuple ⟨2, by decide⟩ then 1 else 0) = 2 := by
    have htuple : StandardRelations.tripleTuple (tuple ⟨0, by decide⟩)
        (tuple ⟨1, by decide⟩) (tuple ⟨2, by decide⟩) = tuple := by
      funext i
      fin_cases i <;> rfl
    apply (exactlyTwo3Rel_holds_triple_iff (tuple ⟨0, by decide⟩)
      (tuple ⟨1, by decide⟩) (tuple ⟨2, by decide⟩)).1
    rw [htuple]
    exact tupleHolds
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (oneInThreeConstraint_satisfies_iff 0 3 6 (exactlyTwo3TupleWitness tuple)).2
      (by simpa [exactlyTwo3TupleWitness] using
        (disequality_witness_of_ne (tuple ⟨0, by decide⟩)).1)
  · exact (oneInThreeConstraint_satisfies_iff 7 6 6 (exactlyTwo3TupleWitness tuple)).2
      (by simpa [exactlyTwo3TupleWitness] using
        (disequality_witness_of_ne (tuple ⟨0, by decide⟩)).2)
  · exact (oneInThreeConstraint_satisfies_iff 1 4 8 (exactlyTwo3TupleWitness tuple)).2
      (by simpa [exactlyTwo3TupleWitness] using
        (disequality_witness_of_ne (tuple ⟨1, by decide⟩)).1)
  · exact (oneInThreeConstraint_satisfies_iff 9 8 8 (exactlyTwo3TupleWitness tuple)).2
      (by simpa [exactlyTwo3TupleWitness] using
        (disequality_witness_of_ne (tuple ⟨1, by decide⟩)).2)
  · exact (oneInThreeConstraint_satisfies_iff 2 5 10 (exactlyTwo3TupleWitness tuple)).2
      (by simpa [exactlyTwo3TupleWitness] using
        (disequality_witness_of_ne (tuple ⟨2, by decide⟩)).1)
  · exact (oneInThreeConstraint_satisfies_iff 11 10 10 (exactlyTwo3TupleWitness tuple)).2
      (by simpa [exactlyTwo3TupleWitness] using
        (disequality_witness_of_ne (tuple ⟨2, by decide⟩)).2)
  · exact (oneInThreeConstraint_satisfies_iff 3 4 5 (exactlyTwo3TupleWitness tuple)).2
      (by simpa [exactlyTwo3TupleWitness] using
        (weightOne_of_complements_iff_weightTwo (tuple ⟨0, by decide⟩)
          (tuple ⟨1, by decide⟩) (tuple ⟨2, by decide⟩)).2 hsum)

end Hardness
end BooleanCSP
end Domain
end ComplexityReduction
