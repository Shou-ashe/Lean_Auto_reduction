/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP.Hardness.Cores
import ComplexityReduction.Domain.BooleanCSP.Hardness.PPDefinability
import ComplexityReduction.Domain.BooleanCSP.Classes
import ComplexityReduction.Legacy.ComplexityReduction.CSP.StandardRelations

/-!
Expressive power of Schaefer's hardness proof: the case analysis.

The natural-language proof of the hardness direction of Schaefer's dichotomy
(Schaefer 1978; Creignou–Khanna–Sudan, Chapter 4) proceeds in two steps:

1. *Hard cores*: a finite list of canonical languages is NP-hard (certified
   elsewhere in this directory).
2. *Expressive power*: every finite Boolean language `Γ` outside the six
   tractable classes (0-valid, 1-valid, Horn, dual-Horn, bijunctive, affine)
   primitive-positively defines one of those cores.  Substituting the defining
   gadgets transports the certified hardness to `CSP(Γ)`.

This module supplies the second step.  Its library-level lemmas are proved:

* the closure algebra `Horn ∧ dual-Horn → bijunctive`, so a language missing
  bijunctivity is missing Horn or dual-Horn;
* the *constants-or-disequality* dichotomy: a language that is neither 0-valid
  nor 1-valid pp-defines both constants, with canonical pin formulas, or the
  disequality relation (`constantsCase_or_disequality_of_not_zero_one_valid`);
* the *Horn* and *dual-Horn* gadget lemmas: with both constants, a
  meet-failure pp-defines the positive or negative binary clause, or the
  disequality relation;
* the hard cores are outside all six tractable classes, and the core
  languages realize the auxiliary relations used by the case analysis
  (disequality from NAE-3, both constants from 1-in-3 / 2-of-3).

The final assembly of the case analysis into a primitive-positive
interpretation of one certified hard core is the classical step packaged at
the top of `Hardness.SchaeferHardness` as
`interpretation_hardCore_of_not_schaefer_tractable`.
-/

namespace ComplexityReduction
namespace Domain
namespace BooleanCSP
namespace Hardness
namespace ExpressivePower

open ComplexityReduction.CSP

/-! ### Standard auxiliary relations -/

/-- The unary constant-zero relation. -/
noncomputable def const0Rel : BoolRel :=
  BoolRel.ofPredicate 1 fun t => t ⟨0, by decide⟩ = false

/-- The unary constant-one relation. -/
noncomputable def const1Rel : BoolRel :=
  BoolRel.ofPredicate 1 fun t => t ⟨0, by decide⟩ = true

/-- The binary disequality relation `x ≠ y`. -/
noncomputable def diseqRel : BoolRel :=
  BoolRel.ofPredicate 2 fun t => t ⟨0, by decide⟩ ≠ t ⟨1, by decide⟩

/-- The binary positive clause `x ∨ y`. -/
noncomputable def or2Rel : BoolRel :=
  BoolRel.ofPredicate 2 fun t => t ⟨0, by decide⟩ ∨ t ⟨1, by decide⟩

/-- The binary negative clause `¬x ∨ ¬y`. -/
noncomputable def nand2Rel : BoolRel :=
  BoolRel.ofPredicate 2 fun t => ¬ (t ⟨0, by decide⟩ ∧ t ⟨1, by decide⟩)

@[simp]
theorem const0Rel_holds_iff (t : BoolTuple 1) :
    const0Rel.Holds t ↔ t ⟨0, by decide⟩ = false :=
  BoolRel.holds_ofPredicate_iff 1 (fun t : BoolTuple 1 => t ⟨0, by decide⟩ = false) t

@[simp]
theorem const1Rel_holds_iff (t : BoolTuple 1) :
    const1Rel.Holds t ↔ t ⟨0, by decide⟩ = true :=
  BoolRel.holds_ofPredicate_iff 1 (fun t : BoolTuple 1 => t ⟨0, by decide⟩ = true) t

@[simp]
theorem diseqRel_holds_iff (t : BoolTuple 2) :
    diseqRel.Holds t ↔ t ⟨0, by decide⟩ ≠ t ⟨1, by decide⟩ :=
  BoolRel.holds_ofPredicate_iff 2 (fun t : BoolTuple 2 => t ⟨0, by decide⟩ ≠ t ⟨1, by decide⟩) t

@[simp]
theorem or2Rel_holds_iff (t : BoolTuple 2) :
    or2Rel.Holds t ↔ t ⟨0, by decide⟩ ∨ t ⟨1, by decide⟩ :=
  BoolRel.holds_ofPredicate_iff 2 (fun t : BoolTuple 2 => t ⟨0, by decide⟩ ∨ t ⟨1, by decide⟩) t

@[simp]
theorem nand2Rel_holds_iff (t : BoolTuple 2) :
    nand2Rel.Holds t ↔ ¬ (t ⟨0, by decide⟩ ∧ t ⟨1, by decide⟩) :=
  BoolRel.holds_ofPredicate_iff 2
    (fun t : BoolTuple 2 => ¬ (t ⟨0, by decide⟩ ∧ t ⟨1, by decide⟩)) t

/-- Γ pp-defines the constant zero. -/
def PPDefinesConst0 (Γ : Gamma) : Prop :=
  PPDefines Γ const0Rel

/-- Γ pp-defines the constant one. -/
def PPDefinesConst1 (Γ : Gamma) : Prop :=
  PPDefines Γ const1Rel

/-- Γ pp-defines both constants. -/
def PPDefinesBothConstants (Γ : Gamma) : Prop :=
  PPDefinesConst0 Γ ∧ PPDefinesConst1 Γ

/-- Γ pp-defines the disequality relation. -/
def PPDefinesDisequality (Γ : Gamma) : Prop :=
  PPDefines Γ diseqRel

/-- Γ pp-defines the positive binary clause. -/
def PPDefinesOr2 (Γ : Gamma) : Prop :=
  PPDefines Γ or2Rel

/-- Γ pp-defines the negative binary clause. -/
def PPDefinesNand2 (Γ : Gamma) : Prop :=
  PPDefines Γ nand2Rel

/-! ### Closure relations among the six classes -/

/-- Majority is expressible from coordinatewise meet and join. -/
theorem majority_eq_join_meet {arity : Nat} (first second third : BooleanTuple arity) :
    BooleanRelation.majority first second third =
      BooleanRelation.join (BooleanRelation.meet first second)
        (BooleanRelation.join (BooleanRelation.meet first third)
          (BooleanRelation.meet second third)) := by
  funext index
  cases h1 : first index <;> cases h2 : second index <;> cases h3 : third index <;>
    simp [BooleanRelation.majority, BooleanRelation.join, BooleanRelation.meet, h1, h2, h3]

/-- A relation closed under meet and join is closed under majority. -/
theorem relation_IsBijunctive_of_IsHorn_and_IsDualHorn (relation : BooleanRelation) :
    relation.IsHorn → relation.IsDualHorn → relation.IsBijunctive := by
  intro horn dualHorn first second third holdsFirst holdsSecond holdsThird
  rw [majority_eq_join_meet]
  exact dualHorn (BooleanRelation.meet first second)
    (BooleanRelation.join (BooleanRelation.meet first third) (BooleanRelation.meet second third))
    (horn first second holdsFirst holdsSecond)
    (dualHorn (BooleanRelation.meet first third) (BooleanRelation.meet second third)
      (horn first third holdsFirst holdsThird)
      (horn second third holdsSecond holdsThird))

/-- A language whose relations are all Horn and dual-Horn is bijunctive. -/
theorem gamma_IsBijunctive_of_IsHorn_and_IsDualHorn (Γ : Gamma) :
    Γ.IsHorn → Γ.IsDualHorn → Γ.IsBijunctive := by
  intro horn dualHorn symbol
  exact relation_IsBijunctive_of_IsHorn_and_IsDualHorn (Γ.relationOf symbol)
    (horn symbol) (dualHorn symbol)

/-- A language missing bijunctivity is missing Horn or missing dual-Horn. -/
theorem gamma_not_IsHorn_or_not_IsDualHorn_of_not_IsBijunctive (Γ : Gamma)
    (h : ¬ Γ.IsBijunctive) :
    ¬ Γ.IsHorn ∨ ¬ Γ.IsDualHorn := by
  by_cases hHorn : Γ.IsHorn
  · by_cases hDual : Γ.IsDualHorn
    · exact False.elim (h (gamma_IsBijunctive_of_IsHorn_and_IsDualHorn Γ hHorn hDual))
    · exact Or.inr hDual
  · exact Or.inl hHorn

/-! ### Constraint gadgets over one tuple -/

/-- One constraint of `R₀` with all coordinates identified to one variable. -/
def identifyAllConstraint (Γ : Gamma) (symbol : Γ.Symbol) (var : Nat) : Constraint Γ where
  symbol := symbol
  vars := fun _ => var

theorem identifyAllConstraint_satisfies_iff (Γ : Gamma) (symbol : Γ.Symbol) (var : Nat)
    (assignment : SAT.Assignment) :
    Constraint.Satisfies (identifyAllConstraint Γ symbol var) assignment ↔
      (Γ.relationOf symbol).Holds (fun _ => assignment var) := by
  unfold Constraint.Satisfies Constraint.assignmentTuple
  rfl

/-- The tuple `t` with `x` at its 1-positions and `y` at its 0-positions. -/
def mixingTuple {k : Nat} (t : BooleanTuple k) (x y : Bool) : BooleanTuple k :=
  fun i => if t i then x else y

@[simp]
theorem mixingTuple_true_false {k : Nat} (t : BooleanTuple k) :
    mixingTuple t true false = t := by
  funext i
  by_cases h : t i = true <;> simp [mixingTuple, h]

@[simp]
theorem mixingTuple_false_false {k : Nat} (t : BooleanTuple k) :
    mixingTuple t false false = fun _ => false := by
  funext i
  by_cases h : t i = true <;> simp [mixingTuple, h]

@[simp]
theorem mixingTuple_true_true {k : Nat} (t : BooleanTuple k) :
    mixingTuple t true true = fun _ => true := by
  funext i
  by_cases h : t i = true <;> simp [mixingTuple, h]

/-- The constraint of `R₀` realizing `t` on the two variables `x`, `y`. -/
def mixingConstraint (Γ : Gamma) (symbol : Γ.Symbol)
    (t : BooleanTuple (Γ.relationOf symbol).arity) (x y : Nat) : Constraint Γ where
  symbol := symbol
  vars := fun i => if t i then x else y

/-- The assignment of a mixed constraint is the mixed tuple of the assignments. -/
theorem mixingConstraint_tuple_eq (Γ : Gamma) (symbol : Γ.Symbol)
    (t : BooleanTuple (Γ.relationOf symbol).arity) (x y : Nat) (assignment : SAT.Assignment) :
    Constraint.assignmentTuple (mixingConstraint Γ symbol t x y) assignment =
      mixingTuple t (assignment x) (assignment y) := by
  funext i
  by_cases h : t i = true <;> simp [Constraint.assignmentTuple, mixingConstraint, mixingTuple, h]

theorem mixingConstraint_satisfies_iff (Γ : Gamma) (symbol : Γ.Symbol)
    (t : BooleanTuple (Γ.relationOf symbol).arity) (x y : Nat) (assignment : SAT.Assignment) :
    Constraint.Satisfies (mixingConstraint Γ symbol t x y) assignment ↔
      (Γ.relationOf symbol).Holds (mixingTuple t (assignment x) (assignment y)) := by
  unfold Constraint.Satisfies
  rw [mixingConstraint_tuple_eq]
  unfold mixingConstraint
  rfl

/-! ### The constants-or-disequality dichotomy -/

/-- Concrete pp-definitions of both constants with canonical pin formulas.

The pin formulas force the keys `2` and `3` to `true` and `false`, and stay
satisfiable under every assignment of the keys `0` and `1`, so they can be
combined with any gadget built over the keys `0, 1` and pinned keys `2, 3`.
-/
structure ConstantCase (Γ : Gamma) where
  /-- The constant-zero relation. -/
  zero : Gadget Γ const0Rel
  /-- The constant-one relation. -/
  one : Gadget Γ const1Rel
  /-- The canonical pin of the key `3` to `false`. -/
  pinZero : CSP.Formula Γ
  /-- The zero-pin forces the key `3`. -/
  pinZero_spec : ∀ assignment : SAT.Assignment,
    CSP.Formula.Satisfies pinZero assignment → assignment 3 = false
  /-- The canonical pin of the key `2` to `true`. -/
  pinOne : CSP.Formula Γ
  /-- The one-pin forces the key `2`. -/
  pinOne_spec : ∀ assignment : SAT.Assignment,
    CSP.Formula.Satisfies pinOne assignment → assignment 2 = true
  /-- The pins stay satisfiable under every value of the gadget keys `0` and `1`. -/
  pins_satisfiable : ∀ (first second : Bool),
    ∃ assignment : SAT.Assignment,
      assignment 0 = first ∧ assignment 1 = second ∧
        CSP.Formula.Satisfies pinZero assignment ∧ CSP.Formula.Satisfies pinOne assignment

/-- The constant-one gadget from a non-0-valid relation containing the all-one tuple. -/
noncomputable def const1Gadget_of_allOne (Γ : Gamma) (symbol : Γ.Symbol)
    (notZero : ¬ (Γ.relationOf symbol).Holds (fun _ => false))
    (allOne : (Γ.relationOf symbol).Holds (fun _ => true)) : Gadget Γ const1Rel where
  formula := [identifyAllConstraint Γ symbol 0]
  outputs := fun _ => 0
  outputs_injective := by
    intro i j equality
    fin_cases i <;> fin_cases j <;> rfl
  correct := by
    intro tuple
    constructor
    · intro holds
      refine ⟨fun _ => true, ?_, ?_⟩
      · intro constraint constraintMember
        rcases List.mem_cons.mp constraintMember with rfl | hEmpty
        · exact allOne
        · cases hEmpty
      · intro i
        fin_cases i
        exact ((const1Rel_holds_iff tuple).1 holds).symm
    · rintro ⟨assignment, ⟨satisfies, outputs⟩⟩
      have htuple : (Γ.relationOf symbol).Holds (fun _ => assignment 0) := by
        exact (identifyAllConstraint_satisfies_iff Γ symbol 0 assignment).1
          (satisfies (identifyAllConstraint Γ symbol 0) (by simp))
      have hval : assignment 0 = true := by
        by_cases h : assignment 0 = false
        · exfalso
          exact notZero (by simpa [h] using htuple)
        · cases hBool : assignment 0
          · exact False.elim (h hBool)
          · rfl
      have hout := outputs ⟨0, by decide⟩
      exact (const1Rel_holds_iff tuple).2 (hout.symm.trans hval)

/-- The constant-zero gadget from a non-1-valid relation containing the all-zero tuple. -/
noncomputable def const0Gadget_of_allZero (Γ : Gamma) (symbol : Γ.Symbol)
    (notOne : ¬ (Γ.relationOf symbol).Holds (fun _ => true))
    (allZero : (Γ.relationOf symbol).Holds (fun _ => false)) : Gadget Γ const0Rel where
  formula := [identifyAllConstraint Γ symbol 0]
  outputs := fun _ => 0
  outputs_injective := by
    intro i j equality
    fin_cases i <;> fin_cases j <;> rfl
  correct := by
    intro tuple
    constructor
    · intro holds
      refine ⟨fun _ => false, ?_, ?_⟩
      · intro constraint constraintMember
        rcases List.mem_cons.mp constraintMember with rfl | hEmpty
        · exact allZero
        · cases hEmpty
      · intro i
        fin_cases i
        exact ((const0Rel_holds_iff tuple).1 holds).symm
    · rintro ⟨assignment, ⟨satisfies, outputs⟩⟩
      have htuple : (Γ.relationOf symbol).Holds (fun _ => assignment 0) := by
        exact (identifyAllConstraint_satisfies_iff Γ symbol 0 assignment).1
          (satisfies (identifyAllConstraint Γ symbol 0) (by simp))
      have hval : assignment 0 = false := by
        by_cases h : assignment 0 = true
        · exfalso
          exact notOne (by simpa [h] using htuple)
        · cases hBool : assignment 0
          · rfl
          · exact False.elim (h hBool)
      have hout := outputs ⟨0, by decide⟩
      exact (const0Rel_holds_iff tuple).2 (hout.symm.trans hval)

/-- The disequality gadget from one tuple `t` whose four mixed corners are known.

The four corners are: `t` accepted, `(0,0)` and `(1,1)` rejected, and the
swapped tuple accepted.  The constraint `R₀(x at t's 1-positions, y at t's
0-positions)` then realizes `x ≠ y`.
-/
noncomputable def diseqGadget_of_mixing (Γ : Gamma) (symbol : Γ.Symbol)
    (t : BooleanTuple (Γ.relationOf symbol).arity)
    (notZero : ¬ (Γ.relationOf symbol).Holds (fun _ => false))
    (notOne : ¬ (Γ.relationOf symbol).Holds (fun _ => true))
    (oneZero : (Γ.relationOf symbol).Holds (mixingTuple t true false))
    (zeroOne : (Γ.relationOf symbol).Holds (mixingTuple t false true)) : Gadget Γ diseqRel where
  formula := [mixingConstraint Γ symbol t 0 1]
  outputs := fun
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
  outputs_injective := by
    intro i j equality
    fin_cases i <;> fin_cases j <;> simp at equality ⊢
  correct := by
    intro tuple
    constructor
    · intro holds
      have hneq : tuple ⟨0, by decide⟩ ≠ tuple ⟨1, by decide⟩ :=
        (diseqRel_holds_iff tuple).1 holds
      refine ⟨fun var => if var = 0 then tuple ⟨0, by decide⟩
        else if var = 1 then tuple ⟨1, by decide⟩ else false, ?_, ?_⟩
      · intro constraint constraintMember
        rcases List.mem_cons.mp constraintMember with rfl | hEmpty
        · rw [mixingConstraint_satisfies_iff]
          cases h0 : tuple ⟨0, by decide⟩ <;> cases h1 : tuple ⟨1, by decide⟩
          · exact False.elim (hneq (by simp [h0, h1]))
          · simpa [h0, h1, mixingTuple] using zeroOne
          · simpa [h0, h1, mixingTuple] using oneZero
          · exact False.elim (hneq (by simp [h0, h1]))
        · cases hEmpty
      · intro i
        fin_cases i <;> rfl
    · rintro ⟨assignment, ⟨satisfies, outputs⟩⟩
      have htuple : (Γ.relationOf symbol).Holds
          (mixingTuple t (assignment 0) (assignment 1)) := by
        exact (mixingConstraint_satisfies_iff Γ symbol t 0 1 assignment).1
          (satisfies (mixingConstraint Γ symbol t 0 1) (by simp))
      have hOut0 : tuple ⟨0, by decide⟩ = assignment 0 := (outputs ⟨0, by decide⟩).symm
      have hOut1 : tuple ⟨1, by decide⟩ = assignment 1 := (outputs ⟨1, by decide⟩).symm
      cases hBool0 : assignment 0 <;> cases hBool1 : assignment 1
      · exfalso
        exact notZero (by simpa [hBool0, hBool1, mixingTuple] using htuple)
      · exact (diseqRel_holds_iff tuple).2 (by
          intro hEq
          have hAsgn : assignment 0 = assignment 1 := hOut0.symm.trans (hEq.trans hOut1)
          exact Bool.false_ne_true ((hBool0.symm.trans hAsgn).trans hBool1))
      · exact (diseqRel_holds_iff tuple).2 (by
          intro hEq
          have hAsgn : assignment 0 = assignment 1 := hOut0.symm.trans (hEq.trans hOut1)
          exact Bool.false_ne_true ((hBool0.symm.trans hAsgn).trans hBool1).symm)
      · exfalso
        exact notOne (by simpa [hBool0, hBool1, mixingTuple] using htuple)

/-- The constant-one gadget from the projection `{x : ∃ y, R₀(x at t's 1-positions, y at t's 0-positions)}`. -/
noncomputable def const1Gadget_of_mixing (Γ : Gamma) (symbol : Γ.Symbol)
    (t : BooleanTuple (Γ.relationOf symbol).arity)
    (notZero : ¬ (Γ.relationOf symbol).Holds (fun _ => false))
    (notOne : ¬ (Γ.relationOf symbol).Holds (fun _ => true))
    (oneZero : (Γ.relationOf symbol).Holds (mixingTuple t true false))
    (notZeroOne : ¬ (Γ.relationOf symbol).Holds (mixingTuple t false true)) : Gadget Γ const1Rel where
  formula := [mixingConstraint Γ symbol t 0 1]
  outputs := fun _ => 0
  outputs_injective := by
    intro i j equality
    fin_cases i <;> fin_cases j <;> rfl
  correct := by
    intro tuple
    constructor
    · intro holds
      refine ⟨fun var => if var = 0 then true else false, ?_, ?_⟩
      · intro constraint constraintMember
        rcases List.mem_cons.mp constraintMember with rfl | hEmpty
        · rw [mixingConstraint_satisfies_iff]
          simpa [mixingTuple] using oneZero
        · cases hEmpty
      · intro i
        fin_cases i
        exact ((const1Rel_holds_iff tuple).1 holds).symm
    · rintro ⟨assignment, ⟨satisfies, outputs⟩⟩
      have htuple : (Γ.relationOf symbol).Holds
          (mixingTuple t (assignment 0) (assignment 1)) := by
        exact (mixingConstraint_satisfies_iff Γ symbol t 0 1 assignment).1
          (satisfies (mixingConstraint Γ symbol t 0 1) (by simp))
      have hval : assignment 0 = true := by
        by_cases h0 : assignment 0 = false
        · exfalso
          cases h1 : assignment 1 <;> simp [h0, h1, mixingTuple] at htuple
          · exact notZero htuple
          · exact notZeroOne htuple
        · cases hBool : assignment 0
          · exact False.elim (h0 hBool)
          · rfl
      have hout := outputs ⟨0, by decide⟩
      exact (const1Rel_holds_iff tuple).2 (hout.symm.trans hval)

/-- The constant-zero gadget from the projection `{y : ∃ x, R₀(x at t's 1-positions, y at t's 0-positions)}`. -/
noncomputable def const0Gadget_of_mixing (Γ : Gamma) (symbol : Γ.Symbol)
    (t : BooleanTuple (Γ.relationOf symbol).arity)
    (notZero : ¬ (Γ.relationOf symbol).Holds (fun _ => false))
    (notOne : ¬ (Γ.relationOf symbol).Holds (fun _ => true))
    (oneZero : (Γ.relationOf symbol).Holds (mixingTuple t true false))
    (notZeroOne : ¬ (Γ.relationOf symbol).Holds (mixingTuple t false true)) : Gadget Γ const0Rel where
  formula := [mixingConstraint Γ symbol t 0 1]
  outputs := fun _ => 1
  outputs_injective := by
    intro i j equality
    fin_cases i <;> fin_cases j <;> rfl
  correct := by
    intro tuple
    constructor
    · intro holds
      refine ⟨fun var => if var = 0 then true else false, ?_, ?_⟩
      · intro constraint constraintMember
        rcases List.mem_cons.mp constraintMember with rfl | hEmpty
        · rw [mixingConstraint_satisfies_iff]
          simpa [mixingTuple] using oneZero
        · cases hEmpty
      · intro i
        fin_cases i
        exact ((const0Rel_holds_iff tuple).1 holds).symm
    · rintro ⟨assignment, ⟨satisfies, outputs⟩⟩
      have htuple : (Γ.relationOf symbol).Holds
          (mixingTuple t (assignment 0) (assignment 1)) := by
        exact (mixingConstraint_satisfies_iff Γ symbol t 0 1 assignment).1
          (satisfies (mixingConstraint Γ symbol t 0 1) (by simp))
      have hval : assignment 1 = false := by
        by_cases h1 : assignment 1 = true
        · exfalso
          cases h0 : assignment 0 <;> simp [h0, h1, mixingTuple] at htuple
          · exact notZeroOne htuple
          · exact notOne htuple
        · cases hBool : assignment 1
          · rfl
          · exact False.elim (h1 hBool)
      have hout := outputs ⟨0, by decide⟩
      exact (const0Rel_holds_iff tuple).2 (hout.symm.trans hval)

/-! ### The swapped mixing gadget -/

/-- The tuple `t` with `y` at its 1-positions and `x` at its 0-positions. -/
def swappedMixingTuple {k : Nat} (t : BooleanTuple k) (x y : Bool) : BooleanTuple k :=
  fun i => if t i then y else x

@[simp]
theorem swappedMixingTuple_false_true {k : Nat} (t : BooleanTuple k) :
    swappedMixingTuple t false true = t := by
  funext i
  by_cases h : t i = true <;> simp [swappedMixingTuple, h]

@[simp]
theorem swappedMixingTuple_false_false {k : Nat} (t : BooleanTuple k) :
    swappedMixingTuple t false false = fun _ => false := by
  funext i
  by_cases h : t i = true <;> simp [swappedMixingTuple, h]

@[simp]
theorem swappedMixingTuple_true_true {k : Nat} (t : BooleanTuple k) :
    swappedMixingTuple t true true = fun _ => true := by
  funext i
  by_cases h : t i = true <;> simp [swappedMixingTuple, h]

/-- The swapped constraint of `R₀` realizing `t` on the two variables `x`, `y`. -/
def swappedMixingConstraint (Γ : Gamma) (symbol : Γ.Symbol)
    (t : BooleanTuple (Γ.relationOf symbol).arity) (x y : Nat) : Constraint Γ where
  symbol := symbol
  vars := fun i => if t i then y else x

/-- The assignment of a swapped mixed constraint is the swapped mixed tuple of the assignments. -/
theorem swappedMixingConstraint_tuple_eq (Γ : Gamma) (symbol : Γ.Symbol)
    (t : BooleanTuple (Γ.relationOf symbol).arity) (x y : Nat) (assignment : SAT.Assignment) :
    Constraint.assignmentTuple (swappedMixingConstraint Γ symbol t x y) assignment =
      swappedMixingTuple t (assignment x) (assignment y) := by
  funext i
  by_cases h : t i = true <;> simp [Constraint.assignmentTuple, swappedMixingConstraint, swappedMixingTuple, h]

theorem swappedMixingConstraint_satisfies_iff (Γ : Gamma) (symbol : Γ.Symbol)
    (t : BooleanTuple (Γ.relationOf symbol).arity) (x y : Nat) (assignment : SAT.Assignment) :
    Constraint.Satisfies (swappedMixingConstraint Γ symbol t x y) assignment ↔
      (Γ.relationOf symbol).Holds (swappedMixingTuple t (assignment x) (assignment y)) := by
  unfold Constraint.Satisfies
  rw [swappedMixingConstraint_tuple_eq]
  unfold swappedMixingConstraint
  rfl

/-- The disequality gadget from one tuple `t` of a non-1-valid relation whose
swapped tuple is also accepted. -/
noncomputable def diseqGadget_of_swappedMixing (Γ : Gamma) (symbol : Γ.Symbol)
    (t : BooleanTuple (Γ.relationOf symbol).arity)
    (notZero : ¬ (Γ.relationOf symbol).Holds (fun _ => false))
    (notOne : ¬ (Γ.relationOf symbol).Holds (fun _ => true))
    (zeroOne : (Γ.relationOf symbol).Holds (swappedMixingTuple t false true))
    (oneZero : (Γ.relationOf symbol).Holds (swappedMixingTuple t true false)) : Gadget Γ diseqRel where
  formula := [swappedMixingConstraint Γ symbol t 0 1]
  outputs := fun
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
  outputs_injective := by
    intro i j equality
    fin_cases i <;> fin_cases j <;> simp at equality ⊢
  correct := by
    intro tuple
    constructor
    · intro holds
      have hneq : tuple ⟨0, by decide⟩ ≠ tuple ⟨1, by decide⟩ :=
        (diseqRel_holds_iff tuple).1 holds
      refine ⟨fun var => if var = 0 then tuple ⟨0, by decide⟩
        else if var = 1 then tuple ⟨1, by decide⟩ else false, ?_, ?_⟩
      · intro constraint constraintMember
        rcases List.mem_cons.mp constraintMember with rfl | hEmpty
        · rw [swappedMixingConstraint_satisfies_iff]
          cases h0 : tuple ⟨0, by decide⟩ <;> cases h1 : tuple ⟨1, by decide⟩
          · exact False.elim (hneq (by simp [h0, h1]))
          · simpa [h0, h1, swappedMixingTuple] using zeroOne
          · simpa [h0, h1, swappedMixingTuple] using oneZero
          · exact False.elim (hneq (by simp [h0, h1]))
        · cases hEmpty
      · intro i
        fin_cases i <;> rfl
    · rintro ⟨assignment, ⟨satisfies, outputs⟩⟩
      have htuple : (Γ.relationOf symbol).Holds
          (swappedMixingTuple t (assignment 0) (assignment 1)) := by
        exact (swappedMixingConstraint_satisfies_iff Γ symbol t 0 1 assignment).1
          (satisfies (swappedMixingConstraint Γ symbol t 0 1) (by simp))
      have hOut0 : tuple ⟨0, by decide⟩ = assignment 0 := (outputs ⟨0, by decide⟩).symm
      have hOut1 : tuple ⟨1, by decide⟩ = assignment 1 := (outputs ⟨1, by decide⟩).symm
      cases hBool0 : assignment 0 <;> cases hBool1 : assignment 1
      · exfalso
        exact notZero (by simpa [hBool0, hBool1, swappedMixingTuple] using htuple)
      · exact (diseqRel_holds_iff tuple).2 (by
          intro hEq
          have hAsgn : assignment 0 = assignment 1 := hOut0.symm.trans (hEq.trans hOut1)
          exact Bool.false_ne_true ((hBool0.symm.trans hAsgn).trans hBool1))
      · exact (diseqRel_holds_iff tuple).2 (by
          intro hEq
          have hAsgn : assignment 0 = assignment 1 := hOut0.symm.trans (hEq.trans hOut1)
          exact Bool.false_ne_true ((hBool0.symm.trans hAsgn).trans hBool1).symm)
      · exfalso
        exact notOne (by simpa [hBool0, hBool1, swappedMixingTuple] using htuple)

/-- The constant-zero gadget from the projection `{x : ∃ y, S₀(y at t's 1-positions, x at t's 0-positions)}`
when the swapped tuple is rejected. -/
noncomputable def const0Gadget_of_swappedMixing (Γ : Gamma) (symbol : Γ.Symbol)
    (t : BooleanTuple (Γ.relationOf symbol).arity)
    (notZero : ¬ (Γ.relationOf symbol).Holds (fun _ => false))
    (notOne : ¬ (Γ.relationOf symbol).Holds (fun _ => true))
    (zeroOne : (Γ.relationOf symbol).Holds (swappedMixingTuple t false true))
    (notOneZero : ¬ (Γ.relationOf symbol).Holds (swappedMixingTuple t true false)) : Gadget Γ const0Rel where
  formula := [swappedMixingConstraint Γ symbol t 0 1]
  outputs := fun _ => 0
  outputs_injective := by
    intro i j equality
    fin_cases i <;> fin_cases j <;> rfl
  correct := by
    intro tuple
    constructor
    · intro holds
      refine ⟨fun var => if var = 0 then false else true, ?_, ?_⟩
      · intro constraint constraintMember
        rcases List.mem_cons.mp constraintMember with rfl | hEmpty
        · rw [swappedMixingConstraint_satisfies_iff]
          simpa [swappedMixingTuple] using zeroOne
        · cases hEmpty
      · intro i
        fin_cases i
        exact ((const0Rel_holds_iff tuple).1 holds).symm
    · rintro ⟨assignment, ⟨satisfies, outputs⟩⟩
      have htuple : (Γ.relationOf symbol).Holds
          (swappedMixingTuple t (assignment 0) (assignment 1)) := by
        exact (swappedMixingConstraint_satisfies_iff Γ symbol t 0 1 assignment).1
          (satisfies (swappedMixingConstraint Γ symbol t 0 1) (by simp))
      have hval : assignment 0 = false := by
        by_cases h0 : assignment 0 = true
        · exfalso
          cases h1 : assignment 1 <;> simp [h0, h1, swappedMixingTuple] at htuple
          · exact notOneZero htuple
          · exact notOne htuple
        · cases hBool : assignment 0
          · rfl
          · exact False.elim (h0 hBool)
      have hout := outputs ⟨0, by decide⟩
      exact (const0Rel_holds_iff tuple).2 (hout.symm.trans hval)

/-- The constant-one gadget from the projection `{y : ∃ x, S₀(y at t's 1-positions, x at t's 0-positions)}`
when the swapped tuple is rejected. -/
noncomputable def const1Gadget_of_swappedMixing (Γ : Gamma) (symbol : Γ.Symbol)
    (t : BooleanTuple (Γ.relationOf symbol).arity)
    (notZero : ¬ (Γ.relationOf symbol).Holds (fun _ => false))
    (notOne : ¬ (Γ.relationOf symbol).Holds (fun _ => true))
    (zeroOne : (Γ.relationOf symbol).Holds (swappedMixingTuple t false true))
    (notOneZero : ¬ (Γ.relationOf symbol).Holds (swappedMixingTuple t true false)) : Gadget Γ const1Rel where
  formula := [swappedMixingConstraint Γ symbol t 0 1]
  outputs := fun _ => 1
  outputs_injective := by
    intro i j equality
    fin_cases i <;> fin_cases j <;> rfl
  correct := by
    intro tuple
    constructor
    · intro holds
      refine ⟨fun var => if var = 1 then true else false, ?_, ?_⟩
      · intro constraint constraintMember
        rcases List.mem_cons.mp constraintMember with rfl | hEmpty
        · rw [swappedMixingConstraint_satisfies_iff]
          simpa [swappedMixingTuple] using zeroOne
        · cases hEmpty
      · intro i
        fin_cases i
        exact ((const1Rel_holds_iff tuple).1 holds).symm
    · rintro ⟨assignment, ⟨satisfies, outputs⟩⟩
      have htuple : (Γ.relationOf symbol).Holds
          (swappedMixingTuple t (assignment 0) (assignment 1)) := by
        exact (swappedMixingConstraint_satisfies_iff Γ symbol t 0 1 assignment).1
          (satisfies (swappedMixingConstraint Γ symbol t 0 1) (by simp))
      have hval : assignment 1 = true := by
        by_cases h1 : assignment 1 = false
        · exfalso
          cases h0 : assignment 0 <;> simp [h0, h1, swappedMixingTuple] at htuple
          · exact notZero htuple
          · exact notOneZero htuple
        · cases hBool : assignment 1
          · exact False.elim (h1 hBool)
          · rfl
      have hout := outputs ⟨0, by decide⟩
      exact (const1Rel_holds_iff tuple).2 (hout.symm.trans hval)

/-- The constant-zero gadget combining the disequality of `S₀` with the
constant-one pin of `R₀`: `x = 0 ⟺ ∃ w, w = 1 ∧ x ≠ w`. -/
noncomputable def const0Gadget_of_diseq_and_pinOne (Γ : Gamma)
    (sZero : Γ.Symbol)
    (notZero : ¬ (Γ.relationOf sZero).Holds (fun _ => false))
    (allOne : (Γ.relationOf sZero).Holds (fun _ => true))
    (sOne : Γ.Symbol)
    (tOne : BooleanTuple (Γ.relationOf sOne).arity)
    (notZeroIn : ¬ (Γ.relationOf sOne).Holds (fun _ => false))
    (notOne : ¬ (Γ.relationOf sOne).Holds (fun _ => true))
    (zeroOne : (Γ.relationOf sOne).Holds (swappedMixingTuple tOne false true)) : Gadget Γ const0Rel where
  formula := [swappedMixingConstraint Γ sOne tOne 0 1, identifyAllConstraint Γ sZero 1]
  outputs := fun _ => 0
  outputs_injective := by
    intro i j equality
    fin_cases i <;> fin_cases j <;> rfl
  correct := by
    intro tuple
    constructor
    · intro holds
      refine ⟨fun var => if var = 0 then false else if var = 1 then true else false, ?_, ?_⟩
      · intro constraint constraintMember
        rcases List.mem_cons.mp constraintMember with rfl | h'
        · rw [swappedMixingConstraint_satisfies_iff]
          simpa [swappedMixingTuple] using zeroOne
        · rcases List.mem_cons.mp h' with rfl | hEmpty
          · exact allOne
          · cases hEmpty
      · intro i
        fin_cases i
        exact ((const0Rel_holds_iff tuple).1 holds).symm
    · rintro ⟨assignment, ⟨satisfies, outputs⟩⟩
      have hw : assignment 1 = true := by
        by_cases h : assignment 1 = false
        · exfalso
          have hpin : (Γ.relationOf sZero).Holds (fun _ => assignment 1) := by
            exact (identifyAllConstraint_satisfies_iff Γ sZero 1 assignment).1
              (satisfies (identifyAllConstraint Γ sZero 1) (by simp))
          exact notZero (by simpa [h] using hpin)
        · cases hBool : assignment 1
          · exact False.elim (h hBool)
          · rfl
      have hmix : (Γ.relationOf sOne).Holds
          (swappedMixingTuple tOne (assignment 0) (assignment 1)) := by
        exact (swappedMixingConstraint_satisfies_iff Γ sOne tOne 0 1 assignment).1
          (satisfies (swappedMixingConstraint Γ sOne tOne 0 1) (by simp))
      have hval : assignment 0 = false := by
        by_cases h0 : assignment 0 = true
        · exfalso
          exact notOne (by simpa [h0, hw, swappedMixingTuple] using hmix)
        · cases hBool : assignment 0
          · rfl
          · exact False.elim (h0 hBool)
      have hout := outputs ⟨0, by decide⟩
      exact (const0Rel_holds_iff tuple).2 (hout.symm.trans hval)

/-! ### The dichotomy theorem -/

/-- A non-0-valid language has a relation rejecting the all-zero tuple. -/
theorem exists_not_zeroValid (Γ : Gamma) (h : ¬ Γ.IsZeroValid) :
    ∃ symbol : Γ.Symbol, ¬ (Γ.relationOf symbol).Holds (fun _ => false) := by
  classical
  by_contra h'
  apply h
  intro symbol
  by_cases hHolds : (Γ.relationOf symbol).Holds (fun _ => false)
  · exact hHolds
  · exact False.elim (h' ⟨symbol, hHolds⟩)

/-- A non-1-valid language has a relation rejecting the all-one tuple. -/
theorem exists_not_oneValid (Γ : Gamma) (h : ¬ Γ.IsOneValid) :
    ∃ symbol : Γ.Symbol, ¬ (Γ.relationOf symbol).Holds (fun _ => true) := by
  classical
  by_contra h'
  apply h
  intro symbol
  by_cases hHolds : (Γ.relationOf symbol).Holds (fun _ => true)
  · exact hHolds
  · exact False.elim (h' ⟨symbol, hHolds⟩)

/-- The constants-or-disequality dichotomy.

A language that is neither 0-valid nor 1-valid (with only nonempty relations)
pp-defines both constants, together with their canonical pin formulas, or the
disequality relation.
-/
theorem constantsCase_or_disequality_of_not_zero_one_valid (Γ : Gamma)
    (nonempty : ∀ symbol : Γ.Symbol, (Γ.relationOf symbol).Nonempty)
    (notZeroValid : ¬ Γ.IsZeroValid) (notOneValid : ¬ Γ.IsOneValid) :
    Nonempty (ConstantCase Γ) ∨ PPDefinesDisequality Γ := by
  rcases exists_not_zeroValid Γ notZeroValid with ⟨sZero, hZero⟩
  rcases exists_not_oneValid Γ notOneValid with ⟨sOne, hOne⟩
  rcases nonempty sZero with ⟨tZero, htZero⟩
  by_cases hAllOne : (Γ.relationOf sZero).Holds (fun _ => true)
  · have const1 : Gadget Γ const1Rel := const1Gadget_of_allOne Γ sZero hZero hAllOne
    by_cases hZeroIn : (Γ.relationOf sOne).Holds (fun _ => false)
    · refine Or.inl ⟨const0Gadget_of_allZero Γ sOne hOne hZeroIn, const1,
        [identifyAllConstraint Γ sOne 3], ?_, [identifyAllConstraint Γ sZero 2], ?_, ?_⟩
      · intro assignment pinSatisfies
        have htuple : (Γ.relationOf sOne).Holds (fun _ => assignment 3) := by
          exact (identifyAllConstraint_satisfies_iff Γ sOne 3 assignment).1
            (pinSatisfies (identifyAllConstraint Γ sOne 3) (by simp))
        by_cases h : assignment 3 = true
        · exfalso
          exact hOne (by simpa [h] using htuple)
        · cases hBool : assignment 3
          · rfl
          · exact False.elim (h hBool)
      · intro assignment pinSatisfies
        have htuple : (Γ.relationOf sZero).Holds (fun _ => assignment 2) := by
          exact (identifyAllConstraint_satisfies_iff Γ sZero 2 assignment).1
            (pinSatisfies (identifyAllConstraint Γ sZero 2) (by simp))
        by_cases h : assignment 2 = false
        · exfalso
          exact hZero (by simpa [h] using htuple)
        · cases hBool : assignment 2
          · exact False.elim (h hBool)
          · rfl
      · intro first second
        refine ⟨fun var =>
          if var = 0 then first else if var = 1 then second else
            if var = 3 then false else if var = 2 then true else false, ?_, ?_, ?_, ?_⟩
        · simp
        · simp
        · intro constraint constraintMember
          rcases List.mem_singleton.mp constraintMember with rfl
          rw [identifyAllConstraint_satisfies_iff]
          simpa using hZeroIn
        · intro constraint constraintMember
          rcases List.mem_singleton.mp constraintMember with rfl
          rw [identifyAllConstraint_satisfies_iff]
          simpa using hAllOne
    · rcases nonempty sOne with ⟨tOne, htOne⟩
      by_cases hOneZero : (Γ.relationOf sOne).Holds (swappedMixingTuple tOne true false)
      · refine Or.inl ⟨const0Gadget_of_diseq_and_pinOne Γ sZero hZero hAllOne sOne tOne
          hZeroIn hOne (by simpa [swappedMixingTuple] using htOne), const1,
          [swappedMixingConstraint Γ sOne tOne 3 4, identifyAllConstraint Γ sZero 4], ?_,
          [identifyAllConstraint Γ sZero 2], ?_, ?_⟩
        · intro assignment pinSatisfies
          have hw : assignment 4 = true := by
            by_cases h : assignment 4 = false
            · exfalso
              have hpin : (Γ.relationOf sZero).Holds (fun _ => assignment 4) := by
                exact (identifyAllConstraint_satisfies_iff Γ sZero 4 assignment).1
                  (pinSatisfies (identifyAllConstraint Γ sZero 4) (by simp))
              exact hZero (by simpa [h] using hpin)
            · cases hBool : assignment 4
              · exact False.elim (h hBool)
              · rfl
          have hmix : (Γ.relationOf sOne).Holds
              (swappedMixingTuple tOne (assignment 3) (assignment 4)) := by
            exact (swappedMixingConstraint_satisfies_iff Γ sOne tOne 3 4 assignment).1
              (pinSatisfies (swappedMixingConstraint Γ sOne tOne 3 4) (by simp))
          by_cases h3 : assignment 3 = true
          · exfalso
            exact hOne (by simpa [h3, hw, swappedMixingTuple] using hmix)
          · cases hBool : assignment 3
            · rfl
            · exact False.elim (h3 hBool)
        · intro assignment pinSatisfies
          have htuple : (Γ.relationOf sZero).Holds (fun _ => assignment 2) := by
            exact (identifyAllConstraint_satisfies_iff Γ sZero 2 assignment).1
              (pinSatisfies (identifyAllConstraint Γ sZero 2) (by simp))
          by_cases h : assignment 2 = false
          · exfalso
            exact hZero (by simpa [h] using htuple)
          · cases hBool : assignment 2
            · exact False.elim (h hBool)
            · rfl
        · intro first second
          refine ⟨fun var =>
            if var = 0 then first else if var = 1 then second else
              if var = 3 then false else if var = 4 then true else
                if var = 2 then true else false, ?_, ?_, ?_, ?_⟩
          · simp
          · simp
          · intro constraint constraintMember
            rcases List.mem_cons.mp constraintMember with rfl | h'
            · rw [swappedMixingConstraint_satisfies_iff]
              simpa using htOne
            · rcases List.mem_singleton.mp h' with rfl
              rw [identifyAllConstraint_satisfies_iff]
              simpa using hAllOne
          · intro constraint constraintMember
            rcases List.mem_singleton.mp constraintMember with rfl
            rw [identifyAllConstraint_satisfies_iff]
            simpa using hAllOne
      · refine Or.inl ⟨const0Gadget_of_swappedMixing Γ sOne tOne hZeroIn hOne
          (by simpa using htOne) (fun h => hOneZero h),
          const1Gadget_of_swappedMixing Γ sOne tOne hZeroIn hOne
          (by simpa using htOne) (fun h => hOneZero h),
          [swappedMixingConstraint Γ sOne tOne 3 4], ?_,
          [identifyAllConstraint Γ sZero 2], ?_, ?_⟩
        · intro assignment pinSatisfies
          have hmix : (Γ.relationOf sOne).Holds
              (swappedMixingTuple tOne (assignment 3) (assignment 4)) := by
            exact (swappedMixingConstraint_satisfies_iff Γ sOne tOne 3 4 assignment).1
              (pinSatisfies (swappedMixingConstraint Γ sOne tOne 3 4) (by simp))
          by_cases h3 : assignment 3 = true
          · exfalso
            cases h4 : assignment 4 <;> simp [h3, h4, swappedMixingTuple] at hmix
            · exact hOneZero hmix
            · exact hOne hmix
          · cases hBool : assignment 3
            · rfl
            · exact False.elim (h3 hBool)
        · intro assignment pinSatisfies
          have htuple : (Γ.relationOf sZero).Holds (fun _ => assignment 2) := by
            exact (identifyAllConstraint_satisfies_iff Γ sZero 2 assignment).1
              (pinSatisfies (identifyAllConstraint Γ sZero 2) (by simp))
          by_cases h : assignment 2 = false
          · exfalso
            exact hZero (by simpa [h] using htuple)
          · cases hBool : assignment 2
            · exact False.elim (h hBool)
            · rfl
        · intro first second
          refine ⟨fun var =>
            if var = 0 then first else if var = 1 then second else
              if var = 4 then true else if var = 3 then false else
                if var = 2 then true else false, ?_, ?_, ?_, ?_⟩
          · simp
          · simp
          · intro constraint constraintMember
            rcases List.mem_singleton.mp constraintMember with rfl
            rw [swappedMixingConstraint_satisfies_iff]
            simpa using htOne
          · intro constraint constraintMember
            rcases List.mem_singleton.mp constraintMember with rfl
            rw [identifyAllConstraint_satisfies_iff]
            simpa using hAllOne
  · by_cases hZeroOne : (Γ.relationOf sZero).Holds (mixingTuple tZero false true)
    · exact Or.inr ⟨diseqGadget_of_mixing Γ sZero tZero hZero (fun h => hAllOne h) (by simpa using htZero) hZeroOne⟩
    · refine Or.inl ⟨const0Gadget_of_mixing Γ sZero tZero hZero (fun h => hAllOne h)
        (by simpa using htZero) (fun h => hZeroOne h),
        const1Gadget_of_mixing Γ sZero tZero hZero (fun h => hAllOne h)
        (by simpa using htZero) (fun h => hZeroOne h),
        [mixingConstraint Γ sZero tZero 4 3], ?_,
        [mixingConstraint Γ sZero tZero 2 5], ?_, ?_⟩
      · intro assignment pinSatisfies
        have hmix : (Γ.relationOf sZero).Holds
            (mixingTuple tZero (assignment 4) (assignment 3)) := by
          exact (mixingConstraint_satisfies_iff Γ sZero tZero 4 3 assignment).1
            (pinSatisfies (mixingConstraint Γ sZero tZero 4 3) (by simp))
        by_cases h3 : assignment 3 = true
        · exfalso
          cases h4 : assignment 4 <;> simp [h3, h4, mixingTuple] at hmix
          · exact hZeroOne hmix
          · exact hAllOne hmix
        · cases hBool : assignment 3
          · rfl
          · exact False.elim (h3 hBool)
      · intro assignment pinSatisfies
        have hmix : (Γ.relationOf sZero).Holds
            (mixingTuple tZero (assignment 2) (assignment 5)) := by
          exact (mixingConstraint_satisfies_iff Γ sZero tZero 2 5 assignment).1
            (pinSatisfies (mixingConstraint Γ sZero tZero 2 5) (by simp))
        by_cases h2 : assignment 2 = false
        · exfalso
          cases h5 : assignment 5 <;> simp [h2, h5, mixingTuple] at hmix
          · exact hZero hmix
          · exact hZeroOne hmix
        · cases hBool : assignment 2
          · exact False.elim (h2 hBool)
          · rfl
      · intro first second
        refine ⟨fun var =>
          if var = 0 then first else if var = 1 then second else
            if var = 4 then true else if var = 3 then false else
              if var = 5 then false else if var = 2 then true else false, ?_, ?_, ?_, ?_⟩
        · simp
        · simp
        · intro constraint constraintMember
          rcases List.mem_singleton.mp constraintMember with rfl
          rw [mixingConstraint_satisfies_iff]
          simpa using htZero
        · intro constraint constraintMember
          rcases List.mem_singleton.mp constraintMember with rfl
          rw [mixingConstraint_satisfies_iff]
          simpa using htZero

/-- The classical constants-or-disequality statement of the case analysis. -/
theorem ppDefines_constants_or_disequality_of_not_zero_one_valid (Γ : Gamma)
    (nonempty : ∀ symbol : Γ.Symbol, (Γ.relationOf symbol).Nonempty)
    (notZeroValid : ¬ Γ.IsZeroValid) (notOneValid : ¬ Γ.IsOneValid) :
    PPDefinesBothConstants Γ ∨ PPDefinesDisequality Γ := by
  rcases constantsCase_or_disequality_of_not_zero_one_valid Γ nonempty notZeroValid notOneValid
    with hCase | hDiseq
  · rcases hCase with ⟨constants⟩
    exact Or.inl ⟨⟨constants.zero⟩, ⟨constants.one⟩⟩
  · exact Or.inr hDiseq

/-! ### The Horn and dual-Horn gadgets -/

/-- The pair-failure constraint of `R₀` on the variables `x`, `y` and the pins `2`, `3`.

`x` sits on the positions where `a` has `1` and `b` has `0`, `y` where `a` has
`0` and `b` has `1`, the pin `2` where both have `1` and the pin `3` where
both have `0`.
-/
def pairGadgetConstraint (Γ : Gamma) (symbol : Γ.Symbol)
    (a b : BooleanTuple (Γ.relationOf symbol).arity) : Constraint Γ where
  symbol := symbol
  vars := fun i =>
    if a i then
      if b i then 2 else 0
    else
      if b i then 1 else 3

/-- The tuple of the pair-failure gadget at `(x, y)` with the pins `true` and `false`. -/
def pairGadgetTuple {k : Nat} (a b : BooleanTuple k) (x y : Bool) : BooleanTuple k :=
  fun i =>
    if a i then
      if b i then true else x
    else
      if b i then y else false

@[simp]
theorem pairGadgetTuple_true_false {k : Nat} (a b : BooleanTuple k) :
    pairGadgetTuple a b true false = a := by
  funext i
  by_cases h1 : a i = true <;> by_cases h2 : b i = true <;> simp [pairGadgetTuple, h1, h2]

@[simp]
theorem pairGadgetTuple_false_true {k : Nat} (a b : BooleanTuple k) :
    pairGadgetTuple a b false true = b := by
  funext i
  by_cases h1 : a i = true <;> by_cases h2 : b i = true <;> simp [pairGadgetTuple, h1, h2]

@[simp]
theorem pairGadgetTuple_false_false {k : Nat} (a b : BooleanTuple k) :
    pairGadgetTuple a b false false = BooleanRelation.meet a b := by
  funext i
  by_cases h1 : a i = true <;> by_cases h2 : b i = true <;>
    simp [pairGadgetTuple, BooleanRelation.meet, h1, h2]

@[simp]
theorem pairGadgetTuple_true_true {k : Nat} (a b : BooleanTuple k) :
    pairGadgetTuple a b true true = BooleanRelation.join a b := by
  funext i
  by_cases h1 : a i = true <;> by_cases h2 : b i = true <;>
    simp [pairGadgetTuple, BooleanRelation.join, h1, h2]

/-- The assignment of a pair-failure constraint is the pinned pair-failure tuple.

The pin keys `2` and `3` must take the values `true` and `false`, which the
canonical pin formulas of `ConstantCase` guarantee.
-/
theorem pairGadgetConstraint_tuple_eq (Γ : Gamma) (symbol : Γ.Symbol)
    (a b : BooleanTuple (Γ.relationOf symbol).arity) (assignment : SAT.Assignment)
    (h2 : assignment 2 = true) (h3 : assignment 3 = false) :
    Constraint.assignmentTuple (pairGadgetConstraint Γ symbol a b) assignment =
      pairGadgetTuple a b (assignment 0) (assignment 1) := by
  funext i
  by_cases h1 : a i = true <;> by_cases hb : b i = true <;>
    simp [Constraint.assignmentTuple, pairGadgetConstraint, pairGadgetTuple, h1, hb, h2, h3]

theorem pairGadgetConstraint_satisfies_pinned_iff (Γ : Gamma) (symbol : Γ.Symbol)
    (a b : BooleanTuple (Γ.relationOf symbol).arity) (assignment : SAT.Assignment)
    (h2 : assignment 2 = true) (h3 : assignment 3 = false) :
    Constraint.Satisfies (pairGadgetConstraint Γ symbol a b) assignment ↔
      (Γ.relationOf symbol).Holds
        (pairGadgetTuple a b (assignment 0) (assignment 1)) := by
  unfold Constraint.Satisfies
  rw [pairGadgetConstraint_tuple_eq Γ symbol a b assignment h2 h3]
  unfold pairGadgetConstraint
  rfl

/-- The positive-clause gadget from a meet-failure and a join-inclusion.

`R₀(x, y, pins)` realizes `x ∨ y` when `a, b ∈ R₀`, `a ∧ b ∉ R₀` and
`a ∨ b ∈ R₀`.
-/
noncomputable def or2Gadget_of_pairGadget (Γ : Gamma) (symbol : Γ.Symbol)
    (a b : BooleanTuple (Γ.relationOf symbol).arity)
    (ha : (Γ.relationOf symbol).Holds a) (hb : (Γ.relationOf symbol).Holds b)
    (hmeet : ¬ (Γ.relationOf symbol).Holds (BooleanRelation.meet a b))
    (hjoin : (Γ.relationOf symbol).Holds (BooleanRelation.join a b))
    (constants : ConstantCase Γ) : Gadget Γ or2Rel where
  formula := [pairGadgetConstraint Γ symbol a b] ++ constants.pinZero ++ constants.pinOne
  outputs := fun
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
  outputs_injective := by
    intro i j equality
    fin_cases i <;> fin_cases j <;> simp at equality ⊢
  correct := by
    intro tuple
    constructor
    · intro holds
      rcases constants.pins_satisfiable (tuple ⟨0, by decide⟩) (tuple ⟨1, by decide⟩) with
        ⟨witness, hw0, hw1, hpinZero, hpinOne⟩
      have hw2 : witness 2 = true := constants.pinOne_spec witness hpinOne
      have hw3 : witness 3 = false := constants.pinZero_spec witness hpinZero
      refine ⟨witness, ?_, ?_⟩
      · intro constraint constraintMember
        rcases List.mem_cons.mp constraintMember with rfl | h'
        · cases h0 : tuple ⟨0, by decide⟩ <;> cases h1 : tuple ⟨1, by decide⟩
          · exfalso
            rcases (or2Rel_holds_iff tuple).1 holds with hA | hB
            · exact Bool.false_ne_true (h0.symm.trans hA)
            · exact Bool.false_ne_true (h1.symm.trans hB)
          · rw [pairGadgetConstraint_satisfies_pinned_iff Γ symbol a b witness hw2 hw3]
            simpa [hw0, hw1, h0, h1] using hb
          · rw [pairGadgetConstraint_satisfies_pinned_iff Γ symbol a b witness hw2 hw3]
            simpa [hw0, hw1, h0, h1] using ha
          · rw [pairGadgetConstraint_satisfies_pinned_iff Γ symbol a b witness hw2 hw3]
            simpa [hw0, hw1, h0, h1] using hjoin
        · rcases List.mem_append.mp h' with h'' | h'''
          · exact hpinZero constraint h''
          · exact hpinOne constraint h'''
      · intro i
        fin_cases i <;> simp [hw0, hw1]
    · rintro ⟨assignment, ⟨satisfies, outputs⟩⟩
      have hpinOneS : CSP.Formula.Satisfies constants.pinOne assignment :=
        fun d hd => satisfies d (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr hd))))
      have hpinZeroS : CSP.Formula.Satisfies constants.pinZero assignment :=
        fun d hd => satisfies d (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hd))))
      have h2 : assignment 2 = true := constants.pinOne_spec assignment hpinOneS
      have h3 : assignment 3 = false := constants.pinZero_spec assignment hpinZeroS
      have htuple : (Γ.relationOf symbol).Holds
          (pairGadgetTuple a b (assignment 0) (assignment 1)) := by
        exact (pairGadgetConstraint_satisfies_pinned_iff Γ symbol a b assignment h2 h3).1
          (satisfies (pairGadgetConstraint Γ symbol a b) (by simp))
      have hOut0 : tuple ⟨0, by decide⟩ = assignment 0 := (outputs ⟨0, by decide⟩).symm
      have hOut1 : tuple ⟨1, by decide⟩ = assignment 1 := (outputs ⟨1, by decide⟩).symm
      cases h0 : assignment 0 <;> cases h1 : assignment 1 <;> simp [h0, h1] at htuple
      · exact False.elim (hmeet htuple)
      · exact (or2Rel_holds_iff tuple).2 (by
          right
          exact hOut1.trans h1)
      · exact (or2Rel_holds_iff tuple).2 (by
          left
          exact hOut0.trans h0)
      · exact (or2Rel_holds_iff tuple).2 (by
          left
          exact hOut0.trans h0)

/-- The disequality gadget from a pair-failure and the rejection of both corners.

`R₀(x, y, pins)` realizes `x ≠ y` when `a, b ∈ R₀`, and both `a ∧ b` and
`a ∨ b` are rejected.
-/
noncomputable def diseqGadget_of_pairGadget (Γ : Gamma) (symbol : Γ.Symbol)
    (a b : BooleanTuple (Γ.relationOf symbol).arity)
    (ha : (Γ.relationOf symbol).Holds a) (hb : (Γ.relationOf symbol).Holds b)
    (hmeet : ¬ (Γ.relationOf symbol).Holds (BooleanRelation.meet a b))
    (hjoin : ¬ (Γ.relationOf symbol).Holds (BooleanRelation.join a b))
    (constants : ConstantCase Γ) : Gadget Γ diseqRel where
  formula := [pairGadgetConstraint Γ symbol a b] ++ constants.pinZero ++ constants.pinOne
  outputs := fun
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
  outputs_injective := by
    intro i j equality
    fin_cases i <;> fin_cases j <;> simp at equality ⊢
  correct := by
    intro tuple
    constructor
    · intro holds
      have hneq : tuple ⟨0, by decide⟩ ≠ tuple ⟨1, by decide⟩ :=
        (diseqRel_holds_iff tuple).1 holds
      rcases constants.pins_satisfiable (tuple ⟨0, by decide⟩) (tuple ⟨1, by decide⟩) with
        ⟨witness, hw0, hw1, hpinZero, hpinOne⟩
      have hw2 : witness 2 = true := constants.pinOne_spec witness hpinOne
      have hw3 : witness 3 = false := constants.pinZero_spec witness hpinZero
      refine ⟨witness, ?_, ?_⟩
      · intro constraint constraintMember
        rcases List.mem_cons.mp constraintMember with rfl | h'
        · cases h0 : tuple ⟨0, by decide⟩ <;> cases h1 : tuple ⟨1, by decide⟩
          · exfalso
            exact hneq (h0.trans h1.symm)
          · rw [pairGadgetConstraint_satisfies_pinned_iff Γ symbol a b witness hw2 hw3]
            simpa [hw0, hw1, h0, h1] using hb
          · rw [pairGadgetConstraint_satisfies_pinned_iff Γ symbol a b witness hw2 hw3]
            simpa [hw0, hw1, h0, h1] using ha
          · exfalso
            exact hneq (h0.trans h1.symm)
        · rcases List.mem_append.mp h' with h'' | h'''
          · exact hpinZero constraint h''
          · exact hpinOne constraint h'''
      · intro i
        fin_cases i <;> simp [hw0, hw1]
    · rintro ⟨assignment, ⟨satisfies, outputs⟩⟩
      have hpinOneS : CSP.Formula.Satisfies constants.pinOne assignment :=
        fun d hd => satisfies d (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr hd))))
      have hpinZeroS : CSP.Formula.Satisfies constants.pinZero assignment :=
        fun d hd => satisfies d (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hd))))
      have h2 : assignment 2 = true := constants.pinOne_spec assignment hpinOneS
      have h3 : assignment 3 = false := constants.pinZero_spec assignment hpinZeroS
      have htuple : (Γ.relationOf symbol).Holds
          (pairGadgetTuple a b (assignment 0) (assignment 1)) := by
        exact (pairGadgetConstraint_satisfies_pinned_iff Γ symbol a b assignment h2 h3).1
          (satisfies (pairGadgetConstraint Γ symbol a b) (by simp))
      have hOut0 : tuple ⟨0, by decide⟩ = assignment 0 := (outputs ⟨0, by decide⟩).symm
      have hOut1 : tuple ⟨1, by decide⟩ = assignment 1 := (outputs ⟨1, by decide⟩).symm
      cases h0 : assignment 0 <;> cases h1 : assignment 1 <;> simp [h0, h1] at htuple
      · exact False.elim (hmeet htuple)
      · exact (diseqRel_holds_iff tuple).2 (by
          intro hEq
          have hAsgn : assignment 0 = assignment 1 := hOut0.symm.trans (hEq.trans hOut1)
          exact Bool.false_ne_true ((h0.symm.trans hAsgn).trans h1))
      · exact (diseqRel_holds_iff tuple).2 (by
          intro hEq
          have hAsgn : assignment 0 = assignment 1 := hOut0.symm.trans (hEq.trans hOut1)
          exact Bool.false_ne_true ((h0.symm.trans hAsgn).trans h1).symm)
      · exact False.elim (hjoin htuple)

/-- The negative-clause gadget from a join-failure and a meet-inclusion.

`R₀(x, y, pins)` realizes `¬x ∨ ¬y` when `a, b ∈ R₀`, `a ∨ b ∉ R₀` and
`a ∧ b ∈ R₀`.
-/
noncomputable def nand2Gadget_of_pairGadget (Γ : Gamma) (symbol : Γ.Symbol)
    (a b : BooleanTuple (Γ.relationOf symbol).arity)
    (ha : (Γ.relationOf symbol).Holds a) (hb : (Γ.relationOf symbol).Holds b)
    (hjoin : ¬ (Γ.relationOf symbol).Holds (BooleanRelation.join a b))
    (hmeet : (Γ.relationOf symbol).Holds (BooleanRelation.meet a b))
    (constants : ConstantCase Γ) : Gadget Γ nand2Rel where
  formula := [pairGadgetConstraint Γ symbol a b] ++ constants.pinZero ++ constants.pinOne
  outputs := fun
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
  outputs_injective := by
    intro i j equality
    fin_cases i <;> fin_cases j <;> simp at equality ⊢
  correct := by
    intro tuple
    constructor
    · intro holds
      rcases constants.pins_satisfiable (tuple ⟨0, by decide⟩) (tuple ⟨1, by decide⟩) with
        ⟨witness, hw0, hw1, hpinZero, hpinOne⟩
      have hw2 : witness 2 = true := constants.pinOne_spec witness hpinOne
      have hw3 : witness 3 = false := constants.pinZero_spec witness hpinZero
      refine ⟨witness, ?_, ?_⟩
      · intro constraint constraintMember
        rcases List.mem_cons.mp constraintMember with rfl | h'
        · cases h0 : tuple ⟨0, by decide⟩ <;> cases h1 : tuple ⟨1, by decide⟩
          · rw [pairGadgetConstraint_satisfies_pinned_iff Γ symbol a b witness hw2 hw3]
            simpa [hw0, hw1, h0, h1] using hmeet
          · rw [pairGadgetConstraint_satisfies_pinned_iff Γ symbol a b witness hw2 hw3]
            simpa [hw0, hw1, h0, h1] using hb
          · rw [pairGadgetConstraint_satisfies_pinned_iff Γ symbol a b witness hw2 hw3]
            simpa [hw0, hw1, h0, h1] using ha
          · exfalso
            exact (nand2Rel_holds_iff tuple).1 holds ⟨h0, h1⟩
        · rcases List.mem_append.mp h' with h'' | h'''
          · exact hpinZero constraint h''
          · exact hpinOne constraint h'''
      · intro i
        fin_cases i <;> simp [hw0, hw1]
    · rintro ⟨assignment, ⟨satisfies, outputs⟩⟩
      have hpinOneS : CSP.Formula.Satisfies constants.pinOne assignment :=
        fun d hd => satisfies d (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr hd))))
      have hpinZeroS : CSP.Formula.Satisfies constants.pinZero assignment :=
        fun d hd => satisfies d (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hd))))
      have h2 : assignment 2 = true := constants.pinOne_spec assignment hpinOneS
      have h3 : assignment 3 = false := constants.pinZero_spec assignment hpinZeroS
      have htuple : (Γ.relationOf symbol).Holds
          (pairGadgetTuple a b (assignment 0) (assignment 1)) := by
        exact (pairGadgetConstraint_satisfies_pinned_iff Γ symbol a b assignment h2 h3).1
          (satisfies (pairGadgetConstraint Γ symbol a b) (by simp))
      have hOut0 : tuple ⟨0, by decide⟩ = assignment 0 := (outputs ⟨0, by decide⟩).symm
      have hOut1 : tuple ⟨1, by decide⟩ = assignment 1 := (outputs ⟨1, by decide⟩).symm
      cases h0 : assignment 0 <;> cases h1 : assignment 1 <;> simp [h0, h1] at htuple
      · exact (nand2Rel_holds_iff tuple).2 (by
          intro hConj
          rcases hConj with ⟨hA, hB⟩
          exact Bool.false_ne_true ((hOut0.trans h0).symm.trans hA))
      · exact (nand2Rel_holds_iff tuple).2 (by
          intro hConj
          rcases hConj with ⟨hA, hB⟩
          exact Bool.false_ne_true ((hOut0.trans h0).symm.trans hA))
      · exact (nand2Rel_holds_iff tuple).2 (by
          intro hConj
          rcases hConj with ⟨hA, hB⟩
          exact Bool.false_ne_true ((hOut1.trans h1).symm.trans hB))
      · exact False.elim (hjoin htuple)

/-- A non-Horn language has a relation with a meet-failure witness. -/
theorem exists_meet_failure (Γ : Gamma) (h : ¬ Γ.IsHorn) :
    ∃ symbol : Γ.Symbol, ∃ a b : BooleanTuple (Γ.relationOf symbol).arity,
      (Γ.relationOf symbol).Holds a ∧ (Γ.relationOf symbol).Holds b ∧
        ¬ (Γ.relationOf symbol).Holds (BooleanRelation.meet a b) := by
  classical
  have hExists : ∃ symbol : Γ.Symbol, ¬ BooleanRelation.IsHorn (Γ.relationOf symbol) := by
    by_contra h'
    apply h
    intro symbol
    by_cases hSym : BooleanRelation.IsHorn (Γ.relationOf symbol)
    · exact hSym
    · exact False.elim (h' ⟨symbol, hSym⟩)
  rcases hExists with ⟨symbol, hSymbol⟩
  by_contra h'
  apply hSymbol
  intro a b ha hb
  by_cases hmeet : (Γ.relationOf symbol).Holds (BooleanRelation.meet a b)
  · exact hmeet
  · exact False.elim (h' ⟨symbol, a, b, ha, hb, hmeet⟩)

/-- A non-dual-Horn language has a relation with a join-failure witness. -/
theorem exists_join_failure (Γ : Gamma) (h : ¬ Γ.IsDualHorn) :
    ∃ symbol : Γ.Symbol, ∃ a b : BooleanTuple (Γ.relationOf symbol).arity,
      (Γ.relationOf symbol).Holds a ∧ (Γ.relationOf symbol).Holds b ∧
        ¬ (Γ.relationOf symbol).Holds (BooleanRelation.join a b) := by
  classical
  have hExists : ∃ symbol : Γ.Symbol, ¬ BooleanRelation.IsDualHorn (Γ.relationOf symbol) := by
    by_contra h'
    apply h
    intro symbol
    by_cases hSym : BooleanRelation.IsDualHorn (Γ.relationOf symbol)
    · exact hSym
    · exact False.elim (h' ⟨symbol, hSym⟩)
  rcases hExists with ⟨symbol, hSymbol⟩
  by_contra h'
  apply hSymbol
  intro a b ha hb
  by_cases hjoin : (Γ.relationOf symbol).Holds (BooleanRelation.join a b)
  · exact hjoin
  · exact False.elim (h' ⟨symbol, a, b, ha, hb, hjoin⟩)

/-- The Horn-failure step of the case analysis: with both constants, a
meet-failure pp-defines the positive binary clause or the disequality. -/
theorem ppDefines_or2_or_disequality_of_not_horn (Γ : Gamma)
    (constants : ConstantCase Γ) (notHorn : ¬ Γ.IsHorn) :
    PPDefinesOr2 Γ ∨ PPDefinesDisequality Γ := by
  rcases exists_meet_failure Γ notHorn with ⟨symbol, a, b, ha, hb, hmeet⟩
  by_cases hjoin : (Γ.relationOf symbol).Holds (BooleanRelation.join a b)
  · exact Or.inl ⟨or2Gadget_of_pairGadget Γ symbol a b ha hb hmeet hjoin constants⟩
  · exact Or.inr ⟨diseqGadget_of_pairGadget Γ symbol a b ha hb hmeet hjoin constants⟩

/-- The dual-Horn-failure step of the case analysis: with both constants, a
join-failure pp-defines the negative binary clause or the disequality. -/
theorem ppDefines_nand2_or_disequality_of_not_dualHorn (Γ : Gamma)
    (constants : ConstantCase Γ) (notDualHorn : ¬ Γ.IsDualHorn) :
    PPDefinesNand2 Γ ∨ PPDefinesDisequality Γ := by
  rcases exists_join_failure Γ notDualHorn with ⟨symbol, a, b, ha, hb, hjoin⟩
  by_cases hmeet : (Γ.relationOf symbol).Holds (BooleanRelation.meet a b)
  · exact Or.inl ⟨nand2Gadget_of_pairGadget Γ symbol a b ha hb hjoin hmeet constants⟩
  · exact Or.inr ⟨diseqGadget_of_pairGadget Γ symbol a b ha hb hmeet hjoin constants⟩

/-! ### Truth-table helpers for the hard cores -/

/-- A ternary tuple with the three given Boolean values. -/
def triple (x y z : Bool) : BooleanTuple 3 :=
  StandardRelations.tripleTuple x y z

/-- The NAE-3 relation rejects the constant tuples. -/
theorem notAllEqual3Rel_not_holds_const {b : Bool} :
    ¬ StandardRelations.notAllEqual3Rel.Holds (fun _ => b) := by
  intro h
  change (BoolRel.ofPredicate 3 (fun t : BooleanTuple 3 => ∃ i j : Fin 3, t i ≠ t j)).Holds
    (fun _ => b) at h
  rw [BoolRel.holds_ofPredicate_iff] at h
  rcases h with ⟨i, j, hij⟩
  fin_cases i <;> fin_cases j <;> simp at hij

/-- The NAE-3 relation rejects the all-zero tuple. -/
theorem notAllEqual3Rel_not_holds_zero :
    ¬ StandardRelations.notAllEqual3Rel.Holds (fun _ => false) :=
  notAllEqual3Rel_not_holds_const

/-- The NAE-3 relation rejects the all-one tuple. -/
theorem notAllEqual3Rel_not_holds_one :
    ¬ StandardRelations.notAllEqual3Rel.Holds (fun _ => true) :=
  notAllEqual3Rel_not_holds_const

/-- The NAE-3 relation contains the tuple `(x, y, z)` exactly when they are not all equal. -/
theorem notAllEqual3Rel_holds_triple (x y z : Bool) :
    StandardRelations.notAllEqual3Rel.Holds (StandardRelations.tripleTuple x y z) ↔
      ¬ (x = y ∧ y = z) :=
  StandardRelations.notAllEqual3Rel_holds_triple_iff x y z

/-- The NAE-3 witness tuples. -/
theorem notAllEqual3Rel_holds_witness1 :
    StandardRelations.notAllEqual3Rel.Holds (triple false true false) := by
  simpa [triple] using (notAllEqual3Rel_holds_triple false true false).2 (by decide)

theorem notAllEqual3Rel_holds_witness2 :
    StandardRelations.notAllEqual3Rel.Holds (triple true false false) := by
  simpa [triple] using (notAllEqual3Rel_holds_triple true false false).2 (by decide)

/-- The meet of the NAE-3 witnesses is the all-zero tuple. -/
theorem notAllEqual3Rel_witness_meet :
    BooleanRelation.meet (triple false true false) (triple true false false) = fun _ => false := by
  funext i
  fin_cases i <;> simp [BooleanRelation.meet, triple, StandardRelations.tripleTuple]

/-- The NAE-3 join-witness tuples. -/
theorem notAllEqual3Rel_holds_witness_join1 :
    StandardRelations.notAllEqual3Rel.Holds (triple false true true) := by
  simpa [triple] using (notAllEqual3Rel_holds_triple false true true).2 (by decide)

theorem notAllEqual3Rel_holds_witness_join2 :
    StandardRelations.notAllEqual3Rel.Holds (triple true false true) := by
  simpa [triple] using (notAllEqual3Rel_holds_triple true false true).2 (by decide)

/-- The join of the NAE-3 join-witnesses is the all-one tuple. -/
theorem notAllEqual3Rel_witness_join :
    BooleanRelation.join (triple false true true) (triple true false true) = fun _ => true := by
  funext i
  fin_cases i <;> simp [BooleanRelation.join, triple, StandardRelations.tripleTuple]

/-- The majority of the NAE-3 witnesses is the all-one tuple. -/
theorem notAllEqual3Rel_witness_majority :
    BooleanRelation.majority (triple false true true) (triple true false true) (triple true true false) =
      fun _ => true := by
  funext i
  fin_cases i <;> simp [BooleanRelation.majority, triple, StandardRelations.tripleTuple]

/-- The affine sum of the NAE-3 witnesses is the all-zero tuple. -/
theorem notAllEqual3Rel_witness_affine :
    BooleanRelation.affineOp (triple false true true) (triple true false true) (triple true true false) =
      fun _ => false := by
  funext i
  fin_cases i <;> simp [BooleanRelation.affineOp, triple, StandardRelations.tripleTuple]

/-! ### The hard cores lie outside the six classes -/

/-- The positive NAE-3 core is not 0-valid. -/
theorem nae3Core_not_zeroValid : ¬ nae3Core.IsZeroValid := by
  intro h
  have hholds : StandardRelations.notAllEqual3Rel.Holds (fun _ => false) := by
    simpa [nae3Core] using h ()
  exact notAllEqual3Rel_not_holds_zero hholds

/-- The positive NAE-3 core is not 1-valid. -/
theorem nae3Core_not_oneValid : ¬ nae3Core.IsOneValid := by
  intro h
  have hholds : StandardRelations.notAllEqual3Rel.Holds (fun _ => true) := by
    simpa [nae3Core] using h ()
  exact notAllEqual3Rel_not_holds_one hholds

/-- The NAE-3 relation rejects the all-zero meet of its witnesses. -/
theorem notAllEqual3Rel_rejects_meet :
    ¬ StandardRelations.notAllEqual3Rel.Holds
      (BooleanRelation.meet (triple false true false) (triple true false false)) := by
  intro h
  change (BoolRel.ofPredicate 3 (fun t : BooleanTuple 3 => ∃ i j : Fin 3, t i ≠ t j)).Holds
    (BooleanRelation.meet (triple false true false) (triple true false false)) at h
  rw [BoolRel.holds_ofPredicate_iff] at h
  rcases h with ⟨i, j, hij⟩
  fin_cases i <;> fin_cases j <;>
    exact False.elim (by simpa [BooleanRelation.meet, triple, StandardRelations.tripleTuple] using hij)

/-- The NAE-3 relation rejects the all-one join of its witnesses. -/
theorem notAllEqual3Rel_rejects_join :
    ¬ StandardRelations.notAllEqual3Rel.Holds
      (BooleanRelation.join (triple false true true) (triple true false true)) := by
  intro h
  change (BoolRel.ofPredicate 3 (fun t : BooleanTuple 3 => ∃ i j : Fin 3, t i ≠ t j)).Holds
    (BooleanRelation.join (triple false true true) (triple true false true)) at h
  rw [BoolRel.holds_ofPredicate_iff] at h
  rcases h with ⟨i, j, hij⟩
  fin_cases i <;> fin_cases j <;>
    exact False.elim (by simpa [BooleanRelation.join, triple, StandardRelations.tripleTuple] using hij)

/-- The NAE-3 relation rejects the all-one majority of its witnesses. -/
theorem notAllEqual3Rel_rejects_majority :
    ¬ StandardRelations.notAllEqual3Rel.Holds
      (BooleanRelation.majority (triple false true true) (triple true false true)
        (triple true true false)) := by
  intro h
  change (BoolRel.ofPredicate 3 (fun t : BooleanTuple 3 => ∃ i j : Fin 3, t i ≠ t j)).Holds
    (BooleanRelation.majority (triple false true true) (triple true false true)
      (triple true true false)) at h
  rw [BoolRel.holds_ofPredicate_iff] at h
  rcases h with ⟨i, j, hij⟩
  fin_cases i <;> fin_cases j <;>
    exact False.elim (by simpa [BooleanRelation.majority, triple, StandardRelations.tripleTuple] using hij)

/-- The NAE-3 relation rejects the all-zero affine sum of its witnesses. -/
theorem notAllEqual3Rel_rejects_affine :
    ¬ StandardRelations.notAllEqual3Rel.Holds
      (BooleanRelation.affineOp (triple false true true) (triple true false true)
        (triple true true false)) := by
  intro h
  change (BoolRel.ofPredicate 3 (fun t : BooleanTuple 3 => ∃ i j : Fin 3, t i ≠ t j)).Holds
    (BooleanRelation.affineOp (triple false true true) (triple true false true)
      (triple true true false)) at h
  rw [BoolRel.holds_ofPredicate_iff] at h
  rcases h with ⟨i, j, hij⟩
  fin_cases i <;> fin_cases j <;>
    exact False.elim (by simpa [BooleanRelation.affineOp, triple, StandardRelations.tripleTuple] using hij)

/-- The positive NAE-3 core is not Horn. -/
theorem nae3Core_not_horn : ¬ nae3Core.IsHorn := by
  intro h
  have hholds : BooleanRelation.IsHorn (nae3Core.relationOf ()) := h ()
  exact notAllEqual3Rel_rejects_meet (hholds (triple false true false) (triple true false false)
    notAllEqual3Rel_holds_witness1 notAllEqual3Rel_holds_witness2)

/-- The positive NAE-3 core is not dual-Horn. -/
theorem nae3Core_not_dualHorn : ¬ nae3Core.IsDualHorn := by
  intro h
  have hholds : BooleanRelation.IsDualHorn (nae3Core.relationOf ()) := h ()
  exact notAllEqual3Rel_rejects_join (hholds (triple false true true) (triple true false true)
    notAllEqual3Rel_holds_witness_join1 notAllEqual3Rel_holds_witness_join2)

/-- The positive NAE-3 core is not bijunctive. -/
theorem nae3Core_not_bijunctive : ¬ nae3Core.IsBijunctive := by
  intro h
  have hholds : BooleanRelation.IsBijunctive (nae3Core.relationOf ()) := h ()
  exact notAllEqual3Rel_rejects_majority (hholds (triple false true true) (triple true false true)
    (triple true true false)
    (by simpa [triple] using (notAllEqual3Rel_holds_triple false true true).2 (by decide))
    (by simpa [triple] using (notAllEqual3Rel_holds_triple true false true).2 (by decide))
    (by simpa [triple] using (notAllEqual3Rel_holds_triple true true false).2 (by decide)))

/-- The positive NAE-3 core is not affine. -/
theorem nae3Core_not_affine : ¬ nae3Core.IsAffine := by
  intro h
  have hholds : BooleanRelation.IsAffine (nae3Core.relationOf ()) := h ()
  exact notAllEqual3Rel_rejects_affine (hholds (triple false true true) (triple true false true)
    (triple true true false)
    (by simpa [triple] using (notAllEqual3Rel_holds_triple false true true).2 (by decide))
    (by simpa [triple] using (notAllEqual3Rel_holds_triple true false true).2 (by decide))
    (by simpa [triple] using (notAllEqual3Rel_holds_triple true true false).2 (by decide)))

/-- The positive NAE-3 core lies outside the six tractable classes. -/
theorem nae3Core_not_schaeferTractable : ¬ nae3Core.IsSchaeferTractable := by
  intro h
  rcases h with h0 | h1 | hh | hd | hb | ha
  · exact nae3Core_not_zeroValid h0
  · exact nae3Core_not_oneValid h1
  · exact nae3Core_not_horn hh
  · exact nae3Core_not_dualHorn hd
  · exact nae3Core_not_bijunctive hb
  · exact nae3Core_not_affine ha

/-- The 1-in-3 relation rejects the all-zero tuple. -/
theorem exactlyOne3Rel_not_holds_zero :
    ¬ StandardRelations.exactlyOne3Rel.Holds (fun _ => false) := by
  intro h
  change (BoolRel.ofPredicate 3 (fun t : BooleanTuple 3 => StandardRelations.trueCount 3 t = 1)).Holds
    (fun _ => false) at h
  rw [BoolRel.holds_ofPredicate_iff] at h
  norm_num [StandardRelations.trueCount] at h

/-- The 1-in-3 relation rejects the all-one tuple. -/
theorem exactlyOne3Rel_not_holds_one :
    ¬ StandardRelations.exactlyOne3Rel.Holds (fun _ => true) := by
  intro h
  change (BoolRel.ofPredicate 3 (fun t : BooleanTuple 3 => StandardRelations.trueCount 3 t = 1)).Holds
    (fun _ => true) at h
  rw [BoolRel.holds_ofPredicate_iff] at h
  norm_num [StandardRelations.trueCount] at h

/-- The exactly-one witness tuples. -/
theorem exactlyOne3Rel_holds_witness1 :
    StandardRelations.exactlyOne3Rel.Holds (triple true false false) := by
  simpa [triple] using (exactlyOne3Rel_holds_triple_iff true false false).2 (by decide)

theorem exactlyOne3Rel_holds_witness2 :
    StandardRelations.exactlyOne3Rel.Holds (triple false true false) := by
  simpa [triple] using (exactlyOne3Rel_holds_triple_iff false true false).2 (by decide)

theorem exactlyOne3Rel_holds_witness3 :
    StandardRelations.exactlyOne3Rel.Holds (triple false false true) := by
  simpa [triple] using (exactlyOne3Rel_holds_triple_iff false false true).2 (by decide)

/-- The meet of the exactly-one witnesses is the all-zero tuple. -/
theorem exactlyOne3Rel_witness_meet :
    BooleanRelation.meet (triple true false false) (triple false true false) = fun _ => false := by
  funext i
  fin_cases i <;> simp [BooleanRelation.meet, triple, StandardRelations.tripleTuple]

/-- The join of the exactly-one witnesses is the weight-two tuple. -/
theorem exactlyOne3Rel_witness_join :
    BooleanRelation.join (triple true false false) (triple false true false) =
      triple true true false := by
  funext i
  fin_cases i <;> simp [BooleanRelation.join, triple, StandardRelations.tripleTuple]

/-- The majority of the exactly-one witnesses is the all-zero tuple. -/
theorem exactlyOne3Rel_witness_majority :
    BooleanRelation.majority (triple true false false) (triple false true false)
        (triple false false true) = fun _ => false := by
  funext i
  fin_cases i <;> simp [BooleanRelation.majority, triple, StandardRelations.tripleTuple]

/-- The affine sum of the exactly-one witnesses is the all-one tuple. -/
theorem exactlyOne3Rel_witness_affine :
    BooleanRelation.affineOp (triple true false false) (triple false true false)
        (triple false false true) = fun _ => true := by
  funext i
  fin_cases i <;> simp [BooleanRelation.affineOp, triple, StandardRelations.tripleTuple]

/-- The positive exactly-one core is not 0-valid. -/
theorem oneInThreeCore_not_zeroValid : ¬ oneInThreeCore.IsZeroValid := by
  intro h
  have hholds : StandardRelations.exactlyOne3Rel.Holds (fun _ => false) := by
    simpa [oneInThreeCore] using h ()
  exact exactlyOne3Rel_not_holds_zero hholds

/-- The positive exactly-one core is not 1-valid. -/
theorem oneInThreeCore_not_oneValid : ¬ oneInThreeCore.IsOneValid := by
  intro h
  have hholds : StandardRelations.exactlyOne3Rel.Holds (fun _ => true) := by
    simpa [oneInThreeCore] using h ()
  exact exactlyOne3Rel_not_holds_one hholds

/-- The 1-in-3 relation rejects the all-zero meet of its witnesses. -/
theorem exactlyOne3Rel_rejects_meet :
    ¬ StandardRelations.exactlyOne3Rel.Holds
      (BooleanRelation.meet (triple true false false) (triple false true false)) := by
  intro h
  have hOpEq : BooleanRelation.meet (triple true false false) (triple false true false) =
      StandardRelations.tripleTuple false false false := by
    funext i
    fin_cases i <;> simp [BooleanRelation.meet, triple, StandardRelations.tripleTuple]
  have hTriple : StandardRelations.exactlyOne3Rel.Holds
      (StandardRelations.tripleTuple false false false) := by
    simpa [hOpEq] using h
  rw [exactlyOne3Rel_holds_triple_iff] at hTriple
  norm_num at hTriple

/-- The 1-in-3 relation rejects the all-one join of its witnesses. -/
theorem exactlyOne3Rel_rejects_join :
    ¬ StandardRelations.exactlyOne3Rel.Holds
      (BooleanRelation.join (triple true false false) (triple false true false)) := by
  intro h
  have hOpEq : BooleanRelation.join (triple true false false) (triple false true false) =
      StandardRelations.tripleTuple true true false := by
    funext i
    fin_cases i <;> simp [BooleanRelation.join, triple, StandardRelations.tripleTuple]
  have hTriple : StandardRelations.exactlyOne3Rel.Holds
      (StandardRelations.tripleTuple true true false) := by
    simpa [hOpEq] using h
  rw [exactlyOne3Rel_holds_triple_iff] at hTriple
  norm_num at hTriple

/-- The 1-in-3 relation rejects the all-zero majority of its witnesses. -/
theorem exactlyOne3Rel_rejects_majority :
    ¬ StandardRelations.exactlyOne3Rel.Holds
      (BooleanRelation.majority (triple true false false) (triple false true false)
        (triple false false true)) := by
  intro h
  have hOpEq : BooleanRelation.majority (triple true false false) (triple false true false)
      (triple false false true) = StandardRelations.tripleTuple false false false := by
    funext i
    fin_cases i <;> simp [BooleanRelation.majority, triple, StandardRelations.tripleTuple]
  have hTriple : StandardRelations.exactlyOne3Rel.Holds
      (StandardRelations.tripleTuple false false false) := by
    simpa [hOpEq] using h
  rw [exactlyOne3Rel_holds_triple_iff] at hTriple
  norm_num at hTriple

/-- The 1-in-3 relation rejects the all-one affine sum of its witnesses. -/
theorem exactlyOne3Rel_rejects_affine :
    ¬ StandardRelations.exactlyOne3Rel.Holds
      (BooleanRelation.affineOp (triple true false false) (triple false true false)
        (triple false false true)) := by
  intro h
  have hOpEq : BooleanRelation.affineOp (triple true false false) (triple false true false)
      (triple false false true) = StandardRelations.tripleTuple true true true := by
    funext i
    fin_cases i <;> simp [BooleanRelation.affineOp, triple, StandardRelations.tripleTuple]
  have hTriple : StandardRelations.exactlyOne3Rel.Holds
      (StandardRelations.tripleTuple true true true) := by
    simpa [hOpEq] using h
  rw [exactlyOne3Rel_holds_triple_iff] at hTriple
  norm_num at hTriple

/-- The positive exactly-one core is not Horn. -/
theorem oneInThreeCore_not_horn : ¬ oneInThreeCore.IsHorn := by
  intro h
  have hholds : BooleanRelation.IsHorn (oneInThreeCore.relationOf ()) := h ()
  exact exactlyOne3Rel_rejects_meet (hholds (triple true false false) (triple false true false)
    exactlyOne3Rel_holds_witness1 exactlyOne3Rel_holds_witness2)

/-- The positive exactly-one core is not dual-Horn. -/
theorem oneInThreeCore_not_dualHorn : ¬ oneInThreeCore.IsDualHorn := by
  intro h
  have hholds : BooleanRelation.IsDualHorn (oneInThreeCore.relationOf ()) := h ()
  exact exactlyOne3Rel_rejects_join (hholds (triple true false false) (triple false true false)
    exactlyOne3Rel_holds_witness1 exactlyOne3Rel_holds_witness2)

/-- The positive exactly-one core is not bijunctive. -/
theorem oneInThreeCore_not_bijunctive : ¬ oneInThreeCore.IsBijunctive := by
  intro h
  have hholds : BooleanRelation.IsBijunctive (oneInThreeCore.relationOf ()) := h ()
  exact exactlyOne3Rel_rejects_majority (hholds (triple true false false) (triple false true false)
    (triple false false true) exactlyOne3Rel_holds_witness1 exactlyOne3Rel_holds_witness2
    exactlyOne3Rel_holds_witness3)

/-- The positive exactly-one core is not affine. -/
theorem oneInThreeCore_not_affine : ¬ oneInThreeCore.IsAffine := by
  intro h
  have hholds : BooleanRelation.IsAffine (oneInThreeCore.relationOf ()) := h ()
  exact exactlyOne3Rel_rejects_affine (hholds (triple true false false) (triple false true false)
    (triple false false true) exactlyOne3Rel_holds_witness1 exactlyOne3Rel_holds_witness2
    exactlyOne3Rel_holds_witness3)

/-- The positive exactly-one core lies outside the six tractable classes. -/
theorem oneInThreeCore_not_schaeferTractable : ¬ oneInThreeCore.IsSchaeferTractable := by
  intro h
  rcases h with h0 | h1 | hh | hd | hb | ha
  · exact oneInThreeCore_not_zeroValid h0
  · exact oneInThreeCore_not_oneValid h1
  · exact oneInThreeCore_not_horn hh
  · exact oneInThreeCore_not_dualHorn hd
  · exact oneInThreeCore_not_bijunctive hb
  · exact oneInThreeCore_not_affine ha

/-- The exactly-two relation rejects the all-zero tuple. -/
theorem exactlyTwo3Rel_not_holds_zero :
    ¬ (StandardRelations.exactlyRel 3 2).Holds (fun _ => false) := by
  intro h
  change (BoolRel.ofPredicate 3 (fun t : BooleanTuple 3 => StandardRelations.trueCount 3 t = 2)).Holds
    (fun _ => false) at h
  rw [BoolRel.holds_ofPredicate_iff] at h
  norm_num [StandardRelations.trueCount] at h

/-- The exactly-two relation rejects the all-one tuple. -/
theorem exactlyTwo3Rel_not_holds_one :
    ¬ (StandardRelations.exactlyRel 3 2).Holds (fun _ => true) := by
  intro h
  change (BoolRel.ofPredicate 3 (fun t : BooleanTuple 3 => StandardRelations.trueCount 3 t = 2)).Holds
    (fun _ => true) at h
  rw [BoolRel.holds_ofPredicate_iff] at h
  norm_num [StandardRelations.trueCount] at h

/-- The exactly-two witness tuples. -/
theorem exactlyTwo3Rel_holds_witness1 :
    (StandardRelations.exactlyRel 3 2).Holds (triple true true false) := by
  simpa [triple] using (exactlyTwo3Rel_holds_triple_iff true true false).2 (by decide)

theorem exactlyTwo3Rel_holds_witness2 :
    (StandardRelations.exactlyRel 3 2).Holds (triple true false true) := by
  simpa [triple] using (exactlyTwo3Rel_holds_triple_iff true false true).2 (by decide)

theorem exactlyTwo3Rel_holds_witness3 :
    (StandardRelations.exactlyRel 3 2).Holds (triple false true true) := by
  simpa [triple] using (exactlyTwo3Rel_holds_triple_iff false true true).2 (by decide)

/-- The meet of the exactly-two witnesses is the weight-one tuple. -/
theorem exactlyTwo3Rel_witness_meet :
    BooleanRelation.meet (triple true true false) (triple true false true) =
      triple true false false := by
  funext i
  fin_cases i <;> simp [BooleanRelation.meet, triple, StandardRelations.tripleTuple]

/-- The join of the exactly-two witnesses is the all-one tuple. -/
theorem exactlyTwo3Rel_witness_join :
    BooleanRelation.join (triple true true false) (triple false true true) = fun _ => true := by
  funext i
  fin_cases i <;> simp [BooleanRelation.join, triple, StandardRelations.tripleTuple]

/-- The majority of the exactly-two witnesses is the all-one tuple. -/
theorem exactlyTwo3Rel_witness_majority :
    BooleanRelation.majority (triple true true false) (triple true false true)
        (triple false true true) = fun _ => true := by
  funext i
  fin_cases i <;> simp [BooleanRelation.majority, triple, StandardRelations.tripleTuple]

/-- The affine sum of the exactly-two witnesses is the all-zero tuple. -/
theorem exactlyTwo3Rel_witness_affine :
    BooleanRelation.affineOp (triple true true false) (triple true false true)
        (triple false true true) = fun _ => false := by
  funext i
  fin_cases i <;> simp [BooleanRelation.affineOp, triple, StandardRelations.tripleTuple]

/-- The positive exactly-two core is not 0-valid. -/
theorem exactlyTwo3Core_not_zeroValid : ¬ exactlyTwo3Core.IsZeroValid := by
  intro h
  have hholds : (StandardRelations.exactlyRel 3 2).Holds (fun _ => false) := by
    simpa [exactlyTwo3Core] using h ()
  exact exactlyTwo3Rel_not_holds_zero hholds

/-- The positive exactly-two core is not 1-valid. -/
theorem exactlyTwo3Core_not_oneValid : ¬ exactlyTwo3Core.IsOneValid := by
  intro h
  have hholds : (StandardRelations.exactlyRel 3 2).Holds (fun _ => true) := by
    simpa [exactlyTwo3Core] using h ()
  exact exactlyTwo3Rel_not_holds_one hholds

/-- The 2-of-3 relation rejects the weight-one meet of its witnesses. -/
theorem exactlyTwo3Rel_rejects_meet :
    ¬ (StandardRelations.exactlyRel 3 2).Holds
      (BooleanRelation.meet (triple true true false) (triple true false true)) := by
  intro h
  have hOpEq : BooleanRelation.meet (triple true true false) (triple true false true) =
      StandardRelations.tripleTuple true false false := by
    funext i
    fin_cases i <;> simp [BooleanRelation.meet, triple, StandardRelations.tripleTuple]
  have hTriple : (StandardRelations.exactlyRel 3 2).Holds
      (StandardRelations.tripleTuple true false false) := by
    simpa [hOpEq] using h
  rw [exactlyTwo3Rel_holds_triple_iff] at hTriple
  norm_num at hTriple

/-- The 2-of-3 relation rejects the all-one join of its witnesses. -/
theorem exactlyTwo3Rel_rejects_join :
    ¬ (StandardRelations.exactlyRel 3 2).Holds
      (BooleanRelation.join (triple true true false) (triple false true true)) := by
  intro h
  have hOpEq : BooleanRelation.join (triple true true false) (triple false true true) =
      StandardRelations.tripleTuple true true true := by
    funext i
    fin_cases i <;> simp [BooleanRelation.join, triple, StandardRelations.tripleTuple]
  have hTriple : (StandardRelations.exactlyRel 3 2).Holds
      (StandardRelations.tripleTuple true true true) := by
    simpa [hOpEq] using h
  rw [exactlyTwo3Rel_holds_triple_iff] at hTriple
  norm_num at hTriple

/-- The 2-of-3 relation rejects the all-one majority of its witnesses. -/
theorem exactlyTwo3Rel_rejects_majority :
    ¬ (StandardRelations.exactlyRel 3 2).Holds
      (BooleanRelation.majority (triple true true false) (triple true false true)
        (triple false true true)) := by
  intro h
  have hOpEq : BooleanRelation.majority (triple true true false) (triple true false true) (triple false true true) =
      StandardRelations.tripleTuple true true true := by
    funext i
    fin_cases i <;> simp [BooleanRelation.majority, triple, StandardRelations.tripleTuple]
  have hTriple : (StandardRelations.exactlyRel 3 2).Holds
      (StandardRelations.tripleTuple true true true) := by
    simpa [hOpEq] using h
  rw [exactlyTwo3Rel_holds_triple_iff] at hTriple
  norm_num at hTriple

/-- The 2-of-3 relation rejects the all-zero affine sum of its witnesses. -/
theorem exactlyTwo3Rel_rejects_affine :
    ¬ (StandardRelations.exactlyRel 3 2).Holds
      (BooleanRelation.affineOp (triple true true false) (triple true false true)
        (triple false true true)) := by
  intro h
  have hOpEq : BooleanRelation.affineOp (triple true true false) (triple true false true) (triple false true true) =
      StandardRelations.tripleTuple false false false := by
    funext i
    fin_cases i <;> simp [BooleanRelation.affineOp, triple, StandardRelations.tripleTuple]
  have hTriple : (StandardRelations.exactlyRel 3 2).Holds
      (StandardRelations.tripleTuple false false false) := by
    simpa [hOpEq] using h
  rw [exactlyTwo3Rel_holds_triple_iff] at hTriple
  norm_num at hTriple

/-- The positive exactly-two core is not Horn. -/
theorem exactlyTwo3Core_not_horn : ¬ exactlyTwo3Core.IsHorn := by
  intro h
  have hholds : BooleanRelation.IsHorn (exactlyTwo3Core.relationOf ()) := h ()
  exact exactlyTwo3Rel_rejects_meet (hholds (triple true true false) (triple true false true)
    exactlyTwo3Rel_holds_witness1 exactlyTwo3Rel_holds_witness2)

/-- The positive exactly-two core is not dual-Horn. -/
theorem exactlyTwo3Core_not_dualHorn : ¬ exactlyTwo3Core.IsDualHorn := by
  intro h
  have hholds : BooleanRelation.IsDualHorn (exactlyTwo3Core.relationOf ()) := h ()
  exact exactlyTwo3Rel_rejects_join (hholds (triple true true false) (triple false true true)
    exactlyTwo3Rel_holds_witness1 exactlyTwo3Rel_holds_witness3)

/-- The positive exactly-two core is not bijunctive. -/
theorem exactlyTwo3Core_not_bijunctive : ¬ exactlyTwo3Core.IsBijunctive := by
  intro h
  have hholds : BooleanRelation.IsBijunctive (exactlyTwo3Core.relationOf ()) := h ()
  exact exactlyTwo3Rel_rejects_majority (hholds (triple true true false) (triple true false true)
    (triple false true true) exactlyTwo3Rel_holds_witness1 exactlyTwo3Rel_holds_witness2
    exactlyTwo3Rel_holds_witness3)

/-- The positive exactly-two core is not affine. -/
theorem exactlyTwo3Core_not_affine : ¬ exactlyTwo3Core.IsAffine := by
  intro h
  have hholds : BooleanRelation.IsAffine (exactlyTwo3Core.relationOf ()) := h ()
  exact exactlyTwo3Rel_rejects_affine (hholds (triple true true false) (triple true false true)
    (triple false true true) exactlyTwo3Rel_holds_witness1 exactlyTwo3Rel_holds_witness2
    exactlyTwo3Rel_holds_witness3)

/-- The positive exactly-two core lies outside the six tractable classes. -/
theorem exactlyTwo3Core_not_schaeferTractable : ¬ exactlyTwo3Core.IsSchaeferTractable := by
  intro h
  rcases h with h0 | h1 | hh | hd | hb | ha
  · exact exactlyTwo3Core_not_zeroValid h0
  · exact exactlyTwo3Core_not_oneValid h1
  · exact exactlyTwo3Core_not_horn hh
  · exact exactlyTwo3Core_not_dualHorn hd
  · exact exactlyTwo3Core_not_bijunctive hb
  · exact exactlyTwo3Core_not_affine ha

/-- The positive clause relation rejects the all-zero tuple. -/
theorem ternaryClauseRel_positive_not_holds_zero :
    ¬ (StandardRelations.ternaryClauseRel false false false).Holds (fun _ => false) := by
  intro h
  change (BoolRel.ofPredicate 3
    (fun t : BooleanTuple 3 => ∃ i : Fin 3, StandardRelations.literalValue false (t i) = true)).Holds
    (fun _ => false) at h
  rw [BoolRel.holds_ofPredicate_iff] at h
  rcases h with ⟨i, hi⟩
  fin_cases i <;> simp [StandardRelations.literalValue] at hi <;> exact Bool.false_ne_true hi

/-- The negative clause relation rejects the all-one tuple. -/
theorem ternaryClauseRel_negative_not_holds_one :
    ¬ (StandardRelations.ternaryClauseRel true true true).Holds (fun _ => true) := by
  intro h
  change (BoolRel.ofPredicate 3
    (fun t : BooleanTuple 3 => ∃ i : Fin 3, StandardRelations.literalValue true (t i) = true)).Holds
    (fun _ => true) at h
  rw [BoolRel.holds_ofPredicate_iff] at h
  rcases h with ⟨i, hi⟩
  fin_cases i <;> simp [StandardRelations.literalValue] at hi <;> exact Bool.false_ne_true hi

/-- The positive clause contains any tuple with a true entry. -/
theorem ternaryClauseRel_positive_holds (x y z : Bool) (h : x ∨ y ∨ z) :
    (StandardRelations.ternaryClauseRel false false false).Holds (triple x y z) := by
  unfold StandardRelations.ternaryClauseRel StandardRelations.clauseRel
  rw [BoolRel.holds_ofPredicate_iff]
  rcases h with hx | hy | hz
  · exact ⟨⟨0, by decide⟩, by simp [StandardRelations.literalValue, triple,
      StandardRelations.tripleTuple, hx]⟩
  · exact ⟨⟨1, by decide⟩, by simp [StandardRelations.literalValue, triple,
      StandardRelations.tripleTuple, hy]⟩
  · exact ⟨⟨2, by decide⟩, by simp [StandardRelations.literalValue, triple,
      StandardRelations.tripleTuple, hz]⟩

/-- The negative clause contains any tuple with a false entry. -/
theorem ternaryClauseRel_negative_holds (x y z : Bool) (h : ¬x ∨ ¬y ∨ ¬z) :
    (StandardRelations.ternaryClauseRel true true true).Holds (triple x y z) := by
  unfold StandardRelations.ternaryClauseRel StandardRelations.clauseRel
  rw [BoolRel.holds_ofPredicate_iff]
  rcases h with hx | hy | hz
  · exact ⟨⟨0, by decide⟩, by simp [StandardRelations.literalValue, triple,
      StandardRelations.tripleTuple, hx]⟩
  · exact ⟨⟨1, by decide⟩, by simp [StandardRelations.literalValue, triple,
      StandardRelations.tripleTuple, hy]⟩
  · exact ⟨⟨2, by decide⟩, by simp [StandardRelations.literalValue, triple,
      StandardRelations.tripleTuple, hz]⟩

/-- The positive clause rejects the meet of two of its rows. -/
theorem ternaryClauseRel_positive_rejects_meet :
    ¬ (StandardRelations.ternaryClauseRel false false false).Holds
      (BooleanRelation.meet (triple false true false) (triple true false false)) := by
  intro h
  change (BoolRel.ofPredicate 3
    (fun t : BooleanTuple 3 => ∃ i : Fin 3, StandardRelations.literalValue false (t i) = true)).Holds
    (BooleanRelation.meet (triple false true false) (triple true false false)) at h
  rw [BoolRel.holds_ofPredicate_iff] at h
  rcases h with ⟨i, hi⟩
  fin_cases i <;> simp [StandardRelations.literalValue, BooleanRelation.meet, triple,
    StandardRelations.tripleTuple] at hi <;> exact Bool.false_ne_true hi

/-- The negative clause rejects the join of two of its rows. -/
theorem ternaryClauseRel_negative_rejects_join :
    ¬ (StandardRelations.ternaryClauseRel true true true).Holds
      (BooleanRelation.join (triple true true false) (triple true false true)) := by
  intro h
  change (BoolRel.ofPredicate 3
    (fun t : BooleanTuple 3 => ∃ i : Fin 3, StandardRelations.literalValue true (t i) = true)).Holds
    (BooleanRelation.join (triple true true false) (triple true false true)) at h
  rw [BoolRel.holds_ofPredicate_iff] at h
  rcases h with ⟨i, hi⟩
  fin_cases i <;> simp [StandardRelations.literalValue, BooleanRelation.join, triple,
    StandardRelations.tripleTuple] at hi <;> exact Bool.false_ne_true hi

/-- The positive clause rejects the all-zero majority of three of its rows. -/
theorem ternaryClauseRel_positive_rejects_majority :
    ¬ (StandardRelations.ternaryClauseRel false false false).Holds
      (BooleanRelation.majority (triple true false false) (triple false true false)
        (triple false false true)) := by
  intro h
  change (BoolRel.ofPredicate 3
    (fun t : BooleanTuple 3 => ∃ i : Fin 3, StandardRelations.literalValue false (t i) = true)).Holds
    (BooleanRelation.majority (triple true false false) (triple false true false)
      (triple false false true)) at h
  rw [BoolRel.holds_ofPredicate_iff] at h
  rcases h with ⟨i, hi⟩
  fin_cases i <;> simp [StandardRelations.literalValue, BooleanRelation.majority, triple,
    StandardRelations.tripleTuple] at hi <;> exact Bool.false_ne_true hi

/-- The positive clause rejects the all-zero affine sum of three of its rows. -/
theorem ternaryClauseRel_positive_rejects_affine :
    ¬ (StandardRelations.ternaryClauseRel false false false).Holds
      (BooleanRelation.affineOp (triple false true true) (triple true false true)
        (triple true true false)) := by
  intro h
  change (BoolRel.ofPredicate 3
    (fun t : BooleanTuple 3 => ∃ i : Fin 3, StandardRelations.literalValue false (t i) = true)).Holds
    (BooleanRelation.affineOp (triple false true true) (triple true false true)
      (triple true true false)) at h
  rw [BoolRel.holds_ofPredicate_iff] at h
  rcases h with ⟨i, hi⟩
  fin_cases i <;> simp [StandardRelations.literalValue, BooleanRelation.affineOp, triple,
    StandardRelations.tripleTuple] at hi <;> exact Bool.false_ne_true hi

/-- The 3SAT-like core is not 0-valid. -/
theorem threeSATLikeCore_not_zeroValid : ¬ threeSATLikeCore.IsZeroValid := by
  intro h
  have hholds : BooleanRelation.IsZeroValid
      (threeSATLikeCore.relationOf ComplexityReduction.CSP.Examples.ThreeSATLikeSymbol.posPosPos) :=
    h ComplexityReduction.CSP.Examples.ThreeSATLikeSymbol.posPosPos
  exact ternaryClauseRel_positive_not_holds_zero (by simpa [threeSATLikeCore] using hholds)

/-- The 3SAT-like core is not 1-valid. -/
theorem threeSATLikeCore_not_oneValid : ¬ threeSATLikeCore.IsOneValid := by
  intro h
  have hholds : BooleanRelation.IsOneValid
      (threeSATLikeCore.relationOf ComplexityReduction.CSP.Examples.ThreeSATLikeSymbol.negNegNeg) :=
    h ComplexityReduction.CSP.Examples.ThreeSATLikeSymbol.negNegNeg
  exact ternaryClauseRel_negative_not_holds_one (by simpa [threeSATLikeCore] using hholds)

/-- The 3SAT-like core is not Horn. -/
theorem threeSATLikeCore_not_horn : ¬ threeSATLikeCore.IsHorn := by
  intro h
  have hholds : BooleanRelation.IsHorn
      (threeSATLikeCore.relationOf ComplexityReduction.CSP.Examples.ThreeSATLikeSymbol.posPosPos) :=
    h ComplexityReduction.CSP.Examples.ThreeSATLikeSymbol.posPosPos
  have hmeet : ¬ (StandardRelations.ternaryClauseRel false false false).Holds
      (BooleanRelation.meet (triple false true false) (triple true false false)) :=
    ternaryClauseRel_positive_rejects_meet
  exact hmeet (by
    simpa [threeSATLikeCore, ComplexityReduction.CSP.Examples.threeSATLikeRelationOf] using
      (hholds (triple false true false) (triple true false false)
        (ternaryClauseRel_positive_holds false true false (Or.inr (Or.inl rfl)))
        (ternaryClauseRel_positive_holds true false false (Or.inl rfl))))

/-- The 3SAT-like core is not dual-Horn. -/
theorem threeSATLikeCore_not_dualHorn : ¬ threeSATLikeCore.IsDualHorn := by
  intro h
  have hholds : BooleanRelation.IsDualHorn
      (threeSATLikeCore.relationOf ComplexityReduction.CSP.Examples.ThreeSATLikeSymbol.negNegNeg) :=
    h ComplexityReduction.CSP.Examples.ThreeSATLikeSymbol.negNegNeg
  have hjoin : ¬ (StandardRelations.ternaryClauseRel true true true).Holds
      (BooleanRelation.join (triple true true false) (triple true false true)) :=
    ternaryClauseRel_negative_rejects_join
  exact hjoin (by
    simpa [threeSATLikeCore, ComplexityReduction.CSP.Examples.threeSATLikeRelationOf] using
      (hholds (triple true true false) (triple true false true)
        (ternaryClauseRel_negative_holds true true false (Or.inr (Or.inr (by decide))))
        (ternaryClauseRel_negative_holds true false true (Or.inr (Or.inl (by decide))))))

/-- The 3SAT-like core is not bijunctive. -/
theorem threeSATLikeCore_not_bijunctive : ¬ threeSATLikeCore.IsBijunctive := by
  intro h
  have hholds : BooleanRelation.IsBijunctive
      (threeSATLikeCore.relationOf ComplexityReduction.CSP.Examples.ThreeSATLikeSymbol.posPosPos) :=
    h ComplexityReduction.CSP.Examples.ThreeSATLikeSymbol.posPosPos
  have hmajority : ¬ (StandardRelations.ternaryClauseRel false false false).Holds
      (BooleanRelation.majority (triple true false false) (triple false true false)
        (triple false false true)) :=
    ternaryClauseRel_positive_rejects_majority
  exact hmajority (by
    simpa [threeSATLikeCore, ComplexityReduction.CSP.Examples.threeSATLikeRelationOf] using
      (hholds (triple true false false) (triple false true false) (triple false false true)
        (ternaryClauseRel_positive_holds true false false (Or.inl rfl))
        (ternaryClauseRel_positive_holds false true false (Or.inr (Or.inl rfl)))
        (ternaryClauseRel_positive_holds false false true (Or.inr (Or.inr rfl)))))

/-- The 3SAT-like core is not affine. -/
theorem threeSATLikeCore_not_affine : ¬ threeSATLikeCore.IsAffine := by
  intro h
  have hholds : BooleanRelation.IsAffine
      (threeSATLikeCore.relationOf ComplexityReduction.CSP.Examples.ThreeSATLikeSymbol.posPosPos) :=
    h ComplexityReduction.CSP.Examples.ThreeSATLikeSymbol.posPosPos
  have haffine : ¬ (StandardRelations.ternaryClauseRel false false false).Holds
      (BooleanRelation.affineOp (triple false true true) (triple true false true)
        (triple true true false)) :=
    ternaryClauseRel_positive_rejects_affine
  exact haffine (by
    simpa [threeSATLikeCore, ComplexityReduction.CSP.Examples.threeSATLikeRelationOf] using
      (hholds (triple false true true) (triple true false true) (triple true true false)
        (ternaryClauseRel_positive_holds false true true (Or.inr (Or.inl rfl)))
        (ternaryClauseRel_positive_holds true false true (Or.inl rfl))
        (ternaryClauseRel_positive_holds true true false (Or.inl rfl))))

/-- The 3SAT-like core lies outside the six tractable classes. -/
theorem threeSATLikeCore_not_schaeferTractable : ¬ threeSATLikeCore.IsSchaeferTractable := by
  intro h
  rcases h with h0 | h1 | hh | hd | hb | ha
  · exact threeSATLikeCore_not_zeroValid h0
  · exact threeSATLikeCore_not_oneValid h1
  · exact threeSATLikeCore_not_horn hh
  · exact threeSATLikeCore_not_dualHorn hd
  · exact threeSATLikeCore_not_bijunctive hb
  · exact threeSATLikeCore_not_affine ha

/-! ### The cores realize the auxiliary relations -/

/-- The NAE-3 core pp-defines the disequality relation. -/
noncomputable def nae3Gadget_of_disequality : Gadget nae3Core diseqRel where
  formula := [nae3Constraint 0 1 1]
  outputs := fun
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
  outputs_injective := by
    intro i j equality
    fin_cases i <;> fin_cases j <;> simp at equality ⊢
  correct := by
    intro tuple
    constructor
    · intro holds
      refine ⟨fun var => if var = 0 then tuple ⟨0, by decide⟩
        else if var = 1 then tuple ⟨1, by decide⟩ else false, ?_, ?_⟩
      · intro constraint constraintMember
        rcases List.mem_cons.mp constraintMember with rfl | hEmpty
        · have hval : tuple ⟨0, by decide⟩ ≠ tuple ⟨1, by decide⟩ :=
            (diseqRel_holds_iff tuple).1 holds
          rw [nae3Constraint_repeat_satisfies_iff]
          simpa using (bool_ne_iff_eq_not (tuple ⟨0, by decide⟩) (tuple ⟨1, by decide⟩)).1 hval
        · cases hEmpty
      · intro i
        fin_cases i <;> rfl
    · rintro ⟨assignment, ⟨satisfies, outputs⟩⟩
      have hrepeat : Constraint.Satisfies (nae3Constraint 0 1 1) assignment :=
        satisfies (nae3Constraint 0 1 1) (by simp)
      have hneq : assignment 1 = !assignment 0 :=
        (nae3Constraint_repeat_satisfies_iff 0 1 assignment).1 hrepeat
      have hdiseq : assignment 0 ≠ assignment 1 :=
        (bool_ne_iff_eq_not (assignment 0) (assignment 1)).2 hneq
      have hOut0 : tuple ⟨0, by decide⟩ = assignment 0 := (outputs ⟨0, by decide⟩).symm
      have hOut1 : tuple ⟨1, by decide⟩ = assignment 1 := (outputs ⟨1, by decide⟩).symm
      cases hBool0 : assignment 0 <;> cases hBool1 : assignment 1
      · exfalso
        exact hdiseq (hBool0.trans hBool1.symm)
      · exact (diseqRel_holds_iff tuple).2 (by
          intro hEq
          exact hdiseq (hOut0.symm.trans (hEq.trans hOut1)))
      · exact (diseqRel_holds_iff tuple).2 (by
          intro hEq
          exact hdiseq (hOut0.symm.trans (hEq.trans hOut1)))
      · exfalso
        exact hdiseq (hBool0.trans hBool1.symm)

/-- The NAE-3 core pp-defines the disequality relation. -/
theorem nae3Core_ppDefines_disequality : PPDefinesDisequality nae3Core :=
  ⟨nae3Gadget_of_disequality⟩

/-- The exactly-one core pp-defines the constant zero. -/
noncomputable def oneInThreeGadget_of_const0 : Gadget oneInThreeCore const0Rel where
  formula := [oneInThreeConstraint 1 0 0]
  outputs := fun _ => 0
  outputs_injective := by
    intro i j equality
    fin_cases i <;> fin_cases j <;> rfl
  correct := by
    intro tuple
    constructor
    · intro holds
      refine ⟨fun var => if var = 0 then false else true, ?_, ?_⟩
      · intro constraint constraintMember
        rcases List.mem_cons.mp constraintMember with rfl | hEmpty
        · rw [oneInThreeConstraint_satisfies_iff]
          decide
        · cases hEmpty
      · intro i
        fin_cases i
        exact ((const0Rel_holds_iff tuple).1 holds).symm
    · rintro ⟨assignment, ⟨satisfies, outputs⟩⟩
      have hpin := satisfies (oneInThreeConstraint 1 0 0) (by simp)
      have hval : assignment 0 = false := oneInThree_pinFalse 0 1 assignment hpin
      have hout := outputs ⟨0, by decide⟩
      exact (const0Rel_holds_iff tuple).2 (hout.symm.trans hval)

/-- The exactly-one core pp-defines the constant one. -/
noncomputable def oneInThreeGadget_of_const1 : Gadget oneInThreeCore const1Rel where
  formula := [oneInThreeConstraint 0 1 1]
  outputs := fun _ => 0
  outputs_injective := by
    intro i j equality
    fin_cases i <;> fin_cases j <;> rfl
  correct := by
    intro tuple
    constructor
    · intro holds
      refine ⟨fun var => if var = 0 then true else false, ?_, ?_⟩
      · intro constraint constraintMember
        rcases List.mem_cons.mp constraintMember with rfl | hEmpty
        · rw [oneInThreeConstraint_satisfies_iff]
          decide
        · cases hEmpty
      · intro i
        fin_cases i
        exact ((const1Rel_holds_iff tuple).1 holds).symm
    · rintro ⟨assignment, ⟨satisfies, outputs⟩⟩
      have hpin := satisfies (oneInThreeConstraint 0 1 1) (by simp)
      have hval : assignment 0 = true := oneInThree_pinTrue 0 1 assignment hpin
      have hout := outputs ⟨0, by decide⟩
      exact (const1Rel_holds_iff tuple).2 (hout.symm.trans hval)

/-- The exactly-one core pp-defines both constants. -/
theorem oneInThreeCore_ppDefines_constants : PPDefinesBothConstants oneInThreeCore :=
  ⟨⟨oneInThreeGadget_of_const0⟩, ⟨oneInThreeGadget_of_const1⟩⟩

/-- The exactly-one core pp-defines the disequality relation. -/
noncomputable def oneInThreeGadget_of_disequality : Gadget oneInThreeCore diseqRel where
  formula := [oneInThreeConstraint 0 1 2, oneInThreeConstraint 3 2 2]
  outputs := fun
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
  outputs_injective := by
    intro i j equality
    fin_cases i <;> fin_cases j <;> simp at equality ⊢
  correct := by
    intro tuple
    constructor
    · intro holds
      refine ⟨fun var => if var = 0 then tuple ⟨0, by decide⟩
        else if var = 1 then tuple ⟨1, by decide⟩ else
          if var = 3 then true else false, ?_, ?_⟩
      · intro constraint constraintMember
        rcases List.mem_cons.mp constraintMember with rfl | h'
        · rw [oneInThreeConstraint_satisfies_iff]
          have hval : tuple ⟨0, by decide⟩ ≠ tuple ⟨1, by decide⟩ :=
            (diseqRel_holds_iff tuple).1 holds
          cases h0 : tuple ⟨0, by decide⟩ <;> cases h1 : tuple ⟨1, by decide⟩ <;> simp [h0, h1] at hval ⊢
        · rcases List.mem_cons.mp h' with rfl | hEmpty
          · rw [oneInThreeConstraint_satisfies_iff]
            norm_num
          · cases hEmpty
      · intro i
        fin_cases i <;> rfl
    · rintro ⟨assignment, ⟨satisfies, outputs⟩⟩
      have hmain : Constraint.Satisfies (oneInThreeConstraint 0 1 2) assignment :=
        satisfies (oneInThreeConstraint 0 1 2) (by simp)
      have hpin : Constraint.Satisfies (oneInThreeConstraint 3 2 2) assignment :=
        satisfies (oneInThreeConstraint 3 2 2) (by simp)
      have hdiseq : assignment 0 ≠ assignment 1 :=
        oneInThree_disequality_iff 0 1 2 3 assignment ⟨hmain, hpin⟩
      have hOut0 : tuple ⟨0, by decide⟩ = assignment 0 := (outputs ⟨0, by decide⟩).symm
      have hOut1 : tuple ⟨1, by decide⟩ = assignment 1 := (outputs ⟨1, by decide⟩).symm
      cases hBool0 : assignment 0 <;> cases hBool1 : assignment 1
      · exfalso
        exact hdiseq (hBool0.trans hBool1.symm)
      · exact (diseqRel_holds_iff tuple).2 (by
          intro hEq
          exact hdiseq (hOut0.symm.trans (hEq.trans hOut1)))
      · exact (diseqRel_holds_iff tuple).2 (by
          intro hEq
          exact hdiseq (hOut0.symm.trans (hEq.trans hOut1)))
      · exfalso
        exact hdiseq (hBool0.trans hBool1.symm)

/-- The exactly-one core pp-defines the disequality relation. -/
theorem oneInThreeCore_ppDefines_disequality : PPDefinesDisequality oneInThreeCore :=
  ⟨oneInThreeGadget_of_disequality⟩

/-- The exactly-two core pp-defines the constant zero. -/
noncomputable def exactlyTwo3Gadget_of_const0 : Gadget exactlyTwo3Core const0Rel where
  formula := [exactlyTwo3Constraint 0 1 1]
  outputs := fun _ => 0
  outputs_injective := by
    intro i j equality
    fin_cases i <;> fin_cases j <;> rfl
  correct := by
    intro tuple
    constructor
    · intro holds
      refine ⟨fun var => if var = 0 then false else true, ?_, ?_⟩
      · intro constraint constraintMember
        rcases List.mem_cons.mp constraintMember with rfl | hEmpty
        · rw [exactlyTwo3Constraint_satisfies_iff]
          decide
        · cases hEmpty
      · intro i
        fin_cases i
        exact ((const0Rel_holds_iff tuple).1 holds).symm
    · rintro ⟨assignment, ⟨satisfies, outputs⟩⟩
      have hmain := satisfies (exactlyTwo3Constraint 0 1 1) (by simp)
      have hval : assignment 0 = false := by
        rw [exactlyTwo3Constraint_satisfies_iff] at hmain
        cases h : assignment 0
        · rfl
        · exfalso
          cases h1 : assignment 1 <;> simp [h, h1] at hmain
      have hout := outputs ⟨0, by decide⟩
      exact (const0Rel_holds_iff tuple).2 (hout.symm.trans hval)

/-- The exactly-two core pp-defines the constant one. -/
noncomputable def exactlyTwo3Gadget_of_const1 : Gadget exactlyTwo3Core const1Rel where
  formula := [exactlyTwo3Constraint 1 0 0]
  outputs := fun _ => 0
  outputs_injective := by
    intro i j equality
    fin_cases i <;> fin_cases j <;> rfl
  correct := by
    intro tuple
    constructor
    · intro holds
      refine ⟨fun var => if var = 0 then true else false, ?_, ?_⟩
      · intro constraint constraintMember
        rcases List.mem_cons.mp constraintMember with rfl | hEmpty
        · rw [exactlyTwo3Constraint_satisfies_iff]
          decide
        · cases hEmpty
      · intro i
        fin_cases i
        exact ((const1Rel_holds_iff tuple).1 holds).symm
    · rintro ⟨assignment, ⟨satisfies, outputs⟩⟩
      have hmain := satisfies (exactlyTwo3Constraint 1 0 0) (by simp)
      have hval : assignment 0 = true := by
        rw [exactlyTwo3Constraint_satisfies_iff] at hmain
        cases h : assignment 0
        · exfalso
          cases h1 : assignment 1 <;> simp [h, h1] at hmain
        · rfl
      have hout := outputs ⟨0, by decide⟩
      exact (const1Rel_holds_iff tuple).2 (hout.symm.trans hval)

/-- The exactly-two core pp-defines both constants. -/
theorem exactlyTwo3Core_ppDefines_constants : PPDefinesBothConstants exactlyTwo3Core :=
  ⟨⟨exactlyTwo3Gadget_of_const0⟩, ⟨exactlyTwo3Gadget_of_const1⟩⟩

end ExpressivePower
end Hardness
end BooleanCSP
end Domain
end ComplexityReduction
