/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP.Hardness.Cores
import ComplexityReduction.Legacy.ComplexityReduction.Combinatorics.SetSystem
import ComplexityReduction.Legacy.ComplexityReduction.CSP.Encoding
import ComplexityReduction.Legacy.ComplexityReduction.CSP.To3SATCosted
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover.Part3

/-!
Base NP-hardness of the exactly-one-of-three core.

Schaefer's dichotomy lists positive 1-in-3-SAT among its NP-hard cores.  The
classical reduction is not clause-gadget-wise: monotone 1-in-3 constraints
cannot express a clause (`OR₃` is not primitive-positively definable from
1-in-3, and neither is `NAE₃`).  The classical route goes through Exact
Cover: every universe element must be covered by exactly one selected set,
and the `k`-ary "exactly one" constraint is realized by the chain gadget

    E(1)(x)          := 1in3(x, p, p)
    E(2)(x, y)       := 1in3(x, y, a) ∧ 1in3(b, a, a)
    E(k+2)(c, x, xs) := 1in3(c, x, a) ∧ [ā = ¬a] ∧ E(k+1)(ā, xs)

where `[ā = ¬a]` is the two-constraint disequality gadget and the chain
variable of level `l + 1` is a dedicated key never touched by the level-`l`
gadget positions.  This module proves the exact-cover-to-1-in-3 reduction
sound in both directions.
-/

namespace ComplexityReduction
namespace Domain
namespace BooleanCSP
namespace Hardness
namespace ExactCoverToOneInThree

open ComplexityReduction.CSP
open ComplexityReduction.Combinatorics

/-! ### Auxiliary variable allocation -/

/-- The auxiliary key of one gadget position of one universe element. -/
def auxiliaryVar (setsLength : Nat) (element position : Nat) : Nat :=
  setsLength + Nat.pair element position + 1

theorem setsLength_lt_auxiliaryVar (setsLength element position : Nat) :
    setsLength < auxiliaryVar setsLength element position := by
  unfold auxiliaryVar
  omega

theorem auxiliaryVar_injective (setsLength : Nat) :
    Function.Injective (fun input : Nat × Nat => auxiliaryVar setsLength input.1 input.2) := by
  intro left right equality
  unfold auxiliaryVar at equality
  have hpair := Nat.add_left_cancel (Nat.add_right_cancel equality)
  have conj := Nat.pair_eq_pair.mp hpair
  exact Prod.ext conj.1 conj.2

theorem auxiliaryVar_ne_of_position_ne (setsLength element : Nat) {p q : Nat}
    (h : p ≠ q) :
    auxiliaryVar setsLength element p ≠ auxiliaryVar setsLength element q := by
  intro hEq
  unfold auxiliaryVar at hEq
  have hpair : Nat.pair element p = Nat.pair element q := by
    omega
  have hpos := (Nat.pair_eq_pair.mp hpair).2
  exact h hpos

/-- The chain variable of block level `l`. -/
def blockChain (setsLength element level : Nat) : Nat :=
  auxiliaryVar setsLength element (5 * level + 4)

/-- The pin variable of one universe element, above every block position. -/
def elementPin (setsLength element length : Nat) : Nat :=
  auxiliaryVar setsLength element (5 * length + 5)

/-! ### Exactly-one chain gadget -/

/-- Exactly one of a Boolean list is true. -/
def exactlyOneOf (values : List Bool) : Prop :=
  (values.filter fun b => b).length = 1

theorem exactlyOneOf_singleton (value : Bool) :
    exactlyOneOf [value] ↔ value = true := by
  cases value <;> simp [exactlyOneOf]

theorem exactlyOneOf_cons_two (first second : Bool) :
    exactlyOneOf [first, second] ↔ first ≠ second := by
  cases first <;> cases second <;> simp [exactlyOneOf]

theorem exactlyOneOf_not_both (first second : Bool) (rest : List Bool) :
    exactlyOneOf (first :: second :: rest) → ¬ (first = true ∧ second = true) := by
  intro hexactlyOne hboth
  cases first <;> cases second <;> simp [exactlyOneOf] at hexactlyOne hboth

theorem exactlyOneOf_cons_of_orIndicator (first second : Bool) (rest : List Bool)
    (notBoth : ¬ (first = true ∧ second = true)) :
    exactlyOneOf ((first || second) :: rest) ↔ exactlyOneOf (first :: second :: rest) := by
  cases first <;> cases second <;> simp [exactlyOneOf] at notBoth ⊢

theorem exactlyOneOf_false_cons (rest : List Bool) :
    exactlyOneOf (false :: rest) ↔ exactlyOneOf rest := by
  cases rest with
  | nil => simp [exactlyOneOf]
  | cons value values => cases value <;> simp [exactlyOneOf]

/--
The exactly-one chain gadget: the block realizes "exactly one of
`chain :: xs` holds".  The chain variable is `blockChain level`; level `l`
uses auxiliary positions `5l .. 5l + 3` and hands the next chain over at
position `5(l+1) + 4`.
-/
noncomputable def exactlyOneBlock (setsLength element : Nat) (level chain : Nat) :
    List Nat → Formula oneInThreeCore
  | [] =>
      let p := auxiliaryVar setsLength element (5 * level)
      [oneInThreeConstraint chain p p]
  | [x] =>
      let a := auxiliaryVar setsLength element (5 * level)
      let b := auxiliaryVar setsLength element (5 * level + 1)
      [oneInThreeConstraint chain x a, oneInThreeConstraint b a a]
  | x :: rest =>
      let a := auxiliaryVar setsLength element (5 * level)
      let negA := blockChain setsLength element (level + 1)
      let c := auxiliaryVar setsLength element (5 * level + 2)
      let d := auxiliaryVar setsLength element (5 * level + 3)
      [ oneInThreeConstraint chain x a,
        oneInThreeConstraint a negA c,
        oneInThreeConstraint d c c ] ++
        exactlyOneBlock setsLength element (level + 1) negA rest

/-! ### Soundness of the chain gadget -/

/-- Soundness: a satisfying assignment gives exactly one true chain-list value. -/
theorem exactlyOneBlock_satisfies_of (setsLength element : Nat) :
    ∀ (level chain : Nat), ∀ (xs : List Nat),
    ∀ (assignment : SAT.Assignment),
    CSP.Formula.Satisfies (exactlyOneBlock setsLength element level chain xs) assignment →
      exactlyOneOf (assignment chain :: xs.map assignment) := by
  intro level chain
  intro xs
  induction xs generalizing level chain with
  | nil =>
      intro assignment satisfies
      have hpin := satisfies (oneInThreeConstraint chain
        (auxiliaryVar setsLength element (5 * level))
        (auxiliaryVar setsLength element (5 * level))) (by
          simp [exactlyOneBlock])
      have hchain : assignment chain = true :=
        oneInThree_pinTrue chain (auxiliaryVar setsLength element (5 * level))
          assignment hpin
      exact (exactlyOneOf_singleton (assignment chain)).2 hchain
  | cons x xs ih =>
      cases xs with
      | nil =>
          intro assignment satisfies
          have hmain := satisfies (oneInThreeConstraint chain x
            (auxiliaryVar setsLength element (5 * level))) (by
              simp [exactlyOneBlock])
          have hpin := satisfies (oneInThreeConstraint
            (auxiliaryVar setsLength element (5 * level + 1))
            (auxiliaryVar setsLength element (5 * level))
            (auxiliaryVar setsLength element (5 * level))) (by
              simp [exactlyOneBlock])
          have hneq := oneInThree_disequality_iff chain x
            (auxiliaryVar setsLength element (5 * level))
            (auxiliaryVar setsLength element (5 * level + 1))
            assignment ⟨hmain, hpin⟩
          exact (exactlyOneOf_cons_two (assignment chain) (assignment x)).2 hneq
      | cons y rest =>
          intro assignment satisfies
          let a := auxiliaryVar setsLength element (5 * level)
          let negA := blockChain setsLength element (level + 1)
          let c := auxiliaryVar setsLength element (5 * level + 2)
          let d := auxiliaryVar setsLength element (5 * level + 3)
          have hmain := satisfies (oneInThreeConstraint chain x a) (by
            simp [exactlyOneBlock, a, negA, c, d])
          have hneg : assignment negA = !assignment a :=
            (bool_ne_iff_eq_not (assignment a) (assignment negA)).1
              (oneInThree_disequality_iff a negA c d assignment
                ⟨satisfies (oneInThreeConstraint a negA c) (by
                  simp [exactlyOneBlock, a, negA, c, d]),
                  satisfies (oneInThreeConstraint d c c) (by
                    simp [exactlyOneBlock, a, negA, c, d])⟩)
          have htailSatisfies : CSP.Formula.Satisfies
              (exactlyOneBlock setsLength element (level + 1) negA (y :: rest)) assignment := by
            intro constraint constraintMember
            apply satisfies constraint
            change constraint ∈ [ oneInThreeConstraint chain x a,
              oneInThreeConstraint a negA c,
              oneInThreeConstraint d c c ] ++
              exactlyOneBlock setsLength element (level + 1) negA (y :: rest)
            exact List.mem_append.mpr (Or.inr constraintMember)
          have htail := ih (level + 1) negA assignment htailSatisfies
          have haVal : assignment a = (!assignment chain && !assignment x) := by
            have ha := (oneInThreeConstraint_satisfies_iff chain x a assignment).1 hmain
            cases hc : assignment chain <;> cases hx : assignment x <;>
              cases hv : assignment a <;> simp [hc, hx, hv] at ha ⊢
          have htail' : exactlyOneOf
              ((assignment chain || assignment x) :: (y :: rest).map assignment) := by
            rw [hneg, haVal] at htail
            simpa using htail
          cases hc : assignment chain <;> cases hx : assignment x
          · simpa [hc, hx] using htail'
          · simpa [hc, hx] using htail'
          · simpa [hc, hx] using htail'
          · have hmainSum := (oneInThreeConstraint_satisfies_iff chain x a assignment).1 hmain
            simp [hc, hx] at hmainSum
            omega

/-! ### Completeness of the chain gadget -/

/-- The block chain of level `level` never coincides with a gadget position of a
level at least `level`. -/
theorem blockChain_ne_auxiliary_position (level l k : Nat) (hl : level ≤ l) (hk : k ≤ 3) :
    5 * level + 4 ≠ 5 * l + k := by
  omega

/-- The canonical witness of one block level. -/
noncomputable def blockWitness (setsLength element : Nat) (level chain : Nat) :
    List Nat → SAT.Assignment → SAT.Assignment
  | [], base => fun var =>
      if var = auxiliaryVar setsLength element (5 * level) then false else base var
  | [x], base => fun var =>
      if var = auxiliaryVar setsLength element (5 * level) then false
      else if var = auxiliaryVar setsLength element (5 * level + 1) then true
      else base var
  | x :: rest, base =>
      blockWitness setsLength element (level + 1) (blockChain setsLength element (level + 1)) rest
        (fun var =>
          if var = auxiliaryVar setsLength element (5 * level) then
            !(base chain) && !(base x)
          else if var = blockChain setsLength element (level + 1) then
            !(!(base chain) && !(base x))
          else if var = auxiliaryVar setsLength element (5 * level + 2) then false
          else if var = auxiliaryVar setsLength element (5 * level + 3) then true
          else base var)

/--
The witness leaves every variable fresh for the block's levels unchanged.
A variable is fresh when it differs from all auxiliary positions of levels
`level .. level + xs.length` and from the block chains of the strictly higher
levels.
-/
theorem blockWitness_fresh (setsLength element : Nat) (level chain : Nat)
    (xs : List Nat) (base : SAT.Assignment) {var : Nat}
    (hfresh : ∀ l, level ≤ l → l ≤ level + xs.length →
      (∀ k ≤ 3, var ≠ auxiliaryVar setsLength element (5 * l + k)) ∧
        (level < l → var ≠ blockChain setsLength element l)) :
    blockWitness setsLength element level chain xs base var = base var := by
  induction xs generalizing level chain base with
  | nil =>
      have h0 : ¬ var = auxiliaryVar setsLength element (5 * level) :=
        (hfresh level le_rfl (Nat.le_add_right level ([].length))).1 0 (by decide)
      unfold blockWitness
      change (if var = auxiliaryVar setsLength element (5 * level) then false else base var) =
        base var
      rw [if_neg h0]
  | cons x xs ih =>
      cases xs with
      | nil =>
          have h0 : ¬ var = auxiliaryVar setsLength element (5 * level) :=
            (hfresh level le_rfl (Nat.le_add_right level [x].length)).1 0 (by decide)
          have h1 : ¬ var = auxiliaryVar setsLength element (5 * level + 1) :=
            (hfresh level le_rfl (Nat.le_add_right level [x].length)).1 1 (by decide)
          unfold blockWitness
          change (if var = auxiliaryVar setsLength element (5 * level) then false
            else if var = auxiliaryVar setsLength element (5 * level + 1) then true
            else base var) = base var
          rw [if_neg h0, if_neg h1]
      | cons y rest =>
          unfold blockWitness
          let newBase := fun var =>
            if var = auxiliaryVar setsLength element (5 * level) then
              !(base chain) && !(base x)
            else if var = blockChain setsLength element (level + 1) then
              !(!(base chain) && !(base x))
            else if var = auxiliaryVar setsLength element (5 * level + 2) then false
            else if var = auxiliaryVar setsLength element (5 * level + 3) then true
            else base var
          change blockWitness setsLength element (level + 1)
            (blockChain setsLength element (level + 1)) (y :: rest) newBase var = base var
          have hsub := ih (level + 1) (blockChain setsLength element (level + 1)) newBase (by
            intro l hl₁ hl₂
            have hl₁' : level ≤ l := Nat.le_trans (Nat.le_succ level) hl₁
            have hl₂' : l ≤ level + (x :: y :: rest).length := by
              change l ≤ level + ((y :: rest).length + 1)
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hl₂
            refine ⟨?_, ?_⟩
            · intro k hk
              exact (hfresh l hl₁' hl₂').1 k hk
            · intro hlt
              exact (hfresh l hl₁' hl₂').2 (Nat.lt_trans (Nat.lt_succ_self level) hlt))
          rw [hsub]
          unfold newBase
          change (if var = auxiliaryVar setsLength element (5 * level) then
              !(base chain) && !(base x)
            else if var = blockChain setsLength element (level + 1) then
              !(!(base chain) && !(base x))
            else if var = auxiliaryVar setsLength element (5 * level + 2) then false
            else if var = auxiliaryVar setsLength element (5 * level + 3) then true
            else base var) = base var
          have h0 : ¬ var = auxiliaryVar setsLength element (5 * level) :=
            (hfresh level le_rfl
              (Nat.le_add_right level (x :: y :: rest).length)).1 0 (by decide)
          have hchild : ¬ var = blockChain setsLength element (level + 1) :=
            (hfresh (level + 1) (Nat.le_succ level)
              (by
                change level + 1 ≤ level + ((y :: rest).length + 1)
                exact Nat.add_le_add_left (by omega : 1 ≤ (y :: rest).length + 1) level)).2
                (Nat.lt_succ_self level)
          have h2 : ¬ var = auxiliaryVar setsLength element (5 * level + 2) :=
            (hfresh level le_rfl
              (Nat.le_add_right level (x :: y :: rest).length)).1 2 (by decide)
          have h3 : ¬ var = auxiliaryVar setsLength element (5 * level + 3) :=
            (hfresh level le_rfl
              (Nat.le_add_right level (x :: y :: rest).length)).1 3 (by decide)
          rw [if_neg h0, if_neg hchild, if_neg h2, if_neg h3]

/--
The witness keeps the chain variable's base value at this level.
-/
theorem blockWitness_chain (setsLength element : Nat) (level : Nat)
    (xs : List Nat) (base : SAT.Assignment) :
    blockWitness setsLength element level (blockChain setsLength element level) xs base
      (blockChain setsLength element level) = base (blockChain setsLength element level) := by
  let chain := blockChain setsLength element level
  change blockWitness setsLength element level chain xs base chain = base chain
  apply blockWitness_fresh
  intro l hl₁ hl₂
  refine ⟨?_, ?_⟩
  · intro k hk
    intro hEq
    exact auxiliaryVar_ne_of_position_ne setsLength element
      (blockChain_ne_auxiliary_position level l k hl₁ hk) (by
        simpa [chain, blockChain] using hEq)
  · intro hlt
    intro hEq
    have hpos : l = level := by
      have hinj := auxiliaryVar_injective setsLength (show
        (fun input : Nat × Nat => auxiliaryVar setsLength input.1 input.2)
            (element, 5 * level + 4) =
          (fun input : Nat × Nat => auxiliaryVar setsLength input.1 input.2)
            (element, 5 * l + 4) from by
        simpa [chain, blockChain] using hEq)
      have hmul : 5 * level = 5 * l := Nat.add_right_cancel (congrArg Prod.snd hinj)
      exact (Nat.mul_left_cancel (by decide : 0 < 5) hmul).symm
    omega

/-- The witness leaves set-index variables unchanged. -/
theorem blockWitness_smallVar (setsLength element : Nat) (level chain : Nat)
    (xs : List Nat) (base : SAT.Assignment) {var : Nat} (hsmall : var < setsLength) :
    blockWitness setsLength element level chain xs base var = base var := by
  apply blockWitness_fresh
  intro l hl₁ hl₂
  refine ⟨?_, ?_⟩
  · intro k hk
    intro hEq
    dsimp only [auxiliaryVar] at hEq
    omega
  · intro _hlt
    intro hEq
    dsimp only [blockChain, auxiliaryVar] at hEq
    omega

/--
The fresh premise for a fixed parent-level auxiliary position: it lies below
every child block position and every child chain.
-/
theorem auxVar_fresh_premise (setsLength element level length position : Nat)
    (hposition : position < 5 * (level + 1)) :
    ∀ l, level + 1 ≤ l → l ≤ level + 1 + length →
      (∀ k ≤ 3, auxiliaryVar setsLength element position ≠ auxiliaryVar setsLength element (5 * l + k)) ∧
        (level + 1 < l → auxiliaryVar setsLength element position ≠ blockChain setsLength element l) := by
  intro l hl₁ hl₂
  refine ⟨?_, ?_⟩
  · intro _k _hk
    exact auxiliaryVar_ne_of_position_ne setsLength element (by omega)
  · intro _hlt
    exact auxiliaryVar_ne_of_position_ne setsLength element (by omega)



theorem blockWitness_satisfies (setsLength element : Nat) :
    ∀ (level : Nat), ∀ (xs : List Nat), ∀ (base : SAT.Assignment),
    (∀ x ∈ xs, x < setsLength) →
    exactlyOneOf (base (blockChain setsLength element level) :: xs.map base) →
      CSP.Formula.Satisfies (exactlyOneBlock setsLength element level
          (blockChain setsLength element level) xs)
        (blockWitness setsLength element level (blockChain setsLength element level) xs base) := by
  intro level
  intro xs base hsmall
  induction xs generalizing level base with
  | nil =>
      intro hexactlyOne
      intro constraint constraintMember
      rcases List.mem_cons.mp constraintMember with rfl | h'
      · rw [oneInThreeConstraint_satisfies_iff]
        have hchain : base (blockChain setsLength element level) = true :=
          (exactlyOneOf_singleton (base (blockChain setsLength element level))).1 hexactlyOne
        have hchainVal := blockWitness_chain setsLength element level [] base
        have hpinVal : blockWitness setsLength element level (blockChain setsLength element level)
            [] base (auxiliaryVar setsLength element (5 * level)) = false := by
          unfold blockWitness
          rw [if_pos rfl]
        simp [hchainVal, hpinVal, hchain]
      · cases h'
  | cons x xs ih =>
      cases xs with
      | nil =>
          intro hexactlyOne
          intro constraint constraintMember
          rcases List.mem_cons.mp constraintMember with rfl | h'
          · rw [oneInThreeConstraint_satisfies_iff]
            have hneq : base (blockChain setsLength element level) ≠ base x :=
              (exactlyOneOf_cons_two (base (blockChain setsLength element level)) (base x)).1
                hexactlyOne
            have hchainVal := blockWitness_chain setsLength element level [x] base
            have hxVal : blockWitness setsLength element level (blockChain setsLength element level)
                [x] base x = base x := by
              apply blockWitness_smallVar
              exact hsmall x (by simp)
            have haVal : blockWitness setsLength element level (blockChain setsLength element level)
                [x] base (auxiliaryVar setsLength element (5 * level)) = false := by
              unfold blockWitness
              rw [if_pos rfl]
            have hsum : (if base (blockChain setsLength element level) then 1 else 0) +
                (if base x then 1 else 0) +
                (if false then 1 else 0) = 1 := by
              cases hc : base (blockChain setsLength element level) <;> cases hx : base x
              · have hcontra : False := hneq (by simpa [hc, hx])
                exact False.elim hcontra
              · simp [hc, hx]
              · simp [hc, hx]
              · have hcontra : False := hneq (by simpa [hc, hx])
                exact False.elim hcontra
            simpa [hchainVal, hxVal, haVal, hsum]
          · rcases List.mem_cons.mp h' with rfl | h''
            · rw [oneInThreeConstraint_satisfies_iff]
              have hbVal : blockWitness setsLength element level (blockChain setsLength element level)
                  [x] base (auxiliaryVar setsLength element (5 * level + 1)) = true := by
                unfold blockWitness
                rw [if_neg, if_pos rfl]
                exact auxiliaryVar_ne_of_position_ne setsLength element
                  (by omega : 5 * level + 1 ≠ 5 * level)
              have haVal : blockWitness setsLength element level (blockChain setsLength element level)
                  [x] base (auxiliaryVar setsLength element (5 * level)) = false := by
                unfold blockWitness
                rw [if_pos rfl]
              simp [hbVal, haVal]
            · cases h''
      | cons y rest =>
          intro hexactlyOne
          intro constraint constraintMember
          let a := auxiliaryVar setsLength element (5 * level)
          let negA := blockChain setsLength element (level + 1)
          let c := auxiliaryVar setsLength element (5 * level + 2)
          let d := auxiliaryVar setsLength element (5 * level + 3)
          let aVal := !(base (blockChain setsLength element level)) && !(base x)
          let newBase := fun var =>
            if var = a then aVal
            else if var = negA then !aVal
            else if var = c then false
            else if var = d then true
            else base var
          have hnotBoth : ¬ (base (blockChain setsLength element level) = true ∧ base x = true) :=
            exactlyOneOf_not_both (base (blockChain setsLength element level)) (base x)
              ((y :: rest).map base) hexactlyOne
          have htailPre : exactlyOneOf (newBase negA :: (y :: rest).map newBase) := by
            have hnewBaseNegA : newBase negA = !aVal := by
              unfold newBase negA aVal
              rw [if_neg, if_pos rfl]
              exact auxiliaryVar_ne_of_position_ne setsLength element
                (by omega : 5 * (level + 1) + 4 ≠ 5 * level)
            have hrest : (y :: rest).map newBase = (y :: rest).map base := by
              apply List.map_congr_left
              intro var hvar
              have hsmallVar : var < setsLength := hsmall var (by simp [hvar])
              have h1 : ¬ var = a := by
                intro hEq
                dsimp only [a, auxiliaryVar] at hEq
                omega
              have h2 : ¬ var = negA := by
                intro hEq
                dsimp only [negA, blockChain, auxiliaryVar] at hEq
                omega
              have h3 : ¬ var = c := by
                intro hEq
                dsimp only [c, auxiliaryVar] at hEq
                omega
              have h4 : ¬ var = d := by
                intro hEq
                dsimp only [d, auxiliaryVar] at hEq
                omega
              unfold newBase
              rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
            have hpre : exactlyOneOf
                ((base (blockChain setsLength element level) || base x) :: (y :: rest).map base) :=
              (exactlyOneOf_cons_of_orIndicator (base (blockChain setsLength element level)) (base x)
                ((y :: rest).map base) hnotBoth).2 hexactlyOne
            rw [hnewBaseNegA, hrest]
            simpa [aVal] using hpre
          have htailSatisfies := ih (level + 1) newBase
            (fun v hv => hsmall v (by simp [hv])) htailPre
          rcases List.mem_append.mp constraintMember with inHead | inTail
          · rcases List.mem_cons.mp inHead with rfl | h2
            · rw [oneInThreeConstraint_satisfies_iff]
              have hchainVal := blockWitness_chain setsLength element level (x :: y :: rest) base
              have hxVal : blockWitness setsLength element level
                  (blockChain setsLength element level) (x :: y :: rest) base x = base x := by
                have hxSmall : x < setsLength := hsmall x (by simp)
                unfold blockWitness
                change blockWitness setsLength element (level + 1) negA (y :: rest) newBase x =
                  base x
                rw [show blockWitness setsLength element (level + 1) negA (y :: rest) newBase x =
                    newBase x from blockWitness_smallVar setsLength element (level + 1) negA
                      (y :: rest) newBase hxSmall]
                have h1 : ¬ x = a := by
                  intro hEq
                  dsimp only [a, auxiliaryVar] at hEq
                  omega
                have h2 : ¬ x = negA := by
                  intro hEq
                  dsimp only [negA, blockChain, auxiliaryVar] at hEq
                  omega
                have h3 : ¬ x = c := by
                  intro hEq
                  dsimp only [c, auxiliaryVar] at hEq
                  omega
                have h4 : ¬ x = d := by
                  intro hEq
                  dsimp only [d, auxiliaryVar] at hEq
                  omega
                unfold newBase
                rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
              have haVal' : blockWitness setsLength element level
                  (blockChain setsLength element level) (x :: y :: rest) base a = aVal := by
                unfold blockWitness
                change blockWitness setsLength element (level + 1) negA (y :: rest) newBase a = aVal
                rw [show blockWitness setsLength element (level + 1) negA (y :: rest) newBase a =
                    newBase a from
                  blockWitness_fresh setsLength element (level + 1) negA
                    (y :: rest) newBase (auxVar_fresh_premise setsLength element level
                      (y :: rest).length (5 * level) (by omega))]
                unfold newBase
                rw [if_pos rfl]
              have hsum : (if base (blockChain setsLength element level) then 1 else 0) +
                  (if base x then 1 else 0) +
                  (if aVal then 1 else 0) = 1 := by
                cases hc : base (blockChain setsLength element level) <;> cases hx : base x
                · unfold aVal
                  simp [hc, hx]
                · unfold aVal
                  simp [hc, hx]
                · unfold aVal
                  simp [hc, hx]
                · exact False.elim (hnotBoth ⟨hc, hx⟩)
              rw [hchainVal, hxVal, haVal']
              exact hsum
            · rcases List.mem_cons.mp h2 with rfl | h3
              · rw [oneInThreeConstraint_satisfies_iff]
                have haVal' : blockWitness setsLength element level
                    (blockChain setsLength element level) (x :: y :: rest) base a = aVal := by
                  unfold blockWitness
                  change blockWitness setsLength element (level + 1) negA (y :: rest) newBase a = aVal
                  rw [show blockWitness setsLength element (level + 1) negA (y :: rest) newBase a =
                      newBase a from
                    blockWitness_fresh setsLength element (level + 1) negA
                      (y :: rest) newBase (auxVar_fresh_premise setsLength element level
                        (y :: rest).length (5 * level) (by omega))]
                  unfold newBase
                  rw [if_pos rfl]
                have hnegVal : blockWitness setsLength element level
                    (blockChain setsLength element level) (x :: y :: rest) base negA = !aVal := by
                  unfold blockWitness
                  change blockWitness setsLength element (level + 1) negA (y :: rest) newBase negA =
                    !aVal
                  rw [show blockWitness setsLength element (level + 1) negA (y :: rest) newBase negA =
                      newBase negA from
                    blockWitness_chain setsLength element (level + 1)
                      (y :: rest) newBase]
                  unfold newBase
                  rw [if_neg, if_pos rfl]
                  exact auxiliaryVar_ne_of_position_ne setsLength element
                    (by omega : 5 * (level + 1) + 4 ≠ 5 * level)
                have hcVal : blockWitness setsLength element level
                    (blockChain setsLength element level) (x :: y :: rest) base c = false := by
                  unfold blockWitness
                  change blockWitness setsLength element (level + 1) negA (y :: rest) newBase c = false
                  rw [show blockWitness setsLength element (level + 1) negA (y :: rest) newBase c =
                      newBase c from
                    blockWitness_fresh setsLength element (level + 1) negA
                      (y :: rest) newBase (auxVar_fresh_premise setsLength element level
                        (y :: rest).length (5 * level + 2) (by omega))]
                  unfold newBase
                  rw [if_neg, if_neg, if_pos rfl]
                  · exact auxiliaryVar_ne_of_position_ne setsLength element
                      (by omega : 5 * level + 2 ≠ 5 * (level + 1) + 4)
                  · exact auxiliaryVar_ne_of_position_ne setsLength element
                      (by omega : 5 * level + 2 ≠ 5 * level)
                have hsum : (if aVal then 1 else 0) + (if !aVal then 1 else 0) +
                    (if false then 1 else 0) = 1 := by
                  cases aVal <;> decide
                rw [haVal', hnegVal, hcVal]
                exact hsum
              · rcases List.mem_cons.mp h3 with rfl | h4
                · rw [oneInThreeConstraint_satisfies_iff]
                  have hdVal : blockWitness setsLength element level
                      (blockChain setsLength element level) (x :: y :: rest) base d = true := by
                    unfold blockWitness
                    change blockWitness setsLength element (level + 1) negA (y :: rest) newBase d = true
                    rw [show blockWitness setsLength element (level + 1) negA (y :: rest) newBase d =
                        newBase d from
                      blockWitness_fresh setsLength element (level + 1) negA
                        (y :: rest) newBase (auxVar_fresh_premise setsLength element level
                          (y :: rest).length (5 * level + 3) (by omega))]
                    unfold newBase
                    rw [if_neg, if_neg, if_neg, if_pos rfl]
                    · exact auxiliaryVar_ne_of_position_ne setsLength element
                        (by omega : 5 * level + 3 ≠ 5 * level + 2)
                    · exact auxiliaryVar_ne_of_position_ne setsLength element
                        (by omega : 5 * level + 3 ≠ 5 * (level + 1) + 4)
                    · exact auxiliaryVar_ne_of_position_ne setsLength element
                        (by omega : 5 * level + 3 ≠ 5 * level)
                  have hcVal : blockWitness setsLength element level
                      (blockChain setsLength element level) (x :: y :: rest) base c = false := by
                    unfold blockWitness
                    change blockWitness setsLength element (level + 1) negA (y :: rest) newBase c = false
                    rw [show blockWitness setsLength element (level + 1) negA (y :: rest) newBase c =
                        newBase c from
                      blockWitness_fresh setsLength element (level + 1) negA
                        (y :: rest) newBase (auxVar_fresh_premise setsLength element level
                          (y :: rest).length (5 * level + 2) (by omega))]
                    unfold newBase
                    rw [if_neg, if_neg, if_pos rfl]
                    · exact auxiliaryVar_ne_of_position_ne setsLength element
                        (by omega : 5 * level + 2 ≠ 5 * (level + 1) + 4)
                    · exact auxiliaryVar_ne_of_position_ne setsLength element
                        (by omega : 5 * level + 2 ≠ 5 * level)
                  rw [hdVal, hcVal]
                  decide
                · cases h4
          · exact htailSatisfies constraint inTail
/-! ### The element block -/

/-- No block variable collides with the element pin variable. -/
theorem block_vars_ne_pin (setsLength element level length : Nat) (xs : List Nat)
    (hbound : level + xs.length ≤ length) (hsmall : ∀ x ∈ xs, x < setsLength) :
    ∀ d ∈ exactlyOneBlock setsLength element level (blockChain setsLength element level) xs,
    ∀ i, d.vars i ≠ elementPin setsLength element length := by
  induction xs generalizing level with
  | nil =>
      have hlevel : level ≤ length := by simpa using hbound
      intro d dMember i
      rcases List.mem_cons.mp dMember with rfl | h'
      · fin_cases i
        · intro hEq
          exact auxiliaryVar_ne_of_position_ne setsLength element
            (by omega : 5 * level + 4 ≠ 5 * length + 5)
            (by simpa [blockChain, elementPin] using hEq)
        · intro hEq
          exact auxiliaryVar_ne_of_position_ne setsLength element
            (by omega : 5 * level ≠ 5 * length + 5)
            (by simpa [elementPin] using hEq)
        · intro hEq
          exact auxiliaryVar_ne_of_position_ne setsLength element
            (by omega : 5 * level ≠ 5 * length + 5)
            (by simpa [elementPin] using hEq)
      · cases h'
  | cons x xs ih =>
      cases xs with
      | nil =>
          have hlevel : level ≤ length := Nat.le_trans (Nat.le_succ level) (by simpa using hbound)
          intro d dMember i
          rcases List.mem_cons.mp dMember with rfl | h'
          · fin_cases i
            · intro hEq
              exact auxiliaryVar_ne_of_position_ne setsLength element
                (by omega : 5 * level + 4 ≠ 5 * length + 5)
                (by simpa [blockChain, elementPin] using hEq)
            · intro hEq
              have hxv : x < setsLength := hsmall x (by simp)
              exact (Nat.ne_of_lt (Nat.lt_trans hxv
                (setsLength_lt_auxiliaryVar setsLength element (5 * length + 5)))) hEq
            · intro hEq
              exact auxiliaryVar_ne_of_position_ne setsLength element
                (by omega : 5 * level ≠ 5 * length + 5)
                (by simpa [elementPin] using hEq)
          · rcases List.mem_cons.mp h' with rfl | h''
            · fin_cases i
              · intro hEq
                exact auxiliaryVar_ne_of_position_ne setsLength element
                  (by omega : 5 * level + 1 ≠ 5 * length + 5)
                  (by simpa [elementPin] using hEq)
              · intro hEq
                exact auxiliaryVar_ne_of_position_ne setsLength element
                  (by omega : 5 * level ≠ 5 * length + 5)
                  (by simpa [elementPin] using hEq)
              · intro hEq
                exact auxiliaryVar_ne_of_position_ne setsLength element
                  (by omega : 5 * level ≠ 5 * length + 5)
                  (by simpa [elementPin] using hEq)
            · cases h''
      | cons y rest =>
          have hlevel : level ≤ length :=
            Nat.le_trans (Nat.le_add_right level (x :: y :: rest).length) hbound
          have hbound' : (level + 1) + (y :: rest).length ≤ length := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbound
          intro d dMember i
          rcases List.mem_append.mp dMember with inHead | inTail
          · rcases List.mem_cons.mp inHead with rfl | h2
            · fin_cases i
              · intro hEq
                exact auxiliaryVar_ne_of_position_ne setsLength element
                  (by omega : 5 * level + 4 ≠ 5 * length + 5)
                  (by simpa [blockChain, elementPin] using hEq)
              · intro hEq
                have hxv : x < setsLength := hsmall x (by simp)
                exact (Nat.ne_of_lt (Nat.lt_trans hxv
                  (setsLength_lt_auxiliaryVar setsLength element (5 * length + 5)))) hEq
              · intro hEq
                exact auxiliaryVar_ne_of_position_ne setsLength element
                  (by omega : 5 * level ≠ 5 * length + 5)
                  (by simpa [elementPin] using hEq)
            · rcases List.mem_cons.mp h2 with rfl | h3
              · fin_cases i
                · intro hEq
                  exact auxiliaryVar_ne_of_position_ne setsLength element
                    (by omega : 5 * level ≠ 5 * length + 5)
                    (by simpa [elementPin] using hEq)
                · intro hEq
                  exact auxiliaryVar_ne_of_position_ne setsLength element
                    (by omega : 5 * (level + 1) + 4 ≠ 5 * length + 5)
                    (by simpa [blockChain, elementPin] using hEq)
                · intro hEq
                  exact auxiliaryVar_ne_of_position_ne setsLength element
                    (by omega : 5 * level + 2 ≠ 5 * length + 5)
                    (by simpa [elementPin] using hEq)
              · rcases List.mem_cons.mp h3 with rfl | h4
                · fin_cases i
                  · intro hEq
                    exact auxiliaryVar_ne_of_position_ne setsLength element
                      (by omega : 5 * level + 3 ≠ 5 * length + 5)
                      (by simpa [elementPin] using hEq)
                  · intro hEq
                    exact auxiliaryVar_ne_of_position_ne setsLength element
                      (by omega : 5 * level + 2 ≠ 5 * length + 5)
                      (by simpa [elementPin] using hEq)
                  · intro hEq
                    exact auxiliaryVar_ne_of_position_ne setsLength element
                      (by omega : 5 * level + 2 ≠ 5 * length + 5)
                      (by simpa [elementPin] using hEq)
                · cases h4
          · exact ih (level + 1) hbound'
              (fun v hv => hsmall v (by simp [hv])) d inTail i

/-- Assignments agreeing on the variables of every constraint satisfy the same formulas. -/
theorem formula_satisfies_of_vars_agree {Γ : Gamma} {φ : Formula Γ} {a b : SAT.Assignment}
    (agree : ∀ d ∈ φ, ∀ i, a (d.vars i) = b (d.vars i)) :
    Satisfies φ b → Satisfies φ a := by
  intro hb d hd
  have htuple : Constraint.assignmentTuple d a = Constraint.assignmentTuple d b := by
    funext i
    exact agree d hd i
  have hd' := hb d hd
  change (Γ.relationOf d.symbol).Holds (Constraint.assignmentTuple d a)
  rw [htuple]
  exact hd'

/-- The complete exact-cover-to-1-in-3 block for one universe element. -/
noncomputable def elementBlock (setsLength element : Nat) (indices : List Nat) :
    Formula oneInThreeCore :=
  [oneInThreeConstraint (elementPin setsLength element indices.length)
    (blockChain setsLength element 0) (blockChain setsLength element 0)] ++
  exactlyOneBlock setsLength element 0 (blockChain setsLength element 0) indices

/-- The indices of the sets containing one universe element. -/
def indicesOf (sets : List (List Nat)) (element : Nat) : List Nat :=
  ((List.range sets.length).zip sets).filterMap fun entry =>
    if element ∈ entry.2 then some entry.1 else none

/-- Soundness: a satisfied element block selects exactly one index. -/
theorem elementBlock_satisfies_of (setsLength element : Nat) (indices : List Nat)
    (assignment : SAT.Assignment) :
    CSP.Formula.Satisfies (elementBlock setsLength element indices) assignment →
      exactlyOneOf (indices.map assignment) := by
  intro satisfies
  let chain := blockChain setsLength element 0
  let p := elementPin setsLength element indices.length
  have hpin := satisfies (oneInThreeConstraint p chain chain) (by
    simp [elementBlock, chain, p])
  have hchain : assignment chain = false :=
    oneInThree_pinFalse chain p assignment hpin
  have hblock : CSP.Formula.Satisfies
      (exactlyOneBlock setsLength element 0 chain indices) assignment := by
    intro constraint constraintMember
    apply satisfies constraint
    change constraint ∈ [oneInThreeConstraint p chain chain] ++
      exactlyOneBlock setsLength element 0 chain indices
    exact List.mem_append.mpr (Or.inr constraintMember)
  have hexactlyOne := exactlyOneBlock_satisfies_of setsLength element 0 chain
    indices assignment hblock
  have hrewrite : assignment chain :: indices.map assignment =
      false :: indices.map assignment := by
    rw [hchain]
  have hresult : exactlyOneOf (false :: indices.map assignment) := by
    simpa [hrewrite] using hexactlyOne
  exact (exactlyOneOf_false_cons (indices.map assignment)).1 hresult

/-- The canonical witness of one element block. -/
noncomputable def elementWitness (setsLength element : Nat) (indices : List Nat)
    (selection : SAT.Assignment) : SAT.Assignment :=
  let chain := blockChain setsLength element 0
  let p := elementPin setsLength element indices.length
  let base := fun var => if var = chain then false else selection var
  let inner := blockWitness setsLength element 0 chain indices base
  fun var => if var = p then true else inner var

/-- Completeness: exactly one selected index yields a satisfying element witness. -/
theorem elementBlock_witness_satisfies (setsLength element : Nat) (indices : List Nat)
    (selection : SAT.Assignment) (hsmall : ∀ x ∈ indices, x < setsLength)
    (h : exactlyOneOf (indices.map selection)) :
    CSP.Formula.Satisfies (elementBlock setsLength element indices)
      (elementWitness setsLength element indices selection) := by
  intro constraint constraintMember
  let chain := blockChain setsLength element 0
  let p := elementPin setsLength element indices.length
  let base := fun var => if var = chain then false else selection var
  let inner := blockWitness setsLength element 0 chain indices base
  rcases List.mem_append.mp constraintMember with inPin | inBlock
  · rcases List.mem_cons.mp inPin with rfl | h'
    · rw [oneInThreeConstraint_satisfies_iff]
      have hpVal : elementWitness setsLength element indices selection p = true := by
        unfold elementWitness p
        rw [if_pos rfl]
      have hchainVal : elementWitness setsLength element indices selection chain = false := by
        unfold elementWitness chain
        have hchainP : ¬ chain = p := by
          intro hEq
          exact auxiliaryVar_ne_of_position_ne setsLength element
            (by omega : 5 * 0 + 4 ≠ 5 * indices.length + 5) (by
              simpa [chain, p, blockChain, elementPin] using hEq)
        rw [if_neg hchainP]
        change blockWitness setsLength element 0 chain indices base chain = false
        rw [show blockWitness setsLength element 0 chain indices base chain = base chain from
          blockWitness_chain setsLength element 0 indices base]
        unfold base
        rw [if_pos rfl]
      rw [hpVal, hchainVal]
      decide
    · cases h'
  · have hpre : exactlyOneOf (base chain :: indices.map base) := by
      have hbaseChain : base chain = false := by
        unfold base
        rw [if_pos rfl]
      have hbaseRest : indices.map base = indices.map selection := by
        apply List.map_congr_left
        intro var hvar
        have hsmallVar : var < setsLength := hsmall var (by simp [hvar])
        unfold base
        rw [if_neg]
        intro hEq
        dsimp only [chain, blockChain, auxiliaryVar] at hEq
        omega
      rw [hbaseChain, hbaseRest]
      exact (exactlyOneOf_false_cons (indices.map selection)).2 h
    have hwitness := blockWitness_satisfies setsLength element 0 indices base hsmall hpre
    have hinner : CSP.Formula.Satisfies
        (exactlyOneBlock setsLength element 0 chain indices)
        (elementWitness setsLength element indices selection) := by
      apply formula_satisfies_of_vars_agree
      · intro d dMember i
        unfold elementWitness
        rw [if_neg]
        intro hEq
        exact block_vars_ne_pin setsLength element 0 indices.length indices
          (by omega) hsmall d dMember i hEq
      · exact hwitness
    exact hinner constraint inBlock

/-! ### The exact-cover executable -/

/-- A contradictory block for ill-formed inputs. -/
noncomputable def contradictionBlock (var : Nat) : Formula oneInThreeCore :=
  [ oneInThreeConstraint var (var + 1) (var + 1),
    oneInThreeConstraint (var + 2) var var ]

theorem contradictionBlock_unsatisfiable (var : Nat) (assignment : SAT.Assignment) :
    ¬ Satisfies (contradictionBlock var) assignment := by
  intro h
  have hpinTrue := h (oneInThreeConstraint var (var + 1) (var + 1)) (by
    simp [contradictionBlock])
  have hpinFalse := h (oneInThreeConstraint (var + 2) var var) (by
    simp [contradictionBlock])
  have htrue : assignment var = true := oneInThree_pinTrue var (var + 1) assignment hpinTrue
  have hfalse : assignment var = false := oneInThree_pinFalse var (var + 2) assignment hpinFalse
  simp [htrue] at hfalse

/-- The complete executable: one block per universe element over the deduplicated family. -/
noncomputable def executable (I : ExactCoverInput) : Formula oneInThreeCore := by
  classical
  exact
    if wellFormed : SetSystemWellFormed I.system then
      (let sets := I.system.sets.eraseDups
       (List.range I.system.universeSize).flatMap fun element =>
         elementBlock sets.length element (indicesOf sets element))
    else contradictionBlock I.system.sets.length
