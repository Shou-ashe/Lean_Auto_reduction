/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP.CSPInstance
import ComplexityReduction.Domain.BooleanCSP.Relation
import ComplexityReduction.Presentation.FiniteDomainCSPTable
import ComplexityReduction.Certificate.Reduction
import ComplexityReduction.Certificate.CompletenessTransport
import ComplexityReduction.Certificate.Path
import ComplexityReduction.Legacy.ComplexityReduction.SAT.Literal

/-!
Primitive-positive definability and hardness transport.

Schaefer's hardness proof proceeds by primitive-positive definability: a
relation `R` is pp-definable from `Γ` when some Γ-formula with fresh
auxiliary variables realizes `R` on its distinguished output variables.  The
six tractability classes are all closed under pp-definitions, so every
non-tractable Γ pp-defines one of a finite set of hard cores; conversely,
substituting the defining gadgets turns every core formula into a Γ-formula,
witnessing a many-one reduction `CSP(core) ≤ₘ CSP(Γ)`.

This module fixes the exact gadget substitution used by the library:

* `Gadget Γ R` stores one Γ-formula together with its injective output
  variables and the semantic law `R(t) ↔ ∃ a, formula ∧ a(outputs) = t`.
* `LanguageInterpretation Γ' Γ` interprets every relation symbol of `Γ'` by a
  Γ-gadget.
* `interpret` substitutes every constraint of a `Γ'`-formula by its gadget,
  renaming auxiliary variables to fresh keys above the formula's maximum
  variable, so distinct gadgets never share auxiliary variables.
* The substitution preserves satisfiability in both directions, and with a
  direct-TM witness it assembles into a `CertifiedReduction (cspOf Γ') (cspOf Γ)`,
  hence transports `NativeTMNPHard` along the interpretation.
-/

namespace ComplexityReduction
namespace Domain
namespace BooleanCSP
namespace Hardness

open ComplexityReduction.CSP
open ComplexityReduction.Encoding

/-! ### Primitive-positive definitions -/

/-- A pp-definition of one Boolean relation from a finite language Γ. -/
structure Gadget (Γ : Gamma) (relation : BooleanRelation) where
  /-- The defining Γ-formula. -/
  formula : CSP.Formula Γ
  /-- The distinguished output variables. -/
  outputs : Fin relation.arity → Nat
  /-- Distinct output positions select distinct variables. -/
  outputs_injective : Function.Injective outputs
  /-- The formula realizes exactly the relation on its output variables. -/
  correct : ∀ tuple : BooleanTuple relation.arity,
    relation.Holds tuple ↔ ∃ assignment : SAT.Assignment,
      CSP.Formula.Satisfies formula assignment ∧
        ∀ i, assignment (outputs i) = tuple i

/-- `R` is primitive-positively definable from `Γ`. -/
def PPDefines (Γ : Gamma) (relation : BooleanRelation) : Prop :=
  Nonempty (Gadget Γ relation)

/-- Every relation symbol of `Γ'` is interpreted by a Γ-gadget. -/
structure LanguageInterpretation (Γ' Γ : Gamma) where
  gadgetOf : (symbol : Γ'.Symbol) → Gadget Γ (Γ'.relationOf symbol)

/-! ### Constraint keys and fresh auxiliary variables -/

/-- Injective Nat encoding of a variable list. -/
def listPairEncode : List Nat → Nat
  | [] => 0
  | x :: xs => Nat.pair x (listPairEncode xs) + 1

theorem listPairEncode_injective : Function.Injective listPairEncode := by
  intro left right equality
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons _ _ => simp [listPairEncode] at equality
  | cons x xs ih =>
      cases right with
      | nil => simp [listPairEncode] at equality
      | cons y ys =>
          simp [listPairEncode] at equality
          cases equality.1
          cases ih equality.2
          rfl

/-- Injectivity of `List.ofFn` recovers a variable tuple from its list code. -/
private theorem list_ofFn_injective {α : Type} {n : Nat} :
    Function.Injective (List.ofFn : (Fin n → α) → List α) := by
  intro left right equality
  funext index
  have entryEquality := congrArg (fun values : List α => values[index.val]?) equality
  simpa [List.getElem?_ofFn, index.isLt] using entryEquality

/-- An injective Nat key of one Γ' constraint. -/
noncomputable def constraintKey {Γ' : Gamma} (constraint : Constraint Γ') : Nat :=
  Nat.pair (Presentation.FiniteDomainCSPTable.relationCode Γ' constraint.symbol)
    (listPairEncode constraint.varsList)

theorem constraintKey_injective {Γ' : Gamma} :
    Function.Injective (@constraintKey Γ') := by
  intro left right equality
  rcases left with ⟨leftSymbol, leftVars⟩
  rcases right with ⟨rightSymbol, rightVars⟩
  have pairEq := Nat.pair_eq_pair.mp equality
  have symbolEq : leftSymbol = rightSymbol :=
    Presentation.FiniteDomainCSPTable.relationCode_injective Γ' pairEq.1
  cases symbolEq
  have varsEq : leftVars = rightVars :=
    list_ofFn_injective (listPairEncode_injective pairEq.2)
  cases varsEq
  rfl

/-- The fresh auxiliary variable of one gadget occurrence. -/
noncomputable def freshVar {Γ' : Gamma} (reference : Nat) (constraint : Constraint Γ')
    (gadgetVar : Nat) : Nat :=
  reference + Nat.pair (constraintKey constraint) gadgetVar + 1

theorem freshVar_above_reference {Γ' : Gamma} (reference : Nat)
    (constraint : Constraint Γ') (gadgetVar : Nat) :
    reference < freshVar reference constraint gadgetVar := by
  unfold freshVar
  omega

theorem freshVar_injective {Γ' : Gamma} (reference : Nat) :
    Function.Injective (fun input : Constraint Γ' × Nat =>
      freshVar reference input.1 input.2) := by
  rintro ⟨leftConstraint, leftVar⟩ ⟨rightConstraint, rightVar⟩ equality
  have pairConj : constraintKey leftConstraint = constraintKey rightConstraint ∧
      leftVar = rightVar := by
    have freshEq : reference + Nat.pair (constraintKey leftConstraint) leftVar + 1 =
        reference + Nat.pair (constraintKey rightConstraint) rightVar + 1 := by
      simpa [freshVar] using equality
    have pairOfPairs : Nat.pair (constraintKey leftConstraint) leftVar =
        Nat.pair (constraintKey rightConstraint) rightVar := by
      omega
    exact Nat.pair_eq_pair.mp pairOfPairs
  have constraintEq : leftConstraint = rightConstraint :=
    constraintKey_injective pairConj.1
  have varEq : leftVar = rightVar := pairConj.2
  cases constraintEq
  cases varEq
  rfl

/-! ### Gadget instantiation -/

/-- Map one gadget variable to its instantiated target key. -/
noncomputable def instantiateVar {Γ' Γ : Gamma} (interpretation : LanguageInterpretation Γ' Γ)
    (reference : Nat) (constraint : Constraint Γ') (var : Nat) : Nat :=
  let gadget := interpretation.gadgetOf constraint.symbol
  if h : var ∈ Set.range gadget.outputs then
    constraint.vars (Classical.choose h)
  else freshVar reference constraint var

/-- Instantiate one gadget at one source constraint. -/
noncomputable def instantiate {Γ' Γ : Gamma} (interpretation : LanguageInterpretation Γ' Γ)
    (reference : Nat) (constraint : Constraint Γ') : CSP.Formula Γ :=
  (interpretation.gadgetOf constraint.symbol).formula.map fun d =>
    { symbol := d.symbol
      vars := fun j => instantiateVar interpretation reference constraint (d.vars j) }

/-- Interpret every constraint of a Γ'-formula by its gadget. -/
noncomputable def interpret {Γ' Γ : Gamma} (interpretation : LanguageInterpretation Γ' Γ)
    (formula : CSP.Formula Γ') : CSP.Formula Γ :=
  let reference := CSP.Formula.maxVar formula
  formula.flatMap (instantiate interpretation reference)

/-! ### Variable bounds -/

/-- Every constraint variable occurs in the constraint's variable list. -/
theorem vars_mem_varsList {Γ : Gamma} (constraint : Constraint Γ)
    (i : Fin (Γ.relationOf constraint.symbol).arity) :
    constraint.vars i ∈ constraint.varsList := by
  rw [Constraint.varsList]
  exact List.mem_ofFn.2 ⟨i, rfl⟩

/-- The foldl accumulator is bounded by the fold. -/
theorem le_foldl_max_acc (list : List Nat) (acc : Nat) :
    acc ≤ list.foldl Nat.max acc := by
  induction list generalizing acc with
  | nil => rfl
  | cons y ys ih =>
      exact Nat.le_trans (Nat.le_max_left acc y) (ih (Nat.max acc y))

/-- The max-fold is monotone in the initial accumulator. -/
theorem foldl_max_le_of_le (list : List Nat) {left right : Nat} (below : left ≤ right) :
    list.foldl Nat.max left ≤ list.foldl Nat.max right := by
  induction list generalizing left right with
  | nil => exact below
  | cons y ys ih =>
      exact ih (max_le_max below le_rfl)

/-- A list member is bounded by the max-fold of the list. -/
theorem le_foldl_max {list : List Nat} {x : Nat} (member : x ∈ list) :
    x ≤ list.foldl Nat.max 0 := by
  induction list with
  | nil => cases member
  | cons y ys ih =>
      cases member with
      | head =>
          simpa [List.foldl_cons, Nat.max_eq_right] using le_foldl_max_acc ys x
      | tail _ member' =>
          have bound := ih member'
          simpa [List.foldl_cons, Nat.max_eq_right] using
            Nat.le_trans bound (foldl_max_le_of_le ys (Nat.zero_le y))

/-- Every constraint variable is bounded by the constraint's maximum variable. -/
theorem vars_le_maxVar {Γ : Gamma} (constraint : Constraint Γ)
    (i : Fin (Γ.relationOf constraint.symbol).arity) :
    constraint.vars i ≤ Constraint.maxVar constraint :=
  le_foldl_max (vars_mem_varsList constraint i)

/-- The formula max-fold accumulator is bounded by the fold. -/
theorem le_formulaMaxVar_foldl_acc {Γ : Gamma} (list : List (Constraint Γ)) (acc : Nat) :
    acc ≤ list.foldl (fun acc c => Nat.max acc (Constraint.maxVar c)) acc := by
  induction list generalizing acc with
  | nil => rfl
  | cons c cs ih =>
      exact Nat.le_trans (Nat.le_max_left acc (Constraint.maxVar c))
        (ih (Nat.max acc (Constraint.maxVar c)))

/-- The formula max-fold is monotone in the initial accumulator. -/
theorem formulaMaxVar_foldl_le_of_le {Γ : Gamma} (list : List (Constraint Γ))
    {left right : Nat} (below : left ≤ right) :
    list.foldl (fun acc c => Nat.max acc (Constraint.maxVar c)) left ≤
      list.foldl (fun acc c => Nat.max acc (Constraint.maxVar c)) right := by
  induction list generalizing left right with
  | nil => exact below
  | cons c cs ih =>
      exact ih (max_le_max below le_rfl)

/-- Every constraint variable of a formula member is bounded by the formula maximum. -/
theorem constraint_vars_le_formula_maxVar {Γ : Gamma} {constraint : Constraint Γ}
    {formula : CSP.Formula Γ} (member : constraint ∈ formula)
    (i : Fin (Γ.relationOf constraint.symbol).arity) :
    constraint.vars i ≤ CSP.Formula.maxVar formula := by
  induction formula with
  | nil => cases member
  | cons head tail ih =>
      cases member with
      | head =>
          simpa [CSP.Formula.maxVar, Nat.max_eq_right] using
            Nat.le_trans (vars_le_maxVar constraint i)
              (le_formulaMaxVar_foldl_acc tail (Constraint.maxVar constraint))
      | tail _ member' =>
          have bound := ih member'
          simpa [CSP.Formula.maxVar, Nat.max_eq_right] using
            Nat.le_trans bound
              (formulaMaxVar_foldl_le_of_le tail
                (Nat.zero_le (Constraint.maxVar head)))

/-! ### Semantic correctness of the substitution -/

/-- A satisfying assignment of one source constraint selects a gadget witness. -/
noncomputable def witness {Γ' Γ : Gamma} (interpretation : LanguageInterpretation Γ' Γ)
    (constraint : Constraint Γ') (source : SAT.Assignment) : SAT.Assignment := by
  classical
  exact
    let gadget := interpretation.gadgetOf constraint.symbol
    let tuple : BooleanTuple (Γ'.relationOf constraint.symbol).arity :=
      fun i => source (constraint.vars i)
    if satisfied : Constraint.Satisfies constraint source then
      Classical.choose ((gadget.correct tuple).1 satisfied)
    else fun _ => false

/-- The selected witness realizes the gadget on its output variables. -/
theorem witness_spec {Γ' Γ : Gamma} (interpretation : LanguageInterpretation Γ' Γ)
    (constraint : Constraint Γ') (source : SAT.Assignment)
    (satisfied : Constraint.Satisfies constraint source) :
    CSP.Formula.Satisfies (interpretation.gadgetOf constraint.symbol).formula
        (witness interpretation constraint source) ∧
      ∀ i, witness interpretation constraint source
          ((interpretation.gadgetOf constraint.symbol).outputs i) =
        source (constraint.vars i) := by
  classical
  have h := Classical.choose_spec
    ((interpretation.gadgetOf constraint.symbol).correct
      (fun i => source (constraint.vars i)) |>.1 satisfied)
  simpa [witness, satisfied] using h

/--
Forward assignment: source variables keep their values and every gadget
auxiliary variable receives the value of the corresponding selected witness.
-/
noncomputable def forwardAssignment {Γ' Γ : Gamma} (interpretation : LanguageInterpretation Γ' Γ)
    (formula : CSP.Formula Γ') (source : SAT.Assignment)
    (sourceSatisfies : CSP.Formula.Satisfies formula source) : SAT.Assignment := by
  classical
  exact
    let reference := CSP.Formula.maxVar formula
    fun var =>
      if var ≤ reference then source var
      else if fresh : ∃ constraint ∈ formula,
          ∃ gadgetVar, var = freshVar reference constraint gadgetVar then
        let constraint := Classical.choose fresh
        let gadgetVar := Classical.choose (Classical.choose_spec fresh).2
        (witness interpretation constraint source) gadgetVar
      else false

theorem forwardAssignment_source {Γ' Γ : Gamma} (interpretation : LanguageInterpretation Γ' Γ)
    (formula : CSP.Formula Γ') {source : SAT.Assignment}
    {sourceSatisfies : CSP.Formula.Satisfies formula source}
    {var : Nat} (below : var ≤ CSP.Formula.maxVar formula) :
    forwardAssignment interpretation formula source sourceSatisfies var = source var := by
  classical
  unfold forwardAssignment
  rw [if_pos below]

theorem forwardAssignment_fresh {Γ' Γ : Gamma} (interpretation : LanguageInterpretation Γ' Γ)
    (formula : CSP.Formula Γ') {source : SAT.Assignment}
    {sourceSatisfies : CSP.Formula.Satisfies formula source}
    {constraint : Constraint Γ'} (member : constraint ∈ formula) (gadgetVar : Nat) :
    forwardAssignment interpretation formula source sourceSatisfies
        (freshVar (CSP.Formula.maxVar formula) constraint gadgetVar) =
      (witness interpretation constraint source) gadgetVar := by
  classical
  let reference := CSP.Formula.maxVar formula
  have existsWitness : ∃ candidate ∈ formula,
      ∃ candidateVar, freshVar reference constraint gadgetVar =
        freshVar reference candidate candidateVar :=
    ⟨constraint, member, ⟨gadgetVar, rfl⟩⟩
  unfold forwardAssignment
  rw [if_neg (fun below => (Nat.not_lt_of_ge below)
    (freshVar_above_reference reference constraint gadgetVar))]
  rw [dif_pos existsWitness]
  let chosen := Classical.choose existsWitness
  let chosenVar := Classical.choose (Classical.choose_spec existsWitness).2
  have chosenFresh : freshVar reference constraint gadgetVar =
      freshVar reference chosen chosenVar :=
    Classical.choose_spec (Classical.choose_spec existsWitness).2
  have sameFresh : freshVar reference chosen chosenVar =
      freshVar reference constraint gadgetVar := chosenFresh.symm
  have injective := freshVar_injective reference (show
    (fun input : Constraint Γ' × Nat => freshVar reference input.1 input.2)
        (chosen, chosenVar) =
      (fun input : Constraint Γ' × Nat => freshVar reference input.1 input.2)
        (constraint, gadgetVar) from
    by simpa using sameFresh)
  have chosenEq : Classical.choose existsWitness = constraint := congrArg Prod.fst injective
  have chosenVarEq : Classical.choose (Classical.choose_spec existsWitness).2 = gadgetVar :=
    congrArg Prod.snd injective
  dsimp only
  exact congrArg (fun (pc : Constraint Γ' × Nat) => witness interpretation pc.1 source pc.2)
    (Prod.ext (congrArg Prod.fst injective) (congrArg Prod.snd injective))

/-- One instantiated gadget is satisfied by an agreeing target assignment. -/
theorem instantiate_satisfies_forward {Γ' Γ : Gamma} (interpretation : LanguageInterpretation Γ' Γ)
    (reference : Nat) {constraint : Constraint Γ'} {source : SAT.Assignment}
    (sourceSatisfies : Constraint.Satisfies constraint source)
    {target : SAT.Assignment}
    (targetSourceAgrees : ∀ var ≤ reference, target var = source var)
    (constraintVarsBelow : ∀ i, constraint.vars i ≤ reference)
    (targetFreshAgrees : ∀ gadgetVar,
      target (freshVar reference constraint gadgetVar) =
        (witness interpretation constraint source) gadgetVar) :
    CSP.Formula.Satisfies (instantiate interpretation reference constraint) target := by
  intro d dMember
  rcases List.mem_map.mp dMember with ⟨g, gMember, rfl⟩
  let gadget := interpretation.gadgetOf constraint.symbol
  have witnessSpec := witness_spec interpretation constraint source sourceSatisfies
  change (Γ.relationOf g.symbol).Holds
    (fun j => target (instantiateVar interpretation reference constraint (g.vars j)))
  have tupleEq : (fun j => target (instantiateVar interpretation reference constraint (g.vars j))) =
      (fun j => (witness interpretation constraint source) (g.vars j)) := by
    funext j
    unfold instantiateVar
    by_cases h : g.vars j ∈ Set.range gadget.outputs
    · have outputKey : gadget.outputs (Classical.choose h) = g.vars j :=
        Classical.choose_spec h
      rw [dif_pos h]
      have below : constraint.vars (Classical.choose h) ≤ reference :=
        constraintVarsBelow (Classical.choose h)
      have sourceValue : target (constraint.vars (Classical.choose h)) =
          source (constraint.vars (Classical.choose h)) :=
        targetSourceAgrees (constraint.vars (Classical.choose h)) below
      rw [sourceValue]
      have witnessOutput : source (constraint.vars (Classical.choose h)) =
          (witness interpretation constraint source) (g.vars j) := by
        have hw := congrArg (witness interpretation constraint source)
          outputKey
        exact (witnessSpec.2 (Classical.choose h)).symm.trans hw
      exact witnessOutput
    · rw [dif_neg h]
      exact targetFreshAgrees (g.vars j)
  rw [tupleEq]
  exact witnessSpec.1 g gMember

/-- A target assignment satisfying one instantiated gadget satisfies the source constraint. -/
theorem instantiate_satisfies_reverse {Γ' Γ : Gamma} (interpretation : LanguageInterpretation Γ' Γ)
    (reference : Nat) (constraint : Constraint Γ') {target : SAT.Assignment}
    (targetSatisfies : CSP.Formula.Satisfies (instantiate interpretation reference constraint) target) :
    Constraint.Satisfies constraint target := by
  let gadget := interpretation.gadgetOf constraint.symbol
  let tuple : BooleanTuple (Γ'.relationOf constraint.symbol).arity :=
    fun i => target (constraint.vars i)
  apply (gadget.correct tuple).2
  refine ⟨fun var => target (instantiateVar interpretation reference constraint var), ?_⟩
  constructor
  · intro d dMember
    change (Γ.relationOf d.symbol).Holds
      (fun j => target (instantiateVar interpretation reference constraint (d.vars j)))
    exact targetSatisfies _ (List.mem_map.mpr ⟨d, dMember, rfl⟩)
  · intro i
    change target (instantiateVar interpretation reference constraint (gadget.outputs i)) =
      target (constraint.vars i)
    unfold instantiateVar
    have member : gadget.outputs i ∈ Set.range gadget.outputs := ⟨i, rfl⟩
    rw [dif_pos member]
    have outputEq : Classical.choose member = i :=
      gadget.outputs_injective (Classical.choose_spec member)
    rw [outputEq]

/-- The complete substitution preserves satisfiability in the forward direction. -/
theorem interpret_satisfies_forward {Γ' Γ : Gamma} (interpretation : LanguageInterpretation Γ' Γ)
    (formula : CSP.Formula Γ') {source : SAT.Assignment}
    (sourceSatisfies : CSP.Formula.Satisfies formula source) :
    CSP.Formula.Satisfies (interpret interpretation formula)
      (forwardAssignment interpretation formula source sourceSatisfies) := by
  intro constraint constraintMember
  rcases List.mem_flatMap.mp constraintMember with ⟨c, cMember, inBlock⟩
  apply instantiate_satisfies_forward interpretation (CSP.Formula.maxVar formula)
    (sourceSatisfies := sourceSatisfies c cMember)
    (target := forwardAssignment interpretation formula source sourceSatisfies)
  · intro var below
    exact forwardAssignment_source interpretation formula below
  · intro i
    exact constraint_vars_le_formula_maxVar cMember i
  · intro gadgetVar
    exact forwardAssignment_fresh interpretation formula cMember gadgetVar
  exact inBlock

/-- The complete substitution preserves satisfiability in the reverse direction. -/
theorem interpret_satisfies_reverse {Γ' Γ : Gamma} (interpretation : LanguageInterpretation Γ' Γ)
    (formula : CSP.Formula Γ') {target : SAT.Assignment}
    (targetSatisfies : CSP.Formula.Satisfies (interpret interpretation formula) target) :
    CSP.Formula.Satisfies formula target := by
  intro constraint constraintMember
  apply instantiate_satisfies_reverse interpretation (CSP.Formula.maxVar formula) constraint
  intro d dMember
  exact targetSatisfies d (List.mem_flatMap.mpr ⟨constraint, constraintMember, dMember⟩)

/-- Gadget substitution is a valid many-one reduction. -/
theorem interpret_satisfiable_iff {Γ' Γ : Gamma} (interpretation : LanguageInterpretation Γ' Γ)
    (formula : CSP.Formula Γ') :
    CSP.Formula.Satisfiable (interpret interpretation formula) ↔
      CSP.Formula.Satisfiable formula := by
  constructor
  · rintro ⟨target, targetSatisfies⟩
    exact ⟨target, interpret_satisfies_reverse interpretation formula targetSatisfies⟩
  · rintro ⟨source, sourceSatisfies⟩
    exact ⟨forwardAssignment interpretation formula source sourceSatisfies,
      interpret_satisfies_forward interpretation formula sourceSatisfies⟩

/-! ### Certified reduction and hardness transport -/

/--
The substitution is a `CertifiedReduction (cspOf Γ') (cspOf Γ)` once the
interpretation carries a direct-TM witness.
-/
noncomputable def certifiedReduction_of_interpretation {Γ' Γ : Gamma}
    (interpretation : LanguageInterpretation Γ' Γ)
    (interpretTM : ComplexityReduction.TMPolyTimeMap
      (Presentation.FiniteDomainCSPTable.encodedType Γ')
      (Presentation.FiniteDomainCSPTable.encodedType Γ)
      (interpret interpretation)) :
    ComplexityReduction.Certificate.CertifiedReduction (cspOf Γ') (cspOf Γ) := by
  let program : ComplexityReduction.Program.PolyProg
      (cspOf Γ').representation (cspOf Γ).representation :=
    .atom (ComplexityReduction.Program.Primitive.ofTMPolyTime
      (interpret interpretation) interpretTM)
  refine ⟨program, ?_⟩
  intro formula
  have hrun : program.run formula = interpret interpretation formula := rfl
  simpa [cspOf_accepts, hrun] using
    (interpret_satisfiable_iff interpretation formula).symm

/-- NP-hardness transports from an interpreted core to the interpreting Γ. -/
theorem nPHard_of_interpretation {Γ' Γ : Gamma}
    (interpretation : LanguageInterpretation Γ' Γ)
    (interpretTM : ComplexityReduction.TMPolyTimeMap
      (Presentation.FiniteDomainCSPTable.encodedType Γ')
      (Presentation.FiniteDomainCSPTable.encodedType Γ)
      (interpret interpretation))
    (coreNPHard : ComplexityReduction.Certificate.NativeTMNPHard (cspOf Γ')) :
    ComplexityReduction.Certificate.NativeTMNPHard (cspOf Γ) :=
  ComplexityReduction.Certificate.NativeTMNPHard.alongPath coreNPHard
    (ComplexityReduction.Certificate.CertifiedPath.step
      (certifiedReduction_of_interpretation interpretation interpretTM))

end Hardness
end BooleanCSP
end Domain
end ComplexityReduction
