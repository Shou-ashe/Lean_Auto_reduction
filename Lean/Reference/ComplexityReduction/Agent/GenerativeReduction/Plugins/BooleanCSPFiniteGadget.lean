/- Copyright (c) 2026. -/

import ComplexityReduction.Domain.BooleanCSP.Hardness.PPDefinability

/-!
Proof-producing finite search for small Boolean-CSP pp-gadgets.

The search grammar contains no benchmark identifiers or expected routes.  A
candidate is a finite formula over explicitly supplied language symbols.  Lean
checks its complete truth table on six variables, and `Spec.toGadget` lifts the
finite certificate to the total-assignment semantics used by `Gadget`.
-/

namespace ComplexityReduction.Agent.GenerativeReduction.Plugins.BooleanCSPFiniteGadget

open ComplexityReduction
open ComplexityReduction.CSP
open ComplexityReduction.Domain.BooleanCSP
open ComplexityReduction.Domain.BooleanCSP.Hardness

structure FiniteConstraint (Γ : Gamma) (variableCount : Nat) where
  symbol : Γ.Symbol
  vars : Fin (Γ.relationOf symbol).arity → Fin variableCount

namespace FiniteConstraint

def decidableHolds (relation : BooleanRelation) (tuple : BooleanTuple relation.arity) :
    Decidable (relation.Holds tuple) := by
  unfold BoolRel.Holds
  infer_instance

def Satisfies {Γ : Gamma} {variableCount : Nat}
    (constraint : FiniteConstraint Γ variableCount)
    (assignment : Fin variableCount → Bool) : Prop :=
  (Γ.relationOf constraint.symbol).Holds fun index =>
    assignment (constraint.vars index)

instance {Γ : Gamma} {variableCount : Nat}
    (constraint : FiniteConstraint Γ variableCount)
    (assignment : Fin variableCount → Bool) : Decidable (constraint.Satisfies assignment) := by
  unfold Satisfies BoolRel.Holds
  infer_instance

def toConstraint {Γ : Gamma} {variableCount : Nat}
    (constraint : FiniteConstraint Γ variableCount) : Constraint Γ where
  symbol := constraint.symbol
  vars := fun index => (constraint.vars index).val

end FiniteConstraint

abbrev FiniteFormula (Γ : Gamma) (variableCount : Nat) :=
  List (FiniteConstraint Γ variableCount)

namespace FiniteFormula

def Satisfies {Γ : Gamma} {variableCount : Nat} :
    FiniteFormula Γ variableCount → (Fin variableCount → Bool) → Prop
  | [], _ => True
  | constraint :: formula, assignment =>
      constraint.Satisfies assignment ∧ Satisfies formula assignment

instance {Γ : Gamma} {variableCount : Nat}
    (formula : FiniteFormula Γ variableCount)
    (assignment : Fin variableCount → Bool) : Decidable (Satisfies formula assignment) := by
  induction formula with
  | nil => exact isTrue trivial
  | cons constraint formula inductionHypothesis => exact instDecidableAnd

def toFormula {Γ : Gamma} {variableCount : Nat}
    (formula : FiniteFormula Γ variableCount) : Formula Γ :=
  formula.map FiniteConstraint.toConstraint

def extend {variableCount : Nat} (assignment : Fin variableCount → Bool) : SAT.Assignment :=
  fun key => if bound : key < variableCount then assignment ⟨key, bound⟩ else false

def restrict {variableCount : Nat} (assignment : SAT.Assignment) : Fin variableCount → Bool :=
  fun key => assignment key.val

@[simp]
theorem extend_apply {variableCount : Nat} (assignment : Fin variableCount → Bool)
    (key : Fin variableCount) :
    extend assignment key.val = assignment key := by
  simp [extend, key.isLt]

theorem satisfies_extend_iff {Γ : Gamma} {variableCount : Nat}
    (formula : FiniteFormula Γ variableCount) (assignment : Fin variableCount → Bool) :
    Formula.Satisfies formula.toFormula (extend assignment) ↔
      Satisfies formula assignment := by
  induction formula with
  | nil => simp [toFormula, Formula.Satisfies, Satisfies]
  | cons constraint formula inductionHypothesis =>
      simp only [toFormula, List.map_cons, Formula.satisfies_cons, Satisfies]
      constructor
      · rintro ⟨head, tail⟩
        refine ⟨?_, inductionHypothesis.mp tail⟩
        change (Γ.relationOf constraint.symbol).Holds
          (fun index => extend assignment (constraint.vars index).val) at head
        simpa only [extend_apply] using head
      · rintro ⟨head, tail⟩
        refine ⟨?_, inductionHypothesis.mpr tail⟩
        change (Γ.relationOf constraint.symbol).Holds
          (fun index => extend assignment (constraint.vars index).val)
        simpa only [extend_apply] using head

theorem satisfies_restrict_iff {Γ : Gamma} {variableCount : Nat}
    (formula : FiniteFormula Γ variableCount) (assignment : SAT.Assignment) :
    Formula.Satisfies formula.toFormula assignment ↔
      Satisfies formula (restrict assignment) := by
  induction formula with
  | nil => simp [toFormula, Formula.Satisfies, Satisfies]
  | cons constraint formula inductionHypothesis =>
      simp only [toFormula, List.map_cons, Formula.satisfies_cons, Satisfies]
      constructor
      · rintro ⟨head, tail⟩
        refine ⟨?_, inductionHypothesis.mp tail⟩
        change (Γ.relationOf constraint.symbol).Holds
          (fun index => assignment (constraint.vars index).val) at head
        simpa only [FiniteConstraint.Satisfies, restrict] using head
      · rintro ⟨head, tail⟩
        refine ⟨?_, inductionHypothesis.mpr tail⟩
        change (Γ.relationOf constraint.symbol).Holds
          (fun index => assignment (constraint.vars index).val)
        simpa only [FiniteConstraint.Satisfies, restrict] using head

end FiniteFormula

structure Spec (Γ : Gamma) (relation : BooleanRelation) (variableCount : Nat) where
  formula : FiniteFormula Γ variableCount
  outputs : Fin relation.arity → Fin variableCount
  outputs_injective : Function.Injective outputs

namespace Spec

def Correct {Γ : Gamma} {relation : BooleanRelation} {variableCount : Nat}
    (spec : Spec Γ relation variableCount) : Prop :=
  ∀ tuple : BooleanTuple relation.arity,
    relation.Holds tuple ↔ ∃ assignment : Fin variableCount → Bool,
      spec.formula.Satisfies assignment ∧
        ∀ index, assignment (spec.outputs index) = tuple index

instance {Γ : Gamma} {relation : BooleanRelation} {variableCount : Nat}
    (spec : Spec Γ relation variableCount) : Decidable spec.Correct := by
  unfold Correct
  letI (tuple : BooleanTuple relation.arity) : Decidable (relation.Holds tuple) :=
    FiniteConstraint.decidableHolds relation tuple
  infer_instance

noncomputable def toGadget {Γ : Gamma} {relation : BooleanRelation} {variableCount : Nat}
    (spec : Spec Γ relation variableCount) (correct : spec.Correct) : Gadget Γ relation where
  formula := spec.formula.toFormula
  outputs := fun index => (spec.outputs index).val
  outputs_injective := by
    intro left right equality
    apply spec.outputs_injective
    apply Fin.ext
    exact equality
  correct := by
    intro tuple
    constructor
    · intro holds
      rcases (correct tuple).mp holds with ⟨assignment, satisfies, outputs⟩
      refine ⟨FiniteFormula.extend assignment,
        (FiniteFormula.satisfies_extend_iff spec.formula assignment).mpr satisfies, ?_⟩
      intro index
      simpa [FiniteFormula.extend, (spec.outputs index).isLt] using outputs index
    · rintro ⟨assignment, satisfies, outputs⟩
      apply (correct tuple).mpr
      refine ⟨FiniteFormula.restrict assignment,
        (FiniteFormula.satisfies_restrict_iff spec.formula assignment).mp satisfies, ?_⟩
      intro index
      simpa [FiniteFormula.restrict] using outputs index

end Spec

def AnyCorrect {Γ : Gamma} {relation : BooleanRelation} {variableCount : Nat} :
    List (Spec Γ relation variableCount) → Prop
  | [] => False
  | spec :: specs => spec.Correct ∨ AnyCorrect specs

instance anyCorrectDecidable {Γ : Gamma} {relation : BooleanRelation}
    {variableCount : Nat} (specs : List (Spec Γ relation variableCount)) :
    Decidable (AnyCorrect specs) := by
  induction specs with
  | nil => exact isFalse id
  | cons spec specs inductionHypothesis =>
      exact instDecidableOr

noncomputable def chooseCorrect {Γ : Gamma} {relation : BooleanRelation}
    {variableCount : Nat} :
    (specs : List (Spec Γ relation variableCount)) → AnyCorrect specs →
      {spec : Spec Γ relation variableCount // spec.Correct}
  | [], proof => False.elim proof
  | spec :: specs, proof =>
      if correct : spec.Correct then ⟨spec, correct⟩
      else chooseCorrect specs (proof.resolve_left correct)

noncomputable def gadgetOfCandidates {Γ : Gamma} {relation : BooleanRelation}
    {variableCount : Nat} (specs : List (Spec Γ relation variableCount))
    (existsCorrect : AnyCorrect specs) : Gadget Γ relation :=
  let selected := chooseCorrect specs existsCorrect
  selected.val.toGadget selected.property

/-! ### Planner-parameterized grammar materialization -/

/-- Interpret one planner-supplied variable index at an arbitrary positive bound. -/
def plannedMappedVariable (variableCount : Nat) (positive : 0 < variableCount)
    (mapping : List Nat) (index : Nat) : Fin variableCount :=
  ⟨mapping.getD index 0 % variableCount, Nat.mod_lt _ positive⟩

/-- Materialize one target-language constraint from a planner mapping. -/
def plannedConstraintOfMapping {Γ : Gamma} (variableCount : Nat)
    (positive : 0 < variableCount) (symbol : Γ.Symbol) (mapping : List Nat) :
    FiniteConstraint Γ variableCount where
  symbol := symbol
  vars := fun index => plannedMappedVariable variableCount positive mapping index.val

/-- Use the first source-arity variables as outputs at any sufficient bound. -/
def firstOutputs {relation : BooleanRelation} {variableCount : Nat}
    (arityBound : relation.arity ≤ variableCount) :
    Fin relation.arity → Fin variableCount :=
  fun index => ⟨index.val, Nat.lt_of_lt_of_le index.isLt arityBound⟩

theorem firstOutputs_injective {relation : BooleanRelation} {variableCount : Nat}
    (arityBound : relation.arity ≤ variableCount) :
    Function.Injective (firstOutputs arityBound) := by
  intro left right equality
  apply Fin.ext
  simpa [firstOutputs] using congrArg Fin.val equality

/-- Turn a materialized formula into a spec with the planner-selected bound. -/
def plannedSpecOfFormula {Γ : Gamma} {relation : BooleanRelation}
    {variableCount : Nat} (arityBound : relation.arity ≤ variableCount)
    (formula : FiniteFormula Γ variableCount) : Spec Γ relation variableCount where
  formula := formula
  outputs := firstOutputs arityBound
  outputs_injective := firstOutputs_injective arityBound

/-- Enumerate target symbols for exactly one planner-supplied formula shape. -/
def plannedFormulasForTemplate (Γ : Gamma) (symbols : List Γ.Symbol)
    (variableCount : Nat) (positive : 0 < variableCount) :
    List (List Nat) → List (FiniteFormula Γ variableCount)
  | [] => [[]]
  | mapping :: mappings =>
      symbols.flatMap fun symbol =>
        (plannedFormulasForTemplate Γ symbols variableCount positive mappings).map fun tail =>
          plannedConstraintOfMapping variableCount positive symbol mapping :: tail

/--
Materialize the exact bounded grammar selected by the capability planner.
The fixed `templates` below are only one possible seed list; callers can pass
new shapes, bounds, repeated variables, auxiliary layouts, and conjunctions.
-/
def plannedSpecs (Γ : Gamma) (symbols : List Γ.Symbol)
    (relation : BooleanRelation) (variableCount : Nat)
    (positive : 0 < variableCount) (arityBound : relation.arity ≤ variableCount)
    (selectedTemplates : List (List (List Nat))) :
    List (Spec Γ relation variableCount) :=
  selectedTemplates.flatMap fun template =>
    (plannedFormulasForTemplate Γ symbols variableCount positive template).map
      (plannedSpecOfFormula arityBound)

/-! ### Executable counterexample receipts -/

/-- A concrete failed truth-table row, encoded without dependent fields. -/
structure TruthTableCounterexample where
  tuple : List Bool
  expectedRelation : Bool
  formulaSatisfiable : Bool
  deriving Repr, DecidableEq

private def allBoolFunctions : (size : Nat) → List (Fin size → Bool)
  | 0 => [fun index => Fin.elim0 index]
  | size + 1 =>
      (allBoolFunctions size).flatMap fun tail =>
        [ (fun index => Fin.cases false tail index)
        , (fun index => Fin.cases true tail index)
        ]

private def allBoolRows : Nat → List (List Bool)
  | 0 => [[]]
  | size + 1 =>
      (allBoolRows size).flatMap fun tail => [false :: tail, true :: tail]

private def relationHoldsBool (relation : BooleanRelation)
    (tuple : BooleanTuple relation.arity) : Bool :=
  decide (tuple ∈ relation.accepts)

private def Spec.realizesTupleBool {Γ : Gamma} {relation : BooleanRelation}
    {variableCount : Nat} (spec : Spec Γ relation variableCount)
    (tuple : BooleanTuple relation.arity) : Bool :=
  (allBoolFunctions variableCount).any fun assignment =>
    decide (spec.formula.Satisfies assignment) &&
      (List.ofFn fun index : Fin relation.arity => index).all fun index =>
        assignment (spec.outputs index) == tuple index

private def tupleOfRow {arity : Nat} (row : List Bool)
    (arityEq : arity = row.length) : BooleanTuple arity :=
  fun index => row.get (Fin.cast arityEq index)

private def plannedFormulaForSymbols (target : Gamma) (variableCount : Nat)
    (positive : 0 < variableCount) (template : List (List Nat))
    (symbols : Fin template.length → target.Symbol) :
    FiniteFormula target variableCount :=
  List.ofFn fun index =>
    plannedConstraintOfMapping variableCount positive (symbols index)
      (template.get index)

private def mismatchExistsForRow (source target : Gamma) (variableCount : Nat)
    (positive : 0 < variableCount)
    (arityBound : ∀ symbol : source.Symbol,
      (source.relationOf symbol).arity ≤ variableCount)
    (template : List (List Nat)) (row : List Bool)
    (expectedRelation formulaSatisfiable : Bool) : Bool :=
  decide (∃ sourceSymbol : source.Symbol,
    ∃ arityEq : (source.relationOf sourceSymbol).arity = row.length,
    ∃ targetSymbols : Fin template.length → target.Symbol,
      let tuple := tupleOfRow row arityEq
      let formula := plannedFormulaForSymbols target variableCount positive
        template targetSymbols
      let spec := plannedSpecOfFormula (arityBound sourceSymbol) formula
      relationHoldsBool (source.relationOf sourceSymbol) tuple = expectedRelation ∧
        spec.realizesTupleBool tuple = formulaSatisfiable)

/--
Extract an exact source tuple from a rejected planner grammar.  This function
is called only after Lean has rejected `AnyCorrect`; the returned row is
feedback for the next CEGIS round and never proof authority.
-/
def firstPlannedCounterexample? (source target : Gamma) (variableCount : Nat)
    (positive : 0 < variableCount)
    (arityBound : ∀ symbol : source.Symbol,
      (source.relationOf symbol).arity ≤ variableCount)
    (selectedTemplates : List (List (List Nat))) :
    Option TruthTableCounterexample :=
  match selectedTemplates with
  | [] => none
  | template :: _ =>
      let rows := (List.range (variableCount + 1)).flatMap allBoolRows
      match rows.find? fun row =>
          mismatchExistsForRow source target variableCount positive arityBound
              template row true false ||
            mismatchExistsForRow source target variableCount positive arityBound
              template row false true with
      | none => none
      | some row =>
          let positiveMismatch := mismatchExistsForRow source target variableCount
            positive arityBound template row true false
          some {
            tuple := row
            expectedRelation := positiveMismatch
            formulaSatisfiable := !positiveMismatch
          }

private def renderBool (value : Bool) : String :=
  if value then "true" else "false"

/-- Stable line protocol consumed by the Python runtime after a failed check. -/
def renderPlannedCounterexample (source target : Gamma) (variableCount : Nat)
    (positive : 0 < variableCount)
    (arityBound : ∀ symbol : source.Symbol,
      (source.relationOf symbol).arity ≤ variableCount)
    (selectedTemplates : List (List (List Nat))) : String :=
  match firstPlannedCounterexample? source target variableCount positive arityBound
      selectedTemplates with
  | none => "BOOLEAN_CSP_COUNTEREXAMPLE_NONE"
  | some counterexample =>
      String.intercalate "\t"
        [ "BOOLEAN_CSP_COUNTEREXAMPLE"
        , String.intercalate "," (counterexample.tuple.map renderBool)
        , renderBool counterexample.expectedRelation
        , renderBool counterexample.formulaSatisfiable
        ]

/-- Search and certify exactly the planner-selected finite grammar. -/
noncomputable def gadgetOfPlannedSearch (Γ : Gamma) (symbols : List Γ.Symbol)
    (relation : BooleanRelation) (variableCount : Nat)
    (positive : 0 < variableCount) (arityBound : relation.arity ≤ variableCount)
    (selectedTemplates : List (List (List Nat)))
    (existsCorrect : AnyCorrect
      (plannedSpecs Γ symbols relation variableCount positive arityBound selectedTemplates)) :
    Gadget Γ relation :=
  gadgetOfCandidates
    (plannedSpecs Γ symbols relation variableCount positive arityBound selectedTemplates)
    existsCorrect

def mappedVariable (mapping : List Nat) (index : Nat) : Fin 6 :=
  ⟨mapping.getD index 0 % 6, Nat.mod_lt _ (by decide)⟩

def constraintOfMapping {Γ : Gamma} (symbol : Γ.Symbol) (mapping : List Nat) :
    FiniteConstraint Γ 6 where
  symbol := symbol
  vars := fun index => mappedVariable mapping index.val

def firstThreeOutputs {relation : BooleanRelation} (arity : relation.arity = 3) :
    Fin relation.arity → Fin 6 :=
  fun index => ⟨index.val, by omega⟩

theorem firstThreeOutputs_injective {relation : BooleanRelation}
    (arity : relation.arity = 3) : Function.Injective (firstThreeOutputs arity) := by
  intro left right equality
  apply Fin.ext
  simpa [firstThreeOutputs] using congrArg Fin.val equality

def specOfFormula {Γ : Gamma} {relation : BooleanRelation}
    (arity : relation.arity = 3) (formula : FiniteFormula Γ 6) : Spec Γ relation 6 where
  formula := formula
  outputs := firstThreeOutputs arity
  outputs_injective := firstThreeOutputs_injective arity

def formulasForTemplate (Γ : Gamma) (symbols : List Γ.Symbol) :
    List (List Nat) → List (FiniteFormula Γ 6)
  | [] => [[]]
  | mapping :: mappings =>
      symbols.flatMap fun symbol =>
        (formulasForTemplate Γ symbols mappings).map fun tail =>
          constraintOfMapping symbol mapping :: tail

/--
Small repeated-variable and auxiliary-variable pp templates.  The final
seven-atom shape includes the standard exactly-one construction from `OR₃`
and `XOR₂`: one positive clause, three complement links, and three
pairwise-at-most-one clauses.
-/
def templates : List (List (List Nat)) :=
  [ [[0, 1, 2, 0, 0, 0]]
  , [[0, 1, 2, 3, 3, 3]]
  , [[0, 0, 1, 1, 2, 2]]
  , [[0, 0, 1, 2, 3, 4]]
  , [[0, 1, 2, 3], [0, 3, 3, 4]]
  , [[0, 0, 1, 2, 3], [0, 0, 3, 3, 4]]
  , [[0, 0, 3, 3, 4], [0, 1, 2, 4, 4]]
  , [[0, 1], [0, 1, 2]]
  , [[0, 1, 2]]
  -- Generic constant/parity/clause circuit.  With a binary positive clause
  -- and a ternary even-parity relation, an appropriate symbol assignment is:
  --   t = true; nx = not x; p = x xor y;
  --   x xor y xor z = true; nx or p.
  -- This realizes a one-in-three relation without naming any benchmark or
  -- target relation and is also available as a seed for arbitrary finite Γ.
  , [[3, 3], [0, 4, 3], [0, 1, 5], [5, 2, 3], [4, 5]]
  , [[3, 1, 2], [0, 3]]
  , [[0, 3, 2], [1, 3]]
  , [[0, 1, 3], [2, 3]]
  , [[3, 4, 2], [0, 3], [1, 4]]
  , [[3, 1, 4], [0, 3], [2, 4]]
  , [[0, 3, 4], [1, 3], [2, 4]]
  , [[3, 4, 5], [0, 3], [1, 4], [2, 5]]
  , [[0, 1, 2], [0, 3], [1, 4], [2, 5], [3, 4, 4], [3, 5, 5], [4, 5, 5]]
  ]

def defaultSpecs (Γ : Gamma) (symbols : List Γ.Symbol) (relation : BooleanRelation)
    (arity : relation.arity = 3) : List (Spec Γ relation 6) :=
  templates.flatMap fun template =>
    (formulasForTemplate Γ symbols template).map (specOfFormula arity)

noncomputable def gadgetOfDefaultSearch (Γ : Gamma) (symbols : List Γ.Symbol)
    (relation : BooleanRelation)
    (arity : relation.arity = 3)
    (existsCorrect : AnyCorrect (defaultSpecs Γ symbols relation arity)) : Gadget Γ relation :=
  gadgetOfCandidates (defaultSpecs Γ symbols relation arity) existsCorrect

assert_standard_axioms Spec.toGadget, gadgetOfCandidates, gadgetOfPlannedSearch,
  gadgetOfDefaultSearch

end ComplexityReduction.Agent.GenerativeReduction.Plugins.BooleanCSPFiniteGadget
