/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Domain.ThreeSATToThreeSATLikeStandardTM
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatPair
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyCheckedSuffixValidityTM
import ComplexityReduction.Presentation.NAEThreeSAT
import ComplexityReduction.Program.ContextListMap
import ComplexityReduction.Program.List

/-!
An endpoint-exact, direct-TM 3SAT-to-NAE-3SAT ingress.

Each nonempty source clause is padded by repeating its last literal to exactly
three positions.  A public reference variable turns that disjunction into one
NAE-4 constraint; a private auxiliary variable then splits NAE-4 into two exact
NAE-3 clauses.  Auxiliary variables are derived injectively from the padded
literal triple, so duplicate clauses deliberately share the same (compatible)
auxiliary value while distinct triples cannot collide.

This leaf exposes only the executable, direct-TM evidence, semantic theorem,
and raw endpoint-exact `TMKarpReduction`.  It does not publish a hardness
facade or a final certified route.
-/

namespace ComplexityReduction
namespace Domain
namespace ThreeSATToNAEThreeSAT

open ComplexityReduction
open ComplexityReduction.NAEThreeSAT
open ThreeSATToThreeSATLikeStandardTM

/-- Exact structured source encoding. -/
abbrev sourceEncoding : EncodedType := Karp21.threeCNFStructuredEncodedType

/-- Exact structured source-clause encoding. -/
abbrev sourceClauseEncoding : EncodedType := Karp21.clauseStructuredEncodedType

/-- Exact structured source-literal encoding. -/
abbrev literalEncoding : EncodedType := Karp21.literalStructuredEncodedType

/-- Exact public NAE clause encoding. -/
abbrev targetClauseEncoding : EncodedType := Presentation.NAEThreeSAT.clauseEncodedType

/-- Exact public NAE formula encoding. -/
abbrev targetEncoding : EncodedType := Presentation.NAEThreeSAT.formulaEncodedType

/-- Injective unary-natural key for one structured SAT literal. -/
def literalKey (literal : SAT.Literal) : Nat :=
  Nat.pair literal.var (boolToNat literal.neg)

theorem literalKey_injective : Function.Injective literalKey := by
  intro left right equality
  have parts := Nat.pair_eq_pair.mp equality
  have varEquality : left.var = right.var := parts.1
  have negEquality : left.neg = right.neg := by
    cases leftNeg : left.neg <;> cases rightNeg : right.neg <;>
      simp [leftNeg, rightNeg, boolToNat] at parts ⊢
  cases left with
  | mk leftVar leftNeg =>
      cases right with
      | mk rightVar rightNeg =>
          simp only at varEquality negEquality
          cases varEquality
          cases negEquality
          rfl

/-- Injective key for one exact ordered NAE literal triple. -/
def clauseKey (clause : Clause) : Nat :=
  Nat.pair (literalKey clause.first)
    (Nat.pair (literalKey clause.second) (literalKey clause.third))

theorem clauseKey_injective : Function.Injective clauseKey := by
  intro left right equality
  have outer := Nat.pair_eq_pair.mp equality
  have firstEquality : left.first = right.first :=
    literalKey_injective outer.1
  have inner := Nat.pair_eq_pair.mp outer.2
  have secondEquality : left.second = right.second :=
    literalKey_injective inner.1
  have thirdEquality : left.third = right.third :=
    literalKey_injective inner.2
  cases left with
  | mk leftFirst leftSecond leftThird =>
      cases right with
      | mk rightFirst rightSecond rightThird =>
          simp only at firstEquality secondEquality thirdEquality
          cases firstEquality
          cases secondEquality
          cases thirdEquality
          rfl

/-- The established bounded-lookups padded to an exact literal triple. -/
def paddedClause (clause : SAT.Clause) : Clause where
  first := firstLiteral clause
  second := secondLiteral clause
  third := thirdLiteral clause

/-- Reference variable, chosen strictly above every source variable. -/
def referenceVar (formula : SAT.ThreeCNF) : Nat :=
  sourceEncoding.inputSize formula

/-- Collision-free auxiliary variable for one padded source clause. -/
def auxiliaryVar (reference : Nat) (clause : SAT.Clause) : Nat :=
  reference + clauseKey (paddedClause clause) + 1

theorem reference_lt_auxiliaryVar (reference : Nat) (clause : SAT.Clause) :
    reference < auxiliaryVar reference clause := by
  simp [auxiliaryVar]

theorem auxiliaryVar_eq_iff (reference : Nat) (left right : SAT.Clause) :
    auxiliaryVar reference left = auxiliaryVar reference right ↔
      paddedClause left = paddedClause right := by
  constructor
  · intro equality
    apply clauseKey_injective
    unfold auxiliaryVar at equality
    exact Nat.add_left_cancel (Nat.add_right_cancel equality)
  · intro equality
    simp [auxiliaryVar, equality]

/-- Fixed contradictory NAE block used for an empty source clause. -/
def impossibleClause : Clause where
  first := defaultLiteral
  second := defaultLiteral
  third := defaultLiteral

/-- Two-clause NAE-4-to-NAE-3 split for one nonempty source clause. -/
def nonemptyBlock (reference : Nat) (clause : SAT.Clause) : Formula :=
  let padded := paddedClause clause
  let auxiliary := auxiliaryVar reference clause
  [ { first := padded.first
      second := padded.second
      third := SAT.Literal.positive auxiliary },
    { first := SAT.Literal.negative auxiliary
      second := padded.third
      third := SAT.Literal.positive reference } ]

/-- Total exact clause block; empty clauses map to an immediate contradiction. -/
def clauseBlock (reference : Nat) (clause : SAT.Clause) : Formula :=
  if clause.length = 0 then [impossibleClause] else nonemptyBlock reference clause

/-- Pair-carrier spelling used by context/list map. -/
def clauseBlockFromPair (input : Nat × SAT.Clause) : Formula :=
  clauseBlock input.1 input.2

/-- Complete exact 3SAT-to-NAE-3SAT executable. -/
def executable (formula : SAT.ThreeCNF) : Formula :=
  formula.clauses.flatMap (clauseBlock (referenceVar formula))

/-! ### Local semantics -/

/-- Boolean-value spelling of one exact NAE-3 constraint. -/
def nae3Values (first second third : Bool) : Prop :=
  ¬ (first = second ∧ second = third)

/-- Boolean-value spelling of one NAE-4 constraint. -/
def nae4Values (first second third reference : Bool) : Prop :=
  ¬ (first = second ∧ second = third ∧ third = reference)

/-- Deterministic auxiliary value for the standard NAE-4 split. -/
def splitWitness (first second third : Bool) : Bool :=
  if first = second then !first else third

theorem splitWitness_correct {first second third reference : Bool}
    (four : nae4Values first second third reference) :
    nae3Values first second (splitWitness first second third) ∧
      nae3Values (!(splitWitness first second third)) third reference := by
  cases first <;> cases second <;> cases third <;> cases reference <;>
    simp_all [nae3Values, nae4Values, splitWitness]

theorem split_sound {first second third reference auxiliary : Bool}
    (left : nae3Values first second auxiliary)
    (right : nae3Values (!auxiliary) third reference) :
    nae4Values first second third reference := by
  cases first <;> cases second <;> cases third <;> cases reference <;>
    cases auxiliary <;> simp_all [nae3Values, nae4Values]

/-- Complement every Boolean variable in a total assignment. -/
def complementAssignment (assignment : SAT.Assignment) : SAT.Assignment :=
  fun index => !(assignment index)

theorem literal_eval_complement (literal : SAT.Literal) (assignment : SAT.Assignment) :
    literal.eval (complementAssignment assignment) = !(literal.eval assignment) := by
  cases literal with
  | mk index negated =>
      cases negated <;> cases value : assignment index <;>
        simp [SAT.Literal.eval, complementAssignment, value]

theorem naeClause_satisfies_complement (clause : Clause) (assignment : SAT.Assignment) :
    clause.Satisfies (complementAssignment assignment) ↔
      clause.Satisfies assignment := by
  rw [Clause.Satisfies, Clause.Satisfies,
    literal_eval_complement, literal_eval_complement, literal_eval_complement]
  cases clause.first.eval assignment <;>
    cases clause.second.eval assignment <;>
      cases clause.third.eval assignment <;> simp

theorem naeFormula_satisfies_complement (formula : Formula) (assignment : SAT.Assignment) :
    Formula.Satisfies formula (complementAssignment assignment) ↔
      Formula.Satisfies formula assignment := by
  constructor <;> intro satisfies clause member
  · exact (naeClause_satisfies_complement clause assignment).1
      (satisfies clause member)
  · exact (naeClause_satisfies_complement clause assignment).2
      (satisfies clause member)

theorem impossibleClause_not_satisfied (assignment : SAT.Assignment) :
    ¬ impossibleClause.Satisfies assignment := by
  simp [impossibleClause, Clause.Satisfies]

theorem nonemptyBlock_satisfies_iff_values
    (reference : Nat) (clause : SAT.Clause) (assignment : SAT.Assignment) :
    Formula.Satisfies (nonemptyBlock reference clause) assignment ↔
      nae3Values
          ((paddedClause clause).first.eval assignment)
          ((paddedClause clause).second.eval assignment)
          (assignment (auxiliaryVar reference clause)) ∧
        nae3Values
          (!(assignment (auxiliaryVar reference clause)))
          ((paddedClause clause).third.eval assignment)
          (assignment reference) := by
  simp [Formula.Satisfies, Clause.Satisfies, nonemptyBlock, nae3Values,
    SAT.Literal.eval_positive, SAT.Literal.eval_negative]

theorem sourceClause_satisfies_iff_padded_nae4
    (clause : SAT.Clause) (assignment : SAT.Assignment)
    (nonempty : clause.length ≠ 0) (three : clause.length ≤ 3) :
    SAT.Clause.Satisfies clause assignment ↔
      nae4Values
        ((paddedClause clause).first.eval assignment)
        ((paddedClause clause).second.eval assignment)
        ((paddedClause clause).third.eval assignment)
        false := by
  cases clause with
  | nil => simp at nonempty
  | cons first rest =>
      cases rest with
      | nil =>
          cases firstValue : first.eval assignment <;>
            simp [SAT.Clause.Satisfies, paddedClause, firstLiteral, secondLiteral,
              thirdLiteral, nae4Values, firstValue]
      | cons second rest =>
          cases rest with
          | nil =>
              cases firstValue : first.eval assignment <;>
                cases secondValue : second.eval assignment <;>
                  simp [SAT.Clause.Satisfies, paddedClause, firstLiteral, secondLiteral,
                    thirdLiteral, nae4Values, firstValue, secondValue]
          | cons third rest =>
              cases rest with
              | nil =>
                  cases firstValue : first.eval assignment <;>
                    cases secondValue : second.eval assignment <;>
                      cases thirdValue : third.eval assignment <;>
                        simp [SAT.Clause.Satisfies, paddedClause, firstLiteral, secondLiteral,
                          thirdLiteral, nae4Values, firstValue, secondValue, thirdValue]
              | cons fourth tail =>
                  simp only [List.length_cons] at three
                  omega

theorem firstLiteral_mem {clause : SAT.Clause} (nonempty : clause.length ≠ 0) :
    firstLiteral clause ∈ clause := by
  cases clause with
  | nil => simp at nonempty
  | cons first rest => simp [firstLiteral]

theorem secondLiteral_mem {clause : SAT.Clause} (nonempty : clause.length ≠ 0) :
    secondLiteral clause ∈ clause := by
  cases clause with
  | nil => simp at nonempty
  | cons first rest =>
      cases rest with
      | nil => simp [secondLiteral, firstLiteral]
      | cons second tail => simp [secondLiteral]

theorem thirdLiteral_mem {clause : SAT.Clause} (nonempty : clause.length ≠ 0) :
    thirdLiteral clause ∈ clause := by
  cases clause with
  | nil => simp at nonempty
  | cons first rest =>
      cases rest with
      | nil => simp [thirdLiteral, secondLiteral, firstLiteral]
      | cons second rest =>
          cases rest with
          | nil => simp [thirdLiteral, secondLiteral]
          | cons third tail => simp [thirdLiteral]

theorem sourceLiteral_var_lt_reference {formula : SAT.ThreeCNF}
    {clause : SAT.Clause} (clauseMember : clause ∈ formula.clauses)
    {literal : SAT.Literal} (literalMember : literal ∈ clause) :
    literal.var < referenceVar formula := by
  have belowSemanticBound :=
    SAT.CNF.clause_vars_lt_varBound clauseMember literal literalMember
  have semanticBound := SAT.satCNFVarBound_le_cnfStructured_inputSize formula.clauses
  have belowStructured :
      SAT.CNF.varBound formula.clauses ≤ referenceVar formula := by
    simpa [referenceVar, sourceEncoding,
      Karp21.threeCNFStructuredEncodedType, Karp21.cnfStructuredEncodedType,
      SAT.cnfStructuredEncodedType, SAT.clauseStructuredEncodedType,
      SAT.literalStructuredEncodedType, SAT.literalTupleStructuredEncodedType] using semanticBound
  exact belowSemanticBound.trans_le belowStructured

/-- Clause-local deterministic value stored in its injectively keyed auxiliary variable. -/
def clauseSplitWitness (assignment : SAT.Assignment) (clause : SAT.Clause) : Bool :=
  splitWitness
    ((paddedClause clause).first.eval assignment)
    ((paddedClause clause).second.eval assignment)
    ((paddedClause clause).third.eval assignment)

/-- Extend a satisfying source assignment with the reference and keyed auxiliaries. -/
noncomputable def forwardAssignment
    (formula : SAT.ThreeCNF) (assignment : SAT.Assignment) : SAT.Assignment :=
  fun index =>
    if index = referenceVar formula then false
    else if witness : ∃ clause ∈ formula.clauses,
        index = auxiliaryVar (referenceVar formula) clause then
      clauseSplitWitness assignment (Classical.choose witness)
    else assignment index

@[simp] theorem forwardAssignment_reference
    (formula : SAT.ThreeCNF) (assignment : SAT.Assignment) :
    forwardAssignment formula assignment (referenceVar formula) = false := by
  simp [forwardAssignment]

theorem forwardAssignment_source_index
    (formula : SAT.ThreeCNF) (assignment : SAT.Assignment)
    {index : Nat} (below : index < referenceVar formula) :
    forwardAssignment formula assignment index = assignment index := by
  classical
  have notReference : index ≠ referenceVar formula := Nat.ne_of_lt below
  have noAuxiliary : ¬ ∃ clause ∈ formula.clauses,
      index = auxiliaryVar (referenceVar formula) clause := by
    rintro ⟨clause, _member, equality⟩
    have above := reference_lt_auxiliaryVar (referenceVar formula) clause
    omega
  simp [forwardAssignment, notReference, noAuxiliary]

theorem forwardAssignment_source_literal_eval
    (formula : SAT.ThreeCNF) (assignment : SAT.Assignment)
    {clause : SAT.Clause} (clauseMember : clause ∈ formula.clauses)
    {literal : SAT.Literal} (literalMember : literal ∈ clause) :
    literal.eval (forwardAssignment formula assignment) = literal.eval assignment := by
  apply SAT.Clause.literal_eval_eq_of_var_eq
  exact forwardAssignment_source_index formula assignment
    (sourceLiteral_var_lt_reference clauseMember literalMember)

theorem forwardAssignment_auxiliary
    (formula : SAT.ThreeCNF) (assignment : SAT.Assignment)
    {clause : SAT.Clause} (clauseMember : clause ∈ formula.clauses) :
    forwardAssignment formula assignment
        (auxiliaryVar (referenceVar formula) clause) =
      clauseSplitWitness assignment clause := by
  classical
  let index := auxiliaryVar (referenceVar formula) clause
  have notReference : index ≠ referenceVar formula := by
    exact Nat.ne_of_gt (reference_lt_auxiliaryVar (referenceVar formula) clause)
  have hasWitness : ∃ candidate ∈ formula.clauses,
      index = auxiliaryVar (referenceVar formula) candidate :=
    ⟨clause, clauseMember, rfl⟩
  dsimp [index] at notReference hasWitness ⊢
  unfold forwardAssignment
  rw [if_neg notReference]
  rw [dif_pos hasWitness]
  have chosenSpec := Classical.choose_spec hasWitness
  have paddedEquality :
      paddedClause (Classical.choose hasWitness) = paddedClause clause := by
    apply (auxiliaryVar_eq_iff (referenceVar formula)
      (Classical.choose hasWitness) clause).1
    exact chosenSpec.2.symm
  simp [clauseSplitWitness, paddedEquality]

theorem clauseBlock_forward_satisfied
    (formula : SAT.ThreeCNF) (assignment : SAT.Assignment)
    {clause : SAT.Clause} (clauseMember : clause ∈ formula.clauses)
    (sourceSatisfies : SAT.Clause.Satisfies clause assignment) :
    Formula.Satisfies (clauseBlock (referenceVar formula) clause)
      (forwardAssignment formula assignment) := by
  by_cases empty : clause.length = 0
  · have clauseNil : clause = [] := List.length_eq_zero_iff.mp empty
    subst clause
    simp [SAT.Clause.Satisfies] at sourceSatisfies
  · rw [clauseBlock, if_neg empty]
    apply (nonemptyBlock_satisfies_iff_values
      (referenceVar formula) clause (forwardAssignment formula assignment)).2
    have three := formula.isThree clause clauseMember
    have sourceFour :=
      (sourceClause_satisfies_iff_padded_nae4 clause assignment empty three).1
        sourceSatisfies
    have split := splitWitness_correct sourceFour
    have firstEval :
        (paddedClause clause).first.eval (forwardAssignment formula assignment) =
          (paddedClause clause).first.eval assignment := by
      exact forwardAssignment_source_literal_eval formula assignment clauseMember
        (firstLiteral_mem empty)
    have secondEval :
        (paddedClause clause).second.eval (forwardAssignment formula assignment) =
          (paddedClause clause).second.eval assignment := by
      exact forwardAssignment_source_literal_eval formula assignment clauseMember
        (secondLiteral_mem empty)
    have thirdEval :
        (paddedClause clause).third.eval (forwardAssignment formula assignment) =
          (paddedClause clause).third.eval assignment := by
      exact forwardAssignment_source_literal_eval formula assignment clauseMember
        (thirdLiteral_mem empty)
    rw [firstEval, secondEval,
      forwardAssignment_auxiliary formula assignment clauseMember,
      thirdEval, forwardAssignment_reference]
    simpa [clauseSplitWitness] using split

theorem executable_forward_satisfied
    (formula : SAT.ThreeCNF) (assignment : SAT.Assignment)
    (sourceSatisfies : SAT.ThreeCNF.Satisfies formula assignment) :
    Formula.Satisfies (executable formula) (forwardAssignment formula assignment) := by
  intro targetClause targetMember
  rcases List.mem_flatMap.mp targetMember with
    ⟨sourceClause, sourceMember, targetInBlock⟩
  exact clauseBlock_forward_satisfied formula assignment sourceMember
    (sourceSatisfies sourceClause sourceMember) targetClause targetInBlock

/-- Normalize the global NAE symmetry so that the reference variable is false. -/
def normalizeAssignment (reference : Nat) (assignment : SAT.Assignment) : SAT.Assignment :=
  if assignment reference then complementAssignment assignment else assignment

@[simp] theorem normalizeAssignment_reference
    (reference : Nat) (assignment : SAT.Assignment) :
    normalizeAssignment reference assignment reference = false := by
  cases value : assignment reference <;>
    simp [normalizeAssignment, complementAssignment, value]

theorem normalizeAssignment_preserves_nae
    (reference : Nat) (formula : Formula) (assignment : SAT.Assignment) :
    Formula.Satisfies formula (normalizeAssignment reference assignment) ↔
      Formula.Satisfies formula assignment := by
  cases value : assignment reference
  · simp [normalizeAssignment, value]
  · simpa [normalizeAssignment, value] using
      naeFormula_satisfies_complement formula assignment

theorem executable_reverse_satisfied
    (formula : SAT.ThreeCNF) (assignment : SAT.Assignment)
    (targetSatisfies : Formula.Satisfies (executable formula) assignment) :
    SAT.ThreeCNF.Satisfies formula
      (normalizeAssignment (referenceVar formula) assignment) := by
  let normalized := normalizeAssignment (referenceVar formula) assignment
  have normalizedSatisfies : Formula.Satisfies (executable formula) normalized := by
    exact (normalizeAssignment_preserves_nae
      (referenceVar formula) (executable formula) assignment).2 targetSatisfies
  intro clause clauseMember
  have blockSatisfies :
      Formula.Satisfies (clauseBlock (referenceVar formula) clause) normalized := by
    intro targetClause targetMember
    exact normalizedSatisfies targetClause
      (List.mem_flatMap.mpr ⟨clause, clauseMember, targetMember⟩)
  have normalizedReference : normalized (referenceVar formula) = false := by
    exact normalizeAssignment_reference (referenceVar formula) assignment
  by_cases empty : clause.length = 0
  · have impossibleMember : impossibleClause ∈
        clauseBlock (referenceVar formula) clause := by
      simp [clauseBlock, empty]
    exact False.elim
      (impossibleClause_not_satisfied normalized
        (blockSatisfies impossibleClause impossibleMember))
  · have values :=
      (nonemptyBlock_satisfies_iff_values
        (referenceVar formula) clause normalized).1
        (by simpa [clauseBlock, empty] using blockSatisfies)
    have four := split_sound values.1 values.2
    apply (sourceClause_satisfies_iff_padded_nae4 clause normalized empty
      (formula.isThree clause clauseMember)).2
    simpa [normalizedReference] using four

/-- Exact semantic law of the complete 3SAT-to-NAE-3SAT executable. -/
theorem executable_correct (formula : SAT.ThreeCNF) :
    SAT.ThreeCNF.Satisfiable formula ↔ Formula.Satisfiable (executable formula) := by
  constructor
  · rintro ⟨assignment, sourceSatisfies⟩
    exact ⟨forwardAssignment formula assignment,
      executable_forward_satisfied formula assignment sourceSatisfies⟩
  · rintro ⟨assignment, targetSatisfies⟩
    exact ⟨normalizeAssignment (referenceVar formula) assignment,
      executable_reverse_satisfied formula assignment targetSatisfies⟩

/-! ### Direct-TM construction -/

theorem literalKey_tmPolyTime :
    TMPolyTimeMap literalEncoding EncodedType.nat literalKey := by
  have variableMap : TMPolyTimeMap literalEncoding EncodedType.nat
      (fun literal : SAT.Literal => literal.var) :=
    Karp21.Clique.literal_var_tm_polytime
  have polarity : TMPolyTimeMap literalEncoding EncodedType.bool
      (fun literal : SAT.Literal => literal.neg) :=
    Karp21.Clique.literal_neg_tm_polytime
  have polarityNat : TMPolyTimeMap literalEncoding EncodedType.nat
      (fun literal : SAT.Literal => boolToNat literal.neg) := by
    have composed := TMPolyTimeMap.comp boolToNat_tm_polytime polarity
    simpa [Function.comp] using composed
  have paired := TMPolyTimeMap.prod_mk variableMap polarityNat
  have composed := TMPolyTimeMap.comp natPair_tm_polytime paired
  simpa [literalKey, Function.comp] using composed

/-- Rewrap a nested literal payload as the exact public NAE clause. -/
def clauseOfPayload
    (payload : Presentation.NAEThreeSAT.clausePayloadEncodedType.Carrier) : Clause where
  first := payload.1
  second := payload.2.1
  third := payload.2.2

theorem clauseOfPayload_tmPolyTime :
    TMPolyTimeMap Presentation.NAEThreeSAT.clausePayloadEncodedType
      targetClauseEncoding clauseOfPayload := by
  apply TMPolyTimeMap.of_encodingEquiv
    Presentation.NAEThreeSAT.clausePayloadEncodedType targetClauseEncoding
    clauseOfPayload (Equiv.refl _)
  intro payload
  change Presentation.NAEThreeSAT.clausePayloadEncodedType.encode payload =
    List.map id (Presentation.NAEThreeSAT.clausePayloadEncodedType.encode payload)
  rw [List.map_id]

theorem clauseKey_tmPolyTime :
    TMPolyTimeMap targetClauseEncoding EncodedType.nat clauseKey := by
  let Payload := Presentation.NAEThreeSAT.clausePayloadEncodedType
  have first : TMPolyTimeMap targetClauseEncoding literalEncoding
      (fun clause : Clause => clause.first) := by
    have payload : TMPolyTimeMap targetClauseEncoding Payload
        (fun clause : Clause => (clause.first, (clause.second, clause.third))) := by
      apply TMPolyTimeMap.of_encodingEquiv targetClauseEncoding Payload
        (fun clause : Clause => (clause.first, (clause.second, clause.third)))
        (Equiv.refl _)
      intro clause
      change Payload.encode (clause.first, (clause.second, clause.third)) =
        List.map id (Payload.encode (clause.first, (clause.second, clause.third)))
      rw [List.map_id]
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst literalEncoding
        (EncodedType.prod literalEncoding literalEncoding)) payload
    simpa [Function.comp, Payload] using composed
  have tail : TMPolyTimeMap targetClauseEncoding
      (EncodedType.prod literalEncoding literalEncoding)
      (fun clause : Clause => (clause.second, clause.third)) := by
    let Payload := Presentation.NAEThreeSAT.clausePayloadEncodedType
    have payload : TMPolyTimeMap targetClauseEncoding Payload
        (fun clause : Clause => (clause.first, (clause.second, clause.third))) := by
      apply TMPolyTimeMap.of_encodingEquiv targetClauseEncoding Payload
        (fun clause : Clause => (clause.first, (clause.second, clause.third)))
        (Equiv.refl _)
      intro clause
      change Payload.encode (clause.first, (clause.second, clause.third)) =
        List.map id (Payload.encode (clause.first, (clause.second, clause.third)))
      rw [List.map_id]
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd literalEncoding
        (EncodedType.prod literalEncoding literalEncoding)) payload
    simpa [Function.comp, Payload] using composed
  have second : TMPolyTimeMap targetClauseEncoding literalEncoding
      (fun clause : Clause => clause.second) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst literalEncoding literalEncoding) tail
    simpa [Function.comp] using composed
  have third : TMPolyTimeMap targetClauseEncoding literalEncoding
      (fun clause : Clause => clause.third) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd literalEncoding literalEncoding) tail
    simpa [Function.comp] using composed
  have firstCode := TMPolyTimeMap.comp literalKey_tmPolyTime first
  have secondCode := TMPolyTimeMap.comp literalKey_tmPolyTime second
  have thirdCode := TMPolyTimeMap.comp literalKey_tmPolyTime third
  have innerInput := TMPolyTimeMap.prod_mk secondCode thirdCode
  have inner := TMPolyTimeMap.comp natPair_tm_polytime innerInput
  have outerInput := TMPolyTimeMap.prod_mk firstCode inner
  have outer := TMPolyTimeMap.comp natPair_tm_polytime outerInput
  simpa [clauseKey, Function.comp] using outer

theorem paddedClause_tmPolyTime :
    TMPolyTimeMap sourceClauseEncoding targetClauseEncoding paddedClause := by
  have payload : TMPolyTimeMap sourceClauseEncoding
      Presentation.NAEThreeSAT.clausePayloadEncodedType
      (fun clause : SAT.Clause =>
        (firstLiteral clause,
          (secondLiteral clause, thirdLiteral clause))) := by
    exact TMPolyTimeMap.prod_mk firstLiteral_tmPolyTime
      (TMPolyTimeMap.prod_mk secondLiteral_tmPolyTime thirdLiteral_tmPolyTime)
  have composed := TMPolyTimeMap.comp clauseOfPayload_tmPolyTime payload
  simpa [paddedClause, clauseOfPayload, Function.comp] using composed

theorem auxiliaryVar_tmPolyTime :
    TMPolyTimeMap (EncodedType.prod EncodedType.nat sourceClauseEncoding)
      EncodedType.nat (fun input : Nat × SAT.Clause => auxiliaryVar input.1 input.2) := by
  let X := EncodedType.prod EncodedType.nat sourceClauseEncoding
  have reference : TMPolyTimeMap X EncodedType.nat
      (fun input : Nat × SAT.Clause => input.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.nat sourceClauseEncoding
  have sourceClause : TMPolyTimeMap X sourceClauseEncoding
      (fun input : Nat × SAT.Clause => input.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.nat sourceClauseEncoding
  have padded : TMPolyTimeMap X targetClauseEncoding
      (fun input : Nat × SAT.Clause => paddedClause input.2) := by
    have composed := TMPolyTimeMap.comp paddedClause_tmPolyTime sourceClause
    simpa [Function.comp, X] using composed
  have key : TMPolyTimeMap X EncodedType.nat
      (fun input : Nat × SAT.Clause => clauseKey (paddedClause input.2)) := by
    have composed := TMPolyTimeMap.comp clauseKey_tmPolyTime padded
    simpa [Function.comp, X] using composed
  have sumInput := TMPolyTimeMap.prod_mk reference key
  have sum := TMPolyTimeMap.comp natAdd_tm_polytime sumInput
  have successor := TMPolyTimeMap.comp Karp21.natSuccTMBackedMap.tm_polytime sum
  simpa [auxiliaryVar, Function.comp, X, Nat.add_assoc] using successor

private theorem literalPositive_tmPolyTime {X : EncodedType}
    {value : X.Carrier → Nat} (valueTM : TMPolyTimeMap X EncodedType.nat value) :
    TMPolyTimeMap X literalEncoding (fun input => SAT.Literal.positive (value input)) := by
  have composed := TMPolyTimeMap.comp Karp21.posAuxTMBackedMap.tm_polytime valueTM
  simpa [SAT.Clause.posAux, SAT.Literal.positive, Function.comp] using composed

private theorem literalNegative_tmPolyTime {X : EncodedType}
    {value : X.Carrier → Nat} (valueTM : TMPolyTimeMap X EncodedType.nat value) :
    TMPolyTimeMap X literalEncoding (fun input => SAT.Literal.negative (value input)) := by
  have composed := TMPolyTimeMap.comp Karp21.negAuxTMBackedMap.tm_polytime valueTM
  simpa [SAT.Clause.negAux, SAT.Literal.negative, Function.comp] using composed

private theorem exactClause_tmPolyTime {X : EncodedType}
    {first second third : X.Carrier → SAT.Literal}
    (firstTM : TMPolyTimeMap X literalEncoding first)
    (secondTM : TMPolyTimeMap X literalEncoding second)
    (thirdTM : TMPolyTimeMap X literalEncoding third) :
    TMPolyTimeMap X targetClauseEncoding
      (fun input => Clause.mk (first input) (second input) (third input)) := by
  have payload := TMPolyTimeMap.prod_mk firstTM (TMPolyTimeMap.prod_mk secondTM thirdTM)
  have composed := TMPolyTimeMap.comp clauseOfPayload_tmPolyTime payload
  simpa [clauseOfPayload, Function.comp] using composed

theorem nonemptyBlockFromPair_tmPolyTime :
    TMPolyTimeMap (EncodedType.prod EncodedType.nat sourceClauseEncoding)
      targetEncoding (fun input : Nat × SAT.Clause => nonemptyBlock input.1 input.2) := by
  let X := EncodedType.prod EncodedType.nat sourceClauseEncoding
  have sourceClause : TMPolyTimeMap X sourceClauseEncoding
      (fun input : Nat × SAT.Clause => input.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.nat sourceClauseEncoding
  have reference : TMPolyTimeMap X EncodedType.nat
      (fun input : Nat × SAT.Clause => input.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.nat sourceClauseEncoding
  have first : TMPolyTimeMap X literalEncoding
      (fun input : Nat × SAT.Clause => firstLiteral input.2) := by
    have composed := TMPolyTimeMap.comp firstLiteral_tmPolyTime sourceClause
    simpa [Function.comp, X] using composed
  have second : TMPolyTimeMap X literalEncoding
      (fun input : Nat × SAT.Clause => secondLiteral input.2) := by
    have composed := TMPolyTimeMap.comp secondLiteral_tmPolyTime sourceClause
    simpa [Function.comp, X] using composed
  have third : TMPolyTimeMap X literalEncoding
      (fun input : Nat × SAT.Clause => thirdLiteral input.2) := by
    have composed := TMPolyTimeMap.comp thirdLiteral_tmPolyTime sourceClause
    simpa [Function.comp, X] using composed
  have auxiliary : TMPolyTimeMap X EncodedType.nat
      (fun input : Nat × SAT.Clause => auxiliaryVar input.1 input.2) := by
    simpa [X] using auxiliaryVar_tmPolyTime
  have positiveAux := literalPositive_tmPolyTime auxiliary
  have negativeAux := literalNegative_tmPolyTime auxiliary
  have positiveReference := literalPositive_tmPolyTime reference
  have firstClause := exactClause_tmPolyTime first second positiveAux
  have secondClause := exactClause_tmPolyTime negativeAux third positiveReference
  have secondSingleton := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_singleton targetClauseEncoding) secondClause
  have listInput := TMPolyTimeMap.prod_mk firstClause secondSingleton
  have output := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons targetClauseEncoding) listInput
  simpa [nonemptyBlock, paddedClause, Function.comp, X] using output

private theorem sourceClauseIsEmpty_tmPolyTime :
    TMPolyTimeMap sourceClauseEncoding EncodedType.bool
      (fun clause : SAT.Clause => decide (clause.length = 0)) := by
  have zero : TMPolyTimeMap sourceClauseEncoding EncodedType.nat
      (fun _ : SAT.Clause => (show Nat from 0)) :=
    TMPolyTimeMap.const sourceClauseEncoding EncodedType.nat (show Nat from 0)
  have pair := TMPolyTimeMap.prod_mk clauseLength_tmPolyTime zero
  have output := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq pair
  convert output using 1

theorem clauseBlockFromPair_tmPolyTime :
    TMPolyTimeMap (EncodedType.prod EncodedType.nat sourceClauseEncoding)
      targetEncoding clauseBlockFromPair := by
  let X := EncodedType.prod EncodedType.nat sourceClauseEncoding
  have sourceClause : TMPolyTimeMap X sourceClauseEncoding
      (fun input : Nat × SAT.Clause => input.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.nat sourceClauseEncoding
  have emptyFlag : TMPolyTimeMap X EncodedType.bool
      (fun input : Nat × SAT.Clause => decide (input.2.length = 0)) := by
    have composed := TMPolyTimeMap.comp sourceClauseIsEmpty_tmPolyTime sourceClause
    simpa [Function.comp, X] using composed
  have tagged := TMPolyTimeMap.prod_mk emptyFlag (TMPolyTimeMap.id X)
  have impossible : TMPolyTimeMap X targetEncoding
      (fun _ : X.Carrier => [impossibleClause]) :=
    TMPolyTimeMap.const X targetEncoding [impossibleClause]
  have dispatched := boolProduct_dispatch_tm_polytime X targetEncoding
    (fFalse := fun input : X.Carrier => nonemptyBlock input.1 input.2)
    (fTrue := fun _ : X.Carrier => [impossibleClause])
    (by simpa [X] using nonemptyBlockFromPair_tmPolyTime) impossible
  have output := TMPolyTimeMap.comp dispatched tagged
  convert output using 1
  funext input
  cases emptyFlagValue : decide (input.2.length = 0)
  · have notEmpty : input.2.length ≠ 0 := by
      simpa using emptyFlagValue
    simp [clauseBlockFromPair, clauseBlock, Function.comp, notEmpty]
  · have empty : input.2.length = 0 := by
      simpa using emptyFlagValue
    simp [clauseBlockFromPair, clauseBlock, Function.comp, empty]
    rfl

private theorem sourceClauses_tmPolyTime :
    TMPolyTimeMap sourceEncoding (EncodedType.list sourceClauseEncoding)
      (fun formula : SAT.ThreeCNF => formula.clauses) :=
  TMPolyTimeMap.of_encodingEquiv sourceEncoding
    (EncodedType.list sourceClauseEncoding)
    (fun formula : SAT.ThreeCNF => formula.clauses) (Equiv.refl _) (by
      intro formula
      change (EncodedType.list sourceClauseEncoding).encode formula.clauses =
        (sourceEncoding.encode formula).map id
      simp [sourceClauseEncoding,
        Karp21.threeCNFStructuredEncodedType, Karp21.cnfStructuredEncodedType])

theorem referenceVar_tmPolyTime :
    TMPolyTimeMap sourceEncoding EncodedType.nat referenceVar := by
  simpa [referenceVar] using
    (Karp21.encodedInputSizeNatTMBackedMap sourceEncoding).tm_polytime

/-- The complete exact executable is direct-TM polynomial time. -/
theorem executable_tmPolyTime :
    TMPolyTimeMap sourceEncoding targetEncoding executable := by
  let ContextualClause := EncodedType.prod EncodedType.nat sourceClauseEncoding
  let ContextualClauses := EncodedType.list ContextualClause
  let Blocks := EncodedType.list targetEncoding
  have clauses := sourceClauses_tmPolyTime
  have attachInput : TMPolyTimeMap sourceEncoding
      (EncodedType.prod EncodedType.nat (EncodedType.list sourceClauseEncoding))
      (fun formula : SAT.ThreeCNF => (referenceVar formula, formula.clauses)) :=
    TMPolyTimeMap.prod_mk referenceVar_tmPolyTime clauses
  have attached : TMPolyTimeMap sourceEncoding ContextualClauses
      (fun formula : SAT.ThreeCNF =>
        Program.contextListMapExecutable
          (C := EncodedType.nat) (X := sourceClauseEncoding)
          (referenceVar formula, formula.clauses)) := by
    have composed := TMPolyTimeMap.comp
      (Program.contextListMapExecutable_tmPolyTime EncodedType.nat sourceClauseEncoding)
      attachInput
    simpa [Function.comp, ContextualClause, ContextualClauses] using composed
  have blocks : TMPolyTimeMap sourceEncoding Blocks
      (fun formula : SAT.ThreeCNF =>
        (Program.contextListMapExecutable
          (C := EncodedType.nat) (X := sourceClauseEncoding)
          (referenceVar formula, formula.clauses)).map clauseBlockFromPair) := by
    have mapped := TMPolyTimeMap.list_map clauseBlockFromPair_tmPolyTime
    have composed := TMPolyTimeMap.comp mapped attached
    simpa [Function.comp, Blocks, ContextualClauses, ContextualClause] using composed
  have flattened := TMPolyTimeMap.comp
    (Program.listFlatten_tmPolyTime targetClauseEncoding) blocks
  convert flattened using 1
  funext formula
  simp only [Function.comp_apply]
  rw [Program.contextListMapExecutable_eq_map]
  unfold executable
  generalize formula.clauses = clauses
  induction clauses with
  | nil => rfl
  | cons clause clauses inductionHypothesis =>
      have appended := congrArg
        (fun tail => clauseBlock (referenceVar formula) clause ++ tail)
        inductionHypothesis
      simpa only [List.flatMap_cons, List.map_cons, List.flatten_cons,
        clauseBlockFromPair] using appended

/-! ### Exact public endpoints and raw reduction evidence -/

/-- Canonical exact structured bundled-3SAT source endpoint. -/
abbrev sourceProblem : Encoding.PresentedProblem :=
  Problems.Karp21.Satisfiability.threeSATStructuredProblem

/-- Canonical exact public NAE-3SAT target endpoint. -/
abbrev targetProblem : Encoding.PresentedProblem :=
  Presentation.NAEThreeSAT.structuredProblem

/-- Raw endpoint-exact direct-TM Karp reduction for staged authoring. -/
noncomputable def threeSATToNAEThreeSATStructuredTMKarpReduction :
    TMKarpReduction sourceProblem.toEncodedDecisionProblem
      targetProblem.toEncodedDecisionProblem where
  f := executable
  polytime := by
    simpa [sourceProblem, targetProblem,
      Problems.Karp21.Satisfiability.threeSATStructuredProblem,
      Problems.Karp21.Satisfiability.threeSATStructuredPresentation,
      Presentation.NAEThreeSAT.structuredProblem,
      Presentation.NAEThreeSAT.structuredPresentation] using executable_tmPolyTime
  correct := by
    intro formula
    change SAT.ThreeCNF.Satisfiable formula ↔ Formula.Satisfiable (executable formula)
    exact executable_correct formula

assert_standard_axioms
  literalKey_injective,
  clauseKey_injective,
  sourceLiteral_var_lt_reference,
  forwardAssignment_auxiliary,
  executable_forward_satisfied,
  executable_reverse_satisfied,
  executable_correct,
  paddedClause_tmPolyTime,
  auxiliaryVar_tmPolyTime,
  nonemptyBlockFromPair_tmPolyTime,
  clauseBlockFromPair_tmPolyTime,
  executable_tmPolyTime,
  threeSATToNAEThreeSATStructuredTMKarpReduction

end ThreeSATToNAEThreeSAT
end Domain
end ComplexityReduction
