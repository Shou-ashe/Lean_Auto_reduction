/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import ComplexityReduction.Domain.FiniteDomainCSPToStructuredCNFOneHotFacts

/-!
Semantic correctness of the exact direct structured program for generic
finite-domain CSP to one-hot CNF.

All relation information used by the program comes from the caller-supplied
`ExecutableLanguageContract.relationRows`.  The proof never constructs an
executable relation table from proposition-valued `Rel.Holds` data.  Empty
domains, empty formulas, and repeated variables in a constraint scope are
handled by the same concrete program output.
-/

namespace ComplexityReduction.Domain.FiniteDomainCSPToStructuredCNFSemantics

open ComplexityReduction
open ComplexityReduction.CSP.FiniteDomain
open FiniteDomainCSPExecutableContract
open FiniteDomainCSPToStructuredCNFProgram
open FiniteDomainCSPToStructuredCNFOneHotFacts

theorem forbiddenRowClause_satisfies_iff {arity : Nat}
    (scope : Fin arity → Nat) (row : List Nat) (rowLength : row.length = arity)
    (assignment : SAT.Assignment) :
    SAT.Clause.Satisfies
        (forbiddenRowClause row (List.ofFn scope)) assignment ↔
      ∃ index : Fin arity,
        assignment (Nat.pair (scope index) (row.getD index.val 0)) = false := by
  rw [forbiddenRowClause_eq_ofFn scope row rowLength]
  constructor
  · rintro ⟨literal, literalMem, literalTrue⟩
    rcases List.mem_ofFn.mp literalMem with ⟨index, rfl⟩
    exact ⟨index, by simpa [SAT.Literal.eval] using literalTrue⟩
  · rintro ⟨index, indexFalse⟩
    have indexBound : index.val < row.length := by
      rw [rowLength]
      exact index.isLt
    refine ⟨{ var := Nat.pair (scope index) (row.getD index.val 0), neg := true },
      List.mem_ofFn.mpr ⟨index, rfl⟩, ?_⟩
    simpa [SAT.Literal.eval, List.getD, indexBound] using indexFalse

def encodeAssignment {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) (source : Assignment D) :
    SAT.Assignment :=
  fun encodedVar =>
    decide ((Nat.unpair encodedVar).2 =
      contract.valueCode (source (Nat.unpair encodedVar).1))

@[simp]
theorem encodeAssignment_pair {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) (source : Assignment D)
    (sourceVar value : Nat) :
    encodeAssignment contract source (Nat.pair sourceVar value) =
      decide (value = contract.valueCode (source sourceVar)) := by
  simp [encodeAssignment, Nat.unpair_pair]

@[simp]
theorem encodeAssignment_pair_eq_true_iff {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) (source : Assignment D)
    (sourceVar value : Nat) :
    encodeAssignment contract source (Nat.pair sourceVar value) = true ↔
      value = contract.valueCode (source sourceVar) := by
  simp

theorem encodeAssignment_oneHotAt {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) (source : Assignment D)
    (sourceVar : Nat) :
    OneHotAt contract.domainSize sourceVar (encodeAssignment contract source) := by
  refine ⟨contract.valueCode (source sourceVar),
    contract.valueCode_lt_domainSize (source sourceVar), by simp, ?_⟩
  intro other otherBound otherTrue
  exact (encodeAssignment_pair_eq_true_iff contract source sourceVar other).1 otherTrue

noncomputable def decodeCode (domainSize : Nat) (domainPositive : 0 < domainSize)
    (assignment : SAT.Assignment) (sourceVar : Nat) : Fin domainSize :=
  if hasTrue : ∃ value, value < domainSize ∧
      assignment (Nat.pair sourceVar value) = true then
    ⟨Classical.choose hasTrue, (Classical.choose_spec hasTrue).1⟩
  else
    ⟨0, domainPositive⟩

noncomputable def decodeAssignment {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ)
    (domainPositive : 0 < contract.domainSize)
    (assignment : SAT.Assignment) : Assignment D :=
  fun sourceVar =>
    contract.domainEquiv.symm
      (decodeCode contract.domainSize domainPositive assignment sourceVar)

theorem decodeCode_true_of_oneHotAt (domainSize : Nat)
    (domainPositive : 0 < domainSize) (assignment : SAT.Assignment)
    (sourceVar : Nat) (oneHot : OneHotAt domainSize sourceVar assignment) :
    assignment
      (Nat.pair sourceVar
        (decodeCode domainSize domainPositive assignment sourceVar).val) = true := by
  rcases oneHot with ⟨value, valueBound, valueTrue, _⟩
  rw [decodeCode]
  split
  · exact (Classical.choose_spec ‹∃ value, value < domainSize ∧
      assignment (Nat.pair sourceVar value) = true›).2
  · exact (‹¬∃ value, value < domainSize ∧
      assignment (Nat.pair sourceVar value) = true›
        ⟨value, valueBound, valueTrue⟩).elim

theorem decodeAssignment_valueCode_true_of_oneHotAt
    {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ)
    (domainPositive : 0 < contract.domainSize)
    (assignment : SAT.Assignment) (sourceVar : Nat)
    (oneHot : OneHotAt contract.domainSize sourceVar assignment) :
    assignment
      (Nat.pair sourceVar
        (contract.valueCode
          (decodeAssignment contract domainPositive assignment sourceVar))) = true := by
  simpa [decodeAssignment, ExecutableLanguageContract.valueCode] using
    decodeCode_true_of_oneHotAt contract.domainSize domainPositive assignment sourceVar oneHot

@[simp]
theorem tupleCode_assignmentTuple {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) (constraint : Constraint Γ)
    (source : Assignment D) :
    contract.tupleCode (constraint.assignmentTuple source) =
      List.ofFn (fun index => contract.valueCode (source (constraint.vars index))) :=
  rfl

theorem tupleCode_entry_lt {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) {arity : Nat}
    (tuple : Tuple D arity) (value : Nat)
    (valueMem : value ∈ contract.tupleCode tuple) :
    value < contract.domainSize := by
  rcases List.mem_ofFn.mp valueMem with ⟨index, equality⟩
  rw [← equality]
  exact contract.valueCode_lt_domainSize (tuple index)

theorem relationCNF_satisfies_encode_of_constraint_satisfies
    {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) (constraint : Constraint Γ)
    (source : Assignment D) (sourceSatisfies : Constraint.Satisfies constraint source) :
    SAT.CNF.Satisfies
      (symbolRelationCNF contract constraint.symbol constraint.varsList)
      (encodeAssignment contract source) := by
  intro clause clauseMem
  rcases List.mem_map.mp clauseMem with ⟨row, rowMem, rfl⟩
  have rowFacts :=
    (mem_falsifyingRows_iff contract constraint.symbol row).1 rowMem
  have actualMem :
      contract.tupleCode (constraint.assignmentTuple source) ∈
        contract.relationRows constraint.symbol :=
    (contract.holds_iff_encodedTuple_mem constraint.symbol
      (constraint.assignmentTuple source)).1 sourceSatisfies
  have rowNe :
      row ≠ contract.tupleCode (constraint.assignmentTuple source) := by
    intro rowEq
    exact rowFacts.2.2 (rowEq ▸ actualMem)
  have mismatch : ∃ index : Fin (Γ.relationOf constraint.symbol).arity,
      row.getD index.val 0 ≠
        contract.valueCode (source (constraint.vars index)) := by
    by_contra noMismatch
    apply rowNe
    apply List.ext_getElem
    · rw [rowFacts.1, contract.tupleCode_length]
    · intro index rowBound tupleBound
      have arityBound : index < (Γ.relationOf constraint.symbol).arity := by
        rw [← rowFacts.1]
        exact rowBound
      have equality : row.getD index 0 =
          contract.valueCode (source (constraint.vars ⟨index, arityBound⟩)) := by
        by_contra indexMismatch
        exact noMismatch ⟨⟨index, arityBound⟩, indexMismatch⟩
      simpa [List.getD, rowBound, tupleBound] using equality
  rcases mismatch with ⟨index, mismatch⟩
  have rowBound : index.val < row.length := by
    rw [rowFacts.1]
    exact index.isLt
  have mismatch' :
      row[index.val]?.getD 0 ≠
        contract.valueCode (source (constraint.vars index)) := by
    simpa [List.getD, rowBound] using mismatch
  have clauseTrue :=
    (forbiddenRowClause_satisfies_iff constraint.vars row rowFacts.1
      (encodeAssignment contract source)).2 ⟨index, by
        simp [mismatch']⟩
  simpa [Constraint.varsList] using clauseTrue

theorem sourceConstraintCNF_satisfies_encode_of_constraint_satisfies
    {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) (constraint : Constraint Γ)
    (source : Assignment D) (sourceSatisfies : Constraint.Satisfies constraint source) :
    SAT.CNF.Satisfies (sourceConstraintCNF contract constraint)
      (encodeAssignment contract source) := by
  apply (SAT.CNF.satisfies_append
    (scopeExactlyOneCNF contract constraint.varsList)
    (symbolRelationCNF contract constraint.symbol constraint.varsList)
    (encodeAssignment contract source)).2
  constructor
  · exact (scopeExactlyOneCNF_satisfies_iff contract constraint.varsList
      (encodeAssignment contract source)).2
        (fun sourceVar _ => encodeAssignment_oneHotAt contract source sourceVar)
  · exact relationCNF_satisfies_encode_of_constraint_satisfies
      contract constraint source sourceSatisfies

theorem constraint_satisfies_decode_of_sourceConstraintCNF_satisfies
    {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ)
    (domainPositive : 0 < contract.domainSize)
    (assignment : SAT.Assignment) (constraint : Constraint Γ)
    (cnfSatisfies : SAT.CNF.Satisfies
      (sourceConstraintCNF contract constraint) assignment) :
    Constraint.Satisfies constraint
      (decodeAssignment contract domainPositive assignment) := by
  have blockFacts :
      SAT.CNF.Satisfies
          (scopeExactlyOneCNF contract constraint.varsList) assignment ∧
        SAT.CNF.Satisfies
          (symbolRelationCNF contract constraint.symbol constraint.varsList) assignment := by
    simpa [sourceConstraintCNF] using
      (SAT.CNF.satisfies_append
        (scopeExactlyOneCNF contract constraint.varsList)
        (symbolRelationCNF contract constraint.symbol constraint.varsList)
        assignment).1 cnfSatisfies
  have scopeOneHot : ∀ sourceVar, sourceVar ∈ constraint.varsList →
      OneHotAt contract.domainSize sourceVar assignment :=
    (scopeExactlyOneCNF_satisfies_iff contract constraint.varsList assignment).1
      blockFacts.1
  let decoded : Assignment D :=
    decodeAssignment contract domainPositive assignment
  apply (contract.holds_iff_encodedTuple_mem constraint.symbol
    (constraint.assignmentTuple decoded)).2
  let actualRow : List Nat :=
    encodeTuple contract.domainEquiv (constraint.assignmentTuple decoded)
  change actualRow ∈ contract.relationRows constraint.symbol
  by_contra actualNotMem
  have actualLength :
      actualRow.length = (Γ.relationOf constraint.symbol).arity := by
    simp [actualRow, encodeTuple]
  have actualBound : ∀ value, value ∈ actualRow →
      value < contract.domainSize := by
    intro value valueMem
    unfold actualRow at valueMem
    rcases List.mem_ofFn.mp valueMem with ⟨index, rfl⟩
    exact contract.valueCode_lt_domainSize
      (constraint.assignmentTuple decoded index)
  have actualFalsifying :
      actualRow ∈ falsifyingRows contract constraint.symbol :=
    (mem_falsifyingRows_iff contract constraint.symbol actualRow).2
      ⟨actualLength, actualBound, actualNotMem⟩
  have clauseMem :
      forbiddenRowClause actualRow constraint.varsList ∈
        symbolRelationCNF contract constraint.symbol constraint.varsList := by
    exact List.mem_map.mpr ⟨actualRow, actualFalsifying, rfl⟩
  have clauseTrue := blockFacts.2 _ clauseMem
  have mismatch :=
    (forbiddenRowClause_satisfies_iff constraint.vars actualRow actualLength assignment).1
      (by simpa [Constraint.varsList] using clauseTrue)
  rcases mismatch with ⟨index, indexFalse⟩
  have variableMem : constraint.vars index ∈ constraint.varsList := by
    exact List.mem_ofFn.mpr ⟨index, rfl⟩
  have selectedTrue :=
    decodeAssignment_valueCode_true_of_oneHotAt contract domainPositive assignment
      (constraint.vars index)
      (scopeOneHot (constraint.vars index) variableMem)
  have selectedTrue' :
      assignment
        (Nat.pair (constraint.vars index)
          (contract.valueCode (decoded (constraint.vars index)))) = true := by
    simpa [decoded] using selectedTrue
  have actualEntry :
      actualRow.getD index.val 0 =
        contract.valueCode (decoded (constraint.vars index)) := by
    simp [actualRow, encodeTuple, Constraint.assignmentTuple,
      ExecutableLanguageContract.valueCode, List.getD, index.isLt]
  rw [actualEntry] at indexFalse
  rw [selectedTrue'] at indexFalse
  contradiction

theorem sourceFormulaCNF_satisfies_iff {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) (formula : Formula Γ)
    (assignment : SAT.Assignment) :
    SAT.CNF.Satisfies (sourceFormulaCNF contract formula) assignment ↔
      ∀ constraint, constraint ∈ formula →
        SAT.CNF.Satisfies (sourceConstraintCNF contract constraint) assignment := by
  constructor
  · intro satisfies constraint constraintMem clause clauseMem
    exact satisfies clause (by
      rw [sourceFormulaCNF, List.mem_flatMap]
      exact ⟨constraint, constraintMem, clauseMem⟩)
  · intro satisfies clause clauseMem
    rw [sourceFormulaCNF, List.mem_flatMap] at clauseMem
    rcases clauseMem with ⟨constraint, constraintMem, clauseMem⟩
    exact satisfies constraint constraintMem clause clauseMem

theorem sourceFormulaCNF_satisfies_encode_of_formula_satisfies
    {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) (formula : Formula Γ)
    (source : Assignment D) (sourceSatisfies : Formula.Satisfies formula source) :
    SAT.CNF.Satisfies (sourceFormulaCNF contract formula)
      (encodeAssignment contract source) := by
  apply (sourceFormulaCNF_satisfies_iff contract formula
    (encodeAssignment contract source)).2
  intro constraint constraintMem
  exact sourceConstraintCNF_satisfies_encode_of_constraint_satisfies
    contract constraint source (sourceSatisfies constraint constraintMem)

theorem initialCNF_satisfies_iff {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) (assignment : SAT.Assignment) :
    SAT.CNF.Satisfies (initialCNF contract) assignment ↔
      contract.domainSize ≠ 0 := by
  by_cases domainZero : contract.domainSize = 0
  · simp [initialCNF, domainZero, SAT.CNF.Satisfies, SAT.Clause.Satisfies]
  · simp [initialCNF, domainZero]

/-- The direct structured program preserves exactly generic CSP satisfiability. -/
theorem formulaToCNF_satisfiable_iff {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) (formula : Formula Γ) :
    SAT.CNF.Satisfiable (formulaToCNF contract formula) ↔
      Formula.Satisfiable formula := by
  constructor
  · rintro ⟨assignment, cnfSatisfies⟩
    have outputFacts :
        SAT.CNF.Satisfies (initialCNF contract) assignment ∧
          SAT.CNF.Satisfies (sourceFormulaCNF contract formula) assignment := by
      rw [formulaToCNF_closedForm] at cnfSatisfies
      exact (SAT.CNF.satisfies_append
        (initialCNF contract) (sourceFormulaCNF contract formula) assignment).1
        cnfSatisfies
    have domainNonzero : contract.domainSize ≠ 0 :=
      (initialCNF_satisfies_iff contract assignment).1 outputFacts.1
    have domainPositive : 0 < contract.domainSize := Nat.pos_of_ne_zero domainNonzero
    refine ⟨decodeAssignment contract domainPositive assignment, ?_⟩
    intro constraint constraintMem
    exact constraint_satisfies_decode_of_sourceConstraintCNF_satisfies
      contract domainPositive assignment constraint
      ((sourceFormulaCNF_satisfies_iff contract formula assignment).1
        outputFacts.2 constraint constraintMem)
  · rintro ⟨source, sourceSatisfies⟩
    refine ⟨encodeAssignment contract source, ?_⟩
    rw [formulaToCNF_closedForm]
    apply (SAT.CNF.satisfies_append
      (initialCNF contract) (sourceFormulaCNF contract formula)
      (encodeAssignment contract source)).2
    constructor
    · apply (initialCNF_satisfies_iff contract
        (encodeAssignment contract source)).2
      exact Nat.ne_of_gt
        (Nat.zero_lt_of_lt (contract.valueCode_lt_domainSize (source 0)))
    · exact sourceFormulaCNF_satisfies_encode_of_formula_satisfies
        contract formula source sourceSatisfies

end ComplexityReduction.Domain.FiniteDomainCSPToStructuredCNFSemantics

