/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.BoolDispatch
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatPair
import ComplexityReduction.Legacy.ComplexityReduction.CSP.ToCNF
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.MaxCut.StructuredTM.Lookup
import ComplexityReduction.Domain.FiniteDomainCSPExecutableContract
import ComplexityReduction.Presentation.Satisfiability
import ComplexityReduction.Program.List

/-!
Direct structured program for the one-hot finite-domain CSP to CNF expansion.

The runtime input is only the existing faithful formula payload: a list of
relation selectors paired with variable scopes.  Domain values and relation
rows come from one caller-supplied `ExecutableLanguageContract`; they are fixed
when the program is assembled.  In particular, this leaf never attempts to
decide a proposition-valued source relation.

The propositional variable for source variable `variable` and numeric domain
value `value` is `Nat.pair variable value`.  Every scope occurrence contributes
the same exactly-one block, so repeated source variables merely duplicate
clauses.  A fixed relation symbol contributes one clause for every numeric row
not listed by its executable contract.

This file establishes only the program and its direct-TM polynomial-time
evidence.  Semantic correctness is intentionally left to a separate leaf.
-/

namespace ComplexityReduction
namespace Domain
namespace FiniteDomainCSPToStructuredCNFProgram

open ComplexityReduction
open Encoding
open FiniteDomainCSPExecutableContract

noncomputable section

/-- The exact generic finite-domain CSP endpoint accepted by the program. -/
abbrev sourceProblem {D : Type} (Γ : ComplexityReduction.CSP.FiniteDomain.Language D) :
    PresentedProblem :=
  Presentation.FiniteDomainCSP.presentedProblem Γ

/-- The canonical structured CNF-SAT endpoint. -/
abbrev targetProblem : PresentedProblem :=
  Presentation.Satisfiability.structuredProblem

/-- Canonical structural carrier of one generic CSP constraint code. -/
abbrev constraintCodeEncodedType : EncodedType :=
  Presentation.FiniteDomainCSP.constraintCodeEncodedType

/-- Canonical structural carrier of a generic CSP formula code. -/
abbrev formulaCodeEncodedType : EncodedType :=
  Presentation.FiniteDomainCSP.formulaCodeEncodedType

/-- Canonical structural carrier of a runtime variable scope. -/
abbrev variableListEncodedType : EncodedType :=
  EncodedType.list EncodedType.nat

/-- Canonical structured literal carrier used by the CNF target. -/
abbrev literalEncodedType : EncodedType :=
  ComplexityReduction.Karp21.literalStructuredEncodedType

/-- Canonical structured clause carrier used by the CNF target. -/
abbrev clauseEncodedType : EncodedType :=
  ComplexityReduction.Karp21.clauseStructuredEncodedType

/-- Canonical structured CNF carrier used by the target endpoint. -/
abbrev cnfEncodedType : EncodedType :=
  ComplexityReduction.Karp21.cnfStructuredEncodedType

/-! ### Fixed executable template data -/

/-- Enumerate all numeric rows of one fixed arity over `0, ..., domainSize - 1`. -/
def allRows (domainSize : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | arity + 1 =>
      (List.range domainSize).flatMap fun value =>
        (allRows domainSize arity).map fun row => value :: row

/-- Exact membership characterization for the fixed numeric row enumeration. -/
theorem mem_allRows_iff (domainSize arity : Nat) (row : List Nat) :
    row ∈ allRows domainSize arity ↔
      row.length = arity ∧ ∀ value, value ∈ row → value < domainSize := by
  induction arity generalizing row with
  | zero =>
      constructor
      · intro rowMem
        have rowEq : row = [] := by simpa [allRows] using rowMem
        subst row
        simp
      · rintro ⟨rowLength, _⟩
        have rowEq : row = [] := List.eq_nil_of_length_eq_zero rowLength
        subst row
        simp [allRows]
  | succ arity inductionHypothesis =>
      constructor
      · intro rowMem
        rcases List.mem_flatMap.mp rowMem with ⟨value, valueMem, rowMem⟩
        rcases List.mem_map.mp rowMem with ⟨tail, tailMem, rfl⟩
        have tailFacts := (inductionHypothesis tail).1 tailMem
        constructor
        · simp [tailFacts.1]
        · intro entry entryMem
          rcases List.mem_cons.mp entryMem with rfl | entryMem
          · exact List.mem_range.mp valueMem
          · exact tailFacts.2 entry entryMem
      · rintro ⟨rowLength, rowBound⟩
        cases row with
        | nil => simp at rowLength
        | cons value tail =>
            have valueBound : value < domainSize := rowBound value (by simp)
            have tailLength : tail.length = arity := by simpa using rowLength
            have tailBound : ∀ entry, entry ∈ tail → entry < domainSize := by
              intro entry entryMem
              exact rowBound entry (by simp [entryMem])
            exact List.mem_flatMap.mpr ⟨value, List.mem_range.mpr valueBound,
              List.mem_map.mpr
                ⟨tail, (inductionHypothesis tail).2 ⟨tailLength, tailBound⟩, rfl⟩⟩

/-- Numeric rows rejected by one exact executable relation table. -/
def falsifyingRows {D : Type} {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) (symbol : Γ.Symbol) : List (List Nat) :=
  (allRows contract.domainSize (Γ.relationOf symbol).arity).filter fun row =>
    decide (row ∉ contract.relationRows symbol)

/-- Exact membership characterization for one fixed rejected-row family. -/
theorem mem_falsifyingRows_iff {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) (symbol : Γ.Symbol) (row : List Nat) :
    row ∈ falsifyingRows contract symbol ↔
      row.length = (Γ.relationOf symbol).arity ∧
        (∀ value, value ∈ row → value < contract.domainSize) ∧
          row ∉ contract.relationRows symbol := by
  simp [falsifyingRows, mem_allRows_iff, and_assoc]

/-- Distinct ordered pairs of numeric domain values, used by at-most-one clauses. -/
def distinctValuePairs (domainSize : Nat) : List (Nat × Nat) :=
  ((List.range domainSize).product (List.range domainSize)).filter fun pair =>
    decide (pair.1 ≠ pair.2)

/-- Fixed literal rows describing exactly-one for one runtime source variable. -/
def exactlyOneRows (domainSize : Nat) : List (List (Nat × Bool)) :=
  ((List.range domainSize).map fun value => (value, false)) ::
    (distinctValuePairs domainSize).map fun pair =>
      [(pair.1, true), (pair.2, true)]

/-! ### Exactly-one blocks for runtime variables -/

/-- One one-hot literal for a runtime source variable and a fixed domain value. -/
def valueLiteral (value : Nat) (negated : Bool) (sourceVar : Nat) : SAT.Literal :=
  { var := Nat.pair sourceVar value, neg := negated }

/-- A fixed-value literal constructor has a checked direct TM. -/
theorem valueLiteral_tmPolyTime (value : Nat) (negated : Bool) :
    TMPolyTimeMap EncodedType.nat literalEncodedType (valueLiteral value negated) := by
  have hVariableCode := nat_pair_const_right_tm_polytime value
  have hNegated : TMPolyTimeMap EncodedType.nat EncodedType.bool
      (fun _ : Nat => negated) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool negated
  have hTuple :
      TMPolyTimeMap EncodedType.nat
        ComplexityReduction.Karp21.literalTupleStructuredEncodedType
        (fun sourceVar : Nat => (Nat.pair sourceVar value, negated)) :=
    TMPolyTimeMap.prod_mk hVariableCode hNegated
  have hLiteral := TMPolyTimeMap.comp
    ComplexityReduction.Karp21.literalTupleToLiteralTMBackedMap.tm_polytime hTuple
  simpa [Function.comp, valueLiteral, ComplexityReduction.Karp21.literalTupleToLiteral]
    using hLiteral

/-- Build a clause from a fixed list of `(value, polarity)` entries. -/
def fixedValueClause : List (Nat × Bool) → Nat → SAT.Clause
  | [], _ => []
  | entry :: entries, sourceVar =>
      valueLiteral entry.1 entry.2 sourceVar :: fixedValueClause entries sourceVar

/-- Every fixed one-hot clause has a checked direct TM. -/
theorem fixedValueClause_tmPolyTime (entries : List (Nat × Bool)) :
    TMPolyTimeMap EncodedType.nat clauseEncodedType (fixedValueClause entries) := by
  induction entries with
  | nil =>
      simpa [fixedValueClause, clauseEncodedType] using
        (TMPolyTimeMap.const EncodedType.nat clauseEncodedType ([] : SAT.Clause))
  | cons entry entries inductionHypothesis =>
      have hHead := valueLiteral_tmPolyTime entry.1 entry.2
      have hPair := TMPolyTimeMap.prod_mk hHead inductionHypothesis
      have hCons := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_cons literalEncodedType) hPair
      simpa [Function.comp, fixedValueClause, clauseEncodedType] using hCons

/-- Build a CNF from a fixed family of one-hot literal rows. -/
def variableCNFFromRows : List (List (Nat × Bool)) → Nat → SAT.CNF
  | [], _ => []
  | row :: rows, sourceVar =>
      fixedValueClause row sourceVar :: variableCNFFromRows rows sourceVar

/-- Every fixed family of one-hot clauses has a checked direct TM. -/
theorem variableCNFFromRows_tmPolyTime (rows : List (List (Nat × Bool))) :
    TMPolyTimeMap EncodedType.nat cnfEncodedType (variableCNFFromRows rows) := by
  induction rows with
  | nil =>
      simpa [variableCNFFromRows, cnfEncodedType] using
        (TMPolyTimeMap.const EncodedType.nat cnfEncodedType ([] : SAT.CNF))
  | cons row rows inductionHypothesis =>
      have hHead := fixedValueClause_tmPolyTime row
      have hPair := TMPolyTimeMap.prod_mk hHead inductionHypothesis
      have hCons := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_cons clauseEncodedType) hPair
      simpa [Function.comp, variableCNFFromRows, cnfEncodedType] using hCons

/-- Exactly-one CNF for one runtime source variable. -/
def exactlyOneCNF {D : Type} {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) (sourceVar : Nat) : SAT.CNF :=
  variableCNFFromRows (exactlyOneRows contract.domainSize) sourceVar

/-- The exactly-one block has a checked structured direct TM. -/
theorem exactlyOneCNF_tmPolyTime {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) :
    TMPolyTimeMap EncodedType.nat cnfEncodedType (exactlyOneCNF contract) := by
  simpa [exactlyOneCNF] using
    variableCNFFromRows_tmPolyTime (exactlyOneRows contract.domainSize)

/-- Add exactly-one blocks for every variable occurrence in a runtime scope. -/
def scopeExactlyOneCNF {D : Type} {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) (scope : List Nat) : SAT.CNF :=
  (scope.map (exactlyOneCNF contract)).flatten

/-- Runtime scope expansion is direct-TM polynomial-time. -/
theorem scopeExactlyOneCNF_tmPolyTime {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) :
    TMPolyTimeMap variableListEncodedType cnfEncodedType (scopeExactlyOneCNF contract) := by
  have hMap := TMPolyTimeMap.list_map (exactlyOneCNF_tmPolyTime contract)
  have hFlatten := Program.listFlatten_tmPolyTime clauseEncodedType
  have hComp := TMPolyTimeMap.comp hFlatten hMap
  simpa [Function.comp, scopeExactlyOneCNF, cnfEncodedType] using hComp

/-! ### Rejected relation rows over runtime scopes -/

/-- One negative one-hot literal at a fixed scope position and fixed domain value. -/
def scopedValueLiteral (index value : Nat) (scope : List Nat) : SAT.Literal :=
  { var := Nat.pair (scope.getD index 0) value, neg := true }

/-- A fixed-position, fixed-value scope literal has a checked direct TM. -/
theorem scopedValueLiteral_tmPolyTime (index value : Nat) :
    TMPolyTimeMap variableListEncodedType literalEncodedType
      (scopedValueLiteral index value) := by
  let X := variableListEncodedType
  have hIndex : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => index) :=
    TMPolyTimeMap.const X EncodedType.nat index
  have hLookupInput :
      TMPolyTimeMap X (EncodedType.prod X EncodedType.nat)
        (fun scope : X.Carrier => (scope, index)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id X) hIndex
  have hVariable := TMPolyTimeMap.comp
    ComplexityReduction.Karp21.MaxCut.natListGetD_tm_polytime hLookupInput
  have hVariableCode := TMPolyTimeMap.comp
    (nat_pair_const_right_tm_polytime value) hVariable
  have hNegated : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hTuple :
      TMPolyTimeMap X ComplexityReduction.Karp21.literalTupleStructuredEncodedType
        (fun scope : List Nat => (Nat.pair (scope.getD index 0) value, true)) :=
    TMPolyTimeMap.prod_mk hVariableCode hNegated
  have hLiteral := TMPolyTimeMap.comp
    ComplexityReduction.Karp21.literalTupleToLiteralTMBackedMap.tm_polytime hTuple
  simpa [X, Function.comp, scopedValueLiteral,
    ComplexityReduction.Karp21.literalTupleToLiteral] using hLiteral

/-- Clause excluding one fixed numeric row from a runtime variable scope. -/
def forbiddenRowClauseAux : Nat → List Nat → List Nat → SAT.Clause
  | _, [], _ => []
  | index, value :: values, scope =>
      scopedValueLiteral index value scope ::
        forbiddenRowClauseAux (index + 1) values scope

/-- Clause excluding one fixed numeric row, starting at scope position zero. -/
def forbiddenRowClause (row : List Nat) (scope : List Nat) : SAT.Clause :=
  forbiddenRowClauseAux 0 row scope

/-- Every fixed rejected-row clause has a checked direct TM. -/
theorem forbiddenRowClauseAux_tmPolyTime (index : Nat) (row : List Nat) :
    TMPolyTimeMap variableListEncodedType clauseEncodedType
      (forbiddenRowClauseAux index row) := by
  induction row generalizing index with
  | nil =>
      simpa [forbiddenRowClauseAux, clauseEncodedType] using
        (TMPolyTimeMap.const variableListEncodedType clauseEncodedType ([] : SAT.Clause))
  | cons value values inductionHypothesis =>
      have hHead := scopedValueLiteral_tmPolyTime index value
      have hTail := inductionHypothesis (index + 1)
      have hPair := TMPolyTimeMap.prod_mk hHead hTail
      have hCons := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_cons literalEncodedType) hPair
      simpa [Function.comp, forbiddenRowClauseAux, clauseEncodedType] using hCons

/-- Direct-TM evidence for one fixed rejected numeric row. -/
theorem forbiddenRowClause_tmPolyTime (row : List Nat) :
    TMPolyTimeMap variableListEncodedType clauseEncodedType
      (forbiddenRowClause row) := by
  simpa [forbiddenRowClause] using forbiddenRowClauseAux_tmPolyTime 0 row

@[simp]
theorem forbiddenRowClauseAux_length (index : Nat) (row scope : List Nat) :
    (forbiddenRowClauseAux index row scope).length = row.length := by
  induction row generalizing index with
  | nil => rfl
  | cons value values inductionHypothesis =>
      simp [forbiddenRowClauseAux, inductionHypothesis]

/-- Exact literal read by the rejected-row constructor at one valid row position. -/
theorem forbiddenRowClauseAux_getElem (offset : Nat) (row scope : List Nat)
    (index : Nat) (indexBound : index < row.length) :
    (forbiddenRowClauseAux offset row scope)[index]'(by
      simpa [forbiddenRowClauseAux_length] using indexBound) =
      { var := Nat.pair (scope.getD (offset + index) 0) row[index], neg := true } := by
  induction row generalizing offset index with
  | nil => simp at indexBound
  | cons value values inductionHypothesis =>
      cases index with
      | zero =>
          simp [forbiddenRowClauseAux, scopedValueLiteral]
      | succ index =>
          have tailBound : index < values.length := by simpa using indexBound
          simp only [forbiddenRowClauseAux, List.getElem_cons_succ]
          have offsetEq : offset + 1 + index = offset + (index + 1) := by omega
          simpa only [offsetEq] using
            inductionHypothesis (offset := offset + 1) (index := index) tailBound

/-- On an arity-correct row and scope, every fallback lookup is unreachable. -/
theorem forbiddenRowClause_eq_ofFn {arity : Nat} (scope : Fin arity → Nat)
    (row : List Nat) (rowLength : row.length = arity) :
    forbiddenRowClause row (List.ofFn scope) =
      List.ofFn fun index =>
        { var := Nat.pair (scope index) (row.getD index.val 0), neg := true } := by
  unfold forbiddenRowClause
  apply List.ext_getElem
  · simp [rowLength]
  · intro index leftBound rightBound
    have rowBound : index < row.length := by simpa [rowLength] using rightBound
    rw [forbiddenRowClauseAux_getElem (indexBound := rowBound)]
    have arityBound : index < arity := by simpa using rightBound
    simp [List.getD, arityBound, rowBound]

/-- Expand a fixed family of rejected numeric rows over a runtime scope. -/
def relationCNFFromRows (rows : List (List Nat)) (scope : List Nat) : SAT.CNF :=
  rows.map fun row => forbiddenRowClause row scope

/-- A fixed family of rejected rows expands by a checked direct TM. -/
theorem relationCNFFromRows_tmPolyTime (rows : List (List Nat)) :
    TMPolyTimeMap variableListEncodedType cnfEncodedType
      (relationCNFFromRows rows) := by
  induction rows with
  | nil =>
      simpa [relationCNFFromRows, cnfEncodedType] using
        (TMPolyTimeMap.const variableListEncodedType cnfEncodedType ([] : SAT.CNF))
  | cons row rows inductionHypothesis =>
      have hHead := forbiddenRowClause_tmPolyTime row
      have hPair := TMPolyTimeMap.prod_mk hHead inductionHypothesis
      have hCons := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_cons clauseEncodedType) hPair
      simpa [Function.comp, relationCNFFromRows, cnfEncodedType] using hCons

/-- Rejected-row block for one exact executable relation symbol. -/
def symbolRelationCNF {D : Type} {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) (symbol : Γ.Symbol)
    (scope : List Nat) : SAT.CNF :=
  relationCNFFromRows (falsifyingRows contract symbol) scope

/-- Every fixed relation-symbol block has a checked direct TM. -/
theorem symbolRelationCNF_tmPolyTime {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) (symbol : Γ.Symbol) :
    TMPolyTimeMap variableListEncodedType cnfEncodedType
      (symbolRelationCNF contract symbol) := by
  simpa [symbolRelationCNF] using
    relationCNFFromRows_tmPolyTime (falsifyingRows contract symbol)

/-! ### Selector dispatch and one-constraint assembly -/

/-- Dispatch a runtime relation selector through a fixed symbol enumeration. -/
def relationCNFDispatch {D : Type} {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) :
    List Γ.Symbol → (Nat × List Nat) → SAT.CNF
  | [], _ => []
  | symbol :: symbols, input =>
      if decide (input.1 = Presentation.FiniteDomainCSP.relationCode Γ symbol) then
        symbolRelationCNF contract symbol input.2
      else
        relationCNFDispatch contract symbols input

/-- The fixed finite selector dispatch has a checked direct TM. -/
theorem relationCNFDispatch_tmPolyTime {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) (symbols : List Γ.Symbol) :
    TMPolyTimeMap constraintCodeEncodedType cnfEncodedType
      (relationCNFDispatch contract symbols) := by
  induction symbols with
  | nil =>
      simpa [relationCNFDispatch] using
        (TMPolyTimeMap.const constraintCodeEncodedType cnfEncodedType ([] : SAT.CNF))
  | cons symbol symbols inductionHypothesis =>
      let X := constraintCodeEncodedType
      have hCode : TMPolyTimeMap X EncodedType.nat
          (fun input : X.Carrier => input.1) := by
        simpa [X, constraintCodeEncodedType] using
          (TMPolyTimeMap.fst EncodedType.nat variableListEncodedType)
      have hExpected : TMPolyTimeMap X EncodedType.nat
          (fun _ : X.Carrier => Presentation.FiniteDomainCSP.relationCode Γ symbol) :=
        TMPolyTimeMap.const X EncodedType.nat
          (Presentation.FiniteDomainCSP.relationCode Γ symbol)
      have hEqInput :
          TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
            (fun input : X.Carrier =>
              (input.1, Presentation.FiniteDomainCSP.relationCode Γ symbol)) :=
        TMPolyTimeMap.prod_mk hCode hExpected
      have hEq := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hEqInput
      have hScope : TMPolyTimeMap X variableListEncodedType
          (fun input : X.Carrier => input.2) := by
        simpa [X, constraintCodeEncodedType] using
          (TMPolyTimeMap.snd EncodedType.nat variableListEncodedType)
      have hHit := TMPolyTimeMap.comp
        (symbolRelationCNF_tmPolyTime contract symbol) hScope
      have hBranchInput :
          TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
            (fun input : Nat × List Nat =>
              (decide
                (input.1 = Presentation.FiniteDomainCSP.relationCode Γ symbol), input)) :=
        TMPolyTimeMap.prod_mk hEq (TMPolyTimeMap.id X)
      have hBranch := boolProduct_dispatch_tm_polytime X cnfEncodedType
        inductionHypothesis hHit
      have hOut := TMPolyTimeMap.comp hBranch hBranchInput
      convert hOut using 1
      funext input
      by_cases hCodeEq :
          input.1 = Presentation.FiniteDomainCSP.relationCode Γ symbol <;>
        simp [Function.comp, relationCNFDispatch, hCodeEq]

/-- Complete fixed symbol enumeration for the exact source language. -/
def languageSymbols {D : Type} (Γ : ComplexityReduction.CSP.FiniteDomain.Language D) :
    List Γ.Symbol :=
  Finset.univ.toList

/-- A faithful selector always reaches its exact fixed relation block. -/
theorem relationCNFDispatch_eq_symbolRelationCNF_of_mem {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) (symbols : List Γ.Symbol)
    (symbol : Γ.Symbol) (symbolMem : symbol ∈ symbols) (scope : List Nat) :
    relationCNFDispatch contract symbols
        (Presentation.FiniteDomainCSP.relationCode Γ symbol, scope) =
      symbolRelationCNF contract symbol scope := by
  induction symbols with
  | nil => simp at symbolMem
  | cons head tail inductionHypothesis =>
      by_cases headEq : symbol = head
      · subst head
        simp [relationCNFDispatch]
      · have tailMem : symbol ∈ tail :=
          (List.mem_cons.mp symbolMem).resolve_left headEq
        have codeNe :
            Presentation.FiniteDomainCSP.relationCode Γ symbol ≠
              Presentation.FiniteDomainCSP.relationCode Γ head := by
          intro codeEq
          have symbolEq := Presentation.FiniteDomainCSP.relationCode_injective Γ codeEq
          exact headEq symbolEq
        simp [relationCNFDispatch, codeNe, inductionHypothesis tailMem]

/-- Typed one-constraint expansion exposed independently of its numeric selector. -/
def sourceConstraintCNF {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ)
    (constraint : ComplexityReduction.CSP.FiniteDomain.Constraint Γ) : SAT.CNF :=
  scopeExactlyOneCNF contract constraint.varsList ++
    symbolRelationCNF contract constraint.symbol constraint.varsList

/-- CNF block for one runtime selector/scope pair. -/
def constraintCodeToCNF {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ)
    (input : constraintCodeEncodedType.Carrier) : SAT.CNF :=
  scopeExactlyOneCNF contract input.2 ++
    relationCNFDispatch contract (languageSymbols Γ) input

/-- One generic CSP constraint code expands by a checked structured direct TM. -/
theorem constraintCodeToCNF_tmPolyTime {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) :
    TMPolyTimeMap constraintCodeEncodedType cnfEncodedType
      (constraintCodeToCNF contract) := by
  let X := constraintCodeEncodedType
  have hScope : TMPolyTimeMap X variableListEncodedType
      (fun input : X.Carrier => input.2) := by
    simpa [X, constraintCodeEncodedType] using
      (TMPolyTimeMap.snd EncodedType.nat variableListEncodedType)
  have hExactlyOne := TMPolyTimeMap.comp
    (scopeExactlyOneCNF_tmPolyTime contract) hScope
  have hRelation := relationCNFDispatch_tmPolyTime contract (languageSymbols Γ)
  have hAppendInput := TMPolyTimeMap.prod_mk hExactlyOne hRelation
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseEncodedType) hAppendInput
  simpa [X, Function.comp, constraintCodeToCNF, cnfEncodedType] using hAppend

/-- Faithful numeric constraint payloads expand to their exact typed block. -/
theorem constraintCodeToCNF_eq_sourceConstraintCNF {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ)
    (constraint : ComplexityReduction.CSP.FiniteDomain.Constraint Γ) :
    constraintCodeToCNF contract
        (Presentation.FiniteDomainCSP.constraintCode constraint) =
      sourceConstraintCNF contract constraint := by
  change
    scopeExactlyOneCNF contract constraint.varsList ++
        relationCNFDispatch contract (languageSymbols Γ)
          (Presentation.FiniteDomainCSP.relationCode Γ constraint.symbol,
            constraint.varsList) =
      scopeExactlyOneCNF contract constraint.varsList ++
        symbolRelationCNF contract constraint.symbol constraint.varsList
  rw [relationCNFDispatch_eq_symbolRelationCNF_of_mem contract (languageSymbols Γ)
    constraint.symbol (by simp [languageSymbols]) constraint.varsList]

/-- Faithful-code equation stated without the typed-block abbreviation. -/
theorem constraintCodeToCNF_constraintCode {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ)
    (constraint : ComplexityReduction.CSP.FiniteDomain.Constraint Γ) :
    constraintCodeToCNF contract
        (Presentation.FiniteDomainCSP.constraintCode constraint) =
      scopeExactlyOneCNF contract constraint.varsList ++
        symbolRelationCNF contract constraint.symbol constraint.varsList := by
  simpa [sourceConstraintCNF] using
    constraintCodeToCNF_eq_sourceConstraintCNF contract constraint

/-! ### Formula fold and exact presentation wrapper -/

/-- Empty-domain guard: no total assignment exists when the domain has no value. -/
def initialCNF {D : Type} {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) : SAT.CNF :=
  if contract.domainSize = 0 then [[]] else []

/-- Append one translated constraint block to the formula accumulator. -/
def appendConstraintCNFStep {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ)
    (input : SAT.CNF × constraintCodeEncodedType.Carrier) : SAT.CNF :=
  input.1 ++ constraintCodeToCNF contract input.2

/-- The accumulator step has a checked structured direct TM. -/
theorem appendConstraintCNFStep_tmPolyTime {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) :
    TMPolyTimeMap (EncodedType.prod cnfEncodedType constraintCodeEncodedType)
      cnfEncodedType (appendConstraintCNFStep contract) := by
  let X := EncodedType.prod cnfEncodedType constraintCodeEncodedType
  have hAccumulator : TMPolyTimeMap X cnfEncodedType
      (fun input : X.Carrier => input.1) := by
    simpa [X] using TMPolyTimeMap.fst cnfEncodedType constraintCodeEncodedType
  have hConstraint : TMPolyTimeMap X constraintCodeEncodedType
      (fun input : X.Carrier => input.2) := by
    simpa [X] using TMPolyTimeMap.snd cnfEncodedType constraintCodeEncodedType
  have hBlock := TMPolyTimeMap.comp
    (constraintCodeToCNF_tmPolyTime contract) hConstraint
  have hAppendInput := TMPolyTimeMap.prod_mk hAccumulator hBlock
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseEncodedType) hAppendInput
  simpa [X, Function.comp, appendConstraintCNFStep, cnfEncodedType] using hAppend

private theorem encodedList_inputSize_append (element : EncodedType)
    (left right : List element.Carrier) :
    (EncodedType.list element).inputSize (left ++ right) =
      (EncodedType.list element).inputSize left +
        (EncodedType.list element).inputSize right := by
  induction left with
  | nil => simp
  | cons item left inductionHypothesis =>
      simp [inductionHypothesis, Nat.add_assoc]

/-- Structured CNF input size is additive under append. -/
theorem cnfEncodedType_inputSize_append (left right : SAT.CNF) :
    cnfEncodedType.inputSize (left ++ right) =
      cnfEncodedType.inputSize left + cnfEncodedType.inputSize right := by
  simpa [cnfEncodedType, ComplexityReduction.Karp21.cnfStructuredEncodedType] using
    encodedList_inputSize_append ComplexityReduction.Karp21.clauseStructuredEncodedType
      left right

/-- Fold all runtime constraint codes into one structured CNF. -/
def formulaCodeToCNF {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ)
    (formula : formulaCodeEncodedType.Carrier) : SAT.CNF :=
  formula.foldl
    (fun accumulator constraint =>
      appendConstraintCNFStep contract (accumulator, constraint))
    (initialCNF contract)

/-- Typed formula expansion exposed independently of its faithful numeric payload. -/
def sourceFormulaCNF {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ)
    (formula : ComplexityReduction.CSP.FiniteDomain.Formula Γ) : SAT.CNF :=
  formula.flatMap (sourceConstraintCNF contract)

/-- Exact fold expansion for a faithful source formula payload and any accumulator. -/
theorem formulaCode_fold_correct {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ)
    (formula : ComplexityReduction.CSP.FiniteDomain.Formula Γ)
    (accumulator : SAT.CNF) :
    (Presentation.FiniteDomainCSP.formulaCode Γ formula).foldl
        (fun current constraint =>
          appendConstraintCNFStep contract (current, constraint)) accumulator =
      accumulator ++ sourceFormulaCNF contract formula := by
  induction formula generalizing accumulator with
  | nil =>
      rw [show Presentation.FiniteDomainCSP.formulaCode Γ
          ([] : ComplexityReduction.CSP.FiniteDomain.Formula Γ) = [] by rfl]
      change accumulator = accumulator ++ sourceFormulaCNF contract []
      simp [sourceFormulaCNF]
  | cons constraint formula inductionHypothesis =>
      simp only [Presentation.FiniteDomainCSP.formulaCode, List.map_cons]
      change
        (Presentation.FiniteDomainCSP.formulaCode Γ formula).foldl
            (fun current code => appendConstraintCNFStep contract (current, code))
            (appendConstraintCNFStep contract
              (accumulator, Presentation.FiniteDomainCSP.constraintCode constraint)) =
          accumulator ++ sourceFormulaCNF contract (constraint :: formula)
      rw [inductionHypothesis]
      simp [appendConstraintCNFStep, constraintCodeToCNF_eq_sourceConstraintCNF,
        sourceFormulaCNF, List.append_assoc]

/-- Closed form of the formula-code transducer on a faithful source payload. -/
theorem formulaCodeToCNF_closedForm {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ)
    (formula : ComplexityReduction.CSP.FiniteDomain.Formula Γ) :
    formulaCodeToCNF contract
        (Presentation.FiniteDomainCSP.formulaCode Γ formula) =
      initialCNF contract ++ sourceFormulaCNF contract formula := by
  simpa [formulaCodeToCNF] using
    formulaCode_fold_correct contract formula (initialCNF contract)

/-- The full formula-code fold is direct-TM polynomial-time. -/
theorem formulaCodeToCNF_tmPolyTime {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) :
    TMPolyTimeMap formulaCodeEncodedType cnfEncodedType
      (formulaCodeToCNF contract) := by
  have hBlockTM := constraintCodeToCNF_tmPolyTime contract
  rcases hBlockTM.outputSizeBound with
    ⟨degree, coefficient, offset, hBlockSize⟩
  let base : Polynomial Nat :=
    Polynomial.C (cnfEncodedType.inputSize (initialCNF contract))
  let grow : Polynomial Nat :=
    Polynomial.C coefficient * Polynomial.X ^ degree + Polynomial.C offset
  rcases appendConstraintCNFStep_tmPolyTime contract with ⟨hStep⟩
  refine TMPolyTimeMap.list_foldl_typed_growth_bounded
    constraintCodeEncodedType cnfEncodedType (appendConstraintCNFStep contract)
    (initialCNF contract) hStep base grow ?_ ?_
  · intro source
    simp [base]
  · intro source accumulator constraint hConstraintSize
    have hMono : constraintCodeEncodedType.inputSize constraint ^ degree ≤
        formulaCodeEncodedType.inputSize source ^ degree :=
      Nat.pow_le_pow_left hConstraintSize degree
    have hBlock := hBlockSize constraint
    rw [appendConstraintCNFStep, cnfEncodedType_inputSize_append]
    have hBound :
        cnfEncodedType.inputSize (constraintCodeToCNF contract constraint) ≤
          coefficient * formulaCodeEncodedType.inputSize source ^ degree + offset :=
      hBlock.trans
        (Nat.add_le_add_right (Nat.mul_le_mul_left coefficient hMono) offset)
    simpa [grow, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X] using
      Nat.add_le_add_left hBound (cnfEncodedType.inputSize accumulator)

/-- Expose the faithful generic CSP formula as its existing selector/scope payload. -/
def formulaCodeMap {D : Type} (Γ : ComplexityReduction.CSP.FiniteDomain.Language D)
    (formula : (Presentation.FiniteDomainCSP.lawfulRepresentation Γ).Carrier) :
    formulaCodeEncodedType.Carrier :=
  Presentation.FiniteDomainCSP.formulaCode Γ formula

/-- Reading the existing faithful formula payload is encoding-preserving. -/
theorem formulaCodeMap_tmPolyTime {D : Type}
    (Γ : ComplexityReduction.CSP.FiniteDomain.Language D) :
    TMPolyTimeMap
      (Presentation.FiniteDomainCSP.lawfulRepresentation Γ).encodedType
      formulaCodeEncodedType (formulaCodeMap Γ) :=
  (TMBackedCostedMap.ofEncodingEquiv
    (Presentation.FiniteDomainCSP.lawfulRepresentation Γ).encodedType
    formulaCodeEncodedType (formulaCodeMap Γ) (Equiv.refl _)
    (by
      intro formula
      change formulaCodeEncodedType.encode
          (Presentation.FiniteDomainCSP.formulaCode Γ formula) =
        (formulaCodeEncodedType.encode
          (Presentation.FiniteDomainCSP.formulaCode Γ formula)).map id
      rw [List.map_id])).tm_polytime

/-- Exact-presentation wrapper around the formula-code transducer. -/
def formulaToCNF {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ)
    (formula : (sourceProblem Γ).Instance) : SAT.CNF :=
  formulaCodeToCNF contract (formulaCodeMap Γ formula)

/-- Direct-TM evidence at the exact generic CSP and structured CNF codecs. -/
theorem formulaToCNF_tmPolyTime {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) :
    TMPolyTimeMap (sourceProblem Γ).representation.encodedType cnfEncodedType
      (formulaToCNF contract) := by
  have hComp := TMPolyTimeMap.comp
    (formulaCodeToCNF_tmPolyTime contract) (formulaCodeMap_tmPolyTime Γ)
  simpa [Function.comp, formulaToCNF] using hComp

/-- Closed form of the exact-presentation transducer on every source formula. -/
theorem formulaToCNF_closedForm {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ)
    (formula : (sourceProblem Γ).Instance) :
    formulaToCNF contract formula =
      initialCNF contract ++ sourceFormulaCNF contract formula := by
  simpa [formulaToCNF, formulaCodeMap] using
    formulaCodeToCNF_closedForm contract formula

/-- Exact direct-TM primitive for generic finite-domain CSP to structured CNF. -/
def formulaToCNFPrimitive {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) :
    Program.Primitive (sourceProblem Γ).representation targetProblem.representation :=
  Program.Primitive.ofTMPolyTime (formulaToCNF contract)
    (formulaToCNF_tmPolyTime contract)

/-- The executable one-hot expansion contains exactly its checked direct-TM atom. -/
def formulaToCNFProgram {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) :
    Program.PolyProg (sourceProblem Γ).representation targetProblem.representation :=
  .atom (formulaToCNFPrimitive contract)

@[simp]
theorem formulaToCNFProgram_run {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) (formula : (sourceProblem Γ).Instance) :
    (formulaToCNFProgram contract).run formula = formulaToCNF contract formula :=
  rfl

end
end FiniteDomainCSPToStructuredCNFProgram
end Domain
end ComplexityReduction
