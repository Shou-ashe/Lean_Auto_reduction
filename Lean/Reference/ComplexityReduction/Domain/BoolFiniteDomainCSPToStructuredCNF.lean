/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.BoolDispatch
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.TMComplexityTransport
import ComplexityReduction.Legacy.ComplexityReduction.CSP.ToCNF
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.MaxCut.StructuredTM.Lookup
import ComplexityReduction.Domain.BoolTableCSPToFiniteDomainAdapter
import ComplexityReduction.Presentation.Satisfiability

/-!
Exact-endpoint construction from the Boolean finite-domain CSP hub to the
canonical structured CNF-SAT hub.

The generic finite-domain endpoint used here is not an arbitrary
`FiniteDomain.Language`: it is precisely the `BoolBridge` view induced by one
finite Boolean table language.  Consequently its constraints can be returned
to the original Boolean CSP syntax without inspecting a proposition-valued
relation.  This first, encoding-preserving adapter is also useful independently
of the CNF expansion below.
-/

namespace ComplexityReduction
namespace Domain
namespace BoolFiniteDomainCSPToStructuredCNF

open Certificate Encoding

noncomputable section

/-- The exact finite Boolean table-language parameter accepted by this gadget. -/
abbrev TableLanguage : Type 1 :=
  Presentation.FiniteDomainCSPTable.TableLanguage

/-- The exact canonical Boolean finite-domain CSP hub. -/
abbrev sourceProblem (Γ : TableLanguage) : PresentedProblem :=
  BoolTableCSPToFiniteDomainAdapter.hubProblem Γ

/-- The exact canonical structured CNF-SAT hub. -/
abbrev targetProblem : PresentedProblem :=
  Presentation.Satisfiability.structuredProblem

/-- Return one `BoolBridge` finite-domain constraint to the original Boolean syntax. -/
def constraintToBool (Γ : TableLanguage)
    (constraint : ComplexityReduction.CSP.FiniteDomain.Constraint
      (ComplexityReduction.CSP.FiniteDomain.BoolBridge.languageOfBoolLanguage Γ)) :
    ComplexityReduction.CSP.Constraint Γ where
  symbol := constraint.symbol
  vars := constraint.vars

/-- Return a `BoolBridge` finite-domain formula to the original Boolean syntax. -/
def formulaToBool (Γ : TableLanguage)
    (formula : (sourceProblem Γ).Instance) : ComplexityReduction.CSP.Formula Γ :=
  formula.map (constraintToBool Γ)

@[simp]
theorem constraintToBool_constraintOfBoolConstraint (Γ : TableLanguage)
    (constraint : ComplexityReduction.CSP.Constraint Γ) :
    constraintToBool Γ
      (ComplexityReduction.CSP.FiniteDomain.BoolBridge.constraintOfBoolConstraint constraint) =
        constraint := by
  cases constraint
  rfl

@[simp]
theorem constraintOfBoolConstraint_constraintToBool (Γ : TableLanguage)
    (constraint : ComplexityReduction.CSP.FiniteDomain.Constraint
      (ComplexityReduction.CSP.FiniteDomain.BoolBridge.languageOfBoolLanguage Γ)) :
    ComplexityReduction.CSP.FiniteDomain.BoolBridge.constraintOfBoolConstraint
      (constraintToBool Γ constraint) = constraint := by
  cases constraint
  rfl

@[simp]
theorem formulaToBool_formulaOfBoolFormula (Γ : TableLanguage)
    (formula : ComplexityReduction.CSP.Formula Γ) :
    formulaToBool Γ
      (ComplexityReduction.CSP.FiniteDomain.BoolBridge.formulaOfBoolFormula formula) = formula := by
  change List.map (constraintToBool Γ)
      (List.map ComplexityReduction.CSP.FiniteDomain.BoolBridge.constraintOfBoolConstraint
        formula) = formula
  rw [List.map_map]
  have hFunction :
      constraintToBool Γ ∘
          ComplexityReduction.CSP.FiniteDomain.BoolBridge.constraintOfBoolConstraint = id := by
    funext constraint
    exact constraintToBool_constraintOfBoolConstraint Γ constraint
  rw [hFunction, List.map_id]

@[simp]
theorem formulaOfBoolFormula_formulaToBool (Γ : TableLanguage)
    (formula : (sourceProblem Γ).Instance) :
    ComplexityReduction.CSP.FiniteDomain.BoolBridge.formulaOfBoolFormula
      (formulaToBool Γ formula) = formula := by
  change List.map ComplexityReduction.CSP.FiniteDomain.BoolBridge.constraintOfBoolConstraint
      (List.map (constraintToBool Γ) formula) = formula
  rw [List.map_map]
  have hFunction :
      ComplexityReduction.CSP.FiniteDomain.BoolBridge.constraintOfBoolConstraint ∘
          constraintToBool Γ = id := by
    funext constraint
    exact constraintOfBoolConstraint_constraintToBool Γ constraint
  rw [hFunction, List.map_id]

private theorem formulaToBool_encode (Γ : TableLanguage)
    (formula : (sourceProblem Γ).Instance) :
    Presentation.FiniteDomainCSPTable.formulaCodeEncodedType.encode
        (Presentation.FiniteDomainCSPTable.formulaCode Γ (formulaToBool Γ formula)) =
      (Presentation.FiniteDomainCSP.formulaCodeEncodedType.encode
        (Presentation.FiniteDomainCSP.formulaCode
          (ComplexityReduction.CSP.FiniteDomain.BoolBridge.languageOfBoolLanguage Γ)
          formula)).map id := by
  rw [List.map_id]
  congr 1
  simp only [formulaToBool, Presentation.FiniteDomainCSPTable.formulaCode,
    Presentation.FiniteDomainCSP.formulaCode, List.map_map]
  apply List.map_congr_left
  intro constraint _
  rfl

/--
The reverse Bool-bridge syntax adapter is a direct TM at the two exact V2
formula codecs.  Its machine is the identity on their common formula-code
word; no legacy raw encoder is involved.
-/
theorem formulaToBool_tmPolyTime (Γ : TableLanguage) :
    ComplexityReduction.TMPolyTimeMap
      (sourceProblem Γ).representation.encodedType
      (Presentation.FiniteDomainCSPTable.lawfulRepresentation Γ).encodedType
      (formulaToBool Γ) :=
  (ComplexityReduction.TMBackedCostedMap.ofEncodingEquiv
    (sourceProblem Γ).representation.encodedType
    (Presentation.FiniteDomainCSPTable.lawfulRepresentation Γ).encodedType
    (formulaToBool Γ) (Equiv.refl _)
    (by
      intro formula
      exact formulaToBool_encode Γ formula)).tm_polytime

/-- The exact reverse adapter primitive, independently reusable by later gadgets. -/
noncomputable def formulaToBoolPrimitive (Γ : TableLanguage) :
    Program.Primitive (sourceProblem Γ).representation
      (Presentation.FiniteDomainCSPTable.lawfulRepresentation Γ) :=
  Program.Primitive.ofTMPolyTime (formulaToBool Γ) (formulaToBool_tmPolyTime Γ)

/-- The exact reverse adapter program contains only its direct-TM-backed atom. -/
noncomputable def formulaToBoolProgram (Γ : TableLanguage) :
    Program.PolyProg (sourceProblem Γ).representation
      (Presentation.FiniteDomainCSPTable.lawfulRepresentation Γ) :=
  .atom (formulaToBoolPrimitive Γ)

@[simp]
theorem formulaToBoolProgram_run (Γ : TableLanguage)
    (formula : (sourceProblem Γ).Instance) :
    (formulaToBoolProgram Γ).run formula = formulaToBool Γ formula :=
  rfl

/-- The reverse adapter preserves satisfiability exactly. -/
theorem formulaToBool_satisfiable_iff (Γ : TableLanguage)
    (formula : (sourceProblem Γ).Instance) :
    ComplexityReduction.CSP.Formula.Satisfiable (formulaToBool Γ formula) ↔
      ComplexityReduction.CSP.FiniteDomain.Formula.Satisfiable formula := by
  have h :=
    ComplexityReduction.CSP.FiniteDomain.BoolBridge.formulaOfBoolFormula_satisfiable_iff
      (formulaToBool Γ formula)
  simpa using h.symm

/-! ### Exact structured direct-TM CNF expansion -/

open ComplexityReduction

/-- Canonical structural carrier of one V2 CSP constraint code. -/
abbrev constraintCodeEncodedType : ComplexityReduction.EncodedType :=
  Presentation.FiniteDomainCSPTable.constraintCodeEncodedType

/-- Canonical structural carrier of a list of CSP constraint codes. -/
abbrev formulaCodeEncodedType : ComplexityReduction.EncodedType :=
  Presentation.FiniteDomainCSPTable.formulaCodeEncodedType

/-- Canonical structured variable-list carrier. -/
abbrev variableListEncodedType : ComplexityReduction.EncodedType :=
  ComplexityReduction.EncodedType.list ComplexityReduction.EncodedType.nat

/-- Canonical structured literal carrier used by the target CNF endpoint. -/
abbrev literalEncodedType : ComplexityReduction.EncodedType :=
  ComplexityReduction.Karp21.literalStructuredEncodedType

/-- Canonical structured clause carrier used by the target CNF endpoint. -/
abbrev clauseEncodedType : ComplexityReduction.EncodedType :=
  ComplexityReduction.Karp21.clauseStructuredEncodedType

/-- Canonical structured CNF carrier used by the target endpoint. -/
abbrev cnfEncodedType : ComplexityReduction.EncodedType :=
  ComplexityReduction.Karp21.cnfStructuredEncodedType

/-- Read one fixed scope position and attach one fixed literal polarity. -/
def literalAt (index : Nat) (negated : Bool) (scope : List Nat) :
    ComplexityReduction.SAT.Literal :=
  { var := scope.getD index (0 : Nat), neg := negated }

/-- Direct-TM evidence for one fixed-position literal constructor. -/
theorem literalAt_tmPolyTime (index : Nat) (negated : Bool) :
    ComplexityReduction.TMPolyTimeMap variableListEncodedType literalEncodedType
      (literalAt index negated) := by
  let X := variableListEncodedType
  have hIndex : ComplexityReduction.TMPolyTimeMap X ComplexityReduction.EncodedType.nat
      (fun _ : X.Carrier => index) :=
    ComplexityReduction.TMPolyTimeMap.const X ComplexityReduction.EncodedType.nat index
  have hLookupInput :
      ComplexityReduction.TMPolyTimeMap X
        (ComplexityReduction.EncodedType.prod X ComplexityReduction.EncodedType.nat)
        (fun scope : X.Carrier => (scope, index)) :=
    ComplexityReduction.TMPolyTimeMap.prod_mk (ComplexityReduction.TMPolyTimeMap.id X) hIndex
  have hVariable := ComplexityReduction.TMPolyTimeMap.comp
    ComplexityReduction.Karp21.MaxCut.natListGetD_tm_polytime hLookupInput
  have hNegated : ComplexityReduction.TMPolyTimeMap X ComplexityReduction.EncodedType.bool
      (fun _ : X.Carrier => negated) :=
    ComplexityReduction.TMPolyTimeMap.const X ComplexityReduction.EncodedType.bool negated
  have hTuple :
      ComplexityReduction.TMPolyTimeMap X
        ComplexityReduction.Karp21.literalTupleStructuredEncodedType
        (fun scope : List Nat => (scope.getD index (0 : Nat), negated)) :=
    ComplexityReduction.TMPolyTimeMap.prod_mk hVariable hNegated
  have hLiteral := ComplexityReduction.TMPolyTimeMap.comp
    ComplexityReduction.Karp21.literalTupleToLiteralTMBackedMap.tm_polytime hTuple
  simpa [X, Function.comp, literalAt, ComplexityReduction.Karp21.literalTupleToLiteral]
    using hLiteral

/-- Build a clause from a fixed polarity row and a runtime variable scope. -/
def clauseFromSignsAux : Nat → List Bool → List Nat → ComplexityReduction.SAT.Clause
  | _, [], _ => []
  | offset, negated :: signs, scope =>
      literalAt offset negated scope :: clauseFromSignsAux (offset + 1) signs scope

/-- Build a clause from a fixed polarity row, starting at scope position zero. -/
def clauseFromSigns (signs : List Bool) (scope : List Nat) :
    ComplexityReduction.SAT.Clause :=
  clauseFromSignsAux 0 signs scope

/-- Each fixed-polarity clause constructor has a checked structured direct TM. -/
theorem clauseFromSignsAux_tmPolyTime (offset : Nat) (signs : List Bool) :
    ComplexityReduction.TMPolyTimeMap variableListEncodedType clauseEncodedType
      (clauseFromSignsAux offset signs) := by
  induction signs generalizing offset with
  | nil =>
      simpa [clauseFromSignsAux, clauseEncodedType] using
        (ComplexityReduction.TMPolyTimeMap.const variableListEncodedType clauseEncodedType
          ([] : ComplexityReduction.SAT.Clause))
  | cons negated signs ih =>
      have hHead := literalAt_tmPolyTime offset negated
      have hTail := ih (offset + 1)
      have hPair := ComplexityReduction.TMPolyTimeMap.prod_mk hHead hTail
      have hCons := ComplexityReduction.TMPolyTimeMap.comp
        (ComplexityReduction.TMPolyTimeMap.list_cons literalEncodedType) hPair
      simpa [Function.comp, clauseFromSignsAux, clauseEncodedType] using hCons

/-- Direct-TM evidence for a fixed-polarity clause constructor. -/
theorem clauseFromSigns_tmPolyTime (signs : List Bool) :
    ComplexityReduction.TMPolyTimeMap variableListEncodedType clauseEncodedType
      (clauseFromSigns signs) := by
  simpa [clauseFromSigns] using clauseFromSignsAux_tmPolyTime 0 signs

/-- Build all clauses associated with a fixed finite list of falsifying rows. -/
def cnfFromSignRows (rows : List (List Bool)) (scope : List Nat) :
    ComplexityReduction.SAT.CNF :=
  rows.map (fun signs => clauseFromSigns signs scope)

/-- A fixed finite table of falsifying rows expands by a checked structured direct TM. -/
theorem cnfFromSignRows_tmPolyTime (rows : List (List Bool)) :
    ComplexityReduction.TMPolyTimeMap variableListEncodedType cnfEncodedType
      (cnfFromSignRows rows) := by
  induction rows with
  | nil =>
      simpa [cnfFromSignRows, cnfEncodedType] using
        (ComplexityReduction.TMPolyTimeMap.const variableListEncodedType cnfEncodedType
          ([] : ComplexityReduction.SAT.CNF))
  | cons signs rows ih =>
      have hHead := clauseFromSigns_tmPolyTime signs
      have hPair := ComplexityReduction.TMPolyTimeMap.prod_mk hHead ih
      have hCons := ComplexityReduction.TMPolyTimeMap.comp
        (ComplexityReduction.TMPolyTimeMap.list_cons clauseEncodedType) hPair
      simpa [Function.comp, cnfFromSignRows, cnfEncodedType] using hCons

/-- Fixed falsifying Boolean rows belonging to one exact relation symbol. -/
noncomputable def falsifyingSignRows (Γ : TableLanguage) (symbol : Γ.Symbol) :
    List (List Bool) :=
  ((Γ.relationOf symbol).falsifyingTuples.toList).map List.ofFn

/-- CNF block for one fixed relation symbol and a runtime variable scope. -/
noncomputable def symbolCNFBlock (Γ : TableLanguage) (symbol : Γ.Symbol)
    (scope : List Nat) : ComplexityReduction.SAT.CNF :=
  cnfFromSignRows (falsifyingSignRows Γ symbol) scope

/-- Every fixed relation-symbol block has a checked structured direct TM. -/
theorem symbolCNFBlock_tmPolyTime (Γ : TableLanguage) (symbol : Γ.Symbol) :
    ComplexityReduction.TMPolyTimeMap variableListEncodedType cnfEncodedType
      (symbolCNFBlock Γ symbol) := by
  simpa [symbolCNFBlock] using
    cnfFromSignRows_tmPolyTime (falsifyingSignRows Γ symbol)

/--
Dispatch a numeric relation code through a fixed list of exact language symbols.
The fallback is empty and is unreachable for codes emitted by the faithful CSP
formula presentation.
-/
noncomputable def constraintCNFDispatch (Γ : TableLanguage) :
    List Γ.Symbol → (Nat × List Nat) → ComplexityReduction.SAT.CNF
  | [], _ => []
  | symbol :: symbols, input =>
      if decide (input.1 = Presentation.FiniteDomainCSPTable.relationCode Γ symbol) then
        symbolCNFBlock Γ symbol input.2
      else
        constraintCNFDispatch Γ symbols input

/-- Direct-TM evidence for the fixed finite relation-code dispatch. -/
theorem constraintCNFDispatch_tmPolyTime (Γ : TableLanguage) (symbols : List Γ.Symbol) :
    ComplexityReduction.TMPolyTimeMap constraintCodeEncodedType cnfEncodedType
      (constraintCNFDispatch Γ symbols) := by
  induction symbols with
  | nil =>
      simpa [constraintCNFDispatch] using
        (ComplexityReduction.TMPolyTimeMap.const constraintCodeEncodedType cnfEncodedType
          ([] : ComplexityReduction.SAT.CNF))
  | cons symbol symbols ih =>
      let X := constraintCodeEncodedType
      have hCode : ComplexityReduction.TMPolyTimeMap X ComplexityReduction.EncodedType.nat
          (fun input : X.Carrier => input.1) := by
        simpa [X, constraintCodeEncodedType] using
          (ComplexityReduction.TMPolyTimeMap.fst ComplexityReduction.EncodedType.nat
            variableListEncodedType)
      have hExpected : ComplexityReduction.TMPolyTimeMap X ComplexityReduction.EncodedType.nat
          (fun _ : X.Carrier => Presentation.FiniteDomainCSPTable.relationCode Γ symbol) :=
        ComplexityReduction.TMPolyTimeMap.const X ComplexityReduction.EncodedType.nat
          (Presentation.FiniteDomainCSPTable.relationCode Γ symbol)
      have hEqInput :
          ComplexityReduction.TMPolyTimeMap X
            (ComplexityReduction.EncodedType.prod ComplexityReduction.EncodedType.nat
              ComplexityReduction.EncodedType.nat)
            (fun input : X.Carrier =>
              (input.1, Presentation.FiniteDomainCSPTable.relationCode Γ symbol)) :=
        ComplexityReduction.TMPolyTimeMap.prod_mk hCode hExpected
      have hEq := ComplexityReduction.TMPolyTimeMap.comp
        ComplexityReduction.TMPolyTimeMap.nat_eq hEqInput
      have hVariables : ComplexityReduction.TMPolyTimeMap X variableListEncodedType
          (fun input : X.Carrier => input.2) := by
        simpa [X, constraintCodeEncodedType] using
          (ComplexityReduction.TMPolyTimeMap.snd ComplexityReduction.EncodedType.nat
            variableListEncodedType)
      have hHit := ComplexityReduction.TMPolyTimeMap.comp
        (symbolCNFBlock_tmPolyTime Γ symbol) hVariables
      have hBranchInput :
          ComplexityReduction.TMPolyTimeMap X
            (ComplexityReduction.EncodedType.prod ComplexityReduction.EncodedType.bool X)
            (fun input : Nat × List Nat =>
              (decide (input.1 = Presentation.FiniteDomainCSPTable.relationCode Γ symbol),
                input)) :=
        ComplexityReduction.TMPolyTimeMap.prod_mk hEq
          (ComplexityReduction.TMPolyTimeMap.id X)
      have hBranch := ComplexityReduction.boolProduct_dispatch_tm_polytime X cnfEncodedType
        ih hHit
      have hOut := ComplexityReduction.TMPolyTimeMap.comp hBranch hBranchInput
      convert hOut using 1
      funext input
      by_cases hCodeEq :
          input.1 = Presentation.FiniteDomainCSPTable.relationCode Γ symbol <;>
        simp [Function.comp, constraintCNFDispatch, hCodeEq]

/-- Canonical complete symbol enumeration for one exact table language. -/
noncomputable def languageSymbols (Γ : TableLanguage) : List Γ.Symbol :=
  Finset.univ.toList

/-- Translate one faithful numeric constraint code to its structured CNF block. -/
noncomputable def constraintCodeToCNF (Γ : TableLanguage)
    (input : constraintCodeEncodedType.Carrier) : ComplexityReduction.SAT.CNF :=
  constraintCNFDispatch Γ (languageSymbols Γ) input

/-- Exact structured direct-TM evidence for one faithful numeric constraint code. -/
theorem constraintCodeToCNF_tmPolyTime (Γ : TableLanguage) :
    ComplexityReduction.TMPolyTimeMap constraintCodeEncodedType cnfEncodedType
      (constraintCodeToCNF Γ) := by
  simpa [constraintCodeToCNF] using
    constraintCNFDispatch_tmPolyTime Γ (languageSymbols Γ)

@[simp]
theorem clauseFromSignsAux_length (offset : Nat) (signs : List Bool) (scope : List Nat) :
    (clauseFromSignsAux offset signs scope).length = signs.length := by
  induction signs generalizing offset with
  | nil => rfl
  | cons sign signs ih =>
      simp [clauseFromSignsAux, ih]

theorem clauseFromSignsAux_getElem (offset : Nat) (signs : List Bool)
    (scope : List Nat) (index : Nat) (hIndex : index < signs.length) :
    (clauseFromSignsAux offset signs scope)[index]'(by
      simpa [clauseFromSignsAux_length] using hIndex) =
      { var := scope.getD (offset + index) (0 : Nat), neg := signs[index] } := by
  induction signs generalizing offset index with
  | nil => simp at hIndex
  | cons sign signs ih =>
      cases index with
      | zero =>
          simp [clauseFromSignsAux, literalAt]
      | succ index =>
          have hTail : index < signs.length := by simpa using hIndex
          simp only [clauseFromSignsAux, List.getElem_cons_succ]
          have hOffset : offset + 1 + index = offset + (index + 1) := by omega
          simpa only [hOffset] using ih (offset := offset + 1) (index := index) hTail

/-- The code-level fixed-row constructor is exactly the established tuple clause. -/
theorem clauseFromSigns_ofFn {arity : Nat} (scope : Fin arity → Nat)
    (tuple : ComplexityReduction.CSP.BoolTuple arity) :
    clauseFromSigns (List.ofFn tuple) (List.ofFn scope) =
      ComplexityReduction.CSP.clauseForTuple scope tuple := by
  unfold clauseFromSigns ComplexityReduction.CSP.clauseForTuple
  apply List.ext_getElem
  · simp
  · intro index hLeft hRight
    have hIndex : index < (List.ofFn tuple).length := by simpa using hRight
    have hArity : index < arity := by simpa using hIndex
    rw [clauseFromSignsAux_getElem (hIndex := hIndex)]
    simp [ComplexityReduction.CSP.literalForTuple, List.getD, hArity]

/-- One fixed-symbol block agrees exactly with CR's semantic CNF block. -/
theorem symbolCNFBlock_eq_constraintToCNF (Γ : TableLanguage)
    (constraint : ComplexityReduction.CSP.Constraint Γ) :
    symbolCNFBlock Γ constraint.symbol constraint.varsList =
      ComplexityReduction.CSP.Constraint.toCNF constraint := by
  simp only [symbolCNFBlock, falsifyingSignRows, cnfFromSignRows,
    ComplexityReduction.CSP.Constraint.toCNF, ComplexityReduction.CSP.Constraint.varsList,
    List.map_map]
  apply List.map_congr_left
  intro tuple _
  exact clauseFromSigns_ofFn constraint.vars tuple

theorem constraintCNFDispatch_eq_symbolBlock_of_mem (Γ : TableLanguage)
    (symbols : List Γ.Symbol) (symbol : Γ.Symbol) (hMem : symbol ∈ symbols)
    (scope : List Nat) :
    constraintCNFDispatch Γ symbols
        (Presentation.FiniteDomainCSPTable.relationCode Γ symbol, scope) =
      symbolCNFBlock Γ symbol scope := by
  induction symbols with
  | nil => simp at hMem
  | cons head tail ih =>
      by_cases hHead : symbol = head
      · subst head
        simp [constraintCNFDispatch]
      · have hTail : symbol ∈ tail := (List.mem_cons.mp hMem).resolve_left hHead
        have hNe :
          Presentation.FiniteDomainCSPTable.relationCode Γ symbol ≠
            Presentation.FiniteDomainCSPTable.relationCode Γ head := by
          intro hCode
          have hSymbol := Presentation.FiniteDomainCSPTable.relationCode_injective Γ hCode
          exact hHead hSymbol
        simp [constraintCNFDispatch, hNe, ih hTail]

/-- Faithful constraint codes always select their exact relation-symbol block. -/
theorem constraintCodeToCNF_eq_constraintToCNF (Γ : TableLanguage)
    (constraint : ComplexityReduction.CSP.Constraint Γ) :
    constraintCodeToCNF Γ (Presentation.FiniteDomainCSPTable.constraintCode constraint) =
      ComplexityReduction.CSP.Constraint.toCNF constraint := by
  rw [constraintCodeToCNF, Presentation.FiniteDomainCSPTable.constraintCode]
  rw [constraintCNFDispatch_eq_symbolBlock_of_mem Γ (languageSymbols Γ)
    constraint.symbol (by simp [languageSymbols]) constraint.varsList]
  exact symbolCNFBlock_eq_constraintToCNF Γ constraint

/-- Append one translated constraint block to the formula accumulator. -/
noncomputable def appendConstraintCNFStep (Γ : TableLanguage)
    (input : ComplexityReduction.SAT.CNF × constraintCodeEncodedType.Carrier) :
    ComplexityReduction.SAT.CNF :=
  input.1 ++ constraintCodeToCNF Γ input.2

/-- The accumulator step is a composition of the exact block TM and structured list append. -/
theorem appendConstraintCNFStep_tmPolyTime (Γ : TableLanguage) :
    ComplexityReduction.TMPolyTimeMap
      (ComplexityReduction.EncodedType.prod cnfEncodedType constraintCodeEncodedType)
      cnfEncodedType (appendConstraintCNFStep Γ) := by
  let X := ComplexityReduction.EncodedType.prod cnfEncodedType constraintCodeEncodedType
  have hAccumulator : ComplexityReduction.TMPolyTimeMap X cnfEncodedType
      (fun input : X.Carrier => input.1) := by
    simpa [X] using ComplexityReduction.TMPolyTimeMap.fst cnfEncodedType constraintCodeEncodedType
  have hConstraint : ComplexityReduction.TMPolyTimeMap X constraintCodeEncodedType
      (fun input : X.Carrier => input.2) := by
    simpa [X] using ComplexityReduction.TMPolyTimeMap.snd cnfEncodedType constraintCodeEncodedType
  have hBlock := ComplexityReduction.TMPolyTimeMap.comp
    (constraintCodeToCNF_tmPolyTime Γ) hConstraint
  have hAppendInput := ComplexityReduction.TMPolyTimeMap.prod_mk hAccumulator hBlock
  have hAppend := ComplexityReduction.TMPolyTimeMap.comp
    (ComplexityReduction.TMPolyTimeMap.list_append clauseEncodedType) hAppendInput
  simpa [X, Function.comp, appendConstraintCNFStep, cnfEncodedType] using hAppend

private theorem encodedList_inputSize_append (element : ComplexityReduction.EncodedType)
    (left right : List element.Carrier) :
    (ComplexityReduction.EncodedType.list element).inputSize (left ++ right) =
      (ComplexityReduction.EncodedType.list element).inputSize left +
        (ComplexityReduction.EncodedType.list element).inputSize right := by
  induction left with
  | nil => simp
  | cons clause left ih =>
      simp [ih, Nat.add_assoc]

theorem cnfEncodedType_inputSize_append (left right : ComplexityReduction.SAT.CNF) :
    cnfEncodedType.inputSize (left ++ right) =
      cnfEncodedType.inputSize left + cnfEncodedType.inputSize right := by
  simpa [cnfEncodedType, ComplexityReduction.Karp21.cnfStructuredEncodedType] using
    encodedList_inputSize_append ComplexityReduction.Karp21.clauseStructuredEncodedType
      left right

/-- Fold all faithful constraint codes into one structured CNF. -/
noncomputable def formulaCodeToCNF (Γ : TableLanguage)
    (formula : formulaCodeEncodedType.Carrier) : ComplexityReduction.SAT.CNF :=
  formula.foldl (fun accumulator constraint =>
    appendConstraintCNFStep Γ (accumulator, constraint)) []

/--
The formula fold is directly TM polynomial-time.  The global accumulator bound
is derived from the direct constraint-block machine's own output-size theorem.
-/
theorem formulaCodeToCNF_tmPolyTime (Γ : TableLanguage) :
    ComplexityReduction.TMPolyTimeMap formulaCodeEncodedType cnfEncodedType
      (formulaCodeToCNF Γ) := by
  have hBlockTM := constraintCodeToCNF_tmPolyTime Γ
  rcases hBlockTM.outputSizeBound with ⟨degree, coefficient, offset, hBlockSize⟩
  let base : Polynomial Nat := Polynomial.C 0
  let grow : Polynomial Nat :=
    Polynomial.C coefficient * Polynomial.X ^ degree + Polynomial.C offset
  rcases appendConstraintCNFStep_tmPolyTime Γ with ⟨hStep⟩
  refine ComplexityReduction.TMPolyTimeMap.list_foldl_typed_growth_bounded
    constraintCodeEncodedType cnfEncodedType (appendConstraintCNFStep Γ)
    ([] : ComplexityReduction.SAT.CNF) hStep base grow ?_ ?_
  · intro source
    change
      (ComplexityReduction.EncodedType.list
        ComplexityReduction.Karp21.clauseStructuredEncodedType).inputSize
          ([] : List ComplexityReduction.SAT.Clause) ≤ base.eval
            (formulaCodeEncodedType.inputSize source)
    rw [show base.eval (formulaCodeEncodedType.inputSize source) = 0 by simp [base]]
    exact Nat.le_of_eq
      (ComplexityReduction.EncodedType.inputSize_list_nil
        ComplexityReduction.Karp21.clauseStructuredEncodedType)
  · intro source accumulator constraint hConstraintSize
    have hMono : constraintCodeEncodedType.inputSize constraint ^ degree ≤
        formulaCodeEncodedType.inputSize source ^ degree :=
      Nat.pow_le_pow_left hConstraintSize degree
    have hBlock := hBlockSize constraint
    rw [appendConstraintCNFStep, cnfEncodedType_inputSize_append]
    have hBound :
        cnfEncodedType.inputSize (constraintCodeToCNF Γ constraint) ≤
          coefficient * formulaCodeEncodedType.inputSize source ^ degree + offset :=
      hBlock.trans (Nat.add_le_add_right (Nat.mul_le_mul_left coefficient hMono) offset)
    simpa [grow, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X] using
      Nat.add_le_add_left hBound (cnfEncodedType.inputSize accumulator)

/-- The faithful table-formula codec exposed as a structural code-list map. -/
def tableFormulaCode (Γ : TableLanguage)
    (formula : (Presentation.FiniteDomainCSPTable.lawfulRepresentation Γ).Carrier) :
    formulaCodeEncodedType.Carrier :=
  Presentation.FiniteDomainCSPTable.formulaCode Γ formula

/-- Reading the faithful table formula as its canonical code list is encoding-preserving. -/
theorem tableFormulaCode_tmPolyTime (Γ : TableLanguage) :
    ComplexityReduction.TMPolyTimeMap
      (Presentation.FiniteDomainCSPTable.lawfulRepresentation Γ).encodedType
      formulaCodeEncodedType (tableFormulaCode Γ) :=
  (ComplexityReduction.TMBackedCostedMap.ofEncodingEquiv
    (Presentation.FiniteDomainCSPTable.lawfulRepresentation Γ).encodedType
    formulaCodeEncodedType (tableFormulaCode Γ) (Equiv.refl _)
    (by
      intro formula
      change formulaCodeEncodedType.encode
          (Presentation.FiniteDomainCSPTable.formulaCode Γ formula) =
        (formulaCodeEncodedType.encode
          (Presentation.FiniteDomainCSPTable.formulaCode Γ formula)).map id
      rw [List.map_id])).tm_polytime

/-- Exact structured CNF expansion on the faithful table-CSP presentation. -/
noncomputable def tableFormulaToCNF (Γ : TableLanguage)
    (formula : (Presentation.FiniteDomainCSPTable.lawfulRepresentation Γ).Carrier) :
    ComplexityReduction.SAT.CNF :=
  formulaCodeToCNF Γ (tableFormulaCode Γ formula)

/-- Direct-TM evidence at the exact faithful table-CSP and structured CNF codecs. -/
theorem tableFormulaToCNF_tmPolyTime (Γ : TableLanguage) :
    ComplexityReduction.TMPolyTimeMap
      (Presentation.FiniteDomainCSPTable.lawfulRepresentation Γ).encodedType
      cnfEncodedType (tableFormulaToCNF Γ) := by
  have hComp := ComplexityReduction.TMPolyTimeMap.comp
    (formulaCodeToCNF_tmPolyTime Γ) (tableFormulaCode_tmPolyTime Γ)
  simpa [Function.comp, tableFormulaToCNF] using hComp

theorem formulaCodeToCNF_fold_correct (Γ : TableLanguage)
    (formula : ComplexityReduction.CSP.Formula Γ) (accumulator : ComplexityReduction.SAT.CNF) :
    (Presentation.FiniteDomainCSPTable.formulaCode Γ formula).foldl
        (fun acc constraint => appendConstraintCNFStep Γ (acc, constraint)) accumulator =
      accumulator ++ ComplexityReduction.CSP.Formula.toCNF formula := by
  induction formula generalizing accumulator with
  | nil =>
      have hCode : Presentation.FiniteDomainCSPTable.formulaCode Γ
          ([] : ComplexityReduction.CSP.Formula Γ) = [] := rfl
      rw [hCode, ComplexityReduction.CSP.Formula.toCNF_nil]
      exact (List.foldl_nil).trans (List.append_nil accumulator).symm
  | cons constraint formula ih =>
      simp only [Presentation.FiniteDomainCSPTable.formulaCode, List.map_cons]
      change
        (Presentation.FiniteDomainCSPTable.formulaCode Γ formula).foldl
            (fun acc code => appendConstraintCNFStep Γ (acc, code))
            (appendConstraintCNFStep Γ
              (accumulator, Presentation.FiniteDomainCSPTable.constraintCode constraint)) =
          accumulator ++ ComplexityReduction.CSP.Formula.toCNF (constraint :: formula)
      rw [ih]
      simp [appendConstraintCNFStep, constraintCodeToCNF_eq_constraintToCNF,
        ComplexityReduction.CSP.Formula.toCNF, List.append_assoc]

/-- The checked code-list fold runs exactly CR's established semantic construction. -/
theorem tableFormulaToCNF_eq_toCNF (Γ : TableLanguage)
    (formula : ComplexityReduction.CSP.Formula Γ) :
    tableFormulaToCNF Γ formula = ComplexityReduction.CSP.Formula.toCNF formula := by
  simpa [tableFormulaToCNF, tableFormulaCode, formulaCodeToCNF] using
    formulaCodeToCNF_fold_correct Γ formula []

/-! ### Exact V2 programs, certificates, and component resolution -/

/-- The original Boolean table presentation used as the internal typed midpoint. -/
abbrev tableProblem (Γ : TableLanguage) : PresentedProblem :=
  Presentation.FiniteDomainCSPTable.presentedProblem Γ

/-- Exact direct-TM primitive for faithful table-CSP to faithful structured CNF. -/
noncomputable def tableFormulaToCNFPrimitive (Γ : TableLanguage) :
    Program.Primitive (tableProblem Γ).representation targetProblem.representation :=
  Program.Primitive.ofTMPolyTime (tableFormulaToCNF Γ) (tableFormulaToCNF_tmPolyTime Γ)

/-- The table-CSP-to-CNF program contains exactly the checked expansion atom. -/
noncomputable def tableFormulaToCNFProgram (Γ : TableLanguage) :
    Program.PolyProg (tableProblem Γ).representation targetProblem.representation :=
  .atom (tableFormulaToCNFPrimitive Γ)

@[simp]
theorem tableFormulaToCNFProgram_run (Γ : TableLanguage)
    (formula : (tableProblem Γ).Instance) :
    (tableFormulaToCNFProgram Γ).run formula = tableFormulaToCNF Γ formula :=
  rfl

/-- The exact semantic law for the checked faithful table-CSP CNF expansion. -/
theorem tableFormulaToCNFProgram_correct (Γ : TableLanguage)
    (formula : (tableProblem Γ).Instance) :
    (tableProblem Γ).accepts formula ↔
      targetProblem.accepts ((tableFormulaToCNFProgram Γ).run formula) := by
  change ComplexityReduction.CSP.Formula.Satisfiable formula ↔
    ComplexityReduction.SAT.CNF.Satisfiable (tableFormulaToCNF Γ formula)
  rw [tableFormulaToCNF_eq_toCNF]
  exact (ComplexityReduction.CSP.Formula.toCNF_satisfiable_iff formula).symm

/-- Certified reverse syntax adapter from the Bool finite-domain hub to the table midpoint. -/
noncomputable def reverseAdapter (Γ : TableLanguage) :
    CertifiedReduction (sourceProblem Γ) (tableProblem Γ) where
  program := formulaToBoolProgram Γ
  correct := by
    intro formula
    change ComplexityReduction.CSP.FiniteDomain.Formula.Satisfiable formula ↔
      ComplexityReduction.CSP.Formula.Satisfiable (formulaToBool Γ formula)
    exact (formulaToBool_satisfiable_iff Γ formula).symm

/-- Certified faithful table-CSP-to-structured-CNF expansion. -/
noncomputable def tableSharedGadget (Γ : TableLanguage) :
    CertifiedReduction (tableProblem Γ) targetProblem where
  program := tableFormulaToCNFProgram Γ
  correct := tableFormulaToCNFProgram_correct Γ

/--
The reusable exact-endpoint Boolean finite-domain CSP hub to structured CNF
gadget.  Its sole program is the composition of the encoding-preserving reverse
adapter and the checked faithful CNF expansion atom.
-/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def sharedGadget (Γ : TableLanguage) :
    CertifiedReduction (sourceProblem Γ) targetProblem :=
  CertifiedReduction.comp (tableSharedGadget Γ) (reverseAdapter Γ)

@[simp]
theorem sharedGadget_program (Γ : TableLanguage) :
    (sharedGadget Γ).program =
      Program.PolyProg.comp (tableFormulaToCNFProgram Γ) (formulaToBoolProgram Γ) :=
  rfl

@[simp]
theorem sharedGadget_run (Γ : TableLanguage) (formula : (sourceProblem Γ).Instance) :
    (sharedGadget Γ).program.run formula =
      tableFormulaToCNF Γ (formulaToBool Γ formula) :=
  rfl

/-- The shared gadget's semantic projection is indexed by its one stored program. -/
theorem sharedGadget_correct (Γ : TableLanguage) (formula : (sourceProblem Γ).Instance) :
    (sourceProblem Γ).accepts formula ↔
      targetProblem.accepts ((sharedGadget Γ).program.run formula) :=
  (sharedGadget Γ).correct formula

/-- The direct TM is definitionally the compiler output of the same stored program. -/
@[simp]
theorem sharedGadget_directTM_eq_compileTM (Γ : TableLanguage) :
    (sharedGadget Γ).directTM = (sharedGadget Γ).program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM (sharedGadget Γ)

/-- Exact shared-component request accepted by this domain-owned gadget. -/
abbrev SharedGadgetRequest (Γ : TableLanguage) : Type 2 :=
  Protocol.ComponentRequest .sharedGadget (sourceProblem Γ) targetProblem

/-- The request fixes the exact Boolean finite-domain CSP and structured CNF hubs. -/
def request (Γ : TableLanguage) : SharedGadgetRequest Γ :=
  .exact

/-- Accepted exact component resolution for the newly closed shared gadget. -/
noncomputable def resolution (Γ : TableLanguage) :
    Protocol.ComponentResolution .sharedGadget (sourceProblem Γ) targetProblem :=
  Protocol.ComponentResolver.accept (request Γ) (sharedGadget Γ)

@[simp]
theorem resolution_exact (Γ : TableLanguage) :
    resolution Γ = .accepted (sharedGadget Γ) :=
  rfl

end
end BoolFiniteDomainCSPToStructuredCNF
end Domain
end ComplexityReduction
