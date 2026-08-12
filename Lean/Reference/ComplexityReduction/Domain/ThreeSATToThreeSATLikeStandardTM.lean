/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.HittingSet.StructuredRoute
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ListLookupTM
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.BoolDispatch
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Reduction
import ComplexityReduction.Presentation.ThreeSATLike
import ComplexityReduction.Problems.Karp21.Satisfiability
import ComplexityReduction.Program.EncodingTransport
import ComplexityReduction.Program.List
import ComplexityReduction.Protocol.ComponentResolver

/-!
Direct-TM companion for the reusable structured bundled-3SAT to fixed
3SAT-like CSP hub component.

The read-only CSP library supplies the semantic map
`Hardness.ThreeSATLike.threeCNFToFormula` but only a costed certificate.  This
leaf keeps that exact executable and rebuilds its finite list operations from
direct-TM list lookup, length, map, and flattening combinators.  No costed
certificate is used as a source of machine capability.
-/

namespace ComplexityReduction
namespace Domain
namespace ThreeSATToThreeSATLikeStandardTM

open ComplexityReduction
open ComplexityReduction.CSP
open ComplexityReduction.CSP.Examples
open ComplexityReduction.CSP.Hardness.ThreeSATLike
open Certificate Encoding Program

/-- The direct-TM encoding of one structured SAT literal. -/
abbrev literalEncoding : EncodedType := ComplexityReduction.Karp21.literalStructuredEncodedType

/-- The direct-TM encoding of one structured SAT clause. -/
abbrev clauseEncoding : EncodedType := ComplexityReduction.Karp21.clauseStructuredEncodedType

/-- The direct-TM encoding of one bundled local 3SAT formula. -/
abbrev sourceEncoding : EncodedType := ComplexityReduction.Karp21.threeCNFStructuredEncodedType

/-- The direct-TM encoding selected for one 3SAT-like CSP formula. -/
noncomputable abbrev targetEncoding : EncodedType := Presentation.ThreeSATLike.encodedType

/-- A fixed fallback literal used only by bounded positional lookups. -/
def defaultLiteral : SAT.Literal := SAT.Literal.positive 0

/-- The first literal, with a fixed fallback for an empty clause. -/
def firstLiteral (clause : SAT.Clause) : SAT.Literal :=
  clause.getD 0 defaultLiteral

/-- The second literal, repeated from the first when the clause is unary. -/
def secondLiteral (clause : SAT.Clause) : SAT.Literal :=
  if 1 < clause.length then clause.getD 1 defaultLiteral else firstLiteral clause

/-- The third literal, repeated from the second when the clause is binary. -/
def thirdLiteral (clause : SAT.Clause) : SAT.Literal :=
  if 2 < clause.length then clause.getD 2 defaultLiteral else secondLiteral clause

/-- The one-constraint nonempty-clause realization. -/
def nonemptyClauseFormula (clause : SAT.Clause) : Formula threeSATLikeLanguage :=
  [constraintOfLiterals (firstLiteral clause) (secondLiteral clause) (thirdLiteral clause)]

/--
The exact read-only clause construction expressed through bounded lookups.
The empty branch retains the established contradictory two-constraint block.
-/
def clauseExecutable (clause : SAT.Clause) : Formula threeSATLikeLanguage :=
  if clause.length = 0 then contradictionBlock else nonemptyClauseFormula clause

theorem clauseExecutable_eq_clauseToFormula (clause : SAT.Clause) :
    clauseExecutable clause = clauseToFormula clause := by
  cases clause with
  | nil =>
      simp [clauseExecutable, clauseToFormula]
  | cons first rest =>
      cases rest with
      | nil =>
          simp [clauseExecutable, nonemptyClauseFormula, firstLiteral, secondLiteral,
            thirdLiteral, clauseToFormula]
      | cons second rest =>
          cases rest with
          | nil =>
              simp [clauseExecutable, nonemptyClauseFormula, firstLiteral, secondLiteral,
                thirdLiteral, clauseToFormula]
          | cons third rest =>
              simp [clauseExecutable, nonemptyClauseFormula, firstLiteral, secondLiteral,
                thirdLiteral, clauseToFormula]

/-- The exact reusable 3SAT-to-CSP executable. -/
def executable (formula : SAT.ThreeCNF) : Formula threeSATLikeLanguage :=
  formula.clauses.flatMap clauseExecutable

/-- The executable is definitionally aligned with the read-only semantic construction. -/
theorem executable_eq_readOnly (formula : SAT.ThreeCNF) :
    executable formula = threeCNFToFormula formula := by
  change formula.clauses.flatMap clauseExecutable = formula.clauses.flatMap clauseToFormula
  exact congrArg (fun f : SAT.Clause → Formula threeSATLikeLanguage =>
    formula.clauses.flatMap f) (by
      funext clause
      exact clauseExecutable_eq_clauseToFormula clause)

/-- The relation-code arithmetic corresponding to the fixed polarity constructor order. -/
def polarityCode (first second third : Bool) : Nat :=
  (if first then 1 else 0) + (if second then 2 else 0) + (if third then 4 else 0)

theorem relationCode_symbolOfNegs (first second third : Bool) :
    Presentation.ThreeSATLike.relationCode (symbolOfNegs first second third) =
      polarityCode first second third := by
  cases first <;> cases second <;> cases third <;> rfl

theorem constraintCode_ofLiterals (first second third : SAT.Literal) :
    Presentation.ThreeSATLike.constraintCode (constraintOfLiterals first second third) =
      (polarityCode first.neg second.neg third.neg,
        [first.var, second.var, third.var]) := by
  rcases first with ⟨firstVar, firstNeg⟩
  rcases second with ⟨secondVar, secondNeg⟩
  rcases third with ⟨thirdVar, thirdNeg⟩
  cases firstNeg <;> cases secondNeg <;> cases thirdNeg <;>
    simp [constraintOfLiterals, polarityCode, Presentation.ThreeSATLike.constraintCode,
      Presentation.ThreeSATLike.relationCode, symbolOfNegs, Constraint.varsList, List.ofFn,
      Fin.foldr, Fin.foldr.loop, threeSATLikeLanguage, threeSATLikeRelationOf]

/-- Direct-TM lookup at a fixed position in the structured clause encoding. -/
theorem literalAt_tmPolyTime (index : Nat) :
    ComplexityReduction.TMPolyTimeMap clauseEncoding literalEncoding
      (fun clause : SAT.Clause => clause.getD index defaultLiteral) := by
  have hInput : ComplexityReduction.TMPolyTimeMap clauseEncoding
      (ComplexityReduction.EncodedType.prod
        (ComplexityReduction.EncodedType.list literalEncoding)
        ComplexityReduction.EncodedType.nat)
      (fun clause : SAT.Clause => (clause, index)) := by
    simpa [clauseEncoding] using
      ComplexityReduction.TMPolyTimeMap.prod_id_const
        (ComplexityReduction.EncodedType.list literalEncoding)
        ComplexityReduction.EncodedType.nat index
  have hComp := ComplexityReduction.TMPolyTimeMap.comp
    (ComplexityReduction.Karp21.EncodedListLookup.getD_tm_polytime literalEncoding defaultLiteral)
    hInput
  simpa [ComplexityReduction.Karp21.EncodedListLookup.getD] using hComp

/-- The first bounded lookup uses the shared encoded-list lookup machine. -/
theorem firstLiteral_tmPolyTime :
    ComplexityReduction.TMPolyTimeMap clauseEncoding literalEncoding firstLiteral := by
  simpa [firstLiteral] using literalAt_tmPolyTime 0

/-- The clause length is computed by the shared encoded-list length machine. -/
theorem clauseLength_tmPolyTime :
    ComplexityReduction.TMPolyTimeMap clauseEncoding ComplexityReduction.EncodedType.nat
      List.length := by
  simpa [clauseEncoding] using
    (ComplexityReduction.Karp21.HittingSet.listLengthTMBackedMap literalEncoding).tm_polytime

/-- Compare a fixed literal position with the encoded clause length. -/
theorem clauseIndexLtLength_tmPolyTime (index : Nat) :
    ComplexityReduction.TMPolyTimeMap clauseEncoding ComplexityReduction.EncodedType.bool
      (fun clause : SAT.Clause => decide (index < clause.length)) := by
  have hIndex : ComplexityReduction.TMPolyTimeMap clauseEncoding
      ComplexityReduction.EncodedType.nat (fun _ : SAT.Clause => index) :=
    ComplexityReduction.TMPolyTimeMap.const clauseEncoding ComplexityReduction.EncodedType.nat index
  have hPair := ComplexityReduction.TMPolyTimeMap.prod_mk hIndex clauseLength_tmPolyTime
  have hComp := ComplexityReduction.TMPolyTimeMap.comp ComplexityReduction.natLtBool_tm_polytime hPair
  simpa [ComplexityReduction.natLtBool, Function.comp] using hComp

/-- The second literal branches only on the shared length comparison. -/
theorem secondLiteral_tmPolyTime :
    ComplexityReduction.TMPolyTimeMap clauseEncoding literalEncoding secondLiteral := by
  have hTagged := ComplexityReduction.TMPolyTimeMap.prod_mk
    (clauseIndexLtLength_tmPolyTime 1)
    (ComplexityReduction.TMPolyTimeMap.id clauseEncoding)
  have hDispatch := ComplexityReduction.boolProduct_dispatch_tm_polytime
    clauseEncoding literalEncoding
    (fFalse := firstLiteral) (fTrue := fun clause : SAT.Clause => clause.getD 1 defaultLiteral)
    firstLiteral_tmPolyTime (literalAt_tmPolyTime 1)
  have hComp := ComplexityReduction.TMPolyTimeMap.comp hDispatch hTagged
  convert hComp using 1
  funext clause
  by_cases h : 1 < clause.length <;> simp [secondLiteral, Function.comp, h]

/-- The third literal branches only on the shared length comparison. -/
theorem thirdLiteral_tmPolyTime :
    ComplexityReduction.TMPolyTimeMap clauseEncoding literalEncoding thirdLiteral := by
  have hTagged := ComplexityReduction.TMPolyTimeMap.prod_mk
    (clauseIndexLtLength_tmPolyTime 2)
    (ComplexityReduction.TMPolyTimeMap.id clauseEncoding)
  have hDispatch := ComplexityReduction.boolProduct_dispatch_tm_polytime
    clauseEncoding literalEncoding
    (fFalse := secondLiteral) (fTrue := fun clause : SAT.Clause => clause.getD 2 defaultLiteral)
    secondLiteral_tmPolyTime (literalAt_tmPolyTime 2)
  have hComp := ComplexityReduction.TMPolyTimeMap.comp hDispatch hTagged
  convert hComp using 1
  funext clause
  by_cases h : 2 < clause.length <;> simp [thirdLiteral, Function.comp, h]

private theorem literalNeg_tmPolyTime
    (literalMap : SAT.Clause → SAT.Literal)
    (hLiteral : ComplexityReduction.TMPolyTimeMap clauseEncoding literalEncoding literalMap) :
    ComplexityReduction.TMPolyTimeMap clauseEncoding ComplexityReduction.EncodedType.bool
      (fun clause => (literalMap clause).neg) := by
  have hComp := ComplexityReduction.TMPolyTimeMap.comp
    ComplexityReduction.Karp21.Clique.literal_neg_tm_polytime hLiteral
  simpa [Function.comp] using hComp

private theorem literalVar_tmPolyTime
    (literalMap : SAT.Clause → SAT.Literal)
    (hLiteral : ComplexityReduction.TMPolyTimeMap clauseEncoding literalEncoding literalMap) :
    ComplexityReduction.TMPolyTimeMap clauseEncoding ComplexityReduction.EncodedType.nat
      (fun clause => (literalMap clause).var) := by
  have hComp := ComplexityReduction.TMPolyTimeMap.comp
    ComplexityReduction.Karp21.Clique.literal_var_tm_polytime hLiteral
  simpa [Function.comp] using hComp

/-- Compute the canonical fixed-language relation code from literal polarities. -/
theorem polarityCode_tmPolyTime :
    ComplexityReduction.TMPolyTimeMap clauseEncoding ComplexityReduction.EncodedType.nat
      (fun clause : SAT.Clause =>
        polarityCode (firstLiteral clause).neg (secondLiteral clause).neg (thirdLiteral clause).neg) := by
  have hFirstNat := ComplexityReduction.TMPolyTimeMap.comp ComplexityReduction.boolToNat_tm_polytime
    (literalNeg_tmPolyTime firstLiteral firstLiteral_tmPolyTime)
  have hSecondNat := ComplexityReduction.TMPolyTimeMap.comp ComplexityReduction.boolToNat_tm_polytime
    (literalNeg_tmPolyTime secondLiteral secondLiteral_tmPolyTime)
  have hThirdNat := ComplexityReduction.TMPolyTimeMap.comp ComplexityReduction.boolToNat_tm_polytime
    (literalNeg_tmPolyTime thirdLiteral thirdLiteral_tmPolyTime)
  have hSecondDouble := ComplexityReduction.TMPolyTimeMap.comp
    (ComplexityReduction.nat_mul_const_tm_polytime 2) hSecondNat
  have hThirdQuadruple := ComplexityReduction.TMPolyTimeMap.comp
    (ComplexityReduction.nat_mul_const_tm_polytime 4) hThirdNat
  have hFirstSecond := ComplexityReduction.TMPolyTimeMap.prod_mk hFirstNat hSecondDouble
  have hFirstSecondSum := ComplexityReduction.TMPolyTimeMap.comp
    ComplexityReduction.natAdd_tm_polytime hFirstSecond
  have hAll := ComplexityReduction.TMPolyTimeMap.prod_mk hFirstSecondSum hThirdQuadruple
  have hOut := ComplexityReduction.TMPolyTimeMap.comp ComplexityReduction.natAdd_tm_polytime hAll
  convert hOut using 1
  funext clause
  simp [Function.comp, polarityCode, ComplexityReduction.boolToNat]

/-- The ordered variable payload of one nonempty 3SAT-like constraint. -/
def variableCode (clause : SAT.Clause) : List Nat :=
  [(firstLiteral clause).var, (secondLiteral clause).var, (thirdLiteral clause).var]

/-- Build the ordered variable payload using only direct-TM projections and list constructors. -/
theorem variableCode_tmPolyTime :
    ComplexityReduction.TMPolyTimeMap clauseEncoding
      (ComplexityReduction.EncodedType.list ComplexityReduction.EncodedType.nat)
      variableCode := by
  let natList := ComplexityReduction.EncodedType.list ComplexityReduction.EncodedType.nat
  have hFirst := literalVar_tmPolyTime firstLiteral firstLiteral_tmPolyTime
  have hSecond := literalVar_tmPolyTime secondLiteral secondLiteral_tmPolyTime
  have hThird := literalVar_tmPolyTime thirdLiteral thirdLiteral_tmPolyTime
  have hOut := ComplexityReduction.TMPolyTimeMap.list_cons_of hFirst
    (ComplexityReduction.TMPolyTimeMap.list_cons_of hSecond
      (ComplexityReduction.TMPolyTimeMap.list_singleton_of hThird))
  simpa [variableCode, natList] using hOut

/-- The raw encoder payload for a nonempty clause's one constraint. -/
def nonemptyClauseCode (clause : SAT.Clause) : List (Nat × List Nat) :=
  [(polarityCode (firstLiteral clause).neg (secondLiteral clause).neg (thirdLiteral clause).neg,
    variableCode clause)]

/-- The raw nonempty-clause payload is directly TM computable. -/
theorem nonemptyClauseCode_tmPolyTime :
    ComplexityReduction.TMPolyTimeMap clauseEncoding
      Presentation.ThreeSATLike.formulaCodeEncodedType nonemptyClauseCode := by
  have hConstraint := ComplexityReduction.TMPolyTimeMap.prod_mk
    polarityCode_tmPolyTime variableCode_tmPolyTime
  have hOut := ComplexityReduction.TMPolyTimeMap.list_singleton_of hConstraint
  simpa [nonemptyClauseCode, Presentation.ThreeSATLike.formulaCodeEncodedType,
    Presentation.ThreeSATLike.constraintCodeEncodedType, Function.comp] using hOut

private theorem nonemptyClauseCode_eq_formulaCode (clause : SAT.Clause) :
    nonemptyClauseCode clause =
      Presentation.ThreeSATLike.formulaCode (nonemptyClauseFormula clause) := by
  simp [nonemptyClauseCode, nonemptyClauseFormula, Presentation.ThreeSATLike.formulaCode,
    variableCode, constraintCode_ofLiterals]

/-- The exact raw payload selected by the clause executable. -/
noncomputable def clauseCode (clause : SAT.Clause) : List (Nat × List Nat) :=
  Presentation.ThreeSATLike.formulaCode (clauseExecutable clause)

private theorem clauseIsEmpty_tmPolyTime :
    ComplexityReduction.TMPolyTimeMap clauseEncoding ComplexityReduction.EncodedType.bool
      (fun clause : SAT.Clause => decide (clause.length = 0)) := by
  have hZero : ComplexityReduction.TMPolyTimeMap clauseEncoding
      ComplexityReduction.EncodedType.nat (fun _ : SAT.Clause => (show Nat from 0)) :=
    ComplexityReduction.TMPolyTimeMap.const clauseEncoding ComplexityReduction.EncodedType.nat
      (show Nat from 0)
  have hPair := ComplexityReduction.TMPolyTimeMap.prod_mk clauseLength_tmPolyTime hZero
  have hOut := ComplexityReduction.TMPolyTimeMap.comp ComplexityReduction.TMPolyTimeMap.nat_eq hPair
  convert hOut using 1

private theorem clauseCode_tmPolyTime :
    ComplexityReduction.TMPolyTimeMap clauseEncoding
      Presentation.ThreeSATLike.formulaCodeEncodedType clauseCode := by
  have hTagged := ComplexityReduction.TMPolyTimeMap.prod_mk
    clauseIsEmpty_tmPolyTime (ComplexityReduction.TMPolyTimeMap.id clauseEncoding)
  have hEmpty : ComplexityReduction.TMPolyTimeMap clauseEncoding
      Presentation.ThreeSATLike.formulaCodeEncodedType
      (fun _ : SAT.Clause => Presentation.ThreeSATLike.formulaCode contradictionBlock) :=
    ComplexityReduction.TMPolyTimeMap.const clauseEncoding
      Presentation.ThreeSATLike.formulaCodeEncodedType
      (Presentation.ThreeSATLike.formulaCode contradictionBlock)
  have hDispatch := ComplexityReduction.boolProduct_dispatch_tm_polytime
    clauseEncoding Presentation.ThreeSATLike.formulaCodeEncodedType
    (fFalse := nonemptyClauseCode)
    (fTrue := fun _ : SAT.Clause => Presentation.ThreeSATLike.formulaCode contradictionBlock)
    nonemptyClauseCode_tmPolyTime hEmpty
  have hOut := ComplexityReduction.TMPolyTimeMap.comp hDispatch hTagged
  convert hOut using 1
  funext clause
  by_cases h : clause.length = 0
  · simp [clauseCode, clauseExecutable, h]
  · simp [clauseCode, clauseExecutable, h, nonemptyClauseCode_eq_formulaCode]

/-- The clause executable's direct-TM witness uses the same selected formula encoder. -/
theorem clauseExecutable_tmPolyTime :
    ComplexityReduction.TMPolyTimeMap clauseEncoding targetEncoding clauseExecutable := by
  apply ComplexityReduction.TMPolyTimeMap.transport_output
    (Z := targetEncoding) (targetOutput := clauseExecutable)
    clauseCode_tmPolyTime (Equiv.refl _)
  intro clause
  rw [show clauseCode clause =
    Presentation.ThreeSATLike.formulaCode (clauseExecutable clause) from rfl]
  change _ = List.map (fun symbol => symbol) _
  exact (List.map_id _).symm

private theorem sourceClauses_tmPolyTime :
    ComplexityReduction.TMPolyTimeMap sourceEncoding
      (ComplexityReduction.EncodedType.list clauseEncoding)
      (fun formula : SAT.ThreeCNF => formula.clauses) :=
  ComplexityReduction.TMPolyTimeMap.of_encodingEquiv sourceEncoding
    (ComplexityReduction.EncodedType.list clauseEncoding)
    (fun formula : SAT.ThreeCNF => formula.clauses) (Equiv.refl _)
    (by
      intro formula
      change
        (ComplexityReduction.EncodedType.list clauseEncoding).encode formula.clauses =
          (sourceEncoding.encode formula).map id
      simp [clauseEncoding,
        ComplexityReduction.Karp21.threeCNFStructuredEncodedType,
        ComplexityReduction.Karp21.cnfStructuredEncodedType])

/-- The raw formula payload produced by flattening the clause payloads. -/
noncomputable def executableCode (formula : SAT.ThreeCNF) : List (Nat × List Nat) :=
  formula.clauses.flatMap clauseCode

private theorem executableCode_eq_formulaCode (formula : SAT.ThreeCNF) :
    executableCode formula = Presentation.ThreeSATLike.formulaCode (executable formula) := by
  unfold executableCode executable Presentation.ThreeSATLike.formulaCode
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro clause _
  rfl

private theorem executableCode_tmPolyTime :
    ComplexityReduction.TMPolyTimeMap sourceEncoding
      Presentation.ThreeSATLike.formulaCodeEncodedType executableCode := by
  have hMapped := ComplexityReduction.TMPolyTimeMap.list_map clauseCode_tmPolyTime
  have hMapComp := ComplexityReduction.TMPolyTimeMap.comp hMapped sourceClauses_tmPolyTime
  have hFlat := Program.listFlatten_tmPolyTime
    Presentation.ThreeSATLike.constraintCodeEncodedType
  have hOut := ComplexityReduction.TMPolyTimeMap.comp hFlat hMapComp
  convert hOut using 1

/--
The exact 3SAT-to-fixed-3SAT-like executable is direct-TM polynomial time.  Its
machine computes the canonical encoder payload before reinterpreting that same
payload through the target presentation's explicit encoder.
-/
theorem executable_tmPolyTime :
    ComplexityReduction.TMPolyTimeMap sourceEncoding targetEncoding executable := by
  apply ComplexityReduction.TMPolyTimeMap.transport_output
    (Z := targetEncoding) (targetOutput := executable)
    executableCode_tmPolyTime (Equiv.refl _)
  intro formula
  rw [executableCode_eq_formulaCode formula]
  change _ = List.map (fun symbol => symbol) _
  exact (List.map_id _).symm

/-- The canonical structured bundled-3SAT hub. -/
abbrev sourceProblem : PresentedProblem :=
  Problems.Karp21.Satisfiability.threeSATStructuredProblem

/-- The explicit fixed-language 3SAT-like CSP hub. -/
noncomputable abbrev targetProblem : PresentedProblem :=
  Presentation.ThreeSATLike.presentedProblem

/-- The exact role-indexed endpoint of the reusable 3SAT-to-CSP hub component. -/
noncomputable abbrev SharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget sourceProblem targetProblem

/-- The unique request for the reusable structured-3SAT-to-CSP gadget. -/
noncomputable def request : SharedGadgetRequest := .exact

/-- The primitive is indexed by the exact executable and its direct-TM witness. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def sharedGadgetPrimitive :
    Primitive sourceProblem.representation targetProblem.representation :=
  Primitive.ofTMPolyTime executable executable_tmPolyTime

/-- The shared computation is a single typed primitive atom. -/
noncomputable def sharedGadgetProgram :
    PolyProg sourceProblem.representation targetProblem.representation :=
  .atom sharedGadgetPrimitive

@[simp] theorem sharedGadgetProgram_run (input : sourceProblem.Instance) :
    sharedGadgetProgram.run input = executable input :=
  rfl

/-- The program compiler preserves the exact direct-TM witness of its primitive. -/
@[simp] theorem sharedGadgetProgram_directTM :
    sharedGadgetProgram.compileTM = executable_tmPolyTime :=
  rfl

/--
The authoritative shared certificate uses the same atom program as its
executable, semantic law, and direct-TM compiler.
-/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def sharedGadget : CertifiedReduction sourceProblem targetProblem where
  program := sharedGadgetProgram
  correct := by
    intro input
    simpa [sourceProblem, targetProblem, sharedGadgetProgram, sharedGadgetPrimitive,
      executable_eq_readOnly] using
      (threeCNFToFormula_satisfiable_iff input).symm

@[simp] theorem sharedGadget_program :
    sharedGadget.program = sharedGadgetProgram :=
  rfl

/-- The final certificate projects direct-TM evidence only from its stored program. -/
@[simp] theorem sharedGadget_directTM :
    sharedGadget.directTM = sharedGadget.program.compileTM :=
  rfl

/-- The semantic law is indexed by the shared atom program. -/
theorem sharedGadget_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔ targetProblem.accepts (sharedGadgetProgram.run input) :=
  sharedGadget.correct input

/-- Only the exact shared-gadget request is accepted. -/
noncomputable def resolution :
    Protocol.ComponentResolution .sharedGadget sourceProblem targetProblem :=
  Protocol.ComponentResolver.accept request sharedGadget

@[simp] theorem resolution_exact :
    resolution = .accepted sharedGadget :=
  rfl

end ThreeSATToThreeSATLikeStandardTM
end Domain
end ComplexityReduction
