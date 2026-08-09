/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatPair
import ComplexityReduction.Legacy.ComplexityReduction.SAT.StructuredEncoding
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyBlocks
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyBoundsTM

/-!
Direct standard-TM witnesses for x-only Cook-Levin CNF block generators.

This file starts with reusable atom and unit-CNF constructors.  The x-only
block generators use only bounds and ranges computed from `x`; all fixed
verifier/tableau coordinates remain constants in the generated TM maps.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Tableau atom constructors -/

/-- A tableau variable with only the cell coordinate supplied as input is direct TM computable. -/
theorem tmVerifierTableauVar_cell_tm_polytime
    (kind : TMVerifierTableauVarKind) (time stack payload : Nat) :
    TMPolyTimeMap EncodedType.nat EncodedType.nat
      (fun cell : Nat => tmVerifierTableauVar kind time stack cell payload) := by
  have hCellPayload :
      TMPolyTimeMap EncodedType.nat EncodedType.nat
        (fun cell : Nat => Nat.pair cell payload) :=
    nat_pair_const_right_tm_polytime payload
  have hStackPayload :
      TMPolyTimeMap EncodedType.nat EncodedType.nat
        (fun cell : Nat => Nat.pair stack (Nat.pair cell payload)) := by
    have hComp := TMPolyTimeMap.comp (nat_pair_const_left_tm_polytime stack) hCellPayload
    simpa [Function.comp] using hComp
  have hTimePayload :
      TMPolyTimeMap EncodedType.nat EncodedType.nat
        (fun cell : Nat => Nat.pair time (Nat.pair stack (Nat.pair cell payload))) := by
    have hComp := TMPolyTimeMap.comp (nat_pair_const_left_tm_polytime time) hStackPayload
    simpa [Function.comp] using hComp
  have hVar :
      TMPolyTimeMap EncodedType.nat EncodedType.nat
        (fun cell : Nat =>
          Nat.pair kind.tag (Nat.pair time (Nat.pair stack (Nat.pair cell payload)))) := by
    have hComp := TMPolyTimeMap.comp (nat_pair_const_left_tm_polytime kind.tag) hTimePayload
    simpa [Function.comp] using hComp
  simpa [tmVerifierTableauVar] using hVar

/-- Positive tableau atoms with only the cell coordinate supplied as input are direct TM computable. -/
theorem tmVerifierTableauAtom_cell_tm_polytime
    (kind : TMVerifierTableauVarKind) (time stack payload : Nat) :
    TMPolyTimeMap EncodedType.nat literalStructuredEncodedType
      (fun cell : Nat => tmVerifierTableauAtom kind time stack cell payload) := by
  have hVar := tmVerifierTableauVar_cell_tm_polytime kind time stack payload
  have hLiteral := literalPositiveTMBackedMap.tm_polytime
  have hComp := TMPolyTimeMap.comp hLiteral hVar
  simpa [Function.comp, tmVerifierTableauAtom, Literal.positive] using hComp

/-- Negative tableau atoms with only the cell coordinate supplied as input are direct TM computable. -/
theorem negTMVerifierTableauAtom_cell_tm_polytime
    (kind : TMVerifierTableauVarKind) (time stack payload : Nat) :
    TMPolyTimeMap EncodedType.nat literalStructuredEncodedType
      (fun cell : Nat => negTMVerifierTableauAtom kind time stack cell payload) := by
  have hVar := tmVerifierTableauVar_cell_tm_polytime kind time stack payload
  have hLiteral := literalNegativeTMBackedMap.tm_polytime
  have hComp := TMPolyTimeMap.comp hLiteral hVar
  simpa [Function.comp, negTMVerifierTableauAtom, Literal.negative] using hComp

/-- Stack-empty atoms with only the cell coordinate supplied as input are direct TM computable. -/
theorem tmVerifierStackEmptyAtom_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap EncodedType.nat literalStructuredEncodedType
      (fun cell : Nat => tmVerifierStackEmptyAtom V t k cell) := by
  simpa [tmVerifierStackEmptyAtom] using
    tmVerifierTableauAtom_cell_tm_polytime
      TMVerifierTableauVarKind.stackEmpty t (tmVerifierStackCode V k) 0

/-- Stack-symbol atoms with only the cell coordinate supplied as input are direct TM computable. -/
theorem tmVerifierStackSymbolAtom_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) (payload : Nat) :
    TMPolyTimeMap EncodedType.nat literalStructuredEncodedType
      (fun cell : Nat => tmVerifierStackSymbolAtom V t k cell payload) := by
  simpa [tmVerifierStackSymbolAtom] using
    tmVerifierTableauAtom_cell_tm_polytime
      TMVerifierTableauVarKind.stackSymbol t (tmVerifierStackCode V k) payload

/-- Negated stack-empty atoms with only the cell coordinate supplied as input are direct TM computable. -/
theorem negTMVerifierStackEmptyAtom_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap EncodedType.nat literalStructuredEncodedType
      (fun cell : Nat => negTMVerifierStackEmptyAtom V t k cell) := by
  simpa [negTMVerifierStackEmptyAtom] using
    negTMVerifierTableauAtom_cell_tm_polytime
      TMVerifierTableauVarKind.stackEmpty t (tmVerifierStackCode V k) 0

/-- One read-choice atom with only the cell coordinate supplied as input is direct TM computable. -/
theorem tmVerifierStackReadChoice_atomAt_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V)
    (choice : TMVerifierStackReadChoice V k) :
    TMPolyTimeMap EncodedType.nat literalStructuredEncodedType
      (fun cell : Nat =>
        TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice) := by
  cases choice with
  | empty =>
      simpa [TMVerifierStackReadChoice.atomAt] using
        tmVerifierStackEmptyAtom_cell_tm_polytime V t k
  | symbol payload symbol =>
      simpa [TMVerifierStackReadChoice.atomAt] using
        tmVerifierStackSymbolAtom_cell_tm_polytime V t k payload

/-- The negation of one read-choice atom is direct TM computable from the cell coordinate. -/
theorem tmVerifierStackReadChoice_negAtomAt_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V)
    (choice : TMVerifierStackReadChoice V k) :
    TMPolyTimeMap EncodedType.nat literalStructuredEncodedType
      (fun cell : Nat =>
        Clause.negate (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice)) := by
  have hAtom := tmVerifierStackReadChoice_atomAt_cell_tm_polytime V t k choice
  have hNeg := literalNegateTMBackedMap.tm_polytime
  have hComp := TMPolyTimeMap.comp hNeg hAtom
  simpa [Function.comp] using hComp

theorem tmVerifierStackReadChoiceLiteralsFor_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V)
    (choices : List (TMVerifierStackReadChoice V k)) :
    TMPolyTimeMap EncodedType.nat (EncodedType.list literalStructuredEncodedType)
      (fun cell : Nat =>
        choices.map fun choice =>
          TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice) := by
  induction choices with
  | nil =>
      exact TMPolyTimeMap.const EncodedType.nat
        (EncodedType.list literalStructuredEncodedType) []
  | cons choice choices ih =>
      have hHead := tmVerifierStackReadChoice_atomAt_cell_tm_polytime V t k choice
      have hTail := ih
      have hConsInput :
          TMPolyTimeMap EncodedType.nat
            (EncodedType.prod literalStructuredEncodedType
              (EncodedType.list literalStructuredEncodedType))
            (fun cell : Nat =>
              (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice,
                choices.map fun choice =>
                  TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice)) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hCons := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons literalStructuredEncodedType)
        hConsInput
      simpa [Function.comp] using hCons

/-- Read-choice literals for one stack cell are direct TM computable from the cell coordinate. -/
theorem tmVerifierStackReadChoiceLiteralsAt_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap EncodedType.nat (EncodedType.list literalStructuredEncodedType)
      (fun cell : Nat => tmVerifierStackReadChoiceLiteralsAt V t k cell) := by
  simpa [tmVerifierStackReadChoiceLiteralsAt] using
    tmVerifierStackReadChoiceLiteralsFor_cell_tm_polytime V t k
      (tmVerifierStackReadChoices V k)

/-! ### Unit clause constructors -/

/-- Clause singleton construction is direct TM polynomial-time under structured encodings. -/
theorem literalSingletonClause_tm_polytime :
    TMPolyTimeMap literalStructuredEncodedType clauseStructuredEncodedType
      (fun l : Literal => [l]) :=
  TMPolyTimeMap.list_singleton literalStructuredEncodedType

/-- Unit-CNF construction is direct TM polynomial-time under structured encodings. -/
theorem tmVerifierUnitCNF_tm_polytime :
    TMPolyTimeMap literalStructuredEncodedType cnfStructuredEncodedType
      tmVerifierUnitCNF := by
  have hClause := literalSingletonClause_tm_polytime
  have hCNF := clauseSingletonTMBackedMap.tm_polytime
  have hComp := TMPolyTimeMap.comp hCNF hClause
  simpa [Function.comp, tmVerifierUnitCNF] using hComp

/-- Unit clauses for a list of literals are direct TM polynomial-time generated. -/
theorem tmVerifierUnitClauses_tm_polytime :
    TMPolyTimeMap (EncodedType.list literalStructuredEncodedType) cnfStructuredEncodedType
      tmVerifierUnitClauses := by
  have hMap := TMPolyTimeMap.list_map literalSingletonClause_tm_polytime
  simpa [tmVerifierUnitClauses, cnfStructuredEncodedType, clauseStructuredEncodedType] using hMap

/-- Two-literal clause construction is direct TM polynomial-time. -/
theorem literalPairClause_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
      clauseStructuredEncodedType
      (fun p : Literal × Literal => [p.1, p.2]) := by
  let X := EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType
  have hFirst : TMPolyTimeMap X literalStructuredEncodedType (fun p : Literal × Literal => p.1) := by
    simpa [X] using TMPolyTimeMap.fst literalStructuredEncodedType literalStructuredEncodedType
  have hSecond :
      TMPolyTimeMap X literalStructuredEncodedType (fun p : Literal × Literal => p.2) := by
    simpa [X] using TMPolyTimeMap.snd literalStructuredEncodedType literalStructuredEncodedType
  have hTail :
      TMPolyTimeMap X clauseStructuredEncodedType (fun p : Literal × Literal => [p.2]) := by
    have hComp := TMPolyTimeMap.comp literalSingletonClause_tm_polytime hSecond
    simpa [Function.comp, clauseStructuredEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod literalStructuredEncodedType clauseStructuredEncodedType)
        (fun p : Literal × Literal => (p.1, [p.2])) :=
    TMPolyTimeMap.prod_mk hFirst hTail
  have hClause := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons literalStructuredEncodedType)
    hConsInput
  simpa [Function.comp, clauseStructuredEncodedType, X] using hClause

theorem tmVerifierStackReadChoiceAtMostOneWithCNF_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V)
    (head : TMVerifierStackReadChoice V k)
    (tail : List (TMVerifierStackReadChoice V k)) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun cell : Nat =>
        CookLevin.atMostOneWithCNF
          (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell head)
          (tail.map fun choice =>
            TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice)) := by
  induction tail with
  | nil =>
      exact TMPolyTimeMap.const EncodedType.nat cnfStructuredEncodedType []
  | cons choice tail ih =>
      have hHeadNeg := tmVerifierStackReadChoice_negAtomAt_cell_tm_polytime V t k head
      have hChoiceNeg := tmVerifierStackReadChoice_negAtomAt_cell_tm_polytime V t k choice
      have hPair :
          TMPolyTimeMap EncodedType.nat
            (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
            (fun cell : Nat =>
              (Clause.negate
                  (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell head),
                Clause.negate
                  (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice))) :=
        TMPolyTimeMap.prod_mk hHeadNeg hChoiceNeg
      have hClause :
          TMPolyTimeMap EncodedType.nat clauseStructuredEncodedType
            (fun cell : Nat =>
              [Clause.negate
                  (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell head),
                Clause.negate
                  (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice)]) := by
        have hComp := TMPolyTimeMap.comp literalPairClause_tm_polytime hPair
        simpa [Function.comp] using hComp
      have hTail := ih
      have hConsInput :
          TMPolyTimeMap EncodedType.nat
            (EncodedType.prod clauseStructuredEncodedType cnfStructuredEncodedType)
            (fun cell : Nat =>
              ([Clause.negate
                  (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell head),
                Clause.negate
                  (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice)],
                CookLevin.atMostOneWithCNF
                  (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell head)
                  (tail.map fun choice =>
                    TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice))) :=
        TMPolyTimeMap.prod_mk hClause hTail
      have hCons := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons clauseStructuredEncodedType)
        hConsInput
      simpa [Function.comp, CookLevin.atMostOneWithCNF, cnfStructuredEncodedType,
        clauseStructuredEncodedType] using hCons

theorem tmVerifierStackReadChoiceAtMostOneCNF_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V)
    (choices : List (TMVerifierStackReadChoice V k)) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun cell : Nat =>
        CookLevin.atMostOneCNF
          (choices.map fun choice =>
            TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice)) := by
  induction choices with
  | nil =>
      exact TMPolyTimeMap.const EncodedType.nat cnfStructuredEncodedType []
  | cons choice choices ih =>
      have hWith := tmVerifierStackReadChoiceAtMostOneWithCNF_cell_tm_polytime
        V t k choice choices
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap EncodedType.nat
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun cell : Nat =>
              (CookLevin.atMostOneWithCNF
                (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice)
                (choices.map fun choice =>
                  TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice),
                CookLevin.atMostOneCNF
                  (choices.map fun choice =>
                    TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice))) :=
        TMPolyTimeMap.prod_mk hWith hTail
      have hAppend := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
        hAppendInput
      simpa [Function.comp, CookLevin.atMostOneCNF, cnfStructuredEncodedType] using hAppend

theorem tmVerifierStackReadChoiceExactlyOneCNF_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V)
    (choices : List (TMVerifierStackReadChoice V k)) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun cell : Nat =>
        CookLevin.exactlyOneCNF
          (choices.map fun choice =>
            TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice)) := by
  have hAtoms := tmVerifierStackReadChoiceLiteralsFor_cell_tm_polytime V t k choices
  have hAtLeast :
      TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
        (fun cell : Nat =>
          CookLevin.atLeastOneCNF
            (choices.map fun choice =>
              TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice)) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton clauseStructuredEncodedType)
      hAtoms
    simpa [Function.comp, CookLevin.atLeastOneCNF, cnfStructuredEncodedType,
      clauseStructuredEncodedType] using hComp
  have hAtMost := tmVerifierStackReadChoiceAtMostOneCNF_cell_tm_polytime V t k choices
  have hAppendInput :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun cell : Nat =>
          (CookLevin.atLeastOneCNF
            (choices.map fun choice =>
              TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice),
            CookLevin.atMostOneCNF
              (choices.map fun choice =>
                TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice))) :=
    TMPolyTimeMap.prod_mk hAtLeast hAtMost
  have hAppend := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
    hAppendInput
  simpa [Function.comp, CookLevin.exactlyOneCNF, cnfStructuredEncodedType] using hAppend

/-- One stack-cell domain CNF is direct TM computable from the cell coordinate. -/
theorem tmVerifierStackCellDomainCNFAt_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun cell : Nat => tmVerifierStackCellDomainCNFAt V t k cell) := by
  simpa [tmVerifierStackCellDomainCNFAt, tmVerifierStackReadChoiceDomainCNFAt,
    tmVerifierStackReadChoiceLiteralsAt] using
    tmVerifierStackReadChoiceExactlyOneCNF_cell_tm_polytime V t k
      (tmVerifierStackReadChoices V k)

/-! ### Cell-list folds for x-only domain rows -/

noncomputable def tmVerifierDomainCellFoldStep
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V)
    (p : CNF × Nat) : CNF :=
  (show CNF from p.1) ++ tmVerifierStackCellDomainCNFAt V t k p.2

noncomputable def tmVerifierDomainCellFold
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V)
    (cells : List Nat) : CNF :=
  cells.foldl (fun acc cell => tmVerifierDomainCellFoldStep V t k (acc, cell)) []

theorem tmVerifierDomainCellFoldWith_eq_append_flatMap
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V)
    (cells : List Nat) (out : CNF) :
    cells.foldl (fun acc cell => tmVerifierDomainCellFoldStep V t k (acc, cell)) out =
      out ++ cells.flatMap fun cell => tmVerifierStackCellDomainCNFAt V t k cell := by
  induction cells generalizing out with
  | nil =>
      simp
  | cons cell rest ih =>
      rw [List.foldl_cons]
      simpa [tmVerifierDomainCellFoldStep, List.append_assoc] using
        ih (out ++ tmVerifierStackCellDomainCNFAt V t k cell)

theorem tmVerifierDomainCellFold_eq_flatMap
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) (cells : List Nat) :
    tmVerifierDomainCellFold V t k cells =
      cells.flatMap fun cell => tmVerifierStackCellDomainCNFAt V t k cell := by
  simpa [tmVerifierDomainCellFold] using
    tmVerifierDomainCellFoldWith_eq_append_flatMap V t k cells []

theorem tmVerifierDomainCellFoldStep_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap
      (EncodedType.prod cnfStructuredEncodedType EncodedType.nat)
      cnfStructuredEncodedType
      (tmVerifierDomainCellFoldStep V t k) := by
  let X := EncodedType.prod cnfStructuredEncodedType EncodedType.nat
  have hAcc :
      TMPolyTimeMap X cnfStructuredEncodedType
        (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst cnfStructuredEncodedType EncodedType.nat
  have hCell :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd cnfStructuredEncodedType EncodedType.nat
  have hBlock :
      TMPolyTimeMap X cnfStructuredEncodedType
        (fun p : X.Carrier => tmVerifierStackCellDomainCNFAt V t k p.2) := by
    have hComp :=
      TMPolyTimeMap.comp (tmVerifierStackCellDomainCNFAt_cell_tm_polytime V t k) hCell
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun p : X.Carrier =>
          ((show CNF from p.1), tmVerifierStackCellDomainCNFAt V t k p.2)) :=
    TMPolyTimeMap.prod_mk hAcc hBlock
  have hAppend := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
    hAppendInput
  simpa [Function.comp, tmVerifierDomainCellFoldStep, cnfStructuredEncodedType, X]
    using hAppend

theorem tmVerifierDomainCellFold_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap
      (EncodedType.list EncodedType.nat)
      cnfStructuredEncodedType
      (tmVerifierDomainCellFold V t k) := by
  rcases tmVerifierDomainCellFoldStep_tm_polytime V t k with ⟨hStep⟩
  rcases tmVerifierStackCellDomainCNFAt_cell_tm_polytime V t k with ⟨hCellBlock⟩
  let grow : Polynomial Nat :=
    Polynomial.X +
      hCellBlock.time.comp Polynomial.X *
        Polynomial.C (TM2Programs.finTM2StepPushBound hCellBlock.tm)
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      EncodedType.nat cnfStructuredEncodedType
      (tmVerifierDomainCellFoldStep V t k) ([] : CNF) hStep
      (Polynomial.C 0) grow ?_ ?_
  · intro xs
    rw [show cnfStructuredEncodedType.inputSize ([] : CNF) = 0 by
      change (EncodedType.list clauseStructuredEncodedType).inputSize ([] : CNF) = 0
      exact EncodedType.inputSize_list_nil clauseStructuredEncodedType]
    simp
  · intro source acc cell hCellSize
    let N := (EncodedType.list EncodedType.nat).inputSize source
    let B := TM2Programs.finTM2StepPushBound hCellBlock.tm
    have hOut :=
      TM2Programs.tm2ComputableInPolyTime_output_length_le hCellBlock cell
    have hOutSize :
        cnfStructuredEncodedType.inputSize (tmVerifierStackCellDomainCNFAt V t k cell) ≤
          EncodedType.nat.inputSize cell +
            hCellBlock.time.eval (EncodedType.nat.inputSize cell) * B := by
      simpa [EncodedType.inputSize, B] using hOut
    have hTimeMono :
        hCellBlock.time.eval (EncodedType.nat.inputSize cell) ≤
          hCellBlock.time.eval N := by
      exact TM2Programs.polynomialNat_eval_mono hCellBlock.time (by simpa [N] using hCellSize)
    have hGrow :
        cnfStructuredEncodedType.inputSize (tmVerifierStackCellDomainCNFAt V t k cell) ≤
          grow.eval N := by
      have hBound :
          EncodedType.nat.inputSize cell +
              hCellBlock.time.eval (EncodedType.nat.inputSize cell) * B ≤
            N + hCellBlock.time.eval N * B := by
        nlinarith [hCellSize, hTimeMono, Nat.zero_le B]
      have hEval :
          grow.eval N =
            N + hCellBlock.time.eval N * B := by
        simp [grow, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, B]
      exact hOutSize.trans (by simpa [hEval] using hBound)
    have hAppend :
        cnfStructuredEncodedType.inputSize (tmVerifierDomainCellFoldStep V t k (acc, cell)) =
          cnfStructuredEncodedType.inputSize acc +
            cnfStructuredEncodedType.inputSize (tmVerifierStackCellDomainCNFAt V t k cell) := by
      simpa [tmVerifierDomainCellFoldStep, cnfStructuredEncodedType] using
        list_inputSize_append clauseStructuredEncodedType acc
          (tmVerifierStackCellDomainCNFAt V t k cell)
    calc
      cnfStructuredEncodedType.inputSize (tmVerifierDomainCellFoldStep V t k (acc, cell))
          =
        cnfStructuredEncodedType.inputSize acc +
          cnfStructuredEncodedType.inputSize (tmVerifierStackCellDomainCNFAt V t k cell) :=
          hAppend
      _ ≤ cnfStructuredEncodedType.inputSize acc + grow.eval
            ((EncodedType.list EncodedType.nat).inputSize source) :=
          Nat.add_le_add_left (by simpa [N] using hGrow) _

/-- Cell-domain clauses over the x-only bounded range are direct TM generated from `x`. -/
theorem tmVerifierXOnlyStackCellDomainsCNFAt_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier => tmVerifierXOnlyStackCellDomainsCNFAt V x t k) := by
  have hRange := tmVerifierXOnlyCellRange_tm_polytime V
  have hFold := tmVerifierDomainCellFold_tm_polytime V t k
  have hComp := TMPolyTimeMap.comp hFold hRange
  convert hComp using 1
  funext x
  simp [Function.comp, tmVerifierXOnlyStackCellDomainsCNFAt,
    tmVerifierDomainCellFold_eq_flatMap]

/-- The empty-tail implication clause for a fixed stack row is direct TM generated from `cell`. -/
theorem tmVerifierStackEmptyTailClause_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap EncodedType.nat clauseStructuredEncodedType
      (fun cell : Nat => tmVerifierStackEmptyTailClause V t k cell) := by
  have hNeg := negTMVerifierStackEmptyAtom_cell_tm_polytime V t k
  have hSucc :
      TMPolyTimeMap EncodedType.nat EncodedType.nat (fun cell : Nat => cell + 1) :=
    nat_add_const_tm_polytime 1
  have hNext :
      TMPolyTimeMap EncodedType.nat literalStructuredEncodedType
        (fun cell : Nat => tmVerifierStackEmptyAtom V t k (cell + 1)) := by
    have hComp := TMPolyTimeMap.comp (tmVerifierStackEmptyAtom_cell_tm_polytime V t k) hSucc
    simpa [Function.comp] using hComp
  have hPair :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
        (fun cell : Nat =>
          (negTMVerifierStackEmptyAtom V t k cell,
            tmVerifierStackEmptyAtom V t k (cell + 1))) :=
    TMPolyTimeMap.prod_mk hNeg hNext
  have hClause := TMPolyTimeMap.comp literalPairClause_tm_polytime hPair
  convert hClause using 1

/-! ### First x-only stack blocks -/

/-- The final-empty sentinel clause for a fixed stack row is direct TM generated from `x`. -/
theorem tmVerifierXOnlyStackFinalEmptyCNFAt_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier => tmVerifierXOnlyStackFinalEmptyCNFAt V x t k) := by
  have hBound := tmVerifierXOnlyCellBound_tm_polytime V
  have hAtom :
      TMPolyTimeMap L.Instance literalStructuredEncodedType
        (fun x : L.Instance.Carrier =>
          tmVerifierStackEmptyAtom V t k (tmVerifierXOnlyCellBound V x)) := by
    have hComp := TMPolyTimeMap.comp (tmVerifierStackEmptyAtom_cell_tm_polytime V t k) hBound
    simpa [Function.comp] using hComp
  have hCNF := TMPolyTimeMap.comp tmVerifierUnitCNF_tm_polytime hAtom
  simpa [Function.comp, tmVerifierXOnlyStackFinalEmptyCNFAt, tmVerifierUnitCNF] using hCNF

/-- Empty-tail monotonicity clauses for a fixed stack row are direct TM generated from `x`. -/
theorem tmVerifierXOnlyStackEmptyTailCNFAt_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier => tmVerifierXOnlyStackEmptyTailCNFAt V x t k) := by
  have hRange := tmVerifierXOnlyCellSuccessorRange_tm_polytime V
  have hMap := TMPolyTimeMap.list_map (tmVerifierStackEmptyTailClause_cell_tm_polytime V t k)
  have hComp := TMPolyTimeMap.comp hMap hRange
  simpa [Function.comp, tmVerifierXOnlyStackEmptyTailCNFAt, cnfStructuredEncodedType,
    clauseStructuredEncodedType] using hComp

/-- One x-only stack row well-formedness block is direct TM generated from `x`. -/
theorem tmVerifierXOnlyStackWellFormedCNFAt_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier => tmVerifierXOnlyStackWellFormedCNFAt V x t k) := by
  have hDomains := tmVerifierXOnlyStackCellDomainsCNFAt_tm_polytime V t k
  have hTail := tmVerifierXOnlyStackEmptyTailCNFAt_tm_polytime V t k
  have hFinal := tmVerifierXOnlyStackFinalEmptyCNFAt_tm_polytime V t k
  have hTailFinalInput :
      TMPolyTimeMap L.Instance
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun x : L.Instance.Carrier =>
          (tmVerifierXOnlyStackEmptyTailCNFAt V x t k,
            tmVerifierXOnlyStackFinalEmptyCNFAt V x t k)) :=
    TMPolyTimeMap.prod_mk hTail hFinal
  have hTailFinal :
      TMPolyTimeMap L.Instance cnfStructuredEncodedType
        (fun x : L.Instance.Carrier =>
          tmVerifierXOnlyStackEmptyTailCNFAt V x t k ++
            tmVerifierXOnlyStackFinalEmptyCNFAt V x t k) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
      hTailFinalInput
    simpa [Function.comp, cnfStructuredEncodedType] using hComp
  have hAllInput :
      TMPolyTimeMap L.Instance
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun x : L.Instance.Carrier =>
          (tmVerifierXOnlyStackCellDomainsCNFAt V x t k,
            tmVerifierXOnlyStackEmptyTailCNFAt V x t k ++
              tmVerifierXOnlyStackFinalEmptyCNFAt V x t k)) :=
    TMPolyTimeMap.prod_mk hDomains hTailFinal
  have hAll := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
    hAllInput
  simpa [Function.comp, tmVerifierXOnlyStackWellFormedCNFAt, cnfStructuredEncodedType]
    using hAll

theorem tmVerifierXOnlyStackWellFormedForList_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (ks : List (tmVerifierStackIndex V)) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier =>
        ks.flatMap fun k => tmVerifierXOnlyStackWellFormedCNFAt V x t k) := by
  induction ks with
  | nil =>
      exact TMPolyTimeMap.const L.Instance cnfStructuredEncodedType []
  | cons k ks ih =>
      have hHead := tmVerifierXOnlyStackWellFormedCNFAt_tm_polytime V t k
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap L.Instance
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun x : L.Instance.Carrier =>
              (tmVerifierXOnlyStackWellFormedCNFAt V x t k,
                ks.flatMap fun k => tmVerifierXOnlyStackWellFormedCNFAt V x t k)) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hAppend := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
        hAppendInput
      simpa [Function.comp, cnfStructuredEncodedType] using hAppend

/-- X-only well-formedness for every fixed stack at one time row is direct TM generated. -/
theorem tmVerifierXOnlyAllStackWellFormedCNFAt_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier => tmVerifierXOnlyAllStackWellFormedCNFAt V x t) := by
  simpa [tmVerifierXOnlyAllStackWellFormedCNFAt] using
    tmVerifierXOnlyStackWellFormedForList_tm_polytime V t (tmVerifierStackList V)

end SAT
end ComplexityReduction
