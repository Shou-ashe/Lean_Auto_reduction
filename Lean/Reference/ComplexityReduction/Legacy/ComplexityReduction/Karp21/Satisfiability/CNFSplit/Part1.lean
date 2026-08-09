/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.SplitWith

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction
open Turing.TM2.Stmt

/--
TM-friendly CNF splitter target: use the source structured input length as the
first fresh variable.  This bound is directly writable by a TM and is already
proved above all variables occurring in the source CNF.
-/
def cnfSplitFromStructuredBoundToThreeCNF (φ : SAT.CNF) : SAT.ThreeCNF where
  clauses := SAT.CNF.splitAux (cnfStructuredEncodedType.inputSize φ) φ
  isThree := SAT.CNF.splitAux_isThreeCNF (cnfStructuredEncodedType.inputSize φ) φ

theorem cnfSplitFromStructuredBound_satisfiable_iff (φ : SAT.CNF) :
    SAT.ThreeCNF.Satisfiable (cnfSplitFromStructuredBoundToThreeCNF φ) ↔
      SAT.CNF.Satisfiable φ := by
  constructor
  · rintro ⟨a, hSat⟩
    exact ⟨a, SAT.CNF.splitAux_project (cnfStructuredEncodedType.inputSize φ) φ a hSat⟩
  · rintro ⟨a, hSat⟩
    have hBound : ∀ c ∈ φ, ∀ l ∈ c, l.var < cnfStructuredEncodedType.inputSize φ := by
      intro c hc l hl
      exact lt_of_lt_of_le (SAT.CNF.clause_vars_lt_varBound hc l hl)
        (cnfVarBound_le_cnfStructured_inputSize φ)
    rcases SAT.CNF.splitAux_extend (cnfStructuredEncodedType.inputSize φ) φ a hBound hSat with
      ⟨b, _hbPres, hbSat⟩
    exact ⟨b, hbSat⟩

theorem cnfSplitFromStructuredBound_polynomialSizeBound :
    PolynomialSizeBound
      (fun φ : SAT.CNF => cnfStructuredEncodedType.inputSize φ)
      (fun ψ : SAT.ThreeCNF => threeCNFStructuredEncodedType.inputSize ψ)
      cnfSplitFromStructuredBoundToThreeCNF := by
  refine PolynomialSizeBound.intro_with 2 1000 1000 ?_
  intro φ
  let S := cnfStructuredEncodedType.inputSize φ
  have hBound : ∀ c ∈ φ, ∀ l ∈ c, l.var < S := by
    intro c hc l hl
    exact lt_of_lt_of_le (SAT.CNF.clause_vars_lt_varBound hc l hl)
      (by simpa [S] using cnfVarBound_le_cnfStructured_inputSize φ)
  have hEncode :=
    SAT.CNF.splitAux_encodedLength_le S φ hBound
  have hStruct :
      threeCNFStructuredEncodedType.inputSize (cnfSplitFromStructuredBoundToThreeCNF φ) ≤
        (SAT.ThreeSATEncoding.encodeCNF
          (SAT.CNF.splitAux (cnfStructuredEncodedType.inputSize φ) φ)).length := by
    simpa [cnfSplitFromStructuredBoundToThreeCNF, threeCNFStructuredEncodedType,
      EncodedType.inputSize, SAT.ThreeSATEncoding.encodeCNF] using
      cnfStructured_inputSize_le_encodeCNF_length
        (SAT.CNF.splitAux (cnfStructuredEncodedType.inputSize φ) φ)
  have hTotal := cnfStructured_inputSize_ge_totalClauseLength_add_length φ
  calc
    threeCNFStructuredEncodedType.inputSize (cnfSplitFromStructuredBoundToThreeCNF φ)
        ≤ (SAT.ThreeSATEncoding.encodeCNF
          (SAT.CNF.splitAux (cnfStructuredEncodedType.inputSize φ) φ)).length := hStruct
    _ ≤ (SAT.CNF.totalClauseLength φ + φ.length) *
          (1 + 3 * (S + SAT.CNF.totalClauseLength φ + 5)) := by
            simpa [S] using hEncode
    _ ≤ S * (1 + 3 * (S + S + 5)) := by
          have hTotalLe : SAT.CNF.totalClauseLength φ + φ.length ≤ S := by
            simpa [S] using hTotal
          have hFactor :
              1 + 3 * (S + SAT.CNF.totalClauseLength φ + 5) ≤
                1 + 3 * (S + S + 5) := by
            nlinarith [hTotalLe]
          exact Nat.mul_le_mul hTotalLe hFactor
    _ ≤ 1000 * S ^ 2 + 1000 := by
          nlinarith [sq_nonneg (S : Int)]

/-- CNF-level splitting accumulator `(nextFresh, emittedClauses)`. -/
def cnfSplitFoldAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat cnfStructuredEncodedType

/-- CNF-level runner instruction: initialize the fresh bound, then consume clauses. -/
def cnfSplitInstructionEncodedType : EncodedType :=
  EncodedType.sum EncodedType.nat clauseStructuredEncodedType

def cnfSplitRunnerInstructions (φ : SAT.CNF) :
    List cnfSplitInstructionEncodedType.Carrier :=
  Sum.inl (cnfStructuredEncodedType.inputSize φ) :: φ.map (fun c => Sum.inr c)

def cnfSplitFoldRightStep
    (p : cnfSplitFoldAccEncodedType.Carrier × clauseStructuredEncodedType.Carrier) :
    cnfSplitFoldAccEncodedType.Carrier := by
  rcases p with ⟨⟨next, out⟩, c⟩
  change Nat at next
  change SAT.CNF at out
  exact (next + c.length, out ++ SAT.Clause.splitWith next c)

def cnfSplitFoldRightSplitInput
    (p : (EncodedType.prod cnfSplitFoldAccEncodedType clauseStructuredEncodedType).Carrier) :
    splitWithInputEncodedType.Carrier := by
  rcases p with ⟨⟨next, _out⟩, c⟩
  change Nat at next
  exact (next, c)

def cnfSplitFoldRightAppendOutput
    (p : (EncodedType.prod cnfSplitFoldAccEncodedType clauseStructuredEncodedType).Carrier) :
    cnfStructuredEncodedType.Carrier := by
  rcases p with ⟨⟨next, out⟩, c⟩
  change Nat at next
  change SAT.CNF at out
  exact out ++ SAT.Clause.splitWith next c

theorem cnfSplitFoldRightStep_eq_pair
    (p : (EncodedType.prod cnfSplitFoldAccEncodedType clauseStructuredEncodedType).Carrier) :
    cnfSplitFoldRightStep p =
      (splitWithNextAfterClause (cnfSplitFoldRightSplitInput p),
        cnfSplitFoldRightAppendOutput p) := by
  rcases p with ⟨⟨next, out⟩, c⟩
  rfl

theorem cnfSplitFoldRightStep_inputSize_le
    (p : (EncodedType.prod cnfSplitFoldAccEncodedType clauseStructuredEncodedType).Carrier) :
    cnfSplitFoldAccEncodedType.inputSize (cnfSplitFoldRightStep p) ≤
      100 *
          ((EncodedType.prod cnfSplitFoldAccEncodedType clauseStructuredEncodedType).inputSize p) ^
            2 +
        100 := by
  rcases p with ⟨⟨next, out⟩, c⟩
  change Nat at next
  change SAT.CNF at out
  let N :=
    (EncodedType.prod cnfSplitFoldAccEncodedType clauseStructuredEncodedType).inputSize
      ((next, out), c)
  have hLen := clauseStructured_inputSize_ge_length c
  have hSplit := splitWith_structured_inputSize_le_quadratic next c
  have hNextClause :
      next + clauseStructuredEncodedType.inputSize c + 1 ≤ N := by
    simp [N, cnfSplitFoldAccEncodedType, EncodedType.inputSize, EncodedType.prod,
      EncodedType.nat]
  have hNextLen : next + c.length + 1 ≤ N := by
    have hLocal : next + c.length + 1 ≤
        next + clauseStructuredEncodedType.inputSize c + 1 := by
      simpa [Nat.add_assoc] using
        Nat.succ_le_succ (Nat.add_le_add_left hLen next)
    exact le_trans hLocal hNextClause
  have hOutLe : cnfStructuredEncodedType.inputSize out ≤ N := by
    simp [N, cnfSplitFoldAccEncodedType, EncodedType.inputSize, EncodedType.prod,
      EncodedType.nat]
    omega
  have hPow :
      (next + clauseStructuredEncodedType.inputSize c + 1) ^ 2 ≤ N ^ 2 :=
    Nat.pow_le_pow_left hNextClause 2
  have hAppendSize :
      cnfStructuredEncodedType.inputSize (out ++ SAT.Clause.splitWith next c) =
        cnfStructuredEncodedType.inputSize out +
          cnfStructuredEncodedType.inputSize (SAT.Clause.splitWith next c) := by
    simpa [cnfStructuredEncodedType] using
      encodedList_inputSize_append clauseStructuredEncodedType out (SAT.Clause.splitWith next c)
  change
    cnfSplitFoldAccEncodedType.inputSize
      (cnfSplitFoldRightStep (((next, out), c) :
        cnfSplitFoldAccEncodedType.Carrier × clauseStructuredEncodedType.Carrier)) ≤
      100 * N ^ 2 + 100
  simp only [cnfSplitFoldRightStep, cnfSplitFoldAccEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat]
  change
    next + c.length + 1 + 1 +
        cnfStructuredEncodedType.inputSize (out ++ SAT.Clause.splitWith next c) ≤
      100 * N ^ 2 + 100
  rw [hAppendSize]
  calc
    next + c.length + 1 + 1 +
          (cnfStructuredEncodedType.inputSize out +
            cnfStructuredEncodedType.inputSize (SAT.Clause.splitWith next c))
        ≤ N + 1 + (N + 20 * (next + clauseStructuredEncodedType.inputSize c + 1) ^ 2) := by
          omega
    _ ≤ N + 1 + (N + 20 * N ^ 2) := by
          exact Nat.add_le_add_left
            (Nat.add_le_add_left (Nat.mul_le_mul_left 20 hPow) N) (N + 1)
    _ ≤ 100 * N ^ 2 + 100 := by
          nlinarith [sq_nonneg (N : Int)]

theorem cnfSplitFoldRightStep_polynomialSizeBound :
    PolynomialSizeBound
      (fun p : (EncodedType.prod cnfSplitFoldAccEncodedType clauseStructuredEncodedType).Carrier =>
        (EncodedType.prod cnfSplitFoldAccEncodedType clauseStructuredEncodedType).inputSize p)
      (fun a : cnfSplitFoldAccEncodedType.Carrier => cnfSplitFoldAccEncodedType.inputSize a)
      cnfSplitFoldRightStep := by
  refine PolynomialSizeBound.intro_with 2 100 100 ?_
  intro p
  exact cnfSplitFoldRightStep_inputSize_le p

noncomputable def cnfSplitFoldRightStepTMBackedMap :
    TMBackedCostedMap
      (EncodedType.prod cnfSplitFoldAccEncodedType clauseStructuredEncodedType)
      cnfSplitFoldAccEncodedType
      cnfSplitFoldRightStep where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound cnfSplitFoldRightStep_polynomialSizeBound
  tm_polytime := by
    let X := EncodedType.prod cnfSplitFoldAccEncodedType clauseStructuredEncodedType
    have hAcc :
        TMPolyTimeMap X cnfSplitFoldAccEncodedType
          (fun p : X.Carrier => p.1) :=
      TMPolyTimeMap.fst cnfSplitFoldAccEncodedType clauseStructuredEncodedType
    have hClause :
        TMPolyTimeMap X clauseStructuredEncodedType
          (fun p : X.Carrier => p.2) :=
      TMPolyTimeMap.snd cnfSplitFoldAccEncodedType clauseStructuredEncodedType
    have hNext :
        TMPolyTimeMap X EncodedType.nat
          (fun p : X.Carrier => p.1.1) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.fst EncodedType.nat cnfStructuredEncodedType)
        hAcc
    have hOut :
        TMPolyTimeMap X cnfStructuredEncodedType
          (fun p : X.Carrier => p.1.2) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.snd EncodedType.nat cnfStructuredEncodedType)
        hAcc
    have hSplitInput :
        TMPolyTimeMap X splitWithInputEncodedType
          cnfSplitFoldRightSplitInput :=
      by
        have hPair := TMPolyTimeMap.prod_mk hNext hClause
        simpa [cnfSplitFoldRightSplitInput] using hPair
    have hNextAfter :
        TMPolyTimeMap X EncodedType.nat
          (fun p : X.Carrier => splitWithNextAfterClause (cnfSplitFoldRightSplitInput p)) :=
      by
        have hComp :=
          TMPolyTimeMap.comp splitWithNextAfterClauseTMBackedMap.tm_polytime hSplitInput
        simpa [Function.comp] using hComp
    have hSplit :
        TMPolyTimeMap X cnfStructuredEncodedType
          (fun p : X.Carrier =>
            SAT.Clause.splitWith (cnfSplitFoldRightSplitInput p).1
              (cnfSplitFoldRightSplitInput p).2) :=
      by
        have hComp := TMPolyTimeMap.comp splitWithInputTMBackedMap.tm_polytime hSplitInput
        simpa [Function.comp] using hComp
    have hAppendInput :
        TMPolyTimeMap X
          (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
          (fun p : X.Carrier =>
            (p.1.2, SAT.Clause.splitWith (cnfSplitFoldRightSplitInput p).1
              (cnfSplitFoldRightSplitInput p).2)) :=
      TMPolyTimeMap.prod_mk hOut hSplit
    have hAppend :
        TMPolyTimeMap X cnfStructuredEncodedType
          cnfSplitFoldRightAppendOutput :=
      by
        have hComp :=
          TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
        simpa [Function.comp, cnfSplitFoldRightAppendOutput] using hComp
    have hFinal :
        TMPolyTimeMap X cnfSplitFoldAccEncodedType cnfSplitFoldRightStep :=
      by
        have hPair := TMPolyTimeMap.prod_mk hNextAfter hAppend
        simpa [cnfSplitFoldRightStep_eq_pair] using hPair
    simpa [X] using hFinal

abbrev cnfSplitFoldStepInputEncodedType : EncodedType :=
  EncodedType.prod cnfSplitFoldAccEncodedType cnfSplitInstructionEncodedType

abbrev cnfSplitFoldStepRightPayloadEncodedType : EncodedType :=
  EncodedType.prod cnfSplitFoldAccEncodedType clauseStructuredEncodedType

def cnfSplitFoldStepChoiceEncodedType : EncodedType :=
  EncodedType.sum EncodedType.nat cnfSplitFoldStepRightPayloadEncodedType

def cnfSplitFoldStepChoice (p : cnfSplitFoldStepInputEncodedType.Carrier) :
    cnfSplitFoldStepChoiceEncodedType.Carrier :=
  match p.2 with
  | Sum.inl next => Sum.inl next
  | Sum.inr c => Sum.inr (p.1, c)

def cnfSplitFoldStepChoiceDispatch (q : cnfSplitFoldStepChoiceEncodedType.Carrier) :
    cnfSplitFoldAccEncodedType.Carrier :=
  match q with
  | Sum.inl next => (next, ([] : SAT.CNF))
  | Sum.inr p => cnfSplitFoldRightStep p

theorem cnfSplitFoldStepChoiceDispatch_inputSize_le
    (q : cnfSplitFoldStepChoiceEncodedType.Carrier) :
    cnfSplitFoldAccEncodedType.inputSize (cnfSplitFoldStepChoiceDispatch q) ≤
      100 * cnfSplitFoldStepChoiceEncodedType.inputSize q ^ 2 + 100 := by
  cases q with
  | inl next =>
      change Nat at next
      simp [cnfSplitFoldStepChoiceDispatch, cnfSplitFoldStepChoiceEncodedType,
        cnfSplitFoldAccEncodedType, cnfStructuredEncodedType, EncodedType.inputSize,
        EncodedType.prod, EncodedType.sum, EncodedType.nat, EncodedType.list]
      change next + 1 + 1 ≤ 100 * (next + 1 + 1) ^ 2 + 100
      have hsq : next + 1 + 1 ≤ (next + 1 + 1) ^ 2 := by
        have hpos : 1 ≤ next + 1 + 1 := by omega
        rw [pow_two]
        nth_rewrite 1 [← Nat.mul_one (next + 1 + 1)]
        exact Nat.mul_le_mul_left (next + 1 + 1) hpos
      exact le_trans hsq (by omega)
  | inr p =>
      have h := cnfSplitFoldRightStep_inputSize_le p
      let N := (cnfSplitFoldStepRightPayloadEncodedType.encode p).length
      have hN :
          cnfSplitFoldAccEncodedType.inputSize (cnfSplitFoldRightStep p) ≤
            100 * N ^ 2 + 100 := by
        simpa [N, cnfSplitFoldStepRightPayloadEncodedType, EncodedType.inputSize] using h
      have hPow : N ^ 2 ≤ (N + 1) ^ 2 :=
        Nat.pow_le_pow_left (Nat.le_succ N) 2
      have hGrow : 100 * N ^ 2 + 100 ≤ 100 * (N + 1) ^ 2 + 100 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 100 hPow) 100
      exact le_trans hN (by
        simpa [N, cnfSplitFoldStepChoiceDispatch, cnfSplitFoldStepChoiceEncodedType,
          cnfSplitFoldStepRightPayloadEncodedType, EncodedType.inputSize,
          EncodedType.sum] using hGrow)

noncomputable def cnfSplitFoldStepInitBranchTMBackedMap :
    TMBackedCostedMap
      EncodedType.nat
      cnfSplitFoldAccEncodedType
      (fun next : Nat => (next, ([] : SAT.CNF))) := by
  simpa [cnfSplitFoldAccEncodedType] using
    (TMBackedCostedMap.prodIdConstEmptyRight
      EncodedType.nat cnfStructuredEncodedType ([] : SAT.CNF)
      (by rfl))

abbrev cnfSplitFoldStepChoicePayloadSymbol :=
  EncodedType.nat.Symbol ⊕ cnfSplitFoldStepRightPayloadEncodedType.Symbol

def cnfSplitFoldStepChoiceLeftPayloadEncodedType : EncodedType where
  Carrier := EncodedType.nat.Carrier
  Symbol := cnfSplitFoldStepChoicePayloadSymbol
  finite_symbol := inferInstance
  encode := fun next => (EncodedType.nat.encode next).map Sum.inl

def cnfSplitFoldStepChoiceRightPayloadEncodedType : EncodedType where
  Carrier := cnfSplitFoldStepRightPayloadEncodedType.Carrier
  Symbol := cnfSplitFoldStepChoicePayloadSymbol
  finite_symbol := inferInstance
  encode := fun p => (cnfSplitFoldStepRightPayloadEncodedType.encode p).map Sum.inr

def cnfSplitFoldStepChoiceLeftPayloadKeep :
    cnfSplitFoldStepChoicePayloadSymbol → Option EncodedType.nat.Symbol
  | Sum.inl s => some s
  | Sum.inr _ => none

def cnfSplitFoldStepChoiceRightPayloadKeep :
    cnfSplitFoldStepChoicePayloadSymbol →
      Option cnfSplitFoldStepRightPayloadEncodedType.Symbol
  | Sum.inl _ => none
  | Sum.inr s => some s

theorem cnfSplitFoldStepChoiceLeftPayload_encode_filterMap (next : Nat) :
    (cnfSplitFoldStepChoiceLeftPayloadEncodedType.encode next).filterMap
        cnfSplitFoldStepChoiceLeftPayloadKeep =
      EncodedType.nat.encode next := by
  simp [cnfSplitFoldStepChoiceLeftPayloadEncodedType,
    cnfSplitFoldStepChoiceLeftPayloadKeep]

theorem cnfSplitFoldStepChoiceRightPayload_encode_filterMap
    (p : cnfSplitFoldStepRightPayloadEncodedType.Carrier) :
    (cnfSplitFoldStepChoiceRightPayloadEncodedType.encode p).filterMap
        cnfSplitFoldStepChoiceRightPayloadKeep =
      cnfSplitFoldStepRightPayloadEncodedType.encode p := by
  simp [cnfSplitFoldStepChoiceRightPayloadEncodedType,
    cnfSplitFoldStepChoiceRightPayloadKeep]

noncomputable def cnfSplitFoldStepChoiceLeftPayloadForgetTMBackedMap :
    TMBackedCostedMap
      cnfSplitFoldStepChoiceLeftPayloadEncodedType
      EncodedType.nat
      id where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := cnfSplitFoldStepChoiceLeftPayloadEncodedType)
      (Y := EncodedType.nat)
      (LinearSizeBound.intro_with 1 0 (by
        intro next
        rw [EncodedType.inputSize, EncodedType.inputSize]
        change (EncodedType.nat.encode next).length ≤
          1 * (cnfSplitFoldStepChoiceLeftPayloadEncodedType.encode next).length + 0
        rw [← cnfSplitFoldStepChoiceLeftPayload_encode_filterMap next]
        have h := List.length_filterMap_le cnfSplitFoldStepChoiceLeftPayloadKeep
          (cnfSplitFoldStepChoiceLeftPayloadEncodedType.encode next)
        simpa using h))
  tm_polytime :=
    ⟨{ tm :=
          TM2Programs.filterMapMachine
            cnfSplitFoldStepChoiceLeftPayloadEncodedType.Symbol
            EncodedType.nat.Symbol
            cnfSplitFoldStepChoiceLeftPayloadKeep
       inputAlphabet := Equiv.refl _
       outputAlphabet := Equiv.refl _
       time := 4 * Polynomial.X + 2
       outputsFun := by
        intro next
        change Turing.TM2OutputsInTime
          (TM2Programs.filterMapMachine
            cnfSplitFoldStepChoiceLeftPayloadEncodedType.Symbol
            EncodedType.nat.Symbol
            cnfSplitFoldStepChoiceLeftPayloadKeep)
          (List.map id (cnfSplitFoldStepChoiceLeftPayloadEncodedType.encode next))
          (some (List.map id (EncodedType.nat.encode next)))
          ((4 * Polynomial.X + 2).eval
            (cnfSplitFoldStepChoiceLeftPayloadEncodedType.encode next).length)
        have hOut :=
          TM2Programs.filterMap_outputs
            cnfSplitFoldStepChoiceLeftPayloadEncodedType.Symbol
            EncodedType.nat.Symbol
            cnfSplitFoldStepChoiceLeftPayloadKeep
            (cnfSplitFoldStepChoiceLeftPayloadEncodedType.encode next)
        convert hOut using 1
        · simp
        · simp [List.map_id]
          exact (cnfSplitFoldStepChoiceLeftPayload_encode_filterMap next).symm
        · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] }⟩

noncomputable def cnfSplitFoldStepChoiceRightPayloadForgetTMBackedMap :
    TMBackedCostedMap
      cnfSplitFoldStepChoiceRightPayloadEncodedType
      cnfSplitFoldStepRightPayloadEncodedType
      id where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := cnfSplitFoldStepChoiceRightPayloadEncodedType)
      (Y := cnfSplitFoldStepRightPayloadEncodedType)
      (LinearSizeBound.intro_with 1 0 (by
        intro p
        rw [EncodedType.inputSize, EncodedType.inputSize]
        change (cnfSplitFoldStepRightPayloadEncodedType.encode p).length ≤
          1 * (cnfSplitFoldStepChoiceRightPayloadEncodedType.encode p).length + 0
        rw [← cnfSplitFoldStepChoiceRightPayload_encode_filterMap p]
        have h := List.length_filterMap_le cnfSplitFoldStepChoiceRightPayloadKeep
          (cnfSplitFoldStepChoiceRightPayloadEncodedType.encode p)
        simpa using h))
  tm_polytime :=
    ⟨{ tm :=
          TM2Programs.filterMapMachine
            cnfSplitFoldStepChoiceRightPayloadEncodedType.Symbol
            cnfSplitFoldStepRightPayloadEncodedType.Symbol
            cnfSplitFoldStepChoiceRightPayloadKeep
       inputAlphabet := Equiv.refl _
       outputAlphabet := Equiv.refl _
       time := 4 * Polynomial.X + 2
       outputsFun := by
        intro p
        change Turing.TM2OutputsInTime
          (TM2Programs.filterMapMachine
            cnfSplitFoldStepChoiceRightPayloadEncodedType.Symbol
            cnfSplitFoldStepRightPayloadEncodedType.Symbol
            cnfSplitFoldStepChoiceRightPayloadKeep)
          (List.map id (cnfSplitFoldStepChoiceRightPayloadEncodedType.encode p))
          (some (List.map id (cnfSplitFoldStepRightPayloadEncodedType.encode p)))
          ((4 * Polynomial.X + 2).eval
            (cnfSplitFoldStepChoiceRightPayloadEncodedType.encode p).length)
        have hOut :=
          TM2Programs.filterMap_outputs
            cnfSplitFoldStepChoiceRightPayloadEncodedType.Symbol
            cnfSplitFoldStepRightPayloadEncodedType.Symbol
            cnfSplitFoldStepChoiceRightPayloadKeep
            (cnfSplitFoldStepChoiceRightPayloadEncodedType.encode p)
        convert hOut using 1
        · simp
        · simp [List.map_id]
          exact (cnfSplitFoldStepChoiceRightPayload_encode_filterMap p).symm
        · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] }⟩

noncomputable def cnfSplitFoldStepChoiceDispatchTMBackedMap :
    TMBackedCostedMap
      cnfSplitFoldStepChoiceEncodedType
      cnfSplitFoldAccEncodedType
      cnfSplitFoldStepChoiceDispatch where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      (PolynomialSizeBound.intro_with 2 100 100 (by
        intro q
        exact cnfSplitFoldStepChoiceDispatch_inputSize_le q))
  tm_polytime := by
    have hLeftInit :
        TMPolyTimeMap
          EncodedType.nat
          cnfSplitFoldAccEncodedType
          (fun next : Nat => (next, ([] : SAT.CNF))) :=
      cnfSplitFoldStepInitBranchTMBackedMap.tm_polytime
    have hLeftForget :
        TMPolyTimeMap
          cnfSplitFoldStepChoiceLeftPayloadEncodedType
          EncodedType.nat
          (fun next : Nat => next) :=
      cnfSplitFoldStepChoiceLeftPayloadForgetTMBackedMap.tm_polytime
    have hLeftMap :
        TMPolyTimeMap
          cnfSplitFoldStepChoiceLeftPayloadEncodedType
          cnfSplitFoldAccEncodedType
          (fun next : Nat => (next, ([] : SAT.CNF))) := by
      have hComp := TMPolyTimeMap.comp hLeftInit hLeftForget
      simpa [Function.comp] using hComp
    have hRightStep :
        TMPolyTimeMap
          cnfSplitFoldStepRightPayloadEncodedType
          cnfSplitFoldAccEncodedType
          cnfSplitFoldRightStep :=
      cnfSplitFoldRightStepTMBackedMap.tm_polytime
    have hRightForget :
        TMPolyTimeMap
          cnfSplitFoldStepChoiceRightPayloadEncodedType
          cnfSplitFoldStepRightPayloadEncodedType
          (fun p : cnfSplitFoldStepRightPayloadEncodedType.Carrier => p) :=
      cnfSplitFoldStepChoiceRightPayloadForgetTMBackedMap.tm_polytime
    have hRightMap :
        TMPolyTimeMap
          cnfSplitFoldStepChoiceRightPayloadEncodedType
          cnfSplitFoldAccEncodedType
          cnfSplitFoldRightStep := by
      have hComp := TMPolyTimeMap.comp hRightStep hRightForget
      simpa [Function.comp] using hComp
    rcases hLeftMap with ⟨hLeft⟩
    rcases hRightMap with ⟨hRight⟩
    refine ⟨?_⟩
    convert taggedBranchDispatchComputableInPolyTime hLeft hRight using 1
    · funext q
      cases q <;>
        simp [cnfSplitFoldStepChoiceEncodedType,
          cnfSplitFoldStepChoiceLeftPayloadEncodedType,
          cnfSplitFoldStepChoiceRightPayloadEncodedType, EncodedType.sum]
    · funext q
      cases q <;> rfl

inductive CNFSplitFoldStepChoiceStack where
  | input
  | output
  | temp
  deriving DecidableEq, Fintype

abbrev cnfSplitFoldStepChoiceInputSymbol :=
  cnfSplitFoldStepInputEncodedType.Symbol

abbrev cnfSplitFoldStepChoiceOutputSymbol :=
  cnfSplitFoldStepChoiceEncodedType.Symbol

abbrev cnfSplitFoldStepChoiceMachineAlphabet :
    CNFSplitFoldStepChoiceStack → Type
  | .input => cnfSplitFoldStepChoiceInputSymbol
  | .output => cnfSplitFoldStepChoiceOutputSymbol
  | .temp => cnfSplitFoldStepChoiceOutputSymbol

inductive CNFSplitFoldStepChoiceLabel where
  | readAcc
  | pushAccTemp (s : cnfSplitFoldStepChoiceOutputSymbol)
  | pushLeftTemp (s : cnfSplitFoldStepChoiceOutputSymbol)
  | pushRightTemp (s : cnfSplitFoldStepChoiceOutputSymbol)
  | readInstructionTag
  | clearAcc
  | readLeftPayload
  | pushRightDelimiter
  | readRightPayload
  | moveTemp (tag : Bool)
  | pushOutput (tag : Bool) (s : cnfSplitFoldStepChoiceOutputSymbol)
  | writeTag (tag : Bool)
  | invalid
  deriving Fintype

inductive CNFSplitFoldStepChoiceState where
  | input (head : Option cnfSplitFoldStepChoiceInputSymbol)
  | output (head : Option cnfSplitFoldStepChoiceOutputSymbol)
  deriving Fintype

def cnfSplitFoldStepChoiceInputState :
    CNFSplitFoldStepChoiceState → Option cnfSplitFoldStepChoiceInputSymbol
  | .input head => head
  | _ => none

def cnfSplitFoldStepChoiceOutputState :
    CNFSplitFoldStepChoiceState → Option cnfSplitFoldStepChoiceOutputSymbol
  | .output head => head
  | _ => none

def cnfSplitFoldStepChoiceAccOutputSymbol
    (s : cnfSplitFoldAccEncodedType.Symbol) :
    cnfSplitFoldStepChoiceOutputSymbol :=
  Sum.inr (Sum.inr (some (Sum.inl s)))

def cnfSplitFoldStepChoiceRightDelimiter :
    cnfSplitFoldStepChoiceOutputSymbol :=
  Sum.inr (Sum.inr none)

def cnfSplitFoldStepChoiceNatOutputSymbol
    (s : EncodedType.nat.Symbol) :
    cnfSplitFoldStepChoiceOutputSymbol :=
  Sum.inr (Sum.inl s)

def cnfSplitFoldStepChoiceClauseOutputSymbol
    (s : clauseStructuredEncodedType.Symbol) :
    cnfSplitFoldStepChoiceOutputSymbol :=
  Sum.inr (Sum.inr (some (Sum.inr s)))

def cnfSplitFoldStepChoiceAccInputSymbol
    (s : cnfSplitFoldAccEncodedType.Symbol) :
    cnfSplitFoldStepChoiceInputSymbol :=
  some (Sum.inl s)

def cnfSplitFoldStepChoiceInstructionTagInputSymbol
    (tag : Bool) :
    cnfSplitFoldStepChoiceInputSymbol :=
  some (Sum.inr (Sum.inl tag))

def cnfSplitFoldStepChoiceNatPayloadInputSymbol
    (s : EncodedType.nat.Symbol) :
    cnfSplitFoldStepChoiceInputSymbol :=
  some (Sum.inr (Sum.inr (Sum.inl s)))

def cnfSplitFoldStepChoiceClausePayloadInputSymbol
    (s : clauseStructuredEncodedType.Symbol) :
    cnfSplitFoldStepChoiceInputSymbol :=
  some (Sum.inr (Sum.inr (Sum.inr s)))

def cnfSplitFoldStepChoiceMachine : Turing.FinTM2 where
  K := CNFSplitFoldStepChoiceStack
  k₀ := .input
  k₁ := .output
  Γ := cnfSplitFoldStepChoiceMachineAlphabet
  Λ := CNFSplitFoldStepChoiceLabel
  main := .readAcc
  σ := CNFSplitFoldStepChoiceState
  initialState := .input none
  Γk₀Fin := inferInstance
  m
    | .readAcc =>
        pop .input (fun _ head => .input head)
          (goto fun state =>
            match cnfSplitFoldStepChoiceInputState state with
            | some (some (Sum.inl s)) =>
                .pushAccTemp (cnfSplitFoldStepChoiceAccOutputSymbol s)
            | some none => .readInstructionTag
            | _ => .invalid)
    | .pushAccTemp s =>
        push .temp (fun _ => s) (goto fun _ => .readAcc)
    | .pushLeftTemp s =>
        push .temp (fun _ => s) (goto fun _ => .readLeftPayload)
    | .pushRightTemp s =>
        push .temp (fun _ => s) (goto fun _ => .readRightPayload)
    | .readInstructionTag =>
        pop .input (fun _ head => .input head)
          (goto fun state =>
            match cnfSplitFoldStepChoiceInputState state with
            | some (some (Sum.inr (Sum.inl false))) => .clearAcc
            | some (some (Sum.inr (Sum.inl true))) => .pushRightDelimiter
            | _ => .invalid)
    | .clearAcc =>
        pop .temp (fun _ head => .output head)
          (goto fun state =>
            match cnfSplitFoldStepChoiceOutputState state with
            | some _ => .clearAcc
            | none => .readLeftPayload)
    | .readLeftPayload =>
        pop .input (fun _ head => .input head)
          (goto fun state =>
            match cnfSplitFoldStepChoiceInputState state with
            | some (some (Sum.inr (Sum.inr (Sum.inl s)))) =>
                .pushLeftTemp (cnfSplitFoldStepChoiceNatOutputSymbol s)
            | none => .moveTemp false
            | _ => .invalid)
    | .pushRightDelimiter =>
        push .temp (fun _ => cnfSplitFoldStepChoiceRightDelimiter)
          (goto fun _ => .readRightPayload)
    | .readRightPayload =>
        pop .input (fun _ head => .input head)
          (goto fun state =>
            match cnfSplitFoldStepChoiceInputState state with
            | some (some (Sum.inr (Sum.inr (Sum.inr s)))) =>
                .pushRightTemp (cnfSplitFoldStepChoiceClauseOutputSymbol s)
            | none => .moveTemp true
            | _ => .invalid)
    | .moveTemp tag =>
        pop .temp (fun _ head => .output head)
          (goto fun state =>
            match cnfSplitFoldStepChoiceOutputState state with
            | some s => .pushOutput tag s
            | none => .writeTag tag)
    | .pushOutput tag s =>
        push .output (fun _ => s) (goto fun _ => .moveTemp tag)
    | .writeTag tag =>
        push .output (fun _ => Sum.inl tag) (load (fun _ => .input none) halt)
    | .invalid =>
        halt

def cnfSplitFoldStepChoiceCfg
    (label : CNFSplitFoldStepChoiceLabel)
    (state : CNFSplitFoldStepChoiceState)
    (input : List cnfSplitFoldStepChoiceInputSymbol)
    (output temp : List cnfSplitFoldStepChoiceOutputSymbol) :
    cnfSplitFoldStepChoiceMachine.Cfg where
  l := some label
  var := state
  stk
    | .input => input
    | .output => output
    | .temp => temp

def cnfSplitFoldStepChoiceHalt
    (output : List cnfSplitFoldStepChoiceOutputSymbol) :
    cnfSplitFoldStepChoiceMachine.Cfg where
  l := none
  var := .input none
  stk
    | .input => []
    | .output => output
    | .temp => []

lemma cnfSplitFoldStepChoice_readAcc_step_cons
    (s : cnfSplitFoldAccEncodedType.Symbol)
    (state : CNFSplitFoldStepChoiceState)
    (input : List cnfSplitFoldStepChoiceInputSymbol)
    (output temp : List cnfSplitFoldStepChoiceOutputSymbol) :
    cnfSplitFoldStepChoiceMachine.step
        (cnfSplitFoldStepChoiceCfg .readAcc state
          (some (Sum.inl s) :: input) output temp) =
      some (cnfSplitFoldStepChoiceCfg
        (.pushAccTemp (cnfSplitFoldStepChoiceAccOutputSymbol s))
        (.input (some (some (Sum.inl s)))) input output temp) := by
  simp [cnfSplitFoldStepChoiceMachine, cnfSplitFoldStepChoiceCfg,
    cnfSplitFoldStepChoiceInputState]
  congr
  funext k
  cases k <;> rfl

lemma cnfSplitFoldStepChoice_readAcc_step_delim
    (state : CNFSplitFoldStepChoiceState)
    (input : List cnfSplitFoldStepChoiceInputSymbol)
    (output temp : List cnfSplitFoldStepChoiceOutputSymbol) :
    cnfSplitFoldStepChoiceMachine.step
        (cnfSplitFoldStepChoiceCfg .readAcc state
          ((none : cnfSplitFoldStepChoiceInputSymbol) :: input) output temp) =
      some (cnfSplitFoldStepChoiceCfg .readInstructionTag
        (.input (some none)) input output temp) := by
  simp [cnfSplitFoldStepChoiceMachine, cnfSplitFoldStepChoiceCfg,
    cnfSplitFoldStepChoiceInputState]
  congr
  funext k
  cases k <;> rfl

lemma cnfSplitFoldStepChoice_pushAccTemp_step
    (s : cnfSplitFoldStepChoiceOutputSymbol)
    (state : CNFSplitFoldStepChoiceState)
    (input : List cnfSplitFoldStepChoiceInputSymbol)
    (output temp : List cnfSplitFoldStepChoiceOutputSymbol) :
    cnfSplitFoldStepChoiceMachine.step
        (cnfSplitFoldStepChoiceCfg (.pushAccTemp s) state input output temp) =
      some (cnfSplitFoldStepChoiceCfg .readAcc state input output (s :: temp)) := by
  simp [cnfSplitFoldStepChoiceMachine, cnfSplitFoldStepChoiceCfg]
  congr
  funext k
  cases k <;> rfl

lemma cnfSplitFoldStepChoice_pushLeftTemp_step
    (s : cnfSplitFoldStepChoiceOutputSymbol)
    (state : CNFSplitFoldStepChoiceState)
    (input : List cnfSplitFoldStepChoiceInputSymbol)
    (output temp : List cnfSplitFoldStepChoiceOutputSymbol) :
    cnfSplitFoldStepChoiceMachine.step
        (cnfSplitFoldStepChoiceCfg (.pushLeftTemp s) state input output temp) =
      some (cnfSplitFoldStepChoiceCfg .readLeftPayload state input output (s :: temp)) := by
  simp [cnfSplitFoldStepChoiceMachine, cnfSplitFoldStepChoiceCfg]
  congr
  funext k
  cases k <;> rfl

lemma cnfSplitFoldStepChoice_pushRightTemp_step
    (s : cnfSplitFoldStepChoiceOutputSymbol)
    (state : CNFSplitFoldStepChoiceState)
    (input : List cnfSplitFoldStepChoiceInputSymbol)
    (output temp : List cnfSplitFoldStepChoiceOutputSymbol) :
    cnfSplitFoldStepChoiceMachine.step
        (cnfSplitFoldStepChoiceCfg (.pushRightTemp s) state input output temp) =
      some (cnfSplitFoldStepChoiceCfg .readRightPayload state input output (s :: temp)) := by
  simp [cnfSplitFoldStepChoiceMachine, cnfSplitFoldStepChoiceCfg]
  congr
  funext k
  cases k <;> rfl

lemma cnfSplitFoldStepChoice_readInstructionTag_step_left
    (input : List cnfSplitFoldStepChoiceInputSymbol)
    (output temp : List cnfSplitFoldStepChoiceOutputSymbol) :
    cnfSplitFoldStepChoiceMachine.step
        (cnfSplitFoldStepChoiceCfg .readInstructionTag (.input (some none))
          (some (Sum.inr (Sum.inl false)) :: input) output temp) =
      some (cnfSplitFoldStepChoiceCfg .clearAcc
        (.input (some (some (Sum.inr (Sum.inl false))))) input output temp) := by
  simp [cnfSplitFoldStepChoiceMachine, cnfSplitFoldStepChoiceCfg,
    cnfSplitFoldStepChoiceInputState]
  congr
  funext k
  cases k <;> rfl

lemma cnfSplitFoldStepChoice_readInstructionTag_step_right
    (input : List cnfSplitFoldStepChoiceInputSymbol)
    (output temp : List cnfSplitFoldStepChoiceOutputSymbol) :
    cnfSplitFoldStepChoiceMachine.step
        (cnfSplitFoldStepChoiceCfg .readInstructionTag (.input (some none))
          (some (Sum.inr (Sum.inl true)) :: input) output temp) =
      some (cnfSplitFoldStepChoiceCfg .pushRightDelimiter
        (.input (some (some (Sum.inr (Sum.inl true))))) input output temp) := by
  simp [cnfSplitFoldStepChoiceMachine, cnfSplitFoldStepChoiceCfg,
    cnfSplitFoldStepChoiceInputState]
  congr
  funext k
  cases k <;> rfl

lemma cnfSplitFoldStepChoice_clearAcc_step_cons
    (s : cnfSplitFoldStepChoiceOutputSymbol)
    (state : CNFSplitFoldStepChoiceState)
    (input : List cnfSplitFoldStepChoiceInputSymbol)
    (output temp : List cnfSplitFoldStepChoiceOutputSymbol) :
    cnfSplitFoldStepChoiceMachine.step
        (cnfSplitFoldStepChoiceCfg .clearAcc state input output (s :: temp)) =
      some (cnfSplitFoldStepChoiceCfg .clearAcc
        (.output (some s)) input output temp) := by
  simp [cnfSplitFoldStepChoiceMachine, cnfSplitFoldStepChoiceCfg,
    cnfSplitFoldStepChoiceOutputState]
  congr
  funext k
  cases k <;> rfl

lemma cnfSplitFoldStepChoice_clearAcc_step_nil
    (state : CNFSplitFoldStepChoiceState)
    (input : List cnfSplitFoldStepChoiceInputSymbol)
    (output : List cnfSplitFoldStepChoiceOutputSymbol) :
    cnfSplitFoldStepChoiceMachine.step
        (cnfSplitFoldStepChoiceCfg .clearAcc state input output []) =
      some (cnfSplitFoldStepChoiceCfg .readLeftPayload
        (.output none) input output []) := by
  simp [cnfSplitFoldStepChoiceMachine, cnfSplitFoldStepChoiceCfg,
    cnfSplitFoldStepChoiceOutputState]
  congr

lemma cnfSplitFoldStepChoice_readLeftPayload_step_cons
    (s : EncodedType.nat.Symbol)
    (state : CNFSplitFoldStepChoiceState)
    (input : List cnfSplitFoldStepChoiceInputSymbol)
    (output temp : List cnfSplitFoldStepChoiceOutputSymbol) :
    cnfSplitFoldStepChoiceMachine.step
        (cnfSplitFoldStepChoiceCfg .readLeftPayload state
          (some (Sum.inr (Sum.inr (Sum.inl s))) :: input) output temp) =
      some (cnfSplitFoldStepChoiceCfg
        (.pushLeftTemp (cnfSplitFoldStepChoiceNatOutputSymbol s))
        (.input (some (some (Sum.inr (Sum.inr (Sum.inl s)))))) input output temp) := by
  simp [cnfSplitFoldStepChoiceMachine, cnfSplitFoldStepChoiceCfg,
    cnfSplitFoldStepChoiceInputState]
  congr
  funext k
  cases k <;> rfl

lemma cnfSplitFoldStepChoice_readLeftPayload_step_nil
    (state : CNFSplitFoldStepChoiceState)
    (output temp : List cnfSplitFoldStepChoiceOutputSymbol) :
    cnfSplitFoldStepChoiceMachine.step
        (cnfSplitFoldStepChoiceCfg .readLeftPayload state [] output temp) =
      some (cnfSplitFoldStepChoiceCfg (.moveTemp false)
        (.input none) [] output temp) := by
  simp [cnfSplitFoldStepChoiceMachine, cnfSplitFoldStepChoiceCfg,
    cnfSplitFoldStepChoiceInputState]
  congr

lemma cnfSplitFoldStepChoice_pushRightDelimiter_step
    (state : CNFSplitFoldStepChoiceState)
    (input : List cnfSplitFoldStepChoiceInputSymbol)
    (output temp : List cnfSplitFoldStepChoiceOutputSymbol) :
    cnfSplitFoldStepChoiceMachine.step
        (cnfSplitFoldStepChoiceCfg .pushRightDelimiter state input output temp) =
      some (cnfSplitFoldStepChoiceCfg .readRightPayload state input output
        (cnfSplitFoldStepChoiceRightDelimiter :: temp)) := by
  simp [cnfSplitFoldStepChoiceMachine, cnfSplitFoldStepChoiceCfg]
  congr
  funext k
  cases k <;> rfl

lemma cnfSplitFoldStepChoice_readRightPayload_step_cons
    (s : clauseStructuredEncodedType.Symbol)
    (state : CNFSplitFoldStepChoiceState)
    (input : List cnfSplitFoldStepChoiceInputSymbol)
    (output temp : List cnfSplitFoldStepChoiceOutputSymbol) :
    cnfSplitFoldStepChoiceMachine.step
        (cnfSplitFoldStepChoiceCfg .readRightPayload state
          (some (Sum.inr (Sum.inr (Sum.inr s))) :: input) output temp) =
      some (cnfSplitFoldStepChoiceCfg
        (.pushRightTemp (cnfSplitFoldStepChoiceClauseOutputSymbol s))
        (.input (some (some (Sum.inr (Sum.inr (Sum.inr s)))))) input output temp) := by
  simp [cnfSplitFoldStepChoiceMachine, cnfSplitFoldStepChoiceCfg,
    cnfSplitFoldStepChoiceInputState]
  congr
  funext k
  cases k <;> rfl

end Karp21
end ComplexityReduction
