/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.SplitWith.RunnerFold

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction
open Turing.TM2.Stmt

theorem literalStructured_inputSize_succ_var_le_encodeLiteral_length (l : SAT.Literal) :
    literalStructuredEncodedType.inputSize l + 1 ≤
      (SAT.ThreeSATEncoding.encodeLiteral l).length := by
  cases l
  simp [literalStructured_inputSize_eq, SAT.ThreeSATEncoding.encodeLiteral,
    SAT.ThreeSATEncoding.encodeNat, EncodedType.nat]

theorem listStructured_inputSize_ge_length (X : EncodedType) :
    ∀ xs : List X.Carrier, xs.length ≤ (EncodedType.list X).inputSize xs
  | [] => by simp [EncodedType.inputSize, EncodedType.list]
  | x :: xs => by
      have ih := listStructured_inputSize_ge_length X xs
      rw [EncodedType.inputSize_list_cons]
      simp only [List.length_cons]
      omega

theorem clauseStructured_inputSize_ge_length (c : SAT.Clause) :
    c.length ≤ clauseStructuredEncodedType.inputSize c :=
  listStructured_inputSize_ge_length literalStructuredEncodedType c

theorem clauseVarBound_le_clauseStructured_inputSize (c : SAT.Clause) :
    SAT.Clause.varBound c ≤ clauseStructuredEncodedType.inputSize c := by
  induction c with
  | nil =>
      simp [SAT.Clause.varBound, clauseStructuredEncodedType, EncodedType.inputSize,
        EncodedType.list]
  | cons l ls ih =>
      have ih' :
          SAT.Clause.varBound ls ≤ (EncodedType.list literalStructuredEncodedType).inputSize ls := by
        simpa [clauseStructuredEncodedType] using ih
      have hl : l.var + 1 ≤ literalStructuredEncodedType.inputSize l := by
        rw [literalStructured_inputSize_eq]
        omega
      change
        max (l.var + 1) (SAT.Clause.varBound ls) ≤
          (EncodedType.list literalStructuredEncodedType).inputSize (l :: ls)
      rw [EncodedType.inputSize_list_cons]
      exact max_le (by omega) (by omega)

theorem cnfStructured_inputSize_ge_length (φ : SAT.CNF) :
    φ.length ≤ cnfStructuredEncodedType.inputSize φ :=
  listStructured_inputSize_ge_length clauseStructuredEncodedType φ

theorem cnfStructured_inputSize_ge_totalClauseLength_add_length (φ : SAT.CNF) :
    SAT.CNF.totalClauseLength φ + φ.length ≤ cnfStructuredEncodedType.inputSize φ := by
  induction φ with
  | nil =>
      simp [SAT.CNF.totalClauseLength, cnfStructuredEncodedType, EncodedType.inputSize,
        EncodedType.list]
  | cons c cs ih =>
      have ih' :
          SAT.CNF.totalClauseLength cs + cs.length ≤
            (EncodedType.list clauseStructuredEncodedType).inputSize cs := by
        simpa [cnfStructuredEncodedType] using ih
      have hc := clauseStructured_inputSize_ge_length c
      change
        SAT.CNF.totalClauseLength (c :: cs) + (c :: cs).length ≤
          (EncodedType.list clauseStructuredEncodedType).inputSize (c :: cs)
      rw [EncodedType.inputSize_list_cons]
      simp [SAT.CNF.totalClauseLength]
      omega

theorem cnfVarBound_le_cnfStructured_inputSize (φ : SAT.CNF) :
    SAT.CNF.varBound φ ≤ cnfStructuredEncodedType.inputSize φ := by
  induction φ with
  | nil =>
      simp [SAT.CNF.varBound, cnfStructuredEncodedType, EncodedType.inputSize,
        EncodedType.list]
  | cons c cs ih =>
      have ih' :
          SAT.CNF.varBound cs ≤ (EncodedType.list clauseStructuredEncodedType).inputSize cs := by
        simpa [cnfStructuredEncodedType] using ih
      have hc := clauseVarBound_le_clauseStructured_inputSize c
      change
        max (SAT.Clause.varBound c) (SAT.CNF.varBound cs) ≤
          (EncodedType.list clauseStructuredEncodedType).inputSize (c :: cs)
      rw [EncodedType.inputSize_list_cons]
      exact max_le (by omega) (by omega)

theorem cnfStructuralSize_le_structured_inputSize_poly_base (φ : SAT.CNF) :
    SAT.CNF.structuralSize φ ≤ 2 * cnfStructuredEncodedType.inputSize φ + 1 := by
  have hVar := cnfVarBound_le_cnfStructured_inputSize φ
  have hTotal := cnfStructured_inputSize_ge_totalClauseLength_add_length φ
  unfold SAT.CNF.structuralSize
  omega

theorem clauseStructured_inputSize_le_encodeLiteralPayload_length (c : SAT.Clause) :
    clauseStructuredEncodedType.inputSize c ≤
      (c.flatMap SAT.ThreeSATEncoding.encodeLiteral).length := by
  induction c with
  | nil =>
      simp [clauseStructuredEncodedType, EncodedType.inputSize, EncodedType.list,
        List.length_flatMap]
      exact ⟨rfl, rfl⟩
  | cons l ls ih =>
      have ih' :
          (EncodedType.list literalStructuredEncodedType).inputSize ls ≤
            (ls.flatMap SAT.ThreeSATEncoding.encodeLiteral).length := by
        simpa [clauseStructuredEncodedType] using ih
      have hl := literalStructured_inputSize_succ_var_le_encodeLiteral_length l
      change
        (EncodedType.list literalStructuredEncodedType).inputSize (l :: ls) ≤
          ((l :: ls).flatMap SAT.ThreeSATEncoding.encodeLiteral).length
      rw [EncodedType.inputSize_list_cons]
      change
        literalStructuredEncodedType.inputSize l + 1 +
            (EncodedType.list literalStructuredEncodedType).inputSize ls ≤
          (SAT.ThreeSATEncoding.encodeLiteral l ++
            ls.flatMap SAT.ThreeSATEncoding.encodeLiteral).length
      rw [List.length_append]
      omega

theorem clauseStructured_inputSize_succ_le_encodeClause_length (c : SAT.Clause) :
    clauseStructuredEncodedType.inputSize c + 1 ≤
      (SAT.ThreeSATEncoding.encodeClause c).length := by
  have h := clauseStructured_inputSize_le_encodeLiteralPayload_length c
  simp [SAT.ThreeSATEncoding.encodeClause, List.length_flatMap] at h ⊢
  omega

theorem cnfStructured_inputSize_le_encodeCNF_length (φ : SAT.CNF) :
    cnfStructuredEncodedType.inputSize φ ≤
      (SAT.ThreeSATEncoding.encodeCNF φ).length := by
  induction φ with
  | nil =>
      simp [cnfStructuredEncodedType, SAT.ThreeSATEncoding.encodeCNF,
        EncodedType.inputSize, EncodedType.list, List.length_flatMap]
      exact ⟨rfl, rfl⟩
  | cons c cs ih =>
      have ih' :
          (EncodedType.list clauseStructuredEncodedType).inputSize cs ≤
            (SAT.ThreeSATEncoding.encodeCNF cs).length := by
        simpa [cnfStructuredEncodedType] using ih
      have hc := clauseStructured_inputSize_succ_le_encodeClause_length c
      change
        (EncodedType.list clauseStructuredEncodedType).inputSize (c :: cs) ≤
          (SAT.ThreeSATEncoding.encodeCNF (c :: cs)).length
      rw [EncodedType.inputSize_list_cons]
      change
        clauseStructuredEncodedType.inputSize c + 1 +
            (EncodedType.list clauseStructuredEncodedType).inputSize cs ≤
          (SAT.ThreeSATEncoding.encodeClause c ++
            SAT.ThreeSATEncoding.encodeCNF cs).length
      rw [List.length_append]
      omega

theorem splitWith_lit_bound_of_vars_lt_and_length
    (next : Nat) (c : SAT.Clause) (B : Nat)
    (hVars : ∀ l ∈ c, l.var < B) (hFresh : next + c.length ≤ B) :
    ∀ d ∈ SAT.Clause.splitWith next c, ∀ l ∈ d, l.var < B := by
  fun_induction SAT.Clause.splitWith next c with
  | case1 next =>
      intro d hd l hl
      have hd' : d = [] := by
        simpa [SAT.Clause.splitWith] using hd
      subst d
      cases hl
  | case2 next lit =>
      intro d hd l hl
      have hd' : d = [lit] := by
        simpa [SAT.Clause.splitWith] using hd
      subst d
      exact hVars l (by simpa using hl)
  | case3 next lit1 lit2 =>
      intro d hd l hl
      have hd' : d = [lit1, lit2] := by
        simpa [SAT.Clause.splitWith] using hd
      subst d
      exact hVars l (by simpa using hl)
  | case4 next lit1 lit2 lit3 =>
      intro d hd l hl
      have hd' : d = [lit1, lit2, lit3] := by
        simpa [SAT.Clause.splitWith] using hd
      subst d
      exact hVars l (by simpa using hl)
  | case5 next lit1 lit2 lit3 lit4 rest ih =>
      intro d hd l hl
      rcases List.mem_cons.mp (by simpa [SAT.Clause.splitWith] using hd) with hhead | htail
      · subst d
        rcases List.mem_cons.mp hl with h1 | hl
        · subst l
          exact hVars lit1 (by simp)
        · rcases List.mem_cons.mp hl with h2 | hl
          · subst l
            exact hVars lit2 (by simp)
          · have hpos : l = SAT.Clause.posAux next := by
              simpa using hl
            subst l
            have hnext : next < B := by
              have hlen : next < next + (lit1 :: lit2 :: lit3 :: lit4 :: rest).length := by
                simp
              omega
            simpa [SAT.Clause.posAux] using hnext
      · have hTailVars :
            ∀ l ∈ SAT.Clause.negAux next :: lit3 :: lit4 :: rest, l.var < B := by
          intro l hl'
          rcases List.mem_cons.mp hl' with hneg | hrest
          · subst l
            have hnext : next < B := by
              have hlen : next < next + (lit1 :: lit2 :: lit3 :: lit4 :: rest).length := by
                simp
              omega
            simpa [SAT.Clause.negAux] using hnext
          · exact hVars l (by simp [hrest])
        have hTailFresh :
            next + 1 + (SAT.Clause.negAux next :: lit3 :: lit4 :: rest).length ≤ B := by
          have hEq :
              next + 1 + (SAT.Clause.negAux next :: lit3 :: lit4 :: rest).length =
                next + (lit1 :: lit2 :: lit3 :: lit4 :: rest).length := by
            simp
            omega
          rw [hEq]
          exact hFresh
        exact ih hTailVars hTailFresh d htail l hl

theorem splitWith_lit_bound_structured (next : Nat) (c : SAT.Clause) :
    ∀ d ∈ SAT.Clause.splitWith next c, ∀ l ∈ d,
      l.var < next + clauseStructuredEncodedType.inputSize c + 1 := by
  refine
    splitWith_lit_bound_of_vars_lt_and_length next c
      (next + clauseStructuredEncodedType.inputSize c + 1) ?_ ?_
  · intro l hl
    have hVar := SAT.Clause.var_lt_varBound hl
    have hBound := clauseVarBound_le_clauseStructured_inputSize c
    omega
  · have hLen := clauseStructured_inputSize_ge_length c
    omega

theorem splitWith_structured_inputSize_le_quadratic (next : Nat) (c : SAT.Clause) :
    cnfStructuredEncodedType.inputSize (SAT.Clause.splitWith next c) ≤
      20 * (next + clauseStructuredEncodedType.inputSize c + 1) ^ 2 := by
  let B := next + clauseStructuredEncodedType.inputSize c + 1
  have hStruct := cnfStructured_inputSize_le_encodeCNF_length (SAT.Clause.splitWith next c)
  have hEncode :=
    SAT.ThreeSATEncoding.encodeCNF_length_le_of_vars_lt
      (SAT.Clause.splitWith next c) B
      (SAT.Clause.splitWith_isThreeCNF next c)
      (by
        simpa [B] using splitWith_lit_bound_structured next c)
  have hLen := SAT.Clause.splitWith_length_le next c
  have hClauseLen := clauseStructured_inputSize_ge_length c
  have hLenFactor :
      (SAT.Clause.splitWith next c).length ≤ clauseStructuredEncodedType.inputSize c + 1 := by
    omega
  have hBFactor : clauseStructuredEncodedType.inputSize c + 1 ≤ B := by
    simp [B]
  have hBpos : 0 < B := by
    simp [B]
  calc
    cnfStructuredEncodedType.inputSize (SAT.Clause.splitWith next c)
        ≤ (SAT.ThreeSATEncoding.encodeCNF (SAT.Clause.splitWith next c)).length := hStruct
    _ ≤ (SAT.Clause.splitWith next c).length * (1 + 3 * (B + 5)) := hEncode
    _ ≤ (clauseStructuredEncodedType.inputSize c + 1) * (1 + 3 * (B + 5)) := by
          exact Nat.mul_le_mul hLenFactor (Nat.le_refl _)
    _ ≤ B * (1 + 3 * (B + 5)) := by
          exact Nat.mul_le_mul hBFactor (Nat.le_refl _)
    _ ≤ 20 * B ^ 2 := by
          nlinarith [sq_nonneg (B : Int)]

theorem splitWithInput_polynomialSizeBound :
    PolynomialSizeBound
      (fun p : splitWithInputEncodedType.Carrier => splitWithInputEncodedType.inputSize p)
      (fun φ : SAT.CNF => cnfStructuredEncodedType.inputSize φ)
      (fun p : splitWithInputEncodedType.Carrier => SAT.Clause.splitWith p.1 p.2) := by
  refine PolynomialSizeBound.intro_with 2 20 0 ?_
  intro p
  rcases p with ⟨next, c⟩
  change Nat at next
  have hSplit := splitWith_structured_inputSize_le_quadratic next c
  have hInput :
      next + clauseStructuredEncodedType.inputSize c + 1 ≤
        splitWithInputEncodedType.inputSize (next, c) := by
    simp [splitWithInputEncodedType, EncodedType.inputSize, EncodedType.prod, EncodedType.nat]
  have hPow := Nat.pow_le_pow_left hInput 2
  calc
    cnfStructuredEncodedType.inputSize (SAT.Clause.splitWith next c)
        ≤ 20 * (next + clauseStructuredEncodedType.inputSize c + 1) ^ 2 := hSplit
    _ ≤ 20 * (splitWithInputEncodedType.inputSize (next, c)) ^ 2 := by
          exact Nat.mul_le_mul_left 20 hPow
    _ ≤ 20 * (splitWithInputEncodedType.inputSize (next, c)) ^ 2 + 0 := by
          omega

theorem splitWithTraceOutput_polynomialSizeBound :
    PolynomialSizeBound
      (fun p : splitWithInputEncodedType.Carrier => splitWithInputEncodedType.inputSize p)
      (fun out : splitWithTraceOutputEncodedType.Carrier =>
        splitWithTraceOutputEncodedType.inputSize out)
      (fun p : splitWithInputEncodedType.Carrier => splitWithTrace p.1 p.2) := by
  refine PolynomialSizeBound.intro_with 2 1000 1000 ?_
  intro p
  have hCurrent :=
    splitWithTraceLoopAccCurrentOutput_inputSize_le (splitWithTraceRunnerFold p)
  have hFold := splitWithTraceRunnerFold_inputSize_le p
  have hInstr := splitWithTraceRunnerInstructions_inputSize_le p
  let S :=
    (EncodedType.list splitWithTraceRunnerInstructionEncodedType).inputSize
      (splitWithTraceRunnerInstructions p)
  let N := splitWithInputEncodedType.inputSize p
  have hNpos : 1 ≤ N := by
    rcases p with ⟨next, c⟩
    simp [N, splitWithInputEncodedType, EncodedType.inputSize, EncodedType.prod,
      EncodedType.nat]
    omega
  have hSsq : S ^ 2 ≤ (3 * N + 6) ^ 2 := by
    exact Nat.pow_le_pow_left (by simpa [S, N] using hInstr) 2
  rw [← splitWithTraceRunnerFold_currentOutput_eq_trace p]
  change
    splitWithTraceOutputEncodedType.inputSize
        (splitWithTraceLoopAccCurrentOutput (splitWithTraceRunnerFold p)) ≤
      1000 * N ^ 2 + 1000
  change
    splitWithTraceLoopAccEncodedType.inputSize (splitWithTraceRunnerFold p) ≤
      20 * S ^ 2 + 20 at hFold
  calc
    splitWithTraceOutputEncodedType.inputSize
        (splitWithTraceLoopAccCurrentOutput (splitWithTraceRunnerFold p))
        ≤ splitWithTraceLoopAccEncodedType.inputSize (splitWithTraceRunnerFold p) := hCurrent
    _ ≤ 20 * S ^ 2 + 20 := hFold
    _ ≤ 20 * (3 * N + 6) ^ 2 + 20 := by
          exact Nat.add_le_add_right (Nat.mul_le_mul_left 20 hSsq) 20
    _ ≤ 1000 * N ^ 2 + 1000 := by
          nlinarith [hNpos, sq_nonneg (N : Int)]

noncomputable def splitWithTraceOutputTMBackedMap :
    TMBackedCostedMap
      splitWithInputEncodedType
      splitWithTraceOutputEncodedType
      (fun p : splitWithInputEncodedType.Carrier => splitWithTrace p.1 p.2) where
  costed := CostedMap.of_encodedPolynomialSizeBound splitWithTraceOutput_polynomialSizeBound
  tm_polytime := by
    have hRunner :
        TMPolyTimeMap
          splitWithInputEncodedType
          splitWithTraceLoopAccEncodedType
          splitWithTraceRunnerFold := by
      have hComp :=
        TMPolyTimeMap.comp
          splitWithTraceRunnerFoldImageTMBackedMap.tm_polytime
          splitWithTraceRunnerInstructionsImageTMBackedMap.tm_polytime
      simpa [Function.comp] using hComp
    have hCurrent :=
      splitWithTraceLoopAccCurrentOutputTMBackedMap.tm_polytime
    have hComp :=
      TMPolyTimeMap.comp hCurrent hRunner
    convert hComp using 1
    funext p
    exact (splitWithTraceRunnerFold_currentOutput_eq_trace p).symm

noncomputable def splitWithInputTMBackedMap :
    TMBackedCostedMap
      splitWithInputEncodedType
      cnfStructuredEncodedType
      (fun p : splitWithInputEncodedType.Carrier => SAT.Clause.splitWith p.1 p.2) where
  costed := CostedMap.of_encodedPolynomialSizeBound splitWithInput_polynomialSizeBound
  tm_polytime := by
    have hComp :=
      TMPolyTimeMap.comp
        splitWithTraceOutputToCNFTMBackedMap.tm_polytime
        splitWithTraceOutputTMBackedMap.tm_polytime
    convert hComp using 1
    funext p
    exact splitWith_eq_traceOutputToCNF p.1 p.2

end Karp21
end ComplexityReduction
