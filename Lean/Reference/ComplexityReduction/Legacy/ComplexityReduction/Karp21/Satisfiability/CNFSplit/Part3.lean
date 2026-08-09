import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.CNFSplit.Part2

namespace ComplexityReduction
namespace Karp21
open ComplexityReduction
open Turing.TM2.Stmt

def cnfSplitFoldStep
    (p : cnfSplitFoldAccEncodedType.Carrier × cnfSplitInstructionEncodedType.Carrier) :
    cnfSplitFoldAccEncodedType.Carrier := by
  rcases p with ⟨acc, instr⟩
  cases instr with
  | inl next =>
      change Nat at next
      exact (next, ([] : SAT.CNF))
  | inr c =>
      exact cnfSplitFoldRightStep (acc, c)

theorem cnfSplitFoldStep_eq_dispatch_choice
    (p : cnfSplitFoldStepInputEncodedType.Carrier) :
    cnfSplitFoldStep p =
      cnfSplitFoldStepChoiceDispatch (cnfSplitFoldStepChoice p) := by
  rcases p with ⟨acc, instr⟩
  cases instr with
  | inl next =>
      rfl
  | inr c =>
      rfl

theorem cnfSplitFoldStep_inputSize_le
    (p : cnfSplitFoldStepInputEncodedType.Carrier) :
    cnfSplitFoldAccEncodedType.inputSize (cnfSplitFoldStep p) ≤
      100 * cnfSplitFoldStepInputEncodedType.inputSize p ^ 2 + 100 := by
  have hChoice := cnfSplitFoldStepChoice_inputSize_le p
  have hDispatch :=
    cnfSplitFoldStepChoiceDispatch_inputSize_le (cnfSplitFoldStepChoice p)
  have hPow :
      cnfSplitFoldStepChoiceEncodedType.inputSize (cnfSplitFoldStepChoice p) ^ 2 ≤
        cnfSplitFoldStepInputEncodedType.inputSize p ^ 2 :=
    Nat.pow_le_pow_left hChoice 2
  calc
    cnfSplitFoldAccEncodedType.inputSize (cnfSplitFoldStep p) =
        cnfSplitFoldAccEncodedType.inputSize
          (cnfSplitFoldStepChoiceDispatch (cnfSplitFoldStepChoice p)) := by
          rw [cnfSplitFoldStep_eq_dispatch_choice p]
    _ ≤ 100 * cnfSplitFoldStepChoiceEncodedType.inputSize (cnfSplitFoldStepChoice p) ^ 2 +
          100 := hDispatch
    _ ≤ 100 * cnfSplitFoldStepInputEncodedType.inputSize p ^ 2 + 100 := by
          exact Nat.add_le_add_right (Nat.mul_le_mul_left 100 hPow) 100

noncomputable def cnfSplitFoldStepTMBackedMap :
    TMBackedCostedMap
      cnfSplitFoldStepInputEncodedType
      cnfSplitFoldAccEncodedType
      cnfSplitFoldStep where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      (PolynomialSizeBound.intro_with 2 100 100 (by
        intro p
        exact cnfSplitFoldStep_inputSize_le p))
  tm_polytime := by
    have hComp :=
      TMPolyTimeMap.comp
        cnfSplitFoldStepChoiceDispatchTMBackedMap.tm_polytime
        cnfSplitFoldStepChoiceTMBackedMap.tm_polytime
    convert hComp using 1
    funext p
    exact cnfSplitFoldStep_eq_dispatch_choice p

def cnfSplitRunnerInit : cnfSplitFoldAccEncodedType.Carrier :=
  ((0 : Nat), ([] : SAT.CNF))

def cnfSplitRunnerFold (φ : SAT.CNF) : cnfSplitFoldAccEncodedType.Carrier :=
  (cnfSplitRunnerInstructions φ).foldl
    (fun acc instr => cnfSplitFoldStep (acc, instr)) cnfSplitRunnerInit

theorem cnfSplitFoldRightStep_fold_eq_splitAux
    (φ : SAT.CNF) (next : Nat) (out : SAT.CNF) :
    φ.foldl (fun acc c => cnfSplitFoldRightStep (acc, c)) (next, out) =
      (next + SAT.CNF.totalClauseLength φ, out ++ SAT.CNF.splitAux next φ) := by
  induction φ generalizing next out with
  | nil =>
      change (next, out) = (next + 0, out ++ ([] : SAT.CNF))
      simp
  | cons c cs ih =>
      change
        cs.foldl (fun acc c => cnfSplitFoldRightStep (acc, c))
            (next + c.length, out ++ SAT.Clause.splitWith next c) =
          (next + SAT.CNF.totalClauseLength (c :: cs),
            out ++ SAT.CNF.splitAux next (c :: cs))
      rw [ih]
      simp [SAT.CNF.totalClauseLength, SAT.CNF.splitAux, Nat.add_assoc,
        List.append_assoc]

theorem cnfSplitFoldStep_fold_map_inr
    (φ : SAT.CNF) (acc : cnfSplitFoldAccEncodedType.Carrier) :
    (φ.map (fun c => (Sum.inr c : cnfSplitInstructionEncodedType.Carrier))).foldl
        (fun acc instr => cnfSplitFoldStep (acc, instr)) acc =
      φ.foldl (fun acc c => cnfSplitFoldRightStep (acc, c)) acc := by
  induction φ generalizing acc with
  | nil =>
      rfl
  | cons c cs ih =>
      change
        (cs.map (fun c => (Sum.inr c : cnfSplitInstructionEncodedType.Carrier))).foldl
            (fun acc instr => cnfSplitFoldStep (acc, instr))
            (cnfSplitFoldStep (acc, Sum.inr c)) =
          cs.foldl (fun acc c => cnfSplitFoldRightStep (acc, c))
            (cnfSplitFoldRightStep (acc, c))
      exact ih (cnfSplitFoldRightStep (acc, c))

theorem cnfSplitRunnerFold_eq_splitAux (φ : SAT.CNF) :
    cnfSplitRunnerFold φ =
      (cnfStructuredEncodedType.inputSize φ + SAT.CNF.totalClauseLength φ,
        SAT.CNF.splitAux (cnfStructuredEncodedType.inputSize φ) φ) := by
  unfold cnfSplitRunnerFold cnfSplitRunnerInstructions cnfSplitRunnerInit
  rw [List.foldl_cons]
  change
    (φ.map (fun c => (Sum.inr c : cnfSplitInstructionEncodedType.Carrier))).foldl
        (fun acc instr => cnfSplitFoldStep (acc, instr))
        (cnfStructuredEncodedType.inputSize φ, ([] : SAT.CNF)) =
      (cnfStructuredEncodedType.inputSize φ + SAT.CNF.totalClauseLength φ,
        SAT.CNF.splitAux (cnfStructuredEncodedType.inputSize φ) φ)
  rw [cnfSplitFoldStep_fold_map_inr]
  simpa using
    cnfSplitFoldRightStep_fold_eq_splitAux φ (cnfStructuredEncodedType.inputSize φ) []

theorem cnfSplitRunnerFold_clauses_eq (φ : SAT.CNF) :
    (cnfSplitRunnerFold φ).2 =
      SAT.CNF.splitAux (cnfStructuredEncodedType.inputSize φ) φ := by
  rw [cnfSplitRunnerFold_eq_splitAux]

theorem clauseStructured_inputSize_le_cnfStructured_inputSize_of_mem
    {φ : SAT.CNF} {c : SAT.Clause} (hc : c ∈ φ) :
    clauseStructuredEncodedType.inputSize c ≤ cnfStructuredEncodedType.inputSize φ := by
  induction φ with
  | nil =>
      cases hc
  | cons d ds ih =>
      rw [List.mem_cons] at hc
      change clauseStructuredEncodedType.inputSize c ≤
        (EncodedType.list clauseStructuredEncodedType).inputSize (d :: ds)
      rw [EncodedType.inputSize_list_cons]
      cases hc with
      | inl h =>
          subst h
          omega
      | inr h =>
          have ih' :
              clauseStructuredEncodedType.inputSize c ≤
                (EncodedType.list clauseStructuredEncodedType).inputSize ds := by
            simpa [cnfStructuredEncodedType] using ih h
          omega

theorem cnfSplitPrefixAcc_inputSize_le
    (S : Nat) (ψ : SAT.CNF)
    (hTotal : SAT.CNF.totalClauseLength ψ + ψ.length ≤ S)
    (hBound : ∀ c ∈ ψ, ∀ l ∈ c, l.var < S) :
    cnfSplitFoldAccEncodedType.inputSize
        (S + SAT.CNF.totalClauseLength ψ, SAT.CNF.splitAux S ψ) ≤
      2000 * S ^ 2 + 2000 := by
  have hEncode := SAT.CNF.splitAux_encodedLength_le S ψ hBound
  have hStruct :
      cnfStructuredEncodedType.inputSize (SAT.CNF.splitAux S ψ) ≤
        (SAT.ThreeSATEncoding.encodeCNF (SAT.CNF.splitAux S ψ)).length :=
    cnfStructured_inputSize_le_encodeCNF_length (SAT.CNF.splitAux S ψ)
  have hCNF :
      cnfStructuredEncodedType.inputSize (SAT.CNF.splitAux S ψ) ≤
        1000 * S ^ 2 + 1000 := by
    calc
      cnfStructuredEncodedType.inputSize (SAT.CNF.splitAux S ψ)
          ≤ (SAT.ThreeSATEncoding.encodeCNF (SAT.CNF.splitAux S ψ)).length := hStruct
      _ ≤ (SAT.CNF.totalClauseLength ψ + ψ.length) *
            (1 + 3 * (S + SAT.CNF.totalClauseLength ψ + 5)) := hEncode
      _ ≤ S * (1 + 3 * (S + S + 5)) := by
            have hFactor :
                1 + 3 * (S + SAT.CNF.totalClauseLength ψ + 5) ≤
                  1 + 3 * (S + S + 5) := by
              nlinarith [hTotal]
            exact Nat.mul_le_mul hTotal hFactor
      _ ≤ 1000 * S ^ 2 + 1000 := by
            nlinarith [sq_nonneg (S : Int)]
  have hNext : S + SAT.CNF.totalClauseLength ψ ≤ 2 * S := by
    nlinarith [hTotal]
  change
    (EncodedType.prod EncodedType.nat cnfStructuredEncodedType).inputSize
        (S + SAT.CNF.totalClauseLength ψ, SAT.CNF.splitAux S ψ) ≤
      2000 * S ^ 2 + 2000
  rw [EncodedType.inputSize_prod]
  simp [EncodedType.inputSize, EncodedType.nat]
  have hCNFLen :
      (cnfStructuredEncodedType.encode (SAT.CNF.splitAux S ψ)).length ≤
        1000 * S ^ 2 + 1000 := by
    simpa [EncodedType.inputSize] using hCNF
  nlinarith [hCNFLen, hNext, sq_nonneg (S : Int)]

noncomputable def cnfSplitRunnerFoldAccBoundPolynomial : Polynomial Nat :=
  Polynomial.C 2000 * (Polynomial.X * Polynomial.X) + Polynomial.C 2000

@[simp] theorem cnfSplitRunnerFoldAccBoundPolynomial_eval (n : Nat) :
    cnfSplitRunnerFoldAccBoundPolynomial.eval n = 2000 * (n * n) + 2000 := by
  simp [cnfSplitRunnerFoldAccBoundPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_X]

theorem cnfSplitPrefixAcc_inputSize_le_image_bound
    (φ pref rest : SAT.CNF) (hSource : pref ++ rest = φ) :
    cnfSplitFoldAccEncodedType.inputSize
        (cnfStructuredEncodedType.inputSize φ + SAT.CNF.totalClauseLength pref,
          SAT.CNF.splitAux (cnfStructuredEncodedType.inputSize φ) pref) ≤
      cnfSplitRunnerFoldAccBoundPolynomial.eval
        ((EncodedType.list cnfSplitInstructionEncodedType).inputSize
          (cnfSplitRunnerInstructions φ)) := by
  let S := cnfStructuredEncodedType.inputSize φ
  let N :=
    (EncodedType.list cnfSplitInstructionEncodedType).inputSize
      (cnfSplitRunnerInstructions φ)
  have hSN : S ≤ N := by
    dsimp [N]
    rw [cnfSplitRunnerInstructions, EncodedType.inputSize_list_cons]
    have hInit :
        cnfSplitInstructionEncodedType.inputSize
            (Sum.inl S : cnfSplitInstructionEncodedType.Carrier) = S + 2 := by
      simp [cnfSplitInstructionEncodedType, EncodedType.inputSize, EncodedType.sum,
        EncodedType.nat]
    rw [hInit]
    omega
  have hTotalSource := cnfStructured_inputSize_ge_totalClauseLength_add_length φ
  have hTotalPrefix : SAT.CNF.totalClauseLength pref + pref.length ≤ S := by
    have hEq :
        SAT.CNF.totalClauseLength φ + φ.length =
          (SAT.CNF.totalClauseLength pref + pref.length) +
            (SAT.CNF.totalClauseLength rest + rest.length) := by
      rw [← hSource, SAT.CNF.totalClauseLength_append, List.length_append]
      omega
    omega
  have hVarSource : ∀ c ∈ φ, ∀ l ∈ c, l.var < S := by
    intro c hc l hl
    exact lt_of_lt_of_le (SAT.CNF.clause_vars_lt_varBound hc l hl)
      (by simpa [S] using cnfVarBound_le_cnfStructured_inputSize φ)
  have hBoundPrefix : ∀ c ∈ pref, ∀ l ∈ c, l.var < S := by
    intro c hc l hl
    exact hVarSource c (by
      rw [← hSource]
      exact List.mem_append.mpr (Or.inl hc)) l hl
  have hPrefix :=
    cnfSplitPrefixAcc_inputSize_le S pref hTotalPrefix hBoundPrefix
  have hPow : S ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hSN 2
  calc
    cnfSplitFoldAccEncodedType.inputSize
        (S + SAT.CNF.totalClauseLength pref, SAT.CNF.splitAux S pref)
        ≤ 2000 * S ^ 2 + 2000 := hPrefix
    _ ≤ 2000 * N ^ 2 + 2000 := by
          exact Nat.add_le_add_right (Nat.mul_le_mul_left 2000 hPow) 2000
    _ = cnfSplitRunnerFoldAccBoundPolynomial.eval N := by
          simp [pow_two]

theorem cnfSplitPrefix_step_eq (S : Nat) (pref : SAT.CNF) (c : SAT.Clause) :
    cnfSplitFoldStep
        ((S + SAT.CNF.totalClauseLength pref, SAT.CNF.splitAux S pref),
          (Sum.inr c : cnfSplitInstructionEncodedType.Carrier)) =
      (S + SAT.CNF.totalClauseLength (pref ++ [c]), SAT.CNF.splitAux S (pref ++ [c])) := by
  let step := fun acc c => cnfSplitFoldRightStep (acc, c)
  have hPref :
      pref.foldl step (S, ([] : SAT.CNF)) =
        (S + SAT.CNF.totalClauseLength pref, SAT.CNF.splitAux S pref) := by
    simpa [step] using cnfSplitFoldRightStep_fold_eq_splitAux pref S []
  have hAppend :
      (pref ++ [c]).foldl step (S, ([] : SAT.CNF)) =
        cnfSplitFoldRightStep
          ((S + SAT.CNF.totalClauseLength pref, SAT.CNF.splitAux S pref), c) := by
    have hAppendGeneral :
        ∀ (xs : SAT.CNF) (acc : cnfSplitFoldAccEncodedType.Carrier),
          (xs ++ [c]).foldl step acc = cnfSplitFoldRightStep (xs.foldl step acc, c) := by
      intro xs
      induction xs with
      | nil =>
          intro acc
          rfl
      | cons d ds ih =>
          intro acc
          change (ds ++ [c]).foldl step (step acc d) =
            cnfSplitFoldRightStep (ds.foldl step (step acc d), c)
          exact ih (step acc d)
    have h := hAppendGeneral pref (S, ([] : SAT.CNF))
    rw [hPref] at h
    exact h
  have hWhole :
      (pref ++ [c]).foldl step (S, ([] : SAT.CNF)) =
        (S + SAT.CNF.totalClauseLength (pref ++ [c]), SAT.CNF.splitAux S (pref ++ [c])) := by
    simpa [step] using cnfSplitFoldRightStep_fold_eq_splitAux (pref ++ [c]) S []
  calc
    cnfSplitFoldStep
        ((S + SAT.CNF.totalClauseLength pref, SAT.CNF.splitAux S pref),
          (Sum.inr c : cnfSplitInstructionEncodedType.Carrier))
        = cnfSplitFoldRightStep
            ((S + SAT.CNF.totalClauseLength pref, SAT.CNF.splitAux S pref), c) := rfl
    _ = (pref ++ [c]).foldl step (S, ([] : SAT.CNF)) := hAppend.symm
    _ = (S + SAT.CNF.totalClauseLength (pref ++ [c]), SAT.CNF.splitAux S (pref ++ [c])) :=
          hWhole

theorem cnfSplitRunnerInstructionTail_inputSize_eq
    (φ : SAT.CNF) :
    (EncodedType.list cnfSplitInstructionEncodedType).inputSize
        (φ.map (fun c => (Sum.inr c : cnfSplitInstructionEncodedType.Carrier))) =
      cnfStructuredEncodedType.inputSize φ + φ.length := by
  induction φ with
  | nil =>
      rfl
  | cons c cs ih =>
      change
        (EncodedType.list cnfSplitInstructionEncodedType).inputSize
            (Sum.inr c :: cs.map
              (fun c => (Sum.inr c : cnfSplitInstructionEncodedType.Carrier))) =
          cnfStructuredEncodedType.inputSize (c :: cs) + (c :: cs).length
      rw [EncodedType.inputSize_list_cons, ih]
      have hCNFCons :
          cnfStructuredEncodedType.inputSize (c :: cs) =
            clauseStructuredEncodedType.inputSize c + 1 + cnfStructuredEncodedType.inputSize cs := by
        simp [cnfStructuredEncodedType, EncodedType.inputSize_list_cons]
      rw [hCNFCons]
      simp [cnfSplitInstructionEncodedType, cnfStructuredEncodedType,
        EncodedType.inputSize, EncodedType.sum]
      omega

theorem cnfSplitRunnerInstructionTail_inputSize_le
    (φ : SAT.CNF) :
    (EncodedType.list cnfSplitInstructionEncodedType).inputSize
        (φ.map (fun c => (Sum.inr c : cnfSplitInstructionEncodedType.Carrier))) ≤
      2 * cnfStructuredEncodedType.inputSize φ := by
  rw [cnfSplitRunnerInstructionTail_inputSize_eq]
  have hLen := cnfStructured_inputSize_ge_length φ
  omega

theorem cnfSplitRunnerInstructions_inputSize_le (φ : SAT.CNF) :
    (EncodedType.list cnfSplitInstructionEncodedType).inputSize
        (cnfSplitRunnerInstructions φ) ≤
      3 * cnfStructuredEncodedType.inputSize φ + 3 := by
  let S := cnfStructuredEncodedType.inputSize φ
  have hTail := cnfSplitRunnerInstructionTail_inputSize_le φ
  rw [cnfSplitRunnerInstructions, EncodedType.inputSize_list_cons]
  have hInit :
      cnfSplitInstructionEncodedType.inputSize
          (Sum.inl S : cnfSplitInstructionEncodedType.Carrier) = S + 2 := by
    simp [cnfSplitInstructionEncodedType, EncodedType.inputSize, EncodedType.sum,
      EncodedType.nat]
  rw [hInit]
  omega

theorem cnfSplitRunnerInstructions_inputSize_ge_source (φ : SAT.CNF) :
    cnfStructuredEncodedType.inputSize φ ≤
      (EncodedType.list cnfSplitInstructionEncodedType).inputSize
        (cnfSplitRunnerInstructions φ) := by
  let S := cnfStructuredEncodedType.inputSize φ
  rw [cnfSplitRunnerInstructions, EncodedType.inputSize_list_cons]
  have hInit :
      cnfSplitInstructionEncodedType.inputSize
          (Sum.inl S : cnfSplitInstructionEncodedType.Carrier) = S + 2 := by
    simp [cnfSplitInstructionEncodedType, EncodedType.inputSize, EncodedType.sum,
      EncodedType.nat]
  rw [hInit]
  omega

noncomputable def cnfSplitRunnerInstructionsTMBackedMap :
    TMBackedCostedMap
      cnfStructuredEncodedType
      (EncodedType.list cnfSplitInstructionEncodedType)
      cnfSplitRunnerInstructions where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := cnfStructuredEncodedType)
      (Y := EncodedType.list cnfSplitInstructionEncodedType)
      (LinearSizeBound.intro_with 3 3 (by
        intro φ
        exact cnfSplitRunnerInstructions_inputSize_le φ))
  tm_polytime := by
    let X := cnfStructuredEncodedType
    let Instr := cnfSplitInstructionEncodedType
    have hSize :
        TMPolyTimeMap X EncodedType.nat
          (fun φ : X.Carrier => cnfStructuredEncodedType.inputSize φ) :=
      (encodedInputSizeNatTMBackedMap cnfStructuredEncodedType).tm_polytime
    have hInitInstr :
        TMPolyTimeMap X Instr
          (fun φ : X.Carrier => Sum.inl (cnfStructuredEncodedType.inputSize φ)) :=
      TMPolyTimeMap.comp (TMPolyTimeMap.inl EncodedType.nat clauseStructuredEncodedType) hSize
    have hInitSingleton :
        TMPolyTimeMap X (EncodedType.list Instr)
          (fun φ : X.Carrier => [Sum.inl (cnfStructuredEncodedType.inputSize φ)]) :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton Instr) hInitInstr
    have hClauseInstr :
        TMPolyTimeMap clauseStructuredEncodedType Instr
          (fun c : SAT.Clause => Sum.inr c) :=
      TMPolyTimeMap.inr EncodedType.nat clauseStructuredEncodedType
    have hTail :
        TMPolyTimeMap X (EncodedType.list Instr)
          (fun φ : X.Carrier => φ.map (fun c => Sum.inr c)) :=
      TMPolyTimeMap.list_map hClauseInstr
    have hPair :
        TMPolyTimeMap X
          (EncodedType.prod (EncodedType.list Instr) (EncodedType.list Instr))
          (fun φ : X.Carrier =>
            ([Sum.inl (cnfStructuredEncodedType.inputSize φ)],
              φ.map (fun c => Sum.inr c))) :=
      TMPolyTimeMap.prod_mk hInitSingleton hTail
    have hAppend :
        TMPolyTimeMap X (EncodedType.list Instr)
          (fun φ : X.Carrier =>
            [Sum.inl (cnfStructuredEncodedType.inputSize φ)] ++
              φ.map (fun c => Sum.inr c)) :=
      by
        have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append Instr) hPair
        simpa [Function.comp] using hComp
    simpa [cnfSplitRunnerInstructions] using hAppend

def cnfSplitRunnerInstructionsImageEncodedType : EncodedType where
  Carrier := cnfStructuredEncodedType.Carrier
  Symbol := (EncodedType.list cnfSplitInstructionEncodedType).Symbol
  finite_symbol := inferInstance
  encode := fun φ =>
    (EncodedType.list cnfSplitInstructionEncodedType).encode
      (cnfSplitRunnerInstructions φ)

noncomputable def cnfSplitRunnerInstructionsImageTMBackedMap :
    TMBackedCostedMap
      cnfStructuredEncodedType
      cnfSplitRunnerInstructionsImageEncodedType
      id where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := cnfStructuredEncodedType)
      (Y := cnfSplitRunnerInstructionsImageEncodedType)
      (LinearSizeBound.intro_with 3 3 (by
        intro φ
        change
          (EncodedType.list cnfSplitInstructionEncodedType).inputSize
              (cnfSplitRunnerInstructions φ) ≤
            3 * cnfStructuredEncodedType.inputSize φ + 3
        exact cnfSplitRunnerInstructions_inputSize_le φ))
  tm_polytime := by
    rcases cnfSplitRunnerInstructionsTMBackedMap.tm_polytime with ⟨hInstr⟩
    refine ⟨?_⟩
    exact
      { tm := hInstr.tm
        inputAlphabet := hInstr.inputAlphabet
        outputAlphabet := hInstr.outputAlphabet
        time := hInstr.time
        outputsFun := by
          intro φ
          simpa [cnfSplitRunnerInstructionsImageEncodedType] using hInstr.outputsFun φ }

theorem cnfSplitRunnerFoldImage_polynomialSizeBound :
    PolynomialSizeBound
      (fun φ : cnfSplitRunnerInstructionsImageEncodedType.Carrier =>
        cnfSplitRunnerInstructionsImageEncodedType.inputSize φ)
      (fun a : cnfSplitFoldAccEncodedType.Carrier =>
        cnfSplitFoldAccEncodedType.inputSize a)
      cnfSplitRunnerFold := by
  refine PolynomialSizeBound.intro_with 2 2000 2000 ?_
  intro φ
  rw [cnfSplitRunnerFold_eq_splitAux]
  have h :=
    cnfSplitPrefixAcc_inputSize_le_image_bound φ φ ([] : SAT.CNF) (by
      induction φ with
      | nil =>
          rfl
      | cons c cs ih =>
          change c :: (cs ++ []) = c :: cs
          exact congrArg (fun xs => c :: xs) ih)
  simpa [cnfSplitRunnerInstructionsImageEncodedType, pow_two] using h

noncomputable def cnfSplitRunnerFoldTimePolynomial
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod
          cnfSplitFoldAccEncodedType
          cnfSplitInstructionEncodedType).encode
        cnfSplitFoldAccEncodedType.encode
        cnfSplitFoldStep) : Polynomial Nat :=
  let B := cnfSplitRunnerFoldAccBoundPolynomial
  let T := hStep.time.comp (B + Polynomial.X + Polynomial.C 5)
  TM2Programs.listFoldBoundedTimePolynomial hStep.tm B T

theorem cnfSplitRunnerClauseFold_loopTime_le
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod
          cnfSplitFoldAccEncodedType
          cnfSplitInstructionEncodedType).encode
        cnfSplitFoldAccEncodedType.encode
        cnfSplitFoldStep)
    (φ pref rest : SAT.CNF) (hSource : pref ++ rest = φ) :
    TM2Programs.listFoldTypedLoopTime
        cnfSplitInstructionEncodedType
        cnfSplitFoldAccEncodedType
        cnfSplitFoldStep hStep
        (cnfStructuredEncodedType.inputSize φ + SAT.CNF.totalClauseLength pref,
          SAT.CNF.splitAux (cnfStructuredEncodedType.inputSize φ) pref)
        (rest.map (fun c => (Sum.inr c : cnfSplitInstructionEncodedType.Carrier))) ≤
      TM2Programs.listFoldBlockTimeCoeff hStep.tm
        (cnfSplitRunnerFoldAccBoundPolynomial.eval
          ((EncodedType.list cnfSplitInstructionEncodedType).inputSize
            (cnfSplitRunnerInstructions φ)))
        (hStep.time.eval
          (cnfSplitRunnerFoldAccBoundPolynomial.eval
              ((EncodedType.list cnfSplitInstructionEncodedType).inputSize
                (cnfSplitRunnerInstructions φ)) +
            (EncodedType.list cnfSplitInstructionEncodedType).inputSize
              (cnfSplitRunnerInstructions φ) + 5)) *
        TM2Programs.listFoldSourceLength cnfSplitInstructionEncodedType.encode
          (rest.map (fun c => (Sum.inr c : cnfSplitInstructionEncodedType.Carrier))) := by
  induction rest generalizing pref with
  | nil =>
      change 0 ≤
        TM2Programs.listFoldBlockTimeCoeff hStep.tm
            (cnfSplitRunnerFoldAccBoundPolynomial.eval
              ((EncodedType.list cnfSplitInstructionEncodedType).inputSize
                (cnfSplitRunnerInstructions φ)))
            (hStep.time.eval
              (cnfSplitRunnerFoldAccBoundPolynomial.eval
                  ((EncodedType.list cnfSplitInstructionEncodedType).inputSize
                    (cnfSplitRunnerInstructions φ)) +
                (EncodedType.list cnfSplitInstructionEncodedType).inputSize
                  (cnfSplitRunnerInstructions φ) + 5)) *
          TM2Programs.listFoldSourceLength cnfSplitInstructionEncodedType.encode
            (([] : List SAT.Clause).map
              (fun c => (Sum.inr c : cnfSplitInstructionEncodedType.Carrier)))
      exact Nat.zero_le _
  | cons c cs ih =>
      let S := cnfStructuredEncodedType.inputSize φ
      let N :=
        (EncodedType.list cnfSplitInstructionEncodedType).inputSize
          (cnfSplitRunnerInstructions φ)
      let B := cnfSplitRunnerFoldAccBoundPolynomial.eval N
      let T := hStep.time.eval (B + N + 5)
      let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
      let current : cnfSplitFoldAccEncodedType.Carrier :=
        (S + SAT.CNF.totalClauseLength pref, SAT.CNF.splitAux S pref)
      let next : cnfSplitFoldAccEncodedType.Carrier :=
        (S + SAT.CNF.totalClauseLength (pref ++ [c]), SAT.CNF.splitAux S (pref ++ [c]))
      have hSourceNext : (pref ++ [c]) ++ cs = φ := by
        have hAssoc : (pref ++ [c]) ++ cs = pref ++ c :: cs := by
          rw [List.append_assoc]
          rfl
        exact hAssoc.trans hSource
      have hStepAcc :
          cnfSplitFoldStep (current, (Sum.inr c : cnfSplitInstructionEncodedType.Carrier)) =
            next := by
        simpa [current, next, S] using cnfSplitPrefix_step_eq S pref c
      have hCur :
          cnfSplitFoldAccEncodedType.inputSize current ≤ B := by
        simpa [current, S, B, N] using
          cnfSplitPrefixAcc_inputSize_le_image_bound φ pref (c :: cs) hSource
      have hNext :
          cnfSplitFoldAccEncodedType.inputSize next ≤ B := by
        simpa [next, S, B, N] using
          cnfSplitPrefixAcc_inputSize_le_image_bound φ (pref ++ [c]) cs hSourceNext
      have hcSource : c ∈ φ := by
        rw [← hSource]
        exact List.mem_append.mpr (Or.inr (by simp))
      have hSN : S ≤ N := by
        dsimp [S, N]
        rw [cnfSplitRunnerInstructions, EncodedType.inputSize_list_cons]
        have hInit :
            cnfSplitInstructionEncodedType.inputSize
                (Sum.inl (cnfStructuredEncodedType.inputSize φ) :
                  cnfSplitInstructionEncodedType.Carrier) =
              cnfStructuredEncodedType.inputSize φ + 2 := by
          simp [cnfSplitInstructionEncodedType, EncodedType.inputSize, EncodedType.sum,
            EncodedType.nat]
        rw [hInit]
        omega
      have hClauseSize :=
        clauseStructured_inputSize_le_cnfStructured_inputSize_of_mem hcSource
      have hInstr :
          cnfSplitInstructionEncodedType.inputSize
              (Sum.inr c : cnfSplitInstructionEncodedType.Carrier) ≤ N + 2 := by
        have hClauseLen :
            (clauseStructuredEncodedType.encode c).length ≤ N := by
          simpa [EncodedType.inputSize] using le_trans hClauseSize hSN
        simp [cnfSplitInstructionEncodedType, EncodedType.inputSize, EncodedType.sum]
        omega
      have hStepTime :
          hStep.time.eval
              ((EncodedType.prod
                cnfSplitFoldAccEncodedType
                cnfSplitInstructionEncodedType).inputSize
                  (current, (Sum.inr c : cnfSplitInstructionEncodedType.Carrier))) ≤ T := by
        have hArg :
            (EncodedType.prod
              cnfSplitFoldAccEncodedType
              cnfSplitInstructionEncodedType).inputSize
                (current, (Sum.inr c : cnfSplitInstructionEncodedType.Carrier)) ≤
              B + N + 5 := by
          rw [EncodedType.inputSize_prod]
          nlinarith [hCur, hInstr]
        exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
      have hBlock :
          TM2Programs.listFoldBlockTime hStep.tm
              (cnfSplitInstructionEncodedType.encode
                (Sum.inr c : cnfSplitInstructionEncodedType.Carrier)).length
              (cnfSplitFoldAccEncodedType.encode current).length
              (cnfSplitFoldAccEncodedType.encode
                (cnfSplitFoldStep
                  (current, (Sum.inr c : cnfSplitInstructionEncodedType.Carrier)))).length
              (hStep.time.eval
                ((EncodedType.prod
                  cnfSplitFoldAccEncodedType
                  cnfSplitInstructionEncodedType).inputSize
                    (current, (Sum.inr c : cnfSplitInstructionEncodedType.Carrier)))) ≤
            C *
              ((cnfSplitInstructionEncodedType.encode
                (Sum.inr c : cnfSplitInstructionEncodedType.Carrier)).length + 1) := by
        exact
          TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
            (by simpa [EncodedType.inputSize] using hCur)
            (by simpa [EncodedType.inputSize, hStepAcc] using hNext)
            hStepTime
      have hTail := ih (pref ++ [c]) hSourceNext
      change
        TM2Programs.listFoldTypedLoopTime
            cnfSplitInstructionEncodedType
            cnfSplitFoldAccEncodedType
            cnfSplitFoldStep hStep current
            ((Sum.inr c : cnfSplitInstructionEncodedType.Carrier) ::
              cs.map (fun c => (Sum.inr c : cnfSplitInstructionEncodedType.Carrier))) ≤
          C *
            TM2Programs.listFoldSourceLength cnfSplitInstructionEncodedType.encode
              ((Sum.inr c : cnfSplitInstructionEncodedType.Carrier) ::
                cs.map (fun c => (Sum.inr c : cnfSplitInstructionEncodedType.Carrier)))
      simp [TM2Programs.listFoldTypedLoopTime, TM2Programs.listFoldSourceLength,
        hStepAcc, current, next, S, N, B, T, C] at hTail hBlock ⊢
      nlinarith [hTail, hBlock, Nat.zero_le C]

theorem cnfSplitRunnerFold_loopTime_le
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod
          cnfSplitFoldAccEncodedType
          cnfSplitInstructionEncodedType).encode
        cnfSplitFoldAccEncodedType.encode
        cnfSplitFoldStep)
    (φ : cnfSplitRunnerInstructionsImageEncodedType.Carrier) :
    2 +
        TM2Programs.listFoldTypedLoopTime
          cnfSplitInstructionEncodedType
          cnfSplitFoldAccEncodedType
          cnfSplitFoldStep hStep cnfSplitRunnerInit
          (cnfSplitRunnerInstructions φ) ≤
      (cnfSplitRunnerFoldTimePolynomial hStep).eval
        (cnfSplitRunnerInstructionsImageEncodedType.inputSize φ) := by
  let S := cnfStructuredEncodedType.inputSize φ
  let first : cnfSplitInstructionEncodedType.Carrier := Sum.inl S
  let tail : List cnfSplitInstructionEncodedType.Carrier :=
    φ.map (fun c => (Sum.inr c : cnfSplitInstructionEncodedType.Carrier))
  let N :=
    (EncodedType.list cnfSplitInstructionEncodedType).inputSize
      (cnfSplitRunnerInstructions φ)
  let B := cnfSplitRunnerFoldAccBoundPolynomial.eval N
  let T := hStep.time.eval (B + N + 5)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hImageSize : cnfSplitRunnerInstructionsImageEncodedType.inputSize φ = N := rfl
  have hInstrs : cnfSplitRunnerInstructions φ = first :: tail := by
    rfl
  have hEmptyCNFSize :
      cnfStructuredEncodedType.inputSize ([] : SAT.CNF) = 0 := by
    change ((EncodedType.list clauseStructuredEncodedType).encode ([] : SAT.CNF)).length = 0
    rfl
  have hInitAcc :
      cnfSplitFoldAccEncodedType.inputSize cnfSplitRunnerInit ≤ B := by
    change
      (EncodedType.prod EncodedType.nat cnfStructuredEncodedType).inputSize
          ((0 : Nat), ([] : SAT.CNF)) ≤ B
    rw [EncodedType.inputSize_prod, hEmptyCNFSize]
    simp [B, EncodedType.inputSize, EncodedType.nat]
  have hAfterFirst :
      cnfSplitFoldAccEncodedType.inputSize (S, ([] : SAT.CNF)) ≤ B := by
    have hSN : S ≤ N := by
      simpa [S, N] using cnfSplitRunnerInstructions_inputSize_ge_source φ
    change
      (EncodedType.prod EncodedType.nat cnfStructuredEncodedType).inputSize
          (S, ([] : SAT.CNF)) ≤ B
    rw [EncodedType.inputSize_prod, hEmptyCNFSize]
    simp [B, EncodedType.inputSize, EncodedType.nat]
    nlinarith [hSN, sq_nonneg (N : Int)]
  have hFirstInstr :
      cnfSplitInstructionEncodedType.inputSize first ≤ N := by
    dsimp [N, first, S]
    rw [cnfSplitRunnerInstructions, EncodedType.inputSize_list_cons]
    have hInit :
        cnfSplitInstructionEncodedType.inputSize
            (Sum.inl (cnfStructuredEncodedType.inputSize φ) :
              cnfSplitInstructionEncodedType.Carrier) =
          cnfStructuredEncodedType.inputSize φ + 2 := by
      simp [cnfSplitInstructionEncodedType, EncodedType.inputSize, EncodedType.sum,
        EncodedType.nat]
    rw [hInit]
    omega
  have hFirstStepTime :
      hStep.time.eval
          ((EncodedType.prod
            cnfSplitFoldAccEncodedType
            cnfSplitInstructionEncodedType).inputSize
              (cnfSplitRunnerInit, first)) ≤ T := by
    have hArg :
        (EncodedType.prod
          cnfSplitFoldAccEncodedType
          cnfSplitInstructionEncodedType).inputSize
            (cnfSplitRunnerInit, first) ≤ B + N + 5 := by
      rw [EncodedType.inputSize_prod]
      nlinarith [hInitAcc, hFirstInstr]
    exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
  have hFirstStep :
      cnfSplitFoldStep (cnfSplitRunnerInit, first) = (S, ([] : SAT.CNF)) := by
    rfl
  have hFirstBlock :
      TM2Programs.listFoldBlockTime hStep.tm
          (cnfSplitInstructionEncodedType.encode first).length
          (cnfSplitFoldAccEncodedType.encode cnfSplitRunnerInit).length
          (cnfSplitFoldAccEncodedType.encode
            (cnfSplitFoldStep (cnfSplitRunnerInit, first))).length
          (hStep.time.eval
            ((EncodedType.prod
              cnfSplitFoldAccEncodedType
              cnfSplitInstructionEncodedType).inputSize
                (cnfSplitRunnerInit, first))) ≤
        C * ((cnfSplitInstructionEncodedType.encode first).length + 1) := by
    exact
      TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
        (by simpa [EncodedType.inputSize] using hInitAcc)
        (by simpa [EncodedType.inputSize, hFirstStep] using hAfterFirst)
        hFirstStepTime
  have hTail :
      TM2Programs.listFoldTypedLoopTime
          cnfSplitInstructionEncodedType
          cnfSplitFoldAccEncodedType
          cnfSplitFoldStep hStep
          (S, ([] : SAT.CNF)) tail ≤
        C * TM2Programs.listFoldSourceLength cnfSplitInstructionEncodedType.encode tail := by
    simpa [S, N, B, T, C, tail] using
      cnfSplitRunnerClauseFold_loopTime_le hStep φ ([] : SAT.CNF) φ rfl
  have hSource :
      N =
        (cnfSplitInstructionEncodedType.encode first).length + 1 +
          TM2Programs.listFoldSourceLength cnfSplitInstructionEncodedType.encode tail := by
    calc
      N = (EncodedType.list cnfSplitInstructionEncodedType).inputSize (first :: tail) := by
            simp [N, hInstrs]
      _ =
          cnfSplitInstructionEncodedType.inputSize first + 1 +
            (EncodedType.list cnfSplitInstructionEncodedType).inputSize tail := by
            rw [EncodedType.inputSize_list_cons]
      _ =
          (cnfSplitInstructionEncodedType.encode first).length + 1 +
            TM2Programs.listFoldSourceLength cnfSplitInstructionEncodedType.encode tail := rfl
  have hLoop :
      TM2Programs.listFoldTypedLoopTime
          cnfSplitInstructionEncodedType
          cnfSplitFoldAccEncodedType
          cnfSplitFoldStep hStep cnfSplitRunnerInit
          (cnfSplitRunnerInstructions φ) ≤
        C * N := by
    calc
      TM2Programs.listFoldTypedLoopTime
          cnfSplitInstructionEncodedType
          cnfSplitFoldAccEncodedType
          cnfSplitFoldStep hStep cnfSplitRunnerInit
          (cnfSplitRunnerInstructions φ)
          =
        TM2Programs.listFoldTypedLoopTime
          cnfSplitInstructionEncodedType
          cnfSplitFoldAccEncodedType
          cnfSplitFoldStep hStep (cnfSplitFoldStep (cnfSplitRunnerInit, first)) tail +
        TM2Programs.listFoldBlockTime hStep.tm
          (cnfSplitInstructionEncodedType.encode first).length
          (cnfSplitFoldAccEncodedType.encode cnfSplitRunnerInit).length
          (cnfSplitFoldAccEncodedType.encode
            (cnfSplitFoldStep (cnfSplitRunnerInit, first))).length
          (hStep.time.eval
            ((EncodedType.prod
              cnfSplitFoldAccEncodedType
              cnfSplitInstructionEncodedType).inputSize
                (cnfSplitRunnerInit, first))) := by
            rw [hInstrs]
            rfl
      _ =
        TM2Programs.listFoldTypedLoopTime
          cnfSplitInstructionEncodedType
          cnfSplitFoldAccEncodedType
          cnfSplitFoldStep hStep (S, ([] : SAT.CNF)) tail +
        TM2Programs.listFoldBlockTime hStep.tm
          (cnfSplitInstructionEncodedType.encode first).length
          (cnfSplitFoldAccEncodedType.encode cnfSplitRunnerInit).length
          (cnfSplitFoldAccEncodedType.encode
            (cnfSplitFoldStep (cnfSplitRunnerInit, first))).length
          (hStep.time.eval
            ((EncodedType.prod
              cnfSplitFoldAccEncodedType
              cnfSplitInstructionEncodedType).inputSize
                (cnfSplitRunnerInit, first))) := by
            rw [hFirstStep]
            rfl
      _ ≤ C * TM2Programs.listFoldSourceLength cnfSplitInstructionEncodedType.encode tail +
            C * ((cnfSplitInstructionEncodedType.encode first).length + 1) :=
          Nat.add_le_add hTail hFirstBlock
      _ ≤ C * N := by
            nlinarith [hSource, Nat.zero_le C]
  rw [hImageSize]
  have hTimeEval :
      (cnfSplitRunnerFoldTimePolynomial hStep).eval N = (C + 2) * (N + 1) := by
    simp [cnfSplitRunnerFoldTimePolynomial, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval, TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_comp]
  rw [hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

noncomputable def cnfSplitRunnerFoldImageTMBackedMap :
    TMBackedCostedMap
      cnfSplitRunnerInstructionsImageEncodedType
      cnfSplitFoldAccEncodedType
      cnfSplitRunnerFold where
  costed := CostedMap.of_encodedPolynomialSizeBound
    cnfSplitRunnerFoldImage_polynomialSizeBound
  tm_polytime := by
    rcases cnfSplitFoldStepTMBackedMap.tm_polytime with ⟨hStep⟩
    let X := cnfSplitInstructionEncodedType
    let Y := cnfSplitFoldAccEncodedType
    refine ⟨?_⟩
    exact
      { tm :=
          TM2Programs.listFoldMachine X.Symbol Y.Symbol hStep.tm
            hStep.inputAlphabet.invFun hStep.outputAlphabet.toFun
            (Y.encode cnfSplitRunnerInit)
        inputAlphabet := Equiv.refl (Option X.Symbol)
        outputAlphabet := Equiv.refl Y.Symbol
        time := cnfSplitRunnerFoldTimePolynomial hStep
        outputsFun := by
          intro φ
          let xs := cnfSplitRunnerInstructions φ
          let machine :=
            TM2Programs.listFoldMachine X.Symbol Y.Symbol hStep.tm
              hStep.inputAlphabet.invFun hStep.outputAlphabet.toFun
              (Y.encode cnfSplitRunnerInit)
          have hRaw :=
            TM2Programs.listFoldTyped_outputsInTime X Y cnfSplitFoldStep
              cnfSplitRunnerInit hStep xs
          have hTime :
              2 + TM2Programs.listFoldTypedLoopTime X Y cnfSplitFoldStep
                    hStep cnfSplitRunnerInit xs ≤
                (cnfSplitRunnerFoldTimePolynomial hStep).eval
                  (cnfSplitRunnerInstructionsImageEncodedType.encode φ).length := by
            simpa [X, Y, xs, cnfSplitRunnerInstructionsImageEncodedType,
              EncodedType.inputSize] using
              cnfSplitRunnerFold_loopTime_le hStep φ
          have hMono := TM2Programs.evalsToInTime_mono hRaw hTime
          have hInput :
              List.map (Equiv.refl (Option X.Symbol)).invFun
                  (cnfSplitRunnerInstructionsImageEncodedType.encode φ) =
                (EncodedType.list X).encode xs := by
            change List.map id (cnfSplitRunnerInstructionsImageEncodedType.encode φ) =
              (EncodedType.list X).encode xs
            simp [X, xs, cnfSplitRunnerInstructionsImageEncodedType]
          have hOutput :
              List.map (Equiv.refl Y.Symbol).invFun
                  (Y.encode (cnfSplitRunnerFold φ)) =
                Y.encode (xs.foldl (fun acc instr => cnfSplitFoldStep (acc, instr))
                  cnfSplitRunnerInit) := by
            change List.map id (Y.encode (cnfSplitRunnerFold φ)) =
              Y.encode (xs.foldl (fun acc instr => cnfSplitFoldStep (acc, instr))
                cnfSplitRunnerInit)
            rw [List.map_id]
            rfl
          unfold Turing.TM2OutputsInTime
          convert hMono using 1
          · exact congrArg (Turing.initList machine) hInput
          · exact congrArg (Option.map (Turing.haltList machine)) (congrArg some hOutput) }

theorem cnfSplitRunnerFold_clauses_tm_polytime :
    TMPolyTimeMap
      cnfStructuredEncodedType
      cnfStructuredEncodedType
      (fun φ : SAT.CNF => (cnfSplitRunnerFold φ).2) := by
  have hFold :
      TMPolyTimeMap
        cnfStructuredEncodedType
        cnfSplitFoldAccEncodedType
        cnfSplitRunnerFold := by
    have hComp :=
      TMPolyTimeMap.comp
        cnfSplitRunnerFoldImageTMBackedMap.tm_polytime
        cnfSplitRunnerInstructionsImageTMBackedMap.tm_polytime
    simpa [Function.comp] using hComp
  have hSnd :
      TMPolyTimeMap
        cnfSplitFoldAccEncodedType
        cnfStructuredEncodedType
        (fun a : cnfSplitFoldAccEncodedType.Carrier => a.2) := by
    simpa [cnfSplitFoldAccEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat cnfStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp] using hComp

end Karp21
end ComplexityReduction
