import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Clique.Part2

namespace ComplexityReduction
namespace Karp21
namespace Clique

open ComplexityReduction.Combinatorics.Graph

def cliquePriorEdgeRunnerFoldImageEncodedType : EncodedType where
  Carrier := cliquePriorEdgeRunnerInstructionsImageEncodedType.Carrier
  Symbol := cliquePriorEdgeFoldAccEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun p => cliquePriorEdgeFoldAccEncodedType.encode (cliquePriorEdgeRunnerFold p)

theorem encodedList_element_inputSize_le {X : EncodedType} {x : X.Carrier}
    {xs : List X.Carrier} (hx : x ∈ xs) :
    X.inputSize x ≤ (EncodedType.list X).inputSize xs := by
  induction xs with
  | nil =>
      simp at hx
  | cons y ys ih =>
      rw [EncodedType.inputSize_list_cons]
      rcases List.mem_cons.mp hx with hxy | hxys
      · subst x
        omega
      · have hTail := ih hxys
        omega

theorem encodedList_inputSize_take_le (X : EncodedType) (k : Nat)
    (xs : List X.Carrier) :
    (EncodedType.list X).inputSize (xs.take k) ≤ (EncodedType.list X).inputSize xs := by
  induction xs generalizing k with
  | nil =>
      simp
  | cons x xs ih =>
      cases k with
      | zero =>
          simp
      | succ k =>
          change (EncodedType.list X).inputSize (x :: xs.take k) ≤
            (EncodedType.list X).inputSize (x :: xs)
          rw [EncodedType.inputSize_list_cons, EncodedType.inputSize_list_cons]
          exact Nat.add_le_add_left (ih k) (X.inputSize x + 1)

theorem cliquePriorEdgeFoldAcc_current_inputSize_le
    (acc : cliquePriorEdgeFoldAccEncodedType.Carrier) :
    indexedLiteralOccurrenceEncodedType.inputSize acc.2 ≤
      cliquePriorEdgeFoldAccEncodedType.inputSize acc := by
  rcases acc with ⟨edges, current⟩
  simp [cliquePriorEdgeFoldAccEncodedType, EncodedType.inputSize_prod]

theorem cliquePriorEdgeRunnerInitInstruction_init_inputSize_le
    (init : cliquePriorEdgeFoldAccEncodedType.Carrier) :
    cliquePriorEdgeFoldAccEncodedType.inputSize init ≤
      cliquePriorEdgeRunnerInstructionEncodedType.inputSize
        (cliquePriorEdgeRunnerInitInstruction init) := by
  simp [cliquePriorEdgeRunnerInitInstruction, cliquePriorEdgeRunnerInstructionEncodedType,
    cliquePriorEdgeRunnerInstructionPayloadEncodedType, EncodedType.inputSize_prod]
  omega

theorem cliquePriorEdgeRunnerPriorInstruction_prior_inputSize_le
    (prior : indexedLiteralOccurrenceEncodedType.Carrier) :
    indexedLiteralOccurrenceEncodedType.inputSize prior ≤
      cliquePriorEdgeRunnerInstructionEncodedType.inputSize
        (cliquePriorEdgeRunnerPriorInstruction prior) := by
  simp [cliquePriorEdgeRunnerPriorInstruction, cliquePriorEdgeRunnerInstructionEncodedType,
    cliquePriorEdgeRunnerInstructionPayloadEncodedType, EncodedType.inputSize_prod]
  omega

theorem cliquePriorEdgeRunnerPriorInstructions_inputSize_ge_prior
    (prior : List indexedLiteralOccurrenceEncodedType.Carrier) :
    (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize prior ≤
      (EncodedType.list cliquePriorEdgeRunnerInstructionEncodedType).inputSize
        (prior.map cliquePriorEdgeRunnerPriorInstruction) := by
  induction prior with
  | nil =>
      simp
  | cons prior rest ih =>
      rw [List.map_cons, EncodedType.inputSize_list_cons, EncodedType.inputSize_list_cons]
      have hPrior := cliquePriorEdgeRunnerPriorInstruction_prior_inputSize_le prior
      omega

theorem cliquePriorEdgeRunnerInstructions_inputSize_ge_init
    (init : cliquePriorEdgeFoldAccEncodedType.Carrier)
    (prior : List indexedLiteralOccurrenceEncodedType.Carrier) :
    cliquePriorEdgeFoldAccEncodedType.inputSize init ≤
      (EncodedType.list cliquePriorEdgeRunnerInstructionEncodedType).inputSize
        (cliquePriorEdgeRunnerInstructions init prior) := by
  have hInit := cliquePriorEdgeRunnerInitInstruction_init_inputSize_le init
  simp [cliquePriorEdgeRunnerInstructions, EncodedType.inputSize_list_cons] at hInit ⊢
  omega

theorem cliquePriorEdgeRunnerInstructions_inputSize_ge_prior
    (init : cliquePriorEdgeFoldAccEncodedType.Carrier)
    (prior : List indexedLiteralOccurrenceEncodedType.Carrier) :
    (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize prior ≤
      (EncodedType.list cliquePriorEdgeRunnerInstructionEncodedType).inputSize
        (cliquePriorEdgeRunnerInstructions init prior) := by
  have hPrior := cliquePriorEdgeRunnerPriorInstructions_inputSize_ge_prior prior
  simp [cliquePriorEdgeRunnerInstructions, EncodedType.inputSize_list_cons]
  omega

theorem cliquePriorEdgeRunnerInstructions_inputSize_ge_prior_length
    (init : cliquePriorEdgeFoldAccEncodedType.Carrier)
    (prior : List indexedLiteralOccurrenceEncodedType.Carrier) :
    prior.length ≤
      (EncodedType.list cliquePriorEdgeRunnerInstructionEncodedType).inputSize
        (cliquePriorEdgeRunnerInstructions init prior) := by
  have hLen := encodedList_length_le_inputSize indexedLiteralOccurrenceEncodedType prior
  have hPrior := cliquePriorEdgeRunnerInstructions_inputSize_ge_prior init prior
  omega

@[simp] theorem appendPriorCompatibleEdgeStep_current
    (acc : cliquePriorEdgeFoldAccEncodedType.Carrier)
    (prior : indexedLiteralOccurrenceEncodedType.Carrier) :
    (appendPriorCompatibleEdgeStep (acc, prior)).2 = acc.2 := by
  rfl

theorem cliquePriorEdgeRunnerPriorFold_current
    (acc : cliquePriorEdgeFoldAccEncodedType.Carrier)
    (prior : List indexedLiteralOccurrenceEncodedType.Carrier) :
    (prior.foldl
        (fun acc prior => cliquePriorEdgeRunnerStep (acc,
          cliquePriorEdgeRunnerPriorInstruction prior))
        acc).2 = acc.2 := by
  induction prior generalizing acc with
  | nil =>
      rfl
  | cons prior rest ih =>
      simpa [cliquePriorEdgeRunnerStep_prior] using
        ih (appendPriorCompatibleEdgeStep (acc, prior))

theorem cliquePriorEdgeRunnerPriorFold_inputSize_le_aux
    (current : indexedLiteralOccurrenceEncodedType.Carrier)
    (acc : cliquePriorEdgeFoldAccEncodedType.Carrier)
    (hCurrent : acc.2 = current)
    (prior : List indexedLiteralOccurrenceEncodedType.Carrier) :
    cliquePriorEdgeFoldAccEncodedType.inputSize
        (prior.foldl
          (fun acc prior => cliquePriorEdgeRunnerStep (acc,
            cliquePriorEdgeRunnerPriorInstruction prior))
          acc) ≤
      cliquePriorEdgeFoldAccEncodedType.inputSize acc +
        prior.length * (indexedLiteralOccurrenceEncodedType.inputSize current + 4) +
        (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize prior := by
  induction prior generalizing acc with
  | nil =>
      simp
  | cons prior rest ih =>
      have hStep :=
        cliquePriorEdgeRunnerStep_priorInstruction_inputSize_growth acc prior
      have hCurrentStep :
          (cliquePriorEdgeRunnerStep (acc,
            cliquePriorEdgeRunnerPriorInstruction prior)).2 = current := by
        simp [cliquePriorEdgeRunnerStep_prior, hCurrent]
      have hTail :=
        ih (cliquePriorEdgeRunnerStep (acc,
          cliquePriorEdgeRunnerPriorInstruction prior)) hCurrentStep
      rw [EncodedType.inputSize_list_cons]
      simp [cliquePriorEdgeRunnerStep_prior] at hStep hTail ⊢
      rw [hCurrent] at hStep
      nlinarith

theorem cliquePriorEdgeRunnerPriorFold_inputSize_le
    (init : cliquePriorEdgeFoldAccEncodedType.Carrier)
    (prior : List indexedLiteralOccurrenceEncodedType.Carrier) :
    cliquePriorEdgeFoldAccEncodedType.inputSize
        (prior.foldl
          (fun acc prior => cliquePriorEdgeRunnerStep (acc,
            cliquePriorEdgeRunnerPriorInstruction prior))
          init) ≤
      cliquePriorEdgeFoldAccEncodedType.inputSize init +
        prior.length * (indexedLiteralOccurrenceEncodedType.inputSize init.2 + 4) +
        (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize prior := by
  exact cliquePriorEdgeRunnerPriorFold_inputSize_le_aux init.2 init rfl prior

noncomputable def cliquePriorEdgeRunnerFoldAccBoundPolynomial : Polynomial Nat :=
  Polynomial.C 20 * (Polynomial.X * Polynomial.X) + Polynomial.C 100

@[simp] theorem cliquePriorEdgeRunnerFoldAccBoundPolynomial_eval (n : Nat) :
    cliquePriorEdgeRunnerFoldAccBoundPolynomial.eval n = 20 * (n * n) + 100 := by
  simp [cliquePriorEdgeRunnerFoldAccBoundPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_X]

theorem cliquePriorEdgeRunnerPriorFold_prefix_inputSize_le
    (init : cliquePriorEdgeFoldAccEncodedType.Carrier)
    (prior : List indexedLiteralOccurrenceEncodedType.Carrier)
    (k : Nat) (hk : k ≤ prior.length) :
    cliquePriorEdgeFoldAccEncodedType.inputSize
        ((prior.take k).foldl
          (fun acc prior => cliquePriorEdgeRunnerStep (acc,
            cliquePriorEdgeRunnerPriorInstruction prior))
          init) ≤
      cliquePriorEdgeRunnerFoldAccBoundPolynomial.eval
        ((EncodedType.list cliquePriorEdgeRunnerInstructionEncodedType).inputSize
          (cliquePriorEdgeRunnerInstructions init prior)) := by
  let N :=
    (EncodedType.list cliquePriorEdgeRunnerInstructionEncodedType).inputSize
      (cliquePriorEdgeRunnerInstructions init prior)
  have hFold := cliquePriorEdgeRunnerPriorFold_inputSize_le init (prior.take k)
  have hInit := cliquePriorEdgeRunnerInstructions_inputSize_ge_init init prior
  have hPrior := cliquePriorEdgeRunnerInstructions_inputSize_ge_prior init prior
  have hLen := cliquePriorEdgeRunnerInstructions_inputSize_ge_prior_length init prior
  have hCurrent : indexedLiteralOccurrenceEncodedType.inputSize init.2 ≤ N := by
    have hCur := cliquePriorEdgeFoldAcc_current_inputSize_le init
    omega
  have hInitN : cliquePriorEdgeFoldAccEncodedType.inputSize init ≤ N := by
    simpa [N] using hInit
  have hTakeLen : (prior.take k).length ≤ N := by
    have hTake : (prior.take k).length ≤ k := List.length_take_le k prior
    omega
  have hTakeInput :
      (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize (prior.take k) ≤ N := by
    have hTake := encodedList_inputSize_take_le indexedLiteralOccurrenceEncodedType k prior
    omega
  calc
    cliquePriorEdgeFoldAccEncodedType.inputSize
        ((prior.take k).foldl
          (fun acc prior => cliquePriorEdgeRunnerStep (acc,
            cliquePriorEdgeRunnerPriorInstruction prior))
          init)
        ≤ cliquePriorEdgeFoldAccEncodedType.inputSize init +
            (prior.take k).length *
              (indexedLiteralOccurrenceEncodedType.inputSize init.2 + 4) +
            (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize
              (prior.take k) := hFold
    _ ≤ 20 * (N * N) + 100 := by
          have hGrow :
              (prior.take k).length *
                  (indexedLiteralOccurrenceEncodedType.inputSize init.2 + 4) ≤
                N * (N + 4) :=
            Nat.mul_le_mul hTakeLen (Nat.add_le_add_right hCurrent 4)
          have hQuad : N + N * (N + 4) + N ≤ 20 * (N * N) + 100 := by
            nlinarith [sq_nonneg (N : Int)]
          nlinarith
    _ = cliquePriorEdgeRunnerFoldAccBoundPolynomial.eval
          ((EncodedType.list cliquePriorEdgeRunnerInstructionEncodedType).inputSize
            (cliquePriorEdgeRunnerInstructions init prior)) := by
          simp [N]

theorem cliquePriorEdgeRunnerFold_inputSize_le
    (p : cliquePriorEdgeRunnerInstructionsImageEncodedType.Carrier) :
    cliquePriorEdgeFoldAccEncodedType.inputSize (cliquePriorEdgeRunnerFold p) ≤
      cliquePriorEdgeRunnerFoldAccBoundPolynomial.eval
        (cliquePriorEdgeRunnerInstructionsImageEncodedType.inputSize p) := by
  rcases p with ⟨init, prior⟩
  have hPrefix :=
    cliquePriorEdgeRunnerPriorFold_prefix_inputSize_le init prior prior.length (by simp)
  simpa [cliquePriorEdgeRunnerFold, cliquePriorEdgeRunnerInstructions_fold_eq,
    cliquePriorEdgeRunnerInstructionsImageEncodedType] using hPrefix

theorem cliquePriorEdgeRunnerFoldImage_polynomialSizeBound :
    PolynomialSizeBound
      (fun p : cliquePriorEdgeRunnerInstructionsImageEncodedType.Carrier =>
        cliquePriorEdgeRunnerInstructionsImageEncodedType.inputSize p)
      (fun p : cliquePriorEdgeRunnerFoldImageEncodedType.Carrier =>
        cliquePriorEdgeRunnerFoldImageEncodedType.inputSize p)
      id := by
  refine PolynomialSizeBound.intro_with 2 20 100 ?_
  intro p
  change cliquePriorEdgeFoldAccEncodedType.inputSize (cliquePriorEdgeRunnerFold p) ≤
    20 * (cliquePriorEdgeRunnerInstructionsImageEncodedType.inputSize p) ^ 2 + 100
  simpa [pow_two] using cliquePriorEdgeRunnerFold_inputSize_le p

theorem cliquePriorEdgeFoldInit_inputSize_le_100 :
    cliquePriorEdgeFoldAccEncodedType.inputSize cliquePriorEdgeFoldInit ≤ 100 := by
  simp [cliquePriorEdgeFoldInit, defaultIndexedLiteralOccurrence, defaultOccurrence,
    cliquePriorEdgeFoldAccEncodedType, indexedLiteralOccurrenceEncodedType,
    literalOccurrenceStructuredEncodedType, literalOccurrenceToTuple,
    literalOccurrenceTupleStructuredEncodedType, literalStructuredEncodedType,
    literalTupleStructuredEncodedType, SAT.Literal.positive, EncodedType.inputSize,
    EncodedType.prod, EncodedType.list, EncodedType.nat, EncodedType.bool]

theorem cliquePriorEdgeRunnerPriorInstructions_loopTime_le
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod
          cliquePriorEdgeFoldAccEncodedType
          cliquePriorEdgeRunnerInstructionEncodedType).encode
        cliquePriorEdgeFoldAccEncodedType.encode
        cliquePriorEdgeRunnerStep)
    (priors : List indexedLiteralOccurrenceEncodedType.Carrier)
    (init : cliquePriorEdgeFoldAccEncodedType.Carrier) (B T : Nat)
    (hAcc : ∀ k, k ≤ priors.length →
      cliquePriorEdgeFoldAccEncodedType.inputSize
        ((priors.take k).foldl
          (fun acc occ => cliquePriorEdgeRunnerStep (acc,
            cliquePriorEdgeRunnerPriorInstruction occ))
          init) ≤ B)
    (hStepTime : ∀ b occ,
      cliquePriorEdgeFoldAccEncodedType.inputSize b ≤ B →
        List.Mem occ priors →
          hStep.time.eval
            ((EncodedType.prod
              cliquePriorEdgeFoldAccEncodedType
              cliquePriorEdgeRunnerInstructionEncodedType).inputSize
                (b, cliquePriorEdgeRunnerPriorInstruction occ)) ≤ T) :
    TM2Programs.listFoldTypedLoopTime
        cliquePriorEdgeRunnerInstructionEncodedType
        cliquePriorEdgeFoldAccEncodedType
        cliquePriorEdgeRunnerStep hStep init
        (priors.map cliquePriorEdgeRunnerPriorInstruction) ≤
      TM2Programs.listFoldBlockTimeCoeff hStep.tm B T *
        TM2Programs.listFoldSourceLength cliquePriorEdgeRunnerInstructionEncodedType.encode
          (priors.map cliquePriorEdgeRunnerPriorInstruction) := by
  induction priors generalizing init with
  | nil =>
      simp [TM2Programs.listFoldTypedLoopTime, TM2Programs.listFoldSourceLength]
  | cons prior rest ih =>
      have hAcc0 : cliquePriorEdgeFoldAccEncodedType.inputSize init ≤ B := by
        simpa using hAcc 0 (by simp)
      have hAcc1 :
          cliquePriorEdgeFoldAccEncodedType.inputSize
              (cliquePriorEdgeRunnerStep
                (init, cliquePriorEdgeRunnerPriorInstruction prior)) ≤ B := by
        simpa using hAcc 1 (by simp)
      have hTailAcc : ∀ k, k ≤ rest.length →
          cliquePriorEdgeFoldAccEncodedType.inputSize
            ((rest.take k).foldl
              (fun acc occ => cliquePriorEdgeRunnerStep (acc,
                cliquePriorEdgeRunnerPriorInstruction occ))
              (cliquePriorEdgeRunnerStep
                (init, cliquePriorEdgeRunnerPriorInstruction prior))) ≤ B := by
        intro k hk
        have hk' : k + 1 ≤ (prior :: rest).length := by
          simp
          omega
        simpa [List.take, Nat.succ_eq_add_one] using hAcc (k + 1) hk'
      have hTailStepTime : ∀ b prior',
          cliquePriorEdgeFoldAccEncodedType.inputSize b ≤ B →
            List.Mem prior' rest →
              hStep.time.eval
                ((EncodedType.prod
                  cliquePriorEdgeFoldAccEncodedType
                  cliquePriorEdgeRunnerInstructionEncodedType).inputSize
                    (b, cliquePriorEdgeRunnerPriorInstruction prior')) ≤ T := by
        intro b prior' hb hmem
        exact hStepTime b prior' hb (List.mem_cons_of_mem prior hmem)
      have hTail :=
        ih (cliquePriorEdgeRunnerStep
          (init, cliquePriorEdgeRunnerPriorInstruction prior)) hTailAcc hTailStepTime
      have hBlock :
          TM2Programs.listFoldBlockTime hStep.tm
              (cliquePriorEdgeRunnerInstructionEncodedType.encode
                (cliquePriorEdgeRunnerPriorInstruction prior)).length
              (cliquePriorEdgeFoldAccEncodedType.encode init).length
              (cliquePriorEdgeFoldAccEncodedType.encode
                (cliquePriorEdgeRunnerStep
                  (init, cliquePriorEdgeRunnerPriorInstruction prior))).length
              (hStep.time.eval
                ((EncodedType.prod
                  cliquePriorEdgeFoldAccEncodedType
                  cliquePriorEdgeRunnerInstructionEncodedType).inputSize
                    (init, cliquePriorEdgeRunnerPriorInstruction prior))) ≤
            TM2Programs.listFoldBlockTimeCoeff hStep.tm B T *
              ((cliquePriorEdgeRunnerInstructionEncodedType.encode
                (cliquePriorEdgeRunnerPriorInstruction prior)).length + 1) := by
        exact
          TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
            (by simpa [EncodedType.inputSize] using hAcc0)
            (by simpa [EncodedType.inputSize] using hAcc1)
            (hStepTime init prior hAcc0 (by
              exact List.mem_cons_self))
      simp [TM2Programs.listFoldTypedLoopTime, TM2Programs.listFoldSourceLength] at hTail hBlock ⊢
      nlinarith [hTail, hBlock]

noncomputable def cliquePriorEdgeRunnerFoldTimePolynomial
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod
          cliquePriorEdgeFoldAccEncodedType
          cliquePriorEdgeRunnerInstructionEncodedType).encode
        cliquePriorEdgeFoldAccEncodedType.encode
        cliquePriorEdgeRunnerStep) : Polynomial Nat :=
  let B := cliquePriorEdgeRunnerFoldAccBoundPolynomial
  let T := hStep.time.comp (B + Polynomial.X + Polynomial.C 2)
  TM2Programs.listFoldBoundedTimePolynomial hStep.tm B T

theorem cliquePriorEdgeRunnerFold_loopTime_le
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod
          cliquePriorEdgeFoldAccEncodedType
          cliquePriorEdgeRunnerInstructionEncodedType).encode
        cliquePriorEdgeFoldAccEncodedType.encode
        cliquePriorEdgeRunnerStep)
    (p : cliquePriorEdgeRunnerInstructionsImageEncodedType.Carrier) :
    2 +
        TM2Programs.listFoldTypedLoopTime
          cliquePriorEdgeRunnerInstructionEncodedType
          cliquePriorEdgeFoldAccEncodedType
          cliquePriorEdgeRunnerStep hStep cliquePriorEdgeFoldInit
          (cliquePriorEdgeRunnerInstructions p.1 p.2) ≤
      (cliquePriorEdgeRunnerFoldTimePolynomial hStep).eval
        (cliquePriorEdgeRunnerInstructionsImageEncodedType.inputSize p) := by
  rcases p with ⟨init, prior⟩
  let first : cliquePriorEdgeRunnerInstructionEncodedType.Carrier :=
    cliquePriorEdgeRunnerInitInstruction init
  let tail : List cliquePriorEdgeRunnerInstructionEncodedType.Carrier :=
    prior.map cliquePriorEdgeRunnerPriorInstruction
  let N :=
    (EncodedType.list cliquePriorEdgeRunnerInstructionEncodedType).inputSize
      (cliquePriorEdgeRunnerInstructions init prior)
  let B := cliquePriorEdgeRunnerFoldAccBoundPolynomial.eval N
  let T := hStep.time.eval (B + N + 2)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hImageSize :
      cliquePriorEdgeRunnerInstructionsImageEncodedType.inputSize (init, prior) = N := rfl
  have hInitN := cliquePriorEdgeRunnerInstructions_inputSize_ge_init init prior
  have hBgeN : N ≤ B := by
    simp [B]
    nlinarith [sq_nonneg (N : Int)]
  have hDefaultAcc :
      cliquePriorEdgeFoldAccEncodedType.inputSize cliquePriorEdgeFoldInit ≤ B := by
    exact le_trans cliquePriorEdgeFoldInit_inputSize_le_100 (by simp [B])
  have hAfterInit : cliquePriorEdgeFoldAccEncodedType.inputSize init ≤ B := by
    have h : cliquePriorEdgeFoldAccEncodedType.inputSize init ≤ N := by
      simpa [N] using hInitN
    omega
  have hTailAcc : ∀ k, k ≤ prior.length →
      cliquePriorEdgeFoldAccEncodedType.inputSize
        ((prior.take k).foldl
          (fun acc prior => cliquePriorEdgeRunnerStep (acc,
            cliquePriorEdgeRunnerPriorInstruction prior))
          init) ≤ B := by
    intro k hk
    simpa [B, N] using cliquePriorEdgeRunnerPriorFold_prefix_inputSize_le init prior k hk
  have hTailStepTime : ∀ b prior',
      cliquePriorEdgeFoldAccEncodedType.inputSize b ≤ B →
        List.Mem prior' (prior : List indexedLiteralOccurrenceEncodedType.Carrier) →
          hStep.time.eval
            ((EncodedType.prod
              cliquePriorEdgeFoldAccEncodedType
              cliquePriorEdgeRunnerInstructionEncodedType).inputSize
                (b, cliquePriorEdgeRunnerPriorInstruction prior')) ≤ T := by
    intro b prior' hb hmem
    have hInstrMem :
        cliquePriorEdgeRunnerPriorInstruction prior' ∈
          cliquePriorEdgeRunnerInstructions init prior := by
      exact List.mem_append.mpr
        (Or.inr (List.mem_map.mpr ⟨prior', hmem, rfl⟩))
    have hInstrSize :
        cliquePriorEdgeRunnerInstructionEncodedType.inputSize
            (cliquePriorEdgeRunnerPriorInstruction prior') ≤ N := by
      simpa [N] using
        encodedList_element_inputSize_le
          (X := cliquePriorEdgeRunnerInstructionEncodedType) hInstrMem
    have hArg :
        (EncodedType.prod
          cliquePriorEdgeFoldAccEncodedType
          cliquePriorEdgeRunnerInstructionEncodedType).inputSize
            (b, cliquePriorEdgeRunnerPriorInstruction prior') ≤ B + N + 2 := by
      rw [EncodedType.inputSize_prod]
      change cliquePriorEdgeFoldAccEncodedType.inputSize b + 1 +
        cliquePriorEdgeRunnerInstructionEncodedType.inputSize
          (cliquePriorEdgeRunnerPriorInstruction prior') ≤ B + N + 2
      omega
    exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
  have hTailLoop :=
    cliquePriorEdgeRunnerPriorInstructions_loopTime_le hStep
      (prior : List indexedLiteralOccurrenceEncodedType.Carrier) init B T
      hTailAcc hTailStepTime
  have hFirstMem : first ∈ cliquePriorEdgeRunnerInstructions init prior := by
    simp [first, cliquePriorEdgeRunnerInstructions]
  have hFirstInstrSize :
      cliquePriorEdgeRunnerInstructionEncodedType.inputSize first ≤ N := by
    simpa [N] using
      encodedList_element_inputSize_le
        (X := cliquePriorEdgeRunnerInstructionEncodedType) hFirstMem
  have hFirstStepTime :
      hStep.time.eval
          ((EncodedType.prod
            cliquePriorEdgeFoldAccEncodedType
            cliquePriorEdgeRunnerInstructionEncodedType).inputSize
              (cliquePriorEdgeFoldInit, first)) ≤ T := by
    have hArg :
        (EncodedType.prod
          cliquePriorEdgeFoldAccEncodedType
          cliquePriorEdgeRunnerInstructionEncodedType).inputSize
            (cliquePriorEdgeFoldInit, first) ≤ B + N + 2 := by
      rw [EncodedType.inputSize_prod]
      change cliquePriorEdgeFoldAccEncodedType.inputSize cliquePriorEdgeFoldInit + 1 +
        cliquePriorEdgeRunnerInstructionEncodedType.inputSize first ≤ B + N + 2
      omega
    exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
  have hFirstBlock :
      TM2Programs.listFoldBlockTime hStep.tm
          (cliquePriorEdgeRunnerInstructionEncodedType.encode first).length
          (cliquePriorEdgeFoldAccEncodedType.encode cliquePriorEdgeFoldInit).length
          (cliquePriorEdgeFoldAccEncodedType.encode
            (cliquePriorEdgeRunnerStep (cliquePriorEdgeFoldInit, first))).length
          (hStep.time.eval
            ((EncodedType.prod
              cliquePriorEdgeFoldAccEncodedType
              cliquePriorEdgeRunnerInstructionEncodedType).inputSize
                (cliquePriorEdgeFoldInit, first))) ≤
        C * ((cliquePriorEdgeRunnerInstructionEncodedType.encode first).length + 1) := by
    exact
      TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
        (by simpa [EncodedType.inputSize] using hDefaultAcc)
        (by simpa [first, EncodedType.inputSize] using hAfterInit)
        hFirstStepTime
  have hInstrs :
      cliquePriorEdgeRunnerInstructions init prior = first :: tail := by
    simp [cliquePriorEdgeRunnerInstructions, first, tail]
  have hTailLoop' :
      TM2Programs.listFoldTypedLoopTime
          cliquePriorEdgeRunnerInstructionEncodedType
          cliquePriorEdgeFoldAccEncodedType
          cliquePriorEdgeRunnerStep hStep init tail ≤
        C * TM2Programs.listFoldSourceLength
          cliquePriorEdgeRunnerInstructionEncodedType.encode tail := by
    simpa [tail] using hTailLoop
  have hSource :
      N =
        (cliquePriorEdgeRunnerInstructionEncodedType.encode first).length + 1 +
          TM2Programs.listFoldSourceLength
            cliquePriorEdgeRunnerInstructionEncodedType.encode tail := by
    calc
      N = (EncodedType.list cliquePriorEdgeRunnerInstructionEncodedType).inputSize
            (first :: tail) := by
              simp [N, hInstrs]
      _ = cliquePriorEdgeRunnerInstructionEncodedType.inputSize first + 1 +
            (EncodedType.list cliquePriorEdgeRunnerInstructionEncodedType).inputSize tail := by
              rw [EncodedType.inputSize_list_cons]
      _ =
          (cliquePriorEdgeRunnerInstructionEncodedType.encode first).length + 1 +
            TM2Programs.listFoldSourceLength
              cliquePriorEdgeRunnerInstructionEncodedType.encode tail := rfl
  have hLoop :
      TM2Programs.listFoldTypedLoopTime
          cliquePriorEdgeRunnerInstructionEncodedType
          cliquePriorEdgeFoldAccEncodedType
          cliquePriorEdgeRunnerStep hStep cliquePriorEdgeFoldInit
          (cliquePriorEdgeRunnerInstructions init prior) ≤
        C * N := by
    have hFirstStep :
        cliquePriorEdgeRunnerStep (cliquePriorEdgeFoldInit, first) = init := by
      simp [first]
    calc
      TM2Programs.listFoldTypedLoopTime
          cliquePriorEdgeRunnerInstructionEncodedType
          cliquePriorEdgeFoldAccEncodedType
          cliquePriorEdgeRunnerStep hStep cliquePriorEdgeFoldInit
          (cliquePriorEdgeRunnerInstructions init prior)
          =
        TM2Programs.listFoldTypedLoopTime
          cliquePriorEdgeRunnerInstructionEncodedType
          cliquePriorEdgeFoldAccEncodedType
          cliquePriorEdgeRunnerStep hStep
          (cliquePriorEdgeRunnerStep (cliquePriorEdgeFoldInit, first))
          tail +
        TM2Programs.listFoldBlockTime hStep.tm
          (cliquePriorEdgeRunnerInstructionEncodedType.encode first).length
          (cliquePriorEdgeFoldAccEncodedType.encode cliquePriorEdgeFoldInit).length
          (cliquePriorEdgeFoldAccEncodedType.encode
            (cliquePriorEdgeRunnerStep (cliquePriorEdgeFoldInit, first))).length
          (hStep.time.eval
            ((EncodedType.prod
              cliquePriorEdgeFoldAccEncodedType
              cliquePriorEdgeRunnerInstructionEncodedType).inputSize
                (cliquePriorEdgeFoldInit, first))) := by
            rw [hInstrs]
            rfl
      _ =
        TM2Programs.listFoldTypedLoopTime
          cliquePriorEdgeRunnerInstructionEncodedType
          cliquePriorEdgeFoldAccEncodedType
          cliquePriorEdgeRunnerStep hStep init tail +
        TM2Programs.listFoldBlockTime hStep.tm
          (cliquePriorEdgeRunnerInstructionEncodedType.encode first).length
          (cliquePriorEdgeFoldAccEncodedType.encode cliquePriorEdgeFoldInit).length
          (cliquePriorEdgeFoldAccEncodedType.encode
            (cliquePriorEdgeRunnerStep (cliquePriorEdgeFoldInit, first))).length
          (hStep.time.eval
            ((EncodedType.prod
              cliquePriorEdgeFoldAccEncodedType
              cliquePriorEdgeRunnerInstructionEncodedType).inputSize
                (cliquePriorEdgeFoldInit, first))) := by
            rw [hFirstStep]
      _ ≤ C *
            TM2Programs.listFoldSourceLength
              cliquePriorEdgeRunnerInstructionEncodedType.encode tail +
          C * ((cliquePriorEdgeRunnerInstructionEncodedType.encode first).length + 1) :=
            Nat.add_le_add hTailLoop' hFirstBlock
      _ ≤ C * N := by
            nlinarith [hSource, Nat.zero_le C]
  rw [hImageSize]
  have hTimeEval :
      (cliquePriorEdgeRunnerFoldTimePolynomial hStep).eval N = (C + 2) * (N + 1) := by
    simp [cliquePriorEdgeRunnerFoldTimePolynomial, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval, TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_comp]
  rw [hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

theorem cliquePriorEdgeRunnerFoldImage_tm_polytime :
    TMPolyTimeMap
      cliquePriorEdgeRunnerInstructionsImageEncodedType
      cliquePriorEdgeRunnerFoldImageEncodedType
      id := by
  rcases cliquePriorEdgeRunnerStep_tm_polytime with ⟨hStep⟩
  let X := cliquePriorEdgeRunnerInstructionEncodedType
  let Y := cliquePriorEdgeFoldAccEncodedType
  refine ⟨?_⟩
  exact
    { tm :=
        TM2Programs.listFoldMachine X.Symbol Y.Symbol hStep.tm
          hStep.inputAlphabet.invFun hStep.outputAlphabet.toFun
          (Y.encode cliquePriorEdgeFoldInit)
      inputAlphabet := Equiv.refl (Option X.Symbol)
      outputAlphabet := Equiv.refl Y.Symbol
      time := cliquePriorEdgeRunnerFoldTimePolynomial hStep
      outputsFun := by
        intro p
        let xs := cliquePriorEdgeRunnerInstructions p.1 p.2
        let machine :=
          TM2Programs.listFoldMachine X.Symbol Y.Symbol hStep.tm
            hStep.inputAlphabet.invFun hStep.outputAlphabet.toFun
            (Y.encode cliquePriorEdgeFoldInit)
        have hRaw :=
          TM2Programs.listFoldTyped_outputsInTime X Y cliquePriorEdgeRunnerStep
            cliquePriorEdgeFoldInit hStep xs
        have hTime :
            2 + TM2Programs.listFoldTypedLoopTime X Y cliquePriorEdgeRunnerStep
                  hStep cliquePriorEdgeFoldInit xs ≤
              (cliquePriorEdgeRunnerFoldTimePolynomial hStep).eval
                (cliquePriorEdgeRunnerInstructionsImageEncodedType.encode p).length := by
          simpa [X, Y, xs, cliquePriorEdgeRunnerInstructionsImageEncodedType,
            EncodedType.inputSize] using
            cliquePriorEdgeRunnerFold_loopTime_le hStep p
        have hMono := TM2Programs.evalsToInTime_mono hRaw hTime
        have hInput :
            List.map (Equiv.refl (Option X.Symbol)).invFun
                (cliquePriorEdgeRunnerInstructionsImageEncodedType.encode p) =
              (EncodedType.list X).encode xs := by
          change List.map id (cliquePriorEdgeRunnerInstructionsImageEncodedType.encode p) =
            (EncodedType.list X).encode xs
          simp [X, xs, cliquePriorEdgeRunnerInstructionsImageEncodedType]
        have hOutput :
            List.map (Equiv.refl Y.Symbol).invFun
                (cliquePriorEdgeRunnerFoldImageEncodedType.encode (id p)) =
              Y.encode (xs.foldl (fun acc instr => cliquePriorEdgeRunnerStep (acc, instr))
                cliquePriorEdgeFoldInit) := by
          change List.map id (cliquePriorEdgeRunnerFoldImageEncodedType.encode p) =
            Y.encode (xs.foldl (fun acc instr => cliquePriorEdgeRunnerStep (acc, instr))
              cliquePriorEdgeFoldInit)
          simp [Y, xs, cliquePriorEdgeRunnerFoldImageEncodedType,
            cliquePriorEdgeRunnerFold]
        unfold Turing.TM2OutputsInTime
        convert hMono using 1
        · exact congrArg (Turing.initList machine) hInput
        · exact congrArg (Option.map (Turing.haltList machine)) (congrArg some hOutput) }

theorem cliquePriorEdgeRunnerFoldFromImage_tm_polytime :
    TMPolyTimeMap
      cliquePriorEdgeRunnerFoldImageEncodedType
      cliquePriorEdgeFoldAccEncodedType
      cliquePriorEdgeRunnerFold :=
  TMPolyTimeMap.of_encodingEquiv
    cliquePriorEdgeRunnerFoldImageEncodedType
    cliquePriorEdgeFoldAccEncodedType
    cliquePriorEdgeRunnerFold
    (Equiv.refl _)
    (by
      intro p
      change cliquePriorEdgeFoldAccEncodedType.encode (cliquePriorEdgeRunnerFold p) =
        (cliquePriorEdgeRunnerFoldImageEncodedType.encode p).map id
      simp [cliquePriorEdgeRunnerFoldImageEncodedType])

noncomputable def cliquePriorEdgeRunnerFoldImageTMBackedMap :
    TMBackedCostedMap
      cliquePriorEdgeRunnerInstructionsImageEncodedType
      cliquePriorEdgeRunnerFoldImageEncodedType
      id where
  costed := CostedMap.of_encodedPolynomialSizeBound
    cliquePriorEdgeRunnerFoldImage_polynomialSizeBound
  tm_polytime := cliquePriorEdgeRunnerFoldImage_tm_polytime

noncomputable def cliquePriorEdgeRunnerFoldFromImageTMBackedMap :
    TMBackedCostedMap
      cliquePriorEdgeRunnerFoldImageEncodedType
      cliquePriorEdgeFoldAccEncodedType
      cliquePriorEdgeRunnerFold :=
  TMBackedCostedMap.ofEncodingEquiv
    cliquePriorEdgeRunnerFoldImageEncodedType
    cliquePriorEdgeFoldAccEncodedType
    cliquePriorEdgeRunnerFold
    (Equiv.refl _)
    (by
      intro p
      change cliquePriorEdgeFoldAccEncodedType.encode (cliquePriorEdgeRunnerFold p) =
        (cliquePriorEdgeRunnerFoldImageEncodedType.encode p).map id
      simp [cliquePriorEdgeRunnerFoldImageEncodedType])

theorem literal_compatible_of_eval_true {a : SAT.Assignment} {l₁ l₂ : SAT.Literal}
    (h₁ : l₁.eval a = true) (h₂ : l₂.eval a = true) :
    l₁.var ≠ l₂.var ∨ l₁.neg = l₂.neg := by
  cases l₁ with
  | mk v₁ n₁ =>
      cases l₂ with
      | mk v₂ n₂ =>
          by_cases hv : v₁ = v₂
          · subst v₂
            right
            cases n₁ <;> cases n₂ <;> simp_all [SAT.Literal.eval]
          · exact Or.inl hv

theorem literal_compatible_symm {l₁ l₂ : SAT.Literal}
    (h : l₁.var ≠ l₂.var ∨ l₁.neg = l₂.neg) :
    l₂.var ≠ l₁.var ∨ l₂.neg = l₁.neg := by
  rcases h with h | h
  · exact Or.inl (Ne.symm h)
  · exact Or.inr h.symm

theorem occurrenceCompatible_symm {a b : LiteralOccurrence}
    (h : occurrenceCompatible a b) :
    occurrenceCompatible b a :=
  ⟨Ne.symm h.1, literal_compatible_symm h.2⟩

theorem mem_compatibleEdgesFromHead_iff
    (head : indexedLiteralOccurrenceEncodedType.Carrier)
    (rest : List indexedLiteralOccurrenceEncodedType.Carrier)
    (e : edgeStructuredEncodedType.Carrier) :
    e ∈ compatibleEdgesFromHead head rest ↔
      ∃ current ∈ rest, e = (head.1, current.1) ∧
        occurrenceCompatible head.2 current.2 := by
  induction rest with
  | nil =>
      simp [compatibleEdgesFromHead]
  | cons current rest ih =>
      by_cases hCompatBool : occurrenceCompatibleBool (head.2, current.2) = true
      · have hCompat :
            occurrenceCompatible head.2 current.2 :=
          (occurrenceCompatibleBool_eq_true_iff (head.2, current.2)).1 hCompatBool
        simp [compatibleEdgesFromHead, hCompatBool, ih, hCompat]
      · have hNotCompat :
            ¬ occurrenceCompatible head.2 current.2 := by
          intro hCompat
          exact hCompatBool
            ((occurrenceCompatibleBool_eq_true_iff (head.2, current.2)).2 hCompat)
        simp [compatibleEdgesFromHead, hCompatBool, ih, hNotCompat]

theorem mem_compatibleEdgesFromHead_of_mem
    {head current : indexedLiteralOccurrenceEncodedType.Carrier}
    {rest : List indexedLiteralOccurrenceEncodedType.Carrier}
    (hCurrent : current ∈ rest)
    (hCompat : occurrenceCompatible head.2 current.2) :
    (head.1, current.1) ∈ compatibleEdgesFromHead head rest :=
  (mem_compatibleEdgesFromHead_iff head rest (head.1, current.1)).2
    ⟨current, hCurrent, rfl, hCompat⟩

theorem mem_compatibleEdgesFromIndexedOccurrences_info
    {xs : List indexedLiteralOccurrenceEncodedType.Carrier}
    {e : edgeStructuredEncodedType.Carrier}
    (he : e ∈ compatibleEdgesFromIndexedOccurrences xs) :
    ∃ a ∈ xs, ∃ b ∈ xs, e = (a.1, b.1) ∧ occurrenceCompatible a.2 b.2 := by
  induction xs with
  | nil =>
      simp [compatibleEdgesFromIndexedOccurrences] at he
  | cons head rest ih =>
      simp [compatibleEdgesFromIndexedOccurrences] at he
      rcases he with hHead | hRest
      · rcases (mem_compatibleEdgesFromHead_iff head rest e).1 hHead with
          ⟨current, hCurrent, hEdge, hCompat⟩
        exact ⟨head, by simp, current, by simp [hCurrent], hEdge, hCompat⟩
      · rcases ih hRest with ⟨a, ha, b, hb, hEdge, hCompat⟩
        exact ⟨a, by simp [ha], b, by simp [hb], hEdge, hCompat⟩

theorem hasUndirectedEdge_compatibleEdgesFromIndexedOccurrences_of_mem
    {xs : List indexedLiteralOccurrenceEncodedType.Carrier}
    {x y : indexedLiteralOccurrenceEncodedType.Carrier}
    (hx : x ∈ xs) (hy : y ∈ xs) (hxy : x.1 ≠ y.1)
    (hCompat : occurrenceCompatible x.2 y.2) :
    (x.1, y.1) ∈ compatibleEdgesFromIndexedOccurrences xs ∨
      (y.1, x.1) ∈ compatibleEdgesFromIndexedOccurrences xs := by
  induction xs with
  | nil =>
      simp at hx
  | cons head rest ih =>
      simp at hx hy
      rcases hx with rfl | hxRest
      · rcases hy with rfl | hyRest
        · exact (hxy rfl).elim
        · left
          simp [compatibleEdgesFromIndexedOccurrences]
          exact List.mem_append.mpr
            (Or.inl (mem_compatibleEdgesFromHead_of_mem hyRest hCompat))
      · rcases hy with rfl | hyRest
        · right
          simp [compatibleEdgesFromIndexedOccurrences]
          exact List.mem_append.mpr
            (Or.inl
              (mem_compatibleEdgesFromHead_of_mem hxRest (occurrenceCompatible_symm hCompat)))
        · rcases ih hxRest hyRest with hEdge | hEdge
          · left
            simp [compatibleEdgesFromIndexedOccurrences]
            exact List.mem_append.mpr (Or.inr hEdge)
          · right
            simp [compatibleEdgesFromIndexedOccurrences]
            exact List.mem_append.mpr (Or.inr hEdge)

noncomputable def occurrenceAt? (φ : SAT.ThreeCNF) (v : Nat) : Option LiteralOccurrence :=
  (literalOccurrences φ)[v]?

end Clique
end Karp21
end ComplexityReduction
