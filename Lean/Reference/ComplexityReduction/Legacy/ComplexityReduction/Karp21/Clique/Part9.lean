/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Clique.Part8

/-!
Continuation module for the 3SAT -> Clique proof-carrying TM migration.
-/

namespace ComplexityReduction
namespace Karp21
namespace Clique

def cliqueIndexedFormulaOccurrenceStepRunnerInput
    (p : cliqueIndexedFormulaOccurrenceStepInputEncodedType.Carrier) :
    cliqueIndexedClauseOccurrenceRunnerInputEncodedType.Carrier :=
  ((p.1.1, ((0 : Nat), (p.1.2.1, p.1.2.2))), p.2)

theorem cliqueIndexedFormulaOccurrenceStepRunnerInput_fold_eq
    (p : cliqueIndexedFormulaOccurrenceStepInputEncodedType.Carrier) :
    cliqueIndexedClauseOccurrenceRunnerFold
        (cliqueIndexedFormulaOccurrenceStepRunnerInput p) =
      cliqueIndexedClauseOccurrenceFold p.1.1 (0 : Nat) p.1.2.1 p.1.2.2 p.2 := by
  simpa [cliqueIndexedFormulaOccurrenceStepRunnerInput] using
    cliqueIndexedClauseOccurrenceRunnerFold_eq
      (cliqueIndexedFormulaOccurrenceStepRunnerInput p)

theorem cliqueIndexedFormulaOccurrenceStep_tm_polytime :
    TMPolyTimeMap
      cliqueIndexedFormulaOccurrenceStepInputEncodedType
      cliqueIndexedFormulaOccurrenceAccEncodedType
      cliqueIndexedFormulaOccurrenceStep := by
  let X := cliqueIndexedFormulaOccurrenceStepInputEncodedType
  have hFormulaAcc :
      TMPolyTimeMap X cliqueIndexedFormulaOccurrenceAccEncodedType
        (fun p : X.Carrier => p.1) := by
    simpa [X, cliqueIndexedFormulaOccurrenceStepInputEncodedType] using
      TMPolyTimeMap.fst cliqueIndexedFormulaOccurrenceAccEncodedType clauseStructuredEncodedType
  have hClause :
      TMPolyTimeMap X clauseStructuredEncodedType
        (fun p : X.Carrier => p.2) := by
    simpa [X, cliqueIndexedFormulaOccurrenceStepInputEncodedType] using
      TMPolyTimeMap.snd cliqueIndexedFormulaOccurrenceAccEncodedType clauseStructuredEncodedType
  have hClauseIdx :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => p.1.1) := by
    have hFst :=
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.list indexedLiteralOccurrenceEncodedType))
    have hComp := TMPolyTimeMap.comp hFst hFormulaAcc
    simpa [Function.comp, cliqueIndexedFormulaOccurrenceAccEncodedType, X] using hComp
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.list indexedLiteralOccurrenceEncodedType))
        (fun p : X.Carrier => p.1.2) := by
    have hSnd :=
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.list indexedLiteralOccurrenceEncodedType))
    have hComp := TMPolyTimeMap.comp hSnd hFormulaAcc
    simpa [Function.comp, cliqueIndexedFormulaOccurrenceAccEncodedType, X] using hComp
  have hNext :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => p.1.2.1) := by
    have hFst :=
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.list indexedLiteralOccurrenceEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hOut :
      TMPolyTimeMap X (EncodedType.list indexedLiteralOccurrenceEncodedType)
        (fun p : X.Carrier => p.1.2.2) := by
    have hSnd :=
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.list indexedLiteralOccurrenceEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hZero :
      TMPolyTimeMap X EncodedType.nat
        (fun _ : X.Carrier => (0 : Nat)) :=
    (TMBackedCostedMap.const X EncodedType.nat (0 : Nat)).tm_polytime
  have hNextOut :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.list indexedLiteralOccurrenceEncodedType))
        (fun p : X.Carrier => (p.1.2.1, p.1.2.2)) :=
    TMPolyTimeMap.prod_mk hNext hOut
  have hSlotNextOut :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat
            (EncodedType.list indexedLiteralOccurrenceEncodedType)))
        (fun p : X.Carrier => ((0 : Nat), (p.1.2.1, p.1.2.2))) :=
    TMPolyTimeMap.prod_mk hZero hNextOut
  have hClauseAcc :
      TMPolyTimeMap X cliqueIndexedClauseOccurrenceAccEncodedType
        (fun p : X.Carrier => (p.1.1, ((0 : Nat), (p.1.2.1, p.1.2.2)))) := by
    simpa [cliqueIndexedClauseOccurrenceAccEncodedType] using
      TMPolyTimeMap.prod_mk hClauseIdx hSlotNextOut
  have hRunnerInput :
      TMPolyTimeMap X cliqueIndexedClauseOccurrenceRunnerInputEncodedType
        cliqueIndexedFormulaOccurrenceStepRunnerInput := by
    simpa [cliqueIndexedFormulaOccurrenceStepRunnerInput,
      cliqueIndexedClauseOccurrenceRunnerInputEncodedType] using
      TMPolyTimeMap.prod_mk hClauseAcc hClause
  have hInstructionsImage :
      TMPolyTimeMap X cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType
        cliqueIndexedFormulaOccurrenceStepRunnerInput := by
    have hComp := TMPolyTimeMap.comp
      cliqueIndexedClauseOccurrenceRunnerInstructionsImageTMBackedMap.tm_polytime hRunnerInput
    simpa [Function.comp] using hComp
  have hFoldImage :
      TMPolyTimeMap X cliqueIndexedClauseOccurrenceRunnerFoldImageEncodedType
        cliqueIndexedFormulaOccurrenceStepRunnerInput := by
    have hComp := TMPolyTimeMap.comp
      cliqueIndexedClauseOccurrenceRunnerFoldImageTMBackedMap.tm_polytime hInstructionsImage
    simpa [Function.comp] using hComp
  have hFold :
      TMPolyTimeMap X cliqueIndexedClauseOccurrenceAccEncodedType
        (fun p : X.Carrier =>
          cliqueIndexedClauseOccurrenceRunnerFold
            (cliqueIndexedFormulaOccurrenceStepRunnerInput p)) := by
    have hComp := TMPolyTimeMap.comp
      cliqueIndexedClauseOccurrenceRunnerFoldFromImageTMBackedMap.tm_polytime hFoldImage
    simpa [Function.comp] using hComp
  have hFoldTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat
            (EncodedType.list indexedLiteralOccurrenceEncodedType)))
        (fun p : X.Carrier =>
          (cliqueIndexedClauseOccurrenceRunnerFold
            (cliqueIndexedFormulaOccurrenceStepRunnerInput p)).2) := by
    have hSnd :=
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat
            (EncodedType.list indexedLiteralOccurrenceEncodedType)))
    have hComp := TMPolyTimeMap.comp hSnd hFold
    simpa [Function.comp, cliqueIndexedClauseOccurrenceAccEncodedType] using hComp
  have hFoldNextOut :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.list indexedLiteralOccurrenceEncodedType))
        (fun p : X.Carrier =>
          (cliqueIndexedClauseOccurrenceRunnerFold
            (cliqueIndexedFormulaOccurrenceStepRunnerInput p)).2.2) := by
    have hSnd :=
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.list indexedLiteralOccurrenceEncodedType))
    have hComp := TMPolyTimeMap.comp hSnd hFoldTail
    simpa [Function.comp] using hComp
  have hFoldNext :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier =>
          (cliqueIndexedClauseOccurrenceRunnerFold
            (cliqueIndexedFormulaOccurrenceStepRunnerInput p)).2.2.1) := by
    have hFst :=
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.list indexedLiteralOccurrenceEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hFoldNextOut
    simpa [Function.comp] using hComp
  have hFoldOut :
      TMPolyTimeMap X (EncodedType.list indexedLiteralOccurrenceEncodedType)
        (fun p : X.Carrier =>
          (cliqueIndexedClauseOccurrenceRunnerFold
            (cliqueIndexedFormulaOccurrenceStepRunnerInput p)).2.2.2) := by
    have hSnd :=
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.list indexedLiteralOccurrenceEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hFoldNextOut
    simpa [Function.comp] using hComp
  have hClauseSucc :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => Nat.succ (p.1.1 : Nat)) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hClauseIdx
    simpa [Function.comp] using hComp
  have hOutputTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.list indexedLiteralOccurrenceEncodedType))
        (fun p : X.Carrier =>
          ((cliqueIndexedClauseOccurrenceRunnerFold
              (cliqueIndexedFormulaOccurrenceStepRunnerInput p)).2.2.1,
            (cliqueIndexedClauseOccurrenceRunnerFold
              (cliqueIndexedFormulaOccurrenceStepRunnerInput p)).2.2.2)) :=
    TMPolyTimeMap.prod_mk hFoldNext hFoldOut
  have hOutput :
      TMPolyTimeMap X cliqueIndexedFormulaOccurrenceAccEncodedType
        (fun p : X.Carrier =>
          (Nat.succ (p.1.1 : Nat),
            ((cliqueIndexedClauseOccurrenceRunnerFold
                (cliqueIndexedFormulaOccurrenceStepRunnerInput p)).2.2.1,
              (cliqueIndexedClauseOccurrenceRunnerFold
                (cliqueIndexedFormulaOccurrenceStepRunnerInput p)).2.2.2))) := by
    simpa [cliqueIndexedFormulaOccurrenceAccEncodedType] using
      TMPolyTimeMap.prod_mk hClauseSucc hOutputTail
  simpa [cliqueIndexedFormulaOccurrenceStep,
    cliqueIndexedFormulaOccurrenceStepRunnerInput_fold_eq, X] using hOutput

theorem cliqueIndexedFormulaOccurrenceStep_inputSize_le
    (p : cliqueIndexedFormulaOccurrenceStepInputEncodedType.Carrier) :
    cliqueIndexedFormulaOccurrenceAccEncodedType.inputSize
        (cliqueIndexedFormulaOccurrenceStep p) ≤
      20 * cliqueIndexedFormulaOccurrenceStepInputEncodedType.inputSize p ^ 2 + 100 := by
  rcases p with ⟨acc, c⟩
  rcases acc with ⟨clauseIdx, tail⟩
  rcases tail with ⟨next, out⟩
  change Nat at clauseIdx
  change Nat at next
  change List indexedLiteralOccurrenceEncodedType.Carrier at out
  change SAT.Clause at c
  let S :=
    cliqueIndexedFormulaOccurrenceStepInputEncodedType.inputSize
      (((clauseIdx, (next, out)), c) :
        cliqueIndexedFormulaOccurrenceStepInputEncodedType.Carrier)
  let occs :=
    indexedLiteralOccurrencesFrom next (clauseOccurrencesFrom clauseIdx (0 : Nat) c)
  have hClauseIdxS : clauseIdx ≤ S := by
    simp [S, cliqueIndexedFormulaOccurrenceStepInputEncodedType,
      cliqueIndexedFormulaOccurrenceAccEncodedType, EncodedType.inputSize_prod]
    omega
  have hNextS : next ≤ S := by
    simp [S, cliqueIndexedFormulaOccurrenceStepInputEncodedType,
      cliqueIndexedFormulaOccurrenceAccEncodedType, EncodedType.inputSize_prod]
    omega
  have hOutS :
      (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize out ≤ S := by
    simp [S, cliqueIndexedFormulaOccurrenceStepInputEncodedType,
      cliqueIndexedFormulaOccurrenceAccEncodedType, EncodedType.inputSize_prod]
    omega
  have hClauseInputS : clauseStructuredEncodedType.inputSize c ≤ S := by
    simp [S, cliqueIndexedFormulaOccurrenceStepInputEncodedType,
      cliqueIndexedFormulaOccurrenceAccEncodedType, EncodedType.inputSize_prod]
  have hLenS : c.length ≤ S := by
    have hLen := encodedList_length_le_inputSize literalStructuredEncodedType c
    have hClauseInput :
        (EncodedType.list literalStructuredEncodedType).inputSize c ≤ S := by
      simpa [clauseStructuredEncodedType] using hClauseInputS
    exact hLen.trans hClauseInput
  have hOccsRaw :
      (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize occs ≤
        c.length *
          (clauseIdx + (0 : Nat) + next + c.length +
            clauseStructuredEncodedType.inputSize c + 30) := by
    simpa [occs] using indexedClauseOccurrencesFrom_inputSize_le clauseIdx (0 : Nat) next c
  have hFactor :
      clauseIdx + (0 : Nat) + next + c.length +
          clauseStructuredEncodedType.inputSize c + 30 ≤
        4 * S + 30 := by
    omega
  have hOccsBound :
      (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize occs ≤
        S * (4 * S + 30) :=
    hOccsRaw.trans (Nat.mul_le_mul hLenS hFactor)
  have hSquare :
      clauseIdx + next + c.length +
          (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize out +
          S * (4 * S + 30) + 20 ≤
        20 * (S * S) + 100 := by
    nlinarith [sq_nonneg (S : Int), hClauseIdxS, hNextS, hLenS, hOutS]
  change
    cliqueIndexedFormulaOccurrenceAccEncodedType.inputSize
        (Nat.succ clauseIdx,
          ((cliqueIndexedClauseOccurrenceFold clauseIdx (0 : Nat) next out c).2.2.1,
            (cliqueIndexedClauseOccurrenceFold clauseIdx (0 : Nat) next out c).2.2.2)) ≤
      20 * S ^ 2 + 100
  rw [cliqueIndexedClauseOccurrenceFold_next, cliqueIndexedClauseOccurrenceFold_out]
  simp [cliqueIndexedFormulaOccurrenceAccEncodedType, EncodedType.inputSize_prod,
    encodedList_inputSize_append, pow_two]
  nlinarith [hOccsBound, hSquare]

theorem cliqueIndexedFormulaOccurrenceStep_polynomialSizeBound :
    PolynomialSizeBound
      (fun p : cliqueIndexedFormulaOccurrenceStepInputEncodedType.Carrier =>
        cliqueIndexedFormulaOccurrenceStepInputEncodedType.inputSize p)
      (fun acc : cliqueIndexedFormulaOccurrenceAccEncodedType.Carrier =>
        cliqueIndexedFormulaOccurrenceAccEncodedType.inputSize acc)
      cliqueIndexedFormulaOccurrenceStep := by
  refine PolynomialSizeBound.intro_with 2 20 100 ?_
  intro p
  simpa [pow_two] using cliqueIndexedFormulaOccurrenceStep_inputSize_le p

noncomputable def cliqueIndexedFormulaOccurrenceStepTMBackedMap :
    TMBackedCostedMap
      cliqueIndexedFormulaOccurrenceStepInputEncodedType
      cliqueIndexedFormulaOccurrenceAccEncodedType
      cliqueIndexedFormulaOccurrenceStep where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      cliqueIndexedFormulaOccurrenceStep_polynomialSizeBound
  tm_polytime := cliqueIndexedFormulaOccurrenceStep_tm_polytime

def cliqueIndexedFormulaOccurrenceInit :
    cliqueIndexedFormulaOccurrenceAccEncodedType.Carrier :=
  ((0 : Nat), ((0 : Nat), ([] : List indexedLiteralOccurrenceEncodedType.Carrier)))

theorem cliqueIndexedFormulaOccurrencesFrom_clause
    (clauseIdx next : Nat)
    (out : List indexedLiteralOccurrenceEncodedType.Carrier)
    (cs : SAT.CNF) :
    (cliqueIndexedFormulaOccurrencesFrom clauseIdx next out cs).1 =
      clauseIdx + cs.length := by
  induction cs generalizing clauseIdx next out with
  | nil =>
      rfl
  | cons c rest ih =>
      let folded := cliqueIndexedClauseOccurrenceFold clauseIdx 0 next out c
      simp only [cliqueIndexedFormulaOccurrencesFrom, cliqueIndexedFormulaOccurrenceStep]
      change
        (cliqueIndexedFormulaOccurrencesFrom (clauseIdx + 1) folded.2.2.1
            folded.2.2.2 rest).1 =
          clauseIdx + (c :: rest).length
      rw [ih]
      simp [Nat.add_comm, Nat.add_left_comm]

theorem cliqueIndexedFormulaOccurrencesFrom_next
    (clauseIdx next : Nat)
    (out : List indexedLiteralOccurrenceEncodedType.Carrier)
    (cs : SAT.CNF) :
    (cliqueIndexedFormulaOccurrencesFrom clauseIdx next out cs).2.1 =
      next + SAT.CNF.totalClauseLength cs := by
  induction cs generalizing clauseIdx next out with
  | nil =>
      rfl
  | cons c rest ih =>
      let folded := cliqueIndexedClauseOccurrenceFold clauseIdx 0 next out c
      have hFoldNext :
          folded.2.2.1 = next + c.length := by
        have hNext := cliqueIndexedClauseOccurrenceFold_next clauseIdx 0 next out c
        simpa [folded] using hNext
      simp only [cliqueIndexedFormulaOccurrencesFrom, cliqueIndexedFormulaOccurrenceStep]
      change
        (cliqueIndexedFormulaOccurrencesFrom (clauseIdx + 1) folded.2.2.1
            folded.2.2.2 rest).2.1 =
          next + SAT.CNF.totalClauseLength (c :: rest)
      rw [ih, hFoldNext]
      simp [SAT.CNF.totalClauseLength, Nat.add_assoc]

theorem indexedFormulaOccurrencesFrom_inputSize_le
    (clauseIdx next : Nat) (cs : SAT.CNF) :
    (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize
        (indexedLiteralOccurrencesFrom next (formulaOccurrencesFrom clauseIdx cs)) ≤
      SAT.CNF.totalClauseLength cs *
        (clauseIdx + next + cs.length + SAT.CNF.totalClauseLength cs +
          cnfStructuredEncodedType.inputSize cs + 50) := by
  induction cs generalizing clauseIdx next with
  | nil =>
      simp [formulaOccurrencesFrom, indexedLiteralOccurrencesFrom, SAT.CNF.totalClauseLength]
  | cons c rest ih =>
      let current :=
        indexedLiteralOccurrencesFrom next (clauseOccurrencesFrom clauseIdx 0 c)
      let tail :=
        indexedLiteralOccurrencesFrom (next + c.length)
          (formulaOccurrencesFrom (clauseIdx + 1) rest)
      have hAppend :
          indexedLiteralOccurrencesFrom next
              (formulaOccurrencesFrom clauseIdx (c :: rest)) =
            current ++ tail := by
        simp [current, tail, formulaOccurrencesFrom, indexedLiteralOccurrencesFrom_append,
          clauseOccurrences, clauseOccurrencesFrom_length]
      have hCurrent :
          (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize current ≤
            c.length *
              (clauseIdx + next + c.length + clauseStructuredEncodedType.inputSize c + 30) := by
        simpa [current, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          indexedClauseOccurrencesFrom_inputSize_le clauseIdx 0 next c
      have hTail :
          (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize tail ≤
            SAT.CNF.totalClauseLength rest *
              ((clauseIdx + 1) + (next + c.length) + rest.length +
                SAT.CNF.totalClauseLength rest +
                cnfStructuredEncodedType.inputSize rest + 50) := by
        simpa [tail] using ih (clauseIdx + 1) (next + c.length)
      have hCurrentFactor :
          clauseIdx + next + c.length + clauseStructuredEncodedType.inputSize c + 30 ≤
            clauseIdx + next + (c :: rest).length +
              SAT.CNF.totalClauseLength (c :: rest) +
              cnfStructuredEncodedType.inputSize (c :: rest) + 50 := by
        simp [SAT.CNF.totalClauseLength, cnfStructuredEncodedType,
          clauseStructuredEncodedType]
        omega
      have hTailFactor :
          (clauseIdx + 1) + (next + c.length) + rest.length +
              SAT.CNF.totalClauseLength rest +
              cnfStructuredEncodedType.inputSize rest + 50 ≤
            clauseIdx + next + (c :: rest).length +
              SAT.CNF.totalClauseLength (c :: rest) +
              cnfStructuredEncodedType.inputSize (c :: rest) + 50 := by
        simp [SAT.CNF.totalClauseLength, cnfStructuredEncodedType,
          clauseStructuredEncodedType]
        omega
      rw [hAppend, encodedList_inputSize_append]
      calc
        (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize current +
            (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize tail
            ≤
          c.length *
              (clauseIdx + next + (c :: rest).length +
                SAT.CNF.totalClauseLength (c :: rest) +
                cnfStructuredEncodedType.inputSize (c :: rest) + 50) +
            SAT.CNF.totalClauseLength rest *
              (clauseIdx + next + (c :: rest).length +
                SAT.CNF.totalClauseLength (c :: rest) +
                cnfStructuredEncodedType.inputSize (c :: rest) + 50) := by
              exact Nat.add_le_add
                (hCurrent.trans (Nat.mul_le_mul_left c.length hCurrentFactor))
                (hTail.trans (Nat.mul_le_mul_left _ hTailFactor))
        _ =
          SAT.CNF.totalClauseLength (c :: rest) *
            (clauseIdx + next + (c :: rest).length +
              SAT.CNF.totalClauseLength (c :: rest) +
              cnfStructuredEncodedType.inputSize (c :: rest) + 50) := by
              simp [SAT.CNF.totalClauseLength, Nat.add_mul]

noncomputable def cliqueIndexedFormulaOccurrencesFoldBoundPolynomial : Polynomial Nat :=
  Polynomial.C 1000 * (Polynomial.X * (Polynomial.X * Polynomial.X)) + Polynomial.C 1000

@[simp] theorem cliqueIndexedFormulaOccurrencesFoldBoundPolynomial_eval (n : Nat) :
    cliqueIndexedFormulaOccurrencesFoldBoundPolynomial.eval n =
      1000 * (n * (n * n)) + 1000 := by
  simp [cliqueIndexedFormulaOccurrencesFoldBoundPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_X]

theorem cliqueIndexedFormulaOccurrencesFrom_init_inputSize_le
    (cs : SAT.CNF) :
    cliqueIndexedFormulaOccurrenceAccEncodedType.inputSize
        (cliqueIndexedFormulaOccurrencesFrom 0 0
          ([] : List indexedLiteralOccurrenceEncodedType.Carrier) cs) ≤
      cliqueIndexedFormulaOccurrencesFoldBoundPolynomial.eval
        (cnfStructuredEncodedType.inputSize cs) := by
  let N := cnfStructuredEncodedType.inputSize cs
  let L := SAT.CNF.totalClauseLength cs
  let C := cs.length
  have hLen : C ≤ N := by
    simpa [C, N] using cnfStructured_inputSize_ge_length cs
  have hTotal : L ≤ N := by
    have h := cnfStructured_inputSize_ge_totalClauseLength_add_length cs
    omega
  have hOut :
      (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize
          (indexedLiteralOccurrencesFrom 0 (formulaOccurrencesFrom 0 cs)) ≤
        L * (C + L + N + 50) := by
    have hRaw := indexedFormulaOccurrencesFrom_inputSize_le 0 0 cs
    simpa [L, C, N, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hRaw
  have hAcc :
      cliqueIndexedFormulaOccurrenceAccEncodedType.inputSize
          (cliqueIndexedFormulaOccurrencesFrom 0 0
            ([] : List indexedLiteralOccurrenceEncodedType.Carrier) cs) =
        C + (L +
          (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize
            (indexedLiteralOccurrencesFrom 0 (formulaOccurrencesFrom 0 cs)) + 4) := by
    have hClause := cliqueIndexedFormulaOccurrencesFrom_clause 0 0
      ([] : List indexedLiteralOccurrenceEncodedType.Carrier) cs
    have hNext := cliqueIndexedFormulaOccurrencesFrom_next 0 0
      ([] : List indexedLiteralOccurrenceEncodedType.Carrier) cs
    have hOutEq := cliqueIndexedFormulaOccurrencesFrom_out 0 0
      ([] : List indexedLiteralOccurrenceEncodedType.Carrier) cs
    simp [cliqueIndexedFormulaOccurrenceAccEncodedType, EncodedType.inputSize_prod,
      hClause, hNext, hOutEq, C, L]
    omega
  have hOutBound :
      (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize
          (indexedLiteralOccurrencesFrom 0 (formulaOccurrencesFrom 0 cs)) ≤
        N * (3 * N + 50) := by
    have hFactor : C + L + N + 50 ≤ 3 * N + 50 := by omega
    exact hOut.trans (Nat.mul_le_mul hTotal hFactor)
  rw [hAcc, cliqueIndexedFormulaOccurrencesFoldBoundPolynomial_eval]
  change
    C + (L +
      (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize
        (indexedLiteralOccurrencesFrom 0 (formulaOccurrencesFrom 0 cs)) + 4) ≤
      1000 * (N * (N * N)) + 1000
  have hSmall :
      C + (L +
        (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize
          (indexedLiteralOccurrencesFrom 0 (formulaOccurrencesFrom 0 cs)) + 4) ≤
        N + (N + N * (3 * N + 50) + 4) := by
    omega
  have hPoly :
      N + (N + N * (3 * N + 50) + 4) ≤
        1000 * (N * (N * N)) + 1000 := by
    cases N with
    | zero =>
        norm_num
    | succ n =>
        have hNpos : 1 ≤ Nat.succ n := by omega
        nlinarith [sq_nonneg (Nat.succ n : Int), hNpos]
  exact hSmall.trans hPoly

theorem cliqueIndexedFormulaOccurrencesFrom_init_prefix_inputSize_le
    (source pref rest : SAT.CNF) (hSplit : pref ++ rest = source) :
    cliqueIndexedFormulaOccurrenceAccEncodedType.inputSize
        (cliqueIndexedFormulaOccurrencesFrom 0 0
          ([] : List indexedLiteralOccurrenceEncodedType.Carrier) pref) ≤
      cliqueIndexedFormulaOccurrencesFoldBoundPolynomial.eval
        (cnfStructuredEncodedType.inputSize source) := by
  have hPrefix :=
    cliqueIndexedFormulaOccurrencesFrom_init_inputSize_le pref
  have hPrefixInput :
      cnfStructuredEncodedType.inputSize pref ≤ cnfStructuredEncodedType.inputSize source := by
    have hAppend :=
      encodedList_inputSize_append clauseStructuredEncodedType pref rest
    have hSource :
        cnfStructuredEncodedType.inputSize source =
          cnfStructuredEncodedType.inputSize pref + cnfStructuredEncodedType.inputSize rest := by
      rw [← hSplit]
      simpa [cnfStructuredEncodedType] using hAppend
    omega
  exact hPrefix.trans
    (TM2Programs.polynomialNat_eval_mono
      cliqueIndexedFormulaOccurrencesFoldBoundPolynomial hPrefixInput)

theorem cliqueIndexedFormulaOccurrencesFrom_append_singleton
    (pref : SAT.CNF) (c : SAT.Clause) :
    cliqueIndexedFormulaOccurrenceStep
        (cliqueIndexedFormulaOccurrencesFrom 0 0
        ([] : List indexedLiteralOccurrenceEncodedType.Carrier) pref, c) =
      cliqueIndexedFormulaOccurrencesFrom 0 0
        ([] : List indexedLiteralOccurrenceEncodedType.Carrier) (pref ++ [c]) := by
  unfold cliqueIndexedFormulaOccurrencesFrom
  let step :=
    fun acc clause => cliqueIndexedFormulaOccurrenceStep (acc, clause)
  let init := (0, 0, ([] : List indexedLiteralOccurrenceEncodedType.Carrier))
  change step (List.foldl step init pref) c =
    List.foldl step init (pref ++ [c])
  calc
    step (List.foldl step init pref) c =
        List.foldl step (List.foldl step init pref) [c] := by
          rfl
    _ = List.foldl step init (pref ++ [c]) := by
          exact (List.foldl_append (f := step) (b := init) (l := pref) (l' := [c])).symm

noncomputable def cliqueIndexedFormulaOccurrencesFoldTimePolynomial
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod
          cliqueIndexedFormulaOccurrenceAccEncodedType
          clauseStructuredEncodedType).encode
        cliqueIndexedFormulaOccurrenceAccEncodedType.encode
        cliqueIndexedFormulaOccurrenceStep) : Polynomial Nat :=
  TMPolyTimeMap.listFoldTypedBoundedTimePolynomial
    clauseStructuredEncodedType
    cliqueIndexedFormulaOccurrenceAccEncodedType
    cliqueIndexedFormulaOccurrenceStep hStep
    cliqueIndexedFormulaOccurrencesFoldBoundPolynomial

theorem cliqueIndexedFormulaOccurrencesFold_loopTime_le
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod
          cliqueIndexedFormulaOccurrenceAccEncodedType
          clauseStructuredEncodedType).encode
        cliqueIndexedFormulaOccurrenceAccEncodedType.encode
        cliqueIndexedFormulaOccurrenceStep)
    (source : SAT.CNF) :
    2 +
        TM2Programs.listFoldTypedLoopTime
          clauseStructuredEncodedType
          cliqueIndexedFormulaOccurrenceAccEncodedType
          cliqueIndexedFormulaOccurrenceStep hStep
          cliqueIndexedFormulaOccurrenceInit source ≤
      (cliqueIndexedFormulaOccurrencesFoldTimePolynomial hStep).eval
        (cnfStructuredEncodedType.inputSize source) := by
  let X := clauseStructuredEncodedType
  let Y := cliqueIndexedFormulaOccurrenceAccEncodedType
  let N := (EncodedType.list X).inputSize source
  let B := cliqueIndexedFormulaOccurrencesFoldBoundPolynomial.eval N
  let T := hStep.time.eval (B + N + 5)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hLoopAux :
      ∀ (rest pref : SAT.CNF) (acc : Y.Carrier),
        acc =
            cliqueIndexedFormulaOccurrencesFrom 0 0
              ([] : List indexedLiteralOccurrenceEncodedType.Carrier) pref →
          pref ++ rest = source →
            (EncodedType.list X).inputSize rest ≤ N →
              TM2Programs.listFoldTypedLoopTime X Y cliqueIndexedFormulaOccurrenceStep
                  hStep acc rest ≤
                C * (EncodedType.list X).inputSize rest := by
    intro rest
    induction rest with
    | nil =>
        intro pref acc _hAcc _hSplit _hRest
        simp [TM2Programs.listFoldTypedLoopTime]
    | cons current tail ih =>
        intro pref acc hAcc hSplit hRestInput
        have hRestCons :
            X.inputSize current + 1 + (EncodedType.list X).inputSize tail ≤ N := by
          have hRestEq :
              X.list.inputSize (current :: tail) =
                X.inputSize current + 1 + X.list.inputSize tail :=
            EncodedType.inputSize_list_cons X current tail
          exact hRestEq ▸ hRestInput
        have hCurrentN : X.inputSize current ≤ N := by
          omega
        have hTailN : (EncodedType.list X).inputSize tail ≤ N := by
          omega
        have hAccBound : Y.inputSize acc ≤ B := by
          rw [hAcc]
          have hPrefix :=
            cliqueIndexedFormulaOccurrencesFrom_init_prefix_inputSize_le
              source pref (current :: tail) hSplit
          simpa [X, Y, N, B, cnfStructuredEncodedType] using hPrefix
        have hAccTail :
            cliqueIndexedFormulaOccurrenceStep (acc, current) =
              cliqueIndexedFormulaOccurrencesFrom 0 0
                ([] : List indexedLiteralOccurrenceEncodedType.Carrier)
                (pref ++ [current]) := by
          rw [hAcc]
          exact cliqueIndexedFormulaOccurrencesFrom_append_singleton pref current
        have hSplitTail : (pref ++ [current]) ++ tail = source := by
          simpa [List.append_assoc] using hSplit
        have hNextBound :
            Y.inputSize (cliqueIndexedFormulaOccurrenceStep (acc, current)) ≤ B := by
          rw [hAccTail]
          have hPrefix :=
            cliqueIndexedFormulaOccurrencesFrom_init_prefix_inputSize_le
              source (pref ++ [current]) tail hSplitTail
          simpa [X, Y, N, B, cnfStructuredEncodedType] using hPrefix
        have hTail := ih (pref ++ [current])
          (cliqueIndexedFormulaOccurrenceStep (acc, current))
          hAccTail hSplitTail hTailN
        have hStepTime :
            hStep.time.eval ((EncodedType.prod Y X).inputSize (acc, current)) ≤ T := by
          have hArg :
              (EncodedType.prod Y X).inputSize (acc, current) ≤ B + N + 5 := by
            rw [EncodedType.inputSize_prod]
            change Y.inputSize acc + 1 + X.inputSize current ≤ B + N + 5
            omega
          exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
        have hBlock :
            TM2Programs.listFoldBlockTime hStep.tm (X.encode current).length
                (Y.encode acc).length
                (Y.encode (cliqueIndexedFormulaOccurrenceStep (acc, current))).length
                (hStep.time.eval ((EncodedType.prod Y X).inputSize (acc, current))) ≤
              C * (X.inputSize current + 1) := by
          exact
            TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
              (by simpa [Y, EncodedType.inputSize] using hAccBound)
              (by simpa [Y, EncodedType.inputSize] using hNextBound)
              hStepTime
        calc
          TM2Programs.listFoldTypedLoopTime X Y cliqueIndexedFormulaOccurrenceStep hStep
              acc (current :: tail)
              =
            TM2Programs.listFoldTypedLoopTime X Y cliqueIndexedFormulaOccurrenceStep hStep
              (cliqueIndexedFormulaOccurrenceStep (acc, current)) tail +
            TM2Programs.listFoldBlockTime hStep.tm (X.encode current).length
              (Y.encode acc).length
              (Y.encode (cliqueIndexedFormulaOccurrenceStep (acc, current))).length
              (hStep.time.eval ((EncodedType.prod Y X).inputSize (acc, current))) := by
                rfl
          _ ≤ C * (EncodedType.list X).inputSize tail + C * (X.inputSize current + 1) :=
                Nat.add_le_add hTail hBlock
          _ ≤ C * (EncodedType.list X).inputSize (current :: tail) := by
                rw [EncodedType.inputSize_list_cons]
                nlinarith
  have hInitAcc :
      cliqueIndexedFormulaOccurrenceInit =
        cliqueIndexedFormulaOccurrencesFrom 0 0
          ([] : List indexedLiteralOccurrenceEncodedType.Carrier) [] := by
    rfl
  have hLoop :
      TM2Programs.listFoldTypedLoopTime X Y cliqueIndexedFormulaOccurrenceStep hStep
          cliqueIndexedFormulaOccurrenceInit source ≤ C * N := by
    simpa [X, Y, N] using
      hLoopAux source [] cliqueIndexedFormulaOccurrenceInit
        hInitAcc (by rfl) (by simp [N])
  have hTimeEval :
      (cliqueIndexedFormulaOccurrencesFoldTimePolynomial hStep).eval N = (C + 2) * (N + 1) := by
    simp [cliqueIndexedFormulaOccurrencesFoldTimePolynomial, X, N, B, T, C,
      TMPolyTimeMap.listFoldTypedBoundedTimePolynomial,
      TM2Programs.listFoldBoundedTimePolynomial_eval, TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_comp]
  rw [show cnfStructuredEncodedType.inputSize source = N by rfl, hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

theorem cliqueIndexedFormulaOccurrencesFold_tm_polytime :
    TMPolyTimeMap
      cnfStructuredEncodedType
      cliqueIndexedFormulaOccurrenceAccEncodedType
      (fun cs : SAT.CNF =>
        cliqueIndexedFormulaOccurrencesFrom 0 0
          ([] : List indexedLiteralOccurrenceEncodedType.Carrier) cs) := by
  rcases cliqueIndexedFormulaOccurrenceStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed
      clauseStructuredEncodedType
      cliqueIndexedFormulaOccurrenceAccEncodedType
      cliqueIndexedFormulaOccurrenceStep cliqueIndexedFormulaOccurrenceInit hStep
      (cliqueIndexedFormulaOccurrencesFoldTimePolynomial hStep) ?_
  intro source
  simpa [cnfStructuredEncodedType, cliqueIndexedFormulaOccurrenceInit,
    cliqueIndexedFormulaOccurrencesFrom] using
    cliqueIndexedFormulaOccurrencesFold_loopTime_le hStep source

theorem cliqueIndexedFormulaOccurrencesFold_polynomialSizeBound :
    PolynomialSizeBound
      (fun cs : SAT.CNF => cnfStructuredEncodedType.inputSize cs)
      (fun acc : cliqueIndexedFormulaOccurrenceAccEncodedType.Carrier =>
        cliqueIndexedFormulaOccurrenceAccEncodedType.inputSize acc)
      (fun cs : SAT.CNF =>
        cliqueIndexedFormulaOccurrencesFrom 0 0
          ([] : List indexedLiteralOccurrenceEncodedType.Carrier) cs) := by
  refine PolynomialSizeBound.intro_with 3 1000 1000 ?_
  intro cs
  have h := cliqueIndexedFormulaOccurrencesFrom_init_inputSize_le cs
  rw [cliqueIndexedFormulaOccurrencesFoldBoundPolynomial_eval] at h
  simpa [pow_succ, pow_two, Nat.mul_assoc] using h

noncomputable def cliqueIndexedFormulaOccurrencesFoldTMBackedMap :
    TMBackedCostedMap
      cnfStructuredEncodedType
      cliqueIndexedFormulaOccurrenceAccEncodedType
      (fun cs : SAT.CNF =>
        cliqueIndexedFormulaOccurrencesFrom 0 0
          ([] : List indexedLiteralOccurrenceEncodedType.Carrier) cs) where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      cliqueIndexedFormulaOccurrencesFold_polynomialSizeBound
  tm_polytime := cliqueIndexedFormulaOccurrencesFold_tm_polytime

def cliqueIndexedFormulaOccurrencesFromThreeCNF (φ : SAT.ThreeCNF) :
    cliqueIndexedFormulaOccurrenceAccEncodedType.Carrier :=
  cliqueIndexedFormulaOccurrencesFrom 0 0
    ([] : List indexedLiteralOccurrenceEncodedType.Carrier) φ.clauses

theorem cliqueIndexedFormulaOccurrencesFromThreeCNF_inputSize_le
    (φ : SAT.ThreeCNF) :
    cliqueIndexedFormulaOccurrenceAccEncodedType.inputSize
        (cliqueIndexedFormulaOccurrencesFromThreeCNF φ) ≤
      1000 * (threeCNFStructuredEncodedType.inputSize φ) ^ 3 + 1000 := by
  have h := cliqueIndexedFormulaOccurrencesFrom_init_inputSize_le φ.clauses
  rw [cliqueIndexedFormulaOccurrencesFoldBoundPolynomial_eval] at h
  simpa [cliqueIndexedFormulaOccurrencesFromThreeCNF, threeCNFStructuredEncodedType,
    pow_succ, pow_two, Nat.mul_assoc] using h

theorem cliqueIndexedFormulaOccurrencesFromThreeCNF_polynomialSizeBound :
    PolynomialSizeBound
      (fun φ : SAT.ThreeCNF => threeCNFStructuredEncodedType.inputSize φ)
      (fun acc : cliqueIndexedFormulaOccurrenceAccEncodedType.Carrier =>
        cliqueIndexedFormulaOccurrenceAccEncodedType.inputSize acc)
      cliqueIndexedFormulaOccurrencesFromThreeCNF := by
  exact PolynomialSizeBound.intro_with 3 1000 1000
    cliqueIndexedFormulaOccurrencesFromThreeCNF_inputSize_le

noncomputable def cliqueIndexedFormulaOccurrencesFromThreeCNFTMBackedMap :
    TMBackedCostedMap
      threeCNFStructuredEncodedType
      cliqueIndexedFormulaOccurrenceAccEncodedType
      cliqueIndexedFormulaOccurrencesFromThreeCNF where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      cliqueIndexedFormulaOccurrencesFromThreeCNF_polynomialSizeBound
  tm_polytime := by
    have hForget :
        TMPolyTimeMap threeCNFStructuredEncodedType cnfStructuredEncodedType threeCNFToCNF :=
      (TMBackedCostedMap.ofEncodingEquiv
        threeCNFStructuredEncodedType cnfStructuredEncodedType threeCNFToCNF
        (Equiv.refl _) (by
          intro φ
          change
            cnfStructuredEncodedType.encode φ.clauses =
              List.map (Equiv.refl cnfStructuredEncodedType.Symbol)
                (cnfStructuredEncodedType.encode φ.clauses)
          simp)).tm_polytime
    have hComp := TMPolyTimeMap.comp
      cliqueIndexedFormulaOccurrencesFoldTMBackedMap.tm_polytime hForget
    simpa [Function.comp, cliqueIndexedFormulaOccurrencesFromThreeCNF, threeCNFToCNF] using hComp

theorem cliqueIndexedLiteralOccurrences_inputSize_le (φ : SAT.ThreeCNF) :
    (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize
        (cliqueIndexedLiteralOccurrences φ) ≤
      1000 * (threeCNFStructuredEncodedType.inputSize φ) ^ 3 + 1000 := by
  have hAcc := cliqueIndexedFormulaOccurrencesFromThreeCNF_inputSize_le φ
  have hOut :
      (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize
          (cliqueIndexedLiteralOccurrences φ) ≤
        cliqueIndexedFormulaOccurrenceAccEncodedType.inputSize
          (cliqueIndexedFormulaOccurrencesFromThreeCNF φ) := by
    simp [cliqueIndexedLiteralOccurrences, cliqueIndexedFormulaOccurrencesFromThreeCNF,
      cliqueIndexedFormulaOccurrenceAccEncodedType, EncodedType.inputSize_prod]
    omega
  exact hOut.trans hAcc

theorem indexedLiteralOccurrences_polynomialSizeBound :
    PolynomialSizeBound
      (fun φ : SAT.ThreeCNF => threeCNFStructuredEncodedType.inputSize φ)
      (fun xs : List indexedLiteralOccurrenceEncodedType.Carrier =>
        (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize xs)
      indexedLiteralOccurrences := by
  refine PolynomialSizeBound.intro_with 3 1000 1000 ?_
  intro φ
  rw [← cliqueIndexedLiteralOccurrences_eq_indexedLiteralOccurrences φ]
  exact cliqueIndexedLiteralOccurrences_inputSize_le φ

theorem cliqueIndexedLiteralOccurrences_tm_polytime :
    TMPolyTimeMap
      threeCNFStructuredEncodedType
      (EncodedType.list indexedLiteralOccurrenceEncodedType)
      cliqueIndexedLiteralOccurrences := by
  have hAcc :=
    cliqueIndexedFormulaOccurrencesFromThreeCNFTMBackedMap.tm_polytime
  have hTail :
      TMPolyTimeMap
        cliqueIndexedFormulaOccurrenceAccEncodedType
        (EncodedType.prod EncodedType.nat
          (EncodedType.list indexedLiteralOccurrenceEncodedType))
        (fun acc : cliqueIndexedFormulaOccurrenceAccEncodedType.Carrier => acc.2) := by
    simpa [cliqueIndexedFormulaOccurrenceAccEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.list indexedLiteralOccurrenceEncodedType))
  have hTailFromInput := TMPolyTimeMap.comp hTail hAcc
  have hOutProj :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.nat
          (EncodedType.list indexedLiteralOccurrenceEncodedType))
        (EncodedType.list indexedLiteralOccurrenceEncodedType)
        (fun p :
          (EncodedType.prod EncodedType.nat
            (EncodedType.list indexedLiteralOccurrenceEncodedType)).Carrier => p.2) := by
    simpa using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.list indexedLiteralOccurrenceEncodedType)
  have hOut := TMPolyTimeMap.comp hOutProj hTailFromInput
  simpa [Function.comp, cliqueIndexedLiteralOccurrences,
    cliqueIndexedFormulaOccurrencesFromThreeCNF] using hOut

theorem indexedLiteralOccurrences_tm_polytime :
    TMPolyTimeMap
      threeCNFStructuredEncodedType
      (EncodedType.list indexedLiteralOccurrenceEncodedType)
      indexedLiteralOccurrences := by
  have hClique := cliqueIndexedLiteralOccurrences_tm_polytime
  have hFun : indexedLiteralOccurrences = cliqueIndexedLiteralOccurrences := by
    funext φ
    exact (cliqueIndexedLiteralOccurrences_eq_indexedLiteralOccurrences φ).symm
  simpa [hFun] using hClique

noncomputable def indexedLiteralOccurrencesTMBackedMap :
    TMBackedCostedMap
      threeCNFStructuredEncodedType
      (EncodedType.list indexedLiteralOccurrenceEncodedType)
      indexedLiteralOccurrences where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      indexedLiteralOccurrences_polynomialSizeBound
  tm_polytime := indexedLiteralOccurrences_tm_polytime

end Clique
end Karp21
end ComplexityReduction
