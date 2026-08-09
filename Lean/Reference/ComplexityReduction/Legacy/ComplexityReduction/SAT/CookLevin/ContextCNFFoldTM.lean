/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.InvariantFold
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.Sum
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatRange
import ComplexityReduction.Legacy.ComplexityReduction.SAT.StructuredEncoding

namespace ComplexityReduction
namespace SAT

/-!
Direct-TM helper for CNF-producing list folds with a loaded context.

The fold source starts with one context instruction and then one right
instruction per list element.  The accumulator is initially unloaded, so this
works without an arbitrary inhabitant for the context type.
-/

def cnfContextFoldAccEncodedType (C : EncodedType) : EncodedType :=
  EncodedType.sum (EncodedType.raw Unit) (EncodedType.prod C cnfStructuredEncodedType)

def cnfContextFoldInstructionEncodedType (C X : EncodedType) : EncodedType :=
  EncodedType.sum C X

def cnfContextFoldInstructionListEncodedType (C X : EncodedType) : EncodedType :=
  EncodedType.list (cnfContextFoldInstructionEncodedType C X)

def cnfContextFoldInitAcc (C : EncodedType) :
    (cnfContextFoldAccEncodedType C).Carrier :=
  Sum.inl ()

noncomputable def cnfContextFoldStep {C X : EncodedType}
    (block : C.Carrier → X.Carrier → CNF)
    (p : (cnfContextFoldAccEncodedType C).Carrier ×
      (cnfContextFoldInstructionEncodedType C X).Carrier) :
    (cnfContextFoldAccEncodedType C).Carrier :=
  match p.2 with
  | Sum.inl c => Sum.inr (c, ([] : CNF))
  | Sum.inr x =>
      match p.1 with
      | Sum.inl _ => Sum.inl ()
      | Sum.inr cx => Sum.inr (cx.1, (show CNF from cx.2) ++ block cx.1 x)

def cnfContextFoldOutput {C : EncodedType}
    (acc : (cnfContextFoldAccEncodedType C).Carrier) : CNF :=
  match acc with
  | Sum.inl _ => []
  | Sum.inr cx => cx.2

def cnfContextFoldInstructions {C X : EncodedType}
    (c : C.Carrier) (xs : List X.Carrier) :
    List (cnfContextFoldInstructionEncodedType C X).Carrier :=
  Sum.inl c :: xs.map Sum.inr

theorem cnfContextFoldStep_tm_polytime {C X : EncodedType}
    (block : C.Carrier → X.Carrier → CNF)
    (hBlock :
      TMPolyTimeMap (EncodedType.prod C X) cnfStructuredEncodedType
        (fun p : C.Carrier × X.Carrier => block p.1 p.2)) :
    TMPolyTimeMap
      (EncodedType.prod (cnfContextFoldAccEncodedType C)
        (cnfContextFoldInstructionEncodedType C X))
      (cnfContextFoldAccEncodedType C)
      (cnfContextFoldStep block) := by
  let Acc := cnfContextFoldAccEncodedType C
  let Instr := cnfContextFoldInstructionEncodedType C X
  have hLeft :
      TMPolyTimeMap C Acc (fun c : C.Carrier => Sum.inr (c, ([] : CNF))) := by
    have hEmpty : TMPolyTimeMap C cnfStructuredEncodedType (fun _ : C.Carrier => ([] : CNF)) :=
      TMPolyTimeMap.const C cnfStructuredEncodedType []
    have hPair :
        TMPolyTimeMap C (EncodedType.prod C cnfStructuredEncodedType)
          (fun c : C.Carrier => (c, ([] : CNF))) :=
      TMPolyTimeMap.prod_mk (TMPolyTimeMap.id C) hEmpty
    have hInr :=
      TMPolyTimeMap.inr (EncodedType.raw Unit)
        (EncodedType.prod C cnfStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hInr hPair
    simpa [Acc, cnfContextFoldAccEncodedType, Function.comp] using hComp
  have hRight :
      TMPolyTimeMap (EncodedType.prod Acc X) Acc
        (fun p : Acc.Carrier × X.Carrier =>
          match p.1 with
          | Sum.inl _ => Sum.inl ()
          | Sum.inr cx => Sum.inr (cx.1, (show CNF from cx.2) ++ block cx.1 p.2)) := by
    let P := EncodedType.prod Acc X
    let Loaded := EncodedType.prod C cnfStructuredEncodedType
    have hElem : TMPolyTimeMap P X (fun p : P.Carrier => p.2) := by
      simpa [P] using TMPolyTimeMap.snd Acc X
    have hAcc : TMPolyTimeMap P Acc (fun p : P.Carrier => p.1) := by
      simpa [P] using TMPolyTimeMap.fst Acc X
    have hSwap :
        TMPolyTimeMap P (EncodedType.prod X Acc)
          (fun p : P.Carrier => (p.2, p.1)) :=
      TMPolyTimeMap.prod_mk hElem hAcc
    have hChoice := prodSumChoice_tm_polytime X (EncodedType.raw Unit) Loaded
    have hUnloaded :
        TMPolyTimeMap (EncodedType.raw Unit) Acc (fun _ : Unit => Sum.inl ()) := by
      simpa [Acc, cnfContextFoldAccEncodedType] using
        TMPolyTimeMap.inl (EncodedType.raw Unit) Loaded
    have hLoaded :
        TMPolyTimeMap (EncodedType.prod X Loaded) Acc
          (fun p : X.Carrier × Loaded.Carrier =>
            Sum.inr (p.2.1, (show CNF from p.2.2) ++ block p.2.1 p.1)) := by
      let Q := EncodedType.prod X Loaded
      have hX : TMPolyTimeMap Q X (fun p : Q.Carrier => p.1) := by
        simpa [Q] using TMPolyTimeMap.fst X Loaded
      have hLoadedPayload : TMPolyTimeMap Q Loaded (fun p : Q.Carrier => p.2) := by
        simpa [Q] using TMPolyTimeMap.snd X Loaded
      have hCtx : TMPolyTimeMap Q C (fun p : Q.Carrier => p.2.1) := by
        have hFst := TMPolyTimeMap.fst C cnfStructuredEncodedType
        have hComp := TMPolyTimeMap.comp hFst hLoadedPayload
        simpa [Function.comp, Loaded, Q] using hComp
      have hOut : TMPolyTimeMap Q cnfStructuredEncodedType (fun p : Q.Carrier => p.2.2) := by
        have hSnd := TMPolyTimeMap.snd C cnfStructuredEncodedType
        have hComp := TMPolyTimeMap.comp hSnd hLoadedPayload
        simpa [Function.comp, Loaded, Q] using hComp
      have hBlockInput :
          TMPolyTimeMap Q (EncodedType.prod C X)
            (fun p : Q.Carrier => (p.2.1, p.1)) :=
        TMPolyTimeMap.prod_mk hCtx hX
      have hBlockQ :
          TMPolyTimeMap Q cnfStructuredEncodedType
            (fun p : Q.Carrier => block p.2.1 p.1) := by
        have hComp := TMPolyTimeMap.comp hBlock hBlockInput
        simpa [Function.comp, Q] using hComp
      have hAppendInput :
          TMPolyTimeMap Q
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun p : Q.Carrier => (p.2.2, block p.2.1 p.1)) :=
        TMPolyTimeMap.prod_mk hOut hBlockQ
      have hAppend :
          TMPolyTimeMap Q cnfStructuredEncodedType
            (fun p : Q.Carrier => (show CNF from p.2.2) ++ block p.2.1 p.1) := by
        have hComp := TMPolyTimeMap.comp
          (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
        simpa [Function.comp, cnfStructuredEncodedType, Q] using hComp
      have hPair :
          TMPolyTimeMap Q Loaded
            (fun p : Q.Carrier =>
              (p.2.1, (show CNF from p.2.2) ++ block p.2.1 p.1)) :=
        TMPolyTimeMap.prod_mk hCtx hAppend
      have hInr := TMPolyTimeMap.inr (EncodedType.raw Unit) Loaded
      have hComp := TMPolyTimeMap.comp hInr hPair
      simpa [Function.comp, Acc, Loaded, cnfContextFoldAccEncodedType, Q] using hComp
    have hBranches := TMPolyTimeMap.sum_elim hUnloaded hLoaded
    have hDispatch := TMPolyTimeMap.comp hBranches hChoice
    have hComp := TMPolyTimeMap.comp hDispatch hSwap
    convert hComp using 1
    funext p
    rcases p with ⟨acc, x⟩
    cases acc <;> rfl
  have hChoice := prodSumChoice_tm_polytime Acc C X
  have hBranches := TMPolyTimeMap.sum_elim hLeft hRight
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem cnfContextFoldOutput_tm_polytime (C : EncodedType) :
    TMPolyTimeMap (cnfContextFoldAccEncodedType C) cnfStructuredEncodedType
      cnfContextFoldOutput := by
  let Loaded := EncodedType.prod C cnfStructuredEncodedType
  have hLeft :
      TMPolyTimeMap (EncodedType.raw Unit) cnfStructuredEncodedType
        (fun _ : Unit => ([] : CNF)) :=
    TMPolyTimeMap.const (EncodedType.raw Unit) cnfStructuredEncodedType []
  have hRight :
      TMPolyTimeMap Loaded cnfStructuredEncodedType
        (fun p : Loaded.Carrier => p.2) := by
    simpa [Loaded] using TMPolyTimeMap.snd C cnfStructuredEncodedType
  have h := TMPolyTimeMap.sum_elim hLeft hRight
  convert h using 1
  funext acc
  cases acc <;> rfl

theorem cnfContextFoldInstructions_tm_polytime (C X : EncodedType) :
    TMPolyTimeMap
      (EncodedType.prod C (EncodedType.list X))
      (cnfContextFoldInstructionListEncodedType C X)
      (fun p : C.Carrier × List X.Carrier => cnfContextFoldInstructions p.1 p.2) := by
  let P := EncodedType.prod C (EncodedType.list X)
  let Instr := cnfContextFoldInstructionEncodedType C X
  have hCtx : TMPolyTimeMap P C (fun p : P.Carrier => p.1) := by
    simpa [P] using TMPolyTimeMap.fst C (EncodedType.list X)
  have hList : TMPolyTimeMap P (EncodedType.list X) (fun p : P.Carrier => p.2) := by
    simpa [P] using TMPolyTimeMap.snd C (EncodedType.list X)
  have hHead : TMPolyTimeMap P Instr (fun p : P.Carrier => Sum.inl p.1) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.inl C X) hCtx
    simpa [Function.comp, Instr, P, cnfContextFoldInstructionEncodedType] using hComp
  have hRightInstr : TMPolyTimeMap X Instr (fun x : X.Carrier => Sum.inr x) := by
    simpa [Instr, cnfContextFoldInstructionEncodedType] using TMPolyTimeMap.inr C X
  have hTail :
      TMPolyTimeMap P (cnfContextFoldInstructionListEncodedType C X)
        (fun p : P.Carrier => p.2.map Sum.inr) := by
    have hMap := TMPolyTimeMap.list_map hRightInstr
    have hComp := TMPolyTimeMap.comp hMap hList
    simpa [Function.comp, cnfContextFoldInstructionListEncodedType, Instr, P] using hComp
  have hConsInput :
      TMPolyTimeMap P
        (EncodedType.prod Instr (cnfContextFoldInstructionListEncodedType C X))
        (fun p : P.Carrier => (Sum.inl p.1, p.2.map Sum.inr)) :=
    TMPolyTimeMap.prod_mk hHead hTail
  have hCons := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons Instr) hConsInput
  simpa [Function.comp, cnfContextFoldInstructions, cnfContextFoldInstructionListEncodedType,
    Instr, P] using hCons

theorem cnfContextFoldRightInstructions_eq {C X : EncodedType}
    (block : C.Carrier → X.Carrier → CNF)
    (c : C.Carrier) (xs : List X.Carrier) (out : CNF) :
    (xs.map Sum.inr).foldl
        (fun acc instr => cnfContextFoldStep block (acc, instr))
        (Sum.inr (c, out) : (cnfContextFoldAccEncodedType C).Carrier) =
      Sum.inr (c, out ++ xs.flatMap fun x => block c x) := by
  induction xs generalizing out with
  | nil =>
      simpa using
        (show
          (Sum.inr (c, out) : (cnfContextFoldAccEncodedType C).Carrier) =
            Sum.inr (c, out) from rfl)
  | cons x xs ih =>
      simpa [cnfContextFoldStep, List.append_assoc] using ih (out ++ block c x)

theorem cnfContextFoldInstructions_eq_flatMap {C X : EncodedType}
    (block : C.Carrier → X.Carrier → CNF)
    (c : C.Carrier) (xs : List X.Carrier) :
    (cnfContextFoldInstructions c xs).foldl
        (fun acc instr => cnfContextFoldStep block (acc, instr))
        (cnfContextFoldInitAcc C) =
      Sum.inr (c, xs.flatMap fun x => block c x) := by
  rw [cnfContextFoldInstructions]
  rw [List.foldl_cons]
  simpa [cnfContextFoldInitAcc, cnfContextFoldStep] using
    cnfContextFoldRightInstructions_eq block c xs []

theorem cnfContextFlatMap_tm_polytime {C X : EncodedType}
    (block : C.Carrier → X.Carrier → CNF)
    (hBlock :
      TMPolyTimeMap (EncodedType.prod C X) cnfStructuredEncodedType
        (fun p : C.Carrier × X.Carrier => block p.1 p.2)) :
    TMPolyTimeMap
      (EncodedType.prod C (EncodedType.list X))
      cnfStructuredEncodedType
      (fun p : C.Carrier × List X.Carrier =>
        p.2.flatMap fun x => block p.1 x) := by
  rcases hBlock with ⟨hBlockRaw⟩
  let Acc := cnfContextFoldAccEncodedType C
  let Instr := cnfContextFoldInstructionEncodedType C X
  let InstrList := cnfContextFoldInstructionListEncodedType C X
  have hBlockMap :
      TMPolyTimeMap (EncodedType.prod C X) cnfStructuredEncodedType
        (fun p : C.Carrier × X.Carrier => block p.1 p.2) :=
    ⟨hBlockRaw⟩
  rcases cnfContextFoldStep_tm_polytime block hBlockMap with ⟨hStep⟩
  let B := TM2Programs.finTM2StepPushBound hBlockRaw.tm
  let grow : Polynomial Nat :=
    Polynomial.C 4 * Polynomial.X + Polynomial.C 4 +
      hBlockRaw.time.comp (Polynomial.C 2 * Polynomial.X + Polynomial.C 1) *
        Polynomial.C B
  let Inv : Nat → Acc.Carrier → Prop :=
    fun N acc =>
      match acc with
      | Sum.inl _ => True
      | Sum.inr cx => C.inputSize cx.1 ≤ N
  have hFold :
      TMPolyTimeMap InstrList Acc
        (fun is : List Instr.Carrier =>
          is.foldl (fun acc instr => cnfContextFoldStep block (acc, instr))
            (cnfContextFoldInitAcc C)) := by
    refine
      TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
        Instr Acc (cnfContextFoldStep block) (cnfContextFoldInitAcc C)
        hStep (Polynomial.C 1) grow Inv ?_ ?_
    · intro source
      constructor
      · simp [Inv, cnfContextFoldInitAcc]
      · simp [Acc, cnfContextFoldAccEncodedType, cnfContextFoldInitAcc,
          EncodedType.inputSize, EncodedType.sum, EncodedType.raw]
    · intro source acc instr hInv hInstrSize
      let N := (EncodedType.list Instr).inputSize source
      have hGrowEval :
          grow.eval N =
            4 * N + 4 + hBlockRaw.time.eval (2 * N + 1) * B := by
        simp [grow, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
          Polynomial.eval_X, B, Nat.add_assoc]
      cases instr with
      | inl c =>
          have hcN : C.inputSize c ≤ N := by
            have h : C.inputSize c + 1 ≤ N := by
              simpa [Instr, cnfContextFoldInstructionEncodedType, EncodedType.inputSize,
                EncodedType.sum] using hInstrSize
            omega
          constructor
          · simpa [Inv, cnfContextFoldStep] using hcN
          · have hSize :
                Acc.inputSize (Sum.inr (c, ([] : CNF))) = C.inputSize c + 2 := by
              have hNilEncode :
                  (cnfStructuredEncodedType.encode ([] : CNF)).length = 0 := by
                change (EncodedType.list clauseStructuredEncodedType).inputSize ([] : CNF) = 0
                exact EncodedType.inputSize_list_nil clauseStructuredEncodedType
              rw [EncodedType.inputSize]
              simp [Acc, cnfContextFoldAccEncodedType, EncodedType.sum, EncodedType.prod,
                EncodedType.inputSize, hNilEncode]
            have hOut :
                Acc.inputSize (Sum.inr (c, ([] : CNF))) ≤ grow.eval N := by
              rw [hSize, hGrowEval]
              nlinarith [hcN, Nat.zero_le (hBlockRaw.time.eval (2 * N + 1) * B)]
            calc
              Acc.inputSize (cnfContextFoldStep block (acc, Sum.inl c))
                  = Acc.inputSize (Sum.inr (c, ([] : CNF))) := by
                    cases acc <;> rfl
              _ ≤ grow.eval N := hOut
              _ ≤ Acc.inputSize acc + grow.eval N := Nat.le_add_left _ _
      | inr x =>
          have hxN : X.inputSize x ≤ N := by
            have h : X.inputSize x + 1 ≤ N := by
              simpa [Instr, cnfContextFoldInstructionEncodedType, EncodedType.inputSize,
                EncodedType.sum] using hInstrSize
            omega
          cases acc with
          | inl u =>
              constructor
              · simp [Inv, cnfContextFoldStep]
              · simp [cnfContextFoldStep]
                exact Nat.le_add_right _ _
          | inr cx =>
              rcases cx with ⟨c, out⟩
              have hcN : C.inputSize c ≤ N := by
                simpa [Inv] using hInv
              have hArg :
                  (EncodedType.prod C X).inputSize (c, x) ≤ 2 * N + 1 := by
                rw [EncodedType.inputSize_prod]
                change C.inputSize c + 1 + X.inputSize x ≤ 2 * N + 1
                omega
              have hTimeMono :
                  hBlockRaw.time.eval ((EncodedType.prod C X).inputSize (c, x)) ≤
                    hBlockRaw.time.eval (2 * N + 1) :=
                TM2Programs.polynomialNat_eval_mono hBlockRaw.time hArg
              have hOutBoundRaw :=
                TM2Programs.tm2ComputableInPolyTime_output_length_le hBlockRaw (c, x)
              have hBlockSize :
                  cnfStructuredEncodedType.inputSize (block c x) ≤ grow.eval N := by
                have hRaw :
                    cnfStructuredEncodedType.inputSize (block c x) ≤
                      (EncodedType.prod C X).inputSize (c, x) +
                        hBlockRaw.time.eval ((EncodedType.prod C X).inputSize (c, x)) * B := by
                  simpa [EncodedType.inputSize, B] using hOutBoundRaw
                have hBound :
                    (EncodedType.prod C X).inputSize (c, x) +
                        hBlockRaw.time.eval ((EncodedType.prod C X).inputSize (c, x)) * B ≤
                      4 * N + 4 + hBlockRaw.time.eval (2 * N + 1) * B := by
                  have hArgGrow :
                      (EncodedType.prod C X).inputSize (c, x) ≤ 4 * N + 4 := by
                    nlinarith [hArg]
                  have hTimeGrow :
                      hBlockRaw.time.eval ((EncodedType.prod C X).inputSize (c, x)) * B ≤
                        hBlockRaw.time.eval (2 * N + 1) * B :=
                    Nat.mul_le_mul_right B hTimeMono
                  exact Nat.add_le_add hArgGrow hTimeGrow
                exact hRaw.trans (by simpa [hGrowEval] using hBound)
              constructor
              · simpa [Inv, cnfContextFoldStep] using hcN
              · have hAppend :
                    cnfStructuredEncodedType.inputSize ((show CNF from out) ++ block c x) =
                      cnfStructuredEncodedType.inputSize out +
                        cnfStructuredEncodedType.inputSize (block c x) := by
                  simpa [cnfStructuredEncodedType] using
                    list_inputSize_append clauseStructuredEncodedType
                      (show CNF from out) (block c x)
                have hStepSize :
                    Acc.inputSize (cnfContextFoldStep block (Sum.inr (c, out), Sum.inr x)) =
                      Acc.inputSize (Sum.inr (c, out) : Acc.Carrier) +
                        cnfStructuredEncodedType.inputSize (block c x) := by
                  simp [Acc, cnfContextFoldAccEncodedType, cnfContextFoldStep,
                    EncodedType.inputSize, EncodedType.sum, EncodedType.prod]
                  change
                    C.inputSize c +
                          (cnfStructuredEncodedType.inputSize
                              ((show CNF from out) ++ block c x) + 1) + 1 =
                        C.inputSize c +
                            (cnfStructuredEncodedType.inputSize out + 1) + 1 +
                          cnfStructuredEncodedType.inputSize (block c x)
                  rw [hAppend]
                  omega
                rw [hStepSize]
                exact Nat.add_le_add_left hBlockSize _
  have hInstr := cnfContextFoldInstructions_tm_polytime C X
  have hFoldFromInput :
      TMPolyTimeMap (EncodedType.prod C (EncodedType.list X)) Acc
        (fun p : C.Carrier × List X.Carrier =>
          (cnfContextFoldInstructions p.1 p.2).foldl
            (fun acc instr => cnfContextFoldStep block (acc, instr))
            (cnfContextFoldInitAcc C)) := by
    have hComp := TMPolyTimeMap.comp hFold hInstr
    simpa [Function.comp, InstrList] using hComp
  have hOut := cnfContextFoldOutput_tm_polytime C
  have hComp := TMPolyTimeMap.comp hOut hFoldFromInput
  convert hComp using 1
  funext p
  rw [Function.comp]
  rw [cnfContextFoldInstructions_eq_flatMap block p.1 p.2]
  rfl

end SAT
end ComplexityReduction
