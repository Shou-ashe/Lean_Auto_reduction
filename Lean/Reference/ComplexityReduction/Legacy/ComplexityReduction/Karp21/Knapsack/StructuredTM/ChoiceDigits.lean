import Mathlib.Data.List.Range
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.RowLookup
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.SlackPowers
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.DigitCodeList

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

open ComplexityReduction.Combinatorics

@[simp] theorem binaryNatList_inputSize_nil :
    (EncodedType.list EncodedType.binaryNat).inputSize ([] : List Nat) = 0 :=
  EncodedType.inputSize_list_nil EncodedType.binaryNat

@[simp] theorem binaryInt_inputSize_ofNat_payload (n : Nat) :
    EncodedType.binaryInt.inputSize (Int.ofNat n) =
      EncodedType.binaryNat.inputSize n + 1 := by
  simp [EncodedType.inputSize, EncodedType.binaryInt]

@[simp] theorem binaryInt_inputSize_negSucc_payload (n : Nat) :
    EncodedType.binaryInt.inputSize (Int.negSucc n) =
      EncodedType.binaryNat.inputSize n + 1 := by
  simp [EncodedType.inputSize, EncodedType.binaryInt]

/-!
Executable compact Knapsack code generation.

This file builds the remaining direct binary witnesses for the compact
`0-1 IP -> Knapsack` route.  The first layer below generates the variable-choice
digits by scanning structural fuel (`compactTargetOnes`) rather than expanding an
arbitrary binary natural range.
-/

def compactChoiceDigitsAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat
    (EncodedType.prod EncodedType.binaryNat (EncodedType.list EncodedType.binaryNat))

abbrev CompactChoiceDigitsAcc := Nat × Nat × List Nat

def compactChoiceDigitsInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool EncodedType.binaryNat

def compactChoiceDigitsInstructionListEncodedType : EncodedType :=
  EncodedType.list compactChoiceDigitsInstructionEncodedType

def compactChoiceDigitsInputEncodedType : EncodedType :=
  EncodedType.prod (EncodedType.list EncodedType.binaryNat) EncodedType.binaryNat

def compactChoiceDigitsInitAcc : CompactChoiceDigitsAcc :=
  ((0 : Nat), ((0 : Nat), ([] : List Nat)))

def compactChoiceDigitsInitInstruction (target : Nat) :
    compactChoiceDigitsInstructionEncodedType.Carrier :=
  (false, target)

def compactChoiceDigitsTickInstruction (_fuel : Nat) :
    compactChoiceDigitsInstructionEncodedType.Carrier :=
  (true, (0 : Nat))

def compactChoiceDigitsInstructions (p : List Nat × Nat) :
    List compactChoiceDigitsInstructionEncodedType.Carrier :=
  compactChoiceDigitsInitInstruction p.2 ::
    p.1.map compactChoiceDigitsTickInstruction

def compactChoiceDigitsStep
    (p : CompactChoiceDigitsAcc × compactChoiceDigitsInstructionEncodedType.Carrier) :
    CompactChoiceDigitsAcc :=
  match p.2.1 with
  | false => (p.2.2, ((0 : Nat), ([] : List Nat)))
  | true =>
      let target := p.1.1
      let idx := p.1.2.1
      let out := p.1.2.2
      (target, (idx.succ, out ++ [binaryNatEqDigit (idx, target)]))

def compactChoiceDigitsFromInstructions
    (xs : List compactChoiceDigitsInstructionEncodedType.Carrier) : List Nat :=
  (xs.foldl (fun acc instr => compactChoiceDigitsStep (acc, instr))
    compactChoiceDigitsInitAcc).2.2

def compactChoiceDigits (p : List Nat × Nat) : List Nat :=
  compactChoiceDigitsFromInstructions (compactChoiceDigitsInstructions p)

theorem compactChoiceDigitsTick_fold
    (fuel : List Nat) (target idx : Nat) (out : List Nat) :
    ((fuel.map compactChoiceDigitsTickInstruction).foldl
        (fun acc instr => compactChoiceDigitsStep (acc, instr))
        (target, (idx, out))).2.2 =
      out ++ (List.range' idx fuel.length).map fun j =>
        if j = target then (1 : Nat) else 0 := by
  induction fuel generalizing idx out with
  | nil =>
      simp
  | cons _fuel fuel ih =>
      rw [List.map_cons, List.foldl_cons]
      change
        (((fuel.map compactChoiceDigitsTickInstruction).foldl
              (fun acc instr => compactChoiceDigitsStep (acc, instr))
              (target, (idx.succ, out ++ [binaryNatEqDigit (idx, target)]))).2.2) =
          out ++ (List.range' idx (_fuel :: fuel).length).map fun j =>
            if j = target then (1 : Nat) else 0
      rw [ih idx.succ (out ++ [binaryNatEqDigit (idx, target)])]
      simp [binaryNatEqDigit, boolToBinaryNat, binaryNatEqBool_eq_true_iff,
        List.range'_succ, List.append_assoc, Nat.succ_eq_add_one]

theorem compactChoiceDigits_eq_range (fuel : List Nat) (target : Nat) :
    compactChoiceDigits (fuel, target) =
      (List.range fuel.length).map fun j => if j = target then (1 : Nat) else 0 := by
  have h := compactChoiceDigitsTick_fold fuel target 0 []
  simpa [compactChoiceDigits, compactChoiceDigitsFromInstructions,
    compactChoiceDigitsInstructions, compactChoiceDigitsInitInstruction,
    compactChoiceDigitsInitAcc, compactChoiceDigitsStep, List.range_eq_range'] using h

def compactVariableChoiceDigitsExecutable (I : IntegerProgrammingInput) (i : Nat) : List Nat :=
  compactChoiceDigits (compactTargetOnes I, i)

theorem compactVariableChoiceDigitsExecutable_eq
    (I : IntegerProgrammingInput) (i : Nat) :
    compactVariableChoiceDigitsExecutable I i = compactVariableChoiceDigits I i := by
  rw [compactVariableChoiceDigitsExecutable, compactChoiceDigits_eq_range]
  simp [compactVariableChoiceDigits, compactTargetOnes_eq_replicate]

theorem compactChoiceDigitsInitInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.binaryNat
      compactChoiceDigitsInstructionEncodedType
      compactChoiceDigitsInitInstruction := by
  let X := EncodedType.binaryNat
  have hTag : TMPolyTimeMap X EncodedType.bool (fun _ : Nat => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hPayload : TMPolyTimeMap X EncodedType.binaryNat (fun target : Nat => target) :=
    TMPolyTimeMap.id X
  have hOut := TMPolyTimeMap.prod_mk hTag hPayload
  simpa [compactChoiceDigitsInitInstruction, compactChoiceDigitsInstructionEncodedType, X]
    using hOut

theorem compactChoiceDigitsTickInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.binaryNat
      compactChoiceDigitsInstructionEncodedType
      compactChoiceDigitsTickInstruction := by
  let X := EncodedType.binaryNat
  have hTag : TMPolyTimeMap X EncodedType.bool (fun _ : Nat => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hZero : TMPolyTimeMap X EncodedType.binaryNat (fun _ : Nat => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.binaryNat (0 : Nat)
  have hOut := TMPolyTimeMap.prod_mk hTag hZero
  simpa [compactChoiceDigitsTickInstruction, compactChoiceDigitsInstructionEncodedType, X]
    using hOut

theorem compactChoiceDigitsInstructions_tm_polytime :
    TMPolyTimeMap
      compactChoiceDigitsInputEncodedType
      compactChoiceDigitsInstructionListEncodedType
      compactChoiceDigitsInstructions := by
  let X := compactChoiceDigitsInputEncodedType
  let L := EncodedType.list EncodedType.binaryNat
  have hFuel : TMPolyTimeMap X L (fun p : List Nat × Nat => p.1) := by
    simpa [X, compactChoiceDigitsInputEncodedType, L] using
      TMPolyTimeMap.fst L EncodedType.binaryNat
  have hTarget : TMPolyTimeMap X EncodedType.binaryNat (fun p : List Nat × Nat => p.2) := by
    simpa [X, compactChoiceDigitsInputEncodedType, L] using
      TMPolyTimeMap.snd L EncodedType.binaryNat
  have hInit :
      TMPolyTimeMap X compactChoiceDigitsInstructionEncodedType
        (fun p : List Nat × Nat => compactChoiceDigitsInitInstruction p.2) := by
    have hComp := TMPolyTimeMap.comp compactChoiceDigitsInitInstruction_tm_polytime hTarget
    simpa [Function.comp, X] using hComp
  have hTicks :
      TMPolyTimeMap X compactChoiceDigitsInstructionListEncodedType
        (fun p : List Nat × Nat => p.1.map compactChoiceDigitsTickInstruction) := by
    have hMap := TMPolyTimeMap.list_map compactChoiceDigitsTickInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hFuel
    simpa [Function.comp, compactChoiceDigitsInstructionListEncodedType, X, L] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod compactChoiceDigitsInstructionEncodedType
          compactChoiceDigitsInstructionListEncodedType)
        (fun p : List Nat × Nat =>
          (compactChoiceDigitsInitInstruction p.2,
            p.1.map compactChoiceDigitsTickInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hTicks
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons compactChoiceDigitsInstructionEncodedType) hConsInput
  simpa [Function.comp, compactChoiceDigitsInstructions,
    compactChoiceDigitsInstructionListEncodedType, X] using hOut

theorem compactChoiceDigitsStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactChoiceDigitsAccEncodedType
        compactChoiceDigitsInstructionEncodedType)
      compactChoiceDigitsAccEncodedType
      compactChoiceDigitsStep := by
  let X := EncodedType.prod compactChoiceDigitsAccEncodedType
    compactChoiceDigitsInstructionEncodedType
  let A := compactChoiceDigitsAccEncodedType
  let Tail := EncodedType.prod EncodedType.binaryNat (EncodedType.list EncodedType.binaryNat)
  let L := EncodedType.list EncodedType.binaryNat
  have hAcc : TMPolyTimeMap X A
      (fun p : CompactChoiceDigitsAcc × compactChoiceDigitsInstructionEncodedType.Carrier =>
        p.1) := by
    simpa [X, A] using TMPolyTimeMap.fst A compactChoiceDigitsInstructionEncodedType
  have hInstr : TMPolyTimeMap X compactChoiceDigitsInstructionEncodedType
      (fun p : CompactChoiceDigitsAcc × compactChoiceDigitsInstructionEncodedType.Carrier =>
        p.2) := by
    simpa [X, A] using TMPolyTimeMap.snd A compactChoiceDigitsInstructionEncodedType
  have hTarget : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : CompactChoiceDigitsAcc × compactChoiceDigitsInstructionEncodedType.Carrier =>
        p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat Tail
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, compactChoiceDigitsAccEncodedType, X, Tail] using hComp
  have hAccTail : TMPolyTimeMap X Tail
      (fun p : CompactChoiceDigitsAcc × compactChoiceDigitsInstructionEncodedType.Carrier =>
        p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat Tail
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, compactChoiceDigitsAccEncodedType, X, Tail] using hComp
  have hIdx : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : CompactChoiceDigitsAcc × compactChoiceDigitsInstructionEncodedType.Carrier =>
        p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat L
    have hComp := TMPolyTimeMap.comp hFst hAccTail
    simpa [Function.comp, Tail, X, L] using hComp
  have hOutList : TMPolyTimeMap X L
      (fun p : CompactChoiceDigitsAcc × compactChoiceDigitsInstructionEncodedType.Carrier =>
        p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat L
    have hComp := TMPolyTimeMap.comp hSnd hAccTail
    simpa [Function.comp, Tail, X, L] using hComp
  have hTag : TMPolyTimeMap X EncodedType.bool
      (fun p : CompactChoiceDigitsAcc × compactChoiceDigitsInstructionEncodedType.Carrier =>
        p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, compactChoiceDigitsInstructionEncodedType, X] using hComp
  have hPayload : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : CompactChoiceDigitsAcc × compactChoiceDigitsInstructionEncodedType.Carrier =>
        p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, compactChoiceDigitsInstructionEncodedType, X] using hComp
  have hZero : TMPolyTimeMap X EncodedType.binaryNat
      (fun _ : CompactChoiceDigitsAcc × compactChoiceDigitsInstructionEncodedType.Carrier =>
        (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.binaryNat (0 : Nat)
  have hEmpty : TMPolyTimeMap X L
      (fun _ : CompactChoiceDigitsAcc × compactChoiceDigitsInstructionEncodedType.Carrier =>
        ([] : List Nat)) :=
    TMPolyTimeMap.const X L []
  have hFalseTail : TMPolyTimeMap X Tail
      (fun _ : CompactChoiceDigitsAcc × compactChoiceDigitsInstructionEncodedType.Carrier =>
        ((0 : Nat), ([] : List Nat))) :=
    TMPolyTimeMap.prod_mk hZero hEmpty
  have hFalse : TMPolyTimeMap X A
      (fun p : CompactChoiceDigitsAcc × compactChoiceDigitsInstructionEncodedType.Carrier =>
        (p.2.2, ((0 : Nat), ([] : List Nat)))) :=
    TMPolyTimeMap.prod_mk hPayload hFalseTail
  have hIdxSucc : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : CompactChoiceDigitsAcc × compactChoiceDigitsInstructionEncodedType.Carrier =>
        p.1.2.1.succ) := by
    have hComp := TMPolyTimeMap.comp binaryNatSucc_tm_polytime hIdx
    simpa [Function.comp, X] using hComp
  have hEqInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : CompactChoiceDigitsAcc × compactChoiceDigitsInstructionEncodedType.Carrier =>
          (p.1.2.1, p.1.1)) :=
    TMPolyTimeMap.prod_mk hIdx hTarget
  have hEqDigit : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : CompactChoiceDigitsAcc × compactChoiceDigitsInstructionEncodedType.Carrier =>
        binaryNatEqDigit (p.1.2.1, p.1.1)) := by
    have hComp := TMPolyTimeMap.comp binaryNatEqDigit_tm_polytime hEqInput
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X (EncodedType.prod L EncodedType.binaryNat)
        (fun p : CompactChoiceDigitsAcc × compactChoiceDigitsInstructionEncodedType.Carrier =>
          (p.1.2.2, binaryNatEqDigit (p.1.2.1, p.1.1))) :=
    TMPolyTimeMap.prod_mk hOutList hEqDigit
  have hAppend : TMPolyTimeMap X L
      (fun p : CompactChoiceDigitsAcc × compactChoiceDigitsInstructionEncodedType.Carrier =>
        p.1.2.2 ++ [binaryNatEqDigit (p.1.2.1, p.1.1)]) := by
    have hComp := TMPolyTimeMap.comp binaryNatListAppendSingleton_tm_polytime hAppendInput
    simpa [Function.comp, X, L] using hComp
  have hTrueTail : TMPolyTimeMap X Tail
      (fun p : CompactChoiceDigitsAcc × compactChoiceDigitsInstructionEncodedType.Carrier =>
        (p.1.2.1.succ, p.1.2.2 ++ [binaryNatEqDigit (p.1.2.1, p.1.1)])) :=
    TMPolyTimeMap.prod_mk hIdxSucc hAppend
  have hTrue : TMPolyTimeMap X A
      (fun p : CompactChoiceDigitsAcc × compactChoiceDigitsInstructionEncodedType.Carrier =>
        (p.1.1,
          (p.1.2.1.succ, p.1.2.2 ++ [binaryNatEqDigit (p.1.2.1, p.1.1)]))) :=
    TMPolyTimeMap.prod_mk hTarget hTrueTail
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : CompactChoiceDigitsAcc × compactChoiceDigitsInstructionEncodedType.Carrier =>
          (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hDispatch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p :
            Bool × (CompactChoiceDigitsAcc × compactChoiceDigitsInstructionEncodedType.Carrier) =>
          match p.1 with
          | true =>
              (p.2.1.1,
                (p.2.1.2.1.succ,
                  p.2.1.2.2 ++ [binaryNatEqDigit (p.2.1.2.1, p.2.1.1)]))
          | false => (p.2.2.2, ((0 : Nat), ([] : List Nat)))) :=
    Clique.boolProduct_dispatch_tm_polytime X A
      (fFalse := fun p :
          CompactChoiceDigitsAcc × compactChoiceDigitsInstructionEncodedType.Carrier =>
        (p.2.2, ((0 : Nat), ([] : List Nat))))
      (fTrue := fun p :
          CompactChoiceDigitsAcc × compactChoiceDigitsInstructionEncodedType.Carrier =>
        (p.1.1, (p.1.2.1.succ,
          p.1.2.2 ++ [binaryNatEqDigit (p.1.2.1, p.1.1)])))
      hFalse hTrue
  have hComp := TMPolyTimeMap.comp hDispatch hBranchInput
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases h : instr.1 <;> simp [Function.comp, compactChoiceDigitsStep, h]
  all_goals rfl

theorem compactChoiceDigitsInitAcc_bound
    (xs : List compactChoiceDigitsInstructionEncodedType.Carrier) :
    compactChoiceDigitsAccEncodedType.inputSize compactChoiceDigitsInitAcc ≤
      (Polynomial.C 20).eval (compactChoiceDigitsInstructionListEncodedType.inputSize xs) := by
  simp [compactChoiceDigitsInitAcc, compactChoiceDigitsAccEncodedType,
    EncodedType.inputSize_prod]

theorem compactChoiceDigitsInstruction_payload_inputSize_le
    (instr : compactChoiceDigitsInstructionEncodedType.Carrier) :
    EncodedType.binaryNat.inputSize instr.2 ≤
      compactChoiceDigitsInstructionEncodedType.inputSize instr := by
  rcases instr with ⟨tag, payload⟩
  simp [compactChoiceDigitsInstructionEncodedType, EncodedType.inputSize_prod]

theorem compactChoiceDigitsStep_growth
    (source : List compactChoiceDigitsInstructionEncodedType.Carrier)
    (acc : compactChoiceDigitsAccEncodedType.Carrier)
    (instr : compactChoiceDigitsInstructionEncodedType.Carrier)
    (hInstr :
      compactChoiceDigitsInstructionEncodedType.inputSize instr ≤
        compactChoiceDigitsInstructionListEncodedType.inputSize source) :
    compactChoiceDigitsAccEncodedType.inputSize (compactChoiceDigitsStep (acc, instr)) ≤
      compactChoiceDigitsAccEncodedType.inputSize acc +
        (Polynomial.C 50 * Polynomial.X + Polynomial.C 100).eval
          (compactChoiceDigitsInstructionListEncodedType.inputSize source) := by
  change CompactChoiceDigitsAcc at acc
  rcases acc with ⟨target, idx, out⟩
  rcases instr with ⟨tag, payload⟩
  have hPayload :
      EncodedType.binaryNat.inputSize payload ≤
        compactChoiceDigitsInstructionListEncodedType.inputSize source :=
    (compactChoiceDigitsInstruction_payload_inputSize_le (tag, payload)).trans hInstr
  have hSucc := binaryNatAdd_inputSize_le idx 1
  have hOneSize : EncodedType.binaryNat.inputSize (1 : Nat) = 1 := by
    simp [EncodedType.inputSize, EncodedType.binaryNat]
  have hEqDigitSize :
      EncodedType.binaryNat.inputSize (binaryNatEqDigit (idx, target)) ≤ 1 := by
    by_cases h : idx = target
    · simp [binaryNatEqDigit, boolToBinaryNat, binaryNatEqBool_eq_true_iff, h, hOneSize]
    · have hFalse : binaryNatEqBool (idx, target) = false := by
        exact Bool.eq_false_iff.mpr ((binaryNatEqBool_eq_true_iff _).not.mpr h)
      simp [binaryNatEqDigit, boolToBinaryNat, hFalse, rowLookup_binaryNat_inputSize_zero]
  have hAppend :
      (EncodedType.list EncodedType.binaryNat).inputSize
          (out ++ [binaryNatEqDigit (idx, target)]) =
        (EncodedType.list EncodedType.binaryNat).inputSize out +
          EncodedType.binaryNat.inputSize (binaryNatEqDigit (idx, target)) + 1 :=
    encodedList_inputSize_append_singleton EncodedType.binaryNat out
      (binaryNatEqDigit (idx, target))
  cases tag
  · simp [compactChoiceDigitsStep, compactChoiceDigitsAccEncodedType,
      EncodedType.inputSize_prod, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, rowLookup_binaryNat_inputSize_zero]
    omega
  · simp [compactChoiceDigitsStep, compactChoiceDigitsAccEncodedType,
      EncodedType.inputSize_prod, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Nat.succ_eq_add_one, hAppend] at hSucc ⊢
    omega

theorem compactChoiceDigitsFold_tm_polytime :
    TMPolyTimeMap
      compactChoiceDigitsInstructionListEncodedType
      compactChoiceDigitsAccEncodedType
      (fun xs : List compactChoiceDigitsInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => compactChoiceDigitsStep (acc, instr))
          compactChoiceDigitsInitAcc) := by
  rcases compactChoiceDigitsStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      compactChoiceDigitsInstructionEncodedType compactChoiceDigitsAccEncodedType
      compactChoiceDigitsStep compactChoiceDigitsInitAcc hStep
      (Polynomial.C 20) (Polynomial.C 50 * Polynomial.X + Polynomial.C 100) ?_ ?_
  · intro xs
    exact compactChoiceDigitsInitAcc_bound xs
  · intro source acc instr hInstr
    exact compactChoiceDigitsStep_growth source acc instr hInstr

theorem compactChoiceDigitsFromInstructions_tm_polytime :
    TMPolyTimeMap
      compactChoiceDigitsInstructionListEncodedType
      (EncodedType.list EncodedType.binaryNat)
      compactChoiceDigitsFromInstructions := by
  let Tail := EncodedType.prod EncodedType.binaryNat (EncodedType.list EncodedType.binaryNat)
  have hTail : TMPolyTimeMap compactChoiceDigitsAccEncodedType Tail
      (fun acc : CompactChoiceDigitsAcc => acc.2) := by
    simpa [compactChoiceDigitsAccEncodedType, Tail] using
      TMPolyTimeMap.snd EncodedType.binaryNat Tail
  have hOut : TMPolyTimeMap Tail (EncodedType.list EncodedType.binaryNat)
      (fun tail : Nat × List Nat => tail.2) := by
    simpa [Tail] using
      TMPolyTimeMap.snd EncodedType.binaryNat (EncodedType.list EncodedType.binaryNat)
  have hTailComp := TMPolyTimeMap.comp hTail compactChoiceDigitsFold_tm_polytime
  have hOutComp := TMPolyTimeMap.comp hOut hTailComp
  simpa [Function.comp, compactChoiceDigitsFromInstructions, Tail] using hOutComp

theorem compactChoiceDigits_tm_polytime :
    TMPolyTimeMap
      compactChoiceDigitsInputEncodedType
      (EncodedType.list EncodedType.binaryNat)
      compactChoiceDigits := by
  have hComp :=
    TMPolyTimeMap.comp compactChoiceDigitsFromInstructions_tm_polytime
      compactChoiceDigitsInstructions_tm_polytime
  simpa [Function.comp, compactChoiceDigits] using hComp

theorem compactVariableChoiceDigitsExecutable_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod integerProgrammingBinaryStructuredEncodedType EncodedType.binaryNat)
      (EncodedType.list EncodedType.binaryNat)
      (fun p : IntegerProgrammingInput × Nat =>
        compactVariableChoiceDigitsExecutable p.1 p.2) := by
  let X := EncodedType.prod integerProgrammingBinaryStructuredEncodedType EncodedType.binaryNat
  have hI : TMPolyTimeMap X integerProgrammingBinaryStructuredEncodedType
      (fun p : IntegerProgrammingInput × Nat => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst integerProgrammingBinaryStructuredEncodedType EncodedType.binaryNat
  have hIdx : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : IntegerProgrammingInput × Nat => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd integerProgrammingBinaryStructuredEncodedType EncodedType.binaryNat
  have hFuel : TMPolyTimeMap X (EncodedType.list EncodedType.binaryNat)
      (fun p : IntegerProgrammingInput × Nat => compactTargetOnes p.1) := by
    have hComp := TMPolyTimeMap.comp compactTargetOnes_tm_polytime hI
    simpa [Function.comp, X] using hComp
  have hInput :
      TMPolyTimeMap X compactChoiceDigitsInputEncodedType
        (fun p : IntegerProgrammingInput × Nat => (compactTargetOnes p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hFuel hIdx
  have hComp := TMPolyTimeMap.comp compactChoiceDigits_tm_polytime hInput
  simpa [Function.comp, compactVariableChoiceDigitsExecutable,
    compactChoiceDigitsInputEncodedType, X] using hComp

end Knapsack
end Karp21
end ComplexityReduction
