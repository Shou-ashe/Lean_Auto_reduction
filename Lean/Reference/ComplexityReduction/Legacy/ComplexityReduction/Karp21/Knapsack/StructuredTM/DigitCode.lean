import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryMul
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.InvariantFold

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

/-!
Direct binary `Nat.ofDigits` witness for compact Knapsack code generation.

The compact route stores digit vectors little-endian.  The executable path first
reverses the digit list and then runs a Horner fold:
`acc ↦ acc * base + digit`.  The base is installed by an initial instruction so
the typed fold still has a fixed initial accumulator.
-/

def knapsackListReverseStep (X : EncodedType) (p : List X.Carrier × X.Carrier) :
    List X.Carrier :=
  p.2 :: p.1

theorem knapsackListReverseStep_tm_polytime (X : EncodedType) :
    TMPolyTimeMap
      (EncodedType.prod (EncodedType.list X) X)
      (EncodedType.list X)
      (knapsackListReverseStep X) := by
  let P := EncodedType.prod (EncodedType.list X) X
  have hHead : TMPolyTimeMap P X (fun p : P.Carrier => p.2) := by
    simpa [P] using TMPolyTimeMap.snd (EncodedType.list X) X
  have hTail : TMPolyTimeMap P (EncodedType.list X) (fun p : P.Carrier => p.1) := by
    simpa [P] using TMPolyTimeMap.fst (EncodedType.list X) X
  have hPair :
      TMPolyTimeMap P
        (EncodedType.prod X (EncodedType.list X))
        (fun p : P.Carrier => (p.2, p.1)) :=
    TMPolyTimeMap.prod_mk hHead hTail
  have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons X) hPair
  simpa [Function.comp, P, knapsackListReverseStep] using hComp

theorem knapsackListReverseFold_eq_reverse (X : EncodedType)
    (xs acc : List X.Carrier) :
    xs.foldl (fun acc x => knapsackListReverseStep X (acc, x)) acc =
      xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil =>
      simp [knapsackListReverseStep]
  | cons x xs ih =>
      rw [List.foldl_cons, ih]
      simp [knapsackListReverseStep, List.append_assoc]

theorem knapsackListReverse_tm_polytime (X : EncodedType) :
    TMPolyTimeMap
      (EncodedType.list X)
      (EncodedType.list X)
      List.reverse := by
  rcases knapsackListReverseStep_tm_polytime X with ⟨hStep⟩
  have hFold :
      TMPolyTimeMap
        (EncodedType.list X)
        (EncodedType.list X)
        (fun xs : List X.Carrier =>
          xs.foldl (fun acc x => knapsackListReverseStep X (acc, x)) []) := by
    refine
      TMPolyTimeMap.list_foldl_typed_growth_bounded
        X (EncodedType.list X)
        (knapsackListReverseStep X) ([] : List X.Carrier)
        hStep (Polynomial.C 0) (Polynomial.X + Polynomial.C 1) ?_ ?_
    · intro xs
      simp
    · intro source acc x hx
      simp [knapsackListReverseStep, Polynomial.eval_add, Polynomial.eval_X]
      omega
  convert hFold using 1
  funext xs
  simpa using (knapsackListReverseFold_eq_reverse X xs []).symm

def binaryNatOfDigitsInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat (EncodedType.list EncodedType.binaryNat)

def binaryNatOfDigitsAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat

def binaryNatOfDigitsInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool EncodedType.binaryNat

def binaryNatOfDigitsInstructionListEncodedType : EncodedType :=
  EncodedType.list binaryNatOfDigitsInstructionEncodedType

def binaryNatOfDigitsStepInputEncodedType : EncodedType :=
  EncodedType.prod binaryNatOfDigitsAccEncodedType binaryNatOfDigitsInstructionEncodedType

abbrev BinaryNatOfDigitsAcc := Nat × Nat
abbrev BinaryNatOfDigitsInstruction := Bool × Nat

def binaryNatOfDigitsInitAcc : BinaryNatOfDigitsAcc :=
  (0, 0)

def binaryNatOfDigitsInitInstruction (base : Nat) : BinaryNatOfDigitsInstruction :=
  (false, base)

def binaryNatOfDigitsDigitInstruction (digit : Nat) : BinaryNatOfDigitsInstruction :=
  (true, digit)

def binaryNatOfDigitsInstructions (p : Nat × List Nat) :
    List BinaryNatOfDigitsInstruction :=
  binaryNatOfDigitsInitInstruction p.1 ::
    p.2.reverse.map binaryNatOfDigitsDigitInstruction

def binaryNatOfDigitsStep
    (p : BinaryNatOfDigitsAcc × BinaryNatOfDigitsInstruction) :
    BinaryNatOfDigitsAcc :=
  if p.2.1 then
    (p.1.1, p.1.2 * p.1.1 + p.2.2)
  else
    (p.2.2, 0)

def binaryNatOfDigitsFold (xs : List BinaryNatOfDigitsInstruction) :
    BinaryNatOfDigitsAcc :=
  xs.foldl (fun acc instr => binaryNatOfDigitsStep (acc, instr))
    binaryNatOfDigitsInitAcc

def binaryNatOfDigitsFromInstructions
    (xs : List BinaryNatOfDigitsInstruction) : Nat :=
  (binaryNatOfDigitsFold xs).2

def binaryNatOfDigitsExecutable (p : Nat × List Nat) : Nat :=
  binaryNatOfDigitsFromInstructions (binaryNatOfDigitsInstructions p)

def binaryNatOfDigits (p : Nat × List Nat) : Nat :=
  Nat.ofDigits p.1 p.2

theorem foldl_horner_reverse_eq_ofDigits
    (base : Nat) (digits : List Nat) (acc : Nat) :
    digits.reverse.foldl (fun acc digit => acc * base + digit) acc =
      acc * base ^ digits.length + Nat.ofDigits base digits := by
  induction digits with
  | nil =>
      simp
  | cons digit digits ih =>
      rw [List.reverse_cons, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      simp [Nat.ofDigits_cons, pow_succ]
      ring

theorem foldl_horner_reverse_zero_eq_ofDigits (base : Nat) (digits : List Nat) :
    digits.reverse.foldl (fun acc digit => acc * base + digit) 0 =
      Nat.ofDigits base digits := by
  simpa using foldl_horner_reverse_eq_ofDigits base digits 0

theorem binaryNatOfDigits_digitInstructions_fold
    (base : Nat) (digits : List Nat) (acc : Nat) :
    (digits.map binaryNatOfDigitsDigitInstruction).foldl
        (fun acc instr => binaryNatOfDigitsStep (acc, instr)) (base, acc) =
      (base, digits.foldl (fun acc digit => acc * base + digit) acc) := by
  induction digits generalizing acc with
  | nil =>
      simp
  | cons digit digits ih =>
      change
        (digits.map binaryNatOfDigitsDigitInstruction).foldl
            (fun acc instr => binaryNatOfDigitsStep (acc, instr))
            (base, acc * base + digit) =
          (base, (digit :: digits).foldl (fun acc digit => acc * base + digit) acc)
      rw [ih]
      rfl

theorem binaryNatOfDigitsExecutable_eq_ofDigits (p : Nat × List Nat) :
    binaryNatOfDigitsExecutable p = Nat.ofDigits p.1 p.2 := by
  rcases p with ⟨base, digits⟩
  unfold binaryNatOfDigitsExecutable binaryNatOfDigitsFromInstructions
    binaryNatOfDigitsInstructions binaryNatOfDigitsFold
  simp only [binaryNatOfDigitsInitInstruction, binaryNatOfDigitsInitAcc, List.foldl_cons]
  change
    ((digits.reverse.map binaryNatOfDigitsDigitInstruction).foldl
        (fun acc instr => binaryNatOfDigitsStep (acc, instr)) (base, 0)).2 =
      Nat.ofDigits base digits
  rw [binaryNatOfDigits_digitInstructions_fold]
  exact foldl_horner_reverse_zero_eq_ofDigits base digits

theorem binaryNatMul_inputSize_le (a b : Nat) :
    EncodedType.binaryNat.inputSize (a * b) ≤
      EncodedType.binaryNat.inputSize a + EncodedType.binaryNat.inputSize b := by
  let sa := EncodedType.binaryNat.inputSize a
  let sb := EncodedType.binaryNat.inputSize b
  have ha : a < 2 ^ sa := by
    simpa [sa] using binaryNat_lt_two_pow_inputSize a
  have hb : b < 2 ^ sb := by
    simpa [sb] using binaryNat_lt_two_pow_inputSize b
  have hapos : 0 < 2 ^ sa := pow_pos (by decide : 0 < 2) _
  have hbpos : 0 < 2 ^ sb := pow_pos (by decide : 0 < 2) _
  have hmul : a * b < 2 ^ sa * 2 ^ sb := by
    nlinarith
  rw [← pow_add] at hmul
  exact binaryNat_inputSize_le_of_lt_two_pow hmul

theorem binaryNatOfDigitsInstruction_payload_inputSize_le
    (instr : BinaryNatOfDigitsInstruction) :
    EncodedType.binaryNat.inputSize instr.2 ≤
      binaryNatOfDigitsInstructionEncodedType.inputSize instr := by
  rcases instr with ⟨tag, payload⟩
  simp [binaryNatOfDigitsInstructionEncodedType, EncodedType.inputSize_prod]

theorem binaryNatOfDigitsInitInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.binaryNat
      binaryNatOfDigitsInstructionEncodedType
      binaryNatOfDigitsInitInstruction := by
  let X := EncodedType.binaryNat
  have hTag : TMPolyTimeMap X EncodedType.bool (fun _ : Nat => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hOut := TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  simpa [binaryNatOfDigitsInitInstruction, binaryNatOfDigitsInstructionEncodedType, X]
    using hOut

theorem binaryNatOfDigitsDigitInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.binaryNat
      binaryNatOfDigitsInstructionEncodedType
      binaryNatOfDigitsDigitInstruction := by
  let X := EncodedType.binaryNat
  have hTag : TMPolyTimeMap X EncodedType.bool (fun _ : Nat => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hOut := TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  simpa [binaryNatOfDigitsDigitInstruction, binaryNatOfDigitsInstructionEncodedType, X]
    using hOut

theorem binaryNatOfDigitsInstructions_tm_polytime :
    TMPolyTimeMap
      binaryNatOfDigitsInputEncodedType
      binaryNatOfDigitsInstructionListEncodedType
      binaryNatOfDigitsInstructions := by
  let X := binaryNatOfDigitsInputEncodedType
  have hBase : TMPolyTimeMap X EncodedType.binaryNat (fun p : Nat × List Nat => p.1) := by
    simpa [X, binaryNatOfDigitsInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.binaryNat (EncodedType.list EncodedType.binaryNat)
  have hDigits :
      TMPolyTimeMap X (EncodedType.list EncodedType.binaryNat)
        (fun p : Nat × List Nat => p.2) := by
    simpa [X, binaryNatOfDigitsInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.binaryNat (EncodedType.list EncodedType.binaryNat)
  have hInit :
      TMPolyTimeMap X binaryNatOfDigitsInstructionEncodedType
        (fun p : Nat × List Nat => binaryNatOfDigitsInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp binaryNatOfDigitsInitInstruction_tm_polytime hBase
    simpa [Function.comp, X] using hComp
  have hReverse :
      TMPolyTimeMap X (EncodedType.list EncodedType.binaryNat)
        (fun p : Nat × List Nat => p.2.reverse) := by
    have hComp := TMPolyTimeMap.comp
      (knapsackListReverse_tm_polytime EncodedType.binaryNat) hDigits
    simpa [Function.comp, X] using hComp
  have hDigitInstrs :
      TMPolyTimeMap X binaryNatOfDigitsInstructionListEncodedType
        (fun p : Nat × List Nat =>
          p.2.reverse.map binaryNatOfDigitsDigitInstruction) := by
    have hMap := TMPolyTimeMap.list_map binaryNatOfDigitsDigitInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hReverse
    convert hComp using 1
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod binaryNatOfDigitsInstructionEncodedType
          binaryNatOfDigitsInstructionListEncodedType)
        (fun p : Nat × List Nat =>
          (binaryNatOfDigitsInitInstruction p.1,
            p.2.reverse.map binaryNatOfDigitsDigitInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hDigitInstrs
  have hCons := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons binaryNatOfDigitsInstructionEncodedType) hConsInput
  convert hCons using 1

theorem binaryNatOfDigitsAccTotal_tm_polytime :
    TMPolyTimeMap
      binaryNatOfDigitsAccEncodedType
      EncodedType.binaryNat
      (fun acc : BinaryNatOfDigitsAcc => acc.2) := by
  simpa [binaryNatOfDigitsAccEncodedType] using
    TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryNat

theorem binaryNatOfDigitsStep_tm_polytime :
    TMPolyTimeMap
      binaryNatOfDigitsStepInputEncodedType
      binaryNatOfDigitsAccEncodedType
      binaryNatOfDigitsStep := by
  let X := binaryNatOfDigitsStepInputEncodedType
  have hAcc :
      TMPolyTimeMap X binaryNatOfDigitsAccEncodedType
        (fun p : BinaryNatOfDigitsAcc × BinaryNatOfDigitsInstruction => p.1) := by
    simpa [X, binaryNatOfDigitsStepInputEncodedType] using
      TMPolyTimeMap.fst binaryNatOfDigitsAccEncodedType
        binaryNatOfDigitsInstructionEncodedType
  have hInstr :
      TMPolyTimeMap X binaryNatOfDigitsInstructionEncodedType
        (fun p : BinaryNatOfDigitsAcc × BinaryNatOfDigitsInstruction => p.2) := by
    simpa [X, binaryNatOfDigitsStepInputEncodedType] using
      TMPolyTimeMap.snd binaryNatOfDigitsAccEncodedType
        binaryNatOfDigitsInstructionEncodedType
  have hBase :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun p : BinaryNatOfDigitsAcc × BinaryNatOfDigitsInstruction => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, binaryNatOfDigitsAccEncodedType, X] using hComp
  have hTotal :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun p : BinaryNatOfDigitsAcc × BinaryNatOfDigitsInstruction => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, binaryNatOfDigitsAccEncodedType, X] using hComp
  have hTag :
      TMPolyTimeMap X EncodedType.bool
        (fun p : BinaryNatOfDigitsAcc × BinaryNatOfDigitsInstruction => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, binaryNatOfDigitsInstructionEncodedType, X] using hComp
  have hPayload :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun p : BinaryNatOfDigitsAcc × BinaryNatOfDigitsInstruction => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, binaryNatOfDigitsInstructionEncodedType, X] using hComp
  have hMulInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : BinaryNatOfDigitsAcc × BinaryNatOfDigitsInstruction => (p.1.2, p.1.1)) :=
    TMPolyTimeMap.prod_mk hTotal hBase
  have hMul :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun p : BinaryNatOfDigitsAcc × BinaryNatOfDigitsInstruction => p.1.2 * p.1.1) := by
    have hComp := TMPolyTimeMap.comp binaryNatMul_tm_polytime hMulInput
    simpa [Function.comp, X] using hComp
  have hAddInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : BinaryNatOfDigitsAcc × BinaryNatOfDigitsInstruction =>
          (p.1.2 * p.1.1, p.2.2)) :=
    TMPolyTimeMap.prod_mk hMul hPayload
  have hHorner :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun p : BinaryNatOfDigitsAcc × BinaryNatOfDigitsInstruction =>
          p.1.2 * p.1.1 + p.2.2) := by
    have hComp := TMPolyTimeMap.comp binaryNatAdd_tm_polytime hAddInput
    simpa [Function.comp, X] using hComp
  have hDigitBranch :
      TMPolyTimeMap X binaryNatOfDigitsAccEncodedType
        (fun p : BinaryNatOfDigitsAcc × BinaryNatOfDigitsInstruction =>
          (p.1.1, p.1.2 * p.1.1 + p.2.2)) :=
    TMPolyTimeMap.prod_mk hBase hHorner
  have hInitBranch :
      TMPolyTimeMap X binaryNatOfDigitsAccEncodedType
        (fun p : BinaryNatOfDigitsAcc × BinaryNatOfDigitsInstruction =>
          (p.2.2, (0 : Nat))) := by
    have hZero : TMPolyTimeMap X EncodedType.binaryNat (fun _ : X.Carrier => (0 : Nat)) :=
      TMPolyTimeMap.const X EncodedType.binaryNat (0 : Nat)
    exact TMPolyTimeMap.prod_mk hPayload hZero
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hDispatch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool X)
        binaryNatOfDigitsAccEncodedType
        (fun p : Bool × (BinaryNatOfDigitsAcc × BinaryNatOfDigitsInstruction) =>
          match p.1 with
          | true =>
              ((p.2.1.1 : Nat), (p.2.1.2 : Nat) * (p.2.1.1 : Nat) + (p.2.2.2 : Nat))
          | false => (p.2.2.2, (0 : Nat))) :=
    Clique.boolProduct_dispatch_tm_polytime X binaryNatOfDigitsAccEncodedType
      (fFalse := fun p : BinaryNatOfDigitsAcc × BinaryNatOfDigitsInstruction =>
        (p.2.2, (0 : Nat)))
      (fTrue := fun p : BinaryNatOfDigitsAcc × BinaryNatOfDigitsInstruction =>
        ((p.1.1 : Nat), (p.1.2 : Nat) * (p.1.1 : Nat) + (p.2.2 : Nat)))
      hInitBranch hDigitBranch
  have hComp := TMPolyTimeMap.comp hDispatch hBranchInput
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  rcases instr with ⟨tag, payload⟩
  cases tag <;> rfl

def binaryNatOfDigitsFoldInv (N : Nat) (acc : BinaryNatOfDigitsAcc) : Prop :=
  EncodedType.binaryNat.inputSize acc.1 ≤ N

theorem binaryNatOfDigitsStep_growth
    (source : List BinaryNatOfDigitsInstruction)
    (acc : BinaryNatOfDigitsAcc) (instr : BinaryNatOfDigitsInstruction)
    (hInv :
      binaryNatOfDigitsFoldInv
        (binaryNatOfDigitsInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      binaryNatOfDigitsInstructionEncodedType.inputSize instr ≤
        binaryNatOfDigitsInstructionListEncodedType.inputSize source) :
    binaryNatOfDigitsFoldInv
        (binaryNatOfDigitsInstructionListEncodedType.inputSize source)
        (binaryNatOfDigitsStep (acc, instr)) ∧
      binaryNatOfDigitsAccEncodedType.inputSize (binaryNatOfDigitsStep (acc, instr)) ≤
        binaryNatOfDigitsAccEncodedType.inputSize acc +
          ((Polynomial.C 4 * Polynomial.X + Polynomial.C 8).eval
            (binaryNatOfDigitsInstructionListEncodedType.inputSize source)) := by
  rcases acc with ⟨base, total⟩
  rcases instr with ⟨tag, payload⟩
  simp [binaryNatOfDigitsFoldInv] at hInv ⊢
  have hPayload :
      EncodedType.binaryNat.inputSize payload ≤
        binaryNatOfDigitsInstructionListEncodedType.inputSize source := by
    exact (binaryNatOfDigitsInstruction_payload_inputSize_le (tag, payload)).trans hInstr
  cases tag
  · constructor
    · exact hPayload
    · simp only [binaryNatOfDigitsStep, Bool.false_eq_true, ↓reduceIte]
      have hOutSmall :
          binaryNatOfDigitsAccEncodedType.inputSize (payload, (0 : Nat)) ≤
            binaryNatOfDigitsInstructionListEncodedType.inputSize source + 1 := by
        change
          (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat).inputSize
              (payload, (0 : Nat)) ≤
            binaryNatOfDigitsInstructionListEncodedType.inputSize source + 1
        rw [EncodedType.inputSize_prod]
        have hZero : EncodedType.binaryNat.inputSize (0 : Nat) = 0 := by
          simp [EncodedType.inputSize, EncodedType.binaryNat]
        rw [hZero]
        simpa using Nat.add_le_add_right hPayload 1
      have hBudget :
          binaryNatOfDigitsInstructionListEncodedType.inputSize source + 1 ≤
            binaryNatOfDigitsAccEncodedType.inputSize (base, total) +
              (4 * binaryNatOfDigitsInstructionListEncodedType.inputSize source + 8) := by
        have hAccNonneg :
            0 ≤ binaryNatOfDigitsAccEncodedType.inputSize (base, total) :=
          Nat.zero_le _
        omega
      exact hOutSmall.trans hBudget
  · have hMul := binaryNatMul_inputSize_le total base
    have hAdd := binaryNatAdd_inputSize_le_max (total * base) payload
    have hMax :
        max (EncodedType.binaryNat.inputSize (total * base))
            (EncodedType.binaryNat.inputSize payload) ≤
          EncodedType.binaryNat.inputSize total +
            binaryNatOfDigitsInstructionListEncodedType.inputSize source +
            binaryNatOfDigitsInstructionListEncodedType.inputSize source := by
      apply max_le
      · exact hMul.trans (by omega)
      · omega
    constructor
    · exact hInv
    · simp [binaryNatOfDigitsStep, binaryNatOfDigitsAccEncodedType,
        EncodedType.inputSize_prod]
      have hTotal :
          EncodedType.binaryNat.inputSize (total * base + payload) ≤
            EncodedType.binaryNat.inputSize total +
              binaryNatOfDigitsInstructionListEncodedType.inputSize source +
              binaryNatOfDigitsInstructionListEncodedType.inputSize source + 1 := by
        exact hAdd.trans (by omega)
      omega

theorem binaryNatOfDigitsFold_tm_polytime :
    TMPolyTimeMap
      binaryNatOfDigitsInstructionListEncodedType
      binaryNatOfDigitsAccEncodedType
      binaryNatOfDigitsFold := by
  rcases binaryNatOfDigitsStep_tm_polytime with ⟨hStep⟩
  have hFold :
      TMPolyTimeMap
        binaryNatOfDigitsInstructionListEncodedType
        binaryNatOfDigitsAccEncodedType
        (fun xs : List BinaryNatOfDigitsInstruction =>
          xs.foldl (fun acc instr => binaryNatOfDigitsStep (acc, instr))
            binaryNatOfDigitsInitAcc) := by
    refine
      TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
        binaryNatOfDigitsInstructionEncodedType binaryNatOfDigitsAccEncodedType
        binaryNatOfDigitsStep binaryNatOfDigitsInitAcc hStep
        (Polynomial.C 1) (Polynomial.C 4 * Polynomial.X + Polynomial.C 8)
        binaryNatOfDigitsFoldInv ?_ ?_
    · intro xs
      constructor
      · simp [binaryNatOfDigitsFoldInv, binaryNatOfDigitsInitAcc,
          EncodedType.inputSize, EncodedType.binaryNat]
      · simp [binaryNatOfDigitsInitAcc, binaryNatOfDigitsAccEncodedType,
          EncodedType.inputSize, EncodedType.prod, EncodedType.binaryNat]
    · intro source acc instr hInv hInstr
      exact binaryNatOfDigitsStep_growth source acc instr hInv hInstr
  simpa [binaryNatOfDigitsFold] using hFold

theorem binaryNatOfDigitsFromInstructions_tm_polytime :
    TMPolyTimeMap
      binaryNatOfDigitsInstructionListEncodedType
      EncodedType.binaryNat
      binaryNatOfDigitsFromInstructions := by
  have hComp := TMPolyTimeMap.comp binaryNatOfDigitsAccTotal_tm_polytime
    binaryNatOfDigitsFold_tm_polytime
  simpa [Function.comp, binaryNatOfDigitsFromInstructions] using hComp

theorem binaryNatOfDigitsExecutable_tm_polytime :
    TMPolyTimeMap
      binaryNatOfDigitsInputEncodedType
      EncodedType.binaryNat
      binaryNatOfDigitsExecutable := by
  have hComp := TMPolyTimeMap.comp binaryNatOfDigitsFromInstructions_tm_polytime
    binaryNatOfDigitsInstructions_tm_polytime
  simpa [Function.comp, binaryNatOfDigitsExecutable] using hComp

theorem binaryNatOfDigits_tm_polytime :
    TMPolyTimeMap
      binaryNatOfDigitsInputEncodedType
      EncodedType.binaryNat
      binaryNatOfDigits := by
  convert binaryNatOfDigitsExecutable_tm_polytime using 1
  funext p
  exact (binaryNatOfDigitsExecutable_eq_ofDigits p).symm

end Knapsack
end Karp21
end ComplexityReduction
