import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinarySubMachine
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryCompareTM

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

open Turing.TM2.Stmt
open TM2Programs

def binaryNatSubTrimBits (left right : List Bool) : List Bool :=
  binaryTrimRev (binaryNatSubRaw left right).2.reverse

def binaryNatSubTrimNat (p : Nat × Nat) : Nat :=
  boolBitsValue
    (binaryNatSubTrimBits
      (EncodedType.binaryNat.encode p.1)
      (EncodedType.binaryNat.encode p.2))

theorem binaryNatSubTrimBits_canonical (left right : List Bool) :
    boolBitsCanonical (binaryNatSubTrimBits left right) :=
  binaryTrimRev_canonical (binaryNatSubRaw left right).2.reverse

theorem binaryNatSubTrimBits_encode_eq (left right : List Bool) :
    EncodedType.binaryNat.encode (boolBitsValue (binaryNatSubTrimBits left right)) =
      binaryNatSubTrimBits left right :=
  binaryNat_encode_eq_of_canonical
    (binaryNatSubTrimBits left right)
    (binaryNatSubTrimBits_canonical left right)

theorem binaryNatSubRaw_no_borrow_of_le
    {left right : List Bool} (hLe : boolBitsValue right ≤ boolBitsValue left) :
    (binaryNatSubRaw left right).1 = false := by
  cases hBorrow : (binaryNatSubRaw left right).1
  · rfl
  · exact False.elim ((not_lt_of_ge hLe) (binaryNatSubRaw_borrow_lt hBorrow))

theorem binaryNatSubTrimBits_value_of_le
    {left right : List Bool} (hLe : boolBitsValue right ≤ boolBitsValue left) :
    boolBitsValue (binaryNatSubTrimBits left right) =
      boolBitsValue left - boolBitsValue right := by
  have hBorrow := binaryNatSubRaw_no_borrow_of_le (left := left) (right := right) hLe
  rw [binaryNatSubTrimBits, binaryTrimRev_value, List.reverse_reverse]
  exact binaryNatSubRaw_no_borrow_value hBorrow

theorem binaryNatSubTrimNat_eq_sub_of_le {m n : Nat} (hLe : n ≤ m) :
    binaryNatSubTrimNat (m, n) = m - n := by
  unfold binaryNatSubTrimNat
  rw [binaryNatSubTrimBits_value_of_le]
  · rw [boolBitsValue_binaryNat_encode, boolBitsValue_binaryNat_encode]
  · rw [boolBitsValue_binaryNat_encode, boolBitsValue_binaryNat_encode]
    exact hLe

def binarySub_finishLeft_run
    (carry : Bool) (var : BinarySubVar) (left output leftRev rawRev : List Bool) :
    StateTransition.EvalsToInTime binarySubMachine.step
      (binarySubCfg (some (BinarySubLabel.finishLeft carry)) var
        [] output leftRev left rawRev)
      (some
        (binarySubCfg (some BinarySubLabel.trim) BinarySubVar.unit
          [] output leftRev [] ((binaryNatSubRawAux left [] carry).2.reverse ++ rawRev)))
      (2 * left.length + 2) := by
  induction left generalizing carry var rawRev with
  | nil =>
      cases carry
      · let c₀ := binarySubCfg (some (BinarySubLabel.finishLeft false)) var
          [] output leftRev [] rawRev
        let c₁ := binarySubCfg (some (BinarySubLabel.finishCarry false))
          (BinarySubVar.bit none) [] output leftRev [] rawRev
        let c₂ := binarySubCfg (some BinarySubLabel.trim) BinarySubVar.unit
          [] output leftRev [] rawRev
        have h₁ : StateTransition.EvalsToInTime binarySubMachine.step c₀ (some c₁) 1 :=
          evalsToInTimeOne (binarySub_finishLeft_empty_step false var output leftRev rawRev)
        have h₂ : StateTransition.EvalsToInTime binarySubMachine.step c₁ (some c₂) 1 :=
          evalsToInTimeOne
            (binarySub_finishCarry_false_step (BinarySubVar.bit none) output leftRev rawRev)
        have hAll :=
          StateTransition.EvalsToInTime.trans binarySubMachine.step 1 1 c₀ c₁
            (some c₂) h₁ h₂
        simpa [c₀, c₁, c₂, binaryNatSubRawAux] using hAll
      · let c₀ := binarySubCfg (some (BinarySubLabel.finishLeft true)) var
          [] output leftRev [] rawRev
        let c₁ := binarySubCfg (some (BinarySubLabel.finishCarry true))
          (BinarySubVar.bit none) [] output leftRev [] rawRev
        let c₂ := binarySubCfg (some BinarySubLabel.trim) BinarySubVar.unit
          [] output leftRev [] rawRev
        have h₁ : StateTransition.EvalsToInTime binarySubMachine.step c₀ (some c₁) 1 :=
          evalsToInTimeOne (binarySub_finishLeft_empty_step true var output leftRev rawRev)
        have h₂ : StateTransition.EvalsToInTime binarySubMachine.step c₁ (some c₂) 1 :=
          evalsToInTimeOne
            (binarySub_finishCarry_true_step (BinarySubVar.bit none) output leftRev rawRev)
        have hAll :=
          StateTransition.EvalsToInTime.trans binarySubMachine.step 1 1 c₀ c₁
            (some c₂) h₁ h₂
        simpa [c₀, c₁, c₂, binaryNatSubRawAux] using hAll
  | cons leftBit left ih =>
      let next := binaryNatSubStep carry leftBit false
      let c₀ := binarySubCfg (some (BinarySubLabel.finishLeft carry)) var
        [] output leftRev (leftBit :: left) rawRev
      let c₁ := binarySubCfg (some (BinarySubLabel.pushRawFinishLeft next.2 next.1))
        (BinarySubVar.bit (some leftBit)) [] output leftRev left rawRev
      let c₂ := binarySubCfg (some (BinarySubLabel.finishLeft next.2))
        (BinarySubVar.bit (some leftBit)) [] output leftRev left (next.1 :: rawRev)
      have h₁ : StateTransition.EvalsToInTime binarySubMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (binarySub_finishLeft_bit_step carry leftBit var output leftRev left rawRev)
      have h₂ : StateTransition.EvalsToInTime binarySubMachine.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (binarySub_pushRawFinishLeft_step next.2 next.1
            (BinarySubVar.bit (some leftBit)) output leftRev left rawRev)
      have h₁₂ : StateTransition.EvalsToInTime binarySubMachine.step c₀ (some c₂)
          (1 + 1) :=
        StateTransition.EvalsToInTime.trans binarySubMachine.step 1 1 c₀ c₁
          (some c₂) h₁ h₂
      have hTail := ih next.2 (BinarySubVar.bit (some leftBit)) (next.1 :: rawRev)
      simpa [c₀, c₁, c₂, next, binaryNatSubRawAux, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans binarySubMachine.step (1 + 1)
          (2 * left.length + 2) c₀ c₂
          (some
            (binarySubCfg (some BinarySubLabel.trim) BinarySubVar.unit []
              output leftRev []
              ((binaryNatSubRawAux left [] next.2).2.reverse ++ next.1 :: rawRev)))
          h₁₂ hTail

def binarySub_readRight_run
    (carry : Bool) (var : BinarySubVar) (left right output leftRev rawRev : List Bool) :
    StateTransition.EvalsToInTime binarySubMachine.step
      (binarySubCfg (some (BinarySubLabel.readRight carry)) var
        (right.map binarySubRightSymbol) output leftRev left rawRev)
      (some
        (binarySubCfg (some BinarySubLabel.trim) BinarySubVar.unit
          [] output leftRev [] ((binaryNatSubRawAux left right carry).2.reverse ++ rawRev)))
      (3 * right.length + 2 * left.length + 4) := by
  induction right generalizing carry var left rawRev with
  | nil =>
      let c₀ := binarySubCfg (some (BinarySubLabel.readRight carry)) var
        [] output leftRev left rawRev
      let c₁ := binarySubCfg (some (BinarySubLabel.finishLeft carry))
        (BinarySubVar.input none) [] output leftRev left rawRev
      have h₁ : StateTransition.EvalsToInTime binarySubMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne (binarySub_readRight_empty_step carry var output leftRev left rawRev)
      have hTail :=
        binarySub_finishLeft_run carry (BinarySubVar.input none) left output leftRev rawRev
      have hAll :=
        StateTransition.EvalsToInTime.trans binarySubMachine.step 1
          (2 * left.length + 2) c₀ c₁
          (some
            (binarySubCfg (some BinarySubLabel.trim) BinarySubVar.unit
              [] output leftRev [] ((binaryNatSubRawAux left [] carry).2.reverse ++ rawRev)))
          h₁ hTail
      refine evalsToInTime_mono (by
        simpa [c₀, c₁, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAll) ?_
      omega
  | cons rightBit right ih =>
      cases left with
      | nil =>
          let next := binaryNatSubStep carry false rightBit
          let c₀ := binarySubCfg (some (BinarySubLabel.readRight carry)) var
            (binarySubRightSymbol rightBit :: right.map binarySubRightSymbol)
            output leftRev [] rawRev
          let c₁ := binarySubCfg (some (BinarySubLabel.popLeftForRight carry rightBit))
            (BinarySubVar.input (some (binarySubRightSymbol rightBit)))
            (right.map binarySubRightSymbol) output leftRev [] rawRev
          let c₂ := binarySubCfg (some (BinarySubLabel.pushRawReadRight next.2 next.1))
            (BinarySubVar.bit none) (right.map binarySubRightSymbol)
            output leftRev [] rawRev
          let c₃ := binarySubCfg (some (BinarySubLabel.readRight next.2))
            (BinarySubVar.bit none) (right.map binarySubRightSymbol)
            output leftRev [] (next.1 :: rawRev)
          have h₁ : StateTransition.EvalsToInTime binarySubMachine.step c₀ (some c₁) 1 :=
            evalsToInTimeOne
              (binarySub_readRight_bit_step carry rightBit var
                (right.map binarySubRightSymbol) output leftRev [] rawRev)
          have h₂ : StateTransition.EvalsToInTime binarySubMachine.step c₁ (some c₂) 1 :=
            evalsToInTimeOne
              (binarySub_popLeftForRight_empty_step carry rightBit
                (BinarySubVar.input (some (binarySubRightSymbol rightBit)))
                (right.map binarySubRightSymbol) output leftRev rawRev)
          have h₃ : StateTransition.EvalsToInTime binarySubMachine.step c₂ (some c₃) 1 :=
            evalsToInTimeOne
              (binarySub_pushRawReadRight_step next.2 next.1 (BinarySubVar.bit none)
                (right.map binarySubRightSymbol) output leftRev [] rawRev)
          have h₁₂ : StateTransition.EvalsToInTime binarySubMachine.step c₀ (some c₂)
              (1 + 1) :=
            StateTransition.EvalsToInTime.trans binarySubMachine.step 1 1 c₀ c₁
              (some c₂) h₁ h₂
          have h₁₂₃ : StateTransition.EvalsToInTime binarySubMachine.step c₀ (some c₃)
              ((1 + 1) + 1) :=
            StateTransition.EvalsToInTime.trans binarySubMachine.step (1 + 1) 1
              c₀ c₂ (some c₃) h₁₂ h₃
          have hTail := ih next.2 (BinarySubVar.bit none) [] (next.1 :: rawRev)
          simpa [c₀, c₁, c₂, c₃, next, List.map_cons, binaryNatSubRawAux,
            List.reverse_cons, List.append_assoc, Nat.mul_add,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            StateTransition.EvalsToInTime.trans binarySubMachine.step ((1 + 1) + 1)
              (3 * right.length + 2 * 0 + 4) c₀ c₃
              (some
                (binarySubCfg (some BinarySubLabel.trim) BinarySubVar.unit []
                  output leftRev []
                  ((binaryNatSubRawAux [] right next.2).2.reverse ++ next.1 :: rawRev)))
              h₁₂₃ hTail
      | cons leftBit left =>
          let next := binaryNatSubStep carry leftBit rightBit
          let c₀ := binarySubCfg (some (BinarySubLabel.readRight carry)) var
            (binarySubRightSymbol rightBit :: right.map binarySubRightSymbol)
            output leftRev (leftBit :: left) rawRev
          let c₁ := binarySubCfg (some (BinarySubLabel.popLeftForRight carry rightBit))
            (BinarySubVar.input (some (binarySubRightSymbol rightBit)))
            (right.map binarySubRightSymbol) output leftRev (leftBit :: left) rawRev
          let c₂ := binarySubCfg (some (BinarySubLabel.pushRawReadRight next.2 next.1))
            (BinarySubVar.bit (some leftBit)) (right.map binarySubRightSymbol)
            output leftRev left rawRev
          let c₃ := binarySubCfg (some (BinarySubLabel.readRight next.2))
            (BinarySubVar.bit (some leftBit)) (right.map binarySubRightSymbol)
            output leftRev left (next.1 :: rawRev)
          have h₁ : StateTransition.EvalsToInTime binarySubMachine.step c₀ (some c₁) 1 :=
            evalsToInTimeOne
              (binarySub_readRight_bit_step carry rightBit var
                (right.map binarySubRightSymbol) output leftRev (leftBit :: left) rawRev)
          have h₂ : StateTransition.EvalsToInTime binarySubMachine.step c₁ (some c₂) 1 :=
            evalsToInTimeOne
              (binarySub_popLeftForRight_bit_step carry rightBit leftBit
                (BinarySubVar.input (some (binarySubRightSymbol rightBit)))
                (right.map binarySubRightSymbol) output leftRev left rawRev)
          have h₃ : StateTransition.EvalsToInTime binarySubMachine.step c₂ (some c₃) 1 :=
            evalsToInTimeOne
              (binarySub_pushRawReadRight_step next.2 next.1
                (BinarySubVar.bit (some leftBit)) (right.map binarySubRightSymbol)
                output leftRev left rawRev)
          have h₁₂ : StateTransition.EvalsToInTime binarySubMachine.step c₀ (some c₂)
              (1 + 1) :=
            StateTransition.EvalsToInTime.trans binarySubMachine.step 1 1 c₀ c₁
              (some c₂) h₁ h₂
          have h₁₂₃ : StateTransition.EvalsToInTime binarySubMachine.step c₀ (some c₃)
              ((1 + 1) + 1) :=
            StateTransition.EvalsToInTime.trans binarySubMachine.step (1 + 1) 1
              c₀ c₂ (some c₃) h₁₂ h₃
          have hTail := ih next.2 (BinarySubVar.bit (some leftBit)) left
            (next.1 :: rawRev)
          have hAll :=
            StateTransition.EvalsToInTime.trans binarySubMachine.step ((1 + 1) + 1)
              (3 * right.length + 2 * left.length + 4) c₀ c₃
              (some
                (binarySubCfg (some BinarySubLabel.trim) BinarySubVar.unit []
                  output leftRev []
                  ((binaryNatSubRawAux left right next.2).2.reverse ++ next.1 :: rawRev)))
              h₁₂₃ hTail
          refine evalsToInTime_mono (by
            simpa [c₀, c₁, c₂, c₃, next, List.map_cons, binaryNatSubRawAux,
              List.reverse_cons, List.append_assoc, Nat.mul_add,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAll) ?_
          simp
          omega

theorem binaryNatSubRawAux_length_le :
    ∀ (left right : List Bool) (carry : Bool),
      (binaryNatSubRawAux left right carry).2.length ≤ left.length + right.length + 1
  | left, right, carry => by
      rw [binaryNatSubRawAux_length]
      omega

theorem binaryNatSubRaw_length_le (left right : List Bool) :
    (binaryNatSubRaw left right).2.length ≤ left.length + right.length + 1 := by
  simpa [binaryNatSubRaw] using binaryNatSubRawAux_length_le left right false

noncomputable def binaryNatSubMachine_outputs (left right : List Bool) :
    Turing.TM2OutputsInTime binarySubMachine
      (left.map binarySubLeftSymbol ++ none :: right.map binarySubRightSymbol)
      (some (binaryNatSubTrimBits left right))
      ((20 * Polynomial.X + 20).eval
        (left.map binarySubLeftSymbol ++ none :: right.map binarySubRightSymbol).length) := by
  let input := left.map binarySubLeftSymbol ++ none :: right.map binarySubRightSymbol
  let rawRev := (binaryNatSubRaw left right).2.reverse
  let cMove := binarySubCfg (some BinarySubLabel.moveLeft)
    (BinarySubVar.input (some none)) (right.map binarySubRightSymbol) []
    left.reverse [] []
  let cReadRight := binarySubCfg (some (BinarySubLabel.readRight false))
    (BinarySubVar.bit none) (right.map binarySubRightSymbol) [] [] left []
  let cTrim := binarySubCfg (some BinarySubLabel.trim) BinarySubVar.unit
    [] [] [] [] rawRev
  let cHalt := binarySubCfg none BinarySubVar.unit [] (binaryNatSubTrimBits left right) [] [] []
  have hRead : StateTransition.EvalsToInTime binarySubMachine.step
      (Turing.initList binarySubMachine input) (some cMove) (2 * left.length + 1) := by
    rw [binarySub_initList]
    simpa [input, cMove] using
      binarySub_readLeft_run BinarySubVar.unit left
        (right.map binarySubRightSymbol) [] [] [] []
  have hMove : StateTransition.EvalsToInTime binarySubMachine.step
      cMove (some cReadRight) (2 * left.length + 1) := by
    simpa [cMove, cReadRight, List.length_reverse] using
      binarySub_moveLeft_run (BinarySubVar.input (some none))
        (right.map binarySubRightSymbol) [] left.reverse [] []
  have hRight : StateTransition.EvalsToInTime binarySubMachine.step
      cReadRight (some cTrim) (3 * right.length + 2 * left.length + 4) := by
    simpa [cReadRight, cTrim, rawRev, binaryNatSubRaw] using
      binarySub_readRight_run false (BinarySubVar.bit none) left right [] [] []
  have hTrim : StateTransition.EvalsToInTime binarySubMachine.step
      cTrim (some cHalt) (2 * rawRev.length + 2) := by
    simpa [cTrim, cHalt, rawRev, binaryNatSubTrimBits] using
      binarySub_trim_run BinarySubVar.unit rawRev [] [] []
  have hReadMove : StateTransition.EvalsToInTime binarySubMachine.step
      (Turing.initList binarySubMachine input) (some cReadRight)
      ((2 * left.length + 1) + (2 * left.length + 1)) :=
    StateTransition.EvalsToInTime.trans binarySubMachine.step
      (2 * left.length + 1) (2 * left.length + 1)
      (Turing.initList binarySubMachine input) cMove (some cReadRight) hRead hMove
  have hToTrim : StateTransition.EvalsToInTime binarySubMachine.step
      (Turing.initList binarySubMachine input) (some cTrim)
      ((3 * right.length + 2 * left.length + 4) +
        ((2 * left.length + 1) + (2 * left.length + 1))) :=
    StateTransition.EvalsToInTime.trans binarySubMachine.step
      ((2 * left.length + 1) + (2 * left.length + 1))
      (3 * right.length + 2 * left.length + 4)
      (Turing.initList binarySubMachine input) cReadRight (some cTrim)
      hReadMove hRight
  have hAll : StateTransition.EvalsToInTime binarySubMachine.step
      (Turing.initList binarySubMachine input) (some cHalt)
      ((2 * rawRev.length + 2) +
        ((3 * right.length + 2 * left.length + 4) +
          ((2 * left.length + 1) + (2 * left.length + 1)))) :=
    StateTransition.EvalsToInTime.trans binarySubMachine.step
      ((3 * right.length + 2 * left.length + 4) +
        ((2 * left.length + 1) + (2 * left.length + 1)))
      (2 * rawRev.length + 2)
      (Turing.initList binarySubMachine input) cTrim (some cHalt)
      hToTrim hTrim
  unfold Turing.TM2OutputsInTime
  change StateTransition.EvalsToInTime binarySubMachine.step
    (Turing.initList binarySubMachine input)
    (some (Turing.haltList binarySubMachine (binaryNatSubTrimBits left right)))
    ((20 * Polynomial.X + 20).eval input.length)
  rw [binarySub_haltList]
  refine evalsToInTime_mono (by simpa [cHalt] using hAll) ?_
  have hRawLen : rawRev.length ≤ left.length + right.length + 1 := by
    simpa [rawRev] using binaryNatSubRaw_length_le left right
  simp [input, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
  omega

noncomputable def binaryNatSubTrimComputableInPolyTime :
    Turing.TM2ComputableInPolyTime
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat).encode
      EncodedType.binaryNat.encode
      binaryNatSubTrimNat where
  tm := binarySubMachine
  inputAlphabet := Equiv.refl (Option (Bool ⊕ Bool))
  outputAlphabet := Equiv.refl Bool
  time := 20 * Polynomial.X + 20
  outputsFun p := by
    rcases p with ⟨m, n⟩
    change Nat at m
    change Nat at n
    have h :=
      binaryNatSubMachine_outputs
        (EncodedType.binaryNat.encode m)
        (EncodedType.binaryNat.encode n)
    unfold Turing.TM2OutputsInTime at h ⊢
    dsimp [EncodedType.prod] at h ⊢
    have hInputList :
        ((EncodedType.binaryNat.encode m).map (fun s : Bool => some (Sum.inl s)) ++
          [none] ++
          (EncodedType.binaryNat.encode n).map (fun s : Bool => some (Sum.inr s))).map
            (Equiv.refl (Option (Bool ⊕ Bool))).symm =
        List.map binarySubLeftSymbol (EncodedType.binaryNat.encode m) ++
          none :: List.map binarySubRightSymbol (EncodedType.binaryNat.encode n) := by
      exact binarySubProductSymbolsMapped_eq
        (EncodedType.binaryNat.encode m) (EncodedType.binaryNat.encode n)
    have hRawInputList :
        (EncodedType.binaryNat.encode m).map (fun s : Bool => some (Sum.inl s)) ++
          [none] ++
          (EncodedType.binaryNat.encode n).map (fun s : Bool => some (Sum.inr s)) =
        List.map binarySubLeftSymbol (EncodedType.binaryNat.encode m) ++
          none :: List.map binarySubRightSymbol (EncodedType.binaryNat.encode n) := by
      exact binarySubProductSymbolsRaw_eq
        (EncodedType.binaryNat.encode m) (EncodedType.binaryNat.encode n)
    have hOutputList :
        List.map (Equiv.refl Bool).symm
            (EncodedType.binaryNat.encode (binaryNatSubTrimNat (m, n))) =
          binaryNatSubTrimBits (EncodedType.binaryNat.encode m)
            (EncodedType.binaryNat.encode n) := by
      rw [binaryNatSubTrimNat, binaryNatSubTrimBits_encode_eq]
      exact list_map_equivRefl_symm
        (binaryNatSubTrimBits (EncodedType.binaryNat.encode m) (EncodedType.binaryNat.encode n))
    convert h using 1
    · exact congrArg (Turing.initList binarySubMachine) hInputList
    · exact congrArg some (congrArg (Turing.haltList binarySubMachine) hOutputList)
    · exact congrArg (fun xs : List (Option (Bool ⊕ Bool)) =>
        Polynomial.eval xs.length (20 * Polynomial.X + 20)) hRawInputList

theorem binaryNatSubTrimNat_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      EncodedType.binaryNat
      binaryNatSubTrimNat :=
  ⟨binaryNatSubTrimComputableInPolyTime⟩

theorem binaryNatSub_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      EncodedType.binaryNat
      (fun p : Nat × Nat => p.1 - p.2) := by
  let X := EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat
  let N := EncodedType.binaryNat
  have hFlag : TMPolyTimeMap X EncodedType.bool binaryNatSuccLeBool := by
    simpa [X] using binaryNatSuccLeBool_tm_polytime
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : Nat × Nat => (binaryNatSuccLeBool p, p)) :=
    TMPolyTimeMap.prod_mk hFlag (TMPolyTimeMap.id X)
  have hZero : TMPolyTimeMap X N (fun _ : Nat × Nat => (0 : Nat)) :=
    TMPolyTimeMap.const X N (0 : Nat)
  have hDispatch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool X)
        N
        (fun p : Bool × (Nat × Nat) =>
          match p.1 with
          | true => (0 : Nat)
          | false => binaryNatSubTrimNat p.2) :=
    Clique.boolProduct_dispatch_tm_polytime X N
      (fFalse := binaryNatSubTrimNat)
      (fTrue := fun _ : Nat × Nat => (0 : Nat))
      binaryNatSubTrimNat_tm_polytime hZero
  have hComp := TMPolyTimeMap.comp hDispatch hBranchInput
  convert hComp using 1
  funext p
  rcases p with ⟨m, n⟩
  by_cases hlt : m < n
  · have hFlagTrue : binaryNatSuccLeBool (m, n) = true := by
      simp [binaryNatSuccLeBool, hlt]
    simp [Function.comp, hFlagTrue, Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]
  · have hLe : n ≤ m := le_of_not_gt hlt
    have hFlagFalse : binaryNatSuccLeBool (m, n) = false := by
      simp [binaryNatSuccLeBool, hlt]
    simp [Function.comp, hFlagFalse, binaryNatSubTrimNat_eq_sub_of_le hLe]

end Knapsack
end Karp21
end ComplexityReduction
