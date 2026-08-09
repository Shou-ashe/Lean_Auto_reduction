import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryAddMachine

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

open Turing.TM2.Stmt
open TM2Programs

def binaryAdd_finishLeft_run
    (carry : Bool) (var : BinaryAddVar) (left output leftRev rawRev : List Bool) :
    StateTransition.EvalsToInTime binaryAddMachine.step
      (binaryAddCfg (some (BinaryAddLabel.finishLeft carry)) var
        [] output leftRev left rawRev)
      (some
        (binaryAddCfg (some BinaryAddLabel.trim) BinaryAddVar.unit
          [] output leftRev [] ((binaryNatAddRawAux left [] carry).reverse ++ rawRev)))
      (2 * left.length + 2) := by
  induction left generalizing carry var rawRev with
  | nil =>
      cases carry
      · let c₀ := binaryAddCfg (some (BinaryAddLabel.finishLeft false)) var
          [] output leftRev [] rawRev
        let c₁ := binaryAddCfg (some (BinaryAddLabel.finishCarry false))
          (BinaryAddVar.bit none) [] output leftRev [] rawRev
        let c₂ := binaryAddCfg (some BinaryAddLabel.trim) BinaryAddVar.unit
          [] output leftRev [] rawRev
        have h₁ : StateTransition.EvalsToInTime binaryAddMachine.step c₀ (some c₁) 1 :=
          evalsToInTimeOne (binaryAdd_finishLeft_empty_step false var output leftRev rawRev)
        have h₂ : StateTransition.EvalsToInTime binaryAddMachine.step c₁ (some c₂) 1 :=
          evalsToInTimeOne
            (binaryAdd_finishCarry_false_step (BinaryAddVar.bit none) output leftRev rawRev)
        have hAll :=
          StateTransition.EvalsToInTime.trans binaryAddMachine.step 1 1 c₀ c₁
            (some c₂) h₁ h₂
        simpa [c₀, c₁, c₂, binaryNatAddRawAux] using hAll
      · let c₀ := binaryAddCfg (some (BinaryAddLabel.finishLeft true)) var
          [] output leftRev [] rawRev
        let c₁ := binaryAddCfg (some (BinaryAddLabel.finishCarry true))
          (BinaryAddVar.bit none) [] output leftRev [] rawRev
        let c₂ := binaryAddCfg (some BinaryAddLabel.trim) BinaryAddVar.unit
          [] output leftRev [] (true :: rawRev)
        have h₁ : StateTransition.EvalsToInTime binaryAddMachine.step c₀ (some c₁) 1 :=
          evalsToInTimeOne (binaryAdd_finishLeft_empty_step true var output leftRev rawRev)
        have h₂ : StateTransition.EvalsToInTime binaryAddMachine.step c₁ (some c₂) 1 :=
          evalsToInTimeOne
            (binaryAdd_finishCarry_true_step (BinaryAddVar.bit none) output leftRev rawRev)
        have hAll :=
          StateTransition.EvalsToInTime.trans binaryAddMachine.step 1 1 c₀ c₁
            (some c₂) h₁ h₂
        simpa [c₀, c₁, c₂, binaryNatAddRawAux] using hAll
  | cons leftBit left ih =>
      let next := binaryNatAddStep carry leftBit false
      let c₀ := binaryAddCfg (some (BinaryAddLabel.finishLeft carry)) var
        [] output leftRev (leftBit :: left) rawRev
      let c₁ := binaryAddCfg (some (BinaryAddLabel.pushRawFinishLeft next.2 next.1))
        (BinaryAddVar.bit (some leftBit)) [] output leftRev left rawRev
      let c₂ := binaryAddCfg (some (BinaryAddLabel.finishLeft next.2))
        (BinaryAddVar.bit (some leftBit)) [] output leftRev left (next.1 :: rawRev)
      have h₁ : StateTransition.EvalsToInTime binaryAddMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (binaryAdd_finishLeft_bit_step carry leftBit var output leftRev left rawRev)
      have h₂ : StateTransition.EvalsToInTime binaryAddMachine.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (binaryAdd_pushRawFinishLeft_step next.2 next.1
            (BinaryAddVar.bit (some leftBit)) output leftRev left rawRev)
      have h₁₂ : StateTransition.EvalsToInTime binaryAddMachine.step c₀ (some c₂)
          (1 + 1) :=
        StateTransition.EvalsToInTime.trans binaryAddMachine.step 1 1 c₀ c₁
          (some c₂) h₁ h₂
      have hTail := ih next.2 (BinaryAddVar.bit (some leftBit)) (next.1 :: rawRev)
      simpa [c₀, c₁, c₂, next, binaryNatAddRawAux, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans binaryAddMachine.step (1 + 1)
          (2 * left.length + 2) c₀ c₂
          (some
            (binaryAddCfg (some BinaryAddLabel.trim) BinaryAddVar.unit []
              output leftRev []
              ((binaryNatAddRawAux left [] next.2).reverse ++ next.1 :: rawRev)))
          h₁₂ hTail

def binaryAdd_readRight_run
    (carry : Bool) (var : BinaryAddVar) (left right output leftRev rawRev : List Bool) :
    StateTransition.EvalsToInTime binaryAddMachine.step
      (binaryAddCfg (some (BinaryAddLabel.readRight carry)) var
        (right.map binaryAddRightSymbol) output leftRev left rawRev)
      (some
        (binaryAddCfg (some BinaryAddLabel.trim) BinaryAddVar.unit
          [] output leftRev [] ((binaryNatAddRawAux left right carry).reverse ++ rawRev)))
      (3 * right.length + 2 * left.length + 4) := by
  induction right generalizing carry var left rawRev with
  | nil =>
      let c₀ := binaryAddCfg (some (BinaryAddLabel.readRight carry)) var
        [] output leftRev left rawRev
      let c₁ := binaryAddCfg (some (BinaryAddLabel.finishLeft carry))
        (BinaryAddVar.input none) [] output leftRev left rawRev
      have h₁ : StateTransition.EvalsToInTime binaryAddMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne (binaryAdd_readRight_empty_step carry var output leftRev left rawRev)
      have hTail :=
        binaryAdd_finishLeft_run carry (BinaryAddVar.input none) left output leftRev rawRev
      have hAll :=
        StateTransition.EvalsToInTime.trans binaryAddMachine.step 1
          (2 * left.length + 2) c₀ c₁
          (some
            (binaryAddCfg (some BinaryAddLabel.trim) BinaryAddVar.unit
              [] output leftRev [] ((binaryNatAddRawAux left [] carry).reverse ++ rawRev)))
          h₁ hTail
      refine evalsToInTime_mono (by
        simpa [c₀, c₁, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAll) ?_
      omega
  | cons rightBit right ih =>
      cases left with
      | nil =>
          let next := binaryNatAddStep carry false rightBit
          let c₀ := binaryAddCfg (some (BinaryAddLabel.readRight carry)) var
            (binaryAddRightSymbol rightBit :: right.map binaryAddRightSymbol)
            output leftRev [] rawRev
          let c₁ := binaryAddCfg (some (BinaryAddLabel.popLeftForRight carry rightBit))
            (BinaryAddVar.input (some (binaryAddRightSymbol rightBit)))
            (right.map binaryAddRightSymbol) output leftRev [] rawRev
          let c₂ := binaryAddCfg (some (BinaryAddLabel.pushRawReadRight next.2 next.1))
            (BinaryAddVar.bit none) (right.map binaryAddRightSymbol)
            output leftRev [] rawRev
          let c₃ := binaryAddCfg (some (BinaryAddLabel.readRight next.2))
            (BinaryAddVar.bit none) (right.map binaryAddRightSymbol)
            output leftRev [] (next.1 :: rawRev)
          have h₁ : StateTransition.EvalsToInTime binaryAddMachine.step c₀ (some c₁) 1 :=
            evalsToInTimeOne
              (binaryAdd_readRight_bit_step carry rightBit var
                (right.map binaryAddRightSymbol) output leftRev [] rawRev)
          have h₂ : StateTransition.EvalsToInTime binaryAddMachine.step c₁ (some c₂) 1 :=
            evalsToInTimeOne
              (binaryAdd_popLeftForRight_empty_step carry rightBit
                (BinaryAddVar.input (some (binaryAddRightSymbol rightBit)))
                (right.map binaryAddRightSymbol) output leftRev rawRev)
          have h₃ : StateTransition.EvalsToInTime binaryAddMachine.step c₂ (some c₃) 1 :=
            evalsToInTimeOne
              (binaryAdd_pushRawReadRight_step next.2 next.1 (BinaryAddVar.bit none)
                (right.map binaryAddRightSymbol) output leftRev [] rawRev)
          have h₁₂ : StateTransition.EvalsToInTime binaryAddMachine.step c₀ (some c₂)
              (1 + 1) :=
            StateTransition.EvalsToInTime.trans binaryAddMachine.step 1 1 c₀ c₁
              (some c₂) h₁ h₂
          have h₁₂₃ : StateTransition.EvalsToInTime binaryAddMachine.step c₀ (some c₃)
              ((1 + 1) + 1) :=
            StateTransition.EvalsToInTime.trans binaryAddMachine.step (1 + 1) 1
              c₀ c₂ (some c₃) h₁₂ h₃
          have hTail := ih next.2 (BinaryAddVar.bit none) [] (next.1 :: rawRev)
          simpa [c₀, c₁, c₂, c₃, next, List.map_cons, binaryNatAddRawAux,
            List.reverse_cons, List.append_assoc, Nat.mul_add,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            StateTransition.EvalsToInTime.trans binaryAddMachine.step ((1 + 1) + 1)
              (3 * right.length + 2 * 0 + 4) c₀ c₃
              (some
                (binaryAddCfg (some BinaryAddLabel.trim) BinaryAddVar.unit []
                  output leftRev []
                  ((binaryNatAddRawAux [] right next.2).reverse ++ next.1 :: rawRev)))
              h₁₂₃ hTail
      | cons leftBit left =>
          let next := binaryNatAddStep carry leftBit rightBit
          let c₀ := binaryAddCfg (some (BinaryAddLabel.readRight carry)) var
            (binaryAddRightSymbol rightBit :: right.map binaryAddRightSymbol)
            output leftRev (leftBit :: left) rawRev
          let c₁ := binaryAddCfg (some (BinaryAddLabel.popLeftForRight carry rightBit))
            (BinaryAddVar.input (some (binaryAddRightSymbol rightBit)))
            (right.map binaryAddRightSymbol) output leftRev (leftBit :: left) rawRev
          let c₂ := binaryAddCfg (some (BinaryAddLabel.pushRawReadRight next.2 next.1))
            (BinaryAddVar.bit (some leftBit)) (right.map binaryAddRightSymbol)
            output leftRev left rawRev
          let c₃ := binaryAddCfg (some (BinaryAddLabel.readRight next.2))
            (BinaryAddVar.bit (some leftBit)) (right.map binaryAddRightSymbol)
            output leftRev left (next.1 :: rawRev)
          have h₁ : StateTransition.EvalsToInTime binaryAddMachine.step c₀ (some c₁) 1 :=
            evalsToInTimeOne
              (binaryAdd_readRight_bit_step carry rightBit var
                (right.map binaryAddRightSymbol) output leftRev (leftBit :: left) rawRev)
          have h₂ : StateTransition.EvalsToInTime binaryAddMachine.step c₁ (some c₂) 1 :=
            evalsToInTimeOne
              (binaryAdd_popLeftForRight_bit_step carry rightBit leftBit
                (BinaryAddVar.input (some (binaryAddRightSymbol rightBit)))
                (right.map binaryAddRightSymbol) output leftRev left rawRev)
          have h₃ : StateTransition.EvalsToInTime binaryAddMachine.step c₂ (some c₃) 1 :=
            evalsToInTimeOne
              (binaryAdd_pushRawReadRight_step next.2 next.1
                (BinaryAddVar.bit (some leftBit)) (right.map binaryAddRightSymbol)
                output leftRev left rawRev)
          have h₁₂ : StateTransition.EvalsToInTime binaryAddMachine.step c₀ (some c₂)
              (1 + 1) :=
            StateTransition.EvalsToInTime.trans binaryAddMachine.step 1 1 c₀ c₁
              (some c₂) h₁ h₂
          have h₁₂₃ : StateTransition.EvalsToInTime binaryAddMachine.step c₀ (some c₃)
              ((1 + 1) + 1) :=
            StateTransition.EvalsToInTime.trans binaryAddMachine.step (1 + 1) 1
              c₀ c₂ (some c₃) h₁₂ h₃
          have hTail := ih next.2 (BinaryAddVar.bit (some leftBit)) left
            (next.1 :: rawRev)
          have hAll :=
            StateTransition.EvalsToInTime.trans binaryAddMachine.step ((1 + 1) + 1)
              (3 * right.length + 2 * left.length + 4) c₀ c₃
              (some
                (binaryAddCfg (some BinaryAddLabel.trim) BinaryAddVar.unit []
                  output leftRev []
                  ((binaryNatAddRawAux left right next.2).reverse ++ next.1 :: rawRev)))
              h₁₂₃ hTail
          refine evalsToInTime_mono (by
            simpa [c₀, c₁, c₂, c₃, next, List.map_cons, binaryNatAddRawAux,
              List.reverse_cons, List.append_assoc, Nat.mul_add,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAll) ?_
          simp
          omega

theorem binaryNatAddRawAux_length_le :
    ∀ (left right : List Bool) (carry : Bool),
      (binaryNatAddRawAux left right carry).length ≤ left.length + right.length + 1
  | [], [], carry => by
      cases carry <;> simp [binaryNatAddRawAux]
  | leftBit :: left, [], carry => by
      rw [binaryNatAddRawAux]
      set next := binaryNatAddStep carry leftBit false
      have hTail := binaryNatAddRawAux_length_le left [] next.2
      simp [next] at hTail ⊢
      omega
  | [], rightBit :: right, carry => by
      rw [binaryNatAddRawAux]
      set next := binaryNatAddStep carry false rightBit
      have hTail := binaryNatAddRawAux_length_le [] right next.2
      simp [next] at hTail ⊢
      omega
  | leftBit :: left, rightBit :: right, carry => by
      rw [binaryNatAddRawAux]
      set next := binaryNatAddStep carry leftBit rightBit
      have hTail := binaryNatAddRawAux_length_le left right next.2
      simp [next] at hTail ⊢
      omega

theorem binaryNatAddRaw_length_le (left right : List Bool) :
    (binaryNatAddRaw left right).length ≤ left.length + right.length + 1 := by
  simpa [binaryNatAddRaw] using binaryNatAddRawAux_length_le left right false

noncomputable def binaryNatAddMachine_outputs (left right : List Bool) :
    Turing.TM2OutputsInTime binaryAddMachine
      (left.map binaryAddLeftSymbol ++ none :: right.map binaryAddRightSymbol)
      (some (binaryNatAddBits left right))
      ((20 * Polynomial.X + 20).eval
        (left.map binaryAddLeftSymbol ++ none :: right.map binaryAddRightSymbol).length) := by
  let input := left.map binaryAddLeftSymbol ++ none :: right.map binaryAddRightSymbol
  let rawRev := (binaryNatAddRaw left right).reverse
  let cMove := binaryAddCfg (some BinaryAddLabel.moveLeft)
    (BinaryAddVar.input (some none)) (right.map binaryAddRightSymbol) []
    left.reverse [] []
  let cReadRight := binaryAddCfg (some (BinaryAddLabel.readRight false))
    (BinaryAddVar.bit none) (right.map binaryAddRightSymbol) [] [] left []
  let cTrim := binaryAddCfg (some BinaryAddLabel.trim) BinaryAddVar.unit
    [] [] [] [] rawRev
  let cHalt := binaryAddCfg none BinaryAddVar.unit [] (binaryNatAddBits left right) [] [] []
  have hRead : StateTransition.EvalsToInTime binaryAddMachine.step
      (Turing.initList binaryAddMachine input) (some cMove) (2 * left.length + 1) := by
    rw [binaryAdd_initList]
    simpa [input, cMove] using
      binaryAdd_readLeft_run BinaryAddVar.unit left
        (right.map binaryAddRightSymbol) [] [] [] []
  have hMove : StateTransition.EvalsToInTime binaryAddMachine.step
      cMove (some cReadRight) (2 * left.length + 1) := by
    simpa [cMove, cReadRight, List.length_reverse] using
      binaryAdd_moveLeft_run (BinaryAddVar.input (some none))
        (right.map binaryAddRightSymbol) [] left.reverse [] []
  have hRight : StateTransition.EvalsToInTime binaryAddMachine.step
      cReadRight (some cTrim) (3 * right.length + 2 * left.length + 4) := by
    simpa [cReadRight, cTrim, rawRev, binaryNatAddRaw] using
      binaryAdd_readRight_run false (BinaryAddVar.bit none) left right [] [] []
  have hTrim : StateTransition.EvalsToInTime binaryAddMachine.step
      cTrim (some cHalt) (2 * rawRev.length + 2) := by
    simpa [cTrim, cHalt, rawRev, binaryNatAddBits] using
      binaryAdd_trim_run BinaryAddVar.unit rawRev [] [] []
  have hReadMove : StateTransition.EvalsToInTime binaryAddMachine.step
      (Turing.initList binaryAddMachine input) (some cReadRight)
      ((2 * left.length + 1) + (2 * left.length + 1)) :=
    StateTransition.EvalsToInTime.trans binaryAddMachine.step
      (2 * left.length + 1) (2 * left.length + 1)
      (Turing.initList binaryAddMachine input) cMove (some cReadRight) hRead hMove
  have hToTrim : StateTransition.EvalsToInTime binaryAddMachine.step
      (Turing.initList binaryAddMachine input) (some cTrim)
      ((3 * right.length + 2 * left.length + 4) +
        ((2 * left.length + 1) + (2 * left.length + 1))) :=
    StateTransition.EvalsToInTime.trans binaryAddMachine.step
      ((2 * left.length + 1) + (2 * left.length + 1))
      (3 * right.length + 2 * left.length + 4)
      (Turing.initList binaryAddMachine input) cReadRight (some cTrim)
      hReadMove hRight
  have hAll : StateTransition.EvalsToInTime binaryAddMachine.step
      (Turing.initList binaryAddMachine input) (some cHalt)
      ((2 * rawRev.length + 2) +
        ((3 * right.length + 2 * left.length + 4) +
          ((2 * left.length + 1) + (2 * left.length + 1)))) :=
    StateTransition.EvalsToInTime.trans binaryAddMachine.step
      ((3 * right.length + 2 * left.length + 4) +
        ((2 * left.length + 1) + (2 * left.length + 1)))
      (2 * rawRev.length + 2)
      (Turing.initList binaryAddMachine input) cTrim (some cHalt)
      hToTrim hTrim
  unfold Turing.TM2OutputsInTime
  change StateTransition.EvalsToInTime binaryAddMachine.step
    (Turing.initList binaryAddMachine input)
    (some (Turing.haltList binaryAddMachine (binaryNatAddBits left right)))
    ((20 * Polynomial.X + 20).eval input.length)
  rw [binaryAdd_haltList]
  refine evalsToInTime_mono (by simpa [cHalt] using hAll) ?_
  have hRawLen : rawRev.length ≤ left.length + right.length + 1 := by
    simpa [rawRev] using binaryNatAddRaw_length_le left right
  simp [input, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
  omega

noncomputable def binaryNatAddComputableInPolyTime :
    Turing.TM2ComputableInPolyTime
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat).encode
      EncodedType.binaryNat.encode
      (fun p : Nat × Nat => p.1 + p.2) where
  tm := binaryAddMachine
  inputAlphabet := Equiv.refl (Option (Bool ⊕ Bool))
  outputAlphabet := Equiv.refl Bool
  time := 20 * Polynomial.X + 20
  outputsFun p := by
    rcases p with ⟨m, n⟩
    change Nat at m
    change Nat at n
    have h :=
      binaryNatAddMachine_outputs
        (EncodedType.binaryNat.encode m)
        (EncodedType.binaryNat.encode n)
    unfold Turing.TM2OutputsInTime at h ⊢
    dsimp [EncodedType.prod] at h ⊢
    have hInputList :
        ((EncodedType.binaryNat.encode m).map (fun s : Bool => some (Sum.inl s)) ++
          [none] ++
          (EncodedType.binaryNat.encode n).map (fun s : Bool => some (Sum.inr s))).map
            (Equiv.refl (Option (Bool ⊕ Bool))).symm =
        List.map binaryAddLeftSymbol (EncodedType.binaryNat.encode m) ++
          none :: List.map binaryAddRightSymbol (EncodedType.binaryNat.encode n) := by
      exact binaryAddProductSymbolsMapped_eq
        (EncodedType.binaryNat.encode m) (EncodedType.binaryNat.encode n)
    have hRawInputList :
        (EncodedType.binaryNat.encode m).map (fun s : Bool => some (Sum.inl s)) ++
          [none] ++
          (EncodedType.binaryNat.encode n).map (fun s : Bool => some (Sum.inr s)) =
        List.map binaryAddLeftSymbol (EncodedType.binaryNat.encode m) ++
          none :: List.map binaryAddRightSymbol (EncodedType.binaryNat.encode n) := by
      exact binaryAddProductSymbolsRaw_eq
        (EncodedType.binaryNat.encode m) (EncodedType.binaryNat.encode n)
    have hOutputList :
        List.map (Equiv.refl Bool).symm (EncodedType.binaryNat.encode (m + n)) =
          binaryNatAddBits (EncodedType.binaryNat.encode m)
            (EncodedType.binaryNat.encode n) := by
      rw [← binaryNatAddBits_encode_eq (m, n)]
      exact list_map_equivRefl_symm
        (binaryNatAddBits (EncodedType.binaryNat.encode m) (EncodedType.binaryNat.encode n))
    convert h using 1
    · exact congrArg (Turing.initList binaryAddMachine) hInputList
    · exact congrArg some (congrArg (Turing.haltList binaryAddMachine) hOutputList)
    · exact congrArg (fun xs : List (Option (Bool ⊕ Bool)) =>
        Polynomial.eval xs.length (20 * Polynomial.X + 20)) hRawInputList

theorem binaryNatAdd_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      EncodedType.binaryNat
      (fun p : Nat × Nat => p.1 + p.2) :=
  ⟨binaryNatAddComputableInPolyTime⟩

end Knapsack
end Karp21
end ComplexityReduction
