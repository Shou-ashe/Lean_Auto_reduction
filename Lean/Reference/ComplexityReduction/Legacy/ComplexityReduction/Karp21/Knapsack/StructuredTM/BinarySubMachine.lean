import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinarySub

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

open Turing.TM2.Stmt
open TM2Programs

@[simp] theorem equivRefl_symm_apply {α : Type} (x : α) :
    (Equiv.refl α).symm x = x := rfl

@[simp] theorem equivRefl_symm_comp {α β : Type} (f : α → β) :
    ((Equiv.refl β).symm ∘ f) = f := by
  funext x
  simp

@[simp] theorem list_map_equivRefl_symm {α : Type} (xs : List α) :
    xs.map (Equiv.refl α).symm = xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      change (Equiv.refl α).symm x :: xs.map (Equiv.refl α).symm = x :: xs
      rw [ih]
      rfl

/-!
Direct TM witness for binary natural subtraction raw bit scan.

The machine subtracts the two product payloads bit-by-bit, stores the raw result in
reverse order, then drops high zeroes while draining the stack to the public
output.  Pure bit-level correctness is imported from `BinarySub`.
-/

inductive BinarySubStack where
  | input
  | output
  | leftRev
  | leftWork
  | rawRev
  deriving DecidableEq, Fintype

abbrev binarySubAlphabet : BinarySubStack → Type
  | BinarySubStack.input => Option (Bool ⊕ Bool)
  | BinarySubStack.output => Bool
  | BinarySubStack.leftRev => Bool
  | BinarySubStack.leftWork => Bool
  | BinarySubStack.rawRev => Bool

inductive BinarySubVar where
  | unit
  | input (head : Option (Option (Bool ⊕ Bool)))
  | bit (head : Option Bool)
  deriving DecidableEq, Fintype

inductive BinarySubLabel where
  | readLeft
  | pushLeftRev (bit : Bool)
  | moveLeft
  | pushLeftWork (bit : Bool)
  | readRight (carry : Bool)
  | popLeftForRight (carry rightBit : Bool)
  | pushRawReadRight (carry bit : Bool)
  | finishLeft (carry : Bool)
  | pushRawFinishLeft (carry bit : Bool)
  | finishCarry (carry : Bool)
  | trim
  | drain
  | pushOutput (bit : Bool)
  | done
  deriving DecidableEq, Fintype

def binarySubLeftSymbol (b : Bool) : Option (Bool ⊕ Bool) :=
  some (Sum.inl b)

def binarySubRightSymbol (b : Bool) : Option (Bool ⊕ Bool) :=
  some (Sum.inr b)

theorem binarySubLeftSymbols_raw_eq (left : List Bool) :
    left.map (fun s : Bool => some (Sum.inl s)) =
      left.map binarySubLeftSymbol := by
  induction left with
  | nil => rfl
  | cons bit bits ih =>
      change some (Sum.inl bit) :: bits.map (fun s : Bool => some (Sum.inl s)) =
        binarySubLeftSymbol bit :: bits.map binarySubLeftSymbol
      rw [ih]
      rfl

theorem binarySubRightSymbols_raw_eq (right : List Bool) :
    right.map (fun s : Bool => some (Sum.inr s)) =
      right.map binarySubRightSymbol := by
  induction right with
  | nil => rfl
  | cons bit bits ih =>
      change some (Sum.inr bit) :: bits.map (fun s : Bool => some (Sum.inr s)) =
        binarySubRightSymbol bit :: bits.map binarySubRightSymbol
      rw [ih]
      rfl

theorem binarySubProductSymbolsRaw_eq (left right : List Bool) :
    left.map (fun s : Bool => some (Sum.inl s)) ++ [none] ++
        right.map (fun s : Bool => some (Sum.inr s)) =
      left.map binarySubLeftSymbol ++ none :: right.map binarySubRightSymbol := by
  rw [binarySubLeftSymbols_raw_eq, binarySubRightSymbols_raw_eq]
  simp

theorem binarySubLeftSymbols_mapped_eq (left : List Bool) :
    (left.map (fun s : Bool => some (Sum.inl s))).map
        (Equiv.refl (Option (Bool ⊕ Bool))).symm =
      left.map binarySubLeftSymbol := by
  rw [list_map_equivRefl_symm, binarySubLeftSymbols_raw_eq]

theorem binarySubRightSymbols_mapped_eq (right : List Bool) :
    (right.map (fun s : Bool => some (Sum.inr s))).map
        (Equiv.refl (Option (Bool ⊕ Bool))).symm =
      right.map binarySubRightSymbol := by
  rw [list_map_equivRefl_symm, binarySubRightSymbols_raw_eq]

theorem binarySubProductSymbolsMapped_eq (left right : List Bool) :
    (left.map (fun s : Bool => some (Sum.inl s)) ++ [none] ++
        right.map (fun s : Bool => some (Sum.inr s))).map
        (Equiv.refl (Option (Bool ⊕ Bool))).symm =
      left.map binarySubLeftSymbol ++ none :: right.map binarySubRightSymbol := by
  rw [List.map_append, List.map_append, binarySubLeftSymbols_mapped_eq,
    binarySubRightSymbols_mapped_eq]
  simp

def binarySubAfterReadLeft : BinarySubVar → BinarySubLabel
  | BinarySubVar.input (some (some (Sum.inl bit))) => BinarySubLabel.pushLeftRev bit
  | BinarySubVar.input (some none) => BinarySubLabel.moveLeft
  | BinarySubVar.input none => BinarySubLabel.moveLeft
  | _ => BinarySubLabel.moveLeft

def binarySubAfterMoveLeft : BinarySubVar → BinarySubLabel
  | BinarySubVar.bit (some bit) => BinarySubLabel.pushLeftWork bit
  | BinarySubVar.bit none => BinarySubLabel.readRight false
  | _ => BinarySubLabel.readRight false

def binarySubAfterReadRight (carry : Bool) : BinarySubVar → BinarySubLabel
  | BinarySubVar.input (some (some (Sum.inr bit))) =>
      BinarySubLabel.popLeftForRight carry bit
  | _ => BinarySubLabel.finishLeft carry

def binarySubAfterPopLeftForRight (carry rightBit : Bool) :
    BinarySubVar → BinarySubLabel
  | BinarySubVar.bit (some leftBit) =>
      let next := binaryNatSubStep carry leftBit rightBit
      BinarySubLabel.pushRawReadRight next.2 next.1
  | BinarySubVar.bit none =>
      let next := binaryNatSubStep carry false rightBit
      BinarySubLabel.pushRawReadRight next.2 next.1
  | _ =>
      let next := binaryNatSubStep carry false rightBit
      BinarySubLabel.pushRawReadRight next.2 next.1

def binarySubAfterFinishLeft (carry : Bool) : BinarySubVar → BinarySubLabel
  | BinarySubVar.bit (some leftBit) =>
      let next := binaryNatSubStep carry leftBit false
      BinarySubLabel.pushRawFinishLeft next.2 next.1
  | BinarySubVar.bit none => BinarySubLabel.finishCarry carry
  | _ => BinarySubLabel.finishCarry carry

def binarySubAfterTrim : BinarySubVar → BinarySubLabel
  | BinarySubVar.bit (some false) => BinarySubLabel.trim
  | BinarySubVar.bit (some true) => BinarySubLabel.pushOutput true
  | _ => BinarySubLabel.done

def binarySubAfterDrain : BinarySubVar → BinarySubLabel
  | BinarySubVar.bit (some bit) => BinarySubLabel.pushOutput bit
  | _ => BinarySubLabel.done

def binarySubMachine : Turing.FinTM2 where
  K := BinarySubStack
  k₀ := BinarySubStack.input
  k₁ := BinarySubStack.output
  Γ := binarySubAlphabet
  Λ := BinarySubLabel
  main := BinarySubLabel.readLeft
  σ := BinarySubVar
  initialState := BinarySubVar.unit
  Γk₀Fin := by
    dsimp [binarySubAlphabet]
    infer_instance
  m
    | BinarySubLabel.readLeft =>
        pop BinarySubStack.input (fun _ head => BinarySubVar.input head)
          (goto binarySubAfterReadLeft)
    | BinarySubLabel.pushLeftRev bit =>
        push BinarySubStack.leftRev (fun _ => bit)
          (goto fun _ => BinarySubLabel.readLeft)
    | BinarySubLabel.moveLeft =>
        pop BinarySubStack.leftRev (fun _ head => BinarySubVar.bit head)
          (goto binarySubAfterMoveLeft)
    | BinarySubLabel.pushLeftWork bit =>
        push BinarySubStack.leftWork (fun _ => bit)
          (goto fun _ => BinarySubLabel.moveLeft)
    | BinarySubLabel.readRight carry =>
        pop BinarySubStack.input (fun _ head => BinarySubVar.input head)
          (goto (binarySubAfterReadRight carry))
    | BinarySubLabel.popLeftForRight carry rightBit =>
        pop BinarySubStack.leftWork (fun _ head => BinarySubVar.bit head)
          (goto (binarySubAfterPopLeftForRight carry rightBit))
    | BinarySubLabel.pushRawReadRight carry bit =>
        push BinarySubStack.rawRev (fun _ => bit)
          (goto fun _ => BinarySubLabel.readRight carry)
    | BinarySubLabel.finishLeft carry =>
        pop BinarySubStack.leftWork (fun _ head => BinarySubVar.bit head)
          (goto (binarySubAfterFinishLeft carry))
    | BinarySubLabel.pushRawFinishLeft carry bit =>
        push BinarySubStack.rawRev (fun _ => bit)
          (goto fun _ => BinarySubLabel.finishLeft carry)
    | BinarySubLabel.finishCarry carry =>
        load (fun _ => BinarySubVar.unit) (goto fun _ => BinarySubLabel.trim)
    | BinarySubLabel.trim =>
        pop BinarySubStack.rawRev (fun _ head => BinarySubVar.bit head)
          (goto binarySubAfterTrim)
    | BinarySubLabel.drain =>
        pop BinarySubStack.rawRev (fun _ head => BinarySubVar.bit head)
          (goto binarySubAfterDrain)
    | BinarySubLabel.pushOutput bit =>
        push BinarySubStack.output (fun _ => bit)
          (goto fun _ => BinarySubLabel.drain)
    | BinarySubLabel.done =>
        load (fun _ => BinarySubVar.unit) halt

def binarySubCfg
    (label : Option BinarySubLabel) (var : BinarySubVar)
    (input : List (Option (Bool ⊕ Bool))) (output : List Bool)
    (leftRev leftWork rawRev : List Bool) : binarySubMachine.Cfg where
  l := label
  var := var
  stk
    | BinarySubStack.input => input
    | BinarySubStack.output => output
    | BinarySubStack.leftRev => leftRev
    | BinarySubStack.leftWork => leftWork
    | BinarySubStack.rawRev => rawRev

lemma binarySub_initList (input : List (Option (Bool ⊕ Bool))) :
    Turing.initList binarySubMachine input =
      binarySubCfg (some BinarySubLabel.readLeft)
        BinarySubVar.unit input [] [] [] [] := by
  simp [Turing.initList, binarySubMachine, binarySubCfg]
  congr
  funext k
  cases k <;> rfl

lemma binarySub_haltList (output : List Bool) :
    Turing.haltList binarySubMachine output =
      binarySubCfg none BinarySubVar.unit [] output [] [] [] := by
  simp [Turing.haltList, binarySubMachine, binarySubCfg]
  congr
  funext k
  cases k <;> rfl

lemma binarySub_readLeft_bit_step
    (bit : Bool) (var : BinarySubVar)
    (input : List (Option (Bool ⊕ Bool))) (output leftRev leftWork rawRev : List Bool) :
    binarySubMachine.step
        (binarySubCfg (some BinarySubLabel.readLeft) var
          (binarySubLeftSymbol bit :: input) output leftRev leftWork rawRev) =
      some
        (binarySubCfg (some (BinarySubLabel.pushLeftRev bit))
          (BinarySubVar.input (some (binarySubLeftSymbol bit)))
          input output leftRev leftWork rawRev) := by
  simp [binarySubMachine, binarySubCfg, binarySubLeftSymbol, binarySubAfterReadLeft]
  congr
  funext k
  cases k <;> rfl

lemma binarySub_readLeft_delim_step
    (var : BinarySubVar) (input : List (Option (Bool ⊕ Bool)))
    (output leftRev leftWork rawRev : List Bool) :
    binarySubMachine.step
        (binarySubCfg (some BinarySubLabel.readLeft) var
          (none :: input) output leftRev leftWork rawRev) =
      some
        (binarySubCfg (some BinarySubLabel.moveLeft)
          (BinarySubVar.input (some none)) input output leftRev leftWork rawRev) := by
  simp [binarySubMachine, binarySubCfg, binarySubAfterReadLeft]
  congr
  funext k
  cases k <;> rfl

lemma binarySub_pushLeftRev_step
    (bit : Bool) (var : BinarySubVar)
    (input : List (Option (Bool ⊕ Bool))) (output leftRev leftWork rawRev : List Bool) :
    binarySubMachine.step
        (binarySubCfg (some (BinarySubLabel.pushLeftRev bit)) var
          input output leftRev leftWork rawRev) =
      some
        (binarySubCfg (some BinarySubLabel.readLeft) var
          input output (bit :: leftRev) leftWork rawRev) := by
  simp [binarySubMachine, binarySubCfg]
  congr
  funext k
  cases k <;> rfl

lemma binarySub_moveLeft_bit_step
    (bit : Bool) (var : BinarySubVar)
    (input : List (Option (Bool ⊕ Bool))) (output : List Bool)
    (leftRev leftWork rawRev : List Bool) :
    binarySubMachine.step
        (binarySubCfg (some BinarySubLabel.moveLeft) var
          input output (bit :: leftRev) leftWork rawRev) =
      some
        (binarySubCfg (some (BinarySubLabel.pushLeftWork bit))
          (BinarySubVar.bit (some bit)) input output leftRev leftWork rawRev) := by
  simp [binarySubMachine, binarySubCfg, binarySubAfterMoveLeft]
  congr
  funext k
  cases k <;> rfl

lemma binarySub_moveLeft_empty_step
    (var : BinarySubVar)
    (input : List (Option (Bool ⊕ Bool))) (output leftWork rawRev : List Bool) :
    binarySubMachine.step
        (binarySubCfg (some BinarySubLabel.moveLeft) var
          input output [] leftWork rawRev) =
      some
        (binarySubCfg (some (BinarySubLabel.readRight false))
          (BinarySubVar.bit none) input output [] leftWork rawRev) := by
  simp [binarySubMachine, binarySubCfg, binarySubAfterMoveLeft]
  rfl

lemma binarySub_pushLeftWork_step
    (bit : Bool) (var : BinarySubVar)
    (input : List (Option (Bool ⊕ Bool))) (output : List Bool)
    (leftRev leftWork rawRev : List Bool) :
    binarySubMachine.step
        (binarySubCfg (some (BinarySubLabel.pushLeftWork bit)) var
          input output leftRev leftWork rawRev) =
      some
        (binarySubCfg (some BinarySubLabel.moveLeft) var
          input output leftRev (bit :: leftWork) rawRev) := by
  simp [binarySubMachine, binarySubCfg]
  congr
  funext k
  cases k <;> rfl

lemma binarySub_readRight_bit_step
    (carry bit : Bool) (var : BinarySubVar)
    (input : List (Option (Bool ⊕ Bool))) (output leftRev leftWork rawRev : List Bool) :
    binarySubMachine.step
        (binarySubCfg (some (BinarySubLabel.readRight carry)) var
          (binarySubRightSymbol bit :: input) output leftRev leftWork rawRev) =
      some
        (binarySubCfg (some (BinarySubLabel.popLeftForRight carry bit))
          (BinarySubVar.input (some (binarySubRightSymbol bit)))
          input output leftRev leftWork rawRev) := by
  simp [binarySubMachine, binarySubCfg, binarySubRightSymbol, binarySubAfterReadRight]
  congr
  funext k
  cases k <;> rfl

lemma binarySub_readRight_empty_step
    (carry : Bool) (var : BinarySubVar) (output leftRev leftWork rawRev : List Bool) :
    binarySubMachine.step
        (binarySubCfg (some (BinarySubLabel.readRight carry)) var
          [] output leftRev leftWork rawRev) =
      some
        (binarySubCfg (some (BinarySubLabel.finishLeft carry))
          (BinarySubVar.input none) [] output leftRev leftWork rawRev) := by
  simp [binarySubMachine, binarySubCfg, binarySubAfterReadRight]
  rfl

lemma binarySub_popLeftForRight_bit_step
    (carry rightBit leftBit : Bool) (var : BinarySubVar)
    (input : List (Option (Bool ⊕ Bool))) (output leftRev leftWork rawRev : List Bool) :
    let next := binaryNatSubStep carry leftBit rightBit
    binarySubMachine.step
        (binarySubCfg (some (BinarySubLabel.popLeftForRight carry rightBit)) var
          input output leftRev (leftBit :: leftWork) rawRev) =
      some
        (binarySubCfg (some (BinarySubLabel.pushRawReadRight next.2 next.1))
          (BinarySubVar.bit (some leftBit)) input output leftRev leftWork rawRev) := by
  simp [binarySubMachine, binarySubCfg, binarySubAfterPopLeftForRight]
  congr
  funext k
  cases k <;> rfl

lemma binarySub_popLeftForRight_empty_step
    (carry rightBit : Bool) (var : BinarySubVar)
    (input : List (Option (Bool ⊕ Bool))) (output leftRev rawRev : List Bool) :
    let next := binaryNatSubStep carry false rightBit
    binarySubMachine.step
        (binarySubCfg (some (BinarySubLabel.popLeftForRight carry rightBit)) var
          input output leftRev [] rawRev) =
      some
        (binarySubCfg (some (BinarySubLabel.pushRawReadRight next.2 next.1))
          (BinarySubVar.bit none) input output leftRev [] rawRev) := by
  simp [binarySubMachine, binarySubCfg, binarySubAfterPopLeftForRight]
  rfl

lemma binarySub_pushRawReadRight_step
    (carry bit : Bool) (var : BinarySubVar)
    (input : List (Option (Bool ⊕ Bool))) (output leftRev leftWork rawRev : List Bool) :
    binarySubMachine.step
        (binarySubCfg (some (BinarySubLabel.pushRawReadRight carry bit)) var
          input output leftRev leftWork rawRev) =
      some
        (binarySubCfg (some (BinarySubLabel.readRight carry)) var
          input output leftRev leftWork (bit :: rawRev)) := by
  simp [binarySubMachine, binarySubCfg]
  congr
  funext k
  cases k <;> rfl

lemma binarySub_finishLeft_bit_step
    (carry leftBit : Bool) (var : BinarySubVar)
    (output leftRev leftWork rawRev : List Bool) :
    let next := binaryNatSubStep carry leftBit false
    binarySubMachine.step
        (binarySubCfg (some (BinarySubLabel.finishLeft carry)) var
          [] output leftRev (leftBit :: leftWork) rawRev) =
      some
        (binarySubCfg (some (BinarySubLabel.pushRawFinishLeft next.2 next.1))
          (BinarySubVar.bit (some leftBit)) [] output leftRev leftWork rawRev) := by
  simp [binarySubMachine, binarySubCfg, binarySubAfterFinishLeft]
  congr
  funext k
  cases k <;> rfl

lemma binarySub_finishLeft_empty_step
    (carry : Bool) (var : BinarySubVar) (output leftRev rawRev : List Bool) :
    binarySubMachine.step
        (binarySubCfg (some (BinarySubLabel.finishLeft carry)) var
          [] output leftRev [] rawRev) =
      some
        (binarySubCfg (some (BinarySubLabel.finishCarry carry))
          (BinarySubVar.bit none) [] output leftRev [] rawRev) := by
  simp [binarySubMachine, binarySubCfg, binarySubAfterFinishLeft]
  rfl

lemma binarySub_pushRawFinishLeft_step
    (carry bit : Bool) (var : BinarySubVar)
    (output leftRev leftWork rawRev : List Bool) :
    binarySubMachine.step
        (binarySubCfg (some (BinarySubLabel.pushRawFinishLeft carry bit)) var
          [] output leftRev leftWork rawRev) =
      some
        (binarySubCfg (some (BinarySubLabel.finishLeft carry)) var
          [] output leftRev leftWork (bit :: rawRev)) := by
  simp [binarySubMachine, binarySubCfg]
  congr
  funext k
  cases k <;> rfl

lemma binarySub_finishCarry_false_step
    (var : BinarySubVar) (output leftRev rawRev : List Bool) :
    binarySubMachine.step
        (binarySubCfg (some (BinarySubLabel.finishCarry false)) var
          [] output leftRev [] rawRev) =
      some
        (binarySubCfg (some BinarySubLabel.trim) BinarySubVar.unit
          [] output leftRev [] rawRev) := by
  simp [binarySubMachine, binarySubCfg]
  rfl

lemma binarySub_finishCarry_true_step
    (var : BinarySubVar) (output leftRev rawRev : List Bool) :
    binarySubMachine.step
        (binarySubCfg (some (BinarySubLabel.finishCarry true)) var
          [] output leftRev [] rawRev) =
      some
        (binarySubCfg (some BinarySubLabel.trim) BinarySubVar.unit
          [] output leftRev [] rawRev) := by
  simp [binarySubMachine, binarySubCfg]
  rfl

lemma binarySub_trim_bit_step
    (bit : Bool) (var : BinarySubVar) (output leftRev leftWork rawRev : List Bool) :
    binarySubMachine.step
        (binarySubCfg (some BinarySubLabel.trim) var
          [] output leftRev leftWork (bit :: rawRev)) =
      some
        (binarySubCfg (some (binarySubAfterTrim (BinarySubVar.bit (some bit))))
          (BinarySubVar.bit (some bit)) [] output leftRev leftWork rawRev) := by
  simp [binarySubMachine, binarySubCfg]
  congr
  funext k
  cases k <;> rfl

lemma binarySub_trim_empty_step
    (var : BinarySubVar) (output leftRev leftWork : List Bool) :
    binarySubMachine.step
        (binarySubCfg (some BinarySubLabel.trim) var
          [] output leftRev leftWork []) =
      some
        (binarySubCfg (some BinarySubLabel.done)
          (BinarySubVar.bit none) [] output leftRev leftWork []) := by
  simp [binarySubMachine, binarySubCfg, binarySubAfterTrim]
  rfl

lemma binarySub_drain_bit_step
    (bit : Bool) (var : BinarySubVar) (output leftRev leftWork rawRev : List Bool) :
    binarySubMachine.step
        (binarySubCfg (some BinarySubLabel.drain) var
          [] output leftRev leftWork (bit :: rawRev)) =
      some
        (binarySubCfg (some (BinarySubLabel.pushOutput bit))
          (BinarySubVar.bit (some bit)) [] output leftRev leftWork rawRev) := by
  simp [binarySubMachine, binarySubCfg, binarySubAfterDrain]
  congr
  funext k
  cases k <;> rfl

lemma binarySub_drain_empty_step
    (var : BinarySubVar) (output leftRev leftWork : List Bool) :
    binarySubMachine.step
        (binarySubCfg (some BinarySubLabel.drain) var
          [] output leftRev leftWork []) =
      some
        (binarySubCfg (some BinarySubLabel.done)
          (BinarySubVar.bit none) [] output leftRev leftWork []) := by
  simp [binarySubMachine, binarySubCfg, binarySubAfterDrain]
  rfl

lemma binarySub_pushOutput_step
    (bit : Bool) (var : BinarySubVar) (output leftRev leftWork rawRev : List Bool) :
    binarySubMachine.step
        (binarySubCfg (some (BinarySubLabel.pushOutput bit)) var
          [] output leftRev leftWork rawRev) =
      some
        (binarySubCfg (some BinarySubLabel.drain) var
          [] (bit :: output) leftRev leftWork rawRev) := by
  simp [binarySubMachine, binarySubCfg]
  congr
  funext k
  cases k <;> rfl

lemma binarySub_done_step
    (var : BinarySubVar) (output leftRev leftWork rawRev : List Bool) :
    binarySubMachine.step
        (binarySubCfg (some BinarySubLabel.done) var
          [] output leftRev leftWork rawRev) =
      some
        (binarySubCfg none BinarySubVar.unit
          [] output leftRev leftWork rawRev) := by
  simp [binarySubMachine, binarySubCfg]
  rfl

def binarySub_readLeft_run
    (var : BinarySubVar) (left : List Bool)
    (rest : List (Option (Bool ⊕ Bool))) (output leftRev leftWork rawRev : List Bool) :
    StateTransition.EvalsToInTime binarySubMachine.step
      (binarySubCfg (some BinarySubLabel.readLeft) var
        (left.map binarySubLeftSymbol ++ none :: rest) output leftRev leftWork rawRev)
      (some
        (binarySubCfg (some BinarySubLabel.moveLeft)
          (BinarySubVar.input (some none)) rest output (left.reverse ++ leftRev)
          leftWork rawRev))
      (2 * left.length + 1) := by
  induction left generalizing var leftRev with
  | nil =>
      simpa using
        evalsToInTimeOne
          (binarySub_readLeft_delim_step var rest output leftRev leftWork rawRev)
  | cons bit left ih =>
      let c₀ := binarySubCfg (some BinarySubLabel.readLeft) var
        (binarySubLeftSymbol bit :: (left.map binarySubLeftSymbol ++ none :: rest))
        output leftRev leftWork rawRev
      let c₁ := binarySubCfg (some (BinarySubLabel.pushLeftRev bit))
        (BinarySubVar.input (some (binarySubLeftSymbol bit)))
        (left.map binarySubLeftSymbol ++ none :: rest) output leftRev leftWork rawRev
      let c₂ := binarySubCfg (some BinarySubLabel.readLeft)
        (BinarySubVar.input (some (binarySubLeftSymbol bit)))
        (left.map binarySubLeftSymbol ++ none :: rest) output (bit :: leftRev)
        leftWork rawRev
      have h₁ : StateTransition.EvalsToInTime binarySubMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (binarySub_readLeft_bit_step bit var
            (left.map binarySubLeftSymbol ++ none :: rest) output leftRev leftWork rawRev)
      have h₂ : StateTransition.EvalsToInTime binarySubMachine.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (binarySub_pushLeftRev_step bit
            (BinarySubVar.input (some (binarySubLeftSymbol bit)))
            (left.map binarySubLeftSymbol ++ none :: rest) output leftRev leftWork rawRev)
      have h₁₂ : StateTransition.EvalsToInTime binarySubMachine.step c₀ (some c₂)
          (1 + 1) :=
        StateTransition.EvalsToInTime.trans binarySubMachine.step 1 1 c₀ c₁
          (some c₂) h₁ h₂
      have hTail :=
        ih (BinarySubVar.input (some (binarySubLeftSymbol bit))) (bit :: leftRev)
      simpa [c₀, c₁, c₂, List.map_cons, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans binarySubMachine.step (1 + 1)
          (2 * left.length + 1) c₀ c₂
          (some
            (binarySubCfg (some BinarySubLabel.moveLeft)
              (BinarySubVar.input (some none)) rest output
              (left.reverse ++ bit :: leftRev) leftWork rawRev))
          h₁₂ hTail

def binarySub_moveLeft_run
    (var : BinarySubVar)
    (input : List (Option (Bool ⊕ Bool))) (output : List Bool)
    (leftRev leftWork rawRev : List Bool) :
    StateTransition.EvalsToInTime binarySubMachine.step
      (binarySubCfg (some BinarySubLabel.moveLeft) var
        input output leftRev leftWork rawRev)
      (some
        (binarySubCfg (some (BinarySubLabel.readRight false))
          (BinarySubVar.bit none) input output [] (leftRev.reverse ++ leftWork) rawRev))
      (2 * leftRev.length + 1) := by
  induction leftRev generalizing var leftWork with
  | nil =>
      simpa using
        evalsToInTimeOne
          (binarySub_moveLeft_empty_step var input output leftWork rawRev)
  | cons bit leftRev ih =>
      let c₀ := binarySubCfg (some BinarySubLabel.moveLeft) var
        input output (bit :: leftRev) leftWork rawRev
      let c₁ := binarySubCfg (some (BinarySubLabel.pushLeftWork bit))
        (BinarySubVar.bit (some bit)) input output leftRev leftWork rawRev
      let c₂ := binarySubCfg (some BinarySubLabel.moveLeft)
        (BinarySubVar.bit (some bit)) input output leftRev (bit :: leftWork) rawRev
      have h₁ : StateTransition.EvalsToInTime binarySubMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (binarySub_moveLeft_bit_step bit var input output leftRev leftWork rawRev)
      have h₂ : StateTransition.EvalsToInTime binarySubMachine.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (binarySub_pushLeftWork_step bit (BinarySubVar.bit (some bit))
            input output leftRev leftWork rawRev)
      have h₁₂ : StateTransition.EvalsToInTime binarySubMachine.step c₀ (some c₂)
          (1 + 1) :=
        StateTransition.EvalsToInTime.trans binarySubMachine.step 1 1 c₀ c₁
          (some c₂) h₁ h₂
      have hTail := ih (BinarySubVar.bit (some bit)) (bit :: leftWork)
      simpa [c₀, c₁, c₂, List.reverse_cons, List.append_assoc, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans binarySubMachine.step (1 + 1)
          (2 * leftRev.length + 1) c₀ c₂
          (some
            (binarySubCfg (some (BinarySubLabel.readRight false))
              (BinarySubVar.bit none) input output []
              (leftRev.reverse ++ bit :: leftWork) rawRev))
          h₁₂ hTail

def binarySub_drain_run
    (var : BinarySubVar) (rev output leftRev leftWork : List Bool) :
    StateTransition.EvalsToInTime binarySubMachine.step
      (binarySubCfg (some BinarySubLabel.drain) var
        [] output leftRev leftWork rev)
      (some
        (binarySubCfg none BinarySubVar.unit
          [] (rev.reverse ++ output) leftRev leftWork []))
      (2 * rev.length + 2) := by
  induction rev generalizing var output with
  | nil =>
      let c₀ := binarySubCfg (some BinarySubLabel.drain) var
        [] output leftRev leftWork []
      let c₁ := binarySubCfg (some BinarySubLabel.done)
        (BinarySubVar.bit none) [] output leftRev leftWork []
      let c₂ := binarySubCfg none BinarySubVar.unit [] output leftRev leftWork []
      have h₁ : StateTransition.EvalsToInTime binarySubMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne (binarySub_drain_empty_step var output leftRev leftWork)
      have h₂ : StateTransition.EvalsToInTime binarySubMachine.step c₁ (some c₂) 1 :=
        evalsToInTimeOne (binarySub_done_step (BinarySubVar.bit none) output leftRev leftWork [])
      have hAll :=
        StateTransition.EvalsToInTime.trans binarySubMachine.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      simpa [c₀, c₁, c₂] using hAll
  | cons bit rev ih =>
      let c₀ := binarySubCfg (some BinarySubLabel.drain) var
        [] output leftRev leftWork (bit :: rev)
      let c₁ := binarySubCfg (some (BinarySubLabel.pushOutput bit))
        (BinarySubVar.bit (some bit)) [] output leftRev leftWork rev
      let c₂ := binarySubCfg (some BinarySubLabel.drain)
        (BinarySubVar.bit (some bit)) [] (bit :: output) leftRev leftWork rev
      have h₁ : StateTransition.EvalsToInTime binarySubMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne (binarySub_drain_bit_step bit var output leftRev leftWork rev)
      have h₂ : StateTransition.EvalsToInTime binarySubMachine.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (binarySub_pushOutput_step bit (BinarySubVar.bit (some bit)) output leftRev
            leftWork rev)
      have h₁₂ : StateTransition.EvalsToInTime binarySubMachine.step c₀ (some c₂)
          (1 + 1) :=
        StateTransition.EvalsToInTime.trans binarySubMachine.step 1 1 c₀ c₁
          (some c₂) h₁ h₂
      have hTail := ih (BinarySubVar.bit (some bit)) (bit :: output)
      simpa [c₀, c₁, c₂, List.reverse_cons, List.append_assoc, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans binarySubMachine.step (1 + 1)
          (2 * rev.length + 2) c₀ c₂
          (some
            (binarySubCfg none BinarySubVar.unit []
              (rev.reverse ++ bit :: output) leftRev leftWork []))
          h₁₂ hTail

def binarySub_trim_run
    (var : BinarySubVar) (rev output leftRev leftWork : List Bool) :
    StateTransition.EvalsToInTime binarySubMachine.step
      (binarySubCfg (some BinarySubLabel.trim) var
        [] output leftRev leftWork rev)
      (some
        (binarySubCfg none BinarySubVar.unit
          [] (binaryTrimRev rev ++ output) leftRev leftWork []))
      (2 * rev.length + 2) := by
  induction rev generalizing var output with
  | nil =>
      let c₀ := binarySubCfg (some BinarySubLabel.trim) var
        [] output leftRev leftWork []
      let c₁ := binarySubCfg (some BinarySubLabel.done)
        (BinarySubVar.bit none) [] output leftRev leftWork []
      let c₂ := binarySubCfg none BinarySubVar.unit [] output leftRev leftWork []
      have h₁ : StateTransition.EvalsToInTime binarySubMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne (binarySub_trim_empty_step var output leftRev leftWork)
      have h₂ : StateTransition.EvalsToInTime binarySubMachine.step c₁ (some c₂) 1 :=
        evalsToInTimeOne (binarySub_done_step (BinarySubVar.bit none) output leftRev leftWork [])
      have hAll :=
        StateTransition.EvalsToInTime.trans binarySubMachine.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      simpa [c₀, c₁, c₂, binaryTrimRev] using hAll
  | cons bit rev ih =>
      cases bit
      · let c₀ := binarySubCfg (some BinarySubLabel.trim) var
          [] output leftRev leftWork (false :: rev)
        let c₁ := binarySubCfg (some BinarySubLabel.trim)
          (BinarySubVar.bit (some false)) [] output leftRev leftWork rev
        have h₁ : StateTransition.EvalsToInTime binarySubMachine.step c₀ (some c₁) 1 :=
          evalsToInTimeOne (binarySub_trim_bit_step false var output leftRev leftWork rev)
        have hTail := ih (BinarySubVar.bit (some false)) output
        have hAll :=
          StateTransition.EvalsToInTime.trans binarySubMachine.step 1
            (2 * rev.length + 2) c₀ c₁
            (some
              (binarySubCfg none BinarySubVar.unit []
                (binaryTrimRev rev ++ output) leftRev leftWork []))
            h₁ hTail
        refine evalsToInTime_mono (by
          simpa [c₀, c₁, binaryTrimRev, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using hAll) ?_
        simp
        omega
      · let c₀ := binarySubCfg (some BinarySubLabel.trim) var
          [] output leftRev leftWork (true :: rev)
        let c₁ := binarySubCfg (some (BinarySubLabel.pushOutput true))
          (BinarySubVar.bit (some true)) [] output leftRev leftWork rev
        let c₂ := binarySubCfg (some BinarySubLabel.drain)
          (BinarySubVar.bit (some true)) [] (true :: output) leftRev leftWork rev
        have h₁ : StateTransition.EvalsToInTime binarySubMachine.step c₀ (some c₁) 1 :=
          evalsToInTimeOne (binarySub_trim_bit_step true var output leftRev leftWork rev)
        have h₂ : StateTransition.EvalsToInTime binarySubMachine.step c₁ (some c₂) 1 :=
          evalsToInTimeOne
            (binarySub_pushOutput_step true (BinarySubVar.bit (some true)) output leftRev
              leftWork rev)
        have h₁₂ : StateTransition.EvalsToInTime binarySubMachine.step c₀ (some c₂)
            (1 + 1) :=
          StateTransition.EvalsToInTime.trans binarySubMachine.step 1 1 c₀ c₁
            (some c₂) h₁ h₂
        have hDrain := binarySub_drain_run (BinarySubVar.bit (some true)) rev
          (true :: output) leftRev leftWork
        have hAll :=
          StateTransition.EvalsToInTime.trans binarySubMachine.step (1 + 1)
            (2 * rev.length + 2) c₀ c₂
            (some
              (binarySubCfg none BinarySubVar.unit []
                (rev.reverse ++ true :: output) leftRev leftWork []))
            h₁₂ hDrain
        simpa [c₀, c₁, c₂, binaryTrimRev, List.reverse_cons, List.append_assoc,
          Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAll

end Knapsack
end Karp21
end ComplexityReduction
