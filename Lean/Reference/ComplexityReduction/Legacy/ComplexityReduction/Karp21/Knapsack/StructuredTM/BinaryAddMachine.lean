import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryAdd

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
Direct TM witness for binary natural addition.

The machine adds the two product payloads bit-by-bit, stores the raw result in
reverse order, then drops high zeroes while draining the stack to the public
output.  Pure bit-level correctness is imported from `BinaryAdd`.
-/

inductive BinaryAddStack where
  | input
  | output
  | leftRev
  | leftWork
  | rawRev
  deriving DecidableEq, Fintype

abbrev binaryAddAlphabet : BinaryAddStack → Type
  | BinaryAddStack.input => Option (Bool ⊕ Bool)
  | BinaryAddStack.output => Bool
  | BinaryAddStack.leftRev => Bool
  | BinaryAddStack.leftWork => Bool
  | BinaryAddStack.rawRev => Bool

inductive BinaryAddVar where
  | unit
  | input (head : Option (Option (Bool ⊕ Bool)))
  | bit (head : Option Bool)
  deriving DecidableEq, Fintype

inductive BinaryAddLabel where
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

def binaryAddLeftSymbol (b : Bool) : Option (Bool ⊕ Bool) :=
  some (Sum.inl b)

def binaryAddRightSymbol (b : Bool) : Option (Bool ⊕ Bool) :=
  some (Sum.inr b)

theorem binaryAddLeftSymbols_raw_eq (left : List Bool) :
    left.map (fun s : Bool => some (Sum.inl s)) =
      left.map binaryAddLeftSymbol := by
  induction left with
  | nil => rfl
  | cons bit bits ih =>
      change some (Sum.inl bit) :: bits.map (fun s : Bool => some (Sum.inl s)) =
        binaryAddLeftSymbol bit :: bits.map binaryAddLeftSymbol
      rw [ih]
      rfl

theorem binaryAddRightSymbols_raw_eq (right : List Bool) :
    right.map (fun s : Bool => some (Sum.inr s)) =
      right.map binaryAddRightSymbol := by
  induction right with
  | nil => rfl
  | cons bit bits ih =>
      change some (Sum.inr bit) :: bits.map (fun s : Bool => some (Sum.inr s)) =
        binaryAddRightSymbol bit :: bits.map binaryAddRightSymbol
      rw [ih]
      rfl

theorem binaryAddProductSymbolsRaw_eq (left right : List Bool) :
    left.map (fun s : Bool => some (Sum.inl s)) ++ [none] ++
        right.map (fun s : Bool => some (Sum.inr s)) =
      left.map binaryAddLeftSymbol ++ none :: right.map binaryAddRightSymbol := by
  rw [binaryAddLeftSymbols_raw_eq, binaryAddRightSymbols_raw_eq]
  simp

theorem binaryAddLeftSymbols_mapped_eq (left : List Bool) :
    (left.map (fun s : Bool => some (Sum.inl s))).map
        (Equiv.refl (Option (Bool ⊕ Bool))).symm =
      left.map binaryAddLeftSymbol := by
  rw [list_map_equivRefl_symm, binaryAddLeftSymbols_raw_eq]

theorem binaryAddRightSymbols_mapped_eq (right : List Bool) :
    (right.map (fun s : Bool => some (Sum.inr s))).map
        (Equiv.refl (Option (Bool ⊕ Bool))).symm =
      right.map binaryAddRightSymbol := by
  rw [list_map_equivRefl_symm, binaryAddRightSymbols_raw_eq]

theorem binaryAddProductSymbolsMapped_eq (left right : List Bool) :
    (left.map (fun s : Bool => some (Sum.inl s)) ++ [none] ++
        right.map (fun s : Bool => some (Sum.inr s))).map
        (Equiv.refl (Option (Bool ⊕ Bool))).symm =
      left.map binaryAddLeftSymbol ++ none :: right.map binaryAddRightSymbol := by
  rw [List.map_append, List.map_append, binaryAddLeftSymbols_mapped_eq,
    binaryAddRightSymbols_mapped_eq]
  simp

def binaryAddAfterReadLeft : BinaryAddVar → BinaryAddLabel
  | BinaryAddVar.input (some (some (Sum.inl bit))) => BinaryAddLabel.pushLeftRev bit
  | BinaryAddVar.input (some none) => BinaryAddLabel.moveLeft
  | BinaryAddVar.input none => BinaryAddLabel.moveLeft
  | _ => BinaryAddLabel.moveLeft

def binaryAddAfterMoveLeft : BinaryAddVar → BinaryAddLabel
  | BinaryAddVar.bit (some bit) => BinaryAddLabel.pushLeftWork bit
  | BinaryAddVar.bit none => BinaryAddLabel.readRight false
  | _ => BinaryAddLabel.readRight false

def binaryAddAfterReadRight (carry : Bool) : BinaryAddVar → BinaryAddLabel
  | BinaryAddVar.input (some (some (Sum.inr bit))) =>
      BinaryAddLabel.popLeftForRight carry bit
  | _ => BinaryAddLabel.finishLeft carry

def binaryAddAfterPopLeftForRight (carry rightBit : Bool) :
    BinaryAddVar → BinaryAddLabel
  | BinaryAddVar.bit (some leftBit) =>
      let next := binaryNatAddStep carry leftBit rightBit
      BinaryAddLabel.pushRawReadRight next.2 next.1
  | BinaryAddVar.bit none =>
      let next := binaryNatAddStep carry false rightBit
      BinaryAddLabel.pushRawReadRight next.2 next.1
  | _ =>
      let next := binaryNatAddStep carry false rightBit
      BinaryAddLabel.pushRawReadRight next.2 next.1

def binaryAddAfterFinishLeft (carry : Bool) : BinaryAddVar → BinaryAddLabel
  | BinaryAddVar.bit (some leftBit) =>
      let next := binaryNatAddStep carry leftBit false
      BinaryAddLabel.pushRawFinishLeft next.2 next.1
  | BinaryAddVar.bit none => BinaryAddLabel.finishCarry carry
  | _ => BinaryAddLabel.finishCarry carry

def binaryAddAfterTrim : BinaryAddVar → BinaryAddLabel
  | BinaryAddVar.bit (some false) => BinaryAddLabel.trim
  | BinaryAddVar.bit (some true) => BinaryAddLabel.pushOutput true
  | _ => BinaryAddLabel.done

def binaryAddAfterDrain : BinaryAddVar → BinaryAddLabel
  | BinaryAddVar.bit (some bit) => BinaryAddLabel.pushOutput bit
  | _ => BinaryAddLabel.done

def binaryAddMachine : Turing.FinTM2 where
  K := BinaryAddStack
  k₀ := BinaryAddStack.input
  k₁ := BinaryAddStack.output
  Γ := binaryAddAlphabet
  Λ := BinaryAddLabel
  main := BinaryAddLabel.readLeft
  σ := BinaryAddVar
  initialState := BinaryAddVar.unit
  Γk₀Fin := by
    dsimp [binaryAddAlphabet]
    infer_instance
  m
    | BinaryAddLabel.readLeft =>
        pop BinaryAddStack.input (fun _ head => BinaryAddVar.input head)
          (goto binaryAddAfterReadLeft)
    | BinaryAddLabel.pushLeftRev bit =>
        push BinaryAddStack.leftRev (fun _ => bit)
          (goto fun _ => BinaryAddLabel.readLeft)
    | BinaryAddLabel.moveLeft =>
        pop BinaryAddStack.leftRev (fun _ head => BinaryAddVar.bit head)
          (goto binaryAddAfterMoveLeft)
    | BinaryAddLabel.pushLeftWork bit =>
        push BinaryAddStack.leftWork (fun _ => bit)
          (goto fun _ => BinaryAddLabel.moveLeft)
    | BinaryAddLabel.readRight carry =>
        pop BinaryAddStack.input (fun _ head => BinaryAddVar.input head)
          (goto (binaryAddAfterReadRight carry))
    | BinaryAddLabel.popLeftForRight carry rightBit =>
        pop BinaryAddStack.leftWork (fun _ head => BinaryAddVar.bit head)
          (goto (binaryAddAfterPopLeftForRight carry rightBit))
    | BinaryAddLabel.pushRawReadRight carry bit =>
        push BinaryAddStack.rawRev (fun _ => bit)
          (goto fun _ => BinaryAddLabel.readRight carry)
    | BinaryAddLabel.finishLeft carry =>
        pop BinaryAddStack.leftWork (fun _ head => BinaryAddVar.bit head)
          (goto (binaryAddAfterFinishLeft carry))
    | BinaryAddLabel.pushRawFinishLeft carry bit =>
        push BinaryAddStack.rawRev (fun _ => bit)
          (goto fun _ => BinaryAddLabel.finishLeft carry)
    | BinaryAddLabel.finishCarry carry =>
        if carry then
          push BinaryAddStack.rawRev (fun _ => true)
            (load (fun _ => BinaryAddVar.unit) (goto fun _ => BinaryAddLabel.trim))
        else
          load (fun _ => BinaryAddVar.unit) (goto fun _ => BinaryAddLabel.trim)
    | BinaryAddLabel.trim =>
        pop BinaryAddStack.rawRev (fun _ head => BinaryAddVar.bit head)
          (goto binaryAddAfterTrim)
    | BinaryAddLabel.drain =>
        pop BinaryAddStack.rawRev (fun _ head => BinaryAddVar.bit head)
          (goto binaryAddAfterDrain)
    | BinaryAddLabel.pushOutput bit =>
        push BinaryAddStack.output (fun _ => bit)
          (goto fun _ => BinaryAddLabel.drain)
    | BinaryAddLabel.done =>
        load (fun _ => BinaryAddVar.unit) halt

def binaryAddCfg
    (label : Option BinaryAddLabel) (var : BinaryAddVar)
    (input : List (Option (Bool ⊕ Bool))) (output : List Bool)
    (leftRev leftWork rawRev : List Bool) : binaryAddMachine.Cfg where
  l := label
  var := var
  stk
    | BinaryAddStack.input => input
    | BinaryAddStack.output => output
    | BinaryAddStack.leftRev => leftRev
    | BinaryAddStack.leftWork => leftWork
    | BinaryAddStack.rawRev => rawRev

lemma binaryAdd_initList (input : List (Option (Bool ⊕ Bool))) :
    Turing.initList binaryAddMachine input =
      binaryAddCfg (some BinaryAddLabel.readLeft)
        BinaryAddVar.unit input [] [] [] [] := by
  simp [Turing.initList, binaryAddMachine, binaryAddCfg]
  congr
  funext k
  cases k <;> rfl

lemma binaryAdd_haltList (output : List Bool) :
    Turing.haltList binaryAddMachine output =
      binaryAddCfg none BinaryAddVar.unit [] output [] [] [] := by
  simp [Turing.haltList, binaryAddMachine, binaryAddCfg]
  congr
  funext k
  cases k <;> rfl

lemma binaryAdd_readLeft_bit_step
    (bit : Bool) (var : BinaryAddVar)
    (input : List (Option (Bool ⊕ Bool))) (output leftRev leftWork rawRev : List Bool) :
    binaryAddMachine.step
        (binaryAddCfg (some BinaryAddLabel.readLeft) var
          (binaryAddLeftSymbol bit :: input) output leftRev leftWork rawRev) =
      some
        (binaryAddCfg (some (BinaryAddLabel.pushLeftRev bit))
          (BinaryAddVar.input (some (binaryAddLeftSymbol bit)))
          input output leftRev leftWork rawRev) := by
  simp [binaryAddMachine, binaryAddCfg, binaryAddLeftSymbol, binaryAddAfterReadLeft]
  congr
  funext k
  cases k <;> rfl

lemma binaryAdd_readLeft_delim_step
    (var : BinaryAddVar) (input : List (Option (Bool ⊕ Bool)))
    (output leftRev leftWork rawRev : List Bool) :
    binaryAddMachine.step
        (binaryAddCfg (some BinaryAddLabel.readLeft) var
          (none :: input) output leftRev leftWork rawRev) =
      some
        (binaryAddCfg (some BinaryAddLabel.moveLeft)
          (BinaryAddVar.input (some none)) input output leftRev leftWork rawRev) := by
  simp [binaryAddMachine, binaryAddCfg, binaryAddAfterReadLeft]
  congr
  funext k
  cases k <;> rfl

lemma binaryAdd_pushLeftRev_step
    (bit : Bool) (var : BinaryAddVar)
    (input : List (Option (Bool ⊕ Bool))) (output leftRev leftWork rawRev : List Bool) :
    binaryAddMachine.step
        (binaryAddCfg (some (BinaryAddLabel.pushLeftRev bit)) var
          input output leftRev leftWork rawRev) =
      some
        (binaryAddCfg (some BinaryAddLabel.readLeft) var
          input output (bit :: leftRev) leftWork rawRev) := by
  simp [binaryAddMachine, binaryAddCfg]
  congr
  funext k
  cases k <;> rfl

lemma binaryAdd_moveLeft_bit_step
    (bit : Bool) (var : BinaryAddVar)
    (input : List (Option (Bool ⊕ Bool))) (output : List Bool)
    (leftRev leftWork rawRev : List Bool) :
    binaryAddMachine.step
        (binaryAddCfg (some BinaryAddLabel.moveLeft) var
          input output (bit :: leftRev) leftWork rawRev) =
      some
        (binaryAddCfg (some (BinaryAddLabel.pushLeftWork bit))
          (BinaryAddVar.bit (some bit)) input output leftRev leftWork rawRev) := by
  simp [binaryAddMachine, binaryAddCfg, binaryAddAfterMoveLeft]
  congr
  funext k
  cases k <;> rfl

lemma binaryAdd_moveLeft_empty_step
    (var : BinaryAddVar)
    (input : List (Option (Bool ⊕ Bool))) (output leftWork rawRev : List Bool) :
    binaryAddMachine.step
        (binaryAddCfg (some BinaryAddLabel.moveLeft) var
          input output [] leftWork rawRev) =
      some
        (binaryAddCfg (some (BinaryAddLabel.readRight false))
          (BinaryAddVar.bit none) input output [] leftWork rawRev) := by
  simp [binaryAddMachine, binaryAddCfg, binaryAddAfterMoveLeft]
  rfl

lemma binaryAdd_pushLeftWork_step
    (bit : Bool) (var : BinaryAddVar)
    (input : List (Option (Bool ⊕ Bool))) (output : List Bool)
    (leftRev leftWork rawRev : List Bool) :
    binaryAddMachine.step
        (binaryAddCfg (some (BinaryAddLabel.pushLeftWork bit)) var
          input output leftRev leftWork rawRev) =
      some
        (binaryAddCfg (some BinaryAddLabel.moveLeft) var
          input output leftRev (bit :: leftWork) rawRev) := by
  simp [binaryAddMachine, binaryAddCfg]
  congr
  funext k
  cases k <;> rfl

lemma binaryAdd_readRight_bit_step
    (carry bit : Bool) (var : BinaryAddVar)
    (input : List (Option (Bool ⊕ Bool))) (output leftRev leftWork rawRev : List Bool) :
    binaryAddMachine.step
        (binaryAddCfg (some (BinaryAddLabel.readRight carry)) var
          (binaryAddRightSymbol bit :: input) output leftRev leftWork rawRev) =
      some
        (binaryAddCfg (some (BinaryAddLabel.popLeftForRight carry bit))
          (BinaryAddVar.input (some (binaryAddRightSymbol bit)))
          input output leftRev leftWork rawRev) := by
  simp [binaryAddMachine, binaryAddCfg, binaryAddRightSymbol, binaryAddAfterReadRight]
  congr
  funext k
  cases k <;> rfl

lemma binaryAdd_readRight_empty_step
    (carry : Bool) (var : BinaryAddVar) (output leftRev leftWork rawRev : List Bool) :
    binaryAddMachine.step
        (binaryAddCfg (some (BinaryAddLabel.readRight carry)) var
          [] output leftRev leftWork rawRev) =
      some
        (binaryAddCfg (some (BinaryAddLabel.finishLeft carry))
          (BinaryAddVar.input none) [] output leftRev leftWork rawRev) := by
  simp [binaryAddMachine, binaryAddCfg, binaryAddAfterReadRight]
  rfl

lemma binaryAdd_popLeftForRight_bit_step
    (carry rightBit leftBit : Bool) (var : BinaryAddVar)
    (input : List (Option (Bool ⊕ Bool))) (output leftRev leftWork rawRev : List Bool) :
    let next := binaryNatAddStep carry leftBit rightBit
    binaryAddMachine.step
        (binaryAddCfg (some (BinaryAddLabel.popLeftForRight carry rightBit)) var
          input output leftRev (leftBit :: leftWork) rawRev) =
      some
        (binaryAddCfg (some (BinaryAddLabel.pushRawReadRight next.2 next.1))
          (BinaryAddVar.bit (some leftBit)) input output leftRev leftWork rawRev) := by
  simp [binaryAddMachine, binaryAddCfg, binaryAddAfterPopLeftForRight]
  congr
  funext k
  cases k <;> rfl

lemma binaryAdd_popLeftForRight_empty_step
    (carry rightBit : Bool) (var : BinaryAddVar)
    (input : List (Option (Bool ⊕ Bool))) (output leftRev rawRev : List Bool) :
    let next := binaryNatAddStep carry false rightBit
    binaryAddMachine.step
        (binaryAddCfg (some (BinaryAddLabel.popLeftForRight carry rightBit)) var
          input output leftRev [] rawRev) =
      some
        (binaryAddCfg (some (BinaryAddLabel.pushRawReadRight next.2 next.1))
          (BinaryAddVar.bit none) input output leftRev [] rawRev) := by
  simp [binaryAddMachine, binaryAddCfg, binaryAddAfterPopLeftForRight]
  rfl

lemma binaryAdd_pushRawReadRight_step
    (carry bit : Bool) (var : BinaryAddVar)
    (input : List (Option (Bool ⊕ Bool))) (output leftRev leftWork rawRev : List Bool) :
    binaryAddMachine.step
        (binaryAddCfg (some (BinaryAddLabel.pushRawReadRight carry bit)) var
          input output leftRev leftWork rawRev) =
      some
        (binaryAddCfg (some (BinaryAddLabel.readRight carry)) var
          input output leftRev leftWork (bit :: rawRev)) := by
  simp [binaryAddMachine, binaryAddCfg]
  congr
  funext k
  cases k <;> rfl

lemma binaryAdd_finishLeft_bit_step
    (carry leftBit : Bool) (var : BinaryAddVar)
    (output leftRev leftWork rawRev : List Bool) :
    let next := binaryNatAddStep carry leftBit false
    binaryAddMachine.step
        (binaryAddCfg (some (BinaryAddLabel.finishLeft carry)) var
          [] output leftRev (leftBit :: leftWork) rawRev) =
      some
        (binaryAddCfg (some (BinaryAddLabel.pushRawFinishLeft next.2 next.1))
          (BinaryAddVar.bit (some leftBit)) [] output leftRev leftWork rawRev) := by
  simp [binaryAddMachine, binaryAddCfg, binaryAddAfterFinishLeft]
  congr
  funext k
  cases k <;> rfl

lemma binaryAdd_finishLeft_empty_step
    (carry : Bool) (var : BinaryAddVar) (output leftRev rawRev : List Bool) :
    binaryAddMachine.step
        (binaryAddCfg (some (BinaryAddLabel.finishLeft carry)) var
          [] output leftRev [] rawRev) =
      some
        (binaryAddCfg (some (BinaryAddLabel.finishCarry carry))
          (BinaryAddVar.bit none) [] output leftRev [] rawRev) := by
  simp [binaryAddMachine, binaryAddCfg, binaryAddAfterFinishLeft]
  rfl

lemma binaryAdd_pushRawFinishLeft_step
    (carry bit : Bool) (var : BinaryAddVar)
    (output leftRev leftWork rawRev : List Bool) :
    binaryAddMachine.step
        (binaryAddCfg (some (BinaryAddLabel.pushRawFinishLeft carry bit)) var
          [] output leftRev leftWork rawRev) =
      some
        (binaryAddCfg (some (BinaryAddLabel.finishLeft carry)) var
          [] output leftRev leftWork (bit :: rawRev)) := by
  simp [binaryAddMachine, binaryAddCfg]
  congr
  funext k
  cases k <;> rfl

lemma binaryAdd_finishCarry_false_step
    (var : BinaryAddVar) (output leftRev rawRev : List Bool) :
    binaryAddMachine.step
        (binaryAddCfg (some (BinaryAddLabel.finishCarry false)) var
          [] output leftRev [] rawRev) =
      some
        (binaryAddCfg (some BinaryAddLabel.trim) BinaryAddVar.unit
          [] output leftRev [] rawRev) := by
  simp [binaryAddMachine, binaryAddCfg]
  rfl

lemma binaryAdd_finishCarry_true_step
    (var : BinaryAddVar) (output leftRev rawRev : List Bool) :
    binaryAddMachine.step
        (binaryAddCfg (some (BinaryAddLabel.finishCarry true)) var
          [] output leftRev [] rawRev) =
      some
        (binaryAddCfg (some BinaryAddLabel.trim) BinaryAddVar.unit
          [] output leftRev [] (true :: rawRev)) := by
  simp [binaryAddMachine, binaryAddCfg]
  congr
  funext k
  cases k <;> rfl

lemma binaryAdd_trim_bit_step
    (bit : Bool) (var : BinaryAddVar) (output leftRev leftWork rawRev : List Bool) :
    binaryAddMachine.step
        (binaryAddCfg (some BinaryAddLabel.trim) var
          [] output leftRev leftWork (bit :: rawRev)) =
      some
        (binaryAddCfg (some (binaryAddAfterTrim (BinaryAddVar.bit (some bit))))
          (BinaryAddVar.bit (some bit)) [] output leftRev leftWork rawRev) := by
  simp [binaryAddMachine, binaryAddCfg]
  congr
  funext k
  cases k <;> rfl

lemma binaryAdd_trim_empty_step
    (var : BinaryAddVar) (output leftRev leftWork : List Bool) :
    binaryAddMachine.step
        (binaryAddCfg (some BinaryAddLabel.trim) var
          [] output leftRev leftWork []) =
      some
        (binaryAddCfg (some BinaryAddLabel.done)
          (BinaryAddVar.bit none) [] output leftRev leftWork []) := by
  simp [binaryAddMachine, binaryAddCfg, binaryAddAfterTrim]
  rfl

lemma binaryAdd_drain_bit_step
    (bit : Bool) (var : BinaryAddVar) (output leftRev leftWork rawRev : List Bool) :
    binaryAddMachine.step
        (binaryAddCfg (some BinaryAddLabel.drain) var
          [] output leftRev leftWork (bit :: rawRev)) =
      some
        (binaryAddCfg (some (BinaryAddLabel.pushOutput bit))
          (BinaryAddVar.bit (some bit)) [] output leftRev leftWork rawRev) := by
  simp [binaryAddMachine, binaryAddCfg, binaryAddAfterDrain]
  congr
  funext k
  cases k <;> rfl

lemma binaryAdd_drain_empty_step
    (var : BinaryAddVar) (output leftRev leftWork : List Bool) :
    binaryAddMachine.step
        (binaryAddCfg (some BinaryAddLabel.drain) var
          [] output leftRev leftWork []) =
      some
        (binaryAddCfg (some BinaryAddLabel.done)
          (BinaryAddVar.bit none) [] output leftRev leftWork []) := by
  simp [binaryAddMachine, binaryAddCfg, binaryAddAfterDrain]
  rfl

lemma binaryAdd_pushOutput_step
    (bit : Bool) (var : BinaryAddVar) (output leftRev leftWork rawRev : List Bool) :
    binaryAddMachine.step
        (binaryAddCfg (some (BinaryAddLabel.pushOutput bit)) var
          [] output leftRev leftWork rawRev) =
      some
        (binaryAddCfg (some BinaryAddLabel.drain) var
          [] (bit :: output) leftRev leftWork rawRev) := by
  simp [binaryAddMachine, binaryAddCfg]
  congr
  funext k
  cases k <;> rfl

lemma binaryAdd_done_step
    (var : BinaryAddVar) (output leftRev leftWork rawRev : List Bool) :
    binaryAddMachine.step
        (binaryAddCfg (some BinaryAddLabel.done) var
          [] output leftRev leftWork rawRev) =
      some
        (binaryAddCfg none BinaryAddVar.unit
          [] output leftRev leftWork rawRev) := by
  simp [binaryAddMachine, binaryAddCfg]
  rfl

def binaryAdd_readLeft_run
    (var : BinaryAddVar) (left : List Bool)
    (rest : List (Option (Bool ⊕ Bool))) (output leftRev leftWork rawRev : List Bool) :
    StateTransition.EvalsToInTime binaryAddMachine.step
      (binaryAddCfg (some BinaryAddLabel.readLeft) var
        (left.map binaryAddLeftSymbol ++ none :: rest) output leftRev leftWork rawRev)
      (some
        (binaryAddCfg (some BinaryAddLabel.moveLeft)
          (BinaryAddVar.input (some none)) rest output (left.reverse ++ leftRev)
          leftWork rawRev))
      (2 * left.length + 1) := by
  induction left generalizing var leftRev with
  | nil =>
      simpa using
        evalsToInTimeOne
          (binaryAdd_readLeft_delim_step var rest output leftRev leftWork rawRev)
  | cons bit left ih =>
      let c₀ := binaryAddCfg (some BinaryAddLabel.readLeft) var
        (binaryAddLeftSymbol bit :: (left.map binaryAddLeftSymbol ++ none :: rest))
        output leftRev leftWork rawRev
      let c₁ := binaryAddCfg (some (BinaryAddLabel.pushLeftRev bit))
        (BinaryAddVar.input (some (binaryAddLeftSymbol bit)))
        (left.map binaryAddLeftSymbol ++ none :: rest) output leftRev leftWork rawRev
      let c₂ := binaryAddCfg (some BinaryAddLabel.readLeft)
        (BinaryAddVar.input (some (binaryAddLeftSymbol bit)))
        (left.map binaryAddLeftSymbol ++ none :: rest) output (bit :: leftRev)
        leftWork rawRev
      have h₁ : StateTransition.EvalsToInTime binaryAddMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (binaryAdd_readLeft_bit_step bit var
            (left.map binaryAddLeftSymbol ++ none :: rest) output leftRev leftWork rawRev)
      have h₂ : StateTransition.EvalsToInTime binaryAddMachine.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (binaryAdd_pushLeftRev_step bit
            (BinaryAddVar.input (some (binaryAddLeftSymbol bit)))
            (left.map binaryAddLeftSymbol ++ none :: rest) output leftRev leftWork rawRev)
      have h₁₂ : StateTransition.EvalsToInTime binaryAddMachine.step c₀ (some c₂)
          (1 + 1) :=
        StateTransition.EvalsToInTime.trans binaryAddMachine.step 1 1 c₀ c₁
          (some c₂) h₁ h₂
      have hTail :=
        ih (BinaryAddVar.input (some (binaryAddLeftSymbol bit))) (bit :: leftRev)
      simpa [c₀, c₁, c₂, List.map_cons, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans binaryAddMachine.step (1 + 1)
          (2 * left.length + 1) c₀ c₂
          (some
            (binaryAddCfg (some BinaryAddLabel.moveLeft)
              (BinaryAddVar.input (some none)) rest output
              (left.reverse ++ bit :: leftRev) leftWork rawRev))
          h₁₂ hTail

def binaryAdd_moveLeft_run
    (var : BinaryAddVar)
    (input : List (Option (Bool ⊕ Bool))) (output : List Bool)
    (leftRev leftWork rawRev : List Bool) :
    StateTransition.EvalsToInTime binaryAddMachine.step
      (binaryAddCfg (some BinaryAddLabel.moveLeft) var
        input output leftRev leftWork rawRev)
      (some
        (binaryAddCfg (some (BinaryAddLabel.readRight false))
          (BinaryAddVar.bit none) input output [] (leftRev.reverse ++ leftWork) rawRev))
      (2 * leftRev.length + 1) := by
  induction leftRev generalizing var leftWork with
  | nil =>
      simpa using
        evalsToInTimeOne
          (binaryAdd_moveLeft_empty_step var input output leftWork rawRev)
  | cons bit leftRev ih =>
      let c₀ := binaryAddCfg (some BinaryAddLabel.moveLeft) var
        input output (bit :: leftRev) leftWork rawRev
      let c₁ := binaryAddCfg (some (BinaryAddLabel.pushLeftWork bit))
        (BinaryAddVar.bit (some bit)) input output leftRev leftWork rawRev
      let c₂ := binaryAddCfg (some BinaryAddLabel.moveLeft)
        (BinaryAddVar.bit (some bit)) input output leftRev (bit :: leftWork) rawRev
      have h₁ : StateTransition.EvalsToInTime binaryAddMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (binaryAdd_moveLeft_bit_step bit var input output leftRev leftWork rawRev)
      have h₂ : StateTransition.EvalsToInTime binaryAddMachine.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (binaryAdd_pushLeftWork_step bit (BinaryAddVar.bit (some bit))
            input output leftRev leftWork rawRev)
      have h₁₂ : StateTransition.EvalsToInTime binaryAddMachine.step c₀ (some c₂)
          (1 + 1) :=
        StateTransition.EvalsToInTime.trans binaryAddMachine.step 1 1 c₀ c₁
          (some c₂) h₁ h₂
      have hTail := ih (BinaryAddVar.bit (some bit)) (bit :: leftWork)
      simpa [c₀, c₁, c₂, List.reverse_cons, List.append_assoc, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans binaryAddMachine.step (1 + 1)
          (2 * leftRev.length + 1) c₀ c₂
          (some
            (binaryAddCfg (some (BinaryAddLabel.readRight false))
              (BinaryAddVar.bit none) input output []
              (leftRev.reverse ++ bit :: leftWork) rawRev))
          h₁₂ hTail

def binaryAdd_drain_run
    (var : BinaryAddVar) (rev output leftRev leftWork : List Bool) :
    StateTransition.EvalsToInTime binaryAddMachine.step
      (binaryAddCfg (some BinaryAddLabel.drain) var
        [] output leftRev leftWork rev)
      (some
        (binaryAddCfg none BinaryAddVar.unit
          [] (rev.reverse ++ output) leftRev leftWork []))
      (2 * rev.length + 2) := by
  induction rev generalizing var output with
  | nil =>
      let c₀ := binaryAddCfg (some BinaryAddLabel.drain) var
        [] output leftRev leftWork []
      let c₁ := binaryAddCfg (some BinaryAddLabel.done)
        (BinaryAddVar.bit none) [] output leftRev leftWork []
      let c₂ := binaryAddCfg none BinaryAddVar.unit [] output leftRev leftWork []
      have h₁ : StateTransition.EvalsToInTime binaryAddMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne (binaryAdd_drain_empty_step var output leftRev leftWork)
      have h₂ : StateTransition.EvalsToInTime binaryAddMachine.step c₁ (some c₂) 1 :=
        evalsToInTimeOne (binaryAdd_done_step (BinaryAddVar.bit none) output leftRev leftWork [])
      have hAll :=
        StateTransition.EvalsToInTime.trans binaryAddMachine.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      simpa [c₀, c₁, c₂] using hAll
  | cons bit rev ih =>
      let c₀ := binaryAddCfg (some BinaryAddLabel.drain) var
        [] output leftRev leftWork (bit :: rev)
      let c₁ := binaryAddCfg (some (BinaryAddLabel.pushOutput bit))
        (BinaryAddVar.bit (some bit)) [] output leftRev leftWork rev
      let c₂ := binaryAddCfg (some BinaryAddLabel.drain)
        (BinaryAddVar.bit (some bit)) [] (bit :: output) leftRev leftWork rev
      have h₁ : StateTransition.EvalsToInTime binaryAddMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne (binaryAdd_drain_bit_step bit var output leftRev leftWork rev)
      have h₂ : StateTransition.EvalsToInTime binaryAddMachine.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (binaryAdd_pushOutput_step bit (BinaryAddVar.bit (some bit)) output leftRev
            leftWork rev)
      have h₁₂ : StateTransition.EvalsToInTime binaryAddMachine.step c₀ (some c₂)
          (1 + 1) :=
        StateTransition.EvalsToInTime.trans binaryAddMachine.step 1 1 c₀ c₁
          (some c₂) h₁ h₂
      have hTail := ih (BinaryAddVar.bit (some bit)) (bit :: output)
      simpa [c₀, c₁, c₂, List.reverse_cons, List.append_assoc, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans binaryAddMachine.step (1 + 1)
          (2 * rev.length + 2) c₀ c₂
          (some
            (binaryAddCfg none BinaryAddVar.unit []
              (rev.reverse ++ bit :: output) leftRev leftWork []))
          h₁₂ hTail

def binaryAdd_trim_run
    (var : BinaryAddVar) (rev output leftRev leftWork : List Bool) :
    StateTransition.EvalsToInTime binaryAddMachine.step
      (binaryAddCfg (some BinaryAddLabel.trim) var
        [] output leftRev leftWork rev)
      (some
        (binaryAddCfg none BinaryAddVar.unit
          [] (binaryTrimRev rev ++ output) leftRev leftWork []))
      (2 * rev.length + 2) := by
  induction rev generalizing var output with
  | nil =>
      let c₀ := binaryAddCfg (some BinaryAddLabel.trim) var
        [] output leftRev leftWork []
      let c₁ := binaryAddCfg (some BinaryAddLabel.done)
        (BinaryAddVar.bit none) [] output leftRev leftWork []
      let c₂ := binaryAddCfg none BinaryAddVar.unit [] output leftRev leftWork []
      have h₁ : StateTransition.EvalsToInTime binaryAddMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne (binaryAdd_trim_empty_step var output leftRev leftWork)
      have h₂ : StateTransition.EvalsToInTime binaryAddMachine.step c₁ (some c₂) 1 :=
        evalsToInTimeOne (binaryAdd_done_step (BinaryAddVar.bit none) output leftRev leftWork [])
      have hAll :=
        StateTransition.EvalsToInTime.trans binaryAddMachine.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      simpa [c₀, c₁, c₂, binaryTrimRev] using hAll
  | cons bit rev ih =>
      cases bit
      · let c₀ := binaryAddCfg (some BinaryAddLabel.trim) var
          [] output leftRev leftWork (false :: rev)
        let c₁ := binaryAddCfg (some BinaryAddLabel.trim)
          (BinaryAddVar.bit (some false)) [] output leftRev leftWork rev
        have h₁ : StateTransition.EvalsToInTime binaryAddMachine.step c₀ (some c₁) 1 :=
          evalsToInTimeOne (binaryAdd_trim_bit_step false var output leftRev leftWork rev)
        have hTail := ih (BinaryAddVar.bit (some false)) output
        have hAll :=
          StateTransition.EvalsToInTime.trans binaryAddMachine.step 1
            (2 * rev.length + 2) c₀ c₁
            (some
              (binaryAddCfg none BinaryAddVar.unit []
                (binaryTrimRev rev ++ output) leftRev leftWork []))
            h₁ hTail
        refine evalsToInTime_mono (by
          simpa [c₀, c₁, binaryTrimRev, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using hAll) ?_
        simp
        omega
      · let c₀ := binaryAddCfg (some BinaryAddLabel.trim) var
          [] output leftRev leftWork (true :: rev)
        let c₁ := binaryAddCfg (some (BinaryAddLabel.pushOutput true))
          (BinaryAddVar.bit (some true)) [] output leftRev leftWork rev
        let c₂ := binaryAddCfg (some BinaryAddLabel.drain)
          (BinaryAddVar.bit (some true)) [] (true :: output) leftRev leftWork rev
        have h₁ : StateTransition.EvalsToInTime binaryAddMachine.step c₀ (some c₁) 1 :=
          evalsToInTimeOne (binaryAdd_trim_bit_step true var output leftRev leftWork rev)
        have h₂ : StateTransition.EvalsToInTime binaryAddMachine.step c₁ (some c₂) 1 :=
          evalsToInTimeOne
            (binaryAdd_pushOutput_step true (BinaryAddVar.bit (some true)) output leftRev
              leftWork rev)
        have h₁₂ : StateTransition.EvalsToInTime binaryAddMachine.step c₀ (some c₂)
            (1 + 1) :=
          StateTransition.EvalsToInTime.trans binaryAddMachine.step 1 1 c₀ c₁
            (some c₂) h₁ h₂
        have hDrain := binaryAdd_drain_run (BinaryAddVar.bit (some true)) rev
          (true :: output) leftRev leftWork
        have hAll :=
          StateTransition.EvalsToInTime.trans binaryAddMachine.step (1 + 1)
            (2 * rev.length + 2) c₀ c₂
            (some
              (binaryAddCfg none BinaryAddVar.unit []
                (rev.reverse ++ true :: output) leftRev leftWork []))
            h₁₂ hDrain
        simpa [c₀, c₁, c₂, binaryTrimRev, List.reverse_cons, List.append_assoc,
          Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAll

end Knapsack
end Karp21
end ComplexityReduction
