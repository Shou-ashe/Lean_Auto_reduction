import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryCompare

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

open Turing.TM2.Stmt
open TM2Programs

/-!
Direct TM witness for the binary natural comparison primitive.

The machine consumes an encoded product of two `binaryNat` payloads.  It first
copies the left payload through a reversal buffer so that its stack is again
little-endian, then scans the right payload while updating the carry/borrow
state from `binarySuccLeStep`.
-/

inductive BinaryCompareStack where
  | input
  | output
  | leftRev
  | leftWork
  deriving DecidableEq, Fintype

abbrev binaryCompareAlphabet : BinaryCompareStack → Type
  | BinaryCompareStack.input => Option (Bool ⊕ Bool)
  | BinaryCompareStack.output => Bool
  | BinaryCompareStack.leftRev => Bool
  | BinaryCompareStack.leftWork => Bool

inductive BinaryCompareVar where
  | unit
  | input (head : Option (Option (Bool ⊕ Bool)))
  | bit (head : Option Bool)
  deriving DecidableEq, Fintype

inductive BinaryCompareLabel where
  | readLeft (carry borrow : Bool)
  | pushLeftRev (carry borrow bit : Bool)
  | moveLeft (carry borrow : Bool)
  | pushLeftWork (carry borrow bit : Bool)
  | readRight (carry borrow : Bool)
  | popLeftForRight (carry borrow rightBit : Bool)
  | finishLeft (carry borrow : Bool)
  | write (out : Bool)
  deriving DecidableEq, Fintype

def binaryCompareLeftSymbol (b : Bool) : Option (Bool ⊕ Bool) :=
  some (Sum.inl b)

def binaryCompareRightSymbol (b : Bool) : Option (Bool ⊕ Bool) :=
  some (Sum.inr b)

def binaryCompareFinalBool (carry borrow : Bool) : Bool :=
  decide (boolBitValue carry + boolBitValue borrow ≤ 0)

def binaryCompareAfterReadLeft (carry borrow : Bool) : BinaryCompareVar → BinaryCompareLabel
  | BinaryCompareVar.input (some (some (Sum.inl bit))) =>
      BinaryCompareLabel.pushLeftRev carry borrow bit
  | BinaryCompareVar.input (some none) => BinaryCompareLabel.moveLeft carry borrow
  | BinaryCompareVar.input none => BinaryCompareLabel.moveLeft carry borrow
  | _ => BinaryCompareLabel.moveLeft carry borrow

def binaryCompareAfterMoveLeft (carry borrow : Bool) : BinaryCompareVar → BinaryCompareLabel
  | BinaryCompareVar.bit (some bit) => BinaryCompareLabel.pushLeftWork carry borrow bit
  | BinaryCompareVar.bit none => BinaryCompareLabel.readRight carry borrow
  | _ => BinaryCompareLabel.readRight carry borrow

def binaryCompareAfterReadRight (carry borrow : Bool) : BinaryCompareVar → BinaryCompareLabel
  | BinaryCompareVar.input (some (some (Sum.inr bit))) =>
      BinaryCompareLabel.popLeftForRight carry borrow bit
  | _ => BinaryCompareLabel.finishLeft carry borrow

def binaryCompareAfterPopLeftForRight
    (carry borrow rightBit : Bool) : BinaryCompareVar → BinaryCompareLabel
  | BinaryCompareVar.bit (some leftBit) =>
      let next := binarySuccLeStep carry borrow leftBit rightBit
      BinaryCompareLabel.readRight next.1 next.2
  | BinaryCompareVar.bit none =>
      let next := binarySuccLeStep carry borrow false rightBit
      BinaryCompareLabel.readRight next.1 next.2
  | _ =>
      let next := binarySuccLeStep carry borrow false rightBit
      BinaryCompareLabel.readRight next.1 next.2

def binaryCompareAfterFinishLeft (carry borrow : Bool) : BinaryCompareVar → BinaryCompareLabel
  | BinaryCompareVar.bit (some leftBit) =>
      let next := binarySuccLeStep carry borrow leftBit false
      BinaryCompareLabel.finishLeft next.1 next.2
  | BinaryCompareVar.bit none =>
      BinaryCompareLabel.write (binaryCompareFinalBool carry borrow)
  | _ => BinaryCompareLabel.write (binaryCompareFinalBool carry borrow)

def binaryCompareMachine : Turing.FinTM2 where
  K := BinaryCompareStack
  k₀ := BinaryCompareStack.input
  k₁ := BinaryCompareStack.output
  Γ := binaryCompareAlphabet
  Λ := BinaryCompareLabel
  main := BinaryCompareLabel.readLeft true false
  σ := BinaryCompareVar
  initialState := BinaryCompareVar.unit
  Γk₀Fin := by
    dsimp [binaryCompareAlphabet]
    infer_instance
  m
    | BinaryCompareLabel.readLeft carry borrow =>
        pop BinaryCompareStack.input (fun _ head => BinaryCompareVar.input head)
          (goto (binaryCompareAfterReadLeft carry borrow))
    | BinaryCompareLabel.pushLeftRev carry borrow bit =>
        push BinaryCompareStack.leftRev (fun _ => bit)
          (goto fun _ => BinaryCompareLabel.readLeft carry borrow)
    | BinaryCompareLabel.moveLeft carry borrow =>
        pop BinaryCompareStack.leftRev (fun _ head => BinaryCompareVar.bit head)
          (goto (binaryCompareAfterMoveLeft carry borrow))
    | BinaryCompareLabel.pushLeftWork carry borrow bit =>
        push BinaryCompareStack.leftWork (fun _ => bit)
          (goto fun _ => BinaryCompareLabel.moveLeft carry borrow)
    | BinaryCompareLabel.readRight carry borrow =>
        pop BinaryCompareStack.input (fun _ head => BinaryCompareVar.input head)
          (goto (binaryCompareAfterReadRight carry borrow))
    | BinaryCompareLabel.popLeftForRight carry borrow rightBit =>
        pop BinaryCompareStack.leftWork (fun _ head => BinaryCompareVar.bit head)
          (goto (binaryCompareAfterPopLeftForRight carry borrow rightBit))
    | BinaryCompareLabel.finishLeft carry borrow =>
        pop BinaryCompareStack.leftWork (fun _ head => BinaryCompareVar.bit head)
          (goto (binaryCompareAfterFinishLeft carry borrow))
    | BinaryCompareLabel.write out =>
        push BinaryCompareStack.output (fun _ => out)
          (load (fun _ => BinaryCompareVar.unit) halt)

def binaryCompareCfg
    (label : Option BinaryCompareLabel) (var : BinaryCompareVar)
    (input : List (Option (Bool ⊕ Bool))) (output : List Bool)
    (leftRev leftWork : List Bool) : binaryCompareMachine.Cfg where
  l := label
  var := var
  stk
    | BinaryCompareStack.input => input
    | BinaryCompareStack.output => output
    | BinaryCompareStack.leftRev => leftRev
    | BinaryCompareStack.leftWork => leftWork

lemma binaryCompare_initList (input : List (Option (Bool ⊕ Bool))) :
    Turing.initList binaryCompareMachine input =
      binaryCompareCfg (some (BinaryCompareLabel.readLeft true false))
        BinaryCompareVar.unit input [] [] [] := by
  simp [Turing.initList, binaryCompareMachine, binaryCompareCfg]
  congr
  funext k
  cases k <;> rfl

lemma binaryCompare_haltList (output : List Bool) :
    Turing.haltList binaryCompareMachine output =
      binaryCompareCfg none BinaryCompareVar.unit [] output [] [] := by
  simp [Turing.haltList, binaryCompareMachine, binaryCompareCfg]
  congr
  funext k
  cases k <;> rfl

lemma binaryCompare_readLeft_bit_step
    (carry borrow bit : Bool) (var : BinaryCompareVar)
    (input : List (Option (Bool ⊕ Bool))) (output leftRev leftWork : List Bool) :
    binaryCompareMachine.step
        (binaryCompareCfg (some (BinaryCompareLabel.readLeft carry borrow)) var
          (binaryCompareLeftSymbol bit :: input) output leftRev leftWork) =
      some
        (binaryCompareCfg (some (BinaryCompareLabel.pushLeftRev carry borrow bit))
          (BinaryCompareVar.input (some (binaryCompareLeftSymbol bit)))
          input output leftRev leftWork) := by
  simp [binaryCompareMachine, binaryCompareCfg, binaryCompareLeftSymbol,
    binaryCompareAfterReadLeft]
  congr
  funext k
  cases k <;> rfl

lemma binaryCompare_readLeft_delim_step
    (carry borrow : Bool) (var : BinaryCompareVar)
    (input : List (Option (Bool ⊕ Bool))) (output leftRev leftWork : List Bool) :
    binaryCompareMachine.step
        (binaryCompareCfg (some (BinaryCompareLabel.readLeft carry borrow)) var
          (none :: input) output leftRev leftWork) =
      some
        (binaryCompareCfg (some (BinaryCompareLabel.moveLeft carry borrow))
          (BinaryCompareVar.input (some none)) input output leftRev leftWork) := by
  simp [binaryCompareMachine, binaryCompareCfg, binaryCompareAfterReadLeft]
  congr
  funext k
  cases k <;> rfl

lemma binaryCompare_pushLeftRev_step
    (carry borrow bit : Bool) (var : BinaryCompareVar)
    (input : List (Option (Bool ⊕ Bool))) (output leftRev leftWork : List Bool) :
    binaryCompareMachine.step
        (binaryCompareCfg (some (BinaryCompareLabel.pushLeftRev carry borrow bit)) var
          input output leftRev leftWork) =
      some
        (binaryCompareCfg (some (BinaryCompareLabel.readLeft carry borrow)) var
          input output (bit :: leftRev) leftWork) := by
  simp [binaryCompareMachine, binaryCompareCfg]
  congr
  funext k
  cases k <;> rfl

lemma binaryCompare_moveLeft_bit_step
    (carry borrow bit : Bool) (var : BinaryCompareVar)
    (input : List (Option (Bool ⊕ Bool))) (output : List Bool)
    (leftRev leftWork : List Bool) :
    binaryCompareMachine.step
        (binaryCompareCfg (some (BinaryCompareLabel.moveLeft carry borrow)) var
          input output (bit :: leftRev) leftWork) =
      some
        (binaryCompareCfg (some (BinaryCompareLabel.pushLeftWork carry borrow bit))
          (BinaryCompareVar.bit (some bit)) input output leftRev leftWork) := by
  simp [binaryCompareMachine, binaryCompareCfg, binaryCompareAfterMoveLeft]
  congr
  funext k
  cases k <;> rfl

lemma binaryCompare_moveLeft_empty_step
    (carry borrow : Bool) (var : BinaryCompareVar)
    (input : List (Option (Bool ⊕ Bool))) (output leftWork : List Bool) :
    binaryCompareMachine.step
        (binaryCompareCfg (some (BinaryCompareLabel.moveLeft carry borrow)) var
          input output [] leftWork) =
      some
        (binaryCompareCfg (some (BinaryCompareLabel.readRight carry borrow))
          (BinaryCompareVar.bit none) input output [] leftWork) := by
  simp [binaryCompareMachine, binaryCompareCfg, binaryCompareAfterMoveLeft]
  rfl

lemma binaryCompare_pushLeftWork_step
    (carry borrow bit : Bool) (var : BinaryCompareVar)
    (input : List (Option (Bool ⊕ Bool))) (output : List Bool)
    (leftRev leftWork : List Bool) :
    binaryCompareMachine.step
        (binaryCompareCfg (some (BinaryCompareLabel.pushLeftWork carry borrow bit)) var
          input output leftRev leftWork) =
      some
        (binaryCompareCfg (some (BinaryCompareLabel.moveLeft carry borrow)) var
          input output leftRev (bit :: leftWork)) := by
  simp [binaryCompareMachine, binaryCompareCfg]
  congr
  funext k
  cases k <;> rfl

lemma binaryCompare_readRight_bit_step
    (carry borrow bit : Bool) (var : BinaryCompareVar)
    (input : List (Option (Bool ⊕ Bool))) (output leftRev leftWork : List Bool) :
    binaryCompareMachine.step
        (binaryCompareCfg (some (BinaryCompareLabel.readRight carry borrow)) var
          (binaryCompareRightSymbol bit :: input) output leftRev leftWork) =
      some
        (binaryCompareCfg (some (BinaryCompareLabel.popLeftForRight carry borrow bit))
          (BinaryCompareVar.input (some (binaryCompareRightSymbol bit)))
          input output leftRev leftWork) := by
  simp [binaryCompareMachine, binaryCompareCfg, binaryCompareRightSymbol,
    binaryCompareAfterReadRight]
  congr
  funext k
  cases k <;> rfl

lemma binaryCompare_readRight_empty_step
    (carry borrow : Bool) (var : BinaryCompareVar)
    (output leftRev leftWork : List Bool) :
    binaryCompareMachine.step
        (binaryCompareCfg (some (BinaryCompareLabel.readRight carry borrow)) var
          [] output leftRev leftWork) =
      some
        (binaryCompareCfg (some (BinaryCompareLabel.finishLeft carry borrow))
          (BinaryCompareVar.input none) [] output leftRev leftWork) := by
  simp [binaryCompareMachine, binaryCompareCfg, binaryCompareAfterReadRight]
  rfl

lemma binaryCompare_popLeftForRight_bit_step
    (carry borrow rightBit leftBit : Bool) (var : BinaryCompareVar)
    (input : List (Option (Bool ⊕ Bool))) (output leftRev leftWork : List Bool) :
    let next := binarySuccLeStep carry borrow leftBit rightBit
    binaryCompareMachine.step
        (binaryCompareCfg
          (some (BinaryCompareLabel.popLeftForRight carry borrow rightBit)) var
          input output leftRev (leftBit :: leftWork)) =
      some
        (binaryCompareCfg (some (BinaryCompareLabel.readRight next.1 next.2))
          (BinaryCompareVar.bit (some leftBit)) input output leftRev leftWork) := by
  simp [binaryCompareMachine, binaryCompareCfg, binaryCompareAfterPopLeftForRight]
  congr
  funext k
  cases k <;> rfl

lemma binaryCompare_popLeftForRight_empty_step
    (carry borrow rightBit : Bool) (var : BinaryCompareVar)
    (input : List (Option (Bool ⊕ Bool))) (output leftRev : List Bool) :
    let next := binarySuccLeStep carry borrow false rightBit
    binaryCompareMachine.step
        (binaryCompareCfg
          (some (BinaryCompareLabel.popLeftForRight carry borrow rightBit)) var
          input output leftRev []) =
      some
        (binaryCompareCfg (some (BinaryCompareLabel.readRight next.1 next.2))
          (BinaryCompareVar.bit none) input output leftRev []) := by
  simp [binaryCompareMachine, binaryCompareCfg, binaryCompareAfterPopLeftForRight]
  rfl

lemma binaryCompare_finishLeft_bit_step
    (carry borrow leftBit : Bool) (var : BinaryCompareVar)
    (output leftRev leftWork : List Bool) :
    let next := binarySuccLeStep carry borrow leftBit false
    binaryCompareMachine.step
        (binaryCompareCfg (some (BinaryCompareLabel.finishLeft carry borrow)) var
          [] output leftRev (leftBit :: leftWork)) =
      some
        (binaryCompareCfg (some (BinaryCompareLabel.finishLeft next.1 next.2))
          (BinaryCompareVar.bit (some leftBit)) [] output leftRev leftWork) := by
  simp [binaryCompareMachine, binaryCompareCfg, binaryCompareAfterFinishLeft]
  congr
  funext k
  cases k <;> rfl

lemma binaryCompare_finishLeft_empty_step
    (carry borrow : Bool) (var : BinaryCompareVar) (output leftRev : List Bool) :
    binaryCompareMachine.step
        (binaryCompareCfg (some (BinaryCompareLabel.finishLeft carry borrow)) var
          [] output leftRev []) =
      some
        (binaryCompareCfg
          (some (BinaryCompareLabel.write (binaryCompareFinalBool carry borrow)))
          (BinaryCompareVar.bit none) [] output leftRev []) := by
  simp [binaryCompareMachine, binaryCompareCfg, binaryCompareAfterFinishLeft]
  rfl

lemma binaryCompare_write_step (out : Bool) (var : BinaryCompareVar)
    (output leftRev leftWork : List Bool) :
    binaryCompareMachine.step
        (binaryCompareCfg (some (BinaryCompareLabel.write out)) var
          [] output leftRev leftWork) =
      some (binaryCompareCfg none BinaryCompareVar.unit [] (out :: output) leftRev leftWork) := by
  simp [binaryCompareMachine, binaryCompareCfg]
  congr
  funext k
  cases k <;> rfl

def binaryCompare_readLeft_run
    (carry borrow : Bool) (var : BinaryCompareVar) (left : List Bool)
    (rest : List (Option (Bool ⊕ Bool))) (output leftRev leftWork : List Bool) :
    StateTransition.EvalsToInTime binaryCompareMachine.step
      (binaryCompareCfg (some (BinaryCompareLabel.readLeft carry borrow)) var
        (left.map binaryCompareLeftSymbol ++ none :: rest) output leftRev leftWork)
      (some
        (binaryCompareCfg (some (BinaryCompareLabel.moveLeft carry borrow))
          (BinaryCompareVar.input (some none)) rest output (left.reverse ++ leftRev)
          leftWork))
      (2 * left.length + 1) := by
  induction left generalizing var leftRev with
  | nil =>
      simpa using
        evalsToInTimeOne
          (binaryCompare_readLeft_delim_step carry borrow var rest output leftRev leftWork)
  | cons bit left ih =>
      let c₀ := binaryCompareCfg (some (BinaryCompareLabel.readLeft carry borrow)) var
        (binaryCompareLeftSymbol bit :: (left.map binaryCompareLeftSymbol ++ none :: rest))
        output leftRev leftWork
      let c₁ := binaryCompareCfg (some (BinaryCompareLabel.pushLeftRev carry borrow bit))
        (BinaryCompareVar.input (some (binaryCompareLeftSymbol bit)))
        (left.map binaryCompareLeftSymbol ++ none :: rest) output leftRev leftWork
      let c₂ := binaryCompareCfg (some (BinaryCompareLabel.readLeft carry borrow))
        (BinaryCompareVar.input (some (binaryCompareLeftSymbol bit)))
        (left.map binaryCompareLeftSymbol ++ none :: rest) output (bit :: leftRev) leftWork
      have h₁ : StateTransition.EvalsToInTime binaryCompareMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (binaryCompare_readLeft_bit_step carry borrow bit var
            (left.map binaryCompareLeftSymbol ++ none :: rest) output leftRev leftWork)
      have h₂ : StateTransition.EvalsToInTime binaryCompareMachine.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (binaryCompare_pushLeftRev_step carry borrow bit
            (BinaryCompareVar.input (some (binaryCompareLeftSymbol bit)))
            (left.map binaryCompareLeftSymbol ++ none :: rest) output leftRev leftWork)
      have h₁₂ : StateTransition.EvalsToInTime binaryCompareMachine.step c₀ (some c₂)
          (1 + 1) :=
        StateTransition.EvalsToInTime.trans binaryCompareMachine.step 1 1 c₀ c₁
          (some c₂) h₁ h₂
      have hTail :=
        ih (BinaryCompareVar.input (some (binaryCompareLeftSymbol bit))) (bit :: leftRev)
      simpa [c₀, c₁, c₂, List.map_cons, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans binaryCompareMachine.step (1 + 1)
          (2 * left.length + 1) c₀ c₂
          (some
            (binaryCompareCfg (some (BinaryCompareLabel.moveLeft carry borrow))
              (BinaryCompareVar.input (some none)) rest output
              (left.reverse ++ bit :: leftRev) leftWork))
          h₁₂ hTail

def binaryCompare_moveLeft_run
    (carry borrow : Bool) (var : BinaryCompareVar)
    (input : List (Option (Bool ⊕ Bool))) (output : List Bool)
    (leftRev leftWork : List Bool) :
    StateTransition.EvalsToInTime binaryCompareMachine.step
      (binaryCompareCfg (some (BinaryCompareLabel.moveLeft carry borrow)) var
        input output leftRev leftWork)
      (some
        (binaryCompareCfg (some (BinaryCompareLabel.readRight carry borrow))
          (BinaryCompareVar.bit none) input output [] (leftRev.reverse ++ leftWork)))
      (2 * leftRev.length + 1) := by
  induction leftRev generalizing var leftWork with
  | nil =>
      simpa using
        evalsToInTimeOne
          (binaryCompare_moveLeft_empty_step carry borrow var input output leftWork)
  | cons bit leftRev ih =>
      let c₀ := binaryCompareCfg (some (BinaryCompareLabel.moveLeft carry borrow)) var
        input output (bit :: leftRev) leftWork
      let c₁ := binaryCompareCfg (some (BinaryCompareLabel.pushLeftWork carry borrow bit))
        (BinaryCompareVar.bit (some bit)) input output leftRev leftWork
      let c₂ := binaryCompareCfg (some (BinaryCompareLabel.moveLeft carry borrow))
        (BinaryCompareVar.bit (some bit)) input output leftRev (bit :: leftWork)
      have h₁ : StateTransition.EvalsToInTime binaryCompareMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (binaryCompare_moveLeft_bit_step carry borrow bit var input output leftRev leftWork)
      have h₂ : StateTransition.EvalsToInTime binaryCompareMachine.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (binaryCompare_pushLeftWork_step carry borrow bit (BinaryCompareVar.bit (some bit))
            input output leftRev leftWork)
      have h₁₂ : StateTransition.EvalsToInTime binaryCompareMachine.step c₀ (some c₂)
          (1 + 1) :=
        StateTransition.EvalsToInTime.trans binaryCompareMachine.step 1 1 c₀ c₁
          (some c₂) h₁ h₂
      have hTail := ih (BinaryCompareVar.bit (some bit)) (bit :: leftWork)
      simpa [c₀, c₁, c₂, List.reverse_cons, List.append_assoc, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans binaryCompareMachine.step (1 + 1)
          (2 * leftRev.length + 1) c₀ c₂
          (some
            (binaryCompareCfg (some (BinaryCompareLabel.readRight carry borrow))
              (BinaryCompareVar.bit none) input output [] (leftRev.reverse ++ bit :: leftWork)))
          h₁₂ hTail

def binaryCompare_finishLeft_run
    (carry borrow : Bool) (var : BinaryCompareVar) (left : List Bool)
    (output leftRev : List Bool) :
    StateTransition.EvalsToInTime binaryCompareMachine.step
      (binaryCompareCfg (some (BinaryCompareLabel.finishLeft carry borrow)) var
        [] output leftRev left)
      (some
        (binaryCompareCfg
          (some (BinaryCompareLabel.write (binaryNatSuccLeBitsAux left [] carry borrow)))
          (BinaryCompareVar.bit none) [] output leftRev []))
      (left.length + 1) := by
  induction left generalizing carry borrow var with
  | nil =>
      simpa [binaryNatSuccLeBitsAux, binaryCompareFinalBool] using
        evalsToInTimeOne
          (binaryCompare_finishLeft_empty_step carry borrow var output leftRev)
  | cons leftBit left ih =>
      let next := binarySuccLeStep carry borrow leftBit false
      let c₀ := binaryCompareCfg (some (BinaryCompareLabel.finishLeft carry borrow)) var
        [] output leftRev (leftBit :: left)
      let c₁ := binaryCompareCfg (some (BinaryCompareLabel.finishLeft next.1 next.2))
        (BinaryCompareVar.bit (some leftBit)) [] output leftRev left
      have h₁ : StateTransition.EvalsToInTime binaryCompareMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (binaryCompare_finishLeft_bit_step carry borrow leftBit var output leftRev left)
      have hTail := ih next.1 next.2 (BinaryCompareVar.bit (some leftBit))
      simpa [c₀, c₁, next, binaryNatSuccLeBitsAux, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans binaryCompareMachine.step 1 (left.length + 1)
          c₀ c₁
          (some
            (binaryCompareCfg
              (some (BinaryCompareLabel.write
                (binaryNatSuccLeBitsAux left [] next.1 next.2)))
              (BinaryCompareVar.bit none) [] output leftRev []))
          h₁ hTail

def binaryCompare_readRight_run
    (carry borrow : Bool) (var : BinaryCompareVar) (left right : List Bool)
    (output leftRev : List Bool) :
    StateTransition.EvalsToInTime binaryCompareMachine.step
      (binaryCompareCfg (some (BinaryCompareLabel.readRight carry borrow)) var
        (right.map binaryCompareRightSymbol) output leftRev left)
      (some
        (binaryCompareCfg
          (some (BinaryCompareLabel.write (binaryNatSuccLeBitsAux left right carry borrow)))
          (BinaryCompareVar.bit none) [] output leftRev []))
      (2 * right.length + left.length + 2) := by
  induction right generalizing carry borrow var left with
  | nil =>
      let c₀ := binaryCompareCfg (some (BinaryCompareLabel.readRight carry borrow)) var
        [] output leftRev left
      let c₁ := binaryCompareCfg (some (BinaryCompareLabel.finishLeft carry borrow))
        (BinaryCompareVar.input none) [] output leftRev left
      have h₁ : StateTransition.EvalsToInTime binaryCompareMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (binaryCompare_readRight_empty_step carry borrow var output leftRev left)
      have hTail :=
        binaryCompare_finishLeft_run carry borrow (BinaryCompareVar.input none) left output leftRev
      simpa [c₀, c₁, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans binaryCompareMachine.step 1 (left.length + 1)
          c₀ c₁
          (some
            (binaryCompareCfg
              (some (BinaryCompareLabel.write (binaryNatSuccLeBitsAux left [] carry borrow)))
              (BinaryCompareVar.bit none) [] output leftRev []))
          h₁ hTail
  | cons rightBit right ih =>
      cases left with
      | nil =>
          let next := binarySuccLeStep carry borrow false rightBit
          let c₀ := binaryCompareCfg (some (BinaryCompareLabel.readRight carry borrow)) var
            (binaryCompareRightSymbol rightBit :: right.map binaryCompareRightSymbol)
            output leftRev []
          let c₁ := binaryCompareCfg
            (some (BinaryCompareLabel.popLeftForRight carry borrow rightBit))
            (BinaryCompareVar.input (some (binaryCompareRightSymbol rightBit)))
            (right.map binaryCompareRightSymbol) output leftRev []
          let c₂ := binaryCompareCfg (some (BinaryCompareLabel.readRight next.1 next.2))
            (BinaryCompareVar.bit none) (right.map binaryCompareRightSymbol) output leftRev []
          have h₁ : StateTransition.EvalsToInTime binaryCompareMachine.step c₀ (some c₁) 1 :=
            evalsToInTimeOne
              (binaryCompare_readRight_bit_step carry borrow rightBit var
                (right.map binaryCompareRightSymbol) output leftRev [])
          have h₂ : StateTransition.EvalsToInTime binaryCompareMachine.step c₁ (some c₂) 1 :=
            evalsToInTimeOne
              (binaryCompare_popLeftForRight_empty_step carry borrow rightBit
                (BinaryCompareVar.input (some (binaryCompareRightSymbol rightBit)))
                (right.map binaryCompareRightSymbol) output leftRev)
          have h₁₂ : StateTransition.EvalsToInTime binaryCompareMachine.step c₀ (some c₂)
              (1 + 1) :=
            StateTransition.EvalsToInTime.trans binaryCompareMachine.step 1 1 c₀ c₁
              (some c₂) h₁ h₂
          have hTail := ih next.1 next.2 (BinaryCompareVar.bit none) []
          simpa [c₀, c₁, c₂, next, List.map_cons, binaryNatSuccLeBitsAux, Nat.mul_add,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            StateTransition.EvalsToInTime.trans binaryCompareMachine.step (1 + 1)
              (2 * right.length + 0 + 2) c₀ c₂
              (some
                (binaryCompareCfg
                  (some (BinaryCompareLabel.write
                    (binaryNatSuccLeBitsAux [] right next.1 next.2)))
                  (BinaryCompareVar.bit none) [] output leftRev []))
              h₁₂ hTail
      | cons leftBit left =>
          let next := binarySuccLeStep carry borrow leftBit rightBit
          let c₀ := binaryCompareCfg (some (BinaryCompareLabel.readRight carry borrow)) var
            (binaryCompareRightSymbol rightBit :: right.map binaryCompareRightSymbol)
            output leftRev (leftBit :: left)
          let c₁ := binaryCompareCfg
            (some (BinaryCompareLabel.popLeftForRight carry borrow rightBit))
            (BinaryCompareVar.input (some (binaryCompareRightSymbol rightBit)))
            (right.map binaryCompareRightSymbol) output leftRev (leftBit :: left)
          let c₂ := binaryCompareCfg (some (BinaryCompareLabel.readRight next.1 next.2))
            (BinaryCompareVar.bit (some leftBit)) (right.map binaryCompareRightSymbol)
            output leftRev left
          have h₁ : StateTransition.EvalsToInTime binaryCompareMachine.step c₀ (some c₁) 1 :=
            evalsToInTimeOne
              (binaryCompare_readRight_bit_step carry borrow rightBit var
                (right.map binaryCompareRightSymbol) output leftRev (leftBit :: left))
          have h₂ : StateTransition.EvalsToInTime binaryCompareMachine.step c₁ (some c₂) 1 :=
            evalsToInTimeOne
              (binaryCompare_popLeftForRight_bit_step carry borrow rightBit leftBit
                (BinaryCompareVar.input (some (binaryCompareRightSymbol rightBit)))
                (right.map binaryCompareRightSymbol) output leftRev left)
          have h₁₂ : StateTransition.EvalsToInTime binaryCompareMachine.step c₀ (some c₂)
              (1 + 1) :=
            StateTransition.EvalsToInTime.trans binaryCompareMachine.step 1 1 c₀ c₁
              (some c₂) h₁ h₂
          have hTail := ih next.1 next.2 (BinaryCompareVar.bit (some leftBit)) left
          have hTrans :
              StateTransition.EvalsToInTime binaryCompareMachine.step c₀
              (some
                (binaryCompareCfg
                  (some (BinaryCompareLabel.write
                    (binaryNatSuccLeBitsAux left right next.1 next.2)))
                  (BinaryCompareVar.bit none) [] output leftRev []))
                (2 * right.length + left.length + 4) := by
            refine evalsToInTime_mono
              (StateTransition.EvalsToInTime.trans binaryCompareMachine.step (1 + 1)
                (2 * right.length + left.length + 2) c₀ c₂
                (some
                  (binaryCompareCfg
                    (some (BinaryCompareLabel.write
                      (binaryNatSuccLeBitsAux left right next.1 next.2)))
                    (BinaryCompareVar.bit none) [] output leftRev []))
                h₁₂ ?_) ?_
            · simpa [c₂] using hTail
            · omega
          exact
            evalsToInTime_mono (by
              simpa [c₀, c₁, c₂, next, binaryNatSuccLeBitsAux,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hTrans) (by
              simp
              omega)

noncomputable def binaryCompareMachine_outputs (left right : List Bool) :
    Turing.TM2OutputsInTime binaryCompareMachine
      (left.map binaryCompareLeftSymbol ++ none :: right.map binaryCompareRightSymbol)
      (some (EncodedType.bool.encode (binaryNatSuccLeBits left right)))
      ((10 * Polynomial.X + 20).eval
        (left.map binaryCompareLeftSymbol ++ none :: right.map binaryCompareRightSymbol).length) := by
  let input := left.map binaryCompareLeftSymbol ++ none :: right.map binaryCompareRightSymbol
  let cReadLeft := binaryCompareCfg (some (BinaryCompareLabel.readLeft true false))
    BinaryCompareVar.unit input [] [] []
  let cMove := binaryCompareCfg (some (BinaryCompareLabel.moveLeft true false))
    (BinaryCompareVar.input (some none)) (right.map binaryCompareRightSymbol) []
    left.reverse []
  let cReadRight := binaryCompareCfg (some (BinaryCompareLabel.readRight true false))
    (BinaryCompareVar.bit none) (right.map binaryCompareRightSymbol) [] [] left
  let cWrite := binaryCompareCfg (some (BinaryCompareLabel.write (binaryNatSuccLeBits left right)))
    (BinaryCompareVar.bit none) [] [] [] []
  let cHalt := binaryCompareCfg none BinaryCompareVar.unit []
    (EncodedType.bool.encode (binaryNatSuccLeBits left right)) [] []
  have hRead : StateTransition.EvalsToInTime binaryCompareMachine.step
      (Turing.initList binaryCompareMachine input) (some cMove) (2 * left.length + 1) := by
    rw [binaryCompare_initList]
    simpa [input, cMove] using
      binaryCompare_readLeft_run true false BinaryCompareVar.unit left
        (right.map binaryCompareRightSymbol) [] [] []
  have hMove : StateTransition.EvalsToInTime binaryCompareMachine.step
      cMove (some cReadRight) (2 * left.length + 1) := by
    simpa [cMove, cReadRight, List.length_reverse] using
      binaryCompare_moveLeft_run true false (BinaryCompareVar.input (some none))
        (right.map binaryCompareRightSymbol) [] left.reverse []
  have hRight : StateTransition.EvalsToInTime binaryCompareMachine.step
      cReadRight (some cWrite) (2 * right.length + left.length + 2) := by
    simpa [cReadRight, cWrite, binaryNatSuccLeBits] using
      binaryCompare_readRight_run true false (BinaryCompareVar.bit none) left right [] []
  have hWrite : StateTransition.EvalsToInTime binaryCompareMachine.step
      cWrite (some cHalt) 1 := by
    simpa [cWrite, cHalt, EncodedType.bool] using
      evalsToInTimeOne
        (binaryCompare_write_step (binaryNatSuccLeBits left right) (BinaryCompareVar.bit none)
          [] [] [])
  have hReadMove : StateTransition.EvalsToInTime binaryCompareMachine.step
      (Turing.initList binaryCompareMachine input) (some cReadRight)
      ((2 * left.length + 1) + (2 * left.length + 1)) :=
    evalsToInTime_mono
      (StateTransition.EvalsToInTime.trans binaryCompareMachine.step
        (2 * left.length + 1) (2 * left.length + 1)
        (Turing.initList binaryCompareMachine input) cMove (some cReadRight) hRead hMove)
      (by omega)
  have hToWrite : StateTransition.EvalsToInTime binaryCompareMachine.step
      (Turing.initList binaryCompareMachine input) (some cWrite)
      ((2 * right.length + left.length + 2) +
        ((2 * left.length + 1) + (2 * left.length + 1))) :=
    StateTransition.EvalsToInTime.trans binaryCompareMachine.step
      ((2 * left.length + 1) + (2 * left.length + 1))
      (2 * right.length + left.length + 2)
      (Turing.initList binaryCompareMachine input) cReadRight (some cWrite)
      hReadMove hRight
  have hAll : StateTransition.EvalsToInTime binaryCompareMachine.step
      (Turing.initList binaryCompareMachine input) (some cHalt)
      (1 + ((2 * right.length + left.length + 2) +
        ((2 * left.length + 1) + (2 * left.length + 1)))) :=
    StateTransition.EvalsToInTime.trans binaryCompareMachine.step
      ((2 * right.length + left.length + 2) +
        ((2 * left.length + 1) + (2 * left.length + 1)))
      1
      (Turing.initList binaryCompareMachine input) cWrite (some cHalt)
      hToWrite hWrite
  unfold Turing.TM2OutputsInTime
  change StateTransition.EvalsToInTime binaryCompareMachine.step
    (Turing.initList binaryCompareMachine input)
    (some (Turing.haltList binaryCompareMachine
      (EncodedType.bool.encode (binaryNatSuccLeBits left right))))
    ((10 * Polynomial.X + 20).eval input.length)
  rw [binaryCompare_haltList]
  refine evalsToInTime_mono (by simpa [cHalt, EncodedType.bool] using hAll) ?_
  simp [input, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
  omega

noncomputable def binaryNatSuccLeBoolComputableInPolyTime :
    Turing.TM2ComputableInPolyTime
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat).encode
      EncodedType.bool.encode
      binaryNatSuccLeBool where
  tm := binaryCompareMachine
  inputAlphabet := Equiv.refl (Option (Bool ⊕ Bool))
  outputAlphabet := Equiv.refl Bool
  time := 10 * Polynomial.X + 20
  outputsFun p := by
    rcases p with ⟨m, n⟩
    have h :=
      binaryCompareMachine_outputs
        (EncodedType.binaryNat.encode m)
        (EncodedType.binaryNat.encode n)
    unfold Turing.TM2OutputsInTime at h ⊢
    simpa [EncodedType.prod, binaryCompareLeftSymbol, binaryCompareRightSymbol,
      binaryNatSuccLeBits_encode_eq (m, n)] using h

theorem binaryNatSuccLeBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      EncodedType.bool
      binaryNatSuccLeBool :=
  ⟨binaryNatSuccLeBoolComputableInPolyTime⟩

theorem intNatAddNonnegativeBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.binaryInt EncodedType.binaryNat)
      EncodedType.bool
      intNatAddNonnegativeBool :=
  intNatAddNonnegativeBool_tm_polytime_of_binaryNatSuccLe_witness
    binaryNatSuccLeBool_tm_polytime

end Knapsack
end Karp21
end ComplexityReduction
