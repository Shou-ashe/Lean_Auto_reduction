/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.SeqComp

namespace ComplexityReduction
namespace TM2Programs

open Turing.TM2.Stmt

/-- Stack indices for the product-diagonal program. -/
inductive ProdDiagStack where
  | input
  | output
  | leftTemp
  | rightTemp
  deriving DecidableEq, Fintype

/-- Stack alphabets for the product-diagonal program. -/
abbrev prodDiagAlphabet (α : Type) : ProdDiagStack → Type
  | ProdDiagStack.input => α
  | ProdDiagStack.output => Option (α ⊕ α)
  | ProdDiagStack.leftTemp => α
  | ProdDiagStack.rightTemp => α

/-- Control labels for the product-diagonal program. -/
inductive ProdDiagLabel (α : Type) where
  | readInput
  | pushLeft (a : α)
  | pushRight (a : α)
  | moveRight
  | pushRightOutput (a : α)
  | writeDelimiter
  | moveLeft
  | pushLeftOutput (a : α)
  deriving DecidableEq, Fintype

/--
A concrete TM2 program for duplicating an encoded input into a product encoding:
`input ↦ input.map inl ++ [delimiter] ++ input.map inr`.
-/
def prodDiagMachine (α : Type) [Fintype α] : Turing.FinTM2 where
  K := ProdDiagStack
  k₀ := ProdDiagStack.input
  k₁ := ProdDiagStack.output
  Γ := prodDiagAlphabet α
  Λ := ProdDiagLabel α
  main := ProdDiagLabel.readInput
  σ := Option α
  initialState := none
  Γk₀Fin := by
    dsimp [prodDiagAlphabet]
    infer_instance
  m
    | ProdDiagLabel.readInput =>
        pop ProdDiagStack.input (fun _ head => head)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some a => ProdDiagLabel.pushLeft a
              | none => ProdDiagLabel.moveRight)
            (goto fun _ => ProdDiagLabel.moveRight))
    | ProdDiagLabel.pushLeft a =>
        push ProdDiagStack.leftTemp (fun _ => a) (goto fun _ => ProdDiagLabel.pushRight a)
    | ProdDiagLabel.pushRight a =>
        push ProdDiagStack.rightTemp (fun _ => a) (goto fun _ => ProdDiagLabel.readInput)
    | ProdDiagLabel.moveRight =>
        pop ProdDiagStack.rightTemp (fun _ head => head)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some a => ProdDiagLabel.pushRightOutput a
              | none => ProdDiagLabel.writeDelimiter)
            (goto fun _ => ProdDiagLabel.writeDelimiter))
    | ProdDiagLabel.pushRightOutput a =>
        push ProdDiagStack.output (fun _ => some (Sum.inr a))
          (goto fun _ => ProdDiagLabel.moveRight)
    | ProdDiagLabel.writeDelimiter =>
        push ProdDiagStack.output (fun _ => none) (goto fun _ => ProdDiagLabel.moveLeft)
    | ProdDiagLabel.moveLeft =>
        pop ProdDiagStack.leftTemp (fun _ head => head)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some a => ProdDiagLabel.pushLeftOutput a
              | none => ProdDiagLabel.moveLeft)
            (load (fun _ => none) halt))
    | ProdDiagLabel.pushLeftOutput a =>
        push ProdDiagStack.output (fun _ => some (Sum.inl a))
          (goto fun _ => ProdDiagLabel.moveLeft)

def prodDiagCfg (α : Type) [Fintype α]
    (label : ProdDiagLabel α) (state : Option α)
    (input : List α) (output : List (Option (α ⊕ α)))
    (leftTemp rightTemp : List α) :
    (prodDiagMachine α).Cfg where
  l := some label
  var := state
  stk
    | ProdDiagStack.input => input
    | ProdDiagStack.output => output
    | ProdDiagStack.leftTemp => leftTemp
    | ProdDiagStack.rightTemp => rightTemp

def prodDiagHalt (α : Type) [Fintype α] (output : List (Option (α ⊕ α))) :
    (prodDiagMachine α).Cfg where
  l := none
  var := none
  stk
    | ProdDiagStack.input => []
    | ProdDiagStack.output => output
    | ProdDiagStack.leftTemp => []
    | ProdDiagStack.rightTemp => []

lemma prodDiag_readInput_step_cons (α : Type) [Fintype α] (state : Option α)
    (a : α) (input : List α) (output : List (Option (α ⊕ α)))
    (leftTemp rightTemp : List α) :
    (prodDiagMachine α).step
        (prodDiagCfg α ProdDiagLabel.readInput state (a :: input) output leftTemp rightTemp) =
      some (prodDiagCfg α (ProdDiagLabel.pushLeft a) (some a)
        input output leftTemp rightTemp) := by
  simp [prodDiagMachine, prodDiagCfg]
  congr
  funext k
  cases k <;> rfl

lemma prodDiag_readInput_step_nil (α : Type) [Fintype α] (state : Option α)
    (output : List (Option (α ⊕ α))) (leftTemp rightTemp : List α) :
    (prodDiagMachine α).step
        (prodDiagCfg α ProdDiagLabel.readInput state [] output leftTemp rightTemp) =
      some (prodDiagCfg α ProdDiagLabel.moveRight none [] output leftTemp rightTemp) := by
  simp [prodDiagMachine, prodDiagCfg]
  congr

lemma prodDiag_pushLeft_step (α : Type) [Fintype α] (state : Option α)
    (a : α) (input : List α) (output : List (Option (α ⊕ α)))
    (leftTemp rightTemp : List α) :
    (prodDiagMachine α).step
        (prodDiagCfg α (ProdDiagLabel.pushLeft a) state input output leftTemp rightTemp) =
      some (prodDiagCfg α (ProdDiagLabel.pushRight a) state input output
        (a :: leftTemp) rightTemp) := by
  simp [prodDiagMachine, prodDiagCfg]
  congr
  funext k
  cases k <;> rfl

lemma prodDiag_pushRight_step (α : Type) [Fintype α] (state : Option α)
    (a : α) (input : List α) (output : List (Option (α ⊕ α)))
    (leftTemp rightTemp : List α) :
    (prodDiagMachine α).step
        (prodDiagCfg α (ProdDiagLabel.pushRight a) state input output leftTemp rightTemp) =
      some (prodDiagCfg α ProdDiagLabel.readInput state input output
        leftTemp (a :: rightTemp)) := by
  simp [prodDiagMachine, prodDiagCfg]
  congr
  funext k
  cases k <;> rfl

lemma prodDiag_moveRight_step_cons (α : Type) [Fintype α] (state : Option α)
    (output : List (Option (α ⊕ α))) (leftTemp : List α) (a : α) (rightTemp : List α) :
    (prodDiagMachine α).step
        (prodDiagCfg α ProdDiagLabel.moveRight state [] output leftTemp (a :: rightTemp)) =
      some (prodDiagCfg α (ProdDiagLabel.pushRightOutput a) (some a)
        [] output leftTemp rightTemp) := by
  simp [prodDiagMachine, prodDiagCfg]
  congr
  funext k
  cases k <;> rfl

lemma prodDiag_moveRight_step_nil (α : Type) [Fintype α] (state : Option α)
    (output : List (Option (α ⊕ α))) (leftTemp : List α) :
    (prodDiagMachine α).step
        (prodDiagCfg α ProdDiagLabel.moveRight state [] output leftTemp []) =
      some (prodDiagCfg α ProdDiagLabel.writeDelimiter none [] output leftTemp []) := by
  simp [prodDiagMachine, prodDiagCfg]
  congr

lemma prodDiag_pushRightOutput_step (α : Type) [Fintype α] (state : Option α)
    (a : α) (output : List (Option (α ⊕ α))) (leftTemp rightTemp : List α) :
    (prodDiagMachine α).step
        (prodDiagCfg α (ProdDiagLabel.pushRightOutput a) state [] output leftTemp rightTemp) =
      some (prodDiagCfg α ProdDiagLabel.moveRight state []
        (some (Sum.inr a) :: output) leftTemp rightTemp) := by
  simp [prodDiagMachine, prodDiagCfg]
  congr
  funext k
  cases k <;> rfl

lemma prodDiag_writeDelimiter_step (α : Type) [Fintype α] (state : Option α)
    (output : List (Option (α ⊕ α))) (leftTemp : List α) :
    (prodDiagMachine α).step
        (prodDiagCfg α ProdDiagLabel.writeDelimiter state [] output leftTemp []) =
      some (prodDiagCfg α ProdDiagLabel.moveLeft state [] (none :: output) leftTemp []) := by
  simp [prodDiagMachine, prodDiagCfg]
  congr
  funext k
  cases k <;> rfl

lemma prodDiag_moveLeft_step_cons (α : Type) [Fintype α] (state : Option α)
    (output : List (Option (α ⊕ α))) (a : α) (leftTemp : List α) :
    (prodDiagMachine α).step
        (prodDiagCfg α ProdDiagLabel.moveLeft state [] output (a :: leftTemp) []) =
      some (prodDiagCfg α (ProdDiagLabel.pushLeftOutput a) (some a)
        [] output leftTemp []) := by
  simp [prodDiagMachine, prodDiagCfg]
  congr
  funext k
  cases k <;> rfl

lemma prodDiag_moveLeft_step_nil (α : Type) [Fintype α] (state : Option α)
    (output : List (Option (α ⊕ α))) :
    (prodDiagMachine α).step
        (prodDiagCfg α ProdDiagLabel.moveLeft state [] output [] []) =
      some (prodDiagHalt α output) := by
  simp [prodDiagMachine, prodDiagCfg, prodDiagHalt]
  congr

lemma prodDiag_pushLeftOutput_step (α : Type) [Fintype α] (state : Option α)
    (a : α) (output : List (Option (α ⊕ α))) (leftTemp : List α) :
    (prodDiagMachine α).step
        (prodDiagCfg α (ProdDiagLabel.pushLeftOutput a) state [] output leftTemp []) =
      some (prodDiagCfg α ProdDiagLabel.moveLeft state []
        (some (Sum.inl a) :: output) leftTemp []) := by
  simp [prodDiagMachine, prodDiagCfg]
  congr
  funext k
  cases k <;> rfl

lemma initList_prodDiagMachine (α : Type) [Fintype α] (input : List α) :
    Turing.initList (prodDiagMachine α) input =
      prodDiagCfg α ProdDiagLabel.readInput none input [] [] [] := by
  simp [prodDiagMachine, prodDiagCfg, Turing.initList]
  congr
  funext k
  cases k <;> rfl

lemma haltList_prodDiagMachine (α : Type) [Fintype α] (output : List (Option (α ⊕ α))) :
    Turing.haltList (prodDiagMachine α) output =
      prodDiagHalt α output := by
  simp [prodDiagMachine, prodDiagHalt, Turing.haltList]
  congr
  funext k
  cases k <;> rfl

def prodDiag_readInput_run (α : Type) [Fintype α] (state : Option α)
    (input : List α) (output : List (Option (α ⊕ α)))
    (leftTemp rightTemp : List α) :
    StateTransition.EvalsToInTime (prodDiagMachine α).step
      (prodDiagCfg α ProdDiagLabel.readInput state input output leftTemp rightTemp)
      (some (prodDiagCfg α ProdDiagLabel.moveRight none [] output
        (input.reverse ++ leftTemp) (input.reverse ++ rightTemp)))
      (3 * input.length + 1) := by
  induction input generalizing state leftTemp rightTemp with
  | nil =>
      simpa using
        evalsToInTimeOne
          (prodDiag_readInput_step_nil α state output leftTemp rightTemp)
  | cons a input ih =>
      let tm := prodDiagMachine α
      let c₀ := prodDiagCfg α ProdDiagLabel.readInput state (a :: input) output
        leftTemp rightTemp
      let c₁ := prodDiagCfg α (ProdDiagLabel.pushLeft a) (some a) input output
        leftTemp rightTemp
      let c₂ := prodDiagCfg α (ProdDiagLabel.pushRight a) (some a) input output
        (a :: leftTemp) rightTemp
      let c₃ := prodDiagCfg α ProdDiagLabel.readInput (some a) input output
        (a :: leftTemp) (a :: rightTemp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (prodDiag_readInput_step_cons α state a input output leftTemp rightTemp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (prodDiag_pushLeft_step α (some a) a input output leftTemp rightTemp)
      have h₃ : StateTransition.EvalsToInTime tm.step c₂ (some c₃) 1 :=
        evalsToInTimeOne
          (prodDiag_pushRight_step α (some a) a input output (a :: leftTemp) rightTemp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have h₁₂₃ : StateTransition.EvalsToInTime tm.step c₀ (some c₃) (1 + (1 + 1)) :=
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) 1 c₀ c₂ (some c₃) h₁₂ h₃
      have hTail : StateTransition.EvalsToInTime tm.step c₃
          (some (prodDiagCfg α ProdDiagLabel.moveRight none [] output
            (input.reverse ++ (a :: leftTemp)) (input.reverse ++ (a :: rightTemp))))
          (3 * input.length + 1) :=
        ih (some a) (a :: leftTemp) (a :: rightTemp)
      simpa [tm, c₀, c₁, c₂, c₃, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + (1 + 1))
          (3 * input.length + 1) c₀ c₃
          (some (prodDiagCfg α ProdDiagLabel.moveRight none [] output
            (input.reverse ++ (a :: leftTemp)) (input.reverse ++ (a :: rightTemp))))
          h₁₂₃ hTail

def prodDiag_moveRight_run (α : Type) [Fintype α] (state : Option α)
    (output : List (Option (α ⊕ α))) (leftTemp rightTemp : List α) :
    StateTransition.EvalsToInTime (prodDiagMachine α).step
      (prodDiagCfg α ProdDiagLabel.moveRight state [] output leftTemp rightTemp)
      (some (prodDiagCfg α ProdDiagLabel.writeDelimiter none []
        ((rightTemp.reverse.map fun a => some (Sum.inr a)) ++ output) leftTemp []))
      (2 * rightTemp.length + 1) := by
  induction rightTemp generalizing state output with
  | nil =>
      simpa using
        evalsToInTimeOne
          (prodDiag_moveRight_step_nil α state output leftTemp)
  | cons a rightTemp ih =>
      let tm := prodDiagMachine α
      let c₀ := prodDiagCfg α ProdDiagLabel.moveRight state [] output leftTemp
        (a :: rightTemp)
      let c₁ := prodDiagCfg α (ProdDiagLabel.pushRightOutput a) (some a) []
        output leftTemp rightTemp
      let c₂ := prodDiagCfg α ProdDiagLabel.moveRight (some a) []
        (some (Sum.inr a) :: output) leftTemp rightTemp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (prodDiag_moveRight_step_cons α state output leftTemp a rightTemp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (prodDiag_pushRightOutput_step α (some a) a output leftTemp rightTemp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (prodDiagCfg α ProdDiagLabel.writeDelimiter none []
            ((rightTemp.reverse.map fun a => some (Sum.inr a)) ++
              (some (Sum.inr a) :: output)) leftTemp []))
          (2 * rightTemp.length + 1) :=
        ih (some a) (some (Sum.inr a) :: output)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.map_append, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1)
          (2 * rightTemp.length + 1) c₀ c₂
          (some (prodDiagCfg α ProdDiagLabel.writeDelimiter none []
            ((rightTemp.reverse.map fun a => some (Sum.inr a)) ++
              (some (Sum.inr a) :: output)) leftTemp []))
          h₁₂ hTail

def prodDiag_writeDelimiter_run (α : Type) [Fintype α] (state : Option α)
    (output : List (Option (α ⊕ α))) (leftTemp : List α) :
    StateTransition.EvalsToInTime (prodDiagMachine α).step
      (prodDiagCfg α ProdDiagLabel.writeDelimiter state [] output leftTemp [])
      (some (prodDiagCfg α ProdDiagLabel.moveLeft state [] (none :: output) leftTemp [])) 1 :=
  evalsToInTimeOne (prodDiag_writeDelimiter_step α state output leftTemp)

def prodDiag_moveLeft_run (α : Type) [Fintype α] (state : Option α)
    (output : List (Option (α ⊕ α))) (leftTemp : List α) :
    StateTransition.EvalsToInTime (prodDiagMachine α).step
      (prodDiagCfg α ProdDiagLabel.moveLeft state [] output leftTemp [])
      (some (prodDiagHalt α ((leftTemp.reverse.map fun a => some (Sum.inl a)) ++ output)))
      (2 * leftTemp.length + 1) := by
  induction leftTemp generalizing state output with
  | nil =>
      simpa using
        evalsToInTimeOne
          (prodDiag_moveLeft_step_nil α state output)
  | cons a leftTemp ih =>
      let tm := prodDiagMachine α
      let c₀ := prodDiagCfg α ProdDiagLabel.moveLeft state [] output (a :: leftTemp) []
      let c₁ := prodDiagCfg α (ProdDiagLabel.pushLeftOutput a) (some a) []
        output leftTemp []
      let c₂ := prodDiagCfg α ProdDiagLabel.moveLeft (some a) []
        (some (Sum.inl a) :: output) leftTemp []
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (prodDiag_moveLeft_step_cons α state output a leftTemp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (prodDiag_pushLeftOutput_step α (some a) a output leftTemp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (prodDiagHalt α
            ((leftTemp.reverse.map fun a => some (Sum.inl a)) ++
              (some (Sum.inl a) :: output))))
          (2 * leftTemp.length + 1) :=
        ih (some a) (some (Sum.inl a) :: output)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.map_append, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1)
          (2 * leftTemp.length + 1) c₀ c₂
          (some (prodDiagHalt α
            ((leftTemp.reverse.map fun a => some (Sum.inl a)) ++
              (some (Sum.inl a) :: output))))
          h₁₂ hTail

/-- The product-diagonal program computes `input ↦ (input, input)` with a delimiter. -/
def prodDiag_outputs (α : Type) [Fintype α] (input : List α) :
    Turing.TM2OutputsInTime (prodDiagMachine α)
      input
      (some
        (input.map (fun a => some (Sum.inl a : α ⊕ α)) ++
          [none] ++
          input.map (fun a => some (Sum.inr a : α ⊕ α))))
      (7 * input.length + 4) := by
  let tm := prodDiagMachine α
  let left := input.map (fun a => some (Sum.inl a : α ⊕ α))
  let right := input.map (fun a => some (Sum.inr a : α ⊕ α))
  let mid₁ := prodDiagCfg α ProdDiagLabel.moveRight none [] [] input.reverse input.reverse
  let mid₂ := prodDiagCfg α ProdDiagLabel.writeDelimiter none [] right input.reverse []
  let mid₃ := prodDiagCfg α ProdDiagLabel.moveLeft none [] (none :: right) input.reverse []
  let done := prodDiagHalt α (left ++ [none] ++ right)
  have hRead : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some mid₁) (3 * input.length + 1) := by
    simpa [tm, mid₁, initList_prodDiagMachine] using
      prodDiag_readInput_run α none input [] [] []
  have hRight : StateTransition.EvalsToInTime tm.step mid₁
      (some mid₂) (2 * input.length + 1) := by
    simpa [tm, mid₁, mid₂, right, List.length_reverse] using
      prodDiag_moveRight_run α none [] input.reverse input.reverse
  have hDelim : StateTransition.EvalsToInTime tm.step mid₂ (some mid₃) 1 := by
    simpa [tm, mid₂, mid₃] using
      prodDiag_writeDelimiter_run α none right input.reverse
  have hLeft : StateTransition.EvalsToInTime tm.step mid₃
      (some done) (2 * input.length + 1) := by
    simpa [tm, mid₃, done, left, right, List.length_reverse, List.append_assoc] using
      prodDiag_moveLeft_run α none (none :: right) input.reverse
  have hReadRight : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some mid₂) ((2 * input.length + 1) + (3 * input.length + 1)) :=
    StateTransition.EvalsToInTime.trans tm.step (3 * input.length + 1)
      (2 * input.length + 1) (Turing.initList tm input) mid₁ (some mid₂)
      hRead hRight
  have hReadRightDelim : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some mid₃) (1 + ((2 * input.length + 1) + (3 * input.length + 1))) :=
    StateTransition.EvalsToInTime.trans tm.step
      ((2 * input.length + 1) + (3 * input.length + 1)) 1
      (Turing.initList tm input) mid₂ (some mid₃) hReadRight hDelim
  have hAll : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some done)
      ((2 * input.length + 1) +
        (1 + ((2 * input.length + 1) + (3 * input.length + 1)))) :=
    StateTransition.EvalsToInTime.trans tm.step
      (1 + ((2 * input.length + 1) + (3 * input.length + 1)))
      (2 * input.length + 1)
      (Turing.initList tm input) mid₃ (some done) hReadRightDelim hLeft
  change StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
    (some (Turing.haltList tm (left ++ [none] ++ right))) (7 * input.length + 4)
  rw [haltList_prodDiagMachine]
  convert hAll using 1
  omega

/--
TM2 polynomial-time computation of the structural product map `x ↦ (x, x)`.

This is a direct `prod_mk` structural subcase: it duplicates the input encoding
into left- and right-tagged copies separated by the product delimiter.
-/
noncomputable def prodDiagComputableInPolyTime (X : EncodedType) :
    Turing.TM2ComputableInPolyTime X.encode (EncodedType.prod X X).encode
      (fun x : X.Carrier => (x, x)) where
  tm := prodDiagMachine X.Symbol
  inputAlphabet := Equiv.refl X.Symbol
  outputAlphabet := Equiv.refl (Option (X.Symbol ⊕ X.Symbol))
  time := 7 * Polynomial.X + 4
  outputsFun x := by
    convert prodDiag_outputs X.Symbol (X.encode x) using 1
    · change List.map id (X.encode x) = X.encode x
      simp
    · change
        some (List.map id ((EncodedType.prod X X).encode (x, x))) =
          some
            (
          (X.encode x).map (fun s : X.Symbol => some (Sum.inl s : X.Symbol ⊕ X.Symbol)) ++
            [none] ++
            (X.encode x).map (fun s : X.Symbol => some (Sum.inr s : X.Symbol ⊕ X.Symbol)))
      simp [EncodedType.prod]
    · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]

/-- Stack indices for the product symbol-map program. -/
inductive ProdSymbolMapsStack where
  | input
  | output
  | leftTemp
  | rightTemp
  deriving DecidableEq, Fintype

/-- Stack alphabets for the product symbol-map program. -/
abbrev prodSymbolMapsAlphabet (α β γ : Type) : ProdSymbolMapsStack → Type
  | ProdSymbolMapsStack.input => α
  | ProdSymbolMapsStack.output => Option (β ⊕ γ)
  | ProdSymbolMapsStack.leftTemp => β
  | ProdSymbolMapsStack.rightTemp => γ

/-- Control labels for the product symbol-map program. -/
inductive ProdSymbolMapsLabel (β γ : Type) where
  | readInput
  | pushLeft (b : β) (c : γ)
  | pushRight (c : γ)
  | moveRight
  | pushRightOutput (c : γ)
  | writeDelimiter
  | moveLeft
  | pushLeftOutput (b : β)
  deriving DecidableEq, Fintype

/-- Internal states for the product symbol-map program. -/
inductive ProdSymbolMapsState (β γ : Type) where
  | pair (b : β) (c : γ)
  | right (c : γ)
  | left (b : β)
  | done
  deriving DecidableEq, Fintype

namespace ProdSymbolMapsState

def isPair {β γ : Type} : ProdSymbolMapsState β γ → Bool
  | pair _ _ => true
  | _ => false

def isRight {β γ : Type} : ProdSymbolMapsState β γ → Bool
  | right _ => true
  | _ => false

def isLeft {β γ : Type} : ProdSymbolMapsState β γ → Bool
  | left _ => true
  | _ => false

end ProdSymbolMapsState

/--
A concrete TM2 program for
`input ↦ input.map (inl ∘ mapLeft) ++ [delimiter] ++ input.map (inr ∘ mapRight)`.
-/
def prodSymbolMapsMachine (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
    (mapLeft : α → β) (mapRight : α → γ) : Turing.FinTM2 where
  K := ProdSymbolMapsStack
  k₀ := ProdSymbolMapsStack.input
  k₁ := ProdSymbolMapsStack.output
  Γ := prodSymbolMapsAlphabet α β γ
  Λ := ProdSymbolMapsLabel β γ
  main := ProdSymbolMapsLabel.readInput
  σ := ProdSymbolMapsState β γ
  initialState := ProdSymbolMapsState.done
  Γk₀Fin := by
    dsimp [prodSymbolMapsAlphabet]
    infer_instance
  m
    | ProdSymbolMapsLabel.readInput =>
        pop ProdSymbolMapsStack.input
          (fun _ head =>
            match head with
            | some a => ProdSymbolMapsState.pair (mapLeft a) (mapRight a)
            | none => ProdSymbolMapsState.done)
          (branch ProdSymbolMapsState.isPair
            (goto fun state =>
              match state with
              | ProdSymbolMapsState.pair b c => ProdSymbolMapsLabel.pushLeft b c
              | _ => ProdSymbolMapsLabel.moveRight)
            (goto fun _ => ProdSymbolMapsLabel.moveRight))
    | ProdSymbolMapsLabel.pushLeft b c =>
        push ProdSymbolMapsStack.leftTemp (fun _ => b)
          (goto fun _ => ProdSymbolMapsLabel.pushRight c)
    | ProdSymbolMapsLabel.pushRight c =>
        push ProdSymbolMapsStack.rightTemp (fun _ => c)
          (goto fun _ => ProdSymbolMapsLabel.readInput)
    | ProdSymbolMapsLabel.moveRight =>
        pop ProdSymbolMapsStack.rightTemp
          (fun _ head =>
            match head with
            | some c => ProdSymbolMapsState.right c
            | none => ProdSymbolMapsState.done)
          (branch ProdSymbolMapsState.isRight
            (goto fun state =>
              match state with
              | ProdSymbolMapsState.right c => ProdSymbolMapsLabel.pushRightOutput c
              | _ => ProdSymbolMapsLabel.writeDelimiter)
            (goto fun _ => ProdSymbolMapsLabel.writeDelimiter))
    | ProdSymbolMapsLabel.pushRightOutput c =>
        push ProdSymbolMapsStack.output (fun _ => some (Sum.inr c))
          (goto fun _ => ProdSymbolMapsLabel.moveRight)
    | ProdSymbolMapsLabel.writeDelimiter =>
        push ProdSymbolMapsStack.output (fun _ => none)
          (goto fun _ => ProdSymbolMapsLabel.moveLeft)
    | ProdSymbolMapsLabel.moveLeft =>
        pop ProdSymbolMapsStack.leftTemp
          (fun _ head =>
            match head with
            | some b => ProdSymbolMapsState.left b
            | none => ProdSymbolMapsState.done)
          (branch ProdSymbolMapsState.isLeft
            (goto fun state =>
              match state with
              | ProdSymbolMapsState.left b => ProdSymbolMapsLabel.pushLeftOutput b
              | _ => ProdSymbolMapsLabel.moveLeft)
            (load (fun _ => ProdSymbolMapsState.done) halt))
    | ProdSymbolMapsLabel.pushLeftOutput b =>
        push ProdSymbolMapsStack.output (fun _ => some (Sum.inl b))
          (goto fun _ => ProdSymbolMapsLabel.moveLeft)

def prodSymbolMapsCfg (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
    (mapLeft : α → β) (mapRight : α → γ)
    (label : ProdSymbolMapsLabel β γ) (state : ProdSymbolMapsState β γ)
    (input : List α) (output : List (Option (β ⊕ γ)))
    (leftTemp : List β) (rightTemp : List γ) :
    (prodSymbolMapsMachine α β γ mapLeft mapRight).Cfg where
  l := some label
  var := state
  stk
    | ProdSymbolMapsStack.input => input
    | ProdSymbolMapsStack.output => output
    | ProdSymbolMapsStack.leftTemp => leftTemp
    | ProdSymbolMapsStack.rightTemp => rightTemp

def prodSymbolMapsHalt (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
    (mapLeft : α → β) (mapRight : α → γ) (output : List (Option (β ⊕ γ))) :
    (prodSymbolMapsMachine α β γ mapLeft mapRight).Cfg where
  l := none
  var := ProdSymbolMapsState.done
  stk
    | ProdSymbolMapsStack.input => []
    | ProdSymbolMapsStack.output => output
    | ProdSymbolMapsStack.leftTemp => []
    | ProdSymbolMapsStack.rightTemp => []

lemma prodSymbolMaps_readInput_step_cons (α β γ : Type) [Fintype α] [Fintype β]
    [Fintype γ] (mapLeft : α → β) (mapRight : α → γ)
    (state : ProdSymbolMapsState β γ)
    (a : α) (input : List α) (output : List (Option (β ⊕ γ)))
    (leftTemp : List β) (rightTemp : List γ) :
    (prodSymbolMapsMachine α β γ mapLeft mapRight).step
        (prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.readInput state
          (a :: input) output leftTemp rightTemp) =
      some (prodSymbolMapsCfg α β γ mapLeft mapRight
        (ProdSymbolMapsLabel.pushLeft (mapLeft a) (mapRight a))
        (ProdSymbolMapsState.pair (mapLeft a) (mapRight a))
        input output leftTemp rightTemp) := by
  simp [prodSymbolMapsMachine, prodSymbolMapsCfg, ProdSymbolMapsState.isPair]
  congr
  funext k
  cases k <;> rfl

lemma prodSymbolMaps_readInput_step_nil (α β γ : Type) [Fintype α] [Fintype β]
    [Fintype γ] (mapLeft : α → β) (mapRight : α → γ)
    (state : ProdSymbolMapsState β γ)
    (output : List (Option (β ⊕ γ))) (leftTemp : List β) (rightTemp : List γ) :
    (prodSymbolMapsMachine α β γ mapLeft mapRight).step
        (prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.readInput state
          [] output leftTemp rightTemp) =
      some (prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.moveRight
        ProdSymbolMapsState.done [] output leftTemp rightTemp) := by
  simp [prodSymbolMapsMachine, prodSymbolMapsCfg, ProdSymbolMapsState.isPair]
  congr

lemma prodSymbolMaps_pushLeft_step (α β γ : Type) [Fintype α] [Fintype β]
    [Fintype γ] (mapLeft : α → β) (mapRight : α → γ)
    (state : ProdSymbolMapsState β γ)
    (b : β) (c : γ) (input : List α) (output : List (Option (β ⊕ γ)))
    (leftTemp : List β) (rightTemp : List γ) :
    (prodSymbolMapsMachine α β γ mapLeft mapRight).step
        (prodSymbolMapsCfg α β γ mapLeft mapRight
          (ProdSymbolMapsLabel.pushLeft b c) state input output leftTemp rightTemp) =
      some (prodSymbolMapsCfg α β γ mapLeft mapRight
        (ProdSymbolMapsLabel.pushRight c) state input output (b :: leftTemp) rightTemp) := by
  simp [prodSymbolMapsMachine, prodSymbolMapsCfg]
  congr
  funext k
  cases k <;> rfl

lemma prodSymbolMaps_pushRight_step (α β γ : Type) [Fintype α] [Fintype β]
    [Fintype γ] (mapLeft : α → β) (mapRight : α → γ)
    (state : ProdSymbolMapsState β γ)
    (c : γ) (input : List α) (output : List (Option (β ⊕ γ)))
    (leftTemp : List β) (rightTemp : List γ) :
    (prodSymbolMapsMachine α β γ mapLeft mapRight).step
        (prodSymbolMapsCfg α β γ mapLeft mapRight (ProdSymbolMapsLabel.pushRight c)
          state input output leftTemp rightTemp) =
      some (prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.readInput
        state input output leftTemp (c :: rightTemp)) := by
  simp [prodSymbolMapsMachine, prodSymbolMapsCfg]
  congr
  funext k
  cases k <;> rfl

lemma prodSymbolMaps_moveRight_step_cons (α β γ : Type) [Fintype α] [Fintype β]
    [Fintype γ] (mapLeft : α → β) (mapRight : α → γ)
    (state : ProdSymbolMapsState β γ)
    (output : List (Option (β ⊕ γ))) (leftTemp : List β) (c : γ)
    (rightTemp : List γ) :
    (prodSymbolMapsMachine α β γ mapLeft mapRight).step
        (prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.moveRight
          state [] output leftTemp (c :: rightTemp)) =
      some (prodSymbolMapsCfg α β γ mapLeft mapRight
        (ProdSymbolMapsLabel.pushRightOutput c) (ProdSymbolMapsState.right c)
        [] output leftTemp rightTemp) := by
  simp [prodSymbolMapsMachine, prodSymbolMapsCfg, ProdSymbolMapsState.isRight]
  congr
  funext k
  cases k <;> rfl

lemma prodSymbolMaps_moveRight_step_nil (α β γ : Type) [Fintype α] [Fintype β]
    [Fintype γ] (mapLeft : α → β) (mapRight : α → γ)
    (state : ProdSymbolMapsState β γ)
    (output : List (Option (β ⊕ γ))) (leftTemp : List β) :
    (prodSymbolMapsMachine α β γ mapLeft mapRight).step
        (prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.moveRight
          state [] output leftTemp []) =
      some (prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.writeDelimiter
        ProdSymbolMapsState.done [] output leftTemp []) := by
  simp [prodSymbolMapsMachine, prodSymbolMapsCfg]
  congr

lemma prodSymbolMaps_pushRightOutput_step (α β γ : Type) [Fintype α] [Fintype β]
    [Fintype γ] (mapLeft : α → β) (mapRight : α → γ)
    (state : ProdSymbolMapsState β γ)
    (c : γ) (output : List (Option (β ⊕ γ))) (leftTemp : List β)
    (rightTemp : List γ) :
    (prodSymbolMapsMachine α β γ mapLeft mapRight).step
        (prodSymbolMapsCfg α β γ mapLeft mapRight
          (ProdSymbolMapsLabel.pushRightOutput c) state [] output leftTemp rightTemp) =
      some (prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.moveRight
        state [] (some (Sum.inr c) :: output) leftTemp rightTemp) := by
  simp [prodSymbolMapsMachine, prodSymbolMapsCfg]
  congr
  funext k
  cases k <;> rfl

lemma prodSymbolMaps_writeDelimiter_step (α β γ : Type) [Fintype α] [Fintype β]
    [Fintype γ] (mapLeft : α → β) (mapRight : α → γ)
    (state : ProdSymbolMapsState β γ)
    (output : List (Option (β ⊕ γ))) (leftTemp : List β) :
    (prodSymbolMapsMachine α β γ mapLeft mapRight).step
        (prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.writeDelimiter
          state [] output leftTemp []) =
      some (prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.moveLeft
        state [] (none :: output) leftTemp []) := by
  simp [prodSymbolMapsMachine, prodSymbolMapsCfg]
  congr
  funext k
  cases k <;> rfl

lemma prodSymbolMaps_moveLeft_step_cons (α β γ : Type) [Fintype α] [Fintype β]
    [Fintype γ] (mapLeft : α → β) (mapRight : α → γ)
    (state : ProdSymbolMapsState β γ)
    (output : List (Option (β ⊕ γ))) (b : β) (leftTemp : List β) :
    (prodSymbolMapsMachine α β γ mapLeft mapRight).step
        (prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.moveLeft
          state [] output (b :: leftTemp) []) =
      some (prodSymbolMapsCfg α β γ mapLeft mapRight
        (ProdSymbolMapsLabel.pushLeftOutput b) (ProdSymbolMapsState.left b)
        [] output leftTemp []) := by
  simp [prodSymbolMapsMachine, prodSymbolMapsCfg, ProdSymbolMapsState.isLeft]
  congr
  funext k
  cases k <;> rfl

lemma prodSymbolMaps_moveLeft_step_nil (α β γ : Type) [Fintype α] [Fintype β]
    [Fintype γ] (mapLeft : α → β) (mapRight : α → γ)
    (state : ProdSymbolMapsState β γ)
    (output : List (Option (β ⊕ γ))) :
    (prodSymbolMapsMachine α β γ mapLeft mapRight).step
        (prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.moveLeft
          state [] output [] []) =
      some (prodSymbolMapsHalt α β γ mapLeft mapRight output) := by
  simp [prodSymbolMapsMachine, prodSymbolMapsCfg, prodSymbolMapsHalt]
  congr

lemma prodSymbolMaps_pushLeftOutput_step (α β γ : Type) [Fintype α] [Fintype β]
    [Fintype γ] (mapLeft : α → β) (mapRight : α → γ)
    (state : ProdSymbolMapsState β γ)
    (b : β) (output : List (Option (β ⊕ γ))) (leftTemp : List β) :
    (prodSymbolMapsMachine α β γ mapLeft mapRight).step
        (prodSymbolMapsCfg α β γ mapLeft mapRight
          (ProdSymbolMapsLabel.pushLeftOutput b) state [] output leftTemp []) =
      some (prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.moveLeft
        state [] (some (Sum.inl b) :: output) leftTemp []) := by
  simp [prodSymbolMapsMachine, prodSymbolMapsCfg]
  congr
  funext k
  cases k <;> rfl

lemma initList_prodSymbolMapsMachine (α β γ : Type) [Fintype α] [Fintype β]
    [Fintype γ] (mapLeft : α → β) (mapRight : α → γ) (input : List α) :
    Turing.initList (prodSymbolMapsMachine α β γ mapLeft mapRight) input =
      prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.readInput
        ProdSymbolMapsState.done input [] [] [] := by
  simp [prodSymbolMapsMachine, prodSymbolMapsCfg, Turing.initList]
  congr
  funext k
  cases k <;> rfl

lemma haltList_prodSymbolMapsMachine (α β γ : Type) [Fintype α] [Fintype β]
    [Fintype γ] (mapLeft : α → β) (mapRight : α → γ)
    (output : List (Option (β ⊕ γ))) :
    Turing.haltList (prodSymbolMapsMachine α β γ mapLeft mapRight) output =
      prodSymbolMapsHalt α β γ mapLeft mapRight output := by
  simp [prodSymbolMapsMachine, prodSymbolMapsHalt, Turing.haltList]
  congr
  funext k
  cases k <;> rfl

def prodSymbolMaps_readInput_run (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
    (mapLeft : α → β) (mapRight : α → γ) (state : ProdSymbolMapsState β γ)
    (input : List α) (output : List (Option (β ⊕ γ)))
    (leftTemp : List β) (rightTemp : List γ) :
    StateTransition.EvalsToInTime (prodSymbolMapsMachine α β γ mapLeft mapRight).step
      (prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.readInput
        state input output leftTemp rightTemp)
      (some (prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.moveRight
        ProdSymbolMapsState.done [] output ((input.map mapLeft).reverse ++ leftTemp)
        ((input.map mapRight).reverse ++ rightTemp)))
      (3 * input.length + 1) := by
  induction input generalizing state leftTemp rightTemp with
  | nil =>
      simpa using
        evalsToInTimeOne
          (prodSymbolMaps_readInput_step_nil α β γ mapLeft mapRight state output
            leftTemp rightTemp)
  | cons a input ih =>
      let tm := prodSymbolMapsMachine α β γ mapLeft mapRight
      let c₀ := prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.readInput
        state (a :: input) output leftTemp rightTemp
      let c₁ := prodSymbolMapsCfg α β γ mapLeft mapRight
        (ProdSymbolMapsLabel.pushLeft (mapLeft a) (mapRight a))
        (ProdSymbolMapsState.pair (mapLeft a) (mapRight a)) input output leftTemp rightTemp
      let c₂ := prodSymbolMapsCfg α β γ mapLeft mapRight
        (ProdSymbolMapsLabel.pushRight (mapRight a))
        (ProdSymbolMapsState.pair (mapLeft a) (mapRight a)) input output
        (mapLeft a :: leftTemp) rightTemp
      let c₃ := prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.readInput
        (ProdSymbolMapsState.pair (mapLeft a) (mapRight a)) input output
        (mapLeft a :: leftTemp)
        (mapRight a :: rightTemp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (prodSymbolMaps_readInput_step_cons α β γ mapLeft mapRight state a input
            output leftTemp rightTemp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (prodSymbolMaps_pushLeft_step α β γ mapLeft mapRight
            (ProdSymbolMapsState.pair (mapLeft a) (mapRight a)) (mapLeft a) (mapRight a)
            input output leftTemp rightTemp)
      have h₃ : StateTransition.EvalsToInTime tm.step c₂ (some c₃) 1 :=
        evalsToInTimeOne
          (prodSymbolMaps_pushRight_step α β γ mapLeft mapRight
            (ProdSymbolMapsState.pair (mapLeft a) (mapRight a)) (mapRight a) input output
            (mapLeft a :: leftTemp) rightTemp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have h₁₂₃ : StateTransition.EvalsToInTime tm.step c₀ (some c₃) (1 + (1 + 1)) :=
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) 1 c₀ c₂ (some c₃) h₁₂ h₃
      have hTail : StateTransition.EvalsToInTime tm.step c₃
          (some (prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.moveRight
            ProdSymbolMapsState.done [] output
            ((input.map mapLeft).reverse ++ (mapLeft a :: leftTemp))
            ((input.map mapRight).reverse ++ (mapRight a :: rightTemp))))
          (3 * input.length + 1) :=
        ih (ProdSymbolMapsState.pair (mapLeft a) (mapRight a)) (mapLeft a :: leftTemp)
          (mapRight a :: rightTemp)
      simpa [tm, c₀, c₁, c₂, c₃, List.map_cons, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + (1 + 1))
          (3 * input.length + 1) c₀ c₃
          (some (prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.moveRight
            ProdSymbolMapsState.done [] output
            ((input.map mapLeft).reverse ++ (mapLeft a :: leftTemp))
            ((input.map mapRight).reverse ++ (mapRight a :: rightTemp))))
          h₁₂₃ hTail

end TM2Programs
end ComplexityReduction
