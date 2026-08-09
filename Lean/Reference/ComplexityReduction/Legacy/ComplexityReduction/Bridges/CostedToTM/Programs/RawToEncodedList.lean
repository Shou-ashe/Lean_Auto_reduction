import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.Base

namespace ComplexityReduction
namespace TM2Programs

open Turing.TM2.Stmt

/-!
Finite-state transducer from a raw symbol stream to the delimiter encoding of
the corresponding list of singleton-encoded symbols.
-/

inductive RawToEncodedListStack where
  | input
  | output
  | temp
  deriving DecidableEq, Fintype

abbrev rawToEncodedListAlphabet (α : Type) : RawToEncodedListStack → Type
  | RawToEncodedListStack.input => α
  | RawToEncodedListStack.output => Option α
  | RawToEncodedListStack.temp => Option α

inductive RawToEncodedListLabel (α : Type) where
  | readInput
  | pushSome (a : α)
  | pushNone
  | moveTemp
  | pushOutput (b : Option α)
  deriving DecidableEq, Fintype

def rawToEncodedListMachine (α : Type) [Fintype α] : Turing.FinTM2 where
  K := RawToEncodedListStack
  k₀ := RawToEncodedListStack.input
  k₁ := RawToEncodedListStack.output
  Γ := rawToEncodedListAlphabet α
  Λ := RawToEncodedListLabel α
  main := RawToEncodedListLabel.readInput
  σ := Option (Option α)
  initialState := none
  Γk₀Fin := by
    dsimp [rawToEncodedListAlphabet]
    infer_instance
  m
    | RawToEncodedListLabel.readInput =>
        pop RawToEncodedListStack.input (fun _ head => head.map some)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some (some a) => RawToEncodedListLabel.pushSome a
              | _ => RawToEncodedListLabel.moveTemp)
            (goto fun _ => RawToEncodedListLabel.moveTemp))
    | RawToEncodedListLabel.pushSome a =>
        push RawToEncodedListStack.temp (fun _ => some a)
          (goto fun _ => RawToEncodedListLabel.pushNone)
    | RawToEncodedListLabel.pushNone =>
        push RawToEncodedListStack.temp (fun _ => none)
          (goto fun _ => RawToEncodedListLabel.readInput)
    | RawToEncodedListLabel.moveTemp =>
        pop RawToEncodedListStack.temp (fun _ head => head)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some b => RawToEncodedListLabel.pushOutput b
              | none => RawToEncodedListLabel.moveTemp)
            (load (fun _ => none) halt))
    | RawToEncodedListLabel.pushOutput b =>
        push RawToEncodedListStack.output (fun _ => b)
          (goto fun _ => RawToEncodedListLabel.moveTemp)

def rawToEncodedListBlock {α : Type} (a : α) : List (Option α) :=
  [some a, none]

def rawToEncodedListOutput {α : Type} (input : List α) : List (Option α) :=
  input.flatMap rawToEncodedListBlock

def rawToEncodedListCfg (α : Type) [Fintype α]
    (label : RawToEncodedListLabel α) (state : Option (Option α))
    (input : List α) (output temp : List (Option α)) :
    (rawToEncodedListMachine α).Cfg where
  l := some label
  var := state
  stk
    | RawToEncodedListStack.input => input
    | RawToEncodedListStack.output => output
    | RawToEncodedListStack.temp => temp

def rawToEncodedListHalt (α : Type) [Fintype α] (output : List (Option α)) :
    (rawToEncodedListMachine α).Cfg where
  l := none
  var := none
  stk
    | RawToEncodedListStack.input => []
    | RawToEncodedListStack.output => output
    | RawToEncodedListStack.temp => []

@[simp]
theorem initList_rawToEncodedListMachine (α : Type) [Fintype α] (input : List α) :
    Turing.initList (rawToEncodedListMachine α) input =
      rawToEncodedListCfg α RawToEncodedListLabel.readInput none input [] [] := by
  simp [rawToEncodedListMachine, rawToEncodedListCfg, Turing.initList]
  congr
  funext k
  cases k <;> rfl

@[simp]
theorem haltList_rawToEncodedListMachine (α : Type) [Fintype α]
    (output : List (Option α)) :
    Turing.haltList (rawToEncodedListMachine α) output =
      rawToEncodedListHalt α output := by
  simp [rawToEncodedListMachine, rawToEncodedListHalt, Turing.haltList]
  congr
  funext k
  cases k <;> rfl

theorem rawToEncodedList_readInput_step_cons (α : Type) [Fintype α]
    (state : Option (Option α)) (a : α) (input : List α)
    (output temp : List (Option α)) :
    (rawToEncodedListMachine α).step
        (rawToEncodedListCfg α RawToEncodedListLabel.readInput state
          (a :: input) output temp) =
      some (rawToEncodedListCfg α (RawToEncodedListLabel.pushSome a)
        (some (some a)) input output temp) := by
  simp [rawToEncodedListMachine, rawToEncodedListCfg]
  congr
  funext k
  cases k <;> rfl

theorem rawToEncodedList_readInput_step_nil (α : Type) [Fintype α]
    (state : Option (Option α)) (output temp : List (Option α)) :
    (rawToEncodedListMachine α).step
        (rawToEncodedListCfg α RawToEncodedListLabel.readInput state [] output temp) =
      some (rawToEncodedListCfg α RawToEncodedListLabel.moveTemp none [] output temp) := by
  simp [rawToEncodedListMachine, rawToEncodedListCfg]
  congr

theorem rawToEncodedList_pushSome_step (α : Type) [Fintype α]
    (state : Option (Option α)) (a : α) (input : List α)
    (output temp : List (Option α)) :
    (rawToEncodedListMachine α).step
        (rawToEncodedListCfg α (RawToEncodedListLabel.pushSome a) state input output temp) =
      some (rawToEncodedListCfg α RawToEncodedListLabel.pushNone state input output
        (some a :: temp)) := by
  simp [rawToEncodedListMachine, rawToEncodedListCfg]
  congr
  funext k
  cases k <;> rfl

theorem rawToEncodedList_pushNone_step (α : Type) [Fintype α]
    (state : Option (Option α)) (input : List α) (output temp : List (Option α)) :
    (rawToEncodedListMachine α).step
        (rawToEncodedListCfg α RawToEncodedListLabel.pushNone state input output temp) =
      some (rawToEncodedListCfg α RawToEncodedListLabel.readInput state input output
        (none :: temp)) := by
  simp [rawToEncodedListMachine, rawToEncodedListCfg]
  congr
  funext k
  cases k <;> rfl

theorem rawToEncodedList_moveTemp_step_cons (α : Type) [Fintype α]
    (state : Option (Option α)) (input : List α)
    (output : List (Option α)) (b : Option α) (temp : List (Option α)) :
    (rawToEncodedListMachine α).step
        (rawToEncodedListCfg α RawToEncodedListLabel.moveTemp state input output (b :: temp)) =
      some (rawToEncodedListCfg α (RawToEncodedListLabel.pushOutput b)
        (some b) input output temp) := by
  simp [rawToEncodedListMachine, rawToEncodedListCfg]
  congr
  funext k
  cases k <;> rfl

theorem rawToEncodedList_moveTemp_step_nil (α : Type) [Fintype α]
    (state : Option (Option α)) (output : List (Option α)) :
    (rawToEncodedListMachine α).step
        (rawToEncodedListCfg α RawToEncodedListLabel.moveTemp state [] output []) =
      some (rawToEncodedListHalt α output) := by
  simp [rawToEncodedListMachine, rawToEncodedListCfg, rawToEncodedListHalt]
  congr

theorem rawToEncodedList_pushOutput_step (α : Type) [Fintype α]
    (state : Option (Option α)) (input : List α)
    (output : List (Option α)) (b : Option α) (temp : List (Option α)) :
    (rawToEncodedListMachine α).step
        (rawToEncodedListCfg α (RawToEncodedListLabel.pushOutput b) state input output temp) =
      some (rawToEncodedListCfg α RawToEncodedListLabel.moveTemp state input
        (b :: output) temp) := by
  simp [rawToEncodedListMachine, rawToEncodedListCfg]
  congr
  funext k
  cases k <;> rfl

def rawToEncodedList_readInput_run (α : Type) [Fintype α]
    (state : Option (Option α)) (input : List α)
    (output temp : List (Option α)) :
    StateTransition.EvalsToInTime (rawToEncodedListMachine α).step
      (rawToEncodedListCfg α RawToEncodedListLabel.readInput state input output temp)
      (some (rawToEncodedListCfg α RawToEncodedListLabel.moveTemp none [] output
        ((rawToEncodedListOutput input).reverse ++ temp)))
      (3 * input.length + 1) := by
  induction input generalizing state temp with
  | nil =>
      simpa [rawToEncodedListOutput] using
        evalsToInTimeOne (rawToEncodedList_readInput_step_nil α state output temp)
  | cons a input ih =>
      let tm := rawToEncodedListMachine α
      let c₀ := rawToEncodedListCfg α RawToEncodedListLabel.readInput state
        (a :: input) output temp
      let c₁ := rawToEncodedListCfg α (RawToEncodedListLabel.pushSome a)
        (some (some a)) input output temp
      let c₂ := rawToEncodedListCfg α RawToEncodedListLabel.pushNone
        (some (some a)) input output (some a :: temp)
      let c₃ := rawToEncodedListCfg α RawToEncodedListLabel.readInput
        (some (some a)) input output (none :: some a :: temp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne (rawToEncodedList_readInput_step_cons α state a input output temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (rawToEncodedList_pushSome_step α (some (some a)) a input output temp)
      have h₃ : StateTransition.EvalsToInTime tm.step c₂ (some c₃) 1 :=
        evalsToInTimeOne
          (rawToEncodedList_pushNone_step α (some (some a)) input output (some a :: temp))
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have h₁₂₃ : StateTransition.EvalsToInTime tm.step c₀ (some c₃) (1 + (1 + 1)) :=
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) 1 c₀ c₂ (some c₃) h₁₂ h₃
      have hTail : StateTransition.EvalsToInTime tm.step c₃
          (some (rawToEncodedListCfg α RawToEncodedListLabel.moveTemp none [] output
            ((rawToEncodedListOutput input).reverse ++ (none :: some a :: temp))))
          (3 * input.length + 1) :=
        ih (some (some a)) (none :: some a :: temp)
      simpa [tm, c₀, c₁, c₂, c₃, rawToEncodedListOutput, rawToEncodedListBlock,
        List.reverse_cons, List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + (1 + 1))
          (3 * input.length + 1) c₀ c₃
          (some (rawToEncodedListCfg α RawToEncodedListLabel.moveTemp none [] output
            ((rawToEncodedListOutput input).reverse ++ (none :: some a :: temp))))
          h₁₂₃ hTail

def rawToEncodedList_moveTemp_run (α : Type) [Fintype α]
    (state : Option (Option α)) (output temp : List (Option α)) :
    StateTransition.EvalsToInTime (rawToEncodedListMachine α).step
      (rawToEncodedListCfg α RawToEncodedListLabel.moveTemp state [] output temp)
      (some (rawToEncodedListHalt α (temp.reverse ++ output)))
      (2 * temp.length + 1) := by
  induction temp generalizing state output with
  | nil =>
      simpa using evalsToInTimeOne (rawToEncodedList_moveTemp_step_nil α state output)
  | cons b temp ih =>
      let tm := rawToEncodedListMachine α
      let c₀ := rawToEncodedListCfg α RawToEncodedListLabel.moveTemp state [] output (b :: temp)
      let c₁ := rawToEncodedListCfg α (RawToEncodedListLabel.pushOutput b)
        (some b) [] output temp
      let c₂ := rawToEncodedListCfg α RawToEncodedListLabel.moveTemp
        (some b) [] (b :: output) temp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne (rawToEncodedList_moveTemp_step_cons α state [] output b temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (rawToEncodedList_pushOutput_step α (some b) [] output b temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (rawToEncodedListHalt α (temp.reverse ++ (b :: output))))
          (2 * temp.length + 1) :=
        ih (some b) (b :: output)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * temp.length + 1)
          c₀ c₂ (some (rawToEncodedListHalt α (temp.reverse ++ (b :: output))))
          h₁₂ hTail

theorem rawToEncodedListOutput_length (α : Type) (input : List α) :
    (rawToEncodedListOutput input).length = 2 * input.length := by
  induction input with
  | nil =>
      simp [rawToEncodedListOutput]
  | cons a input ih =>
      have hTail : (List.flatMap rawToEncodedListBlock input).length = 2 * input.length := ih
      simp [rawToEncodedListOutput, rawToEncodedListBlock, hTail]
      omega

def rawToEncodedList_outputs (α : Type) [Fintype α] (input : List α) :
    Turing.TM2OutputsInTime (rawToEncodedListMachine α)
      input (some (rawToEncodedListOutput input)) (7 * input.length + 2) := by
  let tm := rawToEncodedListMachine α
  let encoded := rawToEncodedListOutput input
  let mid := rawToEncodedListCfg α RawToEncodedListLabel.moveTemp none [] [] encoded.reverse
  let done := rawToEncodedListHalt α encoded
  have hRead : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some mid) (3 * input.length + 1) := by
    simpa [tm, mid, encoded] using rawToEncodedList_readInput_run α none input [] []
  have hMove : StateTransition.EvalsToInTime tm.step mid
      (some done) (2 * encoded.length + 1) := by
    simpa [tm, mid, done, encoded, List.length_reverse] using
      rawToEncodedList_moveTemp_run α none [] encoded.reverse
  have hAll : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some done) ((2 * encoded.length + 1) + (3 * input.length + 1)) :=
    StateTransition.EvalsToInTime.trans tm.step (3 * input.length + 1)
      (2 * encoded.length + 1) (Turing.initList tm input) mid (some done) hRead hMove
  change StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
    (some (Turing.haltList tm encoded)) (7 * input.length + 2)
  rw [haltList_rawToEncodedListMachine]
  refine evalsToInTime_mono hAll ?_
  have hLen : encoded.length = 2 * input.length := by
    simpa [encoded] using rawToEncodedListOutput_length α input
  rw [hLen]
  omega

end TM2Programs
end ComplexityReduction
