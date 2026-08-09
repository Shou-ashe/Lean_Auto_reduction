import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryAddMachine

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

open Turing.TM2.Stmt
open TM2Programs

/-!
Direct TM witness converting a binary natural payload into the encoded list of
its bits.

The project `binaryNat` encoding is just the little-endian bit payload.  For
list folds over those bits we need the structural list encoding
`[some b₀, none, some b₁, none, ...]`.  This machine expands each input bit to
one singleton list block and preserves source order.
-/

def binaryNatBitsList (n : Nat) : List Bool :=
  EncodedType.binaryNat.encode n

def boolListSingletonBlocks (bits : List Bool) : List (Option Bool) :=
  bits.flatMap fun bit => [some bit, none]

theorem boolListSingletonBlocks_eq_encode (bits : List Bool) :
    boolListSingletonBlocks bits = (EncodedType.list EncodedType.bool).encode bits := by
  simp [boolListSingletonBlocks, EncodedType.list, EncodedType.bool]

inductive BinaryBitsListStack where
  | input
  | output
  | temp
  deriving DecidableEq, Fintype

abbrev binaryBitsListAlphabet : BinaryBitsListStack → Type
  | .input => Bool
  | .output => Option Bool
  | .temp => Option Bool

inductive BinaryBitsListLabel where
  | readInput
  | pushPayload (bit : Bool)
  | pushDelimiter
  | drain
  | pushOutput (sym : Option Bool)
  | done
  deriving DecidableEq, Fintype

def binaryBitsListMachine : Turing.FinTM2 where
  K := BinaryBitsListStack
  k₀ := BinaryBitsListStack.input
  k₁ := BinaryBitsListStack.output
  Γ := binaryBitsListAlphabet
  Λ := BinaryBitsListLabel
  main := BinaryBitsListLabel.readInput
  σ := Option (Option Bool)
  initialState := none
  Γk₀Fin := by
    dsimp [binaryBitsListAlphabet]
    infer_instance
  m
    | BinaryBitsListLabel.readInput =>
        pop BinaryBitsListStack.input (fun _ head => head.map some)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some (some bit) => BinaryBitsListLabel.pushPayload bit
              | _ => BinaryBitsListLabel.drain)
            (goto fun _ => BinaryBitsListLabel.drain))
    | BinaryBitsListLabel.pushPayload bit =>
        push BinaryBitsListStack.temp (fun _ => some bit)
          (goto fun _ => BinaryBitsListLabel.pushDelimiter)
    | BinaryBitsListLabel.pushDelimiter =>
        push BinaryBitsListStack.temp (fun _ => none)
          (goto fun _ => BinaryBitsListLabel.readInput)
    | BinaryBitsListLabel.drain =>
        pop BinaryBitsListStack.temp (fun _ head => head)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some sym => BinaryBitsListLabel.pushOutput sym
              | none => BinaryBitsListLabel.done)
            (goto fun _ => BinaryBitsListLabel.done))
    | BinaryBitsListLabel.pushOutput sym =>
        push BinaryBitsListStack.output (fun _ => sym)
          (goto fun _ => BinaryBitsListLabel.drain)
    | BinaryBitsListLabel.done =>
        load (fun _ => none) halt

def binaryBitsListCfg
    (label : Option BinaryBitsListLabel) (state : Option (Option Bool))
    (input : List Bool) (output temp : List (Option Bool)) :
    binaryBitsListMachine.Cfg where
  l := label
  var := state
  stk
    | BinaryBitsListStack.input => input
    | BinaryBitsListStack.output => output
    | BinaryBitsListStack.temp => temp

theorem binaryBitsList_initList (input : List Bool) :
    Turing.initList binaryBitsListMachine input =
      binaryBitsListCfg (some BinaryBitsListLabel.readInput) none input [] [] := by
  simp [Turing.initList, binaryBitsListMachine, binaryBitsListCfg]
  congr
  funext k
  cases k <;> rfl

theorem binaryBitsList_haltList (output : List (Option Bool)) :
    Turing.haltList binaryBitsListMachine output =
      binaryBitsListCfg none none [] output [] := by
  simp [Turing.haltList, binaryBitsListMachine, binaryBitsListCfg]
  congr
  funext k
  cases k <;> rfl

theorem binaryBitsList_readInput_step_cons
    (state : Option (Option Bool)) (bit : Bool) (input : List Bool)
    (output temp : List (Option Bool)) :
    binaryBitsListMachine.step
        (binaryBitsListCfg (some BinaryBitsListLabel.readInput) state
          (bit :: input) output temp) =
      some (binaryBitsListCfg (some (BinaryBitsListLabel.pushPayload bit))
        (some (some bit)) input output temp) := by
  simp [binaryBitsListMachine, binaryBitsListCfg]
  congr
  funext k
  cases k <;> rfl

theorem binaryBitsList_readInput_step_nil
    (state : Option (Option Bool)) (output temp : List (Option Bool)) :
    binaryBitsListMachine.step
        (binaryBitsListCfg (some BinaryBitsListLabel.readInput) state [] output temp) =
      some (binaryBitsListCfg (some BinaryBitsListLabel.drain) none [] output temp) := by
  simp [binaryBitsListMachine, binaryBitsListCfg]
  congr

theorem binaryBitsList_pushPayload_step
    (state : Option (Option Bool)) (bit : Bool) (input : List Bool)
    (output temp : List (Option Bool)) :
    binaryBitsListMachine.step
        (binaryBitsListCfg (some (BinaryBitsListLabel.pushPayload bit)) state
          input output temp) =
      some (binaryBitsListCfg (some BinaryBitsListLabel.pushDelimiter) state
        input output (some bit :: temp)) := by
  simp [binaryBitsListMachine, binaryBitsListCfg]
  congr
  funext k
  cases k <;> rfl

theorem binaryBitsList_pushDelimiter_step
    (state : Option (Option Bool)) (input : List Bool)
    (output temp : List (Option Bool)) :
    binaryBitsListMachine.step
        (binaryBitsListCfg (some BinaryBitsListLabel.pushDelimiter) state
          input output temp) =
      some (binaryBitsListCfg (some BinaryBitsListLabel.readInput) state
        input output (none :: temp)) := by
  simp [binaryBitsListMachine, binaryBitsListCfg]
  congr
  funext k
  cases k <;> rfl

theorem binaryBitsList_drain_step_cons
    (state : Option (Option Bool)) (sym : Option Bool) (temp : List (Option Bool))
    (output : List (Option Bool)) :
    binaryBitsListMachine.step
        (binaryBitsListCfg (some BinaryBitsListLabel.drain) state [] output (sym :: temp)) =
      some (binaryBitsListCfg (some (BinaryBitsListLabel.pushOutput sym))
        (some sym) [] output temp) := by
  simp [binaryBitsListMachine, binaryBitsListCfg]
  congr
  funext k
  cases k <;> rfl

theorem binaryBitsList_drain_step_nil
    (state : Option (Option Bool)) (output : List (Option Bool)) :
    binaryBitsListMachine.step
        (binaryBitsListCfg (some BinaryBitsListLabel.drain) state [] output []) =
      some (binaryBitsListCfg (some BinaryBitsListLabel.done) none [] output []) := by
  simp [binaryBitsListMachine, binaryBitsListCfg]
  congr

theorem binaryBitsList_pushOutput_step
    (state : Option (Option Bool)) (sym : Option Bool)
    (output temp : List (Option Bool)) :
    binaryBitsListMachine.step
        (binaryBitsListCfg (some (BinaryBitsListLabel.pushOutput sym)) state
          [] output temp) =
      some (binaryBitsListCfg (some BinaryBitsListLabel.drain) state
        [] (sym :: output) temp) := by
  simp [binaryBitsListMachine, binaryBitsListCfg]
  congr
  funext k
  cases k <;> rfl

theorem binaryBitsList_done_step (output : List (Option Bool)) :
    binaryBitsListMachine.step
        (binaryBitsListCfg (some BinaryBitsListLabel.done) none [] output []) =
      some (binaryBitsListCfg none none [] output []) := by
  simp [binaryBitsListMachine, binaryBitsListCfg]
  congr

def binaryBitsList_readInput_run
    (bits : List Bool) (state : Option (Option Bool))
    (output temp : List (Option Bool)) :
    StateTransition.EvalsToInTime binaryBitsListMachine.step
      (binaryBitsListCfg (some BinaryBitsListLabel.readInput) state bits output temp)
      (some (binaryBitsListCfg (some BinaryBitsListLabel.drain) none [] output
        ((boolListSingletonBlocks bits).reverse ++ temp)))
      (3 * bits.length + 1) := by
  induction bits generalizing state temp with
  | nil =>
      have h₁ : StateTransition.EvalsToInTime binaryBitsListMachine.step
          (binaryBitsListCfg (some BinaryBitsListLabel.readInput) state [] output temp)
          (some (binaryBitsListCfg (some BinaryBitsListLabel.drain) none [] output temp)) 1 :=
        evalsToInTimeOne (binaryBitsList_readInput_step_nil state output temp)
      simpa [boolListSingletonBlocks] using h₁
  | cons bit bits ih =>
      let c₀ := binaryBitsListCfg (some BinaryBitsListLabel.readInput) state
        (bit :: bits) output temp
      let c₁ := binaryBitsListCfg (some (BinaryBitsListLabel.pushPayload bit))
        (some (some bit)) bits output temp
      let c₂ := binaryBitsListCfg (some BinaryBitsListLabel.pushDelimiter)
        (some (some bit)) bits output (some bit :: temp)
      let c₃ := binaryBitsListCfg (some BinaryBitsListLabel.readInput)
        (some (some bit)) bits output (none :: some bit :: temp)
      have h₁ : StateTransition.EvalsToInTime binaryBitsListMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (binaryBitsList_readInput_step_cons state bit bits output temp)
      have h₂ : StateTransition.EvalsToInTime binaryBitsListMachine.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (binaryBitsList_pushPayload_step (some (some bit)) bit bits output temp)
      have h₃ : StateTransition.EvalsToInTime binaryBitsListMachine.step c₂ (some c₃) 1 :=
        evalsToInTimeOne
          (binaryBitsList_pushDelimiter_step (some (some bit)) bits output (some bit :: temp))
      have h₁₂ : StateTransition.EvalsToInTime binaryBitsListMachine.step c₀ (some c₂)
          (1 + 1) :=
        StateTransition.EvalsToInTime.trans binaryBitsListMachine.step 1 1 c₀ c₁
          (some c₂) h₁ h₂
      have h₁₂₃ : StateTransition.EvalsToInTime binaryBitsListMachine.step c₀ (some c₃)
          ((1 + 1) + 1) :=
        StateTransition.EvalsToInTime.trans binaryBitsListMachine.step (1 + 1) 1 c₀ c₂
          (some c₃) h₁₂ h₃
      have hTail := ih (some (some bit)) (none :: some bit :: temp)
      have hAll :=
        StateTransition.EvalsToInTime.trans binaryBitsListMachine.step ((1 + 1) + 1)
          (3 * bits.length + 1) c₀ c₃
          (some (binaryBitsListCfg (some BinaryBitsListLabel.drain) none [] output
            ((boolListSingletonBlocks bits).reverse ++ none :: some bit :: temp)))
          h₁₂₃ hTail
      simpa [c₀, c₁, c₂, c₃, boolListSingletonBlocks, List.reverse_append,
        List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hAll

def binaryBitsList_drain_run
    (temp output : List (Option Bool)) (state : Option (Option Bool)) :
    StateTransition.EvalsToInTime binaryBitsListMachine.step
      (binaryBitsListCfg (some BinaryBitsListLabel.drain) state [] output temp)
      (some (binaryBitsListCfg none none [] (temp.reverse ++ output) []))
      (2 * temp.length + 2) := by
  induction temp generalizing output state with
  | nil =>
      let c₀ := binaryBitsListCfg (some BinaryBitsListLabel.drain) state [] output []
      let c₁ := binaryBitsListCfg (some BinaryBitsListLabel.done) none [] output []
      let c₂ := binaryBitsListCfg none none [] output []
      have h₁ : StateTransition.EvalsToInTime binaryBitsListMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne (binaryBitsList_drain_step_nil state output)
      have h₂ : StateTransition.EvalsToInTime binaryBitsListMachine.step c₁ (some c₂) 1 :=
        evalsToInTimeOne (binaryBitsList_done_step output)
      have hAll :=
        StateTransition.EvalsToInTime.trans binaryBitsListMachine.step 1 1 c₀ c₁
          (some c₂) h₁ h₂
      simpa [c₀, c₁, c₂] using hAll
  | cons sym temp ih =>
      let c₀ := binaryBitsListCfg (some BinaryBitsListLabel.drain) state [] output
        (sym :: temp)
      let c₁ := binaryBitsListCfg (some (BinaryBitsListLabel.pushOutput sym))
        (some sym) [] output temp
      let c₂ := binaryBitsListCfg (some BinaryBitsListLabel.drain) (some sym) []
        (sym :: output) temp
      have h₁ : StateTransition.EvalsToInTime binaryBitsListMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne (binaryBitsList_drain_step_cons state sym temp output)
      have h₂ : StateTransition.EvalsToInTime binaryBitsListMachine.step c₁ (some c₂) 1 :=
        evalsToInTimeOne (binaryBitsList_pushOutput_step (some sym) sym output temp)
      have h₁₂ : StateTransition.EvalsToInTime binaryBitsListMachine.step c₀ (some c₂)
          (1 + 1) :=
        StateTransition.EvalsToInTime.trans binaryBitsListMachine.step 1 1 c₀ c₁
          (some c₂) h₁ h₂
      have hTail := ih (sym :: output) (some sym)
      have hAll :=
        StateTransition.EvalsToInTime.trans binaryBitsListMachine.step (1 + 1)
          (2 * temp.length + 2) c₀ c₂
          (some (binaryBitsListCfg none none [] (temp.reverse ++ sym :: output) []))
          h₁₂ hTail
      simpa [c₀, c₁, c₂, List.reverse_cons, List.append_assoc, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAll

noncomputable def binaryNatBitsListMachine_outputs (bits : List Bool) :
    Turing.TM2OutputsInTime binaryBitsListMachine bits
      (some (boolListSingletonBlocks bits)) ((8 * Polynomial.X + 8).eval bits.length) := by
  let encoded := boolListSingletonBlocks bits
  let cDrain := binaryBitsListCfg (some BinaryBitsListLabel.drain) none []
    [] encoded.reverse
  let cHalt := binaryBitsListCfg none none [] encoded []
  have hRead : StateTransition.EvalsToInTime binaryBitsListMachine.step
      (Turing.initList binaryBitsListMachine bits) (some cDrain) (3 * bits.length + 1) := by
    rw [binaryBitsList_initList]
    simpa [cDrain, encoded] using binaryBitsList_readInput_run bits none [] []
  have hDrain : StateTransition.EvalsToInTime binaryBitsListMachine.step
      cDrain (some cHalt) (2 * encoded.reverse.length + 2) := by
    simpa [cDrain, cHalt, List.reverse_reverse] using
      binaryBitsList_drain_run encoded.reverse [] none
  have hAll : StateTransition.EvalsToInTime binaryBitsListMachine.step
      (Turing.initList binaryBitsListMachine bits) (some cHalt)
      ((2 * encoded.reverse.length + 2) + (3 * bits.length + 1)) :=
    StateTransition.EvalsToInTime.trans binaryBitsListMachine.step
      (3 * bits.length + 1) (2 * encoded.reverse.length + 2)
      (Turing.initList binaryBitsListMachine bits) cDrain (some cHalt) hRead hDrain
  unfold Turing.TM2OutputsInTime
  change StateTransition.EvalsToInTime binaryBitsListMachine.step
    (Turing.initList binaryBitsListMachine bits)
    (some (Turing.haltList binaryBitsListMachine (boolListSingletonBlocks bits)))
    ((8 * Polynomial.X + 8).eval bits.length)
  rw [binaryBitsList_haltList]
  refine evalsToInTime_mono (by simpa [cHalt, encoded] using hAll) ?_
  simp [boolListSingletonBlocks, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
  omega

noncomputable def binaryNatBitsListComputableInPolyTime :
    Turing.TM2ComputableInPolyTime
      EncodedType.binaryNat.encode
      (EncodedType.list EncodedType.bool).encode
      binaryNatBitsList where
  tm := binaryBitsListMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl (Option Bool)
  time := 8 * Polynomial.X + 8
  outputsFun n := by
    have h := binaryNatBitsListMachine_outputs (EncodedType.binaryNat.encode n)
    unfold Turing.TM2OutputsInTime at h ⊢
    have hInput :
        (EncodedType.binaryNat.encode n).map (Equiv.refl Bool).symm =
          EncodedType.binaryNat.encode n :=
      list_map_equivRefl_symm (EncodedType.binaryNat.encode n)
    have hOutput :
        (EncodedType.list EncodedType.bool).encode (binaryNatBitsList n) =
          boolListSingletonBlocks (EncodedType.binaryNat.encode n) := by
      rw [binaryNatBitsList, ← boolListSingletonBlocks_eq_encode]
    convert h using 1
    · exact congrArg (Turing.initList binaryBitsListMachine) hInput
    · rw [hOutput]
      exact congrArg (fun xs : List (Option Bool) =>
        Option.map (Turing.haltList binaryBitsListMachine) (some xs))
        (list_map_equivRefl_symm (boolListSingletonBlocks (EncodedType.binaryNat.encode n)))

theorem binaryNatBitsList_tm_polytime :
    TMPolyTimeMap
      EncodedType.binaryNat
      (EncodedType.list EncodedType.bool)
      binaryNatBitsList :=
  ⟨binaryNatBitsListComputableInPolyTime⟩

end Knapsack
end Karp21
end ComplexityReduction
