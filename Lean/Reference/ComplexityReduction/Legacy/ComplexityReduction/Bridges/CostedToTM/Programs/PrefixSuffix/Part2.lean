import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.PrefixSuffix.Part1

namespace ComplexityReduction
namespace TM2Programs
open Turing.TM2.Stmt

def prefixListMap_readInput_run (α β : Type) [Fintype α] [Fintype β]
    (prefList : List β) (mapSym : α → β) (state : Option β)
    (input : List α) (output temp : List β) :
    StateTransition.EvalsToInTime (prefixListMapMachine α β prefList mapSym).step
      (prefixListMapCfg α β prefList mapSym PrefixMapLabel.readInput state input output temp)
      (some (prefixListMapCfg α β prefList mapSym PrefixMapLabel.moveTemp none [] output
        ((input.map mapSym).reverse ++ temp)))
      (2 * input.length + 1) := by
  induction input generalizing state temp with
  | nil =>
      simpa using
        evalsToInTimeOne
          (prefixListMap_readInput_step_nil α β prefList mapSym state output temp)
  | cons a input ih =>
      let tm := prefixListMapMachine α β prefList mapSym
      let c₀ := prefixListMapCfg α β prefList mapSym PrefixMapLabel.readInput state
        (a :: input) output temp
      let c₁ := prefixListMapCfg α β prefList mapSym (PrefixMapLabel.pushTemp (mapSym a))
        (some (mapSym a)) input output temp
      let c₂ := prefixListMapCfg α β prefList mapSym PrefixMapLabel.readInput
        (some (mapSym a)) input output (mapSym a :: temp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (prefixListMap_readInput_step_cons α β prefList mapSym state a input output temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (prefixListMap_pushTemp_step α β prefList mapSym (some (mapSym a))
            (mapSym a) input output temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (prefixListMapCfg α β prefList mapSym PrefixMapLabel.moveTemp none [] output
            ((input.map mapSym).reverse ++ (mapSym a :: temp))))
          (2 * input.length + 1) :=
        ih (some (mapSym a)) (mapSym a :: temp)
      simpa [tm, c₀, c₁, c₂, List.map_cons, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * input.length + 1)
          c₀ c₂
          (some (prefixListMapCfg α β prefList mapSym PrefixMapLabel.moveTemp none [] output
            ((input.map mapSym).reverse ++ (mapSym a :: temp))))
          h₁₂ hTail

def prefixListMap_moveTemp_run (α β : Type) [Fintype α] [Fintype β]
    (prefList : List β) (mapSym : α → β) (state : Option β)
    (input : List α) (output temp : List β) :
    StateTransition.EvalsToInTime (prefixListMapMachine α β prefList mapSym).step
      (prefixListMapCfg α β prefList mapSym PrefixMapLabel.moveTemp state input output temp)
      (some (prefixListMapCfg α β prefList mapSym PrefixMapLabel.writePrefix none input
        (temp.reverse ++ output) []))
      (2 * temp.length + 1) := by
  induction temp generalizing state output with
  | nil =>
      simpa using
        evalsToInTimeOne
          (prefixListMap_moveTemp_step_nil α β prefList mapSym state input output)
  | cons b temp ih =>
      let tm := prefixListMapMachine α β prefList mapSym
      let c₀ := prefixListMapCfg α β prefList mapSym PrefixMapLabel.moveTemp state input output
        (b :: temp)
      let c₁ := prefixListMapCfg α β prefList mapSym (PrefixMapLabel.pushOutput b) (some b)
        input output temp
      let c₂ := prefixListMapCfg α β prefList mapSym PrefixMapLabel.moveTemp (some b) input
        (b :: output) temp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (prefixListMap_moveTemp_step_cons α β prefList mapSym state input output b temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (prefixListMap_pushOutput_step α β prefList mapSym (some b) input output b temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (prefixListMapCfg α β prefList mapSym PrefixMapLabel.writePrefix none input
            (temp.reverse ++ (b :: output)) []))
          (2 * temp.length + 1) :=
        ih (some b) (b :: output)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * temp.length + 1)
          c₀ c₂
          (some (prefixListMapCfg α β prefList mapSym PrefixMapLabel.writePrefix none input
            (temp.reverse ++ (b :: output)) []))
          h₁₂ hTail

def prefixListMap_writePrefix_run (α β : Type) [Fintype α] [Fintype β]
    (prefList : List β) (mapSym : α → β) (state : Option β) (output : List β) :
    StateTransition.EvalsToInTime (prefixListMapMachine α β prefList mapSym).step
      (prefixListMapCfg α β prefList mapSym PrefixMapLabel.writePrefix state [] output [])
      (some (prefixListMapHalt α β prefList mapSym (prefList ++ output))) 1 :=
  evalsToInTimeOne (prefixListMap_writePrefix_step α β prefList mapSym state output)

/-- The fixed-prefList map program computes `input ↦ prefList ++ input.map mapSym`. -/
def prefixListMap_outputs (α β : Type) [Fintype α] [Fintype β]
    (prefList : List β) (mapSym : α → β) (input : List α) :
    Turing.TM2OutputsInTime (prefixListMapMachine α β prefList mapSym)
      input (some (prefList ++ input.map mapSym)) (4 * input.length + 3) := by
  let tm := prefixListMapMachine α β prefList mapSym
  let mapped := input.map mapSym
  let mid₁ := prefixListMapCfg α β prefList mapSym PrefixMapLabel.moveTemp none [] []
    mapped.reverse
  let mid₂ := prefixListMapCfg α β prefList mapSym PrefixMapLabel.writePrefix none [] mapped []
  let done := prefixListMapHalt α β prefList mapSym (prefList ++ mapped)
  have hRead : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some mid₁) (2 * input.length + 1) := by
    simpa [tm, mid₁, mapped, initList_prefixListMapMachine] using
      prefixListMap_readInput_run α β prefList mapSym none input [] []
  have hMove : StateTransition.EvalsToInTime tm.step mid₁
      (some mid₂) (2 * input.length + 1) := by
    simpa [tm, mid₁, mid₂, mapped, List.length_reverse] using
      prefixListMap_moveTemp_run α β prefList mapSym none [] [] mapped.reverse
  have hWrite : StateTransition.EvalsToInTime tm.step mid₂ (some done) 1 := by
    simpa [tm, mid₂, done, mapped] using
      prefixListMap_writePrefix_run α β prefList mapSym none mapped
  have hReadMove : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some mid₂) ((2 * input.length + 1) + (2 * input.length + 1)) :=
    StateTransition.EvalsToInTime.trans tm.step (2 * input.length + 1)
      (2 * input.length + 1) (Turing.initList tm input) mid₁ (some mid₂)
      hRead hMove
  have hAll : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some done) (1 + ((2 * input.length + 1) + (2 * input.length + 1))) :=
    StateTransition.EvalsToInTime.trans tm.step
      ((2 * input.length + 1) + (2 * input.length + 1)) 1
      (Turing.initList tm input) mid₂ (some done) hReadMove hWrite
  change StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
    (some (Turing.haltList tm (prefList ++ mapped))) (4 * input.length + 3)
  rw [haltList_prefixListMapMachine]
  convert hAll using 1
  omega

/-- Control labels for a program that maps input symbols and appends one output suffix. -/
inductive SuffixMapLabel (β : Type) where
  | readInput
  | pushTemp (b : β)
  | writeSuffix
  | moveTemp
  | pushOutput (b : β)
  deriving DecidableEq, Fintype

/--
A concrete TM2 program for `input ↦ input.map mapSym ++ [suff]`.

The program first maps input into a temporary stack, writes the suffix to output,
and then moves the temporary stack to output so mapped symbols precede the
suffix in the restored order.
-/
def suffixMapMachine (α β : Type) [Fintype α] [Fintype β]
    (suff : β) (mapSym : α → β) : Turing.FinTM2 where
  K := PrefixMapStack
  k₀ := PrefixMapStack.input
  k₁ := PrefixMapStack.output
  Γ := prefixMapAlphabet α β
  Λ := SuffixMapLabel β
  main := SuffixMapLabel.readInput
  σ := Option β
  initialState := none
  Γk₀Fin := by
    dsimp [prefixMapAlphabet]
    infer_instance
  m
    | SuffixMapLabel.readInput =>
        pop PrefixMapStack.input (fun _ head => head.map mapSym)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some b => SuffixMapLabel.pushTemp b
              | none => SuffixMapLabel.writeSuffix)
            (goto fun _ => SuffixMapLabel.writeSuffix))
    | SuffixMapLabel.pushTemp b =>
        push PrefixMapStack.temp (fun _ => b)
          (goto fun _ => SuffixMapLabel.readInput)
    | SuffixMapLabel.writeSuffix =>
        push PrefixMapStack.output (fun _ => suff)
          (goto fun _ => SuffixMapLabel.moveTemp)
    | SuffixMapLabel.moveTemp =>
        pop PrefixMapStack.temp (fun _ head => head)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some b => SuffixMapLabel.pushOutput b
              | none => SuffixMapLabel.moveTemp)
            (load (fun _ => none) halt))
    | SuffixMapLabel.pushOutput b =>
        push PrefixMapStack.output (fun _ => b)
          (goto fun _ => SuffixMapLabel.moveTemp)

def suffixMapCfg (α β : Type) [Fintype α] [Fintype β]
    (suff : β) (mapSym : α → β) (label : SuffixMapLabel β) (state : Option β)
    (input : List α) (output temp : List β) :
    (suffixMapMachine α β suff mapSym).Cfg where
  l := some label
  var := state
  stk
    | PrefixMapStack.input => input
    | PrefixMapStack.output => output
    | PrefixMapStack.temp => temp

def suffixMapHalt (α β : Type) [Fintype α] [Fintype β]
    (suff : β) (mapSym : α → β) (output : List β) :
    (suffixMapMachine α β suff mapSym).Cfg where
  l := none
  var := none
  stk
    | PrefixMapStack.input => []
    | PrefixMapStack.output => output
    | PrefixMapStack.temp => []

lemma suffixMap_readInput_step_cons (α β : Type) [Fintype α] [Fintype β]
    (suff : β) (mapSym : α → β) (state : Option β)
    (a : α) (input : List α) (output temp : List β) :
    (suffixMapMachine α β suff mapSym).step
        (suffixMapCfg α β suff mapSym SuffixMapLabel.readInput state
          (a :: input) output temp) =
      some (suffixMapCfg α β suff mapSym (SuffixMapLabel.pushTemp (mapSym a))
        (some (mapSym a)) input output temp) := by
  simp [suffixMapMachine, suffixMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma suffixMap_readInput_step_nil (α β : Type) [Fintype α] [Fintype β]
    (suff : β) (mapSym : α → β) (state : Option β) (output temp : List β) :
    (suffixMapMachine α β suff mapSym).step
        (suffixMapCfg α β suff mapSym SuffixMapLabel.readInput state [] output temp) =
      some (suffixMapCfg α β suff mapSym SuffixMapLabel.writeSuffix none [] output temp) := by
  simp [suffixMapMachine, suffixMapCfg]
  congr

lemma suffixMap_pushTemp_step (α β : Type) [Fintype α] [Fintype β]
    (suff : β) (mapSym : α → β) (state : Option β)
    (b : β) (input : List α) (output temp : List β) :
    (suffixMapMachine α β suff mapSym).step
        (suffixMapCfg α β suff mapSym (SuffixMapLabel.pushTemp b) state
          input output temp) =
      some (suffixMapCfg α β suff mapSym SuffixMapLabel.readInput state input output
        (b :: temp)) := by
  simp [suffixMapMachine, suffixMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma suffixMap_writeSuffix_step (α β : Type) [Fintype α] [Fintype β]
    (suff : β) (mapSym : α → β) (state : Option β)
    (input : List α) (output temp : List β) :
    (suffixMapMachine α β suff mapSym).step
        (suffixMapCfg α β suff mapSym SuffixMapLabel.writeSuffix state input output temp) =
      some (suffixMapCfg α β suff mapSym SuffixMapLabel.moveTemp state input
        (suff :: output) temp) := by
  simp [suffixMapMachine, suffixMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma suffixMap_moveTemp_step_cons (α β : Type) [Fintype α] [Fintype β]
    (suff : β) (mapSym : α → β) (state : Option β)
    (input : List α) (output : List β) (b : β) (temp : List β) :
    (suffixMapMachine α β suff mapSym).step
        (suffixMapCfg α β suff mapSym SuffixMapLabel.moveTemp state input output
          (b :: temp)) =
      some (suffixMapCfg α β suff mapSym (SuffixMapLabel.pushOutput b) (some b)
        input output temp) := by
  simp [suffixMapMachine, suffixMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma suffixMap_moveTemp_step_nil (α β : Type) [Fintype α] [Fintype β]
    (suff : β) (mapSym : α → β) (state : Option β) (output : List β) :
    (suffixMapMachine α β suff mapSym).step
        (suffixMapCfg α β suff mapSym SuffixMapLabel.moveTemp state [] output []) =
      some (suffixMapHalt α β suff mapSym output) := by
  simp [suffixMapMachine, suffixMapCfg, suffixMapHalt]
  congr

lemma suffixMap_pushOutput_step (α β : Type) [Fintype α] [Fintype β]
    (suff : β) (mapSym : α → β) (state : Option β)
    (input : List α) (output : List β) (b : β) (temp : List β) :
    (suffixMapMachine α β suff mapSym).step
        (suffixMapCfg α β suff mapSym (SuffixMapLabel.pushOutput b) state input output
          temp) =
      some (suffixMapCfg α β suff mapSym SuffixMapLabel.moveTemp state input
        (b :: output) temp) := by
  simp [suffixMapMachine, suffixMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma initList_suffixMapMachine (α β : Type) [Fintype α] [Fintype β]
    (suff : β) (mapSym : α → β) (input : List α) :
    Turing.initList (suffixMapMachine α β suff mapSym) input =
      suffixMapCfg α β suff mapSym SuffixMapLabel.readInput none input [] [] := by
  simp [suffixMapMachine, suffixMapCfg, Turing.initList]
  congr
  funext k
  cases k <;> rfl

lemma haltList_suffixMapMachine (α β : Type) [Fintype α] [Fintype β]
    (suff : β) (mapSym : α → β) (output : List β) :
    Turing.haltList (suffixMapMachine α β suff mapSym) output =
      suffixMapHalt α β suff mapSym output := by
  simp [suffixMapMachine, suffixMapHalt, Turing.haltList]
  congr
  funext k
  cases k <;> rfl

def suffixMap_readInput_run (α β : Type) [Fintype α] [Fintype β]
    (suff : β) (mapSym : α → β) (state : Option β)
    (input : List α) (output temp : List β) :
    StateTransition.EvalsToInTime (suffixMapMachine α β suff mapSym).step
      (suffixMapCfg α β suff mapSym SuffixMapLabel.readInput state input output temp)
      (some (suffixMapCfg α β suff mapSym SuffixMapLabel.writeSuffix none [] output
        ((input.map mapSym).reverse ++ temp)))
      (2 * input.length + 1) := by
  induction input generalizing state temp with
  | nil =>
      simpa using
        evalsToInTimeOne
          (suffixMap_readInput_step_nil α β suff mapSym state output temp)
  | cons a input ih =>
      let tm := suffixMapMachine α β suff mapSym
      let c₀ := suffixMapCfg α β suff mapSym SuffixMapLabel.readInput state
        (a :: input) output temp
      let c₁ := suffixMapCfg α β suff mapSym (SuffixMapLabel.pushTemp (mapSym a))
        (some (mapSym a)) input output temp
      let c₂ := suffixMapCfg α β suff mapSym SuffixMapLabel.readInput (some (mapSym a))
        input output (mapSym a :: temp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (suffixMap_readInput_step_cons α β suff mapSym state a input output temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (suffixMap_pushTemp_step α β suff mapSym (some (mapSym a))
            (mapSym a) input output temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (suffixMapCfg α β suff mapSym SuffixMapLabel.writeSuffix none [] output
            ((input.map mapSym).reverse ++ (mapSym a :: temp))))
          (2 * input.length + 1) :=
        ih (some (mapSym a)) (mapSym a :: temp)
      simpa [tm, c₀, c₁, c₂, List.map_cons, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * input.length + 1)
          c₀ c₂
          (some (suffixMapCfg α β suff mapSym SuffixMapLabel.writeSuffix none [] output
            ((input.map mapSym).reverse ++ (mapSym a :: temp))))
          h₁₂ hTail

def suffixMap_moveTemp_run (α β : Type) [Fintype α] [Fintype β]
    (suff : β) (mapSym : α → β) (state : Option β)
    (output temp : List β) :
    StateTransition.EvalsToInTime (suffixMapMachine α β suff mapSym).step
      (suffixMapCfg α β suff mapSym SuffixMapLabel.moveTemp state [] output temp)
      (some (suffixMapHalt α β suff mapSym (temp.reverse ++ output)))
      (2 * temp.length + 1) := by
  induction temp generalizing state output with
  | nil =>
      simpa using
        evalsToInTimeOne
          (suffixMap_moveTemp_step_nil α β suff mapSym state output)
  | cons b temp ih =>
      let tm := suffixMapMachine α β suff mapSym
      let c₀ := suffixMapCfg α β suff mapSym SuffixMapLabel.moveTemp state [] output
        (b :: temp)
      let c₁ := suffixMapCfg α β suff mapSym (SuffixMapLabel.pushOutput b) (some b)
        [] output temp
      let c₂ := suffixMapCfg α β suff mapSym SuffixMapLabel.moveTemp (some b) []
        (b :: output) temp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (suffixMap_moveTemp_step_cons α β suff mapSym state [] output b temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (suffixMap_pushOutput_step α β suff mapSym (some b) [] output b temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (suffixMapHalt α β suff mapSym (temp.reverse ++ (b :: output))))
          (2 * temp.length + 1) := by
        simpa [c₂] using ih (some b) (b :: output)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * temp.length + 1)
          c₀ c₂ (some (suffixMapHalt α β suff mapSym (temp.reverse ++ (b :: output))))
          h₁₂ hTail

/-- The suffix-map program computes `input ↦ input.map mapSym ++ [suff]` in linear TM2 time. -/
def suffixMap_outputs (α β : Type) [Fintype α] [Fintype β]
    (suff : β) (mapSym : α → β) (input : List α) :
    Turing.TM2OutputsInTime (suffixMapMachine α β suff mapSym)
      input (some (input.map mapSym ++ [suff])) (4 * input.length + 3) := by
  let tm := suffixMapMachine α β suff mapSym
  let mapped := input.map mapSym
  let mid₁ := suffixMapCfg α β suff mapSym SuffixMapLabel.writeSuffix none [] []
    mapped.reverse
  let mid₂ := suffixMapCfg α β suff mapSym SuffixMapLabel.moveTemp none [] [suff]
    mapped.reverse
  let done := suffixMapHalt α β suff mapSym (mapped ++ [suff])
  have hRead : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some mid₁) (2 * input.length + 1) := by
    simpa [tm, mid₁, mapped, initList_suffixMapMachine] using
      suffixMap_readInput_run α β suff mapSym none input [] []
  have hSuffix : StateTransition.EvalsToInTime tm.step mid₁
      (some mid₂) 1 := by
    simpa [tm, mid₁, mid₂, mapped] using
      evalsToInTimeOne
        (suffixMap_writeSuffix_step α β suff mapSym none [] [] mapped.reverse)
  have hMove : StateTransition.EvalsToInTime tm.step mid₂
      (some done) (2 * input.length + 1) := by
    simpa [tm, mid₂, done, mapped, List.length_reverse, List.singleton_append,
      List.append_assoc] using
      suffixMap_moveTemp_run α β suff mapSym none [suff] mapped.reverse
  have hReadSuffix : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some mid₂) (1 + (2 * input.length + 1)) :=
    StateTransition.EvalsToInTime.trans tm.step (2 * input.length + 1) 1
      (Turing.initList tm input) mid₁ (some mid₂) hRead hSuffix
  have hAll : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some done) ((2 * input.length + 1) + (1 + (2 * input.length + 1))) :=
    StateTransition.EvalsToInTime.trans tm.step (1 + (2 * input.length + 1))
      (2 * input.length + 1) (Turing.initList tm input) mid₂ (some done)
      hReadSuffix hMove
  change StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
    (some (Turing.haltList tm (mapped ++ [suff]))) (4 * input.length + 3)
  rw [haltList_suffixMapMachine]
  convert hAll using 1
  omega

/-- Add a fixed list of output symbols to the output stack in a suffix-map machine. -/
def pushAllSuffixMapOutput {α β : Type} :
    List β →
      Turing.TM2.Stmt (prefixMapAlphabet α β) (SuffixMapLabel β) (Option β) →
      Turing.TM2.Stmt (prefixMapAlphabet α β) (SuffixMapLabel β) (Option β)
  | [], q => q
  | b :: bs, q =>
      push PrefixMapStack.output (fun _ => b) (pushAllSuffixMapOutput bs q)

/--
Executing the nested fixed-suffix statement prepends the fixed suffix to the
current output stack and then enters `moveTemp`.
-/
lemma stepAux_pushAllSuffixMapOutput {α β : Type} (suffList : List β)
    (state : Option β)
    (stk : (k : PrefixMapStack) → List (prefixMapAlphabet α β k)) :
    Turing.TM2.stepAux (K := PrefixMapStack)
      (pushAllSuffixMapOutput (α := α) (β := β) suffList.reverse
        (goto fun _ : Option β => SuffixMapLabel.moveTemp))
      state stk =
    { l := some SuffixMapLabel.moveTemp, var := state,
      stk := Function.update stk PrefixMapStack.output (suffList ++ stk PrefixMapStack.output) } := by
  induction suffList using List.reverseRecOn generalizing stk with
  | nil =>
      simp [pushAllSuffixMapOutput]
  | append_singleton xs x ih =>
      simp [pushAllSuffixMapOutput, List.reverse_append, ih, List.append_assoc]

/--
A concrete TM2 program for `input ↦ input.map mapSym ++ suffList`, where
`suffList` is fixed in the machine.
-/
def suffixListMapMachine (α β : Type) [Fintype α] [Fintype β]
    (suffList : List β) (mapSym : α → β) : Turing.FinTM2 where
  K := PrefixMapStack
  k₀ := PrefixMapStack.input
  k₁ := PrefixMapStack.output
  Γ := prefixMapAlphabet α β
  Λ := SuffixMapLabel β
  main := SuffixMapLabel.readInput
  σ := Option β
  initialState := none
  Γk₀Fin := by
    dsimp [prefixMapAlphabet]
    infer_instance
  m
    | SuffixMapLabel.readInput =>
        pop PrefixMapStack.input (fun _ head => head.map mapSym)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some b => SuffixMapLabel.pushTemp b
              | none => SuffixMapLabel.writeSuffix)
            (goto fun _ => SuffixMapLabel.writeSuffix))
    | SuffixMapLabel.pushTemp b =>
        push PrefixMapStack.temp (fun _ => b)
          (goto fun _ => SuffixMapLabel.readInput)
    | SuffixMapLabel.writeSuffix =>
        pushAllSuffixMapOutput suffList.reverse
          (goto fun _ : Option β => SuffixMapLabel.moveTemp)
    | SuffixMapLabel.moveTemp =>
        pop PrefixMapStack.temp (fun _ head => head)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some b => SuffixMapLabel.pushOutput b
              | none => SuffixMapLabel.moveTemp)
            (load (fun _ => none) halt))
    | SuffixMapLabel.pushOutput b =>
        push PrefixMapStack.output (fun _ => b)
          (goto fun _ => SuffixMapLabel.moveTemp)

def suffixListMapCfg (α β : Type) [Fintype α] [Fintype β]
    (suffList : List β) (mapSym : α → β) (label : SuffixMapLabel β)
    (state : Option β) (input : List α) (output temp : List β) :
    (suffixListMapMachine α β suffList mapSym).Cfg where
  l := some label
  var := state
  stk
    | PrefixMapStack.input => input
    | PrefixMapStack.output => output
    | PrefixMapStack.temp => temp

def suffixListMapHalt (α β : Type) [Fintype α] [Fintype β]
    (suffList : List β) (mapSym : α → β) (output : List β) :
    (suffixListMapMachine α β suffList mapSym).Cfg where
  l := none
  var := none
  stk
    | PrefixMapStack.input => []
    | PrefixMapStack.output => output
    | PrefixMapStack.temp => []

lemma suffixListMap_readInput_step_cons (α β : Type) [Fintype α] [Fintype β]
    (suffList : List β) (mapSym : α → β) (state : Option β)
    (a : α) (input : List α) (output temp : List β) :
    (suffixListMapMachine α β suffList mapSym).step
        (suffixListMapCfg α β suffList mapSym SuffixMapLabel.readInput state
          (a :: input) output temp) =
      some (suffixListMapCfg α β suffList mapSym (SuffixMapLabel.pushTemp (mapSym a))
        (some (mapSym a)) input output temp) := by
  simp [suffixListMapMachine, suffixListMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma suffixListMap_readInput_step_nil (α β : Type) [Fintype α] [Fintype β]
    (suffList : List β) (mapSym : α → β) (state : Option β) (output temp : List β) :
    (suffixListMapMachine α β suffList mapSym).step
        (suffixListMapCfg α β suffList mapSym SuffixMapLabel.readInput state
          [] output temp) =
      some (suffixListMapCfg α β suffList mapSym SuffixMapLabel.writeSuffix none
        [] output temp) := by
  simp [suffixListMapMachine, suffixListMapCfg]
  congr

lemma suffixListMap_pushTemp_step (α β : Type) [Fintype α] [Fintype β]
    (suffList : List β) (mapSym : α → β) (state : Option β)
    (b : β) (input : List α) (output temp : List β) :
    (suffixListMapMachine α β suffList mapSym).step
        (suffixListMapCfg α β suffList mapSym (SuffixMapLabel.pushTemp b) state
          input output temp) =
      some (suffixListMapCfg α β suffList mapSym SuffixMapLabel.readInput state
        input output (b :: temp)) := by
  simp [suffixListMapMachine, suffixListMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma suffixListMap_writeSuffix_step (α β : Type) [Fintype α] [Fintype β]
    (suffList : List β) (mapSym : α → β) (state : Option β)
    (input : List α) (output temp : List β) :
    (suffixListMapMachine α β suffList mapSym).step
        (suffixListMapCfg α β suffList mapSym SuffixMapLabel.writeSuffix state
          input output temp) =
      some (suffixListMapCfg α β suffList mapSym SuffixMapLabel.moveTemp state input
        (suffList ++ output) temp) := by
  simp [suffixListMapMachine, suffixListMapCfg]
  congr
  have hStep :
      Turing.TM2.stepAux
          (pushAllSuffixMapOutput suffList.reverse
            (goto fun _ : Option β => SuffixMapLabel.moveTemp))
          state
          (fun
            | PrefixMapStack.input => input
            | PrefixMapStack.output => output
            | PrefixMapStack.temp => temp) =
        (⟨some SuffixMapLabel.moveTemp, state,
          Function.update
            (fun
              | PrefixMapStack.input => input
              | PrefixMapStack.output => output
              | PrefixMapStack.temp => temp)
            PrefixMapStack.output (suffList ++ output)⟩ :
          (suffixListMapMachine α β suffList mapSym).Cfg) := by
    convert
      stepAux_pushAllSuffixMapOutput (α := α) (β := β) suffList state
        (fun
          | PrefixMapStack.input => input
          | PrefixMapStack.output => output
          | PrefixMapStack.temp => temp) using 1
    · congr
      funext k
      cases k <;> rfl
  have hCfg :
      (⟨some SuffixMapLabel.moveTemp, state,
        Function.update
          (fun
            | PrefixMapStack.input => input
            | PrefixMapStack.output => output
            | PrefixMapStack.temp => temp)
          PrefixMapStack.output (suffList ++ output)⟩ :
        (suffixListMapMachine α β suffList mapSym).Cfg) =
      suffixListMapCfg α β suffList mapSym SuffixMapLabel.moveTemp state input
        (suffList ++ output) temp := by
    dsimp [suffixListMapCfg]
    congr
    funext k
    cases k <;> simp [Function.update]
  convert hStep.trans hCfg using 1
  · congr
    funext k
    cases k <;> rfl

lemma suffixListMap_moveTemp_step_cons (α β : Type) [Fintype α] [Fintype β]
    (suffList : List β) (mapSym : α → β) (state : Option β)
    (input : List α) (output : List β) (b : β) (temp : List β) :
    (suffixListMapMachine α β suffList mapSym).step
        (suffixListMapCfg α β suffList mapSym SuffixMapLabel.moveTemp state input output
          (b :: temp)) =
      some (suffixListMapCfg α β suffList mapSym (SuffixMapLabel.pushOutput b) (some b)
        input output temp) := by
  simp [suffixListMapMachine, suffixListMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma suffixListMap_moveTemp_step_nil (α β : Type) [Fintype α] [Fintype β]
    (suffList : List β) (mapSym : α → β) (state : Option β) (output : List β) :
    (suffixListMapMachine α β suffList mapSym).step
        (suffixListMapCfg α β suffList mapSym SuffixMapLabel.moveTemp state [] output []) =
      some (suffixListMapHalt α β suffList mapSym output) := by
  simp [suffixListMapMachine, suffixListMapCfg, suffixListMapHalt]
  congr

lemma suffixListMap_pushOutput_step (α β : Type) [Fintype α] [Fintype β]
    (suffList : List β) (mapSym : α → β) (state : Option β)
    (input : List α) (output : List β) (b : β) (temp : List β) :
    (suffixListMapMachine α β suffList mapSym).step
        (suffixListMapCfg α β suffList mapSym (SuffixMapLabel.pushOutput b) state
          input output temp) =
      some (suffixListMapCfg α β suffList mapSym SuffixMapLabel.moveTemp state input
        (b :: output) temp) := by
  simp [suffixListMapMachine, suffixListMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma initList_suffixListMapMachine (α β : Type) [Fintype α] [Fintype β]
    (suffList : List β) (mapSym : α → β) (input : List α) :
    Turing.initList (suffixListMapMachine α β suffList mapSym) input =
      suffixListMapCfg α β suffList mapSym SuffixMapLabel.readInput none input [] [] := by
  simp [suffixListMapMachine, suffixListMapCfg, Turing.initList]
  congr
  funext k
  cases k <;> rfl

lemma haltList_suffixListMapMachine (α β : Type) [Fintype α] [Fintype β]
    (suffList : List β) (mapSym : α → β) (output : List β) :
    Turing.haltList (suffixListMapMachine α β suffList mapSym) output =
      suffixListMapHalt α β suffList mapSym output := by
  simp [suffixListMapMachine, suffixListMapHalt, Turing.haltList]
  congr
  funext k
  cases k <;> rfl

def suffixListMap_readInput_run (α β : Type) [Fintype α] [Fintype β]
    (suffList : List β) (mapSym : α → β) (state : Option β)
    (input : List α) (output temp : List β) :
    StateTransition.EvalsToInTime (suffixListMapMachine α β suffList mapSym).step
      (suffixListMapCfg α β suffList mapSym SuffixMapLabel.readInput state input output temp)
      (some (suffixListMapCfg α β suffList mapSym SuffixMapLabel.writeSuffix none
        [] output ((input.map mapSym).reverse ++ temp)))
      (2 * input.length + 1) := by
  induction input generalizing state temp with
  | nil =>
      simpa using
        evalsToInTimeOne
          (suffixListMap_readInput_step_nil α β suffList mapSym state output temp)
  | cons a input ih =>
      let tm := suffixListMapMachine α β suffList mapSym
      let c₀ := suffixListMapCfg α β suffList mapSym SuffixMapLabel.readInput state
        (a :: input) output temp
      let c₁ := suffixListMapCfg α β suffList mapSym (SuffixMapLabel.pushTemp (mapSym a))
        (some (mapSym a)) input output temp
      let c₂ := suffixListMapCfg α β suffList mapSym SuffixMapLabel.readInput
        (some (mapSym a)) input output (mapSym a :: temp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (suffixListMap_readInput_step_cons α β suffList mapSym state a input output temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (suffixListMap_pushTemp_step α β suffList mapSym (some (mapSym a))
            (mapSym a) input output temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (suffixListMapCfg α β suffList mapSym SuffixMapLabel.writeSuffix none
            [] output ((input.map mapSym).reverse ++ (mapSym a :: temp))))
          (2 * input.length + 1) :=
        ih (some (mapSym a)) (mapSym a :: temp)
      simpa [tm, c₀, c₁, c₂, List.map_cons, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * input.length + 1)
          c₀ c₂
          (some (suffixListMapCfg α β suffList mapSym SuffixMapLabel.writeSuffix none
            [] output ((input.map mapSym).reverse ++ (mapSym a :: temp))))
          h₁₂ hTail

def suffixListMap_moveTemp_run (α β : Type) [Fintype α] [Fintype β]
    (suffList : List β) (mapSym : α → β) (state : Option β)
    (output temp : List β) :
    StateTransition.EvalsToInTime (suffixListMapMachine α β suffList mapSym).step
      (suffixListMapCfg α β suffList mapSym SuffixMapLabel.moveTemp state [] output temp)
      (some (suffixListMapHalt α β suffList mapSym (temp.reverse ++ output)))
      (2 * temp.length + 1) := by
  induction temp generalizing state output with
  | nil =>
      simpa using
        evalsToInTimeOne
          (suffixListMap_moveTemp_step_nil α β suffList mapSym state output)
  | cons b temp ih =>
      let tm := suffixListMapMachine α β suffList mapSym
      let c₀ := suffixListMapCfg α β suffList mapSym SuffixMapLabel.moveTemp state
        [] output (b :: temp)
      let c₁ := suffixListMapCfg α β suffList mapSym (SuffixMapLabel.pushOutput b)
        (some b) [] output temp
      let c₂ := suffixListMapCfg α β suffList mapSym SuffixMapLabel.moveTemp
        (some b) [] (b :: output) temp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (suffixListMap_moveTemp_step_cons α β suffList mapSym state [] output b temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (suffixListMap_pushOutput_step α β suffList mapSym (some b) [] output b temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (suffixListMapHalt α β suffList mapSym (temp.reverse ++ (b :: output))))
          (2 * temp.length + 1) := by
        simpa [c₂] using ih (some b) (b :: output)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * temp.length + 1)
          c₀ c₂
          (some (suffixListMapHalt α β suffList mapSym
            (temp.reverse ++ (b :: output))))
          h₁₂ hTail

/-- The fixed-suffList map program computes `input ↦ input.map mapSym ++ suffList`. -/
def suffixListMap_outputs (α β : Type) [Fintype α] [Fintype β]
    (suffList : List β) (mapSym : α → β) (input : List α) :
    Turing.TM2OutputsInTime (suffixListMapMachine α β suffList mapSym)
      input (some (input.map mapSym ++ suffList)) (4 * input.length + 3) := by
  let tm := suffixListMapMachine α β suffList mapSym
  let mapped := input.map mapSym
  let mid₁ := suffixListMapCfg α β suffList mapSym SuffixMapLabel.writeSuffix none
    [] [] mapped.reverse
  let mid₂ := suffixListMapCfg α β suffList mapSym SuffixMapLabel.moveTemp none
    [] suffList mapped.reverse
  let done := suffixListMapHalt α β suffList mapSym (mapped ++ suffList)
  have hRead : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some mid₁) (2 * input.length + 1) := by
    simpa [tm, mid₁, mapped, initList_suffixListMapMachine] using
      suffixListMap_readInput_run α β suffList mapSym none input [] []
  have hSuffix : StateTransition.EvalsToInTime tm.step mid₁
      (some mid₂) 1 := by
    simpa [tm, mid₁, mid₂, mapped] using
      evalsToInTimeOne
        (suffixListMap_writeSuffix_step α β suffList mapSym none [] [] mapped.reverse)
  have hMove : StateTransition.EvalsToInTime tm.step mid₂
      (some done) (2 * input.length + 1) := by
    simpa [tm, mid₂, done, mapped, List.length_reverse, List.append_assoc] using
      suffixListMap_moveTemp_run α β suffList mapSym none suffList mapped.reverse
  have hReadSuffix : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some mid₂) (1 + (2 * input.length + 1)) :=
    StateTransition.EvalsToInTime.trans tm.step (2 * input.length + 1) 1
      (Turing.initList tm input) mid₁ (some mid₂) hRead hSuffix
  have hAll : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some done) ((2 * input.length + 1) + (1 + (2 * input.length + 1))) :=
    StateTransition.EvalsToInTime.trans tm.step (1 + (2 * input.length + 1))
      (2 * input.length + 1) (Turing.initList tm input) mid₂ (some done)
      hReadSuffix hMove
  change StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
    (some (Turing.haltList tm (mapped ++ suffList))) (4 * input.length + 3)
  rw [haltList_suffixListMapMachine]
  convert hAll using 1
  omega

/-- TM2 polynomial-time computation of the singleton-list map `x ↦ [x]`. -/
noncomputable def listSingletonComputableInPolyTime (X : EncodedType) :
    Turing.TM2ComputableInPolyTime X.encode (EncodedType.list X).encode
      (fun x : X.Carrier => [x]) where
  tm := suffixListMapMachine X.Symbol (Option X.Symbol) [none] some
  inputAlphabet := Equiv.refl X.Symbol
  outputAlphabet := Equiv.refl (Option X.Symbol)
  time := 4 * Polynomial.X + 3
  outputsFun x := by
    convert
      suffixListMap_outputs X.Symbol (Option X.Symbol) [none] some (X.encode x) using 1
    · change List.map id (X.encode x) = X.encode x
      simp
    · change
        some (List.map id ((EncodedType.list X).encode [x])) =
          some ((X.encode x).map some ++ [none])
      simp [EncodedType.list]
    · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]

/--
TM2 polynomial-time computation of the structural product map `x ↦ (x, y)` when
the fixed right component has empty encoding.
-/
noncomputable def prodRightConstEmptyIdComputableInPolyTime
    (X Y : EncodedType) (y : Y.Carrier) (hy : Y.encode y = []) :
    Turing.TM2ComputableInPolyTime X.encode (EncodedType.prod X Y).encode
      (fun x : X.Carrier => (x, y)) where
  tm :=
    suffixMapMachine X.Symbol (Option (X.Symbol ⊕ Y.Symbol))
      none (fun s => some (Sum.inl s))
  inputAlphabet := Equiv.cast rfl
  outputAlphabet := Equiv.cast rfl
  time := 4 * Polynomial.X + 3
  outputsFun x := by
    convert
      suffixMap_outputs X.Symbol (Option (X.Symbol ⊕ Y.Symbol))
        none (fun s => some (Sum.inl s))
        (List.map (Equiv.cast rfl).invFun (X.encode x)) using 1
    ·
      have hNone :
          (Equiv.cast rfl).symm (none : Option (X.Symbol ⊕ Y.Symbol)) = none := by
        rfl
      have hSome :
          ∀ a : X.Symbol,
            (Equiv.cast rfl).symm (some (Sum.inl a : X.Symbol ⊕ Y.Symbol)) =
              some (Sum.inl a : X.Symbol ⊕ Y.Symbol) := by
        intro a
        rfl
      simp [EncodedType.prod, hy, Function.comp_def]
      induction X.encode x with
      | nil =>
          simpa only [List.map_nil, List.nil_append] using congrArg (fun z => [z]) hNone
      | cons a xs ih =>
          simp only [List.map_cons]
          congr
    · simp

/--
TM2 polynomial-time computation of the structural product map `x ↦ (x, y)` for
an arbitrary fixed right component.

This is still only a direct `prod_mk` structural subcase: it pairs the identity
map with a fixed constant by writing the retagged input, the product delimiter,
and the fixed right encoding.
-/
noncomputable def prodRightConstIdComputableInPolyTime
    (X Y : EncodedType) (y : Y.Carrier) :
    Turing.TM2ComputableInPolyTime X.encode (EncodedType.prod X Y).encode
      (fun x : X.Carrier => (x, y)) where
  tm :=
    suffixListMapMachine X.Symbol (Option (X.Symbol ⊕ Y.Symbol))
      ([none] ++ (Y.encode y).map (fun s => some (Sum.inr s)))
      (fun s => some (Sum.inl s))
  inputAlphabet := Equiv.refl X.Symbol
  outputAlphabet := Equiv.refl (Option (X.Symbol ⊕ Y.Symbol))
  time := 4 * Polynomial.X + 3
  outputsFun x := by
    convert
      suffixListMap_outputs X.Symbol (Option (X.Symbol ⊕ Y.Symbol))
        ([none] ++ (Y.encode y).map (fun s => some (Sum.inr s)))
        (fun s => some (Sum.inl s))
        (X.encode x) using 1
    · change List.map id (X.encode x) = X.encode x
      simp
    · change
        some (List.map id ((EncodedType.prod X Y).encode (x, y))) =
          some
            ((X.encode x).map (fun s : X.Symbol => some (Sum.inl s : X.Symbol ⊕ Y.Symbol)) ++
              ([none] ++
                (Y.encode y).map (fun s : Y.Symbol => some (Sum.inr s : X.Symbol ⊕ Y.Symbol))))
      simp [EncodedType.prod]
    · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]


end TM2Programs
end ComplexityReduction
