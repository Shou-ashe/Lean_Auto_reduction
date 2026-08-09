import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.Base

namespace ComplexityReduction
namespace TM2Programs

open Turing.TM2.Stmt

/-!
Finite single-symbol lookup programs.

The input encoding is a singleton symbol `[a]`; after reading that symbol the
machine clears the input and writes the fixed output block associated with `a`.
-/

inductive FiniteLookupStack where
  | input
  | output
  deriving DecidableEq, Fintype

abbrev finiteLookupAlphabet (α β : Type) : FiniteLookupStack → Type
  | FiniteLookupStack.input => α
  | FiniteLookupStack.output => β

inductive FiniteLookupLabel (α : Type) where
  | readInput
  | write (a : α)
  | invalid
  deriving DecidableEq, Fintype

def finiteLookupPushAll {α β : Type} :
    List β →
      Turing.TM2.Stmt (finiteLookupAlphabet α β) (FiniteLookupLabel α) (Option α) →
      Turing.TM2.Stmt (finiteLookupAlphabet α β) (FiniteLookupLabel α) (Option α)
  | [], q => q
  | b :: bs, q => push FiniteLookupStack.output (fun _ => b) (finiteLookupPushAll bs q)

def finiteLookupMachine (α β : Type) [Fintype α] [Fintype β]
    (block : α → List β) : Turing.FinTM2 where
  K := FiniteLookupStack
  k₀ := FiniteLookupStack.input
  k₁ := FiniteLookupStack.output
  Γ := finiteLookupAlphabet α β
  Λ := FiniteLookupLabel α
  main := FiniteLookupLabel.readInput
  σ := Option α
  initialState := none
  Γk₀Fin := by
    dsimp [finiteLookupAlphabet]
    infer_instance
  m
    | FiniteLookupLabel.readInput =>
        pop FiniteLookupStack.input (fun _ head => head)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some a => FiniteLookupLabel.write a
              | none => FiniteLookupLabel.invalid)
            (goto fun _ => FiniteLookupLabel.invalid))
    | FiniteLookupLabel.write a =>
        finiteLookupPushAll (block a).reverse (load (fun _ => none) halt)
    | FiniteLookupLabel.invalid =>
        halt

def finiteLookupStacks (α β : Type) (input : List α) (output : List β) :
    (k : FiniteLookupStack) → List (finiteLookupAlphabet α β k)
  | FiniteLookupStack.input => input
  | FiniteLookupStack.output => output

def finiteLookupCfg (α β : Type) [Fintype α] [Fintype β]
    (block : α → List β) (label : FiniteLookupLabel α) (state : Option α)
    (input : List α) (output : List β) :
    (finiteLookupMachine α β block).Cfg where
  l := some label
  var := state
  stk := finiteLookupStacks α β input output

def finiteLookupHalt (α β : Type) [Fintype α] [Fintype β]
    (block : α → List β) (output : List β) :
    (finiteLookupMachine α β block).Cfg where
  l := none
  var := none
  stk := finiteLookupStacks α β [] output

@[simp]
theorem initList_finiteLookupMachine (α β : Type) [Fintype α] [Fintype β]
    (block : α → List β) (input : List α) :
    Turing.initList (finiteLookupMachine α β block) input =
      finiteLookupCfg α β block FiniteLookupLabel.readInput none input [] := by
  simp [finiteLookupMachine, finiteLookupCfg, Turing.initList]
  congr
  funext k
  cases k <;> rfl

@[simp]
theorem haltList_finiteLookupMachine (α β : Type) [Fintype α] [Fintype β]
    (block : α → List β) (output : List β) :
    Turing.haltList (finiteLookupMachine α β block) output =
      finiteLookupHalt α β block output := by
  simp [finiteLookupMachine, finiteLookupHalt, Turing.haltList]
  congr
  funext k
  cases k <;> rfl

theorem finiteLookup_read_step (α β : Type) [Fintype α] [Fintype β]
    (block : α → List β) (a : α) :
    (finiteLookupMachine α β block).step
        (finiteLookupCfg α β block FiniteLookupLabel.readInput none [a] []) =
      some (finiteLookupCfg α β block (FiniteLookupLabel.write a) (some a) [] []) := by
  simp [finiteLookupMachine, finiteLookupCfg, finiteLookupStacks]
  congr
  funext k
  cases k <;> rfl

lemma finiteLookup_stepAux_pushAll {α β : Type} (out : List β) (state : Option α)
    (stk : (k : FiniteLookupStack) → List (finiteLookupAlphabet α β k)) :
    Turing.TM2.stepAux (K := FiniteLookupStack)
      (finiteLookupPushAll (α := α) (β := β) out.reverse
        (load (fun _ : Option α => none) halt))
      state stk =
    { l := none, var := none,
      stk := Function.update stk FiniteLookupStack.output
        (out ++ stk FiniteLookupStack.output) } := by
  induction out using List.reverseRecOn generalizing stk with
  | nil =>
      simp [finiteLookupPushAll]
  | append_singleton xs x ih =>
      simp [finiteLookupPushAll, List.reverse_append, ih, List.append_assoc]

theorem finiteLookup_write_step (α β : Type) [Fintype α] [Fintype β]
    (block : α → List β) (a : α) :
    (finiteLookupMachine α β block).step
        (finiteLookupCfg α β block (FiniteLookupLabel.write a) (some a) [] []) =
      some (finiteLookupHalt α β block (block a)) := by
  simp [finiteLookupMachine, finiteLookupCfg, finiteLookupHalt]
  apply congrArg some
  refine
    (finiteLookup_stepAux_pushAll (α := α) (β := β) (out := block a)
      (state := some a) (stk := finiteLookupStacks α β [] [])).trans ?_
  congr
  funext k
  cases k <;> simp [finiteLookupStacks, Function.update]

def finiteLookup_outputs (α β : Type) [Fintype α] [Fintype β]
    (block : α → List β) (a : α) :
    Turing.TM2OutputsInTime (finiteLookupMachine α β block)
      [a] (some (block a)) 2 := by
  let tm := finiteLookupMachine α β block
  let c₁ := finiteLookupCfg α β block (FiniteLookupLabel.write a) (some a) [] []
  have hRead : StateTransition.EvalsToInTime tm.step (Turing.initList tm [a]) (some c₁) 1 := by
    simpa [tm, c₁] using evalsToInTimeOne (finiteLookup_read_step α β block a)
  have hWrite : StateTransition.EvalsToInTime tm.step c₁
      (some (Turing.haltList tm (block a))) 1 := by
    rw [haltList_finiteLookupMachine]
    simpa [tm, c₁] using evalsToInTimeOne (finiteLookup_write_step α β block a)
  unfold Turing.TM2OutputsInTime
  change StateTransition.EvalsToInTime tm.step (Turing.initList tm [a])
    (Option.map (Turing.haltList tm) (some (block a))) 2
  simpa [tm, c₁] using
    StateTransition.EvalsToInTime.trans tm.step 1 1
      (Turing.initList tm [a]) c₁ (some (Turing.haltList tm (block a))) hRead hWrite

/-- TM2 polynomial-time computation of any map out of a singleton-symbol finite encoding. -/
noncomputable def finiteSymbolComputableInPolyTime
    (α : Type) [Fintype α] (Y : EncodedType) (f : α → Y.Carrier) :
    Turing.TM2ComputableInPolyTime
      (fun a : α => [a]) Y.encode f where
  tm := finiteLookupMachine α Y.Symbol (fun a => Y.encode (f a))
  inputAlphabet := Equiv.refl α
  outputAlphabet := Equiv.refl Y.Symbol
  time := Polynomial.C 2
  outputsFun a := by
    have hMapReflInv :
        ∀ {γ : Type} (xs : List γ), List.map (Equiv.refl γ).invFun xs = xs := by
      intro γ xs
      induction xs with
      | nil => rfl
      | cons b bs ih =>
          rw [List.map_cons, ih]
          rfl
    have hInput :
        List.map (Equiv.refl α).invFun ([a] : List α) = [a] :=
      hMapReflInv [a]
    have hOutput :
        List.map (Equiv.refl Y.Symbol).invFun (Y.encode (f a)) = Y.encode (f a) :=
      hMapReflInv (Y.encode (f a))
    have h := finiteLookup_outputs α Y.Symbol (fun a => Y.encode (f a)) a
    unfold Turing.TM2OutputsInTime at h ⊢
    convert h using 1
    · exact congrArg (fun xs : List Y.Symbol =>
        Option.map (Turing.haltList (finiteLookupMachine α Y.Symbol
          (fun a => Y.encode (f a)))) (some xs)) hOutput
    · simp

end TM2Programs
end ComplexityReduction
