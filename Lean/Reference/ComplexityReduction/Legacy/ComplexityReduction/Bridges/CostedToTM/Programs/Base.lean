/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Status

namespace ComplexityReduction

namespace TM2Programs

open Turing.TM2.Stmt

/-- Build a one-step `EvalsToInTime` proof from a concrete step equation. -/
def evalsToInTimeOne {σ : Type} {f : σ → Option σ} {a b : σ}
    (h : f a = some b) : StateTransition.EvalsToInTime f a (some b) 1 := by
  refine
    { steps := 1
      evals_in_steps := ?_
      steps_le_m := le_rfl }
  simpa using h

def evalsToInTime_mono {σ : Type} {f : σ → Option σ} {a : σ} {b : Option σ}
    {m n : Nat} (h : StateTransition.EvalsToInTime f a b m) (hmn : m ≤ n) :
    StateTransition.EvalsToInTime f a b n :=
  { h with steps_le_m := le_trans h.steps_le_m hmn }

/--
TM2 polynomial-time computation for maps whose target encoding is obtained from
the source encoding by a fixed alphabet equivalence.

This is a direct identity-machine subcase; it does not use or prove arbitrary
composition.
-/
noncomputable def encodingEquivComputableInPolyTime
    (X Y : EncodedType) (f : X.Carrier → Y.Carrier) (e : X.Symbol ≃ Y.Symbol)
    (hf : ∀ x, Y.encode (f x) = (X.encode x).map e) :
    Turing.TM2ComputableInPolyTime X.encode Y.encode f where
  tm := Turing.idComputer X.Symbol
  inputAlphabet := Equiv.refl X.Symbol
  outputAlphabet := e
  time := 1
  outputsFun x := by
    have hOut : List.map e.invFun (Y.encode (f x)) = X.encode x := by
      rw [hf x]
      simp
    have hEval :
        Turing.TM2OutputsInTime (Turing.idComputer X.Symbol)
          (X.encode x) (some (X.encode x)) 1 :=
      { steps := 1
        evals_in_steps := rfl
        steps_le_m := by simp }
    convert hEval using 1
    · induction X.encode x with
      | nil =>
          rfl
      | cons a xs ih =>
          simp only [List.map_cons]
          congr
    · exact congrArg some hOut
    · simp

/-- Shared finite stack alphabet for two-stack constant-output programs. -/
abbrev constOutputAlphabet (αΓ βΓ : Type) : Bool → Type
  | false => αΓ
  | true => βΓ

/-- Add a fixed list of output symbols to the output stack using nested TM2 pushes. -/
def pushAllOutput {αΓ βΓ : Type} :
    List βΓ →
      Turing.TM2.Stmt (constOutputAlphabet αΓ βΓ) Bool Bool →
      Turing.TM2.Stmt (constOutputAlphabet αΓ βΓ) Bool Bool
  | [], q => q
  | b :: bs, q => push true (fun _ => b) (pushAllOutput bs q)

/--
A small TM2 program that repeatedly pops the input stack until it is empty and
then halts with an empty output stack.
-/
def clearInputEmptyOutputMachine (αΓ βΓ : Type) [Fintype αΓ] : Turing.FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ
    | false => αΓ
    | true => βΓ
  Λ := Bool
  main := false
  σ := Bool
  initialState := false
  m
    | false =>
        pop false (fun _ head => head.isNone)
          (branch id (goto fun _ => true) (goto fun _ => false))
    | true =>
        load (fun _ => false) halt

/-- The intermediate configuration after the input stack has been cleared. -/
def clearInputEmptyOutputAfterClear (αΓ βΓ : Type) [Fintype αΓ] :
    (clearInputEmptyOutputMachine αΓ βΓ).Cfg where
  l := some true
  var := true
  stk _ := []

/-- The clear-input machine halts with an empty output in `input.length + 2` steps. -/
def clearInputEmptyOutput_outputs (αΓ βΓ : Type) [Fintype αΓ] (l : List αΓ) :
    Turing.TM2OutputsInTime (clearInputEmptyOutputMachine αΓ βΓ)
      l (some ([] : List βΓ)) (l.length + 2) := by
  induction l with
  | nil =>
      let tm := clearInputEmptyOutputMachine αΓ βΓ
      let mid := clearInputEmptyOutputAfterClear αΓ βΓ
      have hClear : StateTransition.EvalsToInTime tm.step (Turing.initList tm [])
          (some mid) 1 := by
        refine
          { steps := 1
            evals_in_steps := ?_
            steps_le_m := le_rfl }
        change tm.step (Turing.initList tm []) = some mid
        simp [tm, mid, clearInputEmptyOutputMachine, clearInputEmptyOutputAfterClear,
          Turing.initList]
        congr
        funext k
        cases k <;> rfl
      have hHalt : StateTransition.EvalsToInTime tm.step mid
          (Option.map (Turing.haltList tm) (some ([] : List βΓ))) 1 := by
        refine
          { steps := 1
            evals_in_steps := ?_
            steps_le_m := le_rfl }
        change tm.step mid = Option.map (Turing.haltList tm) (some ([] : List βΓ))
        simp [tm, mid, clearInputEmptyOutputMachine, clearInputEmptyOutputAfterClear,
          Turing.haltList]
        congr
        funext k
        cases k <;> rfl
      simpa [tm, mid] using
        StateTransition.EvalsToInTime.trans tm.step 1 1 (Turing.initList tm []) mid
          (Option.map (Turing.haltList tm) (some ([] : List βΓ))) hClear hHalt
  | cons a l ih =>
      let tm := clearInputEmptyOutputMachine αΓ βΓ
      have hStep : StateTransition.EvalsToInTime tm.step (Turing.initList tm (a :: l))
          (some (Turing.initList tm l)) 1 := by
        refine
          { steps := 1
            evals_in_steps := ?_
            steps_le_m := le_rfl }
        change tm.step (Turing.initList tm (a :: l)) = some (Turing.initList tm l)
        simp [tm, clearInputEmptyOutputMachine, Turing.initList]
        congr
        funext k
        cases k <;> rfl
      have hTail : StateTransition.EvalsToInTime tm.step (Turing.initList tm l)
          (Option.map (Turing.haltList tm) (some ([] : List βΓ))) (l.length + 2) := ih
      simpa [tm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step 1 (l.length + 2)
          (Turing.initList tm (a :: l)) (Turing.initList tm l)
          (Option.map (Turing.haltList tm) (some ([] : List βΓ))) hStep hTail

/--
TM2 polynomial-time computation of a constant whose output encoding is empty.
This is a proved subcase of the generic `const_map` closure obligation.
-/
noncomputable def constEmptyEncodingComputableInPolyTime
    (X Y : EncodedType) (y : Y.Carrier) (hy : Y.encode y = []) :
    Turing.TM2ComputableInPolyTime X.encode Y.encode (fun _ : X.Carrier => y) where
  tm := clearInputEmptyOutputMachine X.Symbol Y.Symbol
  inputAlphabet := Equiv.cast rfl
  outputAlphabet := Equiv.cast rfl
  time := Polynomial.X + 2
  outputsFun x := by
    convert
      clearInputEmptyOutput_outputs X.Symbol Y.Symbol
        (List.map (Equiv.cast rfl).invFun (X.encode x)) using 1
    · rw [hy]
      rfl
    · simp

/--
TM2 polynomial-time computation of any function whose output encoding is always
empty.  This is a current-encoding theorem; it does not assert that the encoding
faithfully represents the natural-language target problem.
-/
noncomputable def emptyOutputComputableInPolyTime
    (X Y : EncodedType) (f : X.Carrier → Y.Carrier)
    (hf : ∀ x, Y.encode (f x) = []) :
    Turing.TM2ComputableInPolyTime X.encode Y.encode f where
  tm := clearInputEmptyOutputMachine X.Symbol Y.Symbol
  inputAlphabet := Equiv.cast rfl
  outputAlphabet := Equiv.cast rfl
  time := Polynomial.X + 2
  outputsFun x := by
    convert
      clearInputEmptyOutput_outputs X.Symbol Y.Symbol
        (List.map (Equiv.cast rfl).invFun (X.encode x)) using 1
    · rw [hf x]
      rfl
    · simp

/--
A TM2 program that clears the input stack and then writes a fixed output string
to the output stack.
-/
def constOutputMachine (αΓ βΓ : Type) [Fintype αΓ] (out : List βΓ) :
    Turing.FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := constOutputAlphabet αΓ βΓ
  Λ := Bool
  main := false
  σ := Bool
  initialState := false
  Γk₀Fin := by
    dsimp [constOutputAlphabet]
    infer_instance
  m
    | false =>
        pop false (fun _ head => head.isNone)
          (branch id (goto fun _ => true) (goto fun _ => false))
    | true =>
        pushAllOutput out.reverse (load (fun _ => false) halt)

/-- The intermediate configuration after the input stack has been cleared. -/
def constOutputAfterClear (αΓ βΓ : Type) [Fintype αΓ] (out : List βΓ) :
    (constOutputMachine αΓ βΓ out).Cfg where
  l := some true
  var := true
  stk _ := []

/--
Executing the nested fixed-output statement prepends the fixed output to the
current output stack and halts.
-/
lemma stepAux_pushAllOutput {αΓ βΓ : Type} (out : List βΓ)
    (stk : (b : Bool) → List (constOutputAlphabet αΓ βΓ b)) :
    Turing.TM2.stepAux (K := Bool)
      (pushAllOutput (αΓ := αΓ) (βΓ := βΓ) out.reverse (load (fun _ : Bool => false) halt))
      true stk =
    { l := none, var := false,
      stk := Function.update stk true (out ++ stk true) } := by
  induction out using List.reverseRecOn generalizing stk with
  | nil =>
      simp [pushAllOutput]
  | append_singleton xs x ih =>
      simp [pushAllOutput, List.reverse_append, ih, List.append_assoc]

/-- The generic constant-output machine halts with the fixed output in `input.length + 2` steps. -/
def constOutput_outputs (αΓ βΓ : Type) [Fintype αΓ] (out : List βΓ) (l : List αΓ) :
    Turing.TM2OutputsInTime (constOutputMachine αΓ βΓ out)
      l (some out) (l.length + 2) := by
  induction l with
  | nil =>
      let tm := constOutputMachine αΓ βΓ out
      let mid := constOutputAfterClear αΓ βΓ out
      have hClear : StateTransition.EvalsToInTime tm.step (Turing.initList tm [])
          (some mid) 1 := by
        refine
          { steps := 1
            evals_in_steps := ?_
            steps_le_m := le_rfl }
        change tm.step (Turing.initList tm []) = some mid
        simp [tm, mid, constOutputMachine, constOutputAfterClear, Turing.initList]
        congr
        funext k
        cases k <;> rfl
      have hWrite : StateTransition.EvalsToInTime tm.step mid
          (Option.map (Turing.haltList tm) (some out)) 1 := by
        refine
          { steps := 1
            evals_in_steps := ?_
            steps_le_m := le_rfl }
        change tm.step mid = Option.map (Turing.haltList tm) (some out)
        simp [tm, mid, constOutputMachine, constOutputAfterClear, Turing.haltList]
        have hPush :=
          stepAux_pushAllOutput (αΓ := αΓ) (βΓ := βΓ) out (fun _ => [])
        refine (congrArg some hPush).trans ?_
        simp
        congr
        funext k
        cases k <;> rfl
      simpa [tm, mid] using
        StateTransition.EvalsToInTime.trans tm.step 1 1 (Turing.initList tm []) mid
          (Option.map (Turing.haltList tm) (some out)) hClear hWrite
  | cons a l ih =>
      let tm := constOutputMachine αΓ βΓ out
      have hStep : StateTransition.EvalsToInTime tm.step (Turing.initList tm (a :: l))
          (some (Turing.initList tm l)) 1 := by
        refine
          { steps := 1
            evals_in_steps := ?_
            steps_le_m := le_rfl }
        change tm.step (Turing.initList tm (a :: l)) = some (Turing.initList tm l)
        simp [tm, constOutputMachine, Turing.initList]
        congr
        funext k
        cases k <;> rfl
      have hTail : StateTransition.EvalsToInTime tm.step (Turing.initList tm l)
          (Option.map (Turing.haltList tm) (some out)) (l.length + 2) := ih
      simpa [tm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step 1 (l.length + 2)
          (Turing.initList tm (a :: l)) (Turing.initList tm l)
          (Option.map (Turing.haltList tm) (some out)) hStep hTail

/-- TM2 polynomial-time computation of an arbitrary constant map. -/
noncomputable def constComputableInPolyTime (X Y : EncodedType) (y : Y.Carrier) :
    Turing.TM2ComputableInPolyTime X.encode Y.encode (fun _ : X.Carrier => y) where
  tm := constOutputMachine X.Symbol Y.Symbol (Y.encode y)
  inputAlphabet := Equiv.cast rfl
  outputAlphabet := Equiv.cast rfl
  time := Polynomial.X + 2
  outputsFun x := by
    convert
      constOutput_outputs X.Symbol Y.Symbol (Y.encode y)
        (List.map (Equiv.cast rfl).invFun (X.encode x)) using 1
    · change some (List.map id (Y.encode y)) = some (Y.encode y)
      simp
    · simp

  /-- Stack indices for the unary natural-number equality program. -/
  inductive NatEqStack where
    | input
    | work
    | output
    deriving DecidableEq, Fintype

  /-- Stack alphabets for the unary natural-number equality program. -/
  abbrev natEqAlphabet : NatEqStack → Type
    | NatEqStack.input => Option (Bool ⊕ Bool)
    | NatEqStack.work => Unit
    | NatEqStack.output => Bool

  instance (k : NatEqStack) : Fintype (natEqAlphabet k) := by
    cases k
    · exact inferInstanceAs (Fintype (Option (Bool ⊕ Bool)))
    · exact inferInstanceAs (Fintype Unit)
    · exact inferInstanceAs (Fintype Bool)

  /-- Control labels for the unary natural-number equality program. -/
  inductive NatEqLabel where
    | readLeft
    | pushLeft
    | readRight
    | cancelRight
    | finish
    | clearWorkFalse
    | write
    deriving DecidableEq, Fintype

  /-- Finite control state for the unary natural-number equality program. -/
  inductive NatEqState where
    | readLeft (ok : Bool)
    | pushLeft (ok : Bool)
    | readRight (ok : Bool)
    | cancelRight (ok : Bool)
    | finish (ok : Bool)
    | clearWorkFalse
    | write (out : Bool)
    deriving DecidableEq, Fintype

  def NatEqState.label : NatEqState → NatEqLabel
    | .readLeft _ => .readLeft
    | .pushLeft _ => .pushLeft
    | .readRight _ => .readRight
    | .cancelRight _ => .cancelRight
    | .finish _ => .finish
    | .clearWorkFalse => .clearWorkFalse
    | .write _ => .write

  def NatEqState.output : NatEqState → Bool
    | .write out => out
    | .readLeft ok => ok
    | .pushLeft ok => ok
    | .readRight ok => ok
    | .cancelRight ok => ok
    | .finish ok => ok
    | .clearWorkFalse => false

  def natEqReadLeftAfterPop :
      NatEqState → Option (Option (Bool ⊕ Bool)) → NatEqState
    | .readLeft ok, some (some (Sum.inl true)) => .pushLeft ok
    | .readLeft ok, some (some (Sum.inl false)) => .readLeft ok
    | .readLeft ok, some none => .readRight ok
    | .readLeft _, _ => .readLeft false
    | state, _ => state

  def natEqAfterPushLeft : NatEqState → NatEqState
    | .pushLeft ok => .readLeft ok
    | state => state

  def natEqReadRightAfterPop :
      NatEqState → Option (Option (Bool ⊕ Bool)) → NatEqState
    | .readRight false, some (some (Sum.inr false)) => .finish false
    | .readRight false, none => .finish false
    | .readRight false, _ => .readRight false
    | .readRight true, some (some (Sum.inr true)) => .cancelRight true
    | .readRight true, some (some (Sum.inr false)) => .finish true
    | .readRight true, none => .finish true
    | .readRight true, _ => .readRight false
    | state, _ => state

  def natEqAfterCancelRight :
      NatEqState → Option Unit → NatEqState
    | .cancelRight ok, some _ => .readRight ok
    | .cancelRight _, none => .readRight false
    | state, _ => state

  def natEqAfterFinish : NatEqState → Option Unit → NatEqState
    | .finish ok, none => .write ok
    | .finish _, some _ => .clearWorkFalse
    | state, _ => state

  def natEqAfterClearWorkFalse : NatEqState → Option Unit → NatEqState
    | .clearWorkFalse, none => .write false
    | .clearWorkFalse, some _ => .clearWorkFalse
    | state, _ => state

  def natEqAfterWrite : NatEqState → NatEqState
    | .write _ => .readLeft true
    | state => state

  /--
  A concrete TM2 program deciding equality of two unary natural numbers encoded as
  `EncodedType.prod EncodedType.nat EncodedType.nat`.
  -/
  def natEqMachine : Turing.FinTM2 where
    K := NatEqStack
    k₀ := .input
    k₁ := .output
    Γ := natEqAlphabet
    Λ := NatEqLabel
    main := .readLeft
    σ := NatEqState
    initialState := .readLeft true
    m
      | .readLeft =>
          pop .input natEqReadLeftAfterPop
            (goto NatEqState.label)
      | .pushLeft =>
          push .work (fun _ => ())
            (load natEqAfterPushLeft (goto NatEqState.label))
      | .readRight =>
          pop .input natEqReadRightAfterPop
            (goto NatEqState.label)
      | .cancelRight =>
          pop .work natEqAfterCancelRight
            (goto NatEqState.label)
      | .finish =>
          pop .work natEqAfterFinish
            (goto NatEqState.label)
      | .clearWorkFalse =>
          pop .work natEqAfterClearWorkFalse
            (goto NatEqState.label)
      | .write =>
          push .output NatEqState.output
            (load natEqAfterWrite halt)

  def natEqCfg
      (label : Option NatEqLabel) (state : NatEqState)
      (input : List (Option (Bool ⊕ Bool))) (work : List Unit) (output : List Bool) :
      natEqMachine.Cfg where
    l := label
    var := state
    stk
      | .input => input
      | .work => work
      | .output => output

  lemma natEq_initList (input : List (Option (Bool ⊕ Bool))) :
      Turing.initList natEqMachine input =
        natEqCfg (some .readLeft) (.readLeft true) input [] [] := by
    simp [Turing.initList, natEqMachine, natEqCfg]
    congr
    funext k
    cases k <;> rfl

  lemma natEq_haltList (output : List Bool) :
      Turing.haltList natEqMachine output =
        natEqCfg none (.readLeft true) [] [] output := by
    simp [Turing.haltList, natEqMachine, natEqCfg]
    congr
    funext k
    cases k <;> rfl

  def natEqLeftTrue : Option (Bool ⊕ Bool) := some (Sum.inl true)
  def natEqLeftFalse : Option (Bool ⊕ Bool) := some (Sum.inl false)
  def natEqRightTrue : Option (Bool ⊕ Bool) := some (Sum.inr true)
  def natEqRightFalse : Option (Bool ⊕ Bool) := some (Sum.inr false)

  lemma natEq_readLeft_true_step (ok : Bool) (input : List (Option (Bool ⊕ Bool)))
      (work : List Unit) (output : List Bool) :
      natEqMachine.step
          (natEqCfg (some .readLeft) (.readLeft ok) (natEqLeftTrue :: input) work output) =
        some (natEqCfg (some .pushLeft) (.pushLeft ok) input work output) := by
    simp [natEqMachine, natEqCfg, natEqLeftTrue, natEqReadLeftAfterPop, NatEqState.label]
    congr
    funext k
    cases k <;> rfl

  lemma natEq_pushLeft_step (ok : Bool) (input : List (Option (Bool ⊕ Bool)))
      (work : List Unit) (output : List Bool) :
      natEqMachine.step
          (natEqCfg (some .pushLeft) (.pushLeft ok) input work output) =
        some (natEqCfg (some .readLeft) (.readLeft ok) input (() :: work) output) := by
    simp [natEqMachine, natEqCfg, natEqAfterPushLeft, NatEqState.label]
    congr
    funext k
    cases k <;> rfl

  lemma natEq_readLeft_false_step (ok : Bool) (input : List (Option (Bool ⊕ Bool)))
      (work : List Unit) (output : List Bool) :
      natEqMachine.step
          (natEqCfg (some .readLeft) (.readLeft ok) (natEqLeftFalse :: input) work output) =
        some (natEqCfg (some .readLeft) (.readLeft ok) input work output) := by
    simp [natEqMachine, natEqCfg, natEqLeftFalse, natEqReadLeftAfterPop, NatEqState.label]
    congr
    funext k
    cases k <;> rfl

  lemma natEq_readLeft_delim_step (ok : Bool) (input : List (Option (Bool ⊕ Bool)))
      (work : List Unit) (output : List Bool) :
      natEqMachine.step
          (natEqCfg (some .readLeft) (.readLeft ok) (none :: input) work output) =
        some (natEqCfg (some .readRight) (.readRight ok) input work output) := by
    simp [natEqMachine, natEqCfg, natEqReadLeftAfterPop, NatEqState.label]
    congr
    funext k
    cases k <;> rfl

  lemma natEq_readRight_true_ok_step (input : List (Option (Bool ⊕ Bool)))
      (work : List Unit) (output : List Bool) :
      natEqMachine.step
          (natEqCfg (some .readRight) (.readRight true) (natEqRightTrue :: input) work output) =
        some (natEqCfg (some .cancelRight) (.cancelRight true) input work output) := by
    simp [natEqMachine, natEqCfg, natEqRightTrue, natEqReadRightAfterPop,
      NatEqState.label]
    congr
    funext k
    cases k <;> rfl

  lemma natEq_readRight_true_bad_step (input : List (Option (Bool ⊕ Bool)))
      (work : List Unit) (output : List Bool) :
      natEqMachine.step
          (natEqCfg (some .readRight) (.readRight false) (natEqRightTrue :: input) work output) =
        some (natEqCfg (some .readRight) (.readRight false) input work output) := by
    simp [natEqMachine, natEqCfg, natEqRightTrue, natEqReadRightAfterPop,
      NatEqState.label]
    congr
    funext k
    cases k <;> rfl

  lemma natEq_cancelRight_cons_step (ok : Bool) (input : List (Option (Bool ⊕ Bool)))
      (work : List Unit) (output : List Bool) :
      natEqMachine.step
          (natEqCfg (some .cancelRight) (.cancelRight ok) input (() :: work) output) =
        some (natEqCfg (some .readRight) (.readRight ok) input work output) := by
    simp [natEqMachine, natEqCfg, natEqAfterCancelRight, NatEqState.label]
    congr
    funext k
    cases k <;> rfl

  lemma natEq_cancelRight_nil_step (ok : Bool) (input : List (Option (Bool ⊕ Bool)))
      (output : List Bool) :
      natEqMachine.step
          (natEqCfg (some .cancelRight) (.cancelRight ok) input [] output) =
        some (natEqCfg (some .readRight) (.readRight false) input [] output) := by
    simp [natEqMachine, natEqCfg, natEqAfterCancelRight, NatEqState.label]
    rfl

  lemma natEq_readRight_false_step (ok : Bool) (input : List (Option (Bool ⊕ Bool)))
      (work : List Unit) (output : List Bool) :
      natEqMachine.step
          (natEqCfg (some .readRight) (.readRight ok) (natEqRightFalse :: input) work output) =
        some (natEqCfg (some .finish) (.finish ok) input work output) := by
    cases ok <;>
      simp [natEqMachine, natEqCfg, natEqRightFalse, natEqReadRightAfterPop,
        NatEqState.label] <;>
      (congr; funext k; cases k <;> rfl)

  lemma natEq_finish_nil_step (ok : Bool) (output : List Bool) :
      natEqMachine.step
          (natEqCfg (some .finish) (.finish ok) [] [] output) =
        some (natEqCfg (some .write) (.write ok) [] [] output) := by
    simp [natEqMachine, natEqCfg, natEqAfterFinish, NatEqState.label]
    rfl

  lemma natEq_finish_cons_step (ok : Bool) (work : List Unit) (output : List Bool) :
      natEqMachine.step
          (natEqCfg (some .finish) (.finish ok) [] (() :: work) output) =
        some (natEqCfg (some .clearWorkFalse) .clearWorkFalse [] work output) := by
    simp [natEqMachine, natEqCfg, natEqAfterFinish, NatEqState.label]
    congr
    funext k
    cases k <;> rfl

  lemma natEq_clearWorkFalse_cons_step (work : List Unit) (output : List Bool) :
      natEqMachine.step
          (natEqCfg (some .clearWorkFalse) .clearWorkFalse [] (() :: work) output) =
        some (natEqCfg (some .clearWorkFalse) .clearWorkFalse [] work output) := by
    simp [natEqMachine, natEqCfg, natEqAfterClearWorkFalse, NatEqState.label]
    congr
    funext k
    cases k <;> rfl

  lemma natEq_clearWorkFalse_nil_step (output : List Bool) :
      natEqMachine.step
          (natEqCfg (some .clearWorkFalse) .clearWorkFalse [] [] output) =
        some (natEqCfg (some .write) (.write false) [] [] output) := by
    simp [natEqMachine, natEqCfg, natEqAfterClearWorkFalse, NatEqState.label]
    rfl

  lemma natEq_write_step (out : Bool) (output : List Bool) :
      natEqMachine.step
          (natEqCfg (some .write) (.write out) [] [] output) =
        some (natEqCfg none (.readLeft true) [] [] (out :: output)) := by
    simp [natEqMachine, natEqCfg, NatEqState.output, natEqAfterWrite]
    congr
    funext k
    cases k <;> rfl

  lemma natEq_replicateUnit_append_cons (n : Nat) (work : List Unit) :
      List.replicate n () ++ () :: work = () :: (List.replicate n () ++ work) := by
    induction n with
    | zero =>
        rfl
    | succ n ih =>
        simpa [List.replicate_succ, List.append_assoc] using congrArg (fun xs => () :: xs) ih

  def natEq_readLeftTrues_run (ok : Bool) (n : Nat)
      (input : List (Option (Bool ⊕ Bool))) (work : List Unit) (output : List Bool) :
      StateTransition.EvalsToInTime natEqMachine.step
        (natEqCfg (some .readLeft) (.readLeft ok)
          (List.replicate n natEqLeftTrue ++ input) work output)
        (some
          (natEqCfg (some .readLeft) (.readLeft ok) input
            (List.replicate n () ++ work) output))
        (2 * n) := by
    induction n generalizing work with
    | zero =>
        simpa using
          StateTransition.EvalsToInTime.refl natEqMachine.step
            (natEqCfg (some .readLeft) (.readLeft ok) input work output)
    | succ n ih =>
        let c₀ := natEqCfg (some .readLeft) (.readLeft ok)
          (natEqLeftTrue :: (List.replicate n natEqLeftTrue ++ input)) work output
        let c₁ := natEqCfg (some .pushLeft) (.pushLeft ok)
          (List.replicate n natEqLeftTrue ++ input) work output
        let c₂ := natEqCfg (some .readLeft) (.readLeft ok)
          (List.replicate n natEqLeftTrue ++ input) (() :: work) output
        let cDone := natEqCfg (some .readLeft) (.readLeft ok) input
          (List.replicate (n + 1) () ++ work) output
        have h₁ : StateTransition.EvalsToInTime natEqMachine.step c₀ (some c₁) 1 :=
          evalsToInTimeOne (natEq_readLeft_true_step ok
            (List.replicate n natEqLeftTrue ++ input) work output)
        have h₂ : StateTransition.EvalsToInTime natEqMachine.step c₁ (some c₂) 1 :=
          evalsToInTimeOne (natEq_pushLeft_step ok
            (List.replicate n natEqLeftTrue ++ input) work output)
        have h₁₂ : StateTransition.EvalsToInTime natEqMachine.step c₀ (some c₂) (1 + 1) :=
          StateTransition.EvalsToInTime.trans natEqMachine.step 1 1 c₀ c₁ (some c₂) h₁ h₂
        have hTail :
            StateTransition.EvalsToInTime natEqMachine.step c₂ (some cDone) (2 * n) := by
          simpa [c₂, cDone, List.replicate_succ, List.append_assoc,
            natEq_replicateUnit_append_cons] using
            ih (() :: work)
        have hAll :
            StateTransition.EvalsToInTime natEqMachine.step c₀ (some cDone)
              ((1 + 1) + 2 * n) :=
          evalsToInTime_mono
            (StateTransition.EvalsToInTime.trans natEqMachine.step (1 + 1) (2 * n)
              c₀ c₂ (some cDone) h₁₂ hTail)
            (by omega)
        simpa [c₀, cDone, List.replicate_succ, Nat.mul_add, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using hAll

  def natEq_badRightTrues_run (n : Nat)
      (input : List (Option (Bool ⊕ Bool))) (output : List Bool) :
      StateTransition.EvalsToInTime natEqMachine.step
        (natEqCfg (some .readRight) (.readRight false)
          (List.replicate n natEqRightTrue ++ input) [] output)
        (some (natEqCfg (some .readRight) (.readRight false) input [] output))
        n := by
    induction n with
    | zero =>
        simpa using
          StateTransition.EvalsToInTime.refl natEqMachine.step
            (natEqCfg (some .readRight) (.readRight false) input [] output)
    | succ n ih =>
        let c₀ := natEqCfg (some .readRight) (.readRight false)
          (natEqRightTrue :: (List.replicate n natEqRightTrue ++ input)) [] output
        let c₁ := natEqCfg (some .readRight) (.readRight false)
          (List.replicate n natEqRightTrue ++ input) [] output
        let cDone := natEqCfg (some .readRight) (.readRight false) input [] output
        have h₁ : StateTransition.EvalsToInTime natEqMachine.step c₀ (some c₁) 1 :=
          evalsToInTimeOne (natEq_readRight_true_bad_step
            (List.replicate n natEqRightTrue ++ input) [] output)
        have hTail : StateTransition.EvalsToInTime natEqMachine.step c₁ (some cDone) n := by
          simpa [c₁, cDone] using ih
        have hAll :
            StateTransition.EvalsToInTime natEqMachine.step c₀ (some cDone) (n + 1) :=
          StateTransition.EvalsToInTime.trans natEqMachine.step 1 n c₀ c₁ (some cDone)
            h₁ hTail
        simpa [c₀, cDone, List.replicate_succ] using hAll

  def natEq_clearWorkFalse_run (work : List Unit) (output : List Bool) :
      StateTransition.EvalsToInTime natEqMachine.step
        (natEqCfg (some .clearWorkFalse) .clearWorkFalse [] work output)
        (some (natEqCfg (some .write) (.write false) [] [] output))
        (work.length + 1) := by
    induction work with
    | nil =>
        simpa using evalsToInTimeOne (natEq_clearWorkFalse_nil_step output)
    | cons _ work ih =>
        let c₀ := natEqCfg (some .clearWorkFalse) .clearWorkFalse [] (() :: work) output
        let c₁ := natEqCfg (some .clearWorkFalse) .clearWorkFalse [] work output
        let cDone := natEqCfg (some .write) (.write false) [] [] output
        have h₁ : StateTransition.EvalsToInTime natEqMachine.step c₀ (some c₁) 1 :=
          evalsToInTimeOne (natEq_clearWorkFalse_cons_step work output)
        have hTail :
            StateTransition.EvalsToInTime natEqMachine.step c₁ (some cDone)
              (work.length + 1) := by
          simpa [c₁, cDone] using ih
        have hAll :
            StateTransition.EvalsToInTime natEqMachine.step c₀ (some cDone)
              (1 + (work.length + 1)) :=
          evalsToInTime_mono
            (StateTransition.EvalsToInTime.trans natEqMachine.step 1 (work.length + 1)
              c₀ c₁ (some cDone) h₁ hTail)
            (by omega)
        simpa [c₀, cDone, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAll

  def natEq_readRightCompare_run (n m : Nat) (output : List Bool) :
      StateTransition.EvalsToInTime natEqMachine.step
        (natEqCfg (some .readRight) (.readRight true)
          (List.replicate m natEqRightTrue ++ [natEqRightFalse])
          (List.replicate n ()) output)
        (some (natEqCfg (some .write) (.write (decide (n = m))) [] [] output))
        (3 * n + 3 * m + 5) := by
    induction n generalizing m with
    | zero =>
        cases m with
        | zero =>
            let c₀ := natEqCfg (some .readRight) (.readRight true) [natEqRightFalse] [] output
            let c₁ := natEqCfg (some .finish) (.finish true) [] [] output
            let c₂ := natEqCfg (some .write) (.write true) [] [] output
            have h₁ : StateTransition.EvalsToInTime natEqMachine.step c₀ (some c₁) 1 :=
              evalsToInTimeOne (natEq_readRight_false_step true [] [] output)
            have h₂ : StateTransition.EvalsToInTime natEqMachine.step c₁ (some c₂) 1 :=
              evalsToInTimeOne (natEq_finish_nil_step true output)
            have hAll :
                StateTransition.EvalsToInTime natEqMachine.step c₀ (some c₂) (1 + 1) :=
              StateTransition.EvalsToInTime.trans natEqMachine.step 1 1 c₀ c₁ (some c₂)
                h₁ h₂
            exact evalsToInTime_mono (by
              simpa [c₀, c₂] using hAll) (by omega)
        | succ m =>
            let rest := List.replicate m natEqRightTrue ++ [natEqRightFalse]
            let c₀ := natEqCfg (some .readRight) (.readRight true) (natEqRightTrue :: rest)
              [] output
            let c₁ := natEqCfg (some .cancelRight) (.cancelRight true) rest [] output
            let c₂ := natEqCfg (some .readRight) (.readRight false) rest [] output
            let c₃ := natEqCfg (some .readRight) (.readRight false) [natEqRightFalse] [] output
            let c₄ := natEqCfg (some .finish) (.finish false) [] [] output
            let c₅ := natEqCfg (some .write) (.write false) [] [] output
            have h₁ : StateTransition.EvalsToInTime natEqMachine.step c₀ (some c₁) 1 :=
              evalsToInTimeOne (natEq_readRight_true_ok_step rest [] output)
            have h₂ : StateTransition.EvalsToInTime natEqMachine.step c₁ (some c₂) 1 :=
              evalsToInTimeOne (natEq_cancelRight_nil_step true rest output)
            have hBad : StateTransition.EvalsToInTime natEqMachine.step c₂ (some c₃) m := by
              simpa [c₂, c₃, rest] using natEq_badRightTrues_run m [natEqRightFalse] output
            have hFalse : StateTransition.EvalsToInTime natEqMachine.step c₃ (some c₄) 1 :=
              evalsToInTimeOne (natEq_readRight_false_step false [] [] output)
            have hFinish : StateTransition.EvalsToInTime natEqMachine.step c₄ (some c₅) 1 :=
              evalsToInTimeOne (natEq_finish_nil_step false output)
            have h₁₂ : StateTransition.EvalsToInTime natEqMachine.step c₀ (some c₂) (1 + 1) :=
              StateTransition.EvalsToInTime.trans natEqMachine.step 1 1 c₀ c₁ (some c₂)
                h₁ h₂
            have h₁₂₃ :
                StateTransition.EvalsToInTime natEqMachine.step c₀ (some c₃) ((1 + 1) + m) :=
              evalsToInTime_mono
                (StateTransition.EvalsToInTime.trans natEqMachine.step (1 + 1) m c₀ c₂
                  (some c₃) h₁₂ hBad)
                (by omega)
            have h₄₅ : StateTransition.EvalsToInTime natEqMachine.step c₃ (some c₅) (1 + 1) :=
              StateTransition.EvalsToInTime.trans natEqMachine.step 1 1 c₃ c₄ (some c₅)
                hFalse hFinish
            have hAll :
                StateTransition.EvalsToInTime natEqMachine.step c₀ (some c₅)
                  (((1 + 1) + m) + (1 + 1)) :=
              evalsToInTime_mono
                (StateTransition.EvalsToInTime.trans natEqMachine.step ((1 + 1) + m) (1 + 1)
                  c₀ c₃ (some c₅) h₁₂₃ h₄₅)
                (by omega)
            exact evalsToInTime_mono (by
              simpa [c₀, c₅, rest, List.replicate_succ] using hAll) (by omega)
    | succ n ih =>
        cases m with
        | zero =>
            let c₀ := natEqCfg (some .readRight) (.readRight true) [natEqRightFalse]
              (List.replicate (n + 1) ()) output
            let c₁ := natEqCfg (some .finish) (.finish true) []
              (List.replicate (n + 1) ()) output
            let c₂ := natEqCfg (some .clearWorkFalse) .clearWorkFalse []
              (List.replicate n ()) output
            let c₃ := natEqCfg (some .write) (.write false) [] [] output
            have h₁ : StateTransition.EvalsToInTime natEqMachine.step c₀ (some c₁) 1 :=
              evalsToInTimeOne
                (natEq_readRight_false_step true [] (List.replicate (n + 1) ()) output)
            have h₂ : StateTransition.EvalsToInTime natEqMachine.step c₁ (some c₂) 1 := by
              simpa [c₁, c₂, List.replicate_succ] using
                evalsToInTimeOne (natEq_finish_cons_step true (List.replicate n ()) output)
            have hClear : StateTransition.EvalsToInTime natEqMachine.step c₂ (some c₃)
                (n + 1) := by
              simpa [c₂, c₃] using natEq_clearWorkFalse_run (List.replicate n ()) output
            have h₁₂ : StateTransition.EvalsToInTime natEqMachine.step c₀ (some c₂) (1 + 1) :=
              StateTransition.EvalsToInTime.trans natEqMachine.step 1 1 c₀ c₁ (some c₂)
                h₁ h₂
            have hAll :
                StateTransition.EvalsToInTime natEqMachine.step c₀ (some c₃)
                  ((1 + 1) + (n + 1)) :=
              evalsToInTime_mono
                (StateTransition.EvalsToInTime.trans natEqMachine.step (1 + 1) (n + 1)
                  c₀ c₂ (some c₃) h₁₂ hClear)
                (by omega)
            exact evalsToInTime_mono (by
              simpa [c₀, c₃] using hAll) (by omega)
        | succ m =>
            let rest := List.replicate m natEqRightTrue ++ [natEqRightFalse]
            let c₀ := natEqCfg (some .readRight) (.readRight true) (natEqRightTrue :: rest)
              (List.replicate (n + 1) ()) output
            let c₁ := natEqCfg (some .cancelRight) (.cancelRight true) rest
              (List.replicate (n + 1) ()) output
            let c₂ := natEqCfg (some .readRight) (.readRight true) rest
              (List.replicate n ()) output
            let cDone := natEqCfg (some .write) (.write (decide (n = m))) [] [] output
            have h₁ : StateTransition.EvalsToInTime natEqMachine.step c₀ (some c₁) 1 :=
              evalsToInTimeOne
                (natEq_readRight_true_ok_step rest (List.replicate (n + 1) ()) output)
            have h₂ : StateTransition.EvalsToInTime natEqMachine.step c₁ (some c₂) 1 := by
              simpa [c₁, c₂, List.replicate_succ] using
                evalsToInTimeOne
                  (natEq_cancelRight_cons_step true rest (List.replicate n ()) output)
            have hTail :
                StateTransition.EvalsToInTime natEqMachine.step c₂ (some cDone)
                  (3 * n + 3 * m + 5) := by
              simpa [c₂, cDone, rest] using ih m
            have h₁₂ : StateTransition.EvalsToInTime natEqMachine.step c₀ (some c₂) (1 + 1) :=
              StateTransition.EvalsToInTime.trans natEqMachine.step 1 1 c₀ c₁ (some c₂)
                h₁ h₂
            have hAll :
                StateTransition.EvalsToInTime natEqMachine.step c₀ (some cDone)
                  ((1 + 1) + (3 * n + 3 * m + 5)) :=
              evalsToInTime_mono
                (StateTransition.EvalsToInTime.trans natEqMachine.step (1 + 1)
                  (3 * n + 3 * m + 5) c₀ c₂ (some cDone) h₁₂ hTail)
                (by omega)
            exact evalsToInTime_mono (by
              simpa [c₀, cDone, rest, List.replicate_succ, Nat.succ.injEq] using hAll)
              (by omega)

  def natEq_readLeftPrefix_run (n m : Nat) :
      StateTransition.EvalsToInTime natEqMachine.step
        (natEqCfg (some .readLeft) (.readLeft true)
          (List.replicate n natEqLeftTrue ++
            natEqLeftFalse :: none :: (List.replicate m natEqRightTrue ++ [natEqRightFalse]))
          [] [])
        (some
          (natEqCfg (some .readRight) (.readRight true)
            (List.replicate m natEqRightTrue ++ [natEqRightFalse])
            (List.replicate n ()) []))
        (2 * n + 2) := by
    let right := List.replicate m natEqRightTrue ++ [natEqRightFalse]
    let rest := natEqLeftFalse :: none :: right
    let c₀ := natEqCfg (some .readLeft) (.readLeft true)
      (List.replicate n natEqLeftTrue ++ rest) [] []
    let c₁ := natEqCfg (some .readLeft) (.readLeft true) rest (List.replicate n ()) []
    let c₂ := natEqCfg (some .readLeft) (.readLeft true) (none :: right)
      (List.replicate n ()) []
    let c₃ := natEqCfg (some .readRight) (.readRight true) right (List.replicate n ()) []
    have hLeft : StateTransition.EvalsToInTime natEqMachine.step c₀ (some c₁) (2 * n) := by
      simpa [c₀, c₁, rest] using natEq_readLeftTrues_run true n rest [] []
    have hFalse : StateTransition.EvalsToInTime natEqMachine.step c₁ (some c₂) 1 := by
      simpa [c₁, c₂, rest] using
        evalsToInTimeOne
          (natEq_readLeft_false_step true (none :: right) (List.replicate n ()) [])
    have hDelim : StateTransition.EvalsToInTime natEqMachine.step c₂ (some c₃) 1 := by
      simpa [c₂, c₃] using
        evalsToInTimeOne (natEq_readLeft_delim_step true right (List.replicate n ()) [])
    have hPrefix :
        StateTransition.EvalsToInTime natEqMachine.step c₀ (some c₂) (2 * n + 1) :=
      evalsToInTime_mono
        (StateTransition.EvalsToInTime.trans natEqMachine.step (2 * n) 1 c₀ c₁
          (some c₂) hLeft hFalse)
        (by omega)
    have hAll :
        StateTransition.EvalsToInTime natEqMachine.step c₀ (some c₃) ((2 * n + 1) + 1) :=
      evalsToInTime_mono
        (StateTransition.EvalsToInTime.trans natEqMachine.step (2 * n + 1) 1 c₀ c₂
          (some c₃) hPrefix hDelim)
        (by omega)
    simpa [c₀, c₃, rest, right, Nat.add_assoc] using hAll

  noncomputable def natEqMachine_outputs (n m : Nat) :
      Turing.TM2OutputsInTime natEqMachine
        ((EncodedType.prod EncodedType.nat EncodedType.nat).encode (n, m))
        (some (EncodedType.bool.encode (decide (n = m))))
        ((5 * Polynomial.X + 20).eval
          (((EncodedType.prod EncodedType.nat EncodedType.nat).encode (n, m)).length)) := by
    let encodedInput := (EncodedType.prod EncodedType.nat EncodedType.nat).encode (n, m)
    let right := List.replicate m natEqRightTrue ++ [natEqRightFalse]
    let cRight := natEqCfg (some .readRight) (.readRight true) right (List.replicate n ()) []
    let cWrite := natEqCfg (some .write) (.write (decide (n = m))) [] [] []
    let cHalt := natEqCfg none (.readLeft true) [] [] [decide (n = m)]
    have hInput :
        encodedInput =
          List.replicate n natEqLeftTrue ++ natEqLeftFalse :: none :: right := by
      simp [encodedInput, right, natEqLeftTrue, natEqLeftFalse, natEqRightTrue,
        natEqRightFalse, EncodedType.prod, EncodedType.nat]
    have hLeft : StateTransition.EvalsToInTime natEqMachine.step
        (Turing.initList natEqMachine encodedInput) (some cRight) (2 * n + 2) := by
      rw [hInput, natEq_initList]
      simpa [cRight, right] using natEq_readLeftPrefix_run n m
    have hRight : StateTransition.EvalsToInTime natEqMachine.step cRight (some cWrite)
        (3 * n + 3 * m + 5) := by
      simpa [cRight, cWrite, right] using natEq_readRightCompare_run n m []
    have hWrite : StateTransition.EvalsToInTime natEqMachine.step cWrite (some cHalt) 1 := by
      simpa [cWrite, cHalt] using evalsToInTimeOne (natEq_write_step (decide (n = m)) [])
    have hLeftRight : StateTransition.EvalsToInTime natEqMachine.step
        (Turing.initList natEqMachine encodedInput) (some cWrite)
        ((2 * n + 2) + (3 * n + 3 * m + 5)) :=
      evalsToInTime_mono
        (StateTransition.EvalsToInTime.trans natEqMachine.step (2 * n + 2)
          (3 * n + 3 * m + 5) (Turing.initList natEqMachine encodedInput) cRight
          (some cWrite) hLeft hRight)
        (by omega)
    have hAll : StateTransition.EvalsToInTime natEqMachine.step
        (Turing.initList natEqMachine encodedInput) (some cHalt)
        (((2 * n + 2) + (3 * n + 3 * m + 5)) + 1) :=
      evalsToInTime_mono
        (StateTransition.EvalsToInTime.trans natEqMachine.step
          ((2 * n + 2) + (3 * n + 3 * m + 5)) 1
          (Turing.initList natEqMachine encodedInput) cWrite (some cHalt) hLeftRight hWrite)
        (by omega)
    unfold Turing.TM2OutputsInTime
    change StateTransition.EvalsToInTime natEqMachine.step
      (Turing.initList natEqMachine encodedInput)
      (some (Turing.haltList natEqMachine (EncodedType.bool.encode (decide (n = m)))))
      ((5 * Polynomial.X + 20).eval encodedInput.length)
    rw [natEq_haltList]
    refine evalsToInTime_mono (by
      simpa [encodedInput, cHalt, EncodedType.bool]) ?_
    simp [encodedInput, EncodedType.prod, EncodedType.nat, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_X]
    omega

  /-- Unary natural-number equality is directly TM2 polynomial-time computable. -/
  noncomputable def natEqComputableInPolyTime :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod EncodedType.nat EncodedType.nat).encode
        EncodedType.bool.encode
        (fun p : Nat × Nat => decide (p.1 = p.2)) where
    tm := natEqMachine
    inputAlphabet := Equiv.refl (Option (Bool ⊕ Bool))
    outputAlphabet := Equiv.refl Bool
    time := 5 * Polynomial.X + 20
    outputsFun p := by
      rcases p with ⟨n, m⟩
      letI : Decidable (n = m) := Nat.decEq n m
      have h := natEqMachine_outputs n m
      have hMapReflInv :
          ∀ {α : Type} (xs : List α), List.map (Equiv.refl α).invFun xs = xs := by
        intro α xs
        induction xs with
        | nil => rfl
        | cons a as ih =>
            rw [List.map_cons, ih]
            rfl
      have hInput :
          List.map (Equiv.refl (Option (Bool ⊕ Bool))).invFun
              ((EncodedType.prod EncodedType.nat EncodedType.nat).encode (n, m)) =
            (EncodedType.prod EncodedType.nat EncodedType.nat).encode (n, m) :=
        hMapReflInv ((EncodedType.prod EncodedType.nat EncodedType.nat).encode (n, m))
      have hOutput :
          List.map (Equiv.refl Bool).invFun
              (EncodedType.bool.encode (decide ((n, m).1 = (n, m).2))) =
            EncodedType.bool.encode (decide (n = m)) := by
        calc
          List.map (Equiv.refl Bool).invFun
              (EncodedType.bool.encode (decide ((n, m).1 = (n, m).2))) =
            EncodedType.bool.encode (decide ((n, m).1 = (n, m).2)) :=
              hMapReflInv (EncodedType.bool.encode (decide ((n, m).1 = (n, m).2)))
          _ = EncodedType.bool.encode (decide (n = m)) := rfl
      unfold Turing.TM2OutputsInTime at h ⊢
      convert h using 1
      · exact congrArg (Turing.initList natEqMachine) hInput


end TM2Programs
end ComplexityReduction
