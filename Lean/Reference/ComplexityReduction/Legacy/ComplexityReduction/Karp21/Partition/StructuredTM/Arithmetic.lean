import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.StructuredTM.ExactWrapper

namespace ComplexityReduction

namespace TM2Programs

open Turing.TM2.Stmt

/-! Direct unary multiplication for the Partition structured route. -/

inductive NatMulStack where
  | input
  | left
  | right
  | temp
  | output
  deriving DecidableEq, Fintype

abbrev natMulAlphabet : NatMulStack → Type
  | .input => Option (Bool ⊕ Bool)
  | .left => Unit
  | .right => Unit
  | .temp => Unit
  | .output => Bool

instance (k : NatMulStack) : Fintype (natMulAlphabet k) := by
  cases k
  · exact inferInstanceAs (Fintype (Option (Bool ⊕ Bool)))
  · exact inferInstanceAs (Fintype Unit)
  · exact inferInstanceAs (Fintype Unit)
  · exact inferInstanceAs (Fintype Unit)
  · exact inferInstanceAs (Fintype Bool)

inductive NatMulState where
  | readLeft
  | pushLeft
  | skipDelim
  | readRight
  | pushRight
  | writeFalse
  | startLoop
  | copyRight
  | pushTemp
  | pushTrue
  | restoreRight
  | pushRightBack
  | clearRight
  | done
  deriving DecidableEq, Fintype

def natMulReadLeftAfterPop :
    NatMulState → Option (Option (Bool ⊕ Bool)) → NatMulState
  | .readLeft, some (some (Sum.inl true)) => .pushLeft
  | .readLeft, some (some (Sum.inl false)) => .skipDelim
  | .readLeft, _ => .readLeft
  | state, _ => state

def natMulAfterPushLeft : NatMulState → NatMulState
  | .pushLeft => .readLeft
  | state => state

def natMulAfterSkipDelim :
    NatMulState → Option (Option (Bool ⊕ Bool)) → NatMulState
  | .skipDelim, _ => .readRight
  | state, _ => state

def natMulReadRightAfterPop :
    NatMulState → Option (Option (Bool ⊕ Bool)) → NatMulState
  | .readRight, some (some (Sum.inr true)) => .pushRight
  | .readRight, _ => .writeFalse
  | state, _ => state

def natMulAfterPushRight : NatMulState → NatMulState
  | .pushRight => .readRight
  | state => state

def natMulAfterWriteFalse : NatMulState → NatMulState
  | .writeFalse => .startLoop
  | state => state

def natMulStartLoopAfterPop : NatMulState → Option Unit → NatMulState
  | .startLoop, some _ => .copyRight
  | .startLoop, none => .clearRight
  | state, _ => state

def natMulCopyRightAfterPop : NatMulState → Option Unit → NatMulState
  | .copyRight, some _ => .pushTemp
  | .copyRight, none => .restoreRight
  | state, _ => state

def natMulAfterPushTemp : NatMulState → NatMulState
  | .pushTemp => .pushTrue
  | state => state

def natMulAfterPushTrue : NatMulState → NatMulState
  | .pushTrue => .copyRight
  | state => state

def natMulRestoreRightAfterPop : NatMulState → Option Unit → NatMulState
  | .restoreRight, some _ => .pushRightBack
  | .restoreRight, none => .startLoop
  | state, _ => state

def natMulAfterPushRightBack : NatMulState → NatMulState
  | .pushRightBack => .restoreRight
  | state => state

def natMulClearRightAfterPop : NatMulState → Option Unit → NatMulState
  | .clearRight, some _ => .clearRight
  | .clearRight, none => .done
  | state, _ => state

def natMulAfterDone : NatMulState → NatMulState
  | .done => .readLeft
  | state => state

def natMulMachine : Turing.FinTM2 where
  K := NatMulStack
  k₀ := .input
  k₁ := .output
  Γ := natMulAlphabet
  Λ := NatMulState
  main := .readLeft
  σ := NatMulState
  initialState := .readLeft
  m
    | .readLeft =>
        pop .input natMulReadLeftAfterPop (goto id)
    | .pushLeft =>
        push .left (fun _ => ()) (load natMulAfterPushLeft (goto id))
    | .skipDelim =>
        pop .input natMulAfterSkipDelim (goto id)
    | .readRight =>
        pop .input natMulReadRightAfterPop (goto id)
    | .pushRight =>
        push .right (fun _ => ()) (load natMulAfterPushRight (goto id))
    | .writeFalse =>
        push .output (fun _ => false) (load natMulAfterWriteFalse (goto id))
    | .startLoop =>
        pop .left natMulStartLoopAfterPop (goto id)
    | .copyRight =>
        pop .right natMulCopyRightAfterPop (goto id)
    | .pushTemp =>
        push .temp (fun _ => ()) (load natMulAfterPushTemp (goto id))
    | .pushTrue =>
        push .output (fun _ => true) (load natMulAfterPushTrue (goto id))
    | .restoreRight =>
        pop .temp natMulRestoreRightAfterPop (goto id)
    | .pushRightBack =>
        push .right (fun _ => ()) (load natMulAfterPushRightBack (goto id))
    | .clearRight =>
        pop .right natMulClearRightAfterPop (goto id)
    | .done =>
        load natMulAfterDone halt

def natMulCfg
    (label : Option NatMulState) (state : NatMulState)
    (input : List (Option (Bool ⊕ Bool))) (left right temp : List Unit)
    (output : List Bool) : natMulMachine.Cfg where
  l := label
  var := state
  stk
    | .input => input
    | .left => left
    | .right => right
    | .temp => temp
    | .output => output

lemma natMul_initList (input : List (Option (Bool ⊕ Bool))) :
    Turing.initList natMulMachine input =
      natMulCfg (some .readLeft) .readLeft input [] [] [] [] := by
  simp [Turing.initList, natMulMachine, natMulCfg]
  congr
  funext k
  cases k <;> rfl

lemma natMul_haltList (output : List Bool) :
    Turing.haltList natMulMachine output =
      natMulCfg none .readLeft [] [] [] [] output := by
  simp [Turing.haltList, natMulMachine, natMulCfg]
  congr
  funext k
  cases k <;> rfl

lemma natMul_readLeft_true_step (input : List (Option (Bool ⊕ Bool)))
    (left right temp : List Unit) (output : List Bool) :
    natMulMachine.step
        (natMulCfg (some .readLeft) .readLeft
          (some (Sum.inl true) :: input) left right temp output) =
      some (natMulCfg (some .pushLeft) .pushLeft input left right temp output) := by
  simp [natMulMachine, natMulCfg, natMulReadLeftAfterPop]
  congr
  funext k
  cases k <;> rfl

lemma natMul_pushLeft_step (input : List (Option (Bool ⊕ Bool)))
    (left right temp : List Unit) (output : List Bool) :
    natMulMachine.step
        (natMulCfg (some .pushLeft) .pushLeft input left right temp output) =
      some (natMulCfg (some .readLeft) .readLeft input (() :: left) right temp output) := by
  simp [natMulMachine, natMulCfg, natMulAfterPushLeft]
  congr
  funext k
  cases k <;> rfl

lemma natMul_readLeft_false_step (input : List (Option (Bool ⊕ Bool)))
    (left right temp : List Unit) (output : List Bool) :
    natMulMachine.step
        (natMulCfg (some .readLeft) .readLeft
          (some (Sum.inl false) :: input) left right temp output) =
      some (natMulCfg (some .skipDelim) .skipDelim input left right temp output) := by
  simp [natMulMachine, natMulCfg, natMulReadLeftAfterPop]
  congr
  funext k
  cases k <;> rfl

lemma natMul_skipDelim_step (head : Option (Bool ⊕ Bool))
    (input : List (Option (Bool ⊕ Bool)))
    (left right temp : List Unit) (output : List Bool) :
    natMulMachine.step
        (natMulCfg (some .skipDelim) .skipDelim (head :: input) left right temp output) =
      some (natMulCfg (some .readRight) .readRight input left right temp output) := by
  simp [natMulMachine, natMulCfg, natMulAfterSkipDelim]
  congr
  funext k
  cases k <;> rfl

lemma natMul_readRight_true_step (input : List (Option (Bool ⊕ Bool)))
    (left right temp : List Unit) (output : List Bool) :
    natMulMachine.step
        (natMulCfg (some .readRight) .readRight
          (some (Sum.inr true) :: input) left right temp output) =
      some (natMulCfg (some .pushRight) .pushRight input left right temp output) := by
  simp [natMulMachine, natMulCfg, natMulReadRightAfterPop]
  congr
  funext k
  cases k <;> rfl

lemma natMul_pushRight_step (input : List (Option (Bool ⊕ Bool)))
    (left right temp : List Unit) (output : List Bool) :
    natMulMachine.step
        (natMulCfg (some .pushRight) .pushRight input left right temp output) =
      some (natMulCfg (some .readRight) .readRight input left (() :: right) temp output) := by
  simp [natMulMachine, natMulCfg, natMulAfterPushRight]
  congr
  funext k
  cases k <;> rfl

lemma natMul_readRight_false_step (input : List (Option (Bool ⊕ Bool)))
    (left right temp : List Unit) (output : List Bool) :
    natMulMachine.step
        (natMulCfg (some .readRight) .readRight
          (some (Sum.inr false) :: input) left right temp output) =
      some (natMulCfg (some .writeFalse) .writeFalse input left right temp output) := by
  simp [natMulMachine, natMulCfg, natMulReadRightAfterPop]
  congr
  funext k
  cases k <;> rfl

lemma natMul_writeFalse_step (input : List (Option (Bool ⊕ Bool)))
    (left right temp : List Unit) (output : List Bool) :
    natMulMachine.step
        (natMulCfg (some .writeFalse) .writeFalse input left right temp output) =
      some (natMulCfg (some .startLoop) .startLoop input left right temp (false :: output)) := by
  simp [natMulMachine, natMulCfg, natMulAfterWriteFalse]
  congr
  funext k
  cases k <;> rfl

lemma natMul_startLoop_cons_step (input : List (Option (Bool ⊕ Bool)))
    (left right temp : List Unit) (output : List Bool) :
    natMulMachine.step
        (natMulCfg (some .startLoop) .startLoop input (() :: left) right temp output) =
      some (natMulCfg (some .copyRight) .copyRight input left right temp output) := by
  simp [natMulMachine, natMulCfg, natMulStartLoopAfterPop]
  congr
  funext k
  cases k <;> rfl

lemma natMul_startLoop_nil_step (input : List (Option (Bool ⊕ Bool)))
    (right temp : List Unit) (output : List Bool) :
    natMulMachine.step
        (natMulCfg (some .startLoop) .startLoop input [] right temp output) =
  some (natMulCfg (some .clearRight) .clearRight input [] right temp output) := by
  simp [natMulMachine, natMulCfg, natMulStartLoopAfterPop]
  congr

lemma natMul_clearRight_cons_step (input : List (Option (Bool ⊕ Bool)))
    (right temp : List Unit) (output : List Bool) :
    natMulMachine.step
        (natMulCfg (some .clearRight) .clearRight input [] (() :: right) temp output) =
      some (natMulCfg (some .clearRight) .clearRight input [] right temp output) := by
  simp [natMulMachine, natMulCfg, natMulClearRightAfterPop]
  congr
  funext k
  cases k <;> rfl

lemma natMul_clearRight_nil_step (input : List (Option (Bool ⊕ Bool)))
    (temp : List Unit) (output : List Bool) :
    natMulMachine.step
        (natMulCfg (some .clearRight) .clearRight input [] [] temp output) =
      some (natMulCfg (some .done) .done input [] [] temp output) := by
  simp [natMulMachine, natMulCfg, natMulClearRightAfterPop]
  congr

lemma natMul_done_step (output : List Bool) :
    natMulMachine.step
        (natMulCfg (some .done) .done [] [] [] [] output) =
      some (natMulCfg none .readLeft [] [] [] [] output) := by
  simp [natMulMachine, natMulCfg, natMulAfterDone]
  congr

lemma natMul_copyRight_cons_step (input : List (Option (Bool ⊕ Bool)))
    (left right temp : List Unit) (output : List Bool) :
    natMulMachine.step
        (natMulCfg (some .copyRight) .copyRight input left (() :: right) temp output) =
      some (natMulCfg (some .pushTemp) .pushTemp input left right temp output) := by
  simp [natMulMachine, natMulCfg, natMulCopyRightAfterPop]
  congr
  funext k
  cases k <;> rfl

lemma natMul_copyRight_nil_step (input : List (Option (Bool ⊕ Bool)))
    (left temp : List Unit) (output : List Bool) :
    natMulMachine.step
        (natMulCfg (some .copyRight) .copyRight input left [] temp output) =
      some (natMulCfg (some .restoreRight) .restoreRight input left [] temp output) := by
  simp [natMulMachine, natMulCfg, natMulCopyRightAfterPop]
  congr

lemma natMul_pushTemp_step (input : List (Option (Bool ⊕ Bool)))
    (left right temp : List Unit) (output : List Bool) :
    natMulMachine.step
        (natMulCfg (some .pushTemp) .pushTemp input left right temp output) =
      some (natMulCfg (some .pushTrue) .pushTrue input left right (() :: temp) output) := by
  simp [natMulMachine, natMulCfg, natMulAfterPushTemp]
  congr
  funext k
  cases k <;> rfl

lemma natMul_pushTrue_step (input : List (Option (Bool ⊕ Bool)))
    (left right temp : List Unit) (output : List Bool) :
    natMulMachine.step
        (natMulCfg (some .pushTrue) .pushTrue input left right temp output) =
      some (natMulCfg (some .copyRight) .copyRight input left right temp (true :: output)) := by
  simp [natMulMachine, natMulCfg, natMulAfterPushTrue]
  congr
  funext k
  cases k <;> rfl

lemma natMul_restoreRight_cons_step (input : List (Option (Bool ⊕ Bool)))
    (left right temp : List Unit) (output : List Bool) :
    natMulMachine.step
        (natMulCfg (some .restoreRight) .restoreRight input left right (() :: temp) output) =
      some (natMulCfg (some .pushRightBack) .pushRightBack input left right temp output) := by
  simp [natMulMachine, natMulCfg, natMulRestoreRightAfterPop]
  congr
  funext k
  cases k <;> rfl

lemma natMul_restoreRight_nil_step (input : List (Option (Bool ⊕ Bool)))
    (left right : List Unit) (output : List Bool) :
    natMulMachine.step
        (natMulCfg (some .restoreRight) .restoreRight input left right [] output) =
      some (natMulCfg (some .startLoop) .startLoop input left right [] output) := by
  simp [natMulMachine, natMulCfg, natMulRestoreRightAfterPop]
  congr

lemma natMul_pushRightBack_step (input : List (Option (Bool ⊕ Bool)))
    (left right temp : List Unit) (output : List Bool) :
    natMulMachine.step
        (natMulCfg (some .pushRightBack) .pushRightBack input left right temp output) =
      some (natMulCfg (some .restoreRight) .restoreRight input left (() :: right) temp output) := by
  simp [natMulMachine, natMulCfg, natMulAfterPushRightBack]
  congr
  funext k
  cases k <;> rfl

lemma natMul_replicateUnit_append_cons (n : Nat) (work : List Unit) :
    List.replicate n () ++ () :: work = () :: (List.replicate n () ++ work) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simpa [List.replicate_succ, List.append_assoc] using congrArg (fun xs => () :: xs) ih

lemma natMul_replicateTrue_append_cons (n : Nat) (output : List Bool) :
    List.replicate n true ++ true :: output =
      true :: (List.replicate n true ++ output) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simpa [List.replicate_succ, List.append_assoc] using congrArg (fun xs => true :: xs) ih

def natMul_readLeftTrues_run (n : Nat) (input : List (Option (Bool ⊕ Bool)))
    (left right temp : List Unit) (output : List Bool) :
    StateTransition.EvalsToInTime natMulMachine.step
      (natMulCfg (some .readLeft) .readLeft
        (List.replicate n (some (Sum.inl true)) ++ input) left right temp output)
      (some (natMulCfg (some .readLeft) .readLeft input
        (List.replicate n () ++ left) right temp output))
      (2 * n) := by
  induction n generalizing left with
  | zero =>
      exact StateTransition.EvalsToInTime.refl natMulMachine.step _
  | succ n ih =>
      let c₀ := natMulCfg (some .readLeft) .readLeft
        (some (Sum.inl true) :: List.replicate n (some (Sum.inl true)) ++ input)
        left right temp output
      let c₁ := natMulCfg (some .pushLeft) .pushLeft
        (List.replicate n (some (Sum.inl true)) ++ input) left right temp output
      let c₂ := natMulCfg (some .readLeft) .readLeft
        (List.replicate n (some (Sum.inl true)) ++ input) (() :: left) right temp output
      have h₁ : StateTransition.EvalsToInTime natMulMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne (by
          simpa [c₀, c₁] using natMul_readLeft_true_step
            (List.replicate n (some (Sum.inl true)) ++ input) left right temp output)
      have h₂ : StateTransition.EvalsToInTime natMulMachine.step c₁ (some c₂) 1 :=
        evalsToInTimeOne (by
          simpa [c₁, c₂] using natMul_pushLeft_step
            (List.replicate n (some (Sum.inl true)) ++ input) left right temp output)
      have hTail := ih (() :: left)
      have h₁₂ : StateTransition.EvalsToInTime natMulMachine.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans natMulMachine.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hAll :
          StateTransition.EvalsToInTime natMulMachine.step c₀
            (some (natMulCfg (some .readLeft) .readLeft input
              (List.replicate (n + 1) () ++ left) right temp output))
            ((1 + 1) + 2 * n) := by
        refine evalsToInTime_mono
          (StateTransition.EvalsToInTime.trans natMulMachine.step (1 + 1) (2 * n)
            c₀ c₂ _ h₁₂ ?_) (by omega)
        simpa [c₂, List.replicate_succ, List.append_assoc,
          natMul_replicateUnit_append_cons] using hTail
      simpa [c₀, List.replicate_succ, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hAll

def natMul_readRightTrues_run (m : Nat) (input : List (Option (Bool ⊕ Bool)))
    (left right temp : List Unit) (output : List Bool) :
    StateTransition.EvalsToInTime natMulMachine.step
      (natMulCfg (some .readRight) .readRight
        (List.replicate m (some (Sum.inr true)) ++ input) left right temp output)
      (some (natMulCfg (some .readRight) .readRight input left
        (List.replicate m () ++ right) temp output))
      (2 * m) := by
  induction m generalizing right with
  | zero =>
      exact StateTransition.EvalsToInTime.refl natMulMachine.step _
  | succ m ih =>
      let c₀ := natMulCfg (some .readRight) .readRight
        (some (Sum.inr true) :: List.replicate m (some (Sum.inr true)) ++ input)
        left right temp output
      let c₁ := natMulCfg (some .pushRight) .pushRight
        (List.replicate m (some (Sum.inr true)) ++ input) left right temp output
      let c₂ := natMulCfg (some .readRight) .readRight
        (List.replicate m (some (Sum.inr true)) ++ input) left (() :: right) temp output
      have h₁ : StateTransition.EvalsToInTime natMulMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne (by
          simpa [c₀, c₁] using natMul_readRight_true_step
            (List.replicate m (some (Sum.inr true)) ++ input) left right temp output)
      have h₂ : StateTransition.EvalsToInTime natMulMachine.step c₁ (some c₂) 1 :=
        evalsToInTimeOne (by
          simpa [c₁, c₂] using natMul_pushRight_step
            (List.replicate m (some (Sum.inr true)) ++ input) left right temp output)
      have hTail := ih (() :: right)
      have h₁₂ : StateTransition.EvalsToInTime natMulMachine.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans natMulMachine.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hAll :
          StateTransition.EvalsToInTime natMulMachine.step c₀
            (some (natMulCfg (some .readRight) .readRight input left
              (List.replicate (m + 1) () ++ right) temp output))
            ((1 + 1) + 2 * m) := by
        refine evalsToInTime_mono
          (StateTransition.EvalsToInTime.trans natMulMachine.step (1 + 1) (2 * m)
            c₀ c₂ _ h₁₂ ?_) (by omega)
        simpa [c₂, List.replicate_succ, List.append_assoc,
          natMul_replicateUnit_append_cons] using hTail
      simpa [c₀, List.replicate_succ, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hAll

def natMul_copyRight_run (m : Nat) (left temp : List Unit) (output : List Bool) :
    StateTransition.EvalsToInTime natMulMachine.step
      (natMulCfg (some .copyRight) .copyRight []
        left (List.replicate m ()) temp output)
      (some (natMulCfg (some .restoreRight) .restoreRight []
        left [] (List.replicate m () ++ temp) (List.replicate m true ++ output)))
      (3 * m + 1) := by
  induction m generalizing temp output with
  | zero =>
      simpa using
        evalsToInTimeOne (natMul_copyRight_nil_step [] left temp output)
  | succ m ih =>
      let c₀ := natMulCfg (some .copyRight) .copyRight []
        left (() :: List.replicate m ()) temp output
      let c₁ := natMulCfg (some .pushTemp) .pushTemp []
        left (List.replicate m ()) temp output
      let c₂ := natMulCfg (some .pushTrue) .pushTrue []
        left (List.replicate m ()) (() :: temp) output
      let c₃ := natMulCfg (some .copyRight) .copyRight []
        left (List.replicate m ()) (() :: temp) (true :: output)
      have h₁ : StateTransition.EvalsToInTime natMulMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne (natMul_copyRight_cons_step [] left (List.replicate m ()) temp output)
      have h₂ : StateTransition.EvalsToInTime natMulMachine.step c₁ (some c₂) 1 :=
        evalsToInTimeOne (natMul_pushTemp_step [] left (List.replicate m ()) temp output)
      have h₃ : StateTransition.EvalsToInTime natMulMachine.step c₂ (some c₃) 1 :=
        evalsToInTimeOne (natMul_pushTrue_step [] left (List.replicate m ()) (() :: temp) output)
      have h₁₂ : StateTransition.EvalsToInTime natMulMachine.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans natMulMachine.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have h₁₂₃ : StateTransition.EvalsToInTime natMulMachine.step c₀ (some c₃) ((1 + 1) + 1) :=
        StateTransition.EvalsToInTime.trans natMulMachine.step (1 + 1) 1 c₀ c₂
          (some c₃) h₁₂ h₃
      have hTail := ih (() :: temp) (true :: output)
      have hAll :
          StateTransition.EvalsToInTime natMulMachine.step c₀
            (some (natMulCfg (some .restoreRight) .restoreRight []
              left [] (List.replicate (m + 1) () ++ temp)
              (List.replicate (m + 1) true ++ output)))
            (((1 + 1) + 1) + (3 * m + 1)) := by
        refine evalsToInTime_mono
          (StateTransition.EvalsToInTime.trans natMulMachine.step ((1 + 1) + 1)
            (3 * m + 1) c₀ c₃ _ h₁₂₃ ?_) (by omega)
        simpa [c₃, List.replicate_succ, List.append_assoc,
          natMul_replicateUnit_append_cons, natMul_replicateTrue_append_cons] using hTail
      simpa [c₀, List.replicate_succ, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hAll

def natMul_restoreRight_run (m : Nat) (left right : List Unit) (output : List Bool) :
    StateTransition.EvalsToInTime natMulMachine.step
      (natMulCfg (some .restoreRight) .restoreRight []
        left right (List.replicate m ()) output)
      (some (natMulCfg (some .startLoop) .startLoop []
        left (List.replicate m () ++ right) [] output))
      (2 * m + 1) := by
  induction m generalizing right output with
  | zero =>
      simpa using
        evalsToInTimeOne (natMul_restoreRight_nil_step [] left right output)
  | succ m ih =>
      let c₀ := natMulCfg (some .restoreRight) .restoreRight []
        left right (() :: List.replicate m ()) output
      let c₁ := natMulCfg (some .pushRightBack) .pushRightBack []
        left right (List.replicate m ()) output
      let c₂ := natMulCfg (some .restoreRight) .restoreRight []
        left (() :: right) (List.replicate m ()) output
      have h₁ : StateTransition.EvalsToInTime natMulMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne (natMul_restoreRight_cons_step [] left right (List.replicate m ()) output)
      have h₂ : StateTransition.EvalsToInTime natMulMachine.step c₁ (some c₂) 1 :=
        evalsToInTimeOne (natMul_pushRightBack_step [] left right (List.replicate m ()) output)
      have hTail := ih (() :: right) output
      have h₁₂ : StateTransition.EvalsToInTime natMulMachine.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans natMulMachine.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hAll :
          StateTransition.EvalsToInTime natMulMachine.step c₀
            (some (natMulCfg (some .startLoop) .startLoop []
              left (List.replicate (m + 1) () ++ right) [] output))
            ((1 + 1) + (2 * m + 1)) := by
        refine evalsToInTime_mono
          (StateTransition.EvalsToInTime.trans natMulMachine.step (1 + 1)
            (2 * m + 1) c₀ c₂ _ h₁₂ ?_) (by omega)
        simpa [c₂, List.replicate_succ, List.append_assoc,
          natMul_replicateUnit_append_cons] using hTail
      simpa [c₀, List.replicate_succ, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hAll

def natMul_clearRight_run (m : Nat) (output : List Bool) :
    StateTransition.EvalsToInTime natMulMachine.step
      (natMulCfg (some .clearRight) .clearRight [] [] (List.replicate m ()) [] output)
      (some (natMulCfg (some .done) .done [] [] [] [] output))
      (m + 1) := by
  induction m with
  | zero =>
      simpa using
        evalsToInTimeOne (natMul_clearRight_nil_step [] [] output)
  | succ m ih =>
      let c₀ := natMulCfg (some .clearRight) .clearRight []
        [] (() :: List.replicate m ()) [] output
      let c₁ := natMulCfg (some .clearRight) .clearRight []
        [] (List.replicate m ()) [] output
      have hStep : StateTransition.EvalsToInTime natMulMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne (by
          simpa [c₀, c₁] using natMul_clearRight_cons_step []
            (List.replicate m ()) [] output)
      have hAll :
          StateTransition.EvalsToInTime natMulMachine.step c₀
            (some (natMulCfg (some .done) .done [] [] [] [] output))
            (1 + (m + 1)) :=
        evalsToInTime_mono
          (StateTransition.EvalsToInTime.trans natMulMachine.step 1 (m + 1)
            c₀ c₁ _ hStep (by simpa [c₁] using ih)) (by omega)
      simpa [c₀, List.replicate_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hAll

def natMul_loop_run (n m : Nat) (output : List Bool) :
    StateTransition.EvalsToInTime natMulMachine.step
      (natMulCfg (some .startLoop) .startLoop []
        (List.replicate n ()) (List.replicate m ()) [] output)
      (some (natMulCfg none .readLeft [] [] [] []
        (List.replicate (n * m) true ++ output)))
      (n * (5 * m + 3) + m + 3) := by
  induction n generalizing output with
  | zero =>
      let c₀ := natMulCfg (some .startLoop) .startLoop [] [] (List.replicate m ()) [] output
      let c₁ := natMulCfg (some .clearRight) .clearRight [] [] (List.replicate m ()) [] output
      let c₂ := natMulCfg (some .done) .done [] [] [] [] output
      have hStart : StateTransition.EvalsToInTime natMulMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne (by
          simpa [c₀, c₁] using natMul_startLoop_nil_step []
            (List.replicate m ()) [] output)
      have hClear : StateTransition.EvalsToInTime natMulMachine.step c₁ (some c₂) (m + 1) :=
        by simpa [c₁, c₂] using natMul_clearRight_run m output
      have hDone : StateTransition.EvalsToInTime natMulMachine.step c₂
          (some (natMulCfg none .readLeft [] [] [] [] output)) 1 :=
        evalsToInTimeOne (natMul_done_step output)
      have hStartClear :
          StateTransition.EvalsToInTime natMulMachine.step c₀ (some c₂) (m + 2) :=
        evalsToInTime_mono
          (StateTransition.EvalsToInTime.trans natMulMachine.step 1 (m + 1)
            c₀ c₁ (some c₂) hStart hClear) (by omega)
      have hAll :
          StateTransition.EvalsToInTime natMulMachine.step c₀
            (some (natMulCfg none .readLeft [] [] [] [] output))
            (m + 3) :=
        evalsToInTime_mono
          (StateTransition.EvalsToInTime.trans natMulMachine.step (m + 2) 1
            c₀ c₂ _ hStartClear hDone) (by omega)
      simpa [c₀, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hAll
  | succ n ih =>
      let c₀ := natMulCfg (some .startLoop) .startLoop []
        (() :: List.replicate n ()) (List.replicate m ()) [] output
      let c₁ := natMulCfg (some .copyRight) .copyRight []
        (List.replicate n ()) (List.replicate m ()) [] output
      have hStart : StateTransition.EvalsToInTime natMulMachine.step c₀ (some c₁) 1 :=
        evalsToInTimeOne (natMul_startLoop_cons_step []
          (List.replicate n ()) (List.replicate m ()) [] output)
      have hCopy := natMul_copyRight_run m (List.replicate n ()) [] output
      let c₂ := natMulCfg (some .restoreRight) .restoreRight []
        (List.replicate n ()) [] (List.replicate m ())
        (List.replicate m true ++ output)
      have hRestore := natMul_restoreRight_run m (List.replicate n ()) []
        (List.replicate m true ++ output)
      let c₃ := natMulCfg (some .startLoop) .startLoop []
        (List.replicate n ()) (List.replicate m ()) []
        (List.replicate m true ++ output)
      have hTail := ih (List.replicate m true ++ output)
      have hStartCopy :
          StateTransition.EvalsToInTime natMulMachine.step c₀ (some c₂)
            (1 + (3 * m + 1)) := by
        exact evalsToInTime_mono
          (StateTransition.EvalsToInTime.trans natMulMachine.step 1 (3 * m + 1)
            c₀ c₁ (some c₂) hStart (by simpa [c₁, c₂] using hCopy)) (by omega)
      have hStartCopyRestore :
          StateTransition.EvalsToInTime natMulMachine.step c₀ (some c₃)
            ((1 + (3 * m + 1)) + (2 * m + 1)) := by
        exact evalsToInTime_mono
          (StateTransition.EvalsToInTime.trans natMulMachine.step
            (1 + (3 * m + 1)) (2 * m + 1)
            c₀ c₂ (some c₃) hStartCopy (by simpa [c₂, c₃] using hRestore)) (by omega)
      have hAll :
          StateTransition.EvalsToInTime natMulMachine.step c₀
            (some (natMulCfg none .readLeft [] [] [] []
              (List.replicate ((n + 1) * m) true ++ output)))
            (((1 + (3 * m + 1)) + (2 * m + 1)) +
              (n * (5 * m + 3) + m + 3)) := by
        refine evalsToInTime_mono
          (StateTransition.EvalsToInTime.trans natMulMachine.step
            ((1 + (3 * m + 1)) + (2 * m + 1))
            (n * (5 * m + 3) + m + 3) c₀ c₃ _ hStartCopyRestore ?_) (by omega)
        have hOut :
            List.replicate (n * m) true ++ (List.replicate m true ++ output) =
              List.replicate (m + n * m) true ++ output := by
          rw [← List.append_assoc, List.replicate_append_replicate]
          rw [Nat.add_comm]
        simpa [c₃, hOut, Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hTail
      have hAll₀ :
          StateTransition.EvalsToInTime natMulMachine.step
            (natMulCfg (some .startLoop) .startLoop []
              (() :: List.replicate n ()) (List.replicate m ()) [] output)
            (some (natMulCfg none .readLeft [] [] [] []
              (List.replicate ((n + 1) * m) true ++ output)))
            (((1 + (3 * m + 1)) + (2 * m + 1)) +
              (n * (5 * m + 3) + m + 3)) := by
        simpa [c₀] using hAll
      exact evalsToInTime_mono hAll₀ (by nlinarith [Nat.zero_le n, Nat.zero_le m])

noncomputable def natMulMachine_outputs (n m : Nat) :
    Turing.TM2OutputsInTime natMulMachine
      ((EncodedType.prod EncodedType.nat EncodedType.nat).encode (n, m))
      (some (EncodedType.nat.encode (n * m)))
      ((10 * Polynomial.X ^ 2 + 50 * Polynomial.X + 100).eval
        ((EncodedType.prod EncodedType.nat EncodedType.nat).encode (n, m)).length) := by
  let rightInput : List (Option (Bool ⊕ Bool)) :=
    List.replicate m (some (Sum.inr true)) ++ [some (Sum.inr false)]
  let afterLeft := natMulCfg (some .readRight) .readRight rightInput
    (List.replicate n ()) [] [] []
  let afterRight := natMulCfg (some .startLoop) .startLoop []
    (List.replicate n ()) (List.replicate m ()) [] [false]
  have hInput :
      (EncodedType.prod EncodedType.nat EncodedType.nat).encode (n, m) =
        List.replicate n (some (Sum.inl true)) ++
          some (Sum.inl false) :: none :: rightInput := by
    simp [rightInput, EncodedType.prod, EncodedType.nat, List.map_append]
  have hLeftRun : StateTransition.EvalsToInTime natMulMachine.step
      (Turing.initList natMulMachine
        ((EncodedType.prod EncodedType.nat EncodedType.nat).encode (n, m)))
      (some afterLeft)
      (2 * n + 2) := by
    rw [hInput, natMul_initList]
    let cMid := natMulCfg (some .readLeft) .readLeft
      (some (Sum.inl false) :: none :: rightInput)
      (List.replicate n ()) [] [] []
    let cSkip := natMulCfg (some .skipDelim) .skipDelim
      (none :: rightInput) (List.replicate n ()) [] [] []
    have hTrues := natMul_readLeftTrues_run n
      (some (Sum.inl false) :: none :: rightInput) [] [] [] []
    have hFalse :
        StateTransition.EvalsToInTime natMulMachine.step cMid (some cSkip) 1 :=
      evalsToInTimeOne (natMul_readLeft_false_step
        (none :: rightInput) (List.replicate n ()) [] [] [])
    have hSkip :
        StateTransition.EvalsToInTime natMulMachine.step cSkip (some afterLeft) 1 :=
      evalsToInTimeOne (natMul_skipDelim_step
        none rightInput (List.replicate n ()) [] [] [])
    have hFalseSkip :
        StateTransition.EvalsToInTime natMulMachine.step cMid (some afterLeft) (1 + 1) :=
      StateTransition.EvalsToInTime.trans natMulMachine.step 1 1
        cMid cSkip (some afterLeft) hFalse hSkip
    have hAll :
        StateTransition.EvalsToInTime natMulMachine.step
          (natMulCfg (some .readLeft) .readLeft
            (List.replicate n (some (Sum.inl true)) ++
              some (Sum.inl false) :: none :: rightInput) [] [] [] [])
          (some afterLeft) (2 * n + (1 + 1)) :=
      evalsToInTime_mono
        (StateTransition.EvalsToInTime.trans natMulMachine.step (2 * n) (1 + 1)
          _ cMid (some afterLeft) (by simpa [cMid] using hTrues) hFalseSkip) (by omega)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAll
  have hRightRun : StateTransition.EvalsToInTime natMulMachine.step afterLeft
      (some afterRight) (2 * m + 2) := by
    let cBeforeFalse := natMulCfg (some .readRight) .readRight
      [some (Sum.inr false)] (List.replicate n ()) (List.replicate m ()) [] []
    let cWrite := natMulCfg (some .writeFalse) .writeFalse []
      (List.replicate n ()) (List.replicate m ()) [] []
    have hTrues := natMul_readRightTrues_run m [some (Sum.inr false)]
      (List.replicate n ()) [] [] []
    have hFalse :
        StateTransition.EvalsToInTime natMulMachine.step cBeforeFalse (some cWrite) 1 :=
      evalsToInTimeOne (natMul_readRight_false_step []
        (List.replicate n ()) (List.replicate m ()) [] [])
    have hWrite :
        StateTransition.EvalsToInTime natMulMachine.step cWrite (some afterRight) 1 :=
      evalsToInTimeOne (natMul_writeFalse_step []
        (List.replicate n ()) (List.replicate m ()) [] [])
    have hFalseWrite :
        StateTransition.EvalsToInTime natMulMachine.step cBeforeFalse
          (some afterRight) (1 + 1) :=
      StateTransition.EvalsToInTime.trans natMulMachine.step 1 1
        cBeforeFalse cWrite (some afterRight) hFalse hWrite
    have hAll :
        StateTransition.EvalsToInTime natMulMachine.step afterLeft
          (some afterRight) (2 * m + (1 + 1)) :=
      evalsToInTime_mono
        (StateTransition.EvalsToInTime.trans natMulMachine.step (2 * m) (1 + 1)
          afterLeft cBeforeFalse (some afterRight)
          (by simpa [afterLeft, rightInput, cBeforeFalse, List.append_assoc] using hTrues)
          hFalseWrite) (by omega)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAll
  have hLoop := natMul_loop_run n m [false]
  have hLeftRight :
      StateTransition.EvalsToInTime natMulMachine.step
        (Turing.initList natMulMachine
          ((EncodedType.prod EncodedType.nat EncodedType.nat).encode (n, m)))
        (some afterRight)
        ((2 * n + 2) + (2 * m + 2)) :=
    evalsToInTime_mono
      (StateTransition.EvalsToInTime.trans natMulMachine.step (2 * n + 2) (2 * m + 2)
        _ afterLeft (some afterRight) hLeftRun hRightRun) (by omega)
  have hAll :
      StateTransition.EvalsToInTime natMulMachine.step
        (Turing.initList natMulMachine
          ((EncodedType.prod EncodedType.nat EncodedType.nat).encode (n, m)))
        (some (natMulCfg none .readLeft [] [] [] []
          (List.replicate (n * m) true ++ [false])))
        (((2 * n + 2) + (2 * m + 2)) + (n * (5 * m + 3) + m + 3)) :=
    evalsToInTime_mono
      (StateTransition.EvalsToInTime.trans natMulMachine.step
        ((2 * n + 2) + (2 * m + 2)) (n * (5 * m + 3) + m + 3)
        _ afterRight _ hLeftRight (by simpa [afterRight] using hLoop)) (by omega)
  unfold Turing.TM2OutputsInTime
  change StateTransition.EvalsToInTime natMulMachine.step
    (Turing.initList natMulMachine
      ((EncodedType.prod EncodedType.nat EncodedType.nat).encode (n, m)))
    (some (Turing.haltList natMulMachine (EncodedType.nat.encode (n * m))))
    ((10 * Polynomial.X ^ 2 + 50 * Polynomial.X + 100).eval
      ((EncodedType.prod EncodedType.nat EncodedType.nat).encode (n, m)).length)
  rw [natMul_haltList]
  refine evalsToInTime_mono (by
    simpa [EncodedType.nat] using hAll) ?_
  simp [EncodedType.prod, EncodedType.nat, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X]
  nlinarith [Nat.zero_le n, Nat.zero_le m]

/-- Unary natural-number multiplication is directly TM2 polynomial-time computable. -/
noncomputable def natMulComputableInPolyTime :
    Turing.TM2ComputableInPolyTime
      (EncodedType.prod EncodedType.nat EncodedType.nat).encode
      EncodedType.nat.encode
      (fun p : Nat × Nat => p.1 * p.2) where
  tm := natMulMachine
  inputAlphabet := Equiv.refl (Option (Bool ⊕ Bool))
  outputAlphabet := Equiv.refl Bool
  time := 10 * Polynomial.X ^ 2 + 50 * Polynomial.X + 100
  outputsFun p := by
    rcases p with ⟨(n : Nat), (m : Nat)⟩
    have h := natMulMachine_outputs n m
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
            (EncodedType.nat.encode ((((n, m) : Nat × Nat).1 * ((n, m) : Nat × Nat).2))) =
          EncodedType.nat.encode (n * m) := by
      simp
    unfold Turing.TM2OutputsInTime at h ⊢
    convert h using 1
    · exact congrArg (Turing.initList natMulMachine) hInput
    · exact congrArg (fun xs => Option.map (Turing.haltList natMulMachine) (some xs)) hOutput

end TM2Programs

namespace TMPolyTimeMap

theorem nat_mul :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.nat
      (fun p : Nat × Nat => p.1 * p.2) :=
  ⟨TM2Programs.natMulComputableInPolyTime⟩

end TMPolyTimeMap

end ComplexityReduction
