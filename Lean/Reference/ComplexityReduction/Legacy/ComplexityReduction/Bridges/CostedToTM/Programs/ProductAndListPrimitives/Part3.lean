import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.ProductAndListPrimitives.Part2

namespace ComplexityReduction
namespace TM2Programs
open Turing.TM2.Stmt

/--
TM2 polynomial-time computation of list-map when every mapped element has empty
encoding.  This is a structural subcase of list-map, not the arbitrary
`list_map_map` closure theorem.
-/

noncomputable def listEmptyOutputComputableInPolyTime
    (X Y : EncodedType) (f : X.Carrier → Y.Carrier)
    (hf : ∀ x, Y.encode (f x) = []) :
    Turing.TM2ComputableInPolyTime
      (EncodedType.list X).encode
      (EncodedType.list Y).encode
      (fun xs : List X.Carrier => xs.map f) where
  tm :=
    filterMapMachine
      (Option X.Symbol)
      (Option Y.Symbol)
      listConstEmptyKeep
  inputAlphabet := Equiv.cast rfl
  outputAlphabet := Equiv.cast rfl
  time := 4 * Polynomial.X + 2
  outputsFun xs := by
    convert
      filterMap_outputs
        (Option X.Symbol)
        (Option Y.Symbol)
        listConstEmptyKeep
        (List.map (Equiv.cast rfl).invFun ((EncodedType.list X).encode xs)) using 1
    · simp
      calc
        List.map (Equiv.cast rfl).invFun ((EncodedType.list Y).encode (xs.map f)) =
            (EncodedType.list Y).encode (xs.map f) := by
          simp
        _ =
            (List.map (Equiv.cast rfl).invFun
              ((EncodedType.list X).encode xs)).filterMap
                listConstEmptyKeep :=
          (listEmptyOutput_filterMap_encode X Y f hf xs).symm
        _ =
            ((EncodedType.list X).encode xs).filterMap listConstEmptyKeep := by
          simp
    · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
      rfl

/-- The encoded-list block emitted for one source element mapped to a fixed target value. -/
def listConstBlock {β : Type} (out : List β) : List (Option β) :=
  out.map some ++ [none]

/-- Expand source encoded-list delimiters into a fixed target element encoding. -/
def listConstExpand {α β : Type} (out : List β) : Option α → List (Option β)
  | some _ => []
  | none => listConstBlock out

lemma listConstExpand_payload {α β : Type} (out : List β) :
    ∀ symbols : List α,
      (symbols.map some).flatMap (listConstExpand out) = []
  | [] => by rfl
  | a :: symbols => by
      change listConstExpand out (some a) ++
          (symbols.map some).flatMap (listConstExpand out) = []
      rw [listConstExpand_payload out symbols]
      rfl

lemma listConstExpand_length_le {α β : Type} (out : List β) :
    ∀ input : List (Option α),
      (input.flatMap (listConstExpand out)).length ≤ (out.length + 1) * input.length
  | [] => by simp
  | some _ :: input => by
      have ih := listConstExpand_length_le out input
      change (input.flatMap (listConstExpand out)).length ≤
        (out.length + 1) * (input.length + 1)
      exact Nat.le_trans ih
        (Nat.mul_le_mul_left (out.length + 1) (Nat.le_succ input.length))
  | none :: input => by
      have ih := listConstExpand_length_le out input
      change (listConstBlock out ++ input.flatMap (listConstExpand out)).length ≤
        (out.length + 1) * (input.length + 1)
      rw [List.length_append]
      have hOut : (listConstBlock out).length = out.length + 1 := by
        simp [listConstBlock, List.length_map]
      rw [hOut]
      calc
        out.length + 1 + (input.flatMap (listConstExpand out)).length ≤
            out.length + 1 + (out.length + 1) * input.length :=
          Nat.add_le_add_left ih (out.length + 1)
        _ = (out.length + 1) * input.length + (out.length + 1) := by omega
        _ = (out.length + 1) * (input.length + 1) := by
          rw [Nat.mul_succ]

lemma listConst_flatMap_encode (X Y : EncodedType) (y : Y.Carrier) :
    ∀ xs : List X.Carrier,
      ((EncodedType.list X).encode xs).flatMap (listConstExpand (Y.encode y)) =
        (EncodedType.list Y).encode (xs.map fun _ => y)
  | [] => by
      simp [EncodedType.list]
  | x :: xs => by
      have ih := listConst_flatMap_encode X Y y xs
      have ih' :
          (xs.flatMap fun x => (X.encode x).map some ++ [none]).flatMap
              (listConstExpand (Y.encode y)) =
            (xs.map fun _ => y).flatMap
              (fun y => (Y.encode y).map some ++ [none]) := by
        simpa [EncodedType.list] using ih
      change
        (((X.encode x).map some ++ [none]) ++
            (xs.flatMap fun x => (X.encode x).map some ++ [none])).flatMap
            (listConstExpand (Y.encode y)) =
          listConstBlock (Y.encode y) ++
            ((xs.map fun _ => y).flatMap fun y => (Y.encode y).map some ++ [none])
      rw [List.flatMap_append, ih']
      simp [List.flatMap_append, listConstExpand_payload, listConstExpand, listConstBlock]

/-- Internal state for the fixed-value list-map expansion program. -/
inductive ListConstState (β : Type) where
  | delimiter
  | skip
  | output (b : Option β)
  | done
  deriving DecidableEq, Fintype

namespace ListConstState

def isDelimiter {β : Type} : ListConstState β → Bool
  | delimiter => true
  | _ => false

def isOutput {β : Type} : ListConstState β → Bool
  | output _ => true
  | _ => false

def isDone {β : Type} : ListConstState β → Bool
  | done => true
  | _ => false

end ListConstState

/-- Control labels for the fixed-value list-map expansion program. -/
inductive ListConstLabel (β : Type) where
  | readInput
  | moveTemp
  | pushOutput (b : Option β)
  deriving DecidableEq, Fintype

/-- Push a fixed block onto the temporary stack in one TM2 statement. -/
def pushAllListConstTemp {α β : Type} :
    List (Option β) →
      Turing.TM2.Stmt
        (fmAlphabet (Option α) (Option β))
        (ListConstLabel β)
        (ListConstState β) →
      Turing.TM2.Stmt
        (fmAlphabet (Option α) (Option β))
        (ListConstLabel β)
        (ListConstState β)
  | [], q => q
  | b :: bs, q => push FMStack.temp (fun _ => b) (pushAllListConstTemp bs q)

lemma stepAux_pushAllListConstTemp {α β : Type} [DecidableEq FMStack] (block : List (Option β))
    (state : ListConstState β)
    (stk : (k : FMStack) → List (fmAlphabet (Option α) (Option β) k)) :
    Turing.TM2.stepAux (K := FMStack)
      (pushAllListConstTemp (α := α) (β := β) block
        (goto fun _ : ListConstState β => ListConstLabel.readInput))
      state stk =
    { l := some ListConstLabel.readInput, var := state,
      stk := Function.update stk FMStack.temp (block.reverse ++ stk FMStack.temp) } := by
  induction block generalizing stk with
  | nil =>
      simp [pushAllListConstTemp]
  | cons b block ih =>
      simp [pushAllListConstTemp, ih, List.append_assoc]

lemma stepAux_pushAllListConstTemp_cfg {α β : Type} [DecidableEq FMStack] (block : List (Option β))
    (state : ListConstState β) (input : List (Option α)) (output temp : List (Option β)) :
    Turing.TM2.stepAux (K := FMStack)
      (pushAllListConstTemp (α := α) (β := β) block
        (goto fun _ : ListConstState β => ListConstLabel.readInput))
      state
      (fun
        | FMStack.input => input
        | FMStack.output => output
        | FMStack.temp => temp) =
    { l := some ListConstLabel.readInput, var := state,
      stk := fun
        | FMStack.input => input
        | FMStack.output => output
        | FMStack.temp => block.reverse ++ temp } := by
  convert
    stepAux_pushAllListConstTemp (α := α) (β := β) block state
      (fun
        | FMStack.input => input
        | FMStack.output => output
        | FMStack.temp => temp) using 1
  congr
  funext k
  cases k <;> simp [Function.update]

lemma stepAux_pushAllListConstTemp_afterInputPop {α β : Type} [DecidableEq FMStack]
    (block : List (Option β))
    (state : ListConstState β) (headInput input : List (Option α))
    (output temp : List (Option β)) :
    Turing.TM2.stepAux (K := FMStack)
      (pushAllListConstTemp (α := α) (β := β) block
        (goto fun _ : ListConstState β => ListConstLabel.readInput))
      state
      (Function.update
        ((fun
          | FMStack.input => headInput
          | FMStack.output => output
          | FMStack.temp => temp) :
          (k : FMStack) → List (fmAlphabet (Option α) (Option β) k))
        FMStack.input input) =
    { l := some ListConstLabel.readInput, var := state,
      stk := fun
        | FMStack.input => input
        | FMStack.output => output
        | FMStack.temp => block.reverse ++ temp } := by
  induction block generalizing temp with
  | nil =>
      simp [pushAllListConstTemp]
      funext k
      cases k <;> simp [Function.update]
  | cons b block ih =>
      have hUpdate :
          Function.update
              (Function.update
                ((fun
                  | FMStack.input => headInput
                  | FMStack.output => output
                  | FMStack.temp => temp) :
                  (k : FMStack) → List (fmAlphabet (Option α) (Option β) k))
                FMStack.input input)
              FMStack.temp (b :: temp) =
            Function.update
              ((fun
                | FMStack.input => headInput
                | FMStack.output => output
                | FMStack.temp => b :: temp) :
                (k : FMStack) → List (fmAlphabet (Option α) (Option β) k))
              FMStack.input input := by
        funext k
        cases k <;> simp [Function.update]
      simp [pushAllListConstTemp, List.append_assoc]
      convert ih (b :: temp) using 1
      exact
        congrArg
          (fun stk : (k : FMStack) → List (fmAlphabet (Option α) (Option β) k) =>
            Turing.TM2.stepAux (K := FMStack)
              (pushAllListConstTemp (α := α) (β := β) block
                (goto fun _ : ListConstState β => ListConstLabel.readInput))
              state stk)
          hUpdate

def listConstMachine (α β : Type) [Fintype α] [Fintype β] (out : List β) :
    Turing.FinTM2 where
  K := FMStack
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := FMStack.input
  k₁ := FMStack.output
  Γ := fmAlphabet (Option α) (Option β)
  Λ := ListConstLabel β
  main := ListConstLabel.readInput
  σ := ListConstState β
  initialState := ListConstState.done
  Γk₀Fin := by
    dsimp [fmAlphabet]
    infer_instance
  m
    | ListConstLabel.readInput =>
        pop FMStack.input
          (fun _ head =>
            match head with
            | none => ListConstState.done
            | some none => ListConstState.delimiter
            | some (some _) => ListConstState.skip)
          (branch ListConstState.isDelimiter
            (pushAllListConstTemp (listConstBlock out)
              (goto fun _ : ListConstState β => ListConstLabel.readInput))
            (branch ListConstState.isDone
              (goto fun _ => ListConstLabel.moveTemp)
              (goto fun _ => ListConstLabel.readInput)))
    | ListConstLabel.moveTemp =>
        pop FMStack.temp
          (fun _ head =>
            match head with
            | some b => ListConstState.output b
            | none => ListConstState.done)
          (branch ListConstState.isOutput
            (goto fun state =>
              match state with
              | ListConstState.output b => ListConstLabel.pushOutput b
              | _ => ListConstLabel.moveTemp)
            (load (fun _ => ListConstState.done) halt))
    | ListConstLabel.pushOutput b =>
        push FMStack.output (fun _ => b) (goto fun _ => ListConstLabel.moveTemp)

def listConstCfg (α β : Type) [Fintype α] [Fintype β] (out : List β)
    (label : ListConstLabel β) (state : ListConstState β)
    (input : List (Option α)) (output temp : List (Option β)) :
    (listConstMachine α β out).Cfg where
  l := some label
  var := state
  stk
    | FMStack.input => input
    | FMStack.output => output
    | FMStack.temp => temp

def listConstHalt (α β : Type) [Fintype α] [Fintype β] (out : List β)
    (output : List (Option β)) :
    (listConstMachine α β out).Cfg where
  l := none
  var := ListConstState.done
  stk
    | FMStack.input => []
    | FMStack.output => output
    | FMStack.temp => []

lemma listConst_readInput_step_payload (α β : Type) [Fintype α] [Fintype β]
    (out : List β) (state : ListConstState β)
    (a : α) (input : List (Option α)) (output temp : List (Option β)) :
    (listConstMachine α β out).step
        (listConstCfg α β out ListConstLabel.readInput state (some a :: input) output temp) =
      some (listConstCfg α β out ListConstLabel.readInput
        ListConstState.skip input output temp) := by
  simp [listConstMachine, listConstCfg, ListConstState.isDelimiter, ListConstState.isDone]
  congr
  funext k
  cases k <;> rfl

lemma listConst_readInput_step_nil (α β : Type) [Fintype α] [Fintype β]
    (out : List β) (state : ListConstState β) (output temp : List (Option β)) :
    (listConstMachine α β out).step
        (listConstCfg α β out ListConstLabel.readInput state [] output temp) =
      some (listConstCfg α β out ListConstLabel.moveTemp
        ListConstState.done [] output temp) := by
  simp [listConstMachine, listConstCfg, ListConstState.isDelimiter, ListConstState.isDone]
  congr

set_option backward.isDefEq.respectTransparency false in
lemma listConst_readInput_step_delimiter (α β : Type) [Fintype α] [Fintype β]
    (out : List β) (state : ListConstState β)
    (input : List (Option α)) (output temp : List (Option β)) :
    (listConstMachine α β out).step
        (listConstCfg α β out ListConstLabel.readInput state (none :: input) output temp) =
      some (listConstCfg α β out ListConstLabel.readInput
        ListConstState.delimiter input output ((listConstBlock out).reverse ++ temp)) := by
  simp [listConstMachine, listConstCfg, ListConstState.isDelimiter]
  convert @stepAux_pushAllListConstTemp_afterInputPop α β
    (Turing.FinTM2.decidableEqK (listConstMachine α β out))
    (listConstBlock out) ListConstState.delimiter (none :: input) input output temp
    using 1
  · congr 1
    funext k
    cases k <;> rfl
  · congr
    funext k
    cases k <;> rfl

lemma listConst_moveTemp_step_cons (α β : Type) [Fintype α] [Fintype β]
    (out : List β) (state : ListConstState β)
    (input : List (Option α)) (output : List (Option β)) (b : Option β)
    (temp : List (Option β)) :
    (listConstMachine α β out).step
        (listConstCfg α β out ListConstLabel.moveTemp state input output (b :: temp)) =
      some (listConstCfg α β out (ListConstLabel.pushOutput b)
        (ListConstState.output b) input output temp) := by
  simp [listConstMachine, listConstCfg, ListConstState.isOutput]
  congr
  funext k
  cases k <;> rfl

lemma listConst_moveTemp_step_nil (α β : Type) [Fintype α] [Fintype β]
    (out : List β) (state : ListConstState β) (output : List (Option β)) :
    (listConstMachine α β out).step
        (listConstCfg α β out ListConstLabel.moveTemp state [] output []) =
      some (listConstHalt α β out output) := by
  simp [listConstMachine, listConstCfg, listConstHalt, ListConstState.isOutput]
  congr

lemma listConst_pushOutput_step (α β : Type) [Fintype α] [Fintype β]
    (out : List β) (state : ListConstState β)
    (input : List (Option α)) (output : List (Option β)) (b : Option β)
    (temp : List (Option β)) :
    (listConstMachine α β out).step
        (listConstCfg α β out (ListConstLabel.pushOutput b) state input output temp) =
      some (listConstCfg α β out ListConstLabel.moveTemp state input (b :: output) temp) := by
  simp [listConstMachine, listConstCfg]
  congr
  funext k
  cases k <;> rfl

lemma initList_listConstMachine (α β : Type) [Fintype α] [Fintype β]
    (out : List β) (input : List (Option α)) :
    Turing.initList (listConstMachine α β out) input =
      listConstCfg α β out ListConstLabel.readInput ListConstState.done input [] [] := by
  simp [listConstMachine, listConstCfg, Turing.initList]
  congr
  funext k
  cases k <;> rfl

lemma haltList_listConstMachine (α β : Type) [Fintype α] [Fintype β]
    (out : List β) (output : List (Option β)) :
    Turing.haltList (listConstMachine α β out) output =
      listConstHalt α β out output := by
  simp [listConstMachine, listConstHalt, Turing.haltList]
  congr
  funext k
  cases k <;> rfl

def listConst_readInput_run (α β : Type) [Fintype α] [Fintype β]
    (out : List β) (state : ListConstState β)
    (input : List (Option α)) (output temp : List (Option β)) :
    StateTransition.EvalsToInTime (listConstMachine α β out).step
      (listConstCfg α β out ListConstLabel.readInput state input output temp)
      (some (listConstCfg α β out ListConstLabel.moveTemp ListConstState.done [] output
        ((input.flatMap (listConstExpand out)).reverse ++ temp)))
      (input.length + 1) := by
  induction input generalizing state temp with
  | nil =>
      simpa using evalsToInTimeOne
        (listConst_readInput_step_nil α β out state output temp)
  | cons head input ih =>
      cases head with
      | none =>
          let tm := listConstMachine α β out
          let c₀ := listConstCfg α β out ListConstLabel.readInput state
            (none :: input) output temp
          let c₁ := listConstCfg α β out ListConstLabel.readInput
            ListConstState.delimiter input output ((listConstBlock out).reverse ++ temp)
          have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
            evalsToInTimeOne
              (listConst_readInput_step_delimiter α β out state input output temp)
          have hTail : StateTransition.EvalsToInTime tm.step c₁
              (some (listConstCfg α β out ListConstLabel.moveTemp ListConstState.done
                [] output
                ((input.flatMap (listConstExpand out)).reverse ++
                  ((listConstBlock out).reverse ++ temp))))
              (input.length + 1) :=
            ih ListConstState.delimiter ((listConstBlock out).reverse ++ temp)
          simpa [tm, c₀, c₁, listConstExpand, List.flatMap_cons, List.reverse_append,
            List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            StateTransition.EvalsToInTime.trans tm.step 1 (input.length + 1)
              c₀ c₁
              (some (listConstCfg α β out ListConstLabel.moveTemp ListConstState.done
                [] output
                ((input.flatMap (listConstExpand out)).reverse ++
                  ((listConstBlock out).reverse ++ temp))))
              h₁ hTail
      | some a =>
          let tm := listConstMachine α β out
          let c₀ := listConstCfg α β out ListConstLabel.readInput state
            (some a :: input) output temp
          let c₁ := listConstCfg α β out ListConstLabel.readInput
            ListConstState.skip input output temp
          have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
            evalsToInTimeOne
              (listConst_readInput_step_payload α β out state a input output temp)
          have hTail : StateTransition.EvalsToInTime tm.step c₁
              (some (listConstCfg α β out ListConstLabel.moveTemp ListConstState.done
                [] output ((input.flatMap (listConstExpand out)).reverse ++ temp)))
              (input.length + 1) :=
            ih ListConstState.skip temp
          simpa [tm, c₀, c₁, listConstExpand, List.flatMap_cons, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using
            StateTransition.EvalsToInTime.trans tm.step 1 (input.length + 1)
              c₀ c₁
              (some (listConstCfg α β out ListConstLabel.moveTemp ListConstState.done
                [] output ((input.flatMap (listConstExpand out)).reverse ++ temp)))
              h₁ hTail

def listConst_moveTemp_run (α β : Type) [Fintype α] [Fintype β]
    (out : List β) (state : ListConstState β)
    (output temp : List (Option β)) :
    StateTransition.EvalsToInTime (listConstMachine α β out).step
      (listConstCfg α β out ListConstLabel.moveTemp state [] output temp)
      (some (listConstHalt α β out (temp.reverse ++ output)))
      (2 * temp.length + 1) := by
  induction temp generalizing state output with
  | nil =>
      simpa using
        evalsToInTimeOne (listConst_moveTemp_step_nil α β out state output)
  | cons b temp ih =>
      let tm := listConstMachine α β out
      let c₀ := listConstCfg α β out ListConstLabel.moveTemp state [] output (b :: temp)
      let c₁ := listConstCfg α β out (ListConstLabel.pushOutput b)
        (ListConstState.output b) [] output temp
      let c₂ := listConstCfg α β out ListConstLabel.moveTemp
        (ListConstState.output b) [] (b :: output) temp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (listConst_moveTemp_step_cons α β out state [] output b temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (listConst_pushOutput_step α β out (ListConstState.output b) [] output b temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (listConstHalt α β out (temp.reverse ++ (b :: output))))
          (2 * temp.length + 1) :=
        ih (ListConstState.output b) (b :: output)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * temp.length + 1)
          c₀ c₂ (some (listConstHalt α β out (temp.reverse ++ (b :: output))))
          h₁₂ hTail

/-- The fixed-output list-map expansion program computes delimiter expansion. -/
def listConst_outputs (α β : Type) [Fintype α] [Fintype β]
    (out : List β) (input : List (Option α)) :
    Turing.TM2OutputsInTime (listConstMachine α β out)
      input (some (input.flatMap (listConstExpand out)))
      ((2 * out.length + 3) * input.length + 2) := by
  let tm := listConstMachine α β out
  let expanded := input.flatMap (listConstExpand out)
  let mid := listConstCfg α β out ListConstLabel.moveTemp ListConstState.done
    [] [] expanded.reverse
  let done := listConstHalt α β out expanded
  have hRead : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some mid) (input.length + 1) := by
    simpa [tm, mid, expanded, initList_listConstMachine] using
      listConst_readInput_run α β out ListConstState.done input [] []
  have hMove : StateTransition.EvalsToInTime tm.step mid
      (some done) (2 * expanded.length + 1) := by
    simpa [tm, mid, done, expanded, List.length_reverse] using
      listConst_moveTemp_run α β out ListConstState.done [] expanded.reverse
  have hAll : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some done) ((2 * expanded.length + 1) + (input.length + 1)) :=
    StateTransition.EvalsToInTime.trans tm.step (input.length + 1)
      (2 * expanded.length + 1) (Turing.initList tm input) mid (some done) hRead hMove
  change StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
    (some (Turing.haltList tm expanded)) ((2 * out.length + 3) * input.length + 2)
  rw [haltList_listConstMachine]
  refine
    { steps := hAll.steps
      evals_in_steps := hAll.evals_in_steps
      steps_le_m := ?_ }
  have hExpanded : expanded.length ≤ (out.length + 1) * input.length := by
    simpa [expanded] using listConstExpand_length_le (α := α) (β := β) out input
  have hSteps := hAll.steps_le_m
  have hTime :
      (2 * expanded.length + 1) + (input.length + 1) ≤
        (2 * out.length + 3) * input.length + 2 := by
    have hMain :
        2 * expanded.length + input.length ≤
          (2 * out.length + 3) * input.length := by
      calc
        2 * expanded.length + input.length ≤
            2 * ((out.length + 1) * input.length) + input.length := by
          exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hExpanded) input.length
        _ = (2 * (out.length + 1)) * input.length + input.length := by
          rw [Nat.mul_assoc]
        _ = (2 * (out.length + 1) + 1) * input.length := by
          rw [Nat.add_mul, Nat.one_mul]
        _ = (2 * out.length + 3) * input.length := by
          congr 1
    omega
  exact hSteps.trans hTime

noncomputable def listConstComputableInPolyTime
    (X Y : EncodedType) (y : Y.Carrier) :
    Turing.TM2ComputableInPolyTime
      (EncodedType.list X).encode
      (EncodedType.list Y).encode
      (fun xs : List X.Carrier => xs.map fun _ => y) where
  tm := listConstMachine X.Symbol Y.Symbol (Y.encode y)
  inputAlphabet := Equiv.refl (Option X.Symbol)
  outputAlphabet := Equiv.refl (Option Y.Symbol)
  time := Polynomial.C (2 * (Y.encode y).length + 3) * Polynomial.X + 2
  outputsFun xs := by
    convert
      listConst_outputs X.Symbol Y.Symbol (Y.encode y)
        ((EncodedType.list X).encode xs) using 1
    · change List.map id ((EncodedType.list X).encode xs) = (EncodedType.list X).encode xs
      simp
    · change
        some (List.map id ((EncodedType.list Y).encode (xs.map fun _ => y))) =
          some (((EncodedType.list X).encode xs).flatMap (listConstExpand (Y.encode y)))
      rw [listConst_flatMap_encode X Y y xs]
      exact congrArg some (List.map_id ((EncodedType.list Y).encode (xs.map fun _ => y)))
    · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
      rfl

/-- Map every encoded-list symbol by a fixed alphabet map, preserving delimiters. -/
def listSymbolMapKeep {α β : Type} (mapSym : α → β) : Option α → Option (Option β)
  | some a => some (some (mapSym a))
  | none => some none

lemma filterMap_listSymbolMapKeep {α β : Type} (mapSym : α → β)
    (input : List (Option α)) :
    input.filterMap (listSymbolMapKeep mapSym) = input.map (Option.map mapSym) := by
  induction input with
  | nil =>
      simp [listSymbolMapKeep]
  | cons a input ih =>
      cases a <;> simp [listSymbolMapKeep] <;> exact ih

lemma listSymbolMap_target_encode (X Y : EncodedType)
    (f : X.Carrier → Y.Carrier) (mapSym : X.Symbol → Y.Symbol)
    (hf : ∀ x, Y.encode (f x) = (X.encode x).map mapSym)
    (xs : List X.Carrier) :
    (EncodedType.list Y).encode (xs.map f) =
      ((EncodedType.list X).encode xs).map (Option.map mapSym) := by
  induction xs with
  | nil =>
      simp [EncodedType.list]
  | cons x xs ih =>
      have ih' :
          List.flatMap (fun x => (Y.encode x).map some ++ [none]) (xs.map f) =
            List.map (Option.map mapSym)
              (List.flatMap (fun x => (X.encode x).map some ++ [none]) xs) := by
        simpa [EncodedType.list] using ih
      simp [EncodedType.list, hf x, ih', List.map_append, Function.comp_def]

lemma listSymbolMap_filterMap_encode (X Y : EncodedType)
    (f : X.Carrier → Y.Carrier) (mapSym : X.Symbol → Y.Symbol)
    (hf : ∀ x, Y.encode (f x) = (X.encode x).map mapSym)
    (xs : List X.Carrier) :
    ((EncodedType.list X).encode xs).filterMap (listSymbolMapKeep mapSym) =
      (EncodedType.list Y).encode (xs.map f) := by
  rw [filterMap_listSymbolMapKeep]
  exact (listSymbolMap_target_encode X Y f mapSym hf xs).symm

/--
TM2 polynomial-time computation of list-map when the element map is implemented
by a fixed symbol map on encodings.  This is a structural subcase of list-map,
not the arbitrary `list_map_map` closure theorem.
-/
noncomputable def listSymbolMapComputableInPolyTime
    (X Y : EncodedType) (f : X.Carrier → Y.Carrier)
    (mapSym : X.Symbol → Y.Symbol)
    (hf : ∀ x, Y.encode (f x) = (X.encode x).map mapSym) :
    Turing.TM2ComputableInPolyTime
      (EncodedType.list X).encode
      (EncodedType.list Y).encode
      (fun xs : List X.Carrier => xs.map f) where
  tm :=
    filterMapMachine
      (Option X.Symbol)
      (Option Y.Symbol)
      (listSymbolMapKeep mapSym)
  inputAlphabet := Equiv.refl (Option X.Symbol)
  outputAlphabet := Equiv.refl (Option Y.Symbol)
  time := 4 * Polynomial.X + 2
  outputsFun xs := by
    convert
      filterMap_outputs
        (Option X.Symbol)
        (Option Y.Symbol)
        (listSymbolMapKeep mapSym)
        ((EncodedType.list X).encode xs) using 1
    · change List.map id ((EncodedType.list X).encode xs) = (EncodedType.list X).encode xs
      simp
    · change
        some (List.map id ((EncodedType.list Y).encode (xs.map f))) =
          some (((EncodedType.list X).encode xs).filterMap (listSymbolMapKeep mapSym))
      rw [listSymbolMap_filterMap_encode X Y f mapSym hf xs]
      exact congrArg some (List.map_id ((EncodedType.list Y).encode (xs.map f)))
    · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
      rfl

end TM2Programs
end ComplexityReduction
