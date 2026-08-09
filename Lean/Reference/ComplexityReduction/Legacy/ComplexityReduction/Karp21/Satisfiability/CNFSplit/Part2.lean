import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.CNFSplit.Part1

namespace ComplexityReduction
namespace Karp21
open ComplexityReduction
open Turing.TM2.Stmt

lemma cnfSplitFoldStepChoice_readRightPayload_step_nil
    (state : CNFSplitFoldStepChoiceState)
    (output temp : List cnfSplitFoldStepChoiceOutputSymbol) :
    cnfSplitFoldStepChoiceMachine.step
        (cnfSplitFoldStepChoiceCfg .readRightPayload state [] output temp) =
      some (cnfSplitFoldStepChoiceCfg (.moveTemp true)
        (.input none) [] output temp) := by
  simp [cnfSplitFoldStepChoiceMachine, cnfSplitFoldStepChoiceCfg,
    cnfSplitFoldStepChoiceInputState]
  congr

lemma cnfSplitFoldStepChoice_moveTemp_step_cons
    (tag : Bool) (s : cnfSplitFoldStepChoiceOutputSymbol)
    (state : CNFSplitFoldStepChoiceState)
    (input : List cnfSplitFoldStepChoiceInputSymbol)
    (output temp : List cnfSplitFoldStepChoiceOutputSymbol) :
    cnfSplitFoldStepChoiceMachine.step
        (cnfSplitFoldStepChoiceCfg (.moveTemp tag) state input output (s :: temp)) =
      some (cnfSplitFoldStepChoiceCfg (.pushOutput tag s)
        (.output (some s)) input output temp) := by
  simp [cnfSplitFoldStepChoiceMachine, cnfSplitFoldStepChoiceCfg,
    cnfSplitFoldStepChoiceOutputState]
  congr
  funext k
  cases k <;> rfl

lemma cnfSplitFoldStepChoice_moveTemp_step_nil
    (tag : Bool) (state : CNFSplitFoldStepChoiceState)
    (input : List cnfSplitFoldStepChoiceInputSymbol)
    (output : List cnfSplitFoldStepChoiceOutputSymbol) :
    cnfSplitFoldStepChoiceMachine.step
        (cnfSplitFoldStepChoiceCfg (.moveTemp tag) state input output []) =
      some (cnfSplitFoldStepChoiceCfg (.writeTag tag)
        (.output none) input output []) := by
  simp [cnfSplitFoldStepChoiceMachine, cnfSplitFoldStepChoiceCfg,
    cnfSplitFoldStepChoiceOutputState]
  congr

lemma cnfSplitFoldStepChoice_pushOutput_step
    (tag : Bool) (s : cnfSplitFoldStepChoiceOutputSymbol)
    (state : CNFSplitFoldStepChoiceState)
    (input : List cnfSplitFoldStepChoiceInputSymbol)
    (output temp : List cnfSplitFoldStepChoiceOutputSymbol) :
    cnfSplitFoldStepChoiceMachine.step
        (cnfSplitFoldStepChoiceCfg (.pushOutput tag s) state input output temp) =
      some (cnfSplitFoldStepChoiceCfg (.moveTemp tag)
        state input (s :: output) temp) := by
  simp [cnfSplitFoldStepChoiceMachine, cnfSplitFoldStepChoiceCfg]
  congr
  funext k
  cases k <;> rfl

lemma cnfSplitFoldStepChoice_writeTag_step
    (tag : Bool) (output : List cnfSplitFoldStepChoiceOutputSymbol) :
    cnfSplitFoldStepChoiceMachine.step
        (cnfSplitFoldStepChoiceCfg (.writeTag tag) (.output none) [] output []) =
      some (cnfSplitFoldStepChoiceHalt (Sum.inl tag :: output)) := by
  simp [cnfSplitFoldStepChoiceMachine, cnfSplitFoldStepChoiceCfg,
    cnfSplitFoldStepChoiceHalt]
  congr
  funext k
  cases k <;> rfl

lemma cnfSplitFoldStepChoice_initList
    (input : List cnfSplitFoldStepChoiceInputSymbol) :
    Turing.initList cnfSplitFoldStepChoiceMachine input =
      cnfSplitFoldStepChoiceCfg .readAcc (.input none) input [] [] := by
  simp [cnfSplitFoldStepChoiceMachine, cnfSplitFoldStepChoiceCfg,
    Turing.initList]
  congr
  funext k
  cases k <;> rfl

lemma cnfSplitFoldStepChoice_haltList
    (output : List cnfSplitFoldStepChoiceOutputSymbol) :
    Turing.haltList cnfSplitFoldStepChoiceMachine output =
      cnfSplitFoldStepChoiceHalt output := by
  simp [cnfSplitFoldStepChoiceMachine, cnfSplitFoldStepChoiceHalt,
    Turing.haltList]
  congr
  funext k
  cases k <;> rfl

def cnfSplitFoldStepChoice_readAcc_run
    (acc : List cnfSplitFoldAccEncodedType.Symbol)
    (state : CNFSplitFoldStepChoiceState)
    (rest : List cnfSplitFoldStepChoiceInputSymbol)
    (output temp : List cnfSplitFoldStepChoiceOutputSymbol) :
    StateTransition.EvalsToInTime
      cnfSplitFoldStepChoiceMachine.step
      (cnfSplitFoldStepChoiceCfg .readAcc state
        (List.append (acc.map cnfSplitFoldStepChoiceAccInputSymbol)
          ((none : cnfSplitFoldStepChoiceInputSymbol) :: rest)) output temp)
      (some (cnfSplitFoldStepChoiceCfg .readInstructionTag (.input (some none))
        rest output ((acc.map cnfSplitFoldStepChoiceAccOutputSymbol).reverse ++ temp)))
      (2 * acc.length + 1) := by
  induction acc generalizing state temp with
  | nil =>
      simpa [cnfSplitFoldStepChoiceAccInputSymbol] using
        TM2Programs.evalsToInTimeOne
          (cnfSplitFoldStepChoice_readAcc_step_delim state rest output temp)
  | cons s acc ih =>
      let mapped := cnfSplitFoldStepChoiceAccOutputSymbol s
      let tm := cnfSplitFoldStepChoiceMachine
      let c₀ := cnfSplitFoldStepChoiceCfg .readAcc state
        (some (Sum.inl s) ::
          List.append (acc.map cnfSplitFoldStepChoiceAccInputSymbol)
            ((none : cnfSplitFoldStepChoiceInputSymbol) :: rest)) output temp
      let c₁ := cnfSplitFoldStepChoiceCfg (.pushAccTemp mapped)
        (.input (some (some (Sum.inl s))))
        (List.append (acc.map cnfSplitFoldStepChoiceAccInputSymbol)
          ((none : cnfSplitFoldStepChoiceInputSymbol) :: rest)) output temp
      let c₂ := cnfSplitFoldStepChoiceCfg .readAcc
        (.input (some (some (Sum.inl s))))
        (List.append (acc.map cnfSplitFoldStepChoiceAccInputSymbol)
          ((none : cnfSplitFoldStepChoiceInputSymbol) :: rest)) output (mapped :: temp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 := by
        simpa [tm, c₀, c₁, mapped, cnfSplitFoldStepChoiceAccInputSymbol] using
          TM2Programs.evalsToInTimeOne
              (cnfSplitFoldStepChoice_readAcc_step_cons s
              state
              (List.append (acc.map cnfSplitFoldStepChoiceAccInputSymbol)
                ((none : cnfSplitFoldStepChoiceInputSymbol) :: rest)) output temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 := by
        simpa [tm, c₁, c₂] using
          TM2Programs.evalsToInTimeOne
              (cnfSplitFoldStepChoice_pushAccTemp_step mapped
              (.input (some (some (Sum.inl s))))
              (List.append (acc.map cnfSplitFoldStepChoiceAccInputSymbol)
                ((none : cnfSplitFoldStepChoiceInputSymbol) :: rest)) output temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (cnfSplitFoldStepChoiceCfg .readInstructionTag (.input (some none))
            rest output
            ((acc.map cnfSplitFoldStepChoiceAccOutputSymbol).reverse ++
              (mapped :: temp))))
          (2 * acc.length + 1) :=
        ih (.input (some (some (Sum.inl s)))) (mapped :: temp)
      simpa [tm, c₀, c₁, c₂, mapped, cnfSplitFoldStepChoiceAccInputSymbol,
        List.map_cons, List.reverse_cons, List.append_assoc, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * acc.length + 1)
          c₀ c₂
          (some (cnfSplitFoldStepChoiceCfg .readInstructionTag (.input (some none))
            rest output
            ((acc.map cnfSplitFoldStepChoiceAccOutputSymbol).reverse ++ (mapped :: temp))))
          h₁₂ hTail

def cnfSplitFoldStepChoice_clearAcc_run
    (state : CNFSplitFoldStepChoiceState)
    (input : List cnfSplitFoldStepChoiceInputSymbol)
    (output temp : List cnfSplitFoldStepChoiceOutputSymbol) :
    StateTransition.EvalsToInTime
      cnfSplitFoldStepChoiceMachine.step
      (cnfSplitFoldStepChoiceCfg .clearAcc state input output temp)
      (some (cnfSplitFoldStepChoiceCfg .readLeftPayload (.output none)
        input output []))
      (temp.length + 1) := by
  induction temp generalizing state with
  | nil =>
      simpa using
        TM2Programs.evalsToInTimeOne
          (cnfSplitFoldStepChoice_clearAcc_step_nil state input output)
  | cons s temp ih =>
      let tm := cnfSplitFoldStepChoiceMachine
      let c₀ := cnfSplitFoldStepChoiceCfg .clearAcc state input output (s :: temp)
      let c₁ := cnfSplitFoldStepChoiceCfg .clearAcc
        (.output (some s)) input output temp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        by
          simpa [tm, c₀, c₁] using
            TM2Programs.evalsToInTimeOne
              (cnfSplitFoldStepChoice_clearAcc_step_cons s state input output temp)
      have hTail : StateTransition.EvalsToInTime tm.step c₁
          (some (cnfSplitFoldStepChoiceCfg .readLeftPayload (.output none)
            input output []))
          (temp.length + 1) :=
        ih (.output (some s))
      simpa [tm, c₀, c₁, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step 1 (temp.length + 1)
          c₀ c₁
          (some (cnfSplitFoldStepChoiceCfg .readLeftPayload (.output none)
            input output []))
          h₁ hTail

def cnfSplitFoldStepChoice_readLeftPayload_run
    (payload : List EncodedType.nat.Symbol)
    (state : CNFSplitFoldStepChoiceState)
    (output temp : List cnfSplitFoldStepChoiceOutputSymbol) :
    StateTransition.EvalsToInTime
      cnfSplitFoldStepChoiceMachine.step
      (cnfSplitFoldStepChoiceCfg .readLeftPayload state
        (payload.map cnfSplitFoldStepChoiceNatPayloadInputSymbol) output temp)
      (some (cnfSplitFoldStepChoiceCfg (.moveTemp false) (.input none)
        [] output
        ((payload.map cnfSplitFoldStepChoiceNatOutputSymbol).reverse ++ temp)))
      (2 * payload.length + 1) := by
  induction payload generalizing state temp with
  | nil =>
      simpa using
        TM2Programs.evalsToInTimeOne
          (cnfSplitFoldStepChoice_readLeftPayload_step_nil state output temp)
  | cons s payload ih =>
      let mapped := cnfSplitFoldStepChoiceNatOutputSymbol s
      let tm := cnfSplitFoldStepChoiceMachine
      let c₀ := cnfSplitFoldStepChoiceCfg .readLeftPayload state
        (some (Sum.inr (Sum.inr (Sum.inl s))) ::
          payload.map cnfSplitFoldStepChoiceNatPayloadInputSymbol) output temp
      let c₁ := cnfSplitFoldStepChoiceCfg (.pushLeftTemp mapped)
        (.input (some (some (Sum.inr (Sum.inr (Sum.inl s))))))
        (payload.map cnfSplitFoldStepChoiceNatPayloadInputSymbol) output temp
      let c₂ := cnfSplitFoldStepChoiceCfg .readLeftPayload
        (.input (some (some (Sum.inr (Sum.inr (Sum.inl s))))))
        (payload.map cnfSplitFoldStepChoiceNatPayloadInputSymbol) output
        (mapped :: temp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        by
          simpa [tm, c₀, c₁, mapped, cnfSplitFoldStepChoiceNatPayloadInputSymbol] using
            TM2Programs.evalsToInTimeOne
              (cnfSplitFoldStepChoice_readLeftPayload_step_cons s
                state
                (payload.map cnfSplitFoldStepChoiceNatPayloadInputSymbol) output temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 := by
        simpa [tm, c₁, c₂] using
          TM2Programs.evalsToInTimeOne
            (cnfSplitFoldStepChoice_pushLeftTemp_step mapped
              (.input (some (some (Sum.inr (Sum.inr (Sum.inl s))))))
              (payload.map cnfSplitFoldStepChoiceNatPayloadInputSymbol) output temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (cnfSplitFoldStepChoiceCfg (.moveTemp false) (.input none)
            [] output
            ((payload.map cnfSplitFoldStepChoiceNatOutputSymbol).reverse ++
              (mapped :: temp))))
          (2 * payload.length + 1) :=
        ih (.input (some (some (Sum.inr (Sum.inr (Sum.inl s)))))) (mapped :: temp)
      simpa [tm, c₀, c₁, c₂, mapped, cnfSplitFoldStepChoiceNatPayloadInputSymbol,
        List.map_cons, List.reverse_cons, List.append_assoc, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * payload.length + 1)
          c₀ c₂
          (some (cnfSplitFoldStepChoiceCfg (.moveTemp false) (.input none)
            [] output
            ((payload.map cnfSplitFoldStepChoiceNatOutputSymbol).reverse ++ (mapped :: temp))))
          h₁₂ hTail

def cnfSplitFoldStepChoice_readRightPayload_run
    (payload : List clauseStructuredEncodedType.Symbol)
    (state : CNFSplitFoldStepChoiceState)
    (output temp : List cnfSplitFoldStepChoiceOutputSymbol) :
    StateTransition.EvalsToInTime
      cnfSplitFoldStepChoiceMachine.step
      (cnfSplitFoldStepChoiceCfg .readRightPayload state
        (payload.map cnfSplitFoldStepChoiceClausePayloadInputSymbol) output temp)
      (some (cnfSplitFoldStepChoiceCfg (.moveTemp true) (.input none)
        [] output
        ((payload.map cnfSplitFoldStepChoiceClauseOutputSymbol).reverse ++ temp)))
      (2 * payload.length + 1) := by
  induction payload generalizing state temp with
  | nil =>
      simpa using
        TM2Programs.evalsToInTimeOne
          (cnfSplitFoldStepChoice_readRightPayload_step_nil state output temp)
  | cons s payload ih =>
      let mapped := cnfSplitFoldStepChoiceClauseOutputSymbol s
      let tm := cnfSplitFoldStepChoiceMachine
      let c₀ := cnfSplitFoldStepChoiceCfg .readRightPayload state
        (some (Sum.inr (Sum.inr (Sum.inr s))) ::
          payload.map cnfSplitFoldStepChoiceClausePayloadInputSymbol) output temp
      let c₁ := cnfSplitFoldStepChoiceCfg (.pushRightTemp mapped)
        (.input (some (some (Sum.inr (Sum.inr (Sum.inr s))))))
        (payload.map cnfSplitFoldStepChoiceClausePayloadInputSymbol) output temp
      let c₂ := cnfSplitFoldStepChoiceCfg .readRightPayload
        (.input (some (some (Sum.inr (Sum.inr (Sum.inr s))))))
        (payload.map cnfSplitFoldStepChoiceClausePayloadInputSymbol) output
        (mapped :: temp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        by
          simpa [tm, c₀, c₁, mapped, cnfSplitFoldStepChoiceClausePayloadInputSymbol] using
            TM2Programs.evalsToInTimeOne
              (cnfSplitFoldStepChoice_readRightPayload_step_cons s
                state
                (payload.map cnfSplitFoldStepChoiceClausePayloadInputSymbol) output temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 := by
        simpa [tm, c₁, c₂] using
          TM2Programs.evalsToInTimeOne
            (cnfSplitFoldStepChoice_pushRightTemp_step mapped
              (.input (some (some (Sum.inr (Sum.inr (Sum.inr s))))))
              (payload.map cnfSplitFoldStepChoiceClausePayloadInputSymbol) output temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (cnfSplitFoldStepChoiceCfg (.moveTemp true) (.input none)
            [] output
            ((payload.map cnfSplitFoldStepChoiceClauseOutputSymbol).reverse ++
              (mapped :: temp))))
          (2 * payload.length + 1) :=
        ih (.input (some (some (Sum.inr (Sum.inr (Sum.inr s)))))) (mapped :: temp)
      simpa [tm, c₀, c₁, c₂, mapped, cnfSplitFoldStepChoiceClausePayloadInputSymbol,
        List.map_cons, List.reverse_cons, List.append_assoc, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * payload.length + 1)
          c₀ c₂
          (some (cnfSplitFoldStepChoiceCfg (.moveTemp true) (.input none)
            [] output
            ((payload.map cnfSplitFoldStepChoiceClauseOutputSymbol).reverse ++ (mapped :: temp))))
          h₁₂ hTail

def cnfSplitFoldStepChoice_moveTemp_run
    (tag : Bool) (state : CNFSplitFoldStepChoiceState)
    (input : List cnfSplitFoldStepChoiceInputSymbol)
    (output temp : List cnfSplitFoldStepChoiceOutputSymbol) :
    StateTransition.EvalsToInTime
      cnfSplitFoldStepChoiceMachine.step
      (cnfSplitFoldStepChoiceCfg (.moveTemp tag) state input output temp)
      (some (cnfSplitFoldStepChoiceCfg (.writeTag tag) (.output none)
        input (temp.reverse ++ output) []))
      (2 * temp.length + 1) := by
  induction temp generalizing state output with
  | nil =>
      simpa using
        TM2Programs.evalsToInTimeOne
          (cnfSplitFoldStepChoice_moveTemp_step_nil tag state input output)
  | cons s temp ih =>
      let tm := cnfSplitFoldStepChoiceMachine
      let c₀ := cnfSplitFoldStepChoiceCfg (.moveTemp tag) state input output (s :: temp)
      let c₁ := cnfSplitFoldStepChoiceCfg (.pushOutput tag s)
        (.output (some s)) input output temp
      let c₂ := cnfSplitFoldStepChoiceCfg (.moveTemp tag)
        (.output (some s)) input (s :: output) temp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne
          (cnfSplitFoldStepChoice_moveTemp_step_cons tag s state input output temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        TM2Programs.evalsToInTimeOne
          (cnfSplitFoldStepChoice_pushOutput_step tag s
            (.output (some s)) input output temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (cnfSplitFoldStepChoiceCfg (.writeTag tag) (.output none)
            input (temp.reverse ++ (s :: output)) []))
          (2 * temp.length + 1) :=
        ih (.output (some s)) (s :: output)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * temp.length + 1)
          c₀ c₂
          (some (cnfSplitFoldStepChoiceCfg (.writeTag tag) (.output none)
            input (temp.reverse ++ (s :: output)) []))
          h₁₂ hTail

def cnfSplitFoldStepChoiceLeftInputStack
    (acc : List cnfSplitFoldAccEncodedType.Symbol)
    (payload : List EncodedType.nat.Symbol) :
    List cnfSplitFoldStepChoiceInputSymbol :=
  List.append (acc.map cnfSplitFoldStepChoiceAccInputSymbol)
    ((none : cnfSplitFoldStepChoiceInputSymbol) ::
      cnfSplitFoldStepChoiceInstructionTagInputSymbol false ::
      payload.map cnfSplitFoldStepChoiceNatPayloadInputSymbol)

def cnfSplitFoldStepChoiceRightInputStack
    (acc : List cnfSplitFoldAccEncodedType.Symbol)
    (payload : List clauseStructuredEncodedType.Symbol) :
    List cnfSplitFoldStepChoiceInputSymbol :=
  List.append (acc.map cnfSplitFoldStepChoiceAccInputSymbol)
    ((none : cnfSplitFoldStepChoiceInputSymbol) ::
      cnfSplitFoldStepChoiceInstructionTagInputSymbol true ::
      payload.map cnfSplitFoldStepChoiceClausePayloadInputSymbol)

theorem list_append_cons_eq_append_singleton {α : Type}
    (xs : List α) (x : α) (ys : List α) :
    xs ++ x :: ys = xs ++ [x] ++ ys := by
  induction xs with
  | nil =>
      rfl
  | cons y xs ih =>
      change y :: (xs ++ x :: ys) = y :: (xs ++ [x] ++ ys)
      rw [ih]

theorem list_length_append_cons {α : Type}
    (xs : List α) (x : α) (ys : List α) :
    (xs ++ x :: ys).length = xs.length + (1 + ys.length) := by
  induction xs with
  | nil =>
      simp
      omega
  | cons y xs ih =>
      change (xs ++ x :: ys).length + 1 = (xs.length + 1) + (1 + ys.length)
      rw [ih]
      omega

theorem cnfSplitFoldStepChoiceLeftInputStack_eq_encode
    (acc : cnfSplitFoldAccEncodedType.Carrier) (next : Nat) :
    cnfSplitFoldStepChoiceLeftInputStack
        (cnfSplitFoldAccEncodedType.encode acc) (EncodedType.nat.encode next) =
      cnfSplitFoldStepInputEncodedType.encode (acc, Sum.inl next) := by
  dsimp [cnfSplitFoldStepChoiceLeftInputStack, cnfSplitFoldStepInputEncodedType,
    cnfSplitInstructionEncodedType, cnfSplitFoldStepChoiceAccInputSymbol,
    cnfSplitFoldStepChoiceInstructionTagInputSymbol,
    cnfSplitFoldStepChoiceNatPayloadInputSymbol, EncodedType.prod, EncodedType.sum]
  have hAcc :
      (cnfSplitFoldAccEncodedType.encode acc).map cnfSplitFoldStepChoiceAccInputSymbol =
        (cnfSplitFoldAccEncodedType.encode acc).map (fun s => some (Sum.inl s)) := by
    apply List.map_congr_left
    intro s _
    rfl
  have hPayload :
      (EncodedType.nat.encode next).map cnfSplitFoldStepChoiceNatPayloadInputSymbol =
        (EncodedType.nat.encode next).map
          (((fun s => some (Sum.inr s)) ∘ fun s => Sum.inr (Sum.inl s))) := by
    apply List.map_congr_left
    intro s _
    rfl
  rw [hAcc, hPayload]
  rw [List.map_map]
  exact
    list_append_cons_eq_append_singleton
      ((cnfSplitFoldAccEncodedType.encode acc).map (fun s => some (Sum.inl s)))
      (none : cnfSplitFoldStepChoiceInputSymbol)
      (some (Sum.inr (Sum.inl false)) ::
        (EncodedType.nat.encode next).map
          (((fun s => some (Sum.inr s)) ∘ fun s => Sum.inr (Sum.inl s))))

theorem cnfSplitFoldStepChoiceRightInputStack_eq_encode
    (acc : cnfSplitFoldAccEncodedType.Carrier) (c : clauseStructuredEncodedType.Carrier) :
    cnfSplitFoldStepChoiceRightInputStack
        (cnfSplitFoldAccEncodedType.encode acc) (clauseStructuredEncodedType.encode c) =
      cnfSplitFoldStepInputEncodedType.encode (acc, Sum.inr c) := by
  dsimp [cnfSplitFoldStepChoiceRightInputStack, cnfSplitFoldStepInputEncodedType,
    cnfSplitInstructionEncodedType, cnfSplitFoldStepChoiceAccInputSymbol,
    cnfSplitFoldStepChoiceInstructionTagInputSymbol,
    cnfSplitFoldStepChoiceClausePayloadInputSymbol, EncodedType.prod, EncodedType.sum]
  have hAcc :
      (cnfSplitFoldAccEncodedType.encode acc).map cnfSplitFoldStepChoiceAccInputSymbol =
        (cnfSplitFoldAccEncodedType.encode acc).map (fun s => some (Sum.inl s)) := by
    apply List.map_congr_left
    intro s _
    rfl
  have hPayload :
      (clauseStructuredEncodedType.encode c).map cnfSplitFoldStepChoiceClausePayloadInputSymbol =
        (clauseStructuredEncodedType.encode c).map
          (((fun s => some (Sum.inr s)) ∘ fun s => Sum.inr (Sum.inr s))) := by
    apply List.map_congr_left
    intro s _
    rfl
  rw [hAcc, hPayload]
  rw [List.map_map]
  exact
    list_append_cons_eq_append_singleton
      ((cnfSplitFoldAccEncodedType.encode acc).map (fun s => some (Sum.inl s)))
      (none : cnfSplitFoldStepChoiceInputSymbol)
      (some (Sum.inr (Sum.inl true)) ::
        (clauseStructuredEncodedType.encode c).map
          (((fun s => some (Sum.inr s)) ∘ fun s => Sum.inr (Sum.inr s))))

theorem cnfSplitFoldStepChoiceLeftOutput_eq_encode
    (acc : cnfSplitFoldAccEncodedType.Carrier) (next : Nat) :
    Sum.inl false ::
        (EncodedType.nat.encode next).map cnfSplitFoldStepChoiceNatOutputSymbol =
      cnfSplitFoldStepChoiceEncodedType.encode
        (cnfSplitFoldStepChoice (acc, Sum.inl next)) := by
  simp [cnfSplitFoldStepChoice, cnfSplitFoldStepChoiceEncodedType,
    cnfSplitFoldStepChoiceNatOutputSymbol, EncodedType.sum]

theorem cnfSplitFoldStepChoiceRightOutput_eq_encode
    (acc : cnfSplitFoldAccEncodedType.Carrier) (c : clauseStructuredEncodedType.Carrier) :
    Sum.inl true ::
        ((cnfSplitFoldAccEncodedType.encode acc).map cnfSplitFoldStepChoiceAccOutputSymbol ++
          cnfSplitFoldStepChoiceRightDelimiter ::
            (clauseStructuredEncodedType.encode c).map
              cnfSplitFoldStepChoiceClauseOutputSymbol) =
      cnfSplitFoldStepChoiceEncodedType.encode
        (cnfSplitFoldStepChoice (acc, Sum.inr c)) := by
  dsimp [cnfSplitFoldStepChoice, cnfSplitFoldStepChoiceEncodedType,
    cnfSplitFoldStepRightPayloadEncodedType, cnfSplitFoldStepChoiceAccOutputSymbol,
    cnfSplitFoldStepChoiceRightDelimiter, cnfSplitFoldStepChoiceClauseOutputSymbol,
    EncodedType.prod, EncodedType.sum]
  have hAcc :
      (cnfSplitFoldAccEncodedType.encode acc).map cnfSplitFoldStepChoiceAccOutputSymbol =
        (cnfSplitFoldAccEncodedType.encode acc).map
          (fun s => Sum.inr (Sum.inr (some (Sum.inl s)))) := by
    apply List.map_congr_left
    intro s _
    rfl
  have hClause :
      (clauseStructuredEncodedType.encode c).map cnfSplitFoldStepChoiceClauseOutputSymbol =
        (clauseStructuredEncodedType.encode c).map
          (fun s => Sum.inr (Sum.inr (some (Sum.inr s)))) := by
    apply List.map_congr_left
    intro s _
    rfl
  rw [hAcc, hClause]
  simp [List.map_append, List.map_map, Function.comp_def]
  rfl

def cnfSplitFoldStepChoice_outputs_left
    (acc : List cnfSplitFoldAccEncodedType.Symbol)
    (payload : List EncodedType.nat.Symbol) :
    Turing.TM2OutputsInTime
      cnfSplitFoldStepChoiceMachine
      (cnfSplitFoldStepChoiceLeftInputStack acc payload)
      (some (Sum.inl false ::
        payload.map cnfSplitFoldStepChoiceNatOutputSymbol))
      (4 * (cnfSplitFoldStepChoiceLeftInputStack acc payload).length + 8) := by
  let tm := cnfSplitFoldStepChoiceMachine
  let accMapped := acc.map cnfSplitFoldStepChoiceAccOutputSymbol
  let payloadInput := payload.map cnfSplitFoldStepChoiceNatPayloadInputSymbol
  let payloadMapped := payload.map cnfSplitFoldStepChoiceNatOutputSymbol
  let rest : List cnfSplitFoldStepChoiceInputSymbol :=
    cnfSplitFoldStepChoiceInstructionTagInputSymbol false :: payloadInput
  let input := cnfSplitFoldStepChoiceLeftInputStack acc payload
  let cTag := cnfSplitFoldStepChoiceCfg .readInstructionTag (.input (some none))
    rest [] accMapped.reverse
  let cClear := cnfSplitFoldStepChoiceCfg .clearAcc
    (.input (some (some (Sum.inr (Sum.inl false))))) payloadInput [] accMapped.reverse
  let cPayload := cnfSplitFoldStepChoiceCfg .readLeftPayload (.output none)
    payloadInput [] []
  let cMove := cnfSplitFoldStepChoiceCfg (.moveTemp false) (.input none)
    [] [] payloadMapped.reverse
  let cWrite := cnfSplitFoldStepChoiceCfg (.writeTag false) (.output none)
    [] payloadMapped []
  let done := cnfSplitFoldStepChoiceHalt (Sum.inl false :: payloadMapped)
  have hRead : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some cTag) (2 * acc.length + 1) := by
    simpa [tm, input, rest, cTag, accMapped,
      cnfSplitFoldStepChoiceAccInputSymbol,
      cnfSplitFoldStepChoiceInstructionTagInputSymbol,
      cnfSplitFoldStepChoiceLeftInputStack,
      cnfSplitFoldStepChoice_initList] using
      cnfSplitFoldStepChoice_readAcc_run acc (.input none) rest [] []
  have hTag : StateTransition.EvalsToInTime tm.step cTag (some cClear) 1 := by
    simpa [tm, cTag, cClear, rest, payloadInput, accMapped,
      cnfSplitFoldStepChoiceInstructionTagInputSymbol] using
      TM2Programs.evalsToInTimeOne
        (cnfSplitFoldStepChoice_readInstructionTag_step_left
          payloadInput [] accMapped.reverse)
  have hClear : StateTransition.EvalsToInTime tm.step cClear (some cPayload)
      (accMapped.reverse.length + 1) := by
    simpa [tm, cClear, cPayload] using
      cnfSplitFoldStepChoice_clearAcc_run
        (.input (some (some (Sum.inr (Sum.inl false))))) payloadInput [] accMapped.reverse
  have hPayload : StateTransition.EvalsToInTime tm.step cPayload (some cMove)
      (2 * payload.length + 1) := by
    simpa [tm, cPayload, cMove, payloadInput, payloadMapped,
      cnfSplitFoldStepChoiceNatPayloadInputSymbol] using
      cnfSplitFoldStepChoice_readLeftPayload_run payload (.output none) [] []
  have hMove : StateTransition.EvalsToInTime tm.step cMove (some cWrite)
      (2 * payloadMapped.reverse.length + 1) := by
    simpa [tm, cMove, cWrite, payloadMapped, List.reverse_reverse] using
      cnfSplitFoldStepChoice_moveTemp_run false (.input none) [] []
        payloadMapped.reverse
  have hWrite : StateTransition.EvalsToInTime tm.step cWrite (some done) 1 := by
    simpa [tm, cWrite, done, payloadMapped] using
      TM2Programs.evalsToInTimeOne
        (cnfSplitFoldStepChoice_writeTag_step false payloadMapped)
  have hReadTag : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some cClear) (1 + (2 * acc.length + 1)) :=
    StateTransition.EvalsToInTime.trans tm.step (2 * acc.length + 1) 1
      (Turing.initList tm input) cTag (some cClear) hRead hTag
  have hToPayload : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some cPayload)
      ((accMapped.reverse.length + 1) + (1 + (2 * acc.length + 1))) :=
    StateTransition.EvalsToInTime.trans tm.step (1 + (2 * acc.length + 1))
      (accMapped.reverse.length + 1)
      (Turing.initList tm input) cClear (some cPayload) hReadTag hClear
  have hToMove : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some cMove)
      ((2 * payload.length + 1) +
        ((accMapped.reverse.length + 1) + (1 + (2 * acc.length + 1)))) :=
    StateTransition.EvalsToInTime.trans tm.step
      ((accMapped.reverse.length + 1) + (1 + (2 * acc.length + 1)))
      (2 * payload.length + 1)
      (Turing.initList tm input) cPayload (some cMove) hToPayload hPayload
  have hToWrite : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some cWrite)
      ((2 * payloadMapped.reverse.length + 1) +
        ((2 * payload.length + 1) +
          ((accMapped.reverse.length + 1) + (1 + (2 * acc.length + 1))))) :=
    StateTransition.EvalsToInTime.trans tm.step
      ((2 * payload.length + 1) +
        ((accMapped.reverse.length + 1) + (1 + (2 * acc.length + 1))))
      (2 * payloadMapped.reverse.length + 1)
      (Turing.initList tm input) cMove (some cWrite) hToMove hMove
  have hAll : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some done)
      (1 +
        ((2 * payloadMapped.reverse.length + 1) +
          ((2 * payload.length + 1) +
            ((accMapped.reverse.length + 1) + (1 + (2 * acc.length + 1)))))) :=
    StateTransition.EvalsToInTime.trans tm.step
      ((2 * payloadMapped.reverse.length + 1) +
        ((2 * payload.length + 1) +
          ((accMapped.reverse.length + 1) + (1 + (2 * acc.length + 1)))))
      1
      (Turing.initList tm input) cWrite (some done) hToWrite hWrite
  change StateTransition.EvalsToInTime tm.step
    (Turing.initList tm input)
    (some (Turing.haltList tm (Sum.inl false :: payloadMapped)))
    (4 * input.length + 8)
  exact
    TM2Programs.evalsToInTime_mono
      (by simpa [tm, done, cnfSplitFoldStepChoice_haltList] using hAll)
      (by
        simp [input, accMapped, payloadMapped,
          cnfSplitFoldStepChoiceLeftInputStack,
          cnfSplitFoldStepChoiceInstructionTagInputSymbol]
        omega)

def cnfSplitFoldStepChoice_outputs_right
    (acc : List cnfSplitFoldAccEncodedType.Symbol)
    (payload : List clauseStructuredEncodedType.Symbol) :
    Turing.TM2OutputsInTime
      cnfSplitFoldStepChoiceMachine
      (cnfSplitFoldStepChoiceRightInputStack acc payload)
      (some (Sum.inl true ::
        (acc.map cnfSplitFoldStepChoiceAccOutputSymbol ++
          cnfSplitFoldStepChoiceRightDelimiter ::
            payload.map cnfSplitFoldStepChoiceClauseOutputSymbol)))
      (4 * (cnfSplitFoldStepChoiceRightInputStack acc payload).length + 8) := by
  let tm := cnfSplitFoldStepChoiceMachine
  let accMapped := acc.map cnfSplitFoldStepChoiceAccOutputSymbol
  let payloadInput := payload.map cnfSplitFoldStepChoiceClausePayloadInputSymbol
  let payloadMapped := payload.map cnfSplitFoldStepChoiceClauseOutputSymbol
  let rest : List cnfSplitFoldStepChoiceInputSymbol :=
    cnfSplitFoldStepChoiceInstructionTagInputSymbol true :: payloadInput
  let input := cnfSplitFoldStepChoiceRightInputStack acc payload
  let cTag := cnfSplitFoldStepChoiceCfg .readInstructionTag (.input (some none))
    rest [] accMapped.reverse
  let cDelimiter := cnfSplitFoldStepChoiceCfg .pushRightDelimiter
    (.input (some (some (Sum.inr (Sum.inl true))))) payloadInput [] accMapped.reverse
  let cPayload := cnfSplitFoldStepChoiceCfg .readRightPayload
    (.input (some (some (Sum.inr (Sum.inl true))))) payloadInput []
    (cnfSplitFoldStepChoiceRightDelimiter :: accMapped.reverse)
  let cMove := cnfSplitFoldStepChoiceCfg (.moveTemp true) (.input none) [] []
    (payloadMapped.reverse ++
      cnfSplitFoldStepChoiceRightDelimiter :: accMapped.reverse)
  let cWrite := cnfSplitFoldStepChoiceCfg (.writeTag true) (.output none)
    [] (accMapped ++ cnfSplitFoldStepChoiceRightDelimiter :: payloadMapped) []
  let done := cnfSplitFoldStepChoiceHalt
    (Sum.inl true ::
      (accMapped ++ cnfSplitFoldStepChoiceRightDelimiter :: payloadMapped))
  have hRead : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some cTag) (2 * acc.length + 1) := by
    simpa [tm, input, rest, cTag, accMapped,
      cnfSplitFoldStepChoiceAccInputSymbol,
      cnfSplitFoldStepChoiceInstructionTagInputSymbol,
      cnfSplitFoldStepChoiceRightInputStack,
      cnfSplitFoldStepChoice_initList] using
      cnfSplitFoldStepChoice_readAcc_run acc (.input none) rest [] []
  have hTag : StateTransition.EvalsToInTime tm.step cTag (some cDelimiter) 1 := by
    simpa [tm, cTag, cDelimiter, rest, payloadInput, accMapped,
      cnfSplitFoldStepChoiceInstructionTagInputSymbol] using
      TM2Programs.evalsToInTimeOne
        (cnfSplitFoldStepChoice_readInstructionTag_step_right
          payloadInput [] accMapped.reverse)
  have hDelimiter : StateTransition.EvalsToInTime tm.step cDelimiter (some cPayload) 1 := by
    simpa [tm, cDelimiter, cPayload] using
      TM2Programs.evalsToInTimeOne
        (cnfSplitFoldStepChoice_pushRightDelimiter_step
          (.input (some (some (Sum.inr (Sum.inl true))))) payloadInput []
          accMapped.reverse)
  have hPayload : StateTransition.EvalsToInTime tm.step cPayload (some cMove)
      (2 * payload.length + 1) := by
    simpa [tm, cPayload, cMove, payloadInput, payloadMapped,
      cnfSplitFoldStepChoiceClausePayloadInputSymbol, List.append_assoc] using
      cnfSplitFoldStepChoice_readRightPayload_run payload
        (.input (some (some (Sum.inr (Sum.inl true))))) []
        (cnfSplitFoldStepChoiceRightDelimiter :: accMapped.reverse)
  have hMove : StateTransition.EvalsToInTime tm.step cMove (some cWrite)
      (2 *
          (payloadMapped.reverse ++
            cnfSplitFoldStepChoiceRightDelimiter :: accMapped.reverse).length +
        1) := by
    simpa [tm, cMove, cWrite, payloadMapped, accMapped, List.reverse_append,
      List.reverse_reverse, List.append_assoc] using
      cnfSplitFoldStepChoice_moveTemp_run true (.input none) [] []
        (payloadMapped.reverse ++
          cnfSplitFoldStepChoiceRightDelimiter :: accMapped.reverse)
  have hWrite : StateTransition.EvalsToInTime tm.step cWrite (some done) 1 := by
    simpa [tm, cWrite, done, accMapped, payloadMapped] using
      TM2Programs.evalsToInTimeOne
        (cnfSplitFoldStepChoice_writeTag_step true
          (accMapped ++ cnfSplitFoldStepChoiceRightDelimiter :: payloadMapped))
  have hReadTag : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some cDelimiter) (1 + (2 * acc.length + 1)) :=
    StateTransition.EvalsToInTime.trans tm.step (2 * acc.length + 1) 1
      (Turing.initList tm input) cTag (some cDelimiter) hRead hTag
  have hToPayload : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some cPayload)
      (1 + (1 + (2 * acc.length + 1))) :=
    StateTransition.EvalsToInTime.trans tm.step (1 + (2 * acc.length + 1)) 1
      (Turing.initList tm input) cDelimiter (some cPayload) hReadTag hDelimiter
  have hToMove : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some cMove)
      ((2 * payload.length + 1) + (1 + (1 + (2 * acc.length + 1)))) :=
    StateTransition.EvalsToInTime.trans tm.step
      (1 + (1 + (2 * acc.length + 1))) (2 * payload.length + 1)
      (Turing.initList tm input) cPayload (some cMove) hToPayload hPayload
  have hToWrite : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some cWrite)
      ((2 *
          (payloadMapped.reverse ++
            cnfSplitFoldStepChoiceRightDelimiter :: accMapped.reverse).length + 1) +
        ((2 * payload.length + 1) + (1 + (1 + (2 * acc.length + 1))))) :=
    StateTransition.EvalsToInTime.trans tm.step
      ((2 * payload.length + 1) + (1 + (1 + (2 * acc.length + 1))))
      (2 *
          (payloadMapped.reverse ++
            cnfSplitFoldStepChoiceRightDelimiter :: accMapped.reverse).length +
        1)
      (Turing.initList tm input) cMove (some cWrite) hToMove hMove
  have hAll : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some done)
      (1 +
        ((2 *
            (payloadMapped.reverse ++
              cnfSplitFoldStepChoiceRightDelimiter :: accMapped.reverse).length + 1) +
          ((2 * payload.length + 1) + (1 + (1 + (2 * acc.length + 1)))))) :=
    StateTransition.EvalsToInTime.trans tm.step
      ((2 *
          (payloadMapped.reverse ++
            cnfSplitFoldStepChoiceRightDelimiter :: accMapped.reverse).length + 1) +
        ((2 * payload.length + 1) + (1 + (1 + (2 * acc.length + 1))))) 1
      (Turing.initList tm input) cWrite (some done) hToWrite hWrite
  change StateTransition.EvalsToInTime tm.step
    (Turing.initList tm input)
    (some (Turing.haltList tm
      (Sum.inl true ::
        (accMapped ++ cnfSplitFoldStepChoiceRightDelimiter :: payloadMapped))))
    (4 * input.length + 8)
  exact
    TM2Programs.evalsToInTime_mono
      (by simpa [tm, done, cnfSplitFoldStepChoice_haltList] using hAll)
      (by
        simp [input, accMapped, payloadMapped,
          cnfSplitFoldStepChoiceRightInputStack,
          cnfSplitFoldStepChoiceInstructionTagInputSymbol]
        omega)

theorem cnfSplitFoldStepChoice_inputSize_le
    (p : cnfSplitFoldStepInputEncodedType.Carrier) :
    cnfSplitFoldStepChoiceEncodedType.inputSize (cnfSplitFoldStepChoice p) ≤
      cnfSplitFoldStepInputEncodedType.inputSize p := by
  rcases p with ⟨acc, instr⟩
  cases instr with
  | inl next =>
      change Nat at next
      unfold EncodedType.inputSize
      rw [← cnfSplitFoldStepChoiceLeftOutput_eq_encode acc next,
        ← cnfSplitFoldStepChoiceLeftInputStack_eq_encode acc next]
      have hOutLen :
          (Sum.inl false ::
              (EncodedType.nat.encode next).map cnfSplitFoldStepChoiceNatOutputSymbol).length =
            1 + (EncodedType.nat.encode next).length := by
        simp only [List.length_cons, List.length_map]
        omega
      have hInLen :
          (cnfSplitFoldStepChoiceLeftInputStack
              (cnfSplitFoldAccEncodedType.encode acc)
              (EncodedType.nat.encode next)).length =
            (cnfSplitFoldAccEncodedType.encode acc).length +
              (1 + (1 + (EncodedType.nat.encode next).length)) := by
        simp [cnfSplitFoldStepChoiceLeftInputStack]
        omega
      calc
        (Sum.inl false ::
            (EncodedType.nat.encode next).map cnfSplitFoldStepChoiceNatOutputSymbol).length =
            1 + (EncodedType.nat.encode next).length := hOutLen
        _ ≤ (cnfSplitFoldAccEncodedType.encode acc).length +
              (1 + (1 + (EncodedType.nat.encode next).length)) := by omega
        _ = (cnfSplitFoldStepChoiceLeftInputStack
              (cnfSplitFoldAccEncodedType.encode acc)
              (EncodedType.nat.encode next)).length := hInLen.symm
  | inr c =>
      unfold EncodedType.inputSize
      rw [← cnfSplitFoldStepChoiceRightOutput_eq_encode acc c,
        ← cnfSplitFoldStepChoiceRightInputStack_eq_encode acc c]
      change
        (Sum.inl true ::
          ((cnfSplitFoldAccEncodedType.encode acc).map cnfSplitFoldStepChoiceAccOutputSymbol ++
            cnfSplitFoldStepChoiceRightDelimiter ::
              (clauseStructuredEncodedType.encode c).map
                cnfSplitFoldStepChoiceClauseOutputSymbol)).length ≤
          (cnfSplitFoldStepChoiceRightInputStack
            (cnfSplitFoldAccEncodedType.encode acc) (clauseStructuredEncodedType.encode c)).length
      have hOutLen :
          (Sum.inl true ::
            ((cnfSplitFoldAccEncodedType.encode acc).map cnfSplitFoldStepChoiceAccOutputSymbol ++
              cnfSplitFoldStepChoiceRightDelimiter ::
                (clauseStructuredEncodedType.encode c).map
                  cnfSplitFoldStepChoiceClauseOutputSymbol)).length =
            1 + ((cnfSplitFoldAccEncodedType.encode acc).length +
              (1 + (clauseStructuredEncodedType.encode c).length)) := by
        let mid :=
          (cnfSplitFoldAccEncodedType.encode acc).map cnfSplitFoldStepChoiceAccOutputSymbol ++
            cnfSplitFoldStepChoiceRightDelimiter ::
              (clauseStructuredEncodedType.encode c).map
                cnfSplitFoldStepChoiceClauseOutputSymbol
        change (Sum.inl true :: mid).length =
          1 + ((cnfSplitFoldAccEncodedType.encode acc).length +
            (1 + (clauseStructuredEncodedType.encode c).length))
        have hMid :
            mid.length =
              (cnfSplitFoldAccEncodedType.encode acc).length +
                (1 + (clauseStructuredEncodedType.encode c).length) := by
          simpa only [mid, List.length_map] using
            list_length_append_cons
              ((cnfSplitFoldAccEncodedType.encode acc).map
                cnfSplitFoldStepChoiceAccOutputSymbol)
              cnfSplitFoldStepChoiceRightDelimiter
              ((clauseStructuredEncodedType.encode c).map
                cnfSplitFoldStepChoiceClauseOutputSymbol)
        calc
          (Sum.inl true :: mid).length = mid.length + 1 := rfl
          _ = ((cnfSplitFoldAccEncodedType.encode acc).length +
              (1 + (clauseStructuredEncodedType.encode c).length)) + 1 := by
            exact congrArg (fun n => n + 1) hMid
          _ = 1 + ((cnfSplitFoldAccEncodedType.encode acc).length +
              (1 + (clauseStructuredEncodedType.encode c).length)) := by
            omega
      have hInLen :
          (cnfSplitFoldStepChoiceRightInputStack
            (cnfSplitFoldAccEncodedType.encode acc) (clauseStructuredEncodedType.encode c)).length =
            (cnfSplitFoldAccEncodedType.encode acc).length +
              (1 + (1 + (clauseStructuredEncodedType.encode c).length)) := by
        simp [cnfSplitFoldStepChoiceRightInputStack]
        omega
      calc
        (Sum.inl true ::
          ((cnfSplitFoldAccEncodedType.encode acc).map cnfSplitFoldStepChoiceAccOutputSymbol ++
            cnfSplitFoldStepChoiceRightDelimiter ::
              (clauseStructuredEncodedType.encode c).map
                cnfSplitFoldStepChoiceClauseOutputSymbol)).length =
            1 + ((cnfSplitFoldAccEncodedType.encode acc).length +
              (1 + (clauseStructuredEncodedType.encode c).length)) := hOutLen
        _ ≤ (cnfSplitFoldAccEncodedType.encode acc).length +
              (1 + (1 + (clauseStructuredEncodedType.encode c).length)) := by omega
        _ = (cnfSplitFoldStepChoiceRightInputStack
              (cnfSplitFoldAccEncodedType.encode acc) (clauseStructuredEncodedType.encode c)).length :=
            hInLen.symm

noncomputable def cnfSplitFoldStepChoiceTMBackedMap :
    TMBackedCostedMap
      cnfSplitFoldStepInputEncodedType
      cnfSplitFoldStepChoiceEncodedType
      cnfSplitFoldStepChoice where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := cnfSplitFoldStepInputEncodedType)
      (Y := cnfSplitFoldStepChoiceEncodedType)
      (LinearSizeBound.of_le (by
        intro p
        exact cnfSplitFoldStepChoice_inputSize_le p))
  tm_polytime :=
    ⟨{ tm := cnfSplitFoldStepChoiceMachine
       inputAlphabet := Equiv.refl _
       outputAlphabet := Equiv.refl _
       time := 4 * Polynomial.X + 8
       outputsFun := by
        intro p
        rcases p with ⟨acc, instr⟩
        cases instr with
        | inl next =>
            change Nat at next
            change Turing.TM2OutputsInTime
              cnfSplitFoldStepChoiceMachine
              (List.map id (cnfSplitFoldStepInputEncodedType.encode (acc, Sum.inl next)))
              (some (List.map id
                (cnfSplitFoldStepChoiceEncodedType.encode
                  (cnfSplitFoldStepChoice (acc, Sum.inl next)))))
              ((4 * Polynomial.X + 8).eval
                (cnfSplitFoldStepInputEncodedType.encode (acc, Sum.inl next)).length)
            have hOut :=
              cnfSplitFoldStepChoice_outputs_left
                (cnfSplitFoldAccEncodedType.encode acc)
                (EncodedType.nat.encode next)
            rw [cnfSplitFoldStepChoiceLeftInputStack_eq_encode acc next] at hOut
            simpa [List.map_id, Polynomial.eval_add, Polynomial.eval_mul,
              Polynomial.eval_X, ← cnfSplitFoldStepChoiceLeftOutput_eq_encode acc next] using hOut
        | inr c =>
            change Turing.TM2OutputsInTime
              cnfSplitFoldStepChoiceMachine
              (List.map id (cnfSplitFoldStepInputEncodedType.encode (acc, Sum.inr c)))
              (some (List.map id
                (cnfSplitFoldStepChoiceEncodedType.encode
                  (cnfSplitFoldStepChoice (acc, Sum.inr c)))))
              ((4 * Polynomial.X + 8).eval
                (cnfSplitFoldStepInputEncodedType.encode (acc, Sum.inr c)).length)
            have hOut :=
              cnfSplitFoldStepChoice_outputs_right
                (cnfSplitFoldAccEncodedType.encode acc)
                (clauseStructuredEncodedType.encode c)
            rw [cnfSplitFoldStepChoiceRightInputStack_eq_encode acc c] at hOut
            simpa [List.map_id, Polynomial.eval_add, Polynomial.eval_mul,
              Polynomial.eval_X, ← cnfSplitFoldStepChoiceRightOutput_eq_encode acc c] using hOut }⟩

end Karp21
end ComplexityReduction
