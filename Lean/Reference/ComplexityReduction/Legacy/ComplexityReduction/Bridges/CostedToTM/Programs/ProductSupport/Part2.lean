import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.ProductSupport.Part1

namespace ComplexityReduction
namespace TM2Programs
open Turing.TM2.Stmt

def pairStackCopyMap_drainLeft_run
    (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
    (mapLeft : α → β) (mapRight : α → γ)
    (state : PairStackCopyMapState β γ) (leftTarget : List β)
    (rightTarget : List γ) (leftTemp : List β) (rightTemp : List γ) :
    StateTransition.EvalsToInTime (pairStackCopyMapMachine α β γ mapLeft mapRight).step
      (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.drainLeft
        state [] leftTarget rightTarget leftTemp rightTemp)
      (some
        (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.drainRight
          PairStackCopyMapState.none [] (leftTemp.reverse ++ leftTarget) rightTarget
          [] rightTemp))
      (2 * leftTemp.length + 1) := by
  induction leftTemp generalizing state leftTarget with
  | nil =>
      simpa using
        evalsToInTimeOne
          (pairStackCopyMap_drainLeft_step_nil α β γ mapLeft mapRight state
            leftTarget rightTarget rightTemp)
  | cons b leftTemp ih =>
      let tm := pairStackCopyMapMachine α β γ mapLeft mapRight
      let c₀ := pairStackCopyMapCfg α β γ mapLeft mapRight
        PairStackCopyMapLabel.drainLeft state [] leftTarget rightTarget
        (b :: leftTemp) rightTemp
      let c₁ := pairStackCopyMapCfg α β γ mapLeft mapRight
        (PairStackCopyMapLabel.pushLeftTarget b) (PairStackCopyMapState.left b)
        [] leftTarget rightTarget leftTemp rightTemp
      let c₂ := pairStackCopyMapCfg α β γ mapLeft mapRight
        PairStackCopyMapLabel.drainLeft (PairStackCopyMapState.left b)
        [] (b :: leftTarget) rightTarget leftTemp rightTemp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (pairStackCopyMap_drainLeft_step_cons α β γ mapLeft mapRight state b
            leftTemp leftTarget rightTarget rightTemp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (pairStackCopyMap_pushLeftTarget_step α β γ mapLeft mapRight
            (PairStackCopyMapState.left b) b leftTarget rightTarget leftTemp rightTemp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some
            (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.drainRight
              PairStackCopyMapState.none [] (leftTemp.reverse ++ (b :: leftTarget))
              rightTarget [] rightTemp))
          (2 * leftTemp.length + 1) :=
        ih (PairStackCopyMapState.left b) (b :: leftTarget)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1)
          (2 * leftTemp.length + 1) c₀ c₂
          (some
            (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.drainRight
              PairStackCopyMapState.none [] (leftTemp.reverse ++ (b :: leftTarget))
              rightTarget [] rightTemp))
          h₁₂ hTail

def pairStackCopyMap_drainRight_run
    (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
    (mapLeft : α → β) (mapRight : α → γ)
    (state : PairStackCopyMapState β γ) (leftTarget : List β)
    (rightTarget : List γ) (rightTemp : List γ) :
    StateTransition.EvalsToInTime (pairStackCopyMapMachine α β γ mapLeft mapRight).step
      (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.drainRight
        state [] leftTarget rightTarget [] rightTemp)
      (some
        (pairStackCopyMapHalt α β γ mapLeft mapRight leftTarget
          (rightTemp.reverse ++ rightTarget)))
      (2 * rightTemp.length + 1) := by
  induction rightTemp generalizing state rightTarget with
  | nil =>
      simpa using
        evalsToInTimeOne
          (pairStackCopyMap_drainRight_step_nil α β γ mapLeft mapRight state
            leftTarget rightTarget)
  | cons c rightTemp ih =>
      let tm := pairStackCopyMapMachine α β γ mapLeft mapRight
      let c₀ := pairStackCopyMapCfg α β γ mapLeft mapRight
        PairStackCopyMapLabel.drainRight state [] leftTarget rightTarget [] (c :: rightTemp)
      let c₁ := pairStackCopyMapCfg α β γ mapLeft mapRight
        (PairStackCopyMapLabel.pushRightTarget c) (PairStackCopyMapState.right c)
        [] leftTarget rightTarget [] rightTemp
      let c₂ := pairStackCopyMapCfg α β γ mapLeft mapRight
        PairStackCopyMapLabel.drainRight (PairStackCopyMapState.right c)
        [] leftTarget (c :: rightTarget) [] rightTemp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (pairStackCopyMap_drainRight_step_cons α β γ mapLeft mapRight state c
            leftTarget rightTarget rightTemp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (pairStackCopyMap_pushRightTarget_step α β γ mapLeft mapRight
            (PairStackCopyMapState.right c) c leftTarget rightTarget rightTemp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some
            (pairStackCopyMapHalt α β γ mapLeft mapRight leftTarget
              (rightTemp.reverse ++ (c :: rightTarget))))
          (2 * rightTemp.length + 1) :=
        ih (PairStackCopyMapState.right c) (c :: rightTarget)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1)
          (2 * rightTemp.length + 1) c₀ c₂
          (some
            (pairStackCopyMapHalt α β γ mapLeft mapRight leftTarget
              (rightTemp.reverse ++ (c :: rightTarget))))
          h₁₂ hTail

def pairStackCopyMap_run
    (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
    (mapLeft : α → β) (mapRight : α → γ)
    (source : List α) (leftTarget : List β) (rightTarget : List γ) :
    StateTransition.EvalsToInTime (pairStackCopyMapMachine α β γ mapLeft mapRight).step
      (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.readSource
        PairStackCopyMapState.none source leftTarget rightTarget [] [])
      (some
        (pairStackCopyMapHalt α β γ mapLeft mapRight
          (source.map mapLeft ++ leftTarget) (source.map mapRight ++ rightTarget)))
      (7 * source.length + 3) := by
  let tm := pairStackCopyMapMachine α β γ mapLeft mapRight
  let leftMid := (source.map mapLeft).reverse
  let rightMid := (source.map mapRight).reverse
  let c₁ := pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.drainLeft
    PairStackCopyMapState.none [] leftTarget rightTarget leftMid rightMid
  let c₂ := pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.drainRight
    PairStackCopyMapState.none [] (leftMid.reverse ++ leftTarget) rightTarget [] rightMid
  have hFill : StateTransition.EvalsToInTime tm.step
      (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.readSource
        PairStackCopyMapState.none source leftTarget rightTarget [] [])
      (some c₁) (3 * source.length + 1) := by
    simpa [tm, c₁, leftMid, rightMid] using
      pairStackCopyMap_fillTemps_run α β γ mapLeft mapRight PairStackCopyMapState.none
        source leftTarget rightTarget [] []
  have hLeft : StateTransition.EvalsToInTime tm.step c₁ (some c₂)
      (2 * leftMid.length + 1) := by
    simpa [tm, c₁, c₂, leftMid, rightMid] using
      pairStackCopyMap_drainLeft_run α β γ mapLeft mapRight PairStackCopyMapState.none
        leftTarget rightTarget leftMid rightMid
  have hRight : StateTransition.EvalsToInTime tm.step c₂
      (some
        (pairStackCopyMapHalt α β γ mapLeft mapRight
          (leftMid.reverse ++ leftTarget) (rightMid.reverse ++ rightTarget)))
      (2 * rightMid.length + 1) := by
    simpa [tm, c₂, leftMid, rightMid] using
      pairStackCopyMap_drainRight_run α β γ mapLeft mapRight PairStackCopyMapState.none
        (leftMid.reverse ++ leftTarget) rightTarget rightMid
  have hFillLeft : StateTransition.EvalsToInTime tm.step
      (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.readSource
        PairStackCopyMapState.none source leftTarget rightTarget [] [])
      (some c₂) ((2 * leftMid.length + 1) + (3 * source.length + 1)) :=
    StateTransition.EvalsToInTime.trans tm.step (3 * source.length + 1)
      (2 * leftMid.length + 1)
      (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.readSource
        PairStackCopyMapState.none source leftTarget rightTarget [] [])
      c₁ (some c₂) hFill hLeft
  have hAll : StateTransition.EvalsToInTime tm.step
      (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.readSource
        PairStackCopyMapState.none source leftTarget rightTarget [] [])
      (some
        (pairStackCopyMapHalt α β γ mapLeft mapRight
          (leftMid.reverse ++ leftTarget) (rightMid.reverse ++ rightTarget)))
      ((2 * rightMid.length + 1) + ((2 * leftMid.length + 1) +
        (3 * source.length + 1))) :=
    StateTransition.EvalsToInTime.trans tm.step
      ((2 * leftMid.length + 1) + (3 * source.length + 1))
      (2 * rightMid.length + 1)
      (pairStackCopyMapCfg α β γ mapLeft mapRight PairStackCopyMapLabel.readSource
        PairStackCopyMapState.none source leftTarget rightTarget [] [])
      c₂
      (some
        (pairStackCopyMapHalt α β γ mapLeft mapRight
          (leftMid.reverse ++ leftTarget) (rightMid.reverse ++ rightTarget)))
      hFillLeft hRight
  refine
    { steps := hAll.steps
      evals_in_steps := by
        simpa [tm, c₁, c₂, leftMid, rightMid] using hAll.evals_in_steps
      steps_le_m := ?_ }
  have hSteps := hAll.steps_le_m
  simp [leftMid, rightMid, List.length_reverse] at hSteps
  omega

/-- Stack indices for writing two source stacks into one delimited product output. -/
inductive PairOutputWriteStack where
  | leftSource
  | rightSource
  | output
  | temp
  deriving DecidableEq, Fintype

/-- Alphabets for the product-output writer. -/
abbrev pairOutputWriteAlphabet (α β δ : Type) : PairOutputWriteStack → Type
  | PairOutputWriteStack.leftSource => α
  | PairOutputWriteStack.rightSource => β
  | PairOutputWriteStack.output => δ
  | PairOutputWriteStack.temp => δ

/-- Control labels for the product-output writer. -/
inductive PairOutputWriteLabel (δ : Type) where
  | readRight
  | pushRightTemp (d : δ)
  | drainRight
  | pushRightOutput (d : δ)
  | writeDelimiter
  | readLeft
  | pushLeftTemp (d : δ)
  | drainLeft
  | pushLeftOutput (d : δ)
  deriving DecidableEq, Fintype

/--
Write two source stacks into one output stack as
`left.map mapLeft ++ [delimiter] ++ right.map mapRight ++ output`.
-/
def pairOutputWriteMachine (α β δ : Type) [Fintype α] [Fintype β] [Fintype δ]
    (mapLeft : α → δ) (mapRight : β → δ) (delimiter : δ) : Turing.FinTM2 where
  K := PairOutputWriteStack
  k₀ := PairOutputWriteStack.leftSource
  k₁ := PairOutputWriteStack.output
  Γ := pairOutputWriteAlphabet α β δ
  Λ := PairOutputWriteLabel δ
  main := PairOutputWriteLabel.readRight
  σ := Option δ
  initialState := none
  Γk₀Fin := by
    dsimp [pairOutputWriteAlphabet]
    infer_instance
  m
    | PairOutputWriteLabel.readRight =>
        pop PairOutputWriteStack.rightSource (fun _ head => head.map mapRight)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some d => PairOutputWriteLabel.pushRightTemp d
              | none => PairOutputWriteLabel.drainRight)
            (goto fun _ => PairOutputWriteLabel.drainRight))
    | PairOutputWriteLabel.pushRightTemp d =>
        push PairOutputWriteStack.temp (fun _ => d)
          (goto fun _ => PairOutputWriteLabel.readRight)
    | PairOutputWriteLabel.drainRight =>
        pop PairOutputWriteStack.temp (fun _ head => head)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some d => PairOutputWriteLabel.pushRightOutput d
              | none => PairOutputWriteLabel.writeDelimiter)
            (goto fun _ => PairOutputWriteLabel.writeDelimiter))
    | PairOutputWriteLabel.pushRightOutput d =>
        push PairOutputWriteStack.output (fun _ => d)
          (goto fun _ => PairOutputWriteLabel.drainRight)
    | PairOutputWriteLabel.writeDelimiter =>
        push PairOutputWriteStack.output (fun _ => delimiter)
          (goto fun _ => PairOutputWriteLabel.readLeft)
    | PairOutputWriteLabel.readLeft =>
        pop PairOutputWriteStack.leftSource (fun _ head => head.map mapLeft)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some d => PairOutputWriteLabel.pushLeftTemp d
              | none => PairOutputWriteLabel.drainLeft)
            (goto fun _ => PairOutputWriteLabel.drainLeft))
    | PairOutputWriteLabel.pushLeftTemp d =>
        push PairOutputWriteStack.temp (fun _ => d)
          (goto fun _ => PairOutputWriteLabel.readLeft)
    | PairOutputWriteLabel.drainLeft =>
        pop PairOutputWriteStack.temp (fun _ head => head)
          (branch Option.isSome
            (goto fun state =>
              match state with
              | some d => PairOutputWriteLabel.pushLeftOutput d
              | none => PairOutputWriteLabel.drainLeft)
            (load (fun _ => none) halt))
    | PairOutputWriteLabel.pushLeftOutput d =>
        push PairOutputWriteStack.output (fun _ => d)
          (goto fun _ => PairOutputWriteLabel.drainLeft)

def pairOutputWriteCfg (α β δ : Type) [Fintype α] [Fintype β] [Fintype δ]
    (mapLeft : α → δ) (mapRight : β → δ) (delimiter : δ)
    (label : PairOutputWriteLabel δ) (state : Option δ)
    (leftSource : List α) (rightSource : List β) (output temp : List δ) :
    (pairOutputWriteMachine α β δ mapLeft mapRight delimiter).Cfg where
  l := some label
  var := state
  stk
    | PairOutputWriteStack.leftSource => leftSource
    | PairOutputWriteStack.rightSource => rightSource
    | PairOutputWriteStack.output => output
    | PairOutputWriteStack.temp => temp

def pairOutputWriteHalt (α β δ : Type) [Fintype α] [Fintype β] [Fintype δ]
    (mapLeft : α → δ) (mapRight : β → δ) (delimiter : δ) (output : List δ) :
    (pairOutputWriteMachine α β δ mapLeft mapRight delimiter).Cfg where
  l := none
  var := none
  stk
    | PairOutputWriteStack.leftSource => []
    | PairOutputWriteStack.rightSource => []
    | PairOutputWriteStack.output => output
    | PairOutputWriteStack.temp => []

lemma pairOutputWrite_readRight_step_cons
    (α β δ : Type) [Fintype α] [Fintype β] [Fintype δ]
    (mapLeft : α → δ) (mapRight : β → δ) (delimiter : δ)
    (state : Option δ) (leftSource : List α) (b : β) (rightSource : List β)
    (output temp : List δ) :
    (pairOutputWriteMachine α β δ mapLeft mapRight delimiter).step
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.readRight
          state leftSource (b :: rightSource) output temp) =
      some
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter
          (PairOutputWriteLabel.pushRightTemp (mapRight b)) (some (mapRight b))
          leftSource rightSource output temp) := by
  simp [pairOutputWriteMachine, pairOutputWriteCfg]
  congr
  funext k
  cases k <;> rfl

lemma pairOutputWrite_readRight_step_nil
    (α β δ : Type) [Fintype α] [Fintype β] [Fintype δ]
    (mapLeft : α → δ) (mapRight : β → δ) (delimiter : δ)
    (state : Option δ) (leftSource : List α) (output temp : List δ) :
    (pairOutputWriteMachine α β δ mapLeft mapRight delimiter).step
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.readRight
          state leftSource [] output temp) =
      some
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.drainRight
          none leftSource [] output temp) := by
  simp [pairOutputWriteMachine, pairOutputWriteCfg]
  congr

lemma pairOutputWrite_pushRightTemp_step
    (α β δ : Type) [Fintype α] [Fintype β] [Fintype δ]
    (mapLeft : α → δ) (mapRight : β → δ) (delimiter : δ)
    (state : Option δ) (d : δ) (leftSource : List α) (rightSource : List β)
    (output temp : List δ) :
    (pairOutputWriteMachine α β δ mapLeft mapRight delimiter).step
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter
          (PairOutputWriteLabel.pushRightTemp d) state leftSource rightSource output temp) =
      some
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.readRight
          state leftSource rightSource output (d :: temp)) := by
  simp [pairOutputWriteMachine, pairOutputWriteCfg]
  congr
  funext k
  cases k <;> rfl

lemma pairOutputWrite_drainRight_step_cons
    (α β δ : Type) [Fintype α] [Fintype β] [Fintype δ]
    (mapLeft : α → δ) (mapRight : β → δ) (delimiter : δ)
    (state : Option δ) (leftSource : List α) (d : δ) (output temp : List δ) :
    (pairOutputWriteMachine α β δ mapLeft mapRight delimiter).step
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.drainRight
          state leftSource [] output (d :: temp)) =
      some
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter
          (PairOutputWriteLabel.pushRightOutput d) (some d) leftSource [] output temp) := by
  simp [pairOutputWriteMachine, pairOutputWriteCfg]
  congr
  funext k
  cases k <;> rfl

lemma pairOutputWrite_drainRight_step_nil
    (α β δ : Type) [Fintype α] [Fintype β] [Fintype δ]
    (mapLeft : α → δ) (mapRight : β → δ) (delimiter : δ)
    (state : Option δ) (leftSource : List α) (output : List δ) :
    (pairOutputWriteMachine α β δ mapLeft mapRight delimiter).step
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.drainRight
          state leftSource [] output []) =
      some
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter
          PairOutputWriteLabel.writeDelimiter none leftSource [] output []) := by
  simp [pairOutputWriteMachine, pairOutputWriteCfg]
  congr

lemma pairOutputWrite_pushRightOutput_step
    (α β δ : Type) [Fintype α] [Fintype β] [Fintype δ]
    (mapLeft : α → δ) (mapRight : β → δ) (delimiter : δ)
    (state : Option δ) (d : δ) (leftSource : List α) (output temp : List δ) :
    (pairOutputWriteMachine α β δ mapLeft mapRight delimiter).step
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter
          (PairOutputWriteLabel.pushRightOutput d) state leftSource [] output temp) =
      some
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.drainRight
          state leftSource [] (d :: output) temp) := by
  simp [pairOutputWriteMachine, pairOutputWriteCfg]
  congr
  funext k
  cases k <;> rfl

lemma pairOutputWrite_writeDelimiter_step
    (α β δ : Type) [Fintype α] [Fintype β] [Fintype δ]
    (mapLeft : α → δ) (mapRight : β → δ) (delimiter : δ)
    (state : Option δ) (leftSource : List α) (output : List δ) :
    (pairOutputWriteMachine α β δ mapLeft mapRight delimiter).step
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter
          PairOutputWriteLabel.writeDelimiter state leftSource [] output []) =
      some
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.readLeft
          state leftSource [] (delimiter :: output) []) := by
  simp [pairOutputWriteMachine, pairOutputWriteCfg]
  congr
  funext k
  cases k <;> rfl

lemma pairOutputWrite_readLeft_step_cons
    (α β δ : Type) [Fintype α] [Fintype β] [Fintype δ]
    (mapLeft : α → δ) (mapRight : β → δ) (delimiter : δ)
    (state : Option δ) (a : α) (leftSource : List α) (output temp : List δ) :
    (pairOutputWriteMachine α β δ mapLeft mapRight delimiter).step
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.readLeft
          state (a :: leftSource) [] output temp) =
      some
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter
          (PairOutputWriteLabel.pushLeftTemp (mapLeft a)) (some (mapLeft a))
          leftSource [] output temp) := by
  simp [pairOutputWriteMachine, pairOutputWriteCfg]
  congr
  funext k
  cases k <;> rfl

lemma pairOutputWrite_readLeft_step_nil
    (α β δ : Type) [Fintype α] [Fintype β] [Fintype δ]
    (mapLeft : α → δ) (mapRight : β → δ) (delimiter : δ)
    (state : Option δ) (output temp : List δ) :
    (pairOutputWriteMachine α β δ mapLeft mapRight delimiter).step
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.readLeft
          state [] [] output temp) =
      some
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.drainLeft
          none [] [] output temp) := by
  simp [pairOutputWriteMachine, pairOutputWriteCfg]
  congr

lemma pairOutputWrite_pushLeftTemp_step
    (α β δ : Type) [Fintype α] [Fintype β] [Fintype δ]
    (mapLeft : α → δ) (mapRight : β → δ) (delimiter : δ)
    (state : Option δ) (d : δ) (leftSource : List α) (output temp : List δ) :
    (pairOutputWriteMachine α β δ mapLeft mapRight delimiter).step
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter
          (PairOutputWriteLabel.pushLeftTemp d) state leftSource [] output temp) =
      some
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.readLeft
          state leftSource [] output (d :: temp)) := by
  simp [pairOutputWriteMachine, pairOutputWriteCfg]
  congr
  funext k
  cases k <;> rfl

lemma pairOutputWrite_drainLeft_step_cons
    (α β δ : Type) [Fintype α] [Fintype β] [Fintype δ]
    (mapLeft : α → δ) (mapRight : β → δ) (delimiter : δ)
    (state : Option δ) (d : δ) (output temp : List δ) :
    (pairOutputWriteMachine α β δ mapLeft mapRight delimiter).step
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.drainLeft
          state [] [] output (d :: temp)) =
      some
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter
          (PairOutputWriteLabel.pushLeftOutput d) (some d) [] [] output temp) := by
  simp [pairOutputWriteMachine, pairOutputWriteCfg]
  congr
  funext k
  cases k <;> rfl

lemma pairOutputWrite_drainLeft_step_nil
    (α β δ : Type) [Fintype α] [Fintype β] [Fintype δ]
    (mapLeft : α → δ) (mapRight : β → δ) (delimiter : δ)
    (state : Option δ) (output : List δ) :
    (pairOutputWriteMachine α β δ mapLeft mapRight delimiter).step
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.drainLeft
          state [] [] output []) =
      some (pairOutputWriteHalt α β δ mapLeft mapRight delimiter output) := by
  simp [pairOutputWriteMachine, pairOutputWriteCfg, pairOutputWriteHalt]
  congr

lemma pairOutputWrite_pushLeftOutput_step
    (α β δ : Type) [Fintype α] [Fintype β] [Fintype δ]
    (mapLeft : α → δ) (mapRight : β → δ) (delimiter : δ)
    (state : Option δ) (d : δ) (output temp : List δ) :
    (pairOutputWriteMachine α β δ mapLeft mapRight delimiter).step
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter
          (PairOutputWriteLabel.pushLeftOutput d) state [] [] output temp) =
      some
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.drainLeft
          state [] [] (d :: output) temp) := by
  simp [pairOutputWriteMachine, pairOutputWriteCfg]
  congr
  funext k
  cases k <;> rfl

def pairOutputWrite_readRight_run
    (α β δ : Type) [Fintype α] [Fintype β] [Fintype δ]
    (mapLeft : α → δ) (mapRight : β → δ) (delimiter : δ)
    (state : Option δ) (leftSource : List α) (rightSource : List β)
    (output temp : List δ) :
    StateTransition.EvalsToInTime
      (pairOutputWriteMachine α β δ mapLeft mapRight delimiter).step
      (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.readRight
        state leftSource rightSource output temp)
      (some
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.drainRight
          none leftSource [] output ((rightSource.map mapRight).reverse ++ temp)))
      (2 * rightSource.length + 1) := by
  induction rightSource generalizing state temp with
  | nil =>
      simpa using
        evalsToInTimeOne
          (pairOutputWrite_readRight_step_nil α β δ mapLeft mapRight delimiter state
            leftSource output temp)
  | cons b rightSource ih =>
      let tm := pairOutputWriteMachine α β δ mapLeft mapRight delimiter
      let c₀ := pairOutputWriteCfg α β δ mapLeft mapRight delimiter
        PairOutputWriteLabel.readRight state leftSource (b :: rightSource) output temp
      let c₁ := pairOutputWriteCfg α β δ mapLeft mapRight delimiter
        (PairOutputWriteLabel.pushRightTemp (mapRight b)) (some (mapRight b))
        leftSource rightSource output temp
      let c₂ := pairOutputWriteCfg α β δ mapLeft mapRight delimiter
        PairOutputWriteLabel.readRight (some (mapRight b)) leftSource rightSource output
        (mapRight b :: temp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (pairOutputWrite_readRight_step_cons α β δ mapLeft mapRight delimiter state
            leftSource b rightSource output temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (pairOutputWrite_pushRightTemp_step α β δ mapLeft mapRight delimiter
            (some (mapRight b)) (mapRight b) leftSource rightSource output temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some
            (pairOutputWriteCfg α β δ mapLeft mapRight delimiter
              PairOutputWriteLabel.drainRight none leftSource [] output
              ((rightSource.map mapRight).reverse ++ (mapRight b :: temp))))
          (2 * rightSource.length + 1) :=
        ih (some (mapRight b)) (mapRight b :: temp)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1)
          (2 * rightSource.length + 1) c₀ c₂
          (some
            (pairOutputWriteCfg α β δ mapLeft mapRight delimiter
              PairOutputWriteLabel.drainRight none leftSource [] output
              ((rightSource.map mapRight).reverse ++ (mapRight b :: temp))))
          h₁₂ hTail

def pairOutputWrite_drainRight_run
    (α β δ : Type) [Fintype α] [Fintype β] [Fintype δ]
    (mapLeft : α → δ) (mapRight : β → δ) (delimiter : δ)
    (state : Option δ) (leftSource : List α) (output temp : List δ) :
    StateTransition.EvalsToInTime
      (pairOutputWriteMachine α β δ mapLeft mapRight delimiter).step
      (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.drainRight
        state leftSource [] output temp)
      (some
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter
          PairOutputWriteLabel.writeDelimiter none leftSource [] (temp.reverse ++ output) []))
      (2 * temp.length + 1) := by
  induction temp generalizing state output with
  | nil =>
      simpa using
        evalsToInTimeOne
          (pairOutputWrite_drainRight_step_nil α β δ mapLeft mapRight delimiter state
            leftSource output)
  | cons d temp ih =>
      let tm := pairOutputWriteMachine α β δ mapLeft mapRight delimiter
      let c₀ := pairOutputWriteCfg α β δ mapLeft mapRight delimiter
        PairOutputWriteLabel.drainRight state leftSource [] output (d :: temp)
      let c₁ := pairOutputWriteCfg α β δ mapLeft mapRight delimiter
        (PairOutputWriteLabel.pushRightOutput d) (some d) leftSource [] output temp
      let c₂ := pairOutputWriteCfg α β δ mapLeft mapRight delimiter
        PairOutputWriteLabel.drainRight (some d) leftSource [] (d :: output) temp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (pairOutputWrite_drainRight_step_cons α β δ mapLeft mapRight delimiter state
            leftSource d output temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (pairOutputWrite_pushRightOutput_step α β δ mapLeft mapRight delimiter
            (some d) d leftSource output temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some
            (pairOutputWriteCfg α β δ mapLeft mapRight delimiter
              PairOutputWriteLabel.writeDelimiter none leftSource []
              (temp.reverse ++ (d :: output)) []))
          (2 * temp.length + 1) :=
        ih (some d) (d :: output)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1)
          (2 * temp.length + 1) c₀ c₂
          (some
            (pairOutputWriteCfg α β δ mapLeft mapRight delimiter
              PairOutputWriteLabel.writeDelimiter none leftSource []
              (temp.reverse ++ (d :: output)) []))
          h₁₂ hTail

def pairOutputWrite_writeDelimiter_run
    (α β δ : Type) [Fintype α] [Fintype β] [Fintype δ]
    (mapLeft : α → δ) (mapRight : β → δ) (delimiter : δ)
    (state : Option δ) (leftSource : List α) (output : List δ) :
    StateTransition.EvalsToInTime
      (pairOutputWriteMachine α β δ mapLeft mapRight delimiter).step
      (pairOutputWriteCfg α β δ mapLeft mapRight delimiter
        PairOutputWriteLabel.writeDelimiter state leftSource [] output [])
      (some
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.readLeft
          state leftSource [] (delimiter :: output) []))
      1 :=
  evalsToInTimeOne
    (pairOutputWrite_writeDelimiter_step α β δ mapLeft mapRight delimiter state leftSource output)

def pairOutputWrite_readLeft_run
    (α β δ : Type) [Fintype α] [Fintype β] [Fintype δ]
    (mapLeft : α → δ) (mapRight : β → δ) (delimiter : δ)
    (state : Option δ) (leftSource : List α) (output temp : List δ) :
    StateTransition.EvalsToInTime
      (pairOutputWriteMachine α β δ mapLeft mapRight delimiter).step
      (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.readLeft
        state leftSource [] output temp)
      (some
        (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.drainLeft
          none [] [] output ((leftSource.map mapLeft).reverse ++ temp)))
      (2 * leftSource.length + 1) := by
  induction leftSource generalizing state temp with
  | nil =>
      simpa using
        evalsToInTimeOne
          (pairOutputWrite_readLeft_step_nil α β δ mapLeft mapRight delimiter state
            output temp)
  | cons a leftSource ih =>
      let tm := pairOutputWriteMachine α β δ mapLeft mapRight delimiter
      let c₀ := pairOutputWriteCfg α β δ mapLeft mapRight delimiter
        PairOutputWriteLabel.readLeft state (a :: leftSource) [] output temp
      let c₁ := pairOutputWriteCfg α β δ mapLeft mapRight delimiter
        (PairOutputWriteLabel.pushLeftTemp (mapLeft a)) (some (mapLeft a))
        leftSource [] output temp
      let c₂ := pairOutputWriteCfg α β δ mapLeft mapRight delimiter
        PairOutputWriteLabel.readLeft (some (mapLeft a)) leftSource [] output
        (mapLeft a :: temp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (pairOutputWrite_readLeft_step_cons α β δ mapLeft mapRight delimiter state
            a leftSource output temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (pairOutputWrite_pushLeftTemp_step α β δ mapLeft mapRight delimiter
            (some (mapLeft a)) (mapLeft a) leftSource output temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some
            (pairOutputWriteCfg α β δ mapLeft mapRight delimiter
              PairOutputWriteLabel.drainLeft none [] [] output
              ((leftSource.map mapLeft).reverse ++ (mapLeft a :: temp))))
          (2 * leftSource.length + 1) :=
        ih (some (mapLeft a)) (mapLeft a :: temp)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1)
          (2 * leftSource.length + 1) c₀ c₂
          (some
            (pairOutputWriteCfg α β δ mapLeft mapRight delimiter
              PairOutputWriteLabel.drainLeft none [] [] output
              ((leftSource.map mapLeft).reverse ++ (mapLeft a :: temp))))
          h₁₂ hTail

def pairOutputWrite_drainLeft_run
    (α β δ : Type) [Fintype α] [Fintype β] [Fintype δ]
    (mapLeft : α → δ) (mapRight : β → δ) (delimiter : δ)
    (state : Option δ) (output temp : List δ) :
    StateTransition.EvalsToInTime
      (pairOutputWriteMachine α β δ mapLeft mapRight delimiter).step
      (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.drainLeft
        state [] [] output temp)
      (some
        (pairOutputWriteHalt α β δ mapLeft mapRight delimiter (temp.reverse ++ output)))
      (2 * temp.length + 1) := by
  induction temp generalizing state output with
  | nil =>
      simpa using
        evalsToInTimeOne
          (pairOutputWrite_drainLeft_step_nil α β δ mapLeft mapRight delimiter state output)
  | cons d temp ih =>
      let tm := pairOutputWriteMachine α β δ mapLeft mapRight delimiter
      let c₀ := pairOutputWriteCfg α β δ mapLeft mapRight delimiter
        PairOutputWriteLabel.drainLeft state [] [] output (d :: temp)
      let c₁ := pairOutputWriteCfg α β δ mapLeft mapRight delimiter
        (PairOutputWriteLabel.pushLeftOutput d) (some d) [] [] output temp
      let c₂ := pairOutputWriteCfg α β δ mapLeft mapRight delimiter
        PairOutputWriteLabel.drainLeft (some d) [] [] (d :: output) temp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (pairOutputWrite_drainLeft_step_cons α β δ mapLeft mapRight delimiter state
            d output temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (pairOutputWrite_pushLeftOutput_step α β δ mapLeft mapRight delimiter
            (some d) d output temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some
            (pairOutputWriteHalt α β δ mapLeft mapRight delimiter
              (temp.reverse ++ (d :: output))))
          (2 * temp.length + 1) :=
        ih (some d) (d :: output)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1)
          (2 * temp.length + 1) c₀ c₂
          (some
            (pairOutputWriteHalt α β δ mapLeft mapRight delimiter
              (temp.reverse ++ (d :: output))))
          h₁₂ hTail

def pairOutputWrite_run
    (α β δ : Type) [Fintype α] [Fintype β] [Fintype δ]
    (mapLeft : α → δ) (mapRight : β → δ) (delimiter : δ)
    (leftSource : List α) (rightSource : List β) (output : List δ) :
    StateTransition.EvalsToInTime
      (pairOutputWriteMachine α β δ mapLeft mapRight delimiter).step
      (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.readRight
        none leftSource rightSource output [])
      (some
        (pairOutputWriteHalt α β δ mapLeft mapRight delimiter
          (leftSource.map mapLeft ++ delimiter :: rightSource.map mapRight ++ output)))
      (4 * leftSource.length + 4 * rightSource.length + 5) := by
  let tm := pairOutputWriteMachine α β δ mapLeft mapRight delimiter
  let rightOut := rightSource.map mapRight
  let afterRight := pairOutputWriteCfg α β δ mapLeft mapRight delimiter
    PairOutputWriteLabel.drainRight none leftSource [] output rightOut.reverse
  let afterRightDone := pairOutputWriteCfg α β δ mapLeft mapRight delimiter
    PairOutputWriteLabel.writeDelimiter none leftSource [] (rightOut.reverse.reverse ++ output) []
  let afterDelim := pairOutputWriteCfg α β δ mapLeft mapRight delimiter
    PairOutputWriteLabel.readLeft none leftSource []
    (delimiter :: rightOut.reverse.reverse ++ output) []
  let leftOut := leftSource.map mapLeft
  let afterLeft := pairOutputWriteCfg α β δ mapLeft mapRight delimiter
    PairOutputWriteLabel.drainLeft none [] []
    (delimiter :: rightOut.reverse.reverse ++ output) leftOut.reverse
  have hReadRight : StateTransition.EvalsToInTime tm.step
      (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.readRight
        none leftSource rightSource output [])
      (some afterRight) (2 * rightSource.length + 1) := by
    simpa [tm, afterRight, rightOut] using
      pairOutputWrite_readRight_run α β δ mapLeft mapRight delimiter none
        leftSource rightSource output []
  have hDrainRight : StateTransition.EvalsToInTime tm.step afterRight
      (some afterRightDone) (2 * rightOut.reverse.length + 1) := by
    simpa [tm, afterRight, afterRightDone, rightOut] using
      pairOutputWrite_drainRight_run α β δ mapLeft mapRight delimiter none
        leftSource output rightOut.reverse
  have hRight : StateTransition.EvalsToInTime tm.step
      (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.readRight
        none leftSource rightSource output [])
      (some afterRightDone) ((2 * rightOut.reverse.length + 1) +
        (2 * rightSource.length + 1)) :=
    StateTransition.EvalsToInTime.trans tm.step (2 * rightSource.length + 1)
      (2 * rightOut.reverse.length + 1)
      (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.readRight
        none leftSource rightSource output [])
      afterRight (some afterRightDone) hReadRight hDrainRight
  have hDelim : StateTransition.EvalsToInTime tm.step afterRightDone (some afterDelim) 1 := by
    simpa [tm, afterRightDone, afterDelim, rightOut] using
      pairOutputWrite_writeDelimiter_run α β δ mapLeft mapRight delimiter none leftSource
        (rightOut.reverse.reverse ++ output)
  have hRightDelim : StateTransition.EvalsToInTime tm.step
      (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.readRight
        none leftSource rightSource output [])
      (some afterDelim) (1 + ((2 * rightOut.reverse.length + 1) +
        (2 * rightSource.length + 1))) :=
    StateTransition.EvalsToInTime.trans tm.step
      ((2 * rightOut.reverse.length + 1) + (2 * rightSource.length + 1)) 1
      (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.readRight
        none leftSource rightSource output [])
      afterRightDone (some afterDelim) hRight hDelim
  have hReadLeft : StateTransition.EvalsToInTime tm.step afterDelim
      (some afterLeft) (2 * leftSource.length + 1) := by
    simpa [tm, afterDelim, afterLeft, leftOut, rightOut] using
      pairOutputWrite_readLeft_run α β δ mapLeft mapRight delimiter none leftSource
        (delimiter :: rightOut.reverse.reverse ++ output) []
  let done := pairOutputWriteHalt α β δ mapLeft mapRight delimiter
    (leftOut.reverse.reverse ++ delimiter :: rightOut.reverse.reverse ++ output)
  have hDrainLeft : StateTransition.EvalsToInTime tm.step afterLeft (some done)
      (2 * leftOut.reverse.length + 1) := by
    simpa [tm, afterLeft, done, leftOut, rightOut] using
      pairOutputWrite_drainLeft_run α β δ mapLeft mapRight delimiter none
        (delimiter :: rightOut.reverse.reverse ++ output) leftOut.reverse
  have hLeft : StateTransition.EvalsToInTime tm.step afterDelim (some done)
      ((2 * leftOut.reverse.length + 1) + (2 * leftSource.length + 1)) :=
    StateTransition.EvalsToInTime.trans tm.step (2 * leftSource.length + 1)
      (2 * leftOut.reverse.length + 1) afterDelim afterLeft (some done)
      hReadLeft hDrainLeft
  have hAll : StateTransition.EvalsToInTime tm.step
      (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.readRight
        none leftSource rightSource output [])
      (some done)
      (((2 * leftOut.reverse.length + 1) + (2 * leftSource.length + 1)) +
        (1 + ((2 * rightOut.reverse.length + 1) + (2 * rightSource.length + 1)))) :=
    StateTransition.EvalsToInTime.trans tm.step
      (1 + ((2 * rightOut.reverse.length + 1) + (2 * rightSource.length + 1)))
      ((2 * leftOut.reverse.length + 1) + (2 * leftSource.length + 1))
      (pairOutputWriteCfg α β δ mapLeft mapRight delimiter PairOutputWriteLabel.readRight
        none leftSource rightSource output [])
      afterDelim (some done) hRightDelim hLeft
  refine
    { steps := hAll.steps
      evals_in_steps := by
        simpa [tm, done, leftOut, rightOut, List.append_assoc] using hAll.evals_in_steps
      steps_le_m := ?_ }
  have hSteps := hAll.steps_le_m
  simp [leftOut, rightOut, List.length_reverse] at hSteps
  omega

end TM2Programs
end ComplexityReduction
