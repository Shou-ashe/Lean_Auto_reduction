import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.ListMap.Part1

namespace ComplexityReduction
namespace TM2Programs
open Turing.TM2.Stmt

lemma listMap_readSource_step_nil (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (state : ListMapState tm.σ (tm.Γ tm.k₀) β)
    (work : (k : tm.K) → List (tm.Γ k))
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀)) :
    (listMapMachine α β tm readInput writeOutput).step
        (listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource) state
          [] work acc output blockTemp) =
      some (listMapCfg α β tm readInput writeOutput (some ListMapLabel.finalDrain)
        (ListMapState.final none) [] work acc output blockTemp) := by
  simp [listMapMachine, listMapCfg, listMapCopyState, ListMapCopyState.isPayload,
    ListMapCopyState.isDelimiter]

lemma listMap_pushBlockTemp_step (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (state : ListMapState tm.σ (tm.Γ tm.k₀) β)
    (a : tm.Γ tm.k₀) (source : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀)) :
    (listMapMachine α β tm readInput writeOutput).step
        (listMapCfg α β tm readInput writeOutput (some (ListMapLabel.pushBlockTemp a))
          state source work acc output blockTemp) =
      some (listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
        state source work acc output (a :: blockTemp)) := by
  simp [listMapMachine, listMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma listMap_drainBlockTemp_step_cons (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (state : ListMapState tm.σ (tm.Γ tm.k₀) β)
    (a : tm.Γ tm.k₀) (source : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀)) :
    (listMapMachine α β tm readInput writeOutput).step
        (listMapCfg α β tm readInput writeOutput (some ListMapLabel.drainBlockTemp)
          state source work acc output (a :: blockTemp)) =
      some (listMapCfg α β tm readInput writeOutput (some (ListMapLabel.pushWorkInput a))
        (ListMapState.copy (ListMapCopyState.payload a))
        source work acc output blockTemp) := by
  simp [listMapMachine, listMapCfg, listMapCopyState, ListMapCopyState.isPayload]
  congr
  funext k
  cases k <;> rfl

lemma listMap_drainBlockTemp_step_nil (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (state : ListMapState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (acc output : List (Option β)) :
    (listMapMachine α β tm readInput writeOutput).step
        (listMapCfg α β tm readInput writeOutput (some ListMapLabel.drainBlockTemp)
          state source work acc output []) =
      some (listMapCfg α β tm readInput writeOutput (some (ListMapLabel.run tm.main))
        (ListMapState.run tm.initialState) source work acc output []) := by
  simp [listMapMachine, listMapCfg, listMapCopyState, ListMapCopyState.isPayload]

lemma listMap_pushWorkInput_step (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (state : ListMapState tm.σ (tm.Γ tm.k₀) β)
    (a : tm.Γ tm.k₀) (source : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀)) :
    (listMapMachine α β tm readInput writeOutput).step
        (listMapCfg α β tm readInput writeOutput (some (ListMapLabel.pushWorkInput a))
          state source work acc output blockTemp) =
      some (listMapCfg α β tm readInput writeOutput (some ListMapLabel.drainBlockTemp)
        state source (Function.update work tm.k₀ (a :: work tm.k₀)) acc output blockTemp) := by
  simp [listMapMachine, listMapCfg]
  congr
  funext stack
  cases stack with
  | source => rfl
  | work k =>
      by_cases hk : k = tm.k₀
      · subst k
        simp [Function.update]
      · simp [Function.update, hk]
  | acc => rfl
  | output => rfl
  | blockTemp => rfl

lemma listMap_writeOutput_step_cons (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (state : ListMapState tm.σ (tm.Γ tm.k₀) β)
    (b : tm.Γ tm.k₁) (source : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀)) :
    (listMapMachine α β tm readInput writeOutput).step
        (listMapCfg α β tm readInput writeOutput (some ListMapLabel.writeOutput)
          state source (Function.update work tm.k₁ (b :: work tm.k₁)) acc output blockTemp) =
      some (listMapCfg α β tm readInput writeOutput
        (some (ListMapLabel.pushAccPayload (writeOutput b)))
        (ListMapState.write (some (writeOutput b)))
        source (Function.update work tm.k₁ (work tm.k₁)) acc output blockTemp) := by
  simp [listMapMachine, listMapCfg, listMapWriteState]
  congr
  funext stack
  cases stack with
  | source => rfl
  | work k =>
      by_cases hk : k = tm.k₁
      · subst k
        simp [Function.update]
      · simp [Function.update, hk]
  | acc => rfl
  | output => rfl
  | blockTemp => rfl

lemma listMap_writeOutput_step_nil (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (state : ListMapState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀))
    (hEmpty : work tm.k₁ = []) :
    (listMapMachine α β tm readInput writeOutput).step
        (listMapCfg α β tm readInput writeOutput (some ListMapLabel.writeOutput)
          state source work acc output blockTemp) =
      some (listMapCfg α β tm readInput writeOutput (some ListMapLabel.pushAccDelimiter)
        (ListMapState.write none) source work acc output blockTemp) := by
  simp [listMapMachine, listMapCfg, listMapWriteState, hEmpty]
  congr
  funext stack
  cases stack with
  | source => rfl
  | work k =>
      by_cases hk : k = tm.k₁
      · subst k
        simp [Function.update, hEmpty]
      · simp [Function.update, hk]
  | acc => rfl
  | output => rfl
  | blockTemp => rfl

lemma listMap_pushAccPayload_step (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (state : ListMapState tm.σ (tm.Γ tm.k₀) β)
    (b : β) (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀)) :
    (listMapMachine α β tm readInput writeOutput).step
        (listMapCfg α β tm readInput writeOutput (some (ListMapLabel.pushAccPayload b))
          state source work acc output blockTemp) =
      some (listMapCfg α β tm readInput writeOutput (some ListMapLabel.writeOutput)
        state source work (some b :: acc) output blockTemp) := by
  simp [listMapMachine, listMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma listMap_pushAccDelimiter_step (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (state : ListMapState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀)) :
    (listMapMachine α β tm readInput writeOutput).step
        (listMapCfg α β tm readInput writeOutput (some ListMapLabel.pushAccDelimiter)
          state source work acc output blockTemp) =
      some (listMapCfg α β tm readInput writeOutput
        (some (ListMapLabel.reset (listMapAllWorkStacks tm)))
        state source work (none :: acc) output blockTemp) := by
  simp [listMapMachine, listMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma listMap_finalDrain_step_cons (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (state : ListMapState tm.σ (tm.Γ tm.k₀) β)
    (b : Option β) (source : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀)) :
    (listMapMachine α β tm readInput writeOutput).step
        (listMapCfg α β tm readInput writeOutput (some ListMapLabel.finalDrain)
          state source work (b :: acc) output blockTemp) =
      some (listMapCfg α β tm readInput writeOutput (some (ListMapLabel.pushFinal b))
        (ListMapState.final (some b)) source work acc output blockTemp) := by
  simp [listMapMachine, listMapCfg, listMapFinalState]
  congr
  funext k
  cases k <;> rfl

lemma listMap_pushFinal_step (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (state : ListMapState tm.σ (tm.Γ tm.k₀) β)
    (b : Option β) (source : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀)) :
    (listMapMachine α β tm readInput writeOutput).step
        (listMapCfg α β tm readInput writeOutput (some (ListMapLabel.pushFinal b))
          state source work acc output blockTemp) =
      some (listMapCfg α β tm readInput writeOutput (some ListMapLabel.finalDrain)
        state source work acc (b :: output) blockTemp) := by
  simp [listMapMachine, listMapCfg]
  congr
  funext k
  cases k <;> rfl

lemma listMap_finalDrain_step_nil (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (state : ListMapState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀)) :
    (listMapMachine α β tm readInput writeOutput).step
        (listMapCfg α β tm readInput writeOutput (some ListMapLabel.finalDrain)
          state source work [] output blockTemp) =
      some (listMapCfg α β tm readInput writeOutput none
        (ListMapState.copy ListMapCopyState.endInput)
        source work [] output blockTemp) := by
  simp [listMapMachine, listMapCfg, listMapFinalState]

noncomputable def listMap_finalDrain_run (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (state : ListMapState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀)) :
    StateTransition.EvalsToInTime (listMapMachine α β tm readInput writeOutput).step
      (listMapCfg α β tm readInput writeOutput (some ListMapLabel.finalDrain)
        state source work acc output blockTemp)
      (some (listMapCfg α β tm readInput writeOutput none
        (ListMapState.copy ListMapCopyState.endInput)
        source work [] (acc.reverse ++ output) blockTemp))
      (2 * acc.length + 1) := by
  induction acc generalizing state output with
  | nil =>
      exact evalsToInTimeOne
        (listMap_finalDrain_step_nil α β tm readInput writeOutput state source work output
          blockTemp)
  | cons b acc ih =>
      let c₀ := listMapCfg α β tm readInput writeOutput (some ListMapLabel.finalDrain)
        state source work (b :: acc) output blockTemp
      let c₁ := listMapCfg α β tm readInput writeOutput (some (ListMapLabel.pushFinal b))
        (ListMapState.final (some b)) source work acc output blockTemp
      let c₂ := listMapCfg α β tm readInput writeOutput (some ListMapLabel.finalDrain)
        (ListMapState.final (some b)) source work acc (b :: output) blockTemp
      have h₁ : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (listMap_finalDrain_step_cons α β tm readInput writeOutput state b source work acc
            output blockTemp)
      have h₂ : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (listMap_pushFinal_step α β tm readInput writeOutput
            (ListMapState.final (some b)) b source work acc output blockTemp)
      have h₁₂ : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans
          (listMapMachine α β tm readInput writeOutput).step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₂
          (some (listMapCfg α β tm readInput writeOutput none
            (ListMapState.copy ListMapCopyState.endInput)
            source work [] (acc.reverse ++ b :: output) blockTemp))
          (2 * acc.length + 1) :=
        ih (ListMapState.final (some b)) (b :: output)
      have hAll :=
        StateTransition.EvalsToInTime.trans
          (listMapMachine α β tm readInput writeOutput).step (1 + 1)
          (2 * acc.length + 1) c₀ c₂
          (some (listMapCfg α β tm readInput writeOutput none
            (ListMapState.copy ListMapCopyState.endInput)
            source work [] (acc.reverse ++ b :: output) blockTemp))
          h₁₂ hTail
      simpa [c₀, c₁, c₂, List.reverse_cons, List.append_assoc] using hAll

noncomputable def listMap_writeOutput_runFromState (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (state : ListMapState tm.σ (tm.Γ tm.k₀) β)
    (payload : List (tm.Γ tm.k₁)) (source : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀)) :
    StateTransition.EvalsToInTime (listMapMachine α β tm readInput writeOutput).step
      (listMapCfg α β tm readInput writeOutput (some ListMapLabel.writeOutput)
        state source (Function.update work tm.k₁ payload) acc output blockTemp)
      (some (listMapCfg α β tm readInput writeOutput
        (some (ListMapLabel.reset (listMapAllWorkStacks tm)))
        (ListMapState.write none) source (Function.update work tm.k₁ [])
        (none :: (payload.map (fun b => some (writeOutput b))).reverse ++ acc) output
        blockTemp))
      (2 * payload.length + 2) := by
  induction payload generalizing state acc with
  | nil =>
      let c₀ := listMapCfg α β tm readInput writeOutput (some ListMapLabel.writeOutput)
        state source (Function.update work tm.k₁ []) acc output blockTemp
      let c₁ := listMapCfg α β tm readInput writeOutput (some ListMapLabel.pushAccDelimiter)
        (ListMapState.write none) source (Function.update work tm.k₁ []) acc output blockTemp
      let c₂ := listMapCfg α β tm readInput writeOutput
        (some (ListMapLabel.reset (listMapAllWorkStacks tm)))
        (ListMapState.write none) source (Function.update work tm.k₁ [])
        (none :: acc) output blockTemp
      have hEmpty : (Function.update work tm.k₁ ([] : List (tm.Γ tm.k₁))) tm.k₁ = [] := by
        simp [Function.update]
      have h₁ : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (listMap_writeOutput_step_nil α β tm readInput writeOutput state source
            (Function.update work tm.k₁ []) acc output blockTemp hEmpty)
      have h₂ : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (listMap_pushAccDelimiter_step α β tm readInput writeOutput
            (ListMapState.write none) source (Function.update work tm.k₁ []) acc output
            blockTemp)
      have hAll : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans
          (listMapMachine α β tm readInput writeOutput).step 1 1 c₀ c₁ (some c₂) h₁ h₂
      simpa [c₀, c₁, c₂] using hAll
  | cons b payload ih =>
      let workTail := Function.update work tm.k₁ payload
      let c₀ := listMapCfg α β tm readInput writeOutput (some ListMapLabel.writeOutput)
        state source (Function.update work tm.k₁ (b :: payload)) acc output blockTemp
      let c₁ := listMapCfg α β tm readInput writeOutput
        (some (ListMapLabel.pushAccPayload (writeOutput b)))
        (ListMapState.write (some (writeOutput b))) source workTail acc output blockTemp
      let c₂ := listMapCfg α β tm readInput writeOutput (some ListMapLabel.writeOutput)
        (ListMapState.write (some (writeOutput b))) source workTail
        (some (writeOutput b) :: acc) output blockTemp
      have h₁ : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₀ (some c₁) 1 := by
        have hStep :=
          listMap_writeOutput_step_cons α β tm readInput writeOutput state b source
            workTail acc output blockTemp
        exact evalsToInTimeOne (by simpa [c₀, c₁, workTail, Function.update] using hStep)
      have h₂ : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (listMap_pushAccPayload_step α β tm readInput writeOutput
            (ListMapState.write (some (writeOutput b))) (writeOutput b) source workTail acc
            output blockTemp)
      have h₁₂ : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans
          (listMapMachine α β tm readInput writeOutput).step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₂
          (some (listMapCfg α β tm readInput writeOutput
            (some (ListMapLabel.reset (listMapAllWorkStacks tm)))
            (ListMapState.write none) source (Function.update work tm.k₁ [])
            (none :: (payload.map (fun b => some (writeOutput b))).reverse ++
              some (writeOutput b) :: acc)
            output blockTemp))
          (2 * payload.length + 2) := by
        simpa [c₂, workTail] using
          ih (ListMapState.write (some (writeOutput b))) (some (writeOutput b) :: acc)
      have hAll :=
        StateTransition.EvalsToInTime.trans
          (listMapMachine α β tm readInput writeOutput).step (1 + 1)
          (2 * payload.length + 2) c₀ c₂
          (some (listMapCfg α β tm readInput writeOutput
            (some (ListMapLabel.reset (listMapAllWorkStacks tm)))
            (ListMapState.write none) source (Function.update work tm.k₁ [])
            (none :: (payload.map (fun b => some (writeOutput b))).reverse ++
              some (writeOutput b) :: acc)
            output blockTemp))
          h₁₂ hTail
      simpa [c₀, c₁, c₂, List.map_cons, List.reverse_cons, List.append_assoc] using hAll

noncomputable def listMap_writeOutput_run (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (payload : List (tm.Γ tm.k₁)) (source : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀)) :
    StateTransition.EvalsToInTime (listMapMachine α β tm readInput writeOutput).step
      (listMapCfg α β tm readInput writeOutput (some ListMapLabel.writeOutput)
        (ListMapState.write none) source (Function.update work tm.k₁ payload) acc output
        blockTemp)
      (some (listMapCfg α β tm readInput writeOutput
        (some (ListMapLabel.reset (listMapAllWorkStacks tm)))
        (ListMapState.write none) source (Function.update work tm.k₁ [])
        (none :: (payload.map (fun b => some (writeOutput b))).reverse ++ acc) output
        blockTemp))
      (2 * payload.length + 2) :=
  listMap_writeOutput_runFromState α β tm readInput writeOutput (ListMapState.write none)
    payload source work acc output blockTemp

lemma listMap_reset_empty_step_done (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (state : ListMapState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (remaining : Finset tm.K)
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀))
    (hRemaining : remaining.toList = []) :
    (listMapMachine α β tm readInput writeOutput).step
        (listMapCfg α β tm readInput writeOutput (some (ListMapLabel.reset remaining))
          state source (listMapEmptyWork tm) acc output blockTemp) =
      some (listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
        (ListMapState.copy ListMapCopyState.endInput)
        source (listMapEmptyWork tm) acc output blockTemp) := by
  simp [listMapMachine, listMapCfg, hRemaining]

lemma listMap_reset_empty_step_cons (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (state : ListMapState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (remaining : Finset tm.K)
    (k : tm.K) (tail : List tm.K)
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀))
    (hRemaining : remaining.toList = k :: tail) :
    (listMapMachine α β tm readInput writeOutput).step
        (listMapCfg α β tm readInput writeOutput (some (ListMapLabel.reset remaining))
          state source (listMapEmptyWork tm) acc output blockTemp) =
      some (listMapCfg α β tm readInput writeOutput
        (some (ListMapLabel.reset (remaining.erase k)))
        (ListMapState.reset false) source (listMapEmptyWork tm) acc output blockTemp) := by
  simp [listMapMachine, listMapCfg, listMapResetState, listMapEmptyWork, hRemaining]

noncomputable def listMap_resetEmpty_run (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (state : ListMapState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (remaining : Finset tm.K)
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀)) :
    StateTransition.EvalsToInTime (listMapMachine α β tm readInput writeOutput).step
      (listMapCfg α β tm readInput writeOutput (some (ListMapLabel.reset remaining))
        state source (listMapEmptyWork tm) acc output blockTemp)
      (some (listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
        (ListMapState.copy ListMapCopyState.endInput)
        source (listMapEmptyWork tm) acc output blockTemp))
      (remaining.card + 1) := by
  classical
  cases hRemaining : remaining.toList with
  | nil =>
      have hEmpty : remaining = ∅ := Finset.toList_eq_nil.mp hRemaining
      have hStep : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step
          (listMapCfg α β tm readInput writeOutput (some (ListMapLabel.reset remaining))
            state source (listMapEmptyWork tm) acc output blockTemp)
          (some (listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
            (ListMapState.copy ListMapCopyState.endInput)
            source (listMapEmptyWork tm) acc output blockTemp))
          1 :=
        evalsToInTimeOne
          (listMap_reset_empty_step_done α β tm readInput writeOutput state source remaining acc
            output blockTemp hRemaining)
      simpa [hEmpty] using hStep
  | cons k tail =>
      have hMemList : k ∈ remaining.toList := by
        simp [hRemaining]
      have hMem : k ∈ remaining := by
        simpa [Finset.mem_toList] using hMemList
      let c₀ := listMapCfg α β tm readInput writeOutput (some (ListMapLabel.reset remaining))
        state source (listMapEmptyWork tm) acc output blockTemp
      let c₁ := listMapCfg α β tm readInput writeOutput
        (some (ListMapLabel.reset (remaining.erase k)))
        (ListMapState.reset false) source (listMapEmptyWork tm) acc output blockTemp
      let c₂ := listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
        (ListMapState.copy ListMapCopyState.endInput)
        source (listMapEmptyWork tm) acc output blockTemp
      have h₁ : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (listMap_reset_empty_step_cons α β tm readInput writeOutput state source remaining k
            tail acc output blockTemp hRemaining)
      have hTail : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₁ (some c₂)
          ((remaining.erase k).card + 1) := by
        simpa [c₁, c₂] using
          listMap_resetEmpty_run α β tm readInput writeOutput (ListMapState.reset false)
            source (remaining.erase k) acc output blockTemp
      have hAll :=
        StateTransition.EvalsToInTime.trans
          (listMapMachine α β tm readInput writeOutput).step 1
          ((remaining.erase k).card + 1) c₀ c₁ (some c₂) h₁ hTail
      simpa [c₀, c₁, c₂, Finset.card_erase_add_one hMem, Nat.add_assoc] using hAll
termination_by remaining.card
decreasing_by
  exact Finset.card_erase_lt_of_mem hMem

lemma listMapEmptyWork_update_empty (tm : Turing.FinTM2) (k₀ : tm.K) :
    Function.update (listMapEmptyWork tm) k₀ ([] : List (tm.Γ k₀)) =
      listMapEmptyWork tm := by
  letI := tm.kDecidableEq
  funext k
  by_cases hk : k = k₀
  · subst k
    simp [Function.update, listMapEmptyWork]
  · simp [Function.update, listMapEmptyWork, hk]

noncomputable def listMap_writeOutput_reset_run (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (payload : List (tm.Γ tm.k₁)) (source : List (Option α))
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀)) :
    StateTransition.EvalsToInTime (listMapMachine α β tm readInput writeOutput).step
      (listMapCfg α β tm readInput writeOutput (some ListMapLabel.writeOutput)
        (ListMapState.write none) source
        (Function.update (listMapEmptyWork tm) tm.k₁ payload) acc output blockTemp)
      (some (listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
        (ListMapState.copy ListMapCopyState.endInput) source (listMapEmptyWork tm)
        (none :: (payload.map (fun b => some (writeOutput b))).reverse ++ acc)
        output blockTemp))
      ((listMapAllWorkStacks tm).card + 1 + (2 * payload.length + 2)) := by
  let c₀ := listMapCfg α β tm readInput writeOutput (some ListMapLabel.writeOutput)
    (ListMapState.write none) source
    (Function.update (listMapEmptyWork tm) tm.k₁ payload) acc output blockTemp
  let acc' := none :: (payload.map (fun b => some (writeOutput b))).reverse ++ acc
  let c₁ := listMapCfg α β tm readInput writeOutput
    (some (ListMapLabel.reset (listMapAllWorkStacks tm)))
    (ListMapState.write none) source (listMapEmptyWork tm) acc' output blockTemp
  let c₂ := listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
    (ListMapState.copy ListMapCopyState.endInput) source (listMapEmptyWork tm) acc' output
    blockTemp
  have hWrite : StateTransition.EvalsToInTime
      (listMapMachine α β tm readInput writeOutput).step c₀ (some c₁)
      (2 * payload.length + 2) := by
    have hRaw :=
      listMap_writeOutput_run α β tm readInput writeOutput payload source (listMapEmptyWork tm)
        acc output blockTemp
    simpa [c₀, c₁, acc', listMapEmptyWork_update_empty] using hRaw
  have hReset : StateTransition.EvalsToInTime
      (listMapMachine α β tm readInput writeOutput).step c₁ (some c₂)
      ((listMapAllWorkStacks tm).card + 1) := by
    simpa [c₁, c₂, acc'] using
      listMap_resetEmpty_run α β tm readInput writeOutput (ListMapState.write none)
        source (listMapAllWorkStacks tm) acc' output blockTemp
  simpa [c₀, c₁, c₂, acc'] using
    StateTransition.EvalsToInTime.trans
      (listMapMachine α β tm readInput writeOutput).step (2 * payload.length + 2)
      ((listMapAllWorkStacks tm).card + 1) c₀ c₁ (some c₂) hWrite hReset

noncomputable def listMap_drainBlockTemp_run (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (state : ListMapState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀)) :
    StateTransition.EvalsToInTime (listMapMachine α β tm readInput writeOutput).step
      (listMapCfg α β tm readInput writeOutput (some ListMapLabel.drainBlockTemp)
        state source work acc output blockTemp)
      (some (listMapCfg α β tm readInput writeOutput (some (ListMapLabel.run tm.main))
        (ListMapState.run tm.initialState) source
        (Function.update work tm.k₀ (blockTemp.reverse ++ work tm.k₀))
        acc output []))
      (2 * blockTemp.length + 1) := by
  induction blockTemp generalizing state work with
  | nil =>
      simpa using
        evalsToInTimeOne
          (listMap_drainBlockTemp_step_nil α β tm readInput writeOutput state source work acc
            output)
  | cons a blockTemp ih =>
      let workTail := Function.update work tm.k₀ (a :: work tm.k₀)
      let c₀ := listMapCfg α β tm readInput writeOutput (some ListMapLabel.drainBlockTemp)
        state source work acc output (a :: blockTemp)
      let c₁ := listMapCfg α β tm readInput writeOutput (some (ListMapLabel.pushWorkInput a))
        (ListMapState.copy (ListMapCopyState.payload a)) source work acc output blockTemp
      let c₂ := listMapCfg α β tm readInput writeOutput (some ListMapLabel.drainBlockTemp)
        (ListMapState.copy (ListMapCopyState.payload a)) source workTail acc output blockTemp
      let c₃ := listMapCfg α β tm readInput writeOutput (some (ListMapLabel.run tm.main))
        (ListMapState.run tm.initialState) source
        (Function.update work tm.k₀ ((a :: blockTemp).reverse ++ work tm.k₀))
        acc output []
      have h₁ : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (listMap_drainBlockTemp_step_cons α β tm readInput writeOutput state a source work
            acc output blockTemp)
      have h₂ : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (listMap_pushWorkInput_step α β tm readInput writeOutput
            (ListMapState.copy (ListMapCopyState.payload a)) a source work acc output blockTemp)
      have h₁₂ : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans
          (listMapMachine α β tm readInput writeOutput).step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₂ (some c₃)
          (2 * blockTemp.length + 1) := by
        have hRaw :=
          ih (ListMapState.copy (ListMapCopyState.payload a)) workTail
        simpa [c₂, c₃, workTail, Function.update, List.reverse_cons, List.append_assoc] using
          hRaw
      have hAll :=
        StateTransition.EvalsToInTime.trans
          (listMapMachine α β tm readInput writeOutput).step (1 + 1)
          (2 * blockTemp.length + 1) c₀ c₂ (some c₃) h₁₂ hTail
      exact hAll

noncomputable def listMap_readBlock_runFromTemp (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (state : ListMapState tm.σ (tm.Γ tm.k₀) β)
    (payload : List α) (sourceRest : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (acc output : List (Option β)) (blockTemp : List (tm.Γ tm.k₀)) :
    StateTransition.EvalsToInTime (listMapMachine α β tm readInput writeOutput).step
      (listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
        state ((payload.map some) ++ none :: sourceRest) work acc output blockTemp)
      (some (listMapCfg α β tm readInput writeOutput (some (ListMapLabel.run tm.main))
        (ListMapState.run tm.initialState) sourceRest
        (Function.update work tm.k₀
          (blockTemp.reverse ++ payload.map readInput ++ work tm.k₀))
        acc output []))
      (4 * payload.length + 2 * blockTemp.length + 2) := by
  induction payload generalizing state work blockTemp with
  | nil =>
      let c₀ := listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
        state (none :: sourceRest) work acc output blockTemp
      let c₁ := listMapCfg α β tm readInput writeOutput (some ListMapLabel.drainBlockTemp)
        (ListMapState.copy ListMapCopyState.delimiter) sourceRest work acc output blockTemp
      let c₂ := listMapCfg α β tm readInput writeOutput (some (ListMapLabel.run tm.main))
        (ListMapState.run tm.initialState) sourceRest
        (Function.update work tm.k₀ (blockTemp.reverse ++ work tm.k₀)) acc output []
      have h₁ : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (listMap_readSource_step_delimiter α β tm readInput writeOutput state sourceRest work
            acc output blockTemp)
      have h₂ : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₁ (some c₂)
          (2 * blockTemp.length + 1) := by
        simpa [c₁, c₂] using
          listMap_drainBlockTemp_run α β tm readInput writeOutput
            (ListMapState.copy ListMapCopyState.delimiter) sourceRest work acc output blockTemp
      have hAll :=
        StateTransition.EvalsToInTime.trans
          (listMapMachine α β tm readInput writeOutput).step 1
          (2 * blockTemp.length + 1) c₀ c₁ (some c₂) h₁ h₂
      exact evalsToInTime_mono (by simpa [c₀, c₁, c₂] using hAll) (by simp)
  | cons a payload ih =>
      let inputSym := readInput a
      let c₀ := listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
        state ((a :: payload).map some ++ none :: sourceRest) work acc output blockTemp
      let c₁ := listMapCfg α β tm readInput writeOutput
        (some (ListMapLabel.pushBlockTemp inputSym))
        (ListMapState.copy (ListMapCopyState.payload inputSym))
        (payload.map some ++ none :: sourceRest) work acc output blockTemp
      let c₂ := listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
        (ListMapState.copy (ListMapCopyState.payload inputSym))
        (payload.map some ++ none :: sourceRest) work acc output (inputSym :: blockTemp)
      let c₃ := listMapCfg α β tm readInput writeOutput (some (ListMapLabel.run tm.main))
        (ListMapState.run tm.initialState) sourceRest
        (Function.update work tm.k₀
          (blockTemp.reverse ++ (a :: payload).map readInput ++ work tm.k₀))
        acc output []
      have h₁ : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₀ (some c₁) 1 := by
        simpa [c₀, c₁, inputSym, List.map_cons] using
          evalsToInTimeOne
            (listMap_readSource_step_payload α β tm readInput writeOutput state a
              (payload.map some ++ none :: sourceRest) work acc output blockTemp)
      have h₂ : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (listMap_pushBlockTemp_step α β tm readInput writeOutput
            (ListMapState.copy (ListMapCopyState.payload inputSym)) inputSym
            (payload.map some ++ none :: sourceRest) work acc output blockTemp)
      have h₁₂ : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans
          (listMapMachine α β tm readInput writeOutput).step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₂ (some c₃)
          (4 * payload.length + 2 * (inputSym :: blockTemp).length + 2) := by
        have hRaw :=
          ih (ListMapState.copy (ListMapCopyState.payload inputSym)) work
            (inputSym :: blockTemp)
        simpa [c₂, c₃, inputSym, List.map_cons, List.reverse_cons, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hRaw
      have hAll :=
        StateTransition.EvalsToInTime.trans
          (listMapMachine α β tm readInput writeOutput).step (1 + 1)
          (4 * payload.length + 2 * (inputSym :: blockTemp).length + 2)
          c₀ c₂ (some c₃) h₁₂ hTail
      convert hAll using 1
      simp only [List.length_cons]
      omega

noncomputable def listMap_readBlock_run (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (payload : List α) (sourceRest : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (acc output : List (Option β)) :
    StateTransition.EvalsToInTime (listMapMachine α β tm readInput writeOutput).step
      (listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
        (ListMapState.copy ListMapCopyState.endInput)
        (payload.map some ++ none :: sourceRest) work acc output [])
      (some (listMapCfg α β tm readInput writeOutput (some (ListMapLabel.run tm.main))
        (ListMapState.run tm.initialState) sourceRest
        (Function.update work tm.k₀ (payload.map readInput ++ work tm.k₀))
        acc output []))
      (4 * payload.length + 2) := by
  simpa using
    listMap_readBlock_runFromTemp α β tm readInput writeOutput
      (ListMapState.copy ListMapCopyState.endInput) payload sourceRest work acc output []

noncomputable def listMap_oneBlock_run (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (payload : List α) (sourceRest : List (Option α))
    (mapped : List (tm.Γ tm.k₁)) (acc output : List (Option β)) {time : Nat}
    (hRun :
      StateTransition.EvalsToInTime tm.step
        (Turing.initList tm (payload.map readInput))
        (some (Turing.haltList tm mapped)) time) :
    StateTransition.EvalsToInTime (listMapMachine α β tm readInput writeOutput).step
      (listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
        (ListMapState.copy ListMapCopyState.endInput)
        (payload.map some ++ none :: sourceRest) (listMapEmptyWork tm) acc output [])
      (some (listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
        (ListMapState.copy ListMapCopyState.endInput) sourceRest (listMapEmptyWork tm)
        (none :: (mapped.map (fun b => some (writeOutput b))).reverse ++ acc) output []))
      (((listMapAllWorkStacks tm).card + 1 + (2 * mapped.length + 2)) +
        (time + (4 * payload.length + 2))) := by
  let input := payload.map readInput
  let c₀ := listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
    (ListMapState.copy ListMapCopyState.endInput)
    (payload.map some ++ none :: sourceRest) (listMapEmptyWork tm) acc output []
  let cRunStart :=
    listMapRunCfg α β tm readInput writeOutput (Turing.initList tm input) sourceRest acc output []
  let cWriteStart :=
    listMapRunCfg α β tm readInput writeOutput (Turing.haltList tm mapped) sourceRest acc output []
  let acc' := none :: (mapped.map (fun b => some (writeOutput b))).reverse ++ acc
  let cDone := listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
    (ListMapState.copy ListMapCopyState.endInput) sourceRest (listMapEmptyWork tm) acc' output []
  have hRead : StateTransition.EvalsToInTime
      (listMapMachine α β tm readInput writeOutput).step c₀ (some cRunStart)
      (4 * payload.length + 2) := by
    have hRaw :=
      listMap_readBlock_run α β tm readInput writeOutput payload sourceRest
        (listMapEmptyWork tm) acc output
    simpa [c₀, cRunStart, input, listMapRunCfg, listMapCfg, listMapEmptyWork,
      initList_eq_update_empty] using hRaw
  have hRunLift : StateTransition.EvalsToInTime
      (listMapMachine α β tm readInput writeOutput).step cRunStart (some cWriteStart) time := by
    simpa [cRunStart, cWriteStart, input] using
      listMapRun_evalsToInTime α β tm readInput writeOutput sourceRest acc output [] hRun
  have hReadRun : StateTransition.EvalsToInTime
      (listMapMachine α β tm readInput writeOutput).step c₀ (some cWriteStart)
      (time + (4 * payload.length + 2)) :=
    StateTransition.EvalsToInTime.trans
      (listMapMachine α β tm readInput writeOutput).step (4 * payload.length + 2) time
      c₀ cRunStart (some cWriteStart) hRead hRunLift
  have hWrite : StateTransition.EvalsToInTime
      (listMapMachine α β tm readInput writeOutput).step cWriteStart (some cDone)
      ((listMapAllWorkStacks tm).card + 1 + (2 * mapped.length + 2)) := by
    have hWriteStart :
        cWriteStart =
          listMapCfg α β tm readInput writeOutput (some ListMapLabel.writeOutput)
            (ListMapState.write none) sourceRest
            (Function.update (listMapEmptyWork tm) tm.k₁ mapped) acc output [] := by
      simp [cWriteStart, listMapRunCfg, listMapCfg, Turing.haltList]
      funext stack
      cases stack with
      | source => rfl
      | work k =>
          by_cases hk : k = tm.k₁
          · subst k
            simp [Function.update]
          · simp [Function.update, listMapEmptyWork, hk]
      | acc => rfl
      | output => rfl
      | blockTemp => rfl
    have hRaw :=
      listMap_writeOutput_reset_run α β tm readInput writeOutput mapped sourceRest acc output []
    rw [hWriteStart]
    simpa [cDone, acc'] using hRaw
  simpa [c₀, cRunStart, cWriteStart, cDone, acc'] using
    StateTransition.EvalsToInTime.trans
      (listMapMachine α β tm readInput writeOutput).step
      (time + (4 * payload.length + 2))
      ((listMapAllWorkStacks tm).card + 1 + (2 * mapped.length + 2))
      c₀ cWriteStart (some cDone) hReadRun hWrite

/-- One element-output block as it is kept in the reverse accumulator. -/
def listMapReverseBlock {β γ : Type} (writeOutput : γ → β) (mapped : List γ) :
    List (Option β) :=
  none :: (mapped.map (fun b => some (writeOutput b))).reverse

/-- Reverse accumulator produced by scanning a source list from left to right. -/
def listMapLoopAcc {δ β γ : Type} (writeOutput : γ → β)
    (mapped : δ → List γ) : List δ → List (Option β)
  | [] => []
  | x :: xs => listMapLoopAcc writeOutput mapped xs ++
      listMapReverseBlock writeOutput (mapped x)

/-- Physical encoded-source length for a list-map loop. -/
def listMapSourceLength {δ α : Type} (payload : δ → List α) (xs : List δ) : Nat :=
  (xs.flatMap fun x => (payload x).map some ++ [none]).length

@[simp] lemma listMapSourceLength_nil {δ α : Type} (payload : δ → List α) :
    listMapSourceLength payload [] = 0 := by
  simp [listMapSourceLength]

@[simp] lemma listMapSourceLength_cons {δ α : Type}
    (payload : δ → List α) (x : δ) (xs : List δ) :
    listMapSourceLength payload (x :: xs) =
      (payload x).length + 1 + listMapSourceLength payload xs := by
  simp [listMapSourceLength]
  omega

/-- Exact time for one source element block in the arbitrary list-map runner. -/
noncomputable def listMapBlockTime (tm : Turing.FinTM2)
    (payloadLen mappedLen elemTime : Nat) : Nat :=
  (((listMapAllWorkStacks tm).card + 1 + (2 * mappedLen + 2)) +
    (elemTime + (4 * payloadLen + 2)))

/-- Exact loop time obtained by summing the one-block runner over the input list. -/
noncomputable def listMapLoopTime {δ α γ : Type} (tm : Turing.FinTM2)
    (payload : δ → List α) (mapped : δ → List γ) (elemTime : δ → Nat) :
    List δ → Nat
  | [] => 0
  | x :: xs =>
      listMapLoopTime tm payload mapped elemTime xs +
        listMapBlockTime tm (payload x).length (mapped x).length (elemTime x)

lemma listMapLoopAcc_reverse {δ β γ : Type}
    (writeOutput : γ → β) (mapped : δ → List γ) :
    ∀ xs : List δ,
      (listMapLoopAcc writeOutput mapped xs).reverse =
        xs.flatMap fun x => (mapped x).map (fun b => some (writeOutput b)) ++ [none]
  | [] => by
      simp [listMapLoopAcc]
  | x :: xs => by
      simp [listMapLoopAcc, listMapReverseBlock, listMapLoopAcc_reverse writeOutput mapped xs,
        List.append_assoc]

noncomputable def listMap_loop_run {δ α β : Type} (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : α → tm.Γ tm.k₀) (writeOutput : tm.Γ tm.k₁ → β)
    (payload : δ → List α) (mapped : δ → List (tm.Γ tm.k₁)) (elemTime : δ → Nat)
    (sourceRest : List (Option α)) (acc output : List (Option β))
    (hRun : ∀ x,
      StateTransition.EvalsToInTime tm.step
        (Turing.initList tm ((payload x).map readInput))
        (some (Turing.haltList tm (mapped x))) (elemTime x)) :
    ∀ xs : List δ,
      StateTransition.EvalsToInTime (listMapMachine α β tm readInput writeOutput).step
        (listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
          (ListMapState.copy ListMapCopyState.endInput)
          (xs.flatMap (fun x => (payload x).map some ++ [none]) ++ sourceRest)
          (listMapEmptyWork tm) acc output [])
        (some (listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
          (ListMapState.copy ListMapCopyState.endInput) sourceRest (listMapEmptyWork tm)
          (listMapLoopAcc writeOutput mapped xs ++ acc) output []))
        (listMapLoopTime tm payload mapped elemTime xs)
  | [] => by
      simpa [listMapLoopTime, listMapLoopAcc] using
        StateTransition.EvalsToInTime.refl
          (listMapMachine α β tm readInput writeOutput).step
          (listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
            (ListMapState.copy ListMapCopyState.endInput) sourceRest (listMapEmptyWork tm)
            acc output [])
  | x :: xs => by
      let blockAcc := listMapReverseBlock writeOutput (mapped x)
      let restSource :=
        xs.flatMap (fun x => (payload x).map some ++ [none]) ++ sourceRest
      let c₀ := listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
        (ListMapState.copy ListMapCopyState.endInput)
        (((payload x).map some ++ [none]) ++ restSource)
        (listMapEmptyWork tm) acc output []
      let c₁ := listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
        (ListMapState.copy ListMapCopyState.endInput) restSource (listMapEmptyWork tm)
        (blockAcc ++ acc) output []
      let c₂ := listMapCfg α β tm readInput writeOutput (some ListMapLabel.readSource)
        (ListMapState.copy ListMapCopyState.endInput) sourceRest (listMapEmptyWork tm)
        (listMapLoopAcc writeOutput mapped xs ++ blockAcc ++ acc) output []
      have hBlock : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₀ (some c₁)
          (listMapBlockTime tm (payload x).length (mapped x).length (elemTime x)) := by
        have hRaw :=
          listMap_oneBlock_run α β tm readInput writeOutput (payload x) restSource
            (mapped x) acc output (hRun x)
        simpa [c₀, c₁, blockAcc, restSource, listMapReverseBlock, listMapBlockTime,
          List.append_assoc] using hRaw
      have hTail : StateTransition.EvalsToInTime
          (listMapMachine α β tm readInput writeOutput).step c₁ (some c₂)
          (listMapLoopTime tm payload mapped elemTime xs) := by
        have hRaw :=
          listMap_loop_run tm readInput writeOutput payload mapped elemTime sourceRest
            (blockAcc ++ acc) output hRun xs
        simpa [c₁, c₂, restSource, blockAcc, List.append_assoc] using hRaw
      have hAll :=
        StateTransition.EvalsToInTime.trans
          (listMapMachine α β tm readInput writeOutput).step
          (listMapBlockTime tm (payload x).length (mapped x).length (elemTime x))
          (listMapLoopTime tm payload mapped elemTime xs)
          c₀ c₁ (some c₂) hBlock hTail
      simpa [c₀, c₁, c₂, restSource, blockAcc, listMapLoopTime, listMapLoopAcc,
        List.append_assoc] using hAll

end TM2Programs
end ComplexityReduction
