import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.ListFold.Part2

namespace ComplexityReduction
namespace TM2Programs
open Turing.TM2.Stmt

noncomputable def listFold_outputToAcc_reset_run (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (payload : List (tm.Γ tm.k₁)) (source : List (Option α))
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀)) :
    StateTransition.EvalsToInTime (listFoldMachine α β tm readInput writeOutput initialAcc).step
      (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readOutput) (ListFoldState.output none) source
        (Function.update (listFoldEmptyWork tm) tm.k₁ payload) acc payloadTemp accTemp [])
      (some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput)
        source (listFoldEmptyWork tm) (payload.map writeOutput ++ acc) payloadTemp
        accTemp []))
      ((listFoldAllWorkStacks tm).card + 1 + (4 * payload.length + 2)) := by
  let acc' := payload.map writeOutput ++ acc
  let c₀ := listFoldCfg α β tm readInput writeOutput initialAcc
    (some ListFoldLabel.readOutput) (ListFoldState.output none) source
    (Function.update (listFoldEmptyWork tm) tm.k₁ payload) acc payloadTemp accTemp []
  let c₁ := listFoldCfg α β tm readInput writeOutput initialAcc
    (some (ListFoldLabel.reset (listFoldAllWorkStacks tm))) (ListFoldState.output none)
    source (listFoldEmptyWork tm) acc' payloadTemp accTemp []
  let c₂ := listFoldCfg α β tm readInput writeOutput initialAcc
    (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput)
    source (listFoldEmptyWork tm) acc' payloadTemp accTemp []
  have hWrite : StateTransition.EvalsToInTime
      (listFoldMachine α β tm readInput writeOutput initialAcc).step c₀ (some c₁)
      (4 * payload.length + 2) := by
    have hRaw :=
      listFold_outputToAcc_run α β tm readInput writeOutput initialAcc payload source
        (listFoldEmptyWork tm) acc payloadTemp accTemp
    simpa [c₀, c₁, acc', listFoldEmptyWork_update_empty] using hRaw
  have hReset : StateTransition.EvalsToInTime
      (listFoldMachine α β tm readInput writeOutput initialAcc).step c₁ (some c₂)
      ((listFoldAllWorkStacks tm).card + 1) := by
    simpa [c₁, c₂, acc'] using
      listFold_resetEmpty_run α β tm readInput writeOutput initialAcc
        (ListFoldState.output none) source (listFoldAllWorkStacks tm) acc' payloadTemp
        accTemp
  simpa [c₀, c₁, c₂, acc'] using
    StateTransition.EvalsToInTime.trans
      (listFoldMachine α β tm readInput writeOutput initialAcc).step
      (4 * payload.length + 2) ((listFoldAllWorkStacks tm).card + 1)
      c₀ c₁ (some c₂) hWrite hReset

noncomputable def listFold_oneBlock_run (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (payload : List α) (sourceRest : List (Option α)) (accStack : List β)
    (mapped : List (tm.Γ tm.k₁)) {time : Nat}
    (hRun :
      StateTransition.EvalsToInTime tm.step
        (Turing.initList tm
          (accStack.map (fun b => readInput (some (Sum.inl b))) ++ readInput none ::
            payload.map (fun a => readInput (some (Sum.inr a)))))
        (some (Turing.haltList tm mapped)) time) :
    StateTransition.EvalsToInTime (listFoldMachine α β tm readInput writeOutput initialAcc).step
      (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput)
        (payload.map some ++ none :: sourceRest) (listFoldEmptyWork tm) accStack [] [] [])
      (some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput)
        sourceRest (listFoldEmptyWork tm) (mapped.map writeOutput) [] [] []))
      (((listFoldAllWorkStacks tm).card + 1 + (4 * mapped.length + 2)) +
        (time + (4 * payload.length + 4 * accStack.length + 5))) := by
  let input :=
    accStack.map (fun b => readInput (some (Sum.inl b))) ++ readInput none ::
      payload.map (fun a => readInput (some (Sum.inr a)))
  let c₀ := listFoldCfg α β tm readInput writeOutput initialAcc
    (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput)
    (payload.map some ++ none :: sourceRest) (listFoldEmptyWork tm) accStack [] [] []
  let cRunStart :=
    listFoldRunCfg α β tm readInput writeOutput initialAcc (Turing.initList tm input)
      sourceRest [] [] [] []
  let cWriteStart :=
    listFoldRunCfg α β tm readInput writeOutput initialAcc (Turing.haltList tm mapped)
      sourceRest [] [] [] []
  let cDone := listFoldCfg α β tm readInput writeOutput initialAcc
    (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput)
    sourceRest (listFoldEmptyWork tm) (mapped.map writeOutput) [] [] []
  have hBuild : StateTransition.EvalsToInTime
      (listFoldMachine α β tm readInput writeOutput initialAcc).step c₀ (some cRunStart)
      (4 * payload.length + 4 * accStack.length + 5) := by
    have hRaw :=
      listFold_productInput_run α β tm readInput writeOutput initialAcc payload sourceRest
        (listFoldEmptyWork tm) accStack []
    simpa [c₀, cRunStart, input, listFoldRunCfg, listFoldCfg, listFoldEmptyWork,
      initList_eq_update_empty] using hRaw
  have hRunLift : StateTransition.EvalsToInTime
      (listFoldMachine α β tm readInput writeOutput initialAcc).step cRunStart
      (some cWriteStart) time := by
    simpa [cRunStart, cWriteStart, input] using
      listFoldRun_evalsToInTime α β tm readInput writeOutput initialAcc sourceRest [] [] [] []
        hRun
  have hBuildRun : StateTransition.EvalsToInTime
      (listFoldMachine α β tm readInput writeOutput initialAcc).step c₀ (some cWriteStart)
      (time + (4 * payload.length + 4 * accStack.length + 5)) :=
    StateTransition.EvalsToInTime.trans
      (listFoldMachine α β tm readInput writeOutput initialAcc).step
      (4 * payload.length + 4 * accStack.length + 5) time c₀ cRunStart
      (some cWriteStart) hBuild hRunLift
  have hTail : StateTransition.EvalsToInTime
      (listFoldMachine α β tm readInput writeOutput initialAcc).step cWriteStart
      (some cDone) ((listFoldAllWorkStacks tm).card + 1 + (4 * mapped.length + 2)) := by
    have hWriteStart :
        cWriteStart =
          listFoldCfg α β tm readInput writeOutput initialAcc
            (some ListFoldLabel.readOutput) (ListFoldState.output none) sourceRest
            (Function.update (listFoldEmptyWork tm) tm.k₁ mapped) [] [] [] [] := by
      simp [cWriteStart, listFoldRunCfg, listFoldCfg, Turing.haltList]
      funext stack
      cases stack with
      | source => rfl
      | work k =>
          by_cases hk : k = tm.k₁
          · subst k
            simp [Function.update]
          · simp [Function.update, listFoldEmptyWork, hk]
      | acc => rfl
      | payloadTemp => rfl
      | accTemp => rfl
      | outputTemp => rfl
    have hRaw :=
      listFold_outputToAcc_reset_run α β tm readInput writeOutput initialAcc mapped sourceRest
        [] [] []
    rw [hWriteStart]
    simpa [cDone] using hRaw
  simpa [c₀, cRunStart, cWriteStart, cDone] using
    StateTransition.EvalsToInTime.trans
      (listFoldMachine α β tm readInput writeOutput initialAcc).step
      (time + (4 * payload.length + 4 * accStack.length + 5))
      ((listFoldAllWorkStacks tm).card + 1 + (4 * mapped.length + 2))
      c₀ cWriteStart (some cDone) hBuildRun hTail

/-- Physical encoded-source length for the list-fold runner loop. -/
def listFoldSourceLength {δ α : Type} (payload : δ → List α) (xs : List δ) : Nat :=
  (xs.flatMap fun x => (payload x).map some ++ [none]).length

@[simp] lemma listFoldSourceLength_encodedType (X : EncodedType) (xs : List X.Carrier) :
    listFoldSourceLength X.encode xs = (EncodedType.list X).inputSize xs := by
  rfl

@[simp] lemma listFoldSourceLength_nil {δ α : Type} (payload : δ → List α) :
    listFoldSourceLength payload [] = 0 := by
  simp [listFoldSourceLength]

@[simp] lemma listFoldSourceLength_cons {δ α : Type}
    (payload : δ → List α) (x : δ) (xs : List δ) :
    listFoldSourceLength payload (x :: xs) =
      (payload x).length + 1 + listFoldSourceLength payload xs := by
  simp [listFoldSourceLength]
  omega

/-- Exact time for one source element block in the list-fold runner. -/
noncomputable def listFoldBlockTime (tm : Turing.FinTM2)
    (payloadLen accLen mappedLen stepTime : Nat) : Nat :=
  ((listFoldAllWorkStacks tm).card + 1 + (4 * mappedLen + 2)) +
    (stepTime + (4 * payloadLen + 4 * accLen + 5))

/-- Accumulator obtained by iterating supplied fold-step outputs over the source list. -/
def listFoldLoopAcc {δ β γ : Type} (writeOutput : γ → β)
    (mapped : List β → δ → List γ) : List β → List δ → List β
  | acc, [] => acc
  | acc, x :: xs => listFoldLoopAcc writeOutput mapped ((mapped acc x).map writeOutput) xs

/-- Exact loop time obtained by summing the one-block runner over the input list. -/
noncomputable def listFoldLoopTime {δ α β γ : Type} (tm : Turing.FinTM2)
    (payload : δ → List α) (mapped : List β → δ → List γ)
    (writeOutput : γ → β) (stepTime : List β → δ → Nat) : List β → List δ → Nat
  | _acc, [] => 0
  | acc, x :: xs =>
      listFoldLoopTime tm payload mapped writeOutput stepTime
          ((mapped acc x).map writeOutput) xs +
        listFoldBlockTime tm (payload x).length acc.length (mapped acc x).length
          (stepTime acc x)

/-- Per-block linear coefficient for bounded list-fold loop-time estimates. -/
noncomputable def listFoldBlockTimeCoeff (tm : Turing.FinTM2) (B T : Nat) : Nat :=
  (listFoldAllWorkStacks tm).card + 8 * B + T + 12

lemma listFoldLoopAcc_length_le_global {δ β γ : Type}
    (writeOutput : γ → β) (mapped : List β → δ → List γ) (B : Nat)
    (hMapped : ∀ acc x, acc.length ≤ B → (mapped acc x).length ≤ B) :
    ∀ (xs : List δ) (acc : List β), acc.length ≤ B →
      (listFoldLoopAcc writeOutput mapped acc xs).length ≤ B
  | [], acc, hAcc => by
      simpa [listFoldLoopAcc] using hAcc
  | x :: xs, acc, hAcc => by
      have hNext : ((mapped acc x).map writeOutput).length ≤ B := by
        simpa using hMapped acc x hAcc
      simpa [listFoldLoopAcc] using
        listFoldLoopAcc_length_le_global writeOutput mapped B hMapped xs
          ((mapped acc x).map writeOutput) hNext

lemma listFoldBlockTime_le_linear_payload (tm : Turing.FinTM2)
    {payloadLen accLen mappedLen step : Nat} (B T : Nat)
    (hAcc : accLen ≤ B) (hMapped : mappedLen ≤ B) (hStep : step ≤ T) :
    listFoldBlockTime tm payloadLen accLen mappedLen step ≤
      listFoldBlockTimeCoeff tm B T * (payloadLen + 1) := by
  simp [listFoldBlockTime, listFoldBlockTimeCoeff]
  nlinarith [hAcc, hMapped, hStep,
    Nat.zero_le (payloadLen * (listFoldAllWorkStacks tm).card),
    Nat.zero_le (payloadLen * B), Nat.zero_le (payloadLen * T)]

lemma listFoldLoopTime_le_global {δ α β γ : Type} (tm : Turing.FinTM2)
    (payload : δ → List α) (mapped : List β → δ → List γ)
    (writeOutput : γ → β) (stepTime : List β → δ → Nat) (B T : Nat)
    (hMapped : ∀ acc x, acc.length ≤ B → (mapped acc x).length ≤ B)
    (hStep : ∀ acc x, acc.length ≤ B → stepTime acc x ≤ T) :
    ∀ (xs : List δ) (acc : List β), acc.length ≤ B →
      listFoldLoopTime tm payload mapped writeOutput stepTime acc xs ≤
        listFoldBlockTimeCoeff tm B T * listFoldSourceLength payload xs
  | [], _acc, _hAcc => by
      simp [listFoldLoopTime]
  | x :: xs, acc, hAcc => by
      let nextAcc := (mapped acc x).map writeOutput
      have hNext : nextAcc.length ≤ B := by
        simpa [nextAcc] using hMapped acc x hAcc
      have hTail :=
        listFoldLoopTime_le_global tm payload mapped writeOutput stepTime B T hMapped hStep
          xs nextAcc hNext
      have hBlock :
          listFoldBlockTime tm (payload x).length acc.length (mapped acc x).length
              (stepTime acc x) ≤
            listFoldBlockTimeCoeff tm B T * ((payload x).length + 1) :=
        listFoldBlockTime_le_linear_payload tm B T hAcc (hMapped acc x hAcc)
          (hStep acc x hAcc)
      calc
        listFoldLoopTime tm payload mapped writeOutput stepTime acc (x :: xs)
            = listFoldLoopTime tm payload mapped writeOutput stepTime nextAcc xs +
                listFoldBlockTime tm (payload x).length acc.length
                  (mapped acc x).length (stepTime acc x) := by
                    simp [listFoldLoopTime, nextAcc]
        _ ≤ listFoldBlockTimeCoeff tm B T * listFoldSourceLength payload xs +
              listFoldBlockTimeCoeff tm B T * ((payload x).length + 1) :=
                Nat.add_le_add hTail hBlock
        _ ≤ listFoldBlockTimeCoeff tm B T * listFoldSourceLength payload (x :: xs) := by
              simp [listFoldSourceLength]
              nlinarith

lemma listFold_totalTime_le_global {δ α β γ : Type} (tm : Turing.FinTM2)
    (payload : δ → List α) (mapped : List β → δ → List γ)
    (writeOutput : γ → β) (stepTime : List β → δ → Nat) (B T : Nat)
    (initialAcc : List β)
    (hInitial : initialAcc.length ≤ B)
    (hMapped : ∀ acc x, acc.length ≤ B → (mapped acc x).length ≤ B)
    (hStep : ∀ acc x, acc.length ≤ B → stepTime acc x ≤ T) (xs : List δ) :
    2 + listFoldLoopTime tm payload mapped writeOutput stepTime initialAcc xs ≤
      (listFoldBlockTimeCoeff tm B T + 2) * (listFoldSourceLength payload xs + 1) := by
  have hLoop :=
    listFoldLoopTime_le_global tm payload mapped writeOutput stepTime B T hMapped hStep
      xs initialAcc hInitial
  nlinarith [hLoop, Nat.zero_le (listFoldBlockTimeCoeff tm B T),
    Nat.zero_le (listFoldSourceLength payload xs)]

noncomputable def listFold_loop_run {δ α β : Type} (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (payload : δ → List α) (mapped : List β → δ → List (tm.Γ tm.k₁))
    (stepTime : List β → δ → Nat) (sourceRest : List (Option α))
    (hRun : ∀ acc x,
      StateTransition.EvalsToInTime tm.step
        (Turing.initList tm
          (acc.map (fun b => readInput (some (Sum.inl b))) ++ readInput none ::
            (payload x).map (fun a => readInput (some (Sum.inr a)))))
        (some (Turing.haltList tm (mapped acc x))) (stepTime acc x)) :
    ∀ (xs : List δ) (acc : List β),
      StateTransition.EvalsToInTime
        (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldCfg α β tm readInput writeOutput initialAcc
          (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput)
          (xs.flatMap (fun x => (payload x).map some ++ [none]) ++ sourceRest)
          (listFoldEmptyWork tm) acc [] [] [])
        (some (listFoldCfg α β tm readInput writeOutput initialAcc
          (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput)
          sourceRest (listFoldEmptyWork tm)
          (listFoldLoopAcc writeOutput mapped acc xs) [] [] []))
        (listFoldLoopTime tm payload mapped writeOutput stepTime acc xs)
  | [], acc => by
      simpa [listFoldLoopTime, listFoldLoopAcc] using
        StateTransition.EvalsToInTime.refl
          (listFoldMachine α β tm readInput writeOutput initialAcc).step
          (listFoldCfg α β tm readInput writeOutput initialAcc
            (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput)
            sourceRest (listFoldEmptyWork tm) acc [] [] [])
  | x :: xs, acc => by
      let blockSource :=
        xs.flatMap (fun x => (payload x).map some ++ [none]) ++ sourceRest
      let nextAcc := (mapped acc x).map writeOutput
      let c₀ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput)
        (((payload x).map some ++ [none]) ++ blockSource) (listFoldEmptyWork tm)
        acc [] [] []
      let c₁ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput)
        blockSource (listFoldEmptyWork tm) nextAcc [] [] []
      let c₂ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput)
        sourceRest (listFoldEmptyWork tm)
        (listFoldLoopAcc writeOutput mapped nextAcc xs) [] [] []
      have hBlock : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₀ (some c₁)
          (listFoldBlockTime tm (payload x).length acc.length (mapped acc x).length
            (stepTime acc x)) := by
        have hRaw :=
          listFold_oneBlock_run α β tm readInput writeOutput initialAcc (payload x)
            blockSource acc (mapped acc x) (hRun acc x)
        simpa [c₀, c₁, blockSource, nextAcc, listFoldBlockTime, List.append_assoc] using hRaw
      have hTail : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₁ (some c₂)
          (listFoldLoopTime tm payload mapped writeOutput stepTime nextAcc xs) := by
        have hRaw :=
          listFold_loop_run tm readInput writeOutput initialAcc payload mapped stepTime
            sourceRest hRun xs nextAcc
        simpa [c₁, c₂, blockSource, nextAcc, List.append_assoc] using hRaw
      have hAll :=
        StateTransition.EvalsToInTime.trans
          (listFoldMachine α β tm readInput writeOutput initialAcc).step
          (listFoldBlockTime tm (payload x).length acc.length (mapped acc x).length
            (stepTime acc x))
          (listFoldLoopTime tm payload mapped writeOutput stepTime nextAcc xs)
          c₀ c₁ (some c₂) hBlock hTail
      simpa [c₀, c₁, c₂, blockSource, nextAcc, listFoldLoopTime, listFoldLoopAcc,
        List.append_assoc] using hAll

lemma listFold_initList_eq_cfg (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (input : List (Option α)) :
    Turing.initList (listFoldMachine α β tm readInput writeOutput initialAcc) input =
      listFoldCfg α β tm readInput writeOutput initialAcc (some ListFoldLabel.init)
        (ListFoldState.scan ListFoldScanState.endInput) input (listFoldEmptyWork tm)
        [] [] [] [] := by
  simp [Turing.initList, listFoldMachine, listFoldCfg, listFoldEmptyWork]
  congr
  funext stack
  cases stack <;> simp

lemma listFold_haltList_eq_cfg (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc output : List β) :
    Turing.haltList (listFoldMachine α β tm readInput writeOutput initialAcc) output =
      listFoldCfg α β tm readInput writeOutput initialAcc none
        (ListFoldState.scan ListFoldScanState.endInput) [] (listFoldEmptyWork tm)
        output [] [] [] := by
  simp [Turing.haltList, listFoldMachine, listFoldCfg, listFoldEmptyWork]
  congr
  funext stack
  cases stack <;> simp

lemma listFold_init_step (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (source : List (Option α)) :
    (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldCfg α β tm readInput writeOutput initialAcc (some ListFoldLabel.init)
          (ListFoldState.scan ListFoldScanState.endInput) source (listFoldEmptyWork tm)
          [] [] [] []) =
      some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput)
        source (listFoldEmptyWork tm) initialAcc [] [] []) := by
  simp [listFoldMachine, listFoldCfg, Turing.FinTM2.step, Turing.TM2.step]
  have h :=
    stepAux_pushAllListFoldAcc (α := α) (β := β) tm initialAcc
      (Turing.TM2.Stmt.goto fun _ => ListFoldLabel.readSource)
      (ListFoldState.scan ListFoldScanState.endInput)
      (fun
        | ListFoldStack.source => source
        | ListFoldStack.work k => ([] : List (tm.Γ k))
        | ListFoldStack.acc => ([] : List β)
        | ListFoldStack.payloadTemp => ([] : List (tm.Γ tm.k₀))
        | ListFoldStack.accTemp => ([] : List (tm.Γ tm.k₀))
        | ListFoldStack.outputTemp => ([] : List β))
  have hUpdate :
      Function.update
          ((fun
            | ListFoldStack.source => source
            | ListFoldStack.work k => ([] : List (tm.Γ k))
            | ListFoldStack.acc => ([] : List β)
            | ListFoldStack.payloadTemp => ([] : List (tm.Γ tm.k₀))
            | ListFoldStack.accTemp => ([] : List (tm.Γ tm.k₀))
            | ListFoldStack.outputTemp => ([] : List β)) :
            (s : ListFoldStack tm.K) → List (listFoldAlphabet α β tm s))
          ListFoldStack.acc initialAcc =
        ((fun
          | ListFoldStack.source => source
          | ListFoldStack.work k => ([] : List (tm.Γ k))
          | ListFoldStack.acc => initialAcc
          | ListFoldStack.payloadTemp => ([] : List (tm.Γ tm.k₀))
          | ListFoldStack.accTemp => ([] : List (tm.Γ tm.k₀))
          | ListFoldStack.outputTemp => ([] : List β)) :
          (s : ListFoldStack tm.K) → List (listFoldAlphabet α β tm s)) := by
    funext stack
    cases stack <;> simp [Function.update]
  apply congrArg some
  simpa [listFoldEmptyWork, listFoldCfg, hUpdate] using h

noncomputable def listFold_outputsInTime {δ α β : Type} (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (payload : δ → List α) (mapped : List β → δ → List (tm.Γ tm.k₁))
    (stepTime : List β → δ → Nat)
    (hRun : ∀ acc x,
      StateTransition.EvalsToInTime tm.step
        (Turing.initList tm
          (acc.map (fun b => readInput (some (Sum.inl b))) ++ readInput none ::
            (payload x).map (fun a => readInput (some (Sum.inr a)))))
        (some (Turing.haltList tm (mapped acc x))) (stepTime acc x))
    (xs : List δ) :
    Turing.TM2OutputsInTime (listFoldMachine α β tm readInput writeOutput initialAcc)
      (xs.flatMap fun x => (payload x).map some ++ [none])
      (some (listFoldLoopAcc writeOutput mapped initialAcc xs))
      (2 + listFoldLoopTime tm payload mapped writeOutput stepTime initialAcc xs) := by
  let input := xs.flatMap fun x => (payload x).map some ++ [none]
  let finalAcc := listFoldLoopAcc writeOutput mapped initialAcc xs
  let cInit := listFoldCfg α β tm readInput writeOutput initialAcc (some ListFoldLabel.init)
    (ListFoldState.scan ListFoldScanState.endInput) input (listFoldEmptyWork tm) [] [] [] []
  let cStart := listFoldCfg α β tm readInput writeOutput initialAcc
    (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput) input
    (listFoldEmptyWork tm) initialAcc [] [] []
  let cLoopDone := listFoldCfg α β tm readInput writeOutput initialAcc
    (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput) []
    (listFoldEmptyWork tm) finalAcc [] [] []
  let cHalt := listFoldCfg α β tm readInput writeOutput initialAcc none
    (ListFoldState.scan ListFoldScanState.endInput) [] (listFoldEmptyWork tm) finalAcc [] [] []
  have hInit : StateTransition.EvalsToInTime
      (listFoldMachine α β tm readInput writeOutput initialAcc).step cInit (some cStart) 1 := by
    simpa [cInit, cStart] using
      evalsToInTimeOne
        (listFold_init_step α β tm readInput writeOutput initialAcc input)
  have hLoop : StateTransition.EvalsToInTime
      (listFoldMachine α β tm readInput writeOutput initialAcc).step cStart (some cLoopDone)
      (listFoldLoopTime tm payload mapped writeOutput stepTime initialAcc xs) := by
    have hRaw :=
      listFold_loop_run tm readInput writeOutput initialAcc payload mapped stepTime [] hRun xs
        initialAcc
    simpa [cStart, cLoopDone, input, finalAcc] using hRaw
  have hInitLoop : StateTransition.EvalsToInTime
      (listFoldMachine α β tm readInput writeOutput initialAcc).step cInit (some cLoopDone)
      (listFoldLoopTime tm payload mapped writeOutput stepTime initialAcc xs + 1) := by
    have hRaw :=
      StateTransition.EvalsToInTime.trans
        (listFoldMachine α β tm readInput writeOutput initialAcc).step 1
        (listFoldLoopTime tm payload mapped writeOutput stepTime initialAcc xs)
        cInit cStart (some cLoopDone) hInit hLoop
    simpa [Nat.add_comm] using hRaw
  have hFinal : StateTransition.EvalsToInTime
      (listFoldMachine α β tm readInput writeOutput initialAcc).step cLoopDone (some cHalt)
      1 := by
    simpa [cLoopDone, cHalt, finalAcc] using
      evalsToInTimeOne
        (listFold_readSource_step_nil α β tm readInput writeOutput initialAcc
          (ListFoldState.scan ListFoldScanState.endInput) (listFoldEmptyWork tm)
          finalAcc [] [] [])
  have hAll : StateTransition.EvalsToInTime
      (listFoldMachine α β tm readInput writeOutput initialAcc).step cInit (some cHalt)
      (2 + listFoldLoopTime tm payload mapped writeOutput stepTime initialAcc xs) := by
    have hRaw :=
      StateTransition.EvalsToInTime.trans
        (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldLoopTime tm payload mapped writeOutput stepTime initialAcc xs + 1) 1
        cInit cLoopDone (some cHalt) hInitLoop hFinal
    convert hRaw using 1
    omega
  simpa [Turing.TM2OutputsInTime, cInit, cHalt, input, finalAcc,
    listFold_initList_eq_cfg, listFold_haltList_eq_cfg] using hAll

/-- Polynomial time bound used by bounded raw-stack list-fold runners. -/
noncomputable def listFoldBoundedTimePolynomial (tm : Turing.FinTM2)
    (bound stepBound : Polynomial Nat) : Polynomial Nat :=
  (Polynomial.C (listFoldAllWorkStacks tm).card + Polynomial.C 8 * bound +
      stepBound + Polynomial.C 14) * (Polynomial.X + 1)

@[simp] lemma listFoldBoundedTimePolynomial_eval (tm : Turing.FinTM2)
    (bound stepBound : Polynomial Nat) (n : Nat) :
    (listFoldBoundedTimePolynomial tm bound stepBound).eval n =
      ((listFoldAllWorkStacks tm).card + 8 * bound.eval n +
          stepBound.eval n + 14) * (n + 1) := by
  simp [listFoldBoundedTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Nat.add_assoc]

/--
Bounded raw-stack list fold as a direct TM2 polynomial-time computation.

This theorem deliberately computes a fold over raw accumulator/output stacks.
It is the sound bounded foundation for future typed fold wrappers; it does not
promote the arbitrary `CostedPolyTimeMap.list_foldl_map` constructor.
-/
noncomputable def listFoldBoundedComputableInPolyTime {δ α β : Type}
    [Fintype α] [Fintype β]
    (tm : Turing.FinTM2)
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (payload : δ → List α) (mapped : List β → δ → List (tm.Γ tm.k₁))
    (stepTime : List β → δ → Nat) (bound stepBound : Polynomial Nat)
    (hRun : ∀ acc x,
      StateTransition.EvalsToInTime tm.step
        (Turing.initList tm
          (acc.map (fun b => readInput (some (Sum.inl b))) ++ readInput none ::
            (payload x).map (fun a => readInput (some (Sum.inr a)))))
        (some (Turing.haltList tm (mapped acc x))) (stepTime acc x))
    (hInitial : ∀ xs : List δ,
      initialAcc.length ≤ bound.eval (listFoldSourceLength payload xs))
    (hMapped : ∀ (xs : List δ) acc x,
      acc.length ≤ bound.eval (listFoldSourceLength payload xs) →
        (mapped acc x).length ≤ bound.eval (listFoldSourceLength payload xs))
    (hStep : ∀ (xs : List δ) acc x,
      acc.length ≤ bound.eval (listFoldSourceLength payload xs) →
        stepTime acc x ≤ stepBound.eval (listFoldSourceLength payload xs)) :
    Turing.TM2ComputableInPolyTime
      (fun xs : List δ => xs.flatMap fun x => (payload x).map some ++ [none])
      (fun output : List β => output)
      (fun xs : List δ => listFoldLoopAcc writeOutput mapped initialAcc xs) where
  tm := listFoldMachine α β tm readInput writeOutput initialAcc
  inputAlphabet := Equiv.refl (Option α)
  outputAlphabet := Equiv.refl β
  time := listFoldBoundedTimePolynomial tm bound stepBound
  outputsFun xs := by
    let n := listFoldSourceLength payload xs
    have hRaw :=
      listFold_outputsInTime tm readInput writeOutput initialAcc payload mapped stepTime hRun xs
    have hTime :
        2 + listFoldLoopTime tm payload mapped writeOutput stepTime initialAcc xs ≤
          (listFoldBoundedTimePolynomial tm bound stepBound).eval
            ((xs.flatMap fun x => (payload x).map some ++ [none]).length) := by
      have hBound :=
        listFold_totalTime_le_global tm payload mapped writeOutput stepTime
          (bound.eval n) (stepBound.eval n) initialAcc (hInitial xs)
          (hMapped xs) (hStep xs) xs
      simpa [n, listFoldSourceLength, listFoldBlockTimeCoeff,
        listFoldBoundedTimePolynomial_eval, Nat.add_assoc] using hBound
    have hMono := evalsToInTime_mono hRaw hTime
    have hInput :
        List.map (Equiv.refl (Option α)).invFun
            (List.flatMap (fun x => List.map some (payload x) ++ [none]) xs) =
          List.flatMap (fun x => List.map some (payload x) ++ [none]) xs := by
      change
        List.map id (List.flatMap (fun x => List.map some (payload x) ++ [none]) xs) =
          List.flatMap (fun x => List.map some (payload x) ++ [none]) xs
      simp
    have hOutput :
        List.map (Equiv.refl β).invFun (listFoldLoopAcc writeOutput mapped initialAcc xs) =
          listFoldLoopAcc writeOutput mapped initialAcc xs := by
      change
        List.map id (listFoldLoopAcc writeOutput mapped initialAcc xs) =
          listFoldLoopAcc writeOutput mapped initialAcc xs
      simp
    unfold Turing.TM2OutputsInTime
    convert hMono using 1
    · exact
        congrArg
          (Turing.initList (listFoldMachine α β tm readInput writeOutput initialAcc))
          hInput
    · exact
        congrArg
          (Option.map (Turing.haltList
            (listFoldMachine α β tm readInput writeOutput initialAcc)))
          (congrArg some hOutput)

/-- Exact loop time for the typed, reachable-accumulator list-fold runner. -/
noncomputable def listFoldTypedLoopTime
    (X Y : EncodedType) (step : Y.Carrier × X.Carrier → Y.Carrier)
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod Y X).encode Y.encode step) :
    Y.Carrier → List X.Carrier → Nat
  | _acc, [] => 0
  | acc, x :: xs =>
      listFoldTypedLoopTime X Y step hStep (step (acc, x)) xs +
        listFoldBlockTime hStep.tm (X.encode x).length (Y.encode acc).length
          (Y.encode (step (acc, x))).length
          (hStep.time.eval ((EncodedType.prod Y X).inputSize (acc, x)))

/--
List-fold loop execution specialized to typed reachable accumulators.

Unlike `listFoldBoundedComputableInPolyTime`, this theorem never asks the
supplied step machine to run on arbitrary raw accumulator stacks.  Each block
is run only on an accumulator stack known to be `Y.encode acc`.
-/
noncomputable def listFoldTyped_loop_run
    (X Y : EncodedType) (step : Y.Carrier × X.Carrier → Y.Carrier)
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod Y X).encode Y.encode step)
    (init : Y.Carrier) (sourceRest : List (Option X.Symbol)) :
    ∀ (xs : List X.Carrier) (acc : Y.Carrier),
      StateTransition.EvalsToInTime
        (listFoldMachine X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
          hStep.outputAlphabet.toFun (Y.encode init)).step
        (listFoldCfg X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
          hStep.outputAlphabet.toFun (Y.encode init)
          (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput)
          ((xs.flatMap fun x => (X.encode x).map some ++ [none]) ++ sourceRest)
          (listFoldEmptyWork hStep.tm)
          (Y.encode acc) [] [] [])
        (some (listFoldCfg X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
          hStep.outputAlphabet.toFun (Y.encode init)
          (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput)
          sourceRest (listFoldEmptyWork hStep.tm)
          (Y.encode (xs.foldl (fun acc x => step (acc, x)) acc)) [] [] []))
        (listFoldTypedLoopTime X Y step hStep acc xs)
  | [], acc => by
      simpa [listFoldTypedLoopTime, EncodedType.list] using
        StateTransition.EvalsToInTime.refl
          (listFoldMachine X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
            hStep.outputAlphabet.toFun (Y.encode init)).step
          (listFoldCfg X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
            hStep.outputAlphabet.toFun (Y.encode init)
            (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput)
            sourceRest (listFoldEmptyWork hStep.tm) (Y.encode acc) [] [] [])
  | x :: xs, acc => by
      let mapped : List (hStep.tm.Γ hStep.tm.k₁) :=
        (Y.encode (step (acc, x))).map hStep.outputAlphabet.invFun
      let sourceTail := (xs.flatMap fun x => (X.encode x).map some ++ [none]) ++ sourceRest
      let nextAcc := step (acc, x)
      let c₀ := listFoldCfg X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
        hStep.outputAlphabet.toFun (Y.encode init)
        (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput)
        ((X.encode x).map some ++ none :: sourceTail) (listFoldEmptyWork hStep.tm)
        (Y.encode acc) [] [] []
      let c₁ := listFoldCfg X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
        hStep.outputAlphabet.toFun (Y.encode init)
        (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput)
        sourceTail (listFoldEmptyWork hStep.tm) (Y.encode nextAcc) [] [] []
      let c₂ := listFoldCfg X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
        hStep.outputAlphabet.toFun (Y.encode init)
        (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput)
        sourceRest (listFoldEmptyWork hStep.tm)
        (Y.encode (xs.foldl (fun acc x => step (acc, x)) nextAcc)) [] [] []
      have hRun : StateTransition.EvalsToInTime hStep.tm.step
          (Turing.initList hStep.tm
            ((Y.encode acc).map
                (fun b => hStep.inputAlphabet.invFun (some (Sum.inl b))) ++
              hStep.inputAlphabet.invFun none ::
                (X.encode x).map
                  (fun a => hStep.inputAlphabet.invFun (some (Sum.inr a)))))
          (some (Turing.haltList hStep.tm mapped))
          (hStep.time.eval ((EncodedType.prod Y X).inputSize (acc, x))) := by
        simpa [mapped, EncodedType.prod, EncodedType.inputSize] using
          hStep.outputsFun (acc, x)
      have hBlock : StateTransition.EvalsToInTime
          (listFoldMachine X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
            hStep.outputAlphabet.toFun (Y.encode init)).step c₀ (some c₁)
          (listFoldBlockTime hStep.tm (X.encode x).length (Y.encode acc).length
            (Y.encode nextAcc).length
            (hStep.time.eval ((EncodedType.prod Y X).inputSize (acc, x)))) := by
        have hRaw :=
          listFold_oneBlock_run X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
            hStep.outputAlphabet.toFun (Y.encode init) (X.encode x) sourceTail (Y.encode acc)
            mapped hRun
        simpa [c₀, c₁, sourceTail, mapped, nextAcc, listFoldBlockTime] using hRaw
      have hTail : StateTransition.EvalsToInTime
          (listFoldMachine X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
            hStep.outputAlphabet.toFun (Y.encode init)).step c₁ (some c₂)
          (listFoldTypedLoopTime X Y step hStep nextAcc xs) := by
        have hRaw :=
          listFoldTyped_loop_run X Y step hStep init sourceRest xs nextAcc
        simpa [c₁, c₂, sourceTail, nextAcc] using hRaw
      have hAll :=
        StateTransition.EvalsToInTime.trans
          (listFoldMachine X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
            hStep.outputAlphabet.toFun (Y.encode init)).step
          (listFoldBlockTime hStep.tm (X.encode x).length (Y.encode acc).length
            (Y.encode nextAcc).length
            (hStep.time.eval ((EncodedType.prod Y X).inputSize (acc, x))))
          (listFoldTypedLoopTime X Y step hStep nextAcc xs)
          c₀ c₁ (some c₂) hBlock hTail
      simpa [c₀, c₁, c₂, sourceTail, nextAcc, listFoldTypedLoopTime,
        EncodedType.list, List.append_assoc] using hAll

/--
Fixed-initial-accumulator typed list fold as a direct TM2 computation under an
explicit total loop-time polynomial bound.  This is a bounded/reachable fold
runner; it does not promote the arbitrary raw `listFoldlMap` closure.
-/
noncomputable def listFoldTyped_outputsInTime
    (X Y : EncodedType) (step : Y.Carrier × X.Carrier → Y.Carrier)
    (init : Y.Carrier)
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod Y X).encode Y.encode step)
    (xs : List X.Carrier) :
    Turing.TM2OutputsInTime
      (listFoldMachine X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
        hStep.outputAlphabet.toFun (Y.encode init))
      ((EncodedType.list X).encode xs)
      (some (Y.encode (xs.foldl (fun acc x => step (acc, x)) init)))
      (2 + listFoldTypedLoopTime X Y step hStep init xs) := by
  let machine :=
    listFoldMachine X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
      hStep.outputAlphabet.toFun (Y.encode init)
  let input := xs.flatMap fun x => (X.encode x).map some ++ [none]
  let finalAcc := xs.foldl (fun acc x => step (acc, x)) init
  let cInit := listFoldCfg X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
    hStep.outputAlphabet.toFun (Y.encode init) (some ListFoldLabel.init)
    (ListFoldState.scan ListFoldScanState.endInput) input (listFoldEmptyWork hStep.tm)
    [] [] [] []
  let cStart := listFoldCfg X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
    hStep.outputAlphabet.toFun (Y.encode init) (some ListFoldLabel.readSource)
    (ListFoldState.scan ListFoldScanState.endInput) input (listFoldEmptyWork hStep.tm)
    (Y.encode init) [] [] []
  let cLoopDone := listFoldCfg X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
    hStep.outputAlphabet.toFun (Y.encode init) (some ListFoldLabel.readSource)
    (ListFoldState.scan ListFoldScanState.endInput) [] (listFoldEmptyWork hStep.tm)
    (Y.encode finalAcc) [] [] []
  let cHalt := listFoldCfg X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
    hStep.outputAlphabet.toFun (Y.encode init) none
    (ListFoldState.scan ListFoldScanState.endInput) [] (listFoldEmptyWork hStep.tm)
    (Y.encode finalAcc) [] [] []
  have hInit : StateTransition.EvalsToInTime machine.step cInit (some cStart) 1 := by
    simpa [machine, cInit, cStart, input] using
      evalsToInTimeOne
        (listFold_init_step X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
          hStep.outputAlphabet.toFun (Y.encode init) input)
  have hLoop : StateTransition.EvalsToInTime machine.step cStart (some cLoopDone)
      (listFoldTypedLoopTime X Y step hStep init xs) := by
    have hRaw := listFoldTyped_loop_run X Y step hStep init [] xs init
    simpa [machine, cStart, cLoopDone, input, finalAcc] using hRaw
  have hInitLoop : StateTransition.EvalsToInTime machine.step cInit (some cLoopDone)
      (listFoldTypedLoopTime X Y step hStep init xs + 1) := by
    have hRaw :=
      StateTransition.EvalsToInTime.trans machine.step 1
        (listFoldTypedLoopTime X Y step hStep init xs)
        cInit cStart (some cLoopDone) hInit hLoop
    simpa [Nat.add_comm] using hRaw
  have hFinal : StateTransition.EvalsToInTime machine.step cLoopDone (some cHalt) 1 := by
    simpa [machine, cLoopDone, cHalt, finalAcc] using
      evalsToInTimeOne
        (listFold_readSource_step_nil X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
          hStep.outputAlphabet.toFun (Y.encode init)
          (ListFoldState.scan ListFoldScanState.endInput) (listFoldEmptyWork hStep.tm)
          (Y.encode finalAcc) [] [] [])
  have hAll : StateTransition.EvalsToInTime machine.step cInit (some cHalt)
      (2 + listFoldTypedLoopTime X Y step hStep init xs) := by
    have hRaw :=
      StateTransition.EvalsToInTime.trans machine.step
        (listFoldTypedLoopTime X Y step hStep init xs + 1) 1
        cInit cLoopDone (some cHalt) hInitLoop hFinal
    convert hRaw using 1
    omega
  unfold Turing.TM2OutputsInTime
  convert hAll using 1
  · simp [cInit, input, listFold_initList_eq_cfg, EncodedType.list]
  · simp [machine, cHalt, finalAcc, listFold_haltList_eq_cfg]

noncomputable def listFoldTypedComputableInPolyTime
    (X Y : EncodedType) (step : Y.Carrier × X.Carrier → Y.Carrier)
    (init : Y.Carrier)
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod Y X).encode Y.encode step)
    (time : Polynomial Nat)
    (hTime : ∀ xs : List X.Carrier,
      2 + listFoldTypedLoopTime X Y step hStep init xs ≤
        time.eval ((EncodedType.list X).inputSize xs)) :
    Turing.TM2ComputableInPolyTime
      (EncodedType.list X).encode Y.encode
      (fun xs : List X.Carrier => xs.foldl (fun acc x => step (acc, x)) init) where
  tm :=
    listFoldMachine X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
      hStep.outputAlphabet.toFun (Y.encode init)
  inputAlphabet := Equiv.refl (Option X.Symbol)
  outputAlphabet := Equiv.refl Y.Symbol
  time := time
  outputsFun xs := by
    let machine :=
      listFoldMachine X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
        hStep.outputAlphabet.toFun (Y.encode init)
    let input := xs.flatMap fun x => (X.encode x).map some ++ [none]
    let finalAcc := xs.foldl (fun acc x => step (acc, x)) init
    let cInit := listFoldCfg X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
      hStep.outputAlphabet.toFun (Y.encode init) (some ListFoldLabel.init)
      (ListFoldState.scan ListFoldScanState.endInput) input (listFoldEmptyWork hStep.tm)
      [] [] [] []
    let cStart := listFoldCfg X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
      hStep.outputAlphabet.toFun (Y.encode init) (some ListFoldLabel.readSource)
      (ListFoldState.scan ListFoldScanState.endInput) input (listFoldEmptyWork hStep.tm)
      (Y.encode init) [] [] []
    let cLoopDone := listFoldCfg X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
      hStep.outputAlphabet.toFun (Y.encode init) (some ListFoldLabel.readSource)
      (ListFoldState.scan ListFoldScanState.endInput) [] (listFoldEmptyWork hStep.tm)
      (Y.encode finalAcc) [] [] []
    let cHalt := listFoldCfg X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
      hStep.outputAlphabet.toFun (Y.encode init) none
      (ListFoldState.scan ListFoldScanState.endInput) [] (listFoldEmptyWork hStep.tm)
      (Y.encode finalAcc) [] [] []
    have hInit : StateTransition.EvalsToInTime machine.step cInit (some cStart) 1 := by
      simpa [machine, cInit, cStart, input] using
        evalsToInTimeOne
          (listFold_init_step X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
            hStep.outputAlphabet.toFun (Y.encode init) input)
    have hLoop : StateTransition.EvalsToInTime machine.step cStart (some cLoopDone)
        (listFoldTypedLoopTime X Y step hStep init xs) := by
      have hRaw := listFoldTyped_loop_run X Y step hStep init [] xs init
      simpa [machine, cStart, cLoopDone, input, finalAcc] using hRaw
    have hInitLoop : StateTransition.EvalsToInTime machine.step cInit (some cLoopDone)
        (listFoldTypedLoopTime X Y step hStep init xs + 1) := by
      have hRaw :=
        StateTransition.EvalsToInTime.trans machine.step 1
          (listFoldTypedLoopTime X Y step hStep init xs)
          cInit cStart (some cLoopDone) hInit hLoop
      simpa [Nat.add_comm] using hRaw
    have hFinal : StateTransition.EvalsToInTime machine.step cLoopDone (some cHalt) 1 := by
      simpa [machine, cLoopDone, cHalt, finalAcc] using
        evalsToInTimeOne
          (listFold_readSource_step_nil X.Symbol Y.Symbol hStep.tm hStep.inputAlphabet.invFun
            hStep.outputAlphabet.toFun (Y.encode init)
            (ListFoldState.scan ListFoldScanState.endInput) (listFoldEmptyWork hStep.tm)
            (Y.encode finalAcc) [] [] [])
    have hAll : StateTransition.EvalsToInTime machine.step cInit (some cHalt)
        (2 + listFoldTypedLoopTime X Y step hStep init xs) := by
      have hRaw :=
        StateTransition.EvalsToInTime.trans machine.step
          (listFoldTypedLoopTime X Y step hStep init xs + 1) 1
          cInit cLoopDone (some cHalt) hInitLoop hFinal
      convert hRaw using 1
      omega
    have hMono := evalsToInTime_mono hAll (hTime xs)
    have hInput :
        List.map (Equiv.refl (Option X.Symbol)).invFun ((EncodedType.list X).encode xs) =
          input := by
      change List.map id (xs.flatMap fun x => (X.encode x).map some ++ [none]) = input
      simp [input]
    have hOutput :
        List.map (Equiv.refl Y.Symbol).invFun
            (Y.encode (xs.foldl (fun acc x => step (acc, x)) init)) =
          Y.encode (xs.foldl (fun acc x => step (acc, x)) init) := by
      change List.map id (Y.encode (xs.foldl (fun acc x => step (acc, x)) init)) =
        Y.encode (xs.foldl (fun acc x => step (acc, x)) init)
      simp
    unfold Turing.TM2OutputsInTime
    convert hMono using 1
    · calc
        Turing.initList machine
            (List.map (Equiv.refl (Option X.Symbol)).invFun ((EncodedType.list X).encode xs)) =
          Turing.initList machine input := by
            exact congrArg (Turing.initList machine) hInput
        _ = cInit := by
            simp [machine, cInit, listFold_initList_eq_cfg]
    · exact
        calc
          Option.map (Turing.haltList machine)
              (some (List.map (Equiv.refl Y.Symbol).invFun
                (Y.encode (xs.foldl (fun acc x => step (acc, x)) init)))) =
            Option.map (Turing.haltList machine)
              (some (Y.encode (xs.foldl (fun acc x => step (acc, x)) init))) := by
              exact
                congrArg (Option.map (Turing.haltList machine))
                  (congrArg some hOutput)
          _ = some cHalt := by
              simp [machine, cHalt, finalAcc, listFold_haltList_eq_cfg]
              rfl

end TM2Programs
end ComplexityReduction
