import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.ListFold.Part1

namespace ComplexityReduction
namespace TM2Programs
open Turing.TM2.Stmt

noncomputable def listFold_sourceBlock_run (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (payload : List α) (sourceRest : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (accTemp : List (tm.Γ tm.k₀)) (outputTemp : List β) :
    StateTransition.EvalsToInTime (listFoldMachine α β tm readInput writeOutput initialAcc).step
      (listFoldCfg α β tm readInput writeOutput initialAcc (some ListFoldLabel.readSource)
        (ListFoldState.scan ListFoldScanState.endInput)
        (payload.map some ++ none :: sourceRest) work acc [] accTemp outputTemp)
      (some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readAcc) (ListFoldState.scan ListFoldScanState.delimiter)
        sourceRest
        (Function.update work tm.k₀
          (readInput none :: payload.map (fun a => readInput (some (Sum.inr a))) ++
            work tm.k₀))
        acc [] accTemp outputTemp))
      (4 * payload.length + 3) := by
  let workPayload :=
    Function.update work tm.k₀
      (payload.map (fun a => readInput (some (Sum.inr a))) ++ work tm.k₀)
  let c₀ := listFoldCfg α β tm readInput writeOutput initialAcc (some ListFoldLabel.readSource)
    (ListFoldState.scan ListFoldScanState.endInput)
    (payload.map some ++ none :: sourceRest) work acc [] accTemp outputTemp
  let c₁ := listFoldCfg α β tm readInput writeOutput initialAcc
    (some ListFoldLabel.pushDelimiter) (ListFoldState.scan ListFoldScanState.delimiter)
    sourceRest workPayload acc [] accTemp outputTemp
  let c₂ := listFoldCfg α β tm readInput writeOutput initialAcc
    (some ListFoldLabel.readAcc) (ListFoldState.scan ListFoldScanState.delimiter)
    sourceRest
    (Function.update work tm.k₀
      (readInput none :: payload.map (fun a => readInput (some (Sum.inr a))) ++ work tm.k₀))
    acc [] accTemp outputTemp
  have hRead : StateTransition.EvalsToInTime
      (listFoldMachine α β tm readInput writeOutput initialAcc).step c₀ (some c₁)
      (4 * payload.length + 2) := by
    simpa [c₀, c₁, workPayload] using
      listFold_readSourcePayload_run α β tm readInput writeOutput initialAcc payload sourceRest
        work acc accTemp outputTemp
  have hDelimiter : StateTransition.EvalsToInTime
      (listFoldMachine α β tm readInput writeOutput initialAcc).step c₁ (some c₂) 1 := by
    have hStep :=
      listFold_pushDelimiter_step α β tm readInput writeOutput initialAcc
        (ListFoldState.scan ListFoldScanState.delimiter) sourceRest workPayload acc [] accTemp
        outputTemp
    simpa [c₁, c₂, workPayload, Function.update] using evalsToInTimeOne hStep
  have hAll :=
    StateTransition.EvalsToInTime.trans
      (listFoldMachine α β tm readInput writeOutput initialAcc).step (4 * payload.length + 2)
      1 c₀ c₁ (some c₂) hRead hDelimiter
  convert hAll using 1
  omega

lemma listFold_readAcc_step_payload (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (b : β) (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀))
    (outputTemp : List β) :
    (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldCfg α β tm readInput writeOutput initialAcc
          (some ListFoldLabel.readAcc) state source work (b :: acc)
          payloadTemp accTemp outputTemp) =
      some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.pushAccTemp (readInput (some (Sum.inl b)))))
        (ListFoldState.scan (ListFoldScanState.payload (readInput (some (Sum.inl b)))))
        source work acc payloadTemp accTemp outputTemp) := by
  simp [listFoldMachine, listFoldCfg, listFoldScanState, ListFoldScanState.isPayload]
  congr
  funext k
  cases k <;> rfl

lemma listFold_readAcc_step_nil (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (payloadTemp accTemp : List (tm.Γ tm.k₀)) (outputTemp : List β) :
    (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldCfg α β tm readInput writeOutput initialAcc
          (some ListFoldLabel.readAcc) state source work [] payloadTemp accTemp
          outputTemp) =
      some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.drainAcc)
        (ListFoldState.scan ListFoldScanState.delimiter)
        source work [] payloadTemp accTemp outputTemp) := by
  simp [listFoldMachine, listFoldCfg, listFoldScanState, ListFoldScanState.isPayload]

lemma listFold_pushAccTemp_step (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (a : tm.Γ tm.k₀) (source : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀))
    (outputTemp : List β) :
    (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldCfg α β tm readInput writeOutput initialAcc
          (some (ListFoldLabel.pushAccTemp a)) state source work acc
          payloadTemp accTemp outputTemp) =
      some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readAcc) state source work acc payloadTemp
        (a :: accTemp) outputTemp) := by
  simp [listFoldMachine, listFoldCfg]
  congr
  funext k
  cases k <;> rfl

lemma listFold_drainAcc_step_cons (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (a : tm.Γ tm.k₀) (source : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (payloadTemp accTemp : List (tm.Γ tm.k₀)) (outputTemp : List β) :
    (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldCfg α β tm readInput writeOutput initialAcc
          (some ListFoldLabel.drainAcc) state source work [] payloadTemp
          (a :: accTemp) outputTemp) =
      some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.pushAccInput a))
        (ListFoldState.scan (ListFoldScanState.payload a))
        source work [] payloadTemp accTemp outputTemp) := by
  simp [listFoldMachine, listFoldCfg, listFoldScanState, ListFoldScanState.isPayload]
  congr
  funext k
  cases k <;> rfl

lemma listFold_drainAcc_step_nil (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (payloadTemp : List (tm.Γ tm.k₀)) (outputTemp : List β) :
    (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldCfg α β tm readInput writeOutput initialAcc
          (some ListFoldLabel.drainAcc) state source work [] payloadTemp []
          outputTemp) =
      some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.run tm.main)) (ListFoldState.run tm.initialState)
        source work [] payloadTemp [] outputTemp) := by
  simp [listFoldMachine, listFoldCfg, listFoldScanState, ListFoldScanState.isPayload]

lemma listFold_pushAccInput_step (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (a : tm.Γ tm.k₀) (source : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (payloadTemp accTemp : List (tm.Γ tm.k₀)) (outputTemp : List β) :
    (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldCfg α β tm readInput writeOutput initialAcc
          (some (ListFoldLabel.pushAccInput a)) state source work [] payloadTemp
          accTemp outputTemp) =
      some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.drainAcc) state source
        (Function.update work tm.k₀ (a :: work tm.k₀)) [] payloadTemp accTemp
        outputTemp) := by
  simp [listFoldMachine, listFoldCfg]
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
  | payloadTemp => rfl
  | accTemp => rfl
  | outputTemp => rfl

noncomputable def listFold_drainAcc_run (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (payloadTemp accTemp : List (tm.Γ tm.k₀)) (outputTemp : List β) :
    StateTransition.EvalsToInTime (listFoldMachine α β tm readInput writeOutput initialAcc).step
      (listFoldCfg α β tm readInput writeOutput initialAcc (some ListFoldLabel.drainAcc)
        state source work [] payloadTemp accTemp outputTemp)
      (some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.run tm.main)) (ListFoldState.run tm.initialState)
        source (Function.update work tm.k₀ (accTemp.reverse ++ work tm.k₀))
        [] payloadTemp [] outputTemp))
      (2 * accTemp.length + 1) := by
  induction accTemp generalizing state work with
  | nil =>
      simpa using
        evalsToInTimeOne
          (listFold_drainAcc_step_nil α β tm readInput writeOutput initialAcc state
            source work payloadTemp outputTemp)
  | cons a accTemp ih =>
      let workTail := Function.update work tm.k₀ (a :: work tm.k₀)
      let c₀ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.drainAcc) state source work [] payloadTemp (a :: accTemp)
        outputTemp
      let c₁ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.pushAccInput a))
        (ListFoldState.scan (ListFoldScanState.payload a))
        source work [] payloadTemp accTemp outputTemp
      let c₂ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.drainAcc)
        (ListFoldState.scan (ListFoldScanState.payload a))
        source workTail [] payloadTemp accTemp outputTemp
      let c₃ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.run tm.main)) (ListFoldState.run tm.initialState)
        source (Function.update work tm.k₀ ((a :: accTemp).reverse ++ work tm.k₀))
        [] payloadTemp [] outputTemp
      have h₁ : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (listFold_drainAcc_step_cons α β tm readInput writeOutput initialAcc state a
            source work payloadTemp accTemp outputTemp)
      have h₂ : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (listFold_pushAccInput_step α β tm readInput writeOutput initialAcc
            (ListFoldState.scan (ListFoldScanState.payload a)) a source work payloadTemp
            accTemp outputTemp)
      have h₁₂ : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans
          (listFoldMachine α β tm readInput writeOutput initialAcc).step 1 1 c₀ c₁
          (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₂ (some c₃)
          (2 * accTemp.length + 1) := by
        have hRaw :=
          ih (ListFoldState.scan (ListFoldScanState.payload a)) workTail
        simpa [c₂, c₃, workTail, Function.update, List.reverse_cons, List.append_assoc] using
          hRaw
      have hAll :=
        StateTransition.EvalsToInTime.trans
          (listFoldMachine α β tm readInput writeOutput initialAcc).step (1 + 1)
          (2 * accTemp.length + 1) c₀ c₂ (some c₃) h₁₂ hTail
      exact evalsToInTime_mono (by simpa [c₀, c₃] using hAll) (by
        simp
        omega)

noncomputable def listFold_readAcc_runFromTemp (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (accStack : List β) (source : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (payloadTemp accTemp : List (tm.Γ tm.k₀)) (outputTemp : List β) :
    StateTransition.EvalsToInTime (listFoldMachine α β tm readInput writeOutput initialAcc).step
      (listFoldCfg α β tm readInput writeOutput initialAcc (some ListFoldLabel.readAcc)
        state source work accStack payloadTemp accTemp outputTemp)
      (some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.run tm.main)) (ListFoldState.run tm.initialState)
        source
        (Function.update work tm.k₀
          (accTemp.reverse ++ accStack.map (fun b => readInput (some (Sum.inl b))) ++
            work tm.k₀))
        [] payloadTemp [] outputTemp))
      (4 * accStack.length + 2 * accTemp.length + 2) := by
  induction accStack generalizing state work accTemp with
  | nil =>
      let c₀ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readAcc) state source work [] payloadTemp accTemp outputTemp
      let c₁ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.drainAcc) (ListFoldState.scan ListFoldScanState.delimiter)
        source work [] payloadTemp accTemp outputTemp
      let c₂ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.run tm.main)) (ListFoldState.run tm.initialState)
        source (Function.update work tm.k₀ (accTemp.reverse ++ work tm.k₀))
        [] payloadTemp [] outputTemp
      have h₁ : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (listFold_readAcc_step_nil α β tm readInput writeOutput initialAcc state
            source work payloadTemp accTemp outputTemp)
      have h₂ : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₁ (some c₂)
          (2 * accTemp.length + 1) := by
        simpa [c₁, c₂] using
          listFold_drainAcc_run α β tm readInput writeOutput initialAcc
            (ListFoldState.scan ListFoldScanState.delimiter) source work payloadTemp accTemp
            outputTemp
      have hAll :=
        StateTransition.EvalsToInTime.trans
          (listFoldMachine α β tm readInput writeOutput initialAcc).step 1
          (2 * accTemp.length + 1) c₀ c₁ (some c₂) h₁ h₂
      exact evalsToInTime_mono (by simpa [c₀, c₁, c₂] using hAll) (by simp)
  | cons b accStack ih =>
      let inputSym := readInput (some (Sum.inl b))
      let c₀ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readAcc) state source work (b :: accStack)
        payloadTemp accTemp outputTemp
      let c₁ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.pushAccTemp inputSym))
        (ListFoldState.scan (ListFoldScanState.payload inputSym))
        source work accStack payloadTemp accTemp outputTemp
      let c₂ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readAcc)
        (ListFoldState.scan (ListFoldScanState.payload inputSym))
        source work accStack payloadTemp (inputSym :: accTemp) outputTemp
      let c₃ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.run tm.main)) (ListFoldState.run tm.initialState)
        source
        (Function.update work tm.k₀
          (accTemp.reverse ++
            (b :: accStack).map (fun b => readInput (some (Sum.inl b))) ++ work tm.k₀))
        [] payloadTemp [] outputTemp
      have h₁ : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₀ (some c₁) 1 := by
        simpa [c₀, c₁, inputSym, List.map_cons] using
          evalsToInTimeOne
            (listFold_readAcc_step_payload α β tm readInput writeOutput initialAcc state b
              source work accStack payloadTemp accTemp outputTemp)
      have h₂ : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (listFold_pushAccTemp_step α β tm readInput writeOutput initialAcc
            (ListFoldState.scan (ListFoldScanState.payload inputSym)) inputSym source work
            accStack payloadTemp accTemp outputTemp)
      have h₁₂ : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans
          (listFoldMachine α β tm readInput writeOutput initialAcc).step 1 1 c₀ c₁
          (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₂ (some c₃)
          (4 * accStack.length + 2 * (inputSym :: accTemp).length + 2) := by
        have hRaw :=
          ih (ListFoldState.scan (ListFoldScanState.payload inputSym)) work
            (inputSym :: accTemp)
        simpa [c₂, c₃, inputSym, List.map_cons, List.reverse_cons, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hRaw
      have hAll :=
        StateTransition.EvalsToInTime.trans
          (listFoldMachine α β tm readInput writeOutput initialAcc).step (1 + 1)
          (4 * accStack.length + 2 * (inputSym :: accTemp).length + 2)
          c₀ c₂ (some c₃) h₁₂ hTail
      convert hAll using 1
      simp only [List.length_cons]
      omega

noncomputable def listFold_readAcc_run (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (accStack : List β) (source : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (payloadTemp : List (tm.Γ tm.k₀)) (outputTemp : List β) :
    StateTransition.EvalsToInTime (listFoldMachine α β tm readInput writeOutput initialAcc).step
      (listFoldCfg α β tm readInput writeOutput initialAcc (some ListFoldLabel.readAcc)
        (ListFoldState.scan ListFoldScanState.delimiter)
        source work accStack payloadTemp [] outputTemp)
      (some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.run tm.main)) (ListFoldState.run tm.initialState)
        source
        (Function.update work tm.k₀
          (accStack.map (fun b => readInput (some (Sum.inl b))) ++ work tm.k₀))
        [] payloadTemp [] outputTemp))
      (4 * accStack.length + 2) := by
  simpa using
    listFold_readAcc_runFromTemp α β tm readInput writeOutput initialAcc
      (ListFoldState.scan ListFoldScanState.delimiter) accStack source work payloadTemp []
      outputTemp

noncomputable def listFold_productInput_run (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (payload : List α) (sourceRest : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (accStack : List β) (outputTemp : List β) :
    StateTransition.EvalsToInTime (listFoldMachine α β tm readInput writeOutput initialAcc).step
      (listFoldCfg α β tm readInput writeOutput initialAcc (some ListFoldLabel.readSource)
        (ListFoldState.scan ListFoldScanState.endInput)
        (payload.map some ++ none :: sourceRest) work accStack [] [] outputTemp)
      (some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.run tm.main)) (ListFoldState.run tm.initialState)
        sourceRest
        (Function.update work tm.k₀
          (accStack.map (fun b => readInput (some (Sum.inl b))) ++ readInput none ::
            payload.map (fun a => readInput (some (Sum.inr a))) ++ work tm.k₀))
        [] [] [] outputTemp))
      (4 * payload.length + 4 * accStack.length + 5) := by
  let payloadInput :=
    payload.map (fun a => readInput (some (Sum.inr a)))
  let accInput :=
    accStack.map (fun b => readInput (some (Sum.inl b)))
  let workPayload :=
    Function.update work tm.k₀ (readInput none :: payloadInput ++ work tm.k₀)
  let c₀ := listFoldCfg α β tm readInput writeOutput initialAcc (some ListFoldLabel.readSource)
    (ListFoldState.scan ListFoldScanState.endInput)
    (payload.map some ++ none :: sourceRest) work accStack [] [] outputTemp
  let c₁ := listFoldCfg α β tm readInput writeOutput initialAcc (some ListFoldLabel.readAcc)
    (ListFoldState.scan ListFoldScanState.delimiter) sourceRest workPayload accStack [] []
    outputTemp
  let c₂ := listFoldCfg α β tm readInput writeOutput initialAcc
    (some (ListFoldLabel.run tm.main)) (ListFoldState.run tm.initialState)
    sourceRest
    (Function.update work tm.k₀
      (accInput ++ readInput none :: payloadInput ++ work tm.k₀))
    [] [] [] outputTemp
  have hPayload : StateTransition.EvalsToInTime
      (listFoldMachine α β tm readInput writeOutput initialAcc).step c₀ (some c₁)
      (4 * payload.length + 3) := by
    simpa [c₀, c₁, workPayload, payloadInput] using
      listFold_sourceBlock_run α β tm readInput writeOutput initialAcc payload sourceRest work
        accStack [] outputTemp
  have hAcc : StateTransition.EvalsToInTime
      (listFoldMachine α β tm readInput writeOutput initialAcc).step c₁ (some c₂)
      (4 * accStack.length + 2) := by
    have hRaw :=
      listFold_readAcc_run α β tm readInput writeOutput initialAcc accStack sourceRest
        workPayload [] outputTemp
    simpa [c₁, c₂, workPayload, payloadInput, accInput, Function.update, List.append_assoc] using
      hRaw
  have hAll :=
    StateTransition.EvalsToInTime.trans
      (listFoldMachine α β tm readInput writeOutput initialAcc).step (4 * payload.length + 3)
      (4 * accStack.length + 2) c₀ c₁ (some c₂) hPayload hAcc
  convert hAll using 1
  omega

lemma listFold_readOutput_step_cons (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (b : tm.Γ tm.k₁) (source : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀))
    (outputTemp : List β) :
    (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldCfg α β tm readInput writeOutput initialAcc
          (some ListFoldLabel.readOutput) state source
          (Function.update work tm.k₁ (b :: work tm.k₁)) acc payloadTemp accTemp
          outputTemp) =
      some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.pushOutputTemp (writeOutput b)))
        (ListFoldState.output (some (writeOutput b))) source
        (Function.update work tm.k₁ (work tm.k₁)) acc payloadTemp accTemp outputTemp) := by
  simp [listFoldMachine, listFoldCfg, listFoldOutputState]
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
  | payloadTemp => rfl
  | accTemp => rfl
  | outputTemp => rfl

lemma listFold_readOutput_step_nil (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀))
    (outputTemp : List β) (hEmpty : work tm.k₁ = []) :
    (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldCfg α β tm readInput writeOutput initialAcc
          (some ListFoldLabel.readOutput) state source work acc payloadTemp accTemp
          outputTemp) =
      some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.drainOutput) (ListFoldState.output none) source work acc
        payloadTemp accTemp outputTemp) := by
  simp [listFoldMachine, listFoldCfg, listFoldOutputState, hEmpty]
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
  | payloadTemp => rfl
  | accTemp => rfl
  | outputTemp => rfl

lemma listFold_pushOutputTemp_step (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (b : β) (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀))
    (outputTemp : List β) :
    (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldCfg α β tm readInput writeOutput initialAcc
          (some (ListFoldLabel.pushOutputTemp b)) state source work acc payloadTemp
          accTemp outputTemp) =
      some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readOutput) state source work acc payloadTemp accTemp
        (b :: outputTemp)) := by
  simp [listFoldMachine, listFoldCfg]
  congr
  funext k
  cases k <;> rfl

lemma listFold_drainOutput_step_cons (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (b : β) (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀))
    (outputTemp : List β) :
    (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldCfg α β tm readInput writeOutput initialAcc
          (some ListFoldLabel.drainOutput) state source work acc payloadTemp accTemp
          (b :: outputTemp)) =
      some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.pushAcc b)) (ListFoldState.output (some b)) source work acc
        payloadTemp accTemp outputTemp) := by
  simp [listFoldMachine, listFoldCfg, listFoldOutputState]
  congr
  funext k
  cases k <;> rfl

lemma listFold_drainOutput_step_nil (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀)) :
    (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldCfg α β tm readInput writeOutput initialAcc
          (some ListFoldLabel.drainOutput) state source work acc payloadTemp accTemp []) =
      some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.reset (listFoldAllWorkStacks tm))) (ListFoldState.output none)
        source work acc payloadTemp accTemp []) := by
  simp [listFoldMachine, listFoldCfg, listFoldOutputState]

lemma listFold_pushAcc_step (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (b : β) (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀))
    (outputTemp : List β) :
    (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldCfg α β tm readInput writeOutput initialAcc
          (some (ListFoldLabel.pushAcc b)) state source work acc payloadTemp accTemp
          outputTemp) =
      some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.drainOutput) state source work (b :: acc) payloadTemp accTemp
        outputTemp) := by
  simp [listFoldMachine, listFoldCfg]
  congr
  funext k
  cases k <;> rfl

noncomputable def listFold_readOutput_runFromState (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (payload : List (tm.Γ tm.k₁)) (source : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀))
    (outputTemp : List β) :
    StateTransition.EvalsToInTime (listFoldMachine α β tm readInput writeOutput initialAcc).step
      (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readOutput) state source
        (Function.update work tm.k₁ payload) acc payloadTemp accTemp outputTemp)
      (some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.drainOutput) (ListFoldState.output none) source
        (Function.update work tm.k₁ []) acc payloadTemp accTemp
        ((payload.map writeOutput).reverse ++ outputTemp)))
      (2 * payload.length + 1) := by
  induction payload generalizing state outputTemp with
  | nil =>
      have hEmpty : (Function.update work tm.k₁ ([] : List (tm.Γ tm.k₁))) tm.k₁ = [] := by
        simp [Function.update]
      simpa using
        evalsToInTimeOne
          (listFold_readOutput_step_nil α β tm readInput writeOutput initialAcc state
            source (Function.update work tm.k₁ []) acc payloadTemp accTemp outputTemp
            hEmpty)
  | cons b payload ih =>
      let workTail := Function.update work tm.k₁ payload
      let outputSym := writeOutput b
      let c₀ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readOutput) state source
        (Function.update work tm.k₁ (b :: payload)) acc payloadTemp accTemp outputTemp
      let c₁ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.pushOutputTemp outputSym))
        (ListFoldState.output (some outputSym)) source workTail acc payloadTemp accTemp
        outputTemp
      let c₂ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readOutput) (ListFoldState.output (some outputSym))
        source workTail acc payloadTemp accTemp (outputSym :: outputTemp)
      let c₃ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.drainOutput) (ListFoldState.output none) source
        (Function.update work tm.k₁ []) acc payloadTemp accTemp
        ((payload.map writeOutput).reverse ++ outputSym :: outputTemp)
      have h₁ : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₀ (some c₁) 1 := by
        have hStep :=
          listFold_readOutput_step_cons α β tm readInput writeOutput initialAcc state b
            source workTail acc payloadTemp accTemp outputTemp
        exact evalsToInTimeOne (by
          simpa [c₀, c₁, workTail, outputSym, Function.update] using hStep)
      have h₂ : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (listFold_pushOutputTemp_step α β tm readInput writeOutput initialAcc
            (ListFoldState.output (some outputSym)) outputSym source workTail acc
            payloadTemp accTemp outputTemp)
      have h₁₂ : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans
          (listFoldMachine α β tm readInput writeOutput initialAcc).step 1 1 c₀ c₁
          (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₂ (some c₃)
          (2 * payload.length + 1) := by
        have hRaw :=
          ih (ListFoldState.output (some outputSym)) (outputSym :: outputTemp)
        simpa [c₂, c₃, workTail, outputSym, Function.update, List.map_cons,
          List.reverse_cons, List.append_assoc] using hRaw
      have hAll :=
        StateTransition.EvalsToInTime.trans
          (listFoldMachine α β tm readInput writeOutput initialAcc).step (1 + 1)
          (2 * payload.length + 1) c₀ c₂ (some c₃) h₁₂ hTail
      exact evalsToInTime_mono (by
        simpa [c₀, c₃, outputSym, List.map_cons, List.reverse_cons,
          List.append_assoc] using hAll) (by
        simp
        omega)

noncomputable def listFold_readOutput_run (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (payload : List (tm.Γ tm.k₁)) (source : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀))
    (outputTemp : List β) :
    StateTransition.EvalsToInTime (listFoldMachine α β tm readInput writeOutput initialAcc).step
      (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readOutput) (ListFoldState.output none) source
        (Function.update work tm.k₁ payload) acc payloadTemp accTemp outputTemp)
      (some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.drainOutput) (ListFoldState.output none) source
        (Function.update work tm.k₁ []) acc payloadTemp accTemp
        ((payload.map writeOutput).reverse ++ outputTemp)))
      (2 * payload.length + 1) :=
  listFold_readOutput_runFromState α β tm readInput writeOutput initialAcc
    (ListFoldState.output none) payload source work acc payloadTemp accTemp outputTemp

noncomputable def listFold_drainOutput_run (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀))
    (outputTemp : List β) :
    StateTransition.EvalsToInTime (listFoldMachine α β tm readInput writeOutput initialAcc).step
      (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.drainOutput) state source work acc payloadTemp accTemp outputTemp)
      (some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.reset (listFoldAllWorkStacks tm))) (ListFoldState.output none)
        source work (outputTemp.reverse ++ acc) payloadTemp accTemp []))
      (2 * outputTemp.length + 1) := by
  induction outputTemp generalizing state acc with
  | nil =>
      simpa using
        evalsToInTimeOne
          (listFold_drainOutput_step_nil α β tm readInput writeOutput initialAcc state
            source work acc payloadTemp accTemp)
  | cons b outputTemp ih =>
      let c₀ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.drainOutput) state source work acc payloadTemp accTemp
        (b :: outputTemp)
      let c₁ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.pushAcc b)) (ListFoldState.output (some b)) source work acc
        payloadTemp accTemp outputTemp
      let c₂ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.drainOutput) (ListFoldState.output (some b)) source work
        (b :: acc) payloadTemp accTemp outputTemp
      let c₃ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.reset (listFoldAllWorkStacks tm))) (ListFoldState.output none)
        source work ((b :: outputTemp).reverse ++ acc) payloadTemp accTemp []
      have h₁ : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (listFold_drainOutput_step_cons α β tm readInput writeOutput initialAcc state b
            source work acc payloadTemp accTemp outputTemp)
      have h₂ : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (listFold_pushAcc_step α β tm readInput writeOutput initialAcc
            (ListFoldState.output (some b)) b source work acc payloadTemp accTemp outputTemp)
      have h₁₂ : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans
          (listFoldMachine α β tm readInput writeOutput initialAcc).step 1 1 c₀ c₁
          (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₂ (some c₃)
          (2 * outputTemp.length + 1) := by
        have hRaw := ih (ListFoldState.output (some b)) (b :: acc)
        simpa [c₂, c₃, List.reverse_cons, List.append_assoc] using hRaw
      have hAll :=
        StateTransition.EvalsToInTime.trans
          (listFoldMachine α β tm readInput writeOutput initialAcc).step (1 + 1)
          (2 * outputTemp.length + 1) c₀ c₂ (some c₃) h₁₂ hTail
      exact evalsToInTime_mono (by simpa [c₀, c₃] using hAll) (by
        simp
        omega)

noncomputable def listFold_outputToAcc_run (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (payload : List (tm.Γ tm.k₁)) (source : List (Option α))
    (work : (k : tm.K) → List (tm.Γ k))
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀)) :
    StateTransition.EvalsToInTime (listFoldMachine α β tm readInput writeOutput initialAcc).step
      (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readOutput) (ListFoldState.output none) source
        (Function.update work tm.k₁ payload) acc payloadTemp accTemp [])
      (some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.reset (listFoldAllWorkStacks tm))) (ListFoldState.output none)
        source (Function.update work tm.k₁ []) (payload.map writeOutput ++ acc)
        payloadTemp accTemp []))
      (4 * payload.length + 2) := by
  let outputBlock := (payload.map writeOutput).reverse
  let c₀ := listFoldCfg α β tm readInput writeOutput initialAcc
    (some ListFoldLabel.readOutput) (ListFoldState.output none) source
    (Function.update work tm.k₁ payload) acc payloadTemp accTemp []
  let c₁ := listFoldCfg α β tm readInput writeOutput initialAcc
    (some ListFoldLabel.drainOutput) (ListFoldState.output none) source
    (Function.update work tm.k₁ []) acc payloadTemp accTemp outputBlock
  let c₂ := listFoldCfg α β tm readInput writeOutput initialAcc
    (some (ListFoldLabel.reset (listFoldAllWorkStacks tm))) (ListFoldState.output none)
    source (Function.update work tm.k₁ []) (payload.map writeOutput ++ acc)
    payloadTemp accTemp []
  have hRead : StateTransition.EvalsToInTime
      (listFoldMachine α β tm readInput writeOutput initialAcc).step c₀ (some c₁)
      (2 * payload.length + 1) := by
    simpa [c₀, c₁, outputBlock] using
      listFold_readOutput_run α β tm readInput writeOutput initialAcc payload source work
        acc payloadTemp accTemp []
  have hDrain : StateTransition.EvalsToInTime
      (listFoldMachine α β tm readInput writeOutput initialAcc).step c₁ (some c₂)
      (2 * outputBlock.length + 1) := by
    have hRaw :=
      listFold_drainOutput_run α β tm readInput writeOutput initialAcc
        (ListFoldState.output none) source (Function.update work tm.k₁ []) acc
        payloadTemp accTemp outputBlock
    simpa [c₁, c₂, outputBlock, List.reverse_reverse] using hRaw
  have hAll :=
    StateTransition.EvalsToInTime.trans
      (listFoldMachine α β tm readInput writeOutput initialAcc).step
      (2 * payload.length + 1) (2 * outputBlock.length + 1) c₀ c₁ (some c₂)
      hRead hDrain
  convert hAll using 1
  simp [outputBlock]
  omega

lemma listFold_reset_empty_step_done (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (remaining : Finset tm.K)
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀))
    (hRemaining : remaining.toList = []) :
    (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldCfg α β tm readInput writeOutput initialAcc
          (some (ListFoldLabel.reset remaining)) state source (listFoldEmptyWork tm)
          acc payloadTemp accTemp []) =
      some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput)
        source (listFoldEmptyWork tm) acc payloadTemp accTemp []) := by
  simp [listFoldMachine, listFoldCfg, hRemaining]

lemma listFold_reset_empty_step_cons (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (remaining : Finset tm.K)
    (k : tm.K) (tail : List tm.K)
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀))
    (hRemaining : remaining.toList = k :: tail) :
    (listFoldMachine α β tm readInput writeOutput initialAcc).step
        (listFoldCfg α β tm readInput writeOutput initialAcc
          (some (ListFoldLabel.reset remaining)) state source (listFoldEmptyWork tm)
          acc payloadTemp accTemp []) =
      some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.reset (remaining.erase k))) (ListFoldState.reset false)
        source (listFoldEmptyWork tm) acc payloadTemp accTemp []) := by
  simp [listFoldMachine, listFoldCfg, listFoldResetState, listFoldEmptyWork, hRemaining]

noncomputable def listFold_resetEmpty_run (α β : Type) (tm : Turing.FinTM2)
    [Fintype α] [Fintype β]
    (readInput : Option (β ⊕ α) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → β) (initialAcc : List β)
    (state : ListFoldState tm.σ (tm.Γ tm.k₀) β)
    (source : List (Option α)) (remaining : Finset tm.K)
    (acc : List β) (payloadTemp accTemp : List (tm.Γ tm.k₀)) :
    StateTransition.EvalsToInTime (listFoldMachine α β tm readInput writeOutput initialAcc).step
      (listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.reset remaining)) state source (listFoldEmptyWork tm)
        acc payloadTemp accTemp [])
      (some (listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput)
        source (listFoldEmptyWork tm) acc payloadTemp accTemp []))
      (remaining.card + 1) := by
  classical
  cases hRemaining : remaining.toList with
  | nil =>
      have hEmpty : remaining = ∅ := Finset.toList_eq_nil.mp hRemaining
      have hStep : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step
          (listFoldCfg α β tm readInput writeOutput initialAcc
            (some (ListFoldLabel.reset remaining)) state source (listFoldEmptyWork tm)
            acc payloadTemp accTemp [])
          (some (listFoldCfg α β tm readInput writeOutput initialAcc
            (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput)
            source (listFoldEmptyWork tm) acc payloadTemp accTemp []))
          1 :=
        evalsToInTimeOne
          (listFold_reset_empty_step_done α β tm readInput writeOutput initialAcc state
            source remaining acc payloadTemp accTemp hRemaining)
      simpa [hEmpty] using hStep
  | cons k tail =>
      have hMemList : k ∈ remaining.toList := by
        simp [hRemaining]
      have hMem : k ∈ remaining := by
        simpa [Finset.mem_toList] using hMemList
      let c₀ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.reset remaining)) state source (listFoldEmptyWork tm)
        acc payloadTemp accTemp []
      let c₁ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some (ListFoldLabel.reset (remaining.erase k))) (ListFoldState.reset false)
        source (listFoldEmptyWork tm) acc payloadTemp accTemp []
      let c₂ := listFoldCfg α β tm readInput writeOutput initialAcc
        (some ListFoldLabel.readSource) (ListFoldState.scan ListFoldScanState.endInput)
        source (listFoldEmptyWork tm) acc payloadTemp accTemp []
      have h₁ : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (listFold_reset_empty_step_cons α β tm readInput writeOutput initialAcc state
            source remaining k tail acc payloadTemp accTemp hRemaining)
      have hTail : StateTransition.EvalsToInTime
          (listFoldMachine α β tm readInput writeOutput initialAcc).step c₁ (some c₂)
          ((remaining.erase k).card + 1) := by
        simpa [c₁, c₂] using
          listFold_resetEmpty_run α β tm readInput writeOutput initialAcc
            (ListFoldState.reset false) source (remaining.erase k) acc payloadTemp accTemp
      have hAll :=
        StateTransition.EvalsToInTime.trans
          (listFoldMachine α β tm readInput writeOutput initialAcc).step 1
          ((remaining.erase k).card + 1) c₀ c₁ (some c₂) h₁ hTail
      simpa [c₀, c₁, c₂, Finset.card_erase_add_one hMem, Nat.add_assoc] using hAll
termination_by remaining.card
decreasing_by
  exact Finset.card_erase_lt_of_mem hMem

lemma listFoldEmptyWork_update_empty (tm : Turing.FinTM2) (k₀ : tm.K) :
    Function.update (listFoldEmptyWork tm) k₀ ([] : List (tm.Γ k₀)) =
      listFoldEmptyWork tm := by
  letI := tm.kDecidableEq
  funext k
  by_cases hk : k = k₀
  · subst k
    simp [Function.update, listFoldEmptyWork]
  · simp [Function.update, listFoldEmptyWork, hk]

end TM2Programs
end ComplexityReduction
