import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.ProductAndListPrimitives.Part1

namespace ComplexityReduction
namespace TM2Programs
open Turing.TM2.Stmt

def prodSymbolMaps_moveRight_run (α β γ : Type) [Fintype α] [Fintype β]
    [Fintype γ] (mapLeft : α → β) (mapRight : α → γ)
    (state : ProdSymbolMapsState β γ)
    (output : List (Option (β ⊕ γ))) (leftTemp : List β) (rightTemp : List γ) :
    StateTransition.EvalsToInTime (prodSymbolMapsMachine α β γ mapLeft mapRight).step
      (prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.moveRight
        state [] output leftTemp rightTemp)
      (some (prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.writeDelimiter
        ProdSymbolMapsState.done []
        ((rightTemp.reverse.map fun c => some (Sum.inr c)) ++ output) leftTemp []))
      (2 * rightTemp.length + 1) := by
  induction rightTemp generalizing state output with
  | nil =>
      simpa using
        evalsToInTimeOne
          (prodSymbolMaps_moveRight_step_nil α β γ mapLeft mapRight state output leftTemp)
  | cons c rightTemp ih =>
      let tm := prodSymbolMapsMachine α β γ mapLeft mapRight
      let c₀ := prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.moveRight
        state [] output leftTemp (c :: rightTemp)
      let c₁ := prodSymbolMapsCfg α β γ mapLeft mapRight
        (ProdSymbolMapsLabel.pushRightOutput c) (ProdSymbolMapsState.right c)
        [] output leftTemp rightTemp
      let c₂ := prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.moveRight
        (ProdSymbolMapsState.right c) [] (some (Sum.inr c) :: output) leftTemp rightTemp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (prodSymbolMaps_moveRight_step_cons α β γ mapLeft mapRight state output leftTemp
            c rightTemp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (prodSymbolMaps_pushRightOutput_step α β γ mapLeft mapRight
            (ProdSymbolMapsState.right c) c output leftTemp rightTemp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.writeDelimiter
            ProdSymbolMapsState.done []
            ((rightTemp.reverse.map fun c => some (Sum.inr c)) ++
              (some (Sum.inr c) :: output)) leftTemp []))
          (2 * rightTemp.length + 1) :=
        ih (ProdSymbolMapsState.right c) (some (Sum.inr c) :: output)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.map_append, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1)
          (2 * rightTemp.length + 1) c₀ c₂
          (some (prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.writeDelimiter
            ProdSymbolMapsState.done []
            ((rightTemp.reverse.map fun c => some (Sum.inr c)) ++
              (some (Sum.inr c) :: output)) leftTemp []))
          h₁₂ hTail

def prodSymbolMaps_writeDelimiter_run (α β γ : Type) [Fintype α] [Fintype β]
    [Fintype γ] (mapLeft : α → β) (mapRight : α → γ)
    (state : ProdSymbolMapsState β γ)
    (output : List (Option (β ⊕ γ))) (leftTemp : List β) :
    StateTransition.EvalsToInTime (prodSymbolMapsMachine α β γ mapLeft mapRight).step
      (prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.writeDelimiter
        state [] output leftTemp [])
      (some (prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.moveLeft
        state [] (none :: output) leftTemp [])) 1 :=
  evalsToInTimeOne
    (prodSymbolMaps_writeDelimiter_step α β γ mapLeft mapRight state output leftTemp)

def prodSymbolMaps_moveLeft_run (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
    (mapLeft : α → β) (mapRight : α → γ) (state : ProdSymbolMapsState β γ)
    (output : List (Option (β ⊕ γ))) (leftTemp : List β) :
    StateTransition.EvalsToInTime (prodSymbolMapsMachine α β γ mapLeft mapRight).step
      (prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.moveLeft
        state [] output leftTemp [])
      (some (prodSymbolMapsHalt α β γ mapLeft mapRight
        ((leftTemp.reverse.map fun b => some (Sum.inl b)) ++ output)))
      (2 * leftTemp.length + 1) := by
  induction leftTemp generalizing state output with
  | nil =>
      simpa using
        evalsToInTimeOne
          (prodSymbolMaps_moveLeft_step_nil α β γ mapLeft mapRight state output)
  | cons b leftTemp ih =>
      let tm := prodSymbolMapsMachine α β γ mapLeft mapRight
      let c₀ := prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.moveLeft
        state [] output (b :: leftTemp) []
      let c₁ := prodSymbolMapsCfg α β γ mapLeft mapRight
        (ProdSymbolMapsLabel.pushLeftOutput b) (ProdSymbolMapsState.left b)
        [] output leftTemp []
      let c₂ := prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.moveLeft
        (ProdSymbolMapsState.left b) [] (some (Sum.inl b) :: output) leftTemp []
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (prodSymbolMaps_moveLeft_step_cons α β γ mapLeft mapRight state output b leftTemp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (prodSymbolMaps_pushLeftOutput_step α β γ mapLeft mapRight
            (ProdSymbolMapsState.left b) b output leftTemp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (prodSymbolMapsHalt α β γ mapLeft mapRight
            ((leftTemp.reverse.map fun b => some (Sum.inl b)) ++
              (some (Sum.inl b) :: output))))
          (2 * leftTemp.length + 1) :=
        ih (ProdSymbolMapsState.left b) (some (Sum.inl b) :: output)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.map_append, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1)
          (2 * leftTemp.length + 1) c₀ c₂
          (some (prodSymbolMapsHalt α β γ mapLeft mapRight
            ((leftTemp.reverse.map fun b => some (Sum.inl b)) ++
              (some (Sum.inl b) :: output))))
          h₁₂ hTail

/-- The product symbol-map program computes the expected product encoding. -/
def prodSymbolMaps_outputs (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
    (mapLeft : α → β) (mapRight : α → γ) (input : List α) :
    Turing.TM2OutputsInTime (prodSymbolMapsMachine α β γ mapLeft mapRight)
      input
      (some
        (input.map (fun a => some (Sum.inl (mapLeft a) : β ⊕ γ)) ++
          [none] ++
          input.map (fun a => some (Sum.inr (mapRight a) : β ⊕ γ))))
      (7 * input.length + 4) := by
  let tm := prodSymbolMapsMachine α β γ mapLeft mapRight
  let left := input.map (fun a => some (Sum.inl (mapLeft a) : β ⊕ γ))
  let right := input.map (fun a => some (Sum.inr (mapRight a) : β ⊕ γ))
  let leftRaw := input.map mapLeft
  let rightRaw := input.map mapRight
  let mid₁ := prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.moveRight
    ProdSymbolMapsState.done [] [] leftRaw.reverse rightRaw.reverse
  let mid₂ := prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.writeDelimiter
    ProdSymbolMapsState.done [] right leftRaw.reverse []
  let mid₃ := prodSymbolMapsCfg α β γ mapLeft mapRight ProdSymbolMapsLabel.moveLeft
    ProdSymbolMapsState.done [] (none :: right) leftRaw.reverse []
  let done := prodSymbolMapsHalt α β γ mapLeft mapRight (left ++ [none] ++ right)
  have hRead : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some mid₁) (3 * input.length + 1) := by
    simpa [tm, mid₁, leftRaw, rightRaw, initList_prodSymbolMapsMachine] using
      prodSymbolMaps_readInput_run α β γ mapLeft mapRight ProdSymbolMapsState.done
        input [] [] []
  have hRight : StateTransition.EvalsToInTime tm.step mid₁
      (some mid₂) (2 * input.length + 1) := by
    simpa [tm, mid₁, mid₂, right, rightRaw, leftRaw, List.length_reverse, List.map_map,
      Function.comp_def] using
      prodSymbolMaps_moveRight_run α β γ mapLeft mapRight ProdSymbolMapsState.done
        [] leftRaw.reverse rightRaw.reverse
  have hDelim : StateTransition.EvalsToInTime tm.step mid₂ (some mid₃) 1 := by
    simpa [tm, mid₂, mid₃] using
      prodSymbolMaps_writeDelimiter_run α β γ mapLeft mapRight ProdSymbolMapsState.done
        right leftRaw.reverse
  have hLeft : StateTransition.EvalsToInTime tm.step mid₃
      (some done) (2 * input.length + 1) := by
    simpa [tm, mid₃, done, left, right, leftRaw, List.length_reverse, List.map_map,
      List.append_assoc, Function.comp_def] using
      prodSymbolMaps_moveLeft_run α β γ mapLeft mapRight ProdSymbolMapsState.done
        (none :: right) leftRaw.reverse
  have hReadRight : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some mid₂) ((2 * input.length + 1) + (3 * input.length + 1)) :=
    StateTransition.EvalsToInTime.trans tm.step (3 * input.length + 1)
      (2 * input.length + 1) (Turing.initList tm input) mid₁ (some mid₂)
      hRead hRight
  have hReadRightDelim : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some mid₃) (1 + ((2 * input.length + 1) + (3 * input.length + 1))) :=
    StateTransition.EvalsToInTime.trans tm.step
      ((2 * input.length + 1) + (3 * input.length + 1)) 1
      (Turing.initList tm input) mid₂ (some mid₃) hReadRight hDelim
  have hAll : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some done)
      ((2 * input.length + 1) +
        (1 + ((2 * input.length + 1) + (3 * input.length + 1)))) :=
    StateTransition.EvalsToInTime.trans tm.step
      (1 + ((2 * input.length + 1) + (3 * input.length + 1)))
      (2 * input.length + 1)
      (Turing.initList tm input) mid₃ (some done) hReadRightDelim hLeft
  change StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
    (some (Turing.haltList tm (left ++ [none] ++ right))) (7 * input.length + 4)
  rw [haltList_prodSymbolMapsMachine]
  convert hAll using 1
  omega

/--
TM2 polynomial-time computation of a structural product map whose two component
encodings are both obtained by fixed symbol maps from the same input encoding.

This is a direct `prod_mk` structural subcase; it does not prove arbitrary
product pairing closure.
-/
noncomputable def prodSymbolMapsComputableInPolyTime
    (X Y Z : EncodedType) (f : X.Carrier → Y.Carrier) (g : X.Carrier → Z.Carrier)
    (mapLeft : X.Symbol → Y.Symbol) (mapRight : X.Symbol → Z.Symbol)
    (hf : ∀ x, Y.encode (f x) = (X.encode x).map mapLeft)
    (hg : ∀ x, Z.encode (g x) = (X.encode x).map mapRight) :
    Turing.TM2ComputableInPolyTime X.encode (EncodedType.prod Y Z).encode
      (fun x : X.Carrier => (f x, g x)) where
  tm := prodSymbolMapsMachine X.Symbol Y.Symbol Z.Symbol mapLeft mapRight
  inputAlphabet := Equiv.refl X.Symbol
  outputAlphabet := Equiv.refl (Option (Y.Symbol ⊕ Z.Symbol))
  time := 7 * Polynomial.X + 4
  outputsFun x := by
    convert
      prodSymbolMaps_outputs X.Symbol Y.Symbol Z.Symbol mapLeft mapRight (X.encode x) using 1
    · change List.map id (X.encode x) = X.encode x
      simp
    · change
        some (List.map id ((EncodedType.prod Y Z).encode (f x, g x))) =
          some
            ((X.encode x).map
              (fun s : X.Symbol => some (Sum.inl (mapLeft s) : Y.Symbol ⊕ Z.Symbol)) ++
              [none] ++
              (X.encode x).map
                (fun s : X.Symbol => some (Sum.inr (mapRight s) : Y.Symbol ⊕ Z.Symbol)))
      simp [EncodedType.prod, hf x, hg x, List.map_map, Function.comp_def]
    · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]

/-- Stack indices for the filter-map program used by product projections. -/
inductive FMStack where
  | input
  | output
  | temp
  deriving DecidableEq, Fintype

/-- Stack alphabets for the generic filter-map program. -/
abbrev fmAlphabet (α β : Type) : FMStack → Type
  | FMStack.input => α
  | FMStack.output => β
  | FMStack.temp => β

/-- Internal state for the generic filter-map program. -/
inductive FMState (β : Type) where
  | emit (b : β)
  | skip
  | done
  deriving DecidableEq, Fintype

namespace FMState

def isEmit {β : Type} : FMState β → Bool
  | emit _ => true
  | _ => false

def isDone {β : Type} : FMState β → Bool
  | done => true
  | _ => false

end FMState

/-- Control labels for the generic filter-map program. -/
inductive FMLabel (β : Type) where
  | readInput
  | pushTemp (b : β)
  | moveTemp
  | pushOutput (b : β)
  deriving DecidableEq, Fintype

/--
A concrete TM2 program for `input ↦ input.filterMap keep`.

The program scans and clears the input stack, pushes kept symbols to a temporary
stack, then moves the temporary stack to output to restore the original order.
-/
def filterMapMachine (α β : Type) [Fintype α] [Fintype β] (keep : α → Option β) :
    Turing.FinTM2 where
  K := FMStack
  k₀ := FMStack.input
  k₁ := FMStack.output
  Γ := fmAlphabet α β
  Λ := FMLabel β
  main := FMLabel.readInput
  σ := FMState β
  initialState := FMState.done
  Γk₀Fin := by
    dsimp [fmAlphabet]
    infer_instance
  m
    | FMLabel.readInput =>
        pop FMStack.input
          (fun _ head =>
            match head with
            | none => FMState.done
            | some a =>
                match keep a with
                | some b => FMState.emit b
                | none => FMState.skip)
          (branch FMState.isEmit
            (goto fun state =>
              match state with
              | FMState.emit b => FMLabel.pushTemp b
              | _ => FMLabel.readInput)
            (branch FMState.isDone
              (goto fun _ => FMLabel.moveTemp)
              (goto fun _ => FMLabel.readInput)))
    | FMLabel.pushTemp b =>
        push FMStack.temp (fun _ => b) (goto fun _ => FMLabel.readInput)
    | FMLabel.moveTemp =>
        pop FMStack.temp
          (fun _ head =>
            match head with
            | some b => FMState.emit b
            | none => FMState.done)
          (branch FMState.isEmit
            (goto fun state =>
              match state with
              | FMState.emit b => FMLabel.pushOutput b
              | _ => FMLabel.moveTemp)
            (load (fun _ => FMState.done) halt))
    | FMLabel.pushOutput b =>
        push FMStack.output (fun _ => b) (goto fun _ => FMLabel.moveTemp)

def fmCfg (α β : Type) [Fintype α] [Fintype β] (keep : α → Option β)
    (label : FMLabel β) (state : FMState β)
    (input : List α) (output temp : List β) :
    (filterMapMachine α β keep).Cfg where
  l := some label
  var := state
  stk
    | FMStack.input => input
    | FMStack.output => output
    | FMStack.temp => temp

def fmHalt (α β : Type) [Fintype α] [Fintype β] (keep : α → Option β)
    (output : List β) :
    (filterMapMachine α β keep).Cfg where
  l := none
  var := FMState.done
  stk
    | FMStack.input => []
    | FMStack.output => output
    | FMStack.temp => []

lemma readInput_step_emit (α β : Type) [Fintype α] [Fintype β]
    (keep : α → Option β) (state : FMState β)
    (a : α) (b : β) (input : List α) (output temp : List β)
    (hkeep : keep a = some b) :
    (filterMapMachine α β keep).step
        (fmCfg α β keep FMLabel.readInput state (a :: input) output temp) =
      some (fmCfg α β keep (FMLabel.pushTemp b) (FMState.emit b) input output temp) := by
  simp [filterMapMachine, fmCfg, hkeep, FMState.isEmit]
  congr
  funext k
  cases k <;> rfl

lemma readInput_step_skip (α β : Type) [Fintype α] [Fintype β]
    (keep : α → Option β) (state : FMState β)
    (a : α) (input : List α) (output temp : List β)
    (hkeep : keep a = none) :
    (filterMapMachine α β keep).step
        (fmCfg α β keep FMLabel.readInput state (a :: input) output temp) =
      some (fmCfg α β keep FMLabel.readInput FMState.skip input output temp) := by
  simp [filterMapMachine, fmCfg, hkeep, FMState.isEmit, FMState.isDone]
  congr
  funext k
  cases k <;> rfl

lemma readInput_step_nil (α β : Type) [Fintype α] [Fintype β]
    (keep : α → Option β) (state : FMState β) (output temp : List β) :
    (filterMapMachine α β keep).step
        (fmCfg α β keep FMLabel.readInput state [] output temp) =
      some (fmCfg α β keep FMLabel.moveTemp FMState.done [] output temp) := by
  simp [filterMapMachine, fmCfg, FMState.isEmit, FMState.isDone]
  congr

lemma pushTemp_step (α β : Type) [Fintype α] [Fintype β]
    (keep : α → Option β) (state : FMState β)
    (b : β) (input : List α) (output temp : List β) :
    (filterMapMachine α β keep).step
        (fmCfg α β keep (FMLabel.pushTemp b) state input output temp) =
      some (fmCfg α β keep FMLabel.readInput state input output (b :: temp)) := by
  simp [filterMapMachine, fmCfg]
  congr
  funext k
  cases k <;> rfl

lemma moveTemp_step_cons (α β : Type) [Fintype α] [Fintype β]
    (keep : α → Option β) (state : FMState β)
    (input : List α) (output : List β) (b : β) (temp : List β) :
    (filterMapMachine α β keep).step
        (fmCfg α β keep FMLabel.moveTemp state input output (b :: temp)) =
      some (fmCfg α β keep (FMLabel.pushOutput b) (FMState.emit b) input output temp) := by
  simp [filterMapMachine, fmCfg, FMState.isEmit]
  congr
  funext k
  cases k <;> rfl

lemma moveTemp_step_nil (α β : Type) [Fintype α] [Fintype β]
    (keep : α → Option β) (state : FMState β) (output : List β) :
    (filterMapMachine α β keep).step
        (fmCfg α β keep FMLabel.moveTemp state [] output []) =
      some (fmHalt α β keep output) := by
  simp [filterMapMachine, fmCfg, fmHalt, FMState.isEmit]
  congr

lemma pushOutput_step (α β : Type) [Fintype α] [Fintype β]
    (keep : α → Option β) (state : FMState β)
    (input : List α) (output : List β) (b : β) (temp : List β) :
    (filterMapMachine α β keep).step
        (fmCfg α β keep (FMLabel.pushOutput b) state input output temp) =
      some (fmCfg α β keep FMLabel.moveTemp state input (b :: output) temp) := by
  simp [filterMapMachine, fmCfg]
  congr
  funext k
  cases k <;> rfl

lemma initList_filterMapMachine (α β : Type) [Fintype α] [Fintype β]
    (keep : α → Option β) (input : List α) :
    Turing.initList (filterMapMachine α β keep) input =
      fmCfg α β keep FMLabel.readInput FMState.done input [] [] := by
  simp [filterMapMachine, fmCfg, Turing.initList]
  congr
  funext k
  cases k <;> rfl

lemma haltList_filterMapMachine (α β : Type) [Fintype α] [Fintype β]
    (keep : α → Option β) (output : List β) :
    Turing.haltList (filterMapMachine α β keep) output =
      fmHalt α β keep output := by
  simp [filterMapMachine, fmHalt, Turing.haltList]
  congr
  funext k
  cases k <;> rfl

theorem filterMap_length_le {α β : Type} (keep : α → Option β) :
    ∀ input : List α, (input.filterMap keep).length ≤ input.length
  | [] => by simp
  | a :: input => by
      have ih := filterMap_length_le keep input
      cases h : keep a with
      | none =>
          exact Nat.le_trans (by simpa [h] using ih) (Nat.le_succ _)
      | some _ =>
          simpa [h] using Nat.succ_le_succ ih

def readInput_run (α β : Type) [Fintype α] [Fintype β]
    (keep : α → Option β) (state : FMState β)
    (input : List α) (output temp : List β) :
    StateTransition.EvalsToInTime (filterMapMachine α β keep).step
      (fmCfg α β keep FMLabel.readInput state input output temp)
      (some (fmCfg α β keep FMLabel.moveTemp FMState.done [] output
        ((input.filterMap keep).reverse ++ temp)))
      (input.length + (input.filterMap keep).length + 1) := by
  induction input generalizing state temp with
  | nil =>
      simpa using
        evalsToInTimeOne
          (readInput_step_nil α β keep state output temp)
  | cons a input ih =>
      cases hkeep : keep a with
      | none =>
          let tm := filterMapMachine α β keep
          let c₀ := fmCfg α β keep FMLabel.readInput state (a :: input) output temp
          let c₁ := fmCfg α β keep FMLabel.readInput FMState.skip input output temp
          have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
            evalsToInTimeOne
              (readInput_step_skip α β keep state a input output temp hkeep)
          have hTail : StateTransition.EvalsToInTime tm.step c₁
              (some (fmCfg α β keep FMLabel.moveTemp FMState.done [] output
                ((input.filterMap keep).reverse ++ temp)))
              (input.length + (input.filterMap keep).length + 1) := by
            simpa [c₁] using ih FMState.skip temp
          simpa [tm, c₀, c₁, List.filterMap_cons, hkeep, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using
            StateTransition.EvalsToInTime.trans tm.step 1
              (input.length + (input.filterMap keep).length + 1)
              c₀ c₁
              (some (fmCfg α β keep FMLabel.moveTemp FMState.done [] output
                ((input.filterMap keep).reverse ++ temp)))
              h₁ hTail
      | some b =>
          let tm := filterMapMachine α β keep
          let c₀ := fmCfg α β keep FMLabel.readInput state (a :: input) output temp
          let c₁ := fmCfg α β keep (FMLabel.pushTemp b) (FMState.emit b) input output temp
          let c₂ := fmCfg α β keep FMLabel.readInput (FMState.emit b) input output
            (b :: temp)
          have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
            evalsToInTimeOne
              (readInput_step_emit α β keep state a b input output temp hkeep)
          have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
            evalsToInTimeOne
              (pushTemp_step α β keep (FMState.emit b) b input output temp)
          have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
            StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
          have hTail : StateTransition.EvalsToInTime tm.step c₂
              (some (fmCfg α β keep FMLabel.moveTemp FMState.done [] output
                ((input.filterMap keep).reverse ++ (b :: temp))))
              (input.length + (input.filterMap keep).length + 1) := by
            simpa [c₂] using ih (FMState.emit b) (b :: temp)
          simpa [tm, c₀, c₁, c₂, List.filterMap_cons, hkeep, List.reverse_cons,
            List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            StateTransition.EvalsToInTime.trans tm.step (1 + 1)
              (input.length + (input.filterMap keep).length + 1)
              c₀ c₂
              (some (fmCfg α β keep FMLabel.moveTemp FMState.done [] output
                ((input.filterMap keep).reverse ++ (b :: temp))))
              h₁₂ hTail

def moveTemp_run (α β : Type) [Fintype α] [Fintype β]
    (keep : α → Option β) (state : FMState β)
    (output temp : List β) :
    StateTransition.EvalsToInTime (filterMapMachine α β keep).step
      (fmCfg α β keep FMLabel.moveTemp state [] output temp)
      (some (fmHalt α β keep (temp.reverse ++ output)))
      (2 * temp.length + 1) := by
  induction temp generalizing state output with
  | nil =>
      simpa using
        evalsToInTimeOne
          (moveTemp_step_nil α β keep state output)
  | cons b temp ih =>
      let tm := filterMapMachine α β keep
      let c₀ := fmCfg α β keep FMLabel.moveTemp state [] output (b :: temp)
      let c₁ := fmCfg α β keep (FMLabel.pushOutput b) (FMState.emit b) [] output temp
      let c₂ := fmCfg α β keep FMLabel.moveTemp (FMState.emit b) [] (b :: output) temp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (moveTemp_step_cons α β keep state [] output b temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (pushOutput_step α β keep (FMState.emit b) [] output b temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some (fmHalt α β keep (temp.reverse ++ (b :: output))))
          (2 * temp.length + 1) := by
        simpa [c₂] using ih (FMState.emit b) (b :: output)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * temp.length + 1)
          c₀ c₂ (some (fmHalt α β keep (temp.reverse ++ (b :: output)))) h₁₂ hTail

/-- The filter-map program computes `input.filterMap keep` in linear TM2 time. -/
def filterMap_outputs (α β : Type) [Fintype α] [Fintype β]
    (keep : α → Option β) (input : List α) :
    Turing.TM2OutputsInTime (filterMapMachine α β keep)
      input (some (input.filterMap keep)) (4 * input.length + 2) := by
  let tm := filterMapMachine α β keep
  let kept := input.filterMap keep
  let mid := fmCfg α β keep FMLabel.moveTemp FMState.done [] [] kept.reverse
  let done := fmHalt α β keep kept
  have hRead : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some mid) (input.length + kept.length + 1) := by
    simpa [tm, mid, kept, initList_filterMapMachine] using
      readInput_run α β keep FMState.done input [] []
  have hMove : StateTransition.EvalsToInTime tm.step mid
      (some done) (2 * kept.length + 1) := by
    simpa [tm, mid, done, kept, List.length_reverse] using
      moveTemp_run α β keep FMState.done [] kept.reverse
  have hAll : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some done) ((2 * kept.length + 1) + (input.length + kept.length + 1)) :=
    StateTransition.EvalsToInTime.trans tm.step (input.length + kept.length + 1)
      (2 * kept.length + 1) (Turing.initList tm input) mid (some done) hRead hMove
  change StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
    (some (Turing.haltList tm kept)) (4 * input.length + 2)
  rw [haltList_filterMapMachine]
  refine
    { steps := hAll.steps
      evals_in_steps := hAll.evals_in_steps
      steps_le_m := ?_ }
  have hkept : kept.length ≤ input.length := by
    simpa [kept] using filterMap_length_le keep input
  have hSteps := hAll.steps_le_m
  omega

def fstKeep {α β : Type} : Option (α ⊕ β) → Option α
  | some (Sum.inl a) => some a
  | _ => none

def sndKeep {α β : Type} : Option (α ⊕ β) → Option β
  | some (Sum.inr b) => some b
  | _ => none

lemma fstKeep_right_symbols {α β : Type} (ys : List β) :
    ((none :: (ys.map fun s => some (Sum.inr s))).filterMap
      (fstKeep : Option (α ⊕ β) → Option α)) = [] := by
  induction ys <;> simp [fstKeep, *]

lemma sndKeep_right_symbols {α β : Type} (ys : List β) :
    ((none :: (ys.map fun s => some (Sum.inr s))).filterMap
      (sndKeep : Option (α ⊕ β) → Option β)) = ys := by
  induction ys <;> simp [sndKeep, *]

/-- TM2 polynomial-time computation of the first product projection. -/
noncomputable def fstComputableInPolyTime (X Y : EncodedType) :
    Turing.TM2ComputableInPolyTime
      (EncodedType.prod X Y).encode X.encode (@Prod.fst X.Carrier Y.Carrier) where
  tm := filterMapMachine (Option (X.Symbol ⊕ Y.Symbol)) X.Symbol fstKeep
  inputAlphabet := Equiv.cast rfl
  outputAlphabet := Equiv.cast rfl
  time := 4 * Polynomial.X + 2
  outputsFun p := by
    convert
      filterMap_outputs (Option (X.Symbol ⊕ Y.Symbol)) X.Symbol fstKeep
        (List.map (Equiv.cast rfl).invFun ((EncodedType.prod X Y).encode p)) using 1
    · congr
      simp [EncodedType.prod]
      have hFirst :
          List.filterMap
              (fun x : X.Symbol => fstKeep (some (Sum.inl x : X.Symbol ⊕ Y.Symbol)))
              (X.encode p.1) =
            X.encode p.1 := by
        induction X.encode p.1 <;> simp [fstKeep, *]
      have hRight :
          List.filterMap (fstKeep : Option (X.Symbol ⊕ Y.Symbol) → Option X.Symbol)
              (none :: List.map (fun s : Y.Symbol => some (Sum.inr s)) (Y.encode p.2)) =
            [] :=
        fstKeep_right_symbols (α := X.Symbol) (β := Y.Symbol) (Y.encode p.2)
      have hMap :
          List.map (Equiv.cast rfl).invFun (X.encode p.1) = X.encode p.1 := by
        simp
      have hRhs :
          List.filterMap
                (fun x : X.Symbol => fstKeep (some (Sum.inl x : X.Symbol ⊕ Y.Symbol)))
                (X.encode p.1) ++
              List.filterMap (fstKeep : Option (X.Symbol ⊕ Y.Symbol) → Option X.Symbol)
                (none :: List.map (fun s : Y.Symbol => some (Sum.inr s)) (Y.encode p.2)) =
            X.encode p.1 :=
        (congrArg₂ List.append hFirst hRight).trans (List.append_nil _)
      exact hMap.trans hRhs.symm
    · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
      rfl

/-- TM2 polynomial-time computation of the second product projection. -/
noncomputable def sndComputableInPolyTime (X Y : EncodedType) :
    Turing.TM2ComputableInPolyTime
      (EncodedType.prod X Y).encode Y.encode (@Prod.snd X.Carrier Y.Carrier) where
  tm := filterMapMachine (Option (X.Symbol ⊕ Y.Symbol)) Y.Symbol sndKeep
  inputAlphabet := Equiv.cast rfl
  outputAlphabet := Equiv.cast rfl
  time := 4 * Polynomial.X + 2
  outputsFun p := by
    convert
      filterMap_outputs (Option (X.Symbol ⊕ Y.Symbol)) Y.Symbol sndKeep
        (List.map (Equiv.cast rfl).invFun ((EncodedType.prod X Y).encode p)) using 1
    · congr
      simp [EncodedType.prod]
      have hLeft :
          List.filterMap
              (fun x : X.Symbol => sndKeep (some (Sum.inl x : X.Symbol ⊕ Y.Symbol)))
              (X.encode p.1) =
            [] := by
        induction X.encode p.1 <;> simp [sndKeep, *]
      have hRight :
          List.filterMap (sndKeep : Option (X.Symbol ⊕ Y.Symbol) → Option Y.Symbol)
              (none :: List.map (fun s : Y.Symbol => some (Sum.inr s)) (Y.encode p.2)) =
            Y.encode p.2 :=
        sndKeep_right_symbols (α := X.Symbol) (β := Y.Symbol) (Y.encode p.2)
      have hMap :
          List.map (Equiv.cast rfl).invFun (Y.encode p.2) = Y.encode p.2 := by
        simp
      have hRhs :
          List.filterMap
                (fun x : X.Symbol => sndKeep (some (Sum.inl x : X.Symbol ⊕ Y.Symbol)))
                (X.encode p.1) ++
              List.filterMap (sndKeep : Option (X.Symbol ⊕ Y.Symbol) → Option Y.Symbol)
                (none :: List.map (fun s : Y.Symbol => some (Sum.inr s)) (Y.encode p.2)) =
            Y.encode p.2 :=
        (congrArg₂ List.append hLeft hRight).trans (List.nil_append _)
      exact hMap.trans hRhs.symm
    · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
      rfl

/-- Keep both encoded-list payload sides while dropping the product delimiter. -/
def listAppendKeep {α : Type} : Option (Option α ⊕ Option α) → Option (Option α)
  | some (Sum.inl s) => some s
  | some (Sum.inr s) => some s
  | none => none

lemma list_append_encode_filterMap (X : EncodedType)
    (p : List X.Carrier × List X.Carrier) :
    (List.map (Equiv.cast rfl).invFun
        ((EncodedType.prod (EncodedType.list X) (EncodedType.list X)).encode p)).filterMap
      (listAppendKeep : Option (Option X.Symbol ⊕ Option X.Symbol) → Option (Option X.Symbol)) =
    (EncodedType.list X).encode (p.1 ++ p.2) := by
  simp [EncodedType.prod, EncodedType.list, listAppendKeep, List.flatMap_append]

/-- TM2 polynomial-time computation of encoded-list append. -/
noncomputable def listAppendComputableInPolyTime (X : EncodedType) :
    Turing.TM2ComputableInPolyTime
      (EncodedType.prod (EncodedType.list X) (EncodedType.list X)).encode
      (EncodedType.list X).encode
      (fun p : List X.Carrier × List X.Carrier => p.1 ++ p.2) where
  tm :=
    filterMapMachine
      (Option (Option X.Symbol ⊕ Option X.Symbol))
      (Option X.Symbol)
      listAppendKeep
  inputAlphabet := Equiv.cast rfl
  outputAlphabet := Equiv.cast rfl
  time := 4 * Polynomial.X + 2
  outputsFun p := by
    rcases p with ⟨xs, ys⟩
    change List X.Carrier at xs
    change List X.Carrier at ys
    convert
      filterMap_outputs
        (Option (Option X.Symbol ⊕ Option X.Symbol))
        (Option X.Symbol)
        listAppendKeep
        (List.map (Equiv.cast rfl).invFun
          ((EncodedType.prod (EncodedType.list X) (EncodedType.list X)).encode (xs, ys))) using 1
    · simp
      calc
        List.map (Equiv.cast rfl).invFun ((EncodedType.list X).encode (xs ++ ys)) =
            (EncodedType.list X).encode (xs ++ ys) := by
          simp
        _ =
            (List.map (Equiv.cast rfl).invFun
              ((EncodedType.prod (EncodedType.list X) (EncodedType.list X)).encode
                (xs, ys))).filterMap
                listAppendKeep :=
          (list_append_encode_filterMap X (xs, ys)).symm
        _ =
            ((EncodedType.prod (EncodedType.list X) (EncodedType.list X)).encode
              (xs, ys)).filterMap
              listAppendKeep := by
          simp
    · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
      rfl

/-- Keep exactly encoded-list delimiters while dropping all source payload symbols. -/
def listConstEmptyKeep {α β : Type} : Option α → Option (Option β)
  | some _ => none
  | none => some none

lemma filterMap_listConstEmptyKeep_element {α β : Type} (symbols : List α) :
    ((symbols.map some).filterMap
      (listConstEmptyKeep : Option α → Option (Option β))) = [] := by
  induction symbols <;> simp [listConstEmptyKeep, *]

lemma listConstEmpty_filterMap_source_raw (X Y : EncodedType) (xs : List X.Carrier) :
    ((EncodedType.list X).encode xs).filterMap
      (listConstEmptyKeep : Option X.Symbol → Option (Option Y.Symbol)) =
    List.replicate xs.length (none : Option Y.Symbol) := by
  induction xs with
  | nil =>
      simp [EncodedType.list]
  | cons x xs ih =>
      have ih' :
          List.filterMap
              (listConstEmptyKeep : Option X.Symbol → Option (Option Y.Symbol))
              (xs.flatMap fun x => (X.encode x).map some ++ [none]) =
            List.replicate xs.length (none : Option Y.Symbol) := by
        simpa [EncodedType.list] using ih
      change
        List.filterMap
              (listConstEmptyKeep : Option X.Symbol → Option (Option Y.Symbol))
              (((X.encode x).map some ++ [none]) ++
                xs.flatMap fun x => (X.encode x).map some ++ [none]) =
            List.replicate (xs.length + 1) (none : Option Y.Symbol)
      rw [List.filterMap_append, ih']
      simp [List.filterMap_append, listConstEmptyKeep, List.replicate_succ]

lemma listConstEmpty_filterMap_source (X Y : EncodedType) (xs : List X.Carrier) :
    (List.map (Equiv.cast rfl).invFun ((EncodedType.list X).encode xs)).filterMap
      (listConstEmptyKeep : Option X.Symbol → Option (Option Y.Symbol)) =
    List.replicate xs.length (none : Option Y.Symbol) := by
  simpa using listConstEmpty_filterMap_source_raw X Y xs

lemma listConstEmpty_target_replicate_encode (Y : EncodedType) (y : Y.Carrier)
    (hy : Y.encode y = []) :
    ∀ n : Nat, (EncodedType.list Y).encode (List.replicate n y) =
      List.replicate n (none : Option Y.Symbol)
  | 0 => by
      simp [EncodedType.list]
  | Nat.succ n => by
      have hTail :
          (List.replicate n y).flatMap (fun x => (Y.encode x).map some ++ [none]) =
            List.replicate n (none : Option Y.Symbol) := by
        simpa [EncodedType.list] using
          listConstEmpty_target_replicate_encode Y y hy n
      change
        ((Y.encode y).map some ++ [none]) ++
            (List.replicate n y).flatMap (fun x => (Y.encode x).map some ++ [none]) =
          List.replicate (n + 1) (none : Option Y.Symbol)
      rw [hTail]
      simp [hy, List.replicate_succ]

lemma listConstEmpty_target_encode (X Y : EncodedType) (y : Y.Carrier)
    (hy : Y.encode y = []) (xs : List X.Carrier) :
    (EncodedType.list Y).encode (xs.map fun _ => y) =
      List.replicate xs.length (none : Option Y.Symbol) := by
  have hMap : xs.map (fun _ => y) = List.replicate xs.length y := by
    simp [Function.const_def]
  rw [hMap]
  exact listConstEmpty_target_replicate_encode Y y hy xs.length

lemma listEmptyOutput_target_encode (X Y : EncodedType) (f : X.Carrier → Y.Carrier)
    (hf : ∀ x, Y.encode (f x) = []) :
    ∀ xs : List X.Carrier,
      (EncodedType.list Y).encode (xs.map f) =
        List.replicate xs.length (none : Option Y.Symbol)
  | [] => by
      simp [EncodedType.list]
  | x :: xs => by
      have hTail :
          (xs.map f).flatMap (fun y => (Y.encode y).map some ++ [none]) =
            List.replicate xs.length (none : Option Y.Symbol) := by
        simpa [EncodedType.list] using listEmptyOutput_target_encode X Y f hf xs
      change
        ((Y.encode (f x)).map some ++ [none]) ++
            (xs.map f).flatMap (fun y => (Y.encode y).map some ++ [none]) =
          List.replicate (xs.length + 1) (none : Option Y.Symbol)
      rw [hTail]
      simp [hf x, List.replicate_succ]

lemma listEncode_length_ge_length (X : EncodedType) :
    ∀ xs : List X.Carrier, xs.length ≤ ((EncodedType.list X).encode xs).length
  | [] => by simp [EncodedType.list]
  | _ :: xs => by
      have ih := listEncode_length_ge_length X xs
      simp [EncodedType.list]
      omega

lemma listConstEmpty_filterMap_encode (X Y : EncodedType) (y : Y.Carrier)
    (hy : Y.encode y = []) (xs : List X.Carrier) :
    (List.map (Equiv.cast rfl).invFun ((EncodedType.list X).encode xs)).filterMap
      (listConstEmptyKeep : Option X.Symbol → Option (Option Y.Symbol)) =
    (EncodedType.list Y).encode (xs.map fun _ => y) :=
  (listConstEmpty_filterMap_source X Y xs).trans
    (listConstEmpty_target_encode X Y y hy xs).symm

lemma listEmptyOutput_filterMap_encode (X Y : EncodedType)
    (f : X.Carrier → Y.Carrier) (hf : ∀ x, Y.encode (f x) = [])
    (xs : List X.Carrier) :
    (List.map (Equiv.cast rfl).invFun ((EncodedType.list X).encode xs)).filterMap
      (listConstEmptyKeep : Option X.Symbol → Option (Option Y.Symbol)) =
    (EncodedType.list Y).encode (xs.map f) :=
  (listConstEmpty_filterMap_source X Y xs).trans
    (listEmptyOutput_target_encode X Y f hf xs).symm

/--
TM2 polynomial-time computation of list-mapping to a fixed value whose encoding
is empty.  This is a structural subcase of list-map, not the arbitrary
`list_map_map` closure theorem.
-/
noncomputable def listConstEmptyComputableInPolyTime
    (X Y : EncodedType) (y : Y.Carrier) (hy : Y.encode y = []) :
    Turing.TM2ComputableInPolyTime
      (EncodedType.list X).encode
      (EncodedType.list Y).encode
      (fun xs : List X.Carrier => xs.map fun _ => y) where
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
        List.map (Equiv.cast rfl).invFun
            ((EncodedType.list Y).encode (List.replicate xs.length y)) =
            (EncodedType.list Y).encode (List.replicate xs.length y) := by
          simp
        _ =
            (List.map (Equiv.cast rfl).invFun
              ((EncodedType.list X).encode xs)).filterMap
                listConstEmptyKeep :=
          by
            have hMap :
                xs.map (fun _ => y) = List.replicate xs.length y := by
              simp [Function.const_def]
            rw [← hMap]
            exact (listConstEmpty_filterMap_encode X Y y hy xs).symm
        _ =
            ((EncodedType.list X).encode xs).filterMap listConstEmptyKeep := by
          simp
    · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
      rfl


end TM2Programs
end ComplexityReduction
