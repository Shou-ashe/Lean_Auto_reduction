import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.Part1
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.TaggedDispatch.Part4

namespace ComplexityReduction

open Turing.TM2.Stmt

/-!
Direct TM support for dispatching fold steps whose input has shape
`acc × (left ⊕ right)`.  The machine below performs only the structural
rebracketing

`(acc, Sum.inl left)  ↦ Sum.inl left`
`(acc, Sum.inr right) ↦ Sum.inr (acc, right)`.

The actual branch computations are supplied separately by `TMPolyTimeMap.sum_elim`.
-/

def sumLeftPayloadEncodedType (X Y : EncodedType) : EncodedType where
  Carrier := X.Carrier
  Symbol := X.Symbol ⊕ Y.Symbol
  finite_symbol := inferInstance
  encode := fun x => (X.encode x).map Sum.inl

def sumRightPayloadEncodedType (X Y : EncodedType) : EncodedType where
  Carrier := Y.Carrier
  Symbol := X.Symbol ⊕ Y.Symbol
  finite_symbol := inferInstance
  encode := fun y => (Y.encode y).map Sum.inr

def sumLeftPayloadKeep {X Y : EncodedType} :
    X.Symbol ⊕ Y.Symbol → Option X.Symbol
  | Sum.inl s => some s
  | Sum.inr _ => none

def sumRightPayloadKeep {X Y : EncodedType} :
    X.Symbol ⊕ Y.Symbol → Option Y.Symbol
  | Sum.inl _ => none
  | Sum.inr s => some s

theorem sumLeftPayload_encode_filterMap (X Y : EncodedType) (x : X.Carrier) :
    ((sumLeftPayloadEncodedType X Y).encode x).filterMap sumLeftPayloadKeep =
      X.encode x := by
  simp [sumLeftPayloadEncodedType, sumLeftPayloadKeep]

theorem sumRightPayload_encode_filterMap (X Y : EncodedType) (y : Y.Carrier) :
    ((sumRightPayloadEncodedType X Y).encode y).filterMap sumRightPayloadKeep =
      Y.encode y := by
  simp [sumRightPayloadEncodedType, sumRightPayloadKeep]

theorem TMPolyTimeMap.sum_elim {X Y Z : EncodedType}
    {f : X.Carrier → Z.Carrier} {g : Y.Carrier → Z.Carrier}
    (hf : TMPolyTimeMap X Z f) (hg : TMPolyTimeMap Y Z g) :
    TMPolyTimeMap
      (EncodedType.sum X Y)
      Z
      (fun q : X.Carrier ⊕ Y.Carrier =>
        match q with
        | Sum.inl x => f x
        | Sum.inr y => g y) := by
  have hLeftForget :
      TMPolyTimeMap (sumLeftPayloadEncodedType X Y) X
        (fun x : X.Carrier => x) :=
    TMPolyTimeMap.symbol_filterMap
      (sumLeftPayloadEncodedType X Y) X (fun x : X.Carrier => x)
      sumLeftPayloadKeep
      (by
        intro x
        exact (sumLeftPayload_encode_filterMap X Y x).symm)
  have hRightForget :
      TMPolyTimeMap (sumRightPayloadEncodedType X Y) Y
        (fun y : Y.Carrier => y) :=
    TMPolyTimeMap.symbol_filterMap
      (sumRightPayloadEncodedType X Y) Y (fun y : Y.Carrier => y)
      sumRightPayloadKeep
      (by
        intro y
        exact (sumRightPayload_encode_filterMap X Y y).symm)
  have hLeftMap :
      TMPolyTimeMap (sumLeftPayloadEncodedType X Y) Z f := by
    have hComp := TMPolyTimeMap.comp hf hLeftForget
    simpa [Function.comp] using hComp
  have hRightMap :
      TMPolyTimeMap (sumRightPayloadEncodedType X Y) Z g := by
    have hComp := TMPolyTimeMap.comp hg hRightForget
    simpa [Function.comp] using hComp
  rcases hLeftMap with ⟨hLeft⟩
  rcases hRightMap with ⟨hRight⟩
  refine ⟨?_⟩
  convert taggedBranchDispatchComputableInPolyTime hLeft hRight using 1
  · funext q
    cases q <;> simp [EncodedType.sum, sumLeftPayloadEncodedType,
      sumRightPayloadEncodedType, List.map_map]
  · funext q
    cases q <;> rfl

def prodSumChoiceEncodedType (A B C : EncodedType) : EncodedType :=
  EncodedType.sum B (EncodedType.prod A C)

def prodSumChoice (A B C : EncodedType)
    (p : A.Carrier × (B.Carrier ⊕ C.Carrier)) :
    (prodSumChoiceEncodedType A B C).Carrier :=
  match p.2 with
  | Sum.inl b => Sum.inl b
  | Sum.inr c => Sum.inr (p.1, c)

inductive ProdSumChoiceStack where
  | input
  | output
  | temp
  deriving DecidableEq, Fintype

abbrev prodSumChoiceInputSymbol (α β γ : Type) :=
  Option (α ⊕ (Bool ⊕ (β ⊕ γ)))

abbrev prodSumChoiceOutputSymbol (α β γ : Type) :=
  Bool ⊕ (β ⊕ Option (α ⊕ γ))

abbrev prodSumChoiceAlphabet (α β γ : Type) :
    ProdSumChoiceStack → Type
  | .input => prodSumChoiceInputSymbol α β γ
  | .output => prodSumChoiceOutputSymbol α β γ
  | .temp => prodSumChoiceOutputSymbol α β γ

inductive ProdSumChoiceLabel (α β γ : Type) where
  | readAcc
  | pushAccTemp (s : prodSumChoiceOutputSymbol α β γ)
  | pushLeftTemp (s : prodSumChoiceOutputSymbol α β γ)
  | pushRightTemp (s : prodSumChoiceOutputSymbol α β γ)
  | readInstructionTag
  | clearAcc
  | readLeftPayload
  | pushRightDelimiter
  | readRightPayload
  | moveTemp (tag : Bool)
  | pushOutput (tag : Bool) (s : prodSumChoiceOutputSymbol α β γ)
  | writeTag (tag : Bool)
  | invalid
  deriving Fintype

inductive ProdSumChoiceState (α β γ : Type) where
  | input (head : Option (prodSumChoiceInputSymbol α β γ))
  | output (head : Option (prodSumChoiceOutputSymbol α β γ))
  deriving Fintype

def prodSumChoiceInputState {α β γ : Type} :
    ProdSumChoiceState α β γ → Option (prodSumChoiceInputSymbol α β γ)
  | .input head => head
  | _ => none

def prodSumChoiceOutputState {α β γ : Type} :
    ProdSumChoiceState α β γ → Option (prodSumChoiceOutputSymbol α β γ)
  | .output head => head
  | _ => none

def prodSumChoiceAccOutputSymbol {α β γ : Type}
    (s : α) : prodSumChoiceOutputSymbol α β γ :=
  Sum.inr (Sum.inr (some (Sum.inl s)))

def prodSumChoiceRightDelimiter {α β γ : Type} :
    prodSumChoiceOutputSymbol α β γ :=
  Sum.inr (Sum.inr none)

def prodSumChoiceLeftOutputSymbol {α β γ : Type}
    (s : β) : prodSumChoiceOutputSymbol α β γ :=
  Sum.inr (Sum.inl s)

def prodSumChoiceRightOutputSymbol {α β γ : Type}
    (s : γ) : prodSumChoiceOutputSymbol α β γ :=
  Sum.inr (Sum.inr (some (Sum.inr s)))

def prodSumChoiceMachine
    (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ] :
    Turing.FinTM2 where
  K := ProdSumChoiceStack
  k₀ := .input
  k₁ := .output
  Γ := prodSumChoiceAlphabet α β γ
  Λ := ProdSumChoiceLabel α β γ
  main := .readAcc
  σ := ProdSumChoiceState α β γ
  initialState := .input none
  Γk₀Fin := inferInstance
  m
    | .readAcc =>
        pop .input (fun _ head => .input head)
          (goto fun state =>
            match prodSumChoiceInputState state with
            | some (some (Sum.inl s)) => .pushAccTemp (prodSumChoiceAccOutputSymbol s)
            | some none => .readInstructionTag
            | _ => .invalid)
    | .pushAccTemp s =>
        push .temp (fun _ => s) (goto fun _ => .readAcc)
    | .pushLeftTemp s =>
        push .temp (fun _ => s) (goto fun _ => .readLeftPayload)
    | .pushRightTemp s =>
        push .temp (fun _ => s) (goto fun _ => .readRightPayload)
    | .readInstructionTag =>
        pop .input (fun _ head => .input head)
          (goto fun state =>
            match prodSumChoiceInputState state with
            | some (some (Sum.inr (Sum.inl false))) => .clearAcc
            | some (some (Sum.inr (Sum.inl true))) => .pushRightDelimiter
            | _ => .invalid)
    | .clearAcc =>
        pop .temp (fun _ head => .output head)
          (goto fun state =>
            match prodSumChoiceOutputState state with
            | some _ => .clearAcc
            | none => .readLeftPayload)
    | .readLeftPayload =>
        pop .input (fun _ head => .input head)
          (goto fun state =>
            match prodSumChoiceInputState state with
            | some (some (Sum.inr (Sum.inr (Sum.inl s)))) =>
                .pushLeftTemp (prodSumChoiceLeftOutputSymbol s)
            | none => .moveTemp false
            | _ => .invalid)
    | .pushRightDelimiter =>
        push .temp (fun _ => prodSumChoiceRightDelimiter)
          (goto fun _ => .readRightPayload)
    | .readRightPayload =>
        pop .input (fun _ head => .input head)
          (goto fun state =>
            match prodSumChoiceInputState state with
            | some (some (Sum.inr (Sum.inr (Sum.inr s)))) =>
                .pushRightTemp (prodSumChoiceRightOutputSymbol s)
            | none => .moveTemp true
            | _ => .invalid)
    | .moveTemp tag =>
        pop .temp (fun _ head => .output head)
          (goto fun state =>
            match prodSumChoiceOutputState state with
            | some s => .pushOutput tag s
            | none => .writeTag tag)
    | .pushOutput tag s =>
        push .output (fun _ => s) (goto fun _ => .moveTemp tag)
    | .writeTag tag =>
        push .output (fun _ => Sum.inl tag) (load (fun _ => .input none) halt)
    | .invalid =>
        halt

def prodSumChoiceCfg {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (label : ProdSumChoiceLabel α β γ)
    (state : ProdSumChoiceState α β γ)
    (input : List (prodSumChoiceInputSymbol α β γ))
    (output temp : List (prodSumChoiceOutputSymbol α β γ)) :
    (prodSumChoiceMachine α β γ).Cfg where
  l := some label
  var := state
  stk
    | .input => input
    | .output => output
    | .temp => temp

def prodSumChoiceHalt {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (output : List (prodSumChoiceOutputSymbol α β γ)) :
    (prodSumChoiceMachine α β γ).Cfg where
  l := none
  var := .input none
  stk
    | .input => []
    | .output => output
    | .temp => []

lemma prodSumChoice_readAcc_step_cons {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (s : α) (state : ProdSumChoiceState α β γ)
    (input : List (prodSumChoiceInputSymbol α β γ))
    (output temp : List (prodSumChoiceOutputSymbol α β γ)) :
    (prodSumChoiceMachine α β γ).step
        (prodSumChoiceCfg .readAcc state (some (Sum.inl s) :: input) output temp) =
      some (prodSumChoiceCfg
        (.pushAccTemp (prodSumChoiceAccOutputSymbol s))
        (.input (some (some (Sum.inl s)))) input output temp) := by
  simp [prodSumChoiceMachine, prodSumChoiceCfg, prodSumChoiceInputState]
  congr
  funext k
  cases k <;> rfl

lemma prodSumChoice_readAcc_step_delim {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (state : ProdSumChoiceState α β γ)
    (input : List (prodSumChoiceInputSymbol α β γ))
    (output temp : List (prodSumChoiceOutputSymbol α β γ)) :
    (prodSumChoiceMachine α β γ).step
        (prodSumChoiceCfg .readAcc state (none :: input) output temp) =
      some (prodSumChoiceCfg .readInstructionTag (.input (some none))
        input output temp) := by
  simp [prodSumChoiceMachine, prodSumChoiceCfg, prodSumChoiceInputState]
  congr
  funext k
  cases k <;> rfl

lemma prodSumChoice_pushAccTemp_step {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (s : prodSumChoiceOutputSymbol α β γ) (state : ProdSumChoiceState α β γ)
    (input : List (prodSumChoiceInputSymbol α β γ))
    (output temp : List (prodSumChoiceOutputSymbol α β γ)) :
    (prodSumChoiceMachine α β γ).step
        (prodSumChoiceCfg (.pushAccTemp s) state input output temp) =
      some (prodSumChoiceCfg .readAcc state input output (s :: temp)) := by
  simp [prodSumChoiceMachine, prodSumChoiceCfg]
  congr
  funext k
  cases k <;> rfl

lemma prodSumChoice_pushLeftTemp_step {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (s : prodSumChoiceOutputSymbol α β γ) (state : ProdSumChoiceState α β γ)
    (input : List (prodSumChoiceInputSymbol α β γ))
    (output temp : List (prodSumChoiceOutputSymbol α β γ)) :
    (prodSumChoiceMachine α β γ).step
        (prodSumChoiceCfg (.pushLeftTemp s) state input output temp) =
      some (prodSumChoiceCfg .readLeftPayload state input output (s :: temp)) := by
  simp [prodSumChoiceMachine, prodSumChoiceCfg]
  congr
  funext k
  cases k <;> rfl

lemma prodSumChoice_pushRightTemp_step {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (s : prodSumChoiceOutputSymbol α β γ) (state : ProdSumChoiceState α β γ)
    (input : List (prodSumChoiceInputSymbol α β γ))
    (output temp : List (prodSumChoiceOutputSymbol α β γ)) :
    (prodSumChoiceMachine α β γ).step
        (prodSumChoiceCfg (.pushRightTemp s) state input output temp) =
      some (prodSumChoiceCfg .readRightPayload state input output (s :: temp)) := by
  simp [prodSumChoiceMachine, prodSumChoiceCfg]
  congr
  funext k
  cases k <;> rfl

lemma prodSumChoice_readInstructionTag_step_left {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (input : List (prodSumChoiceInputSymbol α β γ))
    (output temp : List (prodSumChoiceOutputSymbol α β γ)) :
    (prodSumChoiceMachine α β γ).step
        (prodSumChoiceCfg .readInstructionTag (.input (some none))
          (some (Sum.inr (Sum.inl false)) :: input) output temp) =
      some (prodSumChoiceCfg .clearAcc
        (.input (some (some (Sum.inr (Sum.inl false))))) input output temp) := by
  simp [prodSumChoiceMachine, prodSumChoiceCfg, prodSumChoiceInputState]
  congr
  funext k
  cases k <;> rfl

lemma prodSumChoice_readInstructionTag_step_right {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (input : List (prodSumChoiceInputSymbol α β γ))
    (output temp : List (prodSumChoiceOutputSymbol α β γ)) :
    (prodSumChoiceMachine α β γ).step
        (prodSumChoiceCfg .readInstructionTag (.input (some none))
          (some (Sum.inr (Sum.inl true)) :: input) output temp) =
      some (prodSumChoiceCfg .pushRightDelimiter
        (.input (some (some (Sum.inr (Sum.inl true))))) input output temp) := by
  simp [prodSumChoiceMachine, prodSumChoiceCfg, prodSumChoiceInputState]
  congr
  funext k
  cases k <;> rfl

lemma prodSumChoice_clearAcc_step_cons {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (s : prodSumChoiceOutputSymbol α β γ) (state : ProdSumChoiceState α β γ)
    (input : List (prodSumChoiceInputSymbol α β γ))
    (output temp : List (prodSumChoiceOutputSymbol α β γ)) :
    (prodSumChoiceMachine α β γ).step
        (prodSumChoiceCfg .clearAcc state input output (s :: temp)) =
      some (prodSumChoiceCfg .clearAcc (.output (some s)) input output temp) := by
  simp [prodSumChoiceMachine, prodSumChoiceCfg, prodSumChoiceOutputState]
  congr
  funext k
  cases k <;> rfl

lemma prodSumChoice_clearAcc_step_nil {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (state : ProdSumChoiceState α β γ)
    (input : List (prodSumChoiceInputSymbol α β γ))
    (output : List (prodSumChoiceOutputSymbol α β γ)) :
    (prodSumChoiceMachine α β γ).step
        (prodSumChoiceCfg .clearAcc state input output []) =
      some (prodSumChoiceCfg .readLeftPayload (.output none) input output []) := by
  simp [prodSumChoiceMachine, prodSumChoiceCfg, prodSumChoiceOutputState]
  congr

lemma prodSumChoice_readLeftPayload_step_cons {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (s : β) (state : ProdSumChoiceState α β γ)
    (input : List (prodSumChoiceInputSymbol α β γ))
    (output temp : List (prodSumChoiceOutputSymbol α β γ)) :
    (prodSumChoiceMachine α β γ).step
        (prodSumChoiceCfg .readLeftPayload state
          (some (Sum.inr (Sum.inr (Sum.inl s))) :: input) output temp) =
      some (prodSumChoiceCfg (.pushLeftTemp (prodSumChoiceLeftOutputSymbol s))
        (.input (some (some (Sum.inr (Sum.inr (Sum.inl s)))))) input output temp) := by
  simp [prodSumChoiceMachine, prodSumChoiceCfg, prodSumChoiceInputState]
  congr
  funext k
  cases k <;> rfl

lemma prodSumChoice_readLeftPayload_step_nil {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (state : ProdSumChoiceState α β γ)
    (output temp : List (prodSumChoiceOutputSymbol α β γ)) :
    (prodSumChoiceMachine α β γ).step
        (prodSumChoiceCfg .readLeftPayload state [] output temp) =
      some (prodSumChoiceCfg (.moveTemp false) (.input none) [] output temp) := by
  simp [prodSumChoiceMachine, prodSumChoiceCfg, prodSumChoiceInputState]
  congr

lemma prodSumChoice_pushRightDelimiter_step {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (state : ProdSumChoiceState α β γ)
    (input : List (prodSumChoiceInputSymbol α β γ))
    (output temp : List (prodSumChoiceOutputSymbol α β γ)) :
    (prodSumChoiceMachine α β γ).step
        (prodSumChoiceCfg .pushRightDelimiter state input output temp) =
      some (prodSumChoiceCfg .readRightPayload state input output
        (prodSumChoiceRightDelimiter :: temp)) := by
  simp [prodSumChoiceMachine, prodSumChoiceCfg]
  congr
  funext k
  cases k <;> rfl

lemma prodSumChoice_readRightPayload_step_cons {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (s : γ) (state : ProdSumChoiceState α β γ)
    (input : List (prodSumChoiceInputSymbol α β γ))
    (output temp : List (prodSumChoiceOutputSymbol α β γ)) :
    (prodSumChoiceMachine α β γ).step
        (prodSumChoiceCfg .readRightPayload state
          (some (Sum.inr (Sum.inr (Sum.inr s))) :: input) output temp) =
      some (prodSumChoiceCfg (.pushRightTemp (prodSumChoiceRightOutputSymbol s))
        (.input (some (some (Sum.inr (Sum.inr (Sum.inr s)))))) input output temp) := by
  simp [prodSumChoiceMachine, prodSumChoiceCfg, prodSumChoiceInputState]
  congr
  funext k
  cases k <;> rfl

lemma prodSumChoice_readRightPayload_step_nil {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (state : ProdSumChoiceState α β γ)
    (output temp : List (prodSumChoiceOutputSymbol α β γ)) :
    (prodSumChoiceMachine α β γ).step
        (prodSumChoiceCfg .readRightPayload state [] output temp) =
      some (prodSumChoiceCfg (.moveTemp true) (.input none) [] output temp) := by
  simp [prodSumChoiceMachine, prodSumChoiceCfg, prodSumChoiceInputState]
  congr

lemma prodSumChoice_moveTemp_step_cons {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (tag : Bool) (s : prodSumChoiceOutputSymbol α β γ)
    (state : ProdSumChoiceState α β γ)
    (input : List (prodSumChoiceInputSymbol α β γ))
    (output temp : List (prodSumChoiceOutputSymbol α β γ)) :
    (prodSumChoiceMachine α β γ).step
        (prodSumChoiceCfg (.moveTemp tag) state input output (s :: temp)) =
      some (prodSumChoiceCfg (.pushOutput tag s) (.output (some s))
        input output temp) := by
  simp [prodSumChoiceMachine, prodSumChoiceCfg, prodSumChoiceOutputState]
  congr
  funext k
  cases k <;> rfl

lemma prodSumChoice_moveTemp_step_nil {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (tag : Bool) (state : ProdSumChoiceState α β γ)
    (input : List (prodSumChoiceInputSymbol α β γ))
    (output : List (prodSumChoiceOutputSymbol α β γ)) :
    (prodSumChoiceMachine α β γ).step
        (prodSumChoiceCfg (.moveTemp tag) state input output []) =
      some (prodSumChoiceCfg (.writeTag tag) (.output none) input output []) := by
  simp [prodSumChoiceMachine, prodSumChoiceCfg, prodSumChoiceOutputState]
  congr

lemma prodSumChoice_pushOutput_step {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (tag : Bool) (s : prodSumChoiceOutputSymbol α β γ)
    (state : ProdSumChoiceState α β γ)
    (input : List (prodSumChoiceInputSymbol α β γ))
    (output temp : List (prodSumChoiceOutputSymbol α β γ)) :
    (prodSumChoiceMachine α β γ).step
        (prodSumChoiceCfg (.pushOutput tag s) state input output temp) =
      some (prodSumChoiceCfg (.moveTemp tag) state input (s :: output) temp) := by
  simp [prodSumChoiceMachine, prodSumChoiceCfg]
  congr
  funext k
  cases k <;> rfl

lemma prodSumChoice_writeTag_step {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (tag : Bool) (output : List (prodSumChoiceOutputSymbol α β γ)) :
    (prodSumChoiceMachine α β γ).step
        (prodSumChoiceCfg (.writeTag tag) (.output none) [] output []) =
      some (prodSumChoiceHalt (Sum.inl tag :: output)) := by
  simp [prodSumChoiceMachine, prodSumChoiceCfg, prodSumChoiceHalt]
  congr
  funext k
  cases k <;> rfl

lemma prodSumChoice_initList {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (input : List (prodSumChoiceInputSymbol α β γ)) :
    Turing.initList (prodSumChoiceMachine α β γ) input =
      prodSumChoiceCfg .readAcc (.input none) input [] [] := by
  simp [prodSumChoiceMachine, prodSumChoiceCfg, Turing.initList]
  congr
  funext k
  cases k <;> rfl

lemma prodSumChoice_haltList {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (output : List (prodSumChoiceOutputSymbol α β γ)) :
    Turing.haltList (prodSumChoiceMachine α β γ) output =
      prodSumChoiceHalt output := by
  simp [prodSumChoiceMachine, prodSumChoiceHalt, Turing.haltList]
  congr
  funext k
  cases k <;> rfl

def prodSumChoice_readAcc_run {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (acc : List α) (state : ProdSumChoiceState α β γ)
    (input : List (prodSumChoiceInputSymbol α β γ))
    (output temp : List (prodSumChoiceOutputSymbol α β γ)) :
    StateTransition.EvalsToInTime
      (prodSumChoiceMachine α β γ).step
      (prodSumChoiceCfg .readAcc state
        (acc.map (fun s => some (Sum.inl s)) ++ none :: input) output temp)
      (some (prodSumChoiceCfg .readInstructionTag (.input (some none)) input
        output ((acc.map (fun s => prodSumChoiceAccOutputSymbol (β := β) (γ := γ) s)).reverse ++
          temp)))
      (2 * acc.length + 1) := by
  induction acc generalizing state temp with
  | nil =>
      simpa using
        TM2Programs.evalsToInTimeOne
          (prodSumChoice_readAcc_step_delim state input output temp)
  | cons s rest ih =>
      let mapped : prodSumChoiceOutputSymbol α β γ := prodSumChoiceAccOutputSymbol s
      let tm := prodSumChoiceMachine α β γ
      let c₀ := prodSumChoiceCfg .readAcc state
        (some (Sum.inl s) :: rest.map (fun s => some (Sum.inl s)) ++ none :: input)
        output temp
      let c₁ := prodSumChoiceCfg (.pushAccTemp mapped)
        (.input (some (some (Sum.inl s))))
        (rest.map (fun s => some (Sum.inl s)) ++ none :: input) output temp
      let c₂ := prodSumChoiceCfg .readAcc
        (.input (some (some (Sum.inl s))))
        (rest.map (fun s => some (Sum.inl s)) ++ none :: input) output (mapped :: temp)
      have hStep₁ : tm.step c₀ = some c₁ := by
        simpa [tm, c₀, c₁, mapped] using
          (prodSumChoice_readAcc_step_cons s state
            (rest.map (fun s => some (Sum.inl s)) ++ none :: input) output temp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne hStep₁
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        TM2Programs.evalsToInTimeOne
          (prodSumChoice_pushAccTemp_step mapped (.input (some (some (Sum.inl s))))
            (rest.map (fun s => some (Sum.inl s)) ++ none :: input) output temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail := ih (.input (some (some (Sum.inl s)))) (mapped :: temp)
      simpa [tm, c₀, c₁, c₂, mapped, List.map_cons, List.reverse_cons,
        List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using
          StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * rest.length + 1)
            c₀ c₂
            (some (prodSumChoiceCfg .readInstructionTag (.input (some none)) input
              output
              ((rest.map (fun s => prodSumChoiceAccOutputSymbol (β := β) (γ := γ) s)).reverse ++
                mapped :: temp)))
            h₁₂ hTail

def prodSumChoice_clearAcc_run {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (state : ProdSumChoiceState α β γ)
    (input : List (prodSumChoiceInputSymbol α β γ))
    (output temp : List (prodSumChoiceOutputSymbol α β γ)) :
    StateTransition.EvalsToInTime
      (prodSumChoiceMachine α β γ).step
      (prodSumChoiceCfg .clearAcc state input output temp)
      (some (prodSumChoiceCfg .readLeftPayload (.output none) input output []))
      (temp.length + 1) := by
  induction temp generalizing state with
  | nil =>
      simpa using
        TM2Programs.evalsToInTimeOne
          (prodSumChoice_clearAcc_step_nil state input output)
  | cons s temp ih =>
      let tm := prodSumChoiceMachine α β γ
      let c₀ := prodSumChoiceCfg .clearAcc state input output (s :: temp)
      let c₁ := prodSumChoiceCfg .clearAcc (.output (some s)) input output temp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne
          (prodSumChoice_clearAcc_step_cons s state input output temp)
      have hTail := ih (.output (some s))
      simpa [tm, c₀, c₁, Nat.add_assoc] using
        StateTransition.EvalsToInTime.trans tm.step 1 (temp.length + 1)
          c₀ c₁
          (some (prodSumChoiceCfg .readLeftPayload (.output none) input output []))
          h₁ hTail

def prodSumChoice_readLeftPayload_run {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (payload : List β) (state : ProdSumChoiceState α β γ)
    (output temp : List (prodSumChoiceOutputSymbol α β γ)) :
    StateTransition.EvalsToInTime
      (prodSumChoiceMachine α β γ).step
      (prodSumChoiceCfg .readLeftPayload state
        (payload.map (fun s => some (Sum.inr (Sum.inr (Sum.inl s))))) output temp)
      (some (prodSumChoiceCfg (.moveTemp false) (.input none) [] output
        ((payload.map (fun s => prodSumChoiceLeftOutputSymbol (α := α) (γ := γ) s)).reverse ++
          temp)))
      (2 * payload.length + 1) := by
  induction payload generalizing state temp with
  | nil =>
      simpa using
        TM2Programs.evalsToInTimeOne
          (prodSumChoice_readLeftPayload_step_nil state output temp)
  | cons s rest ih =>
      let mapped : prodSumChoiceOutputSymbol α β γ := prodSumChoiceLeftOutputSymbol s
      let tm := prodSumChoiceMachine α β γ
      let c₀ := prodSumChoiceCfg .readLeftPayload state
        (some (Sum.inr (Sum.inr (Sum.inl s))) ::
          rest.map (fun s => some (Sum.inr (Sum.inr (Sum.inl s)))))
        output temp
      let c₁ := prodSumChoiceCfg (.pushLeftTemp mapped)
        (.input (some (some (Sum.inr (Sum.inr (Sum.inl s))))))
        (rest.map (fun s => some (Sum.inr (Sum.inr (Sum.inl s))))) output temp
      let c₂ := prodSumChoiceCfg .readLeftPayload
        (.input (some (some (Sum.inr (Sum.inr (Sum.inl s))))))
        (rest.map (fun s => some (Sum.inr (Sum.inr (Sum.inl s)))))
        output (mapped :: temp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne
          (prodSumChoice_readLeftPayload_step_cons s state
            (rest.map (fun s => some (Sum.inr (Sum.inr (Sum.inl s))))) output temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        TM2Programs.evalsToInTimeOne
          (prodSumChoice_pushLeftTemp_step mapped
            (.input (some (some (Sum.inr (Sum.inr (Sum.inl s))))))
            (rest.map (fun s => some (Sum.inr (Sum.inr (Sum.inl s))))) output temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail := ih
        (.input (some (some (Sum.inr (Sum.inr (Sum.inl s)))))) (mapped :: temp)
      simpa [tm, c₀, c₁, c₂, mapped, List.map_cons, List.reverse_cons,
        List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using
          StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * rest.length + 1)
            c₀ c₂
            (some (prodSumChoiceCfg (.moveTemp false) (.input none) [] output
              ((rest.map (fun s => prodSumChoiceLeftOutputSymbol (α := α) (γ := γ) s)).reverse ++
                mapped :: temp)))
            h₁₂ hTail

def prodSumChoice_readRightPayload_run {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (payload : List γ) (state : ProdSumChoiceState α β γ)
    (output temp : List (prodSumChoiceOutputSymbol α β γ)) :
    StateTransition.EvalsToInTime
      (prodSumChoiceMachine α β γ).step
      (prodSumChoiceCfg .readRightPayload state
        (payload.map (fun s => some (Sum.inr (Sum.inr (Sum.inr s))))) output temp)
      (some (prodSumChoiceCfg (.moveTemp true) (.input none) [] output
        ((payload.map (fun s => prodSumChoiceRightOutputSymbol (α := α) (β := β) s)).reverse ++
          temp)))
      (2 * payload.length + 1) := by
  induction payload generalizing state temp with
  | nil =>
      simpa using
        TM2Programs.evalsToInTimeOne
          (prodSumChoice_readRightPayload_step_nil state output temp)
  | cons s rest ih =>
      let mapped : prodSumChoiceOutputSymbol α β γ := prodSumChoiceRightOutputSymbol s
      let tm := prodSumChoiceMachine α β γ
      let c₀ := prodSumChoiceCfg .readRightPayload state
        (some (Sum.inr (Sum.inr (Sum.inr s))) ::
          rest.map (fun s => some (Sum.inr (Sum.inr (Sum.inr s)))))
        output temp
      let c₁ := prodSumChoiceCfg (.pushRightTemp mapped)
        (.input (some (some (Sum.inr (Sum.inr (Sum.inr s))))))
        (rest.map (fun s => some (Sum.inr (Sum.inr (Sum.inr s))))) output temp
      let c₂ := prodSumChoiceCfg .readRightPayload
        (.input (some (some (Sum.inr (Sum.inr (Sum.inr s))))))
        (rest.map (fun s => some (Sum.inr (Sum.inr (Sum.inr s)))))
        output (mapped :: temp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne
          (prodSumChoice_readRightPayload_step_cons s state
            (rest.map (fun s => some (Sum.inr (Sum.inr (Sum.inr s))))) output temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        TM2Programs.evalsToInTimeOne
          (prodSumChoice_pushRightTemp_step mapped
            (.input (some (some (Sum.inr (Sum.inr (Sum.inr s))))))
            (rest.map (fun s => some (Sum.inr (Sum.inr (Sum.inr s))))) output temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail := ih
        (.input (some (some (Sum.inr (Sum.inr (Sum.inr s)))))) (mapped :: temp)
      simpa [tm, c₀, c₁, c₂, mapped, List.map_cons, List.reverse_cons,
        List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using
          StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * rest.length + 1)
            c₀ c₂
            (some (prodSumChoiceCfg (.moveTemp true) (.input none) [] output
              ((rest.map (fun s => prodSumChoiceRightOutputSymbol (α := α) (β := β) s)).reverse ++
                mapped :: temp)))
            h₁₂ hTail

def prodSumChoice_moveTemp_run {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (tag : Bool) (state : ProdSumChoiceState α β γ)
    (input : List (prodSumChoiceInputSymbol α β γ))
    (output temp : List (prodSumChoiceOutputSymbol α β γ)) :
    StateTransition.EvalsToInTime
      (prodSumChoiceMachine α β γ).step
      (prodSumChoiceCfg (.moveTemp tag) state input output temp)
      (some (prodSumChoiceCfg (.writeTag tag) (.output none) input
        (temp.reverse ++ output) []))
      (2 * temp.length + 1) := by
  induction temp generalizing state output with
  | nil =>
      simpa using
        TM2Programs.evalsToInTimeOne
          (prodSumChoice_moveTemp_step_nil tag state input output)
  | cons s temp ih =>
      let tm := prodSumChoiceMachine α β γ
      let c₀ := prodSumChoiceCfg (.moveTemp tag) state input output (s :: temp)
      let c₁ := prodSumChoiceCfg (.pushOutput tag s) (.output (some s)) input output temp
      let c₂ := prodSumChoiceCfg (.moveTemp tag) (.output (some s)) input (s :: output) temp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne
          (prodSumChoice_moveTemp_step_cons tag s state input output temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        TM2Programs.evalsToInTimeOne
          (prodSumChoice_pushOutput_step tag s (.output (some s)) input output temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail := ih (.output (some s)) (s :: output)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          StateTransition.EvalsToInTime.trans tm.step (1 + 1) (2 * temp.length + 1)
            c₀ c₂
            (some (prodSumChoiceCfg (.writeTag tag) (.output none) input
              (temp.reverse ++ s :: output) []))
            h₁₂ hTail

def prodSumChoice_outputs_left {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (acc : List α) (payload : List β) :
    Turing.TM2OutputsInTime
      (prodSumChoiceMachine α β γ)
      (acc.map (fun s => some (Sum.inl s)) ++
        none :: some (Sum.inr (Sum.inl false)) ::
          payload.map (fun s => some (Sum.inr (Sum.inr (Sum.inl s)))))
      (some (Sum.inl false ::
        payload.map (fun s => prodSumChoiceLeftOutputSymbol (α := α) (γ := γ) s)))
      (4 * (acc.length + payload.length) + 8) := by
  let tm := prodSumChoiceMachine α β γ
  let accMapped : List (prodSumChoiceOutputSymbol α β γ) :=
    acc.map (fun s => prodSumChoiceAccOutputSymbol (β := β) (γ := γ) s)
  let payloadInput : List (prodSumChoiceInputSymbol α β γ) :=
    payload.map (fun s =>
      (some (Sum.inr (Sum.inr (Sum.inl s))) : prodSumChoiceInputSymbol α β γ))
  let payloadMapped : List (prodSumChoiceOutputSymbol α β γ) :=
    payload.map (fun s => prodSumChoiceLeftOutputSymbol (α := α) (γ := γ) s)
  let rest := some (Sum.inr (Sum.inl false)) :: payloadInput
  let cTag := prodSumChoiceCfg .readInstructionTag (.input (some none)) rest [] accMapped.reverse
  let cClear := prodSumChoiceCfg .clearAcc
    (.input (some (some (Sum.inr (Sum.inl false))))) payloadInput [] accMapped.reverse
  let cPayload := prodSumChoiceCfg .readLeftPayload (.output none) payloadInput [] []
  let cMove := prodSumChoiceCfg (.moveTemp false) (.input none) [] [] payloadMapped.reverse
  let cWrite := prodSumChoiceCfg (.writeTag false) (.output none) [] payloadMapped []
  let done := prodSumChoiceHalt (Sum.inl false :: payloadMapped)
  have hRead :
      StateTransition.EvalsToInTime tm.step (Turing.initList tm
        (acc.map (fun s => some (Sum.inl s)) ++ none :: rest)) (some cTag)
        (2 * acc.length + 1) := by
    simpa [tm, cTag, rest, accMapped, prodSumChoice_initList]
      using prodSumChoice_readAcc_run acc (.input none) rest [] []
  have hTag : StateTransition.EvalsToInTime tm.step cTag (some cClear) 1 :=
    TM2Programs.evalsToInTimeOne
      (by simpa [tm, cTag, cClear, rest] using
        (prodSumChoice_readInstructionTag_step_left payloadInput [] accMapped.reverse))
  have hClear :
      StateTransition.EvalsToInTime tm.step cClear (some cPayload)
        (accMapped.reverse.length + 1) := by
    simpa [tm, cClear, cPayload, accMapped] using
      prodSumChoice_clearAcc_run
        (.input (some (some (Sum.inr (Sum.inl false))))) payloadInput []
        accMapped.reverse
  have hPayload :
      StateTransition.EvalsToInTime tm.step cPayload (some cMove)
        (2 * payload.length + 1) := by
    simpa [tm, cPayload, cMove, payloadInput, payloadMapped] using
      prodSumChoice_readLeftPayload_run payload (.output none) [] []
  have hMove :
      StateTransition.EvalsToInTime tm.step cMove (some cWrite)
        (2 * payloadMapped.reverse.length + 1) := by
    simpa [tm, cMove, cWrite, payloadMapped] using
      prodSumChoice_moveTemp_run false (.input none) [] [] payloadMapped.reverse
  have hWrite : StateTransition.EvalsToInTime tm.step cWrite (some done) 1 :=
    TM2Programs.evalsToInTimeOne
      (by simpa [tm, cWrite, done] using prodSumChoice_writeTag_step false payloadMapped)
  have hAll :=
    StateTransition.EvalsToInTime.trans tm.step _ _ _ _ _ hRead
      (StateTransition.EvalsToInTime.trans tm.step _ _ _ _ _ hTag
        (StateTransition.EvalsToInTime.trans tm.step _ _ _ _ _ hClear
          (StateTransition.EvalsToInTime.trans tm.step _ _ _ _ _ hPayload
            (StateTransition.EvalsToInTime.trans tm.step _ _ _ _ _ hMove hWrite))))
  change StateTransition.EvalsToInTime tm.step
    (Turing.initList tm
      (acc.map (fun s => some (Sum.inl s)) ++ none :: some (Sum.inr (Sum.inl false)) ::
        payload.map (fun s => some (Sum.inr (Sum.inr (Sum.inl s))))))
    (some (Turing.haltList tm (Sum.inl false :: payloadMapped)))
    (4 * (acc.length + payload.length) + 8)
  exact
    TM2Programs.evalsToInTime_mono
      (by simpa [tm, done, prodSumChoice_haltList] using hAll)
      (by
        simp [accMapped, payloadMapped]
        omega)

def prodSumChoice_outputs_right {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (acc : List α) (payload : List γ) :
    Turing.TM2OutputsInTime
      (prodSumChoiceMachine α β γ)
      (acc.map (fun s => some (Sum.inl s)) ++
        none :: some (Sum.inr (Sum.inl true)) ::
          payload.map (fun s => some (Sum.inr (Sum.inr (Sum.inr s)))))
      (some
        (Sum.inl true ::
          (acc.map (fun s => prodSumChoiceAccOutputSymbol (β := β) (γ := γ) s) ++
            prodSumChoiceRightDelimiter ::
              payload.map (fun s => prodSumChoiceRightOutputSymbol (α := α) (β := β) s))))
      (4 * (acc.length + payload.length) + 8) := by
  let tm := prodSumChoiceMachine α β γ
  let accMapped : List (prodSumChoiceOutputSymbol α β γ) :=
    acc.map (fun s => prodSumChoiceAccOutputSymbol (β := β) (γ := γ) s)
  let payloadInput : List (prodSumChoiceInputSymbol α β γ) :=
    payload.map (fun s =>
      (some (Sum.inr (Sum.inr (Sum.inr s))) : prodSumChoiceInputSymbol α β γ))
  let payloadMapped : List (prodSumChoiceOutputSymbol α β γ) :=
    payload.map (fun s => prodSumChoiceRightOutputSymbol (α := α) (β := β) s)
  let rest := some (Sum.inr (Sum.inl true)) :: payloadInput
  let cTag := prodSumChoiceCfg .readInstructionTag (.input (some none)) rest [] accMapped.reverse
  let cDelim := prodSumChoiceCfg .pushRightDelimiter
    (.input (some (some (Sum.inr (Sum.inl true))))) payloadInput [] accMapped.reverse
  let cPayload := prodSumChoiceCfg .readRightPayload
    (.input (some (some (Sum.inr (Sum.inl true))))) payloadInput []
    (prodSumChoiceRightDelimiter :: accMapped.reverse)
  let cMove := prodSumChoiceCfg (.moveTemp true) (.input none) [] []
    (payloadMapped.reverse ++ prodSumChoiceRightDelimiter :: accMapped.reverse)
  let outPayload := accMapped ++ prodSumChoiceRightDelimiter :: payloadMapped
  let cWrite := prodSumChoiceCfg (.writeTag true) (.output none) [] outPayload []
  let done := prodSumChoiceHalt (Sum.inl true :: outPayload)
  have hRead :
      StateTransition.EvalsToInTime tm.step (Turing.initList tm
        (acc.map (fun s => some (Sum.inl s)) ++ none :: rest)) (some cTag)
        (2 * acc.length + 1) := by
    simpa [tm, cTag, rest, accMapped, prodSumChoice_initList]
      using prodSumChoice_readAcc_run acc (.input none) rest [] []
  have hTag : StateTransition.EvalsToInTime tm.step cTag (some cDelim) 1 :=
    TM2Programs.evalsToInTimeOne
      (by simpa [tm, cTag, cDelim, rest] using
        (prodSumChoice_readInstructionTag_step_right payloadInput [] accMapped.reverse))
  have hDelim : StateTransition.EvalsToInTime tm.step cDelim (some cPayload) 1 :=
    TM2Programs.evalsToInTimeOne
      (by simpa [tm, cDelim, cPayload] using
        (prodSumChoice_pushRightDelimiter_step
          (.input (some (some (Sum.inr (Sum.inl true))))) payloadInput []
          accMapped.reverse))
  have hPayload :
      StateTransition.EvalsToInTime tm.step cPayload (some cMove)
        (2 * payload.length + 1) := by
    simpa [tm, cPayload, cMove, payloadInput, payloadMapped, List.append_assoc]
      using
        prodSumChoice_readRightPayload_run payload
          (.input (some (some (Sum.inr (Sum.inl true))))) []
          (prodSumChoiceRightDelimiter :: accMapped.reverse)
  have hMove :
      StateTransition.EvalsToInTime tm.step cMove (some cWrite)
        (2 * (payloadMapped.reverse ++ prodSumChoiceRightDelimiter ::
          accMapped.reverse).length + 1) := by
    simpa [tm, cMove, cWrite, outPayload, accMapped, payloadMapped,
      List.reverse_append, List.append_assoc] using
      prodSumChoice_moveTemp_run true (.input none) [] []
        (payloadMapped.reverse ++ prodSumChoiceRightDelimiter :: accMapped.reverse)
  have hWrite : StateTransition.EvalsToInTime tm.step cWrite (some done) 1 :=
    TM2Programs.evalsToInTimeOne
      (by simpa [tm, cWrite, done] using prodSumChoice_writeTag_step true outPayload)
  have hAll :=
    StateTransition.EvalsToInTime.trans tm.step _ _ _ _ _ hRead
      (StateTransition.EvalsToInTime.trans tm.step _ _ _ _ _ hTag
        (StateTransition.EvalsToInTime.trans tm.step _ _ _ _ _ hDelim
          (StateTransition.EvalsToInTime.trans tm.step _ _ _ _ _ hPayload
            (StateTransition.EvalsToInTime.trans tm.step _ _ _ _ _ hMove hWrite))))
  change StateTransition.EvalsToInTime tm.step
    (Turing.initList tm
      (acc.map (fun s => some (Sum.inl s)) ++ none :: some (Sum.inr (Sum.inl true)) ::
        payload.map (fun s => some (Sum.inr (Sum.inr (Sum.inr s))))))
    (some (Turing.haltList tm (Sum.inl true :: outPayload)))
    (4 * (acc.length + payload.length) + 8)
  exact
    TM2Programs.evalsToInTime_mono
      (by simpa [tm, done, prodSumChoice_haltList, outPayload] using hAll)
      (by
        simp [accMapped, payloadMapped]
        omega)

theorem prodSumChoice_tm_polytime (A B C : EncodedType) :
    TMPolyTimeMap
      (EncodedType.prod A (EncodedType.sum B C))
      (prodSumChoiceEncodedType A B C)
      (prodSumChoice A B C) :=
  ⟨{ tm := prodSumChoiceMachine A.Symbol B.Symbol C.Symbol
     inputAlphabet := Equiv.refl _
     outputAlphabet := Equiv.refl _
     time := 4 * Polynomial.X + 8
     outputsFun := by
      intro p
      rcases p with ⟨acc, instr⟩
      cases instr with
      | inl left =>
          have hOut :=
            prodSumChoice_outputs_left
              (α := A.Symbol) (β := B.Symbol) (γ := C.Symbol)
              (A.encode acc) (B.encode left)
          exact
            TM2Programs.evalsToInTime_mono
              (m := 4 * ((A.encode acc).length + (B.encode left).length) + 8)
              (by
                simpa [Turing.TM2OutputsInTime, List.map_id, prodSumChoice,
                  prodSumChoiceEncodedType, EncodedType.prod, EncodedType.sum,
                  prodSumChoiceAccOutputSymbol, prodSumChoiceLeftOutputSymbol]
                  using hOut)
              (by
                simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
                  EncodedType.prod, EncodedType.sum]
                omega)
      | inr right =>
          have hOut :=
            prodSumChoice_outputs_right
              (α := A.Symbol) (β := B.Symbol) (γ := C.Symbol)
              (A.encode acc) (C.encode right)
          exact
            TM2Programs.evalsToInTime_mono
              (m := 4 * ((A.encode acc).length + (C.encode right).length) + 8)
              (by
                simpa [Turing.TM2OutputsInTime, List.map_id, prodSumChoice,
                  prodSumChoiceEncodedType, EncodedType.prod, EncodedType.sum,
                  prodSumChoiceAccOutputSymbol, prodSumChoiceRightOutputSymbol,
                  prodSumChoiceRightDelimiter]
                  using hOut)
              (by
                simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
                  EncodedType.prod, EncodedType.sum]
                omega) }⟩

end ComplexityReduction
