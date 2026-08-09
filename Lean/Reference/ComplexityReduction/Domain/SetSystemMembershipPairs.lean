/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.BoolDispatch
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.InvariantFold
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatArithmetic
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.HittingSet.StructuredRoute
import ComplexityReduction.Domain.Core.IncidenceIR

/-!
Clean direct-TM building blocks for the ordered membership-pair payload of the
canonical incidence hub.

This leaf deliberately owns only source-local list processing. It imports no
legacy packet, descriptor, provider, route, or registry API; a later concrete
SetSystem ingress composes these blocks with its source presentation and the
canonical `IncidenceIR` hub.
-/

namespace ComplexityReduction
namespace Domain
namespace SetSystemMembershipPairs

open ComplexityReduction
open ComplexityReduction.Combinatorics

/-- The canonical codec for one ordered incidence pair. -/
abbrev pairEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.nat

/-- The canonical codec for an ordered incidence-pair payload. -/
abbrev pairListEncodedType : EncodedType :=
  EncodedType.list pairEncodedType

/-- A tagged instruction either selects the current set index or emits one member. -/
abbrev instructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool EncodedType.nat

abbrev instructionListEncodedType : EncodedType :=
  EncodedType.list instructionEncodedType

abbrev instructionInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat setStructuredEncodedType

abbrev accumulatorEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat pairListEncodedType

abbrev stepInputEncodedType : EncodedType :=
  EncodedType.prod accumulatorEncodedType instructionEncodedType

/-- Install the current right-vertex index. -/
def initInstruction (index : Nat) : Bool × Nat :=
  (false, index)

/-- Emit one member of the current set. -/
def elementInstruction (element : Nat) : Bool × Nat :=
  (true, element)

/-- Encode one set as an index instruction followed by its member instructions. -/
def instructions (input : Nat × List Nat) : List (Bool × Nat) :=
  initInstruction input.1 :: input.2.map elementInstruction

/-- One local instruction transition for the ordered membership-pair payload. -/
def step (input : (Nat × List (Nat × Nat)) × (Bool × Nat)) : Nat × List (Nat × Nat) :=
  if input.2.1 then
    (input.1.1, input.1.2 ++ [(input.2.2, input.1.1)])
  else
    (input.2.2, [])

/-- Emit the canonical `(element, setIndex)` sequence for one source set. -/
def pairsForSet (input : Nat × List Nat) : List (Nat × Nat) :=
  ((instructions input).foldl (fun accumulator instruction => step (accumulator, instruction))
    ((0 : Nat), ([] : List (Nat × Nat)))).2

private theorem elementInstructions_fold
    (index : Nat) (elements : List Nat) (output : List (Nat × Nat)) :
    ((elements.map elementInstruction).foldl
        (fun accumulator instruction => step (accumulator, instruction)) (index, output)) =
      (index, output ++ elements.map fun element => (element, index)) := by
  induction elements generalizing output with
  | nil => simp
  | cons element elements ih =>
      change
        ((elements.map elementInstruction).foldl
            (fun accumulator instruction => step (accumulator, instruction))
            (index, output ++ [(element, index)])) =
          (index, output ++ (element, index) :: elements.map fun x => (x, index))
      rw [ih (output ++ [(element, index)])]
      simp [List.append_assoc]

/-- The local executable has the expected ordered source semantics. -/
theorem pairsForSet_eq_map (index : Nat) (elements : List Nat) :
    pairsForSet (index, elements) = elements.map fun element => (element, index) := by
  change
    (((initInstruction index :: elements.map elementInstruction).foldl
        (fun accumulator instruction => step (accumulator, instruction))
        ((0 : Nat), ([] : List (Nat × Nat)))).2) =
      elements.map fun element => (element, index)
  rw [List.foldl_cons]
  simp [initInstruction, step]
  have folded := elementInstructions_fold index elements []
  simpa using congrArg Prod.snd folded

private theorem initInstruction_tmPolyTime :
    TMPolyTimeMap EncodedType.nat instructionEncodedType initInstruction := by
  have hFalse : TMPolyTimeMap EncodedType.nat EncodedType.bool (fun _ : Nat => false) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool false
  have hIndex : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  simpa [initInstruction, instructionEncodedType] using TMPolyTimeMap.prod_mk hFalse hIndex

private theorem elementInstruction_tmPolyTime :
    TMPolyTimeMap EncodedType.nat instructionEncodedType elementInstruction := by
  have hTrue : TMPolyTimeMap EncodedType.nat EncodedType.bool (fun _ : Nat => true) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool true
  have hElement : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  simpa [elementInstruction, instructionEncodedType] using TMPolyTimeMap.prod_mk hTrue hElement

private theorem instructions_tmPolyTime :
    TMPolyTimeMap instructionInputEncodedType instructionListEncodedType instructions := by
  let X := instructionInputEncodedType
  have hIndex : TMPolyTimeMap X EncodedType.nat (fun input : X.Carrier => input.1) := by
    simpa [X, instructionInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat setStructuredEncodedType
  have hSet : TMPolyTimeMap X setStructuredEncodedType (fun input : X.Carrier => input.2) := by
    simpa [X, instructionInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat setStructuredEncodedType
  have hInit : TMPolyTimeMap X instructionEncodedType
      (fun input : X.Carrier => initInstruction input.1) := by
    have hComp := TMPolyTimeMap.comp initInstruction_tmPolyTime hIndex
    simpa [Function.comp, X] using hComp
  have hElements : TMPolyTimeMap X instructionListEncodedType
      (fun input : X.Carrier => input.2.map elementInstruction) := by
    have hMap := TMPolyTimeMap.list_map elementInstruction_tmPolyTime
    have hComp := TMPolyTimeMap.comp hMap hSet
    simpa [Function.comp, instructionListEncodedType, setStructuredEncodedType, X] using hComp
  have hConsInput : TMPolyTimeMap X (EncodedType.prod instructionEncodedType instructionListEncodedType)
      (fun input : X.Carrier =>
        (initInstruction input.1, input.2.map elementInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hElements
  have hOut := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons instructionEncodedType) hConsInput
  simpa [Function.comp, instructions, instructionListEncodedType, X] using hOut

private theorem step_tmPolyTime :
    TMPolyTimeMap stepInputEncodedType accumulatorEncodedType step := by
  let X := stepInputEncodedType
  let Acc := accumulatorEncodedType
  let Instr := instructionEncodedType
  have hAcc : TMPolyTimeMap X Acc (fun input : X.Carrier => input.1) := by
    simpa [X, Acc, Instr, stepInputEncodedType] using TMPolyTimeMap.fst Acc Instr
  have hInstr : TMPolyTimeMap X Instr (fun input : X.Carrier => input.2) := by
    simpa [X, Acc, Instr, stepInputEncodedType] using TMPolyTimeMap.snd Acc Instr
  have hIndex : TMPolyTimeMap X EncodedType.nat (fun input : X.Carrier => input.1.1) := by
    have hFirst := TMPolyTimeMap.fst EncodedType.nat pairListEncodedType
    have hComp := TMPolyTimeMap.comp hFirst hAcc
    simpa [Function.comp, Acc, X] using hComp
  have hOutput : TMPolyTimeMap X pairListEncodedType (fun input : X.Carrier => input.1.2) := by
    have hSecond := TMPolyTimeMap.snd EncodedType.nat pairListEncodedType
    have hComp := TMPolyTimeMap.comp hSecond hAcc
    simpa [Function.comp, Acc, X] using hComp
  have hTag : TMPolyTimeMap X EncodedType.bool (fun input : X.Carrier => input.2.1) := by
    have hFirst := TMPolyTimeMap.fst EncodedType.bool EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFirst hInstr
    simpa [Function.comp, Instr, X] using hComp
  have hPayload : TMPolyTimeMap X EncodedType.nat (fun input : X.Carrier => input.2.2) := by
    have hSecond := TMPolyTimeMap.snd EncodedType.bool EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSecond hInstr
    simpa [Function.comp, Instr, X] using hComp
  have hEmpty : TMPolyTimeMap X pairListEncodedType
      (fun _ : X.Carrier => ([] : List (Nat × Nat))) :=
    TMPolyTimeMap.const X pairListEncodedType []
  have hFalse : TMPolyTimeMap X Acc
      (fun input : X.Carrier => (input.2.2, ([] : List (Nat × Nat)))) :=
    TMPolyTimeMap.prod_mk hPayload hEmpty
  have hPair : TMPolyTimeMap X pairEncodedType
      (fun input : X.Carrier => (input.2.2, input.1.1)) :=
    TMPolyTimeMap.prod_mk hPayload hIndex
  have hSingleton : TMPolyTimeMap X pairListEncodedType
      (fun input : X.Carrier => [(input.2.2, input.1.1)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton pairEncodedType) hPair
    simpa [Function.comp, pairListEncodedType] using hComp
  have hAppendInput : TMPolyTimeMap X (EncodedType.prod pairListEncodedType pairListEncodedType)
      (fun input : X.Carrier =>
        ((show List (Nat × Nat) from input.1.2),
          ([(input.2.2, input.1.1)] : List (Nat × Nat)))) :=
    TMPolyTimeMap.prod_mk hOutput hSingleton
  have hAppend : TMPolyTimeMap X pairListEncodedType
      (fun input : X.Carrier =>
        List.append (show List (Nat × Nat) from input.1.2)
          ([(input.2.2, input.1.1)] : List (Nat × Nat))) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append pairEncodedType) hAppendInput
    simpa [Function.comp, pairListEncodedType] using hComp
  have hTrue : TMPolyTimeMap X Acc
      (fun input : X.Carrier =>
        (input.1.1, List.append (show List (Nat × Nat) from input.1.2)
          ([(input.2.2, input.1.1)] : List (Nat × Nat)))) :=
    TMPolyTimeMap.prod_mk hIndex hAppend
  have hBranchInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun input : X.Carrier => (input.2.1, input)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranch : TMPolyTimeMap (EncodedType.prod EncodedType.bool X) Acc
      (fun input : Bool × X.Carrier =>
        match input.1 with
        | true =>
            (input.2.1.1,
              List.append (show List (Nat × Nat) from input.2.1.2)
                ([(input.2.2.2, input.2.1.1)] : List (Nat × Nat)))
        | false => (input.2.2.2, ([] : List (Nat × Nat)))) :=
    boolProduct_dispatch_tm_polytime X Acc
      (fFalse := fun input : X.Carrier => (input.2.2, ([] : List (Nat × Nat))))
      (fTrue := fun input : X.Carrier =>
        (input.1.1, List.append (show List (Nat × Nat) from input.1.2)
          ([(input.2.2, input.1.1)] : List (Nat × Nat))))
      hFalse hTrue
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext input
  rcases input with ⟨⟨index, output⟩, ⟨tag, payload⟩⟩
  cases tag <;> rfl

private theorem list_inputSize_append (X : EncodedType) :
    ∀ (first second : List X.Carrier),
      (EncodedType.list X).inputSize (first ++ second) =
        (EncodedType.list X).inputSize first + (EncodedType.list X).inputSize second
  | [], second => by
      simp [EncodedType.inputSize, EncodedType.list]
  | first :: rest, second => by
      rw [List.cons_append, EncodedType.inputSize_list_cons,
        EncodedType.inputSize_list_cons, list_inputSize_append X rest second]
      omega

private theorem pairList_inputSize_append_singleton
    (pairs : List (Nat × Nat)) (pair : Nat × Nat) :
    pairListEncodedType.inputSize (pairs ++ [pair]) =
      pairListEncodedType.inputSize pairs + pairEncodedType.inputSize pair + 1 := by
  have h := list_inputSize_append pairEncodedType pairs [pair]
  simpa [pairListEncodedType, EncodedType.inputSize_list_cons,
    EncodedType.inputSize_list_nil] using h

private theorem pairList_inputSize_nil :
    pairListEncodedType.inputSize ([] : List (Nat × Nat)) = 0 :=
  rfl

private theorem pairList_inputSize_cons (pair : Nat × Nat) (pairs : List (Nat × Nat)) :
    pairListEncodedType.inputSize (pair :: pairs) =
      pairEncodedType.inputSize pair + 1 + pairListEncodedType.inputSize pairs := by
  rw [EncodedType.inputSize_list_cons]

private theorem set_inputSize_nil :
    setStructuredEncodedType.inputSize ([] : List Nat) = 0 := by
  change (EncodedType.list EncodedType.nat).inputSize ([] : List Nat) = 0
  rfl

private theorem set_inputSize_cons (element : Nat) (elements : List Nat) :
    setStructuredEncodedType.inputSize (element :: elements) =
      EncodedType.nat.inputSize element + 1 + setStructuredEncodedType.inputSize elements := by
  change (EncodedType.list EncodedType.nat).inputSize (element :: elements) =
    EncodedType.nat.inputSize element + 1 + (EncodedType.list EncodedType.nat).inputSize elements
  rw [EncodedType.inputSize_list_cons]

private theorem accumulator_inputSize (index : Nat) (pairs : List (Nat × Nat)) :
    accumulatorEncodedType.inputSize (index, pairs) =
      EncodedType.nat.inputSize index + 1 + pairListEncodedType.inputSize pairs := by
  change (EncodedType.prod EncodedType.nat pairListEncodedType).inputSize (index, pairs) =
    EncodedType.nat.inputSize index + 1 + pairListEncodedType.inputSize pairs
  rw [EncodedType.inputSize_prod]

private theorem instruction_inputSize (instruction : Bool × Nat) :
    instructionEncodedType.inputSize instruction =
      EncodedType.bool.inputSize instruction.1 + 1 + EncodedType.nat.inputSize instruction.2 := by
  change (EncodedType.prod EncodedType.bool EncodedType.nat).inputSize instruction =
    EncodedType.bool.inputSize instruction.1 + 1 + EncodedType.nat.inputSize instruction.2
  rw [EncodedType.inputSize_prod]

private theorem pairsForSet_inputSize_aux (index : Nat) :
    ∀ elements : List Nat,
      pairListEncodedType.inputSize (elements.map fun element => (element, index)) ≤
        (index + 3) * elements.length + setStructuredEncodedType.inputSize elements
  | [] => by
      change pairListEncodedType.inputSize ([] : List (Nat × Nat)) ≤
        setStructuredEncodedType.inputSize ([] : List Nat)
      rw [pairList_inputSize_nil, set_inputSize_nil]
  | element :: elements => by
      have ih := pairsForSet_inputSize_aux index elements
      change pairListEncodedType.inputSize ((element, index) :: elements.map fun x => (x, index)) ≤
        (index + 3) * (element :: elements).length +
          setStructuredEncodedType.inputSize (element :: elements)
      rw [pairList_inputSize_cons, set_inputSize_cons]
      simp [pairEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_nat] at ih ⊢
      nlinarith

private theorem pairsForSet_inputSize_le (input : Nat × List Nat) :
    pairListEncodedType.inputSize (pairsForSet input) ≤
      4 * (instructionInputEncodedType.inputSize input) ^ 2 + 10 := by
  rcases input with ⟨index, elements⟩
  rw [pairsForSet_eq_map]
  let N := instructionInputEncodedType.inputSize (index, elements)
  let elementsSize := setStructuredEncodedType.inputSize elements
  have hAux := pairsForSet_inputSize_aux index elements
  have hLength : elements.length ≤ elementsSize := by
    simpa [elementsSize, setStructuredEncodedType] using
      ComplexityReduction.Karp21.HittingSet.encodedListLength_le_inputSize EncodedType.nat elements
  have hIndex : index + 1 ≤ N := by
    simp [N, EncodedType.inputSize_prod, EncodedType.inputSize_nat]
    omega
  have hElements : elementsSize ≤ N := by
    simp [N, elementsSize, EncodedType.inputSize_prod]
  have hBound :
      (index + 3) * elements.length + elementsSize ≤ 4 * N ^ 2 + 10 := by
    have hIndexThree : index + 3 ≤ N + 2 := by omega
    have hLengthN : elements.length ≤ N := hLength.trans hElements
    have hMultiply : (index + 3) * elements.length ≤ (N + 2) * N :=
      Nat.mul_le_mul hIndexThree hLengthN
    nlinarith [hMultiply, hElements, sq_nonneg (N : Int)]
  exact hAux.trans hBound

private def stepInv (bound : Nat) (accumulator : Nat × List (Nat × Nat)) : Prop :=
  accumulator.1 ≤ bound

private theorem step_growth
    (source : List (Bool × Nat)) (accumulator : Nat × List (Nat × Nat))
    (instruction : Bool × Nat)
    (hInv : stepInv (instructionListEncodedType.inputSize source) accumulator)
    (hInstruction : instructionEncodedType.inputSize instruction ≤
      instructionListEncodedType.inputSize source) :
    stepInv (instructionListEncodedType.inputSize source) (step (accumulator, instruction)) ∧
      accumulatorEncodedType.inputSize (step (accumulator, instruction)) ≤
        accumulatorEncodedType.inputSize accumulator +
          ((Polynomial.C 3 * Polynomial.X + Polynomial.C 10).eval
            (instructionListEncodedType.inputSize source)) := by
  rcases accumulator with ⟨index, output⟩
  rcases instruction with ⟨tag, payload⟩
  have hPayload : payload + 3 ≤ instructionListEncodedType.inputSize source := by
    have hPayloadRaw : 2 + (payload + 1) ≤ instructionListEncodedType.inputSize source := by
      simpa [instruction_inputSize, EncodedType.inputSize_bool,
        EncodedType.inputSize_nat] using hInstruction
    omega
  cases tag
  · constructor
    · simp [stepInv, step] at hInstruction ⊢
      omega
    · simp [step]
      rw [pairList_inputSize_nil]
      simp [EncodedType.inputSize_nat] at hInstruction ⊢
      omega
  · constructor
    · simpa [stepInv, step] using hInv
    · have hAppend := pairList_inputSize_append_singleton output (payload, index)
      have hIndexLe : index ≤ instructionListEncodedType.inputSize source := by
        simpa [stepInv] using hInv
      simp [step]
      rw [hAppend]
      simp [pairEncodedType, EncodedType.inputSize_prod,
        EncodedType.inputSize_nat] at hInv ⊢
      omega

private theorem accumulatorFromInstructions_tmPolyTime :
    TMPolyTimeMap instructionListEncodedType accumulatorEncodedType
      (fun instructions : List (Bool × Nat) =>
        instructions.foldl (fun accumulator instruction => step (accumulator, instruction))
          ((0 : Nat), ([] : List (Nat × Nat)))) := by
  rcases step_tmPolyTime with ⟨hStep⟩
  refine TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
    instructionEncodedType accumulatorEncodedType step
    ((0 : Nat), ([] : List (Nat × Nat))) hStep
    (Polynomial.C 2) (Polynomial.C 3 * Polynomial.X + Polynomial.C 10)
    stepInv ?_ ?_
  · intro instructions
    constructor
    · simp [stepInv]
    · rw [accumulator_inputSize, pairList_inputSize_nil]
      simp [EncodedType.inputSize_nat]
  · intro source accumulator instruction hInv hInstruction
    exact step_growth source accumulator instruction hInv hInstruction

private theorem pairsFromInstructions_tmPolyTime :
    TMPolyTimeMap instructionListEncodedType pairListEncodedType
      (fun instructions : List (Bool × Nat) =>
        (instructions.foldl (fun accumulator instruction => step (accumulator, instruction))
          ((0 : Nat), ([] : List (Nat × Nat)))).2) := by
  have hFold := accumulatorFromInstructions_tmPolyTime
  have hSnd := TMPolyTimeMap.snd EncodedType.nat pairListEncodedType
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, accumulatorEncodedType] using hComp

/-- Direct-TM evidence for the local membership-pair emitter. -/
theorem pairsForSet_tmPolyTime :
    TMPolyTimeMap instructionInputEncodedType pairListEncodedType pairsForSet := by
  have hComp := TMPolyTimeMap.comp pairsFromInstructions_tmPolyTime instructions_tmPolyTime
  simpa [Function.comp, pairsForSet] using hComp

/-- One source set paired with its independently retained right-vertex index. -/
abbrev indexedSetEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat setStructuredEncodedType

abbrev indexedSetListEncodedType : EncodedType :=
  EncodedType.list indexedSetEncodedType

abbrev indexedSetAccumulatorEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat indexedSetListEncodedType

abbrev indexedSetStepInputEncodedType : EncodedType :=
  EncodedType.prod indexedSetAccumulatorEncodedType setStructuredEncodedType

abbrev setFamilyInputEncodedType : EncodedType :=
  setFamilyStructuredEncodedType

/-- Append the next source set with the current canonical right-vertex identity. -/
def indexSetStep (input : (Nat × List (Nat × List Nat)) × List Nat) :
    Nat × List (Nat × List Nat) :=
  (input.1.1 + 1, input.1.2 ++ [(input.1.1, input.2)])

/-- Enumerate source sets from zero while retaining duplicate-set identities. -/
def indexedSetsFromZero (sets : List (List Nat)) : List (Nat × List Nat) :=
  (sets.foldl (fun accumulator set => indexSetStep (accumulator, set))
    ((0 : Nat), [])).2

/-- Local indexed source layout used only by this direct-TM construction. -/
def indexedFrom : Nat → List (List Nat) → List (Nat × List Nat)
  | _, [] => []
  | start, set :: sets => (start, set) :: indexedFrom (start + 1) sets

private theorem indexedSetsFrom_fold_eq :
    ∀ (sets : List (List Nat)) (next : Nat) (accumulator : List (Nat × List Nat)),
      sets.foldl (fun accumulator set => indexSetStep (accumulator, set)) (next, accumulator) =
        (next + sets.length, accumulator ++ indexedFrom next sets)
  | [], next, accumulator => by
      simp [indexedFrom]
  | set :: sets, next, accumulator => by
      rw [List.foldl_cons]
      simpa [indexSetStep, indexedFrom, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        indexedSetsFrom_fold_eq sets (next + 1) (accumulator ++ [(next, set)])

private theorem indexedSetsFromZero_eq_indexedFrom (sets : List (List Nat)) :
    indexedSetsFromZero sets = indexedFrom 0 sets := by
  have h := congrArg Prod.snd (indexedSetsFrom_fold_eq sets 0 ([] : List (Nat × List Nat)))
  simpa [indexedSetsFromZero] using h

private theorem encodedListLength_le_inputSize (X : EncodedType) :
    ∀ entries : List X.Carrier, entries.length ≤ (EncodedType.list X).inputSize entries
  | [] => by simp [EncodedType.inputSize, EncodedType.list]
  | _ :: entries => by
      have ih := encodedListLength_le_inputSize X entries
      rw [EncodedType.inputSize_list_cons]
      simp only [List.length_cons]
      omega

private theorem indexedSets_inputSize_aux :
    ∀ (sets : List (List Nat)) (start : Nat),
      indexedSetListEncodedType.inputSize (indexedFrom start sets) ≤
        setFamilyStructuredEncodedType.inputSize sets +
          sets.length * (start + sets.length + 2)
  | [], _start => by
      change (EncodedType.list indexedSetEncodedType).inputSize ([] : List (Nat × List Nat)) ≤
        (EncodedType.list setStructuredEncodedType).inputSize ([] : List (List Nat)) +
          0 * (_start + 0 + 2)
      have hLeft : (EncodedType.list indexedSetEncodedType).inputSize
          ([] : List (Nat × List Nat)) = 0 := by rfl
      have hRight : (EncodedType.list setStructuredEncodedType).inputSize
          ([] : List (List Nat)) = 0 := by rfl
      rw [hLeft, hRight]
      omega
  | set :: sets, start => by
      have ih := indexedSets_inputSize_aux sets (start + 1)
      change (EncodedType.list indexedSetEncodedType).inputSize
          ((start, set) :: indexedFrom (start + 1) sets) ≤
        (EncodedType.list setStructuredEncodedType).inputSize (set :: sets) +
          (set :: sets).length * (start + (set :: sets).length + 2)
      rw [EncodedType.inputSize_list_cons, EncodedType.inputSize_list_cons]
      have hEntry : indexedSetEncodedType.inputSize (start, set) =
          start + setStructuredEncodedType.inputSize set + 2 := by
        simp [indexedSetEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_nat]
        omega
      rw [hEntry]
      have ih' : (EncodedType.list indexedSetEncodedType).inputSize
          (indexedFrom (start + 1) sets) ≤
        (EncodedType.list setStructuredEncodedType).inputSize sets +
          sets.length * (start + 1 + sets.length + 2) := by
        simpa [indexedSetListEncodedType, setFamilyStructuredEncodedType] using ih
      simp only [List.length_cons]
      nlinarith

private theorem indexedSetsFromZero_inputSize_le (sets : List (List Nat)) :
    indexedSetListEncodedType.inputSize (indexedSetsFromZero sets) ≤
      4 * (setFamilyInputEncodedType.inputSize sets) ^ 2 + 10 := by
  rw [indexedSetsFromZero_eq_indexedFrom]
  let L := setFamilyStructuredEncodedType.inputSize sets
  have hAux := indexedSets_inputSize_aux sets 0
  have hLength : sets.length ≤ L := by
    simpa [L, setFamilyStructuredEncodedType] using
      encodedListLength_le_inputSize setStructuredEncodedType sets
  have hBound : L + sets.length * (0 + sets.length + 2) ≤ 4 * L ^ 2 + 10 := by
    have hLengthSquared : sets.length * sets.length ≤ L * L :=
      Nat.mul_le_mul hLength hLength
    have hTwoLength : 2 * sets.length ≤ 2 * L := Nat.mul_le_mul_left 2 hLength
    nlinarith [hLengthSquared, hTwoLength, Nat.zero_le L]
  calc
    indexedSetListEncodedType.inputSize (indexedFrom 0 sets) ≤
        L + sets.length * (0 + sets.length + 2) := by
          simpa [L, indexedSetListEncodedType, setFamilyStructuredEncodedType] using hAux
    _ ≤ 4 * L ^ 2 + 10 := hBound

private theorem indexSetStep_tmPolyTime :
    TMPolyTimeMap indexedSetStepInputEncodedType indexedSetAccumulatorEncodedType indexSetStep := by
  let X := indexedSetStepInputEncodedType
  let Acc := indexedSetAccumulatorEncodedType
  let Set := setStructuredEncodedType
  have hAcc : TMPolyTimeMap X Acc (fun input : X.Carrier => input.1) := by
    simpa [X, Acc, Set, indexedSetStepInputEncodedType] using TMPolyTimeMap.fst Acc Set
  have hSet : TMPolyTimeMap X Set (fun input : X.Carrier => input.2) := by
    simpa [X, Acc, Set, indexedSetStepInputEncodedType] using TMPolyTimeMap.snd Acc Set
  have hNextOfAcc : TMPolyTimeMap Acc EncodedType.nat (fun accumulator : Acc.Carrier => accumulator.1) := by
    simpa [Acc, indexedSetAccumulatorEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat indexedSetListEncodedType
  have hOutputOfAcc : TMPolyTimeMap Acc indexedSetListEncodedType
      (fun accumulator : Acc.Carrier => accumulator.2) := by
    simpa [Acc, indexedSetAccumulatorEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat indexedSetListEncodedType
  have hNext : TMPolyTimeMap X EncodedType.nat (fun input : X.Carrier => input.1.1) := by
    have hComp := TMPolyTimeMap.comp hNextOfAcc hAcc
    simpa [Function.comp] using hComp
  have hOutput : TMPolyTimeMap X indexedSetListEncodedType
      (fun input : X.Carrier => input.1.2) := by
    have hComp := TMPolyTimeMap.comp hOutputOfAcc hAcc
    simpa [Function.comp] using hComp
  have hNextSucc : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => Nat.succ input.1.1) := by
    have hComp := TMPolyTimeMap.comp (ComplexityReduction.nat_add_const_tm_polytime 1) hNext
    simpa [Function.comp, Nat.succ_eq_add_one] using hComp
  have hEntry : TMPolyTimeMap X indexedSetEncodedType
      (fun input : X.Carrier => ((input.1.1 : Nat), input.2)) := by
    have hPair := TMPolyTimeMap.prod_mk hNext hSet
    simpa [indexedSetEncodedType] using hPair
  have hSingleton : TMPolyTimeMap X indexedSetListEncodedType
      (fun input : X.Carrier => [((input.1.1 : Nat), input.2)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton indexedSetEncodedType) hEntry
    simpa [Function.comp, indexedSetListEncodedType] using hComp
  have hAppendInput : TMPolyTimeMap X
      (EncodedType.prod indexedSetListEncodedType indexedSetListEncodedType)
      (fun input : X.Carrier =>
        ((show List (Nat × List Nat) from input.1.2),
          ([((input.1.1 : Nat), input.2)] : List (Nat × List Nat)))) :=
    TMPolyTimeMap.prod_mk hOutput hSingleton
  have hAppend : TMPolyTimeMap X indexedSetListEncodedType
      (fun input : X.Carrier => List.append (show List (Nat × List Nat) from input.1.2)
        ([((input.1.1 : Nat), input.2)] : List (Nat × List Nat))) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append indexedSetEncodedType) hAppendInput
    simpa [Function.comp, indexedSetListEncodedType] using hComp
  have hPair : TMPolyTimeMap X indexedSetAccumulatorEncodedType
      (fun input : X.Carrier =>
        (Nat.succ input.1.1, List.append (show List (Nat × List Nat) from input.1.2)
          ([((input.1.1 : Nat), input.2)] : List (Nat × List Nat)))) :=
    TMPolyTimeMap.prod_mk hNextSucc hAppend
  simpa [indexSetStep, Nat.succ_eq_add_one] using hPair

private theorem indexedFrom_zero_append_singleton_set
    (pref : List (List Nat)) (set : List Nat) :
    indexedFrom 0 (pref ++ [set]) =
      indexedFrom 0 pref ++ [(pref.length, set)] := by
  induction pref with
  | nil => simp [indexedFrom]
  | cons head tail ih =>
      change (0, head) :: indexedFrom 1 (tail ++ [set]) =
        (0, head) :: indexedFrom 1 tail ++ [(Nat.succ tail.length, set)]
      congr
      have hShift : ∀ (start : Nat) (sets : List (List Nat)),
          indexedFrom (start + 1) sets =
            (indexedFrom start sets).map (fun entry => (entry.1 + 1, entry.2)) := by
        intro start sets
        induction sets generalizing start with
        | nil => simp [indexedFrom]
        | cons item sets ih' =>
            simp [indexedFrom, ih', Nat.add_comm, Nat.add_left_comm]
      have hShifted := congrArg (List.map fun entry : Nat × List Nat => (entry.1 + 1, entry.2)) ih
      simpa [hShift, List.map_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hShifted

private theorem indexSetStep_reachable_eq (pref : List (List Nat)) (set : List Nat) :
    indexSetStep ((pref.length, indexedFrom 0 pref), set) =
      ((pref ++ [set]).length, indexedFrom 0 (pref ++ [set])) := by
  rw [indexSetStep, indexedFrom_zero_append_singleton_set]
  simp

private noncomputable def indexedSetAccumulatorBound : Polynomial Nat :=
  Polynomial.C 10 * (Polynomial.X * Polynomial.X) + Polynomial.C 100

@[simp] private theorem indexedSetAccumulatorBound_eval (size : Nat) :
    indexedSetAccumulatorBound.eval size = 10 * (size * size) + 100 := by
  simp [indexedSetAccumulatorBound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]

private theorem indexedSetAccumulator_inputSize_le_source
    (pref remaining : List (List Nat)) :
    indexedSetAccumulatorEncodedType.inputSize (pref.length, indexedFrom 0 pref) ≤
      indexedSetAccumulatorBound.eval (setFamilyStructuredEncodedType.inputSize (pref ++ remaining)) := by
  let prefixSize := setFamilyStructuredEncodedType.inputSize pref
  let sourceSize := setFamilyStructuredEncodedType.inputSize (pref ++ remaining)
  have hAppend := list_inputSize_append setStructuredEncodedType pref remaining
  have hPrefixLeSource : prefixSize ≤ sourceSize := by
    simpa [prefixSize, sourceSize, setFamilyStructuredEncodedType] using Nat.le.intro hAppend.symm
  have hPrefixLength : pref.length ≤ prefixSize := by
    simpa [prefixSize, setFamilyStructuredEncodedType] using
      encodedListLength_le_inputSize setStructuredEncodedType pref
  have hOutput : indexedSetListEncodedType.inputSize (indexedFrom 0 pref) ≤
      4 * prefixSize ^ 2 + 10 := by
    have h := indexedSetsFromZero_inputSize_le pref
    simpa [indexedSetsFromZero_eq_indexedFrom, prefixSize, setFamilyInputEncodedType] using h
  have hSquare : prefixSize * prefixSize ≤ sourceSize * sourceSize :=
    Nat.mul_le_mul hPrefixLeSource hPrefixLeSource
  simp [indexedSetAccumulatorEncodedType, indexedSetListEncodedType,
    indexedSetAccumulatorBound_eval, EncodedType.inputSize_nat]
  nlinarith [hOutput, hPrefixLength, hPrefixLeSource, hSquare,
    Nat.zero_le prefixSize, Nat.zero_le sourceSize]

private noncomputable def indexedSetsFromZeroFoldTimePolynomial
    (hStep : Turing.TM2ComputableInPolyTime indexedSetStepInputEncodedType.encode
      indexedSetAccumulatorEncodedType.encode indexSetStep) : Polynomial Nat :=
  ComplexityReduction.TM2Programs.listFoldBoundedTimePolynomial hStep.tm
    indexedSetAccumulatorBound
    (hStep.time.comp (indexedSetAccumulatorBound + Polynomial.X + Polynomial.C 5))

private theorem indexedSetsFromZero_fold_loopTime_le
    (hStep : Turing.TM2ComputableInPolyTime indexedSetStepInputEncodedType.encode
      indexedSetAccumulatorEncodedType.encode indexSetStep)
    (source : List (List Nat)) :
    2 + ComplexityReduction.TM2Programs.listFoldTypedLoopTime setStructuredEncodedType
        indexedSetAccumulatorEncodedType indexSetStep hStep
        ((0 : Nat), ([] : List (Nat × List Nat))) source ≤
      (indexedSetsFromZeroFoldTimePolynomial hStep).eval
        (setFamilyStructuredEncodedType.inputSize source) := by
  let X := setStructuredEncodedType
  let Y := indexedSetAccumulatorEncodedType
  let N := setFamilyStructuredEncodedType.inputSize source
  let B := indexedSetAccumulatorBound.eval N
  let T := hStep.time.eval (B + N + 5)
  let C := ComplexityReduction.TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hLoopAux : ∀ (remaining pref : List (List Nat)),
      pref ++ remaining = source →
        ComplexityReduction.TM2Programs.listFoldTypedLoopTime X Y indexSetStep hStep
          (pref.length, indexedFrom 0 pref) remaining ≤
          C * (EncodedType.list X).inputSize remaining := by
    intro remaining
    induction remaining generalizing source with
    | nil =>
        intro pref _hSplit
        simp [ComplexityReduction.TM2Programs.listFoldTypedLoopTime]
    | cons current remaining ih =>
        intro pref hSplit
        have hRemainingN : (EncodedType.list X).inputSize (current :: remaining) ≤ N := by
          have hAppend := list_inputSize_append X pref (current :: remaining)
          have hSourceSize : N = (EncodedType.list X).inputSize pref +
              (EncodedType.list X).inputSize (current :: remaining) := by
            dsimp [N]
            rw [← hSplit]
            simpa [X, setFamilyStructuredEncodedType] using hAppend
          omega
        have hCurrentN : X.inputSize current ≤ N := by
          rw [EncodedType.inputSize_list_cons] at hRemainingN
          omega
        have hAccumulatorRaw := indexedSetAccumulator_inputSize_le_source pref (current :: remaining)
        have hAccumulator : Y.inputSize (pref.length, indexedFrom 0 pref) ≤ B := by
          simpa [Y, X, B, N, setFamilyStructuredEncodedType, hSplit] using hAccumulatorRaw
        let nextPrefix := pref ++ [current]
        have hSplitTail : nextPrefix ++ remaining = source := by
          dsimp [nextPrefix]
          simpa [List.append_assoc] using hSplit
        have hStepEq : indexSetStep ((pref.length, indexedFrom 0 pref), current) =
            (nextPrefix.length, indexedFrom 0 nextPrefix) := by
          dsimp [nextPrefix]
          exact indexSetStep_reachable_eq pref current
        have hNextRaw := indexedSetAccumulator_inputSize_le_source nextPrefix remaining
        have hNext : Y.inputSize (indexSetStep ((pref.length, indexedFrom 0 pref), current)) ≤ B := by
          rw [hStepEq]
          simpa [Y, X, B, N, setFamilyStructuredEncodedType, hSplitTail] using hNextRaw
        have hStepTime : hStep.time.eval ((EncodedType.prod Y X).inputSize
            ((pref.length, indexedFrom 0 pref), current)) ≤ T := by
          have hArgument : (EncodedType.prod Y X).inputSize
              ((pref.length, indexedFrom 0 pref), current) ≤ B + N + 5 := by
            rw [EncodedType.inputSize_prod]
            change Y.inputSize (pref.length, indexedFrom 0 pref) + 1 + X.inputSize current ≤
              B + N + 5
            omega
          exact ComplexityReduction.TM2Programs.polynomialNat_eval_mono hStep.time hArgument
        have hBlock : ComplexityReduction.TM2Programs.listFoldBlockTime hStep.tm
            (X.encode current).length
            (Y.encode (pref.length, indexedFrom 0 pref)).length
            (Y.encode (indexSetStep ((pref.length, indexedFrom 0 pref), current))).length
            (hStep.time.eval ((EncodedType.prod Y X).inputSize
              ((pref.length, indexedFrom 0 pref), current))) ≤
            C * (X.inputSize current + 1) := by
          exact ComplexityReduction.TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
            (by simpa [Y, EncodedType.inputSize] using hAccumulator)
            (by simpa [Y, EncodedType.inputSize] using hNext)
            hStepTime
        have hTail := ih source nextPrefix hSplitTail
        calc
          ComplexityReduction.TM2Programs.listFoldTypedLoopTime X Y indexSetStep hStep
              (pref.length, indexedFrom 0 pref) (current :: remaining) =
            ComplexityReduction.TM2Programs.listFoldTypedLoopTime X Y indexSetStep hStep
              (indexSetStep ((pref.length, indexedFrom 0 pref), current)) remaining +
            ComplexityReduction.TM2Programs.listFoldBlockTime hStep.tm (X.encode current).length
              (Y.encode (pref.length, indexedFrom 0 pref)).length
              (Y.encode (indexSetStep ((pref.length, indexedFrom 0 pref), current))).length
              (hStep.time.eval ((EncodedType.prod Y X).inputSize
                ((pref.length, indexedFrom 0 pref), current))) := by rfl
          _ = ComplexityReduction.TM2Programs.listFoldTypedLoopTime X Y indexSetStep hStep
              (nextPrefix.length, indexedFrom 0 nextPrefix) remaining +
            ComplexityReduction.TM2Programs.listFoldBlockTime hStep.tm (X.encode current).length
              (Y.encode (pref.length, indexedFrom 0 pref)).length
              (Y.encode (indexSetStep ((pref.length, indexedFrom 0 pref), current))).length
              (hStep.time.eval ((EncodedType.prod Y X).inputSize
                ((pref.length, indexedFrom 0 pref), current))) := by
                  rw [hStepEq]
                  rfl
          _ ≤ C * (EncodedType.list X).inputSize remaining + C * (X.inputSize current + 1) :=
            Nat.add_le_add hTail hBlock
          _ ≤ C * (EncodedType.list X).inputSize (current :: remaining) := by
            rw [EncodedType.inputSize_list_cons]
            nlinarith
  have hLoop : ComplexityReduction.TM2Programs.listFoldTypedLoopTime setStructuredEncodedType
      indexedSetAccumulatorEncodedType indexSetStep hStep
      ((0 : Nat), ([] : List (Nat × List Nat))) source ≤ C * N := by
    simpa [X, Y, N] using hLoopAux source [] (by rfl)
  have hTimeEval : (indexedSetsFromZeroFoldTimePolynomial hStep).eval N =
      (C + 2) * (N + 1) := by
    simp [indexedSetsFromZeroFoldTimePolynomial, B, T, C,
      ComplexityReduction.TM2Programs.listFoldBoundedTimePolynomial_eval,
      ComplexityReduction.TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_comp]
  rw [show setFamilyStructuredEncodedType.inputSize source = N from rfl, hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

private theorem indexedSetsFromZero_tmPolyTime :
    TMPolyTimeMap setFamilyInputEncodedType indexedSetListEncodedType indexedSetsFromZero := by
  rcases indexSetStep_tmPolyTime with ⟨hStep⟩
  have hFold : TMPolyTimeMap setFamilyInputEncodedType indexedSetAccumulatorEncodedType
      (fun sets : List (List Nat) =>
        sets.foldl (fun accumulator set => indexSetStep (accumulator, set))
          ((0 : Nat), [])) := by
    refine TMPolyTimeMap.list_foldl_typed setStructuredEncodedType indexedSetAccumulatorEncodedType
      indexSetStep ((0 : Nat), ([] : List (Nat × List Nat))) hStep
      (indexedSetsFromZeroFoldTimePolynomial hStep) ?_
    intro source
    exact indexedSetsFromZero_fold_loopTime_le hStep source
  have hSnd : TMPolyTimeMap indexedSetAccumulatorEncodedType indexedSetListEncodedType
      (fun accumulator : indexedSetAccumulatorEncodedType.Carrier => accumulator.2) := by
    simpa [indexedSetAccumulatorEncodedType] using TMPolyTimeMap.snd EncodedType.nat indexedSetListEncodedType
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, indexedSetsFromZero] using hComp

abbrev indexedMembershipScanInputEncodedType : EncodedType :=
  EncodedType.prod pairListEncodedType indexedSetEncodedType

/-- Add the members of one indexed set to the ordered incidence payload. -/
def appendIndexedSetPairs (input : List (Nat × Nat) × (Nat × List Nat)) : List (Nat × Nat) :=
  input.1 ++ pairsForSet input.2

/-- Flatten indexed source sets into their ordered incidence-pair payload. -/
def indexedMembershipPairs (entries : List (Nat × List Nat)) : List (Nat × Nat) :=
  entries.foldl (fun output entry => appendIndexedSetPairs (output, entry)) ([] : List (Nat × Nat))

private theorem appendIndexedSetPairs_eq_append
    (output : List (Nat × Nat)) (entry : Nat × List Nat) :
    appendIndexedSetPairs (output, entry) =
      output ++ entry.2.map (fun element => (element, entry.1)) := by
  rw [appendIndexedSetPairs, pairsForSet_eq_map]

private theorem indexedMembershipPairs_fold_eq_flatMap
    (entries : List (Nat × List Nat)) (output : List (Nat × Nat)) :
    entries.foldl (fun output entry => appendIndexedSetPairs (output, entry)) output =
      output ++ entries.flatMap (fun entry => entry.2.map (fun element => (element, entry.1))) := by
  induction entries generalizing output with
  | nil => simp
  | cons entry entries ih =>
      rw [List.foldl_cons, appendIndexedSetPairs_eq_append, ih]
      simp [List.append_assoc]

private theorem indexedMembershipPairs_eq_flatMap (entries : List (Nat × List Nat)) :
    indexedMembershipPairs entries =
      entries.flatMap (fun entry => entry.2.map (fun element => (element, entry.1))) := by
  simpa [indexedMembershipPairs] using
    indexedMembershipPairs_fold_eq_flatMap entries ([] : List (Nat × Nat))

/-- The recursive source semantics of ordered membership pairs. -/
def membershipPairsFrom : Nat → List (List Nat) → List (Nat × Nat)
  | _, [] => []
  | index, set :: sets => set.map (fun element => (element, index)) ++ membershipPairsFrom (index + 1) sets

/--
The reusable ordered incidence-pair emitter for a plain family of sets.

The family itself is the complete source payload: right-vertex identities are
assigned by position, so duplicate source sets remain distinct.
-/
def fromSetFamily (sets : List (List Nat)) : List (Nat × Nat) :=
  indexedMembershipPairs (indexedSetsFromZero sets)

private theorem appendIndexedSetPairs_tmPolyTime :
    TMPolyTimeMap indexedMembershipScanInputEncodedType pairListEncodedType appendIndexedSetPairs := by
  let X := indexedMembershipScanInputEncodedType
  have hOutput : TMPolyTimeMap X pairListEncodedType (fun input : X.Carrier => input.1) := by
    simpa [X, indexedMembershipScanInputEncodedType] using
      TMPolyTimeMap.fst pairListEncodedType indexedSetEncodedType
  have hEntry : TMPolyTimeMap X indexedSetEncodedType (fun input : X.Carrier => input.2) := by
    simpa [X, indexedMembershipScanInputEncodedType] using
      TMPolyTimeMap.snd pairListEncodedType indexedSetEncodedType
  have hPairs : TMPolyTimeMap X pairListEncodedType (fun input : X.Carrier => pairsForSet input.2) := by
    have hComp := TMPolyTimeMap.comp pairsForSet_tmPolyTime hEntry
    simpa [Function.comp, indexedSetEncodedType, instructionInputEncodedType, X] using hComp
  have hAppendInput : TMPolyTimeMap X (EncodedType.prod pairListEncodedType pairListEncodedType)
      (fun input : X.Carrier =>
        ((show List (Nat × Nat) from input.1), pairsForSet input.2)) :=
    TMPolyTimeMap.prod_mk hOutput hPairs
  have hAppend := TMPolyTimeMap.comp (TMPolyTimeMap.list_append pairEncodedType) hAppendInput
  simpa [Function.comp, pairListEncodedType, appendIndexedSetPairs, X] using hAppend

private theorem appendIndexedSetPairs_growth
    (source : List (Nat × List Nat)) (output : List (Nat × Nat)) (entry : Nat × List Nat)
    (hEntry : indexedSetEncodedType.inputSize entry ≤ indexedSetListEncodedType.inputSize source) :
    pairListEncodedType.inputSize (appendIndexedSetPairs (output, entry)) ≤
      pairListEncodedType.inputSize output +
        ((Polynomial.C 4 * (Polynomial.X * Polynomial.X) + Polynomial.C 10).eval
          (indexedSetListEncodedType.inputSize source)) := by
  have hPairs := pairsForSet_inputSize_le entry
  have hPairsIndexed : pairListEncodedType.inputSize (pairsForSet entry) ≤
      4 * indexedSetEncodedType.inputSize entry ^ 2 + 10 := by
    simpa [instructionInputEncodedType, indexedSetEncodedType] using hPairs
  have hPower : indexedSetEncodedType.inputSize entry ^ 2 ≤
      indexedSetListEncodedType.inputSize source ^ 2 := Nat.pow_le_pow_left hEntry 2
  have hPairsSource : pairListEncodedType.inputSize (pairsForSet entry) ≤
      4 * indexedSetListEncodedType.inputSize source ^ 2 + 10 := by
    nlinarith [hPairsIndexed, hPower]
  change (EncodedType.list pairEncodedType).inputSize (output ++ pairsForSet entry) ≤
    pairListEncodedType.inputSize output +
      ((Polynomial.C 4 * (Polynomial.X * Polynomial.X) + Polynomial.C 10).eval
        (indexedSetListEncodedType.inputSize source))
  have hAppend : (EncodedType.list pairEncodedType).inputSize (output ++ pairsForSet entry) =
      pairListEncodedType.inputSize output + pairListEncodedType.inputSize (pairsForSet entry) := by
    simpa [pairListEncodedType] using
      list_inputSize_append pairEncodedType output (pairsForSet entry)
  rw [hAppend]
  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
  nlinarith [hPairsSource]

private theorem indexedMembershipPairs_tmPolyTime :
    TMPolyTimeMap indexedSetListEncodedType pairListEncodedType indexedMembershipPairs := by
  rcases appendIndexedSetPairs_tmPolyTime with ⟨hStep⟩
  have hFold : TMPolyTimeMap indexedSetListEncodedType pairListEncodedType
      (fun entries : List (Nat × List Nat) =>
        entries.foldl (fun output entry => appendIndexedSetPairs (output, entry))
          ([] : List (Nat × Nat))) := by
    refine TMPolyTimeMap.list_foldl_typed_growth_bounded
      indexedSetEncodedType pairListEncodedType appendIndexedSetPairs
      ([] : List (Nat × Nat)) hStep
      (Polynomial.C 0) (Polynomial.C 4 * (Polynomial.X * Polynomial.X) + Polynomial.C 10)
      ?_ ?_
    · intro _entries
      rw [pairList_inputSize_nil]
      simp
    · intro source output entry hEntry
      exact appendIndexedSetPairs_growth source output entry hEntry
  simpa [indexedMembershipPairs] using hFold

/-- Direct-TM evidence for the wrapper-free ordered set-family emitter. -/
theorem fromSetFamily_tmPolyTime :
    TMPolyTimeMap setFamilyInputEncodedType pairListEncodedType fromSetFamily := by
  have indexed : TMPolyTimeMap setFamilyInputEncodedType indexedSetListEncodedType
      indexedSetsFromZero :=
    indexedSetsFromZero_tmPolyTime
  have composed := TMPolyTimeMap.comp indexedMembershipPairs_tmPolyTime indexed
  simpa [fromSetFamily] using composed

/-- Source-local ordered membership pairs, before any concrete problem wrapper is introduced. -/
def fromSetSystem (input : SetSystemInput) : List (Nat × Nat) :=
  fromSetFamily input.2

private theorem indexedMembershipPairs_indexedFrom_eq_membershipPairsFrom
    (start : Nat) (sets : List (List Nat)) :
    indexedMembershipPairs (indexedFrom start sets) = membershipPairsFrom start sets := by
  rw [indexedMembershipPairs_eq_flatMap]
  induction sets generalizing start with
  | nil => simp [indexedFrom, membershipPairsFrom]
  | cons set sets ih =>
      simp [indexedFrom, membershipPairsFrom, ih]

theorem fromSetFamily_eq_membershipPairsFrom (sets : List (List Nat)) :
    fromSetFamily sets = membershipPairsFrom 0 sets := by
  rw [fromSetFamily, indexedSetsFromZero_eq_indexedFrom]
  exact indexedMembershipPairs_indexedFrom_eq_membershipPairsFrom 0 sets

theorem fromSetSystem_eq_membershipPairsFrom (input : SetSystemInput) :
    fromSetSystem input = membershipPairsFrom 0 input.2 := by
  exact fromSetFamily_eq_membershipPairsFrom input.2

/-- Direct-TM evidence for the entire clean source membership-pair calculation. -/
theorem fromSetSystem_tmPolyTime :
    TMPolyTimeMap setSystemStructuredEncodedType pairListEncodedType fromSetSystem := by
  have hSets : TMPolyTimeMap setSystemStructuredEncodedType setFamilyInputEncodedType
      (fun input : SetSystemInput => input.2) := by
    have hTuple := ComplexityReduction.Karp21.HittingSet.setSystemInputToTupleTMBackedMap.tm_polytime
    have hSnd := TMPolyTimeMap.snd EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTuple
    simpa [Function.comp, ComplexityReduction.Karp21.HittingSet.setSystemInputToTuple,
      setFamilyInputEncodedType] using hComp
  have hPairs := TMPolyTimeMap.comp fromSetFamily_tmPolyTime hSets
  simpa [Function.comp, fromSetSystem] using hPairs

end SetSystemMembershipPairs
end Domain
end ComplexityReduction
