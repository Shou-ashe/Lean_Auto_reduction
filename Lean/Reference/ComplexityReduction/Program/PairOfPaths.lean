/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Program.ContextListAll
import ComplexityReduction.Program.ContextListMap
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.StrictPairs
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.HittingSet.MembershipRunner
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.ListNat
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ListLookupTM
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipKnapsackBinary
import ComplexityReduction.Problems.Karp21.GraphAtoms
import Mathlib.Tactic

/-!
Reusable direct-TM checks for edge-index paths and pairs of such paths.

The implementation deliberately keeps parallel edges distinct: a path is a
list of edge indices, indexed lookup produces the aligned directed edges and
costs, and disjointness is checked on the indices themselves.
-/

namespace ComplexityReduction
namespace Program
namespace PairOfPaths

open ComplexityReduction
open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph
open ComplexityReduction.Karp21

abbrev natListEncodedType : EncodedType := setStructuredEncodedType

abbrev binaryNatListEncodedType : EncodedType :=
  EncodedType.list EncodedType.binaryNat

abbrev edgeEncodedType : EncodedType := edgeStructuredEncodedType

abbrev edgeListEncodedType : EncodedType := edgeListStructuredEncodedType

/-- Boolean equality on unary naturals, kept explicit across encoded carriers. -/
def natEqBool (input : Nat × Nat) : Bool :=
  decide (input.1 = input.2)

@[simp] theorem natEqBool_eq_true_iff (input : Nat × Nat) :
    natEqBool input = true ↔ input.1 = input.2 := by
  simp [natEqBool]

theorem natEqBool_tmPolyTime :
    TMPolyTimeMap (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.bool natEqBool := by
  simpa [natEqBool] using TMPolyTimeMap.nat_eq

/-! ### Index bounds and indexed edges -/

/-- Check one edge index against a retained edge-count context. -/
def indexBoundBool (input : Nat × Nat) : Bool :=
  natLtBool (input.2, input.1)

@[simp] theorem indexBoundBool_eq_true_iff (input : Nat × Nat) :
    indexBoundBool input = true ↔ input.2 < input.1 := by
  simp [indexBoundBool, natLtBool]

theorem indexBoundBool_tmPolyTime :
    TMPolyTimeMap (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.bool indexBoundBool := by
  let X := EncodedType.prod EncodedType.nat EncodedType.nat
  have first : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have second : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have swapped : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : X.Carrier => (input.2, input.1)) :=
    TMPolyTimeMap.prod_mk second first
  have composed := TMPolyTimeMap.comp natLtBool_tm_polytime swapped
  simpa [Function.comp, indexBoundBool, X] using composed

/-- Require every path entry to be a valid edge index. -/
def allIndicesBoundBool (input : Nat × List Nat) : Bool :=
  ContextListAll.executable
    (C := EncodedType.nat) (X := EncodedType.nat)
    indexBoundBool input

theorem allIndicesBoundBool_eq_true_iff (edgeCount : Nat) (path : List Nat) :
    allIndicesBoundBool (edgeCount, path) = true ↔
      ∀ index ∈ path, index < edgeCount := by
  simpa [allIndicesBoundBool, indexBoundBool_eq_true_iff] using
    (ContextListAll.executable_eq_true_iff
      (C := EncodedType.nat) (X := EncodedType.nat)
      indexBoundBool edgeCount path)

theorem allIndicesBoundBool_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat natListEncodedType)
      EncodedType.bool allIndicesBoundBool := by
  simpa [allIndicesBoundBool, natListEncodedType] using
    ContextListAll.executable_tmPolyTime
      (C := EncodedType.nat) (X := EncodedType.nat)
      indexBoundBool indexBoundBool_tmPolyTime

/-- Total lookup of an edge by an edge index. -/
def edgeAtIndex (input : List (Nat × Nat) × Nat) : Nat × Nat :=
  input.1.getD input.2 (0, 0)

theorem edgeAtIndex_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod edgeListEncodedType EncodedType.nat)
      edgeEncodedType edgeAtIndex := by
  simpa [edgeAtIndex, edgeEncodedType, edgeListEncodedType,
    EncodedListLookup.getD] using
      EncodedListLookup.getD_tm_polytime edgeEncodedType ((0 : Nat), (0 : Nat))

/-- Replace every edge index by its aligned total edge lookup. -/
def indexedEdges (input : List (Nat × Nat) × List Nat) : List (Nat × Nat) :=
  (contextListMapExecutable
      (C := edgeListEncodedType) (X := EncodedType.nat) input).map edgeAtIndex

theorem indexedEdges_eq_map (edges : List (Nat × Nat)) (path : List Nat) :
    indexedEdges (edges, path) =
      path.map fun index => edges.getD index (0, 0) := by
  have attached := contextListMapExecutable_eq_map
    (C := edgeListEncodedType) (X := EncodedType.nat) edges path
  calc
    indexedEdges (edges, path) =
        (path.map fun index => (edges, index)).map edgeAtIndex := by
          exact congrArg (List.map edgeAtIndex) attached
    _ = path.map fun index => edges.getD index (0, 0) := by
      simp [edgeAtIndex, List.map_map, Function.comp_def]

theorem indexedEdges_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod edgeListEncodedType natListEncodedType)
      edgeListEncodedType indexedEdges := by
  have attached := contextListMapExecutable_tmPolyTime
    edgeListEncodedType EncodedType.nat
  have mapped := TMPolyTimeMap.list_map edgeAtIndex_tmPolyTime
  have composed := TMPolyTimeMap.comp mapped attached
  simpa [indexedEdges, Function.comp, natListEncodedType,
    edgeListEncodedType, edgeEncodedType] using composed

/-! ### Directed endpoint chain fold -/

/-- A chain over already-looked-up directed edges. -/
def EndpointChain : Nat → List (Nat × Nat) → Nat → Prop
  | current, [], target => current = target
  | current, edge :: rest, target =>
      edge.1 = current ∧ EndpointChain edge.2 rest target

abbrev chainAccumulatorEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.bool

abbrev chainInstructionEncodedType : EncodedType :=
  EncodedType.sum EncodedType.nat edgeEncodedType

abbrev chainInstructionListEncodedType : EncodedType :=
  EncodedType.list chainInstructionEncodedType

abbrev chainInputEncodedType : EncodedType :=
  EncodedType.prod
    (EncodedType.prod EncodedType.nat EncodedType.nat)
    edgeListEncodedType

/-- Advance the current vertex through one already-looked-up edge. -/
def chainEdgeStep
    (input : (Nat × Bool) × (Nat × Nat)) : Nat × Bool :=
  (input.2.2,
    graphBoolAndPair (input.1.2, natEqBool (input.2.1, input.1.1)))

theorem chainEdgeStep_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod chainAccumulatorEncodedType edgeEncodedType)
      chainAccumulatorEncodedType chainEdgeStep := by
  let X := EncodedType.prod chainAccumulatorEncodedType edgeEncodedType
  have accumulator : TMPolyTimeMap X chainAccumulatorEncodedType
      (fun input : X.Carrier => input.1) := by
    simpa [X] using TMPolyTimeMap.fst chainAccumulatorEncodedType edgeEncodedType
  have edge : TMPolyTimeMap X edgeEncodedType
      (fun input : X.Carrier => input.2) := by
    simpa [X] using TMPolyTimeMap.snd chainAccumulatorEncodedType edgeEncodedType
  have current : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.1.1) := by
    have projected := TMPolyTimeMap.fst EncodedType.nat EncodedType.bool
    have composed := TMPolyTimeMap.comp projected accumulator
    simpa [Function.comp, chainAccumulatorEncodedType, X] using composed
  have ok : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier => input.1.2) := by
    have projected := TMPolyTimeMap.snd EncodedType.nat EncodedType.bool
    have composed := TMPolyTimeMap.comp projected accumulator
    simpa [Function.comp, chainAccumulatorEncodedType, X] using composed
  have edgeSource : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.2.1) := by
    have projected := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have composed := TMPolyTimeMap.comp projected edge
    simpa [Function.comp, edgeEncodedType, X] using composed
  have edgeTarget : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.2.2) := by
    have projected := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have composed := TMPolyTimeMap.comp projected edge
    simpa [Function.comp, edgeEncodedType, X] using composed
  have equalityInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : X.Carrier => (input.2.1, input.1.1)) :=
    TMPolyTimeMap.prod_mk edgeSource current
  have equality : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier => natEqBool (input.2.1, input.1.1)) := by
    have composed := TMPolyTimeMap.comp natEqBool_tmPolyTime equalityInput
    simpa [Function.comp] using composed
  have checkedInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : X.Carrier =>
        (input.1.2, natEqBool (input.2.1, input.1.1))) :=
    TMPolyTimeMap.prod_mk ok equality
  have checked : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier =>
        graphBoolAndPair (input.1.2, natEqBool (input.2.1, input.1.1))) := by
    have composed := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime checkedInput
    simpa [Function.comp] using composed
  have output := TMPolyTimeMap.prod_mk edgeTarget checked
  simpa [chainEdgeStep, chainAccumulatorEncodedType, X] using output

/-- Load a source vertex, then consume directed edges. -/
def chainInstructionStep
    (input : (Nat × Bool) × (Nat ⊕ (Nat × Nat))) : Nat × Bool :=
  match input.2 with
  | Sum.inl source => (source, true)
  | Sum.inr edge => chainEdgeStep (input.1, edge)

theorem chainInstructionStep_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod chainAccumulatorEncodedType chainInstructionEncodedType)
      chainAccumulatorEncodedType chainInstructionStep := by
  let X := EncodedType.prod chainAccumulatorEncodedType chainInstructionEncodedType
  have leftBranch : TMPolyTimeMap
      EncodedType.nat
      chainAccumulatorEncodedType
      (fun source : Nat => (source, true)) := by
    have source : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
      TMPolyTimeMap.id EncodedType.nat
    have truth : TMPolyTimeMap EncodedType.nat EncodedType.bool
        (fun _source : Nat => true) :=
      TMPolyTimeMap.const EncodedType.nat EncodedType.bool true
    simpa [chainAccumulatorEncodedType] using TMPolyTimeMap.prod_mk source truth
  have rightBranch : TMPolyTimeMap
      (EncodedType.prod chainAccumulatorEncodedType edgeEncodedType)
      chainAccumulatorEncodedType
      (fun input : (Nat × Bool) × (Nat × Nat) => chainEdgeStep input) :=
    chainEdgeStep_tmPolyTime
  have dispatch := prodSumChoice_tm_polytime
    chainAccumulatorEncodedType EncodedType.nat edgeEncodedType
  have branches := TMPolyTimeMap.sum_elim leftBranch rightBranch
  have composed := TMPolyTimeMap.comp branches dispatch
  convert composed using 1
  funext input
  rcases input with ⟨accumulator, instruction⟩
  cases instruction <;> rfl

/-- Instruction stream with one dynamic-source header. -/
def chainInstructions (input : Nat × List (Nat × Nat)) :
    List (Nat ⊕ (Nat × Nat)) :=
  Sum.inl input.1 :: input.2.map Sum.inr

theorem chainInstructions_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat edgeListEncodedType)
      chainInstructionListEncodedType chainInstructions := by
  let X := EncodedType.prod EncodedType.nat edgeListEncodedType
  have source : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.nat edgeListEncodedType
  have edges : TMPolyTimeMap X edgeListEncodedType
      (fun input : X.Carrier => input.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.nat edgeListEncodedType
  have sourceInstruction : TMPolyTimeMap X chainInstructionEncodedType
      (fun input : X.Carrier => Sum.inl input.1) := by
    have injected := TMPolyTimeMap.inl EncodedType.nat edgeEncodedType
    have composed := TMPolyTimeMap.comp injected source
    simpa [Function.comp, chainInstructionEncodedType] using composed
  have sourceSingleton : TMPolyTimeMap X chainInstructionListEncodedType
      (fun input : X.Carrier => [Sum.inl input.1]) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton chainInstructionEncodedType) sourceInstruction
    simpa [Function.comp, chainInstructionListEncodedType] using composed
  have edgeInstruction : TMPolyTimeMap edgeEncodedType chainInstructionEncodedType
      (fun edge : edgeEncodedType.Carrier => Sum.inr edge) := by
    simpa [chainInstructionEncodedType] using
      TMPolyTimeMap.inr EncodedType.nat edgeEncodedType
  have edgeInstructions : TMPolyTimeMap X chainInstructionListEncodedType
      (fun input : X.Carrier => input.2.map Sum.inr) := by
    have mapped := TMPolyTimeMap.list_map edgeInstruction
    have composed := TMPolyTimeMap.comp mapped edges
    simpa [Function.comp, chainInstructionListEncodedType,
      edgeListEncodedType] using composed
  have appendInput : TMPolyTimeMap X
      (EncodedType.prod chainInstructionListEncodedType
        chainInstructionListEncodedType)
      (fun input : X.Carrier => ([Sum.inl input.1], input.2.map Sum.inr)) :=
    TMPolyTimeMap.prod_mk sourceSingleton edgeInstructions
  have appended := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append chainInstructionEncodedType) appendInput
  simpa [Function.comp, chainInstructions, chainInstructionListEncodedType, X] using appended

def chainInitialAccumulator : Nat × Bool :=
  (0, true)

@[simp] theorem chainInstruction_inputSize_inl (source : Nat) :
    chainInstructionEncodedType.inputSize (Sum.inl source) = source + 2 := by
  unfold chainInstructionEncodedType EncodedType.inputSize EncodedType.sum
  change
    ([Sum.inl false] ++
      (EncodedType.nat.encode source).map
        (fun symbol => Sum.inr (Sum.inl symbol))).length = _
  rw [List.length_append, List.length_singleton, List.length_map]
  change 1 + EncodedType.nat.inputSize source = _
  rw [EncodedType.inputSize_nat]
  omega

@[simp] theorem edgeEncodedType_inputSize (left right : Nat) :
    edgeEncodedType.inputSize (left, right) = left + right + 3 := by
  simp [edgeEncodedType, edgeStructuredEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_nat]
  omega

@[simp] theorem chainInstruction_inputSize_inr (left right : Nat) :
    chainInstructionEncodedType.inputSize (Sum.inr (left, right)) =
      left + right + 4 := by
  unfold chainInstructionEncodedType EncodedType.inputSize EncodedType.sum
  change
    ([Sum.inl true] ++
      (edgeEncodedType.encode (left, right)).map
        (fun symbol => Sum.inr (Sum.inr symbol))).length = _
  rw [List.length_append, List.length_singleton, List.length_map]
  change 1 + edgeEncodedType.inputSize (left, right) = _
  rw [edgeEncodedType_inputSize]
  omega

private theorem chainInstructionStep_growth
    (source : List (Nat ⊕ (Nat × Nat))) (accumulator : Nat × Bool)
    (instruction : Nat ⊕ (Nat × Nat))
    (instructionBound :
      chainInstructionEncodedType.inputSize instruction ≤
        chainInstructionListEncodedType.inputSize source) :
    chainAccumulatorEncodedType.inputSize
        (chainInstructionStep (accumulator, instruction)) ≤
      chainAccumulatorEncodedType.inputSize accumulator +
        (Polynomial.X + Polynomial.C 10).eval
          (chainInstructionListEncodedType.inputSize source) := by
  rcases accumulator with ⟨current, ok⟩
  rcases instruction with sourceVertex | edge
  · have payloadBound : sourceVertex + 2 ≤
        chainInstructionListEncodedType.inputSize source := by
      calc
        sourceVertex + 2 =
            chainInstructionEncodedType.inputSize (Sum.inl sourceVertex) :=
          (chainInstruction_inputSize_inl sourceVertex).symm
        _ ≤ chainInstructionListEncodedType.inputSize source := instructionBound
    simp [chainInstructionStep, chainAccumulatorEncodedType,
      chainInstructionListEncodedType, EncodedType.inputSize_prod,
      EncodedType.inputSize_bool, Polynomial.eval_add, Polynomial.eval_X]
      at payloadBound ⊢
    omega
  · rcases edge with ⟨left, right⟩
    have payloadBound : left + right + 4 ≤
        chainInstructionListEncodedType.inputSize source := by
      calc
        left + right + 4 =
            chainInstructionEncodedType.inputSize (Sum.inr (left, right)) :=
          (chainInstruction_inputSize_inr left right).symm
        _ ≤ chainInstructionListEncodedType.inputSize source := instructionBound
    simp [chainInstructionStep, chainEdgeStep, chainAccumulatorEncodedType,
      chainInstructionListEncodedType, EncodedType.inputSize_prod,
      EncodedType.inputSize_bool, graphBoolAndPair,
      Polynomial.eval_add, Polynomial.eval_X] at payloadBound ⊢
    omega

private theorem chainFold_tmPolyTime :
    TMPolyTimeMap chainInstructionListEncodedType chainAccumulatorEncodedType
      (fun instructions : List (Nat ⊕ (Nat × Nat)) =>
        instructions.foldl
          (fun accumulator instruction =>
            chainInstructionStep (accumulator, instruction))
          chainInitialAccumulator) := by
  rcases chainInstructionStep_tmPolyTime with ⟨stepTM⟩
  refine TMPolyTimeMap.list_foldl_typed_growth_bounded
    chainInstructionEncodedType chainAccumulatorEncodedType
    chainInstructionStep chainInitialAccumulator stepTM
    (Polynomial.C 3) (Polynomial.X + Polynomial.C 10) ?_ ?_
  · intro instructions
    simp [chainInitialAccumulator, chainAccumulatorEncodedType,
      EncodedType.inputSize_prod, EncodedType.inputSize_bool]
  · intro source accumulator instruction instructionBound
    exact chainInstructionStep_growth source accumulator instruction instructionBound

/-- Finish one dynamic-source endpoint-chain fold at the target vertex. -/
def finishChain (input : (Nat × Bool) × Nat) : Bool :=
  graphBoolAndPair (input.1.2, natEqBool (input.1.1, input.2))

theorem finishChain_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod chainAccumulatorEncodedType EncodedType.nat)
      EncodedType.bool finishChain := by
  let X := EncodedType.prod chainAccumulatorEncodedType EncodedType.nat
  have accumulator : TMPolyTimeMap X chainAccumulatorEncodedType
      (fun input : X.Carrier => input.1) := by
    simpa [X] using TMPolyTimeMap.fst chainAccumulatorEncodedType EncodedType.nat
  have target : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.2) := by
    simpa [X] using TMPolyTimeMap.snd chainAccumulatorEncodedType EncodedType.nat
  have current : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.1.1) := by
    have projected := TMPolyTimeMap.fst EncodedType.nat EncodedType.bool
    have composed := TMPolyTimeMap.comp projected accumulator
    simpa [Function.comp, chainAccumulatorEncodedType, X] using composed
  have ok : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier => input.1.2) := by
    have projected := TMPolyTimeMap.snd EncodedType.nat EncodedType.bool
    have composed := TMPolyTimeMap.comp projected accumulator
    simpa [Function.comp, chainAccumulatorEncodedType, X] using composed
  have equalityInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : X.Carrier => (input.1.1, input.2)) :=
    TMPolyTimeMap.prod_mk current target
  have equality : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier => natEqBool (input.1.1, input.2)) := by
    have composed := TMPolyTimeMap.comp natEqBool_tmPolyTime equalityInput
    simpa [Function.comp] using composed
  have checkedInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : X.Carrier =>
        (input.1.2, natEqBool (input.1.1, input.2))) :=
    TMPolyTimeMap.prod_mk ok equality
  have composed := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime checkedInput
  simpa [Function.comp, finishChain] using composed

/-- Direct endpoint-chain checker over a list of already-looked-up edges. -/
def chainEndpointsBool
    (input : (Nat × Nat) × List (Nat × Nat)) : Bool :=
  let instructions := chainInstructions (input.1.1, input.2)
  let accumulator := instructions.foldl
    (fun current instruction => chainInstructionStep (current, instruction))
    chainInitialAccumulator
  finishChain (accumulator, input.1.2)

private theorem chainFold_eq_true_iff
    (edges : List (Nat × Nat)) (current target : Nat) (ok : Bool) :
    finishChain
        (edges.foldl
          (fun accumulator edge => chainEdgeStep (accumulator, edge))
          (current, ok), target) = true ↔
      ok = true ∧ EndpointChain current edges target := by
  induction edges generalizing current ok with
  | nil =>
      rw [finishChain, graphBoolAndPair_eq_true_iff, natEqBool_eq_true_iff]
      rfl
  | cons edge edges inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis]
      rw [chainEdgeStep, graphBoolAndPair_eq_true_iff, natEqBool_eq_true_iff]
      simp only [EndpointChain, and_assoc]

private theorem chainMappedFold_eq (edges : List (Nat × Nat))
    (accumulator : Nat × Bool) :
    (edges.map Sum.inr).foldl
        (fun current instruction => chainInstructionStep (current, instruction))
        accumulator =
      edges.foldl
        (fun current edge => chainEdgeStep (current, edge)) accumulator := by
  induction edges generalizing accumulator with
  | nil => rfl
  | cons edge edges inductionHypothesis =>
      simp only [List.map_cons, List.foldl_cons, chainInstructionStep]
      exact inductionHypothesis (chainEdgeStep (accumulator, edge))

theorem chainEndpointsBool_eq_true_iff
    (source target : Nat) (edges : List (Nat × Nat)) :
    chainEndpointsBool ((source, target), edges) = true ↔
      EndpointChain source edges target := by
  change finishChain
      ((chainInstructions (source, edges)).foldl
        (fun current instruction => chainInstructionStep (current, instruction))
        chainInitialAccumulator, target) = true ↔ _
  simp only [chainInstructions, List.foldl_cons]
  rw [chainMappedFold_eq]
  simpa using chainFold_eq_true_iff edges source target true

theorem chainEndpointsBool_tmPolyTime :
    TMPolyTimeMap chainInputEncodedType EncodedType.bool chainEndpointsBool := by
  let X := chainInputEncodedType
  have terminals : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : X.Carrier => input.1) := by
    simpa [X, chainInputEncodedType] using
      TMPolyTimeMap.fst
        (EncodedType.prod EncodedType.nat EncodedType.nat) edgeListEncodedType
  have edges : TMPolyTimeMap X edgeListEncodedType
      (fun input : X.Carrier => input.2) := by
    simpa [X, chainInputEncodedType] using
      TMPolyTimeMap.snd
        (EncodedType.prod EncodedType.nat EncodedType.nat) edgeListEncodedType
  have source : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.1.1) := by
    have projected := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have composed := TMPolyTimeMap.comp projected terminals
    simpa [Function.comp, X] using composed
  have target : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.1.2) := by
    have projected := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have composed := TMPolyTimeMap.comp projected terminals
    simpa [Function.comp, X] using composed
  have instructionInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat edgeListEncodedType)
      (fun input : X.Carrier => (input.1.1, input.2)) :=
    TMPolyTimeMap.prod_mk source edges
  have instructions : TMPolyTimeMap X chainInstructionListEncodedType
      (fun input : X.Carrier => chainInstructions (input.1.1, input.2)) := by
    have composed := TMPolyTimeMap.comp chainInstructions_tmPolyTime instructionInput
    simpa [Function.comp] using composed
  have accumulator : TMPolyTimeMap X chainAccumulatorEncodedType
      (fun input : X.Carrier =>
        (chainInstructions (input.1.1, input.2)).foldl
          (fun current instruction => chainInstructionStep (current, instruction))
          chainInitialAccumulator) := by
    have composed := TMPolyTimeMap.comp chainFold_tmPolyTime instructions
    simpa [Function.comp] using composed
  have finishInput : TMPolyTimeMap X
      (EncodedType.prod chainAccumulatorEncodedType EncodedType.nat)
      (fun input : X.Carrier =>
        ((chainInstructions (input.1.1, input.2)).foldl
            (fun current instruction => chainInstructionStep (current, instruction))
            chainInitialAccumulator,
          input.1.2)) :=
    TMPolyTimeMap.prod_mk accumulator target
  have composed := TMPolyTimeMap.comp finishChain_tmPolyTime finishInput
  simpa [Function.comp, chainEndpointsBool, X] using composed

/-! ### Complete edge-index chain check -/

/-- The generic edge-list form of the public recursive edge-index chain. -/
def EdgeIndexChain (edges : List (Nat × Nat)) : Nat → List Nat → Nat → Prop
  | current, [], target => current = target
  | current, index :: rest, target =>
      index < edges.length ∧
        (edges.getD index (0, 0)).1 = current ∧
        EdgeIndexChain edges (edges.getD index (0, 0)).2 rest target

abbrev edgeChainInputEncodedType : EncodedType :=
  EncodedType.prod edgeListEncodedType
    (EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.nat natListEncodedType))

private theorem endpointChain_indexedEdges_iff
    (edges : List (Nat × Nat)) (path : List Nat)
    (current target : Nat)
    (bounds : ∀ index ∈ path, index < edges.length) :
    EndpointChain current (indexedEdges (edges, path)) target ↔
      EdgeIndexChain edges current path target := by
  rw [indexedEdges_eq_map]
  induction path generalizing current with
  | nil =>
      rfl
  | cons index path inductionHypothesis =>
      have indexBound : index < edges.length := bounds index (by simp)
      have restBounds : ∀ candidate ∈ path, candidate < edges.length := by
        intro candidate member
        exact bounds candidate (by simp [member])
      simp only [List.map_cons, EndpointChain, EdgeIndexChain]
      rw [inductionHypothesis
        (current := (edges.getD index (0, 0)).2) restBounds]
      simp [indexBound]

/-- Check bounds and directed endpoint continuity for one edge-index list. -/
def edgeChainBool
    (input : List (Nat × Nat) × Nat × Nat × List Nat) : Bool :=
  graphBoolAndPair
    (allIndicesBoundBool (input.1.length, input.2.2.2),
      chainEndpointsBool
        ((input.2.1, input.2.2.1), indexedEdges (input.1, input.2.2.2)))

theorem edgeChainBool_eq_true_iff
    (edges : List (Nat × Nat)) (source target : Nat) (path : List Nat) :
    edgeChainBool (edges, source, target, path) = true ↔
      EdgeIndexChain edges source path target := by
  rw [edgeChainBool, graphBoolAndPair_eq_true_iff,
    allIndicesBoundBool_eq_true_iff, chainEndpointsBool_eq_true_iff]
  constructor
  · rintro ⟨bounds, chain⟩
    exact (endpointChain_indexedEdges_iff edges path source target bounds).1 chain
  · intro chain
    have bounds : ∀ index ∈ path, index < edges.length := by
      induction path generalizing source with
      | nil => simp
      | cons index path inductionHypothesis =>
          rcases chain with ⟨indexBound, sourceMatch, restChain⟩
          intro candidate member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact indexBound
          · exact inductionHypothesis
              (source := (edges.getD index (0, 0)).2) restChain candidate member
    exact ⟨bounds,
      (endpointChain_indexedEdges_iff edges path source target bounds).2 chain⟩

theorem edgeChainBool_tmPolyTime :
    TMPolyTimeMap edgeChainInputEncodedType EncodedType.bool edgeChainBool := by
  let X := edgeChainInputEncodedType
  let Tail := EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat natListEncodedType)
  let TargetPath := EncodedType.prod EncodedType.nat natListEncodedType
  have edges : TMPolyTimeMap X edgeListEncodedType
      (fun input : X.Carrier => input.1) := by
    simpa [X, edgeChainInputEncodedType, Tail] using
      TMPolyTimeMap.fst edgeListEncodedType Tail
  have tail : TMPolyTimeMap X Tail
      (fun input : X.Carrier => input.2) := by
    simpa [X, edgeChainInputEncodedType, Tail] using
      TMPolyTimeMap.snd edgeListEncodedType Tail
  have source : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.2.1) := by
    have projected := TMPolyTimeMap.fst EncodedType.nat TargetPath
    have composed := TMPolyTimeMap.comp projected tail
    simpa [Function.comp, Tail, TargetPath, X] using composed
  have targetPath : TMPolyTimeMap X TargetPath
      (fun input : X.Carrier => input.2.2) := by
    have projected := TMPolyTimeMap.snd EncodedType.nat TargetPath
    have composed := TMPolyTimeMap.comp projected tail
    simpa [Function.comp, Tail, TargetPath, X] using composed
  have target : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.2.2.1) := by
    have projected := TMPolyTimeMap.fst EncodedType.nat natListEncodedType
    have composed := TMPolyTimeMap.comp projected targetPath
    simpa [Function.comp, TargetPath, X] using composed
  have path : TMPolyTimeMap X natListEncodedType
      (fun input : X.Carrier => input.2.2.2) := by
    have projected := TMPolyTimeMap.snd EncodedType.nat natListEncodedType
    have composed := TMPolyTimeMap.comp projected targetPath
    simpa [Function.comp, TargetPath, X] using composed
  have edgeCount : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.1.length) := by
    have composed := TMPolyTimeMap.comp
      (HittingSet.listLengthTMBackedMap edgeEncodedType).tm_polytime edges
    simpa [Function.comp, edgeListEncodedType] using composed
  have boundsInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat natListEncodedType)
      (fun input : X.Carrier => (input.1.length, input.2.2.2)) :=
    TMPolyTimeMap.prod_mk edgeCount path
  have bounds : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier =>
        allIndicesBoundBool (input.1.length, input.2.2.2)) := by
    have composed := TMPolyTimeMap.comp allIndicesBoundBool_tmPolyTime boundsInput
    simpa [Function.comp] using composed
  have indexedInput : TMPolyTimeMap X
      (EncodedType.prod edgeListEncodedType natListEncodedType)
      (fun input : X.Carrier => (input.1, input.2.2.2)) :=
    TMPolyTimeMap.prod_mk edges path
  have lookedUp : TMPolyTimeMap X edgeListEncodedType
      (fun input : X.Carrier => indexedEdges (input.1, input.2.2.2)) := by
    have composed := TMPolyTimeMap.comp indexedEdges_tmPolyTime indexedInput
    simpa [Function.comp] using composed
  have terminals : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : X.Carrier => (input.2.1, input.2.2.1)) :=
    TMPolyTimeMap.prod_mk source target
  have chainInput : TMPolyTimeMap X chainInputEncodedType
      (fun input : X.Carrier =>
        ((input.2.1, input.2.2.1), indexedEdges (input.1, input.2.2.2))) := by
    simpa [chainInputEncodedType] using TMPolyTimeMap.prod_mk terminals lookedUp
  have chain : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier =>
        chainEndpointsBool
          ((input.2.1, input.2.2.1), indexedEdges (input.1, input.2.2.2))) := by
    have composed := TMPolyTimeMap.comp chainEndpointsBool_tmPolyTime chainInput
    simpa [Function.comp] using composed
  have outputInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : X.Carrier =>
        (allIndicesBoundBool (input.1.length, input.2.2.2),
          chainEndpointsBool
            ((input.2.1, input.2.2.1), indexedEdges (input.1, input.2.2.2)))) :=
    TMPolyTimeMap.prod_mk bounds chain
  have composed := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime outputInput
  simpa [Function.comp, edgeChainBool, X] using composed

/-! ### Edge-index simplicity (`List.Nodup`) -/

/-- Compare the two path entries selected by a strict index pair. -/
def pairDifferentBool (input : List Nat × (Nat × Nat)) : Bool :=
  Bool.not
    (natEqBool
      (input.1.getD input.2.1 0, input.1.getD input.2.2 0))

theorem pairDifferentBool_eq_true_iff
    (path : List Nat) (pair : Nat × Nat) :
    pairDifferentBool (path, pair) = true ↔
      path.getD pair.1 0 ≠ path.getD pair.2 0 := by
  simp [pairDifferentBool, natEqBool]

theorem pairDifferentBool_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod natListEncodedType vertexPairEncodedType)
      EncodedType.bool pairDifferentBool := by
  let X := EncodedType.prod natListEncodedType vertexPairEncodedType
  have path : TMPolyTimeMap X natListEncodedType
      (fun input : X.Carrier => input.1) := by
    simpa [X] using TMPolyTimeMap.fst natListEncodedType vertexPairEncodedType
  have pair : TMPolyTimeMap X vertexPairEncodedType
      (fun input : X.Carrier => input.2) := by
    simpa [X] using TMPolyTimeMap.snd natListEncodedType vertexPairEncodedType
  have firstIndex : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.2.1) := by
    have projected := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have composed := TMPolyTimeMap.comp projected pair
    simpa [Function.comp, vertexPairEncodedType, X] using composed
  have secondIndex : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.2.2) := by
    have projected := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have composed := TMPolyTimeMap.comp projected pair
    simpa [Function.comp, vertexPairEncodedType, X] using composed
  have firstInput : TMPolyTimeMap X
      (EncodedType.prod natListEncodedType EncodedType.nat)
      (fun input : X.Carrier => (input.1, input.2.1)) :=
    TMPolyTimeMap.prod_mk path firstIndex
  have secondInput : TMPolyTimeMap X
      (EncodedType.prod natListEncodedType EncodedType.nat)
      (fun input : X.Carrier => (input.1, input.2.2)) :=
    TMPolyTimeMap.prod_mk path secondIndex
  have firstValue : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.1.getD input.2.1 (0 : Nat)) := by
    have composed := TMPolyTimeMap.comp
      (EncodedListLookup.getD_tm_polytime EncodedType.nat (0 : Nat)) firstInput
    simpa [Function.comp, natListEncodedType, setStructuredEncodedType,
      EncodedListLookup.getD] using composed
  have secondValue : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.1.getD input.2.2 (0 : Nat)) := by
    have composed := TMPolyTimeMap.comp
      (EncodedListLookup.getD_tm_polytime EncodedType.nat (0 : Nat)) secondInput
    simpa [Function.comp, natListEncodedType, setStructuredEncodedType,
      EncodedListLookup.getD] using composed
  have equalityInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : X.Carrier =>
        (input.1.getD input.2.1 (0 : Nat),
          input.1.getD input.2.2 (0 : Nat))) :=
    TMPolyTimeMap.prod_mk firstValue secondValue
  have equality : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier =>
        natEqBool
          (input.1.getD input.2.1 (0 : Nat),
            input.1.getD input.2.2 (0 : Nat))) := by
    have composed := TMPolyTimeMap.comp natEqBool_tmPolyTime equalityInput
    simpa [Function.comp] using composed
  have composed := TMPolyTimeMap.comp TMPolyTimeMap.bool_not equality
  simpa [Function.comp, pairDifferentBool, X] using composed

/-- Check all strict path-position pairs against the same retained path. -/
def allPairsDifferentBool
    (input : List Nat × List (Nat × Nat)) : Bool :=
  ContextListAll.executable
    (C := natListEncodedType) (X := vertexPairEncodedType)
    pairDifferentBool input

theorem allPairsDifferentBool_eq_true_iff
    (path : List Nat) (pairs : List (Nat × Nat)) :
    allPairsDifferentBool (path, pairs) = true ↔
      ∀ pair ∈ pairs, pairDifferentBool (path, pair) = true := by
  exact ContextListAll.executable_eq_true_iff
    (C := natListEncodedType) (X := vertexPairEncodedType)
    pairDifferentBool path pairs

theorem allPairsDifferentBool_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod natListEncodedType vertexPairListEncodedType)
      EncodedType.bool allPairsDifferentBool := by
  simpa [allPairsDifferentBool, vertexPairListEncodedType] using
    ContextListAll.executable_tmPolyTime
      (C := natListEncodedType) (X := vertexPairEncodedType)
      pairDifferentBool pairDifferentBool_tmPolyTime

/-- Enumerate all strict position pairs and require different path entries. -/
def pathNodupBool (path : List Nat) : Bool :=
  allPairsDifferentBool (path, strictNatPairCandidates path.length)

theorem pathNodupBool_eq_true_iff (path : List Nat) :
    pathNodupBool path = true ↔ path.Nodup := by
  rw [pathNodupBool, allPairsDifferentBool_eq_true_iff]
  constructor
  · intro checked
    apply List.nodup_iff_injective_getElem.mpr
    intro left right equalValues
    by_contra differentIndices
    have valuesDifferent : path.getD left.1 0 ≠ path.getD right.1 0 := by
      rcases Nat.lt_trichotomy left.1 right.1 with leftBefore | same | rightBefore
      · exact (pairDifferentBool_eq_true_iff path (left.1, right.1)).1
          (checked (left.1, right.1)
            ((mem_strictNatPairCandidates_iff path.length (left.1, right.1)).2
              ⟨left.2, right.2, leftBefore⟩))
      · exact False.elim (differentIndices (Fin.ext same))
      · exact fun equality =>
          (pairDifferentBool_eq_true_iff path (right.1, left.1)).1
            (checked (right.1, left.1)
              ((mem_strictNatPairCandidates_iff path.length (right.1, left.1)).2
                ⟨right.2, left.2, rightBefore⟩)) equality.symm
    rw [List.getD_eq_getElem (l := path) (d := 0) left.2,
      List.getD_eq_getElem (l := path) (d := 0) right.2] at valuesDifferent
    exact valuesDifferent equalValues
  · intro nodup pair pairMember
    rcases (mem_strictNatPairCandidates_iff path.length pair).1 pairMember with
      ⟨leftBound, rightBound, leftBefore⟩
    apply (pairDifferentBool_eq_true_iff path pair).2
    rw [List.getD_eq_getElem (l := path) (d := 0) leftBound,
      List.getD_eq_getElem (l := path) (d := 0) rightBound]
    intro equality
    have indexEquality :
        (⟨pair.1, leftBound⟩ : Fin path.length) =
          ⟨pair.2, rightBound⟩ :=
      (List.nodup_iff_injective_getElem.mp nodup) equality
    exact Nat.ne_of_lt leftBefore (congrArg Fin.val indexEquality)

theorem pathNodupBool_tmPolyTime :
    TMPolyTimeMap natListEncodedType EncodedType.bool pathNodupBool := by
  let X := natListEncodedType
  have path : TMPolyTimeMap X natListEncodedType id :=
    TMPolyTimeMap.id X
  have length : TMPolyTimeMap X EncodedType.nat
      (fun path : List Nat => path.length) := by
    simpa [X, natListEncodedType, setStructuredEncodedType] using
      (HittingSet.listLengthTMBackedMap EncodedType.nat).tm_polytime
  have pairs : TMPolyTimeMap X vertexPairListEncodedType
      (fun path : List Nat => strictNatPairCandidates path.length) := by
    have composed := TMPolyTimeMap.comp strictNatPairCandidates_tm_polytime length
    simpa [Function.comp, X] using composed
  have input : TMPolyTimeMap X
      (EncodedType.prod natListEncodedType vertexPairListEncodedType)
      (fun path : List Nat => (path, strictNatPairCandidates path.length)) :=
    TMPolyTimeMap.prod_mk path pairs
  have composed := TMPolyTimeMap.comp allPairsDifferentBool_tmPolyTime input
  simpa [Function.comp, pathNodupBool, X] using composed

/-! ### Aligned binary path cost -/

/-- Total lookup of one aligned binary edge cost. -/
def costAtIndex (input : List Nat × Nat) : Nat :=
  input.1.getD input.2 0

theorem costAtIndex_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod binaryNatListEncodedType EncodedType.nat)
      EncodedType.binaryNat costAtIndex := by
  simpa [costAtIndex, binaryNatListEncodedType,
    EncodedListLookup.getD] using
      EncodedListLookup.getD_tm_polytime EncodedType.binaryNat (0 : Nat)

/-- Look up all aligned costs selected by a path. -/
def indexedCosts (input : List Nat × List Nat) : List Nat :=
  (contextListMapExecutable
      (C := binaryNatListEncodedType) (X := EncodedType.nat) input).map costAtIndex

theorem indexedCosts_eq_map (costs path : List Nat) :
    indexedCosts (costs, path) =
      path.map fun index => costs.getD index 0 := by
  have attached := contextListMapExecutable_eq_map
    (C := binaryNatListEncodedType) (X := EncodedType.nat) costs path
  calc
    indexedCosts (costs, path) =
        (path.map fun index => (costs, index)).map costAtIndex := by
          exact congrArg (List.map costAtIndex) attached
    _ = path.map fun index => costs.getD index 0 := by
      simp [costAtIndex, List.map_map, Function.comp_def]

theorem indexedCosts_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod binaryNatListEncodedType natListEncodedType)
      binaryNatListEncodedType indexedCosts := by
  have attached := contextListMapExecutable_tmPolyTime
    binaryNatListEncodedType EncodedType.nat
  have mapped := TMPolyTimeMap.list_map costAtIndex_tmPolyTime
  have composed := TMPolyTimeMap.comp mapped attached
  simpa [indexedCosts, Function.comp, natListEncodedType,
    binaryNatListEncodedType] using composed

/-- Direct-TM path cost under a binary aligned cost list. -/
def pathCost (input : List Nat × List Nat) : Nat :=
  (indexedCosts input).sum

theorem pathCost_eq_map_sum (costs path : List Nat) :
    pathCost (costs, path) =
      (path.map fun index => costs.getD index 0).sum := by
  rw [pathCost, indexedCosts_eq_map]

theorem pathCost_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod binaryNatListEncodedType natListEncodedType)
      EncodedType.binaryNat pathCost := by
  have composed := TMPolyTimeMap.comp
    Knapsack.binaryNatListSum_tm_polytime_sum indexedCosts_tmPolyTime
  simpa [Function.comp, pathCost] using composed

abbrev boundedCostInputEncodedType : EncodedType :=
  EncodedType.prod binaryNatListEncodedType
    (EncodedType.prod EncodedType.binaryNat natListEncodedType)

/-- Compare one computed binary path cost with a retained binary bound. -/
def boundedCostBool (input : List Nat × Nat × List Nat) : Bool :=
  Knapsack.binaryNatLeBool (pathCost (input.1, input.2.2), input.2.1)

theorem boundedCostBool_eq_true_iff
    (costs : List Nat) (bound : Nat) (path : List Nat) :
    boundedCostBool (costs, bound, path) = true ↔
      pathCost (costs, path) ≤ bound := by
  exact Knapsack.binaryNatLeBool_eq_true_iff _

theorem boundedCostBool_tmPolyTime :
    TMPolyTimeMap boundedCostInputEncodedType EncodedType.bool boundedCostBool := by
  let X := boundedCostInputEncodedType
  let Tail := EncodedType.prod EncodedType.binaryNat natListEncodedType
  have costs : TMPolyTimeMap X binaryNatListEncodedType
      (fun input : X.Carrier => input.1) := by
    simpa [X, boundedCostInputEncodedType, Tail] using
      TMPolyTimeMap.fst binaryNatListEncodedType Tail
  have tail : TMPolyTimeMap X Tail
      (fun input : X.Carrier => input.2) := by
    simpa [X, boundedCostInputEncodedType, Tail] using
      TMPolyTimeMap.snd binaryNatListEncodedType Tail
  have bound : TMPolyTimeMap X EncodedType.binaryNat
      (fun input : X.Carrier => input.2.1) := by
    have projected := TMPolyTimeMap.fst EncodedType.binaryNat natListEncodedType
    have composed := TMPolyTimeMap.comp projected tail
    simpa [Function.comp, Tail, X] using composed
  have path : TMPolyTimeMap X natListEncodedType
      (fun input : X.Carrier => input.2.2) := by
    have projected := TMPolyTimeMap.snd EncodedType.binaryNat natListEncodedType
    have composed := TMPolyTimeMap.comp projected tail
    simpa [Function.comp, Tail, X] using composed
  have costInput : TMPolyTimeMap X
      (EncodedType.prod binaryNatListEncodedType natListEncodedType)
      (fun input : X.Carrier => (input.1, input.2.2)) :=
    TMPolyTimeMap.prod_mk costs path
  have cost : TMPolyTimeMap X EncodedType.binaryNat
      (fun input : X.Carrier => pathCost (input.1, input.2.2)) := by
    have composed := TMPolyTimeMap.comp pathCost_tmPolyTime costInput
    simpa [Function.comp] using composed
  have compareInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      (fun input : X.Carrier =>
        (pathCost (input.1, input.2.2), input.2.1)) :=
    TMPolyTimeMap.prod_mk cost bound
  have composed := TMPolyTimeMap.comp
    Knapsack.binaryNatLeBool_tm_polytime compareInput
  simpa [Function.comp, boundedCostBool, X] using composed

/-! ### Edge-disjoint path pairs -/

/-- One retained path does not contain the supplied edge index. -/
def absentFromPathBool (input : List Nat × Nat) : Bool :=
  Bool.not (HittingSet.setContainsBool (input.2, input.1))

theorem absentFromPathBool_eq_true_iff (path : List Nat) (index : Nat) :
    absentFromPathBool (path, index) = true ↔ index ∉ path := by
  by_cases member : index ∈ path
  · have found := (HittingSet.setContainsBool_eq_true_iff (index, path)).2 member
    simp [absentFromPathBool, found, member]
  · have missing : HittingSet.setContainsBool (index, path) = false := by
      cases result : HittingSet.setContainsBool (index, path)
      · rfl
      · exact False.elim (member
          ((HittingSet.setContainsBool_eq_true_iff (index, path)).1 result))
    simp [absentFromPathBool, missing, member]

theorem absentFromPathBool_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod natListEncodedType EncodedType.nat)
      EncodedType.bool absentFromPathBool := by
  let X := EncodedType.prod natListEncodedType EncodedType.nat
  have path : TMPolyTimeMap X natListEncodedType
      (fun input : X.Carrier => input.1) := by
    simpa [X] using TMPolyTimeMap.fst natListEncodedType EncodedType.nat
  have index : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.2) := by
    simpa [X] using TMPolyTimeMap.snd natListEncodedType EncodedType.nat
  have containsInput : TMPolyTimeMap X
      HittingSet.setContainsInstructionInputEncodedType
      (fun input : X.Carrier => (input.2, input.1)) := by
    simpa [HittingSet.setContainsInstructionInputEncodedType,
      natListEncodedType, setStructuredEncodedType] using
        TMPolyTimeMap.prod_mk index path
  have contains : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier => HittingSet.setContainsBool (input.2, input.1)) := by
    have composed := TMPolyTimeMap.comp HittingSet.setContainsBool_tm_polytime
      containsInput
    simpa [Function.comp] using composed
  have composed := TMPolyTimeMap.comp TMPolyTimeMap.bool_not contains
  simpa [Function.comp, absentFromPathBool, X] using composed

/-- Every edge index of the first path is absent from the second path. -/
def pathsDisjointBool (input : List Nat × List Nat) : Bool :=
  ContextListAll.executable
    (C := natListEncodedType) (X := EncodedType.nat)
    absentFromPathBool (input.2, input.1)

theorem pathsDisjointBool_eq_true_iff (left right : List Nat) :
    pathsDisjointBool (left, right) = true ↔
      ∀ index ∈ left, index ∉ right := by
  rw [pathsDisjointBool,
    ContextListAll.executable_eq_true_iff
      (C := natListEncodedType) (X := EncodedType.nat)
      absentFromPathBool right left]
  constructor
  · intro checked index member
    exact (absentFromPathBool_eq_true_iff right index).1 (checked index member)
  · intro disjoint index member
    exact (absentFromPathBool_eq_true_iff right index).2 (disjoint index member)

theorem pathsDisjointBool_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod natListEncodedType natListEncodedType)
      EncodedType.bool pathsDisjointBool := by
  let X := EncodedType.prod natListEncodedType natListEncodedType
  have left : TMPolyTimeMap X natListEncodedType
      (fun input : X.Carrier => input.1) := by
    simpa [X] using TMPolyTimeMap.fst natListEncodedType natListEncodedType
  have right : TMPolyTimeMap X natListEncodedType
      (fun input : X.Carrier => input.2) := by
    simpa [X] using TMPolyTimeMap.snd natListEncodedType natListEncodedType
  have swapped : TMPolyTimeMap X
      (EncodedType.prod natListEncodedType natListEncodedType)
      (fun input : X.Carrier => (input.2, input.1)) :=
    TMPolyTimeMap.prod_mk right left
  have all := ContextListAll.executable_tmPolyTime
    (C := natListEncodedType) (X := EncodedType.nat)
    absentFromPathBool absentFromPathBool_tmPolyTime
  have composed := TMPolyTimeMap.comp all swapped
  simpa [Function.comp, pathsDisjointBool, X] using composed

/-! ### One complete edge-index path -/

/-- Combine edge simplicity with the directed edge-index chain check. -/
def edgeIndexPathBool
    (input : List (Nat × Nat) × Nat × Nat × List Nat) : Bool :=
  graphBoolAndPair
    (pathNodupBool input.2.2.2, edgeChainBool input)

theorem edgeIndexPathBool_eq_true_iff
    (edges : List (Nat × Nat)) (source target : Nat) (path : List Nat) :
    edgeIndexPathBool (edges, source, target, path) = true ↔
      path.Nodup ∧ EdgeIndexChain edges source path target := by
  rw [edgeIndexPathBool, graphBoolAndPair_eq_true_iff,
    pathNodupBool_eq_true_iff, edgeChainBool_eq_true_iff]

theorem edgeIndexPathBool_tmPolyTime :
    TMPolyTimeMap edgeChainInputEncodedType EncodedType.bool edgeIndexPathBool := by
  let X := edgeChainInputEncodedType
  let Tail := EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat natListEncodedType)
  let TargetPath := EncodedType.prod EncodedType.nat natListEncodedType
  have tail : TMPolyTimeMap X Tail
      (fun input : X.Carrier => input.2) := by
    simpa [X, edgeChainInputEncodedType, Tail] using
      TMPolyTimeMap.snd edgeListEncodedType Tail
  have targetPath : TMPolyTimeMap X TargetPath
      (fun input : X.Carrier => input.2.2) := by
    have projected := TMPolyTimeMap.snd EncodedType.nat TargetPath
    have composed := TMPolyTimeMap.comp projected tail
    simpa [Function.comp, Tail, TargetPath, X] using composed
  have path : TMPolyTimeMap X natListEncodedType
      (fun input : X.Carrier => input.2.2.2) := by
    have projected := TMPolyTimeMap.snd EncodedType.nat natListEncodedType
    have composed := TMPolyTimeMap.comp projected targetPath
    simpa [Function.comp, TargetPath, X] using composed
  have simple : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier => pathNodupBool input.2.2.2) := by
    have composed := TMPolyTimeMap.comp pathNodupBool_tmPolyTime path
    simpa [Function.comp] using composed
  have chain : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier => edgeChainBool input) :=
    edgeChainBool_tmPolyTime
  have outputInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : X.Carrier =>
        (pathNodupBool input.2.2.2, edgeChainBool input)) :=
    TMPolyTimeMap.prod_mk simple chain
  have composed := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime outputInput
  simpa [Function.comp, edgeIndexPathBool, X] using composed

end PairOfPaths
end Program
end ComplexityReduction

assert_standard_axioms
  ComplexityReduction.Program.PairOfPaths.indexBoundBool_tmPolyTime,
  ComplexityReduction.Program.PairOfPaths.allIndicesBoundBool_tmPolyTime,
  ComplexityReduction.Program.PairOfPaths.indexedEdges_tmPolyTime,
  ComplexityReduction.Program.PairOfPaths.chainEndpointsBool_tmPolyTime,
  ComplexityReduction.Program.PairOfPaths.edgeChainBool_tmPolyTime,
  ComplexityReduction.Program.PairOfPaths.pairDifferentBool_tmPolyTime,
  ComplexityReduction.Program.PairOfPaths.pathNodupBool_tmPolyTime,
  ComplexityReduction.Program.PairOfPaths.pathCost_tmPolyTime,
  ComplexityReduction.Program.PairOfPaths.boundedCostBool_tmPolyTime,
  ComplexityReduction.Program.PairOfPaths.pathsDisjointBool_tmPolyTime,
  ComplexityReduction.Program.PairOfPaths.edgeIndexPathBool_tmPolyTime
