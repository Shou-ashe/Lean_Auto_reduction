/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.Authoring
import ComplexityReduction.Agent.Hardness.FiniteWitnessNative
import ComplexityReduction.AxiomGate
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.FiniteWitness
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.EdgeScan
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSteinerTreeEdgeScan
import ComplexityReduction.Problems.Karp21.HittingSetStandardTM
import ComplexityReduction.Presentation.ExactlyOneNeighbor
import Mathlib.Tactic

/-!
Exact public formalization and native-membership authoring packet for the
Spring 2015 Exactly-One-Neighbor qualifying-exam problem.

The benchmark endpoint is definitionally the production existential-witness
presentation.  The checker uses a `List Nat` certificate, checks both vertex
bounds, and scans the explicit graph edge list to require exactly one selected
neighbor for every required vertex.  No oracle declaration or hidden gold
route is imported by this module.
-/

namespace Benchmark.Hardness.Inputs.Quals.Spring2015ExactlyOneNeighbor

open ComplexityReduction
open ComplexityReduction.Encoding
open ComplexityReduction.Certificate
open ComplexityReduction.Program
open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph
open ComplexityReduction.Karp21
open ComplexityReduction.Agent.Hardness.FiniteWitness
open ComplexityReduction.Agent.Hardness.FiniteWitnessNative

/-- The exact public endpoint for the qualifying-exam problem. -/
@[complexity_reduction_ir_typed_problem]
abbrev problem : PresentedProblem :=
  ComplexityReduction.Presentation.ExactlyOneNeighbor.presentedProblem

abbrev source : PresentedProblem := problem

/-- The public benchmark predicate is exactly the legacy exam witness predicate. -/
theorem problem_accepts_iff (input : problem.Instance) :
    problem.accepts input ↔
      ∃ selected : List Nat,
        ComplexityReduction.ExactlyOneNeighborWitness input selected :=
  Iff.rfl

/-! ### One required vertex: count selected graph neighbors -/

abbrev natListEncodedType : EncodedType :=
  ComplexityReduction.Combinatorics.setStructuredEncodedType

abbrev edgeListEncodedType : EncodedType :=
  ComplexityReduction.Combinatorics.Graph.edgeListStructuredEncodedType

def neighborCountContextEncodedType : EncodedType :=
  EncodedType.prod edgeListEncodedType EncodedType.nat

def neighborCountAccEncodedType : EncodedType :=
  EncodedType.prod neighborCountContextEncodedType EncodedType.nat

def neighborCountInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool
    (EncodedType.prod neighborCountContextEncodedType EncodedType.nat)

def neighborCountInstructionListEncodedType : EncodedType :=
  EncodedType.list neighborCountInstructionEncodedType

def neighborCountInputEncodedType : EncodedType :=
  EncodedType.prod neighborCountContextEncodedType natListEncodedType

def neighborCountInitInstruction (context : List (Nat × Nat) × Nat) :
    Bool × ((List (Nat × Nat) × Nat) × Nat) :=
  (false, (context, 0))

def neighborCountElementInstruction (vertex : Nat) :
    Bool × ((List (Nat × Nat) × Nat) × Nat) :=
  (true, (([], 0), vertex))

def neighborCountInstructions
    (input : (List (Nat × Nat) × Nat) × List Nat) :
    List (Bool × ((List (Nat × Nat) × Nat) × Nat)) :=
  neighborCountInitInstruction input.1 ::
    input.2.map neighborCountElementInstruction

def neighborCountRunnerInit : (List (Nat × Nat) × Nat) × Nat :=
  (([], 0), 0)

def neighborCountStep
    (input : ((List (Nat × Nat) × Nat) × Nat) ×
      (Bool × ((List (Nat × Nat) × Nat) × Nat))) :
    (List (Nat × Nat) × Nat) × Nat :=
  if input.2.1 then
    if sourceHasUndirectedEdgeBool
        ((input.2.2.2, input.1.1.2), input.1.1.1) then
      (input.1.1, input.1.2 + 1)
    else
      input.1
  else
    (input.2.2.1, 0)

def neighborCountFromInstructions
    (instructions : List (Bool × ((List (Nat × Nat) × Nat) × Nat))) : Nat :=
  (instructions.foldl
    (fun acc instruction => neighborCountStep (acc, instruction))
    neighborCountRunnerInit).2

def neighborHitCount (graph : GraphInput) (required : Nat) : List Nat → Nat
  | [] => 0
  | selected :: rest =>
      (if sourceHasUndirectedEdgeBool ((selected, required), graph.edges) then 1 else 0) +
        neighborHitCount graph required rest

def neighborCount (input : (List (Nat × Nat) × Nat) × List Nat) : Nat :=
  neighborCountFromInstructions (neighborCountInstructions input)

def exactlyOneNeighborBool
    (input : (List (Nat × Nat) × Nat) × List Nat) : Bool :=
  ComplexityReduction.Karp21.SteinerTreeMembership.natEqBool
    (neighborCount input, 1)

theorem neighborCountElementInstructions_fold_eq
    (graph : GraphInput) (required count : Nat) (selected : List Nat) :
    ((selected.map neighborCountElementInstruction).foldl
      (fun acc instruction => neighborCountStep (acc, instruction))
      ((graph.edges, required), count)) =
        ((graph.edges, required), count + neighborHitCount graph required selected) := by
  induction selected generalizing count with
  | nil =>
      rfl
  | cons vertex rest ih =>
      rw [List.map_cons, List.foldl_cons]
      cases hEdge : sourceHasUndirectedEdgeBool ((vertex, required), graph.edges)
      · simp [neighborCountElementInstruction, neighborCountStep, hEdge,
          neighborHitCount]
        exact ih count
      · simp [neighborCountElementInstruction, neighborCountStep, hEdge,
          neighborHitCount]
        simpa [Nat.add_assoc] using ih (count + 1)

theorem neighborCount_eq_hitCount
    (graph : GraphInput) (required : Nat) (selected : List Nat) :
    neighborCount ((graph.edges, required), selected) =
      neighborHitCount graph required selected := by
  change
    ((neighborCountInitInstruction (graph.edges, required) ::
      selected.map neighborCountElementInstruction).foldl
      (fun acc instruction => neighborCountStep (acc, instruction))
      neighborCountRunnerInit).2 = _
  rw [List.foldl_cons]
  simpa [neighborCountRunnerInit, neighborCountInitInstruction, neighborCountStep] using
    congrArg Prod.snd
      (neighborCountElementInstructions_fold_eq graph required 0 selected)

theorem neighborHitCount_eq_zero_iff
    (graph : GraphInput) (required : Nat) (selected : List Nat) :
    neighborHitCount graph required selected = 0 ↔
      ∀ vertex ∈ selected, ¬ HasUndirectedEdge graph vertex required := by
  induction selected with
  | nil =>
      simp [neighborHitCount]
  | cons vertex rest ih =>
      by_cases hEdge : HasUndirectedEdge graph vertex required
      · have hBool :
          sourceHasUndirectedEdgeBool ((vertex, required), graph.edges) = true :=
          (sourceHasUndirectedEdgeBool_graph_eq_true_iff graph vertex required).2 hEdge
        simp [neighborHitCount, hBool, hEdge]
      · have hBool :
          sourceHasUndirectedEdgeBool ((vertex, required), graph.edges) = false := by
          cases h : sourceHasUndirectedEdgeBool ((vertex, required), graph.edges)
          · rfl
          · exact False.elim
              (hEdge ((sourceHasUndirectedEdgeBool_graph_eq_true_iff graph vertex required).1 h))
        simp [neighborHitCount, hBool, hEdge, ih]

theorem neighborHitCount_eq_one_implies
    (graph : GraphInput) (required : Nat) (selected : List Nat)
    (hCount : neighborHitCount graph required selected = 1) :
    HasExactlyOneNeighborIn graph selected required := by
  induction selected with
  | nil =>
      simp [neighborHitCount] at hCount
  | cons vertex rest ih =>
      by_cases hEdge : HasUndirectedEdge graph vertex required
      · have hBool :
          sourceHasUndirectedEdgeBool ((vertex, required), graph.edges) = true :=
          (sourceHasUndirectedEdgeBool_graph_eq_true_iff graph vertex required).2 hEdge
        have hTailZero : neighborHitCount graph required rest = 0 := by
          simp [neighborHitCount, hBool] at hCount
          omega
        refine ⟨vertex, by simp, hEdge, ?_⟩
        intro other hOther hOtherEdge
        simp at hOther
        rcases hOther with rfl | hOtherTail
        · rfl
        · exact False.elim
            ((neighborHitCount_eq_zero_iff graph required rest).1 hTailZero
              other hOtherTail hOtherEdge)
      · have hBool :
          sourceHasUndirectedEdgeBool ((vertex, required), graph.edges) = false := by
          cases h : sourceHasUndirectedEdgeBool ((vertex, required), graph.edges)
          · rfl
          · exact False.elim
              (hEdge ((sourceHasUndirectedEdgeBool_graph_eq_true_iff graph vertex required).1 h))
        have hTailCount : neighborHitCount graph required rest = 1 := by
          simpa [neighborHitCount, hBool] using hCount
        rcases ih hTailCount with ⟨witness, hWitness, hWitnessEdge, hUnique⟩
        refine ⟨witness, by simp [hWitness], hWitnessEdge, ?_⟩
        intro other hOther hOtherEdge
        simp at hOther
        rcases hOther with rfl | hOtherTail
        · exact False.elim (hEdge hOtherEdge)
        · exact hUnique other hOtherTail hOtherEdge

theorem neighborHitCount_eq_one_of_nodup
    (graph : GraphInput) (required : Nat) (selected : List Nat)
    (hNodup : selected.Nodup)
    (hExactlyOne : HasExactlyOneNeighborIn graph selected required) :
    neighborHitCount graph required selected = 1 := by
  induction selected with
  | nil =>
      rcases hExactlyOne with ⟨witness, hWitness, _⟩
      simp at hWitness
  | cons vertex rest ih =>
      have hRestNodup : rest.Nodup := hNodup.of_cons
      by_cases hEdge : HasUndirectedEdge graph vertex required
      · have hBool :
          sourceHasUndirectedEdgeBool ((vertex, required), graph.edges) = true :=
          (sourceHasUndirectedEdgeBool_graph_eq_true_iff graph vertex required).2 hEdge
        rcases hExactlyOne with ⟨witness, hWitness, hWitnessEdge, hUnique⟩
        have hVertexEq : vertex = witness :=
          hUnique vertex (by simp) hEdge
        have hNoTail : ∀ other ∈ rest, ¬ HasUndirectedEdge graph other required := by
          intro other hOther hOtherEdge
          have hOtherEq : other = witness :=
            hUnique other (by simp [hOther]) hOtherEdge
          exact hNodup.notMem (by simpa [hVertexEq, hOtherEq] using hOther)
        have hTailZero : neighborHitCount graph required rest = 0 :=
          (neighborHitCount_eq_zero_iff graph required rest).2 hNoTail
        simp [neighborHitCount, hBool, hTailZero]
      · have hBool :
          sourceHasUndirectedEdgeBool ((vertex, required), graph.edges) = false := by
          cases h : sourceHasUndirectedEdgeBool ((vertex, required), graph.edges)
          · rfl
          · exact False.elim
              (hEdge ((sourceHasUndirectedEdgeBool_graph_eq_true_iff graph vertex required).1 h))
        rcases hExactlyOne with ⟨witness, hWitness, hWitnessEdge, hUnique⟩
        have hWitnessTail : witness ∈ rest := by
          simp at hWitness
          rcases hWitness with hWitnessHead | hWitnessTail
          · subst witness
            exact False.elim (hEdge hWitnessEdge)
          · exact hWitnessTail
        have hTailExactlyOne : HasExactlyOneNeighborIn graph rest required := by
          refine ⟨witness, hWitnessTail, hWitnessEdge, ?_⟩
          intro other hOther hOtherEdge
          exact hUnique other (by simp [hOther]) hOtherEdge
        simpa [neighborHitCount, hBool] using ih hRestNodup hTailExactlyOne

theorem exactlyOneNeighborBool_eq_true_iff_count
    (graph : GraphInput) (required : Nat) (selected : List Nat) :
    exactlyOneNeighborBool ((graph.edges, required), selected) = true ↔
      neighborHitCount graph required selected = 1 := by
  rw [exactlyOneNeighborBool,
    ComplexityReduction.Karp21.SteinerTreeMembership.natEqBool_eq_true_iff,
    neighborCount_eq_hitCount]

/-! ### Direct standard-TM realization of the one-vertex counter -/

theorem neighborCountInitInstruction_tm_polytime :
    TMPolyTimeMap neighborCountContextEncodedType
      neighborCountInstructionEncodedType neighborCountInitInstruction := by
  have hFalse : TMPolyTimeMap neighborCountContextEncodedType EncodedType.bool
      (fun _ : neighborCountContextEncodedType.Carrier => false) :=
    TMPolyTimeMap.const neighborCountContextEncodedType EncodedType.bool false
  have hContext : TMPolyTimeMap neighborCountContextEncodedType
      neighborCountContextEncodedType id :=
    TMPolyTimeMap.id neighborCountContextEncodedType
  have hZero : TMPolyTimeMap neighborCountContextEncodedType EncodedType.nat
      (fun _ : neighborCountContextEncodedType.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const neighborCountContextEncodedType EncodedType.nat (0 : Nat)
  have hPayload := TMPolyTimeMap.prod_mk hContext hZero
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [neighborCountInitInstruction, neighborCountInstructionEncodedType] using hOut

theorem neighborCountElementInstruction_tm_polytime :
    TMPolyTimeMap EncodedType.nat neighborCountInstructionEncodedType
      neighborCountElementInstruction := by
  have hTrue : TMPolyTimeMap EncodedType.nat EncodedType.bool
      (fun _ : Nat => true) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool true
  have hEmptyEdges : TMPolyTimeMap EncodedType.nat edgeListEncodedType
      (fun _ : Nat => ([] : List (Nat × Nat))) :=
    TMPolyTimeMap.const EncodedType.nat edgeListEncodedType []
  have hZero : TMPolyTimeMap EncodedType.nat EncodedType.nat
      (fun _ : Nat => (0 : Nat)) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.nat (0 : Nat)
  have hContext : TMPolyTimeMap EncodedType.nat neighborCountContextEncodedType
      (fun _ : Nat => (([] : List (Nat × Nat)), (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hEmptyEdges hZero
  have hVertex : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  have hPayload := TMPolyTimeMap.prod_mk hContext hVertex
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [neighborCountElementInstruction, neighborCountInstructionEncodedType] using hOut

theorem neighborCountInstructions_tm_polytime :
    TMPolyTimeMap neighborCountInputEncodedType
      neighborCountInstructionListEncodedType neighborCountInstructions := by
  let X := neighborCountInputEncodedType
  have hContext : TMPolyTimeMap X neighborCountContextEncodedType
      (fun input : X.Carrier => input.1) := by
    simpa [X, neighborCountInputEncodedType] using
      TMPolyTimeMap.fst neighborCountContextEncodedType natListEncodedType
  have hSelected : TMPolyTimeMap X natListEncodedType
      (fun input : X.Carrier => input.2) := by
    simpa [X, neighborCountInputEncodedType] using
      TMPolyTimeMap.snd neighborCountContextEncodedType natListEncodedType
  have hInit : TMPolyTimeMap X neighborCountInstructionEncodedType
      (fun input : X.Carrier => neighborCountInitInstruction input.1) := by
    have hComp := TMPolyTimeMap.comp neighborCountInitInstruction_tm_polytime hContext
    simpa [Function.comp, X] using hComp
  have hInitSingleton : TMPolyTimeMap X neighborCountInstructionListEncodedType
      (fun input : X.Carrier => [neighborCountInitInstruction input.1]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton neighborCountInstructionEncodedType) hInit
    simpa [Function.comp, neighborCountInstructionListEncodedType, X] using hComp
  have hElements : TMPolyTimeMap X neighborCountInstructionListEncodedType
      (fun input : X.Carrier => input.2.map neighborCountElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map neighborCountElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hSelected
    simpa [Function.comp, neighborCountInstructionListEncodedType, X] using hComp
  have hAppendInput : TMPolyTimeMap X
      (EncodedType.prod neighborCountInstructionListEncodedType
        neighborCountInstructionListEncodedType)
      (fun input : X.Carrier =>
        ([neighborCountInitInstruction input.1],
          input.2.map neighborCountElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hElements
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append neighborCountInstructionEncodedType) hAppendInput
  simpa [Function.comp, neighborCountInstructions,
    neighborCountInstructionListEncodedType, X] using hOut

theorem neighborCountStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod neighborCountAccEncodedType neighborCountInstructionEncodedType)
      neighborCountAccEncodedType neighborCountStep := by
  let X := EncodedType.prod neighborCountAccEncodedType neighborCountInstructionEncodedType
  let A := neighborCountAccEncodedType
  let Payload := EncodedType.prod neighborCountContextEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X A (fun input : X.Carrier => input.1) := by
    simpa [X, A] using
      TMPolyTimeMap.fst neighborCountAccEncodedType neighborCountInstructionEncodedType
  have hInstruction : TMPolyTimeMap X neighborCountInstructionEncodedType
      (fun input : X.Carrier => input.2) := by
    simpa [X] using
      TMPolyTimeMap.snd neighborCountAccEncodedType neighborCountInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier => input.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hFst hInstruction
    simpa [Function.comp, neighborCountInstructionEncodedType, Payload, X] using hComp
  have hPayload : TMPolyTimeMap X Payload
      (fun input : X.Carrier => input.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hSnd hInstruction
    simpa [Function.comp, neighborCountInstructionEncodedType, Payload, X] using hComp
  have hAccContext : TMPolyTimeMap X neighborCountContextEncodedType
      (fun input : X.Carrier => input.1.1) := by
    have hFst := TMPolyTimeMap.fst neighborCountContextEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, neighborCountAccEncodedType, A, X] using hComp
  have hAccCount : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.1.2) := by
    have hSnd := TMPolyTimeMap.snd neighborCountContextEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, neighborCountAccEncodedType, A, X] using hComp
  have hAccEdges : TMPolyTimeMap X edgeListEncodedType
      (fun input : X.Carrier => input.1.1.1) := by
    have hFst := TMPolyTimeMap.fst edgeListEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hAccContext
    simpa [Function.comp, neighborCountContextEncodedType, X] using hComp
  have hAccRequired : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.1.1.2) := by
    have hSnd := TMPolyTimeMap.snd edgeListEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hAccContext
    simpa [Function.comp, neighborCountContextEncodedType, X] using hComp
  have hPayloadContext : TMPolyTimeMap X neighborCountContextEncodedType
      (fun input : X.Carrier => input.2.2.1) := by
    have hFst := TMPolyTimeMap.fst neighborCountContextEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hPayloadVertex : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd neighborCountContextEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hPair : TMPolyTimeMap X vertexPairEncodedType
      (fun input : X.Carrier => (input.2.2.2, input.1.1.2)) :=
    TMPolyTimeMap.prod_mk hPayloadVertex hAccRequired
  have hEdgeInput : TMPolyTimeMap X
      (EncodedType.prod vertexPairEncodedType edgeListEncodedType)
      (fun input : X.Carrier =>
        ((input.2.2.2, input.1.1.2), input.1.1.1)) :=
    TMPolyTimeMap.prod_mk hPair hAccEdges
  have hEdge : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier =>
        sourceHasUndirectedEdgeBool
          ((input.2.2.2, input.1.1.2), input.1.1.1)) := by
    have hComp := TMPolyTimeMap.comp sourceHasUndirectedEdgeBool_tm_polytime hEdgeInput
    simpa [Function.comp] using hComp
  have hCountSucc : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => Nat.succ input.1.2) := by
    have hComp := TMPolyTimeMap.comp
      ComplexityReduction.Karp21.natSuccTMBackedMap.tm_polytime hAccCount
    simpa [Function.comp, X] using hComp
  have hHit : TMPolyTimeMap X A
      (fun input : X.Carrier => (input.1.1, Nat.succ input.1.2)) :=
    TMPolyTimeMap.prod_mk hAccContext hCountSucc
  have hMiss : TMPolyTimeMap X A (fun input : X.Carrier => input.1) := hAcc
  have hEdgeBranchInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun input : X.Carrier =>
        (sourceHasUndirectedEdgeBool
          ((input.2.2.2, input.1.1.2), input.1.1.1), input)) :=
    TMPolyTimeMap.prod_mk hEdge (TMPolyTimeMap.id X)
  have hEdgeBranch : TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
      (fun input : Bool × X.Carrier =>
        match input.1 with
        | true => (input.2.1.1, Nat.succ input.2.1.2)
        | false => input.2.1) :=
    graphBoolProduct_dispatch_tm_polytime X A hMiss hHit
  have hSelectedBranch : TMPolyTimeMap X A
      (fun input : X.Carrier =>
        if sourceHasUndirectedEdgeBool
            ((input.2.2.2, input.1.1.2), input.1.1.1) then
          (input.1.1, Nat.succ input.1.2)
        else
          input.1) := by
    have hComp := TMPolyTimeMap.comp hEdgeBranch hEdgeBranchInput
    convert hComp using 1
    funext input
    cases h : sourceHasUndirectedEdgeBool
      ((input.2.2.2, input.1.1.2), input.1.1.1) <;>
        simp [Function.comp, h]
  have hZero : TMPolyTimeMap X EncodedType.nat
      (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hInitBranch : TMPolyTimeMap X A
      (fun input : X.Carrier => (input.2.2.1, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hPayloadContext hZero
  have hTagBranchInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun input : X.Carrier => (input.2.1, input)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hTagBranch : TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
      (fun input : Bool × X.Carrier =>
        match input.1 with
        | true =>
            if sourceHasUndirectedEdgeBool
                ((input.2.2.2.2, input.2.1.1.2), input.2.1.1.1) then
              (input.2.1.1, Nat.succ input.2.1.2)
            else
              input.2.1
        | false => (input.2.2.2.1, (0 : Nat))) :=
    graphBoolProduct_dispatch_tm_polytime X A hInitBranch hSelectedBranch
  have hOut := TMPolyTimeMap.comp hTagBranch hTagBranchInput
  convert hOut using 1
  funext input
  rcases input with ⟨⟨context, count⟩, ⟨tag, payloadContext, vertex⟩⟩
  cases tag <;> simp [Function.comp, neighborCountStep] <;> rfl

theorem neighborCountStep_growth
    (source : List neighborCountInstructionEncodedType.Carrier)
    (accumulator : neighborCountAccEncodedType.Carrier)
    (instruction : neighborCountInstructionEncodedType.Carrier)
    (hInstruction :
      neighborCountInstructionEncodedType.inputSize instruction ≤
        neighborCountInstructionListEncodedType.inputSize source) :
    neighborCountAccEncodedType.inputSize
        (neighborCountStep (accumulator, instruction)) ≤
      neighborCountAccEncodedType.inputSize accumulator +
        (Polynomial.X + Polynomial.C 30).eval
          (neighborCountInstructionListEncodedType.inputSize source) := by
  rcases accumulator with ⟨context, count⟩
  rcases instruction with ⟨tag, payloadContext, vertex⟩
  cases tag
  · have hLocal :
      neighborCountAccEncodedType.inputSize (payloadContext, (0 : Nat)) ≤
        neighborCountInstructionEncodedType.inputSize
          (false, (payloadContext, vertex)) + 30 := by
        simp [neighborCountAccEncodedType, neighborCountInstructionEncodedType,
          neighborCountContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_bool, EncodedType.inputSize_nat]
        omega
    exact calc
      neighborCountAccEncodedType.inputSize
          (neighborCountStep ((context, count), (false, (payloadContext, vertex))))
          ≤ neighborCountInstructionEncodedType.inputSize
              (false, (payloadContext, vertex)) + 30 := by
            simpa [neighborCountStep] using hLocal
      _ ≤ neighborCountInstructionListEncodedType.inputSize source + 30 :=
        Nat.add_le_add_right hInstruction 30
      _ ≤ neighborCountAccEncodedType.inputSize (context, count) +
          (Polynomial.X + Polynomial.C 30).eval
            (neighborCountInstructionListEncodedType.inputSize source) := by
        simp [Polynomial.eval_add]
  · cases hEdge : sourceHasUndirectedEdgeBool
      ((vertex, context.2), context.1)
    · simp [neighborCountStep, hEdge, Polynomial.eval_add]
    · simp [neighborCountStep, hEdge, neighborCountAccEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_nat, Polynomial.eval_add]
      omega

theorem neighborCountFold_tm_polytime :
    TMPolyTimeMap neighborCountInstructionListEncodedType neighborCountAccEncodedType
      (fun instructions : neighborCountInstructionListEncodedType.Carrier =>
        instructions.foldl
          (fun acc instruction => neighborCountStep (acc, instruction))
          neighborCountRunnerInit) := by
  rcases neighborCountStep_tm_polytime with ⟨hStep⟩
  refine TMPolyTimeMap.list_foldl_typed_growth_bounded
    neighborCountInstructionEncodedType neighborCountAccEncodedType
    neighborCountStep neighborCountRunnerInit hStep
    (Polynomial.C 30) (Polynomial.X + Polynomial.C 30) ?_ ?_
  · intro source
    have hEdges : edgeListEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
      exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
    have hInit :
        neighborCountAccEncodedType.inputSize neighborCountRunnerInit ≤ 30 := by
      simp [neighborCountRunnerInit, neighborCountAccEncodedType,
        neighborCountContextEncodedType, EncodedType.inputSize_prod,
        EncodedType.inputSize_nat, hEdges]
    simpa using hInit
  · intro source accumulator instruction hInstruction
    exact neighborCountStep_growth source accumulator instruction hInstruction

theorem neighborCountFromInstructions_tm_polytime :
    TMPolyTimeMap neighborCountInstructionListEncodedType EncodedType.nat
      neighborCountFromInstructions := by
  have hCount := TMPolyTimeMap.snd neighborCountContextEncodedType EncodedType.nat
  have hComp := TMPolyTimeMap.comp hCount neighborCountFold_tm_polytime
  simpa [Function.comp, neighborCountFromInstructions,
    neighborCountAccEncodedType] using hComp

theorem neighborCount_tm_polytime :
    TMPolyTimeMap neighborCountInputEncodedType EncodedType.nat neighborCount := by
  have hComp := TMPolyTimeMap.comp neighborCountFromInstructions_tm_polytime
    neighborCountInstructions_tm_polytime
  simpa [Function.comp, neighborCount] using hComp

theorem exactlyOneNeighborBool_tm_polytime :
    TMPolyTimeMap neighborCountInputEncodedType EncodedType.bool
      exactlyOneNeighborBool := by
  have hCount := neighborCount_tm_polytime
  have hOne : TMPolyTimeMap neighborCountInputEncodedType EncodedType.nat
      (fun _ : neighborCountInputEncodedType.Carrier => (1 : Nat)) :=
    TMPolyTimeMap.const neighborCountInputEncodedType EncodedType.nat (1 : Nat)
  have hInput := TMPolyTimeMap.prod_mk hCount hOne
  have hComp := TMPolyTimeMap.comp
    ComplexityReduction.Karp21.SteinerTreeMembership.natEqBool_tm_polytime hInput
  simpa [Function.comp, exactlyOneNeighborBool] using hComp

/-! ### All required vertices -/

def allRequiredContextEncodedType : EncodedType :=
  EncodedType.prod edgeListEncodedType natListEncodedType

def allRequiredAccEncodedType : EncodedType :=
  EncodedType.prod allRequiredContextEncodedType EncodedType.bool

def allRequiredInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool
    (EncodedType.prod allRequiredContextEncodedType EncodedType.nat)

def allRequiredInstructionListEncodedType : EncodedType :=
  EncodedType.list allRequiredInstructionEncodedType

def allRequiredInputEncodedType : EncodedType :=
  EncodedType.prod allRequiredContextEncodedType natListEncodedType

def allRequiredInitInstruction (context : List (Nat × Nat) × List Nat) :
    Bool × ((List (Nat × Nat) × List Nat) × Nat) :=
  (false, (context, 0))

def allRequiredElementInstruction (required : Nat) :
    Bool × ((List (Nat × Nat) × List Nat) × Nat) :=
  (true, (([], []), required))

def allRequiredInstructions
    (input : (List (Nat × Nat) × List Nat) × List Nat) :
    List (Bool × ((List (Nat × Nat) × List Nat) × Nat)) :=
  allRequiredInitInstruction input.1 ::
    input.2.map allRequiredElementInstruction

def allRequiredRunnerInit : (List (Nat × Nat) × List Nat) × Bool :=
  (([], []), true)

def allRequiredStep
    (input : ((List (Nat × Nat) × List Nat) × Bool) ×
      (Bool × ((List (Nat × Nat) × List Nat) × Nat))) :
    (List (Nat × Nat) × List Nat) × Bool :=
  if input.2.1 then
    (input.1.1,
      graphBoolAndPair
        (input.1.2,
          exactlyOneNeighborBool
            ((input.1.1.1, input.2.2.2), input.1.1.2)))
  else
    (input.2.2.1, true)

def allRequiredFromInstructions
    (instructions : List (Bool × ((List (Nat × Nat) × List Nat) × Nat))) : Bool :=
  (instructions.foldl
    (fun acc instruction => allRequiredStep (acc, instruction))
    allRequiredRunnerInit).2

def allRequiredExactlyOneBool
    (input : (List (Nat × Nat) × List Nat) × List Nat) : Bool :=
  allRequiredFromInstructions (allRequiredInstructions input)

theorem allRequiredElementInstructions_fold_eq_true_iff
    (graph : GraphInput) (selected requiredVertices : List Nat) (ok : Bool) :
    ((requiredVertices.map allRequiredElementInstruction).foldl
      (fun acc instruction => allRequiredStep (acc, instruction))
      ((graph.edges, selected), ok)).2 = true ↔
        ok = true ∧
          ∀ required ∈ requiredVertices,
            neighborHitCount graph required selected = 1 := by
  induction requiredVertices generalizing ok with
  | nil =>
      simp
  | cons required rest ih =>
      rw [List.map_cons, List.foldl_cons]
      change
        ((rest.map allRequiredElementInstruction).foldl
          (fun acc instruction => allRequiredStep (acc, instruction))
          ((graph.edges, selected),
            graphBoolAndPair
              (ok, exactlyOneNeighborBool ((graph.edges, required), selected)))).2 = true ↔ _
      rw [ih]
      constructor
      · rintro ⟨hHead, hTail⟩
        rcases (graphBoolAndPair_eq_true_iff
          (ok, exactlyOneNeighborBool ((graph.edges, required), selected))).1 hHead with
          ⟨hOk, hRequired⟩
        refine ⟨hOk, ?_⟩
        intro vertex hVertex
        simp at hVertex
        rcases hVertex with hVertex | hVertex
        · subst vertex
          exact (exactlyOneNeighborBool_eq_true_iff_count graph required selected).1
            hRequired
        · exact hTail vertex hVertex
      · rintro ⟨hOk, hAll⟩
        refine ⟨?_, ?_⟩
        · exact (graphBoolAndPair_eq_true_iff
            (ok, exactlyOneNeighborBool ((graph.edges, required), selected))).2
              ⟨hOk, (exactlyOneNeighborBool_eq_true_iff_count graph required selected).2
                (hAll required (by simp))⟩
        · intro vertex hVertex
          exact hAll vertex (List.mem_cons_of_mem required hVertex)

theorem allRequiredExactlyOneBool_eq_true_iff
    (graph : GraphInput) (requiredVertices selected : List Nat) :
    allRequiredExactlyOneBool ((graph.edges, selected), requiredVertices) = true ↔
      ∀ required ∈ requiredVertices,
        neighborHitCount graph required selected = 1 := by
  change
    ((allRequiredInitInstruction (graph.edges, selected) ::
      requiredVertices.map allRequiredElementInstruction).foldl
      (fun acc instruction => allRequiredStep (acc, instruction))
      allRequiredRunnerInit).2 = true ↔ _
  rw [List.foldl_cons]
  simpa [allRequiredRunnerInit, allRequiredInitInstruction, allRequiredStep] using
    allRequiredElementInstructions_fold_eq_true_iff graph selected requiredVertices true

/-! ### Direct standard-TM realization of the outer required-vertex scan -/

theorem allRequiredInitInstruction_tm_polytime :
    TMPolyTimeMap allRequiredContextEncodedType allRequiredInstructionEncodedType
      allRequiredInitInstruction := by
  have hFalse : TMPolyTimeMap allRequiredContextEncodedType EncodedType.bool
      (fun _ : allRequiredContextEncodedType.Carrier => false) :=
    TMPolyTimeMap.const allRequiredContextEncodedType EncodedType.bool false
  have hContext : TMPolyTimeMap allRequiredContextEncodedType
      allRequiredContextEncodedType id :=
    TMPolyTimeMap.id allRequiredContextEncodedType
  have hZero : TMPolyTimeMap allRequiredContextEncodedType EncodedType.nat
      (fun _ : allRequiredContextEncodedType.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const allRequiredContextEncodedType EncodedType.nat (0 : Nat)
  have hPayload := TMPolyTimeMap.prod_mk hContext hZero
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [allRequiredInitInstruction, allRequiredInstructionEncodedType] using hOut

theorem allRequiredElementInstruction_tm_polytime :
    TMPolyTimeMap EncodedType.nat allRequiredInstructionEncodedType
      allRequiredElementInstruction := by
  have hTrue : TMPolyTimeMap EncodedType.nat EncodedType.bool
      (fun _ : Nat => true) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool true
  have hEmptyEdges : TMPolyTimeMap EncodedType.nat edgeListEncodedType
      (fun _ : Nat => ([] : List (Nat × Nat))) :=
    TMPolyTimeMap.const EncodedType.nat edgeListEncodedType []
  have hEmptySelected : TMPolyTimeMap EncodedType.nat natListEncodedType
      (fun _ : Nat => ([] : List Nat)) :=
    TMPolyTimeMap.const EncodedType.nat natListEncodedType []
  have hContext : TMPolyTimeMap EncodedType.nat allRequiredContextEncodedType
      (fun _ : Nat => (([] : List (Nat × Nat)), ([] : List Nat))) :=
    TMPolyTimeMap.prod_mk hEmptyEdges hEmptySelected
  have hRequired : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  have hPayload := TMPolyTimeMap.prod_mk hContext hRequired
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [allRequiredElementInstruction, allRequiredInstructionEncodedType] using hOut

theorem allRequiredInstructions_tm_polytime :
    TMPolyTimeMap allRequiredInputEncodedType allRequiredInstructionListEncodedType
      allRequiredInstructions := by
  let X := allRequiredInputEncodedType
  have hContext : TMPolyTimeMap X allRequiredContextEncodedType
      (fun input : X.Carrier => input.1) := by
    simpa [X, allRequiredInputEncodedType] using
      TMPolyTimeMap.fst allRequiredContextEncodedType natListEncodedType
  have hRequiredVertices : TMPolyTimeMap X natListEncodedType
      (fun input : X.Carrier => input.2) := by
    simpa [X, allRequiredInputEncodedType] using
      TMPolyTimeMap.snd allRequiredContextEncodedType natListEncodedType
  have hInit : TMPolyTimeMap X allRequiredInstructionEncodedType
      (fun input : X.Carrier => allRequiredInitInstruction input.1) := by
    have hComp := TMPolyTimeMap.comp allRequiredInitInstruction_tm_polytime hContext
    simpa [Function.comp, X] using hComp
  have hInitSingleton : TMPolyTimeMap X allRequiredInstructionListEncodedType
      (fun input : X.Carrier => [allRequiredInitInstruction input.1]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton allRequiredInstructionEncodedType) hInit
    simpa [Function.comp, allRequiredInstructionListEncodedType, X] using hComp
  have hElements : TMPolyTimeMap X allRequiredInstructionListEncodedType
      (fun input : X.Carrier => input.2.map allRequiredElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map allRequiredElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRequiredVertices
    simpa [Function.comp, allRequiredInstructionListEncodedType, X] using hComp
  have hAppendInput : TMPolyTimeMap X
      (EncodedType.prod allRequiredInstructionListEncodedType
        allRequiredInstructionListEncodedType)
      (fun input : X.Carrier =>
        ([allRequiredInitInstruction input.1],
          input.2.map allRequiredElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hElements
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append allRequiredInstructionEncodedType) hAppendInput
  simpa [Function.comp, allRequiredInstructions,
    allRequiredInstructionListEncodedType, X] using hOut

theorem allRequiredStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod allRequiredAccEncodedType allRequiredInstructionEncodedType)
      allRequiredAccEncodedType allRequiredStep := by
  let X := EncodedType.prod allRequiredAccEncodedType allRequiredInstructionEncodedType
  let A := allRequiredAccEncodedType
  let Payload := EncodedType.prod allRequiredContextEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X A (fun input : X.Carrier => input.1) := by
    simpa [X, A] using
      TMPolyTimeMap.fst allRequiredAccEncodedType allRequiredInstructionEncodedType
  have hInstruction : TMPolyTimeMap X allRequiredInstructionEncodedType
      (fun input : X.Carrier => input.2) := by
    simpa [X] using
      TMPolyTimeMap.snd allRequiredAccEncodedType allRequiredInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier => input.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hFst hInstruction
    simpa [Function.comp, allRequiredInstructionEncodedType, Payload, X] using hComp
  have hPayload : TMPolyTimeMap X Payload
      (fun input : X.Carrier => input.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hSnd hInstruction
    simpa [Function.comp, allRequiredInstructionEncodedType, Payload, X] using hComp
  have hAccContext : TMPolyTimeMap X allRequiredContextEncodedType
      (fun input : X.Carrier => input.1.1) := by
    have hFst := TMPolyTimeMap.fst allRequiredContextEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, allRequiredAccEncodedType, A, X] using hComp
  have hOk : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier => input.1.2) := by
    have hSnd := TMPolyTimeMap.snd allRequiredContextEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, allRequiredAccEncodedType, A, X] using hComp
  have hAccEdges : TMPolyTimeMap X edgeListEncodedType
      (fun input : X.Carrier => input.1.1.1) := by
    have hFst := TMPolyTimeMap.fst edgeListEncodedType natListEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAccContext
    simpa [Function.comp, allRequiredContextEncodedType, X] using hComp
  have hAccSelected : TMPolyTimeMap X natListEncodedType
      (fun input : X.Carrier => input.1.1.2) := by
    have hSnd := TMPolyTimeMap.snd edgeListEncodedType natListEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAccContext
    simpa [Function.comp, allRequiredContextEncodedType, X] using hComp
  have hPayloadContext : TMPolyTimeMap X allRequiredContextEncodedType
      (fun input : X.Carrier => input.2.2.1) := by
    have hFst := TMPolyTimeMap.fst allRequiredContextEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hPayloadRequired : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd allRequiredContextEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hNeighborContext : TMPolyTimeMap X neighborCountContextEncodedType
      (fun input : X.Carrier => (input.1.1.1, input.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAccEdges hPayloadRequired
  have hNeighborInput : TMPolyTimeMap X neighborCountInputEncodedType
      (fun input : X.Carrier =>
        ((input.1.1.1, input.2.2.2), input.1.1.2)) :=
    TMPolyTimeMap.prod_mk hNeighborContext hAccSelected
  have hExactlyOne : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier =>
        exactlyOneNeighborBool
          ((input.1.1.1, input.2.2.2), input.1.1.2)) := by
    have hComp := TMPolyTimeMap.comp exactlyOneNeighborBool_tm_polytime hNeighborInput
    simpa [Function.comp] using hComp
  have hAndInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : X.Carrier =>
        (input.1.2,
          exactlyOneNeighborBool
            ((input.1.1.1, input.2.2.2), input.1.1.2))) :=
    TMPolyTimeMap.prod_mk hOk hExactlyOne
  have hAnd : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier =>
        graphBoolAndPair
          (input.1.2,
            exactlyOneNeighborBool
              ((input.1.1.1, input.2.2.2), input.1.1.2))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
    simpa [Function.comp] using hComp
  have hTrueBranch : TMPolyTimeMap X A
      (fun input : X.Carrier =>
        (input.1.1,
          graphBoolAndPair
            (input.1.2,
              exactlyOneNeighborBool
                ((input.1.1.1, input.2.2.2), input.1.1.2)))) :=
    TMPolyTimeMap.prod_mk hAccContext hAnd
  have hTrue : TMPolyTimeMap X EncodedType.bool
      (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hFalseBranch : TMPolyTimeMap X A
      (fun input : X.Carrier => (input.2.2.1, true)) :=
    TMPolyTimeMap.prod_mk hPayloadContext hTrue
  have hBranchInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun input : X.Carrier => (input.2.1, input)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranch : TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
      (fun input : Bool × X.Carrier =>
        match input.1 with
        | true =>
            (input.2.1.1,
              graphBoolAndPair
                (input.2.1.2,
                  exactlyOneNeighborBool
                    ((input.2.1.1.1, input.2.2.2.2), input.2.1.1.2)))
        | false => (input.2.2.2.1, true)) :=
    graphBoolProduct_dispatch_tm_polytime X A hFalseBranch hTrueBranch
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext input
  rcases input with ⟨⟨context, ok⟩, ⟨tag, payloadContext, required⟩⟩
  cases tag <;> rfl

theorem allRequiredStep_inputSize_le
    (source : List allRequiredInstructionEncodedType.Carrier)
    (accumulator : allRequiredAccEncodedType.Carrier)
    (instruction : allRequiredInstructionEncodedType.Carrier)
    (hAccumulator :
      allRequiredAccEncodedType.inputSize accumulator ≤
        allRequiredInstructionListEncodedType.inputSize source + 20)
    (hInstruction :
      allRequiredInstructionEncodedType.inputSize instruction ≤
        allRequiredInstructionListEncodedType.inputSize source) :
    allRequiredAccEncodedType.inputSize
        (allRequiredStep (accumulator, instruction)) ≤
      allRequiredInstructionListEncodedType.inputSize source + 20 := by
  rcases accumulator with ⟨context, ok⟩
  rcases instruction with ⟨tag, payloadContext, required⟩
  cases tag
  · have hLocal :
      allRequiredAccEncodedType.inputSize (payloadContext, true) ≤
        allRequiredInstructionEncodedType.inputSize
          (false, (payloadContext, required)) + 20 := by
        simp [allRequiredAccEncodedType, allRequiredInstructionEncodedType,
          allRequiredContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_bool, EncodedType.inputSize_nat]
        omega
    simpa [allRequiredStep] using
      hLocal.trans (Nat.add_le_add_right hInstruction 20)
  · have hLocal :
      allRequiredAccEncodedType.inputSize
          (allRequiredStep ((context, ok), (true, (payloadContext, required)))) ≤
        allRequiredAccEncodedType.inputSize (context, ok) := by
        cases hExact : exactlyOneNeighborBool
          ((context.1, required), context.2) <;>
          cases ok <;>
          simp [allRequiredStep, hExact, allRequiredAccEncodedType,
            EncodedType.inputSize_prod, EncodedType.inputSize_bool]
    exact hLocal.trans hAccumulator

theorem allRequiredFold_tm_polytime :
    TMPolyTimeMap allRequiredInstructionListEncodedType allRequiredAccEncodedType
      (fun instructions : allRequiredInstructionListEncodedType.Carrier =>
        instructions.foldl
          (fun acc instruction => allRequiredStep (acc, instruction))
          allRequiredRunnerInit) := by
  rcases allRequiredStep_tm_polytime with ⟨hStep⟩
  let bound : Polynomial Nat := Polynomial.X + Polynomial.C 20
  refine TMPolyTimeMap.list_foldl_typed_bounded
    allRequiredInstructionEncodedType allRequiredAccEncodedType
    allRequiredStep allRequiredRunnerInit hStep bound ?_ ?_
  · intro source
    have hEdges : edgeListEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
      exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
    have hSelected : natListEncodedType.inputSize ([] : List Nat) = 0 := by
      exact EncodedType.inputSize_list_nil EncodedType.nat
    have hInit :
        allRequiredAccEncodedType.inputSize allRequiredRunnerInit ≤ 20 := by
      simp [allRequiredRunnerInit, allRequiredAccEncodedType,
        allRequiredContextEncodedType, EncodedType.inputSize_prod,
        EncodedType.inputSize_bool, hEdges, hSelected]
    have hEval :
        bound.eval (allRequiredInstructionEncodedType.list.inputSize source) =
          allRequiredInstructionEncodedType.list.inputSize source + 20 := by
      simp [bound, Polynomial.eval_add]
    rw [hEval]
    exact hInit.trans (Nat.le_add_left 20 _)
  · intro source accumulator instruction hAccumulator hInstruction
    have hAccumulator' :
        allRequiredAccEncodedType.inputSize accumulator ≤
          allRequiredInstructionListEncodedType.inputSize source + 20 := by
      simpa [allRequiredInstructionListEncodedType, bound,
        Polynomial.eval_add] using hAccumulator
    have hInstruction' :
        allRequiredInstructionEncodedType.inputSize instruction ≤
          allRequiredInstructionListEncodedType.inputSize source := by
      simpa [allRequiredInstructionListEncodedType] using hInstruction
    simpa [allRequiredInstructionListEncodedType, bound,
      Polynomial.eval_add] using
        allRequiredStep_inputSize_le source accumulator instruction
          hAccumulator' hInstruction'

theorem allRequiredFromInstructions_tm_polytime :
    TMPolyTimeMap allRequiredInstructionListEncodedType EncodedType.bool
      allRequiredFromInstructions := by
  have hOk := TMPolyTimeMap.snd allRequiredContextEncodedType EncodedType.bool
  have hComp := TMPolyTimeMap.comp hOk allRequiredFold_tm_polytime
  simpa [Function.comp, allRequiredFromInstructions,
    allRequiredAccEncodedType] using hComp

theorem allRequiredExactlyOneBool_tm_polytime :
    TMPolyTimeMap allRequiredInputEncodedType EncodedType.bool
      allRequiredExactlyOneBool := by
  have hComp := TMPolyTimeMap.comp allRequiredFromInstructions_tm_polytime
    allRequiredInstructions_tm_polytime
  simpa [Function.comp, allRequiredExactlyOneBool] using hComp

/-! ### Exact finite checker semantics -/

def finiteVerify (input : ExactlyOneNeighborInput) (selected : List Nat) : Bool :=
  graphBoolAndPair
    (HittingSet.boundedNatListBool (input.graph.vertices, selected),
      graphBoolAndPair
        (HittingSet.boundedNatListBool (input.graph.vertices, input.R),
          allRequiredExactlyOneBool ((input.graph.edges, selected), input.R)))

theorem finiteVerify_eq_true_iff
    (input : ExactlyOneNeighborInput) (selected : List Nat) :
    finiteVerify input selected = true ↔
      VerticesWithinBounds input.graph selected ∧
        VerticesWithinBounds input.graph input.R ∧
          ∀ required ∈ input.R,
            neighborHitCount input.graph required selected = 1 := by
  rw [finiteVerify, graphBoolAndPair_eq_true_iff,
    graphBoolAndPair_eq_true_iff,
    HittingSet.boundedNatListBool_eq_true_iff,
    HittingSet.boundedNatListBool_eq_true_iff,
    allRequiredExactlyOneBool_eq_true_iff]
  rfl

theorem finiteVerify_complete
    (input : ExactlyOneNeighborInput) (selected : List Nat)
    (hWitness : ExactlyOneNeighborWitness input selected) :
    finiteVerify input selected = true := by
  rcases hWitness with ⟨hNodup, hSelectedBounds, hRequiredBounds, hAll⟩
  apply (finiteVerify_eq_true_iff input selected).2
  refine ⟨hSelectedBounds, hRequiredBounds, ?_⟩
  intro required hRequired
  exact neighborHitCount_eq_one_of_nodup input.graph required selected hNodup
    (hAll required hRequired)

theorem hasExactlyOneNeighborIn_dedup
    (graph : GraphInput) (selected : List Nat) (required : Nat)
    (hExactlyOne : HasExactlyOneNeighborIn graph selected required) :
    HasExactlyOneNeighborIn graph selected.dedup required := by
  rcases hExactlyOne with ⟨witness, hWitness, hEdge, hUnique⟩
  refine ⟨witness, List.mem_dedup.mpr hWitness, hEdge, ?_⟩
  intro other hOther hOtherEdge
  exact hUnique other (List.mem_dedup.mp hOther) hOtherEdge

theorem finiteVerify_sound
    (input : ExactlyOneNeighborInput) (selected : List Nat)
    (hVerify : finiteVerify input selected = true) :
    ExactlyOneNeighborWitness input selected.dedup := by
  rcases (finiteVerify_eq_true_iff input selected).1 hVerify with
    ⟨hSelectedBounds, hRequiredBounds, hAll⟩
  refine ⟨List.nodup_dedup selected, ?_, hRequiredBounds, ?_⟩
  · intro vertex hVertex
    exact hSelectedBounds vertex (List.mem_dedup.mp hVertex)
  · intro required hRequired
    apply hasExactlyOneNeighborIn_dedup
    exact neighborHitCount_eq_one_implies input.graph required selected
      (hAll required hRequired)

/-! ### Direct standard-TM checker at the exact public presentation -/

def inputToTuple (input : ExactlyOneNeighborInput) : GraphInput × List Nat :=
  (input.graph, input.R)

theorem inputToTuple_tm_polytime :
    TMPolyTimeMap exactlyOneNeighborStructuredEncodedType
      (EncodedType.prod graphStructuredEncodedType natListEncodedType)
      inputToTuple := by
  exact TMPolyTimeMap.of_encodingEquiv _ _ _ (Equiv.refl _) (by
    intro input
    change
      (EncodedType.prod graphStructuredEncodedType natListEncodedType).encode
          (input.graph, input.R) =
        List.map id
          ((EncodedType.prod graphStructuredEncodedType natListEncodedType).encode
            (input.graph, input.R))
    rw [List.map_id])

def graphToTuple (graph : GraphInput) :
    Nat × (List (Nat × Nat) × Bool) :=
  (graph.vertices, (graph.edges, graph.directed))

theorem graphToTuple_tm_polytime :
    TMPolyTimeMap graphStructuredEncodedType graphTupleStructuredEncodedType
      graphToTuple := by
  exact TMPolyTimeMap.of_encodingEquiv _ _ _ (Equiv.refl _) (by
    intro graph
    change graphTupleStructuredEncodedType.encode
        (graph.vertices, (graph.edges, graph.directed)) =
      List.map id
        (graphTupleStructuredEncodedType.encode
          (graph.vertices, (graph.edges, graph.directed)))
    rw [List.map_id])

theorem finiteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod exactlyOneNeighborStructuredEncodedType natListEncodedType)
      EncodedType.bool
      (fun input : ExactlyOneNeighborInput × List Nat =>
        finiteVerify input.1 input.2) := by
  let X := EncodedType.prod exactlyOneNeighborStructuredEncodedType natListEncodedType
  have hInstance : TMPolyTimeMap X exactlyOneNeighborStructuredEncodedType
      (fun input : X.Carrier => input.1) := by
    simpa [X] using
      TMPolyTimeMap.fst exactlyOneNeighborStructuredEncodedType natListEncodedType
  have hSelected : TMPolyTimeMap X natListEncodedType
      (fun input : X.Carrier => input.2) := by
    simpa [X] using
      TMPolyTimeMap.snd exactlyOneNeighborStructuredEncodedType natListEncodedType
  have hInputTuple : TMPolyTimeMap X
      (EncodedType.prod graphStructuredEncodedType natListEncodedType)
      (fun input : X.Carrier => (input.1.graph, input.1.R)) := by
    have hComp := TMPolyTimeMap.comp inputToTuple_tm_polytime hInstance
    simpa [Function.comp, inputToTuple, X] using hComp
  have hGraph : TMPolyTimeMap X graphStructuredEncodedType
      (fun input : X.Carrier => input.1.graph) := by
    have hFst := TMPolyTimeMap.fst graphStructuredEncodedType natListEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInputTuple
    simpa [Function.comp, X] using hComp
  have hRequiredVertices : TMPolyTimeMap X natListEncodedType
      (fun input : X.Carrier => input.1.R) := by
    have hSnd := TMPolyTimeMap.snd graphStructuredEncodedType natListEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInputTuple
    simpa [Function.comp, X] using hComp
  have hGraphTuple : TMPolyTimeMap X graphTupleStructuredEncodedType
      (fun input : X.Carrier =>
        (input.1.graph.vertices, (input.1.graph.edges, input.1.graph.directed))) := by
    have hComp := TMPolyTimeMap.comp graphToTuple_tm_polytime hGraph
    simpa [Function.comp, graphToTuple, X] using hComp
  have hVertices : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.1.graph.vertices) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat graphPayloadStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hGraphTuple
    simpa [Function.comp, graphTupleStructuredEncodedType, X] using hComp
  have hGraphPayload : TMPolyTimeMap X graphPayloadStructuredEncodedType
      (fun input : X.Carrier => (input.1.graph.edges, input.1.graph.directed)) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat graphPayloadStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hGraphTuple
    simpa [Function.comp, graphTupleStructuredEncodedType, X] using hComp
  have hEdges : TMPolyTimeMap X edgeListEncodedType
      (fun input : X.Carrier => input.1.graph.edges) := by
    have hFst := TMPolyTimeMap.fst edgeListEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hGraphPayload
    simpa [Function.comp, graphPayloadStructuredEncodedType, X] using hComp
  have hSelectedBoundsInput : TMPolyTimeMap X HittingSet.boundedNatInstructionInputEncodedType
      (fun input : X.Carrier => (input.1.graph.vertices, input.2)) :=
    TMPolyTimeMap.prod_mk hVertices hSelected
  have hSelectedBounds : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier =>
        HittingSet.boundedNatListBool (input.1.graph.vertices, input.2)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.boundedNatListBool_tm_polytime
      hSelectedBoundsInput
    simpa [Function.comp, HittingSet.boundedNatInstructionInputEncodedType, X] using hComp
  have hRequiredBoundsInput :
      TMPolyTimeMap X HittingSet.boundedNatInstructionInputEncodedType
        (fun input : X.Carrier => (input.1.graph.vertices, input.1.R)) :=
    TMPolyTimeMap.prod_mk hVertices hRequiredVertices
  have hRequiredBounds : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier =>
        HittingSet.boundedNatListBool (input.1.graph.vertices, input.1.R)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.boundedNatListBool_tm_polytime
      hRequiredBoundsInput
    simpa [Function.comp, HittingSet.boundedNatInstructionInputEncodedType, X] using hComp
  have hAllContext : TMPolyTimeMap X allRequiredContextEncodedType
      (fun input : X.Carrier => (input.1.graph.edges, input.2)) :=
    TMPolyTimeMap.prod_mk hEdges hSelected
  have hAllInput : TMPolyTimeMap X allRequiredInputEncodedType
      (fun input : X.Carrier =>
        ((input.1.graph.edges, input.2), input.1.R)) :=
    TMPolyTimeMap.prod_mk hAllContext hRequiredVertices
  have hAllRequired : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier =>
        allRequiredExactlyOneBool
          ((input.1.graph.edges, input.2), input.1.R)) := by
    have hComp := TMPolyTimeMap.comp allRequiredExactlyOneBool_tm_polytime hAllInput
    simpa [Function.comp] using hComp
  have hTailInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : X.Carrier =>
        (HittingSet.boundedNatListBool
            (input.1.graph.vertices, input.1.R),
          allRequiredExactlyOneBool
            ((input.1.graph.edges, input.2), input.1.R))) :=
    TMPolyTimeMap.prod_mk hRequiredBounds hAllRequired
  have hTail : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier =>
        graphBoolAndPair
          (HittingSet.boundedNatListBool
              (input.1.graph.vertices, input.1.R),
            allRequiredExactlyOneBool
              ((input.1.graph.edges, input.2), input.1.R))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hTailInput
    simpa [Function.comp] using hComp
  have hFinalInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : X.Carrier =>
        (HittingSet.boundedNatListBool
            (input.1.graph.vertices, input.2),
          graphBoolAndPair
            (HittingSet.boundedNatListBool
                (input.1.graph.vertices, input.1.R),
              allRequiredExactlyOneBool
                ((input.1.graph.edges, input.2), input.1.R)))) :=
    TMPolyTimeMap.prod_mk hSelectedBounds hTail
  have hFinal := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hFinalInput
  simpa [Function.comp, finiteVerify, X] using hFinal

theorem graphStructuredInputSize_eq (graph : GraphInput) :
    graphStructuredEncodedType.inputSize graph =
      graph.vertices + edgeListEncodedType.inputSize graph.edges + 4 := by
  change graphTupleStructuredEncodedType.inputSize
      (graph.vertices, (graph.edges, graph.directed)) = _
  simp [graphTupleStructuredEncodedType, graphPayloadStructuredEncodedType,
    edgeListEncodedType]
  omega

theorem certificate_inputSize_le_square
    (input : ExactlyOneNeighborInput) (selected : List Nat)
    (hNodup : selected.Nodup)
    (hBounds : VerticesWithinBounds input.graph selected) :
    natListEncodedType.inputSize selected ≤
      exactlyOneNeighborStructuredEncodedType.inputSize input ^ 2 := by
  let inputSize := exactlyOneNeighborStructuredEncodedType.inputSize input
  have hSelectedLength : selected.length ≤ input.graph.vertices := by
    have hMembers : ∀ vertex ∈ selected, vertex ∈ List.range input.graph.vertices := by
      intro vertex hVertex
      simp [hBounds vertex hVertex]
    simpa using
      (ComplexityReduction.Karp21.FiniteWitness.nodup_length_le_of_mem
        hNodup hMembers)
  have hCertificate :=
    ComplexityReduction.Problems.Karp21.HittingSetStandardTM.boundedNatList_inputSize_le
      input.graph.vertices selected hBounds
  have hVertices : input.graph.vertices ≤ inputSize := by
    rw [show inputSize = exactlyOneNeighborStructuredEncodedType.inputSize input by rfl,
      exactlyOneNeighborStructured_inputSize_eq,
      graphStructuredInputSize_eq]
    omega
  have hVerticesSucc : input.graph.vertices + 1 ≤ inputSize := by
    rw [show inputSize = exactlyOneNeighborStructuredEncodedType.inputSize input by rfl,
      exactlyOneNeighborStructured_inputSize_eq,
      graphStructuredInputSize_eq]
    omega
  calc
    natListEncodedType.inputSize selected
        ≤ selected.length * (input.graph.vertices + 1) := hCertificate
    _ ≤ input.graph.vertices * (input.graph.vertices + 1) :=
      Nat.mul_le_mul_right (input.graph.vertices + 1) hSelectedLength
    _ ≤ inputSize * inputSize := Nat.mul_le_mul hVertices hVerticesSucc
    _ = inputSize ^ 2 := by ring

/-- The exact direct-TM-backed checker primitive. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def checkerPrimitive :
    Primitive (StandardInstances.prod problem.representation natListPresentation)
      StandardInstances.bool :=
  Primitive.ofTMPolyTime
    (fun input => finiteVerify input.1 input.2)
    (by
      simpa [problem, ComplexityReduction.Presentation.ExactlyOneNeighbor.presentedProblem,
        ComplexityReduction.Presentation.ExactlyOneNeighbor.structuredPresentation,
        natListPresentation, natListEncodedType, StandardInstances.prod,
        StandardInstances.bool] using finiteVerify_tm_polytime)

/-- The one checker program used by the verifier and its compiled TM. -/
noncomputable def checker :
    PolyProg (StandardInstances.prod problem.representation natListPresentation)
      StandardInstances.bool :=
  .atom checkerPrimitive

@[simp] theorem checker_run
    (input : problem.Instance × List Nat) :
    checker.run input = finiteVerify input.1 input.2 :=
  rfl

noncomputable def verifierData : NatListVerifierData problem where
  checker := checker
  witnessBound := fun input =>
    problem.representation.encodedType.inputSize input ^ 2
  witnessBoundPoly := ComplexityReduction.PolynomialTimeBound.intro_with 2 1 0 (by
    intro input
    simp)
  correct := by
    intro input
    change ExactlyOneNeighborYes input ↔
      ∃ candidate : List Nat,
        natListEncodedType.inputSize candidate ≤
            exactlyOneNeighborStructuredEncodedType.inputSize input ^ 2 ∧
          finiteVerify input candidate = true
    constructor
    · rintro ⟨selected, hWitness⟩
      refine ⟨selected, ?_, finiteVerify_complete input selected hWitness⟩
      exact certificate_inputSize_le_square input selected hWitness.1 hWitness.2.1
    · rintro ⟨candidate, _, hAccepted⟩
      exact ⟨candidate.dedup, finiteVerify_sound input candidate hAccepted⟩
  checkerSound := by
    intro input candidate hAccepted
    change ExactlyOneNeighborYes input
    exact ⟨candidate.dedup, finiteVerify_sound input candidate hAccepted⟩

/-- Exact verifier component exposed to deterministic Optional Authoring. -/
noncomputable def verifier : CertifiedVerifier problem :=
  verifierData.toCertifiedVerifier

/-- Structural certificate for the exact verifier witness presentation. -/
def witnessPresentation : verifier.witness.StructuralCertificate :=
  natListStructuralCertificate

/-- Checked decoder discipline indexed by the exact verifier. -/
noncomputable def discipline : CertifiedVerifierEncodingDiscipline verifier :=
  ComplexityReduction.Agent.Hardness.FiniteWitnessNative.discipline verifierData

/-- Discovery-only exact membership template; it grants no capability by itself. -/
@[complexity_reduction_ir_hardness_native_membership_template]
def template : ComplexityReduction.Agent.Hardness.Authoring.NativeMembershipTemplate
    problem verifier witnessPresentation discipline :=
  ⟨True.intro⟩

assert_standard_axioms finiteVerify_tm_polytime, certificate_inputSize_le_square,
  verifier, witnessPresentation, discipline, template

end Benchmark.Hardness.Inputs.Quals.Spring2015ExactlyOneNeighbor
