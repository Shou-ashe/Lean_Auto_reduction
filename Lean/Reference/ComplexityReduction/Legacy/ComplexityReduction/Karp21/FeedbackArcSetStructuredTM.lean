/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.FeedbackArcSet
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.FeedbackNodeSetStructuredTM
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ChromaticNumber.StructuredRoute

/-!
Direct TM-backed structured assembly for the Feedback Node Set to Feedback Arc
Set textbook node-splitting route.
-/

namespace ComplexityReduction
namespace Karp21
namespace FeedbackArcSet

open ComplexityReduction.Combinatorics.Graph

/-! ### Source and target tuple reifiers -/

theorem feedbackNodeSetGraph_encode_filterMap (I : FeedbackNodeSetInput) :
    graphStructuredEncodedType.encode I.graph =
      (feedbackNodeSetStructuredEncodedType.encode I).filterMap
        (@EncodedType.prodLeftSymbol
          graphStructuredEncodedType.Symbol EncodedType.nat.Symbol) := by
  simpa [feedbackNodeSetStructuredEncodedType] using
    (EncodedType.prod_left_filter_encode
      graphStructuredEncodedType EncodedType.nat (I.graph, I.k)).symm

theorem feedbackNodeSetBudget_encode_filterMap (I : FeedbackNodeSetInput) :
    EncodedType.nat.encode I.k =
      (feedbackNodeSetStructuredEncodedType.encode I).filterMap
        (@EncodedType.prodRightSymbol
          graphStructuredEncodedType.Symbol EncodedType.nat.Symbol) := by
  simpa [feedbackNodeSetStructuredEncodedType] using
    (EncodedType.prod_right_filter_encode
      graphStructuredEncodedType EncodedType.nat (I.graph, I.k)).symm

noncomputable def feedbackNodeSetGraphTMBackedMap :
    TMBackedCostedMap feedbackNodeSetStructuredEncodedType graphStructuredEncodedType
      (fun I : FeedbackNodeSetInput => I.graph) :=
  TMBackedCostedMap.symbolFilterMap
    feedbackNodeSetStructuredEncodedType graphStructuredEncodedType
    (fun I : FeedbackNodeSetInput => I.graph)
    (@EncodedType.prodLeftSymbol
      graphStructuredEncodedType.Symbol EncodedType.nat.Symbol)
    feedbackNodeSetGraph_encode_filterMap

noncomputable def feedbackNodeSetBudgetTMBackedMap :
    TMBackedCostedMap feedbackNodeSetStructuredEncodedType EncodedType.nat
      (fun I : FeedbackNodeSetInput => I.k) :=
  TMBackedCostedMap.symbolFilterMap
    feedbackNodeSetStructuredEncodedType EncodedType.nat
    (fun I : FeedbackNodeSetInput => I.k)
    (@EncodedType.prodRightSymbol
      graphStructuredEncodedType.Symbol EncodedType.nat.Symbol)
    feedbackNodeSetBudget_encode_filterMap

def feedbackArcSetTupleToInput
    (p : feedbackArcSetTupleStructuredEncodedType.Carrier) : FeedbackArcSetInput where
  graph := p.1
  k := p.2

theorem feedbackArcSetTupleToInput_encode
    (p : feedbackArcSetTupleStructuredEncodedType.Carrier) :
    feedbackArcSetStructuredEncodedType.encode (feedbackArcSetTupleToInput p) =
      feedbackArcSetTupleStructuredEncodedType.encode p := by
  rcases p with ⟨graph, k⟩
  rfl

noncomputable def feedbackArcSetTupleToInputTMBackedMap :
    TMBackedCostedMap
      feedbackArcSetTupleStructuredEncodedType
      feedbackArcSetStructuredEncodedType
      feedbackArcSetTupleToInput :=
  TMBackedCostedMap.ofEncodingEquiv
    feedbackArcSetTupleStructuredEncodedType
    feedbackArcSetStructuredEncodedType
    feedbackArcSetTupleToInput
    (Equiv.refl feedbackArcSetTupleStructuredEncodedType.Symbol)
    (by
      intro p
      change feedbackArcSetStructuredEncodedType.encode (feedbackArcSetTupleToInput p) =
        (feedbackArcSetTupleStructuredEncodedType.encode p).map id
      simp [feedbackArcSetTupleToInput_encode])

/-! ### Split-arc and cross-arc blocks -/

def splitVertexCount (n : Nat) : Nat :=
  2 * n

theorem splitVertexCount_tm_polytime :
    TMPolyTimeMap EncodedType.nat EncodedType.nat splitVertexCount := by
  convert natDouble_tm_polytime using 1
  funext n
  simp [splitVertexCount, natDouble]
  omega

theorem inVertex_tm_polytime :
    TMPolyTimeMap EncodedType.nat EncodedType.nat inVertex := by
  simpa [inVertex, splitVertexCount] using splitVertexCount_tm_polytime

theorem outVertex_tm_polytime :
    TMPolyTimeMap EncodedType.nat EncodedType.nat outVertex := by
  have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime inVertex_tm_polytime
  simpa [Function.comp, outVertex] using hComp

theorem splitArc_tm_polytime :
    TMPolyTimeMap EncodedType.nat edgeStructuredEncodedType splitArc := by
  have hPair := TMPolyTimeMap.prod_mk inVertex_tm_polytime outVertex_tm_polytime
  simpa [splitArc, edgeStructuredEncodedType] using hPair

theorem crossArc_tm_polytime :
    TMPolyTimeMap edgeStructuredEncodedType edgeStructuredEncodedType crossArc := by
  let X := edgeStructuredEncodedType
  have hLeft : TMPolyTimeMap X EncodedType.nat (fun e : X.Carrier => e.1) := by
    simpa [X, edgeStructuredEncodedType] using TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hRight : TMPolyTimeMap X EncodedType.nat (fun e : X.Carrier => e.2) := by
    simpa [X, edgeStructuredEncodedType] using TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hOutLeft : TMPolyTimeMap X EncodedType.nat (fun e : X.Carrier => outVertex e.1) := by
    have hComp := TMPolyTimeMap.comp outVertex_tm_polytime hLeft
    simpa [Function.comp, X] using hComp
  have hInRight : TMPolyTimeMap X EncodedType.nat (fun e : X.Carrier => inVertex e.2) := by
    have hComp := TMPolyTimeMap.comp inVertex_tm_polytime hRight
    simpa [Function.comp, X] using hComp
  have hPair := TMPolyTimeMap.prod_mk hOutLeft hInRight
  simpa [crossArc, edgeStructuredEncodedType, X] using hPair

def splitArcsTM (g : GraphInput) : List (Nat × Nat) :=
  (List.range g.vertices).map splitArc

theorem splitArcsTM_eq_splitArcs (g : GraphInput) :
    splitArcsTM g = splitArcs g := by
  rfl

theorem splitArcsTM_tm_polytime :
    TMPolyTimeMap graphStructuredEncodedType edgeListStructuredEncodedType splitArcsTM := by
  have hVertices :
      TMPolyTimeMap graphStructuredEncodedType EncodedType.nat GraphInput.vertices :=
    graphVerticesTMBackedMap.tm_polytime
  have hRange :
      TMPolyTimeMap graphStructuredEncodedType (EncodedType.list EncodedType.nat)
        (fun g : GraphInput => List.range g.vertices) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hVertices
    simpa [Function.comp] using hComp
  have hMap := TMPolyTimeMap.list_map splitArc_tm_polytime
  have hComp := TMPolyTimeMap.comp hMap hRange
  simpa [Function.comp, splitArcsTM, edgeListStructuredEncodedType] using hComp

def crossArcBlockForVertices (vertices : Nat) (edge : Nat × Nat) : List (Nat × Nat) :=
  if edge.1 < vertices then
    if edge.2 < vertices then [crossArc edge] else []
  else
    []

theorem crossArcBlockForVertices_tm_polytime :
    TMPolyTimeMap
      FeedbackNodeSet.edgeBlockInputEncodedType
      edgeListStructuredEncodedType
      (fun p : FeedbackNodeSet.edgeBlockInputEncodedType.Carrier =>
        crossArcBlockForVertices p.1 p.2) := by
  let X := FeedbackNodeSet.edgeBlockInputEncodedType
  have hEdge : TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, FeedbackNodeSet.edgeBlockInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat edgeStructuredEncodedType
  have hCross :
      TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => crossArc p.2) := by
    have hComp := TMPolyTimeMap.comp crossArc_tm_polytime hEdge
    simpa [Function.comp, X] using hComp
  have hSingleton :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier => [crossArc p.2]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton edgeStructuredEncodedType)
      hCross
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hEmpty :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun _ : X.Carrier => ([] : List (Nat × Nat))) :=
    TMPolyTimeMap.const X edgeListStructuredEncodedType []
  have hRightBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (FeedbackNodeSet.edgeEndpointRightLtBool p, p)) :=
    TMPolyTimeMap.prod_mk FeedbackNodeSet.edgeEndpointRightLtBool_tm_polytime
      (TMPolyTimeMap.id X)
  have hLeftTrueBranch :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier =>
          match FeedbackNodeSet.edgeEndpointRightLtBool p with
          | true => [crossArc p.2]
          | false => []) := by
    have hBranch :=
      graphBoolProduct_dispatch_tm_polytime X edgeListStructuredEncodedType
        (fFalse := fun _ : X.Carrier => ([] : List (Nat × Nat)))
        (fTrue := fun p : X.Carrier => [crossArc p.2])
        hEmpty hSingleton
    have hComp := TMPolyTimeMap.comp hBranch hRightBranchInput
    simpa [Function.comp, X] using hComp
  have hLeftBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (FeedbackNodeSet.edgeEndpointLeftLtBool p, p)) :=
    TMPolyTimeMap.prod_mk FeedbackNodeSet.edgeEndpointLeftLtBool_tm_polytime
      (TMPolyTimeMap.id X)
  have hBranch :=
    graphBoolProduct_dispatch_tm_polytime X edgeListStructuredEncodedType
      (fFalse := fun _ : X.Carrier => ([] : List (Nat × Nat)))
      (fTrue := fun p : X.Carrier =>
        match FeedbackNodeSet.edgeEndpointRightLtBool p with
        | true => [crossArc p.2]
        | false => [])
      hEmpty hLeftTrueBranch
  have hOut := TMPolyTimeMap.comp hBranch hLeftBranchInput
  convert hOut using 1
  funext p
  change Nat × (Nat × Nat) at p
  by_cases hLeft : p.2.1 < p.1 <;> by_cases hRight : p.2.2 < p.1
  · simp [Function.comp, crossArcBlockForVertices, FeedbackNodeSet.edgeEndpointLeftLtBool,
      FeedbackNodeSet.edgeEndpointRightLtBool, FeedbackNodeSet.natLtBool, hLeft, hRight]
    rfl
  · simp [Function.comp, crossArcBlockForVertices, FeedbackNodeSet.edgeEndpointLeftLtBool,
      FeedbackNodeSet.edgeEndpointRightLtBool, FeedbackNodeSet.natLtBool, hLeft, hRight]
    rfl
  · simp [Function.comp, crossArcBlockForVertices, FeedbackNodeSet.edgeEndpointLeftLtBool,
      FeedbackNodeSet.natLtBool, hLeft]
  · simp [Function.comp, crossArcBlockForVertices, FeedbackNodeSet.edgeEndpointLeftLtBool,
      FeedbackNodeSet.natLtBool, hLeft]

/-! ### Bounded source-edge fold for cross arcs -/

def crossFoldAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat edgeListStructuredEncodedType

def crossFoldInstructionEncodedType : EncodedType :=
  EncodedType.sum EncodedType.nat edgeStructuredEncodedType

def crossFoldInstructionListEncodedType : EncodedType :=
  EncodedType.list crossFoldInstructionEncodedType

def crossFoldInit : crossFoldAccEncodedType.Carrier :=
  ((0 : Nat), ([] : List (Nat × Nat)))

def crossFoldLeftStep (vertices : Nat) : crossFoldAccEncodedType.Carrier :=
  (vertices, ([] : List (Nat × Nat)))

def crossFoldRightStep
    (p : crossFoldAccEncodedType.Carrier × (Nat × Nat)) :
    crossFoldAccEncodedType.Carrier :=
  let vertices := p.1.1
  let out : List (Nat × Nat) := p.1.2
  let edge := p.2
  (vertices, out ++ crossArcBlockForVertices vertices edge)

def crossFoldStep
    (p :
      crossFoldAccEncodedType.Carrier ×
        crossFoldInstructionEncodedType.Carrier) :
    crossFoldAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl vertices => crossFoldLeftStep vertices
  | Sum.inr edge => crossFoldRightStep (p.1, edge)

def crossFoldInstructions (g : GraphInput) :
    crossFoldInstructionListEncodedType.Carrier :=
  Sum.inl g.vertices :: g.edges.map Sum.inr

def crossFoldResult (g : GraphInput) : crossFoldAccEncodedType.Carrier :=
  (crossFoldInstructions g).foldl
    (fun acc instr => crossFoldStep (acc, instr)) crossFoldInit

def crossArcsTM (g : GraphInput) : List (Nat × Nat) :=
  (crossFoldResult g).2

theorem crossFoldEdgeInstructions_edges_eq
    (vertices : Nat) (out edges : List (Nat × Nat)) :
    ((edges.map Sum.inr).foldl
        (fun acc instr => crossFoldStep (acc, instr))
        (vertices, out)).2 =
      out ++ edges.flatMap (crossArcBlockForVertices vertices) := by
  induction edges generalizing out with
  | nil =>
      rw [List.map_nil, List.flatMap_nil, List.append_nil]
      exact
        congrArg (fun acc : crossFoldAccEncodedType.Carrier => acc.2)
          (List.foldl_nil
            (f := fun acc instr => crossFoldStep (acc, instr))
            (b := (vertices, out)))
  | cons edge edges ih =>
      simpa [crossFoldRightStep, List.append_assoc] using
        ih (out := out ++ crossArcBlockForVertices vertices edge)

theorem crossArcBlock_flatMap_eq_bounded_map
    (vertices : Nat) (edges : List (Nat × Nat)) :
    edges.flatMap (crossArcBlockForVertices vertices) =
      (edges.filter fun e => decide (e.1 < vertices ∧ e.2 < vertices)).map crossArc := by
  induction edges with
  | nil =>
      simp
  | cons edge edges ih =>
      by_cases hLeft : edge.1 < vertices <;> by_cases hRight : edge.2 < vertices <;>
        simp [crossArcBlockForVertices, hLeft, hRight, ih]

theorem crossArcsTM_eq_crossArcs (g : GraphInput) :
    crossArcsTM g = crossArcs g := by
  unfold crossArcsTM crossFoldResult crossFoldInstructions
  rw [List.foldl_cons]
  change
    ((g.edges.map Sum.inr).foldl
        (fun acc instr => crossFoldStep (acc, instr))
        (g.vertices, ([] : List (Nat × Nat)))).2 =
      crossArcs g
  rw [crossFoldEdgeInstructions_edges_eq]
  rw [crossArcBlock_flatMap_eq_bounded_map]
  simp [crossArcs, boundedSourceEdges]

theorem crossFoldLeftStep_tm_polytime :
    TMPolyTimeMap EncodedType.nat crossFoldAccEncodedType crossFoldLeftStep := by
  have hVertices : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  have hEdges :
      TMPolyTimeMap EncodedType.nat edgeListStructuredEncodedType
        (fun _ : Nat => ([] : List (Nat × Nat))) :=
    TMPolyTimeMap.const EncodedType.nat edgeListStructuredEncodedType []
  have hOut := TMPolyTimeMap.prod_mk hVertices hEdges
  simpa [crossFoldLeftStep, crossFoldAccEncodedType] using hOut

theorem crossFoldRightStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod crossFoldAccEncodedType edgeStructuredEncodedType)
      crossFoldAccEncodedType
      crossFoldRightStep := by
  let X := EncodedType.prod crossFoldAccEncodedType edgeStructuredEncodedType
  have hAcc : TMPolyTimeMap X crossFoldAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst crossFoldAccEncodedType edgeStructuredEncodedType
  have hEdge : TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd crossFoldAccEncodedType edgeStructuredEncodedType
  have hVertices : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, crossFoldAccEncodedType, X] using hComp
  have hOutEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, crossFoldAccEncodedType, X] using hComp
  have hBlockInput :
      TMPolyTimeMap X FeedbackNodeSet.edgeBlockInputEncodedType
        (fun p : X.Carrier => (p.1.1, p.2)) :=
    TMPolyTimeMap.prod_mk hVertices hEdge
  have hBlock :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier => crossArcBlockForVertices p.1.1 p.2) := by
    have hComp := TMPolyTimeMap.comp crossArcBlockForVertices_tm_polytime hBlockInput
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier =>
          ((show List (Nat × Nat) from p.1.2), crossArcBlockForVertices p.1.1 p.2)) :=
    TMPolyTimeMap.prod_mk hOutEdges hBlock
  have hAppend :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier =>
          (show List (Nat × Nat) from p.1.2) ++ crossArcBlockForVertices p.1.1 p.2) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append edgeStructuredEncodedType)
      hAppendInput
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hOut := TMPolyTimeMap.prod_mk hVertices hAppend
  simpa [crossFoldRightStep, crossFoldAccEncodedType, X] using hOut

theorem crossFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod crossFoldAccEncodedType crossFoldInstructionEncodedType)
      crossFoldAccEncodedType
      crossFoldStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      crossFoldAccEncodedType EncodedType.nat edgeStructuredEncodedType
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim crossFoldLeftStep_tm_polytime
      crossFoldRightStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

def crossFoldAccBound (N : Nat) (acc : crossFoldAccEncodedType.Carrier) : Prop :=
  EncodedType.nat.inputSize acc.1 ≤ N + 1

noncomputable def crossFoldGrowPolynomial : Polynomial Nat :=
  Polynomial.C 10 * Polynomial.X + Polynomial.C 30

@[simp] theorem crossFoldGrowPolynomial_eval (N : Nat) :
    crossFoldGrowPolynomial.eval N = 10 * N + 30 := by
  simp [crossFoldGrowPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]

theorem edgeListStructured_inputSize_append_cross
    (out block : List (Nat × Nat)) :
    edgeListStructuredEncodedType.inputSize (out ++ block) =
      edgeListStructuredEncodedType.inputSize out +
        edgeListStructuredEncodedType.inputSize block := by
  simpa [edgeListStructuredEncodedType] using
    list_inputSize_append edgeStructuredEncodedType out block

theorem crossArcBlockForVertices_inputSize_le
    (vertices : Nat) (edge : Nat × Nat) {N : Nat}
    (hVertices : EncodedType.nat.inputSize vertices ≤ N + 1) :
    edgeListStructuredEncodedType.inputSize (crossArcBlockForVertices vertices edge) ≤
      5 * N + 10 := by
  have hV : vertices ≤ N := by
    simpa [EncodedType.inputSize_nat] using hVertices
  have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 :=
    EncodedType.inputSize_list_nil edgeStructuredEncodedType
  rcases edge with ⟨u, v⟩
  by_cases hLeft : u < vertices <;> by_cases hRight : v < vertices
  · let g : GraphInput := { vertices := vertices, edges := [(u, v)], directed := true }
    have hMem : crossArc (u, v) ∈ (splitGraph g).edges := by
      exact crossArc_mem_splitGraph (g := g) (e := (u, v))
        (by simp [g]) (by simpa [g] using hLeft) (by simpa [g] using hRight)
    have hEdge :
        edgeStructuredEncodedType.inputSize (crossArc (u, v)) ≤ 4 * vertices + 1 := by
      simpa [g] using edgeStructured_inputSize_le_of_mem_splitGraph_edges (g := g) hMem
    calc
      edgeListStructuredEncodedType.inputSize (crossArcBlockForVertices vertices (u, v))
          = edgeListStructuredEncodedType.inputSize [crossArc (u, v)] := by
              simp [crossArcBlockForVertices, hLeft, hRight]
              rfl
      _ = edgeStructuredEncodedType.inputSize (crossArc (u, v)) + 1 := by
              simp [edgeListStructuredEncodedType]
      _ ≤ 4 * vertices + 2 := by omega
      _ ≤ 5 * N + 10 := by omega
  · calc
      edgeListStructuredEncodedType.inputSize (crossArcBlockForVertices vertices (u, v))
          = edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) := by
              simp [crossArcBlockForVertices, hLeft, hRight]
      _ = 0 := hNil
      _ ≤ 5 * N + 10 := by omega
  · calc
      edgeListStructuredEncodedType.inputSize (crossArcBlockForVertices vertices (u, v))
          = edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) := by
              simp [crossArcBlockForVertices, hLeft]
      _ = 0 := hNil
      _ ≤ 5 * N + 10 := by omega
  · calc
      edgeListStructuredEncodedType.inputSize (crossArcBlockForVertices vertices (u, v))
          = edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) := by
              simp [crossArcBlockForVertices, hLeft]
      _ = 0 := hNil
      _ ≤ 5 * N + 10 := by omega

theorem crossFoldStep_growth
    (source : List crossFoldInstructionEncodedType.Carrier)
    (acc : crossFoldAccEncodedType.Carrier)
    (instr : crossFoldInstructionEncodedType.Carrier)
    (hAcc :
      crossFoldAccBound
        (crossFoldInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      crossFoldInstructionEncodedType.inputSize instr ≤
        crossFoldInstructionListEncodedType.inputSize source) :
    crossFoldAccBound
        (crossFoldInstructionListEncodedType.inputSize source)
        (crossFoldStep (acc, instr)) ∧
      crossFoldAccEncodedType.inputSize (crossFoldStep (acc, instr)) ≤
        crossFoldAccEncodedType.inputSize acc +
          crossFoldGrowPolynomial.eval
            (crossFoldInstructionListEncodedType.inputSize source) := by
  let N := crossFoldInstructionListEncodedType.inputSize source
  cases instr with
  | inl vertices =>
      change Nat at vertices
      have hVerticesTagged :
          EncodedType.nat.inputSize vertices + 1 ≤ N := by
        simpa [crossFoldInstructionEncodedType, EncodedType.inputSize, EncodedType.sum,
          N, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInstr
      have hVertices : EncodedType.nat.inputSize vertices ≤ N + 1 := by omega
      constructor
      · simpa [crossFoldAccBound, crossFoldStep, crossFoldLeftStep, N] using hVertices
      · have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
          exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
        have hVerticesNat : vertices ≤ N := by
          simpa [EncodedType.inputSize_nat] using hVertices
        simp [crossFoldStep, crossFoldLeftStep, crossFoldAccEncodedType,
          EncodedType.inputSize_prod, EncodedType.inputSize_nat, hNil]
        omega
  | inr edge =>
      change Nat × Nat at edge
      constructor
      · simpa [crossFoldAccBound, crossFoldStep, crossFoldRightStep, N] using hAcc
      · let block := crossArcBlockForVertices acc.1 edge
        let out : List (Nat × Nat) := acc.2
        have hBlock :
            edgeListStructuredEncodedType.inputSize block ≤ 5 * N + 10 := by
          simpa [block] using crossArcBlockForVertices_inputSize_le acc.1 edge hAcc
        have hAppend :
            edgeListStructuredEncodedType.inputSize (out ++ block) =
              edgeListStructuredEncodedType.inputSize out +
                edgeListStructuredEncodedType.inputSize block :=
          edgeListStructured_inputSize_append_cross out block
        have hStepEq :
            crossFoldStep (acc, Sum.inr edge) =
              (acc.1, out ++ block) := by
          rfl
        rw [hStepEq]
        dsimp [out, block] at hBlock hAppend ⊢
        simp [crossFoldAccEncodedType, EncodedType.inputSize_prod]
        rw [hAppend]
        omega

theorem crossFold_tm_polytime :
    TMPolyTimeMap
      crossFoldInstructionListEncodedType
      crossFoldAccEncodedType
      (fun xs : List crossFoldInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => crossFoldStep (acc, instr)) crossFoldInit) := by
  rcases crossFoldStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      crossFoldInstructionEncodedType crossFoldAccEncodedType
      crossFoldStep crossFoldInit hStep
      (Polynomial.C 10) crossFoldGrowPolynomial
      crossFoldAccBound ?_ ?_
  · intro xs
    constructor
    · simp [crossFoldAccBound, crossFoldInit, EncodedType.inputSize_nat]
    · have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
        exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
      simp [crossFoldInit, crossFoldAccEncodedType, EncodedType.inputSize_prod,
        EncodedType.inputSize_nat, hNil]
  · intro source acc instr hAcc hInstr
    simpa [crossFoldInstructionListEncodedType] using
      crossFoldStep_growth source acc instr hAcc hInstr

theorem crossFoldInstructions_tm_polytime :
    TMPolyTimeMap
      graphStructuredEncodedType
      crossFoldInstructionListEncodedType
      crossFoldInstructions := by
  let X := graphStructuredEncodedType
  have hPayload :
      TMPolyTimeMap X graphPayloadStructuredEncodedType graphPayloadOfGraph :=
    graphPayloadTMBackedMap.tm_polytime
  have hEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun g : GraphInput => g.edges) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, graphPayloadOfGraph, graphPayloadStructuredEncodedType, X] using hComp
  have hVertices :
      TMPolyTimeMap X EncodedType.nat
        (fun g : GraphInput => g.vertices) :=
    graphVerticesTMBackedMap.tm_polytime
  have hInit :
      TMPolyTimeMap X crossFoldInstructionEncodedType
        (fun g : GraphInput => Sum.inl g.vertices) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.inl EncodedType.nat edgeStructuredEncodedType)
      hVertices
    simpa [Function.comp, crossFoldInstructionEncodedType, X] using hComp
  have hEdgeInstruction :
      TMPolyTimeMap edgeStructuredEncodedType crossFoldInstructionEncodedType
        (fun e : edgeStructuredEncodedType.Carrier => Sum.inr e) := by
    simpa [crossFoldInstructionEncodedType] using
      TMPolyTimeMap.inr EncodedType.nat edgeStructuredEncodedType
  have hMappedEdges :
      TMPolyTimeMap X crossFoldInstructionListEncodedType
        (fun g : GraphInput => g.edges.map Sum.inr) := by
    have hMap := TMPolyTimeMap.list_map hEdgeInstruction
    have hComp := TMPolyTimeMap.comp hMap hEdges
    simpa [Function.comp, crossFoldInstructionListEncodedType,
      edgeListStructuredEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod crossFoldInstructionEncodedType
          crossFoldInstructionListEncodedType)
        (fun g : GraphInput => (Sum.inl g.vertices, g.edges.map Sum.inr)) :=
    TMPolyTimeMap.prod_mk hInit hMappedEdges
  have hCons :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons crossFoldInstructionEncodedType)
      hConsInput
  simpa [Function.comp, crossFoldInstructions, crossFoldInstructionListEncodedType, X]
    using hCons

theorem crossFoldResult_tm_polytime :
    TMPolyTimeMap
      graphStructuredEncodedType
      crossFoldAccEncodedType
      crossFoldResult := by
  have hComp := TMPolyTimeMap.comp crossFold_tm_polytime crossFoldInstructions_tm_polytime
  simpa [Function.comp, crossFoldResult] using hComp

theorem crossArcsTM_tm_polytime :
    TMPolyTimeMap
      graphStructuredEncodedType
      edgeListStructuredEncodedType
      crossArcsTM := by
  have hSnd := TMPolyTimeMap.snd EncodedType.nat edgeListStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hSnd crossFoldResult_tm_polytime
  simpa [Function.comp, crossArcsTM, crossFoldAccEncodedType] using hComp

/-! ### Graph and Feedback Arc Set assembly -/

def splitGraphTM (g : GraphInput) : GraphInput where
  vertices := splitVertexCount g.vertices
  edges := splitArcsTM g ++ crossArcsTM g
  directed := true

theorem splitGraphTM_eq_splitGraph (g : GraphInput) :
    splitGraphTM g = splitGraph g := by
  cases g
  simp [splitGraphTM, splitGraph, splitVertexCount, splitArcsTM_eq_splitArcs,
    crossArcsTM_eq_crossArcs]

def feedbackNodeSetToFeedbackArcSetStructuredTMMap (I : FeedbackNodeSetInput) :
    FeedbackArcSetInput where
  graph := splitGraphTM I.graph
  k := I.k

theorem feedbackNodeSetToFeedbackArcSetStructuredTMMap_eq_textbookMap
    (I : FeedbackNodeSetInput) :
    feedbackNodeSetToFeedbackArcSetStructuredTMMap I = textbookMap I := by
  cases I
  simp [feedbackNodeSetToFeedbackArcSetStructuredTMMap, textbookMap, splitGraphTM_eq_splitGraph]

theorem splitGraphTM_tm_polytime :
    TMPolyTimeMap graphStructuredEncodedType graphStructuredEncodedType splitGraphTM := by
  let X := graphStructuredEncodedType
  have hVerticesSrc :
      TMPolyTimeMap X EncodedType.nat (fun g : GraphInput => g.vertices) :=
    graphVerticesTMBackedMap.tm_polytime
  have hVertices :
      TMPolyTimeMap X EncodedType.nat (fun g : GraphInput => splitVertexCount g.vertices) := by
    have hComp := TMPolyTimeMap.comp splitVertexCount_tm_polytime hVerticesSrc
    simpa [Function.comp, X] using hComp
  have hSplit : TMPolyTimeMap X edgeListStructuredEncodedType splitArcsTM :=
    splitArcsTM_tm_polytime
  have hCross : TMPolyTimeMap X edgeListStructuredEncodedType crossArcsTM :=
    crossArcsTM_tm_polytime
  have hEdgesInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun g : GraphInput => (splitArcsTM g, crossArcsTM g)) :=
    TMPolyTimeMap.prod_mk hSplit hCross
  have hEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun g : GraphInput => splitArcsTM g ++ crossArcsTM g) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append edgeStructuredEncodedType)
      hEdgesInput
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hDirected : TMPolyTimeMap X EncodedType.bool (fun _ : GraphInput => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hPayload :
      TMPolyTimeMap X graphPayloadStructuredEncodedType
        (fun g : GraphInput => (splitArcsTM g ++ crossArcsTM g, true)) :=
    TMPolyTimeMap.prod_mk hEdges hDirected
  have hTuple :
      TMPolyTimeMap X graphTupleStructuredEncodedType
        (fun g : GraphInput =>
          (splitVertexCount g.vertices, (splitArcsTM g ++ crossArcsTM g, true))) :=
    TMPolyTimeMap.prod_mk hVertices hPayload
  have hGraph := TMPolyTimeMap.comp Clique.graphTupleToGraphTMBackedMap.tm_polytime hTuple
  simpa [Function.comp, Clique.graphTupleToGraph, splitGraphTM, X] using hGraph

theorem feedbackNodeSetToFeedbackArcSetStructured_tm_polytime :
    TMPolyTimeMap
      feedbackNodeSetStructuredEncodedType
      feedbackArcSetStructuredEncodedType
      feedbackNodeSetToFeedbackArcSetStructuredTMMap := by
  let X := feedbackNodeSetStructuredEncodedType
  have hGraphSrc :
      TMPolyTimeMap X graphStructuredEncodedType
        (fun I : FeedbackNodeSetInput => I.graph) :=
    feedbackNodeSetGraphTMBackedMap.tm_polytime
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType
        (fun I : FeedbackNodeSetInput => splitGraphTM I.graph) := by
    have hComp := TMPolyTimeMap.comp splitGraphTM_tm_polytime hGraphSrc
    simpa [Function.comp, X] using hComp
  have hBudget :
      TMPolyTimeMap X EncodedType.nat
        (fun I : FeedbackNodeSetInput => I.k) :=
    feedbackNodeSetBudgetTMBackedMap.tm_polytime
  have hTuple :
      TMPolyTimeMap X feedbackArcSetTupleStructuredEncodedType
        (fun I : FeedbackNodeSetInput => (splitGraphTM I.graph, I.k)) :=
    TMPolyTimeMap.prod_mk hGraph hBudget
  have hOut := TMPolyTimeMap.comp feedbackArcSetTupleToInputTMBackedMap.tm_polytime hTuple
  simpa [Function.comp, feedbackArcSetTupleToInput,
    feedbackNodeSetToFeedbackArcSetStructuredTMMap, X] using hOut

/-! ### Public P16c surface -/

theorem feedbackNodeSetToFeedbackArcSetStructuredTMMap_inputSize_le_feedbackNodeSet_poly
    (I : FeedbackNodeSetInput) :
    feedbackArcSetStructuredEncodedType.inputSize
        (feedbackNodeSetToFeedbackArcSetStructuredTMMap I) ≤
      1000 * (feedbackNodeSetStructuredEncodedType.inputSize I) ^ 2 + 1000 := by
  rw [feedbackNodeSetToFeedbackArcSetStructuredTMMap_eq_textbookMap]
  exact feedbackArcSetStructured_inputSize_textbookMap_le_feedbackNodeSet_poly I

theorem feedbackNodeSetToFeedbackArcSetStructuredTMMap_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : FeedbackNodeSetInput => feedbackNodeSetStructuredEncodedType.inputSize I)
      (fun J : FeedbackArcSetInput => feedbackArcSetStructuredEncodedType.inputSize J)
      feedbackNodeSetToFeedbackArcSetStructuredTMMap := by
  refine PolynomialSizeBound.intro_with 2 1000 1000 ?_
  intro I
  exact feedbackNodeSetToFeedbackArcSetStructuredTMMap_inputSize_le_feedbackNodeSet_poly I

noncomputable def feedbackNodeSetToFeedbackArcSetStructuredTMBackedMap :
    TMBackedCostedMap
      feedbackNodeSetStructuredEncodedType
      feedbackArcSetStructuredEncodedType
      feedbackNodeSetToFeedbackArcSetStructuredTMMap where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      feedbackNodeSetToFeedbackArcSetStructuredTMMap_polynomialSizeBound
  tm_polytime := feedbackNodeSetToFeedbackArcSetStructured_tm_polytime

theorem feedbackNodeSetToFeedbackArcSetStructuredTMMap_correct (I : FeedbackNodeSetInput) :
    feedbackNodeSetStructuredDecisionProblem.isYes I ↔
      feedbackArcSetStructuredDecisionProblem.isYes
        (feedbackNodeSetToFeedbackArcSetStructuredTMMap I) := by
  rw [feedbackNodeSetToFeedbackArcSetStructuredTMMap_eq_textbookMap]
  simpa [feedbackNodeSetStructuredDecisionProblem, feedbackArcSetStructuredDecisionProblem]
    using textbookMap_correct I

noncomputable def feedbackNodeSetToFeedbackArcSetStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      feedbackNodeSetStructuredDecisionProblem
      feedbackArcSetStructuredDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    feedbackNodeSetToFeedbackArcSetStructuredTMBackedMap
    (by
      intro I
      exact feedbackNodeSetToFeedbackArcSetStructuredTMMap_correct I)

/--
Public P16c structured finite-alphabet Feedback-Node-Set-to-Feedback-Arc-Set
reduction, projected from the direct TM-backed witness.
-/
noncomputable def feedbackNodeSetToFeedbackArcSetStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      feedbackNodeSetStructuredDecisionProblem
      feedbackArcSetStructuredDecisionProblem :=
  feedbackNodeSetToFeedbackArcSetStructuredTMBackedKarpReduction.toCostedKarpReduction

/-- Compatibility alias for the former size-only structured wrapper. -/
noncomputable def feedbackNodeSetToFeedbackArcSetStructuredCostedKarpReduction :
    KarpReductionM CostedPolyTimeModel
      feedbackNodeSetStructuredDecisionProblem feedbackArcSetStructuredDecisionProblem :=
  feedbackNodeSetToFeedbackArcSetStructuredKarpReduction

noncomputable def feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction :
    TMKarpReduction
      feedbackNodeSetStructuredDecisionProblem
      feedbackArcSetStructuredDecisionProblem :=
  feedbackNodeSetToFeedbackArcSetStructuredTMBackedKarpReduction.toTMKarpReduction

end FeedbackArcSet
end Karp21
end ComplexityReduction
