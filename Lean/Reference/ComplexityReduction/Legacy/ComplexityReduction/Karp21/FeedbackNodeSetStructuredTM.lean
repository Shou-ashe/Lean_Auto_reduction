/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.FeedbackNodeSet
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.InvariantFold
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.StructuredTM.ProductSumChoice

/-!
Direct TM-backed structured assembly for the Vertex Cover to Feedback Node Set
textbook route.
-/

namespace ComplexityReduction
namespace Karp21
namespace FeedbackNodeSet

open ComplexityReduction.Combinatorics.Graph

/-! ### Small arithmetic and tuple reifiers -/

def natLtBool (p : Nat × Nat) : Bool :=
  decide (p.1 < p.2)

theorem natLtBool_eq_true_iff (p : Nat × Nat) :
    natLtBool p = true ↔ p.1 < p.2 := by
  simp [natLtBool]

theorem natLtBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.bool
      natLtBool := by
  let X := EncodedType.prod EncodedType.nat EncodedType.nat
  have hLeft : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hRight : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hSucc :
      TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.1.succ) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hLeft
    simpa [Function.comp, X] using hComp
  have hSubInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × Nat => (p.1.succ, p.2)) :=
    TMPolyTimeMap.prod_mk hSucc hRight
  have hSub :
      TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.1.succ - p.2) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_sub hSubInput
    simpa [Function.comp, X] using hComp
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : Nat × Nat => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hEqInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × Nat => (p.1.succ - p.2, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hSub hZero
  have hEq :
      TMPolyTimeMap X EncodedType.bool
        (fun p : Nat × Nat => decide (p.1.succ - p.2 = 0)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hEqInput
    simpa [Function.comp, X] using hComp
  convert hEq using 1
  funext p
  by_cases hlt : p.1 < p.2
  · have hZeroSub : p.1.succ - p.2 = 0 := by omega
    simp [natLtBool, hlt, hZeroSub]
  · have hNonzero : p.1.succ - p.2 ≠ 0 := by
      intro hZeroSub
      have hLe : p.1.succ ≤ p.2 := (Nat.sub_eq_zero_iff_le).1 hZeroSub
      have : p.1 < p.2 := by omega
      exact hlt this
    simp [natLtBool, hlt, hNonzero]

def feedbackNodeSetTupleToInput
    (p : feedbackNodeSetTupleStructuredEncodedType.Carrier) : FeedbackNodeSetInput where
  graph := p.1
  k := p.2

theorem feedbackNodeSetTupleToInput_encode
    (p : feedbackNodeSetTupleStructuredEncodedType.Carrier) :
    feedbackNodeSetStructuredEncodedType.encode (feedbackNodeSetTupleToInput p) =
      feedbackNodeSetTupleStructuredEncodedType.encode p := by
  rcases p with ⟨graph, k⟩
  rfl

noncomputable def feedbackNodeSetTupleToInputTMBackedMap :
    TMBackedCostedMap
      feedbackNodeSetTupleStructuredEncodedType
      feedbackNodeSetStructuredEncodedType
      feedbackNodeSetTupleToInput :=
  TMBackedCostedMap.ofEncodingEquiv
    feedbackNodeSetTupleStructuredEncodedType
    feedbackNodeSetStructuredEncodedType
    feedbackNodeSetTupleToInput
    (Equiv.refl feedbackNodeSetTupleStructuredEncodedType.Symbol)
    (by
      intro p
      change feedbackNodeSetStructuredEncodedType.encode (feedbackNodeSetTupleToInput p) =
        (feedbackNodeSetTupleStructuredEncodedType.encode p).map id
      simp [feedbackNodeSetTupleToInput_encode])

/-! ### Bidirected edge block runner -/

def edgeBlockInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat edgeStructuredEncodedType

def edgeEndpointLeftLtBool (p : Nat × (Nat × Nat)) : Bool :=
  natLtBool (p.2.1, p.1)

def edgeEndpointRightLtBool (p : Nat × (Nat × Nat)) : Bool :=
  natLtBool (p.2.2, p.1)

def edgeBadBool (p : Nat × (Nat × Nat)) : Bool :=
  graphBoolAndPair
    (Bool.not (edgeEndpointLeftLtBool p), Bool.not (edgeEndpointRightLtBool p))

theorem edgeEndpointLeftLtBool_eq_true_iff (p : Nat × (Nat × Nat)) :
    edgeEndpointLeftLtBool p = true ↔ p.2.1 < p.1 := by
  exact natLtBool_eq_true_iff (p.2.1, p.1)

theorem edgeEndpointRightLtBool_eq_true_iff (p : Nat × (Nat × Nat)) :
    edgeEndpointRightLtBool p = true ↔ p.2.2 < p.1 := by
  exact natLtBool_eq_true_iff (p.2.2, p.1)

theorem edgeBadBool_eq_true_iff (p : Nat × (Nat × Nat)) :
    edgeBadBool p = true ↔ ¬ p.2.1 < p.1 ∧ ¬ p.2.2 < p.1 := by
  rcases p with ⟨n, u, v⟩
  by_cases hLeft : u < n <;> by_cases hRight : v < n <;>
    simp [edgeBadBool, edgeEndpointLeftLtBool, edgeEndpointRightLtBool, natLtBool,
      hLeft, hRight, graphBoolAndPair]

def edgeToArcsForVertices (n : Nat) (e : Nat × Nat) : List (Nat × Nat) :=
  if e.1 < n then
    if e.2 < n then [(e.1, e.2), (e.2, e.1)] else [(e.1, e.1)]
  else
    if e.2 < n then [(e.2, e.2)] else []

theorem edgeToArcsForVertices_eq_edgeToArcs (g : GraphInput) (e : Nat × Nat) :
    edgeToArcsForVertices g.vertices e = edgeToArcs g e := by
  rfl

theorem edgeEndpointLeftLtBool_tm_polytime :
    TMPolyTimeMap edgeBlockInputEncodedType EncodedType.bool edgeEndpointLeftLtBool := by
  let X := edgeBlockInputEncodedType
  have hN : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, edgeBlockInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat edgeStructuredEncodedType
  have hEdge : TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, edgeBlockInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat edgeStructuredEncodedType
  have hLeft : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hEdge
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.1, p.1)) :=
    TMPolyTimeMap.prod_mk hLeft hN
  have hComp := TMPolyTimeMap.comp natLtBool_tm_polytime hInput
  simpa [Function.comp, edgeEndpointLeftLtBool, X] using hComp

theorem edgeEndpointRightLtBool_tm_polytime :
    TMPolyTimeMap edgeBlockInputEncodedType EncodedType.bool edgeEndpointRightLtBool := by
  let X := edgeBlockInputEncodedType
  have hN : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, edgeBlockInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat edgeStructuredEncodedType
  have hEdge : TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, edgeBlockInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat edgeStructuredEncodedType
  have hRight : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hEdge
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.2, p.1)) :=
    TMPolyTimeMap.prod_mk hRight hN
  have hComp := TMPolyTimeMap.comp natLtBool_tm_polytime hInput
  simpa [Function.comp, edgeEndpointRightLtBool, X] using hComp

theorem edgeBadBool_tm_polytime :
    TMPolyTimeMap edgeBlockInputEncodedType EncodedType.bool edgeBadBool := by
  let X := edgeBlockInputEncodedType
  have hLeftNot :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => Bool.not (edgeEndpointLeftLtBool p)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.bool_not edgeEndpointLeftLtBool_tm_polytime
    simpa [Function.comp, X] using hComp
  have hRightNot :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => Bool.not (edgeEndpointRightLtBool p)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.bool_not edgeEndpointRightLtBool_tm_polytime
    simpa [Function.comp, X] using hComp
  have hPair :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (Bool.not (edgeEndpointLeftLtBool p), Bool.not (edgeEndpointRightLtBool p))) :=
    TMPolyTimeMap.prod_mk hLeftNot hRightNot
  have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hPair
  simpa [Function.comp, edgeBadBool, X] using hComp

theorem edgeToArcsForVertices_tm_polytime :
    TMPolyTimeMap
      edgeBlockInputEncodedType
      edgeListStructuredEncodedType
      (fun p : edgeBlockInputEncodedType.Carrier => edgeToArcsForVertices p.1 p.2) := by
  let X := edgeBlockInputEncodedType
  have hEdge : TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, edgeBlockInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat edgeStructuredEncodedType
  have hLeftVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hEdge
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hRightVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hEdge
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hBackwardEdge :
      TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => (p.2.2, p.2.1)) := by
    have hComp := TMPolyTimeMap.comp vertexPairSwap_tm_polytime hEdge
    simpa [Function.comp, vertexPairSwap, X] using hComp
  have hForwardSingleton :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => [p.2]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton edgeStructuredEncodedType) hEdge
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hBackwardSingleton :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier => [(p.2.2, p.2.1)]) := by
    have hComp :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton edgeStructuredEncodedType)
        hBackwardEdge
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hTwoPair :
      TMPolyTimeMap X
        (EncodedType.prod edgeStructuredEncodedType edgeListStructuredEncodedType)
        (fun p : Nat × (Nat × Nat) => (p.2, [(p.2.2, p.2.1)])) :=
    TMPolyTimeMap.prod_mk hEdge hBackwardSingleton
  have hTwo :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : Nat × (Nat × Nat) => [p.2, (p.2.2, p.2.1)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons edgeStructuredEncodedType)
      hTwoPair
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hLeftLoopEdge :
      TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => (p.2.1, p.2.1)) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.prod_diag EncodedType.nat) hLeftVertex
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hRightLoopEdge :
      TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => (p.2.2, p.2.2)) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.prod_diag EncodedType.nat) hRightVertex
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hLeftLoop :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier => [(p.2.1, p.2.1)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton edgeStructuredEncodedType)
      hLeftLoopEdge
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hRightLoop :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier => [(p.2.2, p.2.2)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton edgeStructuredEncodedType)
      hRightLoopEdge
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hEmpty :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun _ : X.Carrier => ([] : List (Nat × Nat))) :=
    TMPolyTimeMap.const X edgeListStructuredEncodedType []
  have hRightBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (edgeEndpointRightLtBool p, p)) :=
    TMPolyTimeMap.prod_mk edgeEndpointRightLtBool_tm_polytime (TMPolyTimeMap.id X)
  have hLeftTrueBranch :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier =>
          match edgeEndpointRightLtBool p with
          | true => [p.2, (p.2.2, p.2.1)]
          | false => [(p.2.1, p.2.1)]) := by
    have hBranch :=
      graphBoolProduct_dispatch_tm_polytime X edgeListStructuredEncodedType
        (fFalse := fun p : X.Carrier => [(p.2.1, p.2.1)])
        (fTrue := fun p : Nat × (Nat × Nat) => [p.2, (p.2.2, p.2.1)])
        hLeftLoop hTwo
    have hComp := TMPolyTimeMap.comp hBranch hRightBranchInput
    simpa [Function.comp, X] using hComp
  have hLeftFalseBranch :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier =>
          match edgeEndpointRightLtBool p with
          | true => [(p.2.2, p.2.2)]
          | false => []) := by
    have hBranch :=
      graphBoolProduct_dispatch_tm_polytime X edgeListStructuredEncodedType
        (fFalse := fun _ : X.Carrier => ([] : List (Nat × Nat)))
        (fTrue := fun p : X.Carrier => [(p.2.2, p.2.2)])
        hEmpty hRightLoop
    have hComp := TMPolyTimeMap.comp hBranch hRightBranchInput
    simpa [Function.comp, X] using hComp
  have hLeftBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (edgeEndpointLeftLtBool p, p)) :=
    TMPolyTimeMap.prod_mk edgeEndpointLeftLtBool_tm_polytime (TMPolyTimeMap.id X)
  have hBranch :=
    graphBoolProduct_dispatch_tm_polytime X edgeListStructuredEncodedType
      (fFalse := fun p : X.Carrier =>
        match edgeEndpointRightLtBool p with
        | true => [(p.2.2, p.2.2)]
        | false => [])
      (fTrue := fun p : X.Carrier =>
        match edgeEndpointRightLtBool p with
        | true => [p.2, (p.2.2, p.2.1)]
        | false => [(p.2.1, p.2.1)])
      hLeftFalseBranch hLeftTrueBranch
  have hOut := TMPolyTimeMap.comp hBranch hLeftBranchInput
  convert hOut using 1
  funext p
  change Nat × (Nat × Nat) at p
  by_cases hLeft : p.2.1 < p.1 <;> by_cases hRight : p.2.2 < p.1
  · simp [Function.comp, edgeToArcsForVertices, edgeEndpointLeftLtBool,
      edgeEndpointRightLtBool, natLtBool, hLeft, hRight]
    rfl
  · simp [Function.comp, edgeToArcsForVertices, edgeEndpointLeftLtBool,
      edgeEndpointRightLtBool, natLtBool, hLeft, hRight]
    rfl
  · simp [Function.comp, edgeToArcsForVertices, edgeEndpointLeftLtBool,
      edgeEndpointRightLtBool, natLtBool, hLeft, hRight]
    rfl
  · simp [Function.comp, edgeToArcsForVertices, edgeEndpointLeftLtBool,
      edgeEndpointRightLtBool, natLtBool, hLeft, hRight]
    rfl

def bidirectedFoldFlaggedEdgesEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool edgeListStructuredEncodedType

def bidirectedFoldAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat bidirectedFoldFlaggedEdgesEncodedType

def bidirectedFoldInstructionEncodedType : EncodedType :=
  EncodedType.sum EncodedType.nat edgeStructuredEncodedType

def bidirectedFoldInstructionListEncodedType : EncodedType :=
  EncodedType.list bidirectedFoldInstructionEncodedType

def bidirectedFoldInit : bidirectedFoldAccEncodedType.Carrier :=
  ((0 : Nat), (false, ([] : List (Nat × Nat))))

def bidirectedFoldLeftStep (vertices : Nat) : bidirectedFoldAccEncodedType.Carrier :=
  (vertices, (false, ([] : List (Nat × Nat))))

def bidirectedFoldRightStep
    (p : bidirectedFoldAccEncodedType.Carrier × (Nat × Nat)) :
    bidirectedFoldAccEncodedType.Carrier :=
  let vertices := p.1.1
  let bad := p.1.2.1
  let out : List (Nat × Nat) := p.1.2.2
  let edge := p.2
  (vertices,
    (graphBoolOrPair (bad, edgeBadBool (vertices, edge)),
      out ++ edgeToArcsForVertices vertices edge))

def bidirectedFoldStep
    (p :
      bidirectedFoldAccEncodedType.Carrier ×
        bidirectedFoldInstructionEncodedType.Carrier) :
    bidirectedFoldAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl vertices => bidirectedFoldLeftStep vertices
  | Sum.inr edge => bidirectedFoldRightStep (p.1, edge)

def bidirectedFoldInstructions (I : VertexCoverInput) :
    bidirectedFoldInstructionListEncodedType.Carrier :=
  Sum.inl I.graph.vertices :: I.graph.edges.map Sum.inr

def bidirectedFoldResult (I : VertexCoverInput) : bidirectedFoldAccEncodedType.Carrier :=
  (bidirectedFoldInstructions I).foldl
    (fun acc instr => bidirectedFoldStep (acc, instr)) bidirectedFoldInit

def hasUncoverableEdgeTM (I : VertexCoverInput) : Bool :=
  (bidirectedFoldResult I).2.1

def textbookEdgesTM (I : VertexCoverInput) : List (Nat × Nat) :=
  (bidirectedFoldResult I).2.2

def textbookGraphTM (I : VertexCoverInput) : GraphInput where
  vertices := I.graph.vertices
  edges := textbookEdgesTM I
  directed := true

def vertexCoverToFeedbackNodeSetStructuredTMMap (I : VertexCoverInput) :
    FeedbackNodeSetInput :=
  if hasUncoverableEdgeTM I then
    noInput
  else
    { graph := textbookGraphTM I
      k := I.k }

/-! ### Semantic alignment -/

theorem bidirectedFoldEdgeInstructions_edges_eq
    (vertices : Nat) (bad : Bool) (out edges : List (Nat × Nat)) :
    ((edges.map Sum.inr).foldl
        (fun acc instr => bidirectedFoldStep (acc, instr))
        (vertices, (bad, out))).2.2 =
      out ++ edges.flatMap (edgeToArcsForVertices vertices) := by
  induction edges generalizing bad out with
  | nil =>
      rw [List.map_nil, List.flatMap_nil, List.append_nil]
      exact
        congrArg (fun acc : bidirectedFoldAccEncodedType.Carrier => acc.2.2)
          (List.foldl_nil
            (f := fun acc instr => bidirectedFoldStep (acc, instr))
            (b := (vertices, (bad, out))))
  | cons edge edges ih =>
      simpa [bidirectedFoldRightStep, List.append_assoc] using
        ih
          (bad := graphBoolOrPair (bad, edgeBadBool (vertices, edge)))
          (out := out ++ edgeToArcsForVertices vertices edge)

theorem bidirectedFoldEdgeInstructions_bad_iff
    (vertices : Nat) (bad : Bool) (out edges : List (Nat × Nat)) :
    ((edges.map Sum.inr).foldl
        (fun acc instr => bidirectedFoldStep (acc, instr))
        (vertices, (bad, out))).2.1 = true ↔
      bad = true ∨ ∃ e ∈ edges, edgeBadBool (vertices, e) = true := by
  induction edges generalizing bad out with
  | nil =>
      cases bad <;> simp [List.foldl]
  | cons edge edges ih =>
      simpa [bidirectedFoldRightStep, graphBoolOrPair_eq_true_iff, or_assoc, or_left_comm,
        or_comm] using
        ih
          (bad := graphBoolOrPair (bad, edgeBadBool (vertices, edge)))
          (out := out ++ edgeToArcsForVertices vertices edge)

theorem textbookEdgesTM_eq_textbookEdges (I : VertexCoverInput) :
    textbookEdgesTM I = textbookEdges I.graph := by
  unfold textbookEdgesTM bidirectedFoldResult bidirectedFoldInstructions
  rw [List.foldl_cons]
  change
    ((I.graph.edges.map Sum.inr).foldl
        (fun acc instr => bidirectedFoldStep (acc, instr))
        (I.graph.vertices, (false, ([] : List (Nat × Nat))))).2.2 =
      textbookEdges I.graph
  rw [bidirectedFoldEdgeInstructions_edges_eq]
  simp [textbookEdges]
  apply List.flatMap_congr
  intro e _
  exact edgeToArcsForVertices_eq_edgeToArcs I.graph e

theorem hasUncoverableEdgeTM_eq_true_iff (I : VertexCoverInput) :
    hasUncoverableEdgeTM I = true ↔ HasUncoverableEdge I.graph := by
  unfold hasUncoverableEdgeTM bidirectedFoldResult bidirectedFoldInstructions
  rw [List.foldl_cons]
  change
    ((I.graph.edges.map Sum.inr).foldl
        (fun acc instr => bidirectedFoldStep (acc, instr))
        (I.graph.vertices, (false, ([] : List (Nat × Nat))))).2.1 = true ↔
      HasUncoverableEdge I.graph
  rw [bidirectedFoldEdgeInstructions_bad_iff]
  change
    (false = true ∨ ∃ e ∈ I.graph.edges,
      edgeBadBool (I.graph.vertices, e) = true) ↔
      (∃ e ∈ I.graph.edges, ¬ e.1 < I.graph.vertices ∧ ¬ e.2 < I.graph.vertices)
  simp only [Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨e, he, hBad⟩
    exact ⟨e, he, (edgeBadBool_eq_true_iff (I.graph.vertices, e)).1 hBad⟩
  · rintro ⟨e, he, hBad⟩
    exact ⟨e, he, (edgeBadBool_eq_true_iff (I.graph.vertices, e)).2 hBad⟩

theorem textbookGraphTM_eq_textbookGraph (I : VertexCoverInput) :
    textbookGraphTM I = textbookGraph I.graph := by
  cases I
  simp [textbookGraphTM, textbookGraph, textbookEdgesTM_eq_textbookEdges]

theorem vertexCoverToFeedbackNodeSetStructuredTMMap_eq_textbookMap
    (I : VertexCoverInput) :
    vertexCoverToFeedbackNodeSetStructuredTMMap I = textbookMap I := by
  by_cases hBadBool : hasUncoverableEdgeTM I = true
  · have hBad : HasUncoverableEdge I.graph :=
      (hasUncoverableEdgeTM_eq_true_iff I).1 hBadBool
    simp [vertexCoverToFeedbackNodeSetStructuredTMMap, hBadBool, textbookMap, hBad]
  · have hBadFalse : hasUncoverableEdgeTM I = false := by
      cases h : hasUncoverableEdgeTM I
      · rfl
      · exact False.elim (hBadBool h)
    have hNoBad : ¬ HasUncoverableEdge I.graph := by
      intro hBad
      exact hBadBool ((hasUncoverableEdgeTM_eq_true_iff I).2 hBad)
    simp [vertexCoverToFeedbackNodeSetStructuredTMMap, hBadFalse, textbookMap, hNoBad,
      textbookGraphTM_eq_textbookGraph]

/-! ### TM-backed fold proof -/

theorem bidirectedFoldLeftStep_tm_polytime :
    TMPolyTimeMap EncodedType.nat bidirectedFoldAccEncodedType bidirectedFoldLeftStep := by
  have hVertices : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  have hBad :
      TMPolyTimeMap EncodedType.nat EncodedType.bool (fun _ : Nat => false) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool false
  have hEdges :
      TMPolyTimeMap EncodedType.nat edgeListStructuredEncodedType
        (fun _ : Nat => ([] : List (Nat × Nat))) :=
    TMPolyTimeMap.const EncodedType.nat edgeListStructuredEncodedType []
  have hPayload :
      TMPolyTimeMap EncodedType.nat bidirectedFoldFlaggedEdgesEncodedType
        (fun _ : Nat => (false, ([] : List (Nat × Nat)))) :=
    TMPolyTimeMap.prod_mk hBad hEdges
  have hOut := TMPolyTimeMap.prod_mk hVertices hPayload
  simpa [bidirectedFoldLeftStep, bidirectedFoldAccEncodedType,
    bidirectedFoldFlaggedEdgesEncodedType] using hOut

theorem bidirectedFoldRightStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod bidirectedFoldAccEncodedType edgeStructuredEncodedType)
      bidirectedFoldAccEncodedType
      bidirectedFoldRightStep := by
  let X := EncodedType.prod bidirectedFoldAccEncodedType edgeStructuredEncodedType
  have hAcc : TMPolyTimeMap X bidirectedFoldAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst bidirectedFoldAccEncodedType edgeStructuredEncodedType
  have hEdge : TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd bidirectedFoldAccEncodedType edgeStructuredEncodedType
  have hVertices : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat bidirectedFoldFlaggedEdgesEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, bidirectedFoldAccEncodedType, X] using hComp
  have hFlagged :
      TMPolyTimeMap X bidirectedFoldFlaggedEdgesEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat bidirectedFoldFlaggedEdgesEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, bidirectedFoldAccEncodedType, X] using hComp
  have hBad : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hFlagged
    simpa [Function.comp, bidirectedFoldFlaggedEdgesEncodedType, X] using hComp
  have hOutEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hFlagged
    simpa [Function.comp, bidirectedFoldFlaggedEdgesEncodedType, X] using hComp
  have hBlockInput :
      TMPolyTimeMap X edgeBlockInputEncodedType (fun p : X.Carrier => (p.1.1, p.2)) :=
    TMPolyTimeMap.prod_mk hVertices hEdge
  have hEdgeBad :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => edgeBadBool (p.1.1, p.2)) := by
    have hComp := TMPolyTimeMap.comp edgeBadBool_tm_polytime hBlockInput
    simpa [Function.comp, X] using hComp
  have hNewBadInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier => (p.1.2.1, edgeBadBool (p.1.1, p.2))) :=
    TMPolyTimeMap.prod_mk hBad hEdgeBad
  have hNewBad :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => graphBoolOrPair (p.1.2.1, edgeBadBool (p.1.1, p.2))) := by
    have hComp := TMPolyTimeMap.comp graphBoolOrPair_tm_polytime hNewBadInput
    simpa [Function.comp, X] using hComp
  have hBlock :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier => edgeToArcsForVertices p.1.1 p.2) := by
    have hComp := TMPolyTimeMap.comp edgeToArcsForVertices_tm_polytime hBlockInput
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier => (p.1.2.2, edgeToArcsForVertices p.1.1 p.2)) :=
    TMPolyTimeMap.prod_mk hOutEdges hBlock
  have hAppend :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier =>
          (show List (Nat × Nat) from p.1.2.2) ++ edgeToArcsForVertices p.1.1 p.2) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append edgeStructuredEncodedType)
      hAppendInput
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hFlaggedOut :
      TMPolyTimeMap X bidirectedFoldFlaggedEdgesEncodedType
        (fun p : X.Carrier =>
          (graphBoolOrPair (p.1.2.1, edgeBadBool (p.1.1, p.2)),
            (show List (Nat × Nat) from p.1.2.2) ++ edgeToArcsForVertices p.1.1 p.2)) :=
    TMPolyTimeMap.prod_mk hNewBad hAppend
  have hOut := TMPolyTimeMap.prod_mk hVertices hFlaggedOut
  simpa [bidirectedFoldRightStep, bidirectedFoldAccEncodedType,
    bidirectedFoldFlaggedEdgesEncodedType, X] using hOut

theorem bidirectedFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod bidirectedFoldAccEncodedType bidirectedFoldInstructionEncodedType)
      bidirectedFoldAccEncodedType
      bidirectedFoldStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      bidirectedFoldAccEncodedType EncodedType.nat edgeStructuredEncodedType
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim bidirectedFoldLeftStep_tm_polytime
      bidirectedFoldRightStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

def bidirectedFoldAccBound (N : Nat) (acc : bidirectedFoldAccEncodedType.Carrier) : Prop :=
  EncodedType.nat.inputSize acc.1 ≤ N + 1

noncomputable def bidirectedFoldGrowPolynomial : Polynomial Nat :=
  Polynomial.C 10 * Polynomial.X + Polynomial.C 30

@[simp] theorem bidirectedFoldGrowPolynomial_eval (N : Nat) :
    bidirectedFoldGrowPolynomial.eval N = 10 * N + 30 := by
  simp [bidirectedFoldGrowPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]

theorem edgeListStructured_inputSize_append_block
    (out block : List (Nat × Nat)) :
    edgeListStructuredEncodedType.inputSize (out ++ block) =
      edgeListStructuredEncodedType.inputSize out +
        edgeListStructuredEncodedType.inputSize block := by
  simpa [edgeListStructuredEncodedType] using
    list_inputSize_append edgeStructuredEncodedType out block

theorem edgeToArcsForVertices_inputSize_le
    (vertices : Nat) (edge : Nat × Nat) {N : Nat}
    (hVertices : EncodedType.nat.inputSize vertices ≤ N + 1) :
    edgeListStructuredEncodedType.inputSize (edgeToArcsForVertices vertices edge) ≤
      5 * N + 10 := by
  have hV : vertices ≤ N := by
    simpa [EncodedType.inputSize_nat] using hVertices
  let g : GraphInput := { vertices := vertices, edges := [], directed := true }
  have hList :
      edgeListStructuredEncodedType.inputSize (edgeToArcsForVertices vertices edge) ≤
        (edgeToArcsForVertices vertices edge).length * (2 * vertices + 2) := by
    refine
      VertexCover.encodedList_inputSize_le_length_mul_bound edgeStructuredEncodedType
        (edgeToArcsForVertices vertices edge) (2 * vertices + 1) ?_
    intro arc hArc
    have hArc' : arc ∈ edgeToArcs g edge := by
      simpa [g, edgeToArcsForVertices_eq_edgeToArcs] using hArc
    have hBounds := edgeToArcs_within_bounds (g := g) (e := edge) (arc := arc) hArc'
    exact VertexCover.edgeStructured_inputSize_le_of_bounds (g := g) (e := arc) hBounds
  have hLen : (edgeToArcsForVertices vertices edge).length ≤ 2 := by
    have h := edgeToArcs_length_le_two g edge
    simpa [g, edgeToArcsForVertices_eq_edgeToArcs] using h
  have hCoarse :
      (edgeToArcsForVertices vertices edge).length * (2 * vertices + 2) ≤
        2 * (2 * vertices + 2) := by
    exact Nat.mul_le_mul_right (2 * vertices + 2) hLen
  calc
    edgeListStructuredEncodedType.inputSize (edgeToArcsForVertices vertices edge)
        ≤ (edgeToArcsForVertices vertices edge).length * (2 * vertices + 2) := hList
    _ ≤ 2 * (2 * vertices + 2) := hCoarse
    _ ≤ 5 * N + 10 := by nlinarith

theorem bidirectedFoldStep_growth
    (source : List bidirectedFoldInstructionEncodedType.Carrier)
    (acc : bidirectedFoldAccEncodedType.Carrier)
    (instr : bidirectedFoldInstructionEncodedType.Carrier)
    (hAcc :
      bidirectedFoldAccBound
        (bidirectedFoldInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      bidirectedFoldInstructionEncodedType.inputSize instr ≤
        bidirectedFoldInstructionListEncodedType.inputSize source) :
    bidirectedFoldAccBound
        (bidirectedFoldInstructionListEncodedType.inputSize source)
        (bidirectedFoldStep (acc, instr)) ∧
      bidirectedFoldAccEncodedType.inputSize (bidirectedFoldStep (acc, instr)) ≤
        bidirectedFoldAccEncodedType.inputSize acc +
          bidirectedFoldGrowPolynomial.eval
            (bidirectedFoldInstructionListEncodedType.inputSize source) := by
  let N := bidirectedFoldInstructionListEncodedType.inputSize source
  cases instr with
  | inl vertices =>
      change Nat at vertices
      have hVerticesTagged :
          EncodedType.nat.inputSize vertices + 1 ≤ N := by
        simpa [bidirectedFoldInstructionEncodedType, EncodedType.inputSize, EncodedType.sum,
          N, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInstr
      have hVertices : EncodedType.nat.inputSize vertices ≤ N + 1 := by omega
      constructor
      · simpa [bidirectedFoldAccBound, bidirectedFoldStep, bidirectedFoldLeftStep, N]
          using hVertices
      · have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
          exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
        have hVerticesNat : vertices ≤ N := by
          simpa [EncodedType.inputSize_nat] using hVertices
        simp [bidirectedFoldStep, bidirectedFoldLeftStep, bidirectedFoldAccEncodedType,
          bidirectedFoldFlaggedEdgesEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_bool, hNil]
        omega
  | inr edge =>
      change Nat × Nat at edge
      constructor
      · simpa [bidirectedFoldAccBound, bidirectedFoldStep, bidirectedFoldRightStep, N]
          using hAcc
      · let block := edgeToArcsForVertices acc.1 edge
        let out : List (Nat × Nat) := acc.2.2
        have hBlock :
            edgeListStructuredEncodedType.inputSize block ≤ 5 * N + 10 := by
          simpa [block] using edgeToArcsForVertices_inputSize_le acc.1 edge hAcc
        have hAppend :
            edgeListStructuredEncodedType.inputSize (out ++ block) =
              edgeListStructuredEncodedType.inputSize out +
                edgeListStructuredEncodedType.inputSize block :=
          edgeListStructured_inputSize_append_block out block
        have hStepEq :
            bidirectedFoldStep (acc, Sum.inr edge) =
              (acc.1,
                (graphBoolOrPair (acc.2.1, edgeBadBool (acc.1, edge)),
                  out ++ block)) := by
          rfl
        rw [hStepEq]
        dsimp [out, block] at hBlock hAppend ⊢
        simp [bidirectedFoldAccEncodedType, bidirectedFoldFlaggedEdgesEncodedType,
          EncodedType.inputSize_prod, EncodedType.inputSize_bool]
        rw [hAppend]
        omega

theorem bidirectedFold_tm_polytime :
    TMPolyTimeMap
      bidirectedFoldInstructionListEncodedType
      bidirectedFoldAccEncodedType
      (fun xs : List bidirectedFoldInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => bidirectedFoldStep (acc, instr)) bidirectedFoldInit) := by
  rcases bidirectedFoldStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      bidirectedFoldInstructionEncodedType bidirectedFoldAccEncodedType
      bidirectedFoldStep bidirectedFoldInit hStep
      (Polynomial.C 10) bidirectedFoldGrowPolynomial
      bidirectedFoldAccBound ?_ ?_
  · intro xs
    constructor
    · simp [bidirectedFoldAccBound, bidirectedFoldInit, EncodedType.inputSize_nat]
    · have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
        exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
      simp [bidirectedFoldInit, bidirectedFoldAccEncodedType,
        bidirectedFoldFlaggedEdgesEncodedType, EncodedType.inputSize_prod,
        EncodedType.inputSize_nat, EncodedType.inputSize_bool, hNil]
  · intro source acc instr hAcc hInstr
    simpa [bidirectedFoldInstructionListEncodedType] using
      bidirectedFoldStep_growth source acc instr hAcc hInstr

theorem bidirectedFoldInstructions_tm_polytime :
    TMPolyTimeMap
      vertexCoverStructuredEncodedType
      bidirectedFoldInstructionListEncodedType
      bidirectedFoldInstructions := by
  let X := vertexCoverStructuredEncodedType
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType
        (fun I : VertexCoverInput => I.graph) := by
    simpa [X] using vertexCoverGraphTMBackedMap.tm_polytime
  have hPayload :
      TMPolyTimeMap X graphPayloadStructuredEncodedType
        (fun I : VertexCoverInput => graphPayloadOfGraph I.graph) := by
    have hComp := TMPolyTimeMap.comp graphPayloadTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun I : VertexCoverInput => I.graph.edges) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, graphPayloadOfGraph, graphPayloadStructuredEncodedType, X] using hComp
  have hVertices :
      TMPolyTimeMap X EncodedType.nat
        (fun I : VertexCoverInput => I.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp graphVerticesTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hInit :
      TMPolyTimeMap X bidirectedFoldInstructionEncodedType
        (fun I : VertexCoverInput => Sum.inl I.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.inl EncodedType.nat edgeStructuredEncodedType)
      hVertices
    simpa [Function.comp, bidirectedFoldInstructionEncodedType, X] using hComp
  have hEdgeInstruction :
      TMPolyTimeMap edgeStructuredEncodedType bidirectedFoldInstructionEncodedType
        (fun e : edgeStructuredEncodedType.Carrier => Sum.inr e) := by
    simpa [bidirectedFoldInstructionEncodedType] using
      TMPolyTimeMap.inr EncodedType.nat edgeStructuredEncodedType
  have hMappedEdges :
      TMPolyTimeMap X bidirectedFoldInstructionListEncodedType
        (fun I : VertexCoverInput => I.graph.edges.map Sum.inr) := by
    have hMap := TMPolyTimeMap.list_map hEdgeInstruction
    have hComp := TMPolyTimeMap.comp hMap hEdges
    simpa [Function.comp, bidirectedFoldInstructionListEncodedType,
      edgeListStructuredEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod bidirectedFoldInstructionEncodedType
          bidirectedFoldInstructionListEncodedType)
        (fun I : VertexCoverInput => (Sum.inl I.graph.vertices, I.graph.edges.map Sum.inr)) :=
    TMPolyTimeMap.prod_mk hInit hMappedEdges
  have hCons :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons bidirectedFoldInstructionEncodedType)
      hConsInput
  simpa [Function.comp, bidirectedFoldInstructions, bidirectedFoldInstructionListEncodedType, X]
    using hCons

theorem bidirectedFoldResult_tm_polytime :
    TMPolyTimeMap
      vertexCoverStructuredEncodedType
      bidirectedFoldAccEncodedType
      bidirectedFoldResult := by
  have hComp := TMPolyTimeMap.comp bidirectedFold_tm_polytime bidirectedFoldInstructions_tm_polytime
  simpa [Function.comp, bidirectedFoldResult] using hComp

theorem hasUncoverableEdgeTM_tm_polytime :
    TMPolyTimeMap
      vertexCoverStructuredEncodedType
      EncodedType.bool
      hasUncoverableEdgeTM := by
  have hBad := TMPolyTimeMap.fst EncodedType.bool edgeListStructuredEncodedType
  have hPayload :
      TMPolyTimeMap bidirectedFoldAccEncodedType bidirectedFoldFlaggedEdgesEncodedType
        (fun acc : bidirectedFoldAccEncodedType.Carrier => acc.2) :=
    TMPolyTimeMap.snd EncodedType.nat bidirectedFoldFlaggedEdgesEncodedType
  have hBadFromAcc := TMPolyTimeMap.comp hBad hPayload
  have hComp := TMPolyTimeMap.comp hBadFromAcc bidirectedFoldResult_tm_polytime
  simpa [Function.comp, hasUncoverableEdgeTM, bidirectedFoldAccEncodedType,
    bidirectedFoldFlaggedEdgesEncodedType] using hComp

theorem textbookEdgesTM_tm_polytime :
    TMPolyTimeMap
      vertexCoverStructuredEncodedType
      edgeListStructuredEncodedType
      textbookEdgesTM := by
  have hEdges := TMPolyTimeMap.snd EncodedType.bool edgeListStructuredEncodedType
  have hPayload :
      TMPolyTimeMap bidirectedFoldAccEncodedType bidirectedFoldFlaggedEdgesEncodedType
        (fun acc : bidirectedFoldAccEncodedType.Carrier => acc.2) :=
    TMPolyTimeMap.snd EncodedType.nat bidirectedFoldFlaggedEdgesEncodedType
  have hEdgesFromAcc := TMPolyTimeMap.comp hEdges hPayload
  have hComp := TMPolyTimeMap.comp hEdgesFromAcc bidirectedFoldResult_tm_polytime
  simpa [Function.comp, textbookEdgesTM, bidirectedFoldAccEncodedType,
    bidirectedFoldFlaggedEdgesEncodedType] using hComp

theorem textbookGraphTM_tm_polytime :
    TMPolyTimeMap
      vertexCoverStructuredEncodedType
      graphStructuredEncodedType
      textbookGraphTM := by
  let X := vertexCoverStructuredEncodedType
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType
        (fun I : VertexCoverInput => I.graph) := by
    simpa [X] using vertexCoverGraphTMBackedMap.tm_polytime
  have hVertices :
      TMPolyTimeMap X EncodedType.nat
        (fun I : VertexCoverInput => I.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp graphVerticesTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hDirected :
      TMPolyTimeMap X EncodedType.bool (fun _ : VertexCoverInput => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hPayload :
      TMPolyTimeMap X graphPayloadStructuredEncodedType
        (fun I : VertexCoverInput => (textbookEdgesTM I, true)) :=
    TMPolyTimeMap.prod_mk textbookEdgesTM_tm_polytime hDirected
  have hTuple :
      TMPolyTimeMap X graphTupleStructuredEncodedType
        (fun I : VertexCoverInput => (I.graph.vertices, (textbookEdgesTM I, true))) :=
    TMPolyTimeMap.prod_mk hVertices hPayload
  have hComp := TMPolyTimeMap.comp Clique.graphTupleToGraphTMBackedMap.tm_polytime hTuple
  simpa [Function.comp, Clique.graphTupleToGraph, textbookGraphTM, X] using hComp

theorem vertexCoverToFeedbackNodeSetStructured_tm_polytime :
    TMPolyTimeMap
      vertexCoverStructuredEncodedType
      feedbackNodeSetStructuredEncodedType
      vertexCoverToFeedbackNodeSetStructuredTMMap := by
  let X := vertexCoverStructuredEncodedType
  have hBudget :
      TMPolyTimeMap X EncodedType.nat
        (fun I : VertexCoverInput => I.k) := by
    simpa [X] using vertexCoverBudgetTMBackedMap.tm_polytime
  have hRegularTuple :
      TMPolyTimeMap X feedbackNodeSetTupleStructuredEncodedType
        (fun I : VertexCoverInput => (textbookGraphTM I, I.k)) :=
    TMPolyTimeMap.prod_mk textbookGraphTM_tm_polytime hBudget
  have hRegular :
      TMPolyTimeMap X feedbackNodeSetStructuredEncodedType
        (fun I : VertexCoverInput =>
          { graph := textbookGraphTM I
            k := I.k }) := by
    have hComp := TMPolyTimeMap.comp feedbackNodeSetTupleToInputTMBackedMap.tm_polytime
      hRegularTuple
    simpa [Function.comp, feedbackNodeSetTupleToInput, X] using hComp
  have hNo :
      TMPolyTimeMap X feedbackNodeSetStructuredEncodedType
        (fun _ : VertexCoverInput => noInput) :=
    TMPolyTimeMap.const X feedbackNodeSetStructuredEncodedType noInput
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun I : VertexCoverInput => (hasUncoverableEdgeTM I, I)) :=
    TMPolyTimeMap.prod_mk hasUncoverableEdgeTM_tm_polytime (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool X)
        feedbackNodeSetStructuredEncodedType
        (fun p : Bool × VertexCoverInput =>
          match p.1 with
          | true => noInput
          | false =>
              { graph := textbookGraphTM p.2
                k := p.2.k }) :=
    graphBoolProduct_dispatch_tm_polytime X feedbackNodeSetStructuredEncodedType
      (fFalse := fun I : VertexCoverInput =>
        { graph := textbookGraphTM I
          k := I.k })
      (fTrue := fun _ : VertexCoverInput => noInput)
      hRegular hNo
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext I
  cases h : hasUncoverableEdgeTM I <;>
    simp [Function.comp, vertexCoverToFeedbackNodeSetStructuredTMMap, h]

/-! ### Public P16c surface -/

theorem vertexCoverToFeedbackNodeSetStructuredTMMap_inputSize_le_vertexCover_poly
    (I : VertexCoverInput) :
    feedbackNodeSetStructuredEncodedType.inputSize
        (vertexCoverToFeedbackNodeSetStructuredTMMap I) ≤
      1000 * (vertexCoverStructuredEncodedType.inputSize I) ^ 2 + 1000 := by
  rw [vertexCoverToFeedbackNodeSetStructuredTMMap_eq_textbookMap]
  exact feedbackNodeSetStructured_inputSize_textbookMap_le_vertexCover_poly I

theorem vertexCoverToFeedbackNodeSetStructuredTMMap_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : VertexCoverInput => vertexCoverStructuredEncodedType.inputSize I)
      (fun J : FeedbackNodeSetInput => feedbackNodeSetStructuredEncodedType.inputSize J)
      vertexCoverToFeedbackNodeSetStructuredTMMap := by
  refine PolynomialSizeBound.intro_with 2 1000 1000 ?_
  intro I
  exact vertexCoverToFeedbackNodeSetStructuredTMMap_inputSize_le_vertexCover_poly I

noncomputable def vertexCoverToFeedbackNodeSetStructuredTMBackedMap :
    TMBackedCostedMap
      vertexCoverStructuredEncodedType
      feedbackNodeSetStructuredEncodedType
      vertexCoverToFeedbackNodeSetStructuredTMMap where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      vertexCoverToFeedbackNodeSetStructuredTMMap_polynomialSizeBound
  tm_polytime := vertexCoverToFeedbackNodeSetStructured_tm_polytime

theorem vertexCoverToFeedbackNodeSetStructuredTMMap_correct (I : VertexCoverInput) :
    vertexCoverStructuredDecisionProblem.isYes I ↔
      feedbackNodeSetStructuredDecisionProblem.isYes
        (vertexCoverToFeedbackNodeSetStructuredTMMap I) := by
  rw [vertexCoverToFeedbackNodeSetStructuredTMMap_eq_textbookMap]
  simpa [vertexCoverStructuredDecisionProblem, feedbackNodeSetStructuredDecisionProblem,
    vertexCoverDecisionProblem] using textbookMap_correct I

noncomputable def vertexCoverToFeedbackNodeSetStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      vertexCoverStructuredDecisionProblem
      feedbackNodeSetStructuredDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    vertexCoverToFeedbackNodeSetStructuredTMBackedMap
    (by
      intro I
      exact vertexCoverToFeedbackNodeSetStructuredTMMap_correct I)

/--
Public P16c structured finite-alphabet Vertex-Cover-to-Feedback-Node-Set
reduction, projected from the direct TM-backed witness.
-/
noncomputable def vertexCoverToFeedbackNodeSetStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      vertexCoverStructuredDecisionProblem
      feedbackNodeSetStructuredDecisionProblem :=
  vertexCoverToFeedbackNodeSetStructuredTMBackedKarpReduction.toCostedKarpReduction

/-- Compatibility alias for the former size-only structured wrapper. -/
noncomputable def vertexCoverToFeedbackNodeSetStructuredCostedKarpReduction :
    KarpReductionM CostedPolyTimeModel
      vertexCoverStructuredDecisionProblem feedbackNodeSetStructuredDecisionProblem :=
  vertexCoverToFeedbackNodeSetStructuredKarpReduction

noncomputable def vertexCoverToFeedbackNodeSetStructuredTMKarpReduction :
    TMKarpReduction
      vertexCoverStructuredDecisionProblem
      feedbackNodeSetStructuredDecisionProblem :=
  vertexCoverToFeedbackNodeSetStructuredTMBackedKarpReduction.toTMKarpReduction

end FeedbackNodeSet
end Karp21
end ComplexityReduction
