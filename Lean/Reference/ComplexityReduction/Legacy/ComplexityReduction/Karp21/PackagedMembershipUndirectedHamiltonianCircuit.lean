/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.UndirectedHamiltonianCircuit
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipDirectedHamiltonianCircuit
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.Projections
import Mathlib.Tactic

/-!
Direct standard-TM NP membership witness for faithful structured Undirected
Hamiltonian Circuit.

The certificate is an ordered list of vertices.  The verifier checks that the
graph is undirected, that the certificate has exactly the declared vertex count,
that every listed vertex is in bounds, that every graph vertex occurs in the
certificate, and that consecutive cyclic certificate entries are undirected
edges.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace UndirectedHamiltonianCircuitMembership

abbrev undirectedHamiltonianCircuitCertificateEncodedType : EncodedType :=
  setStructuredEncodedType

abbrev UndirectedHamiltonianCircuitCertificate := List Nat

theorem undirectedHamiltonianCircuitGraph_encode (I : UndirectedHamiltonianCircuitInput) :
    graphStructuredEncodedType.encode I.graph =
      undirectedHamiltonianCircuitStructuredEncodedType.encode I := by
  rfl

noncomputable def undirectedHamiltonianCircuitGraphTMBackedMap :
    TMBackedCostedMap
      undirectedHamiltonianCircuitStructuredEncodedType
      graphStructuredEncodedType
      (fun I : UndirectedHamiltonianCircuitInput => I.graph) :=
  TMBackedCostedMap.ofEncodingEquiv
    undirectedHamiltonianCircuitStructuredEncodedType
    graphStructuredEncodedType
    (fun I : UndirectedHamiltonianCircuitInput => I.graph)
    (Equiv.refl undirectedHamiltonianCircuitStructuredEncodedType.Symbol)
    (by
      intro I
      change graphStructuredEncodedType.encode I.graph =
        (undirectedHamiltonianCircuitStructuredEncodedType.encode I).map id
      simp [undirectedHamiltonianCircuitGraph_encode])

def undirectedEdgeExpansion (edges : List (Nat × Nat)) : List (Nat × Nat) :=
  edges ++ edges.map vertexPairSwap

theorem mem_undirectedEdgeExpansion_iff
    (edges : List (Nat × Nat)) (u v : Nat) :
    (u, v) ∈ undirectedEdgeExpansion edges ↔
      (u, v) ∈ edges ∨ (v, u) ∈ edges := by
  simp [undirectedEdgeExpansion, vertexPairSwap]

theorem sourceHasDirectedEdgeBool_undirectedExpansion_eq_true_iff
    (g : GraphInput) (u v : Nat) :
    DirectedHamiltonianCircuitMembership.sourceHasDirectedEdgeBool
        ((u, v), undirectedEdgeExpansion g.edges) = true ↔
      HasUndirectedEdge g u v := by
  rw [DirectedHamiltonianCircuitMembership.sourceHasDirectedEdgeBool_eq_true_iff]
  simpa [HasUndirectedEdge] using mem_undirectedEdgeExpansion_iff g.edges u v

theorem undirectedEdgeExpansion_tm_polytime :
    TMPolyTimeMap edgeListStructuredEncodedType edgeListStructuredEncodedType
      undirectedEdgeExpansion := by
  have hId : TMPolyTimeMap edgeListStructuredEncodedType edgeListStructuredEncodedType id :=
    TMPolyTimeMap.id edgeListStructuredEncodedType
  have hSwapList : TMPolyTimeMap edgeListStructuredEncodedType edgeListStructuredEncodedType
      (fun edges : List (Nat × Nat) => edges.map vertexPairSwap) := by
    have hMap := TMPolyTimeMap.list_map vertexPairSwap_tm_polytime
    simpa [edgeListStructuredEncodedType, vertexPairListEncodedType] using hMap
  have hInput :
      TMPolyTimeMap edgeListStructuredEncodedType
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun edges : List (Nat × Nat) => (edges, edges.map vertexPairSwap)) :=
    TMPolyTimeMap.prod_mk hId hSwapList
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append edgeStructuredEncodedType) hInput
  simpa [Function.comp, undirectedEdgeExpansion, edgeListStructuredEncodedType] using hAppend

def undirectedCycleEdgesOKBool (p : List (Nat × Nat) × List Nat) : Bool :=
  DirectedHamiltonianCircuitMembership.cycleEdgesOKBool
    (undirectedEdgeExpansion p.1, p.2)

theorem undirectedCycleEdgesOKBool_eq_true_iff
    (g : GraphInput) (cycle : List Nat) :
    undirectedCycleEdgesOKBool (g.edges, cycle) = true ↔
      cycle.IsChain (fun u v => HasUndirectedEdge g u v) ∧
        ∀ x ∈ cycle.getLast?, ∀ y ∈ cycle.head?, HasUndirectedEdge g x y := by
  rw [undirectedCycleEdgesOKBool,
    DirectedHamiltonianCircuitMembership.cycleEdgesOKBool_eq_true_iff]
  constructor
  · rintro ⟨hChainBool, hCloseBool⟩
    constructor
    · refine hChainBool.imp ?_
      intro u v hEdge
      exact (sourceHasDirectedEdgeBool_undirectedExpansion_eq_true_iff g u v).1 hEdge
    · intro x hx y hy
      exact (sourceHasDirectedEdgeBool_undirectedExpansion_eq_true_iff g x y).1
        (hCloseBool x hx y hy)
  · rintro ⟨hChain, hClose⟩
    constructor
    · refine hChain.imp ?_
      intro u v hEdge
      exact (sourceHasDirectedEdgeBool_undirectedExpansion_eq_true_iff g u v).2 hEdge
    · intro x hx y hy
      exact (sourceHasDirectedEdgeBool_undirectedExpansion_eq_true_iff g x y).2
        (hClose x hx y hy)

theorem orderedUndirectedCycleSteps_to_chain
    {g : GraphInput} {cycle : List Nat}
    (hSteps : OrderedUndirectedCycleSteps g cycle) :
    cycle.IsChain (fun u v => HasUndirectedEdge g u v) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hiLt : i < cycle.length := Nat.lt_trans (Nat.lt_succ_self i) hi
  have hStep := hSteps ⟨i, hiLt⟩
  have hSucc :
      cyclicSuccIndex (cycle := cycle) ⟨i, hiLt⟩ = ⟨i + 1, hi⟩ := by
    ext
    simp [cyclicSuccIndex, Nat.mod_eq_of_lt hi]
  simpa [hSucc] using hStep

theorem orderedUndirectedCycleSteps_to_closing
    {g : GraphInput} {cycle : List Nat}
    (hSteps : OrderedUndirectedCycleSteps g cycle) :
    ∀ x ∈ cycle.getLast?, ∀ y ∈ cycle.head?, HasUndirectedEdge g x y := by
  intro x hx y hy
  cases hCycle : cycle with
  | nil =>
      simp [hCycle] at hx
  | cons first rest =>
      subst cycle
      simp at hy
      subst y
      have hLenPos : 0 < (first :: rest).length := by simp
      have hLastLt : (first :: rest).length - 1 < (first :: rest).length := by
        omega
      have hxLast :
          x = (first :: rest).get ⟨(first :: rest).length - 1, hLastLt⟩ := by
        rcases List.mem_getLast?_eq_getLast hx with ⟨_hne, rfl⟩
        simpa using (List.get_length_sub_one hLastLt).symm
      subst x
      have hSucc :
          cyclicSuccIndex (cycle := first :: rest) ⟨(first :: rest).length - 1, hLastLt⟩ =
            ⟨0, hLenPos⟩ := by
        ext
        simp [cyclicSuccIndex, Nat.mod_self]
      have hStep := hSteps ⟨(first :: rest).length - 1, hLastLt⟩
      rw [hSucc] at hStep
      simpa using hStep

theorem undirectedCycleEdgesOKBool_eq_true_of_orderedSteps
    (g : GraphInput) (cycle : List Nat)
    (hSteps : OrderedUndirectedCycleSteps g cycle) :
    undirectedCycleEdgesOKBool (g.edges, cycle) = true := by
  rw [undirectedCycleEdgesOKBool_eq_true_iff]
  exact ⟨orderedUndirectedCycleSteps_to_chain hSteps,
    orderedUndirectedCycleSteps_to_closing hSteps⟩

theorem orderedUndirectedCycleSteps_of_undirectedCycleEdgesOKBool
    (g : GraphInput) (cycle : List Nat)
    (hOK : undirectedCycleEdgesOKBool (g.edges, cycle) = true) :
    OrderedUndirectedCycleSteps g cycle := by
  rcases (undirectedCycleEdgesOKBool_eq_true_iff g cycle).1 hOK with ⟨hChain, hClose⟩
  exact UndirectedHamiltonianCircuit.orderedUndirectedCycleSteps_of_isChain_closing
    hChain hClose

theorem undirectedCycleEdgesOKBool_tm_polytime :
    TMPolyTimeMap
      DirectedHamiltonianCircuitMembership.cycleEdgesInputEncodedType
      EncodedType.bool
      undirectedCycleEdgesOKBool := by
  let X := DirectedHamiltonianCircuitMembership.cycleEdgesInputEncodedType
  have hEdges : TMPolyTimeMap X edgeListStructuredEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X, DirectedHamiltonianCircuitMembership.cycleEdgesInputEncodedType] using
      TMPolyTimeMap.fst edgeListStructuredEncodedType setStructuredEncodedType
  have hCycle : TMPolyTimeMap X setStructuredEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X, DirectedHamiltonianCircuitMembership.cycleEdgesInputEncodedType] using
      TMPolyTimeMap.snd edgeListStructuredEncodedType setStructuredEncodedType
  have hExpanded : TMPolyTimeMap X edgeListStructuredEncodedType
      (fun p : X.Carrier => undirectedEdgeExpansion p.1) := by
    have hComp := TMPolyTimeMap.comp undirectedEdgeExpansion_tm_polytime hEdges
    simpa [Function.comp, X] using hComp
  have hInput :
      TMPolyTimeMap X DirectedHamiltonianCircuitMembership.cycleEdgesInputEncodedType
        (fun p : X.Carrier => (undirectedEdgeExpansion p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hExpanded hCycle
  have hComp := TMPolyTimeMap.comp
    DirectedHamiltonianCircuitMembership.cycleEdgesOKBool_tm_polytime hInput
  simpa [Function.comp, undirectedCycleEdgesOKBool, X] using hComp

def undirectedHamiltonianCircuitStructuredFiniteVerify
    (I : UndirectedHamiltonianCircuitInput)
    (cycle : UndirectedHamiltonianCircuitCertificate) : Bool :=
  graphBoolAndPair
    (Bool.not I.graph.directed,
      graphBoolAndPair
        (decide (cycle.length = I.graph.vertices),
          graphBoolAndPair
            (HittingSet.boundedNatListBool (I.graph.vertices, cycle),
              graphBoolAndPair
                (DirectedHamiltonianCircuitMembership.allVerticesInCycleBool
                  (I.graph.vertices, cycle),
                  undirectedCycleEdgesOKBool (I.graph.edges, cycle)))))

theorem undirectedHamiltonianCircuitStructuredFiniteVerify_eq_true_iff
    (I : UndirectedHamiltonianCircuitInput) (cycle : List Nat) :
    undirectedHamiltonianCircuitStructuredFiniteVerify I cycle = true ↔
      I.graph.directed = false ∧
        cycle.length = I.graph.vertices ∧
          VerticesWithinBounds I.graph cycle ∧
            (∀ v, v < I.graph.vertices → v ∈ cycle) ∧
              undirectedCycleEdgesOKBool (I.graph.edges, cycle) = true := by
  rw [undirectedHamiltonianCircuitStructuredFiniteVerify,
    graphBoolAndPair_eq_true_iff, graphBoolAndPair_eq_true_iff,
    graphBoolAndPair_eq_true_iff, graphBoolAndPair_eq_true_iff,
    HittingSet.boundedNatListBool_eq_true_iff,
    DirectedHamiltonianCircuitMembership.allVerticesInCycleBool_eq_true_iff]
  simp [VerticesWithinBounds]

theorem undirectedHamiltonianCircuitVerifier_complete
    {I : UndirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hUndirected : I.graph.directed = false)
    (hCycle : OrderedUndirectedHamiltonianCycle I.graph cycle) :
    undirectedHamiltonianCircuitStructuredFiniteVerify I cycle = true := by
  refine (undirectedHamiltonianCircuitStructuredFiniteVerify_eq_true_iff I cycle).2 ?_
  refine ⟨hUndirected, hCycle.1, hCycle.2.2.1, ?_, ?_⟩
  · intro v hv
    exact mem_of_verticesWithinBounds_length_nodup hCycle.1 hCycle.2.1 hCycle.2.2.1 hv
  · exact undirectedCycleEdgesOKBool_eq_true_of_orderedSteps I.graph cycle hCycle.2.2.2

theorem undirectedHamiltonianCircuitVerifier_sound
    {I : UndirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hVerify : undirectedHamiltonianCircuitStructuredFiniteVerify I cycle = true) :
    UndirectedHamiltonianCircuit I := by
  rcases (undirectedHamiltonianCircuitStructuredFiniteVerify_eq_true_iff I cycle).1 hVerify with
    ⟨hUndirected, hLen, hBounds, hAll, hEdges⟩
  have hNodup : cycle.Nodup :=
    DirectedHamiltonianCircuitMembership.nodup_of_verticesWithinBounds_all_length
      hLen hBounds hAll
  have hSteps : OrderedUndirectedCycleSteps I.graph cycle :=
    orderedUndirectedCycleSteps_of_undirectedCycleEdgesOKBool I.graph cycle hEdges
  exact ⟨hUndirected, ⟨cycle, hLen, hNodup, hBounds, hSteps⟩⟩

theorem undirectedHamiltonianCircuitStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod undirectedHamiltonianCircuitStructuredEncodedType
        undirectedHamiltonianCircuitCertificateEncodedType)
      EncodedType.bool
      (fun p : UndirectedHamiltonianCircuitInput × UndirectedHamiltonianCircuitCertificate =>
        undirectedHamiltonianCircuitStructuredFiniteVerify p.1 p.2) := by
  let X :=
    EncodedType.prod undirectedHamiltonianCircuitStructuredEncodedType
      undirectedHamiltonianCircuitCertificateEncodedType
  have hI : TMPolyTimeMap X undirectedHamiltonianCircuitStructuredEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst undirectedHamiltonianCircuitStructuredEncodedType
        undirectedHamiltonianCircuitCertificateEncodedType
  have hCycle : TMPolyTimeMap X undirectedHamiltonianCircuitCertificateEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd undirectedHamiltonianCircuitStructuredEncodedType
        undirectedHamiltonianCircuitCertificateEncodedType
  have hGraph : TMPolyTimeMap X graphStructuredEncodedType
      (fun p : X.Carrier => p.1.graph) := by
    have hComp := TMPolyTimeMap.comp undirectedHamiltonianCircuitGraphTMBackedMap.tm_polytime hI
    simpa [Function.comp, X] using hComp
  have hVertices : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.1.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp graphVerticesTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hPayload : TMPolyTimeMap X graphPayloadStructuredEncodedType
      (fun p : X.Carrier => (p.1.graph.edges, p.1.graph.directed)) := by
    have hComp := TMPolyTimeMap.comp graphPayloadTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, graphPayloadOfGraph, X] using hComp
  have hEdges : TMPolyTimeMap X edgeListStructuredEncodedType
      (fun p : X.Carrier => p.1.graph.edges) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, graphPayloadStructuredEncodedType, X] using hComp
  have hDirected : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => p.1.graph.directed) := by
    have hSnd := TMPolyTimeMap.snd edgeListStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, graphPayloadStructuredEncodedType, X] using hComp
  have hUndirected : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => Bool.not p.1.graph.directed) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.bool_not hDirected
    simpa [Function.comp, X] using hComp
  have hCycleLength : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.2.length) := by
    have hComp := TMPolyTimeMap.comp
      (HittingSet.listLengthTMBackedMap EncodedType.nat).tm_polytime hCycle
    simpa [Function.comp, undirectedHamiltonianCircuitCertificateEncodedType, X] using hComp
  have hLengthEqInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.length, p.1.graph.vertices)) :=
    TMPolyTimeMap.prod_mk hCycleLength hVertices
  have hLengthEq : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => decide (p.2.length = p.1.graph.vertices)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hLengthEqInput
    simpa [Function.comp, X] using hComp
  have hBoundInput :
      TMPolyTimeMap X HittingSet.boundedNatInstructionInputEncodedType
        (fun p : X.Carrier => (p.1.graph.vertices, p.2)) :=
    TMPolyTimeMap.prod_mk hVertices hCycle
  have hBound : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => HittingSet.boundedNatListBool (p.1.graph.vertices, p.2)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.boundedNatListBool_tm_polytime hBoundInput
    simpa [Function.comp, HittingSet.boundedNatInstructionInputEncodedType, X] using hComp
  have hAllInput :
      TMPolyTimeMap X DirectedHamiltonianCircuitMembership.allVerticesInputEncodedType
        (fun p : X.Carrier => (p.1.graph.vertices, p.2)) :=
    TMPolyTimeMap.prod_mk hVertices hCycle
  have hAllVertices : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        DirectedHamiltonianCircuitMembership.allVerticesInCycleBool
          (p.1.graph.vertices, p.2)) := by
    have hComp := TMPolyTimeMap.comp
      DirectedHamiltonianCircuitMembership.allVerticesInCycleBool_tm_polytime hAllInput
    simpa [Function.comp, DirectedHamiltonianCircuitMembership.allVerticesInputEncodedType, X]
      using hComp
  have hCycleEdgesInput :
      TMPolyTimeMap X DirectedHamiltonianCircuitMembership.cycleEdgesInputEncodedType
        (fun p : X.Carrier => (p.1.graph.edges, p.2)) :=
    TMPolyTimeMap.prod_mk hEdges hCycle
  have hCycleEdges : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => undirectedCycleEdgesOKBool (p.1.graph.edges, p.2)) := by
    have hComp := TMPolyTimeMap.comp undirectedCycleEdgesOKBool_tm_polytime hCycleEdgesInput
    simpa [Function.comp, DirectedHamiltonianCircuitMembership.cycleEdgesInputEncodedType, X]
      using hComp
  have hInnerInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (DirectedHamiltonianCircuitMembership.allVerticesInCycleBool
              (p.1.graph.vertices, p.2),
            undirectedCycleEdgesOKBool (p.1.graph.edges, p.2))) :=
    TMPolyTimeMap.prod_mk hAllVertices hCycleEdges
  have hInner : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair
          (DirectedHamiltonianCircuitMembership.allVerticesInCycleBool
              (p.1.graph.vertices, p.2),
            undirectedCycleEdgesOKBool (p.1.graph.edges, p.2))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hInnerInput
    simpa [Function.comp, X] using hComp
  have hMiddleInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (HittingSet.boundedNatListBool (p.1.graph.vertices, p.2),
            graphBoolAndPair
              (DirectedHamiltonianCircuitMembership.allVerticesInCycleBool
                  (p.1.graph.vertices, p.2),
                undirectedCycleEdgesOKBool (p.1.graph.edges, p.2)))) :=
    TMPolyTimeMap.prod_mk hBound hInner
  have hMiddle : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair
          (HittingSet.boundedNatListBool (p.1.graph.vertices, p.2),
            graphBoolAndPair
              (DirectedHamiltonianCircuitMembership.allVerticesInCycleBool
                  (p.1.graph.vertices, p.2),
                undirectedCycleEdgesOKBool (p.1.graph.edges, p.2)))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hMiddleInput
    simpa [Function.comp, X] using hComp
  have hTailInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (decide (p.2.length = p.1.graph.vertices),
            graphBoolAndPair
              (HittingSet.boundedNatListBool (p.1.graph.vertices, p.2),
                graphBoolAndPair
                  (DirectedHamiltonianCircuitMembership.allVerticesInCycleBool
                      (p.1.graph.vertices, p.2),
                    undirectedCycleEdgesOKBool (p.1.graph.edges, p.2))))) :=
    TMPolyTimeMap.prod_mk hLengthEq hMiddle
  have hTail : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair
          (decide (p.2.length = p.1.graph.vertices),
            graphBoolAndPair
              (HittingSet.boundedNatListBool (p.1.graph.vertices, p.2),
                graphBoolAndPair
                  (DirectedHamiltonianCircuitMembership.allVerticesInCycleBool
                      (p.1.graph.vertices, p.2),
                    undirectedCycleEdgesOKBool (p.1.graph.edges, p.2))))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hTailInput
    simpa [Function.comp, X] using hComp
  have hAllInput' :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (Bool.not p.1.graph.directed,
            graphBoolAndPair
              (decide (p.2.length = p.1.graph.vertices),
                graphBoolAndPair
                  (HittingSet.boundedNatListBool (p.1.graph.vertices, p.2),
                    graphBoolAndPair
                      (DirectedHamiltonianCircuitMembership.allVerticesInCycleBool
                          (p.1.graph.vertices, p.2),
                        undirectedCycleEdgesOKBool (p.1.graph.edges, p.2)))))) :=
    TMPolyTimeMap.prod_mk hUndirected hTail
  have hOut := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAllInput'
  simpa [Function.comp, undirectedHamiltonianCircuitStructuredFiniteVerify, X] using hOut

theorem undirectedHamiltonianCircuitCertificate_inputSize_le_square
    (I : UndirectedHamiltonianCircuitInput) (cycle : List Nat)
    (hLen : cycle.length = I.graph.vertices)
    (hBounds : VerticesWithinBounds I.graph cycle) :
    setStructuredEncodedType.inputSize cycle ≤
      (undirectedHamiltonianCircuitStructuredEncodedType.inputSize I) ^ 2 := by
  let S := undirectedHamiltonianCircuitStructuredEncodedType.inputSize I
  have hCert := HittingSet.boundedNatList_inputSize_le I.graph.vertices cycle hBounds
  have hVerticesSucc : I.graph.vertices + 1 ≤ S := by
    dsimp [S]
    rw [UndirectedHamiltonianCircuit.undirectedHamiltonianCircuitStructured_inputSize_eq,
      VertexCover.graphStructured_inputSize_eq]
    omega
  have hVertices : I.graph.vertices ≤ S := by omega
  calc
    setStructuredEncodedType.inputSize cycle
        ≤ cycle.length * (I.graph.vertices + 1) := hCert
    _ ≤ I.graph.vertices * (I.graph.vertices + 1) :=
        Nat.mul_le_mul_right (I.graph.vertices + 1) (by omega)
    _ ≤ S * S := Nat.mul_le_mul hVertices hVerticesSucc
    _ = S ^ 2 := by ring

end UndirectedHamiltonianCircuitMembership

/-- Direct finite-certificate TM verifier for faithful structured Undirected Hamiltonian Circuit. -/
noncomputable def undirectedHamiltonianCircuitStructuredFiniteTMVerifier :
    TMVerifier undirectedHamiltonianCircuitStructuredDecisionProblem where
  Cert := UndirectedHamiltonianCircuitMembership.undirectedHamiltonianCircuitCertificateEncodedType
  verify :=
    UndirectedHamiltonianCircuitMembership.undirectedHamiltonianCircuitStructuredFiniteVerify
  verifier_polytime :=
    UndirectedHamiltonianCircuitMembership.undirectedHamiltonianCircuitStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨2, 1, 0, ?_⟩
    intro I hYes
    rcases hYes with ⟨hUndirected, cycle, hCycle⟩
    refine ⟨cycle, ?_, ?_⟩
    · simpa using
        UndirectedHamiltonianCircuitMembership.undirectedHamiltonianCircuitCertificate_inputSize_le_square
          I cycle hCycle.1 hCycle.2.2.1
    · exact UndirectedHamiltonianCircuitMembership.undirectedHamiltonianCircuitVerifier_complete
        hUndirected hCycle
  sound := by
    intro I cycle hVerify
    exact UndirectedHamiltonianCircuitMembership.undirectedHamiltonianCircuitVerifier_sound hVerify

theorem undirectedHamiltonianCircuitStructured_TMInNP :
    TMInNP undirectedHamiltonianCircuitStructuredDecisionProblem :=
  TMInNP.intro undirectedHamiltonianCircuitStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
