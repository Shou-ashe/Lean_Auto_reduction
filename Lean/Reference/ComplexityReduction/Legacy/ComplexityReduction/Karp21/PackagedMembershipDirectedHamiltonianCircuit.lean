/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipDirectedHamiltonianCircuitCycleTM
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.Projections
import Mathlib.Tactic

/-!
Direct standard-TM NP membership witness for faithful structured Directed
Hamiltonian Circuit.

The certificate is an ordered list of vertices.  The verifier checks that the
graph is directed, that the certificate has exactly the declared vertex count,
that every listed vertex is in bounds, that every graph vertex occurs in the
certificate, and that consecutive cyclic certificate entries are directed edges.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace DirectedHamiltonianCircuitMembership

abbrev directedHamiltonianCircuitCertificateEncodedType : EncodedType :=
  setStructuredEncodedType

abbrev DirectedHamiltonianCircuitCertificate := List Nat

theorem directedHamiltonianCircuitGraph_encode (I : DirectedHamiltonianCircuitInput) :
    graphStructuredEncodedType.encode I.graph =
      directedHamiltonianCircuitStructuredEncodedType.encode I := by
  rfl

noncomputable def directedHamiltonianCircuitGraphTMBackedMap :
    TMBackedCostedMap
      directedHamiltonianCircuitStructuredEncodedType
      graphStructuredEncodedType
      (fun I : DirectedHamiltonianCircuitInput => I.graph) :=
  TMBackedCostedMap.ofEncodingEquiv
    directedHamiltonianCircuitStructuredEncodedType
    graphStructuredEncodedType
    (fun I : DirectedHamiltonianCircuitInput => I.graph)
    (Equiv.refl directedHamiltonianCircuitStructuredEncodedType.Symbol)
    (by
      intro I
      change graphStructuredEncodedType.encode I.graph =
        (directedHamiltonianCircuitStructuredEncodedType.encode I).map id
      simp [directedHamiltonianCircuitGraph_encode])

def directedHamiltonianCircuitStructuredFiniteVerify
    (I : DirectedHamiltonianCircuitInput)
    (cycle : DirectedHamiltonianCircuitCertificate) : Bool :=
  graphBoolAndPair
    (I.graph.directed,
      graphBoolAndPair
        (decide (cycle.length = I.graph.vertices),
          graphBoolAndPair
            (HittingSet.boundedNatListBool (I.graph.vertices, cycle),
              graphBoolAndPair
                (allVerticesInCycleBool (I.graph.vertices, cycle),
                  cycleEdgesOKBool (I.graph.edges, cycle)))))

theorem directedHamiltonianCircuitStructuredFiniteVerify_eq_true_iff
    (I : DirectedHamiltonianCircuitInput) (cycle : List Nat) :
    directedHamiltonianCircuitStructuredFiniteVerify I cycle = true ↔
      I.graph.directed = true ∧
        cycle.length = I.graph.vertices ∧
          VerticesWithinBounds I.graph cycle ∧
            (∀ v, v < I.graph.vertices → v ∈ cycle) ∧
              cycleEdgesOKBool (I.graph.edges, cycle) = true := by
  rw [directedHamiltonianCircuitStructuredFiniteVerify,
    graphBoolAndPair_eq_true_iff, graphBoolAndPair_eq_true_iff,
    graphBoolAndPair_eq_true_iff, graphBoolAndPair_eq_true_iff,
    HittingSet.boundedNatListBool_eq_true_iff, allVerticesInCycleBool_eq_true_iff]
  simp [VerticesWithinBounds]

theorem nodup_of_verticesWithinBounds_all_length
    {g : GraphInput} {cycle : List Nat}
    (hLen : cycle.length = g.vertices)
    (hBounds : VerticesWithinBounds g cycle)
    (hAll : ∀ v, v < g.vertices → v ∈ cycle) :
    cycle.Nodup := by
  classical
  let s : Finset Nat := cycle.toFinset
  have hSet : s = Finset.range g.vertices := by
    ext v
    constructor
    · intro hv
      exact Finset.mem_range.mpr (hBounds v (by simpa [s] using hv))
    · intro hv
      exact (by simpa [s] using hAll v (Finset.mem_range.mp hv))
  have hCard : s.card = cycle.length := by
    calc
      s.card = (Finset.range g.vertices).card := by rw [hSet]
      _ = g.vertices := by simp
      _ = cycle.length := hLen.symm
  have hMulti :
      (cycle : Multiset Nat).Nodup :=
    (Multiset.toFinset_card_eq_card_iff_nodup
      (m := (cycle : Multiset Nat))).1 (by simpa [s] using hCard)
  simpa using hMulti

theorem directedHamiltonianCircuitVerifier_complete
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hDirected : I.graph.directed = true)
    (hCycle : OrderedDirectedHamiltonianCycle I.graph cycle) :
    directedHamiltonianCircuitStructuredFiniteVerify I cycle = true := by
  refine (directedHamiltonianCircuitStructuredFiniteVerify_eq_true_iff I cycle).2 ?_
  refine ⟨hDirected, hCycle.1, hCycle.2.2.1, ?_, ?_⟩
  · intro v hv
    exact OrderedDirectedHamiltonianCycle.mem_of_lt hCycle hv
  · exact cycleEdgesOKBool_eq_true_of_orderedSteps I.graph cycle hCycle.2.2.2

theorem directedHamiltonianCircuitVerifier_sound
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hVerify : directedHamiltonianCircuitStructuredFiniteVerify I cycle = true) :
    DirectedHamiltonianCircuit I := by
  rcases (directedHamiltonianCircuitStructuredFiniteVerify_eq_true_iff I cycle).1 hVerify with
    ⟨hDirected, hLen, hBounds, hAll, hEdges⟩
  have hNodup : cycle.Nodup :=
    nodup_of_verticesWithinBounds_all_length hLen hBounds hAll
  have hSteps : OrderedDirectedCycleSteps I.graph cycle :=
    orderedDirectedCycleSteps_of_cycleEdgesOKBool I.graph cycle hEdges
  exact ⟨hDirected, ⟨cycle, hLen, hNodup, hBounds, hSteps⟩⟩

theorem directedHamiltonianCircuitStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod directedHamiltonianCircuitStructuredEncodedType
        directedHamiltonianCircuitCertificateEncodedType)
      EncodedType.bool
      (fun p : DirectedHamiltonianCircuitInput × DirectedHamiltonianCircuitCertificate =>
        directedHamiltonianCircuitStructuredFiniteVerify p.1 p.2) := by
  let X :=
    EncodedType.prod directedHamiltonianCircuitStructuredEncodedType
      directedHamiltonianCircuitCertificateEncodedType
  have hI : TMPolyTimeMap X directedHamiltonianCircuitStructuredEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst directedHamiltonianCircuitStructuredEncodedType
        directedHamiltonianCircuitCertificateEncodedType
  have hCycle : TMPolyTimeMap X directedHamiltonianCircuitCertificateEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd directedHamiltonianCircuitStructuredEncodedType
        directedHamiltonianCircuitCertificateEncodedType
  have hGraph : TMPolyTimeMap X graphStructuredEncodedType
      (fun p : X.Carrier => p.1.graph) := by
    have hComp := TMPolyTimeMap.comp directedHamiltonianCircuitGraphTMBackedMap.tm_polytime hI
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
  have hCycleLength : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.2.length) := by
    have hComp := TMPolyTimeMap.comp
      (HittingSet.listLengthTMBackedMap EncodedType.nat).tm_polytime hCycle
    simpa [Function.comp, directedHamiltonianCircuitCertificateEncodedType, X] using hComp
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
      TMPolyTimeMap X allVerticesInputEncodedType
        (fun p : X.Carrier => (p.1.graph.vertices, p.2)) :=
    TMPolyTimeMap.prod_mk hVertices hCycle
  have hAllVertices : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => allVerticesInCycleBool (p.1.graph.vertices, p.2)) := by
    have hComp := TMPolyTimeMap.comp allVerticesInCycleBool_tm_polytime hAllInput
    simpa [Function.comp, allVerticesInputEncodedType, X] using hComp
  have hCycleEdgesInput :
      TMPolyTimeMap X cycleEdgesInputEncodedType
        (fun p : X.Carrier => (p.1.graph.edges, p.2)) :=
    TMPolyTimeMap.prod_mk hEdges hCycle
  have hCycleEdges : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => cycleEdgesOKBool (p.1.graph.edges, p.2)) := by
    have hComp := TMPolyTimeMap.comp cycleEdgesOKBool_tm_polytime hCycleEdgesInput
    simpa [Function.comp, cycleEdgesInputEncodedType, X] using hComp
  have hInnerInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (allVerticesInCycleBool (p.1.graph.vertices, p.2),
            cycleEdgesOKBool (p.1.graph.edges, p.2))) :=
    TMPolyTimeMap.prod_mk hAllVertices hCycleEdges
  have hInner : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair
          (allVerticesInCycleBool (p.1.graph.vertices, p.2),
            cycleEdgesOKBool (p.1.graph.edges, p.2))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hInnerInput
    simpa [Function.comp, X] using hComp
  have hMiddleInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (HittingSet.boundedNatListBool (p.1.graph.vertices, p.2),
            graphBoolAndPair
              (allVerticesInCycleBool (p.1.graph.vertices, p.2),
                cycleEdgesOKBool (p.1.graph.edges, p.2)))) :=
    TMPolyTimeMap.prod_mk hBound hInner
  have hMiddle : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair
          (HittingSet.boundedNatListBool (p.1.graph.vertices, p.2),
            graphBoolAndPair
              (allVerticesInCycleBool (p.1.graph.vertices, p.2),
                cycleEdgesOKBool (p.1.graph.edges, p.2)))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hMiddleInput
    simpa [Function.comp, X] using hComp
  have hTailInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (decide (p.2.length = p.1.graph.vertices),
            graphBoolAndPair
              (HittingSet.boundedNatListBool (p.1.graph.vertices, p.2),
                graphBoolAndPair
                  (allVerticesInCycleBool (p.1.graph.vertices, p.2),
                    cycleEdgesOKBool (p.1.graph.edges, p.2))))) :=
    TMPolyTimeMap.prod_mk hLengthEq hMiddle
  have hTail : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair
          (decide (p.2.length = p.1.graph.vertices),
            graphBoolAndPair
              (HittingSet.boundedNatListBool (p.1.graph.vertices, p.2),
                graphBoolAndPair
                  (allVerticesInCycleBool (p.1.graph.vertices, p.2),
                    cycleEdgesOKBool (p.1.graph.edges, p.2))))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hTailInput
    simpa [Function.comp, X] using hComp
  have hAllInput' :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (p.1.graph.directed,
            graphBoolAndPair
              (decide (p.2.length = p.1.graph.vertices),
                graphBoolAndPair
                  (HittingSet.boundedNatListBool (p.1.graph.vertices, p.2),
                    graphBoolAndPair
                      (allVerticesInCycleBool (p.1.graph.vertices, p.2),
                        cycleEdgesOKBool (p.1.graph.edges, p.2)))))) :=
    TMPolyTimeMap.prod_mk hDirected hTail
  have hOut := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAllInput'
  simpa [Function.comp, directedHamiltonianCircuitStructuredFiniteVerify, X] using hOut

theorem directedHamiltonianCircuitCertificate_inputSize_le_square
    (I : DirectedHamiltonianCircuitInput) (cycle : List Nat)
    (hLen : cycle.length = I.graph.vertices)
    (hBounds : VerticesWithinBounds I.graph cycle) :
    setStructuredEncodedType.inputSize cycle ≤
      (directedHamiltonianCircuitStructuredEncodedType.inputSize I) ^ 2 := by
  let S := directedHamiltonianCircuitStructuredEncodedType.inputSize I
  have hCert := HittingSet.boundedNatList_inputSize_le I.graph.vertices cycle hBounds
  have hVerticesSucc : I.graph.vertices + 1 ≤ S := by
    dsimp [S]
    rw [DirectedHamiltonianCircuit.directedHamiltonianCircuitStructured_inputSize_eq,
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

end DirectedHamiltonianCircuitMembership

/-- Direct finite-certificate TM verifier for faithful structured Directed Hamiltonian Circuit. -/
noncomputable def directedHamiltonianCircuitStructuredFiniteTMVerifier :
    TMVerifier directedHamiltonianCircuitStructuredDecisionProblem where
  Cert := DirectedHamiltonianCircuitMembership.directedHamiltonianCircuitCertificateEncodedType
  verify := DirectedHamiltonianCircuitMembership.directedHamiltonianCircuitStructuredFiniteVerify
  verifier_polytime :=
    DirectedHamiltonianCircuitMembership.directedHamiltonianCircuitStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨2, 1, 0, ?_⟩
    intro I hYes
    rcases hYes with ⟨hDirected, cycle, hCycle⟩
    refine ⟨cycle, ?_, ?_⟩
    · simpa using
        DirectedHamiltonianCircuitMembership.directedHamiltonianCircuitCertificate_inputSize_le_square
          I cycle hCycle.1 hCycle.2.2.1
    · exact DirectedHamiltonianCircuitMembership.directedHamiltonianCircuitVerifier_complete
        hDirected hCycle
  sound := by
    intro I cycle hVerify
    exact DirectedHamiltonianCircuitMembership.directedHamiltonianCircuitVerifier_sound hVerify

theorem directedHamiltonianCircuitStructured_TMInNP :
    TMInNP directedHamiltonianCircuitStructuredDecisionProblem :=
  TMInNP.intro directedHamiltonianCircuitStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
