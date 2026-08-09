/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipFeedbackArcSetRemovedRunner
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipFeedbackNodeSet
import Mathlib.Data.List.MinMax
import Mathlib.Tactic

/-!
Direct standard-TM NP membership witness for faithful structured Feedback Arc Set.

The certificate is a removed-arc list together with a rank table.  The verifier checks
the budget, checks that every removed arc is an input graph arc, and checks that every
input arc not removed and with bounded endpoints strictly increases rank.  Any directed
cycle in the graph after deleting the certified arcs then contradicts the maximum-rank
vertex on the cycle.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace FeedbackArcSetMembership

/-! ### Finite verifier and direct runner witness -/

def feedbackArcSetStructuredFiniteVerify
    (I : FeedbackArcSetInput) (cert : FeedbackArcSetCertificate) : Bool :=
  graphBoolAndPair
    (HittingSet.natLeBool (cert.1.length, I.k),
      graphBoolAndPair
        (fasAllRemovedInGraphBool (I.graph.edges, cert.1),
          fasAllEdgesRankOKBool ((I.graph.vertices, cert), I.graph.edges)))

theorem feedbackArcSetStructuredFiniteVerify_eq_true_iff
    (I : FeedbackArcSetInput) (cert : FeedbackArcSetCertificate) :
    feedbackArcSetStructuredFiniteVerify I cert = true ↔
      cert.1.length ≤ I.k ∧
        (∀ e ∈ cert.1, e ∈ I.graph.edges) ∧
        ∀ e ∈ I.graph.edges,
          fasEdgeRankOKBool ((I.graph.vertices, cert), e) = true := by
  rw [feedbackArcSetStructuredFiniteVerify, graphBoolAndPair_eq_true_iff,
    graphBoolAndPair_eq_true_iff, HittingSet.natLeBool_eq_true_iff,
    fasAllRemovedInGraphBool_eq_true_iff, fasAllEdgesRankOKBool_eq_true_iff]

theorem feedbackArcSetStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod feedbackArcSetStructuredEncodedType feedbackArcSetCertificateEncodedType)
      EncodedType.bool
      (fun p : FeedbackArcSetInput × FeedbackArcSetCertificate =>
        feedbackArcSetStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod feedbackArcSetStructuredEncodedType feedbackArcSetCertificateEncodedType
  have hInstance :
      TMPolyTimeMap X feedbackArcSetStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst feedbackArcSetStructuredEncodedType feedbackArcSetCertificateEncodedType
  have hCert :
      TMPolyTimeMap X feedbackArcSetCertificateEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd feedbackArcSetStructuredEncodedType feedbackArcSetCertificateEncodedType
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType (fun p : X.Carrier => p.1.graph) := by
    have hComp := TMPolyTimeMap.comp feedbackArcSetGraphTMBackedMap.tm_polytime hInstance
    simpa [Function.comp, X] using hComp
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.k) := by
    have hComp := TMPolyTimeMap.comp feedbackArcSetBudgetTMBackedMap.tm_polytime hInstance
    simpa [Function.comp, X] using hComp
  have hVertices :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp graphVerticesTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hGraphPayload :
      TMPolyTimeMap X graphPayloadStructuredEncodedType
        (fun p : X.Carrier => graphPayloadOfGraph p.1.graph) := by
    have hComp := TMPolyTimeMap.comp graphPayloadTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.1.graph.edges) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hGraphPayload
    simpa [Function.comp, graphPayloadOfGraph, graphPayloadStructuredEncodedType, X] using hComp
  have hRemoved :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType partitionWeightsStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hCert
    simpa [Function.comp, feedbackArcSetCertificateEncodedType, X] using hComp
  have hRemovedLength : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1.length) := by
    have hComp :=
      TMPolyTimeMap.comp (HittingSet.listLengthTMBackedMap edgeStructuredEncodedType).tm_polytime
        hRemoved
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hLengthInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.1.length, p.1.k)) :=
    TMPolyTimeMap.prod_mk hRemovedLength hBudget
  have hLengthOK :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => HittingSet.natLeBool (p.2.1.length, p.1.k)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.natLeBool_tm_polytime hLengthInput
    simpa [Function.comp] using hComp
  have hRemovedGraphInput :
      TMPolyTimeMap X fasRemovedInstructionInputEncodedType
        (fun p : X.Carrier => (p.1.graph.edges, p.2.1)) :=
    TMPolyTimeMap.prod_mk hEdges hRemoved
  have hRemovedOK :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => fasAllRemovedInGraphBool (p.1.graph.edges, p.2.1)) := by
    have hComp := TMPolyTimeMap.comp fasAllRemovedInGraphBool_tm_polytime hRemovedGraphInput
    simpa [Function.comp, fasRemovedInstructionInputEncodedType] using hComp
  have hContext :
      TMPolyTimeMap X fasRankContextEncodedType
        (fun p : X.Carrier => (p.1.graph.vertices, p.2)) :=
    TMPolyTimeMap.prod_mk hVertices hCert
  have hEdgesInput :
      TMPolyTimeMap X fasEdgeInstructionInputEncodedType
        (fun p : X.Carrier => ((p.1.graph.vertices, p.2), p.1.graph.edges)) :=
    TMPolyTimeMap.prod_mk hContext hEdges
  have hEdgesOK :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier =>
          fasAllEdgesRankOKBool ((p.1.graph.vertices, p.2), p.1.graph.edges)) := by
    have hComp := TMPolyTimeMap.comp fasAllEdgesRankOKBool_tm_polytime hEdgesInput
    simpa [Function.comp, fasEdgeInstructionInputEncodedType] using hComp
  have hTailInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (fasAllRemovedInGraphBool (p.1.graph.edges, p.2.1),
            fasAllEdgesRankOKBool ((p.1.graph.vertices, p.2), p.1.graph.edges))) :=
    TMPolyTimeMap.prod_mk hRemovedOK hEdgesOK
  have hTail :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier =>
          graphBoolAndPair
            (fasAllRemovedInGraphBool (p.1.graph.edges, p.2.1),
              fasAllEdgesRankOKBool ((p.1.graph.vertices, p.2), p.1.graph.edges))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hTailInput
    simpa [Function.comp] using hComp
  have hAllInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (HittingSet.natLeBool (p.2.1.length, p.1.k),
            graphBoolAndPair
              (fasAllRemovedInGraphBool (p.1.graph.edges, p.2.1),
                fasAllEdgesRankOKBool ((p.1.graph.vertices, p.2), p.1.graph.edges)))) :=
    TMPolyTimeMap.prod_mk hLengthOK hTail
  have hAll := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAllInput
  simpa [Function.comp, feedbackArcSetStructuredFiniteVerify, X] using hAll

/-! ### Certificate size bounds -/

theorem feedbackArcSetStructured_inputSize_ge_vertices
    (I : FeedbackArcSetInput) :
    I.graph.vertices ≤ feedbackArcSetStructuredEncodedType.inputSize I := by
  rw [FeedbackArcSet.feedbackArcSetStructured_inputSize_eq,
    VertexCover.graphStructured_inputSize_eq]
  omega

theorem feedbackArcSetStructured_inputSize_ge_budget
    (I : FeedbackArcSetInput) :
    I.k ≤ feedbackArcSetStructuredEncodedType.inputSize I := by
  rw [FeedbackArcSet.feedbackArcSetStructured_inputSize_eq]
  omega

theorem feedbackArcSetStructured_inputSize_ge_edges_inputSize
    (I : FeedbackArcSetInput) :
    edgeListStructuredEncodedType.inputSize I.graph.edges ≤
      feedbackArcSetStructuredEncodedType.inputSize I := by
  rw [FeedbackArcSet.feedbackArcSetStructured_inputSize_eq,
    VertexCover.graphStructured_inputSize_eq]
  omega

theorem encodedList_element_inputSize_le_local {X : EncodedType} {x : X.Carrier}
    {xs : List X.Carrier} (hx : x ∈ xs) :
    X.inputSize x ≤ (EncodedType.list X).inputSize xs := by
  induction xs with
  | nil =>
      simp at hx
  | cons y ys ih =>
      rw [EncodedType.inputSize_list_cons]
      rcases List.mem_cons.mp hx with hxy | hxys
      · subst x
        omega
      · have hTail := ih hxys
        omega

theorem feedbackArcSetCertificate_inputSize_le_poly
    (I : FeedbackArcSetInput) (cert : FeedbackArcSetCertificate)
    (hLen : cert.1.length ≤ I.k)
    (hRemovedEdges : ∀ e ∈ cert.1, e ∈ I.graph.edges)
    (hRankLen : cert.2.length = I.graph.vertices)
    (hRankBounds : ∀ r ∈ cert.2, r < I.graph.vertices + 1) :
    feedbackArcSetCertificateEncodedType.inputSize cert ≤
      20 * (feedbackArcSetStructuredEncodedType.inputSize I) ^ 2 + 20 := by
  let S := feedbackArcSetStructuredEncodedType.inputSize I
  let E := edgeListStructuredEncodedType.inputSize I.graph.edges
  have hVertices : I.graph.vertices ≤ S := by
    simpa [S] using feedbackArcSetStructured_inputSize_ge_vertices I
  have hBudget : I.k ≤ S := by
    simpa [S] using feedbackArcSetStructured_inputSize_ge_budget I
  have hEdgesSize : E ≤ S := by
    simpa [E, S] using feedbackArcSetStructured_inputSize_ge_edges_inputSize I
  have hRemovedSize :
      edgeListStructuredEncodedType.inputSize cert.1 ≤ cert.1.length * (E + 1) := by
    have hElem :
        ∀ e ∈ cert.1, edgeStructuredEncodedType.inputSize e ≤ E := by
      intro e he
      have hGraphMem := hRemovedEdges e he
      simpa [E, edgeListStructuredEncodedType] using
        encodedList_element_inputSize_le_local (X := edgeStructuredEncodedType) hGraphMem
    simpa [edgeListStructuredEncodedType, E] using
      VertexCover.encodedList_inputSize_le_length_mul_bound
        edgeStructuredEncodedType cert.1 E hElem
  have hRankSizeSet :=
    HittingSet.boundedNatList_inputSize_le (I.graph.vertices + 1) cert.2 hRankBounds
  have hRankSize :
      partitionWeightsStructuredEncodedType.inputSize cert.2 ≤
        cert.2.length * (I.graph.vertices + 2) := by
    simpa [partitionWeightsStructuredEncodedType] using hRankSizeSet
  calc
    feedbackArcSetCertificateEncodedType.inputSize cert
        = edgeListStructuredEncodedType.inputSize cert.1 +
            partitionWeightsStructuredEncodedType.inputSize cert.2 + 1 := by
          simp [feedbackArcSetCertificateEncodedType, EncodedType.inputSize,
            EncodedType.prod]
          omega
    _ ≤ cert.1.length * (E + 1) +
          cert.2.length * (I.graph.vertices + 2) + 1 := by
          exact Nat.add_le_add_right (Nat.add_le_add hRemovedSize hRankSize) 1
    _ ≤ I.k * (E + 1) + I.graph.vertices * (I.graph.vertices + 2) + 1 := by
          have hRankLenLe : cert.2.length ≤ I.graph.vertices := by omega
          exact Nat.add_le_add_right
            (Nat.add_le_add
              (Nat.mul_le_mul_right (E + 1) hLen)
              (Nat.mul_le_mul_right (I.graph.vertices + 2) hRankLenLe)) 1
    _ ≤ S * (S + 1) + S * (S + 2) + 1 := by
          have hE1 : E + 1 ≤ S + 1 := Nat.succ_le_succ hEdgesSize
          have hV2 : I.graph.vertices + 2 ≤ S + 2 := by omega
          exact Nat.add_le_add_right
            (Nat.add_le_add (Nat.mul_le_mul hBudget hE1)
              (Nat.mul_le_mul hVertices hV2)) 1
    _ ≤ 20 * S ^ 2 + 20 := by
          nlinarith [sq_nonneg (S : Int)]

/-! ### Semantic correctness -/

theorem no_directed_cycle_of_rank_strict_after_delete
    {g : GraphInput} {removed : List (Nat × Nat)} {ranks cycle : List Nat}
    (hRank : ∀ e ∈ g.edges, e.1 < g.vertices → e.2 < g.vertices →
      e ∉ removed → rankOf ranks e.1 < rankOf ranks e.2)
    (hCycle : DirectedCycle (deleteArcs g removed) cycle) :
    False := by
  classical
  rcases hCycle with ⟨hPos, _hNodup, hBounds, hStep⟩
  let rankList := cycle.map (rankOf ranks)
  have hRankPos : 0 < rankList.length := by simpa [rankList] using hPos
  let m := rankList.maximum_of_length_pos hRankPos
  have hmMem : m ∈ rankList := List.maximum_of_length_pos_mem hRankPos
  rcases List.mem_map.mp hmMem with ⟨u, huCycle, huRank⟩
  rcases hStep u huCycle with ⟨v, hvCycle, hEdgeDeleted⟩
  rcases (hasDirectedEdge_deleteArcs_iff.mp hEdgeDeleted) with ⟨hEdge, hNotRemoved⟩
  have huBound : u < g.vertices := by simpa [deleteArcs] using hBounds u huCycle
  have hvBound : v < g.vertices := by simpa [deleteArcs] using hBounds v hvCycle
  have hUV : rankOf ranks u < rankOf ranks v :=
    hRank (u, v) hEdge huBound hvBound hNotRemoved
  have hvLe : rankOf ranks v ≤ m := by
    have hvRankMem : rankOf ranks v ∈ rankList := List.mem_map.mpr ⟨v, hvCycle, rfl⟩
    simpa [m] using List.le_maximum_of_length_pos_of_mem hvRankMem hRankPos
  have huEq : rankOf ranks u = m := by simpa [rankList] using huRank
  omega

theorem feedbackArcSetStructuredFiniteVerify_complete_of_witness
    (I : FeedbackArcSetInput) {removed : List (Nat × Nat)}
    (hLen : removed.length ≤ I.k) (hWitness : FeedbackArcSetWitness I.graph removed) :
    ∃ cert : FeedbackArcSetCertificate,
      feedbackArcSetCertificateEncodedType.inputSize cert ≤
        20 * (feedbackArcSetStructuredEncodedType.inputSize I) ^ 2 + 20 ∧
      feedbackArcSetStructuredFiniteVerify I cert = true := by
  classical
  rcases hWitness with ⟨hRemovedEdges, hNoCycle⟩
  let gDeleted := deleteArcs I.graph removed
  let R := List.range I.graph.vertices
  have hRNodup : R.Nodup := by
    simpa [R] using List.nodup_range (n := I.graph.vertices)
  have hRBounds : ∀ v ∈ R, v < gDeleted.vertices := by
    intro v hv
    simpa [R, gDeleted, deleteArcs] using List.mem_range.mp hv
  have hRDisjoint : ∀ v ∈ R, v ∉ ([] : List Nat) := by
    intro v hv
    simp
  have hHits :
      ∀ cycle : List Nat, DirectedCycle gDeleted cycle → ∃ v ∈ cycle, v ∈ ([] : List Nat) := by
    intro cycle hCycle
    exact False.elim (hNoCycle cycle (by simpa [gDeleted] using hCycle))
  rcases FeedbackNodeSetMembership.exists_rank_for_subset
      gDeleted ([] : List Nat) R hRNodup hRBounds hRDisjoint hHits with
    ⟨rank, hRankBound, hRankEdges⟩
  let ranks := FeedbackNodeSetMembership.rankListFromRank I.graph.vertices R rank
  let cert : FeedbackArcSetCertificate := (removed, ranks)
  have hRankLen : ranks.length = I.graph.vertices := by
    simp [ranks, FeedbackNodeSetMembership.rankListFromRank]
  have hRankBounds : ∀ r ∈ ranks, r < I.graph.vertices + 1 := by
    intro r hr
    rcases List.mem_map.mp hr with ⟨v, hvRange, hrv⟩
    have hv : v < I.graph.vertices := List.mem_range.mp hvRange
    have hvR : v ∈ R := by simpa [R] using hvRange
    have hBound := hRankBound v hvR
    have hRLen : R.length = I.graph.vertices := by simp [R]
    simp [hvR] at hrv
    omega
  refine ⟨cert, ?_, ?_⟩
  · exact feedbackArcSetCertificate_inputSize_le_poly
      I cert hLen hRemovedEdges hRankLen hRankBounds
  · refine (feedbackArcSetStructuredFiniteVerify_eq_true_iff I cert).2 ?_
    refine ⟨hLen, hRemovedEdges, ?_⟩
    intro e he
    by_cases hActive :
        e.1 < I.graph.vertices ∧ e.2 < I.graph.vertices ∧ e ∉ removed
    · rcases hActive with ⟨hu, hv, hNotRemoved⟩
      have heDeleted : e ∈ gDeleted.edges := by
        exact (mem_deleteArcs_edges_iff (g := I.graph) (removed := removed) (e := e)).2
          ⟨he, hNotRemoved⟩
      have huR : e.1 ∈ R := by simpa [R] using List.mem_range.mpr hu
      have hvR : e.2 ∈ R := by simpa [R] using List.mem_range.mpr hv
      have hLt := hRankEdges e (by simpa [gDeleted] using heDeleted) huR hvR
      have hLeftRank :
          rankOf ranks e.1 = rank e.1 := by
        simpa [rankOf, ranks, huR] using
          FeedbackNodeSetMembership.rankOf_rankListFromRank
            (vertices := I.graph.vertices) (R := R) (rank := rank) (v := e.1) hu
      have hRightRank :
          rankOf ranks e.2 = rank e.2 := by
        simpa [rankOf, ranks, hvR] using
          FeedbackNodeSetMembership.rankOf_rankListFromRank
            (vertices := I.graph.vertices) (R := R) (rank := rank) (v := e.2) hv
      have hActiveBool :
          fasEdgeActiveBool ((I.graph.vertices, cert), e) = true := by
        exact (fasEdgeActiveBool_eq_true_iff ((I.graph.vertices, cert), e)).2
          ⟨hu, hv, hNotRemoved⟩
      have hLtBool :
          FeedbackNodeSet.natLtBool (rankOf ranks e.1, rankOf ranks e.2) = true := by
        exact (FeedbackNodeSet.natLtBool_eq_true_iff
          (rankOf ranks e.1, rankOf ranks e.2)).2 (by
            simpa [hLeftRank, hRightRank] using hLt)
      have hLtBoolCert :
          FeedbackNodeSet.natLtBool (rankOf cert.2 e.1, rankOf cert.2 e.2) = true := by
        simpa [cert] using hLtBool
      rw [fasEdgeRankOKBool, hActiveBool]
      simpa [graphBoolOrPair] using hLtBoolCert
    · have hActiveBool :
          fasEdgeActiveBool ((I.graph.vertices, cert), e) = false := by
        cases hBool : fasEdgeActiveBool ((I.graph.vertices, cert), e)
        · rfl
        · have hProp :=
            (fasEdgeActiveBool_eq_true_iff ((I.graph.vertices, cert), e)).1 hBool
          exact False.elim (hActive hProp)
      simp [fasEdgeRankOKBool, hActiveBool, graphBoolOrPair]

theorem feedbackArcSetStructuredFiniteVerify_sound
    (I : FeedbackArcSetInput) (cert : FeedbackArcSetCertificate)
    (hVerify : feedbackArcSetStructuredFiniteVerify I cert = true) :
    FeedbackArcSet I := by
  rcases (feedbackArcSetStructuredFiniteVerify_eq_true_iff I cert).1 hVerify with
    ⟨hLen, hRemovedEdges, hEdges⟩
  let removed := cert.1
  have hRankStrict :
      ∀ e ∈ I.graph.edges, e.1 < I.graph.vertices → e.2 < I.graph.vertices →
        e ∉ removed → rankOf cert.2 e.1 < rankOf cert.2 e.2 := by
    intro e he hu hv hNotRemoved
    exact rank_lt_of_fasEdgeRankOKBool (hEdges e he) hu hv hNotRemoved
  refine ⟨removed, hLen, ?_⟩
  refine ⟨hRemovedEdges, ?_⟩
  intro cycle hCycle
  exact no_directed_cycle_of_rank_strict_after_delete
    (g := I.graph) (removed := removed) (ranks := cert.2) hRankStrict hCycle

end FeedbackArcSetMembership

/-- Direct finite-certificate TM verifier for faithful structured Feedback Arc Set. -/
noncomputable def feedbackArcSetStructuredFiniteTMVerifier :
    TMVerifier feedbackArcSetStructuredDecisionProblem where
  Cert := FeedbackArcSetMembership.feedbackArcSetCertificateEncodedType
  verify := FeedbackArcSetMembership.feedbackArcSetStructuredFiniteVerify
  verifier_polytime :=
    FeedbackArcSetMembership.feedbackArcSetStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨2, 20, 20, ?_⟩
    intro I hYes
    rcases hYes with ⟨removed, hLen, hWitness⟩
    exact FeedbackArcSetMembership.feedbackArcSetStructuredFiniteVerify_complete_of_witness
      I hLen hWitness
  sound := by
    intro I cert hVerify
    exact FeedbackArcSetMembership.feedbackArcSetStructuredFiniteVerify_sound I cert hVerify

theorem feedbackArcSetStructured_TMInNP :
    TMInNP feedbackArcSetStructuredDecisionProblem :=
  TMInNP.intro feedbackArcSetStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
