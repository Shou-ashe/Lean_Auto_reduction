/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipFeedbackNodeSetRunner
import Mathlib.Data.List.MinMax
import Mathlib.Tactic

/-!
Direct standard-TM NP membership witness for faithful structured Feedback Node Set.

The certificate is a removed-vertex list together with a rank table.  The verifier
checks that the removed list is within the budget and vertex bounds, and that
every input edge whose endpoints are both retained strictly increases rank.  A
directed cycle among retained vertices would then contain a maximum-rank vertex
with an outgoing edge to a strictly larger rank, a contradiction.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace FeedbackNodeSetMembership

/-! ### Semantic rank certificates -/

theorem cycle_has_removed_of_rank_strict
    {g : GraphInput} {removed ranks cycle : List Nat}
    (hRank : ∀ e ∈ g.edges, e.1 < g.vertices → e.2 < g.vertices →
      e.1 ∉ removed → e.2 ∉ removed → rankOf ranks e.1 < rankOf ranks e.2)
    (hCycle : DirectedCycle g cycle) :
    ∃ v ∈ cycle, v ∈ removed := by
  classical
  by_contra hNoHit
  have hNoRemoved : ∀ v ∈ cycle, v ∉ removed := by
    intro v hv hvrem
    exact hNoHit ⟨v, hv, hvrem⟩
  rcases hCycle with ⟨hPos, hNodup, hBounds, hStep⟩
  let rankList := cycle.map (rankOf ranks)
  have hRankPos : 0 < rankList.length := by simpa [rankList] using hPos
  let m := rankList.maximum_of_length_pos hRankPos
  have hmMem : m ∈ rankList := List.maximum_of_length_pos_mem hRankPos
  rcases List.mem_map.mp hmMem with ⟨u, huCycle, huRank⟩
  rcases hStep u huCycle with ⟨v, hvCycle, hEdge⟩
  have hUV : rankOf ranks u < rankOf ranks v := by
    exact hRank (u, v) hEdge (hBounds u huCycle) (hBounds v hvCycle)
      (hNoRemoved u huCycle) (hNoRemoved v hvCycle)
  have hvLe : rankOf ranks v ≤ m := by
    have hvRankMem : rankOf ranks v ∈ rankList := List.mem_map.mpr ⟨v, hvCycle, rfl⟩
    simpa [m] using List.le_maximum_of_length_pos_of_mem hvRankMem hRankPos
  have huEq : rankOf ranks u = m := by simpa [rankList] using huRank
  omega

theorem exists_sink_of_no_unhit_cycle
    {g : GraphInput} {removed R : List Nat}
    (hPos : 0 < R.length) (hNodup : R.Nodup)
    (hBounds : ∀ v ∈ R, v < g.vertices)
    (hDisjoint : ∀ v ∈ R, v ∉ removed)
    (hHits : ∀ cycle : List Nat, DirectedCycle g cycle → ∃ v ∈ cycle, v ∈ removed) :
    ∃ s ∈ R, ∀ v ∈ R, ¬ HasDirectedEdge g s v := by
  classical
  by_contra hNoSink
  have hStep : ∀ u ∈ R, ∃ v ∈ R, HasDirectedEdge g u v := by
    intro u hu
    by_contra hNoOut
    exact hNoSink ⟨u, hu, by
      intro v hv hEdge
      exact hNoOut ⟨v, hv, hEdge⟩⟩
  have hCycle : DirectedCycle g R := ⟨hPos, hNodup, hBounds, hStep⟩
  rcases hHits R hCycle with ⟨v, hv, hvRemoved⟩
  exact hDisjoint v hv hvRemoved

theorem exists_rank_for_subset
    (g : GraphInput) (removed R : List Nat)
    (hNodup : R.Nodup)
    (hBounds : ∀ v ∈ R, v < g.vertices)
    (hDisjoint : ∀ v ∈ R, v ∉ removed)
    (hHits : ∀ cycle : List Nat, DirectedCycle g cycle → ∃ v ∈ cycle, v ∈ removed) :
    ∃ rank : Nat → Nat,
      (∀ v ∈ R, rank v < R.length) ∧
        ∀ e ∈ g.edges, e.1 ∈ R → e.2 ∈ R → rank e.1 < rank e.2 := by
  classical
  let P : Nat → Prop := fun n =>
    ∀ R : List Nat,
      R.length = n → R.Nodup →
      (∀ v ∈ R, v < g.vertices) →
      (∀ v ∈ R, v ∉ removed) →
      (∀ cycle : List Nat, DirectedCycle g cycle → ∃ v ∈ cycle, v ∈ removed) →
      ∃ rank : Nat → Nat,
        (∀ v ∈ R, rank v < R.length) ∧
          ∀ e ∈ g.edges, e.1 ∈ R → e.2 ∈ R → rank e.1 < rank e.2
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro R hLen hNodup hBounds hDisjoint hHits
        by_cases hZero : n = 0
        · have hRlen0 : R.length = 0 := by omega
          have hRnil : R = [] := List.length_eq_zero_iff.mp hRlen0
          subst R
          refine ⟨fun _ => 0, ?_, ?_⟩ <;> simp
        · have hPosR : 0 < R.length := by omega
          rcases exists_sink_of_no_unhit_cycle (g := g) (removed := removed) (R := R)
              hPosR hNodup hBounds hDisjoint hHits with
            ⟨s, hsR, hSink⟩
          let R' := R.erase s
          have hEraseLenAdd : R'.length + 1 = R.length := by
            simpa [R'] using List.length_erase_add_one (l := R) hsR
          have hR'LenLt : R'.length < n := by omega
          have hNodup' : R'.Nodup := by
            simpa [R'] using hNodup.erase s
          have hBounds' : ∀ v ∈ R', v < g.vertices := by
            intro v hv
            exact hBounds v (by simpa [R'] using (List.mem_of_mem_erase hv))
          have hDisjoint' : ∀ v ∈ R', v ∉ removed := by
            intro v hv
            exact hDisjoint v (by simpa [R'] using (List.mem_of_mem_erase hv))
          rcases ih R'.length hR'LenLt R' rfl hNodup' hBounds' hDisjoint' hHits with
            ⟨rank, hRankBound, hRankEdges⟩
          let rankOut : Nat → Nat := fun v => if v = s then R'.length else rank v
          refine ⟨rankOut, ?_, ?_⟩
          · intro v hvR
            by_cases hvs : v = s
            · subst v
              simp [rankOut]
              omega
            · have hvR' : v ∈ R' := by
                simpa [R', hvs] using hvR
              have hvBound := hRankBound v hvR'
              simp [rankOut, hvs]
              omega
          · intro e he huR hvR
            by_cases hus : e.1 = s
            · subst s
              exact False.elim (hSink e.2 hvR he)
            · by_cases hvs : e.2 = s
              · subst s
                have huR' : e.1 ∈ R' := by
                  simpa [R', hus] using huR
                have huBound := hRankBound e.1 huR'
                simp [rankOut, hus]
                omega
              · have huR' : e.1 ∈ R' := by
                  simpa [R', hus] using huR
                have hvR' : e.2 ∈ R' := by
                  simpa [R', hvs] using hvR
                have hLt := hRankEdges e he huR' hvR'
                simp [rankOut, hus, hvs]
                exact hLt
  exact hP R.length R rfl hNodup hBounds hDisjoint hHits

def retainedVertices (vertices : Nat) (removed : List Nat) : List Nat :=
  (List.range vertices).filter fun v => decide (v ∉ removed)

theorem mem_retainedVertices_iff {vertices : Nat} {removed : List Nat} {v : Nat} :
    v ∈ retainedVertices vertices removed ↔ v < vertices ∧ v ∉ removed := by
  simp [retainedVertices]

theorem retainedVertices_nodup (vertices : Nat) (removed : List Nat) :
    (retainedVertices vertices removed).Nodup := by
  simpa [retainedVertices] using
    (List.nodup_range (n := vertices)).filter fun v => decide (v ∉ removed)

theorem retainedVertices_length_le (vertices : Nat) (removed : List Nat) :
    (retainedVertices vertices removed).length ≤ vertices := by
  simpa [retainedVertices] using
    List.length_filter_le (fun v => decide (v ∉ removed)) (List.range vertices)

def rankListFromRank (vertices : Nat) (R : List Nat) (rank : Nat → Nat) : List Nat :=
  (List.range vertices).map fun v => if v ∈ R then rank v else 0

theorem getD_range_map_eq {f : Nat → Nat} {n i : Nat} (hi : i < n) :
    ((List.range n).map f).getD i 0 = f i := by
  have hLen : i < ((List.range n).map f).length := by simpa using hi
  rw [List.getD_eq_getElem (l := (List.range n).map f) (d := 0) (n := i) hLen]
  simp

theorem rankOf_rankListFromRank {vertices : Nat} {R : List Nat} {rank : Nat → Nat}
    {v : Nat} (hv : v < vertices) :
    rankOf (rankListFromRank vertices R rank) v =
      if v ∈ R then rank v else 0 := by
  rw [rankOf_eq_getD, rankListFromRank, getD_range_map_eq hv]

/-! ### Finite verifier and correctness -/

def feedbackNodeSetStructuredFiniteVerify
    (I : FeedbackNodeSetInput) (cert : FeedbackNodeSetCertificate) : Bool :=
  graphBoolAndPair
    (HittingSet.natLeBool (cert.1.length, I.k),
      graphBoolAndPair
        (HittingSet.boundedNatListBool (I.graph.vertices, cert.1),
          fnsAllEdgesRankOKBool
            ((I.graph.vertices, cert), I.graph.edges)))

theorem feedbackNodeSetStructuredFiniteVerify_eq_true_iff
    (I : FeedbackNodeSetInput) (cert : FeedbackNodeSetCertificate) :
    feedbackNodeSetStructuredFiniteVerify I cert = true ↔
      cert.1.length ≤ I.k ∧
        (∀ v ∈ cert.1, v < I.graph.vertices) ∧
        ∀ e ∈ I.graph.edges,
          fnsEdgeRankOKBool ((I.graph.vertices, cert), e) = true := by
  rw [feedbackNodeSetStructuredFiniteVerify, graphBoolAndPair_eq_true_iff,
    graphBoolAndPair_eq_true_iff, HittingSet.natLeBool_eq_true_iff,
    HittingSet.boundedNatListBool_eq_true_iff,
    fnsAllEdgesRankOKBool_eq_true_iff]

theorem feedbackNodeSetStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod feedbackNodeSetStructuredEncodedType feedbackNodeSetCertificateEncodedType)
      EncodedType.bool
      (fun p : FeedbackNodeSetInput × FeedbackNodeSetCertificate =>
        feedbackNodeSetStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod feedbackNodeSetStructuredEncodedType feedbackNodeSetCertificateEncodedType
  have hInstance :
      TMPolyTimeMap X feedbackNodeSetStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst feedbackNodeSetStructuredEncodedType feedbackNodeSetCertificateEncodedType
  have hCert :
      TMPolyTimeMap X feedbackNodeSetCertificateEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd feedbackNodeSetStructuredEncodedType feedbackNodeSetCertificateEncodedType
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType (fun p : X.Carrier => p.1.graph) := by
    have hComp := TMPolyTimeMap.comp feedbackNodeSetGraphTMBackedMap.tm_polytime hInstance
    simpa [Function.comp, X] using hComp
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.k) := by
    have hComp := TMPolyTimeMap.comp feedbackNodeSetBudgetTMBackedMap.tm_polytime hInstance
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
  have hRemoved : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst setStructuredEncodedType partitionWeightsStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hCert
    simpa [Function.comp, feedbackNodeSetCertificateEncodedType, X] using hComp
  have hRemovedLength : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1.length) := by
    have hComp :=
      TMPolyTimeMap.comp (HittingSet.listLengthTMBackedMap EncodedType.nat).tm_polytime
        hRemoved
    simpa [Function.comp, setStructuredEncodedType, X] using hComp
  have hLengthInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.1.length, p.1.k)) :=
    TMPolyTimeMap.prod_mk hRemovedLength hBudget
  have hLengthOK :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => HittingSet.natLeBool (p.2.1.length, p.1.k)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.natLeBool_tm_polytime hLengthInput
    simpa [Function.comp] using hComp
  have hWithinInput :
      TMPolyTimeMap X HittingSet.boundedNatInstructionInputEncodedType
        (fun p : X.Carrier => (p.1.graph.vertices, p.2.1)) :=
    TMPolyTimeMap.prod_mk hVertices hRemoved
  have hWithin :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => HittingSet.boundedNatListBool (p.1.graph.vertices, p.2.1)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.boundedNatListBool_tm_polytime hWithinInput
    simpa [Function.comp, HittingSet.boundedNatInstructionInputEncodedType] using hComp
  have hContext :
      TMPolyTimeMap X fnsRankContextEncodedType
        (fun p : X.Carrier => (p.1.graph.vertices, p.2)) :=
    TMPolyTimeMap.prod_mk hVertices hCert
  have hEdgesInput :
      TMPolyTimeMap X fnsEdgeInstructionInputEncodedType
        (fun p : X.Carrier => ((p.1.graph.vertices, p.2), p.1.graph.edges)) :=
    TMPolyTimeMap.prod_mk hContext hEdges
  have hEdgesOK :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier =>
          fnsAllEdgesRankOKBool ((p.1.graph.vertices, p.2), p.1.graph.edges)) := by
    have hComp := TMPolyTimeMap.comp fnsAllEdgesRankOKBool_tm_polytime hEdgesInput
    simpa [Function.comp, fnsEdgeInstructionInputEncodedType] using hComp
  have hTailInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (HittingSet.boundedNatListBool (p.1.graph.vertices, p.2.1),
            fnsAllEdgesRankOKBool ((p.1.graph.vertices, p.2), p.1.graph.edges))) :=
    TMPolyTimeMap.prod_mk hWithin hEdgesOK
  have hTail :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier =>
          graphBoolAndPair
            (HittingSet.boundedNatListBool (p.1.graph.vertices, p.2.1),
              fnsAllEdgesRankOKBool ((p.1.graph.vertices, p.2), p.1.graph.edges))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hTailInput
    simpa [Function.comp] using hComp
  have hAllInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (HittingSet.natLeBool (p.2.1.length, p.1.k),
            graphBoolAndPair
              (HittingSet.boundedNatListBool (p.1.graph.vertices, p.2.1),
                fnsAllEdgesRankOKBool ((p.1.graph.vertices, p.2), p.1.graph.edges)))) :=
    TMPolyTimeMap.prod_mk hLengthOK hTail
  have hAll := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAllInput
  simpa [Function.comp, feedbackNodeSetStructuredFiniteVerify, X] using hAll

theorem feedbackNodeSetStructured_inputSize_ge_vertices
    (I : FeedbackNodeSetInput) :
    I.graph.vertices ≤ feedbackNodeSetStructuredEncodedType.inputSize I := by
  rw [FeedbackNodeSet.feedbackNodeSetStructured_inputSize_eq,
    VertexCover.graphStructured_inputSize_eq]
  omega

theorem feedbackNodeSetStructured_inputSize_ge_budget
    (I : FeedbackNodeSetInput) :
    I.k ≤ feedbackNodeSetStructuredEncodedType.inputSize I := by
  rw [FeedbackNodeSet.feedbackNodeSetStructured_inputSize_eq]
  omega

theorem feedbackNodeSetCertificate_inputSize_le_poly
    (I : FeedbackNodeSetInput) (cert : FeedbackNodeSetCertificate)
    (hLen : cert.1.length ≤ I.k)
    (hRemovedBounds : ∀ v ∈ cert.1, v < I.graph.vertices)
    (hRankLen : cert.2.length = I.graph.vertices)
    (hRankBounds : ∀ r ∈ cert.2, r < I.graph.vertices + 1) :
    feedbackNodeSetCertificateEncodedType.inputSize cert ≤
      10 * (feedbackNodeSetStructuredEncodedType.inputSize I) ^ 2 + 10 := by
  let S := feedbackNodeSetStructuredEncodedType.inputSize I
  have hVertices : I.graph.vertices ≤ S := by
    simpa [S] using feedbackNodeSetStructured_inputSize_ge_vertices I
  have hBudget : I.k ≤ S := by
    simpa [S] using feedbackNodeSetStructured_inputSize_ge_budget I
  have hRemovedSize :=
    HittingSet.boundedNatList_inputSize_le I.graph.vertices cert.1 hRemovedBounds
  have hRankSizeSet :=
    HittingSet.boundedNatList_inputSize_le (I.graph.vertices + 1) cert.2 hRankBounds
  have hRankSize :
      partitionWeightsStructuredEncodedType.inputSize cert.2 ≤
        cert.2.length * (I.graph.vertices + 2) := by
    simpa [partitionWeightsStructuredEncodedType] using hRankSizeSet
  calc
    feedbackNodeSetCertificateEncodedType.inputSize cert
        = setStructuredEncodedType.inputSize cert.1 +
            partitionWeightsStructuredEncodedType.inputSize cert.2 + 1 := by
          simp [feedbackNodeSetCertificateEncodedType, EncodedType.inputSize,
            EncodedType.prod]
          omega
    _ ≤ cert.1.length * (I.graph.vertices + 1) +
          cert.2.length * (I.graph.vertices + 2) + 1 := by
          exact Nat.add_le_add_right (Nat.add_le_add hRemovedSize hRankSize) 1
    _ ≤ I.k * (I.graph.vertices + 1) +
          I.graph.vertices * (I.graph.vertices + 2) + 1 := by
          have hRankLenLe : cert.2.length ≤ I.graph.vertices := by omega
          exact Nat.add_le_add_right
            (Nat.add_le_add
              (Nat.mul_le_mul_right (I.graph.vertices + 1) hLen)
              (Nat.mul_le_mul_right (I.graph.vertices + 2) hRankLenLe)) 1
    _ ≤ S * (S + 1) + S * (S + 2) + 1 := by
          have hV1 : I.graph.vertices + 1 ≤ S + 1 := Nat.succ_le_succ hVertices
          have hV2 : I.graph.vertices + 2 ≤ S + 2 := by omega
          exact Nat.add_le_add_right
            (Nat.add_le_add (Nat.mul_le_mul hBudget hV1)
              (Nat.mul_le_mul hVertices hV2)) 1
    _ ≤ 10 * S ^ 2 + 10 := by
          nlinarith [sq_nonneg (S : Int)]

theorem feedbackNodeSetStructuredFiniteVerify_complete_of_witness
    (I : FeedbackNodeSetInput) {removed : List Nat}
    (hLen : removed.length ≤ I.k) (hWitness : FeedbackNodeSetWitness I.graph removed) :
    ∃ cert : FeedbackNodeSetCertificate,
      feedbackNodeSetCertificateEncodedType.inputSize cert ≤
        10 * (feedbackNodeSetStructuredEncodedType.inputSize I) ^ 2 + 10 ∧
      feedbackNodeSetStructuredFiniteVerify I cert = true := by
  classical
  rcases hWitness with ⟨_hNodup, hBounds, hHits⟩
  let R := retainedVertices I.graph.vertices removed
  have hRNodup : R.Nodup := by
    simpa [R] using retainedVertices_nodup I.graph.vertices removed
  have hRBounds : ∀ v ∈ R, v < I.graph.vertices := by
    intro v hv
    exact (mem_retainedVertices_iff (vertices := I.graph.vertices)
      (removed := removed)).1 (by simpa [R] using hv) |>.1
  have hRDisjoint : ∀ v ∈ R, v ∉ removed := by
    intro v hv
    exact (mem_retainedVertices_iff (vertices := I.graph.vertices)
      (removed := removed)).1 (by simpa [R] using hv) |>.2
  rcases exists_rank_for_subset I.graph removed R hRNodup hRBounds hRDisjoint hHits with
    ⟨rank, hRankBound, hRankEdges⟩
  let ranks := rankListFromRank I.graph.vertices R rank
  let cert : FeedbackNodeSetCertificate := (removed, ranks)
  have hRankLen : ranks.length = I.graph.vertices := by
    simp [ranks, rankListFromRank]
  have hRankBounds : ∀ r ∈ ranks, r < I.graph.vertices + 1 := by
    intro r hr
    rcases List.mem_map.mp hr with ⟨v, hvRange, hrv⟩
    have hv : v < I.graph.vertices := List.mem_range.mp hvRange
    by_cases hvR : v ∈ R
    · have hBound := hRankBound v hvR
      have hRLen : R.length ≤ I.graph.vertices := by
        simpa [R] using retainedVertices_length_le I.graph.vertices removed
      simp [hvR] at hrv
      omega
    · simp [hvR] at hrv
      omega
  refine ⟨cert, ?_, ?_⟩
  · exact feedbackNodeSetCertificate_inputSize_le_poly I cert hLen hBounds hRankLen hRankBounds
  · refine (feedbackNodeSetStructuredFiniteVerify_eq_true_iff I cert).2 ?_
    refine ⟨hLen, hBounds, ?_⟩
    intro e he
    by_cases hActive :
        e.1 < I.graph.vertices ∧ e.1 ∉ removed ∧
          e.2 < I.graph.vertices ∧ e.2 ∉ removed
    · rcases hActive with ⟨hu, huNot, hv, hvNot⟩
      have huR : e.1 ∈ R := by
        exact (mem_retainedVertices_iff (vertices := I.graph.vertices)
          (removed := removed)).2 ⟨hu, huNot⟩
      have hvR : e.2 ∈ R := by
        exact (mem_retainedVertices_iff (vertices := I.graph.vertices)
          (removed := removed)).2 ⟨hv, hvNot⟩
      have hLt := hRankEdges e he huR hvR
      have hLeftRank :
          rankOf ranks e.1 = rank e.1 := by
        simpa [ranks, huR] using
          rankOf_rankListFromRank (vertices := I.graph.vertices) (R := R)
            (rank := rank) (v := e.1) hu
      have hRightRank :
          rankOf ranks e.2 = rank e.2 := by
        simpa [ranks, hvR] using
          rankOf_rankListFromRank (vertices := I.graph.vertices) (R := R)
            (rank := rank) (v := e.2) hv
      have hActiveBool :
          fnsEdgeActiveBool ((I.graph.vertices, cert), e) = true := by
        exact (fnsEdgeActiveBool_eq_true_iff ((I.graph.vertices, cert), e)).2
          ⟨hu, huNot, hv, hvNot⟩
      have hLtBool :
          FeedbackNodeSet.natLtBool (rankOf ranks e.1, rankOf ranks e.2) = true := by
        exact (FeedbackNodeSet.natLtBool_eq_true_iff
          (rankOf ranks e.1, rankOf ranks e.2)).2 (by
            simpa [hLeftRank, hRightRank] using hLt)
      have hLtBoolCert :
          FeedbackNodeSet.natLtBool (rankOf cert.2 e.1, rankOf cert.2 e.2) = true := by
        simpa [cert] using hLtBool
      rw [fnsEdgeRankOKBool, hActiveBool]
      simpa [graphBoolOrPair] using hLtBoolCert
    · have hActiveBool :
          fnsEdgeActiveBool ((I.graph.vertices, cert), e) = false := by
        cases hBool : fnsEdgeActiveBool ((I.graph.vertices, cert), e)
        · rfl
        · have hProp :=
            (fnsEdgeActiveBool_eq_true_iff ((I.graph.vertices, cert), e)).1 hBool
          exact False.elim (hActive hProp)
      simp [fnsEdgeRankOKBool, hActiveBool, graphBoolOrPair]

theorem feedbackNodeSetStructuredFiniteVerify_sound
    (I : FeedbackNodeSetInput) (cert : FeedbackNodeSetCertificate)
    (hVerify : feedbackNodeSetStructuredFiniteVerify I cert = true) :
    FeedbackNodeSet I := by
  rcases (feedbackNodeSetStructuredFiniteVerify_eq_true_iff I cert).1 hVerify with
    ⟨hLen, hRemovedBounds, hEdges⟩
  let removed := cert.1
  have hRankStrict :
      ∀ e ∈ I.graph.edges, e.1 < I.graph.vertices → e.2 < I.graph.vertices →
        e.1 ∉ removed → e.2 ∉ removed → rankOf cert.2 e.1 < rankOf cert.2 e.2 := by
    intro e he hu hv huNot hvNot
    exact rank_lt_of_fnsEdgeRankOKBool (hEdges e he) hu hv huNot hvNot
  refine ⟨removed.dedup, ?_, ?_⟩
  · exact (List.Sublist.length_le (List.dedup_sublist removed)).trans hLen
  · refine ⟨List.nodup_dedup removed, ?_, ?_⟩
    · intro v hv
      exact hRemovedBounds v (List.mem_dedup.mp hv)
    · intro cycle hCycle
      rcases cycle_has_removed_of_rank_strict (removed := removed) (ranks := cert.2)
          hRankStrict hCycle with
        ⟨v, hvCycle, hvRemoved⟩
      exact ⟨v, hvCycle, List.mem_dedup.mpr hvRemoved⟩

end FeedbackNodeSetMembership

/-- Direct finite-certificate TM verifier for faithful structured Feedback Node Set. -/
noncomputable def feedbackNodeSetStructuredFiniteTMVerifier :
    TMVerifier feedbackNodeSetStructuredDecisionProblem where
  Cert := FeedbackNodeSetMembership.feedbackNodeSetCertificateEncodedType
  verify := FeedbackNodeSetMembership.feedbackNodeSetStructuredFiniteVerify
  verifier_polytime :=
    FeedbackNodeSetMembership.feedbackNodeSetStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨2, 10, 10, ?_⟩
    intro I hYes
    rcases hYes with ⟨removed, hLen, hWitness⟩
    exact FeedbackNodeSetMembership.feedbackNodeSetStructuredFiniteVerify_complete_of_witness
      I hLen hWitness
  sound := by
    intro I cert hVerify
    exact FeedbackNodeSetMembership.feedbackNodeSetStructuredFiniteVerify_sound I cert hVerify

theorem feedbackNodeSetStructured_TMInNP :
    TMInNP feedbackNodeSetStructuredDecisionProblem :=
  TMInNP.intro feedbackNodeSetStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
