/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.NatListSplitTM
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipFeedbackNodeSet

/-!
Alternative unary nat-list certificate verifier for faithful structured
Feedback Node Set.

The original certificate is a pair `(removed, ranks)`.  This verifier uses one
nat list whose first `graph.vertices` entries are the rank table and whose
remaining entries are the removed vertices.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace FeedbackNodeSetMembership

abbrev feedbackNodeSetFlatCertificateEncodedType : EncodedType :=
  setStructuredEncodedType

def feedbackNodeSetFlatCertificatePair
    (I : FeedbackNodeSetInput) (xs : List Nat) : FeedbackNodeSetCertificate :=
  let p := NatListSplit.split (I.graph.vertices, xs)
  (p.2, p.1)

def feedbackNodeSetFlatStructuredFiniteVerify
    (I : FeedbackNodeSetInput) (xs : List Nat) : Bool :=
  feedbackNodeSetStructuredFiniteVerify I (feedbackNodeSetFlatCertificatePair I xs)

theorem feedbackNodeSetFlatCertificatePair_eq
    (I : FeedbackNodeSetInput) (xs : List Nat) :
    feedbackNodeSetFlatCertificatePair I xs =
      (xs.drop I.graph.vertices, xs.take I.graph.vertices) := by
  simpa [feedbackNodeSetFlatCertificatePair] using
    congrArg (fun p : List Nat × List Nat => (p.2, p.1))
      (NatListSplit.split_eq_splitAt I.graph.vertices xs)

theorem feedbackNodeSetFlatCertificatePair_append_of_rankLen
    (I : FeedbackNodeSetInput) (removed ranks : List Nat)
    (hRankLen : ranks.length = I.graph.vertices) :
    feedbackNodeSetFlatCertificatePair I (ranks ++ removed) = (removed, ranks) := by
  rw [feedbackNodeSetFlatCertificatePair_eq]
  simp [hRankLen]

theorem feedbackNodeSetFlatStructuredFiniteVerify_sound
    (I : FeedbackNodeSetInput) (xs : List Nat)
    (hVerify : feedbackNodeSetFlatStructuredFiniteVerify I xs = true) :
    FeedbackNodeSet I := by
  exact feedbackNodeSetStructuredFiniteVerify_sound I
    (feedbackNodeSetFlatCertificatePair I xs) hVerify

theorem feedbackNodeSetFlatCertificate_inputSize_le_poly
    (I : FeedbackNodeSetInput) (removed ranks : List Nat)
    (hLen : removed.length ≤ I.k)
    (hRemovedBounds : ∀ v ∈ removed, v < I.graph.vertices)
    (hRankLen : ranks.length = I.graph.vertices)
    (hRankBounds : ∀ r ∈ ranks, r < I.graph.vertices + 1) :
    feedbackNodeSetFlatCertificateEncodedType.inputSize (ranks ++ removed) ≤
      10 * (feedbackNodeSetStructuredEncodedType.inputSize I) ^ 2 + 10 := by
  have hAppend :
      feedbackNodeSetFlatCertificateEncodedType.inputSize (ranks ++ removed) =
        partitionWeightsStructuredEncodedType.inputSize ranks +
          setStructuredEncodedType.inputSize removed := by
    simpa [feedbackNodeSetFlatCertificateEncodedType, partitionWeightsStructuredEncodedType,
      setStructuredEncodedType] using
      Clique.encodedList_inputSize_append EncodedType.nat ranks removed
  have hPair :
      feedbackNodeSetCertificateEncodedType.inputSize (removed, ranks) ≤
        10 * (feedbackNodeSetStructuredEncodedType.inputSize I) ^ 2 + 10 :=
    feedbackNodeSetCertificate_inputSize_le_poly
      I (removed, ranks) hLen hRemovedBounds hRankLen hRankBounds
  calc
    feedbackNodeSetFlatCertificateEncodedType.inputSize (ranks ++ removed)
        = partitionWeightsStructuredEncodedType.inputSize ranks +
            setStructuredEncodedType.inputSize removed := hAppend
    _ ≤ feedbackNodeSetCertificateEncodedType.inputSize (removed, ranks) := by
          simp [feedbackNodeSetCertificateEncodedType, EncodedType.inputSize,
            EncodedType.prod, partitionWeightsStructuredEncodedType]
          omega
    _ ≤ 10 * (feedbackNodeSetStructuredEncodedType.inputSize I) ^ 2 + 10 := hPair

theorem feedbackNodeSetFlatStructuredFiniteVerify_complete_of_witness
    (I : FeedbackNodeSetInput) {removed : List Nat}
    (hLen : removed.length ≤ I.k) (hWitness : FeedbackNodeSetWitness I.graph removed) :
    ∃ xs : List Nat,
      feedbackNodeSetFlatCertificateEncodedType.inputSize xs ≤
        10 * (feedbackNodeSetStructuredEncodedType.inputSize I) ^ 2 + 10 ∧
      feedbackNodeSetFlatStructuredFiniteVerify I xs = true := by
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
  refine ⟨ranks ++ removed, ?_, ?_⟩
  · exact feedbackNodeSetFlatCertificate_inputSize_le_poly
      I removed ranks hLen hBounds hRankLen hRankBounds
  · rw [feedbackNodeSetFlatStructuredFiniteVerify,
      feedbackNodeSetFlatCertificatePair_append_of_rankLen I removed ranks hRankLen]
    refine (feedbackNodeSetStructuredFiniteVerify_eq_true_iff I cert).2 ?_
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
        simpa [rankOf, ranks, huR] using
          rankOf_rankListFromRank
            (vertices := I.graph.vertices) (R := R) (rank := rank) (v := e.1) hu
      have hRightRank :
          rankOf ranks e.2 = rank e.2 := by
        simpa [rankOf, ranks, hvR] using
          rankOf_rankListFromRank
            (vertices := I.graph.vertices) (R := R) (rank := rank) (v := e.2) hv
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

theorem feedbackNodeSetFlatStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod feedbackNodeSetStructuredEncodedType
        feedbackNodeSetFlatCertificateEncodedType)
      EncodedType.bool
      (fun p : FeedbackNodeSetInput × List Nat =>
        feedbackNodeSetFlatStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod feedbackNodeSetStructuredEncodedType
    feedbackNodeSetFlatCertificateEncodedType
  have hInstance :
      TMPolyTimeMap X feedbackNodeSetStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, feedbackNodeSetFlatCertificateEncodedType] using
      TMPolyTimeMap.fst feedbackNodeSetStructuredEncodedType setStructuredEncodedType
  have hCert :
      TMPolyTimeMap X feedbackNodeSetFlatCertificateEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, feedbackNodeSetFlatCertificateEncodedType] using
      TMPolyTimeMap.snd feedbackNodeSetStructuredEncodedType setStructuredEncodedType
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType (fun p : X.Carrier => p.1.graph) := by
    have hComp := TMPolyTimeMap.comp feedbackNodeSetGraphTMBackedMap.tm_polytime hInstance
    simpa [Function.comp, X] using hComp
  have hVertices :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp graphVerticesTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hSplitInput :
      TMPolyTimeMap X NatListSplit.inputEncodedType
        (fun p : X.Carrier => (p.1.graph.vertices, p.2)) := by
    have hPair :
        TMPolyTimeMap X (EncodedType.prod EncodedType.nat setStructuredEncodedType)
          (fun p : X.Carrier => (p.1.graph.vertices, p.2)) :=
      TMPolyTimeMap.prod_mk hVertices hCert
    simpa [NatListSplit.inputEncodedType, EncodedListLookup.inputEncodedType,
      feedbackNodeSetFlatCertificateEncodedType, setStructuredEncodedType] using hPair
  have hSplit :
      TMPolyTimeMap X NatListSplit.outputEncodedType
        (fun p : X.Carrier => NatListSplit.split (p.1.graph.vertices, p.2)) := by
    have hComp := TMPolyTimeMap.comp NatListSplit.split_tm_polytime hSplitInput
    simpa [Function.comp, NatListSplit.outputEncodedType] using hComp
  have hRanks :
      TMPolyTimeMap X partitionWeightsStructuredEncodedType
        (fun p : X.Carrier => (NatListSplit.split (p.1.graph.vertices, p.2)).1) := by
    have hFst := TMPolyTimeMap.fst setStructuredEncodedType setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hSplit
    simpa [Function.comp, NatListSplit.outputEncodedType,
      partitionWeightsStructuredEncodedType] using hComp
  have hRemoved :
      TMPolyTimeMap X setStructuredEncodedType
        (fun p : X.Carrier => (NatListSplit.split (p.1.graph.vertices, p.2)).2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hSplit
    simpa [Function.comp, NatListSplit.outputEncodedType] using hComp
  have hPair :
      TMPolyTimeMap X feedbackNodeSetCertificateEncodedType
        (fun p : X.Carrier => feedbackNodeSetFlatCertificatePair p.1 p.2) := by
    have hOut :
        TMPolyTimeMap X feedbackNodeSetCertificateEncodedType
          (fun p : X.Carrier =>
            ((NatListSplit.split (p.1.graph.vertices, p.2)).2,
              (NatListSplit.split (p.1.graph.vertices, p.2)).1)) :=
      TMPolyTimeMap.prod_mk hRemoved hRanks
    simpa [feedbackNodeSetFlatCertificatePair, feedbackNodeSetCertificateEncodedType] using hOut
  have hVerifyInput :
      TMPolyTimeMap X
        (EncodedType.prod feedbackNodeSetStructuredEncodedType feedbackNodeSetCertificateEncodedType)
        (fun p : X.Carrier => (p.1, feedbackNodeSetFlatCertificatePair p.1 p.2)) :=
    TMPolyTimeMap.prod_mk hInstance hPair
  have hComp := TMPolyTimeMap.comp feedbackNodeSetStructuredFiniteVerify_tm_polytime
    hVerifyInput
  simpa [Function.comp, feedbackNodeSetFlatStructuredFiniteVerify,
    feedbackNodeSetFlatCertificateEncodedType, X] using hComp

end FeedbackNodeSetMembership

/--
Alternative direct finite-certificate TM verifier for faithful structured
Feedback Node Set whose certificate is one unary nat list.
-/
noncomputable def feedbackNodeSetFlatStructuredFiniteTMVerifier :
    TMVerifier feedbackNodeSetStructuredDecisionProblem where
  Cert := FeedbackNodeSetMembership.feedbackNodeSetFlatCertificateEncodedType
  verify := FeedbackNodeSetMembership.feedbackNodeSetFlatStructuredFiniteVerify
  verifier_polytime :=
    FeedbackNodeSetMembership.feedbackNodeSetFlatStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨2, 10, 10, ?_⟩
    intro I hYes
    rcases hYes with ⟨removed, hLen, hWitness⟩
    exact FeedbackNodeSetMembership.feedbackNodeSetFlatStructuredFiniteVerify_complete_of_witness
      I hLen hWitness
  sound := by
    intro I xs hVerify
    exact FeedbackNodeSetMembership.feedbackNodeSetFlatStructuredFiniteVerify_sound I xs hVerify

theorem feedbackNodeSetStructured_TMInNP_flat :
    TMInNP feedbackNodeSetStructuredDecisionProblem :=
  TMInNP.intro feedbackNodeSetFlatStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
