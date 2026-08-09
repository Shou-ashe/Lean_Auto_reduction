/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.NatListSplitTM
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipFeedbackArcSet

/-!
Alternative unary nat-list certificate verifier for faithful structured
Feedback Arc Set.

The original certificate is a pair `(removed, ranks)`, where `removed` is a list
of arcs.  This verifier uses one nat list whose first `graph.vertices` entries
are the rank table and whose remaining entries are adjacent endpoint pairs.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace NatPairListFromFlat

abbrev accEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool
    (EncodedType.prod EncodedType.nat edgeListStructuredEncodedType)

abbrev Acc := Bool × Nat × List (Nat × Nat)

def initAcc : Acc :=
  (false, 0, [])

def edgeEndpoints (e : Nat × Nat) : List Nat :=
  [e.1, e.2]

def edgeEndpointsList (edges : List (Nat × Nat)) : List Nat :=
  edges.flatMap edgeEndpoints

def step (p : Acc × Nat) : Acc :=
  if p.1.1 then
    (false, 0, p.1.2.2 ++ [(p.1.2.1, p.2)])
  else
    (true, p.2, p.1.2.2)

def fromFlat (xs : List Nat) : List (Nat × Nat) :=
  (xs.foldl (fun acc x => step (acc, x)) initAcc).2.2

theorem fold_edgeEndpointsList_eq
    (edges out : List (Nat × Nat)) :
    (edgeEndpointsList edges).foldl (fun acc x => step (acc, x))
        ((false, 0, out) : Acc) =
      ((false, 0, out ++ edges) : Acc) := by
  induction edges generalizing out with
  | nil =>
      simp [edgeEndpointsList]
  | cons e rest ih =>
      rcases e with ⟨u, v⟩
      change
        (edgeEndpointsList rest).foldl (fun acc x => step (acc, x))
            ((false, 0, out ++ [(u, v)]) : Acc) =
          ((false, 0, out ++ (u, v) :: rest) : Acc)
      simpa [List.append_assoc] using ih (out ++ [(u, v)])

theorem fromFlat_edgeEndpointsList (edges : List (Nat × Nat)) :
    fromFlat (edgeEndpointsList edges) = edges := by
  have h := fold_edgeEndpointsList_eq edges []
  simpa [fromFlat, initAcc] using congrArg (fun q : Acc => q.2.2) h

theorem edgeEndpointsList_inputSize_eq (edges : List (Nat × Nat)) :
    setStructuredEncodedType.inputSize (edgeEndpointsList edges) =
      edgeListStructuredEncodedType.inputSize edges := by
  induction edges with
  | nil =>
      native_decide
  | cons e rest ih =>
      rcases e with ⟨u, v⟩
      rw [edgeEndpointsList]
      simp only [List.flatMap_cons]
      change
        (EncodedType.list EncodedType.nat).inputSize
            (edgeEndpoints (u, v) ++ edgeEndpointsList rest) =
          (EncodedType.list edgeStructuredEncodedType).inputSize ((u, v) :: rest)
      have hAppend :=
        Clique.encodedList_inputSize_append EncodedType.nat
          (edgeEndpoints (u, v)) (edgeEndpointsList rest)
      have ihRaw :
          (EncodedType.list EncodedType.nat).inputSize (edgeEndpointsList rest) =
            (EncodedType.list edgeStructuredEncodedType).inputSize rest := by
        simpa [setStructuredEncodedType, edgeListStructuredEncodedType] using ih
      calc
        (EncodedType.list EncodedType.nat).inputSize
            (edgeEndpoints (u, v) ++ edgeEndpointsList rest)
            =
              (EncodedType.list EncodedType.nat).inputSize (edgeEndpoints (u, v)) +
                (EncodedType.list EncodedType.nat).inputSize (edgeEndpointsList rest) := hAppend
        _ =
              (EncodedType.list EncodedType.nat).inputSize (edgeEndpoints (u, v)) +
                (EncodedType.list edgeStructuredEncodedType).inputSize rest := by
              rw [ihRaw]
        _ = (EncodedType.list edgeStructuredEncodedType).inputSize ((u, v) :: rest) := by
              have hHead :
                  (EncodedType.list EncodedType.nat).inputSize (edgeEndpoints (u, v)) =
                    u + v + 4 := by
                change
                  (EncodedType.list EncodedType.nat).inputSize ([u, v] : List Nat) =
                    u + v + 4
                simp [EncodedType.inputSize, EncodedType.list, EncodedType.nat]
                omega
              have hCons :
                  (EncodedType.list edgeStructuredEncodedType).inputSize ((u, v) :: rest) =
                    u + v + 4 + (EncodedType.list edgeStructuredEncodedType).inputSize rest := by
                rw [EncodedType.inputSize_list_cons]
                simp [edgeStructuredEncodedType, EncodedType.inputSize_prod,
                  EncodedType.inputSize_nat]
                omega
              rw [hHead, hCons]

theorem step_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod accEncodedType EncodedType.nat)
      accEncodedType
      step := by
  let P := EncodedType.prod accEncodedType EncodedType.nat
  let Tail := EncodedType.prod EncodedType.nat edgeListStructuredEncodedType
  have hAcc : TMPolyTimeMap P accEncodedType (fun p : Acc × Nat => p.1) := by
    simpa [P] using TMPolyTimeMap.fst accEncodedType EncodedType.nat
  have hX : TMPolyTimeMap P EncodedType.nat (fun p : Acc × Nat => p.2) := by
    simpa [P] using TMPolyTimeMap.snd accEncodedType EncodedType.nat
  have hPending : TMPolyTimeMap P EncodedType.bool (fun p : Acc × Nat => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool Tail
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, accEncodedType, Tail, P] using hComp
  have hTail : TMPolyTimeMap P Tail (fun p : Acc × Nat => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool Tail
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, accEncodedType, Tail, P] using hComp
  have hHold : TMPolyTimeMap P EncodedType.nat (fun p : Acc × Nat => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, Tail, P] using hComp
  have hEdges :
      TMPolyTimeMap P edgeListStructuredEncodedType (fun p : Acc × Nat => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, Tail, P] using hComp
  have hFalse : TMPolyTimeMap P EncodedType.bool (fun _ : Acc × Nat => false) :=
    TMPolyTimeMap.const P EncodedType.bool false
  have hTrue : TMPolyTimeMap P EncodedType.bool (fun _ : Acc × Nat => true) :=
    TMPolyTimeMap.const P EncodedType.bool true
  have hZero : TMPolyTimeMap P EncodedType.nat (fun _ : Acc × Nat => (0 : Nat)) :=
    TMPolyTimeMap.const P EncodedType.nat (0 : Nat)
  have hEdge :
      TMPolyTimeMap P edgeStructuredEncodedType
        (fun p : Acc × Nat => (p.1.2.1, p.2)) := by
    simpa [edgeStructuredEncodedType] using TMPolyTimeMap.prod_mk hHold hX
  have hSingleton :
      TMPolyTimeMap P edgeListStructuredEncodedType
        (fun p : Acc × Nat => [(p.1.2.1, p.2)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton edgeStructuredEncodedType)
      hEdge
    simpa [Function.comp, edgeListStructuredEncodedType, P] using hComp
  have hAppendInput :
      TMPolyTimeMap P
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun p : Acc × Nat => (p.1.2.2, [(p.1.2.1, p.2)])) :=
    TMPolyTimeMap.prod_mk hEdges hSingleton
  have hAppend :
      TMPolyTimeMap P edgeListStructuredEncodedType
        (fun p : Acc × Nat => p.1.2.2 ++ [(p.1.2.1, p.2)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append edgeStructuredEncodedType)
      hAppendInput
    simpa [Function.comp, edgeListStructuredEncodedType, P] using hComp
  have hFalseBranchTail :
      TMPolyTimeMap P Tail
        (fun p : Acc × Nat => (p.2, p.1.2.2)) :=
    TMPolyTimeMap.prod_mk hX hEdges
  have hFalseBranch :
      TMPolyTimeMap P accEncodedType
        (fun p : Acc × Nat => (show Acc from (true, p.2, p.1.2.2))) :=
    TMPolyTimeMap.prod_mk hTrue hFalseBranchTail
  have hTrueBranchTail :
      TMPolyTimeMap P Tail
        (fun p : Acc × Nat => ((0 : Nat), p.1.2.2 ++ [(p.1.2.1, p.2)])) :=
    TMPolyTimeMap.prod_mk hZero hAppend
  have hTrueBranch :
      TMPolyTimeMap P accEncodedType
        (fun p : Acc × Nat =>
          (show Acc from (false, 0, p.1.2.2 ++ [(p.1.2.1, p.2)]))) :=
    TMPolyTimeMap.prod_mk hFalse hTrueBranchTail
  have hBranchInput :
      TMPolyTimeMap P (EncodedType.prod EncodedType.bool P)
        (fun p : Acc × Nat => (p.1.1, p)) :=
    TMPolyTimeMap.prod_mk hPending (TMPolyTimeMap.id P)
  have hBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool P) accEncodedType
        (fun p : Bool × (Acc × Nat) =>
          match p.1 with
          | true =>
              (show Acc from (false, 0, p.2.1.2.2 ++ [(p.2.1.2.1, p.2.2)]))
          | false => (show Acc from (true, p.2.2, p.2.1.2.2))) :=
    graphBoolProduct_dispatch_tm_polytime P accEncodedType
      (fFalse := fun p : Acc × Nat => (show Acc from (true, p.2, p.1.2.2)))
      (fTrue := fun p : Acc × Nat =>
        (show Acc from (false, 0, p.1.2.2 ++ [(p.1.2.1, p.2)])))
      hFalseBranch hTrueBranch
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext p
  cases h : p.1.1 <;> simp [Function.comp, step, h]

theorem initAcc_bound (xs : List Nat) :
    accEncodedType.inputSize initAcc ≤
      (Polynomial.C 10).eval (setStructuredEncodedType.inputSize xs) := by
  have h : accEncodedType.inputSize initAcc ≤ 10 := by
    native_decide
  simpa using h

theorem step_growth
    (source : List Nat) (acc : accEncodedType.Carrier) (x : Nat)
    (hX : EncodedType.nat.inputSize x ≤ setStructuredEncodedType.inputSize source) :
    accEncodedType.inputSize (step (acc, x)) ≤
      accEncodedType.inputSize acc +
        (Polynomial.C 10 * Polynomial.X + Polynomial.C 100).eval
          (setStructuredEncodedType.inputSize source) := by
  rcases acc with ⟨pending, hold, edges⟩
  change Bool at pending
  change Nat at hold
  change List (Nat × Nat) at edges
  change Nat at x
  have hXSize : x + 1 ≤ setStructuredEncodedType.inputSize source := by
    simpa [EncodedType.inputSize_nat] using hX
  cases pending
  · simp [step, accEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_nat,
      EncodedType.inputSize_bool, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X] at hXSize ⊢
    omega
  · have hAppend :
        edgeListStructuredEncodedType.inputSize (edges ++ [(hold, x)]) =
          edgeListStructuredEncodedType.inputSize edges +
            edgeStructuredEncodedType.inputSize (hold, x) + 1 := by
      simpa [edgeListStructuredEncodedType, EncodedType.inputSize_list_cons,
        EncodedType.inputSize_list_nil] using
        Clique.encodedList_inputSize_append edgeStructuredEncodedType edges [(hold, x)]
    have hAppendRaw :
        (EncodedType.list (EncodedType.prod EncodedType.nat EncodedType.nat)).inputSize
            (edges ++ [(hold, x)]) =
          (EncodedType.list (EncodedType.prod EncodedType.nat EncodedType.nat)).inputSize edges +
            (EncodedType.prod EncodedType.nat EncodedType.nat).inputSize (hold, x) + 1 := by
      simpa [edgeListStructuredEncodedType, edgeStructuredEncodedType] using hAppend
    simp [step, hAppendRaw, accEncodedType, edgeStructuredEncodedType,
      edgeListStructuredEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_nat,
      EncodedType.inputSize_bool, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X] at hXSize ⊢
    omega

theorem fold_tm_polytime :
    TMPolyTimeMap
      setStructuredEncodedType
      accEncodedType
      (fun xs : List Nat => xs.foldl (fun acc x => step (acc, x)) initAcc) := by
  rcases step_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      EncodedType.nat accEncodedType step initAcc hStep
      (Polynomial.C 10) (Polynomial.C 10 * Polynomial.X + Polynomial.C 100)
      ?_ ?_
  · intro xs
    exact initAcc_bound xs
  · intro source acc x hX
    exact step_growth source acc x hX

theorem fromFlat_tm_polytime :
    TMPolyTimeMap setStructuredEncodedType edgeListStructuredEncodedType fromFlat := by
  have hFold := fold_tm_polytime
  have hTail :=
    TMPolyTimeMap.snd EncodedType.bool
      (EncodedType.prod EncodedType.nat edgeListStructuredEncodedType)
  have hEdges := TMPolyTimeMap.snd EncodedType.nat edgeListStructuredEncodedType
  have hTailComp := TMPolyTimeMap.comp hTail hFold
  have hEdgesComp := TMPolyTimeMap.comp hEdges hTailComp
  simpa [Function.comp, fromFlat, accEncodedType] using hEdgesComp

end NatPairListFromFlat

namespace FeedbackArcSetMembership

abbrev feedbackArcSetFlatCertificateEncodedType : EncodedType :=
  setStructuredEncodedType

def feedbackArcSetFlatCertificatePair
    (I : FeedbackArcSetInput) (xs : List Nat) : FeedbackArcSetCertificate :=
  let p := NatListSplit.split (I.graph.vertices, xs)
  (NatPairListFromFlat.fromFlat p.2, p.1)

def feedbackArcSetFlatStructuredFiniteVerify
    (I : FeedbackArcSetInput) (xs : List Nat) : Bool :=
  feedbackArcSetStructuredFiniteVerify I (feedbackArcSetFlatCertificatePair I xs)

theorem feedbackArcSetFlatCertificatePair_eq
    (I : FeedbackArcSetInput) (xs : List Nat) :
    feedbackArcSetFlatCertificatePair I xs =
      (NatPairListFromFlat.fromFlat (xs.drop I.graph.vertices),
        xs.take I.graph.vertices) := by
  simpa [feedbackArcSetFlatCertificatePair] using
    congrArg
      (fun p : List Nat × List Nat => (NatPairListFromFlat.fromFlat p.2, p.1))
      (NatListSplit.split_eq_splitAt I.graph.vertices xs)

theorem feedbackArcSetFlatCertificatePair_append_of_rankLen
    (I : FeedbackArcSetInput) (removed : List (Nat × Nat)) (ranks : List Nat)
    (hRankLen : ranks.length = I.graph.vertices) :
    feedbackArcSetFlatCertificatePair I
        (ranks ++ NatPairListFromFlat.edgeEndpointsList removed) =
      (removed, ranks) := by
  rw [feedbackArcSetFlatCertificatePair_eq]
  simp [hRankLen, NatPairListFromFlat.fromFlat_edgeEndpointsList]

theorem feedbackArcSetFlatStructuredFiniteVerify_sound
    (I : FeedbackArcSetInput) (xs : List Nat)
    (hVerify : feedbackArcSetFlatStructuredFiniteVerify I xs = true) :
    FeedbackArcSet I := by
  exact feedbackArcSetStructuredFiniteVerify_sound I
    (feedbackArcSetFlatCertificatePair I xs) hVerify

theorem feedbackArcSetFlatCertificate_inputSize_le_poly
    (I : FeedbackArcSetInput) (removed : List (Nat × Nat)) (ranks : List Nat)
    (hLen : removed.length ≤ I.k)
    (hRemovedEdges : ∀ e ∈ removed, e ∈ I.graph.edges)
    (hRankLen : ranks.length = I.graph.vertices)
    (hRankBounds : ∀ r ∈ ranks, r < I.graph.vertices + 1) :
    feedbackArcSetFlatCertificateEncodedType.inputSize
        (ranks ++ NatPairListFromFlat.edgeEndpointsList removed) ≤
      20 * (feedbackArcSetStructuredEncodedType.inputSize I) ^ 2 + 20 := by
  have hAppend :
      feedbackArcSetFlatCertificateEncodedType.inputSize
          (ranks ++ NatPairListFromFlat.edgeEndpointsList removed) =
        partitionWeightsStructuredEncodedType.inputSize ranks +
          setStructuredEncodedType.inputSize
            (NatPairListFromFlat.edgeEndpointsList removed) := by
    simpa [feedbackArcSetFlatCertificateEncodedType, partitionWeightsStructuredEncodedType,
      setStructuredEncodedType] using
      Clique.encodedList_inputSize_append EncodedType.nat ranks
        (NatPairListFromFlat.edgeEndpointsList removed)
  have hPair :
      feedbackArcSetCertificateEncodedType.inputSize (removed, ranks) ≤
        20 * (feedbackArcSetStructuredEncodedType.inputSize I) ^ 2 + 20 :=
    feedbackArcSetCertificate_inputSize_le_poly
      I (removed, ranks) hLen hRemovedEdges hRankLen hRankBounds
  calc
    feedbackArcSetFlatCertificateEncodedType.inputSize
        (ranks ++ NatPairListFromFlat.edgeEndpointsList removed)
        =
          partitionWeightsStructuredEncodedType.inputSize ranks +
            setStructuredEncodedType.inputSize
              (NatPairListFromFlat.edgeEndpointsList removed) := hAppend
    _ =
          partitionWeightsStructuredEncodedType.inputSize ranks +
            edgeListStructuredEncodedType.inputSize removed := by
          rw [NatPairListFromFlat.edgeEndpointsList_inputSize_eq]
    _ ≤ feedbackArcSetCertificateEncodedType.inputSize (removed, ranks) := by
          simp [feedbackArcSetCertificateEncodedType, EncodedType.inputSize,
            EncodedType.prod, partitionWeightsStructuredEncodedType]
          omega
    _ ≤ 20 * (feedbackArcSetStructuredEncodedType.inputSize I) ^ 2 + 20 := hPair

theorem feedbackArcSetFlatStructuredFiniteVerify_complete_of_witness
    (I : FeedbackArcSetInput) {removed : List (Nat × Nat)}
    (hLen : removed.length ≤ I.k) (hWitness : FeedbackArcSetWitness I.graph removed) :
    ∃ xs : List Nat,
      feedbackArcSetFlatCertificateEncodedType.inputSize xs ≤
        20 * (feedbackArcSetStructuredEncodedType.inputSize I) ^ 2 + 20 ∧
      feedbackArcSetFlatStructuredFiniteVerify I xs = true := by
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
  refine ⟨ranks ++ NatPairListFromFlat.edgeEndpointsList removed, ?_, ?_⟩
  · exact feedbackArcSetFlatCertificate_inputSize_le_poly
      I removed ranks hLen hRemovedEdges hRankLen hRankBounds
  · rw [feedbackArcSetFlatStructuredFiniteVerify,
      feedbackArcSetFlatCertificatePair_append_of_rankLen I removed ranks hRankLen]
    refine (feedbackArcSetStructuredFiniteVerify_eq_true_iff I cert).2 ?_
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

theorem feedbackArcSetFlatStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod feedbackArcSetStructuredEncodedType
        feedbackArcSetFlatCertificateEncodedType)
      EncodedType.bool
      (fun p : FeedbackArcSetInput × List Nat =>
        feedbackArcSetFlatStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod feedbackArcSetStructuredEncodedType
    feedbackArcSetFlatCertificateEncodedType
  have hInstance :
      TMPolyTimeMap X feedbackArcSetStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, feedbackArcSetFlatCertificateEncodedType] using
      TMPolyTimeMap.fst feedbackArcSetStructuredEncodedType setStructuredEncodedType
  have hCert :
      TMPolyTimeMap X feedbackArcSetFlatCertificateEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, feedbackArcSetFlatCertificateEncodedType] using
      TMPolyTimeMap.snd feedbackArcSetStructuredEncodedType setStructuredEncodedType
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType (fun p : X.Carrier => p.1.graph) := by
    have hComp := TMPolyTimeMap.comp feedbackArcSetGraphTMBackedMap.tm_polytime hInstance
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
      feedbackArcSetFlatCertificateEncodedType, setStructuredEncodedType] using hPair
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
  have hEndpointList :
      TMPolyTimeMap X setStructuredEncodedType
        (fun p : X.Carrier => (NatListSplit.split (p.1.graph.vertices, p.2)).2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hSplit
    simpa [Function.comp, NatListSplit.outputEncodedType] using hComp
  have hRemoved :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier =>
          NatPairListFromFlat.fromFlat
            (NatListSplit.split (p.1.graph.vertices, p.2)).2) := by
    have hComp := TMPolyTimeMap.comp NatPairListFromFlat.fromFlat_tm_polytime hEndpointList
    simpa [Function.comp] using hComp
  have hPair :
      TMPolyTimeMap X feedbackArcSetCertificateEncodedType
        (fun p : X.Carrier => feedbackArcSetFlatCertificatePair p.1 p.2) := by
    have hOut :
        TMPolyTimeMap X feedbackArcSetCertificateEncodedType
          (fun p : X.Carrier =>
            (NatPairListFromFlat.fromFlat
              (NatListSplit.split (p.1.graph.vertices, p.2)).2,
              (NatListSplit.split (p.1.graph.vertices, p.2)).1)) :=
      TMPolyTimeMap.prod_mk hRemoved hRanks
    simpa [feedbackArcSetFlatCertificatePair, feedbackArcSetCertificateEncodedType] using hOut
  have hVerifyInput :
      TMPolyTimeMap X
        (EncodedType.prod feedbackArcSetStructuredEncodedType feedbackArcSetCertificateEncodedType)
        (fun p : X.Carrier => (p.1, feedbackArcSetFlatCertificatePair p.1 p.2)) :=
    TMPolyTimeMap.prod_mk hInstance hPair
  have hComp := TMPolyTimeMap.comp feedbackArcSetStructuredFiniteVerify_tm_polytime
    hVerifyInput
  simpa [Function.comp, feedbackArcSetFlatStructuredFiniteVerify,
    feedbackArcSetFlatCertificateEncodedType, X] using hComp

end FeedbackArcSetMembership

/--
Alternative direct finite-certificate TM verifier for faithful structured
Feedback Arc Set whose certificate is one unary nat list.
-/
noncomputable def feedbackArcSetFlatStructuredFiniteTMVerifier :
    TMVerifier feedbackArcSetStructuredDecisionProblem where
  Cert := FeedbackArcSetMembership.feedbackArcSetFlatCertificateEncodedType
  verify := FeedbackArcSetMembership.feedbackArcSetFlatStructuredFiniteVerify
  verifier_polytime :=
    FeedbackArcSetMembership.feedbackArcSetFlatStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨2, 20, 20, ?_⟩
    intro I hYes
    rcases hYes with ⟨removed, hLen, hWitness⟩
    exact FeedbackArcSetMembership.feedbackArcSetFlatStructuredFiniteVerify_complete_of_witness
      I hLen hWitness
  sound := by
    intro I xs hVerify
    exact FeedbackArcSetMembership.feedbackArcSetFlatStructuredFiniteVerify_sound I xs hVerify

theorem feedbackArcSetStructured_TMInNP_flat :
    TMInNP feedbackArcSetStructuredDecisionProblem :=
  TMInNP.intro feedbackArcSetFlatStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
