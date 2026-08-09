/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.FeedbackArcSetStructuredTM
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipDirectedHamiltonianCircuitEdge
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipFeedbackNodeSetRunner
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.HittingSet.MembershipRunner
import Mathlib.Tactic

/-!
Direct standard-TM edge-rank runner for faithful structured Feedback Arc Set.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace FeedbackArcSetMembership

def feedbackArcSetCertificateEncodedType : EncodedType :=
  EncodedType.prod edgeListStructuredEncodedType partitionWeightsStructuredEncodedType

abbrev FeedbackArcSetCertificate := List (Nat × Nat) × List Nat

def fasRankContextEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat feedbackArcSetCertificateEncodedType

abbrev FASRankContext := Nat × FeedbackArcSetCertificate

def fasRankAtInputEncodedType : EncodedType :=
  EncodedType.prod fasRankContextEncodedType EncodedType.nat

def fasEdgeCheckInputEncodedType : EncodedType :=
  EncodedType.prod fasRankContextEncodedType edgeStructuredEncodedType

theorem feedbackArcSetGraph_encode_filterMap (I : FeedbackArcSetInput) :
    graphStructuredEncodedType.encode I.graph =
      (feedbackArcSetStructuredEncodedType.encode I).filterMap
        (@EncodedType.prodLeftSymbol
          graphStructuredEncodedType.Symbol EncodedType.nat.Symbol) := by
  simpa [feedbackArcSetStructuredEncodedType] using
    (EncodedType.prod_left_filter_encode
      graphStructuredEncodedType EncodedType.nat (I.graph, I.k)).symm

theorem feedbackArcSetBudget_encode_filterMap (I : FeedbackArcSetInput) :
    EncodedType.nat.encode I.k =
      (feedbackArcSetStructuredEncodedType.encode I).filterMap
        (@EncodedType.prodRightSymbol
          graphStructuredEncodedType.Symbol EncodedType.nat.Symbol) := by
  simpa [feedbackArcSetStructuredEncodedType] using
    (EncodedType.prod_right_filter_encode
      graphStructuredEncodedType EncodedType.nat (I.graph, I.k)).symm

noncomputable def feedbackArcSetGraphTMBackedMap :
    TMBackedCostedMap feedbackArcSetStructuredEncodedType graphStructuredEncodedType
      (fun I : FeedbackArcSetInput => I.graph) :=
  TMBackedCostedMap.symbolFilterMap
    feedbackArcSetStructuredEncodedType graphStructuredEncodedType
    (fun I : FeedbackArcSetInput => I.graph)
    (@EncodedType.prodLeftSymbol
      graphStructuredEncodedType.Symbol EncodedType.nat.Symbol)
    feedbackArcSetGraph_encode_filterMap

noncomputable def feedbackArcSetBudgetTMBackedMap :
    TMBackedCostedMap feedbackArcSetStructuredEncodedType EncodedType.nat
      (fun I : FeedbackArcSetInput => I.k) :=
  TMBackedCostedMap.symbolFilterMap
    feedbackArcSetStructuredEncodedType EncodedType.nat
    (fun I : FeedbackArcSetInput => I.k)
    (@EncodedType.prodRightSymbol
      graphStructuredEncodedType.Symbol EncodedType.nat.Symbol)
    feedbackArcSetBudget_encode_filterMap

def rankOf (ranks : List Nat) (v : Nat) : Nat :=
  FeedbackNodeSetMembership.rankOf ranks v

theorem rankOf_eq_getD (ranks : List Nat) (v : Nat) :
    rankOf ranks v = ranks.getD v 0 := by
  rfl

def fasRankAt (p : FASRankContext × Nat) : Nat :=
  rankOf p.1.2.2 p.2

theorem fasRankAt_tm_polytime :
    TMPolyTimeMap fasRankAtInputEncodedType EncodedType.nat fasRankAt := by
  let X := fasRankAtInputEncodedType
  have hCtx : TMPolyTimeMap X fasRankContextEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, fasRankAtInputEncodedType] using
      TMPolyTimeMap.fst fasRankContextEncodedType EncodedType.nat
  have hVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X, fasRankAtInputEncodedType] using
      TMPolyTimeMap.snd fasRankContextEncodedType EncodedType.nat
  have hCert :
      TMPolyTimeMap X feedbackArcSetCertificateEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat feedbackArcSetCertificateEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, fasRankContextEncodedType, X] using hComp
  have hRanks :
      TMPolyTimeMap X partitionWeightsStructuredEncodedType (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd edgeListStructuredEncodedType partitionWeightsStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hCert
    simpa [Function.comp, feedbackArcSetCertificateEncodedType, X] using hComp
  have hInput :
      TMPolyTimeMap X (EncodedType.prod partitionWeightsStructuredEncodedType EncodedType.nat)
        (fun p : X.Carrier => (p.1.2.2, p.2)) :=
    TMPolyTimeMap.prod_mk hRanks hVertex
  have hComp := TMPolyTimeMap.comp MaxCut.natListGetD_tm_polytime hInput
  simpa [Function.comp, fasRankAt, rankOf, FeedbackNodeSetMembership.rankOf] using hComp

def fasEdgeActiveBool (p : FASRankContext × (Nat × Nat)) : Bool :=
  graphBoolAndPair
    (graphBoolAndPair
      (FeedbackNodeSet.natLtBool (p.2.1, p.1.1),
        FeedbackNodeSet.natLtBool (p.2.2, p.1.1)),
      Bool.not
        (DirectedHamiltonianCircuitMembership.sourceHasDirectedEdgeBool (p.2, p.1.2.1)))

theorem fasEdgeActiveBool_eq_true_iff (p : FASRankContext × (Nat × Nat)) :
    fasEdgeActiveBool p = true ↔
      p.2.1 < p.1.1 ∧ p.2.2 < p.1.1 ∧ p.2 ∉ p.1.2.1 := by
  rw [fasEdgeActiveBool, graphBoolAndPair_eq_true_iff,
    graphBoolAndPair_eq_true_iff,
    FeedbackNodeSet.natLtBool_eq_true_iff,
    FeedbackNodeSet.natLtBool_eq_true_iff]
  constructor
  · rintro ⟨⟨hu, hv⟩, hnotBool⟩
    refine ⟨hu, hv, ?_⟩
    intro hmem
    have htrue :=
      (DirectedHamiltonianCircuitMembership.sourceHasDirectedEdgeBool_eq_true_iff
        p.2 p.1.2.1).2 hmem
    simp [htrue] at hnotBool
  · rintro ⟨hu, hv, hnotMem⟩
    refine ⟨⟨hu, hv⟩, ?_⟩
    cases h : DirectedHamiltonianCircuitMembership.sourceHasDirectedEdgeBool (p.2, p.1.2.1)
    · rfl
    · have hmem :=
        (DirectedHamiltonianCircuitMembership.sourceHasDirectedEdgeBool_eq_true_iff
          p.2 p.1.2.1).1 h
      exact False.elim (hnotMem hmem)

theorem fasEdgeActiveBool_tm_polytime :
    TMPolyTimeMap fasEdgeCheckInputEncodedType EncodedType.bool fasEdgeActiveBool := by
  let X := fasEdgeCheckInputEncodedType
  have hCtx : TMPolyTimeMap X fasRankContextEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, fasEdgeCheckInputEncodedType] using
      TMPolyTimeMap.fst fasRankContextEncodedType edgeStructuredEncodedType
  have hEdge : TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, fasEdgeCheckInputEncodedType] using
      TMPolyTimeMap.snd fasRankContextEncodedType edgeStructuredEncodedType
  have hVertices : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat feedbackArcSetCertificateEncodedType
    have hComp := TMPolyTimeMap.comp hFst hCtx
    simpa [Function.comp, fasRankContextEncodedType, X] using hComp
  have hCert :
      TMPolyTimeMap X feedbackArcSetCertificateEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat feedbackArcSetCertificateEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, fasRankContextEncodedType, X] using hComp
  have hRemoved :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType partitionWeightsStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hCert
    simpa [Function.comp, feedbackArcSetCertificateEncodedType, X] using hComp
  have hLeftVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hEdge
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hRightVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hEdge
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hLeftLtInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.1, p.1.1)) :=
    TMPolyTimeMap.prod_mk hLeftVertex hVertices
  have hRightLtInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.2, p.1.1)) :=
    TMPolyTimeMap.prod_mk hRightVertex hVertices
  have hLeftLt :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => FeedbackNodeSet.natLtBool (p.2.1, p.1.1)) := by
    have hComp := TMPolyTimeMap.comp FeedbackNodeSet.natLtBool_tm_polytime hLeftLtInput
    simpa [Function.comp] using hComp
  have hRightLt :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => FeedbackNodeSet.natLtBool (p.2.2, p.1.1)) := by
    have hComp := TMPolyTimeMap.comp FeedbackNodeSet.natLtBool_tm_polytime hRightLtInput
    simpa [Function.comp] using hComp
  have hBoundsInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (FeedbackNodeSet.natLtBool (p.2.1, p.1.1),
            FeedbackNodeSet.natLtBool (p.2.2, p.1.1))) :=
    TMPolyTimeMap.prod_mk hLeftLt hRightLt
  have hBounds :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier =>
          graphBoolAndPair
            (FeedbackNodeSet.natLtBool (p.2.1, p.1.1),
              FeedbackNodeSet.natLtBool (p.2.2, p.1.1))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hBoundsInput
    simpa [Function.comp] using hComp
  have hContainsInput :
      TMPolyTimeMap X (EncodedType.prod vertexPairEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier => (p.2, p.1.2.1)) :=
    TMPolyTimeMap.prod_mk hEdge hRemoved
  have hContains :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier =>
          DirectedHamiltonianCircuitMembership.sourceHasDirectedEdgeBool (p.2, p.1.2.1)) := by
    have hComp :=
      TMPolyTimeMap.comp
        DirectedHamiltonianCircuitMembership.sourceHasDirectedEdgeBool_tm_polytime
        hContainsInput
    simpa [Function.comp, vertexPairEncodedType] using hComp
  have hNotContains :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier =>
          Bool.not
            (DirectedHamiltonianCircuitMembership.sourceHasDirectedEdgeBool
              (p.2, p.1.2.1))) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.bool_not hContains
    simpa [Function.comp] using hComp
  have hAllInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (graphBoolAndPair
            (FeedbackNodeSet.natLtBool (p.2.1, p.1.1),
              FeedbackNodeSet.natLtBool (p.2.2, p.1.1)),
            Bool.not
              (DirectedHamiltonianCircuitMembership.sourceHasDirectedEdgeBool
                (p.2, p.1.2.1)))) :=
    TMPolyTimeMap.prod_mk hBounds hNotContains
  have hOut := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAllInput
  simpa [Function.comp, fasEdgeActiveBool, X] using hOut

def fasEdgeRankOKBool (p : FASRankContext × (Nat × Nat)) : Bool :=
  graphBoolOrPair
    (Bool.not (fasEdgeActiveBool p),
      FeedbackNodeSet.natLtBool (rankOf p.1.2.2 p.2.1, rankOf p.1.2.2 p.2.2))

theorem rank_lt_of_fasEdgeRankOKBool
    {vertices : Nat} {removed : List (Nat × Nat)} {ranks : List Nat} {u v : Nat}
    (hOK : fasEdgeRankOKBool ((vertices, (removed, ranks)), (u, v)) = true)
    (hu : u < vertices) (hv : v < vertices) (hNotRemoved : (u, v) ∉ removed) :
    rankOf ranks u < rankOf ranks v := by
  have hActive : fasEdgeActiveBool ((vertices, (removed, ranks)), (u, v)) = true :=
    (fasEdgeActiveBool_eq_true_iff ((vertices, (removed, ranks)), (u, v))).2
      ⟨hu, hv, hNotRemoved⟩
  rw [fasEdgeRankOKBool, hActive] at hOK
  simpa [graphBoolOrPair_eq_true_iff, FeedbackNodeSet.natLtBool_eq_true_iff] using hOK

theorem fasEdgeRankOKBool_tm_polytime :
    TMPolyTimeMap fasEdgeCheckInputEncodedType EncodedType.bool fasEdgeRankOKBool := by
  let X := fasEdgeCheckInputEncodedType
  have hCtx : TMPolyTimeMap X fasRankContextEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, fasEdgeCheckInputEncodedType] using
      TMPolyTimeMap.fst fasRankContextEncodedType edgeStructuredEncodedType
  have hEdge : TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, fasEdgeCheckInputEncodedType] using
      TMPolyTimeMap.snd fasRankContextEncodedType edgeStructuredEncodedType
  have hLeftVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hEdge
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hRightVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hEdge
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hActive :
      TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => fasEdgeActiveBool p) :=
    fasEdgeActiveBool_tm_polytime
  have hNotActive :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => Bool.not (fasEdgeActiveBool p)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.bool_not hActive
    simpa [Function.comp] using hComp
  have hLeftInput :
      TMPolyTimeMap X fasRankAtInputEncodedType
        (fun p : X.Carrier => (p.1, p.2.1)) :=
    TMPolyTimeMap.prod_mk hCtx hLeftVertex
  have hRightInput :
      TMPolyTimeMap X fasRankAtInputEncodedType
        (fun p : X.Carrier => (p.1, p.2.2)) :=
    TMPolyTimeMap.prod_mk hCtx hRightVertex
  have hLeftRank :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => rankOf p.1.2.2 p.2.1) := by
    have hComp := TMPolyTimeMap.comp fasRankAt_tm_polytime hLeftInput
    simpa [Function.comp, fasRankAtInputEncodedType, fasRankAt] using hComp
  have hRightRank :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => rankOf p.1.2.2 p.2.2) := by
    have hComp := TMPolyTimeMap.comp fasRankAt_tm_polytime hRightInput
    simpa [Function.comp, fasRankAtInputEncodedType, fasRankAt] using hComp
  have hLtInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (rankOf p.1.2.2 p.2.1, rankOf p.1.2.2 p.2.2)) :=
    TMPolyTimeMap.prod_mk hLeftRank hRightRank
  have hLt :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier =>
          FeedbackNodeSet.natLtBool (rankOf p.1.2.2 p.2.1, rankOf p.1.2.2 p.2.2)) := by
    have hComp := TMPolyTimeMap.comp FeedbackNodeSet.natLtBool_tm_polytime hLtInput
    simpa [Function.comp] using hComp
  have hOrInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (Bool.not (fasEdgeActiveBool p),
            FeedbackNodeSet.natLtBool
              (rankOf p.1.2.2 p.2.1, rankOf p.1.2.2 p.2.2))) :=
    TMPolyTimeMap.prod_mk hNotActive hLt
  have hOut := TMPolyTimeMap.comp graphBoolOrPair_tm_polytime hOrInput
  simpa [Function.comp, fasEdgeRankOKBool, X] using hOut

def fasEdgeInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool
    (EncodedType.prod fasRankContextEncodedType edgeStructuredEncodedType)

abbrev FASEdgeInstruction := Bool × (FASRankContext × (Nat × Nat))

def fasEdgeInstructionListEncodedType : EncodedType :=
  EncodedType.list fasEdgeInstructionEncodedType

def fasEdgeInstructionInputEncodedType : EncodedType :=
  EncodedType.prod fasRankContextEncodedType edgeListStructuredEncodedType

def fasEdgeAccEncodedType : EncodedType :=
  EncodedType.prod fasRankContextEncodedType EncodedType.bool

abbrev FASEdgeAcc := FASRankContext × Bool

def fasEmptyCertificate : FeedbackArcSetCertificate :=
  ([], [])

def fasDummyContext : FASRankContext :=
  (0, fasEmptyCertificate)

def fasEdgeInitInstruction (ctx : FASRankContext) : FASEdgeInstruction :=
  (false, (ctx, (0, 0)))

def fasEdgeElementInstruction (e : Nat × Nat) : FASEdgeInstruction :=
  (true, (fasDummyContext, e))

def fasEdgeInstructions (p : FASRankContext × List (Nat × Nat)) :
    List FASEdgeInstruction :=
  fasEdgeInitInstruction p.1 :: p.2.map fasEdgeElementInstruction

def fasEdgeRunnerInit : FASEdgeAcc :=
  (fasDummyContext, false)

def fasEdgeStep (p : FASEdgeAcc × FASEdgeInstruction) : FASEdgeAcc :=
  if p.2.1 then
    (p.1.1, graphBoolAndPair (p.1.2, fasEdgeRankOKBool (p.1.1, p.2.2.2)))
  else
    (p.2.2.1, true)

def fasEdgesFromInstructions (xs : List FASEdgeInstruction) : Bool :=
  (xs.foldl (fun acc instr => fasEdgeStep (acc, instr)) fasEdgeRunnerInit).2

def fasAllEdgesRankOKBool (p : FASRankContext × List (Nat × Nat)) : Bool :=
  fasEdgesFromInstructions (fasEdgeInstructions p)

theorem fasEdgeElementInstructions_fold_eq_true_iff
    (edges : List (Nat × Nat)) (ctx : FASRankContext) (ok : Bool) :
    ((edges.map fasEdgeElementInstruction).foldl
        (fun acc instr => fasEdgeStep (acc, instr)) (ctx, ok)).2 = true ↔
      ok = true ∧ ∀ e ∈ edges, fasEdgeRankOKBool (ctx, e) = true := by
  induction edges generalizing ok with
  | nil =>
      simp
  | cons e edges ih =>
      rw [List.map_cons, List.foldl_cons]
      change
        ((edges.map fasEdgeElementInstruction).foldl
            (fun acc instr => fasEdgeStep (acc, instr))
            (ctx, graphBoolAndPair (ok, fasEdgeRankOKBool (ctx, e)))).2 = true ↔
          ok = true ∧ ∀ f ∈ e :: edges, fasEdgeRankOKBool (ctx, f) = true
      rw [ih]
      constructor
      · rintro ⟨hHead, hTail⟩
        rcases (graphBoolAndPair_eq_true_iff (ok, fasEdgeRankOKBool (ctx, e))).1
            hHead with
          ⟨hok, heBool⟩
        refine ⟨hok, ?_⟩
        intro f hf
        simp at hf
        rcases hf with hfe | hf
        · subst f
          exact heBool
        · exact hTail f hf
      · rintro ⟨hok, hAll⟩
        refine ⟨?_, ?_⟩
        · exact (graphBoolAndPair_eq_true_iff (ok, fasEdgeRankOKBool (ctx, e))).2
            ⟨hok, hAll e (by simp)⟩
        · intro f hf
          exact hAll f (List.mem_cons_of_mem e hf)

theorem fasAllEdgesRankOKBool_eq_true_iff
    (p : FASRankContext × List (Nat × Nat)) :
    fasAllEdgesRankOKBool p = true ↔
      ∀ e ∈ p.2, fasEdgeRankOKBool (p.1, e) = true := by
  rcases p with ⟨ctx, edges⟩
  change
    (((fasEdgeInitInstruction ctx :: edges.map fasEdgeElementInstruction).foldl
        (fun acc instr => fasEdgeStep (acc, instr)) fasEdgeRunnerInit).2 = true) ↔
      ∀ e ∈ edges, fasEdgeRankOKBool (ctx, e) = true
  rw [List.foldl_cons]
  simpa [fasEdgeRunnerInit, fasEdgeInitInstruction, fasEdgeStep] using
    fasEdgeElementInstructions_fold_eq_true_iff edges ctx true

theorem fasEdgeInitInstruction_tm_polytime :
    TMPolyTimeMap fasRankContextEncodedType fasEdgeInstructionEncodedType
      fasEdgeInitInstruction := by
  have hFalse :
      TMPolyTimeMap fasRankContextEncodedType EncodedType.bool
        (fun _ : FASRankContext => false) :=
    TMPolyTimeMap.const fasRankContextEncodedType EncodedType.bool false
  have hCtx : TMPolyTimeMap fasRankContextEncodedType fasRankContextEncodedType id :=
    TMPolyTimeMap.id fasRankContextEncodedType
  have hDummyEdge :
      TMPolyTimeMap fasRankContextEncodedType edgeStructuredEncodedType
        (fun _ : FASRankContext => ((0, 0) : Nat × Nat)) :=
    TMPolyTimeMap.const fasRankContextEncodedType edgeStructuredEncodedType
      (show edgeStructuredEncodedType.Carrier from ((0, 0) : Nat × Nat))
  have hPayload :
      TMPolyTimeMap fasRankContextEncodedType
        (EncodedType.prod fasRankContextEncodedType edgeStructuredEncodedType)
        (fun ctx : FASRankContext =>
          (ctx, (show edgeStructuredEncodedType.Carrier from ((0, 0) : Nat × Nat)))) :=
    TMPolyTimeMap.prod_mk hCtx hDummyEdge
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [fasEdgeInitInstruction, fasEdgeInstructionEncodedType] using hOut

theorem fasEdgeElementInstruction_tm_polytime :
    TMPolyTimeMap edgeStructuredEncodedType fasEdgeInstructionEncodedType
      fasEdgeElementInstruction := by
  have hTrue : TMPolyTimeMap edgeStructuredEncodedType EncodedType.bool
      (fun _ : Nat × Nat => true) :=
    TMPolyTimeMap.const edgeStructuredEncodedType EncodedType.bool true
  have hContext :
      TMPolyTimeMap edgeStructuredEncodedType fasRankContextEncodedType
        (fun _ : Nat × Nat => fasDummyContext) :=
    TMPolyTimeMap.const edgeStructuredEncodedType fasRankContextEncodedType fasDummyContext
  have hEdge : TMPolyTimeMap edgeStructuredEncodedType edgeStructuredEncodedType id :=
    TMPolyTimeMap.id edgeStructuredEncodedType
  have hPayload :
      TMPolyTimeMap edgeStructuredEncodedType
        (EncodedType.prod fasRankContextEncodedType edgeStructuredEncodedType)
        (fun e : Nat × Nat => (fasDummyContext, e)) :=
    TMPolyTimeMap.prod_mk hContext hEdge
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [fasEdgeElementInstruction, fasEdgeInstructionEncodedType] using hOut

theorem fasEdgeInstructions_tm_polytime :
    TMPolyTimeMap fasEdgeInstructionInputEncodedType
      fasEdgeInstructionListEncodedType fasEdgeInstructions := by
  let X := fasEdgeInstructionInputEncodedType
  have hCtx : TMPolyTimeMap X fasRankContextEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, fasEdgeInstructionInputEncodedType] using
      TMPolyTimeMap.fst fasRankContextEncodedType edgeListStructuredEncodedType
  have hEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, fasEdgeInstructionInputEncodedType] using
      TMPolyTimeMap.snd fasRankContextEncodedType edgeListStructuredEncodedType
  have hInit :
      TMPolyTimeMap X fasEdgeInstructionEncodedType
        (fun p : X.Carrier => fasEdgeInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp fasEdgeInitInstruction_tm_polytime hCtx
    simpa [Function.comp, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X fasEdgeInstructionListEncodedType
        (fun p : X.Carrier => [fasEdgeInitInstruction p.1]) := by
    have hComp :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton fasEdgeInstructionEncodedType) hInit
    simpa [Function.comp, fasEdgeInstructionListEncodedType, X] using hComp
  have hElementInstructions :
      TMPolyTimeMap X fasEdgeInstructionListEncodedType
        (fun p : X.Carrier => p.2.map fasEdgeElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map fasEdgeElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hEdges
    simpa [Function.comp, fasEdgeInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod fasEdgeInstructionListEncodedType fasEdgeInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([fasEdgeInitInstruction p.1], p.2.map fasEdgeElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hElementInstructions
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append fasEdgeInstructionEncodedType) hAppendInput
  simpa [Function.comp, fasEdgeInstructions, fasEdgeInstructionListEncodedType, X] using hOut

theorem fasEdgeStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod fasEdgeAccEncodedType fasEdgeInstructionEncodedType)
      fasEdgeAccEncodedType
      fasEdgeStep := by
  let X := EncodedType.prod fasEdgeAccEncodedType fasEdgeInstructionEncodedType
  let A := fasEdgeAccEncodedType
  let Payload := EncodedType.prod fasRankContextEncodedType edgeStructuredEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst A fasEdgeInstructionEncodedType
  have hInstr : TMPolyTimeMap X fasEdgeInstructionEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd A fasEdgeInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, fasEdgeInstructionEncodedType, Payload, X] using hComp
  have hPayload : TMPolyTimeMap X Payload (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, fasEdgeInstructionEncodedType, Payload, X] using hComp
  have hAccCtx : TMPolyTimeMap X fasRankContextEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst fasRankContextEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, fasEdgeAccEncodedType, X] using hComp
  have hOk : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd fasRankContextEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, fasEdgeAccEncodedType, X] using hComp
  have hPayloadCtx :
      TMPolyTimeMap X fasRankContextEncodedType (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst fasRankContextEncodedType edgeStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hPayloadEdge :
      TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd fasRankContextEncodedType edgeStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hEdgeCheckInput :
      TMPolyTimeMap X fasEdgeCheckInputEncodedType
        (fun p : X.Carrier => (p.1.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAccCtx hPayloadEdge
  have hEdgeCheck :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => fasEdgeRankOKBool (p.1.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp fasEdgeRankOKBool_tm_polytime hEdgeCheckInput
    simpa [Function.comp, fasEdgeCheckInputEncodedType] using hComp
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier => (p.1.2, fasEdgeRankOKBool (p.1.1, p.2.2.2))) :=
    TMPolyTimeMap.prod_mk hOk hEdgeCheck
  have hAnd :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier =>
          graphBoolAndPair (p.1.2, fasEdgeRankOKBool (p.1.1, p.2.2.2))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
    simpa [Function.comp] using hComp
  have hTrueBranch :
      TMPolyTimeMap X A
        (fun p : X.Carrier =>
          (p.1.1, graphBoolAndPair (p.1.2, fasEdgeRankOKBool (p.1.1, p.2.2.2)))) :=
    TMPolyTimeMap.prod_mk hAccCtx hAnd
  have hTrueConst : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hFalseBranch : TMPolyTimeMap X A (fun p : X.Carrier => (p.2.2.1, true)) :=
    TMPolyTimeMap.prod_mk hPayloadCtx hTrueConst
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranchOnProduct :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true =>
              (p.2.1.1,
                graphBoolAndPair (p.2.1.2, fasEdgeRankOKBool (p.2.1.1, p.2.2.2.2)))
          | false => (p.2.2.2.1, true)) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier => (p.2.2.1, true))
      (fTrue := fun p : X.Carrier =>
        (p.1.1, graphBoolAndPair (p.1.2, fasEdgeRankOKBool (p.1.1, p.2.2.2))))
      hFalseBranch hTrueBranch
  have hOut := TMPolyTimeMap.comp hBranchOnProduct hBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨ctx, ok⟩, ⟨tag, payloadCtx, edge⟩⟩
  cases tag <;> rfl

theorem fasEdgeStep_inputSize_le
    (source : fasEdgeInstructionListEncodedType.Carrier)
    (acc : fasEdgeAccEncodedType.Carrier)
    (instr : fasEdgeInstructionEncodedType.Carrier)
    (hAcc :
      fasEdgeAccEncodedType.inputSize acc ≤
        fasEdgeInstructionListEncodedType.inputSize source + 10)
    (hInstr :
      fasEdgeInstructionEncodedType.inputSize instr ≤
        fasEdgeInstructionListEncodedType.inputSize source) :
    fasEdgeAccEncodedType.inputSize (fasEdgeStep (acc, instr)) ≤
      fasEdgeInstructionListEncodedType.inputSize source + 10 := by
  rcases acc with ⟨ctx, ok⟩
  rcases instr with ⟨tag, payload⟩
  rcases payload with ⟨payloadCtx, edge⟩
  cases tag
  · have hLocal :
        fasEdgeAccEncodedType.inputSize (payloadCtx, true) ≤
          fasEdgeInstructionEncodedType.inputSize (false, (payloadCtx, edge)) + 10 := by
      simp [fasEdgeAccEncodedType, fasEdgeInstructionEncodedType,
        EncodedType.inputSize, EncodedType.prod, EncodedType.bool]
      omega
    exact (by simpa [fasEdgeStep] using hLocal.trans (Nat.add_le_add_right hInstr 10))
  · have hLocal :
        fasEdgeAccEncodedType.inputSize
            (fasEdgeStep ((ctx, ok), (true, (payloadCtx, edge)))) ≤
          fasEdgeAccEncodedType.inputSize (ctx, ok) := by
      by_cases h : fasEdgeRankOKBool (ctx, edge) = true <;>
        cases ok <;>
          simp [fasEdgeStep, h, fasEdgeAccEncodedType,
            EncodedType.inputSize, EncodedType.prod, EncodedType.bool]
    exact hLocal.trans hAcc

theorem fasEdgeFold_tm_polytime :
    TMPolyTimeMap fasEdgeInstructionListEncodedType fasEdgeAccEncodedType
      (fun xs : fasEdgeInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc instr => fasEdgeStep (acc, instr)) fasEdgeRunnerInit) := by
  rcases fasEdgeStep_tm_polytime with ⟨hStep⟩
  let bound : Polynomial Nat := Polynomial.X + Polynomial.C 10
  refine
    TMPolyTimeMap.list_foldl_typed_bounded
      fasEdgeInstructionEncodedType fasEdgeAccEncodedType
      fasEdgeStep fasEdgeRunnerInit hStep bound ?_ ?_
  · intro xs
    change fasEdgeAccEncodedType.inputSize fasEdgeRunnerInit ≤
      (Polynomial.X + Polynomial.C 10).eval
        (fasEdgeInstructionEncodedType.list.inputSize xs)
    have hInit : fasEdgeAccEncodedType.inputSize fasEdgeRunnerInit ≤ 10 := by
      native_decide
    simp [Polynomial.eval_add]
    omega
  · intro source acc instr hAcc hInstr
    have hAcc' :
        fasEdgeAccEncodedType.inputSize acc ≤
          fasEdgeInstructionListEncodedType.inputSize source + 10 := by
      simpa [fasEdgeInstructionListEncodedType, bound, Polynomial.eval_add] using hAcc
    have hInstr' :
        fasEdgeInstructionEncodedType.inputSize instr ≤
          fasEdgeInstructionListEncodedType.inputSize source := by
      simpa [fasEdgeInstructionListEncodedType] using hInstr
    simpa [fasEdgeInstructionListEncodedType, bound, Polynomial.eval_add] using
      fasEdgeStep_inputSize_le source acc instr hAcc' hInstr'

theorem fasEdgesFromInstructions_tm_polytime :
    TMPolyTimeMap fasEdgeInstructionListEncodedType EncodedType.bool
      fasEdgesFromInstructions := by
  have hFold := fasEdgeFold_tm_polytime
  have hOk := TMPolyTimeMap.snd fasRankContextEncodedType EncodedType.bool
  have hComp := TMPolyTimeMap.comp hOk hFold
  simpa [Function.comp, fasEdgesFromInstructions, fasEdgeAccEncodedType] using hComp

theorem fasAllEdgesRankOKBool_tm_polytime :
    TMPolyTimeMap fasEdgeInstructionInputEncodedType EncodedType.bool
      fasAllEdgesRankOKBool := by
  have hComp := TMPolyTimeMap.comp fasEdgesFromInstructions_tm_polytime
    fasEdgeInstructions_tm_polytime
  simpa [Function.comp, fasAllEdgesRankOKBool] using hComp

end FeedbackArcSetMembership

end Karp21
end ComplexityReduction
