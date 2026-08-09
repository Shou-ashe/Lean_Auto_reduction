/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.FeedbackNodeSetStructuredTM
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetSystem
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.HittingSet.MembershipRunner
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.MaxCut.StructuredTM.Lookup
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

/-! ### Encodings and small projections -/

def feedbackNodeSetCertificateEncodedType : EncodedType :=
  EncodedType.prod setStructuredEncodedType partitionWeightsStructuredEncodedType

abbrev FeedbackNodeSetCertificate := List Nat × List Nat

def fnsRankContextEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat feedbackNodeSetCertificateEncodedType

abbrev FNSRankContext := Nat × FeedbackNodeSetCertificate

def fnsVertexKeptInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod setStructuredEncodedType EncodedType.nat)

def fnsRankAtInputEncodedType : EncodedType :=
  EncodedType.prod fnsRankContextEncodedType EncodedType.nat

def fnsEdgeCheckInputEncodedType : EncodedType :=
  EncodedType.prod fnsRankContextEncodedType edgeStructuredEncodedType

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

/-! ### Rank edge predicate and edge-list runner -/

def rankOf (ranks : List Nat) (v : Nat) : Nat :=
  MaxCut.natListGetD (ranks, v)

theorem rankOf_eq_getD (ranks : List Nat) (v : Nat) :
    rankOf ranks v = ranks.getD v 0 := by
  rfl

def vertexKeptBool (p : Nat × (List Nat × Nat)) : Bool :=
  graphBoolAndPair
    (FeedbackNodeSet.natLtBool (p.2.2, p.1),
      Bool.not (HittingSet.setContainsBool (p.2.2, p.2.1)))

theorem vertexKeptBool_eq_true_iff (p : Nat × (List Nat × Nat)) :
    vertexKeptBool p = true ↔ p.2.2 < p.1 ∧ p.2.2 ∉ p.2.1 := by
  rw [vertexKeptBool, graphBoolAndPair_eq_true_iff,
    FeedbackNodeSet.natLtBool_eq_true_iff]
  constructor
  · rintro ⟨hlt, hnotBool⟩
    refine ⟨hlt, ?_⟩
    intro hmem
    have htrue := (HittingSet.setContainsBool_eq_true_iff (p.2.2, p.2.1)).2 hmem
    simp [htrue] at hnotBool
  · rintro ⟨hlt, hnotMem⟩
    refine ⟨hlt, ?_⟩
    cases h : HittingSet.setContainsBool (p.2.2, p.2.1)
    · rfl
    · have hmem := (HittingSet.setContainsBool_eq_true_iff (p.2.2, p.2.1)).1 h
      exact False.elim (hnotMem hmem)

theorem vertexKeptBool_tm_polytime :
    TMPolyTimeMap fnsVertexKeptInputEncodedType EncodedType.bool vertexKeptBool := by
  let X := fnsVertexKeptInputEncodedType
  have hVertices : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, fnsVertexKeptInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod setStructuredEncodedType EncodedType.nat)
  have hTail :
      TMPolyTimeMap X (EncodedType.prod setStructuredEncodedType EncodedType.nat)
        (fun p : X.Carrier => p.2) := by
    simpa [X, fnsVertexKeptInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod setStructuredEncodedType EncodedType.nat)
  have hRemoved : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst setStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hLtInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.2, p.1)) :=
    TMPolyTimeMap.prod_mk hVertex hVertices
  have hLt :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => FeedbackNodeSet.natLtBool (p.2.2, p.1)) := by
    have hComp := TMPolyTimeMap.comp FeedbackNodeSet.natLtBool_tm_polytime hLtInput
    simpa [Function.comp] using hComp
  have hContainsInput :
      TMPolyTimeMap X HittingSet.setContainsInstructionInputEncodedType
        (fun p : X.Carrier => (p.2.2, p.2.1)) :=
    TMPolyTimeMap.prod_mk hVertex hRemoved
  have hContains :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => HittingSet.setContainsBool (p.2.2, p.2.1)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.setContainsBool_tm_polytime hContainsInput
    simpa [Function.comp, HittingSet.setContainsInstructionInputEncodedType] using hComp
  have hNot :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => Bool.not (HittingSet.setContainsBool (p.2.2, p.2.1))) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.bool_not hContains
    simpa [Function.comp] using hComp
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (FeedbackNodeSet.natLtBool (p.2.2, p.1),
            Bool.not (HittingSet.setContainsBool (p.2.2, p.2.1)))) :=
    TMPolyTimeMap.prod_mk hLt hNot
  have hOut := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
  simpa [Function.comp, vertexKeptBool, X] using hOut

def fnsRankAt (p : FNSRankContext × Nat) : Nat :=
  rankOf p.1.2.2 p.2

theorem fnsRankAt_tm_polytime :
    TMPolyTimeMap fnsRankAtInputEncodedType EncodedType.nat fnsRankAt := by
  let X := fnsRankAtInputEncodedType
  have hCtx : TMPolyTimeMap X fnsRankContextEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, fnsRankAtInputEncodedType] using
      TMPolyTimeMap.fst fnsRankContextEncodedType EncodedType.nat
  have hVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X, fnsRankAtInputEncodedType] using
      TMPolyTimeMap.snd fnsRankContextEncodedType EncodedType.nat
  have hCert :
      TMPolyTimeMap X feedbackNodeSetCertificateEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat feedbackNodeSetCertificateEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, fnsRankContextEncodedType, X] using hComp
  have hRanks :
      TMPolyTimeMap X partitionWeightsStructuredEncodedType (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType partitionWeightsStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hCert
    simpa [Function.comp, feedbackNodeSetCertificateEncodedType, X] using hComp
  have hInput :
      TMPolyTimeMap X (EncodedType.prod partitionWeightsStructuredEncodedType EncodedType.nat)
        (fun p : X.Carrier => (p.1.2.2, p.2)) :=
    TMPolyTimeMap.prod_mk hRanks hVertex
  have hComp := TMPolyTimeMap.comp MaxCut.natListGetD_tm_polytime hInput
  simpa [Function.comp, fnsRankAt, rankOf] using hComp

def fnsEdgeActiveBool (p : FNSRankContext × (Nat × Nat)) : Bool :=
  graphBoolAndPair
    (vertexKeptBool (p.1.1, (p.1.2.1, p.2.1)),
      vertexKeptBool (p.1.1, (p.1.2.1, p.2.2)))

theorem fnsEdgeActiveBool_eq_true_iff
    (p : FNSRankContext × (Nat × Nat)) :
    fnsEdgeActiveBool p = true ↔
      p.2.1 < p.1.1 ∧ p.2.1 ∉ p.1.2.1 ∧
        p.2.2 < p.1.1 ∧ p.2.2 ∉ p.1.2.1 := by
  rw [fnsEdgeActiveBool, graphBoolAndPair_eq_true_iff,
    vertexKeptBool_eq_true_iff, vertexKeptBool_eq_true_iff]
  constructor
  · rintro ⟨⟨hu, huNot⟩, hv, hvNot⟩
    exact ⟨hu, huNot, hv, hvNot⟩
  · rintro ⟨hu, huNot, hv, hvNot⟩
    exact ⟨⟨hu, huNot⟩, hv, hvNot⟩

theorem fnsEdgeActiveBool_tm_polytime :
    TMPolyTimeMap fnsEdgeCheckInputEncodedType EncodedType.bool fnsEdgeActiveBool := by
  let X := fnsEdgeCheckInputEncodedType
  have hCtx : TMPolyTimeMap X fnsRankContextEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, fnsEdgeCheckInputEncodedType] using
      TMPolyTimeMap.fst fnsRankContextEncodedType edgeStructuredEncodedType
  have hEdge : TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, fnsEdgeCheckInputEncodedType] using
      TMPolyTimeMap.snd fnsRankContextEncodedType edgeStructuredEncodedType
  have hVertices : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat feedbackNodeSetCertificateEncodedType
    have hComp := TMPolyTimeMap.comp hFst hCtx
    simpa [Function.comp, fnsRankContextEncodedType, X] using hComp
  have hCert :
      TMPolyTimeMap X feedbackNodeSetCertificateEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat feedbackNodeSetCertificateEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, fnsRankContextEncodedType, X] using hComp
  have hRemoved : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst setStructuredEncodedType partitionWeightsStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hCert
    simpa [Function.comp, feedbackNodeSetCertificateEncodedType, X] using hComp
  have hLeftVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hEdge
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hRightVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hEdge
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hLeftInput :
      TMPolyTimeMap X fnsVertexKeptInputEncodedType
        (fun p : X.Carrier => (p.1.1, (p.1.2.1, p.2.1))) := by
    have hTail :=
      TMPolyTimeMap.prod_mk hRemoved hLeftVertex
    exact TMPolyTimeMap.prod_mk hVertices hTail
  have hRightInput :
      TMPolyTimeMap X fnsVertexKeptInputEncodedType
        (fun p : X.Carrier => (p.1.1, (p.1.2.1, p.2.2))) := by
    have hTail :=
      TMPolyTimeMap.prod_mk hRemoved hRightVertex
    exact TMPolyTimeMap.prod_mk hVertices hTail
  have hLeft :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => vertexKeptBool (p.1.1, (p.1.2.1, p.2.1))) := by
    have hComp := TMPolyTimeMap.comp vertexKeptBool_tm_polytime hLeftInput
    simpa [Function.comp, fnsVertexKeptInputEncodedType] using hComp
  have hRight :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => vertexKeptBool (p.1.1, (p.1.2.1, p.2.2))) := by
    have hComp := TMPolyTimeMap.comp vertexKeptBool_tm_polytime hRightInput
    simpa [Function.comp, fnsVertexKeptInputEncodedType] using hComp
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (vertexKeptBool (p.1.1, (p.1.2.1, p.2.1)),
            vertexKeptBool (p.1.1, (p.1.2.1, p.2.2)))) :=
    TMPolyTimeMap.prod_mk hLeft hRight
  have hOut := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
  simpa [Function.comp, fnsEdgeActiveBool, X] using hOut

def fnsEdgeRankOKBool (p : FNSRankContext × (Nat × Nat)) : Bool :=
  graphBoolOrPair
    (Bool.not (fnsEdgeActiveBool p),
      FeedbackNodeSet.natLtBool (rankOf p.1.2.2 p.2.1, rankOf p.1.2.2 p.2.2))

theorem rank_lt_of_fnsEdgeRankOKBool
    {vertices : Nat} {removed ranks : List Nat} {u v : Nat}
    (hOK : fnsEdgeRankOKBool ((vertices, (removed, ranks)), (u, v)) = true)
    (hu : u < vertices) (hv : v < vertices) (huNot : u ∉ removed)
    (hvNot : v ∉ removed) :
    rankOf ranks u < rankOf ranks v := by
  have hActive : fnsEdgeActiveBool ((vertices, (removed, ranks)), (u, v)) = true :=
    (fnsEdgeActiveBool_eq_true_iff ((vertices, (removed, ranks)), (u, v))).2
      ⟨hu, huNot, hv, hvNot⟩
  rw [fnsEdgeRankOKBool, hActive] at hOK
  simpa [graphBoolOrPair_eq_true_iff, FeedbackNodeSet.natLtBool_eq_true_iff] using hOK

theorem fnsEdgeRankOKBool_tm_polytime :
    TMPolyTimeMap fnsEdgeCheckInputEncodedType EncodedType.bool fnsEdgeRankOKBool := by
  let X := fnsEdgeCheckInputEncodedType
  have hCtx : TMPolyTimeMap X fnsRankContextEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, fnsEdgeCheckInputEncodedType] using
      TMPolyTimeMap.fst fnsRankContextEncodedType edgeStructuredEncodedType
  have hEdge : TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, fnsEdgeCheckInputEncodedType] using
      TMPolyTimeMap.snd fnsRankContextEncodedType edgeStructuredEncodedType
  have hLeftVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hEdge
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hRightVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hEdge
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hActive :
      TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => fnsEdgeActiveBool p) :=
    fnsEdgeActiveBool_tm_polytime
  have hNotActive :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => Bool.not (fnsEdgeActiveBool p)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.bool_not hActive
    simpa [Function.comp] using hComp
  have hLeftInput :
      TMPolyTimeMap X fnsRankAtInputEncodedType
        (fun p : X.Carrier => (p.1, p.2.1)) :=
    TMPolyTimeMap.prod_mk hCtx hLeftVertex
  have hRightInput :
      TMPolyTimeMap X fnsRankAtInputEncodedType
        (fun p : X.Carrier => (p.1, p.2.2)) :=
    TMPolyTimeMap.prod_mk hCtx hRightVertex
  have hLeftRank :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => rankOf p.1.2.2 p.2.1) := by
    have hComp := TMPolyTimeMap.comp fnsRankAt_tm_polytime hLeftInput
    simpa [Function.comp, fnsRankAtInputEncodedType, fnsRankAt] using hComp
  have hRightRank :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => rankOf p.1.2.2 p.2.2) := by
    have hComp := TMPolyTimeMap.comp fnsRankAt_tm_polytime hRightInput
    simpa [Function.comp, fnsRankAtInputEncodedType, fnsRankAt] using hComp
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
          (Bool.not (fnsEdgeActiveBool p),
            FeedbackNodeSet.natLtBool
              (rankOf p.1.2.2 p.2.1, rankOf p.1.2.2 p.2.2))) :=
    TMPolyTimeMap.prod_mk hNotActive hLt
  have hOut := TMPolyTimeMap.comp graphBoolOrPair_tm_polytime hOrInput
  simpa [Function.comp, fnsEdgeRankOKBool, X] using hOut

def fnsEdgeInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool
    (EncodedType.prod fnsRankContextEncodedType edgeStructuredEncodedType)

abbrev FNSEdgeInstruction := Bool × (FNSRankContext × (Nat × Nat))

def fnsEdgeInstructionListEncodedType : EncodedType :=
  EncodedType.list fnsEdgeInstructionEncodedType

def fnsEdgeInstructionInputEncodedType : EncodedType :=
  EncodedType.prod fnsRankContextEncodedType edgeListStructuredEncodedType

def fnsEdgeAccEncodedType : EncodedType :=
  EncodedType.prod fnsRankContextEncodedType EncodedType.bool

abbrev FNSEdgeAcc := FNSRankContext × Bool

def fnsEmptyCertificate : FeedbackNodeSetCertificate :=
  ([], [])

def fnsDummyContext : FNSRankContext :=
  (0, fnsEmptyCertificate)

def fnsEdgeInitInstruction (ctx : FNSRankContext) : FNSEdgeInstruction :=
  (false, (ctx, (0, 0)))

def fnsEdgeElementInstruction (e : Nat × Nat) : FNSEdgeInstruction :=
  (true, (fnsDummyContext, e))

def fnsEdgeInstructions (p : FNSRankContext × List (Nat × Nat)) :
    List FNSEdgeInstruction :=
  fnsEdgeInitInstruction p.1 :: p.2.map fnsEdgeElementInstruction

def fnsEdgeRunnerInit : FNSEdgeAcc :=
  (fnsDummyContext, false)

def fnsEdgeStep (p : FNSEdgeAcc × FNSEdgeInstruction) : FNSEdgeAcc :=
  if p.2.1 then
    (p.1.1, graphBoolAndPair (p.1.2, fnsEdgeRankOKBool (p.1.1, p.2.2.2)))
  else
    (p.2.2.1, true)

def fnsEdgesFromInstructions (xs : List FNSEdgeInstruction) : Bool :=
  (xs.foldl (fun acc instr => fnsEdgeStep (acc, instr)) fnsEdgeRunnerInit).2

def fnsAllEdgesRankOKBool (p : FNSRankContext × List (Nat × Nat)) : Bool :=
  fnsEdgesFromInstructions (fnsEdgeInstructions p)

theorem fnsEdgeElementInstructions_fold_eq_true_iff
    (edges : List (Nat × Nat)) (ctx : FNSRankContext) (ok : Bool) :
    ((edges.map fnsEdgeElementInstruction).foldl
        (fun acc instr => fnsEdgeStep (acc, instr)) (ctx, ok)).2 = true ↔
      ok = true ∧ ∀ e ∈ edges, fnsEdgeRankOKBool (ctx, e) = true := by
  induction edges generalizing ok with
  | nil =>
      simp
  | cons e edges ih =>
      rw [List.map_cons, List.foldl_cons]
      change
        ((edges.map fnsEdgeElementInstruction).foldl
            (fun acc instr => fnsEdgeStep (acc, instr))
            (ctx, graphBoolAndPair (ok, fnsEdgeRankOKBool (ctx, e)))).2 = true ↔
          ok = true ∧ ∀ f ∈ e :: edges, fnsEdgeRankOKBool (ctx, f) = true
      rw [ih]
      constructor
      · rintro ⟨hHead, hTail⟩
        rcases (graphBoolAndPair_eq_true_iff (ok, fnsEdgeRankOKBool (ctx, e))).1
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
        · exact (graphBoolAndPair_eq_true_iff (ok, fnsEdgeRankOKBool (ctx, e))).2
            ⟨hok, hAll e (by simp)⟩
        · intro f hf
          exact hAll f (List.mem_cons_of_mem e hf)

theorem fnsAllEdgesRankOKBool_eq_true_iff
    (p : FNSRankContext × List (Nat × Nat)) :
    fnsAllEdgesRankOKBool p = true ↔
      ∀ e ∈ p.2, fnsEdgeRankOKBool (p.1, e) = true := by
  rcases p with ⟨ctx, edges⟩
  change
    (((fnsEdgeInitInstruction ctx :: edges.map fnsEdgeElementInstruction).foldl
        (fun acc instr => fnsEdgeStep (acc, instr)) fnsEdgeRunnerInit).2 = true) ↔
      ∀ e ∈ edges, fnsEdgeRankOKBool (ctx, e) = true
  rw [List.foldl_cons]
  simpa [fnsEdgeRunnerInit, fnsEdgeInitInstruction, fnsEdgeStep] using
    fnsEdgeElementInstructions_fold_eq_true_iff edges ctx true

theorem fnsEdgeInitInstruction_tm_polytime :
    TMPolyTimeMap fnsRankContextEncodedType fnsEdgeInstructionEncodedType
      fnsEdgeInitInstruction := by
  have hFalse :
      TMPolyTimeMap fnsRankContextEncodedType EncodedType.bool
        (fun _ : FNSRankContext => false) :=
    TMPolyTimeMap.const fnsRankContextEncodedType EncodedType.bool false
  have hCtx : TMPolyTimeMap fnsRankContextEncodedType fnsRankContextEncodedType id :=
    TMPolyTimeMap.id fnsRankContextEncodedType
  have hDummyEdge :
      TMPolyTimeMap fnsRankContextEncodedType edgeStructuredEncodedType
        (fun _ : FNSRankContext => ((0, 0) : Nat × Nat)) :=
    TMPolyTimeMap.const fnsRankContextEncodedType edgeStructuredEncodedType
      (show edgeStructuredEncodedType.Carrier from ((0, 0) : Nat × Nat))
  have hPayload :
      TMPolyTimeMap fnsRankContextEncodedType
        (EncodedType.prod fnsRankContextEncodedType edgeStructuredEncodedType)
        (fun ctx : FNSRankContext =>
          (ctx, (show edgeStructuredEncodedType.Carrier from ((0, 0) : Nat × Nat)))) :=
    TMPolyTimeMap.prod_mk hCtx hDummyEdge
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [fnsEdgeInitInstruction, fnsEdgeInstructionEncodedType] using hOut

theorem fnsEdgeElementInstruction_tm_polytime :
    TMPolyTimeMap edgeStructuredEncodedType fnsEdgeInstructionEncodedType
      fnsEdgeElementInstruction := by
  have hTrue : TMPolyTimeMap edgeStructuredEncodedType EncodedType.bool
      (fun _ : Nat × Nat => true) :=
    TMPolyTimeMap.const edgeStructuredEncodedType EncodedType.bool true
  have hContext :
      TMPolyTimeMap edgeStructuredEncodedType fnsRankContextEncodedType
        (fun _ : Nat × Nat => fnsDummyContext) :=
    TMPolyTimeMap.const edgeStructuredEncodedType fnsRankContextEncodedType fnsDummyContext
  have hEdge : TMPolyTimeMap edgeStructuredEncodedType edgeStructuredEncodedType id :=
    TMPolyTimeMap.id edgeStructuredEncodedType
  have hPayload :
      TMPolyTimeMap edgeStructuredEncodedType
        (EncodedType.prod fnsRankContextEncodedType edgeStructuredEncodedType)
        (fun e : Nat × Nat => (fnsDummyContext, e)) :=
    TMPolyTimeMap.prod_mk hContext hEdge
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [fnsEdgeElementInstruction, fnsEdgeInstructionEncodedType] using hOut

theorem fnsEdgeInstructions_tm_polytime :
    TMPolyTimeMap fnsEdgeInstructionInputEncodedType
      fnsEdgeInstructionListEncodedType fnsEdgeInstructions := by
  let X := fnsEdgeInstructionInputEncodedType
  have hCtx : TMPolyTimeMap X fnsRankContextEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, fnsEdgeInstructionInputEncodedType] using
      TMPolyTimeMap.fst fnsRankContextEncodedType edgeListStructuredEncodedType
  have hEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, fnsEdgeInstructionInputEncodedType] using
      TMPolyTimeMap.snd fnsRankContextEncodedType edgeListStructuredEncodedType
  have hInit :
      TMPolyTimeMap X fnsEdgeInstructionEncodedType
        (fun p : X.Carrier => fnsEdgeInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp fnsEdgeInitInstruction_tm_polytime hCtx
    simpa [Function.comp, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X fnsEdgeInstructionListEncodedType
        (fun p : X.Carrier => [fnsEdgeInitInstruction p.1]) := by
    have hComp :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton fnsEdgeInstructionEncodedType) hInit
    simpa [Function.comp, fnsEdgeInstructionListEncodedType, X] using hComp
  have hElementInstructions :
      TMPolyTimeMap X fnsEdgeInstructionListEncodedType
        (fun p : X.Carrier => p.2.map fnsEdgeElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map fnsEdgeElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hEdges
    simpa [Function.comp, fnsEdgeInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod fnsEdgeInstructionListEncodedType fnsEdgeInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([fnsEdgeInitInstruction p.1], p.2.map fnsEdgeElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hElementInstructions
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append fnsEdgeInstructionEncodedType) hAppendInput
  simpa [Function.comp, fnsEdgeInstructions, fnsEdgeInstructionListEncodedType, X] using hOut

theorem fnsEdgeStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod fnsEdgeAccEncodedType fnsEdgeInstructionEncodedType)
      fnsEdgeAccEncodedType
      fnsEdgeStep := by
  let X := EncodedType.prod fnsEdgeAccEncodedType fnsEdgeInstructionEncodedType
  let A := fnsEdgeAccEncodedType
  let Payload := EncodedType.prod fnsRankContextEncodedType edgeStructuredEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst A fnsEdgeInstructionEncodedType
  have hInstr : TMPolyTimeMap X fnsEdgeInstructionEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd A fnsEdgeInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, fnsEdgeInstructionEncodedType, Payload, X] using hComp
  have hPayload : TMPolyTimeMap X Payload (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, fnsEdgeInstructionEncodedType, Payload, X] using hComp
  have hAccCtx : TMPolyTimeMap X fnsRankContextEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst fnsRankContextEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, fnsEdgeAccEncodedType, X] using hComp
  have hOk : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd fnsRankContextEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, fnsEdgeAccEncodedType, X] using hComp
  have hPayloadCtx :
      TMPolyTimeMap X fnsRankContextEncodedType (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst fnsRankContextEncodedType edgeStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hPayloadEdge :
      TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd fnsRankContextEncodedType edgeStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hEdgeCheckInput :
      TMPolyTimeMap X fnsEdgeCheckInputEncodedType
        (fun p : X.Carrier => (p.1.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAccCtx hPayloadEdge
  have hEdgeCheck :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => fnsEdgeRankOKBool (p.1.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp fnsEdgeRankOKBool_tm_polytime hEdgeCheckInput
    simpa [Function.comp, fnsEdgeCheckInputEncodedType] using hComp
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier => (p.1.2, fnsEdgeRankOKBool (p.1.1, p.2.2.2))) :=
    TMPolyTimeMap.prod_mk hOk hEdgeCheck
  have hAnd :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier =>
          graphBoolAndPair (p.1.2, fnsEdgeRankOKBool (p.1.1, p.2.2.2))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
    simpa [Function.comp] using hComp
  have hTrueBranch :
      TMPolyTimeMap X A
        (fun p : X.Carrier =>
          (p.1.1, graphBoolAndPair (p.1.2, fnsEdgeRankOKBool (p.1.1, p.2.2.2)))) :=
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
                graphBoolAndPair (p.2.1.2, fnsEdgeRankOKBool (p.2.1.1, p.2.2.2.2)))
          | false => (p.2.2.2.1, true)) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier => (p.2.2.1, true))
      (fTrue := fun p : X.Carrier =>
        (p.1.1, graphBoolAndPair (p.1.2, fnsEdgeRankOKBool (p.1.1, p.2.2.2))))
      hFalseBranch hTrueBranch
  have hOut := TMPolyTimeMap.comp hBranchOnProduct hBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨ctx, ok⟩, ⟨tag, payloadCtx, edge⟩⟩
  cases tag <;> rfl

theorem fnsEdgeStep_inputSize_le
    (source : fnsEdgeInstructionListEncodedType.Carrier)
    (acc : fnsEdgeAccEncodedType.Carrier)
    (instr : fnsEdgeInstructionEncodedType.Carrier)
    (hAcc :
      fnsEdgeAccEncodedType.inputSize acc ≤
        fnsEdgeInstructionListEncodedType.inputSize source + 10)
    (hInstr :
      fnsEdgeInstructionEncodedType.inputSize instr ≤
        fnsEdgeInstructionListEncodedType.inputSize source) :
    fnsEdgeAccEncodedType.inputSize (fnsEdgeStep (acc, instr)) ≤
      fnsEdgeInstructionListEncodedType.inputSize source + 10 := by
  rcases acc with ⟨ctx, ok⟩
  rcases instr with ⟨tag, payload⟩
  rcases payload with ⟨payloadCtx, edge⟩
  cases tag
  · have hLocal :
        fnsEdgeAccEncodedType.inputSize (payloadCtx, true) ≤
          fnsEdgeInstructionEncodedType.inputSize (false, (payloadCtx, edge)) + 10 := by
      simp [fnsEdgeAccEncodedType, fnsEdgeInstructionEncodedType,
        EncodedType.inputSize, EncodedType.prod, EncodedType.bool]
      omega
    exact (by simpa [fnsEdgeStep] using hLocal.trans (Nat.add_le_add_right hInstr 10))
  · have hLocal :
        fnsEdgeAccEncodedType.inputSize
            (fnsEdgeStep ((ctx, ok), (true, (payloadCtx, edge)))) ≤
          fnsEdgeAccEncodedType.inputSize (ctx, ok) := by
      by_cases h : fnsEdgeRankOKBool (ctx, edge) = true <;>
        cases ok <;>
          simp [fnsEdgeStep, h, fnsEdgeAccEncodedType,
            EncodedType.inputSize, EncodedType.prod, EncodedType.bool]
    exact hLocal.trans hAcc

theorem fnsEdgeFold_tm_polytime :
    TMPolyTimeMap fnsEdgeInstructionListEncodedType fnsEdgeAccEncodedType
      (fun xs : fnsEdgeInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc instr => fnsEdgeStep (acc, instr)) fnsEdgeRunnerInit) := by
  rcases fnsEdgeStep_tm_polytime with ⟨hStep⟩
  let bound : Polynomial Nat := Polynomial.X + Polynomial.C 10
  refine
    TMPolyTimeMap.list_foldl_typed_bounded
      fnsEdgeInstructionEncodedType fnsEdgeAccEncodedType
      fnsEdgeStep fnsEdgeRunnerInit hStep bound ?_ ?_
  · intro xs
    change fnsEdgeAccEncodedType.inputSize fnsEdgeRunnerInit ≤
      (Polynomial.X + Polynomial.C 10).eval
        (fnsEdgeInstructionEncodedType.list.inputSize xs)
    have hInit : fnsEdgeAccEncodedType.inputSize fnsEdgeRunnerInit ≤ 10 := by
      native_decide
    have hEval :
        (Polynomial.X + Polynomial.C 10).eval
            (fnsEdgeInstructionEncodedType.list.inputSize xs) =
          fnsEdgeInstructionEncodedType.list.inputSize xs + 10 := by
      simp [Polynomial.eval_add]
    rw [hEval]
    omega
  · intro source acc instr hAcc hInstr
    have hAcc' :
        fnsEdgeAccEncodedType.inputSize acc ≤
          fnsEdgeInstructionListEncodedType.inputSize source + 10 := by
      simpa [fnsEdgeInstructionListEncodedType, bound, Polynomial.eval_add] using hAcc
    have hInstr' :
        fnsEdgeInstructionEncodedType.inputSize instr ≤
          fnsEdgeInstructionListEncodedType.inputSize source := by
      simpa [fnsEdgeInstructionListEncodedType] using hInstr
    simpa [fnsEdgeInstructionListEncodedType, bound, Polynomial.eval_add] using
      fnsEdgeStep_inputSize_le source acc instr hAcc' hInstr'

theorem fnsEdgesFromInstructions_tm_polytime :
    TMPolyTimeMap fnsEdgeInstructionListEncodedType EncodedType.bool
      fnsEdgesFromInstructions := by
  have hFold := fnsEdgeFold_tm_polytime
  have hOk := TMPolyTimeMap.snd fnsRankContextEncodedType EncodedType.bool
  have hComp := TMPolyTimeMap.comp hOk hFold
  simpa [Function.comp, fnsEdgesFromInstructions, fnsEdgeAccEncodedType] using hComp

theorem fnsAllEdgesRankOKBool_tm_polytime :
    TMPolyTimeMap fnsEdgeInstructionInputEncodedType EncodedType.bool
      fnsAllEdgesRankOKBool := by
  have hComp := TMPolyTimeMap.comp fnsEdgesFromInstructions_tm_polytime
    fnsEdgeInstructions_tm_polytime
  simpa [Function.comp, fnsAllEdgesRankOKBool] using hComp

end FeedbackNodeSetMembership

end Karp21
end ComplexityReduction
