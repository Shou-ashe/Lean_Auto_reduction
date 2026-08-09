/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SteinerTreeStructuredTM.Projections
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetSystemBounds
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.StructuredTM.ExactWrapper
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.StructuredTM.ProductSumChoice
import Mathlib.Tactic

/-!
Reusable direct standard-TM scans over weighted edge lists for the faithful
structured Steiner Tree verifier.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace SteinerTreeMembership

abbrev weightedEdgeListEncodedType : EncodedType :=
  weightedEdgeListStructuredEncodedType

/-! ### Weighted-edge Boolean primitives -/

def natEqBool (p : Nat × Nat) : Bool :=
  decide (p.1 = p.2)

@[simp] theorem natEqBool_eq_true_iff (p : Nat × Nat) :
    natEqBool p = true ↔ p.1 = p.2 := by
  simp [natEqBool]

theorem natEqBool_tm_polytime :
    TMPolyTimeMap (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.bool natEqBool := by
  simpa [natEqBool] using TMPolyTimeMap.nat_eq

def weightedEdgeEqBool (p : (Nat × Nat × Nat) × (Nat × Nat × Nat)) : Bool :=
  graphBoolAndPair
    (graphBoolAndPair (natEqBool (p.1.1, p.2.1), natEqBool (p.1.2.1, p.2.2.1)),
      natEqBool (p.1.2.2, p.2.2.2))

theorem weightedEdgeEqBool_eq_true_iff
    (p : (Nat × Nat × Nat) × (Nat × Nat × Nat)) :
    weightedEdgeEqBool p = true ↔ p.1 = p.2 := by
  rcases p with ⟨⟨a, b, c⟩, ⟨a', b', c'⟩⟩
  simp [weightedEdgeEqBool, graphBoolAndPair_eq_true_iff, natEqBool_eq_true_iff]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

theorem weightedEdgeEqBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod weightedEdgeStructuredEncodedType weightedEdgeStructuredEncodedType)
      EncodedType.bool
      weightedEdgeEqBool := by
  let X := EncodedType.prod weightedEdgeStructuredEncodedType weightedEdgeStructuredEncodedType
  have hLeft :
      TMPolyTimeMap X weightedEdgeStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst weightedEdgeStructuredEncodedType
      weightedEdgeStructuredEncodedType
  have hRight :
      TMPolyTimeMap X weightedEdgeStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd weightedEdgeStructuredEncodedType
      weightedEdgeStructuredEncodedType
  have hL0 : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hFst hLeft
    simpa [Function.comp, weightedEdgeStructuredEncodedType, X] using hComp
  have hLtail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hLeft
    simpa [Function.comp, weightedEdgeStructuredEncodedType, X] using hComp
  have hL1 : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hLtail
    simpa [Function.comp, X] using hComp
  have hL2 : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hLtail
    simpa [Function.comp, X] using hComp
  have hR0 : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hFst hRight
    simpa [Function.comp, weightedEdgeStructuredEncodedType, X] using hComp
  have hRtail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hRight
    simpa [Function.comp, weightedEdgeStructuredEncodedType, X] using hComp
  have hR1 : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hRtail
    simpa [Function.comp, X] using hComp
  have hR2 : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hRtail
    simpa [Function.comp, X] using hComp
  have hEq0Input : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => (p.1.1, p.2.1)) :=
    TMPolyTimeMap.prod_mk hL0 hR0
  have hEq1Input : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => (p.1.2.1, p.2.2.1)) :=
    TMPolyTimeMap.prod_mk hL1 hR1
  have hEq2Input : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => (p.1.2.2, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hL2 hR2
  have hEq0 : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => natEqBool (p.1.1, p.2.1)) := by
    have hComp := TMPolyTimeMap.comp natEqBool_tm_polytime hEq0Input
    simpa [Function.comp] using hComp
  have hEq1 : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => natEqBool (p.1.2.1, p.2.2.1)) := by
    have hComp := TMPolyTimeMap.comp natEqBool_tm_polytime hEq1Input
    simpa [Function.comp] using hComp
  have hEq2 : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => natEqBool (p.1.2.2, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp natEqBool_tm_polytime hEq2Input
    simpa [Function.comp] using hComp
  have hHeadInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier => (natEqBool (p.1.1, p.2.1), natEqBool (p.1.2.1, p.2.2.1))) :=
    TMPolyTimeMap.prod_mk hEq0 hEq1
  have hHead : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair (natEqBool (p.1.1, p.2.1), natEqBool (p.1.2.1, p.2.2.1))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hHeadInput
    simpa [Function.comp] using hComp
  have hAllInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier =>
        (graphBoolAndPair (natEqBool (p.1.1, p.2.1), natEqBool (p.1.2.1, p.2.2.1)),
          natEqBool (p.1.2.2, p.2.2.2))) :=
    TMPolyTimeMap.prod_mk hHead hEq2
  have hAll := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAllInput
  simpa [Function.comp, weightedEdgeEqBool, X] using hAll

def weightedEdgeHasEndpointBool (p : Nat × (Nat × Nat × Nat)) : Bool :=
  graphBoolOrPair (natEqBool (p.2.1, p.1), natEqBool (p.2.2.1, p.1))

theorem weightedEdgeHasEndpointBool_eq_true_iff
    (p : Nat × (Nat × Nat × Nat)) :
    weightedEdgeHasEndpointBool p = true ↔ WeightedEdgeHasEndpoint p.2 p.1 := by
  rcases p with ⟨v, ⟨u, w, wt⟩⟩
  simp [weightedEdgeHasEndpointBool, WeightedEdgeHasEndpoint, graphBoolOrPair_eq_true_iff]

theorem weightedEdgeHasEndpointBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat weightedEdgeStructuredEncodedType)
      EncodedType.bool
      weightedEdgeHasEndpointBool := by
  let X := EncodedType.prod EncodedType.nat weightedEdgeStructuredEncodedType
  have hVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.nat weightedEdgeStructuredEncodedType
  have hEdge : TMPolyTimeMap X weightedEdgeStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.nat weightedEdgeStructuredEncodedType
  have hLeft : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hFst hEdge
    simpa [Function.comp, weightedEdgeStructuredEncodedType, X] using hComp
  have hTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hEdge
    simpa [Function.comp, weightedEdgeStructuredEncodedType, X] using hComp
  have hRight : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hLeftInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => (p.2.1, p.1)) :=
    TMPolyTimeMap.prod_mk hLeft hVertex
  have hRightInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => (p.2.2.1, p.1)) :=
    TMPolyTimeMap.prod_mk hRight hVertex
  have hLeftEq : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => natEqBool (p.2.1, p.1)) := by
    have hComp := TMPolyTimeMap.comp natEqBool_tm_polytime hLeftInput
    simpa [Function.comp] using hComp
  have hRightEq : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => natEqBool (p.2.2.1, p.1)) := by
    have hComp := TMPolyTimeMap.comp natEqBool_tm_polytime hRightInput
    simpa [Function.comp] using hComp
  have hOrInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier => (natEqBool (p.2.1, p.1), natEqBool (p.2.2.1, p.1))) :=
    TMPolyTimeMap.prod_mk hLeftEq hRightEq
  have hOr := TMPolyTimeMap.comp graphBoolOrPair_tm_polytime hOrInput
  simpa [Function.comp, weightedEdgeHasEndpointBool, X] using hOr

def weightedEdgeTraversesBool
    (p : (Bool × (Nat × Nat × Nat)) × (Nat × Nat)) : Bool :=
  graphBoolOrPair
    (graphBoolAndPair (natEqBool (p.1.2.1, p.2.1), natEqBool (p.1.2.2.1, p.2.2)),
      graphBoolAndPair
        (Bool.not p.1.1,
          graphBoolAndPair (natEqBool (p.1.2.1, p.2.2), natEqBool (p.1.2.2.1, p.2.1))))

theorem weightedEdgeTraversesBool_eq_true_iff
    (p : (Bool × (Nat × Nat × Nat)) × (Nat × Nat)) :
    weightedEdgeTraversesBool p = true ↔
      WeightedEdgeTraverses p.1.1 p.1.2 p.2.1 p.2.2 := by
  rcases p with ⟨⟨directed, ⟨a, b, w⟩⟩, ⟨u, v⟩⟩
  cases directed <;> simp [weightedEdgeTraversesBool, WeightedEdgeTraverses,
    graphBoolAndPair_eq_true_iff, graphBoolOrPair_eq_true_iff]

theorem weightedEdgeTraversesBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod
        (EncodedType.prod EncodedType.bool weightedEdgeStructuredEncodedType)
        (EncodedType.prod EncodedType.nat EncodedType.nat))
      EncodedType.bool
      weightedEdgeTraversesBool := by
  let Pair := EncodedType.prod EncodedType.nat EncodedType.nat
  let Ctx := EncodedType.prod EncodedType.bool weightedEdgeStructuredEncodedType
  let X := EncodedType.prod Ctx Pair
  have hCtx : TMPolyTimeMap X Ctx (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst Ctx Pair
  have hPair : TMPolyTimeMap X Pair (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd Ctx Pair
  have hDirected : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool weightedEdgeStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hCtx
    simpa [Function.comp, Ctx, X] using hComp
  have hEdge : TMPolyTimeMap X weightedEdgeStructuredEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool weightedEdgeStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, Ctx, X] using hComp
  have hA : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat Pair
    have hComp := TMPolyTimeMap.comp hFst hEdge
    simpa [Function.comp, weightedEdgeStructuredEncodedType, Pair, X] using hComp
  have hTail : TMPolyTimeMap X Pair (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat Pair
    have hComp := TMPolyTimeMap.comp hSnd hEdge
    simpa [Function.comp, weightedEdgeStructuredEncodedType, Pair, X] using hComp
  have hB : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, Pair, X] using hComp
  have hU : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPair
    simpa [Function.comp, Pair, X] using hComp
  have hV : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPair
    simpa [Function.comp, Pair, X] using hComp
  have hAUInput : TMPolyTimeMap X Pair (fun p : X.Carrier => (p.1.2.1, p.2.1)) :=
    TMPolyTimeMap.prod_mk hA hU
  have hBVInput : TMPolyTimeMap X Pair (fun p : X.Carrier => (p.1.2.2.1, p.2.2)) :=
    TMPolyTimeMap.prod_mk hB hV
  have hAVInput : TMPolyTimeMap X Pair (fun p : X.Carrier => (p.1.2.1, p.2.2)) :=
    TMPolyTimeMap.prod_mk hA hV
  have hBUInput : TMPolyTimeMap X Pair (fun p : X.Carrier => (p.1.2.2.1, p.2.1)) :=
    TMPolyTimeMap.prod_mk hB hU
  have hAU : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => natEqBool (p.1.2.1, p.2.1)) := by
    have hComp := TMPolyTimeMap.comp natEqBool_tm_polytime hAUInput
    simpa [Function.comp, Pair] using hComp
  have hBV : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => natEqBool (p.1.2.2.1, p.2.2)) := by
    have hComp := TMPolyTimeMap.comp natEqBool_tm_polytime hBVInput
    simpa [Function.comp, Pair] using hComp
  have hAV : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => natEqBool (p.1.2.1, p.2.2)) := by
    have hComp := TMPolyTimeMap.comp natEqBool_tm_polytime hAVInput
    simpa [Function.comp, Pair] using hComp
  have hBU : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => natEqBool (p.1.2.2.1, p.2.1)) := by
    have hComp := TMPolyTimeMap.comp natEqBool_tm_polytime hBUInput
    simpa [Function.comp, Pair] using hComp
  have hForwardInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier => (natEqBool (p.1.2.1, p.2.1), natEqBool (p.1.2.2.1, p.2.2))) :=
    TMPolyTimeMap.prod_mk hAU hBV
  have hForward : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair (natEqBool (p.1.2.1, p.2.1), natEqBool (p.1.2.2.1, p.2.2))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hForwardInput
    simpa [Function.comp] using hComp
  have hNotDirected : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => Bool.not p.1.1) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.bool_not hDirected
    simpa [Function.comp] using hComp
  have hReverseEqInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier => (natEqBool (p.1.2.1, p.2.2), natEqBool (p.1.2.2.1, p.2.1))) :=
    TMPolyTimeMap.prod_mk hAV hBU
  have hReverseEq : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair (natEqBool (p.1.2.1, p.2.2), natEqBool (p.1.2.2.1, p.2.1))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hReverseEqInput
    simpa [Function.comp] using hComp
  have hReverseInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier =>
        (Bool.not p.1.1,
          graphBoolAndPair (natEqBool (p.1.2.1, p.2.2), natEqBool (p.1.2.2.1, p.2.1)))) :=
    TMPolyTimeMap.prod_mk hNotDirected hReverseEq
  have hReverse : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair
          (Bool.not p.1.1,
            graphBoolAndPair (natEqBool (p.1.2.1, p.2.2), natEqBool (p.1.2.2.1, p.2.1)))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hReverseInput
    simpa [Function.comp] using hComp
  have hAllInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier =>
        (graphBoolAndPair (natEqBool (p.1.2.1, p.2.1), natEqBool (p.1.2.2.1, p.2.2)),
          graphBoolAndPair
            (Bool.not p.1.1,
              graphBoolAndPair (natEqBool (p.1.2.1, p.2.2), natEqBool (p.1.2.2.1, p.2.1))))) :=
    TMPolyTimeMap.prod_mk hForward hReverse
  have hAll := TMPolyTimeMap.comp graphBoolOrPair_tm_polytime hAllInput
  simpa [Function.comp, weightedEdgeTraversesBool, X, Ctx, Pair] using hAll

theorem weightedEdgeWeight_tm_polytime :
    TMPolyTimeMap weightedEdgeStructuredEncodedType EncodedType.nat
      (fun e : Nat × Nat × Nat => e.2.2) := by
  let Pair := EncodedType.prod EncodedType.nat EncodedType.nat
  have hTail : TMPolyTimeMap weightedEdgeStructuredEncodedType Pair (fun e => e.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat Pair
    simpa [weightedEdgeStructuredEncodedType, Pair] using hSnd
  have hWeight : TMPolyTimeMap Pair EncodedType.nat (fun p : Nat × Nat => p.2) := by
    simpa [Pair] using TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hComp := TMPolyTimeMap.comp hWeight hTail
  simpa [Function.comp, Pair] using hComp

theorem weightedEdgeListWeight_tm_polytime :
    TMPolyTimeMap weightedEdgeListStructuredEncodedType EncodedType.nat
      WeightedEdgeListWeight := by
  have hWeights :=
    TMPolyTimeMap.list_map weightedEdgeWeight_tm_polytime
  have hSum := Partition.natListSum_tm_polytime
  have hComp := TMPolyTimeMap.comp hSum hWeights
  convert hComp using 1
  funext edges
  dsimp [WeightedEdgeListWeight, Function.comp]
  rw [Partition.natListSum_eq_sum]
  rfl

/-! ### Generic existential and universal scans over weighted edge lists -/

def weightedEdgeExistsInstructionEncodedType (C : EncodedType) : EncodedType :=
  EncodedType.sum C weightedEdgeStructuredEncodedType

def weightedEdgeExistsInstructionListEncodedType (C : EncodedType) : EncodedType :=
  EncodedType.list (weightedEdgeExistsInstructionEncodedType C)

def weightedEdgeExistsInputEncodedType (C : EncodedType) : EncodedType :=
  EncodedType.prod C weightedEdgeListStructuredEncodedType

def weightedEdgeExistsAccEncodedType (C : EncodedType) : EncodedType :=
  EncodedType.prod C EncodedType.bool

def weightedEdgeExistsInitInstruction {C : EncodedType}
    (ctx : C.Carrier) : (weightedEdgeExistsInstructionEncodedType C).Carrier :=
  Sum.inl ctx

def weightedEdgeExistsElementInstruction {C : EncodedType}
    (e : Nat × Nat × Nat) : (weightedEdgeExistsInstructionEncodedType C).Carrier :=
  Sum.inr e

def weightedEdgeExistsInstructions {C : EncodedType}
    (p : C.Carrier × List (Nat × Nat × Nat)) :
    List (weightedEdgeExistsInstructionEncodedType C).Carrier :=
  weightedEdgeExistsInitInstruction p.1 :: p.2.map weightedEdgeExistsElementInstruction

def weightedEdgeExistsRunnerInit {C : EncodedType} [Inhabited C.Carrier] :
    (weightedEdgeExistsAccEncodedType C).Carrier :=
  (default, false)

def weightedEdgeExistsStep {C : EncodedType}
    (pred : C.Carrier × (Nat × Nat × Nat) → Bool)
    (p : (weightedEdgeExistsAccEncodedType C).Carrier ×
      (weightedEdgeExistsInstructionEncodedType C).Carrier) :
    (weightedEdgeExistsAccEncodedType C).Carrier :=
  match p.2 with
  | Sum.inl ctx => (ctx, false)
  | Sum.inr e => (p.1.1, graphBoolOrPair (p.1.2, pred (p.1.1, e)))

def weightedEdgeExistsFromInstructions {C : EncodedType} [Inhabited C.Carrier]
    (pred : C.Carrier × (Nat × Nat × Nat) → Bool)
    (xs : List (weightedEdgeExistsInstructionEncodedType C).Carrier) : Bool :=
  (xs.foldl (fun acc instr => weightedEdgeExistsStep pred (acc, instr))
    weightedEdgeExistsRunnerInit).2

def weightedEdgeExistsBool {C : EncodedType} [Inhabited C.Carrier]
    (pred : C.Carrier × (Nat × Nat × Nat) → Bool)
    (p : C.Carrier × List (Nat × Nat × Nat)) : Bool :=
  weightedEdgeExistsFromInstructions pred (weightedEdgeExistsInstructions p)

theorem weightedEdgeExistsElementInstructions_fold_eq_true_iff
    {C : EncodedType} (pred : C.Carrier × (Nat × Nat × Nat) → Bool)
    (ctx : C.Carrier) (found : Bool) (edges : List (Nat × Nat × Nat)) :
    ((edges.map weightedEdgeExistsElementInstruction).foldl
        (fun acc instr => weightedEdgeExistsStep pred (acc, instr)) (ctx, found)).2 = true ↔
      found = true ∨ ∃ e ∈ edges, pred (ctx, e) = true := by
  induction edges generalizing found with
  | nil =>
      cases found <;> simp
  | cons e rest ih =>
      rw [List.map_cons, List.foldl_cons]
      change
        ((rest.map weightedEdgeExistsElementInstruction).foldl
            (fun acc instr => weightedEdgeExistsStep pred (acc, instr))
            (ctx, graphBoolOrPair (found, pred (ctx, e)))).2 = true ↔
          found = true ∨ ∃ x ∈ e :: rest, pred (ctx, x) = true
      rw [ih]
      constructor
      · intro h
        rcases h with hHead | hTail
        · rcases (graphBoolOrPair_eq_true_iff (found, pred (ctx, e))).1 hHead with
            hFound | hPred
          · exact Or.inl hFound
          · exact Or.inr ⟨e, by simp, hPred⟩
        · rcases hTail with ⟨x, hx, hxPred⟩
          exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hxPred⟩
      · intro h
        rcases h with hFound | h
        · left
          exact (graphBoolOrPair_eq_true_iff (found, pred (ctx, e))).2 (Or.inl hFound)
        · rcases h with ⟨x, hx, hxPred⟩
          rcases List.mem_cons.mp hx with hxHead | hxRest
          · left
            subst x
            exact (graphBoolOrPair_eq_true_iff (found, pred (ctx, e))).2 (Or.inr hxPred)
          · right
            exact ⟨x, hxRest, hxPred⟩

theorem weightedEdgeExistsBool_eq_true_iff
    {C : EncodedType} [Inhabited C.Carrier]
    (pred : C.Carrier × (Nat × Nat × Nat) → Bool)
    (p : C.Carrier × List (Nat × Nat × Nat)) :
    weightedEdgeExistsBool pred p = true ↔
      ∃ e ∈ p.2, pred (p.1, e) = true := by
  rcases p with ⟨ctx, edges⟩
  change
    (((weightedEdgeExistsInitInstruction ctx ::
          edges.map weightedEdgeExistsElementInstruction).foldl
        (fun acc instr => weightedEdgeExistsStep pred (acc, instr))
        weightedEdgeExistsRunnerInit).2 = true) ↔
      ∃ e ∈ edges, pred (ctx, e) = true
  rw [List.foldl_cons]
  simpa [weightedEdgeExistsRunnerInit, weightedEdgeExistsInitInstruction,
    weightedEdgeExistsStep] using
    weightedEdgeExistsElementInstructions_fold_eq_true_iff pred ctx false edges

theorem weightedEdgeExistsInitInstruction_tm_polytime (C : EncodedType) :
    TMPolyTimeMap C (weightedEdgeExistsInstructionEncodedType C)
      weightedEdgeExistsInitInstruction := by
  simpa [weightedEdgeExistsInitInstruction, weightedEdgeExistsInstructionEncodedType] using
    TMPolyTimeMap.inl C weightedEdgeStructuredEncodedType

theorem weightedEdgeExistsElementInstruction_tm_polytime (C : EncodedType) :
    TMPolyTimeMap weightedEdgeStructuredEncodedType (weightedEdgeExistsInstructionEncodedType C)
      weightedEdgeExistsElementInstruction := by
  simpa [weightedEdgeExistsElementInstruction, weightedEdgeExistsInstructionEncodedType] using
    TMPolyTimeMap.inr C weightedEdgeStructuredEncodedType

theorem weightedEdgeExistsInstructions_tm_polytime (C : EncodedType) :
    TMPolyTimeMap
      (weightedEdgeExistsInputEncodedType C)
      (weightedEdgeExistsInstructionListEncodedType C)
      weightedEdgeExistsInstructions := by
  let X := weightedEdgeExistsInputEncodedType C
  have hCtx : TMPolyTimeMap X C (fun p : X.Carrier => p.1) := by
    simpa [X, weightedEdgeExistsInputEncodedType] using
      TMPolyTimeMap.fst C weightedEdgeListStructuredEncodedType
  have hEdges :
      TMPolyTimeMap X weightedEdgeListStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, weightedEdgeExistsInputEncodedType] using
      TMPolyTimeMap.snd C weightedEdgeListStructuredEncodedType
  have hInit : TMPolyTimeMap X (weightedEdgeExistsInstructionEncodedType C)
      (fun p : X.Carrier => weightedEdgeExistsInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp (weightedEdgeExistsInitInstruction_tm_polytime C) hCtx
    simpa [Function.comp, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X (weightedEdgeExistsInstructionListEncodedType C)
        (fun p : X.Carrier => [weightedEdgeExistsInitInstruction p.1]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton (weightedEdgeExistsInstructionEncodedType C)) hInit
    simpa [Function.comp, weightedEdgeExistsInstructionListEncodedType, X] using hComp
  have hElements :
      TMPolyTimeMap X (weightedEdgeExistsInstructionListEncodedType C)
        (fun p : X.Carrier => p.2.map weightedEdgeExistsElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map (weightedEdgeExistsElementInstruction_tm_polytime C)
    have hComp := TMPolyTimeMap.comp hMap hEdges
    simpa [Function.comp, weightedEdgeExistsInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod (weightedEdgeExistsInstructionListEncodedType C)
          (weightedEdgeExistsInstructionListEncodedType C))
        (fun p : X.Carrier =>
          ([weightedEdgeExistsInitInstruction p.1],
            p.2.map weightedEdgeExistsElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hElements
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append (weightedEdgeExistsInstructionEncodedType C)) hAppendInput
  simpa [Function.comp, weightedEdgeExistsInstructions,
    weightedEdgeExistsInstructionListEncodedType, X] using hAppend

theorem weightedEdgeExistsStep_tm_polytime {C : EncodedType}
    {pred : C.Carrier × (Nat × Nat × Nat) → Bool}
    (hPred :
      TMPolyTimeMap
        (EncodedType.prod C weightedEdgeStructuredEncodedType)
        EncodedType.bool pred) :
    TMPolyTimeMap
      (EncodedType.prod
        (weightedEdgeExistsAccEncodedType C)
        (weightedEdgeExistsInstructionEncodedType C))
      (weightedEdgeExistsAccEncodedType C)
      (weightedEdgeExistsStep pred) := by
  let Instr := weightedEdgeExistsInstructionEncodedType C
  let A := weightedEdgeExistsAccEncodedType C
  let X := EncodedType.prod A Instr
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst A Instr
  have hInstr : TMPolyTimeMap X Instr (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd A Instr
  have hCtx : TMPolyTimeMap X C (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst C EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, weightedEdgeExistsAccEncodedType, X] using hComp
  have hFound : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd C EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, weightedEdgeExistsAccEncodedType, X] using hComp
  have hFalse : TMPolyTimeMap C A (fun ctx : C.Carrier => (ctx, false)) := by
    have hId := TMPolyTimeMap.id C
    have hConst : TMPolyTimeMap C EncodedType.bool (fun _ : C.Carrier => false) :=
      TMPolyTimeMap.const C EncodedType.bool false
    have hOut := TMPolyTimeMap.prod_mk hId hConst
    simpa [A, weightedEdgeExistsAccEncodedType] using hOut
  have hTrue : TMPolyTimeMap
      (EncodedType.prod A weightedEdgeStructuredEncodedType) A
      (fun p : A.Carrier × (Nat × Nat × Nat) =>
        (p.1.1, graphBoolOrPair (p.1.2, pred (p.1.1, p.2)))) := by
    let Y := EncodedType.prod A weightedEdgeStructuredEncodedType
    have hA : TMPolyTimeMap Y A (fun p : Y.Carrier => p.1) := by
      simpa [Y] using TMPolyTimeMap.fst A weightedEdgeStructuredEncodedType
    have hC : TMPolyTimeMap Y C (fun p : Y.Carrier => p.1.1) := by
      have hFst := TMPolyTimeMap.fst C EncodedType.bool
      have hComp := TMPolyTimeMap.comp hFst hA
      simpa [Function.comp, A, weightedEdgeExistsAccEncodedType, Y] using hComp
    have hB : TMPolyTimeMap Y EncodedType.bool (fun p : Y.Carrier => p.1.2) := by
      have hSnd := TMPolyTimeMap.snd C EncodedType.bool
      have hComp := TMPolyTimeMap.comp hSnd hA
      simpa [Function.comp, A, weightedEdgeExistsAccEncodedType, Y] using hComp
    have hE : TMPolyTimeMap Y weightedEdgeStructuredEncodedType (fun p : Y.Carrier => p.2) := by
      simpa [Y] using TMPolyTimeMap.snd A weightedEdgeStructuredEncodedType
    have hPInput :
        TMPolyTimeMap Y (EncodedType.prod C weightedEdgeStructuredEncodedType)
          (fun p : Y.Carrier => (p.1.1, p.2)) :=
      TMPolyTimeMap.prod_mk hC hE
    have hP : TMPolyTimeMap Y EncodedType.bool
        (fun p : Y.Carrier => pred (p.1.1, p.2)) := by
      have hComp := TMPolyTimeMap.comp hPred hPInput
      simpa [Function.comp] using hComp
    have hOI : TMPolyTimeMap Y (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : Y.Carrier => (p.1.2, pred (p.1.1, p.2))) :=
      TMPolyTimeMap.prod_mk hB hP
    have hO : TMPolyTimeMap Y EncodedType.bool
        (fun p : Y.Carrier => graphBoolOrPair (p.1.2, pred (p.1.1, p.2))) := by
      have hComp := TMPolyTimeMap.comp graphBoolOrPair_tm_polytime hOI
      simpa [Function.comp] using hComp
    have hOut := TMPolyTimeMap.prod_mk hC hO
    simpa [Y, A, weightedEdgeExistsAccEncodedType] using hOut
  have hStepSum :
      TMPolyTimeMap
        (EncodedType.prod A Instr)
        A
        (fun p : A.Carrier × Instr.Carrier =>
          match p.2 with
          | Sum.inl ctx => (ctx, false)
          | Sum.inr e => (p.1.1, graphBoolOrPair (p.1.2, pred (p.1.1, e)))) := by
    have hChoice := Partition.prodSumChoice_tm_polytime A C weightedEdgeStructuredEncodedType
    have hBranches := Partition.TMPolyTimeMap.sum_elim hFalse hTrue
    have hComp := TMPolyTimeMap.comp hBranches hChoice
    convert hComp using 1
    funext p
    rcases p with ⟨acc, instr⟩
    cases instr <;> rfl
  simpa [weightedEdgeExistsStep, A, Instr, X] using hStepSum

theorem weightedEdgeExistsStep_inputSize_le {C : EncodedType}
    (pred : C.Carrier × (Nat × Nat × Nat) → Bool)
    (K : Nat) (hK : 10 ≤ K)
    (source : (weightedEdgeExistsInstructionListEncodedType C).Carrier)
    (acc : (weightedEdgeExistsAccEncodedType C).Carrier)
    (instr : (weightedEdgeExistsInstructionEncodedType C).Carrier)
    (hAcc :
      (weightedEdgeExistsAccEncodedType C).inputSize acc ≤
        (weightedEdgeExistsInstructionListEncodedType C).inputSize source + K)
    (hInstr :
      (weightedEdgeExistsInstructionEncodedType C).inputSize instr ≤
        (weightedEdgeExistsInstructionListEncodedType C).inputSize source) :
    (weightedEdgeExistsAccEncodedType C).inputSize
        (weightedEdgeExistsStep pred (acc, instr)) ≤
      (weightedEdgeExistsInstructionListEncodedType C).inputSize source + K := by
  rcases acc with ⟨ctx, found⟩
  cases instr with
  | inl newCtx =>
      have hLocal :
          (weightedEdgeExistsAccEncodedType C).inputSize (newCtx, false) ≤
            (weightedEdgeExistsInstructionEncodedType C).inputSize (Sum.inl newCtx) + 10 := by
        simp [weightedEdgeExistsAccEncodedType, weightedEdgeExistsInstructionEncodedType,
          EncodedType.inputSize, EncodedType.prod, EncodedType.sum, EncodedType.bool]
      have hSource : (weightedEdgeExistsInstructionEncodedType C).inputSize (Sum.inl newCtx) + 10 ≤
          (weightedEdgeExistsInstructionListEncodedType C).inputSize source + K := by
        omega
      exact hLocal.trans hSource
  | inr e =>
      have hLocal :
          (weightedEdgeExistsAccEncodedType C).inputSize
              (ctx, graphBoolOrPair (found, pred (ctx, e))) ≤
            (weightedEdgeExistsAccEncodedType C).inputSize (ctx, found) := by
        cases found <;> cases pred (ctx, e) <;>
          simp [weightedEdgeExistsAccEncodedType, EncodedType.inputSize,
            EncodedType.prod, EncodedType.bool, graphBoolOrPair]
      exact hLocal.trans hAcc

theorem weightedEdgeExistsFold_tm_polytime {C : EncodedType} [Inhabited C.Carrier]
    {pred : C.Carrier × (Nat × Nat × Nat) → Bool}
    (hPred :
      TMPolyTimeMap
        (EncodedType.prod C weightedEdgeStructuredEncodedType)
        EncodedType.bool pred) :
    TMPolyTimeMap
      (weightedEdgeExistsInstructionListEncodedType C)
      (weightedEdgeExistsAccEncodedType C)
      (fun xs : (weightedEdgeExistsInstructionListEncodedType C).Carrier =>
        xs.foldl (fun acc instr => weightedEdgeExistsStep pred (acc, instr))
          weightedEdgeExistsRunnerInit) := by
  rcases weightedEdgeExistsStep_tm_polytime hPred with ⟨hStep⟩
  let K : Nat :=
    (weightedEdgeExistsAccEncodedType C).inputSize
      (weightedEdgeExistsRunnerInit : (weightedEdgeExistsAccEncodedType C).Carrier) + 10
  let bound : Polynomial Nat := Polynomial.X + Polynomial.C K
  refine
    TMPolyTimeMap.list_foldl_typed_bounded
      (weightedEdgeExistsInstructionEncodedType C)
      (weightedEdgeExistsAccEncodedType C)
      (weightedEdgeExistsStep pred) weightedEdgeExistsRunnerInit hStep bound ?_ ?_
  · intro xs
    change (weightedEdgeExistsAccEncodedType C).inputSize
        (weightedEdgeExistsRunnerInit : (weightedEdgeExistsAccEncodedType C).Carrier) ≤
      (Polynomial.X + Polynomial.C K).eval
        ((weightedEdgeExistsInstructionEncodedType C).list.inputSize xs)
    simp [Polynomial.eval_add]
    omega
  · intro source acc instr hAcc hInstr
    have hAcc' :
        (weightedEdgeExistsAccEncodedType C).inputSize acc ≤
          (weightedEdgeExistsInstructionListEncodedType C).inputSize source + K := by
      simpa [weightedEdgeExistsInstructionListEncodedType, bound, Polynomial.eval_add] using hAcc
    have hInstr' :
        (weightedEdgeExistsInstructionEncodedType C).inputSize instr ≤
          (weightedEdgeExistsInstructionListEncodedType C).inputSize source := by
      simpa [weightedEdgeExistsInstructionListEncodedType] using hInstr
    simpa [weightedEdgeExistsInstructionListEncodedType, bound, Polynomial.eval_add] using
      weightedEdgeExistsStep_inputSize_le pred K (by omega) source acc instr hAcc' hInstr'

theorem weightedEdgeExistsFromInstructions_tm_polytime
    {C : EncodedType} [Inhabited C.Carrier]
    {pred : C.Carrier × (Nat × Nat × Nat) → Bool}
    (hPred :
      TMPolyTimeMap
        (EncodedType.prod C weightedEdgeStructuredEncodedType)
        EncodedType.bool pred) :
    TMPolyTimeMap
      (weightedEdgeExistsInstructionListEncodedType C)
      EncodedType.bool
      (weightedEdgeExistsFromInstructions pred) := by
  have hFold := weightedEdgeExistsFold_tm_polytime hPred
  have hOut := TMPolyTimeMap.snd C EncodedType.bool
  have hComp := TMPolyTimeMap.comp hOut hFold
  simpa [Function.comp, weightedEdgeExistsFromInstructions, weightedEdgeExistsAccEncodedType]
    using hComp

theorem weightedEdgeExistsBool_tm_polytime
    {C : EncodedType} [Inhabited C.Carrier]
    {pred : C.Carrier × (Nat × Nat × Nat) → Bool}
    (hPred :
      TMPolyTimeMap
        (EncodedType.prod C weightedEdgeStructuredEncodedType)
        EncodedType.bool pred) :
    TMPolyTimeMap
      (weightedEdgeExistsInputEncodedType C)
      EncodedType.bool
      (weightedEdgeExistsBool pred) := by
  have hComp := TMPolyTimeMap.comp
    (weightedEdgeExistsFromInstructions_tm_polytime hPred)
    (weightedEdgeExistsInstructions_tm_polytime C)
  simpa [Function.comp, weightedEdgeExistsBool] using hComp

/-! ### Concrete scans used by the Steiner verifier -/

def weightedEdgeInListBool (p : (Nat × Nat × Nat) × List (Nat × Nat × Nat)) : Bool :=
  letI : Inhabited weightedEdgeStructuredEncodedType.Carrier := ⟨((0, 0, 0) : Nat × Nat × Nat)⟩
  weightedEdgeExistsBool (C := weightedEdgeStructuredEncodedType) weightedEdgeEqBool p

theorem weightedEdgeInListBool_eq_true_iff
    (p : (Nat × Nat × Nat) × List (Nat × Nat × Nat)) :
    weightedEdgeInListBool p = true ↔ p.1 ∈ p.2 := by
  letI : Inhabited weightedEdgeStructuredEncodedType.Carrier := ⟨((0, 0, 0) : Nat × Nat × Nat)⟩
  rw [weightedEdgeInListBool, weightedEdgeExistsBool_eq_true_iff]
  constructor
  · rintro ⟨e, he, hEq⟩
    exact (weightedEdgeEqBool_eq_true_iff (p.1, e)).1 hEq ▸ he
  · intro hp
    exact ⟨p.1, hp, (weightedEdgeEqBool_eq_true_iff (p.1, p.1)).2 rfl⟩

theorem weightedEdgeInListBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod weightedEdgeStructuredEncodedType weightedEdgeListStructuredEncodedType)
      EncodedType.bool
      weightedEdgeInListBool :=
  letI : Inhabited weightedEdgeStructuredEncodedType.Carrier := ⟨((0, 0, 0) : Nat × Nat × Nat)⟩
  weightedEdgeExistsBool_tm_polytime (C := weightedEdgeStructuredEncodedType)
    weightedEdgeEqBool_tm_polytime

def weightedEndpointInListBool (p : Nat × List (Nat × Nat × Nat)) : Bool :=
  letI : Inhabited EncodedType.nat.Carrier :=
    ⟨(show EncodedType.nat.Carrier from (0 : Nat))⟩
  weightedEdgeExistsBool (C := EncodedType.nat) weightedEdgeHasEndpointBool p

theorem weightedEndpointInListBool_eq_true_iff
    (p : Nat × List (Nat × Nat × Nat)) :
    weightedEndpointInListBool p = true ↔
      ∃ e ∈ p.2, WeightedEdgeHasEndpoint e p.1 := by
  letI : Inhabited EncodedType.nat.Carrier :=
    ⟨(show EncodedType.nat.Carrier from (0 : Nat))⟩
  rw [weightedEndpointInListBool, weightedEdgeExistsBool_eq_true_iff]
  constructor
  · rintro ⟨e, he, hEndpoint⟩
    exact ⟨e, he, (weightedEdgeHasEndpointBool_eq_true_iff (p.1, e)).1 hEndpoint⟩
  · rintro ⟨e, he, hEndpoint⟩
    exact ⟨e, he, (weightedEdgeHasEndpointBool_eq_true_iff (p.1, e)).2 hEndpoint⟩

theorem weightedEndpointInListBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat weightedEdgeListStructuredEncodedType)
      EncodedType.bool
      weightedEndpointInListBool :=
  letI : Inhabited EncodedType.nat.Carrier :=
    ⟨(show EncodedType.nat.Carrier from (0 : Nat))⟩
  weightedEdgeExistsBool_tm_polytime (C := EncodedType.nat)
    weightedEdgeHasEndpointBool_tm_polytime

def weightedAdjacentContextEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool (EncodedType.prod EncodedType.nat EncodedType.nat)

def weightedAdjacentPred
    (p : weightedAdjacentContextEncodedType.Carrier × (Nat × Nat × Nat)) : Bool :=
  weightedEdgeTraversesBool ((p.1.1, p.2), p.1.2)

theorem weightedAdjacentPred_eq_true_iff
    (p : weightedAdjacentContextEncodedType.Carrier × (Nat × Nat × Nat)) :
    weightedAdjacentPred p = true ↔
      WeightedEdgeTraverses p.1.1 p.2 p.1.2.1 p.1.2.2 := by
  simpa [weightedAdjacentPred] using
    weightedEdgeTraversesBool_eq_true_iff ((p.1.1, p.2), p.1.2)

theorem weightedAdjacentPred_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod weightedAdjacentContextEncodedType weightedEdgeStructuredEncodedType)
      EncodedType.bool
      weightedAdjacentPred := by
  let Pair := EncodedType.prod EncodedType.nat EncodedType.nat
  let C := weightedAdjacentContextEncodedType
  let X := EncodedType.prod C weightedEdgeStructuredEncodedType
  have hCtx : TMPolyTimeMap X C (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst C weightedEdgeStructuredEncodedType
  have hEdge : TMPolyTimeMap X weightedEdgeStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd C weightedEdgeStructuredEncodedType
  have hDirected : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool Pair
    have hComp := TMPolyTimeMap.comp hFst hCtx
    simpa [Function.comp, C, weightedAdjacentContextEncodedType, X] using hComp
  have hVertices : TMPolyTimeMap X Pair (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool Pair
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, C, weightedAdjacentContextEncodedType, X] using hComp
  have hDE :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool weightedEdgeStructuredEncodedType)
        (fun p : X.Carrier => (p.1.1, p.2)) :=
    TMPolyTimeMap.prod_mk hDirected hEdge
  have hInput :
      TMPolyTimeMap X
        (EncodedType.prod
          (EncodedType.prod EncodedType.bool weightedEdgeStructuredEncodedType)
          Pair)
        (fun p : X.Carrier => ((p.1.1, p.2), p.1.2)) :=
    TMPolyTimeMap.prod_mk hDE hVertices
  have hComp := TMPolyTimeMap.comp weightedEdgeTraversesBool_tm_polytime hInput
  simpa [Function.comp, weightedAdjacentPred, Pair, C, X] using hComp

def weightedAdjacentInputEncodedType : EncodedType :=
  EncodedType.prod
    (EncodedType.prod weightedEdgeListStructuredEncodedType EncodedType.bool)
    (EncodedType.prod EncodedType.nat EncodedType.nat)

def weightedAdjacentBool
    (p : (List (Nat × Nat × Nat) × Bool) × (Nat × Nat)) : Bool :=
  letI : Inhabited weightedAdjacentContextEncodedType.Carrier :=
    ⟨(show weightedAdjacentContextEncodedType.Carrier from (false, ((0 : Nat), (0 : Nat))))⟩
  weightedEdgeExistsBool (C := weightedAdjacentContextEncodedType)
    weightedAdjacentPred ((p.1.2, p.2), p.1.1)

theorem weightedAdjacentBool_eq_true_iff
    (p : (List (Nat × Nat × Nat) × Bool) × (Nat × Nat)) :
    weightedAdjacentBool p = true ↔
      WeightedAdjacent p.1.1 p.1.2 p.2.1 p.2.2 := by
  letI : Inhabited weightedAdjacentContextEncodedType.Carrier :=
    ⟨(show weightedAdjacentContextEncodedType.Carrier from (false, ((0 : Nat), (0 : Nat))))⟩
  rw [weightedAdjacentBool, weightedEdgeExistsBool_eq_true_iff]
  constructor
  · rintro ⟨e, he, hStep⟩
    exact ⟨e, he, (weightedAdjacentPred_eq_true_iff ((p.1.2, p.2), e)).1 hStep⟩
  · rintro ⟨e, he, hStep⟩
    exact ⟨e, he, (weightedAdjacentPred_eq_true_iff ((p.1.2, p.2), e)).2 hStep⟩

theorem weightedAdjacentBool_tm_polytime :
    TMPolyTimeMap weightedAdjacentInputEncodedType EncodedType.bool
      weightedAdjacentBool := by
  let C := weightedAdjacentContextEncodedType
  let X := weightedAdjacentInputEncodedType
  have hSource :
      TMPolyTimeMap X (EncodedType.prod weightedEdgeListStructuredEncodedType EncodedType.bool)
        (fun p : X.Carrier => p.1) := by
    simpa [X, weightedAdjacentInputEncodedType] using
      TMPolyTimeMap.fst
        (EncodedType.prod weightedEdgeListStructuredEncodedType EncodedType.bool)
        (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hPair :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => p.2) := by
    simpa [X, weightedAdjacentInputEncodedType] using
      TMPolyTimeMap.snd
        (EncodedType.prod weightedEdgeListStructuredEncodedType EncodedType.bool)
        (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hEdges :
      TMPolyTimeMap X weightedEdgeListStructuredEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst weightedEdgeListStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hSource
    simpa [Function.comp, X] using hComp
  have hDirected : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd weightedEdgeListStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hSource
    simpa [Function.comp, X] using hComp
  have hCtx : TMPolyTimeMap X C (fun p : X.Carrier => (p.1.2, p.2)) := by
    have hOut := TMPolyTimeMap.prod_mk hDirected hPair
    simpa [C, weightedAdjacentContextEncodedType] using hOut
  have hInput :
      TMPolyTimeMap X (weightedEdgeExistsInputEncodedType C)
        (fun p : X.Carrier => ((p.1.2, p.2), p.1.1)) :=
    TMPolyTimeMap.prod_mk hCtx hEdges
  letI : Inhabited weightedAdjacentContextEncodedType.Carrier :=
    ⟨(show weightedAdjacentContextEncodedType.Carrier from (false, ((0 : Nat), (0 : Nat))))⟩
  have hComp := TMPolyTimeMap.comp
    (weightedEdgeExistsBool_tm_polytime (C := weightedAdjacentContextEncodedType)
      weightedAdjacentPred_tm_polytime) hInput
  convert hComp using 1


end SteinerTreeMembership

end Karp21
end ComplexityReduction
