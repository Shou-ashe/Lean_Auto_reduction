/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.EdgeAssembly

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

/-! ### Executable cross-arc blocks for indexed incidences -/

def dhcCrossArcCandidateEncodedType : EncodedType :=
  EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType

def dhcCrossArcCandidateWithBudgetEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat dhcCrossArcCandidateEncodedType

def dhcCrossArcBitInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod dhcCrossArcCandidateEncodedType EncodedType.nat)

abbrev dhcCrossArcCandidateRaw :=
  ((Nat × Nat) × Nat) × ((Nat × Nat) × Nat)

abbrev dhcCrossArcCandidateWithBudgetRaw :=
  Nat × dhcCrossArcCandidateRaw

def dhcCrossArcLeftVertex (p : dhcCrossArcCandidateRaw) : Nat := p.1.1.1

def dhcCrossArcLeftEdgeIndex (p : dhcCrossArcCandidateRaw) : Nat := p.1.1.2

def dhcCrossArcLeftIncidenceIndex (p : dhcCrossArcCandidateRaw) : Nat := p.1.2

def dhcCrossArcRightVertex (p : dhcCrossArcCandidateRaw) : Nat := p.2.1.1

def dhcCrossArcRightEdgeIndex (p : dhcCrossArcCandidateRaw) : Nat := p.2.1.2

def dhcCrossArcRightIncidenceIndex (p : dhcCrossArcCandidateRaw) : Nat := p.2.2

def dhcCrossArcCandidateBool (p : dhcCrossArcCandidateRaw) : Bool :=
  graphBoolAndPair
    (decide (dhcCrossArcLeftEdgeIndex p = dhcCrossArcRightEdgeIndex p),
      Bool.not (decide (dhcCrossArcLeftVertex p = dhcCrossArcRightVertex p)))

theorem dhcCrossArcCandidateBool_eq_true_iff (p : dhcCrossArcCandidateRaw) :
    dhcCrossArcCandidateBool p = true ↔ p.1.1.2 = p.2.1.2 ∧ p.1.1.1 ≠ p.2.1.1 := by
  simp [dhcCrossArcCandidateBool, dhcCrossArcLeftEdgeIndex, dhcCrossArcRightEdgeIndex,
    dhcCrossArcLeftVertex, dhcCrossArcRightVertex, graphBoolAndPair_eq_true_iff]

theorem dhcCrossArcCandidateBool_tm_polytime :
    TMPolyTimeMap dhcCrossArcCandidateEncodedType EncodedType.bool
      dhcCrossArcCandidateBool := by
  let X := dhcCrossArcCandidateEncodedType
  have hLeft : TMPolyTimeMap X dhcIndexedIncidenceEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, dhcCrossArcCandidateEncodedType] using
      TMPolyTimeMap.fst dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType
  have hRight : TMPolyTimeMap X dhcIndexedIncidenceEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, dhcCrossArcCandidateEncodedType] using
      TMPolyTimeMap.snd dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType
  have hLeftPair : TMPolyTimeMap X vertexPairEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst vertexPairEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hLeft
    simpa [Function.comp, dhcIndexedIncidenceEncodedType, X] using hComp
  have hRightPair : TMPolyTimeMap X vertexPairEncodedType (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst vertexPairEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hRight
    simpa [Function.comp, dhcIndexedIncidenceEncodedType, X] using hComp
  have hLeftVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hLeftPair
    simpa [Function.comp, vertexPairEncodedType, X] using hComp
  have hLeftEdge : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hLeftPair
    simpa [Function.comp, vertexPairEncodedType, X] using hComp
  have hRightVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hRightPair
    simpa [Function.comp, vertexPairEncodedType, X] using hComp
  have hRightEdge : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hRightPair
    simpa [Function.comp, vertexPairEncodedType, X] using hComp
  have hEdgeEqInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier =>
          (dhcCrossArcLeftEdgeIndex p, dhcCrossArcRightEdgeIndex p)) := by
    simpa [dhcCrossArcLeftEdgeIndex, dhcCrossArcRightEdgeIndex] using
    TMPolyTimeMap.prod_mk hLeftEdge hRightEdge
  have hVertexEqInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier =>
          (dhcCrossArcLeftVertex p, dhcCrossArcRightVertex p)) := by
    simpa [dhcCrossArcLeftVertex, dhcCrossArcRightVertex] using
    TMPolyTimeMap.prod_mk hLeftVertex hRightVertex
  have hEdgeEq := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hEdgeEqInput
  have hVertexEq := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hVertexEqInput
  have hVertexNe :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier =>
          Bool.not (decide (dhcCrossArcLeftVertex p = dhcCrossArcRightVertex p))) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.bool_not hVertexEq
    simpa [Function.comp] using hComp
  have hBoth :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (decide (dhcCrossArcLeftEdgeIndex p = dhcCrossArcRightEdgeIndex p),
            Bool.not (decide (dhcCrossArcLeftVertex p = dhcCrossArcRightVertex p)))) :=
    TMPolyTimeMap.prod_mk hEdgeEq hVertexNe
  have hOut := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hBoth
  simpa [Function.comp, dhcCrossArcCandidateBool, X, dhcCrossArcCandidateEncodedType] using hOut

def dhcCrossArcFromIndexedBitRaw
    (budget : Nat) (candidate : dhcCrossArcCandidateRaw) (bit : Nat) : Nat × Nat :=
  (dhcIncidenceVertexCode (budget, (dhcCrossArcLeftIncidenceIndex candidate, bit)),
    dhcIncidenceVertexCode (budget, (dhcCrossArcRightIncidenceIndex candidate, bit)))

def dhcCrossArcFromIndexedBit
    (p : dhcCrossArcBitInputEncodedType.Carrier) : Nat × Nat :=
  dhcCrossArcFromIndexedBitRaw p.1 p.2.1 p.2.2

theorem dhcCrossArcFromIndexedBit_tm_polytime :
    TMPolyTimeMap dhcCrossArcBitInputEncodedType edgeStructuredEncodedType
      dhcCrossArcFromIndexedBit := by
  let X := dhcCrossArcBitInputEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcCrossArcBitInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod dhcCrossArcCandidateEncodedType EncodedType.nat)
  have hTail :
      TMPolyTimeMap X (EncodedType.prod dhcCrossArcCandidateEncodedType EncodedType.nat)
        (fun p : X.Carrier => p.2) := by
    simpa [X, dhcCrossArcBitInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod dhcCrossArcCandidateEncodedType EncodedType.nat)
  have hCandidate :
      TMPolyTimeMap X dhcCrossArcCandidateEncodedType (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst dhcCrossArcCandidateEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hBit : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd dhcCrossArcCandidateEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hLeftInc :
      TMPolyTimeMap X dhcIndexedIncidenceEncodedType (fun p : X.Carrier => p.2.1.1) := by
    have hFst := TMPolyTimeMap.fst dhcIndexedIncidenceEncodedType
      dhcIndexedIncidenceEncodedType
    have hComp := TMPolyTimeMap.comp hFst hCandidate
    simpa [Function.comp, dhcCrossArcCandidateEncodedType, X] using hComp
  have hRightInc :
      TMPolyTimeMap X dhcIndexedIncidenceEncodedType (fun p : X.Carrier => p.2.1.2) := by
    have hSnd := TMPolyTimeMap.snd dhcIndexedIncidenceEncodedType
      dhcIndexedIncidenceEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hCandidate
    simpa [Function.comp, dhcCrossArcCandidateEncodedType, X] using hComp
  have hLeftIdx : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1.1.2) := by
    have hSnd := TMPolyTimeMap.snd vertexPairEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hLeftInc
    simpa [Function.comp, dhcIndexedIncidenceEncodedType, X] using hComp
  have hRightIdx : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd vertexPairEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hRightInc
    simpa [Function.comp, dhcIndexedIncidenceEncodedType, X] using hComp
  have hLeftIdxBit :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.1.1.2, p.2.2)) :=
    TMPolyTimeMap.prod_mk hLeftIdx hBit
  have hRightIdxBit :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.1.2.2, p.2.2)) :=
    TMPolyTimeMap.prod_mk hRightIdx hBit
  have hLeftCodeInput :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat EncodedType.nat))
        (fun p : X.Carrier => (p.1, (p.2.1.1.2, p.2.2))) :=
    TMPolyTimeMap.prod_mk hBudget hLeftIdxBit
  have hRightCodeInput :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat EncodedType.nat))
        (fun p : X.Carrier => (p.1, (p.2.1.2.2, p.2.2))) :=
    TMPolyTimeMap.prod_mk hBudget hRightIdxBit
  have hLeftCode := TMPolyTimeMap.comp dhcIncidenceVertexCode_tm_polytime hLeftCodeInput
  have hRightCode := TMPolyTimeMap.comp dhcIncidenceVertexCode_tm_polytime hRightCodeInput
  have hOut := TMPolyTimeMap.prod_mk hLeftCode hRightCode
  simpa [Function.comp, dhcCrossArcFromIndexedBit, edgeStructuredEncodedType, X,
    dhcCrossArcBitInputEncodedType] using hOut

def dhcCrossArcPairBlock
    (p : dhcCrossArcCandidateWithBudgetRaw) : List (Nat × Nat) :=
  [ dhcCrossArcFromIndexedBitRaw p.1 p.2 0
  , dhcCrossArcFromIndexedBitRaw p.1 p.2 1
  ]

def dhcCrossArcBlockFromIndexed
    (p : dhcCrossArcCandidateWithBudgetRaw) : List (Nat × Nat) :=
  if dhcCrossArcCandidateBool p.2 then dhcCrossArcPairBlock p else []

theorem dhcCrossArcPairBlock_tm_polytime :
    TMPolyTimeMap dhcCrossArcCandidateWithBudgetEncodedType edgeListStructuredEncodedType
      dhcCrossArcPairBlock := by
  let X := dhcCrossArcCandidateWithBudgetEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcCrossArcCandidateWithBudgetEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat dhcCrossArcCandidateEncodedType
  have hCandidate :
      TMPolyTimeMap X dhcCrossArcCandidateEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, dhcCrossArcCandidateWithBudgetEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat dhcCrossArcCandidateEncodedType
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hOne : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (1 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (1 : Nat)
  have hCandidateZero :
      TMPolyTimeMap X (EncodedType.prod dhcCrossArcCandidateEncodedType EncodedType.nat)
        (fun p : X.Carrier => (p.2, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hCandidate hZero
  have hCandidateOne :
      TMPolyTimeMap X (EncodedType.prod dhcCrossArcCandidateEncodedType EncodedType.nat)
        (fun p : X.Carrier => (p.2, (1 : Nat))) :=
    TMPolyTimeMap.prod_mk hCandidate hOne
  have hBit0Input :
      TMPolyTimeMap X dhcCrossArcBitInputEncodedType
        (fun p : X.Carrier => (p.1, (p.2, (0 : Nat)))) :=
    TMPolyTimeMap.prod_mk hBudget hCandidateZero
  have hBit1Input :
      TMPolyTimeMap X dhcCrossArcBitInputEncodedType
        (fun p : X.Carrier => (p.1, (p.2, (1 : Nat)))) :=
    TMPolyTimeMap.prod_mk hBudget hCandidateOne
  have hArc0 : TMPolyTimeMap X edgeStructuredEncodedType
      (fun p : X.Carrier => dhcCrossArcFromIndexedBitRaw p.1 p.2 (0 : Nat)) := by
    have hComp := TMPolyTimeMap.comp dhcCrossArcFromIndexedBit_tm_polytime hBit0Input
    simpa [Function.comp, dhcCrossArcFromIndexedBit, X] using hComp
  have hArc1 : TMPolyTimeMap X edgeStructuredEncodedType
      (fun p : X.Carrier => dhcCrossArcFromIndexedBitRaw p.1 p.2 (1 : Nat)) := by
    have hComp := TMPolyTimeMap.comp dhcCrossArcFromIndexedBit_tm_polytime hBit1Input
    simpa [Function.comp, dhcCrossArcFromIndexedBit, X] using hComp
  have hSingleton1 :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier => [dhcCrossArcFromIndexedBitRaw p.1 p.2 (1 : Nat)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton edgeStructuredEncodedType) hArc1
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeStructuredEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier =>
          (dhcCrossArcFromIndexedBitRaw p.1 p.2 (0 : Nat),
            [dhcCrossArcFromIndexedBitRaw p.1 p.2 (1 : Nat)])) :=
    TMPolyTimeMap.prod_mk hArc0 hSingleton1
  have hOut := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons edgeStructuredEncodedType) hConsInput
  simpa [Function.comp, dhcCrossArcPairBlock, X,
    dhcCrossArcCandidateWithBudgetEncodedType] using hOut

theorem dhcCrossArcBlockFromIndexed_tm_polytime :
    TMPolyTimeMap dhcCrossArcCandidateWithBudgetEncodedType edgeListStructuredEncodedType
      dhcCrossArcBlockFromIndexed := by
  let X := dhcCrossArcCandidateWithBudgetEncodedType
  have hCandidate :
      TMPolyTimeMap X dhcCrossArcCandidateEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, dhcCrossArcCandidateWithBudgetEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat dhcCrossArcCandidateEncodedType
  have hPred :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => dhcCrossArcCandidateBool p.2) := by
    have hComp := TMPolyTimeMap.comp dhcCrossArcCandidateBool_tm_polytime hCandidate
    simpa [Function.comp, X] using hComp
  have hTagged :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (dhcCrossArcCandidateBool p.2, p)) :=
    TMPolyTimeMap.prod_mk hPred (TMPolyTimeMap.id X)
  have hFalse : TMPolyTimeMap X edgeListStructuredEncodedType
      (fun _ : X.Carrier => ([] : List (Nat × Nat))) :=
    TMPolyTimeMap.const X edgeListStructuredEncodedType []
  have hBranch :=
    graphBoolProduct_dispatch_tm_polytime X edgeListStructuredEncodedType
      (fFalse := fun _ : X.Carrier => ([] : List (Nat × Nat)))
      (fTrue := dhcCrossArcPairBlock) hFalse dhcCrossArcPairBlock_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranch hTagged
  convert hComp using 1
  funext p
  cases h : dhcCrossArcCandidateBool p.2 <;>
    simp [Function.comp, dhcCrossArcBlockFromIndexed, h]

/-! ### Row-level fold: one fixed left incidence against the indexed source list -/

def dhcCrossRowPayloadEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat dhcIndexedIncidenceEncodedType

def dhcCrossRowInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceListEncodedType)

def dhcCrossRowAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)

def dhcCrossRowInstructionEncodedType : EncodedType :=
  EncodedType.sum dhcCrossRowPayloadEncodedType dhcIndexedIncidenceEncodedType

def dhcCrossRowInstructionListEncodedType : EncodedType :=
  EncodedType.list dhcCrossRowInstructionEncodedType

abbrev dhcCrossRowInputRaw :=
  Nat × (((Nat × Nat) × Nat) × List ((Nat × Nat) × Nat))

def dhcCrossRowFoldInit : dhcCrossRowAccEncodedType.Carrier :=
  ((0 : Nat), ((((0 : Nat), (0 : Nat)), (0 : Nat)), ([] : List (Nat × Nat))))

def dhcCrossRowFoldLeftStep
    (payload : dhcCrossRowPayloadEncodedType.Carrier) :
    dhcCrossRowAccEncodedType.Carrier :=
  (payload.1, (payload.2, ([] : List (Nat × Nat))))

def dhcCrossRowFoldRightStep
    (p : dhcCrossRowAccEncodedType.Carrier × dhcIndexedIncidenceEncodedType.Carrier) :
    dhcCrossRowAccEncodedType.Carrier :=
  (p.1.1,
    (p.1.2.1,
      (show List (Nat × Nat) from p.1.2.2) ++
        dhcCrossArcBlockFromIndexed (p.1.1, (p.1.2.1, p.2))))

def dhcCrossRowFoldStep
    (p : dhcCrossRowAccEncodedType.Carrier ×
      dhcCrossRowInstructionEncodedType.Carrier) :
    dhcCrossRowAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl payload => dhcCrossRowFoldLeftStep payload
  | Sum.inr right => dhcCrossRowFoldRightStep (p.1, right)

def dhcCrossRowInstructions
    (p : dhcCrossRowInputRaw) :
    dhcCrossRowInstructionListEncodedType.Carrier :=
  Sum.inl (p.1, p.2.1) :: p.2.2.map Sum.inr

def dhcCrossRowFoldResult
    (instrs : dhcCrossRowInstructionListEncodedType.Carrier) :
    List (Nat × Nat) :=
  (instrs.foldl (fun acc instr => dhcCrossRowFoldStep (acc, instr))
    dhcCrossRowFoldInit).2.2

def dhcCrossRowArcsExecutable
    (p : dhcCrossRowInputRaw) : List (Nat × Nat) :=
  dhcCrossRowFoldResult (dhcCrossRowInstructions p)

def dhcCrossRowArcsFromIndexed
    (budget : Nat) (left : (Nat × Nat) × Nat) (xs : List ((Nat × Nat) × Nat)) :
    List (Nat × Nat) :=
  (xs.map fun right => dhcCrossArcBlockFromIndexed (budget, (left, right))).flatten

theorem dhcCrossRowFoldLeftStep_tm_polytime :
    TMPolyTimeMap dhcCrossRowPayloadEncodedType dhcCrossRowAccEncodedType
      dhcCrossRowFoldLeftStep := by
  let X := dhcCrossRowPayloadEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcCrossRowPayloadEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat dhcIndexedIncidenceEncodedType
  have hLeft : TMPolyTimeMap X dhcIndexedIncidenceEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, dhcCrossRowPayloadEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat dhcIndexedIncidenceEncodedType
  have hEmpty :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun _ : X.Carrier => ([] : List (Nat × Nat))) :=
    TMPolyTimeMap.const X edgeListStructuredEncodedType []
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier => (p.2, ([] : List (Nat × Nat)))) :=
    TMPolyTimeMap.prod_mk hLeft hEmpty
  have hOut := TMPolyTimeMap.prod_mk hBudget hTail
  simpa [dhcCrossRowFoldLeftStep, dhcCrossRowAccEncodedType, dhcCrossRowPayloadEncodedType,
    X] using hOut

theorem dhcCrossRowFoldRightStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod dhcCrossRowAccEncodedType dhcIndexedIncidenceEncodedType)
      dhcCrossRowAccEncodedType
      dhcCrossRowFoldRightStep := by
  let X := EncodedType.prod dhcCrossRowAccEncodedType dhcIndexedIncidenceEncodedType
  have hAcc : TMPolyTimeMap X dhcCrossRowAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst dhcCrossRowAccEncodedType dhcIndexedIncidenceEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, dhcCrossRowAccEncodedType, X] using hComp
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, dhcCrossRowAccEncodedType, X] using hComp
  have hLeft : TMPolyTimeMap X dhcIndexedIncidenceEncodedType (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hOutEdges : TMPolyTimeMap X edgeListStructuredEncodedType
      (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hRight : TMPolyTimeMap X dhcIndexedIncidenceEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd dhcCrossRowAccEncodedType dhcIndexedIncidenceEncodedType
  have hCandidate :
      TMPolyTimeMap X dhcCrossArcCandidateEncodedType
        (fun p : X.Carrier => (p.1.2.1, p.2)) :=
    TMPolyTimeMap.prod_mk hLeft hRight
  have hBlockInput :
      TMPolyTimeMap X dhcCrossArcCandidateWithBudgetEncodedType
        (fun p : X.Carrier => (p.1.1, (p.1.2.1, p.2))) :=
    TMPolyTimeMap.prod_mk hBudget hCandidate
  have hBlock :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier => dhcCrossArcBlockFromIndexed (p.1.1, (p.1.2.1, p.2))) := by
    have hComp := TMPolyTimeMap.comp dhcCrossArcBlockFromIndexed_tm_polytime hBlockInput
    simpa [Function.comp, dhcCrossArcCandidateWithBudgetEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier =>
          (p.1.2.2, dhcCrossArcBlockFromIndexed (p.1.1, (p.1.2.1, p.2)))) :=
    TMPolyTimeMap.prod_mk hOutEdges hBlock
  have hAppend :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier =>
          (show List (Nat × Nat) from p.1.2.2) ++
            dhcCrossArcBlockFromIndexed (p.1.1, (p.1.2.1, p.2))) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append edgeStructuredEncodedType) hAppendInput
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hOutTail :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier =>
          (p.1.2.1,
            (show List (Nat × Nat) from p.1.2.2) ++
              dhcCrossArcBlockFromIndexed (p.1.1, (p.1.2.1, p.2)))) :=
    TMPolyTimeMap.prod_mk hLeft hAppend
  have hOut := TMPolyTimeMap.prod_mk hBudget hOutTail
  simpa [dhcCrossRowFoldRightStep, dhcCrossRowAccEncodedType, X] using hOut

theorem dhcCrossRowFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod dhcCrossRowAccEncodedType dhcCrossRowInstructionEncodedType)
      dhcCrossRowAccEncodedType
      dhcCrossRowFoldStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      dhcCrossRowAccEncodedType dhcCrossRowPayloadEncodedType dhcIndexedIncidenceEncodedType
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim dhcCrossRowFoldLeftStep_tm_polytime
      dhcCrossRowFoldRightStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem dhcCrossRowInstructions_tm_polytime :
    TMPolyTimeMap dhcCrossRowInputEncodedType
      dhcCrossRowInstructionListEncodedType
      dhcCrossRowInstructions := by
  let X := dhcCrossRowInputEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcCrossRowInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceListEncodedType)
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceListEncodedType)
        (fun p : X.Carrier => p.2) := by
    simpa [X, dhcCrossRowInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceListEncodedType)
  have hLeft : TMPolyTimeMap X dhcIndexedIncidenceEncodedType (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst dhcIndexedIncidenceEncodedType
      dhcIndexedIncidenceListEncodedType
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hList : TMPolyTimeMap X dhcIndexedIncidenceListEncodedType
      (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd dhcIndexedIncidenceEncodedType
      dhcIndexedIncidenceListEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hPayload :
      TMPolyTimeMap X dhcCrossRowPayloadEncodedType
        (fun p : X.Carrier => (p.1, p.2.1)) :=
    TMPolyTimeMap.prod_mk hBudget hLeft
  have hInitInstr :
      TMPolyTimeMap X dhcCrossRowInstructionEncodedType
        (fun p : X.Carrier => Sum.inl (p.1, p.2.1)) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.inl dhcCrossRowPayloadEncodedType dhcIndexedIncidenceEncodedType)
      hPayload
    simpa [Function.comp, dhcCrossRowInstructionEncodedType, X] using hComp
  have hRightInstrs :
      TMPolyTimeMap X dhcCrossRowInstructionListEncodedType
        (fun p : X.Carrier => p.2.2.map Sum.inr) := by
    have hMap :=
      TMPolyTimeMap.list_map
        (TMPolyTimeMap.inr dhcCrossRowPayloadEncodedType dhcIndexedIncidenceEncodedType)
    have hComp := TMPolyTimeMap.comp hMap hList
    simpa [Function.comp, dhcIndexedIncidenceListEncodedType,
      dhcCrossRowInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod dhcCrossRowInstructionEncodedType
          dhcCrossRowInstructionListEncodedType)
        (fun p : X.Carrier =>
          (Sum.inl (p.1, p.2.1), p.2.2.map Sum.inr)) :=
    TMPolyTimeMap.prod_mk hInitInstr hRightInstrs
  have hOut :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons dhcCrossRowInstructionEncodedType)
      hConsInput
  simpa [Function.comp, dhcCrossRowInstructions, dhcCrossRowInstructionListEncodedType,
    X, dhcCrossRowInputEncodedType] using hOut

def dhcCrossRowFoldAccBound
    (N : Nat) (acc : dhcCrossRowAccEncodedType.Carrier) : Prop :=
  EncodedType.nat.inputSize acc.1 ≤ N + 1 ∧
    dhcIndexedIncidenceEncodedType.inputSize acc.2.1 ≤ N + 5

noncomputable def dhcCrossRowFoldGrowPolynomial : Polynomial Nat :=
  Polynomial.C 120 * Polynomial.X + Polynomial.C 200

theorem dhcCrossRowFoldGrowPolynomial_eval (N : Nat) :
    dhcCrossRowFoldGrowPolynomial.eval N = 120 * N + 200 := by
  simp [dhcCrossRowFoldGrowPolynomial, Polynomial.eval_add, Polynomial.eval_mul]

theorem dhcCrossArcBlock_inputSize_le
    (N budget : Nat) (left right : (Nat × Nat) × Nat)
    (hBudget : EncodedType.nat.inputSize budget ≤ N + 1)
    (hLeft : dhcIndexedIncidenceEncodedType.inputSize left ≤ N + 5)
    (hRight : dhcIndexedIncidenceEncodedType.inputSize right ≤ N + 5) :
    edgeListStructuredEncodedType.inputSize
        (dhcCrossArcBlockFromIndexed (budget, (left, right))) ≤
      120 * N + 200 := by
  rcases left with ⟨⟨u, i⟩, idx₁⟩
  rcases right with ⟨⟨v, j⟩, idx₂⟩
  change Nat at u
  change Nat at i
  change Nat at idx₁
  change Nat at v
  change Nat at j
  change Nat at idx₂
  have hBudgetNat : budget ≤ N := by
    simpa [EncodedType.inputSize_nat] using hBudget
  have hLeftIdxPayload :
      EncodedType.nat.inputSize idx₁ ≤
        dhcIndexedIncidenceEncodedType.inputSize (((u, i), idx₁)) := by
    simp [dhcIndexedIncidenceEncodedType, vertexPairEncodedType,
      EncodedType.inputSize_prod]
  have hRightIdxPayload :
      EncodedType.nat.inputSize idx₂ ≤
        dhcIndexedIncidenceEncodedType.inputSize (((v, j), idx₂)) := by
    simp [dhcIndexedIncidenceEncodedType, vertexPairEncodedType,
      EncodedType.inputSize_prod]
  have hLeftIdxNat : idx₁ ≤ N + 4 := by
    have h := hLeftIdxPayload.trans hLeft
    simpa [EncodedType.inputSize_nat] using h
  have hRightIdxNat : idx₂ ≤ N + 4 := by
    have h := hRightIdxPayload.trans hRight
    simpa [EncodedType.inputSize_nat] using h
  by_cases hKeep :
      dhcCrossArcCandidateBool ((((u, i), idx₁), ((v, j), idx₂)) : dhcCrossArcCandidateRaw) =
        true
  · simp [dhcCrossArcBlockFromIndexed, hKeep, dhcCrossArcPairBlock,
      dhcCrossArcFromIndexedBitRaw, dhcCrossArcLeftIncidenceIndex,
      dhcCrossArcRightIncidenceIndex, dhcIncidenceVertexCode, natDouble,
      edgeListStructuredEncodedType, edgeStructuredEncodedType, EncodedType.inputSize,
      EncodedType.list, EncodedType.prod, EncodedType.nat]
    nlinarith
  · have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
      exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
    simp [dhcCrossArcBlockFromIndexed, hKeep, hNil]

theorem dhcCrossRowFoldStep_growth
    (source : List dhcCrossRowInstructionEncodedType.Carrier)
    (acc : dhcCrossRowAccEncodedType.Carrier)
    (instr : dhcCrossRowInstructionEncodedType.Carrier)
    (hAcc :
      dhcCrossRowFoldAccBound
        (dhcCrossRowInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      dhcCrossRowInstructionEncodedType.inputSize instr ≤
        dhcCrossRowInstructionListEncodedType.inputSize source) :
    dhcCrossRowFoldAccBound
        (dhcCrossRowInstructionListEncodedType.inputSize source)
        (dhcCrossRowFoldStep (acc, instr)) ∧
      dhcCrossRowAccEncodedType.inputSize (dhcCrossRowFoldStep (acc, instr)) ≤
        dhcCrossRowAccEncodedType.inputSize acc +
          dhcCrossRowFoldGrowPolynomial.eval
            (dhcCrossRowInstructionListEncodedType.inputSize source) := by
  let N := dhcCrossRowInstructionListEncodedType.inputSize source
  cases instr with
  | inl payload =>
      rcases payload with ⟨budget, left⟩
      rcases left with ⟨ui, idx⟩
      rcases ui with ⟨u, i⟩
      change Nat at budget
      change Nat at u
      change Nat at i
      change Nat at idx
      have hPayloadInput :
          dhcCrossRowPayloadEncodedType.inputSize (budget, ((u, i), idx)) ≤ N := by
        have hTagged :
            dhcCrossRowPayloadEncodedType.inputSize (budget, ((u, i), idx)) + 1 ≤ N := by
          simpa [dhcCrossRowInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum, N, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInstr
        omega
      have hBudgetPayload :
          EncodedType.nat.inputSize budget ≤
            dhcCrossRowPayloadEncodedType.inputSize (budget, ((u, i), idx)) := by
        simp [dhcCrossRowPayloadEncodedType, EncodedType.inputSize_prod]
        omega
      have hLeftPayload :
          dhcIndexedIncidenceEncodedType.inputSize ((u, i), idx) ≤
            dhcCrossRowPayloadEncodedType.inputSize (budget, ((u, i), idx)) := by
        simp [dhcCrossRowPayloadEncodedType, EncodedType.inputSize_prod]
      have hBudget : EncodedType.nat.inputSize budget ≤ N + 1 :=
        (hBudgetPayload.trans hPayloadInput).trans (Nat.le_succ N)
      have hLeft : dhcIndexedIncidenceEncodedType.inputSize ((u, i), idx) ≤ N + 5 := by
        have h := (hLeftPayload.trans hPayloadInput).trans (Nat.le_succ N)
        omega
      constructor
      · exact ⟨hBudget, hLeft⟩
      · have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
          exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
        simp [dhcCrossRowFoldStep, dhcCrossRowFoldLeftStep, dhcCrossRowAccEncodedType,
          EncodedType.inputSize_prod, hNil, dhcCrossRowFoldGrowPolynomial_eval]
        have hBudgetNat : budget ≤ N := by
          simpa [EncodedType.inputSize_nat] using hBudget
        have hLeftNat :
            dhcIndexedIncidenceEncodedType.inputSize ((u, i), idx) ≤ N + 5 := hLeft
        omega
  | inr right =>
      rcases right with ⟨ui, idx⟩
      rcases ui with ⟨u, i⟩
      change Nat at u
      change Nat at i
      change Nat at idx
      have hBudget : EncodedType.nat.inputSize acc.1 ≤ N + 1 := by
        simpa [dhcCrossRowFoldAccBound, N] using hAcc.1
      have hLeft : dhcIndexedIncidenceEncodedType.inputSize acc.2.1 ≤ N + 5 := by
        simpa [dhcCrossRowFoldAccBound, N] using hAcc.2
      have hRightInput : dhcIndexedIncidenceEncodedType.inputSize ((u, i), idx) ≤ N := by
        have hTagged : dhcIndexedIncidenceEncodedType.inputSize ((u, i), idx) + 1 ≤ N := by
          simpa [dhcCrossRowInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum, N, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInstr
        omega
      have hRight : dhcIndexedIncidenceEncodedType.inputSize ((u, i), idx) ≤ N + 5 := by
        omega
      let out : List (Nat × Nat) := acc.2.2
      let block : List (Nat × Nat) :=
        dhcCrossArcBlockFromIndexed (acc.1, (acc.2.1, ((u, i), idx)))
      have hAppend :
          edgeListStructuredEncodedType.inputSize (out ++ block) =
            edgeListStructuredEncodedType.inputSize out +
              edgeListStructuredEncodedType.inputSize block := by
        simpa [edgeListStructuredEncodedType, block] using
          Clique.encodedList_inputSize_append edgeStructuredEncodedType out block
      constructor
      · exact ⟨hBudget, hLeft⟩
      · have hBlock :
            edgeListStructuredEncodedType.inputSize block ≤ 120 * N + 200 := by
          simpa [block] using
            dhcCrossArcBlock_inputSize_le N acc.1 acc.2.1 ((u, i), idx)
              hBudget hLeft hRight
        simp [dhcCrossRowFoldStep, dhcCrossRowFoldRightStep, dhcCrossRowAccEncodedType,
          EncodedType.inputSize_prod, dhcCrossRowFoldGrowPolynomial_eval]
        change
          (show Nat from acc.1) + 1 + 1 +
                (dhcIndexedIncidenceEncodedType.inputSize acc.2.1 + 1 +
                  edgeListStructuredEncodedType.inputSize (out ++ block)) ≤
            (show Nat from acc.1) + 1 + 1 +
                (dhcIndexedIncidenceEncodedType.inputSize acc.2.1 + 1 +
                  edgeListStructuredEncodedType.inputSize out) +
              (120 * dhcCrossRowInstructionListEncodedType.inputSize source + 200)
        rw [hAppend]
        omega

theorem dhcCrossRowFold_tm_polytime :
    TMPolyTimeMap
      dhcCrossRowInstructionListEncodedType
      dhcCrossRowAccEncodedType
      (fun xs : List dhcCrossRowInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => dhcCrossRowFoldStep (acc, instr))
          dhcCrossRowFoldInit) := by
  rcases dhcCrossRowFoldStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      dhcCrossRowInstructionEncodedType dhcCrossRowAccEncodedType
      dhcCrossRowFoldStep dhcCrossRowFoldInit hStep
      (Polynomial.C 20) dhcCrossRowFoldGrowPolynomial
      dhcCrossRowFoldAccBound ?_ ?_
  · intro xs
    constructor
    · constructor
      · simp [dhcCrossRowFoldInit, EncodedType.inputSize_nat]
      · simp [dhcCrossRowFoldInit, dhcIndexedIncidenceEncodedType, vertexPairEncodedType,
          EncodedType.inputSize_prod, EncodedType.inputSize_nat]
    · have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
        exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
      simp [dhcCrossRowFoldInit, dhcCrossRowAccEncodedType, dhcIndexedIncidenceEncodedType,
        vertexPairEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_nat, hNil]
  · intro source acc instr hAcc hInstr
    simpa [dhcCrossRowInstructionListEncodedType] using
      dhcCrossRowFoldStep_growth source acc instr hAcc hInstr

theorem dhcCrossRowFoldResult_tm_polytime :
    TMPolyTimeMap
      dhcCrossRowInstructionListEncodedType
      edgeListStructuredEncodedType
      dhcCrossRowFoldResult := by
  have hTail := TMPolyTimeMap.snd dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType
  have hAccTail :
      TMPolyTimeMap dhcCrossRowAccEncodedType
        (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
        (fun acc : dhcCrossRowAccEncodedType.Carrier => acc.2) := by
    simpa [dhcCrossRowAccEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
  have hEdges :
      TMPolyTimeMap dhcCrossRowAccEncodedType edgeListStructuredEncodedType
        (fun acc : dhcCrossRowAccEncodedType.Carrier => acc.2.2) := by
    have hComp := TMPolyTimeMap.comp hTail hAccTail
    simpa [Function.comp] using hComp
  have hComp := TMPolyTimeMap.comp hEdges dhcCrossRowFold_tm_polytime
  simpa [Function.comp, dhcCrossRowFoldResult] using hComp

theorem dhcCrossRowArcsExecutable_tm_polytime :
    TMPolyTimeMap dhcCrossRowInputEncodedType edgeListStructuredEncodedType
      dhcCrossRowArcsExecutable := by
  have hComp :=
    TMPolyTimeMap.comp dhcCrossRowFoldResult_tm_polytime
      dhcCrossRowInstructions_tm_polytime
  simpa [Function.comp, dhcCrossRowArcsExecutable] using hComp

theorem dhcCrossRowFold_map_invariant
    (budget : Nat) (left : (Nat × Nat) × Nat) (xs : List ((Nat × Nat) × Nat))
    (out : List (Nat × Nat)) :
    (xs.map Sum.inr).foldl
        (fun acc instr => dhcCrossRowFoldStep (acc, instr))
        (budget, (left, out)) =
      (budget, (left, out ++ dhcCrossRowArcsFromIndexed budget left xs)) := by
  induction xs generalizing out with
  | nil =>
      change (budget, (left, out)) =
        (budget, (left, out ++ ([] : List (Nat × Nat))))
      simp
  | cons right xs ih =>
      change
        (xs.map Sum.inr).foldl
            (fun acc instr => dhcCrossRowFoldStep (acc, instr))
            (dhcCrossRowFoldStep ((budget, (left, out)), Sum.inr right)) =
          (budget,
            (left,
              out ++
                (dhcCrossArcBlockFromIndexed (budget, (left, right)) ::
                  xs.map fun right => dhcCrossArcBlockFromIndexed (budget, (left, right))).flatten))
      rw [show dhcCrossRowFoldStep ((budget, (left, out)), Sum.inr right) =
          (budget,
            (left, out ++ dhcCrossArcBlockFromIndexed (budget, (left, right)))) by
        rfl]
      calc
        (xs.map Sum.inr).foldl
            (fun acc instr => dhcCrossRowFoldStep (acc, instr))
            (budget,
              (left, out ++ dhcCrossArcBlockFromIndexed (budget, (left, right))))
            =
          (budget,
            (left,
              (out ++ dhcCrossArcBlockFromIndexed (budget, (left, right))) ++
                dhcCrossRowArcsFromIndexed budget left xs)) :=
            ih (out ++ dhcCrossArcBlockFromIndexed (budget, (left, right)))
        _ =
          (budget,
            (left,
              out ++
                (dhcCrossArcBlockFromIndexed (budget, (left, right)) ::
                  xs.map fun right => dhcCrossArcBlockFromIndexed (budget, (left, right))).flatten)) := by
            simp [dhcCrossRowArcsFromIndexed, List.append_assoc]

theorem dhcCrossRowArcsExecutable_eq
    (p : dhcCrossRowInputRaw) :
    dhcCrossRowArcsExecutable p =
      dhcCrossRowArcsFromIndexed p.1 p.2.1 p.2.2 := by
  rcases p with ⟨budget, left, xs⟩
  rw [dhcCrossRowArcsExecutable, dhcCrossRowFoldResult, dhcCrossRowInstructions]
  rw [List.foldl_cons]
  rw [show
      dhcCrossRowFoldStep (dhcCrossRowFoldInit, Sum.inl (budget, left)) =
        (budget, (left, ([] : List (Nat × Nat)))) by
    rfl]
  change
    (List.foldl (fun acc instr => dhcCrossRowFoldStep (acc, instr))
      (budget, (left, [])) (List.map Sum.inr xs)).2.2 =
      dhcCrossRowArcsFromIndexed budget left xs
  have hFold :=
    congrArg (fun acc : dhcCrossRowAccEncodedType.Carrier => acc.2.2)
      (dhcCrossRowFold_map_invariant budget left xs ([] : List (Nat × Nat)))
  simpa using hFold

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
