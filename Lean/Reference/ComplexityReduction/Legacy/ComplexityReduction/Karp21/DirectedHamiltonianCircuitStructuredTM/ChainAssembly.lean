/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.CrossAssemblyOuter

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

/-! ### Executable adjacent-chain arcs for indexed incidences -/

def dhcChainArcCandidateEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool
    (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType)

def dhcChainArcCandidateWithBudgetEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat dhcChainArcCandidateEncodedType

abbrev dhcChainArcCandidateRaw :=
  Bool × (((Nat × Nat) × Nat) × ((Nat × Nat) × Nat))

abbrev dhcChainArcCandidateWithBudgetRaw :=
  Nat × dhcChainArcCandidateRaw

def dhcChainArcLeftVertex (p : dhcChainArcCandidateRaw) : Nat := p.2.1.1.1

def dhcChainArcRightVertex (p : dhcChainArcCandidateRaw) : Nat := p.2.2.1.1

def dhcChainArcCandidateBool (p : dhcChainArcCandidateRaw) : Bool :=
  graphBoolAndPair (p.1, decide (dhcChainArcLeftVertex p = dhcChainArcRightVertex p))

theorem dhcChainArcCandidateBool_eq_true_iff (p : dhcChainArcCandidateRaw) :
    dhcChainArcCandidateBool p = true ↔ p.1 = true ∧ p.2.1.1.1 = p.2.2.1.1 := by
  simp [dhcChainArcCandidateBool, dhcChainArcLeftVertex, dhcChainArcRightVertex,
    graphBoolAndPair_eq_true_iff]

theorem dhcChainArcCandidateBool_tm_polytime :
    TMPolyTimeMap dhcChainArcCandidateEncodedType EncodedType.bool
      dhcChainArcCandidateBool := by
  let X := dhcChainArcCandidateEncodedType
  have hFlag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1) := by
    simpa [X, dhcChainArcCandidateEncodedType] using
      TMPolyTimeMap.fst EncodedType.bool
        (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType)
  have hPair :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType)
        (fun p : X.Carrier => p.2) := by
    simpa [X, dhcChainArcCandidateEncodedType] using
      TMPolyTimeMap.snd EncodedType.bool
        (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType)
  have hLeft : TMPolyTimeMap X dhcIndexedIncidenceEncodedType (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPair
    simpa [Function.comp, X] using hComp
  have hRight : TMPolyTimeMap X dhcIndexedIncidenceEncodedType (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPair
    simpa [Function.comp, X] using hComp
  have hLeftVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1.1.1) := by
    have hFst := TMPolyTimeMap.fst vertexPairEncodedType EncodedType.nat
    have hLeftPair := TMPolyTimeMap.comp hFst hLeft
    have hVertexFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hVertexFst hLeftPair
    simpa [Function.comp, dhcIndexedIncidenceEncodedType, vertexPairEncodedType, X] using hComp
  have hRightVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.1.1) := by
    have hFst := TMPolyTimeMap.fst vertexPairEncodedType EncodedType.nat
    have hRightPair := TMPolyTimeMap.comp hFst hRight
    have hVertexFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hVertexFst hRightPair
    simpa [Function.comp, dhcIndexedIncidenceEncodedType, vertexPairEncodedType, X] using hComp
  have hEqInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (dhcChainArcLeftVertex p, dhcChainArcRightVertex p)) := by
    simpa [dhcChainArcLeftVertex, dhcChainArcRightVertex] using
      TMPolyTimeMap.prod_mk hLeftVertex hRightVertex
  have hEq := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hEqInput
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (p.1, decide (dhcChainArcLeftVertex p = dhcChainArcRightVertex p))) :=
    TMPolyTimeMap.prod_mk hFlag hEq
  have hOut := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
  simpa [Function.comp, dhcChainArcCandidateBool, X, dhcChainArcCandidateEncodedType] using hOut

def dhcChainArcFromIndexedRaw
    (budget : Nat) (left right : (Nat × Nat) × Nat) : Nat × Nat :=
  (dhcIncidenceVertexCode (budget, (left.2, (1 : Nat))),
    dhcIncidenceVertexCode (budget, (right.2, (0 : Nat))))

def dhcChainArcPairBlock
    (p : dhcChainArcCandidateWithBudgetRaw) : List (Nat × Nat) :=
  [dhcChainArcFromIndexedRaw p.1 p.2.2.1 p.2.2.2]

def dhcChainArcBlockFromIndexed
    (p : dhcChainArcCandidateWithBudgetRaw) : List (Nat × Nat) :=
  if dhcChainArcCandidateBool p.2 then dhcChainArcPairBlock p else []

def dhcChainArcInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType)

def dhcChainArcFromIndexed
    (p : dhcChainArcInputEncodedType.Carrier) : Nat × Nat :=
  dhcChainArcFromIndexedRaw p.1 p.2.1 p.2.2

theorem dhcChainArcFromIndexed_tm_polytime :
    TMPolyTimeMap dhcChainArcInputEncodedType edgeStructuredEncodedType
      dhcChainArcFromIndexed := by
  let X := dhcChainArcInputEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcChainArcInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType)
  have hPair :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType)
        (fun p : X.Carrier => p.2) := by
    simpa [X, dhcChainArcInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType)
  have hLeft : TMPolyTimeMap X dhcIndexedIncidenceEncodedType (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPair
    simpa [Function.comp, X] using hComp
  have hRight : TMPolyTimeMap X dhcIndexedIncidenceEncodedType (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPair
    simpa [Function.comp, X] using hComp
  have hLeftIdx : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1.2) := by
    have hSnd := TMPolyTimeMap.snd vertexPairEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hLeft
    simpa [Function.comp, dhcIndexedIncidenceEncodedType, X] using hComp
  have hRightIdx : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd vertexPairEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hRight
    simpa [Function.comp, dhcIndexedIncidenceEncodedType, X] using hComp
  have hOne : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (1 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (1 : Nat)
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hLeftIdxBit :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.1.2, (1 : Nat))) :=
    TMPolyTimeMap.prod_mk hLeftIdx hOne
  have hRightIdxBit :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.2.2, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hRightIdx hZero
  have hLeftCodeInput :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat EncodedType.nat))
        (fun p : X.Carrier => (p.1, (p.2.1.2, (1 : Nat)))) :=
    TMPolyTimeMap.prod_mk hBudget hLeftIdxBit
  have hRightCodeInput :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat EncodedType.nat))
        (fun p : X.Carrier => (p.1, (p.2.2.2, (0 : Nat)))) :=
    TMPolyTimeMap.prod_mk hBudget hRightIdxBit
  have hLeftCode := TMPolyTimeMap.comp dhcIncidenceVertexCode_tm_polytime hLeftCodeInput
  have hRightCode := TMPolyTimeMap.comp dhcIncidenceVertexCode_tm_polytime hRightCodeInput
  have hOut := TMPolyTimeMap.prod_mk hLeftCode hRightCode
  simpa [Function.comp, dhcChainArcFromIndexed, dhcChainArcFromIndexedRaw,
    edgeStructuredEncodedType, X, dhcChainArcInputEncodedType] using hOut

theorem dhcChainArcPairBlock_tm_polytime :
    TMPolyTimeMap dhcChainArcCandidateWithBudgetEncodedType edgeListStructuredEncodedType
      dhcChainArcPairBlock := by
  let X := dhcChainArcCandidateWithBudgetEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcChainArcCandidateWithBudgetEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat dhcChainArcCandidateEncodedType
  have hCandidate :
      TMPolyTimeMap X dhcChainArcCandidateEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, dhcChainArcCandidateWithBudgetEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat dhcChainArcCandidateEncodedType
  have hPair :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType)
        (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool
      (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hCandidate
    simpa [Function.comp, dhcChainArcCandidateEncodedType, X] using hComp
  have hArcInput :
      TMPolyTimeMap X dhcChainArcInputEncodedType
        (fun p : X.Carrier => (p.1, p.2.2)) :=
    TMPolyTimeMap.prod_mk hBudget hPair
  have hArc :
      TMPolyTimeMap X edgeStructuredEncodedType
        (fun p : X.Carrier => dhcChainArcFromIndexedRaw p.1 p.2.2.1 p.2.2.2) := by
    have hComp := TMPolyTimeMap.comp dhcChainArcFromIndexed_tm_polytime hArcInput
    simpa [Function.comp, dhcChainArcFromIndexed, X, dhcChainArcInputEncodedType] using hComp
  have hSingleton := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_singleton edgeStructuredEncodedType) hArc
  simpa [Function.comp, dhcChainArcPairBlock, edgeListStructuredEncodedType, X,
    dhcChainArcCandidateWithBudgetEncodedType] using hSingleton

theorem dhcChainArcBlockFromIndexed_tm_polytime :
    TMPolyTimeMap dhcChainArcCandidateWithBudgetEncodedType edgeListStructuredEncodedType
      dhcChainArcBlockFromIndexed := by
  let X := dhcChainArcCandidateWithBudgetEncodedType
  have hCandidate :
      TMPolyTimeMap X dhcChainArcCandidateEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, dhcChainArcCandidateWithBudgetEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat dhcChainArcCandidateEncodedType
  have hPred :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => dhcChainArcCandidateBool p.2) := by
    have hComp := TMPolyTimeMap.comp dhcChainArcCandidateBool_tm_polytime hCandidate
    simpa [Function.comp, X] using hComp
  have hTagged :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (dhcChainArcCandidateBool p.2, p)) :=
    TMPolyTimeMap.prod_mk hPred (TMPolyTimeMap.id X)
  have hFalse : TMPolyTimeMap X edgeListStructuredEncodedType
      (fun _ : X.Carrier => ([] : List (Nat × Nat))) :=
    TMPolyTimeMap.const X edgeListStructuredEncodedType []
  have hBranch :=
    graphBoolProduct_dispatch_tm_polytime X edgeListStructuredEncodedType
      (fFalse := fun _ : X.Carrier => ([] : List (Nat × Nat)))
      (fTrue := dhcChainArcPairBlock) hFalse dhcChainArcPairBlock_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranch hTagged
  convert hComp using 1
  funext p
  cases h : dhcChainArcCandidateBool p.2 <;>
    simp [Function.comp, dhcChainArcBlockFromIndexed, h]

/-! ### One-pass fold over the indexed source list -/

def dhcChainArcsAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.bool
      (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType))

def dhcChainArcsInstructionEncodedType : EncodedType :=
  EncodedType.sum EncodedType.nat dhcIndexedIncidenceEncodedType

def dhcChainArcsInstructionListEncodedType : EncodedType :=
  EncodedType.list dhcChainArcsInstructionEncodedType

def dhcChainDummyIncidence : ((Nat × Nat) × Nat) :=
  (((0 : Nat), (0 : Nat)), (0 : Nat))

def dhcChainArcsFoldInit : dhcChainArcsAccEncodedType.Carrier :=
  ((0 : Nat), (false, (dhcChainDummyIncidence, ([] : List (Nat × Nat)))))

def dhcChainArcsFoldLeftStep (budget : Nat) :
    dhcChainArcsAccEncodedType.Carrier :=
  (budget, (false, (dhcChainDummyIncidence, ([] : List (Nat × Nat)))))

def dhcChainArcsFoldRightStep
    (p : dhcChainArcsAccEncodedType.Carrier × dhcIndexedIncidenceEncodedType.Carrier) :
    dhcChainArcsAccEncodedType.Carrier :=
  (p.1.1,
    (true,
      (p.2,
        (show List (Nat × Nat) from p.1.2.2.2) ++
          dhcChainArcBlockFromIndexed (p.1.1, (p.1.2.1, (p.1.2.2.1, p.2))))))

def dhcChainArcsFoldStep
    (p : dhcChainArcsAccEncodedType.Carrier ×
      dhcChainArcsInstructionEncodedType.Carrier) :
    dhcChainArcsAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl budget => dhcChainArcsFoldLeftStep budget
  | Sum.inr inc => dhcChainArcsFoldRightStep (p.1, inc)

def dhcChainArcsInstructions
    (p : dhcIndexedIncidenceListWithBudgetRaw) :
    dhcChainArcsInstructionListEncodedType.Carrier :=
  Sum.inl p.1 :: p.2.map Sum.inr

def dhcChainArcsFoldResult
    (instrs : dhcChainArcsInstructionListEncodedType.Carrier) :
    List (Nat × Nat) :=
  (instrs.foldl (fun acc instr => dhcChainArcsFoldStep (acc, instr))
    dhcChainArcsFoldInit).2.2.2

def dhcChainArcsExecutableFromIndexed
    (p : dhcIndexedIncidenceListWithBudgetRaw) : List (Nat × Nat) :=
  dhcChainArcsFoldResult (dhcChainArcsInstructions p)

theorem dhcChainArcsFoldLeftStep_tm_polytime :
    TMPolyTimeMap EncodedType.nat dhcChainArcsAccEncodedType
      dhcChainArcsFoldLeftStep := by
  let X := EncodedType.nat
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p) :=
    TMPolyTimeMap.id X
  have hFalse : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hDummy :
      TMPolyTimeMap X dhcIndexedIncidenceEncodedType
        (fun _ : X.Carrier => dhcChainDummyIncidence) :=
    TMPolyTimeMap.const X dhcIndexedIncidenceEncodedType dhcChainDummyIncidence
  have hEmpty :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun _ : X.Carrier => ([] : List (Nat × Nat))) :=
    TMPolyTimeMap.const X edgeListStructuredEncodedType []
  have hInner :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
        (fun _ : X.Carrier => (dhcChainDummyIncidence, ([] : List (Nat × Nat)))) :=
    TMPolyTimeMap.prod_mk hDummy hEmpty
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType))
        (fun _ : X.Carrier =>
          (false, (dhcChainDummyIncidence, ([] : List (Nat × Nat))))) :=
    TMPolyTimeMap.prod_mk hFalse hInner
  have hOut := TMPolyTimeMap.prod_mk hBudget hTail
  simpa [dhcChainArcsFoldLeftStep, dhcChainArcsAccEncodedType, X] using hOut

theorem dhcChainArcsFoldRightStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod dhcChainArcsAccEncodedType dhcIndexedIncidenceEncodedType)
      dhcChainArcsAccEncodedType
      dhcChainArcsFoldRightStep := by
  let X := EncodedType.prod dhcChainArcsAccEncodedType dhcIndexedIncidenceEncodedType
  have hAcc : TMPolyTimeMap X dhcChainArcsAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst dhcChainArcsAccEncodedType
      dhcIndexedIncidenceEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.bool
        (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType))
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, dhcChainArcsAccEncodedType, X] using hComp
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType))
        (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.bool
        (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType))
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, dhcChainArcsAccEncodedType, X] using hComp
  have hActive : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool
      (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hInner :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool
      (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hPrev :
      TMPolyTimeMap X dhcIndexedIncidenceEncodedType (fun p : X.Carrier => p.1.2.2.1) := by
    have hFst := TMPolyTimeMap.fst dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInner
    simpa [Function.comp, X] using hComp
  have hOutEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.1.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInner
    simpa [Function.comp, X] using hComp
  have hCurrent :
      TMPolyTimeMap X dhcIndexedIncidenceEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd dhcChainArcsAccEncodedType
      dhcIndexedIncidenceEncodedType
  have hPair :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType)
        (fun p : X.Carrier => (p.1.2.2.1, p.2)) :=
    TMPolyTimeMap.prod_mk hPrev hCurrent
  have hCandidate :
      TMPolyTimeMap X dhcChainArcCandidateEncodedType
        (fun p : X.Carrier => (p.1.2.1, (p.1.2.2.1, p.2))) :=
    TMPolyTimeMap.prod_mk hActive hPair
  have hBlockInput :
      TMPolyTimeMap X dhcChainArcCandidateWithBudgetEncodedType
        (fun p : X.Carrier => (p.1.1, (p.1.2.1, (p.1.2.2.1, p.2)))) :=
    TMPolyTimeMap.prod_mk hBudget hCandidate
  have hBlock :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier =>
          dhcChainArcBlockFromIndexed (p.1.1, (p.1.2.1, (p.1.2.2.1, p.2)))) := by
    have hComp := TMPolyTimeMap.comp dhcChainArcBlockFromIndexed_tm_polytime hBlockInput
    simpa [Function.comp, dhcChainArcCandidateWithBudgetEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier =>
          (p.1.2.2.2,
            dhcChainArcBlockFromIndexed (p.1.1, (p.1.2.1, (p.1.2.2.1, p.2))))) :=
    TMPolyTimeMap.prod_mk hOutEdges hBlock
  have hAppend :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier =>
          (show List (Nat × Nat) from p.1.2.2.2) ++
            dhcChainArcBlockFromIndexed (p.1.1, (p.1.2.1, (p.1.2.2.1, p.2)))) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append edgeStructuredEncodedType) hAppendInput
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hTrue : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hNewInner :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier =>
          (p.2,
            (show List (Nat × Nat) from p.1.2.2.2) ++
              dhcChainArcBlockFromIndexed (p.1.1, (p.1.2.1, (p.1.2.2.1, p.2))))) :=
    TMPolyTimeMap.prod_mk hCurrent hAppend
  have hNewTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType))
        (fun p : X.Carrier =>
          (true,
            (p.2,
              (show List (Nat × Nat) from p.1.2.2.2) ++
                dhcChainArcBlockFromIndexed
                  (p.1.1, (p.1.2.1, (p.1.2.2.1, p.2)))))) :=
    TMPolyTimeMap.prod_mk hTrue hNewInner
  have hOut := TMPolyTimeMap.prod_mk hBudget hNewTail
  simpa [dhcChainArcsFoldRightStep, dhcChainArcsAccEncodedType, X] using hOut

theorem dhcChainArcsFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod dhcChainArcsAccEncodedType dhcChainArcsInstructionEncodedType)
      dhcChainArcsAccEncodedType
      dhcChainArcsFoldStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      dhcChainArcsAccEncodedType EncodedType.nat dhcIndexedIncidenceEncodedType
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim dhcChainArcsFoldLeftStep_tm_polytime
      dhcChainArcsFoldRightStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem dhcChainArcsInstructions_tm_polytime :
    TMPolyTimeMap dhcIndexedIncidenceListWithBudgetEncodedType
      dhcChainArcsInstructionListEncodedType
      dhcChainArcsInstructions := by
  let X := dhcIndexedIncidenceListWithBudgetEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcIndexedIncidenceListWithBudgetEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat dhcIndexedIncidenceListEncodedType
  have hList :
      TMPolyTimeMap X dhcIndexedIncidenceListEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, dhcIndexedIncidenceListWithBudgetEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat dhcIndexedIncidenceListEncodedType
  have hInit :
      TMPolyTimeMap X dhcChainArcsInstructionEncodedType
        (fun p : X.Carrier => Sum.inl p.1) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.inl EncodedType.nat dhcIndexedIncidenceEncodedType) hBudget
    simpa [Function.comp, dhcChainArcsInstructionEncodedType, X] using hComp
  have hElemInstrs :
      TMPolyTimeMap X dhcChainArcsInstructionListEncodedType
        (fun p : X.Carrier => p.2.map Sum.inr) := by
    have hMap :=
      TMPolyTimeMap.list_map
        (TMPolyTimeMap.inr EncodedType.nat dhcIndexedIncidenceEncodedType)
    have hComp := TMPolyTimeMap.comp hMap hList
    simpa [Function.comp, dhcIndexedIncidenceListEncodedType,
      dhcChainArcsInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod dhcChainArcsInstructionEncodedType
          dhcChainArcsInstructionListEncodedType)
        (fun p : X.Carrier => (Sum.inl p.1, p.2.map Sum.inr)) :=
    TMPolyTimeMap.prod_mk hInit hElemInstrs
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons dhcChainArcsInstructionEncodedType) hConsInput
  simpa [Function.comp, dhcChainArcsInstructions,
    dhcChainArcsInstructionListEncodedType, X,
    dhcIndexedIncidenceListWithBudgetEncodedType] using hOut

def dhcChainArcsFoldAccBound
    (N : Nat) (acc : dhcChainArcsAccEncodedType.Carrier) : Prop :=
  EncodedType.nat.inputSize acc.1 ≤ N + 1 ∧
    dhcIndexedIncidenceEncodedType.inputSize acc.2.2.1 ≤ N + 5

noncomputable def dhcChainArcsFoldGrowPolynomial : Polynomial Nat :=
  Polynomial.C 240 * Polynomial.X + Polynomial.C 400

theorem dhcChainArcsFoldGrowPolynomial_eval (N : Nat) :
    dhcChainArcsFoldGrowPolynomial.eval N = 240 * N + 400 := by
  simp [dhcChainArcsFoldGrowPolynomial, Polynomial.eval_add, Polynomial.eval_mul]

theorem dhcChainArcBlock_inputSize_le
    (N budget : Nat) (active : Bool) (left right : (Nat × Nat) × Nat)
    (hBudget : EncodedType.nat.inputSize budget ≤ N + 1)
    (hLeft : dhcIndexedIncidenceEncodedType.inputSize left ≤ N + 5)
    (hRight : dhcIndexedIncidenceEncodedType.inputSize right ≤ N + 5) :
    edgeListStructuredEncodedType.inputSize
        (dhcChainArcBlockFromIndexed (budget, (active, (left, right)))) ≤
      120 * N + 200 := by
  rcases left with ⟨⟨u, i⟩, idx1⟩
  rcases right with ⟨⟨v, j⟩, idx2⟩
  change Nat at budget
  change Nat at u
  change Nat at i
  change Nat at idx1
  change Nat at v
  change Nat at j
  change Nat at idx2
  have hBudgetNat : budget ≤ N := by
    simpa [EncodedType.inputSize_nat] using hBudget
  have hLeftIdxPayload :
      EncodedType.nat.inputSize idx1 ≤
        dhcIndexedIncidenceEncodedType.inputSize (((u, i), idx1)) := by
    simp [dhcIndexedIncidenceEncodedType, vertexPairEncodedType,
      EncodedType.inputSize_prod]
  have hRightIdxPayload :
      EncodedType.nat.inputSize idx2 ≤
        dhcIndexedIncidenceEncodedType.inputSize (((v, j), idx2)) := by
    simp [dhcIndexedIncidenceEncodedType, vertexPairEncodedType,
      EncodedType.inputSize_prod]
  have hLeftIdxNat : idx1 ≤ N + 4 := by
    have h := hLeftIdxPayload.trans hLeft
    simpa [EncodedType.inputSize_nat] using h
  have hRightIdxNat : idx2 ≤ N + 4 := by
    have h := hRightIdxPayload.trans hRight
    simpa [EncodedType.inputSize_nat] using h
  by_cases hKeep :
      dhcChainArcCandidateBool
          ((active, ((((u, i), idx1), ((v, j), idx2)))) : dhcChainArcCandidateRaw) =
        true
  · simp [dhcChainArcBlockFromIndexed, hKeep, dhcChainArcPairBlock,
      dhcChainArcFromIndexedRaw, dhcIncidenceVertexCode, natDouble,
      edgeListStructuredEncodedType, edgeStructuredEncodedType, EncodedType.inputSize,
      EncodedType.list, EncodedType.prod, EncodedType.nat]
    nlinarith
  · have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
      exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
    simp [dhcChainArcBlockFromIndexed, hKeep, hNil]

theorem dhcChainArcsFoldStep_growth
    (source : List dhcChainArcsInstructionEncodedType.Carrier)
    (acc : dhcChainArcsAccEncodedType.Carrier)
    (instr : dhcChainArcsInstructionEncodedType.Carrier)
    (hAcc :
      dhcChainArcsFoldAccBound
        (dhcChainArcsInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      dhcChainArcsInstructionEncodedType.inputSize instr ≤
        dhcChainArcsInstructionListEncodedType.inputSize source) :
    dhcChainArcsFoldAccBound
        (dhcChainArcsInstructionListEncodedType.inputSize source)
        (dhcChainArcsFoldStep (acc, instr)) ∧
      dhcChainArcsAccEncodedType.inputSize (dhcChainArcsFoldStep (acc, instr)) ≤
        dhcChainArcsAccEncodedType.inputSize acc +
          dhcChainArcsFoldGrowPolynomial.eval
            (dhcChainArcsInstructionListEncodedType.inputSize source) := by
  let N := dhcChainArcsInstructionListEncodedType.inputSize source
  cases instr with
  | inl budget =>
      change Nat at budget
      have hBudgetTagged :
          EncodedType.nat.inputSize budget + 1 ≤ N := by
        simpa [dhcChainArcsInstructionEncodedType, EncodedType.inputSize,
          EncodedType.sum, N, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInstr
      have hBudget : EncodedType.nat.inputSize budget ≤ N + 1 := by
        omega
      have hBudgetNat : budget ≤ N := by
        simpa [EncodedType.inputSize_nat] using hBudget
      have hDummy :
          dhcIndexedIncidenceEncodedType.inputSize dhcChainDummyIncidence ≤ N + 5 := by
        simp [dhcChainDummyIncidence, dhcIndexedIncidenceEncodedType,
          vertexPairEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_nat]
      constructor
      · exact ⟨hBudget, hDummy⟩
      · have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
          exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
        simp [dhcChainArcsFoldStep, dhcChainArcsFoldLeftStep,
          dhcChainArcsAccEncodedType, dhcChainDummyIncidence,
          dhcIndexedIncidenceEncodedType, vertexPairEncodedType,
          EncodedType.inputSize_prod, EncodedType.inputSize_nat,
          EncodedType.inputSize_bool, hNil, dhcChainArcsFoldGrowPolynomial_eval]
        nlinarith
  | inr current =>
      rcases current with ⟨ui, idx⟩
      rcases ui with ⟨u, i⟩
      change Nat at u
      change Nat at i
      change Nat at idx
      have hBudget : EncodedType.nat.inputSize acc.1 ≤ N + 1 := by
        simpa [dhcChainArcsFoldAccBound, N] using hAcc.1
      have hPrev : dhcIndexedIncidenceEncodedType.inputSize acc.2.2.1 ≤ N + 5 := by
        simpa [dhcChainArcsFoldAccBound, N] using hAcc.2
      have hCurrentInput : dhcIndexedIncidenceEncodedType.inputSize ((u, i), idx) ≤ N := by
        have hTagged : dhcIndexedIncidenceEncodedType.inputSize ((u, i), idx) + 1 ≤ N := by
          simpa [dhcChainArcsInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum, N, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInstr
        omega
      have hCurrent : dhcIndexedIncidenceEncodedType.inputSize ((u, i), idx) ≤ N + 5 := by
        omega
      let out : List (Nat × Nat) := acc.2.2.2
      let block : List (Nat × Nat) :=
        dhcChainArcBlockFromIndexed (acc.1, (acc.2.1, (acc.2.2.1, ((u, i), idx))))
      have hAppend :
          edgeListStructuredEncodedType.inputSize (out ++ block) =
            edgeListStructuredEncodedType.inputSize out +
              edgeListStructuredEncodedType.inputSize block := by
        simpa [edgeListStructuredEncodedType, block] using
          Clique.encodedList_inputSize_append edgeStructuredEncodedType out block
      constructor
      · exact ⟨hBudget, hCurrent⟩
      · have hBlock :
            edgeListStructuredEncodedType.inputSize block ≤ 120 * N + 200 := by
          simpa [block] using
            dhcChainArcBlock_inputSize_le N acc.1 acc.2.1 acc.2.2.1 ((u, i), idx)
              hBudget hPrev hCurrent
        simp [dhcChainArcsFoldStep, dhcChainArcsFoldRightStep,
          dhcChainArcsAccEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_bool, dhcChainArcsFoldGrowPolynomial_eval]
        change
          (show Nat from acc.1) + 1 + 1 +
                (EncodedType.bool.inputSize true + 1 +
                  (dhcIndexedIncidenceEncodedType.inputSize ((u, i), idx) + 1 +
                    edgeListStructuredEncodedType.inputSize (out ++ block))) ≤
            (show Nat from acc.1) + 1 + 1 +
                (EncodedType.bool.inputSize acc.2.1 + 1 +
              (dhcIndexedIncidenceEncodedType.inputSize acc.2.2.1 + 1 +
                    edgeListStructuredEncodedType.inputSize out)) +
              (240 * dhcChainArcsInstructionListEncodedType.inputSize source + 400)
        rw [hAppend]
        simp [EncodedType.inputSize_bool]
        nlinarith [hBlock, hCurrent]

theorem dhcChainArcsFold_tm_polytime :
    TMPolyTimeMap
      dhcChainArcsInstructionListEncodedType
      dhcChainArcsAccEncodedType
      (fun xs : List dhcChainArcsInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => dhcChainArcsFoldStep (acc, instr))
          dhcChainArcsFoldInit) := by
  rcases dhcChainArcsFoldStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      dhcChainArcsInstructionEncodedType dhcChainArcsAccEncodedType
      dhcChainArcsFoldStep dhcChainArcsFoldInit hStep
      (Polynomial.C 20) dhcChainArcsFoldGrowPolynomial
      dhcChainArcsFoldAccBound ?_ ?_
  · intro xs
    constructor
    · constructor
      · simp [dhcChainArcsFoldInit, EncodedType.inputSize_nat]
      · simp [dhcChainArcsFoldInit, dhcChainDummyIncidence,
          dhcIndexedIncidenceEncodedType, vertexPairEncodedType,
          EncodedType.inputSize_prod, EncodedType.inputSize_nat]
    · have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
        exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
      simp [dhcChainArcsFoldInit, dhcChainArcsAccEncodedType,
        dhcChainDummyIncidence, dhcIndexedIncidenceEncodedType, vertexPairEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_nat,
        EncodedType.inputSize_bool, hNil]
  · intro source acc instr hAcc hInstr
    simpa [dhcChainArcsInstructionListEncodedType] using
      dhcChainArcsFoldStep_growth source acc instr hAcc hInstr

theorem dhcChainArcsFoldResult_tm_polytime :
    TMPolyTimeMap
      dhcChainArcsInstructionListEncodedType
      edgeListStructuredEncodedType
      dhcChainArcsFoldResult := by
  have hAccTail :
      TMPolyTimeMap dhcChainArcsAccEncodedType
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType))
        (fun acc : dhcChainArcsAccEncodedType.Carrier => acc.2) := by
    simpa [dhcChainArcsAccEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType))
  have hInner :
      TMPolyTimeMap dhcChainArcsAccEncodedType
        (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
        (fun acc : dhcChainArcsAccEncodedType.Carrier => acc.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool
      (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hAccTail
    simpa [Function.comp] using hComp
  have hEdges :
      TMPolyTimeMap dhcChainArcsAccEncodedType edgeListStructuredEncodedType
        (fun acc : dhcChainArcsAccEncodedType.Carrier => acc.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInner
    simpa [Function.comp] using hComp
  have hComp := TMPolyTimeMap.comp hEdges dhcChainArcsFold_tm_polytime
  simpa [Function.comp, dhcChainArcsFoldResult] using hComp

theorem dhcChainArcsExecutableFromIndexed_tm_polytime :
    TMPolyTimeMap dhcIndexedIncidenceListWithBudgetEncodedType
      edgeListStructuredEncodedType
      dhcChainArcsExecutableFromIndexed := by
  have hComp :=
    TMPolyTimeMap.comp dhcChainArcsFoldResult_tm_polytime
      dhcChainArcsInstructions_tm_polytime
  simpa [Function.comp, dhcChainArcsExecutableFromIndexed] using hComp

/-! ### Semantic expansion of the adjacent-chain fold -/

def dhcChainArcsLastOr
    (prev : dhcIndexedIncidenceEncodedType.Carrier) :
    List dhcIndexedIncidenceEncodedType.Carrier → dhcIndexedIncidenceEncodedType.Carrier
  | [] => prev
  | x :: xs => dhcChainArcsLastOr x xs

def dhcChainArcsFromPrevIndexed
    (budget : Nat) (prev : dhcIndexedIncidenceEncodedType.Carrier) :
    List dhcIndexedIncidenceEncodedType.Carrier → List (Nat × Nat)
  | [] => []
  | x :: xs =>
      dhcChainArcBlockFromIndexed (budget, (true, (prev, x))) ++
        dhcChainArcsFromPrevIndexed budget x xs

def dhcChainArcsFromAdjacentIndexed
    (budget : Nat) : List dhcIndexedIncidenceEncodedType.Carrier → List (Nat × Nat)
  | [] => []
  | x :: xs => dhcChainArcsFromPrevIndexed budget x xs

theorem dhcChainArcsFold_active_invariant
    (budget : Nat) (prev : dhcIndexedIncidenceEncodedType.Carrier)
    (xs : List dhcIndexedIncidenceEncodedType.Carrier) (out : List (Nat × Nat)) :
    (xs.map Sum.inr).foldl
        (fun acc instr => dhcChainArcsFoldStep (acc, instr))
        (budget, (true, (prev, out))) =
      (budget,
        (true,
          (dhcChainArcsLastOr prev xs,
            out ++ dhcChainArcsFromPrevIndexed budget prev xs))) := by
  induction xs generalizing prev out with
  | nil =>
      simp [dhcChainArcsLastOr, dhcChainArcsFromPrevIndexed]
      rfl
  | cons x xs ih =>
      change
        (xs.map Sum.inr).foldl
            (fun acc instr => dhcChainArcsFoldStep (acc, instr))
            (dhcChainArcsFoldStep ((budget, (true, (prev, out))), Sum.inr x)) =
          (budget,
            (true,
              (dhcChainArcsLastOr prev (x :: xs),
                out ++ dhcChainArcsFromPrevIndexed budget prev (x :: xs))))
      rw [show
          dhcChainArcsFoldStep ((budget, (true, (prev, out))), Sum.inr x) =
            (budget,
              (true,
                (x,
                  out ++ dhcChainArcBlockFromIndexed (budget, (true, (prev, x)))))) by
        rfl]
      calc
        (xs.map Sum.inr).foldl
            (fun acc instr => dhcChainArcsFoldStep (acc, instr))
            (budget,
              (true,
                (x, out ++ dhcChainArcBlockFromIndexed (budget, (true, (prev, x))))))
            =
          (budget,
            (true,
              (dhcChainArcsLastOr x xs,
                (out ++ dhcChainArcBlockFromIndexed (budget, (true, (prev, x)))) ++
                  dhcChainArcsFromPrevIndexed budget x xs))) := by
            exact ih x (out ++ dhcChainArcBlockFromIndexed (budget, (true, (prev, x))))
        _ =
          (budget,
            (true,
              (dhcChainArcsLastOr prev (x :: xs),
                out ++ dhcChainArcsFromPrevIndexed budget prev (x :: xs)))) := by
            simp [dhcChainArcsLastOr, dhcChainArcsFromPrevIndexed, List.append_assoc]

theorem dhcChainArcBlockFromIndexed_inactive
    (budget : Nat) (left right : dhcIndexedIncidenceEncodedType.Carrier) :
    dhcChainArcBlockFromIndexed (budget, (false, (left, right))) = [] := by
  simp [dhcChainArcBlockFromIndexed, dhcChainArcCandidateBool, graphBoolAndPair]

theorem dhcChainArcsFold_inactive_invariant
    (budget : Nat) (xs : List dhcIndexedIncidenceEncodedType.Carrier)
    (out : List (Nat × Nat)) :
    (xs.map Sum.inr).foldl
        (fun acc instr => dhcChainArcsFoldStep (acc, instr))
        (budget, (false, (dhcChainDummyIncidence, out))) =
      match xs with
      | [] => (budget, (false, (dhcChainDummyIncidence, out)))
      | x :: xs =>
          (budget,
            (true,
              (dhcChainArcsLastOr x xs,
                out ++ dhcChainArcsFromPrevIndexed budget x xs))) := by
  cases xs with
  | nil =>
      simp
      rfl
  | cons x xs =>
      change
        (xs.map Sum.inr).foldl
            (fun acc instr => dhcChainArcsFoldStep (acc, instr))
            (dhcChainArcsFoldStep
              ((budget, (false, (dhcChainDummyIncidence, out))), Sum.inr x)) =
          (budget,
            (true,
              (dhcChainArcsLastOr x xs,
                out ++ dhcChainArcsFromPrevIndexed budget x xs)))
      rw [show
          dhcChainArcsFoldStep
              ((budget, (false, (dhcChainDummyIncidence, out))), Sum.inr x) =
            (budget, (true, (x, out))) by
        simp [dhcChainArcsFoldStep, dhcChainArcsFoldRightStep,
          dhcChainArcBlockFromIndexed_inactive]
        rfl]
      simpa using dhcChainArcsFold_active_invariant budget x xs out

theorem dhcChainArcsExecutableFromIndexed_eq_adjacent
    (p : dhcIndexedIncidenceListWithBudgetRaw) :
    dhcChainArcsExecutableFromIndexed p =
      dhcChainArcsFromAdjacentIndexed p.1 p.2 := by
  rcases p with ⟨budget, xs⟩
  rw [dhcChainArcsExecutableFromIndexed, dhcChainArcsFoldResult,
    dhcChainArcsInstructions]
  rw [List.foldl_cons]
  rw [show dhcChainArcsFoldStep (dhcChainArcsFoldInit, Sum.inl budget) =
      (budget, (false, (dhcChainDummyIncidence, ([] : List (Nat × Nat))))) by
    rfl]
  have hFold :=
    congrArg (fun acc : dhcChainArcsAccEncodedType.Carrier => acc.2.2.2)
      (dhcChainArcsFold_inactive_invariant budget xs ([] : List (Nat × Nat)))
  cases xs with
  | nil =>
      simpa [dhcChainArcsFromAdjacentIndexed] using hFold
  | cons x xs =>
      simpa [dhcChainArcsFromAdjacentIndexed] using hFold

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
