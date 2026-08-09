/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.EntryExitTM

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

/-!
TM-backed slot-boundary scans for entry/exit arcs.

This file starts with the entry scan.  It packages the existing source-order
boundary semantics from `EntryExitAssembly` as a left-initialized fold over the
indexed source-incidence list.
-/

def dhcSlotIndexedIncidenceListEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)

abbrev dhcSlotIndexedIncidenceListRaw :=
  Nat × (Nat × List dhcIndexedIncidenceEncodedType.Carrier)

def dhcEntryExitBoundaryDummyIncidence : dhcIndexedIncidenceEncodedType.Carrier :=
  (((0 : Nat), (0 : Nat)), (0 : Nat))

def dhcBoundaryIncidenceSource
    (inc : dhcIndexedIncidenceEncodedType.Carrier) : Nat :=
  inc.1.1

def dhcBoundarySameSourceBool
    (prev current : dhcIndexedIncidenceEncodedType.Carrier) : Bool :=
  Nat.beq (dhcBoundaryIncidenceSource prev) (dhcBoundaryIncidenceSource current)

theorem dhcEntryArcForSlotBlockFromIndexed_tm_polytime :
    TMPolyTimeMap dhcEntryArcForSlotFromIndexedInputEncodedType
      edgeListStructuredEncodedType
      (fun p : dhcEntryArcForSlotFromIndexedInputEncodedType.Carrier =>
        dhcEntryArcForSlotBlockFromIndexed p.1 p.2.1 p.2.2) := by
  have hComp := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_singleton edgeStructuredEncodedType)
    dhcEntryArcForSlotFromIndexed_tm_polytime
  simpa [Function.comp, dhcEntryArcForSlotFromIndexed,
    dhcEntryArcForSlotBlockFromIndexed, edgeListStructuredEncodedType] using hComp

theorem dhcExitArcForSlotBlockFromIndexed_tm_polytime :
    TMPolyTimeMap dhcExitArcForSlotFromIndexedInputEncodedType
      edgeListStructuredEncodedType
      (fun p : dhcExitArcForSlotFromIndexedInputEncodedType.Carrier =>
        dhcExitArcForSlotBlockFromIndexed p.1 p.2.1 p.2.2) := by
  have hComp := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_singleton edgeStructuredEncodedType)
    dhcExitArcForSlotFromIndexed_tm_polytime
  simpa [Function.comp, dhcExitArcForSlotFromIndexed,
    dhcExitArcForSlotBlockFromIndexed, edgeListStructuredEncodedType] using hComp

/-! ### Entry boundary scan -/

def dhcEntryBoundaryBlockInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.bool
        (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType)))

abbrev dhcEntryBoundaryBlockRaw :=
  Nat × (Nat × (Bool ×
    (dhcIndexedIncidenceEncodedType.Carrier × dhcIndexedIncidenceEncodedType.Carrier)))

def dhcEntryBoundaryBlock (p : dhcEntryBoundaryBlockRaw) : List (Nat × Nat) :=
  match p.2.2.1 with
  | true =>
      match dhcBoundarySameSourceBool p.2.2.2.1 p.2.2.2.2 with
      | true => []
      | false => dhcEntryArcForSlotBlockFromIndexed p.1 p.2.1 p.2.2.2.2
  | false =>
      dhcEntryArcForSlotBlockFromIndexed p.1 p.2.1 p.2.2.2.2

theorem dhcEntryBoundaryBlock_tm_polytime :
    TMPolyTimeMap dhcEntryBoundaryBlockInputEncodedType
      edgeListStructuredEncodedType
      dhcEntryBoundaryBlock := by
  let X := dhcEntryBoundaryBlockInputEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcEntryBoundaryBlockInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.bool
            (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType)))
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.bool
            (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType)))
        (fun p : X.Carrier => p.2) := by
    simpa [X, dhcEntryBoundaryBlockInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.bool
            (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType)))
  have hSlot : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.bool
        (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType))
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hFlagTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType))
        (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.bool
        (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType))
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hActive : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool
      (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hFlagTail
    simpa [Function.comp, X] using hComp
  have hPair :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType)
        (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool
      (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hFlagTail
    simpa [Function.comp, X] using hComp
  have hPrev : TMPolyTimeMap X dhcIndexedIncidenceEncodedType
      (fun p : X.Carrier => p.2.2.2.1) := by
    have hFst := TMPolyTimeMap.fst dhcIndexedIncidenceEncodedType
      dhcIndexedIncidenceEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPair
    simpa [Function.comp, X] using hComp
  have hCurrent : TMPolyTimeMap X dhcIndexedIncidenceEncodedType
      (fun p : X.Carrier => p.2.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd dhcIndexedIncidenceEncodedType
      dhcIndexedIncidenceEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPair
    simpa [Function.comp, X] using hComp
  have hPrevPair : TMPolyTimeMap X vertexPairEncodedType
      (fun p : X.Carrier => p.2.2.2.1.1) := by
    have hFst := TMPolyTimeMap.fst vertexPairEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPrev
    simpa [Function.comp, dhcIndexedIncidenceEncodedType, X] using hComp
  have hCurrentPair : TMPolyTimeMap X vertexPairEncodedType
      (fun p : X.Carrier => p.2.2.2.2.1) := by
    have hFst := TMPolyTimeMap.fst vertexPairEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hCurrent
    simpa [Function.comp, dhcIndexedIncidenceEncodedType, X] using hComp
  have hPrevSource : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.2.2.2.1.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPrevPair
    simpa [Function.comp, vertexPairEncodedType, X] using hComp
  have hCurrentSource : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.2.2.2.2.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hCurrentPair
    simpa [Function.comp, vertexPairEncodedType, X] using hComp
  have hSameInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.2.2.1.1.1, p.2.2.2.2.1.1)) :=
    TMPolyTimeMap.prod_mk hPrevSource hCurrentSource
  have hSame :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier =>
          dhcBoundarySameSourceBool p.2.2.2.1 p.2.2.2.2) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hSameInput
    convert hComp using 1
    funext p
    let a : Nat := p.2.2.2.1.1.1
    let b : Nat := p.2.2.2.2.1.1
    change Nat.beq a b = decide (a = b)
    cases h : Nat.beq a b
    · have hNe : a ≠ b := Nat.ne_of_beq_eq_false h
      have hDec : decide (a = b) = false := decide_eq_false hNe
      simp [hDec]
    · have hEq : a = b := Nat.eq_of_beq_eq_true h
      have hDec : decide (a = b) = true := decide_eq_true hEq
      simp [hDec]
  have hArcInput :
      TMPolyTimeMap X dhcEntryArcForSlotFromIndexedInputEncodedType
        (fun p : X.Carrier => (p.1, (p.2.1, p.2.2.2.2))) :=
    TMPolyTimeMap.prod_mk hBudget (TMPolyTimeMap.prod_mk hSlot hCurrent)
  have hSingleton :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier =>
          dhcEntryArcForSlotBlockFromIndexed p.1 p.2.1 p.2.2.2.2) := by
    have hComp := TMPolyTimeMap.comp dhcEntryArcForSlotBlockFromIndexed_tm_polytime hArcInput
    simpa [Function.comp, X, dhcEntryArcForSlotFromIndexedInputEncodedType] using hComp
  have hEmpty :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun _ : X.Carrier => ([] : List (Nat × Nat))) :=
    TMPolyTimeMap.const X edgeListStructuredEncodedType []
  have hSamePayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier =>
          (dhcBoundarySameSourceBool p.2.2.2.1 p.2.2.2.2, p)) :=
    TMPolyTimeMap.prod_mk hSame (TMPolyTimeMap.id X)
  have hSameDispatch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X)
        edgeListStructuredEncodedType
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true => ([] : List (Nat × Nat))
          | false => dhcEntryArcForSlotBlockFromIndexed p.2.1 p.2.2.1 p.2.2.2.2.2) :=
    graphBoolProduct_dispatch_tm_polytime X edgeListStructuredEncodedType
      (fFalse := fun p : X.Carrier =>
        dhcEntryArcForSlotBlockFromIndexed p.1 p.2.1 p.2.2.2.2)
      (fTrue := fun _ : X.Carrier => ([] : List (Nat × Nat)))
      hSingleton hEmpty
  have hSameBlock :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier =>
          match dhcBoundarySameSourceBool p.2.2.2.1 p.2.2.2.2 with
          | true => []
          | false => dhcEntryArcForSlotBlockFromIndexed p.1 p.2.1 p.2.2.2.2) := by
    have hComp := TMPolyTimeMap.comp hSameDispatch hSamePayload
    simpa [Function.comp] using hComp
  have hActivePayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (p.2.2.1, p)) :=
    TMPolyTimeMap.prod_mk hActive (TMPolyTimeMap.id X)
  have hActiveDispatch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X)
        edgeListStructuredEncodedType
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true =>
              match dhcBoundarySameSourceBool p.2.2.2.2.1 p.2.2.2.2.2 with
              | true => []
              | false =>
                  dhcEntryArcForSlotBlockFromIndexed p.2.1 p.2.2.1 p.2.2.2.2.2
          | false =>
              dhcEntryArcForSlotBlockFromIndexed p.2.1 p.2.2.1 p.2.2.2.2.2) :=
    graphBoolProduct_dispatch_tm_polytime X edgeListStructuredEncodedType
      (fFalse := fun p : X.Carrier =>
        dhcEntryArcForSlotBlockFromIndexed p.1 p.2.1 p.2.2.2.2)
      (fTrue := fun p : X.Carrier =>
        match dhcBoundarySameSourceBool p.2.2.2.1 p.2.2.2.2 with
        | true => []
        | false => dhcEntryArcForSlotBlockFromIndexed p.1 p.2.1 p.2.2.2.2)
      hSingleton hSameBlock
  have hComp := TMPolyTimeMap.comp hActiveDispatch hActivePayload
  simpa [Function.comp, dhcEntryBoundaryBlock] using hComp

def dhcEntryBoundaryAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.bool
        (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)))

def dhcEntryBoundaryPayloadEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.nat

def dhcEntryBoundaryInstructionEncodedType : EncodedType :=
  EncodedType.sum dhcEntryBoundaryPayloadEncodedType dhcIndexedIncidenceEncodedType

def dhcEntryBoundaryInstructionListEncodedType : EncodedType :=
  EncodedType.list dhcEntryBoundaryInstructionEncodedType

def dhcEntryBoundaryFoldInit : dhcEntryBoundaryAccEncodedType.Carrier :=
  ((0 : Nat),
    ((0 : Nat),
      (false, (dhcEntryExitBoundaryDummyIncidence, ([] : List (Nat × Nat))))))

def dhcEntryBoundaryFoldLeftStep
    (payload : dhcEntryBoundaryPayloadEncodedType.Carrier) :
    dhcEntryBoundaryAccEncodedType.Carrier :=
  (payload.1,
    (payload.2,
      (false, (dhcEntryExitBoundaryDummyIncidence, ([] : List (Nat × Nat))))))

def dhcEntryBoundaryFoldRightStep
    (p : dhcEntryBoundaryAccEncodedType.Carrier ×
      dhcIndexedIncidenceEncodedType.Carrier) :
    dhcEntryBoundaryAccEncodedType.Carrier :=
  (p.1.1,
    (p.1.2.1,
      (true,
        (p.2,
          (show List (Nat × Nat) from p.1.2.2.2.2) ++
            dhcEntryBoundaryBlock (p.1.1, (p.1.2.1, (p.1.2.2.1, (p.1.2.2.2.1, p.2))))))))

def dhcEntryBoundaryFoldStep
    (p : dhcEntryBoundaryAccEncodedType.Carrier ×
      dhcEntryBoundaryInstructionEncodedType.Carrier) :
    dhcEntryBoundaryAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl payload => dhcEntryBoundaryFoldLeftStep payload
  | Sum.inr inc => dhcEntryBoundaryFoldRightStep (p.1, inc)

def dhcEntryBoundaryInstructions
    (p : dhcSlotIndexedIncidenceListRaw) :
    dhcEntryBoundaryInstructionListEncodedType.Carrier :=
  Sum.inl (p.1, p.2.1) :: p.2.2.map Sum.inr

def dhcEntryBoundaryFoldResult
    (instrs : dhcEntryBoundaryInstructionListEncodedType.Carrier) :
    List (Nat × Nat) :=
  (instrs.foldl (fun acc instr => dhcEntryBoundaryFoldStep (acc, instr))
    dhcEntryBoundaryFoldInit).2.2.2.2

def dhcEntryArcsForSlotFromBoundaryIndexedExecutable
    (p : dhcSlotIndexedIncidenceListRaw) : List (Nat × Nat) :=
  dhcEntryBoundaryFoldResult (dhcEntryBoundaryInstructions p)

theorem dhcEntryBoundaryFoldLeftStep_tm_polytime :
    TMPolyTimeMap dhcEntryBoundaryPayloadEncodedType dhcEntryBoundaryAccEncodedType
      dhcEntryBoundaryFoldLeftStep := by
  let X := dhcEntryBoundaryPayloadEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcEntryBoundaryPayloadEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hSlot : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X, dhcEntryBoundaryPayloadEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hFalse : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hDummy :
      TMPolyTimeMap X dhcIndexedIncidenceEncodedType
        (fun _ : X.Carrier => dhcEntryExitBoundaryDummyIncidence) :=
    TMPolyTimeMap.const X dhcIndexedIncidenceEncodedType dhcEntryExitBoundaryDummyIncidence
  have hEmpty :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun _ : X.Carrier => ([] : List (Nat × Nat))) :=
    TMPolyTimeMap.const X edgeListStructuredEncodedType []
  have hInner :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
        (fun _ : X.Carrier =>
          (dhcEntryExitBoundaryDummyIncidence, ([] : List (Nat × Nat)))) :=
    TMPolyTimeMap.prod_mk hDummy hEmpty
  have hFlagTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType))
        (fun _ : X.Carrier =>
          (false, (dhcEntryExitBoundaryDummyIncidence, ([] : List (Nat × Nat))))) :=
    TMPolyTimeMap.prod_mk hFalse hInner
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.bool
            (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)))
        (fun p : X.Carrier =>
          (p.2,
            (false, (dhcEntryExitBoundaryDummyIncidence, ([] : List (Nat × Nat)))))) :=
    TMPolyTimeMap.prod_mk hSlot hFlagTail
  have hOut := TMPolyTimeMap.prod_mk hBudget hTail
  simpa [dhcEntryBoundaryFoldLeftStep, dhcEntryBoundaryAccEncodedType,
    dhcEntryBoundaryPayloadEncodedType, X] using hOut

theorem dhcEntryBoundaryFoldRightStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod dhcEntryBoundaryAccEncodedType dhcIndexedIncidenceEncodedType)
      dhcEntryBoundaryAccEncodedType
      dhcEntryBoundaryFoldRightStep := by
  let X := EncodedType.prod dhcEntryBoundaryAccEncodedType dhcIndexedIncidenceEncodedType
  have hAcc : TMPolyTimeMap X dhcEntryBoundaryAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst dhcEntryBoundaryAccEncodedType
      dhcIndexedIncidenceEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)))
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, dhcEntryBoundaryAccEncodedType, X] using hComp
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.bool
            (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)))
        (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)))
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, dhcEntryBoundaryAccEncodedType, X] using hComp
  have hSlot : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.bool
        (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType))
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hFlagTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType))
        (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.bool
        (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType))
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hActive : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool
      (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hFlagTail
    simpa [Function.comp, X] using hComp
  have hInner :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier => p.1.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool
      (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hFlagTail
    simpa [Function.comp, X] using hComp
  have hPrev :
      TMPolyTimeMap X dhcIndexedIncidenceEncodedType (fun p : X.Carrier => p.1.2.2.2.1) := by
    have hFst := TMPolyTimeMap.fst dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInner
    simpa [Function.comp, X] using hComp
  have hOutEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.1.2.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInner
    simpa [Function.comp, X] using hComp
  have hCurrent :
      TMPolyTimeMap X dhcIndexedIncidenceEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd dhcEntryBoundaryAccEncodedType
      dhcIndexedIncidenceEncodedType
  have hPrevCurrent :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType)
        (fun p : X.Carrier => (p.1.2.2.2.1, p.2)) :=
    TMPolyTimeMap.prod_mk hPrev hCurrent
  have hActivePair :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType))
        (fun p : X.Carrier => (p.1.2.2.1, (p.1.2.2.2.1, p.2))) :=
    TMPolyTimeMap.prod_mk hActive hPrevCurrent
  have hBlockTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.bool
            (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceEncodedType)))
        (fun p : X.Carrier => (p.1.2.1, (p.1.2.2.1, (p.1.2.2.2.1, p.2)))) :=
    TMPolyTimeMap.prod_mk hSlot hActivePair
  have hBlockInput :
      TMPolyTimeMap X dhcEntryBoundaryBlockInputEncodedType
        (fun p : X.Carrier =>
          (p.1.1, (p.1.2.1, (p.1.2.2.1, (p.1.2.2.2.1, p.2))))) :=
    TMPolyTimeMap.prod_mk hBudget hBlockTail
  have hBlock :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier =>
          dhcEntryBoundaryBlock
            (p.1.1, (p.1.2.1, (p.1.2.2.1, (p.1.2.2.2.1, p.2))))) := by
    have hComp := TMPolyTimeMap.comp dhcEntryBoundaryBlock_tm_polytime hBlockInput
    simpa [Function.comp, dhcEntryBoundaryBlockInputEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier =>
          (p.1.2.2.2.2,
            dhcEntryBoundaryBlock
              (p.1.1, (p.1.2.1, (p.1.2.2.1, (p.1.2.2.2.1, p.2)))))) :=
    TMPolyTimeMap.prod_mk hOutEdges hBlock
  have hAppend :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier =>
          (show List (Nat × Nat) from p.1.2.2.2.2) ++
            dhcEntryBoundaryBlock
              (p.1.1, (p.1.2.1, (p.1.2.2.1, (p.1.2.2.2.1, p.2))))) := by
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
            (show List (Nat × Nat) from p.1.2.2.2.2) ++
              dhcEntryBoundaryBlock
                (p.1.1, (p.1.2.1, (p.1.2.2.1, (p.1.2.2.2.1, p.2)))))) :=
    TMPolyTimeMap.prod_mk hCurrent hAppend
  have hNewFlagTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType))
        (fun p : X.Carrier =>
          (true,
            (p.2,
              (show List (Nat × Nat) from p.1.2.2.2.2) ++
                dhcEntryBoundaryBlock
                  (p.1.1, (p.1.2.1, (p.1.2.2.1, (p.1.2.2.2.1, p.2))))))) :=
    TMPolyTimeMap.prod_mk hTrue hNewInner
  have hNewTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.bool
            (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)))
        (fun p : X.Carrier =>
          (p.1.2.1,
            (true,
              (p.2,
                (show List (Nat × Nat) from p.1.2.2.2.2) ++
                  dhcEntryBoundaryBlock
                    (p.1.1, (p.1.2.1, (p.1.2.2.1, (p.1.2.2.2.1, p.2)))))))) :=
    TMPolyTimeMap.prod_mk hSlot hNewFlagTail
  have hOut := TMPolyTimeMap.prod_mk hBudget hNewTail
  simpa [dhcEntryBoundaryFoldRightStep, dhcEntryBoundaryAccEncodedType, X] using hOut

theorem dhcEntryBoundaryFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod dhcEntryBoundaryAccEncodedType dhcEntryBoundaryInstructionEncodedType)
      dhcEntryBoundaryAccEncodedType
      dhcEntryBoundaryFoldStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      dhcEntryBoundaryAccEncodedType dhcEntryBoundaryPayloadEncodedType
      dhcIndexedIncidenceEncodedType
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim dhcEntryBoundaryFoldLeftStep_tm_polytime
      dhcEntryBoundaryFoldRightStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem dhcEntryBoundaryInstructions_tm_polytime :
    TMPolyTimeMap dhcSlotIndexedIncidenceListEncodedType
      dhcEntryBoundaryInstructionListEncodedType
      dhcEntryBoundaryInstructions := by
  let X := dhcSlotIndexedIncidenceListEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcSlotIndexedIncidenceListEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)
        (fun p : X.Carrier => p.2) := by
    simpa [X, dhcSlotIndexedIncidenceListEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)
  have hSlot : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat dhcIndexedIncidenceListEncodedType
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hSource :
      TMPolyTimeMap X dhcIndexedIncidenceListEncodedType (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat dhcIndexedIncidenceListEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hPayload :
      TMPolyTimeMap X dhcEntryBoundaryPayloadEncodedType
        (fun p : X.Carrier => (p.1, p.2.1)) :=
    TMPolyTimeMap.prod_mk hBudget hSlot
  have hInit :
      TMPolyTimeMap X dhcEntryBoundaryInstructionEncodedType
        (fun p : X.Carrier => Sum.inl (p.1, p.2.1)) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.inl dhcEntryBoundaryPayloadEncodedType dhcIndexedIncidenceEncodedType)
      hPayload
    simpa [Function.comp, dhcEntryBoundaryInstructionEncodedType, X] using hComp
  have hElemInstrs :
      TMPolyTimeMap X dhcEntryBoundaryInstructionListEncodedType
        (fun p : X.Carrier => p.2.2.map Sum.inr) := by
    have hMap :=
      TMPolyTimeMap.list_map
        (TMPolyTimeMap.inr dhcEntryBoundaryPayloadEncodedType dhcIndexedIncidenceEncodedType)
    have hComp := TMPolyTimeMap.comp hMap hSource
    simpa [Function.comp, dhcIndexedIncidenceListEncodedType,
      dhcEntryBoundaryInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod dhcEntryBoundaryInstructionEncodedType
          dhcEntryBoundaryInstructionListEncodedType)
        (fun p : X.Carrier =>
          (Sum.inl (p.1, p.2.1), p.2.2.map Sum.inr)) :=
    TMPolyTimeMap.prod_mk hInit hElemInstrs
  have hOut :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons dhcEntryBoundaryInstructionEncodedType)
      hConsInput
  simpa [Function.comp, dhcEntryBoundaryInstructions,
    dhcEntryBoundaryInstructionListEncodedType, dhcSlotIndexedIncidenceListEncodedType, X]
    using hOut

def dhcEntryBoundaryFoldAccBound
    (N : Nat) (acc : dhcEntryBoundaryAccEncodedType.Carrier) : Prop :=
  EncodedType.nat.inputSize acc.1 ≤ N + 1 ∧
    EncodedType.nat.inputSize acc.2.1 ≤ N + 1 ∧
      dhcIndexedIncidenceEncodedType.inputSize acc.2.2.2.1 ≤ N + 5

noncomputable def dhcEntryBoundaryFoldGrowPolynomial : Polynomial Nat :=
  Polynomial.C 160 * Polynomial.X + Polynomial.C 400

theorem dhcEntryBoundaryFoldGrowPolynomial_eval (N : Nat) :
    dhcEntryBoundaryFoldGrowPolynomial.eval N = 160 * N + 400 := by
  simp [dhcEntryBoundaryFoldGrowPolynomial, Polynomial.eval_add, Polynomial.eval_mul]

theorem dhcEntryArcForSlotBlockFromIndexed_inputSize_le
    (N budget slot : Nat) (inc : dhcIndexedIncidenceEncodedType.Carrier)
    (hBudget : EncodedType.nat.inputSize budget ≤ N + 1)
    (hSlot : EncodedType.nat.inputSize slot ≤ N + 1)
    (hInc : dhcIndexedIncidenceEncodedType.inputSize inc ≤ N + 5) :
    edgeListStructuredEncodedType.inputSize
        (dhcEntryArcForSlotBlockFromIndexed budget slot inc) ≤
      120 * N + 200 := by
  rcases inc with ⟨⟨u, i⟩, idx⟩
  change Nat at u
  change Nat at i
  change Nat at idx
  have hBudgetNat : budget ≤ N := by
    simpa [EncodedType.inputSize_nat] using hBudget
  have hSlotNat : slot ≤ N := by
    simpa [EncodedType.inputSize_nat] using hSlot
  have hIdxPayload :
      EncodedType.nat.inputSize idx ≤
        dhcIndexedIncidenceEncodedType.inputSize (((u, i), idx)) := by
    simp [dhcIndexedIncidenceEncodedType, vertexPairEncodedType,
      EncodedType.inputSize_prod]
  have hIdxNat : idx ≤ N + 4 := by
    have h := hIdxPayload.trans hInc
    simpa [EncodedType.inputSize_nat] using h
  simp [dhcEntryArcForSlotBlockFromIndexed, dhcEntryArcForSlotFromIndexedRaw,
    dhcIncidenceVertexCode, textbookSelectorVertex, natDouble,
    edgeListStructuredEncodedType, edgeStructuredEncodedType, EncodedType.inputSize,
    EncodedType.list, EncodedType.prod, EncodedType.nat]
  nlinarith

theorem dhcEntryBoundaryBlock_inputSize_le
    (N : Nat) (p : dhcEntryBoundaryBlockRaw)
    (hBudget : EncodedType.nat.inputSize p.1 ≤ N + 1)
    (hSlot : EncodedType.nat.inputSize p.2.1 ≤ N + 1)
    (hCurrent : dhcIndexedIncidenceEncodedType.inputSize p.2.2.2.2 ≤ N + 5) :
    edgeListStructuredEncodedType.inputSize (dhcEntryBoundaryBlock p) ≤
      120 * N + 200 := by
  rcases p with ⟨budget, slot, active, prev, current⟩
  cases active
  · simpa [dhcEntryBoundaryBlock] using
      dhcEntryArcForSlotBlockFromIndexed_inputSize_le N budget slot current
        hBudget hSlot hCurrent
  · by_cases hSame :
        dhcBoundaryIncidenceSource prev = dhcBoundaryIncidenceSource current
    · have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
        exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
      have hSameRaw : (prev.1.1 : Nat) = (current.1.1 : Nat) := by
        simpa [dhcBoundaryIncidenceSource] using hSame
      have hBeq : Nat.beq (prev.1.1 : Nat) (current.1.1 : Nat) = true := by
        rw [Nat.beq_eq]
        exact hSameRaw
      simp [dhcEntryBoundaryBlock, dhcBoundarySameSourceBool, dhcBoundaryIncidenceSource,
        hBeq, hNil]
    · have hSameRaw : ¬(prev.1.1 : Nat) = (current.1.1 : Nat) := by
        simpa [dhcBoundaryIncidenceSource] using hSame
      have hBeq : Nat.beq (prev.1.1 : Nat) (current.1.1 : Nat) = false := by
        rw [← Bool.not_eq_true, Nat.beq_eq]
        exact hSameRaw
      simpa [dhcEntryBoundaryBlock, dhcBoundarySameSourceBool,
        dhcBoundaryIncidenceSource, hBeq] using
        dhcEntryArcForSlotBlockFromIndexed_inputSize_le N budget slot current
          hBudget hSlot hCurrent

theorem dhcEntryBoundaryFoldStep_growth
    (source : List dhcEntryBoundaryInstructionEncodedType.Carrier)
    (acc : dhcEntryBoundaryAccEncodedType.Carrier)
    (instr : dhcEntryBoundaryInstructionEncodedType.Carrier)
    (hAcc :
      dhcEntryBoundaryFoldAccBound
        (dhcEntryBoundaryInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      dhcEntryBoundaryInstructionEncodedType.inputSize instr ≤
        dhcEntryBoundaryInstructionListEncodedType.inputSize source) :
    dhcEntryBoundaryFoldAccBound
        (dhcEntryBoundaryInstructionListEncodedType.inputSize source)
        (dhcEntryBoundaryFoldStep (acc, instr)) ∧
      dhcEntryBoundaryAccEncodedType.inputSize (dhcEntryBoundaryFoldStep (acc, instr)) ≤
        dhcEntryBoundaryAccEncodedType.inputSize acc +
          dhcEntryBoundaryFoldGrowPolynomial.eval
            (dhcEntryBoundaryInstructionListEncodedType.inputSize source) := by
  let N := dhcEntryBoundaryInstructionListEncodedType.inputSize source
  cases instr with
  | inl payload =>
      rcases payload with ⟨budget, slot⟩
      change Nat at budget
      change Nat at slot
      have hPayloadInput :
          dhcEntryBoundaryPayloadEncodedType.inputSize (budget, slot) ≤ N := by
        have hTagged :
            dhcEntryBoundaryPayloadEncodedType.inputSize (budget, slot) + 1 ≤ N := by
          simpa [dhcEntryBoundaryInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum, N, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInstr
        omega
      have hBudgetPayload :
          EncodedType.nat.inputSize budget ≤
            dhcEntryBoundaryPayloadEncodedType.inputSize (budget, slot) := by
        simp [dhcEntryBoundaryPayloadEncodedType, EncodedType.inputSize_prod]
        omega
      have hSlotPayload :
          EncodedType.nat.inputSize slot ≤
            dhcEntryBoundaryPayloadEncodedType.inputSize (budget, slot) := by
        simp [dhcEntryBoundaryPayloadEncodedType, EncodedType.inputSize_prod]
      have hBudget : EncodedType.nat.inputSize budget ≤ N + 1 :=
        (hBudgetPayload.trans hPayloadInput).trans (Nat.le_succ N)
      have hSlot : EncodedType.nat.inputSize slot ≤ N + 1 :=
        (hSlotPayload.trans hPayloadInput).trans (Nat.le_succ N)
      have hDummy :
          dhcIndexedIncidenceEncodedType.inputSize dhcEntryExitBoundaryDummyIncidence ≤
            N + 5 := by
        simp [dhcEntryExitBoundaryDummyIncidence, dhcIndexedIncidenceEncodedType,
          vertexPairEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_nat]
      constructor
      · exact ⟨hBudget, hSlot, hDummy⟩
      · have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
          exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
        simp [dhcEntryBoundaryFoldStep, dhcEntryBoundaryFoldLeftStep,
          dhcEntryBoundaryAccEncodedType, dhcEntryExitBoundaryDummyIncidence,
          dhcIndexedIncidenceEncodedType, vertexPairEncodedType,
          EncodedType.inputSize_prod, EncodedType.inputSize_nat,
          EncodedType.inputSize_bool, hNil, dhcEntryBoundaryFoldGrowPolynomial_eval]
        have hBudgetNat : budget ≤ N := by
          simpa [EncodedType.inputSize_nat] using hBudget
        have hSlotNat : slot ≤ N := by
          simpa [EncodedType.inputSize_nat] using hSlot
        nlinarith
  | inr current =>
      have hBudget : EncodedType.nat.inputSize acc.1 ≤ N + 1 := by
        simpa [dhcEntryBoundaryFoldAccBound, N] using hAcc.1
      have hSlot : EncodedType.nat.inputSize acc.2.1 ≤ N + 1 := by
        simpa [dhcEntryBoundaryFoldAccBound, N] using hAcc.2.1
      have hCurrentInput : dhcIndexedIncidenceEncodedType.inputSize current ≤ N := by
        have hTagged : dhcIndexedIncidenceEncodedType.inputSize current + 1 ≤ N := by
          simpa [dhcEntryBoundaryInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum, N, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInstr
        omega
      have hCurrent : dhcIndexedIncidenceEncodedType.inputSize current ≤ N + 5 := by
        omega
      let out : List (Nat × Nat) := acc.2.2.2.2
      let block : List (Nat × Nat) :=
        dhcEntryBoundaryBlock
          (acc.1, (acc.2.1, (acc.2.2.1, (acc.2.2.2.1, current))))
      have hAppend :
          edgeListStructuredEncodedType.inputSize (out ++ block) =
            edgeListStructuredEncodedType.inputSize out +
              edgeListStructuredEncodedType.inputSize block := by
        simpa [edgeListStructuredEncodedType, block] using
          Clique.encodedList_inputSize_append edgeStructuredEncodedType out block
      have hBlock :
          edgeListStructuredEncodedType.inputSize block ≤ 120 * N + 200 := by
        simpa [block] using
          dhcEntryBoundaryBlock_inputSize_le N
            (acc.1, (acc.2.1, (acc.2.2.1, (acc.2.2.2.1, current))))
            hBudget hSlot hCurrent
      constructor
      · exact ⟨hBudget, hSlot, hCurrent⟩
      · simp [dhcEntryBoundaryFoldStep, dhcEntryBoundaryFoldRightStep,
          dhcEntryBoundaryAccEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_bool, dhcEntryBoundaryFoldGrowPolynomial_eval]
        change
          (show Nat from acc.1) + 1 + 1 +
                ((show Nat from acc.2.1) + 1 + 1 +
                  (EncodedType.bool.inputSize true + 1 +
                    (dhcIndexedIncidenceEncodedType.inputSize current + 1 +
                      edgeListStructuredEncodedType.inputSize (out ++ block)))) ≤
            (show Nat from acc.1) + 1 + 1 +
                ((show Nat from acc.2.1) + 1 + 1 +
                  (EncodedType.bool.inputSize acc.2.2.1 + 1 +
                    (dhcIndexedIncidenceEncodedType.inputSize acc.2.2.2.1 + 1 +
                      edgeListStructuredEncodedType.inputSize out))) +
              (160 * dhcEntryBoundaryInstructionListEncodedType.inputSize source + 400)
        rw [hAppend]
        simp [EncodedType.inputSize_bool]
        nlinarith [hBlock, hCurrent]

theorem dhcEntryBoundaryFold_tm_polytime :
    TMPolyTimeMap
      dhcEntryBoundaryInstructionListEncodedType
      dhcEntryBoundaryAccEncodedType
      (fun xs : List dhcEntryBoundaryInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => dhcEntryBoundaryFoldStep (acc, instr))
          dhcEntryBoundaryFoldInit) := by
  rcases dhcEntryBoundaryFoldStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      dhcEntryBoundaryInstructionEncodedType dhcEntryBoundaryAccEncodedType
      dhcEntryBoundaryFoldStep dhcEntryBoundaryFoldInit hStep
      (Polynomial.C 20) dhcEntryBoundaryFoldGrowPolynomial
      dhcEntryBoundaryFoldAccBound ?_ ?_
  · intro xs
    constructor
    · constructor
      · simp [dhcEntryBoundaryFoldInit, EncodedType.inputSize_nat]
      · constructor
        · simp [dhcEntryBoundaryFoldInit, EncodedType.inputSize_nat]
        · simp [dhcEntryBoundaryFoldInit, dhcEntryExitBoundaryDummyIncidence,
            dhcIndexedIncidenceEncodedType, vertexPairEncodedType,
            EncodedType.inputSize_prod, EncodedType.inputSize_nat]
    · have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
        exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
      simp [dhcEntryBoundaryFoldInit, dhcEntryBoundaryAccEncodedType,
        dhcEntryExitBoundaryDummyIncidence, dhcIndexedIncidenceEncodedType,
        vertexPairEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_nat,
        EncodedType.inputSize_bool, hNil]
  · intro source acc instr hAcc hInstr
    simpa [dhcEntryBoundaryInstructionListEncodedType] using
      dhcEntryBoundaryFoldStep_growth source acc instr hAcc hInstr

theorem dhcEntryBoundaryFoldResult_tm_polytime :
    TMPolyTimeMap
      dhcEntryBoundaryInstructionListEncodedType
      edgeListStructuredEncodedType
      dhcEntryBoundaryFoldResult := by
  have hTail :
      TMPolyTimeMap dhcEntryBoundaryAccEncodedType
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.bool
            (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)))
        (fun acc : dhcEntryBoundaryAccEncodedType.Carrier => acc.2) := by
    simpa [dhcEntryBoundaryAccEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.bool
            (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)))
  have hFlagTail :
      TMPolyTimeMap dhcEntryBoundaryAccEncodedType
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType))
        (fun acc : dhcEntryBoundaryAccEncodedType.Carrier => acc.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.bool
        (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType))
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp] using hComp
  have hInner :
      TMPolyTimeMap dhcEntryBoundaryAccEncodedType
        (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
        (fun acc : dhcEntryBoundaryAccEncodedType.Carrier => acc.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool
      (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hFlagTail
    simpa [Function.comp] using hComp
  have hEdges :
      TMPolyTimeMap dhcEntryBoundaryAccEncodedType edgeListStructuredEncodedType
        (fun acc : dhcEntryBoundaryAccEncodedType.Carrier => acc.2.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInner
    simpa [Function.comp] using hComp
  have hComp := TMPolyTimeMap.comp hEdges dhcEntryBoundaryFold_tm_polytime
  simpa [Function.comp, dhcEntryBoundaryFoldResult] using hComp

theorem dhcEntryArcsForSlotFromBoundaryIndexedExecutable_tm_polytime :
    TMPolyTimeMap dhcSlotIndexedIncidenceListEncodedType
      edgeListStructuredEncodedType
      dhcEntryArcsForSlotFromBoundaryIndexedExecutable := by
  have hComp :=
    TMPolyTimeMap.comp dhcEntryBoundaryFoldResult_tm_polytime
      dhcEntryBoundaryInstructions_tm_polytime
  simpa [Function.comp, dhcEntryArcsForSlotFromBoundaryIndexedExecutable] using hComp

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
