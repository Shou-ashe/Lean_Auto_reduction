/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.EntryExitBoundarySemantics

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

/-!
Executable slot-boundary scan for exit arcs.

Unlike entry arcs, exit arcs are emitted for the previous incidence when the scan
leaves a source block, plus one final arc for the last incidence in a nonempty
block.  The fold below keeps that final arc pending until result extraction.
-/

abbrev dhcExitBoundaryBlockInputEncodedType := dhcEntryBoundaryBlockInputEncodedType

abbrev dhcExitBoundaryBlockRaw := dhcEntryBoundaryBlockRaw

def dhcExitBoundaryBlock (p : dhcExitBoundaryBlockRaw) : List (Nat × Nat) :=
  match p.2.2.1 with
  | true =>
      match dhcBoundarySameSourceBool p.2.2.2.1 p.2.2.2.2 with
      | true => []
      | false => dhcExitArcForSlotBlockFromIndexed p.1 p.2.1 p.2.2.2.1
  | false => []

theorem dhcExitBoundaryBlock_tm_polytime :
    TMPolyTimeMap dhcExitBoundaryBlockInputEncodedType
      edgeListStructuredEncodedType
      dhcExitBoundaryBlock := by
  let X := dhcExitBoundaryBlockInputEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcExitBoundaryBlockInputEncodedType, dhcEntryBoundaryBlockInputEncodedType] using
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
    simpa [X, dhcExitBoundaryBlockInputEncodedType, dhcEntryBoundaryBlockInputEncodedType] using
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
      TMPolyTimeMap X dhcExitArcForSlotFromIndexedInputEncodedType
        (fun p : X.Carrier => (p.1, (p.2.1, p.2.2.2.1))) :=
    TMPolyTimeMap.prod_mk hBudget (TMPolyTimeMap.prod_mk hSlot hPrev)
  have hSingleton :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier =>
          dhcExitArcForSlotBlockFromIndexed p.1 p.2.1 p.2.2.2.1) := by
    have hComp := TMPolyTimeMap.comp dhcExitArcForSlotBlockFromIndexed_tm_polytime hArcInput
    simpa [Function.comp, X, dhcExitArcForSlotFromIndexedInputEncodedType,
      dhcEntryArcForSlotFromIndexedInputEncodedType] using hComp
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
          | false => dhcExitArcForSlotBlockFromIndexed p.2.1 p.2.2.1 p.2.2.2.2.1) :=
    graphBoolProduct_dispatch_tm_polytime X edgeListStructuredEncodedType
      (fFalse := fun p : X.Carrier =>
        dhcExitArcForSlotBlockFromIndexed p.1 p.2.1 p.2.2.2.1)
      (fTrue := fun _ : X.Carrier => ([] : List (Nat × Nat)))
      hSingleton hEmpty
  have hSameBlock :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier =>
          match dhcBoundarySameSourceBool p.2.2.2.1 p.2.2.2.2 with
          | true => []
          | false => dhcExitArcForSlotBlockFromIndexed p.1 p.2.1 p.2.2.2.1) := by
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
                  dhcExitArcForSlotBlockFromIndexed p.2.1 p.2.2.1 p.2.2.2.2.1
          | false => ([] : List (Nat × Nat))) :=
    graphBoolProduct_dispatch_tm_polytime X edgeListStructuredEncodedType
      (fFalse := fun _ : X.Carrier => ([] : List (Nat × Nat)))
      (fTrue := fun p : X.Carrier =>
        match dhcBoundarySameSourceBool p.2.2.2.1 p.2.2.2.2 with
        | true => []
        | false => dhcExitArcForSlotBlockFromIndexed p.1 p.2.1 p.2.2.2.1)
      hEmpty hSameBlock
  have hComp := TMPolyTimeMap.comp hActiveDispatch hActivePayload
  simpa [Function.comp, dhcExitBoundaryBlock] using hComp

abbrev dhcExitBoundaryAccEncodedType := dhcEntryBoundaryAccEncodedType
abbrev dhcExitBoundaryPayloadEncodedType := dhcEntryBoundaryPayloadEncodedType
abbrev dhcExitBoundaryInstructionEncodedType := dhcEntryBoundaryInstructionEncodedType
abbrev dhcExitBoundaryInstructionListEncodedType := dhcEntryBoundaryInstructionListEncodedType

def dhcExitBoundaryFoldInit : dhcExitBoundaryAccEncodedType.Carrier :=
  dhcEntryBoundaryFoldInit

def dhcExitBoundaryFoldLeftStep
    (payload : dhcExitBoundaryPayloadEncodedType.Carrier) :
    dhcExitBoundaryAccEncodedType.Carrier :=
  dhcEntryBoundaryFoldLeftStep payload

def dhcExitBoundaryFoldRightStep
    (p : dhcExitBoundaryAccEncodedType.Carrier ×
      dhcIndexedIncidenceEncodedType.Carrier) :
    dhcExitBoundaryAccEncodedType.Carrier :=
  (p.1.1,
    (p.1.2.1,
      (true,
        (p.2,
          (show List (Nat × Nat) from p.1.2.2.2.2) ++
            dhcExitBoundaryBlock (p.1.1, (p.1.2.1, (p.1.2.2.1, (p.1.2.2.2.1, p.2))))))))

def dhcExitBoundaryFoldStep
    (p : dhcExitBoundaryAccEncodedType.Carrier ×
      dhcExitBoundaryInstructionEncodedType.Carrier) :
    dhcExitBoundaryAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl payload => dhcExitBoundaryFoldLeftStep payload
  | Sum.inr inc => dhcExitBoundaryFoldRightStep (p.1, inc)

def dhcExitBoundaryInstructions
    (p : dhcSlotIndexedIncidenceListRaw) :
    dhcExitBoundaryInstructionListEncodedType.Carrier :=
  dhcEntryBoundaryInstructions p

def dhcExitBoundaryFinalBlock
    (acc : dhcExitBoundaryAccEncodedType.Carrier) : List (Nat × Nat) :=
  match acc.2.2.1 with
  | true => dhcExitArcForSlotBlockFromIndexed acc.1 acc.2.1 acc.2.2.2.1
  | false => []

def dhcExitBoundaryFoldResult
    (instrs : dhcExitBoundaryInstructionListEncodedType.Carrier) :
    List (Nat × Nat) :=
  let acc :=
    instrs.foldl (fun acc instr => dhcExitBoundaryFoldStep (acc, instr))
      dhcExitBoundaryFoldInit
  (show List (Nat × Nat) from acc.2.2.2.2) ++ dhcExitBoundaryFinalBlock acc

def dhcExitArcsForSlotFromBoundaryIndexedExecutable
    (p : dhcSlotIndexedIncidenceListRaw) : List (Nat × Nat) :=
  dhcExitBoundaryFoldResult (dhcExitBoundaryInstructions p)

theorem dhcExitBoundaryFoldLeftStep_tm_polytime :
    TMPolyTimeMap dhcExitBoundaryPayloadEncodedType dhcExitBoundaryAccEncodedType
      dhcExitBoundaryFoldLeftStep := by
  simpa [dhcExitBoundaryFoldLeftStep, dhcExitBoundaryPayloadEncodedType,
    dhcExitBoundaryAccEncodedType] using dhcEntryBoundaryFoldLeftStep_tm_polytime

theorem dhcExitBoundaryFoldRightStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod dhcExitBoundaryAccEncodedType dhcIndexedIncidenceEncodedType)
      dhcExitBoundaryAccEncodedType
      dhcExitBoundaryFoldRightStep := by
  let X := EncodedType.prod dhcExitBoundaryAccEncodedType dhcIndexedIncidenceEncodedType
  have hAcc : TMPolyTimeMap X dhcExitBoundaryAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, dhcExitBoundaryAccEncodedType] using TMPolyTimeMap.fst
      dhcEntryBoundaryAccEncodedType dhcIndexedIncidenceEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)))
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, dhcExitBoundaryAccEncodedType, dhcEntryBoundaryAccEncodedType, X]
      using hComp
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
    simpa [Function.comp, dhcExitBoundaryAccEncodedType, dhcEntryBoundaryAccEncodedType, X]
      using hComp
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
    simpa [X, dhcExitBoundaryAccEncodedType] using TMPolyTimeMap.snd
      dhcEntryBoundaryAccEncodedType dhcIndexedIncidenceEncodedType
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
      TMPolyTimeMap X dhcExitBoundaryBlockInputEncodedType
        (fun p : X.Carrier =>
          (p.1.1, (p.1.2.1, (p.1.2.2.1, (p.1.2.2.2.1, p.2))))) :=
    TMPolyTimeMap.prod_mk hBudget hBlockTail
  have hBlock :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier =>
          dhcExitBoundaryBlock
            (p.1.1, (p.1.2.1, (p.1.2.2.1, (p.1.2.2.2.1, p.2))))) := by
    have hComp := TMPolyTimeMap.comp dhcExitBoundaryBlock_tm_polytime hBlockInput
    simpa [Function.comp, dhcExitBoundaryBlockInputEncodedType,
      dhcEntryBoundaryBlockInputEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier =>
          (p.1.2.2.2.2,
            dhcExitBoundaryBlock
              (p.1.1, (p.1.2.1, (p.1.2.2.1, (p.1.2.2.2.1, p.2)))))) :=
    TMPolyTimeMap.prod_mk hOutEdges hBlock
  have hAppend :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier =>
          (show List (Nat × Nat) from p.1.2.2.2.2) ++
            dhcExitBoundaryBlock
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
              dhcExitBoundaryBlock
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
                dhcExitBoundaryBlock
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
                  dhcExitBoundaryBlock
                    (p.1.1, (p.1.2.1, (p.1.2.2.1, (p.1.2.2.2.1, p.2)))))))) :=
    TMPolyTimeMap.prod_mk hSlot hNewFlagTail
  have hOut := TMPolyTimeMap.prod_mk hBudget hNewTail
  simpa [dhcExitBoundaryFoldRightStep, dhcExitBoundaryAccEncodedType,
    dhcEntryBoundaryAccEncodedType, X] using hOut

theorem dhcExitBoundaryFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod dhcExitBoundaryAccEncodedType dhcExitBoundaryInstructionEncodedType)
      dhcExitBoundaryAccEncodedType
      dhcExitBoundaryFoldStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      dhcExitBoundaryAccEncodedType dhcExitBoundaryPayloadEncodedType
      dhcIndexedIncidenceEncodedType
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim dhcExitBoundaryFoldLeftStep_tm_polytime
      dhcExitBoundaryFoldRightStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem dhcExitBoundaryInstructions_tm_polytime :
    TMPolyTimeMap dhcSlotIndexedIncidenceListEncodedType
      dhcExitBoundaryInstructionListEncodedType
      dhcExitBoundaryInstructions := by
  simpa [dhcExitBoundaryInstructions, dhcExitBoundaryInstructionListEncodedType] using
    dhcEntryBoundaryInstructions_tm_polytime

def dhcExitBoundaryFoldAccBound
    (N : Nat) (acc : dhcExitBoundaryAccEncodedType.Carrier) : Prop :=
  dhcEntryBoundaryFoldAccBound N acc

noncomputable def dhcExitBoundaryFoldGrowPolynomial : Polynomial Nat :=
  dhcEntryBoundaryFoldGrowPolynomial

theorem dhcExitBoundaryFoldGrowPolynomial_eval (N : Nat) :
    dhcExitBoundaryFoldGrowPolynomial.eval N = 160 * N + 400 := by
  simpa [dhcExitBoundaryFoldGrowPolynomial] using dhcEntryBoundaryFoldGrowPolynomial_eval N

theorem dhcExitArcForSlotBlockFromIndexed_inputSize_le
    (N budget slot : Nat) (inc : dhcIndexedIncidenceEncodedType.Carrier)
    (hBudget : EncodedType.nat.inputSize budget ≤ N + 1)
    (hSlot : EncodedType.nat.inputSize slot ≤ N + 1)
    (hInc : dhcIndexedIncidenceEncodedType.inputSize inc ≤ N + 5) :
    edgeListStructuredEncodedType.inputSize
        (dhcExitArcForSlotBlockFromIndexed budget slot inc) ≤
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
  have hNextNat : dhcNextSelectorFromBudget budget slot ≤ N := by
    by_cases hZero : budget = 0
    · simp [dhcNextSelectorFromBudget, hZero]
    · have hPos : 0 < budget := Nat.pos_of_ne_zero hZero
      have hModLt : (slot + 1) % budget < budget := Nat.mod_lt _ hPos
      simpa [dhcNextSelectorFromBudget, hZero] using
        (Nat.le_of_lt hModLt).trans hBudgetNat
  simp [dhcExitArcForSlotBlockFromIndexed, dhcExitArcForSlotFromIndexedRaw,
    dhcIncidenceVertexCode, textbookSelectorVertex, natDouble,
    edgeListStructuredEncodedType, edgeStructuredEncodedType, EncodedType.inputSize,
    EncodedType.list, EncodedType.prod, EncodedType.nat]
  nlinarith

theorem dhcExitBoundaryBlock_inputSize_le
    (N : Nat) (p : dhcExitBoundaryBlockRaw)
    (hBudget : EncodedType.nat.inputSize p.1 ≤ N + 1)
    (hSlot : EncodedType.nat.inputSize p.2.1 ≤ N + 1)
    (hPrev : dhcIndexedIncidenceEncodedType.inputSize p.2.2.2.1 ≤ N + 5) :
    edgeListStructuredEncodedType.inputSize (dhcExitBoundaryBlock p) ≤
      120 * N + 200 := by
  rcases p with ⟨budget, slot, active, prev, current⟩
  cases active
  · have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
      exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
    simp [dhcExitBoundaryBlock, hNil]
  · by_cases hSame :
        dhcBoundaryIncidenceSource prev = dhcBoundaryIncidenceSource current
    · have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
        exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
      have hSameRaw : (prev.1.1 : Nat) = (current.1.1 : Nat) := by
        simpa [dhcBoundaryIncidenceSource] using hSame
      have hBeq : Nat.beq (prev.1.1 : Nat) (current.1.1 : Nat) = true := by
        rw [Nat.beq_eq]
        exact hSameRaw
      simp [dhcExitBoundaryBlock, dhcBoundarySameSourceBool, dhcBoundaryIncidenceSource,
        hBeq, hNil]
    · have hSameRaw : ¬(prev.1.1 : Nat) = (current.1.1 : Nat) := by
        simpa [dhcBoundaryIncidenceSource] using hSame
      have hBeq : Nat.beq (prev.1.1 : Nat) (current.1.1 : Nat) = false := by
        rw [← Bool.not_eq_true, Nat.beq_eq]
        exact hSameRaw
      simpa [dhcExitBoundaryBlock, dhcBoundarySameSourceBool,
        dhcBoundaryIncidenceSource, hBeq] using
        dhcExitArcForSlotBlockFromIndexed_inputSize_le N budget slot prev
          hBudget hSlot hPrev

theorem dhcExitBoundaryFoldStep_growth
    (source : List dhcExitBoundaryInstructionEncodedType.Carrier)
    (acc : dhcExitBoundaryAccEncodedType.Carrier)
    (instr : dhcExitBoundaryInstructionEncodedType.Carrier)
    (hAcc :
      dhcExitBoundaryFoldAccBound
        (dhcExitBoundaryInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      dhcExitBoundaryInstructionEncodedType.inputSize instr ≤
        dhcExitBoundaryInstructionListEncodedType.inputSize source) :
    dhcExitBoundaryFoldAccBound
        (dhcExitBoundaryInstructionListEncodedType.inputSize source)
        (dhcExitBoundaryFoldStep (acc, instr)) ∧
      dhcExitBoundaryAccEncodedType.inputSize (dhcExitBoundaryFoldStep (acc, instr)) ≤
        dhcExitBoundaryAccEncodedType.inputSize acc +
          dhcExitBoundaryFoldGrowPolynomial.eval
            (dhcExitBoundaryInstructionListEncodedType.inputSize source) := by
  let N := dhcExitBoundaryInstructionListEncodedType.inputSize source
  cases instr with
  | inl payload =>
      have hEntry :=
        dhcEntryBoundaryFoldStep_growth source acc (Sum.inl payload) hAcc hInstr
      simpa [dhcExitBoundaryFoldStep, dhcExitBoundaryFoldLeftStep,
        dhcExitBoundaryFoldAccBound, dhcExitBoundaryAccEncodedType,
        dhcExitBoundaryInstructionListEncodedType, dhcExitBoundaryFoldGrowPolynomial] using hEntry
  | inr current =>
      have hBudget : EncodedType.nat.inputSize acc.1 ≤ N + 1 := by
        simpa [dhcExitBoundaryFoldAccBound, dhcEntryBoundaryFoldAccBound, N] using hAcc.1
      have hSlot : EncodedType.nat.inputSize acc.2.1 ≤ N + 1 := by
        simpa [dhcExitBoundaryFoldAccBound, dhcEntryBoundaryFoldAccBound, N] using hAcc.2.1
      have hPrev : dhcIndexedIncidenceEncodedType.inputSize acc.2.2.2.1 ≤ N + 5 := by
        simpa [dhcExitBoundaryFoldAccBound, dhcEntryBoundaryFoldAccBound, N] using hAcc.2.2
      have hCurrentInput : dhcIndexedIncidenceEncodedType.inputSize current ≤ N := by
        have hTagged : dhcIndexedIncidenceEncodedType.inputSize current + 1 ≤ N := by
          simpa [dhcExitBoundaryInstructionEncodedType, dhcEntryBoundaryInstructionEncodedType,
            EncodedType.inputSize, EncodedType.sum, N, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using hInstr
        omega
      have hCurrent : dhcIndexedIncidenceEncodedType.inputSize current ≤ N + 5 := by
        omega
      let out : List (Nat × Nat) := acc.2.2.2.2
      let block : List (Nat × Nat) :=
        dhcExitBoundaryBlock
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
          dhcExitBoundaryBlock_inputSize_le N
            (acc.1, (acc.2.1, (acc.2.2.1, (acc.2.2.2.1, current))))
            hBudget hSlot hPrev
      constructor
      · exact ⟨hBudget, hSlot, hCurrent⟩
      · simp [dhcExitBoundaryFoldStep, dhcExitBoundaryFoldRightStep,
          dhcEntryBoundaryAccEncodedType,
          EncodedType.inputSize_prod, EncodedType.inputSize_bool,
          dhcExitBoundaryFoldGrowPolynomial_eval]
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
              (160 * dhcExitBoundaryInstructionListEncodedType.inputSize source + 400)
        rw [hAppend]
        simp [EncodedType.inputSize_bool]
        nlinarith [hBlock, hCurrent]

theorem dhcExitBoundaryFold_tm_polytime :
    TMPolyTimeMap
      dhcExitBoundaryInstructionListEncodedType
      dhcExitBoundaryAccEncodedType
      (fun xs : List dhcExitBoundaryInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => dhcExitBoundaryFoldStep (acc, instr))
          dhcExitBoundaryFoldInit) := by
  rcases dhcExitBoundaryFoldStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      dhcExitBoundaryInstructionEncodedType dhcExitBoundaryAccEncodedType
      dhcExitBoundaryFoldStep dhcExitBoundaryFoldInit hStep
      (Polynomial.C 20) dhcExitBoundaryFoldGrowPolynomial
      dhcExitBoundaryFoldAccBound ?_ ?_
  · intro xs
    have hEntry :=
      (show dhcEntryBoundaryFoldAccBound
          (dhcEntryBoundaryInstructionListEncodedType.inputSize xs)
          dhcEntryBoundaryFoldInit ∧
        dhcEntryBoundaryAccEncodedType.inputSize dhcEntryBoundaryFoldInit ≤
          (Polynomial.C 20).eval
            (dhcEntryBoundaryInstructionListEncodedType.inputSize xs) from by
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
            EncodedType.inputSize_bool, hNil])
    simpa [dhcExitBoundaryFoldInit, dhcExitBoundaryFoldAccBound,
      dhcExitBoundaryInstructionListEncodedType, dhcExitBoundaryAccEncodedType,
      dhcEntryBoundaryAccEncodedType] using hEntry
  · intro source acc instr hAcc hInstr
    simpa [dhcExitBoundaryInstructionListEncodedType] using
      dhcExitBoundaryFoldStep_growth source acc instr hAcc hInstr

theorem dhcExitBoundaryFinalBlock_tm_polytime :
    TMPolyTimeMap dhcExitBoundaryAccEncodedType
      edgeListStructuredEncodedType
      dhcExitBoundaryFinalBlock := by
  let X := dhcExitBoundaryAccEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun acc : X.Carrier => acc.1) := by
    simpa [X, dhcExitBoundaryAccEncodedType, dhcEntryBoundaryAccEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.bool
            (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)))
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.bool
            (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)))
        (fun acc : X.Carrier => acc.2) := by
    simpa [X, dhcExitBoundaryAccEncodedType, dhcEntryBoundaryAccEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.bool
            (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)))
  have hSlot : TMPolyTimeMap X EncodedType.nat (fun acc : X.Carrier => acc.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.bool
        (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType))
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hFlagTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType))
        (fun acc : X.Carrier => acc.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.bool
        (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType))
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hActive : TMPolyTimeMap X EncodedType.bool (fun acc : X.Carrier => acc.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool
      (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hFlagTail
    simpa [Function.comp, X] using hComp
  have hInner :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
        (fun acc : X.Carrier => acc.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool
      (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hFlagTail
    simpa [Function.comp, X] using hComp
  have hPrev :
      TMPolyTimeMap X dhcIndexedIncidenceEncodedType (fun acc : X.Carrier => acc.2.2.2.1) := by
    have hFst := TMPolyTimeMap.fst dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInner
    simpa [Function.comp, X] using hComp
  have hArcInput :
      TMPolyTimeMap X dhcExitArcForSlotFromIndexedInputEncodedType
        (fun acc : X.Carrier => (acc.1, (acc.2.1, acc.2.2.2.1))) :=
    TMPolyTimeMap.prod_mk hBudget (TMPolyTimeMap.prod_mk hSlot hPrev)
  have hSingleton :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun acc : X.Carrier =>
          dhcExitArcForSlotBlockFromIndexed acc.1 acc.2.1 acc.2.2.2.1) := by
    have hComp := TMPolyTimeMap.comp dhcExitArcForSlotBlockFromIndexed_tm_polytime hArcInput
    simpa [Function.comp, dhcExitArcForSlotFromIndexedInputEncodedType,
      dhcEntryArcForSlotFromIndexedInputEncodedType, X] using hComp
  have hEmpty :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun _ : X.Carrier => ([] : List (Nat × Nat))) :=
    TMPolyTimeMap.const X edgeListStructuredEncodedType []
  have hActivePayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun acc : X.Carrier => (acc.2.2.1, acc)) :=
    TMPolyTimeMap.prod_mk hActive (TMPolyTimeMap.id X)
  have hDispatch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X)
        edgeListStructuredEncodedType
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true => dhcExitArcForSlotBlockFromIndexed p.2.1 p.2.2.1 p.2.2.2.2.1
          | false => ([] : List (Nat × Nat))) :=
    graphBoolProduct_dispatch_tm_polytime X edgeListStructuredEncodedType
      (fFalse := fun _ : X.Carrier => ([] : List (Nat × Nat)))
      (fTrue := fun acc : X.Carrier =>
        dhcExitArcForSlotBlockFromIndexed acc.1 acc.2.1 acc.2.2.2.1)
      hEmpty hSingleton
  have hComp := TMPolyTimeMap.comp hDispatch hActivePayload
  simpa [Function.comp, dhcExitBoundaryFinalBlock, X] using hComp

theorem dhcExitBoundaryAccResult_tm_polytime :
    TMPolyTimeMap dhcExitBoundaryAccEncodedType
      edgeListStructuredEncodedType
      (fun acc : dhcExitBoundaryAccEncodedType.Carrier =>
        (show List (Nat × Nat) from acc.2.2.2.2) ++
          dhcExitBoundaryFinalBlock acc) := by
  let X := dhcExitBoundaryAccEncodedType
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.bool
            (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)))
        (fun acc : X.Carrier => acc.2) := by
    simpa [X, dhcExitBoundaryAccEncodedType, dhcEntryBoundaryAccEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.bool
            (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)))
  have hFlagTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType))
        (fun acc : X.Carrier => acc.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.bool
        (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType))
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hInner :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
        (fun acc : X.Carrier => acc.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool
      (EncodedType.prod dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hFlagTail
    simpa [Function.comp, X] using hComp
  have hEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun acc : X.Carrier => acc.2.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd dhcIndexedIncidenceEncodedType edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInner
    simpa [Function.comp, X] using hComp
  have hInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun acc : X.Carrier =>
          ((show List (Nat × Nat) from acc.2.2.2.2), dhcExitBoundaryFinalBlock acc)) :=
    TMPolyTimeMap.prod_mk hEdges dhcExitBoundaryFinalBlock_tm_polytime
  have hComp := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append edgeStructuredEncodedType) hInput
  simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp

theorem dhcExitBoundaryFoldResult_tm_polytime :
    TMPolyTimeMap
      dhcExitBoundaryInstructionListEncodedType
      edgeListStructuredEncodedType
      dhcExitBoundaryFoldResult := by
  have hComp := TMPolyTimeMap.comp
    dhcExitBoundaryAccResult_tm_polytime dhcExitBoundaryFold_tm_polytime
  simpa [Function.comp, dhcExitBoundaryFoldResult] using hComp

theorem dhcExitArcsForSlotFromBoundaryIndexedExecutable_tm_polytime :
    TMPolyTimeMap dhcSlotIndexedIncidenceListEncodedType
      edgeListStructuredEncodedType
      dhcExitArcsForSlotFromBoundaryIndexedExecutable := by
  have hComp :=
    TMPolyTimeMap.comp dhcExitBoundaryFoldResult_tm_polytime
      dhcExitBoundaryInstructions_tm_polytime
  simpa [Function.comp, dhcExitArcsForSlotFromBoundaryIndexedExecutable] using hComp

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
