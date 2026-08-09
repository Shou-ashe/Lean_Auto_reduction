/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SetCovering.Base

/-!
TM-backed incidence-list runner for the Vertex Cover to Set Covering route.
-/

namespace ComplexityReduction
namespace Karp21
namespace SetCovering

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-! ### TM-facing incidence instruction layer -/

def incidentEdgePayloadEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat edgeStructuredEncodedType

def incidentEdgeInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool incidentEdgePayloadEncodedType

def incidentEdgeInstructionListEncodedType : EncodedType :=
  EncodedType.list incidentEdgeInstructionEncodedType

def incidentEdgeInstructionInputEncodedType : EncodedType :=
  EncodedType.prod edgeListStructuredEncodedType EncodedType.nat

def incidentEdgeScanAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))

def incidentEdgeScanInputEncodedType : EncodedType :=
  EncodedType.prod incidentEdgeScanAccEncodedType incidentEdgeInstructionEncodedType

def incidentEdgeInitInstruction (v : Nat) :
    Bool × (Nat × (Nat × Nat)) :=
  (false, (v, ((0 : Nat), (0 : Nat))))

def incidentEdgeEdgeInstruction (e : Nat × Nat) :
    Bool × (Nat × (Nat × Nat)) :=
  (true, ((0 : Nat), e))

def incidentEdgeInstructions
    (p : List (Nat × Nat) × Nat) :
    List (Bool × (Nat × (Nat × Nat))) :=
  incidentEdgeInitInstruction p.2 :: p.1.map incidentEdgeEdgeInstruction

def edgeIncidentBool (p : Nat × (Nat × Nat)) : Bool :=
  graphBoolOrPair (decide (p.2.1 = p.1), decide (p.2.2 = p.1))

def incidentEdgeScanInit : Nat × (Nat × List Nat) :=
  (0, (0, []))

def incidentEdgeScanStep
    (p : (Nat × (Nat × List Nat)) × (Bool × (Nat × (Nat × Nat)))) :
    Nat × (Nat × List Nat) :=
  if p.2.1 then
    let vertex := p.1.1
    let next := p.1.2.1
    let out := p.1.2.2
    let edge := p.2.2.2
    if edgeIncidentBool (vertex, edge) then
      (vertex, (next + 1, out ++ [next]))
    else
      (vertex, (next + 1, out))
  else
    (p.2.2.1, (0, []))

def incidentEdgeIndicesFromInstructions
    (xs : List (Bool × (Nat × (Nat × Nat)))) : List Nat :=
  (xs.foldl (fun acc x => incidentEdgeScanStep (acc, x)) incidentEdgeScanInit).2.2

def incidentEdgeIndicesFromEdges
    (p : List (Nat × Nat) × Nat) : List Nat :=
  incidentEdgeIndicesFromInstructions (incidentEdgeInstructions p)

theorem edgeIncidentBool_eq_true_iff (p : Nat × (Nat × Nat)) :
    edgeIncidentBool p = true ↔ p.2.1 = p.1 ∨ p.2.2 = p.1 := by
  simp [edgeIncidentBool, graphBoolOrPair_eq_true_iff]

theorem edgeIncidentBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat edgeStructuredEncodedType)
      EncodedType.bool
      edgeIncidentBool := by
  let X := EncodedType.prod EncodedType.nat edgeStructuredEncodedType
  have hVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.nat edgeStructuredEncodedType
  have hEdge : TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.nat edgeStructuredEncodedType
  have hLeftEndpoint : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hEdge
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hRightEndpoint : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hEdge
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hLeftEqInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.1, p.1)) :=
    TMPolyTimeMap.prod_mk hLeftEndpoint hVertex
  have hRightEqInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.2, p.1)) :=
    TMPolyTimeMap.prod_mk hRightEndpoint hVertex
  have hLeftEq := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hLeftEqInput
  have hRightEq := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hRightEqInput
  have hPair :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : Nat × (Nat × Nat) =>
          (decide (p.2.1 = p.1), decide (p.2.2 = p.1))) :=
    TMPolyTimeMap.prod_mk hLeftEq hRightEq
  have hOut := TMPolyTimeMap.comp graphBoolOrPair_tm_polytime hPair
  simpa [Function.comp, edgeIncidentBool, X] using hOut

theorem incidentEdgeEdgeInstruction_tm_polytime :
    TMPolyTimeMap
      edgeStructuredEncodedType
      incidentEdgeInstructionEncodedType
      incidentEdgeEdgeInstruction := by
  let X := edgeStructuredEncodedType
  have hTrue : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hPayload :
      TMPolyTimeMap X incidentEdgePayloadEncodedType
        (fun e : X.Carrier => ((0 : Nat), e)) :=
    TMPolyTimeMap.prod_mk hZero (TMPolyTimeMap.id X)
  have hInstruction :
      TMPolyTimeMap X incidentEdgeInstructionEncodedType
        (fun e : X.Carrier => (true, ((0 : Nat), e))) :=
    TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [incidentEdgeEdgeInstruction, X, incidentEdgeInstructionEncodedType,
    incidentEdgePayloadEncodedType] using hInstruction

theorem incidentEdgeInstructions_tm_polytime :
    TMPolyTimeMap
      incidentEdgeInstructionInputEncodedType
      incidentEdgeInstructionListEncodedType
      incidentEdgeInstructions := by
  let X := incidentEdgeInstructionInputEncodedType
  have hEdges : TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, incidentEdgeInstructionInputEncodedType] using
      TMPolyTimeMap.fst edgeListStructuredEncodedType EncodedType.nat
  have hVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X, incidentEdgeInstructionInputEncodedType] using
      TMPolyTimeMap.snd edgeListStructuredEncodedType EncodedType.nat
  have hFalse : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hDefaultEdge :
      TMPolyTimeMap X edgeStructuredEncodedType
        (fun _ : X.Carrier => ((0 : Nat), (0 : Nat))) :=
    TMPolyTimeMap.const X edgeStructuredEncodedType ((0 : Nat), (0 : Nat))
  have hInitPayload :
      TMPolyTimeMap X incidentEdgePayloadEncodedType
        (fun p : X.Carrier => (p.2, ((0 : Nat), (0 : Nat)))) :=
    TMPolyTimeMap.prod_mk hVertex hDefaultEdge
  have hInitInstruction :
      TMPolyTimeMap X incidentEdgeInstructionEncodedType
        (fun p : X.Carrier => incidentEdgeInitInstruction p.2) := by
    have hPair := TMPolyTimeMap.prod_mk hFalse hInitPayload
    simpa [incidentEdgeInitInstruction, incidentEdgeInstructionEncodedType,
      incidentEdgePayloadEncodedType] using hPair
  have hInitSingleton :
      TMPolyTimeMap X incidentEdgeInstructionListEncodedType
        (fun p : X.Carrier => [incidentEdgeInitInstruction p.2]) := by
    have hComp :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.list_singleton incidentEdgeInstructionEncodedType)
        hInitInstruction
    simpa [Function.comp, incidentEdgeInstructionListEncodedType] using hComp
  have hEdgeInstructions :
      TMPolyTimeMap X incidentEdgeInstructionListEncodedType
        (fun p : X.Carrier => p.1.map incidentEdgeEdgeInstruction) := by
    have hMap :=
      TMPolyTimeMap.list_map incidentEdgeEdgeInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hEdges
    simpa [Function.comp, incidentEdgeInstructionListEncodedType] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod incidentEdgeInstructionListEncodedType
          incidentEdgeInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([incidentEdgeInitInstruction p.2],
            p.1.map incidentEdgeEdgeInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hEdgeInstructions
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append incidentEdgeInstructionEncodedType) hAppendInput
  simpa [Function.comp, incidentEdgeInstructions, incidentEdgeInstructionListEncodedType]
    using hAppend

theorem incidentEdgeScanStep_tm_polytime :
    TMPolyTimeMap
      incidentEdgeScanInputEncodedType
      incidentEdgeScanAccEncodedType
      incidentEdgeScanStep := by
  let X := incidentEdgeScanInputEncodedType
  let A := incidentEdgeScanAccEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X, incidentEdgeScanInputEncodedType] using
      TMPolyTimeMap.fst incidentEdgeScanAccEncodedType incidentEdgeInstructionEncodedType
  have hInstruction :
      TMPolyTimeMap X incidentEdgeInstructionEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, incidentEdgeScanInputEncodedType] using
      TMPolyTimeMap.snd incidentEdgeScanAccEncodedType incidentEdgeInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool incidentEdgePayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstruction
    simpa [Function.comp, incidentEdgeInstructionEncodedType, X] using hComp
  have hPayload :
      TMPolyTimeMap X incidentEdgePayloadEncodedType (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool incidentEdgePayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstruction
    simpa [Function.comp, incidentEdgeInstructionEncodedType, X] using hComp
  have hPayloadVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat edgeStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, incidentEdgePayloadEncodedType, X] using hComp
  have hPayloadEdge :
      TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat edgeStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, incidentEdgePayloadEncodedType, X] using hComp
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hEmptyNatList :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat) (fun _ : X.Carrier => ([] : List Nat)) :=
    TMPolyTimeMap.const X (EncodedType.list EncodedType.nat) ([] : List Nat)
  have hInitTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
        (fun _ : X.Carrier => ((0 : Nat), ([] : List Nat))) :=
    TMPolyTimeMap.prod_mk hZero hEmptyNatList
  have hInitBranch :
      TMPolyTimeMap X A (fun p : X.Carrier => (p.2.2.1, ((0 : Nat), ([] : List Nat)))) :=
    TMPolyTimeMap.prod_mk hPayloadVertex hInitTail
  have hAccVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, incidentEdgeScanAccEncodedType, X] using hComp
  have hAccTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
        (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, incidentEdgeScanAccEncodedType, X] using hComp
  have hAccNext : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat (EncodedType.list EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hFst hAccTail
    simpa [Function.comp, X] using hComp
  have hAccOut :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat) (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat (EncodedType.list EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hAccTail
    simpa [Function.comp, X] using hComp
  have hNextSucc : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => Nat.succ p.1.2.1) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hAccNext
    simpa [Function.comp, X] using hComp
  have hNextSingleton :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier => ([p.1.2.1] : List Nat)) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton EncodedType.nat) hAccNext
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod (EncodedType.list EncodedType.nat)
          (EncodedType.list EncodedType.nat))
        (fun p : X.Carrier => (p.1.2.2, ([p.1.2.1] : List Nat))) :=
    TMPolyTimeMap.prod_mk hAccOut hNextSingleton
  have hOutAppend :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier =>
          List.append (p.1.2.2 : List Nat) ([p.1.2.1] : List Nat)) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append EncodedType.nat) hAppendInput
    simpa [Function.comp, X] using hComp
  have hHitTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
        (fun p : X.Carrier =>
          (Nat.succ p.1.2.1,
            List.append (p.1.2.2 : List Nat) ([p.1.2.1] : List Nat))) :=
    TMPolyTimeMap.prod_mk hNextSucc hOutAppend
  have hMissTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
        (fun p : X.Carrier => (Nat.succ p.1.2.1, (p.1.2.2 : List Nat))) :=
    TMPolyTimeMap.prod_mk hNextSucc hAccOut
  have hHit :
      TMPolyTimeMap X A
        (fun p : X.Carrier =>
          (p.1.1,
            (Nat.succ p.1.2.1,
              List.append (p.1.2.2 : List Nat) ([p.1.2.1] : List Nat)))) :=
    TMPolyTimeMap.prod_mk hAccVertex hHitTail
  have hMiss :
      TMPolyTimeMap X A
        (fun p : X.Carrier => (p.1.1, (Nat.succ p.1.2.1, (p.1.2.2 : List Nat)))) :=
    TMPolyTimeMap.prod_mk hAccVertex hMissTail
  have hIncidentInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat edgeStructuredEncodedType)
        (fun p : X.Carrier => (p.1.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAccVertex hPayloadEdge
  have hIncident :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => edgeIncidentBool (p.1.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp edgeIncidentBool_tm_polytime hIncidentInput
    simpa [Function.comp, X] using hComp
  have hIncidentBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (edgeIncidentBool (p.1.1, p.2.2.2), p)) :=
    TMPolyTimeMap.prod_mk hIncident (TMPolyTimeMap.id X)
  have hEdgeBranchOnProduct :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true =>
              (p.2.1.1,
                (Nat.succ p.2.1.2.1,
                  List.append (p.2.1.2.2 : List Nat) ([p.2.1.2.1] : List Nat)))
          | false => (p.2.1.1, (Nat.succ p.2.1.2.1, (p.2.1.2.2 : List Nat)))) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier => (p.1.1, (Nat.succ p.1.2.1, (p.1.2.2 : List Nat))))
      (fTrue := fun p : X.Carrier =>
        (p.1.1,
          (Nat.succ p.1.2.1,
            List.append (p.1.2.2 : List Nat) ([p.1.2.1] : List Nat))))
      hMiss hHit
  have hEdgeBranch :
      TMPolyTimeMap X A
        (fun p : X.Carrier =>
          if edgeIncidentBool (p.1.1, p.2.2.2) then
            (p.1.1,
              (Nat.succ p.1.2.1,
                List.append (p.1.2.2 : List Nat) ([p.1.2.1] : List Nat)))
          else
            (p.1.1, (Nat.succ p.1.2.1, (p.1.2.2 : List Nat)))) := by
    have hComp := TMPolyTimeMap.comp hEdgeBranchOnProduct hIncidentBranchInput
    convert hComp using 1
    funext p
    cases h : edgeIncidentBool (p.1.1, p.2.2.2) <;> simp [Function.comp, h]
  have hTagBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hTagBranchOnProduct :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true =>
              if edgeIncidentBool (p.2.1.1, p.2.2.2.2) then
                (p.2.1.1,
                  (Nat.succ p.2.1.2.1,
                    List.append (p.2.1.2.2 : List Nat) ([p.2.1.2.1] : List Nat)))
              else
                (p.2.1.1, (Nat.succ p.2.1.2.1, (p.2.1.2.2 : List Nat)))
          | false => (p.2.2.2.1, ((0 : Nat), ([] : List Nat)))) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier => (p.2.2.1, ((0 : Nat), ([] : List Nat))))
      (fTrue := fun p : X.Carrier =>
        if edgeIncidentBool (p.1.1, p.2.2.2) then
          (p.1.1,
            (Nat.succ p.1.2.1,
              List.append (p.1.2.2 : List Nat) ([p.1.2.1] : List Nat)))
        else
          (p.1.1, (Nat.succ p.1.2.1, (p.1.2.2 : List Nat))))
      hInitBranch hEdgeBranch
  have hOut := TMPolyTimeMap.comp hTagBranchOnProduct hTagBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨vertex, next, out⟩, ⟨tag, payloadVertex, edge⟩⟩
  cases tag
  · rfl
  · cases hIncidentVal : edgeIncidentBool (vertex, edge)
    · simp [Function.comp, incidentEdgeScanStep, hIncidentVal, Nat.succ_eq_add_one]
      rfl
    · simp [Function.comp, incidentEdgeScanStep, hIncidentVal, Nat.succ_eq_add_one]
      rfl

theorem incidentEdgeEdgeInstructions_fold_findIdxs
    (edges : List (Nat × Nat)) (v next : Nat) (out : List Nat) :
    (edges.map incidentEdgeEdgeInstruction).foldl
        (fun acc x => incidentEdgeScanStep (acc, x)) (v, (next, out)) =
      (v, (next + edges.length,
        out ++ edges.findIdxs (fun e => edgeIncidentBool (v, e)) next)) := by
  induction edges generalizing next out with
  | nil =>
      simp
  | cons e es ih =>
      cases hIncident : edgeIncidentBool (v, e)
      · simp [incidentEdgeEdgeInstruction, incidentEdgeScanStep, hIncident]
        change (es.map incidentEdgeEdgeInstruction).foldl
            (fun acc x => incidentEdgeScanStep (acc, x)) (v, (next + 1, out)) =
          (v, (next + (es.length + 1),
            out ++ es.findIdxs (fun e => edgeIncidentBool (v, e)) (next + 1)))
        rw [ih (next + 1) out]
        simp [Nat.add_comm, Nat.add_left_comm]
      · simp [incidentEdgeEdgeInstruction, incidentEdgeScanStep, hIncident]
        change (es.map incidentEdgeEdgeInstruction).foldl
            (fun acc x => incidentEdgeScanStep (acc, x)) (v, (next + 1, out ++ [next])) =
          (v, (next + (es.length + 1),
            out ++ next :: es.findIdxs (fun e => edgeIncidentBool (v, e)) (next + 1)))
        rw [ih (next + 1) (out ++ [next])]
        simp [List.append_assoc, Nat.add_comm, Nat.add_left_comm]

theorem incidentEdgeIndicesFromEdges_eq_findIdxs
    (edges : List (Nat × Nat)) (v : Nat) :
    incidentEdgeIndicesFromEdges (edges, v) =
      edges.findIdxs (fun e => edgeIncidentBool (v, e)) := by
  change
    ((incidentEdgeInitInstruction v :: edges.map incidentEdgeEdgeInstruction).foldl
        (fun acc x => incidentEdgeScanStep (acc, x)) incidentEdgeScanInit).2.2 =
      edges.findIdxs (fun e => edgeIncidentBool (v, e))
  rw [List.foldl_cons]
  simp [incidentEdgeInitInstruction, incidentEdgeScanStep]
  have h := incidentEdgeEdgeInstructions_fold_findIdxs edges v 0 []
  simpa using congrArg (fun p : Nat × (Nat × List Nat) => p.2.2) h

theorem edgeIncidentBool_eq_decide (v : Nat) (e : Nat × Nat) :
    edgeIncidentBool (v, e) = decide (e.1 = v ∨ e.2 = v) := by
  cases hIncident : edgeIncidentBool (v, e)
  · have hNot : ¬ (e.1 = v ∨ e.2 = v) := by
      intro hEndpoint
      have hTrue := (edgeIncidentBool_eq_true_iff (v, e)).2 hEndpoint
      simp [hIncident] at hTrue
    simp [hNot]
  · have hEndpoint := (edgeIncidentBool_eq_true_iff (v, e)).1 hIncident
    simp [hEndpoint]

theorem incidentEdgeIndicesFromEdges_eq_incidentEdgeIndices
    (I : VertexCoverInput) (v : Nat) :
    incidentEdgeIndicesFromEdges (I.graph.edges, v) = incidentEdgeIndices I v := by
  rw [incidentEdgeIndicesFromEdges_eq_findIdxs]
  simp [incidentEdgeIndices, edgeIncidentBool_eq_decide]

theorem incidentEncodedList_length_le_inputSize (X : EncodedType) (xs : List X.Carrier) :
    xs.length ≤ (EncodedType.list X).inputSize xs := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [EncodedType.inputSize_list_cons]
      simp only [List.length_cons]
      omega

theorem incidentEncodedList_element_inputSize_le {X : EncodedType} {x : X.Carrier}
    {xs : List X.Carrier} (hx : x ∈ xs) :
    X.inputSize x ≤ (EncodedType.list X).inputSize xs := by
  induction xs with
  | nil =>
      simp at hx
  | cons y ys ih =>
      rw [EncodedType.inputSize_list_cons]
      rcases List.mem_cons.mp hx with hxy | hxys
      · subst x
        omega
      · have hTail := ih hxys
        omega

theorem incidentEncodedList_inputSize_append (X : EncodedType)
    (xs ys : List X.Carrier) :
    (EncodedType.list X).inputSize (xs ++ ys) =
      (EncodedType.list X).inputSize xs + (EncodedType.list X).inputSize ys := by
  simp [EncodedType.inputSize, EncodedType.list, List.flatMap_append]

def incidentEdgeScanAccBound
    (N processed : Nat) (acc : Nat × (Nat × List Nat)) : Prop :=
  acc.1 ≤ N ∧
    acc.2.1 ≤ processed ∧
      (∀ j ∈ acc.2.2, j ≤ processed) ∧ acc.2.2.length ≤ processed

theorem incidentEdgeScanStep_bound {N processed : Nat}
    {acc : Nat × (Nat × List Nat)}
    {instr : Bool × (Nat × (Nat × Nat))}
    (hAcc : incidentEdgeScanAccBound N processed acc)
    (_hProcessed : processed + 1 ≤ N)
    (hInstr : incidentEdgeInstructionEncodedType.inputSize instr ≤ N) :
    incidentEdgeScanAccBound N (processed + 1) (incidentEdgeScanStep (acc, instr)) := by
  rcases acc with ⟨vertex, next, out⟩
  rcases instr with ⟨tag, payloadVertex, edge⟩
  rcases hAcc with ⟨hVertex, hNext, hOutMem, hOutLen⟩
  change vertex ≤ N at hVertex
  change next ≤ processed at hNext
  change (∀ j ∈ out, j ≤ processed) at hOutMem
  change out.length ≤ processed at hOutLen
  cases tag
  · have hPayloadVertex : payloadVertex ≤ N := by
      simp [incidentEdgeInstructionEncodedType, incidentEdgePayloadEncodedType,
        edgeStructuredEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_bool,
        EncodedType.inputSize_nat] at hInstr
      omega
    simp [incidentEdgeScanStep, incidentEdgeScanAccBound]
    exact hPayloadVertex
  · cases hIncident : edgeIncidentBool (vertex, edge)
    · simp [incidentEdgeScanStep, hIncident, incidentEdgeScanAccBound]
      refine ⟨hVertex, by omega, ?_, by omega⟩
      intro j hj
      exact (hOutMem j hj).trans (by omega)
    · simp [incidentEdgeScanStep, hIncident, incidentEdgeScanAccBound]
      refine ⟨hVertex, by omega, ?_, by simp [hOutLen]⟩
      intro j hj
      rcases hj with hjOut | hjNext
      · exact (hOutMem j hjOut).trans (by omega)
      · subst j
        omega

theorem incidentEdgeScanFold_bound_aux
    {N processed : Nat}
    (xs : List incidentEdgeInstructionEncodedType.Carrier)
    (acc : incidentEdgeScanAccEncodedType.Carrier)
    (hAcc : incidentEdgeScanAccBound N processed acc)
    (hLen : processed + xs.length ≤ N)
    (hInstr : ∀ instr ∈ xs, incidentEdgeInstructionEncodedType.inputSize instr ≤ N) :
    incidentEdgeScanAccBound N (processed + xs.length)
      (xs.foldl (fun acc x => incidentEdgeScanStep (acc, x)) acc) := by
  induction xs generalizing processed acc with
  | nil =>
      simpa using hAcc
  | cons x xs ih =>
      have hx : incidentEdgeInstructionEncodedType.inputSize x ≤ N := hInstr x (by simp)
      have hStepProcessed : processed + 1 ≤ N := by
        simp only [List.length_cons] at hLen
        omega
      have hStep := incidentEdgeScanStep_bound hAcc hStepProcessed hx
      have hTailLen : (processed + 1) + xs.length ≤ N := by
        simp only [List.length_cons] at hLen
        omega
      have hTailInstr :
          ∀ instr ∈ xs, incidentEdgeInstructionEncodedType.inputSize instr ≤ N := by
        intro instr hin
        exact hInstr instr (by simp [hin])
      have hTail :=
        ih (processed := processed + 1)
          (acc := incidentEdgeScanStep (acc, x)) hStep hTailLen hTailInstr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hTail

theorem incidentEdgeScanFold_bound_of_inputSize_le
    {N : Nat} (xs : List incidentEdgeInstructionEncodedType.Carrier)
    (hSize : incidentEdgeInstructionListEncodedType.inputSize xs ≤ N) :
    incidentEdgeScanAccBound N xs.length
      (xs.foldl (fun acc x => incidentEdgeScanStep (acc, x)) incidentEdgeScanInit) := by
  have hInit : incidentEdgeScanAccBound N 0 incidentEdgeScanInit := by
    simp [incidentEdgeScanAccBound, incidentEdgeScanInit]
  have hLen : 0 + xs.length ≤ N := by
    have hLenInput :=
      incidentEncodedList_length_le_inputSize incidentEdgeInstructionEncodedType xs
    have hLenInput' : xs.length ≤ incidentEdgeInstructionListEncodedType.inputSize xs := by
      simpa [incidentEdgeInstructionListEncodedType] using hLenInput
    omega
  have hInstr :
      ∀ instr ∈ xs, incidentEdgeInstructionEncodedType.inputSize instr ≤ N := by
    intro instr hin
    have hElem :=
      incidentEncodedList_element_inputSize_le
        (X := incidentEdgeInstructionEncodedType) (x := instr) (xs := xs) hin
    have hElem' : incidentEdgeInstructionEncodedType.inputSize instr ≤
        incidentEdgeInstructionListEncodedType.inputSize xs := by
      simpa [incidentEdgeInstructionListEncodedType] using hElem
    omega
  have h :=
    incidentEdgeScanFold_bound_aux (N := N) (processed := 0) xs incidentEdgeScanInit
      hInit hLen hInstr
  simpa using h

noncomputable def incidentEdgeScanFoldAccBoundPolynomial : Polynomial Nat :=
  Polynomial.C 10 * (Polynomial.X * Polynomial.X) + Polynomial.C 100

@[simp] theorem incidentEdgeScanFoldAccBoundPolynomial_eval (N : Nat) :
    incidentEdgeScanFoldAccBoundPolynomial.eval N = 10 * (N * N) + 100 := by
  simp [incidentEdgeScanFoldAccBoundPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

theorem incidentEdgeScanAccBound_inputSize_le {N processed : Nat}
    {acc : Nat × (Nat × List Nat)}
    (hAcc : incidentEdgeScanAccBound N processed acc)
    (hProcessed : processed ≤ N) :
    incidentEdgeScanAccEncodedType.inputSize acc ≤
      incidentEdgeScanFoldAccBoundPolynomial.eval N := by
  rcases acc with ⟨vertex, next, out⟩
  rcases hAcc with ⟨hVertex, hNext, hOutMem, hOutLen⟩
  have hNextN : next ≤ N := hNext.trans hProcessed
  have hOutSize :
      (EncodedType.list EncodedType.nat).inputSize out ≤ processed * (N + 2) := by
    have hElems : ∀ j ∈ out, EncodedType.nat.inputSize j ≤ N + 1 := by
      intro j hj
      have hjN : j ≤ N := (hOutMem j hj).trans hProcessed
      simp [EncodedType.inputSize_nat]
      omega
    have hList :=
      ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
        EncodedType.nat out (N + 1) hElems
    exact hList.trans (Nat.mul_le_mul_right (N + 2) hOutLen)
  have hOutSizeN :
      (EncodedType.list EncodedType.nat).inputSize out ≤ N * (N + 2) := by
    exact hOutSize.trans (Nat.mul_le_mul_right (N + 2) hProcessed)
  simp [incidentEdgeScanAccEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat]
  nlinarith [sq_nonneg (N : Int), hVertex, hNextN, hOutSizeN]

noncomputable def incidentEdgeScanFoldTimePolynomial
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod incidentEdgeScanAccEncodedType
          incidentEdgeInstructionEncodedType).encode
        incidentEdgeScanAccEncodedType.encode
        incidentEdgeScanStep) : Polynomial Nat :=
  TM2Programs.listFoldBoundedTimePolynomial hStep.tm incidentEdgeScanFoldAccBoundPolynomial
    (hStep.time.comp
      (incidentEdgeScanFoldAccBoundPolynomial + Polynomial.X + Polynomial.C 5))

theorem incidentEdgeScanFold_tm_polytime :
    TMPolyTimeMap
      incidentEdgeInstructionListEncodedType
      incidentEdgeScanAccEncodedType
      (fun xs : List incidentEdgeInstructionEncodedType.Carrier =>
        xs.foldl (fun acc x => incidentEdgeScanStep (acc, x)) incidentEdgeScanInit) := by
  rcases incidentEdgeScanStep_tm_polytime with ⟨hStep⟩
  let time := incidentEdgeScanFoldTimePolynomial hStep
  refine
    TMPolyTimeMap.list_foldl_typed
      incidentEdgeInstructionEncodedType incidentEdgeScanAccEncodedType
      incidentEdgeScanStep incidentEdgeScanInit hStep time ?_
  intro source
  let N := incidentEdgeInstructionListEncodedType.inputSize source
  let B := incidentEdgeScanFoldAccBoundPolynomial.eval N
  let T := hStep.time.eval (B + N + 5)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hSourceLenN : source.length ≤ N := by
    have hLen :=
      incidentEncodedList_length_le_inputSize incidentEdgeInstructionEncodedType source
    simpa [N, incidentEdgeInstructionListEncodedType] using hLen
  have hLoopAux :
      ∀ (pref rest : List incidentEdgeInstructionEncodedType.Carrier),
        source = pref ++ rest →
          TM2Programs.listFoldTypedLoopTime
              incidentEdgeInstructionEncodedType incidentEdgeScanAccEncodedType
              incidentEdgeScanStep hStep
              (pref.foldl (fun acc x => incidentEdgeScanStep (acc, x)) incidentEdgeScanInit)
              rest ≤
            C * (EncodedType.list incidentEdgeInstructionEncodedType).inputSize rest := by
    intro pref rest
    induction rest generalizing pref with
    | nil =>
        intro _hEq
        simp [TM2Programs.listFoldTypedLoopTime]
    | cons x xs ih =>
        intro hEq
        have hxMemSource : x ∈ source := by
          rw [hEq]
          simp
        have hxN : incidentEdgeInstructionEncodedType.inputSize x ≤ N := by
          have hElem :=
            incidentEncodedList_element_inputSize_le
              (X := incidentEdgeInstructionEncodedType) (x := x) (xs := source)
              hxMemSource
          simpa [N, incidentEdgeInstructionListEncodedType] using hElem
        have hPrefixSize : incidentEdgeInstructionListEncodedType.inputSize pref ≤ N := by
          have hEqSize :
              incidentEdgeInstructionListEncodedType.inputSize source =
                incidentEdgeInstructionListEncodedType.inputSize pref +
                  incidentEdgeInstructionListEncodedType.inputSize (x :: xs) := by
            rw [hEq]
            exact incidentEncodedList_inputSize_append incidentEdgeInstructionEncodedType
              pref (x :: xs)
          omega
        have hPrefixBound :=
          incidentEdgeScanFold_bound_of_inputSize_le (N := N) pref hPrefixSize
        have hPrefixLenN : pref.length ≤ N := by
          have hLen :=
            incidentEncodedList_length_le_inputSize incidentEdgeInstructionEncodedType pref
          have hLen' : pref.length ≤ incidentEdgeInstructionListEncodedType.inputSize pref := by
            simpa [incidentEdgeInstructionListEncodedType] using hLen
          omega
        have hAccSize :
            incidentEdgeScanAccEncodedType.inputSize
                (pref.foldl (fun acc x => incidentEdgeScanStep (acc, x))
                  incidentEdgeScanInit) ≤ B := by
          simpa [B] using
            incidentEdgeScanAccBound_inputSize_le hPrefixBound hPrefixLenN
        have hStepProcessed : pref.length + 1 ≤ N := by
          have hLenEq : source.length = pref.length + (x :: xs).length := by
            rw [hEq, List.length_append]
          simp only [List.length_cons] at hLenEq
          omega
        have hStepBound :=
          incidentEdgeScanStep_bound hPrefixBound hStepProcessed hxN
        have hStepSize :
            incidentEdgeScanAccEncodedType.inputSize
                (incidentEdgeScanStep
                  (pref.foldl (fun acc x => incidentEdgeScanStep (acc, x))
                    incidentEdgeScanInit, x)) ≤ B := by
          have hProcessedN : pref.length + 1 ≤ N := hStepProcessed
          simpa [B] using
            incidentEdgeScanAccBound_inputSize_le hStepBound hProcessedN
        have hStepTime :
            hStep.time.eval
                ((EncodedType.prod incidentEdgeScanAccEncodedType
                  incidentEdgeInstructionEncodedType).inputSize
                  (pref.foldl (fun acc x => incidentEdgeScanStep (acc, x))
                    incidentEdgeScanInit, x)) ≤ T := by
          have hArg :
              (EncodedType.prod incidentEdgeScanAccEncodedType
                incidentEdgeInstructionEncodedType).inputSize
                  (pref.foldl (fun acc x => incidentEdgeScanStep (acc, x))
                    incidentEdgeScanInit, x) ≤ B + N + 5 := by
            rw [EncodedType.inputSize_prod]
            change
              incidentEdgeScanAccEncodedType.inputSize
                    (pref.foldl (fun acc x => incidentEdgeScanStep (acc, x))
                      incidentEdgeScanInit) +
                  1 + incidentEdgeInstructionEncodedType.inputSize x ≤ B + N + 5
            omega
          exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
        have hBlock :
            TM2Programs.listFoldBlockTime hStep.tm
                (incidentEdgeInstructionEncodedType.encode x).length
                (incidentEdgeScanAccEncodedType.encode
                  (pref.foldl (fun acc x => incidentEdgeScanStep (acc, x))
                    incidentEdgeScanInit)).length
                (incidentEdgeScanAccEncodedType.encode
                  (incidentEdgeScanStep
                    (pref.foldl (fun acc x => incidentEdgeScanStep (acc, x))
                      incidentEdgeScanInit, x))).length
                (hStep.time.eval
                  ((EncodedType.prod incidentEdgeScanAccEncodedType
                    incidentEdgeInstructionEncodedType).inputSize
                    (pref.foldl (fun acc x => incidentEdgeScanStep (acc, x))
                      incidentEdgeScanInit, x))) ≤
              C * (incidentEdgeInstructionEncodedType.inputSize x + 1) := by
          exact
            TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
              (by simpa [EncodedType.inputSize] using hAccSize)
              (by simpa [EncodedType.inputSize] using hStepSize)
              hStepTime
        have hEqTail : source = (pref ++ [x]) ++ xs := by
          rw [hEq]
          simp [List.append_assoc]
        have hTailRaw := ih (pref := pref ++ [x]) hEqTail
        have hTail :
            TM2Programs.listFoldTypedLoopTime
                incidentEdgeInstructionEncodedType incidentEdgeScanAccEncodedType
                incidentEdgeScanStep hStep
                (incidentEdgeScanStep
                  (pref.foldl (fun acc x => incidentEdgeScanStep (acc, x))
                    incidentEdgeScanInit, x)) xs ≤
              C * (EncodedType.list incidentEdgeInstructionEncodedType).inputSize xs := by
          have hFoldPref :
              (pref ++ [x]).foldl
                  (fun acc x => incidentEdgeScanStep (acc, x)) incidentEdgeScanInit =
                incidentEdgeScanStep
                  (pref.foldl (fun acc x => incidentEdgeScanStep (acc, x))
                    incidentEdgeScanInit, x) := by
            exact
              List.foldl_concat
                (fun acc x => incidentEdgeScanStep (acc, x)) incidentEdgeScanInit x pref
          convert hTailRaw using 1
          exact congrArg
            (fun acc =>
              TM2Programs.listFoldTypedLoopTime
                incidentEdgeInstructionEncodedType incidentEdgeScanAccEncodedType
                incidentEdgeScanStep hStep acc xs)
            hFoldPref.symm
        calc
          TM2Programs.listFoldTypedLoopTime
              incidentEdgeInstructionEncodedType incidentEdgeScanAccEncodedType
              incidentEdgeScanStep hStep
              (pref.foldl (fun acc x => incidentEdgeScanStep (acc, x)) incidentEdgeScanInit)
              (x :: xs)
              =
            TM2Programs.listFoldTypedLoopTime
                incidentEdgeInstructionEncodedType incidentEdgeScanAccEncodedType
                incidentEdgeScanStep hStep
                (incidentEdgeScanStep
                  (pref.foldl (fun acc x => incidentEdgeScanStep (acc, x))
                    incidentEdgeScanInit, x)) xs +
              TM2Programs.listFoldBlockTime hStep.tm
                (incidentEdgeInstructionEncodedType.encode x).length
                (incidentEdgeScanAccEncodedType.encode
                  (pref.foldl (fun acc x => incidentEdgeScanStep (acc, x))
                    incidentEdgeScanInit)).length
                (incidentEdgeScanAccEncodedType.encode
                  (incidentEdgeScanStep
                    (pref.foldl (fun acc x => incidentEdgeScanStep (acc, x))
                      incidentEdgeScanInit, x))).length
                (hStep.time.eval
                  ((EncodedType.prod incidentEdgeScanAccEncodedType
                    incidentEdgeInstructionEncodedType).inputSize
                    (pref.foldl (fun acc x => incidentEdgeScanStep (acc, x))
                      incidentEdgeScanInit, x))) := by
                rfl
          _ ≤
              C * (EncodedType.list incidentEdgeInstructionEncodedType).inputSize xs +
                C * (incidentEdgeInstructionEncodedType.inputSize x + 1) :=
                Nat.add_le_add hTail hBlock
          _ ≤ C * (EncodedType.list incidentEdgeInstructionEncodedType).inputSize (x :: xs) := by
                rw [EncodedType.inputSize_list_cons]
                nlinarith
  have hLoop :
      TM2Programs.listFoldTypedLoopTime
          incidentEdgeInstructionEncodedType incidentEdgeScanAccEncodedType
          incidentEdgeScanStep hStep incidentEdgeScanInit source ≤ C * N := by
    have h := hLoopAux [] source (by simp)
    simpa [N, incidentEdgeInstructionListEncodedType] using h
  have hTimeEval : time.eval N = (C + 2) * (N + 1) := by
    simp [time, incidentEdgeScanFoldTimePolynomial, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval, TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_comp]
  change 2 +
      TM2Programs.listFoldTypedLoopTime
        incidentEdgeInstructionEncodedType incidentEdgeScanAccEncodedType
        incidentEdgeScanStep hStep incidentEdgeScanInit source ≤ time.eval N
  rw [hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

theorem incidentEdgeIndicesFromInstructions_tm_polytime :
    TMPolyTimeMap
      incidentEdgeInstructionListEncodedType
      (EncodedType.list EncodedType.nat)
      incidentEdgeIndicesFromInstructions := by
  have hFold := incidentEdgeScanFold_tm_polytime
  have hTail :
      TMPolyTimeMap incidentEdgeInstructionListEncodedType
        (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
        (fun xs : incidentEdgeInstructionListEncodedType.Carrier =>
          (xs.foldl (fun acc x => incidentEdgeScanStep (acc, x)) incidentEdgeScanInit).2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
    have hComp := TMPolyTimeMap.comp hSnd hFold
    simpa [Function.comp, incidentEdgeScanAccEncodedType] using hComp
  have hOut :
      TMPolyTimeMap incidentEdgeInstructionListEncodedType
        (EncodedType.list EncodedType.nat)
        (fun xs : incidentEdgeInstructionListEncodedType.Carrier =>
          (xs.foldl (fun acc x => incidentEdgeScanStep (acc, x)) incidentEdgeScanInit).2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat (EncodedType.list EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp] using hComp
  simpa [incidentEdgeIndicesFromInstructions] using hOut

theorem incidentEdgeIndicesFromEdges_tm_polytime :
    TMPolyTimeMap
      incidentEdgeInstructionInputEncodedType
      (EncodedType.list EncodedType.nat)
      incidentEdgeIndicesFromEdges := by
  have hComp :=
    TMPolyTimeMap.comp incidentEdgeIndicesFromInstructions_tm_polytime
      incidentEdgeInstructions_tm_polytime
  simpa [Function.comp, incidentEdgeIndicesFromEdges] using hComp

theorem incidentEdgeIndicesFromEdges_length_le
    (p : incidentEdgeInstructionInputEncodedType.Carrier) :
    (incidentEdgeIndicesFromEdges p).length ≤ p.1.length := by
  rcases p with ⟨edges, v⟩
  change (incidentEdgeIndicesFromEdges (edges, v)).length ≤ edges.length
  rw [incidentEdgeIndicesFromEdges_eq_findIdxs edges v]
  simpa using
    (List.countP_le_length (l := edges)
      (p := fun e : Nat × Nat => edgeIncidentBool (v, e)))

theorem mem_incidentEdgeIndicesFromEdges_lt
    {p : incidentEdgeInstructionInputEncodedType.Carrier} {j : Nat}
    (hj : j ∈ incidentEdgeIndicesFromEdges p) :
    j < p.1.length := by
  rcases p with ⟨edges, v⟩
  change j ∈ incidentEdgeIndicesFromEdges (edges, v) at hj
  change j < edges.length
  rw [incidentEdgeIndicesFromEdges_eq_findIdxs edges v] at hj
  rcases (List.mem_findIdxs_iff_exists_getElem_pos (xs := edges)
      (p := fun e : Nat × Nat => edgeIncidentBool (v, e))).1 hj with
    ⟨hjLt, _hPred⟩
  exact hjLt

theorem incidentEdgeIndicesFromEdges_inputSize_le
    (p : incidentEdgeInstructionInputEncodedType.Carrier) :
    (EncodedType.list EncodedType.nat).inputSize (incidentEdgeIndicesFromEdges p) ≤
      3 * incidentEdgeInstructionInputEncodedType.inputSize p ^ 2 + 10 := by
  let N := incidentEdgeInstructionInputEncodedType.inputSize p
  have hEdgesLen :
      p.1.length ≤ N := by
    have hLen := incidentEncodedList_length_le_inputSize edgeStructuredEncodedType p.1
    have hList :
        p.1.length ≤ edgeListStructuredEncodedType.inputSize p.1 := by
      simpa [edgeListStructuredEncodedType] using hLen
    simp [N, incidentEdgeInstructionInputEncodedType, EncodedType.inputSize_prod]
    omega
  have hOutputSize :
      (EncodedType.list EncodedType.nat).inputSize (incidentEdgeIndicesFromEdges p) ≤
        (incidentEdgeIndicesFromEdges p).length * (p.1.length + 2) := by
    have hList :=
      ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
        EncodedType.nat (incidentEdgeIndicesFromEdges p) (p.1.length + 1)
        (by
          intro j hj
          have hjLt := mem_incidentEdgeIndicesFromEdges_lt (p := p) hj
          simp [EncodedType.inputSize, EncodedType.nat]
          omega)
    simpa [Nat.add_assoc] using hList
  have hLen := incidentEdgeIndicesFromEdges_length_le p
  have hOutLenN : (incidentEdgeIndicesFromEdges p).length ≤ N :=
    hLen.trans hEdgesLen
  have hQuadratic :
      (incidentEdgeIndicesFromEdges p).length * (p.1.length + 2) ≤
        N * (N + 2) := by
    exact Nat.mul_le_mul hOutLenN (Nat.add_le_add_right hEdgesLen 2)
  have hPoly : N * (N + 2) ≤ 3 * N ^ 2 + 10 := by
    nlinarith [sq_nonneg (N : Int)]
  exact hOutputSize.trans (hQuadratic.trans hPoly)

theorem incidentEdgeIndicesFromEdges_polynomialSizeBound :
    PolynomialSizeBound
      (fun p : incidentEdgeInstructionInputEncodedType.Carrier =>
        incidentEdgeInstructionInputEncodedType.inputSize p)
      (fun xs : List Nat => (EncodedType.list EncodedType.nat).inputSize xs)
      incidentEdgeIndicesFromEdges :=
  PolynomialSizeBound.intro_with 2 3 10 incidentEdgeIndicesFromEdges_inputSize_le

noncomputable def incidentEdgeIndicesFromEdgesTMBackedMap :
    TMBackedCostedMap
      incidentEdgeInstructionInputEncodedType
      (EncodedType.list EncodedType.nat)
      incidentEdgeIndicesFromEdges where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      incidentEdgeIndicesFromEdges_polynomialSizeBound
  tm_polytime := incidentEdgeIndicesFromEdges_tm_polytime

end SetCovering
end Karp21
end ComplexityReduction
