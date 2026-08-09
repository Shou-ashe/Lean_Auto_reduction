/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuit
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.FeedbackNodeSetStructuredTM
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ChromaticNumber.StructuredRoute

/-!
Direct TM-backed structured assembly for the Vertex Cover to Directed
Hamiltonian Circuit selector/path route.

This file is intentionally separate from the semantic `PartN` proof files so
the existing DHC reconstruction stays below the per-file context budget.
-/

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

/-! ### Target reifiers and small arithmetic -/

def directedHamiltonianCircuitGraphToInput (g : GraphInput) :
    DirectedHamiltonianCircuitInput where
  graph := g

theorem directedHamiltonianCircuitGraphToInput_encode (g : GraphInput) :
    directedHamiltonianCircuitStructuredEncodedType.encode
        (directedHamiltonianCircuitGraphToInput g) =
      graphStructuredEncodedType.encode g := by
  rfl

noncomputable def directedHamiltonianCircuitGraphToInputTMBackedMap :
    TMBackedCostedMap
      graphStructuredEncodedType
      directedHamiltonianCircuitStructuredEncodedType
      directedHamiltonianCircuitGraphToInput :=
  TMBackedCostedMap.ofEncodingEquiv
    graphStructuredEncodedType
    directedHamiltonianCircuitStructuredEncodedType
    directedHamiltonianCircuitGraphToInput
    (Equiv.refl graphStructuredEncodedType.Symbol)
    (by
      intro g
      change
        directedHamiltonianCircuitStructuredEncodedType.encode
            (directedHamiltonianCircuitGraphToInput g) =
          (graphStructuredEncodedType.encode g).map id
      simp [directedHamiltonianCircuitGraphToInput_encode])

def dhcIncidenceVertexCode (p : Nat × (Nat × Nat)) : Nat :=
  p.1 + natDouble p.2.1 + p.2.2

theorem dhcIncidenceVertexCode_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.nat))
      EncodedType.nat
      dhcIncidenceVertexCode := by
  let X :=
    EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hIdx : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hBit : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hDouble : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => natDouble p.2.1) := by
    have hComp := TMPolyTimeMap.comp natDouble_tm_polytime hIdx
    simpa [Function.comp, X] using hComp
  have hFirstAddInput :
      TMPolyTimeMap X natAddInputEncodedType
        (fun p : X.Carrier => (p.1, natDouble p.2.1)) :=
    TMPolyTimeMap.prod_mk hBudget hDouble
  have hFirstAdd :
      TMPolyTimeMap X EncodedType.nat
        (fun p : Nat × (Nat × Nat) => p.1 + natDouble p.2.1) := by
    have hComp := TMPolyTimeMap.comp natAdd_tm_polytime hFirstAddInput
    simpa [Function.comp, X, natAddInputEncodedType] using hComp
  have hSecondAddInput :
      TMPolyTimeMap X natAddInputEncodedType
        (fun p : Nat × (Nat × Nat) => (p.1 + natDouble p.2.1, p.2.2)) :=
    TMPolyTimeMap.prod_mk hFirstAdd hBit
  have hOut := TMPolyTimeMap.comp natAdd_tm_polytime hSecondAddInput
  simpa [Function.comp, dhcIncidenceVertexCode, X, natAddInputEncodedType] using hOut

/-! ### Indexed source-incidence primitives -/

def dhcIndexedIncidenceEncodedType : EncodedType :=
  EncodedType.prod vertexPairEncodedType EncodedType.nat

def dhcIndexedIncidenceListEncodedType : EncodedType :=
  EncodedType.list dhcIndexedIncidenceEncodedType

def dhcRowScanAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)))

def dhcRowScanStepInputEncodedType : EncodedType :=
  EncodedType.prod dhcRowScanAccEncodedType edgeStructuredEncodedType

def dhcRowScanAcc.vertices (acc : dhcRowScanAccEncodedType.Carrier) : Nat :=
  acc.1

def dhcRowScanAcc.sourceVertex (acc : dhcRowScanAccEncodedType.Carrier) : Nat :=
  acc.2.1

def dhcRowScanAcc.edgeIndex (acc : dhcRowScanAccEncodedType.Carrier) : Nat :=
  acc.2.2.1

def dhcRowScanAcc.nextIndex (acc : dhcRowScanAccEncodedType.Carrier) : Nat :=
  acc.2.2.2.1

def dhcRowScanAcc.out (acc : dhcRowScanAccEncodedType.Carrier) :
    List ((Nat × Nat) × Nat) :=
  acc.2.2.2.2

def dhcSourceIncidentBool (p : Nat × (Nat × (Nat × Nat))) : Bool :=
  graphBoolAndPair
    (FeedbackNodeSet.natLtBool (p.2.1, p.1),
      graphBoolOrPair (decide (p.2.1 = p.2.2.1), decide (p.2.1 = p.2.2.2)))

theorem dhcSourceIncidentBool_eq_true_iff (p : Nat × (Nat × (Nat × Nat))) :
    dhcSourceIncidentBool p = true ↔
      p.2.1 < p.1 ∧ (p.2.2.1 = p.2.1 ∨ p.2.2.2 = p.2.1) := by
  rw [dhcSourceIncidentBool, graphBoolAndPair_eq_true_iff, graphBoolOrPair_eq_true_iff,
    FeedbackNodeSet.natLtBool_eq_true_iff]
  simp [eq_comm]

theorem dhcSourceIncidentBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat edgeStructuredEncodedType))
      EncodedType.bool
      dhcSourceIncidentBool := by
  let X :=
    EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.nat edgeStructuredEncodedType)
  have hVertices : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat edgeStructuredEncodedType)
  have hTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat edgeStructuredEncodedType)
        (fun p : X.Carrier => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat edgeStructuredEncodedType)
  have hU : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat edgeStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hEdge : TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat edgeStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hLeftEndpoint : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hEdge
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hRightEndpoint : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hEdge
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hLtInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.1, p.1)) :=
    TMPolyTimeMap.prod_mk hU hVertices
  have hLt := TMPolyTimeMap.comp FeedbackNodeSet.natLtBool_tm_polytime hLtInput
  have hLeftEqInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.1, p.2.2.1)) :=
    TMPolyTimeMap.prod_mk hU hLeftEndpoint
  have hRightEqInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hU hRightEndpoint
  have hLeftEq := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hLeftEqInput
  have hRightEq := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hRightEqInput
  have hOrInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : Nat × (Nat × (Nat × Nat)) =>
          (decide (p.2.1 = p.2.2.1), decide (p.2.1 = p.2.2.2))) :=
    TMPolyTimeMap.prod_mk hLeftEq hRightEq
  have hOr := TMPolyTimeMap.comp graphBoolOrPair_tm_polytime hOrInput
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : Nat × (Nat × (Nat × Nat)) =>
          (FeedbackNodeSet.natLtBool (p.2.1, p.1),
            graphBoolOrPair (decide (p.2.1 = p.2.2.1),
              decide (p.2.1 = p.2.2.2)))) :=
    TMPolyTimeMap.prod_mk hLt hOr
  have hOut := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
  simpa [Function.comp, dhcSourceIncidentBool, X, edgeStructuredEncodedType] using hOut

def dhcRowScanEmitBlock
    (acc : dhcRowScanAccEncodedType.Carrier) (edge : Nat × Nat) :
    List ((Nat × Nat) × Nat) :=
  if dhcSourceIncidentBool (acc.1, (acc.2.1, edge)) then
    [((acc.2.1, acc.2.2.1), acc.2.2.2.1)]
  else
    []

def dhcRowScanStep
    (p : dhcRowScanAccEncodedType.Carrier × (Nat × Nat)) :
    dhcRowScanAccEncodedType.Carrier :=
  let acc := p.1
  let edge := p.2
  let emitted := dhcRowScanEmitBlock acc edge
  let out : List ((Nat × Nat) × Nat) := acc.2.2.2.2
  let nextIdx :=
    if dhcSourceIncidentBool (acc.1, (acc.2.1, edge)) then
      Nat.succ acc.2.2.2.1
    else
      acc.2.2.2.1
  (acc.1,
    (acc.2.1,
      (Nat.succ acc.2.2.1,
        (nextIdx, out ++ emitted))))

theorem dhcRowScanEmitBlock_tm_polytime :
    TMPolyTimeMap
      dhcRowScanStepInputEncodedType
      dhcIndexedIncidenceListEncodedType
      (fun p : dhcRowScanStepInputEncodedType.Carrier => dhcRowScanEmitBlock p.1 p.2) := by
  let X := dhcRowScanStepInputEncodedType
  have hAcc : TMPolyTimeMap X dhcRowScanAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, dhcRowScanStepInputEncodedType] using
      TMPolyTimeMap.fst dhcRowScanAccEncodedType edgeStructuredEncodedType
  have hEdge : TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, dhcRowScanStepInputEncodedType] using
      TMPolyTimeMap.snd dhcRowScanAccEncodedType edgeStructuredEncodedType
  have hVertices : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst :=
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat
            (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)))
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, dhcRowScanAccEncodedType, X] using hComp
  have hTail₁ :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat
            (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)))
        (fun p : X.Carrier => p.1.2) := by
    have hSnd :=
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat
            (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)))
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, dhcRowScanAccEncodedType, X] using hComp
  have hU : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.1) := by
    have hFst :=
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType))
    have hComp := TMPolyTimeMap.comp hFst hTail₁
    simpa [Function.comp, X] using hComp
  have hTail₂ :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType))
        (fun p : X.Carrier => p.1.2.2) := by
    have hSnd :=
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType))
    have hComp := TMPolyTimeMap.comp hSnd hTail₁
    simpa [Function.comp, X] using hComp
  have hEdgeIndex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.2.1) := by
    have hFst :=
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hTail₂
    simpa [Function.comp, X] using hComp
  have hTail₃ :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)
        (fun p : X.Carrier => p.1.2.2.2) := by
    have hSnd :=
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hTail₂
    simpa [Function.comp, X] using hComp
  have hNextIndex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat dhcIndexedIncidenceListEncodedType
    have hComp := TMPolyTimeMap.comp hFst hTail₃
    simpa [Function.comp, X] using hComp
  have hIncidentInput :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat edgeStructuredEncodedType))
        (fun p : X.Carrier => (p.1.1, (p.1.2.1, p.2))) :=
    TMPolyTimeMap.prod_mk hVertices (TMPolyTimeMap.prod_mk hU hEdge)
  have hIncident := TMPolyTimeMap.comp dhcSourceIncidentBool_tm_polytime hIncidentInput
  have hPair :
      TMPolyTimeMap X vertexPairEncodedType
        (fun p : X.Carrier => (p.1.2.1, p.1.2.2.1)) :=
    TMPolyTimeMap.prod_mk hU hEdgeIndex
  have hIndexed :
      TMPolyTimeMap X dhcIndexedIncidenceEncodedType
        (fun p : X.Carrier => ((p.1.2.1, p.1.2.2.1), p.1.2.2.2.1)) :=
    TMPolyTimeMap.prod_mk hPair hNextIndex
  have hSingleton :
      TMPolyTimeMap X dhcIndexedIncidenceListEncodedType
        (fun p : X.Carrier => [((p.1.2.1, p.1.2.2.1), p.1.2.2.2.1)]) := by
    have hComp :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton dhcIndexedIncidenceEncodedType)
        hIndexed
    simpa [Function.comp, dhcIndexedIncidenceListEncodedType, X] using hComp
  have hEmpty :
      TMPolyTimeMap X dhcIndexedIncidenceListEncodedType
        (fun _ : X.Carrier => ([] : List ((Nat × Nat) × Nat))) :=
    TMPolyTimeMap.const X dhcIndexedIncidenceListEncodedType []
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier =>
          (dhcSourceIncidentBool (p.1.1, (p.1.2.1, p.2)), p)) :=
    TMPolyTimeMap.prod_mk hIncident (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X)
        dhcIndexedIncidenceListEncodedType
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true => [((p.2.1.2.1, p.2.1.2.2.1), p.2.1.2.2.2.1)]
          | false => []) :=
    graphBoolProduct_dispatch_tm_polytime X dhcIndexedIncidenceListEncodedType
      (fFalse := fun _ : X.Carrier => ([] : List ((Nat × Nat) × Nat)))
      (fTrue := fun p : X.Carrier =>
        [((p.1.2.1, p.1.2.2.1), p.1.2.2.2.1)])
      hEmpty hSingleton
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext p
  cases h : dhcSourceIncidentBool (p.1.1, (p.1.2.1, p.2)) <;>
    simp [Function.comp, dhcRowScanEmitBlock, h] <;>
    rfl

theorem dhcRowScanStep_tm_polytime :
    TMPolyTimeMap
      dhcRowScanStepInputEncodedType
      dhcRowScanAccEncodedType
      dhcRowScanStep := by
  let X := dhcRowScanStepInputEncodedType
  have hAcc : TMPolyTimeMap X dhcRowScanAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, dhcRowScanStepInputEncodedType] using
      TMPolyTimeMap.fst dhcRowScanAccEncodedType edgeStructuredEncodedType
  have hEdge : TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, dhcRowScanStepInputEncodedType] using
      TMPolyTimeMap.snd dhcRowScanAccEncodedType edgeStructuredEncodedType
  have hVertices : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst :=
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat
            (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)))
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, dhcRowScanAccEncodedType, X] using hComp
  have hTail₁ :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat
            (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)))
        (fun p : X.Carrier => p.1.2) := by
    have hSnd :=
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat
            (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)))
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, dhcRowScanAccEncodedType, X] using hComp
  have hU : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.1) := by
    have hFst :=
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType))
    have hComp := TMPolyTimeMap.comp hFst hTail₁
    simpa [Function.comp, X] using hComp
  have hTail₂ :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType))
        (fun p : X.Carrier => p.1.2.2) := by
    have hSnd :=
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType))
    have hComp := TMPolyTimeMap.comp hSnd hTail₁
    simpa [Function.comp, X] using hComp
  have hEdgeIndex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.2.1) := by
    have hFst :=
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hTail₂
    simpa [Function.comp, X] using hComp
  have hTail₃ :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)
        (fun p : X.Carrier => p.1.2.2.2) := by
    have hSnd :=
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hTail₂
    simpa [Function.comp, X] using hComp
  have hNextIndex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat dhcIndexedIncidenceListEncodedType
    have hComp := TMPolyTimeMap.comp hFst hTail₃
    simpa [Function.comp, X] using hComp
  have hOutList :
      TMPolyTimeMap X dhcIndexedIncidenceListEncodedType
        (fun p : X.Carrier => p.1.2.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat dhcIndexedIncidenceListEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTail₃
    simpa [Function.comp, X] using hComp
  have hIncidentInput :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat edgeStructuredEncodedType))
        (fun p : X.Carrier => (p.1.1, (p.1.2.1, p.2))) :=
    TMPolyTimeMap.prod_mk hVertices (TMPolyTimeMap.prod_mk hU hEdge)
  have hIncident := TMPolyTimeMap.comp dhcSourceIncidentBool_tm_polytime hIncidentInput
  have hNextIndexSucc :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => Nat.succ p.1.2.2.2.1) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hNextIndex
    simpa [Function.comp, X] using hComp
  have hNextIndexBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier =>
          (dhcSourceIncidentBool (p.1.1, (p.1.2.1, p.2)), p)) :=
    TMPolyTimeMap.prod_mk hIncident (TMPolyTimeMap.id X)
  have hNextIndexBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) EncodedType.nat
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true => Nat.succ p.2.1.2.2.2.1
          | false => p.2.1.2.2.2.1) :=
    graphBoolProduct_dispatch_tm_polytime X EncodedType.nat
      (fFalse := fun p : X.Carrier => p.1.2.2.2.1)
      (fTrue := fun p : X.Carrier => Nat.succ p.1.2.2.2.1)
      hNextIndex hNextIndexSucc
  have hNextIndexOut :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier =>
          if dhcSourceIncidentBool (p.1.1, (p.1.2.1, p.2)) then
            Nat.succ p.1.2.2.2.1
          else
            p.1.2.2.2.1) := by
    have hComp := TMPolyTimeMap.comp hNextIndexBranch hNextIndexBranchInput
    convert hComp using 1
    funext p
    cases h : dhcSourceIncidentBool (p.1.1, (p.1.2.1, p.2)) <;>
      simp [Function.comp, h]
  have hEdgeIndexSucc :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => Nat.succ p.1.2.2.1) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hEdgeIndex
    simpa [Function.comp, X] using hComp
  have hEmit :
      TMPolyTimeMap X dhcIndexedIncidenceListEncodedType
        (fun p : X.Carrier => dhcRowScanEmitBlock p.1 p.2) := by
    simpa [X] using dhcRowScanEmitBlock_tm_polytime
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceListEncodedType
          dhcIndexedIncidenceListEncodedType)
        (fun p : X.Carrier =>
          (p.1.2.2.2.2, dhcRowScanEmitBlock p.1 p.2)) :=
    TMPolyTimeMap.prod_mk hOutList hEmit
  have hAppend :
      TMPolyTimeMap X dhcIndexedIncidenceListEncodedType
        (fun p : X.Carrier =>
          (show List ((Nat × Nat) × Nat) from p.1.2.2.2.2) ++
            dhcRowScanEmitBlock p.1 p.2) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append dhcIndexedIncidenceEncodedType) hAppendInput
    simpa [Function.comp, dhcIndexedIncidenceListEncodedType, X] using hComp
  have hInnerPair :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)
        (fun p : X.Carrier =>
          (if dhcSourceIncidentBool (p.1.1, (p.1.2.1, p.2)) then
            Nat.succ p.1.2.2.2.1
          else
            p.1.2.2.2.1,
            (show List ((Nat × Nat) × Nat) from p.1.2.2.2.2) ++
              dhcRowScanEmitBlock p.1 p.2)) :=
    TMPolyTimeMap.prod_mk hNextIndexOut hAppend
  have hMidPair :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType))
        (fun p : X.Carrier =>
          (Nat.succ p.1.2.2.1,
            (if dhcSourceIncidentBool (p.1.1, (p.1.2.1, p.2)) then
                Nat.succ p.1.2.2.2.1
              else
                p.1.2.2.2.1,
              (show List ((Nat × Nat) × Nat) from p.1.2.2.2.2) ++
                dhcRowScanEmitBlock p.1 p.2))) :=
    TMPolyTimeMap.prod_mk hEdgeIndexSucc hInnerPair
  have hTailPair :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat
            (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)))
        (fun p : X.Carrier =>
          (p.1.2.1,
            (Nat.succ p.1.2.2.1,
              (if dhcSourceIncidentBool (p.1.1, (p.1.2.1, p.2)) then
                  Nat.succ p.1.2.2.2.1
                else
                  p.1.2.2.2.1,
                (show List ((Nat × Nat) × Nat) from p.1.2.2.2.2) ++
                  dhcRowScanEmitBlock p.1 p.2)))) :=
    TMPolyTimeMap.prod_mk hU hMidPair
  have hOut := TMPolyTimeMap.prod_mk hVertices hTailPair
  simpa [dhcRowScanStep] using hOut

/-! ### Row-level source-edge scan runner -/

def dhcRowInitPayloadEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat EncodedType.nat)

def dhcRowFoldInstructionEncodedType : EncodedType :=
  EncodedType.sum dhcRowInitPayloadEncodedType edgeStructuredEncodedType

def dhcRowFoldInstructionListEncodedType : EncodedType :=
  EncodedType.list dhcRowFoldInstructionEncodedType

def dhcRowScanInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.nat edgeListStructuredEncodedType))

def dhcRowFoldInit : dhcRowScanAccEncodedType.Carrier :=
  ((0 : Nat), ((0 : Nat), ((0 : Nat), ((0 : Nat), ([] : List ((Nat × Nat) × Nat))))))

def dhcRowFoldLeftStep
    (p : dhcRowInitPayloadEncodedType.Carrier) :
    dhcRowScanAccEncodedType.Carrier :=
  (p.1, (p.2.1, ((0 : Nat), (p.2.2, ([] : List ((Nat × Nat) × Nat))))))

def dhcRowFoldStep
    (p :
      dhcRowScanAccEncodedType.Carrier ×
        dhcRowFoldInstructionEncodedType.Carrier) :
    dhcRowScanAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl payload => dhcRowFoldLeftStep payload
  | Sum.inr edge => dhcRowScanStep (p.1, edge)

def dhcRowScanInstructions
    (vertices u nextIndex : Nat) (edges : List (Nat × Nat)) :
    dhcRowFoldInstructionListEncodedType.Carrier :=
  Sum.inl (vertices, (u, nextIndex)) :: edges.map Sum.inr

def dhcRowScanEdgesFold
    (vertices u nextIndex : Nat) (edges : List (Nat × Nat)) :
    dhcRowScanAccEncodedType.Carrier :=
  edges.foldl
    (fun acc edge => dhcRowScanStep (acc, edge))
    (vertices, (u, ((0 : Nat), (nextIndex, ([] : List ((Nat × Nat) × Nat))))))

def dhcRowScanResult
    (vertices u nextIndex : Nat) (edges : List (Nat × Nat)) :
    dhcRowScanAccEncodedType.Carrier :=
  (dhcRowScanInstructions vertices u nextIndex edges).foldl
    (fun acc instr => dhcRowFoldStep (acc, instr))
    dhcRowFoldInit

def dhcRowScanFromInput
    (p : dhcRowScanInputEncodedType.Carrier) : dhcRowScanAccEncodedType.Carrier :=
  dhcRowScanResult p.1 p.2.1 p.2.2.1 p.2.2.2

def dhcIndexedRowFromEdgeIndices (u nextIndex : Nat) : List Nat → List ((Nat × Nat) × Nat)
  | [] => []
  | i :: is => ((u, i), nextIndex) :: dhcIndexedRowFromEdgeIndices u (nextIndex + 1) is

theorem dhcRowScan_fold_map_inr
    (edges : List (Nat × Nat)) (acc : dhcRowScanAccEncodedType.Carrier) :
    (edges.map Sum.inr).foldl
        (fun acc instr => dhcRowFoldStep (acc, instr)) acc =
      edges.foldl (fun acc edge => dhcRowScanStep (acc, edge)) acc := by
  induction edges generalizing acc with
  | nil =>
      rfl
  | cons edge rest ih =>
      simpa [dhcRowFoldStep] using ih (dhcRowScanStep (acc, edge))

theorem dhcRowScanResult_eq_edgesFold
    (vertices u nextIndex : Nat) (edges : List (Nat × Nat)) :
    dhcRowScanResult vertices u nextIndex edges =
      dhcRowScanEdgesFold vertices u nextIndex edges := by
  unfold dhcRowScanResult dhcRowScanInstructions dhcRowScanEdgesFold
  rw [List.foldl_cons]
  change
    (edges.map Sum.inr).foldl
        (fun acc instr => dhcRowFoldStep (acc, instr))
        (dhcRowFoldLeftStep (vertices, (u, nextIndex))) =
      edges.foldl
        (fun acc edge => dhcRowScanStep (acc, edge))
        (vertices, (u, ((0 : Nat), (nextIndex, ([] : List ((Nat × Nat) × Nat))))))
  rw [dhcRowScan_fold_map_inr]
  rfl

theorem dhcRowScanStep_false
    (vertices u edgeIndex nextIndex : Nat) (out : List ((Nat × Nat) × Nat))
    (edge : Nat × Nat)
    (hIncident : dhcSourceIncidentBool (vertices, (u, edge)) = false) :
    dhcRowScanStep ((vertices, (u, (edgeIndex, (nextIndex, out)))), edge) =
      (vertices, (u, (edgeIndex + 1, (nextIndex, out)))) := by
  simp [dhcRowScanStep, dhcRowScanEmitBlock, hIncident]
  rfl

theorem dhcRowScanStep_true
    (vertices u edgeIndex nextIndex : Nat) (out : List ((Nat × Nat) × Nat))
    (edge : Nat × Nat)
    (hIncident : dhcSourceIncidentBool (vertices, (u, edge)) = true) :
    dhcRowScanStep ((vertices, (u, (edgeIndex, (nextIndex, out)))), edge) =
      (vertices,
        (u, (edgeIndex + 1, (nextIndex + 1, out ++ [((u, edgeIndex), nextIndex)])))) := by
  simp [dhcRowScanStep, dhcRowScanEmitBlock, hIncident]
  rfl

theorem dhcRowScanEdgesFold_findIdxs_aux
    (edges : List (Nat × Nat)) (vertices u edgeIndex nextIndex : Nat)
    (out : List ((Nat × Nat) × Nat)) :
    edges.foldl
        (fun acc edge => dhcRowScanStep (acc, edge))
        (vertices, (u, (edgeIndex, (nextIndex, out)))) =
      let hits := edges.findIdxs (fun edge => dhcSourceIncidentBool (vertices, (u, edge)))
        edgeIndex
      (vertices,
        (u,
          (edgeIndex + edges.length,
            (nextIndex + hits.length,
              out ++ dhcIndexedRowFromEdgeIndices u nextIndex hits)))) := by
  induction edges generalizing edgeIndex nextIndex out with
  | nil =>
      simp [dhcIndexedRowFromEdgeIndices]
      rfl
  | cons edge rest ih =>
      rw [List.foldl_cons]
      cases hIncident : dhcSourceIncidentBool (vertices, (u, edge))
      · rw [dhcRowScanStep_false vertices u edgeIndex nextIndex out edge hIncident]
        exact (ih (edgeIndex + 1) nextIndex out).trans (by
          simp [hIncident, Nat.add_comm, Nat.add_left_comm])
      · rw [dhcRowScanStep_true vertices u edgeIndex nextIndex out edge hIncident]
        exact
          (ih (edgeIndex + 1) (nextIndex + 1)
            (out ++ [((u, edgeIndex), nextIndex)])).trans (by
              simp [hIncident, dhcIndexedRowFromEdgeIndices, List.append_assoc, Nat.add_comm,
                Nat.add_left_comm, Nat.add_assoc])

theorem dhcRowScanResult_findIdxs
    (vertices u nextIndex : Nat) (edges : List (Nat × Nat)) :
    dhcRowScanResult vertices u nextIndex edges =
      let hits := edges.findIdxs (fun edge => dhcSourceIncidentBool (vertices, (u, edge)))
        0
      (vertices,
        (u,
          (edges.length,
            (nextIndex + hits.length,
              dhcIndexedRowFromEdgeIndices u nextIndex hits)))) := by
  rw [dhcRowScanResult_eq_edgesFold]
  unfold dhcRowScanEdgesFold
  simpa using
    dhcRowScanEdgesFold_findIdxs_aux edges vertices u 0 nextIndex
      ([] : List ((Nat × Nat) × Nat))

theorem dhcRowFoldLeftStep_tm_polytime :
    TMPolyTimeMap
      dhcRowInitPayloadEncodedType
      dhcRowScanAccEncodedType
      dhcRowFoldLeftStep := by
  let X := dhcRowInitPayloadEncodedType
  have hVertices : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcRowInitPayloadEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => p.2) := by
    simpa [X, dhcRowInitPayloadEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hU : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hNext : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hEmpty :
      TMPolyTimeMap X dhcIndexedIncidenceListEncodedType
        (fun _ : X.Carrier => ([] : List ((Nat × Nat) × Nat))) :=
    TMPolyTimeMap.const X dhcIndexedIncidenceListEncodedType []
  have hInner :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)
        (fun p : X.Carrier => (p.2.2, ([] : List ((Nat × Nat) × Nat)))) :=
    TMPolyTimeMap.prod_mk hNext hEmpty
  have hMid :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType))
        (fun p : X.Carrier => ((0 : Nat), (p.2.2, ([] : List ((Nat × Nat) × Nat))))) :=
    TMPolyTimeMap.prod_mk hZero hInner
  have hTailOut :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat
            (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)))
        (fun p : X.Carrier =>
          (p.2.1, ((0 : Nat), (p.2.2, ([] : List ((Nat × Nat) × Nat)))))) :=
    TMPolyTimeMap.prod_mk hU hMid
  have hOut := TMPolyTimeMap.prod_mk hVertices hTailOut
  simpa [dhcRowFoldLeftStep, dhcRowScanAccEncodedType, dhcRowInitPayloadEncodedType, X]
    using hOut

theorem dhcRowFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod dhcRowScanAccEncodedType dhcRowFoldInstructionEncodedType)
      dhcRowScanAccEncodedType
      dhcRowFoldStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      dhcRowScanAccEncodedType dhcRowInitPayloadEncodedType edgeStructuredEncodedType
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim dhcRowFoldLeftStep_tm_polytime
      dhcRowScanStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem dhcRowScanInstructions_tm_polytime :
    TMPolyTimeMap
      dhcRowScanInputEncodedType
      dhcRowFoldInstructionListEncodedType
      (fun p : dhcRowScanInputEncodedType.Carrier =>
        dhcRowScanInstructions p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let X := dhcRowScanInputEncodedType
  have hVertices : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcRowScanInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat edgeListStructuredEncodedType))
  have hTail₁ :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat edgeListStructuredEncodedType))
        (fun p : X.Carrier => p.2) := by
    simpa [X, dhcRowScanInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat edgeListStructuredEncodedType))
  have hU : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst :=
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat edgeListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hTail₁
    simpa [Function.comp, X] using hComp
  have hTail₂ :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat edgeListStructuredEncodedType)
        (fun p : X.Carrier => p.2.2) := by
    have hSnd :=
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat edgeListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hTail₁
    simpa [Function.comp, X] using hComp
  have hNext : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hTail₂
    simpa [Function.comp, X] using hComp
  have hEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTail₂
    simpa [Function.comp, X] using hComp
  have hPayload :
      TMPolyTimeMap X dhcRowInitPayloadEncodedType
        (fun p : X.Carrier => (p.1, (p.2.1, p.2.2.1))) :=
    TMPolyTimeMap.prod_mk hVertices (TMPolyTimeMap.prod_mk hU hNext)
  have hInit :
      TMPolyTimeMap X dhcRowFoldInstructionEncodedType
        (fun p : X.Carrier => Sum.inl (p.1, (p.2.1, p.2.2.1))) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.inl dhcRowInitPayloadEncodedType edgeStructuredEncodedType)
      hPayload
    simpa [Function.comp, dhcRowFoldInstructionEncodedType, X] using hComp
  have hEdgeInstruction :
      TMPolyTimeMap edgeStructuredEncodedType dhcRowFoldInstructionEncodedType
        (fun e : edgeStructuredEncodedType.Carrier => Sum.inr e) := by
    simpa [dhcRowFoldInstructionEncodedType] using
      TMPolyTimeMap.inr dhcRowInitPayloadEncodedType edgeStructuredEncodedType
  have hMappedEdges :
      TMPolyTimeMap X dhcRowFoldInstructionListEncodedType
        (fun p : X.Carrier => p.2.2.2.map Sum.inr) := by
    have hMap := TMPolyTimeMap.list_map hEdgeInstruction
    have hComp := TMPolyTimeMap.comp hMap hEdges
    simpa [Function.comp, dhcRowFoldInstructionListEncodedType,
      edgeListStructuredEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod dhcRowFoldInstructionEncodedType
          dhcRowFoldInstructionListEncodedType)
        (fun p : X.Carrier =>
          (Sum.inl (p.1, (p.2.1, p.2.2.1)), p.2.2.2.map Sum.inr)) :=
    TMPolyTimeMap.prod_mk hInit hMappedEdges
  have hCons :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons dhcRowFoldInstructionEncodedType)
      hConsInput
  simpa [Function.comp, dhcRowScanInstructions, dhcRowFoldInstructionListEncodedType, X]
    using hCons

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
