/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipFeedbackArcSetRankRunner

/-!
Direct standard-TM runner checking that every removed Feedback Arc Set certificate
arc belongs to the input graph edge list.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics.Graph

namespace FeedbackArcSetMembership

def fasRemovedEdgeInGraphInputEncodedType : EncodedType :=
  EncodedType.prod edgeListStructuredEncodedType edgeStructuredEncodedType

def fasRemovedEdgeInGraphBool (p : List (Nat × Nat) × (Nat × Nat)) : Bool :=
  DirectedHamiltonianCircuitMembership.sourceHasDirectedEdgeBool (p.2, p.1)

theorem fasRemovedEdgeInGraphBool_eq_true_iff
    (p : List (Nat × Nat) × (Nat × Nat)) :
    fasRemovedEdgeInGraphBool p = true ↔ p.2 ∈ p.1 := by
  simpa [fasRemovedEdgeInGraphBool] using
    DirectedHamiltonianCircuitMembership.sourceHasDirectedEdgeBool_eq_true_iff p.2 p.1

theorem fasRemovedEdgeInGraphBool_tm_polytime :
    TMPolyTimeMap fasRemovedEdgeInGraphInputEncodedType EncodedType.bool
      fasRemovedEdgeInGraphBool := by
  let X := fasRemovedEdgeInGraphInputEncodedType
  have hEdges : TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, fasRemovedEdgeInGraphInputEncodedType] using
      TMPolyTimeMap.fst edgeListStructuredEncodedType edgeStructuredEncodedType
  have hEdge : TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, fasRemovedEdgeInGraphInputEncodedType] using
      TMPolyTimeMap.snd edgeListStructuredEncodedType edgeStructuredEncodedType
  have hInput :
      TMPolyTimeMap X (EncodedType.prod vertexPairEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier => (p.2, p.1)) :=
    TMPolyTimeMap.prod_mk hEdge hEdges
  have hComp :=
    TMPolyTimeMap.comp
      DirectedHamiltonianCircuitMembership.sourceHasDirectedEdgeBool_tm_polytime hInput
  simpa [Function.comp, fasRemovedEdgeInGraphBool, vertexPairEncodedType] using hComp

def fasRemovedInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool
    (EncodedType.prod edgeListStructuredEncodedType edgeStructuredEncodedType)

abbrev FASRemovedInstruction := Bool × (List (Nat × Nat) × (Nat × Nat))

def fasRemovedInstructionListEncodedType : EncodedType :=
  EncodedType.list fasRemovedInstructionEncodedType

def fasRemovedInstructionInputEncodedType : EncodedType :=
  EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType

def fasRemovedAccEncodedType : EncodedType :=
  EncodedType.prod edgeListStructuredEncodedType EncodedType.bool

abbrev FASRemovedAcc := List (Nat × Nat) × Bool

def fasRemovedInitInstruction (edges : List (Nat × Nat)) : FASRemovedInstruction :=
  (false, (edges, (0, 0)))

def fasRemovedElementInstruction (e : Nat × Nat) : FASRemovedInstruction :=
  (true, ([], e))

def fasRemovedInstructions (p : List (Nat × Nat) × List (Nat × Nat)) :
    List FASRemovedInstruction :=
  fasRemovedInitInstruction p.1 :: p.2.map fasRemovedElementInstruction

def fasRemovedRunnerInit : FASRemovedAcc :=
  ([], false)

def fasRemovedStep (p : FASRemovedAcc × FASRemovedInstruction) : FASRemovedAcc :=
  if p.2.1 then
    (p.1.1, graphBoolAndPair (p.1.2, fasRemovedEdgeInGraphBool (p.1.1, p.2.2.2)))
  else
    (p.2.2.1, true)

def fasRemovedFromInstructions (xs : List FASRemovedInstruction) : Bool :=
  (xs.foldl (fun acc instr => fasRemovedStep (acc, instr)) fasRemovedRunnerInit).2

def fasAllRemovedInGraphBool (p : List (Nat × Nat) × List (Nat × Nat)) : Bool :=
  fasRemovedFromInstructions (fasRemovedInstructions p)

theorem fasRemovedElementInstructions_fold_eq_true_iff
    (removed edges : List (Nat × Nat)) (ok : Bool) :
    ((removed.map fasRemovedElementInstruction).foldl
        (fun acc instr => fasRemovedStep (acc, instr)) (edges, ok)).2 = true ↔
      ok = true ∧ ∀ e ∈ removed, fasRemovedEdgeInGraphBool (edges, e) = true := by
  induction removed generalizing ok with
  | nil =>
      simp
  | cons e rest ih =>
      rw [List.map_cons, List.foldl_cons]
      change
        ((rest.map fasRemovedElementInstruction).foldl
            (fun acc instr => fasRemovedStep (acc, instr))
            (edges, graphBoolAndPair (ok, fasRemovedEdgeInGraphBool (edges, e)))).2 = true ↔
          ok = true ∧ ∀ f ∈ e :: rest, fasRemovedEdgeInGraphBool (edges, f) = true
      rw [ih]
      constructor
      · rintro ⟨hHead, hTail⟩
        rcases (graphBoolAndPair_eq_true_iff (ok, fasRemovedEdgeInGraphBool (edges, e))).1
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
        · exact (graphBoolAndPair_eq_true_iff (ok, fasRemovedEdgeInGraphBool (edges, e))).2
            ⟨hok, hAll e (by simp)⟩
        · intro f hf
          exact hAll f (List.mem_cons_of_mem e hf)

theorem fasAllRemovedInGraphBool_eq_true_iff
    (p : List (Nat × Nat) × List (Nat × Nat)) :
    fasAllRemovedInGraphBool p = true ↔ ∀ e ∈ p.2, e ∈ p.1 := by
  rcases p with ⟨edges, removed⟩
  change
    (((fasRemovedInitInstruction edges :: removed.map fasRemovedElementInstruction).foldl
        (fun acc instr => fasRemovedStep (acc, instr)) fasRemovedRunnerInit).2 = true) ↔
      ∀ e ∈ removed, e ∈ edges
  rw [List.foldl_cons]
  change
    (((removed.map fasRemovedElementInstruction).foldl
        (fun acc instr => fasRemovedStep (acc, instr)) (edges, true)).2 = true) ↔
      ∀ e ∈ removed, e ∈ edges
  rw [fasRemovedElementInstructions_fold_eq_true_iff removed edges true]
  simp [fasRemovedEdgeInGraphBool_eq_true_iff]

theorem fasRemovedInitInstruction_tm_polytime :
    TMPolyTimeMap edgeListStructuredEncodedType fasRemovedInstructionEncodedType
      fasRemovedInitInstruction := by
  have hFalse :
      TMPolyTimeMap edgeListStructuredEncodedType EncodedType.bool
        (fun _ : List (Nat × Nat) => false) :=
    TMPolyTimeMap.const edgeListStructuredEncodedType EncodedType.bool false
  have hEdges : TMPolyTimeMap edgeListStructuredEncodedType edgeListStructuredEncodedType id :=
    TMPolyTimeMap.id edgeListStructuredEncodedType
  have hDummyEdge :
      TMPolyTimeMap edgeListStructuredEncodedType edgeStructuredEncodedType
        (fun _ : List (Nat × Nat) => ((0, 0) : Nat × Nat)) :=
    TMPolyTimeMap.const edgeListStructuredEncodedType edgeStructuredEncodedType
      (show edgeStructuredEncodedType.Carrier from ((0, 0) : Nat × Nat))
  have hPayload :
      TMPolyTimeMap edgeListStructuredEncodedType
        (EncodedType.prod edgeListStructuredEncodedType edgeStructuredEncodedType)
        (fun edges : List (Nat × Nat) =>
          (edges, (show edgeStructuredEncodedType.Carrier from ((0, 0) : Nat × Nat)))) :=
    TMPolyTimeMap.prod_mk hEdges hDummyEdge
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [fasRemovedInitInstruction, fasRemovedInstructionEncodedType] using hOut

theorem fasRemovedElementInstruction_tm_polytime :
    TMPolyTimeMap edgeStructuredEncodedType fasRemovedInstructionEncodedType
      fasRemovedElementInstruction := by
  have hTrue : TMPolyTimeMap edgeStructuredEncodedType EncodedType.bool
      (fun _ : Nat × Nat => true) :=
    TMPolyTimeMap.const edgeStructuredEncodedType EncodedType.bool true
  have hEmpty :
      TMPolyTimeMap edgeStructuredEncodedType edgeListStructuredEncodedType
        (fun _ : Nat × Nat => ([] : List (Nat × Nat))) :=
    TMPolyTimeMap.const edgeStructuredEncodedType edgeListStructuredEncodedType []
  have hEdge : TMPolyTimeMap edgeStructuredEncodedType edgeStructuredEncodedType id :=
    TMPolyTimeMap.id edgeStructuredEncodedType
  have hPayload :
      TMPolyTimeMap edgeStructuredEncodedType
        (EncodedType.prod edgeListStructuredEncodedType edgeStructuredEncodedType)
        (fun e : Nat × Nat => (([] : List (Nat × Nat)), e)) :=
    TMPolyTimeMap.prod_mk hEmpty hEdge
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [fasRemovedElementInstruction, fasRemovedInstructionEncodedType] using hOut

theorem fasRemovedInstructions_tm_polytime :
    TMPolyTimeMap fasRemovedInstructionInputEncodedType
      fasRemovedInstructionListEncodedType fasRemovedInstructions := by
  let X := fasRemovedInstructionInputEncodedType
  have hEdges : TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, fasRemovedInstructionInputEncodedType] using
      TMPolyTimeMap.fst edgeListStructuredEncodedType edgeListStructuredEncodedType
  have hRemoved :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, fasRemovedInstructionInputEncodedType] using
      TMPolyTimeMap.snd edgeListStructuredEncodedType edgeListStructuredEncodedType
  have hInit :
      TMPolyTimeMap X fasRemovedInstructionEncodedType
        (fun p : X.Carrier => fasRemovedInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp fasRemovedInitInstruction_tm_polytime hEdges
    simpa [Function.comp, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X fasRemovedInstructionListEncodedType
        (fun p : X.Carrier => [fasRemovedInitInstruction p.1]) := by
    have hComp :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton fasRemovedInstructionEncodedType) hInit
    simpa [Function.comp, fasRemovedInstructionListEncodedType, X] using hComp
  have hElementInstructions :
      TMPolyTimeMap X fasRemovedInstructionListEncodedType
        (fun p : X.Carrier => p.2.map fasRemovedElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map fasRemovedElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRemoved
    simpa [Function.comp, fasRemovedInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod fasRemovedInstructionListEncodedType
          fasRemovedInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([fasRemovedInitInstruction p.1], p.2.map fasRemovedElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hElementInstructions
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append fasRemovedInstructionEncodedType) hAppendInput
  simpa [Function.comp, fasRemovedInstructions, fasRemovedInstructionListEncodedType, X]
    using hOut

theorem fasRemovedStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod fasRemovedAccEncodedType fasRemovedInstructionEncodedType)
      fasRemovedAccEncodedType
      fasRemovedStep := by
  let X := EncodedType.prod fasRemovedAccEncodedType fasRemovedInstructionEncodedType
  let A := fasRemovedAccEncodedType
  let Payload := EncodedType.prod edgeListStructuredEncodedType edgeStructuredEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst A fasRemovedInstructionEncodedType
  have hInstr : TMPolyTimeMap X fasRemovedInstructionEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd A fasRemovedInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, fasRemovedInstructionEncodedType, Payload, X] using hComp
  have hPayload : TMPolyTimeMap X Payload (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, fasRemovedInstructionEncodedType, Payload, X] using hComp
  have hAccEdges : TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, fasRemovedAccEncodedType, X] using hComp
  have hOk : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd edgeListStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, fasRemovedAccEncodedType, X] using hComp
  have hPayloadEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType edgeStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hPayloadEdge :
      TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd edgeListStructuredEncodedType edgeStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hCheckInput :
      TMPolyTimeMap X fasRemovedEdgeInGraphInputEncodedType
        (fun p : X.Carrier => (p.1.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAccEdges hPayloadEdge
  have hCheck :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => fasRemovedEdgeInGraphBool (p.1.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp fasRemovedEdgeInGraphBool_tm_polytime hCheckInput
    simpa [Function.comp, fasRemovedEdgeInGraphInputEncodedType] using hComp
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier => (p.1.2, fasRemovedEdgeInGraphBool (p.1.1, p.2.2.2))) :=
    TMPolyTimeMap.prod_mk hOk hCheck
  have hAnd :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier =>
          graphBoolAndPair (p.1.2, fasRemovedEdgeInGraphBool (p.1.1, p.2.2.2))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
    simpa [Function.comp] using hComp
  have hTrueBranch :
      TMPolyTimeMap X A
        (fun p : X.Carrier =>
          (p.1.1, graphBoolAndPair (p.1.2, fasRemovedEdgeInGraphBool (p.1.1, p.2.2.2)))) :=
    TMPolyTimeMap.prod_mk hAccEdges hAnd
  have hTrueConst : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hFalseBranch : TMPolyTimeMap X A (fun p : X.Carrier => (p.2.2.1, true)) :=
    TMPolyTimeMap.prod_mk hPayloadEdges hTrueConst
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
                graphBoolAndPair (p.2.1.2, fasRemovedEdgeInGraphBool (p.2.1.1, p.2.2.2.2)))
          | false => (p.2.2.2.1, true)) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier => (p.2.2.1, true))
      (fTrue := fun p : X.Carrier =>
        (p.1.1, graphBoolAndPair (p.1.2, fasRemovedEdgeInGraphBool (p.1.1, p.2.2.2))))
      hFalseBranch hTrueBranch
  have hOut := TMPolyTimeMap.comp hBranchOnProduct hBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨edges, ok⟩, ⟨tag, payloadEdges, edge⟩⟩
  cases tag <;> rfl

theorem fasRemovedStep_inputSize_le
    (source : fasRemovedInstructionListEncodedType.Carrier)
    (acc : fasRemovedAccEncodedType.Carrier)
    (instr : fasRemovedInstructionEncodedType.Carrier)
    (hAcc :
      fasRemovedAccEncodedType.inputSize acc ≤
        fasRemovedInstructionListEncodedType.inputSize source + 10)
    (hInstr :
      fasRemovedInstructionEncodedType.inputSize instr ≤
        fasRemovedInstructionListEncodedType.inputSize source) :
    fasRemovedAccEncodedType.inputSize (fasRemovedStep (acc, instr)) ≤
      fasRemovedInstructionListEncodedType.inputSize source + 10 := by
  rcases acc with ⟨edges, ok⟩
  rcases instr with ⟨tag, payload⟩
  rcases payload with ⟨payloadEdges, edge⟩
  cases tag
  · have hLocal :
        fasRemovedAccEncodedType.inputSize (payloadEdges, true) ≤
          fasRemovedInstructionEncodedType.inputSize (false, (payloadEdges, edge)) + 10 := by
      simp [fasRemovedAccEncodedType, fasRemovedInstructionEncodedType,
        EncodedType.inputSize, EncodedType.prod, EncodedType.bool]
      omega
    exact (by simpa [fasRemovedStep] using hLocal.trans (Nat.add_le_add_right hInstr 10))
  · have hLocal :
        fasRemovedAccEncodedType.inputSize
            (fasRemovedStep ((edges, ok), (true, (payloadEdges, edge)))) ≤
          fasRemovedAccEncodedType.inputSize (edges, ok) := by
      by_cases h : fasRemovedEdgeInGraphBool (edges, edge) = true <;>
        cases ok <;>
          simp [fasRemovedStep, h, fasRemovedAccEncodedType,
            EncodedType.inputSize, EncodedType.prod, EncodedType.bool]
    exact hLocal.trans hAcc

theorem fasRemovedFold_tm_polytime :
    TMPolyTimeMap fasRemovedInstructionListEncodedType fasRemovedAccEncodedType
      (fun xs : fasRemovedInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc instr => fasRemovedStep (acc, instr)) fasRemovedRunnerInit) := by
  rcases fasRemovedStep_tm_polytime with ⟨hStep⟩
  let bound : Polynomial Nat := Polynomial.X + Polynomial.C 10
  refine
    TMPolyTimeMap.list_foldl_typed_bounded
      fasRemovedInstructionEncodedType fasRemovedAccEncodedType
      fasRemovedStep fasRemovedRunnerInit hStep bound ?_ ?_
  · intro xs
    change fasRemovedAccEncodedType.inputSize fasRemovedRunnerInit ≤
      (Polynomial.X + Polynomial.C 10).eval
        (fasRemovedInstructionEncodedType.list.inputSize xs)
    have hInit : fasRemovedAccEncodedType.inputSize fasRemovedRunnerInit ≤ 10 := by
      native_decide
    simp [Polynomial.eval_add]
    omega
  · intro source acc instr hAcc hInstr
    have hAcc' :
        fasRemovedAccEncodedType.inputSize acc ≤
          fasRemovedInstructionListEncodedType.inputSize source + 10 := by
      simpa [fasRemovedInstructionListEncodedType, bound, Polynomial.eval_add] using hAcc
    have hInstr' :
        fasRemovedInstructionEncodedType.inputSize instr ≤
          fasRemovedInstructionListEncodedType.inputSize source := by
      simpa [fasRemovedInstructionListEncodedType] using hInstr
    simpa [fasRemovedInstructionListEncodedType, bound, Polynomial.eval_add] using
      fasRemovedStep_inputSize_le source acc instr hAcc' hInstr'

theorem fasRemovedFromInstructions_tm_polytime :
    TMPolyTimeMap fasRemovedInstructionListEncodedType EncodedType.bool
      fasRemovedFromInstructions := by
  have hFold := fasRemovedFold_tm_polytime
  have hOk := TMPolyTimeMap.snd edgeListStructuredEncodedType EncodedType.bool
  have hComp := TMPolyTimeMap.comp hOk hFold
  simpa [Function.comp, fasRemovedFromInstructions, fasRemovedAccEncodedType] using hComp

theorem fasAllRemovedInGraphBool_tm_polytime :
    TMPolyTimeMap fasRemovedInstructionInputEncodedType EncodedType.bool
      fasAllRemovedInGraphBool := by
  have hComp := TMPolyTimeMap.comp fasRemovedFromInstructions_tm_polytime
    fasRemovedInstructions_tm_polytime
  simpa [Function.comp, fasAllRemovedInGraphBool] using hComp

end FeedbackArcSetMembership

end Karp21
end ComplexityReduction
