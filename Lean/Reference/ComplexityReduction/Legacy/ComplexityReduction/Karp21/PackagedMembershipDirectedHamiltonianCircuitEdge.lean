/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.EdgeScan

/-!
Direct standard-TM Boolean runner for membership of an ordered directed edge in
the encoded graph edge list.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics.Graph

namespace DirectedHamiltonianCircuitMembership

def directedEdgeScanRunnerStep
    (p : edgeScanAccEncodedType.Carrier × edgeScanInstructionEncodedType.Carrier) :
    edgeScanAccEncodedType.Carrier :=
  match p.2.1 with
  | false => (p.2.2.1, false)
  | true =>
      (p.1.1, graphBoolOrPair
        (p.1.2, edgePairEqBool (p.1.1, p.2.2.2)))

def sourceHasDirectedEdgeFromInstructions
    (xs : edgeScanInstructionListEncodedType.Carrier) : Bool :=
  (xs.foldl (fun acc x => directedEdgeScanRunnerStep (acc, x)) edgeScanRunnerInit).2

def sourceHasDirectedEdgeBool
    (p : (Nat × Nat) × List (Nat × Nat)) : Bool :=
  sourceHasDirectedEdgeFromInstructions (edgeScanInstructions p)

def sourceHasDirectedEdgeBool' (p : (Nat × Nat) × List (Nat × Nat)) : Bool :=
  sourceHasDirectedEdgeFromInstructions (edgeScanInstructions p)

theorem sourceHasDirectedEdgeBool_eq_sourceHasDirectedEdgeBool'
    (p : (Nat × Nat) × List (Nat × Nat)) :
    sourceHasDirectedEdgeBool p = sourceHasDirectedEdgeBool' p := by
  rfl

theorem directedEdgeScanFoldEdgeInstructions_pair
    (target : Nat × Nat) (found : Bool)
    (edges : List (Nat × Nat)) :
    ((edges.map edgeScanEdgeInstruction).foldl
        (fun acc x => directedEdgeScanRunnerStep (acc, x)) (target, found)).1 = target := by
  induction edges generalizing found with
  | nil =>
      simp
  | cons e es ih =>
      simpa [directedEdgeScanRunnerStep, edgeScanEdgeInstruction] using
        ih (graphBoolOrPair (found, edgePairEqBool (target, e)))

theorem directedEdgeScanFoldEdgeInstructions_found_iff
    (target : Nat × Nat) (found : Bool)
    (edges : List (Nat × Nat)) :
    ((edges.map edgeScanEdgeInstruction).foldl
        (fun acc x => directedEdgeScanRunnerStep (acc, x)) (target, found)).2 = true ↔
      found = true ∨ ∃ e ∈ edges, edgePairEqBool (target, e) = true := by
  induction edges generalizing found with
  | nil =>
      cases found <;> simp
  | cons e es ih =>
      rw [show
        ((e :: es).map edgeScanEdgeInstruction).foldl
            (fun acc x => directedEdgeScanRunnerStep (acc, x)) (target, found) =
          (es.map edgeScanEdgeInstruction).foldl
            (fun acc x => directedEdgeScanRunnerStep (acc, x))
            (target, graphBoolOrPair (found, edgePairEqBool (target, e))) by
        rfl]
      rw [ih]
      constructor
      · intro h
        rcases h with h | h
        · rcases (graphBoolOrPair_eq_true_iff
            (found, edgePairEqBool (target, e))).1 h with hFound | hMatch
          · exact Or.inl hFound
          · exact Or.inr ⟨e, by simp, hMatch⟩
        · rcases h with ⟨x, hx, hMatch⟩
          exact Or.inr ⟨x, by simp [hx], hMatch⟩
      · intro h
        rcases h with hFound | h
        · left
          exact (graphBoolOrPair_eq_true_iff
            (found, edgePairEqBool (target, e))).2 (Or.inl hFound)
        · rcases h with ⟨x, hx, hMatch⟩
          simp at hx
          rcases hx with hx | hx
          · left
            subst x
            exact (graphBoolOrPair_eq_true_iff
              (found, edgePairEqBool (target, e))).2 (Or.inr hMatch)
          · right
            exact ⟨x, hx, hMatch⟩

theorem sourceHasDirectedEdgeBool'_eq_true_iff
    (target : Nat × Nat) (edges : List (Nat × Nat)) :
    sourceHasDirectedEdgeBool' (target, edges) = true ↔ target ∈ edges := by
  change
    ((edgeScanInitInstruction target :: edges.map edgeScanEdgeInstruction).foldl
        (fun acc x => directedEdgeScanRunnerStep (acc, x)) edgeScanRunnerInit).2 = true ↔
      target ∈ edges
  rw [show
    (edgeScanInitInstruction target :: edges.map edgeScanEdgeInstruction).foldl
        (fun acc x => directedEdgeScanRunnerStep (acc, x)) edgeScanRunnerInit =
      (edges.map edgeScanEdgeInstruction).foldl
        (fun acc x => directedEdgeScanRunnerStep (acc, x)) (target, false) by
    rfl]
  rw [directedEdgeScanFoldEdgeInstructions_found_iff target false edges]
  constructor
  · rintro (_ | h)
    · contradiction
    · rcases h with ⟨e, he, hmatch⟩
      have heq : e = target := by
        simpa using (edgePairEqBool_eq_true_iff (target, e)).1 hmatch
      subst e
      exact he
  · intro h
    right
    exact ⟨target, h, (edgePairEqBool_eq_true_iff (target, target)).2 rfl⟩

theorem sourceHasDirectedEdgeBool_eq_true_iff
    (target : Nat × Nat) (edges : List (Nat × Nat)) :
    sourceHasDirectedEdgeBool (target, edges) = true ↔ target ∈ edges := by
  rw [sourceHasDirectedEdgeBool_eq_sourceHasDirectedEdgeBool',
    sourceHasDirectedEdgeBool'_eq_true_iff]

theorem sourceHasDirectedEdgeBool_graph_eq_true_iff (g : GraphInput) (u v : Nat) :
    sourceHasDirectedEdgeBool ((u, v), g.edges) = true ↔
      HasDirectedEdge g u v := by
  simpa [HasDirectedEdge] using
    sourceHasDirectedEdgeBool_eq_true_iff (u, v) g.edges

theorem directedEdgeScanRunnerStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod edgeScanAccEncodedType edgeScanInstructionEncodedType)
      edgeScanAccEncodedType
      directedEdgeScanRunnerStep := by
  let X := EncodedType.prod edgeScanAccEncodedType edgeScanInstructionEncodedType
  have hAcc : TMPolyTimeMap X edgeScanAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst edgeScanAccEncodedType edgeScanInstructionEncodedType
  have hInstr :
      TMPolyTimeMap X edgeScanInstructionEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd edgeScanAccEncodedType edgeScanInstructionEncodedType
  have hTarget : TMPolyTimeMap X vertexPairEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst vertexPairEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, edgeScanAccEncodedType, X] using hComp
  have hFound : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd vertexPairEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, edgeScanAccEncodedType, X] using hComp
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool edgeScanInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, edgeScanInstructionEncodedType, X] using hComp
  have hPayload :
      TMPolyTimeMap X edgeScanInstructionPayloadEncodedType (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool edgeScanInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, edgeScanInstructionEncodedType, X] using hComp
  have hInitPair :
      TMPolyTimeMap X vertexPairEncodedType (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst vertexPairEncodedType edgeStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, edgeScanInstructionPayloadEncodedType, X] using hComp
  have hEdge :
      TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd vertexPairEncodedType edgeStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, edgeScanInstructionPayloadEncodedType, X] using hComp
  have hFalse : TMPolyTimeMap X EncodedType.bool (fun _ => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hInitOut :
      TMPolyTimeMap X edgeScanAccEncodedType
        (fun p : X.Carrier => (p.2.2.1, false)) :=
    TMPolyTimeMap.prod_mk hInitPair hFalse
  have hMatchInput :
      TMPolyTimeMap X (EncodedType.prod vertexPairEncodedType edgeStructuredEncodedType)
        (fun p : X.Carrier => (p.1.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hTarget hEdge
  have hMatch :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => edgePairEqBool (p.1.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp edgePairEqBool_tm_polytime hMatchInput
    simpa [Function.comp, X] using hComp
  have hFoundOrInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier => (p.1.2, edgePairEqBool (p.1.1, p.2.2.2))) :=
    TMPolyTimeMap.prod_mk hFound hMatch
  have hFoundOr :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier =>
          graphBoolOrPair (p.1.2, edgePairEqBool (p.1.1, p.2.2.2))) := by
    have hComp := TMPolyTimeMap.comp graphBoolOrPair_tm_polytime hFoundOrInput
    simpa [Function.comp, X] using hComp
  have hScanOut :
      TMPolyTimeMap X edgeScanAccEncodedType
        (fun p : X.Carrier =>
          (p.1.1, graphBoolOrPair (p.1.2, edgePairEqBool (p.1.1, p.2.2.2)))) :=
    TMPolyTimeMap.prod_mk hTarget hFoundOr
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool X)
        edgeScanAccEncodedType
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true =>
              (p.2.1.1,
                graphBoolOrPair (p.2.1.2, edgePairEqBool (p.2.1.1, p.2.2.2.2)))
          | false => (p.2.2.2.1, false)) :=
    graphBoolProduct_dispatch_tm_polytime X edgeScanAccEncodedType
      (fFalse := fun p : X.Carrier => (p.2.2.1, false))
      (fTrue := fun p : X.Carrier =>
        (p.1.1, graphBoolOrPair (p.1.2, edgePairEqBool (p.1.1, p.2.2.2))))
      (hFalse := hInitOut) (hTrue := hScanOut)
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  ext p
  rcases p with ⟨acc, instr⟩
  rcases instr with ⟨tag, payload⟩
  cases tag <;> rfl

theorem directedEdgeScanRunnerStep_inputSize_le
    (source : edgeScanInstructionListEncodedType.Carrier)
    (acc : edgeScanAccEncodedType.Carrier)
    (instr : edgeScanInstructionEncodedType.Carrier)
    (hAcc :
      edgeScanAccEncodedType.inputSize acc ≤
        edgeScanInstructionListEncodedType.inputSize source + 10)
    (hInstr :
      edgeScanInstructionEncodedType.inputSize instr ≤
        edgeScanInstructionListEncodedType.inputSize source) :
    edgeScanAccEncodedType.inputSize (directedEdgeScanRunnerStep (acc, instr)) ≤
      edgeScanInstructionListEncodedType.inputSize source + 10 := by
  rcases acc with ⟨target, found⟩
  rcases instr with ⟨tag, payload⟩
  rcases payload with ⟨initPair, edge⟩
  cases tag
  · have hLocal :
        edgeScanAccEncodedType.inputSize (initPair, false) ≤
          edgeScanInstructionEncodedType.inputSize (false, (initPair, edge)) + 10 := by
      simp [edgeScanAccEncodedType, edgeScanInstructionEncodedType,
        edgeScanInstructionPayloadEncodedType, vertexPairEncodedType, edgeStructuredEncodedType,
        EncodedType.inputSize, EncodedType.prod, EncodedType.bool, EncodedType.nat]
      omega
    simpa [directedEdgeScanRunnerStep] using hLocal.trans (Nat.add_le_add_right hInstr 10)
  · have hLocal :
        edgeScanAccEncodedType.inputSize
            (target, graphBoolOrPair (found, edgePairEqBool (target, edge))) ≤
          edgeScanAccEncodedType.inputSize (target, found) := by
      simp [edgeScanAccEncodedType, vertexPairEncodedType, EncodedType.inputSize,
        EncodedType.prod, EncodedType.bool, EncodedType.nat]
    simpa [directedEdgeScanRunnerStep] using hLocal.trans hAcc

theorem directedEdgeScanRunnerFold_tm_polytime :
    TMPolyTimeMap
      edgeScanInstructionListEncodedType
      edgeScanAccEncodedType
      (fun xs : edgeScanInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc x => directedEdgeScanRunnerStep (acc, x)) edgeScanRunnerInit) := by
  rcases directedEdgeScanRunnerStep_tm_polytime with ⟨hStep⟩
  let bound : Polynomial Nat := Polynomial.X + Polynomial.C 10
  refine
    TMPolyTimeMap.list_foldl_typed_bounded
      edgeScanInstructionEncodedType edgeScanAccEncodedType
      directedEdgeScanRunnerStep edgeScanRunnerInit hStep bound ?_ ?_
  · intro xs
    change edgeScanAccEncodedType.inputSize edgeScanRunnerInit ≤
      (Polynomial.X + Polynomial.C 10).eval
        (edgeScanInstructionEncodedType.list.inputSize xs)
    have hInit : edgeScanAccEncodedType.inputSize edgeScanRunnerInit ≤ 10 := by
      simp [edgeScanRunnerInit, edgeScanDefaultPair, edgeScanAccEncodedType,
        vertexPairEncodedType, EncodedType.inputSize, EncodedType.prod,
        EncodedType.bool, EncodedType.nat]
    simp [Polynomial.eval_add]
    omega
  · intro source acc instr hAcc hInstr
    have hAcc' :
        edgeScanAccEncodedType.inputSize acc ≤
          edgeScanInstructionListEncodedType.inputSize source + 10 := by
      simpa [edgeScanInstructionListEncodedType, bound, Polynomial.eval_add] using hAcc
    have hInstr' :
        edgeScanInstructionEncodedType.inputSize instr ≤
          edgeScanInstructionListEncodedType.inputSize source := by
      simpa [edgeScanInstructionListEncodedType] using hInstr
    simpa [edgeScanInstructionListEncodedType, bound, Polynomial.eval_add] using
      directedEdgeScanRunnerStep_inputSize_le source acc instr hAcc' hInstr'

theorem sourceHasDirectedEdgeFromInstructions_tm_polytime :
    TMPolyTimeMap
      edgeScanInstructionListEncodedType
      EncodedType.bool
      sourceHasDirectedEdgeFromInstructions := by
  have hFold := directedEdgeScanRunnerFold_tm_polytime
  have hFound := TMPolyTimeMap.snd vertexPairEncodedType EncodedType.bool
  have hComp := TMPolyTimeMap.comp hFound hFold
  simpa [Function.comp, sourceHasDirectedEdgeFromInstructions, edgeScanAccEncodedType]
    using hComp

theorem sourceHasDirectedEdgeBool'_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod vertexPairEncodedType edgeListStructuredEncodedType)
      EncodedType.bool
      sourceHasDirectedEdgeBool' := by
  have hComp :=
    TMPolyTimeMap.comp sourceHasDirectedEdgeFromInstructions_tm_polytime
      edgeScanInstructions_tm_polytime
  simpa [Function.comp, sourceHasDirectedEdgeBool'] using hComp

theorem sourceHasDirectedEdgeBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod vertexPairEncodedType edgeListStructuredEncodedType)
      EncodedType.bool
      sourceHasDirectedEdgeBool := by
  exact sourceHasDirectedEdgeBool'_tm_polytime

end DirectedHamiltonianCircuitMembership
end Karp21
end ComplexityReduction
