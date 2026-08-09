/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.StrictPairs
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.SplitWith.TaggedDispatch

/-!
TM-backed source-edge scanning for faithful structured graph-complement routes.

This module checks, for a fixed strict candidate pair `(u, v)`, whether the
source graph edge list already contains either orientation.  It is the
predicate layer needed before complement-edge list enumeration.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics.Graph

/-! ### Small Boolean branch helpers -/

def graphBoolPayloadEncodedType (X : EncodedType) : EncodedType where
  Carrier := Bool × X.Carrier
  Symbol := Bool ⊕ X.Symbol
  finite_symbol := inferInstance
  encode := fun p => Sum.inl p.1 :: (X.encode p.2).map Sum.inr

def graphBoolPayloadAsSum (X : EncodedType) (p : (graphBoolPayloadEncodedType X).Carrier) :
    X.Carrier ⊕ X.Carrier :=
  if p.1 then Sum.inr p.2 else Sum.inl p.2

theorem graphBoolPayloadFromProduct_encode_filterMap (X : EncodedType)
    (p : (EncodedType.prod EncodedType.bool X).Carrier) :
    (graphBoolPayloadEncodedType X).encode p =
      ((EncodedType.prod EncodedType.bool X).encode p).filterMap
        (fun
          | some (Sum.inl b) => some (Sum.inl b)
          | some (Sum.inr s) => some (Sum.inr s)
          | none => none) := by
  rcases p with ⟨b, x⟩
  simp [graphBoolPayloadEncodedType, EncodedType.prod, EncodedType.bool]

noncomputable def graphBoolPayloadFromProductTMBackedMap (X : EncodedType) :
    TMBackedCostedMap
      (EncodedType.prod EncodedType.bool X)
      (graphBoolPayloadEncodedType X)
      (fun p : (EncodedType.prod EncodedType.bool X).Carrier => p) :=
  TMBackedCostedMap.symbolFilterMap
    (EncodedType.prod EncodedType.bool X)
    (graphBoolPayloadEncodedType X)
    (fun p : (EncodedType.prod EncodedType.bool X).Carrier => p)
    (fun
      | some (Sum.inl b) => some (Sum.inl b)
      | some (Sum.inr s) => some (Sum.inr s)
      | none => none)
    (fun p => graphBoolPayloadFromProduct_encode_filterMap X p)

theorem graphBoolPayload_dispatch_tm_polytime
    (X Y : EncodedType) {fFalse fTrue : X.Carrier → Y.Carrier}
    (hFalse : TMPolyTimeMap X Y fFalse) (hTrue : TMPolyTimeMap X Y fTrue) :
    TMPolyTimeMap
      (graphBoolPayloadEncodedType X)
      Y
      (fun p : (graphBoolPayloadEncodedType X).Carrier =>
        if p.1 then fTrue p.2 else fFalse p.2) := by
  rcases hFalse with ⟨hFalse⟩
  rcases hTrue with ⟨hTrue⟩
  let hSum := taggedBranchDispatchComputableInPolyTime hFalse hTrue
  refine ⟨?_⟩
  exact
    { tm := hSum.tm
      inputAlphabet := hSum.inputAlphabet
      outputAlphabet := hSum.outputAlphabet
      time := hSum.time
      outputsFun := by
        intro p
        rcases p with ⟨b, x⟩
        cases b
        · simpa [graphBoolPayloadEncodedType, graphBoolPayloadAsSum] using
            hSum.outputsFun (Sum.inl x)
        · simpa [graphBoolPayloadEncodedType, graphBoolPayloadAsSum] using
            hSum.outputsFun (Sum.inr x) }

theorem graphBoolProduct_dispatch_tm_polytime
    (X Y : EncodedType) {fFalse fTrue : X.Carrier → Y.Carrier}
    (hFalse : TMPolyTimeMap X Y fFalse) (hTrue : TMPolyTimeMap X Y fTrue) :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.bool X)
      Y
      (fun p : (EncodedType.prod EncodedType.bool X).Carrier =>
        match p.1 with
        | true => fTrue p.2
        | false => fFalse p.2) := by
  have hBranch :=
    graphBoolPayload_dispatch_tm_polytime X Y
      (fFalse := fFalse) (fTrue := fTrue) hFalse hTrue
  have hTagged := graphBoolPayloadFromProductTMBackedMap X |>.tm_polytime
  have hComp := TMPolyTimeMap.comp hBranch hTagged
  convert hComp using 1
  ext p
  rcases p with ⟨b, x⟩
  cases b <;> rfl

def graphBoolAndPair (p : Bool × Bool) : Bool :=
  match p.1 with
  | true => p.2
  | false => false

theorem graphBoolAndPair_eq_true_iff (p : Bool × Bool) :
    graphBoolAndPair p = true ↔ p.1 = true ∧ p.2 = true := by
  cases p with
  | mk a b =>
      cases a <;> cases b <;> simp [graphBoolAndPair]

theorem graphBoolAndPair_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      EncodedType.bool
      graphBoolAndPair := by
  have hFalse : TMPolyTimeMap EncodedType.bool EncodedType.bool (fun _ : Bool => false) :=
    TMPolyTimeMap.const EncodedType.bool EncodedType.bool false
  have hTrue : TMPolyTimeMap EncodedType.bool EncodedType.bool (fun b : Bool => b) :=
    TMPolyTimeMap.id EncodedType.bool
  simpa [graphBoolAndPair] using
    graphBoolProduct_dispatch_tm_polytime EncodedType.bool EncodedType.bool
      (fFalse := fun _ : Bool => false) (fTrue := fun b : Bool => b) hFalse hTrue

def graphBoolOrPair (p : Bool × Bool) : Bool :=
  match p.1 with
  | true => true
  | false => p.2

theorem graphBoolOrPair_eq_true_iff (p : Bool × Bool) :
    graphBoolOrPair p = true ↔ p.1 = true ∨ p.2 = true := by
  cases p with
  | mk a b =>
      cases a <;> cases b <;> simp [graphBoolOrPair]

theorem graphBoolOrPair_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      EncodedType.bool
      graphBoolOrPair := by
  have hFalse : TMPolyTimeMap EncodedType.bool EncodedType.bool (fun b : Bool => b) :=
    TMPolyTimeMap.id EncodedType.bool
  have hTrue : TMPolyTimeMap EncodedType.bool EncodedType.bool (fun _ : Bool => true) :=
    TMPolyTimeMap.const EncodedType.bool EncodedType.bool true
  simpa [graphBoolOrPair] using
    graphBoolProduct_dispatch_tm_polytime EncodedType.bool EncodedType.bool
      (fFalse := fun b : Bool => b) (fTrue := fun _ : Bool => true) hFalse hTrue

/-! ### Edge matching predicate -/

def edgePairEqBool (p : (Nat × Nat) × (Nat × Nat)) : Bool :=
  graphBoolAndPair (decide (p.1.1 = p.2.1), decide (p.1.2 = p.2.2))

theorem edgePairEqBool_eq_true_iff
    (p : (Nat × Nat) × (Nat × Nat)) :
    edgePairEqBool p = true ↔ p.2 = p.1 := by
  rcases p with ⟨⟨u, v⟩, ⟨a, b⟩⟩
  constructor
  · intro h
    have hBoth :=
      (graphBoolAndPair_eq_true_iff
        (decide (u = a), decide (v = b))).1 h
    have hu : u = a := of_decide_eq_true hBoth.1
    have hv : v = b := of_decide_eq_true hBoth.2
    subst a
    subst b
    rfl
  · intro h
    cases h
    simp [edgePairEqBool, graphBoolAndPair]

theorem edgePairEqBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod vertexPairEncodedType edgeStructuredEncodedType)
      EncodedType.bool
      edgePairEqBool := by
  let X := EncodedType.prod vertexPairEncodedType edgeStructuredEncodedType
  have hPair : TMPolyTimeMap X vertexPairEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst vertexPairEncodedType edgeStructuredEncodedType
  have hEdge : TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd vertexPairEncodedType edgeStructuredEncodedType
  have hLeftPair : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPair
    simpa [Function.comp, vertexPairEncodedType, X] using hComp
  have hRightPair : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPair
    simpa [Function.comp, vertexPairEncodedType, X] using hComp
  have hLeftEdge : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hEdge
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hRightEdge : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hEdge
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hLeftInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.1.1, p.2.1)) :=
    TMPolyTimeMap.prod_mk hLeftPair hLeftEdge
  have hRightInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.1.2, p.2.2)) :=
    TMPolyTimeMap.prod_mk hRightPair hRightEdge
  have hLeftEq := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hLeftInput
  have hRightEq := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hRightInput
  have hBoth :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : (Nat × Nat) × (Nat × Nat) =>
          (decide (p.1.1 = p.2.1), decide (p.1.2 = p.2.2))) :=
    TMPolyTimeMap.prod_mk hLeftEq hRightEq
  have hOut := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hBoth
  simpa [Function.comp, edgePairEqBool, X, vertexPairEncodedType, edgeStructuredEncodedType]
    using hOut

def undirectedEdgeMatchesPairBool
    (p : (Nat × Nat) × (Nat × Nat)) : Bool :=
  graphBoolOrPair
    (edgePairEqBool p, edgePairEqBool (vertexPairSwap p.1, p.2))

theorem undirectedEdgeMatchesPairBool_eq_true_iff
    (p : (Nat × Nat) × (Nat × Nat)) :
    undirectedEdgeMatchesPairBool p = true ↔
      p.2 = p.1 ∨ p.2 = vertexPairSwap p.1 := by
  simp [undirectedEdgeMatchesPairBool, graphBoolOrPair_eq_true_iff,
    edgePairEqBool_eq_true_iff]

theorem undirectedEdgeMatchesPairBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod vertexPairEncodedType edgeStructuredEncodedType)
      EncodedType.bool
      undirectedEdgeMatchesPairBool := by
  let X := EncodedType.prod vertexPairEncodedType edgeStructuredEncodedType
  have hDirect := edgePairEqBool_tm_polytime
  have hPair : TMPolyTimeMap X vertexPairEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst vertexPairEncodedType edgeStructuredEncodedType
  have hEdge : TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd vertexPairEncodedType edgeStructuredEncodedType
  have hSwapPair :
      TMPolyTimeMap X vertexPairEncodedType (fun p : X.Carrier => vertexPairSwap p.1) := by
    have hComp := TMPolyTimeMap.comp vertexPairSwap_tm_polytime hPair
    simpa [Function.comp, X] using hComp
  have hReverseInput :
      TMPolyTimeMap X (EncodedType.prod vertexPairEncodedType edgeStructuredEncodedType)
        (fun p : X.Carrier => (vertexPairSwap p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hSwapPair hEdge
  have hReverse := TMPolyTimeMap.comp edgePairEqBool_tm_polytime hReverseInput
  have hBoth :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (edgePairEqBool p, edgePairEqBool (vertexPairSwap p.1, p.2))) :=
    TMPolyTimeMap.prod_mk hDirect hReverse
  have hOut := TMPolyTimeMap.comp graphBoolOrPair_tm_polytime hBoth
  simpa [Function.comp, undirectedEdgeMatchesPairBool, X] using hOut

/-! ### Instruction-based source-edge scanner -/

def edgeScanAccEncodedType : EncodedType :=
  EncodedType.prod vertexPairEncodedType EncodedType.bool

def edgeScanInstructionPayloadEncodedType : EncodedType :=
  EncodedType.prod vertexPairEncodedType edgeStructuredEncodedType

def edgeScanInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool edgeScanInstructionPayloadEncodedType

def edgeScanInstructionListEncodedType : EncodedType :=
  EncodedType.list edgeScanInstructionEncodedType

def edgeScanDefaultPair : Nat × Nat :=
  ((0 : Nat), (0 : Nat))

def edgeScanRunnerInit : edgeScanAccEncodedType.Carrier :=
  (edgeScanDefaultPair, false)

def edgeScanInitInstruction
    (p : Nat × Nat) : edgeScanInstructionEncodedType.Carrier :=
  (false, (p, edgeScanDefaultPair))

def edgeScanEdgeInstruction
    (e : Nat × Nat) : edgeScanInstructionEncodedType.Carrier :=
  (true, (edgeScanDefaultPair, e))

def edgeScanRunnerStep
    (p : edgeScanAccEncodedType.Carrier × edgeScanInstructionEncodedType.Carrier) :
    edgeScanAccEncodedType.Carrier :=
  match p.2.1 with
  | false => (p.2.2.1, false)
  | true =>
      (p.1.1, graphBoolOrPair
        (p.1.2, undirectedEdgeMatchesPairBool (p.1.1, p.2.2.2)))

def edgeScanInstructions
    (p : (Nat × Nat) × List (Nat × Nat)) :
    edgeScanInstructionListEncodedType.Carrier :=
  edgeScanInitInstruction p.1 :: p.2.map edgeScanEdgeInstruction

def edgeScanFromInstructions (xs : edgeScanInstructionListEncodedType.Carrier) : Bool :=
  (xs.foldl (fun acc x => edgeScanRunnerStep (acc, x)) edgeScanRunnerInit).2

def sourceHasUndirectedEdgeBool
    (p : (Nat × Nat) × List (Nat × Nat)) : Bool :=
  edgeScanFromInstructions (edgeScanInstructions p)

def sourceNonedgeBool
    (p : (Nat × Nat) × List (Nat × Nat)) : Bool :=
  Bool.not (sourceHasUndirectedEdgeBool p)

theorem edgeScanFoldEdgeInstructions_pair
    (target : Nat × Nat) (found : Bool)
    (edges : List (Nat × Nat)) :
    ((edges.map edgeScanEdgeInstruction).foldl
        (fun acc x => edgeScanRunnerStep (acc, x)) (target, found)).1 = target := by
  induction edges generalizing found with
  | nil =>
      simp
  | cons e es ih =>
      simpa [edgeScanRunnerStep, edgeScanEdgeInstruction] using
        ih (graphBoolOrPair (found, undirectedEdgeMatchesPairBool (target, e)))

theorem edgeScanFoldEdgeInstructions_found_iff
    (target : Nat × Nat) (found : Bool)
    (edges : List (Nat × Nat)) :
    ((edges.map edgeScanEdgeInstruction).foldl
        (fun acc x => edgeScanRunnerStep (acc, x)) (target, found)).2 = true ↔
      found = true ∨
        ∃ e ∈ edges, undirectedEdgeMatchesPairBool (target, e) = true := by
  induction edges generalizing found with
  | nil =>
      cases found <;> simp
  | cons e es ih =>
      rw [show
        ((e :: es).map edgeScanEdgeInstruction).foldl
            (fun acc x => edgeScanRunnerStep (acc, x)) (target, found) =
          (es.map edgeScanEdgeInstruction).foldl
            (fun acc x => edgeScanRunnerStep (acc, x))
            (target, graphBoolOrPair
              (found, undirectedEdgeMatchesPairBool (target, e))) by
        rfl]
      rw [ih]
      constructor
      · intro h
        rcases h with h | h
        · rcases (graphBoolOrPair_eq_true_iff
            (found, undirectedEdgeMatchesPairBool (target, e))).1 h with hFound | hMatch
          · exact Or.inl hFound
          · exact Or.inr ⟨e, by simp, hMatch⟩
        · rcases h with ⟨x, hx, hMatch⟩
          exact Or.inr ⟨x, by simp [hx], hMatch⟩
      · intro h
        rcases h with hFound | h
        · left
          exact (graphBoolOrPair_eq_true_iff
            (found, undirectedEdgeMatchesPairBool (target, e))).2 (Or.inl hFound)
        · rcases h with ⟨x, hx, hMatch⟩
          simp at hx
          rcases hx with hx | hx
          · left
            subst x
            exact (graphBoolOrPair_eq_true_iff
              (found, undirectedEdgeMatchesPairBool (target, e))).2 (Or.inr hMatch)
          · right
            exact ⟨x, hx, hMatch⟩

theorem sourceHasUndirectedEdgeBool_eq_true_iff
    (target : Nat × Nat)
    (edges : List (Nat × Nat)) :
    sourceHasUndirectedEdgeBool (target, edges) = true ↔
      target ∈ edges ∨ vertexPairSwap target ∈ edges := by
  change
    ((edgeScanInitInstruction target :: edges.map edgeScanEdgeInstruction).foldl
        (fun acc x => edgeScanRunnerStep (acc, x)) edgeScanRunnerInit).2 = true ↔
      target ∈ edges ∨ vertexPairSwap target ∈ edges
  rw [show
    (edgeScanInitInstruction target :: edges.map edgeScanEdgeInstruction).foldl
        (fun acc x => edgeScanRunnerStep (acc, x)) edgeScanRunnerInit =
      (edges.map edgeScanEdgeInstruction).foldl
        (fun acc x => edgeScanRunnerStep (acc, x)) (target, false) by
    rfl]
  rw [edgeScanFoldEdgeInstructions_found_iff target false edges]
  constructor
  · rintro (_ | h)
    · contradiction
    · rcases h with ⟨e, he, hmatch⟩
      rcases (undirectedEdgeMatchesPairBool_eq_true_iff (target, e)).1 hmatch with h | h
      · have heq : e = target := by simpa using h
        subst e
        exact Or.inl he
      · have heq : e = vertexPairSwap target := by simpa using h
        subst e
        exact Or.inr he
  · intro h
    right
    rcases h with h | h
    · exact ⟨target, h, (undirectedEdgeMatchesPairBool_eq_true_iff (target, target)).2
        (Or.inl rfl)⟩
    · exact ⟨vertexPairSwap target, h,
        (undirectedEdgeMatchesPairBool_eq_true_iff (target, vertexPairSwap target)).2
          (Or.inr rfl)⟩

theorem sourceHasUndirectedEdgeBool_graph_eq_true_iff (g : GraphInput) (u v : Nat) :
    sourceHasUndirectedEdgeBool ((u, v), g.edges) = true ↔
      HasUndirectedEdge g u v := by
  simpa [HasUndirectedEdge, vertexPairSwap] using
    sourceHasUndirectedEdgeBool_eq_true_iff (u, v) g.edges

theorem sourceNonedgeBool_graph_eq_true_iff (g : GraphInput) (u v : Nat) :
    sourceNonedgeBool ((u, v), g.edges) = true ↔
      ¬ HasUndirectedEdge g u v := by
  rw [sourceNonedgeBool]
  by_cases hEdge : HasUndirectedEdge g u v
  · have hBool := (sourceHasUndirectedEdgeBool_graph_eq_true_iff g u v).2 hEdge
    simp [hBool, hEdge]
  · have hBool : sourceHasUndirectedEdgeBool ((u, v), g.edges) = false := by
      cases h : sourceHasUndirectedEdgeBool ((u, v), g.edges)
      · rfl
      · exact False.elim (hEdge ((sourceHasUndirectedEdgeBool_graph_eq_true_iff g u v).1 h))
    simp [hBool, hEdge]

/-! ### TM-backed scanner maps -/

theorem edgeScanInitInstruction_tm_polytime :
    TMPolyTimeMap
      vertexPairEncodedType
      edgeScanInstructionEncodedType
      edgeScanInitInstruction := by
  have hTag : TMPolyTimeMap vertexPairEncodedType EncodedType.bool (fun _ => false) :=
    TMPolyTimeMap.const vertexPairEncodedType EncodedType.bool false
  have hPair : TMPolyTimeMap vertexPairEncodedType vertexPairEncodedType id :=
    TMPolyTimeMap.id vertexPairEncodedType
  have hDefault :
      TMPolyTimeMap vertexPairEncodedType edgeStructuredEncodedType
        (fun _ => edgeScanDefaultPair) :=
    TMPolyTimeMap.const vertexPairEncodedType edgeStructuredEncodedType edgeScanDefaultPair
  have hPayload :
      TMPolyTimeMap vertexPairEncodedType edgeScanInstructionPayloadEncodedType
        (fun p : vertexPairEncodedType.Carrier => (p, edgeScanDefaultPair)) :=
    TMPolyTimeMap.prod_mk hPair hDefault
  have hOut := TMPolyTimeMap.prod_mk hTag hPayload
  simpa [edgeScanInitInstruction, edgeScanInstructionEncodedType,
    edgeScanInstructionPayloadEncodedType] using hOut

theorem edgeScanEdgeInstruction_tm_polytime :
    TMPolyTimeMap
      edgeStructuredEncodedType
      edgeScanInstructionEncodedType
      edgeScanEdgeInstruction := by
  have hTag : TMPolyTimeMap edgeStructuredEncodedType EncodedType.bool (fun _ => true) :=
    TMPolyTimeMap.const edgeStructuredEncodedType EncodedType.bool true
  have hDefault :
      TMPolyTimeMap edgeStructuredEncodedType vertexPairEncodedType
        (fun _ => edgeScanDefaultPair) :=
    TMPolyTimeMap.const edgeStructuredEncodedType vertexPairEncodedType edgeScanDefaultPair
  have hEdge : TMPolyTimeMap edgeStructuredEncodedType edgeStructuredEncodedType id :=
    TMPolyTimeMap.id edgeStructuredEncodedType
  have hPayload :
      TMPolyTimeMap edgeStructuredEncodedType edgeScanInstructionPayloadEncodedType
        (fun e : edgeStructuredEncodedType.Carrier => (edgeScanDefaultPair, e)) :=
    TMPolyTimeMap.prod_mk hDefault hEdge
  have hOut := TMPolyTimeMap.prod_mk hTag hPayload
  simpa [edgeScanEdgeInstruction, edgeScanInstructionEncodedType,
    edgeScanInstructionPayloadEncodedType] using hOut

theorem edgeScanInstructions_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod vertexPairEncodedType edgeListStructuredEncodedType)
      edgeScanInstructionListEncodedType
      edgeScanInstructions := by
  let X := EncodedType.prod vertexPairEncodedType edgeListStructuredEncodedType
  have hTarget : TMPolyTimeMap X vertexPairEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst vertexPairEncodedType edgeListStructuredEncodedType
  have hEdges : TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd vertexPairEncodedType edgeListStructuredEncodedType
  have hInit :
      TMPolyTimeMap X edgeScanInstructionEncodedType
        (fun p : X.Carrier => edgeScanInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp edgeScanInitInstruction_tm_polytime hTarget
    simpa [Function.comp, X] using hComp
  have hEdgeInstrs :
      TMPolyTimeMap X edgeScanInstructionListEncodedType
        (fun p : X.Carrier => p.2.map edgeScanEdgeInstruction) := by
    have hMap := TMPolyTimeMap.list_map edgeScanEdgeInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hEdges
    simpa [Function.comp, edgeListStructuredEncodedType, edgeScanInstructionListEncodedType, X]
      using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeScanInstructionEncodedType edgeScanInstructionListEncodedType)
        (fun p : X.Carrier => (edgeScanInitInstruction p.1, p.2.map edgeScanEdgeInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hEdgeInstrs
  have hOut :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons edgeScanInstructionEncodedType) hConsInput
  simpa [Function.comp, edgeScanInstructions, edgeScanInstructionListEncodedType, X] using hOut

theorem edgeScanRunnerStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod edgeScanAccEncodedType edgeScanInstructionEncodedType)
      edgeScanAccEncodedType
      edgeScanRunnerStep := by
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
        (fun p : X.Carrier => undirectedEdgeMatchesPairBool (p.1.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp undirectedEdgeMatchesPairBool_tm_polytime hMatchInput
    simpa [Function.comp, X] using hComp
  have hFoundOrInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (p.1.2, undirectedEdgeMatchesPairBool (p.1.1, p.2.2.2))) :=
    TMPolyTimeMap.prod_mk hFound hMatch
  have hFoundOr :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier =>
          graphBoolOrPair
            (p.1.2, undirectedEdgeMatchesPairBool (p.1.1, p.2.2.2))) := by
    have hComp := TMPolyTimeMap.comp graphBoolOrPair_tm_polytime hFoundOrInput
    simpa [Function.comp, X] using hComp
  have hScanOut :
      TMPolyTimeMap X edgeScanAccEncodedType
        (fun p : X.Carrier =>
          (p.1.1, graphBoolOrPair
            (p.1.2, undirectedEdgeMatchesPairBool (p.1.1, p.2.2.2)))) :=
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
              (p.2.1.1, graphBoolOrPair
                (p.2.1.2, undirectedEdgeMatchesPairBool (p.2.1.1, p.2.2.2.2)))
          | false => (p.2.2.2.1, false)) :=
    graphBoolProduct_dispatch_tm_polytime X edgeScanAccEncodedType
      (fFalse := fun p : X.Carrier => (p.2.2.1, false))
      (fTrue := fun p : X.Carrier =>
        (p.1.1, graphBoolOrPair
          (p.1.2, undirectedEdgeMatchesPairBool (p.1.1, p.2.2.2))))
      (hFalse := hInitOut) (hTrue := hScanOut)
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  ext p
  rcases p with ⟨acc, instr⟩
  rcases instr with ⟨tag, payload⟩
  cases tag <;> rfl

theorem edgeScanRunnerStep_inputSize_le
    (source : edgeScanInstructionListEncodedType.Carrier)
    (acc : edgeScanAccEncodedType.Carrier)
    (instr : edgeScanInstructionEncodedType.Carrier)
    (hAcc :
      edgeScanAccEncodedType.inputSize acc ≤
        edgeScanInstructionListEncodedType.inputSize source + 10)
    (hInstr :
      edgeScanInstructionEncodedType.inputSize instr ≤
        edgeScanInstructionListEncodedType.inputSize source) :
    edgeScanAccEncodedType.inputSize (edgeScanRunnerStep (acc, instr)) ≤
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
    calc
      edgeScanAccEncodedType.inputSize
          (edgeScanRunnerStep ((target, found), (false, (initPair, edge))))
          =
        edgeScanAccEncodedType.inputSize (initPair, false) := by
          rfl
      _ ≤ edgeScanInstructionEncodedType.inputSize (false, (initPair, edge)) + 10 := hLocal
      _ ≤ edgeScanInstructionListEncodedType.inputSize source + 10 :=
          Nat.add_le_add_right hInstr 10
  · have hLocal :
        edgeScanAccEncodedType.inputSize
            (target, graphBoolOrPair (found, undirectedEdgeMatchesPairBool (target, edge))) ≤
          edgeScanAccEncodedType.inputSize (target, found) := by
      simp [edgeScanAccEncodedType, vertexPairEncodedType, EncodedType.inputSize,
        EncodedType.prod, EncodedType.bool, EncodedType.nat]
    calc
      edgeScanAccEncodedType.inputSize
          (edgeScanRunnerStep ((target, found), (true, (initPair, edge))))
          =
        edgeScanAccEncodedType.inputSize
          (target, graphBoolOrPair (found, undirectedEdgeMatchesPairBool (target, edge))) := by
          rfl
      _ ≤ edgeScanAccEncodedType.inputSize (target, found) := hLocal
      _ ≤ edgeScanInstructionListEncodedType.inputSize source + 10 := hAcc

theorem edgeScanRunnerFold_tm_polytime :
    TMPolyTimeMap
      edgeScanInstructionListEncodedType
      edgeScanAccEncodedType
      (fun xs : edgeScanInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc x => edgeScanRunnerStep (acc, x)) edgeScanRunnerInit) := by
  rcases edgeScanRunnerStep_tm_polytime with ⟨hStep⟩
  let bound : Polynomial Nat := Polynomial.X + Polynomial.C 10
  refine
    TMPolyTimeMap.list_foldl_typed_bounded
      edgeScanInstructionEncodedType edgeScanAccEncodedType
      edgeScanRunnerStep edgeScanRunnerInit hStep bound ?_ ?_
  · intro xs
    change edgeScanAccEncodedType.inputSize edgeScanRunnerInit ≤
      (Polynomial.X + Polynomial.C 10).eval
        (edgeScanInstructionEncodedType.list.inputSize xs)
    have hInit : edgeScanAccEncodedType.inputSize edgeScanRunnerInit ≤ 10 := by
      simp [edgeScanRunnerInit, edgeScanDefaultPair, edgeScanAccEncodedType,
        vertexPairEncodedType, EncodedType.inputSize, EncodedType.prod,
        EncodedType.bool, EncodedType.nat]
    have hEval :
        (Polynomial.X + Polynomial.C 10).eval
            (edgeScanInstructionEncodedType.list.inputSize xs) =
          edgeScanInstructionEncodedType.list.inputSize xs + 10 := by
      simp [Polynomial.eval_add]
    rw [hEval]
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
      edgeScanRunnerStep_inputSize_le source acc instr hAcc' hInstr'

theorem edgeScanFromInstructions_tm_polytime :
    TMPolyTimeMap
      edgeScanInstructionListEncodedType
      EncodedType.bool
      edgeScanFromInstructions := by
  have hFold := edgeScanRunnerFold_tm_polytime
  have hFound := TMPolyTimeMap.snd vertexPairEncodedType EncodedType.bool
  have hComp := TMPolyTimeMap.comp hFound hFold
  simpa [Function.comp, edgeScanFromInstructions, edgeScanAccEncodedType] using hComp

theorem sourceHasUndirectedEdgeBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod vertexPairEncodedType edgeListStructuredEncodedType)
      EncodedType.bool
      sourceHasUndirectedEdgeBool := by
  have hComp :=
    TMPolyTimeMap.comp edgeScanFromInstructions_tm_polytime edgeScanInstructions_tm_polytime
  simpa [Function.comp, sourceHasUndirectedEdgeBool] using hComp

theorem sourceNonedgeBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod vertexPairEncodedType edgeListStructuredEncodedType)
      EncodedType.bool
      sourceNonedgeBool := by
  have hComp := TMPolyTimeMap.comp TMPolyTimeMap.bool_not sourceHasUndirectedEdgeBool_tm_polytime
  simpa [Function.comp, sourceNonedgeBool] using hComp

noncomputable def sourceHasUndirectedEdgeBoolTMBackedMap :
    TMBackedCostedMap
      (EncodedType.prod vertexPairEncodedType edgeListStructuredEncodedType)
      EncodedType.bool
      sourceHasUndirectedEdgeBool where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      (PolynomialSizeBound.const 1 (by
        intro p
        simp [EncodedType.inputSize, EncodedType.bool]))
  tm_polytime := sourceHasUndirectedEdgeBool_tm_polytime

noncomputable def sourceNonedgeBoolTMBackedMap :
    TMBackedCostedMap
      (EncodedType.prod vertexPairEncodedType edgeListStructuredEncodedType)
      EncodedType.bool
      sourceNonedgeBool where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      (PolynomialSizeBound.const 1 (by
        intro p
        simp [EncodedType.inputSize, EncodedType.bool]))
  tm_polytime := sourceNonedgeBool_tm_polytime

end Karp21
end ComplexityReduction
