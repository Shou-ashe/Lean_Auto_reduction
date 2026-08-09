/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.Authoring
import ComplexityReduction.AxiomGate
import ComplexityReduction.Domain.SetSystemMembershipPairs
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatRange
import ComplexityReduction.Legacy.IR.Domains.SetSystem
import ComplexityReduction.Presentation.SeeingSet
import ComplexityReduction.Presentation.SetSystem
import ComplexityReduction.Program.ContextListMap
import Mathlib.Tactic

/-!
Public Set Covering to Seeing Set gadget.

Set-family indices are the selectable vertices.  Universe elements become
heavy target vertices, and an edge from set index `j` to target `x` records
that the source set contains `x`.  Heavy target weights rule out the
length-zero reachability loophole without assuming source well-formedness.
-/

namespace ComplexityReduction
namespace Domain
namespace SetCoveringToSeeingSet

open Encoding
open Certificate
open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

abbrev source : PresentedProblem :=
  Presentation.SetSystem.setCoveringStructuredProblem

abbrev target : PresentedProblem :=
  Presentation.SeeingSet.presentedProblem

def setCount (input : SetCoveringInput) : Nat :=
  input.system.sets.length

def targetVertex (input : SetCoveringInput) (element : Nat) : Nat :=
  setCount input + element

/-- Ordered incidence edges from selectable set vertices to heavy target vertices. -/
def edges (input : SetCoveringInput) : List (Nat × Nat) :=
  (SetSystem.membershipPairs input.system).map fun pair =>
    (pair.2, targetVertex input pair.1)

/-- The directed graph of the Seeing Set instance. -/
def graph (input : SetCoveringInput) : GraphInput where
  vertices := setCount input + input.system.universeSize
  edges := edges input
  directed := true

/-- Unit weights on selectable set vertices and prohibitive weights on targets. -/
def weights (input : SetCoveringInput) : List Int :=
  List.replicate (setCount input) 1 ++
    List.replicate input.system.universeSize (Int.ofNat (input.k + 1))

/-- Every universe element is represented by one required target vertex. -/
def targets (input : SetCoveringInput) : List Nat :=
  (List.range input.system.universeSize).map (targetVertex input)

/-- Exact executable reduction. -/
def executable (input : source.Instance) : target.Instance where
  graph := graph input
  weights := weights input
  targets := targets input
  budget := Int.ofNat input.k

@[simp] theorem graph_vertices (input : SetCoveringInput) :
    (graph input).vertices = setCount input + input.system.universeSize :=
  rfl

@[simp] theorem graph_directed (input : SetCoveringInput) :
    (graph input).directed = true :=
  rfl

@[simp] theorem weights_length (input : SetCoveringInput) :
    (weights input).length = (graph input).vertices := by
  simp [weights, graph]

theorem weights_getD_setVertex (input : SetCoveringInput) {vertex : Nat}
    (bound : vertex < setCount input) :
    (weights input).getD vertex 0 = 1 := by
  rw [List.getD_eq_getElem (l := weights input) (d := 0) (n := vertex) (by
    simp [weights]
    omega)]
  simp [weights, bound]

theorem weights_getD_targetVertex (input : SetCoveringInput) {element : Nat}
    (bound : element < input.system.universeSize) :
    (weights input).getD (targetVertex input element) 0 = Int.ofNat (input.k + 1) := by
  rw [List.getD_eq_getElem (l := weights input) (d := 0)
    (n := targetVertex input element) (by
      simp [weights, targetVertex]
      omega)]
  simp [weights, targetVertex, setCount, bound]

theorem weights_getD_ge_one (input : SetCoveringInput) {vertex : Nat}
    (bound : vertex < (graph input).vertices) :
    (1 : Int) ≤ (weights input).getD vertex 0 := by
  by_cases setVertex : vertex < setCount input
  · rw [weights_getD_setVertex input setVertex]
  · have elementBound : vertex - setCount input < input.system.universeSize := by
      have lower : setCount input ≤ vertex := Nat.le_of_not_gt setVertex
      simp [graph] at bound
      omega
    have vertexEq : vertex = targetVertex input (vertex - setCount input) := by
      simp [targetVertex]
      omega
    rw [vertexEq, weights_getD_targetVertex input elementBound]
    simp

theorem targets_nodup (input : SetCoveringInput) :
    (targets input).Nodup := by
  unfold targets
  exact (List.nodup_range (n := input.system.universeSize)).map_on (by
    intro left _ right _ equality
    simpa [targetVertex] using equality)

theorem targets_withinBounds (input : SetCoveringInput) :
    VerticesWithinBounds (graph input) (targets input) := by
  intro vertex member
  rcases List.mem_map.mp member with ⟨element, elementMember, rfl⟩
  have elementBound : element < input.system.universeSize := by
    simpa using elementMember
  simp [graph, targetVertex]
  omega

theorem target_mem_targets (input : SetCoveringInput) {element : Nat}
    (bound : element < input.system.universeSize) :
    targetVertex input element ∈ targets input := by
  exact List.mem_map.mpr ⟨element, by simpa using bound, rfl⟩

theorem edge_of_indexedMembership (input : SetCoveringInput) {element index : Nat}
    (membership : SetSystem.IndexedMembership input.system element index) :
    HasDirectedEdge (graph input) index (targetVertex input element) := by
  change (index, targetVertex input element) ∈ edges input
  exact List.mem_map.mpr
    ⟨(element, index), SetSystem.mem_membershipPairs_iff.mpr membership, rfl⟩

theorem edge_source_lt_setCount (input : SetCoveringInput) {left right : Nat}
    (edge : HasDirectedEdge (graph input) left right) :
    left < setCount input := by
  rcases List.mem_map.mp edge with ⟨pair, pairMember, equality⟩
  have leftEq : pair.2 = left := congrArg Prod.fst equality
  have rightBound := SetSystem.mem_membershipPairsFrom_right_lt
    (start := 0) (sets := input.system.sets) pairMember
  simpa [SetSystem.membershipPairs, setCount, leftEq] using
    (show pair.2 < 0 + input.system.sets.length from rightBound)

theorem edge_target_ge_setCount (input : SetCoveringInput) {left right : Nat}
    (edge : HasDirectedEdge (graph input) left right) :
    setCount input ≤ right := by
  rcases List.mem_map.mp edge with ⟨pair, _pairMember, equality⟩
  cases equality
  simp [targetVertex]

theorem edge_inversion (input : SetCoveringInput) {left right : Nat}
    (edge : HasDirectedEdge (graph input) left right) :
    ∃ element index,
      SetSystem.IndexedMembership input.system element index ∧
        left = index ∧ right = targetVertex input element := by
  rcases List.mem_map.mp edge with ⟨pair, pairMember, equality⟩
  refine ⟨pair.1, pair.2, SetSystem.mem_membershipPairs_iff.mp pairMember, ?_⟩
  simpa using equality.symm

/-- Generated reachability has length zero or exactly one edge. -/
theorem reachable_eq_or_edge (input : SetCoveringInput) {left right : Nat}
    (reachable : Presentation.SeeingSet.DirectedReachable (graph input) left right) :
    left = right ∨ HasDirectedEdge (graph input) left right := by
  induction reachable with
  | refl vertex =>
      exact Or.inl rfl
  | @step sourceVertex next targetVertexValue firstEdge tailReachable inductionHypothesis =>
      rcases inductionHypothesis with tailRefl | tailEdge
      · cases tailRefl
        exact Or.inr firstEdge
      · have nextBelow := edge_source_lt_setCount input tailEdge
        have nextAbove := edge_target_ge_setCount input firstEdge
        omega

def selectedIndices (selected : List Nat) : List Nat :=
  selected.dedup

theorem selectedIndices_nodup (selected : List Nat) :
    (selectedIndices selected).Nodup :=
  List.nodup_dedup selected

theorem selectedIndices_length_le (selected : List Nat) :
    (selectedIndices selected).length ≤ selected.length := by
  exact List.Sublist.length_le (List.dedup_sublist selected)

private theorem selectedWeight_eq_length_of_setVertices
    (input : SetCoveringInput) (selected : List Nat)
    (bounds : ∀ vertex ∈ selected, vertex < setCount input) :
    Presentation.SeeingSet.selectedWeight (weights input) selected =
      Int.ofNat selected.length := by
  have mapped :
      selected.map (fun vertex => (weights input).getD vertex 0) =
        selected.map (fun _vertex => (1 : Int)) := by
    apply List.map_congr_left
    intro vertex member
    exact weights_getD_setVertex input (bounds vertex member)
  rw [Presentation.SeeingSet.selectedWeight, mapped]
  simp

private theorem selectedWeight_ge_length
    (input : SetCoveringInput) (selected : List Nat)
    (bounds : VerticesWithinBounds (graph input) selected) :
    Int.ofNat selected.length ≤
      Presentation.SeeingSet.selectedWeight (weights input) selected := by
  induction selected with
  | nil =>
      simp [Presentation.SeeingSet.selectedWeight]
  | cons vertex rest inductionHypothesis =>
      have vertexBound : vertex < (graph input).vertices := bounds vertex (by simp)
      have restBounds : VerticesWithinBounds (graph input) rest := by
        intro value member
        exact bounds value (by simp [member])
      have headWeight := weights_getD_ge_one input vertexBound
      have tailWeight := inductionHypothesis restBounds
      change Int.ofNat rest.length ≤
        (rest.map fun value => (weights input).getD value 0).sum at tailWeight
      simp only [Int.ofNat_eq_natCast] at tailWeight
      simp only [Presentation.SeeingSet.selectedWeight, List.map_cons, List.sum_cons,
        List.length_cons, Int.ofNat_eq_natCast, Nat.cast_succ]
      omega

private theorem selectedWeight_nonnegative
    (input : SetCoveringInput) (selected : List Nat)
    (bounds : VerticesWithinBounds (graph input) selected) :
    0 ≤ Presentation.SeeingSet.selectedWeight (weights input) selected := by
  have lower := selectedWeight_ge_length input selected bounds
  exact le_trans (by simp) lower

private theorem memberWeight_le_selectedWeight
    (input : SetCoveringInput) (selected : List Nat)
    (bounds : VerticesWithinBounds (graph input) selected)
    {vertex : Nat} (member : vertex ∈ selected) :
    (weights input).getD vertex 0 ≤
      Presentation.SeeingSet.selectedWeight (weights input) selected := by
  induction selected with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      have headBound : head < (graph input).vertices := bounds head (by simp)
      have tailBounds : VerticesWithinBounds (graph input) tail := by
        intro value valueMember
        exact bounds value (by simp [valueMember])
      have headNonnegative : 0 ≤ (weights input).getD head 0 :=
        le_trans (by simp) (weights_getD_ge_one input headBound)
      have tailNonnegative := selectedWeight_nonnegative input tail tailBounds
      change 0 ≤ (tail.map fun value => (weights input).getD value 0).sum at tailNonnegative
      simp only [Presentation.SeeingSet.selectedWeight, List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp member with rfl | tailMember
      · omega
      · have tailLe := inductionHypothesis tailBounds tailMember
        change (weights input).getD vertex 0 ≤
          (tail.map fun value => (weights input).getD value 0).sum at tailLe
        omega

private theorem target_not_selected
    (input : SetCoveringInput) (selected : List Nat)
    (bounds : VerticesWithinBounds (graph input) selected)
    (budget : Presentation.SeeingSet.selectedWeight (weights input) selected ≤ Int.ofNat input.k)
    {element : Nat} (elementBound : element < input.system.universeSize) :
    targetVertex input element ∉ selected := by
  intro member
  have individual := memberWeight_le_selectedWeight input selected bounds member
  rw [weights_getD_targetVertex input elementBound] at individual
  have impossible : input.k + 1 ≤ input.k :=
    Int.ofNat_le.mp (individual.trans budget)
  omega

private theorem sourceVertex_mem_selectedIndices
    {selected : List Nat} {vertex : Nat} (member : vertex ∈ selected) :
    vertex ∈ selectedIndices selected :=
  List.mem_dedup.mpr member

/-- Mathematical correctness of the public Seeing Set executable. -/
theorem executableCorrect :
    Agent.Hardness.Authoring.ExecutableSemanticProof source target executable := by
  intro input
  change SetCovering input ↔ Presentation.SeeingSet.IsYes (executable input)
  constructor
  · intro sourceYes
    rcases (SetSystem.setCovering_iff_existsSetCoveringIndex input).mp sourceYes with
      ⟨selected, selectedLength, selectedBounds, selectedCover⟩
    let canonical := selectedIndices selected
    have canonicalBounds : ∀ vertex ∈ canonical, vertex < setCount input := by
      intro vertex member
      exact selectedBounds vertex (List.mem_dedup.mp member)
    have canonicalGraphBounds : VerticesWithinBounds (graph input) canonical := by
      intro vertex member
      have := canonicalBounds vertex member
      simp [graph]
      omega
    have canonicalWeight :
        Presentation.SeeingSet.selectedWeight (weights input) canonical ≤ Int.ofNat input.k := by
      rw [selectedWeight_eq_length_of_setVertices input canonical canonicalBounds]
      have canonicalLength := selectedIndices_length_le selected
      exact Int.ofNat_le.mpr (canonicalLength.trans selectedLength)
    refine ⟨rfl, weights_length input, targets_nodup input,
      targets_withinBounds input, canonical, selectedIndices_nodup selected,
      canonicalGraphBounds, canonicalWeight, ?_⟩
    intro targetValue targetMember
    rcases List.mem_map.mp targetMember with ⟨element, elementMember, rfl⟩
    have elementBound : element < input.system.universeSize := by
      simpa using elementMember
    rcases selectedCover element elementBound with
      ⟨index, indexMember, incidence⟩
    refine ⟨index, sourceVertex_mem_selectedIndices indexMember, ?_⟩
    exact Presentation.SeeingSet.DirectedReachable.step
      (edge_of_indexedMembership input incidence)
      (Presentation.SeeingSet.DirectedReachable.refl _)
  · rintro ⟨_directed, _weightsLength, _targetNodup, _targetBounds,
      selected, _selectedNodup, selectedBounds, selectedBudget, selectedSees⟩
    have selectedLength : selected.length ≤ input.k := by
      have lengthLower := selectedWeight_ge_length input selected selectedBounds
      exact Int.ofNat_le.mp (lengthLower.trans selectedBudget)
    let sourceSelected := selected.filter fun vertex => decide (vertex < setCount input)
    have sourceLength : sourceSelected.length ≤ input.k := by
      have filterLength := List.length_filter_le
        (l := selected) (p := fun vertex => decide (vertex < setCount input))
      exact filterLength.trans selectedLength
    have sourceBounds : ∀ index ∈ sourceSelected, index < input.system.sets.length := by
      intro index member
      have checked := (List.mem_filter.mp member).2
      simpa [sourceSelected, setCount] using checked
    have sourceCover :
        ∀ element, element < input.system.universeSize →
          ∃ index ∈ sourceSelected, SetSystem.IndexedMembership input.system element index := by
      intro element elementBound
      have targetMember := target_mem_targets input elementBound
      rcases selectedSees (targetVertex input element) targetMember with
        ⟨start, startMember, reachable⟩
      rcases reachable_eq_or_edge input reachable with startEq | directEdge
      · have forbidden := target_not_selected input selected selectedBounds selectedBudget
          elementBound
        exact False.elim (forbidden (startEq ▸ startMember))
      · rcases edge_inversion input directEdge with
          ⟨edgeElement, index, incidence, startEq, targetEq⟩
        have indexBound := edge_source_lt_setCount input directEdge
        have elementEq : edgeElement = element := by
          simp [targetVertex] at targetEq
          omega
        subst edgeElement
        subst start
        refine ⟨index, ?_, incidence⟩
        exact List.mem_filter.mpr ⟨startMember, by simpa using indexBound⟩
    apply (SetSystem.setCovering_iff_existsSetCoveringIndex input).mpr
    exact ⟨sourceSelected, sourceLength, sourceBounds, sourceCover⟩

/-! ### Direct-TM realization of the exact executable -/

private theorem cleanMembershipPairsFrom_eq_legacy
    (start : Nat) (sets : List (List Nat)) :
    SetSystemMembershipPairs.membershipPairsFrom start sets =
      SetSystem.membershipPairsFrom start sets := by
  induction sets generalizing start with
  | nil => rfl
  | cons set sets inductionHypothesis =>
      simp [SetSystemMembershipPairs.membershipPairsFrom,
        SetSystem.membershipPairsFrom, inductionHypothesis]

private theorem natToIntOfNat_tmPolyTime :
    TMPolyTimeMap EncodedType.nat EncodedType.int (fun value : Nat => Int.ofNat value) :=
  ⟨{ tm := TM2Programs.prefixMapMachine Bool Bool false id
     inputAlphabet := Equiv.refl Bool
     outputAlphabet := Equiv.refl Bool
     time := 4 * Polynomial.X + 3
     outputsFun := by
      intro value
      change Turing.TM2OutputsInTime
        (TM2Programs.prefixMapMachine Bool Bool false id)
        (List.map (Equiv.refl Bool).invFun (EncodedType.nat.encode value))
        (some (List.map (Equiv.refl Bool).invFun
          (EncodedType.int.encode (Int.ofNat value))))
        ((4 * Polynomial.X + 3).eval (EncodedType.nat.encode value).length)
      have output :=
        TM2Programs.prefixMap_outputs Bool Bool false id (EncodedType.nat.encode value)
      convert output using 1
      · change List.map id (EncodedType.nat.encode value) =
          EncodedType.nat.encode value
        exact List.map_id (EncodedType.nat.encode value)
      · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
        rfl }⟩

abbrev pairEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.nat

abbrev pairListEncodedType : EncodedType :=
  EncodedType.list pairEncodedType

abbrev contextPairEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat pairEncodedType

def edgeAtContext (input : Nat × (Nat × Nat)) : Nat × Nat :=
  (input.2.2, input.1 + input.2.1)

private theorem edgeAtContext_tmPolyTime :
    TMPolyTimeMap contextPairEncodedType pairEncodedType edgeAtContext := by
  let X := contextPairEncodedType
  have context : TMPolyTimeMap X EncodedType.nat (fun input : X.Carrier => input.1) := by
    simpa [X, contextPairEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat pairEncodedType
  have pair : TMPolyTimeMap X pairEncodedType (fun input : X.Carrier => input.2) := by
    simpa [X, contextPairEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat pairEncodedType
  have element : TMPolyTimeMap X EncodedType.nat (fun input : X.Carrier => input.2.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst EncodedType.nat EncodedType.nat) pair
    simpa [Function.comp, X, pairEncodedType] using composed
  have index : TMPolyTimeMap X EncodedType.nat (fun input : X.Carrier => input.2.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd EncodedType.nat EncodedType.nat) pair
    simpa [Function.comp, X, pairEncodedType] using composed
  have addInput : TMPolyTimeMap X natAddInputEncodedType
      (fun input : X.Carrier => (input.1, input.2.1)) := by
    simpa [natAddInputEncodedType] using TMPolyTimeMap.prod_mk context element
  have shifted : TMPolyTimeMap X EncodedType.nat
      (fun input : Nat × (Nat × Nat) => input.1 + input.2.1) := by
    have composed := TMPolyTimeMap.comp natAdd_tm_polytime addInput
    simpa [Function.comp] using composed
  simpa [edgeAtContext, pairEncodedType] using TMPolyTimeMap.prod_mk index shifted

abbrev natContextEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.nat

def targetAtContext (input : Nat × Nat) : Nat :=
  input.1 + input.2

private theorem targetAtContext_tmPolyTime :
    TMPolyTimeMap natContextEncodedType EncodedType.nat targetAtContext := by
  simpa [targetAtContext, natContextEncodedType, natAddInputEncodedType] using
    natAdd_tm_polytime

def heavyWeightAtContext (input : Nat × Nat) : Int :=
  Int.ofNat (input.1 + 1)

private theorem heavyWeightAtContext_tmPolyTime :
    TMPolyTimeMap natContextEncodedType EncodedType.int heavyWeightAtContext := by
  let X := natContextEncodedType
  have budget : TMPolyTimeMap X EncodedType.nat (fun input : X.Carrier => input.1) := by
    simpa [X, natContextEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have successor : TMPolyTimeMap X EncodedType.nat
      (fun input : Nat × Nat => input.1 + 1) := by
    have composed := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime budget
    simpa [Function.comp, Nat.succ_eq_add_one] using composed
  have converted := TMPolyTimeMap.comp natToIntOfNat_tmPolyTime successor
  simpa [Function.comp, heavyWeightAtContext] using converted

def edgesExecutable (input : SetCoveringInput) : List (Nat × Nat) :=
  (Program.contextListMapExecutable
      (C := EncodedType.nat) (X := pairEncodedType)
      (setCount input, SetSystem.membershipPairs input.system)).map edgeAtContext

theorem edgesExecutable_eq_edges (input : SetCoveringInput) :
    edgesExecutable input = edges input := by
  unfold edgesExecutable edges
  rw [Program.contextListMapExecutable_eq_map]
  change List.map edgeAtContext
      (List.map (fun pair : Nat × Nat => (setCount input, pair))
        (SetSystem.membershipPairs input.system)) =
    List.map (fun pair => (pair.2, targetVertex input pair.1))
      (SetSystem.membershipPairs input.system)
  rw [List.map_map]
  rfl

def targetsExecutable (input : SetCoveringInput) : List Nat :=
  (Program.contextListMapExecutable
      (C := EncodedType.nat) (X := EncodedType.nat)
      (setCount input, List.range input.system.universeSize)).map targetAtContext

theorem targetsExecutable_eq_targets (input : SetCoveringInput) :
    targetsExecutable input = targets input := by
  unfold targetsExecutable targets
  rw [Program.contextListMapExecutable_eq_map]
  change List.map targetAtContext
      (List.map (fun element : Nat => (setCount input, element))
        (List.range input.system.universeSize)) =
    List.map (targetVertex input) (List.range input.system.universeSize)
  rw [List.map_map]
  rfl

def weightsExecutable (input : SetCoveringInput) : List Int :=
  List.replicate (setCount input) (1 : Int) ++
    ((Program.contextListMapExecutable
        (C := EncodedType.nat) (X := EncodedType.nat)
        (input.k, List.range input.system.universeSize)).map heavyWeightAtContext)

theorem weightsExecutable_eq_weights (input : SetCoveringInput) :
    weightsExecutable input = weights input := by
  unfold weightsExecutable weights
  rw [Program.contextListMapExecutable_eq_map]
  change List.replicate (setCount input) (1 : Int) ++
      List.map heavyWeightAtContext
        (List.map (fun element : Nat => (input.k, element))
          (List.range input.system.universeSize)) =
    List.replicate (setCount input) (1 : Int) ++
      List.replicate input.system.universeSize (Int.ofNat (input.k + 1))
  rw [List.map_map]
  simp [Function.comp_def, heavyWeightAtContext]

def graphTupleToGraph
    (payload : ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType.Carrier) :
    GraphInput where
  vertices := payload.1
  edges := payload.2.1
  directed := payload.2.2

private theorem graphTupleToGraph_encode
    (payload : ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType.Carrier) :
    ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType.encode
        (graphTupleToGraph payload) =
      ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType.encode payload := by
  rcases payload with ⟨vertices, edges, directed⟩
  rfl

private noncomputable def graphTupleToGraphTMBackedMap :
    TMBackedCostedMap
      ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType
      ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType
      graphTupleToGraph :=
  TMBackedCostedMap.ofEncodingEquiv
    ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType
    ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType
    graphTupleToGraph
    (Equiv.refl ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType.Symbol)
    (by
      intro payload
      change ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType.encode
          (graphTupleToGraph payload) =
        (ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType.encode
          payload).map id
      simp [graphTupleToGraph_encode])

def seeingTupleToInput
    (payload : Presentation.SeeingSet.tupleStructuredEncodedType.Carrier) :
    Presentation.SeeingSet.Input where
  graph := payload.1
  weights := payload.2.1
  targets := payload.2.2.1
  budget := payload.2.2.2

private theorem seeingTupleToInput_encode
    (payload : Presentation.SeeingSet.tupleStructuredEncodedType.Carrier) :
    Presentation.SeeingSet.structuredEncodedType.encode (seeingTupleToInput payload) =
      Presentation.SeeingSet.tupleStructuredEncodedType.encode payload := by
  rcases payload with ⟨graphValue, weightsValue, targetsValue, budgetValue⟩
  rfl

private noncomputable def seeingTupleToInputTMBackedMap :
    TMBackedCostedMap
      Presentation.SeeingSet.tupleStructuredEncodedType
      Presentation.SeeingSet.structuredEncodedType
      seeingTupleToInput :=
  TMBackedCostedMap.ofEncodingEquiv
    Presentation.SeeingSet.tupleStructuredEncodedType
    Presentation.SeeingSet.structuredEncodedType
    seeingTupleToInput
    (Equiv.refl Presentation.SeeingSet.tupleStructuredEncodedType.Symbol)
    (by
      intro payload
      change Presentation.SeeingSet.structuredEncodedType.encode
          (seeingTupleToInput payload) =
        (Presentation.SeeingSet.tupleStructuredEncodedType.encode payload).map id
      simp [seeingTupleToInput_encode])

/-- Direct-TM evidence for the exact public executable. -/
theorem executableDirectTM :
    Agent.Hardness.Authoring.ExecutableDirectTMEvidence source target executable := by
  let X := ComplexityReduction.Combinatorics.setCoveringStructuredEncodedType
  have sourceTuple : TMPolyTimeMap X
      ComplexityReduction.Combinatorics.setCoveringTupleStructuredEncodedType
      (fun input : SetCoveringInput => (input.system, input.k)) := by
    simpa [X, ComplexityReduction.Karp21.HittingSet.setCoveringInputToTuple] using
      ComplexityReduction.Karp21.HittingSet.setCoveringInputToTupleTMBackedMap.tm_polytime
  have system : TMPolyTimeMap X
      ComplexityReduction.Combinatorics.setSystemStructuredEncodedType
      (fun input : SetCoveringInput => input.system) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst
        ComplexityReduction.Combinatorics.setSystemStructuredEncodedType EncodedType.nat)
      sourceTuple
    simpa [Function.comp, X,
      ComplexityReduction.Combinatorics.setCoveringTupleStructuredEncodedType] using composed
  have budget : TMPolyTimeMap X EncodedType.nat
      (fun input : SetCoveringInput => input.k) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd
        ComplexityReduction.Combinatorics.setSystemStructuredEncodedType EncodedType.nat)
      sourceTuple
    simpa [Function.comp, X,
      ComplexityReduction.Combinatorics.setCoveringTupleStructuredEncodedType] using composed
  have systemTuple : TMPolyTimeMap X
      ComplexityReduction.Combinatorics.setSystemTupleStructuredEncodedType
      (fun input : SetCoveringInput =>
        (input.system.universeSize, input.system.sets)) := by
    have composed := TMPolyTimeMap.comp
      ComplexityReduction.Karp21.HittingSet.setSystemInputToTupleTMBackedMap.tm_polytime system
    simpa [Function.comp, ComplexityReduction.Karp21.HittingSet.setSystemInputToTuple, X] using
      composed
  have universeTM : TMPolyTimeMap X EncodedType.nat
      (fun input : SetCoveringInput => input.system.universeSize) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst EncodedType.nat
        ComplexityReduction.Combinatorics.setFamilyStructuredEncodedType)
      systemTuple
    simpa [Function.comp, X,
      ComplexityReduction.Combinatorics.setSystemTupleStructuredEncodedType] using composed
  have setsTM : TMPolyTimeMap X
      ComplexityReduction.Combinatorics.setFamilyStructuredEncodedType
      (fun input : SetCoveringInput => input.system.sets) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd EncodedType.nat
        ComplexityReduction.Combinatorics.setFamilyStructuredEncodedType)
      systemTuple
    simpa [Function.comp, X,
      ComplexityReduction.Combinatorics.setSystemTupleStructuredEncodedType] using composed
  have setCountTM : TMPolyTimeMap X EncodedType.nat setCount := by
    have composed := TMPolyTimeMap.comp
      (ComplexityReduction.Karp21.HittingSet.listLengthTMBackedMap
        ComplexityReduction.Combinatorics.setStructuredEncodedType).tm_polytime setsTM
    simpa [Function.comp, setCount, X] using composed
  have verticesInput : TMPolyTimeMap X natAddInputEncodedType
      (fun input : SetCoveringInput => (setCount input, input.system.universeSize)) := by
    simpa [natAddInputEncodedType] using TMPolyTimeMap.prod_mk setCountTM universeTM
  have vertices : TMPolyTimeMap X EncodedType.nat
      (fun input : SetCoveringInput => setCount input + input.system.universeSize) := by
    have composed := TMPolyTimeMap.comp natAdd_tm_polytime verticesInput
    simpa [Function.comp] using composed
  have pairsFromSystem : TMPolyTimeMap X pairListEncodedType
      (fun input : SetCoveringInput => SetSystem.membershipPairs input.system) := by
    have composed := TMPolyTimeMap.comp
      SetSystemMembershipPairs.fromSetSystem_tmPolyTime system
    convert composed using 1
    funext input
    simp [Function.comp, SetSystemMembershipPairs.fromSetSystem_eq_membershipPairsFrom,
      cleanMembershipPairsFrom_eq_legacy, SetSystem.membershipPairs]
  have pairContextInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat pairListEncodedType)
      (fun input : SetCoveringInput =>
        (setCount input, SetSystem.membershipPairs input.system)) :=
    TMPolyTimeMap.prod_mk setCountTM pairsFromSystem
  have attachedPairs : TMPolyTimeMap X (EncodedType.list contextPairEncodedType)
      (fun input : SetCoveringInput =>
        Program.contextListMapExecutable
          (setCount input, SetSystem.membershipPairs input.system)) := by
    have composed := TMPolyTimeMap.comp
      (Program.contextListMapExecutable_tmPolyTime EncodedType.nat pairEncodedType)
      pairContextInput
    simpa [Function.comp, contextPairEncodedType] using composed
  have edgeListExecutable : TMPolyTimeMap X pairListEncodedType edgesExecutable := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_map edgeAtContext_tmPolyTime) attachedPairs
    simpa [Function.comp, edgesExecutable] using composed
  have edgeList : TMPolyTimeMap X pairListEncodedType edges := by
    convert edgeListExecutable using 1
    funext input
    exact (edgesExecutable_eq_edges input).symm
  have trueFlag : TMPolyTimeMap X EncodedType.bool
      (fun _input : SetCoveringInput => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have graphPayload : TMPolyTimeMap X
      ComplexityReduction.Combinatorics.Graph.graphPayloadStructuredEncodedType
      (fun input : SetCoveringInput => (edges input, true)) := by
    simpa [ComplexityReduction.Combinatorics.Graph.graphPayloadStructuredEncodedType] using
      TMPolyTimeMap.prod_mk edgeList trueFlag
  have graphTuple : TMPolyTimeMap X
      ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType
      (fun input : SetCoveringInput =>
        (setCount input + input.system.universeSize, (edges input, true))) := by
    simpa [ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType] using
      TMPolyTimeMap.prod_mk vertices graphPayload
  have graphTM : TMPolyTimeMap X
      ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType graph := by
    have composed := TMPolyTimeMap.comp graphTupleToGraphTMBackedMap.tm_polytime graphTuple
    simpa [Function.comp, graphTupleToGraph, graph] using composed
  have setRange : TMPolyTimeMap X (EncodedType.list EncodedType.nat)
      (fun input : SetCoveringInput => List.range (setCount input)) := by
    have composed := TMPolyTimeMap.comp natRange_tm_polytime setCountTM
    simpa [Function.comp] using composed
  have setWeights : TMPolyTimeMap X (EncodedType.list EncodedType.int)
      (fun input : SetCoveringInput =>
        List.replicate (setCount input) (1 : Int)) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_const EncodedType.nat EncodedType.int (1 : Int)) setRange
    convert composed using 1
    funext input
    change List.replicate (setCount input) (1 : Int) =
      List.map (fun _value : Nat => (1 : Int)) (List.range (setCount input))
    simp only [List.map_const', List.length_range]
  have targetRange : TMPolyTimeMap X (EncodedType.list EncodedType.nat)
      (fun input : SetCoveringInput => List.range input.system.universeSize) := by
    have composed := TMPolyTimeMap.comp natRange_tm_polytime universeTM
    simpa [Function.comp] using composed
  have heavyContextInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
      (fun input : SetCoveringInput =>
        (input.k, List.range input.system.universeSize)) :=
    TMPolyTimeMap.prod_mk budget targetRange
  have attachedHeavy : TMPolyTimeMap X (EncodedType.list natContextEncodedType)
      (fun input : SetCoveringInput =>
        Program.contextListMapExecutable
          (C := EncodedType.nat) (X := EncodedType.nat)
          (input.k, List.range input.system.universeSize)) := by
    have composed := TMPolyTimeMap.comp
      (Program.contextListMapExecutable_tmPolyTime EncodedType.nat EncodedType.nat)
      heavyContextInput
    simpa [Function.comp, natContextEncodedType] using composed
  have heavyWeights : TMPolyTimeMap X (EncodedType.list EncodedType.int)
      (fun input : SetCoveringInput =>
        (Program.contextListMapExecutable
          (C := EncodedType.nat) (X := EncodedType.nat)
          (input.k, List.range input.system.universeSize)).map heavyWeightAtContext) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_map heavyWeightAtContext_tmPolyTime) attachedHeavy
    simpa [Function.comp] using composed
  have weightAppendInput : TMPolyTimeMap X
      (EncodedType.prod (EncodedType.list EncodedType.int)
        (EncodedType.list EncodedType.int))
      (fun input : SetCoveringInput =>
        (List.replicate (setCount input) (1 : Int),
          (Program.contextListMapExecutable
            (C := EncodedType.nat) (X := EncodedType.nat)
            (input.k, List.range input.system.universeSize)).map heavyWeightAtContext)) :=
    TMPolyTimeMap.prod_mk setWeights heavyWeights
  have weightListExecutable : TMPolyTimeMap X (EncodedType.list EncodedType.int)
      weightsExecutable := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append EncodedType.int) weightAppendInput
    simpa [Function.comp, weightsExecutable] using composed
  have weightList : TMPolyTimeMap X (EncodedType.list EncodedType.int) weights := by
    convert weightListExecutable using 1
    funext input
    exact (weightsExecutable_eq_weights input).symm
  have targetContextInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
      (fun input : SetCoveringInput =>
        (setCount input, List.range input.system.universeSize)) :=
    TMPolyTimeMap.prod_mk setCountTM targetRange
  have attachedTargets : TMPolyTimeMap X (EncodedType.list natContextEncodedType)
      (fun input : SetCoveringInput =>
        Program.contextListMapExecutable
          (setCount input, List.range input.system.universeSize)) := by
    have composed := TMPolyTimeMap.comp
      (Program.contextListMapExecutable_tmPolyTime EncodedType.nat EncodedType.nat)
      targetContextInput
    simpa [Function.comp, natContextEncodedType] using composed
  have targetListExecutable : TMPolyTimeMap X (EncodedType.list EncodedType.nat)
      targetsExecutable := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_map targetAtContext_tmPolyTime) attachedTargets
    simpa [Function.comp, targetsExecutable] using composed
  have targetList : TMPolyTimeMap X (EncodedType.list EncodedType.nat) targets := by
    convert targetListExecutable using 1
    funext input
    exact (targetsExecutable_eq_targets input).symm
  have integerBudget : TMPolyTimeMap X EncodedType.int
      (fun input : SetCoveringInput => Int.ofNat input.k) := by
    have composed := TMPolyTimeMap.comp natToIntOfNat_tmPolyTime budget
    simpa [Function.comp] using composed
  have targetBudget : TMPolyTimeMap X
      (EncodedType.prod (EncodedType.list EncodedType.nat) EncodedType.int)
      (fun input : SetCoveringInput => (targets input, Int.ofNat input.k)) :=
    TMPolyTimeMap.prod_mk targetList integerBudget
  have tailPayload : TMPolyTimeMap X
      (EncodedType.prod (EncodedType.list EncodedType.int)
        (EncodedType.prod (EncodedType.list EncodedType.nat) EncodedType.int))
      (fun input : SetCoveringInput =>
        (weights input, (targets input, Int.ofNat input.k))) :=
    TMPolyTimeMap.prod_mk weightList targetBudget
  have outputTuple : TMPolyTimeMap X Presentation.SeeingSet.tupleStructuredEncodedType
      (fun input : SetCoveringInput =>
        (graph input, (weights input, (targets input, Int.ofNat input.k)))) := by
    simpa [Presentation.SeeingSet.tupleStructuredEncodedType] using
      TMPolyTimeMap.prod_mk graphTM tailPayload
  have output := TMPolyTimeMap.comp seeingTupleToInputTMBackedMap.tm_polytime outputTuple
  simpa [Function.comp, executable, seeingTupleToInput, source, target,
    Presentation.SetSystem.setCoveringStructuredProblem,
    Presentation.SetSystem.setCoveringStructuredPresentation,
    Presentation.SeeingSet.presentedProblem,
    Presentation.SeeingSet.structuredPresentation, X] using output

/-- Discoverable single-gap authoring packet for the public production gadget. -/
@[complexity_reduction_ir_hardness_program_reduction_template]
def template : Agent.Hardness.Authoring.ProgramIndexedReductionTemplate
    .finalComposition source target executable executableDirectTM executableCorrect :=
  ⟨trivial⟩

end SetCoveringToSeeingSet
end Domain
end ComplexityReduction

assert_standard_axioms
  ComplexityReduction.Domain.SetCoveringToSeeingSet.executableDirectTM,
  ComplexityReduction.Domain.SetCoveringToSeeingSet.executableCorrect
