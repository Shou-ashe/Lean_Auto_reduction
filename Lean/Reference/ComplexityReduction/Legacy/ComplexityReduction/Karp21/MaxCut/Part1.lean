/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.VertexCover
import ComplexityReduction.Legacy.ComplexityReduction.Combinatorics.Graph.WeightedGraph
import Mathlib.Tactic

/-!
P15c arithmetic target: Partition to Max Cut.
-/

namespace ComplexityReduction
namespace Karp21
namespace MaxCut

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-! ### Binary-weighted Max-Cut carrier for arithmetic transports -/

/-- Weighted Max-Cut instance used for compact binary-numeric arithmetic transports. -/
structure WeightedMaxCutInput where
  graph : WeightedGraphInput
  threshold : Nat
  deriving Repr

/-- Tuple-shaped binary-numeric finite-alphabet encoding for weighted edges. -/
def weightedEdgeBinaryStructuredEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat
    (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)

/-- Binary-numeric finite-alphabet encoding for weighted edge lists. -/
def weightedEdgeListBinaryStructuredEncodedType : EncodedType :=
  EncodedType.list weightedEdgeBinaryStructuredEncodedType

/-- Binary-numeric payload encoding for weighted edge data and directedness. -/
def weightedGraphPayloadBinaryStructuredEncodedType : EncodedType :=
  EncodedType.prod weightedEdgeListBinaryStructuredEncodedType EncodedType.bool

/-- Tuple-shaped binary-numeric finite-alphabet encoding for weighted graph fields. -/
def weightedGraphBinaryStructuredEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat weightedGraphPayloadBinaryStructuredEncodedType

/-- Binary-numeric finite-alphabet encoding for weighted graphs. -/
def weightedGraphBinaryStructuredEncodedType' : EncodedType where
  Carrier := WeightedGraphInput
  Symbol := weightedGraphBinaryStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun g => weightedGraphBinaryStructuredEncodedType.encode
    (g.vertices, (g.edges, g.directed))

/-- Tuple-shaped binary-numeric finite-alphabet encoding for weighted Max Cut. -/
def weightedMaxCutTupleBinaryStructuredEncodedType : EncodedType :=
  EncodedType.prod weightedGraphBinaryStructuredEncodedType' EncodedType.binaryNat

/-- Binary-numeric finite-alphabet encoding for weighted Max Cut. -/
def weightedMaxCutBinaryStructuredEncodedType : EncodedType where
  Carrier := WeightedMaxCutInput
  Symbol := weightedMaxCutTupleBinaryStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => weightedMaxCutTupleBinaryStructuredEncodedType.encode
    (I.graph, I.threshold)

theorem weightedEdgeBinaryStructuredEncodedType_encode_injective :
    Function.Injective weightedEdgeBinaryStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    EncodedType.binaryNat_encode_injective
    (EncodedType.prod_encode_injective
      EncodedType.binaryNat_encode_injective
      EncodedType.binaryNat_encode_injective)

theorem weightedEdgeListBinaryStructuredEncodedType_encode_injective :
    Function.Injective weightedEdgeListBinaryStructuredEncodedType.encode :=
  EncodedType.list_encode_injective weightedEdgeBinaryStructuredEncodedType_encode_injective

theorem weightedGraphPayloadBinaryStructuredEncodedType_encode_injective :
    Function.Injective weightedGraphPayloadBinaryStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    weightedEdgeListBinaryStructuredEncodedType_encode_injective
    EncodedType.bool_encode_injective

theorem weightedGraphBinaryStructuredEncodedType_encode_injective :
    Function.Injective weightedGraphBinaryStructuredEncodedType'.encode := by
  intro g h henc
  have htuple :
      (g.vertices, (g.edges, g.directed)) =
        (h.vertices, (h.edges, h.directed)) :=
    (EncodedType.prod_encode_injective
      EncodedType.binaryNat_encode_injective
      weightedGraphPayloadBinaryStructuredEncodedType_encode_injective) (by
        simpa [weightedGraphBinaryStructuredEncodedType'] using henc)
  cases g
  cases h
  simp at htuple
  rcases htuple with ⟨rfl, rfl, rfl⟩
  rfl

theorem weightedMaxCutBinaryStructuredEncodedType_encode_injective :
    Function.Injective weightedMaxCutBinaryStructuredEncodedType.encode := by
  intro I J henc
  have htuple : (I.graph, I.threshold) = (J.graph, J.threshold) :=
    (EncodedType.prod_encode_injective
      weightedGraphBinaryStructuredEncodedType_encode_injective
      EncodedType.binaryNat_encode_injective) (by
        simpa [weightedMaxCutBinaryStructuredEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl⟩
  rfl

/-- Contribution of one weighted edge to a cut. -/
def weightedEdgeCutContribution (side : Nat → Bool) (e : Nat × Nat × Nat) : Nat :=
  if side e.1 ≠ side e.2.1 then e.2.2 else 0

/-- Weighted edge-list cut value. -/
def weightedEdgeListCutValue (edges : List (Nat × Nat × Nat)) (side : Nat → Bool) : Nat :=
  (edges.map (weightedEdgeCutContribution side)).sum

/-- Weighted graph cut value. -/
def WeightedCutSize (g : WeightedGraphInput) (side : Nat → Bool) : Nat :=
  weightedEdgeListCutValue g.edges side

/-- Semantic weighted Max-Cut predicate. -/
def WeightedMaxCut (I : WeightedMaxCutInput) : Prop :=
  ∃ side : Nat → Bool, I.threshold ≤ WeightedCutSize I.graph side

/-- Weighted Max Cut over the binary-numeric finite-alphabet encoding. -/
def weightedMaxCutBinaryStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := weightedMaxCutBinaryStructuredEncodedType
  isYes := WeightedMaxCut

/-- Partition witnesses enumerated as finite Boolean lists. -/
def satisfyingPartitions (I : PartitionInput) : List (List Bool) := by
  classical
  exact (Partition.boolLists I.weights.length).filter fun selected =>
    decide (selectedPartitionWeight I selected = unselectedPartitionWeight I selected)

theorem mem_satisfyingPartitions_iff (I : PartitionInput) (selected : List Bool) :
    selected ∈ satisfyingPartitions I ↔
      selected ∈ Partition.boolLists I.weights.length ∧
        selectedPartitionWeight I selected = unselectedPartitionWeight I selected := by
  classical
  simp [satisfyingPartitions]

theorem partition_iff_satisfyingPartitions_pos (I : PartitionInput) :
    Combinatorics.Partition I ↔ 0 < (satisfyingPartitions I).length := by
  constructor
  · rintro ⟨selected, hLen, hEq⟩
    have hMem : selected ∈ satisfyingPartitions I :=
      (mem_satisfyingPartitions_iff I selected).2
        ⟨Partition.mem_boolLists_of_length hLen, hEq⟩
    exact List.length_pos_of_mem hMem
  · intro hPos
    cases hList : satisfyingPartitions I with
    | nil =>
        simp [hList] at hPos
    | cons selected rest =>
        have hMem : selected ∈ satisfyingPartitions I := by
          simp [hList]
        rcases (mem_satisfyingPartitions_iff I selected).1 hMem with ⟨hBool, hEq⟩
        exact ⟨selected, Partition.mem_boolLists_length hBool, hEq⟩

/-- `m` parallel unit edges between two vertices. -/
def parallelEdges (m : Nat) : List (Nat × Nat) :=
  List.replicate m (0, 1)

/-- Unit Max-Cut family that is satisfiable exactly when at least one edge exists. -/
def nonemptyMaxCutInput (m : Nat) : MaxCutInput :=
  { graph := { vertices := 2, edges := parallelEdges m, directed := false }
    threshold := 1 }

theorem nonemptyMaxCutInput_correct (m : Nat) :
    MaxCut (nonemptyMaxCutInput m) ↔ 0 < m := by
  constructor
  · rintro ⟨side, hCut⟩
    cases m with
    | zero =>
        simp [nonemptyMaxCutInput, parallelEdges, CutSize] at hCut
    | succ m =>
        omega
  · intro h
    cases m with
    | zero =>
        omega
    | succ m =>
        refine ⟨(fun v => if v = 0 then true else false), ?_⟩
        simp [nonemptyMaxCutInput, parallelEdges, CutSize]

/-- P15c syntax map from Partition to unit Max Cut. -/
def map (I : PartitionInput) : MaxCutInput :=
  nonemptyMaxCutInput (satisfyingPartitions I).length

theorem map_correct (I : PartitionInput) :
    partitionDecisionProblem.isYes I ↔ MaxCut (map I) := by
  change Combinatorics.Partition I ↔ MaxCut (map I)
  rw [partition_iff_satisfyingPartitions_pos]
  exact (nonemptyMaxCutInput_correct (satisfyingPartitions I).length).symm

/-! ### Textbook-style complete-graph cut route -/

/-- Local edge-list cut counter, matching `Graph.CutSize` on the edge field. -/
def cutCount (edges : List (Nat × Nat)) (side : Nat → Bool) : Nat :=
  (edges.filter (fun e => decide (side e.1 ≠ side e.2))).length

theorem cutCount_append (xs ys : List (Nat × Nat)) (side : Nat → Bool) :
    cutCount (xs ++ ys) side = cutCount xs side + cutCount ys side := by
  simp [cutCount, List.filter_append]

theorem cutCount_replicate (m : Nat) (edge : Nat × Nat) (side : Nat → Bool) :
    cutCount (List.replicate m edge) side =
      if side edge.1 ≠ side edge.2 then m else 0 := by
  by_cases h : side edge.1 ≠ side edge.2 <;> simp [cutCount, h]

/-- Weight on the `true` side of a cut, starting at vertex index `i`. -/
def selectedSideWeightFrom (side : Nat → Bool) : Nat → List Nat → Nat
  | _, [] => 0
  | i, w :: ws => (if side i then w else 0) + selectedSideWeightFrom side (i + 1) ws

/-- Weight on the `false` side of a cut, starting at vertex index `i`. -/
def unselectedSideWeightFrom (side : Nat → Bool) : Nat → List Nat → Nat
  | _, [] => 0
  | i, w :: ws => (if side i then 0 else w) + unselectedSideWeightFrom side (i + 1) ws

theorem selected_add_unselectedSideWeightFrom (side : Nat → Bool) (i : Nat)
    (weights : List Nat) :
    selectedSideWeightFrom side i weights + unselectedSideWeightFrom side i weights =
      weights.sum := by
  induction weights generalizing i with
  | nil =>
      simp [selectedSideWeightFrom, unselectedSideWeightFrom]
  | cons w ws ih =>
      cases h : side i <;>
        simp [selectedSideWeightFrom, unselectedSideWeightFrom, h, ih, Nat.add_assoc,
          Nat.add_left_comm]

/-- Edges from one item vertex to every later item vertex, with scaled unit multiplicity. -/
def textbookEdgesFrom (i w : Nat) : Nat → List Nat → List (Nat × Nat)
  | _, [] => []
  | j, v :: vs => List.replicate (4 * w * v) (i, j) ++ textbookEdgesFrom i w (j + 1) vs

/-- Complete item graph, represented with repeated unit edges. -/
def textbookEdgesFromList : Nat → List Nat → List (Nat × Nat)
  | _, [] => []
  | i, w :: ws => textbookEdgesFrom i w (i + 1) ws ++ textbookEdgesFromList (i + 1) ws

def textbookEdges (weights : List Nat) : List (Nat × Nat) :=
  textbookEdgesFromList 0 weights

theorem cutCount_textbookEdgesFrom (side : Nat → Bool) (i w j : Nat)
    (weights : List Nat) :
    cutCount (textbookEdgesFrom i w j weights) side =
      if side i then
        4 * w * unselectedSideWeightFrom side j weights
      else
        4 * w * selectedSideWeightFrom side j weights := by
  induction weights generalizing j with
  | nil =>
      simp [textbookEdgesFrom, cutCount, selectedSideWeightFrom, unselectedSideWeightFrom]
  | cons v vs ih =>
      simp [textbookEdgesFrom, cutCount_append, cutCount_replicate, ih,
        selectedSideWeightFrom, unselectedSideWeightFrom]
      cases side i <;> cases side j <;> simp [Nat.mul_add]

theorem cutCount_textbookEdgesFromList (side : Nat → Bool) (i : Nat)
    (weights : List Nat) :
    cutCount (textbookEdgesFromList i weights) side =
      4 * selectedSideWeightFrom side i weights * unselectedSideWeightFrom side i weights := by
  induction weights generalizing i with
  | nil =>
      simp [textbookEdgesFromList, cutCount, selectedSideWeightFrom, unselectedSideWeightFrom]
  | cons w ws ih =>
      simp [textbookEdgesFromList, cutCount_append, cutCount_textbookEdgesFrom, ih,
        selectedSideWeightFrom, unselectedSideWeightFrom]
      cases side i <;> simp [Nat.mul_add]
      · ring
      · ring

/-- Read a Boolean side assignment from a finite selected-list witness. -/
def sideFromBits (bits : List Bool) (i : Nat) : Bool :=
  match bits.drop i with
  | [] => false
  | b :: _ => b

theorem sideFromBits_cons_succ (b : Bool) (bits : List Bool) (i : Nat) :
    sideFromBits (b :: bits) (i + 1) = sideFromBits bits i := by
  simp [sideFromBits]

theorem selectedSideWeightFrom_sideFromBits_shift (b : Bool) (bits : List Bool)
    (weights : List Nat) (i : Nat) :
    selectedSideWeightFrom (sideFromBits (b :: bits)) (i + 1) weights =
      selectedSideWeightFrom (sideFromBits bits) i weights := by
  induction weights generalizing i with
  | nil =>
      simp [selectedSideWeightFrom]
  | cons w ws ih =>
      simp [selectedSideWeightFrom, sideFromBits_cons_succ, ih]

theorem unselectedSideWeightFrom_sideFromBits_shift (b : Bool) (bits : List Bool)
    (weights : List Nat) (i : Nat) :
    unselectedSideWeightFrom (sideFromBits (b :: bits)) (i + 1) weights =
      unselectedSideWeightFrom (sideFromBits bits) i weights := by
  induction weights generalizing i with
  | nil =>
      simp [unselectedSideWeightFrom]
  | cons w ws ih =>
      simp [unselectedSideWeightFrom, sideFromBits_cons_succ, ih]

theorem selectedSideWeightFrom_sideFromBits {weights : List Nat} {bits : List Bool}
    (hLen : bits.length = weights.length) :
    selectedSideWeightFrom (sideFromBits bits) 0 weights =
      selectedPartitionWeight { weights := weights } bits := by
  induction weights generalizing bits with
  | nil =>
      have hNil : bits = [] := by
        exact List.eq_nil_of_length_eq_zero hLen
      simp [hNil, selectedSideWeightFrom, selectedPartitionWeight]
  | cons w ws ih =>
      cases bits with
      | nil =>
          simp at hLen
      | cons b bs =>
          have hTail : bs.length = ws.length := by simpa using hLen
          cases b <;>
            simp [selectedSideWeightFrom, selectedPartitionWeight, sideFromBits,
              selectedSideWeightFrom_sideFromBits_shift, ih hTail]

theorem unselectedSideWeightFrom_sideFromBits {weights : List Nat} {bits : List Bool}
    (hLen : bits.length = weights.length) :
    unselectedSideWeightFrom (sideFromBits bits) 0 weights =
      unselectedPartitionWeight { weights := weights } bits := by
  induction weights generalizing bits with
  | nil =>
      have hNil : bits = [] := by
        exact List.eq_nil_of_length_eq_zero hLen
      simp [hNil, unselectedSideWeightFrom, unselectedPartitionWeight]
  | cons w ws ih =>
      cases bits with
      | nil =>
          simp at hLen
      | cons b bs =>
          have hTail : bs.length = ws.length := by simpa using hLen
          cases b <;>
            simp [unselectedSideWeightFrom, unselectedPartitionWeight, sideFromBits,
              unselectedSideWeightFrom_sideFromBits_shift, ih hTail]

/-- Finite selected-list induced by a Max-Cut side assignment. -/
def sideBitsFrom (side : Nat → Bool) : Nat → Nat → List Bool
  | _, 0 => []
  | i, n + 1 => side i :: sideBitsFrom side (i + 1) n

theorem length_sideBitsFrom (side : Nat → Bool) (i n : Nat) :
    (sideBitsFrom side i n).length = n := by
  induction n generalizing i with
  | zero =>
      simp [sideBitsFrom]
  | succ n ih =>
      simp [sideBitsFrom, ih]

theorem selectedPartitionWeight_sideBitsFrom (side : Nat → Bool) (i : Nat)
    (weights : List Nat) :
    selectedPartitionWeight { weights := weights } (sideBitsFrom side i weights.length) =
      selectedSideWeightFrom side i weights := by
  induction weights generalizing i with
  | nil =>
      simp [selectedPartitionWeight, sideBitsFrom, selectedSideWeightFrom]
  | cons w ws ih =>
      cases h : side i
      · simp [selectedPartitionWeight, sideBitsFrom, selectedSideWeightFrom, h]
        simpa [selectedPartitionWeight] using ih (i + 1)
      · simp [selectedPartitionWeight, sideBitsFrom, selectedSideWeightFrom, h]
        simpa [selectedPartitionWeight] using ih (i + 1)

theorem unselectedPartitionWeight_sideBitsFrom (side : Nat → Bool) (i : Nat)
    (weights : List Nat) :
    unselectedPartitionWeight { weights := weights } (sideBitsFrom side i weights.length) =
      unselectedSideWeightFrom side i weights := by
  induction weights generalizing i with
  | nil =>
      simp [unselectedPartitionWeight, sideBitsFrom, unselectedSideWeightFrom]
  | cons w ws ih =>
      cases h : side i
      · simp [unselectedPartitionWeight, sideBitsFrom, unselectedSideWeightFrom, h]
        simpa [unselectedPartitionWeight] using ih (i + 1)
      · simp [unselectedPartitionWeight, sideBitsFrom, unselectedSideWeightFrom, h]
        simpa [unselectedPartitionWeight] using ih (i + 1)

theorem eq_of_square_sum_le_four_mul {x y : Nat}
    (h : (x + y) * (x + y) ≤ 4 * x * y) :
    x = y := by
  have hInt : ((x + y) * (x + y) : Int) ≤ (4 * x * y : Int) := by
    exact_mod_cast h
  have hSqNonneg : 0 ≤ ((x : Int) - (y : Int)) ^ 2 := sq_nonneg _
  have hSqLe : ((x : Int) - (y : Int)) ^ 2 ≤ 0 := by
    nlinarith
  have hSubZero : (x : Int) - (y : Int) = 0 := by
    nlinarith
  omega

/-- P15o syntax-only Max-Cut map from Partition. -/
def textbookMap (I : PartitionInput) : MaxCutInput :=
  { graph := { vertices := I.weights.length, edges := textbookEdges I.weights, directed := false }
    threshold := I.weights.sum * I.weights.sum }

theorem cutSize_textbookMap (I : PartitionInput) (side : Nat → Bool) :
    CutSize (textbookMap I).graph side =
      4 * selectedSideWeightFrom side 0 I.weights *
        unselectedSideWeightFrom side 0 I.weights := by
  change cutCount (textbookEdges I.weights) side =
    4 * selectedSideWeightFrom side 0 I.weights *
      unselectedSideWeightFrom side 0 I.weights
  simp [textbookEdges, cutCount_textbookEdgesFromList]

theorem textbookMap_correct (I : PartitionInput) :
    partitionDecisionProblem.isYes I ↔ MaxCut (textbookMap I) := by
  change Combinatorics.Partition I ↔ MaxCut (textbookMap I)
  constructor
  · rintro ⟨selected, hLen, hEq⟩
    let side := sideFromBits selected
    refine ⟨side, ?_⟩
    rw [cutSize_textbookMap]
    have hSel :=
      selectedSideWeightFrom_sideFromBits (weights := I.weights) (bits := selected) hLen
    have hUns :=
      unselectedSideWeightFrom_sideFromBits (weights := I.weights) (bits := selected) hLen
    have hSideEq :
        selectedSideWeightFrom side 0 I.weights =
          unselectedSideWeightFrom side 0 I.weights := by
      dsimp [side]
      rw [hSel, hUns]
      exact hEq
    have hTotal :=
      selected_add_unselectedSideWeightFrom side 0 I.weights
    simp [textbookMap]
    nlinarith
  · rintro ⟨side, hCut⟩
    let selected := sideBitsFrom side 0 I.weights.length
    refine ⟨selected, by simp [selected, length_sideBitsFrom], ?_⟩
    have hCut' :
        I.weights.sum * I.weights.sum ≤
          4 * selectedSideWeightFrom side 0 I.weights *
            unselectedSideWeightFrom side 0 I.weights := by
      rw [cutSize_textbookMap I side] at hCut
      simpa [textbookMap] using hCut
    have hTotal :=
      selected_add_unselectedSideWeightFrom side 0 I.weights
    have hProduct :
        (selectedSideWeightFrom side 0 I.weights +
            unselectedSideWeightFrom side 0 I.weights) *
          (selectedSideWeightFrom side 0 I.weights +
            unselectedSideWeightFrom side 0 I.weights) ≤
          4 * selectedSideWeightFrom side 0 I.weights *
            unselectedSideWeightFrom side 0 I.weights := by
      rwa [hTotal]
    have hEqSide :=
      eq_of_square_sum_le_four_mul hProduct
    rw [selectedPartitionWeight_sideBitsFrom, unselectedPartitionWeight_sideBitsFrom]
    exact hEqSide

/-! ### Binary-weighted textbook cut route -/

/-- Weighted edges from one item vertex to every later item vertex. -/
def weightedTextbookEdgesFrom (i w : Nat) : Nat → List Nat → List (Nat × Nat × Nat)
  | _, [] => []
  | j, v :: vs => (i, j, 4 * w * v) :: weightedTextbookEdgesFrom i w (j + 1) vs

/-- Complete weighted item graph. -/
def weightedTextbookEdgesFromList : Nat → List Nat → List (Nat × Nat × Nat)
  | _, [] => []
  | i, w :: ws => weightedTextbookEdgesFrom i w (i + 1) ws ++
      weightedTextbookEdgesFromList (i + 1) ws

def weightedTextbookEdges (weights : List Nat) : List (Nat × Nat × Nat) :=
  weightedTextbookEdgesFromList 0 weights

def weightedTextbookGraph (weights : List Nat) : WeightedGraphInput where
  vertices := weights.length
  edges := weightedTextbookEdges weights
  directed := false

theorem weightedCutSize_append (xs ys : List (Nat × Nat × Nat)) (side : Nat → Bool) :
    weightedEdgeListCutValue (xs ++ ys) side =
      weightedEdgeListCutValue xs side + weightedEdgeListCutValue ys side := by
  simp [weightedEdgeListCutValue]

theorem weightedCutSize_textbookEdgesFrom (side : Nat → Bool) (i w j : Nat)
    (weights : List Nat) :
    weightedEdgeListCutValue (weightedTextbookEdgesFrom i w j weights) side =
      if side i then
        4 * w * unselectedSideWeightFrom side j weights
      else
        4 * w * selectedSideWeightFrom side j weights := by
  induction weights generalizing j with
  | nil =>
      simp [weightedTextbookEdgesFrom, weightedEdgeListCutValue, selectedSideWeightFrom,
        unselectedSideWeightFrom]
  | cons v vs ih =>
      rw [show
        weightedEdgeListCutValue (weightedTextbookEdgesFrom i w j (v :: vs)) side =
          weightedEdgeCutContribution side (i, j, 4 * w * v) +
            weightedEdgeListCutValue (weightedTextbookEdgesFrom i w (j + 1) vs) side by
          simp [weightedTextbookEdgesFrom, weightedEdgeListCutValue]]
      rw [ih (j + 1)]
      cases hi : side i <;> cases hj : side j <;>
        simp [hi, hj, weightedEdgeCutContribution, selectedSideWeightFrom,
          unselectedSideWeightFrom, Nat.mul_add]

theorem weightedCutSize_textbookEdgesFromList (side : Nat → Bool) (i : Nat)
    (weights : List Nat) :
    weightedEdgeListCutValue (weightedTextbookEdgesFromList i weights) side =
      4 * selectedSideWeightFrom side i weights * unselectedSideWeightFrom side i weights := by
  induction weights generalizing i with
  | nil =>
      simp [weightedTextbookEdgesFromList, weightedEdgeListCutValue, selectedSideWeightFrom,
        unselectedSideWeightFrom]
  | cons w ws ih =>
      simp [weightedTextbookEdgesFromList, weightedCutSize_append,
        weightedCutSize_textbookEdgesFrom, ih, selectedSideWeightFrom, unselectedSideWeightFrom]
      cases side i <;> simp [Nat.mul_add]
      · ring
      · ring

/-- Binary-weighted P15o syntax map from Partition to weighted Max Cut. -/
def weightedTextbookMap (I : PartitionInput) : WeightedMaxCutInput :=
  { graph := weightedTextbookGraph I.weights
    threshold := I.weights.sum * I.weights.sum }

theorem weightedCutSize_textbookMap (I : PartitionInput) (side : Nat → Bool) :
    WeightedCutSize (weightedTextbookMap I).graph side =
      4 * selectedSideWeightFrom side 0 I.weights *
        unselectedSideWeightFrom side 0 I.weights := by
  change weightedEdgeListCutValue (weightedTextbookEdges I.weights) side =
    4 * selectedSideWeightFrom side 0 I.weights *
      unselectedSideWeightFrom side 0 I.weights
  simp [weightedTextbookEdges, weightedCutSize_textbookEdgesFromList]

theorem weightedTextbookMap_correct (I : PartitionInput) :
    partitionDecisionProblem.isYes I ↔ WeightedMaxCut (weightedTextbookMap I) := by
  change Combinatorics.Partition I ↔ WeightedMaxCut (weightedTextbookMap I)
  constructor
  · rintro ⟨selected, hLen, hEq⟩
    let side := sideFromBits selected
    refine ⟨side, ?_⟩
    rw [weightedCutSize_textbookMap]
    have hSel :=
      selectedSideWeightFrom_sideFromBits (weights := I.weights) (bits := selected) hLen
    have hUns :=
      unselectedSideWeightFrom_sideFromBits (weights := I.weights) (bits := selected) hLen
    have hSideEq :
        selectedSideWeightFrom side 0 I.weights =
          unselectedSideWeightFrom side 0 I.weights := by
      dsimp [side]
      rw [hSel, hUns]
      exact hEq
    have hTotal :=
      selected_add_unselectedSideWeightFrom side 0 I.weights
    have hGoal :
        I.weights.sum * I.weights.sum ≤
          4 * selectedSideWeightFrom side 0 I.weights *
            unselectedSideWeightFrom side 0 I.weights := by
      rw [← hTotal, hSideEq]
      nlinarith
    simpa [weightedTextbookMap] using hGoal
  · rintro ⟨side, hCut⟩
    let selected := sideBitsFrom side 0 I.weights.length
    refine ⟨selected, by simp [selected, length_sideBitsFrom], ?_⟩
    have hCut' :
        I.weights.sum * I.weights.sum ≤
          4 * selectedSideWeightFrom side 0 I.weights *
            unselectedSideWeightFrom side 0 I.weights := by
      rw [weightedCutSize_textbookMap I side] at hCut
      simpa [weightedTextbookMap] using hCut
    have hTotal :=
      selected_add_unselectedSideWeightFrom side 0 I.weights
    have hProduct :
        (selectedSideWeightFrom side 0 I.weights +
            unselectedSideWeightFrom side 0 I.weights) *
          (selectedSideWeightFrom side 0 I.weights +
            unselectedSideWeightFrom side 0 I.weights) ≤
          4 * selectedSideWeightFrom side 0 I.weights *
            unselectedSideWeightFrom side 0 I.weights := by
      rwa [hTotal]
    have hEqSide :=
      eq_of_square_sum_le_four_mul hProduct
    rw [selectedPartitionWeight_sideBitsFrom, unselectedPartitionWeight_sideBitsFrom]
    exact hEqSide

/-! ### Binary-weighted finite-alphabet size bound for the textbook route -/

theorem weightedEdgeBinaryStructured_inputSize_eq (e : Nat × Nat × Nat) :
    weightedEdgeBinaryStructuredEncodedType.inputSize e =
      EncodedType.binaryNat.inputSize e.1 + 1 +
        (EncodedType.binaryNat.inputSize e.2.1 + 1 +
          EncodedType.binaryNat.inputSize e.2.2) := by
  change (EncodedType.prod EncodedType.binaryNat
    (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)).inputSize e =
      EncodedType.binaryNat.inputSize e.1 + 1 +
        (EncodedType.binaryNat.inputSize e.2.1 + 1 +
          EncodedType.binaryNat.inputSize e.2.2)
  simp

theorem weightedGraphBinaryStructured_inputSize_eq (g : WeightedGraphInput) :
    weightedGraphBinaryStructuredEncodedType'.inputSize g =
      EncodedType.binaryNat.inputSize g.vertices + 1 +
        (weightedEdgeListBinaryStructuredEncodedType.inputSize g.edges + 1 + 1) := by
  change weightedGraphBinaryStructuredEncodedType.inputSize
      (g.vertices, (g.edges, g.directed)) =
    EncodedType.binaryNat.inputSize g.vertices + 1 +
      (weightedEdgeListBinaryStructuredEncodedType.inputSize g.edges + 1 + 1)
  simp [weightedGraphBinaryStructuredEncodedType, weightedGraphPayloadBinaryStructuredEncodedType]

theorem weightedMaxCutBinaryStructured_inputSize_eq (I : WeightedMaxCutInput) :
    weightedMaxCutBinaryStructuredEncodedType.inputSize I =
      weightedGraphBinaryStructuredEncodedType'.inputSize I.graph + 1 +
        EncodedType.binaryNat.inputSize I.threshold := by
  change weightedMaxCutTupleBinaryStructuredEncodedType.inputSize (I.graph, I.threshold) =
    weightedGraphBinaryStructuredEncodedType'.inputSize I.graph + 1 +
      EncodedType.binaryNat.inputSize I.threshold
  simp [weightedMaxCutTupleBinaryStructuredEncodedType]

theorem partitionWeights_length_le_binaryStructured_inputSize (I : PartitionInput) :
    I.weights.length ≤ partitionBinaryStructuredEncodedType.inputSize I := by
  have hList := Knapsack.encodedList_length_le_inputSize EncodedType.binaryNat I.weights
  simpa [partitionBinaryStructuredEncodedType, partitionWeightsBinaryStructuredEncodedType]
    using hList

theorem partitionWeight_binaryNat_inputSize_le_source {I : PartitionInput}
    {w : Nat} (hw : w ∈ I.weights) :
    EncodedType.binaryNat.inputSize w ≤ partitionBinaryStructuredEncodedType.inputSize I := by
  have hElement := Knapsack.encodedList_element_inputSize_le EncodedType.binaryNat hw
  simpa [partitionBinaryStructuredEncodedType, partitionWeightsBinaryStructuredEncodedType]
    using hElement

theorem partitionWeight_lt_two_pow_sourceSucc {I : PartitionInput}
    {w : Nat} (hw : w ∈ I.weights) :
    w < 2 ^ (partitionBinaryStructuredEncodedType.inputSize I + 1) := by
  have hSize :
      EncodedType.binaryNat.inputSize w ≤
        partitionBinaryStructuredEncodedType.inputSize I + 1 := by
    have hSource := partitionWeight_binaryNat_inputSize_le_source hw
    omega
  exact (Knapsack.binaryNat_lt_two_pow_inputSize w).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) hSize)

theorem partitionWeights_sum_le_two_pow_two_mul_sourceSucc (I : PartitionInput) :
    I.weights.sum ≤
      2 ^ (2 * (partitionBinaryStructuredEncodedType.inputSize I + 1)) := by
  let T := partitionBinaryStructuredEncodedType.inputSize I + 1
  have hEach : ∀ w ∈ I.weights, w ≤ 2 ^ T := by
    intro w hw
    exact Nat.le_of_lt (by simpa [T] using partitionWeight_lt_two_pow_sourceSucc hw)
  have hSum := Partition.natList_sum_le_length_mul_bound hEach
  have hLen : I.weights.length ≤ T := by
    have hItems := partitionWeights_length_le_binaryStructured_inputSize I
    omega
  calc
    I.weights.sum ≤ I.weights.length * 2 ^ T := hSum
    _ ≤ T * 2 ^ T := Nat.mul_le_mul_right (2 ^ T) hLen
    _ ≤ 2 ^ (2 * T) := Partition.mul_two_pow_self_le_two_pow_two_mul T
    _ = 2 ^ (2 * (partitionBinaryStructuredEncodedType.inputSize I + 1)) := by rfl

theorem weightedTextbookEdgesFrom_length (i w j : Nat) (weights : List Nat) :
    (weightedTextbookEdgesFrom i w j weights).length = weights.length := by
  induction weights generalizing j with
  | nil =>
      simp [weightedTextbookEdgesFrom]
  | cons v vs ih =>
      simp [weightedTextbookEdgesFrom, ih]

theorem weightedTextbookEdgesFromList_length_le (i : Nat) (weights : List Nat) :
    (weightedTextbookEdgesFromList i weights).length ≤ weights.length * weights.length := by
  induction weights generalizing i with
  | nil =>
      simp [weightedTextbookEdgesFromList]
  | cons w ws ih =>
      have hLen :
          (weightedTextbookEdgesFromList i (w :: ws)).length ≤
            ws.length + ws.length * ws.length := by
        calc
          (weightedTextbookEdgesFromList i (w :: ws)).length =
              (weightedTextbookEdgesFrom i w (i + 1) ws).length +
                (weightedTextbookEdgesFromList (i + 1) ws).length := by
                simp [weightedTextbookEdgesFromList]
          _ = ws.length + (weightedTextbookEdgesFromList (i + 1) ws).length := by
                rw [weightedTextbookEdgesFrom_length]
          _ ≤ ws.length + ws.length * ws.length := by
                exact Nat.add_le_add_left (ih (i := i + 1)) ws.length
      have hPoly : ws.length + ws.length * ws.length ≤ (w :: ws).length * (w :: ws).length := by
        simp
        nlinarith
      exact hLen.trans hPoly

theorem weightedTextbookEdges_length_le (weights : List Nat) :
    (weightedTextbookEdges weights).length ≤ weights.length * weights.length := by
  simpa [weightedTextbookEdges] using weightedTextbookEdgesFromList_length_le 0 weights

theorem weightedTextbookEdgesFrom_mem_bounds {i w j : Nat} {weights : List Nat}
    {e : Nat × Nat × Nat} (he : e ∈ weightedTextbookEdgesFrom i w j weights) :
    e.1 = i ∧ e.2.1 < j + weights.length := by
  induction weights generalizing j with
  | nil =>
      simp [weightedTextbookEdgesFrom] at he
  | cons v vs ih =>
      simp [weightedTextbookEdgesFrom] at he
      rcases he with hHead | hTail
      · subst e
        simp
      · rcases ih (j := j + 1) hTail with ⟨hFirst, hSecond⟩
        exact ⟨hFirst, by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hSecond⟩

theorem weightedTextbookEdgesFromList_mem_bounds {i : Nat} {weights : List Nat}
    {e : Nat × Nat × Nat} (he : e ∈ weightedTextbookEdgesFromList i weights) :
    e.1 < i + weights.length ∧ e.2.1 < i + weights.length := by
  induction weights generalizing i with
  | nil =>
      simp [weightedTextbookEdgesFromList] at he
  | cons w ws ih =>
      have hmem :
          e ∈ weightedTextbookEdgesFrom i w (i + 1) ws ∨
            e ∈ weightedTextbookEdgesFromList (i + 1) ws := by
        simpa [weightedTextbookEdgesFromList] using
          (List.mem_append.1 (by simpa [weightedTextbookEdgesFromList] using he))
      rcases hmem with hhead | htail
      · rcases weightedTextbookEdgesFrom_mem_bounds hhead with ⟨hFirst, hSecond⟩
        constructor
        · rw [hFirst]
          simp
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hSecond
      · rcases ih (i := i + 1) htail with ⟨hFirst, hSecond⟩
        constructor
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hFirst
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hSecond

theorem weightedTextbookEdgesFrom_mem_weight_le {i w j : Nat} {weights : List Nat}
    {e : Nat × Nat × Nat} (he : e ∈ weightedTextbookEdgesFrom i w j weights) :
    e.2.2 ≤ 4 * w * weights.sum := by
  induction weights generalizing j with
  | nil =>
      simp [weightedTextbookEdgesFrom] at he
  | cons v vs ih =>
      simp [weightedTextbookEdgesFrom] at he
      rcases he with hHead | hTail
      · subst e
        have hle : v ≤ (v :: vs).sum := by simp
        simpa [Nat.mul_assoc] using Nat.mul_le_mul_left (4 * w) hle
      · have hTailLe := ih (j := j + 1) hTail
        have hsum : vs.sum ≤ (v :: vs).sum := by simp
        have hmul : 4 * w * vs.sum ≤ 4 * w * (v :: vs).sum := by
          simpa [Nat.mul_assoc] using Nat.mul_le_mul_left (4 * w) hsum
        exact hTailLe.trans hmul

theorem weightedTextbookEdgesFromList_mem_weight_le {i : Nat} {weights : List Nat}
    {e : Nat × Nat × Nat} (he : e ∈ weightedTextbookEdgesFromList i weights) :
    e.2.2 ≤ 4 * weights.sum * weights.sum := by
  induction weights generalizing i with
  | nil =>
      simp [weightedTextbookEdgesFromList] at he
  | cons w ws ih =>
      have hmem :
          e ∈ weightedTextbookEdgesFrom i w (i + 1) ws ∨
            e ∈ weightedTextbookEdgesFromList (i + 1) ws := by
        simpa [weightedTextbookEdgesFromList] using
          (List.mem_append.1 (by simpa [weightedTextbookEdgesFromList] using he))
      have hW : w ≤ (w :: ws).sum := by simp
      have hWs : ws.sum ≤ (w :: ws).sum := by simp
      rcases hmem with hhead | htail
      · have hHead := weightedTextbookEdgesFrom_mem_weight_le hhead
        have hProd :
            4 * w * ws.sum ≤ 4 * (w :: ws).sum * (w :: ws).sum := by
          have hLeft : 4 * w ≤ 4 * (w :: ws).sum := Nat.mul_le_mul_left 4 hW
          simpa [Nat.mul_assoc] using Nat.mul_le_mul hLeft hWs
        exact hHead.trans hProd
      · have hTail := ih (i := i + 1) htail
        have hProd :
            4 * ws.sum * ws.sum ≤ 4 * (w :: ws).sum * (w :: ws).sum := by
          have hLeft : 4 * ws.sum ≤ 4 * (w :: ws).sum := Nat.mul_le_mul_left 4 hWs
          simpa [Nat.mul_assoc] using Nat.mul_le_mul hLeft hWs
        exact hTail.trans hProd

theorem weightedTextbookEdge_binaryStructured_inputSize_le_source_succ {I : PartitionInput}
    {e : Nat × Nat × Nat} (he : e ∈ weightedTextbookEdges I.weights) :
    weightedEdgeBinaryStructuredEncodedType.inputSize e ≤
      8 * (partitionBinaryStructuredEncodedType.inputSize I + 1) + 8 := by
  let S := partitionBinaryStructuredEncodedType.inputSize I
  let T := S + 1
  rcases weightedTextbookEdgesFromList_mem_bounds (i := 0) (weights := I.weights)
      (by simpa [weightedTextbookEdges] using he) with ⟨hFirst, hSecond⟩
  have hLen : I.weights.length ≤ S := by
    simpa [S] using partitionWeights_length_le_binaryStructured_inputSize I
  have hSltPow : S < 2 ^ T := by
    exact S.lt_two_pow_self.trans_le
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by dsimp [T]; omega))
  have hLen0 : 0 + I.weights.length ≤ S := by simpa using hLen
  have hFirstSize : EncodedType.binaryNat.inputSize e.1 ≤ T := by
    have hFirstLe : e.1 ≤ S := (Nat.le_of_lt hFirst).trans hLen0
    exact Knapsack.binaryNat_inputSize_le_of_lt_two_pow (hFirstLe.trans_lt hSltPow)
  have hSecondSize : EncodedType.binaryNat.inputSize e.2.1 ≤ T := by
    have hSecondLe : e.2.1 ≤ S := (Nat.le_of_lt hSecond).trans hLen0
    exact Knapsack.binaryNat_inputSize_le_of_lt_two_pow (hSecondLe.trans_lt hSltPow)
  have hSum : I.weights.sum ≤ 2 ^ (2 * T) := by
    simpa [T, S] using partitionWeights_sum_le_two_pow_two_mul_sourceSucc I
  have hWeightLe : e.2.2 ≤ 4 * I.weights.sum * I.weights.sum := by
    simpa [weightedTextbookEdges] using
      weightedTextbookEdgesFromList_mem_weight_le (i := 0) (weights := I.weights)
        (by simpa [weightedTextbookEdges] using he)
  have hFour : 4 ≤ 2 ^ 2 := by norm_num
  have hProdLeft :
      4 * I.weights.sum ≤ 2 ^ (2 + 2 * T) :=
    Partition.mul_le_two_pow_add_of_le hFour hSum
  have hProd :
      (4 * I.weights.sum) * I.weights.sum ≤ 2 ^ ((2 + 2 * T) + 2 * T) :=
    Partition.mul_le_two_pow_add_of_le hProdLeft hSum
  have hWeightPow :
      e.2.2 ≤ 2 ^ (4 * T + 2) := by
    calc
      e.2.2 ≤ (4 * I.weights.sum) * I.weights.sum := by
        simpa [Nat.mul_assoc] using hWeightLe
      _ ≤ 2 ^ ((2 + 2 * T) + 2 * T) := hProd
      _ ≤ 2 ^ (4 * T + 2) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hWeightLt : e.2.2 < 2 ^ (4 * T + 3) :=
    hWeightPow.trans_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega))
  have hWeightSize : EncodedType.binaryNat.inputSize e.2.2 ≤ 4 * T + 3 :=
    Knapsack.binaryNat_inputSize_le_of_lt_two_pow hWeightLt
  rw [weightedEdgeBinaryStructured_inputSize_eq]
  omega

theorem weightedTextbookEdges_binaryStructured_inputSize_le_source_succ
    (I : PartitionInput) :
    weightedEdgeListBinaryStructuredEncodedType.inputSize (weightedTextbookEdges I.weights) ≤
      100 * (partitionBinaryStructuredEncodedType.inputSize I + 1) ^ 3 := by
  let S := partitionBinaryStructuredEncodedType.inputSize I
  let T := S + 1
  let B := 8 * T + 8
  have hEach :
      ∀ e ∈ weightedTextbookEdges I.weights,
        weightedEdgeBinaryStructuredEncodedType.inputSize e ≤ B := by
    intro e he
    simpa [B, T, S] using
      weightedTextbookEdge_binaryStructured_inputSize_le_source_succ (I := I) he
  have hList :=
    VertexCover.encodedList_inputSize_le_length_mul_bound weightedEdgeBinaryStructuredEncodedType
      (weightedTextbookEdges I.weights) B hEach
  have hLenWeights : I.weights.length ≤ S := by
    simpa [S] using partitionWeights_length_le_binaryStructured_inputSize I
  have hEdgesLen : (weightedTextbookEdges I.weights).length ≤ S * S := by
    have hEdges := weightedTextbookEdges_length_le I.weights
    exact hEdges.trans (Nat.mul_le_mul hLenWeights hLenWeights)
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hSleT : S ≤ T := by dsimp [T]; omega
  have hEdgesLenT : (weightedTextbookEdges I.weights).length ≤ T ^ 2 := by
    have hSS : S * S ≤ T * T := Nat.mul_le_mul hSleT hSleT
    exact hEdgesLen.trans (by simpa [pow_two] using hSS)
  have hB : B + 1 ≤ 20 * T := by
    dsimp [B]
    nlinarith
  calc
    weightedEdgeListBinaryStructuredEncodedType.inputSize (weightedTextbookEdges I.weights)
        ≤ (weightedTextbookEdges I.weights).length * (B + 1) := hList
    _ ≤ T ^ 2 * (20 * T) := Nat.mul_le_mul hEdgesLenT hB
    _ ≤ 100 * T ^ 3 := by
      nlinarith

theorem weightedTextbookMap_threshold_binaryNat_inputSize_le_source_linear
    (I : PartitionInput) :
    EncodedType.binaryNat.inputSize (weightedTextbookMap I).threshold ≤
      4 * (partitionBinaryStructuredEncodedType.inputSize I + 1) + 1 := by
  let S := partitionBinaryStructuredEncodedType.inputSize I
  let T := S + 1
  have hSum : I.weights.sum ≤ 2 ^ (2 * T) := by
    simpa [T, S] using partitionWeights_sum_le_two_pow_two_mul_sourceSucc I
  have hThreshold :
      I.weights.sum * I.weights.sum ≤ 2 ^ (4 * T) := by
    calc
      I.weights.sum * I.weights.sum ≤ 2 ^ ((2 * T) + (2 * T)) :=
        Partition.mul_le_two_pow_add_of_le hSum hSum
      _ = 2 ^ (4 * T) := by congr 1; omega
  have hThresholdLt :
      I.weights.sum * I.weights.sum < 2 ^ (4 * T + 1) :=
    hThreshold.trans_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega))
  change EncodedType.binaryNat.inputSize (I.weights.sum * I.weights.sum) ≤ 4 * T + 1
  exact Knapsack.binaryNat_inputSize_le_of_lt_two_pow hThresholdLt

end MaxCut
end Karp21
end ComplexityReduction
