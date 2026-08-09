/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.GraphColoringToIncidenceSemantics
import ComplexityReduction.Domain.RectangularCoordinates
import ComplexityReduction.Program.CompileTM
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.InvariantFold
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatArithmetic
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.Projections
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.EdgeScan
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.HittingSet.StructuredRoute
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SetCovering.IncidentRunner

/-!
Direct-TM building blocks for the canonical Graph-Coloring-to-Incidence
gadget.

This companion starts with the shared self-loop guard.  It is intentionally
indexed by `GraphColoringIR`, imports no concrete Chromatic Number or Exact
Cover wrapper, and does not import the legacy Exact-Cover assembly.  Later
block-family and membership-pair builders must compose this exact guard rather
than replacing it with a route-local machine.
-/

namespace ComplexityReduction
namespace Domain
namespace GraphColoringToIncidence

open ComplexityReduction
open Encoding

/-- The exact source encoding at the canonical graph-and-colour-bound hub. -/
abbrev graphColoringEncoding : EncodedType :=
  GraphColoringIR.lawfulRepresentation.encodedType

/-- The standard structured encoding of one graph edge. -/
abbrev edgeEncoding : EncodedType :=
  ComplexityReduction.Combinatorics.Graph.edgeStructuredEncodedType

/-- The standard structured encoding of the stored ordered edge list. -/
abbrev edgeListEncoding : EncodedType :=
  ComplexityReduction.Combinatorics.Graph.edgeListStructuredEncodedType

/-- A direct decidable equality test for one edge's endpoints. -/
def edgeSelfLoopBool (edge : Nat × Nat) : Bool :=
  decide (edge.1 = edge.2)

theorem edgeSelfLoopBool_true_iff (edge : Nat × Nat) :
    edgeSelfLoopBool edge = true ↔ edge.1 = edge.2 := by
  simp [edgeSelfLoopBool]

/-- Direct-TM evidence for the exact edge self-loop test. -/
theorem edgeSelfLoopBool_tmPolyTime :
    TMPolyTimeMap edgeEncoding EncodedType.bool edgeSelfLoopBool := by
  have leftProjection :
      TMPolyTimeMap edgeEncoding EncodedType.nat (fun edge : Nat × Nat => edge.1) := by
    simpa [edgeEncoding] using TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have rightProjection :
      TMPolyTimeMap edgeEncoding EncodedType.nat (fun edge : Nat × Nat => edge.2) := by
    simpa [edgeEncoding] using TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have equalityInput :
      TMPolyTimeMap edgeEncoding (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun edge : Nat × Nat => (edge.1, edge.2)) :=
    TMPolyTimeMap.prod_mk leftProjection rightProjection
  have output := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq equalityInput
  simpa [Function.comp, edgeSelfLoopBool, edgeEncoding] using output

/-- Fold Boolean disjunction in a form with a standard direct-TM step witness. -/
def boolListOr (bits : List Bool) : Bool :=
  bits.foldl (fun accumulator bit => ComplexityReduction.Karp21.graphBoolOrPair (accumulator, bit)) false

theorem boolListOr_foldl_eq_true_iff (bits : List Bool) (accumulator : Bool) :
    bits.foldl (fun acc bit => ComplexityReduction.Karp21.graphBoolOrPair (acc, bit))
        accumulator = true ↔
      accumulator = true ∨ true ∈ bits := by
  induction bits generalizing accumulator with
  | nil => simp
  | cons bit bits inductionHypothesis =>
      simp [List.foldl, inductionHypothesis,
        ComplexityReduction.Karp21.graphBoolOrPair_eq_true_iff,
        or_assoc, or_left_comm, or_comm]

theorem boolListOr_eq_true_iff (bits : List Bool) :
    boolListOr bits = true ↔ true ∈ bits := by
  simpa [boolListOr] using boolListOr_foldl_eq_true_iff bits false

/-- Direct-TM evidence for the Boolean disjunction fold. -/
theorem boolListOr_tmPolyTime :
    TMPolyTimeMap (EncodedType.list EncodedType.bool) EncodedType.bool boolListOr := by
  rcases ComplexityReduction.Karp21.graphBoolOrPair_tm_polytime with ⟨stepTM⟩
  exact TMPolyTimeMap.list_foldl_typed_growth_bounded
    EncodedType.bool EncodedType.bool ComplexityReduction.Karp21.graphBoolOrPair false stepTM
    (Polynomial.C 1) (Polynomial.C 1)
    (by
      intro bits
      simp)
    (by
      intro source accumulator bit _bitBound
      simp [ComplexityReduction.Karp21.graphBoolOrPair])

/-- A streamable implementation of the core self-loop guard. -/
def graphHasSelfLoopBoolExecutable (input : GraphColoringIR) : Bool :=
  boolListOr (input.graph.edges.map edgeSelfLoopBool)

theorem graphHasSelfLoopBoolExecutable_eq_true_iff (input : GraphColoringIR) :
    graphHasSelfLoopBoolExecutable input = true ↔ GraphHasSelfLoop input := by
  rw [graphHasSelfLoopBoolExecutable, boolListOr_eq_true_iff]
  constructor
  · intro edgeBooleanMember
    rcases List.mem_map.mp edgeBooleanMember with ⟨edge, edgeMember, edgeLoop⟩
    exact ⟨edge, edgeMember, edgeSelfLoopBool_true_iff edge |>.mp edgeLoop⟩
  · rintro ⟨edge, edgeMember, loop⟩
    exact List.mem_map.mpr
      ⟨edge, edgeMember, edgeSelfLoopBool_true_iff edge |>.mpr loop⟩

/-- The streamable guard is extensionally the canonical hub guard. -/
theorem graphHasSelfLoopBoolExecutable_eq_core (input : GraphColoringIR) :
    graphHasSelfLoopBoolExecutable input = graphHasSelfLoopBool input := by
  cases executable : graphHasSelfLoopBoolExecutable input with
  | false =>
      cases core : graphHasSelfLoopBool input with
      | false => rfl
      | true =>
          have loop : GraphHasSelfLoop input :=
            (graphHasSelfLoopBool_eq_true_iff input).mp core
          have executableTrue := (graphHasSelfLoopBoolExecutable_eq_true_iff input).mpr loop
          simp [executable] at executableTrue
  | true =>
      cases core : graphHasSelfLoopBool input with
      | false =>
          have loop : GraphHasSelfLoop input :=
            (graphHasSelfLoopBoolExecutable_eq_true_iff input).mp executable
          have coreTrue := (graphHasSelfLoopBool_eq_true_iff input).mpr loop
          simp [core] at coreTrue
      | true => rfl

/-! ### Canonical graph-hub projections -/

/-- Direct-TM projection of the canonical graph payload from its graph-and-bound hub. -/
theorem graphProjection_tmPolyTime :
    TMPolyTimeMap graphColoringEncoding
      ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType
      (fun input : GraphColoringIR => input.graph) := by
  simpa [graphColoringEncoding, GraphColoringIR.lawfulRepresentation,
    GraphColoringIR.graph, StandardInstances.prod] using
    TMPolyTimeMap.fst
      ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType EncodedType.nat

/-- Direct-TM projection of the stored edge/direction graph payload. -/
theorem graphPayloadProjection_tmPolyTime :
    TMPolyTimeMap graphColoringEncoding
      ComplexityReduction.Combinatorics.Graph.graphPayloadStructuredEncodedType
      (fun input : GraphColoringIR =>
        ComplexityReduction.Karp21.graphPayloadOfGraph input.graph) := by
  have composed := TMPolyTimeMap.comp
    ComplexityReduction.Karp21.graphPayloadTMBackedMap.tm_polytime graphProjection_tmPolyTime
  simpa [Function.comp, GraphColoringIR.graph] using composed

/-- Direct-TM projection of the graph's complete ordered edge list. -/
theorem edgeListProjection_tmPolyTime :
    TMPolyTimeMap graphColoringEncoding edgeListEncoding
      (fun input : GraphColoringIR => input.graph.edges) := by
  have first := TMPolyTimeMap.fst edgeListEncoding EncodedType.bool
  have composed := TMPolyTimeMap.comp first graphPayloadProjection_tmPolyTime
  simpa [Function.comp, edgeListEncoding,
    ComplexityReduction.Karp21.graphPayloadOfGraph, GraphColoringIR.graph] using composed

/-- Direct-TM projection of the declared vertex bound. -/
theorem vertexCountProjection_tmPolyTime :
    TMPolyTimeMap graphColoringEncoding EncodedType.nat
      (fun input : GraphColoringIR => input.graph.vertices) := by
  have composed := TMPolyTimeMap.comp
    ComplexityReduction.Karp21.graphVerticesTMBackedMap.tm_polytime graphProjection_tmPolyTime
  simpa [Function.comp, GraphColoringIR.graph] using composed

/-- Direct-TM projection of the retained canonical colour bound. -/
theorem colorBoundProjection_tmPolyTime :
    TMPolyTimeMap graphColoringEncoding EncodedType.nat
      (fun input : GraphColoringIR => input.colors) := by
  simpa [graphColoringEncoding, GraphColoringIR.lawfulRepresentation,
    GraphColoringIR.colors, StandardInstances.prod] using
    TMPolyTimeMap.snd
      ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType EncodedType.nat

/-- Direct-TM computation of the ordered stored-edge count. -/
theorem edgeCountProjection_tmPolyTime :
    TMPolyTimeMap graphColoringEncoding EncodedType.nat
      (fun input : GraphColoringIR => input.graph.edges.length) := by
  have composed := TMPolyTimeMap.comp
    (ComplexityReduction.Karp21.HittingSet.listLengthTMBackedMap edgeEncoding).tm_polytime
    edgeListProjection_tmPolyTime
  simpa [Function.comp] using composed

/-- Direct-TM computation of the complete canonical Graph-to-Incidence universe size. -/
theorem universeSize_tmPolyTime :
    TMPolyTimeMap graphColoringEncoding EncodedType.nat universeSize := by
  have edgeColorCountInput :
      TMPolyTimeMap graphColoringEncoding
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun input : GraphColoringIR => (input.graph.edges.length, input.colors)) :=
    TMPolyTimeMap.prod_mk edgeCountProjection_tmPolyTime colorBoundProjection_tmPolyTime
  have edgeColorCount :
      TMPolyTimeMap graphColoringEncoding EncodedType.nat
        (fun input : GraphColoringIR => input.graph.edges.length * input.colors) := by
    have composed := TMPolyTimeMap.comp
      ComplexityReduction.GenericNatTM.natMul_tm_polytime edgeColorCountInput
    simpa [Function.comp] using composed
  have totalInput :
      TMPolyTimeMap graphColoringEncoding
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun input : GraphColoringIR =>
          (input.graph.vertices, input.graph.edges.length * input.colors)) :=
    TMPolyTimeMap.prod_mk vertexCountProjection_tmPolyTime edgeColorCount
  have total := TMPolyTimeMap.comp ComplexityReduction.natAdd_tm_polytime totalInput
  convert total using 1
  funext input
  simp only [Function.comp_apply]
  unfold universeSize
  rw [edgeColorPairs_length]

/-! ### Bounded edge/colour marker layout -/

/-- The direct-TM input layout for one graph-hub edge/colour coordinate. -/
abbrev edgeColorCodeInputEncoding : EncodedType :=
  EncodedType.prod graphColoringEncoding (EncodedType.prod EncodedType.nat EncodedType.nat)

/--
The arithmetic layout of a bounded edge/colour marker.  Bounds are discharged
by the callers that enumerate `List.range`; the next theorem connects this
total executable to the core's ordered-product `idxOf` layout.
-/
def edgeColorCodeExecutable (argument : GraphColoringIR × (Nat × Nat)) : Nat :=
  argument.1.graph.vertices + argument.2.1 * argument.1.colors + argument.2.2

/-- Direct-TM evidence for the arithmetic edge/colour marker layout. -/
theorem edgeColorCodeExecutable_tmPolyTime :
    TMPolyTimeMap edgeColorCodeInputEncoding EncodedType.nat edgeColorCodeExecutable := by
  let X := edgeColorCodeInputEncoding
  have source : TMPolyTimeMap X graphColoringEncoding
      (fun argument : GraphColoringIR × (Nat × Nat) => argument.1) := by
    simpa [X, edgeColorCodeInputEncoding] using
      TMPolyTimeMap.fst graphColoringEncoding (EncodedType.prod EncodedType.nat EncodedType.nat)
  have coordinate : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun argument : GraphColoringIR × (Nat × Nat) => argument.2) := by
    simpa [X, edgeColorCodeInputEncoding] using
      TMPolyTimeMap.snd graphColoringEncoding (EncodedType.prod EncodedType.nat EncodedType.nat)
  have edgeIndex : TMPolyTimeMap X EncodedType.nat
      (fun argument : GraphColoringIR × (Nat × Nat) => argument.2.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst EncodedType.nat EncodedType.nat) coordinate
    simpa [Function.comp, X] using composed
  have color : TMPolyTimeMap X EncodedType.nat
      (fun argument : GraphColoringIR × (Nat × Nat) => argument.2.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd EncodedType.nat EncodedType.nat) coordinate
    simpa [Function.comp, X] using composed
  have vertices : TMPolyTimeMap X EncodedType.nat
      (fun argument : GraphColoringIR × (Nat × Nat) => argument.1.graph.vertices) := by
    have composed := TMPolyTimeMap.comp vertexCountProjection_tmPolyTime source
    simpa [Function.comp, X] using composed
  have colors : TMPolyTimeMap X EncodedType.nat
      (fun argument : GraphColoringIR × (Nat × Nat) => argument.1.colors) := by
    have composed := TMPolyTimeMap.comp colorBoundProjection_tmPolyTime source
    simpa [Function.comp, X] using composed
  have multiplied : TMPolyTimeMap X EncodedType.nat
      (fun argument : GraphColoringIR × (Nat × Nat) => argument.2.1 * argument.1.colors) := by
    have input := TMPolyTimeMap.prod_mk edgeIndex colors
    have composed := TMPolyTimeMap.comp ComplexityReduction.GenericNatTM.natMul_tm_polytime input
    simpa [Function.comp, X] using composed
  have firstSum : TMPolyTimeMap X EncodedType.nat
      (fun argument : GraphColoringIR × (Nat × Nat) =>
        argument.1.graph.vertices + argument.2.1 * argument.1.colors) := by
    have input := TMPolyTimeMap.prod_mk vertices multiplied
    have composed := TMPolyTimeMap.comp ComplexityReduction.natAdd_tm_polytime input
    simpa [Function.comp, X] using composed
  have input := TMPolyTimeMap.prod_mk firstSum color
  have output := TMPolyTimeMap.comp ComplexityReduction.natAdd_tm_polytime input
  simpa [edgeColorCodeExecutable, Function.comp, X] using output

private theorem product_getElem?_mul_add {α β : Type} (xs : List α) (ys : List β)
    (i j : Nat) (hi : i < xs.length) (hj : j < ys.length) :
    (xs ×ˢ ys)[i * ys.length + j]? = some (xs[i], ys[j]) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs inductionHypothesis =>
      cases i with
      | zero => simp [List.product_cons, List.getElem?_append, hj]
      | succ i =>
          have tailBound : i < xs.length := Nat.lt_of_succ_lt_succ hi
          have outsideHead : ¬ ((i + 1) * ys.length + j < ys.length) := by
            have positiveLength : 0 < ys.length := by omega
            nlinarith
          have shiftedIndex : (i + 1) * ys.length + j - ys.length = i * ys.length + j := by
            rw [Nat.succ_mul]
            omega
          simp [List.product_cons, List.getElem?_append, outsideHead, shiftedIndex,
            inductionHypothesis i tailBound]

private theorem range_product_idxOf_eq_mul_add (edgeCount colorCount edgeIndex color : Nat)
    (edgeBound : edgeIndex < edgeCount) (colorBound : color < colorCount) :
    (List.range edgeCount ×ˢ List.range colorCount).idxOf (edgeIndex, color) =
      edgeIndex * colorCount + color := by
  have lookup := product_getElem?_mul_add (List.range edgeCount) (List.range colorCount)
    edgeIndex color (by simpa using edgeBound) (by simpa using colorBound)
  simp at lookup
  rcases (List.getElem?_eq_some_iff.mp lookup) with ⟨indexBound, indexedValue⟩
  have nodup : (List.range edgeCount ×ˢ List.range colorCount).Nodup :=
    (List.nodup_range (n := edgeCount)).product (List.nodup_range (n := colorCount))
  have indexed := nodup.idxOf_getElem (edgeIndex * colorCount + color) indexBound
  simpa [indexedValue] using indexed

/-- Bounded coordinates use exactly the core ordered-product marker identity. -/
theorem edgeColorCodeExecutable_eq_core {input : GraphColoringIR} {edgeIndex color : Nat}
    (edgeBound : edgeIndex < input.graph.edges.length) (colorBound : color < input.colors) :
    edgeColorCodeExecutable (input, (edgeIndex, color)) =
      edgeColorCode input edgeIndex color := by
  simp [edgeColorCodeExecutable, edgeColorCode, edgeColorPairs,
    range_product_idxOf_eq_mul_add _ _ _ _ edgeBound colorBound, Nat.add_assoc]

/-- The executable singleton filler block at one bounded edge/colour coordinate. -/
def fillerBlockExecutable (argument : GraphColoringIR × (Nat × Nat)) : List Nat :=
  [edgeColorCodeExecutable argument]

/-- Direct-TM evidence for the singleton filler block. -/
theorem fillerBlockExecutable_tmPolyTime :
    TMPolyTimeMap edgeColorCodeInputEncoding (EncodedType.list EncodedType.nat)
      fillerBlockExecutable := by
  have output := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_singleton EncodedType.nat) edgeColorCodeExecutable_tmPolyTime
  simpa [fillerBlockExecutable, Function.comp] using output

/-- Bounded executable filler blocks recover exactly the core ordered marker block. -/
theorem fillerBlockExecutable_eq_core {input : GraphColoringIR} {edgeIndex color : Nat}
    (edgeBound : edgeIndex < input.graph.edges.length) (colorBound : color < input.colors) :
    fillerBlockExecutable (input, (edgeIndex, color)) = fillerBlock input edgeIndex color := by
  simp only [fillerBlockExecutable, fillerBlock]
  rw [edgeColorCodeExecutable_eq_core edgeBound colorBound]

/-! ### Ordered incident-edge scan -/

/-- The direct-TM input layout for scanning one graph-hub vertex's incident edge indices. -/
abbrev incidentEdgeInputEncoding : EncodedType :=
  EncodedType.prod graphColoringEncoding EncodedType.nat

/-- Reuse the generic finite-alphabet edge-index scan at the canonical graph hub. -/
def incidentEdgeIndicesExecutable (argument : GraphColoringIR × Nat) : List Nat :=
  ComplexityReduction.Karp21.SetCovering.incidentEdgeIndicesFromEdges
    (argument.1.graph.edges, argument.2)

/-- Direct-TM evidence for the complete ordered incident-edge scan. -/
theorem incidentEdgeIndicesExecutable_tmPolyTime :
    TMPolyTimeMap incidentEdgeInputEncoding (EncodedType.list EncodedType.nat)
      incidentEdgeIndicesExecutable := by
  let X := incidentEdgeInputEncoding
  have source : TMPolyTimeMap X graphColoringEncoding
      (fun argument : GraphColoringIR × Nat => argument.1) := by
    simpa [X, incidentEdgeInputEncoding] using
      TMPolyTimeMap.fst graphColoringEncoding EncodedType.nat
  have vertex : TMPolyTimeMap X EncodedType.nat
      (fun argument : GraphColoringIR × Nat => argument.2) := by
    simpa [X, incidentEdgeInputEncoding] using
      TMPolyTimeMap.snd graphColoringEncoding EncodedType.nat
  have edges : TMPolyTimeMap X edgeListEncoding
      (fun argument : GraphColoringIR × Nat => argument.1.graph.edges) := by
    have composed := TMPolyTimeMap.comp edgeListProjection_tmPolyTime source
    simpa [Function.comp, X] using composed
  have scanInput := TMPolyTimeMap.prod_mk edges vertex
  have output := TMPolyTimeMap.comp
    ComplexityReduction.Karp21.SetCovering.incidentEdgeIndicesFromEdges_tm_polytime scanInput
  simpa [incidentEdgeIndicesExecutable, Function.comp,
    ComplexityReduction.Karp21.SetCovering.incidentEdgeInstructionInputEncodedType, X] using output

private theorem range_succ_eq_zero_map (length : Nat) :
    List.range (length + 1) = 0 :: (List.range length).map (fun index => index + 1) := by
  induction length with
  | zero => rfl
  | succ length inductionHypothesis =>
      change List.range ((length + 1) + 1) =
        0 :: (List.range (length + 1)).map (fun index => index + 1)
      rw [List.range_succ, inductionHypothesis]
      have shifted := congrArg (List.map fun index : Nat => index + 1) inductionHypothesis
      simpa [List.range_succ, List.map_append, List.map_map, Function.comp_def,
        Nat.add_assoc] using shifted

private theorem findIdxs_eq_filter_range_getD {α : Type} (default : α)
    (entries : List α) (predicate : α → Bool) (start : Nat) :
    entries.findIdxs predicate start =
      ((List.range entries.length).filter
        (fun index => predicate (entries.getD index default))).map (fun index => index + start) := by
  induction entries generalizing start with
  | nil => simp
  | cons entry entries inductionHypothesis =>
      change
        (entry :: entries).findIdxs predicate start =
          ((List.range (entries.length + 1)).filter
            (fun index => predicate ((entry :: entries).getD index default))).map
              (fun index => index + start)
      rw [List.findIdxs_cons, range_succ_eq_zero_map]
      rw [List.filter_cons]
      simp only [List.getD_cons_zero]
      have tail :
          (List.filter
            (fun index => predicate ((entry :: entries).getD index default))
            ((List.range entries.length).map fun index => index + 1)).map
              (fun index => index + start) =
            entries.findIdxs predicate (start + 1) := by
        rw [List.filter_map]
        simp only [List.map_map]
        change List.map (fun index => (index + 1) + start)
          (List.filter (fun index => predicate ((entry :: entries).getD (index + 1) default))
            (List.range entries.length)) = _
        have predicateTail :
            (fun index => predicate ((entry :: entries).getD (index + 1) default)) =
              fun index => predicate (entries.getD index default) := by
          funext index
          simp
        rw [predicateTail]
        have addOrder : (fun index : Nat => (index + 1) + start) =
            fun index => index + (start + 1) := by
          funext index
          omega
        rw [addOrder, ← inductionHypothesis]
      split <;> simp_all

/-- The reusable ordered scan agrees exactly with the core's range/filter presentation. -/
theorem incidentEdgeIndicesExecutable_eq_core (input : GraphColoringIR) (vertex : Nat) :
    incidentEdgeIndicesExecutable (input, vertex) = incidentEdgeIndices input vertex := by
  rw [incidentEdgeIndicesExecutable,
    ComplexityReduction.Karp21.SetCovering.incidentEdgeIndicesFromEdges_eq_findIdxs]
  simp only [ComplexityReduction.Karp21.SetCovering.edgeIncidentBool_eq_decide]
  rw [findIdxs_eq_filter_range_getD (0, 0) input.graph.edges
    (fun edge => decide (edge.1 = vertex ∨ edge.2 = vertex)) 0]
  simp [incidentEdgeIndices, edgeIncidentBool, EdgeIncident, edgeAt]

/-! ### Choice-block arithmetic context -/

/-- The retained layout data for one choice block: vertices, colours, vertex, and colour. -/
abbrev ChoiceCodeContext : Type := Nat × (Nat × (Nat × Nat))

/-- Exact structural encoding for the choice-block arithmetic context. -/
abbrev choiceCodeContextEncoding : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.nat))

/-- The direct-TM input layout for a context together with one incident edge index. -/
abbrev choiceCodeInputEncoding : EncodedType :=
  EncodedType.prod choiceCodeContextEncoding EncodedType.nat

/-- Construct one choice-block arithmetic context from a canonical hub coordinate. -/
def choiceCodeContextOf (argument : GraphColoringIR × (Nat × Nat)) : ChoiceCodeContext :=
  (argument.1.graph.vertices, (argument.1.colors, (argument.2.1, argument.2.2)))

/-- Emit one private edge/colour marker from the retained choice-block context. -/
def choiceCodeFromContext (argument : ChoiceCodeContext × Nat) : Nat :=
  argument.1.1 + argument.2 * argument.1.2.1 + argument.1.2.2.2

/-- Direct-TM evidence for one context-indexed choice-block marker. -/
theorem choiceCodeFromContext_tmPolyTime :
    TMPolyTimeMap choiceCodeInputEncoding EncodedType.nat choiceCodeFromContext := by
  let X := choiceCodeInputEncoding
  have context : TMPolyTimeMap X choiceCodeContextEncoding
      (fun argument : ChoiceCodeContext × Nat => argument.1) := by
    simpa [X, choiceCodeInputEncoding] using
      TMPolyTimeMap.fst choiceCodeContextEncoding EncodedType.nat
  have edgeIndex : TMPolyTimeMap X EncodedType.nat
      (fun argument : ChoiceCodeContext × Nat => argument.2) := by
    simpa [X, choiceCodeInputEncoding] using
      TMPolyTimeMap.snd choiceCodeContextEncoding EncodedType.nat
  have contextTail : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat (EncodedType.prod EncodedType.nat EncodedType.nat))
      (fun argument : ChoiceCodeContext × Nat => argument.1.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat (EncodedType.prod EncodedType.nat EncodedType.nat))) context
    simpa [Function.comp, X, choiceCodeContextEncoding] using composed
  have vertices : TMPolyTimeMap X EncodedType.nat
      (fun argument : ChoiceCodeContext × Nat => argument.1.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat (EncodedType.prod EncodedType.nat EncodedType.nat))) context
    simpa [Function.comp, X, choiceCodeContextEncoding] using composed
  have colors : TMPolyTimeMap X EncodedType.nat
      (fun argument : ChoiceCodeContext × Nat => argument.1.2.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst EncodedType.nat (EncodedType.prod EncodedType.nat EncodedType.nat)) contextTail
    simpa [Function.comp, X, choiceCodeContextEncoding] using composed
  have contextCoordinates : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun argument : ChoiceCodeContext × Nat => argument.1.2.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd EncodedType.nat (EncodedType.prod EncodedType.nat EncodedType.nat)) contextTail
    simpa [Function.comp, X, choiceCodeContextEncoding] using composed
  have color : TMPolyTimeMap X EncodedType.nat
      (fun argument : ChoiceCodeContext × Nat => argument.1.2.2.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd EncodedType.nat EncodedType.nat) contextCoordinates
    simpa [Function.comp, X, choiceCodeContextEncoding] using composed
  have multiplied : TMPolyTimeMap X EncodedType.nat
      (fun argument : ChoiceCodeContext × Nat => argument.2 * argument.1.2.1) := by
    have input := TMPolyTimeMap.prod_mk edgeIndex colors
    have composed := TMPolyTimeMap.comp ComplexityReduction.GenericNatTM.natMul_tm_polytime input
    simpa [Function.comp, X] using composed
  have firstSum : TMPolyTimeMap X EncodedType.nat
      (fun argument : ChoiceCodeContext × Nat =>
        argument.1.1 + argument.2 * argument.1.2.1) := by
    have input := TMPolyTimeMap.prod_mk vertices multiplied
    have composed := TMPolyTimeMap.comp ComplexityReduction.natAdd_tm_polytime input
    simpa [Function.comp, X] using composed
  have input := TMPolyTimeMap.prod_mk firstSum color
  have output := TMPolyTimeMap.comp ComplexityReduction.natAdd_tm_polytime input
  simpa [choiceCodeFromContext, Function.comp, X] using output

/-- The retained context emits the same bounded marker identity as the core layout. -/
theorem choiceCodeFromContext_eq_core {input : GraphColoringIR} {vertex edgeIndex color : Nat}
    (edgeBound : edgeIndex < input.graph.edges.length) (colorBound : color < input.colors) :
    choiceCodeFromContext
      (choiceCodeContextOf (input, (vertex, color)), edgeIndex) =
        edgeColorCode input edgeIndex color := by
  exact edgeColorCodeExecutable_eq_core edgeBound colorBound

/-- A choice-block instruction first installs layout context, then emits one incident index. -/
abbrev ChoiceBlockInstruction : Type := ChoiceCodeContext ⊕ Nat

/-- Exact structural encoding for one choice-block instruction. -/
abbrev choiceBlockInstructionEncoding : EncodedType :=
  EncodedType.sum choiceCodeContextEncoding EncodedType.nat

/-- Exact structural encoding for the choice-block instruction stream. -/
abbrev choiceBlockInstructionListEncoding : EncodedType :=
  EncodedType.list choiceBlockInstructionEncoding

/-- The fold retains layout context and the already emitted marker list. -/
abbrev ChoiceBlockAccumulator : Type := ChoiceCodeContext × List Nat

/-- Exact structural encoding for one choice-block fold state. -/
abbrev choiceBlockAccumulatorEncoding : EncodedType :=
  EncodedType.prod choiceCodeContextEncoding (EncodedType.list EncodedType.nat)

/-- Fixed initial state before the context instruction is received. -/
def choiceBlockInitialAccumulator : ChoiceBlockAccumulator :=
  ((0, (0, (0, 0))), [])

/-- Inject a layout context as the leading choice-block instruction. -/
def choiceBlockInitInstruction (context : ChoiceCodeContext) : ChoiceBlockInstruction :=
  .inl context

/-- Inject one incident edge index as a choice-block instruction. -/
def choiceBlockIndexInstruction (edgeIndex : Nat) : ChoiceBlockInstruction :=
  .inr edgeIndex

/-- Construct the complete stream for one graph/vertex/colour coordinate. -/
def choiceBlockInstructions (argument : GraphColoringIR × (Nat × Nat)) :
    List ChoiceBlockInstruction :=
  choiceBlockInitInstruction (choiceCodeContextOf argument) ::
    (incidentEdgeIndicesExecutable (argument.1, argument.2.1)).map choiceBlockIndexInstruction

/-- Direct-TM reification of a graph-hub coordinate into its retained arithmetic context. -/
theorem choiceCodeContextOf_tmPolyTime :
    TMPolyTimeMap edgeColorCodeInputEncoding choiceCodeContextEncoding choiceCodeContextOf := by
  let X := edgeColorCodeInputEncoding
  have source : TMPolyTimeMap X graphColoringEncoding
      (fun argument : GraphColoringIR × (Nat × Nat) => argument.1) := by
    simpa [X, edgeColorCodeInputEncoding] using
      TMPolyTimeMap.fst graphColoringEncoding (EncodedType.prod EncodedType.nat EncodedType.nat)
  have coordinates : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun argument : GraphColoringIR × (Nat × Nat) => argument.2) := by
    simpa [X, edgeColorCodeInputEncoding] using
      TMPolyTimeMap.snd graphColoringEncoding (EncodedType.prod EncodedType.nat EncodedType.nat)
  have vertex : TMPolyTimeMap X EncodedType.nat
      (fun argument : GraphColoringIR × (Nat × Nat) => argument.2.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst EncodedType.nat EncodedType.nat) coordinates
    simpa [Function.comp, X] using composed
  have color : TMPolyTimeMap X EncodedType.nat
      (fun argument : GraphColoringIR × (Nat × Nat) => argument.2.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd EncodedType.nat EncodedType.nat) coordinates
    simpa [Function.comp, X] using composed
  have vertices : TMPolyTimeMap X EncodedType.nat
      (fun argument : GraphColoringIR × (Nat × Nat) => argument.1.graph.vertices) := by
    have composed := TMPolyTimeMap.comp vertexCountProjection_tmPolyTime source
    simpa [Function.comp, X] using composed
  have colors : TMPolyTimeMap X EncodedType.nat
      (fun argument : GraphColoringIR × (Nat × Nat) => argument.1.colors) := by
    have composed := TMPolyTimeMap.comp colorBoundProjection_tmPolyTime source
    simpa [Function.comp, X] using composed
  have output := TMPolyTimeMap.prod_mk vertices
    (TMPolyTimeMap.prod_mk colors (TMPolyTimeMap.prod_mk vertex color))
  simpa [choiceCodeContextOf, choiceCodeContextEncoding] using output

/-- Direct-TM injection of the leading context instruction. -/
theorem choiceBlockInitInstruction_tmPolyTime :
    TMPolyTimeMap choiceCodeContextEncoding choiceBlockInstructionEncoding
      choiceBlockInitInstruction := by
  simpa [choiceBlockInitInstruction, choiceBlockInstructionEncoding] using
    TMPolyTimeMap.inl choiceCodeContextEncoding EncodedType.nat

/-- Direct-TM injection of one incident-index instruction. -/
theorem choiceBlockIndexInstruction_tmPolyTime :
    TMPolyTimeMap EncodedType.nat choiceBlockInstructionEncoding
      choiceBlockIndexInstruction := by
  simpa [choiceBlockIndexInstruction, choiceBlockInstructionEncoding] using
    TMPolyTimeMap.inr choiceCodeContextEncoding EncodedType.nat

/-- Direct-TM construction of the complete context-plus-incident-index instruction stream. -/
theorem choiceBlockInstructions_tmPolyTime :
    TMPolyTimeMap edgeColorCodeInputEncoding choiceBlockInstructionListEncoding
      choiceBlockInstructions := by
  let X := edgeColorCodeInputEncoding
  have source : TMPolyTimeMap X graphColoringEncoding
      (fun argument : GraphColoringIR × (Nat × Nat) => argument.1) := by
    simpa [X, edgeColorCodeInputEncoding] using
      TMPolyTimeMap.fst graphColoringEncoding (EncodedType.prod EncodedType.nat EncodedType.nat)
  have coordinates : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun argument : GraphColoringIR × (Nat × Nat) => argument.2) := by
    simpa [X, edgeColorCodeInputEncoding] using
      TMPolyTimeMap.snd graphColoringEncoding (EncodedType.prod EncodedType.nat EncodedType.nat)
  have vertex : TMPolyTimeMap X EncodedType.nat
      (fun argument : GraphColoringIR × (Nat × Nat) => argument.2.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst EncodedType.nat EncodedType.nat) coordinates
    simpa [Function.comp, X] using composed
  have context : TMPolyTimeMap X choiceCodeContextEncoding
      (fun argument : GraphColoringIR × (Nat × Nat) => choiceCodeContextOf argument) :=
    choiceCodeContextOf_tmPolyTime
  have init : TMPolyTimeMap X choiceBlockInstructionEncoding
      (fun argument : GraphColoringIR × (Nat × Nat) =>
        choiceBlockInitInstruction (choiceCodeContextOf argument)) := by
    have composed := TMPolyTimeMap.comp choiceBlockInitInstruction_tmPolyTime context
    simpa [Function.comp, X] using composed
  have incidentInput : TMPolyTimeMap X incidentEdgeInputEncoding
      (fun argument : GraphColoringIR × (Nat × Nat) => (argument.1, argument.2.1)) := by
    simpa [incidentEdgeInputEncoding] using TMPolyTimeMap.prod_mk source vertex
  have indices : TMPolyTimeMap X (EncodedType.list EncodedType.nat)
      (fun argument : GraphColoringIR × (Nat × Nat) =>
        incidentEdgeIndicesExecutable (argument.1, argument.2.1)) := by
    have composed := TMPolyTimeMap.comp incidentEdgeIndicesExecutable_tmPolyTime incidentInput
    simpa [Function.comp, X] using composed
  have indexInstructions : TMPolyTimeMap X choiceBlockInstructionListEncoding
      (fun argument : GraphColoringIR × (Nat × Nat) =>
        (incidentEdgeIndicesExecutable (argument.1, argument.2.1)).map
          choiceBlockIndexInstruction) := by
    have mapped := TMPolyTimeMap.list_map choiceBlockIndexInstruction_tmPolyTime
    have composed := TMPolyTimeMap.comp mapped indices
    simpa [Function.comp, choiceBlockInstructionListEncoding, X] using composed
  have input := TMPolyTimeMap.prod_mk init indexInstructions
  have output := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons choiceBlockInstructionEncoding) input
  simpa [choiceBlockInstructions, Function.comp, choiceBlockInstructionListEncoding, X] using output

/-- One closed fold step either installs context or appends one private marker. -/
def choiceBlockStep (argument : ChoiceBlockAccumulator × ChoiceBlockInstruction) :
    ChoiceBlockAccumulator :=
  match argument.2 with
  | .inl context => (context, [context.2.2.1])
  | .inr edgeIndex =>
      (argument.1.1,
        argument.1.2 ++ [choiceCodeFromContext (argument.1.1, edgeIndex)])

/-- Direct-TM realization of the context-install branch of the choice-block fold. -/
theorem choiceBlockStepLeft_tmPolyTime :
    TMPolyTimeMap choiceCodeContextEncoding choiceBlockAccumulatorEncoding
      (fun context : ChoiceCodeContext => (context, [context.2.2.1])) := by
  let X := choiceCodeContextEncoding
  have tail : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat (EncodedType.prod EncodedType.nat EncodedType.nat))
      (fun context : ChoiceCodeContext => context.2) := by
    simpa [X, choiceCodeContextEncoding] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat (EncodedType.prod EncodedType.nat EncodedType.nat))
  have coordinates : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun context : ChoiceCodeContext => context.2.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd EncodedType.nat (EncodedType.prod EncodedType.nat EncodedType.nat)) tail
    simpa [Function.comp, X, choiceCodeContextEncoding] using composed
  have vertex : TMPolyTimeMap X EncodedType.nat
      (fun context : ChoiceCodeContext => context.2.2.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst EncodedType.nat EncodedType.nat) coordinates
    simpa [Function.comp, X, choiceCodeContextEncoding] using composed
  have singleton : TMPolyTimeMap X (EncodedType.list EncodedType.nat)
      (fun context : ChoiceCodeContext => [context.2.2.1]) := by
    have composed := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton EncodedType.nat) vertex
    simpa [Function.comp] using composed
  simpa [choiceBlockAccumulatorEncoding] using
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id X) singleton

/-- Direct-TM realization of the index-append branch of the choice-block fold. -/
theorem choiceBlockStepRight_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod choiceBlockAccumulatorEncoding EncodedType.nat)
      choiceBlockAccumulatorEncoding
      (fun argument : ChoiceBlockAccumulator × Nat =>
        (argument.1.1,
          argument.1.2 ++ [choiceCodeFromContext (argument.1.1, argument.2)])) := by
  let X := EncodedType.prod choiceBlockAccumulatorEncoding EncodedType.nat
  have accumulator : TMPolyTimeMap X choiceBlockAccumulatorEncoding
      (fun argument : ChoiceBlockAccumulator × Nat => argument.1) := by
    simpa [X] using TMPolyTimeMap.fst choiceBlockAccumulatorEncoding EncodedType.nat
  have edgeIndex : TMPolyTimeMap X EncodedType.nat
      (fun argument : ChoiceBlockAccumulator × Nat => argument.2) := by
    simpa [X] using TMPolyTimeMap.snd choiceBlockAccumulatorEncoding EncodedType.nat
  have context : TMPolyTimeMap X choiceCodeContextEncoding
      (fun argument : ChoiceBlockAccumulator × Nat => argument.1.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst choiceCodeContextEncoding (EncodedType.list EncodedType.nat)) accumulator
    simpa [Function.comp, X, choiceBlockAccumulatorEncoding] using composed
  have output : TMPolyTimeMap X (EncodedType.list EncodedType.nat)
      (fun argument : ChoiceBlockAccumulator × Nat => argument.1.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd choiceCodeContextEncoding (EncodedType.list EncodedType.nat)) accumulator
    simpa [Function.comp, X, choiceBlockAccumulatorEncoding] using composed
  have codeInput : TMPolyTimeMap X choiceCodeInputEncoding
      (fun argument : ChoiceBlockAccumulator × Nat => (argument.1.1, argument.2)) := by
    simpa [choiceCodeInputEncoding] using TMPolyTimeMap.prod_mk context edgeIndex
  have code : TMPolyTimeMap X EncodedType.nat
      (fun argument : ChoiceBlockAccumulator × Nat =>
        choiceCodeFromContext (argument.1.1, argument.2)) := by
    have composed := TMPolyTimeMap.comp choiceCodeFromContext_tmPolyTime codeInput
    simpa [Function.comp, X] using composed
  have singleton : TMPolyTimeMap X (EncodedType.list EncodedType.nat)
      (fun argument : ChoiceBlockAccumulator × Nat =>
        [choiceCodeFromContext (argument.1.1, argument.2)]) := by
    have composed := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton EncodedType.nat) code
    simpa [Function.comp] using composed
  have appendInput : TMPolyTimeMap X
      (EncodedType.prod (EncodedType.list EncodedType.nat) (EncodedType.list EncodedType.nat))
      (fun argument : ChoiceBlockAccumulator × Nat =>
        (argument.1.2, [choiceCodeFromContext (argument.1.1, argument.2)])) :=
    TMPolyTimeMap.prod_mk output singleton
  have appended : TMPolyTimeMap X (EncodedType.list EncodedType.nat)
      (fun argument : ChoiceBlockAccumulator × Nat =>
        argument.1.2 ++ [choiceCodeFromContext (argument.1.1, argument.2)]) := by
    have composed := TMPolyTimeMap.comp (TMPolyTimeMap.list_append EncodedType.nat) appendInput
    simpa [Function.comp] using composed
  simpa [choiceBlockAccumulatorEncoding] using TMPolyTimeMap.prod_mk context appended

/-- The complete choice-block step uses only reusable structural product/sum dispatch. -/
theorem choiceBlockStep_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod choiceBlockAccumulatorEncoding choiceBlockInstructionEncoding)
      choiceBlockAccumulatorEncoding choiceBlockStep := by
  have choice := ComplexityReduction.prodSumChoice_tm_polytime
    choiceBlockAccumulatorEncoding choiceCodeContextEncoding EncodedType.nat
  have branches := TMPolyTimeMap.sum_elim
    choiceBlockStepLeft_tmPolyTime choiceBlockStepRight_tmPolyTime
  have output := TMPolyTimeMap.comp branches choice
  convert output using 1
  funext argument
  rcases argument with ⟨accumulator, instruction⟩
  cases instruction <;> rfl

/-! ### Verified choice-block fold bound -/

theorem choiceCodeContextEncoding_inputSize
    (vertices colors vertex color : Nat) :
    choiceCodeContextEncoding.inputSize (vertices, (colors, (vertex, color))) =
      vertices + colors + vertex + color + 7 := by
  simp [choiceCodeContextEncoding, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat]
  omega

theorem choiceBlockAccumulatorEncoding_inputSize
    (context : ChoiceCodeContext) (output : List Nat) :
    choiceBlockAccumulatorEncoding.inputSize (context, output) =
      choiceCodeContextEncoding.inputSize context +
        (EncodedType.list EncodedType.nat).inputSize output + 1 := by
  simp [choiceBlockAccumulatorEncoding, EncodedType.inputSize_prod]
  omega

theorem natList_inputSize_append_singleton (output : List Nat) (value : Nat) :
    (EncodedType.list EncodedType.nat).inputSize (output ++ [value]) =
      (EncodedType.list EncodedType.nat).inputSize output + value + 2 := by
  simp [EncodedType.inputSize, EncodedType.list, EncodedType.nat, List.flatMap_append]
  omega

theorem choiceBlockInstructionEncoding_inputSize_inl (context : ChoiceCodeContext) :
    choiceBlockInstructionEncoding.inputSize (Sum.inl context) =
      choiceCodeContextEncoding.inputSize context + 1 := by
  unfold choiceBlockInstructionEncoding
  simp [EncodedType.inputSize, EncodedType.sum]

theorem choiceBlockInstructionEncoding_inputSize_inr (edgeIndex : Nat) :
    choiceBlockInstructionEncoding.inputSize (Sum.inr edgeIndex) = edgeIndex + 2 := by
  unfold choiceBlockInstructionEncoding
  simp only [EncodedType.inputSize, EncodedType.sum]
  rw [List.length_append, List.length_map]
  simp [EncodedType.nat]
  omega

/-- The reachable fold state retains either its initial/zero context or a context bounded by its source. -/
def ChoiceBlockFoldInvariant (bound : Nat) (accumulator : ChoiceBlockAccumulator) : Prop :=
  accumulator = choiceBlockInitialAccumulator ∨
    accumulator.1 = (0, (0, (0, 0))) ∨
      choiceCodeContextEncoding.inputSize accumulator.1 ≤ bound

/-- Fixed base budget for the structural empty choice-block accumulator. -/
noncomputable def choiceBlockFoldBase : Polynomial Nat := Polynomial.C 100

/-- One choice index can add at most a quadratic-in-source-size marker. -/
noncomputable def choiceBlockFoldGrow : Polynomial Nat :=
  Polynomial.C 4 * (Polynomial.X * Polynomial.X) + Polynomial.C 20

@[simp] theorem choiceBlockFoldGrow_eval (bound : Nat) :
    choiceBlockFoldGrow.eval bound = 4 * (bound * bound) + 20 := by
  simp [choiceBlockFoldGrow, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

theorem choiceBlockInitialAccumulator_bound
    (source : List ChoiceBlockInstruction) :
    ChoiceBlockFoldInvariant
        (choiceBlockInstructionListEncoding.inputSize source)
        choiceBlockInitialAccumulator ∧
      choiceBlockAccumulatorEncoding.inputSize choiceBlockInitialAccumulator ≤
        choiceBlockFoldBase.eval (choiceBlockInstructionListEncoding.inputSize source) := by
  constructor
  · exact Or.inl rfl
  · simp only [choiceBlockFoldBase, Polynomial.eval_C]
    change (choiceBlockAccumulatorEncoding.encode choiceBlockInitialAccumulator).length ≤ 100
    decide

theorem choiceBlockStep_growth
    (source : List ChoiceBlockInstruction) (accumulator : ChoiceBlockAccumulator)
    (instruction : ChoiceBlockInstruction)
    (invariant : ChoiceBlockFoldInvariant
      (choiceBlockInstructionListEncoding.inputSize source) accumulator)
    (instructionBound : choiceBlockInstructionEncoding.inputSize instruction ≤
      choiceBlockInstructionListEncoding.inputSize source) :
    ChoiceBlockFoldInvariant
        (choiceBlockInstructionListEncoding.inputSize source)
        (choiceBlockStep (accumulator, instruction)) ∧
      choiceBlockAccumulatorEncoding.inputSize (choiceBlockStep (accumulator, instruction)) ≤
        choiceBlockAccumulatorEncoding.inputSize accumulator +
          choiceBlockFoldGrow.eval (choiceBlockInstructionListEncoding.inputSize source) := by
  let bound := choiceBlockInstructionListEncoding.inputSize source
  rcases accumulator with ⟨context, output⟩
  cases instruction with
  | inl newContext =>
      simp only [choiceBlockStep]
      have contextBound : choiceCodeContextEncoding.inputSize newContext ≤ bound := by
        change choiceBlockInstructionEncoding.inputSize
          (Sum.inl newContext : ChoiceBlockInstruction) ≤ bound at instructionBound
        exact (Nat.le_succ _).trans (by
          calc
            choiceCodeContextEncoding.inputSize newContext + 1 =
                choiceBlockInstructionEncoding.inputSize
                  (Sum.inl newContext : ChoiceBlockInstruction) :=
              (choiceBlockInstructionEncoding_inputSize_inl newContext).symm
            _ ≤ bound := instructionBound)
      constructor
      · exact Or.inr (Or.inr contextBound)
      · rcases newContext with ⟨vertices, colors, vertex, color⟩
        change choiceCodeContextEncoding.inputSize
          (vertices, (colors, (vertex, color))) ≤ bound at contextBound
        rw [choiceCodeContextEncoding_inputSize] at contextBound
        change choiceBlockAccumulatorEncoding.inputSize
          ((vertices, (colors, (vertex, color))), [vertex]) ≤
            choiceBlockAccumulatorEncoding.inputSize (context, output) +
              choiceBlockFoldGrow.eval bound
        calc
          choiceBlockAccumulatorEncoding.inputSize
              ((vertices, (colors, (vertex, color))), [vertex]) =
              choiceCodeContextEncoding.inputSize (vertices, (colors, (vertex, color))) +
                (EncodedType.list EncodedType.nat).inputSize [vertex] + 1 :=
            choiceBlockAccumulatorEncoding_inputSize _ _
          _ ≤ choiceCodeContextEncoding.inputSize context +
                (EncodedType.list EncodedType.nat).inputSize output + 1 +
                  choiceBlockFoldGrow.eval bound := by
              have singletonSize : (EncodedType.list EncodedType.nat).inputSize [vertex] =
                  vertex + 2 := by
                calc
                  (EncodedType.list EncodedType.nat).inputSize [vertex] =
                      (EncodedType.list EncodedType.nat).inputSize [] + vertex + 2 :=
                    natList_inputSize_append_singleton [] vertex
                  _ = vertex + 2 := by simp [EncodedType.inputSize, EncodedType.list]
              rw [choiceCodeContextEncoding_inputSize, singletonSize,
                choiceBlockFoldGrow_eval]
              nlinarith
          _ = choiceBlockAccumulatorEncoding.inputSize (context, output) +
                choiceBlockFoldGrow.eval bound := by
              rw [choiceBlockAccumulatorEncoding_inputSize]
  | inr edgeIndex =>
      simp only [choiceBlockStep]
      have indexBound : edgeIndex + 1 ≤ bound := by
        change choiceBlockInstructionEncoding.inputSize
          (Sum.inr edgeIndex : ChoiceBlockInstruction) ≤ bound at instructionBound
        exact (Nat.succ_le_succ (Nat.le_succ edgeIndex)).trans (by
          calc
            edgeIndex + 2 = choiceBlockInstructionEncoding.inputSize
                (Sum.inr edgeIndex : ChoiceBlockInstruction) :=
              (choiceBlockInstructionEncoding_inputSize_inr edgeIndex).symm
            _ ≤ bound := instructionBound)
      constructor
      · rcases invariant with initial | rest
        · injection initial with contextInitial _outputInitial
          exact Or.inr (Or.inl contextInitial)
        · exact Or.inr rest
      · simp only [choiceBlockAccumulatorEncoding, EncodedType.inputSize_prod]
        rw [
          natList_inputSize_append_singleton]
        rcases invariant with initial | rest
        · injection initial with contextInitial outputInitial
          subst context
          simp [choiceCodeFromContext, choiceBlockFoldGrow_eval]
          omega
        · rcases rest with zeroContext | contextBound
          · change context = (0, (0, (0, 0))) at zeroContext
            subst context
            simp [choiceCodeFromContext, choiceBlockFoldGrow_eval]
            omega
          · rcases context with ⟨vertices, colors, vertex, color⟩
            change choiceCodeContextEncoding.inputSize
              (vertices, (colors, (vertex, color))) ≤ bound at contextBound
            rw [choiceCodeContextEncoding_inputSize] at contextBound
            have edgeIndexBound : edgeIndex ≤ bound := by omega
            have colorCountBound : colors ≤ bound := by omega
            have productBound : edgeIndex * colors ≤ bound * bound :=
              Nat.mul_le_mul edgeIndexBound colorCountBound
            simp [choiceCodeFromContext, choiceBlockFoldGrow_eval]
            nlinarith

/-- Fold a closed instruction stream into its marker block. -/
def choiceBlockFromInstructions (instructions : List ChoiceBlockInstruction) : List Nat :=
  (instructions.foldl (fun accumulator instruction => choiceBlockStep (accumulator, instruction))
    choiceBlockInitialAccumulator).2

/-- Direct-TM realization of the complete bounded choice-block instruction fold. -/
theorem choiceBlockFold_tmPolyTime :
    TMPolyTimeMap choiceBlockInstructionListEncoding choiceBlockAccumulatorEncoding
      (fun instructions : List ChoiceBlockInstruction =>
        instructions.foldl (fun accumulator instruction => choiceBlockStep (accumulator, instruction))
          choiceBlockInitialAccumulator) := by
  rcases choiceBlockStep_tmPolyTime with ⟨stepTM⟩
  exact TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
    choiceBlockInstructionEncoding choiceBlockAccumulatorEncoding choiceBlockStep
    choiceBlockInitialAccumulator stepTM choiceBlockFoldBase choiceBlockFoldGrow
    ChoiceBlockFoldInvariant choiceBlockInitialAccumulator_bound choiceBlockStep_growth

/-- Direct-TM projection of the emitted markers from the completed choice-block fold. -/
theorem choiceBlockFromInstructions_tmPolyTime :
    TMPolyTimeMap choiceBlockInstructionListEncoding (EncodedType.list EncodedType.nat)
      choiceBlockFromInstructions := by
  have outputProjection := TMPolyTimeMap.snd choiceCodeContextEncoding
    (EncodedType.list EncodedType.nat)
  have composed := TMPolyTimeMap.comp outputProjection choiceBlockFold_tmPolyTime
  simpa [choiceBlockFromInstructions, Function.comp, choiceBlockAccumulatorEncoding] using composed

/-- The exact executable shape of one choice block. -/
def choiceBlockExecutable (argument : GraphColoringIR × (Nat × Nat)) : List Nat :=
  choiceBlockFromInstructions (choiceBlockInstructions argument)

/-- Direct-TM evidence for the exact executable choice block. -/
theorem choiceBlockExecutable_tmPolyTime :
    TMPolyTimeMap edgeColorCodeInputEncoding (EncodedType.list EncodedType.nat)
      choiceBlockExecutable := by
  have composed := TMPolyTimeMap.comp choiceBlockFromInstructions_tmPolyTime
    choiceBlockInstructions_tmPolyTime
  simpa [choiceBlockExecutable, Function.comp] using composed

private theorem choiceBlockIndexFold_eq_append_map
    (context : ChoiceCodeContext) (indices output : List Nat) :
    ((indices.map choiceBlockIndexInstruction).foldl
      (fun accumulator instruction => choiceBlockStep (accumulator, instruction))
      (context, output)).2 =
        output ++ indices.map (fun edgeIndex => choiceCodeFromContext (context, edgeIndex)) := by
  induction indices generalizing output with
  | nil => simp
  | cons edgeIndex indices inductionHypothesis =>
      rw [List.map_cons, List.foldl_cons]
      simp [choiceBlockIndexInstruction, choiceBlockStep]
      have tail := inductionHypothesis
        (output ++ [choiceCodeFromContext (context, edgeIndex)])
      simpa [List.append_assoc] using tail

/-- Bounded choice coordinates recover exactly the core ordered choice block. -/
theorem choiceBlockExecutable_eq_core {input : GraphColoringIR} {vertex color : Nat}
    (colorBound : color < input.colors) :
    choiceBlockExecutable (input, (vertex, color)) = choiceBlock input vertex color := by
  unfold choiceBlockExecutable choiceBlockFromInstructions choiceBlockInstructions
  simp only [List.foldl_cons, choiceBlockInitInstruction]
  change
    (((incidentEdgeIndicesExecutable (input, vertex)).map choiceBlockIndexInstruction).foldl
        (fun accumulator instruction => choiceBlockStep (accumulator, instruction))
        (choiceCodeContextOf (input, (vertex, color)), [vertex])).2 =
      choiceBlock input vertex color
  rw [choiceBlockIndexFold_eq_append_map]
  simp only [List.singleton_append]
  rw [incidentEdgeIndicesExecutable_eq_core]
  simp only [choiceBlock, vertexCode]
  congr 1
  apply List.map_congr_left
  intro edgeIndex edgeMember
  exact choiceCodeFromContext_eq_core
    ((mem_incidentEdgeIndices_iff input vertex edgeIndex).mp edgeMember).1 colorBound

/-- Direct-TM evidence for the canonical self-loop guard at the graph hub. -/
theorem graphHasSelfLoopBool_tmPolyTime :
    TMPolyTimeMap graphColoringEncoding EncodedType.bool graphHasSelfLoopBool := by
  have edgeBools :
      TMPolyTimeMap graphColoringEncoding (EncodedType.list EncodedType.bool)
        (fun input : GraphColoringIR => input.graph.edges.map edgeSelfLoopBool) := by
    have mapped := TMPolyTimeMap.list_map edgeSelfLoopBool_tmPolyTime
    have composed := TMPolyTimeMap.comp mapped edgeListProjection_tmPolyTime
    simpa [Function.comp, edgeListEncoding, GraphColoringIR.graph] using composed
  have executableTM := TMPolyTimeMap.comp boolListOr_tmPolyTime edgeBools
  convert executableTM using 1
  funext input
  exact (graphHasSelfLoopBoolExecutable_eq_core input).symm

/-! ### Graph-indexed rectangular coordinate families -/

/-- The exact shared codec for an ordered row-major edge/vertex coordinate family. -/
abbrev rectangularCoordinateListEncoding : EncodedType :=
  RectangularCoordinates.coordinateListEncodedType

/-- Retain the vertex and colour bounds needed by the choice-block coordinate family. -/
def choiceCoordinateContext (input : GraphColoringIR) : RectangularCoordinates.FamilyContext :=
  (input.graph.vertices, input.colors)

/-- Retain the stored-edge and colour bounds needed by the filler-block coordinate family. -/
def fillerCoordinateContext (input : GraphColoringIR) : RectangularCoordinates.FamilyContext :=
  (input.graph.edges.length, input.colors)

/-- The ordered `(vertex, colour)` coordinates at the canonical graph hub. -/
def choiceCoordinatesExecutable (input : GraphColoringIR) : List (Nat × Nat) :=
  RectangularCoordinates.familyExecutable (choiceCoordinateContext input)

/-- The ordered `(edgeIndex, colour)` coordinates at the canonical graph hub. -/
def fillerCoordinatesExecutable (input : GraphColoringIR) : List (Nat × Nat) :=
  RectangularCoordinates.familyExecutable (fillerCoordinateContext input)

/-- Direct-TM construction of the choice-family bounds from the canonical graph hub. -/
theorem choiceCoordinateContext_tmPolyTime :
    TMPolyTimeMap graphColoringEncoding RectangularCoordinates.familyContextEncodedType
      choiceCoordinateContext := by
  simpa [choiceCoordinateContext, RectangularCoordinates.familyContextEncodedType,
    RectangularCoordinates.coordinateEncodedType] using
    TMPolyTimeMap.prod_mk vertexCountProjection_tmPolyTime colorBoundProjection_tmPolyTime

/-- Direct-TM construction of the filler-family bounds from the canonical graph hub. -/
theorem fillerCoordinateContext_tmPolyTime :
    TMPolyTimeMap graphColoringEncoding RectangularCoordinates.familyContextEncodedType
      fillerCoordinateContext := by
  simpa [fillerCoordinateContext, RectangularCoordinates.familyContextEncodedType,
    RectangularCoordinates.coordinateEncodedType] using
    TMPolyTimeMap.prod_mk edgeCountProjection_tmPolyTime colorBoundProjection_tmPolyTime

/-- Direct-TM enumeration of all ordered choice coordinates. -/
theorem choiceCoordinatesExecutable_tmPolyTime :
    TMPolyTimeMap graphColoringEncoding rectangularCoordinateListEncoding
      choiceCoordinatesExecutable := by
  have composed := TMPolyTimeMap.comp
    RectangularCoordinates.familyExecutable_tmPolyTime choiceCoordinateContext_tmPolyTime
  simpa [choiceCoordinatesExecutable, Function.comp, rectangularCoordinateListEncoding] using composed

/-- Direct-TM enumeration of all ordered filler coordinates. -/
theorem fillerCoordinatesExecutable_tmPolyTime :
    TMPolyTimeMap graphColoringEncoding rectangularCoordinateListEncoding
      fillerCoordinatesExecutable := by
  have composed := TMPolyTimeMap.comp
    RectangularCoordinates.familyExecutable_tmPolyTime fillerCoordinateContext_tmPolyTime
  simpa [fillerCoordinatesExecutable, Function.comp, rectangularCoordinateListEncoding] using composed

/-- The choice-coordinate executable has the exact row-major source layout. -/
theorem choiceCoordinatesExecutable_eq_core (input : GraphColoringIR) :
    choiceCoordinatesExecutable input =
      (List.range input.graph.vertices).flatMap (fun vertex =>
        (List.range input.colors).map fun color => (vertex, color)) := by
  rw [choiceCoordinatesExecutable, RectangularCoordinates.familyExecutable_eq_flatMap]
  rfl

/-- The filler-coordinate executable has the exact row-major source layout. -/
theorem fillerCoordinatesExecutable_eq_core (input : GraphColoringIR) :
    fillerCoordinatesExecutable input =
      (List.range input.graph.edges.length).flatMap (fun edgeIndex =>
        (List.range input.colors).map fun color => (edgeIndex, color)) := by
  rw [fillerCoordinatesExecutable, RectangularCoordinates.familyExecutable_eq_flatMap]
  rfl

end GraphColoringToIncidence
end Domain
end ComplexityReduction
