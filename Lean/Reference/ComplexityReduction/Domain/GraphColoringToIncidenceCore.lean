/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.Core.GraphColoringIR
import ComplexityReduction.Domain.Core.IncidenceIR

/-!
Wrapper-independent semantic construction for the Graph-Coloring-to-Incidence
component boundary.

This module deliberately contains only the finite combinatorial construction
at the two canonical hubs.  In particular it does not import
`ChromaticNumberInput`, `ExactCoverInput`, the legacy Exact-Cover assembly,
Program, Certificate, route, registry, or Legacy APIs.  A later companion
must prove its semantic iff and supply a standard direct-TM realization before
this executable can inhabit a trusted `PolyProg` or `CertifiedReduction`.
-/

namespace ComplexityReduction
namespace Domain
namespace GraphColoringToIncidence

open ComplexityReduction.Combinatorics.Graph

/-- The ordered edge/colour coordinates used for the private edge markers. -/
def edgeColorPairs (input : GraphColoringIR) : List (Nat × Nat) :=
  List.range input.graph.edges.length ×ˢ List.range input.colors

/-- The private marker of one source vertex. -/
def vertexCode (_input : GraphColoringIR) (vertex : Nat) : Nat :=
  vertex

/--
The private marker for one indexed edge/colour coordinate.

The `idxOf` layout deliberately follows the ordered product above.  It keeps
the semantic construction aligned with the finite coordinate list while a
future direct-TM companion owns the corresponding executable lookup proof.
-/
def edgeColorCode (input : GraphColoringIR) (edgeIndex color : Nat) : Nat :=
  input.graph.vertices + (edgeColorPairs input).idxOf (edgeIndex, color)

/-- The total marker universe of the construction. -/
def universeSize (input : GraphColoringIR) : Nat :=
  input.graph.vertices + (edgeColorPairs input).length

/-- Total edge lookup used only after a corresponding range-bound guard. -/
def edgeAt (input : GraphColoringIR) (edgeIndex : Nat) : Nat × Nat :=
  input.graph.edges.getD edgeIndex (0, 0)

/-- Proposition-valued incidence of one vertex with one indexed edge. -/
def EdgeIncident (input : GraphColoringIR) (edgeIndex vertex : Nat) : Prop :=
  (edgeAt input edgeIndex).1 = vertex ∨ (edgeAt input edgeIndex).2 = vertex

/-- The finite edge-incidence predicate is decidable at the canonical graph hub. -/
instance edgeIncidentDecidable (input : GraphColoringIR) (edgeIndex vertex : Nat) :
    Decidable (EdgeIncident input edgeIndex vertex) := by
  unfold EdgeIncident
  infer_instance

/-- Decidable incidence of one vertex with one indexed edge. -/
def edgeIncidentBool (input : GraphColoringIR) (edgeIndex vertex : Nat) : Bool :=
  decide (EdgeIncident input edgeIndex vertex)

/-- All edge indices incident with one vertex, in their original order. -/
def incidentEdgeIndices (input : GraphColoringIR) (vertex : Nat) : List Nat :=
  (List.range input.graph.edges.length).filter (fun edgeIndex =>
    edgeIncidentBool input edgeIndex vertex)

/-- The block selecting one colour for one source vertex. -/
def choiceBlock (input : GraphColoringIR) (vertex color : Nat) : List Nat :=
  vertexCode input vertex ::
    (incidentEdgeIndices input vertex).map (fun edgeIndex => edgeColorCode input edgeIndex color)

/-- The singleton filler for an uncovered edge/colour coordinate. -/
def fillerBlock (input : GraphColoringIR) (edgeIndex color : Nat) : List Nat :=
  [edgeColorCode input edgeIndex color]

/-- All colour-choice blocks for one source vertex. -/
def choiceBlocksForVertex (input : GraphColoringIR) (vertex : Nat) : List (List Nat) :=
  (List.range input.colors).map (fun color => choiceBlock input vertex color)

/-- The ordered family of all vertex-colour choice blocks. -/
def choiceBlocks (input : GraphColoringIR) : List (List Nat) :=
  (List.range input.graph.vertices).flatMap (choiceBlocksForVertex input)

/-- All filler blocks for one indexed edge. -/
def fillerBlocksForEdge (input : GraphColoringIR) (edgeIndex : Nat) : List (List Nat) :=
  (List.range input.colors).map (fun color => fillerBlock input edgeIndex color)

/-- The ordered family of all edge-colour filler blocks. -/
def fillerBlocks (input : GraphColoringIR) : List (List Nat) :=
  (List.range input.graph.edges.length).flatMap (fillerBlocksForEdge input)

/-- The complete ordered block family of the canonical graph-colouring construction. -/
def blockFamily (input : GraphColoringIR) : List (List Nat) :=
  choiceBlocks input ++ fillerBlocks input

/-- Emit the incidence pairs of an ordered suffix of blocks. -/
def membershipPairsFrom : Nat → List (List Nat) → List (Nat × Nat)
  | _index, [] => []
  | index, block :: blocks =>
      block.map (fun marker => (marker, index)) ++ membershipPairsFrom (index + 1) blocks

/-- Preserve the ordered membership occurrences of the entire constructed block family. -/
def membershipPairs (input : GraphColoringIR) : List (Nat × Nat) :=
  membershipPairsFrom 0 (blockFamily input)

/-- A fixed canonical incidence instance with one uncovered left vertex. -/
def noTarget : IncidenceIR :=
  IncidenceIR.mk 1 0 []

/-- The source graph contains an explicitly represented self-loop. -/
def GraphHasSelfLoop (input : GraphColoringIR) : Prop :=
  ∃ edge ∈ input.graph.edges, edge.1 = edge.2

/-- The fixed self-loop target cannot have an exact cover because it has no right vertex. -/
theorem noTarget_not_exactCover : ¬ IncidenceIR.ExistsExactCover noTarget := by
  rintro ⟨_wellFormed, _selected, _selectedNodup, covers⟩
  let left : IncidenceIR.LeftVertex noTarget := ⟨0, by decide⟩
  rcases covers left with ⟨right, _rightWitness, _rightUnique⟩
  exact Nat.not_lt_zero right.val (by
    simpa [noTarget, IncidenceIR.mk, IncidenceIR.rightSize] using right.isLt)

/-- Detect a self-loop without referring to a concrete Chromatic Number wrapper. -/
def graphHasSelfLoopBool (input : GraphColoringIR) : Bool :=
  input.graph.edges.any (fun edge => decide (edge.1 = edge.2))

/--
The wrapper-independent executable at the Graph-Coloring/Incidence boundary.

For a self-loop it emits the fixed no-instance; otherwise it turns the ordered
colour blocks directly into the canonical incidence table, retaining block
indices as distinct right vertices.
-/
def run (input : GraphColoringIR) : IncidenceIR :=
  match graphHasSelfLoopBool input with
  | true => noTarget
  | false =>
      IncidenceIR.mk (universeSize input) (blockFamily input).length (membershipPairs input)

@[simp] theorem run_of_graphHasSelfLoopBool_true (input : GraphColoringIR)
    (selfLoop : graphHasSelfLoopBool input = true) :
    run input = noTarget := by
  simp [run, selfLoop]

@[simp] theorem run_of_graphHasSelfLoopBool_false (input : GraphColoringIR)
    (noSelfLoop : graphHasSelfLoopBool input = false) :
    run input =
      IncidenceIR.mk (universeSize input) (blockFamily input).length (membershipPairs input) := by
  simp [run, noSelfLoop]

@[simp] theorem constructed_leftSize (input : GraphColoringIR)
    (noSelfLoop : graphHasSelfLoopBool input = false) :
    (run input).leftSize = universeSize input := by
  rw [run_of_graphHasSelfLoopBool_false input noSelfLoop]
  rfl

@[simp] theorem constructed_rightSize (input : GraphColoringIR)
    (noSelfLoop : graphHasSelfLoopBool input = false) :
    (run input).rightSize = (blockFamily input).length := by
  rw [run_of_graphHasSelfLoopBool_false input noSelfLoop]
  rfl

@[simp] theorem constructed_membershipPairs (input : GraphColoringIR)
    (noSelfLoop : graphHasSelfLoopBool input = false) :
    (run input).membershipPairs = membershipPairs input := by
  rw [run_of_graphHasSelfLoopBool_false input noSelfLoop]
  rfl

end GraphColoringToIncidence
end Domain
end ComplexityReduction
