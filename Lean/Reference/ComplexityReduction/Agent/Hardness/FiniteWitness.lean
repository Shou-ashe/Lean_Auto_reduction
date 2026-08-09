/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Encoding.StandardInstances

/-!
Small, proof-relevant finite-witness combinators used by typed optional
authoring.  These definitions do not construct a verifier, TM, membership
certificate, or reduction.  They provide only reusable witness shapes and
local decidable predicates; a `CertifiedVerifier` must still supply its exact
program, polynomial bound, completeness, soundness, and encoding discipline.
-/

namespace ComplexityReduction.Agent.Hardness.FiniteWitness

open ComplexityReduction.Encoding

/-- Canonical structural presentation for a list of unary natural numbers. -/
abbrev natListPresentation : LawfulEncodedType :=
  StandardInstances.list StandardInstances.unaryNat

/-- The canonical empty nat-list has zero size, using only the standard lawful list theorem. -/
theorem natListEncodedInputSize_nil :
    natListPresentation.encodedType.inputSize ([] : List Nat) = 0 :=
  StandardInstances.inputSize_list_nil StandardInstances.unaryNat

/-- Structural admission for the exact `List Nat` witness presentation. -/
def natListStructuralCertificate : natListPresentation.StructuralCertificate :=
  StandardInstances.listStructuralCertificate StandardInstances.unaryNat
    StandardInstances.unaryNatStructuralCertificate

/-- Every selected index lies below the instance-local vertex/item bound. -/
def VerticesWithinBounds (upper : Nat) (vertices : List Nat) : Prop :=
  ∀ vertex, vertex ∈ vertices → vertex < upper

/-- A standard bounded-subset witness: no duplicates, in bounds, and within budget. -/
def BoundedSubset (upper budget : Nat) (vertices : List Nat) : Prop :=
  vertices.Nodup ∧ VerticesWithinBounds upper vertices ∧ vertices.length ≤ budget

/-- Boolean local bound checker used by packet-index metadata and executable fixtures. -/
def verticesWithinBoundsChecker (upper : Nat) (vertices : List Nat) : Bool :=
  vertices.all fun vertex => decide (vertex < upper)

/-- Boolean cardinality/budget checker for a finite list witness. -/
def cardinalityBudgetChecker (budget : Nat) (vertices : List Nat) : Bool :=
  decide (vertices.length ≤ budget)

/-- A canonical view of one list as an ordered pair of list witnesses. -/
structure PairListView where
  left : List Nat
  right : List Nat
  deriving DecidableEq, Repr

/-- Split alternating entries into the two ordered components of a pair witness. -/
def pairListView : List Nat → PairListView
  | [] => ⟨[], []⟩
  | first :: [] => ⟨[first], []⟩
  | first :: second :: rest =>
      let tail := pairListView rest
      ⟨first :: tail.left, second :: tail.right⟩

/-- The two components of a pair/list witness share no selected index. -/
def PairListDisjoint (witness : List Nat) : Prop :=
  let pair := pairListView witness
  ∀ vertex, vertex ∈ pair.left → vertex ∉ pair.right

/-- Boolean disjointness checker for the canonical alternating pair/list view. -/
def pairListDisjointChecker (witness : List Nat) : Bool :=
  let pair := pairListView witness
  pair.left.all fun vertex => !(pair.right.contains vertex)

/-- A small undirected graph edge representation used by local checker packets. -/
abbrev Edge := Nat × Nat

/-- Local undirected adjacency over an explicit finite edge list. -/
def Adjacent (edges : List Edge) (left right : Nat) : Prop :=
  (left, right) ∈ edges ∨ (right, left) ∈ edges

/-- Boolean local edge/adjacency checker. -/
def adjacencyChecker (edges : List Edge) (left right : Nat) : Bool :=
  edges.contains (left, right) || edges.contains (right, left)

/-- Every graph edge has at least one endpoint in the selected cover. -/
def CoversEdges (edges : List Edge) (cover : List Nat) : Prop :=
  ∀ edge, edge ∈ edges → edge.1 ∈ cover ∨ edge.2 ∈ cover

/-- Boolean local cover checker. -/
def coverChecker (edges : List Edge) (cover : List Nat) : Bool :=
  edges.all fun edge => cover.contains edge.1 || cover.contains edge.2

/-- Adjacent vertices receive different colors from a total local coloring. -/
def ColoringLegal (edges : List Edge) (color : Nat → Nat) : Prop :=
  ∀ edge, edge ∈ edges → color edge.1 ≠ color edge.2

/-- Boolean local coloring checker for a supplied color function. -/
def coloringChecker (edges : List Edge) (color : Nat → Nat) : Bool :=
  edges.all fun edge => color edge.1 != color edge.2

/-!
### Finite deletion-and-coloring witnesses

The value `2` marks a deleted vertex; values `0` and `1` are the two colors
of surviving vertices.  This single finite list therefore replaces the
non-encodable legacy witness `(deleted : List Nat) × (Nat → Bool)`.
-/

/-- The distinguished finite-witness value denoting a deleted item. -/
def deletionMarker : Nat := 2

/-- Read one finite deletion/color value, treating an out-of-range index as deleted. -/
def deletionColorValue (assignment : List Nat) (vertex : Nat) : Nat :=
  assignment.getD vertex deletionMarker

/-- Every stored value is either one of two colors or the deletion marker. -/
def DeletionColorValuesLegal (assignment : List Nat) : Prop :=
  ∀ value, value ∈ assignment → value < 3

/-- One edge is legal when an endpoint is deleted or its surviving colors differ. -/
def DeletionColorEdgeLegal (assignment : List Nat) (edge : Edge) : Prop :=
  deletionColorValue assignment edge.1 = deletionMarker ∨
    deletionColorValue assignment edge.2 = deletionMarker ∨
    deletionColorValue assignment edge.1 ≠ deletionColorValue assignment edge.2

/--
A canonical finite deletion-and-two-coloring witness.  Its length fixes the
instance-local universe, all entries use the three-value alphabet, no more
than `budget` entries are deleted, and every explicit edge is legal.
-/
def DeletionColoring
    (upper budget : Nat) (edges : List Edge) (assignment : List Nat) : Prop :=
  assignment.length = upper ∧
    DeletionColorValuesLegal assignment ∧
    assignment.count deletionMarker ≤ budget ∧
    ∀ edge, edge ∈ edges → DeletionColorEdgeLegal assignment edge

/-- Executable local checker for the canonical finite deletion/coloring witness. -/
def deletionColoringChecker
    (upper budget : Nat) (edges : List Edge) (assignment : List Nat) : Bool :=
  decide (assignment.length = upper) &&
    assignment.all (fun value => decide (value < 3)) &&
    decide (assignment.count deletionMarker ≤ budget) &&
    edges.all fun edge =>
      decide (deletionColorValue assignment edge.1 = deletionMarker) ||
        decide (deletionColorValue assignment edge.2 = deletionMarker) ||
        decide
          (deletionColorValue assignment edge.1 ≠
            deletionColorValue assignment edge.2)

theorem deletionColoringChecker_eq_true_iff
    (upper budget : Nat) (edges : List Edge) (assignment : List Nat) :
    deletionColoringChecker upper budget edges assignment = true ↔
      DeletionColoring upper budget edges assignment := by
  simp [deletionColoringChecker, DeletionColoring, DeletionColorValuesLegal,
    DeletionColorEdgeLegal, and_assoc, or_assoc]

/-- Consecutive vertices of a path are adjacent in the supplied graph. -/
def PathLegal (edges : List Edge) (path : List Nat) : Prop :=
  path.Pairwise fun left right => Adjacent edges left right

/-- Boolean path-legality checker over adjacent entries. -/
def pathLegalityChecker (edges : List Edge) : List Nat → Bool
  | [] | [_] => true
  | left :: right :: rest =>
      adjacencyChecker edges left right && pathLegalityChecker edges (right :: rest)

/-- Natural-number list sum used by budgeted witness packets. -/
def listSum (values : List Nat) : Nat :=
  values.foldl (· + ·) 0

/-- Natural-number budget checker. -/
def natBudgetChecker (budget : Nat) (values : List Nat) : Bool :=
  decide (listSum values ≤ budget)

/-- Integer budget checker, retaining signed local costs without coercing to naturals. -/
def intBudgetChecker (budget : Int) (values : List Int) : Bool :=
  decide (values.foldl (· + ·) 0 ≤ budget)

/-- Apply one decidable local predicate to every element of a finite witness. -/
def localPredicateChecker (predicate : Nat → Bool) (values : List Nat) : Bool :=
  values.all predicate

@[simp] theorem pairListView_nil : pairListView [] = ⟨[], []⟩ := rfl

@[simp] theorem pathLegalityChecker_nil (edges : List Edge) :
    pathLegalityChecker edges [] = true := rfl

@[simp] theorem listSum_nil : listSum [] = 0 := rfl

end ComplexityReduction.Agent.Hardness.FiniteWitness
