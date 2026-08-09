/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.GraphColoringToIncidenceProgram
import ComplexityReduction.Domain.SetSystemMembershipPairs
import ComplexityReduction.Program.ContextListMap
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.BoolDispatch

/-!
Executable ordered block families for the canonical Graph-Coloring-to-
Incidence gadget.

The only source-dependent operation here is attaching the canonical
`GraphColoringIR` context to a coordinate list.  It is a generic checked fold
from `Program.ContextListMap`; no Chromatic Number or Exact Cover wrapper is
imported, and no route-local machine is introduced.
-/

namespace ComplexityReduction
namespace Domain
namespace GraphColoringToIncidence

open ComplexityReduction

/-- The direct-TM input layout for a graph hub together with ordered coordinates. -/
abbrev graphCoordinateListInputEncoding : EncodedType :=
  EncodedType.prod graphColoringEncoding rectangularCoordinateListEncoding

/-- The exact output layout after each coordinate retains its graph-hub context. -/
abbrev graphCoordinateListEncoding : EncodedType :=
  EncodedType.list edgeColorCodeInputEncoding

/-- Attach a canonical graph hub value to every coordinate in order. -/
def attachGraphToCoordinates
    (argument : GraphColoringIR × List (Nat × Nat)) :
    List (GraphColoringIR × (Nat × Nat)) :=
  show List (EncodedType.prod graphColoringEncoding
    RectangularCoordinates.coordinateEncodedType).Carrier from
    Program.contextListMapExecutable
      (C := graphColoringEncoding)
      (X := RectangularCoordinates.coordinateEncodedType)
      (show graphColoringEncoding.Carrier ×
        List RectangularCoordinates.coordinateEncodedType.Carrier from argument)

/-- The generic attachment fold has the exact expected map semantics. -/
theorem attachGraphToCoordinates_eq_map
    (input : GraphColoringIR) (coordinates : List (Nat × Nat)) :
    attachGraphToCoordinates (input, coordinates) =
      coordinates.map (fun coordinate => (input, coordinate)) := by
  exact Program.contextListMapExecutable_eq_map
    (C := graphColoringEncoding)
    (X := RectangularCoordinates.coordinateEncodedType) input coordinates

/-- Direct-TM realization of graph-context attachment. -/
theorem attachGraphToCoordinates_tmPolyTime :
    TMPolyTimeMap graphCoordinateListInputEncoding graphCoordinateListEncoding
      attachGraphToCoordinates := by
  simpa [attachGraphToCoordinates, graphCoordinateListInputEncoding,
    graphCoordinateListEncoding, rectangularCoordinateListEncoding,
    edgeColorCodeInputEncoding] using
    Program.contextListMapExecutable_tmPolyTime
      graphColoringEncoding RectangularCoordinates.coordinateEncodedType

/-! ### Choice blocks -/

/-- Construct all ordered choice blocks directly from the canonical graph hub. -/
def choiceBlocksExecutable (input : GraphColoringIR) : List (List Nat) :=
  (attachGraphToCoordinates (input, choiceCoordinatesExecutable input)).map
    choiceBlockExecutable

theorem choiceBlocksExecutable_tmPolyTime :
    TMPolyTimeMap graphColoringEncoding (EncodedType.list (EncodedType.list EncodedType.nat))
      choiceBlocksExecutable := by
  have coordinates : TMPolyTimeMap graphColoringEncoding graphCoordinateListInputEncoding
      (fun input : GraphColoringIR => (input, choiceCoordinatesExecutable input)) := by
    exact TMPolyTimeMap.prod_mk (TMPolyTimeMap.id graphColoringEncoding)
      choiceCoordinatesExecutable_tmPolyTime
  have attached : TMPolyTimeMap graphColoringEncoding graphCoordinateListEncoding
      (fun input : GraphColoringIR =>
        attachGraphToCoordinates (input, choiceCoordinatesExecutable input)) := by
    have composed := TMPolyTimeMap.comp attachGraphToCoordinates_tmPolyTime coordinates
    simpa [Function.comp] using composed
  have mapped := TMPolyTimeMap.list_map choiceBlockExecutable_tmPolyTime
  have composed := TMPolyTimeMap.comp mapped attached
  simpa [choiceBlocksExecutable, Function.comp, graphCoordinateListEncoding,
    edgeColorCodeInputEncoding] using composed

theorem choiceBlocksExecutable_eq_core (input : GraphColoringIR) :
    choiceBlocksExecutable input = choiceBlocks input := by
  rw [choiceBlocksExecutable, attachGraphToCoordinates_eq_map,
    choiceCoordinatesExecutable_eq_core]
  unfold choiceBlocks choiceBlocksForVertex
  simp only [List.map_flatMap, List.map_map]
  apply List.flatMap_congr
  intro vertex vertexMember
  apply List.map_congr_left
  intro color colorMember
  exact choiceBlockExecutable_eq_core (List.mem_range.mp colorMember)

/-! ### Filler blocks -/

/-- Construct all ordered filler blocks directly from the canonical graph hub. -/
def fillerBlocksExecutable (input : GraphColoringIR) : List (List Nat) :=
  (attachGraphToCoordinates (input, fillerCoordinatesExecutable input)).map
    fillerBlockExecutable

theorem fillerBlocksExecutable_tmPolyTime :
    TMPolyTimeMap graphColoringEncoding (EncodedType.list (EncodedType.list EncodedType.nat))
      fillerBlocksExecutable := by
  have coordinates : TMPolyTimeMap graphColoringEncoding graphCoordinateListInputEncoding
      (fun input : GraphColoringIR => (input, fillerCoordinatesExecutable input)) := by
    exact TMPolyTimeMap.prod_mk (TMPolyTimeMap.id graphColoringEncoding)
      fillerCoordinatesExecutable_tmPolyTime
  have attached : TMPolyTimeMap graphColoringEncoding graphCoordinateListEncoding
      (fun input : GraphColoringIR =>
        attachGraphToCoordinates (input, fillerCoordinatesExecutable input)) := by
    have composed := TMPolyTimeMap.comp attachGraphToCoordinates_tmPolyTime coordinates
    simpa [Function.comp] using composed
  have mapped := TMPolyTimeMap.list_map fillerBlockExecutable_tmPolyTime
  have composed := TMPolyTimeMap.comp mapped attached
  simpa [fillerBlocksExecutable, Function.comp, graphCoordinateListEncoding,
    edgeColorCodeInputEncoding] using composed

theorem fillerBlocksExecutable_eq_core (input : GraphColoringIR) :
    fillerBlocksExecutable input = fillerBlocks input := by
  rw [fillerBlocksExecutable, attachGraphToCoordinates_eq_map,
    fillerCoordinatesExecutable_eq_core]
  unfold fillerBlocks fillerBlocksForEdge
  simp only [List.map_flatMap, List.map_map]
  apply List.flatMap_congr
  intro edgeIndex edgeMember
  apply List.map_congr_left
  intro color colorMember
  exact fillerBlockExecutable_eq_core
    (List.mem_range.mp edgeMember) (List.mem_range.mp colorMember)

/-- The complete executable block family is the canonical ordered concatenation. -/
def blockFamilyExecutable (input : GraphColoringIR) : List (List Nat) :=
  choiceBlocksExecutable input ++ fillerBlocksExecutable input

theorem blockFamilyExecutable_tmPolyTime :
    TMPolyTimeMap graphColoringEncoding (EncodedType.list (EncodedType.list EncodedType.nat))
      blockFamilyExecutable := by
  have input : TMPolyTimeMap graphColoringEncoding
      (EncodedType.prod (EncodedType.list (EncodedType.list EncodedType.nat))
        (EncodedType.list (EncodedType.list EncodedType.nat)))
      (fun source : GraphColoringIR =>
        (choiceBlocksExecutable source, fillerBlocksExecutable source)) :=
    TMPolyTimeMap.prod_mk choiceBlocksExecutable_tmPolyTime fillerBlocksExecutable_tmPolyTime
  have composed := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append (EncodedType.list EncodedType.nat)) input
  simpa [blockFamilyExecutable, Function.comp] using composed

theorem blockFamilyExecutable_eq_core (input : GraphColoringIR) :
    blockFamilyExecutable input = blockFamily input := by
  simp [blockFamilyExecutable, blockFamily, choiceBlocksExecutable_eq_core,
    fillerBlocksExecutable_eq_core]

/-! ### Ordered incidence payload -/

/-- Emit ordered marker/right-vertex pairs from the complete executable block family. -/
def membershipPairsExecutable (input : GraphColoringIR) : List (Nat × Nat) :=
  SetSystemMembershipPairs.fromSetFamily (blockFamilyExecutable input)

theorem membershipPairsExecutable_tmPolyTime :
    TMPolyTimeMap graphColoringEncoding
      SetSystemMembershipPairs.pairListEncodedType membershipPairsExecutable := by
  have composed := TMPolyTimeMap.comp SetSystemMembershipPairs.fromSetFamily_tmPolyTime
    blockFamilyExecutable_tmPolyTime
  simpa [membershipPairsExecutable, Function.comp,
    SetSystemMembershipPairs.setFamilyInputEncodedType] using composed

private theorem setSystemMembershipPairsFrom_eq_core :
    ∀ (start : Nat) (sets : List (List Nat)),
      SetSystemMembershipPairs.membershipPairsFrom start sets = membershipPairsFrom start sets
  | _start, [] => rfl
  | start, set :: sets => by
      simp [SetSystemMembershipPairs.membershipPairsFrom, membershipPairsFrom,
        setSystemMembershipPairsFrom_eq_core (start + 1) sets]

theorem membershipPairsExecutable_eq_core (input : GraphColoringIR) :
    membershipPairsExecutable input = membershipPairs input := by
  rw [membershipPairsExecutable,
    SetSystemMembershipPairs.fromSetFamily_eq_membershipPairsFrom,
    blockFamilyExecutable_eq_core]
  exact setSystemMembershipPairsFrom_eq_core 0 (blockFamily input)

/-! ### Guarded canonical incidence construction -/

/-- The exact canonical encoder for the graph-to-incidence target hub. -/
abbrev incidenceEncoding : EncodedType :=
  IncidenceIR.lawfulRepresentation.encodedType

/-- Direct-TM computation of the number of independently selectable blocks. -/
theorem blockFamilyLength_tmPolyTime :
    TMPolyTimeMap graphColoringEncoding EncodedType.nat
      (fun input : GraphColoringIR => (blockFamilyExecutable input).length) := by
  have composed := TMPolyTimeMap.comp
    (ComplexityReduction.Karp21.HittingSet.listLengthTMBackedMap
      (EncodedType.list EncodedType.nat)).tm_polytime
    blockFamilyExecutable_tmPolyTime
  simpa [Function.comp] using composed

/-- Assemble the non-self-loop branch at the canonical incidence hub. -/
def assembledIncidenceExecutable (input : GraphColoringIR) : IncidenceIR :=
  IncidenceIR.mk (universeSize input) (blockFamilyExecutable input).length
    (membershipPairsExecutable input)

theorem assembledIncidenceExecutable_tmPolyTime :
    TMPolyTimeMap graphColoringEncoding incidenceEncoding assembledIncidenceExecutable := by
  have payload : TMPolyTimeMap graphColoringEncoding
      (EncodedType.prod EncodedType.nat SetSystemMembershipPairs.pairListEncodedType)
      (fun input : GraphColoringIR =>
        ((blockFamilyExecutable input).length, membershipPairsExecutable input)) :=
    TMPolyTimeMap.prod_mk blockFamilyLength_tmPolyTime membershipPairsExecutable_tmPolyTime
  have full : TMPolyTimeMap graphColoringEncoding incidenceEncoding
      (fun input : GraphColoringIR =>
        (universeSize input,
          ((blockFamilyExecutable input).length, membershipPairsExecutable input))) :=
    TMPolyTimeMap.prod_mk universeSize_tmPolyTime payload
  simpa [assembledIncidenceExecutable, incidenceEncoding,
    IncidenceIR.lawfulRepresentation, IncidenceIR.mk,
    SetSystemMembershipPairs.pairListEncodedType] using full

theorem assembledIncidenceExecutable_eq_core (input : GraphColoringIR) :
    assembledIncidenceExecutable input =
      IncidenceIR.mk (universeSize input) (blockFamily input).length (membershipPairs input) := by
  simp [assembledIncidenceExecutable, blockFamilyExecutable_eq_core,
    membershipPairsExecutable_eq_core]

/-- The complete guarded direct executable of the shared canonical hub gadget. -/
def runExecutable (input : GraphColoringIR) : IncidenceIR :=
  match graphHasSelfLoopBool input with
  | true => noTarget
  | false => assembledIncidenceExecutable input

theorem runExecutable_tmPolyTime :
    TMPolyTimeMap graphColoringEncoding incidenceEncoding runExecutable := by
  let BranchInput := EncodedType.prod EncodedType.bool graphColoringEncoding
  have branchInput : TMPolyTimeMap graphColoringEncoding BranchInput
      (fun input : GraphColoringIR => (graphHasSelfLoopBool input, input)) :=
    TMPolyTimeMap.prod_mk graphHasSelfLoopBool_tmPolyTime
      (TMPolyTimeMap.id graphColoringEncoding)
  have noTargetBranch : TMPolyTimeMap graphColoringEncoding incidenceEncoding
      (fun _ : GraphColoringIR => noTarget) :=
    TMPolyTimeMap.const graphColoringEncoding incidenceEncoding noTarget
  have dispatched : TMPolyTimeMap BranchInput incidenceEncoding
      (fun input : Bool × GraphColoringIR =>
        match input.1 with
        | true => noTarget
        | false => assembledIncidenceExecutable input.2) := by
    simpa [BranchInput] using
      boolProduct_dispatch_tm_polytime graphColoringEncoding incidenceEncoding
        (fFalse := assembledIncidenceExecutable) (fTrue := fun _ => noTarget)
        assembledIncidenceExecutable_tmPolyTime noTargetBranch
  have composed := TMPolyTimeMap.comp dispatched branchInput
  simpa [runExecutable, Function.comp] using composed

theorem runExecutable_eq_core (input : GraphColoringIR) :
    runExecutable input = run input := by
  cases loop : graphHasSelfLoopBool input <;>
    simp [runExecutable, run, loop, assembledIncidenceExecutable_eq_core]

end GraphColoringToIncidence
end Domain
end ComplexityReduction
