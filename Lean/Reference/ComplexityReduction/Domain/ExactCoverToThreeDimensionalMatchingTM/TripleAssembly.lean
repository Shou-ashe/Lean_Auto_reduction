/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Domain.ExactCoverToThreeDimensionalMatchingTM.Foundations
import ComplexityReduction.Program.ContextListMap
import ComplexityReduction.Program.List

/-!
Executable triple and structured-payload assembly for the compact
Exact-Cover-to-Three-Dimensional-Matching map.

Every variable-length family below is produced by the checked unary range,
context-map, ordinary list-map, and bounded flatten/fold machines.  The only
representation transport is the final identity machine from the nested
structured payload to the existing five-field `ThreeDimensionalMatchingInput`
wrapper; the two encoders are definitionally the same word layout.
-/

namespace ComplexityReduction
namespace Domain
namespace ExactCoverToThreeDimensionalMatchingTM
namespace TripleAssembly

open ComplexityReduction.Combinatorics
open ComplexityReduction.Karp21
open ComplexityReduction.Karp21.ThreeDimensionalMatching
open Foundations

abbrev natListEncodedType : EncodedType := EncodedType.list EncodedType.nat

abbrev indexedMemberEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.nat

abbrev indexedMemberListEncodedType : EncodedType :=
  EncodedType.list indexedMemberEncodedType

abbrev sourceIndexInputEncodedType : EncodedType :=
  EncodedType.prod exactCoverStructuredEncodedType EncodedType.nat

abbrev sourceIndexedMemberEncodedType : EncodedType :=
  EncodedType.prod exactCoverStructuredEncodedType indexedMemberEncodedType

abbrev sourceBetaEncodedType : EncodedType :=
  EncodedType.prod exactCoverStructuredEncodedType EncodedType.nat

abbrev fillerInputEncodedType : EncodedType :=
  EncodedType.prod sourceBetaEncodedType indexedMemberEncodedType

abbrev tripleEncodedType : EncodedType := tripleStructuredEncodedType

abbrev tripleListEncodedType : EncodedType := tripleListStructuredEncodedType

/-!
The generic context-map theorem exposes its product carrier through a
dependent `show`.  These three typed views keep later list algebra entirely
in the ordinary product types used by the legacy definitions.
-/

private theorem exactCoverNatContextMap_eq_map
    (I : ExactCoverInput) (values : List Nat) :
    Program.contextListMapExecutable
        (C := exactCoverStructuredEncodedType) (X := EncodedType.nat)
        (I, values) =
      values.map (fun value => (I, value)) := by
  rw [Program.contextListMapExecutable_eq_map]
  rfl

private theorem exactCoverIndexedMemberContextMap_eq_map
    (I : ExactCoverInput) (values : List (Nat × Nat)) :
    Program.contextListMapExecutable
        (C := exactCoverStructuredEncodedType) (X := indexedMemberEncodedType)
        (I, values) =
      values.map (fun value => (I, value)) := by
  rw [Program.contextListMapExecutable_eq_map]
  rfl

private theorem sourceBetaIndexedMemberContextMap_eq_map
    (input : ExactCoverInput × Nat) (values : List (Nat × Nat)) :
    Program.contextListMapExecutable
        (C := sourceBetaEncodedType) (X := indexedMemberEncodedType)
        (input, values) =
      values.map (fun value => (input, value)) := by
  rw [Program.contextListMapExecutable_eq_map]
  rfl

/-! ### Ordered bounded support pairs -/

/-- Attach a fixed family index to every bounded member of that source set. -/
def supportPairBlockExecutable (input : ExactCoverInput × Nat) : List (Nat × Nat) :=
  Program.contextListMapExecutable
    (C := EncodedType.nat) (X := EncodedType.nat)
    (input.2,
      compactSupportExecutable
        (input.1, sourceSetAtExecutable input))

theorem supportPairBlockExecutable_eq_legacy (I : ExactCoverInput) (j : Nat) :
    supportPairBlockExecutable (I, j) =
      (compactSupport I (compactSourceSetAt I j)).map (fun x => (j, x)) := by
  rw [supportPairBlockExecutable, Program.contextListMapExecutable_eq_map]
  rw [compactSupportExecutable_eq_legacy, sourceSetAtExecutable_eq_legacy]
  rfl

theorem supportPairBlockExecutable_tmPolyTime :
    TMPolyTimeMap sourceIndexInputEncodedType indexedMemberListEncodedType
      supportPairBlockExecutable := by
  let X := sourceIndexInputEncodedType
  have source : TMPolyTimeMap X exactCoverStructuredEncodedType
      (fun input : ExactCoverInput × Nat => input.1) := by
    simpa [X, sourceIndexInputEncodedType] using
      TMPolyTimeMap.fst exactCoverStructuredEncodedType EncodedType.nat
  have index : TMPolyTimeMap X EncodedType.nat
      (fun input : ExactCoverInput × Nat => input.2) := by
    simpa [X, sourceIndexInputEncodedType] using
      TMPolyTimeMap.snd exactCoverStructuredEncodedType EncodedType.nat
  have sourceSet : TMPolyTimeMap X setStructuredEncodedType
      (fun input : ExactCoverInput × Nat => sourceSetAtExecutable input) := by
    simpa [X, sourceIndexInputEncodedType] using sourceSetAtExecutable_tmPolyTime
  have supportInput : TMPolyTimeMap X supportInputEncodedType
      (fun input : ExactCoverInput × Nat =>
        (input.1, sourceSetAtExecutable input)) :=
    TMPolyTimeMap.prod_mk source sourceSet
  have support : TMPolyTimeMap X natListEncodedType
      (fun input : ExactCoverInput × Nat =>
        compactSupportExecutable (input.1, sourceSetAtExecutable input)) := by
    have composed := TMPolyTimeMap.comp compactSupportExecutable_tmPolyTime supportInput
    simpa [Function.comp, X, natListEncodedType] using composed
  have attachInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat natListEncodedType)
      (fun input : ExactCoverInput × Nat =>
        (input.2,
          compactSupportExecutable (input.1, sourceSetAtExecutable input))) :=
    TMPolyTimeMap.prod_mk index support
  have composed := TMPolyTimeMap.comp
    (Program.contextListMapExecutable_tmPolyTime EncodedType.nat EncodedType.nat)
    attachInput
  simpa [supportPairBlockExecutable, Function.comp, indexedMemberEncodedType,
    indexedMemberListEncodedType, natListEncodedType, X] using composed

/-- Enumerate `(setIndex, element)` in the legacy outer-index/inner-support order. -/
def supportPairsExecutable (I : ExactCoverInput) : List (Nat × Nat) :=
  List.flatten
    ((Program.contextListMapExecutable
        (C := exactCoverStructuredEncodedType) (X := EncodedType.nat)
        (I, List.range (setCountExecutable I))).map supportPairBlockExecutable)

theorem supportPairsExecutable_eq_legacy (I : ExactCoverInput) :
    supportPairsExecutable I =
      (List.range I.system.sets.length).flatMap (fun j =>
        (compactSupport I (compactSourceSetAt I j)).map (fun x => (j, x))) := by
  rw [supportPairsExecutable, exactCoverNatContextMap_eq_map,
    setCountExecutable_eq, List.map_map]
  change
    (List.map (fun j => supportPairBlockExecutable (I, j))
      (List.range I.system.sets.length)).flatten =
      (List.map (fun j =>
        (compactSupport I (compactSourceSetAt I j)).map (fun x => (j, x)))
        (List.range I.system.sets.length)).flatten
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j _
  exact supportPairBlockExecutable_eq_legacy I j

theorem supportPairsExecutable_tmPolyTime :
    TMPolyTimeMap exactCoverStructuredEncodedType indexedMemberListEncodedType
      supportPairsExecutable := by
  let X := exactCoverStructuredEncodedType
  let IndexedSource := sourceIndexInputEncodedType
  let IndexedSources := EncodedType.list IndexedSource
  let Blocks := EncodedType.list indexedMemberListEncodedType
  have count : TMPolyTimeMap X EncodedType.nat setCountExecutable := by
    simpa [X] using setCountExecutable_tmPolyTime
  have indices : TMPolyTimeMap X natListEncodedType
      (fun I : ExactCoverInput => List.range (setCountExecutable I)) := by
    have composed := TMPolyTimeMap.comp Karp21.natRange_tm_polytime count
    simpa [Function.comp, X, natListEncodedType] using composed
  have attachInput : TMPolyTimeMap X
      (EncodedType.prod exactCoverStructuredEncodedType natListEncodedType)
      (fun I : ExactCoverInput => (I, List.range (setCountExecutable I))) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id X) indices
  have indexedSources : TMPolyTimeMap X IndexedSources
      (fun I : ExactCoverInput =>
        Program.contextListMapExecutable
          (C := exactCoverStructuredEncodedType) (X := EncodedType.nat)
          (I, List.range (setCountExecutable I))) := by
    have composed := TMPolyTimeMap.comp
      (Program.contextListMapExecutable_tmPolyTime
        exactCoverStructuredEncodedType EncodedType.nat)
      attachInput
    simpa [Function.comp, IndexedSource, IndexedSources, X,
      sourceIndexInputEncodedType, natListEncodedType] using composed
  have blocks : TMPolyTimeMap X Blocks
      (fun I : ExactCoverInput =>
        (Program.contextListMapExecutable
          (C := exactCoverStructuredEncodedType) (X := EncodedType.nat)
          (I, List.range (setCountExecutable I))).map supportPairBlockExecutable) := by
    have mapped := TMPolyTimeMap.list_map supportPairBlockExecutable_tmPolyTime
    have composed := TMPolyTimeMap.comp mapped indexedSources
    simpa [Function.comp, Blocks, IndexedSources, indexedMemberListEncodedType, X] using composed
  have flattened := TMPolyTimeMap.comp
    (Program.listFlatten_tmPolyTime indexedMemberEncodedType) blocks
  simpa [supportPairsExecutable, Function.comp, Blocks, indexedMemberListEncodedType,
    X] using flattened

/-! ### Cover triples -/

/-- Executable `<alpha(x), <x,j>, <x,j>>` for one indexed member. -/
def coverTripleExecutable (input : ExactCoverInput × (Nat × Nat)) :
    Nat × Nat × Nat :=
  (alphaCodeExecutable (input.1, input.2.2),
    positionCodeExecutable (input.1, (input.2.2, input.2.1)),
    positionCodeExecutable (input.1, (input.2.2, input.2.1)))

theorem coverTripleExecutable_eq_legacy (I : ExactCoverInput) (j x : Nat) :
    coverTripleExecutable (I, (j, x)) = compactCoverTriple I x j := by
  simp [coverTripleExecutable, compactCoverTriple,
    alphaCodeExecutable_eq_legacy, positionCodeExecutable_eq_legacy]

theorem coverTripleExecutable_tmPolyTime :
    TMPolyTimeMap sourceIndexedMemberEncodedType tripleEncodedType
      coverTripleExecutable := by
  let X := sourceIndexedMemberEncodedType
  have source : TMPolyTimeMap X exactCoverStructuredEncodedType
      (fun input : ExactCoverInput × (Nat × Nat) => input.1) := by
    simpa [X, sourceIndexedMemberEncodedType] using
      TMPolyTimeMap.fst exactCoverStructuredEncodedType indexedMemberEncodedType
  have member : TMPolyTimeMap X indexedMemberEncodedType
      (fun input : ExactCoverInput × (Nat × Nat) => input.2) := by
    simpa [X, sourceIndexedMemberEncodedType] using
      TMPolyTimeMap.snd exactCoverStructuredEncodedType indexedMemberEncodedType
  have index : TMPolyTimeMap X EncodedType.nat
      (fun input : ExactCoverInput × (Nat × Nat) => input.2.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst EncodedType.nat EncodedType.nat) member
    simpa [Function.comp, X, indexedMemberEncodedType] using composed
  have element : TMPolyTimeMap X EncodedType.nat
      (fun input : ExactCoverInput × (Nat × Nat) => input.2.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd EncodedType.nat EncodedType.nat) member
    simpa [Function.comp, X, indexedMemberEncodedType] using composed
  have alphaInput : TMPolyTimeMap X elementInputEncodedType
      (fun input : ExactCoverInput × (Nat × Nat) => (input.1, input.2.2)) :=
    TMPolyTimeMap.prod_mk source element
  have alpha : TMPolyTimeMap X EncodedType.nat
      (fun input : ExactCoverInput × (Nat × Nat) =>
        alphaCodeExecutable (input.1, input.2.2)) := by
    have composed := TMPolyTimeMap.comp alphaCodeExecutable_tmPolyTime alphaInput
    simpa [Function.comp, X] using composed
  have coordinates : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : ExactCoverInput × (Nat × Nat) => (input.2.2, input.2.1)) :=
    TMPolyTimeMap.prod_mk element index
  have positionInput : TMPolyTimeMap X positionCodeInputEncodedType
      (fun input : ExactCoverInput × (Nat × Nat) =>
        (input.1, (input.2.2, input.2.1))) :=
    TMPolyTimeMap.prod_mk source coordinates
  have position : TMPolyTimeMap X EncodedType.nat
      (fun input : ExactCoverInput × (Nat × Nat) =>
        positionCodeExecutable (input.1, (input.2.2, input.2.1))) := by
    have composed := TMPolyTimeMap.comp positionCodeExecutable_tmPolyTime positionInput
    simpa [Function.comp, X] using composed
  have tail : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : ExactCoverInput × (Nat × Nat) =>
        (positionCodeExecutable (input.1, (input.2.2, input.2.1)),
          positionCodeExecutable (input.1, (input.2.2, input.2.1)))) :=
    TMPolyTimeMap.prod_mk position position
  simpa [coverTripleExecutable, tripleEncodedType, tripleStructuredEncodedType, X] using
    TMPolyTimeMap.prod_mk alpha tail

/-- Ordered executable cover-triple family. -/
def coverTriplesExecutable (I : ExactCoverInput) : List (Nat × Nat × Nat) :=
  (Program.contextListMapExecutable
      (C := exactCoverStructuredEncodedType) (X := indexedMemberEncodedType)
      (I, supportPairsExecutable I)).map
    coverTripleExecutable

theorem coverTriplesExecutable_eq_legacy (I : ExactCoverInput) :
    coverTriplesExecutable I = compactCoverTriples I := by
  rw [coverTriplesExecutable, exactCoverIndexedMemberContextMap_eq_map,
    List.map_map, supportPairsExecutable_eq_legacy, List.map_flatMap]
  simp only [List.map_map]
  unfold compactCoverTriples compactCoverTriplesForSet
  apply List.flatMap_congr
  intro j _
  apply List.map_congr_left
  intro x _
  exact coverTripleExecutable_eq_legacy I j x

theorem coverTriplesExecutable_tmPolyTime :
    TMPolyTimeMap exactCoverStructuredEncodedType tripleListEncodedType
      coverTriplesExecutable := by
  let X := exactCoverStructuredEncodedType
  let Attached := EncodedType.list sourceIndexedMemberEncodedType
  have pairs : TMPolyTimeMap X indexedMemberListEncodedType supportPairsExecutable := by
    simpa [X] using supportPairsExecutable_tmPolyTime
  have attachInput : TMPolyTimeMap X
      (EncodedType.prod exactCoverStructuredEncodedType indexedMemberListEncodedType)
      (fun I : ExactCoverInput => (I, supportPairsExecutable I)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id X) pairs
  have attached : TMPolyTimeMap X Attached
      (fun I : ExactCoverInput =>
        Program.contextListMapExecutable
          (C := exactCoverStructuredEncodedType) (X := indexedMemberEncodedType)
          (I, supportPairsExecutable I)) := by
    have composed := TMPolyTimeMap.comp
      (Program.contextListMapExecutable_tmPolyTime
        exactCoverStructuredEncodedType indexedMemberEncodedType)
      attachInput
    simpa [Function.comp, Attached, sourceIndexedMemberEncodedType, X] using composed
  have mapped := TMPolyTimeMap.list_map coverTripleExecutable_tmPolyTime
  have composed := TMPolyTimeMap.comp mapped attached
  simpa [coverTriplesExecutable, Function.comp, Attached, tripleListEncodedType, X] using composed

/-! ### Filler triples -/

/-- Executable `<beta, <x,j>, <next_j(x),j>>` for one indexed member. -/
def fillerTripleExecutable
    (input : (ExactCoverInput × Nat) × (Nat × Nat)) : Nat × Nat × Nat :=
  (input.1.2,
    positionCodeExecutable (input.1.1, (input.2.2, input.2.1)),
    positionCodeExecutable
      (input.1.1,
        (compactNextInSetExecutable (input.1.1, (input.2.1, input.2.2)), input.2.1)))

theorem fillerTripleExecutable_eq_legacy
    (I : ExactCoverInput) (beta j x : Nat) :
    fillerTripleExecutable ((I, beta), (j, x)) = compactFillerTriple I beta x j := by
  simp [fillerTripleExecutable, compactFillerTriple,
    positionCodeExecutable_eq_legacy, compactNextInSetExecutable_eq_legacy]

theorem fillerTripleExecutable_tmPolyTime :
    TMPolyTimeMap fillerInputEncodedType tripleEncodedType fillerTripleExecutable := by
  let X := fillerInputEncodedType
  have context : TMPolyTimeMap X sourceBetaEncodedType
      (fun input : (ExactCoverInput × Nat) × (Nat × Nat) => input.1) := by
    simpa [X, fillerInputEncodedType] using
      TMPolyTimeMap.fst sourceBetaEncodedType indexedMemberEncodedType
  have member : TMPolyTimeMap X indexedMemberEncodedType
      (fun input : (ExactCoverInput × Nat) × (Nat × Nat) => input.2) := by
    simpa [X, fillerInputEncodedType] using
      TMPolyTimeMap.snd sourceBetaEncodedType indexedMemberEncodedType
  have source : TMPolyTimeMap X exactCoverStructuredEncodedType
      (fun input : (ExactCoverInput × Nat) × (Nat × Nat) => input.1.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst exactCoverStructuredEncodedType EncodedType.nat) context
    simpa [Function.comp, X, sourceBetaEncodedType] using composed
  have beta : TMPolyTimeMap X EncodedType.nat
      (fun input : (ExactCoverInput × Nat) × (Nat × Nat) => input.1.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd exactCoverStructuredEncodedType EncodedType.nat) context
    simpa [Function.comp, X, sourceBetaEncodedType] using composed
  have index : TMPolyTimeMap X EncodedType.nat
      (fun input : (ExactCoverInput × Nat) × (Nat × Nat) => input.2.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst EncodedType.nat EncodedType.nat) member
    simpa [Function.comp, X, indexedMemberEncodedType] using composed
  have element : TMPolyTimeMap X EncodedType.nat
      (fun input : (ExactCoverInput × Nat) × (Nat × Nat) => input.2.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd EncodedType.nat EncodedType.nat) member
    simpa [Function.comp, X, indexedMemberEncodedType] using composed
  have currentCoordinates : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : (ExactCoverInput × Nat) × (Nat × Nat) =>
        (input.2.2, input.2.1)) :=
    TMPolyTimeMap.prod_mk element index
  have currentPositionInput : TMPolyTimeMap X positionCodeInputEncodedType
      (fun input : (ExactCoverInput × Nat) × (Nat × Nat) =>
        (input.1.1, (input.2.2, input.2.1))) :=
    TMPolyTimeMap.prod_mk source currentCoordinates
  have currentPosition : TMPolyTimeMap X EncodedType.nat
      (fun input : (ExactCoverInput × Nat) × (Nat × Nat) =>
        positionCodeExecutable (input.1.1, (input.2.2, input.2.1))) := by
    have composed := TMPolyTimeMap.comp positionCodeExecutable_tmPolyTime
      currentPositionInput
    simpa [Function.comp, X] using composed
  have nextCoordinates : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : (ExactCoverInput × Nat) × (Nat × Nat) =>
        (input.2.1, input.2.2)) :=
    TMPolyTimeMap.prod_mk index element
  have nextInput : TMPolyTimeMap X nextInputEncodedType
      (fun input : (ExactCoverInput × Nat) × (Nat × Nat) =>
        (input.1.1, (input.2.1, input.2.2))) :=
    TMPolyTimeMap.prod_mk source nextCoordinates
  have next : TMPolyTimeMap X EncodedType.nat
      (fun input : (ExactCoverInput × Nat) × (Nat × Nat) =>
        compactNextInSetExecutable (input.1.1, (input.2.1, input.2.2))) := by
    have composed := TMPolyTimeMap.comp compactNextInSetExecutable_tmPolyTime nextInput
    simpa [Function.comp, X] using composed
  have successorCoordinates : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : (ExactCoverInput × Nat) × (Nat × Nat) =>
        (compactNextInSetExecutable (input.1.1, (input.2.1, input.2.2)), input.2.1)) :=
    TMPolyTimeMap.prod_mk next index
  have successorPositionInput : TMPolyTimeMap X positionCodeInputEncodedType
      (fun input : (ExactCoverInput × Nat) × (Nat × Nat) =>
        (input.1.1,
          (compactNextInSetExecutable (input.1.1, (input.2.1, input.2.2)), input.2.1))) :=
    TMPolyTimeMap.prod_mk source successorCoordinates
  have successorPosition : TMPolyTimeMap X EncodedType.nat
      (fun input : (ExactCoverInput × Nat) × (Nat × Nat) =>
        positionCodeExecutable
          (input.1.1,
            (compactNextInSetExecutable (input.1.1, (input.2.1, input.2.2)), input.2.1))) := by
    have composed := TMPolyTimeMap.comp positionCodeExecutable_tmPolyTime
      successorPositionInput
    simpa [Function.comp, X] using composed
  have tail : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : (ExactCoverInput × Nat) × (Nat × Nat) =>
        (positionCodeExecutable (input.1.1, (input.2.2, input.2.1)),
          positionCodeExecutable
            (input.1.1,
              (compactNextInSetExecutable
                (input.1.1, (input.2.1, input.2.2)), input.2.1)))) :=
    TMPolyTimeMap.prod_mk currentPosition successorPosition
  simpa [fillerTripleExecutable, tripleEncodedType, tripleStructuredEncodedType, X] using
    TMPolyTimeMap.prod_mk beta tail

/-- All filler triples for one fixed beta code. -/
def fillerTriplesForBetaExecutable (input : ExactCoverInput × Nat) :
    List (Nat × Nat × Nat) :=
  (Program.contextListMapExecutable
      (C := sourceBetaEncodedType) (X := indexedMemberEncodedType)
      (input, supportPairsExecutable input.1)).map
    fillerTripleExecutable

theorem fillerTriplesForBetaExecutable_eq_legacy
    (I : ExactCoverInput) (beta : Nat) :
    fillerTriplesForBetaExecutable (I, beta) = compactFillerTriplesForBeta I beta := by
  rw [fillerTriplesForBetaExecutable, sourceBetaIndexedMemberContextMap_eq_map,
    List.map_map, supportPairsExecutable_eq_legacy, List.map_flatMap]
  simp only [List.map_map]
  unfold compactFillerTriplesForBeta compactFillerTriplesForBetaSet
  apply List.flatMap_congr
  intro j _
  apply List.map_congr_left
  intro x _
  exact fillerTripleExecutable_eq_legacy I beta j x

theorem fillerTriplesForBetaExecutable_tmPolyTime :
    TMPolyTimeMap sourceBetaEncodedType tripleListEncodedType
      fillerTriplesForBetaExecutable := by
  let X := sourceBetaEncodedType
  let Attached := EncodedType.list fillerInputEncodedType
  have source : TMPolyTimeMap X exactCoverStructuredEncodedType
      (fun input : ExactCoverInput × Nat => input.1) := by
    simpa [X, sourceBetaEncodedType] using
      TMPolyTimeMap.fst exactCoverStructuredEncodedType EncodedType.nat
  have pairs : TMPolyTimeMap X indexedMemberListEncodedType
      (fun input : ExactCoverInput × Nat => supportPairsExecutable input.1) := by
    have composed := TMPolyTimeMap.comp supportPairsExecutable_tmPolyTime source
    simpa [Function.comp, X] using composed
  have attachInput : TMPolyTimeMap X
      (EncodedType.prod sourceBetaEncodedType indexedMemberListEncodedType)
      (fun input : ExactCoverInput × Nat =>
        (input, supportPairsExecutable input.1)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id X) pairs
  have attached : TMPolyTimeMap X Attached
      (fun input : ExactCoverInput × Nat =>
        Program.contextListMapExecutable
          (C := sourceBetaEncodedType) (X := indexedMemberEncodedType)
          (input, supportPairsExecutable input.1)) := by
    have composed := TMPolyTimeMap.comp
      (Program.contextListMapExecutable_tmPolyTime
        sourceBetaEncodedType indexedMemberEncodedType)
      attachInput
    simpa [Function.comp, Attached, fillerInputEncodedType, X] using composed
  have mapped := TMPolyTimeMap.list_map fillerTripleExecutable_tmPolyTime
  have composed := TMPolyTimeMap.comp mapped attached
  simpa [fillerTriplesForBetaExecutable, Function.comp, Attached,
    tripleListEncodedType, X] using composed

/-- Ordered executable filler-triple family for every non-alpha code. -/
def fillerTriplesExecutable (I : ExactCoverInput) : List (Nat × Nat × Nat) :=
  List.flatten
    ((Program.contextListMapExecutable
        (C := exactCoverStructuredEncodedType) (X := EncodedType.nat)
        (I, nonAlphaCodesExecutable I)).map
      fillerTriplesForBetaExecutable)

theorem fillerTriplesExecutable_eq_legacy (I : ExactCoverInput) :
    fillerTriplesExecutable I = compactFillerTriples I := by
  rw [fillerTriplesExecutable, exactCoverNatContextMap_eq_map,
    List.map_map, nonAlphaCodesExecutable_eq_legacy]
  change
    (List.map (fun beta => fillerTriplesForBetaExecutable (I, beta))
      (compactNonAlphaCodes I)).flatten =
      (List.map (compactFillerTriplesForBeta I) (compactNonAlphaCodes I)).flatten
  apply congrArg List.flatten
  apply List.map_congr_left
  intro beta _
  exact fillerTriplesForBetaExecutable_eq_legacy I beta

set_option maxHeartbeats 600000 in
theorem fillerTriplesExecutable_tmPolyTime :
    TMPolyTimeMap exactCoverStructuredEncodedType tripleListEncodedType
      fillerTriplesExecutable := by
  let X := exactCoverStructuredEncodedType
  let Betas := EncodedType.list sourceBetaEncodedType
  let Blocks := EncodedType.list tripleListEncodedType
  have betas : TMPolyTimeMap X natListEncodedType nonAlphaCodesExecutable := by
    simpa [X, natListEncodedType] using nonAlphaCodesExecutable_tmPolyTime
  have attachInput : TMPolyTimeMap X
      (EncodedType.prod exactCoverStructuredEncodedType natListEncodedType)
      (fun I : ExactCoverInput => (I, nonAlphaCodesExecutable I)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id X) betas
  have attached : TMPolyTimeMap X Betas
      (fun I : ExactCoverInput =>
        Program.contextListMapExecutable
          (C := exactCoverStructuredEncodedType) (X := EncodedType.nat)
          (I, nonAlphaCodesExecutable I)) := by
    have contextMap : TMPolyTimeMap
        (EncodedType.prod exactCoverStructuredEncodedType natListEncodedType)
        Betas
        (Program.contextListMapExecutable
          (C := exactCoverStructuredEncodedType) (X := EncodedType.nat)) := by
      simpa [Betas, sourceBetaEncodedType, natListEncodedType] using
        (Program.contextListMapExecutable_tmPolyTime
          exactCoverStructuredEncodedType EncodedType.nat)
    have functionEq :
        (fun I : ExactCoverInput =>
          Program.contextListMapExecutable
            (C := exactCoverStructuredEncodedType) (X := EncodedType.nat)
            (I, nonAlphaCodesExecutable I)) =
          (Program.contextListMapExecutable
              (C := exactCoverStructuredEncodedType) (X := EncodedType.nat)) ∘
            (fun I : ExactCoverInput => (I, nonAlphaCodesExecutable I)) := by
      rfl
    exact
      (congrArg (fun function => TMPolyTimeMap X Betas function) functionEq).symm.mp
        (TMPolyTimeMap.comp
          (X := X)
          (Y := EncodedType.prod exactCoverStructuredEncodedType natListEncodedType)
          (Z := Betas)
          (f := Program.contextListMapExecutable
            (C := exactCoverStructuredEncodedType) (X := EncodedType.nat))
          (g := fun I : ExactCoverInput => (I, nonAlphaCodesExecutable I))
          contextMap attachInput)
  have blocks : TMPolyTimeMap X Blocks
      (fun I : ExactCoverInput =>
        (Program.contextListMapExecutable
          (C := exactCoverStructuredEncodedType) (X := EncodedType.nat)
          (I, nonAlphaCodesExecutable I)).map
          fillerTriplesForBetaExecutable) := by
    have mapped := TMPolyTimeMap.list_map fillerTriplesForBetaExecutable_tmPolyTime
    have composed := TMPolyTimeMap.comp mapped attached
    simpa [Function.comp, Blocks, Betas, X] using composed
  have flattened := TMPolyTimeMap.comp
    (Program.listFlatten_tmPolyTime tripleEncodedType) blocks
  simpa [fillerTriplesExecutable, Function.comp, Blocks, tripleListEncodedType, X] using
    flattened

/-! ### Full triple list and structured target payload -/

/-- Exact executable concatenation of cover and filler triples. -/
def triplesExecutable (I : ExactCoverInput) : List (Nat × Nat × Nat) :=
  coverTriplesExecutable I ++ fillerTriplesExecutable I

theorem triplesExecutable_eq_legacy (I : ExactCoverInput) :
    triplesExecutable I = compactTriples I := by
  rw [triplesExecutable, coverTriplesExecutable_eq_legacy,
    fillerTriplesExecutable_eq_legacy]
  rfl

theorem triplesExecutable_tmPolyTime :
    TMPolyTimeMap exactCoverStructuredEncodedType tripleListEncodedType
      triplesExecutable := by
  let X := exactCoverStructuredEncodedType
  have appendInput : TMPolyTimeMap X
      (EncodedType.prod tripleListEncodedType tripleListEncodedType)
      (fun I : ExactCoverInput =>
        (coverTriplesExecutable I, fillerTriplesExecutable I)) :=
    TMPolyTimeMap.prod_mk coverTriplesExecutable_tmPolyTime
      fillerTriplesExecutable_tmPolyTime
  have composed := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append tripleEncodedType) appendInput
  simpa [triplesExecutable, Function.comp, tripleListEncodedType, X] using composed

/-- Executable target cardinality, equal to the legacy position-code count. -/
def matchingCardinalityExecutable (I : ExactCoverInput) : Nat :=
  (positionCodesExecutable I).length

theorem matchingCardinalityExecutable_eq_legacy (I : ExactCoverInput) :
    matchingCardinalityExecutable I = (compactPositionCodes I).length := by
  rw [matchingCardinalityExecutable, positionCodesExecutable_eq_legacy]

theorem matchingCardinalityExecutable_tmPolyTime :
    TMPolyTimeMap exactCoverStructuredEncodedType EncodedType.nat
      matchingCardinalityExecutable := by
  have composed := TMPolyTimeMap.comp
    (Karp21.HittingSet.listLengthTMBackedMap EncodedType.nat).tm_polytime
    positionCodesExecutable_tmPolyTime
  simpa [matchingCardinalityExecutable, Function.comp, natListEncodedType] using composed

/-- The exact nested structured payload used by the 3DM wrapper encoder. -/
def compactMapCorePayloadExecutable (I : ExactCoverInput) :
    threeDimensionalMatchingTupleStructuredEncodedType.Carrier :=
  (coordBoundExecutable I,
    (coordBoundExecutable I,
      (coordBoundExecutable I,
        (triplesExecutable I, matchingCardinalityExecutable I))))

theorem compactMapCorePayloadExecutable_eq_legacy (I : ExactCoverInput) :
    compactMapCorePayloadExecutable I =
      ((compactMapCore I).xSize,
        ((compactMapCore I).ySize,
          ((compactMapCore I).zSize,
            ((compactMapCore I).triples, (compactMapCore I).k)))) := by
  simp [compactMapCorePayloadExecutable, compactMapCore, coordBoundExecutable_eq_legacy,
    triplesExecutable_eq_legacy, matchingCardinalityExecutable_eq_legacy]
  rfl

theorem compactMapCorePayloadExecutable_tmPolyTime :
    TMPolyTimeMap exactCoverStructuredEncodedType
      threeDimensionalMatchingTupleStructuredEncodedType
      compactMapCorePayloadExecutable := by
  let X := exactCoverStructuredEncodedType
  have bound : TMPolyTimeMap X EncodedType.nat coordBoundExecutable := by
    simpa [X] using coordBoundExecutable_tmPolyTime
  have triples : TMPolyTimeMap X tripleListEncodedType triplesExecutable := by
    simpa [X] using triplesExecutable_tmPolyTime
  have cardinality : TMPolyTimeMap X EncodedType.nat matchingCardinalityExecutable := by
    simpa [X] using matchingCardinalityExecutable_tmPolyTime
  have payloadTail : TMPolyTimeMap X
      (EncodedType.prod tripleListEncodedType EncodedType.nat)
      (fun I : ExactCoverInput =>
        (triplesExecutable I, matchingCardinalityExecutable I)) :=
    TMPolyTimeMap.prod_mk triples cardinality
  have zTail : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod tripleListEncodedType EncodedType.nat))
      (fun I : ExactCoverInput =>
        (coordBoundExecutable I,
          (triplesExecutable I, matchingCardinalityExecutable I))) :=
    TMPolyTimeMap.prod_mk bound payloadTail
  have yTail : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod tripleListEncodedType EncodedType.nat)))
      (fun I : ExactCoverInput =>
        (coordBoundExecutable I,
          (coordBoundExecutable I,
            (triplesExecutable I, matchingCardinalityExecutable I)))) :=
    TMPolyTimeMap.prod_mk bound zTail
  have full := TMPolyTimeMap.prod_mk bound yTail
  simpa [compactMapCorePayloadExecutable,
    threeDimensionalMatchingTupleStructuredEncodedType, X] using full

/-- Rewrap the exact nested payload without changing its encoded word. -/
def threeDimensionalMatchingInputOfPayload
    (payload : threeDimensionalMatchingTupleStructuredEncodedType.Carrier) :
    ThreeDimensionalMatchingInput where
  xSize := payload.1
  ySize := payload.2.1
  zSize := payload.2.2.1
  triples := payload.2.2.2.1
  k := payload.2.2.2.2

theorem threeDimensionalMatchingInputOfPayload_encode
    (payload : threeDimensionalMatchingTupleStructuredEncodedType.Carrier) :
    threeDimensionalMatchingStructuredEncodedType.encode
        (threeDimensionalMatchingInputOfPayload payload) =
      threeDimensionalMatchingTupleStructuredEncodedType.encode payload := by
  rfl

theorem threeDimensionalMatchingInputOfPayload_tmPolyTime :
    TMPolyTimeMap threeDimensionalMatchingTupleStructuredEncodedType
      threeDimensionalMatchingStructuredEncodedType
      threeDimensionalMatchingInputOfPayload := by
  apply TMPolyTimeMap.of_encodingEquiv
    threeDimensionalMatchingTupleStructuredEncodedType
    threeDimensionalMatchingStructuredEncodedType
    threeDimensionalMatchingInputOfPayload (Equiv.refl _)
  intro payload
  rw [threeDimensionalMatchingInputOfPayload_encode]
  change threeDimensionalMatchingTupleStructuredEncodedType.encode payload =
    List.map id (threeDimensionalMatchingTupleStructuredEncodedType.encode payload)
  rw [List.map_id]

/-- Fully assembled executable core, before the later well-formedness guard. -/
def compactMapCoreExecutable (I : ExactCoverInput) : ThreeDimensionalMatchingInput :=
  threeDimensionalMatchingInputOfPayload (compactMapCorePayloadExecutable I)

theorem compactMapCoreExecutable_eq_legacy (I : ExactCoverInput) :
    compactMapCoreExecutable I = compactMapCore I := by
  unfold compactMapCoreExecutable threeDimensionalMatchingInputOfPayload
    compactMapCorePayloadExecutable compactMapCore
  rw [coordBoundExecutable_eq_legacy, triplesExecutable_eq_legacy,
    matchingCardinalityExecutable_eq_legacy]

theorem compactMapCoreExecutable_tmPolyTime :
    TMPolyTimeMap exactCoverStructuredEncodedType
      threeDimensionalMatchingStructuredEncodedType compactMapCoreExecutable := by
  have composed := TMPolyTimeMap.comp
    threeDimensionalMatchingInputOfPayload_tmPolyTime
    compactMapCorePayloadExecutable_tmPolyTime
  simpa [compactMapCoreExecutable, Function.comp] using composed

assert_standard_axioms
  supportPairBlockExecutable_eq_legacy,
  supportPairBlockExecutable_tmPolyTime,
  supportPairsExecutable_eq_legacy,
  supportPairsExecutable_tmPolyTime,
  coverTripleExecutable_eq_legacy,
  coverTripleExecutable_tmPolyTime,
  coverTriplesExecutable_eq_legacy,
  coverTriplesExecutable_tmPolyTime,
  fillerTripleExecutable_eq_legacy,
  fillerTripleExecutable_tmPolyTime,
  fillerTriplesForBetaExecutable_eq_legacy,
  fillerTriplesForBetaExecutable_tmPolyTime,
  fillerTriplesExecutable_eq_legacy,
  fillerTriplesExecutable_tmPolyTime,
  triplesExecutable_eq_legacy,
  triplesExecutable_tmPolyTime,
  matchingCardinalityExecutable_eq_legacy,
  matchingCardinalityExecutable_tmPolyTime,
  compactMapCorePayloadExecutable_eq_legacy,
  compactMapCorePayloadExecutable_tmPolyTime,
  threeDimensionalMatchingInputOfPayload_encode,
  threeDimensionalMatchingInputOfPayload_tmPolyTime,
  compactMapCoreExecutable_eq_legacy,
  compactMapCoreExecutable_tmPolyTime

end TripleAssembly
end ExactCoverToThreeDimensionalMatchingTM
end Domain
end ComplexityReduction
