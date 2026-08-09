/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.IncidenceToExactlyOneNeighborCore
import Mathlib.Tactic
import ComplexityReduction.Program.CompileTM
import ComplexityReduction.Program.List
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.InvariantFold
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatArithmetic
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatPair
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatRange
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.EdgeScan
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.StructuredTM.ProductSumChoice

/-!
Program-facing executable decomposition for the canonical
`IncidenceIR -> ExactlyOneNeighbor` hub gadget.

This leaf is deliberately still independent of concrete set-system wrappers,
routes, registries, and legacy route assembly.  It records the closed
instruction/state computation which a direct-TM realization must certify.
-/

namespace ComplexityReduction
namespace Domain
namespace IncidenceToExactlyOneNeighbor

open ComplexityReduction
open Encoding
open Program

/-- One instruction is either the retained pair of hub bounds or one incidence pair. -/
abbrev Instruction : Type := (Nat × Nat) ⊕ (Nat × Nat)

/-- The instruction stream first fixes both bounds, then carries each raw incidence pair. -/
def instructions (input : IncidenceIR) : List Instruction :=
  .inl (input.leftSize, input.rightSize) :: input.membershipPairs.map Sum.inr

/-- The fold retains bounds, a validity flag, and the two orientations of the edge table. -/
abbrev FoldState : Type := Nat × (Nat × (Bool × (List (Nat × Nat) × List (Nat × Nat))))

/-- Assemble one fold state without hiding its ordered fields. -/
def mkFoldState (left right : Nat) (valid : Bool)
    (forward reverse : List (Nat × Nat)) : FoldState :=
  (left, (right, (valid, (forward, reverse))))

/-- Fixed initial state before the leading bounds instruction has been read. -/
def initialFoldState : FoldState :=
  mkFoldState 0 0 true [] []

/-- Boolean bound check for one raw pair against the currently retained hub bounds. -/
def pairWithinBoundsBool (bounds pair : Nat × Nat) : Bool :=
  decide (pair.1 < bounds.1 ∧ pair.2 < bounds.2)

/-- The fold step both validates and emits the two required undirected edge orientations. -/
def foldStep (argument : FoldState × Instruction) : FoldState :=
  match argument.2 with
  | .inl bounds => mkFoldState bounds.1 bounds.2 true [] []
  | .inr pair =>
      let left := argument.1.1
      let right := argument.1.2.1
      let valid := argument.1.2.2.1
      let forward := argument.1.2.2.2.1
      let reverse := argument.1.2.2.2.2
      let shifted := left + pair.2
      mkFoldState left right (valid && pairWithinBoundsBool (left, right) pair)
        (forward ++ [(pair.1, shifted)]) (reverse ++ [(shifted, pair.1)])

/-- Run the closed instruction fold for one canonical hub input. -/
def foldedState (input : IncidenceIR) : FoldState :=
  (instructions input).foldl (fun state instruction => foldStep (state, instruction)) initialFoldState

/-- Build the valid target payload from a completed fold state. -/
def coreTargetOfFoldState (state : FoldState) : ExactlyOneNeighborInput where
  graph :=
    { vertices := state.1 + state.2.1
      edges := state.2.2.2.1 ++ state.2.2.2.2
      directed := false }
  R := List.range state.1

/-- The executable fold/dispatch implementation of the canonical shared gadget. -/
def programRun (input : IncidenceIR) : ExactlyOneNeighborInput :=
  if (foldedState input).2.2.1 then coreTargetOfFoldState (foldedState input) else noTarget

/-- Folding a pair suffix has the expected validity and ordered-edge normal form. -/
theorem foldPairs_aux (left right : Nat) :
    ∀ (pairs : List (Nat × Nat)) (valid : Bool)
      (forward reverse : List (Nat × Nat)),
      (pairs.map Sum.inr).foldl (fun state instruction => foldStep (state, instruction))
          (mkFoldState left right valid forward reverse) =
        mkFoldState left right
          (valid && pairs.all (pairWithinBoundsBool (left, right)))
          (forward ++ pairs.map fun pair => (pair.1, left + pair.2))
          (reverse ++ pairs.map fun pair => (left + pair.2, pair.1)) := by
  intro pairs
  induction pairs with
  | nil =>
      intro valid forward reverse
      simp [mkFoldState]
  | cons pair pairs inductionHypothesis =>
      intro valid forward reverse
      simp only [List.map_cons, List.foldl_cons]
      have step_eq :
          foldStep (mkFoldState left right valid forward reverse, Sum.inr pair) =
            mkFoldState left right (valid && pairWithinBoundsBool (left, right) pair)
              (forward ++ [(pair.1, left + pair.2)])
              (reverse ++ [(left + pair.2, pair.1)]) :=
        rfl
      rw [step_eq]
      rw [inductionHypothesis]
      simp only [List.all_cons]
      simp [mkFoldState, List.append_assoc, Bool.and_assoc]

/-- The fold's pointwise Boolean test is the hub's original all-pairs guard. -/
theorem pairWithinBoundsBool_eq_core (input : IncidenceIR) (pair : Nat × Nat) :
    pairWithinBoundsBool (input.leftSize, input.rightSize) pair =
      decide (pair.1 < input.leftSize ∧ pair.2 < input.rightSize) :=
  rfl

/-- The completed state exactly reconstructs the core guard and both edge orientations. -/
theorem foldedState_eq_core (input : IncidenceIR) :
    foldedState input =
      mkFoldState input.leftSize input.rightSize (wellFormedBool input)
        (forwardEdges input) ((forwardEdges input).map fun edge => (edge.2, edge.1)) := by
  unfold foldedState instructions
  simp only [List.foldl_cons]
  have head_eq :
      foldStep (initialFoldState, Sum.inl (input.leftSize, input.rightSize)) =
        mkFoldState input.leftSize input.rightSize true [] [] :=
    rfl
  rw [head_eq]
  rw [foldPairs_aux]
  simp only [mkFoldState]
  have pair_check_eq (pair : Nat × Nat) :
      pairWithinBoundsBool (input.leftSize, input.rightSize) pair =
        (decide (pair.1 < input.leftSize) && decide (pair.2 < input.rightSize)) := by
    unfold pairWithinBoundsBool
    by_cases leftBound : pair.1 < input.leftSize <;>
      by_cases rightBound : pair.2 < input.rightSize <;>
      simp [leftBound, rightBound]
  have all_check_eq : ∀ pairs : List (Nat × Nat),
      pairs.all (pairWithinBoundsBool (input.leftSize, input.rightSize)) =
        pairs.all fun pair =>
          (decide (pair.1 < input.leftSize) && decide (pair.2 < input.rightSize)) := by
    intro pairs
    induction pairs with
    | nil => rfl
    | cons pair pairs inductionHypothesis =>
        simp [pair_check_eq, inductionHypothesis]
  rw [all_check_eq]
  simp [IncidenceIRValidation.wellFormedBool, forwardEdges, rightVertex,
    Function.comp_def]

/-- The program-facing executable is extensionally the semantic core executable. -/
theorem programRun_eq_run (input : IncidenceIR) :
    programRun input = run input := by
  unfold programRun
  rw [show foldedState input =
      mkFoldState input.leftSize input.rightSize (wellFormedBool input)
        (forwardEdges input) ((forwardEdges input).map fun edge => (edge.2, edge.1))
    from foldedState_eq_core input]
  rfl

/-! ### Direct-TM realization ingredients -/

/-- The exact unary-natural encoding reused by every hub index field. -/
abbrev natEncoding : EncodedType := EncodedType.nat

/-- The exact standard encoding of an ordered hub pair. -/
abbrev pairEncoding : EncodedType := EncodedType.prod natEncoding natEncoding

/-- The exact encoded list of ordered hub pairs. -/
abbrev pairListEncoding : EncodedType := EncodedType.list pairEncoding

/-- The canonical full incidence encoding, definitionally the hub presentation's encoder. -/
abbrev incidenceEncoding : EncodedType :=
  EncodedType.prod natEncoding (EncodedType.prod natEncoding pairListEncoding)

/-- The encoded instruction sum used by the closed fold. -/
abbrev instructionEncoding : EncodedType := EncodedType.sum pairEncoding pairEncoding

/-- The encoded instruction stream. -/
abbrev instructionListEncoding : EncodedType := EncodedType.list instructionEncoding

/-- The standard encoded list of graph edges. -/
abbrev edgeListEncoding : EncodedType := EncodedType.list pairEncoding

/-- The exact structural state encoder used by the hub fold. -/
abbrev foldStateEncoding : EncodedType :=
  EncodedType.prod natEncoding
    (EncodedType.prod natEncoding
      (EncodedType.prod EncodedType.bool
        (EncodedType.prod edgeListEncoding edgeListEncoding)))

/-- Exact standard V2 presentations used to assemble the fold step program. -/
abbrev natPresentation : LawfulEncodedType := StandardInstances.unaryNat
abbrev pairPresentation : LawfulEncodedType :=
  StandardInstances.prod natPresentation natPresentation
abbrev pairListPresentation : LawfulEncodedType := StandardInstances.list pairPresentation
abbrev foldStatePresentation : LawfulEncodedType :=
  StandardInstances.prod natPresentation
    (StandardInstances.prod natPresentation
      (StandardInstances.prod StandardInstances.bool
        (StandardInstances.prod pairListPresentation pairListPresentation)))
abbrev foldPairStepPresentation : LawfulEncodedType :=
  StandardInstances.prod foldStatePresentation pairPresentation

/-- The one minimal arithmetic atom required by the pair-processing fold step. -/
def natAddPrimitive : Primitive pairPresentation natPresentation :=
  Primitive.ofTMPolyTime (fun pair : Nat × Nat => pair.1 + pair.2) (by
    simpa [pairPresentation, natPresentation, StandardInstances.prod,
      StandardInstances.unaryNat] using natAdd_tm_polytime)

/-- The one minimal Boolean conjunction atom required by the pair-processing fold step. -/
def boolAndPrimitive :
    Primitive (StandardInstances.prod StandardInstances.bool StandardInstances.bool)
      StandardInstances.bool :=
  Primitive.ofTMPolyTime Karp21.graphBoolAndPair (by
    simpa [StandardInstances.prod, StandardInstances.bool] using Karp21.graphBoolAndPair_tm_polytime)


/-- The standard tuple encoding underlying the structured graph wrapper. -/
abbrev graphTupleEncoding : EncodedType :=
  EncodedType.prod natEncoding
    (EncodedType.prod edgeListEncoding EncodedType.bool)

/-- Repackage an exact structural graph tuple as the canonical graph carrier. -/
def graphOfTuple (value : graphTupleEncoding.Carrier) :
    ComplexityReduction.Combinatorics.Graph.GraphInput :=
  { vertices := value.1, edges := value.2.1, directed := value.2.2 }

/-- The graph wrapper changes no encoded symbols: it is an encoder-preserving reification. -/
theorem graphOfTuple_tmPolyTime :
    TMPolyTimeMap graphTupleEncoding
      ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType graphOfTuple := by
  exact TMPolyTimeMap.of_encodingEquiv _ _ _ (Equiv.refl _) (by
    intro value
    change graphTupleEncoding.encode value = List.map id (graphTupleEncoding.encode value)
    rw [List.map_id])

/-- Repackage a graph/list tuple as the canonical existential EON carrier. -/
def eonOfTuple
    (value : (EncodedType.prod ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType
      exactlyOneNeighborRequiredVerticesStructuredEncodedType).Carrier) :
    ExactlyOneNeighborInput :=
  { graph := value.1, R := value.2 }

/-- The EON wrapper likewise preserves the complete structured tuple encoding. -/
theorem eonOfTuple_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType
        exactlyOneNeighborRequiredVerticesStructuredEncodedType)
      exactlyOneNeighborStructuredEncodedType eonOfTuple := by
  exact TMPolyTimeMap.of_encodingEquiv _ _ _ (Equiv.refl _) (by
    intro value
    change
      (EncodedType.prod ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType
        exactlyOneNeighborRequiredVerticesStructuredEncodedType).encode value =
        List.map id
          ((EncodedType.prod ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType
            exactlyOneNeighborRequiredVerticesStructuredEncodedType).encode value)
    rw [List.map_id])

/-- The bounds header and incidence suffix are assembled using only structural direct-TM maps. -/
theorem instructions_tmPolyTime :
    TMPolyTimeMap incidenceEncoding instructionListEncoding instructions := by
  let X := incidenceEncoding
  let payloadEncoding := EncodedType.prod natEncoding pairListEncoding
  have leftTM :
      TMPolyTimeMap X natEncoding (fun input : X.Carrier => input.1) := by
    simpa [X, incidenceEncoding, payloadEncoding] using
      TMPolyTimeMap.fst natEncoding payloadEncoding
  have payloadTM :
      TMPolyTimeMap X payloadEncoding (fun input : X.Carrier => input.2) := by
    simpa [X, incidenceEncoding, payloadEncoding] using
      TMPolyTimeMap.snd natEncoding payloadEncoding
  have rightTM :
      TMPolyTimeMap X natEncoding (fun input : X.Carrier => input.2.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst natEncoding pairListEncoding) payloadTM
    simpa [Function.comp, X, payloadEncoding] using composed
  have pairsTM :
      TMPolyTimeMap X pairListEncoding (fun input : X.Carrier => input.2.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd natEncoding pairListEncoding) payloadTM
    simpa [Function.comp, X, payloadEncoding] using composed
  have boundsTM :
      TMPolyTimeMap X pairEncoding (fun input : X.Carrier => (input.1, input.2.1)) :=
    TMPolyTimeMap.prod_mk leftTM rightTM
  have headerInstructionTM :
      TMPolyTimeMap X instructionEncoding
        (fun input : X.Carrier => Sum.inl (input.1, input.2.1)) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.inl pairEncoding pairEncoding) boundsTM
    simpa [Function.comp] using composed
  have headerTM :
      TMPolyTimeMap X instructionListEncoding
        (fun input : X.Carrier => [Sum.inl (input.1, input.2.1)]) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton instructionEncoding) headerInstructionTM
    simpa [Function.comp] using composed
  have suffixElementTM :
      TMPolyTimeMap pairEncoding instructionEncoding
        (fun pair : pairEncoding.Carrier => Sum.inr pair) :=
    TMPolyTimeMap.inr pairEncoding pairEncoding
  have suffixListTM :
      TMPolyTimeMap pairListEncoding instructionListEncoding
        (fun pairs : pairListEncoding.Carrier => pairs.map Sum.inr) :=
    TMPolyTimeMap.list_map suffixElementTM
  have suffixTM :
      TMPolyTimeMap X instructionListEncoding
        (fun input : X.Carrier => input.2.2.map Sum.inr) := by
    have composed := TMPolyTimeMap.comp suffixListTM pairsTM
    simpa [Function.comp] using composed
  have appendInputTM :
      TMPolyTimeMap X
        (EncodedType.prod instructionListEncoding instructionListEncoding)
        (fun input : X.Carrier =>
          ([Sum.inl (input.1, input.2.1)], input.2.2.map Sum.inr)) :=
    TMPolyTimeMap.prod_mk headerTM suffixTM
  have assembled := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append instructionEncoding) appendInputTM
  simpa [instructions, Function.comp, X] using assembled

/-- The fold's Boolean pair check is assembled from the reusable unary comparisons. -/
theorem pairWithinBoundsBool_tmPolyTime :
    TMPolyTimeMap (EncodedType.prod pairEncoding pairEncoding) EncodedType.bool
      (fun input : (EncodedType.prod pairEncoding pairEncoding).Carrier =>
        pairWithinBoundsBool input.1 input.2) := by
  let X := EncodedType.prod pairEncoding pairEncoding
  have boundsTM :
      TMPolyTimeMap X pairEncoding (fun input : X.Carrier => input.1) := by
    simpa [X] using TMPolyTimeMap.fst pairEncoding pairEncoding
  have pairTM :
      TMPolyTimeMap X pairEncoding (fun input : X.Carrier => input.2) := by
    simpa [X] using TMPolyTimeMap.snd pairEncoding pairEncoding
  have leftBoundTM :
      TMPolyTimeMap X natEncoding (fun input : X.Carrier => input.1.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst natEncoding natEncoding) boundsTM
    simpa [Function.comp, X] using composed
  have rightBoundTM :
      TMPolyTimeMap X natEncoding (fun input : X.Carrier => input.1.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd natEncoding natEncoding) boundsTM
    simpa [Function.comp, X] using composed
  have leftPairTM :
      TMPolyTimeMap X natEncoding (fun input : X.Carrier => input.2.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst natEncoding natEncoding) pairTM
    simpa [Function.comp, X] using composed
  have rightPairTM :
      TMPolyTimeMap X natEncoding (fun input : X.Carrier => input.2.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd natEncoding natEncoding) pairTM
    simpa [Function.comp, X] using composed
  have leftInputTM :
      TMPolyTimeMap X pairEncoding
        (fun input : X.Carrier => (input.2.1, input.1.1)) :=
    TMPolyTimeMap.prod_mk leftPairTM leftBoundTM
  have rightInputTM :
      TMPolyTimeMap X pairEncoding
        (fun input : X.Carrier => (input.2.2, input.1.2)) :=
    TMPolyTimeMap.prod_mk rightPairTM rightBoundTM
  have leftCheckTM :
      TMPolyTimeMap X EncodedType.bool
        (fun input : X.Carrier => natLtBool (input.2.1, input.1.1)) := by
    have composed := TMPolyTimeMap.comp natLtBool_tm_polytime leftInputTM
    simpa [Function.comp] using composed
  have rightCheckTM :
      TMPolyTimeMap X EncodedType.bool
        (fun input : X.Carrier => natLtBool (input.2.2, input.1.2)) := by
    have composed := TMPolyTimeMap.comp natLtBool_tm_polytime rightInputTM
    simpa [Function.comp] using composed
  have checksTM :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun input : X.Carrier =>
          (natLtBool (input.2.1, input.1.1), natLtBool (input.2.2, input.1.2))) :=
    TMPolyTimeMap.prod_mk leftCheckTM rightCheckTM
  have assembled := TMPolyTimeMap.comp Karp21.graphBoolAndPair_tm_polytime checksTM
  have check_eq (bounds pair : Nat × Nat) :
      pairWithinBoundsBool bounds pair =
        Karp21.graphBoolAndPair
          (natLtBool (pair.1, bounds.1), natLtBool (pair.2, bounds.2)) := by
    by_cases leftBound : pair.1 < bounds.1 <;>
      by_cases rightBound : pair.2 < bounds.2 <;>
      simp [pairWithinBoundsBool, natLtBool, Karp21.graphBoolAndPair, leftBound, rightBound]
  simpa only [Function.comp_apply, check_eq] using assembled

/-- The pair-bound primitive is admitted only from the direct-TM theorem immediately above. -/
def pairWithinBoundsPrimitive :
    Primitive (StandardInstances.prod pairPresentation pairPresentation) StandardInstances.bool :=
  Primitive.ofTMPolyTime (fun value : (Nat × Nat) × (Nat × Nat) =>
    pairWithinBoundsBool value.1 value.2) (by
      simpa [pairPresentation, StandardInstances.prod, StandardInstances.bool] using
        pairWithinBoundsBool_tmPolyTime)

/-- Structural projections of the state/pair input of an incidence instruction step. -/
private def stepStateProgram :
    PolyProg foldPairStepPresentation foldStatePresentation :=
  .fst foldStatePresentation pairPresentation

private def stepPairProgram :
    PolyProg foldPairStepPresentation pairPresentation :=
  .snd foldStatePresentation pairPresentation

private def stateTailProgram :
    PolyProg foldPairStepPresentation
      (StandardInstances.prod natPresentation
        (StandardInstances.prod StandardInstances.bool
          (StandardInstances.prod pairListPresentation pairListPresentation))) :=
  .comp
    (.snd natPresentation
      (StandardInstances.prod natPresentation
        (StandardInstances.prod StandardInstances.bool
          (StandardInstances.prod pairListPresentation pairListPresentation))))
    stepStateProgram

private def stateLeftProgram :
    PolyProg foldPairStepPresentation natPresentation :=
  .comp
    (.fst natPresentation
      (StandardInstances.prod natPresentation
        (StandardInstances.prod StandardInstances.bool
          (StandardInstances.prod pairListPresentation pairListPresentation))))
    stepStateProgram

private def stateRightProgram :
    PolyProg foldPairStepPresentation natPresentation :=
  .comp
    (.fst natPresentation
      (StandardInstances.prod StandardInstances.bool
        (StandardInstances.prod pairListPresentation pairListPresentation)))
    stateTailProgram

private def stateBoolTailProgram :
    PolyProg foldPairStepPresentation
      (StandardInstances.prod StandardInstances.bool
        (StandardInstances.prod pairListPresentation pairListPresentation)) :=
  .comp
    (.snd natPresentation
      (StandardInstances.prod StandardInstances.bool
        (StandardInstances.prod pairListPresentation pairListPresentation)))
    stateTailProgram

private def stateValidProgram :
    PolyProg foldPairStepPresentation StandardInstances.bool :=
  .comp
    (.fst StandardInstances.bool
      (StandardInstances.prod pairListPresentation pairListPresentation))
    stateBoolTailProgram

private def stateEdgeListsProgram :
    PolyProg foldPairStepPresentation
      (StandardInstances.prod pairListPresentation pairListPresentation) :=
  .comp
    (.snd StandardInstances.bool
      (StandardInstances.prod pairListPresentation pairListPresentation))
    stateBoolTailProgram

private def stateForwardProgram :
    PolyProg foldPairStepPresentation pairListPresentation :=
  .comp (.fst pairListPresentation pairListPresentation) stateEdgeListsProgram

private def stateReverseProgram :
    PolyProg foldPairStepPresentation pairListPresentation :=
  .comp (.snd pairListPresentation pairListPresentation) stateEdgeListsProgram

private def pairLeftProgram :
    PolyProg foldPairStepPresentation natPresentation :=
  .comp (.fst natPresentation natPresentation) stepPairProgram

private def pairRightProgram :
    PolyProg foldPairStepPresentation natPresentation :=
  .comp (.snd natPresentation natPresentation) stepPairProgram

/-- The closed program for the `.inr` incidence-pair step of the shared gadget fold. -/
def pairStepProgram : PolyProg foldPairStepPresentation foldStatePresentation :=
  let bounds : PolyProg foldPairStepPresentation pairPresentation :=
    .pair stateLeftProgram stateRightProgram
  let pairCheck : PolyProg foldPairStepPresentation StandardInstances.bool :=
    .comp (.atom pairWithinBoundsPrimitive) (.pair bounds stepPairProgram)
  let nextValid : PolyProg foldPairStepPresentation StandardInstances.bool :=
    .comp (.atom boolAndPrimitive) (.pair stateValidProgram pairCheck)
  let shifted : PolyProg foldPairStepPresentation natPresentation :=
    .comp (.atom natAddPrimitive) (.pair stateLeftProgram pairRightProgram)
  let forwardEdge : PolyProg foldPairStepPresentation pairPresentation :=
    .pair pairLeftProgram shifted
  let reverseEdge : PolyProg foldPairStepPresentation pairPresentation :=
    .pair shifted pairLeftProgram
  let forwardOut : PolyProg foldPairStepPresentation pairListPresentation :=
    .comp (.listAppend pairPresentation)
      (.pair stateForwardProgram
        (.comp (PolyProg.listSingleton pairPresentation) forwardEdge))
  let reverseOut : PolyProg foldPairStepPresentation pairListPresentation :=
    .comp (.listAppend pairPresentation)
      (.pair stateReverseProgram
        (.comp (PolyProg.listSingleton pairPresentation) reverseEdge))
  .pair stateLeftProgram
    (.pair stateRightProgram
      (.pair nextValid (.pair forwardOut reverseOut)))

/-- The closed step program has exactly the pair branch of `foldStep` as its executable. -/
theorem pairStepProgram_run (argument : FoldState × (Nat × Nat)) :
    pairStepProgram.run argument = foldStep (argument.1, Sum.inr argument.2) := by
  rcases argument with ⟨state, pair⟩
  rcases state with ⟨left, right, valid, forward, reverse⟩
  rcases pair with ⟨source, target⟩
  dsimp [foldStep]
  simp [pairStepProgram, stepStateProgram, stepPairProgram, stateTailProgram,
    stateLeftProgram, stateRightProgram, stateBoolTailProgram, stateValidProgram,
    stateEdgeListsProgram, stateForwardProgram, stateReverseProgram, pairLeftProgram,
    pairRightProgram, natAddPrimitive, boolAndPrimitive, pairWithinBoundsPrimitive,
    Karp21.graphBoolAndPair]
  cases valid <;> rfl

/-- Direct TM evidence for the `.inr` fold branch is definitionally its program compiler output. -/
def pairStepProgram_tmPolyTime :
    TMPolyTimeMap foldPairStepPresentation.encodedType foldStatePresentation.encodedType
      pairStepProgram.run :=
  pairStepProgram.compileTM

/-- The closed program for the leading bounds branch of the shared gadget fold. -/
def boundsStepProgram : PolyProg pairPresentation foldStatePresentation :=
  let left : PolyProg pairPresentation natPresentation :=
    .fst natPresentation natPresentation
  let right : PolyProg pairPresentation natPresentation :=
    .snd natPresentation natPresentation
  let valid : PolyProg pairPresentation StandardInstances.bool :=
    .const pairPresentation StandardInstances.bool true
  let empty : PolyProg pairPresentation pairListPresentation :=
    .const pairPresentation pairListPresentation []
  .pair left (.pair right (.pair valid (.pair empty empty)))

/-- The bounds branch ignores its incoming accumulator exactly as `foldStep` does. -/
theorem boundsStepProgram_run (state : FoldState) (bounds : Nat × Nat) :
    boundsStepProgram.run bounds = foldStep (state, Sum.inl bounds) := by
  rcases state with ⟨left, right, valid, forward, reverse⟩
  rcases bounds with ⟨newLeft, newRight⟩
  simp [boundsStepProgram, foldStep, mkFoldState]
  rfl

/-- Direct TM evidence for the bounds branch is definitionally its program compiler output. -/
def boundsStepProgram_tmPolyTime :
    TMPolyTimeMap pairPresentation.encodedType foldStatePresentation.encodedType
      boundsStepProgram.run :=
  boundsStepProgram.compileTM

/-- The complete fold step dispatches through the reusable product/sum structural TM. -/
theorem foldStep_tmPolyTime :
    TMPolyTimeMap (EncodedType.prod foldStateEncoding instructionEncoding) foldStateEncoding foldStep := by
  have choiceTM := Karp21.Partition.prodSumChoice_tm_polytime
    foldStateEncoding pairEncoding pairEncoding
  have branchTM := TMPolyTimeMap.sum_elim boundsStepProgram_tmPolyTime pairStepProgram_tmPolyTime
  have assembled := TMPolyTimeMap.comp branchTM choiceTM
  convert assembled using 1
  funext argument
  rcases argument with ⟨state, instruction⟩
  cases instruction with
  | inl bounds =>
      simpa [Function.comp, Karp21.Partition.prodSumChoice] using
        boundsStepProgram_run state bounds
  | inr pair =>
      simpa [Function.comp, Karp21.Partition.prodSumChoice] using
        (pairStepProgram_run (state, pair)).symm

/-! ### Encoded-size facts for the verified fold bound -/

theorem pairEncoding_inputSize (left right : Nat) :
    pairEncoding.inputSize (left, right) = left + right + 3 := by
  rw [EncodedType.inputSize_prod, EncodedType.inputSize_nat, EncodedType.inputSize_nat]
  omega

theorem instructionEncoding_inputSize_inl (left right : Nat) :
    instructionEncoding.inputSize (Sum.inl (left, right) : Instruction) = left + right + 4 := by
  unfold instructionEncoding EncodedType.inputSize EncodedType.sum
  change
    ([Sum.inl false] ++
      (pairEncoding.encode (left, right)).map (fun symbol => Sum.inr (Sum.inl symbol))).length = _
  rw [List.length_append, List.length_singleton, List.length_map]
  change 1 + pairEncoding.inputSize (left, right) = _
  rw [pairEncoding_inputSize]
  omega

theorem instructionEncoding_inputSize_inr (left right : Nat) :
    instructionEncoding.inputSize (Sum.inr (left, right) : Instruction) = left + right + 4 := by
  unfold instructionEncoding EncodedType.inputSize EncodedType.sum
  change
    ([Sum.inl true] ++
      (pairEncoding.encode (left, right)).map (fun symbol => Sum.inr (Sum.inr symbol))).length = _
  rw [List.length_append, List.length_singleton, List.length_map]
  change 1 + pairEncoding.inputSize (left, right) = _
  rw [pairEncoding_inputSize]
  omega

theorem foldStateEncoding_inputSize (left right : Nat) (valid : Bool)
    (forward reverse : List (Nat × Nat)) :
    foldStateEncoding.inputSize (mkFoldState left right valid forward reverse) =
      left + right + edgeListEncoding.inputSize forward + edgeListEncoding.inputSize reverse + 7 := by
  change foldStateEncoding.inputSize (left, (right, (valid, (forward, reverse)))) = _
  unfold foldStateEncoding
  rw [EncodedType.inputSize_prod, EncodedType.inputSize_prod,
    EncodedType.inputSize_prod, EncodedType.inputSize_prod]
  simp
  omega

theorem edgeListEncoding_inputSize_append_singleton
    (edges : List (Nat × Nat)) (left right : Nat) :
    edgeListEncoding.inputSize (edges ++ [(left, right)]) =
      edgeListEncoding.inputSize edges + left + right + 4 := by
  induction edges with
  | nil =>
      change pairEncoding.list.inputSize [(left, right)] =
        pairEncoding.list.inputSize [] + left + right + 4
      rw [EncodedType.inputSize_list_cons, EncodedType.inputSize_list_nil]
      rw [pairEncoding_inputSize]
      omega
  | cons edge edges inductionHypothesis =>
      have inductionHypothesis' :
          pairEncoding.list.inputSize (edges ++ [(left, right)]) =
            pairEncoding.list.inputSize edges + left + right + 4 :=
        inductionHypothesis
      change pairEncoding.list.inputSize (edge :: (edges ++ [(left, right)])) =
        pairEncoding.list.inputSize (edge :: edges) + left + right + 4
      rw [EncodedType.inputSize_list_cons]
      rw [EncodedType.inputSize_list_cons]
      rw [inductionHypothesis']
      omega

theorem edgeListEncoding_inputSize_nil : edgeListEncoding.inputSize [] = 0 := by
  change pairEncoding.list.inputSize [] = 0
  exact EncodedType.inputSize_list_nil pairEncoding

/-- The fold invariant retains the two numeric bounds inside the instruction-stream size budget. -/
def FoldStateInvariant (bound : Nat) (state : FoldState) : Prop :=
  state.1 ≤ bound ∧ state.2.1 ≤ bound

/-- Fixed base budget for the empty initial fold state. -/
noncomputable def foldBase : Polynomial Nat := Polynomial.C 8

/-- Per-instruction state-growth budget, linear in the complete instruction-stream size. -/
noncomputable def foldGrowth : Polynomial Nat := Polynomial.C 20 * Polynomial.X + Polynomial.C 30

theorem initialFoldState_invariant_bound (source : List Instruction) :
    FoldStateInvariant (instructionListEncoding.inputSize source) initialFoldState ∧
      foldStateEncoding.inputSize initialFoldState ≤
        foldBase.eval (instructionListEncoding.inputSize source) := by
  constructor
  · constructor <;> simp [initialFoldState, mkFoldState]
  · rw [show initialFoldState = mkFoldState 0 0 true [] [] from rfl]
    rw [foldStateEncoding_inputSize]
    change 0 + 0 + pairEncoding.list.inputSize [] + pairEncoding.list.inputSize [] + 7 ≤ _
    rw [EncodedType.inputSize_list_nil]
    simp [foldBase]

theorem foldStep_invariant_growth
    (source : List Instruction) (state : FoldState) (instruction : Instruction)
    (invariant : FoldStateInvariant (instructionListEncoding.inputSize source) state)
    (instructionBound : instructionEncoding.inputSize instruction ≤
      instructionListEncoding.inputSize source) :
    FoldStateInvariant (instructionListEncoding.inputSize source) (foldStep (state, instruction)) ∧
      foldStateEncoding.inputSize (foldStep (state, instruction)) ≤
        foldStateEncoding.inputSize state +
          foldGrowth.eval (instructionListEncoding.inputSize source) := by
  rcases state with ⟨left, right, valid, forward, reverse⟩
  rcases invariant with ⟨leftBound, rightBound⟩
  change left ≤ instructionListEncoding.inputSize source at leftBound
  change right ≤ instructionListEncoding.inputSize source at rightBound
  cases instruction with
  | inl bounds =>
      rcases bounds with ⟨newLeft, newRight⟩
      have boundsBudget : newLeft + newRight + 4 ≤ instructionListEncoding.inputSize source := by
        simpa [instructionEncoding_inputSize_inl] using instructionBound
      change
        FoldStateInvariant (instructionListEncoding.inputSize source)
          (mkFoldState newLeft newRight true [] []) ∧
          foldStateEncoding.inputSize (mkFoldState newLeft newRight true [] []) ≤
            foldStateEncoding.inputSize (mkFoldState left right valid forward reverse) +
              foldGrowth.eval (instructionListEncoding.inputSize source)
      constructor
      · exact ⟨by change newLeft ≤ _; omega, by change newRight ≤ _; omega⟩
      · rw [foldStateEncoding_inputSize]
        change newLeft + newRight + pairEncoding.list.inputSize [] +
          pairEncoding.list.inputSize [] + 7 ≤ _
        rw [EncodedType.inputSize_list_nil]
        have stateSizeNonnegative : 0 ≤
            foldStateEncoding.inputSize (left, (right, (valid, (forward, reverse)))) :=
          Nat.zero_le _
        simp [foldGrowth]
        omega

  | inr pair =>
      rcases pair with ⟨sourceVertex, targetVertex⟩
      have pairBudget : sourceVertex + targetVertex + 4 ≤
          instructionListEncoding.inputSize source := by
        simpa [instructionEncoding_inputSize_inr] using instructionBound
      change
        FoldStateInvariant (instructionListEncoding.inputSize source)
          (mkFoldState left right
            (valid && pairWithinBoundsBool (left, right) (sourceVertex, targetVertex))
            (forward ++ [(sourceVertex, left + targetVertex)])
            (reverse ++ [(left + targetVertex, sourceVertex)])) ∧
          foldStateEncoding.inputSize
            (mkFoldState left right
              (valid && pairWithinBoundsBool (left, right) (sourceVertex, targetVertex))
              (forward ++ [(sourceVertex, left + targetVertex)])
              (reverse ++ [(left + targetVertex, sourceVertex)])) ≤
            foldStateEncoding.inputSize (mkFoldState left right valid forward reverse) +
              foldGrowth.eval (instructionListEncoding.inputSize source)
      constructor
      · exact ⟨by change left ≤ _; exact leftBound,
          by change right ≤ _; exact rightBound⟩
      · rw [foldStateEncoding_inputSize, foldStateEncoding_inputSize]
        rw [edgeListEncoding_inputSize_append_singleton,
          edgeListEncoding_inputSize_append_singleton]
        simp [foldGrowth]
        omega

/-- Direct TM realization of the typed fold, derived from its closed step compiler and growth proof. -/
theorem foldInstructions_tmPolyTime :
    TMPolyTimeMap instructionListEncoding foldStateEncoding
      (fun stream : List Instruction =>
        stream.foldl (fun state instruction => foldStep (state, instruction)) initialFoldState) := by
  rcases foldStep_tmPolyTime with ⟨stepTM⟩
  exact TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
    instructionEncoding foldStateEncoding foldStep initialFoldState stepTM
    foldBase foldGrowth FoldStateInvariant initialFoldState_invariant_bound foldStep_invariant_growth

/-- Reify a completed fold state to the structured existential EON target with direct-TM evidence. -/
theorem coreTargetOfFoldState_tmPolyTime :
    TMPolyTimeMap foldStateEncoding exactlyOneNeighborStructuredEncodedType coreTargetOfFoldState := by
  let X := foldStateEncoding
  let stateTailEncoding := EncodedType.prod natEncoding
    (EncodedType.prod EncodedType.bool (EncodedType.prod edgeListEncoding edgeListEncoding))
  let boolTailEncoding := EncodedType.prod EncodedType.bool
    (EncodedType.prod edgeListEncoding edgeListEncoding)
  let edgeListsEncoding := EncodedType.prod edgeListEncoding edgeListEncoding
  have leftTM : TMPolyTimeMap X natEncoding (fun state : FoldState => state.1) := by
    simpa [X, foldStateEncoding, stateTailEncoding] using
      TMPolyTimeMap.fst natEncoding stateTailEncoding
  have stateTailTM : TMPolyTimeMap X stateTailEncoding (fun state : FoldState => state.2) := by
    simpa [X, foldStateEncoding, stateTailEncoding] using
      TMPolyTimeMap.snd natEncoding stateTailEncoding
  have rightTM : TMPolyTimeMap X natEncoding (fun state : FoldState => state.2.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst natEncoding boolTailEncoding) stateTailTM
    simpa [Function.comp, X, stateTailEncoding, boolTailEncoding] using composed
  have boolTailTM : TMPolyTimeMap X boolTailEncoding (fun state : FoldState => state.2.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd natEncoding boolTailEncoding) stateTailTM
    simpa [Function.comp, X, stateTailEncoding, boolTailEncoding] using composed
  have edgeListsTM : TMPolyTimeMap X edgeListsEncoding
      (fun state : FoldState => state.2.2.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd EncodedType.bool edgeListsEncoding) boolTailTM
    simpa [Function.comp, X, boolTailEncoding, edgeListsEncoding] using composed
  have forwardTM : TMPolyTimeMap X edgeListEncoding
      (fun state : FoldState => state.2.2.2.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst edgeListEncoding edgeListEncoding) edgeListsTM
    simpa [Function.comp, X, edgeListsEncoding] using composed
  have reverseTM : TMPolyTimeMap X edgeListEncoding
      (fun state : FoldState => state.2.2.2.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd edgeListEncoding edgeListEncoding) edgeListsTM
    simpa [Function.comp, X, edgeListsEncoding] using composed
  have verticesInputTM : TMPolyTimeMap X pairEncoding
      (fun state : FoldState => (state.1, state.2.1)) :=
    TMPolyTimeMap.prod_mk leftTM rightTM
  have verticesTM : TMPolyTimeMap X natEncoding
      (fun state : FoldState => state.1 + state.2.1) := by
    have composed := TMPolyTimeMap.comp natAdd_tm_polytime verticesInputTM
    simpa [Function.comp] using composed
  have edgesInputTM : TMPolyTimeMap X (EncodedType.prod edgeListEncoding edgeListEncoding)
      (fun state : FoldState => (state.2.2.2.1, state.2.2.2.2)) :=
    TMPolyTimeMap.prod_mk forwardTM reverseTM
  have edgesTM : TMPolyTimeMap X edgeListEncoding
      (fun state : FoldState => state.2.2.2.1 ++ state.2.2.2.2) := by
    have composed := TMPolyTimeMap.comp (TMPolyTimeMap.list_append pairEncoding) edgesInputTM
    simpa [Function.comp] using composed
  have directedTM : TMPolyTimeMap X EncodedType.bool (fun _ : FoldState => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have graphPayloadTM : TMPolyTimeMap X (EncodedType.prod edgeListEncoding EncodedType.bool)
      (fun state : FoldState => (state.2.2.2.1 ++ state.2.2.2.2, false)) :=
    TMPolyTimeMap.prod_mk edgesTM directedTM
  have graphTupleTM : TMPolyTimeMap X graphTupleEncoding
      (fun state : FoldState =>
        (state.1 + state.2.1, (state.2.2.2.1 ++ state.2.2.2.2, false))) :=
    TMPolyTimeMap.prod_mk verticesTM graphPayloadTM
  have graphTM : TMPolyTimeMap X ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType
      (fun state : FoldState =>
        { vertices := state.1 + state.2.1
          edges := state.2.2.2.1 ++ state.2.2.2.2
          directed := false }) := by
    have composed := TMPolyTimeMap.comp graphOfTuple_tmPolyTime graphTupleTM
    simpa [Function.comp, graphOfTuple] using composed
  have requiredTM : TMPolyTimeMap X exactlyOneNeighborRequiredVerticesStructuredEncodedType
      (fun state : FoldState => List.range state.1) := by
    have composed := TMPolyTimeMap.comp natRange_tm_polytime leftTM
    simpa [Function.comp, exactlyOneNeighborRequiredVerticesStructuredEncodedType] using composed
  have targetTupleTM : TMPolyTimeMap X
      (EncodedType.prod ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType
        exactlyOneNeighborRequiredVerticesStructuredEncodedType)
      (fun state : FoldState =>
        ({ vertices := state.1 + state.2.1
           edges := state.2.2.2.1 ++ state.2.2.2.2
           directed := false }, List.range state.1)) :=
    TMPolyTimeMap.prod_mk graphTM requiredTM
  have assembled := TMPolyTimeMap.comp eonOfTuple_tmPolyTime targetTupleTM
  simpa [Function.comp, coreTargetOfFoldState, eonOfTuple] using assembled

/-- Direct projection of the completed fold's validity flag. -/
theorem foldStateValid_tmPolyTime :
    TMPolyTimeMap foldStateEncoding EncodedType.bool
      (fun state : FoldState => state.2.2.1) := by
  let stateTailEncoding := EncodedType.prod natEncoding
    (EncodedType.prod EncodedType.bool (EncodedType.prod edgeListEncoding edgeListEncoding))
  let boolTailEncoding := EncodedType.prod EncodedType.bool
    (EncodedType.prod edgeListEncoding edgeListEncoding)
  have stateTailTM : TMPolyTimeMap foldStateEncoding stateTailEncoding
      (fun state : FoldState => state.2) := by
    simpa [foldStateEncoding, stateTailEncoding] using
      TMPolyTimeMap.snd natEncoding stateTailEncoding
  have boolTailTM : TMPolyTimeMap foldStateEncoding boolTailEncoding
      (fun state : FoldState => state.2.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd natEncoding boolTailEncoding) stateTailTM
    simpa [Function.comp, stateTailEncoding, boolTailEncoding] using composed
  have assembled := TMPolyTimeMap.comp
    (TMPolyTimeMap.fst EncodedType.bool (EncodedType.prod edgeListEncoding edgeListEncoding)) boolTailTM
  simpa [Function.comp] using assembled

/-- The closed executable has direct-TM evidence assembled from instruction, fold, target, and guard machines. -/
theorem programRun_tmPolyTime :
    TMPolyTimeMap incidenceEncoding exactlyOneNeighborStructuredEncodedType programRun := by
  have foldedTM : TMPolyTimeMap incidenceEncoding foldStateEncoding foldedState := by
    have composed := TMPolyTimeMap.comp foldInstructions_tmPolyTime instructions_tmPolyTime
    simpa [Function.comp, foldedState] using composed
  have guardedPayloadTM : TMPolyTimeMap foldStateEncoding
      (EncodedType.prod EncodedType.bool exactlyOneNeighborStructuredEncodedType)
      (fun state : FoldState => (state.2.2.1, coreTargetOfFoldState state)) :=
    TMPolyTimeMap.prod_mk foldStateValid_tmPolyTime coreTargetOfFoldState_tmPolyTime
  have falseTM : TMPolyTimeMap exactlyOneNeighborStructuredEncodedType
      exactlyOneNeighborStructuredEncodedType (fun _ : ExactlyOneNeighborInput => noTarget) :=
    TMPolyTimeMap.const exactlyOneNeighborStructuredEncodedType
      exactlyOneNeighborStructuredEncodedType noTarget
  have trueTM : TMPolyTimeMap exactlyOneNeighborStructuredEncodedType
      exactlyOneNeighborStructuredEncodedType (fun target : ExactlyOneNeighborInput => target) :=
    TMPolyTimeMap.id exactlyOneNeighborStructuredEncodedType
  have guardedTM : TMPolyTimeMap
      (EncodedType.prod EncodedType.bool exactlyOneNeighborStructuredEncodedType)
      exactlyOneNeighborStructuredEncodedType
      (fun payload : Bool × ExactlyOneNeighborInput =>
        match payload.1 with
        | true => payload.2
        | false => noTarget) := by
    simpa using Karp21.graphBoolProduct_dispatch_tm_polytime
      exactlyOneNeighborStructuredEncodedType exactlyOneNeighborStructuredEncodedType falseTM trueTM
  have afterFoldTM := TMPolyTimeMap.comp guardedTM guardedPayloadTM
  have assembled := TMPolyTimeMap.comp afterFoldTM foldedTM
  convert assembled using 1
  funext input
  unfold programRun
  simp only [Function.comp_apply]
  cases (foldedState input).2.2.1 <;> simp


end IncidenceToExactlyOneNeighbor
end Domain
end ComplexityReduction
