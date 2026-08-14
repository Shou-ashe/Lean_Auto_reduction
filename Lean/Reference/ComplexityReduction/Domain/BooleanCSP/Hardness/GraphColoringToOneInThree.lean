/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP.Hardness.Cores
import ComplexityReduction.Domain.ThreeSATToGraphColoringStandardTM
import ComplexityReduction.Domain.GraphColoringToIncidenceProgram
import ComplexityReduction.Domain.RectangularCoordinates
import ComplexityReduction.Program.ContextListMap
import ComplexityReduction.Program.List
import ComplexityReduction.Certificate.NativeCookLevin
import ComplexityReduction.Certificate.CompletenessTransport
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatPair
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ListLookupTM
import Mathlib.Tactic

/-!
Direct-TM hardness of positive 1-IN-3 CSP.

For a graph with the fixed colour bound three, every vertex receives one
positive exactly-one constraint over its three colour bits.  For each stored
edge and colour, a fresh auxiliary bit turns

`1in3(x[u,c], x[v,c], auxiliary[e,c])`

into the condition that the two endpoints do not both use colour `c`.  The
auxiliary bit is true exactly when neither endpoint uses the colour.  This is
a direct reduction from the canonical fixed-three graph-colouring hub and,
after the existing structured-3SAT ingress, closes the native hardness leaf.
-/

namespace ComplexityReduction
namespace Domain
namespace BooleanCSP
namespace Hardness
namespace GraphColoringToOneInThree

open ComplexityReduction.CSP
open ComplexityReduction.Certificate
open ComplexityReduction.Encoding
open ComplexityReduction.Program
open ComplexityReduction.Combinatorics.Graph

abbrev sourceEncoding : EncodedType :=
  GraphColoringIR.lawfulRepresentation.encodedType

abbrev edgeEncoding : EncodedType :=
  ComplexityReduction.Combinatorics.Graph.edgeStructuredEncodedType

abbrev edgeColorEncoding : EncodedType :=
  RectangularCoordinates.coordinateEncodedType

abbrev edgeContextEncoding : EncodedType :=
  EncodedType.prod sourceEncoding edgeColorEncoding

abbrev constraintCodeEncoding : EncodedType :=
  Presentation.FiniteDomainCSPTable.constraintCodeEncodedType

abbrev formulaCodeEncoding : EncodedType :=
  Presentation.FiniteDomainCSPTable.formulaCodeEncodedType

/-! ### Collision-free variable keys -/

/-- A tagged key for the Boolean bit saying that `vertex` has `color`. -/
def colorVar (vertex color : Nat) : Nat :=
  Nat.pair 0 (Nat.pair vertex color)

/-- A disjoint tagged key for the edge/colour slack bit. -/
def auxiliaryVar (edgeIndex color : Nat) : Nat :=
  Nat.pair 1 (Nat.pair edgeIndex color)

@[simp] theorem colorVar_injective_iff {v c v' c' : Nat} :
    colorVar v c = colorVar v' c' ↔ v = v' ∧ c = c' := by
  simp [colorVar, Nat.pair_eq_pair]

theorem colorVar_ne_auxiliaryVar (v c edgeIndex color : Nat) :
    colorVar v c ≠ auxiliaryVar edgeIndex color := by
  simp [colorVar, auxiliaryVar, Nat.pair_eq_pair]

/-! ### Formula executable -/

/-- One vertex must choose exactly one of the three colours. -/
noncomputable def vertexConstraint (vertex : Nat) : Constraint oneInThreeCore :=
  oneInThreeConstraint (colorVar vertex 0) (colorVar vertex 1) (colorVar vertex 2)

/-- Total lookup of the stored edge at one rectangle coordinate. -/
def edgeAt (input : GraphColoringIR) (edgeIndex : Nat) : Nat × Nat :=
  input.graph.edges.getD edgeIndex (0, 0)

/-- One edge/colour constraint forbids both endpoints from using that colour. -/
noncomputable def edgeColorConstraint (input : GraphColoringIR)
    (coordinate : Nat × Nat) : Constraint oneInThreeCore :=
  let edge := edgeAt input coordinate.1
  oneInThreeConstraint
    (colorVar edge.1 coordinate.2)
    (colorVar edge.2 coordinate.2)
    (auxiliaryVar coordinate.1 coordinate.2)

/-- Row-major list of all stored-edge / fixed-three-colour coordinates. -/
def edgeColorCoordinates (input : GraphColoringIR) : List (Nat × Nat) :=
  RectangularCoordinates.familyExecutable (input.graph.edges.length, 3)

/-- The complete positive 1-IN-3 formula for fixed-three graph colouring. -/
noncomputable def executable (input : GraphColoringIR) : Formula oneInThreeCore :=
  (List.range input.graph.vertices).map vertexConstraint ++
    (edgeColorCoordinates input).map (edgeColorConstraint input)

/-! ### Canonical numeric payload -/

def constraintPayload (first second third : Nat) : Nat × List Nat :=
  (0, [first, second, third])

theorem relationCode_eq_zero (symbol : oneInThreeCore.Symbol) :
    Presentation.FiniteDomainCSPTable.relationCode oneInThreeCore symbol = 0 := by
  have bounded :=
    Presentation.FiniteDomainCSPTable.relationCode_lt_card oneInThreeCore symbol
  have lessThanOne :
      Presentation.FiniteDomainCSPTable.relationCode oneInThreeCore symbol < 1 := by
    simpa [oneInThreeCore] using bounded
  omega

theorem constraintCode_oneInThreeConstraint (first second third : Nat) :
    Presentation.FiniteDomainCSPTable.constraintCode
        (oneInThreeConstraint first second third) =
      constraintPayload first second third := by
  apply Prod.ext
  · simpa [Presentation.FiniteDomainCSPTable.constraintCode,
      constraintPayload] using relationCode_eq_zero ()
  · simp [Presentation.FiniteDomainCSPTable.constraintCode,
      constraintPayload, oneInThreeConstraint, Constraint.varsList,
      oneInThreeCore, StandardRelations.exactlyOne3Rel,
      StandardRelations.exactlyRel, BoolRel.ofPredicate,
      List.ofFn, Fin.foldr, Fin.foldr.loop]

def vertexConstraintCode (vertex : Nat) : Nat × List Nat :=
  constraintPayload (colorVar vertex 0) (colorVar vertex 1) (colorVar vertex 2)

def edgeColorConstraintCode (argument : GraphColoringIR × (Nat × Nat)) :
    Nat × List Nat :=
  let edge := edgeAt argument.1 argument.2.1
  constraintPayload
    (colorVar edge.1 argument.2.2)
    (colorVar edge.2 argument.2.2)
    (auxiliaryVar argument.2.1 argument.2.2)

def codeExecutable (input : GraphColoringIR) : List (Nat × List Nat) :=
  (List.range input.graph.vertices).map vertexConstraintCode ++
    (contextListMapExecutable (C := sourceEncoding) (X := edgeColorEncoding)
      (input, edgeColorCoordinates input)).map
      edgeColorConstraintCode

theorem codeExecutable_eq_formulaCode (input : GraphColoringIR) :
    codeExecutable input =
      Presentation.FiniteDomainCSPTable.formulaCode oneInThreeCore (executable input) := by
  rw [codeExecutable, executable, Presentation.FiniteDomainCSPTable.formulaCode,
    List.map_append, List.map_map, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro vertex _
    simp [vertexConstraintCode, vertexConstraint,
      constraintCode_oneInThreeConstraint]
  · rw [contextListMapExecutable_eq_map]
    change
      List.map edgeColorConstraintCode
          (List.map (fun coordinate => (input, coordinate)) (edgeColorCoordinates input)) =
        List.map (Presentation.FiniteDomainCSPTable.constraintCode ∘
          edgeColorConstraint input) (edgeColorCoordinates input)
    simp only [List.map_map]
    apply List.map_congr_left
    intro coordinate _
    simp [edgeColorConstraintCode, edgeColorConstraint,
      constraintCode_oneInThreeConstraint]

/-! ### Direct-TM proof -/

theorem constraintPayload_tmPolyTime {X : EncodedType}
    {first second third : X.Carrier → Nat}
    (hFirst : TMPolyTimeMap X EncodedType.nat first)
    (hSecond : TMPolyTimeMap X EncodedType.nat second)
    (hThird : TMPolyTimeMap X EncodedType.nat third) :
    TMPolyTimeMap X constraintCodeEncoding
      (fun input => constraintPayload (first input) (second input) (third input)) := by
  have hVariables := TMPolyTimeMap.list_cons_of hFirst
    (TMPolyTimeMap.list_cons_of hSecond
      (TMPolyTimeMap.list_singleton_of hThird))
  have relation : TMPolyTimeMap X EncodedType.nat
      (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (show EncodedType.nat.Carrier from (0 : Nat))
  simpa [constraintPayload, constraintCodeEncoding] using
    TMPolyTimeMap.prod_mk relation hVariables

theorem colorVar_tmPolyTime :
    TMPolyTimeMap (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.nat (fun input : Nat × Nat => colorVar input.1 input.2) := by
  have inner := TMPolyTimeMap.comp natPair_tm_polytime
    (TMPolyTimeMap.id (EncodedType.prod EncodedType.nat EncodedType.nat))
  have zero : TMPolyTimeMap
      (EncodedType.prod EncodedType.nat EncodedType.nat) EncodedType.nat
      (fun _ : Nat × Nat => (0 : Nat)) :=
    TMPolyTimeMap.const
      (EncodedType.prod EncodedType.nat EncodedType.nat) EncodedType.nat
      (show EncodedType.nat.Carrier from (0 : Nat))
  have outerInput := TMPolyTimeMap.prod_mk zero inner
  have outer := TMPolyTimeMap.comp natPair_tm_polytime outerInput
  simpa [colorVar, Function.comp] using outer

theorem auxiliaryVar_tmPolyTime :
    TMPolyTimeMap (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.nat (fun input : Nat × Nat => auxiliaryVar input.1 input.2) := by
  have inner := TMPolyTimeMap.comp natPair_tm_polytime
    (TMPolyTimeMap.id (EncodedType.prod EncodedType.nat EncodedType.nat))
  have one : TMPolyTimeMap
      (EncodedType.prod EncodedType.nat EncodedType.nat) EncodedType.nat
      (fun _ : Nat × Nat => (1 : Nat)) :=
    TMPolyTimeMap.const
      (EncodedType.prod EncodedType.nat EncodedType.nat) EncodedType.nat
      (show EncodedType.nat.Carrier from (1 : Nat))
  have outerInput := TMPolyTimeMap.prod_mk one inner
  have outer := TMPolyTimeMap.comp natPair_tm_polytime outerInput
  simpa [auxiliaryVar, Function.comp] using outer

theorem colorVar_const_tmPolyTime (color : Nat) :
    TMPolyTimeMap EncodedType.nat EncodedType.nat
      (fun vertex => colorVar vertex color) := by
  have input := TMPolyTimeMap.prod_mk (TMPolyTimeMap.id EncodedType.nat)
    (TMPolyTimeMap.const EncodedType.nat EncodedType.nat color)
  have output := TMPolyTimeMap.comp colorVar_tmPolyTime input
  simpa [Function.comp] using output

theorem vertexConstraintCode_tmPolyTime :
    TMPolyTimeMap EncodedType.nat constraintCodeEncoding vertexConstraintCode := by
  simpa [vertexConstraintCode] using constraintPayload_tmPolyTime
    (colorVar_const_tmPolyTime 0) (colorVar_const_tmPolyTime 1)
      (colorVar_const_tmPolyTime 2)

theorem edgeAt_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod sourceEncoding EncodedType.nat)
      edgeEncoding (fun argument : GraphColoringIR × Nat => edgeAt argument.1 argument.2) := by
  let X := EncodedType.prod sourceEncoding EncodedType.nat
  have inputGraph : TMPolyTimeMap X sourceEncoding
      (fun argument : GraphColoringIR × Nat => argument.1) := by
    simpa [X] using TMPolyTimeMap.fst sourceEncoding EncodedType.nat
  have edges : TMPolyTimeMap X (EncodedType.list edgeEncoding)
      (fun argument : GraphColoringIR × Nat => argument.1.graph.edges) := by
    have output := TMPolyTimeMap.comp
      GraphColoringToIncidence.edgeListProjection_tmPolyTime inputGraph
    simpa [Function.comp, X] using output
  have index : TMPolyTimeMap X EncodedType.nat
      (fun argument : GraphColoringIR × Nat => argument.2) := by
    simpa [X] using TMPolyTimeMap.snd sourceEncoding EncodedType.nat
  have lookupInput := TMPolyTimeMap.prod_mk edges index
  have output := TMPolyTimeMap.comp
    (Karp21.EncodedListLookup.getD_tm_polytime edgeEncoding ((0, 0) : Nat × Nat))
    lookupInput
  simpa [edgeAt, Function.comp, X] using output

theorem edgeColorConstraintCode_tmPolyTime :
    TMPolyTimeMap edgeContextEncoding constraintCodeEncoding edgeColorConstraintCode := by
  let X := edgeContextEncoding
  have source : TMPolyTimeMap X sourceEncoding
      (fun argument : GraphColoringIR × (Nat × Nat) => argument.1) := by
    simpa [X, edgeContextEncoding] using
      TMPolyTimeMap.fst sourceEncoding edgeColorEncoding
  have coordinate : TMPolyTimeMap X edgeColorEncoding
      (fun argument : GraphColoringIR × (Nat × Nat) => argument.2) := by
    simpa [X, edgeContextEncoding] using
      TMPolyTimeMap.snd sourceEncoding edgeColorEncoding
  have edgeIndex : TMPolyTimeMap X EncodedType.nat
      (fun argument : GraphColoringIR × (Nat × Nat) => argument.2.1) := by
    have output := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst EncodedType.nat EncodedType.nat) coordinate
    simpa [Function.comp, X, edgeColorEncoding] using output
  have color : TMPolyTimeMap X EncodedType.nat
      (fun argument : GraphColoringIR × (Nat × Nat) => argument.2.2) := by
    have output := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd EncodedType.nat EncodedType.nat) coordinate
    simpa [Function.comp, X, edgeColorEncoding] using output
  have edgeInput := TMPolyTimeMap.prod_mk source edgeIndex
  have edge := TMPolyTimeMap.comp edgeAt_tmPolyTime edgeInput
  have left : TMPolyTimeMap X EncodedType.nat
      (fun argument : GraphColoringIR × (Nat × Nat) =>
        (edgeAt argument.1 argument.2.1).1) := by
    have output := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst EncodedType.nat EncodedType.nat) edge
    simpa [Function.comp, edgeEncoding] using output
  have right : TMPolyTimeMap X EncodedType.nat
      (fun argument : GraphColoringIR × (Nat × Nat) =>
        (edgeAt argument.1 argument.2.1).2) := by
    have output := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd EncodedType.nat EncodedType.nat) edge
    simpa [Function.comp, edgeEncoding] using output
  have firstInput := TMPolyTimeMap.prod_mk left color
  have first := TMPolyTimeMap.comp colorVar_tmPolyTime firstInput
  have secondInput := TMPolyTimeMap.prod_mk right color
  have second := TMPolyTimeMap.comp colorVar_tmPolyTime secondInput
  have auxiliaryInput := TMPolyTimeMap.prod_mk edgeIndex color
  have auxiliary := TMPolyTimeMap.comp auxiliaryVar_tmPolyTime auxiliaryInput
  simpa [edgeColorConstraintCode] using
    constraintPayload_tmPolyTime first second auxiliary

theorem vertexCodeList_tmPolyTime :
    TMPolyTimeMap sourceEncoding formulaCodeEncoding
      (fun input : GraphColoringIR =>
        (List.range input.graph.vertices).map vertexConstraintCode) := by
  have count := GraphColoringToIncidence.vertexCountProjection_tmPolyTime
  have range := TMPolyTimeMap.comp Karp21.natRange_tm_polytime count
  have mapped := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_map vertexConstraintCode_tmPolyTime) range
  simpa [Function.comp, formulaCodeEncoding] using mapped

theorem edgeColorCoordinates_tmPolyTime :
    TMPolyTimeMap sourceEncoding
      (EncodedType.list edgeColorEncoding) edgeColorCoordinates := by
  have edgeCount := GraphColoringToIncidence.edgeCountProjection_tmPolyTime
  have three : TMPolyTimeMap sourceEncoding EncodedType.nat
      (fun _ : GraphColoringIR => (3 : Nat)) :=
    TMPolyTimeMap.const sourceEncoding EncodedType.nat
      (show EncodedType.nat.Carrier from (3 : Nat))
  have context := TMPolyTimeMap.prod_mk edgeCount three
  have output := TMPolyTimeMap.comp
    RectangularCoordinates.familyExecutable_tmPolyTime context
  simpa [edgeColorCoordinates, Function.comp,
    RectangularCoordinates.familyContextEncodedType,
    edgeColorEncoding] using output

theorem edgeCodeList_tmPolyTime :
    TMPolyTimeMap sourceEncoding formulaCodeEncoding
      (fun input : GraphColoringIR =>
        (contextListMapExecutable (C := sourceEncoding) (X := edgeColorEncoding)
          (input, edgeColorCoordinates input)).map
          edgeColorConstraintCode) := by
  have attachedInput := TMPolyTimeMap.prod_mk
    (TMPolyTimeMap.id sourceEncoding) edgeColorCoordinates_tmPolyTime
  have attached := TMPolyTimeMap.comp
    (contextListMapExecutable_tmPolyTime sourceEncoding edgeColorEncoding)
    attachedInput
  have mapped := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_map edgeColorConstraintCode_tmPolyTime) attached
  simpa [Function.comp, formulaCodeEncoding, edgeContextEncoding] using mapped

theorem codeExecutable_tmPolyTime :
    TMPolyTimeMap sourceEncoding formulaCodeEncoding codeExecutable := by
  have input := TMPolyTimeMap.prod_mk vertexCodeList_tmPolyTime edgeCodeList_tmPolyTime
  have output := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append constraintCodeEncoding) input
  simpa [codeExecutable, Function.comp, formulaCodeEncoding] using output

theorem executable_tmPolyTime :
    TMPolyTimeMap sourceEncoding
      (Presentation.FiniteDomainCSPTable.encodedType oneInThreeCore)
      executable :=
  Presentation.FiniteDomainCSPTable.formula_tmPolyTime_of_code
    codeExecutable_tmPolyTime codeExecutable_eq_formulaCode

/-! ### Semantics -/

def forwardAssignment (input : GraphColoringIR) (colorOf : Nat → Nat) : SAT.Assignment :=
  fun key =>
    let decoded := Nat.unpair key
    if decoded.1 = 0 then
      let vertexColor := Nat.unpair decoded.2
      decide (colorOf vertexColor.1 = vertexColor.2)
    else if decoded.1 = 1 then
      let edgeColor := Nat.unpair decoded.2
      let edge := edgeAt input edgeColor.1
      decide (colorOf edge.1 ≠ edgeColor.2 ∧ colorOf edge.2 ≠ edgeColor.2)
    else false

@[simp] theorem forwardAssignment_colorVar (input : GraphColoringIR)
    (colorOf : Nat → Nat) (vertex color : Nat) :
    forwardAssignment input colorOf (colorVar vertex color) =
      decide (colorOf vertex = color) := by
  simp [forwardAssignment, colorVar, Nat.unpair_pair]

@[simp] theorem forwardAssignment_auxiliaryVar (input : GraphColoringIR)
    (colorOf : Nat → Nat) (edgeIndex color : Nat) :
    forwardAssignment input colorOf (auxiliaryVar edgeIndex color) =
      decide (colorOf (edgeAt input edgeIndex).1 ≠ color ∧
        colorOf (edgeAt input edgeIndex).2 ≠ color) := by
  simp [forwardAssignment, auxiliaryVar, Nat.unpair_pair]

theorem weightOne_vertex (value : Nat) (bound : value < 3) :
    (if decide (value = 0) then 1 else 0) +
      (if decide (value = 1) then 1 else 0) +
      (if decide (value = 2) then 1 else 0) = 1 := by
  interval_cases value <;> decide

theorem weightOne_edge (left right color : Nat) (different : left ≠ right) :
    (if decide (left = color) then 1 else 0) +
      (if decide (right = color) then 1 else 0) +
      (if decide (left ≠ color ∧ right ≠ color) then 1 else 0) = 1 := by
  by_cases hl : left = color <;> by_cases hr : right = color
  · exact False.elim (different (hl.trans hr.symm))
  · simp [hl, hr]
  · simp [hl, hr]
  · simp [hl, hr]

theorem executable_satisfies_forward {input : GraphColoringIR}
    {colorOf : Nat → Nat} (proper : ProperColoring input.graph 3 colorOf) :
    Formula.Satisfies (executable input) (forwardAssignment input colorOf) := by
  rw [executable, Formula.satisfies_append]
  constructor
  · intro constraint member
    rcases List.mem_map.mp member with ⟨vertex, vertexMember, rfl⟩
    change Constraint.Satisfies
      (oneInThreeConstraint (colorVar vertex 0) (colorVar vertex 1)
        (colorVar vertex 2)) (forwardAssignment input colorOf)
    rw [oneInThreeConstraint_satisfies_iff]
    simpa using weightOne_vertex (colorOf vertex)
      (proper.1 vertex (List.mem_range.mp vertexMember))
  · intro constraint member
    rcases List.mem_map.mp member with ⟨coordinate, coordinateMember, rfl⟩
    change Constraint.Satisfies
      (oneInThreeConstraint
        (colorVar (edgeAt input coordinate.1).1 coordinate.2)
        (colorVar (edgeAt input coordinate.1).2 coordinate.2)
        (auxiliaryVar coordinate.1 coordinate.2))
      (forwardAssignment input colorOf)
    rw [oneInThreeConstraint_satisfies_iff]
    have coordinateBounds : coordinate.1 < input.graph.edges.length ∧ coordinate.2 < 3 := by
      rw [edgeColorCoordinates, RectangularCoordinates.familyExecutable_eq_flatMap] at coordinateMember
      rcases List.mem_flatMap.mp coordinateMember with ⟨edgeIndex, edgeMember, colorMember⟩
      rcases List.mem_map.mp colorMember with ⟨color, colorRange, equality⟩
      subst coordinate
      simpa using And.intro (List.mem_range.mp edgeMember) (List.mem_range.mp colorRange)
    have edgeMember : edgeAt input coordinate.1 ∈ input.graph.edges := by
      rw [edgeAt, List.getD_eq_getElem input.graph.edges (0, 0) coordinateBounds.1]
      exact List.getElem_mem _
    have different := proper.2 (edgeAt input coordinate.1) edgeMember
    simpa [edgeColorConstraint] using
      weightOne_edge (colorOf (edgeAt input coordinate.1).1)
        (colorOf (edgeAt input coordinate.1).2) coordinate.2 different

/-- Read the unique selected colour from a satisfying vertex triple. -/
def reverseColor (assignment : SAT.Assignment) (vertex : Nat) : Nat :=
  if assignment (colorVar vertex 0) then 0
  else if assignment (colorVar vertex 1) then 1 else 2

theorem reverseColor_lt_three (assignment : SAT.Assignment) (vertex : Nat) :
    reverseColor assignment vertex < 3 := by
  unfold reverseColor
  split
  · decide
  · split <;> decide

theorem selected_color_true {assignment : SAT.Assignment} {vertex : Nat}
    (weight :
      (if assignment (colorVar vertex 0) then 1 else 0) +
        (if assignment (colorVar vertex 1) then 1 else 0) +
        (if assignment (colorVar vertex 2) then 1 else 0) = 1) :
    assignment (colorVar vertex (reverseColor assignment vertex)) = true := by
  cases h0 : assignment (colorVar vertex 0) <;>
    cases h1 : assignment (colorVar vertex 1) <;>
    cases h2 : assignment (colorVar vertex 2) <;>
    simp_all [reverseColor]

theorem weightOne_not_both (first second third : Bool) :
    (if first then 1 else 0) + (if second then 1 else 0) +
      (if third then 1 else 0) = 1 → ¬ (first = true ∧ second = true) := by
  cases first <;> cases second <;> cases third <;> decide

theorem executable_satisfies_reverse {input : GraphColoringIR}
    {assignment : SAT.Assignment}
    (wellFormed : WellFormed input.graph)
    (satisfies : Formula.Satisfies (executable input) assignment) :
    ProperColoring input.graph 3 (reverseColor assignment) := by
  constructor
  · intro vertex _
    exact reverseColor_lt_three assignment vertex
  · intro edge edgeMember
    let edgeIndex := input.graph.edges.idxOf edge
    have edgeIndexBound : edgeIndex < input.graph.edges.length :=
      List.idxOf_lt_length_iff.mpr edgeMember
    have edgeAtEquality : edgeAt input edgeIndex = edge := by
      rw [edgeAt, List.getD_eq_getElem input.graph.edges (0, 0) edgeIndexBound]
      exact List.getElem_idxOf edgeIndexBound
    have endpointBounds : edge.1 < input.graph.vertices ∧ edge.2 < input.graph.vertices :=
      wellFormed edge edgeMember
    intro equalColors
    let color := reverseColor assignment edge.1
    have colorBound : color < 3 := reverseColor_lt_three assignment edge.1
    have coordinateMember : (edgeIndex, color) ∈ edgeColorCoordinates input := by
      rw [edgeColorCoordinates, RectangularCoordinates.familyExecutable_eq_flatMap]
      exact List.mem_flatMap.mpr ⟨edgeIndex, List.mem_range.mpr edgeIndexBound,
        List.mem_map.mpr ⟨color, List.mem_range.mpr colorBound, rfl⟩⟩
    have edgeConstraintSatisfies : Constraint.Satisfies
        (edgeColorConstraint input (edgeIndex, color)) assignment := by
      apply satisfies
      rw [executable]
      exact List.mem_append.mpr (Or.inr
        (List.mem_map.mpr ⟨(edgeIndex, color), coordinateMember, rfl⟩))
    have edgeWeight := (oneInThreeConstraint_satisfies_iff _ _ _ assignment).1
      edgeConstraintSatisfies
    have leftTrue : assignment (colorVar edge.1 color) = true := by
      exact selected_color_true (vertex := edge.1) (assignment := assignment) (by
        have vertexConstraintSatisfies : Constraint.Satisfies
            (vertexConstraint edge.1) assignment := by
          apply satisfies
          rw [executable]
          exact List.mem_append.mpr (Or.inl
            (List.mem_map.mpr ⟨edge.1, List.mem_range.mpr
              endpointBounds.1, rfl⟩))
        exact (oneInThreeConstraint_satisfies_iff _ _ _ assignment).1
          vertexConstraintSatisfies)
    have rightTrue : assignment (colorVar edge.2 color) = true := by
      have colorEquality : reverseColor assignment edge.2 = color := by
        dsimp [color]
        exact equalColors.symm
      rw [← colorEquality]
      exact selected_color_true (vertex := edge.2) (assignment := assignment) (by
        have vertexConstraintSatisfies : Constraint.Satisfies
            (vertexConstraint edge.2) assignment := by
          apply satisfies
          rw [executable]
          exact List.mem_append.mpr (Or.inl
            (List.mem_map.mpr ⟨edge.2, List.mem_range.mpr
              endpointBounds.2, rfl⟩))
        exact (oneInThreeConstraint_satisfies_iff _ _ _ assignment).1
          vertexConstraintSatisfies)
    have notBoth := weightOne_not_both
      (assignment (colorVar (edgeAt input edgeIndex).1 color))
      (assignment (colorVar (edgeAt input edgeIndex).2 color))
      (assignment (auxiliaryVar edgeIndex color)) edgeWeight
    rw [edgeAtEquality] at notBoth
    exact notBoth ⟨leftTrue, rightTrue⟩

theorem executable_correct_of_colors_three (input : GraphColoringIR)
    (wellFormed : WellFormed input.graph) (colors : input.colors = 3) :
    Formula.Satisfiable (executable input) ↔ GraphColoringIR.IsColorable input := by
  constructor
  · rintro ⟨assignment, satisfies⟩
    refine ⟨reverseColor assignment, ?_⟩
    simpa [colors] using executable_satisfies_reverse (input := input) wellFormed satisfies
  · rintro ⟨colorOf, proper⟩
    refine ⟨forwardAssignment input colorOf, ?_⟩
    have properThree : ProperColoring input.graph 3 colorOf := by
      simpa [colors] using proper
    exact executable_satisfies_forward (input := input) properThree

/-! ### Closed native hardness -/

theorem threeSATBoundedGraph_wellFormed (formula : SAT.ThreeCNF) :
    WellFormed (ThreeSATToGraphColoringStandardTM.executable formula).graph := by
  let n := ComplexityReduction.Karp21.threeCNFStructuredEncodedType.inputSize formula
  let m := formula.clauses.length
  intro edge edgeMember
  change edge.1 <
      ComplexityReduction.Karp21.ChromaticNumber.threeSATBoundedVertexCount formula ∧
    edge.2 <
      ComplexityReduction.Karp21.ChromaticNumber.threeSATBoundedVertexCount formula
  change edge ∈
      (ComplexityReduction.Karp21.ChromaticNumber.paletteEdges ++
        ComplexityReduction.Karp21.ChromaticNumber.variableEdges n) ++
        ComplexityReduction.Karp21.ChromaticNumber.clauseEdgesFrom n 0 formula.clauses
      at edgeMember
  rw [List.mem_append] at edgeMember
  rcases edgeMember with paletteOrVariable | clause
  · rw [List.mem_append] at paletteOrVariable
    rcases paletteOrVariable with palette | variableMember
    · simp [ComplexityReduction.Karp21.ChromaticNumber.paletteEdges] at palette
      rcases palette with rfl | rfl | rfl
      all_goals simp [ComplexityReduction.Karp21.ChromaticNumber.threeSATBoundedVertexCount,
        ComplexityReduction.Karp21.ChromaticNumber.textbookVertexCount,
        ComplexityReduction.Karp21.ChromaticNumber.variableLimit,
        ComplexityReduction.Karp21.ChromaticNumber.baseVertex,
        ComplexityReduction.Karp21.ChromaticNumber.trueVertex,
        ComplexityReduction.Karp21.ChromaticNumber.falseVertex] <;> omega
    · rcases List.mem_flatMap.mp variableMember with ⟨index, indexMember, edgeFor⟩
      have indexBound : index < n := List.mem_range.mp indexMember
      simp [ComplexityReduction.Karp21.ChromaticNumber.variableEdgesFor] at edgeFor
      rcases edgeFor with rfl | rfl | rfl
      all_goals simp [ComplexityReduction.Karp21.ChromaticNumber.threeSATBoundedVertexCount,
        ComplexityReduction.Karp21.ChromaticNumber.textbookVertexCount,
        ComplexityReduction.Karp21.ChromaticNumber.variableLimit,
        ComplexityReduction.Karp21.ChromaticNumber.posVertex,
        ComplexityReduction.Karp21.ChromaticNumber.negVertex,
        ComplexityReduction.Karp21.ChromaticNumber.baseVertex, n, m] <;> omega
  · have clauseBound :
        ∀ current ∈ formula.clauses, ∀ literal ∈ current, literal.var < n := by
      intro current currentMember literal literalMember
      simpa [n] using
        ComplexityReduction.Karp21.ChromaticNumber.threeSATBounded_var_lt
          formula current currentMember literal literalMember
    have endpointBound :
        ∀ {start : Nat} {clauses : List SAT.Clause} {candidate : Nat × Nat},
          start + clauses.length ≤ m →
          (∀ current ∈ clauses, ∀ literal ∈ current, literal.var < n) →
          candidate ∈
              ComplexityReduction.Karp21.ChromaticNumber.clauseEdgesFrom n start clauses →
            candidate.1 <
                ComplexityReduction.Karp21.ChromaticNumber.textbookVertexCount n m ∧
              candidate.2 <
                ComplexityReduction.Karp21.ChromaticNumber.textbookVertexCount n m := by
      intro start clauses candidate suffixBound bounded member
      induction clauses generalizing start candidate with
      | nil => simp [ComplexityReduction.Karp21.ChromaticNumber.clauseEdgesFrom] at member
      | cons current rest inductionHypothesis =>
          rw [ComplexityReduction.Karp21.ChromaticNumber.clauseEdgesFrom,
            List.mem_append] at member
          rcases member with currentMember | restMember
          · unfold ComplexityReduction.Karp21.ChromaticNumber.clauseEdgesFor at currentMember
            cases padded : ComplexityReduction.Karp21.ChromaticNumber.paddedClause current with
            | none =>
                simp [padded] at currentMember
                subst candidate
                simp [ComplexityReduction.Karp21.ChromaticNumber.baseVertex,
                  ComplexityReduction.Karp21.ChromaticNumber.textbookVertexCount,
                  ComplexityReduction.Karp21.ChromaticNumber.variableLimit]
            | some triple =>
                rcases triple with ⟨first, second, third⟩
                have firstBound : first.var < n := bounded current (by simp) first
                  (ComplexityReduction.Karp21.ChromaticNumber.paddedClause_left_mem padded)
                have secondBound : second.var < n := bounded current (by simp) second
                  (ComplexityReduction.Karp21.ChromaticNumber.paddedClause_middle_mem padded)
                have thirdBound : third.var < n := bounded current (by simp) third
                  (ComplexityReduction.Karp21.ChromaticNumber.paddedClause_right_mem padded)
                have startBound : start < m := by
                  simp only [List.length_cons] at suffixBound
                  omega
                have literalVertexBound (literal : SAT.Literal) (bound : literal.var < n) :
                    ComplexityReduction.Karp21.ChromaticNumber.literalVertex literal <
                      ComplexityReduction.Karp21.ChromaticNumber.variableLimit n := by
                  cases literal with
                  | mk var negative =>
                      cases negative
                      · exact ComplexityReduction.Karp21.ChromaticNumber.posVertex_lt_variableLimit
                          bound
                      · exact ComplexityReduction.Karp21.ChromaticNumber.negVertex_lt_variableLimit
                          bound
                have firstVertexBound := literalVertexBound first firstBound
                have secondVertexBound := literalVertexBound second secondBound
                have thirdVertexBound := literalVertexBound third thirdBound
                simp [padded,
                  ComplexityReduction.Karp21.ChromaticNumber.clauseGadgetEdges] at currentMember
                rcases currentMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
                · exact ⟨
                    ComplexityReduction.Karp21.ChromaticNumber.clauseA0_lt_textbookVertexCount
                      startBound,
                    ComplexityReduction.Karp21.ChromaticNumber.clauseA1_lt_textbookVertexCount
                      startBound⟩
                · exact ⟨
                    ComplexityReduction.Karp21.ChromaticNumber.clauseA0_lt_textbookVertexCount
                      startBound,
                    ComplexityReduction.Karp21.ChromaticNumber.clauseA2_lt_textbookVertexCount
                      startBound⟩
                · exact ⟨
                    ComplexityReduction.Karp21.ChromaticNumber.clauseA3_lt_textbookVertexCount
                      startBound,
                    by simp [ComplexityReduction.Karp21.ChromaticNumber.trueVertex,
                      ComplexityReduction.Karp21.ChromaticNumber.textbookVertexCount,
                      ComplexityReduction.Karp21.ChromaticNumber.variableLimit]; omega⟩
                · exact ⟨
                    ComplexityReduction.Karp21.ChromaticNumber.clauseA1_lt_textbookVertexCount
                      startBound,
                    by simp [ComplexityReduction.Karp21.ChromaticNumber.trueVertex,
                      ComplexityReduction.Karp21.ChromaticNumber.textbookVertexCount,
                      ComplexityReduction.Karp21.ChromaticNumber.variableLimit]; omega⟩
                · exact ⟨
                    ComplexityReduction.Karp21.ChromaticNumber.clauseA2_lt_textbookVertexCount
                      startBound,
                    ComplexityReduction.Karp21.ChromaticNumber.clauseA3_lt_textbookVertexCount
                      startBound⟩
                · exact ⟨firstVertexBound.trans (by simp
                    [ComplexityReduction.Karp21.ChromaticNumber.textbookVertexCount]; omega),
                    ComplexityReduction.Karp21.ChromaticNumber.clauseA2_lt_textbookVertexCount
                      startBound⟩
                · exact ⟨firstVertexBound.trans (by simp
                    [ComplexityReduction.Karp21.ChromaticNumber.textbookVertexCount]; omega),
                    ComplexityReduction.Karp21.ChromaticNumber.clauseA3_lt_textbookVertexCount
                      startBound⟩
                · exact ⟨secondVertexBound.trans (by simp
                    [ComplexityReduction.Karp21.ChromaticNumber.textbookVertexCount]; omega),
                    ComplexityReduction.Karp21.ChromaticNumber.clauseA0_lt_textbookVertexCount
                      startBound⟩
                · exact ⟨thirdVertexBound.trans (by simp
                    [ComplexityReduction.Karp21.ChromaticNumber.textbookVertexCount]; omega),
                    ComplexityReduction.Karp21.ChromaticNumber.clauseA1_lt_textbookVertexCount
                      startBound⟩
          · apply inductionHypothesis (start := start + 1)
            · simp only [List.length_cons] at suffixBound
              omega
            · intro current currentMember literal literalMember
              exact bounded current (by simp [currentMember]) literal literalMember
            · exact restMember
    have bound := endpointBound (start := 0) (clauses := formula.clauses)
      (candidate := edge) (by simp [m]) clauseBound clause
    simpa [ComplexityReduction.Karp21.ChromaticNumber.threeSATBoundedVertexCount,
      n, m] using bound

noncomputable def threeSATExecutable (formula : SAT.ThreeCNF) :
    Formula oneInThreeCore :=
  executable (ThreeSATToGraphColoringStandardTM.executable formula)

theorem threeSATExecutable_tmPolyTime :
    TMPolyTimeMap
      Problems.Karp21.Satisfiability.threeSATStructuredProblem.representation.encodedType
      (cspOf oneInThreeCore).representation.encodedType
      threeSATExecutable := by
  have output := TMPolyTimeMap.comp executable_tmPolyTime
    ThreeSATToGraphColoringStandardTM.executable_tmPolyTime
  simpa [threeSATExecutable, Function.comp,
    Problems.Karp21.Satisfiability.threeSATStructuredProblem,
    Problems.Karp21.Satisfiability.threeSATStructuredPresentation,
    cspOf, Presentation.FiniteDomainCSPTable.presentedProblem,
    Presentation.FiniteDomainCSPTable.lawfulRepresentation] using output

noncomputable def reduction :
    CertifiedReduction Problems.Karp21.Satisfiability.threeSATStructuredProblem
      (cspOf oneInThreeCore) := by
  let program : PolyProg
      Problems.Karp21.Satisfiability.threeSATStructuredProblem.representation
      (cspOf oneInThreeCore).representation :=
    .atom (Primitive.ofTMPolyTime threeSATExecutable threeSATExecutable_tmPolyTime)
  refine ⟨program, ?_⟩
  intro formula
  have graphCorrect := ThreeSATToGraphColoringStandardTM.executable_correct formula
  have cspCorrect := executable_correct_of_colors_three
    (ThreeSATToGraphColoringStandardTM.executable formula)
    (threeSATBoundedGraph_wellFormed formula) rfl
  simpa [cspOf_accepts, threeSATExecutable, program] using
    graphCorrect.trans cspCorrect.symm

theorem oneInThreeCoreNPHard : NativeTMNPHard (cspOf oneInThreeCore) :=
  NativeTMNPHard.ofCompleteAlongPath
    NativeCookLevin.canonicalThreeSATNativeCompleteness
    (CertifiedPath.step reduction)

assert_standard_axioms
  executable_tmPolyTime,
  executable_correct_of_colors_three,
  threeSATBoundedGraph_wellFormed,
  threeSATExecutable_tmPolyTime,
  reduction,
  oneInThreeCoreNPHard

end GraphColoringToOneInThree
end Hardness
end BooleanCSP
end Domain
end ComplexityReduction
