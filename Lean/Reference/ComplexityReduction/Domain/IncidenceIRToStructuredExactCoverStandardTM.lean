/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.IncidenceIRToStructuredExactCover
import ComplexityReduction.Domain.IncidenceIRValidationStandardTM
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Reduction
import ComplexityReduction.Program.ContextListMap
import ComplexityReduction.Protocol.ComponentResolver
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.BoolDispatch
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatRange
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SetCovering.Base

/-!
The standard-audited direct-TM companion for the canonical
`IncidenceIR -> structured Exact Cover` egress.

Its only domain computation groups the left members of one retained right
identity.  The outer range/map assembly and the total malformed-input guard
reuse generic direct-TM combinators and the canonical incidence validation
component.  The resulting primitive, program, certificate, and resolver are
all indexed by the one guarded executable from the semantic leaf.
-/

namespace ComplexityReduction
namespace Domain
namespace IncidenceIRToStructuredExactCoverStandardTM

open ComplexityReduction
open ComplexityReduction.Combinatorics
open Certificate
open Encoding
open Program

/-- The canonical typed incidence exact-cover hub. -/
abbrev sourceProblem : PresentedProblem :=
  IncidenceIR.exactCoverProblem

/-- The public structured Exact-Cover endpoint. -/
abbrev targetProblem : PresentedProblem :=
  Presentation.SetSystem.exactCoverStructuredProblem

/-- The direct-TM encoding of one retained raw incidence pair. -/
abbrev pairEncoding : EncodedType :=
  IncidenceIRValidation.pairEncoding

/-- The direct-TM encoding of the ordered raw pair payload. -/
abbrev pairListEncoding : EncodedType :=
  IncidenceIRValidation.pairListEncoding

/-- The output encoding of one materialized set. -/
abbrev setEncoding : EncodedType :=
  EncodedType.list EncodedType.nat

/-- A scan item retains one right identity beside the raw pair currently inspected. -/
abbrev memberContextEncoding : EncodedType :=
  EncodedType.prod EncodedType.nat pairEncoding

/-- The member scan fold receives its list accumulator and one retained context item. -/
abbrev memberStepInputEncoding : EncodedType :=
  EncodedType.prod setEncoding memberContextEncoding

/-- The outer map receives the pair payload before the retained right identity. -/
abbrev outerMemberInputEncoding : EncodedType :=
  EncodedType.prod pairListEncoding EncodedType.nat

/-- Decide whether a raw pair belongs to the retained right identity. -/
def pairHasRightBool (input : Nat × (Nat × Nat)) : Bool :=
  decide (input.2.2 = input.1)

/-- The executable Boolean tag has exactly the intended equality semantics. -/
theorem pairHasRightBool_eq_true_iff (input : Nat × (Nat × Nat)) :
    pairHasRightBool input = true ↔ input.2.2 = input.1 := by
  simp [pairHasRightBool]

/-- Append the raw pair's left member exactly when it belongs to the selected right identity. -/
def membersStep (input : List Nat × (Nat × (Nat × Nat))) : List Nat :=
  if pairHasRightBool input.2 then input.1 ++ [input.2.2.1] else input.1

private theorem list_inputSize_append (X : EncodedType) :
    ∀ (first second : List X.Carrier),
      (EncodedType.list X).inputSize (first ++ second) =
        (EncodedType.list X).inputSize first + (EncodedType.list X).inputSize second
  | [], second => by
      simp [EncodedType.inputSize, EncodedType.list]
  | first :: rest, second => by
      rw [List.cons_append, EncodedType.inputSize_list_cons,
        EncodedType.inputSize_list_cons, list_inputSize_append X rest second]
      omega

private theorem set_inputSize_append_singleton (members : List Nat) (member : Nat) :
    setEncoding.inputSize (members ++ [member]) =
      setEncoding.inputSize members + EncodedType.nat.inputSize member + 1 := by
  have h := list_inputSize_append EncodedType.nat members [member]
  simpa [setEncoding, EncodedType.inputSize_list_cons,
    EncodedType.inputSize_list_nil] using h

/-- Direct-TM evidence for the equality tag used by one member scan step. -/
theorem pairHasRightBool_tmPolyTime :
    TMPolyTimeMap memberContextEncoding EncodedType.bool pairHasRightBool := by
  let X := memberContextEncoding
  have hRight : TMPolyTimeMap X EncodedType.nat (fun input : X.Carrier => input.1) := by
    simpa [X, memberContextEncoding] using
      TMPolyTimeMap.fst EncodedType.nat pairEncoding
  have hPair : TMPolyTimeMap X pairEncoding (fun input : X.Carrier => input.2) := by
    simpa [X, memberContextEncoding] using
      TMPolyTimeMap.snd EncodedType.nat pairEncoding
  have hPairRight : TMPolyTimeMap X EncodedType.nat (fun input : X.Carrier => input.2.2) := by
    have h := TMPolyTimeMap.comp (TMPolyTimeMap.snd EncodedType.nat EncodedType.nat) hPair
    simpa [Function.comp, X] using h
  have hInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : X.Carrier => (input.2.2, input.1)) :=
    TMPolyTimeMap.prod_mk hPairRight hRight
  have hOut := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hInput
  simpa [pairHasRightBool, Function.comp] using hOut

/-- Direct-TM realization of one append-or-keep member scan step. -/
theorem membersStep_tmPolyTime :
    TMPolyTimeMap memberStepInputEncoding setEncoding membersStep := by
  let X := memberStepInputEncoding
  have hMembers : TMPolyTimeMap X setEncoding (fun input : X.Carrier => input.1) := by
    simpa [X, memberStepInputEncoding] using
      TMPolyTimeMap.fst setEncoding memberContextEncoding
  have hContext : TMPolyTimeMap X memberContextEncoding (fun input : X.Carrier => input.2) := by
    simpa [X, memberStepInputEncoding] using
      TMPolyTimeMap.snd setEncoding memberContextEncoding
  have hLeft : TMPolyTimeMap X EncodedType.nat (fun input : X.Carrier => input.2.2.1) := by
    have hPair := TMPolyTimeMap.comp (TMPolyTimeMap.snd EncodedType.nat pairEncoding)
      hContext
    have h := TMPolyTimeMap.comp (TMPolyTimeMap.fst EncodedType.nat EncodedType.nat) hPair
    simpa [Function.comp, X] using h
  have hTag : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier => pairHasRightBool input.2) := by
    have h := TMPolyTimeMap.comp pairHasRightBool_tmPolyTime hContext
    simpa [Function.comp, X] using h
  have hSingleton : TMPolyTimeMap X setEncoding (fun input : X.Carrier => [input.2.2.1]) := by
    have h := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton EncodedType.nat) hLeft
    simpa [Function.comp, setEncoding] using h
  have hAppendInput : TMPolyTimeMap X (EncodedType.prod setEncoding setEncoding)
      (fun input : X.Carrier => (input.1, [input.2.2.1])) :=
    TMPolyTimeMap.prod_mk hMembers hSingleton
  have hAppend : TMPolyTimeMap X setEncoding
      (fun input : X.Carrier =>
        List.append (show List Nat from input.1) ([input.2.2.1] : List Nat)) := by
    have h := TMPolyTimeMap.comp (TMPolyTimeMap.list_append EncodedType.nat) hAppendInput
    simpa [Function.comp, setEncoding] using h
  have hTagged : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun input : X.Carrier => (pairHasRightBool input.2, input)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranch : TMPolyTimeMap (EncodedType.prod EncodedType.bool X) setEncoding
      (fun input : Bool × X.Carrier =>
        match input.1 with
        | true => List.append (show List Nat from input.2.1)
            ([input.2.2.2.1] : List Nat)
        | false => input.2.1) :=
    boolProduct_dispatch_tm_polytime X setEncoding
      (fFalse := fun input => input.1)
      (fTrue := fun input =>
        List.append (show List Nat from input.1) ([input.2.2.1] : List Nat)) hMembers hAppend
  have hOut := TMPolyTimeMap.comp hBranch hTagged
  convert hOut using 1
  funext input
  rcases input with ⟨members, right, left, pairRight⟩
  cases h : pairHasRightBool (right, (left, pairRight))
  · simp [Function.comp, membersStep, h]
  · simp [Function.comp, membersStep, h]
    rfl

private theorem member_left_inputSize_le (item : memberContextEncoding.Carrier) :
    EncodedType.nat.inputSize item.2.1 ≤ memberContextEncoding.inputSize item := by
  rcases item with ⟨right, left, pairRight⟩
  simp [memberContextEncoding, pairEncoding, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat]
  omega

private theorem membersStep_growth (source : List memberContextEncoding.Carrier)
    (members : setEncoding.Carrier) (item : memberContextEncoding.Carrier)
    (itemBound : memberContextEncoding.inputSize item ≤
      (EncodedType.list memberContextEncoding).inputSize source) :
    setEncoding.inputSize (membersStep (members, item)) ≤
      setEncoding.inputSize members +
        (Polynomial.X + Polynomial.C 3).eval
          ((EncodedType.list memberContextEncoding).inputSize source) := by
  by_cases selected : item.2.2 = item.1
  · have hLeft : EncodedType.nat.inputSize item.2.1 ≤
        (EncodedType.list memberContextEncoding).inputSize source :=
      (member_left_inputSize_le item).trans itemBound
    have tagTrue : pairHasRightBool item = true := by
      exact (pairHasRightBool_eq_true_iff item).mpr selected
    rw [membersStep, tagTrue]
    change setEncoding.inputSize
        (List.append (show List Nat from members) ([item.2.1] : List Nat)) ≤ _
    have hSum : setEncoding.inputSize members + EncodedType.nat.inputSize item.2.1 + 1 ≤
        setEncoding.inputSize members +
          (Polynomial.X + Polynomial.C 3).eval
            ((EncodedType.list memberContextEncoding).inputSize source) := by
      have hGrow : EncodedType.nat.inputSize item.2.1 + 1 ≤
          (Polynomial.X + Polynomial.C 3).eval
            ((EncodedType.list memberContextEncoding).inputSize source) := by
        rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
        omega
      omega
    have hAppendEq : setEncoding.inputSize
        (List.append (show List Nat from members) ([item.2.1] : List Nat)) =
        setEncoding.inputSize members + EncodedType.nat.inputSize item.2.1 + 1 :=
      set_inputSize_append_singleton (show List Nat from members) item.2.1
    rw [hAppendEq]
    exact hSum
  · have tagFalse : pairHasRightBool item = false := by
      apply Bool.eq_false_of_not_eq_true
      intro tagTrue
      exact selected ((pairHasRightBool_eq_true_iff item).mp tagTrue)
    rw [membersStep, tagFalse]
    simp [Polynomial.eval_add]

/-- The bounded-growth direct-TM fold that scans one retained right identity. -/
theorem membersFold_tmPolyTime :
    TMPolyTimeMap (EncodedType.list memberContextEncoding) setEncoding
      (fun items : List memberContextEncoding.Carrier =>
        items.foldl (fun members item => membersStep (members, item)) []) := by
  rcases membersStep_tmPolyTime with ⟨stepTM⟩
  refine TMPolyTimeMap.list_foldl_typed_growth_bounded
    memberContextEncoding setEncoding membersStep [] stepTM
    (Polynomial.C 0) (Polynomial.X + Polynomial.C 3) ?_ ?_
  · intro items
    simp [setEncoding, EncodedType.inputSize_list_nil]
  · intro source members item itemBound
    exact membersStep_growth source members item itemBound

/-- Context-attach one right identity to all raw pairs before scanning them. -/
def membersOfFold (input : Nat × List (Nat × Nat)) : List Nat :=
  (Program.contextListMapExecutable (C := EncodedType.nat) (X := pairEncoding) input).foldl
    (fun members item => membersStep (members, item)) []

private theorem membersOfFold_aux (right : Nat) :
    ∀ (pairs : List (Nat × Nat)) (members : List Nat),
      (pairs.map fun pair => (right, pair)).foldl
          (fun output item => membersStep (output, item)) members =
        members ++ IncidenceIRToStructuredExactCover.membersOf right pairs
  | [], members => by simp [IncidenceIRToStructuredExactCover.membersOf]
  | pair :: pairs, members => by
      by_cases selected : pair.2 = right
      · simp only [List.map_cons, List.foldl_cons]
        rw [show membersStep (members, (right, pair)) = members ++ [pair.1] by
          simp [membersStep, pairHasRightBool, selected]]
        rw [membersOfFold_aux right pairs (members ++ [pair.1])]
        simp [IncidenceIRToStructuredExactCover.membersOf, selected, List.append_assoc]
      · simp only [List.map_cons, List.foldl_cons]
        rw [show membersStep (members, (right, pair)) = members by
          simp [membersStep, pairHasRightBool, selected]]
        rw [membersOfFold_aux right pairs members]
        simp [IncidenceIRToStructuredExactCover.membersOf, selected]

/-- The fold computes the exact semantic member list retained by one right identity. -/
theorem membersOfFold_eq_membersOf (right : Nat) (pairs : List (Nat × Nat)) :
    membersOfFold (right, pairs) = IncidenceIRToStructuredExactCover.membersOf right pairs := by
  unfold membersOfFold
  change List.foldl (fun members item => membersStep (members, item)) []
      (Program.contextListMapExecutable (C := EncodedType.nat) (X := pairEncoding)
        (right, pairs)) = IncidenceIRToStructuredExactCover.membersOf right pairs
  have hMap := Program.contextListMapExecutable_eq_map
    (C := EncodedType.nat) (X := pairEncoding) right pairs
  rw [hMap]
  simpa using membersOfFold_aux right pairs []

/-- Direct-TM evidence for the exact recursive semantic member-list executable. -/
theorem membersOf_tmPolyTime :
    TMPolyTimeMap (EncodedType.prod EncodedType.nat pairListEncoding) setEncoding
      (fun input : Nat × List (Nat × Nat) =>
        IncidenceIRToStructuredExactCover.membersOf input.1 input.2) := by
  have hAttached := Program.contextListMapExecutable_tmPolyTime EncodedType.nat pairEncoding
  have hFold := TMPolyTimeMap.comp membersFold_tmPolyTime hAttached
  convert hFold using 1
  funext input
  exact (membersOfFold_eq_membersOf input.1 input.2).symm

/-- Reorder an outer context pair for the exact member-list executable. -/
def membersAtContext (input : List (Nat × Nat) × Nat) : List Nat :=
  IncidenceIRToStructuredExactCover.membersOf input.2 input.1

/-- Direct-TM realization of one outer context item. -/
theorem membersAtContext_tmPolyTime :
    TMPolyTimeMap outerMemberInputEncoding setEncoding membersAtContext := by
  let X := outerMemberInputEncoding
  have hPairs : TMPolyTimeMap X pairListEncoding (fun input : X.Carrier => input.1) := by
    simpa [X, outerMemberInputEncoding] using
      TMPolyTimeMap.fst pairListEncoding EncodedType.nat
  have hRight : TMPolyTimeMap X EncodedType.nat (fun input : X.Carrier => input.2) := by
    simpa [X, outerMemberInputEncoding] using
      TMPolyTimeMap.snd pairListEncoding EncodedType.nat
  have hInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat pairListEncoding)
      (fun input : X.Carrier => (input.2, input.1)) :=
    TMPolyTimeMap.prod_mk hRight hPairs
  have hOut := TMPolyTimeMap.comp membersOf_tmPolyTime hInput
  simpa [membersAtContext, Function.comp] using hOut

/-- The direct executable for the ordered materialized set family. -/
def setFamilyExecutable (input : IncidenceIR) : List (List Nat) :=
  (Program.contextListMapExecutable (C := pairListEncoding) (X := EncodedType.nat)
    (input.membershipPairs, List.range input.rightSize)).map membersAtContext

/-- The direct family executable is extensionally the semantic materialization. -/
theorem setFamilyExecutable_eq_setFamily (input : IncidenceIR) :
    setFamilyExecutable input = IncidenceIRToStructuredExactCover.setFamily input := by
  unfold setFamilyExecutable IncidenceIRToStructuredExactCover.setFamily
  have hMap := Program.contextListMapExecutable_eq_map
    (C := pairListEncoding) (X := EncodedType.nat)
    input.membershipPairs (List.range input.rightSize)
  rw [hMap]
  have mapMembers : ∀ rights : List Nat,
      (rights.map fun right => (input.membershipPairs, right)).map membersAtContext =
        rights.map
          (fun right => IncidenceIRToStructuredExactCover.membersOf right input.membershipPairs) := by
    intro rights
    induction rights with
    | nil => rfl
    | cons right rights inductionHypothesis =>
        simp [membersAtContext, inductionHypothesis]
  exact mapMembers (List.range input.rightSize)

/-- Direct-TM realization of the complete retained-right set family. -/
theorem setFamilyExecutable_tmPolyTime :
    TMPolyTimeMap IncidenceIR.lawfulRepresentation.encodedType
      (EncodedType.list setEncoding) setFamilyExecutable := by
  let X := IncidenceIR.lawfulRepresentation.encodedType
  let Payload := EncodedType.prod EncodedType.nat pairListEncoding
  have hPayload : TMPolyTimeMap X Payload (fun input : X.Carrier => input.2) := by
    simpa [X, Payload, IncidenceIR.lawfulRepresentation] using
      TMPolyTimeMap.snd EncodedType.nat Payload
  have hRight : TMPolyTimeMap X EncodedType.nat (fun input : X.Carrier => input.2.1) := by
    have h := TMPolyTimeMap.comp (TMPolyTimeMap.fst EncodedType.nat pairListEncoding) hPayload
    simpa [Function.comp, X, Payload] using h
  have hPairs : TMPolyTimeMap X pairListEncoding (fun input : X.Carrier => input.2.2) := by
    have h := TMPolyTimeMap.comp (TMPolyTimeMap.snd EncodedType.nat pairListEncoding) hPayload
    simpa [Function.comp, X, Payload] using h
  have hRange : TMPolyTimeMap X (EncodedType.list EncodedType.nat)
      (fun input : X.Carrier => List.range input.2.1) := by
    have h := TMPolyTimeMap.comp natRange_tm_polytime hRight
    simpa [Function.comp, X] using h
  have hContextInput : TMPolyTimeMap X
      (EncodedType.prod pairListEncoding (EncodedType.list EncodedType.nat))
      (fun input : X.Carrier => (input.2.2, List.range input.2.1)) :=
    TMPolyTimeMap.prod_mk hPairs hRange
  have hContext := TMPolyTimeMap.comp
    (Program.contextListMapExecutable_tmPolyTime pairListEncoding EncodedType.nat) hContextInput
  have hOut := TMPolyTimeMap.comp (TMPolyTimeMap.list_map membersAtContext_tmPolyTime) hContext
  simpa [setFamilyExecutable, Function.comp, outerMemberInputEncoding] using hOut

/-- Direct reification of the materialized universe size and set family. -/
def toSetSystemExecutable (input : IncidenceIR) : SetSystemInput where
  universeSize := input.leftSize
  sets := setFamilyExecutable input

/-- The direct assembly is extensionally the semantic SetSystem materialization. -/
theorem toSetSystemExecutable_eq_toSetSystem (input : IncidenceIR) :
    toSetSystemExecutable input = IncidenceIRToStructuredExactCover.toSetSystem input := by
  simp [toSetSystemExecutable, IncidenceIRToStructuredExactCover.toSetSystem,
    setFamilyExecutable_eq_setFamily]

/-- Direct-TM realization of the structured SetSystem reification. -/
theorem toSetSystemExecutable_tmPolyTime :
    TMPolyTimeMap IncidenceIR.lawfulRepresentation.encodedType
      setSystemStructuredEncodedType toSetSystemExecutable := by
  let X := IncidenceIR.lawfulRepresentation.encodedType
  let Payload := EncodedType.prod EncodedType.nat pairListEncoding
  have hLeft : TMPolyTimeMap X EncodedType.nat (fun input : X.Carrier => input.1) := by
    simpa [X, Payload, IncidenceIR.lawfulRepresentation] using
      TMPolyTimeMap.fst EncodedType.nat Payload
  have hSets : TMPolyTimeMap X (EncodedType.list setEncoding) setFamilyExecutable :=
    setFamilyExecutable_tmPolyTime
  have hTuple : TMPolyTimeMap X setSystemTupleStructuredEncodedType
      (fun input : X.Carrier => (input.1, setFamilyExecutable input)) := by
    simpa [setSystemTupleStructuredEncodedType] using TMPolyTimeMap.prod_mk hLeft hSets
  have hOut := TMPolyTimeMap.comp
    ComplexityReduction.Karp21.SetCovering.setSystemTupleToSetSystemInputTMBackedMap.tm_polytime
    hTuple
  simpa [Function.comp, toSetSystemExecutable,
    ComplexityReduction.Karp21.SetCovering.setSystemTupleToSetSystemInput] using hOut

/-- Reify a structured SetSystem as its one-field Exact-Cover wrapper. -/
def exactCoverOfSetSystem (input : SetSystemInput) : ExactCoverInput where
  system := input

/-- This wrapper preserves the complete structured encoding. -/
theorem exactCoverOfSetSystem_tmPolyTime :
    TMPolyTimeMap setSystemStructuredEncodedType exactCoverStructuredEncodedType
      exactCoverOfSetSystem := by
  exact TMPolyTimeMap.of_encodingEquiv _ _ _ (Equiv.refl _) (by
    intro input
    change setSystemStructuredEncodedType.encode input =
      List.map id (setSystemStructuredEncodedType.encode input)
    rw [List.map_id])

/-- Direct-TM realization of the unguarded canonical Exact-Cover materialization. -/
theorem coreExecutable_tmPolyTime :
    TMPolyTimeMap sourceProblem.representation.encodedType
      targetProblem.representation.encodedType IncidenceIRToStructuredExactCover.coreExecutable := by
  have hOut := TMPolyTimeMap.comp exactCoverOfSetSystem_tmPolyTime toSetSystemExecutable_tmPolyTime
  convert hOut using 1
  funext input
  simp [Function.comp, exactCoverOfSetSystem,
    toSetSystemExecutable_eq_toSetSystem,
    IncidenceIRToStructuredExactCover.coreExecutable]

/-- Direct-TM realization of the total, malformed-input-guarded egress executable. -/
theorem executable_tmPolyTime :
    TMPolyTimeMap sourceProblem.representation.encodedType
      targetProblem.representation.encodedType IncidenceIRToStructuredExactCover.executable := by
  let X := sourceProblem.representation.encodedType
  have hGuard : TMPolyTimeMap X EncodedType.bool IncidenceIRValidation.wellFormedBool := by
    simpa [X, sourceProblem, IncidenceIR.exactCoverProblem] using
      IncidenceIRValidation.wellFormedBool_tmPolyTime
  have hCore : TMPolyTimeMap X targetProblem.representation.encodedType
      IncidenceIRToStructuredExactCover.coreExecutable := by
    simpa [X, sourceProblem, targetProblem,
      Presentation.SetSystem.exactCoverStructuredProblem,
      Presentation.SetSystem.exactCoverStructuredPresentation] using coreExecutable_tmPolyTime
  have hNo : TMPolyTimeMap X targetProblem.representation.encodedType
      (fun _ : X.Carrier => IncidenceIRToStructuredExactCover.noTarget) :=
    TMPolyTimeMap.const X targetProblem.representation.encodedType
      IncidenceIRToStructuredExactCover.noTarget
  have hTagged : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun input : X.Carrier => (IncidenceIRValidation.wellFormedBool input, input)) :=
    TMPolyTimeMap.prod_mk hGuard (TMPolyTimeMap.id X)
  have hBranch := boolProduct_dispatch_tm_polytime X targetProblem.representation.encodedType
    (fFalse := fun _ => IncidenceIRToStructuredExactCover.noTarget)
    (fTrue := IncidenceIRToStructuredExactCover.coreExecutable) hNo hCore
  have hOut := TMPolyTimeMap.comp hBranch hTagged
  convert hOut using 1
  funext input
  cases guard : IncidenceIRValidation.wellFormedBool input <;>
    simp [IncidenceIRToStructuredExactCover.executable, Function.comp, guard]

/-- The egress primitive is indexed by the exact total executable and its direct TM. -/
@[complexity_reduction_ir_typed_primitive]
def egressPrimitive : Primitive sourceProblem.representation targetProblem.representation :=
  Primitive.ofTMPolyTime IncidenceIRToStructuredExactCover.executable executable_tmPolyTime

/-- The canonical egress computation is one direct-TM-backed atom. -/
def egressProgram : PolyProg sourceProblem.representation targetProblem.representation :=
  .atom egressPrimitive

@[simp] theorem egressProgram_run (input : sourceProblem.Instance) :
    egressProgram.run input = IncidenceIRToStructuredExactCover.executable input :=
  rfl

@[simp] theorem egressProgram_directTM :
    egressProgram.compileTM = egressPrimitive.tmPolyTime :=
  rfl

/-- The semantic law is indexed by the same guarded direct-TM program. -/
theorem egressProgram_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔ targetProblem.accepts (egressProgram.run input) := by
  exact (IncidenceIRToStructuredExactCover.exactCover_iff_incidenceIR input).symm

/-- The authoritative reusable IncidenceIR-to-structured-Exact-Cover egress certificate. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_egress]
def egress : CertifiedReduction sourceProblem targetProblem where
  program := egressProgram
  correct := egressProgram_correct

@[simp] theorem egress_program : egress.program = egressProgram :=
  rfl

@[simp] theorem egress_directTM : egress.directTM = egress.program.compileTM :=
  rfl

/-- The exact role-indexed request for this reusable egress component. -/
abbrev EgressRequest : Type 2 :=
  Protocol.ComponentRequest .egress sourceProblem targetProblem

/-- The only accepted endpoint request has no metadata-based alternative. -/
def request : EgressRequest := .exact

/-- Resolve the egress solely from the canonical program-indexed certificate. -/
def resolution : Protocol.ComponentResolution .egress sourceProblem targetProblem :=
  Protocol.ComponentResolver.accept request egress

@[simp] theorem resolution_exact :
    resolution = .accepted egress :=
  rfl

end IncidenceIRToStructuredExactCoverStandardTM
end Domain
end ComplexityReduction
