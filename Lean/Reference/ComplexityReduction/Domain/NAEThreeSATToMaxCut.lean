/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Certificate.Reduction
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ChromaticNumber.StructuredRoute
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.MaxCut.StructuredTM.Assembly
import ComplexityReduction.Presentation.MaxCut
import ComplexityReduction.Presentation.NAEThreeSAT
import ComplexityReduction.Program.List

/-!
An endpoint-exact NAE-3SAT-to-MaxCut literal-pair/triangle gadget.

For the encoding-safe variable horizon `n`, the graph contains one edge
between the positive and negative vertices of every variable below `n`.
Every ordered NAE clause contributes the three occurrence edges of its
literal triangle.  MaxCut counts the input edge list with multiplicity, so
parallel edges are intentionally retained.  Repeated literals may also
produce self-loops; the local truth table below proves that the three listed
occurrences contribute at most two cut edges, with equality exactly when the
three literal values are not all equal.

This leaf exports only the executable, its direct-TM proof, semantic iff, and
raw endpoint-exact `TMKarpReduction`.  It does not publish a hardness facade,
final route, or certified reduction.
-/

namespace ComplexityReduction
namespace Domain
namespace NAEThreeSATToMaxCut

open ComplexityReduction
open ComplexityReduction.Combinatorics.Graph
open ComplexityReduction.Karp21
open ComplexityReduction.Karp21.ChromaticNumber
open ComplexityReduction.NAEThreeSAT

/-- Exact public NAE source encoding. -/
abbrev sourceEncoding : EncodedType :=
  Presentation.NAEThreeSAT.formulaEncodedType

/-- Exact public NAE clause encoding. -/
abbrev clauseEncoding : EncodedType :=
  Presentation.NAEThreeSAT.clauseEncodedType

/-- Exact structured MaxCut target encoding. -/
abbrev targetEncoding : EncodedType :=
  maxCutStructuredEncodedType

/-- Encoding-safe variable horizon; every represented variable is below it. -/
def variableHorizon (formula : Formula) : Nat :=
  sourceEncoding.inputSize formula

/-- One consistency edge forcing the two vertices of a variable apart. -/
def literalPairEdge (index : Nat) : Nat × Nat :=
  (posVertex index, negVertex index)

/-- One consistency edge per variable in the encoding-safe horizon. -/
def literalPairEdges (horizon : Nat) : List (Nat × Nat) :=
  (List.range horizon).map literalPairEdge

/-- The three occurrence edges of one ordered clause triangle. -/
def clauseTriangleEdges (clause : Clause) : List (Nat × Nat) :=
  let first := literalVertex clause.first
  let second := literalVertex clause.second
  let third := literalVertex clause.third
  [(first, second), (second, third), (third, first)]

/-- All clause triangles, retaining duplicate and self-loop occurrences. -/
def clauseTriangleEdgeList (formula : Formula) : List (Nat × Nat) :=
  formula.flatMap clauseTriangleEdges

/-- Complete gadget edge list. -/
def gadgetEdges (formula : Formula) : List (Nat × Nat) :=
  literalPairEdges (variableHorizon formula) ++ clauseTriangleEdgeList formula

/-- The graph uses exactly the existing literal-vertex numbering horizon. -/
def gadgetGraph (formula : Formula) : GraphInput where
  vertices := variableLimit (variableHorizon formula)
  edges := gadgetEdges formula
  directed := false

/-- Textbook threshold `n + 2m`. -/
def gadgetThreshold (formula : Formula) : Nat :=
  variableHorizon formula + 2 * formula.length

/-- Complete exact NAE-3SAT-to-MaxCut executable. -/
def executable (formula : Formula) : MaxCutInput where
  graph := gadgetGraph formula
  threshold := gadgetThreshold formula

/-! ### Structural occurrence invariants -/

@[simp] theorem literalPairEdges_length (horizon : Nat) :
    (literalPairEdges horizon).length = horizon := by
  simp [literalPairEdges]

@[simp] theorem clauseTriangleEdges_length (clause : Clause) :
    (clauseTriangleEdges clause).length = 3 := by
  simp [clauseTriangleEdges]

theorem clauseTriangleEdgeList_length (formula : Formula) :
    (clauseTriangleEdgeList formula).length = 3 * formula.length := by
  induction formula with
  | nil => rfl
  | cons clause tail inductionHypothesis =>
      rw [show clauseTriangleEdgeList (clause :: tail) =
        clauseTriangleEdges clause ++ clauseTriangleEdgeList tail by rfl]
      rw [List.length_append, clauseTriangleEdges_length, inductionHypothesis]
      simp only [List.length_cons]
      omega

theorem gadgetEdges_length (formula : Formula) :
    (gadgetEdges formula).length =
      variableHorizon formula + 3 * formula.length := by
  simp [gadgetEdges, clauseTriangleEdgeList_length]

theorem gadgetThreshold_eq_horizon_add_two_mul (formula : Formula) :
    gadgetThreshold formula = variableHorizon formula + 2 * formula.length :=
  rfl

@[simp] theorem gadgetGraph_directed (formula : Formula) :
    (gadgetGraph formula).directed = false :=
  rfl

/-! ### Exact direct-TM construction -/

theorem variableHorizon_tmPolyTime :
    TMPolyTimeMap sourceEncoding EncodedType.nat variableHorizon := by
  simpa [variableHorizon] using
    (encodedInputSizeNatTMBackedMap sourceEncoding).tm_polytime

theorem literalPairEdge_tmPolyTime :
    TMPolyTimeMap EncodedType.nat edgeStructuredEncodedType literalPairEdge := by
  simpa [literalPairEdge, edgeStructuredEncodedType] using
    TMPolyTimeMap.prod_mk posVertex_tm_polytime negVertex_tm_polytime

theorem literalPairEdges_tmPolyTime :
    TMPolyTimeMap EncodedType.nat edgeListStructuredEncodedType literalPairEdges := by
  have mapped := TMPolyTimeMap.list_map literalPairEdge_tmPolyTime
  have composed := TMPolyTimeMap.comp mapped natRange_tm_polytime
  simpa [Function.comp, literalPairEdges, edgeListStructuredEncodedType] using composed

/-- Re-expose one exact clause as its nested encoded payload. -/
def clausePayloadView (clause : Clause) :
    Presentation.NAEThreeSAT.clausePayloadEncodedType.Carrier :=
  (clause.first, (clause.second, clause.third))

theorem clausePayloadView_tmPolyTime :
    TMPolyTimeMap clauseEncoding Presentation.NAEThreeSAT.clausePayloadEncodedType
      clausePayloadView := by
  apply TMPolyTimeMap.of_encodingEquiv clauseEncoding
    Presentation.NAEThreeSAT.clausePayloadEncodedType clausePayloadView (Equiv.refl _)
  intro clause
  change Presentation.NAEThreeSAT.clausePayloadEncodedType.encode
      (clause.first, (clause.second, clause.third)) =
    (Presentation.NAEThreeSAT.clausePayloadEncodedType.encode
      (clause.first, (clause.second, clause.third))).map id
  rw [List.map_id]

theorem clauseFirst_tmPolyTime :
    TMPolyTimeMap clauseEncoding literalStructuredEncodedType Clause.first := by
  have projection := TMPolyTimeMap.fst literalStructuredEncodedType
    (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
  have composed := TMPolyTimeMap.comp projection clausePayloadView_tmPolyTime
  simpa [Function.comp, clausePayloadView,
    Presentation.NAEThreeSAT.clausePayloadEncodedType] using composed

theorem clauseTail_tmPolyTime :
    TMPolyTimeMap clauseEncoding
      (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
      (fun clause : Clause => (clause.second, clause.third)) := by
  have projection := TMPolyTimeMap.snd literalStructuredEncodedType
    (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
  have composed := TMPolyTimeMap.comp projection clausePayloadView_tmPolyTime
  simpa [Function.comp, clausePayloadView,
    Presentation.NAEThreeSAT.clausePayloadEncodedType] using composed

theorem clauseSecond_tmPolyTime :
    TMPolyTimeMap clauseEncoding literalStructuredEncodedType Clause.second := by
  have projection := TMPolyTimeMap.fst literalStructuredEncodedType literalStructuredEncodedType
  have composed := TMPolyTimeMap.comp projection clauseTail_tmPolyTime
  simpa [Function.comp] using composed

theorem clauseThird_tmPolyTime :
    TMPolyTimeMap clauseEncoding literalStructuredEncodedType Clause.third := by
  have projection := TMPolyTimeMap.snd literalStructuredEncodedType literalStructuredEncodedType
  have composed := TMPolyTimeMap.comp projection clauseTail_tmPolyTime
  simpa [Function.comp] using composed

theorem clauseTriangleEdges_tmPolyTime :
    TMPolyTimeMap clauseEncoding edgeListStructuredEncodedType clauseTriangleEdges := by
  have firstVertex : TMPolyTimeMap clauseEncoding EncodedType.nat
      (fun clause : Clause => literalVertex clause.first) := by
    have composed := TMPolyTimeMap.comp literalVertex_tm_polytime clauseFirst_tmPolyTime
    simpa [Function.comp] using composed
  have secondVertex : TMPolyTimeMap clauseEncoding EncodedType.nat
      (fun clause : Clause => literalVertex clause.second) := by
    have composed := TMPolyTimeMap.comp literalVertex_tm_polytime clauseSecond_tmPolyTime
    simpa [Function.comp] using composed
  have thirdVertex : TMPolyTimeMap clauseEncoding EncodedType.nat
      (fun clause : Clause => literalVertex clause.third) := by
    have composed := TMPolyTimeMap.comp literalVertex_tm_polytime clauseThird_tmPolyTime
    simpa [Function.comp] using composed
  have firstSecond : TMPolyTimeMap clauseEncoding edgeStructuredEncodedType
      (fun clause : Clause =>
        (literalVertex clause.first, literalVertex clause.second)) := by
    simpa [edgeStructuredEncodedType] using TMPolyTimeMap.prod_mk firstVertex secondVertex
  have secondThird : TMPolyTimeMap clauseEncoding edgeStructuredEncodedType
      (fun clause : Clause =>
        (literalVertex clause.second, literalVertex clause.third)) := by
    simpa [edgeStructuredEncodedType] using TMPolyTimeMap.prod_mk secondVertex thirdVertex
  have thirdFirst : TMPolyTimeMap clauseEncoding edgeStructuredEncodedType
      (fun clause : Clause =>
        (literalVertex clause.third, literalVertex clause.first)) := by
    simpa [edgeStructuredEncodedType] using TMPolyTimeMap.prod_mk thirdVertex firstVertex
  have firstSingleton := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_singleton edgeStructuredEncodedType) firstSecond
  have secondSingleton := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_singleton edgeStructuredEncodedType) secondThird
  have thirdSingleton := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_singleton edgeStructuredEncodedType) thirdFirst
  have firstTwoInput := TMPolyTimeMap.prod_mk firstSingleton secondSingleton
  have firstTwo := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append edgeStructuredEncodedType) firstTwoInput
  have allInput := TMPolyTimeMap.prod_mk firstTwo thirdSingleton
  have all := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append edgeStructuredEncodedType) allInput
  simpa [Function.comp, clauseTriangleEdges, edgeListStructuredEncodedType,
    List.append_assoc] using all

theorem clauseTriangleEdgeList_tmPolyTime :
    TMPolyTimeMap sourceEncoding edgeListStructuredEncodedType clauseTriangleEdgeList := by
  have blocks := TMPolyTimeMap.list_map clauseTriangleEdges_tmPolyTime
  have flattened := TMPolyTimeMap.comp
    (Program.listFlatten_tmPolyTime edgeStructuredEncodedType) blocks
  simpa [Function.comp, clauseTriangleEdgeList] using flattened

theorem gadgetEdges_tmPolyTime :
    TMPolyTimeMap sourceEncoding edgeListStructuredEncodedType gadgetEdges := by
  have pairEdges := TMPolyTimeMap.comp literalPairEdges_tmPolyTime
    variableHorizon_tmPolyTime
  have appendInput := TMPolyTimeMap.prod_mk pairEdges clauseTriangleEdgeList_tmPolyTime
  have appended := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append edgeStructuredEncodedType) appendInput
  simpa [Function.comp, gadgetEdges, edgeListStructuredEncodedType] using appended

theorem gadgetGraph_tmPolyTime :
    TMPolyTimeMap sourceEncoding graphStructuredEncodedType gadgetGraph := by
  have vertices := TMPolyTimeMap.comp variableLimit_tm_polytime variableHorizon_tmPolyTime
  have directed : TMPolyTimeMap sourceEncoding EncodedType.bool
      (fun _ : Formula => false) :=
    TMPolyTimeMap.const sourceEncoding EncodedType.bool false
  have payload : TMPolyTimeMap sourceEncoding graphPayloadStructuredEncodedType
      (fun formula : Formula => (gadgetEdges formula, false)) :=
    TMPolyTimeMap.prod_mk gadgetEdges_tmPolyTime directed
  have tuple : TMPolyTimeMap sourceEncoding graphTupleStructuredEncodedType
      (fun formula : Formula =>
        (variableLimit (variableHorizon formula), (gadgetEdges formula, false))) :=
    TMPolyTimeMap.prod_mk vertices payload
  have graph := TMPolyTimeMap.comp Clique.graphTupleToGraphTMBackedMap.tm_polytime tuple
  simpa [Function.comp, Clique.graphTupleToGraph, gadgetGraph] using graph

theorem formulaLength_tmPolyTime :
    TMPolyTimeMap sourceEncoding EncodedType.nat List.length := by
  simpa [sourceEncoding] using
    (HittingSet.listLengthTMBackedMap clauseEncoding).tm_polytime

theorem gadgetThreshold_tmPolyTime :
    TMPolyTimeMap sourceEncoding EncodedType.nat gadgetThreshold := by
  have doubled := TMPolyTimeMap.comp natDouble_tm_polytime formulaLength_tmPolyTime
  have addInput := TMPolyTimeMap.prod_mk variableHorizon_tmPolyTime doubled
  have added := TMPolyTimeMap.comp natAdd_tm_polytime addInput
  convert added using 1
  funext formula
  simp [Function.comp, gadgetThreshold, natDouble, two_mul]
  rfl

/-- The complete endpoint map is realized by an exact direct TM. -/
theorem executable_tmPolyTime :
    TMPolyTimeMap sourceEncoding targetEncoding executable := by
  have tuple : TMPolyTimeMap sourceEncoding maxCutTupleStructuredEncodedType
      (fun formula : Formula => (gadgetGraph formula, gadgetThreshold formula)) :=
    TMPolyTimeMap.prod_mk gadgetGraph_tmPolyTime gadgetThreshold_tmPolyTime
  have output := TMPolyTimeMap.comp
    Karp21.MaxCut.maxCutTupleToMaxCutInputTMBackedMap.tm_polytime tuple
  simpa [Function.comp, Karp21.MaxCut.maxCutTupleToMaxCutInput, executable,
    targetEncoding] using output

/-- Explicit polynomial output-size bound projected from the same direct TM. -/
theorem executable_polynomialSizeBound :
    PolynomialSizeBound
      (fun formula => sourceEncoding.inputSize formula)
      (fun output => targetEncoding.inputSize output)
      executable :=
  TMPolyTimeMap.outputSizeBound executable_tmPolyTime

/-! ### Occurrence-count semantics -/

/-- Numeric contribution of one listed edge occurrence. -/
def edgeContribution (side : Nat → Bool) (edge : Nat × Nat) : Nat :=
  if side edge.1 ≠ side edge.2 then 1 else 0

/-- Sum spelling of the listed-edge cut count. -/
def edgeListScore (edges : List (Nat × Nat)) (side : Nat → Bool) : Nat :=
  (edges.map (edgeContribution side)).sum

private theorem filter_length_eq_indicator_sum
    {X : Type} (predicate : X → Prop) [DecidablePred predicate] (xs : List X) :
    (xs.filter predicate).length =
      (xs.map (fun x => if predicate x then 1 else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x tail inductionHypothesis =>
      by_cases holds : predicate x <;>
        simp [holds, inductionHypothesis, Nat.add_comm]

theorem cutSize_eq_edgeListScore (graph : GraphInput) (side : Nat → Bool) :
    CutSize graph side = edgeListScore graph.edges side := by
  unfold CutSize edgeListScore edgeContribution
  exact filter_length_eq_indicator_sum
    (fun edge : Nat × Nat => side edge.1 ≠ side edge.2) graph.edges

@[simp] theorem edgeListScore_nil (side : Nat → Bool) :
    edgeListScore [] side = 0 := rfl

@[simp] theorem edgeListScore_append
    (left right : List (Nat × Nat)) (side : Nat → Bool) :
    edgeListScore (left ++ right) side =
      edgeListScore left side + edgeListScore right side := by
  simp [edgeListScore, List.sum_append]

@[simp] theorem edgeListScore_singleton
    (edge : Nat × Nat) (side : Nat → Bool) :
    edgeListScore [edge] side = edgeContribution side edge := by
  simp [edgeListScore]

/-- Boolean truth-table score of a three-occurrence triangle. -/
def triangleBoolScore (first second third : Bool) : Nat :=
  (if first ≠ second then 1 else 0) +
    (if second ≠ third then 1 else 0) +
      (if third ≠ first then 1 else 0)

theorem triangleBoolScore_le_two (first second third : Bool) :
    triangleBoolScore first second third ≤ 2 := by
  cases first <;> cases second <;> cases third <;>
    decide

theorem triangleBoolScore_eq_two_iff (first second third : Bool) :
    triangleBoolScore first second third = 2 ↔
      ¬ (first = second ∧ second = third) := by
  cases first <;> cases second <;> cases third <;>
    decide

theorem clauseTriangle_score
    (clause : Clause) (side : Nat → Bool) :
    edgeListScore (clauseTriangleEdges clause) side =
      triangleBoolScore
        (side (literalVertex clause.first))
        (side (literalVertex clause.second))
        (side (literalVertex clause.third)) := by
  simp [edgeListScore, edgeContribution, clauseTriangleEdges, triangleBoolScore,
    Nat.add_assoc]

theorem clauseTriangle_score_le_two
    (clause : Clause) (side : Nat → Bool) :
    edgeListScore (clauseTriangleEdges clause) side ≤ 2 := by
  rw [clauseTriangle_score]
  exact triangleBoolScore_le_two _ _ _

theorem clauseTriangle_score_eq_two_iff
    (clause : Clause) (side : Nat → Bool) :
    edgeListScore (clauseTriangleEdges clause) side = 2 ↔
      ¬ (side (literalVertex clause.first) = side (literalVertex clause.second) ∧
        side (literalVertex clause.second) = side (literalVertex clause.third)) := by
  rw [clauseTriangle_score, triangleBoolScore_eq_two_iff]

/-- Total score of all clause-triangle occurrence blocks. -/
def clauseScore (formula : Formula) (side : Nat → Bool) : Nat :=
  (formula.map (fun clause => edgeListScore (clauseTriangleEdges clause) side)).sum

theorem clauseTriangleEdgeList_score
    (formula : Formula) (side : Nat → Bool) :
    edgeListScore (clauseTriangleEdgeList formula) side = clauseScore formula side := by
  induction formula with
  | nil => rfl
  | cons clause tail inductionHypothesis =>
      change
        edgeListScore (clauseTriangleEdges clause ++ clauseTriangleEdgeList tail) side =
          edgeListScore (clauseTriangleEdges clause) side + clauseScore tail side
      rw [edgeListScore_append, inductionHypothesis]

theorem clauseScore_le (formula : Formula) (side : Nat → Bool) :
    clauseScore formula side ≤ 2 * formula.length := by
  induction formula with
  | nil => simp [clauseScore]
  | cons clause tail inductionHypothesis =>
      change
        edgeListScore (clauseTriangleEdges clause) side + clauseScore tail side ≤
          2 * (tail.length + 1)
      have localBound := clauseTriangle_score_le_two clause side
      omega

theorem clauseScore_eq_bound_iff
    (formula : Formula) (side : Nat → Bool) :
    clauseScore formula side = 2 * formula.length ↔
      ∀ clause ∈ formula,
        edgeListScore (clauseTriangleEdges clause) side = 2 := by
  induction formula with
  | nil => simp [clauseScore]
  | cons clause tail inductionHypothesis =>
      have localBound := clauseTriangle_score_le_two clause side
      have tailBound := clauseScore_le tail side
      change
        edgeListScore (clauseTriangleEdges clause) side + clauseScore tail side =
            2 * (tail.length + 1) ↔
          ∀ candidate ∈ clause :: tail,
            edgeListScore (clauseTriangleEdges candidate) side = 2
      simp only [List.mem_cons, forall_eq_or_imp]
      constructor
      · intro total
        constructor
        · omega
        · intro candidate member
          have tailTotal : clauseScore tail side = 2 * tail.length := by omega
          exact (inductionHypothesis.mp tailTotal) candidate member
      · rintro ⟨headTotal, rest⟩
        have tailTotal := inductionHypothesis.mpr rest
        omega

/-- Total score of the literal-pair block. -/
def literalPairScore (horizon : Nat) (side : Nat → Bool) : Nat :=
  edgeListScore (literalPairEdges horizon) side

theorem literalPairScore_le (horizon : Nat) (side : Nat → Bool) :
    literalPairScore horizon side ≤ horizon := by
  induction horizon with
  | zero => simp [literalPairScore, literalPairEdges, edgeListScore]
  | succ horizon inductionHypothesis =>
      change edgeListScore (literalPairEdges (Nat.succ horizon)) side ≤ Nat.succ horizon
      rw [show literalPairEdges (Nat.succ horizon) =
        literalPairEdges horizon ++ [literalPairEdge horizon] by
          simp [literalPairEdges, List.range_succ]]
      rw [edgeListScore_append, edgeListScore_singleton]
      change literalPairScore horizon side +
        edgeContribution side (literalPairEdge horizon) ≤ Nat.succ horizon
      simp [edgeContribution, literalPairEdge]
      split <;> omega

theorem literalPairScore_eq_bound_iff
    (horizon : Nat) (side : Nat → Bool) :
    literalPairScore horizon side = horizon ↔
      ∀ index < horizon,
        side (posVertex index) ≠ side (negVertex index) := by
  induction horizon with
  | zero => simp [literalPairScore, literalPairEdges, edgeListScore]
  | succ horizon inductionHypothesis =>
      have priorBound := literalPairScore_le horizon side
      change
        edgeListScore (literalPairEdges (Nat.succ horizon)) side = Nat.succ horizon ↔
          ∀ index < Nat.succ horizon,
            side (posVertex index) ≠ side (negVertex index)
      rw [show literalPairEdges (Nat.succ horizon) =
        literalPairEdges horizon ++ [literalPairEdge horizon] by
          simp [literalPairEdges, List.range_succ]]
      rw [edgeListScore_append, edgeListScore_singleton]
      change
        literalPairScore horizon side +
            (if side (posVertex horizon) ≠ side (negVertex horizon) then 1 else 0) =
              Nat.succ horizon ↔
          ∀ index < Nat.succ horizon,
            side (posVertex index) ≠ side (negVertex index)
      constructor
      · intro total index indexBound
        by_cases last : index = horizon
        · subst index
          split at total
          · assumption
          · omega
        · have priorVariable : index < horizon := by omega
          have priorTotal : literalPairScore horizon side = horizon := by
            split at total <;> omega
          exact (inductionHypothesis.mp priorTotal) index priorVariable
      · intro allCut
        have priorTotal : literalPairScore horizon side = horizon :=
          inductionHypothesis.mpr (fun index bound => allCut index (by omega))
        have lastCut := allCut horizon (by omega)
        rw [priorTotal]
        simp [lastCut]

theorem gadget_cut_score
    (formula : Formula) (side : Nat → Bool) :
    CutSize (gadgetGraph formula) side =
      literalPairScore (variableHorizon formula) side + clauseScore formula side := by
  rw [cutSize_eq_edgeListScore]
  simp [gadgetGraph, gadgetEdges, literalPairScore, edgeListScore_append,
    clauseTriangleEdgeList_score]

/-! ### Literal semantics and correctness -/

/-- Assignment decoded from the positive literal vertices of a cut. -/
def assignmentOfSide (side : Nat → Bool) : SAT.Assignment :=
  fun index => side (posVertex index)

theorem bool_ne_eq_not {left right : Bool} (different : left ≠ right) :
    right = !left := by
  cases left <;> cases right <;> simp_all

theorem literal_eval_assignmentOfSide
    (side : Nat → Bool) (literal : SAT.Literal)
    (pairCut : side (posVertex literal.var) ≠ side (negVertex literal.var)) :
    literal.eval (assignmentOfSide side) = side (literalVertex literal) := by
  cases literal with
  | mk index negated =>
      cases negated
      · simp [SAT.Literal.eval, assignmentOfSide, literalVertex]
      · have opposite := bool_ne_eq_not pairCut
        simp [SAT.Literal.eval, assignmentOfSide, literalVertex, opposite]

private theorem member_inputSize_add_one_le
    (X : EncodedType) {x : X.Carrier} {xs : List X.Carrier} (member : x ∈ xs) :
    X.inputSize x + 1 ≤ (EncodedType.list X).inputSize xs := by
  induction xs with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      rw [EncodedType.inputSize_list_cons]
      simp only [List.mem_cons] at member
      rcases member with rfl | tailMember
      · omega
      · have tailBound := inductionHypothesis tailMember
        omega

theorem literal_var_lt_variableHorizon
    (formula : Formula) {clause : Clause} (clauseMember : clause ∈ formula)
    {literal : SAT.Literal}
    (literalPosition : literal = clause.first ∨ literal = clause.second ∨
      literal = clause.third) :
    literal.var < variableHorizon formula := by
  have literalSize : literal.var + 1 ≤ Karp21.literalStructuredEncodedType.inputSize literal := by
    cases literal with
    | mk index negated =>
        change index + 1 ≤
          Karp21.literalTupleStructuredEncodedType.inputSize (index, negated)
        simp [Karp21.literalTupleStructuredEncodedType]
  have clauseSize :
      Karp21.literalStructuredEncodedType.inputSize literal ≤
        clauseEncoding.inputSize clause := by
    rcases literalPosition with rfl | rfl | rfl
    · change Karp21.literalStructuredEncodedType.inputSize clause.first ≤
        (EncodedType.prod Karp21.literalStructuredEncodedType
          (EncodedType.prod Karp21.literalStructuredEncodedType
            Karp21.literalStructuredEncodedType)).inputSize
          (clause.first, (clause.second, clause.third))
      rw [EncodedType.inputSize_prod]
      simp only
      omega
    · change Karp21.literalStructuredEncodedType.inputSize clause.second ≤
        (EncodedType.prod Karp21.literalStructuredEncodedType
          (EncodedType.prod Karp21.literalStructuredEncodedType
            Karp21.literalStructuredEncodedType)).inputSize
          (clause.first, (clause.second, clause.third))
      rw [EncodedType.inputSize_prod, EncodedType.inputSize_prod]
      simp only
      omega
    · change Karp21.literalStructuredEncodedType.inputSize clause.third ≤
        (EncodedType.prod Karp21.literalStructuredEncodedType
          (EncodedType.prod Karp21.literalStructuredEncodedType
            Karp21.literalStructuredEncodedType)).inputSize
          (clause.first, (clause.second, clause.third))
      rw [EncodedType.inputSize_prod, EncodedType.inputSize_prod]
      simp only
      omega
  have memberSize : clauseEncoding.inputSize clause + 1 ≤
      sourceEncoding.inputSize formula := by
    simpa [sourceEncoding] using
      member_inputSize_add_one_le clauseEncoding clauseMember
  simp only [variableHorizon]
  omega

theorem literalVertex_lt_variableLimit
    (literal : SAT.Literal) {horizon : Nat} (within : literal.var < horizon) :
    literalVertex literal < variableLimit horizon := by
  cases literal with
  | mk index negated =>
      change index < horizon at within
      cases negated <;>
        simp [literalVertex, posVertex, negVertex, variableLimit] <;>
        omega

theorem literalPairEdges_withinBounds
    (horizon : Nat) {edge : Nat × Nat} (member : edge ∈ literalPairEdges horizon) :
    EdgeWithinBounds
      { vertices := variableLimit horizon
        edges := literalPairEdges horizon
        directed := false }
      edge := by
  rcases List.mem_map.mp member with ⟨index, indexMember, rfl⟩
  have indexBound : index < horizon := by simpa using indexMember
  simp [EdgeWithinBounds, literalPairEdge, posVertex, negVertex, variableLimit]
  omega

theorem clauseTriangleEdgeList_withinBounds
    (formula : Formula) {edge : Nat × Nat}
    (member : edge ∈ clauseTriangleEdgeList formula) :
    EdgeWithinBounds (gadgetGraph formula) edge := by
  rcases List.mem_flatMap.mp member with ⟨clause, clauseMember, edgeMember⟩
  have firstBound := literal_var_lt_variableHorizon formula clauseMember (Or.inl rfl)
  have secondBound :=
    literal_var_lt_variableHorizon formula clauseMember (Or.inr (Or.inl rfl))
  have thirdBound :=
    literal_var_lt_variableHorizon formula clauseMember (Or.inr (Or.inr rfl))
  have firstVertex := literalVertex_lt_variableLimit clause.first firstBound
  have secondVertex := literalVertex_lt_variableLimit clause.second secondBound
  have thirdVertex := literalVertex_lt_variableLimit clause.third thirdBound
  simp [clauseTriangleEdges] at edgeMember
  rcases edgeMember with rfl | rfl | rfl <;>
    simp [EdgeWithinBounds, gadgetGraph, firstVertex, secondVertex, thirdVertex]

/-- Every listed occurrence, including repeated/self-loop clause edges, is vertex-bounded. -/
theorem gadgetGraph_wellFormed (formula : Formula) :
    WellFormed (gadgetGraph formula) := by
  intro edge member
  have split := List.mem_append.mp member
  rcases split with pairMember | clauseMember
  · have bounded := literalPairEdges_withinBounds
      (variableHorizon formula) pairMember
    simpa [EdgeWithinBounds, gadgetGraph] using bounded
  · exact clauseTriangleEdgeList_withinBounds formula clauseMember

/-- Forward side assignment, defined arithmetically on the literal vertices. -/
def sideOfAssignment (assignment : SAT.Assignment) (vertex : Nat) : Bool :=
  if vertex % 2 = 1 then assignment ((vertex - 3) / 2)
  else !assignment ((vertex - 4) / 2)

@[simp] theorem sideOfAssignment_pos
    (assignment : SAT.Assignment) (index : Nat) :
    sideOfAssignment assignment (posVertex index) = assignment index := by
  simp [sideOfAssignment, posVertex]

@[simp] theorem sideOfAssignment_neg
    (assignment : SAT.Assignment) (index : Nat) :
    sideOfAssignment assignment (negVertex index) = !assignment index := by
  simp [sideOfAssignment, negVertex]
  omega

@[simp] theorem sideOfAssignment_literal
    (assignment : SAT.Assignment) (literal : SAT.Literal) :
    sideOfAssignment assignment (literalVertex literal) = literal.eval assignment := by
  cases literal with
  | mk index negated =>
      cases negated <;>
        simp [literalVertex, SAT.Literal.eval]

theorem maxCut_of_satisfies
    (formula : Formula) (assignment : SAT.Assignment)
    (satisfies : Formula.Satisfies formula assignment) :
    MaxCut (executable formula) := by
  let side := sideOfAssignment assignment
  refine ⟨side, ?_⟩
  change gadgetThreshold formula ≤ CutSize (gadgetGraph formula) side
  rw [gadget_cut_score]
  have pairTotal :
      literalPairScore (variableHorizon formula) side = variableHorizon formula := by
    apply (literalPairScore_eq_bound_iff (variableHorizon formula) side).2
    intro index indexBound
    simp [side]
  have clauseTotal : clauseScore formula side = 2 * formula.length := by
    apply (clauseScore_eq_bound_iff formula side).2
    intro clause clauseMember
    apply (clauseTriangle_score_eq_two_iff clause side).2
    have clauseSat := satisfies clause clauseMember
    simpa [side, Clause.Satisfies] using clauseSat
  simp [gadgetThreshold, pairTotal, clauseTotal]

theorem satisfies_of_maxCut
    (formula : Formula) (maxCut : MaxCut (executable formula)) :
    Formula.Satisfiable formula := by
  rcases maxCut with ⟨side, threshold⟩
  change gadgetThreshold formula ≤ CutSize (gadgetGraph formula) side at threshold
  rw [gadget_cut_score] at threshold
  have pairBound := literalPairScore_le (variableHorizon formula) side
  have clauseBound := clauseScore_le formula side
  have pairTotal :
      literalPairScore (variableHorizon formula) side = variableHorizon formula := by
    change gadgetThreshold formula ≤ _ at threshold
    simp only [gadgetThreshold] at threshold
    omega
  have clauseTotal : clauseScore formula side = 2 * formula.length := by
    change gadgetThreshold formula ≤ _ at threshold
    simp only [gadgetThreshold] at threshold
    omega
  refine ⟨assignmentOfSide side, ?_⟩
  intro clause clauseMember
  have localTotal :=
    (clauseScore_eq_bound_iff formula side).1 clauseTotal clause clauseMember
  have localNAE := (clauseTriangle_score_eq_two_iff clause side).1 localTotal
  have firstBound := literal_var_lt_variableHorizon formula clauseMember (Or.inl rfl)
  have secondBound := literal_var_lt_variableHorizon formula clauseMember (Or.inr (Or.inl rfl))
  have thirdBound := literal_var_lt_variableHorizon formula clauseMember (Or.inr (Or.inr rfl))
  have allPairs :=
    (literalPairScore_eq_bound_iff (variableHorizon formula) side).1 pairTotal
  have firstEval := literal_eval_assignmentOfSide side clause.first
    (allPairs clause.first.var firstBound)
  have secondEval := literal_eval_assignmentOfSide side clause.second
    (allPairs clause.second.var secondBound)
  have thirdEval := literal_eval_assignmentOfSide side clause.third
    (allPairs clause.third.var thirdBound)
  simpa [Clause.Satisfies, firstEval, secondEval, thirdEval] using localNAE

theorem executable_correct (formula : Formula) :
    Formula.Satisfiable formula ↔ MaxCut (executable formula) := by
  constructor
  · rintro ⟨assignment, satisfies⟩
    exact maxCut_of_satisfies formula assignment satisfies
  · exact satisfies_of_maxCut formula

/-! ### Exact public endpoints and raw reduction evidence -/

/-- Canonical exact public NAE-3SAT source endpoint. -/
abbrev sourceProblem : Encoding.PresentedProblem :=
  Presentation.NAEThreeSAT.structuredProblem

/-- Canonical exact structured MaxCut target endpoint. -/
abbrev targetProblem : Encoding.PresentedProblem :=
  Presentation.MaxCut.structuredProblem

/-- Raw endpoint-exact direct-TM Karp reduction for staged authoring. -/
noncomputable def naeThreeSATToMaxCutStructuredTMKarpReduction :
    TMKarpReduction sourceProblem.toEncodedDecisionProblem
      targetProblem.toEncodedDecisionProblem where
  f := executable
  polytime := by
    simpa [sourceProblem, targetProblem,
      Presentation.NAEThreeSAT.structuredProblem,
      Presentation.NAEThreeSAT.structuredPresentation,
      Presentation.MaxCut.structuredProblem,
      Presentation.MaxCut.structuredPresentation] using executable_tmPolyTime
  correct := by
    intro formula
    change Formula.Satisfiable formula ↔ MaxCut (executable formula)
    exact executable_correct formula

assert_standard_axioms
  literalPairEdges_length,
  clauseTriangleEdges_length,
  clauseTriangleEdgeList_length,
  gadgetEdges_length,
  triangleBoolScore_le_two,
  triangleBoolScore_eq_two_iff,
  clauseTriangle_score_eq_two_iff,
  literalPairScore_eq_bound_iff,
  literal_var_lt_variableHorizon,
  gadgetGraph_wellFormed,
  maxCut_of_satisfies,
  satisfies_of_maxCut,
  executable_correct,
  literalPairEdge_tmPolyTime,
  literalPairEdges_tmPolyTime,
  clauseTriangleEdges_tmPolyTime,
  clauseTriangleEdgeList_tmPolyTime,
  gadgetGraph_tmPolyTime,
  gadgetThreshold_tmPolyTime,
  executable_tmPolyTime,
  executable_polynomialSizeBound,
  naeThreeSATToMaxCutStructuredTMKarpReduction

end NAEThreeSATToMaxCut
end Domain
end ComplexityReduction
