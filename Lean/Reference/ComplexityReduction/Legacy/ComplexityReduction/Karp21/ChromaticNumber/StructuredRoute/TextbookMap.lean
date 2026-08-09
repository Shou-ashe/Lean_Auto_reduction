import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ChromaticNumber.StructuredRoute.ClauseFold

namespace ComplexityReduction
namespace Karp21
namespace ChromaticNumber

open ComplexityReduction.Combinatorics.Graph

/-!
Checked assembly of the P16c structured 3SAT-to-Chromatic-Number map.

The construction uses the encoded input length as a TM-friendly variable bound.
This bound is at least the semantic CNF variable bound, so the textbook coloring
proof applies without requiring an exact `cnfVarBound` runner.
-/

def textbookEdgesForInput (p : ClauseEdgesFromInput) : List (Nat × Nat) :=
  (paletteEdges ++ variableEdges p.1) ++ clauseEdgesFromFromInput p

theorem textbookEdgesForInput_tm_polytime :
    TMPolyTimeMap
      clauseEdgesFromInputEncodedType
      edgeListStructuredEncodedType
      textbookEdgesForInput := by
  let X := clauseEdgesFromInputEncodedType
  have hN : TMPolyTimeMap X EncodedType.nat (fun p : ClauseEdgesFromInput => p.1) := by
    simpa [X, clauseEdgesFromInputEncodedType, ClauseEdgesFromInput] using
      TMPolyTimeMap.fst EncodedType.nat cnfStructuredEncodedType
  have hPalette :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun _ : ClauseEdgesFromInput => paletteEdges) :=
    TMPolyTimeMap.const X edgeListStructuredEncodedType paletteEdges
  have hVariable :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : ClauseEdgesFromInput => variableEdges p.1) := by
    have hComp := TMPolyTimeMap.comp variableEdges_tm_polytime hN
    simpa [Function.comp, X] using hComp
  have hPVInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun p : ClauseEdgesFromInput => (paletteEdges, variableEdges p.1)) :=
    TMPolyTimeMap.prod_mk hPalette hVariable
  have hPV :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : ClauseEdgesFromInput => paletteEdges ++ variableEdges p.1) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append edgeStructuredEncodedType) hPVInput
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hClause : TMPolyTimeMap X edgeListStructuredEncodedType clauseEdgesFromFromInput := by
    simpa [X] using clauseEdgesFrom_tm_polytime
  have hAllInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun p : ClauseEdgesFromInput =>
          (paletteEdges ++ variableEdges p.1, clauseEdgesFromFromInput p)) :=
    TMPolyTimeMap.prod_mk hPV hClause
  have hAll := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append edgeStructuredEncodedType) hAllInput
  simpa [Function.comp, textbookEdgesForInput, edgeListStructuredEncodedType, X] using hAll

def threeSATBoundedClauseInput (φ : SAT.ThreeCNF) : ClauseEdgesFromInput :=
  (threeCNFStructuredEncodedType.inputSize φ, φ.clauses)

theorem threeCNFClauses_tm_polytime :
    TMPolyTimeMap
      threeCNFStructuredEncodedType
      cnfStructuredEncodedType
      (fun φ : SAT.ThreeCNF => φ.clauses) :=
  (TMBackedCostedMap.ofEncodingEquiv
    threeCNFStructuredEncodedType cnfStructuredEncodedType
    (fun φ : SAT.ThreeCNF => φ.clauses)
    (Equiv.refl cnfStructuredEncodedType.Symbol)
    (by
      intro φ
      change
        cnfStructuredEncodedType.encode φ.clauses =
          (cnfStructuredEncodedType.encode φ.clauses).map id
      simp)).tm_polytime

theorem threeSATBoundedClauseInput_tm_polytime :
    TMPolyTimeMap
      threeCNFStructuredEncodedType
      clauseEdgesFromInputEncodedType
      threeSATBoundedClauseInput := by
  have hBound :
      TMPolyTimeMap
        threeCNFStructuredEncodedType
        EncodedType.nat
        (fun φ : SAT.ThreeCNF => threeCNFStructuredEncodedType.inputSize φ) :=
    (encodedInputSizeNatTMBackedMap threeCNFStructuredEncodedType).tm_polytime
  have hPair := TMPolyTimeMap.prod_mk hBound threeCNFClauses_tm_polytime
  simpa [threeSATBoundedClauseInput, clauseEdgesFromInputEncodedType] using hPair

def threeSATTextbookEdgesTM (φ : SAT.ThreeCNF) : List (Nat × Nat) :=
  textbookEdgesForInput (threeSATBoundedClauseInput φ)

theorem threeSATTextbookEdgesTM_tm_polytime :
    TMPolyTimeMap
      threeCNFStructuredEncodedType
      edgeListStructuredEncodedType
      threeSATTextbookEdgesTM := by
  have hComp :=
    TMPolyTimeMap.comp textbookEdgesForInput_tm_polytime threeSATBoundedClauseInput_tm_polytime
  simpa [Function.comp, threeSATTextbookEdgesTM] using hComp

def threeSATBoundedVertexCount (φ : SAT.ThreeCNF) : Nat :=
  textbookVertexCount (threeCNFStructuredEncodedType.inputSize φ)
    (Clique.threeCNFClauseCount φ)

theorem threeSATBoundedVertexCount_tm_polytime :
    TMPolyTimeMap
      threeCNFStructuredEncodedType
      EncodedType.nat
      threeSATBoundedVertexCount := by
  have hBound :
      TMPolyTimeMap
        threeCNFStructuredEncodedType
        EncodedType.nat
        (fun φ : SAT.ThreeCNF => threeCNFStructuredEncodedType.inputSize φ) :=
    (encodedInputSizeNatTMBackedMap threeCNFStructuredEncodedType).tm_polytime
  have hClauses :
      TMPolyTimeMap
        threeCNFStructuredEncodedType
        EncodedType.nat
        Clique.threeCNFClauseCount :=
    Clique.threeCNFClauseCountTMBackedMap.tm_polytime
  have hPair :
      TMPolyTimeMap
        threeCNFStructuredEncodedType
        natAddInputEncodedType
        (fun φ : SAT.ThreeCNF =>
          (threeCNFStructuredEncodedType.inputSize φ, Clique.threeCNFClauseCount φ)) :=
    TMPolyTimeMap.prod_mk hBound hClauses
  have hComp := TMPolyTimeMap.comp textbookVertexCountComponents_tm_polytime hPair
  simpa [Function.comp, threeSATBoundedVertexCount, textbookVertexCountComponents] using hComp

def threeSATBoundedGraph (φ : SAT.ThreeCNF) : GraphInput where
  vertices := threeSATBoundedVertexCount φ
  edges := threeSATTextbookEdgesTM φ
  directed := false

theorem threeSATBoundedGraph_tm_polytime :
    TMPolyTimeMap
      threeCNFStructuredEncodedType
      graphStructuredEncodedType
      threeSATBoundedGraph := by
  have hVertices := threeSATBoundedVertexCount_tm_polytime
  have hEdges := threeSATTextbookEdgesTM_tm_polytime
  have hDirected :
      TMPolyTimeMap
        threeCNFStructuredEncodedType
        EncodedType.bool
        (fun _ : SAT.ThreeCNF => false) :=
    TMPolyTimeMap.const threeCNFStructuredEncodedType EncodedType.bool false
  have hPayload :
      TMPolyTimeMap
        threeCNFStructuredEncodedType
        graphPayloadStructuredEncodedType
        (fun φ : SAT.ThreeCNF => (threeSATTextbookEdgesTM φ, false)) :=
    TMPolyTimeMap.prod_mk hEdges hDirected
  have hTuple :
      TMPolyTimeMap
        threeCNFStructuredEncodedType
        graphTupleStructuredEncodedType
        (fun φ : SAT.ThreeCNF =>
          (threeSATBoundedVertexCount φ, (threeSATTextbookEdgesTM φ, false))) :=
    TMPolyTimeMap.prod_mk hVertices hPayload
  have hGraph := TMPolyTimeMap.comp Clique.graphTupleToGraphTMBackedMap.tm_polytime hTuple
  simpa [Function.comp, Clique.graphTupleToGraph, threeSATBoundedGraph] using hGraph

def threeSATToChromaticNumberStructuredTMMap (φ : SAT.ThreeCNF) :
    ChromaticNumberInput where
  graph := threeSATBoundedGraph φ
  colors := 3

theorem threeSATToChromaticNumberStructuredTMMap_tm_polytime :
    TMPolyTimeMap
      threeCNFStructuredEncodedType
      chromaticNumberStructuredEncodedType
      threeSATToChromaticNumberStructuredTMMap := by
  have hGraph := threeSATBoundedGraph_tm_polytime
  have hColors :
      TMPolyTimeMap
        threeCNFStructuredEncodedType
        EncodedType.nat
        (fun _ : SAT.ThreeCNF => (3 : Nat)) :=
    TMPolyTimeMap.const threeCNFStructuredEncodedType EncodedType.nat (3 : Nat)
  have hTuple :
      TMPolyTimeMap
        threeCNFStructuredEncodedType
        chromaticNumberTupleStructuredEncodedType
        (fun φ : SAT.ThreeCNF => (threeSATBoundedGraph φ, (3 : Nat))) :=
    TMPolyTimeMap.prod_mk hGraph hColors
  have hOut :=
    TMPolyTimeMap.comp chromaticNumberTupleToChromaticNumberInputTMBackedMap.tm_polytime
      hTuple
  simpa [Function.comp, chromaticNumberTupleToChromaticNumberInput,
    threeSATToChromaticNumberStructuredTMMap] using hOut

theorem threeSATBounded_var_lt (φ : SAT.ThreeCNF) :
    ∀ c ∈ φ.clauses, ∀ l ∈ c,
      l.var < threeCNFStructuredEncodedType.inputSize φ := by
  intro c hc l hl
  have hVar := Clique.var_lt_cnfVarBound_of_mem hc hl
  have hBound := cnfVarBound_le_threeCNFStructured_inputSize φ
  omega

theorem threeSATToChromaticNumberStructuredTMMap_colorable_of_satisfies
    (φ : SAT.ThreeCNF) (a : SAT.Assignment)
    (hSat : φ.Satisfies a) :
    ChromaticNumber (threeSATToChromaticNumberStructuredTMMap φ) := by
  let n := threeCNFStructuredEncodedType.inputSize φ
  refine ⟨forwardColorFrom a n φ.clauses 0, ?_⟩
  constructor
  · intro v hv
    exact forwardColorFrom_lt_three a n φ.clauses 0 v
  · intro e he
    simp [threeSATToChromaticNumberStructuredTMMap, threeSATBoundedGraph,
      threeSATTextbookEdgesTM, textbookEdgesForInput, threeSATBoundedClauseInput,
      clauseEdgesFromFromInput, n] at he ⊢
    rcases he with hPalette | hVar | hClause
    · simp [paletteEdges] at hPalette
      rcases hPalette with rfl | rfl | rfl
      · simp [forwardColorFrom_base, forwardColorFrom_true]
      · simp [forwardColorFrom_base, forwardColorFrom_false]
      · simp [forwardColorFrom_true, forwardColorFrom_false]
    · rcases List.mem_flatMap.mp hVar with ⟨i, hiRange, hiEdge⟩
      have hi : i < n := by
        simpa [n] using hiRange
      simp [variableEdgesFor] at hiEdge
      rcases hiEdge with rfl | rfl | rfl
      · rw [forwardColorFrom_pos (a := a) (n := n) hi, forwardColorFrom_base]
        by_cases hai : a i <;> simp [hai]
      · rw [forwardColorFrom_neg (a := a) (n := n) hi, forwardColorFrom_base]
        by_cases hai : a i <;> simp [hai]
      · rw [forwardColorFrom_pos (a := a) (n := n) hi,
          forwardColorFrom_neg (a := a) (n := n) hi]
        by_cases hai : a i <;> simp [hai]
    · exact forwardColorFrom_clauseEdgesFrom_ne
        (a := a) (n := n) (j := 0) (cs := φ.clauses) (e := e)
        (fun c hc => φ.isThree c hc)
        (fun c hc l hl => threeSATBounded_var_lt φ c hc l hl)
        (fun c hc => hSat c hc)
        hClause

theorem threeSATToChromaticNumberStructuredTMMap_correct (φ : SAT.ThreeCNF) :
    SAT.threeSATDecisionProblem.isYes φ ↔
      ChromaticNumber (threeSATToChromaticNumberStructuredTMMap φ) := by
  constructor
  · intro hYes
    rcases (SAT.threeSATDecisionProblem_isYes_iff φ).1 hYes with ⟨a, hSat⟩
    exact threeSATToChromaticNumberStructuredTMMap_colorable_of_satisfies φ a hSat
  · rintro ⟨colorOf, hProper⟩
    refine (SAT.threeSATDecisionProblem_isYes_iff φ).2
      ⟨decodedAssignment colorOf, ?_⟩
    let n := threeCNFStructuredEncodedType.inputSize φ
    apply clauses_satisfy_of_clauseEdgesFrom_proper
      (colorOf := colorOf)
      (n := n)
      (totalM := φ.clauses.length)
      (j := 0)
      (cs := φ.clauses)
    · simp
    · exact fun c hc => φ.isThree c hc
    · exact fun c hc l hl => by
        simpa [n] using threeSATBounded_var_lt φ c hc l hl
    · intro v hv
      exact hProper.1 v (by
        simpa [threeSATToChromaticNumberStructuredTMMap, threeSATBoundedGraph,
          threeSATBoundedVertexCount, n, Clique.threeCNFClauseCount] using hv)
    · exact hProper.2 (baseVertex, trueVertex) (by
        simp [threeSATToChromaticNumberStructuredTMMap, threeSATBoundedGraph,
          threeSATTextbookEdgesTM, textbookEdgesForInput, threeSATBoundedClauseInput,
          paletteEdges])
    · exact hProper.2 (baseVertex, falseVertex) (by
        simp [threeSATToChromaticNumberStructuredTMMap, threeSATBoundedGraph,
          threeSATTextbookEdgesTM, textbookEdgesForInput, threeSATBoundedClauseInput,
          paletteEdges])
    · exact hProper.2 (trueVertex, falseVertex) (by
        simp [threeSATToChromaticNumberStructuredTMMap, threeSATBoundedGraph,
          threeSATTextbookEdgesTM, textbookEdgesForInput, threeSATBoundedClauseInput,
          paletteEdges])
    · intro c hc l hl
      have hvar := threeSATBounded_var_lt φ c hc l hl
      cases l with
      | mk var neg =>
          simp at hvar
          cases neg
          · simpa [literalVertex] using
              hProper.2 (posVertex var, baseVertex) (by
                simp [threeSATToChromaticNumberStructuredTMMap, threeSATBoundedGraph,
                  threeSATTextbookEdgesTM, textbookEdgesForInput, threeSATBoundedClauseInput,
                  variableEdge_pos_base_mem hvar])
          · simpa [literalVertex] using
              hProper.2 (negVertex var, baseVertex) (by
                simp [threeSATToChromaticNumberStructuredTMMap, threeSATBoundedGraph,
                  threeSATTextbookEdgesTM, textbookEdgesForInput, threeSATBoundedClauseInput,
                  variableEdge_neg_base_mem hvar])
    · intro i hi
      exact hProper.2 (posVertex i, negVertex i) (by
        simp [threeSATToChromaticNumberStructuredTMMap, threeSATBoundedGraph,
          threeSATTextbookEdgesTM, textbookEdgesForInput, threeSATBoundedClauseInput]
        exact Or.inr (Or.inl (variableEdge_pos_neg_mem hi)))
    · intro e he
      exact hProper.2 e (by
        simp [threeSATToChromaticNumberStructuredTMMap, threeSATBoundedGraph,
          threeSATTextbookEdgesTM, textbookEdgesForInput, threeSATBoundedClauseInput,
          clauseEdgesFromFromInput]
        exact Or.inr (Or.inr (by simpa [n] using he)))

theorem threeSATTextbookEdgesTM_inputSize_le (φ : SAT.ThreeCNF) :
    edgeListStructuredEncodedType.inputSize (threeSATTextbookEdgesTM φ) ≤
      1000000000000 * (threeCNFStructuredEncodedType.inputSize φ) ^ 4 +
        1000000000000 := by
  let S := threeCNFStructuredEncodedType.inputSize φ
  let p := threeSATBoundedClauseInput φ
  have hAppend :
      edgeListStructuredEncodedType.inputSize (threeSATTextbookEdgesTM φ) =
        edgeListStructuredEncodedType.inputSize paletteEdges +
          edgeListStructuredEncodedType.inputSize (variableEdges S) +
          edgeListStructuredEncodedType.inputSize (clauseEdgesFromFromInput p) := by
    let clause := clauseEdgesFromFromInput p
    have hFirst :=
      ComplexityReduction.Karp21.list_inputSize_append edgeStructuredEncodedType
        paletteEdges (variableEdges S ++ clause)
    have hSecond :=
      ComplexityReduction.Karp21.list_inputSize_append edgeStructuredEncodedType
        (variableEdges S) clause
    calc
      edgeListStructuredEncodedType.inputSize (threeSATTextbookEdgesTM φ)
          =
        edgeListStructuredEncodedType.inputSize (paletteEdges ++ (variableEdges S ++ clause)) := by
          simp [threeSATTextbookEdgesTM, textbookEdgesForInput, threeSATBoundedClauseInput,
            p, S, clause, List.append_assoc]
      _ =
        edgeListStructuredEncodedType.inputSize paletteEdges +
          edgeListStructuredEncodedType.inputSize (variableEdges S ++ clause) := by
          simpa [edgeListStructuredEncodedType] using hFirst
      _ =
        edgeListStructuredEncodedType.inputSize paletteEdges +
          (edgeListStructuredEncodedType.inputSize (variableEdges S) +
            edgeListStructuredEncodedType.inputSize clause) := by
          rw [show edgeListStructuredEncodedType.inputSize (variableEdges S ++ clause) =
            edgeListStructuredEncodedType.inputSize (variableEdges S) +
              edgeListStructuredEncodedType.inputSize clause by
              simpa [edgeListStructuredEncodedType] using hSecond]
      _ =
        edgeListStructuredEncodedType.inputSize paletteEdges +
          edgeListStructuredEncodedType.inputSize (variableEdges S) +
          edgeListStructuredEncodedType.inputSize (clauseEdgesFromFromInput p) := by
          simp [clause, Nat.add_assoc]
  have hPalette : edgeListStructuredEncodedType.inputSize paletteEdges ≤ 100 := by
    native_decide
  have hVariable :
      edgeListStructuredEncodedType.inputSize (variableEdges S) ≤ 100 * (S + 1) ^ 2 + 100 := by
    simpa [S, EncodedType.inputSize_nat] using variableEdges_structured_inputSize_le S
  have hpSize : clauseEdgesFromInputEncodedType.inputSize p = 2 * S + 2 := by
    dsimp [p, threeSATBoundedClauseInput, clauseEdgesFromInputEncodedType]
    rw [EncodedType.inputSize_prod]
    simp [S, threeCNFStructuredEncodedType, EncodedType.inputSize, EncodedType.nat]
    omega
  have hClause :
      edgeListStructuredEncodedType.inputSize (clauseEdgesFromFromInput p) ≤
        1000000000 * (2 * S + 2) ^ 3 + 1000000000 := by
    have h := clauseEdgesFromFromInput_structured_inputSize_le p
    simpa [hpSize] using h
  calc
    edgeListStructuredEncodedType.inputSize (threeSATTextbookEdgesTM φ)
        =
      edgeListStructuredEncodedType.inputSize paletteEdges +
        edgeListStructuredEncodedType.inputSize (variableEdges S) +
        edgeListStructuredEncodedType.inputSize (clauseEdgesFromFromInput p) := hAppend
    _ ≤
      100 + (100 * (S + 1) ^ 2 + 100) +
        (1000000000 * (2 * S + 2) ^ 3 + 1000000000) := by
        omega
    _ ≤ 1000000000000 * S ^ 4 + 1000000000000 := by
        cases S with
        | zero =>
            norm_num
        | succ S =>
            ring_nf
            omega

theorem threeSATBoundedVertexCount_le_inputSize_linear (φ : SAT.ThreeCNF) :
    threeSATBoundedVertexCount φ ≤
      6 * threeCNFStructuredEncodedType.inputSize φ + 3 := by
  let S := threeCNFStructuredEncodedType.inputSize φ
  have hClauses : φ.clauses.length ≤ S := by
    simpa [S, Clique.threeCNFClauseCount] using Clique.threeCNFClauseCount_le_inputSize φ
  simp [threeSATBoundedVertexCount, textbookVertexCount, variableLimit,
    Clique.threeCNFClauseCount]
  omega

theorem threeSATToChromaticNumberStructuredTMMap_inputSize_le (φ : SAT.ThreeCNF) :
    chromaticNumberStructuredEncodedType.inputSize
        (threeSATToChromaticNumberStructuredTMMap φ) ≤
      10000000000000 * (threeCNFStructuredEncodedType.inputSize φ) ^ 4 +
        10000000000000 := by
  let S := threeCNFStructuredEncodedType.inputSize φ
  have hEdges := threeSATTextbookEdgesTM_inputSize_le φ
  have hVertices := threeSATBoundedVertexCount_le_inputSize_linear φ
  calc
    chromaticNumberStructuredEncodedType.inputSize
          (threeSATToChromaticNumberStructuredTMMap φ)
        =
      graphStructuredEncodedType.inputSize (threeSATBoundedGraph φ) + 3 + 2 := by
        rw [chromaticNumberStructured_inputSize_eq]
        simp [threeSATToChromaticNumberStructuredTMMap]
    _ =
      threeSATBoundedVertexCount φ +
          edgeListStructuredEncodedType.inputSize (threeSATTextbookEdgesTM φ) + 4 +
        3 + 2 := by
        rw [Clique.graphStructured_inputSize_eq]
        simp [threeSATBoundedGraph]
    _ ≤
      (6 * S + 3) + (1000000000000 * S ^ 4 + 1000000000000) + 4 +
        3 + 2 := by
        simpa [S] using Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hVertices hEdges)
          (Nat.le_refl 4)) (Nat.le_refl (3 + 2))
    _ ≤ 10000000000000 * S ^ 4 + 10000000000000 := by
        cases S with
        | zero =>
            norm_num
        | succ S =>
            ring_nf
            omega

theorem threeSATToChromaticNumberStructuredTMMap_polynomialSizeBound :
    PolynomialSizeBound
      (fun φ : SAT.ThreeCNF => threeCNFStructuredEncodedType.inputSize φ)
      (fun I : ChromaticNumberInput => chromaticNumberStructuredEncodedType.inputSize I)
      threeSATToChromaticNumberStructuredTMMap := by
  refine PolynomialSizeBound.intro_with 4 10000000000000 10000000000000 ?_
  intro φ
  exact threeSATToChromaticNumberStructuredTMMap_inputSize_le φ

noncomputable def threeSATToChromaticNumberStructuredTMBackedMap :
    TMBackedCostedMap
      threeCNFStructuredEncodedType
      chromaticNumberStructuredEncodedType
      threeSATToChromaticNumberStructuredTMMap where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      threeSATToChromaticNumberStructuredTMMap_polynomialSizeBound
  tm_polytime := threeSATToChromaticNumberStructuredTMMap_tm_polytime

noncomputable def threeSATToChromaticNumberStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      threeSATStructuredDecisionProblem chromaticNumberStructuredDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    threeSATToChromaticNumberStructuredTMBackedMap
    (by
      intro φ
      simpa [threeSATStructuredDecisionProblem, chromaticNumberStructuredDecisionProblem]
        using threeSATToChromaticNumberStructuredTMMap_correct φ)

/--
Public structured 3SAT-to-Chromatic-Number reduction, projected from the direct
TM-backed witness.
-/
noncomputable def threeSATToChromaticNumberStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      threeSATStructuredDecisionProblem chromaticNumberStructuredDecisionProblem :=
  threeSATToChromaticNumberStructuredTMBackedKarpReduction.toCostedKarpReduction

/-- Direct TM-facing structured 3SAT-to-Chromatic-Number reduction. -/
noncomputable def threeSATToChromaticNumberStructuredTMKarpReduction :
    TMKarpReduction threeSATStructuredDecisionProblem chromaticNumberStructuredDecisionProblem :=
  threeSATToChromaticNumberStructuredTMBackedKarpReduction.toTMKarpReduction

end ChromaticNumber
end Karp21
end ComplexityReduction
