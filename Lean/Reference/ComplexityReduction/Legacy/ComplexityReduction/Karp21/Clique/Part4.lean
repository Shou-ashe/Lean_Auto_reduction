import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Clique.Part3

namespace ComplexityReduction
namespace Karp21
namespace Clique
open ComplexityReduction.Combinatorics.Graph

/-- Edge predicate for Karp's clause-literal compatibility graph. -/

noncomputable def textbookEdgeOK (φ : SAT.ThreeCNF) (u v : Nat) : Prop := by
  classical
  exact
    ∃ ou ∈ occurrenceAt? φ u, ∃ ov ∈ occurrenceAt? φ v, occurrenceCompatible ou ov

noncomputable def textbookEdgeList (φ : SAT.ThreeCNF) : List (Nat × Nat) := by
  classical
  let vertexCount := (literalOccurrences φ).length
  exact ((List.range vertexCount).product (List.range vertexCount)).filter fun e =>
    decide (textbookEdgeOK φ e.1 e.2)

theorem mem_textbookEdgeList_iff (φ : SAT.ThreeCNF) (e : Nat × Nat) :
    e ∈ textbookEdgeList φ ↔
      e.1 < (literalOccurrences φ).length ∧
        e.2 < (literalOccurrences φ).length ∧ textbookEdgeOK φ e.1 e.2 := by
  cases e with
  | mk u v =>
      simp [textbookEdgeList, and_assoc]

/-- P15s syntax-only textbook map from local 3SAT to Clique. -/
noncomputable def textbookMap (φ : SAT.ThreeCNF) : CliqueInput where
  graph :=
    { vertices := (literalOccurrences φ).length
      edges := textbookEdgeList φ
      directed := false }
  k := φ.clauses.length

def occurrenceOfVertex (φ : SAT.ThreeCNF) (v : Nat) : LiteralOccurrence :=
  (literalOccurrences φ).getD v defaultOccurrence

def clauseOfVertex (φ : SAT.ThreeCNF) (v : Nat) : Nat :=
  (occurrenceOfVertex φ v).clause

theorem occurrenceOfVertex_mem {φ : SAT.ThreeCNF} {v : Nat}
    (hv : v < (literalOccurrences φ).length) :
    occurrenceOfVertex φ v ∈ literalOccurrences φ := by
  rw [occurrenceOfVertex,
    List.getD_eq_getElem (l := literalOccurrences φ) (d := defaultOccurrence) hv]
  exact List.getElem_mem _

theorem occurrenceAt?_eq_some_occurrenceOfVertex {φ : SAT.ThreeCNF} {v : Nat}
    (hv : v < (literalOccurrences φ).length) :
    occurrenceAt? φ v = some (occurrenceOfVertex φ v) := by
  rw [occurrenceAt?, occurrenceOfVertex,
    List.getD_eq_getElem (l := literalOccurrences φ) (d := defaultOccurrence) hv,
    List.getElem?_eq_getElem hv]

theorem clauseOfVertex_lt {φ : SAT.ThreeCNF} {v : Nat}
    (hv : v < (literalOccurrences φ).length) :
    clauseOfVertex φ v < φ.clauses.length := by
  have hMem := occurrenceOfVertex_mem (φ := φ) hv
  have hLt := mem_formulaOccurrencesFrom_clause_lt (start := 0) hMem
  simpa [clauseOfVertex, literalOccurrences] using hLt

theorem occurrence_eq_of_idxOf_eq {φ : SAT.ThreeCNF} {o₁ o₂ : LiteralOccurrence}
    (h₁ : o₁ ∈ literalOccurrences φ) (h₂ : o₂ ∈ literalOccurrences φ)
    (hidx : (literalOccurrences φ).idxOf o₁ = (literalOccurrences φ).idxOf o₂) :
    o₁ = o₂ := by
  have hGet₁ := List.getElem?_idxOf h₁
  have hGet₂ := List.getElem?_idxOf h₂
  have : some o₁ = some o₂ := by
    rw [← hGet₁, hidx, hGet₂]
  exact Option.some.inj this

theorem occurrenceCompatible_of_edge {φ : SAT.ThreeCNF} {u v : Nat}
    (hu : u < (literalOccurrences φ).length) (hv : v < (literalOccurrences φ).length)
    (hEdge : HasUndirectedEdge (textbookMap φ).graph u v) :
    occurrenceCompatible (occurrenceOfVertex φ u) (occurrenceOfVertex φ v) := by
  rcases hEdge with hEdge | hEdge
  · have hOK := (mem_textbookEdgeList_iff φ (u, v)).1 hEdge |>.2.2
    rcases hOK with ⟨ou, hou, ov, hov, hCompat⟩
    have houEq : occurrenceAt? φ u = some ou := by simpa using hou
    have hovEq : occurrenceAt? φ v = some ov := by simpa using hov
    rw [occurrenceAt?_eq_some_occurrenceOfVertex hu] at houEq
    rw [occurrenceAt?_eq_some_occurrenceOfVertex hv] at hovEq
    injection houEq with hOu
    injection hovEq with hOv
    simpa [hOu, hOv] using hCompat
  · have hOK := (mem_textbookEdgeList_iff φ (v, u)).1 hEdge |>.2.2
    rcases hOK with ⟨ov, hov, ou, hou, hCompat⟩
    have houEq : occurrenceAt? φ u = some ou := by simpa using hou
    have hovEq : occurrenceAt? φ v = some ov := by simpa using hov
    rw [occurrenceAt?_eq_some_occurrenceOfVertex hu] at houEq
    rw [occurrenceAt?_eq_some_occurrenceOfVertex hv] at hovEq
    injection houEq with hOu
    injection hovEq with hOv
    rcases hCompat with ⟨hClause, hLit⟩
    exact ⟨Ne.symm (by simpa [hOu, hOv] using hClause),
      literal_compatible_symm (by simpa [hOu, hOv] using hLit)⟩

noncomputable def decodedAssignmentFromClique (φ : SAT.ThreeCNF) (vs : List Nat) :
    SAT.Assignment :=
  fun x =>
    decide
      (∃ v ∈ vs, ∃ o : LiteralOccurrence,
        occurrenceAt? φ v = some o ∧ o.lit.var = x ∧ o.lit.neg = false)

theorem selected_literal_eval_decoded {φ : SAT.ThreeCNF} {vs : List Nat}
    (hBounds : VerticesWithinBounds (textbookMap φ).graph vs)
    (hAdj : PairwiseAdjacent (textbookMap φ).graph vs) {v : Nat} (hv : v ∈ vs)
    (hLit : occurrenceAt? φ v = some (occurrenceOfVertex φ v)) :
    (occurrenceOfVertex φ v).lit.eval (decodedAssignmentFromClique φ vs) = true := by
  let o := occurrenceOfVertex φ v
  have hvBound : v < (literalOccurrences φ).length := by
    simpa [textbookMap] using hBounds v hv
  cases hneg : o.lit.neg
  · have hPos :
        ∃ w ∈ vs, ∃ ow : LiteralOccurrence,
          occurrenceAt? φ w = some ow ∧ ow.lit.var = o.lit.var ∧ ow.lit.neg = false := by
      exact ⟨v, hv, o, by simpa [o] using hLit, rfl, hneg⟩
    have hAssign : decodedAssignmentFromClique φ vs o.lit.var = true := by
      simp [decodedAssignmentFromClique, hPos]
    change o.lit.eval (decodedAssignmentFromClique φ vs) = true
    simp [SAT.Literal.eval, hneg, hAssign]
  · have hNoPos :
        ¬ ∃ w ∈ vs, ∃ ow : LiteralOccurrence,
          occurrenceAt? φ w = some ow ∧ ow.lit.var = o.lit.var ∧ ow.lit.neg = false := by
      rintro ⟨w, hw, ow, how, hVar, hNegFalse⟩
      by_cases hvw : v = w
      · subst w
        rw [hLit] at how
        injection how with hOw
        have : ow.lit.neg = true := by simpa [o, hOw] using hneg
        simp [hNegFalse] at this
      · have hwBound : w < (literalOccurrences φ).length := by
          simpa [textbookMap] using hBounds w hw
        have hEdge := hAdj v hv w hw hvw
        have hCompat := occurrenceCompatible_of_edge hvBound hwBound hEdge
        have howVertex : occurrenceOfVertex φ w = ow := by
          rw [occurrenceAt?_eq_some_occurrenceOfVertex hwBound] at how
          exact Option.some.inj how
        rcases hCompat.2 with hVarNe | hNegEq
        · exact hVarNe (by simpa [o, howVertex] using hVar.symm)
        · have hOwNeg : ow.lit.neg = true := by
            have hNegEq' : o.lit.neg = ow.lit.neg := by simpa [o, howVertex] using hNegEq
            exact hNegEq'.symm.trans hneg
          simp [hNegFalse] at hOwNeg
    have hAssign : decodedAssignmentFromClique φ vs o.lit.var = false := by
      simp [decodedAssignmentFromClique, hNoPos]
    change o.lit.eval (decodedAssignmentFromClique φ vs) = true
    simp [SAT.Literal.eval, hneg, hAssign]

theorem textbookMap_correct (φ : SAT.ThreeCNF) :
    SAT.threeSATDecisionProblem.isYes φ ↔ Clique (textbookMap φ) := by
  constructor
  · intro hYes
    rcases (SAT.threeSATDecisionProblem_isYes_iff φ).1 hYes with ⟨a, hSat⟩
    let choose : Fin φ.clauses.length → LiteralOccurrence := fun j =>
      Classical.choose (show
        ∃ o : LiteralOccurrence,
          o ∈ literalOccurrences φ ∧ o.clause = j.val ∧ o.lit.eval a = true from by
        have hClauseMem : φ.clauses[j.val] ∈ φ.clauses := List.getElem_mem _
        rcases hSat φ.clauses[j.val] hClauseMem with ⟨l, hl, hEval⟩
        rcases exists_occurrence_of_getElem (cs := φ.clauses) j.isLt hl 0 with
          ⟨o, ho, hClause, hLit⟩
        refine ⟨o, ho, ?_, ?_⟩
        · simpa using hClause
        · simpa [hLit] using hEval)
    have choose_spec :
        ∀ j : Fin φ.clauses.length,
          choose j ∈ literalOccurrences φ ∧ (choose j).clause = j.val ∧
            (choose j).lit.eval a = true := by
      intro j
      exact Classical.choose_spec (show
        ∃ o : LiteralOccurrence,
          o ∈ literalOccurrences φ ∧ o.clause = j.val ∧ o.lit.eval a = true from by
        have hClauseMem : φ.clauses[j.val] ∈ φ.clauses := List.getElem_mem _
        rcases hSat φ.clauses[j.val] hClauseMem with ⟨l, hl, hEval⟩
        rcases exists_occurrence_of_getElem (cs := φ.clauses) j.isLt hl 0 with
          ⟨o, ho, hClause, hLit⟩
        refine ⟨o, ho, ?_, ?_⟩
        · simpa using hClause
        · simpa [hLit] using hEval)
    let vertexOf : Fin φ.clauses.length → Nat := fun j =>
      (literalOccurrences φ).idxOf (choose j)
    let vs := (List.finRange φ.clauses.length).map vertexOf
    have hVertexMem : ∀ j, choose j ∈ literalOccurrences φ := fun j => (choose_spec j).1
    have hVertexBound : ∀ j, vertexOf j < (literalOccurrences φ).length := by
      intro j
      exact List.idxOf_lt_length_iff.mpr (hVertexMem j)
    have hVertexInj : ∀ i ∈ List.finRange φ.clauses.length,
        ∀ j ∈ List.finRange φ.clauses.length, vertexOf i = vertexOf j → i = j := by
      intro i _hi j _hj hEq
      have hOccEq := occurrence_eq_of_idxOf_eq (hVertexMem i) (hVertexMem j) hEq
      apply Fin.ext
      have hClauseEq := congrArg LiteralOccurrence.clause hOccEq
      simpa [(choose_spec i).2.1, (choose_spec j).2.1] using hClauseEq
    refine ⟨vs, by simp [vs, textbookMap], ?_, ?_, ?_⟩
    · exact (List.nodup_finRange φ.clauses.length).map_on hVertexInj
    · intro v hv
      rcases List.mem_map.mp hv with ⟨j, _hj, rfl⟩
      simpa [textbookMap, vertexOf] using hVertexBound j
    · intro u hu v hv huv
      rcases List.mem_map.mp hu with ⟨i, hi, rfl⟩
      rcases List.mem_map.mp hv with ⟨j, hj, rfl⟩
      have hij : i ≠ j := by
        intro h
        exact huv (by simp [h])
      have hClauseNe : (choose i).clause ≠ (choose j).clause := by
        intro h
        exact hij (Fin.ext (by simpa [(choose_spec i).2.1, (choose_spec j).2.1] using h))
      have hCompatLit :=
        literal_compatible_of_eval_true (choose_spec i).2.2 (choose_spec j).2.2
      have hEdge : (vertexOf i, vertexOf j) ∈ textbookEdgeList φ := by
        rw [mem_textbookEdgeList_iff]
        refine ⟨hVertexBound i, hVertexBound j, ?_⟩
        refine ⟨choose i, ?_, choose j, ?_, hClauseNe, hCompatLit⟩
        · simp [occurrenceAt?, vertexOf, List.getElem?_idxOf (hVertexMem i)]
        · simp [occurrenceAt?, vertexOf, List.getElem?_idxOf (hVertexMem j)]
      exact Or.inl hEdge
  · intro hClique
    rcases hClique with ⟨vs, hLen, hNodup, hBounds, hAdj⟩
    let selected : Finset Nat := vs.toFinset
    let target : Finset Nat := Finset.range φ.clauses.length
    let f : Nat → Nat := clauseOfVertex φ
    have hMaps : Set.MapsTo f selected target := by
      intro v hv
      have hvList : v ∈ vs := by simpa [selected] using hv
      have hvBound : v < (literalOccurrences φ).length := by
        simpa [textbookMap] using hBounds v hvList
      exact Finset.mem_range.mpr (clauseOfVertex_lt (φ := φ) hvBound)
    have hInj : Set.InjOn f selected := by
      intro u hu v hv hEq
      by_contra huv
      have huList : u ∈ vs := by simpa [selected] using hu
      have hvList : v ∈ vs := by simpa [selected] using hv
      have huBound : u < (literalOccurrences φ).length := by
        simpa [textbookMap] using hBounds u huList
      have hvBound : v < (literalOccurrences φ).length := by
        simpa [textbookMap] using hBounds v hvList
      have hEdge := hAdj u huList v hvList huv
      have hCompat := occurrenceCompatible_of_edge huBound hvBound hEdge
      exact hCompat.1 (by simpa [f, clauseOfVertex] using hEq)
    have hCardTarget : target.card ≤ selected.card := by
      simp [target, selected, textbookMap, List.toFinset_card_of_nodup hNodup, hLen]
    have hSurj := Finset.surjOn_of_injOn_of_card_le f hMaps hInj hCardTarget
    refine (SAT.threeSATDecisionProblem_isYes_iff φ).2 ?_
    refine ⟨decodedAssignmentFromClique φ vs, ?_⟩
    intro c hc
    let j := φ.clauses.idxOf c
    have hj : j < φ.clauses.length := List.idxOf_lt_length_iff.mpr hc
    have hjTarget : j ∈ target := by simpa [target] using hj
    rcases hSurj hjTarget with ⟨v, hvSelected, hClauseEq⟩
    have hvList : v ∈ vs := by simpa [selected] using hvSelected
    have hvBound : v < (literalOccurrences φ).length := by
      simpa [textbookMap] using hBounds v hvList
    let o := occurrenceOfVertex φ v
    have hOccMem : o ∈ literalOccurrences φ := occurrenceOfVertex_mem (φ := φ) hvBound
    have hClauseEq' : o.clause = 0 + j := by
      simpa [f, clauseOfVertex, o] using hClauseEq
    have hLitMemIndexed : o.lit ∈ φ.clauses[j] :=
      lit_mem_getElem_of_mem_formulaOccurrencesFrom (start := 0) hOccMem hClauseEq' hj
    have hClauseGet : φ.clauses[j] = c := by
      simp [j]
    refine ⟨o.lit, by simpa [hClauseGet] using hLitMemIndexed, ?_⟩
    exact selected_literal_eval_decoded hBounds hAdj hvList
      (occurrenceAt?_eq_some_occurrenceOfVertex hvBound)

theorem clauseOccurrencesFrom_length (j start : Nat) (c : SAT.Clause) :
    (clauseOccurrencesFrom j start c).length = c.length := by
  induction c generalizing start with
  | nil =>
      simp [clauseOccurrencesFrom]
  | cons _ ls ih =>
      simp [clauseOccurrencesFrom, ih]

theorem clauseOccurrences_length (j : Nat) (c : SAT.Clause) :
    (clauseOccurrences j c).length = c.length := by
  simp [clauseOccurrences, clauseOccurrencesFrom_length]

theorem formulaOccurrencesFrom_length (j : Nat) (φ : SAT.CNF) :
    (formulaOccurrencesFrom j φ).length = SAT.CNF.totalClauseLength φ := by
  induction φ generalizing j with
  | nil =>
      simp [formulaOccurrencesFrom, SAT.CNF.totalClauseLength]
  | cons c cs ih =>
      simp [formulaOccurrencesFrom, SAT.CNF.totalClauseLength, clauseOccurrences_length, ih]

theorem literalOccurrences_length_eq_totalClauseLength (φ : SAT.ThreeCNF) :
    (literalOccurrences φ).length = SAT.CNF.totalClauseLength φ.clauses := by
  simp [literalOccurrences, formulaOccurrencesFrom_length]

/-- Filtering never increases list length. -/
theorem filter_length_le {α : Type} (p : α → Bool) :
    ∀ xs : List α, (xs.filter p).length ≤ xs.length
  | [] => by simp
  | x :: xs => by
      by_cases h : p x
      · simp [h, filter_length_le p xs]
      · exact Nat.le_trans (by simpa [h] using filter_length_le p xs) (Nat.le_succ xs.length)

theorem textbookEdgeList_length_le (φ : SAT.ThreeCNF) :
    (textbookEdgeList φ).length ≤ (literalOccurrences φ).length * (literalOccurrences φ).length := by
  classical
  unfold textbookEdgeList
  let vertexCount := (literalOccurrences φ).length
  let candidates := (List.range vertexCount).product (List.range vertexCount)
  have hFilter :
      (candidates.filter fun e : Nat × Nat =>
        decide (textbookEdgeOK φ e.1 e.2)).length ≤ candidates.length :=
    filter_length_le (fun e : Nat × Nat => decide (textbookEdgeOK φ e.1 e.2)) candidates
  have hCandidates : candidates.length = vertexCount * vertexCount := by
    simpa [candidates, SProd.sprod] using
      (List.length_product (List.range vertexCount) (List.range vertexCount))
  simpa [vertexCount, candidates] using hFilter.trans (le_of_eq hCandidates)

theorem edgeStructured_inputSize_le_of_mem_textbookEdgeList {φ : SAT.ThreeCNF}
    {e : Nat × Nat} (he : e ∈ textbookEdgeList φ) :
    edgeStructuredEncodedType.inputSize e ≤ 2 * (literalOccurrences φ).length + 1 := by
  cases e with
  | mk u v =>
      have hmem := (mem_textbookEdgeList_iff φ (u, v)).1 he
      simp [edgeStructuredEncodedType] at hmem ⊢
      omega

/-- If every element encoding has size at most `B`, the delimiter-list encoding is linear in
the number of elements. -/
theorem encodedList_inputSize_le_length_mul_bound (X : EncodedType)
    (xs : List X.Carrier) (B : Nat)
    (hB : ∀ x ∈ xs, X.inputSize x ≤ B) :
    (EncodedType.list X).inputSize xs ≤ xs.length * (B + 1) := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : X.inputSize x ≤ B := hB x (by simp)
      have htail : ∀ y ∈ xs, X.inputSize y ≤ B := by
        intro y hy
        exact hB y (by simp [hy])
      have ih' := ih htail
      calc
        (EncodedType.list X).inputSize (x :: xs)
            = X.inputSize x + 1 + (EncodedType.list X).inputSize xs := by
              simp
        _ ≤ B + 1 + xs.length * (B + 1) := by
              omega
        _ = (x :: xs).length * (B + 1) := by
              simp [Nat.succ_mul, Nat.add_comm, Nat.add_assoc]

theorem textbookEdgeList_structured_inputSize_le (φ : SAT.ThreeCNF) :
    edgeListStructuredEncodedType.inputSize (textbookEdgeList φ) ≤
      ((literalOccurrences φ).length * (literalOccurrences φ).length) *
        (2 * (literalOccurrences φ).length + 2) := by
  have hList :=
    encodedList_inputSize_le_length_mul_bound edgeStructuredEncodedType
      (textbookEdgeList φ) (2 * (literalOccurrences φ).length + 1)
      (by
        intro e he
        exact edgeStructured_inputSize_le_of_mem_textbookEdgeList he)
  have hLen := textbookEdgeList_length_le φ
  exact hList.trans (by
    have hMul := Nat.mul_le_mul_right (2 * (literalOccurrences φ).length + 2) hLen
    simpa [edgeListStructuredEncodedType, Nat.add_assoc] using hMul)

theorem graphStructured_inputSize_eq (g : GraphInput) :
    graphStructuredEncodedType.inputSize g =
      g.vertices + edgeListStructuredEncodedType.inputSize g.edges + 4 := by
  change graphTupleStructuredEncodedType.inputSize (g.vertices, (g.edges, g.directed)) =
    g.vertices + edgeListStructuredEncodedType.inputSize g.edges + 4
  simp [graphTupleStructuredEncodedType, graphPayloadStructuredEncodedType]
  omega

theorem cliqueStructured_inputSize_eq (I : CliqueInput) :
    cliqueStructuredEncodedType.inputSize I =
      graphStructuredEncodedType.inputSize I.graph + I.k + 2 := by
  change cliqueTupleStructuredEncodedType.inputSize (I.graph, I.k) =
    graphStructuredEncodedType.inputSize I.graph + I.k + 2
  simp [cliqueTupleStructuredEncodedType]
  omega

theorem literalOccurrences_length_le_threeCNFStructured_inputSize (φ : SAT.ThreeCNF) :
    (literalOccurrences φ).length ≤ threeCNFStructuredEncodedType.inputSize φ := by
  have hTotal := cnfStructured_inputSize_ge_totalClauseLength_add_length φ.clauses
  rw [literalOccurrences_length_eq_totalClauseLength]
  have hTotal' :
      SAT.CNF.totalClauseLength φ.clauses + φ.clauses.length ≤
        threeCNFStructuredEncodedType.inputSize φ := by
    simpa [threeCNFStructuredEncodedType, EncodedType.inputSize] using hTotal
  omega

theorem threeCNFStructured_inputSize_ge_clauses_length (φ : SAT.ThreeCNF) :
    φ.clauses.length ≤ threeCNFStructuredEncodedType.inputSize φ := by
  have hLen := cnfStructured_inputSize_ge_length φ.clauses
  simpa [threeCNFStructuredEncodedType, EncodedType.inputSize] using hLen

theorem cliqueStructured_inputSize_textbookMap_le_threeSAT_poly (φ : SAT.ThreeCNF) :
    cliqueStructuredEncodedType.inputSize (textbookMap φ) ≤
      1000 * (threeCNFStructuredEncodedType.inputSize φ) ^ 3 + 1000 := by
  let S := threeCNFStructuredEncodedType.inputSize φ
  let V := (literalOccurrences φ).length
  have hV : V ≤ S := by
    simpa [S, V] using literalOccurrences_length_le_threeCNFStructured_inputSize φ
  have hC : φ.clauses.length ≤ S := by
    simpa [S] using threeCNFStructured_inputSize_ge_clauses_length φ
  have hEdges := textbookEdgeList_structured_inputSize_le φ
  have hBase :
      cliqueStructuredEncodedType.inputSize (textbookMap φ) ≤
        V + V * V * (2 * V + 2) + 4 + φ.clauses.length + 2 := by
    calc
      cliqueStructuredEncodedType.inputSize (textbookMap φ)
          = graphStructuredEncodedType.inputSize (textbookMap φ).graph +
              (textbookMap φ).k + 2 := cliqueStructured_inputSize_eq (textbookMap φ)
      _ ≤ V + V * V * (2 * V + 2) + 4 + φ.clauses.length + 2 := by
            rw [graphStructured_inputSize_eq]
            simp [textbookMap, V]
            simpa [V, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hEdges
  have hVV : V * V ≤ S * S := Nat.mul_le_mul hV hV
  have hTerm : V * V * (2 * V + 2) ≤ S * S * (2 * S + 2) := by
    exact Nat.mul_le_mul hVV (by omega)
  have hPolyBase :
      V + V * V * (2 * V + 2) + 4 + φ.clauses.length + 2 ≤
        S + S * S * (2 * S + 2) + 4 + S + 2 := by
    omega
  calc
    cliqueStructuredEncodedType.inputSize (textbookMap φ)
        ≤ V + V * V * (2 * V + 2) + 4 + φ.clauses.length + 2 := hBase
    _ ≤ S + S * S * (2 * S + 2) + 4 + S + 2 := hPolyBase
    _ ≤ 1000 * S ^ 3 + 1000 := by
          cases S with
          | zero =>
              norm_num
          | succ S =>
              ring_nf
              omega

theorem threeSATToCliqueStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun φ : SAT.ThreeCNF => threeCNFStructuredEncodedType.inputSize φ)
      (fun I : CliqueInput => cliqueStructuredEncodedType.inputSize I)
      textbookMap := by
  refine PolynomialSizeBound.intro_with 3 1000 1000 ?_
  intro φ
  exact cliqueStructured_inputSize_textbookMap_le_threeSAT_poly φ

/-! #### TM-backed structured Clique output assembly skeleton -/

/-- Reify the tuple-shaped graph payload as the project graph structure. -/
def graphTupleToGraph (p : graphTupleStructuredEncodedType.Carrier) : GraphInput where
  vertices := p.1
  edges := p.2.1
  directed := p.2.2

theorem graphTupleToGraph_encode (p : graphTupleStructuredEncodedType.Carrier) :
    graphStructuredEncodedType.encode (graphTupleToGraph p) =
      graphTupleStructuredEncodedType.encode p := by
  rcases p with ⟨vertices, edges, directed⟩
  rfl

noncomputable def graphTupleToGraphTMBackedMap :
    TMBackedCostedMap
      graphTupleStructuredEncodedType
      graphStructuredEncodedType
      graphTupleToGraph :=
  TMBackedCostedMap.ofEncodingEquiv
    graphTupleStructuredEncodedType graphStructuredEncodedType graphTupleToGraph
    (Equiv.refl graphTupleStructuredEncodedType.Symbol)
    (by
      intro p
      change graphStructuredEncodedType.encode (graphTupleToGraph p) =
        (graphTupleStructuredEncodedType.encode p).map id
      simp [graphTupleToGraph_encode])

/-- Reify the tuple-shaped Clique payload as the project Clique structure. -/
def cliqueTupleToCliqueInput (p : cliqueTupleStructuredEncodedType.Carrier) :
    CliqueInput where
  graph := p.1
  k := p.2

theorem cliqueTupleToCliqueInput_encode (p : cliqueTupleStructuredEncodedType.Carrier) :
    cliqueStructuredEncodedType.encode (cliqueTupleToCliqueInput p) =
      cliqueTupleStructuredEncodedType.encode p := by
  rcases p with ⟨graph, k⟩
  rfl

noncomputable def cliqueTupleToCliqueInputTMBackedMap :
    TMBackedCostedMap
      cliqueTupleStructuredEncodedType
      cliqueStructuredEncodedType
      cliqueTupleToCliqueInput :=
  TMBackedCostedMap.ofEncodingEquiv
    cliqueTupleStructuredEncodedType cliqueStructuredEncodedType cliqueTupleToCliqueInput
    (Equiv.refl cliqueTupleStructuredEncodedType.Symbol)
    (by
      intro p
      change cliqueStructuredEncodedType.encode (cliqueTupleToCliqueInput p) =
        (cliqueTupleStructuredEncodedType.encode p).map id
      simp [cliqueTupleToCliqueInput_encode])

/--
Clique output skeleton for the 3SAT-to-Clique route, omitting only the
compatibility edge list.  This is an assembly component for the full direct TM
witness, not a reduction.
-/
def cliqueStructuredSkeletonGraph (φ : SAT.ThreeCNF) : GraphInput where
  vertices := threeCNFLiteralOccurrenceCount φ
  edges := []
  directed := false

/--
Clique output skeleton with the right vertex count and target clique size.
The final route replaces the empty edge list by Karp's compatibility edges.
-/
def cliqueStructuredSkeletonMap (φ : SAT.ThreeCNF) : CliqueInput where
  graph := cliqueStructuredSkeletonGraph φ
  k := threeCNFClauseCount φ

theorem cliqueStructuredSkeleton_inputSize_le (φ : SAT.ThreeCNF) :
    cliqueStructuredEncodedType.inputSize (cliqueStructuredSkeletonMap φ) ≤
      2 * threeCNFStructuredEncodedType.inputSize φ + 6 := by
  have hVertices := threeCNFLiteralOccurrenceCount_le_inputSize φ
  have hClauses := threeCNFClauseCount_le_inputSize φ
  have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
    change (EncodedType.list edgeStructuredEncodedType).inputSize ([] : List (Nat × Nat)) = 0
    exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
  rw [cliqueStructured_inputSize_eq, graphStructured_inputSize_eq]
  change threeCNFLiteralOccurrenceCount φ +
      edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) + 4 +
      threeCNFClauseCount φ + 2 ≤
    2 * threeCNFStructuredEncodedType.inputSize φ + 6
  rw [hNil]
  omega

theorem cliqueStructuredSkeleton_linearSizeBound :
    LinearSizeBound
      (fun φ : SAT.ThreeCNF => threeCNFStructuredEncodedType.inputSize φ)
      (fun I : CliqueInput => cliqueStructuredEncodedType.inputSize I)
      cliqueStructuredSkeletonMap :=
  LinearSizeBound.intro_with 2 6 cliqueStructuredSkeleton_inputSize_le

noncomputable def cliqueStructuredSkeletonTMBackedMap :
    TMBackedCostedMap
      threeCNFStructuredEncodedType
      cliqueStructuredEncodedType
      cliqueStructuredSkeletonMap where
  costed :=
    CostedMap.of_encodedLinearSizeBound cliqueStructuredSkeleton_linearSizeBound
  tm_polytime := by
    have hVertices :
        TMPolyTimeMap
          threeCNFStructuredEncodedType
          EncodedType.nat
          threeCNFLiteralOccurrenceCount :=
      threeCNFLiteralOccurrenceCountTMBackedMap.tm_polytime
    have hEdges :
        TMPolyTimeMap
          threeCNFStructuredEncodedType
          edgeListStructuredEncodedType
          (fun _ : SAT.ThreeCNF => ([] : List (Nat × Nat))) :=
      TMPolyTimeMap.const threeCNFStructuredEncodedType edgeListStructuredEncodedType []
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
          (fun φ : SAT.ThreeCNF => (([] : List (Nat × Nat)), false)) :=
      TMPolyTimeMap.prod_mk hEdges hDirected
    have hGraphTuple :
        TMPolyTimeMap
          threeCNFStructuredEncodedType
          graphTupleStructuredEncodedType
          (fun φ : SAT.ThreeCNF =>
            (threeCNFLiteralOccurrenceCount φ, (([] : List (Nat × Nat)), false))) :=
      TMPolyTimeMap.prod_mk hVertices hPayload
    have hGraph :
        TMPolyTimeMap
          threeCNFStructuredEncodedType
          graphStructuredEncodedType
          cliqueStructuredSkeletonGraph := by
      have hComp :=
        TMPolyTimeMap.comp graphTupleToGraphTMBackedMap.tm_polytime hGraphTuple
      simpa [Function.comp, graphTupleToGraph, cliqueStructuredSkeletonGraph] using hComp
    have hK :
        TMPolyTimeMap
          threeCNFStructuredEncodedType
          EncodedType.nat
          threeCNFClauseCount :=
      threeCNFClauseCountTMBackedMap.tm_polytime
    have hCliqueTuple :
        TMPolyTimeMap
          threeCNFStructuredEncodedType
          cliqueTupleStructuredEncodedType
          (fun φ : SAT.ThreeCNF => (cliqueStructuredSkeletonGraph φ, threeCNFClauseCount φ)) :=
      TMPolyTimeMap.prod_mk hGraph hK
    have hClique :
        TMPolyTimeMap
          threeCNFStructuredEncodedType
          cliqueStructuredEncodedType
          cliqueStructuredSkeletonMap := by
      have hComp :=
        TMPolyTimeMap.comp cliqueTupleToCliqueInputTMBackedMap.tm_polytime hCliqueTuple
      simpa [Function.comp, cliqueTupleToCliqueInput, cliqueStructuredSkeletonMap] using hComp
    exact hClique

/-- Proof-carrying raw-encoding Karp reduction from local 3SAT to Clique. -/
noncomputable def threeSATToCliqueTMBackedKarpReduction :
    TMBackedCostedReduction SAT.threeSATDecisionProblem cliqueDecisionProblem := by
  simpa [cliqueDecisionProblem, cliqueEncodedType] using
    rawCodomainTMBackedReduction
      SAT.threeSATDecisionProblem
      Combinatorics.Graph.Clique
      map
      map_correct

/-- Costed Karp reduction from local 3SAT to Clique. -/
noncomputable def threeSATToCliqueKarpReduction :
    KarpReductionM CostedPolyTimeModel SAT.threeSATDecisionProblem cliqueDecisionProblem :=
  threeSATToCliqueTMBackedKarpReduction.toCostedKarpReduction

/--
Proof-carrying raw-encoding Karp reduction from local 3SAT to Clique using
Karp's clause-literal graph.
-/
noncomputable def threeSATToClique_textbookTMBackedKarpReduction :
    TMBackedCostedReduction SAT.threeSATDecisionProblem cliqueDecisionProblem := by
  simpa [cliqueDecisionProblem, cliqueEncodedType] using
    rawCodomainTMBackedReduction
      SAT.threeSATDecisionProblem
      Combinatorics.Graph.Clique
      textbookMap
      textbookMap_correct

/-- Costed Karp reduction from local 3SAT to Clique using Karp's clause-literal graph. -/
noncomputable def threeSATToClique_textbookKarpReduction :
    KarpReductionM CostedPolyTimeModel SAT.threeSATDecisionProblem cliqueDecisionProblem :=
  threeSATToClique_textbookTMBackedKarpReduction.toCostedKarpReduction

/--
Costed Karp reduction from faithful finite-alphabet bundled 3SAT to faithful
finite-alphabet Clique using Karp's clause-literal compatibility graph.

This is the original structured `CostedPolyTimeModel` transport theorem.  The
public `threeSATToCliqueStructuredKarpReduction` name is supplied later by the
direct TM-backed witness.
-/
noncomputable def threeSATToCliqueStructuredTextbookKarpReduction :
    KarpReductionM CostedPolyTimeModel
      threeSATStructuredDecisionProblem cliqueStructuredDecisionProblem where
  f :=
    { toFun := textbookMap
      polytime :=
        CostedPolyTimeMap.of_costed
          (CostedMap.of_encodedPolynomialSizeBound
            threeSATToCliqueStructured_polynomialSizeBound) }
  correct := by
    intro φ
    simpa [threeSATStructuredDecisionProblem, cliqueStructuredDecisionProblem]
      using textbookMap_correct φ

/-- The structured finite-alphabet Clique encoding is faithful. -/
theorem cliqueStructuredEncoding_faithful :
    cliqueStructuredDecisionProblem.FaithfulEncoding where
  injective := cliqueStructuredEncodedType_encode_injective

theorem cliqueStructuredEncoding_predicateRespects :
    cliqueStructuredDecisionProblem.PredicateRespectsEncoding :=
  cliqueStructuredEncoding_faithful.predicateRespects

theorem cliqueStructuredEncoding_accepts_encode_iff (I : CliqueInput) :
    cliqueStructuredDecisionProblem.toEncodedLanguage.accepts
        (cliqueStructuredEncodedType.encode I) ↔
      Clique I :=
  cliqueStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

/-- Clique is locally in NP for the project-local costed model. -/
theorem cliqueInNP :
    InNPEnc CostedPolyTimeModel cliqueDecisionProblem :=
  decidableInNP cliqueDecisionProblem

/-- Local NP-completeness of Clique via the P15b 3SAT edge. -/
theorem cliqueNPComplete :
    NPCompleteEnc CostedPolyTimeModel cliqueDecisionProblem :=
  Targets.npComplete_of_localThreeSAT_karp
    cliqueDecisionProblem
    threeSATToCliqueKarpReduction
    cliqueInNP

/-- Local NP-completeness of Clique via the P15s textbook clause-literal route. -/
theorem clique_textbookNPComplete :
    NPCompleteEnc CostedPolyTimeModel cliqueDecisionProblem :=
  Targets.npComplete_of_localThreeSAT_karp
    cliqueDecisionProblem
    threeSATToClique_textbookKarpReduction
    cliqueInNP

end Clique
end Karp21
end ComplexityReduction
