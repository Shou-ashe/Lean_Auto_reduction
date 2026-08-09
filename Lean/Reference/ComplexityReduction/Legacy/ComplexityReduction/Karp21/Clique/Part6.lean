import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Clique.Part5

namespace ComplexityReduction
namespace Karp21
namespace Clique

open ComplexityReduction.Combinatorics.Graph

/-! #### TM-backed compatibility edges directly from indexed occurrences -/

def cliqueCompatibilityEdgesFromOccurrences
    (xs : List indexedLiteralOccurrenceEncodedType.Carrier) :
    List edgeStructuredEncodedType.Carrier :=
  cliqueCompatibilityEdgesFromItems (cliqueCompatibilityItemsFromOccurrences xs)

theorem cliqueCompatibilityEdgesFromOccurrences_inputSize_le
    (xs : List indexedLiteralOccurrenceEncodedType.Carrier) :
    edgeListStructuredEncodedType.inputSize (cliqueCompatibilityEdgesFromOccurrences xs) ≤
      10000000000 * ((EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize xs) ^ 6 +
        10000000000 := by
  let N := (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize xs
  let items := cliqueCompatibilityItemsFromOccurrences xs
  let M := (EncodedType.list cliqueCompatibilityEdgeItemEncodedType).inputSize items
  have hItems : M ≤ 200 * N ^ 2 + 100 := by
    simpa [M, N, items] using cliqueCompatibilityItemsFromOccurrences_inputSize_le xs
  have hEdges :
      edgeListStructuredEncodedType.inputSize (cliqueCompatibilityEdgesFromItems items) ≤
        200 * M ^ 3 + 100 := by
    simpa [M, items] using cliqueCompatibilityEdgesFromItems_inputSize_le items
  have hMmono : M ^ 3 ≤ (200 * N ^ 2 + 100) ^ 3 := by
    exact Nat.pow_le_pow_left hItems 3
  have hEdges' :
      edgeListStructuredEncodedType.inputSize (cliqueCompatibilityEdgesFromItems items) ≤
        200 * (200 * N ^ 2 + 100) ^ 3 + 100 := by
    exact hEdges.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 200 hMmono) 100)
  have hPoly :
      200 * (200 * N ^ 2 + 100) ^ 3 + 100 ≤
        10000000000 * N ^ 6 + 10000000000 := by
    nlinarith [sq_nonneg (N : Int)]
  exact hEdges'.trans (by simpa [cliqueCompatibilityEdgesFromOccurrences, items, N] using hPoly)

theorem cliqueCompatibilityEdgesFromOccurrences_polynomialSizeBound :
    PolynomialSizeBound
      (fun xs : List indexedLiteralOccurrenceEncodedType.Carrier =>
        (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize xs)
      (fun edges : List edgeStructuredEncodedType.Carrier =>
        edgeListStructuredEncodedType.inputSize edges)
      cliqueCompatibilityEdgesFromOccurrences := by
  refine PolynomialSizeBound.intro_with 6 10000000000 10000000000 ?_
  intro xs
  exact cliqueCompatibilityEdgesFromOccurrences_inputSize_le xs

theorem cliqueCompatibilityEdgesFromOccurrences_tm_polytime :
    TMPolyTimeMap
      (EncodedType.list indexedLiteralOccurrenceEncodedType)
      edgeListStructuredEncodedType
      cliqueCompatibilityEdgesFromOccurrences := by
  have hComp :=
    TMPolyTimeMap.comp cliqueCompatibilityEdgesFromItems_tm_polytime
      cliqueCompatibilityItemsFromOccurrences_tm_polytime
  simpa [Function.comp, cliqueCompatibilityEdgesFromOccurrences] using hComp

noncomputable def cliqueCompatibilityEdgesFromOccurrencesTMBackedMap :
    TMBackedCostedMap
      (EncodedType.list indexedLiteralOccurrenceEncodedType)
      edgeListStructuredEncodedType
      cliqueCompatibilityEdgesFromOccurrences where
  costed := CostedMap.of_encodedPolynomialSizeBound
    cliqueCompatibilityEdgesFromOccurrences_polynomialSizeBound
  tm_polytime := cliqueCompatibilityEdgesFromOccurrences_tm_polytime

/-! #### Membership semantics for the compatibility-edge folds -/

theorem mem_appendCompatibleEdgeStep_iff
    (edges : List edgeStructuredEncodedType.Carrier)
    (candidate : cliqueEdgeCandidateEncodedType.Carrier)
    (e : edgeStructuredEncodedType.Carrier) :
    List.Mem e (appendCompatibleEdgeStep (edges, candidate)) ↔
      List.Mem e edges ∨ cliqueEdgeCandidateCompatible candidate = true ∧ e = candidate.1 := by
  cases h : cliqueEdgeCandidateCompatible candidate
  · simp [appendCompatibleEdgeStep, h]
  · simp only [appendCompatibleEdgeStep, h, true_and]
    constructor
    · intro he
      rcases List.mem_append.mp he with heEdges | heSingleton
      · exact Or.inl heEdges
      · exact Or.inr (by simpa using heSingleton)
    · intro he
      rcases he with heEdges | heEq
      · exact List.mem_append.mpr (Or.inl heEdges)
      · exact List.mem_append.mpr (Or.inr (by simp [heEq]))

theorem mem_appendPriorCompatibleEdgeStep_edges_iff
    (edges : List edgeStructuredEncodedType.Carrier)
    (current prior : indexedLiteralOccurrenceEncodedType.Carrier)
    (e : edgeStructuredEncodedType.Carrier) :
    List.Mem e ((appendPriorCompatibleEdgeStep ((edges, current), prior)).1 :
        List edgeStructuredEncodedType.Carrier) ↔
      List.Mem e edges ∨ occurrenceCompatible prior.2 current.2 ∧ e = (prior.1, current.1) := by
  have hStep :=
    mem_appendCompatibleEdgeStep_iff edges (cliquePriorEdgeCandidate ((edges, current), prior)) e
  simpa [appendPriorCompatibleEdgeStep, cliquePriorEdgeCandidate,
    cliqueEdgeCandidateCompatible, occurrenceCompatibleBool_eq_true_iff] using hStep

theorem mem_cliquePriorEdgeRunnerFold_edges_iff
    (edges : List edgeStructuredEncodedType.Carrier)
    (current : indexedLiteralOccurrenceEncodedType.Carrier)
    (prior : List indexedLiteralOccurrenceEncodedType.Carrier)
    (e : edgeStructuredEncodedType.Carrier) :
    List.Mem e ((cliquePriorEdgeRunnerFold ((edges, current), prior)).1 :
        List edgeStructuredEncodedType.Carrier) ↔
      List.Mem e edges ∨
        ∃ p, List.Mem p (prior : List indexedLiteralOccurrenceEncodedType.Carrier) ∧
          occurrenceCompatible p.2 current.2 ∧ e = (p.1, current.1) := by
  rw [cliquePriorEdgeRunnerFold_eq]
  induction prior generalizing edges with
  | nil =>
      constructor
      · intro h
        exact Or.inl h
      · intro h
        rcases h with h | h
        · exact h
        · rcases h with ⟨p, hp, _hCompat, _hEq⟩
          cases hp
  | cons p rest ih =>
      simp only [List.foldl_cons]
      have hTail :=
        ih (appendPriorCompatibleEdgeStep ((edges, current), p)).1
      have hHead :=
        mem_appendPriorCompatibleEdgeStep_edges_iff edges current p e
      constructor
      · intro h
        rcases hTail.mp h with hStep | hRest
        · rcases hHead.mp hStep with hEdges | hPrior
          · exact Or.inl hEdges
          · rcases hPrior with ⟨hCompat, hEq⟩
            exact Or.inr ⟨p, List.mem_cons_self, hCompat, hEq⟩
        · rcases hRest with ⟨q, hq, hCompat, hEq⟩
          exact Or.inr ⟨q, List.mem_cons_of_mem p hq, hCompat, hEq⟩
      · intro h
        apply hTail.mpr
        rcases h with hEdges | hSome
        · exact Or.inl (hHead.mpr (Or.inl hEdges))
        · rcases hSome with ⟨q, hq, hCompat, hEq⟩
          rcases List.mem_cons.mp hq with hqEq | hqRest
          · subst q
            exact Or.inl (hHead.mpr (Or.inr ⟨hCompat, hEq⟩))
          · exact Or.inr ⟨q, hqRest, hCompat, hEq⟩

theorem mem_cliqueCompatibilityEdgesFromItems_fold_iff
    (items : List cliqueCompatibilityEdgeItemEncodedType.Carrier)
    (edges : List edgeStructuredEncodedType.Carrier)
    (e : edgeStructuredEncodedType.Carrier) :
    List.Mem e (items.foldl (fun edges item => cliqueCompatibilityEdgeItemStep (edges, item)) edges :
        List edgeStructuredEncodedType.Carrier) ↔
      List.Mem e edges ∨
        ∃ item, List.Mem item (items : List cliqueCompatibilityEdgeItemEncodedType.Carrier) ∧
          ∃ p, List.Mem p (item.2 : List indexedLiteralOccurrenceEncodedType.Carrier) ∧
            occurrenceCompatible p.2 item.1.2 ∧ e = (p.1, item.1.1) := by
  induction items generalizing edges with
  | nil =>
      constructor
      · intro h
        exact Or.inl h
      · intro h
        rcases h with h | h
        · exact h
        · rcases h with ⟨item, hitem, _⟩
          cases hitem
  | cons item rest ih =>
      simp only [List.foldl_cons]
      have hTail := ih (cliqueCompatibilityEdgeItemStep (edges, item))
      have hHead :
          List.Mem e (cliqueCompatibilityEdgeItemStep (edges, item)) ↔
            List.Mem e edges ∨
              ∃ p, List.Mem p (item.2 : List indexedLiteralOccurrenceEncodedType.Carrier) ∧
                occurrenceCompatible p.2 item.1.2 ∧ e = (p.1, item.1.1) := by
        simpa [cliqueCompatibilityEdgeItemStep] using
          mem_cliquePriorEdgeRunnerFold_edges_iff edges item.1 item.2 e
      constructor
      · intro h
        rcases hTail.mp h with hStep | hRest
        · rcases hHead.mp hStep with hEdges | hItem
          · exact Or.inl hEdges
          · exact Or.inr ⟨item, List.mem_cons_self, hItem⟩
        · rcases hRest with ⟨item', hitem', hWitness⟩
          exact Or.inr ⟨item', List.mem_cons_of_mem item hitem', hWitness⟩
      · intro h
        apply hTail.mpr
        rcases h with hEdges | hSome
        · exact Or.inl (hHead.mpr (Or.inl hEdges))
        · rcases hSome with ⟨item', hitem', hWitness⟩
          rcases List.mem_cons.mp hitem' with hitemEq | hitemRest
          · subst item'
            exact Or.inl (hHead.mpr (Or.inr hWitness))
          · exact Or.inr ⟨item', hitemRest, hWitness⟩

theorem mem_cliqueCompatibilityEdgesFromItems_iff
    (items : List cliqueCompatibilityEdgeItemEncodedType.Carrier)
    (e : edgeStructuredEncodedType.Carrier) :
    List.Mem e (cliqueCompatibilityEdgesFromItems items) ↔
      ∃ item, List.Mem item (items : List cliqueCompatibilityEdgeItemEncodedType.Carrier) ∧
        ∃ p, List.Mem p (item.2 : List indexedLiteralOccurrenceEncodedType.Carrier) ∧
          occurrenceCompatible p.2 item.1.2 ∧ e = (p.1, item.1.1) := by
  have h :=
    mem_cliqueCompatibilityEdgesFromItems_fold_iff items
      ([] : List edgeStructuredEncodedType.Carrier) e
  constructor
  · intro he
    rcases h.mp (by simpa [cliqueCompatibilityEdgesFromItems] using he) with hNil | hSome
    · cases hNil
    · exact hSome
  · intro hSome
    have hFold := h.mpr (Or.inr hSome)
    simpa [cliqueCompatibilityEdgesFromItems] using hFold

end Clique
end Karp21
end ComplexityReduction
