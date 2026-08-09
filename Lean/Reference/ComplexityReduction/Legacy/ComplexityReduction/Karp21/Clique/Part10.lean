import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Clique.Part9

namespace ComplexityReduction
namespace Karp21
namespace Clique

open ComplexityReduction.Combinatorics.Graph

/-! #### TM-backed compatibility edges directly from structured 3CNF -/

def cliqueCompatibilityEdgesFromThreeCNF (φ : SAT.ThreeCNF) :
    List edgeStructuredEncodedType.Carrier :=
  cliqueCompatibilityEdgesFromOccurrences (indexedLiteralOccurrences φ)

theorem cliqueCompatibilityEdgesFromThreeCNF_inputSize_le (φ : SAT.ThreeCNF) :
    edgeListStructuredEncodedType.inputSize (cliqueCompatibilityEdgesFromThreeCNF φ) ≤
      1000000000000000000000000000000000000 *
          (threeCNFStructuredEncodedType.inputSize φ) ^ 18 +
        1000000000000000000000000000000000000 := by
  let N := threeCNFStructuredEncodedType.inputSize φ
  let M :=
    (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize
      (indexedLiteralOccurrences φ)
  have hOccurrences : M ≤ 1000 * N ^ 3 + 1000 := by
    have hClique := cliqueIndexedLiteralOccurrences_inputSize_le φ
    rw [cliqueIndexedLiteralOccurrences_eq_indexedLiteralOccurrences φ] at hClique
    simpa [M, N] using hClique
  have hEdges :
      edgeListStructuredEncodedType.inputSize
          (cliqueCompatibilityEdgesFromOccurrences (indexedLiteralOccurrences φ)) ≤
        10000000000 * M ^ 6 + 10000000000 := by
    simpa [M] using
      cliqueCompatibilityEdgesFromOccurrences_inputSize_le (indexedLiteralOccurrences φ)
  have hTarget :
      10000000000 * M ^ 6 + 10000000000 ≤
        1000000000000000000000000000000000000 * N ^ 18 +
          1000000000000000000000000000000000000 := by
    cases hN : N with
    | zero =>
        have hM : M ≤ 1000 := by
          simpa [hN] using hOccurrences
        have hPow : M ^ 6 ≤ 1000 ^ 6 :=
          Nat.pow_le_pow_left hM 6
        have hCoarse :
            10000000000 * M ^ 6 + 10000000000 ≤
              10000000000 * 1000 ^ 6 + 10000000000 := by
          exact Nat.add_le_add_right (Nat.mul_le_mul_left 10000000000 hPow) 10000000000
        have hBig :
            10000000000 * 1000 ^ 6 + 10000000000 ≤
              1000000000000000000000000000000000000 := by
          norm_num
        have hTargetZero :
            10000000000 * M ^ 6 + 10000000000 ≤
              1000000000000000000000000000000000000 * (0 : Nat) ^ 18 +
                1000000000000000000000000000000000000 := by
          simpa using hCoarse.trans hBig
        simpa [hN] using hTargetZero
    | succ n =>
        have hNpos : 1 ≤ Nat.succ n := by omega
        have hOccN : M ≤ 1000 * (Nat.succ n) ^ 3 + 1000 := by
          simpa [hN] using hOccurrences
        have hOccSmall : M ≤ 2000 * (Nat.succ n) ^ 3 := by
          have hPowGe : 1 ≤ (Nat.succ n) ^ 3 := by
            exact Nat.succ_le_of_lt (pow_pos (Nat.succ_pos n) 3)
          have hConst : 1000 ≤ 1000 * (Nat.succ n) ^ 3 := by
            calc
              1000 = 1000 * 1 := by omega
              _ ≤ 1000 * (Nat.succ n) ^ 3 :=
                Nat.mul_le_mul_left 1000 hPowGe
          calc
            M ≤ 1000 * (Nat.succ n) ^ 3 + 1000 := hOccN
            _ ≤ 1000 * (Nat.succ n) ^ 3 + 1000 * (Nat.succ n) ^ 3 := by
              exact Nat.add_le_add_left hConst (1000 * (Nat.succ n) ^ 3)
            _ = 2000 * (Nat.succ n) ^ 3 := by ring
        have hPow : M ^ 6 ≤ (2000 * (Nat.succ n) ^ 3) ^ 6 :=
          Nat.pow_le_pow_left hOccSmall 6
        have hCoarse :
            10000000000 * M ^ 6 + 10000000000 ≤
              10000000000 * (2000 * (Nat.succ n) ^ 3) ^ 6 + 10000000000 := by
          exact Nat.add_le_add_right (Nat.mul_le_mul_left 10000000000 hPow) 10000000000
        have hBig :
            10000000000 * (2000 * (Nat.succ n) ^ 3) ^ 6 + 10000000000 ≤
              1000000000000000000000000000000000000 * (Nat.succ n) ^ 18 +
                1000000000000000000000000000000000000 := by
          nlinarith [sq_nonneg ((Nat.succ n) : Int)]
        exact hCoarse.trans hBig
  simpa [cliqueCompatibilityEdgesFromThreeCNF, M, N] using hEdges.trans hTarget

theorem cliqueCompatibilityEdgesFromThreeCNF_polynomialSizeBound :
    PolynomialSizeBound
      (fun φ : SAT.ThreeCNF => threeCNFStructuredEncodedType.inputSize φ)
      (fun edges : List edgeStructuredEncodedType.Carrier =>
        edgeListStructuredEncodedType.inputSize edges)
      cliqueCompatibilityEdgesFromThreeCNF := by
  refine PolynomialSizeBound.intro_with 18
    1000000000000000000000000000000000000
    1000000000000000000000000000000000000 ?_
  intro φ
  exact cliqueCompatibilityEdgesFromThreeCNF_inputSize_le φ

theorem cliqueCompatibilityEdgesFromThreeCNF_tm_polytime :
    TMPolyTimeMap
      threeCNFStructuredEncodedType
      edgeListStructuredEncodedType
      cliqueCompatibilityEdgesFromThreeCNF := by
  have hComp :=
    TMPolyTimeMap.comp
      cliqueCompatibilityEdgesFromOccurrencesTMBackedMap.tm_polytime
      indexedLiteralOccurrencesTMBackedMap.tm_polytime
  simpa [Function.comp, cliqueCompatibilityEdgesFromThreeCNF] using hComp

noncomputable def cliqueCompatibilityEdgesFromThreeCNFTMBackedMap :
    TMBackedCostedMap
      threeCNFStructuredEncodedType
      edgeListStructuredEncodedType
      cliqueCompatibilityEdgesFromThreeCNF where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      cliqueCompatibilityEdgesFromThreeCNF_polynomialSizeBound
  tm_polytime := cliqueCompatibilityEdgesFromThreeCNF_tm_polytime

theorem mem_cliqueCompatibilityEdgesFromThreeCNF_iff
    (φ : SAT.ThreeCNF) (e : edgeStructuredEncodedType.Carrier) :
    List.Mem e (cliqueCompatibilityEdgesFromThreeCNF φ) ↔
      ∃ item, List.Mem item
          (cliqueCompatibilityItemsFromOccurrences (indexedLiteralOccurrences φ)) ∧
        ∃ prior, List.Mem prior
            (item.2 : List indexedLiteralOccurrenceEncodedType.Carrier) ∧
          occurrenceCompatible prior.2 item.1.2 ∧ e = (prior.1, item.1.1) := by
  simpa [cliqueCompatibilityEdgesFromThreeCNF, cliqueCompatibilityEdgesFromOccurrences] using
    mem_cliqueCompatibilityEdgesFromItems_iff
      (cliqueCompatibilityItemsFromOccurrences (indexedLiteralOccurrences φ)) e

def cliqueCompatibilityGraphFromThreeCNF (φ : SAT.ThreeCNF) : GraphInput where
  vertices := threeCNFLiteralOccurrenceCount φ
  edges := cliqueCompatibilityEdgesFromThreeCNF φ
  directed := false

theorem inputSize_le_pow18_add_one (n : Nat) :
    n ≤ n ^ 18 + 1 := by
  cases n with
  | zero =>
      norm_num
  | succ n =>
      have hPowGe : 1 ≤ (Nat.succ n) ^ 17 := by
        exact Nat.succ_le_of_lt (pow_pos (Nat.succ_pos n) 17)
      calc
        Nat.succ n = Nat.succ n * 1 := by omega
        _ ≤ Nat.succ n * (Nat.succ n) ^ 17 :=
          Nat.mul_le_mul_left (Nat.succ n) hPowGe
        _ = (Nat.succ n) ^ 18 := by ring
        _ ≤ (Nat.succ n) ^ 18 + 1 := by omega

theorem cliqueCompatibilityGraphFromThreeCNF_inputSize_le (φ : SAT.ThreeCNF) :
    graphStructuredEncodedType.inputSize (cliqueCompatibilityGraphFromThreeCNF φ) ≤
      1000000000000000000000000000000000010 *
          (threeCNFStructuredEncodedType.inputSize φ) ^ 18 +
        1000000000000000000000000000000000010 := by
  let N := threeCNFStructuredEncodedType.inputSize φ
  have hVertices :
      threeCNFLiteralOccurrenceCount φ ≤ N := by
    simpa [N] using threeCNFLiteralOccurrenceCount_le_inputSize φ
  have hEdges :
      edgeListStructuredEncodedType.inputSize (cliqueCompatibilityEdgesFromThreeCNF φ) ≤
        1000000000000000000000000000000000000 * N ^ 18 +
          1000000000000000000000000000000000000 := by
    simpa [N] using cliqueCompatibilityEdgesFromThreeCNF_inputSize_le φ
  have hNpow : N ≤ N ^ 18 + 1 := inputSize_le_pow18_add_one N
  rw [graphStructured_inputSize_eq]
  change
    threeCNFLiteralOccurrenceCount φ +
        edgeListStructuredEncodedType.inputSize (cliqueCompatibilityEdgesFromThreeCNF φ) + 4 ≤
      1000000000000000000000000000000000010 * N ^ 18 +
        1000000000000000000000000000000000010
  omega

theorem cliqueCompatibilityGraphFromThreeCNF_polynomialSizeBound :
    PolynomialSizeBound
      (fun φ : SAT.ThreeCNF => threeCNFStructuredEncodedType.inputSize φ)
      (fun g : GraphInput => graphStructuredEncodedType.inputSize g)
      cliqueCompatibilityGraphFromThreeCNF := by
  refine PolynomialSizeBound.intro_with 18
    1000000000000000000000000000000000010
    1000000000000000000000000000000000010 ?_
  intro φ
  exact cliqueCompatibilityGraphFromThreeCNF_inputSize_le φ

theorem cliqueCompatibilityGraphFromThreeCNF_tm_polytime :
    TMPolyTimeMap
      threeCNFStructuredEncodedType
      graphStructuredEncodedType
      cliqueCompatibilityGraphFromThreeCNF := by
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
        cliqueCompatibilityEdgesFromThreeCNF :=
    cliqueCompatibilityEdgesFromThreeCNFTMBackedMap.tm_polytime
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
        (fun φ : SAT.ThreeCNF => (cliqueCompatibilityEdgesFromThreeCNF φ, false)) :=
    TMPolyTimeMap.prod_mk hEdges hDirected
  have hTuple :
      TMPolyTimeMap
        threeCNFStructuredEncodedType
        graphTupleStructuredEncodedType
        (fun φ : SAT.ThreeCNF =>
          (threeCNFLiteralOccurrenceCount φ,
            (cliqueCompatibilityEdgesFromThreeCNF φ, false))) :=
    TMPolyTimeMap.prod_mk hVertices hPayload
  have hGraph :=
    TMPolyTimeMap.comp graphTupleToGraphTMBackedMap.tm_polytime hTuple
  simpa [Function.comp, graphTupleToGraph, cliqueCompatibilityGraphFromThreeCNF] using hGraph

noncomputable def cliqueCompatibilityGraphFromThreeCNFTMBackedMap :
    TMBackedCostedMap
      threeCNFStructuredEncodedType
      graphStructuredEncodedType
      cliqueCompatibilityGraphFromThreeCNF where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      cliqueCompatibilityGraphFromThreeCNF_polynomialSizeBound
  tm_polytime := cliqueCompatibilityGraphFromThreeCNF_tm_polytime

def threeSATToCliqueStructuredTMMap (φ : SAT.ThreeCNF) : CliqueInput where
  graph := cliqueCompatibilityGraphFromThreeCNF φ
  k := threeCNFClauseCount φ

theorem threeSATToCliqueStructuredTMMap_inputSize_le (φ : SAT.ThreeCNF) :
    cliqueStructuredEncodedType.inputSize (threeSATToCliqueStructuredTMMap φ) ≤
      1000000000000000000000000000000000020 *
          (threeCNFStructuredEncodedType.inputSize φ) ^ 18 +
        1000000000000000000000000000000000020 := by
  let N := threeCNFStructuredEncodedType.inputSize φ
  have hGraph := cliqueCompatibilityGraphFromThreeCNF_inputSize_le φ
  have hGraphN :
      graphStructuredEncodedType.inputSize (cliqueCompatibilityGraphFromThreeCNF φ) ≤
        1000000000000000000000000000000000010 * N ^ 18 +
          1000000000000000000000000000000000010 := by
    simpa [N] using hGraph
  have hK : threeCNFClauseCount φ ≤ N := by
    simpa [N] using threeCNFClauseCount_le_inputSize φ
  have hNpow : N ≤ N ^ 18 + 1 := inputSize_le_pow18_add_one N
  rw [cliqueStructured_inputSize_eq]
  change
    graphStructuredEncodedType.inputSize (cliqueCompatibilityGraphFromThreeCNF φ) +
        threeCNFClauseCount φ + 2 ≤
      1000000000000000000000000000000000020 * N ^ 18 +
        1000000000000000000000000000000000020
  omega

theorem threeSATToCliqueStructuredTMMap_polynomialSizeBound :
    PolynomialSizeBound
      (fun φ : SAT.ThreeCNF => threeCNFStructuredEncodedType.inputSize φ)
      (fun I : CliqueInput => cliqueStructuredEncodedType.inputSize I)
      threeSATToCliqueStructuredTMMap := by
  refine PolynomialSizeBound.intro_with 18
    1000000000000000000000000000000000020
    1000000000000000000000000000000000020 ?_
  intro φ
  exact threeSATToCliqueStructuredTMMap_inputSize_le φ

theorem threeSATToCliqueStructuredTMMap_tm_polytime :
    TMPolyTimeMap
      threeCNFStructuredEncodedType
      cliqueStructuredEncodedType
      threeSATToCliqueStructuredTMMap := by
  have hGraph :=
    cliqueCompatibilityGraphFromThreeCNFTMBackedMap.tm_polytime
  have hK :
      TMPolyTimeMap
        threeCNFStructuredEncodedType
        EncodedType.nat
        threeCNFClauseCount :=
    threeCNFClauseCountTMBackedMap.tm_polytime
  have hTuple :
      TMPolyTimeMap
        threeCNFStructuredEncodedType
        cliqueTupleStructuredEncodedType
        (fun φ : SAT.ThreeCNF =>
          (cliqueCompatibilityGraphFromThreeCNF φ, threeCNFClauseCount φ)) :=
    TMPolyTimeMap.prod_mk hGraph hK
  have hClique :=
    TMPolyTimeMap.comp cliqueTupleToCliqueInputTMBackedMap.tm_polytime hTuple
  simpa [Function.comp, cliqueTupleToCliqueInput, threeSATToCliqueStructuredTMMap] using hClique

noncomputable def threeSATToCliqueStructuredTMBackedMap :
    TMBackedCostedMap
      threeCNFStructuredEncodedType
      cliqueStructuredEncodedType
      threeSATToCliqueStructuredTMMap where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      threeSATToCliqueStructuredTMMap_polynomialSizeBound
  tm_polytime := threeSATToCliqueStructuredTMMap_tm_polytime

/-! #### Semantic alignment with the P15s textbook Clique route -/

theorem threeCNFLiteralOccurrenceCount_eq_literalOccurrences_length (φ : SAT.ThreeCNF) :
    threeCNFLiteralOccurrenceCount φ = (literalOccurrences φ).length := by
  simpa [threeCNFLiteralOccurrenceCount] using
    (literalOccurrences_length_eq_totalClauseLength φ).symm

theorem mem_indexedLiteralOccurrencesFrom_getElem?
    (next : Nat) (xs : List LiteralOccurrence) {idx : Nat} {occ : LiteralOccurrence}
    (h : (idx, occ) ∈ indexedLiteralOccurrencesFrom next xs) :
    next ≤ idx ∧ xs[idx - next]? = some occ := by
  induction xs generalizing next idx with
  | nil =>
      change (idx, occ) ∈ ([] : List indexedLiteralOccurrenceEncodedType.Carrier) at h
      cases h
  | cons head tail ih =>
      change (idx, occ) ∈
        (next, head) :: indexedLiteralOccurrencesFrom (next + 1) tail at h
      cases h with
      | head =>
          simp
      | tail _ hTail =>
        have hTailInfo := ih (next + 1) hTail
        constructor
        · omega
        · have hIdx : idx - next = Nat.succ (idx - (next + 1)) := by
            omega
          rw [hIdx]
          simpa using hTailInfo.2

theorem mem_indexedLiteralOccurrences_occurrenceAt?
    {φ : SAT.ThreeCNF} {idx : Nat} {occ : LiteralOccurrence}
    (h : (idx, occ) ∈ indexedLiteralOccurrences φ) :
    occurrenceAt? φ idx = some occ := by
  have hInfo := mem_indexedLiteralOccurrencesFrom_getElem?
    0 (literalOccurrences φ) (idx := idx) (occ := occ) (by
      simpa [indexedLiteralOccurrences] using h)
  simpa [occurrenceAt?] using hInfo.2

theorem getElem?_mem_indexedLiteralOccurrencesFrom
    (next : Nat) (xs : List LiteralOccurrence) {idx : Nat} {occ : LiteralOccurrence}
    (h : xs[idx]? = some occ) :
    (next + idx, occ) ∈ indexedLiteralOccurrencesFrom next xs := by
  induction xs generalizing next idx with
  | nil =>
      simp at h
  | cons head tail ih =>
      cases idx with
      | zero =>
          simp [indexedLiteralOccurrencesFrom] at h ⊢
          subst occ
          exact List.Mem.head _
      | succ idx =>
          have hTail : tail[idx]? = some occ := by
            simpa using h
          have hMem := ih (next + 1) hTail
          have hIdx : next + Nat.succ idx = (next + 1) + idx := by omega
          change (next + Nat.succ idx, occ) ∈
            (next, head) :: indexedLiteralOccurrencesFrom (next + 1) tail
          right
          simpa [hIdx] using hMem

theorem occurrenceAt?_some_mem_indexedLiteralOccurrences
    {φ : SAT.ThreeCNF} {idx : Nat} {occ : LiteralOccurrence}
    (h : occurrenceAt? φ idx = some occ) :
    (idx, occ) ∈ indexedLiteralOccurrences φ := by
  have hGet : (literalOccurrences φ)[idx]? = some occ := by
    simpa [occurrenceAt?] using h
  have hMem := getElem?_mem_indexedLiteralOccurrencesFrom
    0 (literalOccurrences φ) (idx := idx) hGet
  simpa [indexedLiteralOccurrences] using hMem

def cliqueCompatibilityItemsFromPrior
    (prior : List indexedLiteralOccurrenceEncodedType.Carrier) :
    List indexedLiteralOccurrenceEncodedType.Carrier →
      List cliqueCompatibilityEdgeItemEncodedType.Carrier
  | [] => []
  | current :: rest =>
      (current, prior) :: cliqueCompatibilityItemsFromPrior (prior ++ [current]) rest

theorem cliqueCompatibilityItemBuilder_fold_eq
    (items : List cliqueCompatibilityEdgeItemEncodedType.Carrier)
    (prior xs : List indexedLiteralOccurrenceEncodedType.Carrier) :
    (xs.foldl
        (fun acc current => cliqueCompatibilityItemBuilderStep (acc, current))
        (items, prior)).1 =
      items ++ cliqueCompatibilityItemsFromPrior prior xs ∧
    (xs.foldl
        (fun acc current => cliqueCompatibilityItemBuilderStep (acc, current))
        (items, prior)).2 = prior ++ xs := by
  induction xs generalizing items prior with
  | nil =>
      simp [cliqueCompatibilityItemsFromPrior]
  | cons current rest ih =>
      have hTail := ih
        (items ++ ([(current, prior)] : List cliqueCompatibilityEdgeItemEncodedType.Carrier))
        (prior ++ [current])
      constructor
      · simpa [cliqueCompatibilityItemBuilderStep, cliqueCompatibilityItemsFromPrior,
          List.append_assoc] using hTail.1
      · simpa [cliqueCompatibilityItemBuilderStep, List.append_assoc] using hTail.2

theorem cliqueCompatibilityItemsFromOccurrences_eq
    (xs : List indexedLiteralOccurrenceEncodedType.Carrier) :
    cliqueCompatibilityItemsFromOccurrences xs =
      cliqueCompatibilityItemsFromPrior [] xs := by
  have h := (cliqueCompatibilityItemBuilder_fold_eq
    ([] : List cliqueCompatibilityEdgeItemEncodedType.Carrier)
    ([] : List indexedLiteralOccurrenceEncodedType.Carrier) xs).1
  simpa [cliqueCompatibilityItemsFromOccurrences] using h

theorem mem_cliqueCompatibilityItemsFromPrior_iff
    (prior xs : List indexedLiteralOccurrenceEncodedType.Carrier)
    (item : cliqueCompatibilityEdgeItemEncodedType.Carrier) :
    item ∈ cliqueCompatibilityItemsFromPrior prior xs ↔
      ∃ pref suffix,
        xs = pref ++ item.1 :: suffix ∧ item.2 = prior ++ pref := by
  induction xs generalizing prior with
  | nil =>
      simp [cliqueCompatibilityItemsFromPrior]
  | cons current rest ih =>
      constructor
      · intro h
        simp [cliqueCompatibilityItemsFromPrior] at h
        rcases h with hHead | hTail
        · subst item
          refine ⟨[], rest, by simp, by simp⟩
        · rcases (ih (prior ++ [current])).1 hTail with
            ⟨pref, suffix, hRest, hPrior⟩
          refine ⟨current :: pref, suffix, ?_, ?_⟩
          · simp [hRest]
          · simp [hPrior, List.append_assoc]
      · intro h
        rcases h with ⟨pref, suffix, hxs, hPrior⟩
        cases pref with
        | nil =>
            simp [cliqueCompatibilityItemsFromPrior]
            left
            rcases item with ⟨itemCurrent, itemPrior⟩
            simp at hxs hPrior ⊢
            rcases hxs with ⟨hCurrent, _hRest⟩
            subst itemCurrent
            subst itemPrior
            rfl
        | cons first pref =>
            simp at hxs
            rcases hxs with ⟨hFirst, hRest⟩
            simp [cliqueCompatibilityItemsFromPrior]
            right
            exact (ih (prior ++ [current])).2
              ⟨pref, suffix, hRest, by simp [hFirst, hPrior, List.append_assoc]⟩

theorem mem_cliqueCompatibilityItemsFromOccurrences_iff
    (xs : List indexedLiteralOccurrenceEncodedType.Carrier)
    (item : cliqueCompatibilityEdgeItemEncodedType.Carrier) :
    item ∈ cliqueCompatibilityItemsFromOccurrences xs ↔
      ∃ pref suffix, xs = pref ++ item.1 :: suffix ∧ item.2 = pref := by
  rw [cliqueCompatibilityItemsFromOccurrences_eq]
  simpa using mem_cliqueCompatibilityItemsFromPrior_iff
    ([] : List indexedLiteralOccurrenceEncodedType.Carrier) xs item

theorem mem_cliqueCompatibilityEdgesFromOccurrences_prefix_iff
    (xs : List indexedLiteralOccurrenceEncodedType.Carrier)
    (e : edgeStructuredEncodedType.Carrier) :
    e ∈ cliqueCompatibilityEdgesFromOccurrences xs ↔
      ∃ pref current suffix prior,
        xs = pref ++ current :: suffix ∧ prior ∈ pref ∧
          occurrenceCompatible prior.2 current.2 ∧ e = (prior.1, current.1) := by
  constructor
  · intro he
    rcases (mem_cliqueCompatibilityEdgesFromItems_iff
        (cliqueCompatibilityItemsFromOccurrences xs) e).1
        (by simpa [cliqueCompatibilityEdgesFromOccurrences] using he) with
      ⟨item, hitem, prior, hprior, hCompat, hEq⟩
    rcases (mem_cliqueCompatibilityItemsFromOccurrences_iff xs item).1 hitem with
      ⟨pref, suffix, hxs, hItemPrior⟩
    exact ⟨pref, item.1, suffix, prior, hxs, by simpa [hItemPrior] using hprior,
      hCompat, hEq⟩
  · intro h
    rcases h with ⟨pref, current, suffix, prior, hxs, hprior, hCompat, hEq⟩
    have hitem :
        ((current, pref) : cliqueCompatibilityEdgeItemEncodedType.Carrier) ∈
          cliqueCompatibilityItemsFromOccurrences xs :=
      (mem_cliqueCompatibilityItemsFromOccurrences_iff xs
        ((current, pref) : cliqueCompatibilityEdgeItemEncodedType.Carrier)).2
        ⟨pref, suffix, by simpa using hxs, by simp⟩
    have hEdges :=
      (mem_cliqueCompatibilityEdgesFromItems_iff
        (cliqueCompatibilityItemsFromOccurrences xs) e).2
        ⟨(current, pref), hitem, prior, hprior, hCompat, hEq⟩
    simpa [cliqueCompatibilityEdgesFromOccurrences] using hEdges

theorem mem_cliqueCompatibilityEdgesFromOccurrences_cons_of_tail
    (head : indexedLiteralOccurrenceEncodedType.Carrier)
    {tail : List indexedLiteralOccurrenceEncodedType.Carrier}
    {e : edgeStructuredEncodedType.Carrier}
    (he : e ∈ cliqueCompatibilityEdgesFromOccurrences tail) :
    e ∈ cliqueCompatibilityEdgesFromOccurrences (head :: tail) := by
  rcases (mem_cliqueCompatibilityEdgesFromOccurrences_prefix_iff tail e).1 he with
    ⟨pref, current, suffix, prior, htail, hprior, hCompat, hEq⟩
  rw [mem_cliqueCompatibilityEdgesFromOccurrences_prefix_iff]
  refine ⟨head :: pref, current, suffix, prior, ?_, ?_, hCompat, hEq⟩
  · simp [htail]
  · simp [hprior]

theorem hasUndirectedEdge_cliqueCompatibilityEdgesFromOccurrences_of_mem
    {xs : List indexedLiteralOccurrenceEncodedType.Carrier}
    {x y : indexedLiteralOccurrenceEncodedType.Carrier}
    (hx : x ∈ xs) (hy : y ∈ xs) (hxy : x.1 ≠ y.1)
    (hCompat : occurrenceCompatible x.2 y.2) :
    (x.1, y.1) ∈ cliqueCompatibilityEdgesFromOccurrences xs ∨
      (y.1, x.1) ∈ cliqueCompatibilityEdgesFromOccurrences xs := by
  induction xs with
  | nil =>
      simp at hx
  | cons head tail ih =>
      simp at hx hy
      rcases hx with rfl | hxTail
      · rcases hy with rfl | hyTail
        · exact (hxy rfl).elim
        · rcases List.mem_iff_append.mp hyTail with ⟨pref, suffix, htail⟩
          left
          exact (mem_cliqueCompatibilityEdgesFromOccurrences_prefix_iff
            (x :: tail) ((x.1, y.1) : edgeStructuredEncodedType.Carrier)).2
            ⟨x :: pref, y, suffix, x, by simp [htail], by simp, hCompat, rfl⟩
      · rcases hy with rfl | hyTail
        · rcases List.mem_iff_append.mp hxTail with ⟨pref, suffix, htail⟩
          right
          exact (mem_cliqueCompatibilityEdgesFromOccurrences_prefix_iff
            (y :: tail) ((y.1, x.1) : edgeStructuredEncodedType.Carrier)).2
            ⟨y :: pref, x, suffix, y, by simp [htail], by simp,
              occurrenceCompatible_symm hCompat, rfl⟩
        · rcases ih hxTail hyTail with hEdge | hEdge
          · exact Or.inl (mem_cliqueCompatibilityEdgesFromOccurrences_cons_of_tail head hEdge)
          · exact Or.inr (mem_cliqueCompatibilityEdgesFromOccurrences_cons_of_tail head hEdge)

theorem mem_textbookEdgeList_of_mem_cliqueCompatibilityEdgesFromThreeCNF
    {φ : SAT.ThreeCNF} {e : edgeStructuredEncodedType.Carrier}
    (he : e ∈ cliqueCompatibilityEdgesFromThreeCNF φ) :
    e ∈ textbookEdgeList φ := by
  rcases e with ⟨u, v⟩
  change Nat at u
  change Nat at v
  rcases (mem_cliqueCompatibilityEdgesFromOccurrences_prefix_iff
      (indexedLiteralOccurrences φ) (u, v)).1
      (by simpa [cliqueCompatibilityEdgesFromThreeCNF] using he) with
    ⟨pref, current, suffix, prior, hxs, hprior, hCompat, hEq⟩
  rcases prior with ⟨priorIdx, priorOcc⟩
  rcases current with ⟨currentIdx, currentOcc⟩
  change Nat at priorIdx
  change Nat at currentIdx
  injection hEq with hPriorIdx hCurrentIdx
  simp at hPriorIdx hCurrentIdx hCompat
  subst u
  subst v
  have hPriorMem : (priorIdx, priorOcc) ∈ indexedLiteralOccurrences φ := by
    rw [hxs]
    exact List.mem_append.mpr (Or.inl hprior)
  have hCurrentMem : (currentIdx, currentOcc) ∈ indexedLiteralOccurrences φ := by
    rw [hxs]
    exact List.mem_append.mpr (Or.inr (List.Mem.head _))
  have hPriorOcc := mem_indexedLiteralOccurrences_occurrenceAt? hPriorMem
  have hCurrentOcc := mem_indexedLiteralOccurrences_occurrenceAt? hCurrentMem
  have hPriorBound : priorIdx < (literalOccurrences φ).length := by
    rw [occurrenceAt?] at hPriorOcc
    exact (List.getElem?_eq_some_iff.mp hPriorOcc).1
  have hCurrentBound : currentIdx < (literalOccurrences φ).length := by
    rw [occurrenceAt?] at hCurrentOcc
    exact (List.getElem?_eq_some_iff.mp hCurrentOcc).1
  exact (mem_textbookEdgeList_iff φ (priorIdx, currentIdx)).2
    ⟨hPriorBound, hCurrentBound,
      ⟨priorOcc, by simpa using hPriorOcc, currentOcc, by simpa using hCurrentOcc, hCompat⟩⟩

theorem hasUndirectedEdge_textbook_of_cliqueCompatibilityGraphFromThreeCNF
    (φ : SAT.ThreeCNF) (u v : Nat)
    (hEdge : HasUndirectedEdge (cliqueCompatibilityGraphFromThreeCNF φ) u v) :
    HasUndirectedEdge (textbookMap φ).graph u v := by
  rcases hEdge with hEdge | hEdge
  · exact Or.inl (mem_textbookEdgeList_of_mem_cliqueCompatibilityEdgesFromThreeCNF hEdge)
  · exact Or.inr (mem_textbookEdgeList_of_mem_cliqueCompatibilityEdgesFromThreeCNF hEdge)

theorem hasUndirectedEdge_cliqueCompatibilityGraphFromThreeCNF_of_textbookEdgeList
    {φ : SAT.ThreeCNF} {u v : Nat}
    (he : (u, v) ∈ textbookEdgeList φ) :
    HasUndirectedEdge (cliqueCompatibilityGraphFromThreeCNF φ) u v := by
  have hInfo := (mem_textbookEdgeList_iff φ (u, v)).1 he
  rcases hInfo.2.2 with ⟨uOcc, huOcc, vOcc, hvOcc, hCompat⟩
  have huOccEq : occurrenceAt? φ u = some uOcc := by simpa using huOcc
  have hvOccEq : occurrenceAt? φ v = some vOcc := by simpa using hvOcc
  have huMem := occurrenceAt?_some_mem_indexedLiteralOccurrences huOccEq
  have hvMem := occurrenceAt?_some_mem_indexedLiteralOccurrences hvOccEq
  have huv : u ≠ v := by
    intro huv
    subst v
    rw [huOccEq] at hvOccEq
    injection hvOccEq with hOcc
    subst vOcc
    exact hCompat.1 rfl
  have hEdges :=
    hasUndirectedEdge_cliqueCompatibilityEdgesFromOccurrences_of_mem
      (xs := indexedLiteralOccurrences φ)
      (x := (u, uOcc)) (y := (v, vOcc)) huMem hvMem huv hCompat
  simpa [cliqueCompatibilityGraphFromThreeCNF, cliqueCompatibilityEdgesFromThreeCNF,
    HasUndirectedEdge] using hEdges

theorem hasUndirectedEdge_cliqueCompatibilityGraphFromThreeCNF_iff
    (φ : SAT.ThreeCNF) (u v : Nat) :
    HasUndirectedEdge (cliqueCompatibilityGraphFromThreeCNF φ) u v ↔
      HasUndirectedEdge (textbookMap φ).graph u v := by
  constructor
  · exact hasUndirectedEdge_textbook_of_cliqueCompatibilityGraphFromThreeCNF φ u v
  · intro hEdge
    rcases hEdge with hEdge | hEdge
    · exact hasUndirectedEdge_cliqueCompatibilityGraphFromThreeCNF_of_textbookEdgeList hEdge
    · rcases hasUndirectedEdge_cliqueCompatibilityGraphFromThreeCNF_of_textbookEdgeList
          (φ := φ) (u := v) (v := u) hEdge with hForward | hBackward
      · exact Or.inr hForward
      · exact Or.inl hBackward

theorem clique_threeSATToCliqueStructuredTMMap_iff_textbookMap (φ : SAT.ThreeCNF) :
    Clique (threeSATToCliqueStructuredTMMap φ) ↔ Clique (textbookMap φ) := by
  have hVertices := threeCNFLiteralOccurrenceCount_eq_literalOccurrences_length φ
  constructor
  · intro hClique
    rcases hClique with ⟨vs, hLen, hNodup, hBounds, hAdj⟩
    refine ⟨vs, ?_, hNodup, ?_, ?_⟩
    · simpa [threeSATToCliqueStructuredTMMap, threeCNFClauseCount, textbookMap] using hLen
    · intro v hv
      have hvBound := hBounds v hv
      simpa [threeSATToCliqueStructuredTMMap, cliqueCompatibilityGraphFromThreeCNF,
        textbookMap, hVertices] using hvBound
    · intro u hu v hv huv
      exact (hasUndirectedEdge_cliqueCompatibilityGraphFromThreeCNF_iff φ u v).1
        (hAdj u hu v hv huv)
  · intro hClique
    rcases hClique with ⟨vs, hLen, hNodup, hBounds, hAdj⟩
    refine ⟨vs, ?_, hNodup, ?_, ?_⟩
    · simpa [threeSATToCliqueStructuredTMMap, threeCNFClauseCount, textbookMap] using hLen
    · intro v hv
      have hvBound := hBounds v hv
      simpa [threeSATToCliqueStructuredTMMap, cliqueCompatibilityGraphFromThreeCNF,
        textbookMap, hVertices] using hvBound
    · intro u hu v hv huv
      exact (hasUndirectedEdge_cliqueCompatibilityGraphFromThreeCNF_iff φ u v).2
        (hAdj u hu v hv huv)

theorem threeSATToCliqueStructuredTMMap_correct (φ : SAT.ThreeCNF) :
    SAT.threeSATDecisionProblem.isYes φ ↔ Clique (threeSATToCliqueStructuredTMMap φ) :=
  (textbookMap_correct φ).trans
    (clique_threeSATToCliqueStructuredTMMap_iff_textbookMap φ).symm

noncomputable def threeSATToCliqueStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      threeSATStructuredDecisionProblem cliqueStructuredDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    threeSATToCliqueStructuredTMBackedMap
    (by
      intro φ
      simpa [threeSATStructuredDecisionProblem, cliqueStructuredDecisionProblem]
        using threeSATToCliqueStructuredTMMap_correct φ)

/--
Public structured 3SAT-to-Clique reduction, now projected from the direct
TM-backed witness rather than the older costed-only transport.
-/
noncomputable def threeSATToCliqueStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      threeSATStructuredDecisionProblem cliqueStructuredDecisionProblem :=
  threeSATToCliqueStructuredTMBackedKarpReduction.toCostedKarpReduction

/-- Direct TM-facing projection of the faithful structured 3SAT-to-Clique route. -/
noncomputable def threeSATToCliqueStructuredTMKarpReduction :
    TMKarpReduction threeSATStructuredDecisionProblem cliqueStructuredDecisionProblem :=
  threeSATToCliqueStructuredTMBackedKarpReduction.toTMKarpReduction

/--
Proof-carrying structured SAT-to-Clique chain: first split a faithful CNF SAT
instance into bundled 3CNF, then apply the direct clause-literal Clique gadget.
-/
noncomputable def satisfiabilityToCliqueStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      satisfiabilityStructuredDecisionProblem cliqueStructuredDecisionProblem :=
  TMBackedCostedReduction.comp
    threeSATToCliqueStructuredTMBackedKarpReduction
    cnfSATToThreeSATStructuredTMBackedKarpReduction

/--
Public structured SAT-to-Clique reduction projected from the proof-carrying
TM-backed chain.  The direct source edge remains
`threeSATToCliqueStructuredKarpReduction`.
-/
noncomputable def satisfiabilityToCliqueStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      satisfiabilityStructuredDecisionProblem cliqueStructuredDecisionProblem :=
  satisfiabilityToCliqueStructuredTMBackedKarpReduction.toCostedKarpReduction

/-- Direct TM-facing projection of the faithful structured SAT-to-Clique chain. -/
noncomputable def satisfiabilityToCliqueStructuredTMKarpReduction :
    TMKarpReduction satisfiabilityStructuredDecisionProblem cliqueStructuredDecisionProblem :=
  satisfiabilityToCliqueStructuredTMBackedKarpReduction.toTMKarpReduction

end Clique
end Karp21
end ComplexityReduction
