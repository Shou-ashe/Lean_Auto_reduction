import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SteinerTree.Part1

namespace ComplexityReduction
namespace Karp21
namespace SteinerTree
open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

theorem digitCountsFrom_sum_ge_len_succ_of_covers_and_two {sets : List (List Nat)}
    {start len x : Nat}
    (hCovers :
      ∀ y, start ≤ y → y < start + len → ∃ S ∈ sets, y ∈ S)
    (hLo : start ≤ x) (hHi : x < start + len)
    (hTwo : 2 ≤ Knapsack.elementCount x sets) :
    len + 1 ≤ (Knapsack.digitCountsFrom start len sets).sum := by
  induction len generalizing start with
  | zero =>
      omega
  | succ len ih =>
      by_cases hxStart : x = start
      · subst x
        have hTailCover :
            ∀ y, start + 1 ≤ y → y < start + 1 + len → ∃ S ∈ sets, y ∈ S := by
          intro y hLoY hHiY
          exact hCovers y (by omega) (by omega)
        have hTail := digitCountsFrom_sum_ge_len_of_covers hTailCover
        simp [Knapsack.digitCountsFrom]
        omega
      · have hHeadCover : ∃ S ∈ sets, start ∈ S := hCovers start (by omega) (by omega)
        rcases hHeadCover with ⟨S, hS, hxS⟩
        have hHeadPos : 0 < Knapsack.elementCount start sets :=
          Knapsack.elementCount_pos_of_mem hS hxS
        have hTailCover :
            ∀ y, start + 1 ≤ y → y < start + 1 + len → ∃ S ∈ sets, y ∈ S := by
          intro y hLoY hHiY
          exact hCovers y (by omega) (by omega)
        have hTail := ih hTailCover (by omega) (by omega)
        simp [Knapsack.digitCountsFrom]
        omega

theorem compactDecodedSets_elementCount_eq_one_of_cover_supportSum_le {I : ExactCoverInput}
    {selected : List (Nat × Nat × Nat)}
    (hCovers : CoversUniverse I.system (compactDecodedSets I selected))
    (hSupportBound :
      ((compactDecodedSets I selected).map fun S => (compactSupport I S).length).sum ≤
        I.system.universeSize)
    {x : Nat} (hx : x < I.system.universeSize) :
    Knapsack.elementCount x (compactDecodedSets I selected) = 1 := by
  have hCoverRange :
      ∀ y, 0 ≤ y → y < 0 + I.system.universeSize →
        ∃ S ∈ compactDecodedSets I selected, y ∈ S := by
    intro y _hyLo hyHi
    exact hCovers y (by omega)
  rcases hCovers x hx with ⟨S, hS, hxS⟩
  have hCountPos : 0 < Knapsack.elementCount x (compactDecodedSets I selected) :=
    Knapsack.elementCount_pos_of_mem hS hxS
  have hDigitSumLe :
      (Knapsack.digitCountsFrom 0 I.system.universeSize
          (compactDecodedSets I selected)).sum ≤ I.system.universeSize := by
    rw [← compactSupport_lengths_sum_eq_digitCountsFrom_sum]
    exact hSupportBound
  have hNotTwo : ¬ 2 ≤ Knapsack.elementCount x (compactDecodedSets I selected) := by
    intro hTwo
    have hLower :=
      digitCountsFrom_sum_ge_len_succ_of_covers_and_two
        (sets := compactDecodedSets I selected) hCoverRange (by omega) (by omega) hTwo
    omega
  omega

theorem compactDecodedSets_pairwiseDisjoint_of_cover_supportSum_le {I : ExactCoverInput}
    {selected : List (Nat × Nat × Nat)}
    (hWellFormed : SetSystemWellFormed I.system)
    (hCovers : CoversUniverse I.system (compactDecodedSets I selected))
    (hSupportBound :
      ((compactDecodedSets I selected).map fun S => (compactSupport I S).length).sum ≤
        I.system.universeSize) :
    PairwiseDisjointFamily (compactDecodedSets I selected) := by
  intro A hA B hB hNe x hxA hxB
  have hxUniverse : x < I.system.universeSize :=
    hWellFormed A (compactDecodedSets_family (I := I) (selected := selected) A hA) x hxA
  have hCount :=
    compactDecodedSets_elementCount_eq_one_of_cover_supportSum_le
      (I := I) (selected := selected) hCovers hSupportBound hxUniverse
  have hTwo :=
    Knapsack.elementCount_ge_two_of_pair
      (x := x) (sets := compactDecodedSets I selected)
      (A := A) (B := B) hA hB hNe hxA hxB
  omega

theorem exactCover_of_compactMapCore_steinerTree {I : ExactCoverInput}
    (hWellFormed : SetSystemWellFormed I.system)
    (hTree : SteinerTree (compactMapCore I)) :
    ExactCover I := by
  rcases hTree with ⟨selected, hFamily, hContains, hWeight⟩
  have hSubgraph : ∀ e ∈ selected, e ∈ compactEdges I := by
    intro e he
    simpa [compactMapCore, WeightedEdgeInGraph] using hFamily e he
  have hContainsCompact : ContainsTerminals selected (compactTerminals I) true := by
    simpa [compactMapCore] using hContains
  have hCovers : CoversUniverse I.system (compactDecodedSets I selected) :=
    compactDecodedSets_cover_of_contains
      (I := I) (selected := selected) hSubgraph hContainsCompact
  have hSupportBound :
      ((compactDecodedSets I selected).map fun S => (compactSupport I S).length).sum ≤
        I.system.universeSize := by
    exact (compactDecodedSupportSum_le_weight I selected).trans
      (by simpa [compactMapCore] using hWeight)
  have hDisjoint :
      PairwiseDisjointFamily (compactDecodedSets I selected) :=
    compactDecodedSets_pairwiseDisjoint_of_cover_supportSum_le
      (I := I) (selected := selected) hWellFormed hCovers hSupportBound
  refine ⟨hWellFormed, compactDecodedSets I selected, ?_, ?_, ?_, ?_⟩
  · exact compactDecodedSets_family (I := I) (selected := selected)
  · exact compactDecodedSets_nodup I selected
  · exact hDisjoint
  · exact hCovers

theorem compactMapCore_correct (I : ExactCoverInput)
    (hWellFormed : SetSystemWellFormed I.system) :
    ExactCover I ↔ SteinerTree (compactMapCore I) := by
  constructor
  · exact compactMapCore_steinerTree_of_exact
  · exact exactCover_of_compactMapCore_steinerTree (I := I) hWellFormed

theorem compactMap_correct (I : ExactCoverInput) :
    exactCoverDecisionProblem.isYes I ↔ SteinerTree (compactMap I) := by
  change ExactCover I ↔ SteinerTree (compactMap I)
  constructor
  · exact compactMap_steinerTree_of_exact
  · intro hTree
    by_cases hWellFormed : SetSystemWellFormed I.system
    · have hCore : SteinerTree (compactMapCore I) := by
        simpa [compactMap, hWellFormed] using hTree
      exact exactCover_of_compactMapCore_steinerTree (I := I) hWellFormed hCore
    · have hNo : SteinerTree noInput := by
        simpa [compactMap, hWellFormed] using hTree
      exact (noInput_isNo hNo).elim

theorem steinerTreeStructured_inputSize_eq (I : SteinerTreeInput) :
    steinerTreeStructuredEncodedType.inputSize I =
      weightedGraphStructuredEncodedType.inputSize I.graph + 1 +
        ((EncodedType.list EncodedType.nat).inputSize I.terminals + 1 +
          EncodedType.nat.inputSize I.weightBound) := by
  cases I with
  | mk graph terminals weightBound =>
      change steinerTreeTupleStructuredEncodedType.inputSize
          (graph, (terminals, weightBound)) =
        weightedGraphStructuredEncodedType.inputSize graph + 1 +
          ((EncodedType.list EncodedType.nat).inputSize terminals + 1 +
            EncodedType.nat.inputSize weightBound)
      simp [steinerTreeTupleStructuredEncodedType]

theorem weightedGraphStructured_inputSize_eq (g : WeightedGraphInput) :
    weightedGraphStructuredEncodedType.inputSize g =
      EncodedType.nat.inputSize g.vertices + 1 +
        (weightedEdgeListStructuredEncodedType.inputSize g.edges + 1 +
          EncodedType.bool.inputSize g.directed) := by
  cases g with
  | mk vertices edges directed =>
      change weightedGraphTupleStructuredEncodedType.inputSize
          (vertices, (edges, directed)) =
        EncodedType.nat.inputSize vertices + 1 +
          (weightedEdgeListStructuredEncodedType.inputSize edges + 1 +
            EncodedType.bool.inputSize directed)
      simp [weightedGraphTupleStructuredEncodedType, weightedGraphPayloadStructuredEncodedType]

theorem compactFlatMap_length_le_mul {α β : Type*} (xs : List α) (f : α → List β)
    (B : Nat) (hB : ∀ x ∈ xs, (f x).length ≤ B) :
    (xs.flatMap f).length ≤ xs.length * B := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : (f x).length ≤ B := hB x (by simp)
      have hTail : ∀ y ∈ xs, (f y).length ≤ B := by
        intro y hy
        exact hB y (by simp [hy])
      have ih' := ih hTail
      have hLen :
          ((x :: xs).flatMap f).length = (f x).length + (xs.flatMap f).length := by
        simp
      rw [hLen]
      calc
        (f x).length + (xs.flatMap f).length ≤ B + xs.length * B := by
          omega
        _ = (x :: xs).length * B := by
          simp [Nat.succ_mul, Nat.add_comm]

theorem compactEdgesForSet_length_le_universe_succ (I : ExactCoverInput) (j : Nat) :
    (compactEdgesForSet I j).length ≤ I.system.universeSize + 1 := by
  have hSupport := compactSupport_length_le_universe I (compactSourceSetAt I j)
  simp [compactEdgesForSet]
  omega

theorem compactEdges_length_le_source_poly_succ (I : ExactCoverInput) :
    (compactEdges I).length ≤ (exactCoverStructuredEncodedType.inputSize I + 1) ^ 2 := by
  let S := exactCoverStructuredEncodedType.inputSize I
  have hSets : I.system.sets.length ≤ S :=
    Knapsack.exactCover_sets_length_le_structured_inputSize I
  have hUniverse : I.system.universeSize ≤ S :=
    Knapsack.exactCover_universeSize_le_structured_inputSize I
  have hFlat :
      ((List.range I.system.sets.length).flatMap (compactEdgesForSet I)).length ≤
        I.system.sets.length * (I.system.universeSize + 1) := by
    simpa using compactFlatMap_length_le_mul (List.range I.system.sets.length)
      (compactEdgesForSet I) (I.system.universeSize + 1) (by
        intro j _hj
        exact compactEdgesForSet_length_le_universe_succ I j)
  have hMul :
      I.system.sets.length * (I.system.universeSize + 1) ≤ S * (S + 1) := by
    exact Nat.mul_le_mul hSets (Nat.add_le_add_right hUniverse 1)
  calc
    (compactEdges I).length =
        1 + ((List.range I.system.sets.length).flatMap (compactEdgesForSet I)).length := by
          simp [compactEdges, Nat.add_comm]
    _ ≤ 1 + I.system.sets.length * (I.system.universeSize + 1) := by
          omega
    _ ≤ 1 + S * (S + 1) := by
          omega
    _ ≤ (S + 1) ^ 2 := by
          nlinarith

theorem weightedEdgeStructured_inputSize_le_of_mem_compactEdges {I : ExactCoverInput}
    {e : Nat × Nat × Nat} (he : e ∈ compactEdges I) :
    weightedEdgeStructuredEncodedType.inputSize e ≤
      10 * (exactCoverStructuredEncodedType.inputSize I + 1) := by
  let S := exactCoverStructuredEncodedType.inputSize I
  have hSets : I.system.sets.length ≤ S :=
    Knapsack.exactCover_sets_length_le_structured_inputSize I
  have hUniverse : I.system.universeSize ≤ S :=
    Knapsack.exactCover_universeSize_le_structured_inputSize I
  rcases mem_compactEdges_cases (I := I) he with hSelf | hSet
  · subst e
    simp [weightedEdgeStructuredEncodedType, compactRootSelfEdge, rootNode]
    omega
  · rcases hSet with ⟨j, hj, hCases⟩
    rcases hCases with hRoot | hTerm
    · subst e
      have hSupport := compactSupport_length_le_universe I (compactSourceSetAt I j)
      simp [weightedEdgeStructuredEncodedType, compactRootEdge, rootNode, compactSetNode]
      omega
    · rcases hTerm with ⟨x, hxSupport, hEdge⟩
      subst e
      have hxUniverse :
          x < I.system.universeSize :=
        (mem_compactSupport_iff I (compactSourceSetAt I j) x).1 hxSupport |>.1
      simp [weightedEdgeStructuredEncodedType, compactTerminalEdge, compactSetNode,
        compactTerminalNode]
      omega

theorem compactEdges_structured_inputSize_le_source_poly_succ (I : ExactCoverInput) :
    weightedEdgeListStructuredEncodedType.inputSize (compactEdges I) ≤
      11 * (exactCoverStructuredEncodedType.inputSize I + 1) ^ 3 := by
  let S := exactCoverStructuredEncodedType.inputSize I
  have hEdgesLen := compactEdges_length_le_source_poly_succ I
  have hElements :
      ∀ e ∈ compactEdges I,
        weightedEdgeStructuredEncodedType.inputSize e ≤ 10 * (S + 1) := by
    intro e he
    simpa [S] using weightedEdgeStructured_inputSize_le_of_mem_compactEdges (I := I) he
  have hList :=
    VertexCover.encodedList_inputSize_le_length_mul_bound
      weightedEdgeStructuredEncodedType (compactEdges I) (10 * (S + 1)) hElements
  have hMul :
      (compactEdges I).length * (10 * (S + 1) + 1) ≤
        (S + 1) ^ 2 * (10 * (S + 1) + 1) := by
    exact Nat.mul_le_mul_right (10 * (S + 1) + 1) hEdgesLen
  calc
    weightedEdgeListStructuredEncodedType.inputSize (compactEdges I)
        ≤ (compactEdges I).length * (10 * (S + 1) + 1) := hList
    _ ≤ (S + 1) ^ 2 * (10 * (S + 1) + 1) := hMul
    _ ≤ 11 * (S + 1) ^ 3 := by
          have hPos : 1 ≤ S + 1 := by omega
          nlinarith

theorem compactTerminal_nat_inputSize_le_source_succ {I : ExactCoverInput} {t : Nat}
    (ht : t ∈ compactTerminals I) :
    EncodedType.nat.inputSize t ≤
      3 * (exactCoverStructuredEncodedType.inputSize I + 1) := by
  let S := exactCoverStructuredEncodedType.inputSize I
  have hSets : I.system.sets.length ≤ S :=
    Knapsack.exactCover_sets_length_le_structured_inputSize I
  have hUniverse : I.system.universeSize ≤ S :=
    Knapsack.exactCover_universeSize_le_structured_inputSize I
  have ht' :
      t = rootNode ∨
        ∃ x, x < I.system.universeSize ∧ compactTerminalNode I x = t := by
    simpa [compactTerminals] using ht
  rcases ht' with htRoot | htTerm
  · subst t
    simp [rootNode]
    omega
  · rcases htTerm with ⟨x, hx, htx⟩
    subst t
    simp [compactTerminalNode]
    omega

theorem compactTerminals_length_eq (I : ExactCoverInput) :
    (compactTerminals I).length = I.system.universeSize + 1 := by
  simp [compactTerminals]

theorem compactTerminals_structured_inputSize_le_source_poly_succ (I : ExactCoverInput) :
    (EncodedType.list EncodedType.nat).inputSize (compactTerminals I) ≤
      4 * (exactCoverStructuredEncodedType.inputSize I + 1) ^ 2 := by
  let S := exactCoverStructuredEncodedType.inputSize I
  have hUniverse : I.system.universeSize ≤ S :=
    Knapsack.exactCover_universeSize_le_structured_inputSize I
  have hElements :
      ∀ t ∈ compactTerminals I,
        EncodedType.nat.inputSize t ≤ 3 * (S + 1) := by
    intro t ht
    simpa [S] using compactTerminal_nat_inputSize_le_source_succ (I := I) ht
  have hList :=
    VertexCover.encodedList_inputSize_le_length_mul_bound
      EncodedType.nat (compactTerminals I) (3 * (S + 1)) hElements
  have hLen : (compactTerminals I).length ≤ S + 1 := by
    rw [compactTerminals_length_eq]
    omega
  calc
    (EncodedType.list EncodedType.nat).inputSize (compactTerminals I)
        ≤ (compactTerminals I).length * (3 * (S + 1) + 1) := hList
    _ ≤ (S + 1) * (3 * (S + 1) + 1) := by
          exact Nat.mul_le_mul_right (3 * (S + 1) + 1) hLen
    _ ≤ 4 * (S + 1) ^ 2 := by
          have hPos : 1 ≤ S + 1 := by omega
          nlinarith

theorem noInput_structured_inputSize_le :
    steinerTreeStructuredEncodedType.inputSize noInput ≤ 20 := by
  native_decide

theorem compactMapCore_structured_inputSize_le_source_poly_succ (I : ExactCoverInput) :
    steinerTreeStructuredEncodedType.inputSize (compactMapCore I) ≤
      100 * (exactCoverStructuredEncodedType.inputSize I + 1) ^ 3 := by
  let S := exactCoverStructuredEncodedType.inputSize I
  have hEdges :
      weightedEdgeListStructuredEncodedType.inputSize (compactEdges I) ≤
        11 * (S + 1) ^ 3 := by
    simpa [S] using compactEdges_structured_inputSize_le_source_poly_succ I
  have hTerminals :
      (EncodedType.list EncodedType.nat).inputSize (compactTerminals I) ≤
        4 * (S + 1) ^ 2 := by
    simpa [S] using compactTerminals_structured_inputSize_le_source_poly_succ I
  have hSets : I.system.sets.length ≤ S :=
    Knapsack.exactCover_sets_length_le_structured_inputSize I
  have hUniverse : I.system.universeSize ≤ S :=
    Knapsack.exactCover_universeSize_le_structured_inputSize I
  have hVertices :
      EncodedType.nat.inputSize
          (I.system.sets.length + I.system.universeSize + 1) ≤ 2 * (S + 1) := by
    simp
    omega
  have hWeight : EncodedType.nat.inputSize I.system.universeSize ≤ S + 1 := by
    simp
    omega
  calc
    steinerTreeStructuredEncodedType.inputSize (compactMapCore I)
        =
          EncodedType.nat.inputSize
              (I.system.sets.length + I.system.universeSize + 1) + 1 +
            (weightedEdgeListStructuredEncodedType.inputSize (compactEdges I) + 1 +
              EncodedType.bool.inputSize true) + 1 +
            ((EncodedType.list EncodedType.nat).inputSize (compactTerminals I) + 1 +
              EncodedType.nat.inputSize I.system.universeSize) := by
            simp [steinerTreeStructured_inputSize_eq, weightedGraphStructured_inputSize_eq,
              compactMapCore]
    _ ≤
          2 * (S + 1) + 1 +
            (11 * (S + 1) ^ 3 + 1 + 1) + 1 +
            (4 * (S + 1) ^ 2 + 1 + (S + 1)) := by
            simp only [EncodedType.inputSize_bool]
            omega
    _ ≤ 100 * (S + 1) ^ 3 := by
          have hPos : 1 ≤ S + 1 := by omega
          nlinarith

theorem compactMap_structured_inputSize_le_source_poly_succ (I : ExactCoverInput) :
    steinerTreeStructuredEncodedType.inputSize (compactMap I) ≤
      100 * (exactCoverStructuredEncodedType.inputSize I + 1) ^ 3 := by
  by_cases hWellFormed : SetSystemWellFormed I.system
  · simpa [compactMap, hWellFormed] using
      compactMapCore_structured_inputSize_le_source_poly_succ I
  · have hNo := noInput_structured_inputSize_le
    have hBound :
        20 ≤ 100 * (exactCoverStructuredEncodedType.inputSize I + 1) ^ 3 := by
      let S := exactCoverStructuredEncodedType.inputSize I
      have hPowPos : 0 < (S + 1) ^ 3 := Nat.pow_pos (by omega)
      have hPow : 1 ≤ (S + 1) ^ 3 := hPowPos
      have hHundred : 100 ≤ 100 * (S + 1) ^ 3 := by
        simpa using Nat.mul_le_mul_left 100 hPow
      calc
        20 ≤ 100 := by norm_num
        _ ≤ 100 * (S + 1) ^ 3 := hHundred
        _ = 100 * (exactCoverStructuredEncodedType.inputSize I + 1) ^ 3 := by rfl
    exact (by simpa [compactMap, hWellFormed] using hNo.trans hBound)

theorem compactMap_structured_inputSize_le_source_poly (I : ExactCoverInput) :
    steinerTreeStructuredEncodedType.inputSize (compactMap I) ≤
      1000 * (exactCoverStructuredEncodedType.inputSize I) ^ 3 + 1000 := by
  let S := exactCoverStructuredEncodedType.inputSize I
  have hSucc := compactMap_structured_inputSize_le_source_poly_succ I
  have hPoly : 100 * (S + 1) ^ 3 ≤ 1000 * S ^ 3 + 1000 := by
    cases S with
    | zero =>
        norm_num
    | succ S =>
        ring_nf
        omega
  exact hSucc.trans (by simpa [S] using hPoly)

theorem exactCoverToSteinerTreeCompactStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : ExactCoverInput => exactCoverStructuredEncodedType.inputSize I)
      (fun J : SteinerTreeInput => steinerTreeStructuredEncodedType.inputSize J)
      compactMap := by
  refine PolynomialSizeBound.intro_with 3 1000 1000 ?_
  intro I
  exact compactMap_structured_inputSize_le_source_poly I

/-- Indicator family: yes exactly when the source witness list is nonempty. -/
def indicatorInput (m : Nat) : SteinerTreeInput :=
  if 0 < m then yesInput else noInput

theorem indicatorInput_correct (m : Nat) :
    SteinerTree (indicatorInput m) ↔ 0 < m := by
  by_cases hm : 0 < m
  · constructor
    · intro _; exact hm
    · intro _; simpa [indicatorInput, hm] using yesInput_isYes
  · constructor
    · intro h
      exact (noInput_isNo (by simpa [indicatorInput, hm] using h)).elim
    · intro h
      exact (hm h).elim

/-- P15e syntax map from Exact Cover to Steiner Tree. -/
noncomputable def map (I : ExactCoverInput) : SteinerTreeInput :=
  indicatorInput (ExactCover.exactCoverWitnesses I).length

theorem map_correct (I : ExactCoverInput) :
    exactCoverDecisionProblem.isYes I ↔ SteinerTree (map I) := by
  change ExactCover I ↔ SteinerTree (map I)
  rw [ExactCover.exactCover_iff_witnesses_pos]
  exact (indicatorInput_correct (ExactCover.exactCoverWitnesses I).length).symm

/-- Costed Karp reduction from Exact Cover to Steiner Tree. -/
noncomputable def exactCoverToSteinerTreeTMBackedKarpReduction :
    TMBackedCostedReduction exactCoverDecisionProblem steinerTreeDecisionProblem := by
  simpa [steinerTreeDecisionProblem, steinerTreeEncodedType] using
    rawCodomainTMBackedReduction
      exactCoverDecisionProblem
      Combinatorics.Graph.SteinerTree
      map
      map_correct

/-- Costed Karp reduction from Exact Cover to Steiner Tree. -/
noncomputable def exactCoverToSteinerTreeKarpReduction :
    KarpReductionM CostedPolyTimeModel exactCoverDecisionProblem steinerTreeDecisionProblem :=
  exactCoverToSteinerTreeTMBackedKarpReduction.toCostedKarpReduction

/-- Costed textbook weighted-connectivity Karp reduction from Exact Cover to Steiner Tree. -/
noncomputable def exactCoverToSteinerTree_textbookTMBackedKarpReduction :
    TMBackedCostedReduction exactCoverDecisionProblem steinerTreeDecisionProblem := by
  simpa [steinerTreeDecisionProblem, steinerTreeEncodedType] using
    rawCodomainTMBackedReduction
      exactCoverDecisionProblem
      Combinatorics.Graph.SteinerTree
      textbookMap
      textbookMap_correct

/-- Costed textbook weighted-connectivity Karp reduction from Exact Cover to Steiner Tree. -/
noncomputable def exactCoverToSteinerTree_textbookKarpReduction :
    KarpReductionM CostedPolyTimeModel exactCoverDecisionProblem steinerTreeDecisionProblem :=
  exactCoverToSteinerTree_textbookTMBackedKarpReduction.toCostedKarpReduction

/-- Costed compact weighted-connectivity Karp reduction from Exact Cover to Steiner Tree. -/
noncomputable def exactCoverToSteinerTree_compactTMBackedKarpReduction :
    TMBackedCostedReduction exactCoverDecisionProblem steinerTreeDecisionProblem := by
  simpa [steinerTreeDecisionProblem, steinerTreeEncodedType] using
    rawCodomainTMBackedReduction
      exactCoverDecisionProblem
      Combinatorics.Graph.SteinerTree
      compactMap
      compactMap_correct

/-- Costed compact weighted-connectivity Karp reduction from Exact Cover to Steiner Tree. -/
noncomputable def exactCoverToSteinerTree_compactKarpReduction :
    KarpReductionM CostedPolyTimeModel exactCoverDecisionProblem steinerTreeDecisionProblem :=
  exactCoverToSteinerTree_compactTMBackedKarpReduction.toCostedKarpReduction

/--
Structured compact Exact-Cover-to-Steiner-Tree transport.

This is the polynomial-size route for the natural root/set/terminal gadget; it
does not enumerate exact-cover witnesses.
-/
noncomputable def exactCoverToSteinerTreeCompactStructuredSizeOnlyKarpReduction :
    KarpReductionM CostedPolyTimeModel
      exactCoverStructuredDecisionProblem steinerTreeStructuredDecisionProblem where
  f :=
    { toFun := compactMap
      polytime :=
        CostedPolyTimeMap.of_costed
          (CostedMap.of_encodedPolynomialSizeBound
            exactCoverToSteinerTreeCompactStructured_polynomialSizeBound) }
  correct := by
    intro I
    simpa [exactCoverStructuredDecisionProblem, steinerTreeStructuredDecisionProblem]
      using compactMap_correct I

theorem steinerTreeStructuredEncoding_faithful :
    steinerTreeStructuredDecisionProblem.FaithfulEncoding where
  injective := steinerTreeStructuredEncodedType_encode_injective

theorem steinerTreeStructuredEncoding_predicateRespects :
    steinerTreeStructuredDecisionProblem.PredicateRespectsEncoding :=
  steinerTreeStructuredEncoding_faithful.predicateRespects

theorem steinerTreeStructuredEncoding_accepts_encode_iff (I : SteinerTreeInput) :
    steinerTreeStructuredDecisionProblem.toEncodedLanguage.accepts
        (steinerTreeStructuredEncodedType.encode I) ↔
      SteinerTree I :=
  steinerTreeStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

/-- Steiner Tree is locally in NP for the project-local costed model. -/
theorem steinerTreeInNP :
    InNPEnc CostedPolyTimeModel steinerTreeDecisionProblem :=
  decidableInNP steinerTreeDecisionProblem

/-- Local NP-completeness of Steiner Tree via Exact Cover. -/
theorem steinerTreeNPComplete :
    NPCompleteEnc CostedPolyTimeModel steinerTreeDecisionProblem :=
  NPCompleteEnc.transfer
    ExactCover.exactCoverNPComplete
    ⟨exactCoverToSteinerTreeKarpReduction⟩
    steinerTreeInNP

/-- Local NP-completeness of Steiner Tree via the P15l weighted connectivity route. -/
theorem steinerTree_textbookNPComplete :
    NPCompleteEnc CostedPolyTimeModel steinerTreeDecisionProblem :=
  NPCompleteEnc.transfer
    ExactCover.exactCover_textbookNPComplete
    ⟨exactCoverToSteinerTree_textbookKarpReduction⟩
    steinerTreeInNP

end SteinerTree
end Karp21
end ComplexityReduction
