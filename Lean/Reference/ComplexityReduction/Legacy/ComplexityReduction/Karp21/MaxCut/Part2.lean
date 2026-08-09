import ComplexityReduction.Legacy.ComplexityReduction.Karp21.MaxCut.Part1

namespace ComplexityReduction
namespace Karp21
namespace MaxCut
open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

theorem weightedTextbookMap_vertices_binaryNat_inputSize_le_source_succ
    (I : PartitionInput) :
    EncodedType.binaryNat.inputSize (weightedTextbookMap I).graph.vertices ≤
      partitionBinaryStructuredEncodedType.inputSize I + 1 := by
  let S := partitionBinaryStructuredEncodedType.inputSize I
  let T := S + 1
  have hLen : I.weights.length ≤ S := by
    simpa [S] using partitionWeights_length_le_binaryStructured_inputSize I
  have hSltPow : S < 2 ^ T := by
    exact S.lt_two_pow_self.trans_le
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by dsimp [T]; omega))
  change EncodedType.binaryNat.inputSize I.weights.length ≤ T
  exact Knapsack.binaryNat_inputSize_le_of_lt_two_pow (hLen.trans_lt hSltPow)

theorem weightedMaxCutBinaryStructured_inputSize_textbookMap_le_partition_poly_succ
    (I : PartitionInput) :
    weightedMaxCutBinaryStructuredEncodedType.inputSize (weightedTextbookMap I) ≤
      1000 * (partitionBinaryStructuredEncodedType.inputSize I + 1) ^ 3 := by
  let S := partitionBinaryStructuredEncodedType.inputSize I
  let T := S + 1
  have hEdges := weightedTextbookEdges_binaryStructured_inputSize_le_source_succ I
  have hEdgesT :
      weightedEdgeListBinaryStructuredEncodedType.inputSize (weightedTextbookEdges I.weights) ≤
        100 * T ^ 3 := by
    simpa [T, S] using hEdges
  have hVertices :
      EncodedType.binaryNat.inputSize (weightedTextbookMap I).graph.vertices ≤ T := by
    simpa [T, S] using weightedTextbookMap_vertices_binaryNat_inputSize_le_source_succ I
  have hVerticesRaw : EncodedType.binaryNat.inputSize I.weights.length ≤ T := by
    simpa [weightedTextbookMap, weightedTextbookGraph] using hVertices
  have hThreshold :
      EncodedType.binaryNat.inputSize (weightedTextbookMap I).threshold ≤ 4 * T + 1 := by
    simpa [T, S] using weightedTextbookMap_threshold_binaryNat_inputSize_le_source_linear I
  have hThresholdRaw :
      EncodedType.binaryNat.inputSize (I.weights.sum * I.weights.sum) ≤ 4 * T + 1 := by
    simpa [weightedTextbookMap] using hThreshold
  have hOutput :
      weightedMaxCutBinaryStructuredEncodedType.inputSize (weightedTextbookMap I) ≤
        T + 1 + (100 * T ^ 3 + 1 + 1) + 1 + (4 * T + 1) := by
    rw [weightedMaxCutBinaryStructured_inputSize_eq, weightedGraphBinaryStructured_inputSize_eq]
    simp [weightedTextbookMap, weightedTextbookGraph]
    omega
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hTleT3 : T ≤ T ^ 3 := by
    have hTleT2 : T ≤ T * T := by
      simpa using Nat.mul_le_mul_left T hT
    have hT2leT3 : T * T ≤ T * T * T := by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left (T * T) hT
    exact hTleT2.trans (by simpa [pow_succ, pow_two, Nat.mul_assoc] using hT2leT3)
  have hCoarse :
      T + 1 + (100 * T ^ 3 + 1 + 1) + 1 + (4 * T + 1) ≤ 1000 * T ^ 3 := by
    nlinarith
  exact hOutput.trans hCoarse

theorem weightedMaxCutBinaryStructured_inputSize_textbookMap_le_partition_poly
    (I : PartitionInput) :
    weightedMaxCutBinaryStructuredEncodedType.inputSize (weightedTextbookMap I) ≤
      8000 * (partitionBinaryStructuredEncodedType.inputSize I) ^ 3 + 1000 := by
  let S := partitionBinaryStructuredEncodedType.inputSize I
  have hSucc := weightedMaxCutBinaryStructured_inputSize_textbookMap_le_partition_poly_succ I
  have hSuccPow : (S + 1) ^ 3 ≤ 8 * S ^ 3 + 1 := by
    cases S with
    | zero =>
        norm_num
    | succ S =>
        have hBase : Nat.succ S + 1 ≤ 2 * Nat.succ S := by omega
        have hPow : (Nat.succ S + 1) ^ 3 ≤ (2 * Nat.succ S) ^ 3 :=
          Nat.pow_le_pow_left hBase 3
        calc
          (Nat.succ S + 1) ^ 3 ≤ (2 * Nat.succ S) ^ 3 := hPow
          _ = 8 * Nat.succ S ^ 3 := by ring
          _ ≤ 8 * Nat.succ S ^ 3 + 1 := Nat.le_add_right _ _
  calc
    weightedMaxCutBinaryStructuredEncodedType.inputSize (weightedTextbookMap I)
        ≤ 1000 * (S + 1) ^ 3 := by simpa [S] using hSucc
    _ ≤ 1000 * (8 * S ^ 3 + 1) := Nat.mul_le_mul_left 1000 hSuccPow
    _ = 8000 * S ^ 3 + 1000 := by ring

theorem partitionToWeightedMaxCutBinaryStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : PartitionInput => partitionBinaryStructuredEncodedType.inputSize I)
      (fun J : WeightedMaxCutInput => weightedMaxCutBinaryStructuredEncodedType.inputSize J)
      weightedTextbookMap := by
  refine PolynomialSizeBound.intro_with 3 8000 1000 ?_
  intro I
  exact weightedMaxCutBinaryStructured_inputSize_textbookMap_le_partition_poly I

/-! ### Structured finite-alphabet size bound for the textbook route -/

theorem textbookEdgesFrom_length_le (i w j : Nat) (weights : List Nat) :
    (textbookEdgesFrom i w j weights).length ≤ 4 * w * weights.sum := by
  induction weights generalizing j with
  | nil =>
      simp [textbookEdgesFrom]
  | cons v vs ih =>
      calc
        (textbookEdgesFrom i w j (v :: vs)).length =
            4 * w * v + (textbookEdgesFrom i w (j + 1) vs).length := by
              simp [textbookEdgesFrom]
        _ ≤ 4 * w * v + 4 * w * vs.sum := by
              exact Nat.add_le_add_left (ih (j := j + 1)) (4 * w * v)
        _ = 4 * w * (v :: vs).sum := by
              simp
              ring

theorem textbookEdgesFromList_length_le (i : Nat) (weights : List Nat) :
    (textbookEdgesFromList i weights).length ≤ 4 * weights.sum * weights.sum := by
  induction weights generalizing i with
  | nil =>
      simp [textbookEdgesFromList]
  | cons w ws ih =>
      have hHead := textbookEdgesFrom_length_le i w (i + 1) ws
      have hTail := ih (i := i + 1)
      have hLen :
          (textbookEdgesFromList i (w :: ws)).length ≤ 4 * w * ws.sum + 4 * ws.sum * ws.sum := by
        calc
          (textbookEdgesFromList i (w :: ws)).length =
              (textbookEdgesFrom i w (i + 1) ws).length +
                (textbookEdgesFromList (i + 1) ws).length := by
                simp [textbookEdgesFromList]
          _ ≤ 4 * w * ws.sum + 4 * ws.sum * ws.sum := by
                exact Nat.add_le_add hHead hTail
      have hPoly :
          4 * w * ws.sum + 4 * ws.sum * ws.sum ≤
            4 * (w + ws.sum) * (w + ws.sum) := by
        ring_nf
        omega
      exact hLen.trans (by
        simpa using hPoly)

theorem textbookEdges_length_le (weights : List Nat) :
    (textbookEdges weights).length ≤ 4 * weights.sum * weights.sum := by
  simpa [textbookEdges] using textbookEdgesFromList_length_le 0 weights

theorem textbookEdgesFrom_mem_bounds {i w j : Nat} {weights : List Nat}
    {e : Nat × Nat} (he : e ∈ textbookEdgesFrom i w j weights) :
    e.1 = i ∧ e.2 < j + weights.length := by
  induction weights generalizing j with
  | nil =>
      simp [textbookEdgesFrom] at he
  | cons v vs ih =>
      have hmem :
          e ∈ List.replicate (4 * w * v) (i, j) ∨
            e ∈ textbookEdgesFrom i w (j + 1) vs := by
        exact List.mem_append.1 (by simpa [textbookEdgesFrom] using he)
      rcases hmem with hrep | htail
      · have hEq : e = (i, j) := List.eq_of_mem_replicate hrep
        subst e
        simp
      · rcases ih (j := j + 1) htail with ⟨hFirst, hSecond⟩
        exact ⟨hFirst, by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hSecond⟩

theorem textbookEdgesFromList_mem_bounds {i : Nat} {weights : List Nat}
    {e : Nat × Nat} (he : e ∈ textbookEdgesFromList i weights) :
    e.1 < i + weights.length ∧ e.2 < i + weights.length := by
  induction weights generalizing i with
  | nil =>
      simp [textbookEdgesFromList] at he
  | cons w ws ih =>
      have hmem :
          e ∈ textbookEdgesFrom i w (i + 1) ws ∨
            e ∈ textbookEdgesFromList (i + 1) ws := by
        simpa [textbookEdgesFromList] using
          (List.mem_append.1 (by simpa [textbookEdgesFromList] using he))
      rcases hmem with hhead | htail
      · rcases textbookEdgesFrom_mem_bounds hhead with ⟨hFirst, hSecond⟩
        constructor
        · rw [hFirst]
          simp
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hSecond
      · rcases ih (i := i + 1) htail with ⟨hFirst, hSecond⟩
        constructor
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hFirst
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hSecond

theorem edgeStructured_inputSize_le_of_mem_textbookEdges {weights : List Nat}
    {e : Nat × Nat} (he : e ∈ textbookEdges weights) :
    edgeStructuredEncodedType.inputSize e ≤ 2 * weights.length + 1 := by
  rcases textbookEdgesFromList_mem_bounds (i := 0) (weights := weights)
      (by simpa [textbookEdges] using he) with ⟨hFirst, hSecond⟩
  cases e with
  | mk u v =>
      simp [edgeStructuredEncodedType] at hFirst hSecond ⊢
      omega

theorem textbookEdges_structured_inputSize_le (weights : List Nat) :
    edgeListStructuredEncodedType.inputSize (textbookEdges weights) ≤
      (4 * weights.sum * weights.sum) * (2 * weights.length + 2) := by
  have hList :=
    VertexCover.encodedList_inputSize_le_length_mul_bound edgeStructuredEncodedType
      (textbookEdges weights) (2 * weights.length + 1)
      (by
        intro e he
        exact edgeStructured_inputSize_le_of_mem_textbookEdges he)
  have hLen := textbookEdges_length_le weights
  exact hList.trans (by
    have hMul := Nat.mul_le_mul_right (2 * weights.length + 2) hLen
    simpa [edgeListStructuredEncodedType, Nat.add_assoc] using hMul)

theorem graphStructured_inputSize_eq (g : GraphInput) :
    graphStructuredEncodedType.inputSize g =
      g.vertices + edgeListStructuredEncodedType.inputSize g.edges + 4 := by
  change graphTupleStructuredEncodedType.inputSize (g.vertices, (g.edges, g.directed)) =
    g.vertices + edgeListStructuredEncodedType.inputSize g.edges + 4
  simp [graphTupleStructuredEncodedType, graphPayloadStructuredEncodedType]
  omega

theorem maxCutStructured_inputSize_eq (I : MaxCutInput) :
    maxCutStructuredEncodedType.inputSize I =
      graphStructuredEncodedType.inputSize I.graph + I.threshold + 2 := by
  change maxCutTupleStructuredEncodedType.inputSize (I.graph, I.threshold) =
    graphStructuredEncodedType.inputSize I.graph + I.threshold + 2
  simp [maxCutTupleStructuredEncodedType]
  omega

theorem partitionWeights_sum_le_partitionStructured_inputSize (I : PartitionInput) :
    I.weights.sum ≤ partitionStructuredEncodedType.inputSize I := by
  rw [Partition.partitionStructured_inputSize_eq]
  omega

theorem partitionWeights_length_le_partitionStructured_inputSize (I : PartitionInput) :
    I.weights.length ≤ partitionStructuredEncodedType.inputSize I := by
  rw [Partition.partitionStructured_inputSize_eq]
  omega

theorem maxCutStructured_inputSize_textbookMap_le_partition_poly (I : PartitionInput) :
    maxCutStructuredEncodedType.inputSize (textbookMap I) ≤
      1000 * (partitionStructuredEncodedType.inputSize I) ^ 4 + 1000 := by
  let S := partitionStructuredEncodedType.inputSize I
  have hSum : I.weights.sum ≤ S := by
    simpa [S] using partitionWeights_sum_le_partitionStructured_inputSize I
  have hLength : I.weights.length ≤ S := by
    simpa [S] using partitionWeights_length_le_partitionStructured_inputSize I
  have hEdges := textbookEdges_structured_inputSize_le I.weights
  have hSumSq : I.weights.sum * I.weights.sum ≤ S * S :=
    Nat.mul_le_mul hSum hSum
  have hEdgePoly :
      (4 * I.weights.sum * I.weights.sum) * (2 * I.weights.length + 2) ≤
        (4 * S * S) * (2 * S + 2) := by
    have hLeft : 4 * I.weights.sum * I.weights.sum ≤ 4 * S * S := by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 4 hSumSq
    have hRight : 2 * I.weights.length + 2 ≤ 2 * S + 2 := by omega
    exact Nat.mul_le_mul hLeft hRight
  have hOutput :
      maxCutStructuredEncodedType.inputSize (textbookMap I) ≤
        I.weights.length +
          (4 * I.weights.sum * I.weights.sum) * (2 * I.weights.length + 2) +
          4 + I.weights.sum * I.weights.sum + 2 := by
    rw [maxCutStructured_inputSize_eq, graphStructured_inputSize_eq]
    simp [textbookMap]
    omega
  have hCoarse :
      maxCutStructuredEncodedType.inputSize (textbookMap I) ≤
        S + (4 * S * S) * (2 * S + 2) + 4 + S * S + 2 := by
    omega
  calc
    maxCutStructuredEncodedType.inputSize (textbookMap I) ≤
        S + (4 * S * S) * (2 * S + 2) + 4 + S * S + 2 := hCoarse
    _ ≤ 1000 * S ^ 4 + 1000 := by
      cases S with
      | zero =>
          norm_num
      | succ S =>
          ring_nf
          omega

theorem partitionToMaxCutStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : PartitionInput => partitionStructuredEncodedType.inputSize I)
      (fun J : MaxCutInput => maxCutStructuredEncodedType.inputSize J)
      textbookMap := by
  refine PolynomialSizeBound.intro_with 4 1000 1000 ?_
  intro I
  exact maxCutStructured_inputSize_textbookMap_le_partition_poly I

/-- Costed Karp reduction from Partition to Max Cut. -/
noncomputable def partitionToMaxCutTMBackedKarpReduction :
    TMBackedCostedReduction partitionDecisionProblem maxCutDecisionProblem := by
  simpa [maxCutDecisionProblem, maxCutEncodedType] using
    rawCodomainTMBackedReduction
      partitionDecisionProblem
      Combinatorics.Graph.MaxCut
      map
      map_correct

/-- Costed Karp reduction from Partition to Max Cut. -/
noncomputable def partitionToMaxCutKarpReduction :
    KarpReductionM CostedPolyTimeModel partitionDecisionProblem maxCutDecisionProblem :=
  partitionToMaxCutTMBackedKarpReduction.toCostedKarpReduction

/-- P15o textbook complete-graph Karp reduction from Partition to Max Cut. -/
noncomputable def partitionToMaxCut_textbookTMBackedKarpReduction :
    TMBackedCostedReduction partitionDecisionProblem maxCutDecisionProblem := by
  simpa [maxCutDecisionProblem, maxCutEncodedType] using
    rawCodomainTMBackedReduction
      partitionDecisionProblem
      Combinatorics.Graph.MaxCut
      textbookMap
      textbookMap_correct

/-- P15o textbook complete-graph Karp reduction from Partition to Max Cut. -/
noncomputable def partitionToMaxCut_textbookKarpReduction :
    KarpReductionM CostedPolyTimeModel partitionDecisionProblem maxCutDecisionProblem :=
  partitionToMaxCut_textbookTMBackedKarpReduction.toCostedKarpReduction

/--
P16c structured finite-alphabet version of the P15o textbook cut route using
only the encoded polynomial-size bound.  The public
`partitionToMaxCutStructuredKarpReduction` name is supplied by the direct
TM-backed witness in `StructuredTM.Assembly`.
-/
noncomputable def partitionToMaxCutStructuredCostedKarpReduction :
    KarpReductionM CostedPolyTimeModel
      partitionStructuredDecisionProblem maxCutStructuredDecisionProblem where
  f :=
    { toFun := textbookMap
      polytime :=
        CostedPolyTimeMap.of_costed
          (CostedMap.of_encodedPolynomialSizeBound
            partitionToMaxCutStructured_polynomialSizeBound) }
  correct := by
    intro I
    simpa [partitionStructuredDecisionProblem, maxCutStructuredDecisionProblem]
      using textbookMap_correct I

/-- Binary-weighted finite-alphabet version of the P15o cut route. -/
noncomputable def partitionToWeightedMaxCutBinaryStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      partitionBinaryStructuredDecisionProblem weightedMaxCutBinaryStructuredDecisionProblem where
  f :=
    { toFun := weightedTextbookMap
      polytime :=
        CostedPolyTimeMap.of_costed
          (CostedMap.of_encodedPolynomialSizeBound
            partitionToWeightedMaxCutBinaryStructured_polynomialSizeBound) }
  correct := by
    intro I
    simpa [partitionBinaryStructuredDecisionProblem, weightedMaxCutBinaryStructuredDecisionProblem]
      using weightedTextbookMap_correct I

theorem weightedMaxCutBinaryStructuredEncoding_faithful :
    weightedMaxCutBinaryStructuredDecisionProblem.FaithfulEncoding where
  injective := weightedMaxCutBinaryStructuredEncodedType_encode_injective

theorem weightedMaxCutBinaryStructuredEncoding_predicateRespects :
    weightedMaxCutBinaryStructuredDecisionProblem.PredicateRespectsEncoding :=
  weightedMaxCutBinaryStructuredEncoding_faithful.predicateRespects

theorem weightedMaxCutBinaryStructuredEncoding_accepts_encode_iff (I : WeightedMaxCutInput) :
    weightedMaxCutBinaryStructuredDecisionProblem.toEncodedLanguage.accepts
        (weightedMaxCutBinaryStructuredEncodedType.encode I) ↔
      WeightedMaxCut I :=
  weightedMaxCutBinaryStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

theorem maxCutStructuredEncoding_faithful :
    maxCutStructuredDecisionProblem.FaithfulEncoding where
  injective := maxCutStructuredEncodedType_encode_injective

theorem maxCutStructuredEncoding_predicateRespects :
    maxCutStructuredDecisionProblem.PredicateRespectsEncoding :=
  maxCutStructuredEncoding_faithful.predicateRespects

theorem maxCutStructuredEncoding_accepts_encode_iff (I : MaxCutInput) :
    maxCutStructuredDecisionProblem.toEncodedLanguage.accepts
        (maxCutStructuredEncodedType.encode I) ↔
      MaxCut I :=
  maxCutStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

theorem maxCutBinaryStructuredEncoding_faithful :
    maxCutBinaryStructuredDecisionProblem.FaithfulEncoding where
  injective := maxCutBinaryStructuredEncodedType_encode_injective

theorem maxCutBinaryStructuredEncoding_predicateRespects :
    maxCutBinaryStructuredDecisionProblem.PredicateRespectsEncoding :=
  maxCutBinaryStructuredEncoding_faithful.predicateRespects

theorem maxCutBinaryStructuredEncoding_accepts_encode_iff (I : MaxCutInput) :
    maxCutBinaryStructuredDecisionProblem.toEncodedLanguage.accepts
        (maxCutBinaryStructuredEncodedType.encode I) ↔
      MaxCut I :=
  maxCutBinaryStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

/-- Max Cut is locally in NP for the project-local costed model. -/
theorem maxCutInNP :
    InNPEnc CostedPolyTimeModel maxCutDecisionProblem :=
  decidableInNP maxCutDecisionProblem

/-- Local NP-completeness of Max Cut via Partition. -/
theorem maxCutNPComplete :
    NPCompleteEnc CostedPolyTimeModel maxCutDecisionProblem :=
  NPCompleteEnc.transfer
    Partition.partitionNPComplete
    ⟨partitionToMaxCutKarpReduction⟩
    maxCutInNP

/-- Local NP-completeness of Max Cut via the P15o textbook cut route. -/
theorem maxCut_textbookNPComplete :
    NPCompleteEnc CostedPolyTimeModel maxCutDecisionProblem :=
  NPCompleteEnc.transfer
    Partition.partition_textbookNPComplete
    ⟨partitionToMaxCut_textbookKarpReduction⟩
    maxCutInNP

end MaxCut
end Karp21
end ComplexityReduction
