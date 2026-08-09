import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.Part2
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.StructuredTM.SubsetWeights

namespace ComplexityReduction
namespace Karp21
namespace Partition
open ComplexityReduction.Combinatorics

theorem knapsackToPartitionCompactBinaryStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : KnapsackInput => knapsackBinaryStructuredEncodedType.inputSize I)
      (fun J : PartitionInput => partitionBinaryStructuredEncodedType.inputSize J)
      compactTextbookMap := by
  refine PolynomialSizeBound.intro_with 2 4000 0 ?_
  intro I
  exact compactTextbookMap_binaryStructured_inputSize_le_knapsack_poly I

/-! ### Structured finite-alphabet size bound for the textbook route -/

theorem partitionWeightsStructured_inputSize_eq (weights : List Nat) :
    partitionWeightsStructuredEncodedType.inputSize weights =
      weights.sum + 2 * weights.length := by
  induction weights with
  | nil =>
      exact EncodedType.inputSize_list_nil EncodedType.nat
  | cons w ws ih =>
      calc
        partitionWeightsStructuredEncodedType.inputSize (w :: ws)
            = EncodedType.nat.inputSize w + 1 +
                partitionWeightsStructuredEncodedType.inputSize ws := by
              exact EncodedType.inputSize_list_cons EncodedType.nat w ws
        _ = (w + 1) + 1 + (ws.sum + 2 * ws.length) := by
              simp [ih]
        _ = (w :: ws).sum + 2 * (w :: ws).length := by
              simp
              omega

theorem partitionStructured_inputSize_eq (I : PartitionInput) :
    partitionStructuredEncodedType.inputSize I =
      I.weights.sum + 2 * I.weights.length := by
  simpa [partitionStructuredEncodedType] using
    partitionWeightsStructured_inputSize_eq I.weights

theorem itemWeightTotal_le_itemListStructured_inputSize (items : List (Nat × Nat)) :
    itemWeightTotal items ≤ knapsackItemListStructuredEncodedType.inputSize items := by
  induction items with
  | nil =>
      simp [itemWeightTotal, knapsackItemListStructuredEncodedType]
  | cons item items ih =>
      rcases item with ⟨w, v⟩
      calc
        itemWeightTotal ((w, v) :: items) = w + itemWeightTotal items := by
          simp [itemWeightTotal]
        _ ≤ w + knapsackItemListStructuredEncodedType.inputSize items := by
          exact Nat.add_le_add_left ih w
        _ ≤ knapsackItemStructuredEncodedType.inputSize (w, v) + 1 +
              knapsackItemListStructuredEncodedType.inputSize items := by
          simp [knapsackItemStructuredEncodedType]
          omega
        _ = knapsackItemListStructuredEncodedType.inputSize ((w, v) :: items) := by
          symm
          exact EncodedType.inputSize_list_cons knapsackItemStructuredEncodedType (w, v) items

theorem itemValueTotal_le_itemListStructured_inputSize (items : List (Nat × Nat)) :
    itemValueTotal items ≤ knapsackItemListStructuredEncodedType.inputSize items := by
  induction items with
  | nil =>
      simp [itemValueTotal, knapsackItemListStructuredEncodedType]
  | cons item items ih =>
      rcases item with ⟨w, v⟩
      calc
        itemValueTotal ((w, v) :: items) = v + itemValueTotal items := by
          simp [itemValueTotal]
        _ ≤ v + knapsackItemListStructuredEncodedType.inputSize items := by
          exact Nat.add_le_add_left ih v
        _ ≤ knapsackItemStructuredEncodedType.inputSize (w, v) + 1 +
              knapsackItemListStructuredEncodedType.inputSize items := by
          simp [knapsackItemStructuredEncodedType]
          omega
        _ = knapsackItemListStructuredEncodedType.inputSize ((w, v) :: items) := by
          symm
          exact EncodedType.inputSize_list_cons knapsackItemStructuredEncodedType (w, v) items

theorem itemLength_le_itemListStructured_inputSize (items : List (Nat × Nat)) :
    items.length ≤ knapsackItemListStructuredEncodedType.inputSize items := by
  induction items with
  | nil =>
      simp [knapsackItemListStructuredEncodedType]
  | cons item items ih =>
      rcases item with ⟨w, v⟩
      calc
        ((w, v) :: items).length = items.length + 1 := by simp
        _ ≤ knapsackItemListStructuredEncodedType.inputSize items + 1 := by omega
        _ ≤ knapsackItemStructuredEncodedType.inputSize (w, v) + 1 +
              knapsackItemListStructuredEncodedType.inputSize items := by
          simp [knapsackItemStructuredEncodedType]
        _ = knapsackItemListStructuredEncodedType.inputSize ((w, v) :: items) := by
          symm
          exact EncodedType.inputSize_list_cons knapsackItemStructuredEncodedType (w, v) items

theorem knapsackStructured_inputSize_eq (I : KnapsackInput) :
    knapsackStructuredEncodedType.inputSize I =
      knapsackItemListStructuredEncodedType.inputSize I.items +
        I.capacity + I.targetValue + 4 := by
  change knapsackTupleStructuredEncodedType.inputSize (I.items, (I.capacity, I.targetValue)) =
    knapsackItemListStructuredEncodedType.inputSize I.items + I.capacity + I.targetValue + 4
  simp [knapsackTupleStructuredEncodedType, knapsackBoundsStructuredEncodedType]
  omega

theorem itemWeightTotal_le_knapsackStructured_inputSize (I : KnapsackInput) :
    itemWeightTotal I.items ≤ knapsackStructuredEncodedType.inputSize I := by
  have hItems := itemWeightTotal_le_itemListStructured_inputSize I.items
  rw [knapsackStructured_inputSize_eq]
  omega

theorem itemValueTotal_le_knapsackStructured_inputSize (I : KnapsackInput) :
    itemValueTotal I.items ≤ knapsackStructuredEncodedType.inputSize I := by
  have hItems := itemValueTotal_le_itemListStructured_inputSize I.items
  rw [knapsackStructured_inputSize_eq]
  omega

theorem itemLength_le_knapsackStructured_inputSize (I : KnapsackInput) :
    I.items.length ≤ knapsackStructuredEncodedType.inputSize I := by
  have hItems := itemLength_le_itemListStructured_inputSize I.items
  rw [knapsackStructured_inputSize_eq]
  omega

theorem capacity_le_knapsackStructured_inputSize (I : KnapsackInput) :
    I.capacity ≤ knapsackStructuredEncodedType.inputSize I := by
  rw [knapsackStructured_inputSize_eq]
  omega

theorem targetValue_le_knapsackStructured_inputSize (I : KnapsackInput) :
    I.targetValue ≤ knapsackStructuredEncodedType.inputSize I := by
  rw [knapsackStructured_inputSize_eq]
  omega

theorem encodedItems_sum_eq (base : Nat) (items : List (Nat × Nat)) :
    (encodedItems base items).sum =
      base * itemWeightTotal items + itemValueTotal items := by
  induction items with
  | nil =>
      simp [encodedItems, itemWeightTotal, itemValueTotal]
  | cons item items ih =>
      rcases item with ⟨w, v⟩
      simp [encodedItems, encodedItem, itemWeightTotal, itemValueTotal] at ih ⊢
      rw [ih]
      ring_nf

theorem knapsackSubsetWeights_sum_eq (I : KnapsackInput) :
    (knapsackSubsetWeights I).sum =
      partitionTextbookBase I * itemWeightTotal I.items + itemValueTotal I.items +
        I.capacity * partitionTextbookBase I + valueSlackBudget I := by
  simp [knapsackSubsetWeights, encodedItems_sum_eq, Nat.add_assoc]

theorem knapsackSubsetWeights_length_eq (I : KnapsackInput) :
    (knapsackSubsetWeights I).length =
      I.items.length + I.capacity + valueSlackBudget I := by
  simp [knapsackSubsetWeights, encodedItems, Nat.add_assoc]

theorem valueTargetLevel_le_knapsackStructured_inputSize (I : KnapsackInput) :
    valueTargetLevel I ≤ knapsackStructuredEncodedType.inputSize I := by
  have hValue := itemValueTotal_le_knapsackStructured_inputSize I
  have hTarget := targetValue_le_knapsackStructured_inputSize I
  unfold valueTargetLevel
  omega

theorem valueSlackBudget_le_knapsackStructured_inputSize (I : KnapsackInput) :
    valueSlackBudget I ≤ knapsackStructuredEncodedType.inputSize I := by
  have hLevel := valueTargetLevel_le_knapsackStructured_inputSize I
  unfold valueSlackBudget
  omega

theorem partitionTextbookBase_le_knapsackStructured_inputSize (I : KnapsackInput) :
    partitionTextbookBase I ≤ 3 * (knapsackStructuredEncodedType.inputSize I + 1) := by
  have hLevel := valueTargetLevel_le_knapsackStructured_inputSize I
  unfold partitionTextbookBase
  omega

theorem knapsackSubsetTarget_sum_le_knapsackStructured_poly (I : KnapsackInput) :
    knapsackSubsetTarget I ≤
      (3 * (knapsackStructuredEncodedType.inputSize I + 1)) *
          knapsackStructuredEncodedType.inputSize I +
        knapsackStructuredEncodedType.inputSize I := by
  have hBase :
      partitionTextbookBase I ≤ 3 * (knapsackStructuredEncodedType.inputSize I + 1) :=
    partitionTextbookBase_le_knapsackStructured_inputSize I
  have hCap : I.capacity ≤ knapsackStructuredEncodedType.inputSize I :=
    capacity_le_knapsackStructured_inputSize I
  have hLevel : valueTargetLevel I ≤ knapsackStructuredEncodedType.inputSize I :=
    valueTargetLevel_le_knapsackStructured_inputSize I
  have hMul :
      partitionTextbookBase I * I.capacity ≤
        (3 * (knapsackStructuredEncodedType.inputSize I + 1)) *
          knapsackStructuredEncodedType.inputSize I :=
    Nat.mul_le_mul hBase hCap
  simp [knapsackSubsetTarget]
  omega

theorem knapsackSubsetWeights_sum_le_knapsackStructured_poly (I : KnapsackInput) :
    (knapsackSubsetWeights I).sum ≤
      2 * ((3 * (knapsackStructuredEncodedType.inputSize I + 1)) *
          knapsackStructuredEncodedType.inputSize I) +
        2 * knapsackStructuredEncodedType.inputSize I := by
  have hBase :
      partitionTextbookBase I ≤ 3 * (knapsackStructuredEncodedType.inputSize I + 1) :=
    partitionTextbookBase_le_knapsackStructured_inputSize I
  have hWeight : itemWeightTotal I.items ≤ knapsackStructuredEncodedType.inputSize I :=
    itemWeightTotal_le_knapsackStructured_inputSize I
  have hValue : itemValueTotal I.items ≤ knapsackStructuredEncodedType.inputSize I :=
    itemValueTotal_le_knapsackStructured_inputSize I
  have hCap : I.capacity ≤ knapsackStructuredEncodedType.inputSize I :=
    capacity_le_knapsackStructured_inputSize I
  have hSlack : valueSlackBudget I ≤ knapsackStructuredEncodedType.inputSize I :=
    valueSlackBudget_le_knapsackStructured_inputSize I
  have hPart₁ :
      partitionTextbookBase I * itemWeightTotal I.items ≤
        (3 * (knapsackStructuredEncodedType.inputSize I + 1)) *
          knapsackStructuredEncodedType.inputSize I :=
    Nat.mul_le_mul hBase hWeight
  have hPart₂ :
      I.capacity * partitionTextbookBase I ≤
        (3 * (knapsackStructuredEncodedType.inputSize I + 1)) *
          knapsackStructuredEncodedType.inputSize I := by
    have h := Nat.mul_le_mul hCap hBase
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  rw [knapsackSubsetWeights_sum_eq]
  omega

theorem knapsackSubsetWeights_length_le_knapsackStructured_poly (I : KnapsackInput) :
    (knapsackSubsetWeights I).length ≤ 3 * knapsackStructuredEncodedType.inputSize I := by
  let S := knapsackStructuredEncodedType.inputSize I
  have hItems : I.items.length ≤ S := by
    simpa [S] using itemLength_le_knapsackStructured_inputSize I
  have hCap : I.capacity ≤ S := by
    simpa [S] using capacity_le_knapsackStructured_inputSize I
  have hSlack : valueSlackBudget I ≤ S := by
    simpa [S] using valueSlackBudget_le_knapsackStructured_inputSize I
  rw [knapsackSubsetWeights_length_eq]
  omega

theorem partitionStructured_inputSize_textbookMap_le_knapsack_poly (I : KnapsackInput) :
    partitionStructuredEncodedType.inputSize (textbookMap I) ≤
      1000 * (knapsackStructuredEncodedType.inputSize I) ^ 4 + 1000 := by
  let S := knapsackStructuredEncodedType.inputSize I
  let A := (3 * (S + 1)) * S
  have hSubset : (knapsackSubsetWeights I).sum ≤ 2 * A + 2 * S := by
    simpa [S, A] using knapsackSubsetWeights_sum_le_knapsackStructured_poly I
  have hTarget : knapsackSubsetTarget I ≤ A + S := by
    simpa [S, A] using knapsackSubsetTarget_sum_le_knapsackStructured_poly I
  have hLength : (knapsackSubsetWeights I).length ≤ 3 * S := by
    simpa [S] using knapsackSubsetWeights_length_le_knapsackStructured_poly I
  have hOutput :
      partitionStructuredEncodedType.inputSize (textbookMap I) =
        2 * (knapsackSubsetWeights I).sum + 2 * knapsackSubsetTarget I +
          2 * ((knapsackSubsetWeights I).length + 2) := by
    simp [textbookMap, partitionStructured_inputSize_eq, subsetToPartitionWeights,
      Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    ring_nf
  have hCoarse :
      partitionStructuredEncodedType.inputSize (textbookMap I) ≤ 6 * A + 12 * S + 4 := by
    rw [hOutput]
    omega
  calc
    partitionStructuredEncodedType.inputSize (textbookMap I) ≤ 6 * A + 12 * S + 4 := hCoarse
    _ ≤ 1000 * S ^ 4 + 1000 := by
      dsimp [A]
      cases S with
      | zero =>
          norm_num
      | succ S =>
          ring_nf
          omega

theorem knapsackToPartitionStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : KnapsackInput => knapsackStructuredEncodedType.inputSize I)
      (fun J : PartitionInput => partitionStructuredEncodedType.inputSize J)
      textbookMap := by
  refine PolynomialSizeBound.intro_with 4 1000 1000 ?_
  intro I
  exact partitionStructured_inputSize_textbookMap_le_knapsack_poly I

/-- Costed Karp reduction from Knapsack to Partition. -/
noncomputable def knapsackToPartitionTMBackedKarpReduction :
    TMBackedCostedReduction knapsackKarpDecisionProblem partitionDecisionProblem := by
  simpa [partitionDecisionProblem, partitionEncodedType] using
    rawCodomainTMBackedReduction
      knapsackKarpDecisionProblem
      Combinatorics.Partition
      map
      map_correct

/-- Costed Karp reduction from Knapsack to Partition. -/
noncomputable def knapsackToPartitionKarpReduction :
    KarpReductionM CostedPolyTimeModel knapsackKarpDecisionProblem partitionDecisionProblem :=
  knapsackToPartitionTMBackedKarpReduction.toCostedKarpReduction

/-- P15n textbook balancing Karp reduction from Knapsack to Partition. -/
noncomputable def knapsackToPartition_textbookTMBackedKarpReduction :
    TMBackedCostedReduction knapsackKarpDecisionProblem partitionDecisionProblem := by
  simpa [partitionDecisionProblem, partitionEncodedType] using
    rawCodomainTMBackedReduction
      knapsackKarpDecisionProblem
      Combinatorics.Partition
      textbookMap
      textbookMap_correct

/-- P15n textbook balancing Karp reduction from Knapsack to Partition. -/
noncomputable def knapsackToPartition_textbookKarpReduction :
    KarpReductionM CostedPolyTimeModel knapsackKarpDecisionProblem partitionDecisionProblem :=
  knapsackToPartition_textbookTMBackedKarpReduction.toCostedKarpReduction

/-- Size-only costed wrapper for the structured P15n textbook balancing route. -/
noncomputable def knapsackToPartitionStructuredCostedKarpReduction :
    KarpReductionM CostedPolyTimeModel
      knapsackStructuredDecisionProblem partitionStructuredDecisionProblem where
  f :=
    { toFun := textbookMap
      polytime :=
        CostedPolyTimeMap.of_costed
          (CostedMap.of_encodedPolynomialSizeBound
            knapsackToPartitionStructured_polynomialSizeBound) }
  correct := by
    intro I
    simpa [knapsackStructuredDecisionProblem, partitionStructuredDecisionProblem]
      using textbookMap_correct I

noncomputable def knapsackToPartitionStructuredTMBackedMap :
    TMBackedCostedMap
      knapsackStructuredEncodedType
      partitionStructuredEncodedType
      textbookMap where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      knapsackToPartitionStructured_polynomialSizeBound
  tm_polytime := knapsackToPartitionStructured_tm_polytime

noncomputable def knapsackToPartitionStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      knapsackStructuredDecisionProblem
      partitionStructuredDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    knapsackToPartitionStructuredTMBackedMap
    (by
      intro I
      simpa [knapsackStructuredDecisionProblem, partitionStructuredDecisionProblem]
        using textbookMap_correct I)

/--
P16c structured finite-alphabet version of the P15n textbook balancing route,
projected from the direct TM-backed witness.
-/
noncomputable def knapsackToPartitionStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      knapsackStructuredDecisionProblem partitionStructuredDecisionProblem :=
  knapsackToPartitionStructuredTMBackedKarpReduction.toCostedKarpReduction

/-- Direct TM-facing structured Knapsack-to-Partition reduction. -/
noncomputable def knapsackToPartitionStructuredTMKarpReduction :
    TMKarpReduction
      knapsackStructuredDecisionProblem
      partitionStructuredDecisionProblem :=
  knapsackToPartitionStructuredTMBackedKarpReduction.toTMKarpReduction

/-- Binary-numeric structured version of the compact P15n balancing route. -/
noncomputable def knapsackToPartitionBinaryStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      knapsackBinaryStructuredDecisionProblem partitionBinaryStructuredDecisionProblem where
  f :=
    { toFun := compactTextbookMap
      polytime :=
        CostedPolyTimeMap.of_costed
          (CostedMap.of_encodedPolynomialSizeBound
            knapsackToPartitionCompactBinaryStructured_polynomialSizeBound) }
  correct := by
    intro I
    simpa [knapsackBinaryStructuredDecisionProblem, partitionBinaryStructuredDecisionProblem]
      using compactTextbookMap_correct I

theorem partitionStructuredEncoding_faithful :
    partitionStructuredDecisionProblem.FaithfulEncoding where
  injective := partitionStructuredEncodedType_encode_injective

theorem partitionStructuredEncoding_predicateRespects :
    partitionStructuredDecisionProblem.PredicateRespectsEncoding :=
  partitionStructuredEncoding_faithful.predicateRespects

theorem partitionStructuredEncoding_accepts_encode_iff (I : PartitionInput) :
    partitionStructuredDecisionProblem.toEncodedLanguage.accepts
        (partitionStructuredEncodedType.encode I) ↔
      Partition I :=
  partitionStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

theorem partitionBinaryStructuredEncoding_faithful :
    partitionBinaryStructuredDecisionProblem.FaithfulEncoding where
  injective := partitionBinaryStructuredEncodedType_encode_injective

theorem partitionBinaryStructuredEncoding_predicateRespects :
    partitionBinaryStructuredDecisionProblem.PredicateRespectsEncoding :=
  partitionBinaryStructuredEncoding_faithful.predicateRespects

theorem partitionBinaryStructuredEncoding_accepts_encode_iff (I : PartitionInput) :
    partitionBinaryStructuredDecisionProblem.toEncodedLanguage.accepts
        (partitionBinaryStructuredEncodedType.encode I) ↔
      Partition I :=
  partitionBinaryStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

/-- Partition is locally in NP for the project-local costed model. -/
theorem partitionInNP :
    InNPEnc CostedPolyTimeModel partitionDecisionProblem :=
  decidableInNP partitionDecisionProblem

/-- Local NP-completeness of Partition via Knapsack. -/
theorem partitionNPComplete :
    NPCompleteEnc CostedPolyTimeModel partitionDecisionProblem :=
  NPCompleteEnc.transfer
    Knapsack.knapsackNPComplete
    ⟨knapsackToPartitionKarpReduction⟩
    partitionInNP

/-- Local NP-completeness of Partition via the P15n textbook balancing route. -/
theorem partition_textbookNPComplete :
    NPCompleteEnc CostedPolyTimeModel partitionDecisionProblem :=
  NPCompleteEnc.transfer
    Knapsack.knapsack_textbookNPComplete
    ⟨knapsackToPartition_textbookKarpReduction⟩
    partitionInNP

end Partition
end Karp21
end ComplexityReduction
