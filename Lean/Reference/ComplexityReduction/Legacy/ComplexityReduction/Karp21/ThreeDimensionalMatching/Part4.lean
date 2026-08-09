import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeDimensionalMatching.Part3

namespace ComplexityReduction
namespace Karp21
namespace ThreeDimensionalMatching
open ComplexityReduction.Combinatorics

theorem compactMapCore_structured_inputSize_le_source_poly_succ (I : ExactCoverInput) :
    threeDimensionalMatchingStructuredEncodedType.inputSize (compactMapCore I) ≤
      32 * (exactCoverStructuredEncodedType.inputSize I + 1) ^ 6 := by
  let S := exactCoverStructuredEncodedType.inputSize I
  have hTriples :
      tripleListStructuredEncodedType.inputSize (compactTriples I) ≤ 10 * (S + 1) ^ 6 := by
    simpa [S] using compactTriples_structured_inputSize_le_source_poly_succ I
  have hCoord :
      EncodedType.nat.inputSize (compactCoordBound I) ≤ (S + 1) ^ 2 + 1 := by
    simpa [S] using compactCoordBound_nat_inputSize_le_source_succ_sq I
  have hK :
      EncodedType.nat.inputSize (compactPositionCodes I).length ≤ (S + 1) ^ 2 + 1 := by
    simpa [S] using compactPositionCodes_nat_inputSize_le_source_succ_sq I
  have hBase : 1 ≤ S + 1 := by omega
  have hPow2 : (S + 1) ^ 2 ≤ (S + 1) ^ 6 :=
    Nat.pow_le_pow_right hBase (by norm_num : 2 ≤ 6)
  have hPow1 : 1 ≤ (S + 1) ^ 6 :=
    Nat.one_le_pow 6 (S + 1) (by omega : 0 < S + 1)
  have hCoord' : compactCoordBound I + 1 ≤ (S + 1) ^ 2 + 1 := by
    simpa using hCoord
  have hK' : (compactPositionCodes I).length + 1 ≤ (S + 1) ^ 2 + 1 := by
    simpa using hK
  rw [threeDimensionalMatchingStructured_inputSize_eq]
  simp [compactMapCore]
  nlinarith

theorem noInput_structured_inputSize_le_source_poly_succ (I : ExactCoverInput) :
    threeDimensionalMatchingStructuredEncodedType.inputSize noInput ≤
      32 * (exactCoverStructuredEncodedType.inputSize I + 1) ^ 6 := by
  let S := exactCoverStructuredEncodedType.inputSize I
  have hPow : 1 ≤ (S + 1) ^ 6 :=
    Nat.one_le_pow 6 (S + 1) (by omega : 0 < S + 1)
  have hNil :
      tripleListStructuredEncodedType.inputSize ([] : List (Nat × Nat × Nat)) = 0 := by
    change (EncodedType.list tripleStructuredEncodedType).inputSize
      ([] : List (Nat × Nat × Nat)) = 0
    rfl
  rw [threeDimensionalMatchingStructured_inputSize_eq]
  simp [noInput, hNil]
  nlinarith

theorem compactMap_structured_inputSize_le_source_poly_succ (I : ExactCoverInput) :
    threeDimensionalMatchingStructuredEncodedType.inputSize (compactMap I) ≤
      32 * (exactCoverStructuredEncodedType.inputSize I + 1) ^ 6 := by
  classical
  by_cases hGuard : SetSystemWellFormed I.system ∧ compactEveryElementOccurs I
  · simpa [compactMap, hGuard] using compactMapCore_structured_inputSize_le_source_poly_succ I
  · simpa [compactMap, hGuard] using noInput_structured_inputSize_le_source_poly_succ I

theorem compactMap_structured_inputSize_le_source_poly (I : ExactCoverInput) :
    threeDimensionalMatchingStructuredEncodedType.inputSize (compactMap I) ≤
      2048 * (exactCoverStructuredEncodedType.inputSize I) ^ 6 := by
  let S := exactCoverStructuredEncodedType.inputSize I
  have hSucc : threeDimensionalMatchingStructuredEncodedType.inputSize (compactMap I) ≤
      32 * (S + 1) ^ 6 := by
    simpa [S] using compactMap_structured_inputSize_le_source_poly_succ I
  have hSpos : 0 < S := by
    simpa [S] using Knapsack.exactCoverStructured_inputSize_pos I
  have hSuccLe : S + 1 ≤ 2 * S := by omega
  have hPow : (S + 1) ^ 6 ≤ (2 * S) ^ 6 :=
    Nat.pow_le_pow_left hSuccLe 6
  calc
    threeDimensionalMatchingStructuredEncodedType.inputSize (compactMap I)
        ≤ 32 * (S + 1) ^ 6 := hSucc
    _ ≤ 32 * (2 * S) ^ 6 := by
          exact Nat.mul_le_mul_left 32 hPow
    _ = 2048 * S ^ 6 := by ring

theorem exactCoverToThreeDimensionalMatchingCompactStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : ExactCoverInput => exactCoverStructuredEncodedType.inputSize I)
      (fun J : ThreeDimensionalMatchingInput =>
        threeDimensionalMatchingStructuredEncodedType.inputSize J)
      compactMap := by
  refine ⟨6, 2048, 0, ?_⟩
  intro I
  simpa using compactMap_structured_inputSize_le_source_poly I

/-- Indicator family: yes exactly when the source witness list is nonempty. -/
def indicatorInput (m : Nat) : ThreeDimensionalMatchingInput :=
  if 0 < m then yesInput else noInput

theorem indicatorInput_correct (m : Nat) :
    ThreeDimensionalMatching (indicatorInput m) ↔ 0 < m := by
  by_cases hm : 0 < m
  · constructor
    · intro _; exact hm
    · intro _; simpa [indicatorInput, hm] using yesInput_isYes
  · constructor
    · intro h
      exact (noInput_isNo (by simpa [indicatorInput, hm] using h)).elim
    · intro h
      exact (hm h).elim

/-- P15e syntax map from Exact Cover to 3-Dimensional Matching. -/
noncomputable def map (I : ExactCoverInput) : ThreeDimensionalMatchingInput :=
  indicatorInput (ExactCover.exactCoverWitnesses I).length

theorem map_correct (I : ExactCoverInput) :
    exactCoverDecisionProblem.isYes I ↔ ThreeDimensionalMatching (map I) := by
  change ExactCover I ↔ ThreeDimensionalMatching (map I)
  rw [ExactCover.exactCover_iff_witnesses_pos]
  exact (indicatorInput_correct (ExactCover.exactCoverWitnesses I).length).symm

/-- Costed Karp reduction from Exact Cover to 3-Dimensional Matching. -/
noncomputable def exactCoverToThreeDimensionalMatchingTMBackedKarpReduction :
    TMBackedCostedReduction exactCoverDecisionProblem
      threeDimensionalMatchingDecisionProblem := by
  simpa [threeDimensionalMatchingDecisionProblem, threeDimensionalMatchingEncodedType] using
    rawCodomainTMBackedReduction
      exactCoverDecisionProblem
      Combinatorics.ThreeDimensionalMatching
      map
      map_correct

/-- Costed Karp reduction from Exact Cover to 3-Dimensional Matching. -/
noncomputable def exactCoverToThreeDimensionalMatchingKarpReduction :
    KarpReductionM CostedPolyTimeModel exactCoverDecisionProblem
      threeDimensionalMatchingDecisionProblem :=
  exactCoverToThreeDimensionalMatchingTMBackedKarpReduction.toCostedKarpReduction

/-- Costed textbook X/Y/Z triple reduction from Exact Cover to 3-Dimensional Matching. -/
noncomputable def exactCoverToThreeDimensionalMatching_textbookTMBackedKarpReduction :
    TMBackedCostedReduction exactCoverDecisionProblem
      threeDimensionalMatchingDecisionProblem := by
  simpa [threeDimensionalMatchingDecisionProblem, threeDimensionalMatchingEncodedType] using
    rawCodomainTMBackedReduction
      exactCoverDecisionProblem
      Combinatorics.ThreeDimensionalMatching
      textbookMap
      textbookMap_correct

/-- Costed textbook X/Y/Z triple reduction from Exact Cover to 3-Dimensional Matching. -/
noncomputable def exactCoverToThreeDimensionalMatching_textbookKarpReduction :
    KarpReductionM CostedPolyTimeModel exactCoverDecisionProblem
      threeDimensionalMatchingDecisionProblem :=
  exactCoverToThreeDimensionalMatching_textbookTMBackedKarpReduction.toCostedKarpReduction

/-- Costed compact membership-cycle Karp reduction from Exact Cover to 3DM. -/
noncomputable def exactCoverToThreeDimensionalMatching_compactTMBackedKarpReduction :
    TMBackedCostedReduction exactCoverDecisionProblem
      threeDimensionalMatchingDecisionProblem := by
  simpa [threeDimensionalMatchingDecisionProblem, threeDimensionalMatchingEncodedType] using
    rawCodomainTMBackedReduction
      exactCoverDecisionProblem
      Combinatorics.ThreeDimensionalMatching
      compactMap
      compactMap_correct

/-- Costed compact membership-cycle Karp reduction from Exact Cover to 3DM. -/
noncomputable def exactCoverToThreeDimensionalMatching_compactKarpReduction :
    KarpReductionM CostedPolyTimeModel exactCoverDecisionProblem
      threeDimensionalMatchingDecisionProblem :=
  exactCoverToThreeDimensionalMatching_compactTMBackedKarpReduction.toCostedKarpReduction

/--
Size-only structured compact Exact-Cover-to-3DM transport.

This is the polynomial-size membership-cycle route from Karp's construction; it
does not enumerate exact-cover witnesses.  The direct TM-backed structured
surface reuses the public name in `ThreeDimensionalMatchingStructuredTM`.
-/
noncomputable def exactCoverToThreeDimensionalMatchingCompactStructuredSizeOnlyKarpReduction :
    KarpReductionM CostedPolyTimeModel
      exactCoverStructuredDecisionProblem threeDimensionalMatchingStructuredDecisionProblem where
  f :=
    { toFun := compactMap
      polytime :=
        CostedPolyTimeMap.of_costed
          (CostedMap.of_encodedPolynomialSizeBound
            exactCoverToThreeDimensionalMatchingCompactStructured_polynomialSizeBound) }
  correct := by
    intro I
    simpa [exactCoverStructuredDecisionProblem, threeDimensionalMatchingStructuredDecisionProblem]
      using compactMap_correct I

theorem threeDimensionalMatchingStructuredEncoding_faithful :
    threeDimensionalMatchingStructuredDecisionProblem.FaithfulEncoding where
  injective := threeDimensionalMatchingStructuredEncodedType_encode_injective

theorem threeDimensionalMatchingStructuredEncoding_predicateRespects :
    threeDimensionalMatchingStructuredDecisionProblem.PredicateRespectsEncoding :=
  threeDimensionalMatchingStructuredEncoding_faithful.predicateRespects

theorem threeDimensionalMatchingStructuredEncoding_accepts_encode_iff
    (I : ThreeDimensionalMatchingInput) :
    threeDimensionalMatchingStructuredDecisionProblem.toEncodedLanguage.accepts
        (threeDimensionalMatchingStructuredEncodedType.encode I) ↔
      ThreeDimensionalMatching I :=
  threeDimensionalMatchingStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

/-- 3-Dimensional Matching is locally in NP for the project-local costed model. -/
theorem threeDimensionalMatchingInNP :
    InNPEnc CostedPolyTimeModel threeDimensionalMatchingDecisionProblem :=
  decidableInNP threeDimensionalMatchingDecisionProblem

/-- Local NP-completeness of 3-Dimensional Matching via Exact Cover. -/
theorem threeDimensionalMatchingNPComplete :
    NPCompleteEnc CostedPolyTimeModel threeDimensionalMatchingDecisionProblem :=
  NPCompleteEnc.transfer
    ExactCover.exactCoverNPComplete
    ⟨exactCoverToThreeDimensionalMatchingKarpReduction⟩
    threeDimensionalMatchingInNP

/-- Local NP-completeness of 3DM via the P15k X/Y/Z triple route. -/
theorem threeDimensionalMatching_textbookNPComplete :
    NPCompleteEnc CostedPolyTimeModel threeDimensionalMatchingDecisionProblem :=
  NPCompleteEnc.transfer
    ExactCover.exactCover_textbookNPComplete
    ⟨exactCoverToThreeDimensionalMatching_textbookKarpReduction⟩
    threeDimensionalMatchingInNP

/-- Local NP-completeness of 3DM via the compact membership-cycle route. -/
theorem threeDimensionalMatching_compactNPComplete :
    NPCompleteEnc CostedPolyTimeModel threeDimensionalMatchingDecisionProblem :=
  NPCompleteEnc.transfer
    ExactCover.exactCover_textbookNPComplete
    ⟨exactCoverToThreeDimensionalMatching_compactKarpReduction⟩
    threeDimensionalMatchingInNP

end ThreeDimensionalMatching
end Karp21
end ComplexityReduction
