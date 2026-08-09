import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ZeroOneIP.StructuredTM.ConstraintsFold

namespace ComplexityReduction
namespace Karp21
namespace ZeroOneIP

open ComplexityReduction.Combinatorics

/-!
Final checked assembly for the structured 3SAT-to-0-1-IP route.

The clause-list runner in `ConstraintsFold` computes the constraint list from
the encoded input bound and the source clauses.  This file reifies the computed
tuple as `IntegerProgrammingInput` and exposes the public TM-backed reduction
surface.
-/

/-- Reify the tuple-shaped integer-programming payload as the project structure. -/
def integerProgrammingTupleToInput
    (p : integerProgrammingTupleStructuredEncodedType.Carrier) :
    IntegerProgrammingInput where
  numVariables := p.1
  constraints := p.2

theorem integerProgrammingTupleToInput_encode
    (p : integerProgrammingTupleStructuredEncodedType.Carrier) :
    integerProgrammingStructuredEncodedType.encode (integerProgrammingTupleToInput p) =
      integerProgrammingTupleStructuredEncodedType.encode p := by
  rcases p with ⟨numVariables, constraints⟩
  rfl

noncomputable def integerProgrammingTupleToInputTMBackedMap :
    TMBackedCostedMap
      integerProgrammingTupleStructuredEncodedType
      integerProgrammingStructuredEncodedType
      integerProgrammingTupleToInput :=
  TMBackedCostedMap.ofEncodingEquiv
    integerProgrammingTupleStructuredEncodedType integerProgrammingStructuredEncodedType
    integerProgrammingTupleToInput
    (Equiv.refl integerProgrammingTupleStructuredEncodedType.Symbol)
    (by
      intro p
      change integerProgrammingStructuredEncodedType.encode (integerProgrammingTupleToInput p) =
        (integerProgrammingTupleStructuredEncodedType.encode p).map id
      simp [integerProgrammingTupleToInput_encode])

def threeSATBoundedConstraintsInput (φ : SAT.ThreeCNF) : ConstraintsFromInput :=
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

theorem threeSATBoundedConstraintsInput_tm_polytime :
    TMPolyTimeMap
      threeCNFStructuredEncodedType
      constraintsFromInputEncodedType
      threeSATBoundedConstraintsInput := by
  have hBound :
      TMPolyTimeMap
        threeCNFStructuredEncodedType
        EncodedType.nat
        (fun φ : SAT.ThreeCNF => threeCNFStructuredEncodedType.inputSize φ) :=
    (encodedInputSizeNatTMBackedMap threeCNFStructuredEncodedType).tm_polytime
  have hPair := TMPolyTimeMap.prod_mk hBound threeCNFClauses_tm_polytime
  simpa [threeSATBoundedConstraintsInput, constraintsFromInputEncodedType] using hPair

def threeSATConstraintsTM (φ : SAT.ThreeCNF) : List (List Int × Int) :=
  constraintsFromComputedInput (threeSATBoundedConstraintsInput φ)

theorem threeSATConstraintsTM_tm_polytime :
    TMPolyTimeMap
      threeCNFStructuredEncodedType
      constraintListStructuredEncodedType
      threeSATConstraintsTM := by
  have hComp :=
    TMPolyTimeMap.comp constraintsFromComputedInput_tm_polytime
      threeSATBoundedConstraintsInput_tm_polytime
  simpa [Function.comp, threeSATConstraintsTM] using hComp

def threeSATToZeroOneIPStructuredTMMapComputed
    (φ : SAT.ThreeCNF) : IntegerProgrammingInput where
  numVariables := threeCNFStructuredEncodedType.inputSize φ
  constraints := threeSATConstraintsTM φ

theorem threeSATToZeroOneIPStructuredTMMapComputed_eq_textbook
    (φ : SAT.ThreeCNF) :
    threeSATToZeroOneIPStructuredTMMapComputed φ =
      threeSATToZeroOneIPStructuredTMMap φ := by
  have hConstraints :=
    constraintsFromComputedInput_eq_textbook
      (threeSATBoundedConstraintsInput φ)
      (by
        intro c hc
        exact φ.isThree c hc)
  unfold threeSATToZeroOneIPStructuredTMMapComputed threeSATToZeroOneIPStructuredTMMap
    boundedTextbookMap threeSATConstraintsTM
  simp [threeSATBoundedConstraintsInput, constraintsFromTextbookInput] at hConstraints ⊢
  exact hConstraints

theorem threeSATToZeroOneIPStructuredTMMapComputed_tm_polytime :
    TMPolyTimeMap
      threeCNFStructuredEncodedType
      integerProgrammingStructuredEncodedType
      threeSATToZeroOneIPStructuredTMMapComputed := by
  have hVariables :
      TMPolyTimeMap
        threeCNFStructuredEncodedType
        EncodedType.nat
        (fun φ : SAT.ThreeCNF => threeCNFStructuredEncodedType.inputSize φ) :=
    (encodedInputSizeNatTMBackedMap threeCNFStructuredEncodedType).tm_polytime
  have hConstraints := threeSATConstraintsTM_tm_polytime
  have hTuple :
      TMPolyTimeMap
        threeCNFStructuredEncodedType
        integerProgrammingTupleStructuredEncodedType
        (fun φ : SAT.ThreeCNF =>
          (threeCNFStructuredEncodedType.inputSize φ, threeSATConstraintsTM φ)) :=
    TMPolyTimeMap.prod_mk hVariables hConstraints
  have hOut :=
    TMPolyTimeMap.comp integerProgrammingTupleToInputTMBackedMap.tm_polytime hTuple
  simpa [Function.comp, integerProgrammingTupleToInput,
    threeSATToZeroOneIPStructuredTMMapComputed] using hOut

theorem threeSATToZeroOneIPStructuredTMMap_tm_polytime :
    TMPolyTimeMap
      threeCNFStructuredEncodedType
      integerProgrammingStructuredEncodedType
      threeSATToZeroOneIPStructuredTMMap := by
  convert threeSATToZeroOneIPStructuredTMMapComputed_tm_polytime using 1
  funext φ
  exact (threeSATToZeroOneIPStructuredTMMapComputed_eq_textbook φ).symm

theorem boundedTextbookConstraints_structured_inputSize_le
    (n : Nat) (φ : SAT.ThreeCNF) :
    constraintListStructuredEncodedType.inputSize
        (φ.clauses.map (clauseConstraint n)) ≤
      φ.clauses.length * (n * 6 + 7) := by
  have hList :=
    Clique.encodedList_inputSize_le_length_mul_bound constraintStructuredEncodedType
      (φ.clauses.map (clauseConstraint n))
      (n * 6 + 6)
      (by
        intro constraint hconstraint
        rcases List.mem_map.mp hconstraint with ⟨c, hc, rfl⟩
        exact clauseConstraint_structured_inputSize_le n (φ.isThree c hc))
  simpa [constraintListStructuredEncodedType] using hList

theorem threeSATToZeroOneIPStructuredTMMap_inputSize_le
    (φ : SAT.ThreeCNF) :
    integerProgrammingStructuredEncodedType.inputSize
        (threeSATToZeroOneIPStructuredTMMap φ) ≤
      1000 * (threeCNFStructuredEncodedType.inputSize φ) ^ 3 + 1000 := by
  let S := threeCNFStructuredEncodedType.inputSize φ
  let C := φ.clauses.length
  have hC : C ≤ S := by
    simpa [S, C] using Clique.threeCNFStructured_inputSize_ge_clauses_length φ
  have hConstraints := boundedTextbookConstraints_structured_inputSize_le S φ
  have hBase :
      integerProgrammingStructuredEncodedType.inputSize
          (threeSATToZeroOneIPStructuredTMMap φ) ≤
        S + C * (S * 6 + 7) + 2 := by
    rw [integerProgrammingStructured_inputSize_eq]
    have hNum :
        (threeSATToZeroOneIPStructuredTMMap φ).numVariables = S := by
      simp [threeSATToZeroOneIPStructuredTMMap, boundedTextbookMap, S]
    have hConstraintsEq :
        (threeSATToZeroOneIPStructuredTMMap φ).constraints =
          φ.clauses.map (clauseConstraint S) := by
      simp [threeSATToZeroOneIPStructuredTMMap, boundedTextbookMap, S]
    rw [hNum, hConstraintsEq]
    simpa [S, C, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hConstraints
  have hMul : C * (S * 6 + 7) ≤ S * (S * 6 + 7) :=
    Nat.mul_le_mul_right (S * 6 + 7) hC
  have hPolyBase :
      S + C * (S * 6 + 7) + 2 ≤ S + S * (S * 6 + 7) + 2 := by
    omega
  calc
    integerProgrammingStructuredEncodedType.inputSize
        (threeSATToZeroOneIPStructuredTMMap φ)
        ≤ S + C * (S * 6 + 7) + 2 := hBase
    _ ≤ S + S * (S * 6 + 7) + 2 := hPolyBase
    _ ≤ 1000 * S ^ 3 + 1000 := by
          cases S with
          | zero =>
              norm_num
          | succ S =>
              ring_nf
              omega

theorem threeSATToZeroOneIPStructuredTMMap_polynomialSizeBound :
    PolynomialSizeBound
      (fun φ : SAT.ThreeCNF => threeCNFStructuredEncodedType.inputSize φ)
      (fun I : IntegerProgrammingInput => integerProgrammingStructuredEncodedType.inputSize I)
      threeSATToZeroOneIPStructuredTMMap := by
  refine PolynomialSizeBound.intro_with 3 1000 1000 ?_
  intro φ
  exact threeSATToZeroOneIPStructuredTMMap_inputSize_le φ

noncomputable def threeSATToZeroOneIPStructuredTMBackedMap :
    TMBackedCostedMap
      threeCNFStructuredEncodedType
      integerProgrammingStructuredEncodedType
      threeSATToZeroOneIPStructuredTMMap where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      threeSATToZeroOneIPStructuredTMMap_polynomialSizeBound
  tm_polytime := threeSATToZeroOneIPStructuredTMMap_tm_polytime

noncomputable def threeSATToZeroOneIPStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      threeSATStructuredDecisionProblem zeroOneIntegerProgrammingStructuredDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    threeSATToZeroOneIPStructuredTMBackedMap
    (by
      intro φ
      simpa [threeSATStructuredDecisionProblem, zeroOneIntegerProgrammingStructuredDecisionProblem]
        using threeSATToZeroOneIPStructuredTMMap_correct φ)

/--
Public structured 3SAT-to-0-1-IP reduction, projected from the direct
TM-backed witness.
-/
noncomputable def threeSATToZeroOneIPStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      threeSATStructuredDecisionProblem zeroOneIntegerProgrammingStructuredDecisionProblem :=
  threeSATToZeroOneIPStructuredTMBackedKarpReduction.toCostedKarpReduction

/-- Direct TM-facing structured 3SAT-to-0-1-IP reduction. -/
noncomputable def threeSATToZeroOneIPStructuredTMKarpReduction :
    TMKarpReduction
      threeSATStructuredDecisionProblem zeroOneIntegerProgrammingStructuredDecisionProblem :=
  threeSATToZeroOneIPStructuredTMBackedKarpReduction.toTMKarpReduction

end ZeroOneIP
end Karp21
end ComplexityReduction
