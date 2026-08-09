/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.CNFSplit

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction
open Turing.TM2.Stmt

theorem threeCNFStructured_inputSize_le_encodeThreeCNF_length (φ : SAT.ThreeCNF) :
    threeCNFStructuredEncodedType.inputSize φ ≤
      (SAT.ThreeSATEncoding.encodeThreeCNF φ).length := by
  simpa [threeCNFStructuredEncodedType, SAT.ThreeSATEncoding.encodeCNF] using
    cnfStructured_inputSize_le_encodeCNF_length φ.clauses

theorem cnfSATToThreeSATStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun φ : SAT.CNF => cnfStructuredEncodedType.inputSize φ)
      (fun ψ : SAT.ThreeCNF => threeCNFStructuredEncodedType.inputSize ψ)
      SAT.CNF.splitToThreeCNF := by
  refine PolynomialSizeBound.intro_with 2 1000 1000 ?_
  intro φ
  let S := cnfStructuredEncodedType.inputSize φ
  have hEncode := threeCNFStructured_inputSize_le_encodeThreeCNF_length
    (SAT.CNF.splitToThreeCNF φ)
  have hSplit := SAT.CNF.splitToThreeCNF_encodedLength_le_quadraticStructural φ
  have hStruct : SAT.CNF.structuralSize φ ≤ 2 * S + 1 := by
    simpa [S] using cnfStructuralSize_le_structured_inputSize_poly_base φ
  have hPow : (SAT.CNF.structuralSize φ) ^ 2 ≤ (2 * S + 1) ^ 2 :=
    Nat.pow_le_pow_left hStruct 2
  calc
    threeCNFStructuredEncodedType.inputSize (SAT.CNF.splitToThreeCNF φ)
        ≤ (SAT.ThreeSATEncoding.encodeThreeCNF (SAT.CNF.splitToThreeCNF φ)).length :=
          hEncode
    _ ≤ 20 * (SAT.CNF.structuralSize φ) ^ 2 := hSplit
    _ ≤ 20 * (2 * S + 1) ^ 2 := Nat.mul_le_mul_left 20 hPow
    _ ≤ 1000 * S ^ 2 + 1000 := by
          nlinarith [sq_nonneg (S : Int)]

/-- Forget the bundled 3CNF proof and view a local 3SAT instance as a CNF. -/
def threeCNFToCNF (φ : SAT.ThreeCNF) : SAT.CNF :=
  φ.clauses

theorem threeSATToCNFSATStructured_linearSizeBound :
    LinearSizeBound
      (fun φ : SAT.ThreeCNF => threeCNFStructuredEncodedType.inputSize φ)
      (fun ψ : SAT.CNF => cnfStructuredEncodedType.inputSize ψ)
      threeCNFToCNF :=
  LinearSizeBound.of_le (by
    intro φ
    rfl)
theorem cnfSATToThreeSAT_linearSizeBound :
    LinearSizeBound
      (fun φ : SAT.CNF => satisfiabilityDecisionProblem.Instance.inputSize φ)
      (fun ψ : SAT.ThreeCNF => SAT.threeSATDecisionProblem.Instance.inputSize ψ)
      SAT.CNF.splitToThreeCNF :=
  LinearSizeBound.of_le (by
    intro φ
    change
      (SAT.ThreeSATEncoding.encodeThreeCNF (SAT.CNF.splitToThreeCNF φ)).length ≤
        (SAT.ThreeSATEncoding.encodeThreeCNF (SAT.CNF.splitToThreeCNF φ)).length
    exact Nat.le_refl _)

theorem threeCNFToCNF_satisfiable_iff (φ : SAT.ThreeCNF) :
    SAT.CNF.Satisfiable (threeCNFToCNF φ) ↔ SAT.ThreeCNF.Satisfiable φ :=
  Iff.rfl

theorem splitToThreeCNF_eq_self_of_threeCNF (φ : SAT.ThreeCNF) :
    SAT.CNF.splitToThreeCNF φ.clauses = φ := by
  cases φ with
  | mk clauses hThree =>
      simp [SAT.CNF.splitToThreeCNF,
        SAT.CNF.splitTo3CNFList_eq_self_of_isThree clauses hThree]

theorem threeSATToCNFSAT_linearSizeBound :
    LinearSizeBound
      (fun φ : SAT.ThreeCNF => SAT.threeSATDecisionProblem.Instance.inputSize φ)
      (fun ψ : SAT.CNF => satisfiabilityDecisionProblem.Instance.inputSize ψ)
      threeCNFToCNF :=
  LinearSizeBound.of_le (by
    intro φ
    change
      (SAT.ThreeSATEncoding.encodeThreeCNF (SAT.CNF.splitToThreeCNF φ.clauses)).length ≤
        (SAT.ThreeSATEncoding.encodeThreeCNF φ).length
    rw [splitToThreeCNF_eq_self_of_threeCNF φ])

/--
Structured costed Karp reduction from faithful finite-alphabet CNF SAT to
faithful finite-alphabet bundled 3SAT.
-/
noncomputable def cnfSATToThreeSATStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      satisfiabilityStructuredDecisionProblem threeSATStructuredDecisionProblem :=
  cnfSATToThreeSATStructuredTMBackedKarpReduction.toCostedKarpReduction

noncomputable def cnfSATToThreeSATStructuredTMKarpReduction :
    TMKarpReduction satisfiabilityStructuredDecisionProblem threeSATStructuredDecisionProblem :=
  cnfSATToThreeSATStructuredTMBackedKarpReduction.toTMKarpReduction

/--
Direct TM-backed version of the faithful finite-alphabet bundled-3SAT to CNF
wrapper.  The map erases only the proof that clauses are three-bounded, so the
underlying structured encoding is preserved exactly.
-/
noncomputable def threeSATToCNFSATStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      threeSATStructuredDecisionProblem satisfiabilityStructuredDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    (TMBackedCostedMap.ofEncodingEquiv
      threeCNFStructuredEncodedType cnfStructuredEncodedType threeCNFToCNF
      (Equiv.refl _) (by
        intro φ
        change
          cnfStructuredEncodedType.encode φ.clauses =
            List.map (Equiv.refl cnfStructuredEncodedType.Symbol)
              (cnfStructuredEncodedType.encode φ.clauses)
        simp))
    (by
      intro φ
      exact (threeCNFToCNF_satisfiable_iff φ).symm)

theorem threeSATToCNFSATStructured_tm_polytime :
    TMPolyTimeMap threeCNFStructuredEncodedType cnfStructuredEncodedType threeCNFToCNF :=
  threeSATToCNFSATStructuredTMBackedKarpReduction.tm_polytime

/--
Structured costed Karp reduction from faithful finite-alphabet bundled 3SAT to
faithful finite-alphabet CNF SAT.
-/
noncomputable def threeSATToCNFSATStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      threeSATStructuredDecisionProblem satisfiabilityStructuredDecisionProblem :=
  threeSATToCNFSATStructuredTMBackedKarpReduction.toCostedKarpReduction

noncomputable def threeSATToCNFSATStructuredTMKarpReduction :
    TMKarpReduction threeSATStructuredDecisionProblem satisfiabilityStructuredDecisionProblem :=
  threeSATToCNFSATStructuredTMBackedKarpReduction.toTMKarpReduction

/-- Structured polynomial-time equivalence between faithful CNF SAT and faithful 3SAT syntax. -/
noncomputable def satisfiability_threeSatisfiability_structuredProblemEquiv :
    ProblemEquivM CostedPolyTimeModel
      satisfiabilityStructuredDecisionProblem threeSATStructuredDecisionProblem where
  toMap := cnfSATToThreeSATStructuredKarpReduction.f
  invMap := threeSATToCNFSATStructuredKarpReduction.f
  to_correct := cnfSATToThreeSATStructuredKarpReduction.correct
  inv_correct := threeSATToCNFSATStructuredKarpReduction.correct

/--
Direct TM-backed version of the project-local CNF SAT to bundled 3SAT wrapper.
The raw CNF SAT encoding is already the encoded split 3CNF formula, so the map
preserves encoded strings exactly.
-/
noncomputable def cnfSATToThreeSATTMBackedKarpReduction :
    TMBackedCostedReduction satisfiabilityDecisionProblem SAT.threeSATDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    (TMBackedCostedMap.ofEncodingEquiv
      satisfiabilityDecisionProblem.Instance SAT.threeSATDecisionProblem.Instance
      SAT.CNF.splitToThreeCNF (Equiv.refl _) (by
        intro φ
        change
          SAT.ThreeSATEncoding.encodeThreeCNF (SAT.CNF.splitToThreeCNF φ) =
            List.map (Equiv.refl SAT.ThreeSATSymbol)
              (SAT.ThreeSATEncoding.encodeThreeCNF (SAT.CNF.splitToThreeCNF φ))
        simp))
    (by
      intro φ
      exact (SAT.CNF.splitToThreeCNF_satisfiable_iff φ).symm)

/-- Costed Karp reduction from project-local CNF SAT to bundled local 3SAT. -/
noncomputable def cnfSATToThreeSATKarpReduction :
    KarpReductionM CostedPolyTimeModel
      satisfiabilityDecisionProblem SAT.threeSATDecisionProblem :=
  cnfSATToThreeSATTMBackedKarpReduction.toCostedKarpReduction

noncomputable def cnfSATToThreeSATTMKarpReduction :
    TMKarpReduction satisfiabilityDecisionProblem SAT.threeSATDecisionProblem :=
  cnfSATToThreeSATTMBackedKarpReduction.toTMKarpReduction

/--
Direct TM-backed version of the project-local bundled-3SAT to CNF wrapper.
Although the target raw SAT encoding is defined through the splitter, splitting
the underlying CNF of a bundled 3CNF formula is extensionally the original
bundle, so the encoded string is preserved exactly.
-/
noncomputable def threeSATToCNFSATTMBackedKarpReduction :
    TMBackedCostedReduction SAT.threeSATDecisionProblem satisfiabilityDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    (TMBackedCostedMap.ofEncodingEquiv
      SAT.threeSATDecisionProblem.Instance satisfiabilityDecisionProblem.Instance threeCNFToCNF
      (Equiv.refl _) (by
        intro φ
        change
          SAT.ThreeSATEncoding.encodeThreeCNF (SAT.CNF.splitToThreeCNF φ.clauses) =
            List.map (Equiv.refl SAT.ThreeSATSymbol) (SAT.ThreeSATEncoding.encodeThreeCNF φ)
        rw [splitToThreeCNF_eq_self_of_threeCNF φ]
        simp))
    (by
      intro φ
      exact (threeCNFToCNF_satisfiable_iff φ).symm)

/-- Costed Karp reduction from bundled local 3SAT to project-local CNF SAT. -/
noncomputable def threeSATToCNFSATKarpReduction :
    KarpReductionM CostedPolyTimeModel
      SAT.threeSATDecisionProblem satisfiabilityDecisionProblem :=
  threeSATToCNFSATTMBackedKarpReduction.toCostedKarpReduction

noncomputable def threeSATToCNFSATTMKarpReduction :
    TMKarpReduction SAT.threeSATDecisionProblem satisfiabilityDecisionProblem :=
  threeSATToCNFSATTMBackedKarpReduction.toTMKarpReduction

/-- Project-local polynomial-time equivalence between CNF SAT and bundled 3SAT. -/
noncomputable def satisfiability_threeSatisfiability_problemEquiv :
    ProblemEquivM CostedPolyTimeModel
      satisfiabilityDecisionProblem SAT.threeSATDecisionProblem where
  toMap := cnfSATToThreeSATKarpReduction.f
  invMap := threeSATToCNFSATKarpReduction.f
  to_correct := cnfSATToThreeSATKarpReduction.correct
  inv_correct := threeSATToCNFSATKarpReduction.correct

/-- General local CNF satisfiability belongs to the project-local encoded NP class. -/
theorem satisfiabilityInNP :
    InNPEnc CostedPolyTimeModel satisfiabilityDecisionProblem :=
  InNPEnc.of_reduction ⟨cnfSATToThreeSATKarpReduction⟩ SAT.threeSAT_inNP

/--
Project-local NP-completeness of general CNF satisfiability, transported from
the P14e local Cook-Levin theorem for bundled 3SAT.
-/
theorem satisfiabilityNPComplete :
    NPCompleteEnc CostedPolyTimeModel satisfiabilityDecisionProblem :=
  Targets.npComplete_of_localThreeSAT_karp
    satisfiabilityDecisionProblem
    threeSATToCNFSATKarpReduction
    satisfiabilityInNP

end Karp21
end ComplexityReduction
