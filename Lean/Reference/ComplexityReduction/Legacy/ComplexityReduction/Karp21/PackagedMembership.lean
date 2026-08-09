/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetSystem
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetPacking
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetCovering
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipVertexCover
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipClique
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipChromaticNumber
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipCliqueCover
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipExactCover
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipDirectedHamiltonianCircuit
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipUndirectedHamiltonianCircuit
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipPartition
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipMaxCut
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipMaxCutBinary
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipFeedbackNodeSet
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipFeedbackArcSet
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipJobSequencingVerifier
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipJobSequencingBinary
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipKnapsackBinary
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipPartitionBinary
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipThreeDimensionalMatching
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSteinerTree
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.Assembly
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ZeroOneIP.StructuredTM.UnaryToBinary
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeSATFiniteVerifierTMFormula
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.TMComplexityTransport

/-!
Direct standard-TM NP membership witnesses used by the Karp21 packaged catalog.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction
open ComplexityReduction.Combinatorics

/-- Finite-certificate verifier for faithful structured CNF satisfiability via the TM CNF splitter. -/
def satisfiabilityStructuredFiniteVerify (φ : SAT.CNF) (bits : List Bool) : Bool :=
  SAT.threeSATStructuredFiniteVerify (cnfSplitFromStructuredBoundToThreeCNF φ) bits

theorem cnfSplitFromStructuredBound_threeCNF_inputSize_le (φ : SAT.CNF) :
    threeCNFStructuredEncodedType.inputSize (cnfSplitFromStructuredBoundToThreeCNF φ) ≤
      1000 * (cnfStructuredEncodedType.inputSize φ) ^ 2 + 1000 := by
  let S := cnfStructuredEncodedType.inputSize φ
  have hBound : ∀ c ∈ φ, ∀ l ∈ c, l.var < S := by
    intro c hc l hl
    exact lt_of_lt_of_le (SAT.CNF.clause_vars_lt_varBound hc l hl)
      (by simpa [S] using cnfVarBound_le_cnfStructured_inputSize φ)
  have hEncode :=
    SAT.CNF.splitAux_encodedLength_le S φ hBound
  have hStruct :
      threeCNFStructuredEncodedType.inputSize (cnfSplitFromStructuredBoundToThreeCNF φ) ≤
        (SAT.ThreeSATEncoding.encodeCNF
          (SAT.CNF.splitAux (cnfStructuredEncodedType.inputSize φ) φ)).length := by
    simpa [cnfSplitFromStructuredBoundToThreeCNF, threeCNFStructuredEncodedType,
      EncodedType.inputSize, SAT.ThreeSATEncoding.encodeCNF] using
      cnfStructured_inputSize_le_encodeCNF_length
        (SAT.CNF.splitAux (cnfStructuredEncodedType.inputSize φ) φ)
  have hTotal := cnfStructured_inputSize_ge_totalClauseLength_add_length φ
  calc
    threeCNFStructuredEncodedType.inputSize (cnfSplitFromStructuredBoundToThreeCNF φ)
        ≤ (SAT.ThreeSATEncoding.encodeCNF
          (SAT.CNF.splitAux (cnfStructuredEncodedType.inputSize φ) φ)).length := hStruct
    _ ≤ (SAT.CNF.totalClauseLength φ + φ.length) *
          (1 + 3 * (S + SAT.CNF.totalClauseLength φ + 5)) := by
            simpa [S] using hEncode
    _ ≤ S * (1 + 3 * (S + S + 5)) := by
          have hTotalLe : SAT.CNF.totalClauseLength φ + φ.length ≤ S := by
            simpa [S] using hTotal
          have hFactor :
              1 + 3 * (S + SAT.CNF.totalClauseLength φ + 5) ≤
                1 + 3 * (S + S + 5) := by
            nlinarith [hTotalLe]
          exact Nat.mul_le_mul hTotalLe hFactor
    _ ≤ 1000 * S ^ 2 + 1000 := by
          nlinarith [sq_nonneg (S : Int)]

theorem satisfiabilityStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod cnfStructuredEncodedType SAT.finiteAssignmentCertEncodedType)
      EncodedType.bool
      (fun p : SAT.CNF × List Bool => satisfiabilityStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod cnfStructuredEncodedType SAT.finiteAssignmentCertEncodedType
  have hSplit : TMPolyTimeMap X threeCNFStructuredEncodedType
      (fun p : SAT.CNF × List Bool => cnfSplitFromStructuredBoundToThreeCNF p.1) := by
    have hFst : TMPolyTimeMap X cnfStructuredEncodedType
        (fun p : SAT.CNF × List Bool => p.1) :=
      TMPolyTimeMap.fst cnfStructuredEncodedType SAT.finiteAssignmentCertEncodedType
    have hComp :=
      TMPolyTimeMap.comp cnfSATToThreeSATStructured_tm_polytime hFst
    simpa [Function.comp, X] using hComp
  have hBits : TMPolyTimeMap X SAT.finiteAssignmentCertEncodedType
      (fun p : SAT.CNF × List Bool => p.2) :=
    TMPolyTimeMap.snd cnfStructuredEncodedType SAT.finiteAssignmentCertEncodedType
  have hInput : TMPolyTimeMap X
      (EncodedType.prod threeCNFStructuredEncodedType SAT.finiteAssignmentCertEncodedType)
      (fun p : SAT.CNF × List Bool => (cnfSplitFromStructuredBoundToThreeCNF p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hSplit hBits
  have hComp := TMPolyTimeMap.comp SAT.threeSATStructuredFiniteVerify_tm_polytime hInput
  simpa [Function.comp, satisfiabilityStructuredFiniteVerify, X] using hComp

/-- Direct finite-certificate TM verifier for faithful structured CNF satisfiability. -/
noncomputable def satisfiabilityStructuredFiniteTMVerifier :
    TMVerifier satisfiabilityStructuredDecisionProblem where
  Cert := SAT.finiteAssignmentCertEncodedType
  verify := satisfiabilityStructuredFiniteVerify
  verifier_polytime := satisfiabilityStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨2, 2000, 2000, ?_⟩
    intro φ hSat
    let ψ := cnfSplitFromStructuredBoundToThreeCNF φ
    have hThreeSat : SAT.ThreeCNF.Satisfiable ψ :=
      (cnfSplitFromStructuredBound_satisfiable_iff φ).2 hSat
    rcases hThreeSat with ⟨a, ha⟩
    refine ⟨SAT.assignmentPrefix (SAT.CNF.varBound ψ.clauses) a, ?_, ?_⟩
    · have hCert := SAT.assignmentPrefix_inputSize_le_threeCNFStructured ψ a
      have hSize := cnfSplitFromStructuredBound_threeCNF_inputSize_le φ
      calc
        SAT.finiteAssignmentCertEncodedType.inputSize
            (SAT.assignmentPrefix (SAT.CNF.varBound ψ.clauses) a)
            ≤ 2 * threeCNFStructuredEncodedType.inputSize ψ := hCert
        _ ≤ 2 * (1000 * (cnfStructuredEncodedType.inputSize φ) ^ 2 + 1000) := by
            exact Nat.mul_le_mul_left 2 hSize
        _ ≤ 2000 * (cnfStructuredEncodedType.inputSize φ) ^ 2 + 2000 := by
            nlinarith
    · exact (SAT.threeSATStructuredFiniteVerify_eq_true_iff ψ _).2
        (SAT.ThreeCNF.satisfies_finiteAssignment_prefix ψ a ha)
  sound := by
    intro φ bits hVerify
    let ψ := cnfSplitFromStructuredBoundToThreeCNF φ
    have hThreeSat : SAT.ThreeCNF.Satisfiable ψ :=
      ⟨SAT.finiteAssignment bits,
        (SAT.threeSATStructuredFiniteVerify_eq_true_iff ψ bits).1 hVerify⟩
    exact (cnfSplitFromStructuredBound_satisfiable_iff φ).1 hThreeSat

theorem satisfiabilityStructured_TMInNP :
    TMInNP satisfiabilityStructuredDecisionProblem :=
  TMInNP.intro satisfiabilityStructuredFiniteTMVerifier

/--
Binary-structured 0-1 IP has ordinary direct standard-TM NP membership by
pulling back the binary Knapsack verifier along the direct compact reduction.

This is only ordinary `TMInNP`; it does not provide a packaged Cook-Levin
suffix/raw witness or a packaged completeness source.
-/
theorem zeroOneIPBinaryStructured_TMInNP :
    TMInNP zeroOneIntegerProgrammingBinaryStructuredDecisionProblem :=
  TMInNP.of_reduction
    (A := zeroOneIntegerProgrammingBinaryStructuredDecisionProblem)
    (B := knapsackBinaryStructuredDecisionProblem)
    ⟨Knapsack.zeroOneIPToKnapsackBinaryStructuredTMKarpReduction⟩
    knapsackBinaryStructured_TMInNP

/--
Faithful structured 0-1 IP has ordinary direct standard-TM NP membership by
changing only the numeric encoding to binary and reusing binary-structured
0-1 IP membership.
-/
theorem zeroOneIPStructured_TMInNP :
    TMInNP zeroOneIntegerProgrammingStructuredDecisionProblem :=
  TMInNP.of_reduction
    (A := zeroOneIntegerProgrammingStructuredDecisionProblem)
    (B := zeroOneIntegerProgrammingBinaryStructuredDecisionProblem)
    ⟨ZeroOneIP.zeroOneIPStructuredToBinaryStructuredTMKarpReduction⟩
    zeroOneIPBinaryStructured_TMInNP

/--
Faithful structured Knapsack has ordinary direct standard-TM NP membership by
changing only numeric payloads from unary to binary and reusing the binary
Knapsack verifier.

This is only ordinary `TMInNP`; it does not provide the remaining packaged
hardness source for the unary structured Knapsack root used by Job Sequencing
and Partition.
-/
theorem knapsackStructured_TMInNP :
    TMInNP knapsackStructuredDecisionProblem :=
  TMInNP.of_reduction
    (A := knapsackStructuredDecisionProblem)
    (B := knapsackBinaryStructuredDecisionProblem)
    ⟨Knapsack.knapsackStructuredToBinaryStructuredTMKarpReduction⟩
    knapsackBinaryStructured_TMInNP

end Karp21
end ComplexityReduction
