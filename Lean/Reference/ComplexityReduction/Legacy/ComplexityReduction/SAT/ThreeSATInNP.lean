/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Certificates.CostedMap
import ComplexityReduction.Legacy.ComplexityReduction.Core.NPClass
import ComplexityReduction.Legacy.ComplexityReduction.SAT.ThreeSAT

/-!
NP membership for the standard local 3SAT target.

This module belongs to the reusable SAT layer: it exposes the bundled local
3CNF satisfiability verifier and packages it as a local Cook-Levin-backed
`InNPEnc` witness using the identity 3SAT map.
-/

namespace ComplexityReduction
namespace SAT

noncomputable section

/-- Direct NP verifier for the local bundled 3SAT decision problem. -/
def threeSATVerifier : NPVerifier CostedPolyTimeModel threeSATDecisionProblem where
  Cert := EncodedType.raw Assignment
  verify := fun φ a => by
    classical
    exact if φ.Satisfies a then true else false
  verifier_polytime := by
    refine CostedPolyTimeMap.of_costed (CostedMap.of_encodedPolynomialSizeBound ?_)
    exact PolynomialSizeBound.const 1 (by
      intro p
      simp [EncodedType.inputSize, EncodedType.bool])
  cert_bound := by
    refine ⟨0, 0, 0, ?_⟩
    intro φ hφ
    change ThreeCNF.Satisfiable φ at hφ
    rcases hφ with ⟨a, ha⟩
    refine ⟨a, ?_, ?_⟩
    · simp [EncodedType.inputSize, EncodedType.raw]
    · simp [ha]
  sound := by
    intro φ a h
    by_cases hs : φ.Satisfies a
    · exact ⟨a, hs⟩
    · simp [hs] at h

/-- Local Cook-Levin-backed witness for the bundled 3SAT decision problem. -/
def threeSATLocalVerifier : LocalNPVerifier CostedPolyTimeModel threeSATDecisionProblem where
  verifier := threeSATVerifier
  cookTableauThreeCNF := id
  cookTableauThreeCNF_polytime := CostedPolyTimeModel.id_map
  cookTableauThreeCNF_correct := by
    intro φ
    exact Iff.rfl

/-- Local 3SAT belongs to encoded NP under the costed model. -/
theorem threeSAT_inNP : InNPEnc CostedPolyTimeModel threeSATDecisionProblem :=
  InNPEnc.intro threeSATLocalVerifier

end

end SAT
end ComplexityReduction
