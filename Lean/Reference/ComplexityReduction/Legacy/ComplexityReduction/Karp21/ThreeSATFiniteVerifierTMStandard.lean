/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeSATFiniteVerifierTMFormula
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeSATStandardParserTM

/-!
Standard bundled-3SAT finite verifier bridge surface.

The executable verifier is the same CNF runner built for the faithful structured
syntax, applied to the bundled formula's clause field.  The remaining direct-TM
bridge is the parser/projection from the historical flat `ThreeSATEncoding`
stream to `cnfStructuredEncodedType`; `ThreeSATStandardParserTM` supplies that
witness directly.
-/

namespace ComplexityReduction
namespace SAT

open ComplexityReduction.Karp21

/-! ### Executable verifier over the standard bundled 3SAT carrier -/

/-- Executable finite-certificate verifier over the standard bundled 3SAT carrier. -/
def threeSATFiniteVerifyExecutable (φ : ThreeCNF) (bits : List Bool) : Bool :=
  cnfFiniteEvalBool (bits, φ.clauses)

theorem threeSATFiniteVerifyExecutable_eq_true_iff (φ : ThreeCNF) (bits : List Bool) :
    threeSATFiniteVerifyExecutable φ bits = true ↔
      φ.Satisfies (finiteAssignment bits) := by
  simpa [threeSATFiniteVerifyExecutable, ThreeCNF.Satisfies] using
    cnfFiniteEvalBool_eq_true_iff bits φ.clauses

theorem threeSATFiniteVerifyExecutable_eq_threeSATFiniteVerify
    (φ : ThreeCNF) (bits : List Bool) :
    threeSATFiniteVerifyExecutable φ bits = threeSATFiniteVerify φ bits := by
  by_cases hSat : φ.Satisfies (finiteAssignment bits)
  · rw [(threeSATFiniteVerifyExecutable_eq_true_iff φ bits).2 hSat,
      (threeSATFiniteVerify_eq_true_iff φ bits).2 hSat]
  · have hExecFalse : threeSATFiniteVerifyExecutable φ bits = false :=
      Bool.eq_false_iff.mpr (by
        intro hExec
        exact hSat ((threeSATFiniteVerifyExecutable_eq_true_iff φ bits).1 hExec))
    have hSemanticFalse : threeSATFiniteVerify φ bits = false :=
      Bool.eq_false_iff.mpr (by
        intro hVerify
        exact hSat ((threeSATFiniteVerify_eq_true_iff φ bits).1 hVerify))
    rw [hExecFalse, hSemanticFalse]

/-! ### Standard verifier assembly from the pending parser/projection witness -/

/-- Standard bundled 3SAT verifier input: a formula and a finite Boolean certificate. -/
abbrev standardThreeSATFiniteVerifierInputEncodedType : EncodedType :=
  EncodedType.prod threeSATDecisionProblem.Instance finiteAssignmentCertEncodedType

/--
If the historical bundled 3SAT encoding can directly project to the faithful
structured CNF payload, the executable finite verifier is a direct TM map.
-/
theorem threeSATFiniteVerifyExecutable_tm_polytime_of_clauses_projection
    (hClauses :
      TMPolyTimeMap
        threeSATDecisionProblem.Instance
        Karp21.cnfStructuredEncodedType
        (fun φ : ThreeCNF => φ.clauses)) :
    TMPolyTimeMap
      standardThreeSATFiniteVerifierInputEncodedType
      EncodedType.bool
      (fun p : ThreeCNF × List Bool => threeSATFiniteVerifyExecutable p.1 p.2) := by
  let X := standardThreeSATFiniteVerifierInputEncodedType
  have hFormula : TMPolyTimeMap X threeSATDecisionProblem.Instance
      (fun p : ThreeCNF × List Bool => p.1) := by
    simpa [X, standardThreeSATFiniteVerifierInputEncodedType] using
      TMPolyTimeMap.fst threeSATDecisionProblem.Instance finiteAssignmentCertEncodedType
  have hBits : TMPolyTimeMap X finiteAssignmentCertEncodedType
      (fun p : ThreeCNF × List Bool => p.2) := by
    simpa [X, standardThreeSATFiniteVerifierInputEncodedType] using
      TMPolyTimeMap.snd threeSATDecisionProblem.Instance finiteAssignmentCertEncodedType
  have hFormulaClauses : TMPolyTimeMap X Karp21.cnfStructuredEncodedType
      (fun p : ThreeCNF × List Bool => p.1.clauses) := by
    have hComp := TMPolyTimeMap.comp hClauses hFormula
    simpa [Function.comp, X] using hComp
  have hInput : TMPolyTimeMap X cnfFiniteEvalInputEncodedType
      (fun p : ThreeCNF × List Bool => (p.2, p.1.clauses)) :=
    TMPolyTimeMap.prod_mk hBits hFormulaClauses
  have hComp := TMPolyTimeMap.comp cnfFiniteEvalBool_tm_polytime hInput
  simpa [Function.comp, threeSATFiniteVerifyExecutable, cnfFiniteEvalInputEncodedType, X]
    using hComp

/--
The standard finite-certificate TM verifier, conditional only on the direct
historical-encoding-to-structured-CNF projection witness.
-/
noncomputable def threeSATFiniteTMVerifier_of_clauses_projection
    (hClauses :
      TMPolyTimeMap
        threeSATDecisionProblem.Instance
        Karp21.cnfStructuredEncodedType
        (fun φ : ThreeCNF => φ.clauses)) :
    TMVerifier threeSATDecisionProblem where
  Cert := finiteAssignmentCertEncodedType
  verify := threeSATFiniteVerifyExecutable
  verifier_polytime :=
    threeSATFiniteVerifyExecutable_tm_polytime_of_clauses_projection hClauses
  cert_bound := by
    refine ⟨1, 2, 0, ?_⟩
    intro φ hSat
    change φ.Satisfiable at hSat
    rcases hSat with ⟨a, ha⟩
    refine ⟨assignmentPrefix (CNF.varBound φ.clauses) a, ?_, ?_⟩
    · simpa using assignmentPrefix_inputSize_le_formula φ a
    · exact (threeSATFiniteVerifyExecutable_eq_true_iff φ _).2
        (ThreeCNF.satisfies_finiteAssignment_prefix φ a ha)
  sound := by
    intro φ bits hVerify
    change φ.Satisfiable
    exact ⟨finiteAssignment bits,
      (threeSATFiniteVerifyExecutable_eq_true_iff φ bits).1 hVerify⟩

theorem threeSAT_TMInNP_of_clauses_projection
    (hClauses :
      TMPolyTimeMap
        threeSATDecisionProblem.Instance
        Karp21.cnfStructuredEncodedType
        (fun φ : ThreeCNF => φ.clauses)) :
    TMInNP threeSATDecisionProblem :=
  TMInNP.intro (threeSATFiniteTMVerifier_of_clauses_projection hClauses)

/-! ### Unconditional standard bundled-3SAT verifier surface -/

theorem threeSATFiniteVerifyExecutable_tm_polytime :
    TMPolyTimeMap
      standardThreeSATFiniteVerifierInputEncodedType
      EncodedType.bool
      (fun p : ThreeCNF × List Bool => threeSATFiniteVerifyExecutable p.1 p.2) :=
  threeSATFiniteVerifyExecutable_tm_polytime_of_clauses_projection
    standardThreeSATClauses_tm_polytime

noncomputable def threeSATFiniteTMVerifier :
    TMVerifier threeSATDecisionProblem :=
  threeSATFiniteTMVerifier_of_clauses_projection
    standardThreeSATClauses_tm_polytime

theorem threeSAT_TMInNP :
    TMInNP threeSATDecisionProblem :=
  threeSAT_TMInNP_of_clauses_projection
    standardThreeSATClauses_tm_polytime

end SAT
end ComplexityReduction
