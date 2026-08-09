/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Certificate.Reduction
import ComplexityReduction.Certificate.VerifierEncodingDiscipline

/-!
Strict V2-native NP-completeness.

This predicate combines native membership at one exact `PresentedProblem` with
hardness witnessed only by exact `CertifiedReduction` values.  Backend
`TMInNP` and legacy/backend completeness declarations do not appear in its
fields and therefore cannot be reclassified as native completeness by this
API.
-/

namespace ComplexityReduction
namespace Certificate

open Encoding

/--
V2-native NP-hardness at one exact presented endpoint.

The proposition retains the same exact source/target indices and program-backed
`CertifiedReduction` witness used by native completeness, but deliberately does
not claim target membership.  This lets target discovery distinguish a hard
endpoint from a complete endpoint instead of manufacturing `NativeTMInNP`.
-/
def NativeTMNPHard (problem : PresentedProblem) : Prop :=
  ∀ source : PresentedProblem,
    NativeTMInNP source → Nonempty (CertifiedReduction source problem)

/--
V2-native NP-completeness for one exact presented problem.

Every native source problem is reduced by a `CertifiedReduction` whose program,
semantic correctness, and compiler-derived complexity evidence are indexed by
that exact source and this exact target.  The `Nonempty` wrapper keeps the
completeness statement in `Prop` without offering an untyped route extractor.
-/
structure NativeTMNPComplete (problem : PresentedProblem) : Prop where
  membership : NativeTMInNP problem
  hardness : ∀ source : PresentedProblem,
    NativeTMInNP source → Nonempty (CertifiedReduction source problem)

namespace NativeTMNPComplete

/-- The native membership component remains indexed by the exact complete problem. -/
theorem nativeMembership {problem : PresentedProblem} (complete : NativeTMNPComplete problem) :
    NativeTMInNP problem :=
  complete.membership

/-- Exact native completeness exposes its hardness component without adding membership elsewhere. -/
theorem nativeHardness {problem : PresentedProblem} (complete : NativeTMNPComplete problem) :
    NativeTMNPHard problem :=
  complete.hardness

/-- The hardness component returns only a program-indexed certificate at exact endpoints. -/
theorem certifiedHardness {problem source : PresentedProblem} (complete : NativeTMNPComplete problem)
    (sourceMembership : NativeTMInNP source) :
    Nonempty (CertifiedReduction source problem) :=
  complete.hardness source sourceMembership

/--
Eliminating native hardness into `Prop` exposes one exact certificate whose
semantic and direct-TM evidence are both indexed by its stored program.

This is a projection of an already supplied completeness value.  It does not
construct hardness from backend completeness, membership, metadata, or a
separate machine/cost witness.
-/
theorem certifiedHardness_exactProgramEvidence {problem source : PresentedProblem}
    (complete : NativeTMNPComplete problem) (sourceMembership : NativeTMInNP source) :
    ∃ reduction : CertifiedReduction source problem,
      (∀ input, source.accepts input ↔ problem.accepts (reduction.program.run input)) ∧
        reduction.directTM = reduction.program.compileTM := by
  rcases complete.certifiedHardness sourceMembership with ⟨reduction⟩
  exact ⟨reduction, reduction.correct, CertifiedReduction.directTM_eq_compileTM reduction⟩

/--
Every native-completeness value decomposes into exact native membership and
hardness evidence for every exact native source.  Each returned hardness
certificate keeps semantic execution and compiled direct-TM evidence tied to
the same `PolyProg` at the source and target indices.
-/
theorem exactEvidenceDecomposition {problem : PresentedProblem}
    (complete : NativeTMNPComplete problem) :
    NativeTMInNP problem ∧
      ∀ source : PresentedProblem, NativeTMInNP source →
        ∃ reduction : CertifiedReduction source problem,
          (∀ input, source.accepts input ↔ problem.accepts (reduction.program.run input)) ∧
            reduction.directTM = reduction.program.compileTM := by
  refine ⟨complete.nativeMembership, ?_⟩
  intro source sourceMembership
  exact complete.certifiedHardness_exactProgramEvidence sourceMembership

end NativeTMNPComplete

end Certificate
end ComplexityReduction
