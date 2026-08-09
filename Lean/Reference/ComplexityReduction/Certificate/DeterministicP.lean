/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Program.CompileTM
import ComplexityReduction.Encoding.PresentedProblem

/-!
V2-native deterministic polynomial-time evidence at an exact presentation.

The executable is a `PolyProg`, so its direct-TM polynomial-time evidence is
derived by compilation and cannot be supplied for a different function.  The
semantic field binds that exact executable to the exact `PresentedProblem`.
-/

namespace ComplexityReduction
namespace Certificate

open Encoding Program

/-- An exact polynomial-time decision algorithm for one presented problem. -/
structure CertifiedPAlgorithm (problem : PresentedProblem) where
  program : PolyProg problem.representation StandardInstances.bool
  correct : ∀ input, program.run input = true ↔ problem.accepts input

namespace CertifiedPAlgorithm

/-- Execute the certificate's exact program. -/
def decide {problem : PresentedProblem} (algorithm : CertifiedPAlgorithm problem) :
    problem.Instance → Bool :=
  algorithm.program.run

/-- Polynomial time is compiler-derived for the same executable program. -/
theorem polytime {problem : PresentedProblem} (algorithm : CertifiedPAlgorithm problem) :
    ComplexityReduction.TMPolyTimeMap problem.representation.encodedType
      ComplexityReduction.EncodedType.bool algorithm.decide := by
  simpa [decide, Encoding.StandardInstances.bool_encodedType] using algorithm.program.compileTM

/-- The public decider agrees exactly with the problem predicate. -/
theorem decide_correct {problem : PresentedProblem} (algorithm : CertifiedPAlgorithm problem)
    (input : problem.Instance) :
    algorithm.decide input = true ↔ problem.accepts input :=
  algorithm.correct input

end CertifiedPAlgorithm

/-- Native membership in P is nonempty exact algorithm evidence. -/
def NativeTMInP (problem : PresentedProblem) : Prop :=
  Nonempty (CertifiedPAlgorithm problem)

namespace NativeTMInP

/-- Introduce P membership only from a complete exact algorithm certificate. -/
theorem ofAlgorithm {problem : PresentedProblem} (algorithm : CertifiedPAlgorithm problem) :
    NativeTMInP problem :=
  ⟨algorithm⟩

/-- Eliminate P membership inside `Prop` through its exact algorithm. -/
theorem exactAlgorithm {problem : PresentedProblem} (membership : NativeTMInP problem)
    {motive : Prop} (use : CertifiedPAlgorithm problem → motive) : motive := by
  rcases membership with ⟨algorithm⟩
  exact use algorithm

end NativeTMInP

end Certificate
end ComplexityReduction
