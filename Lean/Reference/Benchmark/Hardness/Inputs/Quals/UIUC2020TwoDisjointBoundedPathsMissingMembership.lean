/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Presentation.TwoDisjointBoundedPaths

/-!
Capability-negative UIUC 2020 Two Disjoint Bounded Paths input.

The exact endpoint and registered production lower-bound remain available,
but the pair-of-path native-membership template is intentionally absent.
Core must report the exact membership blocker without a model call.
-/

namespace Benchmark.Hardness.Inputs.Quals.UIUC2020TwoDisjointBoundedPathsMissingMembership

open ComplexityReduction
open ComplexityReduction.Encoding

@[complexity_reduction_ir_typed_problem]
abbrev problem : PresentedProblem :=
  ComplexityReduction.Presentation.TwoDisjointBoundedPaths.presentedProblem

theorem problem_accepts_iff (input : problem.Instance) :
    problem.accepts input ↔
      ComplexityReduction.Presentation.TwoDisjointBoundedPaths.IsYes input :=
  Iff.rfl

assert_standard_axioms problem_accepts_iff

end Benchmark.Hardness.Inputs.Quals.UIUC2020TwoDisjointBoundedPathsMissingMembership
