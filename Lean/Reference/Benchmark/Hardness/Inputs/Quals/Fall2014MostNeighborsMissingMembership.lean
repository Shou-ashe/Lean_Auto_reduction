/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Presentation.MostNeighbors

/-!
Capability-negative Fall 2014 Most Neighbors input.

The exact endpoint and registered production lower-bound remain available,
but this module deliberately omits the native external-neighborhood witness
template.  Core must stop at exact target membership before any model call.
-/

namespace Benchmark.Hardness.Inputs.Quals.Fall2014MostNeighborsMissingMembership

open ComplexityReduction
open ComplexityReduction.Encoding

@[complexity_reduction_ir_typed_problem]
abbrev problem : PresentedProblem :=
  ComplexityReduction.Presentation.MostNeighbors.presentedProblem

theorem problem_accepts_iff (input : problem.Instance) :
    problem.accepts input ↔
      ComplexityReduction.Presentation.MostNeighbors.IsYes input :=
  Iff.rfl

assert_standard_axioms problem_accepts_iff

end Benchmark.Hardness.Inputs.Quals.Fall2014MostNeighborsMissingMembership
