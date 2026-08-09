/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Presentation.NodeDeletionBipartite

/-!
Capability-negative Fall 2016 Node Deletion to Bipartite input.

The exact public endpoint and its production lower-bound route remain
available through the hardness runtime, but this module deliberately omits
the native-membership template.  Core must report the membership blocker and
must not invoke Optional Authoring or a model.
-/

namespace Benchmark.Hardness.Inputs.Quals.Fall2016NodeDeletionBipartiteMissingMembership

open ComplexityReduction
open ComplexityReduction.Encoding

@[complexity_reduction_ir_typed_problem]
abbrev problem : PresentedProblem :=
  ComplexityReduction.Presentation.NodeDeletionBipartite.presentedProblem

theorem problem_accepts_iff (input : problem.Instance) :
    problem.accepts input ↔
      ComplexityReduction.Presentation.NodeDeletionBipartite.IsYes input :=
  Iff.rfl

assert_standard_axioms problem_accepts_iff

end Benchmark.Hardness.Inputs.Quals.Fall2016NodeDeletionBipartiteMissingMembership
