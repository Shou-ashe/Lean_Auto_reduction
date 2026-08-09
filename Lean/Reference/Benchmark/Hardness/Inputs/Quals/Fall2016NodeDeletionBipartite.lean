/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Domain.NodeDeletionBipartiteMembership

/-!
Exact public formalization and single-gap native-membership authoring input
for the Fall 2016 Node Deletion to Bipartite qualifying-exam problem.

The production registry supplies the independent Clique lower-bound edge.
This module exposes only the exact finite-witness membership template needed
to close the remaining NP-completeness gap.
-/

namespace Benchmark.Hardness.Inputs.Quals.Fall2016NodeDeletionBipartite

open ComplexityReduction
open ComplexityReduction.Encoding

@[complexity_reduction_ir_typed_problem]
abbrev problem : PresentedProblem :=
  ComplexityReduction.Presentation.NodeDeletionBipartite.presentedProblem

abbrev source : PresentedProblem := problem

/-- The benchmark predicate is exactly deletion plus total Boolean coloring. -/
theorem problem_accepts_iff (input : problem.Instance) :
    problem.accepts input ↔
      ComplexityReduction.Presentation.NodeDeletionBipartite.IsYes input :=
  Iff.rfl

assert_standard_axioms problem_accepts_iff

end Benchmark.Hardness.Inputs.Quals.Fall2016NodeDeletionBipartite
