/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Domain.MostNeighborsMembership

/-!
Exact public formalization and single-gap native-membership authoring input
for the Fall 2014 Most Neighbors qualifying-exam problem.

The production registry supplies the independently audited Clique lower-bound
edge.  This module exposes only the exact finite external-neighborhood witness
template needed to close the remaining NP-completeness gap.
-/

namespace Benchmark.Hardness.Inputs.Quals.Fall2014MostNeighbors

open ComplexityReduction
open ComplexityReduction.Encoding

@[complexity_reduction_ir_typed_problem]
abbrev problem : PresentedProblem :=
  ComplexityReduction.Presentation.MostNeighbors.presentedProblem

abbrev source : PresentedProblem := problem

theorem problem_accepts_iff (input : problem.Instance) :
    problem.accepts input ↔
      ComplexityReduction.Presentation.MostNeighbors.IsYes input :=
  Iff.rfl

assert_standard_axioms problem_accepts_iff

end Benchmark.Hardness.Inputs.Quals.Fall2014MostNeighbors
