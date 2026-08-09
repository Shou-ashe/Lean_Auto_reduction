/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Domain.TwoDisjointBoundedPathsMembership

/-!
Exact public formalization and single-gap native-membership authoring input
for the UIUC 2020 Two Disjoint Bounded Paths qualifying-exam problem.

The production registry supplies the independent binary-Partition lower-bound
edge.  This module exposes only the exact pair-of-path certificate, binary-cost,
and edge-disjointness membership template.
-/

namespace Benchmark.Hardness.Inputs.Quals.UIUC2020TwoDisjointBoundedPaths

open ComplexityReduction
open ComplexityReduction.Encoding

@[complexity_reduction_ir_typed_problem]
abbrev problem : PresentedProblem :=
  ComplexityReduction.Presentation.TwoDisjointBoundedPaths.presentedProblem

abbrev source : PresentedProblem := problem

theorem problem_accepts_iff (input : problem.Instance) :
    problem.accepts input ↔
      ComplexityReduction.Presentation.TwoDisjointBoundedPaths.IsYes input :=
  Iff.rfl

assert_standard_axioms problem_accepts_iff

end Benchmark.Hardness.Inputs.Quals.UIUC2020TwoDisjointBoundedPaths
