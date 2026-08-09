/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Presentation.ExactlyOneNeighbor

/-!
Fail-closed Spring 2015 Exactly-One-Neighbor variant with the exact public
presentation but without importing the Optional Authoring membership template.

The production lower-bound route remains discoverable through the hardness
runtime.  This module contributes no native membership, completeness theorem,
authoring template, oracle, or alternate endpoint.
-/

namespace Benchmark.Hardness.Inputs.Quals.Spring2015ExactlyOneNeighborMissingMembership

open ComplexityReduction
open ComplexityReduction.Encoding

@[complexity_reduction_ir_typed_problem]
abbrev problem : PresentedProblem :=
  ComplexityReduction.Presentation.ExactlyOneNeighbor.presentedProblem

theorem problem_accepts_iff (input : problem.Instance) :
    problem.accepts input ↔
      ∃ selected : List Nat,
        ComplexityReduction.ExactlyOneNeighborWitness input selected :=
  Iff.rfl

assert_standard_axioms problem_accepts_iff

end Benchmark.Hardness.Inputs.Quals.Spring2015ExactlyOneNeighborMissingMembership
