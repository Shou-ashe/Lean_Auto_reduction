/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Benchmark.Hardness.Inputs.Quals.Spring2015ExactlyOneNeighbor
import ComplexityReduction.AxiomGate

/-!
Exact-endpoint negative for the Spring 2015 pilot.

This module intentionally imports the valid public EON membership template,
then defines a different semantic problem at the same lawful representation.
The exact template is indexed by the production existential EON endpoint and
must not be admitted for this always-false endpoint merely because the carrier
and codec agree.
-/

namespace Benchmark.Hardness.Inputs.Quals.Spring2015ExactlyOneNeighborWrongEndpoint

open ComplexityReduction
open ComplexityReduction.Encoding

private def wrongSemantic : ComplexityReduction.DecisionProblem where
  Instance :=
    Benchmark.Hardness.Inputs.Quals.Spring2015ExactlyOneNeighbor.problem.Instance
  isYes := fun _ => False

@[complexity_reduction_ir_typed_problem]
def problem : PresentedProblem where
  semantic := wrongSemantic
  representation :=
    Benchmark.Hardness.Inputs.Quals.Spring2015ExactlyOneNeighbor.problem.representation
  carrier_eq := rfl

@[simp] theorem problem_accepts_iff_false (input : problem.Instance) :
    problem.accepts input ↔ False :=
  Iff.rfl

assert_standard_axioms problem, problem_accepts_iff_false

end Benchmark.Hardness.Inputs.Quals.Spring2015ExactlyOneNeighborWrongEndpoint
