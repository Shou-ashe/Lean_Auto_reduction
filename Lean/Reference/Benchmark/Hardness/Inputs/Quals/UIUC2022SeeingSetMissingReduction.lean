/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Presentation.SeeingSet
import ComplexityReduction.Presentation.SetSystem

/-!
Capability-negative UIUC Spring 2022 Seeing Set input.

The exact source and target presentations are present, but this module does
not import the public Set-Covering gadget template and contributes no route,
oracle, authoring packet, or alternate endpoint.  Core must therefore stop at
the missing forward reduction before any model call.
-/

namespace Benchmark.Hardness.Inputs.Quals.UIUC2022SeeingSetMissingReduction

open ComplexityReduction
open ComplexityReduction.Encoding

@[complexity_reduction_ir_typed_problem]
abbrev source : PresentedProblem :=
  ComplexityReduction.Presentation.SetSystem.setCoveringStructuredProblem

@[complexity_reduction_ir_typed_problem]
abbrev target : PresentedProblem :=
  ComplexityReduction.Presentation.SeeingSet.presentedProblem

theorem target_accepts_iff (input : target.Instance) :
    target.accepts input ↔
      ComplexityReduction.Presentation.SeeingSet.IsYes input :=
  Iff.rfl

assert_standard_axioms target_accepts_iff

end Benchmark.Hardness.Inputs.Quals.UIUC2022SeeingSetMissingReduction
