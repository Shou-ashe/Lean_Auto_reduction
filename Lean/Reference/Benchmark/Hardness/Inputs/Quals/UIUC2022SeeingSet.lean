/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Domain.SetCoveringToSeeingSet

/-!
Exact public formalization and single-gap reduction-authoring input for the
UIUC Spring 2022 Seeing Set qualifying-exam problem.

The public input fixes only the exact finite Seeing Set endpoint.  The
Set-Covering gadget is exposed as a typed program-indexed template, not as a
registered reduction edge, so Optional Authoring must close precisely that
lower-bound gap.  No membership or completeness claim is made for this case.
-/

namespace Benchmark.Hardness.Inputs.Quals.UIUC2022SeeingSet

open ComplexityReduction
open ComplexityReduction.Encoding

/-- Exact public Seeing Set endpoint. -/
@[complexity_reduction_ir_typed_problem]
abbrev problem : PresentedProblem :=
  ComplexityReduction.Presentation.SeeingSet.presentedProblem

/-- Public source endpoint used only by the `reduce_to` hardness request. -/
@[complexity_reduction_ir_typed_problem]
abbrev source : PresentedProblem :=
  ComplexityReduction.Domain.SetCoveringToSeeingSet.source

/-- The fixed reduction target is definitionally the public exam endpoint. -/
@[complexity_reduction_ir_typed_problem]
abbrev target : PresentedProblem := problem

/-- The benchmark predicate is exactly the finite directed weighted semantics. -/
theorem problem_accepts_iff (input : problem.Instance) :
    problem.accepts input ↔
      ComplexityReduction.Presentation.SeeingSet.IsYes input :=
  Iff.rfl

assert_standard_axioms problem_accepts_iff

end Benchmark.Hardness.Inputs.Quals.UIUC2022SeeingSet
