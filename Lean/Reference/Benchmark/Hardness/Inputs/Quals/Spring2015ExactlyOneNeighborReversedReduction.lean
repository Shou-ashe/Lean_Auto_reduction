/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Benchmark.Hardness.Inputs.Quals.Spring2015ExactlyOneNeighborMissingMembership
import ComplexityReduction.AxiomGate
import ComplexityReduction.Routes.FiniteDomainCSP.Unified

/-!
Direction-negative variant for the Spring 2015 pilot.

The imported public certificate has type `structured CNF → existential EON`.
The benchmark request deliberately asks for `existential EON → structured
CNF`.  No equivalence or reverse certificate is declared here, so the Core must
not reuse the one-way theorem backwards.
-/

namespace Benchmark.Hardness.Inputs.Quals.Spring2015ExactlyOneNeighborReversedReduction

open ComplexityReduction
open ComplexityReduction.Certificate
open ComplexityReduction.Encoding

@[complexity_reduction_ir_typed_problem]
abbrev source : PresentedProblem :=
  Benchmark.Hardness.Inputs.Quals.Spring2015ExactlyOneNeighborMissingMembership.problem

@[complexity_reduction_ir_typed_problem]
abbrev target : PresentedProblem :=
  ComplexityReduction.Routes.FiniteDomainCSP.clauseCNFTargetProblem

/-- The only frozen EON/CNF edge has the opposite direction from the request. -/
noncomputable def forwardOnly : CertifiedReduction target source := by
  simpa [source, target,
    Benchmark.Hardness.Inputs.Quals.Spring2015ExactlyOneNeighborMissingMembership.problem,
    ComplexityReduction.Routes.FiniteDomainCSP.existentialEONTargetProblem] using
      ComplexityReduction.Routes.FiniteDomainCSP.clauseToExistentialEON

assert_standard_axioms forwardOnly

end Benchmark.Hardness.Inputs.Quals.Spring2015ExactlyOneNeighborReversedReduction
