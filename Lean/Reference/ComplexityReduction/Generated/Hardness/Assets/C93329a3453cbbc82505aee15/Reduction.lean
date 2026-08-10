/-
H-K shadow publication candidate.  This module contains only the
model-authored reduction DAG and runner-owned CertifiedReduction.
It intentionally provides no native hardness theorem.
-/

import ComplexityReduction.Routes.ThreeSATToClique.IngressAdapters
import ComplexityReduction.Problems.Karp21.Satisfiability
import ComplexityReduction.Certificate.Reduction
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.AxiomGate

namespace ComplexityReduction.Generated.Hardness.Ce9751f385584594e3ba9.Reduction

open ComplexityReduction
open ComplexityReduction.Certificate
open ComplexityReduction.Encoding
open ComplexityReduction.Program
open ComplexityReduction.Problems.Karp21.Satisfiability
open ComplexityReduction.Routes.ThreeSATToClique.IngressAdapters

noncomputable def representationAdapter :
    ComplexityReduction.Program.PolyProg   ComplexityReduction.Problems.Karp21.Satisfiability.threeSATStructuredProblem.representation   ComplexityReduction.Routes.ThreeSATToClique.IngressAdapters.taggedThreeSATProblem.representation :=
  by
    exact (ComplexityReduction.Program.PolyProg.const       ComplexityReduction.Problems.Karp21.Satisfiability.threeSATStructuredProblem.representation       ComplexityReduction.Encoding.StandardInstances.bool Bool.false).pair   (ComplexityReduction.Program.PolyProg.id     ComplexityReduction.Problems.Karp21.Satisfiability.threeSATStructuredProblem.representation)

noncomputable def semanticForward :
    ∀ input : ComplexityReduction.Problems.Karp21.Satisfiability.threeSATStructuredProblem.Instance, ComplexityReduction.Problems.Karp21.Satisfiability.threeSATStructuredProblem.accepts input → ComplexityReduction.Routes.ThreeSATToClique.IngressAdapters.taggedThreeSATProblem.accepts (ComplexityReduction.Generated.Hardness.Ce9751f385584594e3ba9.Reduction.representationAdapter.run input) :=
  by
    intro input accepted
    exact accepted

noncomputable def semanticReverse :
    ∀ input : ComplexityReduction.Problems.Karp21.Satisfiability.threeSATStructuredProblem.Instance, ComplexityReduction.Routes.ThreeSATToClique.IngressAdapters.taggedThreeSATProblem.accepts (ComplexityReduction.Generated.Hardness.Ce9751f385584594e3ba9.Reduction.representationAdapter.run input) → ComplexityReduction.Problems.Karp21.Satisfiability.threeSATStructuredProblem.accepts input :=
  by
    intro input accepted
    exact accepted

noncomputable def semanticCorrect :
    ∀ input : ComplexityReduction.Problems.Karp21.Satisfiability.threeSATStructuredProblem.Instance, ComplexityReduction.Problems.Karp21.Satisfiability.threeSATStructuredProblem.accepts input ↔ ComplexityReduction.Routes.ThreeSATToClique.IngressAdapters.taggedThreeSATProblem.accepts (ComplexityReduction.Generated.Hardness.Ce9751f385584594e3ba9.Reduction.representationAdapter.run input) :=
  by
    intro input
    exact ⟨ComplexityReduction.Generated.Hardness.Ce9751f385584594e3ba9.Reduction.semanticForward input, ComplexityReduction.Generated.Hardness.Ce9751f385584594e3ba9.Reduction.semanticReverse input⟩

@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def authoredForwardReduction :
    ComplexityReduction.Certificate.CertifiedReduction ComplexityReduction.Problems.Karp21.Satisfiability.threeSATStructuredProblem ComplexityReduction.Routes.ThreeSATToClique.IngressAdapters.taggedThreeSATProblem where
  program := ComplexityReduction.Generated.Hardness.Ce9751f385584594e3ba9.Reduction.representationAdapter
  correct := ComplexityReduction.Generated.Hardness.Ce9751f385584594e3ba9.Reduction.semanticCorrect

end ComplexityReduction.Generated.Hardness.Ce9751f385584594e3ba9.Reduction

assert_standard_axioms
  ComplexityReduction.Generated.Hardness.Ce9751f385584594e3ba9.Reduction.representationAdapter,
  ComplexityReduction.Generated.Hardness.Ce9751f385584594e3ba9.Reduction.semanticForward,
  ComplexityReduction.Generated.Hardness.Ce9751f385584594e3ba9.Reduction.semanticReverse,
  ComplexityReduction.Generated.Hardness.Ce9751f385584594e3ba9.Reduction.semanticCorrect,
  ComplexityReduction.Generated.Hardness.Ce9751f385584594e3ba9.Reduction.authoredForwardReduction
