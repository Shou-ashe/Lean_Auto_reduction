/-
H-K shadow publication candidate.  This module contains only the
model-authored reduction DAG and runner-owned CertifiedReduction.
It intentionally provides no native hardness theorem.
-/

import ComplexityReduction.Presentation.ThreeDimensionalMatching
import ComplexityReduction.Presentation.SetSystem
import ComplexityReduction.Agent.Hardness.AuthoringSources
import ComplexityReduction.Certificate.Reduction
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.AxiomGate

namespace ComplexityReduction.Generated.Hardness.C4ddadc69d69dcce12634.Reduction

open ComplexityReduction
open ComplexityReduction.Certificate
open ComplexityReduction.Encoding
open ComplexityReduction.Program
open ComplexityReduction.Presentation.SetSystem
open ComplexityReduction.Presentation.ThreeDimensionalMatching

noncomputable def tmKarpPrimitive :
    ComplexityReduction.Program.Primitive ComplexityReduction.Presentation.SetSystem.exactCoverStructuredProblem.representation ComplexityReduction.Presentation.ThreeDimensionalMatching.structuredProblem.representation :=
  by
    exact Primitive.ofTMPolyTime ComplexityReduction.Agent.Hardness.AuthoringSources.exactCoverToThreeDimensionalMatchingTMKarpReduction.f ComplexityReduction.Agent.Hardness.AuthoringSources.exactCoverToThreeDimensionalMatchingTMKarpReduction.polytime

noncomputable def tmKarpProgram :
    ComplexityReduction.Program.PolyProg ComplexityReduction.Presentation.SetSystem.exactCoverStructuredProblem.representation ComplexityReduction.Presentation.ThreeDimensionalMatching.structuredProblem.representation :=
  by
    exact PolyProg.atom ComplexityReduction.Generated.Hardness.C4ddadc69d69dcce12634.Reduction.tmKarpPrimitive

noncomputable def tmKarpSemanticCorrect :
    ∀ input : ComplexityReduction.Presentation.SetSystem.exactCoverStructuredProblem.Instance, ComplexityReduction.Presentation.SetSystem.exactCoverStructuredProblem.accepts input ↔ ComplexityReduction.Presentation.ThreeDimensionalMatching.structuredProblem.accepts (ComplexityReduction.Generated.Hardness.C4ddadc69d69dcce12634.Reduction.tmKarpProgram.run input) :=
  by
    intro input
    simpa only [ComplexityReduction.Generated.Hardness.C4ddadc69d69dcce12634.Reduction.tmKarpProgram, ComplexityReduction.Generated.Hardness.C4ddadc69d69dcce12634.Reduction.tmKarpPrimitive, PolyProg.run_atom, Primitive.run_ofTMPolyTime] using
      ComplexityReduction.Agent.Hardness.AuthoringSources.exactCoverToThreeDimensionalMatchingTMKarpReduction.correct input

@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def authoredForwardReduction :
    ComplexityReduction.Certificate.CertifiedReduction ComplexityReduction.Presentation.SetSystem.exactCoverStructuredProblem ComplexityReduction.Presentation.ThreeDimensionalMatching.structuredProblem where
  program := ComplexityReduction.Generated.Hardness.C4ddadc69d69dcce12634.Reduction.tmKarpProgram
  correct := ComplexityReduction.Generated.Hardness.C4ddadc69d69dcce12634.Reduction.tmKarpSemanticCorrect

end ComplexityReduction.Generated.Hardness.C4ddadc69d69dcce12634.Reduction

assert_standard_axioms
  ComplexityReduction.Generated.Hardness.C4ddadc69d69dcce12634.Reduction.tmKarpPrimitive,
  ComplexityReduction.Generated.Hardness.C4ddadc69d69dcce12634.Reduction.tmKarpProgram,
  ComplexityReduction.Generated.Hardness.C4ddadc69d69dcce12634.Reduction.tmKarpSemanticCorrect,
  ComplexityReduction.Generated.Hardness.C4ddadc69d69dcce12634.Reduction.authoredForwardReduction
