/-
H-K shadow publication candidate.  This module contains only the
model-authored reduction DAG and runner-owned CertifiedReduction.
It intentionally provides no native hardness theorem.
-/

import ComplexityReduction.Presentation.FeedbackArcSet
import ComplexityReduction.Problems.Karp21.GraphAtoms
import ComplexityReduction.Presentation.FeedbackNodeSet
import ComplexityReduction.Routes.FeedbackNodeSetToFeedbackArcSet.Unified
import ComplexityReduction.Agent.Hardness.AuthoringSources
import ComplexityReduction.Certificate.Reduction
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.AxiomGate

namespace ComplexityReduction.Generated.Hardness.C15c953ce5e20344bf87b.Reduction

open ComplexityReduction
open ComplexityReduction.Certificate
open ComplexityReduction.Encoding
open ComplexityReduction.Program
open ComplexityReduction.Problems.Karp21.GraphAtoms
open ComplexityReduction.Presentation.FeedbackArcSet

noncomputable def tmKarpPrimitive :
    ComplexityReduction.Program.Primitive ComplexityReduction.Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem.representation ComplexityReduction.Presentation.FeedbackNodeSet.structuredProblem.representation :=
  by
    exact Primitive.ofTMPolyTime ComplexityReduction.Agent.Hardness.AuthoringSources.vertexCoverToFeedbackNodeSetTMKarpReduction.f ComplexityReduction.Agent.Hardness.AuthoringSources.vertexCoverToFeedbackNodeSetTMKarpReduction.polytime

noncomputable def tmKarpProgram :
    ComplexityReduction.Program.PolyProg ComplexityReduction.Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem.representation ComplexityReduction.Presentation.FeedbackNodeSet.structuredProblem.representation :=
  by
    exact PolyProg.atom ComplexityReduction.Generated.Hardness.C15c953ce5e20344bf87b.Reduction.tmKarpPrimitive

noncomputable def tmKarpSemanticCorrect :
    ∀ input : ComplexityReduction.Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem.Instance, ComplexityReduction.Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem.accepts input ↔ ComplexityReduction.Presentation.FeedbackNodeSet.structuredProblem.accepts (ComplexityReduction.Generated.Hardness.C15c953ce5e20344bf87b.Reduction.tmKarpProgram.run input) :=
  by
    intro input
    simpa only [ComplexityReduction.Generated.Hardness.C15c953ce5e20344bf87b.Reduction.tmKarpProgram, ComplexityReduction.Generated.Hardness.C15c953ce5e20344bf87b.Reduction.tmKarpPrimitive, PolyProg.run_atom, Primitive.run_ofTMPolyTime] using
      ComplexityReduction.Agent.Hardness.AuthoringSources.vertexCoverToFeedbackNodeSetTMKarpReduction.correct input

noncomputable def composedProgram :
    ComplexityReduction.Program.PolyProg ComplexityReduction.Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem.representation ComplexityReduction.Presentation.FeedbackArcSet.structuredProblem.representation :=
  by
    exact PolyProg.comp ComplexityReduction.Routes.FeedbackNodeSetToFeedbackArcSet.certifiedReduction.program ComplexityReduction.Generated.Hardness.C15c953ce5e20344bf87b.Reduction.tmKarpProgram

noncomputable def composedSemanticCorrect :
    ∀ input : ComplexityReduction.Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem.Instance, ComplexityReduction.Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem.accepts input ↔ ComplexityReduction.Presentation.FeedbackArcSet.structuredProblem.accepts (ComplexityReduction.Generated.Hardness.C15c953ce5e20344bf87b.Reduction.composedProgram.run input) :=
  by
    intro input
    change ComplexityReduction.Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem.accepts input ↔
      ComplexityReduction.Presentation.FeedbackArcSet.structuredProblem.accepts (ComplexityReduction.Routes.FeedbackNodeSetToFeedbackArcSet.certifiedReduction.program.run (ComplexityReduction.Generated.Hardness.C15c953ce5e20344bf87b.Reduction.tmKarpProgram.run input))
    exact (ComplexityReduction.Generated.Hardness.C15c953ce5e20344bf87b.Reduction.tmKarpSemanticCorrect input).trans
      (ComplexityReduction.Routes.FeedbackNodeSetToFeedbackArcSet.certifiedReduction.correct (ComplexityReduction.Generated.Hardness.C15c953ce5e20344bf87b.Reduction.tmKarpProgram.run input))

@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def authoredForwardReduction :
    ComplexityReduction.Certificate.CertifiedReduction ComplexityReduction.Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem ComplexityReduction.Presentation.FeedbackArcSet.structuredProblem where
  program := ComplexityReduction.Generated.Hardness.C15c953ce5e20344bf87b.Reduction.composedProgram
  correct := ComplexityReduction.Generated.Hardness.C15c953ce5e20344bf87b.Reduction.composedSemanticCorrect

end ComplexityReduction.Generated.Hardness.C15c953ce5e20344bf87b.Reduction

assert_standard_axioms
  ComplexityReduction.Generated.Hardness.C15c953ce5e20344bf87b.Reduction.tmKarpPrimitive,
  ComplexityReduction.Generated.Hardness.C15c953ce5e20344bf87b.Reduction.tmKarpProgram,
  ComplexityReduction.Generated.Hardness.C15c953ce5e20344bf87b.Reduction.tmKarpSemanticCorrect,
  ComplexityReduction.Generated.Hardness.C15c953ce5e20344bf87b.Reduction.composedProgram,
  ComplexityReduction.Generated.Hardness.C15c953ce5e20344bf87b.Reduction.composedSemanticCorrect,
  ComplexityReduction.Generated.Hardness.C15c953ce5e20344bf87b.Reduction.authoredForwardReduction
