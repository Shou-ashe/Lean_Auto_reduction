/-
H-K shadow publication candidate.  This module contains only the
model-authored reduction DAG and runner-owned CertifiedReduction.
It intentionally provides no native hardness theorem.
-/

import ComplexityReduction.Presentation.SetSystem
import ComplexityReduction.Problems.Karp21.GraphAtoms
import ComplexityReduction.Agent.Hardness.AuthoringSources
import ComplexityReduction.Certificate.Reduction
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.AxiomGate

namespace ComplexityReduction.Generated.Hardness.C878ab5c0f5232e514499.Reduction

open ComplexityReduction
open ComplexityReduction.Certificate
open ComplexityReduction.Encoding
open ComplexityReduction.Program
open ComplexityReduction.Problems.Karp21.GraphAtoms
open ComplexityReduction.Presentation.SetSystem

noncomputable def tmKarpPrimitive :
    ComplexityReduction.Program.Primitive ComplexityReduction.Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem.representation ComplexityReduction.Presentation.SetSystem.setCoveringStructuredProblem.representation :=
  by
    exact Primitive.ofTMPolyTime ComplexityReduction.Agent.Hardness.AuthoringSources.vertexCoverToSetCoveringTMKarpReduction.f ComplexityReduction.Agent.Hardness.AuthoringSources.vertexCoverToSetCoveringTMKarpReduction.polytime

noncomputable def tmKarpProgram :
    ComplexityReduction.Program.PolyProg ComplexityReduction.Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem.representation ComplexityReduction.Presentation.SetSystem.setCoveringStructuredProblem.representation :=
  by
    exact PolyProg.atom ComplexityReduction.Generated.Hardness.C878ab5c0f5232e514499.Reduction.tmKarpPrimitive

noncomputable def tmKarpSemanticCorrect :
    ∀ input : ComplexityReduction.Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem.Instance, ComplexityReduction.Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem.accepts input ↔ ComplexityReduction.Presentation.SetSystem.setCoveringStructuredProblem.accepts (ComplexityReduction.Generated.Hardness.C878ab5c0f5232e514499.Reduction.tmKarpProgram.run input) :=
  by
    intro input
    simpa only [ComplexityReduction.Generated.Hardness.C878ab5c0f5232e514499.Reduction.tmKarpProgram, ComplexityReduction.Generated.Hardness.C878ab5c0f5232e514499.Reduction.tmKarpPrimitive, PolyProg.run_atom, Primitive.run_ofTMPolyTime] using
      ComplexityReduction.Agent.Hardness.AuthoringSources.vertexCoverToSetCoveringTMKarpReduction.correct input

@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def authoredForwardReduction :
    ComplexityReduction.Certificate.CertifiedReduction ComplexityReduction.Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem ComplexityReduction.Presentation.SetSystem.setCoveringStructuredProblem where
  program := ComplexityReduction.Generated.Hardness.C878ab5c0f5232e514499.Reduction.tmKarpProgram
  correct := ComplexityReduction.Generated.Hardness.C878ab5c0f5232e514499.Reduction.tmKarpSemanticCorrect

end ComplexityReduction.Generated.Hardness.C878ab5c0f5232e514499.Reduction

assert_standard_axioms
  ComplexityReduction.Generated.Hardness.C878ab5c0f5232e514499.Reduction.tmKarpPrimitive,
  ComplexityReduction.Generated.Hardness.C878ab5c0f5232e514499.Reduction.tmKarpProgram,
  ComplexityReduction.Generated.Hardness.C878ab5c0f5232e514499.Reduction.tmKarpSemanticCorrect,
  ComplexityReduction.Generated.Hardness.C878ab5c0f5232e514499.Reduction.authoredForwardReduction
