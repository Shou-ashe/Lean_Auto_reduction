/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipDirectedHamiltonianCircuit
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipFeedbackArcSet
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipFeedbackNodeSet
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipUndirectedHamiltonianCircuit
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.VerifierEncodingDiscipline
import ComplexityReduction.Presentation.DirectedHamiltonianCircuit
import ComplexityReduction.Presentation.FeedbackArcSet
import ComplexityReduction.Presentation.FeedbackNodeSet
import ComplexityReduction.Presentation.UndirectedHamiltonianCircuit

/-!
Backend-membership annotations for four already-presented structured Karp21
graph endpoints.

Each imported CR theorem proves the exact compatibility `TMInNP` proposition.
This leaf exports only that proposition at its matching V2 presentation.  It
does not reconstruct a `CertifiedVerifier`, a checked-decoder discipline,
native membership, hardness, or completeness from legacy verifier internals.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace HamiltonianFeedbackMembership

open Certificate

@[complexity_reduction_ir_typed_verifier]
theorem directedHamiltonianCircuitStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      Presentation.DirectedHamiltonianCircuit.structuredProblem.toEncodedDecisionProblem := by
  change ComplexityReduction.TMInNP
    ComplexityReduction.Combinatorics.Graph.directedHamiltonianCircuitStructuredDecisionProblem
  exact ComplexityReduction.Karp21.directedHamiltonianCircuitStructured_TMInNP

theorem directedHamiltonianCircuitStructured_backendTMInNP :
    BackendTMInNP Presentation.DirectedHamiltonianCircuit.structuredProblem :=
  directedHamiltonianCircuitStructured_backendTMInNP_export

@[complexity_reduction_ir_typed_verifier]
theorem undirectedHamiltonianCircuitStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      Presentation.UndirectedHamiltonianCircuit.structuredProblem.toEncodedDecisionProblem := by
  change ComplexityReduction.TMInNP
    ComplexityReduction.Combinatorics.Graph.undirectedHamiltonianCircuitStructuredDecisionProblem
  exact ComplexityReduction.Karp21.undirectedHamiltonianCircuitStructured_TMInNP

theorem undirectedHamiltonianCircuitStructured_backendTMInNP :
    BackendTMInNP Presentation.UndirectedHamiltonianCircuit.structuredProblem :=
  undirectedHamiltonianCircuitStructured_backendTMInNP_export

@[complexity_reduction_ir_typed_verifier]
theorem feedbackNodeSetStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      Presentation.FeedbackNodeSet.structuredProblem.toEncodedDecisionProblem := by
  change ComplexityReduction.TMInNP
    ComplexityReduction.Combinatorics.Graph.feedbackNodeSetStructuredDecisionProblem
  exact ComplexityReduction.Karp21.feedbackNodeSetStructured_TMInNP

theorem feedbackNodeSetStructured_backendTMInNP :
    BackendTMInNP Presentation.FeedbackNodeSet.structuredProblem :=
  feedbackNodeSetStructured_backendTMInNP_export

@[complexity_reduction_ir_typed_verifier]
theorem feedbackArcSetStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      Presentation.FeedbackArcSet.structuredProblem.toEncodedDecisionProblem := by
  change ComplexityReduction.TMInNP
    ComplexityReduction.Combinatorics.Graph.feedbackArcSetStructuredDecisionProblem
  exact ComplexityReduction.Karp21.feedbackArcSetStructured_TMInNP

theorem feedbackArcSetStructured_backendTMInNP :
    BackendTMInNP Presentation.FeedbackArcSet.structuredProblem :=
  feedbackArcSetStructured_backendTMInNP_export

end HamiltonianFeedbackMembership
end Karp21
end Problems
end ComplexityReduction
