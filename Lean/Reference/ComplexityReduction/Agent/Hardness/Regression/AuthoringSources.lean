/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.AuthoringSources
import ComplexityReduction.Problems.Karp21.GraphAtoms
import ComplexityReduction.Presentation.FeedbackNodeSet
import ComplexityReduction.Presentation.SetSystem
import ComplexityReduction.Routes.FeedbackNodeSetToFeedbackArcSet.Unified
import ComplexityReduction.Routes.SetCoveringToHittingSet.Unified

/-!
Focused compile-time endpoint probes for the public TM/Karp authoring-source
boundary and its registry-certified dependent successors.  This module
exports no registry candidate or hardness result.
-/

namespace ComplexityReduction.Agent.Hardness.Regression.AuthoringSources

open ComplexityReduction Encoding
noncomputable section

example :
    TMKarpReduction
      Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem.toEncodedDecisionProblem
      Presentation.SetSystem.setCoveringStructuredProblem.toEncodedDecisionProblem :=
  Agent.Hardness.AuthoringSources.vertexCoverToSetCoveringTMKarpReduction

example :
    TMKarpReduction
      Problems.Karp21.GraphAtoms.cliqueStructuredProblem.toEncodedDecisionProblem
      Presentation.SetSystem.setPackingStructuredProblem.toEncodedDecisionProblem :=
  Agent.Hardness.AuthoringSources.cliqueToSetPackingTMKarpReduction

example :
    TMKarpReduction
      Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem.toEncodedDecisionProblem
      Presentation.FeedbackNodeSet.structuredProblem.toEncodedDecisionProblem :=
  Agent.Hardness.AuthoringSources.vertexCoverToFeedbackNodeSetTMKarpReduction

/-- The first dependent successor is a public exact certificate, not hardness. -/
example :
    Certificate.CertifiedReduction
      Presentation.SetSystem.setCoveringStructuredProblem
      Presentation.SetSystem.hittingSetStructuredProblem :=
  Routes.SetCoveringToHittingSet.certifiedReduction

/-- The second dependent successor has the canonical structured graph endpoints. -/
example :
    Certificate.CertifiedReduction
      Presentation.FeedbackNodeSet.structuredProblem
      Presentation.FeedbackArcSet.structuredProblem :=
  Routes.FeedbackNodeSetToFeedbackArcSet.certifiedReduction

end
end ComplexityReduction.Agent.Hardness.Regression.AuthoringSources
