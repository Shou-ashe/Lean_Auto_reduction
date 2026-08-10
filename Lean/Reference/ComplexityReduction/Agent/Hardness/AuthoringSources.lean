/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SetCovering.StructuredRoute
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SetPacking.StructuredTMRoute
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.FeedbackNodeSetStructuredTM
import ComplexityReduction.Domain.ExactCoverToThreeDimensionalMatchingTM.Unified
import ComplexityReduction.Problems.Karp21.GraphAtoms
import ComplexityReduction.Presentation.FeedbackNodeSet
import ComplexityReduction.Presentation.SetSystem
import ComplexityReduction.Presentation.ThreeDimensionalMatching

/-!
Public, endpoint-exact direct-TM evidence available to the NP-hard authoring planner.

This is a deliberately small compatibility boundary.  It exposes only raw
`TMKarpReduction` witnesses at canonical `PresentedProblem` backend endpoints;
it does not export a V2 primitive, program, semantic proof, certified reduction,
or hardness result.  The authoring planner may therefore ask an untrusted model
to construct and prove those missing typed layers while Lean retains authority
over the exact source, target, machine, polynomial-time proof, and correctness
theorem carried by each witness.
-/

namespace ComplexityReduction
namespace Agent
namespace Hardness
namespace AuthoringSources

open Encoding

/-- Exact direct-TM evidence from the canonical Vertex Cover hub to Set Covering. -/
noncomputable def vertexCoverToSetCoveringTMKarpReduction :
    TMKarpReduction
      Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem.toEncodedDecisionProblem
      Presentation.SetSystem.setCoveringStructuredProblem.toEncodedDecisionProblem :=
  Karp21.SetCovering.vertexCoverToSetCoveringStructuredTMKarpReduction

/-- Exact direct-TM evidence from the canonical Clique hub to Set Packing. -/
noncomputable def cliqueToSetPackingTMKarpReduction :
    TMKarpReduction
      Problems.Karp21.GraphAtoms.cliqueStructuredProblem.toEncodedDecisionProblem
      Presentation.SetSystem.setPackingStructuredProblem.toEncodedDecisionProblem :=
  Karp21.SetPacking.cliqueToSetPackingStructuredTMKarpReduction

/-- Exact direct-TM evidence from the canonical Vertex Cover hub to Feedback Node Set. -/
noncomputable def vertexCoverToFeedbackNodeSetTMKarpReduction :
    TMKarpReduction
      Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem.toEncodedDecisionProblem
      Presentation.FeedbackNodeSet.structuredProblem.toEncodedDecisionProblem :=
  Karp21.FeedbackNodeSet.vertexCoverToFeedbackNodeSetStructuredTMKarpReduction

/-- Exact direct-TM evidence from the canonical Exact Cover hub to structured 3DM. -/
noncomputable def exactCoverToThreeDimensionalMatchingTMKarpReduction :
    TMKarpReduction
      Presentation.SetSystem.exactCoverStructuredProblem.toEncodedDecisionProblem
      Presentation.ThreeDimensionalMatching.structuredProblem.toEncodedDecisionProblem :=
  ComplexityReduction.Domain.ExactCoverToThreeDimensionalMatchingTM.Unified.exactCoverToThreeDimensionalMatchingStructuredTMKarpReduction

assert_standard_axioms exactCoverToThreeDimensionalMatchingTMKarpReduction

end AuthoringSources
end Hardness
end Agent
end ComplexityReduction
