import Benchmark.Hardness.Inputs.Completeness.BackendCompletenessOnly
import Benchmark.Hardness.Inputs.Gaps.MissingNativeMembership
import Benchmark.Hardness.Inputs.Gaps.RepresentationMismatch
import ComplexityReduction.Presentation.PartitionBinary
import ComplexityReduction.Presentation.UndirectedHamiltonianCircuit
import ComplexityReduction.Problems.Karp21.CliqueNativeVerifier
import ComplexityReduction.Problems.Karp21.KnapsackNativeVerifier
import ComplexityReduction.Problems.Karp21.ThreeSATNativeVerifier
import ComplexityReduction.Routes.CliqueToVertexCover.Unified
import ComplexityReduction.Routes.GraphToRoleGraph.Unified
import ComplexityReduction.Routes.SetCoveringToSatisfiability.Unified
import ComplexityReduction.Routes.ThreeSATToClique.IngressAdapters

/-!
Public Stage-L inputs for the Core generalization contract.

This module deliberately contributes no reduction, membership, completeness,
representation-change, or authoring theorem.  It only exposes existing library
problems and exact predicates under user-facing declarations, plus invalid or
disconnected inputs used to audit typed blockers.
-/

namespace Benchmark.Hardness.Inputs.CoreGeneralization.Inputs

open ComplexityReduction Encoding

private abbrev taggedProblem : PresentedProblem :=
  Routes.ThreeSATToClique.IngressAdapters.taggedThreeSATProblem

private abbrev graphProblem : PresentedProblem :=
  Routes.GraphToRoleGraph.originalSourceProblem

private abbrev graphPredicateProblem : PresentedProblem :=
  Problems.Karp21.GraphAtoms.cliqueStructuredProblem

private abbrev setSystemProblem : PresentedProblem :=
  Presentation.SetSystem.setCoveringStructuredProblem

private abbrev partitionProblem : PresentedProblem :=
  Presentation.Partition.structuredProblem

/-- Clause/CSP-family PresentedProblem with an existing long Core route. -/
abbrev clausePresented : PresentedProblem :=
  taggedProblem

/-- Exact predicate spelling of `clausePresented`. -/
def clausePredicate : taggedProblem.Instance → Prop :=
  taggedProblem.accepts

/-- Graph-family PresentedProblem with an existing direct/factored route. -/
abbrev graphPresented : PresentedProblem :=
  graphProblem

/-- A uniquely presented graph-family predicate with an existing route. -/
def graphPredicate : graphPredicateProblem.Instance → Prop :=
  graphPredicateProblem.accepts

/-- Fixed graph-family target requested by the PresentedProblem case. -/
abbrev graphTarget : PresentedProblem :=
  Routes.GraphToRoleGraph.roleGraphTargetProblem

/-- Fixed target for the graph predicate case. -/
abbrev graphPredicateTarget : PresentedProblem :=
  Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem

/-- Set-system source with an existing cross-family long route. -/
abbrev setSystemPresented : PresentedProblem :=
  setSystemProblem

/-- Exact registered native-membership endpoint. -/
abbrev registeredMembershipProblem : PresentedProblem :=
  Problems.Karp21.Satisfiability.threeSATStructuredProblem

/-- Numeric source whose existing native membership admits the checked Cook--Levin root. -/
abbrev numericCookLevinProblem : PresentedProblem :=
  Presentation.Knapsack.structuredProblem

/-- Graph endpoint with exact native membership and a forward path from complete 3SAT. -/
abbrev graphCompletenessProblem : PresentedProblem :=
  Problems.Karp21.GraphAtoms.cliqueStructuredProblem

/-- A closed proposition is not a decision-problem endpoint. -/
def closedProposition : Prop :=
  True

/-- Multiple encoder-bound Partition presentations share this raw predicate. -/
def ambiguousPartitionPredicate : partitionProblem.Instance → Prop :=
  partitionProblem.accepts

/-- Same semantic carrier as a library problem, but with an incompatible representation. -/
abbrev representationMismatch : PresentedProblem :=
  Benchmark.Hardness.Inputs.Gaps.RepresentationMismatch.source

/-- Valid source used with a policy that filters every target evidence row. -/
abbrev noEligibleTargetSource : PresentedProblem :=
  taggedProblem

/-- Graph presentation whose forward component has no eligible hard target. -/
abbrev forwardRouteAbsent : PresentedProblem :=
  Presentation.Graph.wellFormedProblem

/-- Hard endpoint for which reflexivity is forbidden and only the reverse direction is useful. -/
abbrev reverseOnlyRoute : PresentedProblem :=
  Presentation.UndirectedHamiltonianCircuit.structuredProblem

/-- Exact PresentedProblem with no registered `NativeTMInNP` capability. -/
abbrev missingNativeMembership : PresentedProblem :=
  Benchmark.Hardness.Inputs.Gaps.MissingNativeMembership.source

/-- Endpoint with native membership and backend-only, but no native, completeness. -/
abbrev invalidCompletenessHead : PresentedProblem :=
  Benchmark.Hardness.Inputs.Completeness.BackendCompletenessOnly.source

end Benchmark.Hardness.Inputs.CoreGeneralization.Inputs
