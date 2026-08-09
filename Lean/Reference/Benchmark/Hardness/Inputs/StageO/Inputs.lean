import Benchmark.Hardness.Inputs.Authoring.LawfulPresentation
import Benchmark.Hardness.Inputs.CoreGeneralization.Inputs
import Benchmark.Hardness.Inputs.TypedAuthoring.BoundedSubsetMembership
import Benchmark.Hardness.Inputs.TypedAuthoring.SingleEdgeProgram
import Benchmark.Hardness.Inputs.TypedAuthoring.UnsupportedChecker
import ComplexityReduction.Problems.Karp21.GraphAtoms
import ComplexityReduction.Problems.Karp21.Satisfiability
import ComplexityReduction.Routes.ThreeSATToClique.IngressAdapters

/-!
Frozen public input declarations for the Stage O contract.

This file intentionally contributes no new registered reduction, membership,
completeness, authoring candidate, or promoted capability.  O-A freezes only
the exact input and target declarations.  Runtime candidates and publication
modules are introduced by later work packages and remain invisible here.
-/

namespace Benchmark.Hardness.Inputs.StageO.Inputs

open ComplexityReduction Encoding

private abbrev taggedThreeSAT : PresentedProblem :=
  Routes.ThreeSATToClique.IngressAdapters.taggedThreeSATProblem

private abbrev clique : PresentedProblem :=
  Problems.Karp21.GraphAtoms.cliqueStructuredProblem

private abbrev vertexCover : PresentedProblem :=
  Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem

private abbrev threeSAT : PresentedProblem :=
  Problems.Karp21.Satisfiability.threeSATStructuredProblem

/-- Fixed-target competitive Core source. -/
abbrev coreAmbiguousFixedSource : PresentedProblem := taggedThreeSAT

/-- Fixed target for the competitive Core source. -/
abbrev coreAmbiguousFixedTarget : PresentedProblem := clique

/-- Open-target competitive Core source. -/
abbrev coreAmbiguousAutoSource : PresentedProblem := taggedThreeSAT

/-- Predicate input whose exact presentation is established by Lean. -/
def predicateAdapterRoute : clique.Instance → Prop := clique.accepts

/-- Fixed target for the predicate adapter case. -/
abbrev predicateAdapterTarget : PresentedProblem := vertexCover

/-- A parameterized predicate whose concrete parameter remains in the input declaration. -/
def parameterizedPredicate (parameter : Nat) : threeSAT.Instance → Prop :=
  fun input => threeSAT.accepts input ∧ parameter = parameter

/-- The fully elaborated parameter instance used by the Stage O suite. -/
def parameterizedPredicateThree : threeSAT.Instance → Prop :=
  parameterizedPredicate 3

/--
Predicate input for sequential presentation then reduction authoring.

Its exact problem is the tagged 3SAT endpoint.  The first authored capability
exposes that lawful presentation; only a subsequent fresh Core resolve may
discover the independent tagged-3SAT-to-Clique reduction.
-/
def twoGapPresentationPredicate : taggedThreeSAT.Instance → Prop :=
  taggedThreeSAT.accepts

/-- Fixed target for sequential presentation then reduction authoring. -/
abbrev twoGapPresentationTarget : PresentedProblem :=
  clique

/-- Exact problem for sequential checker then native-membership authoring. -/
abbrev twoGapCheckerProblem : PresentedProblem :=
  clique

/-- Producer source for a reusable, non-case-specific reduction capability. -/
abbrev capabilityProducerSource : PresentedProblem :=
  threeSAT

/-- Producer target and later consumer endpoint. -/
abbrev capabilityProducerTarget : PresentedProblem :=
  clique

/-- Consumer endpoint; discovery must occur through a promoted run-local pack. -/
abbrev capabilityConsumerProblem : PresentedProblem := capabilityProducerTarget

abbrev cycleSource : PresentedProblem := capabilityProducerSource
abbrev cycleTarget : PresentedProblem := capabilityProducerTarget
abbrev secondGapPreconditionProblem : PresentedProblem := twoGapCheckerProblem
abbrev wrongDirectionSource : PresentedProblem := capabilityProducerSource
abbrev wrongDirectionTarget : PresentedProblem := capabilityProducerTarget
abbrev disconnectedSource : PresentedProblem := coreAmbiguousFixedSource
abbrev disconnectedTarget : PresentedProblem := predicateAdapterTarget
abbrev unsupportedCheckerProblem : PresentedProblem :=
  Benchmark.Hardness.Inputs.TypedAuthoring.UnsupportedChecker.source
abbrev staleGapSource : PresentedProblem := capabilityProducerSource
abbrev staleGapTarget : PresentedProblem := capabilityProducerTarget
abbrev unpublishedConsumerProblem : PresentedProblem := capabilityConsumerProblem
abbrev oracleCandidateSource : PresentedProblem := capabilityProducerSource
abbrev oracleCandidateTarget : PresentedProblem := capabilityProducerTarget

end Benchmark.Hardness.Inputs.StageO.Inputs
