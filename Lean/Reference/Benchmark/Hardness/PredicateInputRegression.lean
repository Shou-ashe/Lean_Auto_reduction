import Benchmark.Hardness.Inputs.PredicateInput
import ComplexityReduction.Agent.Hardness.InputInspection
import ComplexityReduction.Agent.Hardness.ProblemCatalog

namespace Benchmark.Hardness.PredicateInputRegression

open Benchmark.Hardness.Inputs.PredicateInput

example : directCNFAccepts =
    ComplexityReduction.Problems.Karp21.Satisfiability.cnfSATStructuredProblem.accepts :=
  rfl

example : notationExpandedCNFAccepts = directCNFAccepts :=
  rfl

example : reducibleWrappedCNFAccepts = directCNFAccepts :=
  rfl

example : representationIncompatiblePartitionAccepts =
    ComplexityReduction.Presentation.PartitionBinary.structuredProblem.accepts :=
  rfl

example : uniqueThreeSATAccepts =
    ComplexityReduction.Problems.Karp21.Satisfiability.threeSATStructuredProblem.accepts :=
  rfl

#hardness_inspect_input "predicate-direct-cnf" directCNFAccepts
#hardness_inspect_input "predicate-notation-cnf" notationExpandedCNFAccepts
#hardness_inspect_input "predicate-reducible-cnf" reducibleWrappedCNFAccepts
#hardness_inspect_input "predicate-different-cnf" sameCarrierDifferentPredicate
#hardness_inspect_input "predicate-partition-codec" representationIncompatiblePartitionAccepts
#hardness_inspect_input "predicate-closed-prop" closedProposition
#hardness_inspect_input "predicate-missing-presentation" missingPresentationPredicate
#hardness_inspect_input "predicate-unique-three-sat" uniqueThreeSATAccepts

private def binaryRelation (_first _second : Nat) : Prop :=
  True

/-! A curried binary relation is not admitted as a unary predicate input. -/
#hardness_inspect_input "predicate-reject-binary-relation" binaryRelation

#hardness_export_problem_catalog "predicate-input-regression-catalog"

end Benchmark.Hardness.PredicateInputRegression
