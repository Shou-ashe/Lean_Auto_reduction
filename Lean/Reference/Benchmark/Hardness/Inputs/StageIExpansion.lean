import ComplexityReduction.Presentation.Graph
import ComplexityReduction.Presentation.PartitionBinary
import ComplexityReduction.Presentation.UndirectedHamiltonianCircuit
import ComplexityReduction.Routes.SetCoveringToSatisfiability.Unified
import ComplexityReduction.Routes.ThreeSATToClique.IngressAdapters

/-!
Stage-I expansion inputs.  These declarations add no reduction, hardness fact,
or representation certificate; they only expose existing library problems and
their exact predicates through a new user-facing module.
-/

namespace Benchmark.Hardness.Inputs.StageIExpansion

open ComplexityReduction Encoding

private abbrev taggedLibraryProblem : PresentedProblem :=
  Routes.ThreeSATToClique.IngressAdapters.taggedThreeSATProblem

private abbrev setCoveringLibraryProblem : PresentedProblem :=
  Presentation.SetSystem.setCoveringStructuredProblem

private abbrev partitionLibraryProblem : PresentedProblem :=
  Presentation.Partition.structuredProblem

/-- Existing tagged-3SAT presentation used as a direct user input. -/
abbrev taggedPresented : PresentedProblem :=
  taggedLibraryProblem

/-- The exact predicate of the same tagged-3SAT presentation. -/
def taggedPredicate : taggedLibraryProblem.Instance → Prop :=
  taggedLibraryProblem.accepts

/-- Existing Set Covering presentation used as a direct user input. -/
abbrev setCoveringPresented : PresentedProblem :=
  setCoveringLibraryProblem

/-- The exact predicate of the same Set Covering presentation. -/
def setCoveringPredicate : setCoveringLibraryProblem.Instance → Prop :=
  setCoveringLibraryProblem.accepts

/-- A graph-family source whose registered forward component graph is disconnected from hard targets. -/
abbrev disconnectedGraphPresented : PresentedProblem :=
  Presentation.Graph.wellFormedProblem

/-- A transported-hard target used as an input to test forbidden reflexive and reverse-only use. -/
abbrev reverseOnlyHardPresented : PresentedProblem :=
  Presentation.UndirectedHamiltonianCircuit.structuredProblem

/-- Partition's predicate remains ambiguous across incompatible encoder-bound presentations. -/
def ambiguousPartitionPredicate : partitionLibraryProblem.Instance → Prop :=
  partitionLibraryProblem.accepts

end Benchmark.Hardness.Inputs.StageIExpansion

