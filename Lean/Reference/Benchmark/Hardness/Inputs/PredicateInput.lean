import ComplexityReduction.Presentation.PartitionBinary
import ComplexityReduction.Problems.Karp21.Satisfiability

/-!
Stage-H inputs for grounding a closed unary Lean predicate at an already
existing lawful `PresentedProblem`.

These declarations add no reduction or representation certificate.  They are
only alternate spellings of existing predicates, together with deliberately
unsupported negative inputs.
-/

namespace Benchmark.Hardness.Inputs.PredicateInput

open ComplexityReduction Encoding

private abbrev cnfProblem : PresentedProblem :=
  Problems.Karp21.Satisfiability.cnfSATStructuredProblem

private abbrev partitionProblem : PresentedProblem :=
  Presentation.Partition.structuredProblem

private abbrev threeSATProblem : PresentedProblem :=
  Problems.Karp21.Satisfiability.threeSATStructuredProblem

/-- Exact use of an existing endpoint's `accepts` projection. -/
def directCNFAccepts : cnfProblem.Instance → Prop :=
  cnfProblem.accepts

local notation "CNF_SAT_PREDICATE" => ComplexityReduction.SAT.CNF.Satisfiable

/-- The same CNF predicate after notation expansion to its semantic spelling. -/
def notationExpandedCNFAccepts : cnfProblem.Instance → Prop :=
  CNF_SAT_PREDICATE

/-- One reducible layer around the exact endpoint predicate. -/
abbrev reducibleCNFAccepts : cnfProblem.Instance → Prop :=
  cnfProblem.accepts

/-- The reducible wrapper must still be definitionally equal to `accepts`. -/
def reducibleWrappedCNFAccepts : cnfProblem.Instance → Prop :=
  reducibleCNFAccepts

/-- The carrier agrees with CNF, but the predicate deliberately does not. -/
def sameCarrierDifferentPredicate : cnfProblem.Instance → Prop :=
  fun _ => False

/--
Unary and binary Partition share this predicate and carrier while retaining
different encoder-bound identities.  A raw predicate cannot choose between
those presentations.
-/
def representationIncompatiblePartitionAccepts : partitionProblem.Instance → Prop :=
  partitionProblem.accepts

/-- A closed proposition has no instance domain or lawful problem encoding. -/
def closedProposition : Prop :=
  True

/-- A carrier intentionally absent from the public PresentedProblem catalog. -/
structure UnpresentedInput where
  value : Nat

/-- A valid unary predicate for which no lawful existing presentation is available. -/
def missingPresentationPredicate : UnpresentedInput → Prop :=
  fun input => input.value = 0

/--
The exact bundled-3SAT predicate.  Search may return many public problem
names, but Lean matching leaves one encoder-bound presentation identity.
-/
def uniqueThreeSATAccepts : threeSATProblem.Instance → Prop :=
  threeSATProblem.accepts

end Benchmark.Hardness.Inputs.PredicateInput
