import ComplexityReduction.Problems.Karp21.SATTractable
import ComplexityReduction.Problems.Karp21.Satisfiability

namespace Benchmark.Hardness.Inputs.Gaps.RepresentationMismatch

private abbrev registeredSource : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Problems.Karp21.SATTractable.twoCNFStructuredProblem

/-!
The encoder and carrier are reused exactly, but the structural identity is not
the registered source presentation.  Carrier equality therefore cannot make
this endpoint definitionally equal to the production route source.
-/
private def mismatchedRepresentation : ComplexityReduction.Encoding.LawfulEncodedType where
  encodedType := registeredSource.representation.encodedType
  representation := ComplexityReduction.Encoding.CodecShape.unit.identity
  faithful := registeredSource.representation.faithful

def source : ComplexityReduction.Encoding.PresentedProblem where
  semantic := registeredSource.semantic
  representation := mismatchedRepresentation
  carrier_eq := registeredSource.carrier_eq

end Benchmark.Hardness.Inputs.Gaps.RepresentationMismatch
