import Benchmark.Hardness.Inputs.Completeness.RegisteredThreeSAT

/-! Public G-E inputs for exact/alias/wrapper and unsupported-encoding checks. -/

namespace Benchmark.Hardness.Inputs.NPHardGeneralization.InputNormalization

open ComplexityReduction

/-- A transparent wrapper around an existing lawful presentation. -/
def wrappedThreeSAT : Encoding.PresentedProblem :=
  Benchmark.Hardness.Inputs.Completeness.RegisteredThreeSAT.source

/-- An encoding without its decision semantics; G-E must reject this boundary. -/
def bareThreeSATEncoding : Encoding.LawfulEncodedType :=
  wrappedThreeSAT.representation

/-- A well-formed Lean declaration with the wrong input type. -/
def unrelatedValue : Nat := 3

end Benchmark.Hardness.Inputs.NPHardGeneralization.InputNormalization
