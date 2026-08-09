import ComplexityReduction_IR.V2.Routes.ThreeSATToClique.IngressAdapters

/-! A representation wrapper whose registered V2 ingress erases an ignored Boolean tag. -/

namespace Benchmark.V2Hardness.TaggedThreeSAT

abbrev source : ComplexityReduction_IR.V2.Encoding.PresentedProblem :=
  ComplexityReduction_IR.V2.Routes.ThreeSATToClique.IngressAdapters.taggedThreeSATProblem

end Benchmark.V2Hardness.TaggedThreeSAT
