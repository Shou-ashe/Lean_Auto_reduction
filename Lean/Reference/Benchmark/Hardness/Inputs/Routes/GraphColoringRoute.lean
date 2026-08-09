import ComplexityReduction.Routes.ChromaticNumberToCliqueCover.Unified

namespace Benchmark.Hardness.Inputs.Routes.GraphColoringRoute

/-- Current exact-presentation port of legacy L2 `graph_coloring_route`. -/
abbrev source : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Presentation.ChromaticNumber.structuredProblem

abbrev target : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Presentation.CliqueCover.structuredProblem

end Benchmark.Hardness.Inputs.Routes.GraphColoringRoute
