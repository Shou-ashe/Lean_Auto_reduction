import Benchmark.Hardness.Inputs.NPHardGeneralization.SetSystemProgramComposition

/-! Isolated benchmark self-check.  Never imported by the public input tree. -/

namespace Benchmark.Hardness.Gold.NPHardGeneralization.SetSystemProgramComposition

open ComplexityReduction.Certificate
open ComplexityReduction.Program
open Benchmark.Hardness.Inputs.NPHardGeneralization.SetSystemProgramComposition

def composedProgram : PolyProg hub.representation source.representation :=
  .comp secondAdapter firstAdapter

def certifiedReduction : CertifiedReduction hub source where
  program := composedProgram
  correct := by
    intro input
    rfl

end Benchmark.Hardness.Gold.NPHardGeneralization.SetSystemProgramComposition
