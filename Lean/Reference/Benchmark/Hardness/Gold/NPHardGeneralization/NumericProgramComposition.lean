import Benchmark.Hardness.Inputs.NPHardGeneralization.NumericProgramComposition

/-! Isolated benchmark self-check.  Never imported by the public input tree. -/

namespace Benchmark.Hardness.Gold.NPHardGeneralization.NumericProgramComposition

open ComplexityReduction.Certificate
open ComplexityReduction.Program
open Benchmark.Hardness.Inputs.NPHardGeneralization.NumericProgramComposition

def composedProgram : PolyProg hub.representation source.representation :=
  .comp secondAdapter firstAdapter

def certifiedReduction : CertifiedReduction hub source where
  program := composedProgram
  correct := by
    intro input
    change hub.accepts input ↔ false = false ∧ hub.accepts input
    exact ⟨fun accepted => ⟨rfl, accepted⟩, fun accepted => accepted.2⟩

end Benchmark.Hardness.Gold.NPHardGeneralization.NumericProgramComposition
