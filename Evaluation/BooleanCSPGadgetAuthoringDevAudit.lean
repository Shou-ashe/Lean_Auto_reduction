/-
Isolated, non-scoring audit for the three gadget-authoring development
fixtures.  Production and capability-gate inputs never import this file.
-/

import Benchmark.Hardness.Inputs.BooleanCSPNPHard.GadgetAuthoringDevRandomHard4
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.GadgetAuthoringDevDualExactlyFive7
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.GadgetAuthoringDevMixedNAND2OR3
import ComplexityReduction.Domain.BooleanCSP.Hardness.SchaeferHardness
import ComplexityReduction.Agent.Reduction.Reflection

namespace Evaluation.BooleanCSPGadgetAuthoringDevAudit

open ComplexityReduction
open ComplexityReduction.Certificate
open ComplexityReduction.Domain.BooleanCSP
open ComplexityReduction.Agent.Reduction

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem nPHardOfFiniteChecks (gamma : Gamma)
    (nonemptyChecked : @decide
      (∀ symbol : gamma.Symbol, (gamma.relationOf symbol).Nonempty)
      (Reflection.gammaRelationsNonemptyDecidable gamma) = true)
    (hardSideChecked : @decide gamma.IsSchaeferTractable
      (Reflection.gammaSchaeferTractableDecidable gamma) = false) :
    NativeTMNPHard (cspOf gamma) := by
  apply Hardness.NativeTMNPHard_of_notSchaeferTractable
  · exact Reflection.gammaRelationsNonempty_of_decide_eq_true gamma nonemptyChecked
  · exact Reflection.gammaNotSchaeferTractable_of_decide_eq_false gamma hardSideChecked

theorem randomHard4 : NativeTMNPHard
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.GadgetAuthoringDevRandomHard4.problem := by
  change NativeTMNPHard (cspOf
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.GadgetAuthoringDevRandomHard4.gamma)
  exact nPHardOfFiniteChecks _ (by decide) (by decide)

theorem dualExactlyFive7 : NativeTMNPHard
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.GadgetAuthoringDevDualExactlyFive7.problem := by
  change NativeTMNPHard (cspOf
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.GadgetAuthoringDevDualExactlyFive7.gamma)
  exact nPHardOfFiniteChecks _ (by decide) (by decide)

theorem mixedNAND2OR3 : NativeTMNPHard
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.GadgetAuthoringDevMixedNAND2OR3.problem := by
  change NativeTMNPHard (cspOf
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.GadgetAuthoringDevMixedNAND2OR3.gamma)
  exact nPHardOfFiniteChecks _ (by decide) (by decide)

end Evaluation.BooleanCSPGadgetAuthoringDevAudit
