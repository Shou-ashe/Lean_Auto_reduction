/-
Isolated oracle audit for Q-B21--Q-B30.

This file is outside the public Lean source roots. It checks the committed
truth tables with the executable finite deciders and then applies Schaefer's
hardness theorem. Benchmark production never imports this file.
-/

import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case21RandomTableA
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case22RandomTableB
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case23RandomTableC
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case24RandomTableD
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case25RandomTableE
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case26RandomTableF
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case27RandomTableG
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case28RandomTableH
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case29RandomTableI
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case30RandomTableJ
import ComplexityReduction.Domain.BooleanCSP.Hardness.SchaeferHardness
import ComplexityReduction.Agent.Reduction.Reflection

namespace Evaluation.BooleanCSPRandomSupplementAudit

open ComplexityReduction
open ComplexityReduction.Certificate
open ComplexityReduction.Domain.BooleanCSP
open ComplexityReduction.Agent.Reduction

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

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

theorem case21 : NativeTMNPHard
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case21RandomTableA.problem := by
  change NativeTMNPHard (cspOf
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case21RandomTableA.gamma)
  exact nPHardOfFiniteChecks _ (by decide) (by decide)

theorem case22 : NativeTMNPHard
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case22RandomTableB.problem := by
  change NativeTMNPHard (cspOf
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case22RandomTableB.gamma)
  exact nPHardOfFiniteChecks _ (by decide) (by decide)

theorem case23 : NativeTMNPHard
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case23RandomTableC.problem := by
  change NativeTMNPHard (cspOf
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case23RandomTableC.gamma)
  exact nPHardOfFiniteChecks _ (by decide) (by decide)

theorem case24 : NativeTMNPHard
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case24RandomTableD.problem := by
  change NativeTMNPHard (cspOf
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case24RandomTableD.gamma)
  exact nPHardOfFiniteChecks _ (by decide) (by decide)

theorem case25 : NativeTMNPHard
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case25RandomTableE.problem := by
  change NativeTMNPHard (cspOf
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case25RandomTableE.gamma)
  exact nPHardOfFiniteChecks _ (by decide) (by decide)

theorem case26 : NativeTMNPHard
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case26RandomTableF.problem := by
  change NativeTMNPHard (cspOf
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case26RandomTableF.gamma)
  exact nPHardOfFiniteChecks _ (by decide) (by decide)

theorem case27 : NativeTMNPHard
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case27RandomTableG.problem := by
  change NativeTMNPHard (cspOf
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case27RandomTableG.gamma)
  exact nPHardOfFiniteChecks _ (by decide) (by decide)

theorem case28 : NativeTMNPHard
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case28RandomTableH.problem := by
  change NativeTMNPHard (cspOf
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case28RandomTableH.gamma)
  exact nPHardOfFiniteChecks _ (by decide) (by decide)

theorem case29 : NativeTMNPHard
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case29RandomTableI.problem := by
  change NativeTMNPHard (cspOf
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case29RandomTableI.gamma)
  exact nPHardOfFiniteChecks _ (by decide) (by decide)

theorem case30 : NativeTMNPHard
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case30RandomTableJ.problem := by
  change NativeTMNPHard (cspOf
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case30RandomTableJ.gamma)
  exact nPHardOfFiniteChecks _ (by decide) (by decide)

end Evaluation.BooleanCSPRandomSupplementAudit
