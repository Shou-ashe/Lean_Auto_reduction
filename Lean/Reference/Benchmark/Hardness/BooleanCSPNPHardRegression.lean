/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case01Canonical
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case02PositiveNAE4
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case03PositiveNAE3
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case04PositiveExactlyOne3
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case05OR2EvenParity3
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case06PositiveNAE5
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case07PositiveExactlyTwo3
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case08PositiveExactlyOne4
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case09PositiveExactlyTwo4
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case10PositiveExactlyThree4
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case11PositiveExactlyOne5
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case12PositiveExactlyTwo5
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case13PositiveExactlyThree5
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case14PositiveExactlyFour5
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case15PositiveExactlyOne6
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case16PositiveExactlyTwo6
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case17PositiveExactlyThree6
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case18PositiveExactlyFour6
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case19PositiveExactlyFive6
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case20OR3XOR2
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

/-! Compile-time surface check for the thirty closed Boolean-CSP benchmark endpoints. -/

namespace Benchmark.Hardness.BooleanCSPNPHardRegression

open ComplexityReduction.Encoding

noncomputable def endpoints : List PresentedProblem :=
  [ Inputs.BooleanCSPNPHard.Case01Canonical.problem
  , Inputs.BooleanCSPNPHard.Case02PositiveNAE4.problem
  , Inputs.BooleanCSPNPHard.Case03PositiveNAE3.problem
  , Inputs.BooleanCSPNPHard.Case04PositiveExactlyOne3.problem
  , Inputs.BooleanCSPNPHard.Case05OR2EvenParity3.problem
  , Inputs.BooleanCSPNPHard.Case06PositiveNAE5.problem
  , Inputs.BooleanCSPNPHard.Case07PositiveExactlyTwo3.problem
  , Inputs.BooleanCSPNPHard.Case08PositiveExactlyOne4.problem
  , Inputs.BooleanCSPNPHard.Case09PositiveExactlyTwo4.problem
  , Inputs.BooleanCSPNPHard.Case10PositiveExactlyThree4.problem
  , Inputs.BooleanCSPNPHard.Case11PositiveExactlyOne5.problem
  , Inputs.BooleanCSPNPHard.Case12PositiveExactlyTwo5.problem
  , Inputs.BooleanCSPNPHard.Case13PositiveExactlyThree5.problem
  , Inputs.BooleanCSPNPHard.Case14PositiveExactlyFour5.problem
  , Inputs.BooleanCSPNPHard.Case15PositiveExactlyOne6.problem
  , Inputs.BooleanCSPNPHard.Case16PositiveExactlyTwo6.problem
  , Inputs.BooleanCSPNPHard.Case17PositiveExactlyThree6.problem
  , Inputs.BooleanCSPNPHard.Case18PositiveExactlyFour6.problem
  , Inputs.BooleanCSPNPHard.Case19PositiveExactlyFive6.problem
  , Inputs.BooleanCSPNPHard.Case20OR3XOR2.problem
  , Inputs.BooleanCSPNPHard.Case21RandomTableA.problem
  , Inputs.BooleanCSPNPHard.Case22RandomTableB.problem
  , Inputs.BooleanCSPNPHard.Case23RandomTableC.problem
  , Inputs.BooleanCSPNPHard.Case24RandomTableD.problem
  , Inputs.BooleanCSPNPHard.Case25RandomTableE.problem
  , Inputs.BooleanCSPNPHard.Case26RandomTableF.problem
  , Inputs.BooleanCSPNPHard.Case27RandomTableG.problem
  , Inputs.BooleanCSPNPHard.Case28RandomTableH.problem
  , Inputs.BooleanCSPNPHard.Case29RandomTableI.problem
  , Inputs.BooleanCSPNPHard.Case30RandomTableJ.problem
  ]

theorem endpoint_count : endpoints.length = 30 := by decide

end Benchmark.Hardness.BooleanCSPNPHardRegression
