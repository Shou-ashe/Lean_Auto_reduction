/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP
import ComplexityReduction.Legacy.ComplexityReduction.CSP.StandardRelations

/-!
Public, answer-free finite-language constructors shared by the Stage Q-B inputs.

This file intentionally exports no reduction certificate, hardness theorem,
expected route, or oracle metadata.
-/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

open ComplexityReduction
open ComplexityReduction.CSP
open ComplexityReduction.Domain.BooleanCSP

noncomputable section

/-- A closed Boolean constraint language containing exactly one relation symbol. -/
def singletonGamma (relation : BoolRel) : Gamma where
  Symbol := Unit
  finiteSymbol := inferInstance
  relationOf := fun _ => relation

/-- A closed Boolean constraint language containing two distinguished relations. -/
def pairGamma (falseRelation trueRelation : BoolRel) : Gamma where
  Symbol := Bool
  finiteSymbol := inferInstance
  relationOf
    | false => falseRelation
    | true => trueRelation

end

end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common
