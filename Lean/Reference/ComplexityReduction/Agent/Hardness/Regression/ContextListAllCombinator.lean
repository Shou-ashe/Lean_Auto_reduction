/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Program.ContextListAll

/-! Non-Quals regression for the generic context/list all-check combinator. -/

namespace ComplexityReduction.Agent.Hardness.Regression.ContextListAllCombinator

open ComplexityReduction
open ComplexityReduction.Program

def predicate (input : Bool × Nat) : Bool := input.1

theorem predicate_tmPolyTime :
    TMPolyTimeMap (EncodedType.prod EncodedType.bool EncodedType.nat)
      EncodedType.bool predicate := by
  simpa [predicate] using TMPolyTimeMap.fst EncodedType.bool EncodedType.nat

example :
    ContextListAll.executable (C := EncodedType.bool) (X := EncodedType.nat)
      predicate (true, ([0, 1, 2] : List Nat)) = true := by
  decide

example :
    ContextListAll.executable (C := EncodedType.bool) (X := EncodedType.nat)
      predicate (false, ([0] : List Nat)) = false := by
  decide

theorem executable_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.bool (EncodedType.list EncodedType.nat))
      EncodedType.bool (ContextListAll.executable predicate) :=
  ContextListAll.executable_tmPolyTime
    (C := EncodedType.bool) (X := EncodedType.nat)
    predicate predicate_tmPolyTime

assert_standard_axioms predicate_tmPolyTime,
  executable_tmPolyTime

end ComplexityReduction.Agent.Hardness.Regression.ContextListAllCombinator
