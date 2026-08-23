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

/-- Binary index of a tuple in lexicographic order `000...0, ..., 111...1`. -/
def tupleIndex {arity : Nat} (tuple : BoolTuple arity) : Nat :=
  (List.ofFn tuple).foldl (fun index bit => index * 2 + bit.toNat) 0

/--
Build a Boolean relation from a truth-table bit mask. Bit `i` is set exactly
when the tuple whose `tupleIndex` is `i` is accepted.
-/
def truthTableRel (arity mask : Nat) : BoolRel :=
  BoolRel.ofPredicate arity fun tuple => mask.testBit (tupleIndex tuple) = true

end

end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common
