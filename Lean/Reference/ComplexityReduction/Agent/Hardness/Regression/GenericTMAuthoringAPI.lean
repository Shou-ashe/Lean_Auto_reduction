/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Agent.Hardness.BooleanCSPReductionScaffold
import ComplexityReduction.Program.EncodingTransport
import ComplexityReduction.Program.List

/-!
Regression checks for the generic authoring interfaces.  The list proofs use
the same two constructors for zero, one, two, and five outputs, so no theorem is
tied to one reduction's fixed gadget length.
-/

namespace ComplexityReduction.Agent.Hardness.Regression.GenericTMAuthoringAPI

open ComplexityReduction

theorem emptyList_tmPolyTime :
    TMPolyTimeMap EncodedType.nat (EncodedType.list EncodedType.nat)
      (fun _ : Nat => []) :=
  TMPolyTimeMap.list_nil EncodedType.nat EncodedType.nat

theorem singletonList_tmPolyTime :
    TMPolyTimeMap EncodedType.nat (EncodedType.list EncodedType.nat)
      (fun input : Nat => [input]) :=
  TMPolyTimeMap.list_singleton_of (TMPolyTimeMap.id EncodedType.nat)

theorem pairList_tmPolyTime :
    TMPolyTimeMap EncodedType.nat (EncodedType.list EncodedType.nat)
      (fun input : Nat => [input, input]) := by
  exact TMPolyTimeMap.list_cons_of (TMPolyTimeMap.id EncodedType.nat)
    (TMPolyTimeMap.list_singleton_of (TMPolyTimeMap.id EncodedType.nat))

theorem fiveList_tmPolyTime :
    TMPolyTimeMap EncodedType.nat (EncodedType.list EncodedType.nat)
      (fun input : Nat => [input, input, input, input, input]) := by
  exact TMPolyTimeMap.list_cons_of (TMPolyTimeMap.id EncodedType.nat)
    (TMPolyTimeMap.list_cons_of (TMPolyTimeMap.id EncodedType.nat)
      (TMPolyTimeMap.list_cons_of (TMPolyTimeMap.id EncodedType.nat)
        (TMPolyTimeMap.list_cons_of (TMPolyTimeMap.id EncodedType.nat)
          (TMPolyTimeMap.list_singleton_of (TMPolyTimeMap.id EncodedType.nat)))))

/-- A second presentation of the same natural-number payload. -/
def copiedNatEncoding : EncodedType where
  Carrier := Nat
  Symbol := EncodedType.nat.Symbol
  finite_symbol := EncodedType.nat.finite_symbol
  encode := EncodedType.nat.encode

theorem copiedNatIdentity_tmPolyTime :
    TMPolyTimeMap EncodedType.nat copiedNatEncoding id := by
  apply TMPolyTimeMap.transport_output
    (Z := copiedNatEncoding) (targetOutput := id)
    (TMPolyTimeMap.id EncodedType.nat) (Equiv.refl _)
  intro input
  change EncodedType.nat.encode input =
    List.map (fun symbol => symbol) (EncodedType.nat.encode input)
  exact (List.map_id _).symm

theorem inferredTernaryConstraintCode_tmPolyTime :
    TMPolyTimeMap EncodedType.nat
      Presentation.FiniteDomainCSPTable.constraintCodeEncodedType
      (fun input => Presentation.FiniteDomainCSPTable.constraintCode
        (Agent.Hardness.BooleanCSPReductionScaffold.ternaryConstraint
          input input input)) := by
  exact Agent.Hardness.BooleanCSPReductionScaffold.ternaryConstraintCode_tmPolyTime
    (TMPolyTimeMap.id EncodedType.nat)
    (TMPolyTimeMap.id EncodedType.nat)
    (TMPolyTimeMap.id EncodedType.nat)

noncomputable def fourTernaryConstraints (input : Nat) :
    CSP.Formula Agent.Hardness.BooleanCSPReductionScaffold.gamma :=
  [ Agent.Hardness.BooleanCSPReductionScaffold.ternaryConstraint input input input,
    Agent.Hardness.BooleanCSPReductionScaffold.ternaryConstraint input 0 input,
    Agent.Hardness.BooleanCSPReductionScaffold.ternaryConstraint 0 input input,
    Agent.Hardness.BooleanCSPReductionScaffold.ternaryConstraint input input 0 ]

theorem inferredFourConstraintFormula_tmPolyTime :
    TMPolyTimeMap EncodedType.nat
      (Presentation.FiniteDomainCSPTable.encodedType
        Agent.Hardness.BooleanCSPReductionScaffold.gamma)
      fourTernaryConstraints := by
  have hInput := TMPolyTimeMap.id EncodedType.nat
  have hZero := TMPolyTimeMap.const EncodedType.nat EncodedType.nat
    (show Nat from 0)
  have hFirst :=
    Agent.Hardness.BooleanCSPReductionScaffold.ternaryConstraintCode_tmPolyTime
      hInput hInput hInput
  have hSecond :=
    Agent.Hardness.BooleanCSPReductionScaffold.ternaryConstraintCode_tmPolyTime
      hInput hZero hInput
  have hThird :=
    Agent.Hardness.BooleanCSPReductionScaffold.ternaryConstraintCode_tmPolyTime
      hZero hInput hInput
  have hFourth :=
    Agent.Hardness.BooleanCSPReductionScaffold.ternaryConstraintCode_tmPolyTime
      hInput hInput hZero
  have hCode := TMPolyTimeMap.list_cons_of hFirst
    (TMPolyTimeMap.list_cons_of hSecond
      (TMPolyTimeMap.list_cons_of hThird
        (TMPolyTimeMap.list_singleton_of hFourth)))
  exact Presentation.FiniteDomainCSPTable.formula_tmPolyTime_of_code hCode (by
    intro input
    rfl)

assert_standard_axioms
  emptyList_tmPolyTime,
  singletonList_tmPolyTime,
  pairList_tmPolyTime,
  fiveList_tmPolyTime,
  copiedNatIdentity_tmPolyTime,
  inferredTernaryConstraintCode_tmPolyTime,
  fourTernaryConstraints,
  inferredFourConstraintFormula_tmPolyTime

end ComplexityReduction.Agent.Hardness.Regression.GenericTMAuthoringAPI
