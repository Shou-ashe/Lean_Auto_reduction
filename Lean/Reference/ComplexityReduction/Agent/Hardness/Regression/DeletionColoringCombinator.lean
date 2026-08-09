/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.FiniteWitness
import ComplexityReduction.AxiomGate

/-!
Cross-family regression for the generic finite deletion-and-coloring witness.
This is deliberately outside the Quals benchmark namespace: the same packet
contract is exercised on a tiny triangle before any qualifying-exam endpoint
is allowed to depend on it.
-/

namespace ComplexityReduction.Agent.Hardness.Regression.DeletionColoringCombinator

open ComplexityReduction.Agent.Hardness.FiniteWitness

def triangle : List Edge := [(0, 1), (1, 2), (2, 0)]

def deleteFirst : List Nat := [deletionMarker, 0, 1]

theorem deleteFirst_legal : DeletionColoring 3 1 triangle deleteFirst := by
  simp [DeletionColoring, DeletionColorValuesLegal, DeletionColorEdgeLegal,
    triangle, deleteFirst, deletionMarker, deletionColorValue]

theorem deleteFirst_checker :
    deletionColoringChecker 3 1 triangle deleteFirst = true :=
  (deletionColoringChecker_eq_true_iff 3 1 triangle deleteFirst).2 deleteFirst_legal

end ComplexityReduction.Agent.Hardness.Regression.DeletionColoringCombinator

assert_standard_axioms
  ComplexityReduction.Agent.Hardness.Regression.DeletionColoringCombinator.deleteFirst_legal,
  ComplexityReduction.Agent.Hardness.Regression.DeletionColoringCombinator.deleteFirst_checker
