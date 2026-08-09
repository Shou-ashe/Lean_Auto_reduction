/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.Core.IncidenceIR

/-!
Executable-free validation for the canonical `IncidenceIR` hub.

The Boolean guard belongs to the hub rather than to any one downstream
gadget: all target realizations must reject a raw incidence table whose stored
pairs lie outside the two retained cardinality bounds.  Its direct-TM
realization is deliberately supplied by the separate standard companion.
-/

namespace ComplexityReduction
namespace Domain
namespace IncidenceIRValidation

/-- Decide whether every retained raw incidence pair is within the hub bounds. -/
def wellFormedBool (input : IncidenceIR) : Bool :=
  input.membershipPairs.all fun pair =>
    decide (pair.1 < input.leftSize ∧ pair.2 < input.rightSize)

/-- The hub guard recognizes exactly the canonical well-formedness contract. -/
theorem wellFormedBool_eq_true_iff (input : IncidenceIR) :
    wellFormedBool input = true ↔ input.WellFormed := by
  unfold wellFormedBool IncidenceIR.WellFormed
  rw [List.all_eq_true]
  constructor
  · intro allBounded pair pairMember
    exact of_decide_eq_true (allBounded pair pairMember)
  · intro wellFormed pair pairMember
    exact decide_eq_true (wellFormed pair pairMember)

end IncidenceIRValidation
end Domain
end ComplexityReduction
