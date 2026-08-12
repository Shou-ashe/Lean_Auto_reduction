/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.Encoding
import ComplexityReduction.Presentation.Satisfiability

/-!
Stable direct-TM operations for the canonical SAT presentation.

This module adapts historically located Karp21 machines to presentation-local
names.  It exposes only representation-generic literal operations and contains
no reduction-specific executable, semantic theorem, or hardness route.
-/

namespace ComplexityReduction
namespace Presentation
namespace Satisfiability

/-- Canonical faithful encoded type of one signed SAT literal. -/
abbrev literalEncodedType : EncodedType := literalPresentation.encodedType

/-- Flipping the polarity of one canonically encoded literal is direct-TM polynomial time. -/
theorem literalNegate_tmPolyTime :
    TMPolyTimeMap literalEncodedType literalEncodedType SAT.Clause.negate := by
  simpa [literalEncodedType] using
    ComplexityReduction.Karp21.literalNegateTMBackedMap.tm_polytime

assert_standard_axioms literalNegate_tmPolyTime

end Satisfiability
end Presentation
end ComplexityReduction
