/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Presentation.NAEThreeSAT
import ComplexityReduction.Presentation.SatisfiabilityTM

/-!
Stable direct-TM views and projections for the canonical NAE-3SAT clause
presentation.

The declarations here depend only on the public clause codec.  They are shared
encoding infrastructure, not a target-specific reduction or gadget proof.
-/

namespace ComplexityReduction
namespace Presentation
namespace NAEThreeSAT

open ComplexityReduction.NAEThreeSAT

/-- Canonical faithful encoded type of one signed literal. -/
abbrev literalEncodedType : EncodedType :=
  Presentation.Satisfiability.literalEncodedType

/-- Re-expose one exact clause as the nested product used by its public encoder. -/
theorem clausePayload_tmPolyTime :
    TMPolyTimeMap clauseEncodedType clausePayloadEncodedType clausePayload := by
  apply TMPolyTimeMap.of_encodingEquiv clauseEncodedType clausePayloadEncodedType
    clausePayload (Equiv.refl _)
  intro clause
  change clausePayloadEncodedType.encode (clausePayload clause) =
    (clausePayloadEncodedType.encode (clausePayload clause)).map id
  rw [List.map_id]

/-- Direct-TM projection of the first literal of an exact NAE clause. -/
theorem clauseFirst_tmPolyTime :
    TMPolyTimeMap clauseEncodedType literalEncodedType Clause.first := by
  have projection := TMPolyTimeMap.fst literalEncodedType
    (EncodedType.prod literalEncodedType literalEncodedType)
  have composed := TMPolyTimeMap.comp projection clausePayload_tmPolyTime
  simpa [Function.comp, clausePayload, clausePayloadEncodedType,
    literalEncodedType] using composed

/-- Direct-TM projection of the `(second, third)` tail of an exact NAE clause. -/
theorem clauseTail_tmPolyTime :
    TMPolyTimeMap clauseEncodedType
      (EncodedType.prod literalEncodedType literalEncodedType)
      (fun clause : Clause => (clause.second, clause.third)) := by
  have projection := TMPolyTimeMap.snd literalEncodedType
    (EncodedType.prod literalEncodedType literalEncodedType)
  have composed := TMPolyTimeMap.comp projection clausePayload_tmPolyTime
  simpa [Function.comp, clausePayload, clausePayloadEncodedType,
    literalEncodedType] using composed

/-- Direct-TM projection of the second literal of an exact NAE clause. -/
theorem clauseSecond_tmPolyTime :
    TMPolyTimeMap clauseEncodedType literalEncodedType Clause.second := by
  have projection := TMPolyTimeMap.fst literalEncodedType literalEncodedType
  have composed := TMPolyTimeMap.comp projection clauseTail_tmPolyTime
  simpa [Function.comp] using composed

/-- Direct-TM projection of the third literal of an exact NAE clause. -/
theorem clauseThird_tmPolyTime :
    TMPolyTimeMap clauseEncodedType literalEncodedType Clause.third := by
  have projection := TMPolyTimeMap.snd literalEncodedType literalEncodedType
  have composed := TMPolyTimeMap.comp projection clauseTail_tmPolyTime
  simpa [Function.comp] using composed

assert_standard_axioms
  clausePayload_tmPolyTime,
  clauseFirst_tmPolyTime,
  clauseTail_tmPolyTime,
  clauseSecond_tmPolyTime,
  clauseThird_tmPolyTime

end NAEThreeSAT
end Presentation
end ComplexityReduction
