/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.CSP.BoolRel

/-! Finite truth-table Boolean relations and exact, order-free fingerprints. -/

namespace ComplexityReduction
namespace Domain
namespace BooleanCSP

open ComplexityReduction.CSP

/-- Stage-Q name for the existing finite Boolean truth-table relation. -/
abbrev BooleanRelation : Type := BoolRel

/-- Stage-Q name for Boolean tuples. -/
abbrev BooleanTuple (arity : Nat) : Type := BoolTuple arity

/-- An arity plus the finite set of accepted rows, serialized as Boolean lists. -/
structure RelationFingerprint where
  arity : Nat
  acceptedRows : Finset (List Bool)
  deriving DecidableEq

/-- Encode a fixed-arity tuple without forgetting coordinate order. -/
def tupleCode {arity : Nat} (tuple : BooleanTuple arity) : List Bool :=
  List.ofFn tuple

/-- Exact finite fingerprint of one relation table. -/
noncomputable def relationFingerprint (relation : BooleanRelation) : RelationFingerprint where
  arity := relation.arity
  acceptedRows := relation.accepts.image tupleCode

@[simp]
theorem relationFingerprint_arity (relation : BooleanRelation) :
    (relationFingerprint relation).arity = relation.arity :=
  rfl

@[simp]
theorem tupleCode_length {arity : Nat} (tuple : BooleanTuple arity) :
    (tupleCode tuple).length = arity := by
  simp [tupleCode]

/-- Fingerprinted rows are exactly codes of accepted tuples. -/
theorem mem_relationFingerprint_rows_iff (relation : BooleanRelation) (row : List Bool) :
    row ∈ (relationFingerprint relation).acceptedRows ↔
      ∃ tuple : BooleanTuple relation.arity, relation.Holds tuple ∧ tupleCode tuple = row := by
  classical
  simp [relationFingerprint, BoolRel.Holds]

end BooleanCSP
end Domain
end ComplexityReduction
