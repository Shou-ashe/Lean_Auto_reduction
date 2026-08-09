/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Presentation.FiniteDomainCSP

/-!
Explicit executable-template data for generic finite-domain CSP languages.

`ComplexityReduction.CSP.FiniteDomain.Language` stores relation membership as
a proposition-valued predicate.  This leaf adds no automatic conversion from
that predicate.  Instead, a producer may provide one numeric domain coding and
one finite numeric row family whose membership agrees exactly with every
relation predicate.  Downstream domain gadgets can then inspect rows with a
Boolean list-membership test without recovering semantic data from a formula
code.

The contract is indexed by the exact source language.  It is data in `Type`,
not a proof-only table statement, and it carries no route, program, machine, or
certificate claim by itself.
-/

namespace ComplexityReduction
namespace Domain
namespace FiniteDomainCSPExecutableContract

open ComplexityReduction.CSP.FiniteDomain

/-- Encode one typed tuple through an explicitly selected finite-domain equivalence. -/
def encodeTuple {D : Type} {size arity : Nat} (domainEquiv : D ≃ Fin size)
    (tuple : Tuple D arity) : List Nat :=
  List.ofFn fun index => (domainEquiv (tuple index)).val

/--
Caller-supplied executable data for one exact finite-domain CSP language.

Rows use natural-number domain codes so membership is decidable without a
runtime value of the source domain.  The final field is the semantic bridge:
the stored rows describe exactly, rather than merely soundly, each source
relation.
-/
structure ExecutableLanguageContract {D : Type} (Γ : Language D) where
  domainSize : Nat
  domainEquiv : D ≃ Fin domainSize
  relationRows : (symbol : Γ.Symbol) → List (List Nat)
  relationRows_shape :
    ∀ symbol row, row ∈ relationRows symbol →
      row.length = (Γ.relationOf symbol).arity ∧
        ∀ value, value ∈ row → value < domainSize
  holds_iff_encodedTuple_mem :
    ∀ symbol tuple,
      (Γ.relationOf symbol).Holds tuple ↔
        encodeTuple domainEquiv tuple ∈ relationRows symbol

namespace ExecutableLanguageContract

/-- Encode one source-domain value using the contract's explicit finite code. -/
def valueCode {D : Type} {Γ : Language D} (contract : ExecutableLanguageContract Γ)
    (value : D) : Nat :=
  (contract.domainEquiv value).val

/-- Encode one typed tuple using the contract's explicit finite code. -/
def tupleCode {D : Type} {Γ : Language D} (contract : ExecutableLanguageContract Γ)
    {arity : Nat} (tuple : Tuple D arity) : List Nat :=
  encodeTuple contract.domainEquiv tuple

/-- Numeric relation-row membership supplied by the selected contract. -/
def relationLookup {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) (symbol : Γ.Symbol)
    (row : List Nat) : Bool :=
  decide (row ∈ contract.relationRows symbol)

/-- Every encoded domain value is inside the selected numeric domain. -/
theorem valueCode_lt_domainSize {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) (value : D) :
    contract.valueCode value < contract.domainSize :=
  (contract.domainEquiv value).isLt

/-- Tuple coding preserves the relation arity exactly. -/
@[simp]
theorem tupleCode_length {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) {arity : Nat}
    (tuple : Tuple D arity) :
    (contract.tupleCode tuple).length = arity := by
  simp [tupleCode, encodeTuple]

/-- The Boolean lookup reports exactly numeric row membership. -/
@[simp]
theorem relationLookup_eq_true_iff_mem {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) (symbol : Γ.Symbol)
    (row : List Nat) :
    contract.relationLookup symbol row = true ↔
      row ∈ contract.relationRows symbol := by
  simp [relationLookup]

/-- Lookup of an encoded typed tuple agrees exactly with the source relation. -/
theorem relationLookup_tupleCode_eq_true_iff_holds {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) (symbol : Γ.Symbol)
    (tuple : Tuple D (Γ.relationOf symbol).arity) :
    contract.relationLookup symbol (contract.tupleCode tuple) = true ↔
      (Γ.relationOf symbol).Holds tuple := by
  rw [relationLookup_eq_true_iff_mem]
  exact (contract.holds_iff_encodedTuple_mem symbol tuple).symm

/-- Stored rows expose their exact arity equation. -/
theorem row_length_eq_arity {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) (symbol : Γ.Symbol)
    (row : List Nat) (hrow : row ∈ contract.relationRows symbol) :
    row.length = (Γ.relationOf symbol).arity :=
  (contract.relationRows_shape symbol row hrow).1

/-- Every entry of a stored row lies inside the explicit numeric domain. -/
theorem row_value_lt_domainSize {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) (symbol : Γ.Symbol)
    (row : List Nat) (hrow : row ∈ contract.relationRows symbol)
    (value : Nat) (hvalue : value ∈ row) :
    value < contract.domainSize :=
  (contract.relationRows_shape symbol row hrow).2 value hvalue

end ExecutableLanguageContract
end FiniteDomainCSPExecutableContract
end Domain
end ComplexityReduction
