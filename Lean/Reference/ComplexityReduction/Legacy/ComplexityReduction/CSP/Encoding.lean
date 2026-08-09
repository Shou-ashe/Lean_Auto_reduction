/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.List.OfFn
import ComplexityReduction.Legacy.ComplexityReduction.Core.EncodedDecisionProblem
import ComplexityReduction.Legacy.ComplexityReduction.CSP.Formula

/-!
Concrete finite-alphabet encodings for Boolean CSP formulas.

The relation language is fixed, so relation symbols are part of the alphabet.
Variable names are encoded in unary using the project-wide natural-number
encoding, with a delimiter before every constraint and every variable field.
-/

namespace ComplexityReduction
namespace CSP

open ComplexityReduction

/-- The finite alphabet used to encode formulas over a fixed CSP language. -/
abbrev FormulaSymbol (Γ : BoolLanguage) : Type :=
  Option (Γ.Symbol ⊕ Bool)

namespace Encoding

/-- Field delimiter. -/
def delimiter {Γ : BoolLanguage} : FormulaSymbol Γ :=
  none

/-- A relation symbol token. -/
def relationToken {Γ : BoolLanguage} (s : Γ.Symbol) : FormulaSymbol Γ :=
  some (Sum.inl s)

/-- A unary natural-number bit token. -/
def bitToken {Γ : BoolLanguage} (b : Bool) : FormulaSymbol Γ :=
  some (Sum.inr b)

/-- Encode a variable name using the shared unary `Nat` encoding. -/
def encodeNat {Γ : BoolLanguage} (n : Nat) : List (FormulaSymbol Γ) :=
  (EncodedType.nat.encode n).map bitToken

/-- Encode one variable field. -/
def encodeVar {Γ : BoolLanguage} (n : Nat) : List (FormulaSymbol Γ) :=
  [delimiter] ++ encodeNat n

/-- Encode one constraint as a relation symbol followed by its variable tuple. -/
def encodeConstraint {Γ : BoolLanguage} (c : Constraint Γ) : List (FormulaSymbol Γ) :=
  [delimiter, relationToken c.symbol] ++ (List.ofFn c.vars).flatMap encodeVar

/-- Encode a CSP formula as the concatenation of encoded constraints. -/
def encodeFormula {Γ : BoolLanguage} (φ : Formula Γ) : List (FormulaSymbol Γ) :=
  φ.flatMap encodeConstraint

@[simp]
theorem encodeFormula_nil {Γ : BoolLanguage} :
    encodeFormula ([] : Formula Γ) = [] :=
  rfl

@[simp]
theorem encodeFormula_cons {Γ : BoolLanguage} (c : Constraint Γ) (φ : Formula Γ) :
    encodeFormula (c :: φ) = encodeConstraint c ++ encodeFormula φ :=
  rfl

end Encoding

/-- Encoded instances for formulas over a fixed Boolean CSP language. -/
def formulaEncodedType (Γ : BoolLanguage) : EncodedType :=
  { Carrier := Formula Γ
    Symbol := FormulaSymbol Γ
    finite_symbol := inferInstance
    encode := Encoding.encodeFormula }

end CSP
end ComplexityReduction
