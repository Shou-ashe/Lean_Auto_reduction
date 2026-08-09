/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Core

namespace ComplexityReduction
namespace Combinatorics

/-- Lightweight integer-programming schema for future NPC targets. -/
structure IntegerProgrammingInput where
  numVariables : Nat
  constraints : List (List Int × Int)
  deriving Repr

def integerProgrammingEncodedType : EncodedType :=
  EncodedType.raw IntegerProgrammingInput

/-- Structured finite-alphabet encoding for one integer coefficient row. -/
def intRowStructuredEncodedType : EncodedType :=
  EncodedType.list EncodedType.int

/-- Structured finite-alphabet encoding for one linear inequality row and bound. -/
def constraintStructuredEncodedType : EncodedType :=
  EncodedType.prod intRowStructuredEncodedType EncodedType.int

/-- Structured finite-alphabet encoding for a list of linear inequality constraints. -/
def constraintListStructuredEncodedType : EncodedType :=
  EncodedType.list constraintStructuredEncodedType

/-- Tuple-shaped finite-alphabet encoding for integer-programming fields. -/
def integerProgrammingTupleStructuredEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat constraintListStructuredEncodedType

/--
Concrete finite-alphabet integer-programming encoding with variable count and
linear inequality constraints.
-/
def integerProgrammingStructuredEncodedType : EncodedType where
  Carrier := IntegerProgrammingInput
  Symbol := integerProgrammingTupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I =>
    integerProgrammingTupleStructuredEncodedType.encode (I.numVariables, I.constraints)

/-- Binary-numeric finite-alphabet encoding for one integer coefficient row. -/
def intRowBinaryStructuredEncodedType : EncodedType :=
  EncodedType.list EncodedType.binaryInt

/-- Binary-numeric finite-alphabet encoding for one linear inequality row and bound. -/
def constraintBinaryStructuredEncodedType : EncodedType :=
  EncodedType.prod intRowBinaryStructuredEncodedType EncodedType.binaryInt

/-- Binary-numeric finite-alphabet encoding for a list of linear inequality constraints. -/
def constraintListBinaryStructuredEncodedType : EncodedType :=
  EncodedType.list constraintBinaryStructuredEncodedType

/-- Tuple-shaped binary-numeric encoding for integer-programming fields. -/
def integerProgrammingTupleBinaryStructuredEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat constraintListBinaryStructuredEncodedType

/--
Concrete binary-numeric finite-alphabet integer-programming encoding with
variable count and linear inequality constraints.
-/
def integerProgrammingBinaryStructuredEncodedType : EncodedType where
  Carrier := IntegerProgrammingInput
  Symbol := integerProgrammingTupleBinaryStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I =>
    integerProgrammingTupleBinaryStructuredEncodedType.encode (I.numVariables, I.constraints)

theorem intRowStructuredEncodedType_encode_injective :
    Function.Injective intRowStructuredEncodedType.encode :=
  EncodedType.list_encode_injective EncodedType.int_encode_injective

theorem constraintStructuredEncodedType_encode_injective :
    Function.Injective constraintStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    intRowStructuredEncodedType_encode_injective
    EncodedType.int_encode_injective

theorem constraintListStructuredEncodedType_encode_injective :
    Function.Injective constraintListStructuredEncodedType.encode :=
  EncodedType.list_encode_injective constraintStructuredEncodedType_encode_injective

theorem integerProgrammingTupleStructuredEncodedType_encode_injective :
    Function.Injective integerProgrammingTupleStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    EncodedType.nat_encode_injective
    constraintListStructuredEncodedType_encode_injective

theorem integerProgrammingStructuredEncodedType_encode_injective :
    Function.Injective integerProgrammingStructuredEncodedType.encode := by
  intro I J henc
  have htuple : (I.numVariables, I.constraints) = (J.numVariables, J.constraints) :=
    integerProgrammingTupleStructuredEncodedType_encode_injective (by
      simpa [integerProgrammingStructuredEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl⟩
  rfl

theorem intRowBinaryStructuredEncodedType_encode_injective :
    Function.Injective intRowBinaryStructuredEncodedType.encode :=
  EncodedType.list_encode_injective EncodedType.binaryInt_encode_injective

theorem constraintBinaryStructuredEncodedType_encode_injective :
    Function.Injective constraintBinaryStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    intRowBinaryStructuredEncodedType_encode_injective
    EncodedType.binaryInt_encode_injective

theorem constraintListBinaryStructuredEncodedType_encode_injective :
    Function.Injective constraintListBinaryStructuredEncodedType.encode :=
  EncodedType.list_encode_injective constraintBinaryStructuredEncodedType_encode_injective

theorem integerProgrammingTupleBinaryStructuredEncodedType_encode_injective :
    Function.Injective integerProgrammingTupleBinaryStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    EncodedType.binaryNat_encode_injective
    constraintListBinaryStructuredEncodedType_encode_injective

theorem integerProgrammingBinaryStructuredEncodedType_encode_injective :
    Function.Injective integerProgrammingBinaryStructuredEncodedType.encode := by
  intro I J henc
  have htuple : (I.numVariables, I.constraints) = (J.numVariables, J.constraints) :=
    integerProgrammingTupleBinaryStructuredEncodedType_encode_injective (by
      simpa [integerProgrammingBinaryStructuredEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl⟩
  rfl

def integerProgrammingDecisionProblem
    (P : IntegerProgrammingInput → Prop) : EncodedDecisionProblem where
  Instance := integerProgrammingEncodedType
  isYes := P

def integerProgrammingStructuredDecisionProblem
    (P : IntegerProgrammingInput → Prop) : EncodedDecisionProblem where
  Instance := integerProgrammingStructuredEncodedType
  isYes := P

/-- A 0-1 assignment for the integer-programming variables. -/
abbrev BoolAssignment : Type :=
  Nat → Bool

/-- Interpret a Boolean assignment as an integer value. -/
def boolValue (a : BoolAssignment) (i : Nat) : Int :=
  if a i then 1 else 0

/-- Dot product of an integer coefficient row with a Boolean assignment, starting at index `i`. -/
def rowValueFrom (a : BoolAssignment) : Nat → List Int → Int
  | _, [] => 0
  | i, c :: cs => c * boolValue a i + rowValueFrom a (i + 1) cs

/-- Dot product of an integer coefficient row with a Boolean assignment. -/
def rowValue (a : BoolAssignment) (row : List Int) : Int :=
  rowValueFrom a 0 row

/-- A row constraint is interpreted as `row ⋅ x ≤ bound`. -/
def SatisfiesConstraint (a : BoolAssignment) (constraint : List Int × Int) : Prop :=
  rowValue a constraint.1 ≤ constraint.2

/-- Semantic predicate for Karp's 0-1 integer programming target. -/
def ZeroOneIntegerProgramming (I : IntegerProgrammingInput) : Prop :=
  ∃ a : BoolAssignment, ∀ constraint ∈ I.constraints, SatisfiesConstraint a constraint

def zeroOneIntegerProgrammingDecisionProblem : EncodedDecisionProblem :=
  integerProgrammingDecisionProblem ZeroOneIntegerProgramming

def zeroOneIntegerProgrammingStructuredDecisionProblem : EncodedDecisionProblem :=
  integerProgrammingStructuredDecisionProblem ZeroOneIntegerProgramming

def integerProgrammingBinaryStructuredDecisionProblem
    (P : IntegerProgrammingInput → Prop) : EncodedDecisionProblem where
  Instance := integerProgrammingBinaryStructuredEncodedType
  isYes := P

def zeroOneIntegerProgrammingBinaryStructuredDecisionProblem : EncodedDecisionProblem :=
  integerProgrammingBinaryStructuredDecisionProblem ZeroOneIntegerProgramming

end Combinatorics
end ComplexityReduction
