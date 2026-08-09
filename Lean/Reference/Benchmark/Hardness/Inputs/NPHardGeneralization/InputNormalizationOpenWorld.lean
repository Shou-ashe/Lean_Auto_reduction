import ComplexityReduction.Encoding.StandardInstances
import ComplexityReduction.Encoding.PresentedProblem

/-!
H-D input-normalization fixtures.  None of these declarations is registered:
the production resolver must derive every relationship from Lean elaboration
over this module's import closure.
-/

namespace Benchmark.Hardness.Inputs.NPHardGeneralization.InputNormalizationOpenWorld

open ComplexityReduction
open ComplexityReduction.Encoding

def uniqueRepresentation : LawfulEncodedType :=
  StandardInstances.sum StandardInstances.bool
    (StandardInstances.list StandardInstances.bool)

def uniqueSemantic : DecisionProblem where
  Instance := uniqueRepresentation.Carrier
  isYes := fun _ => True

def uniqueProblem : PresentedProblem where
  semantic := uniqueSemantic
  representation := uniqueRepresentation
  carrier_eq := rfl

def uniqueEncoding : LawfulEncodedType := uniqueProblem.representation

def missingEncoding : LawfulEncodedType :=
  StandardInstances.list
    (StandardInstances.sum StandardInstances.bool StandardInstances.bool)

def ambiguousRepresentation : LawfulEncodedType :=
  StandardInstances.prod StandardInstances.bool StandardInstances.bool

def ambiguousFirstSemantic : DecisionProblem where
  Instance := ambiguousRepresentation.Carrier
  isYes := fun input => input.1 = true

def ambiguousSecondSemantic : DecisionProblem where
  Instance := ambiguousRepresentation.Carrier
  isYes := fun input => input.2 = true

def ambiguousFirst : PresentedProblem where
  semantic := ambiguousFirstSemantic
  representation := ambiguousRepresentation
  carrier_eq := rfl

def ambiguousSecond : PresentedProblem where
  semantic := ambiguousSecondSemantic
  representation := ambiguousRepresentation
  carrier_eq := rfl

def ambiguousEncoding : LawfulEncodedType := ambiguousRepresentation

end Benchmark.Hardness.Inputs.NPHardGeneralization.InputNormalizationOpenWorld
