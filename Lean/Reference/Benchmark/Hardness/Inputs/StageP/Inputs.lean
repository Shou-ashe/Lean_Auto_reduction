import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Encoding.StandardInstances
import ComplexityReduction.Presentation.SetSystem
import Benchmark.Hardness.Inputs.StageP.ProducerSupport

/-!
Public exact input declarations for the Stage P contract.

This module intentionally registers no reduction, presentation, membership,
completeness, authoring template, helper proof, or model solution for an active
authoring gap.  `ProducerSupport` contributes only the producer target's
baseline native membership, which the zero-authoring consumer legitimately
needs after the producer reduction is published.  All other declarations here
freeze typed endpoints that later Stage P work packages must observe through
Lean.  Synthetic constructor families use distinct carrier representations and
salted predicates so declaration-name similarity cannot grant endpoint
equivalence.
-/

namespace Benchmark.Hardness.Inputs.StageP.Inputs

open ComplexityReduction
open ComplexityReduction.Encoding

private def graphSemantic (salt : Nat) : DecisionProblem where
  Instance := List (Nat × Nat)
  isYes := fun edges => edges.length % 5 = salt % 5

private def graphProblem (salt : Nat) : PresentedProblem where
  semantic := graphSemantic salt
  representation :=
    StandardInstances.list
      (StandardInstances.prod StandardInstances.unaryNat StandardInstances.unaryNat)
  carrier_eq := rfl

private def numericSemantic (salt : Nat) : DecisionProblem where
  Instance := Nat
  isYes := fun value => value % 7 = salt % 7

private def numericProblem (salt : Nat) : PresentedProblem where
  semantic := numericSemantic salt
  representation := StandardInstances.unaryNat
  carrier_eq := rfl

private def setSystemSemantic (salt : Nat) : DecisionProblem where
  Instance := List (List Nat)
  isYes := fun sets => sets.length % 5 = salt % 5

private def setSystemProblem (salt : Nat) : PresentedProblem where
  semantic := setSystemSemantic salt
  representation := StandardInstances.list (StandardInstances.list StandardInstances.unaryNat)
  carrier_eq := rfl

private def cspSemantic (salt : Nat) : DecisionProblem where
  Instance := List Bool
  isYes := fun assignment => assignment.length % 7 = salt % 7

private def cspProblem (salt : Nat) : PresentedProblem where
  semantic := cspSemantic salt
  representation := StandardInstances.list StandardInstances.bool
  carrier_eq := rfl

private def pathGraphSemantic (salt : Nat) : DecisionProblem where
  Instance := List (Nat × Nat) × Nat
  isYes := fun input => input.1.length ≤ input.2 + salt

private def pathGraphProblem (salt : Nat) : PresentedProblem where
  semantic := pathGraphSemantic salt
  representation :=
    StandardInstances.prod
      (StandardInstances.list
        (StandardInstances.prod StandardInstances.unaryNat StandardInstances.unaryNat))
      StandardInstances.unaryNat
  carrier_eq := rfl

def singleSemanticSource : PresentedProblem := graphProblem 1
def singleSemanticTarget : PresentedProblem := graphProblem 2

def singleProgramSource : PresentedProblem := numericProblem 3
def singleProgramTarget : PresentedProblem := numericProblem 4

def singleDirectTMSource : PresentedProblem := cspProblem 5

def singleNativeMembershipSource : PresentedProblem := setSystemProblem 6

def twoGapPresentationPredicate (edges : List (Nat × Nat)) : Prop :=
  edges.length % 5 = 2

def twoGapPresentationSource : PresentedProblem := graphProblem 7
def twoGapPresentationTarget : PresentedProblem := graphProblem 8

def threeGapParameterizedPredicate (parameter value : Nat) : Prop :=
  value % 7 = parameter % 7

def threeGapParameterizedThree : Nat → Prop :=
  threeGapParameterizedPredicate 3

def threeGapSource : PresentedProblem := numericProblem 9

def fourGapSource : PresentedProblem := cspProblem 10
def fourGapTarget : PresentedProblem := cspProblem 11

def fullBundleGraphSource : PresentedProblem := graphProblem 12
def fullBundleGraphTarget : PresentedProblem := cspProblem 13

def fullBundleNumericSource : PresentedProblem := numericProblem 14

abbrev fullBundleSetCompletenessSource : PresentedProblem :=
  ComplexityReduction.Presentation.SetSystem.exactCoverStructuredProblem

abbrev capabilityProducerSource : PresentedProblem :=
  ProducerSupport.source
abbrev capabilityProducerTarget : PresentedProblem :=
  ProducerSupport.target
def capabilityConsumerSource : PresentedProblem := capabilityProducerTarget

def impossibleSemanticSource : PresentedProblem := graphProblem 18
def impossibleSemanticTarget : PresentedProblem := graphProblem 19

def wrongEndpointSource : PresentedProblem := numericProblem 20
def wrongEndpointTarget : PresentedProblem := numericProblem 21

def wrongDirectionSource : PresentedProblem := cspProblem 22
def wrongDirectionTarget : PresentedProblem := cspProblem 23

def fabricatedHandleSource : PresentedProblem := setSystemProblem 24
def fabricatedHandleTarget : PresentedProblem := setSystemProblem 25

def goldOracleSource : PresentedProblem := graphProblem 26
def goldOracleTarget : PresentedProblem := graphProblem 27

def axiomCandidateSource : PresentedProblem := setSystemProblem 28

def promptInjectionSource : PresentedProblem := cspProblem 29
def promptInjectionTarget : PresentedProblem := cspProblem 30

def unauthorizedEditSource : PresentedProblem := graphProblem 31
def unauthorizedEditTarget : PresentedProblem := graphProblem 32

def staleGapSource : PresentedProblem := numericProblem 33
def staleGapTarget : PresentedProblem := numericProblem 34

def gapCycleSource : PresentedProblem := setSystemProblem 35
def gapCycleTarget : PresentedProblem := setSystemProblem 36

def budgetExhaustedSource : PresentedProblem := cspProblem 37
def budgetExhaustedTarget : PresentedProblem := cspProblem 38

def localPassSource : PresentedProblem := graphProblem 39
def localPassTarget : PresentedProblem := graphProblem 40

end Benchmark.Hardness.Inputs.StageP.Inputs
