import ComplexityReduction.Agent.Hardness.Authoring
import ComplexityReduction.Agent.Hardness.FiniteWitnessNative
import ComplexityReduction.Agent.Hardness.Gap

namespace Benchmark.Hardness.Inputs.TypedAuthoring.BoundedSubsetMembership

open ComplexityReduction
open ComplexityReduction.Encoding
open ComplexityReduction.Certificate
open ComplexityReduction.Program
open ComplexityReduction.Agent.Hardness.FiniteWitness
open ComplexityReduction.Agent.Hardness.FiniteWitnessNative

private def semantic : ComplexityReduction.DecisionProblem where
  Instance := Bool
  isYes := fun _ => True

@[complexity_reduction_ir_typed_problem]
def problem : PresentedProblem where
  semantic := semantic
  representation := StandardInstances.bool
  carrier_eq := rfl

abbrev source : PresentedProblem := problem

def checker :
    PolyProg (StandardInstances.prod problem.representation natListPresentation)
      StandardInstances.bool :=
  .const (StandardInstances.prod problem.representation natListPresentation)
    StandardInstances.bool true

def verifierData : NatListVerifierData problem where
  checker := checker
  witnessBound := fun _ => 0
  witnessBoundPoly := ComplexityReduction.PolynomialTimeBound.intro_with 0 0 0 (by
    intro input
    simp)
  correct := by
    intro input
    constructor
    · intro _
      refine ⟨[], ?_, ?_⟩
      · exact Nat.le_of_eq natListEncodedInputSize_nil
      · simp [checker]
    · intro _
      trivial
  checkerSound := by
    intro input candidate accepted
    trivial

def verifier : CertifiedVerifier problem := verifierData.toCertifiedVerifier

def witnessPresentation : verifier.witness.StructuralCertificate := by
  exact natListStructuralCertificate

noncomputable def discipline : CertifiedVerifierEncodingDiscipline verifier := by
  exact ComplexityReduction.Agent.Hardness.FiniteWitnessNative.discipline verifierData

theorem emptyWitness_is_boundedSubset : BoundedSubset 0 0 ([] : List Nat) := by
  simp [BoundedSubset, VerticesWithinBounds]

@[complexity_reduction_ir_typed_gap]
def gap : ComplexityReduction.Agent.Hardness.Gap.DeclaredComponentGap
    .verifierProgram .finalComposition problem problem :=
  .exact

@[complexity_reduction_ir_hardness_native_membership_template]
def template : ComplexityReduction.Agent.Hardness.Authoring.NativeMembershipTemplate
    problem verifier witnessPresentation discipline :=
  ⟨True.intro⟩

end Benchmark.Hardness.Inputs.TypedAuthoring.BoundedSubsetMembership
