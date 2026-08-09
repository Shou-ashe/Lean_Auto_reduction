import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.NativeCookLevin
import ComplexityReduction.Problems.Karp21.CliqueNativeVerifier

/-!
Public support declarations for the Stage P producer/consumer wave.

The target deliberately has the same lawful representation as canonical
structured Clique but a propositionally, not definitionally, equal predicate.
Consequently the production registry cannot reuse Clique capabilities merely
through endpoint `isDefEq`; an exact reduction into this fresh endpoint still
has to be authored and published.  Native membership is public support for the
consumer's completeness closure and is transported only across a proved exact
`PresentedProblem` equality.
-/

namespace Benchmark.Hardness.Inputs.StageP.ProducerSupport

open ComplexityReduction
open ComplexityReduction.Certificate
open ComplexityReduction.Encoding

/-- Add a logically inert conjunct without making the endpoint definitionally equal. -/
def strengthenedProblem (problem : PresentedProblem) : PresentedProblem where
  semantic := {
    Instance := problem.semantic.Instance
    isYes := fun input => problem.semantic.isYes input ∧ True
  }
  representation := problem.representation
  carrier_eq := problem.carrier_eq

/-- The strengthened predicate is propositionally the same exact problem. -/
theorem strengthenedProblem_eq (problem : PresentedProblem) :
    strengthenedProblem problem = problem := by
  cases problem with
  | mk semantic representation carrier_eq =>
      cases semantic with
      | mk Instance isYes =>
          simp [strengthenedProblem]

/-- The known native-complete graph endpoint used as the producer source. -/
abbrev source : PresentedProblem :=
  ComplexityReduction.Problems.Karp21.GraphAtoms.cliqueStructuredProblem

/-- A fresh exact graph endpoint that is not definitionally equal to `source`. -/
def target : PresentedProblem := strengthenedProblem source

/-- Public semantic transport used only to build exact target-local support. -/
theorem target_eq_source : target = source := strengthenedProblem_eq source

/-- The target's native membership is available before the producer wave. -/
@[complexity_reduction_ir_typed_native_membership]
theorem targetNativeTMInNP : NativeTMInNP target := by
  rw [target_eq_source]
  exact ComplexityReduction.Problems.Karp21.CliqueNativeVerifier.nativeTMInNP

end Benchmark.Hardness.Inputs.StageP.ProducerSupport
