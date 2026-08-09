/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Certificate.NativeCompleteness
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeSATTMRoot
import ComplexityReduction.Problems.Karp21.ThreeSATNativeVerifier

/-!
Native checked Cook--Levin certificates for the canonical structured-3SAT endpoint.

This trusted library leaf is the sole owner of the native Cook--Levin root used by the
hardness agent.  It consumes the exact verifier and checked-decoder discipline already packaged
by `NativeVerifierCapability`, reuses CR's proved structured Cook--Levin executable and direct-TM
witness, and stores that same executable as one V2 `Primitive`/`PolyProg`.

The agent runtime only calls `reduce`; it does not define a tableau map, semantic theorem, verifier
machine, or complexity witness.
-/

namespace ComplexityReduction
namespace Certificate
namespace NativeCookLevin

open Encoding Program

/-- The unique canonical target of the native Cook--Levin lane. -/
abbrev canonicalThreeSAT : PresentedProblem :=
  Problems.Karp21.Satisfiability.threeSATStructuredProblem

/--
Construct the exact structured-3SAT reduction from one verifier/discipline capability.

The legacy record used below is only the existing proved direct-TM implementation.  The V2
certificate is constructed from its executable, its direct-TM field, and its semantic theorem at
the exact `PresentedProblem` endpoints; no backend membership proposition is promoted here.
-/
noncomputable def reduceOfCapability {source : PresentedProblem}
    (capability : NativeVerifierCapability source) :
    CertifiedReduction source canonicalThreeSAT := by
  let legacyReduction :=
    ComplexityReduction.SAT.checkedXOnlyCookLevinStructuredTMKarpReduction
      capability.discipline.backendDiscipline.toCheckedSuffixValidity
  exact {
    program := .atom <| Primitive.ofTMPolyTime
      legacyReduction.f legacyReduction.polytime
    correct := by
      intro input
      exact legacyReduction.correct input
  }

/-- Exact native membership selects its packaged verifier/discipline and yields Cook--Levin. -/
noncomputable def reduce {source : PresentedProblem} (membership : NativeTMInNP source) :
    CertifiedReduction source canonicalThreeSAT :=
  reduceOfCapability (Classical.choice membership)

/-- Canonical structured 3SAT is complete for the exact native verifier discipline. -/
@[complexity_reduction_ir_typed_complete]
theorem canonicalThreeSATNativeCompleteness : NativeTMNPComplete canonicalThreeSAT where
  membership :=
    Problems.Karp21.ThreeSATNativeVerifier.threeSATStructuredNativeTMInNP
  hardness := fun _source sourceMembership => ⟨reduce sourceMembership⟩

end NativeCookLevin
end Certificate
end ComplexityReduction

assert_standard_axioms
  ComplexityReduction.Certificate.NativeCookLevin.reduceOfCapability,
  ComplexityReduction.Certificate.NativeCookLevin.reduce,
  ComplexityReduction.Certificate.NativeCookLevin.canonicalThreeSATNativeCompleteness
