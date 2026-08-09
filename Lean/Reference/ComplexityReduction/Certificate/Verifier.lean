/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.TMComplexityClasses
import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Program.CompileTM

/-!
Canonical V2 verifier certificates with backend direct-TM projections.

A certified verifier binds one exact presented problem, one exact witness representation, and one
typed checker program on their canonical product representation.  It can project only the current
backend `TMVerifier`/`TMInNP` evidence.  Native encoding-disciplined membership and Cook--Levin
capabilities require a separate V2 discipline certificate and are intentionally absent here.
This leaf imports only the generic program compiler dependency, not the broad `V2.Program`
aggregate.
-/

namespace ComplexityReduction
namespace Certificate

open Encoding Program

/-- The current direct-TM backend membership proposition for one exact presented problem. -/
abbrev BackendTMInNP (problem : PresentedProblem) : Prop :=
  ComplexityReduction.TMInNP problem.toEncodedDecisionProblem

/--
A typed V2 verifier for one exact problem and witness presentation.

The checker is one `PolyProg`, so its executable and direct-TM realization are fixed together.
`correct` supplies bounded witness completeness, while `checkerSound` is explicit because the
legacy `TMVerifier` API requires soundness for every accepted witness, including an over-bound
witness.  Neither field creates a native encoding-discipline capability.
-/
structure CertifiedVerifier (problem : PresentedProblem) where
  witness : LawfulEncodedType
  checker : PolyProg (StandardInstances.prod problem.representation witness) StandardInstances.bool
  witnessBound : problem.Instance → Nat
  witnessBoundPoly : ComplexityReduction.PolynomialTimeBound
    (fun input => problem.representation.encodedType.inputSize input) witnessBound
  correct : ∀ input, problem.accepts input ↔
    ∃ candidate, witness.encodedType.inputSize candidate ≤ witnessBound input ∧
      checker.run (input, candidate) = true
  checkerSound : ∀ input candidate, checker.run (input, candidate) = true → problem.accepts input

namespace CertifiedVerifier

/-- The direct-TM witness of a verifier is compiled from its one stored checker program. -/
def checkerTM {problem : PresentedProblem} (verifier : CertifiedVerifier problem) :
    ComplexityReduction.TMPolyTimeMap
      (StandardInstances.prod problem.representation verifier.witness).encodedType
      StandardInstances.bool.encodedType verifier.checker.run :=
  verifier.checker.compileTM

/-- The direct-TM witness compiled from the verifier's one exact checker program. -/
theorem checker_compileTM {problem : PresentedProblem} (verifier : CertifiedVerifier problem) :
    ComplexityReduction.TMPolyTimeMap
      (StandardInstances.prod problem.representation verifier.witness).encodedType
      StandardInstances.bool.encodedType verifier.checker.run :=
  verifier.checkerTM

/-- The named checker TM witness is definitionally the compilation of that same checker program. -/
@[simp]
theorem checkerTM_eq_compileTM {problem : PresentedProblem} (verifier : CertifiedVerifier problem) :
    verifier.checkerTM = verifier.checker.compileTM :=
  rfl

/-- Bounded witness completeness is indexed by the verifier's exact checker executable. -/
theorem accepts_iff_exists_bounded_checker {problem : PresentedProblem}
    (verifier : CertifiedVerifier problem) (input : problem.Instance) :
    problem.accepts input ↔
      ∃ candidate, verifier.witness.encodedType.inputSize candidate ≤ verifier.witnessBound input ∧
        verifier.checker.run (input, candidate) = true :=
  verifier.correct input

/-- Every accepted checker output is sound, including witnesses over the declared size bound. -/
theorem checker_all_witness_sound {problem : PresentedProblem}
    (verifier : CertifiedVerifier problem)
    (input : problem.Instance) (candidate : verifier.witness.Carrier)
    (accepted : verifier.checker.run (input, candidate) = true) :
    problem.accepts input :=
  verifier.checkerSound input candidate accepted

/-- Project the checker program and witness bound to the current backend direct-TM verifier. -/
def toTMVerifier {problem : PresentedProblem} (verifier : CertifiedVerifier problem) :
    ComplexityReduction.TMVerifier problem.toEncodedDecisionProblem where
  Cert := verifier.witness.encodedType
  verify := fun input candidate => verifier.checker.run (input, candidate)
  verifier_polytime := verifier.checker_compileTM
  cert_bound := by
    rcases verifier.witnessBoundPoly with ⟨degree, coefficient, offset, bound⟩
    refine ⟨degree, coefficient, offset, ?_⟩
    intro input accepted
    rcases (verifier.correct input).mp accepted with ⟨candidate, candidateBound, checkerAccepts⟩
    exact ⟨candidate, candidateBound.trans (bound input), checkerAccepts⟩
  sound := verifier.checkerSound

/-- Backend direct-TM NP membership derived from the exact checker compilation and witness bound. -/
theorem toBackendTMInNP {problem : PresentedProblem} (verifier : CertifiedVerifier problem) :
    BackendTMInNP problem :=
  ComplexityReduction.TMInNP.intro verifier.toTMVerifier

/-- Backend membership is introduced only from this verifier's exact backend projection. -/
@[simp]
theorem toBackendTMInNP_eq_intro {problem : PresentedProblem}
    (verifier : CertifiedVerifier problem) :
    verifier.toBackendTMInNP = ComplexityReduction.TMInNP.intro verifier.toTMVerifier :=
  rfl

/-- The backend verifier retains the exact witness encoded type. -/
@[simp]
theorem toTMVerifier_cert {problem : PresentedProblem} (verifier : CertifiedVerifier problem) :
    verifier.toTMVerifier.Cert = verifier.witness.encodedType :=
  rfl

/-- The backend verifier executes exactly the checker program. -/
@[simp]
theorem toTMVerifier_verify {problem : PresentedProblem} (verifier : CertifiedVerifier problem)
    (input : problem.Instance) (candidate : verifier.witness.Carrier) :
    verifier.toTMVerifier.verify input candidate = verifier.checker.run (input, candidate) :=
  rfl

/-- The backend verifier's direct-TM field is the compilation of its exact checker program. -/
@[simp]
theorem toTMVerifier_polytime {problem : PresentedProblem} (verifier : CertifiedVerifier problem) :
    verifier.toTMVerifier.verifier_polytime = verifier.checkerTM :=
  rfl

/-- The backend verifier retains bounded completeness using the exact witness bound. -/
theorem toTMVerifier_bounded_correct_iff {problem : PresentedProblem}
    (verifier : CertifiedVerifier problem) (input : problem.Instance) :
    problem.accepts input ↔
      ∃ candidate, verifier.witness.encodedType.inputSize candidate ≤ verifier.witnessBound input ∧
        verifier.toTMVerifier.verify input candidate = true := by
  simpa only [toTMVerifier_verify] using verifier.accepts_iff_exists_bounded_checker input

/-- The backend verifier's all-witness soundness is exactly the checker soundness stored in V2. -/
theorem toTMVerifier_all_witness_sound {problem : PresentedProblem}
    (verifier : CertifiedVerifier problem) (input : problem.Instance)
    (candidate : verifier.witness.Carrier)
    (accepted : verifier.toTMVerifier.verify input candidate = true) :
    problem.accepts input := by
  exact verifier.checker_all_witness_sound input candidate (by
    simpa only [toTMVerifier_verify] using accepted)

/--
Backend verifier semantic correctness follows from bounded completeness and all-witness soundness.
-/
theorem toTMVerifier_correct_iff {problem : PresentedProblem} (verifier : CertifiedVerifier problem)
    (input : problem.Instance) :
    problem.accepts input ↔ ∃ candidate, verifier.toTMVerifier.verify input candidate = true :=
  ComplexityReduction.TMVerifier.correct_iff verifier.toTMVerifier input

/--
After erasing the explicit witness-size bound, backend correctness is still exactly correctness
of the stored checker program. This is a backend projection only: it does not create native
encoding-discipline authority.
-/
theorem toTMVerifier_correct_iff_checker {problem : PresentedProblem}
    (verifier : CertifiedVerifier problem) (input : problem.Instance) :
    problem.accepts input ↔ ∃ candidate, verifier.checker.run (input, candidate) = true := by
  simpa only [toTMVerifier_verify] using verifier.toTMVerifier_correct_iff input

/--
The coherent direct-TM view of one certified checker's exact `PolyProg`.

This invariant deliberately packages every backend projection that must remain attached to one
program: its executable, compiled direct-TM evidence, exact encoded-size bound, both bounded
correctness views, all-witness soundness, and the ordinary backend correctness theorem. It does
not contain an encoding discipline or native capability, so it cannot promote backend `TMInNP`
evidence across the V2-native boundary.
-/
structure CheckerProgramInvariant {problem : PresentedProblem}
    (verifier : CertifiedVerifier problem) : Prop where
  /-- The backend verifier executes precisely the stored checker program. -/
  backendRun : ∀ input candidate,
    verifier.toTMVerifier.verify input candidate = verifier.checker.run (input, candidate)
  /-- The backend verifier's only direct-TM witness is compilation of that checker program. -/
  backendDirectTM : verifier.toTMVerifier.verifier_polytime = verifier.checker.compileTM
  /-- The polynomial witness bound is the exact bound stored alongside the checker program. -/
  witnessBoundPolynomial : ComplexityReduction.PolynomialTimeBound
    (fun input => problem.representation.encodedType.inputSize input) verifier.witnessBound
  /-- The original V2 correctness field is about this exact stored checker executable. -/
  checkerBoundedCorrectness : ∀ input,
    problem.accepts input ↔
      ∃ candidate, verifier.witness.encodedType.inputSize candidate ≤ verifier.witnessBound input ∧
        verifier.checker.run (input, candidate) = true
  /-- Bounded completeness uses that same bound and the backend execution of that checker. -/
  boundedCorrectness : ∀ input,
    problem.accepts input ↔
      ∃ candidate, verifier.witness.encodedType.inputSize candidate ≤ verifier.witnessBound input ∧
        verifier.toTMVerifier.verify input candidate = true
  /-- Soundness is for every witness accepted by the same backend checker execution. -/
  allWitnessSoundness : ∀ input candidate,
    verifier.toTMVerifier.verify input candidate = true → problem.accepts input
  /-- Forgetting the bound preserves correctness for this checker-backed backend verifier only. -/
  backendCorrectness : ∀ input,
    problem.accepts input ↔ ∃ candidate, verifier.toTMVerifier.verify input candidate = true

/--
Construct the coherent backend invariant from a certified verifier's one stored checker program.

The construction only repackages the fields and projections of `CertifiedVerifier`; it creates no
second checker, TM, witness bound, or native encoding-discipline evidence.
-/
def checkerProgramInvariant {problem : PresentedProblem} (verifier : CertifiedVerifier problem) :
    CheckerProgramInvariant verifier where
  backendRun := verifier.toTMVerifier_verify
  backendDirectTM := verifier.toTMVerifier_polytime
  witnessBoundPolynomial := verifier.witnessBoundPoly
  checkerBoundedCorrectness := verifier.accepts_iff_exists_bounded_checker
  boundedCorrectness := verifier.toTMVerifier_bounded_correct_iff
  allWitnessSoundness := verifier.toTMVerifier_all_witness_sound
  backendCorrectness := verifier.toTMVerifier_correct_iff

/--
The backend `TMInNP` projection has one coherent source: the certified verifier's stored
checker program.  In particular, the membership witness, its direct-TM computation, the
witness-size bound, and both bounded and ordinary semantics all refer to the same checker.

This is intentionally a theorem about the erased backend projection only.  It supplies no
`CertifiedVerifierEncodingDiscipline` and therefore cannot be used as native verifier authority.
-/
theorem backendMembership_checkerProgram_chain {problem : PresentedProblem}
    (verifier : CertifiedVerifier problem) :
    verifier.toBackendTMInNP = ComplexityReduction.TMInNP.intro verifier.toTMVerifier ∧
      (∀ input candidate,
        verifier.toTMVerifier.verify input candidate = verifier.checker.run (input, candidate)) ∧
      verifier.toTMVerifier.verifier_polytime = verifier.checker.compileTM ∧
      ComplexityReduction.PolynomialTimeBound
        (fun input => problem.representation.encodedType.inputSize input) verifier.witnessBound ∧
      (∀ input, problem.accepts input ↔
        ∃ candidate, verifier.witness.encodedType.inputSize candidate ≤ verifier.witnessBound input ∧
          verifier.checker.run (input, candidate) = true) ∧
      (∀ input, problem.accepts input ↔
        ∃ candidate, verifier.checker.run (input, candidate) = true) := by
  refine ⟨verifier.toBackendTMInNP_eq_intro, ?_,
    verifier.toTMVerifier_polytime, verifier.witnessBoundPoly,
    verifier.accepts_iff_exists_bounded_checker, verifier.toTMVerifier_correct_iff_checker⟩
  intro input candidate
  exact verifier.toTMVerifier_verify input candidate

end CertifiedVerifier
end Certificate
end ComplexityReduction
