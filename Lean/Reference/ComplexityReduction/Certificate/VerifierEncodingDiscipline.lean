/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.TMEncodingDiscipline
import ComplexityReduction.Certificate.Verifier

/-!
Canonical V2 verifier encoding discipline.

The discipline is indexed by one exact certified verifier, and hence by its exact problem and
witness representation.  It is intentionally distinct from the backend `TMInNP` proposition:
backend direct-TM membership does not contain the structural or executable encoding information
required for V2-native capability.
-/

namespace ComplexityReduction
namespace Certificate

universe u v

open Encoding Program

/--
Explicit executable data for a verifier's exact witness representation.

`canonicalize` is a shared typed program, not a new checker TM.  The two laws make its relation
to the verifier explicit; future Cook--Levin work may consume stronger concrete decoder data
through this constructor without granting any capability to a bare encoding equivalence.
-/
structure ExecutableVerifierEncodingData {problem : PresentedProblem}
    (verifier : CertifiedVerifier problem) where
  canonicalize : PolyProg verifier.witness verifier.witness
  canonicalize_idempotent : ∀ candidate,
    canonicalize.run (canonicalize.run candidate) = canonicalize.run candidate
  checker_canonicalize : ∀ input candidate,
    verifier.checker.run (input, canonicalize.run candidate) = verifier.checker.run (input, candidate)

namespace ExecutableVerifierEncodingData

/-- The explicit canonicalizer compiles from its own exact typed program. -/
theorem canonicalize_compileTM {problem : PresentedProblem} {verifier : CertifiedVerifier problem}
    (data : ExecutableVerifierEncodingData verifier) :
    ComplexityReduction.TMPolyTimeMap verifier.witness.encodedType verifier.witness.encodedType
      data.canonicalize.run :=
  data.canonicalize.compileTM

end ExecutableVerifierEncodingData

/-- The sole trusted basis for a V2 verifier encoding discipline. -/
inductive VerifierEncodingDisciplineBasis {problem : PresentedProblem}
    (verifier : CertifiedVerifier problem) : Type 2 where
  | checkedDecoder
      (backendDiscipline :
        ComplexityReduction.SAT.TMVerifierEncodingDiscipline verifier.toTMVerifier) :
    VerifierEncodingDisciplineBasis verifier

/--
A V2-native encoding discipline for one exact verifier.

No backend theorem, injectivity proof, arbitrary function, carrier equality, or bare equivalence
appears in this type's constructors.  This MVP records the admission boundary only; it deliberately
does not construct a generic Cook--Levin reduction.
-/
structure CertifiedVerifierEncodingDiscipline {problem : PresentedProblem}
    (verifier : CertifiedVerifier problem) : Type 2 where
  basis : VerifierEncodingDisciplineBasis verifier

namespace CertifiedVerifierEncodingDiscipline

/-- The exact witness presentation indexed by the verifier discipline. -/
def witnessRepresentation {problem : PresentedProblem} {verifier : CertifiedVerifier problem}
    (_ : CertifiedVerifierEncodingDiscipline verifier) : LawfulEncodedType :=
  verifier.witness

/-- The witness representation of a discipline is definitionally the verifier's witness representation. -/
theorem witnessRepresentation_eq {problem : PresentedProblem} {verifier : CertifiedVerifier problem}
    (discipline : CertifiedVerifierEncodingDiscipline verifier) :
    discipline.witnessRepresentation = verifier.witness :=
  rfl

/-- Build native discipline only from the exact CR checked-decoder contract. -/
def ofCheckedDecoder {problem : PresentedProblem} {verifier : CertifiedVerifier problem}
    (backendDiscipline :
      ComplexityReduction.SAT.TMVerifierEncodingDiscipline verifier.toTMVerifier) :
    CertifiedVerifierEncodingDiscipline verifier :=
  ⟨.checkedDecoder backendDiscipline⟩

/-- Recover the exact CR discipline stored by a native V2 discipline. -/
def backendDiscipline {problem : PresentedProblem} {verifier : CertifiedVerifier problem}
    (discipline : CertifiedVerifierEncodingDiscipline verifier) :
    ComplexityReduction.SAT.TMVerifierEncodingDiscipline verifier.toTMVerifier :=
  match discipline.basis with
  | .checkedDecoder backendDiscipline => backendDiscipline

/-- Recover the checked suffix decoder for the exact backend verifier. -/
def checkedSuffixDecoder {problem : PresentedProblem} {verifier : CertifiedVerifier problem}
    (discipline : CertifiedVerifierEncodingDiscipline verifier) :=
  discipline.backendDiscipline.checkedSuffixDecoder

@[simp]
theorem backendDiscipline_ofCheckedDecoder {problem : PresentedProblem}
    {verifier : CertifiedVerifier problem}
    (backendDiscipline :
      ComplexityReduction.SAT.TMVerifierEncodingDiscipline verifier.toTMVerifier) :
    (ofCheckedDecoder backendDiscipline).backendDiscipline = backendDiscipline :=
  rfl

/-- Every canonical discipline exposes one exact checked-decoder contract. -/
theorem checkedDecoderProvenance {problem : PresentedProblem} {verifier : CertifiedVerifier problem}
    (discipline : CertifiedVerifierEncodingDiscipline verifier)
    {motive : Prop}
    (checkedDecoder : ∀ _ :
      ComplexityReduction.SAT.TMVerifierEncodingDiscipline verifier.toTMVerifier, motive) :
    motive := by
  cases discipline with
  | mk basis =>
      cases basis with
      | checkedDecoder backendDiscipline =>
          exact checkedDecoder backendDiscipline

/-- A discipline can safely forget to the backend membership of its exact verifier only. -/
theorem toBackendTMInNP {problem : PresentedProblem} {verifier : CertifiedVerifier problem}
    (_ : CertifiedVerifierEncodingDiscipline verifier) :
    BackendTMInNP problem :=
  verifier.toBackendTMInNP

end CertifiedVerifierEncodingDiscipline

/--
V2-native membership capability for one exact presented problem.

The dependent pair records one exact `CertifiedVerifier` followed by the encoding discipline
indexed by that very verifier.  Its public introduction/elimination API below keeps this pairing
explicit.  It is not definitionally equal to the backend `TMInNP` proposition, nor can backend
or legacy evidence fill either component.
-/
def NativeVerifierCapability (problem : PresentedProblem) : Type 2 :=
  Σ verifier : CertifiedVerifier problem, CertifiedVerifierEncodingDiscipline verifier

/-- V2-native NP membership: nonempty native verifier/discipline capability. -/
def NativeTMInNP (problem : PresentedProblem) : Prop :=
  Nonempty (NativeVerifierCapability problem)

namespace NativeVerifierCapability

/-- Build a native capability only from an exact verifier and its exact indexed discipline. -/
def mk {problem : PresentedProblem} (verifier : CertifiedVerifier problem)
    (discipline : CertifiedVerifierEncodingDiscipline verifier) :
    NativeVerifierCapability problem :=
  ⟨verifier, discipline⟩

/-- Recover the exact verifier packaged by a native capability. -/
def verifier {problem : PresentedProblem}
    (capability : NativeVerifierCapability problem) : CertifiedVerifier problem :=
  capability.1

/-- Recover the exact discipline indexed by the verifier packaged by this capability. -/
def discipline {problem : PresentedProblem}
    (capability : NativeVerifierCapability problem) :
    CertifiedVerifierEncodingDiscipline capability.verifier :=
  capability.2

@[simp]
theorem verifier_mk {problem : PresentedProblem} (verifier : CertifiedVerifier problem)
    (discipline : CertifiedVerifierEncodingDiscipline verifier) :
    (mk verifier discipline).verifier = verifier :=
  rfl

@[simp]
theorem discipline_mk {problem : PresentedProblem} (verifier : CertifiedVerifier problem)
    (discipline : CertifiedVerifierEncodingDiscipline verifier) :
    (mk verifier discipline).discipline = discipline :=
  rfl

/--
Eliminate a native capability through its exact paired verifier and discipline.

The continuation receives no backend `TMInNP` theorem and no legacy verifier: the only authority
unpacked here is the `CertifiedVerifier` stored in the capability and the discipline dependent on
that same term.
-/
theorem exactComponents {problem : PresentedProblem}
    (capability : NativeVerifierCapability problem)
    {motive : NativeVerifierCapability problem → Prop}
    (use : ∀ verifier : CertifiedVerifier problem,
      ∀ discipline : CertifiedVerifierEncodingDiscipline verifier,
        motive (.mk verifier discipline)) :
    motive capability := by
  cases capability with
  | mk verifier discipline =>
      exact use verifier discipline

/-- The discipline inside a native capability retains exactly its verifier's witness presentation. -/
theorem discipline_witnessRepresentation_eq {problem : PresentedProblem}
    (capability : NativeVerifierCapability problem) :
    capability.discipline.witnessRepresentation = capability.verifier.witness :=
  capability.discipline.witnessRepresentation_eq

/-- Every native capability carries exact checked-decoder provenance. -/
theorem exactDisciplineProvenance {problem : PresentedProblem}
    (capability : NativeVerifierCapability problem) :
    ∃ backendDiscipline :
        ComplexityReduction.SAT.TMVerifierEncodingDiscipline capability.verifier.toTMVerifier,
      capability.discipline.basis = .checkedDecoder backendDiscipline := by
  rcases capability with ⟨verifier, discipline⟩
  rcases discipline with ⟨basis⟩
  cases basis with
  | checkedDecoder backendDiscipline =>
      exact ⟨backendDiscipline, rfl⟩

/-- Forget native capability only in the safe direction to backend direct-TM membership. -/
theorem toBackendTMInNP {problem : PresentedProblem}
    (capability : NativeVerifierCapability problem) : BackendTMInNP problem :=
  capability.discipline.toBackendTMInNP

/-- The backend projection is exactly the backend membership derived from the packaged verifier. -/
theorem toBackendTMInNP_eq_verifier {problem : PresentedProblem}
    (capability : NativeVerifierCapability problem) :
    capability.toBackendTMInNP = capability.verifier.toBackendTMInNP :=
  rfl

end NativeVerifierCapability

/-- Introduce native membership only from a concrete verifier/discipline capability. -/
theorem NativeTMInNP.ofCapability {problem : PresentedProblem}
    (capability : NativeVerifierCapability problem) : NativeTMInNP problem :=
  ⟨capability⟩

/--
Eliminate native membership only through an exact verifier/discipline pair.

Since `NativeTMInNP` is `Nonempty` capability, this Prop-valued eliminator exposes no route from
backend direct-TM membership into native authority; a caller must already possess the packaged
capability to introduce the premise.
-/
theorem NativeTMInNP.exactComponents {problem : PresentedProblem}
    (membership : NativeTMInNP problem)
    {motive : Prop}
    (use : ∀ verifier : CertifiedVerifier problem,
      CertifiedVerifierEncodingDiscipline verifier → motive) :
    motive := by
  rcases membership with ⟨capability⟩
  exact capability.exactComponents (motive := fun _ => motive)
    (fun verifier discipline => use verifier discipline)

/-- Native membership is definitionally the nonemptiness of exact native capabilities. -/
theorem nativeTMInNP_iff_nonemptyCapability (problem : PresentedProblem) :
    NativeTMInNP problem ↔ Nonempty (NativeVerifierCapability problem) :=
  Iff.rfl

/-- Native membership safely implies backend direct-TM membership, but no converse is provided. -/
theorem NativeTMInNP.toBackendTMInNP {problem : PresentedProblem}
    (membership : NativeTMInNP problem) : BackendTMInNP problem := by
  exact membership.exactComponents fun verifier _ => verifier.toBackendTMInNP

end Certificate
end ComplexityReduction
