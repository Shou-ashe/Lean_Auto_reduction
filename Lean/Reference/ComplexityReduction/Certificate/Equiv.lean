/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Core.ProblemEquiv
import ComplexityReduction.Certificate.Reduction

/-!
Canonical certified equivalences of exact V2 presented problems.

An equivalence is exactly two `CertifiedReduction` values.  Its semantic and direct-TM
projections are therefore projections of the same two typed programs rather than independent
metadata or route-local evidence.
-/

namespace ComplexityReduction
namespace Certificate

open Encoding Program

/-- Two directed certified reductions between exact presented problems. -/
structure CertifiedEquiv (source target : PresentedProblem) where
  forward : CertifiedReduction source target
  backward : CertifiedReduction target source

namespace CertifiedEquiv

/-- Build a certified equivalence from its two exact directed certificates. -/
def ofReductions {source target : PresentedProblem}
    (forward : CertifiedReduction source target) (backward : CertifiedReduction target source) :
    CertifiedEquiv source target :=
  ⟨forward, backward⟩

/--
At fixed presented-problem endpoints, a certified equivalence is determined by
the two programs stored in its directional certificates.

The endpoint indices of those programs remain part of the statement: this
cannot identify certificates merely because their Lean carriers coincide.
-/
@[ext]
theorem ext {source target : PresentedProblem}
    (first second : CertifiedEquiv source target)
    (forwardProgramEquality : first.forward.program = second.forward.program)
    (backwardProgramEquality : first.backward.program = second.backward.program) :
    first = second := by
  have forwardEquality : first.forward = second.forward :=
    CertifiedReduction.ext first.forward second.forward forwardProgramEquality
  have backwardEquality : first.backward = second.backward :=
    CertifiedReduction.ext first.backward second.backward backwardProgramEquality
  cases first
  cases second
  cases forwardEquality
  cases backwardEquality
  rfl

/-- The reflexive certified equivalence at one exact presented problem. -/
def refl (problem : PresentedProblem) : CertifiedEquiv problem problem :=
  ofReductions (.refl problem) (.refl problem)

/-- Reverse the two certified directions without changing their programs. -/
def symm {source target : PresentedProblem} (equiv : CertifiedEquiv source target) :
    CertifiedEquiv target source :=
  ofReductions equiv.backward equiv.forward

/-- Compose endpoint-compatible certified equivalences through certificate composition. -/
def comp {source middle target : PresentedProblem}
    (after : CertifiedEquiv middle target) (before : CertifiedEquiv source middle) :
    CertifiedEquiv source target :=
  ofReductions
    (CertifiedReduction.comp after.forward before.forward)
    (CertifiedReduction.comp before.backward after.backward)

/-- Name the forward directed edge without requiring clients to inspect an equivalence body. -/
def forwardReduction {source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) : CertifiedReduction source target :=
  equiv.forward

/-- Name the backward directed edge without requiring clients to inspect an equivalence body. -/
def backwardReduction {source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) : CertifiedReduction target source :=
  equiv.backward

/-- Precompose the exact forward edge of an equivalence with a certified reduction. -/
def forwardPrecompose {previous source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) (before : CertifiedReduction previous source) :
    CertifiedReduction previous target :=
  CertifiedReduction.comp equiv.forward before

/-- Postcompose the exact forward edge of an equivalence with a certified reduction. -/
def forwardPostcompose {source target next : PresentedProblem}
    (equiv : CertifiedEquiv source target) (after : CertifiedReduction target next) :
    CertifiedReduction source next :=
  CertifiedReduction.comp after equiv.forward

/-- Precompose the exact backward edge of an equivalence with a certified reduction. -/
def backwardPrecompose {previous source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) (before : CertifiedReduction previous target) :
    CertifiedReduction previous source :=
  CertifiedReduction.comp equiv.backward before

/-- Postcompose the exact backward edge of an equivalence with a certified reduction. -/
def backwardPostcompose {source target next : PresentedProblem}
    (equiv : CertifiedEquiv source target) (after : CertifiedReduction source next) :
    CertifiedReduction target next :=
  CertifiedReduction.comp after equiv.backward

@[simp] theorem forwardReduction_eq_forward {source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) : equiv.forwardReduction = equiv.forward :=
  rfl

@[simp] theorem backwardReduction_eq_backward {source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) : equiv.backwardReduction = equiv.backward :=
  rfl

@[simp] theorem forwardPrecompose_eq_comp {previous source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) (before : CertifiedReduction previous source) :
    equiv.forwardPrecompose before = CertifiedReduction.comp equiv.forward before :=
  rfl

@[simp] theorem backwardPrecompose_eq_comp {previous source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) (before : CertifiedReduction previous target) :
    equiv.backwardPrecompose before = CertifiedReduction.comp equiv.backward before :=
  rfl

/-- The forward semantic reduction projection. -/
def toForwardEncodedSemanticReduction {source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) :
    ComplexityReduction.SemanticReduction
      source.toEncodedDecisionProblem target.toEncodedDecisionProblem :=
  equiv.forward.toEncodedSemanticReduction

/-- The backward semantic reduction projection. -/
def toBackwardEncodedSemanticReduction {source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) :
    ComplexityReduction.SemanticReduction
      target.toEncodedDecisionProblem source.toEncodedDecisionProblem :=
  equiv.backward.toEncodedSemanticReduction

/-- The forward direct-TM Karp reduction projection. -/
def toForwardTMKarpReduction {source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) :
    ComplexityReduction.TMKarpReduction
      source.toEncodedDecisionProblem target.toEncodedDecisionProblem :=
  equiv.forward.toTMKarpReduction

/-- The backward direct-TM Karp reduction projection. -/
def toBackwardTMKarpReduction {source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) :
    ComplexityReduction.TMKarpReduction
      target.toEncodedDecisionProblem source.toEncodedDecisionProblem :=
  equiv.backward.toTMKarpReduction

/-- The forward compatibility cost/TM projection of the same typed program. -/
def toForwardTMBackedCostedMap {source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) :
    ComplexityReduction.TMBackedCostedMap
      source.representation.encodedType target.representation.encodedType equiv.forward.program.run :=
  equiv.forward.toTMBackedCostedMap

/-- The backward compatibility cost/TM projection of the same typed program. -/
def toBackwardTMBackedCostedMap {source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) :
    ComplexityReduction.TMBackedCostedMap
      target.representation.encodedType source.representation.encodedType equiv.backward.program.run :=
  equiv.backward.toTMBackedCostedMap

/--
The compatibility-model equivalence facade is a one-way projection of the two
stored typed reductions.  Its forward and inverse maps are the costed Karp
facades compiled from those reductions' exact `PolyProg` values; it accepts no
bare `ProblemEquivM`, `CostedMap`, carrier equivalence, or metadata.
-/
def toCostedProblemEquiv {source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) :
    ComplexityReduction.ProblemEquivM ComplexityReduction.CostedPolyTimeModel
      source.toEncodedDecisionProblem target.toEncodedDecisionProblem where
  toMap := equiv.forward.toCostedKarpReduction.f
  invMap := equiv.backward.toCostedKarpReduction.f
  to_correct := equiv.forward.toCostedKarpReduction.correct
  inv_correct := equiv.backward.toCostedKarpReduction.correct

/-- The forward direct-TM reducibility theorem. -/
theorem toForwardTMPolyReducible {source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) :
    ComplexityReduction.TMPolyReducible
      source.toEncodedDecisionProblem target.toEncodedDecisionProblem :=
  equiv.forward.toTMPolyReducible

/-- The backward direct-TM reducibility theorem. -/
theorem toBackwardTMPolyReducible {source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) :
    ComplexityReduction.TMPolyReducible
      target.toEncodedDecisionProblem source.toEncodedDecisionProblem :=
  equiv.backward.toTMPolyReducible

/--
The forward program retains the complete source and target representation
identities fixed by this equivalence's exact presented-problem indices.
-/
@[simp]
theorem forward_endpointIdentities {source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) :
    equiv.forward.program.endpointIdentities =
      ⟨source.representation.representation, target.representation.representation⟩ :=
  rfl

/--
The backward program retains the reverse complete representation identities
fixed by this equivalence's exact presented-problem indices.
-/
@[simp]
theorem backward_endpointIdentities {source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) :
    equiv.backward.program.endpointIdentities =
      ⟨target.representation.representation, source.representation.representation⟩ :=
  rfl

/-- The forward source identity is exactly the source presentation identity. -/
@[simp]
theorem forward_endpointIdentity_source {source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) :
    equiv.forward.program.endpointIdentities.source = source.representationIdentity :=
  rfl

/-- The forward target identity is exactly the target presentation identity. -/
@[simp]
theorem forward_endpointIdentity_target {source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) :
    equiv.forward.program.endpointIdentities.target = target.representationIdentity :=
  rfl

/-- The backward source identity is exactly the target presentation identity. -/
@[simp]
theorem backward_endpointIdentity_source {source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) :
    equiv.backward.program.endpointIdentities.source = target.representationIdentity :=
  rfl

/-- The backward target identity is exactly the source presentation identity. -/
@[simp]
theorem backward_endpointIdentity_target {source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) :
    equiv.backward.program.endpointIdentities.target = source.representationIdentity :=
  rfl

/--
The two stored programs share one exact endpoint boundary in opposite
directions.  This equality follows from their type indices, not from carrier
equality or an external encoding equivalence.
-/
@[simp]
theorem endpointIdentities_reverse {source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) :
    equiv.forward.program.endpointIdentities =
      ⟨equiv.backward.program.endpointIdentities.target,
        equiv.backward.program.endpointIdentities.source⟩ :=
  rfl

/--
The two directional certificates meet at one exact presented-problem boundary.

Both semantic iff proofs are attached to their own stored programs, while the
program endpoint identities meet in reverse order.  Consequently this boundary
is determined by the two `PresentedProblem` indices, rather than by equality
of their carriers or by a bare `Equiv` between those carriers.
-/
theorem forward_backward_certificate_boundary {source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) :
    (∀ input : source.Instance,
      source.accepts input ↔ target.accepts (equiv.forward.program.run input)) ∧
    (∀ input : target.Instance,
      target.accepts input ↔ source.accepts (equiv.backward.program.run input)) ∧
    equiv.forward.program.endpointIdentities =
      ⟨source.representationIdentity, target.representationIdentity⟩ ∧
    equiv.backward.program.endpointIdentities =
      ⟨target.representationIdentity, source.representationIdentity⟩ :=
  ⟨equiv.forward.correct, equiv.backward.correct, rfl, rfl⟩

/--
Distinct presentation identities remain distinct at the forward program
boundary, even when their Lean carriers happen to coincide.
-/
theorem forward_endpointIdentities_ne_of_representationIdentity_ne
    {source target : PresentedProblem} (equiv : CertifiedEquiv source target)
    (identityNe : source.representationIdentity ≠ target.representationIdentity) :
    equiv.forward.program.endpointIdentities.source ≠
      equiv.forward.program.endpointIdentities.target := by
  simpa using identityNe

/--
Distinct presentation identities remain distinct at the reverse program
boundary, whose exact endpoint order is forced by the same certificate.
-/
theorem backward_endpointIdentities_ne_of_representationIdentity_ne
    {source target : PresentedProblem} (equiv : CertifiedEquiv source target)
    (identityNe : source.representationIdentity ≠ target.representationIdentity) :
    equiv.backward.program.endpointIdentities.source ≠
      equiv.backward.program.endpointIdentities.target := by
  intro equality
  apply identityNe
  simpa using equality.symm

/--
Every forward facade of an equivalence is a projection of the forward stored
program.  In particular, no metadata or bare compatibility cost can introduce
an independent executable or TM witness at this layer.
-/
theorem forward_projections_share_one_program {source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) :
    equiv.toForwardEncodedSemanticReduction.f = equiv.forward.program.run ∧
    (∀ input, source.accepts input ↔ target.accepts (equiv.forward.program.run input)) ∧
    equiv.forward.directTM = equiv.forward.program.compileTM ∧
    equiv.forward.compatibilityCost = equiv.forward.program.compatibilityCost ∧
    equiv.toForwardTMBackedCostedMap.tm_polytime = equiv.forward.program.compileTM ∧
    equiv.toForwardTMBackedCostedMap.costed = equiv.forward.program.compatibilityCost ∧
    equiv.toForwardTMKarpReduction.f = equiv.forward.program.run ∧
    equiv.toForwardTMKarpReduction.polytime = equiv.forward.program.compileTM := by
  simpa [toForwardEncodedSemanticReduction, toForwardTMBackedCostedMap,
    toForwardTMKarpReduction] using
    CertifiedReduction.projections_share_one_program equiv.forward

/--
Every backward facade of an equivalence is a projection of the backward stored
program, at the exact reverse presentation endpoints.
-/
theorem backward_projections_share_one_program {source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) :
    equiv.toBackwardEncodedSemanticReduction.f = equiv.backward.program.run ∧
    (∀ input, target.accepts input ↔ source.accepts (equiv.backward.program.run input)) ∧
    equiv.backward.directTM = equiv.backward.program.compileTM ∧
    equiv.backward.compatibilityCost = equiv.backward.program.compatibilityCost ∧
    equiv.toBackwardTMBackedCostedMap.tm_polytime = equiv.backward.program.compileTM ∧
    equiv.toBackwardTMBackedCostedMap.costed = equiv.backward.program.compatibilityCost ∧
    equiv.toBackwardTMKarpReduction.f = equiv.backward.program.run ∧
    equiv.toBackwardTMKarpReduction.polytime = equiv.backward.program.compileTM := by
  simpa [toBackwardEncodedSemanticReduction, toBackwardTMBackedCostedMap,
    toBackwardTMKarpReduction] using
    CertifiedReduction.projections_share_one_program equiv.backward

/--
Both compatibility-model maps in the legacy `ProblemEquivM` facade are
projections of the exact forward and backward programs stored by this V2
certificate.  The associated model evidence is likewise the compiler-derived
costed map for each program.
-/
theorem toCostedProblemEquiv_projections_share_exact_programs
    {source target : PresentedProblem} (equiv : CertifiedEquiv source target) :
    equiv.toCostedProblemEquiv.toMap.toFun = equiv.forward.program.run ∧
    equiv.toCostedProblemEquiv.toMap.polytime =
      equiv.forward.program.toCostedPolyTimeMap ∧
    (∀ input, source.accepts input ↔
      target.accepts (equiv.toCostedProblemEquiv.toMap.toFun input)) ∧
    equiv.toCostedProblemEquiv.invMap.toFun = equiv.backward.program.run ∧
    equiv.toCostedProblemEquiv.invMap.polytime =
      equiv.backward.program.toCostedPolyTimeMap ∧
    (∀ input, target.accepts input ↔
      source.accepts (equiv.toCostedProblemEquiv.invMap.toFun input)) :=
  ⟨rfl, rfl, equiv.forward.correct, rfl, rfl, equiv.backward.correct⟩

/--
The full two-way executable boundary: each direction's semantic, direct-TM,
costed, and compatibility facades remain indexed by its own stored program,
while the two programs retain the exact reverse representation boundary.
-/
theorem projections_share_exact_programs {source target : PresentedProblem}
    (equiv : CertifiedEquiv source target) :
    (equiv.toForwardEncodedSemanticReduction.f = equiv.forward.program.run ∧
      (∀ input, source.accepts input ↔ target.accepts (equiv.forward.program.run input)) ∧
      equiv.forward.directTM = equiv.forward.program.compileTM ∧
      equiv.forward.compatibilityCost = equiv.forward.program.compatibilityCost ∧
      equiv.toForwardTMBackedCostedMap.tm_polytime = equiv.forward.program.compileTM ∧
      equiv.toForwardTMBackedCostedMap.costed = equiv.forward.program.compatibilityCost ∧
      equiv.toForwardTMKarpReduction.f = equiv.forward.program.run ∧
      equiv.toForwardTMKarpReduction.polytime = equiv.forward.program.compileTM) ∧
    (equiv.toBackwardEncodedSemanticReduction.f = equiv.backward.program.run ∧
      (∀ input, target.accepts input ↔ source.accepts (equiv.backward.program.run input)) ∧
      equiv.backward.directTM = equiv.backward.program.compileTM ∧
      equiv.backward.compatibilityCost = equiv.backward.program.compatibilityCost ∧
      equiv.toBackwardTMBackedCostedMap.tm_polytime = equiv.backward.program.compileTM ∧
      equiv.toBackwardTMBackedCostedMap.costed = equiv.backward.program.compatibilityCost ∧
      equiv.toBackwardTMKarpReduction.f = equiv.backward.program.run ∧
      equiv.toBackwardTMKarpReduction.polytime = equiv.backward.program.compileTM) ∧
    equiv.forward.program.endpointIdentities =
      ⟨equiv.backward.program.endpointIdentities.target,
        equiv.backward.program.endpointIdentities.source⟩ :=
  ⟨equiv.forward_projections_share_one_program,
    equiv.backward_projections_share_one_program,
    equiv.endpointIdentities_reverse⟩

@[simp]
theorem forward_ofReductions {source target : PresentedProblem}
    (forward : CertifiedReduction source target) (backward : CertifiedReduction target source) :
    (ofReductions forward backward).forward = forward :=
  rfl

@[simp]
theorem backward_ofReductions {source target : PresentedProblem}
    (forward : CertifiedReduction source target) (backward : CertifiedReduction target source) :
    (ofReductions forward backward).backward = backward :=
  rfl

@[simp]
theorem forward_symm {source target : PresentedProblem} (equiv : CertifiedEquiv source target) :
    equiv.symm.forward = equiv.backward :=
  rfl

@[simp]
theorem backward_symm {source target : PresentedProblem} (equiv : CertifiedEquiv source target) :
    equiv.symm.backward = equiv.forward :=
  rfl

/-- Reflexivity stores the exact identity program in its forward direction. -/
@[simp]
theorem forward_program_refl (problem : PresentedProblem) :
    (refl problem).forward.program = PolyProg.id problem.representation :=
  rfl

/-- Reflexivity stores the exact identity program in its backward direction. -/
@[simp]
theorem backward_program_refl (problem : PresentedProblem) :
    (refl problem).backward.program = PolyProg.id problem.representation :=
  rfl

/-- Swapping a certified equivalence preserves the exact backward program as its new forward one. -/
@[simp]
theorem forward_program_symm {source target : PresentedProblem} (equiv : CertifiedEquiv source target) :
    equiv.symm.forward.program = equiv.backward.program :=
  rfl

/-- Swapping a certified equivalence preserves the exact forward program as its new backward one. -/
@[simp]
theorem backward_program_symm {source target : PresentedProblem} (equiv : CertifiedEquiv source target) :
    equiv.symm.backward.program = equiv.forward.program :=
  rfl

/-- Equivalence composition stores the forward certificate composition verbatim. -/
@[simp]
theorem forward_comp {source middle target : PresentedProblem}
    (after : CertifiedEquiv middle target) (before : CertifiedEquiv source middle) :
    (comp after before).forward = CertifiedReduction.comp after.forward before.forward :=
  rfl

/-- Equivalence composition stores the reverse certificate composition verbatim. -/
@[simp]
theorem backward_comp {source middle target : PresentedProblem}
    (after : CertifiedEquiv middle target) (before : CertifiedEquiv source middle) :
    (comp after before).backward = CertifiedReduction.comp before.backward after.backward :=
  rfl

/-- The forward execution of an equivalence composite is the composed exact forward program. -/
@[simp]
theorem forward_program_comp {source middle target : PresentedProblem}
    (after : CertifiedEquiv middle target) (before : CertifiedEquiv source middle) :
    (comp after before).forward.program =
      PolyProg.comp after.forward.program before.forward.program :=
  rfl

/-- The backward execution of an equivalence composite is the reverse composed exact program. -/
@[simp]
theorem backward_program_comp {source middle target : PresentedProblem}
    (after : CertifiedEquiv middle target) (before : CertifiedEquiv source middle) :
    (comp after before).backward.program =
      PolyProg.comp before.backward.program after.backward.program :=
  rfl

end CertifiedEquiv
end Certificate
end ComplexityReduction
