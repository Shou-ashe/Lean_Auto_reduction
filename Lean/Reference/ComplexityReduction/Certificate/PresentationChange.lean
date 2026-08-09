/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Certificate.Equiv

/-!
Certified changes between exact V2 problem presentations.

This certificate cannot be built from a bare carrier equality or `Equiv`.  It retains a semantic
problem equality, a two-direction `CertifiedEquiv`, and explicit predicate alignments for the
actual executable programs in that equivalence.
-/

namespace ComplexityReduction
namespace Certificate

open Encoding

/--
A certified problem-level change of presentation.

The computational content is exactly the two reductions stored by `equivalence`.  The additional
fields state that the two presented problems name the same semantic problem and record predicate
alignment for those exact executable programs; neither field permits a bare equivalence or carrier
equality to manufacture an executable or direct-TM capability.
-/
structure CertifiedPresentationChange (source target : PresentedProblem) where
  semantic_eq : source.semantic = target.semantic
  equivalence : CertifiedEquiv source target
  forwardPredicateAlignment : ∀ input,
    source.accepts input ↔ target.accepts (equivalence.forward.program.run input)
  backwardPredicateAlignment : ∀ input,
    target.accepts input ↔ source.accepts (equivalence.backward.program.run input)

namespace CertifiedPresentationChange

/-- Package a semantic equality and an existing two-way certified equivalence as a presentation change. -/
def ofCertifiedEquiv {source target : PresentedProblem}
    (semantic_eq : source.semantic = target.semantic) (equivalence : CertifiedEquiv source target) :
    CertifiedPresentationChange source target where
  semantic_eq := semantic_eq
  equivalence := equivalence
  forwardPredicateAlignment := equivalence.forward.correct
  backwardPredicateAlignment := equivalence.backward.correct

/-- The identity presentation change at one exact presented problem. -/
def refl (problem : PresentedProblem) : CertifiedPresentationChange problem problem :=
  ofCertifiedEquiv rfl (.refl problem)

/-- Reverse a certified presentation change. -/
def symm {source target : PresentedProblem}
    (change : CertifiedPresentationChange source target) :
    CertifiedPresentationChange target source where
  semantic_eq := change.semantic_eq.symm
  equivalence := change.equivalence.symm
  forwardPredicateAlignment := change.backwardPredicateAlignment
  backwardPredicateAlignment := change.forwardPredicateAlignment

/-- Compose presentation changes through the same typed two-way certificate composition. -/
def comp {source middle target : PresentedProblem}
    (after : CertifiedPresentationChange middle target)
    (before : CertifiedPresentationChange source middle) :
    CertifiedPresentationChange source target :=
  ofCertifiedEquiv
    (before.semantic_eq.trans after.semantic_eq)
    (CertifiedEquiv.comp after.equivalence before.equivalence)

/-- The forward reduction stored by a presentation change. -/
def forwardReduction {source target : PresentedProblem}
    (change : CertifiedPresentationChange source target) : CertifiedReduction source target :=
  change.equivalence.forward

/-- The backward reduction stored by a presentation change. -/
def backwardReduction {source target : PresentedProblem}
    (change : CertifiedPresentationChange source target) : CertifiedReduction target source :=
  change.equivalence.backward

/-- Precompose the forward presentation-change edge with a certified reduction. -/
def forwardPrecompose {previous source target : PresentedProblem}
    (change : CertifiedPresentationChange source target)
    (before : CertifiedReduction previous source) : CertifiedReduction previous target :=
  CertifiedReduction.comp change.forwardReduction before

/-- Postcompose the forward presentation-change edge with a certified reduction. -/
def forwardPostcompose {source target next : PresentedProblem}
    (change : CertifiedPresentationChange source target)
    (after : CertifiedReduction target next) : CertifiedReduction source next :=
  CertifiedReduction.comp after change.forwardReduction

/-- Precompose the backward presentation-change edge with a certified reduction. -/
def backwardPrecompose {previous source target : PresentedProblem}
    (change : CertifiedPresentationChange source target)
    (before : CertifiedReduction previous target) : CertifiedReduction previous source :=
  CertifiedReduction.comp change.backwardReduction before

/-- Postcompose the backward presentation-change edge with a certified reduction. -/
def backwardPostcompose {source target next : PresentedProblem}
    (change : CertifiedPresentationChange source target)
    (after : CertifiedReduction source next) : CertifiedReduction target next :=
  CertifiedReduction.comp after change.backwardReduction

/-- The forward direct-TM projection of a certified presentation change. -/
def toForwardTMKarpReduction {source target : PresentedProblem}
    (change : CertifiedPresentationChange source target) :
    ComplexityReduction.TMKarpReduction
      source.toEncodedDecisionProblem target.toEncodedDecisionProblem :=
  change.equivalence.toForwardTMKarpReduction

/-- The backward direct-TM projection of a certified presentation change. -/
def toBackwardTMKarpReduction {source target : PresentedProblem}
    (change : CertifiedPresentationChange source target) :
    ComplexityReduction.TMKarpReduction
      target.toEncodedDecisionProblem source.toEncodedDecisionProblem :=
  change.equivalence.toBackwardTMKarpReduction

/-- The forward semantic reduction projection of a certified presentation change. -/
def toForwardEncodedSemanticReduction {source target : PresentedProblem}
    (change : CertifiedPresentationChange source target) :
    ComplexityReduction.SemanticReduction
      source.toEncodedDecisionProblem target.toEncodedDecisionProblem :=
  change.equivalence.toForwardEncodedSemanticReduction

/-- The backward semantic reduction projection of a certified presentation change. -/
def toBackwardEncodedSemanticReduction {source target : PresentedProblem}
    (change : CertifiedPresentationChange source target) :
    ComplexityReduction.SemanticReduction
      target.toEncodedDecisionProblem source.toEncodedDecisionProblem :=
  change.equivalence.toBackwardEncodedSemanticReduction

@[simp]
theorem forwardReduction_eq_forward {source target : PresentedProblem}
    (change : CertifiedPresentationChange source target) :
    change.forwardReduction = change.equivalence.forward :=
  rfl

@[simp]
theorem backwardReduction_eq_backward {source target : PresentedProblem}
    (change : CertifiedPresentationChange source target) :
    change.backwardReduction = change.equivalence.backward :=
  rfl

@[simp] theorem forwardPrecompose_eq_comp {previous source target : PresentedProblem}
    (change : CertifiedPresentationChange source target)
    (before : CertifiedReduction previous source) :
    change.forwardPrecompose before = CertifiedReduction.comp change.forwardReduction before :=
  rfl

@[simp] theorem backwardPrecompose_eq_comp {previous source target : PresentedProblem}
    (change : CertifiedPresentationChange source target)
    (before : CertifiedReduction previous target) :
    change.backwardPrecompose before = CertifiedReduction.comp change.backwardReduction before :=
  rfl

@[simp]
theorem forwardPredicateAlignment_ofCertifiedEquiv {source target : PresentedProblem}
    (semantic_eq : source.semantic = target.semantic) (equivalence : CertifiedEquiv source target)
    (input : source.Instance) :
    source.accepts input ↔ target.accepts (equivalence.forward.program.run input) :=
  (ofCertifiedEquiv semantic_eq equivalence).forwardPredicateAlignment input

@[simp]
theorem backwardPredicateAlignment_ofCertifiedEquiv {source target : PresentedProblem}
    (semantic_eq : source.semantic = target.semantic) (equivalence : CertifiedEquiv source target)
    (input : target.Instance) :
    target.accepts input ↔ source.accepts (equivalence.backward.program.run input) :=
  (ofCertifiedEquiv semantic_eq equivalence).backwardPredicateAlignment input

/-- A reversed presentation change exposes exactly the original backward reduction. -/
@[simp]
theorem forwardReduction_symm {source target : PresentedProblem}
    (change : CertifiedPresentationChange source target) :
    change.symm.forwardReduction = change.backwardReduction :=
  rfl

/-- A reversed presentation change exposes exactly the original forward reduction. -/
@[simp]
theorem backwardReduction_symm {source target : PresentedProblem}
    (change : CertifiedPresentationChange source target) :
    change.symm.backwardReduction = change.forwardReduction :=
  rfl

/-- Reversal changes only the direction of the recorded semantic problem equality. -/
@[simp]
theorem semantic_eq_symm {source target : PresentedProblem}
    (change : CertifiedPresentationChange source target) :
    change.symm.semantic_eq = change.semantic_eq.symm :=
  rfl

/-- Composition records exactly the transitive semantic-problem equality. -/
@[simp]
theorem semantic_eq_comp {source middle target : PresentedProblem}
    (after : CertifiedPresentationChange middle target)
    (before : CertifiedPresentationChange source middle) :
    (comp after before).semantic_eq = before.semantic_eq.trans after.semantic_eq :=
  rfl

/-- Composition retains the exact typed equivalence composite. -/
@[simp]
theorem equivalence_comp {source middle target : PresentedProblem}
    (after : CertifiedPresentationChange middle target)
    (before : CertifiedPresentationChange source middle) :
    (comp after before).equivalence = CertifiedEquiv.comp after.equivalence before.equivalence :=
  rfl

/-- The forward reduction of a composite is the composition of its two stored forward reductions. -/
@[simp]
theorem forwardReduction_comp {source middle target : PresentedProblem}
    (after : CertifiedPresentationChange middle target)
    (before : CertifiedPresentationChange source middle) :
    (comp after before).forwardReduction =
      CertifiedReduction.comp after.forwardReduction before.forwardReduction :=
  rfl

/-- The backward reduction of a composite is the reverse composition of its stored reductions. -/
@[simp]
theorem backwardReduction_comp {source middle target : PresentedProblem}
    (after : CertifiedPresentationChange middle target)
    (before : CertifiedPresentationChange source middle) :
    (comp after before).backwardReduction =
      CertifiedReduction.comp before.backwardReduction after.backwardReduction :=
  rfl

/-- A forward presentation-change composite runs the corresponding composite typed program. -/
@[simp]
theorem forward_program_comp {source middle target : PresentedProblem}
    (after : CertifiedPresentationChange middle target)
    (before : CertifiedPresentationChange source middle) :
    (comp after before).forwardReduction.program =
      Program.PolyProg.comp after.forwardReduction.program before.forwardReduction.program :=
  rfl

/-- A backward presentation-change composite runs the reverse composite typed program. -/
@[simp]
theorem backward_program_comp {source middle target : PresentedProblem}
    (after : CertifiedPresentationChange middle target)
    (before : CertifiedPresentationChange source middle) :
    (comp after before).backwardReduction.program =
      Program.PolyProg.comp before.backwardReduction.program after.backwardReduction.program :=
  rfl

end CertifiedPresentationChange
end Certificate
end ComplexityReduction
