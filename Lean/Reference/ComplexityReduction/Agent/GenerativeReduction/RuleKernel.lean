/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Certificate.CompletenessTransport
import ComplexityReduction.Certificate.Equiv
import ComplexityReduction.Certificate.PresentationChange

/-! Problem-family-independent certificate rules used by proof reconstruction. -/

namespace ComplexityReduction.Agent.GenerativeReduction.RuleKernel

open ComplexityReduction Encoding Certificate

theorem exactHardness {target : PresentedProblem}
    (hardness : NativeTMNPHard target) : NativeTMNPHard target := hardness

theorem completenessProjection {target : PresentedProblem}
    (complete : NativeTMNPComplete target) : NativeTMNPHard target :=
  complete.nativeHardness

theorem hardnessAlongPath {hub target : PresentedProblem}
    (hardness : NativeTMNPHard hub) (path : CertifiedPath hub target) :
    NativeTMNPHard target :=
  NativeTMNPHard.alongPath hardness path

theorem completenessAlongPath {hub target : PresentedProblem}
    (complete : NativeTMNPComplete hub) (path : CertifiedPath hub target) :
    NativeTMNPHard target :=
  NativeTMNPHard.ofCompleteAlongPath complete path

def reductionStep {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) : CertifiedPath source target :=
  .step reduction

def pathComposition {source middle target : PresentedProblem}
    (before : CertifiedPath source middle) (after : CertifiedPath middle target) :
    CertifiedPath source target :=
  before.append after

def reductionComposition {source middle target : PresentedProblem}
    (before : CertifiedReduction source middle) (after : CertifiedReduction middle target) :
    CertifiedReduction source target :=
  CertifiedReduction.comp after before

def equivalenceForward {source target : PresentedProblem}
    (equivalence : CertifiedEquiv source target) : CertifiedReduction source target :=
  equivalence.forwardReduction

def equivalenceBackward {source target : PresentedProblem}
    (equivalence : CertifiedEquiv source target) : CertifiedReduction target source :=
  equivalence.backwardReduction

def presentationForward {source target : PresentedProblem}
    (change : CertifiedPresentationChange source target) : CertifiedReduction source target :=
  change.forwardReduction

def presentationBackward {source target : PresentedProblem}
    (change : CertifiedPresentationChange source target) : CertifiedReduction target source :=
  change.backwardReduction

end ComplexityReduction.Agent.GenerativeReduction.RuleKernel
