/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Certificates.LogSpaceMap
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.LogSpaceTMSound

namespace ComplexityReduction

/-- A costed many-one reduction certificate. -/
structure CostedReduction (A B : EncodedDecisionProblem) where
  f : A.Instance.Carrier → B.Instance.Carrier
  correct : ∀ x, A.isYes x ↔ B.isYes (f x)
  costed : CostedPolyTimeMap (X := A.Instance) (Y := B.Instance) f

/-- A log-space many-one reduction certificate. -/
structure LogReductionCert (A B : EncodedDecisionProblem) where
  f : A.Instance.Carrier → B.Instance.Carrier
  correct : ∀ x, A.isYes x ↔ B.isYes (f x)
  logspace : LogSpaceMap (X := A.Instance) (Y := B.Instance) f

namespace CostedReduction

/-- Underlying semantic reduction. -/
def toSemantic {A B : EncodedDecisionProblem} (r : CostedReduction A B) :
    SemanticReduction A B where
  f := r.f
  correct := r.correct

/-- Convert a costed reduction to a costed-model Karp reduction. -/
def toKarpReductionM {A B : EncodedDecisionProblem} (r : CostedReduction A B) :
    KarpReductionM CostedPolyTimeModel A B where
  f := { toFun := r.f, polytime := r.costed }
  correct := r.correct

/-- Build a costed reduction from a primitive `CostedMap` witness. -/
def ofCostedMap {A B : EncodedDecisionProblem}
    (f : A.Instance.Carrier → B.Instance.Carrier)
    (hCorrect : ∀ x, A.isYes x ↔ B.isYes (f x))
    (hCosted : CostedMap A.Instance B.Instance f) :
    CostedReduction A B where
  f := f
  correct := hCorrect
  costed := CostedPolyTimeMap.of_costed hCosted

/-- Costed identity reduction. -/
def id (A : EncodedDecisionProblem) : CostedReduction A A where
  f := fun x => x
  correct := fun _ => Iff.rfl
  costed := CostedPolyTimeMap.id_map

/-- Costed reduction composition at the closure-certificate level. -/
def comp {A B C : EncodedDecisionProblem}
    (rBC : CostedReduction B C) (rAB : CostedReduction A B) :
    CostedReduction A C where
  f := rBC.f ∘ rAB.f
  correct := fun x => Iff.trans (rAB.correct x) (rBC.correct (rAB.f x))
  costed := CostedPolyTimeMap.comp_map rBC.costed rAB.costed

end CostedReduction

namespace LogReductionCert

/-- Underlying semantic reduction. -/
def toSemantic {A B : EncodedDecisionProblem} (r : LogReductionCert A B) :
    SemanticReduction A B where
  f := r.f
  correct := r.correct

/-- Convert a log-space certificate to a costed reduction certificate. -/
def toCostedReduction {A B : EncodedDecisionProblem} (r : LogReductionCert A B) :
    CostedReduction A B where
  f := r.f
  correct := r.correct
  costed := r.logspace.toCostedPolyTimeMap

/-- Convert a log-space certificate to a log-space Karp reduction. -/
def toLogKarpReduction {A B : EncodedDecisionProblem} (r : LogReductionCert A B) :
    LogKarpReduction A B where
  f := r.f
  logspace := r.logspace
  correct := r.correct

/-- Convert a log-space certificate to a costed-model Karp reduction. -/
def toKarpReductionM {A B : EncodedDecisionProblem} (r : LogReductionCert A B) :
    KarpReductionM CostedPolyTimeModel A B :=
  r.toLogKarpReduction.toCostedReduction

/-- Convert a log-space certificate to direct TM semantics with a soundness theorem. -/
def toTMKarpReduction (hSound : LogSpaceTMSound)
    {A B : EncodedDecisionProblem} (r : LogReductionCert A B) :
    TMKarpReduction A B :=
  r.toLogKarpReduction.toTMReduction hSound

/-- Log-space identity reduction. -/
def id (A : EncodedDecisionProblem) : LogReductionCert A A where
  f := fun x => x
  correct := fun _ => Iff.rfl
  logspace := LogSpaceMap.id_map

end LogReductionCert

end ComplexityReduction
