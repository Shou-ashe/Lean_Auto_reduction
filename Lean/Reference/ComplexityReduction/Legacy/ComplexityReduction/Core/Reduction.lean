/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Core.EncodedDecisionProblem

namespace ComplexityReduction

/-- A semantic many-one reduction between encoded decision problems. -/
structure SemanticReduction (A B : EncodedDecisionProblem) where
  f : A.Instance.Carrier → B.Instance.Carrier
  correct : ∀ x, A.isYes x ↔ B.isYes (f x)

/-- A Karp reduction between encoded decision problems in a chosen map model. -/
structure KarpReductionM (M : PolyTimeModel) (A B : EncodedDecisionProblem) where
  f : PolyTimeMap M A.Instance B.Instance
  correct : ∀ x, A.isYes x ↔ B.isYes (f.toFun x)

/-- Polynomial-time many-one reducibility over a chosen encoded map model. -/
def PolyReducibleM (M : PolyTimeModel) (A B : EncodedDecisionProblem) : Prop :=
  Nonempty (KarpReductionM M A B)

namespace SemanticReduction

/-- Identity semantic reduction. -/
def id (A : EncodedDecisionProblem) : SemanticReduction A A where
  f := fun x => x
  correct := fun _ => Iff.rfl

/-- Composition of semantic reductions. -/
def comp {A B C : EncodedDecisionProblem}
    (rBC : SemanticReduction B C) (rAB : SemanticReduction A B) :
    SemanticReduction A C where
  f := rBC.f ∘ rAB.f
  correct := fun x => Iff.trans (rAB.correct x) (rBC.correct (rAB.f x))

/-- Add a polynomial-time map certificate to a semantic reduction. -/
def toKarpReductionM {M : PolyTimeModel} {A B : EncodedDecisionProblem}
    (r : SemanticReduction A B) (h : M.IsPolyTimeMap r.f) :
    KarpReductionM M A B where
  f := { toFun := r.f, polytime := h }
  correct := r.correct

/-- Forget a model-level Karp reduction to its semantic content. -/
def ofKarpReductionM {M : PolyTimeModel} {A B : EncodedDecisionProblem}
    (r : KarpReductionM M A B) :
    SemanticReduction A B where
  f := r.f.toFun
  correct := r.correct

end SemanticReduction

namespace KarpReductionM

/-- Underlying semantic reduction. -/
def toSemantic {M : PolyTimeModel} {A B : EncodedDecisionProblem}
    (r : KarpReductionM M A B) :
    SemanticReduction A B :=
  SemanticReduction.ofKarpReductionM r

end KarpReductionM

namespace PolyReducibleM

/-- Encoded polynomial-time reducibility is reflexive. -/
theorem refl (M : PolyTimeModel) (A : EncodedDecisionProblem) :
    PolyReducibleM M A A :=
  ⟨{ f := PolyTimeMap.id M A.Instance, correct := fun _ => Iff.rfl }⟩

/-- Encoded polynomial-time reducibility is transitive. -/
theorem trans {M : PolyTimeModel} {A B C : EncodedDecisionProblem}
    (hAB : PolyReducibleM M A B) (hBC : PolyReducibleM M B C) :
    PolyReducibleM M A C := by
  rcases hAB with ⟨rAB⟩
  rcases hBC with ⟨rBC⟩
  exact ⟨{
    f := PolyTimeMap.comp rBC.f rAB.f
    correct := fun x => Iff.trans (rAB.correct x) (rBC.correct (rAB.f.toFun x)) }⟩

end PolyReducibleM

namespace InP

/-- `P` is downward closed under polynomial-time many-one reductions. -/
theorem of_reduction {M : PolyTimeModel} {A B : EncodedDecisionProblem}
    (hAB : PolyReducibleM M A B) (hB : InP M B) : InP M A := by
  rcases hAB with ⟨rAB⟩
  rcases hB with ⟨dB⟩
  exact intro (PolyTimeMap.comp dB.decide rAB.f)
    (fun x => Iff.trans (dB.correct (rAB.f.toFun x)) (rAB.correct x).symm)

/-- `P` is invariant under polynomial-time equivalent encodings. -/
theorem congr_instance_encoding {M : PolyTimeModel}
    {L₁ L₂ : EncodedDecisionProblem}
    (e : PolyTimeEquiv M L₁.Instance L₂.Instance)
    (hPredicate : ∀ x, L₁.isYes x ↔ L₂.isYes (e.toMap.toFun x)) :
    InP M L₁ ↔ InP M L₂ := by
  constructor
  · intro hP₁
    rcases hP₁ with ⟨d₁⟩
    refine intro (PolyTimeMap.comp d₁.decide e.invMap) ?_
    intro y
    have hCorrect := d₁.correct (e.invMap.toFun y)
    have hPred := hPredicate (e.invMap.toFun y)
    have hRight :
        L₂.isYes (e.toMap.toFun (e.invMap.toFun y)) ↔ L₂.isYes y := by
      rw [e.right_inv y]
    exact (hCorrect.trans hPred).trans hRight
  · intro hP₂
    rcases hP₂ with ⟨d₂⟩
    refine intro (PolyTimeMap.comp d₂.decide e.toMap) ?_
    intro x
    exact (d₂.correct (e.toMap.toFun x)).trans (hPredicate x).symm

end InP

/-- A plain semantic reduction between unencoded decision problems. -/
structure Reduction (A B : DecisionProblem) where
  f : A.Instance → B.Instance
  correct : ∀ x, A.isYes x ↔ B.isYes (f x)

/-- A Karp reduction between plain decision problems under the closure model. -/
structure KarpReduction (A B : DecisionProblem) extends Reduction A B where
  polytime : ClosurePolyTimeMap (X := EncodedType.raw A.Instance)
    (Y := EncodedType.raw B.Instance) f

/-- Legacy-style reducibility for unencoded decision problems. -/
def PolyReducible (A B : DecisionProblem) : Prop :=
  Nonempty (KarpReduction A B)

notation A " ≤ₚ " B => PolyReducible A B

namespace PolyReducible

/-- Legacy-style reducibility is reflexive. -/
theorem refl (A : DecisionProblem) : A ≤ₚ A :=
  ⟨{ f := id, correct := fun _ => Iff.rfl, polytime := ClosurePolyTimeMap.id_map }⟩

/-- Legacy-style reducibility is transitive. -/
theorem trans {A B C : DecisionProblem} (hAB : A ≤ₚ B) (hBC : B ≤ₚ C) : A ≤ₚ C := by
  rcases hAB with ⟨rAB⟩
  rcases hBC with ⟨rBC⟩
  exact ⟨{
    f := rBC.f ∘ rAB.f
    correct := fun x => Iff.trans (rAB.correct x) (rBC.correct (rAB.f x))
    polytime := ClosurePolyTimeMap.comp_map rBC.polytime rAB.polytime }⟩

/-- View legacy reducibility as encoded reducibility over raw encodings. -/
theorem toRawEncoded {A B : DecisionProblem} (h : A ≤ₚ B) :
    PolyReducibleM ClosurePolyTimeModel A.withRawEncoding B.withRawEncoding := by
  rcases h with ⟨r⟩
  exact ⟨{
    f := { toFun := r.f, polytime := r.polytime }
    correct := r.correct }⟩

end PolyReducible

end ComplexityReduction
