/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Core.Reduction
import Mathlib.Computability.TuringMachine.Computable

namespace ComplexityReduction

/-- A language over a finite alphabet. -/
structure EncodedLanguage : Type 1 where
  Alphabet : Type
  finite_alphabet : Fintype Alphabet
  accepts : List Alphabet → Prop

namespace EncodedLanguage

instance (L : EncodedLanguage) : Fintype L.Alphabet :=
  L.finite_alphabet

/-- View a language as an encoded decision problem over strings. -/
def toProblem (L : EncodedLanguage) : EncodedDecisionProblem where
  Instance := EncodedType.ofAlphabet L.Alphabet
  isYes := L.accepts

end EncodedLanguage

namespace EncodedDecisionProblem

/-- The image language of an encoded decision problem. -/
def toEncodedLanguage (L : EncodedDecisionProblem) : EncodedLanguage where
  Alphabet := L.Instance.Symbol
  finite_alphabet := L.Instance.finite_symbol
  accepts := fun w => ∃ x, L.Instance.encode x = w ∧ L.isYes x

theorem accepts_encode_of_yes (L : EncodedDecisionProblem)
    {x : L.Instance.Carrier} (hx : L.isYes x) :
    L.toEncodedLanguage.accepts (L.Instance.encode x) :=
  ⟨x, rfl, hx⟩

end EncodedDecisionProblem

/-- A function computable by mathlib's TM2 model in polynomial time. -/
def TMPolyTimeMap (X Y : EncodedType) (f : X.Carrier → Y.Carrier) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime X.encode Y.encode f)

namespace TMPolyTimeMap

/-- The identity map is polynomial time in mathlib's TM2 semantics. -/
theorem id (X : EncodedType) : TMPolyTimeMap X X id :=
  ⟨Turing.idComputableInPolyTime X.encode⟩

end TMPolyTimeMap

/-- A TM-backed Karp reduction between encoded decision problems. -/
structure TMKarpReduction (A B : EncodedDecisionProblem) where
  f : A.Instance.Carrier → B.Instance.Carrier
  polytime : TMPolyTimeMap A.Instance B.Instance f
  correct : ∀ x, A.isYes x ↔ B.isYes (f x)

/-- TM-semantics polynomial-time many-one reducibility. -/
def TMPolyReducible (A B : EncodedDecisionProblem) : Prop :=
  Nonempty (TMKarpReduction A B)

namespace TMPolyReducible

/-- TM-semantics polynomial-time reducibility is reflexive. -/
theorem refl (A : EncodedDecisionProblem) : TMPolyReducible A A :=
  ⟨{ f := fun x => x, polytime := TMPolyTimeMap.id A.Instance, correct := fun _ => Iff.rfl }⟩

end TMPolyReducible

namespace PolyTimeModel

/-- Compatibility witness between an abstract map model and direct TM2 semantics. -/
structure TMCompatible (M : PolyTimeModel) : Type 1 where
  sound :
    {X Y : EncodedType} →
    {f : X.Carrier → Y.Carrier} →
      M.IsPolyTimeMap f → TMPolyTimeMap X Y f
  complete :
    {X Y : EncodedType} →
    {f : X.Carrier → Y.Carrier} →
      TMPolyTimeMap X Y f → M.IsPolyTimeMap f

end PolyTimeModel

namespace TMKarpReduction

/-- Transport a TM-backed reduction into a compatible generic model. -/
def toModel {M : PolyTimeModel} (hM : PolyTimeModel.TMCompatible M)
    {A B : EncodedDecisionProblem} (r : TMKarpReduction A B) :
    KarpReductionM M A B where
  f := { toFun := r.f, polytime := hM.complete r.polytime }
  correct := r.correct

/-- Transport a model-level reduction into direct TM semantics. -/
def ofModel {M : PolyTimeModel} (hM : PolyTimeModel.TMCompatible M)
    {A B : EncodedDecisionProblem} (r : KarpReductionM M A B) :
    TMKarpReduction A B where
  f := r.f.toFun
  polytime := hM.sound r.f.polytime
  correct := r.correct

/-- Underlying semantic reduction. -/
def toSemantic {A B : EncodedDecisionProblem} (r : TMKarpReduction A B) :
    SemanticReduction A B where
  f := r.f
  correct := r.correct

end TMKarpReduction

namespace TMPolyReducible

/-- Move reducibility from direct TM semantics to a compatible generic model. -/
theorem toModel {M : PolyTimeModel} (hM : PolyTimeModel.TMCompatible M)
    {A B : EncodedDecisionProblem} :
    TMPolyReducible A B → PolyReducibleM M A B := by
  intro h
  rcases h with ⟨r⟩
  exact ⟨r.toModel hM⟩

/-- Move reducibility from a compatible generic model to direct TM semantics. -/
theorem ofModel {M : PolyTimeModel} (hM : PolyTimeModel.TMCompatible M)
    {A B : EncodedDecisionProblem} :
    PolyReducibleM M A B → TMPolyReducible A B := by
  intro h
  rcases h with ⟨r⟩
  exact ⟨TMKarpReduction.ofModel hM r⟩

/-- A compatible generic model and direct TM semantics prove the same reductions. -/
theorem iff_model {M : PolyTimeModel} (hM : PolyTimeModel.TMCompatible M)
    (A B : EncodedDecisionProblem) :
    TMPolyReducible A B ↔ PolyReducibleM M A B :=
  ⟨toModel hM, ofModel hM⟩

end TMPolyReducible

end ComplexityReduction
