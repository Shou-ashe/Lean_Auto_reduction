/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.List.Basic
import ComplexityReduction.Legacy.ComplexityReduction.Core

namespace ComplexityReduction
namespace Combinatorics

/-- Finite set-system instance over universe `{0, ..., universeSize - 1}`. -/
structure SetSystemInput where
  universeSize : Nat
  sets : List (List Nat)
  deriving Repr

def setSystemEncodedType : EncodedType :=
  EncodedType.raw SetSystemInput

/-- Structured finite-alphabet encoding for one set as a list of unary naturals. -/
def setStructuredEncodedType : EncodedType :=
  EncodedType.list EncodedType.nat

/-- Structured finite-alphabet encoding for a family of finite sets. -/
def setFamilyStructuredEncodedType : EncodedType :=
  EncodedType.list setStructuredEncodedType

/-- Tuple-shaped finite-alphabet encoding for set-system fields. -/
def setSystemTupleStructuredEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType

/--
Concrete finite-alphabet set-system encoding with explicit universe-size and
set-family fields.
-/
def setSystemStructuredEncodedType : EncodedType where
  Carrier := SetSystemInput
  Symbol := setSystemTupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => setSystemTupleStructuredEncodedType.encode (I.universeSize, I.sets)

theorem setStructuredEncodedType_encode_injective :
    Function.Injective setStructuredEncodedType.encode :=
  EncodedType.list_encode_injective EncodedType.nat_encode_injective

theorem setFamilyStructuredEncodedType_encode_injective :
    Function.Injective setFamilyStructuredEncodedType.encode :=
  EncodedType.list_encode_injective setStructuredEncodedType_encode_injective

theorem setSystemTupleStructuredEncodedType_encode_injective :
    Function.Injective setSystemTupleStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    EncodedType.nat_encode_injective
    setFamilyStructuredEncodedType_encode_injective

theorem setSystemStructuredEncodedType_encode_injective :
    Function.Injective setSystemStructuredEncodedType.encode := by
  intro I J henc
  have htuple : (I.universeSize, I.sets) = (J.universeSize, J.sets) :=
    setSystemTupleStructuredEncodedType_encode_injective (by
      simpa [setSystemStructuredEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl⟩
  rfl

def setSystemDecisionProblem (P : SetSystemInput → Prop) : EncodedDecisionProblem where
  Instance := setSystemEncodedType
  isYes := P

def SetSystemWellFormed (I : SetSystemInput) : Prop :=
  ∀ S ∈ I.sets, ∀ x ∈ S, x < I.universeSize

/-- A concrete set belongs to the family of a set-system instance. -/
def IsSetInFamily (I : SetSystemInput) (S : List Nat) : Prop :=
  S ∈ I.sets

/-- Pairwise disjointness for a selected subfamily. -/
def PairwiseDisjointFamily (sets : List (List Nat)) : Prop :=
  ∀ A ∈ sets, ∀ B ∈ sets, A ≠ B → ∀ x, x ∈ A → x ∈ B → False

/-- The selected subfamily covers every universe element. -/
def CoversUniverse (I : SetSystemInput) (selected : List (List Nat)) : Prop :=
  ∀ x, x < I.universeSize → ∃ S ∈ selected, x ∈ S

/-- The selected subfamily hits every set in the family. -/
def HitsEverySet (I : SetSystemInput) (hitting : List Nat) : Prop :=
  ∀ S ∈ I.sets, ∃ x ∈ hitting, x ∈ S

/-- Karp-style set-packing instance. -/
structure SetPackingInput where
  system : SetSystemInput
  k : Nat
  deriving Repr

def setPackingEncodedType : EncodedType :=
  EncodedType.raw SetPackingInput

/-- Tuple-shaped finite-alphabet encoding for Set Packing fields. -/
def setPackingTupleStructuredEncodedType : EncodedType :=
  EncodedType.prod setSystemStructuredEncodedType EncodedType.nat

/-- Concrete finite-alphabet Set Packing encoding. -/
def setPackingStructuredEncodedType : EncodedType where
  Carrier := SetPackingInput
  Symbol := setPackingTupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => setPackingTupleStructuredEncodedType.encode (I.system, I.k)

theorem setPackingTupleStructuredEncodedType_encode_injective :
    Function.Injective setPackingTupleStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    setSystemStructuredEncodedType_encode_injective
    EncodedType.nat_encode_injective

theorem setPackingStructuredEncodedType_encode_injective :
    Function.Injective setPackingStructuredEncodedType.encode := by
  intro I J henc
  have htuple : (I.system, I.k) = (J.system, J.k) :=
    setPackingTupleStructuredEncodedType_encode_injective (by
      simpa [setPackingStructuredEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl⟩
  rfl

def SetPacking (I : SetPackingInput) : Prop :=
  ∃ selected : List (List Nat),
    selected.length ≥ I.k ∧
      (∀ S ∈ selected, IsSetInFamily I.system S) ∧
      selected.Nodup ∧
      PairwiseDisjointFamily selected

def setPackingDecisionProblem : EncodedDecisionProblem where
  Instance := setPackingEncodedType
  isYes := SetPacking

/-- Set Packing over the structured finite-alphabet encoding. -/
def setPackingStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := setPackingStructuredEncodedType
  isYes := SetPacking

/-- Karp-style set-covering instance. -/
structure SetCoveringInput where
  system : SetSystemInput
  k : Nat
  deriving Repr

def setCoveringEncodedType : EncodedType :=
  EncodedType.raw SetCoveringInput

/-- Tuple-shaped finite-alphabet encoding for Set Covering fields. -/
def setCoveringTupleStructuredEncodedType : EncodedType :=
  EncodedType.prod setSystemStructuredEncodedType EncodedType.nat

/-- Concrete finite-alphabet Set Covering encoding. -/
def setCoveringStructuredEncodedType : EncodedType where
  Carrier := SetCoveringInput
  Symbol := setCoveringTupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => setCoveringTupleStructuredEncodedType.encode (I.system, I.k)

theorem setCoveringTupleStructuredEncodedType_encode_injective :
    Function.Injective setCoveringTupleStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    setSystemStructuredEncodedType_encode_injective
    EncodedType.nat_encode_injective

theorem setCoveringStructuredEncodedType_encode_injective :
    Function.Injective setCoveringStructuredEncodedType.encode := by
  intro I J henc
  have htuple : (I.system, I.k) = (J.system, J.k) :=
    setCoveringTupleStructuredEncodedType_encode_injective (by
      simpa [setCoveringStructuredEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl⟩
  rfl

def SetCovering (I : SetCoveringInput) : Prop :=
  ∃ selected : List (List Nat),
    selected.length ≤ I.k ∧
      (∀ S ∈ selected, IsSetInFamily I.system S) ∧
      CoversUniverse I.system selected

def setCoveringDecisionProblem : EncodedDecisionProblem where
  Instance := setCoveringEncodedType
  isYes := SetCovering

/-- Set Covering over the structured finite-alphabet encoding. -/
def setCoveringStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := setCoveringStructuredEncodedType
  isYes := SetCovering

/-- Karp-style exact-cover instance. -/
structure ExactCoverInput where
  system : SetSystemInput
  deriving Repr

def exactCoverEncodedType : EncodedType :=
  EncodedType.raw ExactCoverInput

/-- Concrete finite-alphabet Exact Cover encoding. -/
def exactCoverStructuredEncodedType : EncodedType where
  Carrier := ExactCoverInput
  Symbol := setSystemStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => setSystemStructuredEncodedType.encode I.system

theorem exactCoverStructuredEncodedType_encode_injective :
    Function.Injective exactCoverStructuredEncodedType.encode := by
  intro I J henc
  have hsystem : I.system = J.system :=
    setSystemStructuredEncodedType_encode_injective (by
      simpa [exactCoverStructuredEncodedType] using henc)
  cases I
  cases J
  simp at hsystem
  rcases hsystem with rfl
  rfl

def ExactCover (I : ExactCoverInput) : Prop :=
  SetSystemWellFormed I.system ∧
    ∃ selected : List (List Nat),
      (∀ S ∈ selected, IsSetInFamily I.system S) ∧
        selected.Nodup ∧
        PairwiseDisjointFamily selected ∧
        CoversUniverse I.system selected

def exactCoverDecisionProblem : EncodedDecisionProblem where
  Instance := exactCoverEncodedType
  isYes := ExactCover

/-- Exact Cover over the structured finite-alphabet encoding. -/
def exactCoverStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := exactCoverStructuredEncodedType
  isYes := ExactCover

/-- Karp-style hitting-set instance. -/
structure HittingSetInput where
  system : SetSystemInput
  k : Nat
  deriving Repr

def hittingSetEncodedType : EncodedType :=
  EncodedType.raw HittingSetInput

/-- Tuple-shaped finite-alphabet encoding for Hitting Set fields. -/
def hittingSetTupleStructuredEncodedType : EncodedType :=
  EncodedType.prod setSystemStructuredEncodedType EncodedType.nat

/-- Concrete finite-alphabet Hitting Set encoding. -/
def hittingSetStructuredEncodedType : EncodedType where
  Carrier := HittingSetInput
  Symbol := hittingSetTupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => hittingSetTupleStructuredEncodedType.encode (I.system, I.k)

theorem hittingSetTupleStructuredEncodedType_encode_injective :
    Function.Injective hittingSetTupleStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    setSystemStructuredEncodedType_encode_injective
    EncodedType.nat_encode_injective

theorem hittingSetStructuredEncodedType_encode_injective :
    Function.Injective hittingSetStructuredEncodedType.encode := by
  intro I J henc
  have htuple : (I.system, I.k) = (J.system, J.k) :=
    hittingSetTupleStructuredEncodedType_encode_injective (by
      simpa [hittingSetStructuredEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl⟩
  rfl

def HittingSet (I : HittingSetInput) : Prop :=
  ∃ hitting : List Nat,
    hitting.length ≤ I.k ∧
      (∀ x ∈ hitting, x < I.system.universeSize) ∧
      HitsEverySet I.system hitting

def hittingSetDecisionProblem : EncodedDecisionProblem where
  Instance := hittingSetEncodedType
  isYes := HittingSet

/-- Hitting Set over the structured finite-alphabet encoding. -/
def hittingSetStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := hittingSetStructuredEncodedType
  isYes := HittingSet

/-- Karp-style 3-dimensional-matching instance. -/
structure ThreeDimensionalMatchingInput where
  xSize : Nat
  ySize : Nat
  zSize : Nat
  triples : List (Nat × Nat × Nat)
  k : Nat
  deriving Repr

def threeDimensionalMatchingEncodedType : EncodedType :=
  EncodedType.raw ThreeDimensionalMatchingInput

/-- Structured finite-alphabet encoding for one X/Y/Z triple. -/
def tripleStructuredEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat EncodedType.nat)

/-- Structured finite-alphabet encoding for the triple family. -/
def tripleListStructuredEncodedType : EncodedType :=
  EncodedType.list tripleStructuredEncodedType

/-- Tuple-shaped finite-alphabet encoding for 3-Dimensional Matching fields. -/
def threeDimensionalMatchingTupleStructuredEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod tripleListStructuredEncodedType EncodedType.nat)))

/-- Concrete finite-alphabet 3-Dimensional Matching encoding. -/
def threeDimensionalMatchingStructuredEncodedType : EncodedType where
  Carrier := ThreeDimensionalMatchingInput
  Symbol := threeDimensionalMatchingTupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => threeDimensionalMatchingTupleStructuredEncodedType.encode
    (I.xSize, (I.ySize, (I.zSize, (I.triples, I.k))))

theorem tripleStructuredEncodedType_encode_injective :
    Function.Injective tripleStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    EncodedType.nat_encode_injective
    (EncodedType.prod_encode_injective
      EncodedType.nat_encode_injective
      EncodedType.nat_encode_injective)

theorem tripleListStructuredEncodedType_encode_injective :
    Function.Injective tripleListStructuredEncodedType.encode :=
  EncodedType.list_encode_injective tripleStructuredEncodedType_encode_injective

theorem threeDimensionalMatchingTupleStructuredEncodedType_encode_injective :
    Function.Injective threeDimensionalMatchingTupleStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    EncodedType.nat_encode_injective
    (EncodedType.prod_encode_injective
      EncodedType.nat_encode_injective
      (EncodedType.prod_encode_injective
        EncodedType.nat_encode_injective
        (EncodedType.prod_encode_injective
          tripleListStructuredEncodedType_encode_injective
          EncodedType.nat_encode_injective)))

theorem threeDimensionalMatchingStructuredEncodedType_encode_injective :
    Function.Injective threeDimensionalMatchingStructuredEncodedType.encode := by
  intro I J henc
  have htuple :
      (I.xSize, (I.ySize, (I.zSize, (I.triples, I.k)))) =
        (J.xSize, (J.ySize, (J.zSize, (J.triples, J.k)))) :=
    threeDimensionalMatchingTupleStructuredEncodedType_encode_injective (by
      simpa [threeDimensionalMatchingStructuredEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl, rfl, rfl, rfl⟩
  rfl

def TripleWithinBounds (I : ThreeDimensionalMatchingInput) (t : Nat × Nat × Nat) : Prop :=
  t.1 < I.xSize ∧ t.2.1 < I.ySize ∧ t.2.2 < I.zSize

def DisjointTriples (triples : List (Nat × Nat × Nat)) : Prop :=
  ∀ a ∈ triples, ∀ b ∈ triples, a ≠ b →
    a.1 ≠ b.1 ∧ a.2.1 ≠ b.2.1 ∧ a.2.2 ≠ b.2.2

def ThreeDimensionalMatching (I : ThreeDimensionalMatchingInput) : Prop :=
  ∃ selected : List (Nat × Nat × Nat),
    selected.length ≥ I.k ∧
      (∀ t ∈ selected, t ∈ I.triples ∧ TripleWithinBounds I t) ∧
      selected.Nodup ∧
      DisjointTriples selected

def threeDimensionalMatchingDecisionProblem : EncodedDecisionProblem where
  Instance := threeDimensionalMatchingEncodedType
  isYes := ThreeDimensionalMatching

/-- 3-Dimensional Matching over the structured finite-alphabet encoding. -/
def threeDimensionalMatchingStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := threeDimensionalMatchingStructuredEncodedType
  isYes := ThreeDimensionalMatching

end Combinatorics
end ComplexityReduction
