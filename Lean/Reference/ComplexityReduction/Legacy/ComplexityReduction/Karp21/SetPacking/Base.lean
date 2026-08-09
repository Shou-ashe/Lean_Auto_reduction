/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Clique
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.FeedbackNodeSet
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic

/-!
P15e residual set-system target: Clique to Set Packing.

The current set-packing schema is raw.  This module enumerates bounded clique
witnesses and maps nonempty witness lists to a tiny current-schema set-packing
instance.
-/

namespace ComplexityReduction
namespace Karp21
namespace SetPacking

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-- Canonical bounded clique witnesses for an input. -/
noncomputable def cliqueWitnesses (I : CliqueInput) : List (List Nat) := by
  classical
  exact (FeedbackNodeSet.vertexSubsetCandidates I.graph.vertices).filter fun vs =>
    decide
      (vs.length = I.k ∧ vs.Nodup ∧ VerticesWithinBounds I.graph vs ∧
        PairwiseAdjacent I.graph vs)

theorem mem_cliqueWitnesses_iff (I : CliqueInput) (vs : List Nat) :
    vs ∈ cliqueWitnesses I ↔
      vs ∈ FeedbackNodeSet.vertexSubsetCandidates I.graph.vertices ∧
        vs.length = I.k ∧ vs.Nodup ∧ VerticesWithinBounds I.graph vs ∧
          PairwiseAdjacent I.graph vs := by
  classical
  simp [cliqueWitnesses]

theorem clique_iff_witnesses_pos (I : CliqueInput) :
    Clique I ↔ 0 < (cliqueWitnesses I).length := by
  constructor
  · rintro ⟨vs, hLen, hNodup, hBounds, hAdj⟩
    let selected := FeedbackNodeSet.selectedVertices I.graph.vertices
      (FeedbackNodeSet.selectOfList I.graph.vertices vs)
    have hSelectedMem :
        selected ∈ FeedbackNodeSet.vertexSubsetCandidates I.graph.vertices := by
      exact FeedbackNodeSet.selectedVertices_mem_vertexSubsetCandidates I.graph.vertices
        (FeedbackNodeSet.selectOfList I.graph.vertices vs)
    have hSelectedLen : selected.length = I.k := by
      have hEq :=
        FeedbackNodeSet.selectedVertices_selectOfList_length_eq hNodup hBounds
      have hEq' : selected.length = vs.length := by
        simpa [selected] using hEq
      omega
    have hSelectedAdj : PairwiseAdjacent I.graph selected := by
      intro u hu v hv huv
      have huVs :=
        (FeedbackNodeSet.mem_selectedVertices_selectOfList_iff hBounds u).1 hu
      have hvVs :=
        (FeedbackNodeSet.mem_selectedVertices_selectOfList_iff hBounds v).1 hv
      exact hAdj u huVs v hvVs huv
    have hPred :
        selected.length = I.k ∧ selected.Nodup ∧ VerticesWithinBounds I.graph selected ∧
          PairwiseAdjacent I.graph selected := by
      exact
        ⟨hSelectedLen,
          FeedbackNodeSet.selectedVertices_nodup I.graph.vertices
            (FeedbackNodeSet.selectOfList I.graph.vertices vs),
          FeedbackNodeSet.selectedVertices_withinBounds I.graph
            (FeedbackNodeSet.selectOfList I.graph.vertices vs),
          hSelectedAdj⟩
    have hMem : selected ∈ cliqueWitnesses I :=
      (mem_cliqueWitnesses_iff I selected).2 ⟨hSelectedMem, hPred⟩
    exact List.length_pos_of_mem hMem
  · intro hPos
    cases hList : cliqueWitnesses I with
    | nil =>
        simp [hList] at hPos
    | cons vs rest =>
        have hMem : vs ∈ cliqueWitnesses I := by
          simp [hList]
        rcases (mem_cliqueWitnesses_iff I vs).1 hMem with
          ⟨_hCandidate, hLen, hNodup, hBounds, hAdj⟩
        exact ⟨vs, hLen, hNodup, hBounds, hAdj⟩

theorem hasUndirectedEdge_comm (g : GraphInput) (u v : Nat) :
    HasUndirectedEdge g u v ↔ HasUndirectedEdge g v u := by
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  · intro h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h

def vertexMarker (v : Nat) : Nat :=
  Nat.pair 0 v

def directedConflictCode (u v : Nat) : Nat :=
  Nat.pair 1 (Nat.pair u v)

noncomputable def conflictCodesFor (g : GraphInput) (owner other : Nat) : List Nat := by
  classical
  exact
    if owner ≠ other ∧ ¬ HasUndirectedEdge g owner other then
      [directedConflictCode owner other, directedConflictCode other owner]
    else
      []

noncomputable def textbookPackingSet (I : CliqueInput) (v : Nat) : List Nat :=
  vertexMarker v ::
    (List.range I.graph.vertices).flatMap (conflictCodesFor I.graph v)

theorem mem_textbookPackingSet_iff (I : CliqueInput) (v x : Nat) :
    x ∈ textbookPackingSet I v ↔
      x = vertexMarker v ∨
        ∃ u, u < I.graph.vertices ∧
          v ≠ u ∧ ¬ HasUndirectedEdge I.graph v u ∧
          (x = directedConflictCode v u ∨ x = directedConflictCode u v) := by
  classical
  simp [textbookPackingSet, conflictCodesFor, and_assoc]

theorem marker_ne_conflict (v u w : Nat) :
    vertexMarker v ≠ directedConflictCode u w := by
  intro h
  have h01 : 0 = 1 := (Nat.pair_eq_pair.mp h).1
  omega

theorem textbookPackingSet_injective_on {I : CliqueInput} {u v : Nat}
    (h : textbookPackingSet I u = textbookPackingSet I v) :
    u = v := by
  have hHead := congrArg List.head? h
  simpa [textbookPackingSet, vertexMarker] using hHead

theorem common_conflict_of_nonedge {I : CliqueInput} {u v : Nat}
    (hu : u < I.graph.vertices) (hv : v < I.graph.vertices) (huv : u ≠ v)
    (hNonedge : ¬ HasUndirectedEdge I.graph u v) :
    directedConflictCode u v ∈ textbookPackingSet I u ∧
      directedConflictCode u v ∈ textbookPackingSet I v := by
  classical
  constructor
  · rw [mem_textbookPackingSet_iff]
    exact Or.inr ⟨v, hv, huv, hNonedge, Or.inl rfl⟩
  · rw [mem_textbookPackingSet_iff]
    exact Or.inr
      ⟨u, hu,
        Ne.symm huv,
        by
          intro h
          exact hNonedge ((hasUndirectedEdge_comm I.graph u v).2 h),
        Or.inr rfl⟩

theorem no_common_textbookPackingSet_of_edge {I : CliqueInput} {u v x : Nat}
    (huv : u ≠ v) (hEdge : HasUndirectedEdge I.graph u v)
    (hxU : x ∈ textbookPackingSet I u)
    (hxV : x ∈ textbookPackingSet I v) :
    False := by
  rcases (mem_textbookPackingSet_iff I u x).1 hxU with hxMarkerU | hxConflictU
  · rcases (mem_textbookPackingSet_iff I v x).1 hxV with hxMarkerV | hxConflictV
    · have hMarkers : vertexMarker u = vertexMarker v := by omega
      exact huv ((Nat.pair_eq_pair.mp hMarkers).2)
    · rcases hxConflictV with ⟨w, _hw, _hvw, _hNon, hxCode | hxCode⟩
      · have hBad : vertexMarker u = directedConflictCode v w := by omega
        exact marker_ne_conflict u v w hBad
      · have hBad : vertexMarker u = directedConflictCode w v := by omega
        exact marker_ne_conflict u w v hBad
  · rcases hxConflictU with ⟨w, _hw, _huw, _hNon, hxCodeU | hxCodeU⟩
    · rcases (mem_textbookPackingSet_iff I v x).1 hxV with hxMarkerV | hxConflictV
      · have hBad : vertexMarker v = directedConflictCode u w := by omega
        exact marker_ne_conflict v u w hBad
      · rcases hxConflictV with ⟨z, _hz, _hvz, hNonVZ, hxCodeV | hxCodeV⟩
        · have hEq : directedConflictCode u w = directedConflictCode v z := by omega
          have hUV : u = v := (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp hEq).2).1
          exact huv hUV
        · have hEq : directedConflictCode u w = directedConflictCode z v := by omega
          have hPairs := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp hEq).2
          have hZU : z = u := hPairs.1.symm
          have hWV : w = v := hPairs.2
          subst z
          subst w
          exact hNonVZ ((hasUndirectedEdge_comm I.graph u v).1 hEdge)
    · rcases (mem_textbookPackingSet_iff I v x).1 hxV with hxMarkerV | hxConflictV
      · have hBad : vertexMarker v = directedConflictCode w u := by omega
        exact marker_ne_conflict v w u hBad
      · rcases hxConflictV with ⟨z, _hz, _hvz, hNonVZ, hxCodeV | hxCodeV⟩
        · have hEq : directedConflictCode w u = directedConflictCode v z := by omega
          have hPairs := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp hEq).2
          have hWV : w = v := hPairs.1
          have hUZ : u = z := hPairs.2
          subst w
          subst z
          exact hNonVZ ((hasUndirectedEdge_comm I.graph u v).1 hEdge)
        · have hEq : directedConflictCode w u = directedConflictCode z v := by omega
          have hUV : u = v := (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp hEq).2).2
          exact huv hUV

noncomputable def textbookSetSystem (I : CliqueInput) : SetSystemInput where
  universeSize := I.graph.vertices + I.graph.vertices * I.graph.vertices
  sets := (List.range I.graph.vertices).map (textbookPackingSet I)

theorem mem_textbookSetSystem_sets_iff (I : CliqueInput) (S : List Nat) :
    S ∈ (textbookSetSystem I).sets ↔
      ∃ v, v < I.graph.vertices ∧ S = textbookPackingSet I v := by
  constructor
  · intro hS
    rcases List.mem_map.mp hS with ⟨v, hv, rfl⟩
    exact ⟨v, by simpa using hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact List.mem_map.mpr ⟨v, by simpa using hv, rfl⟩

noncomputable def vertexOfTextbookSet (I : CliqueInput) (S : List Nat) : Nat := by
  classical
  exact if h : S ∈ (textbookSetSystem I).sets then
    Classical.choose ((mem_textbookSetSystem_sets_iff I S).1 h)
  else 0

theorem vertexOfTextbookSet_lt_of_mem (I : CliqueInput) {S : List Nat}
    (hS : S ∈ (textbookSetSystem I).sets) :
    vertexOfTextbookSet I S < I.graph.vertices := by
  classical
  simp [vertexOfTextbookSet, hS,
    (Classical.choose_spec ((mem_textbookSetSystem_sets_iff I S).1 hS)).1]

theorem textbookPackingSet_vertexOfTextbookSet_of_mem (I : CliqueInput) {S : List Nat}
    (hS : S ∈ (textbookSetSystem I).sets) :
    S = textbookPackingSet I (vertexOfTextbookSet I S) := by
  classical
  unfold vertexOfTextbookSet
  rw [dif_pos hS]
  exact (Classical.choose_spec ((mem_textbookSetSystem_sets_iff I S).1 hS)).2

noncomputable def textbookMap (I : CliqueInput) : SetPackingInput where
  system := textbookSetSystem I
  k := I.k

theorem textbookMap_correct (I : CliqueInput) :
    cliqueDecisionProblem.isYes I ↔ SetPacking (textbookMap I) := by
  constructor
  · rintro ⟨vs, hLen, hNodup, hBounds, hAdj⟩
    let selected := vs.map (textbookPackingSet I)
    refine ⟨selected, by simp [selected, textbookMap, hLen], ?_, ?_, ?_⟩
    · intro S hS
      rcases List.mem_map.mp hS with ⟨v, hv, rfl⟩
      exact (mem_textbookSetSystem_sets_iff I (textbookPackingSet I v)).2
        ⟨v, hBounds v hv, rfl⟩
    · exact hNodup.map_on (by
        intro u _hu v _hv hEq
        exact textbookPackingSet_injective_on hEq)
    · intro A hA B hB hNe x hxA hxB
      rcases List.mem_map.mp hA with ⟨u, hu, rfl⟩
      rcases List.mem_map.mp hB with ⟨v, hv, rfl⟩
      by_cases huv : u = v
      · subst v
        exact hNe rfl
      · exact no_common_textbookPackingSet_of_edge huv (hAdj u hu v hv huv) hxA hxB
  · rintro ⟨selected, hLen, hFamily, hNodup, hDisjoint⟩
    let chosenSets := selected.take I.k
    let vs := chosenSets.map (vertexOfTextbookSet I)
    have hChosenSub : chosenSets.Sublist selected := by
      exact List.take_sublist I.k selected
    have hChosenNodup : chosenSets.Nodup := List.Nodup.sublist hChosenSub hNodup
    have hk : I.k ≤ selected.length := by
      simpa [textbookMap] using hLen
    refine ⟨vs, ?_, ?_, ?_, ?_⟩
    · simp [vs, chosenSets, List.length_take, Nat.min_eq_left hk]
    · exact hChosenNodup.map_on (by
        intro A hA B hB hEq
        have hASelected : A ∈ selected := hChosenSub.subset hA
        have hBSelected : B ∈ selected := hChosenSub.subset hB
        have hAFamily := hFamily A hASelected
        have hBFamily := hFamily B hBSelected
        calc
          A = textbookPackingSet I (vertexOfTextbookSet I A) :=
            textbookPackingSet_vertexOfTextbookSet_of_mem I hAFamily
          _ = textbookPackingSet I (vertexOfTextbookSet I B) := by rw [hEq]
          _ = B := (textbookPackingSet_vertexOfTextbookSet_of_mem I hBFamily).symm)
    · intro v hv
      rcases List.mem_map.mp hv with ⟨S, hS, rfl⟩
      exact vertexOfTextbookSet_lt_of_mem I (hFamily S (hChosenSub.subset hS))
    · intro u hu v hv huv
      rcases List.mem_map.mp hu with ⟨A, hA, rfl⟩
      rcases List.mem_map.mp hv with ⟨B, hB, rfl⟩
      have hASelected : A ∈ selected := hChosenSub.subset hA
      have hBSelected : B ∈ selected := hChosenSub.subset hB
      have hAFamily := hFamily A hASelected
      have hBFamily := hFamily B hBSelected
      have hAeq := textbookPackingSet_vertexOfTextbookSet_of_mem I hAFamily
      have hBeq := textbookPackingSet_vertexOfTextbookSet_of_mem I hBFamily
      by_contra hNonedge
      have hCommon := common_conflict_of_nonedge
        (vertexOfTextbookSet_lt_of_mem I hAFamily)
        (vertexOfTextbookSet_lt_of_mem I hBFamily)
        huv hNonedge
      have hAneB : A ≠ B := by
        intro hAB
        exact huv (by simp [hAB])
      let conflict :=
        directedConflictCode (vertexOfTextbookSet I A) (vertexOfTextbookSet I B)
      have hAConflict : conflict ∈ A := by
        change conflict ∈ A
        rw [hAeq]
        exact hCommon.1
      have hBConflict : conflict ∈ B := by
        change conflict ∈ B
        rw [hBeq]
        exact hCommon.2
      exact hDisjoint A hASelected B hBSelected hAneB conflict hAConflict hBConflict

/-- Coarse bound for unary encodings of the paired marker/conflict codes. -/
def textbookCodeInputSizeBound (n : Nat) : Nat :=
  ((n + 1) ^ 2 + 2) ^ 2

theorem vertexMarker_inputSize_le (n v : Nat) (hv : v < n) :
    EncodedType.nat.inputSize (vertexMarker v) ≤ textbookCodeInputSizeBound n := by
  have hPairLt : vertexMarker v < (max 0 v + 1) ^ 2 := by
    simpa [vertexMarker] using Nat.pair_lt_max_add_one_sq 0 v
  have hMax : max 0 v + 1 ≤ n + 1 := by
    omega
  have hPairBound : vertexMarker v + 1 ≤ (n + 1) ^ 2 :=
    Nat.succ_le_of_lt (hPairLt.trans_le (Nat.pow_le_pow_left hMax 2))
  have hBig : (n + 1) ^ 2 ≤ textbookCodeInputSizeBound n := by
    unfold textbookCodeInputSizeBound
    ring_nf
    omega
  simpa [EncodedType.inputSize, EncodedType.nat] using hPairBound.trans hBig

theorem directedConflictCode_inputSize_le (n u v : Nat) (hu : u < n) (hv : v < n) :
    EncodedType.nat.inputSize (directedConflictCode u v) ≤
      textbookCodeInputSizeBound n := by
  let inner := Nat.pair u v
  have hInnerLt : inner < (max u v + 1) ^ 2 := by
    simpa [inner] using Nat.pair_lt_max_add_one_sq u v
  have hMaxUV : max u v + 1 ≤ n + 1 := by
    have hMaxLe : max u v ≤ n := max_le (le_of_lt hu) (le_of_lt hv)
    omega
  have hInnerBound : inner + 1 ≤ (n + 1) ^ 2 :=
    Nat.succ_le_of_lt (hInnerLt.trans_le (Nat.pow_le_pow_left hMaxUV 2))
  have hOuterArg : max 1 inner + 1 ≤ (n + 1) ^ 2 + 2 := by
    have hMaxOuter : max 1 inner ≤ inner + 1 := by
      exact max_le (Nat.succ_pos inner) (Nat.le_succ inner)
    omega
  have hOuterLt :
      directedConflictCode u v < textbookCodeInputSizeBound n := by
    unfold directedConflictCode textbookCodeInputSizeBound
    exact (Nat.pair_lt_max_add_one_sq 1 inner).trans_le
      (Nat.pow_le_pow_left hOuterArg 2)
  simpa [EncodedType.inputSize, EncodedType.nat] using Nat.succ_le_of_lt hOuterLt

theorem textbookPackingSet_nat_inputSize_le (I : CliqueInput) {v x : Nat}
    (hv : v < I.graph.vertices) (hx : x ∈ textbookPackingSet I v) :
    EncodedType.nat.inputSize x ≤ textbookCodeInputSizeBound I.graph.vertices := by
  rcases (mem_textbookPackingSet_iff I v x).1 hx with hxMarker | hxConflict
  · subst x
    exact vertexMarker_inputSize_le I.graph.vertices v hv
  · rcases hxConflict with ⟨u, hu, _huv, _hNon, hxCode | hxCode⟩
    · subst x
      exact directedConflictCode_inputSize_le I.graph.vertices v u hv hu
    · subst x
      exact directedConflictCode_inputSize_le I.graph.vertices u v hu hv

theorem conflictCodesFor_length_le (g : GraphInput) (owner other : Nat) :
    (conflictCodesFor g owner other).length ≤ 2 := by
  classical
  unfold conflictCodesFor
  split_ifs <;> simp

theorem flatMap_length_le_mul {α β : Type} (xs : List α) (f : α → List β) (B : Nat)
    (hB : ∀ x ∈ xs, (f x).length ≤ B) :
    (xs.flatMap f).length ≤ xs.length * B := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : (f x).length ≤ B := hB x (by simp)
      have htail : ∀ y ∈ xs, (f y).length ≤ B := by
        intro y hy
        exact hB y (by simp [hy])
      have ih' := ih htail
      calc
        ((x :: xs).flatMap f).length = (f x).length + (xs.flatMap f).length := by
          simp
        _ ≤ B + xs.length * B := by
          omega
        _ = (x :: xs).length * B := by
          simp [Nat.succ_mul, Nat.add_comm]

theorem textbookPackingSet_length_le (I : CliqueInput) (v : Nat) :
    (textbookPackingSet I v).length ≤ 1 + I.graph.vertices * 2 := by
  have hFlat :=
    flatMap_length_le_mul (List.range I.graph.vertices)
      (conflictCodesFor I.graph v) 2 (by
        intro u _hu
        exact conflictCodesFor_length_le I.graph v u)
  simp [textbookPackingSet] at hFlat ⊢
  omega

theorem textbookPackingSet_structured_inputSize_le (I : CliqueInput) {v : Nat}
    (hv : v < I.graph.vertices) :
    setStructuredEncodedType.inputSize (textbookPackingSet I v) ≤
      (1 + I.graph.vertices * 2) *
        (textbookCodeInputSizeBound I.graph.vertices + 1) := by
  have hList :=
    ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
      EncodedType.nat (textbookPackingSet I v)
      (textbookCodeInputSizeBound I.graph.vertices)
      (by
        intro x hx
        exact textbookPackingSet_nat_inputSize_le I hv hx)
  have hLen := textbookPackingSet_length_le I v
  exact hList.trans (by
    have hMul :=
      Nat.mul_le_mul_right (textbookCodeInputSizeBound I.graph.vertices + 1) hLen
    simpa [setStructuredEncodedType] using hMul)

theorem textbookSetSystem_family_structured_inputSize_le (I : CliqueInput) :
    setFamilyStructuredEncodedType.inputSize (textbookSetSystem I).sets ≤
      I.graph.vertices *
        ((1 + I.graph.vertices * 2) *
          (textbookCodeInputSizeBound I.graph.vertices + 1) + 1) := by
  have hList :=
    ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
      setStructuredEncodedType (textbookSetSystem I).sets
      ((1 + I.graph.vertices * 2) *
        (textbookCodeInputSizeBound I.graph.vertices + 1))
      (by
        intro S hS
        rcases (mem_textbookSetSystem_sets_iff I S).1 hS with ⟨v, hv, rfl⟩
        exact textbookPackingSet_structured_inputSize_le I hv)
  have hLen : (textbookSetSystem I).sets.length = I.graph.vertices := by
    simp [textbookSetSystem]
  exact hList.trans (by
    exact Nat.mul_le_mul_right
      ((1 + I.graph.vertices * 2) *
        (textbookCodeInputSizeBound I.graph.vertices + 1) + 1)
      (le_of_eq hLen))

theorem setSystemStructured_inputSize_eq (S : SetSystemInput) :
    setSystemStructuredEncodedType.inputSize S =
      S.universeSize + setFamilyStructuredEncodedType.inputSize S.sets + 2 := by
  change setSystemTupleStructuredEncodedType.inputSize (S.universeSize, S.sets) =
    S.universeSize + setFamilyStructuredEncodedType.inputSize S.sets + 2
  simp [setSystemTupleStructuredEncodedType]
  omega

theorem textbookSetSystem_structured_inputSize_le (I : CliqueInput) :
    setSystemStructuredEncodedType.inputSize (textbookSetSystem I) ≤
      (I.graph.vertices + I.graph.vertices * I.graph.vertices) +
        I.graph.vertices *
          ((1 + I.graph.vertices * 2) *
            (textbookCodeInputSizeBound I.graph.vertices + 1) + 1) + 2 := by
  have hFamily := textbookSetSystem_family_structured_inputSize_le I
  rw [setSystemStructured_inputSize_eq]
  change
    (I.graph.vertices + I.graph.vertices * I.graph.vertices) +
        setFamilyStructuredEncodedType.inputSize (textbookSetSystem I).sets + 2 ≤
      (I.graph.vertices + I.graph.vertices * I.graph.vertices) +
        I.graph.vertices *
          ((1 + I.graph.vertices * 2) *
            (textbookCodeInputSizeBound I.graph.vertices + 1) + 1) + 2
  omega

theorem setPackingStructured_inputSize_eq (I : SetPackingInput) :
    setPackingStructuredEncodedType.inputSize I =
      setSystemStructuredEncodedType.inputSize I.system + I.k + 2 := by
  change setPackingTupleStructuredEncodedType.inputSize (I.system, I.k) =
    setSystemStructuredEncodedType.inputSize I.system + I.k + 2
  simp [setPackingTupleStructuredEncodedType]
  omega

theorem cliqueStructured_inputSize_ge_budget (I : CliqueInput) :
    I.k ≤ cliqueStructuredEncodedType.inputSize I := by
  change I.k ≤ cliqueTupleStructuredEncodedType.inputSize (I.graph, I.k)
  simp [cliqueTupleStructuredEncodedType]
  omega

/-- Structured output size of the textbook Clique-to-Set-Packing map is polynomial in
the structured source size. -/
theorem setPackingStructured_inputSize_textbookMap_le_clique_poly (I : CliqueInput) :
    setPackingStructuredEncodedType.inputSize (textbookMap I) ≤
      1000 * (cliqueStructuredEncodedType.inputSize I + 1) ^ 6 + 1000 := by
  let S := cliqueStructuredEncodedType.inputSize I
  let n := I.graph.vertices
  have hSystem := textbookSetSystem_structured_inputSize_le I
  have hNsucc : n + 1 ≤ S := by
    simpa [S, n] using
      ComplexityReduction.Karp21.VertexCover.cliqueStructured_inputSize_ge_vertices_succ I
  have hN : n ≤ S := by omega
  have hK : I.k ≤ S := by
    simpa [S] using cliqueStructured_inputSize_ge_budget I
  have hCode :
      textbookCodeInputSizeBound n + 1 ≤ ((S + 1) ^ 2 + 2) ^ 2 + 1 := by
    unfold textbookCodeInputSizeBound
    have hPow₁ : (n + 1) ^ 2 ≤ (S + 1) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have hPow₂ : ((n + 1) ^ 2 + 2) ^ 2 ≤ ((S + 1) ^ 2 + 2) ^ 2 :=
      Nat.pow_le_pow_left (Nat.add_le_add_right hPow₁ 2) 2
    omega
  have hSetLen : 1 + n * 2 ≤ 2 * S + 1 := by omega
  have hSetSize :
      (1 + n * 2) * (textbookCodeInputSizeBound n + 1) ≤
        (2 * S + 1) * (((S + 1) ^ 2 + 2) ^ 2 + 1) :=
    Nat.mul_le_mul hSetLen hCode
  have hFamily :
      n * ((1 + n * 2) * (textbookCodeInputSizeBound n + 1) + 1) ≤
        S * ((2 * S + 1) * (((S + 1) ^ 2 + 2) ^ 2 + 1) + 1) :=
    Nat.mul_le_mul hN (Nat.add_le_add_right hSetSize 1)
  calc
    setPackingStructuredEncodedType.inputSize (textbookMap I)
        = setSystemStructuredEncodedType.inputSize (textbookSetSystem I) + I.k + 2 := by
            simp [textbookMap, setPackingStructured_inputSize_eq]
    _ ≤ ((n + n * n) +
          n * ((1 + n * 2) * (textbookCodeInputSizeBound n + 1) + 1) + 2) +
          I.k + 2 := by
            simpa [n] using Nat.add_le_add_right (Nat.add_le_add_right hSystem I.k) 2
    _ ≤ (S + S * S) +
          S * ((2 * S + 1) * (((S + 1) ^ 2 + 2) ^ 2 + 1) + 1) + 2 + S + 2 := by
            have hUniverse : n + n * n ≤ S + S * S := by
              exact Nat.add_le_add hN (Nat.mul_le_mul hN hN)
            omega
    _ ≤ 1000 * (S + 1) ^ 6 + 1000 := by
            ring_nf
            omega

/-- Polynomial output-size bound for the structured textbook Clique-to-Set-Packing map. -/
theorem cliqueToSetPackingStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : CliqueInput => cliqueStructuredEncodedType.inputSize I)
      (fun J : SetPackingInput => setPackingStructuredEncodedType.inputSize J)
      textbookMap := by
  refine PolynomialSizeBound.intro_with 6 100000 100000 ?_
  intro I
  let S := cliqueStructuredEncodedType.inputSize I
  have hBase := setPackingStructured_inputSize_textbookMap_le_clique_poly I
  have hPoly : 1000 * (S + 1) ^ 6 + 1000 ≤ 100000 * S ^ 6 + 100000 := by
    cases S with
    | zero =>
        norm_num
    | succ S =>
        ring_nf
        omega
  exact hBase.trans hPoly

/--
Proof-carrying TM2/costed reduction for the current raw-encoded Set Packing
target using the P15i textbook incidence gadget.  This is not a
natural-language encoding conformance theorem.
-/
noncomputable def cliqueToSetPacking_textbookTMBackedKarpReduction :
    TMBackedCostedReduction cliqueDecisionProblem setPackingDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    (TMBackedCostedMap.rawCodomain cliqueDecisionProblem.Instance SetPackingInput textbookMap)
    textbookMap_correct

noncomputable def cliqueToSetPacking_textbookKarpReduction :
    KarpReductionM CostedPolyTimeModel cliqueDecisionProblem setPackingDecisionProblem :=
  cliqueToSetPacking_textbookTMBackedKarpReduction.toCostedKarpReduction

/--
Costed Karp reduction from the faithful finite-alphabet Clique encoding to the
faithful finite-alphabet Set Packing encoding, using the P15i textbook incidence
gadget.

This is a structured `CostedPolyTimeModel` transport theorem, not a direct TM2
soundness theorem.
-/
noncomputable def cliqueToSetPackingStructuredCostedFallbackKarpReduction :
    KarpReductionM CostedPolyTimeModel
      cliqueStructuredDecisionProblem setPackingStructuredDecisionProblem where
  f :=
    { toFun := textbookMap
      polytime :=
        CostedPolyTimeMap.of_costed
          (CostedMap.of_encodedPolynomialSizeBound
            cliqueToSetPackingStructured_polynomialSizeBound) }
  correct := by
    intro I
    simpa [cliqueStructuredDecisionProblem, setPackingStructuredDecisionProblem,
      cliqueDecisionProblem] using textbookMap_correct I

/-- A tiny yes-instance for current-schema Set Packing. -/
def yesInput : SetPackingInput where
  system := { universeSize := 1, sets := [[0]] }
  k := 1

/-- A tiny no-instance for current-schema Set Packing. -/
def noInput : SetPackingInput where
  system := { universeSize := 1, sets := [] }
  k := 1

theorem yesInput_isYes :
    SetPacking yesInput := by
  refine ⟨[[0]], by simp [yesInput], ?_, ?_, ?_⟩
  · intro S hS
    simp [yesInput, IsSetInFamily] at hS ⊢
    exact hS
  · simp
  · intro A hA B hB hNe x hxA hxB
    simp at hA hB
    subst A
    subst B
    exact hNe rfl

theorem noInput_isNo :
    ¬ SetPacking noInput := by
  rintro ⟨selected, hLen, hFamily, _hDisjoint⟩
  cases selected with
  | nil =>
      simp [noInput] at hLen
  | cons S rest =>
      have hS := hFamily S (by simp)
      simp [noInput, IsSetInFamily] at hS

/-- Indicator family: yes exactly when the source witness list is nonempty. -/
def indicatorInput (m : Nat) : SetPackingInput :=
  if 0 < m then yesInput else noInput

theorem indicatorInput_correct (m : Nat) :
    SetPacking (indicatorInput m) ↔ 0 < m := by
  by_cases hm : 0 < m
  · constructor
    · intro _; exact hm
    · intro _; simpa [indicatorInput, hm] using yesInput_isYes
  · constructor
    · intro h
      exact (noInput_isNo (by simpa [indicatorInput, hm] using h)).elim
    · intro h
      exact (hm h).elim

/-- P15e syntax map from Clique to Set Packing. -/
noncomputable def map (I : CliqueInput) : SetPackingInput :=
  indicatorInput (cliqueWitnesses I).length

theorem map_correct (I : CliqueInput) :
    cliqueDecisionProblem.isYes I ↔ SetPacking (map I) := by
  change Clique I ↔ SetPacking (map I)
  rw [clique_iff_witnesses_pos]
  exact (indicatorInput_correct (cliqueWitnesses I).length).symm

/--
Proof-carrying TM2/costed reduction for the current raw-encoded Set Packing
target using the legacy indicator fallback map.
-/
noncomputable def cliqueToSetPackingTMBackedKarpReduction :
    TMBackedCostedReduction cliqueDecisionProblem setPackingDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    (TMBackedCostedMap.rawCodomain cliqueDecisionProblem.Instance SetPackingInput map)
    map_correct

/-- Costed Karp reduction from Clique to Set Packing. -/
noncomputable def cliqueToSetPackingKarpReduction :
    KarpReductionM CostedPolyTimeModel cliqueDecisionProblem setPackingDecisionProblem :=
  cliqueToSetPackingTMBackedKarpReduction.toCostedKarpReduction

/-- First witness in the raw-encoding collision for Set Packing. -/
def rawEncodingCollisionA : SetPackingInput where
  system := { universeSize := 0, sets := [] }
  k := 0

/-- Second witness in the raw-encoding collision for Set Packing. -/
def rawEncodingCollisionB : SetPackingInput where
  system := { universeSize := 1, sets := [] }
  k := 0

theorem rawEncodingCollisionA_ne_rawEncodingCollisionB :
    rawEncodingCollisionA ≠ rawEncodingCollisionB := by
  intro h
  have hu :
      rawEncodingCollisionA.system.universeSize =
        rawEncodingCollisionB.system.universeSize :=
    congrArg (fun I : SetPackingInput => I.system.universeSize) h
  norm_num [rawEncodingCollisionA, rawEncodingCollisionB] at hu

/--
The current raw encoding for Set Packing is not faithful: two different formal
instances encode as the same empty string.
-/
theorem setPackingRawEncoding_not_faithful :
    ¬ setPackingDecisionProblem.FaithfulEncoding := by
  refine EncodedDecisionProblem.EncodingCollision.not_faithful ?_
  exact
    ⟨rawEncodingCollisionA, rawEncodingCollisionB,
      rawEncodingCollisionA_ne_rawEncodingCollisionB, rfl⟩

/-- The structured finite-alphabet Set Packing encoding is faithful. -/
theorem setPackingStructuredEncoding_faithful :
    setPackingStructuredDecisionProblem.FaithfulEncoding where
  injective := setPackingStructuredEncodedType_encode_injective

theorem setPackingStructuredEncoding_predicateRespects :
    setPackingStructuredDecisionProblem.PredicateRespectsEncoding :=
  setPackingStructuredEncoding_faithful.predicateRespects

theorem setPackingStructuredEncoding_accepts_encode_iff (I : SetPackingInput) :
    setPackingStructuredDecisionProblem.toEncodedLanguage.accepts
        (setPackingStructuredEncodedType.encode I) ↔
      SetPacking I :=
  setPackingStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

/-- Set Packing is locally in NP for the project-local costed model. -/
theorem setPackingInNP :
    InNPEnc CostedPolyTimeModel setPackingDecisionProblem :=
  decidableInNP setPackingDecisionProblem

/-- Local NP-completeness of Set Packing via Clique. -/
theorem setPackingNPComplete :
    NPCompleteEnc CostedPolyTimeModel setPackingDecisionProblem :=
  NPCompleteEnc.transfer
    Clique.cliqueNPComplete
    ⟨cliqueToSetPackingKarpReduction⟩
    setPackingInNP

/-- Local NP-completeness of Set Packing via the P15i textbook incidence gadget. -/
theorem setPacking_textbookNPComplete :
    NPCompleteEnc CostedPolyTimeModel setPackingDecisionProblem :=
  NPCompleteEnc.transfer
    Clique.cliqueNPComplete
    ⟨cliqueToSetPacking_textbookKarpReduction⟩
    setPackingInNP

end SetPacking
end Karp21
end ComplexityReduction
