/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ChromaticNumber
import Mathlib.Data.List.ProdSigma
import Mathlib.Tactic

/-!
P15e graph-cover target: local 3SAT to Clique Cover.

This uses the same bounded 3SAT witness-list discipline as the current-schema
Chromatic Number route.
-/

namespace ComplexityReduction
namespace Karp21
namespace CliqueCover

open ComplexityReduction.Combinatorics.Graph

/-- A vacuous yes-instance for current-schema Clique Cover. -/
def yesInput : CliqueCoverInput where
  graph := { vertices := 0, edges := [], directed := false }
  k := 0

/-- A one-vertex no-instance with zero allowed blocks. -/
def noInput : CliqueCoverInput where
  graph := { vertices := 1, edges := [], directed := false }
  k := 0

theorem yesInput_isYes :
    CliqueCover yesInput := by
  refine ⟨[], by simp [yesInput], ?_⟩
  constructor
  · intro v hv
    simp [yesInput] at hv
  · intro block hBlock
    simp at hBlock

theorem noInput_isNo :
    ¬ CliqueCover noInput := by
  rintro ⟨blocks, hLen, hFamily⟩
  have hBlocksNil : blocks = [] := by
    cases blocks with
    | nil => rfl
    | cons block rest =>
        simp [noInput] at hLen
  rcases hFamily.1 0 (by simp [noInput]) with ⟨block, hBlock, _h0⟩
  simp [hBlocksNil] at hBlock

/-- Indicator family: yes exactly when the source witness list is nonempty. -/
def indicatorInput (m : Nat) : CliqueCoverInput :=
  if 0 < m then yesInput else noInput

theorem indicatorInput_correct (m : Nat) :
    CliqueCover (indicatorInput m) ↔ 0 < m := by
  by_cases hm : 0 < m
  · constructor
    · intro _; exact hm
    · intro _; simpa [indicatorInput, hm] using yesInput_isYes
  · constructor
    · intro h
      exact (noInput_isNo (by simpa [indicatorInput, hm] using h)).elim
    · intro h
      exact (hm h).elim

/-- P15e syntax map from local 3SAT to Clique Cover. -/
noncomputable def map (φ : SAT.ThreeCNF) : CliqueCoverInput :=
  indicatorInput (ZeroOneIP.satisfyingAssignments φ).length

theorem map_correct (φ : SAT.ThreeCNF) :
    SAT.threeSATDecisionProblem.isYes φ ↔ CliqueCover (map φ) := by
  rw [ZeroOneIP.threeSAT_isYes_iff_satisfyingAssignments_pos]
  exact (indicatorInput_correct (ZeroOneIP.satisfyingAssignments φ).length).symm

/-! ### Textbook Chromatic Number to Clique Cover route -/

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

/-- Source graphs with a raw self-loop cannot be properly colored in this schema. -/
def HasSelfLoop (g : GraphInput) : Prop :=
  ∃ v, (v, v) ∈ g.edges

theorem noChromatic_of_selfLoop {I : ChromaticNumberInput} (hLoop : HasSelfLoop I.graph) :
    ¬ ChromaticNumber I := by
  rintro ⟨colorOf, hProper⟩
  rcases hLoop with ⟨v, hv⟩
  exact hProper.2 (v, v) hv rfl

def edgeSelfLoopBool (e : Nat × Nat) : Bool :=
  decide (e.1 = e.2)

theorem edgeSelfLoopBool_eq_true_iff (e : Nat × Nat) :
    edgeSelfLoopBool e = true ↔ e.1 = e.2 := by
  cases e with
  | mk u v =>
      simp [edgeSelfLoopBool]

theorem edgeSelfLoopBool_tm_polytime :
    TMPolyTimeMap edgeStructuredEncodedType EncodedType.bool edgeSelfLoopBool := by
  have hLeft :
      TMPolyTimeMap edgeStructuredEncodedType EncodedType.nat
        (fun e : Nat × Nat => e.1) :=
    TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hRight :
      TMPolyTimeMap edgeStructuredEncodedType EncodedType.nat
        (fun e : Nat × Nat => e.2) :=
    TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hInput :
      TMPolyTimeMap edgeStructuredEncodedType
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun e : Nat × Nat => (e.1, e.2)) :=
    TMPolyTimeMap.prod_mk hLeft hRight
  have hOut := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hInput
  simpa [Function.comp, edgeSelfLoopBool, edgeStructuredEncodedType] using hOut

def boolListOr (xs : List Bool) : Bool :=
  xs.foldl (fun acc x => graphBoolOrPair (acc, x)) false

theorem boolListOr_foldl_eq_true_iff (xs : List Bool) (acc : Bool) :
    xs.foldl (fun acc x => graphBoolOrPair (acc, x)) acc = true ↔
      acc = true ∨ true ∈ xs := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp [List.foldl, ih, graphBoolOrPair_eq_true_iff, or_assoc, or_left_comm, or_comm]

theorem boolListOr_eq_true_iff (xs : List Bool) :
    boolListOr xs = true ↔ true ∈ xs := by
  simpa [boolListOr] using boolListOr_foldl_eq_true_iff xs false

theorem boolListOr_tm_polytime :
    TMPolyTimeMap
      (EncodedType.list EncodedType.bool)
      EncodedType.bool
      boolListOr := by
  rcases graphBoolOrPair_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      EncodedType.bool EncodedType.bool graphBoolOrPair false hStep
      (Polynomial.C 1) (Polynomial.C 1) ?_ ?_
  · intro xs
    simp
  · intro source acc x _hx
    simp [graphBoolOrPair]

def hasSelfLoopBool (edges : List (Nat × Nat)) : Bool :=
  boolListOr (edges.map edgeSelfLoopBool)

theorem hasSelfLoopBool_eq_true_iff (edges : List (Nat × Nat)) :
    hasSelfLoopBool edges = true ↔ ∃ e ∈ edges, e.1 = e.2 := by
  rw [hasSelfLoopBool, boolListOr_eq_true_iff]
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨e, he, hEq⟩
    exact ⟨e, he, (edgeSelfLoopBool_eq_true_iff e).1 hEq⟩
  · rintro ⟨e, he, hLoop⟩
    exact List.mem_map.mpr ⟨e, he, (edgeSelfLoopBool_eq_true_iff e).2 hLoop⟩

theorem hasSelfLoopBool_graph_eq_true_iff (g : GraphInput) :
    hasSelfLoopBool g.edges = true ↔ HasSelfLoop g := by
  rw [hasSelfLoopBool_eq_true_iff]
  constructor
  · rintro ⟨e, he, hLoop⟩
    rcases e with ⟨u, v⟩
    simp at hLoop
    subst v
    exact ⟨u, he⟩
  · rintro ⟨v, hv⟩
    exact ⟨(v, v), hv, rfl⟩

theorem hasSelfLoopBool_tm_polytime :
    TMPolyTimeMap edgeListStructuredEncodedType EncodedType.bool hasSelfLoopBool := by
  have hMap :=
    TMPolyTimeMap.list_map edgeSelfLoopBool_tm_polytime
  have hComp := TMPolyTimeMap.comp boolListOr_tm_polytime hMap
  simpa [Function.comp, hasSelfLoopBool, edgeListStructuredEncodedType] using hComp

/-- All unordered non-edges of a graph, represented in increasing orientation. -/
def complementEdges (g : GraphInput) : List (Nat × Nat) :=
  structuredComplementEdges g

theorem mem_complementEdges_iff (g : GraphInput) (e : Nat × Nat) :
    e ∈ complementEdges g ↔
      e.1 < g.vertices ∧ e.2 < g.vertices ∧
        e.1 < e.2 ∧ ¬ HasUndirectedEdge g e.1 e.2 := by
  cases e with
  | mk u v =>
      simp [complementEdges, mem_structuredComplementEdges_iff]

/-- Undirected complement graph used by the textbook Chromatic Number to Clique Cover route. -/
noncomputable def complementGraph (g : GraphInput) : GraphInput where
  vertices := g.vertices
  edges := complementEdges g
  directed := false

theorem hasUndirectedEdge_complementGraph_iff (g : GraphInput) (u v : Nat) :
    HasUndirectedEdge (complementGraph g) u v ↔
      u < g.vertices ∧ v < g.vertices ∧ u ≠ v ∧ ¬ HasUndirectedEdge g u v := by
  constructor
  · intro h
    rcases h with h | h
    · rcases (mem_complementEdges_iff g (u, v)).1 h with ⟨hu, hv, huv, hNonedge⟩
      exact ⟨hu, hv, Nat.ne_of_lt huv, hNonedge⟩
    · rcases (mem_complementEdges_iff g (v, u)).1 h with ⟨hv, hu, hvu, hNonedge⟩
      refine ⟨hu, hv, Nat.ne_of_gt hvu, ?_⟩
      intro hEdge
      exact hNonedge ((hasUndirectedEdge_comm g u v).1 hEdge)
  · rintro ⟨hu, hv, huvNe, hNonedge⟩
    have hCases : u < v ∨ v < u := by omega
    rcases hCases with huv | hvu
    · exact Or.inl (by
        simp [complementGraph, mem_complementEdges_iff, hu, hv, huv, hNonedge])
    · exact Or.inr (by
        have hSymNonedge : ¬ HasUndirectedEdge g v u := by
          intro hEdge
          exact hNonedge ((hasUndirectedEdge_comm g u v).2 hEdge)
        simp [complementGraph, mem_complementEdges_iff, hv, hu, hvu, hSymNonedge])

theorem complementGraph_wellFormed (g : GraphInput) :
    WellFormed (complementGraph g) := by
  intro e he
  have hmem := (mem_complementEdges_iff g e).1 (by simpa [complementGraph] using he)
  exact ⟨hmem.1, hmem.2.1⟩

/-- Vertices of one color form one clique-cover block in the complement graph. -/
def colorBlock (I : ChromaticNumberInput) (colorOf : Nat → Nat) (c : Nat) : List Nat :=
  (List.range I.graph.vertices).filter fun v => decide (colorOf v = c)

/-- The clique-cover family produced from all color classes. -/
def colorBlocks (I : ChromaticNumberInput) (colorOf : Nat → Nat) : List (List Nat) :=
  (List.range I.colors).map (colorBlock I colorOf)

theorem colorBlocks_cliqueCoverFamily {I : ChromaticNumberInput} {colorOf : Nat → Nat}
    (hProper : ProperColoring I.graph I.colors colorOf) :
    CliqueCoverFamily (complementGraph I.graph) (colorBlocks I colorOf) := by
  constructor
  · intro v hv
    let c := colorOf v
    have hvSource : v < I.graph.vertices := by simpa [complementGraph] using hv
    have hc : c ∈ List.range I.colors := List.mem_range.mpr (hProper.1 v hvSource)
    refine ⟨colorBlock I colorOf c, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨c, hc, rfl⟩
    · simp [colorBlock, c, hvSource]
  · intro block hBlock
    rcases List.mem_map.mp hBlock with ⟨c, _hc, rfl⟩
    constructor
    · exact List.Nodup.filter _ (List.nodup_range (n := I.graph.vertices))
    constructor
    · intro v hv
      simp [colorBlock] at hv
      simpa [complementGraph] using hv.1
    · intro u hu v hv huv
      simp [colorBlock] at hu hv
      have hColorEq : colorOf u = colorOf v := by omega
      have hNonedge : ¬ HasUndirectedEdge I.graph u v := by
        intro hEdge
        rcases hEdge with hEdge | hEdge
        · exact hProper.2 (u, v) hEdge hColorEq
        · exact hProper.2 (v, u) hEdge hColorEq.symm
      exact (hasUndirectedEdge_complementGraph_iff I.graph u v).2
        ⟨hu.1, hv.1, huv, hNonedge⟩

/-- P15r textbook map: a coloring instance becomes a clique-cover instance of the complement. -/
noncomputable def textbookMap (I : ChromaticNumberInput) : CliqueCoverInput :=
  by
    classical
    exact
      if HasSelfLoop I.graph then
        noInput
      else
        { graph := complementGraph I.graph
          k := I.colors }

theorem exists_block_index_of_cover {g : GraphInput} {blocks : List (List Nat)} {v : Nat}
    (hFamily : CliqueCoverFamily (complementGraph g) blocks) (hv : v < g.vertices) :
    ∃ i : Fin blocks.length, v ∈ blocks.get i := by
  have hCover : ∃ block ∈ blocks, v ∈ block := hFamily.1 v (by simpa [complementGraph] using hv)
  exact (List.exists_mem_iff_get (l := blocks) (p := fun block => v ∈ block)).mp hCover

noncomputable def chosenCoverIndex (I : ChromaticNumberInput) (blocks : List (List Nat))
    (hFamily : CliqueCoverFamily (complementGraph I.graph) blocks) (v : Nat)
    (hv : v < I.graph.vertices) : Fin blocks.length :=
  Classical.choose (exists_block_index_of_cover (g := I.graph) hFamily hv)

theorem chosenCoverIndex_spec (I : ChromaticNumberInput) (blocks : List (List Nat))
    (hFamily : CliqueCoverFamily (complementGraph I.graph) blocks) (v : Nat)
    (hv : v < I.graph.vertices) :
    v ∈ blocks.get (chosenCoverIndex I blocks hFamily v hv) :=
  Classical.choose_spec (exists_block_index_of_cover (g := I.graph) hFamily hv)

/--
Decoded coloring from a clique-cover certificate.

In-range vertices use a chosen block index.  Out-of-range raw edge endpoints are assigned
fresh colors `I.colors + v`, which is needed because the current `ProperColoring` schema checks
all raw edges but only bounds colors on declared vertices.
-/
noncomputable def coverColor (I : ChromaticNumberInput) (blocks : List (List Nat))
    (hFamily : CliqueCoverFamily (complementGraph I.graph) blocks) (v : Nat) : Nat :=
  if hv : v < I.graph.vertices then
    chosenCoverIndex I blocks hFamily v hv
  else
    I.colors + v

theorem coverColor_eq_chosenCoverIndex (I : ChromaticNumberInput) (blocks : List (List Nat))
    (hFamily : CliqueCoverFamily (complementGraph I.graph) blocks) {v : Nat}
    (hv : v < I.graph.vertices) :
    coverColor I blocks hFamily v = chosenCoverIndex I blocks hFamily v hv := by
  simp [coverColor, hv]

theorem coverColor_lt_colors (I : ChromaticNumberInput) (blocks : List (List Nat))
    (hLen : blocks.length ≤ I.colors)
    (hFamily : CliqueCoverFamily (complementGraph I.graph) blocks) {v : Nat}
    (hv : v < I.graph.vertices) :
    coverColor I blocks hFamily v < I.colors := by
  rw [coverColor_eq_chosenCoverIndex I blocks hFamily hv]
  have hIdx : ((chosenCoverIndex I blocks hFamily v hv : Fin blocks.length) : Nat) <
      blocks.length :=
    (chosenCoverIndex I blocks hFamily v hv).isLt
  omega

theorem coverColor_properColoring (I : ChromaticNumberInput) (blocks : List (List Nat))
    (hNoLoop : ¬ HasSelfLoop I.graph) (hLen : blocks.length ≤ I.colors)
    (hFamily : CliqueCoverFamily (complementGraph I.graph) blocks) :
    ProperColoring I.graph I.colors (coverColor I blocks hFamily) := by
  constructor
  · intro v hv
    exact coverColor_lt_colors I blocks hLen hFamily hv
  · rintro ⟨u, v⟩ he
    by_cases hSame : u = v
    · exfalso
      subst v
      exact hNoLoop ⟨u, he⟩
    by_cases hLeft : u < I.graph.vertices
    · by_cases hRight : v < I.graph.vertices
      · intro hColorEq
        let i := chosenCoverIndex I blocks hFamily u hLeft
        let j := chosenCoverIndex I blocks hFamily v hRight
        have hiColor : coverColor I blocks hFamily u = i :=
          coverColor_eq_chosenCoverIndex I blocks hFamily hLeft
        have hjColor : coverColor I blocks hFamily v = j :=
          coverColor_eq_chosenCoverIndex I blocks hFamily hRight
        have hijNat : (i : Nat) = (j : Nat) := by
          exact hiColor.symm.trans (hColorEq.trans hjColor)
        have hij : i = j := Fin.ext hijNat
        have hiMem : u ∈ blocks.get i :=
          chosenCoverIndex_spec I blocks hFamily u hLeft
        have hjMem : v ∈ blocks.get i := by
          simpa [i, j, hij] using chosenCoverIndex_spec I blocks hFamily v hRight
        have hBlockMem : blocks.get i ∈ blocks := List.get_mem blocks i
        have hAdj :=
          (hFamily.2 (blocks.get i) hBlockMem).2.2 u hiMem v hjMem hSame
        have hComp :=
          (hasUndirectedEdge_complementGraph_iff I.graph u v).1 hAdj
        exact hComp.2.2.2 (Or.inl he)
      · intro hColorEq
        have hLeftLt := coverColor_lt_colors I blocks hLen hFamily hLeft
        have hRightEq : coverColor I blocks hFamily v = I.colors + v := by
          simp [coverColor, hRight]
        rw [hRightEq] at hColorEq
        rw [hColorEq] at hLeftLt
        omega
    · by_cases hRight : v < I.graph.vertices
      · intro hColorEq
        have hRightLt := coverColor_lt_colors I blocks hLen hFamily hRight
        have hLeftEq : coverColor I blocks hFamily u = I.colors + u := by
          simp [coverColor, hLeft]
        rw [hLeftEq] at hColorEq
        rw [← hColorEq] at hRightLt
        omega
      · intro hColorEq
        have hLeftEq : coverColor I blocks hFamily u = I.colors + u := by
          simp [coverColor, hLeft]
        have hRightEq : coverColor I blocks hFamily v = I.colors + v := by
          simp [coverColor, hRight]
        rw [hLeftEq, hRightEq] at hColorEq
        omega

theorem textbookMap_correct (I : ChromaticNumberInput) :
    chromaticNumberDecisionProblem.isYes I ↔ CliqueCover (textbookMap I) := by
  classical
  by_cases hLoop : HasSelfLoop I.graph
  · constructor
    · intro hChromatic
      exact (noChromatic_of_selfLoop hLoop hChromatic).elim
    · intro hCover
      exact (noInput_isNo (by simpa [textbookMap, hLoop] using hCover)).elim
  · constructor
    · rintro ⟨colorOf, hProper⟩
      refine ⟨colorBlocks I colorOf, ?_, ?_⟩
      · simp [colorBlocks, textbookMap, hLoop]
      · simpa [textbookMap, hLoop] using colorBlocks_cliqueCoverFamily hProper
    · rintro ⟨blocks, hLen, hFamilyRaw⟩
      have hFamily : CliqueCoverFamily (complementGraph I.graph) blocks := by
        simpa [textbookMap, hLoop] using hFamilyRaw
      have hLen' : blocks.length ≤ I.colors := by
        simpa [textbookMap, hLoop] using hLen
      exact ⟨coverColor I blocks hFamily, coverColor_properColoring I blocks hLoop hLen' hFamily⟩

/-- Costed Karp reduction from local 3SAT to Clique Cover. -/
noncomputable def threeSATToCliqueCoverTMBackedKarpReduction :
    TMBackedCostedReduction SAT.threeSATDecisionProblem cliqueCoverDecisionProblem := by
  simpa [cliqueCoverDecisionProblem, cliqueCoverEncodedType] using
    rawCodomainTMBackedReduction
      SAT.threeSATDecisionProblem
      Combinatorics.Graph.CliqueCover
      map
      map_correct

/-- Costed Karp reduction from local 3SAT to Clique Cover. -/
noncomputable def threeSATToCliqueCoverKarpReduction :
    KarpReductionM CostedPolyTimeModel SAT.threeSATDecisionProblem
      cliqueCoverDecisionProblem :=
  threeSATToCliqueCoverTMBackedKarpReduction.toCostedKarpReduction

/-- Costed P15r textbook Karp reduction from Chromatic Number to Clique Cover. -/
noncomputable def chromaticNumberToCliqueCover_textbookTMBackedKarpReduction :
    TMBackedCostedReduction chromaticNumberDecisionProblem cliqueCoverDecisionProblem := by
  simpa [cliqueCoverDecisionProblem, cliqueCoverEncodedType] using
    rawCodomainTMBackedReduction
      chromaticNumberDecisionProblem
      Combinatorics.Graph.CliqueCover
      textbookMap
      textbookMap_correct

/-- Costed P15r textbook Karp reduction from Chromatic Number to Clique Cover. -/
noncomputable def chromaticNumberToCliqueCover_textbookKarpReduction :
    KarpReductionM CostedPolyTimeModel chromaticNumberDecisionProblem
      cliqueCoverDecisionProblem :=
  chromaticNumberToCliqueCover_textbookTMBackedKarpReduction.toCostedKarpReduction

/-- Filtering never increases list length. -/
theorem filter_length_le {α : Type} (p : α → Bool) :
    ∀ xs : List α, (xs.filter p).length ≤ xs.length
  | [] => by simp
  | x :: xs => by
      by_cases h : p x
      · simp [h, filter_length_le p xs]
      · exact Nat.le_trans (by simpa [h] using filter_length_le p xs) (Nat.le_succ xs.length)

theorem edgeStructured_inputSize_le_of_mem_complementEdges {g : GraphInput} {e : Nat × Nat}
    (he : e ∈ complementEdges g) :
    edgeStructuredEncodedType.inputSize e ≤ 2 * g.vertices + 1 := by
  have hmem := (mem_complementEdges_iff g e).1 he
  cases e with
  | mk u v =>
      simp [edgeStructuredEncodedType] at hmem ⊢
      omega

/-- The complement edge list has at most `n^2` candidate pairs. -/
theorem complementEdges_length_le (g : GraphInput) :
    (complementEdges g).length ≤ g.vertices * g.vertices := by
  have hOut :=
    complementEdgesFromCandidates_length_le
      (g.edges, strictNatPairCandidates g.vertices)
  have hCandidates :
      (strictNatPairCandidates g.vertices).length ≤ g.vertices * g.vertices := by
    rw [strictNatPairCandidates_replicate]
    exact strictNatPairCandidatesCore_length_le_square g.vertices
  simpa [complementEdges, structuredComplementEdges] using hOut.trans hCandidates

/-- Structured size of the complement edge list is polynomial in the vertex count. -/
theorem complementEdges_structured_inputSize_le (g : GraphInput) :
    edgeListStructuredEncodedType.inputSize (complementEdges g) ≤
      (g.vertices * g.vertices) * (2 * g.vertices + 2) := by
  have hList :=
    Clique.encodedList_inputSize_le_length_mul_bound edgeStructuredEncodedType
      (complementEdges g) (2 * g.vertices + 1)
      (by
        intro e he
        exact edgeStructured_inputSize_le_of_mem_complementEdges he)
  have hLen := complementEdges_length_le g
  exact hList.trans (by
    have hMul := Nat.mul_le_mul_right (2 * g.vertices + 2) hLen
    simpa [edgeListStructuredEncodedType, Nat.add_assoc] using hMul)

/-- Structured size of the complement graph is polynomial in the source vertex count. -/
theorem complementGraph_structured_inputSize_le (g : GraphInput) :
    graphStructuredEncodedType.inputSize (complementGraph g) ≤
      g.vertices + (g.vertices * g.vertices) * (2 * g.vertices + 2) + 4 := by
  have hEdges := complementEdges_structured_inputSize_le g
  rw [Clique.graphStructured_inputSize_eq]
  simp [complementGraph]
  omega

theorem chromaticNumberStructured_inputSize_ge_vertices_succ (I : ChromaticNumberInput) :
    I.graph.vertices + 1 ≤ chromaticNumberStructuredEncodedType.inputSize I := by
  rw [ChromaticNumber.chromaticNumberStructured_inputSize_eq,
    Clique.graphStructured_inputSize_eq]
  omega

theorem chromaticNumberStructured_inputSize_ge_colors (I : ChromaticNumberInput) :
    I.colors ≤ chromaticNumberStructuredEncodedType.inputSize I := by
  rw [ChromaticNumber.chromaticNumberStructured_inputSize_eq]
  omega

theorem cliqueCoverStructured_inputSize_eq (I : CliqueCoverInput) :
    cliqueCoverStructuredEncodedType.inputSize I =
      graphStructuredEncodedType.inputSize I.graph + I.k + 2 := by
  change cliqueCoverTupleStructuredEncodedType.inputSize (I.graph, I.k) =
    graphStructuredEncodedType.inputSize I.graph + I.k + 2
  simp [cliqueCoverTupleStructuredEncodedType]
  omega

/-- Reify the tuple-shaped Clique Cover payload as the project target structure. -/
def cliqueCoverTupleToCliqueCoverInput
    (p : cliqueCoverTupleStructuredEncodedType.Carrier) : CliqueCoverInput where
  graph := p.1
  k := p.2

theorem cliqueCoverTupleToCliqueCoverInput_encode
    (p : cliqueCoverTupleStructuredEncodedType.Carrier) :
    cliqueCoverStructuredEncodedType.encode (cliqueCoverTupleToCliqueCoverInput p) =
      cliqueCoverTupleStructuredEncodedType.encode p := by
  rcases p with ⟨graph, k⟩
  rfl

noncomputable def cliqueCoverTupleToCliqueCoverInputTMBackedMap :
    TMBackedCostedMap
      cliqueCoverTupleStructuredEncodedType
      cliqueCoverStructuredEncodedType
      cliqueCoverTupleToCliqueCoverInput :=
  TMBackedCostedMap.ofEncodingEquiv
    cliqueCoverTupleStructuredEncodedType
    cliqueCoverStructuredEncodedType
    cliqueCoverTupleToCliqueCoverInput
    (Equiv.refl cliqueCoverTupleStructuredEncodedType.Symbol)
    (by
      intro p
      change cliqueCoverStructuredEncodedType.encode (cliqueCoverTupleToCliqueCoverInput p) =
        (cliqueCoverTupleStructuredEncodedType.encode p).map id
      simp [cliqueCoverTupleToCliqueCoverInput_encode])

theorem chromaticNumberToCliqueCoverStructured_tm_polytime :
    TMPolyTimeMap
      chromaticNumberStructuredEncodedType
      cliqueCoverStructuredEncodedType
      textbookMap := by
  let X := chromaticNumberStructuredEncodedType
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType
        (fun I : ChromaticNumberInput => I.graph) := by
    simpa [X] using chromaticNumberGraphTMBackedMap.tm_polytime
  have hVertices :
      TMPolyTimeMap X EncodedType.nat
        (fun I : ChromaticNumberInput => I.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp graphVerticesTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hPayload :
      TMPolyTimeMap X graphPayloadStructuredEncodedType
        (fun I : ChromaticNumberInput => graphPayloadOfGraph I.graph) := by
    have hComp := TMPolyTimeMap.comp graphPayloadTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hSourceEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun I : ChromaticNumberInput => I.graph.edges) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, graphPayloadOfGraph, graphPayloadStructuredEncodedType, X] using hComp
  have hCandidates :
      TMPolyTimeMap X vertexPairListEncodedType
        (fun I : ChromaticNumberInput => strictNatPairCandidates I.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp strictNatPairCandidatesTMBackedMap.tm_polytime hVertices
    simpa [Function.comp, X] using hComp
  have hComplementInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType vertexPairListEncodedType)
        (fun I : ChromaticNumberInput =>
          (I.graph.edges, strictNatPairCandidates I.graph.vertices)) :=
    TMPolyTimeMap.prod_mk hSourceEdges hCandidates
  have hComplementEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun I : ChromaticNumberInput => complementEdges I.graph) := by
    have hComp := TMPolyTimeMap.comp complementEdgesFromCandidates_tm_polytime hComplementInput
    simpa [Function.comp, complementEdges, structuredComplementEdges, X] using hComp
  have hDirected :
      TMPolyTimeMap X EncodedType.bool (fun _ : ChromaticNumberInput => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hGraphPayloadOut :
      TMPolyTimeMap X graphPayloadStructuredEncodedType
        (fun I : ChromaticNumberInput => (complementEdges I.graph, false)) :=
    TMPolyTimeMap.prod_mk hComplementEdges hDirected
  have hGraphTuple :
      TMPolyTimeMap X graphTupleStructuredEncodedType
        (fun I : ChromaticNumberInput => (I.graph.vertices, (complementEdges I.graph, false))) :=
    TMPolyTimeMap.prod_mk hVertices hGraphPayloadOut
  have hComplementGraph :
      TMPolyTimeMap X graphStructuredEncodedType
        (fun I : ChromaticNumberInput => complementGraph I.graph) := by
    have hComp := TMPolyTimeMap.comp Clique.graphTupleToGraphTMBackedMap.tm_polytime hGraphTuple
    simpa [Function.comp, Clique.graphTupleToGraph, complementGraph, X] using hComp
  have hColors :
      TMPolyTimeMap X EncodedType.nat
        (fun I : ChromaticNumberInput => I.colors) := by
    simpa [X] using chromaticNumberColorsTMBackedMap.tm_polytime
  have hTargetTuple :
      TMPolyTimeMap X cliqueCoverTupleStructuredEncodedType
        (fun I : ChromaticNumberInput => (complementGraph I.graph, I.colors)) :=
    TMPolyTimeMap.prod_mk hComplementGraph hColors
  have hFalseBranch :
      TMPolyTimeMap X cliqueCoverStructuredEncodedType
        (fun I : ChromaticNumberInput =>
          { graph := complementGraph I.graph
            k := I.colors }) := by
    have hComp := TMPolyTimeMap.comp cliqueCoverTupleToCliqueCoverInputTMBackedMap.tm_polytime
      hTargetTuple
    simpa [Function.comp, cliqueCoverTupleToCliqueCoverInput, X] using hComp
  have hSelfLoop :
      TMPolyTimeMap X EncodedType.bool
        (fun I : ChromaticNumberInput => hasSelfLoopBool I.graph.edges) := by
    have hComp := TMPolyTimeMap.comp hasSelfLoopBool_tm_polytime hSourceEdges
    simpa [Function.comp, X] using hComp
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun I : ChromaticNumberInput => (hasSelfLoopBool I.graph.edges, I)) :=
    TMPolyTimeMap.prod_mk hSelfLoop (TMPolyTimeMap.id X)
  have hTrueBranch :
      TMPolyTimeMap X cliqueCoverStructuredEncodedType
        (fun _ : ChromaticNumberInput => noInput) :=
    TMPolyTimeMap.const X cliqueCoverStructuredEncodedType noInput
  have hBranch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool X)
        cliqueCoverStructuredEncodedType
        (fun p : Bool × ChromaticNumberInput =>
          match p.1 with
          | true => noInput
          | false =>
              { graph := complementGraph p.2.graph
                k := p.2.colors }) :=
    graphBoolProduct_dispatch_tm_polytime X cliqueCoverStructuredEncodedType
      (fFalse := fun I : ChromaticNumberInput =>
        { graph := complementGraph I.graph
          k := I.colors })
      (fTrue := fun _ : ChromaticNumberInput => noInput)
      hFalseBranch hTrueBranch
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext I
  by_cases hLoop : HasSelfLoop I.graph
  · have hBool : hasSelfLoopBool I.graph.edges = true :=
      (hasSelfLoopBool_graph_eq_true_iff I.graph).2 hLoop
    simp [Function.comp, textbookMap, hLoop, hBool]
  · have hBool : hasSelfLoopBool I.graph.edges = false := by
      cases h : hasSelfLoopBool I.graph.edges
      · rfl
      · exact False.elim (hLoop ((hasSelfLoopBool_graph_eq_true_iff I.graph).1 h))
    simp [Function.comp, textbookMap, hLoop, hBool]

theorem cliqueCoverStructured_inputSize_noInput_le :
    cliqueCoverStructuredEncodedType.inputSize noInput ≤ 20 := by
  have hEmptyEdges :
      edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
    change ((EncodedType.list edgeStructuredEncodedType).encode ([] : List (Nat × Nat))).length = 0
    rfl
  rw [cliqueCoverStructured_inputSize_eq, Clique.graphStructured_inputSize_eq]
  simp [noInput, hEmptyEdges]

theorem cliqueCoverStructured_inputSize_textbookMap_le_chromatic_poly
    (I : ChromaticNumberInput) :
    cliqueCoverStructuredEncodedType.inputSize (textbookMap I) ≤
      1000 * (chromaticNumberStructuredEncodedType.inputSize I) ^ 3 + 1000 := by
  classical
  by_cases hLoop : HasSelfLoop I.graph
  · calc
      cliqueCoverStructuredEncodedType.inputSize (textbookMap I)
          = cliqueCoverStructuredEncodedType.inputSize noInput := by
              simp [textbookMap, hLoop]
      _ ≤ 20 := cliqueCoverStructured_inputSize_noInput_le
      _ ≤ 1000 * (chromaticNumberStructuredEncodedType.inputSize I) ^ 3 + 1000 := by
          omega
  · let S := chromaticNumberStructuredEncodedType.inputSize I
    let V := I.graph.vertices
    have hVsucc : V + 1 ≤ S := by
      simpa [S, V] using chromaticNumberStructured_inputSize_ge_vertices_succ I
    have hV : V ≤ S := by omega
    have hColors : I.colors ≤ S := by
      simpa [S] using chromaticNumberStructured_inputSize_ge_colors I
    have hBase :
        cliqueCoverStructuredEncodedType.inputSize (textbookMap I) ≤
          V + (V * V) * (2 * V + 2) + 4 + I.colors + 2 := by
      calc
        cliqueCoverStructuredEncodedType.inputSize (textbookMap I)
            = graphStructuredEncodedType.inputSize (complementGraph I.graph) +
                I.colors + 2 := by
                  simp [textbookMap, hLoop, cliqueCoverStructured_inputSize_eq]
        _ ≤ V + (V * V) * (2 * V + 2) + 4 + I.colors + 2 := by
              have hGraph :
                  graphStructuredEncodedType.inputSize (complementGraph I.graph) ≤
                    V + (V * V) * (2 * V + 2) + 4 := by
                simpa [V] using complementGraph_structured_inputSize_le I.graph
              omega
    have hVV : V * V ≤ S * S := Nat.mul_le_mul hV hV
    have hTerm : (V * V) * (2 * V + 2) ≤ (S * S) * (2 * S + 2) :=
      Nat.mul_le_mul hVV (by omega)
    have hPolyBase :
        V + (V * V) * (2 * V + 2) + 4 + I.colors + 2 ≤
          S + (S * S) * (2 * S + 2) + 4 + S + 2 := by
      omega
    calc
      cliqueCoverStructuredEncodedType.inputSize (textbookMap I)
          ≤ V + (V * V) * (2 * V + 2) + 4 + I.colors + 2 := hBase
      _ ≤ S + (S * S) * (2 * S + 2) + 4 + S + 2 := hPolyBase
      _ ≤ 1000 * S ^ 3 + 1000 := by
            cases S with
            | zero =>
                norm_num
            | succ S =>
                ring_nf
                omega

theorem chromaticNumberToCliqueCoverStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : ChromaticNumberInput => chromaticNumberStructuredEncodedType.inputSize I)
      (fun J : CliqueCoverInput => cliqueCoverStructuredEncodedType.inputSize J)
      textbookMap := by
  refine PolynomialSizeBound.intro_with 3 1000 1000 ?_
  intro I
  exact cliqueCoverStructured_inputSize_textbookMap_le_chromatic_poly I

noncomputable def chromaticNumberToCliqueCoverStructuredTMBackedMap :
    TMBackedCostedMap
      chromaticNumberStructuredEncodedType
      cliqueCoverStructuredEncodedType
      textbookMap where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      chromaticNumberToCliqueCoverStructured_polynomialSizeBound
  tm_polytime := chromaticNumberToCliqueCoverStructured_tm_polytime

noncomputable def chromaticNumberToCliqueCoverStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      chromaticNumberStructuredDecisionProblem
      cliqueCoverStructuredDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    chromaticNumberToCliqueCoverStructuredTMBackedMap
    (by
      intro I
      simpa [chromaticNumberStructuredDecisionProblem, cliqueCoverStructuredDecisionProblem]
        using textbookMap_correct I)

noncomputable def chromaticNumberToCliqueCoverStructuredTMKarpReduction :
    TMKarpReduction chromaticNumberStructuredDecisionProblem cliqueCoverStructuredDecisionProblem :=
  chromaticNumberToCliqueCoverStructuredTMBackedKarpReduction.toTMKarpReduction

noncomputable def chromaticNumberToCliqueCoverStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      chromaticNumberStructuredDecisionProblem cliqueCoverStructuredDecisionProblem :=
  chromaticNumberToCliqueCoverStructuredTMBackedKarpReduction.toCostedKarpReduction

theorem cliqueCoverStructuredEncoding_faithful :
    cliqueCoverStructuredDecisionProblem.FaithfulEncoding where
  injective := cliqueCoverStructuredEncodedType_encode_injective

theorem cliqueCoverStructuredEncoding_predicateRespects :
    cliqueCoverStructuredDecisionProblem.PredicateRespectsEncoding :=
  cliqueCoverStructuredEncoding_faithful.predicateRespects

theorem cliqueCoverStructuredEncoding_accepts_encode_iff (I : CliqueCoverInput) :
    cliqueCoverStructuredDecisionProblem.toEncodedLanguage.accepts
        (cliqueCoverStructuredEncodedType.encode I) ↔
      CliqueCover I :=
  cliqueCoverStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

/-- Clique Cover is locally in NP for the project-local costed model. -/
theorem cliqueCoverInNP :
    InNPEnc CostedPolyTimeModel cliqueCoverDecisionProblem :=
  decidableInNP cliqueCoverDecisionProblem

/-- Local NP-completeness of Clique Cover via local 3SAT. -/
theorem cliqueCoverNPComplete :
    NPCompleteEnc CostedPolyTimeModel cliqueCoverDecisionProblem :=
  Targets.npComplete_of_localThreeSAT_karp
    cliqueCoverDecisionProblem
    threeSATToCliqueCoverKarpReduction
    cliqueCoverInNP

/-- Local NP-completeness of Clique Cover via the P15r textbook complement route. -/
theorem cliqueCover_textbookNPComplete :
    NPCompleteEnc CostedPolyTimeModel cliqueCoverDecisionProblem :=
  NPCompleteEnc.transfer
    ChromaticNumber.chromaticNumber_textbookNPComplete
    ⟨chromaticNumberToCliqueCover_textbookKarpReduction⟩
    cliqueCoverInNP

end CliqueCover
end Karp21
end ComplexityReduction
