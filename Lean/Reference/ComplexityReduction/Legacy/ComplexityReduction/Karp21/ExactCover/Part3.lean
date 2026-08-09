import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover.Part2

namespace ComplexityReduction
namespace Karp21
namespace ExactCover
open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph
open ComplexityReduction.Karp21.FiniteWitness

def normalizedColor (I : ChromaticNumberInput) (colorOf : Nat → Nat) (v : Nat) : Nat :=
  if v < I.graph.vertices then colorOf v else I.colors + v

theorem normalizedColor_eq_of_lt
    (I : ChromaticNumberInput) (colorOf : Nat → Nat) {v : Nat}
    (hv : v < I.graph.vertices) :
    normalizedColor I colorOf v = colorOf v := by
  simp [normalizedColor, hv]

theorem normalizedColor_eq_of_not_lt
    (I : ChromaticNumberInput) (colorOf : Nat → Nat) {v : Nat}
    (hv : ¬ v < I.graph.vertices) :
    normalizedColor I colorOf v = I.colors + v := by
  simp [normalizedColor, hv]

theorem mem_colorSelectedFillerBlocks_iff
    (I : ChromaticNumberInput) (colorOf : Nat → Nat) (B : List Nat) :
    B ∈ colorSelectedFillerBlocks I colorOf ↔
      ∃ i, i < I.graph.edges.length ∧
        ∃ c, c < I.colors ∧ c ≠ colorOf (colorEdgeAt I i).1 ∧
          c ≠ colorOf (colorEdgeAt I i).2 ∧ B = colorFillerBlock I i c := by
  constructor
  · intro hB
    rcases List.mem_flatMap.mp hB with ⟨i, hi, hBlock⟩
    rcases (mem_colorSelectedFillerBlocksForEdge_iff I colorOf i B).1 hBlock with
      ⟨c, hc, hcLeft, hcRight, rfl⟩
    exact ⟨i, by simpa using hi, c, hc, hcLeft, hcRight, rfl⟩
  · rintro ⟨i, hi, c, hc, hcLeft, hcRight, rfl⟩
    exact List.mem_flatMap.mpr
      ⟨i, by simpa using hi,
        (mem_colorSelectedFillerBlocksForEdge_iff I colorOf i
          (colorFillerBlock I i c)).2 ⟨c, hc, hcLeft, hcRight, rfl⟩⟩

theorem mem_colorSelectedBlocksRaw_iff
    (I : ChromaticNumberInput) (colorOf : Nat → Nat) (B : List Nat) :
    B ∈ colorSelectedBlocksRaw I colorOf ↔
      (∃ v, v < I.graph.vertices ∧ B = colorChoiceBlock I v (colorOf v)) ∨
        ∃ i, i < I.graph.edges.length ∧
          ∃ c, c < I.colors ∧ c ≠ colorOf (colorEdgeAt I i).1 ∧
            c ≠ colorOf (colorEdgeAt I i).2 ∧ B = colorFillerBlock I i c := by
  constructor
  · intro hB
    rcases List.mem_append.mp hB with hChoice | hFiller
    · exact Or.inl ((mem_colorSelectedChoiceBlocks_iff I colorOf B).1 hChoice)
    · exact Or.inr ((mem_colorSelectedFillerBlocks_iff I colorOf B).1 hFiller)
  · intro hB
    rcases hB with hChoice | hFiller
    · exact List.mem_append.mpr
        (Or.inl ((mem_colorSelectedChoiceBlocks_iff I colorOf B).2 hChoice))
    · exact List.mem_append.mpr
        (Or.inr ((mem_colorSelectedFillerBlocks_iff I colorOf B).2 hFiller))

theorem mem_colorSelectedBlocks_iff
    (I : ChromaticNumberInput) (colorOf : Nat → Nat) (B : List Nat) :
    B ∈ colorSelectedBlocks I colorOf ↔ B ∈ colorSelectedBlocksRaw I colorOf := by
  simp [colorSelectedBlocks]

theorem colorSelectedBlocks_family_of_proper {I : ChromaticNumberInput}
    {colorOf : Nat → Nat} (hProper : ProperColoring I.graph I.colors colorOf) :
    ∀ B ∈ colorSelectedBlocks I colorOf, IsSetInFamily (colorExactCoverSetSystem I) B := by
  intro B hB
  have hRaw := (mem_colorSelectedBlocks_iff I colorOf B).1 hB
  rcases (mem_colorSelectedBlocksRaw_iff I colorOf B).1 hRaw with hChoice | hFiller
  · rcases hChoice with ⟨v, hv, rfl⟩
    exact List.mem_append.mpr
      (Or.inl ((mem_colorChoiceBlocks_iff I (colorChoiceBlock I v (colorOf v))).2
        ⟨v, hv, colorOf v, hProper.1 v hv, rfl⟩))
  · rcases hFiller with ⟨i, hi, c, hc, _hcLeft, _hcRight, rfl⟩
    exact List.mem_append.mpr
      (Or.inr ((mem_colorFillerBlocks_iff I (colorFillerBlock I i c)).2
        ⟨i, hi, c, hc, rfl⟩))

theorem colorSelectedBlocks_nodup (I : ChromaticNumberInput) (colorOf : Nat → Nat) :
    (colorSelectedBlocks I colorOf).Nodup := by
  exact List.nodup_dedup (colorSelectedBlocksRaw I colorOf)

theorem colorSelectedChoiceChoice_eq_of_inter {I : ChromaticNumberInput}
    {colorOf : Nat → Nat} (hProper : ProperColoring I.graph I.colors colorOf)
    {v w x : Nat} (hv : v < I.graph.vertices) (hw : w < I.graph.vertices)
    (hxA : x ∈ colorChoiceBlock I v (colorOf v))
    (hxB : x ∈ colorChoiceBlock I w (colorOf w)) :
    colorChoiceBlock I v (colorOf v) = colorChoiceBlock I w (colorOf w) := by
  rcases (mem_colorChoiceBlock_iff I v (colorOf v) x).1 hxA with hxVertexA | hxEdgeA
  · rcases (mem_colorChoiceBlock_iff I w (colorOf w) x).1 hxB with hxVertexB | hxEdgeB
    · have hvw : v = w := by
        simpa [colorVertexCode] using hxVertexA.symm.trans hxVertexB
      subst w
      rfl
    · rcases hxEdgeB with ⟨j, hj, _hIncident, hxCode⟩
      have hEq : colorVertexCode I v = colorEdgeCode I j (colorOf w) := by
        rw [← hxVertexA, hxCode]
      exact (colorVertexCode_ne_colorEdgeCode (I := I) (v := v) (i := j)
        (c := colorOf w) hv hEq).elim
  · rcases hxEdgeA with ⟨i, hi, hIncidentV, hxCodeA⟩
    rcases (mem_colorChoiceBlock_iff I w (colorOf w) x).1 hxB with hxVertexB | hxEdgeB
    · have hEq : colorVertexCode I w = colorEdgeCode I i (colorOf v) := by
        rw [← hxVertexB, hxCodeA]
      exact (colorVertexCode_ne_colorEdgeCode (I := I) (v := w) (i := i)
        (c := colorOf v) hw hEq).elim
    · rcases hxEdgeB with ⟨j, hj, hIncidentW, hxCodeB⟩
      have hCode :
          colorEdgeCode I i (colorOf v) = colorEdgeCode I j (colorOf w) := by
        rw [← hxCodeA, hxCodeB]
      rcases colorEdgeCode_inj hi (hProper.1 v hv) hj (hProper.1 w hw) hCode with
        ⟨hij, hColor⟩
      subst j
      by_cases hvw : v = w
      · subst w
        rfl
      · have hEdgeMem : colorEdgeAt I i ∈ I.graph.edges := by
          rw [colorEdgeAt_eq_getElem (I := I) hi]
          exact List.getElem_mem hi
        have hDiff := hProper.2 (colorEdgeAt I i) hEdgeMem
        rcases hIncidentV with hVLeft | hVRight <;>
          rcases hIncidentW with hWLeft | hWRight
        · exact (hvw (by simpa [hVLeft] using hWLeft)).elim
        · have hSame :
              colorOf (colorEdgeAt I i).1 = colorOf (colorEdgeAt I i).2 := by
            simpa [hVLeft, hWRight] using hColor
          exact (hDiff hSame).elim
        · have hSame :
              colorOf (colorEdgeAt I i).1 = colorOf (colorEdgeAt I i).2 := by
            simpa [hWLeft, hVRight] using hColor.symm
          exact (hDiff hSame).elim
        · exact (hvw (by simpa [hVRight] using hWRight)).elim

theorem colorSelectedChoiceFiller_disjoint {I : ChromaticNumberInput}
    {colorOf : Nat → Nat} (hProper : ProperColoring I.graph I.colors colorOf)
    {v i c x : Nat} (hv : v < I.graph.vertices) (hi : i < I.graph.edges.length)
    (hc : c < I.colors)
    (hcLeft : c ≠ colorOf (colorEdgeAt I i).1)
    (hcRight : c ≠ colorOf (colorEdgeAt I i).2)
    (hxChoice : x ∈ colorChoiceBlock I v (colorOf v))
    (hxFiller : x ∈ colorFillerBlock I i c) : False := by
  have hxFillerCode := (mem_colorFillerBlock_iff I i c x).1 hxFiller
  rcases (mem_colorChoiceBlock_iff I v (colorOf v) x).1 hxChoice with
    hxVertex | hxEdge
  · have hEq : colorVertexCode I v = colorEdgeCode I i c := by
      rw [← hxVertex, hxFillerCode]
    exact colorVertexCode_ne_colorEdgeCode (I := I) (v := v) (i := i) (c := c) hv hEq
  · rcases hxEdge with ⟨j, hj, hIncident, hxChoiceCode⟩
    have hCode : colorEdgeCode I j (colorOf v) = colorEdgeCode I i c := by
      rw [← hxChoiceCode, hxFillerCode]
    rcases colorEdgeCode_inj hj (hProper.1 v hv) hi hc hCode with ⟨hji, hColor⟩
    subst j
    rcases hIncident with hLeft | hRight
    · have hContr : c = colorOf (colorEdgeAt I i).1 := by
        rw [hLeft]
        exact hColor.symm
      exact hcLeft hContr
    · have hContr : c = colorOf (colorEdgeAt I i).2 := by
        rw [hRight]
        exact hColor.symm
      exact hcRight hContr

theorem colorSelectedBlocks_unique_of_inter {I : ChromaticNumberInput}
    {colorOf : Nat → Nat} (hProper : ProperColoring I.graph I.colors colorOf)
    {A B : List Nat} {x : Nat}
    (hA : A ∈ colorSelectedBlocks I colorOf) (hB : B ∈ colorSelectedBlocks I colorOf)
    (hxA : x ∈ A) (hxB : x ∈ B) :
    A = B := by
  have hARaw := (mem_colorSelectedBlocks_iff I colorOf A).1 hA
  have hBRaw := (mem_colorSelectedBlocks_iff I colorOf B).1 hB
  rcases (mem_colorSelectedBlocksRaw_iff I colorOf A).1 hARaw with hAChoice | hAFiller
  · rcases hAChoice with ⟨v, hv, rfl⟩
    rcases (mem_colorSelectedBlocksRaw_iff I colorOf B).1 hBRaw with hBChoice | hBFiller
    · rcases hBChoice with ⟨w, hw, rfl⟩
      exact colorSelectedChoiceChoice_eq_of_inter hProper hv hw hxA hxB
    · rcases hBFiller with ⟨i, hi, c, hc, hcLeft, hcRight, rfl⟩
      exact (colorSelectedChoiceFiller_disjoint hProper hv hi hc hcLeft hcRight hxA hxB).elim
  · rcases hAFiller with ⟨i, hi, c, hc, hcLeft, hcRight, rfl⟩
    rcases (mem_colorSelectedBlocksRaw_iff I colorOf B).1 hBRaw with hBChoice | hBFiller
    · rcases hBChoice with ⟨v, hv, rfl⟩
      exact (colorSelectedChoiceFiller_disjoint hProper hv hi hc hcLeft hcRight hxB hxA).elim
    · rcases hBFiller with ⟨j, hj, d, hd, _hdLeft, _hdRight, rfl⟩
      have hxCodeA := (mem_colorFillerBlock_iff I i c x).1 hxA
      have hxCodeB := (mem_colorFillerBlock_iff I j d x).1 hxB
      have hCode : colorEdgeCode I i c = colorEdgeCode I j d := by
        rw [← hxCodeA, hxCodeB]
      rcases colorEdgeCode_inj hi hc hj hd hCode with ⟨rfl, rfl⟩
      rfl

theorem colorSelectedBlocks_pairwiseDisjoint {I : ChromaticNumberInput}
    {colorOf : Nat → Nat} (hProper : ProperColoring I.graph I.colors colorOf) :
    PairwiseDisjointFamily (colorSelectedBlocks I colorOf) := by
  intro A hA B hB hAB x hxA hxB
  exact hAB (colorSelectedBlocks_unique_of_inter hProper hA hB hxA hxB)

theorem colorEdgeAt_mem_edges {I : ChromaticNumberInput} {i : Nat}
    (hi : i < I.graph.edges.length) :
    colorEdgeAt I i ∈ I.graph.edges := by
  rw [colorEdgeAt_eq_getElem (I := I) hi]
  exact List.getElem_mem hi

theorem colorSelectedBlocks_coversUniverse {I : ChromaticNumberInput}
    (colorOf : Nat → Nat) :
    CoversUniverse (colorExactCoverSetSystem I)
      (colorSelectedBlocks I (normalizedColor I colorOf)) := by
  intro x hx
  by_cases hxVertex : x < I.graph.vertices
  · refine ⟨colorChoiceBlock I x (normalizedColor I colorOf x), ?_, ?_⟩
    · exact (mem_colorSelectedBlocks_iff I (normalizedColor I colorOf)
        (colorChoiceBlock I x (normalizedColor I colorOf x))).2
        ((mem_colorSelectedBlocksRaw_iff I (normalizedColor I colorOf)
          (colorChoiceBlock I x (normalizedColor I colorOf x))).2
          (Or.inl ⟨x, hxVertex, rfl⟩))
    · exact colorVertex_mem_colorChoiceBlock I x (normalizedColor I colorOf x)
  · have hxAfterVertices : I.graph.vertices ≤ x := Nat.le_of_not_gt hxVertex
    let idx := x - I.graph.vertices
    have hidx : idx < (colorEdgeColorPairs I).length := by
      simp [colorExactCoverSetSystem, colorUniverseSize] at hx
      omega
    let p : Nat × Nat := (colorEdgeColorPairs I)[idx]
    have hpMem : p ∈ colorEdgeColorPairs I := List.getElem_mem hidx
    rcases hp : p with ⟨i, c⟩
    have hPairBounds : i < I.graph.edges.length ∧ c < I.colors := by
      simpa [hp] using (mem_colorEdgeColorPairs_iff I p).1 hpMem
    rcases hPairBounds with ⟨hi, hc⟩
    have hIdxOf : (colorEdgeColorPairs I).idxOf (i, c) = idx := by
      simpa [p, hp] using (colorEdgeColorPairs_nodup I).idxOf_getElem idx hidx
    have hxCode : x = colorEdgeCode I i c := by
      have hxAdd : x = I.graph.vertices + idx := by
        omega
      rw [hxAdd, colorEdgeCode, hIdxOf]
    by_cases hcLeft : c = normalizedColor I colorOf (colorEdgeAt I i).1
    · refine ⟨colorChoiceBlock I (colorEdgeAt I i).1
          (normalizedColor I colorOf (colorEdgeAt I i).1), ?_, ?_⟩
      · have hLeftBounds : (colorEdgeAt I i).1 < I.graph.vertices := by
          by_contra hLeftBounds
          have hNorm :=
            normalizedColor_eq_of_not_lt I colorOf (v := (colorEdgeAt I i).1) hLeftBounds
          omega
        exact (mem_colorSelectedBlocks_iff I (normalizedColor I colorOf)
          (colorChoiceBlock I (colorEdgeAt I i).1
            (normalizedColor I colorOf (colorEdgeAt I i).1))).2
          ((mem_colorSelectedBlocksRaw_iff I (normalizedColor I colorOf)
            (colorChoiceBlock I (colorEdgeAt I i).1
              (normalizedColor I colorOf (colorEdgeAt I i).1))).2
            (Or.inl ⟨(colorEdgeAt I i).1, hLeftBounds, rfl⟩))
      · rw [hxCode, hcLeft]
        exact colorEdgeCode_mem_colorChoiceBlock (I := I) (i := i)
          (v := (colorEdgeAt I i).1)
          (c := normalizedColor I colorOf (colorEdgeAt I i).1)
          hi (Or.inl rfl)
    · by_cases hcRight : c = normalizedColor I colorOf (colorEdgeAt I i).2
      · refine ⟨colorChoiceBlock I (colorEdgeAt I i).2
            (normalizedColor I colorOf (colorEdgeAt I i).2), ?_, ?_⟩
        · have hRightBounds : (colorEdgeAt I i).2 < I.graph.vertices := by
            by_contra hRightBounds
            have hNorm :=
              normalizedColor_eq_of_not_lt I colorOf (v := (colorEdgeAt I i).2) hRightBounds
            omega
          exact (mem_colorSelectedBlocks_iff I (normalizedColor I colorOf)
            (colorChoiceBlock I (colorEdgeAt I i).2
              (normalizedColor I colorOf (colorEdgeAt I i).2))).2
            ((mem_colorSelectedBlocksRaw_iff I (normalizedColor I colorOf)
              (colorChoiceBlock I (colorEdgeAt I i).2
                (normalizedColor I colorOf (colorEdgeAt I i).2))).2
              (Or.inl ⟨(colorEdgeAt I i).2, hRightBounds, rfl⟩))
        · rw [hxCode, hcRight]
          exact colorEdgeCode_mem_colorChoiceBlock (I := I) (i := i)
            (v := (colorEdgeAt I i).2)
            (c := normalizedColor I colorOf (colorEdgeAt I i).2)
            hi (Or.inr rfl)
      · refine ⟨colorFillerBlock I i c, ?_, ?_⟩
        · exact (mem_colorSelectedBlocks_iff I (normalizedColor I colorOf)
              (colorFillerBlock I i c)).2
            ((mem_colorSelectedBlocksRaw_iff I (normalizedColor I colorOf)
                (colorFillerBlock I i c)).2
              (Or.inr ⟨i, hi, c, hc, hcLeft, hcRight, rfl⟩))
        · rw [hxCode]
          simp [colorFillerBlock]

theorem normalizedColor_proper_of_chromaticNumber {I : ChromaticNumberInput}
    {colorOf : Nat → Nat} (hNoLoop : ¬ colorGraphHasSelfLoop I)
    (hProper : ProperColoring I.graph I.colors colorOf) :
    ProperColoring I.graph I.colors (normalizedColor I colorOf) := by
  constructor
  · intro v hv
    simpa [normalizedColor, hv] using hProper.1 v hv
  · intro e he hSame
    by_cases hLeft : e.1 < I.graph.vertices
    · by_cases hRight : e.2 < I.graph.vertices
      · have hSameOriginal : colorOf e.1 = colorOf e.2 := by
          simpa [normalizedColor, hLeft, hRight] using hSame
        exact hProper.2 e he hSameOriginal
      · have hLeftColor := hProper.1 e.1 hLeft
        have hSameOut : colorOf e.1 = I.colors + e.2 := by
          simpa [normalizedColor, hLeft, hRight] using hSame
        omega
    · by_cases hRight : e.2 < I.graph.vertices
      · have hRightColor := hProper.1 e.2 hRight
        have hSameOut : I.colors + e.1 = colorOf e.2 := by
          simpa [normalizedColor, hLeft, hRight] using hSame
        omega
      · have hSameOut : I.colors + e.1 = I.colors + e.2 := by
          simpa [normalizedColor, hLeft, hRight] using hSame
        have hLoop : e.1 = e.2 := by omega
        exact hNoLoop ⟨e, he, hLoop⟩

theorem colorExactCoverCore_of_chromaticNumber {I : ChromaticNumberInput}
    (hNoLoop : ¬ colorGraphHasSelfLoop I) (hColorable : ChromaticNumber I) :
    ExactCover (colorExactCoverCore I) := by
  rcases hColorable with ⟨colorOf, hProper⟩
  let colorOf' := normalizedColor I colorOf
  have hProper' : ProperColoring I.graph I.colors colorOf' := by
    simpa [colorOf'] using normalizedColor_proper_of_chromaticNumber hNoLoop hProper
  refine ⟨colorExactCoverSetSystem_wellFormed I, colorSelectedBlocks I colorOf', ?_, ?_, ?_, ?_⟩
  · exact colorSelectedBlocks_family_of_proper hProper'
  · exact colorSelectedBlocks_nodup I colorOf'
  · exact colorSelectedBlocks_pairwiseDisjoint hProper'
  · simpa [colorOf'] using colorSelectedBlocks_coversUniverse (I := I) colorOf

theorem not_chromaticNumber_of_colorGraphHasSelfLoop {I : ChromaticNumberInput}
    (hLoop : colorGraphHasSelfLoop I) :
    ¬ ChromaticNumber I := by
  rintro ⟨colorOf, hProper⟩
  rcases hLoop with ⟨e, he, hEq⟩
  exact hProper.2 e he (by simp [hEq])

theorem exists_selected_colorChoiceBlock_of_covers {I : ChromaticNumberInput}
    {selected : List (List Nat)}
    (hFamily : ∀ B ∈ selected, IsSetInFamily (colorExactCoverSetSystem I) B)
    (hCovers : CoversUniverse (colorExactCoverSetSystem I) selected)
    {v : Nat} (hv : v < I.graph.vertices) :
    ∃ c, c < I.colors ∧ colorChoiceBlock I v c ∈ selected := by
  have hCover := hCovers (colorVertexCode I v) (by
    simpa [colorExactCoverSetSystem] using colorVertexCode_lt_universe (I := I) hv)
  rcases hCover with ⟨B, hBSelected, hVertexMem⟩
  have hBFamily := hFamily B hBSelected
  rcases List.mem_append.mp hBFamily with hChoice | hFiller
  · rcases (mem_colorChoiceBlocks_iff I B).1 hChoice with ⟨u, _hu, c, hc, rfl⟩
    rcases (mem_colorChoiceBlock_iff I u c (colorVertexCode I v)).1 hVertexMem with
      hVertex | hEdge
    · have hvu : v = u := by
        simpa [colorVertexCode] using hVertex
      subst u
      exact ⟨c, hc, hBSelected⟩
    · rcases hEdge with ⟨i, _hi, _hIncident, hEq⟩
      exact (colorVertexCode_ne_colorEdgeCode (I := I) (v := v) (i := i) (c := c)
        hv hEq).elim
  · rcases (mem_colorFillerBlocks_iff I B).1 hFiller with ⟨i, _hi, c, _hc, rfl⟩
    have hEq := (mem_colorFillerBlock_iff I i c (colorVertexCode I v)).1 hVertexMem
    exact (colorVertexCode_ne_colorEdgeCode (I := I) (v := v) (i := i) (c := c)
      hv hEq).elim

theorem chromaticNumber_of_colorExactCoverCore {I : ChromaticNumberInput}
    (hNoLoop : ¬ colorGraphHasSelfLoop I)
    (hExact : ExactCover (colorExactCoverCore I)) :
    ChromaticNumber I := by
  classical
  rcases hExact with ⟨_hSystemWellFormed, selected, hFamily, _hNodup, hDisjoint, hCovers⟩
  have hExists :
      ∀ v, v < I.graph.vertices →
        ∃ c, c < I.colors ∧ colorChoiceBlock I v c ∈ selected := by
    intro v hv
    exact exists_selected_colorChoiceBlock_of_covers
      (I := I) (selected := selected) hFamily hCovers hv
  let colorOf : Nat → Nat := fun v =>
    if hv : v < I.graph.vertices then Classical.choose (hExists v hv) else I.colors + v
  refine ⟨colorOf, ?_, ?_⟩
  · intro v hv
    have hSpec := Classical.choose_spec (hExists v hv)
    simpa [colorOf, hv] using hSpec.1
  · intro e he hSame
    by_cases hLeft : e.1 < I.graph.vertices
    · by_cases hRight : e.2 < I.graph.vertices
      · let i := I.graph.edges.idxOf e
        have hi : i < I.graph.edges.length := List.idxOf_lt_length_iff.mpr he
        have hAt : colorEdgeAt I i = e := by
          rw [colorEdgeAt_eq_getElem (I := I) hi]
          exact List.idxOf_get (l := I.graph.edges) (a := e) hi
        have hSpecLeft := Classical.choose_spec (hExists e.1 hLeft)
        have hSpecRight := Classical.choose_spec (hExists e.2 hRight)
        have hColorLeft :
            colorOf e.1 = Classical.choose (hExists e.1 hLeft) := by
          simp [colorOf, hLeft]
        have hColorRight :
            colorOf e.2 = Classical.choose (hExists e.2 hRight) := by
          simp [colorOf, hRight]
        have hLeftSelected :
            colorChoiceBlock I e.1 (colorOf e.1) ∈ selected := by
          simpa [hColorLeft] using hSpecLeft.2
        have hRightSelected :
            colorChoiceBlock I e.2 (colorOf e.2) ∈ selected := by
          simpa [hColorRight] using hSpecRight.2
        have hBlocksNe :
            colorChoiceBlock I e.1 (colorOf e.1) ≠
              colorChoiceBlock I e.2 (colorOf e.2) := by
          intro hBlock
          have hHead : e.1 = e.2 := by
            injection hBlock
          exact hNoLoop ⟨e, he, hHead⟩
        have hxLeft :
            colorEdgeCode I i (colorOf e.1) ∈
              colorChoiceBlock I e.1 (colorOf e.1) := by
          exact colorEdgeCode_mem_colorChoiceBlock (I := I) (i := i) (v := e.1)
            (c := colorOf e.1) hi (by
              unfold colorEdgeIncident
              rw [hAt]
              exact Or.inl rfl)
        have hxRight :
            colorEdgeCode I i (colorOf e.1) ∈
              colorChoiceBlock I e.2 (colorOf e.2) := by
          rw [hSame]
          exact colorEdgeCode_mem_colorChoiceBlock (I := I) (i := i) (v := e.2)
            (c := colorOf e.2) hi (by
              unfold colorEdgeIncident
              rw [hAt]
              exact Or.inr rfl)
        exact hDisjoint
          (colorChoiceBlock I e.1 (colorOf e.1)) hLeftSelected
          (colorChoiceBlock I e.2 (colorOf e.2)) hRightSelected
          hBlocksNe (colorEdgeCode I i (colorOf e.1)) hxLeft hxRight
      · have hLeftColor := Classical.choose_spec (hExists e.1 hLeft) |>.1
        have hColorLeft :
            colorOf e.1 = Classical.choose (hExists e.1 hLeft) := by
          simp [colorOf, hLeft]
        have hColorRight : colorOf e.2 = I.colors + e.2 := by
          simp [colorOf, hRight]
        omega
    · by_cases hRight : e.2 < I.graph.vertices
      · have hRightColor := Classical.choose_spec (hExists e.2 hRight) |>.1
        have hColorLeft : colorOf e.1 = I.colors + e.1 := by
          simp [colorOf, hLeft]
        have hColorRight :
            colorOf e.2 = Classical.choose (hExists e.2 hRight) := by
          simp [colorOf, hRight]
        omega
      · have hColorLeft : colorOf e.1 = I.colors + e.1 := by
          simp [colorOf, hLeft]
        have hColorRight : colorOf e.2 = I.colors + e.2 := by
          simp [colorOf, hRight]
        have hLoop : e.1 = e.2 := by omega
        exact hNoLoop ⟨e, he, hLoop⟩

theorem colorExactCoverCore_correct (I : ChromaticNumberInput)
    (hNoLoop : ¬ colorGraphHasSelfLoop I) :
    ChromaticNumber I ↔ ExactCover (colorExactCoverCore I) := by
  constructor
  · exact colorExactCoverCore_of_chromaticNumber hNoLoop
  · exact chromaticNumber_of_colorExactCoverCore hNoLoop

theorem chromaticNumberToExactCoverMap_correct (I : ChromaticNumberInput) :
    chromaticNumberDecisionProblem.isYes I ↔ ExactCover (chromaticNumberToExactCoverMap I) := by
  change ChromaticNumber I ↔ ExactCover (chromaticNumberToExactCoverMap I)
  cases hLoopBool : colorGraphHasSelfLoopBool I
  · have hNoLoop : ¬ colorGraphHasSelfLoop I := by
      intro hLoop
      have hBool := (colorGraphHasSelfLoopBool_eq_true_iff I).2 hLoop
      simp [hLoopBool] at hBool
    simpa [chromaticNumberToExactCoverMap, hLoopBool] using
      colorExactCoverCore_correct I hNoLoop
  · have hLoop : colorGraphHasSelfLoop I :=
      (colorGraphHasSelfLoopBool_eq_true_iff I).1 hLoopBool
    have hNotColor := not_chromaticNumber_of_colorGraphHasSelfLoop hLoop
    constructor
    · intro hColor
      exact (hNotColor hColor).elim
    · intro hExact
      exact (noInput_isNo (by
        simpa [chromaticNumberToExactCoverMap, hLoopBool] using hExact)).elim

theorem encodedList_length_le_inputSize (X : EncodedType) :
    ∀ xs : List X.Carrier, xs.length ≤ (EncodedType.list X).inputSize xs
  | [] => by simp
  | _x :: xs => by
      have ih := encodedList_length_le_inputSize X xs
      calc
        (_x :: xs).length = xs.length + 1 := by simp
        _ ≤ (EncodedType.list X).inputSize xs + 1 := Nat.add_le_add_right ih 1
        _ ≤ X.inputSize _x + 1 + (EncodedType.list X).inputSize xs := by omega
        _ = (EncodedType.list X).inputSize (_x :: xs) := by
            rw [EncodedType.inputSize_list_cons]

theorem colorIncidentEdgeIndices_length_le (I : ChromaticNumberInput) (v : Nat) :
    (colorIncidentEdgeIndices I v).length ≤ I.graph.edges.length := by
  rw [colorIncidentEdgeIndices]
  rw [← SetCovering.incidentEdgeIndicesFromEdges_eq_incidentEdgeIndices
    ({ graph := I.graph, k := 0 } : VertexCoverInput) v]
  exact
    SetCovering.incidentEdgeIndicesFromEdges_length_le (I.graph.edges, v)

theorem colorChoiceBlock_length_le_edges_succ (I : ChromaticNumberInput) (v c : Nat) :
    (colorChoiceBlock I v c).length ≤ I.graph.edges.length + 1 := by
  simp [colorChoiceBlock]
  have hLen := colorIncidentEdgeIndices_length_le I v
  omega

theorem colorChoiceBlocks_length (I : ChromaticNumberInput) :
    (colorChoiceBlocks I).length = I.graph.vertices * I.colors := by
  simp [colorChoiceBlocks, colorChoiceBlocksForVertex, List.length_flatMap]

theorem colorFillerBlocks_length (I : ChromaticNumberInput) :
    (colorFillerBlocks I).length = I.graph.edges.length * I.colors := by
  simp [colorFillerBlocks, colorFillerBlocksForEdge, List.length_flatMap]

theorem colorExactCoverSetSystem_sets_length (I : ChromaticNumberInput) :
    (colorExactCoverSetSystem I).sets.length =
      I.graph.vertices * I.colors + I.graph.edges.length * I.colors := by
  simp [colorExactCoverSetSystem, colorChoiceBlocks_length, colorFillerBlocks_length]

theorem colorExactCoverSetSystem_block_length_le {I : ChromaticNumberInput}
    {B : List Nat} (hB : B ∈ (colorExactCoverSetSystem I).sets) :
    B.length ≤ I.graph.edges.length + 1 := by
  rcases List.mem_append.mp hB with hChoice | hFiller
  · rcases (mem_colorChoiceBlocks_iff I B).1 hChoice with ⟨v, _hv, c, _hc, rfl⟩
    exact colorChoiceBlock_length_le_edges_succ I v c
  · rcases (mem_colorFillerBlocks_iff I B).1 hFiller with ⟨i, _hi, c, _hc, rfl⟩
    simp [colorFillerBlock]

theorem colorExactCoverSetSystem_block_structured_inputSize_le {I : ChromaticNumberInput}
    {B : List Nat} (hB : B ∈ (colorExactCoverSetSystem I).sets) :
    setStructuredEncodedType.inputSize B ≤
      (I.graph.edges.length + 1) * (colorUniverseSize I + 1) := by
  have hList :=
    ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
      EncodedType.nat B (colorUniverseSize I)
      (by
        intro (x : Nat) hx
        have hxLt := colorExactCoverSetSystem_wellFormed I B hB x hx
        have hxLtU : x < colorUniverseSize I := by
          simpa [colorExactCoverSetSystem] using hxLt
        simpa [EncodedType.inputSize, EncodedType.nat] using Nat.succ_le_of_lt hxLtU)
  have hLen := colorExactCoverSetSystem_block_length_le hB
  exact hList.trans (by
    have hMul := Nat.mul_le_mul_right (colorUniverseSize I + 1) hLen
    simpa [setStructuredEncodedType, Nat.add_assoc] using hMul)

theorem colorExactCoverSetSystem_family_structured_inputSize_le
    (I : ChromaticNumberInput) :
    setFamilyStructuredEncodedType.inputSize (colorExactCoverSetSystem I).sets ≤
      (I.graph.vertices * I.colors + I.graph.edges.length * I.colors) *
        ((I.graph.edges.length + 1) * (colorUniverseSize I + 1) + 1) := by
  have hList :=
    ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
      setStructuredEncodedType (colorExactCoverSetSystem I).sets
      ((I.graph.edges.length + 1) * (colorUniverseSize I + 1))
      (by
        intro B hB
        exact colorExactCoverSetSystem_block_structured_inputSize_le hB)
  have hLen := colorExactCoverSetSystem_sets_length I
  exact hList.trans
    (Nat.mul_le_mul_right
      ((I.graph.edges.length + 1) * (colorUniverseSize I + 1) + 1)
      (le_of_eq hLen))

theorem exactCoverStructured_inputSize_eq (I : ExactCoverInput) :
    exactCoverStructuredEncodedType.inputSize I =
      setSystemStructuredEncodedType.inputSize I.system := by
  rfl

theorem chromaticNumberStructured_inputSize_ge_vertices (I : ChromaticNumberInput) :
    I.graph.vertices ≤ chromaticNumberStructuredEncodedType.inputSize I := by
  rw [ChromaticNumber.chromaticNumberStructured_inputSize_eq,
    Clique.graphStructured_inputSize_eq]
  omega

theorem chromaticNumberStructured_inputSize_ge_edges_length (I : ChromaticNumberInput) :
    I.graph.edges.length ≤ chromaticNumberStructuredEncodedType.inputSize I := by
  have hEdges :=
    encodedList_length_le_inputSize edgeStructuredEncodedType I.graph.edges
  have hEdges' :
      I.graph.edges.length ≤ edgeListStructuredEncodedType.inputSize I.graph.edges := by
    simpa [edgeListStructuredEncodedType] using hEdges
  rw [ChromaticNumber.chromaticNumberStructured_inputSize_eq,
    Clique.graphStructured_inputSize_eq]
  omega

theorem chromaticNumberStructured_inputSize_ge_colors (I : ChromaticNumberInput) :
    I.colors ≤ chromaticNumberStructuredEncodedType.inputSize I := by
  rw [ChromaticNumber.chromaticNumberStructured_inputSize_eq]
  omega

theorem exactCoverStructured_inputSize_yesInput_le :
    exactCoverStructuredEncodedType.inputSize yesInput ≤ 20 := by
  native_decide

theorem exactCoverStructured_inputSize_noInput_le :
    exactCoverStructuredEncodedType.inputSize noInput ≤ 20 := by
  native_decide

theorem colorExactCoverCore_structured_inputSize_le_source_poly_succ
    (I : ChromaticNumberInput) :
    exactCoverStructuredEncodedType.inputSize (colorExactCoverCore I) ≤
      1000 * (chromaticNumberStructuredEncodedType.inputSize I + 1) ^ 6 := by
  let S := chromaticNumberStructuredEncodedType.inputSize I
  let V := I.graph.vertices
  let E := I.graph.edges.length
  let C := I.colors
  let U := V + E * C
  have hV : V ≤ S := by
    simpa [S, V] using chromaticNumberStructured_inputSize_ge_vertices I
  have hE : E ≤ S := by
    simpa [S, E] using chromaticNumberStructured_inputSize_ge_edges_length I
  have hC : C ≤ S := by
    simpa [S, C] using chromaticNumberStructured_inputSize_ge_colors I
  have hUniverse : colorUniverseSize I = U := by
    simp [colorUniverseSize, colorEdgeColorPairs_length, U, V, E, C]
  have hFamily := colorExactCoverSetSystem_family_structured_inputSize_le I
  have hBase :
      exactCoverStructuredEncodedType.inputSize (colorExactCoverCore I) ≤
        U + (V * C + E * C) * ((E + 1) * (U + 1) + 1) + 2 := by
    rw [exactCoverStructured_inputSize_eq, SetCovering.setSystemStructured_inputSize_eq]
    change
      (colorExactCoverSetSystem I).universeSize +
          setFamilyStructuredEncodedType.inputSize (colorExactCoverSetSystem I).sets + 2 ≤
        U + (V * C + E * C) * ((E + 1) * (U + 1) + 1) + 2
    have hFamily' :
        setFamilyStructuredEncodedType.inputSize (colorExactCoverSetSystem I).sets ≤
          (V * C + E * C) * ((E + 1) * (U + 1) + 1) := by
      simpa [V, E, C, hUniverse] using hFamily
    simpa [colorExactCoverSetSystem, hUniverse] using
      Nat.add_le_add_right (Nat.add_le_add_left hFamily' U) 2
  have hEC : E * C ≤ S * S := Nat.mul_le_mul hE hC
  have hVC : V * C ≤ S * S := Nat.mul_le_mul hV hC
  have hU : U ≤ (S + 1) ^ 2 := by
    calc
      U = V + E * C := rfl
      _ ≤ S + S * S := by omega
      _ ≤ (S + 1) ^ 2 := by
            ring_nf
            omega
  have hSets : V * C + E * C ≤ 2 * S ^ 2 := by
    ring_nf at hVC hEC ⊢
    omega
  have hBlock :
      (E + 1) * (U + 1) + 1 ≤ (S + 1) * ((S + 1) ^ 2 + 1) + 1 := by
    have hE1 : E + 1 ≤ S + 1 := by omega
    have hU1 : U + 1 ≤ (S + 1) ^ 2 + 1 := by omega
    have hMul : (E + 1) * (U + 1) ≤ (S + 1) * ((S + 1) ^ 2 + 1) :=
      Nat.mul_le_mul hE1 hU1
    omega
  have hMul :
      (V * C + E * C) * ((E + 1) * (U + 1) + 1) ≤
        (2 * S ^ 2) * ((S + 1) * ((S + 1) ^ 2 + 1) + 1) :=
    Nat.mul_le_mul hSets hBlock
  calc
    exactCoverStructuredEncodedType.inputSize (colorExactCoverCore I)
        ≤ U + (V * C + E * C) * ((E + 1) * (U + 1) + 1) + 2 := hBase
    _ ≤ (S + 1) ^ 2 + (2 * S ^ 2) * ((S + 1) * ((S + 1) ^ 2 + 1) + 1) + 2 := by
          omega
    _ ≤ 1000 * (S + 1) ^ 6 := by
          cases S with
          | zero =>
              norm_num
          | succ S =>
              ring_nf
              omega

theorem chromaticNumberToExactCoverMap_structured_inputSize_le_source_poly
    (I : ChromaticNumberInput) :
    exactCoverStructuredEncodedType.inputSize (chromaticNumberToExactCoverMap I) ≤
      1000000 * (chromaticNumberStructuredEncodedType.inputSize I) ^ 6 + 1000000 := by
  let S := chromaticNumberStructuredEncodedType.inputSize I
  have hSuccPoly : 1000 * (S + 1) ^ 6 ≤ 1000000 * S ^ 6 + 1000000 := by
    cases S with
    | zero =>
        norm_num
    | succ S =>
        ring_nf
        omega
  have hSmall : 20 ≤ 1000000 * S ^ 6 + 1000000 := by
    omega
  cases hLoopBool : colorGraphHasSelfLoopBool I
  · have hCoreSize := colorExactCoverCore_structured_inputSize_le_source_poly_succ I
    have hMapSize :
        exactCoverStructuredEncodedType.inputSize (chromaticNumberToExactCoverMap I) ≤
          1000 * (S + 1) ^ 6 := by
      simpa [chromaticNumberToExactCoverMap, hLoopBool, S] using hCoreSize
    exact hMapSize.trans hSuccPoly
  · have hMapSize :
        exactCoverStructuredEncodedType.inputSize (chromaticNumberToExactCoverMap I) ≤
          20 := by
      simpa [chromaticNumberToExactCoverMap, hLoopBool] using
        exactCoverStructured_inputSize_noInput_le
    exact hMapSize.trans hSmall

theorem chromaticNumberToExactCoverStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : ChromaticNumberInput => chromaticNumberStructuredEncodedType.inputSize I)
      (fun J : ExactCoverInput => exactCoverStructuredEncodedType.inputSize J)
      chromaticNumberToExactCoverMap := by
  refine PolynomialSizeBound.intro_with 6 1000000 1000000 ?_
  intro I
  exact chromaticNumberToExactCoverMap_structured_inputSize_le_source_poly I

/-- Costed compact Karp reduction from Chromatic Number to Exact Cover. -/
noncomputable def chromaticNumberToExactCoverTMBackedKarpReduction :
    TMBackedCostedReduction chromaticNumberDecisionProblem exactCoverDecisionProblem := by
  simpa [exactCoverDecisionProblem, exactCoverEncodedType] using
    rawCodomainTMBackedReduction
      chromaticNumberDecisionProblem
      Combinatorics.ExactCover
      chromaticNumberToExactCoverMap
      chromaticNumberToExactCoverMap_correct

/-- Costed compact Karp reduction from Chromatic Number to Exact Cover. -/
noncomputable def chromaticNumberToExactCoverKarpReduction :
    KarpReductionM CostedPolyTimeModel chromaticNumberDecisionProblem exactCoverDecisionProblem :=
  chromaticNumberToExactCoverTMBackedKarpReduction.toCostedKarpReduction

/--
Structured compact Chromatic-Number-to-Exact-Cover transport.

This is the polynomial-size vertex-color / edge-color-marker exact-cover
gadget, guarded only for malformed raw graph inputs.
-/
noncomputable def chromaticNumberToExactCoverStructuredSizeOnlyKarpReduction :
    KarpReductionM CostedPolyTimeModel
      chromaticNumberStructuredDecisionProblem exactCoverStructuredDecisionProblem where
  f :=
    { toFun := chromaticNumberToExactCoverMap
      polytime :=
        CostedPolyTimeMap.of_costed
          (CostedMap.of_encodedPolynomialSizeBound
            chromaticNumberToExactCoverStructured_polynomialSizeBound) }
  correct := by
    intro I
    simpa [chromaticNumberStructuredDecisionProblem, exactCoverStructuredDecisionProblem]
      using chromaticNumberToExactCoverMap_correct I

/--
Structured Set-Covering-to-Exact-Cover transport through the compact CNF route,
the existing CNF-to-3SAT splitter, the structured 3SAT-to-Chromatic-Number
gadget, and the compact Chromatic-Number-to-Exact-Cover gadget.

This is a `CostedPolyTimeModel` composition theorem; it does not claim direct
TM2 soundness for the composed map.
-/
noncomputable def setCoveringToExactCoverViaCNFStructuredSizeOnlyKarpReduction :
    KarpReductionM CostedPolyTimeModel
      setCoveringStructuredDecisionProblem exactCoverStructuredDecisionProblem where
  f :=
    PolyTimeMap.comp chromaticNumberToExactCoverStructuredSizeOnlyKarpReduction.f
      (PolyTimeMap.comp ChromaticNumber.threeSATToChromaticNumberStructuredKarpReduction.f
        (PolyTimeMap.comp cnfSATToThreeSATStructuredKarpReduction.f
          setCoveringToSatisfiabilityStructuredSizeOnlyKarpReduction.f))
  correct := by
    intro I
    have h1 := setCoveringToSatisfiabilityStructuredSizeOnlyKarpReduction.correct I
    have h2 :=
      cnfSATToThreeSATStructuredKarpReduction.correct
        (setCoveringToSatisfiabilityStructuredSizeOnlyKarpReduction.f.toFun I)
    have h3 :=
      ChromaticNumber.threeSATToChromaticNumberStructuredKarpReduction.correct
        (cnfSATToThreeSATStructuredKarpReduction.f.toFun
          (setCoveringToSatisfiabilityStructuredSizeOnlyKarpReduction.f.toFun I))
    have h4 :=
      chromaticNumberToExactCoverStructuredSizeOnlyKarpReduction.correct
        (ChromaticNumber.threeSATToChromaticNumberStructuredKarpReduction.f.toFun
          (cnfSATToThreeSATStructuredKarpReduction.f.toFun
            (setCoveringToSatisfiabilityStructuredSizeOnlyKarpReduction.f.toFun I)))
    simpa [PolyTimeMap.comp] using Iff.trans h1 (Iff.trans h2 (Iff.trans h3 h4))

/-- P15e syntax map from Set Covering to Exact Cover. -/
noncomputable def map (I : SetCoveringInput) : ExactCoverInput :=
  indicatorInput (setCoveringWitnesses I).length

theorem map_correct (I : SetCoveringInput) :
    setCoveringDecisionProblem.isYes I ↔ ExactCover (map I) := by
  change SetCovering I ↔ ExactCover (map I)
  rw [setCovering_iff_witnesses_pos]
  exact (indicatorInput_correct (setCoveringWitnesses I).length).symm

/-- Costed Karp reduction from Set Covering to Exact Cover. -/
noncomputable def setCoveringToExactCoverTMBackedKarpReduction :
    TMBackedCostedReduction setCoveringDecisionProblem exactCoverDecisionProblem := by
  simpa [exactCoverDecisionProblem, exactCoverEncodedType] using
    rawCodomainTMBackedReduction
      setCoveringDecisionProblem
      Combinatorics.ExactCover
      map
      map_correct

/-- Costed Karp reduction from Set Covering to Exact Cover. -/
noncomputable def setCoveringToExactCoverKarpReduction :
    KarpReductionM CostedPolyTimeModel setCoveringDecisionProblem exactCoverDecisionProblem :=
  setCoveringToExactCoverTMBackedKarpReduction.toCostedKarpReduction

/-- Costed textbook slack/dummy Karp reduction from Set Covering to Exact Cover. -/
noncomputable def setCoveringToExactCover_textbookTMBackedKarpReduction :
    TMBackedCostedReduction setCoveringDecisionProblem exactCoverDecisionProblem := by
  simpa [exactCoverDecisionProblem, exactCoverEncodedType] using
    rawCodomainTMBackedReduction
      setCoveringDecisionProblem
      Combinatorics.ExactCover
      textbookMap
      textbookMap_correct

/-- Costed textbook slack/dummy Karp reduction from Set Covering to Exact Cover. -/
noncomputable def setCoveringToExactCover_textbookKarpReduction :
    KarpReductionM CostedPolyTimeModel setCoveringDecisionProblem exactCoverDecisionProblem :=
  setCoveringToExactCover_textbookTMBackedKarpReduction.toCostedKarpReduction

theorem exactCoverStructuredEncoding_faithful :
    exactCoverStructuredDecisionProblem.FaithfulEncoding where
  injective := exactCoverStructuredEncodedType_encode_injective

theorem exactCoverStructuredEncoding_predicateRespects :
    exactCoverStructuredDecisionProblem.PredicateRespectsEncoding :=
  exactCoverStructuredEncoding_faithful.predicateRespects

theorem exactCoverStructuredEncoding_accepts_encode_iff (I : ExactCoverInput) :
    exactCoverStructuredDecisionProblem.toEncodedLanguage.accepts
        (exactCoverStructuredEncodedType.encode I) ↔
      ExactCover I :=
  exactCoverStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

/-- Exact Cover is locally in NP for the project-local costed model. -/
theorem exactCoverInNP :
    InNPEnc CostedPolyTimeModel exactCoverDecisionProblem :=
  decidableInNP exactCoverDecisionProblem

/-- Local NP-completeness of Exact Cover via the compact Chromatic Number route. -/
theorem exactCover_chromaticNumberCompactNPComplete :
    NPCompleteEnc CostedPolyTimeModel exactCoverDecisionProblem :=
  NPCompleteEnc.transfer
    ChromaticNumber.chromaticNumber_textbookNPComplete
    ⟨chromaticNumberToExactCoverKarpReduction⟩
    exactCoverInNP

/-- Local NP-completeness of Exact Cover via Set Covering. -/
theorem exactCoverNPComplete :
    NPCompleteEnc CostedPolyTimeModel exactCoverDecisionProblem :=
  NPCompleteEnc.transfer
    SetCovering.setCoveringNPComplete
    ⟨setCoveringToExactCoverKarpReduction⟩
    exactCoverInNP

/-- Local NP-completeness of Exact Cover via the P15j textbook slack/dummy route. -/
theorem exactCover_textbookNPComplete :
    NPCompleteEnc CostedPolyTimeModel exactCoverDecisionProblem :=
  NPCompleteEnc.transfer
    SetCovering.setCoveringNPComplete
    ⟨setCoveringToExactCover_textbookKarpReduction⟩
    exactCoverInNP

end ExactCover
end Karp21
end ComplexityReduction
