import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.Part4
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.Assembly

namespace ComplexityReduction
namespace Karp21
namespace Knapsack
open ComplexityReduction.Combinatorics

theorem elementCount_pos_of_mem {x : Nat} {sets : List (List Nat)} {S : List Nat}
    (hS : S ∈ sets) (hxS : x ∈ S) :
    0 < elementCount x sets := by
  induction sets with
  | nil =>
      simp at hS
  | cons T sets ih =>
      simp at hS
      rcases hS with rfl | hS
      · simp [elementCount, hxS]
      · by_cases hxT : x ∈ T
        · simp [elementCount, hxT]
        · simp [elementCount, hxT, ih hS]

theorem exists_mem_of_elementCount_pos {x : Nat} {sets : List (List Nat)}
    (hPos : 0 < elementCount x sets) :
    ∃ S ∈ sets, x ∈ S := by
  induction sets with
  | nil =>
      simp [elementCount] at hPos
  | cons S sets ih =>
      by_cases hxS : x ∈ S
      · exact ⟨S, by simp, hxS⟩
      · have hTail : 0 < elementCount x sets := by
          simpa [elementCount, hxS] using hPos
        rcases ih hTail with ⟨T, hT, hxT⟩
        exact ⟨T, by simp [hT], hxT⟩

theorem elementCount_eq_zero_of_forall_not_mem {x : Nat} {sets : List (List Nat)}
    (hNone : ∀ S ∈ sets, x ∉ S) :
    elementCount x sets = 0 := by
  induction sets with
  | nil =>
      simp [elementCount]
  | cons S sets ih =>
      have hxS : x ∉ S := hNone S (by simp)
      have hTail : ∀ T ∈ sets, x ∉ T := by
        intro T hT
        exact hNone T (by simp [hT])
      simp [elementCount, hxS, ih hTail]

theorem elementCount_le_one_of_pairwise {x : Nat} {sets : List (List Nat)}
    (hNodup : sets.Nodup) (hDisjoint : PairwiseDisjointFamily sets) :
    elementCount x sets ≤ 1 := by
  induction sets with
  | nil =>
      simp [elementCount]
  | cons S sets ih =>
      by_cases hxS : x ∈ S
      · have hNone : ∀ T ∈ sets, x ∉ T := by
          intro T hT hxT
          exact hDisjoint S (by simp) T (by simp [hT])
            (by
              intro hEq
              subst T
              exact hNodup.notMem hT)
            x hxS hxT
        simp [elementCount, hxS, elementCount_eq_zero_of_forall_not_mem hNone]
      · have hDisjointTail : PairwiseDisjointFamily sets := by
          intro A hA B hB hNe y hyA hyB
          exact hDisjoint A (by simp [hA]) B (by simp [hB]) hNe y hyA hyB
        have hTail := ih hNodup.of_cons hDisjointTail
        simpa [elementCount, hxS] using hTail

theorem elementCount_eq_one_of_exact {I : ExactCoverInput} {sets : List (List Nat)}
    (hNodup : sets.Nodup) (hDisjoint : PairwiseDisjointFamily sets)
    (hCovers : CoversUniverse I.system sets) {x : Nat} (hx : x < I.system.universeSize) :
    elementCount x sets = 1 := by
  rcases hCovers x hx with ⟨S, hS, hxS⟩
  have hPos := elementCount_pos_of_mem hS hxS
  have hLe := elementCount_le_one_of_pairwise (x := x) hNodup hDisjoint
  omega

theorem digitCountsFrom_eq_replicate_one_of_exact {I : ExactCoverInput}
    {sets : List (List Nat)} (hNodup : sets.Nodup)
    (hDisjoint : PairwiseDisjointFamily sets) (hCovers : CoversUniverse I.system sets)
    {start len : Nat} (hBound : start + len ≤ I.system.universeSize) :
    digitCountsFrom start len sets = List.replicate len 1 := by
  induction len generalizing start with
  | zero =>
      simp [digitCountsFrom]
  | succ len ih =>
      have hx : start < I.system.universeSize := by omega
      have hHead := elementCount_eq_one_of_exact (I := I) hNodup hDisjoint hCovers hx
      have hTail : start + 1 + len ≤ I.system.universeSize := by omega
      simp [digitCountsFrom, hHead, ih hTail, List.replicate_succ]

theorem digitCountsFrom_cons (start len : Nat) (S : List Nat) (sets : List (List Nat)) :
    digitCountsFrom start len (S :: sets) =
      (digitCountsFrom start len [S]).zipWith (· + ·) (digitCountsFrom start len sets) := by
  induction len generalizing start with
  | zero =>
      simp [digitCountsFrom]
  | succ len ih =>
      simp [digitCountsFrom, elementCount, ih]

theorem sum_exactCoverSetCode_eq_ofDigits_counts (I : ExactCoverInput)
    (sets : List (List Nat)) :
    ((sets.map (exactCoverSetCode I)).sum) =
      Nat.ofDigits (exactCoverDigitBase I) (exactCoverDigitCounts I sets) := by
  induction sets with
  | nil =>
      simp [exactCoverDigitCounts, digitCountsFrom_nil, Nat.ofDigits_replicate_zero]
  | cons S sets ih =>
      have hLen :
          (digitCountsFrom 0 I.system.universeSize [S]).length =
            (digitCountsFrom 0 I.system.universeSize sets).length := by
        simp [digitCountsFrom_length]
      rw [List.map_cons, List.sum_cons, ih]
      simp only [exactCoverSetCode, exactCoverSetDigits, exactCoverDigitCounts]
      rw [Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq hLen]
      rw [← digitCountsFrom_cons]

theorem digitCountsFrom_mem_le_length {start len : Nat} {sets : List (List Nat)} {d : Nat}
    (hd : d ∈ digitCountsFrom start len sets) :
    d ≤ sets.length := by
  induction len generalizing start with
  | zero =>
      simp [digitCountsFrom] at hd
  | succ len ih =>
      simp [digitCountsFrom] at hd
      rcases hd with hd | hd
      · subst d
        exact elementCount_le_length start sets
      · exact ih hd

theorem digitCounts_eq_target_of_code_eq {I : ExactCoverInput} {sets : List (List Nat)}
    (hLen : sets.length ≤ I.system.sets.length)
    (hEq :
      Nat.ofDigits (exactCoverDigitBase I) (exactCoverDigitCounts I sets) =
        exactCoverTargetCode I) :
    exactCoverDigitCounts I sets = exactCoverTargetDigits I := by
  have hBase : 1 < exactCoverDigitBase I := by
    simp [exactCoverDigitBase]
  have hLength :
      (exactCoverDigitCounts I sets).length = (exactCoverTargetDigits I).length := by
    simp [exactCoverDigitCounts, exactCoverTargetDigits, digitCountsFrom_length]
  have hCountsLt : ∀ d ∈ exactCoverDigitCounts I sets, d < exactCoverDigitBase I := by
    intro d hd
    have hLe := digitCountsFrom_mem_le_length (start := 0)
      (len := I.system.universeSize) (sets := sets) hd
    simp [exactCoverDigitBase]
    omega
  have hTargetLt : ∀ d ∈ exactCoverTargetDigits I, d < exactCoverDigitBase I := by
    intro d hd
    simp [exactCoverTargetDigits] at hd
    rcases hd with ⟨_hPos, rfl⟩
    simp [exactCoverDigitBase]
  exact Nat.ofDigits_inj_of_len_eq hBase hLength hCountsLt hTargetLt hEq

theorem elementCount_eq_one_of_digitCounts_eq_target {I : ExactCoverInput}
    {sets : List (List Nat)}
    (hDigits : exactCoverDigitCounts I sets = exactCoverTargetDigits I)
    {x : Nat} (hx : x < I.system.universeSize) :
    elementCount x sets = 1 := by
  have h :
      digitCountsFrom 0 I.system.universeSize sets =
        List.replicate I.system.universeSize 1 := by
    simpa [exactCoverDigitCounts, exactCoverTargetDigits] using hDigits
  have hGeneral :
      ∀ {start len : Nat},
        digitCountsFrom start len sets = List.replicate len 1 →
        start ≤ x →
        x < start + len →
        elementCount x sets = 1 := by
    intro start len
    induction len generalizing start with
    | zero =>
        intro _h _hlo hhi
        omega
    | succ len ih =>
        intro h hle hhi
        by_cases hxStart : x = start
        · subst x
          simp [digitCountsFrom, List.replicate_succ] at h
          exact h.1
        · have hTail : digitCountsFrom (start + 1) len sets = List.replicate len 1 := by
            simp [digitCountsFrom, List.replicate_succ] at h
            exact h.2
          exact ih hTail (by omega) (by omega)
  exact hGeneral h (by omega) (by simpa using hx)

theorem elementCount_ge_two_of_pair {x : Nat} {sets : List (List Nat)}
    {A B : List Nat} (hA : A ∈ sets) (hB : B ∈ sets) (hNe : A ≠ B)
    (hxA : x ∈ A) (hxB : x ∈ B) :
    2 ≤ elementCount x sets := by
  induction sets generalizing A B with
  | nil =>
      simp at hA
  | cons S sets ih =>
      simp at hA hB
      rcases hA with rfl | hA
      · rcases hB with rfl | hB
        · exact (hNe rfl).elim
        · have hTailPos := elementCount_pos_of_mem hB hxB
          simp [elementCount, hxA]
          omega
      · rcases hB with rfl | hB
        · have hTailPos := elementCount_pos_of_mem hA hxA
          simp [elementCount, hxB]
          omega
        · have hTail := ih hA hB hNe hxA hxB
          by_cases hxS : x ∈ S <;> simp [elementCount, hxS] <;> omega

theorem exactCoverBaseDigit_filtered_family {I : ExactCoverInput}
    {selected : List (List Nat)} :
    ∀ S ∈ selectedSetsFrom (exactCoverSourceSets I)
        (exactCoverBitsFromSelection (exactCoverSourceSets I) selected),
      IsSetInFamily I.system S := by
  intro S hS
  have hSource := mem_selectedSetsFrom hS
  exact List.mem_dedup.mp hSource

theorem exactCoverBaseDigit_filtered_exact {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (_hNodup : selected.Nodup)
    (hDisjoint : PairwiseDisjointFamily selected)
    (hCovers : CoversUniverse I.system selected) :
    let filtered :=
      selectedSetsFrom (exactCoverSourceSets I)
        (exactCoverBitsFromSelection (exactCoverSourceSets I) selected)
    filtered.Nodup ∧ PairwiseDisjointFamily filtered ∧ CoversUniverse I.system filtered := by
  classical
  let source := exactCoverSourceSets I
  let bits := exactCoverBitsFromSelection source selected
  have hFiltered :
      selectedSetsFrom source bits = source.filter fun S => decide (S ∈ selected) := by
    simpa [source, bits] using selectedSetsFrom_membershipSelector source selected
  have hNodupFiltered : (selectedSetsFrom source bits).Nodup := by
    exact selectedSetsFrom_nodup (List.nodup_dedup I.system.sets)
  have hDisjointFiltered : PairwiseDisjointFamily (selectedSetsFrom source bits) := by
    intro A hA B hB hNe x hxA hxB
    have hASelected : A ∈ selected := by
      rw [hFiltered] at hA
      exact of_decide_eq_true (List.mem_filter.mp hA).2
    have hBSelected : B ∈ selected := by
      rw [hFiltered] at hB
      exact of_decide_eq_true (List.mem_filter.mp hB).2
    exact hDisjoint A hASelected B hBSelected hNe x hxA hxB
  have hCoversFiltered : CoversUniverse I.system (selectedSetsFrom source bits) := by
    intro x hx
    rcases hCovers x hx with ⟨S, hSSelected, hxS⟩
    have hSSource : S ∈ source := by
      exact List.mem_dedup.mpr (hFamily S hSSelected)
    refine ⟨S, ?_, hxS⟩
    rw [hFiltered]
    exact List.mem_filter.mpr ⟨hSSource, decide_eq_true hSSelected⟩
  exact ⟨hNodupFiltered, hDisjointFiltered, hCoversFiltered⟩

theorem exactCoverNoKnapsackInput_not :
    ¬ Combinatorics.Knapsack exactCoverNoKnapsackInput := by
  rintro ⟨selected, hLen, _hWeight, hValue⟩
  cases selected with
  | nil =>
      simp [exactCoverNoKnapsackInput, selectedValue] at hValue
  | cons b bs =>
      simp [exactCoverNoKnapsackInput] at hLen

theorem exactCoverBaseDigitMapCore_correct (I : ExactCoverInput)
    (hWellFormed : SetSystemWellFormed I.system) :
    (∃ selected : List (List Nat),
      (∀ S ∈ selected, IsSetInFamily I.system S) ∧
        selected.Nodup ∧
        PairwiseDisjointFamily selected ∧
        CoversUniverse I.system selected) ↔
      Combinatorics.Knapsack (exactCoverBaseDigitMapCore I) := by
  constructor
  · rintro ⟨selected, hFamily, hNodup, hDisjoint, hCovers⟩
    let source := exactCoverSourceSets I
    let bits := exactCoverBitsFromSelection source selected
    let filtered := selectedSetsFrom source bits
    have hExactFiltered :=
      exactCoverBaseDigit_filtered_exact
        (I := I) hFamily hNodup hDisjoint hCovers
    have hDigits :
        exactCoverDigitCounts I filtered = exactCoverTargetDigits I := by
      exact digitCountsFrom_eq_replicate_one_of_exact
        (I := I) hExactFiltered.1 hExactFiltered.2.1 hExactFiltered.2.2 (by omega)
    have hSum :
        ((filtered.map (exactCoverSetCode I)).sum) = exactCoverTargetCode I := by
      rw [sum_exactCoverSetCode_eq_ofDigits_counts]
      simp [exactCoverTargetCode, hDigits]
    refine ⟨bits, ?_, ?_, ?_⟩
    · simp [bits, source, exactCoverBaseDigitMapCore, exactCoverBaseDigitItems,
        exactCoverBitsFromSelection]
    · rw [selectedWeight_exactCoverBaseDigitMapCore]
      simpa [filtered, source, bits] using hSum.le
    · rw [selectedValue_exactCoverBaseDigitMapCore]
      simpa [filtered, source, bits] using hSum.ge
  · rintro ⟨bits, hLen, hWeight, hValue⟩
    let source := exactCoverSourceSets I
    let selected := selectedSetsFrom source bits
    have hWeight' :
        ((selected.map (exactCoverSetCode I)).sum) ≤ exactCoverTargetCode I := by
      have hWeightCore := hWeight
      rw [selectedWeight_exactCoverBaseDigitMapCore] at hWeightCore
      simpa [selected, source, exactCoverBaseDigitMapCore] using hWeightCore
    have hValue' :
        exactCoverTargetCode I ≤ ((selected.map (exactCoverSetCode I)).sum) := by
      have hValueCore := hValue
      rw [selectedValue_exactCoverBaseDigitMapCore] at hValueCore
      simpa [selected, source, exactCoverBaseDigitMapCore] using hValueCore
    have hSumEq :
        ((selected.map (exactCoverSetCode I)).sum) = exactCoverTargetCode I :=
      le_antisymm hWeight' hValue'
    have hCodeEq :
        Nat.ofDigits (exactCoverDigitBase I) (exactCoverDigitCounts I selected) =
          exactCoverTargetCode I := by
      simpa [sum_exactCoverSetCode_eq_ofDigits_counts] using hSumEq
    have hSelectedLen : selected.length ≤ I.system.sets.length := by
      have hLenSource : source.length ≤ I.system.sets.length := by
        simpa [source, exactCoverSourceSets] using
          List.Sublist.length_le (List.dedup_sublist I.system.sets)
      exact (selectedSetsFrom_length_le source bits).trans hLenSource
    have hDigits := digitCounts_eq_target_of_code_eq (I := I)
      (sets := selected) hSelectedLen hCodeEq
    have hFamily : ∀ S ∈ selected, IsSetInFamily I.system S := by
      intro S hS
      have hSource : S ∈ source := mem_selectedSetsFrom hS
      exact List.mem_dedup.mp hSource
    have hNodup : selected.Nodup := by
      have hSourceNodup : source.Nodup := by
        simpa [source, exactCoverSourceSets] using List.nodup_dedup I.system.sets
      exact selectedSetsFrom_nodup hSourceNodup
    have hCovers : CoversUniverse I.system selected := by
      intro x hx
      have hCount := elementCount_eq_one_of_digitCounts_eq_target
        (I := I) (sets := selected) hDigits hx
      rcases exists_mem_of_elementCount_pos (x := x) (sets := selected) (by omega)
        with ⟨S, hS, hxS⟩
      exact ⟨S, hS, hxS⟩
    have hDisjoint : PairwiseDisjointFamily selected := by
      intro A hA B hB hNe x hxA hxB
      have hCount := elementCount_eq_one_of_digitCounts_eq_target
        (I := I) (sets := selected) hDigits
        (by
          exact hWellFormed A (hFamily A hA) x hxA)
      have hTwo := elementCount_ge_two_of_pair hA hB hNe hxA hxB
      omega
    exact ⟨selected, hFamily, hNodup, hDisjoint, hCovers⟩

theorem exactCoverBaseDigitMap_correct (I : ExactCoverInput) :
    exactCoverDecisionProblem.isYes I ↔ Combinatorics.Knapsack (exactCoverBaseDigitMap I) := by
  change ExactCover I ↔ Combinatorics.Knapsack (exactCoverBaseDigitMap I)
  constructor
  · rintro ⟨hWellFormed, hWitness⟩
    have hCore := (exactCoverBaseDigitMapCore_correct I hWellFormed).1 hWitness
    simpa [exactCoverBaseDigitMap, hWellFormed] using hCore
  · intro hKnapsack
    by_cases hWellFormed : SetSystemWellFormed I.system
    · have hCore : Combinatorics.Knapsack (exactCoverBaseDigitMapCore I) := by
        simpa [exactCoverBaseDigitMap, hWellFormed] using hKnapsack
      exact ⟨hWellFormed, (exactCoverBaseDigitMapCore_correct I hWellFormed).2 hCore⟩
    · have hNo : Combinatorics.Knapsack exactCoverNoKnapsackInput := by
        simpa [exactCoverBaseDigitMap, hWellFormed] using hKnapsack
      exact (exactCoverNoKnapsackInput_not hNo).elim

/-! ### Binary-structured size bounds for the Exact Cover base-digit route -/

theorem exactCoverStructured_inputSize_eq (I : ExactCoverInput) :
    exactCoverStructuredEncodedType.inputSize I =
      EncodedType.nat.inputSize I.system.universeSize + 1 +
        setFamilyStructuredEncodedType.inputSize I.system.sets := by
  cases I with
  | mk system =>
      cases system with
      | mk universeSize sets =>
          change (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType).inputSize
              (universeSize, sets) =
            EncodedType.nat.inputSize universeSize + 1 +
              setFamilyStructuredEncodedType.inputSize sets
          simp

theorem exactCoverStructured_inputSize_pos (I : ExactCoverInput) :
    0 < exactCoverStructuredEncodedType.inputSize I := by
  rw [exactCoverStructured_inputSize_eq]
  simp [EncodedType.inputSize, EncodedType.nat]

theorem exactCover_universeSize_le_structured_inputSize (I : ExactCoverInput) :
    I.system.universeSize ≤ exactCoverStructuredEncodedType.inputSize I := by
  rw [exactCoverStructured_inputSize_eq]
  simp [EncodedType.inputSize, EncodedType.nat]
  omega

theorem exactCover_sets_length_le_structured_inputSize (I : ExactCoverInput) :
    I.system.sets.length ≤ exactCoverStructuredEncodedType.inputSize I := by
  have hList : I.system.sets.length ≤
      setFamilyStructuredEncodedType.inputSize I.system.sets := by
    simpa [setFamilyStructuredEncodedType] using
      encodedList_length_le_inputSize setStructuredEncodedType I.system.sets
  rw [exactCoverStructured_inputSize_eq]
  exact hList.trans (by omega)

theorem exactCoverSourceSets_length_le_structured_inputSize (I : ExactCoverInput) :
    (exactCoverSourceSets I).length ≤ exactCoverStructuredEncodedType.inputSize I := by
  have hDedup : (exactCoverSourceSets I).length ≤ I.system.sets.length := by
    simpa [exactCoverSourceSets] using
      List.Sublist.length_le (List.dedup_sublist I.system.sets)
  exact hDedup.trans (exactCover_sets_length_le_structured_inputSize I)

theorem exactCoverDigitBase_gt_one (I : ExactCoverInput) :
    1 < exactCoverDigitBase I := by
  simp [exactCoverDigitBase]

theorem exactCoverDigitBase_lt_two_pow_source_succ (I : ExactCoverInput) :
    exactCoverDigitBase I <
      2 ^ (exactCoverStructuredEncodedType.inputSize I + 2) := by
  let S := exactCoverStructuredEncodedType.inputSize I
  have hSets : I.system.sets.length ≤ S := by
    simpa [S] using exactCover_sets_length_le_structured_inputSize I
  have hBaseLe : exactCoverDigitBase I ≤ S + 2 := by
    simp [exactCoverDigitBase]
    omega
  exact hBaseLe.trans_lt (S + 2).lt_two_pow_self

def exactCoverBaseDigitCodeBitBound (I : ExactCoverInput) : Nat :=
  4 * (exactCoverStructuredEncodedType.inputSize I + 1) ^ 2

theorem exactCoverDigitCode_binaryNat_inputSize_le
    (I : ExactCoverInput) {digits : List Nat}
    (hLength : digits.length = I.system.universeSize)
    (hDigits : ∀ digit ∈ digits, digit < exactCoverDigitBase I) :
    EncodedType.binaryNat.inputSize
        (Nat.ofDigits (exactCoverDigitBase I) digits : Nat) ≤
      exactCoverBaseDigitCodeBitBound I := by
  let S := exactCoverStructuredEncodedType.inputSize I
  have hCodeBase :
      Nat.ofDigits (exactCoverDigitBase I) digits < (exactCoverDigitBase I) ^ digits.length := by
    exact Nat.ofDigits_lt_base_pow_length (exactCoverDigitBase_gt_one I) hDigits
  have hBaseLe : exactCoverDigitBase I ≤ 2 ^ (S + 2) :=
    Nat.le_of_lt (by simpa [S] using exactCoverDigitBase_lt_two_pow_source_succ I)
  have hPowLe :
      (exactCoverDigitBase I) ^ digits.length ≤ (2 ^ (S + 2)) ^ digits.length :=
    Nat.pow_le_pow_left hBaseLe digits.length
  have hCodePow :
      Nat.ofDigits (exactCoverDigitBase I) digits <
        2 ^ ((S + 2) * I.system.universeSize) := by
    calc
      Nat.ofDigits (exactCoverDigitBase I) digits
          < (exactCoverDigitBase I) ^ digits.length := hCodeBase
      _ ≤ (2 ^ (S + 2)) ^ digits.length := hPowLe
      _ = 2 ^ ((S + 2) * I.system.universeSize) := by
          rw [hLength]
          rw [Nat.pow_mul]
  have hUniverse : I.system.universeSize ≤ S := by
    simpa [S] using exactCover_universeSize_le_structured_inputSize I
  have hExp :
      (S + 2) * I.system.universeSize ≤ exactCoverBaseDigitCodeBitBound I := by
    dsimp [exactCoverBaseDigitCodeBitBound]
    nlinarith
  exact binaryNat_inputSize_le_of_lt_two_pow
    (hCodePow.trans_le (pow_two_le_pow_two_of_le hExp))

theorem exactCoverSetCode_binaryNat_inputSize_le (I : ExactCoverInput) (S : List Nat) :
    EncodedType.binaryNat.inputSize (exactCoverSetCode I S) ≤
      exactCoverBaseDigitCodeBitBound I := by
  refine exactCoverDigitCode_binaryNat_inputSize_le I ?_ ?_
  · simp [exactCoverSetDigits, digitCountsFrom_length]
  · intro digit hdigit
    have hDigit := digitCountsFrom_singleton_mem_le_one (S := S) hdigit
    have hBase := exactCoverDigitBase_gt_one I
    omega

theorem exactCoverTargetCode_binaryNat_inputSize_le (I : ExactCoverInput) :
    EncodedType.binaryNat.inputSize (exactCoverTargetCode I) ≤
      exactCoverBaseDigitCodeBitBound I := by
  refine exactCoverDigitCode_binaryNat_inputSize_le I ?_ ?_
  · simp [exactCoverTargetDigits]
  · intro digit hdigit
    have hBase := exactCoverDigitBase_gt_one I
    simp [exactCoverTargetDigits] at hdigit
    rcases hdigit with ⟨_hPos, rfl⟩
    exact hBase

theorem exactCoverBaseDigitItem_binaryStructured_inputSize_le
    {I : ExactCoverInput} {item : Nat × Nat}
    (hitem : item ∈ exactCoverBaseDigitItems I) :
    knapsackItemBinaryStructuredEncodedType.inputSize item ≤
      2 * exactCoverBaseDigitCodeBitBound I + 1 := by
  rcases List.mem_map.mp hitem with ⟨S, _hS, rfl⟩
  have hCode := exactCoverSetCode_binaryNat_inputSize_le I S
  simp [knapsackItemBinaryStructuredEncodedType]
  omega

theorem exactCoverBaseDigitItems_binaryStructured_inputSize_le
    (I : ExactCoverInput) :
    knapsackItemListBinaryStructuredEncodedType.inputSize (exactCoverBaseDigitItems I) ≤
      (exactCoverSourceSets I).length * (2 * exactCoverBaseDigitCodeBitBound I + 2) := by
  have hList :=
    Clique.encodedList_inputSize_le_length_mul_bound knapsackItemBinaryStructuredEncodedType
      (exactCoverBaseDigitItems I) (2 * exactCoverBaseDigitCodeBitBound I + 1)
      (by
        intro item hitem
        exact exactCoverBaseDigitItem_binaryStructured_inputSize_le hitem)
  calc
    knapsackItemListBinaryStructuredEncodedType.inputSize (exactCoverBaseDigitItems I)
        ≤ (exactCoverBaseDigitItems I).length *
            (2 * exactCoverBaseDigitCodeBitBound I + 1 + 1) := by
          simpa [knapsackItemListBinaryStructuredEncodedType] using hList
    _ = (exactCoverSourceSets I).length * (2 * exactCoverBaseDigitCodeBitBound I + 2) := by
          simp [exactCoverBaseDigitItems]

theorem exactCoverBaseDigitMapCore_binaryStructured_inputSize_le
    (I : ExactCoverInput) :
    knapsackBinaryStructuredEncodedType.inputSize (exactCoverBaseDigitMapCore I) ≤
      ((exactCoverSourceSets I).length + 1) *
        (2 * exactCoverBaseDigitCodeBitBound I + 2) := by
  have hItems := exactCoverBaseDigitItems_binaryStructured_inputSize_le I
  have hTarget := exactCoverTargetCode_binaryNat_inputSize_le I
  rw [knapsackBinaryStructured_inputSize_eq]
  simp [exactCoverBaseDigitMapCore]
  calc
    knapsackItemListBinaryStructuredEncodedType.inputSize (exactCoverBaseDigitItems I) +
          1 + (EncodedType.binaryNat.inputSize (exactCoverTargetCode I) + 1 +
            EncodedType.binaryNat.inputSize (exactCoverTargetCode I))
        ≤ (exactCoverSourceSets I).length * (2 * exactCoverBaseDigitCodeBitBound I + 2) +
            1 + (exactCoverBaseDigitCodeBitBound I + 1 +
              exactCoverBaseDigitCodeBitBound I) := by
          omega
    _ ≤ ((exactCoverSourceSets I).length + 1) *
          (2 * exactCoverBaseDigitCodeBitBound I + 2) := by
          ring_nf
          omega

theorem exactCoverBaseDigitMapCore_binaryStructured_inputSize_le_source_poly_succ
    (I : ExactCoverInput) :
    knapsackBinaryStructuredEncodedType.inputSize (exactCoverBaseDigitMapCore I) ≤
      10 * (exactCoverStructuredEncodedType.inputSize I + 1) ^ 3 := by
  let S := exactCoverStructuredEncodedType.inputSize I
  let T := S + 1
  have hOut := exactCoverBaseDigitMapCore_binaryStructured_inputSize_le I
  have hItems : (exactCoverSourceSets I).length + 1 ≤ T := by
    have hLen := exactCoverSourceSets_length_le_structured_inputSize I
    dsimp [T, S]
    omega
  have hBound :
      2 * exactCoverBaseDigitCodeBitBound I + 2 ≤ 10 * T ^ 2 := by
    have hT2 : 1 ≤ T ^ 2 := by
      have hT : 1 ≤ T := by dsimp [T]; omega
      simpa using Nat.pow_le_pow_left hT 2
    have hTwo : 2 ≤ 2 * T ^ 2 := by
      calc
        2 = 2 * 1 := by ring
        _ ≤ 2 * T ^ 2 := Nat.mul_le_mul_left 2 hT2
    calc
      2 * exactCoverBaseDigitCodeBitBound I + 2
          = 8 * T ^ 2 + 2 := by
            dsimp [exactCoverBaseDigitCodeBitBound, T, S]
            ring
      _ ≤ 8 * T ^ 2 + 2 * T ^ 2 := Nat.add_le_add_left hTwo (8 * T ^ 2)
      _ = 10 * T ^ 2 := by ring
  have hProduct :
      ((exactCoverSourceSets I).length + 1) *
          (2 * exactCoverBaseDigitCodeBitBound I + 2) ≤ T * (10 * T ^ 2) :=
    Nat.mul_le_mul hItems hBound
  have hPoly : T * (10 * T ^ 2) = 10 * T ^ 3 := by ring
  exact hOut.trans (hProduct.trans (le_of_eq hPoly))

theorem exactCoverNoKnapsackInput_binaryStructured_inputSize_le :
    knapsackBinaryStructuredEncodedType.inputSize exactCoverNoKnapsackInput ≤ 10 := by
  native_decide

theorem exactCoverBaseDigitMap_binaryStructured_inputSize_le_source_poly_succ
    (I : ExactCoverInput) :
    knapsackBinaryStructuredEncodedType.inputSize (exactCoverBaseDigitMap I) ≤
      10 * (exactCoverStructuredEncodedType.inputSize I + 1) ^ 3 := by
  classical
  by_cases hWellFormed : SetSystemWellFormed I.system
  · simpa [exactCoverBaseDigitMap, hWellFormed] using
      exactCoverBaseDigitMapCore_binaryStructured_inputSize_le_source_poly_succ I
  · have hNo := exactCoverNoKnapsackInput_binaryStructured_inputSize_le
    have hPos : 1 ≤ (exactCoverStructuredEncodedType.inputSize I + 1) ^ 3 := by
      have hBase : 1 ≤ exactCoverStructuredEncodedType.inputSize I + 1 := by omega
      simpa using Nat.pow_le_pow_left hBase 3
    have hPoly : 10 ≤ 10 * (exactCoverStructuredEncodedType.inputSize I + 1) ^ 3 := by
      calc
        10 = 10 * 1 := by ring
        _ ≤ 10 * (exactCoverStructuredEncodedType.inputSize I + 1) ^ 3 :=
          Nat.mul_le_mul_left 10 hPos
    exact (by simpa [exactCoverBaseDigitMap, hWellFormed] using hNo.trans hPoly)

theorem exactCoverBaseDigitMap_binaryStructured_inputSize_le_source_poly
    (I : ExactCoverInput) :
    knapsackBinaryStructuredEncodedType.inputSize (exactCoverBaseDigitMap I) ≤
      80 * (exactCoverStructuredEncodedType.inputSize I) ^ 3 + 10 := by
  let S := exactCoverStructuredEncodedType.inputSize I
  have hSucc := exactCoverBaseDigitMap_binaryStructured_inputSize_le_source_poly_succ I
  have hPos : 0 < S := by
    simpa [S] using exactCoverStructured_inputSize_pos I
  have hSuccLe : S + 1 ≤ 2 * S := by omega
  have hPow : (S + 1) ^ 3 ≤ (2 * S) ^ 3 :=
    Nat.pow_le_pow_left hSuccLe 3
  have hExpand : 10 * (2 * S) ^ 3 ≤ 80 * S ^ 3 := by
    ring_nf
    exact le_rfl
  calc
    knapsackBinaryStructuredEncodedType.inputSize (exactCoverBaseDigitMap I)
        ≤ 10 * (S + 1) ^ 3 := by simpa [S] using hSucc
    _ ≤ 10 * (2 * S) ^ 3 := Nat.mul_le_mul_left 10 hPow
    _ ≤ 80 * S ^ 3 := hExpand
    _ ≤ 80 * S ^ 3 + 10 := by omega

theorem exactCoverToKnapsackBaseDigitBinaryStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : ExactCoverInput => exactCoverStructuredEncodedType.inputSize I)
      (fun K : KnapsackInput => knapsackBinaryStructuredEncodedType.inputSize K)
      exactCoverBaseDigitMap := by
  refine PolynomialSizeBound.intro_with 3 80 10 ?_
  intro I
  exact exactCoverBaseDigitMap_binaryStructured_inputSize_le_source_poly I

/-- Costed Karp reduction from 0-1 Integer Programming to Knapsack. -/
noncomputable def zeroOneIPToKnapsackTMBackedKarpReduction :
    TMBackedCostedReduction zeroOneIntegerProgrammingDecisionProblem
      knapsackKarpDecisionProblem := by
  simpa [knapsackKarpDecisionProblem, knapsackDecisionProblem, knapsackEncodedType] using
    rawCodomainTMBackedReduction
      zeroOneIntegerProgrammingDecisionProblem
      Combinatorics.Knapsack
      map
      map_correct

/-- Costed Karp reduction from 0-1 Integer Programming to Knapsack. -/
noncomputable def zeroOneIPToKnapsackKarpReduction :
    KarpReductionM CostedPolyTimeModel zeroOneIntegerProgrammingDecisionProblem
      knapsackKarpDecisionProblem :=
  zeroOneIPToKnapsackTMBackedKarpReduction.toCostedKarpReduction

/-- Costed P15m candidate-assignment violation-digit Karp reduction to Knapsack. -/
noncomputable def zeroOneIPToKnapsack_textbookTMBackedKarpReduction :
    TMBackedCostedReduction zeroOneIntegerProgrammingDecisionProblem
      knapsackKarpDecisionProblem := by
  simpa [knapsackKarpDecisionProblem, knapsackDecisionProblem, knapsackEncodedType] using
    rawCodomainTMBackedReduction
      zeroOneIntegerProgrammingDecisionProblem
      Combinatorics.Knapsack
      textbookMap
      textbookMap_correct

/-- Costed P15m candidate-assignment violation-digit Karp reduction to Knapsack. -/
noncomputable def zeroOneIPToKnapsack_textbookKarpReduction :
    KarpReductionM CostedPolyTimeModel zeroOneIntegerProgrammingDecisionProblem
      knapsackKarpDecisionProblem :=
  zeroOneIPToKnapsack_textbookTMBackedKarpReduction.toCostedKarpReduction

/-- Costed alternate base-digit Karp reduction from Exact Cover to Knapsack. -/
noncomputable def exactCoverToKnapsack_baseDigitTMBackedKarpReduction :
    TMBackedCostedReduction exactCoverDecisionProblem knapsackKarpDecisionProblem := by
  simpa [knapsackKarpDecisionProblem, knapsackDecisionProblem, knapsackEncodedType] using
    rawCodomainTMBackedReduction
      exactCoverDecisionProblem
      Combinatorics.Knapsack
      exactCoverBaseDigitMap
      exactCoverBaseDigitMap_correct

/-- Costed alternate base-digit Karp reduction from Exact Cover to Knapsack. -/
noncomputable def exactCoverToKnapsack_baseDigitKarpReduction :
    KarpReductionM CostedPolyTimeModel exactCoverDecisionProblem knapsackKarpDecisionProblem :=
  exactCoverToKnapsack_baseDigitTMBackedKarpReduction.toCostedKarpReduction

noncomputable def exactCoverToKnapsackBaseDigitBinaryStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      exactCoverStructuredDecisionProblem
      knapsackBinaryStructuredDecisionProblem where
  f :=
    { toFun := exactCoverBaseDigitMap
      polytime :=
        CostedPolyTimeMap.of_costed
          (CostedMap.of_encodedPolynomialSizeBound
            exactCoverToKnapsackBaseDigitBinaryStructured_polynomialSizeBound) }
  correct := by
    intro I
    simpa [exactCoverStructuredDecisionProblem, knapsackBinaryStructuredDecisionProblem]
      using exactCoverBaseDigitMap_correct I

noncomputable def zeroOneIPToKnapsackBinaryStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      zeroOneIntegerProgrammingBinaryStructuredDecisionProblem
      knapsackBinaryStructuredDecisionProblem :=
  zeroOneIPToKnapsackBinaryStructuredTMBackedKarpReduction.toCostedKarpReduction

theorem knapsackStructuredEncoding_faithful :
    knapsackStructuredDecisionProblem.FaithfulEncoding where
  injective := knapsackStructuredEncodedType_encode_injective

theorem knapsackStructuredEncoding_predicateRespects :
    knapsackStructuredDecisionProblem.PredicateRespectsEncoding :=
  knapsackStructuredEncoding_faithful.predicateRespects

theorem knapsackStructuredEncoding_accepts_encode_iff (I : KnapsackInput) :
    knapsackStructuredDecisionProblem.toEncodedLanguage.accepts
        (knapsackStructuredEncodedType.encode I) ↔
      Combinatorics.Knapsack I :=
  knapsackStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

theorem knapsackBinaryStructuredEncoding_faithful :
    knapsackBinaryStructuredDecisionProblem.FaithfulEncoding where
  injective := knapsackBinaryStructuredEncodedType_encode_injective

theorem knapsackBinaryStructuredEncoding_predicateRespects :
    knapsackBinaryStructuredDecisionProblem.PredicateRespectsEncoding :=
  knapsackBinaryStructuredEncoding_faithful.predicateRespects

theorem knapsackBinaryStructuredEncoding_accepts_encode_iff (I : KnapsackInput) :
    knapsackBinaryStructuredDecisionProblem.toEncodedLanguage.accepts
        (knapsackBinaryStructuredEncodedType.encode I) ↔
      Combinatorics.Knapsack I :=
  knapsackBinaryStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

/-- Knapsack is locally in NP for the project-local costed model. -/
theorem knapsackInNP :
    InNPEnc CostedPolyTimeModel knapsackKarpDecisionProblem :=
  decidableInNP knapsackKarpDecisionProblem

/-- Local NP-completeness of Knapsack via 0-1 Integer Programming. -/
theorem knapsackNPComplete :
    NPCompleteEnc CostedPolyTimeModel knapsackKarpDecisionProblem :=
  NPCompleteEnc.transfer
    ZeroOneIP.zeroOneIPNPComplete
    ⟨zeroOneIPToKnapsackKarpReduction⟩
    knapsackInNP

/-- Local NP-completeness of Knapsack via the P15m violation-digit route. -/
theorem knapsack_textbookNPComplete :
    NPCompleteEnc CostedPolyTimeModel knapsackKarpDecisionProblem :=
  NPCompleteEnc.transfer
    ZeroOneIP.zeroOneIPNPComplete
    ⟨zeroOneIPToKnapsack_textbookKarpReduction⟩
    knapsackInNP

/-- Alternate local NP-completeness proof via Karp's Exact Cover base-digit route. -/
theorem knapsack_exactCoverBaseDigitNPComplete :
    NPCompleteEnc CostedPolyTimeModel knapsackKarpDecisionProblem :=
  NPCompleteEnc.transfer
    ExactCover.exactCover_textbookNPComplete
    ⟨exactCoverToKnapsack_baseDigitKarpReduction⟩
    knapsackInNP

end Knapsack
end Karp21
end ComplexityReduction
