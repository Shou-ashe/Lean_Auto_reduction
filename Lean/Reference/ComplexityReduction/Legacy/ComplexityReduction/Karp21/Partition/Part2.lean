import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.Part1

namespace ComplexityReduction
namespace Karp21
namespace Partition
open ComplexityReduction.Combinatorics

theorem boundedSlackPrefixSum_le_budget (budget : Nat) :
    boundedSlackPrefixSum budget ≤ budget := by
  unfold boundedSlackPrefixSum
  have hpow := boundedSlackPrefixPow_le_succ budget
  omega

theorem boundedSlackRemainder_le_prefixPow (budget : Nat) :
    boundedSlackRemainder budget ≤ 2 ^ boundedSlackPrefixLength budget := by
  unfold boundedSlackRemainder boundedSlackPrefixSum
  have hnext := budget_succ_lt_next_prefixPow budget
  rw [Nat.pow_succ'] at hnext
  omega

theorem boundedSlackPowers_sum (budget : Nat) :
    (boundedSlackPowers budget).sum = budget := by
  have hPrefixSum :
      (Knapsack.compactBinaryPowers (boundedSlackPrefixLength budget)).sum =
        boundedSlackPrefixSum budget := by
    simp [boundedSlackPrefixSum, compactBinaryPowers_sum]
  have hPrefixLe := boundedSlackPrefixSum_le_budget budget
  by_cases hrem : boundedSlackRemainder budget = 0
  · have hBudgetEq : boundedSlackPrefixSum budget = budget := by
      have hSplit : boundedSlackPrefixSum budget + boundedSlackRemainder budget = budget := by
        unfold boundedSlackRemainder
        exact Nat.add_sub_of_le hPrefixLe
      omega
    simp [boundedSlackPowers, hrem, hPrefixSum, hBudgetEq]
  · have hBudgetEq : boundedSlackPrefixSum budget + boundedSlackRemainder budget = budget := by
      unfold boundedSlackRemainder
      exact Nat.add_sub_of_le hPrefixLe
    calc
      (boundedSlackPowers budget).sum =
          (Knapsack.compactBinaryPowers (boundedSlackPrefixLength budget) ++
              [boundedSlackRemainder budget]).sum := by
        simp [boundedSlackPowers, hrem]
      _ = boundedSlackPrefixSum budget + boundedSlackRemainder budget := by
        simp [hPrefixSum]
      _ = budget := hBudgetEq

theorem boundedSlackPowers_length_le_size_succ (budget : Nat) :
    (boundedSlackPowers budget).length ≤ Nat.size budget + 1 := by
  unfold boundedSlackPowers
  let pref := Knapsack.compactBinaryPowers (boundedSlackPrefixLength budget)
  let remainder := boundedSlackRemainder budget
  have hPrefixLen : pref.length = boundedSlackPrefixLength budget := by
    simp [pref, Knapsack.compactBinaryPowers_length]
  have hLen :
      (if remainder = 0 then pref else pref ++ [remainder]).length ≤
        boundedSlackPrefixLength budget + 1 := by
    by_cases hrem : remainder = 0 <;> simp [hrem, hPrefixLen]
  have hSizeSucc : Nat.size (budget + 1) ≤ Nat.size budget + 1 := by
    apply Nat.size_le.2
    have hlt := Nat.lt_size_self budget
    have hle : budget + 1 ≤ 2 ^ Nat.size budget := by omega
    have hpow : 2 ^ Nat.size budget < 2 ^ (Nat.size budget + 1) := by
      rw [Nat.pow_succ']
      have hpos : 0 < 2 ^ Nat.size budget := Nat.pow_pos (by decide : 0 < 2)
      omega
    exact lt_of_le_of_lt hle hpow
  calc
    (if remainder = 0 then pref else pref ++ [remainder]).length
        ≤ boundedSlackPrefixLength budget + 1 := hLen
    _ = Nat.size (budget + 1) := boundedSlackPrefixLength_add_one budget
    _ ≤ Nat.size budget + 1 := hSizeSucc

theorem boundedSlackPowers_length_le_binary_inputSize_succ (budget : Nat) :
    (boundedSlackPowers budget).length ≤ EncodedType.binaryNat.inputSize budget + 1 := by
  simpa [binaryNat_inputSize_eq_size] using boundedSlackPowers_length_le_size_succ budget

theorem boundedSlackPowers_representable {budget slack : Nat} (hSlack : slack ≤ budget) :
    ∃ bits : List Bool,
      bits.length = (boundedSlackPowers budget).length ∧
        chosenSum (boundedSlackPowers budget) bits = slack := by
  let pref := Knapsack.compactBinaryPowers (boundedSlackPrefixLength budget)
  have hPrefixSum :
      pref.sum = boundedSlackPrefixSum budget := by
    simp [pref, boundedSlackPrefixSum, compactBinaryPowers_sum]
  have hPrefixLe := boundedSlackPrefixSum_le_budget budget
  have hPrefixPow :
      boundedSlackPrefixSum budget + 1 = 2 ^ boundedSlackPrefixLength budget := by
    unfold boundedSlackPrefixSum
    have hpow : 0 < 2 ^ boundedSlackPrefixLength budget := Nat.pow_pos (by decide : 0 < 2)
    omega
  by_cases hrem : boundedSlackRemainder budget = 0
  · let bits := (Nat.digitsAppend 2 (boundedSlackPrefixLength budget) slack).map fun digit =>
      decide (digit = 1)
    have hBudgetEq : budget = boundedSlackPrefixSum budget := by
      simp [boundedSlackRemainder] at hrem
      omega
    have hSlackPow : slack < 2 ^ boundedSlackPrefixLength budget := by
      rw [← hPrefixPow]
      omega
    refine ⟨bits, ?_, ?_⟩
    · have hBitsLen : bits.length = pref.length := by
        simp [bits, pref, Knapsack.compactBinaryPowers_length]
        exact Nat.length_digitsAppend (by decide : 1 < 2)
          (boundedSlackPrefixLength budget) hSlackPow
      simpa [boundedSlackPowers, hrem, bits, pref] using hBitsLen
    · have hPrefixSelected : chosenSum pref bits = slack := by
        simpa [bits, pref] using chosenSum_compactBinaryPowers_digitsAppend hSlackPow
      simpa [boundedSlackPowers, hrem, bits, pref] using hPrefixSelected
  · by_cases hSmall : slack < 2 ^ boundedSlackPrefixLength budget
    · let bitsPrefix :=
        (Nat.digitsAppend 2 (boundedSlackPrefixLength budget) slack).map fun digit =>
          decide (digit = 1)
      refine ⟨bitsPrefix ++ [false], ?_, ?_⟩
      · have hBitsLen : bitsPrefix.length = pref.length := by
          simp [bitsPrefix, pref, Knapsack.compactBinaryPowers_length]
          exact Nat.length_digitsAppend (by decide : 1 < 2)
            (boundedSlackPrefixLength budget) hSmall
        simpa [boundedSlackPowers, hrem, pref, bitsPrefix] using hBitsLen
      · have hLen :
            bitsPrefix.length = pref.length := by
          simp [bitsPrefix, pref, Knapsack.compactBinaryPowers_length]
          exact Nat.length_digitsAppend (by decide : 1 < 2)
            (boundedSlackPrefixLength budget) hSmall
        have hPrefixSelected : chosenSum pref bitsPrefix = slack := by
          simpa [bitsPrefix, pref] using chosenSum_compactBinaryPowers_digitsAppend hSmall
        have hAppend :
            chosenSum (pref ++ [boundedSlackRemainder budget]) (bitsPrefix ++ [false]) =
              slack := by
          rw [chosenSum_append hLen]
          simp [chosenSum, hPrefixSelected]
        simpa [boundedSlackPowers, hrem, pref] using hAppend
    · let adjusted := slack - boundedSlackRemainder budget
      have hRemainderLe : boundedSlackRemainder budget ≤ 2 ^ boundedSlackPrefixLength budget :=
        boundedSlackRemainder_le_prefixPow budget
      have hRemainderLeSlack : boundedSlackRemainder budget ≤ slack := by
        have hSlackGe : 2 ^ boundedSlackPrefixLength budget ≤ slack := by omega
        exact hRemainderLe.trans hSlackGe
      have hAdjustedPow : adjusted < 2 ^ boundedSlackPrefixLength budget := by
        have hBudgetEq :
            budget = boundedSlackPrefixSum budget + boundedSlackRemainder budget := by
          simp [boundedSlackRemainder]
          omega
        have hAdjustedLe : adjusted ≤ boundedSlackPrefixSum budget := by
          simp [adjusted]
          omega
        rw [← hPrefixPow]
        omega
      let bitsPrefix :=
        (Nat.digitsAppend 2 (boundedSlackPrefixLength budget) adjusted).map fun digit =>
          decide (digit = 1)
      refine ⟨bitsPrefix ++ [true], ?_, ?_⟩
      · have hBitsLen : bitsPrefix.length = pref.length := by
          simp [bitsPrefix, pref, Knapsack.compactBinaryPowers_length]
          exact Nat.length_digitsAppend (by decide : 1 < 2)
            (boundedSlackPrefixLength budget) hAdjustedPow
        simpa [boundedSlackPowers, hrem, pref, bitsPrefix] using hBitsLen
      · have hLen :
            bitsPrefix.length = pref.length := by
          simp [bitsPrefix, pref, Knapsack.compactBinaryPowers_length]
          exact Nat.length_digitsAppend (by decide : 1 < 2)
            (boundedSlackPrefixLength budget) hAdjustedPow
        have hPrefixSelected : chosenSum pref bitsPrefix = adjusted := by
          simpa [bitsPrefix, pref] using chosenSum_compactBinaryPowers_digitsAppend hAdjustedPow
        have hAppend :
            chosenSum (pref ++ [boundedSlackRemainder budget]) (bitsPrefix ++ [true]) =
              slack := by
          rw [chosenSum_append hLen]
          simp [chosenSum, hPrefixSelected, adjusted]
          omega
        simpa [boundedSlackPowers, hrem, pref] using hAppend

/-- Base for the compact binary-numeric exact-sum encoding. -/
def compactPartitionBase (I : KnapsackInput) : Nat :=
  valueTargetLevel I + valueSlackBudget I + 1

def compactWeightSlackWeights (I : KnapsackInput) : List Nat :=
  (boundedSlackPowers I.capacity).map fun power => compactPartitionBase I * power

def compactValueSlackWeights (I : KnapsackInput) : List Nat :=
  boundedSlackPowers (valueSlackBudget I)

/-- Exact-sum weights for the compact binary-numeric Knapsack-to-Partition route. -/
def compactKnapsackSubsetWeights (I : KnapsackInput) : List Nat :=
  encodedItems (compactPartitionBase I) I.items ++
    compactWeightSlackWeights I ++ compactValueSlackWeights I

def compactKnapsackSubsetTarget (I : KnapsackInput) : Nat :=
  compactPartitionBase I * I.capacity + valueTargetLevel I

def compactTextbookMap (I : KnapsackInput) : PartitionInput :=
  { weights := subsetToPartitionWeights
      (compactKnapsackSubsetWeights I) (compactKnapsackSubsetTarget I) }

def compactSubsetWeightSlackBits (I : KnapsackInput) (bits : List Bool) : List Bool :=
  (bits.drop I.items.length).take (boundedSlackPowers I.capacity).length

def compactSubsetValueSlackBits (I : KnapsackInput) (bits : List Bool) : List Bool :=
  (bits.drop I.items.length).drop (boundedSlackPowers I.capacity).length

theorem chosenSum_map_mul_left (a : Nat) (weights : List Nat) (bits : List Bool) :
    chosenSum (weights.map fun weight => a * weight) bits =
      a * chosenSum weights bits := by
  induction weights generalizing bits with
  | nil =>
      simp [chosenSum]
  | cons weight weights ih =>
      cases bits with
      | nil =>
          simp [chosenSum]
      | cons bit bits =>
          cases bit <;> simp [chosenSum, ih bits, Nat.mul_add]

theorem chosenSum_compactKnapsackSubsetWeights_eq (I : KnapsackInput) {bits : List Bool}
    (hLen : bits.length = (compactKnapsackSubsetWeights I).length) :
    chosenSum (compactKnapsackSubsetWeights I) bits =
      compactPartitionBase I *
          (selectedWeight I (subsetItemBits I bits) +
            chosenSum (boundedSlackPowers I.capacity)
              (compactSubsetWeightSlackBits I bits)) +
        (selectedValue I (subsetItemBits I bits) +
          chosenSum (boundedSlackPowers (valueSlackBudget I))
            (compactSubsetValueSlackBits I bits)) := by
  let itemBits := subsetItemBits I bits
  let rest := bits.drop I.items.length
  let weightBits := compactSubsetWeightSlackBits I bits
  let valueBits := compactSubsetValueSlackBits I bits
  have hBitsLen :
      bits.length =
        I.items.length + (boundedSlackPowers I.capacity).length +
          (boundedSlackPowers (valueSlackBudget I)).length := by
    simpa [compactKnapsackSubsetWeights, encodedItems, compactWeightSlackWeights,
      compactValueSlackWeights, Nat.add_assoc] using hLen
  have hItemLen : itemBits.length = I.items.length := by
    have hTake : I.items.length ≤ bits.length := by omega
    simp [itemBits, subsetItemBits, hTake]
  have hRestLen :
      rest.length =
        (boundedSlackPowers I.capacity).length +
          (boundedSlackPowers (valueSlackBudget I)).length := by
    simp [rest, hBitsLen]
    omega
  have hWeightLen : weightBits.length = (boundedSlackPowers I.capacity).length := by
    unfold weightBits compactSubsetWeightSlackBits
    rw [List.length_take]
    apply Nat.min_eq_left
    simp [hBitsLen]
    omega
  have hValueLen :
      valueBits.length = (boundedSlackPowers (valueSlackBudget I)).length := by
    simp [valueBits, compactSubsetValueSlackBits]
    omega
  have hRestSplit : rest = weightBits ++ valueBits := by
    simp [weightBits, valueBits, compactSubsetWeightSlackBits,
      compactSubsetValueSlackBits, rest]
  have hSplit : bits = itemBits ++ (weightBits ++ valueBits) := by
    calc
      bits = itemBits ++ rest := by
        simp [itemBits, rest, subsetItemBits]
      _ = itemBits ++ (weightBits ++ valueBits) := by rw [hRestSplit]
  change chosenSum (compactKnapsackSubsetWeights I) bits =
      compactPartitionBase I *
          (selectedWeight I itemBits +
            chosenSum (boundedSlackPowers I.capacity) weightBits) +
        (selectedValue I itemBits +
          chosenSum (boundedSlackPowers (valueSlackBudget I)) valueBits)
  rw [hSplit]
  simp [compactKnapsackSubsetWeights, compactWeightSlackWeights,
    compactValueSlackWeights, itemBits, weightBits, valueBits]
  have hItemLenEncoded :
      itemBits.length = (encodedItems (compactPartitionBase I) I.items).length := by
    simpa [encodedItems] using hItemLen
  rw [chosenSum_append hItemLenEncoded]
  have hWeightLenEncoded :
      weightBits.length =
        (List.map (fun power => compactPartitionBase I * power)
          (boundedSlackPowers I.capacity)).length := by
    simpa using hWeightLen
  rw [chosenSum_append hWeightLenEncoded]
  rw [chosenSum_encodedItems]
  rw [chosenSum_map_mul_left]
  have hItemBitsDef : subsetItemBits I bits = itemBits := rfl
  have hWeightBitsDef : compactSubsetWeightSlackBits I bits = weightBits := rfl
  have hValueBitsDef : compactSubsetValueSlackBits I bits = valueBits := rfl
  simp [hItemBitsDef, hWeightBitsDef, hValueBitsDef, selectedWeight, selectedValue,
    itemOnlyKnapsackInput, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem compactPartitionBase_pos (I : KnapsackInput) :
    0 < compactPartitionBase I := by
  unfold compactPartitionBase
  omega

theorem compact_knapsack_subsetSum_correct (I : KnapsackInput) :
    Combinatorics.Knapsack I ↔
      SubsetSum (compactKnapsackSubsetWeights I) (compactKnapsackSubsetTarget I) := by
  constructor
  · rintro ⟨selected, hSelectedLen, hWeight, hValue⟩
    let weightSlack := I.capacity - selectedWeight I selected
    let valueSlack := valueTargetLevel I - selectedValue I selected
    have hWeightSlackLe : weightSlack ≤ I.capacity := by omega
    have hSelectedValueLeLevel : selectedValue I selected ≤ valueTargetLevel I := by
      exact (selectedValue_le_itemValueTotal_input I selected).trans
        (itemValueTotal_le_valueTargetLevel I)
    have hValueSlackLe : valueSlack ≤ valueSlackBudget I := by
      simp [valueSlack, valueSlackBudget]
      omega
    rcases boundedSlackPowers_representable hWeightSlackLe with
      ⟨weightBits, hWeightBitsLen, hWeightBitsSum⟩
    rcases boundedSlackPowers_representable hValueSlackLe with
      ⟨valueBits, hValueBitsLen, hValueBitsSum⟩
    let bits := selected ++ weightBits ++ valueBits
    refine ⟨bits, ?_, ?_⟩
    · simp [bits, compactKnapsackSubsetWeights, encodedItems, compactWeightSlackWeights,
        compactValueSlackWeights, hSelectedLen, hWeightBitsLen, hValueBitsLen]
    · unfold bits
      rw [compactKnapsackSubsetWeights]
      rw [List.append_assoc (encodedItems (compactPartitionBase I) I.items)
        (compactWeightSlackWeights I) (compactValueSlackWeights I)]
      rw [List.append_assoc selected weightBits valueBits]
      have hSelectedLenEncoded :
          selected.length = (encodedItems (compactPartitionBase I) I.items).length := by
        simpa [encodedItems] using hSelectedLen
      rw [chosenSum_append hSelectedLenEncoded]
      have hWeightPrefixLen :
          weightBits.length = (compactWeightSlackWeights I).length := by
        simpa [compactWeightSlackWeights] using hWeightBitsLen
      rw [chosenSum_append hWeightPrefixLen]
      rw [chosenSum_encodedItems]
      rw [compactWeightSlackWeights, chosenSum_map_mul_left]
      rw [compactValueSlackWeights]
      rw [hWeightBitsSum, hValueBitsSum]
      simp [compactKnapsackSubsetTarget, selectedWeight_itemOnly, selectedValue_itemOnly,
        weightSlack, valueSlack, Nat.add_assoc, Nat.add_comm]
      have hWeightEq :
          selectedWeight I selected + (I.capacity - selectedWeight I selected) =
            I.capacity :=
        Nat.add_sub_of_le hWeight
      have hValueEq :
          selectedValue I selected + (valueTargetLevel I - selectedValue I selected) =
            valueTargetLevel I :=
        Nat.add_sub_of_le hSelectedValueLeLevel
      nlinarith [hWeightEq, hValueEq]
  · rintro ⟨bits, hLen, hSum⟩
    let itemBits := subsetItemBits I bits
    let weightBits := compactSubsetWeightSlackBits I bits
    let valueBits := compactSubsetValueSlackBits I bits
    have hBitsLen :
        bits.length =
          I.items.length + (boundedSlackPowers I.capacity).length +
            (boundedSlackPowers (valueSlackBudget I)).length := by
      simpa [compactKnapsackSubsetWeights, encodedItems, compactWeightSlackWeights,
        compactValueSlackWeights, Nat.add_assoc] using hLen
    have hItemLen : itemBits.length = I.items.length := by
      have hTake : I.items.length ≤ bits.length := by omega
      simp [itemBits, subsetItemBits, hTake]
    have hEqRaw := (chosenSum_compactKnapsackSubsetWeights_eq I hLen).symm.trans hSum
    have hEq :
        compactPartitionBase I *
            (selectedWeight I itemBits +
              chosenSum (boundedSlackPowers I.capacity) weightBits) +
          (selectedValue I itemBits +
            chosenSum (boundedSlackPowers (valueSlackBudget I)) valueBits) =
            compactPartitionBase I * I.capacity + valueTargetLevel I := by
      simpa [itemBits, weightBits, valueBits, compactKnapsackSubsetTarget] using hEqRaw
    have hValueLeLevel : selectedValue I itemBits ≤ valueTargetLevel I := by
      exact (selectedValue_le_itemValueTotal_input I itemBits).trans
        (itemValueTotal_le_valueTargetLevel I)
    have hVsLeBudget :
        chosenSum (boundedSlackPowers (valueSlackBudget I)) valueBits ≤ valueSlackBudget I := by
      have hChosen :=
        chosenSum_le_sum (boundedSlackPowers (valueSlackBudget I)) valueBits
      simpa [boundedSlackPowers_sum] using hChosen
    have hLowBound :
        selectedValue I itemBits +
            chosenSum (boundedSlackPowers (valueSlackBudget I)) valueBits <
          compactPartitionBase I := by
      unfold compactPartitionBase
      omega
    have hTargetLowBound : valueTargetLevel I < compactPartitionBase I := by
      unfold compactPartitionBase
      omega
    rcases noCarry_pair_eq (compactPartitionBase_pos I) hLowBound hTargetLowBound hEq with
      ⟨hLowEq, hHighEq⟩
    have hWeightBound : selectedWeight I itemBits ≤ I.capacity := by
      omega
    have hValueBound : I.targetValue ≤ selectedValue I itemBits := by
      let valueSlackChosen :=
        chosenSum (boundedSlackPowers (valueSlackBudget I)) valueBits
      have hLowEq' :
          selectedValue I itemBits + valueSlackChosen = valueTargetLevel I := by
        simpa [valueSlackChosen, valueBits] using hLowEq
      have hVsLeBudget' :
          valueSlackChosen ≤ valueTargetLevel I - I.targetValue := by
        have hVsLeBudget'' : valueSlackChosen ≤ valueSlackBudget I := by
          simpa [valueSlackChosen] using hVsLeBudget
        simpa [valueSlackBudget] using hVsLeBudget''
      have hTargetLeLevel := targetValue_le_valueTargetLevel I
      omega
    exact ⟨itemBits, hItemLen, hWeightBound, hValueBound⟩

theorem compactTextbookMap_correct (I : KnapsackInput) :
    knapsackKarpDecisionProblem.isYes I ↔ Partition (compactTextbookMap I) := by
  change Combinatorics.Knapsack I ↔ Partition (compactTextbookMap I)
  rw [compact_knapsack_subsetSum_correct I]
  simpa [compactTextbookMap] using
    subsetToPartition_correct (compactKnapsackSubsetWeights I) (compactKnapsackSubsetTarget I)

/-! ### Binary-structured size bound for the compact route -/

theorem nat_le_two_pow_self (n : Nat) :
    n ≤ 2 ^ n :=
  Nat.le_of_lt n.lt_two_pow_self

theorem mul_two_pow_self_le_two_pow_two_mul (n : Nat) :
    n * 2 ^ n ≤ 2 ^ (2 * n) := by
  calc
    n * 2 ^ n ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul_right (2 ^ n) (nat_le_two_pow_self n)
    _ = 2 ^ (n + n) := by rw [← Nat.pow_add]
    _ = 2 ^ (2 * n) := by ring_nf

theorem natList_sum_le_length_mul_bound {xs : List Nat} {B : Nat}
    (hB : ∀ x ∈ xs, x ≤ B) :
    xs.sum ≤ xs.length * B := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : x ≤ B := hB x (by simp)
      have htail : ∀ y ∈ xs, y ≤ B := by
        intro y hy
        exact hB y (by simp [hy])
      have ih' := ih htail
      calc
        (x :: xs).sum = x + xs.sum := by simp
        _ ≤ B + xs.length * B := Nat.add_le_add hx ih'
        _ = (x :: xs).length * B := by
          simp [Nat.succ_mul, Nat.add_comm]

theorem list_mem_le_sum {x : Nat} {xs : List Nat} (hx : x ∈ xs) :
    x ≤ xs.sum := by
  induction xs with
  | nil =>
      simp at hx
  | cons y ys ih =>
      simp at hx
      rcases hx with rfl | hx
      · simp
      · exact (ih hx).trans (Nat.le_add_left ys.sum y)

theorem mul_le_two_pow_add_of_le {a b A B : Nat}
    (ha : a ≤ 2 ^ A) (hb : b ≤ 2 ^ B) :
    a * b ≤ 2 ^ (A + B) := by
  calc
    a * b ≤ 2 ^ A * 2 ^ B := Nat.mul_le_mul ha hb
    _ = 2 ^ (A + B) := by rw [← Nat.pow_add]

theorem add_lt_two_pow_add_two_of_le {a b M : Nat}
    (ha : a ≤ 2 ^ M) (hb : b ≤ 2 ^ M) :
    a + b < 2 ^ (M + 2) := by
  have hsum : a + b ≤ 2 ^ M + 2 ^ M := Nat.add_le_add ha hb
  have hlt : 2 ^ M + 2 ^ M < 2 ^ (M + 2) := by
    rw [show M + 2 = M + 1 + 1 by omega, Nat.pow_succ]
    rw [show M + 1 = M + 1 by rfl, Nat.pow_succ]
    have hpos : 0 < 2 ^ M := Nat.pow_pos (by decide : 0 < 2)
    omega
  exact lt_of_le_of_lt hsum hlt

theorem partitionWeightsBinaryStructured_inputSize_eq (weights : List Nat) :
    partitionWeightsBinaryStructuredEncodedType.inputSize weights =
      (weights.map EncodedType.binaryNat.inputSize).sum + weights.length := by
  induction weights with
  | nil =>
      exact EncodedType.inputSize_list_nil EncodedType.binaryNat
  | cons w ws ih =>
      calc
        partitionWeightsBinaryStructuredEncodedType.inputSize (w :: ws)
            = EncodedType.binaryNat.inputSize w + 1 +
                partitionWeightsBinaryStructuredEncodedType.inputSize ws := by
              exact EncodedType.inputSize_list_cons EncodedType.binaryNat w ws
        _ = EncodedType.binaryNat.inputSize w + 1 +
              ((ws.map EncodedType.binaryNat.inputSize).sum + ws.length) := by
              rw [ih]
        _ = ((w :: ws).map EncodedType.binaryNat.inputSize).sum +
              (w :: ws).length := by
              have hMapSum :
                  ((w :: ws).map EncodedType.binaryNat.inputSize).sum =
                    EncodedType.binaryNat.inputSize w +
                      (ws.map EncodedType.binaryNat.inputSize).sum := by
                rfl
              have hLen : (w :: ws).length = ws.length + 1 := by simp
              rw [hMapSum, hLen]
              omega

theorem partitionBinaryStructured_inputSize_eq (I : PartitionInput) :
    partitionBinaryStructuredEncodedType.inputSize I =
      (I.weights.map EncodedType.binaryNat.inputSize).sum + I.weights.length := by
  simpa [partitionBinaryStructuredEncodedType] using
    partitionWeightsBinaryStructured_inputSize_eq I.weights

theorem knapsackItemListBinaryStructured_inputSize_le_source (I : KnapsackInput) :
    knapsackItemListBinaryStructuredEncodedType.inputSize I.items ≤
      knapsackBinaryStructuredEncodedType.inputSize I := by
  rw [Knapsack.knapsackBinaryStructured_inputSize_eq]
  omega

theorem knapsackItems_length_le_binaryStructured_inputSize (I : KnapsackInput) :
    I.items.length ≤ knapsackBinaryStructuredEncodedType.inputSize I := by
  have hList :=
    Knapsack.encodedList_length_le_inputSize knapsackItemBinaryStructuredEncodedType I.items
  exact hList.trans (knapsackItemListBinaryStructured_inputSize_le_source I)

theorem knapsackItemBinaryStructured_inputSize_le_source {I : KnapsackInput}
    {item : Nat × Nat} (hitem : item ∈ I.items) :
    knapsackItemBinaryStructuredEncodedType.inputSize item ≤
      knapsackBinaryStructuredEncodedType.inputSize I := by
  have hElement :=
    Knapsack.encodedList_element_inputSize_le knapsackItemBinaryStructuredEncodedType hitem
  exact hElement.trans (knapsackItemListBinaryStructured_inputSize_le_source I)

theorem knapsackItem_weight_lt_two_pow_sourceSucc {I : KnapsackInput}
    {item : Nat × Nat} (hitem : item ∈ I.items) :
    item.1 < 2 ^ (knapsackBinaryStructuredEncodedType.inputSize I + 1) := by
  have hSource := knapsackItemBinaryStructured_inputSize_le_source hitem
  have hWeightSize :
      EncodedType.binaryNat.inputSize item.1 ≤
        knapsackItemBinaryStructuredEncodedType.inputSize item := by
    rcases item with ⟨w, v⟩
    simp [knapsackItemBinaryStructuredEncodedType]
    omega
  have hSize :
      EncodedType.binaryNat.inputSize item.1 ≤
        knapsackBinaryStructuredEncodedType.inputSize I + 1 := by
    omega
  exact (Knapsack.binaryNat_lt_two_pow_inputSize item.1).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) hSize)

theorem knapsackItem_value_lt_two_pow_sourceSucc {I : KnapsackInput}
    {item : Nat × Nat} (hitem : item ∈ I.items) :
    item.2 < 2 ^ (knapsackBinaryStructuredEncodedType.inputSize I + 1) := by
  have hSource := knapsackItemBinaryStructured_inputSize_le_source hitem
  have hValueSize :
      EncodedType.binaryNat.inputSize item.2 ≤
        knapsackItemBinaryStructuredEncodedType.inputSize item := by
    rcases item with ⟨w, v⟩
    simp [knapsackItemBinaryStructuredEncodedType]
  have hSize :
      EncodedType.binaryNat.inputSize item.2 ≤
        knapsackBinaryStructuredEncodedType.inputSize I + 1 := by
    omega
  exact (Knapsack.binaryNat_lt_two_pow_inputSize item.2).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) hSize)

theorem capacity_lt_two_pow_sourceSucc (I : KnapsackInput) :
    I.capacity < 2 ^ (knapsackBinaryStructuredEncodedType.inputSize I + 1) := by
  have hSize :
      EncodedType.binaryNat.inputSize I.capacity ≤
        knapsackBinaryStructuredEncodedType.inputSize I + 1 := by
    rw [Knapsack.knapsackBinaryStructured_inputSize_eq]
    omega
  exact (Knapsack.binaryNat_lt_two_pow_inputSize I.capacity).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) hSize)

theorem targetValue_lt_two_pow_sourceSucc (I : KnapsackInput) :
    I.targetValue < 2 ^ (knapsackBinaryStructuredEncodedType.inputSize I + 1) := by
  have hSize :
      EncodedType.binaryNat.inputSize I.targetValue ≤
        knapsackBinaryStructuredEncodedType.inputSize I + 1 := by
    rw [Knapsack.knapsackBinaryStructured_inputSize_eq]
    omega
  exact (Knapsack.binaryNat_lt_two_pow_inputSize I.targetValue).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) hSize)

theorem itemValueTotal_le_two_pow_two_mul_sourceSucc (I : KnapsackInput) :
    itemValueTotal I.items ≤
      2 ^ (2 * (knapsackBinaryStructuredEncodedType.inputSize I + 1)) := by
  let T := knapsackBinaryStructuredEncodedType.inputSize I + 1
  have hEach : ∀ v ∈ I.items.map Prod.snd, v ≤ 2 ^ T := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨item, hitem, rfl⟩
    exact Nat.le_of_lt (by simpa [T] using knapsackItem_value_lt_two_pow_sourceSucc hitem)
  have hSum := natList_sum_le_length_mul_bound hEach
  have hLen : (I.items.map Prod.snd).length ≤ T := by
    have hItems := knapsackItems_length_le_binaryStructured_inputSize I
    simp [T]
    omega
  calc
    itemValueTotal I.items = (I.items.map Prod.snd).sum := by rfl
    _ ≤ (I.items.map Prod.snd).length * 2 ^ T := hSum
    _ ≤ T * 2 ^ T := Nat.mul_le_mul_right (2 ^ T) hLen
    _ ≤ 2 ^ (2 * T) := mul_two_pow_self_le_two_pow_two_mul T
    _ = 2 ^ (2 * (knapsackBinaryStructuredEncodedType.inputSize I + 1)) := by rfl

theorem itemWeightTotal_le_two_pow_two_mul_sourceSucc (I : KnapsackInput) :
    itemWeightTotal I.items ≤
      2 ^ (2 * (knapsackBinaryStructuredEncodedType.inputSize I + 1)) := by
  let T := knapsackBinaryStructuredEncodedType.inputSize I + 1
  have hEach : ∀ w ∈ I.items.map Prod.fst, w ≤ 2 ^ T := by
    intro w hw
    rcases List.mem_map.mp hw with ⟨item, hitem, rfl⟩
    exact Nat.le_of_lt (by simpa [T] using knapsackItem_weight_lt_two_pow_sourceSucc hitem)
  have hSum := natList_sum_le_length_mul_bound hEach
  have hLen : (I.items.map Prod.fst).length ≤ T := by
    have hItems := knapsackItems_length_le_binaryStructured_inputSize I
    simp [T]
    omega
  calc
    itemWeightTotal I.items = (I.items.map Prod.fst).sum := by rfl
    _ ≤ (I.items.map Prod.fst).length * 2 ^ T := hSum
    _ ≤ T * 2 ^ T := Nat.mul_le_mul_right (2 ^ T) hLen
    _ ≤ 2 ^ (2 * T) := mul_two_pow_self_le_two_pow_two_mul T
    _ = 2 ^ (2 * (knapsackBinaryStructuredEncodedType.inputSize I + 1)) := by rfl

theorem valueTargetLevel_le_two_pow_two_mul_sourceSucc (I : KnapsackInput) :
    valueTargetLevel I ≤
      2 ^ (2 * (knapsackBinaryStructuredEncodedType.inputSize I + 1)) := by
  let T := knapsackBinaryStructuredEncodedType.inputSize I + 1
  have hValue : itemValueTotal I.items ≤ 2 ^ (2 * T) := by
    simpa [T] using itemValueTotal_le_two_pow_two_mul_sourceSucc I
  have hTarget : I.targetValue ≤ 2 ^ (2 * T) := by
    have hTargetLt : I.targetValue < 2 ^ T := by
      simpa [T] using targetValue_lt_two_pow_sourceSucc I
    exact (Nat.le_of_lt hTargetLt).trans
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  unfold valueTargetLevel
  exact max_le hValue hTarget

theorem valueSlackBudget_le_two_pow_two_mul_sourceSucc (I : KnapsackInput) :
    valueSlackBudget I ≤
      2 ^ (2 * (knapsackBinaryStructuredEncodedType.inputSize I + 1)) :=
  (Nat.sub_le _ _).trans (valueTargetLevel_le_two_pow_two_mul_sourceSucc I)

theorem compactPartitionBase_lt_two_pow_sourceLinear (I : KnapsackInput) :
    compactPartitionBase I <
      2 ^ (2 * (knapsackBinaryStructuredEncodedType.inputSize I + 1) + 2) := by
  let T := knapsackBinaryStructuredEncodedType.inputSize I + 1
  have hLevel : valueTargetLevel I ≤ 2 ^ (2 * T) := by
    simpa [T] using valueTargetLevel_le_two_pow_two_mul_sourceSucc I
  have hSlack : valueSlackBudget I ≤ 2 ^ (2 * T) := by
    simpa [T] using valueSlackBudget_le_two_pow_two_mul_sourceSucc I
  have hBaseLe : compactPartitionBase I ≤ 2 ^ (2 * T) + 2 ^ (2 * T) + 1 := by
    unfold compactPartitionBase
    omega
  have hPow :
      2 ^ (2 * T) + 2 ^ (2 * T) + 1 < 2 ^ (2 * T + 2) := by
    rw [show 2 * T + 2 = 2 * T + 1 + 1 by omega, Nat.pow_succ]
    rw [show 2 * T + 1 = 2 * T + 1 by rfl, Nat.pow_succ]
    have hpos : 0 < 2 ^ (2 * T) := Nat.pow_pos (by decide : 0 < 2)
    omega
  exact lt_of_le_of_lt hBaseLe (by simpa [T] using hPow)

theorem boundedSlackPowers_mem_le_budget {budget power : Nat}
    (hpower : power ∈ boundedSlackPowers budget) :
    power ≤ budget := by
  exact (list_mem_le_sum hpower).trans (by rw [boundedSlackPowers_sum])

theorem valueSlackBudget_binaryNat_inputSize_le_sourceLinear (I : KnapsackInput) :
    EncodedType.binaryNat.inputSize (valueSlackBudget I) ≤
      2 * (knapsackBinaryStructuredEncodedType.inputSize I + 1) + 1 := by
  let T := knapsackBinaryStructuredEncodedType.inputSize I + 1
  have hSlack : valueSlackBudget I ≤ 2 ^ (2 * T) := by
    simpa [T] using valueSlackBudget_le_two_pow_two_mul_sourceSucc I
  have hlt : valueSlackBudget I < 2 ^ (2 * T + 1) := by
    have hPow : 2 ^ (2 * T) < 2 ^ (2 * T + 1) := by
      rw [Nat.pow_succ]
      have hpos : 0 < 2 ^ (2 * T) := Nat.pow_pos (by decide : 0 < 2)
      omega
    exact lt_of_le_of_lt hSlack hPow
  simpa [T] using Knapsack.binaryNat_inputSize_le_of_lt_two_pow hlt

theorem compactKnapsackSubsetWeights_length_le_sourceLinear (I : KnapsackInput) :
    (compactKnapsackSubsetWeights I).length ≤
      4 * (knapsackBinaryStructuredEncodedType.inputSize I + 1) + 2 := by
  let S := knapsackBinaryStructuredEncodedType.inputSize I
  let T := S + 1
  have hItems : I.items.length ≤ S := by
    simpa [S] using knapsackItems_length_le_binaryStructured_inputSize I
  have hCapSize : EncodedType.binaryNat.inputSize I.capacity ≤ S := by
    dsimp [S]
    rw [Knapsack.knapsackBinaryStructured_inputSize_eq]
    omega
  have hCapLen : (boundedSlackPowers I.capacity).length ≤ S + 1 := by
    exact (boundedSlackPowers_length_le_binary_inputSize_succ I.capacity).trans (by omega)
  have hValueSize :
      EncodedType.binaryNat.inputSize (valueSlackBudget I) ≤ 2 * T + 1 := by
    simpa [T, S] using valueSlackBudget_binaryNat_inputSize_le_sourceLinear I
  have hValueLen : (boundedSlackPowers (valueSlackBudget I)).length ≤ 2 * T + 2 := by
    exact (boundedSlackPowers_length_le_binary_inputSize_succ (valueSlackBudget I)).trans
      (by omega)
  simp [compactKnapsackSubsetWeights, compactWeightSlackWeights, compactValueSlackWeights,
    encodedItems]
  omega

theorem compactKnapsackSubsetWeight_mem_lt_two_pow_sourceLinear {I : KnapsackInput}
    {weight : Nat} (hweight : weight ∈ compactKnapsackSubsetWeights I) :
    weight < 2 ^ (4 * (knapsackBinaryStructuredEncodedType.inputSize I + 1) + 4) := by
  let T := knapsackBinaryStructuredEncodedType.inputSize I + 1
  have hBase : compactPartitionBase I < 2 ^ (2 * T + 2) := by
    simpa [T] using compactPartitionBase_lt_two_pow_sourceLinear I
  have hBaseLe : compactPartitionBase I ≤ 2 ^ (2 * T + 2) := Nat.le_of_lt hBase
  simp [compactKnapsackSubsetWeights, compactWeightSlackWeights,
    compactValueSlackWeights] at hweight
  rcases hweight with hitem | hweightSlack | hvalueSlack
  · have hExists :
        ∃ item : (Nat × Nat),
          item ∈ I.items ∧ encodedItem (compactPartitionBase I) item = weight := by
      simpa [encodedItems] using hitem
    rcases hExists with ⟨item, hpair⟩
    rcases hpair with ⟨hmem, hEq⟩
    subst weight
    have hW : item.1 ≤ 2 ^ T := by
      exact Nat.le_of_lt (by simpa [T] using knapsackItem_weight_lt_two_pow_sourceSucc hmem)
    have hVSmall : item.2 < 2 ^ T := by
      simpa [T] using knapsackItem_value_lt_two_pow_sourceSucc hmem
    have hV : item.2 ≤ 2 ^ (3 * T + 2) := by
      exact (Nat.le_of_lt hVSmall).trans
        (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
    have hProd : compactPartitionBase I * item.1 ≤ 2 ^ (3 * T + 2) := by
      exact (mul_le_two_pow_add_of_le hBaseLe hW).trans
        (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
    have hEnc : encodedItem (compactPartitionBase I) item < 2 ^ (3 * T + 4) := by
      simpa [encodedItem] using add_lt_two_pow_add_two_of_le hProd hV
    exact hEnc.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  · rcases hweightSlack with ⟨power, hpower, rfl⟩
    have hPowerLeBudget := boundedSlackPowers_mem_le_budget hpower
    have hCap : I.capacity < 2 ^ T := by
      simpa [T] using capacity_lt_two_pow_sourceSucc I
    have hPower : power ≤ 2 ^ T := hPowerLeBudget.trans (Nat.le_of_lt hCap)
    have hProd : compactPartitionBase I * power ≤ 2 ^ (3 * T + 2) := by
      exact (mul_le_two_pow_add_of_le hBaseLe hPower).trans
        (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
    have hSmall : compactPartitionBase I * power < 2 ^ (3 * T + 3) :=
      lt_of_le_of_lt hProd (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega))
    exact hSmall.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  · have hPowerLeBudget := boundedSlackPowers_mem_le_budget hvalueSlack
    have hBudget : valueSlackBudget I ≤ 2 ^ (2 * T) := by
      simpa [T] using valueSlackBudget_le_two_pow_two_mul_sourceSucc I
    have hPower : weight ≤ 2 ^ (2 * T) := hPowerLeBudget.trans hBudget
    have hSmall : weight < 2 ^ (2 * T + 1) :=
      lt_of_le_of_lt hPower (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega))
    exact hSmall.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))

theorem compactKnapsackSubsetWeights_sum_lt_two_pow_sourceLinear (I : KnapsackInput) :
    (compactKnapsackSubsetWeights I).sum <
      2 ^ (10 * (knapsackBinaryStructuredEncodedType.inputSize I + 1) + 12) := by
  let T := knapsackBinaryStructuredEncodedType.inputSize I + 1
  let B := 4 * T + 4
  have hEach : ∀ weight ∈ compactKnapsackSubsetWeights I, weight ≤ 2 ^ B := by
    intro weight hweight
    exact Nat.le_of_lt (by
      simpa [B, T] using compactKnapsackSubsetWeight_mem_lt_two_pow_sourceLinear hweight)
  have hSum := natList_sum_le_length_mul_bound hEach
  have hLen :
      (compactKnapsackSubsetWeights I).length ≤ 4 * T + 2 := by
    simpa [T] using compactKnapsackSubsetWeights_length_le_sourceLinear I
  have hLenPow : (compactKnapsackSubsetWeights I).length ≤ 2 ^ (5 * T + 4) := by
    have hLinear : (compactKnapsackSubsetWeights I).length ≤ 5 * T + 4 := by omega
    exact hLinear.trans (nat_le_two_pow_self (5 * T + 4))
  have hMul :
      (compactKnapsackSubsetWeights I).length * 2 ^ B ≤
        2 ^ (5 * T + 4) * 2 ^ B :=
    Nat.mul_le_mul_right (2 ^ B) hLenPow
  calc
    (compactKnapsackSubsetWeights I).sum
        ≤ (compactKnapsackSubsetWeights I).length * 2 ^ B := hSum
    _ ≤ 2 ^ (5 * T + 4) * 2 ^ B := hMul
    _ = 2 ^ ((5 * T + 4) + B) := by rw [← Nat.pow_add]
    _ < 2 ^ (10 * T + 12) := by
      apply Nat.pow_lt_pow_right (by decide : 1 < 2)
      dsimp [B]
      omega

theorem compactKnapsackSubsetTarget_lt_two_pow_sourceLinear (I : KnapsackInput) :
    compactKnapsackSubsetTarget I <
      2 ^ (10 * (knapsackBinaryStructuredEncodedType.inputSize I + 1) + 12) := by
  let T := knapsackBinaryStructuredEncodedType.inputSize I + 1
  have hBase : compactPartitionBase I < 2 ^ (2 * T + 2) := by
    simpa [T] using compactPartitionBase_lt_two_pow_sourceLinear I
  have hCap : I.capacity < 2 ^ T := by
    simpa [T] using capacity_lt_two_pow_sourceSucc I
  have hLevel : valueTargetLevel I ≤ 2 ^ (2 * T) := by
    simpa [T] using valueTargetLevel_le_two_pow_two_mul_sourceSucc I
  have hProd : compactPartitionBase I * I.capacity ≤ 2 ^ (3 * T + 2) := by
    have hBaseLe := Nat.le_of_lt hBase
    have hCapLe := Nat.le_of_lt hCap
    exact (mul_le_two_pow_add_of_le hBaseLe hCapLe).trans
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  have hLevel' : valueTargetLevel I ≤ 2 ^ (3 * T + 2) := by
    exact hLevel.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  have hTargetSmall :
      compactPartitionBase I * I.capacity + valueTargetLevel I < 2 ^ (3 * T + 4) :=
    add_lt_two_pow_add_two_of_le hProd hLevel'
  have hExp : 3 * T + 4 ≤ 10 * T + 12 := by omega
  have hTargetSmall' : compactKnapsackSubsetTarget I < 2 ^ (3 * T + 4) := by
    simpa [compactKnapsackSubsetTarget] using hTargetSmall
  exact hTargetSmall'.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) hExp)

theorem compactTextbookMap_weight_binaryNat_inputSize_le {I : KnapsackInput}
    {weight : Nat} (hweight : weight ∈ (compactTextbookMap I).weights) :
    EncodedType.binaryNat.inputSize weight ≤
      16 * (knapsackBinaryStructuredEncodedType.inputSize I + 1) + 16 := by
  let T := knapsackBinaryStructuredEncodedType.inputSize I + 1
  have hSubsetSum := compactKnapsackSubsetWeights_sum_lt_two_pow_sourceLinear I
  have hTarget := compactKnapsackSubsetTarget_lt_two_pow_sourceLinear I
  have hTwoTarget :
      2 * compactKnapsackSubsetTarget I < 2 ^ (10 * T + 13) := by
    have hMul : 2 * compactKnapsackSubsetTarget I < 2 * 2 ^ (10 * T + 12) :=
      mul_lt_mul_of_pos_left (by simpa [T] using hTarget) (by norm_num)
    have hPow : 2 * 2 ^ (10 * T + 12) = 2 ^ (10 * T + 13) := by
      rw [show 10 * T + 13 = 10 * T + 12 + 1 by omega, Nat.pow_succ]
      ring
    simpa [hPow] using hMul
  have hmem :
      weight ∈ subsetToPartitionWeights
        (compactKnapsackSubsetWeights I) (compactKnapsackSubsetTarget I) := by
    simpa [compactTextbookMap] using hweight
  unfold subsetToPartitionWeights at hmem
  rw [List.mem_append] at hmem
  rcases hmem with hsubset | htail
  · have hSmall :=
      compactKnapsackSubsetWeight_mem_lt_two_pow_sourceLinear (I := I) hsubset
    exact Knapsack.binaryNat_inputSize_le_of_lt_two_pow
      (hSmall.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))
  · simp at htail
    rcases htail with hsum | htarget
    · subst weight
      have hSubsetSum' :
          (compactKnapsackSubsetWeights I).sum < 2 ^ (10 * T + 12) := by
        simpa [T] using hSubsetSum
      exact Knapsack.binaryNat_inputSize_le_of_lt_two_pow
        (hSubsetSum'.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))
    · subst weight
      exact Knapsack.binaryNat_inputSize_le_of_lt_two_pow
        (hTwoTarget.trans_le
          (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))

theorem compactTextbookMap_weights_length_le_sourceLinear (I : KnapsackInput) :
    (compactTextbookMap I).weights.length ≤
      4 * (knapsackBinaryStructuredEncodedType.inputSize I + 1) + 4 := by
  have hSubset := compactKnapsackSubsetWeights_length_le_sourceLinear I
  simp [compactTextbookMap, subsetToPartitionWeights]
  omega

theorem partitionBinaryStructured_inputSize_compactTextbookMap_le_knapsack_poly_succ
    (I : KnapsackInput) :
    partitionBinaryStructuredEncodedType.inputSize (compactTextbookMap I) ≤
      1000 * (knapsackBinaryStructuredEncodedType.inputSize I + 1) ^ 2 := by
  let T := knapsackBinaryStructuredEncodedType.inputSize I + 1
  let L := (compactTextbookMap I).weights.length
  let B := 16 * T + 16
  have hLen : L ≤ 4 * T + 4 := by
    simpa [L, T] using compactTextbookMap_weights_length_le_sourceLinear I
  have hEach :
      ∀ size ∈ (compactTextbookMap I).weights.map EncodedType.binaryNat.inputSize,
        size ≤ B := by
    intro size hsize
    rcases List.mem_map.mp hsize with ⟨weight, hweight, rfl⟩
    simpa [B, T] using compactTextbookMap_weight_binaryNat_inputSize_le hweight
  have hSum :=
    natList_sum_le_length_mul_bound hEach
  have hOutput :
      partitionBinaryStructuredEncodedType.inputSize (compactTextbookMap I) ≤ L * B + L := by
    rw [partitionBinaryStructured_inputSize_eq]
    have hMapLen :
        ((compactTextbookMap I).weights.map EncodedType.binaryNat.inputSize).length = L := by
      simp [L]
      rfl
    have hSum' :
        ((compactTextbookMap I).weights.map EncodedType.binaryNat.inputSize).sum ≤ L * B := by
      simpa [hMapLen] using hSum
    dsimp [L]
    exact Nat.add_le_add_right hSum' _
  have hCoarse : L * B + L ≤ 1000 * T ^ 2 := by
    have hT : 1 ≤ T := by dsimp [T]; omega
    have hB : B ≤ 32 * T := by dsimp [B]; nlinarith
    have hL : L ≤ 8 * T := by nlinarith
    calc
      L * B + L ≤ (8 * T) * (32 * T) + 8 * T := by
        exact Nat.add_le_add (Nat.mul_le_mul hL hB) hL
      _ ≤ 1000 * T ^ 2 := by nlinarith
  exact hOutput.trans hCoarse

theorem knapsackBinaryStructured_inputSize_pos (I : KnapsackInput) :
    0 < knapsackBinaryStructuredEncodedType.inputSize I := by
  rw [Knapsack.knapsackBinaryStructured_inputSize_eq]
  omega

theorem compactTextbookMap_binaryStructured_inputSize_le_knapsack_poly
    (I : KnapsackInput) :
    partitionBinaryStructuredEncodedType.inputSize (compactTextbookMap I) ≤
      4000 * (knapsackBinaryStructuredEncodedType.inputSize I) ^ 2 := by
  let S := knapsackBinaryStructuredEncodedType.inputSize I
  have hSucc := partitionBinaryStructured_inputSize_compactTextbookMap_le_knapsack_poly_succ I
  have hPos : 0 < S := by
    simpa [S] using knapsackBinaryStructured_inputSize_pos I
  have hSuccLe : S + 1 ≤ 2 * S := by omega
  have hPow : (S + 1) ^ 2 ≤ (2 * S) ^ 2 :=
    Nat.pow_le_pow_left hSuccLe 2
  calc
    partitionBinaryStructuredEncodedType.inputSize (compactTextbookMap I)
        ≤ 1000 * (S + 1) ^ 2 := by simpa [S] using hSucc
    _ ≤ 1000 * (2 * S) ^ 2 := Nat.mul_le_mul_left 1000 hPow
    _ = 4000 * S ^ 2 := by ring

end Partition
end Karp21
end ComplexityReduction
