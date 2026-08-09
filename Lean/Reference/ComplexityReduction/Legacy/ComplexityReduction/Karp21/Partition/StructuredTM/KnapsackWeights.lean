import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.StructuredTM.ProductSumChoice
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.Range

namespace ComplexityReduction
namespace Karp21
namespace Partition

open ComplexityReduction.Combinatorics

/-!
Direct TM components for constructing the structured subset-sum weight list in
the Knapsack-to-Partition textbook route.
-/

abbrev EncodedItemsAccCarrier := Nat × List Nat

def encodedItemsAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat partitionWeightsStructuredEncodedType

def encodedItemsInstructionEncodedType : EncodedType :=
  EncodedType.sum EncodedType.nat knapsackItemStructuredEncodedType

def encodedItemsInstructionListEncodedType : EncodedType :=
  EncodedType.list encodedItemsInstructionEncodedType

def encodedItemsInitAcc : EncodedItemsAccCarrier :=
  (0, [])

def encodedItemsInitInstruction (base : Nat) :
    encodedItemsInstructionEncodedType.Carrier :=
  Sum.inl base

def encodedItemsItemInstruction (item : Nat × Nat) :
    encodedItemsInstructionEncodedType.Carrier :=
  Sum.inr item

def encodedItemsInstructions (p : Nat × List (Nat × Nat)) :
    List encodedItemsInstructionEncodedType.Carrier :=
  encodedItemsInitInstruction p.1 :: p.2.map encodedItemsItemInstruction

def encodedItemsStep
    (p : EncodedItemsAccCarrier × encodedItemsInstructionEncodedType.Carrier) :
    EncodedItemsAccCarrier :=
  match p.2 with
  | Sum.inl base => (base, [])
  | Sum.inr item => (p.1.1, p.1.2 ++ [encodedItem p.1.1 item])

def encodedItemsStepLeft (base : Nat) : EncodedItemsAccCarrier :=
  (base, [])

def encodedItemsStepRight (p : EncodedItemsAccCarrier × (Nat × Nat)) :
    EncodedItemsAccCarrier :=
  (p.1.1, p.1.2 ++ [encodedItem p.1.1 p.2])

def encodedItemsFold
    (instructions : List encodedItemsInstructionEncodedType.Carrier) :
    EncodedItemsAccCarrier :=
  instructions.foldl (fun acc instr => encodedItemsStep (acc, instr)) encodedItemsInitAcc

def encodedItemsFromPair (p : Nat × List (Nat × Nat)) : List Nat :=
  (encodedItemsFold (encodedItemsInstructions p)).2

theorem encodedItemsStep_right_fold
    (base : Nat) (out : List Nat) (items : List (Nat × Nat)) :
    (items.map encodedItemsItemInstruction).foldl
        (fun acc instr => encodedItemsStep (acc, instr)) (base, out) =
      (base, out ++ encodedItems base items) := by
  induction items generalizing out with
  | nil =>
      simp [encodedItems]
  | cons item rest ih =>
      simp only [List.map_cons, List.foldl_cons, encodedItemsItemInstruction,
        encodedItemsStep]
      calc
        List.foldl
            (fun acc instr =>
              match instr with
              | Sum.inl base => (base, [])
              | Sum.inr item => (acc.1, acc.2 ++ [encodedItem acc.1 item]))
            (base, out ++ [encodedItem base item])
            (List.map encodedItemsItemInstruction rest)
            = (base, (out ++ [encodedItem base item]) ++ encodedItems base rest) := by
              simpa [encodedItemsStep] using ih (out ++ [encodedItem base item])
        _ = (base, out ++ encodedItems base (item :: rest)) := by
              simp [encodedItems, List.append_assoc]

theorem encodedItemsFromPair_eq (p : Nat × List (Nat × Nat)) :
    encodedItemsFromPair p = encodedItems p.1 p.2 := by
  rcases p with ⟨base, items⟩
  have h := encodedItemsStep_right_fold base [] items
  simpa [encodedItemsFromPair, encodedItemsFold, encodedItemsInstructions,
    encodedItemsInitInstruction, encodedItemsInitAcc, encodedItemsStep] using
    congrArg Prod.snd h

theorem encodedItem_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat knapsackItemStructuredEncodedType)
      EncodedType.nat
      (fun p : Nat × (Nat × Nat) => encodedItem p.1 p.2) := by
  have hBase :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.nat knapsackItemStructuredEncodedType)
        EncodedType.nat
        (fun p : Nat × (Nat × Nat) => p.1) := by
    simpa [knapsackItemStructuredEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat knapsackItemStructuredEncodedType
  have hItem :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.nat knapsackItemStructuredEncodedType)
        knapsackItemStructuredEncodedType
        (fun p : Nat × (Nat × Nat) => p.2) := by
    simpa [knapsackItemStructuredEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat knapsackItemStructuredEncodedType
  have hWeight :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.nat knapsackItemStructuredEncodedType)
        EncodedType.nat
        (fun p : Nat × (Nat × Nat) => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hItem
    simpa [Function.comp, knapsackItemStructuredEncodedType] using hComp
  have hValue :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.nat knapsackItemStructuredEncodedType)
        EncodedType.nat
        (fun p : Nat × (Nat × Nat) => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hItem
    simpa [Function.comp, knapsackItemStructuredEncodedType] using hComp
  have hMulInput :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.nat knapsackItemStructuredEncodedType)
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × (Nat × Nat) => (p.1, p.2.1)) :=
    TMPolyTimeMap.prod_mk hBase hWeight
  have hMul :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.nat knapsackItemStructuredEncodedType)
        EncodedType.nat
        (fun p : Nat × (Nat × Nat) => p.1 * p.2.1) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_mul hMulInput
    simpa [Function.comp] using hComp
  have hAddInput :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.nat knapsackItemStructuredEncodedType)
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × (Nat × Nat) => (p.1 * p.2.1, p.2.2)) :=
    TMPolyTimeMap.prod_mk hMul hValue
  have hComp := TMPolyTimeMap.comp natAdd_tm_polytime hAddInput
  simpa [Function.comp, encodedItem] using hComp

theorem natListAppendSingleton_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod partitionWeightsStructuredEncodedType EncodedType.nat)
      partitionWeightsStructuredEncodedType
      (fun p : List Nat × Nat => p.1 ++ [p.2]) := by
  have hHead :
      TMPolyTimeMap
        (EncodedType.prod partitionWeightsStructuredEncodedType EncodedType.nat)
        partitionWeightsStructuredEncodedType
        (fun p : List Nat × Nat => p.1) :=
    TMPolyTimeMap.fst partitionWeightsStructuredEncodedType EncodedType.nat
  have hSingleton :
      TMPolyTimeMap
        (EncodedType.prod partitionWeightsStructuredEncodedType EncodedType.nat)
        partitionWeightsStructuredEncodedType
        (fun p : List Nat × Nat => [p.2]) := by
    have hSnd :=
      TMPolyTimeMap.snd partitionWeightsStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton EncodedType.nat) hSnd
    simpa [Function.comp, partitionWeightsStructuredEncodedType] using hComp
  have hPair :
      TMPolyTimeMap
        (EncodedType.prod partitionWeightsStructuredEncodedType EncodedType.nat)
        (EncodedType.prod partitionWeightsStructuredEncodedType partitionWeightsStructuredEncodedType)
        (fun p : List Nat × Nat => (p.1, [p.2])) :=
    TMPolyTimeMap.prod_mk hHead hSingleton
  have hComp := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append EncodedType.nat) hPair
  simpa [Function.comp, partitionWeightsStructuredEncodedType] using hComp

theorem encodedItemsStepRight_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod encodedItemsAccEncodedType knapsackItemStructuredEncodedType)
      encodedItemsAccEncodedType
      encodedItemsStepRight := by
  have hAcc :
      TMPolyTimeMap
        (EncodedType.prod encodedItemsAccEncodedType knapsackItemStructuredEncodedType)
        encodedItemsAccEncodedType
        (fun p : EncodedItemsAccCarrier × (Nat × Nat) => p.1) :=
    TMPolyTimeMap.fst encodedItemsAccEncodedType knapsackItemStructuredEncodedType
  have hBase :
      TMPolyTimeMap
        (EncodedType.prod encodedItemsAccEncodedType knapsackItemStructuredEncodedType)
        EncodedType.nat
        (fun p : EncodedItemsAccCarrier × (Nat × Nat) => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat partitionWeightsStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, encodedItemsAccEncodedType] using hComp
  have hOut :
      TMPolyTimeMap
        (EncodedType.prod encodedItemsAccEncodedType knapsackItemStructuredEncodedType)
        partitionWeightsStructuredEncodedType
        (fun p : EncodedItemsAccCarrier × (Nat × Nat) => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat partitionWeightsStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, encodedItemsAccEncodedType] using hComp
  have hItem :
      TMPolyTimeMap
        (EncodedType.prod encodedItemsAccEncodedType knapsackItemStructuredEncodedType)
        knapsackItemStructuredEncodedType
        (fun p : EncodedItemsAccCarrier × (Nat × Nat) => p.2) :=
    TMPolyTimeMap.snd encodedItemsAccEncodedType knapsackItemStructuredEncodedType
  have hEncodedInput :
      TMPolyTimeMap
        (EncodedType.prod encodedItemsAccEncodedType knapsackItemStructuredEncodedType)
        (EncodedType.prod EncodedType.nat knapsackItemStructuredEncodedType)
        (fun p : EncodedItemsAccCarrier × (Nat × Nat) => (p.1.1, p.2)) :=
    TMPolyTimeMap.prod_mk hBase hItem
  have hEncoded :
      TMPolyTimeMap
        (EncodedType.prod encodedItemsAccEncodedType knapsackItemStructuredEncodedType)
        EncodedType.nat
        (fun p : EncodedItemsAccCarrier × (Nat × Nat) =>
          encodedItem p.1.1 p.2) := by
    have hComp := TMPolyTimeMap.comp encodedItem_tm_polytime hEncodedInput
    simpa [Function.comp] using hComp
  have hAppendInput :
      TMPolyTimeMap
        (EncodedType.prod encodedItemsAccEncodedType knapsackItemStructuredEncodedType)
        (EncodedType.prod partitionWeightsStructuredEncodedType EncodedType.nat)
        (fun p : EncodedItemsAccCarrier × (Nat × Nat) =>
          (p.1.2, encodedItem p.1.1 p.2)) :=
    TMPolyTimeMap.prod_mk hOut hEncoded
  have hAppend :
      TMPolyTimeMap
        (EncodedType.prod encodedItemsAccEncodedType knapsackItemStructuredEncodedType)
        partitionWeightsStructuredEncodedType
        (fun p : EncodedItemsAccCarrier × (Nat × Nat) =>
          p.1.2 ++ [encodedItem p.1.1 p.2]) := by
    have hComp := TMPolyTimeMap.comp natListAppendSingleton_tm_polytime hAppendInput
    simpa [Function.comp] using hComp
  have hPair := TMPolyTimeMap.prod_mk hBase hAppend
  simpa [encodedItemsAccEncodedType, encodedItemsStepRight] using hPair

theorem encodedItemsStepLeft_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      encodedItemsAccEncodedType
      encodedItemsStepLeft := by
  have hBase := TMPolyTimeMap.id EncodedType.nat
  have hEmpty :
      TMPolyTimeMap EncodedType.nat partitionWeightsStructuredEncodedType
        (fun _ : Nat => ([] : List Nat)) :=
    TMPolyTimeMap.const EncodedType.nat partitionWeightsStructuredEncodedType []
  have hPair := TMPolyTimeMap.prod_mk hBase hEmpty
  simpa [encodedItemsAccEncodedType, encodedItemsStepLeft] using hPair

theorem encodedItemsStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod encodedItemsAccEncodedType encodedItemsInstructionEncodedType)
      encodedItemsAccEncodedType
      encodedItemsStep := by
  have hChoice :=
    prodSumChoice_tm_polytime
      encodedItemsAccEncodedType EncodedType.nat knapsackItemStructuredEncodedType
  have hBranches :=
    TMPolyTimeMap.sum_elim encodedItemsStepLeft_tm_polytime
      encodedItemsStepRight_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem encodedItemsInstructions_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat knapsackItemListStructuredEncodedType)
      encodedItemsInstructionListEncodedType
      encodedItemsInstructions := by
  have hBase :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.nat knapsackItemListStructuredEncodedType)
        EncodedType.nat
        (fun p : Nat × List (Nat × Nat) => p.1) :=
    TMPolyTimeMap.fst EncodedType.nat knapsackItemListStructuredEncodedType
  have hItems :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.nat knapsackItemListStructuredEncodedType)
        knapsackItemListStructuredEncodedType
        (fun p : Nat × List (Nat × Nat) => p.2) :=
    TMPolyTimeMap.snd EncodedType.nat knapsackItemListStructuredEncodedType
  have hBaseInstr :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.nat knapsackItemListStructuredEncodedType)
        encodedItemsInstructionEncodedType
        (fun p : Nat × List (Nat × Nat) => encodedItemsInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.inl EncodedType.nat knapsackItemStructuredEncodedType) hBase
    simpa [Function.comp, encodedItemsInstructionEncodedType,
      encodedItemsInitInstruction] using hComp
  have hItemInstr :
      TMPolyTimeMap
        knapsackItemStructuredEncodedType
        encodedItemsInstructionEncodedType
        encodedItemsItemInstruction := by
    simpa [encodedItemsInstructionEncodedType, encodedItemsItemInstruction] using
      TMPolyTimeMap.inr EncodedType.nat knapsackItemStructuredEncodedType
  have hMappedItems :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.nat knapsackItemListStructuredEncodedType)
        encodedItemsInstructionListEncodedType
        (fun p : Nat × List (Nat × Nat) =>
          p.2.map encodedItemsItemInstruction) := by
    have hMap := TMPolyTimeMap.list_map hItemInstr
    have hComp := TMPolyTimeMap.comp hMap hItems
    simpa [Function.comp, encodedItemsInstructionListEncodedType,
      knapsackItemListStructuredEncodedType] using hComp
  have hConsInput :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.nat knapsackItemListStructuredEncodedType)
        (EncodedType.prod encodedItemsInstructionEncodedType
          encodedItemsInstructionListEncodedType)
        (fun p : Nat × List (Nat × Nat) =>
          (encodedItemsInitInstruction p.1,
            p.2.map encodedItemsItemInstruction)) :=
    TMPolyTimeMap.prod_mk hBaseInstr hMappedItems
  have hComp := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons encodedItemsInstructionEncodedType) hConsInput
  simpa [Function.comp, encodedItemsInstructionListEncodedType,
    encodedItemsInstructions] using hComp

/-! ### Reachable fold bounds for `encodedItems` -/

theorem encodedItemsList_length_le_inputSize (X : EncodedType)
    (xs : List X.Carrier) :
    xs.length ≤ (EncodedType.list X).inputSize xs := by
  induction xs with
  | nil =>
      simp [EncodedType.inputSize_list_nil]
  | cons x xs ih =>
      simp only [List.length_cons]
      rw [EncodedType.inputSize_list_cons]
      omega

theorem encodedItemsList_element_inputSize_le {X : EncodedType}
    {x : X.Carrier} {xs : List X.Carrier}
    (hx : x ∈ xs) :
    X.inputSize x ≤ (EncodedType.list X).inputSize xs := by
  induction xs with
  | nil =>
      simp at hx
  | cons y ys ih =>
      rw [EncodedType.inputSize_list_cons]
      simp at hx
      rcases hx with rfl | hx
      · omega
      · have h := ih hx
        omega

theorem encodedItemsList_inputSize_append (X : EncodedType)
    (xs ys : List X.Carrier) :
    (EncodedType.list X).inputSize (xs ++ ys) =
      (EncodedType.list X).inputSize xs + (EncodedType.list X).inputSize ys := by
  induction xs with
  | nil =>
      simp [EncodedType.inputSize_list_nil]
  | cons x xs ih =>
      rw [List.cons_append, EncodedType.inputSize_list_cons,
        EncodedType.inputSize_list_cons, ih]
      omega

theorem encodedItemsList_inputSize_append_singleton (X : EncodedType)
    (xs : List X.Carrier) (x : X.Carrier) :
    (EncodedType.list X).inputSize (xs ++ [x]) =
      (EncodedType.list X).inputSize xs + X.inputSize x + 1 := by
  rw [encodedItemsList_inputSize_append]
  rw [EncodedType.inputSize_list_cons, EncodedType.inputSize_list_nil]
  omega

noncomputable def encodedItemsPerStepBoundPolynomial : Polynomial Nat :=
  Polynomial.C 10 * (Polynomial.X * Polynomial.X) + Polynomial.C 20

@[simp] theorem encodedItemsPerStepBoundPolynomial_eval (N : Nat) :
    encodedItemsPerStepBoundPolynomial.eval N = 10 * (N * N) + 20 := by
  simp [encodedItemsPerStepBoundPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

noncomputable def encodedItemsFoldAccBoundPolynomial : Polynomial Nat :=
  Polynomial.C 20 * (Polynomial.X * Polynomial.X * Polynomial.X) + Polynomial.C 100

@[simp] theorem encodedItemsFoldAccBoundPolynomial_eval (N : Nat) :
    encodedItemsFoldAccBoundPolynomial.eval N = 20 * (N * N * N) + 100 := by
  simp [encodedItemsFoldAccBoundPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

def encodedItemsAccBound (N processed : Nat) (acc : EncodedItemsAccCarrier) : Prop :=
  acc.1 ≤ N ∧
    partitionWeightsStructuredEncodedType.inputSize acc.2 ≤
      processed * encodedItemsPerStepBoundPolynomial.eval N

theorem encodedItemsInitAcc_bound (N : Nat) :
    encodedItemsAccBound N 0 encodedItemsInitAcc := by
  constructor
  · simp [encodedItemsInitAcc]
  · have hZero :
        partitionWeightsStructuredEncodedType.inputSize encodedItemsInitAcc.2 = 0 := by
      change (EncodedType.list EncodedType.nat).inputSize ([] : List Nat) = 0
      exact EncodedType.inputSize_list_nil EncodedType.nat
    rw [hZero]
    omega

theorem encodedItemsInstruction_base_le
    {N base : Nat}
    (hInstr : encodedItemsInstructionEncodedType.inputSize (Sum.inl base) ≤ N) :
    base ≤ N := by
  simp [encodedItemsInstructionEncodedType, EncodedType.inputSize,
    EncodedType.sum, EncodedType.nat] at hInstr
  omega

theorem encodedItemsInstruction_item_weight_le
    {N : Nat} {item : Nat × Nat}
    (hInstr : encodedItemsInstructionEncodedType.inputSize (Sum.inr item) ≤ N) :
    item.1 ≤ N := by
  rcases item with ⟨w, v⟩
  simp [encodedItemsInstructionEncodedType, knapsackItemStructuredEncodedType,
    EncodedType.inputSize, EncodedType.sum, EncodedType.prod, EncodedType.nat] at hInstr
  omega

theorem encodedItemsInstruction_item_value_le
    {N : Nat} {item : Nat × Nat}
    (hInstr : encodedItemsInstructionEncodedType.inputSize (Sum.inr item) ≤ N) :
    item.2 ≤ N := by
  rcases item with ⟨w, v⟩
  simp [encodedItemsInstructionEncodedType, knapsackItemStructuredEncodedType,
    EncodedType.inputSize, EncodedType.sum, EncodedType.prod, EncodedType.nat] at hInstr
  omega

theorem encodedItem_inputSize_le_perStep
    {N base : Nat} {item : Nat × Nat}
    (hBase : base ≤ N)
    (hWeight : item.1 ≤ N)
    (hValue : item.2 ≤ N) :
    EncodedType.nat.inputSize (encodedItem base item) + 1 ≤
      encodedItemsPerStepBoundPolynomial.eval N := by
  rcases item with ⟨w, v⟩
  simp [encodedItem, EncodedType.inputSize_nat]
  have hMul : base * w ≤ N * N := Nat.mul_le_mul hBase hWeight
  nlinarith [hMul, hValue, Nat.zero_le N]

theorem encodedItemsStep_bound {N processed : Nat}
    {acc : EncodedItemsAccCarrier}
    {instr : encodedItemsInstructionEncodedType.Carrier}
    (hAcc : encodedItemsAccBound N processed acc)
    (hInstr : encodedItemsInstructionEncodedType.inputSize instr ≤ N) :
    encodedItemsAccBound N (processed + 1) (encodedItemsStep (acc, instr)) := by
  rcases hAcc with ⟨hBase, hOut⟩
  cases instr with
  | inl base =>
      have hBase' := encodedItemsInstruction_base_le hInstr
      constructor
      · simpa [encodedItemsStep] using hBase'
      · have hZero :
            partitionWeightsStructuredEncodedType.inputSize
                (encodedItemsStep (acc, Sum.inl base)).2 = 0 := by
          change (EncodedType.list EncodedType.nat).inputSize ([] : List Nat) = 0
          exact EncodedType.inputSize_list_nil EncodedType.nat
        rw [hZero]
        omega
  | inr item =>
      have hWeight := encodedItemsInstruction_item_weight_le hInstr
      have hValue := encodedItemsInstruction_item_value_le hInstr
      have hEnc := encodedItem_inputSize_le_perStep
        (N := N) (base := acc.1) (item := item) hBase hWeight hValue
      constructor
      · simpa [encodedItemsStep] using hBase
      · have hAppend :
            partitionWeightsStructuredEncodedType.inputSize
                (acc.2 ++ [encodedItem acc.1 item]) =
              partitionWeightsStructuredEncodedType.inputSize acc.2 +
                EncodedType.nat.inputSize (encodedItem acc.1 item) + 1 := by
          simpa [partitionWeightsStructuredEncodedType] using
            encodedItemsList_inputSize_append_singleton EncodedType.nat acc.2
              (encodedItem acc.1 item)
        have hStepOut :
            (encodedItemsStep (acc, Sum.inr item)).2 =
              acc.2 ++ [encodedItem acc.1 item] := by
          simp [encodedItemsStep]
        rw [hStepOut]
        rw [hAppend]
        calc
          partitionWeightsStructuredEncodedType.inputSize acc.2 +
                EncodedType.nat.inputSize (encodedItem acc.1 item) + 1
              = partitionWeightsStructuredEncodedType.inputSize acc.2 +
                  (EncodedType.nat.inputSize (encodedItem acc.1 item) + 1) := by
                  omega
          _ ≤ processed * encodedItemsPerStepBoundPolynomial.eval N +
                encodedItemsPerStepBoundPolynomial.eval N := by
                  exact Nat.add_le_add hOut hEnc
          _ = (processed + 1) * encodedItemsPerStepBoundPolynomial.eval N := by
                  rw [Nat.add_mul, Nat.one_mul]

theorem encodedItemsFold_bound_aux {N processed : Nat}
    (rest : List encodedItemsInstructionEncodedType.Carrier)
    (acc : EncodedItemsAccCarrier)
    (hAcc : encodedItemsAccBound N processed acc)
    (hLen : processed + rest.length ≤ N)
    (hInstr : ∀ instr ∈ rest, encodedItemsInstructionEncodedType.inputSize instr ≤ N) :
    encodedItemsAccBound N (processed + rest.length)
      (rest.foldl (fun acc instr => encodedItemsStep (acc, instr)) acc) := by
  induction rest generalizing processed acc with
  | nil =>
      simpa using hAcc
  | cons instr rest ih =>
      have hHead : encodedItemsInstructionEncodedType.inputSize instr ≤ N := by
        exact hInstr instr (by simp)
      have hStep := encodedItemsStep_bound (N := N) (processed := processed)
        (acc := acc) (instr := instr) hAcc hHead
      have hLenTail : processed + 1 + rest.length ≤ N := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hLen
      have hInstrTail :
          ∀ instr' ∈ rest, encodedItemsInstructionEncodedType.inputSize instr' ≤ N := by
        intro instr' hin
        exact hInstr instr' (by simp [hin])
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (processed := processed + 1) (acc := encodedItemsStep (acc, instr))
          hStep hLenTail hInstrTail

theorem encodedItemsFold_bound_of_inputSize_le {N : Nat}
    (xs : List encodedItemsInstructionEncodedType.Carrier)
    (hSize : encodedItemsInstructionListEncodedType.inputSize xs ≤ N) :
    encodedItemsAccBound N xs.length
      (xs.foldl (fun acc instr => encodedItemsStep (acc, instr)) encodedItemsInitAcc) := by
  have hLenRaw := encodedItemsList_length_le_inputSize encodedItemsInstructionEncodedType xs
  have hLen : xs.length ≤ N := by
    have hLenRaw' :
        xs.length ≤ encodedItemsInstructionListEncodedType.inputSize xs := by
      simpa [encodedItemsInstructionListEncodedType] using hLenRaw
    omega
  have hInstr :
      ∀ instr ∈ xs, encodedItemsInstructionEncodedType.inputSize instr ≤ N := by
    intro instr hin
    have hElem := encodedItemsList_element_inputSize_le
      (X := encodedItemsInstructionEncodedType) (x := instr) (xs := xs) hin
    have hElem' :
        encodedItemsInstructionEncodedType.inputSize instr ≤
          encodedItemsInstructionListEncodedType.inputSize xs := by
      simpa [encodedItemsInstructionListEncodedType] using hElem
    omega
  have h := encodedItemsFold_bound_aux (N := N) (processed := 0) xs encodedItemsInitAcc
    (encodedItemsInitAcc_bound N) (by simpa using hLen) hInstr
  simpa using h

theorem encodedItemsAccBound_inputSize_le {N processed : Nat}
    {acc : EncodedItemsAccCarrier}
    (hAcc : encodedItemsAccBound N processed acc)
    (hProcessed : processed ≤ N) :
    encodedItemsAccEncodedType.inputSize acc ≤
      encodedItemsFoldAccBoundPolynomial.eval N := by
  rcases acc with ⟨base, out⟩
  rcases hAcc with ⟨hBase, hOut⟩
  have hOutN :
      partitionWeightsStructuredEncodedType.inputSize out ≤
        N * encodedItemsPerStepBoundPolynomial.eval N := by
    exact hOut.trans (Nat.mul_le_mul_right _ hProcessed)
  simp [encodedItemsAccEncodedType, EncodedType.inputSize_prod] at hOutN ⊢
  nlinarith [hBase, hOutN, Nat.zero_le N]

noncomputable def encodedItemsFoldTimePolynomial
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod encodedItemsAccEncodedType
          encodedItemsInstructionEncodedType).encode
        encodedItemsAccEncodedType.encode
        encodedItemsStep) : Polynomial Nat :=
  TM2Programs.listFoldBoundedTimePolynomial hStep.tm encodedItemsFoldAccBoundPolynomial
    (hStep.time.comp
      (encodedItemsFoldAccBoundPolynomial + Polynomial.X + Polynomial.C 5))

theorem encodedItemsFold_tm_polytime :
    TMPolyTimeMap
      encodedItemsInstructionListEncodedType
      encodedItemsAccEncodedType
      encodedItemsFold := by
  rcases encodedItemsStep_tm_polytime with ⟨hStep⟩
  let time := encodedItemsFoldTimePolynomial hStep
  refine
    TMPolyTimeMap.list_foldl_typed
      encodedItemsInstructionEncodedType encodedItemsAccEncodedType
      encodedItemsStep encodedItemsInitAcc hStep time ?_
  intro source
  let N := encodedItemsInstructionListEncodedType.inputSize source
  let B := encodedItemsFoldAccBoundPolynomial.eval N
  let T := hStep.time.eval (B + N + 5)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hLoopAux :
      ∀ (pref rest : List encodedItemsInstructionEncodedType.Carrier),
        source = pref ++ rest →
          TM2Programs.listFoldTypedLoopTime
              encodedItemsInstructionEncodedType encodedItemsAccEncodedType
              encodedItemsStep hStep
              (pref.foldl (fun acc instr => encodedItemsStep (acc, instr))
                encodedItemsInitAcc)
              rest ≤
            C * (EncodedType.list encodedItemsInstructionEncodedType).inputSize rest := by
    intro pref rest
    induction rest generalizing pref with
    | nil =>
        intro _hEq
        simp [TM2Programs.listFoldTypedLoopTime]
    | cons x xs ih =>
        intro hEq
        have hxMemSource : x ∈ source := by
          rw [hEq]
          simp
        have hxN : encodedItemsInstructionEncodedType.inputSize x ≤ N := by
          have hElem := encodedItemsList_element_inputSize_le
            (X := encodedItemsInstructionEncodedType) (x := x) (xs := source) hxMemSource
          simpa [N, encodedItemsInstructionListEncodedType] using hElem
        have hPrefixSize : encodedItemsInstructionListEncodedType.inputSize pref ≤ N := by
          have hEqSize :
              encodedItemsInstructionListEncodedType.inputSize source =
                encodedItemsInstructionListEncodedType.inputSize pref +
                  encodedItemsInstructionListEncodedType.inputSize (x :: xs) := by
            rw [hEq]
            exact encodedItemsList_inputSize_append encodedItemsInstructionEncodedType
              pref (x :: xs)
          omega
        have hPrefixBound :=
          encodedItemsFold_bound_of_inputSize_le (N := N) pref hPrefixSize
        have hPrefixLenN : pref.length ≤ N := by
          have hLen :=
            encodedItemsList_length_le_inputSize encodedItemsInstructionEncodedType pref
          have hLen' :
              pref.length ≤ encodedItemsInstructionListEncodedType.inputSize pref := by
            simpa [encodedItemsInstructionListEncodedType] using hLen
          omega
        have hAccSize :
            encodedItemsAccEncodedType.inputSize
                (pref.foldl (fun acc instr => encodedItemsStep (acc, instr))
                  encodedItemsInitAcc) ≤ B := by
          simpa [B] using
            encodedItemsAccBound_inputSize_le hPrefixBound hPrefixLenN
        have hStepProcessed : pref.length + 1 ≤ N := by
          have hLenEq : source.length = pref.length + (x :: xs).length := by
            rw [hEq, List.length_append]
          simp only [List.length_cons] at hLenEq
          have hSourceLenN : source.length ≤ N := by
            have hLen :=
              encodedItemsList_length_le_inputSize encodedItemsInstructionEncodedType source
            simpa [N, encodedItemsInstructionListEncodedType] using hLen
          omega
        have hStepBound :=
          encodedItemsStep_bound hPrefixBound hxN
        have hStepSize :
            encodedItemsAccEncodedType.inputSize
                (encodedItemsStep
                  (pref.foldl (fun acc instr => encodedItemsStep (acc, instr))
                    encodedItemsInitAcc, x)) ≤ B := by
          simpa [B] using
            encodedItemsAccBound_inputSize_le hStepBound hStepProcessed
        have hStepTime :
            hStep.time.eval
                ((EncodedType.prod encodedItemsAccEncodedType
                  encodedItemsInstructionEncodedType).inputSize
                  (pref.foldl (fun acc instr => encodedItemsStep (acc, instr))
                    encodedItemsInitAcc, x)) ≤ T := by
          have hArg :
              (EncodedType.prod encodedItemsAccEncodedType
                encodedItemsInstructionEncodedType).inputSize
                  (pref.foldl (fun acc instr => encodedItemsStep (acc, instr))
                    encodedItemsInitAcc, x) ≤ B + N + 5 := by
            rw [EncodedType.inputSize_prod]
            change
              encodedItemsAccEncodedType.inputSize
                    (pref.foldl (fun acc instr => encodedItemsStep (acc, instr))
                      encodedItemsInitAcc) +
                  1 + encodedItemsInstructionEncodedType.inputSize x ≤ B + N + 5
            omega
          exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
        have hBlock :
            TM2Programs.listFoldBlockTime hStep.tm
                (encodedItemsInstructionEncodedType.encode x).length
                (encodedItemsAccEncodedType.encode
                  (pref.foldl (fun acc instr => encodedItemsStep (acc, instr))
                    encodedItemsInitAcc)).length
                (encodedItemsAccEncodedType.encode
                  (encodedItemsStep
                    (pref.foldl (fun acc instr => encodedItemsStep (acc, instr))
                      encodedItemsInitAcc, x))).length
                (hStep.time.eval
                  ((EncodedType.prod encodedItemsAccEncodedType
                    encodedItemsInstructionEncodedType).inputSize
                    (pref.foldl (fun acc instr => encodedItemsStep (acc, instr))
                      encodedItemsInitAcc, x))) ≤
              C * (encodedItemsInstructionEncodedType.inputSize x + 1) := by
          exact
            TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
              (by simpa [EncodedType.inputSize] using hAccSize)
              (by simpa [EncodedType.inputSize] using hStepSize)
              hStepTime
        have hEqTail : source = (pref ++ [x]) ++ xs := by
          rw [hEq]
          simp [List.append_assoc]
        have hTailRaw := ih (pref := pref ++ [x]) hEqTail
        have hTail :
            TM2Programs.listFoldTypedLoopTime
                encodedItemsInstructionEncodedType encodedItemsAccEncodedType
                encodedItemsStep hStep
                (encodedItemsStep
                  (pref.foldl (fun acc instr => encodedItemsStep (acc, instr))
                    encodedItemsInitAcc, x)) xs ≤
              C * (EncodedType.list encodedItemsInstructionEncodedType).inputSize xs := by
          have hFoldPref :
              (pref ++ [x]).foldl
                  (fun acc instr => encodedItemsStep (acc, instr)) encodedItemsInitAcc =
                encodedItemsStep
                  (pref.foldl (fun acc instr => encodedItemsStep (acc, instr))
                    encodedItemsInitAcc, x) := by
            exact
              List.foldl_concat
                (fun acc instr => encodedItemsStep (acc, instr)) encodedItemsInitAcc x pref
          convert hTailRaw using 1
          exact congrArg
            (fun acc =>
              TM2Programs.listFoldTypedLoopTime
                encodedItemsInstructionEncodedType encodedItemsAccEncodedType
                encodedItemsStep hStep acc xs)
            hFoldPref.symm
        calc
          TM2Programs.listFoldTypedLoopTime
              encodedItemsInstructionEncodedType encodedItemsAccEncodedType
              encodedItemsStep hStep
              (pref.foldl (fun acc instr => encodedItemsStep (acc, instr))
                encodedItemsInitAcc)
              (x :: xs)
              =
            TM2Programs.listFoldTypedLoopTime
                encodedItemsInstructionEncodedType encodedItemsAccEncodedType
                encodedItemsStep hStep
                (encodedItemsStep
                  (pref.foldl (fun acc instr => encodedItemsStep (acc, instr))
                    encodedItemsInitAcc, x)) xs +
              TM2Programs.listFoldBlockTime hStep.tm
                (encodedItemsInstructionEncodedType.encode x).length
                (encodedItemsAccEncodedType.encode
                  (pref.foldl (fun acc instr => encodedItemsStep (acc, instr))
                    encodedItemsInitAcc)).length
                (encodedItemsAccEncodedType.encode
                  (encodedItemsStep
                    (pref.foldl (fun acc instr => encodedItemsStep (acc, instr))
                      encodedItemsInitAcc, x))).length
                (hStep.time.eval
                  ((EncodedType.prod encodedItemsAccEncodedType
                    encodedItemsInstructionEncodedType).inputSize
                    (pref.foldl (fun acc instr => encodedItemsStep (acc, instr))
                      encodedItemsInitAcc, x))) := by
                rfl
          _ ≤
              C * (EncodedType.list encodedItemsInstructionEncodedType).inputSize xs +
                C * (encodedItemsInstructionEncodedType.inputSize x + 1) :=
                Nat.add_le_add hTail hBlock
          _ ≤
              C * (EncodedType.list encodedItemsInstructionEncodedType).inputSize
                (x :: xs) := by
                rw [EncodedType.inputSize_list_cons]
                nlinarith
  have hLoop :
      TM2Programs.listFoldTypedLoopTime
          encodedItemsInstructionEncodedType encodedItemsAccEncodedType
          encodedItemsStep hStep encodedItemsInitAcc source ≤ C * N := by
    have h := hLoopAux [] source (by simp)
    simpa [N, encodedItemsInstructionListEncodedType] using h
  have hTimeEval : time.eval N = (C + 2) * (N + 1) := by
    simp [time, encodedItemsFoldTimePolynomial, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval, TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_comp]
  change 2 +
      TM2Programs.listFoldTypedLoopTime
        encodedItemsInstructionEncodedType encodedItemsAccEncodedType
        encodedItemsStep hStep encodedItemsInitAcc source ≤ time.eval N
  rw [hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

theorem encodedItemsFromPair_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat knapsackItemListStructuredEncodedType)
      partitionWeightsStructuredEncodedType
      encodedItemsFromPair := by
  have hFoldInput := encodedItemsInstructions_tm_polytime
  have hFold :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.nat knapsackItemListStructuredEncodedType)
        encodedItemsAccEncodedType
        (fun p => encodedItemsFold (encodedItemsInstructions p)) := by
    have hComp := TMPolyTimeMap.comp encodedItemsFold_tm_polytime hFoldInput
    simpa [Function.comp] using hComp
  have hSnd :
      TMPolyTimeMap encodedItemsAccEncodedType partitionWeightsStructuredEncodedType
        (fun acc : EncodedItemsAccCarrier => acc.2) := by
    simpa [encodedItemsAccEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat partitionWeightsStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, encodedItemsFromPair] using hComp

theorem encodedItems_pair_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat knapsackItemListStructuredEncodedType)
      partitionWeightsStructuredEncodedType
      (fun p : Nat × List (Nat × Nat) => encodedItems p.1 p.2) := by
  convert encodedItemsFromPair_tm_polytime using 1
  funext p
  exact (encodedItemsFromPair_eq p).symm

end Partition
end Karp21
end ComplexityReduction
