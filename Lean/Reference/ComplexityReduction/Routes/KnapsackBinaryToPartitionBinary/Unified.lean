/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.Authoring
import ComplexityReduction.AxiomGate
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryBitLength
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryLogic
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryMul
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinarySubTM
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.ListNat
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.SlackPowers
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipKnapsackBinary
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.Part3
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.StructuredTM.UnaryToBinary
import ComplexityReduction.Presentation.KnapsackBinary
import ComplexityReduction.Presentation.PartitionBinary
import ComplexityReduction.Program.ContextListMap
import ComplexityReduction.Protocol.ComponentResolver

/-!
Standard-axiom direct-TM reconstruction of the compact binary
Knapsack-to-Partition balancing route.

The legacy endpoint already contains the semantic theorem and a polynomial
output-size bound, but its binary record is cost-only.  This production leaf
rebuilds the same `compactTextbookMap` from direct binary arithmetic, list
folds, and context-list maps before registering the edge.
-/

namespace ComplexityReduction
namespace Routes
namespace KnapsackBinaryToPartitionBinary

open Certificate Encoding Program
open ComplexityReduction.Combinatorics

namespace K

abbrev binaryNatBitLength := ComplexityReduction.Karp21.Knapsack.binaryNatBitLength
abbrev binaryNatBitLength_tm_polytime :=
  ComplexityReduction.Karp21.Knapsack.binaryNatBitLength_tm_polytime
abbrev binaryNatSucc_tm_polytime :=
  ComplexityReduction.Karp21.Knapsack.binaryNatSucc_tm_polytime
abbrev binaryPowersFromBits := ComplexityReduction.Karp21.Knapsack.binaryPowersFromBits
abbrev binaryPowersFromBits_eq_compactBinaryPowers :=
  ComplexityReduction.Karp21.Knapsack.binaryPowersFromBits_eq_compactBinaryPowers
abbrev binaryPowersFromBits_tm_polytime :=
  ComplexityReduction.Karp21.Knapsack.binaryPowersFromBits_tm_polytime
abbrev compactBinaryPowers := ComplexityReduction.Karp21.Knapsack.compactBinaryPowers
abbrev binaryNatListSum_tm_polytime_sum :=
  ComplexityReduction.Karp21.Knapsack.binaryNatListSum_tm_polytime_sum
abbrev binaryNatSub_tm_polytime :=
  ComplexityReduction.Karp21.Knapsack.binaryNatSub_tm_polytime
abbrev binaryNatEqBool := ComplexityReduction.Karp21.Knapsack.binaryNatEqBool
abbrev binaryNatEqBool_eq_true_iff :=
  ComplexityReduction.Karp21.Knapsack.binaryNatEqBool_eq_true_iff
abbrev binaryNatEqBool_tm_polytime :=
  ComplexityReduction.Karp21.Knapsack.binaryNatEqBool_tm_polytime
abbrev knapsackBinaryItemsForMembership :=
  ComplexityReduction.Karp21.Knapsack.knapsackBinaryItemsForMembership
noncomputable abbrev knapsackBinaryItemsTMBackedMap :=
  ComplexityReduction.Karp21.Knapsack.knapsackBinaryItemsTMBackedMap
abbrev knapsackBinaryBoundsForMembership :=
  ComplexityReduction.Karp21.Knapsack.knapsackBinaryBoundsForMembership
noncomputable abbrev knapsackBinaryBoundsTMBackedMap :=
  ComplexityReduction.Karp21.Knapsack.knapsackBinaryBoundsTMBackedMap
abbrev binaryNatMax := ComplexityReduction.Karp21.Knapsack.binaryNatMax
abbrev binaryNatMax_tm_polytime :=
  ComplexityReduction.Karp21.Knapsack.binaryNatMax_tm_polytime
abbrev binaryNatMul_tm_polytime :=
  ComplexityReduction.Karp21.Knapsack.binaryNatMul_tm_polytime
abbrev binaryNatAdd_tm_polytime :=
  ComplexityReduction.Karp21.Knapsack.binaryNatAdd_tm_polytime

end K

namespace P

abbrev boundedSlackPrefixLength :=
  ComplexityReduction.Karp21.Partition.boundedSlackPrefixLength
abbrev binaryNat_inputSize_eq_size :=
  ComplexityReduction.Karp21.Partition.binaryNat_inputSize_eq_size
abbrev boundedSlackPrefixSum :=
  ComplexityReduction.Karp21.Partition.boundedSlackPrefixSum
abbrev boundedSlackRemainder :=
  ComplexityReduction.Karp21.Partition.boundedSlackRemainder
abbrev compactBinaryPowers_sum :=
  ComplexityReduction.Karp21.Partition.compactBinaryPowers_sum
abbrev boundedSlackPowers := ComplexityReduction.Karp21.Partition.boundedSlackPowers
abbrev itemValueTotal := ComplexityReduction.Karp21.Partition.itemValueTotal
abbrev valueTargetLevel := ComplexityReduction.Karp21.Partition.valueTargetLevel
abbrev valueSlackBudget := ComplexityReduction.Karp21.Partition.valueSlackBudget
abbrev compactPartitionBase := ComplexityReduction.Karp21.Partition.compactPartitionBase
abbrev encodedItem := ComplexityReduction.Karp21.Partition.encodedItem
abbrev encodedItems := ComplexityReduction.Karp21.Partition.encodedItems
abbrev compactWeightSlackWeights :=
  ComplexityReduction.Karp21.Partition.compactWeightSlackWeights
abbrev compactValueSlackWeights :=
  ComplexityReduction.Karp21.Partition.compactValueSlackWeights
abbrev compactKnapsackSubsetWeights :=
  ComplexityReduction.Karp21.Partition.compactKnapsackSubsetWeights
abbrev compactKnapsackSubsetTarget :=
  ComplexityReduction.Karp21.Partition.compactKnapsackSubsetTarget
abbrev subsetToPartitionWeights :=
  ComplexityReduction.Karp21.Partition.subsetToPartitionWeights
abbrev partitionInputFromBinaryWeights :=
  ComplexityReduction.Karp21.Partition.partitionInputFromBinaryWeights
noncomputable abbrev partitionInputFromBinaryWeightsTMBackedMap :=
  ComplexityReduction.Karp21.Partition.partitionInputFromBinaryWeightsTMBackedMap
abbrev compactTextbookMap := ComplexityReduction.Karp21.Partition.compactTextbookMap
abbrev compactTextbookMap_correct :=
  ComplexityReduction.Karp21.Partition.compactTextbookMap_correct

end P

abbrev sourcePresentation : LawfulEncodedType :=
  Presentation.KnapsackBinary.structuredPresentation

abbrev targetPresentation : LawfulEncodedType :=
  Presentation.PartitionBinary.structuredPresentation

abbrev sourceProblem : PresentedProblem :=
  Presentation.KnapsackBinary.structuredProblem

abbrev targetProblem : PresentedProblem :=
  Presentation.PartitionBinary.structuredProblem

abbrev binaryNatListEncodedType : EncodedType :=
  EncodedType.list EncodedType.binaryNat

abbrev itemEncodedType : EncodedType :=
  knapsackItemBinaryStructuredEncodedType

abbrev itemListEncodedType : EncodedType :=
  knapsackItemListBinaryStructuredEncodedType

/-! ### Compact bounded slack powers -/

def prefixLengthExecutable (budget : Nat) : Nat :=
  K.binaryNatBitLength (budget + 1) - 1

theorem prefixLengthExecutable_eq (budget : Nat) :
    prefixLengthExecutable budget = P.boundedSlackPrefixLength budget := by
  unfold prefixLengthExecutable P.boundedSlackPrefixLength K.binaryNatBitLength
  change EncodedType.binaryNat.inputSize (budget + 1) - 1 = Nat.size (budget + 1) - 1
  exact congrArg (fun length : Nat => length - 1)
    (P.binaryNat_inputSize_eq_size (budget + 1))

theorem prefixLengthExecutable_tmPolyTime :
    TMPolyTimeMap EncodedType.binaryNat EncodedType.nat prefixLengthExecutable := by
  have successor : TMPolyTimeMap EncodedType.binaryNat EncodedType.binaryNat
      (fun budget : Nat => budget + 1) := by
    simpa [Nat.succ_eq_add_one] using K.binaryNatSucc_tm_polytime
  have bitLength : TMPolyTimeMap EncodedType.binaryNat EncodedType.nat
      (fun budget : Nat => K.binaryNatBitLength (budget + 1)) := by
    have composed := TMPolyTimeMap.comp K.binaryNatBitLength_tm_polytime successor
    simpa [Function.comp] using composed
  have one : TMPolyTimeMap EncodedType.binaryNat EncodedType.nat
      (fun _budget : Nat => (1 : Nat)) :=
    TMPolyTimeMap.const EncodedType.binaryNat EncodedType.nat (1 : Nat)
  have subtractionInput : TMPolyTimeMap EncodedType.binaryNat
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun budget : Nat => (K.binaryNatBitLength (budget + 1), (1 : Nat))) :=
    TMPolyTimeMap.prod_mk bitLength one
  have composed := TMPolyTimeMap.comp TMPolyTimeMap.nat_sub subtractionInput
  simpa [Function.comp, prefixLengthExecutable] using composed

def prefixFuel (length : Nat) : List Bool :=
  List.replicate length false

theorem prefixFuel_tmPolyTime :
    TMPolyTimeMap EncodedType.nat (EncodedType.list EncodedType.bool) prefixFuel := by
  have units : TMPolyTimeMap EncodedType.nat
      (EncodedType.list (EncodedType.raw Unit))
      (fun length : Nat => List.replicate length ()) :=
    natToRawUnitListTMBackedMap.tm_polytime
  have mapped := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_const (EncodedType.raw Unit) EncodedType.bool false) units
  have functionEquality :
      ((fun units : List Unit => units.map (fun _unit : Unit => false)) ∘
          (fun length : Nat => List.replicate length ())) = prefixFuel := by
    funext length
    simp [Function.comp, prefixFuel]
  rw [← functionEquality]
  exact mapped

def prefixPowersExecutable (budget : Nat) : List Nat :=
  K.binaryPowersFromBits (prefixFuel (prefixLengthExecutable budget))

theorem prefixPowersExecutable_eq (budget : Nat) :
    prefixPowersExecutable budget =
      K.compactBinaryPowers (P.boundedSlackPrefixLength budget) := by
  calc
    prefixPowersExecutable budget =
        K.compactBinaryPowers
          (prefixFuel (prefixLengthExecutable budget)).length :=
      K.binaryPowersFromBits_eq_compactBinaryPowers _
    _ = K.compactBinaryPowers (P.boundedSlackPrefixLength budget) := by
      simp [prefixFuel, prefixLengthExecutable_eq]

theorem prefixPowersExecutable_tmPolyTime :
    TMPolyTimeMap EncodedType.binaryNat binaryNatListEncodedType
      prefixPowersExecutable := by
  have fuel : TMPolyTimeMap EncodedType.binaryNat
      (EncodedType.list EncodedType.bool)
      (fun budget : Nat => prefixFuel (prefixLengthExecutable budget)) := by
    have composed := TMPolyTimeMap.comp prefixFuel_tmPolyTime
      prefixLengthExecutable_tmPolyTime
    simpa [Function.comp] using composed
  have composed := TMPolyTimeMap.comp K.binaryPowersFromBits_tm_polytime fuel
  simpa [Function.comp, prefixPowersExecutable, binaryNatListEncodedType] using composed

def boundedSlackRemainderExecutable (budget : Nat) : Nat :=
  budget - (prefixPowersExecutable budget).sum

theorem boundedSlackRemainderExecutable_eq (budget : Nat) :
    boundedSlackRemainderExecutable budget = P.boundedSlackRemainder budget := by
  rw [boundedSlackRemainderExecutable, prefixPowersExecutable_eq]
  change budget -
      (ComplexityReduction.Karp21.Knapsack.compactBinaryPowers
        (P.boundedSlackPrefixLength budget)).sum =
    budget - (2 ^ P.boundedSlackPrefixLength budget - 1)
  rw [ComplexityReduction.Karp21.Partition.compactBinaryPowers_sum]

theorem boundedSlackRemainderExecutable_tmPolyTime :
    TMPolyTimeMap EncodedType.binaryNat EncodedType.binaryNat
      boundedSlackRemainderExecutable := by
  have identity : TMPolyTimeMap EncodedType.binaryNat EncodedType.binaryNat id :=
    TMPolyTimeMap.id EncodedType.binaryNat
  have prefixSum : TMPolyTimeMap EncodedType.binaryNat EncodedType.binaryNat
      (fun budget : Nat => (prefixPowersExecutable budget).sum) := by
    have composed := TMPolyTimeMap.comp K.binaryNatListSum_tm_polytime_sum
      prefixPowersExecutable_tmPolyTime
    simpa [Function.comp, binaryNatListEncodedType] using composed
  have subtractionInput : TMPolyTimeMap EncodedType.binaryNat
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      (fun budget : Nat => (budget, (prefixPowersExecutable budget).sum)) :=
    TMPolyTimeMap.prod_mk identity prefixSum
  have composed := TMPolyTimeMap.comp K.binaryNatSub_tm_polytime subtractionInput
  simpa [Function.comp, boundedSlackRemainderExecutable] using composed

def slackFinalizeExecutable (payload : List Nat × Nat) : List Nat :=
  match K.binaryNatEqBool (payload.2, 0) with
  | true => payload.1
  | false => payload.1 ++ [payload.2]

theorem slackFinalizeExecutable_eq (payload : List Nat × Nat) :
    slackFinalizeExecutable payload =
      if payload.2 = 0 then payload.1 else payload.1 ++ [payload.2] := by
  by_cases zero : payload.2 = 0
  · have flag : K.binaryNatEqBool (payload.2, 0) = true :=
      (K.binaryNatEqBool_eq_true_iff _).2 zero
    unfold slackFinalizeExecutable
    rw [flag]
    simp [zero]
  · have flag : K.binaryNatEqBool (payload.2, 0) = false := by
      cases value : K.binaryNatEqBool (payload.2, 0)
      · rfl
      · exact False.elim (zero ((K.binaryNatEqBool_eq_true_iff _).1 value))
    unfold slackFinalizeExecutable
    rw [flag]
    simp [zero]

theorem slackFinalizeExecutable_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod binaryNatListEncodedType EncodedType.binaryNat)
      binaryNatListEncodedType slackFinalizeExecutable := by
  let X := EncodedType.prod binaryNatListEncodedType EncodedType.binaryNat
  have payloadIdentity : TMPolyTimeMap X X id := TMPolyTimeMap.id X
  have remainder : TMPolyTimeMap X EncodedType.binaryNat
      (fun payload : List Nat × Nat => payload.2) := by
    simpa [X, binaryNatListEncodedType] using
      TMPolyTimeMap.snd binaryNatListEncodedType EncodedType.binaryNat
  have zero : TMPolyTimeMap X EncodedType.binaryNat
      (fun _payload : List Nat × Nat => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.binaryNat (0 : Nat)
  have equalityInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      (fun payload : List Nat × Nat => (payload.2, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk remainder zero
  have flag : TMPolyTimeMap X EncodedType.bool
      (fun payload : List Nat × Nat => K.binaryNatEqBool (payload.2, 0)) := by
    have composed := TMPolyTimeMap.comp K.binaryNatEqBool_tm_polytime equalityInput
    simpa [Function.comp] using composed
  have branchInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun payload : List Nat × Nat =>
        (K.binaryNatEqBool (payload.2, 0), payload)) :=
    TMPolyTimeMap.prod_mk flag payloadIdentity
  have keepPrefix : TMPolyTimeMap X binaryNatListEncodedType
      (fun payload : List Nat × Nat => payload.1) := by
    simpa [X, binaryNatListEncodedType] using
      TMPolyTimeMap.fst binaryNatListEncodedType EncodedType.binaryNat
  have singletonRemainder : TMPolyTimeMap X binaryNatListEncodedType
      (fun payload : List Nat × Nat => [payload.2]) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton EncodedType.binaryNat) remainder
    simpa [Function.comp, binaryNatListEncodedType] using composed
  have appendInput : TMPolyTimeMap X
      (EncodedType.prod binaryNatListEncodedType binaryNatListEncodedType)
      (fun payload : List Nat × Nat => (payload.1, [payload.2])) :=
    TMPolyTimeMap.prod_mk keepPrefix singletonRemainder
  have appendRemainder : TMPolyTimeMap X binaryNatListEncodedType
      (fun payload : List Nat × Nat => payload.1 ++ [payload.2]) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append EncodedType.binaryNat) appendInput
    simpa [Function.comp, binaryNatListEncodedType] using composed
  have dispatch := boolProduct_dispatch_tm_polytime X
    binaryNatListEncodedType appendRemainder keepPrefix
  have composed := TMPolyTimeMap.comp dispatch branchInput
  simpa [Function.comp, slackFinalizeExecutable, X] using composed

def boundedSlackPowersExecutable (budget : Nat) : List Nat :=
  slackFinalizeExecutable
    (prefixPowersExecutable budget, boundedSlackRemainderExecutable budget)

theorem boundedSlackPowersExecutable_eq (budget : Nat) :
    boundedSlackPowersExecutable budget = P.boundedSlackPowers budget := by
  rw [boundedSlackPowersExecutable, slackFinalizeExecutable_eq,
    prefixPowersExecutable_eq, boundedSlackRemainderExecutable_eq]
  rfl

theorem boundedSlackPowersExecutable_tmPolyTime :
    TMPolyTimeMap EncodedType.binaryNat binaryNatListEncodedType
      boundedSlackPowersExecutable := by
  have payload : TMPolyTimeMap EncodedType.binaryNat
      (EncodedType.prod binaryNatListEncodedType EncodedType.binaryNat)
      (fun budget : Nat =>
        (prefixPowersExecutable budget, boundedSlackRemainderExecutable budget)) :=
    TMPolyTimeMap.prod_mk prefixPowersExecutable_tmPolyTime
      boundedSlackRemainderExecutable_tmPolyTime
  have composed := TMPolyTimeMap.comp slackFinalizeExecutable_tmPolyTime payload
  simpa [Function.comp, boundedSlackPowersExecutable] using composed

/-! ### Source fields and binary arithmetic -/

theorem sourceItems_tmPolyTime :
    TMPolyTimeMap knapsackBinaryStructuredEncodedType itemListEncodedType
      (fun input : KnapsackInput => input.items) := by
  simpa [itemListEncodedType, K.knapsackBinaryItemsForMembership] using
    K.knapsackBinaryItemsTMBackedMap.tm_polytime

theorem sourceBounds_tmPolyTime :
    TMPolyTimeMap knapsackBinaryStructuredEncodedType
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      (fun input : KnapsackInput => (input.capacity, input.targetValue)) := by
  simpa [K.knapsackBinaryBoundsForMembership,
    knapsackBoundsBinaryStructuredEncodedType] using
    K.knapsackBinaryBoundsTMBackedMap.tm_polytime

theorem sourceCapacity_tmPolyTime :
    TMPolyTimeMap knapsackBinaryStructuredEncodedType EncodedType.binaryNat
      (fun input : KnapsackInput => input.capacity) := by
  have composed := TMPolyTimeMap.comp
    (TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.binaryNat)
    sourceBounds_tmPolyTime
  simpa [Function.comp] using composed

theorem sourceTargetValue_tmPolyTime :
    TMPolyTimeMap knapsackBinaryStructuredEncodedType EncodedType.binaryNat
      (fun input : KnapsackInput => input.targetValue) := by
  have composed := TMPolyTimeMap.comp
    (TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryNat)
    sourceBounds_tmPolyTime
  simpa [Function.comp] using composed

theorem itemValueTotal_tmPolyTime :
    TMPolyTimeMap knapsackBinaryStructuredEncodedType EncodedType.binaryNat
      (fun input : KnapsackInput => P.itemValueTotal input.items) := by
  have values : TMPolyTimeMap itemListEncodedType binaryNatListEncodedType
      (fun items : List (Nat × Nat) => items.map Prod.snd) := by
    have element := TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryNat
    simpa [itemEncodedType, itemListEncodedType, binaryNatListEncodedType] using
      TMPolyTimeMap.list_map element
  have valuesFromSource : TMPolyTimeMap knapsackBinaryStructuredEncodedType
      binaryNatListEncodedType
      (fun input : KnapsackInput => input.items.map Prod.snd) := by
    have composed := TMPolyTimeMap.comp values sourceItems_tmPolyTime
    simpa [Function.comp] using composed
  have composed := TMPolyTimeMap.comp K.binaryNatListSum_tm_polytime_sum valuesFromSource
  simpa [Function.comp, P.itemValueTotal] using composed

theorem valueTargetLevel_tmPolyTime :
    TMPolyTimeMap knapsackBinaryStructuredEncodedType EncodedType.binaryNat
      P.valueTargetLevel := by
  have input : TMPolyTimeMap knapsackBinaryStructuredEncodedType
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      (fun source : KnapsackInput =>
        (P.itemValueTotal source.items, source.targetValue)) :=
    TMPolyTimeMap.prod_mk itemValueTotal_tmPolyTime sourceTargetValue_tmPolyTime
  have composed := TMPolyTimeMap.comp K.binaryNatMax_tm_polytime input
  simpa [Function.comp, K.binaryNatMax, P.valueTargetLevel] using composed

theorem valueSlackBudget_tmPolyTime :
    TMPolyTimeMap knapsackBinaryStructuredEncodedType EncodedType.binaryNat
      P.valueSlackBudget := by
  have input : TMPolyTimeMap knapsackBinaryStructuredEncodedType
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      (fun source : KnapsackInput =>
        (P.valueTargetLevel source, source.targetValue)) :=
    TMPolyTimeMap.prod_mk valueTargetLevel_tmPolyTime sourceTargetValue_tmPolyTime
  have composed := TMPolyTimeMap.comp K.binaryNatSub_tm_polytime input
  simpa [Function.comp, P.valueSlackBudget] using composed

theorem compactPartitionBase_tmPolyTime :
    TMPolyTimeMap knapsackBinaryStructuredEncodedType EncodedType.binaryNat
      P.compactPartitionBase := by
  have additionInput : TMPolyTimeMap knapsackBinaryStructuredEncodedType
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      (fun source : KnapsackInput =>
        (P.valueTargetLevel source, P.valueSlackBudget source)) :=
    TMPolyTimeMap.prod_mk valueTargetLevel_tmPolyTime valueSlackBudget_tmPolyTime
  have added : TMPolyTimeMap knapsackBinaryStructuredEncodedType EncodedType.binaryNat
      (fun source : KnapsackInput =>
        P.valueTargetLevel source + P.valueSlackBudget source) := by
    have composed := TMPolyTimeMap.comp K.binaryNatAdd_tm_polytime additionInput
    simpa [Function.comp] using composed
  have composed := TMPolyTimeMap.comp K.binaryNatSucc_tm_polytime added
  simpa [Function.comp, P.compactPartitionBase, Nat.succ_eq_add_one] using composed

/-! ### Context-dependent list maps -/

def encodedItemAtContext (payload : Nat × (Nat × Nat)) : Nat :=
  P.encodedItem payload.1 payload.2

theorem encodedItemAtContext_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.binaryNat itemEncodedType)
      EncodedType.binaryNat encodedItemAtContext := by
  let X := EncodedType.prod EncodedType.binaryNat itemEncodedType
  have base : TMPolyTimeMap X EncodedType.binaryNat
      (fun payload : Nat × (Nat × Nat) => payload.1) := by
    simpa [X, itemEncodedType] using
      TMPolyTimeMap.fst EncodedType.binaryNat itemEncodedType
  have item : TMPolyTimeMap X itemEncodedType
      (fun payload : Nat × (Nat × Nat) => payload.2) := by
    simpa [X, itemEncodedType] using
      TMPolyTimeMap.snd EncodedType.binaryNat itemEncodedType
  have weight : TMPolyTimeMap X EncodedType.binaryNat
      (fun payload : Nat × (Nat × Nat) => payload.2.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.binaryNat) item
    simpa [Function.comp, itemEncodedType, X] using composed
  have value : TMPolyTimeMap X EncodedType.binaryNat
      (fun payload : Nat × (Nat × Nat) => payload.2.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryNat) item
    simpa [Function.comp, itemEncodedType, X] using composed
  have multiplicationInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      (fun payload : Nat × (Nat × Nat) => (payload.1, payload.2.1)) :=
    TMPolyTimeMap.prod_mk base weight
  have multiplied : TMPolyTimeMap X EncodedType.binaryNat
      (fun payload : Nat × (Nat × Nat) => payload.1 * payload.2.1) := by
    have composed := TMPolyTimeMap.comp K.binaryNatMul_tm_polytime multiplicationInput
    simpa [Function.comp] using composed
  have additionInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      (fun payload : Nat × (Nat × Nat) =>
        (payload.1 * payload.2.1, payload.2.2)) :=
    TMPolyTimeMap.prod_mk multiplied value
  have composed := TMPolyTimeMap.comp K.binaryNatAdd_tm_polytime additionInput
  simpa [Function.comp, encodedItemAtContext, P.encodedItem, X] using composed

def encodedItemsExecutable (payload : Nat × List (Nat × Nat)) : List Nat :=
  (Program.contextListMapExecutable
      (C := EncodedType.binaryNat) (X := itemEncodedType) payload).map
    encodedItemAtContext

theorem encodedItemsExecutable_eq (base : Nat) (items : List (Nat × Nat)) :
    encodedItemsExecutable (base, items) = P.encodedItems base items := by
  change
    (Program.contextListMapExecutable
      (C := EncodedType.binaryNat) (X := itemEncodedType) (base, items)).map
        encodedItemAtContext =
      items.map (fun item => P.encodedItem base item)
  rw [Program.contextListMapExecutable_eq_map
    (C := EncodedType.binaryNat) (X := itemEncodedType) base items]
  induction items with
  | nil => rfl
  | cons item items inductionHypothesis =>
      have lifted := congrArg
        (fun tail : List Nat => P.encodedItem base item :: tail)
        inductionHypothesis
      simpa only [List.map_cons, encodedItemAtContext] using lifted

theorem encodedItemsExecutable_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.binaryNat itemListEncodedType)
      binaryNatListEncodedType encodedItemsExecutable := by
  have attached := Program.contextListMapExecutable_tmPolyTime
    EncodedType.binaryNat itemEncodedType
  have mapped := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_map encodedItemAtContext_tmPolyTime) attached
  simpa [Function.comp, encodedItemsExecutable, itemListEncodedType,
    binaryNatListEncodedType] using mapped

def multiplyAtContext (payload : Nat × Nat) : Nat :=
  payload.1 * payload.2

theorem multiplyAtContext_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      EncodedType.binaryNat multiplyAtContext := by
  simpa [multiplyAtContext] using K.binaryNatMul_tm_polytime

def multiplyListExecutable (payload : Nat × List Nat) : List Nat :=
  (Program.contextListMapExecutable
      (C := EncodedType.binaryNat) (X := EncodedType.binaryNat) payload).map
    multiplyAtContext

theorem multiplyListExecutable_eq (base : Nat) (values : List Nat) :
    multiplyListExecutable (base, values) = values.map (fun value => base * value) := by
  change
    (Program.contextListMapExecutable
      (C := EncodedType.binaryNat) (X := EncodedType.binaryNat) (base, values)).map
        multiplyAtContext = values.map (fun value => base * value)
  rw [Program.contextListMapExecutable_eq_map
    (C := EncodedType.binaryNat) (X := EncodedType.binaryNat) base values]
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      have lifted := congrArg
        (fun tail : List Nat => base * value :: tail)
        inductionHypothesis
      simpa only [List.map_cons, multiplyAtContext] using lifted

theorem multiplyListExecutable_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.binaryNat binaryNatListEncodedType)
      binaryNatListEncodedType multiplyListExecutable := by
  have attached := Program.contextListMapExecutable_tmPolyTime
    EncodedType.binaryNat EncodedType.binaryNat
  have mapped := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_map multiplyAtContext_tmPolyTime) attached
  simpa [Function.comp, multiplyListExecutable, binaryNatListEncodedType] using mapped

/-! ### Full compact map -/

theorem compactEncodedItems_tmPolyTime :
    TMPolyTimeMap knapsackBinaryStructuredEncodedType binaryNatListEncodedType
      (fun input : KnapsackInput => P.encodedItems (P.compactPartitionBase input) input.items) := by
  have payload : TMPolyTimeMap knapsackBinaryStructuredEncodedType
      (EncodedType.prod EncodedType.binaryNat itemListEncodedType)
      (fun input : KnapsackInput => (P.compactPartitionBase input, input.items)) :=
    TMPolyTimeMap.prod_mk compactPartitionBase_tmPolyTime sourceItems_tmPolyTime
  have composed := TMPolyTimeMap.comp encodedItemsExecutable_tmPolyTime payload
  convert composed using 1
  funext input
  exact (encodedItemsExecutable_eq (P.compactPartitionBase input) input.items).symm

theorem capacitySlackPowers_tmPolyTime :
    TMPolyTimeMap knapsackBinaryStructuredEncodedType binaryNatListEncodedType
      (fun input : KnapsackInput => P.boundedSlackPowers input.capacity) := by
  have composed := TMPolyTimeMap.comp boundedSlackPowersExecutable_tmPolyTime
    sourceCapacity_tmPolyTime
  convert composed using 1
  funext input
  simp [Function.comp, boundedSlackPowersExecutable_eq]

theorem valueSlackPowers_tmPolyTime :
    TMPolyTimeMap knapsackBinaryStructuredEncodedType binaryNatListEncodedType
      (fun input : KnapsackInput =>
        P.boundedSlackPowers (P.valueSlackBudget input)) := by
  have composed := TMPolyTimeMap.comp boundedSlackPowersExecutable_tmPolyTime
    valueSlackBudget_tmPolyTime
  convert composed using 1
  funext input
  simp [Function.comp, boundedSlackPowersExecutable_eq]

theorem compactWeightSlackWeights_tmPolyTime :
    TMPolyTimeMap knapsackBinaryStructuredEncodedType binaryNatListEncodedType
      P.compactWeightSlackWeights := by
  have payload : TMPolyTimeMap knapsackBinaryStructuredEncodedType
      (EncodedType.prod EncodedType.binaryNat binaryNatListEncodedType)
      (fun input : KnapsackInput =>
        (P.compactPartitionBase input, P.boundedSlackPowers input.capacity)) :=
    TMPolyTimeMap.prod_mk compactPartitionBase_tmPolyTime capacitySlackPowers_tmPolyTime
  have composed := TMPolyTimeMap.comp multiplyListExecutable_tmPolyTime payload
  convert composed using 1
  funext input
  exact (multiplyListExecutable_eq
    (P.compactPartitionBase input) (P.boundedSlackPowers input.capacity)).symm

theorem compactKnapsackSubsetWeights_tmPolyTime :
    TMPolyTimeMap knapsackBinaryStructuredEncodedType binaryNatListEncodedType
      P.compactKnapsackSubsetWeights := by
  have firstPair : TMPolyTimeMap knapsackBinaryStructuredEncodedType
      (EncodedType.prod binaryNatListEncodedType binaryNatListEncodedType)
      (fun input : KnapsackInput =>
        (P.encodedItems (P.compactPartitionBase input) input.items,
          P.compactWeightSlackWeights input)) :=
    TMPolyTimeMap.prod_mk compactEncodedItems_tmPolyTime compactWeightSlackWeights_tmPolyTime
  have firstAppend : TMPolyTimeMap knapsackBinaryStructuredEncodedType
      binaryNatListEncodedType
      (fun input : KnapsackInput =>
        P.encodedItems (P.compactPartitionBase input) input.items ++
          P.compactWeightSlackWeights input) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append EncodedType.binaryNat) firstPair
    simpa [Function.comp, binaryNatListEncodedType] using composed
  have finalPair : TMPolyTimeMap knapsackBinaryStructuredEncodedType
      (EncodedType.prod binaryNatListEncodedType binaryNatListEncodedType)
      (fun input : KnapsackInput =>
        (P.encodedItems (P.compactPartitionBase input) input.items ++
            P.compactWeightSlackWeights input,
          P.boundedSlackPowers (P.valueSlackBudget input))) :=
    TMPolyTimeMap.prod_mk firstAppend valueSlackPowers_tmPolyTime
  have composed := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append EncodedType.binaryNat) finalPair
  simpa [Function.comp, P.compactKnapsackSubsetWeights,
    P.compactValueSlackWeights, binaryNatListEncodedType, List.append_assoc] using composed

theorem compactKnapsackSubsetTarget_tmPolyTime :
    TMPolyTimeMap knapsackBinaryStructuredEncodedType EncodedType.binaryNat
      P.compactKnapsackSubsetTarget := by
  have multiplicationInput : TMPolyTimeMap knapsackBinaryStructuredEncodedType
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      (fun input : KnapsackInput =>
        (P.compactPartitionBase input, input.capacity)) :=
    TMPolyTimeMap.prod_mk compactPartitionBase_tmPolyTime sourceCapacity_tmPolyTime
  have multiplied : TMPolyTimeMap knapsackBinaryStructuredEncodedType EncodedType.binaryNat
      (fun input : KnapsackInput => P.compactPartitionBase input * input.capacity) := by
    have composed := TMPolyTimeMap.comp K.binaryNatMul_tm_polytime multiplicationInput
    simpa [Function.comp] using composed
  have additionInput : TMPolyTimeMap knapsackBinaryStructuredEncodedType
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      (fun input : KnapsackInput =>
        (P.compactPartitionBase input * input.capacity, P.valueTargetLevel input)) :=
    TMPolyTimeMap.prod_mk multiplied valueTargetLevel_tmPolyTime
  have composed := TMPolyTimeMap.comp K.binaryNatAdd_tm_polytime additionInput
  simpa [Function.comp, P.compactKnapsackSubsetTarget] using composed

def subsetToPartitionWeightsExecutable (payload : List Nat × Nat) : List Nat :=
  payload.1 ++ [payload.1.sum, payload.2 + payload.2]

theorem subsetToPartitionWeightsExecutable_eq (weights : List Nat) (target : Nat) :
    subsetToPartitionWeightsExecutable (weights, target) =
      P.subsetToPartitionWeights weights target := by
  change weights ++ [weights.sum, target + target] =
    weights ++ [weights.sum, 2 * target]
  simp [two_mul]

theorem subsetToPartitionWeightsExecutable_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod binaryNatListEncodedType EncodedType.binaryNat)
      binaryNatListEncodedType subsetToPartitionWeightsExecutable := by
  let X := EncodedType.prod binaryNatListEncodedType EncodedType.binaryNat
  have weights : TMPolyTimeMap X binaryNatListEncodedType
      (fun payload : List Nat × Nat => payload.1) := by
    simpa [X, binaryNatListEncodedType] using
      TMPolyTimeMap.fst binaryNatListEncodedType EncodedType.binaryNat
  have target : TMPolyTimeMap X EncodedType.binaryNat
      (fun payload : List Nat × Nat => payload.2) := by
    simpa [X, binaryNatListEncodedType] using
      TMPolyTimeMap.snd binaryNatListEncodedType EncodedType.binaryNat
  have sum : TMPolyTimeMap X EncodedType.binaryNat
      (fun payload : List Nat × Nat => payload.1.sum) := by
    have composed := TMPolyTimeMap.comp K.binaryNatListSum_tm_polytime_sum weights
    simpa [Function.comp] using composed
  have doubleInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      (fun payload : List Nat × Nat => (payload.2, payload.2)) :=
    TMPolyTimeMap.prod_mk target target
  have doubled : TMPolyTimeMap X EncodedType.binaryNat
      (fun payload : List Nat × Nat => payload.2 + payload.2) := by
    have composed := TMPolyTimeMap.comp K.binaryNatAdd_tm_polytime doubleInput
    simpa [Function.comp] using composed
  have doubledSingleton : TMPolyTimeMap X binaryNatListEncodedType
      (fun payload : List Nat × Nat => [payload.2 + payload.2]) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton EncodedType.binaryNat) doubled
    simpa [Function.comp, binaryNatListEncodedType] using composed
  have tailInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.binaryNat binaryNatListEncodedType)
      (fun payload : List Nat × Nat =>
        (payload.1.sum, [payload.2 + payload.2])) :=
    TMPolyTimeMap.prod_mk sum doubledSingleton
  have tail : TMPolyTimeMap X binaryNatListEncodedType
      (fun payload : List Nat × Nat => [payload.1.sum, payload.2 + payload.2]) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_cons EncodedType.binaryNat) tailInput
    simpa [Function.comp, binaryNatListEncodedType] using composed
  have appendInput : TMPolyTimeMap X
      (EncodedType.prod binaryNatListEncodedType binaryNatListEncodedType)
      (fun payload : List Nat × Nat =>
        (payload.1, [payload.1.sum, payload.2 + payload.2])) :=
    TMPolyTimeMap.prod_mk weights tail
  have composed := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append EncodedType.binaryNat) appendInput
  simpa [Function.comp, subsetToPartitionWeightsExecutable,
    binaryNatListEncodedType, X] using composed

def executable (input : sourceProblem.Instance) : targetProblem.Instance :=
  P.partitionInputFromBinaryWeights <|
    subsetToPartitionWeightsExecutable
      (P.compactKnapsackSubsetWeights input, P.compactKnapsackSubsetTarget input)

theorem executable_eq_compactTextbookMap (input : sourceProblem.Instance) :
    executable input = P.compactTextbookMap input := by
  unfold executable
  rw [subsetToPartitionWeightsExecutable_eq]
  rfl

theorem executable_tmPolyTime :
    TMPolyTimeMap knapsackBinaryStructuredEncodedType
      partitionBinaryStructuredEncodedType executable := by
  have payload : TMPolyTimeMap knapsackBinaryStructuredEncodedType
      (EncodedType.prod binaryNatListEncodedType EncodedType.binaryNat)
      (fun input : KnapsackInput =>
        (P.compactKnapsackSubsetWeights input, P.compactKnapsackSubsetTarget input)) :=
    TMPolyTimeMap.prod_mk compactKnapsackSubsetWeights_tmPolyTime
      compactKnapsackSubsetTarget_tmPolyTime
  have weights := TMPolyTimeMap.comp subsetToPartitionWeightsExecutable_tmPolyTime payload
  have output := TMPolyTimeMap.comp
    P.partitionInputFromBinaryWeightsTMBackedMap.tm_polytime weights
  simpa [Function.comp, executable, binaryNatListEncodedType] using output

theorem executableCorrect (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔ targetProblem.accepts (executable input) := by
  change Knapsack input ↔ Partition (executable input)
  rw [executable_eq_compactTextbookMap]
  exact P.compactTextbookMap_correct input

theorem executableDirectTM :
    Agent.Hardness.Authoring.ExecutableDirectTMEvidence
      sourceProblem targetProblem executable := by
  simpa [sourceProblem, targetProblem, sourcePresentation, targetPresentation,
    Presentation.KnapsackBinary.structuredProblem,
    Presentation.KnapsackBinary.structuredPresentation,
    Presentation.PartitionBinary.structuredProblem,
    Presentation.PartitionBinary.structuredPresentation] using executable_tmPolyTime

@[complexity_reduction_ir_typed_primitive]
noncomputable def primitive : Primitive sourcePresentation targetPresentation :=
  Primitive.ofTMPolyTime executable executableDirectTM

@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def certifiedReduction : CertifiedReduction sourceProblem targetProblem where
  program := .atom primitive
  correct := by
    intro input
    change sourceProblem.accepts input ↔ targetProblem.accepts (primitive.run input)
    exact executableCorrect input

@[complexity_reduction_ir_hardness_program_reduction_template]
def template : Agent.Hardness.Authoring.ProgramIndexedReductionTemplate
    .finalComposition sourceProblem targetProblem executable executableDirectTM executableCorrect :=
  ⟨trivial⟩

end KnapsackBinaryToPartitionBinary
end Routes
end ComplexityReduction

assert_standard_axioms
  ComplexityReduction.Routes.KnapsackBinaryToPartitionBinary.prefixLengthExecutable_tmPolyTime,
  ComplexityReduction.Routes.KnapsackBinaryToPartitionBinary.boundedSlackPowersExecutable_tmPolyTime,
  ComplexityReduction.Routes.KnapsackBinaryToPartitionBinary.executableDirectTM,
  ComplexityReduction.Routes.KnapsackBinaryToPartitionBinary.primitive,
  ComplexityReduction.Routes.KnapsackBinaryToPartitionBinary.certifiedReduction,
  ComplexityReduction.Routes.KnapsackBinaryToPartitionBinary.template
