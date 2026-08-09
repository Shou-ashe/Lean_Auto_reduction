import ComplexityReduction.Legacy.ComplexityReduction.Karp21.MaxCut.StructuredTM.EdgeBlocks
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.HittingSet.StructuredRoute
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.InvariantFold

namespace ComplexityReduction
namespace Karp21
namespace MaxCut

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
Pair-to-edge-block instruction generation for the direct structured
Partition-to-MaxCut route.

The source list starts with a weight-list initialization instruction, followed
by strict unordered vertex pairs.  The fold mirrors each strict pair through the
current vertex count and conses the resulting block instruction.  Since the
strict pair generator emits the reverse mirror of Karp's row-major order, consing
restores the textbook order.
-/

def maxCutPairFoldInstructionEncodedType : EncodedType :=
  EncodedType.sum partitionWeightsStructuredEncodedType vertexPairEncodedType

def maxCutPairFoldInstructionListEncodedType : EncodedType :=
  EncodedType.list maxCutPairFoldInstructionEncodedType

def maxCutPairInstructionAccEncodedType : EncodedType :=
  EncodedType.prod partitionWeightsStructuredEncodedType maxCutEdgeBlockInstructionListEncodedType

def maxCutPairInstructionInitAcc :
    maxCutPairInstructionAccEncodedType.Carrier :=
  (([] : List Nat), ([] : List ((Nat × Nat) × Nat)))

def maxCutPairBlockMultiplicity (weights : List Nat) (edge : Nat × Nat) : Nat :=
  4 * weights.getD edge.1 0 * weights.getD edge.2 0

def maxCutPairBlockInstruction (weights : List Nat) (pair : Nat × Nat) :
    maxCutEdgeBlockInstructionEncodedType.Carrier :=
  let edge := mirrorVertexPair weights.length pair
  (edge, maxCutPairBlockMultiplicity weights edge)

def maxCutPairInstructionRightStep
    (p : maxCutPairInstructionAccEncodedType.Carrier × (Nat × Nat)) :
    maxCutPairInstructionAccEncodedType.Carrier :=
  let weights : List Nat := p.1.1
  let out : List ((Nat × Nat) × Nat) := p.1.2
  let edge := mirrorVertexPair weights.length p.2
  (weights, (edge, maxCutPairBlockMultiplicity weights edge) :: out)

def maxCutPairInstructionLeftStep
    (weights : List Nat) : maxCutPairInstructionAccEncodedType.Carrier :=
  (weights, ([] : List ((Nat × Nat) × Nat)))

def maxCutPairInstructionStep
    (p :
      maxCutPairInstructionAccEncodedType.Carrier ×
        maxCutPairFoldInstructionEncodedType.Carrier) :
    maxCutPairInstructionAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl weights => maxCutPairInstructionLeftStep weights
  | Sum.inr pair => maxCutPairInstructionRightStep (p.1, pair)

def maxCutPairFoldInstructions (weights : List Nat) :
    List maxCutPairFoldInstructionEncodedType.Carrier :=
  Sum.inl weights :: (strictNatPairCandidates weights.length).map Sum.inr

def maxCutEdgeBlockInstructionsFromWeights (weights : List Nat) :
    List ((Nat × Nat) × Nat) :=
  (maxCutPairFoldInstructions weights).foldl
      (fun acc instr => maxCutPairInstructionStep (acc, instr))
      maxCutPairInstructionInitAcc |>.2

theorem maxCutPairInstructionFold_pairs_eq
    (weights : List Nat) (pairs : List (Nat × Nat))
    (out : List maxCutEdgeBlockInstructionEncodedType.Carrier) :
    (pairs.map Sum.inr).foldl
        (fun acc instr => maxCutPairInstructionStep (acc, instr))
        (weights, out) =
      (weights, ((pairs.map (maxCutPairBlockInstruction weights)).reverse ++ out)) := by
  induction pairs generalizing out with
  | nil =>
      rfl
  | cons pair pairs ih =>
      change
        (pairs.map Sum.inr).foldl
            (fun acc instr => maxCutPairInstructionStep (acc, instr))
            (maxCutPairInstructionStep ((weights, out), Sum.inr pair)) =
          (weights, (List.map (maxCutPairBlockInstruction weights) (pair :: pairs)).reverse ++ out)
      simp [maxCutPairInstructionStep, maxCutPairInstructionRightStep,
        maxCutPairBlockInstruction]
      simpa [List.append_assoc] using ih ((maxCutPairBlockInstruction weights pair) :: out)

theorem maxCutEdgeBlockInstructionsFromWeights_eq_reverse_map (weights : List Nat) :
    maxCutEdgeBlockInstructionsFromWeights weights =
      ((strictNatPairCandidates weights.length).map
        (maxCutPairBlockInstruction weights)).reverse := by
  unfold maxCutEdgeBlockInstructionsFromWeights maxCutPairFoldInstructions
  rw [List.foldl_cons]
  simpa [maxCutPairInstructionInitAcc, maxCutPairInstructionStep,
    maxCutPairInstructionLeftStep] using
    congrArg Prod.snd
      (maxCutPairInstructionFold_pairs_eq weights
        (strictNatPairCandidates weights.length) [])

theorem maxCutEdgeBlockInstructionsFromWeights_eq_textbookPairs (weights : List Nat) :
    maxCutEdgeBlockInstructionsFromWeights weights =
      (maxCutTextbookPairCandidates weights.length).map
        (fun edge => (edge, maxCutPairBlockMultiplicity weights edge)) := by
  rw [maxCutEdgeBlockInstructionsFromWeights_eq_reverse_map]
  rw [← strictNatPairCandidates_mirror_reverse_eq_textbook weights.length]
  let pairs := strictNatPairCandidates weights.length
  change
    (pairs.map (maxCutPairBlockInstruction weights)).reverse =
      ((pairs.map (mirrorVertexPair weights.length)).reverse).map
        (fun edge => (edge, maxCutPairBlockMultiplicity weights edge))
  calc
    (pairs.map (maxCutPairBlockInstruction weights)).reverse =
        (pairs.map
          (((fun edge => (edge, maxCutPairBlockMultiplicity weights edge)) ∘
            mirrorVertexPair weights.length))).reverse := by
          apply congrArg List.reverse
          apply List.map_congr_left
          intro pair _hp
          rfl
    _ =
        ((pairs.map (mirrorVertexPair weights.length)).map
          (fun edge => (edge, maxCutPairBlockMultiplicity weights edge))).reverse := by
          simp [List.map_map]
    _ =
        ((pairs.map (mirrorVertexPair weights.length)).reverse).map
          (fun edge => (edge, maxCutPairBlockMultiplicity weights edge)) := by
          rw [List.map_reverse]

def vertexPairOffset (offset : Nat) (p : Nat × Nat) : Nat × Nat :=
  (offset + p.1, offset + p.2)

def maxCutRowEdgesFrom (i w j : Nat) (weights : List Nat) : List (Nat × Nat) :=
  (List.range weights.length).flatMap fun k =>
    List.replicate (4 * w * weights.getD k 0) (i, k + j)

theorem maxCutRowEdgesFrom_eq_textbookEdgesFrom
    (i w j : Nat) (weights : List Nat) :
    maxCutRowEdgesFrom i w j weights = textbookEdgesFrom i w j weights := by
  induction weights generalizing j with
  | nil =>
      simp [maxCutRowEdgesFrom, textbookEdgesFrom]
  | cons v vs ih =>
      calc
        maxCutRowEdgesFrom i w j (v :: vs) =
            List.replicate (4 * w * v) (i, j) ++ maxCutRowEdgesFrom i w (j + 1) vs := by
              simp [maxCutRowEdgesFrom, List.range_succ_eq_map, List.flatMap_map,
                Nat.add_comm, Nat.add_left_comm]
        _ = textbookEdgesFrom i w j (v :: vs) := by
              simp [textbookEdgesFrom, ih]

theorem maxCutTextbookPairRow_edges_eq_rowEdgesFrom
    (offset w : Nat) (weights : List Nat) :
    (maxCutTextbookPairRow weights.length).flatMap
        (fun pair =>
          List.replicate (4 * (w :: weights).getD pair.1 0 *
              (w :: weights).getD pair.2 0) (vertexPairOffset offset pair)) =
      maxCutRowEdgesFrom offset w (offset + 1) weights := by
  simp [maxCutTextbookPairRow, maxCutRowEdgesFrom, List.flatMap_map,
    vertexPairOffset, Nat.add_left_comm]

def maxCutTextbookCandidateEdgesFrom (offset : Nat) (weights : List Nat) :
    List (Nat × Nat) :=
  (maxCutTextbookPairCandidates weights.length).flatMap fun pair =>
    List.replicate (4 * weights.getD pair.1 0 * weights.getD pair.2 0)
      (vertexPairOffset offset pair)

theorem maxCutTextbookCandidateEdgesFrom_eq_textbookEdgesFromList
    (offset : Nat) (weights : List Nat) :
    maxCutTextbookCandidateEdgesFrom offset weights =
      textbookEdgesFromList offset weights := by
  induction weights generalizing offset with
  | nil =>
      simp [maxCutTextbookCandidateEdgesFrom, textbookEdgesFromList,
        maxCutTextbookPairCandidates]
  | cons w ws ih =>
      have hRow :=
        maxCutTextbookPairRow_edges_eq_rowEdgesFrom offset w ws
      have hTail :
          ((maxCutTextbookPairCandidates ws.length).map vertexPairShiftSucc).flatMap
              (fun pair =>
                List.replicate (4 * (w :: ws).getD pair.1 0 *
                    (w :: ws).getD pair.2 0) (vertexPairOffset offset pair)) =
            maxCutTextbookCandidateEdgesFrom (offset + 1) ws := by
        simp [maxCutTextbookCandidateEdgesFrom, List.flatMap_map, vertexPairShiftSucc,
          vertexPairOffset, Nat.add_comm, Nat.add_left_comm]
      calc
        maxCutTextbookCandidateEdgesFrom offset (w :: ws) =
            (maxCutTextbookPairRow ws.length).flatMap
                (fun pair =>
                  List.replicate (4 * (w :: ws).getD pair.1 0 *
                      (w :: ws).getD pair.2 0) (vertexPairOffset offset pair)) ++
              ((maxCutTextbookPairCandidates ws.length).map vertexPairShiftSucc).flatMap
                (fun pair =>
                  List.replicate (4 * (w :: ws).getD pair.1 0 *
                      (w :: ws).getD pair.2 0) (vertexPairOffset offset pair)) := by
              simp [maxCutTextbookCandidateEdgesFrom, maxCutTextbookPairCandidates,
                List.flatMap_append]
        _ =
            textbookEdgesFrom offset w (offset + 1) ws ++
              maxCutTextbookCandidateEdgesFrom (offset + 1) ws := by
              rw [hRow, maxCutRowEdgesFrom_eq_textbookEdgesFrom, hTail]
        _ = textbookEdgesFromList offset (w :: ws) := by
              simp [textbookEdgesFromList, ih]

theorem maxCutTextbookEdgesFromWeights_eq_textbookEdges (weights : List Nat) :
    maxCutEdgesFromBlockInstructions
        (maxCutEdgeBlockInstructionsFromWeights weights) =
      textbookEdges weights := by
  rw [maxCutEdgesFromBlockInstructions_eq_flatMap,
    maxCutEdgeBlockInstructionsFromWeights_eq_textbookPairs]
  simpa [maxCutTextbookCandidateEdgesFrom, textbookEdges, vertexPairOffset,
    maxCutPairBlockMultiplicity, List.flatMap_map] using
    maxCutTextbookCandidateEdgesFrom_eq_textbookEdgesFromList 0 weights

/-! ### TM witnesses for one pair-instruction step -/

theorem maxCutPairInstructionLeftStep_tm_polytime :
    TMPolyTimeMap
      partitionWeightsStructuredEncodedType
      maxCutPairInstructionAccEncodedType
      maxCutPairInstructionLeftStep := by
  have hWeights := TMPolyTimeMap.id partitionWeightsStructuredEncodedType
  have hOut :
      TMPolyTimeMap partitionWeightsStructuredEncodedType
        maxCutEdgeBlockInstructionListEncodedType
        (fun _ : List Nat => ([] : List ((Nat × Nat) × Nat))) :=
    TMPolyTimeMap.const partitionWeightsStructuredEncodedType
      maxCutEdgeBlockInstructionListEncodedType []
  have hPair := TMPolyTimeMap.prod_mk hWeights hOut
  simpa [maxCutPairInstructionAccEncodedType, maxCutPairInstructionLeftStep] using hPair

theorem maxCutPairInstructionRightStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod maxCutPairInstructionAccEncodedType vertexPairEncodedType)
      maxCutPairInstructionAccEncodedType
      maxCutPairInstructionRightStep := by
  let X := EncodedType.prod maxCutPairInstructionAccEncodedType vertexPairEncodedType
  have hAcc :
      TMPolyTimeMap X maxCutPairInstructionAccEncodedType
        (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst maxCutPairInstructionAccEncodedType vertexPairEncodedType
  have hRawPair :
      TMPolyTimeMap X vertexPairEncodedType
        (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd maxCutPairInstructionAccEncodedType vertexPairEncodedType
  have hWeights :
      TMPolyTimeMap X partitionWeightsStructuredEncodedType
        (fun p : X.Carrier => p.1.1) := by
    have hFst :=
      TMPolyTimeMap.fst partitionWeightsStructuredEncodedType
        maxCutEdgeBlockInstructionListEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, maxCutPairInstructionAccEncodedType, X] using hComp
  have hOut :
      TMPolyTimeMap X maxCutEdgeBlockInstructionListEncodedType
        (fun p : X.Carrier => p.1.2) := by
    have hSnd :=
      TMPolyTimeMap.snd partitionWeightsStructuredEncodedType
        maxCutEdgeBlockInstructionListEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, maxCutPairInstructionAccEncodedType, X] using hComp
  have hLength :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => p.1.1.length) := by
    have hComp := TMPolyTimeMap.comp
      (HittingSet.listLengthTMBackedMap EncodedType.nat).tm_polytime hWeights
    simpa [Function.comp, partitionWeightsStructuredEncodedType, X] using hComp
  have hMirrorInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat vertexPairEncodedType)
        (fun p : X.Carrier => (p.1.1.length, p.2)) :=
    TMPolyTimeMap.prod_mk hLength hRawPair
  have hEdge :
      TMPolyTimeMap X edgeStructuredEncodedType
        (fun p : X.Carrier => mirrorVertexPair p.1.1.length p.2) := by
    have hComp := TMPolyTimeMap.comp mirrorVertexPair_tm_polytime hMirrorInput
    simpa [Function.comp, X, edgeStructuredEncodedType] using hComp
  have hEdgeLeft :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => (mirrorVertexPair p.1.1.length p.2).1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hEdge
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hEdgeRight :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => (mirrorVertexPair p.1.1.length p.2).2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hEdge
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hLeftLookupInput :
      TMPolyTimeMap X
        (EncodedType.prod partitionWeightsStructuredEncodedType EncodedType.nat)
        (fun p : X.Carrier => (p.1.1, (mirrorVertexPair p.1.1.length p.2).1)) :=
    TMPolyTimeMap.prod_mk hWeights hEdgeLeft
  have hRightLookupInput :
      TMPolyTimeMap X
        (EncodedType.prod partitionWeightsStructuredEncodedType EncodedType.nat)
        (fun p : X.Carrier => (p.1.1, (mirrorVertexPair p.1.1.length p.2).2)) :=
    TMPolyTimeMap.prod_mk hWeights hEdgeRight
  have hLeftWeight :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier =>
          p.1.1.getD (mirrorVertexPair p.1.1.length p.2).1 (0 : Nat)) := by
    have hComp := TMPolyTimeMap.comp natListGetD_tm_polytime hLeftLookupInput
    simpa [Function.comp, natListGetD, X] using hComp
  have hRightWeight :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier =>
          p.1.1.getD (mirrorVertexPair p.1.1.length p.2).2 (0 : Nat)) := by
    have hComp := TMPolyTimeMap.comp natListGetD_tm_polytime hRightLookupInput
    simpa [Function.comp, natListGetD, X] using hComp
  have hFour :
      TMPolyTimeMap X EncodedType.nat
        (fun _ : X.Carrier => (4 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (4 : Nat)
  have hFourLeftInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier =>
          ((4 : Nat), p.1.1.getD (mirrorVertexPair p.1.1.length p.2).1 (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hFour hLeftWeight
  have hFourLeft :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier =>
          (4 : Nat) *
            (show Nat from p.1.1.getD (mirrorVertexPair p.1.1.length p.2).1 (0 : Nat))) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_mul hFourLeftInput
    simpa [Function.comp, X] using hComp
  have hMultiplicityInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier =>
          ((4 : Nat) *
              (show Nat from p.1.1.getD (mirrorVertexPair p.1.1.length p.2).1 (0 : Nat)),
            p.1.1.getD (mirrorVertexPair p.1.1.length p.2).2 (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hFourLeft hRightWeight
  have hMultiplicity :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier =>
          maxCutPairBlockMultiplicity p.1.1 (mirrorVertexPair p.1.1.length p.2)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_mul hMultiplicityInput
    simpa [Function.comp, maxCutPairBlockMultiplicity, X] using hComp
  have hBlockInstruction :
      TMPolyTimeMap X maxCutEdgeBlockInstructionEncodedType
        (fun p : X.Carrier =>
          (mirrorVertexPair p.1.1.length p.2,
            maxCutPairBlockMultiplicity p.1.1 (mirrorVertexPair p.1.1.length p.2))) :=
    TMPolyTimeMap.prod_mk hEdge hMultiplicity
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod maxCutEdgeBlockInstructionEncodedType
          maxCutEdgeBlockInstructionListEncodedType)
        (fun p : X.Carrier =>
          ((mirrorVertexPair p.1.1.length p.2,
              maxCutPairBlockMultiplicity p.1.1 (mirrorVertexPair p.1.1.length p.2)),
            p.1.2)) :=
    TMPolyTimeMap.prod_mk hBlockInstruction hOut
  have hCons :
      TMPolyTimeMap X maxCutEdgeBlockInstructionListEncodedType
        (fun p : X.Carrier =>
          (mirrorVertexPair p.1.1.length p.2,
              maxCutPairBlockMultiplicity p.1.1 (mirrorVertexPair p.1.1.length p.2)) ::
            p.1.2) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_cons maxCutEdgeBlockInstructionEncodedType) hConsInput
    simpa [Function.comp, maxCutEdgeBlockInstructionListEncodedType, X] using hComp
  have hOutAcc := TMPolyTimeMap.prod_mk hWeights hCons
  simpa [maxCutPairInstructionRightStep, maxCutPairBlockMultiplicity,
    maxCutPairInstructionAccEncodedType, X]
    using hOutAcc

theorem maxCutPairInstructionStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod maxCutPairInstructionAccEncodedType
        maxCutPairFoldInstructionEncodedType)
      maxCutPairInstructionAccEncodedType
      maxCutPairInstructionStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      maxCutPairInstructionAccEncodedType partitionWeightsStructuredEncodedType
      vertexPairEncodedType
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim maxCutPairInstructionLeftStep_tm_polytime
      maxCutPairInstructionRightStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

/-! ### Growth bound for the pair-instruction fold -/

def maxCutPairInstructionAccBound
    (N : Nat) (acc : maxCutPairInstructionAccEncodedType.Carrier) : Prop :=
  partitionWeightsStructuredEncodedType.inputSize acc.1 ≤ N

noncomputable def maxCutPairInstructionGrowPolynomial : Polynomial Nat :=
  Polynomial.C 10 * (Polynomial.X * Polynomial.X) +
    Polynomial.C 10 * Polynomial.X + Polynomial.C 20

@[simp] theorem maxCutPairInstructionGrowPolynomial_eval (N : Nat) :
    maxCutPairInstructionGrowPolynomial.eval N = 10 * (N * N) + 10 * N + 20 := by
  simp [maxCutPairInstructionGrowPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

theorem nat_mem_le_sum {x : Nat} {xs : List Nat} (h : x ∈ xs) :
    x ≤ xs.sum := by
  induction xs with
  | nil =>
      cases h
  | cons y ys ih =>
      simp at h ⊢
      rcases h with rfl | hTail
      · omega
      · have hTailLe := ih hTail
        omega

theorem nat_getD_le_sum (xs : List Nat) (i : Nat) :
    xs.getD i 0 ≤ xs.sum := by
  by_cases hi : i < xs.length
  · rw [List.getD_eq_getElem (l := xs) (d := 0) hi]
    have hMem : xs[i] ∈ xs := List.getElem_mem hi
    exact nat_mem_le_sum hMem
  · rw [List.getD_eq_default (l := xs) (d := 0) (n := i) (Nat.le_of_not_gt hi)]
    exact Nat.zero_le _

theorem nat_getD_le_partitionWeights_inputSize (weights : List Nat) (i : Nat) :
    weights.getD i 0 ≤ partitionWeightsStructuredEncodedType.inputSize weights := by
  have hGet := nat_getD_le_sum weights i
  have hSum :
      weights.sum ≤ partitionWeightsStructuredEncodedType.inputSize weights := by
    rw [Partition.partitionWeightsStructured_inputSize_eq]
    omega
  exact hGet.trans hSum

theorem mirrorVertexPair_edge_inputSize_le_of_weights
    (weights : List Nat) (pair : Nat × Nat) {N : Nat}
    (hWeights : partitionWeightsStructuredEncodedType.inputSize weights ≤ N) :
    edgeStructuredEncodedType.inputSize (mirrorVertexPair weights.length pair) ≤
      2 * N + 3 := by
  have hLenRaw := HittingSet.encodedListLength_le_inputSize EncodedType.nat weights
  have hLen : weights.length ≤ N := by
    have hLen' : weights.length ≤ partitionWeightsStructuredEncodedType.inputSize weights := by
      simpa [partitionWeightsStructuredEncodedType] using hLenRaw
    exact hLen'.trans hWeights
  rcases pair with ⟨u, v⟩
  simp [mirrorVertexPair, edgeStructuredEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat]
  omega

theorem maxCutPairBlockInstruction_cons_inputSize_le
    (weights : List Nat) (pair : Nat × Nat) {N : Nat}
    (hWeights : partitionWeightsStructuredEncodedType.inputSize weights ≤ N) :
    maxCutEdgeBlockInstructionEncodedType.inputSize
        (mirrorVertexPair weights.length pair,
          maxCutPairBlockMultiplicity weights (mirrorVertexPair weights.length pair)) + 1 ≤
      maxCutPairInstructionGrowPolynomial.eval N := by
  let edge := mirrorVertexPair weights.length pair
  have hEdge :
      edgeStructuredEncodedType.inputSize edge ≤ 2 * N + 3 := by
    simpa [edge] using mirrorVertexPair_edge_inputSize_le_of_weights weights pair hWeights
  have hLeft :
      weights.getD edge.1 0 ≤ N := by
    exact (nat_getD_le_partitionWeights_inputSize weights edge.1).trans hWeights
  have hRight :
      weights.getD edge.2 0 ≤ N := by
    exact (nat_getD_le_partitionWeights_inputSize weights edge.2).trans hWeights
  have hMult :
      maxCutPairBlockMultiplicity weights edge ≤ 4 * N * N := by
    change 4 * weights.getD edge.1 0 * weights.getD edge.2 0 ≤ 4 * N * N
    have hProd :
        weights.getD edge.1 0 * weights.getD edge.2 0 ≤ N * N :=
      Nat.mul_le_mul hLeft hRight
    have hScaled :
        4 * (weights.getD edge.1 0 * weights.getD edge.2 0) ≤ 4 * (N * N) :=
      Nat.mul_le_mul_left 4 hProd
    simpa [Nat.mul_assoc] using hScaled
  simp [maxCutEdgeBlockInstructionEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat, edge] at hEdge hMult ⊢
  nlinarith

theorem maxCutPairInstructionStep_growth
    (source : List maxCutPairFoldInstructionEncodedType.Carrier)
    (acc : maxCutPairInstructionAccEncodedType.Carrier)
    (instr : maxCutPairFoldInstructionEncodedType.Carrier)
    (hAcc :
      maxCutPairInstructionAccBound
        (maxCutPairFoldInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      maxCutPairFoldInstructionEncodedType.inputSize instr ≤
        maxCutPairFoldInstructionListEncodedType.inputSize source) :
    maxCutPairInstructionAccBound
        (maxCutPairFoldInstructionListEncodedType.inputSize source)
        (maxCutPairInstructionStep (acc, instr)) ∧
      maxCutPairInstructionAccEncodedType.inputSize
          (maxCutPairInstructionStep (acc, instr)) ≤
        maxCutPairInstructionAccEncodedType.inputSize acc +
          maxCutPairInstructionGrowPolynomial.eval
            (maxCutPairFoldInstructionListEncodedType.inputSize source) := by
  let N := maxCutPairFoldInstructionListEncodedType.inputSize source
  cases instr with
  | inl weights =>
      have hWeights : partitionWeightsStructuredEncodedType.inputSize weights ≤ N := by
        have hTagged :
            partitionWeightsStructuredEncodedType.inputSize weights + 1 ≤ N := by
          simpa [maxCutPairFoldInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum, N, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInstr
        exact (Nat.le_succ _).trans hTagged
      constructor
      · simpa [maxCutPairInstructionAccBound, maxCutPairInstructionStep,
          maxCutPairInstructionLeftStep, N] using hWeights
      · have hNil :
            maxCutEdgeBlockInstructionListEncodedType.inputSize
                ([] : List ((Nat × Nat) × Nat)) = 0 := by
          change (EncodedType.list maxCutEdgeBlockInstructionEncodedType).inputSize
              ([] : List ((Nat × Nat) × Nat)) = 0
          exact EncodedType.inputSize_list_nil maxCutEdgeBlockInstructionEncodedType
        simp [maxCutPairInstructionStep, maxCutPairInstructionLeftStep,
          maxCutPairInstructionAccEncodedType, EncodedType.inputSize_prod, hNil]
        nlinarith
  | inr pair =>
      constructor
      · simpa [maxCutPairInstructionAccBound, maxCutPairInstructionStep,
          maxCutPairInstructionRightStep, N] using hAcc
      · let edge := mirrorVertexPair acc.1.length pair
        let block : maxCutEdgeBlockInstructionEncodedType.Carrier :=
          (edge, maxCutPairBlockMultiplicity acc.1 edge)
        have hBlock :
            maxCutEdgeBlockInstructionEncodedType.inputSize block + 1 ≤
              maxCutPairInstructionGrowPolynomial.eval N := by
          simpa [block, edge, N] using
            maxCutPairBlockInstruction_cons_inputSize_le acc.1 pair (N := N) hAcc
        have hCons :
            maxCutEdgeBlockInstructionListEncodedType.inputSize (block :: acc.2) =
              maxCutEdgeBlockInstructionEncodedType.inputSize block + 1 +
                maxCutEdgeBlockInstructionListEncodedType.inputSize acc.2 := by
          change (EncodedType.list maxCutEdgeBlockInstructionEncodedType).inputSize
              (block :: acc.2) =
            maxCutEdgeBlockInstructionEncodedType.inputSize block + 1 +
              (EncodedType.list maxCutEdgeBlockInstructionEncodedType).inputSize acc.2
          exact EncodedType.inputSize_list_cons maxCutEdgeBlockInstructionEncodedType block acc.2
        have hStepEq :
            maxCutPairInstructionStep (acc, Sum.inr pair) = (acc.1, block :: acc.2) := by
          rfl
        have hBlock' :
            maxCutEdgeBlockInstructionEncodedType.inputSize block + 1 ≤
              10 * (N * N) + 10 * N + 20 := by
          simpa [maxCutPairInstructionGrowPolynomial_eval] using hBlock
        rw [hStepEq]
        simp [maxCutPairInstructionAccEncodedType, EncodedType.inputSize_prod, hCons]
        nlinarith [hBlock']

theorem maxCutPairInstructionFold_tm_polytime :
    TMPolyTimeMap
      maxCutPairFoldInstructionListEncodedType
      maxCutPairInstructionAccEncodedType
      (fun xs : List maxCutPairFoldInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => maxCutPairInstructionStep (acc, instr))
          maxCutPairInstructionInitAcc) := by
  rcases maxCutPairInstructionStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      maxCutPairFoldInstructionEncodedType maxCutPairInstructionAccEncodedType
      maxCutPairInstructionStep maxCutPairInstructionInitAcc hStep
      (Polynomial.C 5) maxCutPairInstructionGrowPolynomial
      maxCutPairInstructionAccBound ?_ ?_
  · intro xs
    constructor
    · change partitionWeightsStructuredEncodedType.inputSize ([] : List Nat) ≤
        maxCutPairFoldInstructionListEncodedType.inputSize xs
      have hNil : partitionWeightsStructuredEncodedType.inputSize ([] : List Nat) = 0 := by
        change (EncodedType.list EncodedType.nat).inputSize ([] : List Nat) = 0
        exact EncodedType.inputSize_list_nil EncodedType.nat
      rw [hNil]
      exact Nat.zero_le _
    · have hWeightsNil :
          partitionWeightsStructuredEncodedType.inputSize ([] : List Nat) = 0 := by
        change (EncodedType.list EncodedType.nat).inputSize ([] : List Nat) = 0
        exact EncodedType.inputSize_list_nil EncodedType.nat
      have hInstrNil :
          maxCutEdgeBlockInstructionListEncodedType.inputSize
              ([] : List ((Nat × Nat) × Nat)) = 0 := by
        change (EncodedType.list maxCutEdgeBlockInstructionEncodedType).inputSize
            ([] : List ((Nat × Nat) × Nat)) = 0
        exact EncodedType.inputSize_list_nil maxCutEdgeBlockInstructionEncodedType
      simp [maxCutPairInstructionInitAcc, maxCutPairInstructionAccEncodedType,
        EncodedType.inputSize_prod, hWeightsNil, hInstrNil]
  · intro source acc instr hAcc hInstr
    simpa [maxCutPairFoldInstructionListEncodedType] using
      maxCutPairInstructionStep_growth source acc instr hAcc hInstr

theorem maxCutPairFoldInstructions_tm_polytime :
    TMPolyTimeMap
      partitionWeightsStructuredEncodedType
      maxCutPairFoldInstructionListEncodedType
      maxCutPairFoldInstructions := by
  let X := partitionWeightsStructuredEncodedType
  have hWeights : TMPolyTimeMap X partitionWeightsStructuredEncodedType (fun w : X.Carrier => w) :=
    TMPolyTimeMap.id X
  have hLength :
      TMPolyTimeMap X EncodedType.nat (fun w : X.Carrier => w.length) := by
    have hComp := TMPolyTimeMap.comp
      (HittingSet.listLengthTMBackedMap EncodedType.nat).tm_polytime hWeights
    simpa [Function.comp, X, partitionWeightsStructuredEncodedType] using hComp
  have hPairs :
      TMPolyTimeMap X vertexPairListEncodedType
        (fun w : X.Carrier => strictNatPairCandidates w.length) := by
    have hComp := TMPolyTimeMap.comp strictNatPairCandidates_tm_polytime hLength
    simpa [Function.comp, X] using hComp
  have hInit :
      TMPolyTimeMap X maxCutPairFoldInstructionEncodedType
        (fun w : X.Carrier => Sum.inl w) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.inl partitionWeightsStructuredEncodedType vertexPairEncodedType)
      hWeights
    simpa [Function.comp, maxCutPairFoldInstructionEncodedType, X] using hComp
  have hPairInstruction :
      TMPolyTimeMap vertexPairEncodedType maxCutPairFoldInstructionEncodedType
        (fun p : vertexPairEncodedType.Carrier => Sum.inr p) := by
    simpa [maxCutPairFoldInstructionEncodedType] using
      TMPolyTimeMap.inr partitionWeightsStructuredEncodedType vertexPairEncodedType
  have hMappedPairs :
      TMPolyTimeMap X maxCutPairFoldInstructionListEncodedType
        (fun w : X.Carrier => (strictNatPairCandidates w.length).map Sum.inr) := by
    have hMap := TMPolyTimeMap.list_map hPairInstruction
    have hComp := TMPolyTimeMap.comp hMap hPairs
    simpa [Function.comp, maxCutPairFoldInstructionListEncodedType,
      vertexPairListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod maxCutPairFoldInstructionEncodedType
          maxCutPairFoldInstructionListEncodedType)
        (fun w : X.Carrier => (Sum.inl w, (strictNatPairCandidates w.length).map Sum.inr)) :=
    TMPolyTimeMap.prod_mk hInit hMappedPairs
  have hCons :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons maxCutPairFoldInstructionEncodedType)
      hConsInput
  simpa [Function.comp, maxCutPairFoldInstructions, maxCutPairFoldInstructionListEncodedType,
    X] using hCons

theorem maxCutEdgeBlockInstructionsFromWeights_tm_polytime :
    TMPolyTimeMap
      partitionWeightsStructuredEncodedType
      maxCutEdgeBlockInstructionListEncodedType
      maxCutEdgeBlockInstructionsFromWeights := by
  have hFold :=
    TMPolyTimeMap.comp maxCutPairInstructionFold_tm_polytime
      maxCutPairFoldInstructions_tm_polytime
  have hOut :=
    TMPolyTimeMap.comp
      (TMPolyTimeMap.snd partitionWeightsStructuredEncodedType
        maxCutEdgeBlockInstructionListEncodedType)
      hFold
  simpa [Function.comp, maxCutEdgeBlockInstructionsFromWeights,
    maxCutPairInstructionAccEncodedType] using hOut

theorem maxCutTextbookEdgesFromWeights_tm_polytime :
    TMPolyTimeMap
      partitionWeightsStructuredEncodedType
      edgeListStructuredEncodedType
      (fun weights : List Nat =>
        maxCutEdgesFromBlockInstructions
          (maxCutEdgeBlockInstructionsFromWeights weights)) := by
  have hComp :=
    TMPolyTimeMap.comp maxCutEdgesFromBlockInstructions_tm_polytime
      maxCutEdgeBlockInstructionsFromWeights_tm_polytime
  simpa [Function.comp] using hComp

end MaxCut
end Karp21
end ComplexityReduction
