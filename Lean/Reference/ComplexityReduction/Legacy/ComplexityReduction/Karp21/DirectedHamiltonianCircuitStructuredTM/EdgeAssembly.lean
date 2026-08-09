/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.Semantics
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.HittingSet.StructuredRoute

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

/-! ### First edge-assembly layer: vertex count and incidence arcs -/

def dhcIndexedIncidenceWithBudgetEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat dhcIndexedIncidenceEncodedType

def dhcIndexedIncidenceListWithBudgetEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType

abbrev dhcIndexedIncidenceWithBudgetRaw :=
  Nat × ((Nat × Nat) × Nat)

abbrev dhcIndexedIncidenceListWithBudgetRaw :=
  Nat × List ((Nat × Nat) × Nat)

def dhcVertexCountFromIndexed
    (p : dhcIndexedIncidenceListWithBudgetRaw) : Nat :=
  p.1 + 2 * p.2.length

def dhcIncidenceArcFromIndexed
    (p : dhcIndexedIncidenceWithBudgetRaw) : Nat × Nat :=
  (dhcIncidenceVertexCode (p.1, (p.2.2, 0)),
    dhcIncidenceVertexCode (p.1, (p.2.2, 1)))

def dhcIncidenceArcsFromIndexed
    (p : dhcIndexedIncidenceListWithBudgetRaw) : List (Nat × Nat) :=
  p.2.map fun inc => dhcIncidenceArcFromIndexed (p.1, inc)

def dhcIndexedSourceIncidencesFromInput (I : VertexCoverInput) :
    List ((Nat × Nat) × Nat) :=
  dhcIndexedSourceIncidencesFromGraphData (I.graph.vertices, I.graph.edges)

def dhcVertexCountFromInput (I : VertexCoverInput) : Nat :=
  dhcVertexCountFromIndexed (I.k, dhcIndexedSourceIncidencesFromInput I)

def dhcIncidenceArcsFromInput (I : VertexCoverInput) : List (Nat × Nat) :=
  dhcIncidenceArcsFromIndexed (I.k, dhcIndexedSourceIncidencesFromInput I)

def dhcIncidenceArcsAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat edgeListStructuredEncodedType

def dhcIncidenceArcsInstructionEncodedType : EncodedType :=
  EncodedType.sum EncodedType.nat dhcIndexedIncidenceEncodedType

def dhcIncidenceArcsInstructionListEncodedType : EncodedType :=
  EncodedType.list dhcIncidenceArcsInstructionEncodedType

def dhcIncidenceArcsFoldInit : dhcIncidenceArcsAccEncodedType.Carrier :=
  ((0 : Nat), ([] : List (Nat × Nat)))

def dhcIncidenceArcsFoldLeftStep (budget : Nat) :
    dhcIncidenceArcsAccEncodedType.Carrier :=
  (budget, ([] : List (Nat × Nat)))

def dhcIncidenceArcsFoldRightStep
    (p : dhcIncidenceArcsAccEncodedType.Carrier × ((Nat × Nat) × Nat)) :
    dhcIncidenceArcsAccEncodedType.Carrier :=
  (p.1.1, (show List (Nat × Nat) from p.1.2) ++
    [dhcIncidenceArcFromIndexed (p.1.1, p.2)])

def dhcIncidenceArcsFoldStep
    (p : dhcIncidenceArcsAccEncodedType.Carrier ×
      dhcIncidenceArcsInstructionEncodedType.Carrier) :
    dhcIncidenceArcsAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl budget => dhcIncidenceArcsFoldLeftStep budget
  | Sum.inr inc => dhcIncidenceArcsFoldRightStep (p.1, inc)

def dhcIncidenceArcsInstructions
    (p : dhcIndexedIncidenceListWithBudgetRaw) :
    dhcIncidenceArcsInstructionListEncodedType.Carrier :=
  Sum.inl p.1 :: p.2.map Sum.inr

def dhcIncidenceArcsFoldResult
    (instrs : dhcIncidenceArcsInstructionListEncodedType.Carrier) :
    List (Nat × Nat) :=
  (instrs.foldl (fun acc instr => dhcIncidenceArcsFoldStep (acc, instr))
    dhcIncidenceArcsFoldInit).2

def dhcIncidenceArcsExecutableFromIndexed
    (p : dhcIndexedIncidenceListWithBudgetRaw) : List (Nat × Nat) :=
  dhcIncidenceArcsFoldResult (dhcIncidenceArcsInstructions p)

theorem dhcVertexCountFromIndexed_tm_polytime :
    TMPolyTimeMap dhcIndexedIncidenceListWithBudgetEncodedType EncodedType.nat
      dhcVertexCountFromIndexed := by
  let X := dhcIndexedIncidenceListWithBudgetEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcIndexedIncidenceListWithBudgetEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat dhcIndexedIncidenceListEncodedType
  have hList :
      TMPolyTimeMap X dhcIndexedIncidenceListEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, dhcIndexedIncidenceListWithBudgetEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat dhcIndexedIncidenceListEncodedType
  have hLength : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.length) := by
    have hComp :=
      TMPolyTimeMap.comp
        (HittingSet.listLengthTMBackedMap dhcIndexedIncidenceEncodedType).tm_polytime hList
    simpa [Function.comp, dhcIndexedIncidenceListEncodedType] using hComp
  have hDouble :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => natDouble p.2.length) := by
    have hComp := TMPolyTimeMap.comp natDouble_tm_polytime hLength
    simpa [Function.comp] using hComp
  have hAddInput :
      TMPolyTimeMap X natAddInputEncodedType
        (fun p : X.Carrier => (p.1, natDouble p.2.length)) :=
    TMPolyTimeMap.prod_mk hBudget hDouble
  have hOut := TMPolyTimeMap.comp natAdd_tm_polytime hAddInput
  convert hOut using 1
  funext p
  rcases p with ⟨k, xs⟩
  simp [Function.comp, dhcVertexCountFromIndexed, natDouble, Nat.two_mul]
  rfl

theorem dhcIncidenceArcFromIndexed_tm_polytime :
    TMPolyTimeMap dhcIndexedIncidenceWithBudgetEncodedType edgeStructuredEncodedType
      dhcIncidenceArcFromIndexed := by
  let X := dhcIndexedIncidenceWithBudgetEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcIndexedIncidenceWithBudgetEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat dhcIndexedIncidenceEncodedType
  have hInc :
      TMPolyTimeMap X dhcIndexedIncidenceEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, dhcIndexedIncidenceWithBudgetEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat dhcIndexedIncidenceEncodedType
  have hIdx : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd vertexPairEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hInc
    simpa [Function.comp, dhcIndexedIncidenceEncodedType, X] using hComp
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) := by
    simpa [EncodedType.nat] using TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hOne : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (1 : Nat)) := by
    simpa [EncodedType.nat] using TMPolyTimeMap.const X EncodedType.nat (1 : Nat)
  have hIdxBit0 :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.2, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hIdx hZero
  have hIdxBit1 :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.2, (1 : Nat))) :=
    TMPolyTimeMap.prod_mk hIdx hOne
  have hCode0Input :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat EncodedType.nat))
        (fun p : X.Carrier => (p.1, (p.2.2, (0 : Nat)))) :=
    TMPolyTimeMap.prod_mk hBudget hIdxBit0
  have hCode1Input :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat EncodedType.nat))
        (fun p : X.Carrier => (p.1, (p.2.2, (1 : Nat)))) :=
    TMPolyTimeMap.prod_mk hBudget hIdxBit1
  have hCode0 : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => dhcIncidenceVertexCode (p.1, (p.2.2, (0 : Nat)))) := by
    have hComp := TMPolyTimeMap.comp dhcIncidenceVertexCode_tm_polytime hCode0Input
    simpa [Function.comp] using hComp
  have hCode1 : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => dhcIncidenceVertexCode (p.1, (p.2.2, (1 : Nat)))) := by
    have hComp := TMPolyTimeMap.comp dhcIncidenceVertexCode_tm_polytime hCode1Input
    simpa [Function.comp] using hComp
  have hOut := TMPolyTimeMap.prod_mk hCode0 hCode1
  simpa [dhcIncidenceArcFromIndexed, edgeStructuredEncodedType, X,
    dhcIndexedIncidenceWithBudgetEncodedType] using hOut

theorem dhcIncidenceArcsFoldLeftStep_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      dhcIncidenceArcsAccEncodedType
      dhcIncidenceArcsFoldLeftStep := by
  let X := EncodedType.nat
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p) :=
    TMPolyTimeMap.id X
  have hEmpty :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun _ : X.Carrier => ([] : List (Nat × Nat))) := by
    simpa [edgeListStructuredEncodedType] using
      TMPolyTimeMap.const X edgeListStructuredEncodedType ([] : List (Nat × Nat))
  have hOut := TMPolyTimeMap.prod_mk hBudget hEmpty
  simpa [dhcIncidenceArcsFoldLeftStep, dhcIncidenceArcsAccEncodedType, X] using hOut

theorem dhcIncidenceArcsFoldRightStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod dhcIncidenceArcsAccEncodedType dhcIndexedIncidenceEncodedType)
      dhcIncidenceArcsAccEncodedType
      dhcIncidenceArcsFoldRightStep := by
  let X := EncodedType.prod dhcIncidenceArcsAccEncodedType dhcIndexedIncidenceEncodedType
  have hAcc :
      TMPolyTimeMap X dhcIncidenceArcsAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst dhcIncidenceArcsAccEncodedType
      dhcIndexedIncidenceEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, dhcIncidenceArcsAccEncodedType, X] using hComp
  have hOutEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, dhcIncidenceArcsAccEncodedType, X] using hComp
  have hInc :
      TMPolyTimeMap X dhcIndexedIncidenceEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd dhcIncidenceArcsAccEncodedType
      dhcIndexedIncidenceEncodedType
  have hArcInput :
      TMPolyTimeMap X dhcIndexedIncidenceWithBudgetEncodedType
        (fun p : X.Carrier => (p.1.1, p.2)) :=
    TMPolyTimeMap.prod_mk hBudget hInc
  have hArc : TMPolyTimeMap X edgeStructuredEncodedType
      (fun p : X.Carrier => dhcIncidenceArcFromIndexed (p.1.1, p.2)) := by
    have hComp := TMPolyTimeMap.comp dhcIncidenceArcFromIndexed_tm_polytime hArcInput
    simpa [Function.comp, dhcIndexedIncidenceWithBudgetEncodedType, X] using hComp
  have hSingleton :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier => [dhcIncidenceArcFromIndexed (p.1.1, p.2)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton edgeStructuredEncodedType) hArc
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier =>
          (p.1.2, [dhcIncidenceArcFromIndexed (p.1.1, p.2)])) :=
    TMPolyTimeMap.prod_mk hOutEdges hSingleton
  have hAppend : TMPolyTimeMap X edgeListStructuredEncodedType
      (fun p : X.Carrier =>
        (show List (Nat × Nat) from p.1.2) ++
          [dhcIncidenceArcFromIndexed (p.1.1, p.2)]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append edgeStructuredEncodedType) hAppendInput
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hOut := TMPolyTimeMap.prod_mk hBudget hAppend
  simpa [dhcIncidenceArcsFoldRightStep, dhcIncidenceArcsAccEncodedType, X] using hOut

theorem dhcIncidenceArcsFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod dhcIncidenceArcsAccEncodedType
        dhcIncidenceArcsInstructionEncodedType)
      dhcIncidenceArcsAccEncodedType
      dhcIncidenceArcsFoldStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      dhcIncidenceArcsAccEncodedType EncodedType.nat dhcIndexedIncidenceEncodedType
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim dhcIncidenceArcsFoldLeftStep_tm_polytime
      dhcIncidenceArcsFoldRightStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem dhcIncidenceArcsInstructions_tm_polytime :
    TMPolyTimeMap dhcIndexedIncidenceListWithBudgetEncodedType
      dhcIncidenceArcsInstructionListEncodedType
      dhcIncidenceArcsInstructions := by
  let X := dhcIndexedIncidenceListWithBudgetEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcIndexedIncidenceListWithBudgetEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat dhcIndexedIncidenceListEncodedType
  have hList :
      TMPolyTimeMap X dhcIndexedIncidenceListEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, dhcIndexedIncidenceListWithBudgetEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat dhcIndexedIncidenceListEncodedType
  have hInit :
      TMPolyTimeMap X dhcIncidenceArcsInstructionEncodedType
        (fun p : X.Carrier => Sum.inl p.1) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.inl EncodedType.nat dhcIndexedIncidenceEncodedType) hBudget
    simpa [Function.comp, dhcIncidenceArcsInstructionEncodedType, X] using hComp
  have hElemInstrs :
      TMPolyTimeMap X dhcIncidenceArcsInstructionListEncodedType
        (fun p : X.Carrier => p.2.map Sum.inr) := by
    have hMap :=
      TMPolyTimeMap.list_map
        (TMPolyTimeMap.inr EncodedType.nat dhcIndexedIncidenceEncodedType)
    have hComp := TMPolyTimeMap.comp hMap hList
    simpa [Function.comp, dhcIndexedIncidenceListEncodedType,
      dhcIncidenceArcsInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod dhcIncidenceArcsInstructionEncodedType
          dhcIncidenceArcsInstructionListEncodedType)
        (fun p : X.Carrier => (Sum.inl p.1, p.2.map Sum.inr)) :=
    TMPolyTimeMap.prod_mk hInit hElemInstrs
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons dhcIncidenceArcsInstructionEncodedType) hConsInput
  simpa [Function.comp, dhcIncidenceArcsInstructions,
    dhcIncidenceArcsInstructionListEncodedType, X,
    dhcIndexedIncidenceListWithBudgetEncodedType] using hOut

def dhcIncidenceArcsFoldAccBound
    (N : Nat) (acc : dhcIncidenceArcsAccEncodedType.Carrier) : Prop :=
  EncodedType.nat.inputSize acc.1 ≤ N + 1

noncomputable def dhcIncidenceArcsFoldGrowPolynomial : Polynomial Nat :=
  Polynomial.C 10 * Polynomial.X + Polynomial.C 20

theorem dhcIncidenceArcsFoldGrowPolynomial_eval (N : Nat) :
    dhcIncidenceArcsFoldGrowPolynomial.eval N = 10 * N + 20 := by
  simp [dhcIncidenceArcsFoldGrowPolynomial, Polynomial.eval_add, Polynomial.eval_mul]

theorem dhcIncidenceArcSingleton_inputSize_le
    (N k u i idx : Nat)
    (hK : EncodedType.nat.inputSize k ≤ N + 1)
    (hIdx : EncodedType.nat.inputSize idx ≤ N + 1) :
    edgeListStructuredEncodedType.inputSize
        [dhcIncidenceArcFromIndexed (k, ((u, i), idx))] ≤
      10 * N + 20 := by
  have hKNat : k ≤ N := by
    simpa [EncodedType.inputSize_nat] using hK
  have hIdxNat : idx ≤ N := by
    simpa [EncodedType.inputSize_nat] using hIdx
  simp [edgeListStructuredEncodedType, edgeStructuredEncodedType, dhcIncidenceArcFromIndexed,
    dhcIncidenceVertexCode, EncodedType.inputSize_prod, EncodedType.inputSize_nat, natDouble]
  nlinarith

theorem dhcIncidenceArcsFoldStep_growth
    (source : List dhcIncidenceArcsInstructionEncodedType.Carrier)
    (acc : dhcIncidenceArcsAccEncodedType.Carrier)
    (instr : dhcIncidenceArcsInstructionEncodedType.Carrier)
    (hAcc :
      dhcIncidenceArcsFoldAccBound
        (dhcIncidenceArcsInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      dhcIncidenceArcsInstructionEncodedType.inputSize instr ≤
        dhcIncidenceArcsInstructionListEncodedType.inputSize source) :
    dhcIncidenceArcsFoldAccBound
        (dhcIncidenceArcsInstructionListEncodedType.inputSize source)
        (dhcIncidenceArcsFoldStep (acc, instr)) ∧
      dhcIncidenceArcsAccEncodedType.inputSize (dhcIncidenceArcsFoldStep (acc, instr)) ≤
        dhcIncidenceArcsAccEncodedType.inputSize acc +
          dhcIncidenceArcsFoldGrowPolynomial.eval
            (dhcIncidenceArcsInstructionListEncodedType.inputSize source) := by
  let N := dhcIncidenceArcsInstructionListEncodedType.inputSize source
  cases instr with
  | inl budget =>
      change Nat at budget
      have hBudgetTagged :
          EncodedType.nat.inputSize budget + 1 ≤ N := by
        simpa [dhcIncidenceArcsInstructionEncodedType, EncodedType.inputSize,
          EncodedType.sum, N, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInstr
      have hBudget : EncodedType.nat.inputSize budget ≤ N + 1 := by
        omega
      have hBudgetNat : budget ≤ N := by
        simpa [EncodedType.inputSize_nat] using hBudget
      constructor
      · simpa [dhcIncidenceArcsFoldAccBound, dhcIncidenceArcsFoldStep,
          dhcIncidenceArcsFoldLeftStep, N] using hBudget
      · have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
          exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
        simp [dhcIncidenceArcsFoldStep, dhcIncidenceArcsFoldLeftStep,
          dhcIncidenceArcsAccEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat, hNil, dhcIncidenceArcsFoldGrowPolynomial_eval]
        omega
  | inr inc =>
      rcases inc with ⟨ui, idx⟩
      rcases ui with ⟨u, i⟩
      change Nat at idx
      change Nat at u
      change Nat at i
      have hBudget : EncodedType.nat.inputSize acc.1 ≤ N + 1 := by
        simpa [dhcIncidenceArcsFoldAccBound, N] using hAcc
      have hIncInput : dhcIndexedIncidenceEncodedType.inputSize ((u, i), idx) ≤ N := by
        have hTagged : dhcIndexedIncidenceEncodedType.inputSize ((u, i), idx) + 1 ≤ N := by
          simpa [dhcIncidenceArcsInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum, N, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInstr
        omega
      have hIdxPayload :
          EncodedType.nat.inputSize idx ≤
            dhcIndexedIncidenceEncodedType.inputSize ((u, i), idx) := by
        simp [dhcIndexedIncidenceEncodedType, vertexPairEncodedType,
          EncodedType.inputSize_prod]
      have hIdx : EncodedType.nat.inputSize idx ≤ N + 1 := by
        exact (hIdxPayload.trans hIncInput).trans (Nat.le_succ N)
      let out : List (Nat × Nat) := acc.2
      have hAppend :
          edgeListStructuredEncodedType.inputSize
              (out ++ [dhcIncidenceArcFromIndexed (acc.1, ((u, i), idx))]) =
            edgeListStructuredEncodedType.inputSize out +
              edgeListStructuredEncodedType.inputSize
                [dhcIncidenceArcFromIndexed (acc.1, ((u, i), idx))] := by
        simpa [edgeListStructuredEncodedType] using
          Clique.encodedList_inputSize_append edgeStructuredEncodedType out
            [dhcIncidenceArcFromIndexed (acc.1, ((u, i), idx))]
      constructor
      · simpa [dhcIncidenceArcsFoldAccBound, dhcIncidenceArcsFoldStep,
          dhcIncidenceArcsFoldRightStep, N] using hBudget
      · have hSingleton :
            edgeListStructuredEncodedType.inputSize
                [dhcIncidenceArcFromIndexed (acc.1, ((u, i), idx))] ≤
              10 * N + 20 :=
          dhcIncidenceArcSingleton_inputSize_le N acc.1 u i idx hBudget hIdx
        simp [dhcIncidenceArcsFoldStep, dhcIncidenceArcsFoldRightStep,
          dhcIncidenceArcsAccEncodedType, EncodedType.inputSize_prod,
          dhcIncidenceArcsFoldGrowPolynomial_eval]
        change (show Nat from acc.1) + 1 + 1 +
              edgeListStructuredEncodedType.inputSize
                (out ++ [dhcIncidenceArcFromIndexed (acc.1, ((u, i), idx))]) ≤
            (show Nat from acc.1) + 1 + 1 + edgeListStructuredEncodedType.inputSize out +
              (10 * dhcIncidenceArcsInstructionListEncodedType.inputSize source + 20)
        rw [hAppend]
        omega

theorem dhcIncidenceArcsFold_tm_polytime :
    TMPolyTimeMap
      dhcIncidenceArcsInstructionListEncodedType
      dhcIncidenceArcsAccEncodedType
      (fun xs : List dhcIncidenceArcsInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => dhcIncidenceArcsFoldStep (acc, instr))
          dhcIncidenceArcsFoldInit) := by
  rcases dhcIncidenceArcsFoldStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      dhcIncidenceArcsInstructionEncodedType dhcIncidenceArcsAccEncodedType
      dhcIncidenceArcsFoldStep dhcIncidenceArcsFoldInit hStep
      (Polynomial.C 10) dhcIncidenceArcsFoldGrowPolynomial
      dhcIncidenceArcsFoldAccBound ?_ ?_
  · intro xs
    constructor
    · simp [dhcIncidenceArcsFoldAccBound, dhcIncidenceArcsFoldInit,
        EncodedType.inputSize_nat]
    · have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
        exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
      simp [dhcIncidenceArcsFoldInit, dhcIncidenceArcsAccEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_nat, hNil]
  · intro source acc instr hAcc hInstr
    simpa [dhcIncidenceArcsInstructionListEncodedType] using
      dhcIncidenceArcsFoldStep_growth source acc instr hAcc hInstr

theorem dhcIncidenceArcsFoldResult_tm_polytime :
    TMPolyTimeMap
      dhcIncidenceArcsInstructionListEncodedType
      edgeListStructuredEncodedType
      dhcIncidenceArcsFoldResult := by
  have hSnd := TMPolyTimeMap.snd EncodedType.nat edgeListStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hSnd dhcIncidenceArcsFold_tm_polytime
  simpa [Function.comp, dhcIncidenceArcsFoldResult, dhcIncidenceArcsAccEncodedType] using hComp

theorem dhcIncidenceArcsExecutableFromIndexed_tm_polytime :
    TMPolyTimeMap
      dhcIndexedIncidenceListWithBudgetEncodedType
      edgeListStructuredEncodedType
      dhcIncidenceArcsExecutableFromIndexed := by
  have hComp :=
    TMPolyTimeMap.comp dhcIncidenceArcsFoldResult_tm_polytime
      dhcIncidenceArcsInstructions_tm_polytime
  simpa [Function.comp, dhcIncidenceArcsExecutableFromIndexed] using hComp

theorem dhcIncidenceArcsFold_map_invariant
    (budget : Nat) (xs : List ((Nat × Nat) × Nat)) (out : List (Nat × Nat)) :
    (xs.map Sum.inr).foldl
        (fun acc instr => dhcIncidenceArcsFoldStep (acc, instr))
        (budget, out) =
      (budget, out ++ xs.map fun inc => dhcIncidenceArcFromIndexed (budget, inc)) := by
  induction xs generalizing out with
  | nil =>
      change (budget, out) = (budget, out ++ ([] : List (Nat × Nat)))
      simp
  | cons inc xs ih =>
      change
        (xs.map Sum.inr).foldl
            (fun acc instr => dhcIncidenceArcsFoldStep (acc, instr))
            (dhcIncidenceArcsFoldStep ((budget, out), Sum.inr inc)) =
          (budget,
            out ++
              dhcIncidenceArcFromIndexed (budget, inc) ::
                xs.map fun inc => dhcIncidenceArcFromIndexed (budget, inc))
      rw [show dhcIncidenceArcsFoldStep ((budget, out), Sum.inr inc) =
          (budget, out ++ [dhcIncidenceArcFromIndexed (budget, inc)]) by rfl]
      calc
        (xs.map Sum.inr).foldl
            (fun acc instr => dhcIncidenceArcsFoldStep (acc, instr))
            (budget, out ++ [dhcIncidenceArcFromIndexed (budget, inc)])
            =
          (budget,
            (out ++ [dhcIncidenceArcFromIndexed (budget, inc)]) ++
              xs.map fun inc => dhcIncidenceArcFromIndexed (budget, inc)) :=
            ih (out ++ [dhcIncidenceArcFromIndexed (budget, inc)])
        _ =
          (budget,
            out ++
              dhcIncidenceArcFromIndexed (budget, inc) ::
                xs.map fun inc => dhcIncidenceArcFromIndexed (budget, inc)) := by
            simp [List.append_assoc]

theorem dhcIncidenceArcsExecutableFromIndexed_eq
    (p : dhcIndexedIncidenceListWithBudgetRaw) :
    dhcIncidenceArcsExecutableFromIndexed p =
      dhcIncidenceArcsFromIndexed p := by
  rcases p with ⟨budget, xs⟩
  rw [dhcIncidenceArcsExecutableFromIndexed, dhcIncidenceArcsFoldResult,
    dhcIncidenceArcsInstructions]
  rw [List.foldl_cons]
  rw [show dhcIncidenceArcsFoldStep (dhcIncidenceArcsFoldInit, Sum.inl budget) =
      (budget, ([] : List (Nat × Nat))) by rfl]
  change (List.foldl
      (fun acc instr => dhcIncidenceArcsFoldStep (acc, instr))
      (budget, []) (List.map Sum.inr xs)).2 =
    dhcIncidenceArcsFromIndexed (budget, xs)
  have hFold :=
    congrArg Prod.snd
      (dhcIncidenceArcsFold_map_invariant budget xs ([] : List (Nat × Nat)))
  simpa [dhcIncidenceArcsFromIndexed] using hFold

theorem dhcIndexedSourceIncidencesFromInput_eq
    (I : VertexCoverInput) :
    dhcIndexedSourceIncidencesFromInput I =
      dhcIndexedSourceIncidencesFromGraphData
        (I.graph.vertices, I.graph.edges) := by
  rfl

theorem dhcVertexCountFromInput_eq_textbookVertexCount
    (I : VertexCoverInput) :
    dhcVertexCountFromInput I = textbookVertexCount I := by
  simp [dhcVertexCountFromInput, dhcVertexCountFromIndexed,
    dhcIndexedSourceIncidencesFromInput,
    dhcIndexedSourceIncidencesFromInput_eq_zipIdx_sourceIncidences,
    textbookVertexCount]

theorem dhcIncidenceArcFromIndexed_eq_textbook_of_mem
    (I : VertexCoverInput) {u i idx : Nat}
    (hMem : ((u, i), idx) ∈ dhcIndexedSourceIncidencesFromInput I) :
    dhcIncidenceArcFromIndexed (I.k, ((u, i), idx)) =
      (textbookIncidenceVertex I u i 0,
        textbookIncidenceVertex I u i 1) := by
  have hMem' :
      ((u, i), idx) ∈
        dhcIndexedSourceIncidencesFromGraphData
          (I.graph.vertices, I.graph.edges) := by
    simpa [dhcIndexedSourceIncidencesFromInput] using hMem
  ext <;>
    simp [dhcIncidenceArcFromIndexed,
      dhcIncidenceVertexCode_eq_textbookIncidenceVertex_of_mem I hMem']

theorem dhcIncidenceArcsFromInput_eq_textbookIncidenceArcs
    (I : VertexCoverInput) :
    dhcIncidenceArcsFromInput I = textbookIncidenceArcs I := by
  rw [dhcIncidenceArcsFromInput, dhcIncidenceArcsFromIndexed,
    dhcIndexedSourceIncidencesFromInput,
    dhcIndexedSourceIncidencesFromInput_eq_zipIdx_sourceIncidences]
  rw [textbookIncidenceArcs]
  conv_rhs =>
    rw [← List.zipIdx_map_fst 0 (sourceIncidences I), List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro x hx
  rcases x with ⟨ui, idx⟩
  rcases ui with ⟨u, i⟩
  have hMem :
      ((u, i), idx) ∈ dhcIndexedSourceIncidencesFromInput I := by
    simpa [dhcIndexedSourceIncidencesFromInput,
      dhcIndexedSourceIncidencesFromInput_eq_zipIdx_sourceIncidences] using hx
  simpa using dhcIncidenceArcFromIndexed_eq_textbook_of_mem I hMem

/-! ### Edge-list assembly from the indexed source-incidence list -/

def dhcSourceIncidencesFromIndexed
    (xs : List ((Nat × Nat) × Nat)) : List (Nat × Nat) :=
  xs.map Prod.fst

theorem dhcSourceIncidencesFromIndexed_tm_polytime :
    TMPolyTimeMap dhcIndexedIncidenceListEncodedType
      (EncodedType.list vertexPairEncodedType)
      dhcSourceIncidencesFromIndexed := by
  have hFst :
      TMPolyTimeMap dhcIndexedIncidenceEncodedType vertexPairEncodedType
        (fun inc : dhcIndexedIncidenceEncodedType.Carrier => inc.1) := by
    simpa [dhcIndexedIncidenceEncodedType] using
      TMPolyTimeMap.fst vertexPairEncodedType EncodedType.nat
  have hMap := TMPolyTimeMap.list_map hFst
  simpa [dhcSourceIncidencesFromIndexed, dhcIndexedIncidenceListEncodedType] using hMap

def dhcIncidenceVertexFromSourceList
    (budget : Nat) (source : List (Nat × Nat)) (ui : Nat × Nat) (bit : Nat) : Nat :=
  dhcIncidenceVertexCode (budget, (source.idxOf ui, bit))

noncomputable def dhcCrossArcsFromSourceList
    (budget : Nat) (source : List (Nat × Nat)) : List (Nat × Nat) := by
  classical
  exact ((((source.product source).filter fun pair =>
    decide (pair.1.2 = pair.2.2 ∧ pair.1.1 ≠ pair.2.1)).map fun pair =>
      [ (dhcIncidenceVertexFromSourceList budget source pair.1 0,
          dhcIncidenceVertexFromSourceList budget source pair.2 0)
      , (dhcIncidenceVertexFromSourceList budget source pair.1 1,
          dhcIncidenceVertexFromSourceList budget source pair.2 1)
      ]).flatten)

noncomputable def dhcChainArcsFromSourceList
    (I : VertexCoverInput) (source : List (Nat × Nat)) : List (Nat × Nat) := by
  classical
  exact (((source.product source).filter fun pair =>
    decide (pair.1.1 = pair.2.1 ∧ ConsecutiveIncident I pair.1.1 pair.1.2 pair.2.2)).map
    fun pair =>
      (dhcIncidenceVertexFromSourceList I.k source pair.1 1,
        dhcIncidenceVertexFromSourceList I.k source pair.2 0))

noncomputable def dhcEntryArcsFromSourceList
    (I : VertexCoverInput) (source : List (Nat × Nat)) : List (Nat × Nat) := by
  classical
  exact (((List.range I.k).product source).filter fun pair =>
    decide (FirstIncident I pair.2.1 pair.2.2)).map fun pair =>
      (textbookSelectorVertex pair.1,
        dhcIncidenceVertexFromSourceList I.k source pair.2 0)

noncomputable def dhcExitArcsFromSourceList
    (I : VertexCoverInput) (source : List (Nat × Nat)) : List (Nat × Nat) := by
  classical
  exact (((List.range I.k).product source).filter fun pair =>
    decide (LastIncident I pair.2.1 pair.2.2)).map fun pair =>
      (dhcIncidenceVertexFromSourceList I.k source pair.2 1,
        textbookSelectorVertex (textbookNextSelector I pair.1))

noncomputable def dhcCrossArcsFromIndexed
    (p : dhcIndexedIncidenceListWithBudgetRaw) : List (Nat × Nat) :=
  dhcCrossArcsFromSourceList p.1 (dhcSourceIncidencesFromIndexed p.2)

noncomputable def dhcChainArcsFromIndexed
    (I : VertexCoverInput) (xs : List ((Nat × Nat) × Nat)) : List (Nat × Nat) :=
  dhcChainArcsFromSourceList I (dhcSourceIncidencesFromIndexed xs)

noncomputable def dhcEntryArcsFromIndexed
    (I : VertexCoverInput) (xs : List ((Nat × Nat) × Nat)) : List (Nat × Nat) :=
  dhcEntryArcsFromSourceList I (dhcSourceIncidencesFromIndexed xs)

noncomputable def dhcExitArcsFromIndexed
    (I : VertexCoverInput) (xs : List ((Nat × Nat) × Nat)) : List (Nat × Nat) :=
  dhcExitArcsFromSourceList I (dhcSourceIncidencesFromIndexed xs)

noncomputable def dhcCrossArcsFromInput (I : VertexCoverInput) : List (Nat × Nat) :=
  dhcCrossArcsFromIndexed (I.k, dhcIndexedSourceIncidencesFromInput I)

noncomputable def dhcChainArcsFromInput (I : VertexCoverInput) : List (Nat × Nat) :=
  dhcChainArcsFromIndexed I (dhcIndexedSourceIncidencesFromInput I)

def dhcSelectorSkipArcsFromInput (I : VertexCoverInput) : List (Nat × Nat) :=
  (List.range I.k).map fun slot =>
    (textbookSelectorVertex slot, textbookSelectorVertex (textbookNextSelector I slot))

noncomputable def dhcEntryArcsFromInput (I : VertexCoverInput) : List (Nat × Nat) :=
  dhcEntryArcsFromIndexed I (dhcIndexedSourceIncidencesFromInput I)

noncomputable def dhcExitArcsFromInput (I : VertexCoverInput) : List (Nat × Nat) :=
  dhcExitArcsFromIndexed I (dhcIndexedSourceIncidencesFromInput I)

noncomputable def dhcTrackChainArcsFromInput (I : VertexCoverInput) : List (Nat × Nat) :=
  textbookTrackChainArcs I

noncomputable def dhcTrackEntryArcsFromInput (I : VertexCoverInput) : List (Nat × Nat) :=
  textbookTrackEntryArcs I

noncomputable def dhcTrackExitArcsFromInput (I : VertexCoverInput) : List (Nat × Nat) :=
  textbookTrackExitArcs I

noncomputable def dhcEdgeListFromInput (I : VertexCoverInput) : List (Nat × Nat) :=
  dhcIncidenceArcsFromInput I ++
    dhcCrossArcsFromInput I ++
    dhcChainArcsFromInput I ++
    dhcTrackChainArcsFromInput I ++
    dhcSelectorSkipArcsFromInput I ++
    dhcEntryArcsFromInput I ++
    dhcExitArcsFromInput I ++
    dhcTrackEntryArcsFromInput I ++
    dhcTrackExitArcsFromInput I

theorem dhcSourceIncidencesFromIndexed_input_eq_sourceIncidences
    (I : VertexCoverInput) :
    dhcSourceIncidencesFromIndexed (dhcIndexedSourceIncidencesFromInput I) =
      sourceIncidences I := by
  simp [dhcSourceIncidencesFromIndexed, dhcIndexedSourceIncidencesFromInput,
    dhcIndexedSourceIncidencesFromInput_eq_zipIdx_sourceIncidences]

theorem dhcIncidenceVertexFromSourceIncidences_eq_textbook
    (I : VertexCoverInput) (ui : Nat × Nat) (bit : Nat) :
    dhcIncidenceVertexFromSourceList I.k (sourceIncidences I) ui bit =
      textbookIncidenceVertex I ui.1 ui.2 bit := by
  simp [dhcIncidenceVertexFromSourceList, dhcIncidenceVertexCode, textbookIncidenceVertex,
    natDouble]
  omega

theorem dhcCrossArcsFromInput_eq_textbookCrossArcs
    (I : VertexCoverInput) :
    dhcCrossArcsFromInput I = textbookCrossArcs I := by
  simp [dhcCrossArcsFromInput, dhcCrossArcsFromIndexed,
    dhcSourceIncidencesFromIndexed_input_eq_sourceIncidences,
    dhcCrossArcsFromSourceList, textbookCrossArcs,
    dhcIncidenceVertexFromSourceIncidences_eq_textbook]

theorem dhcChainArcsFromInput_eq_textbookChainArcs
    (I : VertexCoverInput) :
    dhcChainArcsFromInput I = textbookChainArcs I := by
  simp [dhcChainArcsFromInput, dhcChainArcsFromIndexed,
    dhcSourceIncidencesFromIndexed_input_eq_sourceIncidences,
    dhcChainArcsFromSourceList, textbookChainArcs,
    dhcIncidenceVertexFromSourceIncidences_eq_textbook]

theorem dhcSelectorSkipArcsFromInput_eq_textbookSelectorSkipArcs
    (I : VertexCoverInput) :
    dhcSelectorSkipArcsFromInput I = textbookSelectorSkipArcs I := by
  rfl

theorem dhcEntryArcsFromInput_eq_textbookEntryArcs
    (I : VertexCoverInput) :
    dhcEntryArcsFromInput I = textbookEntryArcs I := by
  simp [dhcEntryArcsFromInput, dhcEntryArcsFromIndexed,
    dhcSourceIncidencesFromIndexed_input_eq_sourceIncidences,
    dhcEntryArcsFromSourceList, textbookEntryArcs,
    dhcIncidenceVertexFromSourceIncidences_eq_textbook]

theorem dhcExitArcsFromInput_eq_textbookExitArcs
    (I : VertexCoverInput) :
    dhcExitArcsFromInput I = textbookExitArcs I := by
  simp [dhcExitArcsFromInput, dhcExitArcsFromIndexed,
    dhcSourceIncidencesFromIndexed_input_eq_sourceIncidences,
    dhcExitArcsFromSourceList, textbookExitArcs,
    dhcIncidenceVertexFromSourceIncidences_eq_textbook]

theorem dhcTrackChainArcsFromInput_eq_textbookTrackChainArcs
    (I : VertexCoverInput) :
    dhcTrackChainArcsFromInput I = textbookTrackChainArcs I := by
  rfl

theorem dhcTrackEntryArcsFromInput_eq_textbookTrackEntryArcs
    (I : VertexCoverInput) :
    dhcTrackEntryArcsFromInput I = textbookTrackEntryArcs I := by
  rfl

theorem dhcTrackExitArcsFromInput_eq_textbookTrackExitArcs
    (I : VertexCoverInput) :
    dhcTrackExitArcsFromInput I = textbookTrackExitArcs I := by
  rfl

theorem dhcEdgeListFromInput_eq_textbookEdgeList
    (I : VertexCoverInput) :
    dhcEdgeListFromInput I = textbookEdgeList I := by
  simp [dhcEdgeListFromInput, textbookEdgeList,
    dhcIncidenceArcsFromInput_eq_textbookIncidenceArcs,
    dhcCrossArcsFromInput_eq_textbookCrossArcs,
    dhcChainArcsFromInput_eq_textbookChainArcs,
    dhcSelectorSkipArcsFromInput_eq_textbookSelectorSkipArcs,
    dhcEntryArcsFromInput_eq_textbookEntryArcs,
    dhcExitArcsFromInput_eq_textbookExitArcs,
    dhcTrackChainArcsFromInput_eq_textbookTrackChainArcs,
    dhcTrackEntryArcsFromInput_eq_textbookTrackEntryArcs,
    dhcTrackExitArcsFromInput_eq_textbookTrackExitArcs]

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
