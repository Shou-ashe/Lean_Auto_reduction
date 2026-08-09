import ComplexityReduction.Legacy.ComplexityReduction.Karp21.MaxCut.StructuredTM.Pairs

namespace ComplexityReduction
namespace Karp21
namespace MaxCut

open ComplexityReduction.Combinatorics.Graph

/-!
Checked edge-block expansion for the direct structured Partition-to-MaxCut route.

An instruction carries one unit edge and a unary multiplicity.  The runner folds
over explicit instructions and appends the corresponding repeated unit-edge
block.  Upstream code is responsible for generating these instructions in the
textbook pair order.
-/

def maxCutEdgeBlockInstructionEncodedType : EncodedType :=
  EncodedType.prod edgeStructuredEncodedType EncodedType.nat

def maxCutEdgeBlockInstructionListEncodedType : EncodedType :=
  EncodedType.list maxCutEdgeBlockInstructionEncodedType

def maxCutEdgeBlockAppendStep
    (p : List (Nat × Nat) × ((Nat × Nat) × Nat)) :
    List (Nat × Nat) :=
  p.1 ++ List.replicate p.2.2 p.2.1

def maxCutEdgesFromBlockInstructions
    (xs : List ((Nat × Nat) × Nat)) :
    List (Nat × Nat) :=
  xs.foldl (fun acc instr => maxCutEdgeBlockAppendStep (acc, instr)) []

theorem maxCutEdgesFromBlockInstructions_eq_flatMap
    (xs : List ((Nat × Nat) × Nat)) :
    maxCutEdgesFromBlockInstructions xs =
      xs.flatMap fun instr => List.replicate instr.2 instr.1 := by
  unfold maxCutEdgesFromBlockInstructions
  have h :
      ∀ acc : List (Nat × Nat),
        xs.foldl (fun acc instr => maxCutEdgeBlockAppendStep (acc, instr)) acc =
          acc ++ xs.flatMap (fun instr => List.replicate instr.2 instr.1) := by
    induction xs with
    | nil =>
        intro acc
        simp [maxCutEdgeBlockAppendStep]
    | cons instr rest ih =>
        intro acc
        rw [List.foldl_cons, ih]
        simp [List.flatMap, maxCutEdgeBlockAppendStep, List.append_assoc]
  simpa using h []

theorem maxCutEdgeBlockAppendStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod edgeListStructuredEncodedType maxCutEdgeBlockInstructionEncodedType)
      edgeListStructuredEncodedType
      maxCutEdgeBlockAppendStep := by
  let X := EncodedType.prod edgeListStructuredEncodedType maxCutEdgeBlockInstructionEncodedType
  have hAcc :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst edgeListStructuredEncodedType maxCutEdgeBlockInstructionEncodedType
  have hInstr :
      TMPolyTimeMap X maxCutEdgeBlockInstructionEncodedType
        (fun p : X.Carrier => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd edgeListStructuredEncodedType maxCutEdgeBlockInstructionEncodedType
  have hBlock :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier => List.replicate p.2.2 p.2.1) := by
    have hComp := TMPolyTimeMap.comp edgeReplicate_tm_polytime hInstr
    simpa [Function.comp, maxCutEdgeBlockInstructionEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier => (p.1, List.replicate p.2.2 p.2.1)) :=
    TMPolyTimeMap.prod_mk hAcc hBlock
  have hAppend :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_append edgeStructuredEncodedType) hAppendInput
  simpa [Function.comp, maxCutEdgeBlockAppendStep, edgeListStructuredEncodedType,
    maxCutEdgeBlockInstructionEncodedType, X]
    using hAppend

theorem edgeListStructured_inputSize_replicate_le (e : Nat × Nat) (m : Nat) :
    edgeListStructuredEncodedType.inputSize (List.replicate m e) ≤
      m * (edgeStructuredEncodedType.inputSize e + 1) := by
  induction m with
  | zero =>
      simp [edgeListStructuredEncodedType]
  | succ m ih =>
      rw [List.replicate_succ]
      change (EncodedType.list edgeStructuredEncodedType).inputSize
          (e :: List.replicate m e) ≤
        (m + 1) * (edgeStructuredEncodedType.inputSize e + 1)
      rw [EncodedType.inputSize_list_cons]
      calc
        edgeStructuredEncodedType.inputSize e + 1 +
            edgeListStructuredEncodedType.inputSize (List.replicate m e)
            ≤ edgeStructuredEncodedType.inputSize e + 1 +
                m * (edgeStructuredEncodedType.inputSize e + 1) := by
              omega
        _ = (m + 1) * (edgeStructuredEncodedType.inputSize e + 1) := by
              ring

theorem maxCutEdgeBlockAppendStep_growth
    (source : List ((Nat × Nat) × Nat))
    (acc : List (Nat × Nat))
    (instr : (Nat × Nat) × Nat)
    (hinstr :
      maxCutEdgeBlockInstructionEncodedType.inputSize instr ≤
        maxCutEdgeBlockInstructionListEncodedType.inputSize source) :
    edgeListStructuredEncodedType.inputSize
        (maxCutEdgeBlockAppendStep (acc, instr)) ≤
      edgeListStructuredEncodedType.inputSize acc +
        (Polynomial.X * Polynomial.X + Polynomial.C 3 * Polynomial.X + Polynomial.C 3).eval
          (maxCutEdgeBlockInstructionListEncodedType.inputSize source) := by
  let N := maxCutEdgeBlockInstructionListEncodedType.inputSize source
  have hEdge : edgeStructuredEncodedType.inputSize instr.1 ≤ N := by
    simp [maxCutEdgeBlockInstructionEncodedType, EncodedType.inputSize_prod] at hinstr
    omega
  have hCount : instr.2 ≤ N := by
    simp [maxCutEdgeBlockInstructionEncodedType, EncodedType.inputSize_prod,
      EncodedType.inputSize_nat] at hinstr
    omega
  have hRep := edgeListStructured_inputSize_replicate_le instr.1 instr.2
  have hAppend :=
    list_inputSize_append edgeStructuredEncodedType acc (List.replicate instr.2 instr.1)
  have hMain :
      edgeListStructuredEncodedType.inputSize
          (maxCutEdgeBlockAppendStep (acc, instr)) ≤
        edgeListStructuredEncodedType.inputSize acc +
          (Polynomial.X * Polynomial.X + Polynomial.C 3 * Polynomial.X + Polynomial.C 3).eval N := by
    have hEq :
        edgeListStructuredEncodedType.inputSize (maxCutEdgeBlockAppendStep (acc, instr)) =
          edgeListStructuredEncodedType.inputSize acc +
            edgeListStructuredEncodedType.inputSize (List.replicate instr.2 instr.1) := by
      simpa [maxCutEdgeBlockAppendStep, edgeListStructuredEncodedType] using hAppend
    have hStep :
        edgeListStructuredEncodedType.inputSize (maxCutEdgeBlockAppendStep (acc, instr)) ≤
          edgeListStructuredEncodedType.inputSize acc +
            instr.2 * (edgeStructuredEncodedType.inputSize instr.1 + 1) := by
      rw [hEq]
      omega
    have hPoly :
        instr.2 * (edgeStructuredEncodedType.inputSize instr.1 + 1) ≤
          (Polynomial.X * Polynomial.X + Polynomial.C 3 * Polynomial.X + Polynomial.C 3).eval
            N := by
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
      nlinarith
    exact Nat.le_trans hStep (Nat.add_le_add_left hPoly _)
  simpa [N] using hMain

theorem maxCutEdgesFromBlockInstructions_tm_polytime :
    TMPolyTimeMap
      maxCutEdgeBlockInstructionListEncodedType
      edgeListStructuredEncodedType
      maxCutEdgesFromBlockInstructions := by
  rcases maxCutEdgeBlockAppendStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      maxCutEdgeBlockInstructionEncodedType edgeListStructuredEncodedType
      maxCutEdgeBlockAppendStep ([] : List edgeStructuredEncodedType.Carrier)
      hStep (Polynomial.C 0)
      (Polynomial.X * Polynomial.X + Polynomial.C 3 * Polynomial.X + Polynomial.C 3) ?_ ?_
  · intro source
    rw [show edgeListStructuredEncodedType.inputSize
        ([] : List edgeStructuredEncodedType.Carrier) = 0 by rfl]
    simp
  · intro source acc instr hinstr
    simpa [maxCutEdgeBlockInstructionListEncodedType] using
      maxCutEdgeBlockAppendStep_growth source acc instr hinstr

end MaxCut
end Karp21
end ComplexityReduction
