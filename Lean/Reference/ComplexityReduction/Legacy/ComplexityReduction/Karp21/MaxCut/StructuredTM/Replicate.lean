import ComplexityReduction.Legacy.ComplexityReduction.Karp21.MaxCut.Part1
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.StructuredTM.ProductSumChoice
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.Range

namespace ComplexityReduction
namespace Karp21
namespace MaxCut

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
Direct TM utilities for the structured Partition-to-MaxCut route.

The key primitive here is a variable edge replicate.  The source first builds an
instruction list containing the edge once and then one unit instruction per copy;
the typed fold keeps the edge in its reachable accumulator and appends it once
per unit.  This avoids the fixed-value-only `list_const` primitive.
-/

def listReverseStep (X : EncodedType) (p : List X.Carrier × X.Carrier) :
    List X.Carrier :=
  p.2 :: p.1

theorem listReverseStep_tm_polytime (X : EncodedType) :
    TMPolyTimeMap
      (EncodedType.prod (EncodedType.list X) X)
      (EncodedType.list X)
      (listReverseStep X) := by
  let P := EncodedType.prod (EncodedType.list X) X
  have hHead : TMPolyTimeMap P X (fun p : P.Carrier => p.2) := by
    simpa [P] using TMPolyTimeMap.snd (EncodedType.list X) X
  have hTail : TMPolyTimeMap P (EncodedType.list X) (fun p : P.Carrier => p.1) := by
    simpa [P] using TMPolyTimeMap.fst (EncodedType.list X) X
  have hPair :
      TMPolyTimeMap P
        (EncodedType.prod X (EncodedType.list X))
        (fun p : P.Carrier => (p.2, p.1)) :=
    TMPolyTimeMap.prod_mk hHead hTail
  have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons X) hPair
  simpa [Function.comp, P, listReverseStep] using hComp

theorem listReverseFold_eq_reverse (X : EncodedType)
    (xs acc : List X.Carrier) :
    xs.foldl (fun acc x => listReverseStep X (acc, x)) acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil =>
      simp [listReverseStep]
  | cons x xs ih =>
      rw [List.foldl_cons, ih]
      simp [listReverseStep, List.append_assoc]

theorem listReverse_tm_polytime (X : EncodedType) :
    TMPolyTimeMap
      (EncodedType.list X)
      (EncodedType.list X)
      List.reverse := by
  rcases listReverseStep_tm_polytime X with ⟨hStep⟩
  have hFold :
      TMPolyTimeMap
        (EncodedType.list X)
        (EncodedType.list X)
        (fun xs : List X.Carrier =>
          xs.foldl (fun acc x => listReverseStep X (acc, x)) []) := by
    refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      X (EncodedType.list X)
      (listReverseStep X) ([] : List X.Carrier)
      hStep (Polynomial.C 0) (Polynomial.X + Polynomial.C 1) ?_ ?_
    · intro xs
      simp
    · intro source acc x hx
      simp [listReverseStep, Polynomial.eval_add, Polynomial.eval_X]
      omega
  convert hFold using 1
  funext xs
  simpa using (listReverseFold_eq_reverse X xs []).symm

theorem natListReverse_tm_polytime :
    TMPolyTimeMap
      partitionWeightsStructuredEncodedType
      partitionWeightsStructuredEncodedType
      List.reverse := by
  simpa [partitionWeightsStructuredEncodedType] using listReverse_tm_polytime EncodedType.nat

def edgeReplicateAccEncodedType : EncodedType :=
  EncodedType.prod edgeStructuredEncodedType edgeListStructuredEncodedType

def edgeReplicateInstructionEncodedType : EncodedType :=
  EncodedType.sum edgeStructuredEncodedType (EncodedType.raw Unit)

def edgeReplicateInstructionListEncodedType : EncodedType :=
  EncodedType.list edgeReplicateInstructionEncodedType

def edgeReplicateInitAcc : (Nat × Nat) × List (Nat × Nat) :=
  (((0 : Nat), (0 : Nat)), [])

def edgeReplicateInitInstruction (e : Nat × Nat) :
    edgeReplicateInstructionEncodedType.Carrier :=
  Sum.inl e

def edgeReplicateUnitInstruction (_ : Unit) :
    edgeReplicateInstructionEncodedType.Carrier :=
  Sum.inr ()

def edgeReplicateInstructions (p : (Nat × Nat) × List Unit) :
    List edgeReplicateInstructionEncodedType.Carrier :=
  edgeReplicateInitInstruction p.1 :: p.2.map edgeReplicateUnitInstruction

def edgeReplicateStep
    (p : edgeReplicateAccEncodedType.Carrier × edgeReplicateInstructionEncodedType.Carrier) :
    edgeReplicateAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl e => (e, [])
  | Sum.inr _ =>
      let out : List (Nat × Nat) := p.1.2
      (p.1.1, out ++ ([p.1.1] : List (Nat × Nat)))

def edgeReplicateStepLeft (e : Nat × Nat) :
    edgeReplicateAccEncodedType.Carrier :=
  (e, [])

def edgeReplicateStepRight
  (p : edgeReplicateAccEncodedType.Carrier × Unit) :
    edgeReplicateAccEncodedType.Carrier :=
  let out : List (Nat × Nat) := p.1.2
  (p.1.1, out ++ ([p.1.1] : List (Nat × Nat)))

def edgeReplicateFold
    (xs : List edgeReplicateInstructionEncodedType.Carrier) :
    edgeReplicateAccEncodedType.Carrier :=
  xs.foldl (fun acc instr => edgeReplicateStep (acc, instr)) edgeReplicateInitAcc

def edgeReplicateFromUnits (p : (Nat × Nat) × List Unit) : List (Nat × Nat) :=
  (edgeReplicateFold (edgeReplicateInstructions p)).2

def edgeReplicateFromNat (p : (Nat × Nat) × Nat) : List (Nat × Nat) :=
  edgeReplicateFromUnits (p.1, List.replicate p.2 ())

theorem edgeReplicateUnits_fold
    (e : Nat × Nat) (units : List Unit) (out : List (Nat × Nat)) :
    (units.map edgeReplicateUnitInstruction).foldl
        (fun acc instr => edgeReplicateStep (acc, instr)) (e, out) =
      (e, out ++ List.replicate units.length e) := by
  induction units generalizing out with
  | nil =>
      change (e, out) = (e, out ++ [])
      rw [List.append_nil]
  | cons u units ih =>
      simp only [List.map_cons, List.foldl_cons, edgeReplicateUnitInstruction,
        edgeReplicateStep]
      calc
        (units.map edgeReplicateUnitInstruction).foldl
            (fun acc instr =>
              match instr with
              | Sum.inl e => (e, [])
              | Sum.inr _ => (acc.1, acc.2 ++ [acc.1]))
            (e, out ++ [e])
            = (e, (out ++ [e]) ++ List.replicate units.length e) := by
              simpa [edgeReplicateStep] using ih (out ++ [e])
        _ = (e, out ++ List.replicate (u :: units).length e) := by
              change (e, out ++ [e] ++ List.replicate units.length e) =
                (e, out ++ List.replicate (units.length + 1) e)
              rw [List.replicate_succ]
              simp [List.append_assoc]

theorem edgeReplicateFromUnits_eq (e : Nat × Nat) (units : List Unit) :
    edgeReplicateFromUnits (e, units) = List.replicate units.length e := by
  have h := edgeReplicateUnits_fold e units []
  simpa [edgeReplicateFromUnits, edgeReplicateFold, edgeReplicateInstructions,
    edgeReplicateInitInstruction, edgeReplicateInitAcc, edgeReplicateStep] using
    congrArg Prod.snd h

theorem edgeReplicateFromNat_eq (p : (Nat × Nat) × Nat) :
    edgeReplicateFromNat p = List.replicate p.2 p.1 := by
  rcases p with ⟨e, n⟩
  simpa [edgeReplicateFromNat] using
    edgeReplicateFromUnits_eq e (List.replicate n ())

theorem edgeListAppendSingleton_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod edgeListStructuredEncodedType edgeStructuredEncodedType)
      edgeListStructuredEncodedType
      (fun p : List (Nat × Nat) × (Nat × Nat) => p.1 ++ [p.2]) := by
  let X := EncodedType.prod edgeListStructuredEncodedType edgeStructuredEncodedType
  have hHead :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : List (Nat × Nat) × (Nat × Nat) => p.1) := by
    simpa [X] using TMPolyTimeMap.fst edgeListStructuredEncodedType edgeStructuredEncodedType
  have hSingleton :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : List (Nat × Nat) × (Nat × Nat) => [p.2]) := by
    have hSnd := TMPolyTimeMap.snd edgeListStructuredEncodedType edgeStructuredEncodedType
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton edgeStructuredEncodedType) hSnd
    simpa [Function.comp, X, edgeListStructuredEncodedType] using hComp
  have hPair :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun p : List (Nat × Nat) × (Nat × Nat) => (p.1, [p.2])) :=
    TMPolyTimeMap.prod_mk hHead hSingleton
  have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append edgeStructuredEncodedType) hPair
  simpa [Function.comp, X, edgeListStructuredEncodedType] using hComp

theorem edgeReplicateStepRight_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod edgeReplicateAccEncodedType (EncodedType.raw Unit))
      edgeReplicateAccEncodedType
      edgeReplicateStepRight := by
  let X := EncodedType.prod edgeReplicateAccEncodedType (EncodedType.raw Unit)
  have hAcc :
      TMPolyTimeMap X edgeReplicateAccEncodedType
        (fun p : edgeReplicateAccEncodedType.Carrier × Unit => p.1) := by
    simpa [X] using TMPolyTimeMap.fst edgeReplicateAccEncodedType (EncodedType.raw Unit)
  have hEdge :
      TMPolyTimeMap X edgeStructuredEncodedType
        (fun p : edgeReplicateAccEncodedType.Carrier × Unit => p.1.1) := by
    have hFst := TMPolyTimeMap.fst edgeStructuredEncodedType edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, edgeReplicateAccEncodedType, X] using hComp
  have hOut :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : edgeReplicateAccEncodedType.Carrier × Unit => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd edgeStructuredEncodedType edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, edgeReplicateAccEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeStructuredEncodedType)
        (fun p : edgeReplicateAccEncodedType.Carrier × Unit => (p.1.2, p.1.1)) :=
    TMPolyTimeMap.prod_mk hOut hEdge
  have hAppend := TMPolyTimeMap.comp edgeListAppendSingleton_tm_polytime hAppendInput
  have hPair := TMPolyTimeMap.prod_mk hEdge hAppend
  simpa [Function.comp, edgeReplicateAccEncodedType, edgeReplicateStepRight, X] using hPair

theorem edgeReplicateStepLeft_tm_polytime :
    TMPolyTimeMap
      edgeStructuredEncodedType
      edgeReplicateAccEncodedType
      edgeReplicateStepLeft := by
  have hEdge := TMPolyTimeMap.id edgeStructuredEncodedType
  have hEmpty :
      TMPolyTimeMap edgeStructuredEncodedType edgeListStructuredEncodedType
        (fun _ : Nat × Nat => ([] : List (Nat × Nat))) :=
    TMPolyTimeMap.const edgeStructuredEncodedType edgeListStructuredEncodedType []
  have hPair := TMPolyTimeMap.prod_mk hEdge hEmpty
  simpa [edgeReplicateAccEncodedType, edgeReplicateStepLeft] using hPair

theorem edgeReplicateStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod edgeReplicateAccEncodedType edgeReplicateInstructionEncodedType)
      edgeReplicateAccEncodedType
      edgeReplicateStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      edgeReplicateAccEncodedType edgeStructuredEncodedType (EncodedType.raw Unit)
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim edgeReplicateStepLeft_tm_polytime
      edgeReplicateStepRight_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem edgeReplicateInstructions_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod edgeStructuredEncodedType rawUnitListEncodedType)
      edgeReplicateInstructionListEncodedType
      edgeReplicateInstructions := by
  let X := EncodedType.prod edgeStructuredEncodedType rawUnitListEncodedType
  have hEdge : TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst edgeStructuredEncodedType rawUnitListEncodedType
  have hUnits : TMPolyTimeMap X rawUnitListEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd edgeStructuredEncodedType rawUnitListEncodedType
  have hInit :
      TMPolyTimeMap X edgeReplicateInstructionEncodedType
        (fun p : X.Carrier => edgeReplicateInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.inl edgeStructuredEncodedType (EncodedType.raw Unit)) hEdge
    simpa [Function.comp, edgeReplicateInstructionEncodedType,
      edgeReplicateInitInstruction, X] using hComp
  have hUnitInstr :
      TMPolyTimeMap (EncodedType.raw Unit) edgeReplicateInstructionEncodedType
        edgeReplicateUnitInstruction := by
    simpa [edgeReplicateInstructionEncodedType, edgeReplicateUnitInstruction] using
      TMPolyTimeMap.inr edgeStructuredEncodedType (EncodedType.raw Unit)
  have hMappedUnits :
      TMPolyTimeMap X edgeReplicateInstructionListEncodedType
        (fun p : X.Carrier => p.2.map edgeReplicateUnitInstruction) := by
    have hMap := TMPolyTimeMap.list_map hUnitInstr
    have hComp := TMPolyTimeMap.comp hMap hUnits
    simpa [Function.comp, rawUnitListEncodedType,
      edgeReplicateInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeReplicateInstructionEncodedType
          edgeReplicateInstructionListEncodedType)
        (fun p : X.Carrier =>
          (edgeReplicateInitInstruction p.1, p.2.map edgeReplicateUnitInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hMappedUnits
  have hComp :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons edgeReplicateInstructionEncodedType)
      hConsInput
  simpa [Function.comp, edgeReplicateInstructions, edgeReplicateInstructionListEncodedType, X]
    using hComp

def edgeReplicateAccBound (N processed : Nat)
    (acc : edgeReplicateAccEncodedType.Carrier) : Prop :=
  edgeStructuredEncodedType.inputSize acc.1 ≤ N + 3 ∧
    edgeListStructuredEncodedType.inputSize acc.2 ≤ processed * (N + 4)

theorem edgeReplicateInitAcc_bound (N : Nat) :
    edgeReplicateAccBound N 0 edgeReplicateInitAcc := by
  constructor
  · simp [edgeReplicateInitAcc, edgeStructuredEncodedType]
  · change edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) ≤ 0 * (N + 4)
    have hnil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
      change (EncodedType.list edgeStructuredEncodedType).inputSize ([] : List (Nat × Nat)) = 0
      exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
    rw [hnil]
    exact Nat.zero_le _

theorem edgeReplicateInstruction_edge_le
    {N : Nat} {e : Nat × Nat}
    (hInstr : edgeReplicateInstructionEncodedType.inputSize (Sum.inl e) ≤ N) :
    edgeStructuredEncodedType.inputSize e ≤ N := by
  rcases e with ⟨u, v⟩
  simp [edgeReplicateInstructionEncodedType, edgeStructuredEncodedType,
    EncodedType.inputSize, EncodedType.sum, EncodedType.prod, EncodedType.nat] at hInstr ⊢
  omega

theorem edgeReplicateStep_bound {N processed : Nat}
    {acc : edgeReplicateAccEncodedType.Carrier}
    {instr : edgeReplicateInstructionEncodedType.Carrier}
    (hAcc : edgeReplicateAccBound N processed acc)
    (hInstr : edgeReplicateInstructionEncodedType.inputSize instr ≤ N) :
    edgeReplicateAccBound N (processed + 1) (edgeReplicateStep (acc, instr)) := by
  rcases hAcc with ⟨hEdge, hOut⟩
  cases instr with
  | inl e =>
      have hEdge' := edgeReplicateInstruction_edge_le hInstr
      constructor
      · simpa [edgeReplicateStep] using hEdge'.trans (Nat.le_add_right N 3)
      · change edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) ≤
          (processed + 1) * (N + 4)
        have hnil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
          change (EncodedType.list edgeStructuredEncodedType).inputSize ([] : List (Nat × Nat)) = 0
          exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
        rw [hnil]
        exact Nat.zero_le _
  | inr u =>
      constructor
      · simpa [edgeReplicateStep] using hEdge
      · let out : List (Nat × Nat) := acc.2
        have hAppend :
            edgeListStructuredEncodedType.inputSize
                (out ++ ([acc.1] : List (Nat × Nat))) =
              edgeListStructuredEncodedType.inputSize out +
                edgeStructuredEncodedType.inputSize acc.1 + 1 := by
          simpa [edgeListStructuredEncodedType] using
            Partition.encodedItemsList_inputSize_append_singleton
              edgeStructuredEncodedType out acc.1
        rw [show (edgeReplicateStep (acc, Sum.inr u)).2 =
            out ++ ([acc.1] : List (Nat × Nat)) by
          simp [edgeReplicateStep, out]]
        rw [hAppend]
        change edgeListStructuredEncodedType.inputSize acc.2 +
              edgeStructuredEncodedType.inputSize acc.1 + 1 ≤
            (processed + 1) * (N + 4)
        calc
          edgeListStructuredEncodedType.inputSize acc.2 +
                edgeStructuredEncodedType.inputSize acc.1 + 1
              ≤ processed * (N + 4) + (N + 4) := by omega
          _ = (processed + 1) * (N + 4) := by
                rw [Nat.add_mul, Nat.one_mul]

theorem edgeReplicateFold_bound_aux {N processed : Nat}
    (rest : List edgeReplicateInstructionEncodedType.Carrier)
    (acc : edgeReplicateAccEncodedType.Carrier)
    (hAcc : edgeReplicateAccBound N processed acc)
    (hLen : processed + rest.length ≤ N)
    (hInstr : ∀ instr ∈ rest, edgeReplicateInstructionEncodedType.inputSize instr ≤ N) :
    edgeReplicateAccBound N (processed + rest.length)
      (rest.foldl (fun acc instr => edgeReplicateStep (acc, instr)) acc) := by
  induction rest generalizing processed acc with
  | nil =>
      simpa using hAcc
  | cons instr rest ih =>
      have hHead : edgeReplicateInstructionEncodedType.inputSize instr ≤ N := hInstr instr (by simp)
      have hStep := edgeReplicateStep_bound (N := N) (processed := processed)
        (acc := acc) (instr := instr) hAcc hHead
      have hLenTail : processed + 1 + rest.length ≤ N := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hLen
      have hInstrTail :
          ∀ instr' ∈ rest, edgeReplicateInstructionEncodedType.inputSize instr' ≤ N := by
        intro instr' hin
        exact hInstr instr' (by simp [hin])
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (processed := processed + 1) (acc := edgeReplicateStep (acc, instr))
          hStep hLenTail hInstrTail

theorem edgeReplicateFold_bound_of_inputSize_le {N : Nat}
    (xs : List edgeReplicateInstructionEncodedType.Carrier)
    (hSize : edgeReplicateInstructionListEncodedType.inputSize xs ≤ N) :
    edgeReplicateAccBound N xs.length
      (xs.foldl (fun acc instr => edgeReplicateStep (acc, instr)) edgeReplicateInitAcc) := by
  have hLenRaw :=
    Partition.encodedItemsList_length_le_inputSize edgeReplicateInstructionEncodedType xs
  have hLen : xs.length ≤ N := by
    have hLenRaw' :
        xs.length ≤ edgeReplicateInstructionListEncodedType.inputSize xs := by
      simpa [edgeReplicateInstructionListEncodedType] using hLenRaw
    omega
  have hInstr :
      ∀ instr ∈ xs, edgeReplicateInstructionEncodedType.inputSize instr ≤ N := by
    intro instr hin
    have hElem := Partition.encodedItemsList_element_inputSize_le
      (X := edgeReplicateInstructionEncodedType) (x := instr) (xs := xs) hin
    have hElem' :
        edgeReplicateInstructionEncodedType.inputSize instr ≤
          edgeReplicateInstructionListEncodedType.inputSize xs := by
      simpa [edgeReplicateInstructionListEncodedType] using hElem
    omega
  have h := edgeReplicateFold_bound_aux (N := N) (processed := 0) xs edgeReplicateInitAcc
    (edgeReplicateInitAcc_bound N) (by simpa using hLen) hInstr
  simpa using h

noncomputable def edgeReplicateFoldAccBoundPolynomial : Polynomial Nat :=
  Polynomial.C 4 * (Polynomial.X * Polynomial.X) + Polynomial.C 20

@[simp] theorem edgeReplicateFoldAccBoundPolynomial_eval (N : Nat) :
    edgeReplicateFoldAccBoundPolynomial.eval N = 4 * (N * N) + 20 := by
  simp [edgeReplicateFoldAccBoundPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

theorem edgeReplicateAccBound_inputSize_le {N processed : Nat}
    {acc : edgeReplicateAccEncodedType.Carrier}
    (hAcc : edgeReplicateAccBound N processed acc)
    (hProcessed : processed ≤ N) :
    edgeReplicateAccEncodedType.inputSize acc ≤
      edgeReplicateFoldAccBoundPolynomial.eval N := by
  rcases acc with ⟨edge, out⟩
  rcases hAcc with ⟨hEdge, hOut⟩
  have hOutN : edgeListStructuredEncodedType.inputSize out ≤ N * (N + 4) := by
    exact hOut.trans (Nat.mul_le_mul_right _ hProcessed)
  simp [edgeReplicateAccEncodedType, EncodedType.inputSize_prod] at hOutN ⊢
  nlinarith [hEdge, hOutN, Nat.zero_le N]

noncomputable def edgeReplicateFoldTimePolynomial
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod edgeReplicateAccEncodedType
          edgeReplicateInstructionEncodedType).encode
        edgeReplicateAccEncodedType.encode
        edgeReplicateStep) : Polynomial Nat :=
  TM2Programs.listFoldBoundedTimePolynomial hStep.tm edgeReplicateFoldAccBoundPolynomial
    (hStep.time.comp
      (edgeReplicateFoldAccBoundPolynomial + Polynomial.X + Polynomial.C 5))

theorem edgeReplicateFold_tm_polytime :
    TMPolyTimeMap
      edgeReplicateInstructionListEncodedType
      edgeReplicateAccEncodedType
      edgeReplicateFold := by
  rcases edgeReplicateStep_tm_polytime with ⟨hStep⟩
  let time := edgeReplicateFoldTimePolynomial hStep
  refine
    TMPolyTimeMap.list_foldl_typed
      edgeReplicateInstructionEncodedType edgeReplicateAccEncodedType
      edgeReplicateStep edgeReplicateInitAcc hStep time ?_
  intro source
  let N := edgeReplicateInstructionListEncodedType.inputSize source
  let B := edgeReplicateFoldAccBoundPolynomial.eval N
  let T := hStep.time.eval (B + N + 5)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hLoopAux :
      ∀ (pref rest : List edgeReplicateInstructionEncodedType.Carrier),
        source = pref ++ rest →
          TM2Programs.listFoldTypedLoopTime
              edgeReplicateInstructionEncodedType edgeReplicateAccEncodedType
              edgeReplicateStep hStep
              (pref.foldl (fun acc instr => edgeReplicateStep (acc, instr))
                edgeReplicateInitAcc)
              rest ≤
            C * (EncodedType.list edgeReplicateInstructionEncodedType).inputSize rest := by
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
        have hxN : edgeReplicateInstructionEncodedType.inputSize x ≤ N := by
          have hElem := Partition.encodedItemsList_element_inputSize_le
            (X := edgeReplicateInstructionEncodedType) (x := x) (xs := source) hxMemSource
          simpa [N, edgeReplicateInstructionListEncodedType] using hElem
        have hPrefixSize : edgeReplicateInstructionListEncodedType.inputSize pref ≤ N := by
          have hEqSize :
              edgeReplicateInstructionListEncodedType.inputSize source =
                edgeReplicateInstructionListEncodedType.inputSize pref +
                  edgeReplicateInstructionListEncodedType.inputSize (x :: xs) := by
            rw [hEq]
            exact Partition.encodedItemsList_inputSize_append
              edgeReplicateInstructionEncodedType pref (x :: xs)
          omega
        have hPrefixBound :=
          edgeReplicateFold_bound_of_inputSize_le (N := N) pref hPrefixSize
        have hPrefixLenN : pref.length ≤ N := by
          have hLen :=
            Partition.encodedItemsList_length_le_inputSize edgeReplicateInstructionEncodedType pref
          have hLen' :
              pref.length ≤ edgeReplicateInstructionListEncodedType.inputSize pref := by
            simpa [edgeReplicateInstructionListEncodedType] using hLen
          omega
        have hAccSize :
            edgeReplicateAccEncodedType.inputSize
                (pref.foldl (fun acc instr => edgeReplicateStep (acc, instr))
                  edgeReplicateInitAcc) ≤ B := by
          simpa [B] using edgeReplicateAccBound_inputSize_le hPrefixBound hPrefixLenN
        have hStepBound := edgeReplicateStep_bound
          (N := N) (processed := pref.length)
          (acc := pref.foldl (fun acc instr => edgeReplicateStep (acc, instr))
            edgeReplicateInitAcc)
          (instr := x) hPrefixBound hxN
        have hNextSize :
            edgeReplicateAccEncodedType.inputSize
                (edgeReplicateStep
                  (pref.foldl (fun acc instr => edgeReplicateStep (acc, instr))
                    edgeReplicateInitAcc, x)) ≤ B := by
          have hPrefixSucc : pref.length + 1 ≤ N := by
            have hSourceLenN : source.length ≤ N := by
              have hLen :=
                Partition.encodedItemsList_length_le_inputSize
                  edgeReplicateInstructionEncodedType source
              have hLen' : source.length ≤ edgeReplicateInstructionListEncodedType.inputSize source :=
                by simpa [edgeReplicateInstructionListEncodedType] using hLen
              omega
            have hLenEq : source.length = pref.length + (x :: xs).length := by
              rw [hEq, List.length_append]
            simp at hLenEq
            omega
          simpa [B] using edgeReplicateAccBound_inputSize_le hStepBound hPrefixSucc
        have hStepTime :
            hStep.time.eval
                ((EncodedType.prod edgeReplicateAccEncodedType
                    edgeReplicateInstructionEncodedType).inputSize
                  (pref.foldl (fun acc instr => edgeReplicateStep (acc, instr))
                    edgeReplicateInitAcc, x)) ≤ T := by
          have hArg :
              (EncodedType.prod edgeReplicateAccEncodedType
                    edgeReplicateInstructionEncodedType).inputSize
                  (pref.foldl (fun acc instr => edgeReplicateStep (acc, instr))
                    edgeReplicateInitAcc, x) ≤ B + N + 5 := by
            rw [EncodedType.inputSize_prod]
            change edgeReplicateAccEncodedType.inputSize
                  (pref.foldl (fun acc instr => edgeReplicateStep (acc, instr))
                    edgeReplicateInitAcc) + 1 +
                edgeReplicateInstructionEncodedType.inputSize x ≤ B + N + 5
            omega
          exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
        have hBlock :
            TM2Programs.listFoldBlockTime hStep.tm
                (edgeReplicateInstructionEncodedType.encode x).length
                (edgeReplicateAccEncodedType.encode
                  (pref.foldl (fun acc instr => edgeReplicateStep (acc, instr))
                    edgeReplicateInitAcc)).length
                (edgeReplicateAccEncodedType.encode
                  (edgeReplicateStep
                    (pref.foldl (fun acc instr => edgeReplicateStep (acc, instr))
                      edgeReplicateInitAcc, x))).length
                (hStep.time.eval
                  ((EncodedType.prod edgeReplicateAccEncodedType
                    edgeReplicateInstructionEncodedType).inputSize
                    (pref.foldl (fun acc instr => edgeReplicateStep (acc, instr))
                      edgeReplicateInitAcc, x))) ≤
              C * (edgeReplicateInstructionEncodedType.inputSize x + 1) := by
          exact
            TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
              (by simpa [EncodedType.inputSize] using hAccSize)
              (by simpa [EncodedType.inputSize] using hNextSize)
              hStepTime
        have hTail := ih (pref := pref ++ [x]) (by
          rw [hEq]
          simp [List.append_assoc])
        calc
          TM2Programs.listFoldTypedLoopTime
              edgeReplicateInstructionEncodedType edgeReplicateAccEncodedType
              edgeReplicateStep hStep
              (pref.foldl (fun acc instr => edgeReplicateStep (acc, instr))
                edgeReplicateInitAcc)
              (x :: xs)
              =
            TM2Programs.listFoldTypedLoopTime
              edgeReplicateInstructionEncodedType edgeReplicateAccEncodedType
              edgeReplicateStep hStep
              ((pref ++ [x]).foldl (fun acc instr => edgeReplicateStep (acc, instr))
                edgeReplicateInitAcc)
              xs +
            TM2Programs.listFoldBlockTime hStep.tm
              (edgeReplicateInstructionEncodedType.encode x).length
              (edgeReplicateAccEncodedType.encode
                (pref.foldl (fun acc instr => edgeReplicateStep (acc, instr))
                  edgeReplicateInitAcc)).length
              (edgeReplicateAccEncodedType.encode
                (edgeReplicateStep
                  (pref.foldl (fun acc instr => edgeReplicateStep (acc, instr))
                    edgeReplicateInitAcc, x))).length
              (hStep.time.eval
                ((EncodedType.prod edgeReplicateAccEncodedType
                  edgeReplicateInstructionEncodedType).inputSize
                  (pref.foldl (fun acc instr => edgeReplicateStep (acc, instr))
                    edgeReplicateInitAcc, x))) := by
                simp [TM2Programs.listFoldTypedLoopTime, List.foldl_append]
          _ ≤ C * (EncodedType.list edgeReplicateInstructionEncodedType).inputSize xs +
              C * (edgeReplicateInstructionEncodedType.inputSize x + 1) :=
                Nat.add_le_add hTail hBlock
          _ = C * (EncodedType.list edgeReplicateInstructionEncodedType).inputSize (x :: xs) := by
                rw [EncodedType.inputSize_list_cons]
                ring
  have hLoop := hLoopAux [] source (by simp)
  have hTimeEval :
      time.eval N = (C + 2) * (N + 1) := by
    simp [time, edgeReplicateFoldTimePolynomial, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval, Polynomial.eval_add,
      TM2Programs.listFoldBlockTimeCoeff]
  change 2 +
      TM2Programs.listFoldTypedLoopTime
        edgeReplicateInstructionEncodedType edgeReplicateAccEncodedType
        edgeReplicateStep hStep edgeReplicateInitAcc source ≤ time.eval N
  rw [hTimeEval]
  have hLoop' :
      TM2Programs.listFoldTypedLoopTime
        edgeReplicateInstructionEncodedType edgeReplicateAccEncodedType
        edgeReplicateStep hStep edgeReplicateInitAcc source ≤ C * N := by
    simpa [N, edgeReplicateInstructionListEncodedType] using hLoop
  nlinarith [hLoop', Nat.zero_le C, Nat.zero_le N]

theorem edgeReplicateFromUnits_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod edgeStructuredEncodedType rawUnitListEncodedType)
      edgeListStructuredEncodedType
      edgeReplicateFromUnits := by
  let X := EncodedType.prod edgeStructuredEncodedType rawUnitListEncodedType
  have hInstr := edgeReplicateInstructions_tm_polytime
  have hFold :
      TMPolyTimeMap X edgeReplicateAccEncodedType
        (fun p : X.Carrier => edgeReplicateFold (edgeReplicateInstructions p)) := by
    have hComp := TMPolyTimeMap.comp edgeReplicateFold_tm_polytime hInstr
    simpa [Function.comp, X] using hComp
  have hOut :
      TMPolyTimeMap edgeReplicateAccEncodedType edgeListStructuredEncodedType
        (fun p : edgeReplicateAccEncodedType.Carrier => p.2) := by
    simpa [edgeReplicateAccEncodedType] using
      TMPolyTimeMap.snd edgeStructuredEncodedType edgeListStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hOut hFold
  simpa [Function.comp, edgeReplicateFromUnits, X] using hComp

theorem edgeReplicateFromNat_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod edgeStructuredEncodedType EncodedType.nat)
      edgeListStructuredEncodedType
      edgeReplicateFromNat := by
  let X := EncodedType.prod edgeStructuredEncodedType EncodedType.nat
  have hEdge : TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst edgeStructuredEncodedType EncodedType.nat
  have hCount : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd edgeStructuredEncodedType EncodedType.nat
  have hUnits :
      TMPolyTimeMap X rawUnitListEncodedType
        (fun p : X.Carrier => List.replicate p.2 ()) := by
    have hComp := TMPolyTimeMap.comp natToRawUnitListTMBackedMap.tm_polytime hCount
    simpa [Function.comp, X] using hComp
  have hPair :
      TMPolyTimeMap X
        (EncodedType.prod edgeStructuredEncodedType rawUnitListEncodedType)
        (fun p : X.Carrier => (p.1, List.replicate p.2 ())) :=
    TMPolyTimeMap.prod_mk hEdge hUnits
  have hComp := TMPolyTimeMap.comp edgeReplicateFromUnits_tm_polytime hPair
  simpa [Function.comp, edgeReplicateFromNat, X] using hComp

theorem edgeReplicate_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod edgeStructuredEncodedType EncodedType.nat)
      edgeListStructuredEncodedType
      (fun p : (Nat × Nat) × Nat => List.replicate p.2 p.1) := by
  convert edgeReplicateFromNat_tm_polytime using 1
  funext p
  exact (edgeReplicateFromNat_eq p).symm

end MaxCut
end Karp21
end ComplexityReduction
