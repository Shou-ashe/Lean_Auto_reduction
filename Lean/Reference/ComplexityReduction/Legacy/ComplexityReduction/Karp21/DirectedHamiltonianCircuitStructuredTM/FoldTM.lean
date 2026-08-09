/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.RowScan

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

/-! ### TM proof for the row instruction fold -/

abbrev dhcRowScanAccRaw :=
  Nat × (Nat × (Nat × (Nat × List ((Nat × Nat) × Nat))))

def dhcIndexedIncidenceBound (N processed : Nat) (x : ((Nat × Nat) × Nat)) : Prop :=
  x.1.1 ≤ N ∧ x.1.2 ≤ processed ∧ x.2 ≤ N + processed

def dhcRowScanAccBound
    (N processed : Nat) (acc : dhcRowScanAccRaw) : Prop :=
  acc.1 ≤ N ∧
    acc.2.1 ≤ N ∧
      acc.2.2.1 ≤ processed ∧
        acc.2.2.2.1 ≤ N + processed ∧
          (∀ x ∈ acc.2.2.2.2, dhcIndexedIncidenceBound N processed x) ∧
            acc.2.2.2.2.length ≤ processed

theorem dhcIndexedIncidenceBound_mono {N processed processed' : Nat}
    {x : ((Nat × Nat) × Nat)}
    (hProcessed : processed ≤ processed')
    (hBound : dhcIndexedIncidenceBound N processed x) :
    dhcIndexedIncidenceBound N processed' x := by
  rcases hBound with ⟨hU, hEdgeIndex, hNextIndex⟩
  exact ⟨hU, hEdgeIndex.trans hProcessed, by omega⟩

theorem dhcRowFoldStep_bound {N processed : Nat}
    {acc : dhcRowScanAccRaw}
    {instr : dhcRowFoldInstructionEncodedType.Carrier}
    (hAcc : dhcRowScanAccBound N processed acc)
    (hInstr : dhcRowFoldInstructionEncodedType.inputSize instr ≤ N) :
    dhcRowScanAccBound N (processed + 1) (dhcRowFoldStep (acc, instr)) := by
  rcases acc with ⟨vertices, u, edgeIndex, nextIndex, out⟩
  rcases hAcc with ⟨hVertices, hU, hEdgeIndex, hNextIndex, hOut, hOutLen⟩
  change vertices ≤ N at hVertices
  change u ≤ N at hU
  change edgeIndex ≤ processed at hEdgeIndex
  change nextIndex ≤ N + processed at hNextIndex
  change (∀ x ∈ out, dhcIndexedIncidenceBound N processed x) at hOut
  change out.length ≤ processed at hOutLen
  cases instr with
  | inl payload =>
      rcases payload with ⟨vertices', u', nextIndex'⟩
      change Nat at vertices'
      change Nat at u'
      change Nat at nextIndex'
      have hVertices' : vertices' ≤ N := by
        simp [dhcRowFoldInstructionEncodedType, dhcRowInitPayloadEncodedType,
          EncodedType.inputSize, EncodedType.sum, EncodedType.prod, EncodedType.nat] at hInstr
        omega
      have hU' : u' ≤ N := by
        simp [dhcRowFoldInstructionEncodedType, dhcRowInitPayloadEncodedType,
          EncodedType.inputSize, EncodedType.sum, EncodedType.prod, EncodedType.nat] at hInstr
        omega
      have hNext' : nextIndex' ≤ N := by
        simp [dhcRowFoldInstructionEncodedType, dhcRowInitPayloadEncodedType,
          EncodedType.inputSize, EncodedType.sum, EncodedType.prod, EncodedType.nat] at hInstr
        omega
      simp [dhcRowFoldStep, dhcRowFoldLeftStep, dhcRowScanAccBound]
      omega
  | inr edge =>
      cases hIncident : dhcSourceIncidentBool (vertices, (u, edge))
      · change dhcRowScanAccBound N (processed + 1)
          (dhcRowScanStep ((vertices, (u, (edgeIndex, (nextIndex, out)))), edge))
        rw [dhcRowScanStep_false vertices u edgeIndex nextIndex out edge hIncident]
        dsimp [dhcRowScanAccBound]
        refine ⟨hVertices, hU, by omega, by omega, ?_, by omega⟩
        intro x hx
        exact dhcIndexedIncidenceBound_mono (by omega) (hOut x hx)
      · change dhcRowScanAccBound N (processed + 1)
          (dhcRowScanStep ((vertices, (u, (edgeIndex, (nextIndex, out)))), edge))
        rw [dhcRowScanStep_true vertices u edgeIndex nextIndex out edge hIncident]
        dsimp [dhcRowScanAccBound]
        refine ⟨hVertices, hU, by omega, by omega, ?_, by simp [hOutLen]⟩
        intro x hx
        rw [List.mem_append] at hx
        rcases hx with hxOld | hxNew
        · exact dhcIndexedIncidenceBound_mono (by omega) (hOut x hxOld)
        · simp at hxNew
          subst x
          dsimp [dhcIndexedIncidenceBound]
          exact ⟨hU, by omega, by omega⟩

theorem dhcRowScanFold_bound_aux
    {N processed : Nat}
    (xs : List dhcRowFoldInstructionEncodedType.Carrier)
    (acc : dhcRowScanAccRaw)
    (hAcc : dhcRowScanAccBound N processed acc)
    (hLen : processed + xs.length ≤ N)
    (hInstr : ∀ instr ∈ xs, dhcRowFoldInstructionEncodedType.inputSize instr ≤ N) :
    dhcRowScanAccBound N (processed + xs.length)
      (xs.foldl (fun acc instr => dhcRowFoldStep (acc, instr)) acc) := by
  induction xs generalizing processed acc with
  | nil =>
      simpa using hAcc
  | cons instr xs ih =>
      have hStep := dhcRowFoldStep_bound hAcc (hInstr instr (by simp))
      have hTailLen : (processed + 1) + xs.length ≤ N := by
        simp only [List.length_cons] at hLen
        omega
      have hTailInstr :
          ∀ instr ∈ xs, dhcRowFoldInstructionEncodedType.inputSize instr ≤ N := by
        intro instr hin
        exact hInstr instr (by simp [hin])
      have hTail :=
        ih (processed := processed + 1)
          (acc := dhcRowFoldStep (acc, instr)) hStep hTailLen hTailInstr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hTail

theorem dhcRowScanFold_bound_of_inputSize_le
    {N : Nat} (xs : List dhcRowFoldInstructionEncodedType.Carrier)
    (hSize : dhcRowFoldInstructionListEncodedType.inputSize xs ≤ N) :
    dhcRowScanAccBound N xs.length
      (xs.foldl (fun acc instr => dhcRowFoldStep (acc, instr)) dhcRowFoldInit) := by
  have hInit : dhcRowScanAccBound N 0 dhcRowFoldInit := by
    simp [dhcRowScanAccBound, dhcRowFoldInit]
  have hLen : 0 + xs.length ≤ N := by
    have hLenInput :=
      SetCovering.incidentEncodedList_length_le_inputSize dhcRowFoldInstructionEncodedType xs
    have hLenInput' : xs.length ≤ dhcRowFoldInstructionListEncodedType.inputSize xs := by
      simpa [dhcRowFoldInstructionListEncodedType] using hLenInput
    omega
  have hInstr :
      ∀ instr ∈ xs, dhcRowFoldInstructionEncodedType.inputSize instr ≤ N := by
    intro instr hin
    have hElem :=
      SetCovering.incidentEncodedList_element_inputSize_le
        (X := dhcRowFoldInstructionEncodedType) (x := instr) (xs := xs) hin
    have hElem' : dhcRowFoldInstructionEncodedType.inputSize instr ≤
        dhcRowFoldInstructionListEncodedType.inputSize xs := by
      simpa [dhcRowFoldInstructionListEncodedType] using hElem
    omega
  have h :=
    dhcRowScanFold_bound_aux (N := N) (processed := 0) xs dhcRowFoldInit
      hInit hLen hInstr
  simpa using h

noncomputable def dhcRowScanFoldAccBoundPolynomial : Polynomial Nat :=
  Polynomial.C 1000 * (Polynomial.X * Polynomial.X) + Polynomial.C 5000

@[simp] theorem dhcRowScanFoldAccBoundPolynomial_eval (N : Nat) :
    dhcRowScanFoldAccBoundPolynomial.eval N = 1000 * (N * N) + 5000 := by
  simp [dhcRowScanFoldAccBoundPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

theorem dhcIndexedIncidenceBound_inputSize_le {N processed : Nat}
    {x : ((Nat × Nat) × Nat)}
    (hBound : dhcIndexedIncidenceBound N processed x)
    (hProcessed : processed ≤ N) :
    dhcIndexedIncidenceEncodedType.inputSize x ≤ 4 * N + 8 := by
  rcases x with ⟨⟨u, edgeIndex⟩, nextIndex⟩
  rcases hBound with ⟨hU, hEdgeIndex, hNextIndex⟩
  have hNextN : nextIndex ≤ 2 * N := by nlinarith
  simp [dhcIndexedIncidenceEncodedType, vertexPairEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat]
  nlinarith

theorem dhcRowScanAccBound_inputSize_le {N processed : Nat}
    {acc : dhcRowScanAccRaw}
    (hAcc : dhcRowScanAccBound N processed acc)
    (hProcessed : processed ≤ N) :
    dhcRowScanAccEncodedType.inputSize acc ≤
      dhcRowScanFoldAccBoundPolynomial.eval N := by
  rcases acc with ⟨vertices, u, edgeIndex, nextIndex, out⟩
  rcases hAcc with ⟨hVertices, hU, hEdgeIndex, hNextIndex, hOut, hOutLen⟩
  change vertices ≤ N at hVertices
  change u ≤ N at hU
  change edgeIndex ≤ processed at hEdgeIndex
  change nextIndex ≤ N + processed at hNextIndex
  change (∀ x ∈ out, dhcIndexedIncidenceBound N processed x) at hOut
  change out.length ≤ processed at hOutLen
  have hEdgeIndexN : edgeIndex ≤ N := hEdgeIndex.trans hProcessed
  have hNextIndexN : nextIndex ≤ 2 * N := by nlinarith
  have hOutSize :
      dhcIndexedIncidenceListEncodedType.inputSize out ≤ out.length * (4 * N + 9) := by
    have hElems : ∀ x ∈ out, dhcIndexedIncidenceEncodedType.inputSize x ≤ 4 * N + 8 := by
      intro x hx
      exact dhcIndexedIncidenceBound_inputSize_le (hOut x hx) hProcessed
    simpa [dhcIndexedIncidenceListEncodedType] using
      VertexCover.encodedList_inputSize_le_length_mul_bound
        dhcIndexedIncidenceEncodedType out (4 * N + 8) hElems
  have hOutSizeN :
      dhcIndexedIncidenceListEncodedType.inputSize out ≤ N * (4 * N + 9) :=
    hOutSize.trans (Nat.mul_le_mul_right (4 * N + 9) (hOutLen.trans hProcessed))
  have hOutSizeN' :
      dhcIndexedIncidenceEncodedType.list.inputSize out ≤ N * (4 * N + 9) := by
    simpa [dhcIndexedIncidenceListEncodedType] using hOutSizeN
  simp [dhcRowScanAccEncodedType, dhcIndexedIncidenceListEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_nat]
  have hLinear : (N : Int) ≤ N * N + 1 := by
    nlinarith [sq_nonneg ((N : Int) - 1)]
  calc
    vertices + 1 + 1 +
        (u + 1 + 1 +
          (edgeIndex + 1 + 1 +
            (nextIndex + 1 + 1 + dhcIndexedIncidenceEncodedType.list.inputSize out))) ≤
        N + 1 + 1 +
          (N + 1 + 1 +
            (N + 1 + 1 + (2 * N + 1 + 1 + N * (4 * N + 9)))) := by
          nlinarith
    _ ≤ 1000 * (N * N) + 5000 := by
          nlinarith [sq_nonneg (N : Int), hLinear]

noncomputable def dhcRowScanFoldTimePolynomial
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod dhcRowScanAccEncodedType
          dhcRowFoldInstructionEncodedType).encode
        dhcRowScanAccEncodedType.encode
        dhcRowFoldStep) : Polynomial Nat :=
  TM2Programs.listFoldBoundedTimePolynomial hStep.tm dhcRowScanFoldAccBoundPolynomial
    (hStep.time.comp
      (dhcRowScanFoldAccBoundPolynomial + Polynomial.X + Polynomial.C 5))

theorem dhcRowScanFold_tm_polytime :
    TMPolyTimeMap
      dhcRowFoldInstructionListEncodedType
      dhcRowScanAccEncodedType
      (fun xs : List dhcRowFoldInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => dhcRowFoldStep (acc, instr)) dhcRowFoldInit) := by
  rcases dhcRowFoldStep_tm_polytime with ⟨hStep⟩
  let time := dhcRowScanFoldTimePolynomial hStep
  refine
    TMPolyTimeMap.list_foldl_typed
      dhcRowFoldInstructionEncodedType dhcRowScanAccEncodedType
      dhcRowFoldStep dhcRowFoldInit hStep time ?_
  intro source
  let N := dhcRowFoldInstructionListEncodedType.inputSize source
  let B := dhcRowScanFoldAccBoundPolynomial.eval N
  let T := hStep.time.eval (B + N + 5)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hSourceLenN : source.length ≤ N := by
    have hLen :=
      SetCovering.incidentEncodedList_length_le_inputSize dhcRowFoldInstructionEncodedType source
    simpa [N, dhcRowFoldInstructionListEncodedType] using hLen
  have hLoopAux :
      ∀ (pref rest : List dhcRowFoldInstructionEncodedType.Carrier),
        source = pref ++ rest →
          TM2Programs.listFoldTypedLoopTime
              dhcRowFoldInstructionEncodedType dhcRowScanAccEncodedType
              dhcRowFoldStep hStep
              (pref.foldl (fun acc instr => dhcRowFoldStep (acc, instr)) dhcRowFoldInit)
              rest ≤
            C * (EncodedType.list dhcRowFoldInstructionEncodedType).inputSize rest := by
    intro pref rest
    induction rest generalizing pref with
    | nil =>
        intro _hEq
        simp [TM2Programs.listFoldTypedLoopTime]
    | cons instr rest ih =>
        intro hEq
        have hInstrMemSource : instr ∈ source := by
          rw [hEq]
          simp
        have hInstrN : dhcRowFoldInstructionEncodedType.inputSize instr ≤ N := by
          have hElem :=
            SetCovering.incidentEncodedList_element_inputSize_le
              (X := dhcRowFoldInstructionEncodedType) (x := instr) (xs := source)
              hInstrMemSource
          simpa [N, dhcRowFoldInstructionListEncodedType] using hElem
        have hPrefixSize : dhcRowFoldInstructionListEncodedType.inputSize pref ≤ N := by
          have hEqSize :
              dhcRowFoldInstructionListEncodedType.inputSize source =
                dhcRowFoldInstructionListEncodedType.inputSize pref +
                  dhcRowFoldInstructionListEncodedType.inputSize (instr :: rest) := by
            rw [hEq]
            exact SetCovering.incidentEncodedList_inputSize_append
              dhcRowFoldInstructionEncodedType pref (instr :: rest)
          omega
        have hPrefixBound :=
          dhcRowScanFold_bound_of_inputSize_le (N := N) pref hPrefixSize
        have hPrefixLenN : pref.length ≤ N := by
          have hLen :=
            SetCovering.incidentEncodedList_length_le_inputSize
              dhcRowFoldInstructionEncodedType pref
          have hLen' : pref.length ≤ dhcRowFoldInstructionListEncodedType.inputSize pref := by
            simpa [dhcRowFoldInstructionListEncodedType] using hLen
          omega
        have hAccSize :
            dhcRowScanAccEncodedType.inputSize
                (pref.foldl (fun acc instr => dhcRowFoldStep (acc, instr))
                  dhcRowFoldInit) ≤ B := by
          simpa [B] using
            dhcRowScanAccBound_inputSize_le hPrefixBound hPrefixLenN
        have hStepProcessed : pref.length + 1 ≤ N := by
          have hLenEq : source.length = pref.length + (instr :: rest).length := by
            rw [hEq, List.length_append]
          simp only [List.length_cons] at hLenEq
          omega
        have hStepBound :=
          dhcRowFoldStep_bound hPrefixBound hInstrN
        have hStepSize :
            dhcRowScanAccEncodedType.inputSize
                (dhcRowFoldStep
                  (pref.foldl (fun acc instr => dhcRowFoldStep (acc, instr))
                    dhcRowFoldInit, instr)) ≤ B := by
          simpa [B] using
            dhcRowScanAccBound_inputSize_le hStepBound hStepProcessed
        have hStepTime :
            hStep.time.eval
                ((EncodedType.prod dhcRowScanAccEncodedType
                  dhcRowFoldInstructionEncodedType).inputSize
                  (pref.foldl (fun acc instr => dhcRowFoldStep (acc, instr))
                    dhcRowFoldInit, instr)) ≤ T := by
          have hArg :
              (EncodedType.prod dhcRowScanAccEncodedType
                dhcRowFoldInstructionEncodedType).inputSize
                  (pref.foldl (fun acc instr => dhcRowFoldStep (acc, instr))
                    dhcRowFoldInit, instr) ≤ B + N + 5 := by
            rw [EncodedType.inputSize_prod]
            change
              dhcRowScanAccEncodedType.inputSize
                    (pref.foldl (fun acc instr => dhcRowFoldStep (acc, instr))
                      dhcRowFoldInit) +
                  1 + dhcRowFoldInstructionEncodedType.inputSize instr ≤ B + N + 5
            omega
          exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
        have hBlock :
            TM2Programs.listFoldBlockTime hStep.tm
                (dhcRowFoldInstructionEncodedType.encode instr).length
                (dhcRowScanAccEncodedType.encode
                  (pref.foldl (fun acc instr => dhcRowFoldStep (acc, instr))
                    dhcRowFoldInit)).length
                (dhcRowScanAccEncodedType.encode
                  (dhcRowFoldStep
                    (pref.foldl (fun acc instr => dhcRowFoldStep (acc, instr))
                      dhcRowFoldInit, instr))).length
                (hStep.time.eval
                  ((EncodedType.prod dhcRowScanAccEncodedType
                    dhcRowFoldInstructionEncodedType).inputSize
                    (pref.foldl (fun acc instr => dhcRowFoldStep (acc, instr))
                      dhcRowFoldInit, instr))) ≤
              C * (dhcRowFoldInstructionEncodedType.inputSize instr + 1) := by
          exact
            TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
              (by simpa [EncodedType.inputSize] using hAccSize)
              (by simpa [EncodedType.inputSize] using hStepSize)
              hStepTime
        have hEqTail : source = (pref ++ [instr]) ++ rest := by
          rw [hEq]
          simp [List.append_assoc]
        have hTailRaw := ih (pref := pref ++ [instr]) hEqTail
        have hTail :
            TM2Programs.listFoldTypedLoopTime
                dhcRowFoldInstructionEncodedType dhcRowScanAccEncodedType
                dhcRowFoldStep hStep
                (dhcRowFoldStep
                  (pref.foldl (fun acc instr => dhcRowFoldStep (acc, instr))
                    dhcRowFoldInit, instr)) rest ≤
              C * (EncodedType.list dhcRowFoldInstructionEncodedType).inputSize rest := by
          have hFoldPref :
              (pref ++ [instr]).foldl
                  (fun acc instr => dhcRowFoldStep (acc, instr)) dhcRowFoldInit =
                dhcRowFoldStep
                  (pref.foldl (fun acc instr => dhcRowFoldStep (acc, instr))
                    dhcRowFoldInit, instr) := by
            exact
              List.foldl_concat
                (fun acc instr => dhcRowFoldStep (acc, instr)) dhcRowFoldInit instr pref
          convert hTailRaw using 1
          exact congrArg
            (fun acc =>
              TM2Programs.listFoldTypedLoopTime
                dhcRowFoldInstructionEncodedType dhcRowScanAccEncodedType
                dhcRowFoldStep hStep acc rest)
            hFoldPref.symm
        calc
          TM2Programs.listFoldTypedLoopTime
              dhcRowFoldInstructionEncodedType dhcRowScanAccEncodedType
              dhcRowFoldStep hStep
              (pref.foldl (fun acc instr => dhcRowFoldStep (acc, instr)) dhcRowFoldInit)
              (instr :: rest)
              =
            TM2Programs.listFoldTypedLoopTime
                dhcRowFoldInstructionEncodedType dhcRowScanAccEncodedType
                dhcRowFoldStep hStep
                (dhcRowFoldStep
                  (pref.foldl (fun acc instr => dhcRowFoldStep (acc, instr))
                    dhcRowFoldInit, instr)) rest +
              TM2Programs.listFoldBlockTime hStep.tm
                (dhcRowFoldInstructionEncodedType.encode instr).length
                (dhcRowScanAccEncodedType.encode
                  (pref.foldl (fun acc instr => dhcRowFoldStep (acc, instr))
                    dhcRowFoldInit)).length
                (dhcRowScanAccEncodedType.encode
                  (dhcRowFoldStep
                    (pref.foldl (fun acc instr => dhcRowFoldStep (acc, instr))
                      dhcRowFoldInit, instr))).length
                (hStep.time.eval
                  ((EncodedType.prod dhcRowScanAccEncodedType
                    dhcRowFoldInstructionEncodedType).inputSize
                    (pref.foldl (fun acc instr => dhcRowFoldStep (acc, instr))
                      dhcRowFoldInit, instr))) := by
                rfl
          _ ≤
              C * (EncodedType.list dhcRowFoldInstructionEncodedType).inputSize rest +
                C * (dhcRowFoldInstructionEncodedType.inputSize instr + 1) :=
                Nat.add_le_add hTail hBlock
          _ ≤ C * (EncodedType.list dhcRowFoldInstructionEncodedType).inputSize
              (instr :: rest) := by
                rw [EncodedType.inputSize_list_cons]
                nlinarith
  have hLoop :
      TM2Programs.listFoldTypedLoopTime
          dhcRowFoldInstructionEncodedType dhcRowScanAccEncodedType
          dhcRowFoldStep hStep dhcRowFoldInit source ≤ C * N := by
    have h := hLoopAux [] source (by simp)
    simpa [N, dhcRowFoldInstructionListEncodedType] using h
  have hTimeEval : time.eval N = (C + 2) * (N + 1) := by
    simp [time, dhcRowScanFoldTimePolynomial, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval, TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_comp]
  change 2 +
      TM2Programs.listFoldTypedLoopTime
        dhcRowFoldInstructionEncodedType dhcRowScanAccEncodedType
        dhcRowFoldStep hStep dhcRowFoldInit source ≤ time.eval N
  rw [hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

theorem dhcRowScanFromInput_tm_polytime :
    TMPolyTimeMap
      dhcRowScanInputEncodedType
      dhcRowScanAccEncodedType
      dhcRowScanFromInput := by
  have hComp :=
    TMPolyTimeMap.comp dhcRowScanFold_tm_polytime dhcRowScanInstructions_tm_polytime
  simpa [Function.comp, dhcRowScanFromInput, dhcRowScanResult] using hComp

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
