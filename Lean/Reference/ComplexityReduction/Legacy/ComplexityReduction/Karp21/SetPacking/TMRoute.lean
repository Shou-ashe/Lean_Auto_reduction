/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SetPacking.StructuredRoute

/-!
Direct TM-backed structured Clique-to-Set-Packing route.

This file is separated from `StructuredRoute.lean` so the semantic route stays
below the local line-count budget while the machine-facing runner evidence grows.
-/

namespace ComplexityReduction
namespace Karp21
namespace SetPacking

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-! ### Compact-route size bounds -/

theorem compactCodedComplementEdges_length_le (I : CliqueInput) :
    (compactCodedComplementEdges I).length ≤ I.graph.vertices * I.graph.vertices := by
  rw [compactCodedComplementEdges, codeComplementEdgesFrom_length]
  simpa [VertexCover.complementEdges, structuredComplementEdges] using
    VertexCover.complementEdges_length_le I.graph

theorem compactIncidentCodes_length_le_aux
    (codedEdges : List CodedComplementEdge) (v : Nat) (out : List Nat) :
    (codedEdges.foldl
        (fun out ce => if codedEdgeIncidentBool (v, ce) then out ++ [ce.1] else out)
        out).length ≤ out.length + codedEdges.length := by
  induction codedEdges generalizing out with
  | nil =>
      simp
  | cons ce rest ih =>
      by_cases hIncident : codedEdgeIncidentBool (v, ce) = true
      · have hTail := ih (out ++ [ce.1])
        calc
          ((ce :: rest).foldl
              (fun out ce => if codedEdgeIncidentBool (v, ce) then out ++ [ce.1] else out)
              out).length
              =
            (rest.foldl
              (fun out ce => if codedEdgeIncidentBool (v, ce) then out ++ [ce.1] else out)
              (out ++ [ce.1])).length := by
              simp [hIncident]
          _ ≤ (out ++ [ce.1]).length + rest.length := hTail
          _ ≤ out.length + (ce :: rest).length := by
            simp
            omega
      · have hFalse : codedEdgeIncidentBool (v, ce) = false := by
          cases h : codedEdgeIncidentBool (v, ce)
          · rfl
          · exact False.elim (hIncident h)
        have hTail := ih out
        calc
          ((ce :: rest).foldl
              (fun out ce => if codedEdgeIncidentBool (v, ce) then out ++ [ce.1] else out)
              out).length
              =
            (rest.foldl
              (fun out ce => if codedEdgeIncidentBool (v, ce) then out ++ [ce.1] else out)
              out).length := by
              simp [hFalse]
          _ ≤ out.length + rest.length := hTail
          _ ≤ out.length + (ce :: rest).length := by simp

theorem compactIncidentCodes_length_le (codedEdges : List CodedComplementEdge) (v : Nat) :
    (compactIncidentCodes v codedEdges).length ≤ codedEdges.length := by
  simpa [compactIncidentCodes] using
    compactIncidentCodes_length_le_aux codedEdges v ([] : List Nat)

theorem compactPackingSetFromCodes_length_le
    (codedEdges : List CodedComplementEdge) (v : Nat) :
    (compactPackingSetFromCodes v codedEdges).length ≤ 1 + codedEdges.length := by
  have h := compactIncidentCodes_length_le codedEdges v
  simp [compactPackingSetFromCodes]
  omega

theorem compactPackingSetFromCodes_nat_inputSize_le
    (I : CliqueInput) {v x : Nat}
    (hv : v < I.graph.vertices)
    (hx : x ∈ compactPackingSetFromCodes v (compactCodedComplementEdges I)) :
    EncodedType.nat.inputSize x ≤
      I.graph.vertices + I.graph.vertices * I.graph.vertices + 1 := by
  rcases (mem_compactPackingSetFromCodes_iff (compactCodedComplementEdges I) v x).1 hx with
    hxMarker | hxCode
  · subst x
    simp [EncodedType.inputSize_nat]
    omega
  · rcases hxCode with ⟨ce, hMem, hCode, _hInc⟩
    subst x
    have hLt := codeComplementEdgesFrom_mem_code_lt hMem
    have hLen := VertexCover.complementEdges_length_le I.graph
    have hLen' :
        (structuredComplementEdges I.graph).length ≤
          I.graph.vertices * I.graph.vertices := by
      simpa [VertexCover.complementEdges] using hLen
    simp at hLt
    simp [EncodedType.inputSize_nat]
    omega

theorem compactPackingSetFromCodes_structured_inputSize_le
    (I : CliqueInput) {v : Nat} (hv : v < I.graph.vertices) :
    setStructuredEncodedType.inputSize
        (compactPackingSetFromCodes v (compactCodedComplementEdges I)) ≤
      (1 + I.graph.vertices * I.graph.vertices) *
        (I.graph.vertices + I.graph.vertices * I.graph.vertices + 2) := by
  have hList :=
    VertexCover.encodedList_inputSize_le_length_mul_bound
      EncodedType.nat
      (compactPackingSetFromCodes v (compactCodedComplementEdges I))
      (I.graph.vertices + I.graph.vertices * I.graph.vertices + 1)
      (by
        intro x hx
        exact compactPackingSetFromCodes_nat_inputSize_le I hv hx)
  have hLen₀ :=
    compactPackingSetFromCodes_length_le (compactCodedComplementEdges I) v
  have hLen₁ := compactCodedComplementEdges_length_le I
  exact hList.trans (by
    have hLen :
        (compactPackingSetFromCodes v (compactCodedComplementEdges I)).length ≤
          1 + I.graph.vertices * I.graph.vertices := by
      omega
    exact Nat.mul_le_mul_right
      (I.graph.vertices + I.graph.vertices * I.graph.vertices + 2) hLen)

theorem compactSetFamilyFromCodes_structured_inputSize_le (I : CliqueInput) :
    setFamilyStructuredEncodedType.inputSize
        (compactSetFamilyFromCodes I.graph.vertices (compactCodedComplementEdges I)) ≤
      I.graph.vertices *
        ((1 + I.graph.vertices * I.graph.vertices) *
          (I.graph.vertices + I.graph.vertices * I.graph.vertices + 2) + 1) := by
  have hList :=
    VertexCover.encodedList_inputSize_le_length_mul_bound
      setStructuredEncodedType
      (compactSetFamilyFromCodes I.graph.vertices (compactCodedComplementEdges I))
      ((1 + I.graph.vertices * I.graph.vertices) *
        (I.graph.vertices + I.graph.vertices * I.graph.vertices + 2))
      (by
        intro S hS
        rcases (mem_compactSetFamilyFromCodes_iff I.graph.vertices
            (compactCodedComplementEdges I) S).1 hS with
          ⟨v, hv, rfl⟩
        exact compactPackingSetFromCodes_structured_inputSize_le I hv)
  have hLen :
      (compactSetFamilyFromCodes I.graph.vertices (compactCodedComplementEdges I)).length =
        I.graph.vertices := by
    simp [compactSetFamilyFromCodes]
  exact hList.trans (by
    exact Nat.mul_le_mul_right
      ((1 + I.graph.vertices * I.graph.vertices) *
        (I.graph.vertices + I.graph.vertices * I.graph.vertices + 2) + 1)
      (le_of_eq hLen))

theorem compactSetSystem_structured_inputSize_le (I : CliqueInput) :
    setSystemStructuredEncodedType.inputSize (compactMap I).system ≤
      (I.graph.vertices + I.graph.vertices * I.graph.vertices) +
        I.graph.vertices *
          ((1 + I.graph.vertices * I.graph.vertices) *
            (I.graph.vertices + I.graph.vertices * I.graph.vertices + 2) + 1) + 2 := by
  let acc := codeComplementEdgesFrom I.graph.vertices (structuredComplementEdges I.graph)
  have hFamily := compactSetFamilyFromCodes_structured_inputSize_le I
  have hUniverse :
      (compactMap I).system.universeSize ≤
        I.graph.vertices + I.graph.vertices * I.graph.vertices := by
    have hFst := codeComplementEdgesFrom_fst I.graph.vertices (structuredComplementEdges I.graph)
    have hLen := VertexCover.complementEdges_length_le I.graph
    simp [compactMap, compactSetSystemFromAcc, VertexCover.complementEdges,
      structuredComplementEdges] at hFst hLen ⊢
    omega
  rw [setSystemStructured_inputSize_eq]
  change
    (compactMap I).system.universeSize +
        setFamilyStructuredEncodedType.inputSize (compactMap I).system.sets + 2 ≤
      (I.graph.vertices + I.graph.vertices * I.graph.vertices) +
        I.graph.vertices *
          ((1 + I.graph.vertices * I.graph.vertices) *
            (I.graph.vertices + I.graph.vertices * I.graph.vertices + 2) + 1) + 2
  have hSets :
      setFamilyStructuredEncodedType.inputSize (compactMap I).system.sets ≤
        I.graph.vertices *
          ((1 + I.graph.vertices * I.graph.vertices) *
            (I.graph.vertices + I.graph.vertices * I.graph.vertices + 2) + 1) := by
    simpa [compactMap, compactSetSystemFromAcc, compactCodedComplementEdges]
      using hFamily
  omega

theorem setPackingStructured_inputSize_compactMap_le_clique_poly (I : CliqueInput) :
    setPackingStructuredEncodedType.inputSize (compactMap I) ≤
      10000000 * (cliqueStructuredEncodedType.inputSize I) ^ 6 + 10000000 := by
  let S := cliqueStructuredEncodedType.inputSize I
  let n := I.graph.vertices
  have hSystem := compactSetSystem_structured_inputSize_le I
  have hNsucc : n + 1 ≤ S := by
    simpa [S, n] using VertexCover.cliqueStructured_inputSize_ge_vertices_succ I
  have hN : n ≤ S := by omega
  have hK : I.k ≤ S := by
    simpa [S] using cliqueStructured_inputSize_ge_budget I
  calc
    setPackingStructuredEncodedType.inputSize (compactMap I)
        = setSystemStructuredEncodedType.inputSize (compactMap I).system + I.k + 2 := by
            simp [setPackingStructured_inputSize_eq, compactMap]
    _ ≤ ((n + n * n) +
          n * ((1 + n * n) * (n + n * n + 2) + 1) + 2) + I.k + 2 := by
            simpa [n] using Nat.add_le_add_right (Nat.add_le_add_right hSystem I.k) 2
    _ ≤ ((S + S * S) +
          S * ((1 + S * S) * (S + S * S + 2) + 1) + 2) + S + 2 := by
            have hn2 : n * n ≤ S * S := Nat.mul_le_mul hN hN
            have hA : n + n * n ≤ S + S * S := Nat.add_le_add hN hn2
            have hB :
                (1 + n * n) * (n + n * n + 2) + 1 ≤
                  (1 + S * S) * (S + S * S + 2) + 1 := by
              have hLeft₁ : 1 + n * n ≤ 1 + S * S := by omega
              have hLeft₂ : n + n * n + 2 ≤ S + S * S + 2 := by omega
              exact Nat.add_le_add_right (Nat.mul_le_mul hLeft₁ hLeft₂) 1
            have hFam : n * ((1 + n * n) * (n + n * n + 2) + 1) ≤
                S * ((1 + S * S) * (S + S * S + 2) + 1) :=
              Nat.mul_le_mul hN hB
            omega
    _ ≤ 100000 * (S + 1) ^ 6 + 100000 := by
            ring_nf
            omega
    _ ≤ 10000000 * S ^ 6 + 10000000 := by
            cases S with
            | zero =>
                omega
            | succ S =>
                ring_nf
                omega

theorem cliqueToSetPackingStructured_compactPolynomialSizeBound :
    PolynomialSizeBound
      (fun I : CliqueInput => cliqueStructuredEncodedType.inputSize I)
      (fun J : SetPackingInput => setPackingStructuredEncodedType.inputSize J)
      compactMap := by
  refine PolynomialSizeBound.intro_with 6 10000000 10000000 ?_
  intro I
  exact setPackingStructured_inputSize_compactMap_le_clique_poly I

/-! ### Conflict-code runner TM evidence -/

theorem encodedList_length_le_inputSize_local (X : EncodedType) (xs : List X.Carrier) :
    xs.length ≤ (EncodedType.list X).inputSize xs := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [EncodedType.inputSize_list_cons]
      simp only [List.length_cons]
      omega

theorem encodedList_element_inputSize_le_local {X : EncodedType} {x : X.Carrier}
    {xs : List X.Carrier} (hx : x ∈ xs) :
    X.inputSize x ≤ (EncodedType.list X).inputSize xs := by
  induction xs with
  | nil =>
      simp at hx
  | cons y ys ih =>
      rw [EncodedType.inputSize_list_cons]
      rcases List.mem_cons.mp hx with hxy | hxys
      · subst x
        omega
      · have hTail := ih hxys
        omega

theorem encodedList_inputSize_append_local (X : EncodedType)
    (xs ys : List X.Carrier) :
    (EncodedType.list X).inputSize (xs ++ ys) =
      (EncodedType.list X).inputSize xs + (EncodedType.list X).inputSize ys := by
  simp [EncodedType.inputSize, EncodedType.list, List.flatMap_append]

def codeComplementEdgeScanAccBound
    (N processed : Nat) (acc : CodeComplementEdgesAcc) : Prop :=
  acc.1 ≤ N + processed ∧
    (∀ ce ∈ acc.2, ce.1 ≤ N + processed ∧ ce.2.1 ≤ N ∧ ce.2.2 ≤ N) ∧
      acc.2.length ≤ processed

theorem codeComplementEdgeScanStep_bound {N processed : Nat}
    {acc : CodeComplementEdgesAcc}
    {instr : codeComplementEdgeInstructionEncodedType.Carrier}
    (hAcc : codeComplementEdgeScanAccBound N processed acc)
    (hInstr : codeComplementEdgeInstructionEncodedType.inputSize instr ≤ N) :
    codeComplementEdgeScanAccBound N (processed + 1)
      (codeComplementEdgeScanStep (acc, instr)) := by
  rcases acc with ⟨next, out⟩
  rcases instr with ⟨tag, payload⟩
  rcases payload with ⟨start, edge⟩
  rcases edge with ⟨u, v⟩
  change Nat at start
  change Nat at u
  change Nat at v
  rcases hAcc with ⟨hNext, hOutMem, hOutLen⟩
  cases tag
  · have hStart : start ≤ N := by
      simp [codeComplementEdgeInstructionEncodedType,
        codeComplementEdgeInstructionPayloadEncodedType, edgeStructuredEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_bool,
        EncodedType.inputSize_nat] at hInstr
      omega
    change codeComplementEdgeScanAccBound N (processed + 1)
      (start, ([] : List CodedComplementEdge))
    unfold codeComplementEdgeScanAccBound
    refine ⟨by omega, ?_, by simp⟩
    intro ce hce
    simp at hce
  · have hu : u ≤ N := by
      simp [codeComplementEdgeInstructionEncodedType,
        codeComplementEdgeInstructionPayloadEncodedType, edgeStructuredEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_bool,
        EncodedType.inputSize_nat] at hInstr
      omega
    have hv : v ≤ N := by
      simp [codeComplementEdgeInstructionEncodedType,
        codeComplementEdgeInstructionPayloadEncodedType, edgeStructuredEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_bool,
        EncodedType.inputSize_nat] at hInstr
      omega
    change codeComplementEdgeScanAccBound N (processed + 1)
      (Nat.succ next, out ++ [(next, (u, v))])
    unfold codeComplementEdgeScanAccBound
    refine ⟨by omega, ?_, by simp [hOutLen]⟩
    intro ce hce
    rcases List.mem_append.mp hce with hOld | hNew
    · rcases hOutMem ce hOld with ⟨hCode, hLeft, hRight⟩
      exact ⟨by omega, hLeft, hRight⟩
    · have hceEq : ce = (next, (u, v)) := by simpa using hNew
      subst ce
      exact ⟨by omega, hu, hv⟩

theorem codeComplementEdgeScanFold_bound_aux
    {N processed : Nat}
    (xs : List codeComplementEdgeInstructionEncodedType.Carrier)
    (acc : codeComplementEdgesAccEncodedType.Carrier)
    (hAcc : codeComplementEdgeScanAccBound N processed acc)
    (hInstr : ∀ instr ∈ xs, codeComplementEdgeInstructionEncodedType.inputSize instr ≤ N) :
    codeComplementEdgeScanAccBound N (processed + xs.length)
      (xs.foldl (fun acc instr => codeComplementEdgeScanStep (acc, instr)) acc) := by
  induction xs generalizing processed acc with
  | nil =>
      simpa using hAcc
  | cons x xs ih =>
      have hx : codeComplementEdgeInstructionEncodedType.inputSize x ≤ N := hInstr x (by simp)
      have hStep := codeComplementEdgeScanStep_bound hAcc hx
      have hTailInstr :
          ∀ instr ∈ xs, codeComplementEdgeInstructionEncodedType.inputSize instr ≤ N := by
        intro instr hin
        exact hInstr instr (by simp [hin])
      have hTail :=
        ih (processed := processed + 1)
          (acc := codeComplementEdgeScanStep (acc, x)) hStep hTailInstr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hTail

theorem codeComplementEdgeScanFold_bound_of_inputSize_le
    {N : Nat} (xs : List codeComplementEdgeInstructionEncodedType.Carrier)
    (hSize : codeComplementEdgeInstructionListEncodedType.inputSize xs ≤ N) :
    codeComplementEdgeScanAccBound N xs.length
      (xs.foldl (fun acc instr => codeComplementEdgeScanStep (acc, instr))
        codeComplementEdgeScanInit) := by
  have hInit : codeComplementEdgeScanAccBound N 0 codeComplementEdgeScanInit := by
    simp [codeComplementEdgeScanAccBound, codeComplementEdgeScanInit]
  have hInstr :
      ∀ instr ∈ xs, codeComplementEdgeInstructionEncodedType.inputSize instr ≤ N := by
    intro instr hin
    have hElem := encodedList_element_inputSize_le_local
      (X := codeComplementEdgeInstructionEncodedType) (x := instr) (xs := xs) hin
    have hElem' :
        codeComplementEdgeInstructionEncodedType.inputSize instr ≤
          codeComplementEdgeInstructionListEncodedType.inputSize xs := by
      simpa [codeComplementEdgeInstructionListEncodedType] using hElem
    omega
  have h :=
    codeComplementEdgeScanFold_bound_aux (N := N) (processed := 0) xs
      codeComplementEdgeScanInit hInit hInstr
  simpa using h

noncomputable def codeComplementEdgeScanFoldAccBoundPolynomial : Polynomial Nat :=
  Polynomial.C 100 * (Polynomial.X * Polynomial.X) + Polynomial.C 1000

@[simp] theorem codeComplementEdgeScanFoldAccBoundPolynomial_eval (N : Nat) :
    codeComplementEdgeScanFoldAccBoundPolynomial.eval N = 100 * (N * N) + 1000 := by
  simp [codeComplementEdgeScanFoldAccBoundPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_X]

theorem codeComplementEdgeScanAccBound_inputSize_le {N processed : Nat}
    {acc : CodeComplementEdgesAcc}
    (hAcc : codeComplementEdgeScanAccBound N processed acc)
    (hProcessed : processed ≤ N) :
    codeComplementEdgesAccEncodedType.inputSize acc ≤
      codeComplementEdgeScanFoldAccBoundPolynomial.eval N := by
  rcases acc with ⟨next, out⟩
  rcases hAcc with ⟨hNext, hOutMem, hOutLen⟩
  have hNextN : next ≤ 2 * N := by omega
  have hOutSize :
      codedComplementEdgeListEncodedType.inputSize out ≤
        processed * (4 * N + 20 + 1) := by
    have hElems :
        ∀ ce ∈ out,
          codedComplementEdgeEncodedType.inputSize ce ≤ 4 * N + 20 := by
      intro ce hce
      rcases ce with ⟨code, edge⟩
      rcases edge with ⟨u, v⟩
      rcases hOutMem (code, (u, v)) hce with ⟨hCode, hu, hv⟩
      have hCode' : code ≤ N + processed := by simpa using hCode
      have hu' : u ≤ N := by simpa using hu
      have hv' : v ≤ N := by simpa using hv
      simp [codedComplementEdgeEncodedType, vertexPairEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_nat]
      omega
    have hList :=
      VertexCover.encodedList_inputSize_le_length_mul_bound
        codedComplementEdgeEncodedType out (4 * N + 20) hElems
    exact hList.trans (Nat.mul_le_mul_right (4 * N + 20 + 1) hOutLen)
  have hOutSizeN :
      codedComplementEdgeListEncodedType.inputSize out ≤
        N * (4 * N + 21) := by
    exact hOutSize.trans (Nat.mul_le_mul_right (4 * N + 21) hProcessed)
  have hOutSizeN' :
      (EncodedType.list codedComplementEdgeEncodedType).inputSize out ≤
        N * (4 * N + 21) := by
    simpa [codedComplementEdgeListEncodedType] using hOutSizeN
  calc
    codeComplementEdgesAccEncodedType.inputSize (next, out)
        ≤ 2 * N + 2 + N * (4 * N + 21) := by
          simp [codeComplementEdgesAccEncodedType, codedComplementEdgeListEncodedType,
            EncodedType.inputSize_prod, EncodedType.inputSize_nat]
          omega
    _ ≤ codeComplementEdgeScanFoldAccBoundPolynomial.eval N := by
          simp [codeComplementEdgeScanFoldAccBoundPolynomial_eval]
          nlinarith [sq_nonneg (N : Int)]

noncomputable def codeComplementEdgeScanFoldTimePolynomial
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod codeComplementEdgesAccEncodedType
          codeComplementEdgeInstructionEncodedType).encode
        codeComplementEdgesAccEncodedType.encode
        codeComplementEdgeScanStep) : Polynomial Nat :=
  TM2Programs.listFoldBoundedTimePolynomial hStep.tm
    codeComplementEdgeScanFoldAccBoundPolynomial
    (hStep.time.comp
      (codeComplementEdgeScanFoldAccBoundPolynomial + Polynomial.X + Polynomial.C 5))

theorem codeComplementEdgeScanFold_tm_polytime :
    TMPolyTimeMap
      codeComplementEdgeInstructionListEncodedType
      codeComplementEdgesAccEncodedType
      (fun xs : List codeComplementEdgeInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => codeComplementEdgeScanStep (acc, instr))
          codeComplementEdgeScanInit) := by
  rcases codeComplementEdgeScanStep_tm_polytime with ⟨hStep⟩
  let time := codeComplementEdgeScanFoldTimePolynomial hStep
  refine
    TMPolyTimeMap.list_foldl_typed
      codeComplementEdgeInstructionEncodedType codeComplementEdgesAccEncodedType
      codeComplementEdgeScanStep codeComplementEdgeScanInit hStep time ?_
  intro source
  let N := codeComplementEdgeInstructionListEncodedType.inputSize source
  let B := codeComplementEdgeScanFoldAccBoundPolynomial.eval N
  let T := hStep.time.eval (B + N + 5)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hLoopAux :
      ∀ (pref rest : List codeComplementEdgeInstructionEncodedType.Carrier),
        source = pref ++ rest →
          TM2Programs.listFoldTypedLoopTime
              codeComplementEdgeInstructionEncodedType codeComplementEdgesAccEncodedType
              codeComplementEdgeScanStep hStep
              (pref.foldl (fun acc instr => codeComplementEdgeScanStep (acc, instr))
                codeComplementEdgeScanInit)
              rest ≤
            C * (EncodedType.list codeComplementEdgeInstructionEncodedType).inputSize rest := by
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
        have hxN : codeComplementEdgeInstructionEncodedType.inputSize x ≤ N := by
          have hElem := encodedList_element_inputSize_le_local
            (X := codeComplementEdgeInstructionEncodedType) (x := x) (xs := source)
            hxMemSource
          simpa [N, codeComplementEdgeInstructionListEncodedType] using hElem
        have hPrefixSize : codeComplementEdgeInstructionListEncodedType.inputSize pref ≤ N := by
          have hEqSize :
              codeComplementEdgeInstructionListEncodedType.inputSize source =
                codeComplementEdgeInstructionListEncodedType.inputSize pref +
                  codeComplementEdgeInstructionListEncodedType.inputSize (x :: xs) := by
            rw [hEq]
            exact encodedList_inputSize_append_local codeComplementEdgeInstructionEncodedType
              pref (x :: xs)
          omega
        have hPrefixBound :=
          codeComplementEdgeScanFold_bound_of_inputSize_le (N := N) pref hPrefixSize
        have hPrefixLenN : pref.length ≤ N := by
          have hLen :=
            encodedList_length_le_inputSize_local codeComplementEdgeInstructionEncodedType pref
          have hLen' :
              pref.length ≤ codeComplementEdgeInstructionListEncodedType.inputSize pref := by
            simpa [codeComplementEdgeInstructionListEncodedType] using hLen
          omega
        have hAccSize :
            codeComplementEdgesAccEncodedType.inputSize
                (pref.foldl (fun acc instr => codeComplementEdgeScanStep (acc, instr))
                  codeComplementEdgeScanInit) ≤ B := by
          simpa [B] using
            codeComplementEdgeScanAccBound_inputSize_le hPrefixBound hPrefixLenN
        have hStepProcessed : pref.length + 1 ≤ N := by
          have hLenEq : source.length = pref.length + (x :: xs).length := by
            rw [hEq, List.length_append]
          simp only [List.length_cons] at hLenEq
          have hSourceLenN : source.length ≤ N := by
            have hLen :=
              encodedList_length_le_inputSize_local codeComplementEdgeInstructionEncodedType source
            simpa [N, codeComplementEdgeInstructionListEncodedType] using hLen
          omega
        have hStepBound :=
          codeComplementEdgeScanStep_bound hPrefixBound hxN
        have hStepSize :
            codeComplementEdgesAccEncodedType.inputSize
                (codeComplementEdgeScanStep
                  (pref.foldl (fun acc instr => codeComplementEdgeScanStep (acc, instr))
                    codeComplementEdgeScanInit, x)) ≤ B := by
          simpa [B] using
            codeComplementEdgeScanAccBound_inputSize_le hStepBound hStepProcessed
        have hStepTime :
            hStep.time.eval
                ((EncodedType.prod codeComplementEdgesAccEncodedType
                  codeComplementEdgeInstructionEncodedType).inputSize
                  (pref.foldl (fun acc instr => codeComplementEdgeScanStep (acc, instr))
                    codeComplementEdgeScanInit, x)) ≤ T := by
          have hArg :
              (EncodedType.prod codeComplementEdgesAccEncodedType
                codeComplementEdgeInstructionEncodedType).inputSize
                  (pref.foldl (fun acc instr => codeComplementEdgeScanStep (acc, instr))
                    codeComplementEdgeScanInit, x) ≤ B + N + 5 := by
            rw [EncodedType.inputSize_prod]
            change
              codeComplementEdgesAccEncodedType.inputSize
                    (pref.foldl (fun acc instr => codeComplementEdgeScanStep (acc, instr))
                      codeComplementEdgeScanInit) +
                  1 + codeComplementEdgeInstructionEncodedType.inputSize x ≤ B + N + 5
            omega
          exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
        have hBlock :
            TM2Programs.listFoldBlockTime hStep.tm
                (codeComplementEdgeInstructionEncodedType.encode x).length
                (codeComplementEdgesAccEncodedType.encode
                  (pref.foldl (fun acc instr => codeComplementEdgeScanStep (acc, instr))
                    codeComplementEdgeScanInit)).length
                (codeComplementEdgesAccEncodedType.encode
                  (codeComplementEdgeScanStep
                    (pref.foldl (fun acc instr => codeComplementEdgeScanStep (acc, instr))
                      codeComplementEdgeScanInit, x))).length
                (hStep.time.eval
                  ((EncodedType.prod codeComplementEdgesAccEncodedType
                    codeComplementEdgeInstructionEncodedType).inputSize
                    (pref.foldl (fun acc instr => codeComplementEdgeScanStep (acc, instr))
                      codeComplementEdgeScanInit, x))) ≤
              C * (codeComplementEdgeInstructionEncodedType.inputSize x + 1) := by
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
                codeComplementEdgeInstructionEncodedType codeComplementEdgesAccEncodedType
                codeComplementEdgeScanStep hStep
                (codeComplementEdgeScanStep
                  (pref.foldl (fun acc instr => codeComplementEdgeScanStep (acc, instr))
                    codeComplementEdgeScanInit, x)) xs ≤
              C * (EncodedType.list codeComplementEdgeInstructionEncodedType).inputSize xs := by
          have hFoldPref :
              (pref ++ [x]).foldl
                  (fun acc instr => codeComplementEdgeScanStep (acc, instr))
                  codeComplementEdgeScanInit =
                codeComplementEdgeScanStep
                  (pref.foldl (fun acc instr => codeComplementEdgeScanStep (acc, instr))
                    codeComplementEdgeScanInit, x) := by
            exact
              List.foldl_concat
                (fun acc instr => codeComplementEdgeScanStep (acc, instr))
                codeComplementEdgeScanInit x pref
          convert hTailRaw using 1
          exact congrArg
            (fun acc =>
              TM2Programs.listFoldTypedLoopTime
                codeComplementEdgeInstructionEncodedType codeComplementEdgesAccEncodedType
                codeComplementEdgeScanStep hStep acc xs)
            hFoldPref.symm
        calc
          TM2Programs.listFoldTypedLoopTime
              codeComplementEdgeInstructionEncodedType codeComplementEdgesAccEncodedType
              codeComplementEdgeScanStep hStep
              (pref.foldl (fun acc instr => codeComplementEdgeScanStep (acc, instr))
                codeComplementEdgeScanInit)
              (x :: xs)
              =
            TM2Programs.listFoldTypedLoopTime
                codeComplementEdgeInstructionEncodedType codeComplementEdgesAccEncodedType
                codeComplementEdgeScanStep hStep
                (codeComplementEdgeScanStep
                  (pref.foldl (fun acc instr => codeComplementEdgeScanStep (acc, instr))
                    codeComplementEdgeScanInit, x)) xs +
              TM2Programs.listFoldBlockTime hStep.tm
                (codeComplementEdgeInstructionEncodedType.encode x).length
                (codeComplementEdgesAccEncodedType.encode
                  (pref.foldl (fun acc instr => codeComplementEdgeScanStep (acc, instr))
                    codeComplementEdgeScanInit)).length
                (codeComplementEdgesAccEncodedType.encode
                  (codeComplementEdgeScanStep
                    (pref.foldl (fun acc instr => codeComplementEdgeScanStep (acc, instr))
                      codeComplementEdgeScanInit, x))).length
                (hStep.time.eval
                  ((EncodedType.prod codeComplementEdgesAccEncodedType
                    codeComplementEdgeInstructionEncodedType).inputSize
                    (pref.foldl (fun acc instr => codeComplementEdgeScanStep (acc, instr))
                      codeComplementEdgeScanInit, x))) := by
                rfl
          _ ≤
              C * (EncodedType.list codeComplementEdgeInstructionEncodedType).inputSize xs +
                C * (codeComplementEdgeInstructionEncodedType.inputSize x + 1) :=
                Nat.add_le_add hTail hBlock
          _ ≤ C * (EncodedType.list codeComplementEdgeInstructionEncodedType).inputSize
                (x :: xs) := by
                rw [EncodedType.inputSize_list_cons]
                nlinarith
  have hLoop :
      TM2Programs.listFoldTypedLoopTime
          codeComplementEdgeInstructionEncodedType codeComplementEdgesAccEncodedType
          codeComplementEdgeScanStep hStep codeComplementEdgeScanInit source ≤ C * N := by
    have h := hLoopAux [] source (by simp)
    simpa [N, codeComplementEdgeInstructionListEncodedType] using h
  have hTimeEval : time.eval N = (C + 2) * (N + 1) := by
    simp [time, codeComplementEdgeScanFoldTimePolynomial, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval,
      TM2Programs.listFoldBlockTimeCoeff, Polynomial.eval_add, Polynomial.eval_comp]
  change 2 +
      TM2Programs.listFoldTypedLoopTime
        codeComplementEdgeInstructionEncodedType codeComplementEdgesAccEncodedType
        codeComplementEdgeScanStep hStep codeComplementEdgeScanInit source ≤ time.eval N
  rw [hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

theorem codeComplementEdgesFromInstructions_tm_polytime :
    TMPolyTimeMap
      codeComplementEdgeInstructionListEncodedType
      codeComplementEdgesAccEncodedType
      codeComplementEdgesFromInstructions := by
  simpa [codeComplementEdgesFromInstructions] using codeComplementEdgeScanFold_tm_polytime

theorem codeComplementEdgesFromInput_tm_polytime :
    TMPolyTimeMap
      codeComplementEdgeInstructionInputEncodedType
      codeComplementEdgesAccEncodedType
      codeComplementEdgesFromInput := by
  have hComp :=
    TMPolyTimeMap.comp codeComplementEdgesFromInstructions_tm_polytime
      codeComplementEdgeInstructions_tm_polytime
  simpa [Function.comp, codeComplementEdgesFromInput] using hComp

end SetPacking
end Karp21
end ComplexityReduction
