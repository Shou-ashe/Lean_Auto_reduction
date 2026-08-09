/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.EdgeScan

/-!
TM-backed complement edge-list assembly for faithful structured graph encodings.

This layer consumes a source edge list and a precomputed strict candidate list,
then emits exactly the candidates that are source nonedges.  It is reusable for
both the Clique -> Vertex Cover and Chromatic Number -> Clique Cover complement
routes.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics.Graph

/-! ### Candidate-filter runner -/

def complementEdgeAccEncodedType : EncodedType :=
  EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType

def complementEdgeInstructionPayloadEncodedType : EncodedType :=
  EncodedType.prod edgeListStructuredEncodedType edgeStructuredEncodedType

def complementEdgeInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool complementEdgeInstructionPayloadEncodedType

def complementEdgeInstructionListEncodedType : EncodedType :=
  EncodedType.list complementEdgeInstructionEncodedType

def complementEdgeRunnerInit : List (Nat × Nat) × List (Nat × Nat) :=
  (([] : List (Nat × Nat)), ([] : List (Nat × Nat)))

def complementEdgeInitInstruction
    (sourceEdges : List (Nat × Nat)) :
    Bool × (List (Nat × Nat) × (Nat × Nat)) :=
  (false, (sourceEdges, edgeScanDefaultPair))

def complementEdgeCandidateInstruction
    (candidate : Nat × Nat) :
    Bool × (List (Nat × Nat) × (Nat × Nat)) :=
  (true, (([] : List (Nat × Nat)), candidate))

def complementEdgeRunnerStep
    (p :
      (List (Nat × Nat) × List (Nat × Nat)) ×
        (Bool × (List (Nat × Nat) × (Nat × Nat)))) :
    List (Nat × Nat) × List (Nat × Nat) :=
  match p.2.1 with
  | false => (p.2.2.1, [])
  | true =>
      let sourceEdges := p.1.1
      let outEdges := p.1.2
      let candidate := p.2.2.2
      match sourceNonedgeBool (candidate, sourceEdges) with
      | true => (sourceEdges, outEdges ++ [candidate])
      | false => (sourceEdges, outEdges)

def complementEdgeInstructions
    (p : List (Nat × Nat) × List (Nat × Nat)) :
    List (Bool × (List (Nat × Nat) × (Nat × Nat))) :=
  complementEdgeInitInstruction p.1 :: p.2.map complementEdgeCandidateInstruction

def complementEdgesFromInstructions
    (xs : List (Bool × (List (Nat × Nat) × (Nat × Nat)))) :
    List (Nat × Nat) :=
  (xs.foldl (fun acc x => complementEdgeRunnerStep (acc, x)) complementEdgeRunnerInit).2

def complementEdgesFromCandidates
    (p : List (Nat × Nat) × List (Nat × Nat)) : List (Nat × Nat) :=
  complementEdgesFromInstructions (complementEdgeInstructions p)

def structuredComplementEdges (g : GraphInput) : List (Nat × Nat) :=
  complementEdgesFromCandidates (g.edges, strictNatPairCandidates g.vertices)

/-! ### Semantics -/

theorem complementEdgeFoldCandidateInstructions_source
    (sourceEdges outEdges candidates : List (Nat × Nat)) :
    ((candidates.map complementEdgeCandidateInstruction).foldl
        (fun acc x => complementEdgeRunnerStep (acc, x)) (sourceEdges, outEdges)).1 =
      sourceEdges := by
  induction candidates generalizing outEdges with
  | nil =>
      simp
  | cons e es ih =>
      by_cases hNonedge : sourceNonedgeBool (e, sourceEdges) = true
      · simpa [complementEdgeRunnerStep, complementEdgeCandidateInstruction, hNonedge] using
          ih (outEdges ++ [e])
      · have hFalse : sourceNonedgeBool (e, sourceEdges) = false := by
          cases h : sourceNonedgeBool (e, sourceEdges)
          · rfl
          · exact False.elim (hNonedge h)
        simpa [complementEdgeRunnerStep, complementEdgeCandidateInstruction, hFalse] using
          ih outEdges

theorem mem_complementEdgeFoldCandidateInstructions_iff
    (sourceEdges outEdges candidates : List (Nat × Nat)) (e : Nat × Nat) :
    e ∈ ((candidates.map complementEdgeCandidateInstruction).foldl
        (fun acc x => complementEdgeRunnerStep (acc, x)) (sourceEdges, outEdges)).2 ↔
      e ∈ outEdges ∨
        e ∈ candidates ∧ sourceNonedgeBool (e, sourceEdges) = true := by
  induction candidates generalizing outEdges with
  | nil =>
      simp
  | cons c cs ih =>
      by_cases hNonedge : sourceNonedgeBool (c, sourceEdges) = true
      · rw [show
          ((c :: cs).map complementEdgeCandidateInstruction).foldl
              (fun acc x => complementEdgeRunnerStep (acc, x)) (sourceEdges, outEdges) =
            (cs.map complementEdgeCandidateInstruction).foldl
              (fun acc x => complementEdgeRunnerStep (acc, x)) (sourceEdges, outEdges ++ [c]) by
          simp [complementEdgeRunnerStep, complementEdgeCandidateInstruction, hNonedge]]
        rw [ih]
        constructor
        · intro h
          rcases h with hApp | hCs
          · rcases List.mem_append.mp hApp with hOut | hSingleton
            · exact Or.inl hOut
            · have hEq : e = c := by simpa using hSingleton
              subst e
              exact Or.inr ⟨by simp, hNonedge⟩
          · exact Or.inr ⟨by simp [hCs.1], hCs.2⟩
        · intro h
          rcases h with hOut | hCand
          · exact Or.inl (List.mem_append.mpr (Or.inl hOut))
          · rcases hCand with ⟨hMem, hScan⟩
            simp at hMem
            rcases hMem with hEq | hTail
            · subst e
              exact Or.inl (List.mem_append.mpr (Or.inr (by simp)))
            · exact Or.inr ⟨hTail, hScan⟩
      · have hFalse : sourceNonedgeBool (c, sourceEdges) = false := by
          cases h : sourceNonedgeBool (c, sourceEdges)
          · rfl
          · exact False.elim (hNonedge h)
        rw [show
          ((c :: cs).map complementEdgeCandidateInstruction).foldl
              (fun acc x => complementEdgeRunnerStep (acc, x)) (sourceEdges, outEdges) =
            (cs.map complementEdgeCandidateInstruction).foldl
              (fun acc x => complementEdgeRunnerStep (acc, x)) (sourceEdges, outEdges) by
          simp [complementEdgeRunnerStep, complementEdgeCandidateInstruction, hFalse]]
        rw [ih]
        constructor
        · intro h
          rcases h with hOut | hCs
          · exact Or.inl hOut
          · exact Or.inr ⟨by simp [hCs.1], hCs.2⟩
        · intro h
          rcases h with hOut | hCand
          · exact Or.inl hOut
          · rcases hCand with ⟨hMem, hScan⟩
            simp at hMem
            rcases hMem with hEq | hTail
            · subst e
              simp [hFalse] at hScan
            · exact Or.inr ⟨hTail, hScan⟩

theorem mem_complementEdgesFromCandidates_iff
    (sourceEdges candidates : List (Nat × Nat)) (e : Nat × Nat) :
    e ∈ complementEdgesFromCandidates (sourceEdges, candidates) ↔
      e ∈ candidates ∧ sourceNonedgeBool (e, sourceEdges) = true := by
  change
    e ∈ ((complementEdgeInitInstruction sourceEdges ::
        candidates.map complementEdgeCandidateInstruction).foldl
          (fun acc x => complementEdgeRunnerStep (acc, x)) complementEdgeRunnerInit).2 ↔
      e ∈ candidates ∧ sourceNonedgeBool (e, sourceEdges) = true
  rw [show
    (complementEdgeInitInstruction sourceEdges ::
        candidates.map complementEdgeCandidateInstruction).foldl
          (fun acc x => complementEdgeRunnerStep (acc, x)) complementEdgeRunnerInit =
      (candidates.map complementEdgeCandidateInstruction).foldl
        (fun acc x => complementEdgeRunnerStep (acc, x)) (sourceEdges, []) by
    rfl]
  rw [mem_complementEdgeFoldCandidateInstructions_iff sourceEdges [] candidates e]
  simp

theorem mem_structuredComplementEdges_iff (g : GraphInput) (e : Nat × Nat) :
    e ∈ structuredComplementEdges g ↔
      e.1 < g.vertices ∧ e.2 < g.vertices ∧ e.1 < e.2 ∧
        ¬ HasUndirectedEdge g e.1 e.2 := by
  rw [structuredComplementEdges, mem_complementEdgesFromCandidates_iff]
  rw [mem_strictNatPairCandidates_iff]
  constructor
  · rintro ⟨hCand, hNonedge⟩
    rcases hCand with ⟨hLeft, hRight, hStrict⟩
    have hNon :=
      (sourceNonedgeBool_graph_eq_true_iff g e.1 e.2).1 hNonedge
    exact ⟨hLeft, hRight, hStrict, hNon⟩
  · rintro ⟨hLeft, hRight, hStrict, hNonedge⟩
    exact ⟨⟨hLeft, hRight, hStrict⟩,
      (sourceNonedgeBool_graph_eq_true_iff g e.1 e.2).2 hNonedge⟩

theorem complementEdgeFoldCandidateInstructions_length_le
    (sourceEdges outEdges candidates : List (Nat × Nat)) :
    (((candidates.map complementEdgeCandidateInstruction).foldl
        (fun acc x => complementEdgeRunnerStep (acc, x)) (sourceEdges, outEdges)).2).length ≤
      outEdges.length + candidates.length := by
  induction candidates generalizing outEdges with
  | nil =>
      simp
  | cons e es ih =>
      by_cases hNonedge : sourceNonedgeBool (e, sourceEdges) = true
      · have hTail := ih (outEdges ++ [e])
        calc
          ((((e :: es).map complementEdgeCandidateInstruction).foldl
              (fun acc x => complementEdgeRunnerStep (acc, x)) (sourceEdges, outEdges)).2).length
              =
              (((es.map complementEdgeCandidateInstruction).foldl
                (fun acc x => complementEdgeRunnerStep (acc, x))
                (sourceEdges, outEdges ++ [e])).2).length := by
                simp [complementEdgeRunnerStep, complementEdgeCandidateInstruction, hNonedge]
          _ ≤ (outEdges ++ [e]).length + es.length := hTail
          _ ≤ outEdges.length + (e :: es).length := by simp; omega
      · have hFalse : sourceNonedgeBool (e, sourceEdges) = false := by
          cases h : sourceNonedgeBool (e, sourceEdges)
          · rfl
          · exact False.elim (hNonedge h)
        have hTail := ih outEdges
        calc
          ((((e :: es).map complementEdgeCandidateInstruction).foldl
              (fun acc x => complementEdgeRunnerStep (acc, x)) (sourceEdges, outEdges)).2).length
              =
              (((es.map complementEdgeCandidateInstruction).foldl
                (fun acc x => complementEdgeRunnerStep (acc, x)) (sourceEdges, outEdges)).2).length := by
                simp [complementEdgeRunnerStep, complementEdgeCandidateInstruction, hFalse]
          _ ≤ outEdges.length + es.length := hTail
          _ ≤ outEdges.length + (e :: es).length := by simp

theorem complementEdgesFromCandidates_length_le
    (p : List (Nat × Nat) × List (Nat × Nat)) :
    (complementEdgesFromCandidates p).length ≤ p.2.length := by
  rcases p with ⟨sourceEdges, candidates⟩
  have h :=
    complementEdgeFoldCandidateInstructions_length_le sourceEdges
      ([] : List (Nat × Nat)) candidates
  simpa [complementEdgesFromCandidates, complementEdgesFromInstructions,
    complementEdgeInstructions, complementEdgeRunnerInit, complementEdgeInitInstruction,
    complementEdgeRunnerStep] using h

/-! ### Size bounds -/

theorem edgeList_inputSize_singleton (e : Nat × Nat) :
    edgeListStructuredEncodedType.inputSize [e] =
      edgeStructuredEncodedType.inputSize e + 1 := by
  simp [edgeListStructuredEncodedType, EncodedType.inputSize, EncodedType.list]

theorem edgeList_inputSize_nil :
    edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
  rfl

theorem complementEdgeInstruction_candidate_inputSize_le
    (initEdges : List (Nat × Nat)) (candidate : Nat × Nat) :
    edgeStructuredEncodedType.inputSize candidate ≤
      complementEdgeInstructionEncodedType.inputSize (true, (initEdges, candidate)) := by
  simp [complementEdgeInstructionEncodedType, complementEdgeInstructionPayloadEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_bool]
  omega

theorem complementEdgeRunnerStep_output_growth
    (acc : List (Nat × Nat) × List (Nat × Nat))
    (instr : Bool × (List (Nat × Nat) × (Nat × Nat))) :
    edgeListStructuredEncodedType.inputSize (complementEdgeRunnerStep (acc, instr)).2 ≤
      edgeListStructuredEncodedType.inputSize acc.2 +
        complementEdgeInstructionEncodedType.inputSize instr + 1 := by
  rcases acc with ⟨sourceEdges, outEdges⟩
  rcases instr with ⟨tag, payload⟩
  rcases payload with ⟨initEdges, candidate⟩
  cases tag
  · change edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) ≤
      edgeListStructuredEncodedType.inputSize outEdges +
        complementEdgeInstructionEncodedType.inputSize (false, (initEdges, candidate)) + 1
    rw [show edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 by
      exact edgeList_inputSize_nil]
    exact Nat.zero_le _
  · by_cases hNonedge : sourceNonedgeBool (candidate, sourceEdges) = true
    · have hAppend :
          edgeListStructuredEncodedType.inputSize (outEdges ++ [candidate]) =
            edgeListStructuredEncodedType.inputSize outEdges +
              edgeListStructuredEncodedType.inputSize [candidate] := by
        simpa [edgeListStructuredEncodedType] using
          list_inputSize_append edgeStructuredEncodedType outEdges [candidate]
      have hSingleton := edgeList_inputSize_singleton candidate
      have hCandidateLe :
          edgeStructuredEncodedType.inputSize candidate ≤
            complementEdgeInstructionEncodedType.inputSize (true, (initEdges, candidate)) := by
        exact complementEdgeInstruction_candidate_inputSize_le initEdges candidate
      calc
        edgeListStructuredEncodedType.inputSize (complementEdgeRunnerStep
            ((sourceEdges, outEdges), (true, (initEdges, candidate)))).2
            =
          edgeListStructuredEncodedType.inputSize (outEdges ++ [candidate]) := by
            simp [complementEdgeRunnerStep, hNonedge]
        _ = edgeListStructuredEncodedType.inputSize outEdges +
              edgeListStructuredEncodedType.inputSize [candidate] := hAppend
        _ = edgeListStructuredEncodedType.inputSize outEdges +
              (edgeStructuredEncodedType.inputSize candidate + 1) := by
            rw [hSingleton]
        _ ≤ edgeListStructuredEncodedType.inputSize outEdges +
              (complementEdgeInstructionEncodedType.inputSize (true, (initEdges, candidate)) + 1) := by
            exact Nat.add_le_add_left (Nat.add_le_add_right hCandidateLe 1)
              (edgeListStructuredEncodedType.inputSize outEdges)
        _ = edgeListStructuredEncodedType.inputSize outEdges +
              complementEdgeInstructionEncodedType.inputSize (true, (initEdges, candidate)) + 1 := by
            omega
    · have hFalse : sourceNonedgeBool (candidate, sourceEdges) = false := by
        cases h : sourceNonedgeBool (candidate, sourceEdges)
        · rfl
        · exact False.elim (hNonedge h)
      simp [complementEdgeRunnerStep, hFalse]
      omega

theorem complementEdgesFromInstructions_inputSize_le
    (xs : complementEdgeInstructionListEncodedType.Carrier) :
    edgeListStructuredEncodedType.inputSize (complementEdgesFromInstructions xs) ≤
      complementEdgeInstructionListEncodedType.inputSize xs := by
  change edgeListStructuredEncodedType.inputSize
      ((xs.foldl (fun acc x => complementEdgeRunnerStep (acc, x)) complementEdgeRunnerInit).2) ≤
    complementEdgeInstructionListEncodedType.inputSize xs
  have hAux :
      ∀ (rest : List (Bool × (List (Nat × Nat) × (Nat × Nat))))
        (acc : List (Nat × Nat) × List (Nat × Nat)),
        edgeListStructuredEncodedType.inputSize
            ((rest.foldl (fun acc x => complementEdgeRunnerStep (acc, x)) acc).2) ≤
          edgeListStructuredEncodedType.inputSize acc.2 +
            complementEdgeInstructionListEncodedType.inputSize rest := by
    intro rest
    induction rest with
    | nil =>
        intro acc
        simp
    | cons x xs ih =>
        intro acc
        have hStep := complementEdgeRunnerStep_output_growth acc x
        have hTail := ih (complementEdgeRunnerStep (acc, x))
        calc
          edgeListStructuredEncodedType.inputSize
              (((x :: xs).foldl (fun acc x => complementEdgeRunnerStep (acc, x)) acc).2)
              =
            edgeListStructuredEncodedType.inputSize
              ((xs.foldl (fun acc x => complementEdgeRunnerStep (acc, x))
                (complementEdgeRunnerStep (acc, x))).2) := by
                rfl
          _ ≤ edgeListStructuredEncodedType.inputSize (complementEdgeRunnerStep (acc, x)).2 +
                complementEdgeInstructionListEncodedType.inputSize xs := hTail
          _ ≤ edgeListStructuredEncodedType.inputSize acc.2 +
                complementEdgeInstructionEncodedType.inputSize x + 1 +
                complementEdgeInstructionListEncodedType.inputSize xs := by
                omega
          _ = edgeListStructuredEncodedType.inputSize acc.2 +
                complementEdgeInstructionListEncodedType.inputSize (x :: xs) := by
                simp [complementEdgeInstructionListEncodedType, EncodedType.inputSize,
                  EncodedType.list, Nat.add_assoc]
                omega
  have h := hAux xs complementEdgeRunnerInit
  have hEmpty :
      edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
    exact edgeList_inputSize_nil
  simpa [complementEdgeRunnerInit, hEmpty] using h

theorem complementEdgesFromInstructions_polynomialSizeBound :
    PolynomialSizeBound
      (fun xs : complementEdgeInstructionListEncodedType.Carrier =>
        complementEdgeInstructionListEncodedType.inputSize xs)
      (fun ys : edgeListStructuredEncodedType.Carrier =>
        edgeListStructuredEncodedType.inputSize ys)
      complementEdgesFromInstructions :=
  PolynomialSizeBound.intro_with 1 1 0 (by
    intro xs
    simpa using complementEdgesFromInstructions_inputSize_le xs)

/-! ### TM-backed maps -/

theorem complementEdgeInitInstruction_tm_polytime :
    TMPolyTimeMap
      edgeListStructuredEncodedType
      complementEdgeInstructionEncodedType
      complementEdgeInitInstruction := by
  have hTag : TMPolyTimeMap edgeListStructuredEncodedType EncodedType.bool (fun _ => false) :=
    TMPolyTimeMap.const edgeListStructuredEncodedType EncodedType.bool false
  have hSource : TMPolyTimeMap edgeListStructuredEncodedType edgeListStructuredEncodedType id :=
    TMPolyTimeMap.id edgeListStructuredEncodedType
  have hDefault :
      TMPolyTimeMap edgeListStructuredEncodedType edgeStructuredEncodedType
        (fun _ => edgeScanDefaultPair) :=
    TMPolyTimeMap.const edgeListStructuredEncodedType edgeStructuredEncodedType edgeScanDefaultPair
  have hPayload :
      TMPolyTimeMap edgeListStructuredEncodedType complementEdgeInstructionPayloadEncodedType
        (fun sourceEdges : List (Nat × Nat) => (sourceEdges, edgeScanDefaultPair)) :=
    TMPolyTimeMap.prod_mk hSource hDefault
  have hOut := TMPolyTimeMap.prod_mk hTag hPayload
  simpa [complementEdgeInitInstruction, complementEdgeInstructionEncodedType,
    complementEdgeInstructionPayloadEncodedType] using hOut

theorem complementEdgeCandidateInstruction_tm_polytime :
    TMPolyTimeMap
      edgeStructuredEncodedType
      complementEdgeInstructionEncodedType
      complementEdgeCandidateInstruction := by
  have hTag : TMPolyTimeMap edgeStructuredEncodedType EncodedType.bool (fun _ => true) :=
    TMPolyTimeMap.const edgeStructuredEncodedType EncodedType.bool true
  have hEmpty :
      TMPolyTimeMap edgeStructuredEncodedType edgeListStructuredEncodedType
        (fun _ => ([] : List (Nat × Nat))) :=
    TMPolyTimeMap.const edgeStructuredEncodedType edgeListStructuredEncodedType []
  have hCandidate : TMPolyTimeMap edgeStructuredEncodedType edgeStructuredEncodedType id :=
    TMPolyTimeMap.id edgeStructuredEncodedType
  have hPayload :
      TMPolyTimeMap edgeStructuredEncodedType complementEdgeInstructionPayloadEncodedType
        (fun candidate : Nat × Nat => (([] : List (Nat × Nat)), candidate)) :=
    TMPolyTimeMap.prod_mk hEmpty hCandidate
  have hOut := TMPolyTimeMap.prod_mk hTag hPayload
  simpa [complementEdgeCandidateInstruction, complementEdgeInstructionEncodedType,
    complementEdgeInstructionPayloadEncodedType] using hOut

theorem complementEdgeInstructions_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod edgeListStructuredEncodedType vertexPairListEncodedType)
      complementEdgeInstructionListEncodedType
      complementEdgeInstructions := by
  let X := EncodedType.prod edgeListStructuredEncodedType vertexPairListEncodedType
  have hSource : TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst edgeListStructuredEncodedType vertexPairListEncodedType
  have hCandidates :
      TMPolyTimeMap X vertexPairListEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd edgeListStructuredEncodedType vertexPairListEncodedType
  have hInit :
      TMPolyTimeMap X complementEdgeInstructionEncodedType
        (fun p : X.Carrier => complementEdgeInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp complementEdgeInitInstruction_tm_polytime hSource
    simpa [Function.comp, X] using hComp
  have hCandidateInstructions :
      TMPolyTimeMap X complementEdgeInstructionListEncodedType
        (fun p : X.Carrier => p.2.map complementEdgeCandidateInstruction) := by
    have hMap := TMPolyTimeMap.list_map complementEdgeCandidateInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hCandidates
    simpa [Function.comp, vertexPairListEncodedType, complementEdgeInstructionListEncodedType, X]
      using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod complementEdgeInstructionEncodedType complementEdgeInstructionListEncodedType)
        (fun p : X.Carrier =>
          (complementEdgeInitInstruction p.1,
            p.2.map complementEdgeCandidateInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hCandidateInstructions
  have hOut :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons complementEdgeInstructionEncodedType) hConsInput
  simpa [Function.comp, complementEdgeInstructions, complementEdgeInstructionListEncodedType, X]
    using hOut

theorem complementEdgeRunnerStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod complementEdgeAccEncodedType complementEdgeInstructionEncodedType)
      complementEdgeAccEncodedType
      complementEdgeRunnerStep := by
  let X := EncodedType.prod complementEdgeAccEncodedType complementEdgeInstructionEncodedType
  have hAcc : TMPolyTimeMap X complementEdgeAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst complementEdgeAccEncodedType complementEdgeInstructionEncodedType
  have hInstr :
      TMPolyTimeMap X complementEdgeInstructionEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd complementEdgeAccEncodedType complementEdgeInstructionEncodedType
  have hSource : TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, complementEdgeAccEncodedType, X] using hComp
  have hOutEdges : TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd edgeListStructuredEncodedType edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, complementEdgeAccEncodedType, X] using hComp
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool complementEdgeInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, complementEdgeInstructionEncodedType, X] using hComp
  have hPayload :
      TMPolyTimeMap X complementEdgeInstructionPayloadEncodedType (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool complementEdgeInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, complementEdgeInstructionEncodedType, X] using hComp
  have hInitSource :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType edgeStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, complementEdgeInstructionPayloadEncodedType, X] using hComp
  have hCandidate :
      TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd edgeListStructuredEncodedType edgeStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, complementEdgeInstructionPayloadEncodedType, X] using hComp
  have hEmpty : TMPolyTimeMap X edgeListStructuredEncodedType (fun _ => ([] : List (Nat × Nat))) :=
    TMPolyTimeMap.const X edgeListStructuredEncodedType []
  have hInitOut :
      TMPolyTimeMap X complementEdgeAccEncodedType
        (fun p : X.Carrier => (p.2.2.1, ([] : List (Nat × Nat)))) :=
    TMPolyTimeMap.prod_mk hInitSource hEmpty
  have hScanInput :
      TMPolyTimeMap X (EncodedType.prod vertexPairEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier => (p.2.2.2, p.1.1)) :=
    TMPolyTimeMap.prod_mk hCandidate hSource
  have hNonedge :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => sourceNonedgeBool (p.2.2.2, p.1.1)) := by
    have hComp := TMPolyTimeMap.comp sourceNonedgeBool_tm_polytime hScanInput
    simpa [Function.comp, X] using hComp
  have hCandidateSingleton :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier => [p.2.2.2]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton edgeStructuredEncodedType)
      hCandidate
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier => (p.1.2, [p.2.2.2])) :=
    TMPolyTimeMap.prod_mk hOutEdges hCandidateSingleton
  have hAppend :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier =>
          let outEdges : List (Nat × Nat) := p.1.2
          let candidate : Nat × Nat := p.2.2.2
          outEdges ++ [candidate]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append edgeStructuredEncodedType)
      hAppendInput
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hKeepOut :
      TMPolyTimeMap X complementEdgeAccEncodedType
        (fun p : X.Carrier => (p.1.1, p.1.2)) :=
    TMPolyTimeMap.prod_mk hSource hOutEdges
  have hAppendOut :
      TMPolyTimeMap X complementEdgeAccEncodedType
        (fun p : X.Carrier =>
          let sourceEdges : List (Nat × Nat) := p.1.1
          let outEdges : List (Nat × Nat) := p.1.2
          let candidate : Nat × Nat := p.2.2.2
          (sourceEdges, outEdges ++ [candidate])) :=
    TMPolyTimeMap.prod_mk hSource hAppend
  have hInnerBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (sourceNonedgeBool (p.2.2.2, p.1.1), p)) :=
    TMPolyTimeMap.prod_mk hNonedge (TMPolyTimeMap.id X)
  have hInnerBranch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool X)
        complementEdgeAccEncodedType
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true =>
              let sourceEdges : List (Nat × Nat) := p.2.1.1
              let outEdges : List (Nat × Nat) := p.2.1.2
              let candidate : Nat × Nat := p.2.2.2.2
              (sourceEdges, outEdges ++ [candidate])
          | false => (p.2.1.1, p.2.1.2)) :=
    graphBoolProduct_dispatch_tm_polytime X complementEdgeAccEncodedType
      (fFalse := fun p : X.Carrier => (p.1.1, p.1.2))
      (fTrue := fun p : X.Carrier =>
        let sourceEdges : List (Nat × Nat) := p.1.1
        let outEdges : List (Nat × Nat) := p.1.2
        let candidate : Nat × Nat := p.2.2.2
        (sourceEdges, outEdges ++ [candidate]))
      (hFalse := hKeepOut) (hTrue := hAppendOut)
  have hScanOut :
      TMPolyTimeMap X complementEdgeAccEncodedType
        (fun p : X.Carrier =>
          match sourceNonedgeBool (p.2.2.2, p.1.1) with
          | true =>
              let sourceEdges : List (Nat × Nat) := p.1.1
              let outEdges : List (Nat × Nat) := p.1.2
              let candidate : Nat × Nat := p.2.2.2
              (sourceEdges, outEdges ++ [candidate])
          | false => (p.1.1, p.1.2)) := by
    have hComp := TMPolyTimeMap.comp hInnerBranch hInnerBranchInput
    simpa [Function.comp] using hComp
  have hOuterBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hOuterBranch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool X)
        complementEdgeAccEncodedType
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true =>
              (match sourceNonedgeBool (p.2.2.2.2, p.2.1.1) with
              | true =>
                  let sourceEdges : List (Nat × Nat) := p.2.1.1
                  let outEdges : List (Nat × Nat) := p.2.1.2
                  let candidate : Nat × Nat := p.2.2.2.2
                  (sourceEdges, outEdges ++ [candidate])
              | false => (p.2.1.1, p.2.1.2))
          | false => (p.2.2.2.1, ([] : List (Nat × Nat)))) :=
    graphBoolProduct_dispatch_tm_polytime X complementEdgeAccEncodedType
      (fFalse := fun p : X.Carrier => (p.2.2.1, ([] : List (Nat × Nat))))
      (fTrue := fun p : X.Carrier =>
        match sourceNonedgeBool (p.2.2.2, p.1.1) with
        | true =>
            let sourceEdges : List (Nat × Nat) := p.1.1
            let outEdges : List (Nat × Nat) := p.1.2
            let candidate : Nat × Nat := p.2.2.2
            (sourceEdges, outEdges ++ [candidate])
        | false => (p.1.1, p.1.2))
      (hFalse := hInitOut) (hTrue := hScanOut)
  have hOut := TMPolyTimeMap.comp hOuterBranch hOuterBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨acc, instr⟩
  rcases acc with ⟨sourceEdges, outEdges⟩
  rcases instr with ⟨tag, payload⟩
  rcases payload with ⟨initEdges, candidate⟩
  cases tag
  · rfl
  · cases h : sourceNonedgeBool (candidate, sourceEdges) <;> rfl

theorem complementEdgeRunnerStep_growth
    (source : complementEdgeInstructionListEncodedType.Carrier)
    (acc : List (Nat × Nat) × List (Nat × Nat))
    (instr : Bool × (List (Nat × Nat) × (Nat × Nat)))
    (hInstr :
      complementEdgeInstructionEncodedType.inputSize instr ≤
        complementEdgeInstructionListEncodedType.inputSize source) :
    complementEdgeAccEncodedType.inputSize (complementEdgeRunnerStep (acc, instr)) ≤
      complementEdgeAccEncodedType.inputSize acc +
        (complementEdgeInstructionListEncodedType.inputSize source + 20) := by
  have hOut := complementEdgeRunnerStep_output_growth acc instr
  rcases acc with ⟨sourceEdges, outEdges⟩
  rcases instr with ⟨tag, payload⟩
  rcases payload with ⟨initEdges, candidate⟩
  cases tag
  · simp [complementEdgeRunnerStep, complementEdgeAccEncodedType,
      complementEdgeInstructionEncodedType, complementEdgeInstructionPayloadEncodedType,
      edgeListStructuredEncodedType, edgeStructuredEncodedType, EncodedType.inputSize,
      EncodedType.prod, EncodedType.list, EncodedType.bool, EncodedType.nat] at hInstr ⊢
    omega
  · by_cases hNonedge : sourceNonedgeBool (candidate, sourceEdges) = true
    · simp [complementEdgeRunnerStep, hNonedge, complementEdgeAccEncodedType,
        edgeListStructuredEncodedType, EncodedType.inputSize, EncodedType.prod,
        EncodedType.list] at hOut hInstr ⊢
      omega
    · have hFalse : sourceNonedgeBool (candidate, sourceEdges) = false := by
        cases h : sourceNonedgeBool (candidate, sourceEdges)
        · rfl
        · exact False.elim (hNonedge h)
      simp [complementEdgeRunnerStep, hFalse, complementEdgeAccEncodedType,
        edgeListStructuredEncodedType, EncodedType.inputSize, EncodedType.prod,
        EncodedType.list] at hOut hInstr ⊢

theorem complementEdgesFromInstructions_tm_polytime :
    TMPolyTimeMap
      complementEdgeInstructionListEncodedType
      edgeListStructuredEncodedType
      complementEdgesFromInstructions := by
  rcases complementEdgeRunnerStep_tm_polytime with ⟨hStep⟩
  let base : Polynomial Nat := Polynomial.C 10
  let grow : Polynomial Nat := Polynomial.X + Polynomial.C 20
  have hFold :
      TMPolyTimeMap
        complementEdgeInstructionListEncodedType
        complementEdgeAccEncodedType
        (fun xs : complementEdgeInstructionListEncodedType.Carrier =>
          xs.foldl (fun acc x => complementEdgeRunnerStep (acc, x)) complementEdgeRunnerInit) := by
    refine
      TMPolyTimeMap.list_foldl_typed_growth_bounded
        complementEdgeInstructionEncodedType complementEdgeAccEncodedType
        complementEdgeRunnerStep complementEdgeRunnerInit hStep base grow ?_ ?_
    · intro xs
      have hInitSize : complementEdgeAccEncodedType.inputSize complementEdgeRunnerInit = 1 := by
        simp [complementEdgeRunnerInit, complementEdgeAccEncodedType,
          EncodedType.inputSize_prod, edgeList_inputSize_nil]
      rw [hInitSize]
      simp [base]
    · intro source acc instr hInstr
      have hInstr' :
          complementEdgeInstructionEncodedType.inputSize instr ≤
            complementEdgeInstructionListEncodedType.inputSize source := by
        simpa [complementEdgeInstructionListEncodedType] using hInstr
      have h :=
        complementEdgeRunnerStep_growth source acc instr hInstr'
      simpa [complementEdgeInstructionListEncodedType, grow, Polynomial.eval_add] using h
  have hOut := TMPolyTimeMap.snd edgeListStructuredEncodedType edgeListStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hOut hFold
  simpa [Function.comp, complementEdgesFromInstructions, complementEdgeAccEncodedType] using hComp

noncomputable def complementEdgesFromInstructionsTMBackedMap :
    TMBackedCostedMap
      complementEdgeInstructionListEncodedType
      edgeListStructuredEncodedType
      complementEdgesFromInstructions where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      complementEdgesFromInstructions_polynomialSizeBound
  tm_polytime := complementEdgesFromInstructions_tm_polytime

theorem complementEdgesFromCandidates_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod edgeListStructuredEncodedType vertexPairListEncodedType)
      edgeListStructuredEncodedType
      complementEdgesFromCandidates := by
  have hComp :=
    TMPolyTimeMap.comp complementEdgesFromInstructions_tm_polytime
      complementEdgeInstructions_tm_polytime
  simpa [Function.comp, complementEdgesFromCandidates] using hComp

end Karp21
end ComplexityReduction
