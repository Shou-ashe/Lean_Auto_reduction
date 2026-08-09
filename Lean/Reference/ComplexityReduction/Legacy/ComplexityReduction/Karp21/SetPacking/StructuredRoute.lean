/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SetPacking.Base
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.ComplementEdges
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.Projections

/-!
P16c faithful structured Clique-to-Set-Packing route.

The P15i semantic route used paired natural-number codes.  For direct TM-backed
structured output, this module assigns conflict codes by a unary counter over
the already checked complement-edge list.  This avoids depending on a separate
`Nat.pair` writer for unary naturals.
-/

namespace ComplexityReduction
namespace Karp21
namespace SetPacking

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-- A coded complement edge: the generated universe code and the source edge. -/
def codedComplementEdgeEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat vertexPairEncodedType

/-- Structured list encoding for coded complement edges. -/
def codedComplementEdgeListEncodedType : EncodedType :=
  EncodedType.list codedComplementEdgeEncodedType

/-- Accumulator for assigning fresh conflict codes to complement edges. -/
def codeComplementEdgesAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat codedComplementEdgeListEncodedType

/-- Concrete carrier for a coded complement edge. -/
abbrev CodedComplementEdge := Nat × (Nat × Nat)

/-- Concrete carrier for the conflict-code fold accumulator. -/
abbrev CodeComplementEdgesAcc := Nat × List CodedComplementEdge

/-- Assign the current code to one complement edge and advance the counter. -/
def codeComplementEdgeOutput (p : CodeComplementEdgesAcc × (Nat × Nat)) :
    List CodedComplementEdge :=
  p.1.2 ++ [(p.1.1, p.2)]

/-- Assign the current code to one complement edge and advance the counter. -/
def codeComplementEdgeStep
    (p : CodeComplementEdgesAcc × (Nat × Nat)) : CodeComplementEdgesAcc :=
  let nextCode := p.1.1
  (Nat.succ nextCode, codeComplementEdgeOutput p)

/-- Run the conflict-code assignment fold from a supplied initial code. -/
def codeComplementEdgesFrom (start : Nat) (edges : List (Nat × Nat)) :
    CodeComplementEdgesAcc :=
  edges.foldl (fun acc edge => codeComplementEdgeStep (acc, edge)) (start, [])

/-- Payload for initializing the code runner or processing one edge. -/
def codeComplementEdgeInstructionPayloadEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat edgeStructuredEncodedType

/-- Tagged instruction for the code runner.  `false` initializes; `true` scans an edge. -/
def codeComplementEdgeInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool codeComplementEdgeInstructionPayloadEncodedType

/-- Structured instruction-list encoding for the code runner. -/
def codeComplementEdgeInstructionListEncodedType : EncodedType :=
  EncodedType.list codeComplementEdgeInstructionEncodedType

/-- Dynamic input used to build the code-runner instruction stream. -/
def codeComplementEdgeInstructionInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat edgeListStructuredEncodedType

/-- Input encoding for one code-runner step. -/
def codeComplementEdgeScanInputEncodedType : EncodedType :=
  EncodedType.prod codeComplementEdgesAccEncodedType codeComplementEdgeInstructionEncodedType

def codeComplementEdgeInitInstruction (start : Nat) : Bool × (Nat × (Nat × Nat)) :=
  (false, (start, edgeScanDefaultPair))

def codeComplementEdgeEdgeInstruction (edge : Nat × Nat) : Bool × (Nat × (Nat × Nat)) :=
  (true, (0, edge))

def codeComplementEdgeInstructions (p : Nat × List (Nat × Nat)) :
    List (Bool × (Nat × (Nat × Nat))) :=
  codeComplementEdgeInitInstruction p.1 :: p.2.map codeComplementEdgeEdgeInstruction

def codeComplementEdgeScanInit : CodeComplementEdgesAcc :=
  (0, [])

def codeComplementEdgeScanStep
    (p : CodeComplementEdgesAcc × (Bool × (Nat × (Nat × Nat)))) :
    CodeComplementEdgesAcc :=
  if p.2.1 then
    codeComplementEdgeStep (p.1, p.2.2.2)
  else
    (p.2.2.1, [])

def codeComplementEdgesFromInstructions
    (xs : List (Bool × (Nat × (Nat × Nat)))) : CodeComplementEdgesAcc :=
  xs.foldl (fun acc instr => codeComplementEdgeScanStep (acc, instr))
    codeComplementEdgeScanInit

def codeComplementEdgesFromInput (p : Nat × List (Nat × Nat)) : CodeComplementEdgesAcc :=
  codeComplementEdgesFromInstructions (codeComplementEdgeInstructions p)

/-! ### Code-runner semantics -/

theorem codeComplementEdgeInstructions_fold_eq
    (edges : List (Nat × Nat)) (next : Nat) (out : List CodedComplementEdge) :
    (edges.map codeComplementEdgeEdgeInstruction).foldl
        (fun acc instr => codeComplementEdgeScanStep (acc, instr)) (next, out) =
      edges.foldl (fun acc edge => codeComplementEdgeStep (acc, edge)) (next, out) := by
  induction edges generalizing next out with
  | nil =>
      simp
  | cons edge edges ih =>
      simpa [codeComplementEdgeEdgeInstruction, codeComplementEdgeScanStep] using
        ih (codeComplementEdgeStep ((next, out), edge)).1
          (codeComplementEdgeStep ((next, out), edge)).2

theorem codeComplementEdgesFromInput_eq (start : Nat) (edges : List (Nat × Nat)) :
    codeComplementEdgesFromInput (start, edges) = codeComplementEdgesFrom start edges := by
  simpa [codeComplementEdgesFromInput, codeComplementEdgesFromInstructions,
    codeComplementEdgeInstructions, codeComplementEdgeInitInstruction,
    codeComplementEdgeScanStep, codeComplementEdgesFrom] using
    codeComplementEdgeInstructions_fold_eq edges start ([] : List CodedComplementEdge)

theorem codeComplementEdgesFrom_fst_aux
    (edges : List (Nat × Nat)) (next : Nat) (out : List CodedComplementEdge) :
    (edges.foldl (fun acc edge => codeComplementEdgeStep (acc, edge)) (next, out)).1 =
      next + edges.length := by
  induction edges generalizing next out with
  | nil =>
      simp
  | cons edge edges ih =>
      simpa [codeComplementEdgeStep, codeComplementEdgeOutput, Nat.succ_eq_add_one,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        ih (next + 1) (out ++ [(next, edge)])

theorem codeComplementEdgesFrom_fst (start : Nat) (edges : List (Nat × Nat)) :
    (codeComplementEdgesFrom start edges).1 = start + edges.length := by
  simpa [codeComplementEdgesFrom] using
    codeComplementEdgesFrom_fst_aux edges start ([] : List CodedComplementEdge)

theorem codeComplementEdgesFrom_length_aux
    (edges : List (Nat × Nat)) (next : Nat) (out : List CodedComplementEdge) :
    (edges.foldl (fun acc edge => codeComplementEdgeStep (acc, edge)) (next, out)).2.length =
      out.length + edges.length := by
  induction edges generalizing next out with
  | nil =>
      simp
  | cons edge edges ih =>
      simpa [codeComplementEdgeStep, codeComplementEdgeOutput, Nat.succ_eq_add_one,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        ih (next + 1) (out ++ [(next, edge)])

theorem codeComplementEdgesFrom_length (start : Nat) (edges : List (Nat × Nat)) :
    (codeComplementEdgesFrom start edges).2.length = edges.length := by
  simpa [codeComplementEdgesFrom] using
    codeComplementEdgesFrom_length_aux edges start ([] : List CodedComplementEdge)

def codeComplementEdgesSpec : Nat → List (Nat × Nat) → List CodedComplementEdge
  | _start, [] => []
  | start, edge :: edges => (start, edge) :: codeComplementEdgesSpec (start + 1) edges

theorem codeComplementEdgesFrom_aux_eq_spec
    (edges : List (Nat × Nat)) (next : Nat) (out : List CodedComplementEdge) :
    edges.foldl (fun acc edge => codeComplementEdgeStep (acc, edge)) (next, out) =
      (next + edges.length, out ++ codeComplementEdgesSpec next edges) := by
  induction edges generalizing next out with
  | nil =>
      simp [codeComplementEdgesSpec]
  | cons edge edges ih =>
      simpa [codeComplementEdgeStep, codeComplementEdgeOutput, codeComplementEdgesSpec,
        Nat.succ_eq_add_one, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using ih (next + 1) (out ++ [(next, edge)])

theorem codeComplementEdgesFrom_spec (start : Nat) (edges : List (Nat × Nat)) :
    (codeComplementEdgesFrom start edges).2 = codeComplementEdgesSpec start edges := by
  have h :=
    codeComplementEdgesFrom_aux_eq_spec edges start ([] : List CodedComplementEdge)
  simpa [codeComplementEdgesFrom] using congrArg Prod.snd h

theorem codeComplementEdgesSpec_mem_edge
    {start : Nat} {edges : List (Nat × Nat)} {ce : CodedComplementEdge}
    (h : ce ∈ codeComplementEdgesSpec start edges) :
    ce.2 ∈ edges := by
  induction edges generalizing start with
  | nil =>
      simp [codeComplementEdgesSpec] at h
  | cons edge edges ih =>
      simp [codeComplementEdgesSpec] at h
      rcases h with hHead | hTail
      · subst ce
        simp
      · right
        exact ih hTail

theorem codeComplementEdgesSpec_mem_code_ge
    {start : Nat} {edges : List (Nat × Nat)} {ce : CodedComplementEdge}
    (h : ce ∈ codeComplementEdgesSpec start edges) :
    start ≤ ce.1 := by
  induction edges generalizing start with
  | nil =>
      simp [codeComplementEdgesSpec] at h
  | cons edge edges ih =>
      simp [codeComplementEdgesSpec] at h
      rcases h with hHead | hTail
      · simp [hHead]
      · have hGe := ih hTail
        omega

theorem codeComplementEdgesSpec_mem_code_lt
    {start : Nat} {edges : List (Nat × Nat)} {ce : CodedComplementEdge}
    (h : ce ∈ codeComplementEdgesSpec start edges) :
    ce.1 < start + edges.length := by
  induction edges generalizing start with
  | nil =>
      simp [codeComplementEdgesSpec] at h
  | cons edge edges ih =>
      simp [codeComplementEdgesSpec] at h
      rcases h with hHead | hTail
      · simp [hHead]
      · have hLt := ih hTail
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hLt

theorem codeComplementEdgesSpec_code_unique
    {start : Nat} {edges : List (Nat × Nat)} {code : Nat} {e₁ e₂ : Nat × Nat}
    (h₁ : (code, e₁) ∈ codeComplementEdgesSpec start edges)
    (h₂ : (code, e₂) ∈ codeComplementEdgesSpec start edges) :
    e₁ = e₂ := by
  induction edges generalizing start with
  | nil =>
      simp [codeComplementEdgesSpec] at h₁
  | cons edge edges ih =>
      simp [codeComplementEdgesSpec] at h₁ h₂
      rcases h₁ with h₁Head | h₁Tail <;> rcases h₂ with h₂Head | h₂Tail
      · exact h₁Head.2.trans h₂Head.2.symm
      · have hCode : code = start := h₁Head.1
        subst code
        have hGe := codeComplementEdgesSpec_mem_code_ge h₂Tail
        omega
      · have hCode : code = start := h₂Head.1
        subst code
        have hGe := codeComplementEdgesSpec_mem_code_ge h₁Tail
        omega
      · exact ih h₁Tail h₂Tail

theorem exists_mem_codeComplementEdgesSpec_of_mem
    {start : Nat} {edges : List (Nat × Nat)} {edge : Nat × Nat}
    (h : edge ∈ edges) :
    ∃ code, (code, edge) ∈ codeComplementEdgesSpec start edges := by
  induction edges generalizing start with
  | nil =>
      simp at h
  | cons edge' edges ih =>
      simp at h
      rcases h with hHead | hTail
      · subst edge'
        exact ⟨start, by simp [codeComplementEdgesSpec]⟩
      · rcases ih (start := start + 1) hTail with ⟨code, hCode⟩
        exact ⟨code, by simp [codeComplementEdgesSpec, hCode]⟩

theorem codeComplementEdgesFrom_mem_edge
    {start : Nat} {edges : List (Nat × Nat)} {ce : CodedComplementEdge}
    (h : ce ∈ (codeComplementEdgesFrom start edges).2) :
    ce.2 ∈ edges := by
  rw [codeComplementEdgesFrom_spec] at h
  exact codeComplementEdgesSpec_mem_edge h

theorem codeComplementEdgesFrom_mem_code_ge
    {start : Nat} {edges : List (Nat × Nat)} {ce : CodedComplementEdge}
    (h : ce ∈ (codeComplementEdgesFrom start edges).2) :
    start ≤ ce.1 := by
  rw [codeComplementEdgesFrom_spec] at h
  exact codeComplementEdgesSpec_mem_code_ge h

theorem codeComplementEdgesFrom_mem_code_lt
    {start : Nat} {edges : List (Nat × Nat)} {ce : CodedComplementEdge}
    (h : ce ∈ (codeComplementEdgesFrom start edges).2) :
    ce.1 < start + edges.length := by
  rw [codeComplementEdgesFrom_spec] at h
  exact codeComplementEdgesSpec_mem_code_lt h

theorem codeComplementEdgesFrom_code_unique
    {start : Nat} {edges : List (Nat × Nat)} {code : Nat} {e₁ e₂ : Nat × Nat}
    (h₁ : (code, e₁) ∈ (codeComplementEdgesFrom start edges).2)
    (h₂ : (code, e₂) ∈ (codeComplementEdgesFrom start edges).2) :
    e₁ = e₂ := by
  rw [codeComplementEdgesFrom_spec] at h₁ h₂
  exact codeComplementEdgesSpec_code_unique h₁ h₂

theorem exists_mem_codeComplementEdgesFrom_of_mem
    {start : Nat} {edges : List (Nat × Nat)} {edge : Nat × Nat}
    (h : edge ∈ edges) :
    ∃ code, (code, edge) ∈ (codeComplementEdgesFrom start edges).2 := by
  rw [codeComplementEdgesFrom_spec]
  exact exists_mem_codeComplementEdgesSpec_of_mem h

/-! ### Compact Set-Packing semantics from coded complement edges -/

def codedEdgeIncidentBool (p : Nat × CodedComplementEdge) : Bool :=
  graphBoolOrPair (decide (p.2.2.1 = p.1), decide (p.2.2.2 = p.1))

theorem codedEdgeIncidentBool_eq_true_iff (p : Nat × CodedComplementEdge) :
    codedEdgeIncidentBool p = true ↔ p.2.2.1 = p.1 ∨ p.2.2.2 = p.1 := by
  rw [codedEdgeIncidentBool, graphBoolOrPair_eq_true_iff]
  simp

def compactIncidentCodes (v : Nat) (codedEdges : List CodedComplementEdge) : List Nat :=
  codedEdges.foldl
    (fun out ce => if codedEdgeIncidentBool (v, ce) then out ++ [ce.1] else out) []

def compactPackingSetFromCodes (v : Nat) (codedEdges : List CodedComplementEdge) : List Nat :=
  v :: compactIncidentCodes v codedEdges

def compactSetFamilyFromCodes
    (n : Nat) (codedEdges : List CodedComplementEdge) : List (List Nat) :=
  (List.range n).map (fun v => compactPackingSetFromCodes v codedEdges)

def compactSetSystemFromCodes
    (n : Nat) (codedEdges : List CodedComplementEdge) : SetSystemInput where
  universeSize := n + codedEdges.length
  sets := compactSetFamilyFromCodes n codedEdges

def compactSetSystemFromAcc (n : Nat) (acc : CodeComplementEdgesAcc) : SetSystemInput where
  universeSize := acc.1
  sets := compactSetFamilyFromCodes n acc.2

def compactCodedComplementEdges (I : CliqueInput) : List CodedComplementEdge :=
  (codeComplementEdgesFrom I.graph.vertices (structuredComplementEdges I.graph)).2

def compactMap (I : CliqueInput) : SetPackingInput :=
  let acc := codeComplementEdgesFrom I.graph.vertices (structuredComplementEdges I.graph)
  { system := compactSetSystemFromAcc I.graph.vertices acc
    k := I.k }

theorem mem_compactIncidentCodesFold_iff
    (codedEdges : List CodedComplementEdge) (v : Nat) (out : List Nat) (x : Nat) :
    x ∈ codedEdges.foldl
        (fun out ce => if codedEdgeIncidentBool (v, ce) then out ++ [ce.1] else out) out ↔
      x ∈ out ∨ ∃ ce ∈ codedEdges, ce.1 = x ∧ (ce.2.1 = v ∨ ce.2.2 = v) := by
  induction codedEdges generalizing out with
  | nil =>
      simp
  | cons ce rest ih =>
      by_cases hIncident : codedEdgeIncidentBool (v, ce) = true
      · rw [show
          (ce :: rest).foldl
              (fun out ce => if codedEdgeIncidentBool (v, ce) then out ++ [ce.1] else out)
              out =
            rest.foldl
              (fun out ce => if codedEdgeIncidentBool (v, ce) then out ++ [ce.1] else out)
              (out ++ [ce.1]) by
          simp [hIncident]]
        rw [ih (out ++ [ce.1])]
        rw [codedEdgeIncidentBool_eq_true_iff] at hIncident
        constructor
        · intro h
          rcases h with hOut | hRest
          · rcases List.mem_append.mp hOut with hOld | hNew
            · exact Or.inl hOld
            · have hx : x = ce.1 := by simpa using hNew
              exact Or.inr ⟨ce, by simp, hx.symm, hIncident⟩
          · rcases hRest with ⟨ce', hMem, hCode, hInc⟩
            exact Or.inr ⟨ce', by simp [hMem], hCode, hInc⟩
        · intro h
          rcases h with hOut | hRest
          · exact Or.inl (List.mem_append.mpr (Or.inl hOut))
          · rcases hRest with ⟨ce', hMem, hCode, hInc⟩
            simp at hMem
            rcases hMem with hEq | hTail
            · subst ce'
              exact Or.inl (List.mem_append.mpr (Or.inr (by simp [hCode])))
            · exact Or.inr ⟨ce', hTail, hCode, hInc⟩
      · have hFalse : codedEdgeIncidentBool (v, ce) = false := by
          cases h : codedEdgeIncidentBool (v, ce)
          · rfl
          · exact False.elim (hIncident h)
        rw [show
          (ce :: rest).foldl
              (fun out ce => if codedEdgeIncidentBool (v, ce) then out ++ [ce.1] else out)
              out =
            rest.foldl
              (fun out ce => if codedEdgeIncidentBool (v, ce) then out ++ [ce.1] else out)
              out by
          simp [hFalse]]
        rw [ih out]
        rw [codedEdgeIncidentBool_eq_true_iff] at hIncident
        constructor
        · intro h
          rcases h with hOut | hRest
          · exact Or.inl hOut
          · rcases hRest with ⟨ce', hMem, hCode, hInc⟩
            exact Or.inr ⟨ce', by simp [hMem], hCode, hInc⟩
        · intro h
          rcases h with hOut | hRest
          · exact Or.inl hOut
          · rcases hRest with ⟨ce', hMem, hCode, hInc⟩
            simp at hMem
            rcases hMem with hEq | hTail
            · subst ce'
              exact False.elim (hIncident hInc)
            · exact Or.inr ⟨ce', hTail, hCode, hInc⟩

theorem mem_compactIncidentCodes_iff
    (codedEdges : List CodedComplementEdge) (v x : Nat) :
    x ∈ compactIncidentCodes v codedEdges ↔
      ∃ ce ∈ codedEdges, ce.1 = x ∧ (ce.2.1 = v ∨ ce.2.2 = v) := by
  simpa [compactIncidentCodes] using
    mem_compactIncidentCodesFold_iff codedEdges v ([] : List Nat) x

theorem mem_compactPackingSetFromCodes_iff
    (codedEdges : List CodedComplementEdge) (v x : Nat) :
    x ∈ compactPackingSetFromCodes v codedEdges ↔
      x = v ∨ ∃ ce ∈ codedEdges, ce.1 = x ∧ (ce.2.1 = v ∨ ce.2.2 = v) := by
  simp [compactPackingSetFromCodes, mem_compactIncidentCodes_iff]

theorem mem_compactSetFamilyFromCodes_iff
    (n : Nat) (codedEdges : List CodedComplementEdge) (S : List Nat) :
    S ∈ compactSetFamilyFromCodes n codedEdges ↔
      ∃ v, v < n ∧ S = compactPackingSetFromCodes v codedEdges := by
  constructor
  · intro hS
    rcases List.mem_map.mp hS with ⟨v, hv, rfl⟩
    exact ⟨v, by simpa using hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact List.mem_map.mpr ⟨v, by simpa using hv, rfl⟩

theorem compactPackingSetFromCodes_injective_on
    {codedEdges : List CodedComplementEdge} {u v : Nat}
    (h : compactPackingSetFromCodes u codedEdges =
        compactPackingSetFromCodes v codedEdges) :
    u = v := by
  have hHead := congrArg List.head? h
  simpa [compactPackingSetFromCodes] using hHead

noncomputable def compactVertexOfSet
    (n : Nat) (codedEdges : List CodedComplementEdge) (S : List Nat) : Nat := by
  classical
  exact if h : S ∈ compactSetFamilyFromCodes n codedEdges then
    Classical.choose ((mem_compactSetFamilyFromCodes_iff n codedEdges S).1 h)
  else 0

theorem compactVertexOfSet_lt_of_mem
    (n : Nat) (codedEdges : List CodedComplementEdge) {S : List Nat}
    (hS : S ∈ compactSetFamilyFromCodes n codedEdges) :
    compactVertexOfSet n codedEdges S < n := by
  classical
  simp [compactVertexOfSet, hS,
    (Classical.choose_spec ((mem_compactSetFamilyFromCodes_iff n codedEdges S).1 hS)).1]

theorem compactPackingSet_vertexOfSet_of_mem
    (n : Nat) (codedEdges : List CodedComplementEdge) {S : List Nat}
    (hS : S ∈ compactSetFamilyFromCodes n codedEdges) :
    S = compactPackingSetFromCodes
      (compactVertexOfSet n codedEdges S) codedEdges := by
  classical
  unfold compactVertexOfSet
  rw [dif_pos hS]
  exact (Classical.choose_spec ((mem_compactSetFamilyFromCodes_iff n codedEdges S).1 hS)).2

theorem common_compactPackingSet_of_nonedge
    {I : CliqueInput} {u v : Nat}
    (hu : u < I.graph.vertices) (hv : v < I.graph.vertices) (huv : u ≠ v)
    (hNonedge : ¬ HasUndirectedEdge I.graph u v) :
    ∃ x,
      x ∈ compactPackingSetFromCodes u (compactCodedComplementEdges I) ∧
        x ∈ compactPackingSetFromCodes v (compactCodedComplementEdges I) := by
  have hOrder : u < v ∨ v < u := Nat.lt_or_gt_of_ne huv
  rcases hOrder with huvLt | hvuLt
  · have hEdgeMem : (u, v) ∈ structuredComplementEdges I.graph := by
      rw [mem_structuredComplementEdges_iff]
      exact ⟨hu, hv, huvLt, hNonedge⟩
    rcases exists_mem_codeComplementEdgesFrom_of_mem
        (start := I.graph.vertices) hEdgeMem with
      ⟨code, hCode⟩
    refine ⟨code, ?_, ?_⟩
    · rw [mem_compactPackingSetFromCodes_iff]
      exact Or.inr ⟨(code, (u, v)), hCode, rfl, Or.inl rfl⟩
    · rw [mem_compactPackingSetFromCodes_iff]
      exact Or.inr ⟨(code, (u, v)), hCode, rfl, Or.inr rfl⟩
  · have hNonedge' : ¬ HasUndirectedEdge I.graph v u := by
      intro h
      exact hNonedge ((hasUndirectedEdge_comm I.graph u v).2 h)
    have hEdgeMem : (v, u) ∈ structuredComplementEdges I.graph := by
      rw [mem_structuredComplementEdges_iff]
      exact ⟨hv, hu, hvuLt, hNonedge'⟩
    rcases exists_mem_codeComplementEdgesFrom_of_mem
        (start := I.graph.vertices) hEdgeMem with
      ⟨code, hCode⟩
    refine ⟨code, ?_, ?_⟩
    · rw [mem_compactPackingSetFromCodes_iff]
      exact Or.inr ⟨(code, (v, u)), hCode, rfl, Or.inr rfl⟩
    · rw [mem_compactPackingSetFromCodes_iff]
      exact Or.inr ⟨(code, (v, u)), hCode, rfl, Or.inl rfl⟩

theorem no_common_compactPackingSet_of_edge
    {I : CliqueInput} {u v x : Nat}
    (hu : u < I.graph.vertices) (hv : v < I.graph.vertices) (huv : u ≠ v)
    (hEdge : HasUndirectedEdge I.graph u v)
    (hxU : x ∈ compactPackingSetFromCodes u (compactCodedComplementEdges I))
    (hxV : x ∈ compactPackingSetFromCodes v (compactCodedComplementEdges I)) :
    False := by
  rcases (mem_compactPackingSetFromCodes_iff (compactCodedComplementEdges I) u x).1 hxU with
    hxMarkerU | hxCodeU
  · rcases (mem_compactPackingSetFromCodes_iff (compactCodedComplementEdges I) v x).1 hxV with
      hxMarkerV | hxCodeV
    · exact huv (by omega)
    · rcases hxCodeV with ⟨ceV, hMemV, hCodeV, _hIncV⟩
      have hGe := codeComplementEdgesFrom_mem_code_ge hMemV
      omega
  · rcases hxCodeU with ⟨ceU, hMemU, hCodeU, hIncU⟩
    rcases (mem_compactPackingSetFromCodes_iff (compactCodedComplementEdges I) v x).1 hxV with
      hxMarkerV | hxCodeV
    · have hGe := codeComplementEdgesFrom_mem_code_ge hMemU
      omega
    · rcases hxCodeV with ⟨ceV, hMemV, hCodeV, hIncV⟩
      rcases ceU with ⟨codeU, edgeU⟩
      rcases ceV with ⟨codeV, edgeV⟩
      dsimp at hCodeU hCodeV hIncU hIncV hMemU hMemV
      have hMemV' :
          (codeU, edgeV) ∈
            (codeComplementEdgesFrom I.graph.vertices (structuredComplementEdges I.graph)).2 := by
        have hCodeEq : codeV = codeU := by omega
        simpa [compactCodedComplementEdges, hCodeEq] using hMemV
      have hEdgeEq : edgeU = edgeV :=
        codeComplementEdgesFrom_code_unique hMemU hMemV'
      subst edgeV
      have hSourceMem :=
        codeComplementEdgesFrom_mem_edge hMemU
      have hStructured :=
        (mem_structuredComplementEdges_iff I.graph edgeU).1 hSourceMem
      rcases edgeU with ⟨a, b⟩
      rcases hStructured with ⟨_ha, _hb, _hab, hNonedge⟩
      dsimp at hIncU hIncV hNonedge
      rcases hIncU with haU | hbU <;> rcases hIncV with haV | hbV
      · omega
      · subst a
        subst b
        exact hNonedge hEdge
      · subst b
        subst a
        exact hNonedge ((hasUndirectedEdge_comm I.graph u v).1 hEdge)
      · omega

theorem compactMap_correct (I : CliqueInput) :
    cliqueStructuredDecisionProblem.isYes I ↔ SetPacking (compactMap I) := by
  change Clique I ↔ SetPacking (compactMap I)
  constructor
  · rintro ⟨vs, hLen, hNodup, hBounds, hAdj⟩
    let codedEdges := compactCodedComplementEdges I
    let selected := vs.map (fun v => compactPackingSetFromCodes v codedEdges)
    refine ⟨selected, by simp [selected, compactMap, hLen], ?_, ?_, ?_⟩
    · intro S hS
      rcases List.mem_map.mp hS with ⟨v, hv, rfl⟩
      exact
        (mem_compactSetFamilyFromCodes_iff I.graph.vertices codedEdges
          (compactPackingSetFromCodes v codedEdges)).2
          ⟨v, hBounds v hv, rfl⟩
    · exact hNodup.map_on (by
        intro u _hu v _hv hEq
        exact compactPackingSetFromCodes_injective_on hEq)
    · intro A hA B hB hNe x hxA hxB
      rcases List.mem_map.mp hA with ⟨u, huVs, rfl⟩
      rcases List.mem_map.mp hB with ⟨v, hvVs, rfl⟩
      by_cases huv : u = v
      · subst v
        exact hNe rfl
      · exact no_common_compactPackingSet_of_edge
          (I := I) (u := u) (v := v) (x := x)
          (hBounds u huVs) (hBounds v hvVs) huv
          (hAdj u huVs v hvVs huv) hxA hxB
  · rintro ⟨selected, hLen, hFamily, hNodup, hDisjoint⟩
    let codedEdges := compactCodedComplementEdges I
    let chosenSets := selected.take I.k
    let vs := chosenSets.map
      (compactVertexOfSet I.graph.vertices codedEdges)
    have hChosenSub : chosenSets.Sublist selected := by
      exact List.take_sublist I.k selected
    have hChosenNodup : chosenSets.Nodup := List.Nodup.sublist hChosenSub hNodup
    have hk : I.k ≤ selected.length := by
      simpa [compactMap] using hLen
    refine ⟨vs, ?_, ?_, ?_, ?_⟩
    · simp [vs, chosenSets, List.length_take, Nat.min_eq_left hk]
    · exact hChosenNodup.map_on (by
        intro A hA B hB hEq
        have hASelected : A ∈ selected := hChosenSub.subset hA
        have hBSelected : B ∈ selected := hChosenSub.subset hB
        have hAFamily :
            A ∈ compactSetFamilyFromCodes I.graph.vertices codedEdges := by
          simpa [compactMap, compactSetSystemFromCodes] using hFamily A hASelected
        have hBFamily :
            B ∈ compactSetFamilyFromCodes I.graph.vertices codedEdges := by
          simpa [compactMap, compactSetSystemFromCodes] using hFamily B hBSelected
        calc
          A = compactPackingSetFromCodes
                (compactVertexOfSet I.graph.vertices codedEdges A) codedEdges :=
            compactPackingSet_vertexOfSet_of_mem I.graph.vertices codedEdges hAFamily
          _ = compactPackingSetFromCodes
                (compactVertexOfSet I.graph.vertices codedEdges B) codedEdges := by rw [hEq]
          _ = B :=
            (compactPackingSet_vertexOfSet_of_mem I.graph.vertices codedEdges hBFamily).symm)
    · intro v hv
      rcases List.mem_map.mp hv with ⟨S, hS, rfl⟩
      have hSSelected : S ∈ selected := hChosenSub.subset hS
      have hSFamily :
          S ∈ compactSetFamilyFromCodes I.graph.vertices codedEdges := by
        simpa [compactMap, compactSetSystemFromCodes] using hFamily S hSSelected
      exact compactVertexOfSet_lt_of_mem I.graph.vertices codedEdges hSFamily
    · intro u hu v hv huv
      rcases List.mem_map.mp hu with ⟨A, hA, rfl⟩
      rcases List.mem_map.mp hv with ⟨B, hB, rfl⟩
      have hASelected : A ∈ selected := hChosenSub.subset hA
      have hBSelected : B ∈ selected := hChosenSub.subset hB
      have hAFamily :
          A ∈ compactSetFamilyFromCodes I.graph.vertices codedEdges := by
        simpa [compactMap, compactSetSystemFromCodes] using hFamily A hASelected
      have hBFamily :
          B ∈ compactSetFamilyFromCodes I.graph.vertices codedEdges := by
        simpa [compactMap, compactSetSystemFromCodes] using hFamily B hBSelected
      have hAeq :=
        compactPackingSet_vertexOfSet_of_mem I.graph.vertices codedEdges hAFamily
      have hBeq :=
        compactPackingSet_vertexOfSet_of_mem I.graph.vertices codedEdges hBFamily
      by_contra hNonedge
      rcases common_compactPackingSet_of_nonedge
          (I := I)
          (u := compactVertexOfSet I.graph.vertices codedEdges A)
          (v := compactVertexOfSet I.graph.vertices codedEdges B)
          (compactVertexOfSet_lt_of_mem I.graph.vertices codedEdges hAFamily)
          (compactVertexOfSet_lt_of_mem I.graph.vertices codedEdges hBFamily)
          huv hNonedge with
        ⟨x, hxACompact, hxBCompact⟩
      have hAneB : A ≠ B := by
        intro hAB
        exact huv (by simp [hAB])
      have hxA : x ∈ A := by
        rw [hAeq]
        exact hxACompact
      have hxB : x ∈ B := by
        rw [hBeq]
        exact hxBCompact
      exact hDisjoint A hASelected B hBSelected hAneB x hxA hxB

theorem codeComplementEdgeStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod codeComplementEdgesAccEncodedType edgeStructuredEncodedType)
      codeComplementEdgesAccEncodedType
      codeComplementEdgeStep := by
  let X := EncodedType.prod codeComplementEdgesAccEncodedType edgeStructuredEncodedType
  have hAcc :
      TMPolyTimeMap X codeComplementEdgesAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst codeComplementEdgesAccEncodedType edgeStructuredEncodedType
  have hEdge : TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd codeComplementEdgesAccEncodedType edgeStructuredEncodedType
  have hNext : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat codedComplementEdgeListEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, codeComplementEdgesAccEncodedType, X] using hComp
  have hOut :
      TMPolyTimeMap X codedComplementEdgeListEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat codedComplementEdgeListEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, codeComplementEdgesAccEncodedType, X] using hComp
  have hSucc :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => Nat.succ p.1.1) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hNext
    simpa [Function.comp] using hComp
  have hCoded :
      TMPolyTimeMap X codedComplementEdgeEncodedType
        (fun p : X.Carrier => (p.1.1, p.2)) := by
    simpa [codedComplementEdgeEncodedType, X] using TMPolyTimeMap.prod_mk hNext hEdge
  have hSingleton :
      TMPolyTimeMap X codedComplementEdgeListEncodedType
        (fun p : X.Carrier => [(p.1.1, p.2)]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton codedComplementEdgeEncodedType) hCoded
    simpa [Function.comp, codedComplementEdgeListEncodedType] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod codedComplementEdgeListEncodedType codedComplementEdgeListEncodedType)
        (fun p : X.Carrier => (p.1.2, [(p.1.1, p.2)])) :=
    TMPolyTimeMap.prod_mk hOut hSingleton
  have hAppend :
      TMPolyTimeMap X codedComplementEdgeListEncodedType
        (fun p : X.Carrier => codeComplementEdgeOutput p) := by
    have hComp :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_append codedComplementEdgeEncodedType)
        hAppendInput
    simpa [Function.comp, codeComplementEdgeOutput] using hComp
  have hPair :
      TMPolyTimeMap X codeComplementEdgesAccEncodedType
        (fun p : X.Carrier => (Nat.succ p.1.1, codeComplementEdgeOutput p)) := by
    simpa [codeComplementEdgesAccEncodedType, X] using TMPolyTimeMap.prod_mk hSucc hAppend
  simpa [codeComplementEdgeStep, X] using hPair

theorem codeComplementEdgeEdgeInstruction_tm_polytime :
    TMPolyTimeMap
      edgeStructuredEncodedType
      codeComplementEdgeInstructionEncodedType
      codeComplementEdgeEdgeInstruction := by
  let X := edgeStructuredEncodedType
  have hTrue : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hPayload :
      TMPolyTimeMap X codeComplementEdgeInstructionPayloadEncodedType
        (fun edge : X.Carrier => ((0 : Nat), edge)) :=
    TMPolyTimeMap.prod_mk hZero (TMPolyTimeMap.id X)
  have hInstruction :
      TMPolyTimeMap X codeComplementEdgeInstructionEncodedType
        (fun edge : X.Carrier => (true, ((0 : Nat), edge))) :=
    TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [codeComplementEdgeEdgeInstruction, codeComplementEdgeInstructionEncodedType,
    codeComplementEdgeInstructionPayloadEncodedType, X] using hInstruction

theorem codeComplementEdgeInstructions_tm_polytime :
    TMPolyTimeMap
      codeComplementEdgeInstructionInputEncodedType
      codeComplementEdgeInstructionListEncodedType
      codeComplementEdgeInstructions := by
  let X := codeComplementEdgeInstructionInputEncodedType
  have hStart : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, codeComplementEdgeInstructionInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat edgeListStructuredEncodedType
  have hEdges : TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, codeComplementEdgeInstructionInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat edgeListStructuredEncodedType
  have hFalse : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hDefaultEdge :
      TMPolyTimeMap X edgeStructuredEncodedType (fun _ : X.Carrier => edgeScanDefaultPair) :=
    TMPolyTimeMap.const X edgeStructuredEncodedType edgeScanDefaultPair
  have hInitPayload :
      TMPolyTimeMap X codeComplementEdgeInstructionPayloadEncodedType
        (fun p : X.Carrier => (p.1, edgeScanDefaultPair)) :=
    TMPolyTimeMap.prod_mk hStart hDefaultEdge
  have hInitInstruction :
      TMPolyTimeMap X codeComplementEdgeInstructionEncodedType
        (fun p : X.Carrier => codeComplementEdgeInitInstruction p.1) := by
    have hPair := TMPolyTimeMap.prod_mk hFalse hInitPayload
    simpa [codeComplementEdgeInitInstruction, codeComplementEdgeInstructionEncodedType,
      codeComplementEdgeInstructionPayloadEncodedType] using hPair
  have hInitSingleton :
      TMPolyTimeMap X codeComplementEdgeInstructionListEncodedType
        (fun p : X.Carrier => [codeComplementEdgeInitInstruction p.1]) := by
    have hComp :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.list_singleton codeComplementEdgeInstructionEncodedType)
        hInitInstruction
    simpa [Function.comp, codeComplementEdgeInstructionListEncodedType] using hComp
  have hEdgeInstructions :
      TMPolyTimeMap X codeComplementEdgeInstructionListEncodedType
        (fun p : X.Carrier => p.2.map codeComplementEdgeEdgeInstruction) := by
    have hMap := TMPolyTimeMap.list_map codeComplementEdgeEdgeInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hEdges
    simpa [Function.comp, codeComplementEdgeInstructionListEncodedType] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod codeComplementEdgeInstructionListEncodedType
          codeComplementEdgeInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([codeComplementEdgeInitInstruction p.1],
            p.2.map codeComplementEdgeEdgeInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hEdgeInstructions
  have hAppend :=
    TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append codeComplementEdgeInstructionEncodedType)
      hAppendInput
  simpa [Function.comp, codeComplementEdgeInstructions,
    codeComplementEdgeInstructionListEncodedType] using hAppend

theorem codeComplementEdgeScanStep_tm_polytime :
    TMPolyTimeMap
      codeComplementEdgeScanInputEncodedType
      codeComplementEdgesAccEncodedType
      codeComplementEdgeScanStep := by
  let X := codeComplementEdgeScanInputEncodedType
  let A := codeComplementEdgesAccEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X, codeComplementEdgeScanInputEncodedType] using
      TMPolyTimeMap.fst codeComplementEdgesAccEncodedType codeComplementEdgeInstructionEncodedType
  have hInstr :
      TMPolyTimeMap X codeComplementEdgeInstructionEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, codeComplementEdgeScanInputEncodedType] using
      TMPolyTimeMap.snd codeComplementEdgesAccEncodedType codeComplementEdgeInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst :=
      TMPolyTimeMap.fst EncodedType.bool codeComplementEdgeInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, codeComplementEdgeInstructionEncodedType, X] using hComp
  have hPayload :
      TMPolyTimeMap X codeComplementEdgeInstructionPayloadEncodedType
        (fun p : X.Carrier => p.2.2) := by
    have hSnd :=
      TMPolyTimeMap.snd EncodedType.bool codeComplementEdgeInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, codeComplementEdgeInstructionEncodedType, X] using hComp
  have hPayloadStart : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat edgeStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, codeComplementEdgeInstructionPayloadEncodedType, X] using hComp
  have hPayloadEdge :
      TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat edgeStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, codeComplementEdgeInstructionPayloadEncodedType, X] using hComp
  have hEmpty :
      TMPolyTimeMap X codedComplementEdgeListEncodedType
        (fun _ : X.Carrier => ([] : List CodedComplementEdge)) :=
    TMPolyTimeMap.const X codedComplementEdgeListEncodedType []
  have hInitOut :
      TMPolyTimeMap X A (fun p : X.Carrier => (p.2.2.1, ([] : List CodedComplementEdge))) :=
    TMPolyTimeMap.prod_mk hPayloadStart hEmpty
  have hStepInput :
      TMPolyTimeMap X
        (EncodedType.prod codeComplementEdgesAccEncodedType edgeStructuredEncodedType)
        (fun p : X.Carrier => (p.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAcc hPayloadEdge
  have hStepOut :
      TMPolyTimeMap X A (fun p : X.Carrier => codeComplementEdgeStep (p.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp codeComplementEdgeStep_tm_polytime hStepInput
    simpa [Function.comp] using hComp
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool X)
        A
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true => codeComplementEdgeStep (p.2.1, p.2.2.2.2)
          | false => (p.2.2.2.1, ([] : List CodedComplementEdge))) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier => (p.2.2.1, ([] : List CodedComplementEdge)))
      (fTrue := fun p : X.Carrier => codeComplementEdgeStep (p.1, p.2.2.2))
      (hFalse := hInitOut) (hTrue := hStepOut)
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨acc, instr⟩
  rcases instr with ⟨tag, payload⟩
  rcases payload with ⟨start, edge⟩
  cases tag <;> rfl

end SetPacking
end Karp21
end ComplexityReduction
