/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.Range
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SetCovering.IncidentRunner

/-!
TM-backed incidence-family runner for the Vertex Cover to Set Covering route.
-/

namespace ComplexityReduction
namespace Karp21
namespace SetCovering

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-! ### TM-facing incidence-family instruction layer -/

def incidenceFamilyPayloadEncodedType : EncodedType :=
  EncodedType.prod edgeListStructuredEncodedType EncodedType.nat

def incidenceFamilyInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool incidenceFamilyPayloadEncodedType

def incidenceFamilyInstructionListEncodedType : EncodedType :=
  EncodedType.list incidenceFamilyInstructionEncodedType

def incidenceFamilyInstructionInputEncodedType : EncodedType :=
  EncodedType.prod edgeListStructuredEncodedType EncodedType.nat

def incidenceFamilyAccEncodedType : EncodedType :=
  EncodedType.prod edgeListStructuredEncodedType setFamilyStructuredEncodedType

def incidenceFamilyStepInputEncodedType : EncodedType :=
  EncodedType.prod incidenceFamilyAccEncodedType incidenceFamilyInstructionEncodedType

def incidenceFamilyInitAcc : List (Nat × Nat) × List (List Nat) :=
  (([] : List (Nat × Nat)), ([] : List (List Nat)))

def incidenceFamilyInitInstruction
    (edges : List (Nat × Nat)) :
    Bool × (List (Nat × Nat) × Nat) :=
  (false, (edges, 0))

def incidenceFamilyVertexInstruction (v : Nat) :
    Bool × (List (Nat × Nat) × Nat) :=
  (true, (([] : List (Nat × Nat)), v))

def incidenceFamilyInstructions
    (p : List (Nat × Nat) × Nat) :
    List (Bool × (List (Nat × Nat) × Nat)) :=
  incidenceFamilyInitInstruction p.1 ::
    (List.range p.2).map incidenceFamilyVertexInstruction

def incidenceFamilyStep
    (p :
      (List (Nat × Nat) × List (List Nat)) ×
        (Bool × (List (Nat × Nat) × Nat))) :
    List (Nat × Nat) × List (List Nat) :=
  if p.2.1 then
    let edges := p.1.1
    let family := p.1.2
    let vertex := p.2.2.2
    (edges, family ++ [incidentEdgeIndicesFromEdges (edges, vertex)])
  else
    (p.2.2.1, [])

def incidenceFamilyFromInstructions
    (xs : List (Bool × (List (Nat × Nat) × Nat))) : List (List Nat) :=
  (xs.foldl (fun acc x => incidenceFamilyStep (acc, x)) incidenceFamilyInitAcc).2

def incidenceFamilyFromEdges
    (p : List (Nat × Nat) × Nat) : List (List Nat) :=
  incidenceFamilyFromInstructions (incidenceFamilyInstructions p)

/-! ### Semantics -/

theorem incidenceFamilyVertexInstructions_fold
    (edges : List (Nat × Nat)) (vertices : List Nat) (out : List (List Nat)) :
    ((vertices.map incidenceFamilyVertexInstruction).foldl
        (fun acc x => incidenceFamilyStep (acc, x)) (edges, out)) =
      (edges, out ++ vertices.map (fun v => incidentEdgeIndicesFromEdges (edges, v))) := by
  induction vertices generalizing out with
  | nil =>
      simp
  | cons v vs ih =>
      change
        ((vs.map incidenceFamilyVertexInstruction).foldl
            (fun acc x => incidenceFamilyStep (acc, x))
            (edges, out ++ [incidentEdgeIndicesFromEdges (edges, v)])) =
          (edges,
            out ++ incidentEdgeIndicesFromEdges (edges, v) ::
              vs.map (fun v => incidentEdgeIndicesFromEdges (edges, v)))
      rw [ih (out ++ [incidentEdgeIndicesFromEdges (edges, v)])]
      simp [List.append_assoc]

theorem incidenceFamilyFromEdges_eq_map
    (edges : List (Nat × Nat)) (vertices : Nat) :
    incidenceFamilyFromEdges (edges, vertices) =
      (List.range vertices).map (fun v => incidentEdgeIndicesFromEdges (edges, v)) := by
  change
    ((incidenceFamilyInitInstruction edges ::
        (List.range vertices).map incidenceFamilyVertexInstruction).foldl
        (fun acc x => incidenceFamilyStep (acc, x)) incidenceFamilyInitAcc).2 =
      (List.range vertices).map (fun v => incidentEdgeIndicesFromEdges (edges, v))
  rw [List.foldl_cons]
  simp [incidenceFamilyInitInstruction, incidenceFamilyStep]
  have h := incidenceFamilyVertexInstructions_fold edges (List.range vertices) []
  simpa using congrArg Prod.snd h

theorem incidenceFamilyFromEdges_eq_edgeSetSystem_sets
    (I : VertexCoverInput) :
    incidenceFamilyFromEdges (I.graph.edges, I.graph.vertices) =
      (edgeSetSystem I).sets := by
  rw [incidenceFamilyFromEdges_eq_map]
  simp [edgeSetSystem]
  intro v _hv
  exact incidentEdgeIndicesFromEdges_eq_incidentEdgeIndices I v

/-! ### TM witnesses for the instruction layer and step -/

theorem incidenceFamilyInitInstruction_tm_polytime :
    TMPolyTimeMap
      edgeListStructuredEncodedType
      incidenceFamilyInstructionEncodedType
      incidenceFamilyInitInstruction := by
  have hFalse :
      TMPolyTimeMap edgeListStructuredEncodedType EncodedType.bool (fun _ => false) :=
    TMPolyTimeMap.const edgeListStructuredEncodedType EncodedType.bool false
  have hEdges :
      TMPolyTimeMap edgeListStructuredEncodedType edgeListStructuredEncodedType id :=
    TMPolyTimeMap.id edgeListStructuredEncodedType
  have hZero :
      TMPolyTimeMap edgeListStructuredEncodedType EncodedType.nat (fun _ => (0 : Nat)) :=
    TMPolyTimeMap.const edgeListStructuredEncodedType EncodedType.nat (0 : Nat)
  have hPayload :
      TMPolyTimeMap edgeListStructuredEncodedType incidenceFamilyPayloadEncodedType
        (fun edges : List (Nat × Nat) => (edges, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hEdges hZero
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [incidenceFamilyInitInstruction, incidenceFamilyInstructionEncodedType,
    incidenceFamilyPayloadEncodedType] using hOut

theorem incidenceFamilyVertexInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      incidenceFamilyInstructionEncodedType
      incidenceFamilyVertexInstruction := by
  have hTrue : TMPolyTimeMap EncodedType.nat EncodedType.bool (fun _ => true) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool true
  have hEmpty :
      TMPolyTimeMap EncodedType.nat edgeListStructuredEncodedType
        (fun _ => ([] : List (Nat × Nat))) :=
    TMPolyTimeMap.const EncodedType.nat edgeListStructuredEncodedType []
  have hVertex : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  have hPayload :
      TMPolyTimeMap EncodedType.nat incidenceFamilyPayloadEncodedType
        (fun v : Nat => (([] : List (Nat × Nat)), v)) :=
    TMPolyTimeMap.prod_mk hEmpty hVertex
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [incidenceFamilyVertexInstruction, incidenceFamilyInstructionEncodedType,
    incidenceFamilyPayloadEncodedType] using hOut

theorem incidenceFamilyInstructions_tm_polytime :
    TMPolyTimeMap
      incidenceFamilyInstructionInputEncodedType
      incidenceFamilyInstructionListEncodedType
      incidenceFamilyInstructions := by
  let X := incidenceFamilyInstructionInputEncodedType
  have hEdges : TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, incidenceFamilyInstructionInputEncodedType] using
      TMPolyTimeMap.fst edgeListStructuredEncodedType EncodedType.nat
  have hVertexCount : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X, incidenceFamilyInstructionInputEncodedType] using
      TMPolyTimeMap.snd edgeListStructuredEncodedType EncodedType.nat
  have hInit :
      TMPolyTimeMap X incidenceFamilyInstructionEncodedType
        (fun p : X.Carrier => incidenceFamilyInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp incidenceFamilyInitInstruction_tm_polytime hEdges
    simpa [Function.comp, X] using hComp
  have hRange :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier => List.range p.2) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hVertexCount
    simpa [Function.comp, X] using hComp
  have hVertexInstructions :
      TMPolyTimeMap X incidenceFamilyInstructionListEncodedType
        (fun p : X.Carrier => (List.range p.2).map incidenceFamilyVertexInstruction) := by
    have hMap := TMPolyTimeMap.list_map incidenceFamilyVertexInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, incidenceFamilyInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod incidenceFamilyInstructionEncodedType
          incidenceFamilyInstructionListEncodedType)
        (fun p : X.Carrier =>
          (incidenceFamilyInitInstruction p.1,
            (List.range p.2).map incidenceFamilyVertexInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hVertexInstructions
  have hOut :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons incidenceFamilyInstructionEncodedType) hConsInput
  simpa [Function.comp, incidenceFamilyInstructions, incidenceFamilyInstructionListEncodedType, X]
    using hOut

theorem incidenceFamilyStep_tm_polytime :
    TMPolyTimeMap
      incidenceFamilyStepInputEncodedType
      incidenceFamilyAccEncodedType
      incidenceFamilyStep := by
  let X := incidenceFamilyStepInputEncodedType
  let A := incidenceFamilyAccEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X, incidenceFamilyStepInputEncodedType] using
      TMPolyTimeMap.fst incidenceFamilyAccEncodedType incidenceFamilyInstructionEncodedType
  have hInstr :
      TMPolyTimeMap X incidenceFamilyInstructionEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, incidenceFamilyStepInputEncodedType] using
      TMPolyTimeMap.snd incidenceFamilyAccEncodedType incidenceFamilyInstructionEncodedType
  have hEdges : TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, incidenceFamilyAccEncodedType, X] using hComp
  have hFamily :
      TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd edgeListStructuredEncodedType setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, incidenceFamilyAccEncodedType, X] using hComp
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool incidenceFamilyPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, incidenceFamilyInstructionEncodedType, X] using hComp
  have hPayload :
      TMPolyTimeMap X incidenceFamilyPayloadEncodedType (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool incidenceFamilyPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, incidenceFamilyInstructionEncodedType, X] using hComp
  have hInitEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, incidenceFamilyPayloadEncodedType, X] using hComp
  have hVertex :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd edgeListStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, incidenceFamilyPayloadEncodedType, X] using hComp
  have hEmptyFamily :
      TMPolyTimeMap X setFamilyStructuredEncodedType (fun _ => ([] : List (List Nat))) :=
    TMPolyTimeMap.const X setFamilyStructuredEncodedType []
  have hInitBranch :
      TMPolyTimeMap X A (fun p : X.Carrier => (p.2.2.1, ([] : List (List Nat)))) :=
    TMPolyTimeMap.prod_mk hInitEdges hEmptyFamily
  have hIncidentInput :
      TMPolyTimeMap X incidentEdgeInstructionInputEncodedType
        (fun p : X.Carrier => (p.1.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hEdges hVertex
  have hIncident :
      TMPolyTimeMap X setStructuredEncodedType
        (fun p : X.Carrier => incidentEdgeIndicesFromEdges (p.1.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp incidentEdgeIndicesFromEdges_tm_polytime hIncidentInput
    simpa [Function.comp, setStructuredEncodedType, X] using hComp
  have hIncidentSingleton :
      TMPolyTimeMap X setFamilyStructuredEncodedType
        (fun p : X.Carrier => [incidentEdgeIndicesFromEdges (p.1.1, p.2.2.2)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton setStructuredEncodedType)
      hIncident
    simpa [Function.comp, setFamilyStructuredEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod setFamilyStructuredEncodedType setFamilyStructuredEncodedType)
        (fun p : X.Carrier =>
          ((show List (List Nat) from p.1.2),
            [incidentEdgeIndicesFromEdges (p.1.1, p.2.2.2)])) :=
    TMPolyTimeMap.prod_mk hFamily hIncidentSingleton
  have hAppendFamily :
      TMPolyTimeMap X setFamilyStructuredEncodedType
        (fun p : X.Carrier =>
          List.append (show List (List Nat) from p.1.2)
            [incidentEdgeIndicesFromEdges (p.1.1, p.2.2.2)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append setStructuredEncodedType)
      hAppendInput
    simpa [Function.comp, setFamilyStructuredEncodedType, X] using hComp
  have hVertexBranch :
      TMPolyTimeMap X A
        (fun p : X.Carrier =>
          (p.1.1, List.append (show List (List Nat) from p.1.2)
            [incidentEdgeIndicesFromEdges (p.1.1, p.2.2.2)])) :=
    TMPolyTimeMap.prod_mk hEdges hAppendFamily
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true =>
              (p.2.1.1,
                List.append (show List (List Nat) from p.2.1.2)
                  [incidentEdgeIndicesFromEdges (p.2.1.1, p.2.2.2.2)])
          | false => (p.2.2.2.1, ([] : List (List Nat)))) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier => (p.2.2.1, ([] : List (List Nat))))
      (fTrue := fun p : X.Carrier =>
        (p.1.1, List.append (show List (List Nat) from p.1.2)
          [incidentEdgeIndicesFromEdges (p.1.1, p.2.2.2)]))
      hInitBranch hVertexBranch
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨edges, family⟩, ⟨tag, initEdges, vertex⟩⟩
  cases tag <;> rfl

/-! ### Reachable fold bounds and family runner -/

noncomputable def incidenceFamilySetBoundPolynomial : Polynomial Nat :=
  Polynomial.C 20 * (Polynomial.X * Polynomial.X) + Polynomial.C 50

@[simp] theorem incidenceFamilySetBoundPolynomial_eval (N : Nat) :
    incidenceFamilySetBoundPolynomial.eval N = 20 * (N * N) + 50 := by
  simp [incidenceFamilySetBoundPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

noncomputable def incidenceFamilyFoldAccBoundPolynomial : Polynomial Nat :=
  Polynomial.C 100 * (Polynomial.X * Polynomial.X * Polynomial.X) + Polynomial.C 100

@[simp] theorem incidenceFamilyFoldAccBoundPolynomial_eval (N : Nat) :
    incidenceFamilyFoldAccBoundPolynomial.eval N = 100 * (N * N * N) + 100 := by
  simp [incidenceFamilyFoldAccBoundPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

def incidenceFamilyAccBound
    (N processed : Nat) (acc : List (Nat × Nat) × List (List Nat)) : Prop :=
  edgeListStructuredEncodedType.inputSize acc.1 ≤ N ∧
    (∀ S ∈ acc.2, setStructuredEncodedType.inputSize S ≤
      incidenceFamilySetBoundPolynomial.eval N) ∧
      acc.2.length ≤ processed

theorem incidenceFamilyInstruction_payload_edges_inputSize_le
    {N : Nat} {instr : incidenceFamilyInstructionEncodedType.Carrier}
    (hInstr : incidenceFamilyInstructionEncodedType.inputSize instr ≤ N) :
    edgeListStructuredEncodedType.inputSize instr.2.1 ≤ N := by
  rcases instr with ⟨tag, edges, vertex⟩
  change edgeListStructuredEncodedType.inputSize edges ≤ N
  simp [incidenceFamilyInstructionEncodedType, incidenceFamilyPayloadEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_bool] at hInstr
  omega

theorem incidenceFamilyInstruction_vertex_inputSize_le
    {N : Nat} {instr : incidenceFamilyInstructionEncodedType.Carrier}
    (hInstr : incidenceFamilyInstructionEncodedType.inputSize instr ≤ N) :
    EncodedType.nat.inputSize instr.2.2 ≤ N := by
  rcases instr with ⟨tag, edges, vertex⟩
  simp [incidenceFamilyInstructionEncodedType, incidenceFamilyPayloadEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_bool, EncodedType.inputSize_nat] at hInstr ⊢
  omega

theorem incidenceFamilyIncident_inputSize_le
    {N : Nat} {edges : List (Nat × Nat)} {vertex : Nat}
    (hEdges : edgeListStructuredEncodedType.inputSize edges ≤ N)
    (hVertex : EncodedType.nat.inputSize vertex ≤ N) :
    setStructuredEncodedType.inputSize (incidentEdgeIndicesFromEdges (edges, vertex)) ≤
      incidenceFamilySetBoundPolynomial.eval N := by
  have hPair :
      incidentEdgeInstructionInputEncodedType.inputSize (edges, vertex) ≤ 2 * N + 1 := by
    have hVertexNat : vertex + 1 ≤ N := by
      simpa [EncodedType.inputSize_nat] using hVertex
    simp [incidentEdgeInstructionInputEncodedType, EncodedType.inputSize_prod]
    omega
  have hBase := incidentEdgeIndicesFromEdges_inputSize_le (edges, vertex)
  have hPow :
      incidentEdgeInstructionInputEncodedType.inputSize (edges, vertex) ^ 2 ≤
        (2 * N + 1) ^ 2 :=
    Nat.pow_le_pow_left hPair 2
  calc
    setStructuredEncodedType.inputSize (incidentEdgeIndicesFromEdges (edges, vertex))
        ≤ 3 * incidentEdgeInstructionInputEncodedType.inputSize (edges, vertex) ^ 2 + 10 := by
          simpa [setStructuredEncodedType] using hBase
    _ ≤ 3 * (2 * N + 1) ^ 2 + 10 := by
          nlinarith
    _ ≤ incidenceFamilySetBoundPolynomial.eval N := by
          simp [incidenceFamilySetBoundPolynomial_eval]
          nlinarith [sq_nonneg (N : Int)]

theorem incidenceFamilyStep_bound {N processed : Nat}
    {acc : incidenceFamilyAccEncodedType.Carrier}
    {instr : incidenceFamilyInstructionEncodedType.Carrier}
    (hAcc : incidenceFamilyAccBound N processed acc)
    (_hProcessed : processed + 1 ≤ N)
    (hInstr : incidenceFamilyInstructionEncodedType.inputSize instr ≤ N) :
    incidenceFamilyAccBound N (processed + 1) (incidenceFamilyStep (acc, instr)) := by
  rcases acc with ⟨edges, family⟩
  rcases instr with ⟨tag, initEdges, vertex⟩
  rcases hAcc with ⟨hEdges, hFamilyMem, hFamilyLen⟩
  cases tag
  · have hInitEdges :
        edgeListStructuredEncodedType.inputSize initEdges ≤ N :=
      incidenceFamilyInstruction_payload_edges_inputSize_le
        (N := N) (instr := (false, (initEdges, vertex))) hInstr
    simp [incidenceFamilyStep, incidenceFamilyAccBound]
    exact hInitEdges
  · have hVertex :
        EncodedType.nat.inputSize vertex ≤ N :=
      incidenceFamilyInstruction_vertex_inputSize_le
        (N := N) (instr := (true, (initEdges, vertex))) hInstr
    have hIncident :=
      incidenceFamilyIncident_inputSize_le (N := N) (edges := edges) (vertex := vertex)
        hEdges hVertex
    simp [incidenceFamilyStep, incidenceFamilyAccBound]
    refine ⟨hEdges, ?_, by simp [hFamilyLen]⟩
    intro S hS
    rcases hS with hOld | hNew
    · simpa using hFamilyMem S hOld
    · have hEq : S = incidentEdgeIndicesFromEdges (edges, vertex) := by
        simpa using hNew
      simpa [hEq] using hIncident

theorem incidenceFamilyFold_bound_aux
    {N processed : Nat}
    (xs : List incidenceFamilyInstructionEncodedType.Carrier)
    (acc : incidenceFamilyAccEncodedType.Carrier)
    (hAcc : incidenceFamilyAccBound N processed acc)
    (hLen : processed + xs.length ≤ N)
    (hInstr : ∀ instr ∈ xs, incidenceFamilyInstructionEncodedType.inputSize instr ≤ N) :
    incidenceFamilyAccBound N (processed + xs.length)
      (xs.foldl (fun acc x => incidenceFamilyStep (acc, x)) acc) := by
  induction xs generalizing processed acc with
  | nil =>
      simpa using hAcc
  | cons x xs ih =>
      have hx : incidenceFamilyInstructionEncodedType.inputSize x ≤ N := hInstr x (by simp)
      have hStepProcessed : processed + 1 ≤ N := by
        simp only [List.length_cons] at hLen
        omega
      have hStep := incidenceFamilyStep_bound hAcc hStepProcessed hx
      have hTailLen : (processed + 1) + xs.length ≤ N := by
        simp only [List.length_cons] at hLen
        omega
      have hTailInstr :
          ∀ instr ∈ xs, incidenceFamilyInstructionEncodedType.inputSize instr ≤ N := by
        intro instr hin
        exact hInstr instr (by simp [hin])
      have hTail :=
        ih (processed := processed + 1) (acc := incidenceFamilyStep (acc, x))
          hStep hTailLen hTailInstr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hTail

theorem incidenceFamilyFold_bound_of_inputSize_le
    {N : Nat} (xs : List incidenceFamilyInstructionEncodedType.Carrier)
    (hSize : incidenceFamilyInstructionListEncodedType.inputSize xs ≤ N) :
    incidenceFamilyAccBound N xs.length
      (xs.foldl (fun acc x => incidenceFamilyStep (acc, x)) incidenceFamilyInitAcc) := by
  have hInit : incidenceFamilyAccBound N 0 incidenceFamilyInitAcc := by
    have hEmptyEdges : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 :=
      rfl
    simp [incidenceFamilyAccBound, incidenceFamilyInitAcc, hEmptyEdges]
  have hLen : 0 + xs.length ≤ N := by
    have hLenInput :=
      incidentEncodedList_length_le_inputSize incidenceFamilyInstructionEncodedType xs
    have hLenInput' : xs.length ≤ incidenceFamilyInstructionListEncodedType.inputSize xs := by
      simpa [incidenceFamilyInstructionListEncodedType] using hLenInput
    omega
  have hInstr :
      ∀ instr ∈ xs, incidenceFamilyInstructionEncodedType.inputSize instr ≤ N := by
    intro instr hin
    have hElem :=
      incidentEncodedList_element_inputSize_le
        (X := incidenceFamilyInstructionEncodedType) (x := instr) (xs := xs) hin
    have hElem' : incidenceFamilyInstructionEncodedType.inputSize instr ≤
        incidenceFamilyInstructionListEncodedType.inputSize xs := by
      simpa [incidenceFamilyInstructionListEncodedType] using hElem
    omega
  have h :=
    incidenceFamilyFold_bound_aux (N := N) (processed := 0) xs incidenceFamilyInitAcc
      hInit hLen hInstr
  simpa using h

theorem incidenceFamilyAccBound_inputSize_le {N processed : Nat}
    {acc : incidenceFamilyAccEncodedType.Carrier}
    (hAcc : incidenceFamilyAccBound N processed acc)
    (hProcessed : processed ≤ N) :
    incidenceFamilyAccEncodedType.inputSize acc ≤
      incidenceFamilyFoldAccBoundPolynomial.eval N := by
  rcases acc with ⟨edges, family⟩
  rcases hAcc with ⟨hEdges, hFamilyMem, hFamilyLen⟩
  let Bset := incidenceFamilySetBoundPolynomial.eval N
  have hFamilySize :
      setFamilyStructuredEncodedType.inputSize family ≤ processed * (Bset + 1) := by
    have hList :=
      ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
        setStructuredEncodedType family Bset (by
          intro S hS
          exact hFamilyMem S hS)
    exact hList.trans (Nat.mul_le_mul_right (Bset + 1) hFamilyLen)
  have hFamilySizeN :
      setFamilyStructuredEncodedType.inputSize family ≤ N * (Bset + 1) :=
    hFamilySize.trans (Nat.mul_le_mul_right (Bset + 1) hProcessed)
  simp [incidenceFamilyAccEncodedType, EncodedType.inputSize_prod]
  have hBset : Bset = 20 * (N * N) + 50 := by
    simp [Bset]
  nlinarith [sq_nonneg (N : Int), hEdges, hFamilySizeN]

noncomputable def incidenceFamilyFoldTimePolynomial
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod incidenceFamilyAccEncodedType
          incidenceFamilyInstructionEncodedType).encode
        incidenceFamilyAccEncodedType.encode
        incidenceFamilyStep) : Polynomial Nat :=
  TM2Programs.listFoldBoundedTimePolynomial hStep.tm incidenceFamilyFoldAccBoundPolynomial
    (hStep.time.comp
      (incidenceFamilyFoldAccBoundPolynomial + Polynomial.X + Polynomial.C 5))

theorem incidenceFamilyFold_tm_polytime :
    TMPolyTimeMap
      incidenceFamilyInstructionListEncodedType
      incidenceFamilyAccEncodedType
      (fun xs : List incidenceFamilyInstructionEncodedType.Carrier =>
        xs.foldl (fun acc x => incidenceFamilyStep (acc, x)) incidenceFamilyInitAcc) := by
  rcases incidenceFamilyStep_tm_polytime with ⟨hStep⟩
  let time := incidenceFamilyFoldTimePolynomial hStep
  refine
    TMPolyTimeMap.list_foldl_typed
      incidenceFamilyInstructionEncodedType incidenceFamilyAccEncodedType
      incidenceFamilyStep incidenceFamilyInitAcc hStep time ?_
  intro source
  let N := incidenceFamilyInstructionListEncodedType.inputSize source
  let B := incidenceFamilyFoldAccBoundPolynomial.eval N
  let T := hStep.time.eval (B + N + 5)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hSourceLenN : source.length ≤ N := by
    have hLen :=
      incidentEncodedList_length_le_inputSize incidenceFamilyInstructionEncodedType source
    simpa [N, incidenceFamilyInstructionListEncodedType] using hLen
  have hLoopAux :
      ∀ (pref rest : List incidenceFamilyInstructionEncodedType.Carrier),
        source = pref ++ rest →
          TM2Programs.listFoldTypedLoopTime
              incidenceFamilyInstructionEncodedType incidenceFamilyAccEncodedType
              incidenceFamilyStep hStep
              (pref.foldl (fun acc x => incidenceFamilyStep (acc, x)) incidenceFamilyInitAcc)
              rest ≤
            C * (EncodedType.list incidenceFamilyInstructionEncodedType).inputSize rest := by
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
        have hxN : incidenceFamilyInstructionEncodedType.inputSize x ≤ N := by
          have hElem :=
            incidentEncodedList_element_inputSize_le
              (X := incidenceFamilyInstructionEncodedType) (x := x) (xs := source)
              hxMemSource
          simpa [N, incidenceFamilyInstructionListEncodedType] using hElem
        have hPrefixSize : incidenceFamilyInstructionListEncodedType.inputSize pref ≤ N := by
          have hEqSize :
              incidenceFamilyInstructionListEncodedType.inputSize source =
                incidenceFamilyInstructionListEncodedType.inputSize pref +
                  incidenceFamilyInstructionListEncodedType.inputSize (x :: xs) := by
            rw [hEq]
            exact incidentEncodedList_inputSize_append incidenceFamilyInstructionEncodedType
              pref (x :: xs)
          omega
        have hPrefixBound :=
          incidenceFamilyFold_bound_of_inputSize_le (N := N) pref hPrefixSize
        have hPrefixLenN : pref.length ≤ N := by
          have hLen :=
            incidentEncodedList_length_le_inputSize incidenceFamilyInstructionEncodedType pref
          have hLen' :
              pref.length ≤ incidenceFamilyInstructionListEncodedType.inputSize pref := by
            simpa [incidenceFamilyInstructionListEncodedType] using hLen
          omega
        have hAccSize :
            incidenceFamilyAccEncodedType.inputSize
                (pref.foldl (fun acc x => incidenceFamilyStep (acc, x))
                  incidenceFamilyInitAcc) ≤ B := by
          simpa [B] using
            incidenceFamilyAccBound_inputSize_le hPrefixBound hPrefixLenN
        have hStepProcessed : pref.length + 1 ≤ N := by
          have hLenEq : source.length = pref.length + (x :: xs).length := by
            rw [hEq, List.length_append]
          simp only [List.length_cons] at hLenEq
          omega
        have hStepBound :=
          incidenceFamilyStep_bound hPrefixBound hStepProcessed hxN
        have hStepSize :
            incidenceFamilyAccEncodedType.inputSize
                (incidenceFamilyStep
                  (pref.foldl (fun acc x => incidenceFamilyStep (acc, x))
                    incidenceFamilyInitAcc, x)) ≤ B := by
          simpa [B] using
            incidenceFamilyAccBound_inputSize_le hStepBound hStepProcessed
        have hStepTime :
            hStep.time.eval
                ((EncodedType.prod incidenceFamilyAccEncodedType
                  incidenceFamilyInstructionEncodedType).inputSize
                  (pref.foldl (fun acc x => incidenceFamilyStep (acc, x))
                    incidenceFamilyInitAcc, x)) ≤ T := by
          have hArg :
              (EncodedType.prod incidenceFamilyAccEncodedType
                incidenceFamilyInstructionEncodedType).inputSize
                  (pref.foldl (fun acc x => incidenceFamilyStep (acc, x))
                    incidenceFamilyInitAcc, x) ≤ B + N + 5 := by
            rw [EncodedType.inputSize_prod]
            change
              incidenceFamilyAccEncodedType.inputSize
                    (pref.foldl (fun acc x => incidenceFamilyStep (acc, x))
                      incidenceFamilyInitAcc) +
                  1 + incidenceFamilyInstructionEncodedType.inputSize x ≤ B + N + 5
            omega
          exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
        have hBlock :
            TM2Programs.listFoldBlockTime hStep.tm
                (incidenceFamilyInstructionEncodedType.encode x).length
                (incidenceFamilyAccEncodedType.encode
                  (pref.foldl (fun acc x => incidenceFamilyStep (acc, x))
                    incidenceFamilyInitAcc)).length
                (incidenceFamilyAccEncodedType.encode
                  (incidenceFamilyStep
                    (pref.foldl (fun acc x => incidenceFamilyStep (acc, x))
                      incidenceFamilyInitAcc, x))).length
                (hStep.time.eval
                  ((EncodedType.prod incidenceFamilyAccEncodedType
                    incidenceFamilyInstructionEncodedType).inputSize
                    (pref.foldl (fun acc x => incidenceFamilyStep (acc, x))
                      incidenceFamilyInitAcc, x))) ≤
              C * (incidenceFamilyInstructionEncodedType.inputSize x + 1) := by
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
                incidenceFamilyInstructionEncodedType incidenceFamilyAccEncodedType
                incidenceFamilyStep hStep
                (incidenceFamilyStep
                  (pref.foldl (fun acc x => incidenceFamilyStep (acc, x))
                    incidenceFamilyInitAcc, x)) xs ≤
              C * (EncodedType.list incidenceFamilyInstructionEncodedType).inputSize xs := by
          have hFoldPref :
              (pref ++ [x]).foldl
                  (fun acc x => incidenceFamilyStep (acc, x)) incidenceFamilyInitAcc =
                incidenceFamilyStep
                  (pref.foldl (fun acc x => incidenceFamilyStep (acc, x))
                    incidenceFamilyInitAcc, x) := by
            exact
              List.foldl_concat
                (fun acc x => incidenceFamilyStep (acc, x)) incidenceFamilyInitAcc x pref
          convert hTailRaw using 1
          exact congrArg
            (fun acc =>
              TM2Programs.listFoldTypedLoopTime
                incidenceFamilyInstructionEncodedType incidenceFamilyAccEncodedType
                incidenceFamilyStep hStep acc xs)
            hFoldPref.symm
        calc
          TM2Programs.listFoldTypedLoopTime
              incidenceFamilyInstructionEncodedType incidenceFamilyAccEncodedType
              incidenceFamilyStep hStep
              (pref.foldl (fun acc x => incidenceFamilyStep (acc, x)) incidenceFamilyInitAcc)
              (x :: xs)
              =
            TM2Programs.listFoldTypedLoopTime
                incidenceFamilyInstructionEncodedType incidenceFamilyAccEncodedType
                incidenceFamilyStep hStep
                (incidenceFamilyStep
                  (pref.foldl (fun acc x => incidenceFamilyStep (acc, x))
                    incidenceFamilyInitAcc, x)) xs +
              TM2Programs.listFoldBlockTime hStep.tm
                (incidenceFamilyInstructionEncodedType.encode x).length
                (incidenceFamilyAccEncodedType.encode
                  (pref.foldl (fun acc x => incidenceFamilyStep (acc, x))
                    incidenceFamilyInitAcc)).length
                (incidenceFamilyAccEncodedType.encode
                  (incidenceFamilyStep
                    (pref.foldl (fun acc x => incidenceFamilyStep (acc, x))
                      incidenceFamilyInitAcc, x))).length
                (hStep.time.eval
                  ((EncodedType.prod incidenceFamilyAccEncodedType
                    incidenceFamilyInstructionEncodedType).inputSize
                    (pref.foldl (fun acc x => incidenceFamilyStep (acc, x))
                      incidenceFamilyInitAcc, x))) := by
                rfl
          _ ≤
              C * (EncodedType.list incidenceFamilyInstructionEncodedType).inputSize xs +
                C * (incidenceFamilyInstructionEncodedType.inputSize x + 1) :=
                Nat.add_le_add hTail hBlock
          _ ≤ C * (EncodedType.list incidenceFamilyInstructionEncodedType).inputSize (x :: xs) := by
                rw [EncodedType.inputSize_list_cons]
                nlinarith
  have hLoop :
      TM2Programs.listFoldTypedLoopTime
          incidenceFamilyInstructionEncodedType incidenceFamilyAccEncodedType
          incidenceFamilyStep hStep incidenceFamilyInitAcc source ≤ C * N := by
    have h := hLoopAux [] source (by simp)
    simpa [N, incidenceFamilyInstructionListEncodedType] using h
  have hTimeEval : time.eval N = (C + 2) * (N + 1) := by
    simp [time, incidenceFamilyFoldTimePolynomial, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval, TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_comp]
  change 2 +
      TM2Programs.listFoldTypedLoopTime
        incidenceFamilyInstructionEncodedType incidenceFamilyAccEncodedType
        incidenceFamilyStep hStep incidenceFamilyInitAcc source ≤ time.eval N
  rw [hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

theorem incidenceFamilyFromInstructions_tm_polytime :
    TMPolyTimeMap
      incidenceFamilyInstructionListEncodedType
      setFamilyStructuredEncodedType
      incidenceFamilyFromInstructions := by
  have hFold := incidenceFamilyFold_tm_polytime
  have hSnd := TMPolyTimeMap.snd edgeListStructuredEncodedType setFamilyStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, incidenceFamilyFromInstructions, incidenceFamilyAccEncodedType]
    using hComp

theorem incidenceFamilyFromEdges_tm_polytime :
    TMPolyTimeMap
      incidenceFamilyInstructionInputEncodedType
      setFamilyStructuredEncodedType
      incidenceFamilyFromEdges := by
  have hComp :=
    TMPolyTimeMap.comp incidenceFamilyFromInstructions_tm_polytime
      incidenceFamilyInstructions_tm_polytime
  simpa [Function.comp, incidenceFamilyFromEdges] using hComp

theorem incidenceFamilyFromEdges_inputSize_le
    (p : incidenceFamilyInstructionInputEncodedType.Carrier) :
    setFamilyStructuredEncodedType.inputSize (incidenceFamilyFromEdges p) ≤
      1000 * incidenceFamilyInstructionInputEncodedType.inputSize p ^ 3 + 1000 := by
  rcases p with ⟨edges, vertexCount⟩
  change Nat at vertexCount
  let N := incidenceFamilyInstructionInputEncodedType.inputSize (edges, vertexCount)
  change setFamilyStructuredEncodedType.inputSize
      (incidenceFamilyFromEdges (edges, vertexCount)) ≤ 1000 * N ^ 3 + 1000
  have hEdgesSize : edgeListStructuredEncodedType.inputSize edges ≤ N := by
    unfold N
    simp [incidenceFamilyInstructionInputEncodedType, EncodedType.inputSize_prod]
    omega
  have hVertexCount : vertexCount ≤ N := by
    unfold N
    simp [incidenceFamilyInstructionInputEncodedType, EncodedType.inputSize_prod,
      EncodedType.inputSize_nat]
    omega
  have hSetMem :
      ∀ S ∈ incidenceFamilyFromEdges (edges, vertexCount),
        setStructuredEncodedType.inputSize S ≤ incidenceFamilySetBoundPolynomial.eval N := by
    intro S hS
    rw [incidenceFamilyFromEdges_eq_map] at hS
    rcases List.mem_map.mp hS with ⟨v, hv, rfl⟩
    have hvLt : v < vertexCount := by
      simpa using List.mem_range.mp hv
    have hVertexSize : EncodedType.nat.inputSize v ≤ N := by
      simp [EncodedType.inputSize_nat]
      omega
    exact incidenceFamilyIncident_inputSize_le (N := N) hEdgesSize hVertexSize
  have hFamilyList :=
    ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
      setStructuredEncodedType (incidenceFamilyFromEdges (edges, vertexCount))
      (incidenceFamilySetBoundPolynomial.eval N) hSetMem
  have hLen : (incidenceFamilyFromEdges (edges, vertexCount)).length = vertexCount := by
    rw [incidenceFamilyFromEdges_eq_map]
    simp
  have hSizeN :
      setFamilyStructuredEncodedType.inputSize (incidenceFamilyFromEdges (edges, vertexCount)) ≤
        N * (incidenceFamilySetBoundPolynomial.eval N + 1) := by
    have hLenLe : (incidenceFamilyFromEdges (edges, vertexCount)).length ≤ N := by
      omega
    exact hFamilyList.trans
      (Nat.mul_le_mul_right (incidenceFamilySetBoundPolynomial.eval N + 1) hLenLe)
  have hPoly :
      N * (incidenceFamilySetBoundPolynomial.eval N + 1) ≤ 1000 * N ^ 3 + 1000 := by
    by_cases hZero : N = 0
    · simp [hZero, incidenceFamilySetBoundPolynomial_eval]
    · have hPos : 1 ≤ N := by omega
      simp [incidenceFamilySetBoundPolynomial_eval]
      nlinarith [sq_nonneg (N : Int), hPos]
  exact hSizeN.trans hPoly

theorem incidenceFamilyFromEdges_polynomialSizeBound :
    PolynomialSizeBound
      (fun p : incidenceFamilyInstructionInputEncodedType.Carrier =>
        incidenceFamilyInstructionInputEncodedType.inputSize p)
      (fun xs : List (List Nat) => setFamilyStructuredEncodedType.inputSize xs)
      incidenceFamilyFromEdges :=
  PolynomialSizeBound.intro_with 3 1000 1000 incidenceFamilyFromEdges_inputSize_le

noncomputable def incidenceFamilyFromEdgesTMBackedMap :
    TMBackedCostedMap
      incidenceFamilyInstructionInputEncodedType
      setFamilyStructuredEncodedType
      incidenceFamilyFromEdges where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      incidenceFamilyFromEdges_polynomialSizeBound
  tm_polytime := incidenceFamilyFromEdges_tm_polytime

end SetCovering
end Karp21
end ComplexityReduction
