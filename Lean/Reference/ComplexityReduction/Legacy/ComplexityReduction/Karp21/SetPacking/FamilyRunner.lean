/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.Range
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SetPacking.IncidentRunner

/-!
TM-backed set-family runner for the compact Clique-to-Set-Packing route.
-/

namespace ComplexityReduction
namespace Karp21
namespace SetPacking

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-! ### Instruction layer -/

def compactFamilyPayloadEncodedType : EncodedType :=
  EncodedType.prod codedComplementEdgeListEncodedType EncodedType.nat

def compactFamilyInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool compactFamilyPayloadEncodedType

def compactFamilyInstructionListEncodedType : EncodedType :=
  EncodedType.list compactFamilyInstructionEncodedType

def compactFamilyInstructionInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat codedComplementEdgeListEncodedType

def compactFamilyAccEncodedType : EncodedType :=
  EncodedType.prod codedComplementEdgeListEncodedType setFamilyStructuredEncodedType

def compactFamilyStepInputEncodedType : EncodedType :=
  EncodedType.prod compactFamilyAccEncodedType compactFamilyInstructionEncodedType

def compactFamilyInitAcc : List CodedComplementEdge × List (List Nat) :=
  (([] : List CodedComplementEdge), ([] : List (List Nat)))

def compactFamilyInitInstruction (codedEdges : List CodedComplementEdge) :
    Bool × (List CodedComplementEdge × Nat) :=
  (false, (codedEdges, 0))

def compactFamilyVertexInstruction (v : Nat) :
    Bool × (List CodedComplementEdge × Nat) :=
  (true, (([] : List CodedComplementEdge), v))

def compactFamilyInstructions (p : Nat × List CodedComplementEdge) :
    List (Bool × (List CodedComplementEdge × Nat)) :=
  compactFamilyInitInstruction p.2 ::
    (List.range p.1).map compactFamilyVertexInstruction

def compactFamilyStep
    (p :
      (List CodedComplementEdge × List (List Nat)) ×
        (Bool × (List CodedComplementEdge × Nat))) :
    List CodedComplementEdge × List (List Nat) :=
  if p.2.1 then
    let codedEdges := p.1.1
    let family := p.1.2
    let v := p.2.2.2
    (codedEdges, family ++ [compactPackingSetFromCodes v codedEdges])
  else
    (p.2.2.1, [])

def compactFamilyFromInstructions
    (xs : List (Bool × (List CodedComplementEdge × Nat))) : List (List Nat) :=
  (xs.foldl (fun acc instr => compactFamilyStep (acc, instr)) compactFamilyInitAcc).2

def compactFamilyFromInput (p : Nat × List CodedComplementEdge) : List (List Nat) :=
  compactFamilyFromInstructions (compactFamilyInstructions p)

/-! ### Semantics -/

theorem compactFamilyVertexInstructions_fold
    (codedEdges : List CodedComplementEdge) (xs : List Nat) (out : List (List Nat)) :
    ((xs.map compactFamilyVertexInstruction).foldl
        (fun acc instr => compactFamilyStep (acc, instr)) (codedEdges, out)) =
      (codedEdges, out ++ xs.map (fun v => compactPackingSetFromCodes v codedEdges)) := by
  induction xs generalizing out with
  | nil =>
      simp
  | cons v xs ih =>
      change
        ((xs.map compactFamilyVertexInstruction).foldl
            (fun acc instr => compactFamilyStep (acc, instr))
            (codedEdges, out ++ [compactPackingSetFromCodes v codedEdges])) =
          (codedEdges,
            out ++ compactPackingSetFromCodes v codedEdges ::
              xs.map (fun v => compactPackingSetFromCodes v codedEdges))
      rw [ih (out ++ [compactPackingSetFromCodes v codedEdges])]
      simp [List.append_assoc]

theorem compactFamilyFromInput_eq
    (n : Nat) (codedEdges : List CodedComplementEdge) :
    compactFamilyFromInput (n, codedEdges) =
      compactSetFamilyFromCodes n codedEdges := by
  change
    ((compactFamilyInitInstruction codedEdges ::
        (List.range n).map compactFamilyVertexInstruction).foldl
        (fun acc instr => compactFamilyStep (acc, instr)) compactFamilyInitAcc).2 =
      compactSetFamilyFromCodes n codedEdges
  rw [List.foldl_cons]
  simp [compactFamilyInitInstruction, compactFamilyStep, compactSetFamilyFromCodes]
  have h := compactFamilyVertexInstructions_fold codedEdges (List.range n) []
  simpa using congrArg Prod.snd h

/-! ### TM witnesses for instructions and one step -/

theorem compactFamilyInitInstruction_tm_polytime :
    TMPolyTimeMap
      codedComplementEdgeListEncodedType
      compactFamilyInstructionEncodedType
      compactFamilyInitInstruction := by
  have hFalse :
      TMPolyTimeMap codedComplementEdgeListEncodedType EncodedType.bool (fun _ => false) :=
    TMPolyTimeMap.const codedComplementEdgeListEncodedType EncodedType.bool false
  have hEdges :
      TMPolyTimeMap codedComplementEdgeListEncodedType codedComplementEdgeListEncodedType id :=
    TMPolyTimeMap.id codedComplementEdgeListEncodedType
  have hZero :
      TMPolyTimeMap codedComplementEdgeListEncodedType EncodedType.nat (fun _ => (0 : Nat)) :=
    TMPolyTimeMap.const codedComplementEdgeListEncodedType EncodedType.nat (0 : Nat)
  have hPayload :
      TMPolyTimeMap codedComplementEdgeListEncodedType compactFamilyPayloadEncodedType
        (fun codedEdges : List CodedComplementEdge => (codedEdges, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hEdges hZero
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [compactFamilyInitInstruction, compactFamilyInstructionEncodedType,
    compactFamilyPayloadEncodedType] using hOut

theorem compactFamilyVertexInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      compactFamilyInstructionEncodedType
      compactFamilyVertexInstruction := by
  have hTrue : TMPolyTimeMap EncodedType.nat EncodedType.bool (fun _ => true) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool true
  have hEmpty :
      TMPolyTimeMap EncodedType.nat codedComplementEdgeListEncodedType
        (fun _ => ([] : List CodedComplementEdge)) :=
    TMPolyTimeMap.const EncodedType.nat codedComplementEdgeListEncodedType []
  have hVertex : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  have hPayload :
      TMPolyTimeMap EncodedType.nat compactFamilyPayloadEncodedType
        (fun v : Nat => (([] : List CodedComplementEdge), v)) :=
    TMPolyTimeMap.prod_mk hEmpty hVertex
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [compactFamilyVertexInstruction, compactFamilyInstructionEncodedType,
    compactFamilyPayloadEncodedType] using hOut

theorem compactFamilyInstructions_tm_polytime :
    TMPolyTimeMap
      compactFamilyInstructionInputEncodedType
      compactFamilyInstructionListEncodedType
      compactFamilyInstructions := by
  let X := compactFamilyInstructionInputEncodedType
  have hVertexCount : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, compactFamilyInstructionInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat codedComplementEdgeListEncodedType
  have hCodedEdges :
      TMPolyTimeMap X codedComplementEdgeListEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, compactFamilyInstructionInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat codedComplementEdgeListEncodedType
  have hInit :
      TMPolyTimeMap X compactFamilyInstructionEncodedType
        (fun p : X.Carrier => compactFamilyInitInstruction p.2) := by
    have hComp := TMPolyTimeMap.comp compactFamilyInitInstruction_tm_polytime hCodedEdges
    simpa [Function.comp, X] using hComp
  have hRange :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier => List.range p.1) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hVertexCount
    simpa [Function.comp, X] using hComp
  have hVertexInstructions :
      TMPolyTimeMap X compactFamilyInstructionListEncodedType
        (fun p : X.Carrier => (List.range p.1).map compactFamilyVertexInstruction) := by
    have hMap := TMPolyTimeMap.list_map compactFamilyVertexInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, compactFamilyInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod compactFamilyInstructionEncodedType
          compactFamilyInstructionListEncodedType)
        (fun p : X.Carrier =>
          (compactFamilyInitInstruction p.2,
            (List.range p.1).map compactFamilyVertexInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hVertexInstructions
  have hOut :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons compactFamilyInstructionEncodedType)
      hConsInput
  simpa [Function.comp, compactFamilyInstructions, compactFamilyInstructionListEncodedType, X]
    using hOut

theorem compactFamilyStep_tm_polytime :
    TMPolyTimeMap
      compactFamilyStepInputEncodedType
      compactFamilyAccEncodedType
      compactFamilyStep := by
  let X := compactFamilyStepInputEncodedType
  let A := compactFamilyAccEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X, compactFamilyStepInputEncodedType] using
      TMPolyTimeMap.fst compactFamilyAccEncodedType compactFamilyInstructionEncodedType
  have hInstr :
      TMPolyTimeMap X compactFamilyInstructionEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, compactFamilyStepInputEncodedType] using
      TMPolyTimeMap.snd compactFamilyAccEncodedType compactFamilyInstructionEncodedType
  have hSource :
      TMPolyTimeMap X codedComplementEdgeListEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst codedComplementEdgeListEncodedType setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, compactFamilyAccEncodedType, X] using hComp
  have hFamily :
      TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd codedComplementEdgeListEncodedType setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, compactFamilyAccEncodedType, X] using hComp
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool compactFamilyPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, compactFamilyInstructionEncodedType, X] using hComp
  have hPayload :
      TMPolyTimeMap X compactFamilyPayloadEncodedType (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool compactFamilyPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, compactFamilyInstructionEncodedType, X] using hComp
  have hInitEdges :
      TMPolyTimeMap X codedComplementEdgeListEncodedType (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst codedComplementEdgeListEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, compactFamilyPayloadEncodedType, X] using hComp
  have hVertex :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd codedComplementEdgeListEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, compactFamilyPayloadEncodedType, X] using hComp
  have hEmptyFamily :
      TMPolyTimeMap X setFamilyStructuredEncodedType (fun _ => ([] : List (List Nat))) :=
    TMPolyTimeMap.const X setFamilyStructuredEncodedType []
  have hInitBranch :
      TMPolyTimeMap X A (fun p : X.Carrier => (p.2.2.1, ([] : List (List Nat)))) :=
    TMPolyTimeMap.prod_mk hInitEdges hEmptyFamily
  have hPackingInput :
      TMPolyTimeMap X incidentCodeInstructionInputEncodedType
        (fun p : X.Carrier => (p.2.2.2, p.1.1)) :=
    TMPolyTimeMap.prod_mk hVertex hSource
  have hPackingSet :
      TMPolyTimeMap X setStructuredEncodedType
        (fun p : X.Carrier => compactPackingSetFromCodes p.2.2.2 p.1.1) := by
    have hComp := TMPolyTimeMap.comp compactPackingSetFromCodes_tm_polytime hPackingInput
    simpa [Function.comp, incidentCodeInstructionInputEncodedType, X] using hComp
  have hPackingSingleton :
      TMPolyTimeMap X setFamilyStructuredEncodedType
        (fun p : X.Carrier => [compactPackingSetFromCodes p.2.2.2 p.1.1]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton setStructuredEncodedType)
      hPackingSet
    simpa [Function.comp, setFamilyStructuredEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod setFamilyStructuredEncodedType setFamilyStructuredEncodedType)
        (fun p : X.Carrier =>
          ((show List (List Nat) from p.1.2),
            [compactPackingSetFromCodes p.2.2.2 p.1.1])) :=
    TMPolyTimeMap.prod_mk hFamily hPackingSingleton
  have hAppendFamily :
      TMPolyTimeMap X setFamilyStructuredEncodedType
        (fun p : X.Carrier =>
          List.append (show List (List Nat) from p.1.2)
            [compactPackingSetFromCodes p.2.2.2 p.1.1]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append setStructuredEncodedType)
      hAppendInput
    simpa [Function.comp, setFamilyStructuredEncodedType, X] using hComp
  have hVertexBranch :
      TMPolyTimeMap X A
        (fun p : X.Carrier =>
          (p.1.1, List.append (show List (List Nat) from p.1.2)
            [compactPackingSetFromCodes p.2.2.2 p.1.1])) :=
    TMPolyTimeMap.prod_mk hSource hAppendFamily
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
                  [compactPackingSetFromCodes p.2.2.2.2 p.2.1.1])
          | false => (p.2.2.2.1, ([] : List (List Nat)))) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier => (p.2.2.1, ([] : List (List Nat))))
      (fTrue := fun p : X.Carrier =>
        (p.1.1, List.append (show List (List Nat) from p.1.2)
          [compactPackingSetFromCodes p.2.2.2 p.1.1]))
      hInitBranch hVertexBranch
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨codedEdges, family⟩, ⟨tag, initEdges, v⟩⟩
  cases tag <;> rfl

/-! ### Reachable fold bounds and family runner -/

noncomputable def compactFamilySetBoundPolynomial : Polynomial Nat :=
  Polynomial.C 20 * (Polynomial.X * Polynomial.X) + Polynomial.C 100

@[simp] theorem compactFamilySetBoundPolynomial_eval (N : Nat) :
    compactFamilySetBoundPolynomial.eval N = 20 * (N * N) + 100 := by
  simp [compactFamilySetBoundPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

noncomputable def compactFamilyFoldAccBoundPolynomial : Polynomial Nat :=
  Polynomial.C 2000 * (Polynomial.X * Polynomial.X * Polynomial.X) + Polynomial.C 2000

@[simp] theorem compactFamilyFoldAccBoundPolynomial_eval (N : Nat) :
    compactFamilyFoldAccBoundPolynomial.eval N = 2000 * (N * N * N) + 2000 := by
  simp [compactFamilyFoldAccBoundPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

def compactFamilyAccBound
    (N processed : Nat) (acc : List CodedComplementEdge × List (List Nat)) : Prop :=
  codedComplementEdgeListEncodedType.inputSize acc.1 ≤ N ∧
    (∀ S ∈ acc.2, setStructuredEncodedType.inputSize S ≤
      compactFamilySetBoundPolynomial.eval N) ∧
      acc.2.length ≤ processed

theorem compactFamilyInstruction_payload_edges_inputSize_le
    {N : Nat} {instr : compactFamilyInstructionEncodedType.Carrier}
    (hInstr : compactFamilyInstructionEncodedType.inputSize instr ≤ N) :
    codedComplementEdgeListEncodedType.inputSize instr.2.1 ≤ N := by
  rcases instr with ⟨tag, codedEdges, v⟩
  change codedComplementEdgeListEncodedType.inputSize codedEdges ≤ N
  simp [compactFamilyInstructionEncodedType, compactFamilyPayloadEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_bool] at hInstr
  omega

theorem compactFamilyInstruction_vertex_inputSize_le
    {N : Nat} {instr : compactFamilyInstructionEncodedType.Carrier}
    (hInstr : compactFamilyInstructionEncodedType.inputSize instr ≤ N) :
    EncodedType.nat.inputSize instr.2.2 ≤ N := by
  rcases instr with ⟨tag, codedEdges, v⟩
  simp [compactFamilyInstructionEncodedType, compactFamilyPayloadEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_bool, EncodedType.inputSize_nat] at hInstr ⊢
  omega

theorem compactPackingSetFromCodes_inputSize_le
    {N : Nat} {codedEdges : List CodedComplementEdge} {v : Nat}
    (hEdges : codedComplementEdgeListEncodedType.inputSize codedEdges ≤ N)
    (hVertex : EncodedType.nat.inputSize v ≤ N) :
    setStructuredEncodedType.inputSize (compactPackingSetFromCodes v codedEdges) ≤
      compactFamilySetBoundPolynomial.eval N := by
  have hElem :
      ∀ x ∈ compactPackingSetFromCodes v codedEdges, EncodedType.nat.inputSize x ≤ N := by
    intro x hx
    rcases (mem_compactPackingSetFromCodes_iff codedEdges v x).1 hx with hxMarker | hxCode
    · subst x
      exact hVertex
    · rcases hxCode with ⟨ce, hMem, hCode, _hInc⟩
      subst x
      have hCe :=
        encodedList_element_inputSize_le_local
          (X := codedComplementEdgeEncodedType) (x := ce) (xs := codedEdges) hMem
      have hCeN : codedComplementEdgeEncodedType.inputSize ce ≤ N := by
        exact hCe.trans hEdges
      rcases ce with ⟨code, edge⟩
      simp [codedComplementEdgeEncodedType, vertexPairEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_nat] at hCeN ⊢
      omega
  have hList :=
    VertexCover.encodedList_inputSize_le_length_mul_bound
      EncodedType.nat (compactPackingSetFromCodes v codedEdges) N hElem
  have hLen₀ := compactPackingSetFromCodes_length_le codedEdges v
  have hLen₁ :
      codedEdges.length ≤ N := by
    have hLen := encodedList_length_le_inputSize_local codedComplementEdgeEncodedType codedEdges
    exact hLen.trans hEdges
  have hSize :
      setStructuredEncodedType.inputSize (compactPackingSetFromCodes v codedEdges) ≤
        (N + 1) * (N + 1) := by
    have hLen :
        (compactPackingSetFromCodes v codedEdges).length ≤ N + 1 := by
      omega
    exact hList.trans (Nat.mul_le_mul_right (N + 1) hLen)
  exact hSize.trans (by
    simp [compactFamilySetBoundPolynomial_eval]
    nlinarith [sq_nonneg (N : Int)])

theorem compactFamilyStep_bound {N processed : Nat}
    {acc : compactFamilyAccEncodedType.Carrier}
    {instr : compactFamilyInstructionEncodedType.Carrier}
    (hAcc : compactFamilyAccBound N processed acc)
    (_hProcessed : processed + 1 ≤ N)
    (hInstr : compactFamilyInstructionEncodedType.inputSize instr ≤ N) :
    compactFamilyAccBound N (processed + 1) (compactFamilyStep (acc, instr)) := by
  rcases acc with ⟨codedEdges, family⟩
  rcases instr with ⟨tag, initEdges, v⟩
  rcases hAcc with ⟨hEdges, hFamilyMem, hFamilyLen⟩
  cases tag
  · have hInitEdges :
        codedComplementEdgeListEncodedType.inputSize initEdges ≤ N :=
      compactFamilyInstruction_payload_edges_inputSize_le
        (N := N) (instr := (false, (initEdges, v))) hInstr
    simp [compactFamilyStep, compactFamilyAccBound]
    exact hInitEdges
  · have hVertex :
        EncodedType.nat.inputSize v ≤ N :=
      compactFamilyInstruction_vertex_inputSize_le
        (N := N) (instr := (true, (initEdges, v))) hInstr
    have hSet :=
      compactPackingSetFromCodes_inputSize_le (N := N) (codedEdges := codedEdges) (v := v)
        hEdges hVertex
    simp [compactFamilyStep, compactFamilyAccBound]
    refine ⟨hEdges, ?_, by simp [hFamilyLen]⟩
    intro S hS
    rcases hS with hOld | hNew
    · simpa using hFamilyMem S hOld
    · have hEq : S = compactPackingSetFromCodes v codedEdges := by
        simpa using hNew
      simpa [hEq] using hSet

theorem compactFamilyFold_bound_aux
    {N processed : Nat}
    (xs : List compactFamilyInstructionEncodedType.Carrier)
    (acc : compactFamilyAccEncodedType.Carrier)
    (hAcc : compactFamilyAccBound N processed acc)
    (hLen : processed + xs.length ≤ N)
    (hInstr : ∀ instr ∈ xs, compactFamilyInstructionEncodedType.inputSize instr ≤ N) :
    compactFamilyAccBound N (processed + xs.length)
      (xs.foldl (fun acc instr => compactFamilyStep (acc, instr)) acc) := by
  induction xs generalizing processed acc with
  | nil =>
      simpa using hAcc
  | cons x xs ih =>
      have hx : compactFamilyInstructionEncodedType.inputSize x ≤ N := hInstr x (by simp)
      have hStepProcessed : processed + 1 ≤ N := by
        simp only [List.length_cons] at hLen
        omega
      have hStep := compactFamilyStep_bound hAcc hStepProcessed hx
      have hTailLen : (processed + 1) + xs.length ≤ N := by
        simp only [List.length_cons] at hLen
        omega
      have hTailInstr :
          ∀ instr ∈ xs, compactFamilyInstructionEncodedType.inputSize instr ≤ N := by
        intro instr hin
        exact hInstr instr (by simp [hin])
      have hTail :=
        ih (processed := processed + 1) (acc := compactFamilyStep (acc, x))
          hStep hTailLen hTailInstr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hTail

theorem compactFamilyFold_bound_of_inputSize_le
    {N : Nat} (xs : List compactFamilyInstructionEncodedType.Carrier)
    (hSize : compactFamilyInstructionListEncodedType.inputSize xs ≤ N) :
    compactFamilyAccBound N xs.length
      (xs.foldl (fun acc instr => compactFamilyStep (acc, instr)) compactFamilyInitAcc) := by
  have hInit : compactFamilyAccBound N 0 compactFamilyInitAcc := by
    have hEmptyEdges : codedComplementEdgeListEncodedType.inputSize ([] : List CodedComplementEdge) = 0 :=
      rfl
    simp [compactFamilyAccBound, compactFamilyInitAcc, hEmptyEdges]
  have hLen : 0 + xs.length ≤ N := by
    have hLenInput :=
      encodedList_length_le_inputSize_local compactFamilyInstructionEncodedType xs
    have hLenInput' : xs.length ≤ compactFamilyInstructionListEncodedType.inputSize xs := by
      simpa [compactFamilyInstructionListEncodedType] using hLenInput
    omega
  have hInstr :
      ∀ instr ∈ xs, compactFamilyInstructionEncodedType.inputSize instr ≤ N := by
    intro instr hin
    have hElem :=
      encodedList_element_inputSize_le_local
        (X := compactFamilyInstructionEncodedType) (x := instr) (xs := xs) hin
    have hElem' : compactFamilyInstructionEncodedType.inputSize instr ≤
        compactFamilyInstructionListEncodedType.inputSize xs := by
      simpa [compactFamilyInstructionListEncodedType] using hElem
    omega
  have h :=
    compactFamilyFold_bound_aux (N := N) (processed := 0) xs compactFamilyInitAcc
      hInit hLen hInstr
  simpa using h

theorem compactFamilyAccBound_inputSize_le {N processed : Nat}
    {acc : compactFamilyAccEncodedType.Carrier}
    (hAcc : compactFamilyAccBound N processed acc)
    (hProcessed : processed ≤ N) :
    compactFamilyAccEncodedType.inputSize acc ≤
      compactFamilyFoldAccBoundPolynomial.eval N := by
  rcases acc with ⟨codedEdges, family⟩
  rcases hAcc with ⟨hEdges, hFamilyMem, hFamilyLen⟩
  let Bset := compactFamilySetBoundPolynomial.eval N
  have hFamilySize :
      setFamilyStructuredEncodedType.inputSize family ≤ processed * (Bset + 1) := by
    have hList :=
      VertexCover.encodedList_inputSize_le_length_mul_bound
        setStructuredEncodedType family Bset (by
          intro S hS
          exact hFamilyMem S hS)
    exact hList.trans (Nat.mul_le_mul_right (Bset + 1) hFamilyLen)
  have hFamilySizeN :
      setFamilyStructuredEncodedType.inputSize family ≤ N * (Bset + 1) :=
    hFamilySize.trans (Nat.mul_le_mul_right (Bset + 1) hProcessed)
  simp [compactFamilyAccEncodedType, EncodedType.inputSize_prod]
  have hBset : Bset = 20 * (N * N) + 100 := by
    simp [Bset]
  nlinarith [sq_nonneg (N : Int), hEdges, hFamilySizeN]

noncomputable def compactFamilyFoldTimePolynomial
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod compactFamilyAccEncodedType
          compactFamilyInstructionEncodedType).encode
        compactFamilyAccEncodedType.encode
        compactFamilyStep) : Polynomial Nat :=
  TM2Programs.listFoldBoundedTimePolynomial hStep.tm compactFamilyFoldAccBoundPolynomial
    (hStep.time.comp
      (compactFamilyFoldAccBoundPolynomial + Polynomial.X + Polynomial.C 5))

theorem compactFamilyFold_tm_polytime :
    TMPolyTimeMap
      compactFamilyInstructionListEncodedType
      compactFamilyAccEncodedType
      (fun xs : List compactFamilyInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => compactFamilyStep (acc, instr)) compactFamilyInitAcc) := by
  rcases compactFamilyStep_tm_polytime with ⟨hStep⟩
  let time := compactFamilyFoldTimePolynomial hStep
  refine
    TMPolyTimeMap.list_foldl_typed
      compactFamilyInstructionEncodedType compactFamilyAccEncodedType
      compactFamilyStep compactFamilyInitAcc hStep time ?_
  intro source
  let N := compactFamilyInstructionListEncodedType.inputSize source
  let B := compactFamilyFoldAccBoundPolynomial.eval N
  let T := hStep.time.eval (B + N + 5)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hLoopAux :
      ∀ (pref rest : List compactFamilyInstructionEncodedType.Carrier),
        source = pref ++ rest →
          TM2Programs.listFoldTypedLoopTime
              compactFamilyInstructionEncodedType compactFamilyAccEncodedType
              compactFamilyStep hStep
              (pref.foldl (fun acc instr => compactFamilyStep (acc, instr)) compactFamilyInitAcc)
              rest ≤
            C * (EncodedType.list compactFamilyInstructionEncodedType).inputSize rest := by
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
        have hxN : compactFamilyInstructionEncodedType.inputSize x ≤ N := by
          have hElem :=
            encodedList_element_inputSize_le_local
              (X := compactFamilyInstructionEncodedType) (x := x) (xs := source)
              hxMemSource
          simpa [N, compactFamilyInstructionListEncodedType] using hElem
        have hPrefixSize : compactFamilyInstructionListEncodedType.inputSize pref ≤ N := by
          have hEqSize :
              compactFamilyInstructionListEncodedType.inputSize source =
                compactFamilyInstructionListEncodedType.inputSize pref +
                  compactFamilyInstructionListEncodedType.inputSize (x :: xs) := by
            rw [hEq]
            exact encodedList_inputSize_append_local compactFamilyInstructionEncodedType
              pref (x :: xs)
          omega
        have hPrefixBound :=
          compactFamilyFold_bound_of_inputSize_le (N := N) pref hPrefixSize
        have hPrefixLenN : pref.length ≤ N := by
          have hLen :=
            encodedList_length_le_inputSize_local compactFamilyInstructionEncodedType pref
          have hLen' :
              pref.length ≤ compactFamilyInstructionListEncodedType.inputSize pref := by
            simpa [compactFamilyInstructionListEncodedType] using hLen
          omega
        have hAccSize :
            compactFamilyAccEncodedType.inputSize
                (pref.foldl (fun acc instr => compactFamilyStep (acc, instr))
                  compactFamilyInitAcc) ≤ B := by
          simpa [B] using
            compactFamilyAccBound_inputSize_le hPrefixBound hPrefixLenN
        have hStepProcessed : pref.length + 1 ≤ N := by
          have hLenEq : source.length = pref.length + (x :: xs).length := by
            rw [hEq, List.length_append]
          simp only [List.length_cons] at hLenEq
          have hSourceLenN : source.length ≤ N := by
            have hLen :=
              encodedList_length_le_inputSize_local compactFamilyInstructionEncodedType source
            simpa [N, compactFamilyInstructionListEncodedType] using hLen
          omega
        have hStepBound :=
          compactFamilyStep_bound hPrefixBound hStepProcessed hxN
        have hStepSize :
            compactFamilyAccEncodedType.inputSize
                (compactFamilyStep
                  (pref.foldl (fun acc instr => compactFamilyStep (acc, instr))
                    compactFamilyInitAcc, x)) ≤ B := by
          simpa [B] using
            compactFamilyAccBound_inputSize_le hStepBound hStepProcessed
        have hStepTime :
            hStep.time.eval
                ((EncodedType.prod compactFamilyAccEncodedType
                  compactFamilyInstructionEncodedType).inputSize
                  (pref.foldl (fun acc instr => compactFamilyStep (acc, instr))
                    compactFamilyInitAcc, x)) ≤ T := by
          have hArg :
              (EncodedType.prod compactFamilyAccEncodedType
                compactFamilyInstructionEncodedType).inputSize
                  (pref.foldl (fun acc instr => compactFamilyStep (acc, instr))
                    compactFamilyInitAcc, x) ≤ B + N + 5 := by
            rw [EncodedType.inputSize_prod]
            change
              compactFamilyAccEncodedType.inputSize
                    (pref.foldl (fun acc instr => compactFamilyStep (acc, instr))
                      compactFamilyInitAcc) +
                  1 + compactFamilyInstructionEncodedType.inputSize x ≤ B + N + 5
            omega
          exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
        have hBlock :
            TM2Programs.listFoldBlockTime hStep.tm
                (compactFamilyInstructionEncodedType.encode x).length
                (compactFamilyAccEncodedType.encode
                  (pref.foldl (fun acc instr => compactFamilyStep (acc, instr))
                    compactFamilyInitAcc)).length
                (compactFamilyAccEncodedType.encode
                  (compactFamilyStep
                    (pref.foldl (fun acc instr => compactFamilyStep (acc, instr))
                      compactFamilyInitAcc, x))).length
                (hStep.time.eval
                  ((EncodedType.prod compactFamilyAccEncodedType
                    compactFamilyInstructionEncodedType).inputSize
                    (pref.foldl (fun acc instr => compactFamilyStep (acc, instr))
                      compactFamilyInitAcc, x))) ≤
              C * (compactFamilyInstructionEncodedType.inputSize x + 1) := by
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
                compactFamilyInstructionEncodedType compactFamilyAccEncodedType
                compactFamilyStep hStep
                (compactFamilyStep
                  (pref.foldl (fun acc instr => compactFamilyStep (acc, instr))
                    compactFamilyInitAcc, x)) xs ≤
              C * (EncodedType.list compactFamilyInstructionEncodedType).inputSize xs := by
          have hFoldPref :
              (pref ++ [x]).foldl
                  (fun acc instr => compactFamilyStep (acc, instr)) compactFamilyInitAcc =
                compactFamilyStep
                  (pref.foldl (fun acc instr => compactFamilyStep (acc, instr))
                    compactFamilyInitAcc, x) := by
            exact
              List.foldl_concat
                (fun acc instr => compactFamilyStep (acc, instr)) compactFamilyInitAcc x pref
          convert hTailRaw using 1
          exact congrArg
            (fun acc =>
              TM2Programs.listFoldTypedLoopTime
                compactFamilyInstructionEncodedType compactFamilyAccEncodedType
                compactFamilyStep hStep acc xs)
            hFoldPref.symm
        calc
          TM2Programs.listFoldTypedLoopTime
              compactFamilyInstructionEncodedType compactFamilyAccEncodedType
              compactFamilyStep hStep
              (pref.foldl (fun acc instr => compactFamilyStep (acc, instr)) compactFamilyInitAcc)
              (x :: xs)
              =
            TM2Programs.listFoldTypedLoopTime
                compactFamilyInstructionEncodedType compactFamilyAccEncodedType
                compactFamilyStep hStep
                (compactFamilyStep
                  (pref.foldl (fun acc instr => compactFamilyStep (acc, instr))
                    compactFamilyInitAcc, x)) xs +
              TM2Programs.listFoldBlockTime hStep.tm
                (compactFamilyInstructionEncodedType.encode x).length
                (compactFamilyAccEncodedType.encode
                  (pref.foldl (fun acc instr => compactFamilyStep (acc, instr))
                    compactFamilyInitAcc)).length
                (compactFamilyAccEncodedType.encode
                  (compactFamilyStep
                    (pref.foldl (fun acc instr => compactFamilyStep (acc, instr))
                      compactFamilyInitAcc, x))).length
                (hStep.time.eval
                  ((EncodedType.prod compactFamilyAccEncodedType
                    compactFamilyInstructionEncodedType).inputSize
                    (pref.foldl (fun acc instr => compactFamilyStep (acc, instr))
                      compactFamilyInitAcc, x))) := by
                rfl
          _ ≤
              C * (EncodedType.list compactFamilyInstructionEncodedType).inputSize xs +
                C * (compactFamilyInstructionEncodedType.inputSize x + 1) :=
                Nat.add_le_add hTail hBlock
          _ ≤ C * (EncodedType.list compactFamilyInstructionEncodedType).inputSize (x :: xs) := by
                rw [EncodedType.inputSize_list_cons]
                nlinarith
  have hLoop :
      TM2Programs.listFoldTypedLoopTime
          compactFamilyInstructionEncodedType compactFamilyAccEncodedType
          compactFamilyStep hStep compactFamilyInitAcc source ≤ C * N := by
    have h := hLoopAux [] source (by simp)
    simpa [N, compactFamilyInstructionListEncodedType] using h
  have hTimeEval : time.eval N = (C + 2) * (N + 1) := by
    simp [time, compactFamilyFoldTimePolynomial, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval, TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_comp]
  change 2 +
      TM2Programs.listFoldTypedLoopTime
        compactFamilyInstructionEncodedType compactFamilyAccEncodedType
        compactFamilyStep hStep compactFamilyInitAcc source ≤ time.eval N
  rw [hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

theorem compactFamilyFromInstructions_tm_polytime :
    TMPolyTimeMap
      compactFamilyInstructionListEncodedType
      setFamilyStructuredEncodedType
      compactFamilyFromInstructions := by
  have hFold := compactFamilyFold_tm_polytime
  have hSnd := TMPolyTimeMap.snd codedComplementEdgeListEncodedType setFamilyStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, compactFamilyFromInstructions, compactFamilyAccEncodedType]
    using hComp

theorem compactFamilyFromInput_tm_polytime :
    TMPolyTimeMap
      compactFamilyInstructionInputEncodedType
      setFamilyStructuredEncodedType
      compactFamilyFromInput := by
  have hComp :=
    TMPolyTimeMap.comp compactFamilyFromInstructions_tm_polytime
      compactFamilyInstructions_tm_polytime
  simpa [Function.comp, compactFamilyFromInput] using hComp

end SetPacking
end Karp21
end ComplexityReduction
