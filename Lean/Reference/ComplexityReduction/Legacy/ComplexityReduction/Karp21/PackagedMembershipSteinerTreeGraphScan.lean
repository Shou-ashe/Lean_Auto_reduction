/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSteinerTreeTerminal

/-!
Universal scans over weighted edge lists for the faithful structured Steiner
Tree verifier.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace SteinerTreeMembership

def weightedAllInGraphInstructionEncodedType : EncodedType :=
  EncodedType.sum weightedEdgeListStructuredEncodedType weightedEdgeStructuredEncodedType

def weightedAllInGraphInstructionListEncodedType : EncodedType :=
  EncodedType.list weightedAllInGraphInstructionEncodedType

def weightedAllInGraphInputEncodedType : EncodedType :=
  EncodedType.prod weightedEdgeListStructuredEncodedType weightedEdgeListStructuredEncodedType

def weightedAllInGraphAccEncodedType : EncodedType :=
  EncodedType.prod weightedEdgeListStructuredEncodedType EncodedType.bool

abbrev WeightedAllInGraphAcc :=
  List (Nat × Nat × Nat) × Bool

def weightedAllInGraphInitInstruction
    (edges : List (Nat × Nat × Nat)) : weightedAllInGraphInstructionEncodedType.Carrier :=
  Sum.inl edges

def weightedAllInGraphElementInstruction
    (e : Nat × Nat × Nat) : weightedAllInGraphInstructionEncodedType.Carrier :=
  Sum.inr e

def weightedAllInGraphInstructions
    (p : List (Nat × Nat × Nat) × List (Nat × Nat × Nat)) :
    List weightedAllInGraphInstructionEncodedType.Carrier :=
  weightedAllInGraphInitInstruction p.1 :: p.2.map weightedAllInGraphElementInstruction

def weightedAllInGraphRunnerInit : weightedAllInGraphAccEncodedType.Carrier :=
  (([] : List (Nat × Nat × Nat)), false)

def weightedAllInGraphStep
    (p : weightedAllInGraphAccEncodedType.Carrier ×
      weightedAllInGraphInstructionEncodedType.Carrier) :
    weightedAllInGraphAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl edges => (edges, true)
  | Sum.inr e => (p.1.1, graphBoolAndPair (p.1.2, weightedEdgeInListBool (e, p.1.1)))

def weightedAllInGraphFromInstructions
    (xs : List weightedAllInGraphInstructionEncodedType.Carrier) : Bool :=
  (xs.foldl (fun acc instr => weightedAllInGraphStep (acc, instr))
    weightedAllInGraphRunnerInit).2

def weightedAllInGraphBool
    (p : List (Nat × Nat × Nat) × List (Nat × Nat × Nat)) : Bool :=
  weightedAllInGraphFromInstructions (weightedAllInGraphInstructions p)

theorem weightedAllInGraphElementInstructions_fold_eq_true_iff
    (selected edges : List (Nat × Nat × Nat)) (ok : Bool) :
    ((selected.map weightedAllInGraphElementInstruction).foldl
        (fun acc instr => weightedAllInGraphStep (acc, instr)) (edges, ok)).2 = true ↔
      ok = true ∧ ∀ e ∈ selected, weightedEdgeInListBool (e, edges) = true := by
  induction selected generalizing ok with
  | nil =>
      cases ok <;> simp
  | cons e rest ih =>
      rw [List.map_cons, List.foldl_cons]
      change
        ((rest.map weightedAllInGraphElementInstruction).foldl
            (fun acc instr => weightedAllInGraphStep (acc, instr))
            (edges, graphBoolAndPair (ok, weightedEdgeInListBool (e, edges)))).2 = true ↔
          ok = true ∧ ∀ f ∈ e :: rest, weightedEdgeInListBool (f, edges) = true
      rw [ih]
      constructor
      · rintro ⟨hHead, hTail⟩
        rcases (graphBoolAndPair_eq_true_iff (ok, weightedEdgeInListBool (e, edges))).1
            hHead with
          ⟨hok, heBool⟩
        refine ⟨hok, ?_⟩
        intro f hf
        rcases List.mem_cons.mp hf with hfe | hfRest
        · subst f
          exact heBool
        · exact hTail f hfRest
      · rintro ⟨hok, hAll⟩
        refine ⟨?_, ?_⟩
        · exact (graphBoolAndPair_eq_true_iff (ok, weightedEdgeInListBool (e, edges))).2
            ⟨hok, hAll e (by simp)⟩
        · intro f hf
          exact hAll f (List.mem_cons_of_mem e hf)

theorem weightedAllInGraphBool_eq_true_iff
    (p : List (Nat × Nat × Nat) × List (Nat × Nat × Nat)) :
    weightedAllInGraphBool p = true ↔ ∀ e ∈ p.2, e ∈ p.1 := by
  rcases p with ⟨edges, selected⟩
  change
    (((weightedAllInGraphInitInstruction edges ::
          selected.map weightedAllInGraphElementInstruction).foldl
        (fun acc instr => weightedAllInGraphStep (acc, instr))
        weightedAllInGraphRunnerInit).2 = true) ↔
      ∀ e ∈ selected, e ∈ edges
  rw [List.foldl_cons]
  change
    (((selected.map weightedAllInGraphElementInstruction).foldl
        (fun acc instr => weightedAllInGraphStep (acc, instr)) (edges, true)).2 = true) ↔
      ∀ e ∈ selected, e ∈ edges
  rw [weightedAllInGraphElementInstructions_fold_eq_true_iff selected edges true]
  simp [weightedEdgeInListBool_eq_true_iff]

theorem weightedAllInGraphInitInstruction_tm_polytime :
    TMPolyTimeMap weightedEdgeListStructuredEncodedType
      weightedAllInGraphInstructionEncodedType
      weightedAllInGraphInitInstruction := by
  simpa [weightedAllInGraphInitInstruction, weightedAllInGraphInstructionEncodedType] using
    TMPolyTimeMap.inl weightedEdgeListStructuredEncodedType weightedEdgeStructuredEncodedType

theorem weightedAllInGraphElementInstruction_tm_polytime :
    TMPolyTimeMap weightedEdgeStructuredEncodedType
      weightedAllInGraphInstructionEncodedType
      weightedAllInGraphElementInstruction := by
  simpa [weightedAllInGraphElementInstruction, weightedAllInGraphInstructionEncodedType] using
    TMPolyTimeMap.inr weightedEdgeListStructuredEncodedType weightedEdgeStructuredEncodedType

theorem weightedAllInGraphInstructions_tm_polytime :
    TMPolyTimeMap weightedAllInGraphInputEncodedType
      weightedAllInGraphInstructionListEncodedType
      weightedAllInGraphInstructions := by
  let X := weightedAllInGraphInputEncodedType
  have hEdges : TMPolyTimeMap X weightedEdgeListStructuredEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X, weightedAllInGraphInputEncodedType] using
      TMPolyTimeMap.fst weightedEdgeListStructuredEncodedType weightedEdgeListStructuredEncodedType
  have hSelected : TMPolyTimeMap X weightedEdgeListStructuredEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X, weightedAllInGraphInputEncodedType] using
      TMPolyTimeMap.snd weightedEdgeListStructuredEncodedType weightedEdgeListStructuredEncodedType
  have hInit :
      TMPolyTimeMap X weightedAllInGraphInstructionEncodedType
        (fun p : X.Carrier => weightedAllInGraphInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp weightedAllInGraphInitInstruction_tm_polytime hEdges
    simpa [Function.comp, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X weightedAllInGraphInstructionListEncodedType
        (fun p : X.Carrier => [weightedAllInGraphInitInstruction p.1]) := by
    have hComp :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.list_singleton weightedAllInGraphInstructionEncodedType) hInit
    simpa [Function.comp, weightedAllInGraphInstructionListEncodedType, X] using hComp
  have hElementInstructions :
      TMPolyTimeMap X weightedAllInGraphInstructionListEncodedType
        (fun p : X.Carrier => p.2.map weightedAllInGraphElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map weightedAllInGraphElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hSelected
    simpa [Function.comp, weightedAllInGraphInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod weightedAllInGraphInstructionListEncodedType
          weightedAllInGraphInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([weightedAllInGraphInitInstruction p.1],
            p.2.map weightedAllInGraphElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hElementInstructions
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append weightedAllInGraphInstructionEncodedType) hAppendInput
  simpa [Function.comp, weightedAllInGraphInstructions,
    weightedAllInGraphInstructionListEncodedType, X] using hOut

theorem weightedAllInGraphStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod weightedAllInGraphAccEncodedType
        weightedAllInGraphInstructionEncodedType)
      weightedAllInGraphAccEncodedType
      weightedAllInGraphStep := by
  let A := weightedAllInGraphAccEncodedType
  let E := weightedEdgeListStructuredEncodedType
  let W := weightedEdgeStructuredEncodedType
  let Instr := weightedAllInGraphInstructionEncodedType
  have hLeft : TMPolyTimeMap E A (fun edges : E.Carrier => (edges, true)) := by
    have hId : TMPolyTimeMap E E id := TMPolyTimeMap.id E
    have hTrue : TMPolyTimeMap E EncodedType.bool (fun _ : E.Carrier => true) :=
      TMPolyTimeMap.const E EncodedType.bool true
    have hOut := TMPolyTimeMap.prod_mk hId hTrue
    simpa [A, E, weightedAllInGraphAccEncodedType] using hOut
  have hRight : TMPolyTimeMap (EncodedType.prod A W) A
      (fun p : A.Carrier × W.Carrier =>
        (p.1.1, graphBoolAndPair (p.1.2, weightedEdgeInListBool (p.2, p.1.1)))) := by
    let X := EncodedType.prod A W
    have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
      simpa [X] using TMPolyTimeMap.fst A W
    have hEdges : TMPolyTimeMap X E (fun p : X.Carrier => p.1.1) := by
      have hFst := TMPolyTimeMap.fst E EncodedType.bool
      have hComp := TMPolyTimeMap.comp hFst hAcc
      simpa [Function.comp, A, E, weightedAllInGraphAccEncodedType, X] using hComp
    have hOk : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2) := by
      have hSnd := TMPolyTimeMap.snd E EncodedType.bool
      have hComp := TMPolyTimeMap.comp hSnd hAcc
      simpa [Function.comp, A, E, weightedAllInGraphAccEncodedType, X] using hComp
    have hEdge : TMPolyTimeMap X W (fun p : X.Carrier => p.2) := by
      simpa [X] using TMPolyTimeMap.snd A W
    have hCheckInput :
        TMPolyTimeMap X (EncodedType.prod W E) (fun p : X.Carrier => (p.2, p.1.1)) :=
      TMPolyTimeMap.prod_mk hEdge hEdges
    have hCheck : TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => weightedEdgeInListBool (p.2, p.1.1)) := by
      have hComp := TMPolyTimeMap.comp weightedEdgeInListBool_tm_polytime hCheckInput
      simpa [Function.comp, X] using hComp
    have hAndInput :
        TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
          (fun p : X.Carrier => (p.1.2, weightedEdgeInListBool (p.2, p.1.1))) :=
      TMPolyTimeMap.prod_mk hOk hCheck
    have hAnd : TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier =>
          graphBoolAndPair (p.1.2, weightedEdgeInListBool (p.2, p.1.1))) := by
      have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
      simpa [Function.comp, X] using hComp
    have hOut := TMPolyTimeMap.prod_mk hEdges hAnd
    simpa [X, A, E, W, weightedAllInGraphAccEncodedType] using hOut
  have hChoice := Partition.prodSumChoice_tm_polytime A E W
  have hBranches := Partition.TMPolyTimeMap.sum_elim hLeft hRight
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem weightedAllInGraphStep_inputSize_le
    (K : Nat) (hK : 10 ≤ K)
    (source : weightedAllInGraphInstructionListEncodedType.Carrier)
    (acc : weightedAllInGraphAccEncodedType.Carrier)
    (instr : weightedAllInGraphInstructionEncodedType.Carrier)
    (hAcc :
      weightedAllInGraphAccEncodedType.inputSize acc ≤
        weightedAllInGraphInstructionListEncodedType.inputSize source + K)
    (hInstr :
      weightedAllInGraphInstructionEncodedType.inputSize instr ≤
        weightedAllInGraphInstructionListEncodedType.inputSize source) :
    weightedAllInGraphAccEncodedType.inputSize (weightedAllInGraphStep (acc, instr)) ≤
      weightedAllInGraphInstructionListEncodedType.inputSize source + K := by
  rcases acc with ⟨edges, ok⟩
  cases instr with
  | inl newEdges =>
      have hLocal :
          weightedAllInGraphAccEncodedType.inputSize (newEdges, true) ≤
            weightedAllInGraphInstructionEncodedType.inputSize (Sum.inl newEdges) + 10 := by
        simp [weightedAllInGraphAccEncodedType, weightedAllInGraphInstructionEncodedType,
          EncodedType.inputSize, EncodedType.prod, EncodedType.sum, EncodedType.bool]
      have hSource :
          weightedAllInGraphInstructionEncodedType.inputSize (Sum.inl newEdges) + 10 ≤
            weightedAllInGraphInstructionListEncodedType.inputSize source + K := by
        omega
      exact hLocal.trans hSource
  | inr e =>
      have hLocal :
          weightedAllInGraphAccEncodedType.inputSize
              (edges, graphBoolAndPair (ok, weightedEdgeInListBool (e, edges))) ≤
            weightedAllInGraphAccEncodedType.inputSize (edges, ok) := by
        cases ok <;> cases weightedEdgeInListBool (e, edges) <;>
          simp [weightedAllInGraphAccEncodedType, EncodedType.inputSize,
            EncodedType.prod, EncodedType.bool, graphBoolAndPair]
      exact hLocal.trans hAcc

theorem weightedAllInGraphFold_tm_polytime :
    TMPolyTimeMap
      weightedAllInGraphInstructionListEncodedType
      weightedAllInGraphAccEncodedType
      (fun xs : weightedAllInGraphInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc instr => weightedAllInGraphStep (acc, instr))
          weightedAllInGraphRunnerInit) := by
  rcases weightedAllInGraphStep_tm_polytime with ⟨hStep⟩
  let K : Nat := weightedAllInGraphAccEncodedType.inputSize weightedAllInGraphRunnerInit + 10
  let bound : Polynomial Nat := Polynomial.X + Polynomial.C K
  refine
    TMPolyTimeMap.list_foldl_typed_bounded
      weightedAllInGraphInstructionEncodedType
      weightedAllInGraphAccEncodedType
      weightedAllInGraphStep weightedAllInGraphRunnerInit hStep bound ?_ ?_
  · intro xs
    change weightedAllInGraphAccEncodedType.inputSize weightedAllInGraphRunnerInit ≤
      (Polynomial.X + Polynomial.C K).eval
        (weightedAllInGraphInstructionEncodedType.list.inputSize xs)
    simp [Polynomial.eval_add]
    omega
  · intro source acc instr hAcc hInstr
    have hAcc' :
        weightedAllInGraphAccEncodedType.inputSize acc ≤
          weightedAllInGraphInstructionListEncodedType.inputSize source + K := by
      simpa [weightedAllInGraphInstructionListEncodedType, bound, Polynomial.eval_add] using hAcc
    have hInstr' :
        weightedAllInGraphInstructionEncodedType.inputSize instr ≤
          weightedAllInGraphInstructionListEncodedType.inputSize source := by
      simpa [weightedAllInGraphInstructionListEncodedType] using hInstr
    simpa [weightedAllInGraphInstructionListEncodedType, bound, Polynomial.eval_add] using
      weightedAllInGraphStep_inputSize_le K (by omega) source acc instr hAcc' hInstr'

theorem weightedAllInGraphFromInstructions_tm_polytime :
    TMPolyTimeMap weightedAllInGraphInstructionListEncodedType EncodedType.bool
      weightedAllInGraphFromInstructions := by
  have hFold := weightedAllInGraphFold_tm_polytime
  have hOut := TMPolyTimeMap.snd weightedEdgeListStructuredEncodedType EncodedType.bool
  have hComp := TMPolyTimeMap.comp hOut hFold
  simpa [Function.comp, weightedAllInGraphFromInstructions, weightedAllInGraphAccEncodedType]
    using hComp

theorem weightedAllInGraphBool_tm_polytime :
    TMPolyTimeMap weightedAllInGraphInputEncodedType EncodedType.bool
      weightedAllInGraphBool := by
  have hComp := TMPolyTimeMap.comp
    weightedAllInGraphFromInstructions_tm_polytime
    weightedAllInGraphInstructions_tm_polytime
  simpa [Function.comp, weightedAllInGraphBool] using hComp

end SteinerTreeMembership

end Karp21
end ComplexityReduction
