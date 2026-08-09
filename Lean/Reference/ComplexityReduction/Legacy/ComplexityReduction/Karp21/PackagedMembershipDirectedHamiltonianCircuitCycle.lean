/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuit
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipDirectedHamiltonianCircuitEdge
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetSystem

/-!
Direct standard-TM Boolean runners for Directed Hamiltonian Circuit
certificates: all-vertex coverage and ordered cyclic edge checks.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace DirectedHamiltonianCircuitMembership

/-! ### Every graph vertex appears in the certificate -/

def allVerticesInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool
    (EncodedType.prod setStructuredEncodedType EncodedType.nat)

def allVerticesInstructionListEncodedType : EncodedType :=
  EncodedType.list allVerticesInstructionEncodedType

def allVerticesInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat setStructuredEncodedType

def allVerticesAccEncodedType : EncodedType :=
  EncodedType.prod setStructuredEncodedType EncodedType.bool

def allVerticesInitInstruction (cycle : List Nat) : Bool × (List Nat × Nat) :=
  (false, (cycle, (0 : Nat)))

def allVerticesElementInstruction (v : Nat) : Bool × (List Nat × Nat) :=
  (true, ([], v))

def allVerticesInstructions (p : Nat × List Nat) :
    List (Bool × (List Nat × Nat)) :=
  allVerticesInitInstruction p.2 ::
    (List.range p.1).map allVerticesElementInstruction

def allVerticesRunnerInit : List Nat × Bool :=
  ([], true)

def allVerticesStep
    (p : (List Nat × Bool) × (Bool × (List Nat × Nat))) : List Nat × Bool :=
  if p.2.1 then
    (p.1.1, graphBoolAndPair (p.1.2, HittingSet.setContainsBool (p.2.2.2, p.1.1)))
  else
    (p.2.2.1, true)

def allVerticesFromInstructions (xs : List (Bool × (List Nat × Nat))) : Bool :=
  (xs.foldl (fun acc instr => allVerticesStep (acc, instr)) allVerticesRunnerInit).2

def allVerticesInCycleBool (p : Nat × List Nat) : Bool :=
  allVerticesFromInstructions (allVerticesInstructions p)

theorem allVerticesElementInstructions_fold_eq_true_iff
    (vertices cycle : List Nat) (ok : Bool) :
    ((vertices.map allVerticesElementInstruction).foldl
        (fun acc instr => allVerticesStep (acc, instr)) (cycle, ok)).2 = true ↔
      ok = true ∧ ∀ v ∈ vertices, v ∈ cycle := by
  induction vertices generalizing ok with
  | nil =>
      cases ok <;> simp
  | cons v rest ih =>
      rw [List.map_cons, List.foldl_cons]
      change
        ((rest.map allVerticesElementInstruction).foldl
            (fun acc instr => allVerticesStep (acc, instr))
            (cycle, graphBoolAndPair
              (ok, HittingSet.setContainsBool (v, cycle)))).2 = true ↔
          ok = true ∧ ∀ x ∈ v :: rest, x ∈ cycle
      rw [ih]
      constructor
      · rintro ⟨hHead, hTail⟩
        rcases (graphBoolAndPair_eq_true_iff
            (ok, HittingSet.setContainsBool (v, cycle))).1 hHead with
          ⟨hok, hvBool⟩
        refine ⟨hok, ?_⟩
        intro x hx
        simp at hx
        rcases hx with hx | hx
        · subst x
          exact (HittingSet.setContainsBool_eq_true_iff (v, cycle)).1 hvBool
        · exact hTail x hx
      · rintro ⟨hok, hAll⟩
        refine ⟨?_, ?_⟩
        · exact (graphBoolAndPair_eq_true_iff
            (ok, HittingSet.setContainsBool (v, cycle))).2
            ⟨hok, (HittingSet.setContainsBool_eq_true_iff (v, cycle)).2
              (hAll v (by simp))⟩
        · intro x hx
          exact hAll x (List.mem_cons_of_mem v hx)

theorem allVerticesInCycleBool_eq_true_iff (n : Nat) (cycle : List Nat) :
    allVerticesInCycleBool (n, cycle) = true ↔
      ∀ v, v < n → v ∈ cycle := by
  change
    (((allVerticesInitInstruction cycle ::
      (List.range n).map allVerticesElementInstruction).foldl
        (fun acc instr => allVerticesStep (acc, instr))
        allVerticesRunnerInit).2 = true) ↔ _
  rw [List.foldl_cons]
  have hFold := allVerticesElementInstructions_fold_eq_true_iff
    (List.range n) cycle true
  constructor
  · intro h v hv
    exact hFold.1 h |>.2 v (by simpa using hv)
  · intro h
    apply hFold.2
    refine ⟨rfl, ?_⟩
    intro v hv
    exact h v (by simpa using hv)

theorem allVerticesInitInstruction_tm_polytime :
    TMPolyTimeMap setStructuredEncodedType allVerticesInstructionEncodedType
      allVerticesInitInstruction := by
  have hFalse : TMPolyTimeMap setStructuredEncodedType EncodedType.bool (fun _ => false) :=
    TMPolyTimeMap.const setStructuredEncodedType EncodedType.bool false
  have hCycle : TMPolyTimeMap setStructuredEncodedType setStructuredEncodedType id :=
    TMPolyTimeMap.id setStructuredEncodedType
  have hZero : TMPolyTimeMap setStructuredEncodedType EncodedType.nat (fun _ => (0 : Nat)) :=
    TMPolyTimeMap.const setStructuredEncodedType EncodedType.nat (0 : Nat)
  have hPayload :
      TMPolyTimeMap setStructuredEncodedType
        (EncodedType.prod setStructuredEncodedType EncodedType.nat)
        (fun cycle : List Nat => (cycle, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hCycle hZero
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [allVerticesInitInstruction, allVerticesInstructionEncodedType] using hOut

theorem allVerticesElementInstruction_tm_polytime :
    TMPolyTimeMap EncodedType.nat allVerticesInstructionEncodedType
      allVerticesElementInstruction := by
  have hTrue : TMPolyTimeMap EncodedType.nat EncodedType.bool (fun _ => true) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool true
  have hEmpty : TMPolyTimeMap EncodedType.nat setStructuredEncodedType
      (fun _ => ([] : List Nat)) :=
    TMPolyTimeMap.const EncodedType.nat setStructuredEncodedType []
  have hNat : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  have hPayload :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.prod setStructuredEncodedType EncodedType.nat)
        (fun v : Nat => (([] : List Nat), v)) :=
    TMPolyTimeMap.prod_mk hEmpty hNat
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [allVerticesElementInstruction, allVerticesInstructionEncodedType] using hOut

theorem allVerticesInstructions_tm_polytime :
    TMPolyTimeMap allVerticesInputEncodedType allVerticesInstructionListEncodedType
      allVerticesInstructions := by
  let X := allVerticesInputEncodedType
  have hN : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, allVerticesInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat setStructuredEncodedType
  have hCycle : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, allVerticesInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat setStructuredEncodedType
  have hInit :
      TMPolyTimeMap X allVerticesInstructionEncodedType
        (fun p : X.Carrier => allVerticesInitInstruction p.2) := by
    have hComp := TMPolyTimeMap.comp allVerticesInitInstruction_tm_polytime hCycle
    simpa [Function.comp, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X allVerticesInstructionListEncodedType
        (fun p : X.Carrier => [allVerticesInitInstruction p.2]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton allVerticesInstructionEncodedType) hInit
    simpa [Function.comp, allVerticesInstructionListEncodedType, X] using hComp
  have hRange : TMPolyTimeMap X setStructuredEncodedType
      (fun p : X.Carrier => List.range p.1) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hN
    simpa [Function.comp, setStructuredEncodedType, X] using hComp
  have hElements :
      TMPolyTimeMap X allVerticesInstructionListEncodedType
        (fun p : X.Carrier => (List.range p.1).map allVerticesElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map allVerticesElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, allVerticesInstructionListEncodedType, setStructuredEncodedType, X]
      using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod allVerticesInstructionListEncodedType
          allVerticesInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([allVerticesInitInstruction p.2],
            (List.range p.1).map allVerticesElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hElements
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append allVerticesInstructionEncodedType) hAppendInput
  simpa [Function.comp, allVerticesInstructions, allVerticesInstructionListEncodedType, X]
    using hOut

theorem allVerticesStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod allVerticesAccEncodedType allVerticesInstructionEncodedType)
      allVerticesAccEncodedType
      allVerticesStep := by
  let X := EncodedType.prod allVerticesAccEncodedType allVerticesInstructionEncodedType
  let Payload := EncodedType.prod setStructuredEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X allVerticesAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst allVerticesAccEncodedType allVerticesInstructionEncodedType
  have hInstr : TMPolyTimeMap X allVerticesInstructionEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd allVerticesAccEncodedType allVerticesInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, allVerticesInstructionEncodedType, Payload, X] using hComp
  have hPayload : TMPolyTimeMap X Payload (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, allVerticesInstructionEncodedType, Payload, X] using hComp
  have hAccCycle : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst setStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, allVerticesAccEncodedType, X] using hComp
  have hOk : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, allVerticesAccEncodedType, X] using hComp
  have hPayloadCycle : TMPolyTimeMap X setStructuredEncodedType
      (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst setStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hPayloadNat : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hContainsInput :
      TMPolyTimeMap X HittingSet.setContainsInstructionInputEncodedType
        (fun p : X.Carrier => (p.2.2.2, p.1.1)) :=
    TMPolyTimeMap.prod_mk hPayloadNat hAccCycle
  have hContains : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => HittingSet.setContainsBool (p.2.2.2, p.1.1)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.setContainsBool_tm_polytime hContainsInput
    simpa [Function.comp, HittingSet.setContainsInstructionInputEncodedType, X] using hComp
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier => (p.1.2, HittingSet.setContainsBool (p.2.2.2, p.1.1))) :=
    TMPolyTimeMap.prod_mk hOk hContains
  have hAnd : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair (p.1.2, HittingSet.setContainsBool (p.2.2.2, p.1.1))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
    simpa [Function.comp, X] using hComp
  have hTrueBranch : TMPolyTimeMap X allVerticesAccEncodedType
      (fun p : X.Carrier =>
        (p.1.1, graphBoolAndPair (p.1.2, HittingSet.setContainsBool (p.2.2.2, p.1.1)))) :=
    TMPolyTimeMap.prod_mk hAccCycle hAnd
  have hTrue : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hFalseBranch : TMPolyTimeMap X allVerticesAccEncodedType
      (fun p : X.Carrier => (p.2.2.1, true)) :=
    TMPolyTimeMap.prod_mk hPayloadCycle hTrue
  have hBranchInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) allVerticesAccEncodedType
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true =>
              (p.2.1.1,
                graphBoolAndPair
                  (p.2.1.2, HittingSet.setContainsBool (p.2.2.2.2, p.2.1.1)))
          | false => (p.2.2.2.1, true)) :=
    graphBoolProduct_dispatch_tm_polytime X allVerticesAccEncodedType
      (fFalse := fun p : X.Carrier => (p.2.2.1, true))
      (fTrue := fun p : X.Carrier =>
        (p.1.1, graphBoolAndPair
          (p.1.2, HittingSet.setContainsBool (p.2.2.2, p.1.1))))
      hFalseBranch hTrueBranch
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨cycle, ok⟩, ⟨tag, payloadCycle, payloadNat⟩⟩
  cases tag <;> rfl

theorem allVerticesStep_growth
    (source : allVerticesInstructionListEncodedType.Carrier)
    (acc : allVerticesAccEncodedType.Carrier)
    (instr : allVerticesInstructionEncodedType.Carrier)
    (hAcc :
      allVerticesAccEncodedType.inputSize acc ≤
        allVerticesInstructionListEncodedType.inputSize source + 10)
    (hInstr :
      allVerticesInstructionEncodedType.inputSize instr ≤
        allVerticesInstructionListEncodedType.inputSize source) :
    allVerticesAccEncodedType.inputSize (allVerticesStep (acc, instr)) ≤
      allVerticesInstructionListEncodedType.inputSize source + 10 := by
  rcases acc with ⟨cycle, ok⟩
  rcases instr with ⟨tag, payload⟩
  rcases payload with ⟨payloadCycle, payloadNat⟩
  cases tag
  · have hLocal :
        allVerticesAccEncodedType.inputSize (payloadCycle, true) ≤
          allVerticesInstructionEncodedType.inputSize (false, (payloadCycle, payloadNat)) +
            10 := by
      simp [allVerticesAccEncodedType, allVerticesInstructionEncodedType,
        EncodedType.inputSize, EncodedType.prod, EncodedType.bool, EncodedType.nat]
      omega
    simpa [allVerticesStep] using hLocal.trans (Nat.add_le_add_right hInstr 10)
  · have hLocal :
        allVerticesAccEncodedType.inputSize
            (cycle, graphBoolAndPair (ok, HittingSet.setContainsBool (payloadNat, cycle))) ≤
          allVerticesAccEncodedType.inputSize (cycle, ok) := by
      cases ok <;> cases HittingSet.setContainsBool (payloadNat, cycle) <;>
        simp [allVerticesAccEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_bool]
    simpa [allVerticesStep] using hLocal.trans hAcc

theorem allVerticesFold_tm_polytime :
    TMPolyTimeMap
      allVerticesInstructionListEncodedType
      allVerticesAccEncodedType
      (fun xs : allVerticesInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc instr => allVerticesStep (acc, instr)) allVerticesRunnerInit) := by
  rcases allVerticesStep_tm_polytime with ⟨hStep⟩
  let bound : Polynomial Nat := Polynomial.X + Polynomial.C 10
  refine
    TMPolyTimeMap.list_foldl_typed_bounded
      allVerticesInstructionEncodedType allVerticesAccEncodedType
      allVerticesStep allVerticesRunnerInit hStep bound ?_ ?_
  · intro xs
    have hInit : allVerticesAccEncodedType.inputSize allVerticesRunnerInit ≤ 10 := by
      native_decide
    simpa [allVerticesInstructionListEncodedType, bound, Polynomial.eval_add] using
      hInit.trans (by omega)
  · intro source acc instr hAcc hInstr
    have hAcc' :
        allVerticesAccEncodedType.inputSize acc ≤
          allVerticesInstructionListEncodedType.inputSize source + 10 := by
      simpa [allVerticesInstructionListEncodedType, bound, Polynomial.eval_add] using hAcc
    have hInstr' :
        allVerticesInstructionEncodedType.inputSize instr ≤
          allVerticesInstructionListEncodedType.inputSize source := by
      simpa [allVerticesInstructionListEncodedType] using hInstr
    simpa [allVerticesInstructionListEncodedType, bound, Polynomial.eval_add] using
      allVerticesStep_growth source acc instr hAcc' hInstr'

theorem allVerticesFromInstructions_tm_polytime :
    TMPolyTimeMap allVerticesInstructionListEncodedType EncodedType.bool
      allVerticesFromInstructions := by
  have hFold := allVerticesFold_tm_polytime
  have hOk := TMPolyTimeMap.snd setStructuredEncodedType EncodedType.bool
  have hComp := TMPolyTimeMap.comp hOk hFold
  simpa [Function.comp, allVerticesFromInstructions, allVerticesAccEncodedType] using hComp

theorem allVerticesInCycleBool_tm_polytime :
    TMPolyTimeMap allVerticesInputEncodedType EncodedType.bool
      allVerticesInCycleBool := by
  have hComp := TMPolyTimeMap.comp allVerticesFromInstructions_tm_polytime
    allVerticesInstructions_tm_polytime
  simpa [Function.comp, allVerticesInCycleBool] using hComp

/-! ### Ordered cyclic edge checks -/

abbrev CycleEdgesAcc :=
  List (Nat × Nat) × Bool × Nat × Nat × Bool

def cycleEdgesAccEncodedType : EncodedType :=
  EncodedType.prod edgeListStructuredEncodedType
    (EncodedType.prod EncodedType.bool
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.bool)))

def cycleEdgesInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool
    (EncodedType.prod edgeListStructuredEncodedType EncodedType.nat)

def cycleEdgesInstructionListEncodedType : EncodedType :=
  EncodedType.list cycleEdgesInstructionEncodedType

def cycleEdgesInputEncodedType : EncodedType :=
  EncodedType.prod edgeListStructuredEncodedType setStructuredEncodedType

def cycleEdgesAcc.edges (acc : CycleEdgesAcc) : List (Nat × Nat) := acc.1
def cycleEdgesAcc.seen (acc : CycleEdgesAcc) : Bool := acc.2.1
def cycleEdgesAcc.first (acc : CycleEdgesAcc) : Nat := acc.2.2.1
def cycleEdgesAcc.prev (acc : CycleEdgesAcc) : Nat := acc.2.2.2.1
def cycleEdgesAcc.ok (acc : CycleEdgesAcc) : Bool := acc.2.2.2.2

def cycleEdgesInitAcc : CycleEdgesAcc :=
  ([], false, 0, 0, true)

def cycleEdgesInitInstruction (edges : List (Nat × Nat)) :
    Bool × (List (Nat × Nat) × Nat) :=
  (false, (edges, (0 : Nat)))

def cycleEdgesVertexInstruction (v : Nat) :
    Bool × (List (Nat × Nat) × Nat) :=
  (true, ([], v))

def cycleEdgesInstructions (p : List (Nat × Nat) × List Nat) :
    List (Bool × (List (Nat × Nat) × Nat)) :=
  cycleEdgesInitInstruction p.1 :: p.2.map cycleEdgesVertexInstruction

def cycleEdgesFirstVertexAcc (edges : List (Nat × Nat)) (v : Nat) : CycleEdgesAcc :=
  (edges, true, v, v, true)

def cycleEdgesNextVertexAcc (acc : CycleEdgesAcc) (v : Nat) : CycleEdgesAcc :=
  (cycleEdgesAcc.edges acc, true, cycleEdgesAcc.first acc, v,
    graphBoolAndPair
      (cycleEdgesAcc.ok acc,
        sourceHasDirectedEdgeBool ((cycleEdgesAcc.prev acc, v), cycleEdgesAcc.edges acc)))

def cycleEdgesVertexStep (acc : CycleEdgesAcc) (v : Nat) : CycleEdgesAcc :=
  if cycleEdgesAcc.seen acc then
    cycleEdgesNextVertexAcc acc v
  else
    cycleEdgesFirstVertexAcc (cycleEdgesAcc.edges acc) v

def cycleEdgesStep
    (p : CycleEdgesAcc × (Bool × (List (Nat × Nat) × Nat))) : CycleEdgesAcc :=
  if p.2.1 then
    cycleEdgesVertexStep p.1 p.2.2.2
  else
    (p.2.2.1, false, 0, 0, true)

def cycleEdgesClosingOK (acc : CycleEdgesAcc) : Bool :=
  if cycleEdgesAcc.seen acc then
    graphBoolAndPair
      (cycleEdgesAcc.ok acc,
        sourceHasDirectedEdgeBool
          ((cycleEdgesAcc.prev acc, cycleEdgesAcc.first acc), cycleEdgesAcc.edges acc))
  else
    true

def cycleEdgesFromInstructions
    (xs : List (Bool × (List (Nat × Nat) × Nat))) : Bool :=
  cycleEdgesClosingOK
    (xs.foldl (fun acc instr => cycleEdgesStep (acc, instr)) cycleEdgesInitAcc)

def cycleEdgesOKBool (p : List (Nat × Nat) × List Nat) : Bool :=
  cycleEdgesFromInstructions (cycleEdgesInstructions p)

def directedEdgeBoolRel (edges : List (Nat × Nat)) (u v : Nat) : Prop :=
  sourceHasDirectedEdgeBool ((u, v), edges) = true

theorem cycleEdgesTailFold_closing_eq_true_iff
    (edges : List (Nat × Nat)) (first prev : Nat) (ok : Bool) :
    ∀ rest : List Nat,
      cycleEdgesClosingOK
          ((rest.map cycleEdgesVertexInstruction).foldl
            (fun acc instr => cycleEdgesStep (acc, instr))
            (edges, true, first, prev, ok)) = true ↔
        ok = true ∧
          (prev :: rest).IsChain (directedEdgeBoolRel edges) ∧
          ∀ x ∈ (prev :: rest).getLast?, directedEdgeBoolRel edges x first
  | [] => by
      simp [cycleEdgesClosingOK, cycleEdgesAcc.seen, cycleEdgesAcc.ok,
        cycleEdgesAcc.prev, cycleEdgesAcc.first, cycleEdgesAcc.edges,
        directedEdgeBoolRel, graphBoolAndPair_eq_true_iff]
  | v :: rest => by
      rw [List.map_cons, List.foldl_cons]
      simp [cycleEdgesStep, cycleEdgesVertexStep, cycleEdgesNextVertexAcc,
        cycleEdgesVertexInstruction,
        cycleEdgesAcc.seen, cycleEdgesAcc.ok, cycleEdgesAcc.prev,
        cycleEdgesAcc.first, cycleEdgesAcc.edges]
      change
        cycleEdgesClosingOK
            ((rest.map cycleEdgesVertexInstruction).foldl
              (fun acc instr => cycleEdgesStep (acc, instr))
              (edges, true, first, v,
                graphBoolAndPair
                  (ok, sourceHasDirectedEdgeBool ((prev, v), edges)))) = true ↔
          ok = true ∧
            (directedEdgeBoolRel edges prev v ∧
              (v :: rest).IsChain (directedEdgeBoolRel edges)) ∧
            ∀ x ∈ (v :: rest).getLast?, directedEdgeBoolRel edges x first
      rw [cycleEdgesTailFold_closing_eq_true_iff edges first v
        (graphBoolAndPair (ok, sourceHasDirectedEdgeBool ((prev, v), edges))) rest]
      constructor
      · rintro ⟨hHead, hChain, hClose⟩
        rcases (graphBoolAndPair_eq_true_iff
            (ok, sourceHasDirectedEdgeBool ((prev, v), edges))).1 hHead with
          ⟨hok, hEdge⟩
        exact ⟨hok, ⟨hEdge, hChain⟩, hClose⟩
      · rintro ⟨hok, hChain, hClose⟩
        refine ⟨?_, ?_, ?_⟩
        · have hEdge : directedEdgeBoolRel edges prev v := hChain.1
          exact (graphBoolAndPair_eq_true_iff
            (ok, sourceHasDirectedEdgeBool ((prev, v), edges))).2
            ⟨hok, hEdge⟩
        · exact hChain.2
        · simpa using hClose

theorem cycleEdgesOKBool_eq_true_iff
    (edges : List (Nat × Nat)) (cycle : List Nat) :
    cycleEdgesOKBool (edges, cycle) = true ↔
      cycle.IsChain (directedEdgeBoolRel edges) ∧
        ∀ x ∈ cycle.getLast?, ∀ y ∈ cycle.head?, directedEdgeBoolRel edges x y := by
  cases cycle with
  | nil =>
      simp [cycleEdgesOKBool, cycleEdgesFromInstructions, cycleEdgesInstructions,
        cycleEdgesClosingOK, cycleEdgesStep, cycleEdgesInitAcc, cycleEdgesInitInstruction,
        cycleEdgesAcc.seen]
  | cons first rest =>
      change
        cycleEdgesClosingOK
            (((cycleEdgesInitInstruction edges ::
              (first :: rest).map cycleEdgesVertexInstruction).foldl
              (fun acc instr => cycleEdgesStep (acc, instr)) cycleEdgesInitAcc)) = true ↔ _
      rw [List.foldl_cons]
      change
        cycleEdgesClosingOK
            (((first :: rest).map cycleEdgesVertexInstruction).foldl
              (fun acc instr => cycleEdgesStep (acc, instr))
              (edges, false, 0, 0, true)) = true ↔ _
      rw [List.map_cons, List.foldl_cons]
      change
        cycleEdgesClosingOK
            ((rest.map cycleEdgesVertexInstruction).foldl
              (fun acc instr => cycleEdgesStep (acc, instr))
              (edges, true, first, first, true)) = true ↔ _
      rw [cycleEdgesTailFold_closing_eq_true_iff edges first first true rest]
      constructor
      · rintro ⟨_hok, hChain, hClose⟩
        refine ⟨hChain, ?_⟩
        intro x hx y hy
        simp at hy
        subst y
        exact hClose x hx
      · rintro ⟨hChain, hClose⟩
        refine ⟨rfl, hChain, ?_⟩
        intro x hx
        exact hClose x hx first (by simp)

theorem orderedDirectedCycleSteps_to_chain
    {g : GraphInput} {cycle : List Nat}
    (hSteps : OrderedDirectedCycleSteps g cycle) :
    cycle.IsChain (fun u v => HasDirectedEdge g u v) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hiLt : i < cycle.length := Nat.lt_trans (Nat.lt_succ_self i) hi
  have hStep := hSteps ⟨i, hiLt⟩
  have hSucc :
      cyclicSuccIndex (cycle := cycle) ⟨i, hiLt⟩ = ⟨i + 1, hi⟩ := by
    ext
    simp [cyclicSuccIndex, Nat.mod_eq_of_lt hi]
  simpa [hSucc] using hStep

theorem orderedDirectedCycleSteps_to_closing
    {g : GraphInput} {cycle : List Nat}
    (hSteps : OrderedDirectedCycleSteps g cycle) :
    ∀ x ∈ cycle.getLast?, ∀ y ∈ cycle.head?, HasDirectedEdge g x y := by
  intro x hx y hy
  cases hCycle : cycle with
  | nil =>
      simp [hCycle] at hx
  | cons first rest =>
      subst cycle
      simp at hy
      subst y
      have hLenPos : 0 < (first :: rest).length := by simp
      have hLastLt : (first :: rest).length - 1 < (first :: rest).length := by
        omega
      have hxLast :
          x = (first :: rest).get ⟨(first :: rest).length - 1, hLastLt⟩ := by
        rcases List.mem_getLast?_eq_getLast hx with ⟨hne, rfl⟩
        simpa using (List.get_length_sub_one hLastLt).symm
      subst x
      have hSucc :
          cyclicSuccIndex (cycle := first :: rest) ⟨(first :: rest).length - 1, hLastLt⟩ =
            ⟨0, hLenPos⟩ := by
        ext
        simp [cyclicSuccIndex, Nat.mod_self]
      have hStep := hSteps ⟨(first :: rest).length - 1, hLastLt⟩
      rw [hSucc] at hStep
      simpa using hStep

theorem cycleEdgesOKBool_eq_true_of_orderedSteps
    (g : GraphInput) (cycle : List Nat)
    (hSteps : OrderedDirectedCycleSteps g cycle) :
    cycleEdgesOKBool (g.edges, cycle) = true := by
  rw [cycleEdgesOKBool_eq_true_iff]
  constructor
  · have hChain := orderedDirectedCycleSteps_to_chain (g := g) (cycle := cycle) hSteps
    refine hChain.imp ?_
    intro u v hEdge
    exact (sourceHasDirectedEdgeBool_graph_eq_true_iff g u v).2 hEdge
  · intro x hx y hy
    have hClose := orderedDirectedCycleSteps_to_closing (g := g) (cycle := cycle) hSteps
    exact (sourceHasDirectedEdgeBool_graph_eq_true_iff g x y).2 (hClose x hx y hy)

theorem orderedDirectedCycleSteps_of_cycleEdgesOKBool
    (g : GraphInput) (cycle : List Nat)
    (hOK : cycleEdgesOKBool (g.edges, cycle) = true) :
    OrderedDirectedCycleSteps g cycle := by
  rcases (cycleEdgesOKBool_eq_true_iff g.edges cycle).1 hOK with ⟨hChainBool, hCloseBool⟩
  have hChain : cycle.IsChain fun u v => HasDirectedEdge g u v := by
    refine hChainBool.imp ?_
    intro u v hEdge
    exact (sourceHasDirectedEdgeBool_graph_eq_true_iff g u v).1 hEdge
  have hClose : ∀ x ∈ cycle.getLast?, ∀ y ∈ cycle.head?, HasDirectedEdge g x y := by
    intro x hx y hy
    exact (sourceHasDirectedEdgeBool_graph_eq_true_iff g x y).1 (hCloseBool x hx y hy)
  exact DirectedHamiltonianCircuit.orderedDirectedCycleSteps_of_isChain_closing
    hChain hClose

theorem cycleEdgesInitInstruction_tm_polytime :
    TMPolyTimeMap edgeListStructuredEncodedType cycleEdgesInstructionEncodedType
      cycleEdgesInitInstruction := by
  have hFalse : TMPolyTimeMap edgeListStructuredEncodedType EncodedType.bool
      (fun _ => false) :=
    TMPolyTimeMap.const edgeListStructuredEncodedType EncodedType.bool false
  have hEdges : TMPolyTimeMap edgeListStructuredEncodedType edgeListStructuredEncodedType id :=
    TMPolyTimeMap.id edgeListStructuredEncodedType
  have hZero : TMPolyTimeMap edgeListStructuredEncodedType EncodedType.nat
      (fun _ => (0 : Nat)) :=
    TMPolyTimeMap.const edgeListStructuredEncodedType EncodedType.nat (0 : Nat)
  have hPayload :
      TMPolyTimeMap edgeListStructuredEncodedType
        (EncodedType.prod edgeListStructuredEncodedType EncodedType.nat)
        (fun edges : List (Nat × Nat) => (edges, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hEdges hZero
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [cycleEdgesInitInstruction, cycleEdgesInstructionEncodedType] using hOut

theorem cycleEdgesVertexInstruction_tm_polytime :
    TMPolyTimeMap EncodedType.nat cycleEdgesInstructionEncodedType
      cycleEdgesVertexInstruction := by
  have hTrue : TMPolyTimeMap EncodedType.nat EncodedType.bool (fun _ => true) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool true
  have hEmpty : TMPolyTimeMap EncodedType.nat edgeListStructuredEncodedType
      (fun _ => ([] : List (Nat × Nat))) :=
    TMPolyTimeMap.const EncodedType.nat edgeListStructuredEncodedType []
  have hNat : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  have hPayload :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.prod edgeListStructuredEncodedType EncodedType.nat)
        (fun v : Nat => (([] : List (Nat × Nat)), v)) :=
    TMPolyTimeMap.prod_mk hEmpty hNat
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [cycleEdgesVertexInstruction, cycleEdgesInstructionEncodedType] using hOut

theorem cycleEdgesInstructions_tm_polytime :
    TMPolyTimeMap cycleEdgesInputEncodedType cycleEdgesInstructionListEncodedType
      cycleEdgesInstructions := by
  let X := cycleEdgesInputEncodedType
  have hEdges : TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, cycleEdgesInputEncodedType] using
      TMPolyTimeMap.fst edgeListStructuredEncodedType setStructuredEncodedType
  have hCycle : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, cycleEdgesInputEncodedType] using
      TMPolyTimeMap.snd edgeListStructuredEncodedType setStructuredEncodedType
  have hInit :
      TMPolyTimeMap X cycleEdgesInstructionEncodedType
        (fun p : X.Carrier => cycleEdgesInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp cycleEdgesInitInstruction_tm_polytime hEdges
    simpa [Function.comp, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X cycleEdgesInstructionListEncodedType
        (fun p : X.Carrier => [cycleEdgesInitInstruction p.1]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton cycleEdgesInstructionEncodedType) hInit
    simpa [Function.comp, cycleEdgesInstructionListEncodedType, X] using hComp
  have hVertices :
      TMPolyTimeMap X cycleEdgesInstructionListEncodedType
        (fun p : X.Carrier => p.2.map cycleEdgesVertexInstruction) := by
    have hMap := TMPolyTimeMap.list_map cycleEdgesVertexInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hCycle
    simpa [Function.comp, cycleEdgesInstructionListEncodedType, setStructuredEncodedType, X]
      using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod cycleEdgesInstructionListEncodedType
          cycleEdgesInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([cycleEdgesInitInstruction p.1], p.2.map cycleEdgesVertexInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hVertices
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append cycleEdgesInstructionEncodedType) hAppendInput
  simpa [Function.comp, cycleEdgesInstructions, cycleEdgesInstructionListEncodedType, X]
    using hOut

end DirectedHamiltonianCircuitMembership
end Karp21
end ComplexityReduction
