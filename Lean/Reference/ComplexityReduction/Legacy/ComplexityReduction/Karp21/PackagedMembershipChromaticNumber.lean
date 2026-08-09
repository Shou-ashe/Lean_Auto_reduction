/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetSystem
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.MaxCut.StructuredTM.Lookup
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ChromaticNumber
import Mathlib.Tactic

/-!
Direct standard-TM NP membership witness for faithful structured Chromatic Number.

The certificate carries two color tables.  The bounded table supplies colors for
declared vertices and is checked against the requested color bound.  The edge
table supplies colors for raw edge endpoints outside the declared vertex range.
This matches the project semantic predicate, where the color bound is imposed
only on vertices `v < graph.vertices`, while disequality is required for every
raw edge in the input list.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace ChromaticNumber

def chromaticCertificateEncodedType : EncodedType :=
  EncodedType.prod setStructuredEncodedType setStructuredEncodedType

abbrev ChromaticCertificate := List Nat × List Nat

def chromaticColorContextEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat chromaticCertificateEncodedType

abbrev ChromaticColorContext := Nat × ChromaticCertificate

def chromaticColorAtInputEncodedType : EncodedType :=
  EncodedType.prod chromaticColorContextEncodedType EncodedType.nat

def chromaticColorAt (p : ChromaticColorContext × Nat) : Nat :=
  if natLtBool (p.2, p.1.1) then
    MaxCut.natListGetD (p.1.2.1, p.2)
  else
    MaxCut.natListGetD (p.1.2.2, p.2)

theorem chromaticColorAt_in_range
    (vertices : Nat) (cert : ChromaticCertificate) (v : Nat)
    (hv : v < vertices) :
    chromaticColorAt ((vertices, cert), v) = cert.1.getD v 0 := by
  have hlt : natLtBool (v, vertices) = true :=
    (natLtBool_eq_true_iff (v, vertices)).2 hv
  simp [chromaticColorAt, MaxCut.natListGetD, hlt]

theorem chromaticColorAt_out_of_range
    (vertices : Nat) (cert : ChromaticCertificate) (v : Nat)
    (hv : vertices ≤ v) :
    chromaticColorAt ((vertices, cert), v) = cert.2.getD v 0 := by
  have hlt : natLtBool (v, vertices) = false := by
    by_contra h
    have htrue : natLtBool (v, vertices) = true := by simpa using h
    exact Nat.not_lt_of_ge hv ((natLtBool_eq_true_iff (v, vertices)).1 htrue)
  simp [chromaticColorAt, MaxCut.natListGetD, hlt]

theorem chromaticColorAt_tm_polytime :
    TMPolyTimeMap chromaticColorAtInputEncodedType EncodedType.nat chromaticColorAt := by
  let X := chromaticColorAtInputEncodedType
  have hCtx : TMPolyTimeMap X chromaticColorContextEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X, chromaticColorAtInputEncodedType] using
      TMPolyTimeMap.fst chromaticColorContextEncodedType EncodedType.nat
  have hVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X, chromaticColorAtInputEncodedType] using
      TMPolyTimeMap.snd chromaticColorContextEncodedType EncodedType.nat
  have hVertices : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat chromaticCertificateEncodedType
    have hComp := TMPolyTimeMap.comp hFst hCtx
    simpa [Function.comp, chromaticColorContextEncodedType, X] using hComp
  have hCert :
      TMPolyTimeMap X chromaticCertificateEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat chromaticCertificateEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, chromaticColorContextEncodedType, X] using hComp
  have hBounded :
      TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst setStructuredEncodedType setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hCert
    simpa [Function.comp, chromaticCertificateEncodedType, X] using hComp
  have hEdgeTable :
      TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hCert
    simpa [Function.comp, chromaticCertificateEncodedType, X] using hComp
  have hLtInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2, p.1.1)) :=
    TMPolyTimeMap.prod_mk hVertex hVertices
  have hLt :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => natLtBool (p.2, p.1.1)) := by
    have hComp := TMPolyTimeMap.comp natLtBool_tm_polytime hLtInput
    simpa [Function.comp] using hComp
  have hBoundedLookupInput :
      TMPolyTimeMap X
        (EncodedType.prod partitionWeightsStructuredEncodedType EncodedType.nat)
        (fun p : X.Carrier => (p.1.2.1, p.2)) := by
    have hPair :
        TMPolyTimeMap X (EncodedType.prod setStructuredEncodedType EncodedType.nat)
          (fun p : X.Carrier => (p.1.2.1, p.2)) :=
      TMPolyTimeMap.prod_mk hBounded hVertex
    simpa [setStructuredEncodedType, partitionWeightsStructuredEncodedType] using hPair
  have hEdgeLookupInput :
      TMPolyTimeMap X
        (EncodedType.prod partitionWeightsStructuredEncodedType EncodedType.nat)
        (fun p : X.Carrier => (p.1.2.2, p.2)) := by
    have hPair :
        TMPolyTimeMap X (EncodedType.prod setStructuredEncodedType EncodedType.nat)
          (fun p : X.Carrier => (p.1.2.2, p.2)) :=
      TMPolyTimeMap.prod_mk hEdgeTable hVertex
    simpa [setStructuredEncodedType, partitionWeightsStructuredEncodedType] using hPair
  have hBoundedLookup :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => MaxCut.natListGetD (p.1.2.1, p.2)) := by
    have hComp := TMPolyTimeMap.comp MaxCut.natListGetD_tm_polytime hBoundedLookupInput
    simpa [Function.comp] using hComp
  have hEdgeLookup :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => MaxCut.natListGetD (p.1.2.2, p.2)) := by
    have hComp := TMPolyTimeMap.comp MaxCut.natListGetD_tm_polytime hEdgeLookupInput
    simpa [Function.comp] using hComp
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (natLtBool (p.2, p.1.1), p)) :=
    TMPolyTimeMap.prod_mk hLt (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) EncodedType.nat
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true => MaxCut.natListGetD (p.2.1.2.1, p.2.2)
          | false => MaxCut.natListGetD (p.2.1.2.2, p.2.2)) :=
    graphBoolProduct_dispatch_tm_polytime X EncodedType.nat
      (fFalse := fun p : X.Carrier => MaxCut.natListGetD (p.1.2.2, p.2))
      (fTrue := fun p : X.Carrier => MaxCut.natListGetD (p.1.2.1, p.2))
      hEdgeLookup hBoundedLookup
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨vertices, cert⟩, v⟩
  cases h : natLtBool (v, vertices) <;> simp [Function.comp, chromaticColorAt, h]

def chromaticEdgeCheckInputEncodedType : EncodedType :=
  EncodedType.prod chromaticColorContextEncodedType edgeStructuredEncodedType

def chromaticEdgeColorDifferentBool (p : ChromaticColorContext × (Nat × Nat)) : Bool :=
  Bool.not
    (decide
      (chromaticColorAt (p.1, p.2.1) =
        chromaticColorAt (p.1, p.2.2)))

theorem chromaticEdgeColorDifferentBool_eq_true_iff
    (p : ChromaticColorContext × (Nat × Nat)) :
    chromaticEdgeColorDifferentBool p = true ↔
      chromaticColorAt (p.1, p.2.1) ≠ chromaticColorAt (p.1, p.2.2) := by
  simp [chromaticEdgeColorDifferentBool]

theorem chromaticEdgeColorDifferentBool_tm_polytime :
    TMPolyTimeMap chromaticEdgeCheckInputEncodedType EncodedType.bool
      chromaticEdgeColorDifferentBool := by
  let X := chromaticEdgeCheckInputEncodedType
  have hCtx :
      TMPolyTimeMap X chromaticColorContextEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, chromaticEdgeCheckInputEncodedType] using
      TMPolyTimeMap.fst chromaticColorContextEncodedType edgeStructuredEncodedType
  have hEdge : TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, chromaticEdgeCheckInputEncodedType] using
      TMPolyTimeMap.snd chromaticColorContextEncodedType edgeStructuredEncodedType
  have hLeftVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hEdge
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hRightVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hEdge
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hLeftInput :
      TMPolyTimeMap X chromaticColorAtInputEncodedType
        (fun p : X.Carrier => (p.1, p.2.1)) :=
    TMPolyTimeMap.prod_mk hCtx hLeftVertex
  have hRightInput :
      TMPolyTimeMap X chromaticColorAtInputEncodedType
        (fun p : X.Carrier => (p.1, p.2.2)) :=
    TMPolyTimeMap.prod_mk hCtx hRightVertex
  have hLeft :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => chromaticColorAt (p.1, p.2.1)) := by
    have hComp := TMPolyTimeMap.comp chromaticColorAt_tm_polytime hLeftInput
    simpa [Function.comp] using hComp
  have hRight :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => chromaticColorAt (p.1, p.2.2)) := by
    have hComp := TMPolyTimeMap.comp chromaticColorAt_tm_polytime hRightInput
    simpa [Function.comp] using hComp
  have hEqInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier =>
          (chromaticColorAt (p.1, p.2.1), chromaticColorAt (p.1, p.2.2))) :=
    TMPolyTimeMap.prod_mk hLeft hRight
  have hEq :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier =>
          decide (chromaticColorAt (p.1, p.2.1) =
            chromaticColorAt (p.1, p.2.2))) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hEqInput
    simpa [Function.comp] using hComp
  have hNot := TMPolyTimeMap.comp TMPolyTimeMap.bool_not hEq
  simpa [Function.comp, chromaticEdgeColorDifferentBool] using hNot

def chromaticEdgeInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool
    (EncodedType.prod chromaticColorContextEncodedType edgeStructuredEncodedType)

abbrev ChromaticEdgeInstruction := Bool × (ChromaticColorContext × (Nat × Nat))

def chromaticEdgeInstructionListEncodedType : EncodedType :=
  EncodedType.list chromaticEdgeInstructionEncodedType

def chromaticEdgeInstructionInputEncodedType : EncodedType :=
  EncodedType.prod chromaticColorContextEncodedType edgeListStructuredEncodedType

def chromaticEdgeAccEncodedType : EncodedType :=
  EncodedType.prod chromaticColorContextEncodedType EncodedType.bool

abbrev ChromaticEdgeAcc := ChromaticColorContext × Bool

def chromaticEmptyCertificate : ChromaticCertificate :=
  ([], [])

def chromaticDummyContext : ChromaticColorContext :=
  (0, chromaticEmptyCertificate)

def chromaticEdgeInitInstruction
    (ctx : ChromaticColorContext) : ChromaticEdgeInstruction :=
  (false, (ctx, (0, 0)))

def chromaticEdgeElementInstruction
    (e : Nat × Nat) : ChromaticEdgeInstruction :=
  (true, (chromaticDummyContext, e))

def chromaticEdgeInstructions
    (p : ChromaticColorContext × List (Nat × Nat)) :
    List ChromaticEdgeInstruction :=
  chromaticEdgeInitInstruction p.1 :: p.2.map chromaticEdgeElementInstruction

def chromaticEdgeRunnerInit : ChromaticEdgeAcc :=
  (chromaticDummyContext, false)

def chromaticEdgeStep
    (p : ChromaticEdgeAcc × ChromaticEdgeInstruction) : ChromaticEdgeAcc :=
  if p.2.1 then
    (p.1.1, graphBoolAndPair (p.1.2, chromaticEdgeColorDifferentBool (p.1.1, p.2.2.2)))
  else
    (p.2.2.1, true)

def chromaticEdgesFromInstructions
    (xs : List ChromaticEdgeInstruction) : Bool :=
  (xs.foldl (fun acc x => chromaticEdgeStep (acc, x)) chromaticEdgeRunnerInit).2

def chromaticAllEdgesColorDifferentBool
    (p : ChromaticColorContext × List (Nat × Nat)) : Bool :=
  chromaticEdgesFromInstructions (chromaticEdgeInstructions p)

theorem chromaticEdgeElementInstructions_fold_eq_true_iff
    (edges : List (Nat × Nat)) (ctx : ChromaticColorContext) (ok : Bool) :
    ((edges.map chromaticEdgeElementInstruction).foldl
        (fun acc instr => chromaticEdgeStep (acc, instr)) (ctx, ok)).2 = true ↔
      ok = true ∧
        ∀ e ∈ edges,
          chromaticColorAt (ctx, e.1) ≠ chromaticColorAt (ctx, e.2) := by
  induction edges generalizing ok with
  | nil =>
      simp
  | cons e edges ih =>
      rw [List.map_cons, List.foldl_cons]
      change
        ((edges.map chromaticEdgeElementInstruction).foldl
            (fun acc instr => chromaticEdgeStep (acc, instr))
            (ctx, graphBoolAndPair
              (ok, chromaticEdgeColorDifferentBool (ctx, e)))).2 = true ↔
          ok = true ∧
            ∀ f ∈ e :: edges,
              chromaticColorAt (ctx, f.1) ≠ chromaticColorAt (ctx, f.2)
      rw [ih]
      constructor
      · rintro ⟨hHead, hTail⟩
        rcases (graphBoolAndPair_eq_true_iff
            (ok, chromaticEdgeColorDifferentBool (ctx, e))).1 hHead with
          ⟨hok, heBool⟩
        refine ⟨hok, ?_⟩
        intro f hf
        simp at hf
        rcases hf with hfe | hf
        · subst f
          exact (chromaticEdgeColorDifferentBool_eq_true_iff (ctx, e)).1 heBool
        · exact hTail f hf
      · rintro ⟨hok, hAll⟩
        refine ⟨?_, ?_⟩
        · exact (graphBoolAndPair_eq_true_iff
            (ok, chromaticEdgeColorDifferentBool (ctx, e))).2
            ⟨hok, (chromaticEdgeColorDifferentBool_eq_true_iff (ctx, e)).2
              (hAll e (by simp))⟩
        · intro f hf
          exact hAll f (List.mem_cons_of_mem e hf)

theorem chromaticAllEdgesColorDifferentBool_eq_true_iff
    (p : ChromaticColorContext × List (Nat × Nat)) :
    chromaticAllEdgesColorDifferentBool p = true ↔
      ∀ e ∈ p.2,
        chromaticColorAt (p.1, e.1) ≠ chromaticColorAt (p.1, e.2) := by
  rcases p with ⟨ctx, edges⟩
  change
    (((chromaticEdgeInitInstruction ctx :: edges.map chromaticEdgeElementInstruction).foldl
        (fun acc instr => chromaticEdgeStep (acc, instr)) chromaticEdgeRunnerInit).2 =
      true) ↔
      ∀ e ∈ edges, chromaticColorAt (ctx, e.1) ≠ chromaticColorAt (ctx, e.2)
  rw [List.foldl_cons]
  simpa [chromaticEdgeRunnerInit, chromaticEdgeInitInstruction, chromaticEdgeStep] using
    chromaticEdgeElementInstructions_fold_eq_true_iff edges ctx true

theorem chromaticEdgeInitInstruction_tm_polytime :
    TMPolyTimeMap chromaticColorContextEncodedType chromaticEdgeInstructionEncodedType
      chromaticEdgeInitInstruction := by
  have hFalse :
      TMPolyTimeMap chromaticColorContextEncodedType EncodedType.bool
        (fun _ : ChromaticColorContext => false) :=
    TMPolyTimeMap.const chromaticColorContextEncodedType EncodedType.bool false
  have hCtx :
      TMPolyTimeMap chromaticColorContextEncodedType chromaticColorContextEncodedType id :=
    TMPolyTimeMap.id chromaticColorContextEncodedType
  have hDummyEdge :
      TMPolyTimeMap chromaticColorContextEncodedType edgeStructuredEncodedType
        (fun _ : ChromaticColorContext => ((0, 0) : Nat × Nat)) :=
    TMPolyTimeMap.const chromaticColorContextEncodedType edgeStructuredEncodedType
      (show edgeStructuredEncodedType.Carrier from ((0, 0) : Nat × Nat))
  have hPayload :
      TMPolyTimeMap chromaticColorContextEncodedType
        (EncodedType.prod chromaticColorContextEncodedType edgeStructuredEncodedType)
        (fun ctx : ChromaticColorContext =>
          (ctx, (show edgeStructuredEncodedType.Carrier from ((0, 0) : Nat × Nat)))) :=
    TMPolyTimeMap.prod_mk hCtx hDummyEdge
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [chromaticEdgeInitInstruction, chromaticEdgeInstructionEncodedType] using hOut

theorem chromaticEdgeElementInstruction_tm_polytime :
    TMPolyTimeMap edgeStructuredEncodedType chromaticEdgeInstructionEncodedType
      chromaticEdgeElementInstruction := by
  have hTrue : TMPolyTimeMap edgeStructuredEncodedType EncodedType.bool
      (fun _ : Nat × Nat => true) :=
    TMPolyTimeMap.const edgeStructuredEncodedType EncodedType.bool true
  have hContext :
      TMPolyTimeMap edgeStructuredEncodedType chromaticColorContextEncodedType
        (fun _ : Nat × Nat => chromaticDummyContext) :=
    TMPolyTimeMap.const edgeStructuredEncodedType chromaticColorContextEncodedType
      chromaticDummyContext
  have hEdge : TMPolyTimeMap edgeStructuredEncodedType edgeStructuredEncodedType id :=
    TMPolyTimeMap.id edgeStructuredEncodedType
  have hPayload :
      TMPolyTimeMap edgeStructuredEncodedType
        (EncodedType.prod chromaticColorContextEncodedType edgeStructuredEncodedType)
        (fun e : Nat × Nat => (chromaticDummyContext, e)) :=
    TMPolyTimeMap.prod_mk hContext hEdge
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [chromaticEdgeElementInstruction, chromaticEdgeInstructionEncodedType] using hOut

theorem chromaticEdgeInstructions_tm_polytime :
    TMPolyTimeMap chromaticEdgeInstructionInputEncodedType
      chromaticEdgeInstructionListEncodedType chromaticEdgeInstructions := by
  let X := chromaticEdgeInstructionInputEncodedType
  have hCtx :
      TMPolyTimeMap X chromaticColorContextEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, chromaticEdgeInstructionInputEncodedType] using
      TMPolyTimeMap.fst chromaticColorContextEncodedType edgeListStructuredEncodedType
  have hEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, chromaticEdgeInstructionInputEncodedType] using
      TMPolyTimeMap.snd chromaticColorContextEncodedType edgeListStructuredEncodedType
  have hInit :
      TMPolyTimeMap X chromaticEdgeInstructionEncodedType
        (fun p : X.Carrier => chromaticEdgeInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp chromaticEdgeInitInstruction_tm_polytime hCtx
    simpa [Function.comp, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X chromaticEdgeInstructionListEncodedType
        (fun p : X.Carrier => [chromaticEdgeInitInstruction p.1]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton chromaticEdgeInstructionEncodedType) hInit
    simpa [Function.comp, chromaticEdgeInstructionListEncodedType, X] using hComp
  have hElementInstructions :
      TMPolyTimeMap X chromaticEdgeInstructionListEncodedType
        (fun p : X.Carrier => p.2.map chromaticEdgeElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map chromaticEdgeElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hEdges
    simpa [Function.comp, chromaticEdgeInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod chromaticEdgeInstructionListEncodedType
          chromaticEdgeInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([chromaticEdgeInitInstruction p.1],
            p.2.map chromaticEdgeElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hElementInstructions
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append chromaticEdgeInstructionEncodedType) hAppendInput
  simpa [Function.comp, chromaticEdgeInstructions, chromaticEdgeInstructionListEncodedType, X]
    using hOut

theorem chromaticEdgeStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod chromaticEdgeAccEncodedType chromaticEdgeInstructionEncodedType)
      chromaticEdgeAccEncodedType
      chromaticEdgeStep := by
  let X := EncodedType.prod chromaticEdgeAccEncodedType chromaticEdgeInstructionEncodedType
  let A := chromaticEdgeAccEncodedType
  let Payload := EncodedType.prod chromaticColorContextEncodedType edgeStructuredEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst A chromaticEdgeInstructionEncodedType
  have hInstr :
      TMPolyTimeMap X chromaticEdgeInstructionEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd A chromaticEdgeInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, chromaticEdgeInstructionEncodedType, Payload, X] using hComp
  have hPayload : TMPolyTimeMap X Payload (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, chromaticEdgeInstructionEncodedType, Payload, X] using hComp
  have hAccCtx :
      TMPolyTimeMap X chromaticColorContextEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst chromaticColorContextEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, chromaticEdgeAccEncodedType, X] using hComp
  have hOk : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd chromaticColorContextEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, chromaticEdgeAccEncodedType, X] using hComp
  have hPayloadCtx :
      TMPolyTimeMap X chromaticColorContextEncodedType (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst chromaticColorContextEncodedType edgeStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hPayloadEdge :
      TMPolyTimeMap X edgeStructuredEncodedType (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd chromaticColorContextEncodedType edgeStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hEdgeCheckInput :
      TMPolyTimeMap X chromaticEdgeCheckInputEncodedType
        (fun p : X.Carrier => (p.1.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAccCtx hPayloadEdge
  have hEdgeCheck :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => chromaticEdgeColorDifferentBool (p.1.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp chromaticEdgeColorDifferentBool_tm_polytime
      hEdgeCheckInput
    simpa [Function.comp, chromaticEdgeCheckInputEncodedType] using hComp
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (p.1.2, chromaticEdgeColorDifferentBool (p.1.1, p.2.2.2))) :=
    TMPolyTimeMap.prod_mk hOk hEdgeCheck
  have hAnd :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier =>
          graphBoolAndPair
            (p.1.2, chromaticEdgeColorDifferentBool (p.1.1, p.2.2.2))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
    simpa [Function.comp] using hComp
  have hTrueBranch : TMPolyTimeMap X A
      (fun p : X.Carrier =>
        (p.1.1,
          graphBoolAndPair
            (p.1.2, chromaticEdgeColorDifferentBool (p.1.1, p.2.2.2)))) :=
    TMPolyTimeMap.prod_mk hAccCtx hAnd
  have hTrueConst : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hFalseBranch : TMPolyTimeMap X A (fun p : X.Carrier => (p.2.2.1, true)) :=
    TMPolyTimeMap.prod_mk hPayloadCtx hTrueConst
  have hBranchInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranchOnProduct :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true =>
              (p.2.1.1,
                graphBoolAndPair
                  (p.2.1.2, chromaticEdgeColorDifferentBool (p.2.1.1, p.2.2.2.2)))
          | false => (p.2.2.2.1, true)) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier => (p.2.2.1, true))
      (fTrue := fun p : X.Carrier =>
        (p.1.1,
          graphBoolAndPair
            (p.1.2, chromaticEdgeColorDifferentBool (p.1.1, p.2.2.2))))
      hFalseBranch hTrueBranch
  have hOut := TMPolyTimeMap.comp hBranchOnProduct hBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨ctx, ok⟩, ⟨tag, payloadCtx, edge⟩⟩
  cases tag <;> rfl

theorem chromaticEdgeStep_inputSize_le
    (source : chromaticEdgeInstructionListEncodedType.Carrier)
    (acc : chromaticEdgeAccEncodedType.Carrier)
    (instr : chromaticEdgeInstructionEncodedType.Carrier)
    (hAcc :
      chromaticEdgeAccEncodedType.inputSize acc ≤
        chromaticEdgeInstructionListEncodedType.inputSize source + 10)
    (hInstr :
      chromaticEdgeInstructionEncodedType.inputSize instr ≤
        chromaticEdgeInstructionListEncodedType.inputSize source) :
    chromaticEdgeAccEncodedType.inputSize (chromaticEdgeStep (acc, instr)) ≤
      chromaticEdgeInstructionListEncodedType.inputSize source + 10 := by
  rcases acc with ⟨ctx, ok⟩
  rcases instr with ⟨tag, payload⟩
  rcases payload with ⟨payloadCtx, edge⟩
  cases tag
  · have hLocal :
        chromaticEdgeAccEncodedType.inputSize (payloadCtx, true) ≤
          chromaticEdgeInstructionEncodedType.inputSize (false, (payloadCtx, edge)) + 10 := by
      simp [chromaticEdgeAccEncodedType, chromaticEdgeInstructionEncodedType,
        EncodedType.inputSize, EncodedType.prod, EncodedType.bool]
      omega
    exact (by simpa [chromaticEdgeStep] using hLocal.trans (Nat.add_le_add_right hInstr 10))
  · have hLocal :
        chromaticEdgeAccEncodedType.inputSize
            (chromaticEdgeStep ((ctx, ok), (true, (payloadCtx, edge)))) ≤
          chromaticEdgeAccEncodedType.inputSize (ctx, ok) := by
      by_cases h : chromaticEdgeColorDifferentBool (ctx, edge) = true <;>
        cases ok <;>
          simp [chromaticEdgeStep, h, chromaticEdgeAccEncodedType,
            EncodedType.inputSize, EncodedType.prod, EncodedType.bool]
    exact hLocal.trans hAcc

theorem chromaticEdgeFold_tm_polytime :
    TMPolyTimeMap chromaticEdgeInstructionListEncodedType chromaticEdgeAccEncodedType
      (fun xs : chromaticEdgeInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc x => chromaticEdgeStep (acc, x)) chromaticEdgeRunnerInit) := by
  rcases chromaticEdgeStep_tm_polytime with ⟨hStep⟩
  let bound : Polynomial Nat := Polynomial.X + Polynomial.C 10
  refine
    TMPolyTimeMap.list_foldl_typed_bounded
      chromaticEdgeInstructionEncodedType chromaticEdgeAccEncodedType
      chromaticEdgeStep chromaticEdgeRunnerInit hStep bound ?_ ?_
  · intro xs
    change chromaticEdgeAccEncodedType.inputSize chromaticEdgeRunnerInit ≤
      (Polynomial.X + Polynomial.C 10).eval
        (chromaticEdgeInstructionEncodedType.list.inputSize xs)
    have hInit : chromaticEdgeAccEncodedType.inputSize chromaticEdgeRunnerInit ≤ 10 := by
      have hEmpty : setStructuredEncodedType.inputSize ([] : List Nat) = 0 :=
        EncodedType.inputSize_list_nil EncodedType.nat
      simp [chromaticEdgeAccEncodedType, chromaticEdgeRunnerInit,
        chromaticDummyContext, chromaticEmptyCertificate,
        chromaticColorContextEncodedType, chromaticCertificateEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_bool,
        EncodedType.inputSize_nat, hEmpty]
    have hEval :
        (Polynomial.X + Polynomial.C 10).eval
            (chromaticEdgeInstructionEncodedType.list.inputSize xs) =
          chromaticEdgeInstructionEncodedType.list.inputSize xs + 10 := by
      simp [Polynomial.eval_add]
    rw [hEval]
    omega
  · intro source acc instr hAcc hInstr
    have hAcc' :
        chromaticEdgeAccEncodedType.inputSize acc ≤
          chromaticEdgeInstructionListEncodedType.inputSize source + 10 := by
      simpa [chromaticEdgeInstructionListEncodedType, bound, Polynomial.eval_add] using hAcc
    have hInstr' :
        chromaticEdgeInstructionEncodedType.inputSize instr ≤
          chromaticEdgeInstructionListEncodedType.inputSize source := by
      simpa [chromaticEdgeInstructionListEncodedType] using hInstr
    simpa [chromaticEdgeInstructionListEncodedType, bound, Polynomial.eval_add] using
      chromaticEdgeStep_inputSize_le source acc instr hAcc' hInstr'

theorem chromaticEdgesFromInstructions_tm_polytime :
    TMPolyTimeMap chromaticEdgeInstructionListEncodedType EncodedType.bool
      chromaticEdgesFromInstructions := by
  have hFold := chromaticEdgeFold_tm_polytime
  have hOk := TMPolyTimeMap.snd chromaticColorContextEncodedType EncodedType.bool
  have hComp := TMPolyTimeMap.comp hOk hFold
  simpa [Function.comp, chromaticEdgesFromInstructions, chromaticEdgeAccEncodedType]
    using hComp

theorem chromaticAllEdgesColorDifferentBool_tm_polytime :
    TMPolyTimeMap chromaticEdgeInstructionInputEncodedType EncodedType.bool
      chromaticAllEdgesColorDifferentBool := by
  have hComp := TMPolyTimeMap.comp chromaticEdgesFromInstructions_tm_polytime
    chromaticEdgeInstructions_tm_polytime
  simpa [Function.comp, chromaticAllEdgesColorDifferentBool] using hComp

def chromaticNumberStructuredFiniteVerify
    (I : ChromaticNumberInput) (cert : ChromaticCertificate) : Bool :=
  graphBoolAndPair
    (HittingSet.natLeBool (I.graph.vertices, cert.1.length),
      graphBoolAndPair
        (HittingSet.boundedNatListBool (I.colors, cert.1),
          chromaticAllEdgesColorDifferentBool ((I.graph.vertices, cert), I.graph.edges)))

theorem chromaticNumberStructuredFiniteVerify_eq_true_iff
    (I : ChromaticNumberInput) (cert : ChromaticCertificate) :
    chromaticNumberStructuredFiniteVerify I cert = true ↔
      I.graph.vertices ≤ cert.1.length ∧
        (∀ c ∈ cert.1, c < I.colors) ∧
        ∀ e ∈ I.graph.edges,
          chromaticColorAt ((I.graph.vertices, cert), e.1) ≠
            chromaticColorAt ((I.graph.vertices, cert), e.2) := by
  rw [chromaticNumberStructuredFiniteVerify, graphBoolAndPair_eq_true_iff,
    graphBoolAndPair_eq_true_iff, HittingSet.natLeBool_eq_true_iff,
    HittingSet.boundedNatListBool_eq_true_iff,
    chromaticAllEdgesColorDifferentBool_eq_true_iff]

theorem chromaticNumberStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod chromaticNumberStructuredEncodedType chromaticCertificateEncodedType)
      EncodedType.bool
      (fun p : ChromaticNumberInput × ChromaticCertificate =>
        chromaticNumberStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod chromaticNumberStructuredEncodedType chromaticCertificateEncodedType
  have hInstance :
      TMPolyTimeMap X chromaticNumberStructuredEncodedType
        (fun p : X.Carrier => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst chromaticNumberStructuredEncodedType chromaticCertificateEncodedType
  have hCert :
      TMPolyTimeMap X chromaticCertificateEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd chromaticNumberStructuredEncodedType chromaticCertificateEncodedType
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType (fun p : X.Carrier => p.1.graph) := by
    have hComp := TMPolyTimeMap.comp chromaticNumberGraphTMBackedMap.tm_polytime hInstance
    simpa [Function.comp, X] using hComp
  have hColors :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.colors) := by
    have hComp := TMPolyTimeMap.comp chromaticNumberColorsTMBackedMap.tm_polytime hInstance
    simpa [Function.comp, X] using hComp
  have hVertices :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp graphVerticesTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hGraphPayload :
      TMPolyTimeMap X graphPayloadStructuredEncodedType
        (fun p : X.Carrier => graphPayloadOfGraph p.1.graph) := by
    have hComp := TMPolyTimeMap.comp graphPayloadTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.1.graph.edges) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hGraphPayload
    simpa [Function.comp, graphPayloadOfGraph, graphPayloadStructuredEncodedType, X] using hComp
  have hBounded :
      TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst setStructuredEncodedType setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hCert
    simpa [Function.comp, chromaticCertificateEncodedType, X] using hComp
  have hBoundedLength :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1.length) := by
    have hComp := TMPolyTimeMap.comp (HittingSet.listLengthTMBackedMap EncodedType.nat).tm_polytime
      hBounded
    simpa [Function.comp, setStructuredEncodedType, X] using hComp
  have hLengthInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.1.graph.vertices, p.2.1.length)) :=
    TMPolyTimeMap.prod_mk hVertices hBoundedLength
  have hLengthOK :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => HittingSet.natLeBool (p.1.graph.vertices, p.2.1.length)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.natLeBool_tm_polytime hLengthInput
    simpa [Function.comp] using hComp
  have hWithinInput :
      TMPolyTimeMap X HittingSet.boundedNatInstructionInputEncodedType
        (fun p : X.Carrier => (p.1.colors, p.2.1)) :=
    TMPolyTimeMap.prod_mk hColors hBounded
  have hWithin :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => HittingSet.boundedNatListBool (p.1.colors, p.2.1)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.boundedNatListBool_tm_polytime hWithinInput
    simpa [Function.comp, HittingSet.boundedNatInstructionInputEncodedType] using hComp
  have hContext :
      TMPolyTimeMap X chromaticColorContextEncodedType
        (fun p : X.Carrier => (p.1.graph.vertices, p.2)) :=
    TMPolyTimeMap.prod_mk hVertices hCert
  have hEdgesInput :
      TMPolyTimeMap X chromaticEdgeInstructionInputEncodedType
        (fun p : X.Carrier => ((p.1.graph.vertices, p.2), p.1.graph.edges)) :=
    TMPolyTimeMap.prod_mk hContext hEdges
  have hEdgesOK :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier =>
          chromaticAllEdgesColorDifferentBool ((p.1.graph.vertices, p.2), p.1.graph.edges)) := by
    have hComp := TMPolyTimeMap.comp chromaticAllEdgesColorDifferentBool_tm_polytime hEdgesInput
    simpa [Function.comp, chromaticEdgeInstructionInputEncodedType] using hComp
  have hTailInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (HittingSet.boundedNatListBool (p.1.colors, p.2.1),
            chromaticAllEdgesColorDifferentBool ((p.1.graph.vertices, p.2), p.1.graph.edges))) :=
    TMPolyTimeMap.prod_mk hWithin hEdgesOK
  have hTail :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier =>
          graphBoolAndPair
            (HittingSet.boundedNatListBool (p.1.colors, p.2.1),
              chromaticAllEdgesColorDifferentBool
                ((p.1.graph.vertices, p.2), p.1.graph.edges))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hTailInput
    simpa [Function.comp] using hComp
  have hAllInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (HittingSet.natLeBool (p.1.graph.vertices, p.2.1.length),
            graphBoolAndPair
              (HittingSet.boundedNatListBool (p.1.colors, p.2.1),
                chromaticAllEdgesColorDifferentBool
                  ((p.1.graph.vertices, p.2), p.1.graph.edges)))) :=
    TMPolyTimeMap.prod_mk hLengthOK hTail
  have hAll := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAllInput
  simpa [Function.comp, chromaticNumberStructuredFiniteVerify, X] using hAll

def boundedColorTable (I : ChromaticNumberInput) (colorOf : Nat → Nat) : List Nat :=
  (List.range I.graph.vertices).map colorOf

def normalizedEdgeColor (I : ChromaticNumberInput) (colorOf : Nat → Nat) (v : Nat) : Nat :=
  if v < I.graph.vertices then colorOf v else I.colors + v

def edgeColorTable (I : ChromaticNumberInput) (colorOf : Nat → Nat) : List Nat :=
  (List.range (chromaticNumberStructuredEncodedType.inputSize I + 1)).map
    (normalizedEdgeColor I colorOf)

def certificateOfColoring (I : ChromaticNumberInput) (colorOf : Nat → Nat) :
    ChromaticCertificate :=
  (boundedColorTable I colorOf, edgeColorTable I colorOf)

theorem getD_range_map_eq {f : Nat → Nat} {n i : Nat} (hi : i < n) :
    ((List.range n).map f).getD i 0 = f i := by
  have hLen : i < ((List.range n).map f).length := by simpa using hi
  rw [List.getD_eq_getElem (l := (List.range n).map f) (d := 0) (n := i) hLen]
  simp

theorem chromaticNumberStructured_inputSize_ge_vertices
    (I : ChromaticNumberInput) :
    I.graph.vertices ≤ chromaticNumberStructuredEncodedType.inputSize I := by
  rw [chromaticNumberStructured_inputSize_eq, Clique.graphStructured_inputSize_eq]
  omega

theorem chromaticNumberStructured_inputSize_ge_colors
    (I : ChromaticNumberInput) :
    I.colors ≤ chromaticNumberStructuredEncodedType.inputSize I := by
  rw [chromaticNumberStructured_inputSize_eq]
  omega

theorem chromaticEdge_endpoint_lt_inputSize_succ
    {I : ChromaticNumberInput} {e : Nat × Nat} (he : e ∈ I.graph.edges) :
    e.1 < chromaticNumberStructuredEncodedType.inputSize I + 1 ∧
      e.2 < chromaticNumberStructuredEncodedType.inputSize I + 1 := by
  let S := chromaticNumberStructuredEncodedType.inputSize I
  have hEdge :=
    Clique.encodedList_element_inputSize_le (X := edgeStructuredEncodedType) he
  have hEdgeSize :
      e.1 + e.2 + 3 ≤ edgeListStructuredEncodedType.inputSize I.graph.edges := by
    simpa [edgeStructuredEncodedType, EncodedType.inputSize, EncodedType.prod,
      EncodedType.nat] using hEdge
  have hListLe : edgeListStructuredEncodedType.inputSize I.graph.edges ≤ S := by
    simp [S, chromaticNumberStructured_inputSize_eq, Clique.graphStructured_inputSize_eq]
    omega
  constructor <;> omega

theorem certificateOfColoring_colorAt
    (I : ChromaticNumberInput) (colorOf : Nat → Nat) {v : Nat}
    (hv : v < chromaticNumberStructuredEncodedType.inputSize I + 1) :
    chromaticColorAt ((I.graph.vertices, certificateOfColoring I colorOf), v) =
      normalizedEdgeColor I colorOf v := by
  by_cases hIn : v < I.graph.vertices
  · rw [chromaticColorAt_in_range _ _ _ hIn]
    change (boundedColorTable I colorOf).getD v 0 = normalizedEdgeColor I colorOf v
    rw [boundedColorTable]
    rw [getD_range_map_eq hIn]
    simp [normalizedEdgeColor, hIn]
  · have hOut : I.graph.vertices ≤ v := Nat.le_of_not_gt hIn
    rw [chromaticColorAt_out_of_range _ _ _ hOut]
    change (edgeColorTable I colorOf).getD v 0 = normalizedEdgeColor I colorOf v
    rw [edgeColorTable]
    rw [getD_range_map_eq hv]

theorem normalizedEdgeColor_edge_ne
    (I : ChromaticNumberInput) (colorOf : Nat → Nat)
    (hProper : ProperColoring I.graph I.colors colorOf)
    (e : Nat × Nat) (he : e ∈ I.graph.edges) :
    normalizedEdgeColor I colorOf e.1 ≠ normalizedEdgeColor I colorOf e.2 := by
  by_cases hLeft : e.1 < I.graph.vertices
  · by_cases hRight : e.2 < I.graph.vertices
    · simpa [normalizedEdgeColor, hLeft, hRight] using hProper.2 e he
    · intro hEq
      have hLeftColor := hProper.1 e.1 hLeft
      simp [normalizedEdgeColor, hLeft, hRight] at hEq
      omega
  · by_cases hRight : e.2 < I.graph.vertices
    · intro hEq
      have hRightColor := hProper.1 e.2 hRight
      simp [normalizedEdgeColor, hLeft, hRight] at hEq
      omega
    · have hEndpoints : e.1 ≠ e.2 := by
        intro hEq
        exact hProper.2 e he (by simp [hEq])
      intro hEq
      simp [normalizedEdgeColor, hLeft, hRight] at hEq
      omega

theorem certificateOfColoring_inputSize_le_poly
    (I : ChromaticNumberInput) (colorOf : Nat → Nat)
    (hProper : ProperColoring I.graph I.colors colorOf) :
    chromaticCertificateEncodedType.inputSize (certificateOfColoring I colorOf) ≤
      20 * (chromaticNumberStructuredEncodedType.inputSize I) ^ 3 + 100 := by
  let S := chromaticNumberStructuredEncodedType.inputSize I
  have hVertices : I.graph.vertices ≤ S := by
    simpa [S] using chromaticNumberStructured_inputSize_ge_vertices I
  have hColors : I.colors ≤ S := by
    simpa [S] using chromaticNumberStructured_inputSize_ge_colors I
  have hBoundedWithin :
      ∀ c ∈ boundedColorTable I colorOf, c < I.colors := by
    intro c hc
    rcases List.mem_map.mp hc with ⟨v, hv, rfl⟩
    exact hProper.1 v (List.mem_range.mp hv)
  have hBoundedSize :=
    HittingSet.boundedNatList_inputSize_le I.colors
      (boundedColorTable I colorOf) hBoundedWithin
  have hEdgeWithin :
      ∀ c ∈ edgeColorTable I colorOf, c < 2 * S + 1 := by
    intro c hc
    rcases List.mem_map.mp hc with ⟨v, hv, rfl⟩
    have hvS : v < S + 1 := by simpa [S] using List.mem_range.mp hv
    by_cases hvtx : v < I.graph.vertices
    · have hcBound := hProper.1 v hvtx
      simp [normalizedEdgeColor, hvtx]
      omega
    · simp [normalizedEdgeColor, hvtx]
      omega
  have hEdgeSize :=
    HittingSet.boundedNatList_inputSize_le (2 * S + 1)
      (edgeColorTable I colorOf) hEdgeWithin
  have hBoundedLen : (boundedColorTable I colorOf).length = I.graph.vertices := by
    simp [boundedColorTable]
  have hEdgeLen : (edgeColorTable I colorOf).length = S + 1 := by
    simp [edgeColorTable, S]
  calc
    chromaticCertificateEncodedType.inputSize (certificateOfColoring I colorOf)
        = setStructuredEncodedType.inputSize (boundedColorTable I colorOf) +
            setStructuredEncodedType.inputSize (edgeColorTable I colorOf) + 1 := by
          simp [certificateOfColoring, chromaticCertificateEncodedType,
            EncodedType.inputSize, EncodedType.prod]
          omega
    _ ≤ (boundedColorTable I colorOf).length * (I.colors + 1) +
          (edgeColorTable I colorOf).length * ((2 * S + 1) + 1) + 1 := by
          exact Nat.add_le_add_right (Nat.add_le_add hBoundedSize hEdgeSize) 1
    _ = I.graph.vertices * (I.colors + 1) + (S + 1) * (2 * S + 2) + 1 := by
          rw [hBoundedLen, hEdgeLen]
    _ ≤ S * (S + 1) + (S + 1) * (2 * S + 2) + 1 := by
          have hColorSucc : I.colors + 1 ≤ S + 1 := Nat.succ_le_succ hColors
          exact Nat.add_le_add_right
            (Nat.add_le_add (Nat.mul_le_mul hVertices hColorSucc)
              (le_refl ((S + 1) * (2 * S + 2)))) 1
    _ ≤ 20 * S ^ 3 + 100 := by
          by_cases hS : S = 0
          · rw [hS]
            norm_num
          · have hSpos : 1 ≤ S := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hS)
            nlinarith [sq_nonneg (S : Int)]

theorem chromaticNumberStructuredFiniteVerify_sound
    (I : ChromaticNumberInput) (cert : ChromaticCertificate)
    (hVerify : chromaticNumberStructuredFiniteVerify I cert = true) :
    ChromaticNumber I := by
  rcases (chromaticNumberStructuredFiniteVerify_eq_true_iff I cert).1 hVerify with
    ⟨hLen, hBounded, hEdges⟩
  refine ⟨fun v => chromaticColorAt ((I.graph.vertices, cert), v), ?_⟩
  constructor
  · intro v hv
    change chromaticColorAt ((I.graph.vertices, cert), v) < I.colors
    rw [chromaticColorAt_in_range I.graph.vertices cert v hv]
    have hvLen : v < cert.1.length := lt_of_lt_of_le hv hLen
    have hMem : cert.1.getD v 0 ∈ cert.1 := by
      rw [List.getD_eq_getElem (l := cert.1) (d := 0) (n := v) hvLen]
      exact List.getElem_mem hvLen
    exact hBounded _ hMem
  · intro e he
    exact hEdges e he

theorem chromaticNumberStructuredFiniteVerify_complete
    (I : ChromaticNumberInput) {colorOf : Nat → Nat}
    (hProper : ProperColoring I.graph I.colors colorOf) :
    chromaticNumberStructuredFiniteVerify I (certificateOfColoring I colorOf) = true := by
  refine (chromaticNumberStructuredFiniteVerify_eq_true_iff
    I (certificateOfColoring I colorOf)).2 ?_
  constructor
  · simp [certificateOfColoring, boundedColorTable]
  constructor
  · intro c hc
    rcases List.mem_map.mp hc with ⟨v, hv, rfl⟩
    exact hProper.1 v (List.mem_range.mp hv)
  · intro e he
    have hLeft := chromaticEdge_endpoint_lt_inputSize_succ (I := I) he |>.1
    have hRight := chromaticEdge_endpoint_lt_inputSize_succ (I := I) he |>.2
    rw [certificateOfColoring_colorAt I colorOf hLeft,
      certificateOfColoring_colorAt I colorOf hRight]
    exact normalizedEdgeColor_edge_ne I colorOf hProper e he

end ChromaticNumber

/-- Direct finite-certificate TM verifier for faithful structured Chromatic Number. -/
noncomputable def chromaticNumberStructuredFiniteTMVerifier :
    TMVerifier chromaticNumberStructuredDecisionProblem where
  Cert := ChromaticNumber.chromaticCertificateEncodedType
  verify := ChromaticNumber.chromaticNumberStructuredFiniteVerify
  verifier_polytime := ChromaticNumber.chromaticNumberStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨3, 20, 100, ?_⟩
    intro I hYes
    rcases hYes with ⟨colorOf, hProper⟩
    refine ⟨ChromaticNumber.certificateOfColoring I colorOf, ?_, ?_⟩
    · exact ChromaticNumber.certificateOfColoring_inputSize_le_poly I colorOf hProper
    · exact ChromaticNumber.chromaticNumberStructuredFiniteVerify_complete I hProper
  sound := by
    intro I cert hVerify
    exact ChromaticNumber.chromaticNumberStructuredFiniteVerify_sound I cert hVerify

theorem chromaticNumberStructured_TMInNP :
    TMInNP chromaticNumberStructuredDecisionProblem :=
  TMInNP.intro chromaticNumberStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
