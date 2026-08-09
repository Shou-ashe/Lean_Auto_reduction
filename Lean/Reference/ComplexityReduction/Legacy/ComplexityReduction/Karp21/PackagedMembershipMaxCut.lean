/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatPair
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetSystemBounds
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.Projections
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.MaxCut
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeSATFiniteVerifierTM
import Mathlib.Tactic

/-!
Direct standard-TM NP membership witness for faithful structured Max Cut.

The certificate is a finite Boolean side-assignment.  Missing indices default to
`false`, exactly as `SAT.finiteAssignment` does.  Completeness uses the prefix
of the semantic side assignment up to the encoded Max-Cut input size; every raw
edge endpoint in the encoded edge list is below that size.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace MaxCut

abbrev maxCutCertificateEncodedType : EncodedType :=
  SAT.finiteAssignmentCertEncodedType

abbrev MaxCutCertificate := List Bool

/-! ### Structured Max-Cut projections -/

theorem maxCutGraph_encode_filterMap (I : MaxCutInput) :
    graphStructuredEncodedType.encode I.graph =
      (maxCutStructuredEncodedType.encode I).filterMap
        (@EncodedType.prodLeftSymbol
          graphStructuredEncodedType.Symbol EncodedType.nat.Symbol) := by
  simpa [maxCutStructuredEncodedType] using
    (EncodedType.prod_left_filter_encode
      graphStructuredEncodedType EncodedType.nat (I.graph, I.threshold)).symm

theorem maxCutThreshold_encode_filterMap (I : MaxCutInput) :
    EncodedType.nat.encode I.threshold =
      (maxCutStructuredEncodedType.encode I).filterMap
        (@EncodedType.prodRightSymbol
          graphStructuredEncodedType.Symbol EncodedType.nat.Symbol) := by
  simpa [maxCutStructuredEncodedType] using
    (EncodedType.prod_right_filter_encode
      graphStructuredEncodedType EncodedType.nat (I.graph, I.threshold)).symm

noncomputable def maxCutGraphTMBackedMap :
    TMBackedCostedMap maxCutStructuredEncodedType graphStructuredEncodedType
      (fun I : MaxCutInput => I.graph) :=
  TMBackedCostedMap.symbolFilterMap
    maxCutStructuredEncodedType graphStructuredEncodedType
    (fun I : MaxCutInput => I.graph)
    (@EncodedType.prodLeftSymbol
      graphStructuredEncodedType.Symbol EncodedType.nat.Symbol)
    maxCutGraph_encode_filterMap

noncomputable def maxCutThresholdTMBackedMap :
    TMBackedCostedMap maxCutStructuredEncodedType EncodedType.nat
      (fun I : MaxCutInput => I.threshold) :=
  TMBackedCostedMap.symbolFilterMap
    maxCutStructuredEncodedType EncodedType.nat
    (fun I : MaxCutInput => I.threshold)
    (@EncodedType.prodRightSymbol
      graphStructuredEncodedType.Symbol EncodedType.nat.Symbol)
    maxCutThreshold_encode_filterMap

/-! ### Edge-cut runner -/

def maxCutSideFromCertificate (bits : MaxCutCertificate) (v : Nat) : Bool :=
  SAT.lookupBoolAt (bits, v)

theorem maxCutSideFromCertificate_eq_finiteAssignment
    (bits : MaxCutCertificate) :
    maxCutSideFromCertificate bits = SAT.finiteAssignment bits := by
  funext v
  exact SAT.lookupBoolAt_eq_finiteAssignment bits v

def maxCutEdgeCutInputEncodedType : EncodedType :=
  EncodedType.prod maxCutCertificateEncodedType edgeStructuredEncodedType

def maxCutEdgeCutBool (p : MaxCutCertificate × (Nat × Nat)) : Bool :=
  Bool.not
    (decide
      (boolToNat (maxCutSideFromCertificate p.1 p.2.1) =
        boolToNat (maxCutSideFromCertificate p.1 p.2.2)))

theorem maxCutEdgeCutBool_eq_true_iff
    (p : MaxCutCertificate × (Nat × Nat)) :
    maxCutEdgeCutBool p = true ↔
      maxCutSideFromCertificate p.1 p.2.1 ≠
        maxCutSideFromCertificate p.1 p.2.2 := by
  rcases p with ⟨bits, u, v⟩
  unfold maxCutEdgeCutBool
  cases hLeft : maxCutSideFromCertificate bits u <;>
    cases hRight : maxCutSideFromCertificate bits v <;>
      simp [boolToNat]

theorem maxCutEdgeCutBool_tm_polytime :
    TMPolyTimeMap maxCutEdgeCutInputEncodedType EncodedType.bool
      maxCutEdgeCutBool := by
  let X := maxCutEdgeCutInputEncodedType
  have hBits : TMPolyTimeMap X maxCutCertificateEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X, maxCutEdgeCutInputEncodedType] using
      TMPolyTimeMap.fst maxCutCertificateEncodedType edgeStructuredEncodedType
  have hEdge : TMPolyTimeMap X edgeStructuredEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X, maxCutEdgeCutInputEncodedType] using
      TMPolyTimeMap.snd maxCutCertificateEncodedType edgeStructuredEncodedType
  have hLeftVertex : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hEdge
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hRightVertex : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hEdge
    simpa [Function.comp, edgeStructuredEncodedType, X] using hComp
  have hLeftInput :
      TMPolyTimeMap X SAT.lookupBoolInputEncodedType
        (fun p : X.Carrier => (p.1, p.2.1)) :=
    TMPolyTimeMap.prod_mk hBits hLeftVertex
  have hRightInput :
      TMPolyTimeMap X SAT.lookupBoolInputEncodedType
        (fun p : X.Carrier => (p.1, p.2.2)) :=
    TMPolyTimeMap.prod_mk hBits hRightVertex
  have hLeftBool :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => maxCutSideFromCertificate p.1 p.2.1) := by
    have hComp := TMPolyTimeMap.comp SAT.lookupBoolAt_tm_polytime hLeftInput
    simpa [Function.comp, maxCutSideFromCertificate] using hComp
  have hRightBool :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => maxCutSideFromCertificate p.1 p.2.2) := by
    have hComp := TMPolyTimeMap.comp SAT.lookupBoolAt_tm_polytime hRightInput
    simpa [Function.comp, maxCutSideFromCertificate] using hComp
  have hLeftNat :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => boolToNat (maxCutSideFromCertificate p.1 p.2.1)) := by
    have hComp := TMPolyTimeMap.comp boolToNat_tm_polytime hLeftBool
    simpa [Function.comp] using hComp
  have hRightNat :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => boolToNat (maxCutSideFromCertificate p.1 p.2.2)) := by
    have hComp := TMPolyTimeMap.comp boolToNat_tm_polytime hRightBool
    simpa [Function.comp] using hComp
  have hEqInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier =>
          (boolToNat (maxCutSideFromCertificate p.1 p.2.1),
            boolToNat (maxCutSideFromCertificate p.1 p.2.2))) :=
    TMPolyTimeMap.prod_mk hLeftNat hRightNat
  have hEq :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier =>
          decide
            (boolToNat (maxCutSideFromCertificate p.1 p.2.1) =
              boolToNat (maxCutSideFromCertificate p.1 p.2.2))) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hEqInput
    simpa [Function.comp] using hComp
  have hNot := TMPolyTimeMap.comp TMPolyTimeMap.bool_not hEq
  simpa [Function.comp, maxCutEdgeCutBool, X] using hNot

def maxCutEdgeCountInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool
    (EncodedType.prod maxCutCertificateEncodedType edgeStructuredEncodedType)

abbrev MaxCutEdgeCountInstruction :=
  Bool × (MaxCutCertificate × (Nat × Nat))

def maxCutEdgeCountInstructionListEncodedType : EncodedType :=
  EncodedType.list maxCutEdgeCountInstructionEncodedType

def maxCutEdgeCountInputEncodedType : EncodedType :=
  EncodedType.prod maxCutCertificateEncodedType edgeListStructuredEncodedType

def maxCutEdgeCountAccEncodedType : EncodedType :=
  EncodedType.prod maxCutCertificateEncodedType EncodedType.nat

abbrev MaxCutEdgeCountAcc := MaxCutCertificate × Nat

def maxCutEdgeCountInitInstruction
    (bits : MaxCutCertificate) : MaxCutEdgeCountInstruction :=
  (false, (bits, (0, 0)))

def maxCutEdgeCountElementInstruction
    (e : Nat × Nat) : MaxCutEdgeCountInstruction :=
  (true, ([], e))

def maxCutEdgeCountInstructions
    (p : MaxCutCertificate × List (Nat × Nat)) :
    List MaxCutEdgeCountInstruction :=
  maxCutEdgeCountInitInstruction p.1 :: p.2.map maxCutEdgeCountElementInstruction

def maxCutEdgeCountRunnerInit : MaxCutEdgeCountAcc :=
  ([], 0)

def maxCutEdgeCountStep
    (p : MaxCutEdgeCountAcc × MaxCutEdgeCountInstruction) :
    MaxCutEdgeCountAcc :=
  if p.2.1 then
    (p.1.1, p.1.2 + boolToNat (maxCutEdgeCutBool (p.1.1, p.2.2.2)))
  else
    (p.2.2.1, 0)

def maxCutEdgeCountFromInstructions
    (xs : List MaxCutEdgeCountInstruction) : Nat :=
  (xs.foldl (fun acc x => maxCutEdgeCountStep (acc, x))
    maxCutEdgeCountRunnerInit).2

def maxCutCutCount (p : MaxCutCertificate × List (Nat × Nat)) : Nat :=
  maxCutEdgeCountFromInstructions (maxCutEdgeCountInstructions p)

theorem maxCutEdgeCountElementInstructions_fold_eq_cutCount
    (edges : List (Nat × Nat)) (bits : MaxCutCertificate) (count : Nat) :
    ((edges.map maxCutEdgeCountElementInstruction).foldl
        (fun acc instr => maxCutEdgeCountStep (acc, instr)) (bits, count)).2 =
      count + cutCount edges (maxCutSideFromCertificate bits) := by
  induction edges generalizing count with
  | nil =>
      simp [cutCount]
  | cons e edges ih =>
      rw [List.map_cons, List.foldl_cons]
      change
        ((edges.map maxCutEdgeCountElementInstruction).foldl
            (fun acc instr => maxCutEdgeCountStep (acc, instr))
            (bits, count + boolToNat (maxCutEdgeCutBool (bits, e)))).2 =
          count + cutCount (e :: edges) (maxCutSideFromCertificate bits)
      rw [ih]
      by_cases hCut :
          maxCutSideFromCertificate bits e.1 ≠
            maxCutSideFromCertificate bits e.2
      · have hBool : maxCutEdgeCutBool (bits, e) = true :=
          (maxCutEdgeCutBool_eq_true_iff (bits, e)).2 hCut
        simp [cutCount, hCut, hBool, boolToNat, Nat.add_assoc, Nat.add_comm]
      · have hBool : maxCutEdgeCutBool (bits, e) = false := by
          cases h : maxCutEdgeCutBool (bits, e)
          · rfl
          · exact False.elim (hCut ((maxCutEdgeCutBool_eq_true_iff (bits, e)).1 h))
        simp [cutCount, hCut, hBool, boolToNat]

theorem maxCutCutCount_eq_cutCount
    (p : MaxCutCertificate × List (Nat × Nat)) :
    maxCutCutCount p = cutCount p.2 (maxCutSideFromCertificate p.1) := by
  rcases p with ⟨bits, edges⟩
  change
    (((maxCutEdgeCountInitInstruction bits ::
        edges.map maxCutEdgeCountElementInstruction).foldl
          (fun acc instr => maxCutEdgeCountStep (acc, instr))
          maxCutEdgeCountRunnerInit).2) =
      cutCount edges (maxCutSideFromCertificate bits)
  rw [List.foldl_cons]
  simpa [maxCutEdgeCountRunnerInit, maxCutEdgeCountInitInstruction, maxCutEdgeCountStep]
    using maxCutEdgeCountElementInstructions_fold_eq_cutCount edges bits 0

theorem maxCutEdgeCountInitInstruction_tm_polytime :
    TMPolyTimeMap maxCutCertificateEncodedType maxCutEdgeCountInstructionEncodedType
      maxCutEdgeCountInitInstruction := by
  have hFalse :
      TMPolyTimeMap maxCutCertificateEncodedType EncodedType.bool
        (fun _ : MaxCutCertificate => false) :=
    TMPolyTimeMap.const maxCutCertificateEncodedType EncodedType.bool false
  have hBits :
      TMPolyTimeMap maxCutCertificateEncodedType maxCutCertificateEncodedType id :=
    TMPolyTimeMap.id maxCutCertificateEncodedType
  have hDummyEdge :
      TMPolyTimeMap maxCutCertificateEncodedType edgeStructuredEncodedType
        (fun _ : MaxCutCertificate => ((0, 0) : Nat × Nat)) :=
    TMPolyTimeMap.const maxCutCertificateEncodedType edgeStructuredEncodedType
      (show edgeStructuredEncodedType.Carrier from ((0, 0) : Nat × Nat))
  have hPayload :
      TMPolyTimeMap maxCutCertificateEncodedType
        (EncodedType.prod maxCutCertificateEncodedType edgeStructuredEncodedType)
        (fun bits : MaxCutCertificate =>
          (bits, (show edgeStructuredEncodedType.Carrier from ((0, 0) : Nat × Nat)))) :=
    TMPolyTimeMap.prod_mk hBits hDummyEdge
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [maxCutEdgeCountInitInstruction, maxCutEdgeCountInstructionEncodedType] using hOut

theorem maxCutEdgeCountElementInstruction_tm_polytime :
    TMPolyTimeMap edgeStructuredEncodedType maxCutEdgeCountInstructionEncodedType
      maxCutEdgeCountElementInstruction := by
  have hTrue : TMPolyTimeMap edgeStructuredEncodedType EncodedType.bool
      (fun _ : Nat × Nat => true) :=
    TMPolyTimeMap.const edgeStructuredEncodedType EncodedType.bool true
  have hEmpty :
      TMPolyTimeMap edgeStructuredEncodedType maxCutCertificateEncodedType
        (fun _ : Nat × Nat => ([] : List Bool)) :=
    TMPolyTimeMap.const edgeStructuredEncodedType maxCutCertificateEncodedType
      ([] : List Bool)
  have hEdge : TMPolyTimeMap edgeStructuredEncodedType edgeStructuredEncodedType id :=
    TMPolyTimeMap.id edgeStructuredEncodedType
  have hPayload :
      TMPolyTimeMap edgeStructuredEncodedType
        (EncodedType.prod maxCutCertificateEncodedType edgeStructuredEncodedType)
        (fun e : Nat × Nat => (([] : List Bool), e)) :=
    TMPolyTimeMap.prod_mk hEmpty hEdge
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [maxCutEdgeCountElementInstruction, maxCutEdgeCountInstructionEncodedType] using hOut

theorem maxCutEdgeCountInstructions_tm_polytime :
    TMPolyTimeMap maxCutEdgeCountInputEncodedType
      maxCutEdgeCountInstructionListEncodedType maxCutEdgeCountInstructions := by
  let X := maxCutEdgeCountInputEncodedType
  have hBits :
      TMPolyTimeMap X maxCutCertificateEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, maxCutEdgeCountInputEncodedType] using
      TMPolyTimeMap.fst maxCutCertificateEncodedType edgeListStructuredEncodedType
  have hEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, maxCutEdgeCountInputEncodedType] using
      TMPolyTimeMap.snd maxCutCertificateEncodedType edgeListStructuredEncodedType
  have hInit :
      TMPolyTimeMap X maxCutEdgeCountInstructionEncodedType
        (fun p : X.Carrier => maxCutEdgeCountInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp maxCutEdgeCountInitInstruction_tm_polytime hBits
    simpa [Function.comp, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X maxCutEdgeCountInstructionListEncodedType
        (fun p : X.Carrier => [maxCutEdgeCountInitInstruction p.1]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton maxCutEdgeCountInstructionEncodedType) hInit
    simpa [Function.comp, maxCutEdgeCountInstructionListEncodedType, X] using hComp
  have hElementInstructions :
      TMPolyTimeMap X maxCutEdgeCountInstructionListEncodedType
        (fun p : X.Carrier => p.2.map maxCutEdgeCountElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map maxCutEdgeCountElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hEdges
    simpa [Function.comp, maxCutEdgeCountInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod maxCutEdgeCountInstructionListEncodedType
          maxCutEdgeCountInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([maxCutEdgeCountInitInstruction p.1],
            p.2.map maxCutEdgeCountElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hElementInstructions
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append maxCutEdgeCountInstructionEncodedType) hAppendInput
  simpa [Function.comp, maxCutEdgeCountInstructions,
    maxCutEdgeCountInstructionListEncodedType, X] using hOut

theorem maxCutEdgeCountStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod maxCutEdgeCountAccEncodedType maxCutEdgeCountInstructionEncodedType)
      maxCutEdgeCountAccEncodedType
      maxCutEdgeCountStep := by
  let X := EncodedType.prod maxCutEdgeCountAccEncodedType maxCutEdgeCountInstructionEncodedType
  let A := maxCutEdgeCountAccEncodedType
  let Payload := EncodedType.prod maxCutCertificateEncodedType edgeStructuredEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst A maxCutEdgeCountInstructionEncodedType
  have hInstr : TMPolyTimeMap X maxCutEdgeCountInstructionEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd A maxCutEdgeCountInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, maxCutEdgeCountInstructionEncodedType, Payload, X] using hComp
  have hPayload : TMPolyTimeMap X Payload (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, maxCutEdgeCountInstructionEncodedType, Payload, X] using hComp
  have hAccBits : TMPolyTimeMap X maxCutCertificateEncodedType
      (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst maxCutCertificateEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, maxCutEdgeCountAccEncodedType, X] using hComp
  have hAccCount : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd maxCutCertificateEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, maxCutEdgeCountAccEncodedType, X] using hComp
  have hPayloadBits : TMPolyTimeMap X maxCutCertificateEncodedType
      (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst maxCutCertificateEncodedType edgeStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hPayloadEdge : TMPolyTimeMap X edgeStructuredEncodedType
      (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd maxCutCertificateEncodedType edgeStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hEdgeCutInput :
      TMPolyTimeMap X maxCutEdgeCutInputEncodedType
        (fun p : X.Carrier => (p.1.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAccBits hPayloadEdge
  have hEdgeCut :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => maxCutEdgeCutBool (p.1.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp maxCutEdgeCutBool_tm_polytime hEdgeCutInput
    simpa [Function.comp, maxCutEdgeCutInputEncodedType] using hComp
  have hEdgeCutNat :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => boolToNat (maxCutEdgeCutBool (p.1.1, p.2.2.2))) := by
    have hComp := TMPolyTimeMap.comp boolToNat_tm_polytime hEdgeCut
    simpa [Function.comp] using hComp
  have hAddInput :
      TMPolyTimeMap X natAddInputEncodedType
        (fun p : X.Carrier =>
          (p.1.2, boolToNat (maxCutEdgeCutBool (p.1.1, p.2.2.2)))) :=
    TMPolyTimeMap.prod_mk hAccCount hEdgeCutNat
  have hNextCount :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier =>
          (show Nat from p.1.2) + boolToNat (maxCutEdgeCutBool (p.1.1, p.2.2.2))) := by
    have hComp := TMPolyTimeMap.comp natAdd_tm_polytime hAddInput
    simpa [Function.comp, natAddInputEncodedType] using hComp
  have hTrueBranch : TMPolyTimeMap X A
      (fun p : X.Carrier =>
        (p.1.1,
          (show Nat from p.1.2) + boolToNat (maxCutEdgeCutBool (p.1.1, p.2.2.2)))) :=
    TMPolyTimeMap.prod_mk hAccBits hNextCount
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hFalseBranch : TMPolyTimeMap X A
      (fun p : X.Carrier =>
        (p.2.2.1, (show EncodedType.nat.Carrier from (0 : Nat)))) :=
    TMPolyTimeMap.prod_mk hPayloadBits hZero
  have hBranchInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranchOnProduct :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true =>
              (p.2.1.1,
                (show Nat from p.2.1.2) +
                  boolToNat (maxCutEdgeCutBool (p.2.1.1, p.2.2.2.2)))
          | false =>
              (p.2.2.2.1, (show EncodedType.nat.Carrier from (0 : Nat)))) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier =>
        (p.2.2.1, (show EncodedType.nat.Carrier from (0 : Nat))))
      (fTrue := fun p : X.Carrier =>
        (p.1.1,
          (show Nat from p.1.2) + boolToNat (maxCutEdgeCutBool (p.1.1, p.2.2.2))))
      hFalseBranch hTrueBranch
  have hOut := TMPolyTimeMap.comp hBranchOnProduct hBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨bits, count⟩, ⟨tag, payloadBits, edge⟩⟩
  cases tag <;> rfl

theorem maxCutEdgeCountStep_growth
    (source : maxCutEdgeCountInstructionListEncodedType.Carrier)
    (acc : maxCutEdgeCountAccEncodedType.Carrier)
    (instr : maxCutEdgeCountInstructionEncodedType.Carrier)
    (hInstr :
      maxCutEdgeCountInstructionEncodedType.inputSize instr ≤
        maxCutEdgeCountInstructionListEncodedType.inputSize source) :
    maxCutEdgeCountAccEncodedType.inputSize (maxCutEdgeCountStep (acc, instr)) ≤
      maxCutEdgeCountAccEncodedType.inputSize acc +
        (Polynomial.X + Polynomial.C 10).eval
          (maxCutEdgeCountInstructionListEncodedType.inputSize source) := by
  rcases acc with ⟨bits, count⟩
  rcases instr with ⟨tag, payload⟩
  rcases payload with ⟨payloadBits, edge⟩
  cases tag
  · have hLocal :
        maxCutEdgeCountAccEncodedType.inputSize
            (payloadBits, (show EncodedType.nat.Carrier from (0 : Nat))) ≤
          maxCutEdgeCountInstructionEncodedType.inputSize (false, (payloadBits, edge)) + 10 := by
      simp [maxCutEdgeCountAccEncodedType, maxCutEdgeCountInstructionEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_bool,
        EncodedType.inputSize_nat]
      omega
    have hBound :=
      hLocal.trans (Nat.add_le_add_right hInstr 10)
    simpa [maxCutEdgeCountStep, Polynomial.eval_add] using
      hBound.trans (by omega)
  · have hLocal :
        maxCutEdgeCountAccEncodedType.inputSize
            (bits, (show Nat from count) + boolToNat (maxCutEdgeCutBool (bits, edge))) ≤
          maxCutEdgeCountAccEncodedType.inputSize (bits, count) + 1 := by
      cases maxCutEdgeCutBool (bits, edge)
      · simp [maxCutEdgeCountAccEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat, boolToNat]
      · simp [maxCutEdgeCountAccEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat, boolToNat]
        omega
    have hGrow : 1 ≤ (Polynomial.X + Polynomial.C 10).eval
        (maxCutEdgeCountInstructionListEncodedType.inputSize source) := by
      simp [Polynomial.eval_add]
    exact (by
      simpa [maxCutEdgeCountStep] using
        le_trans hLocal (Nat.add_le_add_left hGrow _))

theorem maxCutEdgeCountFold_tm_polytime :
    TMPolyTimeMap maxCutEdgeCountInstructionListEncodedType maxCutEdgeCountAccEncodedType
      (fun xs : maxCutEdgeCountInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc x => maxCutEdgeCountStep (acc, x))
          maxCutEdgeCountRunnerInit) := by
  rcases maxCutEdgeCountStep_tm_polytime with ⟨hStep⟩
  let base : Polynomial Nat := Polynomial.C 10
  let grow : Polynomial Nat := Polynomial.X + Polynomial.C 10
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      maxCutEdgeCountInstructionEncodedType maxCutEdgeCountAccEncodedType
      maxCutEdgeCountStep maxCutEdgeCountRunnerInit hStep base grow ?_ ?_
  · intro xs
    change maxCutEdgeCountAccEncodedType.inputSize maxCutEdgeCountRunnerInit ≤
      (Polynomial.C 10).eval
        (maxCutEdgeCountInstructionEncodedType.list.inputSize xs)
    have hInit : maxCutEdgeCountAccEncodedType.inputSize maxCutEdgeCountRunnerInit ≤ 10 := by
      native_decide
    simpa using hInit
  · intro source acc instr hInstr
    have hInstr' :
        maxCutEdgeCountInstructionEncodedType.inputSize instr ≤
          maxCutEdgeCountInstructionListEncodedType.inputSize source := by
      simpa [maxCutEdgeCountInstructionListEncodedType] using hInstr
    simpa [maxCutEdgeCountInstructionListEncodedType, grow] using
      maxCutEdgeCountStep_growth source acc instr hInstr'

theorem maxCutEdgeCountFromInstructions_tm_polytime :
    TMPolyTimeMap maxCutEdgeCountInstructionListEncodedType EncodedType.nat
      maxCutEdgeCountFromInstructions := by
  have hFold := maxCutEdgeCountFold_tm_polytime
  have hCount := TMPolyTimeMap.snd maxCutCertificateEncodedType EncodedType.nat
  have hComp := TMPolyTimeMap.comp hCount hFold
  simpa [Function.comp, maxCutEdgeCountFromInstructions, maxCutEdgeCountAccEncodedType]
    using hComp

theorem maxCutCutCount_tm_polytime :
    TMPolyTimeMap maxCutEdgeCountInputEncodedType EncodedType.nat
      maxCutCutCount := by
  have hComp := TMPolyTimeMap.comp maxCutEdgeCountFromInstructions_tm_polytime
    maxCutEdgeCountInstructions_tm_polytime
  simpa [Function.comp, maxCutCutCount] using hComp

/-! ### Semantic bridge and finite verifier -/

theorem edge_mem_left_lt_edgeList_inputSize
    {edges : List (Nat × Nat)} {e : Nat × Nat} (he : e ∈ edges) :
    e.1 < edgeListStructuredEncodedType.inputSize edges := by
  have hEdge :=
    Clique.encodedList_element_inputSize_le (X := edgeStructuredEncodedType) he
  have hSize :
      e.1 + e.2 + 3 ≤ edgeListStructuredEncodedType.inputSize edges := by
    simpa [edgeStructuredEncodedType, EncodedType.inputSize, EncodedType.prod,
      EncodedType.nat] using hEdge
  omega

theorem edge_mem_right_lt_edgeList_inputSize
    {edges : List (Nat × Nat)} {e : Nat × Nat} (he : e ∈ edges) :
    e.2 < edgeListStructuredEncodedType.inputSize edges := by
  have hEdge :=
    Clique.encodedList_element_inputSize_le (X := edgeStructuredEncodedType) he
  have hSize :
      e.1 + e.2 + 3 ≤ edgeListStructuredEncodedType.inputSize edges := by
    simpa [edgeStructuredEncodedType, EncodedType.inputSize, EncodedType.prod,
      EncodedType.nat] using hEdge
  omega

theorem edgeList_inputSize_lt_maxCutStructured_inputSize (I : MaxCutInput) :
    edgeListStructuredEncodedType.inputSize I.graph.edges <
      maxCutStructuredEncodedType.inputSize I := by
  rw [maxCutStructured_inputSize_eq, graphStructured_inputSize_eq]
  omega

theorem edge_mem_left_lt_maxCutStructured_inputSize
    (I : MaxCutInput) {e : Nat × Nat} (he : e ∈ I.graph.edges) :
    e.1 < maxCutStructuredEncodedType.inputSize I :=
  lt_trans (edge_mem_left_lt_edgeList_inputSize he)
    (edgeList_inputSize_lt_maxCutStructured_inputSize I)

theorem edge_mem_right_lt_maxCutStructured_inputSize
    (I : MaxCutInput) {e : Nat × Nat} (he : e ∈ I.graph.edges) :
    e.2 < maxCutStructuredEncodedType.inputSize I :=
  lt_trans (edge_mem_right_lt_edgeList_inputSize he)
    (edgeList_inputSize_lt_maxCutStructured_inputSize I)

theorem cutCount_congr_on_edges
    {edges : List (Nat × Nat)} {sideA sideB : Nat → Bool}
    (h :
      ∀ e ∈ edges, sideA e.1 = sideB e.1 ∧ sideA e.2 = sideB e.2) :
    cutCount edges sideA = cutCount edges sideB := by
  unfold cutCount
  apply congrArg List.length
  refine List.filter_congr ?_
  intro e he
  have hEdge := h e he
  simp [hEdge.1, hEdge.2]

theorem cutSize_assignmentPrefix_maxCutInputSize_eq
    (I : MaxCutInput) (side : Nat → Bool) :
    CutSize I.graph
        (SAT.finiteAssignment
          (SAT.assignmentPrefix (maxCutStructuredEncodedType.inputSize I) side)) =
      CutSize I.graph side := by
  change
    cutCount I.graph.edges
        (SAT.finiteAssignment
          (SAT.assignmentPrefix (maxCutStructuredEncodedType.inputSize I) side)) =
      cutCount I.graph.edges side
  apply cutCount_congr_on_edges
  intro e he
  exact
    ⟨SAT.finiteAssignment_assignmentPrefix_of_lt
        (a := side) (edge_mem_left_lt_maxCutStructured_inputSize I he),
      SAT.finiteAssignment_assignmentPrefix_of_lt
        (a := side) (edge_mem_right_lt_maxCutStructured_inputSize I he)⟩

def maxCutStructuredFiniteVerify
    (I : MaxCutInput) (bits : MaxCutCertificate) : Bool :=
  HittingSet.natLeBool (I.threshold, maxCutCutCount (bits, I.graph.edges))

theorem maxCutStructuredFiniteVerify_eq_true_iff
    (I : MaxCutInput) (bits : MaxCutCertificate) :
    maxCutStructuredFiniteVerify I bits = true ↔
      I.threshold ≤ CutSize I.graph (SAT.finiteAssignment bits) := by
  rw [maxCutStructuredFiniteVerify, HittingSet.natLeBool_eq_true_iff,
    maxCutCutCount_eq_cutCount]
  have hSide := maxCutSideFromCertificate_eq_finiteAssignment bits
  change I.threshold ≤ cutCount I.graph.edges (maxCutSideFromCertificate bits) ↔
    I.threshold ≤ CutSize I.graph (SAT.finiteAssignment bits)
  rw [hSide]
  rfl

theorem maxCutStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod maxCutStructuredEncodedType maxCutCertificateEncodedType)
      EncodedType.bool
      (fun p : MaxCutInput × MaxCutCertificate =>
        maxCutStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod maxCutStructuredEncodedType maxCutCertificateEncodedType
  have hInstance :
      TMPolyTimeMap X maxCutStructuredEncodedType
        (fun p : MaxCutInput × MaxCutCertificate => p.1) := by
    simpa [X] using TMPolyTimeMap.fst maxCutStructuredEncodedType maxCutCertificateEncodedType
  have hBits :
      TMPolyTimeMap X maxCutCertificateEncodedType
        (fun p : MaxCutInput × MaxCutCertificate => p.2) := by
    simpa [X] using TMPolyTimeMap.snd maxCutStructuredEncodedType maxCutCertificateEncodedType
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType
        (fun p : MaxCutInput × MaxCutCertificate => p.1.graph) := by
    have hComp := TMPolyTimeMap.comp maxCutGraphTMBackedMap.tm_polytime hInstance
    simpa [Function.comp, X] using hComp
  have hPayload :
      TMPolyTimeMap X graphPayloadStructuredEncodedType
        (fun p : MaxCutInput × MaxCutCertificate => (p.1.graph.edges, p.1.graph.directed)) := by
    have hComp := TMPolyTimeMap.comp graphPayloadTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, graphPayloadOfGraph, X] using hComp
  have hEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : MaxCutInput × MaxCutCertificate => p.1.graph.edges) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, graphPayloadStructuredEncodedType, X] using hComp
  have hThreshold :
      TMPolyTimeMap X EncodedType.nat
        (fun p : MaxCutInput × MaxCutCertificate => p.1.threshold) := by
    have hComp := TMPolyTimeMap.comp maxCutThresholdTMBackedMap.tm_polytime hInstance
    simpa [Function.comp, X] using hComp
  have hCountInput :
      TMPolyTimeMap X maxCutEdgeCountInputEncodedType
        (fun p : MaxCutInput × MaxCutCertificate => (p.2, p.1.graph.edges)) :=
    TMPolyTimeMap.prod_mk hBits hEdges
  have hCount :
      TMPolyTimeMap X EncodedType.nat
        (fun p : MaxCutInput × MaxCutCertificate =>
          maxCutCutCount (p.2, p.1.graph.edges)) := by
    have hComp := TMPolyTimeMap.comp maxCutCutCount_tm_polytime hCountInput
    simpa [Function.comp, maxCutEdgeCountInputEncodedType, X] using hComp
  have hLeInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : MaxCutInput × MaxCutCertificate =>
          (p.1.threshold, maxCutCutCount (p.2, p.1.graph.edges))) :=
    TMPolyTimeMap.prod_mk hThreshold hCount
  have hOut := TMPolyTimeMap.comp HittingSet.natLeBool_tm_polytime hLeInput
  simpa [Function.comp, maxCutStructuredFiniteVerify, X] using hOut

theorem maxCutCertificate_inputSize_le_linear
    (I : MaxCutInput) (side : Nat → Bool) :
    maxCutCertificateEncodedType.inputSize
        (SAT.assignmentPrefix (maxCutStructuredEncodedType.inputSize I) side) ≤
      2 * maxCutStructuredEncodedType.inputSize I := by
  rw [SAT.assignmentPrefix_inputSize]

end MaxCut

/-- Direct finite-certificate TM verifier for faithful structured Max Cut. -/
noncomputable def maxCutStructuredFiniteTMVerifier :
    TMVerifier maxCutStructuredDecisionProblem where
  Cert := MaxCut.maxCutCertificateEncodedType
  verify := MaxCut.maxCutStructuredFiniteVerify
  verifier_polytime := MaxCut.maxCutStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨1, 2, 0, ?_⟩
    intro I hYes
    rcases hYes with ⟨side, hCut⟩
    let bits :=
      SAT.assignmentPrefix (maxCutStructuredEncodedType.inputSize I) side
    refine ⟨bits, ?_, ?_⟩
    · simpa [bits] using MaxCut.maxCutCertificate_inputSize_le_linear I side
    · exact (MaxCut.maxCutStructuredFiniteVerify_eq_true_iff I bits).2
        (by
          simpa [bits, MaxCut.cutSize_assignmentPrefix_maxCutInputSize_eq I side]
            using hCut)
  sound := by
    intro I bits hVerify
    exact ⟨SAT.finiteAssignment bits,
      (MaxCut.maxCutStructuredFiniteVerify_eq_true_iff I bits).1 hVerify⟩

theorem maxCutStructured_TMInNP :
    TMInNP maxCutStructuredDecisionProblem :=
  TMInNP.intro maxCutStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
