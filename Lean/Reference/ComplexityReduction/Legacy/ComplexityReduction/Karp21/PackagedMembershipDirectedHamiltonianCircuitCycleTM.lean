/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipDirectedHamiltonianCircuitCycle

/-!
Direct standard-TM witnesses for the ordered cyclic edge-check runner used by
Directed Hamiltonian Circuit membership.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace DirectedHamiltonianCircuitMembership

theorem cycleEdgesNextVertexAcc_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod cycleEdgesAccEncodedType EncodedType.nat)
      cycleEdgesAccEncodedType
      (fun p : CycleEdgesAcc × Nat => cycleEdgesNextVertexAcc p.1 p.2) := by
  let X := EncodedType.prod cycleEdgesAccEncodedType EncodedType.nat
  let Tail :=
    EncodedType.prod EncodedType.bool
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.bool))
  let FirstPrevOk :=
    EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.bool)
  let PrevOk := EncodedType.prod EncodedType.nat EncodedType.bool
  have hAcc : TMPolyTimeMap X cycleEdgesAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst cycleEdgesAccEncodedType EncodedType.nat
  have hV : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd cycleEdgesAccEncodedType EncodedType.nat
  have hEdges : TMPolyTimeMap X edgeListStructuredEncodedType
      (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType Tail
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, cycleEdgesAccEncodedType, Tail, X] using hComp
  have hTail : TMPolyTimeMap X Tail (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd edgeListStructuredEncodedType Tail
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, cycleEdgesAccEncodedType, Tail, X] using hComp
  have hFirstPrevOk : TMPolyTimeMap X FirstPrevOk
      (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool FirstPrevOk
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, Tail, FirstPrevOk, X] using hComp
  have hFirst : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.1.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat PrevOk
    have hComp := TMPolyTimeMap.comp hFst hFirstPrevOk
    simpa [Function.comp, FirstPrevOk, PrevOk, X] using hComp
  have hPrevOk : TMPolyTimeMap X PrevOk
      (fun p : X.Carrier => p.1.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat PrevOk
    have hComp := TMPolyTimeMap.comp hSnd hFirstPrevOk
    simpa [Function.comp, FirstPrevOk, PrevOk, X] using hComp
  have hPrev : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.1.2.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hPrevOk
    simpa [Function.comp, PrevOk, X] using hComp
  have hOk : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => p.1.2.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hPrevOk
    simpa [Function.comp, PrevOk, X] using hComp
  have hPair : TMPolyTimeMap X vertexPairEncodedType
      (fun p : X.Carrier => (p.1.2.2.2.1, p.2)) :=
    TMPolyTimeMap.prod_mk hPrev hV
  have hEdgeInput :
      TMPolyTimeMap X (EncodedType.prod vertexPairEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier => ((p.1.2.2.2.1, p.2), p.1.1)) :=
    TMPolyTimeMap.prod_mk hPair hEdges
  have hHasEdge : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        sourceHasDirectedEdgeBool ((p.1.2.2.2.1, p.2), p.1.1)) := by
    have hComp := TMPolyTimeMap.comp sourceHasDirectedEdgeBool_tm_polytime hEdgeInput
    simpa [Function.comp, X] using hComp
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (p.1.2.2.2.2,
            sourceHasDirectedEdgeBool ((p.1.2.2.2.1, p.2), p.1.1))) :=
    TMPolyTimeMap.prod_mk hOk hHasEdge
  have hNextOk : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair
          (p.1.2.2.2.2,
            sourceHasDirectedEdgeBool ((p.1.2.2.2.1, p.2), p.1.1))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
    simpa [Function.comp, X] using hComp
  have hTrue : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hPrevOkOut : TMPolyTimeMap X PrevOk
      (fun p : X.Carrier =>
        (p.2,
          graphBoolAndPair
            (p.1.2.2.2.2,
              sourceHasDirectedEdgeBool ((p.1.2.2.2.1, p.2), p.1.1)))) :=
    TMPolyTimeMap.prod_mk hV hNextOk
  have hFirstPrevOkOut : TMPolyTimeMap X FirstPrevOk
      (fun p : X.Carrier =>
        (p.1.2.2.1,
          (p.2,
            graphBoolAndPair
              (p.1.2.2.2.2,
                sourceHasDirectedEdgeBool ((p.1.2.2.2.1, p.2), p.1.1))))) :=
    TMPolyTimeMap.prod_mk hFirst hPrevOkOut
  have hTailOut : TMPolyTimeMap X Tail
      (fun p : X.Carrier =>
        (true,
          (p.1.2.2.1,
            (p.2,
              graphBoolAndPair
                (p.1.2.2.2.2,
                  sourceHasDirectedEdgeBool ((p.1.2.2.2.1, p.2), p.1.1)))))) :=
    TMPolyTimeMap.prod_mk hTrue hFirstPrevOkOut
  have hOut := TMPolyTimeMap.prod_mk hEdges hTailOut
  simpa [cycleEdgesNextVertexAcc, cycleEdgesAcc.edges, cycleEdgesAcc.first,
    cycleEdgesAcc.prev, cycleEdgesAcc.ok, cycleEdgesAccEncodedType, Tail, FirstPrevOk,
    PrevOk, X] using hOut

theorem cycleEdgesFirstVertexAcc_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod cycleEdgesAccEncodedType EncodedType.nat)
      cycleEdgesAccEncodedType
      (fun p : CycleEdgesAcc × Nat => cycleEdgesFirstVertexAcc (cycleEdgesAcc.edges p.1) p.2) := by
  let X := EncodedType.prod cycleEdgesAccEncodedType EncodedType.nat
  let Tail :=
    EncodedType.prod EncodedType.bool
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.bool))
  let FirstPrevOk :=
    EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.bool)
  let PrevOk := EncodedType.prod EncodedType.nat EncodedType.bool
  have hAcc : TMPolyTimeMap X cycleEdgesAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst cycleEdgesAccEncodedType EncodedType.nat
  have hV : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd cycleEdgesAccEncodedType EncodedType.nat
  have hEdges : TMPolyTimeMap X edgeListStructuredEncodedType
      (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType Tail
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, cycleEdgesAccEncodedType, Tail, X] using hComp
  have hTrue : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hPrevOk : TMPolyTimeMap X PrevOk (fun p : X.Carrier => (p.2, true)) :=
    TMPolyTimeMap.prod_mk hV hTrue
  have hFirstPrevOk : TMPolyTimeMap X FirstPrevOk
      (fun p : X.Carrier => (p.2, (p.2, true))) :=
    TMPolyTimeMap.prod_mk hV hPrevOk
  have hTail : TMPolyTimeMap X Tail
      (fun p : X.Carrier => (true, (p.2, (p.2, true)))) :=
    TMPolyTimeMap.prod_mk hTrue hFirstPrevOk
  have hOut := TMPolyTimeMap.prod_mk hEdges hTail
  simpa [cycleEdgesFirstVertexAcc, cycleEdgesAcc.edges, cycleEdgesAccEncodedType, Tail,
    FirstPrevOk, PrevOk, X] using hOut

theorem cycleEdgesVertexStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod cycleEdgesAccEncodedType EncodedType.nat)
      cycleEdgesAccEncodedType
      (fun p : CycleEdgesAcc × Nat => cycleEdgesVertexStep p.1 p.2) := by
  let X := EncodedType.prod cycleEdgesAccEncodedType EncodedType.nat
  let Tail :=
    EncodedType.prod EncodedType.bool
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.bool))
  have hAcc : TMPolyTimeMap X cycleEdgesAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst cycleEdgesAccEncodedType EncodedType.nat
  have hTail : TMPolyTimeMap X Tail (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd edgeListStructuredEncodedType Tail
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, cycleEdgesAccEncodedType, Tail, X] using hComp
  have hSeen : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.bool))
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, Tail, X] using hComp
  have hBranchInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun p : X.Carrier => (p.1.2.1, p)) :=
    TMPolyTimeMap.prod_mk hSeen (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) cycleEdgesAccEncodedType
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true => cycleEdgesNextVertexAcc p.2.1 p.2.2
          | false => cycleEdgesFirstVertexAcc (cycleEdgesAcc.edges p.2.1) p.2.2) :=
    graphBoolProduct_dispatch_tm_polytime X cycleEdgesAccEncodedType
      (fFalse := fun p : X.Carrier =>
        cycleEdgesFirstVertexAcc (cycleEdgesAcc.edges p.1) p.2)
      (fTrue := fun p : X.Carrier => cycleEdgesNextVertexAcc p.1 p.2)
      cycleEdgesFirstVertexAcc_tm_polytime cycleEdgesNextVertexAcc_tm_polytime
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨acc, v⟩
  rcases acc with ⟨edges, seen, first, prev, ok⟩
  cases seen <;> rfl

theorem cycleEdgesStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod cycleEdgesAccEncodedType cycleEdgesInstructionEncodedType)
      cycleEdgesAccEncodedType
      cycleEdgesStep := by
  let X := EncodedType.prod cycleEdgesAccEncodedType cycleEdgesInstructionEncodedType
  let Payload := EncodedType.prod edgeListStructuredEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X cycleEdgesAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst cycleEdgesAccEncodedType cycleEdgesInstructionEncodedType
  have hInstr : TMPolyTimeMap X cycleEdgesInstructionEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd cycleEdgesAccEncodedType cycleEdgesInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, cycleEdgesInstructionEncodedType, Payload, X] using hComp
  have hPayload : TMPolyTimeMap X Payload (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, cycleEdgesInstructionEncodedType, Payload, X] using hComp
  have hPayloadEdges : TMPolyTimeMap X edgeListStructuredEncodedType
      (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hPayloadNat : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd edgeListStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hVertexInput :
      TMPolyTimeMap X (EncodedType.prod cycleEdgesAccEncodedType EncodedType.nat)
        (fun p : X.Carrier => (p.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAcc hPayloadNat
  have hVertex :
      TMPolyTimeMap X cycleEdgesAccEncodedType
        (fun p : X.Carrier => cycleEdgesVertexStep p.1 p.2.2.2) := by
    have hComp := TMPolyTimeMap.comp cycleEdgesVertexStep_tm_polytime hVertexInput
    simpa [Function.comp, X] using hComp
  have hFalse : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hTrue : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hPrevOk :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.bool)
        (fun _ : X.Carrier => ((0 : Nat), true)) :=
    TMPolyTimeMap.prod_mk hZero hTrue
  have hFirstPrevOk :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat EncodedType.bool))
        (fun _ : X.Carrier => ((0 : Nat), ((0 : Nat), true))) :=
    TMPolyTimeMap.prod_mk hZero hPrevOk
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod EncodedType.nat
            (EncodedType.prod EncodedType.nat EncodedType.bool)))
        (fun _ : X.Carrier => (false, ((0 : Nat), ((0 : Nat), true)))) :=
    TMPolyTimeMap.prod_mk hFalse hFirstPrevOk
  have hInitOut : TMPolyTimeMap X cycleEdgesAccEncodedType
      (fun p : X.Carrier => (p.2.2.1, false, (0 : Nat), (0 : Nat), true)) := by
    have hOut := TMPolyTimeMap.prod_mk hPayloadEdges hTail
    simpa [cycleEdgesAccEncodedType] using hOut
  have hBranchInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) cycleEdgesAccEncodedType
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true => cycleEdgesVertexStep p.2.1 p.2.2.2.2
          | false => (p.2.2.2.1, false, (0 : Nat), (0 : Nat), true)) :=
    graphBoolProduct_dispatch_tm_polytime X cycleEdgesAccEncodedType
      (fFalse := fun p : X.Carrier =>
        (p.2.2.1, false, (0 : Nat), (0 : Nat), true))
      (fTrue := fun p : X.Carrier => cycleEdgesVertexStep p.1 p.2.2.2)
      hInitOut hVertex
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨acc, tag, payloadEdges, payloadNat⟩
  cases tag <;> rfl

theorem cycleEdgesStep_growth
    (source : cycleEdgesInstructionListEncodedType.Carrier)
    (acc : cycleEdgesAccEncodedType.Carrier)
    (instr : cycleEdgesInstructionEncodedType.Carrier)
    (hInstr :
      cycleEdgesInstructionEncodedType.inputSize instr ≤
        cycleEdgesInstructionListEncodedType.inputSize source) :
    cycleEdgesAccEncodedType.inputSize (cycleEdgesStep (acc, instr)) ≤
      cycleEdgesAccEncodedType.inputSize acc +
        (Polynomial.C 10 * Polynomial.X + Polynomial.C 50).eval
          (cycleEdgesInstructionListEncodedType.inputSize source) := by
  rcases acc with ⟨edges, seen, first, prev, ok⟩
  rcases instr with ⟨tag, payloadEdges, payloadNat⟩
  cases tag <;> cases seen <;>
    simp [cycleEdgesStep, cycleEdgesVertexStep, cycleEdgesFirstVertexAcc,
      cycleEdgesNextVertexAcc, cycleEdgesAcc.edges, cycleEdgesAcc.seen, cycleEdgesAcc.first,
      cycleEdgesAcc.prev, cycleEdgesAcc.ok, cycleEdgesAccEncodedType,
      cycleEdgesInstructionEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_bool,
      EncodedType.inputSize_nat, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X] at hInstr ⊢ <;>
    omega

theorem cycleEdgesFold_tm_polytime :
    TMPolyTimeMap
      cycleEdgesInstructionListEncodedType
      cycleEdgesAccEncodedType
      (fun xs : cycleEdgesInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc instr => cycleEdgesStep (acc, instr)) cycleEdgesInitAcc) := by
  rcases cycleEdgesStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      cycleEdgesInstructionEncodedType cycleEdgesAccEncodedType
      cycleEdgesStep cycleEdgesInitAcc hStep
      (Polynomial.C 20) (Polynomial.C 10 * Polynomial.X + Polynomial.C 50) ?_ ?_
  · intro xs
    have hInit : cycleEdgesAccEncodedType.inputSize cycleEdgesInitAcc ≤ 20 := by
      native_decide
    simpa [cycleEdgesInstructionListEncodedType] using hInit
  · intro source acc instr hInstr
    exact cycleEdgesStep_growth source acc instr hInstr

theorem cycleEdgesClosingOK_tm_polytime :
    TMPolyTimeMap cycleEdgesAccEncodedType EncodedType.bool
      cycleEdgesClosingOK := by
  let X := cycleEdgesAccEncodedType
  let Tail :=
    EncodedType.prod EncodedType.bool
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.bool))
  let FirstPrevOk :=
    EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.bool)
  let PrevOk := EncodedType.prod EncodedType.nat EncodedType.bool
  have hId : TMPolyTimeMap X X id := TMPolyTimeMap.id X
  have hEdges : TMPolyTimeMap X edgeListStructuredEncodedType (fun acc : X.Carrier => acc.1) := by
    simpa [X, cycleEdgesAccEncodedType, Tail] using
      TMPolyTimeMap.fst edgeListStructuredEncodedType Tail
  have hTail : TMPolyTimeMap X Tail (fun acc : X.Carrier => acc.2) := by
    simpa [X, cycleEdgesAccEncodedType, Tail] using
      TMPolyTimeMap.snd edgeListStructuredEncodedType Tail
  have hSeen : TMPolyTimeMap X EncodedType.bool (fun acc : X.Carrier => acc.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool FirstPrevOk
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, Tail, FirstPrevOk, X] using hComp
  have hFirstPrevOk : TMPolyTimeMap X FirstPrevOk
      (fun acc : X.Carrier => acc.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool FirstPrevOk
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, Tail, FirstPrevOk, X] using hComp
  have hFirst : TMPolyTimeMap X EncodedType.nat
      (fun acc : X.Carrier => acc.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat PrevOk
    have hComp := TMPolyTimeMap.comp hFst hFirstPrevOk
    simpa [Function.comp, FirstPrevOk, PrevOk, X] using hComp
  have hPrevOk : TMPolyTimeMap X PrevOk
      (fun acc : X.Carrier => acc.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat PrevOk
    have hComp := TMPolyTimeMap.comp hSnd hFirstPrevOk
    simpa [Function.comp, FirstPrevOk, PrevOk, X] using hComp
  have hPrev : TMPolyTimeMap X EncodedType.nat
      (fun acc : X.Carrier => acc.2.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hPrevOk
    simpa [Function.comp, PrevOk, X] using hComp
  have hOk : TMPolyTimeMap X EncodedType.bool
      (fun acc : X.Carrier => acc.2.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hPrevOk
    simpa [Function.comp, PrevOk, X] using hComp
  have hPair : TMPolyTimeMap X vertexPairEncodedType
      (fun acc : X.Carrier => (acc.2.2.2.1, acc.2.2.1)) :=
    TMPolyTimeMap.prod_mk hPrev hFirst
  have hEdgeInput :
      TMPolyTimeMap X (EncodedType.prod vertexPairEncodedType edgeListStructuredEncodedType)
        (fun acc : X.Carrier => ((acc.2.2.2.1, acc.2.2.1), acc.1)) :=
    TMPolyTimeMap.prod_mk hPair hEdges
  have hHasEdge : TMPolyTimeMap X EncodedType.bool
      (fun acc : X.Carrier =>
        sourceHasDirectedEdgeBool ((acc.2.2.2.1, acc.2.2.1), acc.1)) := by
    have hComp := TMPolyTimeMap.comp sourceHasDirectedEdgeBool_tm_polytime hEdgeInput
    simpa [Function.comp, X] using hComp
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun acc : X.Carrier =>
          (acc.2.2.2.2,
            sourceHasDirectedEdgeBool ((acc.2.2.2.1, acc.2.2.1), acc.1))) :=
    TMPolyTimeMap.prod_mk hOk hHasEdge
  have hTrueBranch : TMPolyTimeMap X EncodedType.bool
      (fun acc : X.Carrier =>
        graphBoolAndPair
          (acc.2.2.2.2,
            sourceHasDirectedEdgeBool ((acc.2.2.2.1, acc.2.2.1), acc.1))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
    simpa [Function.comp, X] using hComp
  have hFalseBranch : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hBranchInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun acc : X.Carrier => (acc.2.1, acc)) :=
    TMPolyTimeMap.prod_mk hSeen hId
  have hBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) EncodedType.bool
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true =>
              graphBoolAndPair
                (p.2.2.2.2.2,
                  sourceHasDirectedEdgeBool ((p.2.2.2.2.1, p.2.2.2.1), p.2.1))
          | false => true) :=
    graphBoolProduct_dispatch_tm_polytime X EncodedType.bool
      (fFalse := fun _ : X.Carrier => true)
      (fTrue := fun acc : X.Carrier =>
        graphBoolAndPair
          (acc.2.2.2.2,
            sourceHasDirectedEdgeBool ((acc.2.2.2.1, acc.2.2.1), acc.1)))
      hFalseBranch hTrueBranch
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext acc
  rcases acc with ⟨edges, seen, first, prev, ok⟩
  cases seen <;> rfl

theorem cycleEdgesFromInstructions_tm_polytime :
    TMPolyTimeMap cycleEdgesInstructionListEncodedType EncodedType.bool
      cycleEdgesFromInstructions := by
  have hFold := cycleEdgesFold_tm_polytime
  have hComp := TMPolyTimeMap.comp cycleEdgesClosingOK_tm_polytime hFold
  simpa [Function.comp, cycleEdgesFromInstructions] using hComp

theorem cycleEdgesOKBool_tm_polytime :
    TMPolyTimeMap cycleEdgesInputEncodedType EncodedType.bool
      cycleEdgesOKBool := by
  have hComp := TMPolyTimeMap.comp cycleEdgesFromInstructions_tm_polytime
    cycleEdgesInstructions_tm_polytime
  simpa [Function.comp, cycleEdgesOKBool] using hComp

end DirectedHamiltonianCircuitMembership
end Karp21
end ComplexityReduction
