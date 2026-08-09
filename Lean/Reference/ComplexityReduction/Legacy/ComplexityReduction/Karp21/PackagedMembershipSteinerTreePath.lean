/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSteinerTreeEdgeScan
import Mathlib.Tactic

/-!
Boolean path checker for faithful structured Steiner Tree membership.

A path certificate is a list of vertices.  The checker verifies that the list is
nonempty, starts at the declared root, ends at the declared terminal, and that
each consecutive vertex pair is adjacent through one selected weighted edge.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace SteinerTreeMembership

def steinerPathContextEncodedType : EncodedType :=
  EncodedType.prod
    (EncodedType.prod weightedEdgeListStructuredEncodedType EncodedType.bool)
    (EncodedType.prod EncodedType.nat EncodedType.nat)

abbrev SteinerPathContext :=
  (List (Nat × Nat × Nat) × Bool) × (Nat × Nat)

abbrev SteinerPathAcc :=
  SteinerPathContext × (Bool × (Nat × Bool))

def steinerPathAccEncodedType : EncodedType :=
  EncodedType.prod steinerPathContextEncodedType
    (EncodedType.prod EncodedType.bool
      (EncodedType.prod EncodedType.nat EncodedType.bool))

def steinerPathInstructionEncodedType : EncodedType :=
  EncodedType.sum steinerPathContextEncodedType EncodedType.nat

def steinerPathInstructionListEncodedType : EncodedType :=
  EncodedType.list steinerPathInstructionEncodedType

def steinerPathInputEncodedType : EncodedType :=
  EncodedType.prod steinerPathContextEncodedType (EncodedType.list EncodedType.nat)

def steinerPathInitAcc : SteinerPathAcc :=
  (((([] : List (Nat × Nat × Nat)), false), (0, 0)), (false, (0, true)))

def steinerPathInitInstruction
    (ctx : SteinerPathContext) : steinerPathInstructionEncodedType.Carrier :=
  Sum.inl ctx

def steinerPathVertexInstruction (v : Nat) : steinerPathInstructionEncodedType.Carrier :=
  Sum.inr v

def steinerPathInstructions (p : SteinerPathContext × List Nat) :
    List steinerPathInstructionEncodedType.Carrier :=
  steinerPathInitInstruction p.1 :: p.2.map steinerPathVertexInstruction

def steinerPathAcc.ctx (acc : SteinerPathAcc) : SteinerPathContext := acc.1
def steinerPathAcc.seen (acc : SteinerPathAcc) : Bool := acc.2.1
def steinerPathAcc.prev (acc : SteinerPathAcc) : Nat := acc.2.2.1
def steinerPathAcc.ok (acc : SteinerPathAcc) : Bool := acc.2.2.2

def steinerPathFirstVertexAcc (ctx : SteinerPathContext) (v : Nat) (ok : Bool) :
    SteinerPathAcc :=
  (ctx, (true, (v, graphBoolAndPair (ok, natEqBool (v, ctx.2.1)))))

def steinerPathNextVertexAcc (acc : SteinerPathAcc) (v : Nat) : SteinerPathAcc :=
  let ctx := steinerPathAcc.ctx acc
  (ctx, (true, (v,
    graphBoolAndPair
      (steinerPathAcc.ok acc,
        weightedAdjacentBool ((ctx.1, (steinerPathAcc.prev acc, v)))))))

def steinerPathVertexStep (acc : SteinerPathAcc) (v : Nat) : SteinerPathAcc :=
  if steinerPathAcc.seen acc then
    steinerPathNextVertexAcc acc v
  else
    steinerPathFirstVertexAcc (steinerPathAcc.ctx acc) v (steinerPathAcc.ok acc)

def steinerPathStep
    (p : SteinerPathAcc × steinerPathInstructionEncodedType.Carrier) : SteinerPathAcc :=
  match p.2 with
  | Sum.inl ctx => (ctx, (false, (0, true)))
  | Sum.inr v => steinerPathVertexStep p.1 v

def steinerPathClosingOK (acc : SteinerPathAcc) : Bool :=
  if steinerPathAcc.seen acc then
    graphBoolAndPair
      (steinerPathAcc.ok acc,
        natEqBool (steinerPathAcc.prev acc, (steinerPathAcc.ctx acc).2.2))
  else
    false

def steinerPathFromInstructions
    (xs : List steinerPathInstructionEncodedType.Carrier) : Bool :=
  steinerPathClosingOK
    (xs.foldl (fun acc instr => steinerPathStep (acc, instr)) steinerPathInitAcc)

def steinerPathBool (p : SteinerPathContext × List Nat) : Bool :=
  steinerPathFromInstructions (steinerPathInstructions p)

/-! ### Direct standard-TM witnesses for the path checker -/

theorem steinerPathInitInstruction_tm_polytime :
    TMPolyTimeMap steinerPathContextEncodedType steinerPathInstructionEncodedType
      steinerPathInitInstruction := by
  simpa [steinerPathInitInstruction, steinerPathInstructionEncodedType] using
    TMPolyTimeMap.inl steinerPathContextEncodedType EncodedType.nat

theorem steinerPathVertexInstruction_tm_polytime :
    TMPolyTimeMap EncodedType.nat steinerPathInstructionEncodedType
      steinerPathVertexInstruction := by
  simpa [steinerPathVertexInstruction, steinerPathInstructionEncodedType] using
    TMPolyTimeMap.inr steinerPathContextEncodedType EncodedType.nat

theorem steinerPathInstructions_tm_polytime :
    TMPolyTimeMap steinerPathInputEncodedType steinerPathInstructionListEncodedType
      steinerPathInstructions := by
  let X := steinerPathInputEncodedType
  have hCtx : TMPolyTimeMap X steinerPathContextEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, steinerPathInputEncodedType] using
      TMPolyTimeMap.fst steinerPathContextEncodedType (EncodedType.list EncodedType.nat)
  have hPath : TMPolyTimeMap X (EncodedType.list EncodedType.nat)
      (fun p : X.Carrier => p.2) := by
    simpa [X, steinerPathInputEncodedType] using
      TMPolyTimeMap.snd steinerPathContextEncodedType (EncodedType.list EncodedType.nat)
  have hInit : TMPolyTimeMap X steinerPathInstructionEncodedType
      (fun p : X.Carrier => steinerPathInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp steinerPathInitInstruction_tm_polytime hCtx
    simpa [Function.comp, X] using hComp
  have hInitSingleton : TMPolyTimeMap X steinerPathInstructionListEncodedType
      (fun p : X.Carrier => [steinerPathInitInstruction p.1]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton steinerPathInstructionEncodedType) hInit
    simpa [Function.comp, steinerPathInstructionListEncodedType, X] using hComp
  have hElements : TMPolyTimeMap X steinerPathInstructionListEncodedType
      (fun p : X.Carrier => p.2.map steinerPathVertexInstruction) := by
    have hMap := TMPolyTimeMap.list_map steinerPathVertexInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hPath
    simpa [Function.comp, steinerPathInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod steinerPathInstructionListEncodedType
          steinerPathInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([steinerPathInitInstruction p.1], p.2.map steinerPathVertexInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hElements
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append steinerPathInstructionEncodedType) hAppendInput
  simpa [Function.comp, steinerPathInstructions, steinerPathInstructionListEncodedType, X]
    using hAppend

theorem steinerPathFirstVertexAcc_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod steinerPathAccEncodedType EncodedType.nat)
      steinerPathAccEncodedType
      (fun p : SteinerPathAcc × Nat =>
        steinerPathFirstVertexAcc (steinerPathAcc.ctx p.1) p.2 (steinerPathAcc.ok p.1)) := by
  let X := EncodedType.prod steinerPathAccEncodedType EncodedType.nat
  let Tail := EncodedType.prod EncodedType.bool
    (EncodedType.prod EncodedType.nat EncodedType.bool)
  let RootTarget := EncodedType.prod EncodedType.nat EncodedType.nat
  let GraphCtx := EncodedType.prod weightedEdgeListStructuredEncodedType EncodedType.bool
  have hAcc : TMPolyTimeMap X steinerPathAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst steinerPathAccEncodedType EncodedType.nat
  have hV : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd steinerPathAccEncodedType EncodedType.nat
  have hCtx : TMPolyTimeMap X steinerPathContextEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst steinerPathContextEncodedType Tail
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, steinerPathAccEncodedType, Tail, X] using hComp
  have hAccTail : TMPolyTimeMap X Tail (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd steinerPathContextEncodedType Tail
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, steinerPathAccEncodedType, Tail, X] using hComp
  have hPrevOk : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.bool)
      (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool
      (EncodedType.prod EncodedType.nat EncodedType.bool)
    have hComp := TMPolyTimeMap.comp hSnd hAccTail
    simpa [Function.comp, Tail, X] using hComp
  have hOk : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hPrevOk
    simpa [Function.comp, X] using hComp
  have hRootTarget : TMPolyTimeMap X RootTarget (fun p : X.Carrier => p.1.1.2) := by
    have hSnd := TMPolyTimeMap.snd GraphCtx RootTarget
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, steinerPathContextEncodedType, GraphCtx, RootTarget, X] using hComp
  have hRoot : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hRootTarget
    simpa [Function.comp, RootTarget, X] using hComp
  have hEqInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => (p.2, p.1.1.2.1)) :=
    TMPolyTimeMap.prod_mk hV hRoot
  have hEq : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => natEqBool (p.2, p.1.1.2.1)) := by
    have hComp := TMPolyTimeMap.comp natEqBool_tm_polytime hEqInput
    simpa [Function.comp, X] using hComp
  have hAndInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier => (p.1.2.2.2, natEqBool (p.2, p.1.1.2.1))) :=
    TMPolyTimeMap.prod_mk hOk hEq
  have hAnd : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => graphBoolAndPair (p.1.2.2.2, natEqBool (p.2, p.1.1.2.1))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
    simpa [Function.comp, X] using hComp
  have hTrue : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hPrevOkOut : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.bool)
      (fun p : X.Carrier =>
        (p.2, graphBoolAndPair (p.1.2.2.2, natEqBool (p.2, p.1.1.2.1)))) :=
    TMPolyTimeMap.prod_mk hV hAnd
  have hTailOut : TMPolyTimeMap X Tail
      (fun p : X.Carrier =>
        (true, (p.2, graphBoolAndPair (p.1.2.2.2, natEqBool (p.2, p.1.1.2.1))))) :=
    TMPolyTimeMap.prod_mk hTrue hPrevOkOut
  have hOut := TMPolyTimeMap.prod_mk hCtx hTailOut
  simpa [steinerPathFirstVertexAcc, steinerPathAcc.ctx, steinerPathAcc.ok,
    steinerPathAccEncodedType, Tail, RootTarget, GraphCtx, X] using hOut

theorem steinerPathNextVertexAcc_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod steinerPathAccEncodedType EncodedType.nat)
      steinerPathAccEncodedType
      (fun p : SteinerPathAcc × Nat => steinerPathNextVertexAcc p.1 p.2) := by
  let X := EncodedType.prod steinerPathAccEncodedType EncodedType.nat
  let Tail := EncodedType.prod EncodedType.bool
    (EncodedType.prod EncodedType.nat EncodedType.bool)
  let GraphCtx := EncodedType.prod weightedEdgeListStructuredEncodedType EncodedType.bool
  let PrevOk := EncodedType.prod EncodedType.nat EncodedType.bool
  have hAcc : TMPolyTimeMap X steinerPathAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst steinerPathAccEncodedType EncodedType.nat
  have hV : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd steinerPathAccEncodedType EncodedType.nat
  have hCtx : TMPolyTimeMap X steinerPathContextEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst steinerPathContextEncodedType Tail
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, steinerPathAccEncodedType, Tail, X] using hComp
  have hGraphCtx : TMPolyTimeMap X GraphCtx (fun p : X.Carrier => p.1.1.1) := by
    have hFst := TMPolyTimeMap.fst GraphCtx (EncodedType.prod EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hFst hCtx
    simpa [Function.comp, steinerPathContextEncodedType, GraphCtx, X] using hComp
  have hAccTail : TMPolyTimeMap X Tail (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd steinerPathContextEncodedType Tail
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, steinerPathAccEncodedType, Tail, X] using hComp
  have hPrevOk : TMPolyTimeMap X PrevOk (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool PrevOk
    have hComp := TMPolyTimeMap.comp hSnd hAccTail
    simpa [Function.comp, Tail, PrevOk, X] using hComp
  have hPrev : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hPrevOk
    simpa [Function.comp, PrevOk, X] using hComp
  have hOk : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hPrevOk
    simpa [Function.comp, PrevOk, X] using hComp
  have hPair : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => (p.1.2.2.1, p.2)) :=
    TMPolyTimeMap.prod_mk hPrev hV
  have hAdjacentInput : TMPolyTimeMap X weightedAdjacentInputEncodedType
      (fun p : X.Carrier => (p.1.1.1, (p.1.2.2.1, p.2))) :=
    TMPolyTimeMap.prod_mk hGraphCtx hPair
  have hAdjacent : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => weightedAdjacentBool (p.1.1.1, (p.1.2.2.1, p.2))) := by
    have hComp := TMPolyTimeMap.comp weightedAdjacentBool_tm_polytime hAdjacentInput
    simpa [Function.comp, weightedAdjacentInputEncodedType, X] using hComp
  have hAndInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier =>
        (p.1.2.2.2, weightedAdjacentBool (p.1.1.1, (p.1.2.2.1, p.2)))) :=
    TMPolyTimeMap.prod_mk hOk hAdjacent
  have hAnd : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair (p.1.2.2.2, weightedAdjacentBool (p.1.1.1, (p.1.2.2.1, p.2)))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
    simpa [Function.comp, X] using hComp
  have hTrue : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hPrevOkOut : TMPolyTimeMap X PrevOk
      (fun p : X.Carrier =>
        (p.2,
          graphBoolAndPair
            (p.1.2.2.2, weightedAdjacentBool (p.1.1.1, (p.1.2.2.1, p.2))))) :=
    TMPolyTimeMap.prod_mk hV hAnd
  have hTailOut : TMPolyTimeMap X Tail
      (fun p : X.Carrier =>
        (true,
          (p.2,
            graphBoolAndPair
              (p.1.2.2.2, weightedAdjacentBool (p.1.1.1, (p.1.2.2.1, p.2)))))) :=
    TMPolyTimeMap.prod_mk hTrue hPrevOkOut
  have hOut := TMPolyTimeMap.prod_mk hCtx hTailOut
  simpa [steinerPathNextVertexAcc, steinerPathAcc.ctx, steinerPathAcc.prev,
    steinerPathAcc.ok, steinerPathAccEncodedType, Tail, GraphCtx, PrevOk, X] using hOut

theorem steinerPathVertexStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod steinerPathAccEncodedType EncodedType.nat)
      steinerPathAccEncodedType
      (fun p : SteinerPathAcc × Nat => steinerPathVertexStep p.1 p.2) := by
  let X := EncodedType.prod steinerPathAccEncodedType EncodedType.nat
  let Tail := EncodedType.prod EncodedType.bool
    (EncodedType.prod EncodedType.nat EncodedType.bool)
  have hAcc : TMPolyTimeMap X steinerPathAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst steinerPathAccEncodedType EncodedType.nat
  have hTail : TMPolyTimeMap X Tail (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd steinerPathContextEncodedType Tail
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, steinerPathAccEncodedType, Tail, X] using hComp
  have hSeen : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool
      (EncodedType.prod EncodedType.nat EncodedType.bool)
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, Tail, X] using hComp
  have hBranchInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun p : X.Carrier => (p.1.2.1, p)) :=
    TMPolyTimeMap.prod_mk hSeen (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) steinerPathAccEncodedType
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true => steinerPathNextVertexAcc p.2.1 p.2.2
          | false => steinerPathFirstVertexAcc (steinerPathAcc.ctx p.2.1) p.2.2
              (steinerPathAcc.ok p.2.1)) :=
    graphBoolProduct_dispatch_tm_polytime X steinerPathAccEncodedType
      (fFalse := fun p : X.Carrier =>
        steinerPathFirstVertexAcc (steinerPathAcc.ctx p.1) p.2 (steinerPathAcc.ok p.1))
      (fTrue := fun p : X.Carrier => steinerPathNextVertexAcc p.1 p.2)
      steinerPathFirstVertexAcc_tm_polytime steinerPathNextVertexAcc_tm_polytime
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨acc, v⟩
  rcases acc with ⟨ctx, seen, prev, ok⟩
  cases seen <;> rfl

theorem steinerPathStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod steinerPathAccEncodedType steinerPathInstructionEncodedType)
      steinerPathAccEncodedType
      steinerPathStep := by
  let A := steinerPathAccEncodedType
  let C := steinerPathContextEncodedType
  let Instr := steinerPathInstructionEncodedType
  let X := EncodedType.prod A Instr
  have hFalse : TMPolyTimeMap C A
      (fun ctx : C.Carrier => (ctx, (false, ((0 : Nat), true)))) := by
    have hId : TMPolyTimeMap C C id := TMPolyTimeMap.id C
    have hFalse : TMPolyTimeMap C EncodedType.bool (fun _ : C.Carrier => false) :=
      TMPolyTimeMap.const C EncodedType.bool false
    have hZero : TMPolyTimeMap C EncodedType.nat (fun _ : C.Carrier => (0 : Nat)) :=
      TMPolyTimeMap.const C EncodedType.nat (0 : Nat)
    have hTrue : TMPolyTimeMap C EncodedType.bool (fun _ : C.Carrier => true) :=
      TMPolyTimeMap.const C EncodedType.bool true
    have hPrevOk : TMPolyTimeMap C (EncodedType.prod EncodedType.nat EncodedType.bool)
        (fun _ : C.Carrier => ((0 : Nat), true)) :=
      TMPolyTimeMap.prod_mk hZero hTrue
    have hTail : TMPolyTimeMap C
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod EncodedType.nat EncodedType.bool))
        (fun _ : C.Carrier => (false, ((0 : Nat), true))) :=
      TMPolyTimeMap.prod_mk hFalse hPrevOk
    have hOut := TMPolyTimeMap.prod_mk hId hTail
    simpa [A, C, steinerPathAccEncodedType] using hOut
  have hTrue : TMPolyTimeMap (EncodedType.prod A EncodedType.nat) A
      (fun p : A.Carrier × Nat => steinerPathVertexStep p.1 p.2) := by
    simpa [A] using steinerPathVertexStep_tm_polytime
  have hChoice := Partition.prodSumChoice_tm_polytime A C EncodedType.nat
  have hBranches := Partition.TMPolyTimeMap.sum_elim hFalse hTrue
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem steinerPathClosingOK_tm_polytime :
    TMPolyTimeMap steinerPathAccEncodedType EncodedType.bool steinerPathClosingOK := by
  let X := steinerPathAccEncodedType
  let Tail := EncodedType.prod EncodedType.bool
    (EncodedType.prod EncodedType.nat EncodedType.bool)
  let RootTarget := EncodedType.prod EncodedType.nat EncodedType.nat
  let GraphCtx := EncodedType.prod weightedEdgeListStructuredEncodedType EncodedType.bool
  let PrevOk := EncodedType.prod EncodedType.nat EncodedType.bool
  have hId : TMPolyTimeMap X X id := TMPolyTimeMap.id X
  have hCtx : TMPolyTimeMap X steinerPathContextEncodedType (fun acc : X.Carrier => acc.1) := by
    simpa [X, steinerPathAccEncodedType, Tail] using
      TMPolyTimeMap.fst steinerPathContextEncodedType Tail
  have hTail : TMPolyTimeMap X Tail (fun acc : X.Carrier => acc.2) := by
    simpa [X, steinerPathAccEncodedType, Tail] using
      TMPolyTimeMap.snd steinerPathContextEncodedType Tail
  have hSeen : TMPolyTimeMap X EncodedType.bool (fun acc : X.Carrier => acc.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool PrevOk
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, Tail, PrevOk, X] using hComp
  have hPrevOk : TMPolyTimeMap X PrevOk (fun acc : X.Carrier => acc.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool PrevOk
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, Tail, PrevOk, X] using hComp
  have hPrev : TMPolyTimeMap X EncodedType.nat (fun acc : X.Carrier => acc.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hPrevOk
    simpa [Function.comp, PrevOk, X] using hComp
  have hOk : TMPolyTimeMap X EncodedType.bool (fun acc : X.Carrier => acc.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hPrevOk
    simpa [Function.comp, PrevOk, X] using hComp
  have hRootTarget : TMPolyTimeMap X RootTarget (fun acc : X.Carrier => acc.1.2) := by
    have hSnd := TMPolyTimeMap.snd GraphCtx RootTarget
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, steinerPathContextEncodedType, GraphCtx, RootTarget, X] using hComp
  have hTarget : TMPolyTimeMap X EncodedType.nat (fun acc : X.Carrier => acc.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hRootTarget
    simpa [Function.comp, RootTarget, X] using hComp
  have hEqInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun acc : X.Carrier => (acc.2.2.1, acc.1.2.2)) :=
    TMPolyTimeMap.prod_mk hPrev hTarget
  have hEq : TMPolyTimeMap X EncodedType.bool
      (fun acc : X.Carrier => natEqBool (acc.2.2.1, acc.1.2.2)) := by
    have hComp := TMPolyTimeMap.comp natEqBool_tm_polytime hEqInput
    simpa [Function.comp, X] using hComp
  have hAndInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun acc : X.Carrier => (acc.2.2.2, natEqBool (acc.2.2.1, acc.1.2.2))) :=
    TMPolyTimeMap.prod_mk hOk hEq
  have hTrueBranch : TMPolyTimeMap X EncodedType.bool
      (fun acc : X.Carrier =>
        graphBoolAndPair (acc.2.2.2, natEqBool (acc.2.2.1, acc.1.2.2))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
    simpa [Function.comp, X] using hComp
  have hFalseBranch : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hBranchInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun acc : X.Carrier => (acc.2.1, acc)) :=
    TMPolyTimeMap.prod_mk hSeen hId
  have hBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) EncodedType.bool
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true => graphBoolAndPair (p.2.2.2.2, natEqBool (p.2.2.2.1, p.2.1.2.2))
          | false => false) :=
    graphBoolProduct_dispatch_tm_polytime X EncodedType.bool
      (fFalse := fun _ : X.Carrier => false)
      (fTrue := fun acc : X.Carrier =>
        graphBoolAndPair (acc.2.2.2, natEqBool (acc.2.2.1, acc.1.2.2)))
      hFalseBranch hTrueBranch
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext acc
  rcases acc with ⟨ctx, seen, prev, ok⟩
  cases seen <;> rfl

theorem steinerPathStep_growth
    (source : steinerPathInstructionListEncodedType.Carrier)
    (acc : steinerPathAccEncodedType.Carrier)
    (instr : steinerPathInstructionEncodedType.Carrier)
    (hInstr :
      steinerPathInstructionEncodedType.inputSize instr ≤
        steinerPathInstructionListEncodedType.inputSize source) :
    steinerPathAccEncodedType.inputSize (steinerPathStep (acc, instr)) ≤
      steinerPathAccEncodedType.inputSize acc +
        (Polynomial.C 20 * Polynomial.X + Polynomial.C 100).eval
          (steinerPathInstructionListEncodedType.inputSize source) := by
  rcases acc with ⟨ctx, seen, prev, ok⟩
  cases instr with
  | inl newCtx =>
      have hCtxSize :
          steinerPathContextEncodedType.inputSize newCtx ≤
            steinerPathInstructionListEncodedType.inputSize source := by
        have hPayload :
            steinerPathContextEncodedType.inputSize newCtx + 1 ≤
              steinerPathInstructionListEncodedType.inputSize source := by
          simpa [steinerPathInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum] using hInstr
        omega
      have hLocal :
          steinerPathAccEncodedType.inputSize (newCtx, (false, ((0 : Nat), true))) ≤
            steinerPathContextEncodedType.inputSize newCtx + 10 := by
        simp [steinerPathAccEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_bool, EncodedType.inputSize_nat]
      have hBudget :
          steinerPathContextEncodedType.inputSize newCtx + 10 ≤
            steinerPathAccEncodedType.inputSize (ctx, (seen, (prev, ok))) +
              (Polynomial.C 20 * Polynomial.X + Polynomial.C 100).eval
                (steinerPathInstructionListEncodedType.inputSize source) := by
        simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
        omega
      simpa [steinerPathStep] using hLocal.trans hBudget
  | inr v =>
      change Nat at v
      have hVSize : v ≤ steinerPathInstructionListEncodedType.inputSize source := by
        have hPayload :
            EncodedType.nat.inputSize v + 1 ≤
              steinerPathInstructionListEncodedType.inputSize source := by
          simpa [steinerPathInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum] using hInstr
        simp [EncodedType.inputSize_nat] at hPayload
        omega
      cases seen <;>
        simp [steinerPathStep, steinerPathVertexStep, steinerPathFirstVertexAcc,
          steinerPathNextVertexAcc, steinerPathAcc.ctx, steinerPathAcc.seen,
          steinerPathAcc.prev, steinerPathAcc.ok, steinerPathAccEncodedType,
          EncodedType.inputSize_prod, EncodedType.inputSize_bool, EncodedType.inputSize_nat,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] <;>
        omega

theorem steinerPathFold_tm_polytime :
    TMPolyTimeMap
      steinerPathInstructionListEncodedType
      steinerPathAccEncodedType
      (fun xs : steinerPathInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc instr => steinerPathStep (acc, instr)) steinerPathInitAcc) := by
  rcases steinerPathStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      steinerPathInstructionEncodedType steinerPathAccEncodedType
      steinerPathStep steinerPathInitAcc hStep
      (Polynomial.C 50) (Polynomial.C 20 * Polynomial.X + Polynomial.C 100) ?_ ?_
  · intro xs
    have hInit : steinerPathAccEncodedType.inputSize steinerPathInitAcc ≤ 50 := by
      native_decide
    simpa [steinerPathInstructionListEncodedType] using hInit
  · intro source acc instr hInstr
    exact steinerPathStep_growth source acc instr hInstr

theorem steinerPathFromInstructions_tm_polytime :
    TMPolyTimeMap steinerPathInstructionListEncodedType EncodedType.bool
      steinerPathFromInstructions := by
  have hFold := steinerPathFold_tm_polytime
  have hComp := TMPolyTimeMap.comp steinerPathClosingOK_tm_polytime hFold
  simpa [Function.comp, steinerPathFromInstructions] using hComp

theorem steinerPathBool_tm_polytime :
    TMPolyTimeMap steinerPathInputEncodedType EncodedType.bool steinerPathBool := by
  have hComp := TMPolyTimeMap.comp steinerPathFromInstructions_tm_polytime
    steinerPathInstructions_tm_polytime
  simpa [Function.comp, steinerPathBool] using hComp

def weightedAdjacentBoolRel
    (selected : List (Nat × Nat × Nat)) (directed : Bool) (u v : Nat) : Prop :=
  weightedAdjacentBool (((selected, directed), (u, v))) = true

theorem weightedAdjacentBoolRel_iff
    (selected : List (Nat × Nat × Nat)) (directed : Bool) (u v : Nat) :
    weightedAdjacentBoolRel selected directed u v ↔
      WeightedAdjacent selected directed u v := by
  simpa [weightedAdjacentBoolRel] using
    weightedAdjacentBool_eq_true_iff (((selected, directed), (u, v)))

theorem steinerPathTailFold_closing_eq_true_iff
    (ctx : SteinerPathContext) (prev : Nat) (ok : Bool) :
    ∀ rest : List Nat,
      steinerPathClosingOK
          ((rest.map steinerPathVertexInstruction).foldl
            (fun acc instr => steinerPathStep (acc, instr))
            (ctx, (true, (prev, ok)))) = true ↔
        ok = true ∧
          (prev :: rest).IsChain (weightedAdjacentBoolRel ctx.1.1 ctx.1.2) ∧
          ctx.2.2 ∈ (prev :: rest).getLast?
  | [] => by
      simp [steinerPathClosingOK, steinerPathAcc.seen, steinerPathAcc.ok,
        steinerPathAcc.prev, steinerPathAcc.ctx, graphBoolAndPair_eq_true_iff,
        natEqBool_eq_true_iff]
  | v :: rest => by
      rw [List.map_cons, List.foldl_cons]
      simp [steinerPathStep, steinerPathVertexStep, steinerPathNextVertexAcc,
        steinerPathVertexInstruction, steinerPathAcc.seen, steinerPathAcc.ok,
        steinerPathAcc.prev, steinerPathAcc.ctx]
      change
        steinerPathClosingOK
            ((rest.map steinerPathVertexInstruction).foldl
              (fun acc instr => steinerPathStep (acc, instr))
              (ctx, (true,
                (v,
                  graphBoolAndPair
                    (ok, weightedAdjacentBool ((ctx.1, (prev, v)))))))) = true ↔
          ok = true ∧
            (weightedAdjacentBoolRel ctx.1.1 ctx.1.2 prev v ∧
              (v :: rest).IsChain (weightedAdjacentBoolRel ctx.1.1 ctx.1.2)) ∧
            ctx.2.2 ∈ (v :: rest).getLast?
      rw [steinerPathTailFold_closing_eq_true_iff ctx v
        (graphBoolAndPair (ok, weightedAdjacentBool ((ctx.1, (prev, v))))) rest]
      constructor
      · rintro ⟨hHead, hChain, hLast⟩
        rcases (graphBoolAndPair_eq_true_iff
            (ok, weightedAdjacentBool ((ctx.1, (prev, v))))).1 hHead with
          ⟨hok, hAdj⟩
        exact ⟨hok, ⟨hAdj, hChain⟩, hLast⟩
      · rintro ⟨hok, hChain, hLast⟩
        refine ⟨?_, ?_, ?_⟩
        · exact (graphBoolAndPair_eq_true_iff
            (ok, weightedAdjacentBool ((ctx.1, (prev, v))))).2
            ⟨hok, hChain.1⟩
        · exact hChain.2
        · exact hLast

theorem steinerPathBool_eq_true_iff
    (ctx : SteinerPathContext) (path : List Nat) :
    steinerPathBool (ctx, path) = true ↔
      path.IsChain (weightedAdjacentBoolRel ctx.1.1 ctx.1.2) ∧
        ctx.2.1 ∈ path.head? ∧
        ctx.2.2 ∈ path.getLast? := by
  cases path with
  | nil =>
      simp [steinerPathBool, steinerPathFromInstructions, steinerPathInstructions,
        steinerPathInitInstruction, steinerPathClosingOK, steinerPathStep,
        steinerPathInitAcc, steinerPathAcc.seen]
  | cons first rest =>
      change
        steinerPathClosingOK
            (((steinerPathInitInstruction ctx ::
              (first :: rest).map steinerPathVertexInstruction).foldl
              (fun acc instr => steinerPathStep (acc, instr)) steinerPathInitAcc)) = true ↔ _
      rw [List.foldl_cons]
      change
        steinerPathClosingOK
            (((first :: rest).map steinerPathVertexInstruction).foldl
              (fun acc instr => steinerPathStep (acc, instr))
              (ctx, (false, (0, true)))) = true ↔ _
      rw [List.map_cons, List.foldl_cons]
      change
        steinerPathClosingOK
            ((rest.map steinerPathVertexInstruction).foldl
              (fun acc instr => steinerPathStep (acc, instr))
              (ctx, (true,
                (first, graphBoolAndPair (true, natEqBool (first, ctx.2.1)))))) = true ↔ _
      rw [steinerPathTailFold_closing_eq_true_iff ctx first
        (graphBoolAndPair (true, natEqBool (first, ctx.2.1))) rest]
      constructor
      · rintro ⟨hStartBool, hChain, hLast⟩
        rcases (graphBoolAndPair_eq_true_iff (true, natEqBool (first, ctx.2.1))).1
            hStartBool with
          ⟨_hTrue, hStart⟩
        have hStartEq : first = ctx.2.1 := (natEqBool_eq_true_iff _).1 hStart
        exact ⟨hChain, by simpa [hStartEq], hLast⟩
      · rintro ⟨hChain, hHead, hLast⟩
        simp at hHead
        subst first
        refine ⟨?_, hChain, hLast⟩
        exact (graphBoolAndPair_eq_true_iff (true, natEqBool (ctx.2.1, ctx.2.1))).2
          ⟨rfl, (natEqBool_eq_true_iff _).2 rfl⟩

theorem weightedReachable_of_isChain_cons
    {selected : List (Nat × Nat × Nat)} {directed : Bool}
    {root target : Nat} :
    ∀ rest : List Nat,
      (root :: rest).IsChain (WeightedAdjacent selected directed) →
      target ∈ (root :: rest).getLast? →
      WeightedReachable selected directed root target
  | [] => by
      intro _ hLast
      simp at hLast
      subst target
      exact WeightedReachable.refl root
  | v :: rest => by
      intro hChain hLast
      cases hChain with
      | cons_cons hAdj hTail =>
          exact WeightedReachable.step hAdj
            (weightedReachable_of_isChain_cons rest hTail hLast)

theorem weightedReachable_of_steinerPathBool
    {selected : List (Nat × Nat × Nat)} {directed : Bool}
    {root target : Nat} {path : List Nat}
    (hPath : steinerPathBool (((selected, directed), (root, target)), path) = true) :
    WeightedReachable selected directed root target := by
  rcases (steinerPathBool_eq_true_iff ((selected, directed), (root, target)) path).1 hPath with
    ⟨hChainBool, hHead, hLast⟩
  cases path with
  | nil =>
      simp at hHead
  | cons first rest =>
      simp at hHead
      subst first
      have hChain : (root :: rest).IsChain (WeightedAdjacent selected directed) :=
        hChainBool.imp (fun u v hAdj =>
          (weightedAdjacentBoolRel_iff selected directed u v).1 hAdj)
      exact weightedReachable_of_isChain_cons rest hChain hLast

end SteinerTreeMembership

end Karp21
end ComplexityReduction
