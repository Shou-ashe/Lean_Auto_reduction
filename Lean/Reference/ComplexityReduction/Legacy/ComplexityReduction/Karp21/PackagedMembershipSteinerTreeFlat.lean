/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSteinerTree

/-!
Alternative unary nat-list certificate verifier for faithful structured
Steiner Tree.

The original certificate stores a root, a selected weighted-edge list, and a
terminal-to-path entry table.  This verifier uses one nat list:

`root :: selected.length :: selected-edge-triples ++ path-entry-blocks`.

Each selected edge contributes the three endpoint/weight naturals.  Each path
entry contributes `terminal :: path.length :: path`.  Malformed trailing partial
blocks are ignored by the parser; soundness is inherited from the original
structured verifier applied to the parsed certificate.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace SteinerTreeMembership

abbrev steinerTreeFlatCertificateEncodedType : EncodedType :=
  setStructuredEncodedType

theorem setStructured_inputSize_cons (x : Nat) (xs : List Nat) :
    setStructuredEncodedType.inputSize (x :: xs) =
      EncodedType.nat.inputSize x + 1 + setStructuredEncodedType.inputSize xs := by
  simp [setStructuredEncodedType]

@[simp] theorem setStructured_inputSize_nil :
    setStructuredEncodedType.inputSize ([] : List Nat) = 0 := by
  native_decide

@[simp] theorem natList_inputSize_nil :
    (EncodedType.list EncodedType.nat).inputSize ([] : List Nat) = 0 := by
  native_decide

abbrev FlatAcc :=
  Nat × Nat × Nat × Nat × Nat × Nat × Nat × List Nat ×
    List (Nat × Nat × Nat) × List SteinerPathEntry

abbrev flatAccTail8EncodedType : EncodedType :=
  EncodedType.prod weightedEdgeListStructuredEncodedType steinerPathEntryListEncodedType

abbrev flatAccTail7EncodedType : EncodedType :=
  EncodedType.prod setStructuredEncodedType flatAccTail8EncodedType

abbrev flatAccTail6EncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat flatAccTail7EncodedType

abbrev flatAccTail5EncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat flatAccTail6EncodedType

abbrev flatAccTail4EncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat flatAccTail5EncodedType

abbrev flatAccTail3EncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat flatAccTail4EncodedType

abbrev flatAccTail2EncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat flatAccTail3EncodedType

abbrev flatAccTail1EncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat flatAccTail2EncodedType

abbrev flatAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat flatAccTail1EncodedType

def flatAccMode (acc : FlatAcc) : Nat := acc.1

def flatAccRoot (acc : FlatAcc) : Nat := acc.2.1

def flatAccEdgeRemaining (acc : FlatAcc) : Nat := acc.2.2.1

def flatAccU (acc : FlatAcc) : Nat := acc.2.2.2.1

def flatAccV (acc : FlatAcc) : Nat := acc.2.2.2.2.1

def flatAccPathRemaining (acc : FlatAcc) : Nat := acc.2.2.2.2.2.1

def flatAccTerminal (acc : FlatAcc) : Nat := acc.2.2.2.2.2.2.1

def flatAccPath (acc : FlatAcc) : List Nat := acc.2.2.2.2.2.2.2.1

def flatAccSelected (acc : FlatAcc) : List (Nat × Nat × Nat) :=
  acc.2.2.2.2.2.2.2.2.1

def flatAccEntries (acc : FlatAcc) : List SteinerPathEntry :=
  acc.2.2.2.2.2.2.2.2.2

theorem flatAccMk_tm_polytime {X : EncodedType}
    {mode root edgeRemaining u v pathRemaining terminal : X.Carrier → Nat}
    {path : X.Carrier → List Nat}
    {selected : X.Carrier → List (Nat × Nat × Nat)}
    {entries : X.Carrier → List SteinerPathEntry}
    (hMode : TMPolyTimeMap X EncodedType.nat mode)
    (hRoot : TMPolyTimeMap X EncodedType.nat root)
    (hEdgeRemaining : TMPolyTimeMap X EncodedType.nat edgeRemaining)
    (hU : TMPolyTimeMap X EncodedType.nat u)
    (hV : TMPolyTimeMap X EncodedType.nat v)
    (hPathRemaining : TMPolyTimeMap X EncodedType.nat pathRemaining)
    (hTerminal : TMPolyTimeMap X EncodedType.nat terminal)
    (hPath : TMPolyTimeMap X setStructuredEncodedType path)
    (hSelected : TMPolyTimeMap X weightedEdgeListStructuredEncodedType selected)
    (hEntries : TMPolyTimeMap X steinerPathEntryListEncodedType entries) :
    TMPolyTimeMap X flatAccEncodedType
      (fun x => (mode x, root x, edgeRemaining x, u x, v x, pathRemaining x,
        terminal x, path x, selected x, entries x)) := by
  have hTail8 :
      TMPolyTimeMap X flatAccTail8EncodedType
        (fun x => (selected x, entries x)) :=
    TMPolyTimeMap.prod_mk hSelected hEntries
  have hTail7 :
      TMPolyTimeMap X flatAccTail7EncodedType
        (fun x => (path x, selected x, entries x)) :=
    TMPolyTimeMap.prod_mk hPath hTail8
  have hTail6 :
      TMPolyTimeMap X flatAccTail6EncodedType
        (fun x => (terminal x, path x, selected x, entries x)) :=
    TMPolyTimeMap.prod_mk hTerminal hTail7
  have hTail5 :
      TMPolyTimeMap X flatAccTail5EncodedType
        (fun x => (pathRemaining x, terminal x, path x, selected x, entries x)) :=
    TMPolyTimeMap.prod_mk hPathRemaining hTail6
  have hTail4 :
      TMPolyTimeMap X flatAccTail4EncodedType
        (fun x => (v x, pathRemaining x, terminal x, path x, selected x, entries x)) :=
    TMPolyTimeMap.prod_mk hV hTail5
  have hTail3 :
      TMPolyTimeMap X flatAccTail3EncodedType
        (fun x => (u x, v x, pathRemaining x, terminal x, path x, selected x, entries x)) :=
    TMPolyTimeMap.prod_mk hU hTail4
  have hTail2 :
      TMPolyTimeMap X flatAccTail2EncodedType
        (fun x => (edgeRemaining x, u x, v x, pathRemaining x, terminal x, path x,
          selected x, entries x)) :=
    TMPolyTimeMap.prod_mk hEdgeRemaining hTail3
  have hTail1 :
      TMPolyTimeMap X flatAccTail1EncodedType
        (fun x => (root x, edgeRemaining x, u x, v x, pathRemaining x, terminal x,
          path x, selected x, entries x)) :=
    TMPolyTimeMap.prod_mk hRoot hTail2
  have hOut := TMPolyTimeMap.prod_mk hMode hTail1
  simpa [flatAccEncodedType, flatAccTail1EncodedType, flatAccTail2EncodedType,
    flatAccTail3EncodedType, flatAccTail4EncodedType, flatAccTail5EncodedType,
    flatAccTail6EncodedType, flatAccTail7EncodedType, flatAccTail8EncodedType] using hOut

theorem flatAccMode_tm_polytime {X : EncodedType} {f : X.Carrier → FlatAcc}
    (hf : TMPolyTimeMap X flatAccEncodedType f) :
    TMPolyTimeMap X EncodedType.nat (fun x => flatAccMode (f x)) := by
  have hFst := TMPolyTimeMap.fst EncodedType.nat flatAccTail1EncodedType
  have hComp := TMPolyTimeMap.comp hFst hf
  simpa [Function.comp, flatAccEncodedType, flatAccMode] using hComp

theorem flatAccRoot_tm_polytime {X : EncodedType} {f : X.Carrier → FlatAcc}
    (hf : TMPolyTimeMap X flatAccEncodedType f) :
    TMPolyTimeMap X EncodedType.nat (fun x => flatAccRoot (f x)) := by
  have hTail := TMPolyTimeMap.snd EncodedType.nat flatAccTail1EncodedType
  have hFst := TMPolyTimeMap.fst EncodedType.nat flatAccTail2EncodedType
  have hComp := TMPolyTimeMap.comp hFst (TMPolyTimeMap.comp hTail hf)
  simpa [Function.comp, flatAccEncodedType, flatAccRoot] using hComp

theorem flatAccEdgeRemaining_tm_polytime {X : EncodedType} {f : X.Carrier → FlatAcc}
    (hf : TMPolyTimeMap X flatAccEncodedType f) :
    TMPolyTimeMap X EncodedType.nat (fun x => flatAccEdgeRemaining (f x)) := by
  have hTail1 := TMPolyTimeMap.snd EncodedType.nat flatAccTail1EncodedType
  have hTail2 := TMPolyTimeMap.snd EncodedType.nat flatAccTail2EncodedType
  have hFst := TMPolyTimeMap.fst EncodedType.nat flatAccTail3EncodedType
  have hComp := TMPolyTimeMap.comp hFst
    (TMPolyTimeMap.comp hTail2 (TMPolyTimeMap.comp hTail1 hf))
  simpa [Function.comp, flatAccEncodedType, flatAccEdgeRemaining] using hComp

theorem flatAccU_tm_polytime {X : EncodedType} {f : X.Carrier → FlatAcc}
    (hf : TMPolyTimeMap X flatAccEncodedType f) :
    TMPolyTimeMap X EncodedType.nat (fun x => flatAccU (f x)) := by
  have hTail1 := TMPolyTimeMap.snd EncodedType.nat flatAccTail1EncodedType
  have hTail2 := TMPolyTimeMap.snd EncodedType.nat flatAccTail2EncodedType
  have hTail3 := TMPolyTimeMap.snd EncodedType.nat flatAccTail3EncodedType
  have hFst := TMPolyTimeMap.fst EncodedType.nat flatAccTail4EncodedType
  have hComp := TMPolyTimeMap.comp hFst
    (TMPolyTimeMap.comp hTail3
      (TMPolyTimeMap.comp hTail2 (TMPolyTimeMap.comp hTail1 hf)))
  simpa [Function.comp, flatAccEncodedType, flatAccU] using hComp

theorem flatAccV_tm_polytime {X : EncodedType} {f : X.Carrier → FlatAcc}
    (hf : TMPolyTimeMap X flatAccEncodedType f) :
    TMPolyTimeMap X EncodedType.nat (fun x => flatAccV (f x)) := by
  have hTail1 := TMPolyTimeMap.snd EncodedType.nat flatAccTail1EncodedType
  have hTail2 := TMPolyTimeMap.snd EncodedType.nat flatAccTail2EncodedType
  have hTail3 := TMPolyTimeMap.snd EncodedType.nat flatAccTail3EncodedType
  have hTail4 := TMPolyTimeMap.snd EncodedType.nat flatAccTail4EncodedType
  have hFst := TMPolyTimeMap.fst EncodedType.nat flatAccTail5EncodedType
  have hComp := TMPolyTimeMap.comp hFst
    (TMPolyTimeMap.comp hTail4
      (TMPolyTimeMap.comp hTail3
        (TMPolyTimeMap.comp hTail2 (TMPolyTimeMap.comp hTail1 hf))))
  simpa [Function.comp, flatAccEncodedType, flatAccV] using hComp

theorem flatAccPathRemaining_tm_polytime {X : EncodedType} {f : X.Carrier → FlatAcc}
    (hf : TMPolyTimeMap X flatAccEncodedType f) :
    TMPolyTimeMap X EncodedType.nat (fun x => flatAccPathRemaining (f x)) := by
  have hTail1 := TMPolyTimeMap.snd EncodedType.nat flatAccTail1EncodedType
  have hTail2 := TMPolyTimeMap.snd EncodedType.nat flatAccTail2EncodedType
  have hTail3 := TMPolyTimeMap.snd EncodedType.nat flatAccTail3EncodedType
  have hTail4 := TMPolyTimeMap.snd EncodedType.nat flatAccTail4EncodedType
  have hTail5 := TMPolyTimeMap.snd EncodedType.nat flatAccTail5EncodedType
  have hFst := TMPolyTimeMap.fst EncodedType.nat flatAccTail6EncodedType
  have hComp := TMPolyTimeMap.comp hFst
    (TMPolyTimeMap.comp hTail5
      (TMPolyTimeMap.comp hTail4
        (TMPolyTimeMap.comp hTail3
          (TMPolyTimeMap.comp hTail2 (TMPolyTimeMap.comp hTail1 hf)))))
  simpa [Function.comp, flatAccEncodedType, flatAccPathRemaining] using hComp

theorem flatAccTerminal_tm_polytime {X : EncodedType} {f : X.Carrier → FlatAcc}
    (hf : TMPolyTimeMap X flatAccEncodedType f) :
    TMPolyTimeMap X EncodedType.nat (fun x => flatAccTerminal (f x)) := by
  have hTail1 := TMPolyTimeMap.snd EncodedType.nat flatAccTail1EncodedType
  have hTail2 := TMPolyTimeMap.snd EncodedType.nat flatAccTail2EncodedType
  have hTail3 := TMPolyTimeMap.snd EncodedType.nat flatAccTail3EncodedType
  have hTail4 := TMPolyTimeMap.snd EncodedType.nat flatAccTail4EncodedType
  have hTail5 := TMPolyTimeMap.snd EncodedType.nat flatAccTail5EncodedType
  have hTail6 := TMPolyTimeMap.snd EncodedType.nat flatAccTail6EncodedType
  have hFst := TMPolyTimeMap.fst EncodedType.nat flatAccTail7EncodedType
  have hComp := TMPolyTimeMap.comp hFst
    (TMPolyTimeMap.comp hTail6
      (TMPolyTimeMap.comp hTail5
        (TMPolyTimeMap.comp hTail4
          (TMPolyTimeMap.comp hTail3
            (TMPolyTimeMap.comp hTail2 (TMPolyTimeMap.comp hTail1 hf))))))
  simpa [Function.comp, flatAccEncodedType, flatAccTerminal] using hComp

theorem flatAccPath_tm_polytime {X : EncodedType} {f : X.Carrier → FlatAcc}
    (hf : TMPolyTimeMap X flatAccEncodedType f) :
    TMPolyTimeMap X setStructuredEncodedType (fun x => flatAccPath (f x)) := by
  have hTail1 := TMPolyTimeMap.snd EncodedType.nat flatAccTail1EncodedType
  have hTail2 := TMPolyTimeMap.snd EncodedType.nat flatAccTail2EncodedType
  have hTail3 := TMPolyTimeMap.snd EncodedType.nat flatAccTail3EncodedType
  have hTail4 := TMPolyTimeMap.snd EncodedType.nat flatAccTail4EncodedType
  have hTail5 := TMPolyTimeMap.snd EncodedType.nat flatAccTail5EncodedType
  have hTail6 := TMPolyTimeMap.snd EncodedType.nat flatAccTail6EncodedType
  have hTail7 := TMPolyTimeMap.snd EncodedType.nat flatAccTail7EncodedType
  have hFst := TMPolyTimeMap.fst setStructuredEncodedType flatAccTail8EncodedType
  have hComp := TMPolyTimeMap.comp hFst
    (TMPolyTimeMap.comp hTail7
      (TMPolyTimeMap.comp hTail6
        (TMPolyTimeMap.comp hTail5
          (TMPolyTimeMap.comp hTail4
            (TMPolyTimeMap.comp hTail3
              (TMPolyTimeMap.comp hTail2 (TMPolyTimeMap.comp hTail1 hf)))))))
  simpa [Function.comp, flatAccEncodedType, flatAccPath] using hComp

theorem flatAccSelected_tm_polytime {X : EncodedType} {f : X.Carrier → FlatAcc}
    (hf : TMPolyTimeMap X flatAccEncodedType f) :
    TMPolyTimeMap X weightedEdgeListStructuredEncodedType
      (fun x => flatAccSelected (f x)) := by
  have hTail1 := TMPolyTimeMap.snd EncodedType.nat flatAccTail1EncodedType
  have hTail2 := TMPolyTimeMap.snd EncodedType.nat flatAccTail2EncodedType
  have hTail3 := TMPolyTimeMap.snd EncodedType.nat flatAccTail3EncodedType
  have hTail4 := TMPolyTimeMap.snd EncodedType.nat flatAccTail4EncodedType
  have hTail5 := TMPolyTimeMap.snd EncodedType.nat flatAccTail5EncodedType
  have hTail6 := TMPolyTimeMap.snd EncodedType.nat flatAccTail6EncodedType
  have hTail7 := TMPolyTimeMap.snd EncodedType.nat flatAccTail7EncodedType
  have hTail8 := TMPolyTimeMap.snd setStructuredEncodedType flatAccTail8EncodedType
  have hFst := TMPolyTimeMap.fst weightedEdgeListStructuredEncodedType
    steinerPathEntryListEncodedType
  have hComp := TMPolyTimeMap.comp hFst
    (TMPolyTimeMap.comp hTail8
      (TMPolyTimeMap.comp hTail7
        (TMPolyTimeMap.comp hTail6
          (TMPolyTimeMap.comp hTail5
            (TMPolyTimeMap.comp hTail4
              (TMPolyTimeMap.comp hTail3
                (TMPolyTimeMap.comp hTail2 (TMPolyTimeMap.comp hTail1 hf))))))))
  simpa [Function.comp, flatAccEncodedType, flatAccSelected] using hComp

theorem flatAccEntries_tm_polytime {X : EncodedType} {f : X.Carrier → FlatAcc}
    (hf : TMPolyTimeMap X flatAccEncodedType f) :
    TMPolyTimeMap X steinerPathEntryListEncodedType
      (fun x => flatAccEntries (f x)) := by
  have hTail1 := TMPolyTimeMap.snd EncodedType.nat flatAccTail1EncodedType
  have hTail2 := TMPolyTimeMap.snd EncodedType.nat flatAccTail2EncodedType
  have hTail3 := TMPolyTimeMap.snd EncodedType.nat flatAccTail3EncodedType
  have hTail4 := TMPolyTimeMap.snd EncodedType.nat flatAccTail4EncodedType
  have hTail5 := TMPolyTimeMap.snd EncodedType.nat flatAccTail5EncodedType
  have hTail6 := TMPolyTimeMap.snd EncodedType.nat flatAccTail6EncodedType
  have hTail7 := TMPolyTimeMap.snd EncodedType.nat flatAccTail7EncodedType
  have hTail8 := TMPolyTimeMap.snd setStructuredEncodedType flatAccTail8EncodedType
  have hSnd := TMPolyTimeMap.snd weightedEdgeListStructuredEncodedType
    steinerPathEntryListEncodedType
  have hComp := TMPolyTimeMap.comp hSnd
    (TMPolyTimeMap.comp hTail8
      (TMPolyTimeMap.comp hTail7
        (TMPolyTimeMap.comp hTail6
          (TMPolyTimeMap.comp hTail5
            (TMPolyTimeMap.comp hTail4
              (TMPolyTimeMap.comp hTail3
                (TMPolyTimeMap.comp hTail2 (TMPolyTimeMap.comp hTail1 hf))))))))
  simpa [Function.comp, flatAccEncodedType, flatAccEntries] using hComp

theorem natEqConst_tm_polytime {X : EncodedType} {f : X.Carrier → Nat}
    (hf : TMPolyTimeMap X EncodedType.nat f) (k : Nat) :
    TMPolyTimeMap X EncodedType.bool (fun x => decide (f x = k)) := by
  have hConst : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => k) :=
    TMPolyTimeMap.const X EncodedType.nat k
  have hPair :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun x => (f x, k)) :=
    TMPolyTimeMap.prod_mk hf hConst
  have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hPair
  simpa [Function.comp] using hComp

theorem tmPolyTimeMap_boolDispatch {X Y : EncodedType}
    {cond : X.Carrier → Bool} {fFalse fTrue : X.Carrier → Y.Carrier}
    (hCond : TMPolyTimeMap X EncodedType.bool cond)
    (hFalse : TMPolyTimeMap X Y fFalse)
    (hTrue : TMPolyTimeMap X Y fTrue) :
    TMPolyTimeMap X Y (fun x => if cond x then fTrue x else fFalse x) := by
  have hInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun x => (cond x, x)) :=
    TMPolyTimeMap.prod_mk hCond (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) Y
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true => fTrue p.2
          | false => fFalse p.2) :=
    graphBoolProduct_dispatch_tm_polytime X Y hFalse hTrue
  have hOut := TMPolyTimeMap.comp hBranch hInput
  convert hOut using 1
  funext x
  cases h : cond x <;> simp [Function.comp, h]

def flatInitAcc : FlatAcc :=
  (0, 0, 0, 0, 0, 0, 0, [], [], [])

def flatSelectedEdgeBlock (e : Nat × Nat × Nat) : List Nat :=
  [e.1, e.2.1, e.2.2]

def flatSelectedEdgeBlocks (edges : List (Nat × Nat × Nat)) : List Nat :=
  edges.flatMap flatSelectedEdgeBlock

def flatPathEntryBlock (entry : SteinerPathEntry) : List Nat :=
  [entry.1, entry.2.length] ++ entry.2

def flatPathEntryBlocks (entries : List SteinerPathEntry) : List Nat :=
  entries.flatMap flatPathEntryBlock

def flatCertificateOf (cert : SteinerTreeCertificate) : List Nat :=
  steinerTreeCertificateRoot cert ::
    ((steinerTreeCertificateSelected cert).length ::
      flatSelectedEdgeBlocks (steinerTreeCertificateSelected cert) ++
        flatPathEntryBlocks (steinerTreeCertificateEntries cert))

def flatStep (p : FlatAcc × Nat) : FlatAcc :=
  match p with
  | ((mode, root, edgeRemaining, u, v, pathRemaining, terminal, path, selected, entries), x) =>
      if mode = 0 then
        (1, x, 0, 0, 0, 0, 0, [], selected, entries)
      else if mode = 1 then
        if x = 0 then
          (5, root, 0, 0, 0, 0, 0, [], selected, entries)
        else
          (2, root, x, 0, 0, 0, 0, [], selected, entries)
      else if mode = 2 then
        (3, root, edgeRemaining, x, 0, 0, 0, [], selected, entries)
      else if mode = 3 then
        (4, root, edgeRemaining, u, x, 0, 0, [], selected, entries)
      else if mode = 4 then
        let selected' := selected ++ [(u, v, x)]
        if edgeRemaining = 1 then
          (5, root, 0, 0, 0, 0, 0, [], selected', entries)
        else
          (2, root, edgeRemaining - 1, 0, 0, 0, 0, [], selected', entries)
      else if mode = 5 then
        (6, root, edgeRemaining, 0, 0, 0, x, [], selected, entries)
      else if mode = 6 then
        if x = 0 then
          (5, root, edgeRemaining, 0, 0, 0, 0, [], selected, entries ++ [(terminal, [])])
        else
          (7, root, edgeRemaining, 0, 0, x, terminal, [], selected, entries)
      else
        let path' := path ++ [x]
        if pathRemaining = 1 then
          (5, root, edgeRemaining, 0, 0, 0, 0, [], selected, entries ++ [(terminal, path')])
        else
          (7, root, edgeRemaining, 0, 0, pathRemaining - 1, terminal, path',
            selected, entries)

def flatStepMode0 (p : FlatAcc × Nat) : FlatAcc :=
  (1, p.2, 0, 0, 0, 0, 0, [], flatAccSelected p.1, flatAccEntries p.1)

def flatStepMode1Zero (p : FlatAcc × Nat) : FlatAcc :=
  (5, flatAccRoot p.1, 0, 0, 0, 0, 0, [],
    flatAccSelected p.1, flatAccEntries p.1)

def flatStepMode1Nonzero (p : FlatAcc × Nat) : FlatAcc :=
  (2, flatAccRoot p.1, p.2, 0, 0, 0, 0, [],
    flatAccSelected p.1, flatAccEntries p.1)

def flatStepMode1 (p : FlatAcc × Nat) : FlatAcc :=
  if p.2 = 0 then flatStepMode1Zero p else flatStepMode1Nonzero p

def flatStepMode2 (p : FlatAcc × Nat) : FlatAcc :=
  (3, flatAccRoot p.1, flatAccEdgeRemaining p.1, p.2, 0, 0, 0, [],
    flatAccSelected p.1, flatAccEntries p.1)

def flatStepMode3 (p : FlatAcc × Nat) : FlatAcc :=
  (4, flatAccRoot p.1, flatAccEdgeRemaining p.1, flatAccU p.1, p.2, 0, 0, [],
    flatAccSelected p.1, flatAccEntries p.1)

def flatStepSelectedAppend (p : FlatAcc × Nat) : List (Nat × Nat × Nat) :=
  flatAccSelected p.1 ++ [(flatAccU p.1, flatAccV p.1, p.2)]

def flatStepMode4Done (p : FlatAcc × Nat) : FlatAcc :=
  (5, flatAccRoot p.1, 0, 0, 0, 0, 0, [],
    flatStepSelectedAppend p, flatAccEntries p.1)

def flatStepMode4More (p : FlatAcc × Nat) : FlatAcc :=
  (2, flatAccRoot p.1, flatAccEdgeRemaining p.1 - 1, 0, 0, 0, 0, [],
    flatStepSelectedAppend p, flatAccEntries p.1)

def flatStepMode4 (p : FlatAcc × Nat) : FlatAcc :=
  if flatAccEdgeRemaining p.1 = 1 then flatStepMode4Done p else flatStepMode4More p

def flatStepMode5 (p : FlatAcc × Nat) : FlatAcc :=
  (6, flatAccRoot p.1, flatAccEdgeRemaining p.1, 0, 0, 0, p.2, [],
    flatAccSelected p.1, flatAccEntries p.1)

def flatStepEntriesAppendEmpty (p : FlatAcc × Nat) : List SteinerPathEntry :=
  flatAccEntries p.1 ++ [(flatAccTerminal p.1, [])]

def flatStepMode6Zero (p : FlatAcc × Nat) : FlatAcc :=
  (5, flatAccRoot p.1, flatAccEdgeRemaining p.1, 0, 0, 0, 0, [],
    flatAccSelected p.1, flatStepEntriesAppendEmpty p)

def flatStepMode6Nonzero (p : FlatAcc × Nat) : FlatAcc :=
  (7, flatAccRoot p.1, flatAccEdgeRemaining p.1, 0, 0, p.2,
    flatAccTerminal p.1, [], flatAccSelected p.1, flatAccEntries p.1)

def flatStepMode6 (p : FlatAcc × Nat) : FlatAcc :=
  if p.2 = 0 then flatStepMode6Zero p else flatStepMode6Nonzero p

def flatStepPathAppend (p : FlatAcc × Nat) : List Nat :=
  flatAccPath p.1 ++ [p.2]

def flatStepEntriesAppendPath (p : FlatAcc × Nat) : List SteinerPathEntry :=
  flatAccEntries p.1 ++ [(flatAccTerminal p.1, flatStepPathAppend p)]

def flatStepDefaultDone (p : FlatAcc × Nat) : FlatAcc :=
  (5, flatAccRoot p.1, flatAccEdgeRemaining p.1, 0, 0, 0, 0, [],
    flatAccSelected p.1, flatStepEntriesAppendPath p)

def flatStepDefaultMore (p : FlatAcc × Nat) : FlatAcc :=
  (7, flatAccRoot p.1, flatAccEdgeRemaining p.1, 0, 0,
    flatAccPathRemaining p.1 - 1, flatAccTerminal p.1, flatStepPathAppend p,
    flatAccSelected p.1, flatAccEntries p.1)

def flatStepDefault (p : FlatAcc × Nat) : FlatAcc :=
  if flatAccPathRemaining p.1 = 1 then flatStepDefaultDone p else flatStepDefaultMore p

set_option linter.unusedSimpArgs false in
theorem flatStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod flatAccEncodedType EncodedType.nat)
      flatAccEncodedType
      flatStep := by
  let P := EncodedType.prod flatAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap P flatAccEncodedType (fun p : FlatAcc × Nat => p.1) := by
    simpa [P] using TMPolyTimeMap.fst flatAccEncodedType EncodedType.nat
  have hX : TMPolyTimeMap P EncodedType.nat (fun p : FlatAcc × Nat => p.2) := by
    simpa [P] using TMPolyTimeMap.snd flatAccEncodedType EncodedType.nat
  have hMode : TMPolyTimeMap P EncodedType.nat (fun p => flatAccMode p.1) :=
    flatAccMode_tm_polytime hAcc
  have hRoot : TMPolyTimeMap P EncodedType.nat (fun p => flatAccRoot p.1) :=
    flatAccRoot_tm_polytime hAcc
  have hEdgeRemaining :
      TMPolyTimeMap P EncodedType.nat (fun p => flatAccEdgeRemaining p.1) :=
    flatAccEdgeRemaining_tm_polytime hAcc
  have hU : TMPolyTimeMap P EncodedType.nat (fun p => flatAccU p.1) :=
    flatAccU_tm_polytime hAcc
  have hV : TMPolyTimeMap P EncodedType.nat (fun p => flatAccV p.1) :=
    flatAccV_tm_polytime hAcc
  have hPathRemaining :
      TMPolyTimeMap P EncodedType.nat (fun p => flatAccPathRemaining p.1) :=
    flatAccPathRemaining_tm_polytime hAcc
  have hTerminal : TMPolyTimeMap P EncodedType.nat (fun p => flatAccTerminal p.1) :=
    flatAccTerminal_tm_polytime hAcc
  have hPath : TMPolyTimeMap P setStructuredEncodedType (fun p => flatAccPath p.1) :=
    flatAccPath_tm_polytime hAcc
  have hSelected :
      TMPolyTimeMap P weightedEdgeListStructuredEncodedType
        (fun p => flatAccSelected p.1) :=
    flatAccSelected_tm_polytime hAcc
  have hEntries :
      TMPolyTimeMap P steinerPathEntryListEncodedType
        (fun p => flatAccEntries p.1) :=
    flatAccEntries_tm_polytime hAcc
  have hZero : TMPolyTimeMap P EncodedType.nat (fun _ : FlatAcc × Nat => (0 : Nat)) :=
    TMPolyTimeMap.const P EncodedType.nat (0 : Nat)
  have hOne : TMPolyTimeMap P EncodedType.nat (fun _ : FlatAcc × Nat => (1 : Nat)) :=
    TMPolyTimeMap.const P EncodedType.nat (1 : Nat)
  have hTwo : TMPolyTimeMap P EncodedType.nat (fun _ : FlatAcc × Nat => (2 : Nat)) :=
    TMPolyTimeMap.const P EncodedType.nat (2 : Nat)
  have hThree : TMPolyTimeMap P EncodedType.nat (fun _ : FlatAcc × Nat => (3 : Nat)) :=
    TMPolyTimeMap.const P EncodedType.nat (3 : Nat)
  have hFour : TMPolyTimeMap P EncodedType.nat (fun _ : FlatAcc × Nat => (4 : Nat)) :=
    TMPolyTimeMap.const P EncodedType.nat (4 : Nat)
  have hFive : TMPolyTimeMap P EncodedType.nat (fun _ : FlatAcc × Nat => (5 : Nat)) :=
    TMPolyTimeMap.const P EncodedType.nat (5 : Nat)
  have hSix : TMPolyTimeMap P EncodedType.nat (fun _ : FlatAcc × Nat => (6 : Nat)) :=
    TMPolyTimeMap.const P EncodedType.nat (6 : Nat)
  have hSeven : TMPolyTimeMap P EncodedType.nat (fun _ : FlatAcc × Nat => (7 : Nat)) :=
    TMPolyTimeMap.const P EncodedType.nat (7 : Nat)
  have hEmptyPath :
      TMPolyTimeMap P setStructuredEncodedType (fun _ : FlatAcc × Nat => ([] : List Nat)) :=
    TMPolyTimeMap.const P setStructuredEncodedType []
  have hXSingleton :
      TMPolyTimeMap P setStructuredEncodedType (fun p : FlatAcc × Nat => [p.2]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton EncodedType.nat) hX
    simpa [Function.comp, setStructuredEncodedType, P] using hComp
  have hPathAppendInput :
      TMPolyTimeMap P (EncodedType.prod setStructuredEncodedType setStructuredEncodedType)
        (fun p : FlatAcc × Nat => (flatAccPath p.1, [p.2])) :=
    TMPolyTimeMap.prod_mk hPath hXSingleton
  have hPathAppend :
      TMPolyTimeMap P setStructuredEncodedType flatStepPathAppend := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append EncodedType.nat)
      hPathAppendInput
    simpa [Function.comp, setStructuredEncodedType, flatStepPathAppend, P] using hComp
  have hEdgeTail :
      TMPolyTimeMap P (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : FlatAcc × Nat => (flatAccV p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hV hX
  have hEdge :
      TMPolyTimeMap P weightedEdgeStructuredEncodedType
        (fun p : FlatAcc × Nat => (flatAccU p.1, flatAccV p.1, p.2)) := by
    have hOut := TMPolyTimeMap.prod_mk hU hEdgeTail
    simpa [weightedEdgeStructuredEncodedType, P] using hOut
  have hEdgeSingleton :
      TMPolyTimeMap P weightedEdgeListStructuredEncodedType
        (fun p : FlatAcc × Nat => [(flatAccU p.1, flatAccV p.1, p.2)]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton weightedEdgeStructuredEncodedType) hEdge
    simpa [Function.comp, weightedEdgeListStructuredEncodedType, P] using hComp
  have hSelectedAppendInput :
      TMPolyTimeMap P
        (EncodedType.prod weightedEdgeListStructuredEncodedType
          weightedEdgeListStructuredEncodedType)
        (fun p : FlatAcc × Nat =>
          (flatAccSelected p.1, [(flatAccU p.1, flatAccV p.1, p.2)])) :=
    TMPolyTimeMap.prod_mk hSelected hEdgeSingleton
  have hSelectedAppend :
      TMPolyTimeMap P weightedEdgeListStructuredEncodedType flatStepSelectedAppend := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append weightedEdgeStructuredEncodedType) hSelectedAppendInput
    simpa [Function.comp, weightedEdgeListStructuredEncodedType, flatStepSelectedAppend, P]
      using hComp
  have hEntryEmpty :
      TMPolyTimeMap P steinerPathEntryEncodedType
        (fun p : FlatAcc × Nat => (flatAccTerminal p.1, ([] : List Nat))) := by
    have hOut := TMPolyTimeMap.prod_mk hTerminal hEmptyPath
    simpa [steinerPathEntryEncodedType, P] using hOut
  have hEntryEmptySingleton :
      TMPolyTimeMap P steinerPathEntryListEncodedType
        (fun p : FlatAcc × Nat => [(flatAccTerminal p.1, ([] : List Nat))]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton steinerPathEntryEncodedType) hEntryEmpty
    simpa [Function.comp, steinerPathEntryListEncodedType, P] using hComp
  have hEntriesAppendEmptyInput :
      TMPolyTimeMap P
        (EncodedType.prod steinerPathEntryListEncodedType steinerPathEntryListEncodedType)
        (fun p : FlatAcc × Nat =>
          (flatAccEntries p.1, [(flatAccTerminal p.1, ([] : List Nat))])) :=
    TMPolyTimeMap.prod_mk hEntries hEntryEmptySingleton
  have hEntriesAppendEmpty :
      TMPolyTimeMap P steinerPathEntryListEncodedType flatStepEntriesAppendEmpty := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append steinerPathEntryEncodedType) hEntriesAppendEmptyInput
    simpa [Function.comp, steinerPathEntryListEncodedType, flatStepEntriesAppendEmpty, P]
      using hComp
  have hEntryPath :
      TMPolyTimeMap P steinerPathEntryEncodedType
        (fun p : FlatAcc × Nat => (flatAccTerminal p.1, flatStepPathAppend p)) := by
    have hOut := TMPolyTimeMap.prod_mk hTerminal hPathAppend
    simpa [steinerPathEntryEncodedType, P] using hOut
  have hEntryPathSingleton :
      TMPolyTimeMap P steinerPathEntryListEncodedType
        (fun p : FlatAcc × Nat => [(flatAccTerminal p.1, flatStepPathAppend p)]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton steinerPathEntryEncodedType) hEntryPath
    simpa [Function.comp, steinerPathEntryListEncodedType, P] using hComp
  have hEntriesAppendPathInput :
      TMPolyTimeMap P
        (EncodedType.prod steinerPathEntryListEncodedType steinerPathEntryListEncodedType)
        (fun p : FlatAcc × Nat =>
          (flatAccEntries p.1, [(flatAccTerminal p.1, flatStepPathAppend p)])) :=
    TMPolyTimeMap.prod_mk hEntries hEntryPathSingleton
  have hEntriesAppendPath :
      TMPolyTimeMap P steinerPathEntryListEncodedType flatStepEntriesAppendPath := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append steinerPathEntryEncodedType) hEntriesAppendPathInput
    simpa [Function.comp, steinerPathEntryListEncodedType, flatStepEntriesAppendPath, P]
      using hComp
  have hPredEdgeInput :
      TMPolyTimeMap P (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : FlatAcc × Nat => (flatAccEdgeRemaining p.1, (1 : Nat))) :=
    TMPolyTimeMap.prod_mk hEdgeRemaining hOne
  have hPredEdge :
      TMPolyTimeMap P EncodedType.nat
        (fun p : FlatAcc × Nat => flatAccEdgeRemaining p.1 - 1) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_sub hPredEdgeInput
    simpa [Function.comp, P] using hComp
  have hPredPathInput :
      TMPolyTimeMap P (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : FlatAcc × Nat => (flatAccPathRemaining p.1, (1 : Nat))) :=
    TMPolyTimeMap.prod_mk hPathRemaining hOne
  have hPredPath :
      TMPolyTimeMap P EncodedType.nat
        (fun p : FlatAcc × Nat => flatAccPathRemaining p.1 - 1) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_sub hPredPathInput
    simpa [Function.comp, P] using hComp
  have hMode0 : TMPolyTimeMap P flatAccEncodedType flatStepMode0 := by
    simpa [flatStepMode0, P] using
      flatAccMk_tm_polytime hOne hX hZero hZero hZero hZero hZero hEmptyPath hSelected hEntries
  have hMode1Zero : TMPolyTimeMap P flatAccEncodedType flatStepMode1Zero := by
    simpa [flatStepMode1Zero, P] using
      flatAccMk_tm_polytime hFive hRoot hZero hZero hZero hZero hZero hEmptyPath hSelected hEntries
  have hMode1Nonzero : TMPolyTimeMap P flatAccEncodedType flatStepMode1Nonzero := by
    simpa [flatStepMode1Nonzero, P] using
      flatAccMk_tm_polytime hTwo hRoot hX hZero hZero hZero hZero hEmptyPath hSelected hEntries
  have hXZero : TMPolyTimeMap P EncodedType.bool (fun p : FlatAcc × Nat => decide (p.2 = 0)) :=
    natEqConst_tm_polytime hX 0
  have hMode1 : TMPolyTimeMap P flatAccEncodedType flatStepMode1 := by
    have hBool := tmPolyTimeMap_boolDispatch hXZero hMode1Nonzero hMode1Zero
    convert hBool using 1
    funext p
    by_cases h : p.2 = 0 <;> simp [flatStepMode1, h]
  have hMode2 : TMPolyTimeMap P flatAccEncodedType flatStepMode2 := by
    simpa [flatStepMode2, P] using
      flatAccMk_tm_polytime hThree hRoot hEdgeRemaining hX hZero hZero hZero
        hEmptyPath hSelected hEntries
  have hMode3 : TMPolyTimeMap P flatAccEncodedType flatStepMode3 := by
    simpa [flatStepMode3, P] using
      flatAccMk_tm_polytime hFour hRoot hEdgeRemaining hU hX hZero hZero
        hEmptyPath hSelected hEntries
  have hMode4Done : TMPolyTimeMap P flatAccEncodedType flatStepMode4Done := by
    simpa [flatStepMode4Done, P] using
      flatAccMk_tm_polytime hFive hRoot hZero hZero hZero hZero hZero hEmptyPath
        hSelectedAppend hEntries
  have hMode4More : TMPolyTimeMap P flatAccEncodedType flatStepMode4More := by
    simpa [flatStepMode4More, P] using
      flatAccMk_tm_polytime hTwo hRoot hPredEdge hZero hZero hZero hZero hEmptyPath
        hSelectedAppend hEntries
  have hEdgeRemainingOne :
      TMPolyTimeMap P EncodedType.bool
        (fun p : FlatAcc × Nat => decide (flatAccEdgeRemaining p.1 = 1)) :=
    natEqConst_tm_polytime hEdgeRemaining 1
  have hMode4 : TMPolyTimeMap P flatAccEncodedType flatStepMode4 := by
    have hBool := tmPolyTimeMap_boolDispatch hEdgeRemainingOne hMode4More hMode4Done
    convert hBool using 1
    funext p
    by_cases h : flatAccEdgeRemaining p.1 = 1 <;> simp [flatStepMode4, h]
  have hMode5 : TMPolyTimeMap P flatAccEncodedType flatStepMode5 := by
    simpa [flatStepMode5, P] using
      flatAccMk_tm_polytime hSix hRoot hEdgeRemaining hZero hZero hZero hX hEmptyPath
        hSelected hEntries
  have hMode6Zero : TMPolyTimeMap P flatAccEncodedType flatStepMode6Zero := by
    simpa [flatStepMode6Zero, P] using
      flatAccMk_tm_polytime hFive hRoot hEdgeRemaining hZero hZero hZero hZero hEmptyPath
        hSelected hEntriesAppendEmpty
  have hMode6Nonzero : TMPolyTimeMap P flatAccEncodedType flatStepMode6Nonzero := by
    simpa [flatStepMode6Nonzero, P] using
      flatAccMk_tm_polytime hSeven hRoot hEdgeRemaining hZero hZero hX hTerminal hEmptyPath
        hSelected hEntries
  have hMode6 : TMPolyTimeMap P flatAccEncodedType flatStepMode6 := by
    have hBool := tmPolyTimeMap_boolDispatch hXZero hMode6Nonzero hMode6Zero
    convert hBool using 1
    funext p
    by_cases h : p.2 = 0 <;> simp [flatStepMode6, h]
  have hDefaultDone : TMPolyTimeMap P flatAccEncodedType flatStepDefaultDone := by
    simpa [flatStepDefaultDone, P] using
      flatAccMk_tm_polytime hFive hRoot hEdgeRemaining hZero hZero hZero hZero hEmptyPath
        hSelected hEntriesAppendPath
  have hDefaultMore : TMPolyTimeMap P flatAccEncodedType flatStepDefaultMore := by
    simpa [flatStepDefaultMore, P] using
      flatAccMk_tm_polytime hSeven hRoot hEdgeRemaining hZero hZero hPredPath hTerminal
        hPathAppend hSelected hEntries
  have hPathRemainingOne :
      TMPolyTimeMap P EncodedType.bool
        (fun p : FlatAcc × Nat => decide (flatAccPathRemaining p.1 = 1)) :=
    natEqConst_tm_polytime hPathRemaining 1
  have hDefault : TMPolyTimeMap P flatAccEncodedType flatStepDefault := by
    have hBool := tmPolyTimeMap_boolDispatch hPathRemainingOne hDefaultMore hDefaultDone
    convert hBool using 1
    funext p
    by_cases h : flatAccPathRemaining p.1 = 1 <;> simp [flatStepDefault, h]
  have hModeEq0 :
      TMPolyTimeMap P EncodedType.bool (fun p : FlatAcc × Nat => decide (flatAccMode p.1 = 0)) :=
    natEqConst_tm_polytime hMode 0
  have hModeEq1 :
      TMPolyTimeMap P EncodedType.bool (fun p : FlatAcc × Nat => decide (flatAccMode p.1 = 1)) :=
    natEqConst_tm_polytime hMode 1
  have hModeEq2 :
      TMPolyTimeMap P EncodedType.bool (fun p : FlatAcc × Nat => decide (flatAccMode p.1 = 2)) :=
    natEqConst_tm_polytime hMode 2
  have hModeEq3 :
      TMPolyTimeMap P EncodedType.bool (fun p : FlatAcc × Nat => decide (flatAccMode p.1 = 3)) :=
    natEqConst_tm_polytime hMode 3
  have hModeEq4 :
      TMPolyTimeMap P EncodedType.bool (fun p : FlatAcc × Nat => decide (flatAccMode p.1 = 4)) :=
    natEqConst_tm_polytime hMode 4
  have hModeEq5 :
      TMPolyTimeMap P EncodedType.bool (fun p : FlatAcc × Nat => decide (flatAccMode p.1 = 5)) :=
    natEqConst_tm_polytime hMode 5
  have hModeEq6 :
      TMPolyTimeMap P EncodedType.bool (fun p : FlatAcc × Nat => decide (flatAccMode p.1 = 6)) :=
    natEqConst_tm_polytime hMode 6
  have hAfter6 :
      TMPolyTimeMap P flatAccEncodedType
        (fun p : FlatAcc × Nat =>
          if decide (flatAccMode p.1 = 6) then flatStepMode6 p else flatStepDefault p) :=
    tmPolyTimeMap_boolDispatch hModeEq6 hDefault hMode6
  have hAfter5 :
      TMPolyTimeMap P flatAccEncodedType
        (fun p : FlatAcc × Nat =>
          if decide (flatAccMode p.1 = 5) then flatStepMode5 p
          else if decide (flatAccMode p.1 = 6) then flatStepMode6 p
          else flatStepDefault p) :=
    tmPolyTimeMap_boolDispatch hModeEq5 hAfter6 hMode5
  have hAfter4 :
      TMPolyTimeMap P flatAccEncodedType
        (fun p : FlatAcc × Nat =>
          if decide (flatAccMode p.1 = 4) then flatStepMode4 p
          else if decide (flatAccMode p.1 = 5) then flatStepMode5 p
          else if decide (flatAccMode p.1 = 6) then flatStepMode6 p
          else flatStepDefault p) :=
    tmPolyTimeMap_boolDispatch hModeEq4 hAfter5 hMode4
  have hAfter3 :
      TMPolyTimeMap P flatAccEncodedType
        (fun p : FlatAcc × Nat =>
          if decide (flatAccMode p.1 = 3) then flatStepMode3 p
          else if decide (flatAccMode p.1 = 4) then flatStepMode4 p
          else if decide (flatAccMode p.1 = 5) then flatStepMode5 p
          else if decide (flatAccMode p.1 = 6) then flatStepMode6 p
          else flatStepDefault p) :=
    tmPolyTimeMap_boolDispatch hModeEq3 hAfter4 hMode3
  have hAfter2 :
      TMPolyTimeMap P flatAccEncodedType
        (fun p : FlatAcc × Nat =>
          if decide (flatAccMode p.1 = 2) then flatStepMode2 p
          else if decide (flatAccMode p.1 = 3) then flatStepMode3 p
          else if decide (flatAccMode p.1 = 4) then flatStepMode4 p
          else if decide (flatAccMode p.1 = 5) then flatStepMode5 p
          else if decide (flatAccMode p.1 = 6) then flatStepMode6 p
          else flatStepDefault p) :=
    tmPolyTimeMap_boolDispatch hModeEq2 hAfter3 hMode2
  have hAfter1 :
      TMPolyTimeMap P flatAccEncodedType
        (fun p : FlatAcc × Nat =>
          if decide (flatAccMode p.1 = 1) then flatStepMode1 p
          else if decide (flatAccMode p.1 = 2) then flatStepMode2 p
          else if decide (flatAccMode p.1 = 3) then flatStepMode3 p
          else if decide (flatAccMode p.1 = 4) then flatStepMode4 p
          else if decide (flatAccMode p.1 = 5) then flatStepMode5 p
          else if decide (flatAccMode p.1 = 6) then flatStepMode6 p
          else flatStepDefault p) :=
    tmPolyTimeMap_boolDispatch hModeEq1 hAfter2 hMode1
  have hOut :
      TMPolyTimeMap P flatAccEncodedType
        (fun p : FlatAcc × Nat =>
          if decide (flatAccMode p.1 = 0) then flatStepMode0 p
          else if decide (flatAccMode p.1 = 1) then flatStepMode1 p
          else if decide (flatAccMode p.1 = 2) then flatStepMode2 p
          else if decide (flatAccMode p.1 = 3) then flatStepMode3 p
          else if decide (flatAccMode p.1 = 4) then flatStepMode4 p
          else if decide (flatAccMode p.1 = 5) then flatStepMode5 p
          else if decide (flatAccMode p.1 = 6) then flatStepMode6 p
          else flatStepDefault p) :=
    tmPolyTimeMap_boolDispatch hModeEq0 hAfter1 hMode0
  convert hOut using 1
  funext p
  rcases p with ⟨acc, x⟩
  rcases acc with
    ⟨mode, root, edgeRemaining, u, v, pathRemaining, terminal, path, selected, entries⟩
  by_cases h0 : mode = 0
  · simp [flatStep, flatStepMode0, flatAccMode, flatAccRoot, flatAccEdgeRemaining,
      flatAccU, flatAccV, flatAccPathRemaining, flatAccTerminal, flatAccPath,
      flatAccSelected, flatAccEntries, h0]
  · by_cases h1 : mode = 1
    · by_cases hx : x = 0
      · simp [flatStep, flatStepMode1, flatStepMode1Zero, flatAccMode, flatAccRoot,
          flatAccEdgeRemaining, flatAccU, flatAccV, flatAccPathRemaining, flatAccTerminal,
          flatAccPath, flatAccSelected, flatAccEntries, h0, h1, hx]
      · simp [flatStep, flatStepMode1, flatStepMode1Nonzero, flatAccMode, flatAccRoot,
          flatAccEdgeRemaining, flatAccU, flatAccV, flatAccPathRemaining, flatAccTerminal,
          flatAccPath, flatAccSelected, flatAccEntries, h0, h1, hx]
    · by_cases h2 : mode = 2
      · simp [flatStep, flatStepMode2, flatAccMode, flatAccRoot, flatAccEdgeRemaining,
          flatAccU, flatAccV, flatAccPathRemaining, flatAccTerminal, flatAccPath,
          flatAccSelected, flatAccEntries, h0, h1, h2]
      · by_cases h3 : mode = 3
        · simp [flatStep, flatStepMode3, flatAccMode, flatAccRoot, flatAccEdgeRemaining,
            flatAccU, flatAccV, flatAccPathRemaining, flatAccTerminal, flatAccPath,
            flatAccSelected, flatAccEntries, h0, h1, h2, h3]
        · by_cases h4 : mode = 4
          · by_cases he : edgeRemaining = 1
            · simp [flatStep, flatStepMode4, flatStepMode4Done, flatStepSelectedAppend,
                flatAccMode, flatAccRoot, flatAccEdgeRemaining, flatAccU, flatAccV,
                flatAccPathRemaining, flatAccTerminal, flatAccPath, flatAccSelected,
                flatAccEntries, h0, h1, h2, h3, h4, he]
            · simp [flatStep, flatStepMode4, flatStepMode4More, flatStepSelectedAppend,
                flatAccMode, flatAccRoot, flatAccEdgeRemaining, flatAccU, flatAccV,
                flatAccPathRemaining, flatAccTerminal, flatAccPath, flatAccSelected,
                flatAccEntries, h0, h1, h2, h3, h4, he]
          · by_cases h5 : mode = 5
            · simp [flatStep, flatStepMode5, flatAccMode, flatAccRoot,
                flatAccEdgeRemaining, flatAccU, flatAccV, flatAccPathRemaining,
                flatAccTerminal, flatAccPath, flatAccSelected, flatAccEntries,
                h0, h1, h2, h3, h4, h5]
            · by_cases h6 : mode = 6
              · by_cases hx : x = 0
                · simp [flatStep, flatStepMode6, flatStepMode6Zero,
                    flatStepEntriesAppendEmpty, flatAccMode, flatAccRoot,
                    flatAccEdgeRemaining, flatAccU, flatAccV, flatAccPathRemaining,
                    flatAccTerminal, flatAccPath, flatAccSelected, flatAccEntries,
                    h0, h1, h2, h3, h4, h5, h6, hx]
                · simp [flatStep, flatStepMode6, flatStepMode6Nonzero,
                    flatAccMode, flatAccRoot, flatAccEdgeRemaining, flatAccU, flatAccV,
                    flatAccPathRemaining, flatAccTerminal, flatAccPath, flatAccSelected,
                    flatAccEntries, h0, h1, h2, h3, h4, h5, h6, hx]
              · by_cases hp : pathRemaining = 1
                · simp [flatStep, flatStepDefault, flatStepDefaultDone,
                    flatStepPathAppend, flatStepEntriesAppendPath, flatAccMode,
                    flatAccRoot, flatAccEdgeRemaining, flatAccU, flatAccV,
                    flatAccPathRemaining, flatAccTerminal, flatAccPath, flatAccSelected,
                    flatAccEntries, h0, h1, h2, h3, h4, h5, h6, hp]
                · simp [flatStep, flatStepDefault, flatStepDefaultMore,
                    flatStepPathAppend, flatAccMode, flatAccRoot, flatAccEdgeRemaining,
                    flatAccU, flatAccV, flatAccPathRemaining, flatAccTerminal,
                    flatAccPath, flatAccSelected, flatAccEntries, h0, h1, h2, h3, h4,
                    h5, h6, hp]

def flatFromFlatAcc (xs : List Nat) : FlatAcc :=
  xs.foldl (fun acc x => flatStep (acc, x)) flatInitAcc

def flatAccCertificate (acc : FlatAcc) : SteinerTreeCertificate :=
  match acc with
  | (_, root, _, _, _, _, _, _, selected, entries) => (root, (selected, entries))

def flatCertificatePair (_I : SteinerTreeInput) (xs : List Nat) : SteinerTreeCertificate :=
  flatAccCertificate (flatFromFlatAcc xs)

def steinerTreeFlatStructuredFiniteVerify
    (I : SteinerTreeInput) (xs : List Nat) : Bool :=
  steinerTreeStructuredFiniteVerify I (flatCertificatePair I xs)

theorem flatSelectedEdgeBlock_fold_eq
    (root edgeRemaining u v pathRemaining terminal : Nat)
    (path : List Nat) (selected : List (Nat × Nat × Nat))
    (entries : List SteinerPathEntry) (e : Nat × Nat × Nat) :
    (flatSelectedEdgeBlock e).foldl (fun acc x => flatStep (acc, x))
        (2, root, edgeRemaining, u, v, pathRemaining, terminal, path, selected, entries) =
      (if edgeRemaining = 1 then
        (5, root, 0, 0, 0, 0, 0, [], selected ++ [e], entries)
      else
        (2, root, edgeRemaining - 1, 0, 0, 0, 0, [], selected ++ [e], entries)) := by
  rcases e with ⟨a, b, w⟩
  by_cases h : edgeRemaining = 1 <;>
    simp [flatSelectedEdgeBlock, flatStep, h]

theorem flatSelectedEdgeBlocks_fold_eq_nonempty
    (root : Nat) :
    ∀ (edges out : List (Nat × Nat × Nat)),
      edges ≠ [] →
        (flatSelectedEdgeBlocks edges).foldl (fun acc x => flatStep (acc, x))
            (2, root, edges.length, 0, 0, 0, 0, [], out, ([] : List SteinerPathEntry)) =
          (5, root, 0, 0, 0, 0, 0, [], out ++ edges, ([] : List SteinerPathEntry))
  | [], _out, h => False.elim (h rfl)
  | e :: rest, out, _ => by
      rw [flatSelectedEdgeBlocks, List.flatMap_cons, List.foldl_append,
        flatSelectedEdgeBlock_fold_eq]
      rcases rest with _ | ⟨e₂, rest⟩
      · simp
      · have hRest :
            ((flatSelectedEdgeBlocks (e₂ :: rest)).foldl
                (fun acc x => flatStep (acc, x))
                (2, root, (e₂ :: rest).length, 0, 0, 0, 0, [], out ++ [e],
                  ([] : List SteinerPathEntry))) =
              (5, root, 0, 0, 0, 0, 0, [], (out ++ [e]) ++ (e₂ :: rest),
                ([] : List SteinerPathEntry)) :=
          flatSelectedEdgeBlocks_fold_eq_nonempty root (e₂ :: rest) (out ++ [e]) (by simp)
        simpa [flatSelectedEdgeBlocks, List.append_assoc] using hRest

theorem flatSelectedSection_fold_eq
    (root : Nat) (selected : List (Nat × Nat × Nat)) :
    (selected.length :: flatSelectedEdgeBlocks selected).foldl
        (fun acc x => flatStep (acc, x))
        (1, root, 0, 0, 0, 0, 0, [], ([] : List (Nat × Nat × Nat)),
          ([] : List SteinerPathEntry)) =
      (5, root, 0, 0, 0, 0, 0, [], selected, ([] : List SteinerPathEntry)) := by
  rcases selected with _ | ⟨e, rest⟩
  · simp [flatSelectedEdgeBlocks, flatStep]
  · rw [List.foldl_cons]
    simp only [List.length_cons]
    have hNe : (e :: rest) ≠ [] := by simp
    have hFold :=
      flatSelectedEdgeBlocks_fold_eq_nonempty root (e :: rest)
        ([] : List (Nat × Nat × Nat)) hNe
    simpa [flatStep] using hFold

theorem flatPathPayload_fold_eq
    (root edgeRemaining terminal : Nat)
    (selected : List (Nat × Nat × Nat)) (entries : List SteinerPathEntry) :
    ∀ (payload pfx : List Nat), payload ≠ [] →
      payload.foldl (fun acc x => flatStep (acc, x))
          (7, root, edgeRemaining, 0, 0, payload.length, terminal, pfx, selected, entries) =
        (5, root, edgeRemaining, 0, 0, 0, 0, [], selected,
          entries ++ [(terminal, pfx ++ payload)])
  | [], _pfx, h => False.elim (h rfl)
  | x :: xs, pfx, _ => by
      rw [List.foldl_cons]
      rcases xs with _ | ⟨y, ys⟩
      · simp [flatStep]
      · have hTail :=
          flatPathPayload_fold_eq root edgeRemaining terminal selected entries
            (y :: ys) (pfx ++ [x]) (by simp)
        simpa [flatStep, List.append_assoc] using hTail

theorem flatPathEntryBlock_fold_eq
    (root edgeRemaining : Nat)
    (selected : List (Nat × Nat × Nat)) (entries : List SteinerPathEntry)
    (entry : SteinerPathEntry) :
    (flatPathEntryBlock entry).foldl (fun acc x => flatStep (acc, x))
        (5, root, edgeRemaining, 0, 0, 0, 0, [], selected, entries) =
      (5, root, edgeRemaining, 0, 0, 0, 0, [], selected, entries ++ [entry]) := by
  rcases entry with ⟨terminal, path⟩
  rcases path with _ | ⟨x, xs⟩
  · simp [flatPathEntryBlock, flatStep]
  · change
      (([terminal, (x :: xs).length] ++ (x :: xs)).foldl
          (fun acc x => flatStep (acc, x))
          (5, root, edgeRemaining, 0, 0, 0, 0, [], selected, entries)) =
        (5, root, edgeRemaining, 0, 0, 0, 0, [], selected,
          entries ++ [(terminal, x :: xs)])
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hPayload :=
      flatPathPayload_fold_eq root edgeRemaining terminal selected entries
        (x :: xs) ([] : List Nat) (by simp)
    simpa [flatStep] using hPayload

theorem flatPathEntryBlocks_fold_eq
    (root edgeRemaining : Nat) (selected : List (Nat × Nat × Nat)) :
    ∀ (entries out : List SteinerPathEntry),
      (flatPathEntryBlocks entries).foldl (fun acc x => flatStep (acc, x))
          (5, root, edgeRemaining, 0, 0, 0, 0, [], selected, out) =
        (5, root, edgeRemaining, 0, 0, 0, 0, [], selected, out ++ entries)
  | [], out => by simp [flatPathEntryBlocks]
  | entry :: rest, out => by
      rw [flatPathEntryBlocks, List.flatMap_cons, List.foldl_append,
        flatPathEntryBlock_fold_eq]
      have hRest :=
        flatPathEntryBlocks_fold_eq root edgeRemaining selected rest (out ++ [entry])
      simpa [flatPathEntryBlocks, List.append_assoc] using hRest

theorem flatCertificatePair_flatCertificateOf
    (I : SteinerTreeInput) (cert : SteinerTreeCertificate) :
    flatCertificatePair I (flatCertificateOf cert) = cert := by
  rcases cert with ⟨root, selected, entries⟩
  simp only [flatCertificatePair, flatFromFlatAcc, flatCertificateOf,
    steinerTreeCertificateRoot, steinerTreeCertificateSelected,
    steinerTreeCertificateEntries]
  change
    flatAccCertificate
      (((selected.length :: flatSelectedEdgeBlocks selected) ++
          flatPathEntryBlocks entries).foldl (fun acc x => flatStep (acc, x))
          (flatStep (flatInitAcc, root))) =
      (root, (selected, entries))
  rw [List.foldl_append]
  have hRoot :
      flatStep (flatInitAcc, root) =
        (1, root, 0, 0, 0, 0, 0, [],
          ([] : List (Nat × Nat × Nat)), ([] : List SteinerPathEntry)) := by
    simp [flatInitAcc, flatStep]
  rw [hRoot]
  rw [flatSelectedSection_fold_eq]
  have hEntries := flatPathEntryBlocks_fold_eq root 0 selected entries []
  have hCert := congrArg flatAccCertificate hEntries
  simpa [flatAccCertificate, flatPathEntryBlocks, List.append_assoc] using hCert

theorem flatSelectedEdgeBlock_inputSize_eq (e : Nat × Nat × Nat) :
    setStructuredEncodedType.inputSize (flatSelectedEdgeBlock e) =
      weightedEdgeStructuredEncodedType.inputSize e + 1 := by
  rcases e with ⟨u, v, w⟩
  simp [flatSelectedEdgeBlock, setStructuredEncodedType, weightedEdgeStructuredEncodedType,
    EncodedType.inputSize, EncodedType.list, EncodedType.nat, EncodedType.prod]
  omega

theorem flatSelectedEdgeBlocks_inputSize_eq
    (edges : List (Nat × Nat × Nat)) :
    setStructuredEncodedType.inputSize (flatSelectedEdgeBlocks edges) =
      weightedEdgeListStructuredEncodedType.inputSize edges := by
  induction edges with
  | nil =>
      native_decide
  | cons e rest ih =>
      simp only [flatSelectedEdgeBlocks, List.flatMap_cons]
      change
        (EncodedType.list EncodedType.nat).inputSize
            (flatSelectedEdgeBlock e ++ flatSelectedEdgeBlocks rest) =
          weightedEdgeListStructuredEncodedType.inputSize (e :: rest)
      have hAppend :=
        Clique.encodedList_inputSize_append EncodedType.nat
          (flatSelectedEdgeBlock e) (flatSelectedEdgeBlocks rest)
      calc
        (EncodedType.list EncodedType.nat).inputSize
            (flatSelectedEdgeBlock e ++ flatSelectedEdgeBlocks rest)
            =
              (EncodedType.list EncodedType.nat).inputSize (flatSelectedEdgeBlock e) +
                (EncodedType.list EncodedType.nat).inputSize (flatSelectedEdgeBlocks rest) :=
          hAppend
        _ =
              (weightedEdgeStructuredEncodedType.inputSize e + 1) +
                weightedEdgeListStructuredEncodedType.inputSize rest := by
          rw [show (EncodedType.list EncodedType.nat).inputSize
              (flatSelectedEdgeBlock e) =
                weightedEdgeStructuredEncodedType.inputSize e + 1 by
              simpa [setStructuredEncodedType] using flatSelectedEdgeBlock_inputSize_eq e]
          rw [show (EncodedType.list EncodedType.nat).inputSize
              (flatSelectedEdgeBlocks rest) =
                weightedEdgeListStructuredEncodedType.inputSize rest by
              simpa [setStructuredEncodedType] using ih]
        _ = weightedEdgeListStructuredEncodedType.inputSize (e :: rest) := by
          simp [weightedEdgeListStructuredEncodedType]

theorem flatPathEntryBlock_inputSize_le (entry : SteinerPathEntry) :
    setStructuredEncodedType.inputSize (flatPathEntryBlock entry) ≤
      2 * (steinerPathEntryEncodedType.inputSize entry + 1) := by
  rcases entry with ⟨terminal, path⟩
  have hAppend :=
    Clique.encodedList_inputSize_append EncodedType.nat
      [terminal, path.length] path
  have hPathLen :
      path.length ≤ setStructuredEncodedType.inputSize path := by
    simpa [setStructuredEncodedType] using
      encodedList_length_le_inputSize EncodedType.nat path
  calc
    setStructuredEncodedType.inputSize (flatPathEntryBlock (terminal, path))
        =
          setStructuredEncodedType.inputSize [terminal, path.length] +
            setStructuredEncodedType.inputSize path := by
          change
            setStructuredEncodedType.inputSize ([terminal, path.length] ++ path) =
              setStructuredEncodedType.inputSize [terminal, path.length] +
                setStructuredEncodedType.inputSize path
          exact hAppend
    _ ≤ 2 * (steinerPathEntryEncodedType.inputSize (terminal, path) + 1) := by
          simp [setStructuredEncodedType, steinerPathEntryEncodedType,
            EncodedType.inputSize_prod, EncodedType.inputSize_nat] at hPathLen ⊢
          omega

theorem flatPathEntryBlocks_inputSize_le
    (entries : List SteinerPathEntry) :
    setStructuredEncodedType.inputSize (flatPathEntryBlocks entries) ≤
      2 * steinerPathEntryListEncodedType.inputSize entries := by
  induction entries with
  | nil =>
      native_decide
  | cons entry rest ih =>
      simp only [flatPathEntryBlocks, List.flatMap_cons]
      change
        setStructuredEncodedType.inputSize
            (flatPathEntryBlock entry ++ flatPathEntryBlocks rest) ≤
          2 * steinerPathEntryListEncodedType.inputSize (entry :: rest)
      have hAppend :=
        Clique.encodedList_inputSize_append EncodedType.nat
          (flatPathEntryBlock entry) (flatPathEntryBlocks rest)
      have hEntry := flatPathEntryBlock_inputSize_le entry
      calc
        setStructuredEncodedType.inputSize
            (flatPathEntryBlock entry ++ flatPathEntryBlocks rest)
            =
              setStructuredEncodedType.inputSize (flatPathEntryBlock entry) +
                setStructuredEncodedType.inputSize (flatPathEntryBlocks rest) := by
          exact hAppend
        _ ≤ 2 * steinerPathEntryListEncodedType.inputSize (entry :: rest) := by
          simp [steinerPathEntryListEncodedType] at ih hEntry ⊢
          omega

theorem flatCertificateOf_inputSize_le (cert : SteinerTreeCertificate) :
    steinerTreeFlatCertificateEncodedType.inputSize (flatCertificateOf cert) ≤
      2 * steinerTreeCertificateEncodedType.inputSize cert + 2 := by
  rcases cert with ⟨root, selected, entries⟩
  have hAppend :=
    Clique.encodedList_inputSize_append EncodedType.nat
      (flatSelectedEdgeBlocks selected) (flatPathEntryBlocks entries)
  have hEdges := flatSelectedEdgeBlocks_inputSize_eq selected
  have hEntries := flatPathEntryBlocks_inputSize_le entries
  have hSelectedLen :
      selected.length ≤ weightedEdgeListStructuredEncodedType.inputSize selected := by
    simpa [weightedEdgeListStructuredEncodedType] using
      encodedList_length_le_inputSize weightedEdgeStructuredEncodedType selected
  change
    steinerTreeFlatCertificateEncodedType.inputSize
        (root :: selected.length ::
          (flatSelectedEdgeBlocks selected ++ flatPathEntryBlocks entries)) ≤
      2 * steinerTreeCertificateEncodedType.inputSize (root, (selected, entries)) + 2
  change
    setStructuredEncodedType.inputSize
        (root :: selected.length ::
          (flatSelectedEdgeBlocks selected ++ flatPathEntryBlocks entries)) ≤
      2 * steinerTreeCertificateEncodedType.inputSize (root, (selected, entries)) + 2
  calc
    setStructuredEncodedType.inputSize
        (root :: selected.length :: flatSelectedEdgeBlocks selected ++
          flatPathEntryBlocks entries)
        =
          EncodedType.nat.inputSize root + 1 +
            (EncodedType.nat.inputSize selected.length + 1 +
              setStructuredEncodedType.inputSize
                (flatSelectedEdgeBlocks selected ++ flatPathEntryBlocks entries)) := by
          change
            setStructuredEncodedType.inputSize
                (root :: selected.length ::
                  (flatSelectedEdgeBlocks selected ++ flatPathEntryBlocks entries)) =
              EncodedType.nat.inputSize root + 1 +
                (EncodedType.nat.inputSize selected.length + 1 +
                  setStructuredEncodedType.inputSize
                    (flatSelectedEdgeBlocks selected ++ flatPathEntryBlocks entries))
          rw [setStructured_inputSize_cons,
            setStructured_inputSize_cons]
    _ =
          EncodedType.nat.inputSize root + 1 +
            (EncodedType.nat.inputSize selected.length + 1 +
              (setStructuredEncodedType.inputSize (flatSelectedEdgeBlocks selected) +
                setStructuredEncodedType.inputSize (flatPathEntryBlocks entries))) := by
          rw [show setStructuredEncodedType.inputSize
              (flatSelectedEdgeBlocks selected ++ flatPathEntryBlocks entries) =
                setStructuredEncodedType.inputSize (flatSelectedEdgeBlocks selected) +
                  setStructuredEncodedType.inputSize (flatPathEntryBlocks entries) by
            exact hAppend]
    _ ≤ 2 * steinerTreeCertificateEncodedType.inputSize (root, (selected, entries)) + 2 := by
          rw [hEdges]
          simp [steinerTreeCertificateEncodedType, steinerPathEntryListEncodedType,
            EncodedType.inputSize_prod, EncodedType.inputSize_nat] at hEntries hSelectedLen ⊢
          omega

theorem steinerTreeFlatStructuredFiniteVerify_sound
    (I : SteinerTreeInput) (xs : List Nat)
    (hVerify : steinerTreeFlatStructuredFiniteVerify I xs = true) :
    SteinerTree I :=
  steinerTreeStructuredFiniteVerify_sound I (flatCertificatePair I xs) hVerify

theorem flatInitAcc_bound (xs : List Nat) :
    flatAccEncodedType.inputSize flatInitAcc ≤
      (Polynomial.C 20).eval (setStructuredEncodedType.inputSize xs) := by
  have h : flatAccEncodedType.inputSize flatInitAcc ≤ 20 := by
    native_decide
  simpa using h

set_option linter.unusedSimpArgs false in
theorem flatStep_growth
    (source : List Nat) (acc : flatAccEncodedType.Carrier) (x : Nat)
    (hX : EncodedType.nat.inputSize x ≤ setStructuredEncodedType.inputSize source) :
    flatAccEncodedType.inputSize (flatStep (acc, x)) ≤
      flatAccEncodedType.inputSize acc +
        (Polynomial.C 100 * Polynomial.X + Polynomial.C 1000).eval
          (setStructuredEncodedType.inputSize source) := by
  rcases acc with
    ⟨mode, root, edgeRemaining, u, v, pathRemaining, terminal, path, selected, entries⟩
  change Nat at mode root edgeRemaining u v pathRemaining terminal x
  change List Nat at path
  change List (Nat × Nat × Nat) at selected
  change List SteinerPathEntry at entries
  have hXSize : x + 1 ≤ setStructuredEncodedType.inputSize source := by
    simpa [EncodedType.inputSize_nat] using hX
  have hPathAppend :
      setStructuredEncodedType.inputSize (path ++ [x]) =
        setStructuredEncodedType.inputSize path + EncodedType.nat.inputSize x + 1 := by
    simpa [setStructuredEncodedType, EncodedType.inputSize_list_cons,
      EncodedType.inputSize_list_nil] using
      Clique.encodedList_inputSize_append EncodedType.nat path [x]
  have hPathAppendRaw :
      (EncodedType.list EncodedType.nat).inputSize (path ++ [x]) =
        (EncodedType.list EncodedType.nat).inputSize path + EncodedType.nat.inputSize x + 1 := by
    simpa [setStructuredEncodedType] using hPathAppend
  have hPathRawEq :
      setStructuredEncodedType.inputSize path =
        (EncodedType.list EncodedType.nat).inputSize path := rfl
  have hSelectedAppend :
      weightedEdgeListStructuredEncodedType.inputSize (selected ++ [(u, v, x)]) =
        weightedEdgeListStructuredEncodedType.inputSize selected +
          weightedEdgeStructuredEncodedType.inputSize (u, v, x) + 1 := by
    simpa [weightedEdgeListStructuredEncodedType, EncodedType.inputSize_list_cons,
      EncodedType.inputSize_list_nil] using
      Clique.encodedList_inputSize_append weightedEdgeStructuredEncodedType
        selected [(u, v, x)]
  have hEntriesAppendEmpty :
      steinerPathEntryListEncodedType.inputSize (entries ++ [(terminal, [])]) =
        steinerPathEntryListEncodedType.inputSize entries +
          steinerPathEntryEncodedType.inputSize (terminal, ([] : List Nat)) + 1 := by
    simpa [steinerPathEntryListEncodedType, EncodedType.inputSize_list_cons,
      EncodedType.inputSize_list_nil] using
      Clique.encodedList_inputSize_append steinerPathEntryEncodedType
        entries [(terminal, ([] : List Nat))]
  have hEntriesAppendPath :
      steinerPathEntryListEncodedType.inputSize (entries ++ [(terminal, path ++ [x])]) =
        steinerPathEntryListEncodedType.inputSize entries +
          steinerPathEntryEncodedType.inputSize (terminal, path ++ [x]) + 1 := by
    simpa [steinerPathEntryListEncodedType, EncodedType.inputSize_list_cons,
      EncodedType.inputSize_list_nil] using
      Clique.encodedList_inputSize_append steinerPathEntryEncodedType
        entries [(terminal, path ++ [x])]
  have hEntryEmptySize :
      steinerPathEntryEncodedType.inputSize (terminal, ([] : List Nat)) =
        EncodedType.nat.inputSize terminal + 1 := by
    simp [steinerPathEntryEncodedType, EncodedType.inputSize_prod]
  have hEntryEmptySizeNat :
      steinerPathEntryEncodedType.inputSize (terminal, ([] : List Nat)) = terminal + 2 := by
    simp [steinerPathEntryEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_nat]
  have hEntriesAppendEmptyExpanded :
      steinerPathEntryListEncodedType.inputSize (entries ++ [(terminal, [])]) =
        steinerPathEntryListEncodedType.inputSize entries + (terminal + 2) + 1 := by
    rw [hEntriesAppendEmpty, hEntryEmptySizeNat]
  have hEntryPathSize :
      steinerPathEntryEncodedType.inputSize (terminal, path ++ [x]) =
        EncodedType.nat.inputSize terminal + 1 +
          (EncodedType.list EncodedType.nat).inputSize (path ++ [x]) := by
    simp [steinerPathEntryEncodedType, EncodedType.inputSize_prod]
  have hEntriesAppendPathExpanded :
      steinerPathEntryListEncodedType.inputSize (entries ++ [(terminal, path ++ [x])]) =
        steinerPathEntryListEncodedType.inputSize entries +
          (EncodedType.nat.inputSize terminal + 1 +
            ((EncodedType.list EncodedType.nat).inputSize path + EncodedType.nat.inputSize x + 1)) +
          1 := by
    rw [hEntriesAppendPath, hEntryPathSize, hPathAppendRaw]
  by_cases h0 : mode = 0
  · simp [flatStep, h0, flatAccEncodedType, flatAccTail1EncodedType,
      flatAccTail2EncodedType, flatAccTail3EncodedType, flatAccTail4EncodedType,
      flatAccTail5EncodedType, flatAccTail6EncodedType, flatAccTail7EncodedType,
      flatAccTail8EncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_nat,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] at hXSize ⊢
    omega
  · by_cases h1 : mode = 1
    · by_cases hx : x = 0
      · simp [flatStep, h0, h1, hx, flatAccEncodedType, flatAccTail1EncodedType,
          flatAccTail2EncodedType, flatAccTail3EncodedType, flatAccTail4EncodedType,
          flatAccTail5EncodedType, flatAccTail6EncodedType, flatAccTail7EncodedType,
          flatAccTail8EncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_nat,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] at hXSize ⊢
        omega
      · simp [flatStep, h0, h1, hx, flatAccEncodedType, flatAccTail1EncodedType,
          flatAccTail2EncodedType, flatAccTail3EncodedType, flatAccTail4EncodedType,
          flatAccTail5EncodedType, flatAccTail6EncodedType, flatAccTail7EncodedType,
          flatAccTail8EncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_nat,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] at hXSize ⊢
        omega
    · by_cases h2 : mode = 2
      · simp [flatStep, h0, h1, h2, flatAccEncodedType, flatAccTail1EncodedType,
          flatAccTail2EncodedType, flatAccTail3EncodedType, flatAccTail4EncodedType,
          flatAccTail5EncodedType, flatAccTail6EncodedType, flatAccTail7EncodedType,
          flatAccTail8EncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_nat,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] at hXSize ⊢
        omega
      · by_cases h3 : mode = 3
        · simp [flatStep, h0, h1, h2, h3, flatAccEncodedType, flatAccTail1EncodedType,
            flatAccTail2EncodedType, flatAccTail3EncodedType, flatAccTail4EncodedType,
            flatAccTail5EncodedType, flatAccTail6EncodedType, flatAccTail7EncodedType,
            flatAccTail8EncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_nat,
            Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] at hXSize ⊢
          omega
        · by_cases h4 : mode = 4
          · by_cases he : edgeRemaining = 1
            · simp [flatStep, h0, h1, h2, h3, h4, he, hSelectedAppend,
                flatAccEncodedType, flatAccTail1EncodedType, flatAccTail2EncodedType,
                flatAccTail3EncodedType, flatAccTail4EncodedType, flatAccTail5EncodedType,
                flatAccTail6EncodedType, flatAccTail7EncodedType, flatAccTail8EncodedType,
                weightedEdgeStructuredEncodedType, EncodedType.inputSize_prod,
                EncodedType.inputSize_nat, Polynomial.eval_add, Polynomial.eval_mul,
                Polynomial.eval_X] at hXSize ⊢
              omega
            · simp [flatStep, h0, h1, h2, h3, h4, he, hSelectedAppend,
                flatAccEncodedType, flatAccTail1EncodedType, flatAccTail2EncodedType,
                flatAccTail3EncodedType, flatAccTail4EncodedType, flatAccTail5EncodedType,
                flatAccTail6EncodedType, flatAccTail7EncodedType, flatAccTail8EncodedType,
                weightedEdgeStructuredEncodedType, EncodedType.inputSize_prod,
                EncodedType.inputSize_nat, Polynomial.eval_add, Polynomial.eval_mul,
                Polynomial.eval_X] at hXSize ⊢
              omega
          · by_cases h5 : mode = 5
            · simp [flatStep, h0, h1, h2, h3, h4, h5, flatAccEncodedType,
                flatAccTail1EncodedType, flatAccTail2EncodedType, flatAccTail3EncodedType,
                flatAccTail4EncodedType, flatAccTail5EncodedType, flatAccTail6EncodedType,
                flatAccTail7EncodedType, flatAccTail8EncodedType,
                EncodedType.inputSize_prod, EncodedType.inputSize_nat,
                Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] at hXSize ⊢
              omega
            · by_cases h6 : mode = 6
              · by_cases hx : x = 0
                · simp [flatStep, h0, h1, h2, h3, h4, h5, h6, hx,
                    hEntriesAppendEmptyExpanded, flatAccEncodedType, flatAccTail1EncodedType,
                    flatAccTail2EncodedType, flatAccTail3EncodedType,
                    flatAccTail4EncodedType, flatAccTail5EncodedType,
                    flatAccTail6EncodedType, flatAccTail7EncodedType,
                    flatAccTail8EncodedType, steinerPathEntryEncodedType,
                    EncodedType.inputSize_prod, EncodedType.inputSize_nat,
                    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] at hXSize ⊢
                  omega
                · simp [flatStep, h0, h1, h2, h3, h4, h5, h6, hx,
                    flatAccEncodedType, flatAccTail1EncodedType, flatAccTail2EncodedType,
                    flatAccTail3EncodedType, flatAccTail4EncodedType,
                    flatAccTail5EncodedType, flatAccTail6EncodedType,
                    flatAccTail7EncodedType, flatAccTail8EncodedType,
                    EncodedType.inputSize_prod, EncodedType.inputSize_nat,
                    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] at hXSize ⊢
                  omega
              · by_cases hp : pathRemaining = 1
                · simp [flatStep, h0, h1, h2, h3, h4, h5, h6, hp, hPathAppend,
                    hPathAppendRaw, hPathRawEq, hEntriesAppendPathExpanded,
                    setStructuredEncodedType,
                    flatAccEncodedType, flatAccTail1EncodedType,
                    flatAccTail2EncodedType, flatAccTail3EncodedType,
                    flatAccTail4EncodedType, flatAccTail5EncodedType,
                    flatAccTail6EncodedType, flatAccTail7EncodedType,
                    flatAccTail8EncodedType, steinerPathEntryEncodedType,
                    EncodedType.inputSize_prod, EncodedType.inputSize_nat,
                    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] at hXSize ⊢
                  omega
                · simp [flatStep, h0, h1, h2, h3, h4, h5, h6, hp, hPathAppend,
                    hPathAppendRaw, setStructuredEncodedType,
                    flatAccEncodedType, flatAccTail1EncodedType, flatAccTail2EncodedType,
                    flatAccTail3EncodedType, flatAccTail4EncodedType,
                    flatAccTail5EncodedType, flatAccTail6EncodedType,
                    flatAccTail7EncodedType, flatAccTail8EncodedType,
                    EncodedType.inputSize_prod, EncodedType.inputSize_nat,
                    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] at hXSize ⊢
                  omega

theorem flatFromFlatAcc_tm_polytime :
    TMPolyTimeMap setStructuredEncodedType flatAccEncodedType flatFromFlatAcc := by
  rcases flatStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      EncodedType.nat flatAccEncodedType flatStep flatInitAcc hStep
      (Polynomial.C 20) (Polynomial.C 100 * Polynomial.X + Polynomial.C 1000)
      ?_ ?_
  · intro xs
    exact flatInitAcc_bound xs
  · intro source acc x hX
    exact flatStep_growth source acc x hX

theorem flatAccCertificate_tm_polytime :
    TMPolyTimeMap flatAccEncodedType steinerTreeCertificateEncodedType flatAccCertificate := by
  have hId : TMPolyTimeMap flatAccEncodedType flatAccEncodedType (fun acc : FlatAcc => acc) := by
    simpa using TMPolyTimeMap.id flatAccEncodedType
  have hRoot : TMPolyTimeMap flatAccEncodedType EncodedType.nat flatAccRoot := by
    simpa using
      flatAccRoot_tm_polytime
        (X := flatAccEncodedType) (f := fun acc : FlatAcc => acc) hId
  have hSelected :
      TMPolyTimeMap flatAccEncodedType weightedEdgeListStructuredEncodedType
        flatAccSelected := by
    simpa using
      flatAccSelected_tm_polytime
        (X := flatAccEncodedType) (f := fun acc : FlatAcc => acc) hId
  have hEntries :
      TMPolyTimeMap flatAccEncodedType steinerPathEntryListEncodedType flatAccEntries := by
    simpa using
      flatAccEntries_tm_polytime
        (X := flatAccEncodedType) (f := fun acc : FlatAcc => acc) hId
  have hTail :
      TMPolyTimeMap flatAccEncodedType
        (EncodedType.prod weightedEdgeListStructuredEncodedType steinerPathEntryListEncodedType)
        (fun acc : FlatAcc => (flatAccSelected acc, flatAccEntries acc)) :=
    TMPolyTimeMap.prod_mk hSelected hEntries
  have hOut := TMPolyTimeMap.prod_mk hRoot hTail
  have hOut' :
      TMPolyTimeMap flatAccEncodedType steinerTreeCertificateEncodedType
        (fun acc : FlatAcc => (flatAccRoot acc, (flatAccSelected acc, flatAccEntries acc))) := by
    simpa [steinerTreeCertificateEncodedType] using hOut
  simpa [flatAccCertificate, flatAccRoot, flatAccSelected, flatAccEntries] using hOut'

theorem flatCertificatePair_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod steinerTreeStructuredEncodedType steinerTreeFlatCertificateEncodedType)
      steinerTreeCertificateEncodedType
      (fun p : SteinerTreeInput × List Nat => flatCertificatePair p.1 p.2) := by
  let X := EncodedType.prod steinerTreeStructuredEncodedType steinerTreeFlatCertificateEncodedType
  have hCert : TMPolyTimeMap X steinerTreeFlatCertificateEncodedType
      (fun p : SteinerTreeInput × List Nat => p.2) := by
    simpa [X, steinerTreeFlatCertificateEncodedType] using
      TMPolyTimeMap.snd steinerTreeStructuredEncodedType setStructuredEncodedType
  have hAcc : TMPolyTimeMap X flatAccEncodedType
      (fun p : SteinerTreeInput × List Nat => flatFromFlatAcc p.2) := by
    have hComp := TMPolyTimeMap.comp flatFromFlatAcc_tm_polytime hCert
    simpa [Function.comp, steinerTreeFlatCertificateEncodedType] using hComp
  have hOut := TMPolyTimeMap.comp flatAccCertificate_tm_polytime hAcc
  simpa [Function.comp, flatCertificatePair, flatFromFlatAcc, X] using hOut

theorem steinerTreeFlatStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod steinerTreeStructuredEncodedType steinerTreeFlatCertificateEncodedType)
      EncodedType.bool
      (fun p : SteinerTreeInput × List Nat =>
        steinerTreeFlatStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod steinerTreeStructuredEncodedType steinerTreeFlatCertificateEncodedType
  have hInstance : TMPolyTimeMap X steinerTreeStructuredEncodedType
      (fun p : SteinerTreeInput × List Nat => p.1) := by
    simpa [X, steinerTreeFlatCertificateEncodedType] using
      TMPolyTimeMap.fst steinerTreeStructuredEncodedType setStructuredEncodedType
  have hPair := flatCertificatePair_tm_polytime
  have hInput :
      TMPolyTimeMap X
        (EncodedType.prod steinerTreeStructuredEncodedType steinerTreeCertificateEncodedType)
        (fun p : SteinerTreeInput × List Nat => (p.1, flatCertificatePair p.1 p.2)) :=
    TMPolyTimeMap.prod_mk hInstance hPair
  have hComp := TMPolyTimeMap.comp steinerTreeStructuredFiniteVerify_tm_polytime hInput
  simpa [Function.comp, steinerTreeFlatStructuredFiniteVerify, X] using hComp

end SteinerTreeMembership

noncomputable def steinerTreeFlatStructuredFiniteTMVerifier :
    TMVerifier steinerTreeStructuredDecisionProblem where
  Cert := SteinerTreeMembership.steinerTreeFlatCertificateEncodedType
  verify := SteinerTreeMembership.steinerTreeFlatStructuredFiniteVerify
  verifier_polytime :=
    SteinerTreeMembership.steinerTreeFlatStructuredFiniteVerify_tm_polytime
  cert_bound := by
    rcases SteinerTreeMembership.steinerTreeStructuredFiniteTMVerifier.cert_bound with
      ⟨degree, coeff, const, hBound⟩
    refine ⟨degree, 2 * coeff, 2 * const + 2, ?_⟩
    intro I hYes
    rcases hBound I hYes with ⟨cert, hSize, hVerify⟩
    refine ⟨SteinerTreeMembership.flatCertificateOf cert, ?_, ?_⟩
    · calc
        SteinerTreeMembership.steinerTreeFlatCertificateEncodedType.inputSize
            (SteinerTreeMembership.flatCertificateOf cert)
            ≤
              2 * SteinerTreeMembership.steinerTreeCertificateEncodedType.inputSize cert + 2 :=
          SteinerTreeMembership.flatCertificateOf_inputSize_le cert
        _ ≤ 2 * (coeff * steinerTreeStructuredEncodedType.inputSize I ^ degree + const) + 2 := by
          exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hSize) 2
        _ = (2 * coeff) * steinerTreeStructuredEncodedType.inputSize I ^ degree +
              (2 * const + 2) := by
          ring
    · simpa [SteinerTreeMembership.steinerTreeFlatStructuredFiniteVerify,
        SteinerTreeMembership.flatCertificatePair_flatCertificateOf] using hVerify
  sound := by
    intro I xs hVerify
    exact SteinerTreeMembership.steinerTreeFlatStructuredFiniteVerify_sound I xs hVerify

theorem steinerTreeStructured_TMInNP_flat :
    TMInNP steinerTreeStructuredDecisionProblem :=
  TMInNP.intro steinerTreeFlatStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
