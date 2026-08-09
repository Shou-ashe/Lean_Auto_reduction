/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSteinerTreeGraphScan
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.FiniteWitness

/-!
Direct standard-TM finite verifier core for faithful structured Steiner Tree.

The certificate contains a root, a selected weighted-edge list, and a table of
terminal-to-path entries.  The verifier checks the selected-edge weight bound,
that every selected edge is an input graph edge, and that the terminal scanner
accepts all input terminals against the certified root/path table.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace SteinerTreeMembership

/-! ### Structured projections for Steiner inputs -/

def weightedGraphPayloadOfWeightedGraph
    (g : WeightedGraphInput) : weightedGraphPayloadStructuredEncodedType.Carrier :=
  (g.edges, g.directed)

theorem weightedGraphPayload_encode_filterMap (g : WeightedGraphInput) :
    weightedGraphPayloadStructuredEncodedType.encode (weightedGraphPayloadOfWeightedGraph g) =
      (weightedGraphStructuredEncodedType.encode g).filterMap
        (@EncodedType.prodRightSymbol
          EncodedType.nat.Symbol weightedGraphPayloadStructuredEncodedType.Symbol) := by
  simpa [weightedGraphPayloadOfWeightedGraph, weightedGraphStructuredEncodedType] using
    (EncodedType.prod_right_filter_encode
      EncodedType.nat weightedGraphPayloadStructuredEncodedType
      (g.vertices, (g.edges, g.directed))).symm

noncomputable def weightedGraphPayloadTMBackedMap :
    TMBackedCostedMap
      weightedGraphStructuredEncodedType
      weightedGraphPayloadStructuredEncodedType
      weightedGraphPayloadOfWeightedGraph :=
  TMBackedCostedMap.symbolFilterMap
    weightedGraphStructuredEncodedType weightedGraphPayloadStructuredEncodedType
    weightedGraphPayloadOfWeightedGraph
    (@EncodedType.prodRightSymbol
      EncodedType.nat.Symbol weightedGraphPayloadStructuredEncodedType.Symbol)
    weightedGraphPayload_encode_filterMap

def steinerTreeTailOfInput
    (I : SteinerTreeInput) :
    (EncodedType.prod (EncodedType.list EncodedType.nat) EncodedType.nat).Carrier :=
  (I.terminals, I.weightBound)

theorem steinerTreeGraph_encode_filterMap (I : SteinerTreeInput) :
    weightedGraphStructuredEncodedType.encode I.graph =
      (steinerTreeStructuredEncodedType.encode I).filterMap
        (@EncodedType.prodLeftSymbol
          weightedGraphStructuredEncodedType.Symbol
          (EncodedType.prod (EncodedType.list EncodedType.nat) EncodedType.nat).Symbol) := by
  simpa [steinerTreeStructuredEncodedType] using
    (EncodedType.prod_left_filter_encode
      weightedGraphStructuredEncodedType
      (EncodedType.prod (EncodedType.list EncodedType.nat) EncodedType.nat)
      (I.graph, (I.terminals, I.weightBound))).symm

theorem steinerTreeTail_encode_filterMap (I : SteinerTreeInput) :
    (EncodedType.prod (EncodedType.list EncodedType.nat) EncodedType.nat).encode
        (steinerTreeTailOfInput I) =
      (steinerTreeStructuredEncodedType.encode I).filterMap
        (@EncodedType.prodRightSymbol
          weightedGraphStructuredEncodedType.Symbol
          (EncodedType.prod (EncodedType.list EncodedType.nat) EncodedType.nat).Symbol) := by
  simpa [steinerTreeTailOfInput, steinerTreeStructuredEncodedType] using
    (EncodedType.prod_right_filter_encode
      weightedGraphStructuredEncodedType
      (EncodedType.prod (EncodedType.list EncodedType.nat) EncodedType.nat)
      (I.graph, (I.terminals, I.weightBound))).symm

noncomputable def steinerTreeGraphTMBackedMap :
    TMBackedCostedMap
      steinerTreeStructuredEncodedType
      weightedGraphStructuredEncodedType
      (fun I : SteinerTreeInput => I.graph) :=
  TMBackedCostedMap.symbolFilterMap
    steinerTreeStructuredEncodedType weightedGraphStructuredEncodedType
    (fun I : SteinerTreeInput => I.graph)
    (@EncodedType.prodLeftSymbol
      weightedGraphStructuredEncodedType.Symbol
      (EncodedType.prod (EncodedType.list EncodedType.nat) EncodedType.nat).Symbol)
    steinerTreeGraph_encode_filterMap

noncomputable def steinerTreeTailTMBackedMap :
    TMBackedCostedMap
      steinerTreeStructuredEncodedType
      (EncodedType.prod (EncodedType.list EncodedType.nat) EncodedType.nat)
      steinerTreeTailOfInput :=
  TMBackedCostedMap.symbolFilterMap
    steinerTreeStructuredEncodedType
    (EncodedType.prod (EncodedType.list EncodedType.nat) EncodedType.nat)
    steinerTreeTailOfInput
    (@EncodedType.prodRightSymbol
      weightedGraphStructuredEncodedType.Symbol
      (EncodedType.prod (EncodedType.list EncodedType.nat) EncodedType.nat).Symbol)
    steinerTreeTail_encode_filterMap

/-! ### Certificate and finite verifier -/

def steinerTreeCertificateEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod weightedEdgeListStructuredEncodedType steinerPathEntryListEncodedType)

abbrev SteinerTreeCertificate :=
  Nat × (List (Nat × Nat × Nat) × List SteinerPathEntry)

def steinerTreeCertificateRoot (cert : SteinerTreeCertificate) : Nat := cert.1

def steinerTreeCertificateSelected (cert : SteinerTreeCertificate) :
    List (Nat × Nat × Nat) := cert.2.1

def steinerTreeCertificateEntries (cert : SteinerTreeCertificate) :
    List SteinerPathEntry := cert.2.2

def steinerTreeStructuredFiniteVerify
    (I : SteinerTreeInput) (cert : SteinerTreeCertificate) : Bool :=
  let selected := steinerTreeCertificateSelected cert
  let root := steinerTreeCertificateRoot cert
  let entries := steinerTreeCertificateEntries cert
  graphBoolAndPair
    (HittingSet.natLeBool (WeightedEdgeListWeight selected, I.weightBound),
      graphBoolAndPair
        (weightedAllInGraphBool (I.graph.edges, selected),
          steinerTerminalScanBool
            ((((selected, I.graph.directed), (root, entries))), I.terminals)))

theorem steinerTreeStructuredFiniteVerify_eq_true_iff
    (I : SteinerTreeInput) (cert : SteinerTreeCertificate) :
    steinerTreeStructuredFiniteVerify I cert = true ↔
      WeightedEdgeListWeight (steinerTreeCertificateSelected cert) ≤ I.weightBound ∧
        (∀ e ∈ steinerTreeCertificateSelected cert, e ∈ I.graph.edges) ∧
        steinerTerminalScanBool
          (((((steinerTreeCertificateSelected cert, I.graph.directed),
            (steinerTreeCertificateRoot cert, steinerTreeCertificateEntries cert))),
            I.terminals)) = true := by
  rw [steinerTreeStructuredFiniteVerify, graphBoolAndPair_eq_true_iff,
    graphBoolAndPair_eq_true_iff, HittingSet.natLeBool_eq_true_iff,
    weightedAllInGraphBool_eq_true_iff]

theorem steinerTreeStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod steinerTreeStructuredEncodedType steinerTreeCertificateEncodedType)
      EncodedType.bool
      (fun p : SteinerTreeInput × SteinerTreeCertificate =>
        steinerTreeStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod steinerTreeStructuredEncodedType steinerTreeCertificateEncodedType
  let Tail := EncodedType.prod (EncodedType.list EncodedType.nat) EncodedType.nat
  let GraphPayload := weightedGraphPayloadStructuredEncodedType
  let CertTail := EncodedType.prod weightedEdgeListStructuredEncodedType
    steinerPathEntryListEncodedType
  have hInstance :
      TMPolyTimeMap X steinerTreeStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst steinerTreeStructuredEncodedType steinerTreeCertificateEncodedType
  have hCert :
      TMPolyTimeMap X steinerTreeCertificateEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd steinerTreeStructuredEncodedType steinerTreeCertificateEncodedType
  have hGraph :
      TMPolyTimeMap X weightedGraphStructuredEncodedType (fun p : X.Carrier => p.1.graph) := by
    have hComp := TMPolyTimeMap.comp steinerTreeGraphTMBackedMap.tm_polytime hInstance
    simpa [Function.comp, X] using hComp
  have hTail : TMPolyTimeMap X Tail (fun p : X.Carrier => (p.1.terminals, p.1.weightBound)) := by
    have hComp := TMPolyTimeMap.comp steinerTreeTailTMBackedMap.tm_polytime hInstance
    simpa [Function.comp, steinerTreeTailOfInput, Tail, X] using hComp
  have hTerminals :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat) (fun p : X.Carrier => p.1.terminals) := by
    have hFst := TMPolyTimeMap.fst (EncodedType.list EncodedType.nat) EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, Tail, X] using hComp
  have hWeightBound : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.weightBound) := by
    have hSnd := TMPolyTimeMap.snd (EncodedType.list EncodedType.nat) EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, Tail, X] using hComp
  have hGraphPayload : TMPolyTimeMap X GraphPayload
      (fun p : X.Carrier => (p.1.graph.edges, p.1.graph.directed)) := by
    have hComp := TMPolyTimeMap.comp weightedGraphPayloadTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, weightedGraphPayloadOfWeightedGraph, GraphPayload, X] using hComp
  have hGraphEdges :
      TMPolyTimeMap X weightedEdgeListStructuredEncodedType
        (fun p : X.Carrier => p.1.graph.edges) := by
    have hFst := TMPolyTimeMap.fst weightedEdgeListStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hGraphPayload
    simpa [Function.comp, GraphPayload, X] using hComp
  have hDirected : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => p.1.graph.directed) := by
    have hSnd := TMPolyTimeMap.snd weightedEdgeListStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hGraphPayload
    simpa [Function.comp, GraphPayload, X] using hComp
  have hRoot : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat CertTail
    have hComp := TMPolyTimeMap.comp hFst hCert
    simpa [Function.comp, steinerTreeCertificateEncodedType, CertTail, X] using hComp
  have hCertTail : TMPolyTimeMap X CertTail (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat CertTail
    have hComp := TMPolyTimeMap.comp hSnd hCert
    simpa [Function.comp, steinerTreeCertificateEncodedType, CertTail, X] using hComp
  have hSelected :
      TMPolyTimeMap X weightedEdgeListStructuredEncodedType (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst weightedEdgeListStructuredEncodedType
      steinerPathEntryListEncodedType
    have hComp := TMPolyTimeMap.comp hFst hCertTail
    simpa [Function.comp, CertTail, X] using hComp
  have hEntries :
      TMPolyTimeMap X steinerPathEntryListEncodedType (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd weightedEdgeListStructuredEncodedType
      steinerPathEntryListEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hCertTail
    simpa [Function.comp, CertTail, X] using hComp
  have hSelectedWeight :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => WeightedEdgeListWeight p.2.2.1) := by
    have hComp := TMPolyTimeMap.comp weightedEdgeListWeight_tm_polytime hSelected
    simpa [Function.comp, X] using hComp
  have hWeightInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (WeightedEdgeListWeight p.2.2.1, p.1.weightBound)) :=
    TMPolyTimeMap.prod_mk hSelectedWeight hWeightBound
  have hWeightOK : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => HittingSet.natLeBool (WeightedEdgeListWeight p.2.2.1,
        p.1.weightBound)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.natLeBool_tm_polytime hWeightInput
    simpa [Function.comp, X] using hComp
  have hAllInGraphInput :
      TMPolyTimeMap X weightedAllInGraphInputEncodedType
        (fun p : X.Carrier => (p.1.graph.edges, p.2.2.1)) :=
    TMPolyTimeMap.prod_mk hGraphEdges hSelected
  have hAllInGraph : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => weightedAllInGraphBool (p.1.graph.edges, p.2.2.1)) := by
    have hComp := TMPolyTimeMap.comp weightedAllInGraphBool_tm_polytime hAllInGraphInput
    simpa [Function.comp, weightedAllInGraphInputEncodedType, X] using hComp
  have hSelectedDirected :
      TMPolyTimeMap X (EncodedType.prod weightedEdgeListStructuredEncodedType EncodedType.bool)
        (fun p : X.Carrier => (p.2.2.1, p.1.graph.directed)) :=
    TMPolyTimeMap.prod_mk hSelected hDirected
  have hRootEntries :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat steinerPathEntryListEncodedType)
        (fun p : X.Carrier => (p.2.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hRoot hEntries
  have hTerminalContext :
      TMPolyTimeMap X steinerTerminalScanContextEncodedType
        (fun p : X.Carrier => ((p.2.2.1, p.1.graph.directed), (p.2.1, p.2.2.2))) := by
    have hOut := TMPolyTimeMap.prod_mk hSelectedDirected hRootEntries
    simpa [steinerTerminalScanContextEncodedType] using hOut
  have hTerminalInput :
      TMPolyTimeMap X steinerTerminalScanInputEncodedType
        (fun p : X.Carrier =>
          (((p.2.2.1, p.1.graph.directed), (p.2.1, p.2.2.2)), p.1.terminals)) :=
    TMPolyTimeMap.prod_mk hTerminalContext hTerminals
  have hTerminalsOK : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        steinerTerminalScanBool
          (((p.2.2.1, p.1.graph.directed), (p.2.1, p.2.2.2)), p.1.terminals)) := by
    have hComp := TMPolyTimeMap.comp steinerTerminalScanBool_tm_polytime hTerminalInput
    simpa [Function.comp, steinerTerminalScanInputEncodedType, X] using hComp
  have hTailInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (weightedAllInGraphBool (p.1.graph.edges, p.2.2.1),
            steinerTerminalScanBool
              (((p.2.2.1, p.1.graph.directed), (p.2.1, p.2.2.2)), p.1.terminals))) :=
    TMPolyTimeMap.prod_mk hAllInGraph hTerminalsOK
  have hTailOK : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair
          (weightedAllInGraphBool (p.1.graph.edges, p.2.2.1),
            steinerTerminalScanBool
              (((p.2.2.1, p.1.graph.directed), (p.2.1, p.2.2.2)), p.1.terminals))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hTailInput
    simpa [Function.comp, X] using hComp
  have hAllInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (HittingSet.natLeBool (WeightedEdgeListWeight p.2.2.1, p.1.weightBound),
            graphBoolAndPair
              (weightedAllInGraphBool (p.1.graph.edges, p.2.2.1),
                steinerTerminalScanBool
                  (((p.2.2.1, p.1.graph.directed), (p.2.1, p.2.2.2)),
                    p.1.terminals)))) :=
    TMPolyTimeMap.prod_mk hWeightOK hTailOK
  have hAll := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAllInput
  simpa [Function.comp, steinerTreeStructuredFiniteVerify, steinerTreeCertificateRoot,
    steinerTreeCertificateSelected, steinerTreeCertificateEntries, X] using hAll

theorem steinerTreeStructuredFiniteVerify_sound
    (I : SteinerTreeInput) (cert : SteinerTreeCertificate)
    (hVerify : steinerTreeStructuredFiniteVerify I cert = true) :
    SteinerTree I := by
  rcases (steinerTreeStructuredFiniteVerify_eq_true_iff I cert).1 hVerify with
    ⟨hWeight, hEdges, hTerminals⟩
  let selected := steinerTreeCertificateSelected cert
  let root := steinerTreeCertificateRoot cert
  let entries := steinerTreeCertificateEntries cert
  refine ⟨selected, ?_, ?_, hWeight⟩
  · simpa [selected] using hEdges
  · intro t ht
    have hScan := steinerTerminalScanBool_sound
      (((selected, I.graph.directed), (root, entries))) I.terminals hTerminals
    rcases hScan with ⟨hRoot, hAll⟩
    rcases hAll t ht with ⟨hEndpoint, hReach⟩
    rcases hTerms : I.terminals with _ | ⟨first, rest⟩
    · simp [hTerms] at ht
    · have hRootEq : root = first := by
        rcases hRoot with hNil | hHead
        · simp [hTerms] at hNil
        · simpa [hTerms] using hHead.symm
      refine ⟨?_, ?_⟩
      · simpa [selected] using hEndpoint
      · simpa [hRootEq, selected] using hReach

/-! ### Reachability witnesses for completeness -/

def chainBypass {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: rest =>
      let tail := chainBypass rest
      if h : a ∈ tail then
        tail.drop (tail.idxOf a)
      else
        a :: tail

theorem head?_drop_idxOf {α : Type} [DecidableEq α] {a : α} {xs : List α}
    (h : a ∈ xs) :
    (xs.drop (xs.idxOf a)).head? = some a := by
  rw [List.head?_eq_getElem?, List.getElem?_drop]
  simpa using List.getElem?_idxOf h

theorem getLast?_eq_of_suffix {α : Type} {xs ys : List α}
    (h : xs <:+ ys) (hne : xs ≠ []) :
    xs.getLast? = ys.getLast? := by
  rcases h with ⟨pre, rfl⟩
  exact (List.getLast?_append_of_ne_nil pre hne).symm

theorem chainBypass_head?_cons {α : Type} [DecidableEq α] (a : α) (rest : List α) :
    (chainBypass (a :: rest)).head? = some a := by
  by_cases h : a ∈ chainBypass rest
  · simpa [chainBypass, h] using head?_drop_idxOf h
  · simp [chainBypass, h]

theorem chainBypass_ne_nil {α : Type} [DecidableEq α] {xs : List α}
    (hxs : xs ≠ []) :
    chainBypass xs ≠ [] := by
  rcases xs with _ | ⟨a, rest⟩
  · contradiction
  · intro hnil
    have hhead := chainBypass_head?_cons a rest
    simp [hnil] at hhead

theorem chainBypass_getLast?_eq {α : Type} [DecidableEq α] :
    ∀ xs : List α, xs ≠ [] → (chainBypass xs).getLast? = xs.getLast?
  | [], hxs => False.elim (hxs rfl)
  | a :: [], _ => by
      simp [chainBypass]
  | a :: b :: rest, _ => by
      have ih :
          (chainBypass (b :: rest)).getLast? = (b :: rest).getLast? :=
        chainBypass_getLast?_eq (b :: rest) (by simp)
      by_cases h : a ∈ chainBypass (b :: rest)
      · have hSuffix :
            (chainBypass (b :: rest)).drop ((chainBypass (b :: rest)).idxOf a) <:+
              chainBypass (b :: rest) :=
          List.drop_suffix _ _
        have hNonempty :
            (chainBypass (b :: rest)).drop ((chainBypass (b :: rest)).idxOf a) ≠ [] := by
          intro hnil
          have hhead := head?_drop_idxOf h
          simp [hnil] at hhead
        calc
          (chainBypass (a :: b :: rest)).getLast?
              =
                ((chainBypass (b :: rest)).drop
                  ((chainBypass (b :: rest)).idxOf a)).getLast? := by
                    change
                      (if h' : a ∈ chainBypass (b :: rest) then
                          (chainBypass (b :: rest)).drop
                            ((chainBypass (b :: rest)).idxOf a)
                        else
                          a :: chainBypass (b :: rest)).getLast? =
                        ((chainBypass (b :: rest)).drop
                          ((chainBypass (b :: rest)).idxOf a)).getLast?
                    simp [h]
          _ = (chainBypass (b :: rest)).getLast? :=
                getLast?_eq_of_suffix hSuffix hNonempty
          _ = (b :: rest).getLast? := ih
          _ = (a :: b :: rest).getLast? := by simp
      · have hTailNonempty : chainBypass (b :: rest) ≠ [] :=
          chainBypass_ne_nil (by simp)
        calc
          (chainBypass (a :: b :: rest)).getLast?
              = (a :: chainBypass (b :: rest)).getLast? := by
                  change
                    (if h' : a ∈ chainBypass (b :: rest) then
                        (chainBypass (b :: rest)).drop
                          ((chainBypass (b :: rest)).idxOf a)
                      else
                        a :: chainBypass (b :: rest)).getLast? =
                      (a :: chainBypass (b :: rest)).getLast?
                  simp [h]
          _ = (chainBypass (b :: rest)).getLast? := by
                cases htail : chainBypass (b :: rest) with
                | nil => exact False.elim (hTailNonempty htail)
                | cons c tail => simp
          _ = (b :: rest).getLast? := ih
          _ = (a :: b :: rest).getLast? := by simp

theorem chainBypass_getLast?_cons {α : Type} [DecidableEq α]
    (a : α) (rest : List α) :
    (chainBypass (a :: rest)).getLast? = (a :: rest).getLast? :=
  chainBypass_getLast?_eq (a :: rest) (by simp)

theorem chainBypass_isChain {α : Type} [DecidableEq α] {R : α → α → Prop}
    {xs : List α} (hChain : xs.IsChain R) :
    (chainBypass xs).IsChain R := by
  induction xs with
  | nil =>
      simp [chainBypass]
  | cons a rest ih =>
      rcases rest with _ | ⟨b, rest⟩
      · simp [chainBypass]
      · have hTailChain : (b :: rest).IsChain R := hChain.tail
        have hTailBypass := ih hTailChain
        by_cases h : a ∈ chainBypass (b :: rest)
        · have hSuffix :
              (chainBypass (b :: rest)).drop ((chainBypass (b :: rest)).idxOf a) <:+
                chainBypass (b :: rest) :=
            List.drop_suffix _ _
          change
            (if h' : a ∈ chainBypass (b :: rest) then
                (chainBypass (b :: rest)).drop ((chainBypass (b :: rest)).idxOf a)
              else
                a :: chainBypass (b :: rest)).IsChain R
          simp [h, hTailBypass.suffix hSuffix]
        · have hHead : (chainBypass (b :: rest)).head? = some b :=
            chainBypass_head?_cons b rest
          have hRel : ∀ y ∈ (chainBypass (b :: rest)).head?, R a y := by
            intro y hy
            simp [hHead] at hy
            subst y
            exact hChain.rel_head
          have hCons := hTailBypass.cons hRel
          change
            (if h' : a ∈ chainBypass (b :: rest) then
                (chainBypass (b :: rest)).drop ((chainBypass (b :: rest)).idxOf a)
              else
                a :: chainBypass (b :: rest)).IsChain R
          simp [h, hCons]

theorem chainBypass_nodup {α : Type} [DecidableEq α] (xs : List α) :
    (chainBypass xs).Nodup := by
  induction xs with
  | nil =>
      simp [chainBypass]
  | cons a rest ih =>
      by_cases h : a ∈ chainBypass rest
      · have hSuffix :
            (chainBypass rest).drop ((chainBypass rest).idxOf a) <:+ chainBypass rest :=
          List.drop_suffix _ _
        change
          (if h' : a ∈ chainBypass rest then
              (chainBypass rest).drop ((chainBypass rest).idxOf a)
            else
              a :: chainBypass rest).Nodup
        simp [h, ih.sublist hSuffix.sublist]
      · have hCons : (a :: chainBypass rest).Nodup := List.Nodup.cons h ih
        change
          (if h' : a ∈ chainBypass rest then
              (chainBypass rest).drop ((chainBypass rest).idxOf a)
            else
              a :: chainBypass rest).Nodup
        simp [h, hCons]

theorem chainBypass_subset {α : Type} [DecidableEq α] (xs : List α) :
    chainBypass xs ⊆ xs := by
  induction xs with
  | nil =>
      intro x hx
      simp [chainBypass] at hx
  | cons a rest ih =>
      by_cases h : a ∈ chainBypass rest
      · have hSuffix :
            (chainBypass rest).drop ((chainBypass rest).idxOf a) <:+ chainBypass rest :=
          List.drop_suffix _ _
        intro x hx
        have hxDrop :
            x ∈ (chainBypass rest).drop ((chainBypass rest).idxOf a) := by
          simpa [chainBypass, h] using hx
        exact List.mem_cons_of_mem a (ih (hSuffix.sublist.subset hxDrop))
      · intro x hx
        simp [chainBypass, h] at hx
        rcases hx with hxa | hxTail
        · subst x
          simp
        · exact List.mem_cons_of_mem a (ih hxTail)

def weightedEndpointSupport (selected : List (Nat × Nat × Nat)) (root : Nat) : List Nat :=
  root :: selected.flatMap (fun e => [e.1, e.2.1])

theorem weightedEndpointSupport_length
    (selected : List (Nat × Nat × Nat)) (root : Nat) :
    (weightedEndpointSupport selected root).length = 1 + 2 * selected.length := by
  induction selected with
  | nil =>
      simp [weightedEndpointSupport]
  | cons e rest ih =>
      simp [weightedEndpointSupport, ih]
      omega

theorem weightedEndpointSupport_mem_of_adj
    {selected : List (Nat × Nat × Nat)} {directed : Bool}
    {root u v : Nat}
    (hAdj : WeightedAdjacent selected directed u v) :
    v ∈ weightedEndpointSupport selected root := by
  rcases hAdj with ⟨e, he, hTrav⟩
  rcases e with ⟨a, b, w⟩
  rcases hTrav with hForward | hReverse
  · rcases hForward with ⟨rfl, rfl⟩
    have hFlat : b ∈ selected.flatMap (fun e => [e.1, e.2.1]) := by
      exact List.mem_flatMap.mpr ⟨(a, b, w), he, by simp⟩
    exact List.mem_cons_of_mem root hFlat
  · rcases hReverse with ⟨_hDir, rfl, rfl⟩
    have hFlat : a ∈ selected.flatMap (fun e => [e.1, e.2.1]) := by
      exact List.mem_flatMap.mpr ⟨(a, b, w), he, by simp⟩
    exact List.mem_cons_of_mem root hFlat

theorem isChain_mem_weightedEndpointSupport
    {selected : List (Nat × Nat × Nat)} {directed : Bool}
    {root : Nat} {rest : List Nat}
    (hChain : (root :: rest).IsChain (WeightedAdjacent selected directed)) :
    ∀ v ∈ root :: rest, v ∈ weightedEndpointSupport selected root := by
  intro v hv
  rcases List.mem_cons.mp hv with hRoot | hRest
  · subst v
    simp [weightedEndpointSupport]
  · exact hChain.cons_induction
      (p := fun v => v ∈ weightedEndpointSupport selected root)
      (l := rest)
      (carries := by
        intro x y hAdj _hx
        exact weightedEndpointSupport_mem_of_adj (root := root) hAdj)
      (initial := by simp [weightedEndpointSupport])
      v hRest

theorem weightedReachable_to_reflTransGen
    {selected : List (Nat × Nat × Nat)} {directed : Bool} {u v : Nat}
    (hReach : WeightedReachable selected directed u v) :
    Relation.ReflTransGen (WeightedAdjacent selected directed) u v := by
  induction hReach with
  | refl u =>
      exact Relation.ReflTransGen.refl
  | step hAdj _hReach ih =>
      exact Relation.ReflTransGen.head hAdj ih

theorem weightedAdjacent_dedup
    {selected : List (Nat × Nat × Nat)} {directed : Bool} {u v : Nat}
    (hAdj : WeightedAdjacent selected directed u v) :
    WeightedAdjacent selected.dedup directed u v := by
  rcases hAdj with ⟨e, he, hTrav⟩
  exact ⟨e, List.mem_dedup.mpr he, hTrav⟩

theorem weightedReachable_dedup
    {selected : List (Nat × Nat × Nat)} {directed : Bool} {u v : Nat}
    (hReach : WeightedReachable selected directed u v) :
    WeightedReachable selected.dedup directed u v := by
  induction hReach with
  | refl u =>
      exact WeightedReachable.refl u
  | step hAdj _hReach ih =>
      exact WeightedReachable.step (weightedAdjacent_dedup hAdj) ih

theorem weightedEndpoint_dedup
    {selected : List (Nat × Nat × Nat)} {t : Nat}
    (hEndpoint : ∃ e ∈ selected, WeightedEdgeHasEndpoint e t) :
    ∃ e ∈ selected.dedup, WeightedEdgeHasEndpoint e t := by
  rcases hEndpoint with ⟨e, he, hEnd⟩
  exact ⟨e, List.mem_dedup.mpr he, hEnd⟩

theorem weightedEdgeListWeight_dedup_le (selected : List (Nat × Nat × Nat)) :
    WeightedEdgeListWeight selected.dedup ≤ WeightedEdgeListWeight selected := by
  simpa [WeightedEdgeListWeight] using
    Knapsack.sum_map_le_of_sublist (fun e : Nat × Nat × Nat => e.2.2)
      (List.dedup_sublist selected)

theorem exists_bounded_steinerPathBool_of_weightedReachable
    {selected : List (Nat × Nat × Nat)} {directed : Bool}
    {root target : Nat}
    (hReach : WeightedReachable selected directed root target) :
    ∃ path : List Nat,
      steinerPathBool (((selected, directed), (root, target)), path) = true ∧
        path.Nodup ∧ path.length ≤ 1 + 2 * selected.length ∧
        ∀ v ∈ path, v ∈ weightedEndpointSupport selected root := by
  classical
  rcases List.exists_isChain_cons_of_relationReflTransGen
      (weightedReachable_to_reflTransGen hReach) with
    ⟨rest, hChain, hLast⟩
  let rawPath := root :: rest
  let path := chainBypass rawPath
  have hPathHead : root ∈ path.head? := by
    simpa [path, rawPath] using chainBypass_head?_cons root rest
  have hPathLast : target ∈ path.getLast? := by
    have hLast? : rawPath.getLast? = some target := by
      have hne : rawPath ≠ [] := by simp [rawPath]
      have hGetLast : rawPath.getLast hne = target := by
        simpa [rawPath] using hLast
      simpa [List.getLast?_eq_getLast_of_ne_nil hne, hGetLast]
    simpa [path, rawPath, hLast?] using chainBypass_getLast?_cons root rest
  have hPathChain :
      path.IsChain (weightedAdjacentBoolRel selected directed) := by
    have hSimple : path.IsChain (WeightedAdjacent selected directed) := by
      simpa [path, rawPath] using chainBypass_isChain hChain
    exact hSimple.imp (fun u v hAdj => (weightedAdjacentBoolRel_iff selected directed u v).2 hAdj)
  have hPathBool :
      steinerPathBool (((selected, directed), (root, target)), path) = true :=
    (steinerPathBool_eq_true_iff ((selected, directed), (root, target)) path).2
      ⟨hPathChain, hPathHead, hPathLast⟩
  have hPathNodup : path.Nodup := by
    simpa [path, rawPath] using chainBypass_nodup rawPath
  have hRawSupport :
      ∀ v ∈ rawPath, v ∈ weightedEndpointSupport selected root := by
    simpa [rawPath] using isChain_mem_weightedEndpointSupport hChain
  have hPathSupport :
      ∀ v ∈ path, v ∈ weightedEndpointSupport selected root := by
    intro v hv
    exact hRawSupport v (chainBypass_subset rawPath hv)
  have hLenSupport :
      path.length ≤ (weightedEndpointSupport selected root).length :=
    FiniteWitness.nodup_length_le_of_mem hPathNodup hPathSupport
  have hLen : path.length ≤ 1 + 2 * selected.length := by
    simpa [weightedEndpointSupport_length selected root] using hLenSupport
  exact ⟨path, hPathBool, hPathNodup, hLen, hPathSupport⟩

theorem steinerTreeStructuredFiniteVerify_complete
    (I : SteinerTreeInput) (hYes : SteinerTree I) :
    ∃ cert : SteinerTreeCertificate,
      steinerTreeStructuredFiniteVerify I cert = true := by
  classical
  rcases hYes with ⟨selectedRaw, hEdgesRaw, hContainsRaw, hWeightRaw⟩
  let selected := selectedRaw.dedup
  let root : Nat :=
    match I.terminals with
    | [] => 0
    | first :: _ => first
  have hEdges : ∀ e ∈ selected, e ∈ I.graph.edges := by
    intro e he
    exact hEdgesRaw e (List.mem_dedup.mp he)
  have hWeight : WeightedEdgeListWeight selected ≤ I.weightBound := by
    exact (weightedEdgeListWeight_dedup_le selectedRaw).trans hWeightRaw
  have hContains : ContainsTerminals selected I.terminals I.graph.directed := by
    intro t ht
    have hRaw := hContainsRaw t ht
    rcases hRaw with ⟨hEndpointRaw, hReachRaw⟩
    refine ⟨weightedEndpoint_dedup hEndpointRaw, ?_⟩
    rcases hTerms : I.terminals with _ | ⟨first, rest⟩
    · simp [hTerms] at ht
    · have hReachRaw' :
          WeightedReachable selectedRaw I.graph.directed first t := by
        simpa [hTerms] using hReachRaw
      simpa [selected, hTerms] using weightedReachable_dedup hReachRaw'
  have hRoot : I.terminals = [] ∨ root ∈ I.terminals.head? := by
    rcases hTerms : I.terminals with _ | ⟨first, rest⟩
    · exact Or.inl rfl
    · right
      simp [root, hTerms]
  have hReachFromRoot :
      ∀ t ∈ I.terminals, WeightedReachable selected I.graph.directed root t := by
    intro t ht
    have hReach := (hContains t ht).2
    rcases hTerms : I.terminals with _ | ⟨first, rest⟩
    · simp [hTerms] at ht
    · simpa [root, hTerms] using hReach
  let pathOf : Nat → List Nat := fun t =>
    if ht : t ∈ I.terminals then
      Classical.choose
        (exists_bounded_steinerPathBool_of_weightedReachable
          (selected := selected) (directed := I.graph.directed)
          (root := root) (target := t) (hReachFromRoot t ht))
    else
      []
  let entries : List SteinerPathEntry := I.terminals.map fun t => (t, pathOf t)
  let cert : SteinerTreeCertificate := (root, (selected, entries))
  refine ⟨cert, ?_⟩
  refine (steinerTreeStructuredFiniteVerify_eq_true_iff I cert).2 ⟨hWeight, hEdges, ?_⟩
  let ctx : SteinerTerminalScanContext := ((selected, I.graph.directed), (root, entries))
  have hCoverage : ∀ t ∈ I.terminals, steinerTerminalCoverageBool (ctx, t) = true := by
    intro t ht
    have hEndpoint := (hContains t ht).1
    have hPathSpec :
        steinerPathBool (((selected, I.graph.directed), (root, t)), pathOf t) = true ∧
          (pathOf t).Nodup ∧ (pathOf t).length ≤ 1 + 2 * selected.length ∧
          ∀ v ∈ pathOf t, v ∈ weightedEndpointSupport selected root := by
      have hExists :=
        exists_bounded_steinerPathBool_of_weightedReachable
          (selected := selected) (directed := I.graph.directed)
          (root := root) (target := t) (hReachFromRoot t ht)
      simpa [pathOf, ht] using Classical.choose_spec hExists
    refine (steinerTerminalCoverageBool_eq_true_iff ctx t).2 ?_
    refine ⟨hEndpoint, ?_⟩
    refine ⟨(t, pathOf t), ?_, rfl, hPathSpec.1⟩
    exact List.mem_map.mpr ⟨t, ht, rfl⟩
  simpa [cert, ctx] using
    steinerTerminalScanBool_complete ctx I.terminals hRoot hCoverage

/-! ### Certificate size bound and NP membership -/

theorem encodedList_length_le_inputSize (X : EncodedType) (xs : List X.Carrier) :
    xs.length ≤ (EncodedType.list X).inputSize xs := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [EncodedType.inputSize_list_cons]
      change xs.length + 1 ≤ X.inputSize x + 1 + (EncodedType.list X).inputSize xs
      exact (Nat.succ_le_succ ih).trans (by omega)
theorem encodedList_element_inputSize_le {X : EncodedType} {x : X.Carrier}
    {xs : List X.Carrier} (hx : x ∈ xs) :
    X.inputSize x ≤ (EncodedType.list X).inputSize xs := by
  induction xs with
  | nil =>
      simp at hx
  | cons y ys ih =>
      rw [EncodedType.inputSize_list_cons]
      rcases List.mem_cons.mp hx with hxy | hxys
      · subst x
        omega
      · have hTail := ih hxys
        omega
theorem steinerTreeStructured_inputSize_ge_edgeList (I : SteinerTreeInput) :
    weightedEdgeListStructuredEncodedType.inputSize I.graph.edges ≤
      steinerTreeStructuredEncodedType.inputSize I := by
  rw [ComplexityReduction.Karp21.SteinerTree.steinerTreeStructured_inputSize_eq,
    ComplexityReduction.Karp21.SteinerTree.weightedGraphStructured_inputSize_eq]
  omega
theorem steinerTreeStructured_inputSize_ge_terminalList (I : SteinerTreeInput) :
    (EncodedType.list EncodedType.nat).inputSize I.terminals ≤
      steinerTreeStructuredEncodedType.inputSize I := by
  rw [ComplexityReduction.Karp21.SteinerTree.steinerTreeStructured_inputSize_eq]
  omega
theorem steinerTreeStructured_inputSize_ge_edges_length (I : SteinerTreeInput) :
    I.graph.edges.length ≤ steinerTreeStructuredEncodedType.inputSize I := by
  exact (encodedList_length_le_inputSize weightedEdgeStructuredEncodedType I.graph.edges).trans
    (steinerTreeStructured_inputSize_ge_edgeList I)
theorem steinerTreeStructured_inputSize_ge_terminals_length (I : SteinerTreeInput) :
    I.terminals.length ≤ steinerTreeStructuredEncodedType.inputSize I := by
  exact (encodedList_length_le_inputSize EncodedType.nat I.terminals).trans
    (steinerTreeStructured_inputSize_ge_terminalList I)
theorem steinerTreeStructured_inputSize_ge_edge_inputSize
    {I : SteinerTreeInput} {e : Nat × Nat × Nat} (he : e ∈ I.graph.edges) :
    weightedEdgeStructuredEncodedType.inputSize e ≤
      steinerTreeStructuredEncodedType.inputSize I := by
  exact (encodedList_element_inputSize_le
    (X := weightedEdgeStructuredEncodedType) he).trans
    (steinerTreeStructured_inputSize_ge_edgeList I)
theorem steinerTreeStructured_inputSize_ge_terminal_inputSize
    {I : SteinerTreeInput} {t : Nat} (ht : t ∈ I.terminals) :
    EncodedType.nat.inputSize t ≤ steinerTreeStructuredEncodedType.inputSize I := by
  exact (encodedList_element_inputSize_le (X := EncodedType.nat) ht).trans
    (steinerTreeStructured_inputSize_ge_terminalList I)
theorem weightedEdge_endpoint_inputSize_le (e : Nat × Nat × Nat) :
    EncodedType.nat.inputSize e.1 ≤ weightedEdgeStructuredEncodedType.inputSize e ∧
      EncodedType.nat.inputSize e.2.1 ≤ weightedEdgeStructuredEncodedType.inputSize e := by
  rcases e with ⟨u, v, w⟩
  simp [weightedEdgeStructuredEncodedType]
  omega
theorem weightedEndpointSupport_inputSize_le
    (I : SteinerTreeInput) {selected : List (Nat × Nat × Nat)} {root v : Nat}
    (hEdges : ∀ e ∈ selected, e ∈ I.graph.edges)
    (hRoot : EncodedType.nat.inputSize root ≤ steinerTreeStructuredEncodedType.inputSize I + 1)
    (hv : v ∈ weightedEndpointSupport selected root) :
    EncodedType.nat.inputSize v ≤ steinerTreeStructuredEncodedType.inputSize I + 1 := by
  rcases List.mem_cons.mp hv with hRootMem | hFlat
  · subst v
    exact hRoot
  · rcases List.mem_flatMap.mp hFlat with ⟨e, heSelected, hvEndpoint⟩
    have heGraph := hEdges e heSelected
    have heSize := steinerTreeStructured_inputSize_ge_edge_inputSize (I := I) heGraph
    rcases e with ⟨a, b, w⟩
    simp at hvEndpoint
    rcases hvEndpoint with hA | hB
    · subst v
      exact ((weightedEdge_endpoint_inputSize_le (a, b, w)).1.trans heSize).trans
        (Nat.le_succ _)
    · subst v
      exact ((weightedEdge_endpoint_inputSize_le (a, b, w)).2.trans heSize).trans
        (Nat.le_succ _)
noncomputable def steinerTreeStructuredFiniteTMVerifier :
    TMVerifier steinerTreeStructuredDecisionProblem where
  Cert := steinerTreeCertificateEncodedType
  verify := steinerTreeStructuredFiniteVerify
  verifier_polytime := steinerTreeStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨6, 100000, 100000, ?_⟩
    intro I hYes
    classical
    rcases hYes with ⟨selectedRaw, hEdgesRaw, hContainsRaw, hWeightRaw⟩
    let S := steinerTreeStructuredEncodedType.inputSize I
    let selected := selectedRaw.dedup
    let root : Nat :=
      match I.terminals with
      | [] => 0
      | first :: _ => first
    have hEdges : ∀ e ∈ selected, e ∈ I.graph.edges := by
      intro e he
      exact hEdgesRaw e (List.mem_dedup.mp he)
    have hWeight : WeightedEdgeListWeight selected ≤ I.weightBound := by
      exact (weightedEdgeListWeight_dedup_le selectedRaw).trans hWeightRaw
    have hContains : ContainsTerminals selected I.terminals I.graph.directed := by
      intro t ht
      have hRaw := hContainsRaw t ht
      rcases hRaw with ⟨hEndpointRaw, hReachRaw⟩
      refine ⟨weightedEndpoint_dedup hEndpointRaw, ?_⟩
      rcases hTerms : I.terminals with _ | ⟨first, rest⟩
      · simp [hTerms] at ht
      · have hReachRaw' :
            WeightedReachable selectedRaw I.graph.directed first t := by
          simpa [hTerms] using hReachRaw
        simpa [selected, hTerms] using weightedReachable_dedup hReachRaw'
    have hRootOK : I.terminals = [] ∨ root ∈ I.terminals.head? := by
      rcases hTerms : I.terminals with _ | ⟨first, rest⟩
      · exact Or.inl rfl
      · right
        simp [root, hTerms]
    have hReachFromRoot :
        ∀ t ∈ I.terminals, WeightedReachable selected I.graph.directed root t := by
      intro t ht
      have hReach := (hContains t ht).2
      rcases hTerms : I.terminals with _ | ⟨first, rest⟩
      · simp [hTerms] at ht
      · simpa [root, hTerms] using hReach
    let pathOf : Nat → List Nat := fun t =>
      if ht : t ∈ I.terminals then
        Classical.choose
          (exists_bounded_steinerPathBool_of_weightedReachable
            (selected := selected) (directed := I.graph.directed)
            (root := root) (target := t) (hReachFromRoot t ht))
      else
        []
    let entries : List SteinerPathEntry := I.terminals.map fun t => (t, pathOf t)
    let cert : SteinerTreeCertificate := (root, (selected, entries))
    have hVerify : steinerTreeStructuredFiniteVerify I cert = true := by
      refine (steinerTreeStructuredFiniteVerify_eq_true_iff I cert).2
        ⟨hWeight, hEdges, ?_⟩
      let ctx : SteinerTerminalScanContext := ((selected, I.graph.directed), (root, entries))
      have hCoverage : ∀ t ∈ I.terminals, steinerTerminalCoverageBool (ctx, t) = true := by
        intro t ht
        have hEndpoint := (hContains t ht).1
        have hPathSpec :
            steinerPathBool (((selected, I.graph.directed), (root, t)), pathOf t) = true ∧
              (pathOf t).Nodup ∧ (pathOf t).length ≤ 1 + 2 * selected.length ∧
              ∀ v ∈ pathOf t, v ∈ weightedEndpointSupport selected root := by
          have hExists :=
            exists_bounded_steinerPathBool_of_weightedReachable
              (selected := selected) (directed := I.graph.directed)
              (root := root) (target := t) (hReachFromRoot t ht)
          simpa [pathOf, ht] using Classical.choose_spec hExists
        refine (steinerTerminalCoverageBool_eq_true_iff ctx t).2 ?_
        refine ⟨hEndpoint, ?_⟩
        refine ⟨(t, pathOf t), ?_, rfl, hPathSpec.1⟩
        exact List.mem_map.mpr ⟨t, ht, rfl⟩
      simpa [cert, ctx] using
        steinerTerminalScanBool_complete ctx I.terminals hRootOK hCoverage
    have hRootSize :
        EncodedType.nat.inputSize root ≤ S + 1 := by
      rcases hTerms : I.terminals with _ | ⟨first, rest⟩
      · simp [root, hTerms, S]
      · have hFirstMem : first ∈ I.terminals := by simp [hTerms]
        have hFirstSize :=
          steinerTreeStructured_inputSize_ge_terminal_inputSize (I := I) hFirstMem
        have hFirstSize' : EncodedType.nat.inputSize first ≤ S + 1 := by
          simpa [S] using hFirstSize.trans (Nat.le_succ _)
        simpa [root, hTerms] using hFirstSize'
    have hSelectedLen : selected.length ≤ S := by
      have hLenToGraph :
          selected.length ≤ I.graph.edges.length :=
        FiniteWitness.nodup_length_le_of_mem (List.nodup_dedup selectedRaw) hEdges
      exact hLenToGraph.trans (by simpa [S] using
        steinerTreeStructured_inputSize_ge_edges_length I)
    have hSelectedElemSize :
        ∀ e ∈ selected, weightedEdgeStructuredEncodedType.inputSize e ≤ S := by
      intro e he
      simpa [S] using steinerTreeStructured_inputSize_ge_edge_inputSize (I := I) (hEdges e he)
    have hSelectedSize :
        weightedEdgeListStructuredEncodedType.inputSize selected ≤ S * (S + 1) := by
      have hList :=
        ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
          weightedEdgeStructuredEncodedType selected S hSelectedElemSize
      exact hList.trans (Nat.mul_le_mul_right (S + 1) hSelectedLen)
    have hTerminalLen : I.terminals.length ≤ S := by
      simpa [S] using steinerTreeStructured_inputSize_ge_terminals_length I
    have hEntriesLen : entries.length ≤ S := by
      simpa [entries] using hTerminalLen
    have hEntryElemSize :
        ∀ entry ∈ entries,
          steinerPathEntryEncodedType.inputSize entry ≤ 10 * (S + 2) ^ 2 := by
      intro entry hEntry
      rcases List.mem_map.mp hEntry with ⟨t, ht, rfl⟩
      have hTermSize :
          EncodedType.nat.inputSize t ≤ S := by
        simpa [S] using steinerTreeStructured_inputSize_ge_terminal_inputSize (I := I) ht
      have hPathSpec :
          steinerPathBool (((selected, I.graph.directed), (root, t)), pathOf t) = true ∧
            (pathOf t).Nodup ∧ (pathOf t).length ≤ 1 + 2 * selected.length ∧
            ∀ v ∈ pathOf t, v ∈ weightedEndpointSupport selected root := by
        have hExists :=
          exists_bounded_steinerPathBool_of_weightedReachable
            (selected := selected) (directed := I.graph.directed)
            (root := root) (target := t) (hReachFromRoot t ht)
        simpa [pathOf, ht] using Classical.choose_spec hExists
      have hPathLen : (pathOf t).length ≤ 1 + 2 * S := by
        have hBase := hPathSpec.2.2.1
        omega
      have hPathElem :
          ∀ v ∈ pathOf t, EncodedType.nat.inputSize v ≤ S + 1 := by
        intro v hv
        exact weightedEndpointSupport_inputSize_le I hEdges hRootSize (hPathSpec.2.2.2 v hv)
      have hPathSize :
          (EncodedType.list EncodedType.nat).inputSize (pathOf t) ≤
            (1 + 2 * S) * (S + 2) := by
        have hList :=
          ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
            EncodedType.nat (pathOf t) (S + 1) hPathElem
        calc
          (EncodedType.list EncodedType.nat).inputSize (pathOf t)
              ≤ (pathOf t).length * (S + 1 + 1) := hList
          _ ≤ (1 + 2 * S) * (S + 2) := by
              exact Nat.mul_le_mul_right (S + 2) hPathLen
      calc
        steinerPathEntryEncodedType.inputSize (t, pathOf t)
            = EncodedType.nat.inputSize t + 1 +
                (EncodedType.list EncodedType.nat).inputSize (pathOf t) := by
              simp [steinerPathEntryEncodedType]
        _ ≤ S + 1 + ((1 + 2 * S) * (S + 2)) := by
              omega
        _ ≤ 10 * (S + 2) ^ 2 := by
              nlinarith [sq_nonneg (S : Int)]
    have hEntriesSize :
        steinerPathEntryListEncodedType.inputSize entries ≤
          S * (10 * (S + 2) ^ 2 + 1) := by
      have hList :=
        ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
          steinerPathEntryEncodedType entries (10 * (S + 2) ^ 2) hEntryElemSize
      exact hList.trans (Nat.mul_le_mul_right (10 * (S + 2) ^ 2 + 1) hEntriesLen)
    have hCertCubic :
        steinerTreeCertificateEncodedType.inputSize cert ≤ 100 * (S + 2) ^ 3 := by
      calc
        steinerTreeCertificateEncodedType.inputSize cert
            = EncodedType.nat.inputSize root + 1 +
                (weightedEdgeListStructuredEncodedType.inputSize selected + 1 +
                  steinerPathEntryListEncodedType.inputSize entries) := by
              simp [cert, steinerTreeCertificateEncodedType]
        _ ≤ (S + 1) + 1 + (S * (S + 1) + 1 +
              S * (10 * (S + 2) ^ 2 + 1)) := by
              omega
        _ ≤ 100 * (S + 2) ^ 3 := by
              nlinarith [sq_nonneg (S : Int)]
    refine ⟨cert, ?_, hVerify⟩
    calc
      steinerTreeCertificateEncodedType.inputSize cert
          ≤ 100 * (S + 2) ^ 3 := hCertCubic
      _ ≤ 100000 * (steinerTreeStructuredEncodedType.inputSize I) ^ 6 + 100000 := by
          by_cases hS0 : S = 0
          · norm_num [S, hS0]
          · have hSpos : 1 ≤ S := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hS0)
            have hShift : S + 2 ≤ 3 * S := by omega
            have hPowShift : (S + 2) ^ 3 ≤ (3 * S) ^ 3 :=
              pow_le_pow_left' hShift 3
            have hPow36 : S ^ 3 ≤ S ^ 6 :=
              pow_le_pow_right' hSpos (by norm_num : (3 : Nat) ≤ 6)
            have hPoly : 100 * (S + 2) ^ 3 ≤ 100000 * S ^ 6 + 100000 := by
              calc
                100 * (S + 2) ^ 3 ≤ 100 * (3 * S) ^ 3 :=
                  Nat.mul_le_mul_left 100 hPowShift
                _ = 2700 * S ^ 3 := by ring
                _ ≤ 2700 * S ^ 6 := Nat.mul_le_mul_left 2700 hPow36
                _ ≤ 100000 * S ^ 6 + 100000 := by omega
            simpa [S] using hPoly
  sound := by
    intro I cert hVerify
    exact steinerTreeStructuredFiniteVerify_sound I cert hVerify

theorem steinerTreeStructured_TMInNP :
    TMInNP steinerTreeStructuredDecisionProblem :=
  TMInNP.intro steinerTreeStructuredFiniteTMVerifier

end SteinerTreeMembership

end Karp21
end ComplexityReduction
