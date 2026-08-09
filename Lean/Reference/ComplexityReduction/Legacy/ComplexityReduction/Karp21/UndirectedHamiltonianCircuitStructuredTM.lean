/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.UndirectedHamiltonianCircuit
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM

/-!
Direct TM-backed structured assembly for the Directed Hamiltonian Circuit to
Undirected Hamiltonian Circuit in/mid/out replacement route.
-/

namespace ComplexityReduction
namespace Karp21
namespace UndirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

/-! ### Source and target reifiers -/

theorem directedHamiltonianCircuitGraph_encode (I : DirectedHamiltonianCircuitInput) :
    graphStructuredEncodedType.encode I.graph =
      directedHamiltonianCircuitStructuredEncodedType.encode I := by
  rfl

noncomputable def directedHamiltonianCircuitGraphTMBackedMap :
    TMBackedCostedMap
      directedHamiltonianCircuitStructuredEncodedType
      graphStructuredEncodedType
      (fun I : DirectedHamiltonianCircuitInput => I.graph) :=
  TMBackedCostedMap.ofEncodingEquiv
    directedHamiltonianCircuitStructuredEncodedType
    graphStructuredEncodedType
    (fun I : DirectedHamiltonianCircuitInput => I.graph)
    (Equiv.refl directedHamiltonianCircuitStructuredEncodedType.Symbol)
    (by
      intro I
      change graphStructuredEncodedType.encode I.graph =
        (directedHamiltonianCircuitStructuredEncodedType.encode I).map id
      simp [directedHamiltonianCircuitGraph_encode])

def undirectedHamiltonianCircuitGraphToInput (g : GraphInput) :
    UndirectedHamiltonianCircuitInput where
  graph := g

theorem undirectedHamiltonianCircuitGraphToInput_encode (g : GraphInput) :
    undirectedHamiltonianCircuitStructuredEncodedType.encode
        (undirectedHamiltonianCircuitGraphToInput g) =
      graphStructuredEncodedType.encode g := by
  rfl

noncomputable def undirectedHamiltonianCircuitGraphToInputTMBackedMap :
    TMBackedCostedMap
      graphStructuredEncodedType
      undirectedHamiltonianCircuitStructuredEncodedType
      undirectedHamiltonianCircuitGraphToInput :=
  TMBackedCostedMap.ofEncodingEquiv
    graphStructuredEncodedType
    undirectedHamiltonianCircuitStructuredEncodedType
    undirectedHamiltonianCircuitGraphToInput
    (Equiv.refl graphStructuredEncodedType.Symbol)
    (by
      intro g
      change
        undirectedHamiltonianCircuitStructuredEncodedType.encode
            (undirectedHamiltonianCircuitGraphToInput g) =
          (graphStructuredEncodedType.encode g).map id
      simp [undirectedHamiltonianCircuitGraphToInput_encode])

/-! ### Replacement vertices and edge blocks -/

def uhcNatTriple (n : Nat) : Nat :=
  natDouble n + n

theorem uhcNatTriple_tm_polytime :
    TMPolyTimeMap EncodedType.nat EncodedType.nat uhcNatTriple := by
  have hPair :
      TMPolyTimeMap EncodedType.nat natAddInputEncodedType
        (fun n : Nat => (natDouble n, n)) :=
    TMPolyTimeMap.prod_mk natDouble_tm_polytime (TMPolyTimeMap.id EncodedType.nat)
  have hComp := TMPolyTimeMap.comp natAdd_tm_polytime hPair
  simpa [Function.comp, uhcNatTriple, natAddInputEncodedType] using hComp

theorem inVertex_tm_polytime :
    TMPolyTimeMap EncodedType.nat EncodedType.nat inVertex := by
  convert uhcNatTriple_tm_polytime using 1
  funext n
  simp [inVertex, uhcNatTriple, natDouble]
  omega

theorem midVertex_tm_polytime :
    TMPolyTimeMap EncodedType.nat EncodedType.nat midVertex := by
  have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime inVertex_tm_polytime
  simpa [Function.comp, midVertex, inVertex] using hComp

theorem outVertex_tm_polytime :
    TMPolyTimeMap EncodedType.nat EncodedType.nat outVertex := by
  have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime midVertex_tm_polytime
  simpa [Function.comp, outVertex, midVertex] using hComp

theorem internalEdgesForVertex_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      edgeListStructuredEncodedType
      internalEdgesForVertex := by
  let X := EncodedType.nat
  have hIn : TMPolyTimeMap X EncodedType.nat (fun v : Nat => inVertex v) :=
    inVertex_tm_polytime
  have hMid : TMPolyTimeMap X EncodedType.nat (fun v : Nat => midVertex v) :=
    midVertex_tm_polytime
  have hOut : TMPolyTimeMap X EncodedType.nat (fun v : Nat => outVertex v) :=
    outVertex_tm_polytime
  have hFirst : TMPolyTimeMap X edgeStructuredEncodedType
      (fun v : Nat => (inVertex v, midVertex v)) := by
    have hPair := TMPolyTimeMap.prod_mk hIn hMid
    simpa [edgeStructuredEncodedType, X] using hPair
  have hSecond : TMPolyTimeMap X edgeStructuredEncodedType
      (fun v : Nat => (midVertex v, outVertex v)) := by
    have hPair := TMPolyTimeMap.prod_mk hMid hOut
    simpa [edgeStructuredEncodedType, X] using hPair
  have hSecondSingleton :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun v : Nat => [(midVertex v, outVertex v)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton edgeStructuredEncodedType)
      hSecond
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeStructuredEncodedType edgeListStructuredEncodedType)
        (fun v : Nat => ((inVertex v, midVertex v), [(midVertex v, outVertex v)])) :=
    TMPolyTimeMap.prod_mk hFirst hSecondSingleton
  have hOutList :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons edgeStructuredEncodedType) hConsInput
  simpa [Function.comp, internalEdgesForVertex, edgeListStructuredEncodedType, X] using hOutList

def uhcInternalFoldStep
    (p : edgeListStructuredEncodedType.Carrier × Nat) :
    edgeListStructuredEncodedType.Carrier :=
  (show List (Nat × Nat) from p.1) ++ internalEdgesForVertex p.2

def uhcInternalEdgesExecutableFromVertices (vertices : Nat) : List (Nat × Nat) :=
  (List.range vertices).foldl
    (fun out v => uhcInternalFoldStep (out, v))
    ([] : List (Nat × Nat))

theorem uhcInternalFold_eq_append_flatMap
    (xs : List Nat) (out : List (Nat × Nat)) :
    xs.foldl (fun out v => uhcInternalFoldStep (out, v)) out =
      out ++ xs.flatMap internalEdgesForVertex := by
  induction xs generalizing out with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.foldl_cons]
      rw [ih (uhcInternalFoldStep (out, x))]
      rw [uhcInternalFoldStep]
      simp [List.append_assoc]

theorem uhcInternalEdgesExecutableFromVertices_eq_flatMap (vertices : Nat) :
    uhcInternalEdgesExecutableFromVertices vertices =
      (List.range vertices).flatMap internalEdgesForVertex := by
  simpa [uhcInternalEdgesExecutableFromVertices] using
    (uhcInternalFold_eq_append_flatMap (List.range vertices) ([] : List (Nat × Nat)))

def uhcInternalEdgesExecutable (I : DirectedHamiltonianCircuitInput) : List (Nat × Nat) :=
  uhcInternalEdgesExecutableFromVertices I.graph.vertices

theorem uhcInternalEdgesExecutable_eq_textbookInternalEdges
    (I : DirectedHamiltonianCircuitInput) :
    uhcInternalEdgesExecutable I = textbookInternalEdges I := by
  simp [uhcInternalEdgesExecutable, textbookInternalEdges,
    uhcInternalEdgesExecutableFromVertices_eq_flatMap]

theorem edgeListStructured_inputSize_append
    (xs ys : List (Nat × Nat)) :
    edgeListStructuredEncodedType.inputSize (xs ++ ys) =
      edgeListStructuredEncodedType.inputSize xs +
        edgeListStructuredEncodedType.inputSize ys := by
  simpa [edgeListStructuredEncodedType] using
    list_inputSize_append edgeStructuredEncodedType xs ys

theorem internalEdgesForVertex_inputSize_le
    (v : Nat) {N : Nat} (hv : EncodedType.nat.inputSize v ≤ N) :
    edgeListStructuredEncodedType.inputSize (internalEdgesForVertex v) ≤ 20 * N + 20 := by
  have hvNat : v ≤ N := by
    have hv' : v + 1 ≤ N := by simpa [EncodedType.inputSize_nat] using hv
    omega
  change
    (EncodedType.list edgeStructuredEncodedType).inputSize
        ([(inVertex v, midVertex v), (midVertex v, outVertex v)] : List (Nat × Nat)) ≤
      20 * N + 20
  simp [EncodedType.inputSize, EncodedType.list, edgeStructuredEncodedType,
    EncodedType.prod, EncodedType.nat, inVertex, midVertex, outVertex]
  omega

noncomputable def uhcInternalFoldGrowPolynomial : Polynomial Nat :=
  Polynomial.C 20 * Polynomial.X + Polynomial.C 20

@[simp] theorem uhcInternalFoldGrowPolynomial_eval (N : Nat) :
    uhcInternalFoldGrowPolynomial.eval N = 20 * N + 20 := by
  simp [uhcInternalFoldGrowPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]

theorem uhcInternalFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod edgeListStructuredEncodedType EncodedType.nat)
      edgeListStructuredEncodedType
      uhcInternalFoldStep := by
  let X := EncodedType.prod edgeListStructuredEncodedType EncodedType.nat
  have hOut : TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst edgeListStructuredEncodedType EncodedType.nat
  have hVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd edgeListStructuredEncodedType EncodedType.nat
  have hBlock :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier => internalEdgesForVertex p.2) := by
    have hComp := TMPolyTimeMap.comp internalEdgesForVertex_tm_polytime hVertex
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier => (p.1, internalEdgesForVertex p.2)) :=
    TMPolyTimeMap.prod_mk hOut hBlock
  have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append edgeStructuredEncodedType)
    hAppendInput
  exact hComp

theorem uhcInternalFoldStep_growth
    (source : List Nat) (acc : edgeListStructuredEncodedType.Carrier) (v : Nat)
    (_hAcc : True)
    (hv : EncodedType.nat.inputSize v ≤
        (EncodedType.list EncodedType.nat).inputSize source) :
    True ∧
      edgeListStructuredEncodedType.inputSize (uhcInternalFoldStep (acc, v)) ≤
        edgeListStructuredEncodedType.inputSize acc +
          uhcInternalFoldGrowPolynomial.eval
            ((EncodedType.list EncodedType.nat).inputSize source) := by
  let N := (EncodedType.list EncodedType.nat).inputSize source
  have hBlock : edgeListStructuredEncodedType.inputSize (internalEdgesForVertex v) ≤
      20 * N + 20 := by
    simpa [N] using internalEdgesForVertex_inputSize_le v hv
  constructor
  · trivial
  · change
      edgeListStructuredEncodedType.inputSize
          ((show List (Nat × Nat) from acc) ++ internalEdgesForVertex v) ≤
        edgeListStructuredEncodedType.inputSize acc +
          uhcInternalFoldGrowPolynomial.eval
            ((EncodedType.list EncodedType.nat).inputSize source)
    rw [edgeListStructured_inputSize_append, uhcInternalFoldGrowPolynomial_eval]
    change
      edgeListStructuredEncodedType.inputSize acc +
          edgeListStructuredEncodedType.inputSize (internalEdgesForVertex v) ≤
        edgeListStructuredEncodedType.inputSize acc + (20 * N + 20)
    omega

theorem uhcInternalFold_tm_polytime :
    TMPolyTimeMap
      (EncodedType.list EncodedType.nat)
      edgeListStructuredEncodedType
      (fun xs : List Nat =>
        xs.foldl (fun out v => uhcInternalFoldStep (out, v)) ([] : List (Nat × Nat))) := by
  rcases uhcInternalFoldStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      EncodedType.nat edgeListStructuredEncodedType
      uhcInternalFoldStep ([] : List (Nat × Nat)) hStep
      (Polynomial.C 0) uhcInternalFoldGrowPolynomial
      (fun _ _ => True) ?_ ?_
  · intro xs
    constructor
    · trivial
    · have hNil :
        edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
          change
            (EncodedType.list edgeStructuredEncodedType).inputSize
                ([] : List (Nat × Nat)) = 0
          exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
      simpa using (le_of_eq hNil)
  · intro source acc v hAcc hv
    exact uhcInternalFoldStep_growth source acc v hAcc hv

theorem uhcInternalEdgesExecutableFromVertices_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      edgeListStructuredEncodedType
      uhcInternalEdgesExecutableFromVertices := by
  have hComp := TMPolyTimeMap.comp uhcInternalFold_tm_polytime natRange_tm_polytime
  simpa [Function.comp, uhcInternalEdgesExecutableFromVertices] using hComp

/-! ### Cross edges and final graph assembly -/

theorem textbookVertexCount_tm_polytime :
    TMPolyTimeMap
      directedHamiltonianCircuitStructuredEncodedType
      EncodedType.nat
      textbookVertexCount := by
  have hGraph :
      TMPolyTimeMap
        directedHamiltonianCircuitStructuredEncodedType
        graphStructuredEncodedType
        (fun I : DirectedHamiltonianCircuitInput => I.graph) :=
    directedHamiltonianCircuitGraphTMBackedMap.tm_polytime
  have hVertices :
      TMPolyTimeMap
        directedHamiltonianCircuitStructuredEncodedType
        EncodedType.nat
        (fun I : DirectedHamiltonianCircuitInput => I.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp graphVerticesTMBackedMap.tm_polytime hGraph
    simpa [Function.comp] using hComp
  have hTriple :
      TMPolyTimeMap
        directedHamiltonianCircuitStructuredEncodedType
        EncodedType.nat
        (fun I : DirectedHamiltonianCircuitInput => uhcNatTriple I.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp uhcNatTriple_tm_polytime hVertices
    simpa [Function.comp] using hComp
  convert hTriple using 1
  funext I
  simp [textbookVertexCount, uhcNatTriple, natDouble]
  omega

theorem uhcInternalEdgesExecutable_tm_polytime :
    TMPolyTimeMap
      directedHamiltonianCircuitStructuredEncodedType
      edgeListStructuredEncodedType
      uhcInternalEdgesExecutable := by
  have hGraph :
      TMPolyTimeMap
        directedHamiltonianCircuitStructuredEncodedType
        graphStructuredEncodedType
        (fun I : DirectedHamiltonianCircuitInput => I.graph) :=
    directedHamiltonianCircuitGraphTMBackedMap.tm_polytime
  have hVertices :
      TMPolyTimeMap
        directedHamiltonianCircuitStructuredEncodedType
        EncodedType.nat
        (fun I : DirectedHamiltonianCircuitInput => I.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp graphVerticesTMBackedMap.tm_polytime hGraph
    simpa [Function.comp] using hComp
  have hComp := TMPolyTimeMap.comp uhcInternalEdgesExecutableFromVertices_tm_polytime hVertices
  simpa [Function.comp, uhcInternalEdgesExecutable] using hComp

theorem crossEdgeOfDirectedEdge_tm_polytime :
    TMPolyTimeMap
      edgeStructuredEncodedType
      edgeStructuredEncodedType
      crossEdgeOfDirectedEdge := by
  let X := edgeStructuredEncodedType
  have hLeft : TMPolyTimeMap X EncodedType.nat (fun e : X.Carrier => e.1) := by
    simpa [X, edgeStructuredEncodedType] using TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hRight : TMPolyTimeMap X EncodedType.nat (fun e : X.Carrier => e.2) := by
    simpa [X, edgeStructuredEncodedType] using TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hOutLeft :
      TMPolyTimeMap X EncodedType.nat (fun e : X.Carrier => outVertex e.1) := by
    have hComp := TMPolyTimeMap.comp outVertex_tm_polytime hLeft
    simpa [Function.comp, X] using hComp
  have hInRight :
      TMPolyTimeMap X EncodedType.nat (fun e : X.Carrier => inVertex e.2) := by
    have hComp := TMPolyTimeMap.comp inVertex_tm_polytime hRight
    simpa [Function.comp, X] using hComp
  have hPair := TMPolyTimeMap.prod_mk hOutLeft hInRight
  simpa [crossEdgeOfDirectedEdge, edgeStructuredEncodedType, X] using hPair

def uhcCrossEdgesExecutable (I : DirectedHamiltonianCircuitInput) : List (Nat × Nat) :=
  I.graph.edges.map crossEdgeOfDirectedEdge

theorem uhcCrossEdgesExecutable_eq_textbookCrossEdges
    (I : DirectedHamiltonianCircuitInput) :
    uhcCrossEdgesExecutable I = textbookCrossEdges I := by
  rfl

theorem uhcCrossEdgesExecutable_tm_polytime :
    TMPolyTimeMap
      directedHamiltonianCircuitStructuredEncodedType
      edgeListStructuredEncodedType
      uhcCrossEdgesExecutable := by
  let X := directedHamiltonianCircuitStructuredEncodedType
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType
        (fun I : DirectedHamiltonianCircuitInput => I.graph) :=
    directedHamiltonianCircuitGraphTMBackedMap.tm_polytime
  have hPayload :
      TMPolyTimeMap X graphPayloadStructuredEncodedType
        (fun I : DirectedHamiltonianCircuitInput => graphPayloadOfGraph I.graph) := by
    have hComp := TMPolyTimeMap.comp graphPayloadTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun I : DirectedHamiltonianCircuitInput => I.graph.edges) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, graphPayloadOfGraph, graphPayloadStructuredEncodedType, X]
      using hComp
  have hMap := TMPolyTimeMap.list_map crossEdgeOfDirectedEdge_tm_polytime
  have hComp := TMPolyTimeMap.comp hMap hEdges
  simpa [Function.comp, uhcCrossEdgesExecutable, edgeListStructuredEncodedType, X] using hComp

def uhcEdgeListExecutable (I : DirectedHamiltonianCircuitInput) : List (Nat × Nat) :=
  uhcInternalEdgesExecutable I ++ uhcCrossEdgesExecutable I

theorem uhcEdgeListExecutable_eq_textbookEdgeList
    (I : DirectedHamiltonianCircuitInput) :
    uhcEdgeListExecutable I = textbookEdgeList I := by
  simp [uhcEdgeListExecutable, textbookEdgeList,
    uhcInternalEdgesExecutable_eq_textbookInternalEdges,
    uhcCrossEdgesExecutable_eq_textbookCrossEdges]

theorem uhcEdgeListExecutable_tm_polytime :
    TMPolyTimeMap
      directedHamiltonianCircuitStructuredEncodedType
      edgeListStructuredEncodedType
      uhcEdgeListExecutable := by
  let X := directedHamiltonianCircuitStructuredEncodedType
  have hInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun I : DirectedHamiltonianCircuitInput =>
          (uhcInternalEdgesExecutable I, uhcCrossEdgesExecutable I)) :=
    TMPolyTimeMap.prod_mk uhcInternalEdgesExecutable_tm_polytime
      uhcCrossEdgesExecutable_tm_polytime
  have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append edgeStructuredEncodedType) hInput
  simpa [Function.comp, uhcEdgeListExecutable, edgeListStructuredEncodedType, X] using hComp

def uhcExecutableGraphFromInput (I : DirectedHamiltonianCircuitInput) : GraphInput where
  vertices := textbookVertexCount I
  edges := uhcEdgeListExecutable I
  directed := false

theorem uhcExecutableGraphFromInput_tm_polytime :
    TMPolyTimeMap
      directedHamiltonianCircuitStructuredEncodedType
      graphStructuredEncodedType
      uhcExecutableGraphFromInput := by
  let X := directedHamiltonianCircuitStructuredEncodedType
  have hDirected : TMPolyTimeMap X EncodedType.bool
      (fun _ : DirectedHamiltonianCircuitInput => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hPayload :
      TMPolyTimeMap X graphPayloadStructuredEncodedType
        (fun I : DirectedHamiltonianCircuitInput => (uhcEdgeListExecutable I, false)) :=
    TMPolyTimeMap.prod_mk uhcEdgeListExecutable_tm_polytime hDirected
  have hTuple :
      TMPolyTimeMap X graphTupleStructuredEncodedType
        (fun I : DirectedHamiltonianCircuitInput =>
          (textbookVertexCount I, (uhcEdgeListExecutable I, false))) :=
    TMPolyTimeMap.prod_mk textbookVertexCount_tm_polytime hPayload
  have hComp := TMPolyTimeMap.comp Clique.graphTupleToGraphTMBackedMap.tm_polytime hTuple
  simpa [Function.comp, Clique.graphTupleToGraph, uhcExecutableGraphFromInput, X] using hComp

theorem uhcExecutableGraphFromInput_eq_textbookGraph
    (I : DirectedHamiltonianCircuitInput) :
    uhcExecutableGraphFromInput I = (textbookMap I).graph := by
  simp [uhcExecutableGraphFromInput, textbookMap, uhcEdgeListExecutable_eq_textbookEdgeList]

def uhcExecutableInputFromDirectedHamiltonianCircuit
    (I : DirectedHamiltonianCircuitInput) : UndirectedHamiltonianCircuitInput :=
  undirectedHamiltonianCircuitGraphToInput (uhcExecutableGraphFromInput I)

theorem uhcExecutableInputFromDirectedHamiltonianCircuit_tm_polytime :
    TMPolyTimeMap
      directedHamiltonianCircuitStructuredEncodedType
      undirectedHamiltonianCircuitStructuredEncodedType
      uhcExecutableInputFromDirectedHamiltonianCircuit := by
  have hComp := TMPolyTimeMap.comp
    undirectedHamiltonianCircuitGraphToInputTMBackedMap.tm_polytime
    uhcExecutableGraphFromInput_tm_polytime
  simpa [Function.comp, undirectedHamiltonianCircuitGraphToInput,
    uhcExecutableInputFromDirectedHamiltonianCircuit] using hComp

theorem uhcExecutableInputFromDirectedHamiltonianCircuit_eq_textbookMap
    (I : DirectedHamiltonianCircuitInput) :
    uhcExecutableInputFromDirectedHamiltonianCircuit I = textbookMap I := by
  simp [uhcExecutableInputFromDirectedHamiltonianCircuit,
    undirectedHamiltonianCircuitGraphToInput, uhcExecutableGraphFromInput_eq_textbookGraph]

/-! ### Guarded public map -/

def directedToUndirectedHamiltonianCircuitStructuredTMMap
    (I : DirectedHamiltonianCircuitInput) : UndirectedHamiltonianCircuitInput :=
  if I.graph.directed then
    uhcExecutableInputFromDirectedHamiltonianCircuit I
  else
    noInput

abbrev uhcGuardedExecutableMap :
    DirectedHamiltonianCircuitInput → UndirectedHamiltonianCircuitInput :=
  directedToUndirectedHamiltonianCircuitStructuredTMMap

theorem directedToUndirectedHamiltonianCircuitStructuredTMMap_eq_guardedTextbookMap
    (I : DirectedHamiltonianCircuitInput) :
    directedToUndirectedHamiltonianCircuitStructuredTMMap I = guardedTextbookMap I := by
  classical
  by_cases hDirected : I.graph.directed = true
  · simp [directedToUndirectedHamiltonianCircuitStructuredTMMap, hDirected,
      guardedTextbookMap, uhcExecutableInputFromDirectedHamiltonianCircuit_eq_textbookMap]
  · have hFalse : I.graph.directed = false := by
      cases h : I.graph.directed
      · rfl
      · exact False.elim (hDirected h)
    simp [directedToUndirectedHamiltonianCircuitStructuredTMMap, hDirected,
      guardedTextbookMap]

theorem uhcGuardedExecutableMap_eq_guardedTextbookMap
    (I : DirectedHamiltonianCircuitInput) :
    uhcGuardedExecutableMap I = guardedTextbookMap I :=
  directedToUndirectedHamiltonianCircuitStructuredTMMap_eq_guardedTextbookMap I

theorem directedHamiltonianCircuitDirectedFlag_tm_polytime :
    TMPolyTimeMap
      directedHamiltonianCircuitStructuredEncodedType
      EncodedType.bool
      (fun I : DirectedHamiltonianCircuitInput => I.graph.directed) := by
  let X := directedHamiltonianCircuitStructuredEncodedType
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType
        (fun I : DirectedHamiltonianCircuitInput => I.graph) :=
    directedHamiltonianCircuitGraphTMBackedMap.tm_polytime
  have hPayload :
      TMPolyTimeMap X graphPayloadStructuredEncodedType
        (fun I : DirectedHamiltonianCircuitInput => graphPayloadOfGraph I.graph) := by
    have hComp := TMPolyTimeMap.comp graphPayloadTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hSnd := TMPolyTimeMap.snd edgeListStructuredEncodedType EncodedType.bool
  have hComp := TMPolyTimeMap.comp hSnd hPayload
  simpa [Function.comp, graphPayloadOfGraph, graphPayloadStructuredEncodedType, X] using hComp

theorem directedToUndirectedHamiltonianCircuitStructured_tm_polytime :
    TMPolyTimeMap
      directedHamiltonianCircuitStructuredEncodedType
      undirectedHamiltonianCircuitStructuredEncodedType
      directedToUndirectedHamiltonianCircuitStructuredTMMap := by
  let X := directedHamiltonianCircuitStructuredEncodedType
  have hNo :
      TMPolyTimeMap X undirectedHamiltonianCircuitStructuredEncodedType
        (fun _ : DirectedHamiltonianCircuitInput => noInput) :=
    TMPolyTimeMap.const X undirectedHamiltonianCircuitStructuredEncodedType noInput
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun I : DirectedHamiltonianCircuitInput => (I.graph.directed, I)) :=
    TMPolyTimeMap.prod_mk directedHamiltonianCircuitDirectedFlag_tm_polytime
      (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool X)
        undirectedHamiltonianCircuitStructuredEncodedType
        (fun p : Bool × DirectedHamiltonianCircuitInput =>
          match p.1 with
          | true => uhcExecutableInputFromDirectedHamiltonianCircuit p.2
          | false => noInput) :=
    graphBoolProduct_dispatch_tm_polytime X undirectedHamiltonianCircuitStructuredEncodedType
      (fFalse := fun _ : DirectedHamiltonianCircuitInput => noInput)
      (fTrue := fun I : DirectedHamiltonianCircuitInput =>
        uhcExecutableInputFromDirectedHamiltonianCircuit I)
      hNo uhcExecutableInputFromDirectedHamiltonianCircuit_tm_polytime
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext I
  cases h : I.graph.directed <;>
    simp [Function.comp, directedToUndirectedHamiltonianCircuitStructuredTMMap, h]

/-! ### Public P16c surface -/

theorem directedToUndirectedHamiltonianCircuitStructuredTMMap_inputSize_le_directed_poly
    (I : DirectedHamiltonianCircuitInput) :
    undirectedHamiltonianCircuitStructuredEncodedType.inputSize
        (directedToUndirectedHamiltonianCircuitStructuredTMMap I) ≤
      1000 * (directedHamiltonianCircuitStructuredEncodedType.inputSize I) ^ 2 + 1000 := by
  rw [directedToUndirectedHamiltonianCircuitStructuredTMMap_eq_guardedTextbookMap]
  exact undirectedHamiltonianCircuitStructured_inputSize_guardedTextbookMap_le_directed_poly I

theorem directedToUndirectedHamiltonianCircuitStructuredTMMap_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : DirectedHamiltonianCircuitInput =>
        directedHamiltonianCircuitStructuredEncodedType.inputSize I)
      (fun J : UndirectedHamiltonianCircuitInput =>
        undirectedHamiltonianCircuitStructuredEncodedType.inputSize J)
      directedToUndirectedHamiltonianCircuitStructuredTMMap := by
  refine PolynomialSizeBound.intro_with 2 1000 1000 ?_
  intro I
  exact directedToUndirectedHamiltonianCircuitStructuredTMMap_inputSize_le_directed_poly I

noncomputable def directedToUndirectedHamiltonianCircuitStructuredTMBackedMap :
    TMBackedCostedMap
      directedHamiltonianCircuitStructuredEncodedType
      undirectedHamiltonianCircuitStructuredEncodedType
      directedToUndirectedHamiltonianCircuitStructuredTMMap where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      directedToUndirectedHamiltonianCircuitStructuredTMMap_polynomialSizeBound
  tm_polytime := directedToUndirectedHamiltonianCircuitStructured_tm_polytime

theorem directedToUndirectedHamiltonianCircuitStructuredTMMap_correct
    (I : DirectedHamiltonianCircuitInput) :
    directedHamiltonianCircuitStructuredDecisionProblem.isYes I ↔
      undirectedHamiltonianCircuitStructuredDecisionProblem.isYes
        (directedToUndirectedHamiltonianCircuitStructuredTMMap I) := by
  rw [directedToUndirectedHamiltonianCircuitStructuredTMMap_eq_guardedTextbookMap]
  simpa [directedHamiltonianCircuitStructuredDecisionProblem,
    undirectedHamiltonianCircuitStructuredDecisionProblem] using guardedTextbookMap_correct I

noncomputable def directedToUndirectedHamiltonianCircuitStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      directedHamiltonianCircuitStructuredDecisionProblem
      undirectedHamiltonianCircuitStructuredDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    directedToUndirectedHamiltonianCircuitStructuredTMBackedMap
    (by
      intro I
      exact directedToUndirectedHamiltonianCircuitStructuredTMMap_correct I)

/--
Public P16c structured finite-alphabet Directed-Hamiltonian-Circuit-to-
Undirected-Hamiltonian-Circuit reduction, projected from the direct TM-backed
witness.
-/
noncomputable def directedToUndirectedHamiltonianCircuitStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      directedHamiltonianCircuitStructuredDecisionProblem
      undirectedHamiltonianCircuitStructuredDecisionProblem :=
  directedToUndirectedHamiltonianCircuitStructuredTMBackedKarpReduction.toCostedKarpReduction

noncomputable def directedToUndirectedHamiltonianCircuitStructuredTMKarpReduction :
    TMKarpReduction
      directedHamiltonianCircuitStructuredDecisionProblem
      undirectedHamiltonianCircuitStructuredDecisionProblem :=
  directedToUndirectedHamiltonianCircuitStructuredTMBackedKarpReduction.toTMKarpReduction

end UndirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
