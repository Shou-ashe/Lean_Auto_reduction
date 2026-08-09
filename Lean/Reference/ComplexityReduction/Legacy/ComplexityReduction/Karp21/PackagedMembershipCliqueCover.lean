/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipChromaticNumber
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.CliqueCover
import Mathlib.Tactic

/-!
Direct standard-TM NP membership witness for faithful structured Clique Cover.

The verifier uses the standard semantic equivalence between a clique cover of a
graph and a coloring of its undirected complement.  This keeps the certificate a
finite coloring table and reuses the direct standard-TM Chromatic Number
verifier instead of introducing a separate list-of-blocks machine.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics.Graph

namespace CliqueCover

noncomputable def complementChromaticInput (I : CliqueCoverInput) : ChromaticNumberInput where
  graph := complementGraph I.graph
  colors := I.k

theorem cliqueCoverGraph_encode_filterMap (I : CliqueCoverInput) :
    graphStructuredEncodedType.encode I.graph =
      (cliqueCoverStructuredEncodedType.encode I).filterMap
        (@EncodedType.prodLeftSymbol
          graphStructuredEncodedType.Symbol EncodedType.nat.Symbol) := by
  simpa [cliqueCoverStructuredEncodedType] using
    (EncodedType.prod_left_filter_encode
      graphStructuredEncodedType EncodedType.nat (I.graph, I.k)).symm

theorem cliqueCoverBudget_encode_filterMap (I : CliqueCoverInput) :
    EncodedType.nat.encode I.k =
      (cliqueCoverStructuredEncodedType.encode I).filterMap
        (@EncodedType.prodRightSymbol
          graphStructuredEncodedType.Symbol EncodedType.nat.Symbol) := by
  simpa [cliqueCoverStructuredEncodedType] using
    (EncodedType.prod_right_filter_encode
      graphStructuredEncodedType EncodedType.nat (I.graph, I.k)).symm

noncomputable def cliqueCoverGraphTMBackedMap :
    TMBackedCostedMap cliqueCoverStructuredEncodedType graphStructuredEncodedType
      (fun I : CliqueCoverInput => I.graph) :=
  TMBackedCostedMap.symbolFilterMap
    cliqueCoverStructuredEncodedType graphStructuredEncodedType
    (fun I : CliqueCoverInput => I.graph)
    (@EncodedType.prodLeftSymbol
      graphStructuredEncodedType.Symbol EncodedType.nat.Symbol)
    cliqueCoverGraph_encode_filterMap

noncomputable def cliqueCoverBudgetTMBackedMap :
    TMBackedCostedMap cliqueCoverStructuredEncodedType EncodedType.nat
      (fun I : CliqueCoverInput => I.k) :=
  TMBackedCostedMap.symbolFilterMap
    cliqueCoverStructuredEncodedType EncodedType.nat
    (fun I : CliqueCoverInput => I.k)
    (@EncodedType.prodRightSymbol
      graphStructuredEncodedType.Symbol EncodedType.nat.Symbol)
    cliqueCoverBudget_encode_filterMap

theorem complementChromaticInput_tm_polytime :
    TMPolyTimeMap
      cliqueCoverStructuredEncodedType
      chromaticNumberStructuredEncodedType
      complementChromaticInput := by
  let X := cliqueCoverStructuredEncodedType
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType
        (fun I : CliqueCoverInput => I.graph) := by
    simpa [X] using cliqueCoverGraphTMBackedMap.tm_polytime
  have hVertices :
      TMPolyTimeMap X EncodedType.nat
        (fun I : CliqueCoverInput => I.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp graphVerticesTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hPayload :
      TMPolyTimeMap X graphPayloadStructuredEncodedType
        (fun I : CliqueCoverInput => graphPayloadOfGraph I.graph) := by
    have hComp := TMPolyTimeMap.comp graphPayloadTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hSourceEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun I : CliqueCoverInput => I.graph.edges) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, graphPayloadOfGraph, graphPayloadStructuredEncodedType, X] using hComp
  have hCandidates :
      TMPolyTimeMap X vertexPairListEncodedType
        (fun I : CliqueCoverInput => strictNatPairCandidates I.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp strictNatPairCandidatesTMBackedMap.tm_polytime hVertices
    simpa [Function.comp, X] using hComp
  have hComplementInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType vertexPairListEncodedType)
        (fun I : CliqueCoverInput =>
          (I.graph.edges, strictNatPairCandidates I.graph.vertices)) :=
    TMPolyTimeMap.prod_mk hSourceEdges hCandidates
  have hComplementEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun I : CliqueCoverInput => complementEdges I.graph) := by
    have hComp := TMPolyTimeMap.comp complementEdgesFromCandidates_tm_polytime hComplementInput
    simpa [Function.comp, complementEdges, structuredComplementEdges, X] using hComp
  have hDirected :
      TMPolyTimeMap X EncodedType.bool (fun _ : CliqueCoverInput => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hGraphPayloadOut :
      TMPolyTimeMap X graphPayloadStructuredEncodedType
        (fun I : CliqueCoverInput => (complementEdges I.graph, false)) :=
    TMPolyTimeMap.prod_mk hComplementEdges hDirected
  have hGraphTuple :
      TMPolyTimeMap X graphTupleStructuredEncodedType
        (fun I : CliqueCoverInput => (I.graph.vertices, (complementEdges I.graph, false))) :=
    TMPolyTimeMap.prod_mk hVertices hGraphPayloadOut
  have hComplementGraph :
      TMPolyTimeMap X graphStructuredEncodedType
        (fun I : CliqueCoverInput => complementGraph I.graph) := by
    have hComp := TMPolyTimeMap.comp Clique.graphTupleToGraphTMBackedMap.tm_polytime hGraphTuple
    simpa [Function.comp, Clique.graphTupleToGraph, complementGraph, X] using hComp
  have hBudget :
      TMPolyTimeMap X EncodedType.nat (fun I : CliqueCoverInput => I.k) := by
    simpa [X] using cliqueCoverBudgetTMBackedMap.tm_polytime
  have hTargetTuple :
      TMPolyTimeMap X chromaticNumberTupleStructuredEncodedType
        (fun I : CliqueCoverInput => (complementGraph I.graph, I.k)) :=
    TMPolyTimeMap.prod_mk hComplementGraph hBudget
  have hOut := TMPolyTimeMap.comp
    ChromaticNumber.chromaticNumberTupleToChromaticNumberInputTMBackedMap.tm_polytime
    hTargetTuple
  simpa [Function.comp, complementChromaticInput,
    ChromaticNumber.chromaticNumberTupleToChromaticNumberInput, X] using hOut

def colorBlockForCover (I : CliqueCoverInput) (colorOf : Nat → Nat) (c : Nat) :
    List Nat :=
  (List.range I.graph.vertices).filter fun v => decide (colorOf v = c)

def colorBlocksForCover (I : CliqueCoverInput) (colorOf : Nat → Nat) :
    List (List Nat) :=
  (List.range I.k).map (colorBlockForCover I colorOf)

theorem colorBlocksForCover_cliqueCoverFamily
    {I : CliqueCoverInput} {colorOf : Nat → Nat}
    (hProper : ProperColoring (complementGraph I.graph) I.k colorOf) :
    CliqueCoverFamily I.graph (colorBlocksForCover I colorOf) := by
  constructor
  · intro v hv
    let c := colorOf v
    have hc : c ∈ List.range I.k := List.mem_range.mpr (hProper.1 v (by simpa using hv))
    refine ⟨colorBlockForCover I colorOf c, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨c, hc, rfl⟩
    · simp [colorBlockForCover, c, hv]
  · intro block hBlock
    rcases List.mem_map.mp hBlock with ⟨c, _hc, rfl⟩
    constructor
    · exact List.Nodup.filter _ (List.nodup_range (n := I.graph.vertices))
    constructor
    · intro v hv
      simp [colorBlockForCover] at hv
      exact hv.1
    · intro u hu v hv huv
      simp [colorBlockForCover] at hu hv
      have hColorEq : colorOf u = colorOf v := by omega
      by_contra hNoEdge
      have hCompEdge :
          HasUndirectedEdge (complementGraph I.graph) u v := by
        exact (hasUndirectedEdge_complementGraph_iff I.graph u v).2
          ⟨hu.1, hv.1, huv, hNoEdge⟩
      rcases hCompEdge with hEdge | hEdge
      · exact hProper.2 (u, v) hEdge hColorEq
      · exact hProper.2 (v, u) hEdge hColorEq.symm

theorem exists_block_index_of_cliqueCoverFamily
    {g : GraphInput} {blocks : List (List Nat)} {v : Nat}
    (hFamily : CliqueCoverFamily g blocks) (hv : v < g.vertices) :
    ∃ i : Fin blocks.length, v ∈ blocks.get i := by
  have hCover : ∃ block ∈ blocks, v ∈ block := hFamily.1 v hv
  exact (List.exists_mem_iff_get (l := blocks) (p := fun block => v ∈ block)).mp hCover

noncomputable def chosenCliqueCoverIndex
    (I : CliqueCoverInput) (blocks : List (List Nat))
    (hFamily : CliqueCoverFamily I.graph blocks) (v : Nat)
    (hv : v < I.graph.vertices) : Fin blocks.length :=
  Classical.choose (exists_block_index_of_cliqueCoverFamily hFamily hv)

theorem chosenCliqueCoverIndex_spec
    (I : CliqueCoverInput) (blocks : List (List Nat))
    (hFamily : CliqueCoverFamily I.graph blocks) (v : Nat)
    (hv : v < I.graph.vertices) :
    v ∈ blocks.get (chosenCliqueCoverIndex I blocks hFamily v hv) :=
  Classical.choose_spec (exists_block_index_of_cliqueCoverFamily hFamily hv)

noncomputable def coverColorForComplement
    (I : CliqueCoverInput) (blocks : List (List Nat))
    (hFamily : CliqueCoverFamily I.graph blocks) (v : Nat) : Nat :=
  if hv : v < I.graph.vertices then
    chosenCliqueCoverIndex I blocks hFamily v hv
  else
    I.k + v

theorem coverColorForComplement_eq_chosen
    (I : CliqueCoverInput) (blocks : List (List Nat))
    (hFamily : CliqueCoverFamily I.graph blocks) {v : Nat}
    (hv : v < I.graph.vertices) :
    coverColorForComplement I blocks hFamily v =
      chosenCliqueCoverIndex I blocks hFamily v hv := by
  simp [coverColorForComplement, hv]

theorem coverColorForComplement_lt_budget
    (I : CliqueCoverInput) (blocks : List (List Nat))
    (hLen : blocks.length ≤ I.k)
    (hFamily : CliqueCoverFamily I.graph blocks) {v : Nat}
    (hv : v < I.graph.vertices) :
    coverColorForComplement I blocks hFamily v < I.k := by
  rw [coverColorForComplement_eq_chosen I blocks hFamily hv]
  have hIdx :
      ((chosenCliqueCoverIndex I blocks hFamily v hv : Fin blocks.length) : Nat) <
        blocks.length :=
    (chosenCliqueCoverIndex I blocks hFamily v hv).isLt
  omega

theorem cliqueCover_to_complement_properColoring
    (I : CliqueCoverInput) (blocks : List (List Nat))
    (hLen : blocks.length ≤ I.k)
    (hFamily : CliqueCoverFamily I.graph blocks) :
    ProperColoring (complementGraph I.graph) I.k
      (coverColorForComplement I blocks hFamily) := by
  constructor
  · intro v hv
    exact coverColorForComplement_lt_budget I blocks hLen hFamily (by simpa using hv)
  · intro e he
    have hComp :=
      (hasUndirectedEdge_complementGraph_iff I.graph e.1 e.2).1 (Or.inl he)
    intro hColorEq
    have hLeft :=
      coverColorForComplement_eq_chosen I blocks hFamily hComp.1
    have hRight :=
      coverColorForComplement_eq_chosen I blocks hFamily hComp.2.1
    let i := chosenCliqueCoverIndex I blocks hFamily e.1 hComp.1
    let j := chosenCliqueCoverIndex I blocks hFamily e.2 hComp.2.1
    have hijNat : (i : Nat) = (j : Nat) := by
      exact hLeft.symm.trans (hColorEq.trans hRight)
    have hij : i = j := Fin.ext hijNat
    have hiMem : e.1 ∈ blocks.get i :=
      chosenCliqueCoverIndex_spec I blocks hFamily e.1 hComp.1
    have hjMem : e.2 ∈ blocks.get i := by
      simpa [i, j, hij] using
        chosenCliqueCoverIndex_spec I blocks hFamily e.2 hComp.2.1
    have hBlockMem : blocks.get i ∈ blocks := List.get_mem blocks i
    have hAdj :=
      (hFamily.2 (blocks.get i) hBlockMem).2.2 e.1 hiMem e.2 hjMem hComp.2.2.1
    exact hComp.2.2.2 hAdj

theorem cliqueCover_iff_complementChromaticInput (I : CliqueCoverInput) :
    CliqueCover I ↔ ChromaticNumber (complementChromaticInput I) := by
  constructor
  · rintro ⟨blocks, hLen, hFamily⟩
    exact ⟨coverColorForComplement I blocks hFamily,
      cliqueCover_to_complement_properColoring I blocks hLen hFamily⟩
  · rintro ⟨colorOf, hProper⟩
    refine ⟨colorBlocksForCover I colorOf, ?_, ?_⟩
    · simp [colorBlocksForCover]
    · exact colorBlocksForCover_cliqueCoverFamily (by simpa [complementChromaticInput] using hProper)

noncomputable def cliqueCoverStructuredFiniteVerify
    (I : CliqueCoverInput) (cert : ChromaticNumber.ChromaticCertificate) : Bool :=
  ChromaticNumber.chromaticNumberStructuredFiniteVerify (complementChromaticInput I) cert

theorem cliqueCoverStructuredFiniteVerify_sound
    (I : CliqueCoverInput) (cert : ChromaticNumber.ChromaticCertificate) :
    cliqueCoverStructuredFiniteVerify I cert = true → CliqueCover I := by
  intro hVerify
  exact (cliqueCover_iff_complementChromaticInput I).2
    (ChromaticNumber.chromaticNumberStructuredFiniteVerify_sound
      (complementChromaticInput I) cert hVerify)

theorem cliqueCoverStructuredFiniteVerify_complete
    (I : CliqueCoverInput) {colorOf : Nat → Nat}
    (hProper : ProperColoring (complementChromaticInput I).graph
      (complementChromaticInput I).colors colorOf) :
    cliqueCoverStructuredFiniteVerify I
      (ChromaticNumber.certificateOfColoring (complementChromaticInput I) colorOf) = true := by
  exact ChromaticNumber.chromaticNumberStructuredFiniteVerify_complete
    (complementChromaticInput I) hProper

theorem cliqueCoverStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod cliqueCoverStructuredEncodedType
        ChromaticNumber.chromaticCertificateEncodedType)
      EncodedType.bool
      (fun p : CliqueCoverInput × ChromaticNumber.ChromaticCertificate =>
        cliqueCoverStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod cliqueCoverStructuredEncodedType
    ChromaticNumber.chromaticCertificateEncodedType
  have hInstance :
      TMPolyTimeMap X cliqueCoverStructuredEncodedType
        (fun p : X.Carrier => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst cliqueCoverStructuredEncodedType
        ChromaticNumber.chromaticCertificateEncodedType
  have hCert :
      TMPolyTimeMap X ChromaticNumber.chromaticCertificateEncodedType
        (fun p : X.Carrier => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd cliqueCoverStructuredEncodedType
        ChromaticNumber.chromaticCertificateEncodedType
  have hMapped :
      TMPolyTimeMap X chromaticNumberStructuredEncodedType
        (fun p : X.Carrier => complementChromaticInput p.1) := by
    have hComp := TMPolyTimeMap.comp complementChromaticInput_tm_polytime hInstance
    simpa [Function.comp, X] using hComp
  have hInput :
      TMPolyTimeMap X
        (EncodedType.prod chromaticNumberStructuredEncodedType
          ChromaticNumber.chromaticCertificateEncodedType)
        (fun p : X.Carrier => (complementChromaticInput p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hMapped hCert
  have hComp := TMPolyTimeMap.comp
    ChromaticNumber.chromaticNumberStructuredFiniteVerify_tm_polytime hInput
  simpa [Function.comp, cliqueCoverStructuredFiniteVerify, X] using hComp

theorem complementChromaticInput_inputSize_le_cliqueCover_poly
    (I : CliqueCoverInput) :
    chromaticNumberStructuredEncodedType.inputSize (complementChromaticInput I) ≤
      1000 * (cliqueCoverStructuredEncodedType.inputSize I) ^ 3 + 1000 := by
  let S := cliqueCoverStructuredEncodedType.inputSize I
  let V := I.graph.vertices
  have hVsucc : V + 1 ≤ S := by
    simp [S, V, cliqueCoverStructured_inputSize_eq, Clique.graphStructured_inputSize_eq]
    omega
  have hV : V ≤ S := by omega
  have hK : I.k ≤ S := by
    simp [S, cliqueCoverStructured_inputSize_eq]
    omega
  have hBase :
      chromaticNumberStructuredEncodedType.inputSize (complementChromaticInput I) ≤
        V + (V * V) * (2 * V + 2) + 4 + I.k + 2 := by
    calc
      chromaticNumberStructuredEncodedType.inputSize (complementChromaticInput I)
          = graphStructuredEncodedType.inputSize (complementGraph I.graph) + I.k + 2 := by
              simp [complementChromaticInput, ChromaticNumber.chromaticNumberStructured_inputSize_eq]
      _ ≤ V + (V * V) * (2 * V + 2) + 4 + I.k + 2 := by
            have hGraph :
                graphStructuredEncodedType.inputSize (complementGraph I.graph) ≤
                  V + (V * V) * (2 * V + 2) + 4 := by
              simpa [V] using complementGraph_structured_inputSize_le I.graph
            omega
  have hVV : V * V ≤ S * S := Nat.mul_le_mul hV hV
  have hTerm : (V * V) * (2 * V + 2) ≤ (S * S) * (2 * S + 2) :=
    Nat.mul_le_mul hVV (by omega)
  have hPolyBase :
      V + (V * V) * (2 * V + 2) + 4 + I.k + 2 ≤
        S + (S * S) * (2 * S + 2) + 4 + S + 2 := by
    omega
  calc
    chromaticNumberStructuredEncodedType.inputSize (complementChromaticInput I)
        ≤ V + (V * V) * (2 * V + 2) + 4 + I.k + 2 := hBase
    _ ≤ S + (S * S) * (2 * S + 2) + 4 + S + 2 := hPolyBase
    _ ≤ 1000 * S ^ 3 + 1000 := by
          cases S with
          | zero =>
              norm_num
          | succ S =>
              ring_nf
              omega

theorem cliqueCoverCertificate_inputSize_le_poly
    (I : CliqueCoverInput) (colorOf : Nat → Nat)
    (hProper : ProperColoring (complementChromaticInput I).graph
      (complementChromaticInput I).colors colorOf) :
    ChromaticNumber.chromaticCertificateEncodedType.inputSize
        (ChromaticNumber.certificateOfColoring (complementChromaticInput I) colorOf) ≤
      160000000000 * (cliqueCoverStructuredEncodedType.inputSize I) ^ 9 + 100 := by
  let C := chromaticNumberStructuredEncodedType.inputSize (complementChromaticInput I)
  let S := cliqueCoverStructuredEncodedType.inputSize I
  have hCert := ChromaticNumber.certificateOfColoring_inputSize_le_poly
    (complementChromaticInput I) colorOf hProper
  have hCBase : C ≤ 1000 * S ^ 3 + 1000 := by
    simpa [C, S] using complementChromaticInput_inputSize_le_cliqueCover_poly I
  have hSpos : 1 ≤ S := by
    simp [S, cliqueCoverStructured_inputSize_eq]
  have hC : C ≤ 2000 * S ^ 3 := by
    calc
      C ≤ 1000 * S ^ 3 + 1000 := hCBase
      _ ≤ 1000 * S ^ 3 + 1000 * S ^ 3 := by
            have hPow : 1 ≤ S ^ 3 := Nat.pow_le_pow_left hSpos 3
            have hThousand : 1000 ≤ 1000 * S ^ 3 := by
              exact Nat.mul_le_mul_left 1000 hPow
            omega
      _ = 2000 * S ^ 3 := by ring
  calc
    ChromaticNumber.chromaticCertificateEncodedType.inputSize
        (ChromaticNumber.certificateOfColoring (complementChromaticInput I) colorOf)
        ≤ 20 * C ^ 3 + 100 := by simpa [C] using hCert
    _ ≤ 20 * (2000 * S ^ 3) ^ 3 + 100 := by
          exact Nat.add_le_add_right
            (Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left hC 3)) 100
    _ = 160000000000 * S ^ 9 + 100 := by ring

end CliqueCover

/-- Direct finite-certificate TM verifier for faithful structured Clique Cover. -/
noncomputable def cliqueCoverStructuredFiniteTMVerifier :
    TMVerifier cliqueCoverStructuredDecisionProblem where
  Cert := ChromaticNumber.chromaticCertificateEncodedType
  verify := CliqueCover.cliqueCoverStructuredFiniteVerify
  verifier_polytime := CliqueCover.cliqueCoverStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨9, 160000000000, 100, ?_⟩
    intro I hYes
    rcases (CliqueCover.cliqueCover_iff_complementChromaticInput I).1 hYes with
      ⟨colorOf, hProper⟩
    refine ⟨
      ChromaticNumber.certificateOfColoring
        (CliqueCover.complementChromaticInput I) colorOf, ?_, ?_⟩
    · exact CliqueCover.cliqueCoverCertificate_inputSize_le_poly I colorOf hProper
    · exact CliqueCover.cliqueCoverStructuredFiniteVerify_complete I hProper
  sound := by
    intro I cert hVerify
    exact CliqueCover.cliqueCoverStructuredFiniteVerify_sound I cert hVerify

theorem cliqueCoverStructured_TMInNP :
    TMInNP cliqueCoverStructuredDecisionProblem :=
  TMInNP.intro cliqueCoverStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
