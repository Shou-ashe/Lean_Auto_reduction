import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipMaxCut
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipKnapsackBinary
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.UnaryToBinary

/-!
Direct standard-TM NP membership witness for faithful binary-structured Max Cut.

This reuses the structured Max-Cut edge-count runner.  The only binary-specific
part is the threshold comparison: the unary edge count is converted to
`binaryNat` before comparing against the binary-encoded threshold.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics.Graph

namespace MaxCut

/-! ### Binary Max-Cut projections -/

theorem maxCutBinaryGraph_encode_filterMap (I : MaxCutInput) :
    graphStructuredEncodedType.encode I.graph =
      (maxCutBinaryStructuredEncodedType.encode I).filterMap
        (@EncodedType.prodLeftSymbol
          graphStructuredEncodedType.Symbol EncodedType.binaryNat.Symbol) := by
  simpa [maxCutBinaryStructuredEncodedType] using
    (EncodedType.prod_left_filter_encode
      graphStructuredEncodedType EncodedType.binaryNat (I.graph, I.threshold)).symm

theorem maxCutBinaryThreshold_encode_filterMap (I : MaxCutInput) :
    EncodedType.binaryNat.encode I.threshold =
      (maxCutBinaryStructuredEncodedType.encode I).filterMap
        (@EncodedType.prodRightSymbol
          graphStructuredEncodedType.Symbol EncodedType.binaryNat.Symbol) := by
  simpa [maxCutBinaryStructuredEncodedType] using
    (EncodedType.prod_right_filter_encode
      graphStructuredEncodedType EncodedType.binaryNat (I.graph, I.threshold)).symm

noncomputable def maxCutBinaryGraphTMBackedMap :
    TMBackedCostedMap maxCutBinaryStructuredEncodedType graphStructuredEncodedType
      (fun I : MaxCutInput => I.graph) :=
  TMBackedCostedMap.symbolFilterMap
    maxCutBinaryStructuredEncodedType graphStructuredEncodedType
    (fun I : MaxCutInput => I.graph)
    (@EncodedType.prodLeftSymbol
      graphStructuredEncodedType.Symbol EncodedType.binaryNat.Symbol)
    maxCutBinaryGraph_encode_filterMap

noncomputable def maxCutBinaryThresholdTMBackedMap :
    TMBackedCostedMap maxCutBinaryStructuredEncodedType EncodedType.binaryNat
      (fun I : MaxCutInput => I.threshold) :=
  TMBackedCostedMap.symbolFilterMap
    maxCutBinaryStructuredEncodedType EncodedType.binaryNat
    (fun I : MaxCutInput => I.threshold)
    (@EncodedType.prodRightSymbol
      graphStructuredEncodedType.Symbol EncodedType.binaryNat.Symbol)
    maxCutBinaryThreshold_encode_filterMap

theorem maxCutBinaryStructured_inputSize_eq (I : MaxCutInput) :
    maxCutBinaryStructuredEncodedType.inputSize I =
      graphStructuredEncodedType.inputSize I.graph +
        EncodedType.binaryNat.inputSize I.threshold + 1 := by
  change maxCutTupleBinaryStructuredEncodedType.inputSize (I.graph, I.threshold) =
    graphStructuredEncodedType.inputSize I.graph +
      EncodedType.binaryNat.inputSize I.threshold + 1
  simp [maxCutTupleBinaryStructuredEncodedType]
  omega

theorem edgeList_inputSize_lt_maxCutBinaryStructured_inputSize (I : MaxCutInput) :
    edgeListStructuredEncodedType.inputSize I.graph.edges <
      maxCutBinaryStructuredEncodedType.inputSize I := by
  rw [maxCutBinaryStructured_inputSize_eq, graphStructured_inputSize_eq]
  omega

theorem edge_mem_left_lt_maxCutBinaryStructured_inputSize
    (I : MaxCutInput) {e : Nat × Nat} (he : e ∈ I.graph.edges) :
    e.1 < maxCutBinaryStructuredEncodedType.inputSize I :=
  lt_trans (edge_mem_left_lt_edgeList_inputSize he)
    (edgeList_inputSize_lt_maxCutBinaryStructured_inputSize I)

theorem edge_mem_right_lt_maxCutBinaryStructured_inputSize
    (I : MaxCutInput) {e : Nat × Nat} (he : e ∈ I.graph.edges) :
    e.2 < maxCutBinaryStructuredEncodedType.inputSize I :=
  lt_trans (edge_mem_right_lt_edgeList_inputSize he)
    (edgeList_inputSize_lt_maxCutBinaryStructured_inputSize I)

theorem cutSize_assignmentPrefix_maxCutBinaryInputSize_eq
    (I : MaxCutInput) (side : Nat → Bool) :
    CutSize I.graph
        (SAT.finiteAssignment
          (SAT.assignmentPrefix (maxCutBinaryStructuredEncodedType.inputSize I) side)) =
      CutSize I.graph side := by
  change
    cutCount I.graph.edges
        (SAT.finiteAssignment
          (SAT.assignmentPrefix (maxCutBinaryStructuredEncodedType.inputSize I) side)) =
      cutCount I.graph.edges side
  apply cutCount_congr_on_edges
  intro e he
  exact
    ⟨SAT.finiteAssignment_assignmentPrefix_of_lt
        (a := side) (edge_mem_left_lt_maxCutBinaryStructured_inputSize I he),
      SAT.finiteAssignment_assignmentPrefix_of_lt
        (a := side) (edge_mem_right_lt_maxCutBinaryStructured_inputSize I he)⟩

/-! ### Binary finite verifier -/

def maxCutBinaryStructuredFiniteVerify
    (I : MaxCutInput) (bits : MaxCutCertificate) : Bool :=
  Knapsack.binaryNatLeBool (I.threshold, maxCutCutCount (bits, I.graph.edges))

theorem maxCutBinaryStructuredFiniteVerify_eq_true_iff
    (I : MaxCutInput) (bits : MaxCutCertificate) :
    maxCutBinaryStructuredFiniteVerify I bits = true ↔
      I.threshold ≤ CutSize I.graph (SAT.finiteAssignment bits) := by
  rw [maxCutBinaryStructuredFiniteVerify, Knapsack.binaryNatLeBool_eq_true_iff,
    maxCutCutCount_eq_cutCount]
  have hSide := maxCutSideFromCertificate_eq_finiteAssignment bits
  change I.threshold ≤ cutCount I.graph.edges (maxCutSideFromCertificate bits) ↔
    I.threshold ≤ CutSize I.graph (SAT.finiteAssignment bits)
  rw [hSide]
  rfl

theorem maxCutBinaryStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod maxCutBinaryStructuredEncodedType maxCutCertificateEncodedType)
      EncodedType.bool
      (fun p : MaxCutInput × MaxCutCertificate =>
        maxCutBinaryStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod maxCutBinaryStructuredEncodedType maxCutCertificateEncodedType
  have hInstance :
      TMPolyTimeMap X maxCutBinaryStructuredEncodedType
        (fun p : MaxCutInput × MaxCutCertificate => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst maxCutBinaryStructuredEncodedType maxCutCertificateEncodedType
  have hBits :
      TMPolyTimeMap X maxCutCertificateEncodedType
        (fun p : MaxCutInput × MaxCutCertificate => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd maxCutBinaryStructuredEncodedType maxCutCertificateEncodedType
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType
        (fun p : MaxCutInput × MaxCutCertificate => p.1.graph) := by
    have hComp := TMPolyTimeMap.comp maxCutBinaryGraphTMBackedMap.tm_polytime hInstance
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
      TMPolyTimeMap X EncodedType.binaryNat
        (fun p : MaxCutInput × MaxCutCertificate => p.1.threshold) := by
    have hComp := TMPolyTimeMap.comp maxCutBinaryThresholdTMBackedMap.tm_polytime hInstance
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
  have hCountBinary :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun p : MaxCutInput × MaxCutCertificate =>
          maxCutCutCount (p.2, p.1.graph.edges)) := by
    have hComp := TMPolyTimeMap.comp Knapsack.unaryNatToBinaryNat_tm_polytime hCount
    simpa [Function.comp, X] using hComp
  have hLeInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : MaxCutInput × MaxCutCertificate =>
          (p.1.threshold, maxCutCutCount (p.2, p.1.graph.edges))) :=
    TMPolyTimeMap.prod_mk hThreshold hCountBinary
  have hOut := TMPolyTimeMap.comp Knapsack.binaryNatLeBool_tm_polytime hLeInput
  simpa [Function.comp, maxCutBinaryStructuredFiniteVerify, X] using hOut

theorem maxCutBinaryCertificate_inputSize_le_linear
    (I : MaxCutInput) (side : Nat → Bool) :
    maxCutCertificateEncodedType.inputSize
        (SAT.assignmentPrefix (maxCutBinaryStructuredEncodedType.inputSize I) side) ≤
      2 * maxCutBinaryStructuredEncodedType.inputSize I := by
  rw [SAT.assignmentPrefix_inputSize]

end MaxCut

/-- Direct finite-certificate TM verifier for faithful binary-structured Max Cut. -/
noncomputable def maxCutBinaryStructuredFiniteTMVerifier :
    TMVerifier maxCutBinaryStructuredDecisionProblem where
  Cert := MaxCut.maxCutCertificateEncodedType
  verify := MaxCut.maxCutBinaryStructuredFiniteVerify
  verifier_polytime := MaxCut.maxCutBinaryStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨1, 2, 0, ?_⟩
    intro I hYes
    rcases hYes with ⟨side, hCut⟩
    let bits :=
      SAT.assignmentPrefix (maxCutBinaryStructuredEncodedType.inputSize I) side
    refine ⟨bits, ?_, ?_⟩
    · simpa [bits] using MaxCut.maxCutBinaryCertificate_inputSize_le_linear I side
    · exact (MaxCut.maxCutBinaryStructuredFiniteVerify_eq_true_iff I bits).2
        (by
          simpa [bits, MaxCut.cutSize_assignmentPrefix_maxCutBinaryInputSize_eq I side]
            using hCut)
  sound := by
    intro I bits hVerify
    exact ⟨SAT.finiteAssignment bits,
      (MaxCut.maxCutBinaryStructuredFiniteVerify_eq_true_iff I bits).1 hVerify⟩

theorem maxCutBinaryStructured_TMInNP :
    TMInNP maxCutBinaryStructuredDecisionProblem :=
  TMInNP.intro maxCutBinaryStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
