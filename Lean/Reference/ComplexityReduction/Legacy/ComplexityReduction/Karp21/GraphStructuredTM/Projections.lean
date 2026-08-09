import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.PairCandidates

/-!
TM-backed projections for faithful structured graph encodings.

These projections only extract fields already present in the finite-alphabet
source encodings; they do not enumerate complement edges.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics.Graph

def graphPayloadOfGraph (g : GraphInput) : graphPayloadStructuredEncodedType.Carrier :=
  (g.edges, g.directed)

theorem graphVertices_encode_filterMap (g : GraphInput) :
    EncodedType.nat.encode g.vertices =
      (graphStructuredEncodedType.encode g).filterMap
        (@EncodedType.prodLeftSymbol
          EncodedType.nat.Symbol graphPayloadStructuredEncodedType.Symbol) := by
  simpa [graphStructuredEncodedType] using
    (EncodedType.prod_left_filter_encode
      EncodedType.nat graphPayloadStructuredEncodedType
      (g.vertices, (g.edges, g.directed))).symm

theorem graphPayload_encode_filterMap (g : GraphInput) :
    graphPayloadStructuredEncodedType.encode (graphPayloadOfGraph g) =
      (graphStructuredEncodedType.encode g).filterMap
        (@EncodedType.prodRightSymbol
          EncodedType.nat.Symbol graphPayloadStructuredEncodedType.Symbol) := by
  simpa [graphPayloadOfGraph, graphStructuredEncodedType] using
    (EncodedType.prod_right_filter_encode
      EncodedType.nat graphPayloadStructuredEncodedType
      (g.vertices, (g.edges, g.directed))).symm

noncomputable def graphVerticesTMBackedMap :
    TMBackedCostedMap graphStructuredEncodedType EncodedType.nat GraphInput.vertices :=
  TMBackedCostedMap.symbolFilterMap
    graphStructuredEncodedType EncodedType.nat GraphInput.vertices
    (@EncodedType.prodLeftSymbol
      EncodedType.nat.Symbol graphPayloadStructuredEncodedType.Symbol)
    graphVertices_encode_filterMap

noncomputable def graphPayloadTMBackedMap :
    TMBackedCostedMap
      graphStructuredEncodedType
      graphPayloadStructuredEncodedType
      graphPayloadOfGraph :=
  TMBackedCostedMap.symbolFilterMap
    graphStructuredEncodedType graphPayloadStructuredEncodedType graphPayloadOfGraph
    (@EncodedType.prodRightSymbol
      EncodedType.nat.Symbol graphPayloadStructuredEncodedType.Symbol)
    graphPayload_encode_filterMap

theorem cliqueGraph_encode_filterMap (I : CliqueInput) :
    graphStructuredEncodedType.encode I.graph =
      (cliqueStructuredEncodedType.encode I).filterMap
        (@EncodedType.prodLeftSymbol
          graphStructuredEncodedType.Symbol EncodedType.nat.Symbol) := by
  simpa [cliqueStructuredEncodedType] using
    (EncodedType.prod_left_filter_encode
      graphStructuredEncodedType EncodedType.nat (I.graph, I.k)).symm

theorem cliqueBudget_encode_filterMap (I : CliqueInput) :
    EncodedType.nat.encode I.k =
      (cliqueStructuredEncodedType.encode I).filterMap
        (@EncodedType.prodRightSymbol
          graphStructuredEncodedType.Symbol EncodedType.nat.Symbol) := by
  simpa [cliqueStructuredEncodedType] using
    (EncodedType.prod_right_filter_encode
      graphStructuredEncodedType EncodedType.nat (I.graph, I.k)).symm

noncomputable def cliqueGraphTMBackedMap :
    TMBackedCostedMap cliqueStructuredEncodedType graphStructuredEncodedType
      (fun I : CliqueInput => I.graph) :=
  TMBackedCostedMap.symbolFilterMap
    cliqueStructuredEncodedType graphStructuredEncodedType
    (fun I : CliqueInput => I.graph)
    (@EncodedType.prodLeftSymbol
      graphStructuredEncodedType.Symbol EncodedType.nat.Symbol)
    cliqueGraph_encode_filterMap

noncomputable def cliqueBudgetTMBackedMap :
    TMBackedCostedMap cliqueStructuredEncodedType EncodedType.nat
      (fun I : CliqueInput => I.k) :=
  TMBackedCostedMap.symbolFilterMap
    cliqueStructuredEncodedType EncodedType.nat
    (fun I : CliqueInput => I.k)
    (@EncodedType.prodRightSymbol
      graphStructuredEncodedType.Symbol EncodedType.nat.Symbol)
    cliqueBudget_encode_filterMap

theorem vertexCoverGraph_encode_filterMap (I : VertexCoverInput) :
    graphStructuredEncodedType.encode I.graph =
      (vertexCoverStructuredEncodedType.encode I).filterMap
        (@EncodedType.prodLeftSymbol
          graphStructuredEncodedType.Symbol EncodedType.nat.Symbol) := by
  simpa [vertexCoverStructuredEncodedType] using
    (EncodedType.prod_left_filter_encode
      graphStructuredEncodedType EncodedType.nat (I.graph, I.k)).symm

theorem vertexCoverBudget_encode_filterMap (I : VertexCoverInput) :
    EncodedType.nat.encode I.k =
      (vertexCoverStructuredEncodedType.encode I).filterMap
        (@EncodedType.prodRightSymbol
          graphStructuredEncodedType.Symbol EncodedType.nat.Symbol) := by
  simpa [vertexCoverStructuredEncodedType] using
    (EncodedType.prod_right_filter_encode
      graphStructuredEncodedType EncodedType.nat (I.graph, I.k)).symm

noncomputable def vertexCoverGraphTMBackedMap :
    TMBackedCostedMap vertexCoverStructuredEncodedType graphStructuredEncodedType
      (fun I : VertexCoverInput => I.graph) :=
  TMBackedCostedMap.symbolFilterMap
    vertexCoverStructuredEncodedType graphStructuredEncodedType
    (fun I : VertexCoverInput => I.graph)
    (@EncodedType.prodLeftSymbol
      graphStructuredEncodedType.Symbol EncodedType.nat.Symbol)
    vertexCoverGraph_encode_filterMap

noncomputable def vertexCoverBudgetTMBackedMap :
    TMBackedCostedMap vertexCoverStructuredEncodedType EncodedType.nat
      (fun I : VertexCoverInput => I.k) :=
  TMBackedCostedMap.symbolFilterMap
    vertexCoverStructuredEncodedType EncodedType.nat
    (fun I : VertexCoverInput => I.k)
    (@EncodedType.prodRightSymbol
      graphStructuredEncodedType.Symbol EncodedType.nat.Symbol)
    vertexCoverBudget_encode_filterMap

theorem chromaticNumberGraph_encode_filterMap (I : ChromaticNumberInput) :
    graphStructuredEncodedType.encode I.graph =
      (chromaticNumberStructuredEncodedType.encode I).filterMap
        (@EncodedType.prodLeftSymbol
          graphStructuredEncodedType.Symbol EncodedType.nat.Symbol) := by
  simpa [chromaticNumberStructuredEncodedType] using
    (EncodedType.prod_left_filter_encode
      graphStructuredEncodedType EncodedType.nat (I.graph, I.colors)).symm

theorem chromaticNumberColors_encode_filterMap (I : ChromaticNumberInput) :
    EncodedType.nat.encode I.colors =
      (chromaticNumberStructuredEncodedType.encode I).filterMap
        (@EncodedType.prodRightSymbol
          graphStructuredEncodedType.Symbol EncodedType.nat.Symbol) := by
  simpa [chromaticNumberStructuredEncodedType] using
    (EncodedType.prod_right_filter_encode
      graphStructuredEncodedType EncodedType.nat (I.graph, I.colors)).symm

noncomputable def chromaticNumberGraphTMBackedMap :
    TMBackedCostedMap chromaticNumberStructuredEncodedType graphStructuredEncodedType
      (fun I : ChromaticNumberInput => I.graph) :=
  TMBackedCostedMap.symbolFilterMap
    chromaticNumberStructuredEncodedType graphStructuredEncodedType
    (fun I : ChromaticNumberInput => I.graph)
    (@EncodedType.prodLeftSymbol
      graphStructuredEncodedType.Symbol EncodedType.nat.Symbol)
    chromaticNumberGraph_encode_filterMap

noncomputable def chromaticNumberColorsTMBackedMap :
    TMBackedCostedMap chromaticNumberStructuredEncodedType EncodedType.nat
      (fun I : ChromaticNumberInput => I.colors) :=
  TMBackedCostedMap.symbolFilterMap
    chromaticNumberStructuredEncodedType EncodedType.nat
    (fun I : ChromaticNumberInput => I.colors)
    (@EncodedType.prodRightSymbol
      graphStructuredEncodedType.Symbol EncodedType.nat.Symbol)
    chromaticNumberColors_encode_filterMap

end Karp21
end ComplexityReduction
