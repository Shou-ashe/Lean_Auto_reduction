import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.UnaryToBinary
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.MaxCut

/-!
Direct unary-to-binary encoding bridge for faithful structured Max Cut.

The semantic instance is unchanged; only the threshold field changes from the
ordinary unary `Nat` encoding to `binaryNat`.
-/

namespace ComplexityReduction
namespace Karp21
namespace MaxCut

open ComplexityReduction.Combinatorics.Graph

def maxCutGraphForUnaryToBinary (I : MaxCutInput) : GraphInput :=
  I.graph

def maxCutThresholdForUnaryToBinary (I : MaxCutInput) : Nat :=
  I.threshold

theorem maxCutGraphForUnaryToBinary_encode_filterMap (I : MaxCutInput) :
    graphStructuredEncodedType.encode (maxCutGraphForUnaryToBinary I) =
      (maxCutStructuredEncodedType.encode I).filterMap
        (@EncodedType.prodLeftSymbol
          graphStructuredEncodedType.Symbol EncodedType.nat.Symbol) := by
  simpa [maxCutGraphForUnaryToBinary, maxCutStructuredEncodedType] using
    (EncodedType.prod_left_filter_encode
      graphStructuredEncodedType EncodedType.nat (I.graph, I.threshold)).symm

theorem maxCutThresholdForUnaryToBinary_encode_filterMap (I : MaxCutInput) :
    EncodedType.nat.encode (maxCutThresholdForUnaryToBinary I) =
      (maxCutStructuredEncodedType.encode I).filterMap
        (@EncodedType.prodRightSymbol
          graphStructuredEncodedType.Symbol EncodedType.nat.Symbol) := by
  simpa [maxCutThresholdForUnaryToBinary, maxCutStructuredEncodedType] using
    (EncodedType.prod_right_filter_encode
      graphStructuredEncodedType EncodedType.nat (I.graph, I.threshold)).symm

noncomputable def maxCutGraphForUnaryToBinaryTMBackedMap :
    TMBackedCostedMap
      maxCutStructuredEncodedType
      graphStructuredEncodedType
      maxCutGraphForUnaryToBinary :=
  TMBackedCostedMap.symbolFilterMap
    maxCutStructuredEncodedType
    graphStructuredEncodedType
    maxCutGraphForUnaryToBinary
    (@EncodedType.prodLeftSymbol
      graphStructuredEncodedType.Symbol EncodedType.nat.Symbol)
    maxCutGraphForUnaryToBinary_encode_filterMap

noncomputable def maxCutThresholdForUnaryToBinaryTMBackedMap :
    TMBackedCostedMap
      maxCutStructuredEncodedType
      EncodedType.nat
      maxCutThresholdForUnaryToBinary :=
  TMBackedCostedMap.symbolFilterMap
    maxCutStructuredEncodedType
    EncodedType.nat
    maxCutThresholdForUnaryToBinary
    (@EncodedType.prodRightSymbol
      graphStructuredEncodedType.Symbol EncodedType.nat.Symbol)
    maxCutThresholdForUnaryToBinary_encode_filterMap

def maxCutInputFromBinaryTuple (p : GraphInput × Nat) : MaxCutInput where
  graph := p.1
  threshold := p.2

theorem maxCutInputFromBinaryTuple_encode (p : GraphInput × Nat) :
    maxCutBinaryStructuredEncodedType.encode (maxCutInputFromBinaryTuple p) =
      maxCutTupleBinaryStructuredEncodedType.encode p := by
  rfl

noncomputable def maxCutInputFromBinaryTupleTMBackedMap :
    TMBackedCostedMap
      maxCutTupleBinaryStructuredEncodedType
      maxCutBinaryStructuredEncodedType
      maxCutInputFromBinaryTuple :=
  TMBackedCostedMap.ofEncodingEquiv
    maxCutTupleBinaryStructuredEncodedType
    maxCutBinaryStructuredEncodedType
    maxCutInputFromBinaryTuple
    (Equiv.refl maxCutTupleBinaryStructuredEncodedType.Symbol)
    (by
      intro p
      change
        maxCutBinaryStructuredEncodedType.encode (maxCutInputFromBinaryTuple p) =
          (maxCutTupleBinaryStructuredEncodedType.encode p).map id
      simp [maxCutInputFromBinaryTuple_encode])

theorem maxCutStructuredToBinary_tm_polytime :
    TMPolyTimeMap
      maxCutStructuredEncodedType
      maxCutBinaryStructuredEncodedType
      id := by
  let X := maxCutStructuredEncodedType
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType
        (fun I : MaxCutInput => I.graph) := by
    simpa [X, maxCutGraphForUnaryToBinary] using
      maxCutGraphForUnaryToBinaryTMBackedMap.tm_polytime
  have hThresholdUnary :
      TMPolyTimeMap X EncodedType.nat
        (fun I : MaxCutInput => I.threshold) := by
    simpa [X, maxCutThresholdForUnaryToBinary] using
      maxCutThresholdForUnaryToBinaryTMBackedMap.tm_polytime
  have hThresholdBinary :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun I : MaxCutInput => I.threshold) := by
    have hComp := TMPolyTimeMap.comp
      Knapsack.unaryNatToBinaryNat_tm_polytime hThresholdUnary
    simpa [Function.comp, X] using hComp
  have hTuple :
      TMPolyTimeMap X maxCutTupleBinaryStructuredEncodedType
        (fun I : MaxCutInput => (I.graph, I.threshold)) :=
    TMPolyTimeMap.prod_mk hGraph hThresholdBinary
  have hOut := TMPolyTimeMap.comp maxCutInputFromBinaryTupleTMBackedMap.tm_polytime hTuple
  simpa [Function.comp, maxCutInputFromBinaryTuple, X] using hOut

noncomputable def maxCutStructuredToBinaryStructuredTMKarpReduction :
    TMKarpReduction
      maxCutStructuredDecisionProblem
      maxCutBinaryStructuredDecisionProblem where
  f := id
  polytime := maxCutStructuredToBinary_tm_polytime
  correct := by
    intro I
    rfl

end MaxCut
end Karp21
end ComplexityReduction
