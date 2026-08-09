import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover.Part3
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.NatPairTM

namespace ComplexityReduction
namespace Karp21
namespace ExactCover

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
Executable edge/color marker codes for the compact
Chromatic-Number-to-Exact-Cover route.

The semantic proof in `Part3` uses `List.idxOf` into `colorEdgeColorPairs`.
For the direct TM witness we use the closed form `vertices + i * colors + c`
and prove it agrees with the `idxOf` code on the bounded coordinates emitted by
the gadget.
-/

theorem product_getElem?_mul_add {α β : Type} (xs : List α) (ys : List β)
    (i j : Nat) (hi : i < xs.length) (hj : j < ys.length) :
    (xs ×ˢ ys)[i * ys.length + j]? = some (xs[i], ys[j]) := by
  induction xs generalizing i with
  | nil =>
      simp at hi
  | cons x xs ih =>
      cases i with
      | zero =>
          simp [List.product_cons, List.getElem?_append, hj]
      | succ i =>
          have hiTail : i < xs.length := Nat.lt_of_succ_lt_succ hi
          have hnot : ¬ ((i + 1) * ys.length + j < ys.length) := by
            have hpos : 0 < ys.length := by omega
            nlinarith
          have hsub : (i + 1) * ys.length + j - ys.length = i * ys.length + j := by
            rw [Nat.succ_mul]
            omega
          simp [List.product_cons, List.getElem?_append, hnot, hsub, ih i hiTail]

theorem range_product_idxOf_eq_mul_add (E C i c : Nat)
    (hi : i < E) (hc : c < C) :
    (List.range E ×ˢ List.range C).idxOf (i, c) = i * C + c := by
  have hGet? :=
    product_getElem?_mul_add (List.range E) (List.range C) i c
      (by simpa using hi) (by simpa using hc)
  simp at hGet?
  rcases (List.getElem?_eq_some_iff.mp hGet?) with ⟨hidx, hget⟩
  have hNodup : (List.range E ×ˢ List.range C).Nodup :=
    (List.nodup_range (n := E)).product (List.nodup_range (n := C))
  have hIdx := hNodup.idxOf_getElem (i * C + c) hidx
  simpa [hget] using hIdx

def colorEdgeCodeFast (I : ChromaticNumberInput) (i c : Nat) : Nat :=
  I.graph.vertices + i * I.colors + c

theorem colorEdgeCodeFast_eq_colorEdgeCode {I : ChromaticNumberInput} {i c : Nat}
    (hi : i < I.graph.edges.length) (hc : c < I.colors) :
    colorEdgeCodeFast I i c = colorEdgeCode I i c := by
  simp [colorEdgeCodeFast, colorEdgeCode, colorEdgeColorPairs,
    range_product_idxOf_eq_mul_add _ _ _ _ hi hc, Nat.add_assoc]

def colorEdgeCodeFastInputEncodedType : EncodedType :=
  EncodedType.prod chromaticNumberStructuredEncodedType
    (EncodedType.prod EncodedType.nat EncodedType.nat)

theorem colorEdgeCodeFast_tm_polytime :
    TMPolyTimeMap
      colorEdgeCodeFastInputEncodedType
      EncodedType.nat
      (fun p : ChromaticNumberInput × (Nat × Nat) =>
        colorEdgeCodeFast p.1 p.2.1 p.2.2) := by
  let X := colorEdgeCodeFastInputEncodedType
  have hSource :
      TMPolyTimeMap X chromaticNumberStructuredEncodedType
        (fun p : ChromaticNumberInput × (Nat × Nat) => p.1) := by
    simpa [X, colorEdgeCodeFastInputEncodedType] using
      TMPolyTimeMap.fst chromaticNumberStructuredEncodedType
        (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : ChromaticNumberInput × (Nat × Nat) => p.2) := by
    simpa [X, colorEdgeCodeFastInputEncodedType] using
      TMPolyTimeMap.snd chromaticNumberStructuredEncodedType
        (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hIndex :
      TMPolyTimeMap X EncodedType.nat
        (fun p : ChromaticNumberInput × (Nat × Nat) => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hColor :
      TMPolyTimeMap X EncodedType.nat
        (fun p : ChromaticNumberInput × (Nat × Nat) => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, X] using hComp
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType
        (fun p : ChromaticNumberInput × (Nat × Nat) => p.1.graph) := by
    have hComp := TMPolyTimeMap.comp chromaticNumberGraphTMBackedMap.tm_polytime hSource
    simpa [Function.comp, X] using hComp
  have hVertices :
      TMPolyTimeMap X EncodedType.nat
        (fun p : ChromaticNumberInput × (Nat × Nat) => p.1.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp graphVerticesTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hColors :
      TMPolyTimeMap X EncodedType.nat
        (fun p : ChromaticNumberInput × (Nat × Nat) => p.1.colors) := by
    have hComp := TMPolyTimeMap.comp chromaticNumberColorsTMBackedMap.tm_polytime hSource
    simpa [Function.comp, X] using hComp
  have hMulInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : ChromaticNumberInput × (Nat × Nat) => (p.2.1, p.1.colors)) :=
    TMPolyTimeMap.prod_mk hIndex hColors
  have hMul :
      TMPolyTimeMap X EncodedType.nat
        (fun p : ChromaticNumberInput × (Nat × Nat) => p.2.1 * p.1.colors) := by
    have hComp := TMPolyTimeMap.comp GenericNatTM.natMul_tm_polytime hMulInput
    simpa [Function.comp, X] using hComp
  have hFirstAddInput :
      TMPolyTimeMap X natAddInputEncodedType
        (fun p : ChromaticNumberInput × (Nat × Nat) =>
          (p.1.graph.vertices, p.2.1 * p.1.colors)) := by
    simpa [natAddInputEncodedType] using TMPolyTimeMap.prod_mk hVertices hMul
  have hFirstAdd :
      TMPolyTimeMap X EncodedType.nat
        (fun p : ChromaticNumberInput × (Nat × Nat) =>
          p.1.graph.vertices + p.2.1 * p.1.colors) := by
    have hComp := TMPolyTimeMap.comp natAdd_tm_polytime hFirstAddInput
    simpa [Function.comp, natAddInputEncodedType, X] using hComp
  have hSecondAddInput :
      TMPolyTimeMap X natAddInputEncodedType
        (fun p : ChromaticNumberInput × (Nat × Nat) =>
          (p.1.graph.vertices + p.2.1 * p.1.colors, p.2.2)) := by
    simpa [natAddInputEncodedType] using TMPolyTimeMap.prod_mk hFirstAdd hColor
  have hOut := TMPolyTimeMap.comp natAdd_tm_polytime hSecondAddInput
  simpa [Function.comp, natAddInputEncodedType, colorEdgeCodeFast, X] using hOut

end ExactCover
end Karp21
end ComplexityReduction
