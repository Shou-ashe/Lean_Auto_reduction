/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.Part1

/-!
Generic reuse of a direct-TM machine when its computed payload is presented by
another output encoding.  The caller must prove the exact relationship between
the two encodings; this theorem does not create a computation or a reduction.
-/

namespace ComplexityReduction
namespace TMPolyTimeMap

/--
Reuse one direct-TM computation through an exact output-alphabet equivalence.
The input function, output function, and encoding equality are inferred from
the direct-TM proof and the caller's equality proof.
-/
theorem transport_output {X Y Z : EncodedType}
    {sourceOutput : X.Carrier → Y.Carrier}
    {targetOutput : X.Carrier → Z.Carrier}
    (hSource : TMPolyTimeMap X Y sourceOutput)
    (symbolEquiv : Y.Symbol ≃ Z.Symbol)
    (encodeEq : ∀ input,
      Z.encode (targetOutput input) =
        (Y.encode (sourceOutput input)).map symbolEquiv) :
    TMPolyTimeMap X Z targetOutput := by
  rcases hSource with ⟨machine⟩
  refine ⟨
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet.trans symbolEquiv
      time := machine.time
      outputsFun := by
        intro input
        simpa [encodeEq input, List.map_map, Function.comp_def] using
          machine.outputsFun input }⟩

assert_standard_axioms transport_output

end TMPolyTimeMap
end ComplexityReduction
