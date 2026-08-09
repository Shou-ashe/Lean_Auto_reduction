import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyInputPrefixAtomTM

/-!
Direct standard-TM witnesses for the x-only verifier input prefix.

The prefix is the raw encoding stream of the instance, retagged into the
verifier-input product alphabet and followed by the product delimiter.  It is not
a constant list and it is not an `EncodedType.list`; these witnesses therefore
use the raw-symbol stream encoding from `SymbolList`.
-/

namespace ComplexityReduction
namespace SAT

theorem tmVerifierInstanceInputPrefixEncoded_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap L.Instance
      (symbolListEncodedType (tmVerifierInputEncodedType V).Symbol)
      (fun x : L.Instance.Carrier => tmVerifierInstanceInputPrefixEncoded V x) := by
  simpa [tmVerifierInstanceInputPrefixEncoded] using
    encodedSymbols_suffixMap_tm_polytime L.Instance
      (tmVerifierInputEncodedType V).Symbol
      (fun s : L.Instance.Symbol => (some (Sum.inl s) :
        (tmVerifierInputEncodedType V).Symbol))
      (none : (tmVerifierInputEncodedType V).Symbol)

theorem tmVerifierInstanceInputPrefixWord_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap L.Instance
      (@symbolListEncodedType
        ((tmVerifierTM V).Γ (tmVerifierTM V).k₀) (tmVerifierTM V).Γk₀Fin)
      (fun x : L.Instance.Carrier => tmVerifierInstanceInputPrefixWord V x) := by
  letI : Fintype ((tmVerifierTM V).Γ (tmVerifierTM V).k₀) := (tmVerifierTM V).Γk₀Fin
  have hPrefix := tmVerifierInstanceInputPrefixEncoded_tm_polytime V
  have hWord :
      TMPolyTimeMap
        (symbolListEncodedType (tmVerifierInputEncodedType V).Symbol)
        (symbolListEncodedType ((tmVerifierTM V).Γ (tmVerifierTM V).k₀))
        (fun xs : List (tmVerifierInputEncodedType V).Symbol =>
          xs.map (tmVerifierComputableWitness V).inputAlphabet.invFun) :=
    encodedSymbols_map_tm_polytime
      (symbolListEncodedType (tmVerifierInputEncodedType V).Symbol)
      ((tmVerifierTM V).Γ (tmVerifierTM V).k₀)
      (tmVerifierComputableWitness V).inputAlphabet.invFun
  have hComp := TMPolyTimeMap.comp hWord hPrefix
  simpa [Function.comp, tmVerifierInstanceInputPrefixWord] using hComp

end SAT
end ComplexityReduction
