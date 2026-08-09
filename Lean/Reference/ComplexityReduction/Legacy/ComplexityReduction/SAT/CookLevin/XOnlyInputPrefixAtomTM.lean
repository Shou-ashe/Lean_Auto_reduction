import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.SymbolList
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyIOTM

/-!
Direct standard-TM witnesses for the x-only input-prefix atom layer.

This file only contains the reusable indexed-symbol and instruction generators.
The full x-prefix literal fold is kept as the next execution slice so
`XOnlyInputPrefixTM` stays below the 1000-line file budget.
-/

namespace ComplexityReduction
namespace SAT

noncomputable abbrev tmVerifierInputSymbolEncodedType {L : EncodedDecisionProblem}
    (V : TMVerifier L) : EncodedType :=
  @finiteSymbolEncodedType
    ((tmVerifierTM V).Γ (tmVerifierTM V).k₀) (tmVerifierTM V).Γk₀Fin

noncomputable def tmVerifierInputPrefixLiteralInstructionEncodedType {L : EncodedDecisionProblem}
    (V : TMVerifier L) : EncodedType :=
  EncodedType.sum EncodedType.nat (tmVerifierInputSymbolEncodedType V)

noncomputable def tmVerifierInputPrefixLiteralInitInstruction {L : EncodedDecisionProblem}
    (V : TMVerifier L)
    (xs : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀)) :
    (tmVerifierInputPrefixLiteralInstructionEncodedType V).Carrier :=
  Sum.inl ((EncodedType.list (tmVerifierInputSymbolEncodedType V)).inputSize xs)

noncomputable def tmVerifierInputPrefixLiteralSymbolInstruction {L : EncodedDecisionProblem}
    (V : TMVerifier L)
    (s : (tmVerifierTM V).Γ (tmVerifierTM V).k₀) :
    (tmVerifierInputPrefixLiteralInstructionEncodedType V).Carrier :=
  Sum.inr s

noncomputable def tmVerifierInputPrefixLiteralInstructions {L : EncodedDecisionProblem}
    (V : TMVerifier L)
    (xs : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀)) :
    List (tmVerifierInputPrefixLiteralInstructionEncodedType V).Carrier :=
  [tmVerifierInputPrefixLiteralInitInstruction V xs] ++
    xs.map (tmVerifierInputPrefixLiteralSymbolInstruction V)

theorem tmVerifierTableauVar_cellPayload_tm_polytime
    (kind : TMVerifierTableauVarKind) (time stack : Nat) :
    TMPolyTimeMap (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.nat
      (fun p : Nat × Nat => tmVerifierTableauVar kind time stack p.1 p.2) := by
  let X := EncodedType.prod EncodedType.nat EncodedType.nat
  have hCell : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hPayload : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hCellPayload :
      TMPolyTimeMap X EncodedType.nat
        (fun p : Nat × Nat => Nat.pair p.1 p.2) := by
    have hPair : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × Nat => (p.1, p.2)) :=
      TMPolyTimeMap.prod_mk hCell hPayload
    have hComp := TMPolyTimeMap.comp natPair_tm_polytime hPair
    simpa [Function.comp, X] using hComp
  have hStackPayload :
      TMPolyTimeMap X EncodedType.nat
        (fun p : Nat × Nat => Nat.pair stack (Nat.pair p.1 p.2)) := by
    have hComp := TMPolyTimeMap.comp (nat_pair_const_left_tm_polytime stack) hCellPayload
    simpa [Function.comp, X] using hComp
  have hTimePayload :
      TMPolyTimeMap X EncodedType.nat
        (fun p : Nat × Nat => Nat.pair time (Nat.pair stack (Nat.pair p.1 p.2))) := by
    have hComp := TMPolyTimeMap.comp (nat_pair_const_left_tm_polytime time) hStackPayload
    simpa [Function.comp, X] using hComp
  have hKind :
      TMPolyTimeMap X EncodedType.nat
        (fun p : Nat × Nat =>
          Nat.pair kind.tag (Nat.pair time (Nat.pair stack (Nat.pair p.1 p.2)))) := by
    have hComp := TMPolyTimeMap.comp (nat_pair_const_left_tm_polytime kind.tag) hTimePayload
    simpa [Function.comp, X] using hComp
  simpa [tmVerifierTableauVar, X] using hKind

theorem tmVerifierStackSymbolAtom_cellPayload_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap (EncodedType.prod EncodedType.nat EncodedType.nat)
      literalStructuredEncodedType
      (fun p : Nat × Nat => tmVerifierStackSymbolAtom V t k p.1 p.2) := by
  have hVar :=
    tmVerifierTableauVar_cellPayload_tm_polytime
      TMVerifierTableauVarKind.stackSymbol t (tmVerifierStackCode V k)
  have hComp := TMPolyTimeMap.comp literalPositiveTMBackedMap.tm_polytime hVar
  simpa [Function.comp, tmVerifierStackSymbolAtom, tmVerifierTableauAtom, Literal.positive]
    using hComp

theorem tmVerifierInputStackSymbolAtom_indexed_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat (tmVerifierInputSymbolEncodedType V))
      literalStructuredEncodedType
      (fun p : Nat × (tmVerifierTM V).Γ (tmVerifierTM V).k₀ =>
        tmVerifierInputStackSymbolAtom V 0 p.1 p.2) := by
  let X := EncodedType.prod EncodedType.nat (tmVerifierInputSymbolEncodedType V)
  have hCell : TMPolyTimeMap X EncodedType.nat
      (fun p : Nat × (tmVerifierTM V).Γ (tmVerifierTM V).k₀ => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst EncodedType.nat (tmVerifierInputSymbolEncodedType V)
  have hSymbol : TMPolyTimeMap X (tmVerifierInputSymbolEncodedType V)
      (fun p : Nat × (tmVerifierTM V).Γ (tmVerifierTM V).k₀ => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd EncodedType.nat (tmVerifierInputSymbolEncodedType V)
  have hPayloadSymbol :
      TMPolyTimeMap (tmVerifierInputSymbolEncodedType V) EncodedType.nat
        (fun s : (tmVerifierTM V).Γ (tmVerifierTM V).k₀ =>
          tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₀ s) := by
    simpa [tmVerifierInputSymbolEncodedType] using
      (@finiteSymbol_map_tm_polytime
        ((tmVerifierTM V).Γ (tmVerifierTM V).k₀) (tmVerifierTM V).Γk₀Fin
        EncodedType.nat
        (fun s : (tmVerifierTM V).Γ (tmVerifierTM V).k₀ =>
          tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₀ s))
  have hPayload : TMPolyTimeMap X EncodedType.nat
      (fun p : Nat × (tmVerifierTM V).Γ (tmVerifierTM V).k₀ =>
        tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₀ p.2) := by
    have hComp := TMPolyTimeMap.comp hPayloadSymbol hSymbol
    simpa [Function.comp, X] using hComp
  have hCellPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × (tmVerifierTM V).Γ (tmVerifierTM V).k₀ =>
          (p.1, tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₀ p.2)) :=
    TMPolyTimeMap.prod_mk hCell hPayload
  have hAtom := tmVerifierStackSymbolAtom_cellPayload_tm_polytime V 0 (tmVerifierTM V).k₀
  have hComp := TMPolyTimeMap.comp hAtom hCellPayload
  simpa [Function.comp, tmVerifierInputStackSymbolAtom, X] using hComp

theorem tmVerifierInputPrefixLiteralInitInstruction_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap
      (EncodedType.list (tmVerifierInputSymbolEncodedType V))
      (tmVerifierInputPrefixLiteralInstructionEncodedType V)
      (tmVerifierInputPrefixLiteralInitInstruction V) := by
  have hSize :
      TMPolyTimeMap (EncodedType.list (tmVerifierInputSymbolEncodedType V)) EncodedType.nat
        (fun xs : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀) =>
          (EncodedType.list (tmVerifierInputSymbolEncodedType V)).inputSize xs) :=
    (encodedInputSizeNatTMBackedMap
      (EncodedType.list (tmVerifierInputSymbolEncodedType V))).tm_polytime
  have hInl := TMPolyTimeMap.inl EncodedType.nat (tmVerifierInputSymbolEncodedType V)
  have hComp := TMPolyTimeMap.comp hInl hSize
  simpa [Function.comp, tmVerifierInputPrefixLiteralInitInstruction,
    tmVerifierInputPrefixLiteralInstructionEncodedType] using hComp

theorem tmVerifierInputPrefixLiteralSymbolInstruction_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap
      (tmVerifierInputSymbolEncodedType V)
      (tmVerifierInputPrefixLiteralInstructionEncodedType V)
      (tmVerifierInputPrefixLiteralSymbolInstruction V) := by
  simpa [tmVerifierInputPrefixLiteralSymbolInstruction,
    tmVerifierInputPrefixLiteralInstructionEncodedType] using
    TMPolyTimeMap.inr EncodedType.nat (tmVerifierInputSymbolEncodedType V)

theorem tmVerifierInputPrefixLiteralInstructions_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap
      (EncodedType.list (tmVerifierInputSymbolEncodedType V))
      (EncodedType.list (tmVerifierInputPrefixLiteralInstructionEncodedType V))
      (tmVerifierInputPrefixLiteralInstructions V) := by
  have hInit :
      TMPolyTimeMap (EncodedType.list (tmVerifierInputSymbolEncodedType V))
        (tmVerifierInputPrefixLiteralInstructionEncodedType V)
        (fun xs : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀) =>
          tmVerifierInputPrefixLiteralInitInstruction V xs) :=
    tmVerifierInputPrefixLiteralInitInstruction_tm_polytime V
  have hInitSingleton :
      TMPolyTimeMap (EncodedType.list (tmVerifierInputSymbolEncodedType V))
        (EncodedType.list (tmVerifierInputPrefixLiteralInstructionEncodedType V))
        (fun xs : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀) =>
          [tmVerifierInputPrefixLiteralInitInstruction V xs]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton (tmVerifierInputPrefixLiteralInstructionEncodedType V)) hInit
    simpa [Function.comp] using hComp
  have hMapped :
      TMPolyTimeMap (EncodedType.list (tmVerifierInputSymbolEncodedType V))
        (EncodedType.list (tmVerifierInputPrefixLiteralInstructionEncodedType V))
        (fun xs : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀) =>
          xs.map (tmVerifierInputPrefixLiteralSymbolInstruction V)) := by
    exact TMPolyTimeMap.list_map
      (tmVerifierInputPrefixLiteralSymbolInstruction_tm_polytime V)
  have hPair :
      TMPolyTimeMap (EncodedType.list (tmVerifierInputSymbolEncodedType V))
        (EncodedType.prod
          (EncodedType.list (tmVerifierInputPrefixLiteralInstructionEncodedType V))
          (EncodedType.list (tmVerifierInputPrefixLiteralInstructionEncodedType V)))
        (fun xs : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀) =>
          ([tmVerifierInputPrefixLiteralInitInstruction V xs],
            xs.map (tmVerifierInputPrefixLiteralSymbolInstruction V))) :=
    TMPolyTimeMap.prod_mk hInitSingleton hMapped
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append (tmVerifierInputPrefixLiteralInstructionEncodedType V)) hPair
  simpa [Function.comp, tmVerifierInputPrefixLiteralInstructions] using hAppend

end SAT
end ComplexityReduction
