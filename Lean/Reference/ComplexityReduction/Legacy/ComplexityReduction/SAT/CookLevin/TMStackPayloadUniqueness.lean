/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMStackPayloadDecoder

/-!
Concrete active-payload uniqueness lemmas.

This file starts discharging the uniqueness boundary exposed in
`TMStackPayloadDecoder`: input/output payload codes are injective and their
role tags are disjoint from each other and from pushed-symbol payloads.  The
remaining work is to combine these facts with `zipIdx` uniqueness for pushed
symbols and active-list membership inversion.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Input/output payload-code injectivity -/

theorem tmVerifierInputSymbolCode_injective
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    Function.Injective (tmVerifierInputSymbolCode V) := by
  intro s₁ s₂ h
  letI : Fintype (tmVerifierInputEncodedType V).Symbol :=
    (tmVerifierInputEncodedType V).finite_symbol
  have hFin :
      (Fintype.equivFin (tmVerifierInputEncodedType V).Symbol)
          ((tmVerifierComputableWitness V).inputAlphabet s₁) =
        (Fintype.equivFin (tmVerifierInputEncodedType V).Symbol)
          ((tmVerifierComputableWitness V).inputAlphabet s₂) := by
    apply Fin.ext
    simpa [tmVerifierInputSymbolCode] using h
  exact (tmVerifierComputableWitness V).inputAlphabet.injective
    ((Fintype.equivFin (tmVerifierInputEncodedType V).Symbol).injective hFin)

theorem tmVerifierOutputSymbolCode_injective
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    Function.Injective (tmVerifierOutputSymbolCode V) := by
  intro s₁ s₂ h
  letI : Fintype EncodedType.bool.Symbol := EncodedType.bool.finite_symbol
  have hFin :
      (Fintype.equivFin EncodedType.bool.Symbol)
          ((tmVerifierComputableWitness V).outputAlphabet s₁) =
        (Fintype.equivFin EncodedType.bool.Symbol)
          ((tmVerifierComputableWitness V).outputAlphabet s₂) := by
    apply Fin.ext
    simpa [tmVerifierOutputSymbolCode] using h
  exact (tmVerifierComputableWitness V).outputAlphabet.injective
    ((Fintype.equivFin EncodedType.bool.Symbol).injective hFin)

theorem tmVerifierIOSymbol_code_injective
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    Function.Injective (TMVerifierIOSymbol.code (V := V)) := by
  intro a b h
  cases a with
  | input s₁ =>
      cases b with
      | input s₂ =>
          have hCode :
              tmVerifierInputSymbolCode V s₁ = tmVerifierInputSymbolCode V s₂ :=
            (Nat.pair_eq_pair.mp h).2
          have hs := tmVerifierInputSymbolCode_injective V hCode
          cases hs
          rfl
      | output s₂ =>
          have hTag : 0 = 1 := (Nat.pair_eq_pair.mp h).1
          contradiction
  | output s₁ =>
      cases b with
      | input s₂ =>
          have hTag : 1 = 0 := (Nat.pair_eq_pair.mp h).1
          contradiction
      | output s₂ =>
          have hCode :
              tmVerifierOutputSymbolCode V s₁ = tmVerifierOutputSymbolCode V s₂ :=
            (Nat.pair_eq_pair.mp h).2
          have hs := tmVerifierOutputSymbolCode_injective V hCode
          cases hs
          rfl

theorem tmVerifierIOSymbol_code_ne_pushedPayload
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (io : TMVerifierIOSymbol V) (idx : Nat) :
    TMVerifierIOSymbol.code io ≠ Nat.pair 2 idx := by
  intro h
  cases io with
  | input s =>
      have hTag : 0 = 2 := (Nat.pair_eq_pair.mp h).1
      contradiction
  | output s =>
      have hTag : 1 = 2 := (Nat.pair_eq_pair.mp h).1
      contradiction

/-! ### Membership inversion for named-symbol lists -/

theorem tmVerifierInputNamedStackSymbols_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (named : TMVerifierNamedStackSymbol V)
    (h : named ∈ tmVerifierInputNamedStackSymbols V) :
    ∃ s : (tmVerifierTM V).Γ (tmVerifierTM V).k₀,
      named =
        ({ stack := (tmVerifierTM V).k₀
           payload := TMVerifierIOSymbol.code (TMVerifierIOSymbol.input (V := V) s)
           symbol := s } : TMVerifierNamedStackSymbol V) := by
  rw [tmVerifierInputNamedStackSymbols] at h
  rcases List.mem_map.mp h with ⟨s, _hs, rfl⟩
  exact ⟨s, rfl⟩

theorem tmVerifierOutputNamedStackSymbols_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (named : TMVerifierNamedStackSymbol V)
    (h : named ∈ tmVerifierOutputNamedStackSymbols V) :
    ∃ s : (tmVerifierTM V).Γ (tmVerifierTM V).k₁,
      named =
        ({ stack := (tmVerifierTM V).k₁
           payload := TMVerifierIOSymbol.code (TMVerifierIOSymbol.output (V := V) s)
           symbol := s } : TMVerifierNamedStackSymbol V) := by
  rw [tmVerifierOutputNamedStackSymbols] at h
  rcases List.mem_map.mp h with ⟨s, _hs, rfl⟩
  exact ⟨s, rfl⟩

theorem tmVerifierNamedPushedStackSymbols_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (named : TMVerifierNamedStackSymbol V)
    (h : named ∈ tmVerifierNamedPushedStackSymbols V) :
    ∃ raw : TMVerifierStackSymbol V, ∃ idx : Nat,
      (raw, idx) ∈ (tmVerifierControlPushSymbols V).zipIdx ∧
        named =
          ({ stack := raw.stack
             payload := Nat.pair 2 idx
             symbol := raw.symbol } : TMVerifierNamedStackSymbol V) := by
  rw [tmVerifierNamedPushedStackSymbols] at h
  rcases List.mem_map.mp h with ⟨entry, hEntry, rfl⟩
  exact ⟨entry.1, entry.2, hEntry, rfl⟩

/-! ### Payload uniqueness inside each source list -/

theorem tmVerifierInputNamedStackSymbols_payload_unique
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    {n₁ n₂ : TMVerifierNamedStackSymbol V}
    (h₁ : n₁ ∈ tmVerifierInputNamedStackSymbols V)
    (h₂ : n₂ ∈ tmVerifierInputNamedStackSymbols V)
    (hPayload : n₁.payload = n₂.payload) :
    n₁.stack = n₂.stack ∧ HEq n₁.symbol n₂.symbol := by
  rcases tmVerifierInputNamedStackSymbols_mem V n₁ h₁ with ⟨s₁, rfl⟩
  rcases tmVerifierInputNamedStackSymbols_mem V n₂ h₂ with ⟨s₂, rfl⟩
  have hCode :
      tmVerifierInputSymbolCode V s₁ = tmVerifierInputSymbolCode V s₂ :=
    (Nat.pair_eq_pair.mp hPayload).2
  have hs := tmVerifierInputSymbolCode_injective V hCode
  cases hs
  exact ⟨rfl, HEq.rfl⟩

theorem tmVerifierOutputNamedStackSymbols_payload_unique
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    {n₁ n₂ : TMVerifierNamedStackSymbol V}
    (h₁ : n₁ ∈ tmVerifierOutputNamedStackSymbols V)
    (h₂ : n₂ ∈ tmVerifierOutputNamedStackSymbols V)
    (hPayload : n₁.payload = n₂.payload) :
    n₁.stack = n₂.stack ∧ HEq n₁.symbol n₂.symbol := by
  rcases tmVerifierOutputNamedStackSymbols_mem V n₁ h₁ with ⟨s₁, rfl⟩
  rcases tmVerifierOutputNamedStackSymbols_mem V n₂ h₂ with ⟨s₂, rfl⟩
  have hCode :
      tmVerifierOutputSymbolCode V s₁ = tmVerifierOutputSymbolCode V s₂ :=
    (Nat.pair_eq_pair.mp hPayload).2
  have hs := tmVerifierOutputSymbolCode_injective V hCode
  cases hs
  exact ⟨rfl, HEq.rfl⟩

theorem tmVerifierNamedPushedStackSymbols_payload_unique
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    {n₁ n₂ : TMVerifierNamedStackSymbol V}
    (h₁ : n₁ ∈ tmVerifierNamedPushedStackSymbols V)
    (h₂ : n₂ ∈ tmVerifierNamedPushedStackSymbols V)
    (hPayload : n₁.payload = n₂.payload) :
    n₁.stack = n₂.stack ∧ HEq n₁.symbol n₂.symbol := by
  rcases tmVerifierNamedPushedStackSymbols_mem V n₁ h₁ with ⟨raw₁, idx₁, hZip₁, rfl⟩
  rcases tmVerifierNamedPushedStackSymbols_mem V n₂ h₂ with ⟨raw₂, idx₂, hZip₂, rfl⟩
  have hIdx : idx₁ = idx₂ := (Nat.pair_eq_pair.mp hPayload).2
  subst idx₂
  rcases List.mem_zipIdx' hZip₁ with ⟨_hLt₁, hGet₁⟩
  rcases List.mem_zipIdx' hZip₂ with ⟨_hLt₂, hGet₂⟩
  have hRaw : raw₁ = raw₂ := hGet₁.trans hGet₂.symm
  cases hRaw
  exact ⟨rfl, HEq.rfl⟩

/-! ### Full active-symbol payload uniqueness -/

theorem tmVerifierIONamedStackSymbols_payload_unique
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    {n₁ n₂ : TMVerifierNamedStackSymbol V}
    (h₁ : n₁ ∈ tmVerifierIONamedStackSymbols V)
    (h₂ : n₂ ∈ tmVerifierIONamedStackSymbols V)
    (hPayload : n₁.payload = n₂.payload) :
    n₁.stack = n₂.stack ∧ HEq n₁.symbol n₂.symbol := by
  rw [tmVerifierIONamedStackSymbols] at h₁ h₂
  rcases List.mem_append.mp h₁ with hIn₁ | hOut₁
  · rcases List.mem_append.mp h₂ with hIn₂ | hOut₂
    · exact tmVerifierInputNamedStackSymbols_payload_unique V hIn₁ hIn₂ hPayload
    · rcases tmVerifierInputNamedStackSymbols_mem V n₁ hIn₁ with ⟨s₁, rfl⟩
      rcases tmVerifierOutputNamedStackSymbols_mem V n₂ hOut₂ with ⟨s₂, rfl⟩
      have hTag : 0 = 1 := (Nat.pair_eq_pair.mp hPayload).1
      contradiction
  · rcases List.mem_append.mp h₂ with hIn₂ | hOut₂
    · rcases tmVerifierOutputNamedStackSymbols_mem V n₁ hOut₁ with ⟨s₁, rfl⟩
      rcases tmVerifierInputNamedStackSymbols_mem V n₂ hIn₂ with ⟨s₂, rfl⟩
      have hTag : 1 = 0 := (Nat.pair_eq_pair.mp hPayload).1
      contradiction
    · exact tmVerifierOutputNamedStackSymbols_payload_unique V hOut₁ hOut₂ hPayload

theorem tmVerifierActiveStackSymbols_payload_unique
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    {n₁ n₂ : TMVerifierNamedStackSymbol V}
    (h₁ : n₁ ∈ tmVerifierActiveStackSymbols V)
    (h₂ : n₂ ∈ tmVerifierActiveStackSymbols V)
    (hPayload : n₁.payload = n₂.payload) :
    n₁.stack = n₂.stack ∧ HEq n₁.symbol n₂.symbol := by
  rw [tmVerifierActiveStackSymbols] at h₁ h₂
  rcases List.mem_append.mp h₁ with hIO₁ | hPush₁
  · rcases List.mem_append.mp h₂ with hIO₂ | hPush₂
    · exact tmVerifierIONamedStackSymbols_payload_unique V hIO₁ hIO₂ hPayload
    · rcases tmVerifierNamedPushedStackSymbols_mem V n₂ hPush₂ with
        ⟨raw₂, idx₂, _hZip₂, rfl⟩
      rw [tmVerifierIONamedStackSymbols] at hIO₁
      rcases List.mem_append.mp hIO₁ with hIn₁ | hOut₁
      · rcases tmVerifierInputNamedStackSymbols_mem V n₁ hIn₁ with ⟨s₁, rfl⟩
        exact False.elim ((tmVerifierIOSymbol_code_ne_pushedPayload V
          (TMVerifierIOSymbol.input (V := V) s₁) idx₂) hPayload)
      · rcases tmVerifierOutputNamedStackSymbols_mem V n₁ hOut₁ with ⟨s₁, rfl⟩
        exact False.elim ((tmVerifierIOSymbol_code_ne_pushedPayload V
          (TMVerifierIOSymbol.output (V := V) s₁) idx₂) hPayload)
  · rcases List.mem_append.mp h₂ with hIO₂ | hPush₂
    · rcases tmVerifierNamedPushedStackSymbols_mem V n₁ hPush₁ with
        ⟨raw₁, idx₁, _hZip₁, rfl⟩
      rw [tmVerifierIONamedStackSymbols] at hIO₂
      rcases List.mem_append.mp hIO₂ with hIn₂ | hOut₂
      · rcases tmVerifierInputNamedStackSymbols_mem V n₂ hIn₂ with ⟨s₂, rfl⟩
        exact False.elim ((tmVerifierIOSymbol_code_ne_pushedPayload V
          (TMVerifierIOSymbol.input (V := V) s₂) idx₁) hPayload.symm)
      · rcases tmVerifierOutputNamedStackSymbols_mem V n₂ hOut₂ with ⟨s₂, rfl⟩
        exact False.elim ((tmVerifierIOSymbol_code_ne_pushedPayload V
          (TMVerifierIOSymbol.output (V := V) s₂) idx₁) hPayload.symm)
    · exact tmVerifierNamedPushedStackSymbols_payload_unique V hPush₁ hPush₂ hPayload

theorem tmVerifierStackPayloadUnique
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMVerifierStackPayloadUnique V where
  unique := by
    intro k payload s₁ s₂ m₁ m₂
    have hPayload : m₁.named.payload = m₂.named.payload := by
      rw [m₁.payload_eq, m₂.payload_eq]
    have hActive :=
      tmVerifierActiveStackSymbols_payload_unique V m₁.named_mem m₂.named_mem hPayload
    exact eq_of_heq ((m₁.symbol_eq.symm.trans hActive.2).trans m₂.symbol_eq)

end SAT
end ComplexityReduction
