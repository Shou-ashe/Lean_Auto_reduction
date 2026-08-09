/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMStackActionDecoded

/-!
Payload-decoder surface for active stack symbols.

The CNF atom for a nonempty stack cell stores only a numeric payload.  The
finite read-choice list still carries the dependent stack symbol.  This file
connects those two views: every nonempty read choice is traced back to an
active named symbol.  Full uniqueness of payloads is kept as an explicit
boundary record, because that is the condition needed before arbitrary decoded
prefix choices can be identified by payload alone.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Active payload matches -/

/--
A concrete stack symbol matching one active payload.

This is a relational decoder: it records the active named-symbol row that
justifies the `(stack, payload, symbol)` triple.
-/
structure TMVerifierStackPayloadMatch {L : EncodedDecisionProblem}
    (V : TMVerifier L) (k : tmVerifierStackIndex V) (payload : Nat)
    (symbol : (tmVerifierTM V).Γ k) where
  named : TMVerifierNamedStackSymbol V
  named_mem : named ∈ tmVerifierActiveStackSymbols V
  stack_eq : named.stack = k
  payload_eq : named.payload = payload
  symbol_eq : HEq named.symbol symbol

theorem tmVerifierActiveReadChoiceOfNamed?_eq_some_symbol
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (k : tmVerifierStackIndex V) (named : TMVerifierNamedStackSymbol V)
    (payload : Nat) (symbol : (tmVerifierTM V).Γ k)
    (h :
      tmVerifierActiveReadChoiceOfNamed? V k named =
        some (TMVerifierStackReadChoice.symbol (V := V) (k := k) payload symbol)) :
    named.stack = k ∧ named.payload = payload ∧ HEq named.symbol symbol := by
  unfold tmVerifierActiveReadChoiceOfNamed? at h
  by_cases hStack : named.stack = k
  · rw [dif_pos hStack] at h
    cases hStack
    cases h
    exact ⟨rfl, rfl, HEq.rfl⟩
  · rw [dif_neg hStack] at h
    simp at h

noncomputable def tmVerifierStackReadChoice_symbol_payload_match
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (k : tmVerifierStackIndex V) (payload : Nat)
    (symbol : (tmVerifierTM V).Γ k)
    (h :
      TMVerifierStackReadChoice.symbol (V := V) (k := k) payload symbol ∈
        tmVerifierStackReadChoices V k) :
    TMVerifierStackPayloadMatch V k payload symbol := by
  classical
  have hActive :
      TMVerifierStackReadChoice.symbol (V := V) (k := k) payload symbol ∈
        tmVerifierActiveReadChoices V k := by
    simpa [tmVerifierStackReadChoices] using h
  have hExists :
      ∃ named ∈ tmVerifierActiveStackSymbols V,
        tmVerifierActiveReadChoiceOfNamed? V k named =
          some (TMVerifierStackReadChoice.symbol (V := V) (k := k) payload symbol) := by
    rw [tmVerifierActiveReadChoices] at hActive
    exact List.mem_filterMap.mp hActive
  let named := Classical.choose hExists
  have hNamed : named ∈ tmVerifierActiveStackSymbols V :=
    (Classical.choose_spec hExists).1
  have hSome :
      tmVerifierActiveReadChoiceOfNamed? V k named =
        some (TMVerifierStackReadChoice.symbol (V := V) (k := k) payload symbol) :=
    (Classical.choose_spec hExists).2
  have hInv := tmVerifierActiveReadChoiceOfNamed?_eq_some_symbol V k named payload symbol hSome
  exact
    { named := named
      named_mem := hNamed
      stack_eq := hInv.1
      payload_eq := hInv.2.1
      symbol_eq := hInv.2.2 }

noncomputable def tmVerifierPushPayloadBoundary_payload_match
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (raw : TMVerifierStackSymbol V)
    (hraw : raw ∈ tmVerifierControlPushSymbols V) :
    TMVerifierStackPayloadMatch V raw.stack (B.payload raw) raw.symbol := by
  classical
  let witness := B.covered raw hraw
  let named := Classical.choose witness
  have hspec := Classical.choose_spec witness
  exact
    { named := named
      named_mem := hspec.1
      stack_eq := hspec.2.1
      payload_eq := hspec.2.2.1
      symbol_eq := hspec.2.2.2 }

noncomputable def tmVerifierDecodedStackCell_payload_match
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    {t : Nat} {k : tmVerifierStackIndex V} {cell payload : Nat}
    {symbol : (tmVerifierTM V).Γ k} {a : Assignment}
    (d : TMVerifierDecodedStackCell V t k cell a)
    (hchoice :
      d.choice = TMVerifierStackReadChoice.symbol (V := V) (k := k) payload symbol) :
    TMVerifierStackPayloadMatch V k payload symbol := by
  exact tmVerifierStackReadChoice_symbol_payload_match V k payload symbol
    (by simpa [hchoice] using d.choice_mem)

/-! ### Explicit payload-uniqueness boundary -/

/--
Boundary needed to identify decoded stack cells by payload alone.

The current relational decoder is concrete, but full prefix/list equality later
needs this uniqueness principle whenever two decoded choices mention the same
`stack` and numeric `payload`.
-/
structure TMVerifierStackPayloadUnique {L : EncodedDecisionProblem}
    (V : TMVerifier L) : Prop where
  unique :
    ∀ {k : tmVerifierStackIndex V} {payload : Nat}
      {s₁ s₂ : (tmVerifierTM V).Γ k},
      TMVerifierStackPayloadMatch V k payload s₁ →
        TMVerifierStackPayloadMatch V k payload s₂ → s₁ = s₂

theorem tmVerifierStackReadChoice_symbol_eq_of_payloadUnique
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (U : TMVerifierStackPayloadUnique V)
    (k : tmVerifierStackIndex V) (payload : Nat)
    (s₁ s₂ : (tmVerifierTM V).Γ k)
    (h₁ :
      TMVerifierStackReadChoice.symbol (V := V) (k := k) payload s₁ ∈
        tmVerifierStackReadChoices V k)
    (h₂ :
      TMVerifierStackReadChoice.symbol (V := V) (k := k) payload s₂ ∈
        tmVerifierStackReadChoices V k) :
    s₁ = s₂ :=
  U.unique
    (tmVerifierStackReadChoice_symbol_payload_match V k payload s₁ h₁)
    (tmVerifierStackReadChoice_symbol_payload_match V k payload s₂ h₂)

theorem tmVerifierDecodedStackCell_symbol_eq_of_payloadUnique
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (U : TMVerifierStackPayloadUnique V)
    {t₁ t₂ : Nat} {k : tmVerifierStackIndex V} {cell₁ cell₂ payload : Nat}
    {s₁ s₂ : (tmVerifierTM V).Γ k} {a : Assignment}
    (d₁ : TMVerifierDecodedStackCell V t₁ k cell₁ a)
    (d₂ : TMVerifierDecodedStackCell V t₂ k cell₂ a)
    (h₁ :
      d₁.choice = TMVerifierStackReadChoice.symbol (V := V) (k := k) payload s₁)
    (h₂ :
      d₂.choice = TMVerifierStackReadChoice.symbol (V := V) (k := k) payload s₂) :
    s₁ = s₂ :=
  U.unique
    (tmVerifierDecodedStackCell_payload_match V d₁ h₁)
    (tmVerifierDecodedStackCell_payload_match V d₂ h₂)

end SAT
end ComplexityReduction
