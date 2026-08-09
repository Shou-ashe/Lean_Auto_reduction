/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMStackActionBlocks

/-!
Concrete push-payload boundary for the future standard-TM Cook-Levin tableau.

`TMActiveSymbols` names every finitely collected pushed stack symbol by the
index at which it appears in `tmVerifierControlPushSymbols`.  This file exposes
that fact as a concrete `TMVerifierPushPayloadBoundary`, so later push-action
clauses can use a checked payload function instead of carrying an abstract
boundary parameter.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Coverage of named pushed symbols -/

/--
Every raw pushed symbol collected from the finite control graph has a named
payload in `tmVerifierNamedPushedStackSymbols`.
-/
theorem tmVerifierNamedPushedStackSymbols_cover
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (raw : TMVerifierStackSymbol V)
    (h : raw ∈ tmVerifierControlPushSymbols V) :
    ∃ named ∈ tmVerifierNamedPushedStackSymbols V,
      named.stack = raw.stack ∧ HEq named.symbol raw.symbol := by
  let xs := tmVerifierControlPushSymbols V
  have hExists : ∃ x ∈ xs, x = raw := ⟨raw, by simpa [xs] using h, rfl⟩
  rcases (List.exists_mem_iff_get.mp hExists) with ⟨i, hget⟩
  let named : TMVerifierNamedStackSymbol V :=
    { stack := (xs.get i).stack
      payload := Nat.pair 2 i
      symbol := (xs.get i).symbol }
  refine ⟨named, ?_, ?_, ?_⟩
  · have hzip : (xs.get i, (i : Nat)) ∈ xs.zipIdx := by
      rw [List.mem_iff_getElem]
      refine ⟨i.1, ?_, ?_⟩
      · simp [List.length_zipIdx]
      · simp
    have hmem :
        named ∈
          xs.zipIdx.map fun entry =>
            ({ stack := entry.1.stack
               payload := Nat.pair 2 entry.2
               symbol := entry.1.symbol } : TMVerifierNamedStackSymbol V) := by
      refine List.mem_map.mpr ⟨(xs.get i, (i : Nat)), hzip, ?_⟩
      rfl
    simpa [tmVerifierNamedPushedStackSymbols, xs] using hmem
  · change (xs.get i).stack = raw.stack
    rw [hget]
  · change HEq (xs.get i).symbol raw.symbol
    rw [hget]

/--
Every raw pushed symbol collected from the finite control graph has a named
payload in the full active-symbol boundary.
-/
theorem tmVerifierActiveStackSymbols_push_cover
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (raw : TMVerifierStackSymbol V)
    (h : raw ∈ tmVerifierControlPushSymbols V) :
    ∃ named ∈ tmVerifierActiveStackSymbols V,
      named.stack = raw.stack ∧ HEq named.symbol raw.symbol := by
  rcases tmVerifierNamedPushedStackSymbols_cover V raw h with
    ⟨named, hNamed, hStack, hSymbol⟩
  exact ⟨named, by simp [tmVerifierActiveStackSymbols, hNamed], hStack, hSymbol⟩

/-! ### Concrete push-payload function and boundary record -/

/--
The payload assigned to a raw pushed symbol.  Outside the collected control-push
set the value is irrelevant; push clauses only use the covered case.
-/
noncomputable def tmVerifierPushPayloadOf
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (raw : TMVerifierStackSymbol V) : Nat :=
  by
    classical
    exact
      if h : raw ∈ tmVerifierControlPushSymbols V then
        (Classical.choose (tmVerifierNamedPushedStackSymbols_cover V raw h)).payload
      else
        0

/-- Coverage theorem for the concrete push-payload function. -/
theorem tmVerifierPushPayloadOf_covered
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (raw : TMVerifierStackSymbol V)
    (h : raw ∈ tmVerifierControlPushSymbols V) :
    ∃ named ∈ tmVerifierActiveStackSymbols V,
      named.stack = raw.stack ∧
        named.payload = tmVerifierPushPayloadOf V raw ∧
          HEq named.symbol raw.symbol := by
  classical
  let named := Classical.choose (tmVerifierNamedPushedStackSymbols_cover V raw h)
  have hspec := Classical.choose_spec (tmVerifierNamedPushedStackSymbols_cover V raw h)
  rcases hspec with ⟨hNamed, hStack, hSymbol⟩
  refine ⟨named, ?_, hStack, ?_, hSymbol⟩
  · exact List.mem_append.mpr (Or.inr hNamed)
  · change named.payload = tmVerifierPushPayloadOf V raw
    simp [tmVerifierPushPayloadOf, h, named]

/-- Concrete inhabitant of the push-payload boundary required by stack-action clauses. -/
noncomputable def tmVerifierPushPayloadBoundary
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMVerifierPushPayloadBoundary V where
  payload := tmVerifierPushPayloadOf V
  covered := by
    intro raw h
    exact tmVerifierPushPayloadOf_covered V raw h

end SAT
end ComplexityReduction
