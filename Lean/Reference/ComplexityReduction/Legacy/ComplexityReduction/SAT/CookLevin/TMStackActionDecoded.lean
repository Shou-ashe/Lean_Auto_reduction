/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMStackDecoder

/-!
Decoded-cell consequences of primitive stack-action CNF blocks.

`TMStackActionSemantics` proves that satisfied action clauses propagate raw
atoms.  This file repackages those atom facts as decoded stack cells.  It is
still cell-level: list-stack equality and the final `TM2.stepAux` alignment are
left for the aggregate transition semantics layer.
-/

namespace ComplexityReduction
namespace SAT

theorem tmVerifierPushPayloadBoundary_readChoice_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (raw : TMVerifierStackSymbol V)
    (hraw : raw ∈ tmVerifierControlPushSymbols V) :
    TMVerifierStackReadChoice.symbol (V := V) (k := raw.stack)
        (B.payload raw) raw.symbol ∈
      tmVerifierStackReadChoices V raw.stack := by
  rcases B.covered raw hraw with ⟨named, hNamed, hStack, hPayload, hSymbol⟩
  rcases raw with ⟨rawStack, rawSymbol⟩
  rcases named with ⟨namedStack, namedPayload, namedSymbol⟩
  simp at hStack hPayload hSymbol hNamed ⊢
  cases hStack
  have hSymbolEq : namedSymbol = rawSymbol := by
    simpa using hSymbol
  simpa [hPayload, hSymbolEq] using
    tmVerifierActiveReadChoice_mem_of_named V
      ({ stack := rawStack, payload := namedPayload, symbol := namedSymbol } :
        TMVerifierNamedStackSymbol V) hNamed

/-! ### Push decoded-cell consequences -/

def tmVerifierPushActionCNFBetween_decoded_top
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierPushActionCNFBetween V B p tin tout raw antecedents) a)
    (hraw : raw ∈ tmVerifierControlPushSymbols V)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    TMVerifierDecodedStackCell V tout raw.stack 0 a :=
  { choice := TMVerifierStackReadChoice.symbol (V := V) (k := raw.stack)
      (B.payload raw) raw.symbol
    choice_mem := tmVerifierPushPayloadBoundary_readChoice_mem V B raw hraw
    atom_true := by
      simpa [TMVerifierStackReadChoice.atomAt] using
        tmVerifierPushActionCNFBetween_satisfies_top V B p tin tout raw antecedents a h
          hAntecedents }

def tmVerifierPushActionCNFBetween_decoded_shift
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (cell : Nat) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierPushActionCNFBetween V B p tin tout raw antecedents) a)
    (hcell : cell ∈ tmVerifierCellRange V p)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (d : TMVerifierDecodedStackCell V tin raw.stack cell a) :
    TMVerifierDecodedStackCell V tout raw.stack (cell + 1) a :=
  { choice := d.choice
    choice_mem := d.choice_mem
    atom_true :=
      tmVerifierPushActionCNFBetween_satisfies_shift V B p tin tout raw cell d.choice
        antecedents a h hcell d.choice_mem hAntecedents d.atom_true }

def tmVerifierPushActionCNFBetween_decoded_other_stack_forward
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (j : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierPushActionCNFBetween V B p tin tout raw antecedents) a)
    (hj : j ∈ tmVerifierOtherStacks V raw.stack)
    (hcell : cell ∈ tmVerifierCellRange V p)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (d : TMVerifierDecodedStackCell V tin j cell a) :
    TMVerifierDecodedStackCell V tout j cell a :=
  { choice := d.choice
    choice_mem := d.choice_mem
    atom_true :=
      tmVerifierPushActionCNFBetween_satisfies_other_stack_forward V B p tin tout raw j cell
        d.choice antecedents a h hj hcell d.choice_mem hAntecedents d.atom_true }

/-! ### Pop and preserve decoded-cell consequences -/

def tmVerifierPopActionCNFBetween_decoded_shift
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierPopActionCNFBetween V p tin tout k antecedents) a)
    (hcell : cell ∈ tmVerifierCellRange V p)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (d : TMVerifierDecodedStackCell V tin k (cell + 1) a) :
    TMVerifierDecodedStackCell V tout k cell a :=
  { choice := d.choice
    choice_mem := d.choice_mem
    atom_true :=
      tmVerifierPopActionCNFBetween_satisfies_shift V p tin tout k cell d.choice antecedents
        a h hcell d.choice_mem hAntecedents d.atom_true }

def tmVerifierPopActionCNFBetween_decoded_other_stack_forward
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (k j : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierPopActionCNFBetween V p tin tout k antecedents) a)
    (hj : j ∈ tmVerifierOtherStacks V k)
    (hcell : cell ∈ tmVerifierCellRange V p)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (d : TMVerifierDecodedStackCell V tin j cell a) :
    TMVerifierDecodedStackCell V tout j cell a :=
  { choice := d.choice
    choice_mem := d.choice_mem
    atom_true :=
      tmVerifierPopActionCNFBetween_satisfies_other_stack_forward V p tin tout k j cell
        d.choice antecedents a h hj hcell d.choice_mem hAntecedents d.atom_true }

def tmVerifierPreserveAllStacksActionCNFBetween_decoded_forward
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierPreserveAllStacksActionCNFBetween V p tin tout antecedents) a)
    (hk : k ∈ tmVerifierStackList V)
    (hcell : cell ∈ tmVerifierCellRange V p)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (d : TMVerifierDecodedStackCell V tin k cell a) :
    TMVerifierDecodedStackCell V tout k cell a :=
  { choice := d.choice
    choice_mem := d.choice_mem
    atom_true :=
      tmVerifierPreserveAllStacksActionCNFBetween_satisfies_forward V p tin tout k cell d.choice
        antecedents a h hk hcell d.choice_mem hAntecedents d.atom_true }

def tmVerifierPreserveAllStacksActionCNFBetween_decoded_backward
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierPreserveAllStacksActionCNFBetween V p tin tout antecedents) a)
    (hk : k ∈ tmVerifierStackList V)
    (hcell : cell ∈ tmVerifierCellRange V p)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (d : TMVerifierDecodedStackCell V tout k cell a) :
    TMVerifierDecodedStackCell V tin k cell a :=
  { choice := d.choice
    choice_mem := d.choice_mem
    atom_true :=
      tmVerifierPreserveAllStacksActionCNFBetween_satisfies_backward V p tin tout k cell
        d.choice antecedents a h hk hcell d.choice_mem hAntecedents d.atom_true }

end SAT
end ComplexityReduction
