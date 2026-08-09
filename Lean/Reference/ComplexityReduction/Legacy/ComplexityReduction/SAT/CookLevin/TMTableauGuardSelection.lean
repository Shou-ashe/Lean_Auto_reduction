/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauMicroDomains

/-!
Top-cell guard alignment for selected transition windows.

Statement windows for `peek` and `pop` carry a guard asserting a particular
top-cell read choice.  This file proves that, in a satisfied fixed-pair
tableau, any such true guard agrees with the decoded top cell coming from the
macro-time stack-domain row.
-/

namespace ComplexityReduction
namespace SAT

theorem tmVerifierAllStackWellFormedCNFAt_satisfies_stackDomains
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierAllStackWellFormedCNFAt V p t) a) :
    CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a := by
  have hStack : CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p t k) a := by
    intro c hc
    exact h c (by
      rw [tmVerifierAllStackWellFormedCNFAt]
      exact List.mem_flatMap.mpr ⟨k, tmVerifierStackList_mem V k, hc⟩)
  exact tmVerifierStackWellFormedCNFAt_satisfies_domains V p t k a hStack

namespace TMVerifierFixedPairTableauEvidence

theorem stackCellDomainsAt
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a)
    (t : Nat) (ht : t ∈ tmVerifierTableauTimeRange V p)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a :=
  tmVerifierAllStackWellFormedCNFAt_satisfies_stackDomains V p t k a
    (E.stackWellFormedRow t ht)

theorem transitionStackCellDomainsAt
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a :=
  E.stackCellDomainsAt t (tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht) k

noncomputable def topDecodedCell
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a)
    (t : Nat) (ht : t ∈ tmVerifierTableauTimeRange V p)
    (k : tmVerifierStackIndex V) :
    TMVerifierDecodedStackCell V t k 0 a :=
  tmVerifierDecodedStackCellOf V p t k 0 a (E.stackCellDomainsAt t ht k)
    (tmVerifierCellRange_zero_mem V p)

theorem topDecodedCell_choice_eq_of_guard
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTableauTimeRange V p)
    (k : tmVerifierStackIndex V) (choice : TMVerifierStackReadChoice V k)
    (hchoice : choice ∈ tmVerifierStackReadChoices V k)
    (hGuard :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice).eval a = true) :
    (E.topDecodedCell t ht k).choice = choice := by
  let hDomain := E.stackCellDomainsAt t ht k
  let d := E.topDecodedCell t ht k
  exact tmVerifierStackCellDomainsCNFAt_satisfies_choice_eq V p t k 0 a hDomain
    (tmVerifierCellRange_zero_mem V p) d.choice choice d.choice_mem hchoice d.atom_true hGuard

theorem topDecodedCell_choice_eq_of_guard_mem
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTableauTimeRange V p)
    {w : TMVerifierStmtWindow V} (hGuards : ∀ g ∈ w.guards, g.eval a = true)
    (k : tmVerifierStackIndex V) (choice : TMVerifierStackReadChoice V k)
    (hchoice : choice ∈ tmVerifierStackReadChoices V k)
    (hGuardMem :
      TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice ∈ w.guards) :
    (E.topDecodedCell t ht k).choice = choice :=
  E.topDecodedCell_choice_eq_of_guard ht k choice hchoice (hGuards _ hGuardMem)

theorem transitionTopDecodedCell_choice_eq_of_guard
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p)
    (k : tmVerifierStackIndex V) (choice : TMVerifierStackReadChoice V k)
    (hchoice : choice ∈ tmVerifierStackReadChoices V k)
    (hGuard :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice).eval a = true) :
    (E.topDecodedCell t (tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht) k).choice =
      choice :=
  E.topDecodedCell_choice_eq_of_guard
    (tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht) k choice hchoice hGuard

end TMVerifierFixedPairTableauEvidence

namespace TMVerifierXOnlyTableauSeed

noncomputable def topDecodedCell
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyTableauSeed V B x a)
    (t : Nat) (ht : t ∈ tmVerifierTableauTimeRange V (x, wSeed.cert))
    (k : tmVerifierStackIndex V) :
    TMVerifierDecodedStackCell V t k 0 a :=
  wSeed.fixedPairEvidence.topDecodedCell t ht k

theorem topDecodedCell_choice_eq_of_guard
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyTableauSeed V B x a)
    {t : Nat} (ht : t ∈ tmVerifierTableauTimeRange V (x, wSeed.cert))
    (k : tmVerifierStackIndex V) (choice : TMVerifierStackReadChoice V k)
    (hchoice : choice ∈ tmVerifierStackReadChoices V k)
    (hGuard :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice).eval a = true) :
    (wSeed.topDecodedCell t ht k).choice = choice :=
  wSeed.fixedPairEvidence.topDecodedCell_choice_eq_of_guard ht k choice hchoice hGuard

theorem transitionTopDecodedCell_choice_eq_of_guard
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyTableauSeed V B x a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V (x, wSeed.cert))
    (k : tmVerifierStackIndex V) (choice : TMVerifierStackReadChoice V k)
    (hchoice : choice ∈ tmVerifierStackReadChoices V k)
    (hGuard :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice).eval a = true) :
    (wSeed.topDecodedCell t
      (tmVerifierTransitionTimeRange_mem_tableauTimeRange V (x, wSeed.cert) ht) k).choice =
      choice :=
  wSeed.fixedPairEvidence.transitionTopDecodedCell_choice_eq_of_guard ht k choice hchoice
    hGuard

end TMVerifierXOnlyTableauSeed

end SAT
end ComplexityReduction
