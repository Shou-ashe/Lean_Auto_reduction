/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyTransitions
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauExtraction

/-!
Projection lemmas for the x-only Cook-Levin tableau surface.

The x-only CNF fixes the instance prefix and leaves the certificate suffix
existential.  These lemmas expose the checked component blocks without turning
an arbitrary suffix word into a typed certificate.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Initial stack block projections -/

theorem tmVerifierXOnlyInputStackInitialCNF_satisfies
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (a : Assignment) :
    CNF.Satisfies (tmVerifierXOnlyInputStackInitialCNF V x) a ↔
      ∀ l ∈
        tmVerifierInstanceInputPrefixLiterals V x ++
          tmVerifierXOnlyInputStackEmptyTailLiterals V x,
          l.eval a = true := by
  simp [tmVerifierXOnlyInputStackInitialCNF, tmVerifierUnitClauses_satisfies]

theorem tmVerifierXOnlyInitialStackCNF_satisfies
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (a : Assignment) :
    CNF.Satisfies (tmVerifierXOnlyInitialStackCNF V x) a ↔
      (∀ l ∈
        tmVerifierInstanceInputPrefixLiterals V x ++
          tmVerifierXOnlyInputStackEmptyTailLiterals V x,
          l.eval a = true) ∧
      (∀ l ∈ tmVerifierXOnlyInitialNonInputEmptyLiterals V x, l.eval a = true) := by
  simp [tmVerifierXOnlyInitialStackCNF, CNF.satisfies_append,
    tmVerifierXOnlyInputStackInitialCNF_satisfies,
    tmVerifierXOnlyInitialNonInputEmptyStackCNF, tmVerifierUnitClauses_satisfies]

theorem tmVerifierXOnlyInitialStackCNF_satisfies_instancePrefix
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyInitialStackCNF V x) a) :
    CNF.Satisfies (tmVerifierInstanceInputPrefixCNF V x) a := by
  rw [tmVerifierInstanceInputPrefixCNF_satisfies]
  intro l hl
  exact ((tmVerifierXOnlyInitialStackCNF_satisfies V x a).1 h).1 l
    (List.mem_append_left _ hl)

theorem tmVerifierXOnlyInitialStackCNF_satisfies_input_prefix_symbol
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyInitialStackCNF V x) a)
    {i : Nat} (hi : i < (tmVerifierInstanceInputPrefixWord V x).length) :
    (tmVerifierInputStackSymbolAtom V 0 i
      (tmVerifierInstanceInputPrefixWord V x)[i]).eval a = true := by
  have hUnit := (tmVerifierXOnlyInitialStackCNF_satisfies V x a).1 h |>.1
  exact hUnit _ (by
    apply List.mem_append_left
    rw [tmVerifierInstanceInputPrefixLiterals]
    apply List.mem_map.mpr
    let hzip : i < (tmVerifierInstanceInputPrefixWord V x).zipIdx.length := by
      simpa using hi
    refine ⟨(tmVerifierInstanceInputPrefixWord V x).zipIdx[i], ?_, ?_⟩
    · exact List.getElem_mem (l := (tmVerifierInstanceInputPrefixWord V x).zipIdx) (n := i)
        hzip
    · rw [List.getElem_zipIdx]
      simp)

theorem tmVerifierXOnlyInitialStackCNF_satisfies_input_empty_tail
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyInitialStackCNF V x) a)
    {cell : Nat} (hcell : cell ∈ tmVerifierXOnlyCellRange V x)
    (hTail : tmVerifierXOnlyInputLengthBound V x ≤ cell) :
    (tmVerifierStackEmptyAtom V 0 (tmVerifierTM V).k₀ cell).eval a = true := by
  have hUnit := (tmVerifierXOnlyInitialStackCNF_satisfies V x a).1 h |>.1
  exact hUnit _ (by
    apply List.mem_append_right
    rw [tmVerifierXOnlyInputStackEmptyTailLiterals]
    apply List.mem_map.mpr
    refine ⟨cell, ?_, rfl⟩
    simp [hcell, hTail])

theorem tmVerifierXOnlyInitialStackCNF_satisfies_noninput_empty
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyInitialStackCNF V x) a)
    {k : tmVerifierStackIndex V} (hk : k ≠ (tmVerifierTM V).k₀)
    {cell : Nat} (hcell : cell ∈ tmVerifierXOnlyCellRange V x) :
    (tmVerifierStackEmptyAtom V 0 k cell).eval a = true := by
  have hUnit := (tmVerifierXOnlyInitialStackCNF_satisfies V x a).1 h |>.2
  exact hUnit _ (by
    rw [tmVerifierXOnlyInitialNonInputEmptyLiterals]
    rw [List.mem_flatMap]
    refine ⟨k, ?_, ?_⟩
    · simp [tmVerifierNonInputStacks, hk]
    · apply List.mem_map.mpr
      exact ⟨cell, hcell, rfl⟩)

/-! ### Endpoint block projections -/

theorem tmVerifierXOnlyOutputTrueCNFAt_satisfies
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) (a : Assignment) :
    CNF.Satisfies (tmVerifierXOnlyOutputTrueCNFAt V x t) a ↔
      (∀ l ∈
        tmVerifierOutputTrueSymbolLiteralsAt V t ++
          tmVerifierXOnlyOutputTrueEmptyTailLiteralsAt V x t,
          l.eval a = true) ∧
      (∀ l ∈ tmVerifierXOnlyOutputTrueNonOutputEmptyLiteralsAt V x t,
        l.eval a = true) := by
  simp [tmVerifierXOnlyOutputTrueCNFAt, CNF.satisfies_append,
    tmVerifierXOnlyOutputTrueStackCNFAt,
    tmVerifierXOnlyOutputTrueNonOutputEmptyStackCNFAt, tmVerifierUnitClauses_satisfies]

theorem tmVerifierXOnlyEndpointCNF_satisfies_halting
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyEndpointCNF V x) a) :
    CNF.Satisfies (tmVerifierHaltingControlCNFAt V (tmVerifierXOnlyTimeBound V x)) a :=
  (CNF.satisfies_append
    (tmVerifierHaltingControlCNFAt V (tmVerifierXOnlyTimeBound V x))
    (tmVerifierUnitCNF (tmVerifierStateAtom V (tmVerifierXOnlyTimeBound V x)
      (tmVerifierTM V).initialState) ++
      tmVerifierXOnlyOutputTrueCNFAt V x (tmVerifierXOnlyTimeBound V x)) a).1
      (by simpa [tmVerifierXOnlyEndpointCNF] using h) |>.1

theorem tmVerifierXOnlyEndpointCNF_satisfies_initialState
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyEndpointCNF V x) a) :
    (tmVerifierStateAtom V (tmVerifierXOnlyTimeBound V x)
      (tmVerifierTM V).initialState).eval a = true := by
  have htail := (CNF.satisfies_append
    (tmVerifierHaltingControlCNFAt V (tmVerifierXOnlyTimeBound V x))
    (tmVerifierUnitCNF (tmVerifierStateAtom V (tmVerifierXOnlyTimeBound V x)
      (tmVerifierTM V).initialState) ++
      tmVerifierXOnlyOutputTrueCNFAt V x (tmVerifierXOnlyTimeBound V x)) a).1
      (by simpa [tmVerifierXOnlyEndpointCNF] using h) |>.2
  have hstate := (CNF.satisfies_append
    (tmVerifierUnitCNF (tmVerifierStateAtom V (tmVerifierXOnlyTimeBound V x)
      (tmVerifierTM V).initialState))
    (tmVerifierXOnlyOutputTrueCNFAt V x (tmVerifierXOnlyTimeBound V x)) a).1 htail |>.1
  exact (tmVerifierUnitCNF_satisfies
    (tmVerifierStateAtom V (tmVerifierXOnlyTimeBound V x)
      (tmVerifierTM V).initialState) a).1 hstate

theorem tmVerifierXOnlyEndpointCNF_satisfies_outputTrue
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyEndpointCNF V x) a) :
    CNF.Satisfies (tmVerifierXOnlyOutputTrueCNFAt V x (tmVerifierXOnlyTimeBound V x)) a :=
  (CNF.satisfies_append
    (tmVerifierHaltingControlCNFAt V (tmVerifierXOnlyTimeBound V x))
    (tmVerifierUnitCNF (tmVerifierStateAtom V (tmVerifierXOnlyTimeBound V x)
      (tmVerifierTM V).initialState) ++
      tmVerifierXOnlyOutputTrueCNFAt V x (tmVerifierXOnlyTimeBound V x)) a).1
      (by simpa [tmVerifierXOnlyEndpointCNF] using h) |>.2 |>
    (CNF.satisfies_append
      (tmVerifierUnitCNF (tmVerifierStateAtom V (tmVerifierXOnlyTimeBound V x)
        (tmVerifierTM V).initialState))
      (tmVerifierXOnlyOutputTrueCNFAt V x (tmVerifierXOnlyTimeBound V x)) a).1 |>.2

/-! ### Aggregate block projections -/

theorem tmVerifierXOnlyGlobalTableauCNF_satisfies_controlDomainRows
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyGlobalTableauCNF V B x) a) :
    CNF.Satisfies ((tmVerifierXOnlyTableauTimeRange V x).flatMap fun t =>
      tmVerifierControlDomainCNFAt V t) a :=
  tmVerifierXOnlyGlobalTableauCNF_satisfies_block V B x a h (by
    simp [tmVerifierXOnlyGlobalTableauBlocks])

theorem tmVerifierXOnlyGlobalTableauCNF_satisfies_initialControl
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyGlobalTableauCNF V B x) a) :
    CNF.Satisfies (tmVerifierInitialControlCNF V) a :=
  tmVerifierXOnlyGlobalTableauCNF_satisfies_block V B x a h (by
    simp [tmVerifierXOnlyGlobalTableauBlocks])

theorem tmVerifierXOnlyGlobalTableauCNF_satisfies_initialStack
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyGlobalTableauCNF V B x) a) :
    CNF.Satisfies (tmVerifierXOnlyInitialStackCNF V x) a :=
  tmVerifierXOnlyGlobalTableauCNF_satisfies_block V B x a h (by
    simp [tmVerifierXOnlyGlobalTableauBlocks])

theorem tmVerifierXOnlyGlobalTableauCNF_satisfies_instancePrefix
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyGlobalTableauCNF V B x) a) :
    CNF.Satisfies (tmVerifierInstanceInputPrefixCNF V x) a :=
  tmVerifierXOnlyInitialStackCNF_satisfies_instancePrefix V x a
    (tmVerifierXOnlyGlobalTableauCNF_satisfies_initialStack V B x a h)

theorem tmVerifierXOnlyGlobalTableauCNF_satisfies_stackWellFormedRows
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyGlobalTableauCNF V B x) a) :
    CNF.Satisfies (tmVerifierXOnlyStackWellFormedRowsCNF V x) a :=
  tmVerifierXOnlyGlobalTableauCNF_satisfies_block V B x a h (by
    simp [tmVerifierXOnlyGlobalTableauBlocks])

theorem tmVerifierXOnlyGlobalTableauCNF_satisfies_transitionFixedMicroDomainRows
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyGlobalTableauCNF V B x) a) :
    CNF.Satisfies (tmVerifierXOnlyTransitionFixedMicroDomainRowsCNF V x) a :=
  tmVerifierXOnlyGlobalTableauCNF_satisfies_block V B x a h (by
    simp [tmVerifierXOnlyGlobalTableauBlocks])

theorem tmVerifierXOnlyGlobalTableauCNF_satisfies_endpoint
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyGlobalTableauCNF V B x) a) :
    CNF.Satisfies (tmVerifierXOnlyEndpointCNF V x) a :=
  tmVerifierXOnlyGlobalTableauCNF_satisfies_block V B x a h (by
    simp [tmVerifierXOnlyGlobalTableauBlocks])

theorem tmVerifierXOnlyControlDomainRowsCNF_satisfies_at
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies ((tmVerifierXOnlyTableauTimeRange V x).flatMap fun t =>
      tmVerifierControlDomainCNFAt V t) a)
    (ht : t ∈ tmVerifierXOnlyTableauTimeRange V x) :
    CNF.Satisfies (tmVerifierControlDomainCNFAt V t) a := by
  intro c hc
  exact h c (by
    exact List.mem_flatMap.mpr ⟨t, ht, hc⟩)

theorem tmVerifierXOnlyGlobalTableauCNF_satisfies_controlDomainRow
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyGlobalTableauCNF V B x) a)
    (ht : t ∈ tmVerifierXOnlyTableauTimeRange V x) :
    CNF.Satisfies (tmVerifierControlDomainCNFAt V t) a :=
  tmVerifierXOnlyControlDomainRowsCNF_satisfies_at V x t a
    (tmVerifierXOnlyGlobalTableauCNF_satisfies_controlDomainRows V B x a h) ht

theorem tmVerifierXOnlyStackWellFormedRowsCNF_satisfies_at
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyStackWellFormedRowsCNF V x) a)
    (ht : t ∈ tmVerifierXOnlyTableauTimeRange V x) :
    CNF.Satisfies (tmVerifierXOnlyAllStackWellFormedCNFAt V x t) a := by
  intro c hc
  exact h c (by
    rw [tmVerifierXOnlyStackWellFormedRowsCNF]
    exact List.mem_flatMap.mpr ⟨t, ht, hc⟩)

theorem tmVerifierXOnlyAllStackWellFormedCNFAt_satisfies_stack
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) (k : tmVerifierStackIndex V)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyAllStackWellFormedCNFAt V x t) a) :
    CNF.Satisfies (tmVerifierXOnlyStackWellFormedCNFAt V x t k) a := by
  intro c hc
  exact h c (by
    rw [tmVerifierXOnlyAllStackWellFormedCNFAt]
    exact List.mem_flatMap.mpr ⟨k, tmVerifierStackList_mem V k, hc⟩)

theorem tmVerifierXOnlyGlobalTableauCNF_satisfies_stackWellFormedAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (t : Nat) (k : tmVerifierStackIndex V)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyGlobalTableauCNF V B x) a)
    (ht : t ∈ tmVerifierXOnlyTableauTimeRange V x) :
    CNF.Satisfies (tmVerifierXOnlyStackWellFormedCNFAt V x t k) a :=
  tmVerifierXOnlyAllStackWellFormedCNFAt_satisfies_stack V x t k a
    (tmVerifierXOnlyStackWellFormedRowsCNF_satisfies_at V x t a
      (tmVerifierXOnlyGlobalTableauCNF_satisfies_stackWellFormedRows V B x a h) ht)

theorem tmVerifierXOnlyGlobalTableauCNF_satisfies_stackDomainsAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (t : Nat) (k : tmVerifierStackIndex V)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyGlobalTableauCNF V B x) a)
    (ht : t ∈ tmVerifierXOnlyTableauTimeRange V x) :
    CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t k) a :=
  tmVerifierXOnlyStackWellFormedCNFAt_satisfies_domains V x t k a
    (tmVerifierXOnlyGlobalTableauCNF_satisfies_stackWellFormedAt V B x t k a h ht)

theorem tmVerifierXOnlyTransitionFixedMicroDomainRowsCNF_satisfies_at
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyTransitionFixedMicroDomainRowsCNF V x) a)
    (ht : t ∈ tmVerifierXOnlyTransitionTimeRange V x) :
    CNF.Satisfies (tmVerifierXOnlyTransitionFixedMicroDomainCNFAt V x t) a := by
  intro c hc
  exact h c (by
    rw [tmVerifierXOnlyTransitionFixedMicroDomainRowsCNF]
    exact List.mem_flatMap.mpr ⟨t, ht, hc⟩)

theorem tmVerifierXOnlyTransitionFixedMicroDomainCNFAt_satisfies_window
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyTransitionFixedMicroDomainCNFAt V x t) a)
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s) :
    CNF.Satisfies (tmVerifierXOnlyWindowFixedMicroDomainCNFAt V x t w) a := by
  intro c hc
  exact h c (by
    rw [tmVerifierXOnlyTransitionFixedMicroDomainCNFAt]
    exact List.mem_flatMap.mpr
      ⟨l, hl, List.mem_flatMap.mpr
        ⟨s, hs, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩⟩)

theorem tmVerifierXOnlyWindowFixedMicroDomainCNFAt_satisfies_wellFormed_of_microTime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (micro : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyWindowFixedMicroDomainCNFAt V x t w) a)
    (hmicro : micro ∈ tmVerifierWindowMicroTimeRange V w)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies
      (tmVerifierXOnlyStackWellFormedCNFAt V x
        (tmVerifierXOnlyFixedMicroTime V x t micro) k) a := by
  intro c hc
  exact h c (by
    rw [tmVerifierXOnlyWindowFixedMicroDomainCNFAt]
    exact List.mem_flatMap.mpr
      ⟨micro, hmicro,
        List.mem_flatMap.mpr ⟨k, tmVerifierStackList_mem V k, hc⟩⟩)

theorem tmVerifierXOnlyWindowFixedMicroDomainCNFAt_satisfies_domain_of_microTime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (micro : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyWindowFixedMicroDomainCNFAt V x t w) a)
    (hmicro : micro ∈ tmVerifierWindowMicroTimeRange V w)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies
      (tmVerifierXOnlyStackCellDomainsCNFAt V x
        (tmVerifierXOnlyFixedMicroTime V x t micro) k) a :=
  tmVerifierXOnlyStackWellFormedCNFAt_satisfies_domains V x
    (tmVerifierXOnlyFixedMicroTime V x t micro) k a
    (tmVerifierXOnlyWindowFixedMicroDomainCNFAt_satisfies_wellFormed_of_microTime
      V x t w micro a h hmicro k)

theorem tmVerifierXOnlyWindowFixedMicroDomainCNFAt_satisfies_domain
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (micro : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyWindowFixedMicroDomainCNFAt V x t w) a)
    (hmicro : micro ∈ tmVerifierWindowActionMicroTimeRange V w)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies
      (tmVerifierXOnlyStackCellDomainsCNFAt V x
        (tmVerifierXOnlyFixedMicroTime V x t micro) k) a :=
  tmVerifierXOnlyWindowFixedMicroDomainCNFAt_satisfies_domain_of_microTime V x t w
    micro a h (tmVerifierWindowActionMicroTimeRange_mem_microTimeRange V w hmicro) k

theorem tmVerifierXOnlyGlobalTableauCNF_satisfies_transitionFixedMicroDomainRow
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyGlobalTableauCNF V B x) a)
    (ht : t ∈ tmVerifierXOnlyTransitionTimeRange V x) :
    CNF.Satisfies (tmVerifierXOnlyTransitionFixedMicroDomainCNFAt V x t) a :=
  tmVerifierXOnlyTransitionFixedMicroDomainRowsCNF_satisfies_at V x t a
    (tmVerifierXOnlyGlobalTableauCNF_satisfies_transitionFixedMicroDomainRows V B x a h)
    ht

/-! ### Packed x-only tableau evidence -/

structure TMVerifierXOnlyGlobalTableauEvidence
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (a : Assignment) : Type where
  controlDomainRow :
    ∀ t, t ∈ tmVerifierXOnlyTableauTimeRange V x →
      CNF.Satisfies (tmVerifierControlDomainCNFAt V t) a
  controlRow :
    ∀ t, t ∈ tmVerifierXOnlyTableauTimeRange V x → TMVerifierDecodedControlRow V t a
  initial_label :
    (tmVerifierLabelAtom V 0 (some (tmVerifierTM V).main)).eval a = true
  initial_state :
    (tmVerifierStateAtom V 0 (tmVerifierTM V).initialState).eval a = true
  initial_stack : CNF.Satisfies (tmVerifierXOnlyInitialStackCNF V x) a
  stackWellFormedRow :
    ∀ t, t ∈ tmVerifierXOnlyTableauTimeRange V x →
      CNF.Satisfies (tmVerifierXOnlyAllStackWellFormedCNFAt V x t) a
  transitionFixedMicroDomainRow :
    ∀ t, t ∈ tmVerifierXOnlyTransitionTimeRange V x →
      CNF.Satisfies (tmVerifierXOnlyTransitionFixedMicroDomainCNFAt V x t) a
  transitionFixedRow :
    ∀ t, t ∈ tmVerifierXOnlyTransitionTimeRange V x →
      CNF.Satisfies (tmVerifierXOnlyTransitionFixedRowCNFAt V B x t) a
  endpoint_halted :
    (tmVerifierLabelAtom V (tmVerifierXOnlyTimeBound V x) none).eval a = true
  endpoint_state :
    (tmVerifierStateAtom V (tmVerifierXOnlyTimeBound V x)
      (tmVerifierTM V).initialState).eval a = true
  endpoint_output_true :
    CNF.Satisfies (tmVerifierXOnlyOutputTrueCNFAt V x (tmVerifierXOnlyTimeBound V x)) a
  instance_prefix :
    CNF.Satisfies (tmVerifierInstanceInputPrefixCNF V x) a

noncomputable def tmVerifierXOnlyGlobalTableauCNF_evidence
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyGlobalTableauCNF V B x) a) :
    TMVerifierXOnlyGlobalTableauEvidence V B x a := by
  let hControlRows := tmVerifierXOnlyGlobalTableauCNF_satisfies_controlDomainRows V B x a h
  let hInitialControl := tmVerifierXOnlyGlobalTableauCNF_satisfies_initialControl V B x a h
  let hEndpoint := tmVerifierXOnlyGlobalTableauCNF_satisfies_endpoint V B x a h
  exact
    { controlDomainRow := fun t ht =>
        tmVerifierXOnlyControlDomainRowsCNF_satisfies_at V x t a hControlRows ht
      controlRow := fun t ht =>
        tmVerifierControlDomainCNFAt_decoded V t a
          (tmVerifierXOnlyControlDomainRowsCNF_satisfies_at V x t a hControlRows ht)
      initial_label :=
        tmVerifierInitialControlCNF_satisfies_initialLabel V a hInitialControl
      initial_state :=
        tmVerifierInitialControlCNF_satisfies_initialState V a hInitialControl
      initial_stack :=
        tmVerifierXOnlyGlobalTableauCNF_satisfies_initialStack V B x a h
      stackWellFormedRow := fun t ht =>
        tmVerifierXOnlyStackWellFormedRowsCNF_satisfies_at V x t a
          (tmVerifierXOnlyGlobalTableauCNF_satisfies_stackWellFormedRows V B x a h) ht
      transitionFixedMicroDomainRow := fun t ht =>
        tmVerifierXOnlyGlobalTableauCNF_satisfies_transitionFixedMicroDomainRow V B x t a
          h ht
      transitionFixedRow := fun t ht =>
        tmVerifierXOnlyGlobalTableauCNF_satisfies_transitionFixedRow V B x t a h ht
      endpoint_halted :=
        tmVerifierHaltingControlCNFAt_satisfies_halted V (tmVerifierXOnlyTimeBound V x) a
          (tmVerifierXOnlyEndpointCNF_satisfies_halting V x a hEndpoint)
      endpoint_state :=
        tmVerifierXOnlyEndpointCNF_satisfies_initialState V x a hEndpoint
      endpoint_output_true :=
        tmVerifierXOnlyEndpointCNF_satisfies_outputTrue V x a hEndpoint
      instance_prefix :=
        tmVerifierXOnlyGlobalTableauCNF_satisfies_instancePrefix V B x a h }

namespace TMVerifierXOnlyGlobalTableauEvidence

theorem stackWellFormedAt
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (t : Nat) (ht : t ∈ tmVerifierXOnlyTableauTimeRange V x)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierXOnlyStackWellFormedCNFAt V x t k) a :=
  tmVerifierXOnlyAllStackWellFormedCNFAt_satisfies_stack V x t k a
    (E.stackWellFormedRow t ht)

theorem stackCellDomainsAt
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (t : Nat) (ht : t ∈ tmVerifierXOnlyTableauTimeRange V x)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t k) a :=
  tmVerifierXOnlyStackWellFormedCNFAt_satisfies_domains V x t k a
    (E.stackWellFormedAt t ht k)

theorem transitionStackCellDomainsAt
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {t : Nat} (ht : t ∈ tmVerifierXOnlyTransitionTimeRange V x)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t k) a :=
  E.stackCellDomainsAt t
    (by
      rw [tmVerifierXOnlyTransitionTimeRange, List.mem_range] at ht
      exact tmVerifierXOnlyTableauTimeRange_mem_of_le V x (Nat.le_of_lt ht))
    k

theorem controlRow_label_proof_irrel
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {t : Nat} (ht ht' : t ∈ tmVerifierXOnlyTableauTimeRange V x) :
    (E.controlRow t ht).label = (E.controlRow t ht').label := by
  have hproof : ht = ht' := Subsingleton.elim ht ht'
  cases hproof
  rfl

theorem controlRow_state_proof_irrel
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {t : Nat} (ht ht' : t ∈ tmVerifierXOnlyTableauTimeRange V x) :
    (E.controlRow t ht).state = (E.controlRow t ht').state := by
  have hproof : ht = ht' := Subsingleton.elim ht ht'
  cases hproof
  rfl

end TMVerifierXOnlyGlobalTableauEvidence

end SAT
end ComplexityReduction
