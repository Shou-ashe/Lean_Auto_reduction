/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTransitionRowSemantics
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMXOnlyCertificate

/-!
Aggregate verifier-tableau CNF surface.

Previous slices define local CNF blocks and semantic extraction lemmas.  This
file packages those blocks into a fixed-pair tableau CNF and an x-only
existential tableau seed.  The results here are only block-extraction lemmas:
they do not yet prove that the aggregate CNF is satisfiable iff the verifier
accepts.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Time ranges and row-level block groups -/

/-- Macro time rows of the bounded verifier tableau for a fixed pair. -/
noncomputable def tmVerifierTableauTimeRange {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) : List Nat :=
  List.range (tmVerifierTimeBound V p + 1)

/-- Macro transition rows; each row has a successor row inside `tmVerifierTableauTimeRange`. -/
noncomputable def tmVerifierTransitionTimeRange {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) : List Nat :=
  List.range (tmVerifierTimeBound V p)

theorem tmVerifierStackList_mem {L : EncodedDecisionProblem}
    (V : TMVerifier L) (k : tmVerifierStackIndex V) :
    k ∈ tmVerifierStackList V := by
  classical
  simp [tmVerifierStackList]

/-- Exactly-one label/state domain at one macro time row. -/
noncomputable def tmVerifierControlDomainCNFAt {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) : CNF :=
  tmVerifierExactlyOneLabelCNFAt V t ++ tmVerifierExactlyOneStateCNFAt V t

/-- Exactly-one label/state domains for every bounded macro time row. -/
noncomputable def tmVerifierControlDomainRowsCNF {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) : CNF :=
  (tmVerifierTableauTimeRange V p).flatMap fun t =>
    tmVerifierControlDomainCNFAt V t

/-- Stack well-formedness rows at every bounded macro time row. -/
noncomputable def tmVerifierStackWellFormedRowsCNF {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) : CNF :=
  (tmVerifierTableauTimeRange V p).flatMap fun t =>
    tmVerifierAllStackWellFormedCNFAt V p t

/-- Micro-time indices used as action inputs/outputs by one selected statement window. -/
noncomputable def tmVerifierWindowActionMicroTimeRange {L : EncodedDecisionProblem}
    (V : TMVerifier L) (w : TMVerifierStmtWindow V) : List Nat :=
  w.actions.zipIdx.flatMap fun entry => [entry.2, entry.2 + 1]

/-- Micro-time indices whose stack rows are used by one statement window. -/
noncomputable def tmVerifierWindowMicroTimeRange {L : EncodedDecisionProblem}
    (V : TMVerifier L) (w : TMVerifierStmtWindow V) : List Nat :=
  0 :: w.actions.length :: tmVerifierWindowActionMicroTimeRange V w

theorem tmVerifierWindowMicroTimeRange_zero_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (w : TMVerifierStmtWindow V) :
    0 ∈ tmVerifierWindowMicroTimeRange V w := by
  simp [tmVerifierWindowMicroTimeRange]

theorem tmVerifierWindowMicroTimeRange_final_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (w : TMVerifierStmtWindow V) :
    w.actions.length ∈ tmVerifierWindowMicroTimeRange V w := by
  simp [tmVerifierWindowMicroTimeRange]

theorem tmVerifierWindowActionMicroTimeRange_mem_microTimeRange
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (w : TMVerifierStmtWindow V) {micro : Nat}
    (hmicro : micro ∈ tmVerifierWindowActionMicroTimeRange V w) :
    micro ∈ tmVerifierWindowMicroTimeRange V w := by
  simp [tmVerifierWindowMicroTimeRange, hmicro]

theorem tmVerifierWindowActionMicroTimeRange_input_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (w : TMVerifierStmtWindow V) (entry : TMVerifierStackAction V × Nat)
    (hentry : entry ∈ w.actions.zipIdx) :
    entry.2 ∈ tmVerifierWindowActionMicroTimeRange V w := by
  rw [tmVerifierWindowActionMicroTimeRange]
  exact List.mem_flatMap.mpr ⟨entry, hentry, by simp⟩

theorem tmVerifierWindowActionMicroTimeRange_output_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (w : TMVerifierStmtWindow V) (entry : TMVerifierStackAction V × Nat)
    (hentry : entry ∈ w.actions.zipIdx) :
    entry.2 + 1 ∈ tmVerifierWindowActionMicroTimeRange V w := by
  rw [tmVerifierWindowActionMicroTimeRange]
  exact List.mem_flatMap.mpr ⟨entry, hentry, by simp⟩

/-- Stack well-formed rows for all micro rows touched by one statement window. -/
noncomputable def tmVerifierWindowMicroDomainCNFAt {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) : CNF :=
  (tmVerifierWindowMicroTimeRange V w).flatMap fun micro =>
    (tmVerifierStackList V).flatMap fun k =>
      tmVerifierStackWellFormedCNFAt V p (tmVerifierMicroTime t micro) k

theorem tmVerifierWindowMicroDomainCNFAt_satisfies_wellFormed_of_microTime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (micro : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierWindowMicroDomainCNFAt V p t w) a)
    (hmicro : micro ∈ tmVerifierWindowMicroTimeRange V w)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p (tmVerifierMicroTime t micro) k)
      a := by
  intro c hc
  exact h c (by
    rw [tmVerifierWindowMicroDomainCNFAt]
    exact List.mem_flatMap.mpr
      ⟨micro, hmicro,
        List.mem_flatMap.mpr ⟨k, tmVerifierStackList_mem V k, hc⟩⟩)

theorem tmVerifierWindowMicroDomainCNFAt_satisfies_wellFormed
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (micro : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierWindowMicroDomainCNFAt V p t w) a)
    (hmicro : micro ∈ tmVerifierWindowActionMicroTimeRange V w)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p (tmVerifierMicroTime t micro) k)
      a :=
  tmVerifierWindowMicroDomainCNFAt_satisfies_wellFormed_of_microTime V p t w micro a h
    (tmVerifierWindowActionMicroTimeRange_mem_microTimeRange V w hmicro) k

theorem tmVerifierWindowMicroDomainCNFAt_satisfies_domain_of_microTime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (micro : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierWindowMicroDomainCNFAt V p t w) a)
    (hmicro : micro ∈ tmVerifierWindowMicroTimeRange V w)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t micro) k)
      a := by
  have hWF :=
    tmVerifierWindowMicroDomainCNFAt_satisfies_wellFormed_of_microTime V p t w micro a h
      hmicro k
  exact tmVerifierStackWellFormedCNFAt_satisfies_domains V p (tmVerifierMicroTime t micro) k
    a hWF

theorem tmVerifierWindowMicroDomainCNFAt_satisfies_domain
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (micro : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierWindowMicroDomainCNFAt V p t w) a)
    (hmicro : micro ∈ tmVerifierWindowActionMicroTimeRange V w)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t micro) k)
      a := by
  exact tmVerifierWindowMicroDomainCNFAt_satisfies_domain_of_microTime V p t w micro a h
    (tmVerifierWindowActionMicroTimeRange_mem_microTimeRange V w hmicro) k

/-- Micro-domain rows for every statement window of one transition row. -/
noncomputable def tmVerifierTransitionMicroDomainCNFAt {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) : CNF :=
  (tmVerifierLabelList V).flatMap fun l =>
    (tmVerifierStateList V).flatMap fun s =>
      (tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s).flatMap fun w =>
        tmVerifierWindowMicroDomainCNFAt V p t w

theorem tmVerifierTransitionMicroDomainCNFAt_satisfies_window
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierTransitionMicroDomainCNFAt V p t) a)
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s) :
    CNF.Satisfies (tmVerifierWindowMicroDomainCNFAt V p t w) a := by
  intro c hc
  exact h c (by
    rw [tmVerifierTransitionMicroDomainCNFAt]
    exact List.mem_flatMap.mpr
      ⟨l, hl, List.mem_flatMap.mpr
        ⟨s, hs, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩⟩)

/-- Micro-domain rows for every transition row with a successor. -/
noncomputable def tmVerifierTransitionMicroDomainRowsCNF {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) : CNF :=
  (tmVerifierTransitionTimeRange V p).flatMap fun t =>
    tmVerifierTransitionMicroDomainCNFAt V p t

theorem tmVerifierTransitionMicroDomainRowsCNF_satisfies_at
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierTransitionMicroDomainRowsCNF V p) a)
    (ht : t ∈ tmVerifierTransitionTimeRange V p) :
    CNF.Satisfies (tmVerifierTransitionMicroDomainCNFAt V p t) a := by
  intro c hc
  exact h c (by
    rw [tmVerifierTransitionMicroDomainRowsCNF]
    exact List.mem_flatMap.mpr ⟨t, ht, hc⟩)

/-- Transition rows for every macro time row with a successor. -/
noncomputable def tmVerifierTransitionRowsCNF {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) : CNF :=
  (tmVerifierTransitionTimeRange V p).flatMap fun t =>
    tmVerifierTransitionRowCNFAt V B p t

/-- Final halting/output-true endpoint block at the supplied time bound. -/
noncomputable def tmVerifierEndpointCNF {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) : CNF :=
  tmVerifierHaltingControlCNFAt V (tmVerifierTimeBound V p) ++
    tmVerifierUnitCNF (tmVerifierStateAtom V (tmVerifierTimeBound V p)
      (tmVerifierTM V).initialState) ++
    tmVerifierOutputTrueCNFAt V p (tmVerifierTimeBound V p)

/-! ### Fixed-pair aggregate tableau -/

/-- Named component blocks of the fixed-pair verifier tableau. -/
noncomputable def tmVerifierFixedPairTableauBlocks {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) : List CNF :=
  [ tmVerifierControlDomainRowsCNF V p
  , tmVerifierInitialControlCNF V
  , tmVerifierInitialStackCNF V p
  , tmVerifierStackWellFormedRowsCNF V p
  , tmVerifierTransitionMicroDomainRowsCNF V p
  , tmVerifierTransitionRowsCNF V B p
  , tmVerifierEndpointCNF V p
  ]

/-- Aggregate fixed-pair tableau CNF. -/
noncomputable def tmVerifierFixedPairTableauCNF {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) : CNF :=
  (tmVerifierFixedPairTableauBlocks V B p).flatMap id

theorem tmVerifierFixedPairTableauCNF_satisfies_block
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierFixedPairTableauCNF V B p) a)
    {block : CNF} (hblock : block ∈ tmVerifierFixedPairTableauBlocks V B p) :
    CNF.Satisfies block a := by
  intro c hc
  exact h c (by
    rw [tmVerifierFixedPairTableauCNF]
    exact List.mem_flatMap.mpr ⟨block, hblock, hc⟩)

theorem tmVerifierControlDomainRowsCNF_satisfies_at
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierControlDomainRowsCNF V p) a)
    (ht : t ∈ tmVerifierTableauTimeRange V p) :
    CNF.Satisfies (tmVerifierControlDomainCNFAt V t) a := by
  intro c hc
  exact h c (by
    rw [tmVerifierControlDomainRowsCNF]
    exact List.mem_flatMap.mpr ⟨t, ht, hc⟩)

theorem tmVerifierStackWellFormedRowsCNF_satisfies_at
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackWellFormedRowsCNF V p) a)
    (ht : t ∈ tmVerifierTableauTimeRange V p) :
    CNF.Satisfies (tmVerifierAllStackWellFormedCNFAt V p t) a := by
  intro c hc
  exact h c (by
    rw [tmVerifierStackWellFormedRowsCNF]
    exact List.mem_flatMap.mpr ⟨t, ht, hc⟩)

theorem tmVerifierTransitionRowsCNF_satisfies_at
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierTransitionRowsCNF V B p) a)
    (ht : t ∈ tmVerifierTransitionTimeRange V p) :
    CNF.Satisfies (tmVerifierTransitionRowCNFAt V B p t) a := by
  intro c hc
  exact h c (by
    rw [tmVerifierTransitionRowsCNF]
    exact List.mem_flatMap.mpr ⟨t, ht, hc⟩)

theorem tmVerifierEndpointCNF_satisfies_halting
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierEndpointCNF V p) a) :
    CNF.Satisfies (tmVerifierHaltingControlCNFAt V (tmVerifierTimeBound V p)) a :=
  (CNF.satisfies_append
    (tmVerifierHaltingControlCNFAt V (tmVerifierTimeBound V p))
    (tmVerifierUnitCNF (tmVerifierStateAtom V (tmVerifierTimeBound V p)
      (tmVerifierTM V).initialState) ++
      tmVerifierOutputTrueCNFAt V p (tmVerifierTimeBound V p)) a).1
      (by simpa [tmVerifierEndpointCNF] using h) |>.1

theorem tmVerifierEndpointCNF_satisfies_initialState
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierEndpointCNF V p) a) :
    (tmVerifierStateAtom V (tmVerifierTimeBound V p) (tmVerifierTM V).initialState).eval
      a = true := by
  have htail := (CNF.satisfies_append
    (tmVerifierHaltingControlCNFAt V (tmVerifierTimeBound V p))
    (tmVerifierUnitCNF (tmVerifierStateAtom V (tmVerifierTimeBound V p)
      (tmVerifierTM V).initialState) ++
      tmVerifierOutputTrueCNFAt V p (tmVerifierTimeBound V p)) a).1
      (by simpa [tmVerifierEndpointCNF] using h) |>.2
  have hstate := (CNF.satisfies_append
    (tmVerifierUnitCNF (tmVerifierStateAtom V (tmVerifierTimeBound V p)
      (tmVerifierTM V).initialState))
    (tmVerifierOutputTrueCNFAt V p (tmVerifierTimeBound V p)) a).1 htail |>.1
  exact (tmVerifierUnitCNF_satisfies
    (tmVerifierStateAtom V (tmVerifierTimeBound V p) (tmVerifierTM V).initialState) a).1
    hstate

theorem tmVerifierEndpointCNF_satisfies_outputTrue
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierEndpointCNF V p) a) :
    CNF.Satisfies (tmVerifierOutputTrueCNFAt V p (tmVerifierTimeBound V p)) a :=
  (CNF.satisfies_append
    (tmVerifierHaltingControlCNFAt V (tmVerifierTimeBound V p))
    (tmVerifierUnitCNF (tmVerifierStateAtom V (tmVerifierTimeBound V p)
      (tmVerifierTM V).initialState) ++
      tmVerifierOutputTrueCNFAt V p (tmVerifierTimeBound V p)) a).1
      (by simpa [tmVerifierEndpointCNF] using h) |>.2 |>
    (CNF.satisfies_append
      (tmVerifierUnitCNF (tmVerifierStateAtom V (tmVerifierTimeBound V p)
        (tmVerifierTM V).initialState))
      (tmVerifierOutputTrueCNFAt V p (tmVerifierTimeBound V p)) a).1 |>.2

theorem tmVerifierFixedPairTableauCNF_satisfies_controlDomainRows
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierFixedPairTableauCNF V B p) a) :
    CNF.Satisfies (tmVerifierControlDomainRowsCNF V p) a :=
  tmVerifierFixedPairTableauCNF_satisfies_block V B p a h (by
    simp [tmVerifierFixedPairTableauBlocks])

theorem tmVerifierFixedPairTableauCNF_satisfies_initialControl
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierFixedPairTableauCNF V B p) a) :
    CNF.Satisfies (tmVerifierInitialControlCNF V) a :=
  tmVerifierFixedPairTableauCNF_satisfies_block V B p a h (by
    simp [tmVerifierFixedPairTableauBlocks])

theorem tmVerifierFixedPairTableauCNF_satisfies_initialStack
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierFixedPairTableauCNF V B p) a) :
    CNF.Satisfies (tmVerifierInitialStackCNF V p) a :=
  tmVerifierFixedPairTableauCNF_satisfies_block V B p a h (by
    simp [tmVerifierFixedPairTableauBlocks])

theorem tmVerifierFixedPairTableauCNF_satisfies_stackWellFormedRows
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierFixedPairTableauCNF V B p) a) :
    CNF.Satisfies (tmVerifierStackWellFormedRowsCNF V p) a :=
  tmVerifierFixedPairTableauCNF_satisfies_block V B p a h (by
    simp [tmVerifierFixedPairTableauBlocks])

theorem tmVerifierFixedPairTableauCNF_satisfies_transitionRows
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierFixedPairTableauCNF V B p) a) :
    CNF.Satisfies (tmVerifierTransitionRowsCNF V B p) a :=
  tmVerifierFixedPairTableauCNF_satisfies_block V B p a h (by
    simp [tmVerifierFixedPairTableauBlocks])

theorem tmVerifierFixedPairTableauCNF_satisfies_transitionMicroDomainRows
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierFixedPairTableauCNF V B p) a) :
    CNF.Satisfies (tmVerifierTransitionMicroDomainRowsCNF V p) a :=
  tmVerifierFixedPairTableauCNF_satisfies_block V B p a h (by
    simp [tmVerifierFixedPairTableauBlocks])

theorem tmVerifierFixedPairTableauCNF_satisfies_endpoint
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierFixedPairTableauCNF V B p) a) :
    CNF.Satisfies (tmVerifierEndpointCNF V p) a :=
  tmVerifierFixedPairTableauCNF_satisfies_block V B p a h (by
    simp [tmVerifierFixedPairTableauBlocks])

theorem tmVerifierFixedPairTableauCNF_satisfies_transitionRow
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierFixedPairTableauCNF V B p) a)
    (ht : t ∈ tmVerifierTransitionTimeRange V p) :
    CNF.Satisfies (tmVerifierTransitionRowCNFAt V B p t) a :=
  tmVerifierTransitionRowsCNF_satisfies_at V B p t a
    (tmVerifierFixedPairTableauCNF_satisfies_transitionRows V B p a h) ht

theorem tmVerifierFixedPairTableauCNF_satisfies_transitionMicroDomainRow
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierFixedPairTableauCNF V B p) a)
    (ht : t ∈ tmVerifierTransitionTimeRange V p) :
    CNF.Satisfies (tmVerifierTransitionMicroDomainCNFAt V p t) a :=
  tmVerifierTransitionMicroDomainRowsCNF_satisfies_at V p t a
    (tmVerifierFixedPairTableauCNF_satisfies_transitionMicroDomainRows V B p a h) ht

theorem tmVerifierFixedPairTableauCNF_satisfies_instancePrefix
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierFixedPairTableauCNF V B (x, c)) a) :
    CNF.Satisfies (tmVerifierInstanceInputPrefixCNF V x) a :=
  tmVerifierInitialStackCNF_satisfies_instancePrefix V x c a
    (tmVerifierFixedPairTableauCNF_satisfies_initialStack V B (x, c) a h)

/-! ### x-only aggregate tableau seeds -/

/--
An x-only tableau seed chooses a bounded certificate and satisfies the fixed-pair
aggregate tableau for that certificate.
-/
structure TMVerifierXOnlyTableauSeed {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (a : Assignment) : Type where
  cert : V.Cert.Carrier
  cert_size :
    V.Cert.inputSize cert ≤ tmVerifierCertificateSizeBound V x
  fixed_tableau :
    CNF.Satisfies (tmVerifierFixedPairTableauCNF V B (x, cert)) a

namespace TMVerifierXOnlyTableauSeed

theorem nonempty_iff_exists {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (a : Assignment) :
    Nonempty (TMVerifierXOnlyTableauSeed V B x a) ↔
      ∃ c, V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x ∧
        CNF.Satisfies (tmVerifierFixedPairTableauCNF V B (x, c)) a := by
  constructor
  · rintro ⟨w⟩
    exact ⟨w.cert, w.cert_size, w.fixed_tableau⟩
  · rintro ⟨c, hSize, hTableau⟩
    exact ⟨{ cert := c, cert_size := hSize, fixed_tableau := hTableau }⟩

/-- Forget the aggregate tableau and retain the x-only initial seed. -/
def toInitialSeed {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyTableauSeed V B x a) :
    TMVerifierXOnlyInitialSeed V x a where
  cert := w.cert
  cert_size := w.cert_size
  initial_stack :=
    tmVerifierFixedPairTableauCNF_satisfies_initialStack V B (x, w.cert) a
      w.fixed_tableau

theorem prefixCNF_satisfies {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyTableauSeed V B x a) :
    CNF.Satisfies (tmVerifierInstanceInputPrefixCNF V x) a :=
  w.toInitialSeed.prefixCNF_satisfies

theorem transitionRow_satisfies {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyTableauSeed V B x a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V (x, w.cert)) :
    CNF.Satisfies (tmVerifierTransitionRowCNFAt V B (x, w.cert) t) a :=
  tmVerifierFixedPairTableauCNF_satisfies_transitionRow V B (x, w.cert) t a
    w.fixed_tableau ht

theorem endpoint_satisfies {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyTableauSeed V B x a) :
    CNF.Satisfies (tmVerifierEndpointCNF V (x, w.cert)) a :=
  tmVerifierFixedPairTableauCNF_satisfies_endpoint V B (x, w.cert) a w.fixed_tableau

end TMVerifierXOnlyTableauSeed

end SAT
end ComplexityReduction
