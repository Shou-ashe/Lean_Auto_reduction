/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.Control

namespace ComplexityReduction
namespace SAT

/-! ### Unified control-boundary assignment -/

theorem tmVerifierTableauVar_ne_of_kind_tag_ne
    {kind₁ kind₂ : TMVerifierTableauVarKind}
    {time₁ stack₁ cell₁ payload₁ time₂ stack₂ cell₂ payload₂ : Nat}
    (hKind : kind₁.tag ≠ kind₂.tag) :
    tmVerifierTableauVar kind₁ time₁ stack₁ cell₁ payload₁ ≠
      tmVerifierTableauVar kind₂ time₂ stack₂ cell₂ payload₂ := by
  intro h
  exact hKind (Nat.pair_eq_pair.mp h).1

theorem tmVerifierStackSymbolAtom_var_ne_labelAtom_var
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t u : Nat) (k : tmVerifierStackIndex V) (cell payload : Nat)
    (label : Option (tmVerifierTM V).Λ) :
    (tmVerifierStackSymbolAtom V t k cell payload).var ≠
      (tmVerifierLabelAtom V u label).var := by
  simpa [tmVerifierStackSymbolAtom, tmVerifierLabelAtom, tmVerifierTableauAtom]
    using tmVerifierTableauVar_ne_of_kind_tag_ne
      (kind₁ := TMVerifierTableauVarKind.stackSymbol)
      (kind₂ := TMVerifierTableauVarKind.label)
      (time₁ := t) (stack₁ := tmVerifierStackCode V k) (cell₁ := cell)
      (payload₁ := payload) (time₂ := u) (stack₂ := 0) (cell₂ := 0)
      (payload₂ := tmVerifierLabelCode V label)
      (by simp [TMVerifierTableauVarKind.tag])

theorem tmVerifierStackSymbolAtom_var_ne_stateAtom_var
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t u : Nat) (k : tmVerifierStackIndex V) (cell payload : Nat)
    (state : (tmVerifierTM V).σ) :
    (tmVerifierStackSymbolAtom V t k cell payload).var ≠
      (tmVerifierStateAtom V u state).var := by
  simpa [tmVerifierStackSymbolAtom, tmVerifierStateAtom, tmVerifierTableauAtom]
    using tmVerifierTableauVar_ne_of_kind_tag_ne
      (kind₁ := TMVerifierTableauVarKind.stackSymbol)
      (kind₂ := TMVerifierTableauVarKind.state)
      (time₁ := t) (stack₁ := tmVerifierStackCode V k) (cell₁ := cell)
      (payload₁ := payload) (time₂ := u) (stack₂ := 0) (cell₂ := 0)
      (payload₂ := tmVerifierStateCode V state)
      (by simp [TMVerifierTableauVarKind.tag])

theorem tmVerifierStackEmptyAtom_var_ne_labelAtom_var
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t u : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (label : Option (tmVerifierTM V).Λ) :
    (tmVerifierStackEmptyAtom V t k cell).var ≠
      (tmVerifierLabelAtom V u label).var := by
  simpa [tmVerifierStackEmptyAtom, tmVerifierLabelAtom, tmVerifierTableauAtom]
    using tmVerifierTableauVar_ne_of_kind_tag_ne
      (kind₁ := TMVerifierTableauVarKind.stackEmpty)
      (kind₂ := TMVerifierTableauVarKind.label)
      (time₁ := t) (stack₁ := tmVerifierStackCode V k) (cell₁ := cell)
      (payload₁ := 0) (time₂ := u) (stack₂ := 0) (cell₂ := 0)
      (payload₂ := tmVerifierLabelCode V label)
      (by simp [TMVerifierTableauVarKind.tag])

theorem tmVerifierStackEmptyAtom_var_ne_stateAtom_var
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t u : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (state : (tmVerifierTM V).σ) :
    (tmVerifierStackEmptyAtom V t k cell).var ≠
      (tmVerifierStateAtom V u state).var := by
  simpa [tmVerifierStackEmptyAtom, tmVerifierStateAtom, tmVerifierTableauAtom]
    using tmVerifierTableauVar_ne_of_kind_tag_ne
      (kind₁ := TMVerifierTableauVarKind.stackEmpty)
      (kind₂ := TMVerifierTableauVarKind.state)
      (time₁ := t) (stack₁ := tmVerifierStackCode V k) (cell₁ := cell)
      (payload₁ := 0) (time₂ := u) (stack₂ := 0) (cell₂ := 0)
      (payload₂ := tmVerifierStateCode V state)
      (by simp [TMVerifierTableauVarKind.tag])

theorem tmVerifierStackSymbolAtom_var_ne_stackEmptyAtom_var
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t u : Nat) (k j : tmVerifierStackIndex V) (cell₁ cell₂ payload : Nat) :
    (tmVerifierStackSymbolAtom V t k cell₁ payload).var ≠
      (tmVerifierStackEmptyAtom V u j cell₂).var := by
  simpa [tmVerifierStackSymbolAtom, tmVerifierStackEmptyAtom, tmVerifierTableauAtom]
    using tmVerifierTableauVar_ne_of_kind_tag_ne
      (kind₁ := TMVerifierTableauVarKind.stackSymbol)
      (kind₂ := TMVerifierTableauVarKind.stackEmpty)
      (time₁ := t) (stack₁ := tmVerifierStackCode V k) (cell₁ := cell₁)
      (payload₁ := payload) (time₂ := u) (stack₂ := tmVerifierStackCode V j)
      (cell₂ := cell₂) (payload₂ := 0)
      (by simp [TMVerifierTableauVarKind.tag])

theorem tmVerifierStackEmptyAtom_var_ne_stackSymbolAtom_var
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t u : Nat) (k j : tmVerifierStackIndex V) (cell₁ cell₂ payload : Nat) :
    (tmVerifierStackEmptyAtom V t k cell₁).var ≠
      (tmVerifierStackSymbolAtom V u j cell₂ payload).var := by
  intro h
  exact tmVerifierStackSymbolAtom_var_ne_stackEmptyAtom_var V u t j k cell₂ cell₁ payload h.symm

theorem tmVerifierStackCode_injective
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    Function.Injective (tmVerifierStackCode V) := by
  intro k j h
  letI : Fintype (tmVerifierTM V).K := (tmVerifierTM V).kFin
  have hFin :
      (Fintype.equivFin (tmVerifierTM V).K) k =
        (Fintype.equivFin (tmVerifierTM V).K) j := by
    apply Fin.ext
    simpa [tmVerifierStackCode] using h
  exact (Fintype.equivFin (tmVerifierTM V).K).injective hFin

theorem tmVerifierStackSymbolAtom_var_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    {t u : Nat} {k j : tmVerifierStackIndex V} {cell₁ cell₂ payload₁ payload₂ : Nat}
    (h : (tmVerifierStackSymbolAtom V t k cell₁ payload₁).var =
        (tmVerifierStackSymbolAtom V u j cell₂ payload₂).var) :
    t = u ∧ tmVerifierStackCode V k = tmVerifierStackCode V j ∧
      cell₁ = cell₂ ∧ payload₁ = payload₂ := by
  have hTail :
      Nat.pair t
          (Nat.pair (tmVerifierStackCode V k) (Nat.pair cell₁ payload₁)) =
        Nat.pair u
          (Nat.pair (tmVerifierStackCode V j) (Nat.pair cell₂ payload₂)) := by
    simpa [tmVerifierStackSymbolAtom, tmVerifierTableauAtom, tmVerifierTableauVar,
      TMVerifierTableauVarKind.tag] using (Nat.pair_eq_pair.mp h).2
  have htu : t = u := (Nat.pair_eq_pair.mp hTail).1
  have hRest := (Nat.pair_eq_pair.mp hTail).2
  have hStack : tmVerifierStackCode V k = tmVerifierStackCode V j :=
    (Nat.pair_eq_pair.mp hRest).1
  have hCellPayload := (Nat.pair_eq_pair.mp hRest).2
  exact ⟨htu, hStack, (Nat.pair_eq_pair.mp hCellPayload).1,
    (Nat.pair_eq_pair.mp hCellPayload).2⟩

theorem tmVerifierStackSymbolAtom_var_eq_payload
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    {t u : Nat} {k j : tmVerifierStackIndex V} {cell₁ cell₂ payload₁ payload₂ : Nat}
    (h : (tmVerifierStackSymbolAtom V t k cell₁ payload₁).var =
        (tmVerifierStackSymbolAtom V u j cell₂ payload₂).var) :
    payload₁ = payload₂ :=
  (tmVerifierStackSymbolAtom_var_eq V h).2.2.2

theorem tmVerifierStackEmptyAtom_var_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    {t u : Nat} {k j : tmVerifierStackIndex V} {cell₁ cell₂ : Nat}
    (h : (tmVerifierStackEmptyAtom V t k cell₁).var =
        (tmVerifierStackEmptyAtom V u j cell₂).var) :
    t = u ∧ k = j ∧ cell₁ = cell₂ := by
  have hTail :
      Nat.pair t (Nat.pair (tmVerifierStackCode V k) (Nat.pair cell₁ 0)) =
        Nat.pair u (Nat.pair (tmVerifierStackCode V j) (Nat.pair cell₂ 0)) := by
    simpa [tmVerifierStackEmptyAtom, tmVerifierTableauAtom, tmVerifierTableauVar,
      TMVerifierTableauVarKind.tag] using (Nat.pair_eq_pair.mp h).2
  have htu : t = u := (Nat.pair_eq_pair.mp hTail).1
  have hRest := (Nat.pair_eq_pair.mp hTail).2
  have hStackCode : tmVerifierStackCode V k = tmVerifierStackCode V j :=
    (Nat.pair_eq_pair.mp hRest).1
  have hCellPayload := (Nat.pair_eq_pair.mp hRest).2
  exact ⟨htu, tmVerifierStackCode_injective V hStackCode,
    (Nat.pair_eq_pair.mp hCellPayload).1⟩

theorem tmVerifierInputNamedStackSymbols_payloads_nodup
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    ((tmVerifierInputNamedStackSymbols V).map fun named => named.payload).Nodup := by
  classical
  letI : Fintype ((tmVerifierTM V).Γ (tmVerifierTM V).k₀) := (tmVerifierTM V).Γk₀Fin
  letI : DecidableEq ((tmVerifierTM V).Γ (tmVerifierTM V).k₀) := Classical.decEq _
  rw [tmVerifierInputNamedStackSymbols, List.map_map]
  refine (Finset.nodup_toList
    (Finset.univ : Finset ((tmVerifierTM V).Γ (tmVerifierTM V).k₀))).map ?_
  intro s₁ s₂ h
  have hIO :
      TMVerifierIOSymbol.input (V := V) s₁ =
        TMVerifierIOSymbol.input (V := V) s₂ :=
    tmVerifierIOSymbol_code_injective V h
  cases hIO
  rfl

theorem tmVerifierOutputNamedStackSymbols_payloads_nodup
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    ((tmVerifierOutputNamedStackSymbols V).map fun named => named.payload).Nodup := by
  classical
  letI : Fintype ((tmVerifierTM V).Γ (tmVerifierTM V).k₁) :=
    Fintype.ofEquiv EncodedType.bool.Symbol
      (tmVerifierComputableWitness V).outputAlphabet.symm
  letI : DecidableEq ((tmVerifierTM V).Γ (tmVerifierTM V).k₁) := Classical.decEq _
  rw [tmVerifierOutputNamedStackSymbols, List.map_map]
  refine (Finset.nodup_toList
    (Finset.univ : Finset ((tmVerifierTM V).Γ (tmVerifierTM V).k₁))).map ?_
  intro s₁ s₂ h
  have hIO :
      TMVerifierIOSymbol.output (V := V) s₁ =
        TMVerifierIOSymbol.output (V := V) s₂ :=
    tmVerifierIOSymbol_code_injective V h
  cases hIO
  rfl

theorem tmVerifierInputOutputPayloads_disjoint
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    List.Disjoint ((tmVerifierInputNamedStackSymbols V).map fun named => named.payload)
      ((tmVerifierOutputNamedStackSymbols V).map fun named => named.payload) := by
  intro payload hIn hOut
  rcases List.mem_map.mp hIn with ⟨namedIn, hNamedIn, rfl⟩
  rcases tmVerifierInputNamedStackSymbols_mem V namedIn hNamedIn with ⟨sIn, rfl⟩
  rcases List.mem_map.mp hOut with ⟨namedOut, hNamedOut, hPayload⟩
  rcases tmVerifierOutputNamedStackSymbols_mem V namedOut hNamedOut with ⟨sOut, rfl⟩
  have hTag : 1 = 0 := (Nat.pair_eq_pair.mp hPayload).1
  contradiction

theorem tmVerifierIONamedStackSymbols_payloads_nodup
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    ((tmVerifierIONamedStackSymbols V).map fun named => named.payload).Nodup := by
  rw [tmVerifierIONamedStackSymbols, List.map_append]
  exact (tmVerifierInputNamedStackSymbols_payloads_nodup V).append
    (tmVerifierOutputNamedStackSymbols_payloads_nodup V)
    (tmVerifierInputOutputPayloads_disjoint V)

theorem tmVerifierNamedPushedStackSymbols_payloads_nodup
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    ((tmVerifierNamedPushedStackSymbols V).map fun named => named.payload).Nodup := by
  rw [tmVerifierNamedPushedStackSymbols, List.map_map]
  have hIdx : (((tmVerifierControlPushSymbols V).zipIdx).map Prod.snd).Nodup :=
    List.nodup_zipIdx_map_snd (tmVerifierControlPushSymbols V)
  have hPayloads :
      (List.map (fun idx => Nat.pair 2 idx)
        (((tmVerifierControlPushSymbols V).zipIdx).map Prod.snd)).Nodup :=
    hIdx.map (by
      intro i j h
      exact (Nat.pair_eq_pair.mp h).2)
  rw [List.map_map] at hPayloads
  simpa [Function.comp_def] using hPayloads

theorem tmVerifierIOPushedPayloads_disjoint
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    List.Disjoint ((tmVerifierIONamedStackSymbols V).map fun named => named.payload)
      ((tmVerifierNamedPushedStackSymbols V).map fun named => named.payload) := by
  intro payload hIO hPush
  rw [tmVerifierIONamedStackSymbols, List.map_append] at hIO
  rcases List.mem_append.mp hIO with hIn | hOut
  · rcases List.mem_map.mp hIn with ⟨namedIn, hNamedIn, rfl⟩
    rcases tmVerifierInputNamedStackSymbols_mem V namedIn hNamedIn with ⟨sIn, rfl⟩
    rcases List.mem_map.mp hPush with ⟨namedPush, hNamedPush, hPayload⟩
    rcases tmVerifierNamedPushedStackSymbols_mem V namedPush hNamedPush with
      ⟨raw, idx, _hZip, rfl⟩
    have hTag : 2 = 0 := (Nat.pair_eq_pair.mp hPayload).1
    contradiction
  · rcases List.mem_map.mp hOut with ⟨namedOut, hNamedOut, rfl⟩
    rcases tmVerifierOutputNamedStackSymbols_mem V namedOut hNamedOut with ⟨sOut, rfl⟩
    rcases List.mem_map.mp hPush with ⟨namedPush, hNamedPush, hPayload⟩
    rcases tmVerifierNamedPushedStackSymbols_mem V namedPush hNamedPush with
      ⟨raw, idx, _hZip, rfl⟩
    have hTag : 2 = 1 := (Nat.pair_eq_pair.mp hPayload).1
    contradiction

theorem tmVerifierActiveStackSymbols_payloads_nodup
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    ((tmVerifierActiveStackSymbols V).map fun named => named.payload).Nodup := by
  rw [tmVerifierActiveStackSymbols, List.map_append]
  exact (tmVerifierIONamedStackSymbols_payloads_nodup V).append
    (tmVerifierNamedPushedStackSymbols_payloads_nodup V)
    (tmVerifierIOPushedPayloads_disjoint V)

theorem tmVerifierActiveStackSymbols_nodup
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    (tmVerifierActiveStackSymbols V).Nodup :=
  List.Nodup.of_map (fun named : TMVerifierNamedStackSymbol V => named.payload)
    (tmVerifierActiveStackSymbols_payloads_nodup V)

theorem tmVerifierActiveReadChoiceOfNamed?_eq_some_injective
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (k : tmVerifierStackIndex V) (named₁ named₂ : TMVerifierNamedStackSymbol V)
    (choice : TMVerifierStackReadChoice V k)
    (h₁ : tmVerifierActiveReadChoiceOfNamed? V k named₁ = some choice)
    (h₂ : tmVerifierActiveReadChoiceOfNamed? V k named₂ = some choice) :
    named₁ = named₂ := by
  cases choice with
  | empty =>
      unfold tmVerifierActiveReadChoiceOfNamed? at h₁
      split at h₁ <;> simp at h₁
  | symbol payload symbol =>
      rcases
        tmVerifierActiveReadChoiceOfNamed?_eq_some_symbol V k named₁ payload symbol h₁
        with ⟨hStack₁, hPayload₁, hSymbol₁⟩
      rcases
        tmVerifierActiveReadChoiceOfNamed?_eq_some_symbol V k named₂ payload symbol h₂
        with ⟨hStack₂, hPayload₂, hSymbol₂⟩
      rcases named₁ with ⟨stack₁, payload₁, symbol₁⟩
      rcases named₂ with ⟨stack₂, payload₂, symbol₂⟩
      simp at hStack₁ hStack₂ hPayload₁ hPayload₂ hSymbol₁ hSymbol₂ ⊢
      cases hStack₁
      cases hStack₂
      cases hPayload₁
      cases hPayload₂
      constructor
      · rfl
      constructor
      · rfl
      · exact hSymbol₁.trans hSymbol₂.symm

theorem tmVerifierActiveReadChoices_nodup
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (k : tmVerifierStackIndex V) :
    (tmVerifierActiveReadChoices V k).Nodup := by
  rw [tmVerifierActiveReadChoices]
  exact (tmVerifierActiveStackSymbols_nodup V).filterMap (by
    intro named₁ named₂ choice h₁ h₂
    have hSome₁ : tmVerifierActiveReadChoiceOfNamed? V k named₁ = some choice := by
      simpa using h₁
    have hSome₂ : tmVerifierActiveReadChoiceOfNamed? V k named₂ = some choice := by
      simpa using h₂
    exact tmVerifierActiveReadChoiceOfNamed?_eq_some_injective V k named₁ named₂ choice
      hSome₁ hSome₂)

theorem tmVerifierStackReadChoices_nodup
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (k : tmVerifierStackIndex V) :
    (tmVerifierStackReadChoices V k).Nodup := by
  rw [tmVerifierStackReadChoices]
  constructor
  · intro choice hchoice hEq
    cases hEq
    unfold tmVerifierActiveReadChoices at hchoice
    rcases List.mem_filterMap.mp hchoice with ⟨named, _hNamed, hSome⟩
    unfold tmVerifierActiveReadChoiceOfNamed? at hSome
    split at hSome <;> simp at hSome
  · exact tmVerifierActiveReadChoices_nodup V k

theorem tmVerifierStackReadChoiceLiteralsAt_nodup
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) :
    (tmVerifierStackReadChoiceLiteralsAt V t k cell).Nodup := by
  rw [tmVerifierStackReadChoiceLiteralsAt]
  exact (tmVerifierStackReadChoices_nodup V k).map_on (by
    intro choice₁ h₁ choice₂ h₂ hAtom
    exact tmVerifierStackReadChoice_atomAt_injective_of_mem V t cell k choice₁ choice₂
      h₁ h₂ hAtom)

/--
Unified assignment for the current completeness slice.

Control variables are interpreted by the run-indexed exact-one assignment;
all non-control variables default to true, which satisfies positive stack
boundary unit clauses without affecting control-domain at-most-one clauses.
-/
noncomputable def tmVerifierControlBoundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) : Assignment :=
  by
    classical
    exact fun var =>
      if ∃ t label, var = (tmVerifierLabelAtom V t label).var then
        tmVerifierControlRunAssignment V p var
      else if ∃ t state, var = (tmVerifierStateAtom V t state).var then
        tmVerifierControlRunAssignment V p var
      else
        true

theorem tmVerifierLabelAtom_eval_controlBoundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (label : Option (tmVerifierTM V).Λ) :
    (tmVerifierLabelAtom V t label).eval (tmVerifierControlBoundaryAssignment V p) =
      (tmVerifierLabelAtom V t label).eval (tmVerifierControlRunAssignment V p) := by
  classical
  change tmVerifierControlBoundaryAssignment V p (tmVerifierLabelAtom V t label).var =
    tmVerifierControlRunAssignment V p (tmVerifierLabelAtom V t label).var
  have hLabel : ∃ u label', (tmVerifierLabelAtom V t label).var =
      (tmVerifierLabelAtom V u label').var := ⟨t, label, rfl⟩
  simp [tmVerifierControlBoundaryAssignment, hLabel]

theorem tmVerifierStateAtom_eval_controlBoundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (state : (tmVerifierTM V).σ) :
    (tmVerifierStateAtom V t state).eval (tmVerifierControlBoundaryAssignment V p) =
      (tmVerifierStateAtom V t state).eval (tmVerifierControlRunAssignment V p) := by
  classical
  change tmVerifierControlBoundaryAssignment V p (tmVerifierStateAtom V t state).var =
    tmVerifierControlRunAssignment V p (tmVerifierStateAtom V t state).var
  have hNoLabel : ¬ ∃ u label, (tmVerifierStateAtom V t state).var =
      (tmVerifierLabelAtom V u label).var := by
    rintro ⟨u, label, h⟩
    exact tmVerifierStateAtom_var_ne_labelAtom_var V t u state label h
  have hState : ∃ u state', (tmVerifierStateAtom V t state).var =
      (tmVerifierStateAtom V u state').var := ⟨t, state, rfl⟩
  simp [tmVerifierControlBoundaryAssignment, hNoLabel, hState]

theorem tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (label : Option (tmVerifierTM V).Λ) :
    (tmVerifierLabelAtom V t label).eval (tmVerifierControlBoundaryAssignment V p) = true ↔
      label = (tmVerifierRunCfgAt V p t).l := by
  rw [tmVerifierLabelAtom_eval_controlBoundaryAssignment,
    tmVerifierLabelAtom_eval_controlRunAssignment_iff]

theorem tmVerifierStateAtom_eval_controlBoundaryAssignment_iff
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (state : (tmVerifierTM V).σ) :
    (tmVerifierStateAtom V t state).eval (tmVerifierControlBoundaryAssignment V p) = true ↔
      state = (tmVerifierRunCfgAt V p t).var := by
  rw [tmVerifierStateAtom_eval_controlBoundaryAssignment,
    tmVerifierStateAtom_eval_controlRunAssignment_iff]

theorem tmVerifierStackSymbolAtom_eval_controlBoundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (cell payload : Nat) :
    (tmVerifierStackSymbolAtom V t k cell payload).eval
      (tmVerifierControlBoundaryAssignment V p) = true := by
  classical
  change tmVerifierControlBoundaryAssignment V p
    (tmVerifierStackSymbolAtom V t k cell payload).var = true
  have hNoLabel : ¬ ∃ u label, (tmVerifierStackSymbolAtom V t k cell payload).var =
      (tmVerifierLabelAtom V u label).var := by
    rintro ⟨u, label, h⟩
    exact tmVerifierStackSymbolAtom_var_ne_labelAtom_var V t u k cell payload label h
  have hNoState : ¬ ∃ u state, (tmVerifierStackSymbolAtom V t k cell payload).var =
      (tmVerifierStateAtom V u state).var := by
    rintro ⟨u, state, h⟩
    exact tmVerifierStackSymbolAtom_var_ne_stateAtom_var V t u k cell payload state h
  simp [tmVerifierControlBoundaryAssignment, hNoLabel, hNoState]

theorem tmVerifierStackEmptyAtom_eval_controlBoundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) :
    (tmVerifierStackEmptyAtom V t k cell).eval
      (tmVerifierControlBoundaryAssignment V p) = true := by
  classical
  change tmVerifierControlBoundaryAssignment V p
    (tmVerifierStackEmptyAtom V t k cell).var = true
  have hNoLabel : ¬ ∃ u label, (tmVerifierStackEmptyAtom V t k cell).var =
      (tmVerifierLabelAtom V u label).var := by
    rintro ⟨u, label, h⟩
    exact tmVerifierStackEmptyAtom_var_ne_labelAtom_var V t u k cell label h
  have hNoState : ¬ ∃ u state, (tmVerifierStackEmptyAtom V t k cell).var =
      (tmVerifierStateAtom V u state).var := by
    rintro ⟨u, state, h⟩
    exact tmVerifierStackEmptyAtom_var_ne_stateAtom_var V t u k cell state h
  simp [tmVerifierControlBoundaryAssignment, hNoLabel, hNoState]

theorem tmVerifierInputStackSymbolAtom_eval_controlBoundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t cell : Nat) (s : (tmVerifierTM V).Γ (tmVerifierTM V).k₀) :
    (tmVerifierInputStackSymbolAtom V t cell s).eval
      (tmVerifierControlBoundaryAssignment V p) = true := by
  simp [tmVerifierInputStackSymbolAtom,
    tmVerifierStackSymbolAtom_eval_controlBoundaryAssignment]

theorem tmVerifierOutputStackSymbolAtom_eval_controlBoundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t cell : Nat) (s : (tmVerifierTM V).Γ (tmVerifierTM V).k₁) :
    (tmVerifierOutputStackSymbolAtom V t cell s).eval
      (tmVerifierControlBoundaryAssignment V p) = true := by
  simp [tmVerifierOutputStackSymbolAtom,
    tmVerifierStackSymbolAtom_eval_controlBoundaryAssignment]

end SAT
end ComplexityReduction
