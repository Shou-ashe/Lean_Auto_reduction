/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMActiveSymbols

/-!
Transition-window surfaces for the future standard-TM Cook-Levin tableau.

This slice is intentionally a surface, not the finished Cook-Levin theorem.  It
recurses through `TM2.Stmt`, records finite read choices for `peek` and `pop`
from the active stack-symbol boundary, and emits guarded control clauses that
force the next label/state selected by one local execution window.

The full stack-update/frame correctness theorem is still separate: `push` is
recorded as a raw pushed symbol, while `peek` and `pop` consume only the already
audited finite active-symbol choices.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Statement and read-choice atoms -/

/-- Tableau time coordinate for a micro-step inside one macro time row. -/
def tmVerifierMicroTime (t micro : Nat) : Nat :=
  Nat.pair (t + 2) micro

@[simp]
theorem tmVerifierMicroTime_unpair_second (t micro : Nat) :
    (Nat.unpair (tmVerifierMicroTime t micro)).2 = micro := by
  simp [tmVerifierMicroTime, Nat.unpair_pair]

@[simp]
theorem tmVerifierMicroTime_ne_macro (t micro : Nat) :
    tmVerifierMicroTime t micro ≠ t := by
  intro h
  have hle : t + 2 ≤ tmVerifierMicroTime t micro := by
    simpa [tmVerifierMicroTime] using Nat.left_le_pair (t + 2) micro
  omega

@[simp]
theorem tmVerifierMicroTime_ne_macro_succ (t micro : Nat) :
    tmVerifierMicroTime t micro ≠ t + 1 := by
  intro h
  have hle : t + 2 ≤ tmVerifierMicroTime t micro := by
    simpa [tmVerifierMicroTime] using Nat.left_le_pair (t + 2) micro
  omega

/-- Tags for the `TM2.Stmt` constructors encountered while building a window. -/
inductive TMVerifierStmtTag where
  | push
  | peek
  | pop
  | load
  | branchTrue
  | branchFalse
  | goto
  | halt
deriving DecidableEq, Repr

namespace TMVerifierStmtTag

/-- Stable numeric code for statement-constructor tags. -/
def code : TMVerifierStmtTag → Nat
  | push => 0
  | peek => 1
  | pop => 2
  | load => 3
  | branchTrue => 4
  | branchFalse => 5
  | goto => 6
  | halt => 7

theorem code_injective : Function.Injective code := by
  intro a b h
  cases a <;> cases b <;> simp [code] at h ⊢

end TMVerifierStmtTag

/-- Auxiliary atom recording that a statement-constructor tag appears in a window. -/
noncomputable def tmVerifierStmtTagAtom {L : EncodedDecisionProblem}
    (_V : TMVerifier L) (t : Nat) (tag : TMVerifierStmtTag) : Literal :=
  tmVerifierTableauAtom TMVerifierTableauVarKind.aux t 0 0 (Nat.pair 0 tag.code)

/-- Negative auxiliary atom for a statement-constructor tag. -/
noncomputable def negTMVerifierStmtTagAtom {L : EncodedDecisionProblem}
    (_V : TMVerifier L) (t : Nat) (tag : TMVerifierStmtTag) : Literal :=
  negTMVerifierTableauAtom TMVerifierTableauVarKind.aux t 0 0 (Nat.pair 0 tag.code)

/--
A finite choice for the top of stack `k`.

`empty` represents `List.head? = none`; `symbol payload s` represents a named
active symbol at the top cell whose actual stack symbol is `s`.
-/
inductive TMVerifierStackReadChoice {L : EncodedDecisionProblem}
    (V : TMVerifier L) (k : tmVerifierStackIndex V) where
  | empty : TMVerifierStackReadChoice V k
  | symbol : Nat → (tmVerifierTM V).Γ k → TMVerifierStackReadChoice V k

namespace TMVerifierStackReadChoice

/-- The `Option` value passed to mathlib `peek`/`pop` transition functions. -/
def toOption {L : EncodedDecisionProblem} {V : TMVerifier L}
    {k : tmVerifierStackIndex V} :
    TMVerifierStackReadChoice V k → Option ((tmVerifierTM V).Γ k)
  | empty => none
  | symbol _ s => some s

/-- Literal asserting this read choice at the top cell of stack `k`. -/
noncomputable def atomAt {L : EncodedDecisionProblem} {V : TMVerifier L}
    {k : tmVerifierStackIndex V} (t cell : Nat) :
    TMVerifierStackReadChoice V k → Literal
  | empty => tmVerifierStackEmptyAtom V t k cell
  | symbol payload _ => tmVerifierStackSymbolAtom V t k cell payload

end TMVerifierStackReadChoice

/-- Convert one active named symbol to a read choice for stack `k`, when it is on that stack. -/
noncomputable def tmVerifierActiveReadChoiceOfNamed? {L : EncodedDecisionProblem}
    (V : TMVerifier L) (k : tmVerifierStackIndex V)
    (s : TMVerifierNamedStackSymbol V) : Option (TMVerifierStackReadChoice V k) :=
  if h : s.stack = k then
    let sym : (tmVerifierTM V).Γ k := by
      cases h
      exact s.symbol
    some (TMVerifierStackReadChoice.symbol (V := V) (k := k) s.payload sym)
  else
    none

/-- All active nonempty top-symbol choices for stack `k`. -/
noncomputable def tmVerifierActiveReadChoices {L : EncodedDecisionProblem}
    (V : TMVerifier L) (k : tmVerifierStackIndex V) :
    List (TMVerifierStackReadChoice V k) :=
  (tmVerifierActiveStackSymbols V).filterMap (tmVerifierActiveReadChoiceOfNamed? V k)

/-- The finite read-choice list for stack `k`, including the empty-stack case. -/
noncomputable def tmVerifierStackReadChoices {L : EncodedDecisionProblem}
    (V : TMVerifier L) (k : tmVerifierStackIndex V) :
    List (TMVerifierStackReadChoice V k) :=
  TMVerifierStackReadChoice.empty :: tmVerifierActiveReadChoices V k

/-- Literals asserting the finite read-choice domain for one stack top cell. -/
noncomputable def tmVerifierStackReadChoiceLiteralsAt {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) :
    List Literal :=
  (tmVerifierStackReadChoices V k).map fun choice =>
    TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice

/-- Exactly one audited read choice is selected for one stack top cell. -/
noncomputable def tmVerifierStackReadChoiceDomainCNFAt {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) : CNF :=
  CookLevin.exactlyOneCNF (tmVerifierStackReadChoiceLiteralsAt V t k cell)

theorem tmVerifierStackReadChoices_empty_mem {L : EncodedDecisionProblem}
    (V : TMVerifier L) (k : tmVerifierStackIndex V) :
    TMVerifierStackReadChoice.empty ∈ tmVerifierStackReadChoices V k := by
  simp [tmVerifierStackReadChoices]

theorem tmVerifierActiveReadChoice_mem_of_named
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (named : TMVerifierNamedStackSymbol V)
    (hNamed : named ∈ tmVerifierActiveStackSymbols V) :
    TMVerifierStackReadChoice.symbol (V := V) (k := named.stack) named.payload named.symbol ∈
      tmVerifierStackReadChoices V named.stack := by
  rw [tmVerifierStackReadChoices]
  exact List.mem_cons_of_mem _ (by
    rw [tmVerifierActiveReadChoices]
    refine List.mem_filterMap.mpr ⟨named, hNamed, ?_⟩
    unfold tmVerifierActiveReadChoiceOfNamed?
    rw [dif_pos rfl])

theorem tmVerifierActiveStackSymbolPayload_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (k : tmVerifierStackIndex V) (s : (tmVerifierTM V).Γ k)
    (hs : tmVerifierStackSymbolActive V k s) :
    TMVerifierStackReadChoice.symbol (V := V) (k := k)
        (tmVerifierActiveStackSymbolPayload V k s) s ∈
      tmVerifierStackReadChoices V k := by
  classical
  let named := Classical.choose hs
  have hspec :
      named ∈ tmVerifierActiveStackSymbols V ∧ named.stack = k ∧ HEq named.symbol s :=
    Classical.choose_spec hs
  have hmem := tmVerifierActiveReadChoice_mem_of_named V named hspec.1
  unfold tmVerifierActiveStackSymbolPayload
  rw [dif_pos hs]
  change
    TMVerifierStackReadChoice.symbol (V := V) (k := k) named.payload s ∈
      tmVerifierStackReadChoices V k
  rcases named with ⟨namedStack, namedPayload, namedSymbol⟩
  dsimp at hspec hmem ⊢
  have hStack : namedStack = k := hspec.2.1
  cases hStack
  have hSymbol : namedSymbol = s := by
    simpa using hspec.2.2
  subst s
  exact hmem

theorem tmVerifierStackReadChoiceDomainCNFAt_satisfies_has_atom
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat)
    (k : tmVerifierStackIndex V) (cell : Nat) (a : Assignment) :
    CNF.Satisfies (tmVerifierStackReadChoiceDomainCNFAt V t k cell) a →
      ∃ l ∈ tmVerifierStackReadChoiceLiteralsAt V t k cell, l.eval a = true := by
  intro h
  let atoms := tmVerifierStackReadChoiceLiteralsAt V t k cell
  have hsplit :
      CNF.Satisfies (CookLevin.atLeastOneCNF atoms) a ∧
        CNF.Satisfies (CookLevin.atMostOneCNF atoms) a := by
    simpa [tmVerifierStackReadChoiceDomainCNFAt, CookLevin.exactlyOneCNF, atoms]
      using (CNF.satisfies_append (CookLevin.atLeastOneCNF atoms)
        (CookLevin.atMostOneCNF atoms) a).1 h
  exact (CookLevin.atLeastOneCNF_satisfies atoms a).1 hsplit.1

/-! ### Statement windows -/

/-- Stack actions recorded while recursively evaluating one `TM2.Stmt` window. -/
inductive TMVerifierStackAction {L : EncodedDecisionProblem} (V : TMVerifier L) where
  | push : TMVerifierStackSymbol V → TMVerifierStackAction V
  | peek : (k : tmVerifierStackIndex V) → TMVerifierStackReadChoice V k →
      TMVerifierStackAction V
  | pop : (k : tmVerifierStackIndex V) → TMVerifierStackReadChoice V k →
      TMVerifierStackAction V
  | load : TMVerifierStackAction V
  | branch : TMVerifierStmtTag → TMVerifierStackAction V

/-- The read choice recorded by a `peek`/`pop` action is from the finite choice domain. -/
def TMVerifierStackActionReadChoiceMem {L : EncodedDecisionProblem} {V : TMVerifier L} :
    TMVerifierStackAction V → Prop
  | TMVerifierStackAction.peek k choice => choice ∈ tmVerifierStackReadChoices V k
  | TMVerifierStackAction.pop k choice => choice ∈ tmVerifierStackReadChoices V k
  | _ => True

/-- A recorded `push` action names a symbol collected from the finite control graph. -/
def TMVerifierStackActionPushSymbolMem {L : EncodedDecisionProblem} {V : TMVerifier L} :
    TMVerifierStackAction V → Prop
  | TMVerifierStackAction.push raw => raw ∈ tmVerifierControlPushSymbols V
  | _ => True

/-- The micro-row read guard contributed by one indexed action, if it reads a stack head. -/
noncomputable def TMVerifierStackAction.readGuardAt {L : EncodedDecisionProblem}
    {V : TMVerifier L} (t actionIdx : Nat) : TMVerifierStackAction V → List Literal
  | TMVerifierStackAction.peek k choice =>
      [TMVerifierStackReadChoice.atomAt (V := V) (k := k)
        (tmVerifierMicroTime t actionIdx) 0 choice]
  | TMVerifierStackAction.pop k choice =>
      [TMVerifierStackReadChoice.atomAt (V := V) (k := k)
        (tmVerifierMicroTime t actionIdx) 0 choice]
  | _ => []

/-- Micro-row read guards for a list of recorded actions starting at action index `idx`. -/
noncomputable def tmVerifierWindowActionReadGuardsFrom {L : EncodedDecisionProblem}
    {V : TMVerifier L} (t : Nat) (actions : List (TMVerifierStackAction V))
    (idx : Nat) : List Literal :=
  actions.zipIdx idx |>.flatMap fun entry =>
    entry.1.readGuardAt t entry.2

/--
One finite local execution window produced by recursively interpreting a
statement from a fixed current internal state.
-/
structure TMVerifierStmtWindow {L : EncodedDecisionProblem} (V : TMVerifier L) where
  guards : List Literal
  actions : List (TMVerifierStackAction V)
  nextLabel : Option (tmVerifierTM V).Λ
  nextState : (tmVerifierTM V).σ

namespace TMVerifierStmtWindow

/-- Add one SAT guard literal to the front of a window. -/
def consGuard {L : EncodedDecisionProblem} {V : TMVerifier L}
    (g : Literal) (w : TMVerifierStmtWindow V) : TMVerifierStmtWindow V :=
  { w with guards := g :: w.guards }

/-- Add one recorded stack/control action to the front of a window. -/
def consAction {L : EncodedDecisionProblem} {V : TMVerifier L}
    (act : TMVerifierStackAction V) (w : TMVerifierStmtWindow V) :
    TMVerifierStmtWindow V :=
  { w with actions := act :: w.actions }

end TMVerifierStmtWindow

/-- Micro-row read guards for one generated statement window. -/
noncomputable def tmVerifierWindowActionReadGuards {L : EncodedDecisionProblem}
    {V : TMVerifier L} (t : Nat) (w : TMVerifierStmtWindow V) : List Literal :=
  tmVerifierWindowActionReadGuardsFrom t w.actions 0

/--
Finite local windows for recursively executing a `TM2.Stmt` from internal state
`s` at time row `t`.
-/
noncomputable def tmVerifierStmtWindowsAt {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) :
    (tmVerifierTM V).Stmt → (tmVerifierTM V).σ → List (TMVerifierStmtWindow V)
  | Turing.TM2.Stmt.push k f q, s =>
      (tmVerifierStmtWindowsAt V t q s).map fun w =>
        TMVerifierStmtWindow.consAction
          (TMVerifierStackAction.push (V := V) { stack := k, symbol := f s }) w
  | Turing.TM2.Stmt.peek k f q, s =>
      (tmVerifierStackReadChoices V k).flatMap fun choice =>
        (tmVerifierStmtWindowsAt V t q (f s choice.toOption)).map fun w =>
          TMVerifierStmtWindow.consAction (TMVerifierStackAction.peek (V := V) k choice)
            (TMVerifierStmtWindow.consGuard
              (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice) w)
  | Turing.TM2.Stmt.pop k f q, s =>
      (tmVerifierStackReadChoices V k).flatMap fun choice =>
        (tmVerifierStmtWindowsAt V t q (f s choice.toOption)).map fun w =>
          TMVerifierStmtWindow.consAction (TMVerifierStackAction.pop (V := V) k choice)
            (TMVerifierStmtWindow.consGuard
              (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice) w)
  | Turing.TM2.Stmt.load f q, s =>
      (tmVerifierStmtWindowsAt V t q (f s)).map fun w =>
        TMVerifierStmtWindow.consAction (TMVerifierStackAction.load (V := V)) w
  | Turing.TM2.Stmt.branch f q₁ q₂, s =>
      if f s then
        (tmVerifierStmtWindowsAt V t q₁ s).map fun w =>
          TMVerifierStmtWindow.consAction
            (TMVerifierStackAction.branch (V := V) TMVerifierStmtTag.branchTrue) w
      else
        (tmVerifierStmtWindowsAt V t q₂ s).map fun w =>
          TMVerifierStmtWindow.consAction
            (TMVerifierStackAction.branch (V := V) TMVerifierStmtTag.branchFalse) w
  | Turing.TM2.Stmt.goto f, s =>
      [{ guards := [], actions := [], nextLabel := some (f s), nextState := s }]
  | Turing.TM2.Stmt.halt, s =>
      [{ guards := [], actions := [], nextLabel := none, nextState := s }]

theorem tmVerifierStmtWindowsAt_actions_readChoiceMem {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) (stmt : (tmVerifierTM V).Stmt)
    (s : (tmVerifierTM V).σ) {w : TMVerifierStmtWindow V}
    (hw : w ∈ tmVerifierStmtWindowsAt V t stmt s) :
    ∀ act ∈ w.actions, TMVerifierStackActionReadChoiceMem (V := V) act := by
  induction stmt generalizing s w with
  | push k f q ih =>
      rcases List.mem_map.mp hw with ⟨w₀, hw₀, rfl⟩
      intro act hact
      simp [TMVerifierStmtWindow.consAction] at hact
      rcases hact with hhead | htail
      · subst act
        simp [TMVerifierStackActionReadChoiceMem]
      · exact ih s hw₀ act htail
  | peek k f q ih =>
      rcases List.mem_flatMap.mp hw with ⟨choice, hchoice, hmem⟩
      rcases List.mem_map.mp hmem with ⟨w₀, hw₀, rfl⟩
      intro act hact
      simp [TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard] at hact
      rcases hact with hhead | htail
      · subst act
        simpa [TMVerifierStackActionReadChoiceMem] using hchoice
      · exact ih (f s choice.toOption) hw₀ act htail
  | pop k f q ih =>
      rcases List.mem_flatMap.mp hw with ⟨choice, hchoice, hmem⟩
      rcases List.mem_map.mp hmem with ⟨w₀, hw₀, rfl⟩
      intro act hact
      simp [TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard] at hact
      rcases hact with hhead | htail
      · subst act
        simpa [TMVerifierStackActionReadChoiceMem] using hchoice
      · exact ih (f s choice.toOption) hw₀ act htail
  | load f q ih =>
      rcases List.mem_map.mp hw with ⟨w₀, hw₀, rfl⟩
      intro act hact
      simp [TMVerifierStmtWindow.consAction] at hact
      rcases hact with hhead | htail
      · subst act
        simp [TMVerifierStackActionReadChoiceMem]
      · exact ih (f s) hw₀ act htail
  | branch f q₁ q₂ ih₁ ih₂ =>
      by_cases hBranch : f s
      · simp [tmVerifierStmtWindowsAt, hBranch] at hw
        rcases hw with ⟨w₀, hw₀, rfl⟩
        intro act hact
        simp [TMVerifierStmtWindow.consAction] at hact
        rcases hact with hhead | htail
        · subst act
          simp [TMVerifierStackActionReadChoiceMem]
        · exact ih₁ s hw₀ act htail
      · simp [tmVerifierStmtWindowsAt, hBranch] at hw
        rcases hw with ⟨w₀, hw₀, rfl⟩
        intro act hact
        simp [TMVerifierStmtWindow.consAction] at hact
        rcases hact with hhead | htail
        · subst act
          simp [TMVerifierStackActionReadChoiceMem]
        · exact ih₂ s hw₀ act htail
  | goto f =>
      simp [tmVerifierStmtWindowsAt] at hw
      subst w
      simp
  | halt =>
      simp [tmVerifierStmtWindowsAt] at hw
      subst w
      simp

theorem tmVerifierStmtWindowsAt_zipIdx_action_readChoiceMem
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat)
    (stmt : (tmVerifierTM V).Stmt) (s : (tmVerifierTM V).σ)
    {w : TMVerifierStmtWindow V}
    (hw : w ∈ tmVerifierStmtWindowsAt V t stmt s)
    (entry : TMVerifierStackAction V × Nat)
    (hentry : entry ∈ w.actions.zipIdx) :
    TMVerifierStackActionReadChoiceMem (V := V) entry.1 := by
  have hAll := tmVerifierStmtWindowsAt_actions_readChoiceMem V t stmt s hw
  have hZip := List.mem_zipIdx hentry
  have hLt : entry.2 < w.actions.length := by
    simpa using hZip.2.1
  have hEq : entry.1 = w.actions[entry.2] := by
    simpa using hZip.2.2
  exact hAll entry.1 (by
    rw [hEq]
    exact List.get_mem w.actions ⟨entry.2, hLt⟩)

theorem tmVerifierStmtWindowsAt_actions_pushSymbolMem_of_stmt
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat)
    (stmt : (tmVerifierTM V).Stmt) (s : (tmVerifierTM V).σ)
    {w : TMVerifierStmtWindow V}
    (hw : w ∈ tmVerifierStmtWindowsAt V t stmt s)
    (hStmt :
      ∀ sym, sym ∈ tmVerifierStmtPushSymbols V stmt →
        sym ∈ tmVerifierControlPushSymbols V) :
    ∀ act ∈ w.actions, TMVerifierStackActionPushSymbolMem (V := V) act := by
  induction stmt generalizing s w with
  | push k f q ih =>
      rcases List.mem_map.mp hw with ⟨w₀, hw₀, rfl⟩
      have hTailStmt :
          ∀ sym, sym ∈ tmVerifierStmtPushSymbols V q →
            sym ∈ tmVerifierControlPushSymbols V := by
        intro sym hsym
        exact hStmt sym (by simp [tmVerifierStmtPushSymbols, hsym])
      intro act hact
      simp [TMVerifierStmtWindow.consAction] at hact
      rcases hact with hhead | htail
      · subst act
        exact hStmt ({ stack := k, symbol := f s } : TMVerifierStackSymbol V)
          (tmVerifierStmtPushSymbols_push_mem V k f q s)
      · exact ih s hw₀ hTailStmt act htail
  | peek k f q ih =>
      rcases List.mem_flatMap.mp hw with ⟨choice, _hchoice, hmem⟩
      rcases List.mem_map.mp hmem with ⟨w₀, hw₀, rfl⟩
      intro act hact
      simp [TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard] at hact
      rcases hact with hhead | htail
      · subst act
        simp [TMVerifierStackActionPushSymbolMem]
      · exact ih (f s choice.toOption) hw₀ (by
          intro sym hsym
          exact hStmt sym (by simpa [tmVerifierStmtPushSymbols] using hsym)) act htail
  | pop k f q ih =>
      rcases List.mem_flatMap.mp hw with ⟨choice, _hchoice, hmem⟩
      rcases List.mem_map.mp hmem with ⟨w₀, hw₀, rfl⟩
      intro act hact
      simp [TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard] at hact
      rcases hact with hhead | htail
      · subst act
        simp [TMVerifierStackActionPushSymbolMem]
      · exact ih (f s choice.toOption) hw₀ (by
          intro sym hsym
          exact hStmt sym (by simpa [tmVerifierStmtPushSymbols] using hsym)) act htail
  | load f q ih =>
      rcases List.mem_map.mp hw with ⟨w₀, hw₀, rfl⟩
      intro act hact
      simp [TMVerifierStmtWindow.consAction] at hact
      rcases hact with hhead | htail
      · subst act
        simp [TMVerifierStackActionPushSymbolMem]
      · exact ih (f s) hw₀ (by
          intro sym hsym
          exact hStmt sym (by simpa [tmVerifierStmtPushSymbols] using hsym)) act htail
  | branch f q₁ q₂ ih₁ ih₂ =>
      by_cases hBranch : f s
      · simp [tmVerifierStmtWindowsAt, hBranch] at hw
        rcases hw with ⟨w₀, hw₀, rfl⟩
        intro act hact
        simp [TMVerifierStmtWindow.consAction] at hact
        rcases hact with hhead | htail
        · subst act
          simp [TMVerifierStackActionPushSymbolMem]
        · exact ih₁ s hw₀ (by
            intro sym hsym
            exact hStmt sym (by simp [tmVerifierStmtPushSymbols, hsym])) act htail
      · simp [tmVerifierStmtWindowsAt, hBranch] at hw
        rcases hw with ⟨w₀, hw₀, rfl⟩
        intro act hact
        simp [TMVerifierStmtWindow.consAction] at hact
        rcases hact with hhead | htail
        · subst act
          simp [TMVerifierStackActionPushSymbolMem]
        · exact ih₂ s hw₀ (by
            intro sym hsym
            exact hStmt sym (by simp [tmVerifierStmtPushSymbols, hsym])) act htail
  | goto f =>
      simp [tmVerifierStmtWindowsAt] at hw
      subst w
      simp
  | halt =>
      simp [tmVerifierStmtWindowsAt] at hw
      subst w
      simp

theorem tmVerifierStmtWindowsAt_zipIdx_action_pushSymbolMem_of_stmt
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat)
    (stmt : (tmVerifierTM V).Stmt) (s : (tmVerifierTM V).σ)
    {w : TMVerifierStmtWindow V}
    (hw : w ∈ tmVerifierStmtWindowsAt V t stmt s)
    (hStmt :
      ∀ sym, sym ∈ tmVerifierStmtPushSymbols V stmt →
        sym ∈ tmVerifierControlPushSymbols V)
    (entry : TMVerifierStackAction V × Nat)
    (hentry : entry ∈ w.actions.zipIdx) :
    TMVerifierStackActionPushSymbolMem (V := V) entry.1 := by
  have hAll :=
    tmVerifierStmtWindowsAt_actions_pushSymbolMem_of_stmt V t stmt s hw hStmt
  have hZip := List.mem_zipIdx hentry
  have hLt : entry.2 < w.actions.length := by
    simpa using hZip.2.1
  have hEq : entry.1 = w.actions[entry.2] := by
    simpa using hZip.2.2
  exact hAll entry.1 (by
    rw [hEq]
    exact List.get_mem w.actions ⟨entry.2, hLt⟩)

theorem tmVerifierStmtWindowsAt_zipIdx_action_pushSymbolMem_of_label
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    {w : TMVerifierStmtWindow V}
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (entry : TMVerifierStackAction V × Nat)
    (hentry : entry ∈ w.actions.zipIdx) :
    TMVerifierStackActionPushSymbolMem (V := V) entry.1 :=
  tmVerifierStmtWindowsAt_zipIdx_action_pushSymbolMem_of_stmt V t ((tmVerifierTM V).m l)
    s hw (fun sym hsym => tmVerifierControlPushSymbols_label_mem V l sym hsym)
    entry hentry

theorem tmVerifierStmtWindowsAt_goto_mem {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) (f : (tmVerifierTM V).σ → (tmVerifierTM V).Λ)
    (s : (tmVerifierTM V).σ) :
    ({ guards := [], actions := [], nextLabel := some (f s), nextState := s } :
      TMVerifierStmtWindow V) ∈
        tmVerifierStmtWindowsAt V t (Turing.TM2.Stmt.goto f) s := by
  simp [tmVerifierStmtWindowsAt]

theorem tmVerifierStmtWindowsAt_halt_mem {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) (s : (tmVerifierTM V).σ) :
    ({ guards := [], actions := [], nextLabel := none, nextState := s } :
      TMVerifierStmtWindow V) ∈
        tmVerifierStmtWindowsAt V t Turing.TM2.Stmt.halt s := by
  simp [tmVerifierStmtWindowsAt]

theorem tmVerifierStmtWindowsAt_push_action_mem {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) (k : tmVerifierStackIndex V)
    (f : (tmVerifierTM V).σ → (tmVerifierTM V).Γ k)
    (q : (tmVerifierTM V).Stmt) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V)
    (h : w ∈ tmVerifierStmtWindowsAt V t q s) :
    TMVerifierStmtWindow.consAction
        (TMVerifierStackAction.push (V := V) { stack := k, symbol := f s }) w ∈
      tmVerifierStmtWindowsAt V t (Turing.TM2.Stmt.push k f q) s := by
  exact List.mem_map.mpr ⟨w, h, rfl⟩

theorem tmVerifierStmtWindowsAt_push_symbol_collected {L : EncodedDecisionProblem}
    (V : TMVerifier L) (k : tmVerifierStackIndex V)
    (f : (tmVerifierTM V).σ → (tmVerifierTM V).Γ k)
    (q : (tmVerifierTM V).Stmt) (s : (tmVerifierTM V).σ) :
    ({ stack := k, symbol := f s } : TMVerifierStackSymbol V) ∈
      tmVerifierStmtPushSymbols V (Turing.TM2.Stmt.push k f q) := by
  exact tmVerifierStmtPushSymbols_push_mem V k f q s

/-! ### Guarded control clauses emitted from windows -/

/-- A single implication clause: all antecedents true force the conclusion literal. -/
def tmVerifierImplicationClause (antecedents : List Literal) (conclusion : Literal) :
    Clause :=
  antecedents.map Clause.negate ++ [conclusion]

theorem tmVerifierImplicationClause_satisfies_of_antecedents
    (antecedents : List Literal) (conclusion : Literal) (a : Assignment) :
    CNF.Satisfies [tmVerifierImplicationClause antecedents conclusion] a →
      (∀ l ∈ antecedents, l.eval a = true) → conclusion.eval a = true := by
  intro h hAntecedents
  have hClause :
      Clause.Satisfies (tmVerifierImplicationClause antecedents conclusion) a := by
    exact h _ (by simp)
  rcases hClause with ⟨lit, hlit, heval⟩
  rcases List.mem_append.mp hlit with hneg | hconcl
  · rcases List.mem_map.mp hneg with ⟨ant, hant, rfl⟩
    have hfalse := (Clause.negate_eval_true_iff ant a).1 heval
    simp [hAntecedents ant hant] at hfalse
  · have hlit : lit = conclusion := by simpa using hconcl
    simpa [hlit] using heval

/-- Antecedent literals for a window starting at label `l` and state `s`. -/
noncomputable def tmVerifierWindowAntecedents {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) (l : (tmVerifierTM V).Λ)
    (s : (tmVerifierTM V).σ) (w : TMVerifierStmtWindow V) : List Literal :=
  [tmVerifierLabelAtom V t (some l), tmVerifierStateAtom V t s] ++
    tmVerifierWindowActionReadGuards t w

/-- Guarded next-label and next-state control clauses for one local window. -/
noncomputable def tmVerifierWindowControlCNFAt {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) (l : (tmVerifierTM V).Λ)
    (s : (tmVerifierTM V).σ) (w : TMVerifierStmtWindow V) : CNF :=
  let antecedents := tmVerifierWindowAntecedents V t l s w
  [ tmVerifierImplicationClause antecedents (tmVerifierLabelAtom V (t + 1) w.nextLabel)
  , tmVerifierImplicationClause antecedents (tmVerifierStateAtom V (t + 1) w.nextState) ]

theorem tmVerifierWindowControlCNFAt_satisfies_next_control
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment) :
    CNF.Satisfies (tmVerifierWindowControlCNFAt V t l s w) a →
      (∀ g ∈ tmVerifierWindowAntecedents V t l s w, g.eval a = true) →
        (tmVerifierLabelAtom V (t + 1) w.nextLabel).eval a = true ∧
          (tmVerifierStateAtom V (t + 1) w.nextState).eval a = true := by
  intro h hAntecedents
  let antecedents := tmVerifierWindowAntecedents V t l s w
  have hLabel :
      CNF.Satisfies
        [tmVerifierImplicationClause antecedents
          (tmVerifierLabelAtom V (t + 1) w.nextLabel)] a := by
    intro c hc
    have hc' :
        c = tmVerifierImplicationClause antecedents
          (tmVerifierLabelAtom V (t + 1) w.nextLabel) := by
      simpa using hc
    subst c
    exact h _ (by simp [tmVerifierWindowControlCNFAt, antecedents])
  have hState :
      CNF.Satisfies
        [tmVerifierImplicationClause antecedents
          (tmVerifierStateAtom V (t + 1) w.nextState)] a := by
    intro c hc
    have hc' :
        c = tmVerifierImplicationClause antecedents
          (tmVerifierStateAtom V (t + 1) w.nextState) := by
      simpa using hc
    subst c
    exact h _ (by simp [tmVerifierWindowControlCNFAt, antecedents])
  constructor
  · exact tmVerifierImplicationClause_satisfies_of_antecedents antecedents
      (tmVerifierLabelAtom V (t + 1) w.nextLabel) a hLabel (by
        simpa [antecedents] using hAntecedents)
  · exact tmVerifierImplicationClause_satisfies_of_antecedents antecedents
      (tmVerifierStateAtom V (t + 1) w.nextState) a hState (by
        simpa [antecedents] using hAntecedents)

/-- All finite labels of the extracted verifier machine. -/
noncomputable def tmVerifierLabelList {L : EncodedDecisionProblem}
    (V : TMVerifier L) : List (tmVerifierTM V).Λ :=
  letI : Fintype (tmVerifierTM V).Λ := (tmVerifierTM V).ΛFin
  letI : DecidableEq (tmVerifierTM V).Λ := Classical.decEq _
  (Finset.univ : Finset (tmVerifierTM V).Λ).toList

/-- All finite internal states of the extracted verifier machine. -/
noncomputable def tmVerifierStateList {L : EncodedDecisionProblem}
    (V : TMVerifier L) : List (tmVerifierTM V).σ :=
  letI : Fintype (tmVerifierTM V).σ := (tmVerifierTM V).σFin
  letI : DecidableEq (tmVerifierTM V).σ := Classical.decEq _
  (Finset.univ : Finset (tmVerifierTM V).σ).toList

/-- All guarded control clauses for one time row of the verifier transition relation. -/
noncomputable def tmVerifierTransitionControlCNFAt {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) : CNF :=
  (tmVerifierLabelList V).flatMap fun l =>
    (tmVerifierStateList V).flatMap fun s =>
      (tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s).flatMap fun w =>
        tmVerifierWindowControlCNFAt V t l s w

end SAT
end ComplexityReduction
