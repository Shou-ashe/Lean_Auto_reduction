/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import ComplexityReduction.Legacy.ComplexityReduction.CSP.FiniteDomain.LanguageBounds
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.LocalPredicateFamilyCSP

/-!
Finite alphabet and local-window metadata for Cook-Levin predicate families.

The existing `TableauCSP.LocalPredicateFamily` compiler turns finite local
tableau predicates into a finite-domain CSP formula.  This module adds the
syntactic metadata that generated reductions need when assembling Cook-Levin
style local checks: finite state/symbol alphabets, local atom windows, maximum
arity, formula length, and conservative variable-support bounds.
-/

namespace ComplexityReduction
namespace SAT
namespace CookLevin
namespace TableauCSP

open ComplexityReduction.CSP.FiniteDomain

/-- Finite state/symbol alphabet metadata for one bounded verifier machine. -/
structure FiniteAlphabetDescriptor where
  machine : BoundedMachineSyntax
  timeBound : Nat
  cellBound : Nat
  payloadBound : Nat
  notes : List String := []

namespace FiniteAlphabetDescriptor

/-- The finite list of machine states, for planner-side enumeration metadata. -/
noncomputable def stateList (A : FiniteAlphabetDescriptor) : List A.machine.State := by
  classical
  exact (Finset.univ : Finset A.machine.State).toList

/-- The finite list of tape symbols, for planner-side enumeration metadata. -/
noncomputable def symbolList (A : FiniteAlphabetDescriptor) : List A.machine.Symbol := by
  classical
  exact (Finset.univ : Finset A.machine.Symbol).toList

/-- Number of machine states in the finite alphabet descriptor. -/
noncomputable def stateCount (A : FiniteAlphabetDescriptor) : Nat :=
  Fintype.card A.machine.State

/-- Number of tape symbols in the finite alphabet descriptor. -/
noncomputable def symbolCount (A : FiniteAlphabetDescriptor) : Nat :=
  Fintype.card A.machine.Symbol

@[simp]
theorem mem_stateList (A : FiniteAlphabetDescriptor) (q : A.machine.State) :
    q ∈ A.stateList := by
  classical
  simp [stateList]

@[simp]
theorem mem_symbolList (A : FiniteAlphabetDescriptor) (s : A.machine.Symbol) :
    s ∈ A.symbolList := by
  classical
  simp [symbolList]

@[simp]
theorem stateList_length (A : FiniteAlphabetDescriptor) :
    A.stateList.length = A.stateCount := by
  classical
  simp [stateList, stateCount]

@[simp]
theorem symbolList_length (A : FiniteAlphabetDescriptor) :
    A.symbolList.length = A.symbolCount := by
  classical
  simp [symbolList, symbolCount]

end FiniteAlphabetDescriptor

/-- A tableau atom reference is within the supplied syntactic tableau bounds. -/
def RefWithinBounds (timeBound cellBound payloadBound : Nat)
    (ref : TableauAtomRef) : Prop :=
  ref.time < timeBound ∧ ref.cell < cellBound ∧ ref.payload < payloadBound

/-- A local Cook-Levin window with concrete tableau-atom references. -/
structure LocalWindowDescriptor where
  name : String
  predicate : LocalPredicate
  refs : Fin predicate.arity → TableauAtomRef
  timeBound : Nat
  cellBound : Nat
  payloadBound : Nat
  notes : List String := []

namespace LocalWindowDescriptor

/-- SAT/CSP variables read by the local window. -/
def atomScope (W : LocalWindowDescriptor) : Fin W.predicate.arity → Nat :=
  W.predicate.atomScope W.refs

/-- Local predicate block obtained by forgetting the atom-reference metadata. -/
def block (W : LocalWindowDescriptor) : LocalPredicateBlock where
  predicate := W.predicate
  scope := W.atomScope

/-- Singleton finite-domain CSP formula for the local window. -/
def formula (W : LocalWindowDescriptor) : Formula W.predicate.language :=
  W.predicate.formulaOfRefs W.refs

/-- Every atom reference in the local window respects the stored bounds. -/
def ReferencesWithinBounds (W : LocalWindowDescriptor) : Prop :=
  ∀ i : Fin W.predicate.arity,
    RefWithinBounds W.timeBound W.cellBound W.payloadBound (W.refs i)

@[simp]
theorem block_satisfies_iff (W : LocalWindowDescriptor)
    (a : CSP.FiniteDomain.Assignment Bool) :
    W.block.Satisfies a ↔
      W.predicate.accepts (fun i => a ((W.refs i).var)) := by
  rfl

theorem formula_satisfies_iff (W : LocalWindowDescriptor)
    (a : CSP.FiniteDomain.Assignment Bool) :
    Formula.Satisfies W.formula a ↔
      W.predicate.accepts (fun i => a ((W.refs i).var)) := by
  simpa [formula] using W.predicate.formulaOfRefs_satisfies_iff W.refs a

theorem ref_time_lt_of_referencesWithinBounds (W : LocalWindowDescriptor)
    (h : W.ReferencesWithinBounds) (i : Fin W.predicate.arity) :
    (W.refs i).time < W.timeBound :=
  (h i).1

theorem ref_cell_lt_of_referencesWithinBounds (W : LocalWindowDescriptor)
    (h : W.ReferencesWithinBounds) (i : Fin W.predicate.arity) :
    (W.refs i).cell < W.cellBound :=
  (h i).2.1

theorem ref_payload_lt_of_referencesWithinBounds (W : LocalWindowDescriptor)
    (h : W.ReferencesWithinBounds) (i : Fin W.predicate.arity) :
    (W.refs i).payload < W.payloadBound :=
  (h i).2.2

end LocalWindowDescriptor

namespace LocalPredicateFamily

/-- Maximum relation arity in the finite-domain language generated by a predicate family. -/
noncomputable def maxArity (F : LocalPredicateFamily) : Nat :=
  F.language.maxArity

/-- Each local block has arity at most the family maximum arity. -/
theorem block_arity_le_maxArity (F : LocalPredicateFamily)
    (i : Fin F.blocks.length) :
    (F.blocks.get i).predicate.arity ≤ F.maxArity := by
  simpa [maxArity, language, LocalPredicate.rel] using
    F.language.arity_le_maxArity i

/-- The finite support of the family formula as a list. -/
noncomputable def supportList (F : LocalPredicateFamily) : List Nat :=
  (FiniteSupport.formulaVars F.formula).toList

@[simp]
theorem mem_supportList (F : LocalPredicateFamily) (x : Nat) :
    x ∈ F.supportList ↔ x ∈ FiniteSupport.formulaVars F.formula := by
  classical
  simp [supportList]

/-- The indexed constraint for a family block appears in the family formula. -/
theorem constraint_mem_formula (F : LocalPredicateFamily)
    (i : Fin F.blocks.length) :
    F.constraint i ∈ F.formula :=
  List.mem_ofFn.mpr ⟨i, rfl⟩

/-- Every scoped variable of a local predicate block appears in formula support. -/
theorem scope_mem_formulaVars (F : LocalPredicateFamily)
    (i : Fin F.blocks.length) (j : Fin (F.blocks.get i).predicate.arity) :
    (F.blocks.get i).scope j ∈ FiniteSupport.formulaVars F.formula := by
  have h :=
    FiniteSupport.var_mem_formulaVars_of_constraint_mem
      (φ := F.formula) (c := F.constraint i) (F.constraint_mem_formula i) j
  simpa [constraint] using h

/-- Every scoped variable of a local predicate block appears in the support list. -/
theorem scope_mem_supportList (F : LocalPredicateFamily)
    (i : Fin F.blocks.length) (j : Fin (F.blocks.get i).predicate.arity) :
    (F.blocks.get i).scope j ∈ F.supportList :=
  (F.mem_supportList ((F.blocks.get i).scope j)).2 (F.scope_mem_formulaVars i j)

/-- Every scoped variable is below the finite-support variable bound. -/
theorem scope_lt_formulaVarBound (F : LocalPredicateFamily)
    (i : Fin F.blocks.length) (j : Fin (F.blocks.get i).predicate.arity) :
    (F.blocks.get i).scope j < FiniteSupport.formulaVarBound F.formula := by
  have h :=
    FiniteSupport.constraint_var_lt_formulaVarBound_of_mem
      (φ := F.formula) (c := F.constraint i) (F.constraint_mem_formula i) j
  simpa [constraint] using h

end LocalPredicateFamily

/-- The top-level family compiler emits one constraint per local predicate block. -/
theorem formulaOfPredicateFamily_length (F : LocalPredicateFamily) :
    (formulaOfPredicateFamily F).length = F.blocks.length := by
  change F.formula.length = F.blocks.length
  exact F.formula_length

/-- Support-list wrapper for the top-level family compiler. -/
noncomputable def supportListOfPredicateFamily (F : LocalPredicateFamily) : List Nat :=
  F.supportList

theorem mem_supportListOfPredicateFamily (F : LocalPredicateFamily) (x : Nat) :
    x ∈ supportListOfPredicateFamily F ↔
      x ∈ FiniteSupport.formulaVars (formulaOfPredicateFamily F) := by
  classical
  simp [supportListOfPredicateFamily, LocalPredicateFamily.supportList,
    formulaOfPredicateFamily]

/-- Top-level variable-bound lemma for variables in indexed local predicate blocks. -/
theorem formulaOfPredicateFamily_scope_lt_formulaVarBound (F : LocalPredicateFamily)
    (i : Fin F.blocks.length) (j : Fin (F.blocks.get i).predicate.arity) :
    (F.blocks.get i).scope j <
      FiniteSupport.formulaVarBound (formulaOfPredicateFamily F) := by
  simpa [formulaOfPredicateFamily] using F.scope_lt_formulaVarBound i j

end TableauCSP
end CookLevin
end SAT
end ComplexityReduction
