/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.List.Basic

/-!
Basic many-sorted finite relational carrier for normalized reduction schemas.

The executable core is deliberately numeric. Human-readable sort, relation,
and role names belong to the explicit `Legacy.Metadata` compatibility leaf,
rather than kernel-facing data.
-/

namespace ComplexityReduction

abbrev SortId := Nat
abbrev RelId := Nat
abbrev ObjId := Nat
abbrev RoleId := Nat

/-- Signature of a finite relation, as a list of argument sort identifiers. -/
structure RelSig where
  arity : List SortId
  deriving DecidableEq, Repr

/-- A tuple fits a relation arity when its length and per-position bounds agree. -/
def TupleFits
    (sortSize : SortId → Option Nat)
    (arity : List SortId)
    (tuple : List ObjId) : Prop :=
  tuple.length = arity.length ∧
    ∀ (k : Nat) (s : SortId) (x : ObjId),
      arity[k]? = some s →
      tuple[k]? = some x →
      ∃ n, sortSize s = some n ∧ x < n

/-- Universal many-sorted finite relational carrier. -/
structure UniversalRelIR where
  sortSizes : List Nat
  relSigs : List RelSig
  relTuples : List (List (List ObjId))
  deriving Repr

namespace UniversalRelIR

/--
Architectural placement of the legacy universal carrier.

New typed schemas are authored through `V2.RelInstance`; this core deliberately
does not import that layer.  `UniversalRelIR` remains the compatible erased and
interchange representation for legacy views and adapters.
-/
inductive ArchitectureRole where
  | erasedInterchange
  deriving DecidableEq, Repr

/-- `UniversalRelIR` is retained as an erased/interchange backend, not a new-route authoring API. -/
def architectureRole : ArchitectureRole :=
  .erasedInterchange

theorem architectureRole_is_erasedInterchange :
    architectureRole = .erasedInterchange :=
  rfl

def numSorts (U : UniversalRelIR) : Nat :=
  U.sortSizes.length

def numRels (U : UniversalRelIR) : Nat :=
  U.relSigs.length

def sortSize? (U : UniversalRelIR) (s : SortId) : Option Nat :=
  U.sortSizes[s]?

def relSig? (U : UniversalRelIR) (r : RelId) : Option RelSig :=
  U.relSigs[r]?

def tuples? (U : UniversalRelIR) (r : RelId) : Option (List (List ObjId)) :=
  U.relTuples[r]?

def SortWF (U : UniversalRelIR) (s : SortId) : Prop :=
  s < U.numSorts

def ObjWF (U : UniversalRelIR) (s : SortId) (x : ObjId) : Prop :=
  ∃ n, U.sortSize? s = some n ∧ x < n

def TupleWF (U : UniversalRelIR) (sig : RelSig) (t : List ObjId) : Prop :=
  TupleFits U.sortSize? sig.arity t

def RelTupleWF (U : UniversalRelIR) (r : RelId) (t : List ObjId) : Prop :=
  ∃ sig, U.relSig? r = some sig ∧ U.TupleWF sig t

def WellFormed (U : UniversalRelIR) : Prop :=
  U.relTuples.length = U.relSigs.length ∧
    ∀ r ts sig, U.relSig? r = some sig → U.tuples? r = some ts →
      ∀ t ∈ ts, U.TupleWF sig t

def RelHolds (U : UniversalRelIR) (r : RelId) (t : List ObjId) : Prop :=
  ∃ ts, U.tuples? r = some ts ∧ t ∈ ts

def RelHoldsBool (U : UniversalRelIR) (r : RelId) (t : List ObjId) : Bool :=
  match U.tuples? r with
  | some ts => t ∈ ts
  | none => false

end UniversalRelIR

end ComplexityReduction
