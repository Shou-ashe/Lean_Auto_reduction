/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Encoding.StandardInstances
import ComplexityReduction.Program.Primitive

/-!
Canonical type-indexed syntax for V2 polynomial-time programs.

Every endpoint is an exact `LawfulEncodedType`, rather than merely its Lean
carrier.  The structural constructors use only the canonical standard product
presentation, while domain-specific computation enters the language only
through a `Primitive` carrying its direct-TM witness.
-/

namespace ComplexityReduction
namespace Program

open Encoding

/--
The explicit growth data required by the restricted structural list fold.

The step is an exact direct-TM-backed `Primitive`; `initialBound` and
`stepGrowth` are precisely the natural-number inequalities consumed by
`TMPolyTimeMap.list_foldl_typed_growth_bounded`.  This is a shared program
constructor input, not a route-level proposition certificate.
-/
structure BoundedFold (element accumulator : LawfulEncodedType) where
  /-- The direct-TM-backed accumulator update. -/
  step : Primitive (StandardInstances.prod accumulator element) accumulator
  /-- The fixed initial accumulator. -/
  init : accumulator.Carrier
  /-- A polynomial bound for the initial accumulator encoding length. -/
  base : Polynomial Nat
  /-- The allowed polynomial encoding-length growth per input element. -/
  grow : Polynomial Nat
  /-- The initial accumulator obeys the declared natural-valued size bound. -/
  initialBound : ∀ source : List element.Carrier,
    accumulator.encodedType.inputSize init ≤
      base.eval ((StandardInstances.list element).encodedType.inputSize source)
  /-- One primitive step obeys the declared natural-valued growth bound. -/
  stepGrowth : ∀ (source : List element.Carrier) (current : accumulator.Carrier)
      (next : element.Carrier),
    element.encodedType.inputSize next ≤
        (StandardInstances.list element).encodedType.inputSize source →
      accumulator.encodedType.inputSize (step.run (current, next)) ≤
        accumulator.encodedType.inputSize current +
          grow.eval ((StandardInstances.list element).encodedType.inputSize source)

/--
The MVP syntax of computations between exact lawful presentations.

This syntax admits no arbitrary function constructor.  In particular, an
`atom` must be a canonical `Primitive`, whose executable and direct-TM
evidence are already indexed by the same source and target presentations.
-/
inductive PolyProg : LawfulEncodedType → LawfulEncodedType → Type 2 where
  /-- The identity program at one exact representation. -/
  | id (presentation : LawfulEncodedType) : PolyProg presentation presentation
  /-- Sequential composition of endpoint-compatible programs. -/
  | comp {source middle target : LawfulEncodedType} :
      PolyProg middle target → PolyProg source middle → PolyProg source target
  /-- A constant output at an exact target representation. -/
  | const (source target : LawfulEncodedType) (value : target.Carrier) : PolyProg source target
  /-- First projection from the canonical product representation. -/
  | fst (left right : LawfulEncodedType) :
      PolyProg (StandardInstances.prod left right) left
  /-- Second projection from the canonical product representation. -/
  | snd (left right : LawfulEncodedType) :
      PolyProg (StandardInstances.prod left right) right
  /-- Pair two programs with the same exact source representation. -/
  | pair {source left right : LawfulEncodedType} :
      PolyProg source left → PolyProg source right →
        PolyProg source (StandardInstances.prod left right)
  /-- Inject into the left branch of the canonical sum representation. -/
  | inl (left right : LawfulEncodedType) : PolyProg left (StandardInstances.sum left right)
  /-- Inject into the right branch of the canonical sum representation. -/
  | inr (left right : LawfulEncodedType) : PolyProg right (StandardInstances.sum left right)
  /-- Dispatch a canonical sum representation to endpoint-compatible branch programs. -/
  | sumCase {left right target : LawfulEncodedType} :
      PolyProg left target → PolyProg right target →
        PolyProg (StandardInstances.sum left right) target
  /-- Map a program over the canonical encoded-list representation. -/
  | listMap {source target : LawfulEncodedType} :
      PolyProg source target →
        PolyProg (StandardInstances.list source) (StandardInstances.list target)
  /-- Append a pair of canonical encoded lists. -/
  | listAppend (element : LawfulEncodedType) :
      PolyProg
        (StandardInstances.prod (StandardInstances.list element) (StandardInstances.list element))
        (StandardInstances.list element)
  /-- Fold a list using only direct-TM-backed step data with explicit growth bounds. -/
  | boundedFold {element accumulator : LawfulEncodedType} :
      BoundedFold element accumulator → PolyProg (StandardInstances.list element) accumulator
  /-- Embed exactly a direct-TM-backed V2 primitive. -/
  | atom {source target : LawfulEncodedType} : Primitive source target → PolyProg source target

end Program
end ComplexityReduction
