/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.Part1
import ComplexityReduction.Encoding.LawfulEncodedType

/-!
Canonical direct-TM primitives for `ComplexityReduction`.

A `Primitive` is an executable map between two exact lawful presentations together with direct
TM2 polynomial-time evidence for that very executable.  In particular, this layer has no route
metadata, theorem-name lookup, Boolean readiness bit, or promotion from a bare `CostedMap`.
-/

namespace ComplexityReduction
namespace Program

open Encoding

/--
One executable primitive between exact lawful presentations.

The direct-TM witness is dependent on `run`, so an executable map and its machine evidence cannot
be assembled for different functions.  Cost evidence deliberately does not occur here: it may only
be projected later from a program compilation or from an existing `TMBackedCostedMap` adapter.
-/
structure Primitive (source target : LawfulEncodedType) where
  run : source.Carrier → target.Carrier
  tmPolyTime : ComplexityReduction.TMPolyTimeMap source.encodedType target.encodedType run

namespace Primitive

/-- Build a primitive directly from real TM2 polynomial-time evidence for its executable map. -/
def ofTMPolyTime {source target : LawfulEncodedType}
    (run : source.Carrier → target.Carrier)
    (tmPolyTime : ComplexityReduction.TMPolyTimeMap source.encodedType target.encodedType run) :
    Primitive source target where
  run := run
  tmPolyTime := tmPolyTime

/--
Build a direct-TM-backed primitive from an encoder-coherent executable.

The alphabet equivalence and pointwise encoding equation are passed directly
to CR's `TMPolyTimeMap.of_encodingEquiv`; no carrier equality, bare `Equiv`,
or separately supplied cost witness can enter this constructor.
-/
def ofEncodingEquiv {source target : LawfulEncodedType}
    (run : source.Carrier → target.Carrier)
    (alphabetEquiv : source.encodedType.Symbol ≃ target.encodedType.Symbol)
    (encodeCoherence : ∀ input,
      target.encodedType.encode (run input) =
        (source.encodedType.encode input).map alphabetEquiv) :
    Primitive source target :=
  ofTMPolyTime run <|
    ComplexityReduction.TMPolyTimeMap.of_encodingEquiv
      source.encodedType target.encodedType run alphabetEquiv encodeCoherence

/-- The direct-TM evidence of a primitive certifies exactly its executable map. -/
theorem tmPolyTime_run {source target : LawfulEncodedType} (primitive : Primitive source target) :
    ComplexityReduction.TMPolyTimeMap source.encodedType target.encodedType primitive.run :=
  primitive.tmPolyTime

/-- A primitive is determined at fixed presentations by its executable map. -/
@[ext]
theorem ext {source target : LawfulEncodedType} (first second : Primitive source target)
    (runEquality : first.run = second.run) : first = second := by
  cases first
  cases second
  cases runEquality
  rfl

@[simp]
theorem run_ofTMPolyTime {source target : LawfulEncodedType}
    (run : source.Carrier → target.Carrier)
    (tmPolyTime : ComplexityReduction.TMPolyTimeMap source.encodedType target.encodedType run) :
    (ofTMPolyTime run tmPolyTime).run = run :=
  rfl

/-- The direct-TM field of the constructor is exactly the evidence supplied for that executable. -/
theorem tmPolyTime_ofTMPolyTime {source target : LawfulEncodedType}
    (run : source.Carrier → target.Carrier)
    (tmPolyTime : ComplexityReduction.TMPolyTimeMap source.encodedType target.encodedType run) :
    (ofTMPolyTime run tmPolyTime).tmPolyTime = tmPolyTime :=
  rfl

/-- The encoder-coherent constructor retains exactly its supplied executable. -/
@[simp]
theorem run_ofEncodingEquiv {source target : LawfulEncodedType}
    (run : source.Carrier → target.Carrier)
    (alphabetEquiv : source.encodedType.Symbol ≃ target.encodedType.Symbol)
    (encodeCoherence : ∀ input,
      target.encodedType.encode (run input) =
        (source.encodedType.encode input).map alphabetEquiv) :
    (ofEncodingEquiv run alphabetEquiv encodeCoherence).run = run :=
  rfl

/-- The encoder-coherent primitive obtains direct-TM evidence only from CR's trusted bridge. -/
@[simp]
theorem tmPolyTime_ofEncodingEquiv {source target : LawfulEncodedType}
    (run : source.Carrier → target.Carrier)
    (alphabetEquiv : source.encodedType.Symbol ≃ target.encodedType.Symbol)
    (encodeCoherence : ∀ input,
      target.encodedType.encode (run input) =
        (source.encodedType.encode input).map alphabetEquiv) :
    (ofEncodingEquiv run alphabetEquiv encodeCoherence).tmPolyTime =
      ComplexityReduction.TMPolyTimeMap.of_encodingEquiv
        source.encodedType target.encodedType run alphabetEquiv encodeCoherence :=
  rfl

/-- Rebuilding a primitive from its dependent executable and direct-TM field changes nothing. -/
@[simp]
theorem ofTMPolyTime_eta {source target : LawfulEncodedType} (primitive : Primitive source target) :
    ofTMPolyTime primitive.run primitive.tmPolyTime = primitive :=
  rfl

/-- The direct-TM identity map, at one exact lawful representation. -/
def id (presentation : LawfulEncodedType) : Primitive presentation presentation :=
  ofTMPolyTime _ (ComplexityReduction.TMPolyTimeMap.id presentation.encodedType)

@[simp]
theorem run_id (presentation : LawfulEncodedType) : (id presentation).run = _root_.id :=
  rfl

/-- Composition preserves the exact executable/TM alignment through the legacy direct-TM theorem. -/
def comp {source middle target : LawfulEncodedType}
    (after : Primitive middle target) (before : Primitive source middle) :
    Primitive source target :=
  ofTMPolyTime (after.run ∘ before.run)
    (ComplexityReduction.TMPolyTimeMap.comp after.tmPolyTime before.tmPolyTime)

@[simp]
theorem run_comp {source middle target : LawfulEncodedType}
    (after : Primitive middle target) (before : Primitive source middle) :
    (comp after before).run = after.run ∘ before.run :=
  rfl

end Primitive
end Program
end ComplexityReduction
