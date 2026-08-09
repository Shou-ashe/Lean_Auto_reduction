/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Program.Syntax

/-!
Executable semantics for canonical V2 `PolyProg` syntax.

The evaluator is defined only by the closed structural constructors and the
executable component of a `Primitive`; it introduces no arbitrary executable
map and does not erase a representation endpoint to its carrier type.
-/

namespace ComplexityReduction
namespace Program

open Encoding

namespace PolyProg

/-- Execute a program between its exact lawful source and target representations. -/
def run {source target : LawfulEncodedType} :
    PolyProg source target → source.Carrier → target.Carrier
  | .id _ => fun input => input
  | .comp after before => fun input => run after (run before input)
  | .const _ _ value => fun _ => value
  | .fst _ _ => fun input => input.1
  | .snd _ _ => fun input => input.2
  | .pair left right => fun input => (run left input, run right input)
  | .inl _ _ => fun input => .inl input
  | .inr _ _ => fun input => .inr input
  | .sumCase left right => fun input =>
      match input with
      | .inl value => run left value
      | .inr value => run right value
  | .listMap program => fun values => values.map program.run
  | .listAppend _ => fun input => List.append input.1 input.2
  | .boundedFold data => fun values =>
      values.foldl (fun current next => data.step.run (current, next)) data.init
  | .atom primitive => primitive.run

/--
The structural layout identities fixed by a program's typed endpoints.

This observation is retained for closed `CodecLayoutIso` compilation and
other layout-only APIs.  It deliberately records only `CodecShape.Identity`;
the encoder-bound program provenance observation below is the canonical
identity for endpoints whose concrete codec must not be forgotten.
-/
structure EndpointIdentities where
  source : CodecShape.Identity
  target : CodecShape.Identity
  deriving DecidableEq, Repr

/-- Recover the two exact representation identities already fixed by a program's type indices. -/
def endpointIdentities {source target : LawfulEncodedType}
    (_program : PolyProg source target) : EndpointIdentities :=
  ⟨source.representation, target.representation⟩

/-- The recovered source identity is precisely the source presentation identity index. -/
@[simp]
theorem endpointIdentities_source {source target : LawfulEncodedType}
    (program : PolyProg source target) :
    program.endpointIdentities.source = source.representation :=
  rfl

/-- The recovered target identity is precisely the target presentation identity index. -/
@[simp]
theorem endpointIdentities_target {source target : LawfulEncodedType}
    (program : PolyProg source target) :
    program.endpointIdentities.target = target.representation :=
  rfl

/--
Sequential composition retains the outer exact representation identities.

The single `middle` index in `PolyProg.comp` is shared by both inputs.  Thus this theorem does
not compare carrier types and cannot validate composition by a same-carrier coincidence.
-/
@[simp]
theorem endpointIdentities_comp {source middle target : LawfulEncodedType}
    (after : PolyProg middle target) (before : PolyProg source middle) :
    (PolyProg.comp after before).endpointIdentities =
      ⟨before.endpointIdentities.source, after.endpointIdentities.target⟩ :=
  rfl

/--
The two subprograms of a sequential composition share one *exact* middle
presentation.  In particular, this is an equality of representation
identities obtained from the common `middle` type index, not from equality of
the two underlying Lean carrier types.

Consequently, a unary-natural endpoint cannot be used to feed a
binary-natural endpoint merely because both carriers are `Nat`: no
`PolyProg.comp` term has those differently indexed programs as its two
arguments.
-/
@[simp]
theorem comp_sharedMiddle_endpointIdentity {source middle target : LawfulEncodedType}
    (after : PolyProg middle target) (before : PolyProg source middle) :
    after.endpointIdentities.source = before.endpointIdentities.target :=
  rfl

/--
The complete encoder-bound endpoint identities fixed by one typed program.

Unlike `EndpointIdentities`, this observation retains the exact
`EncodedType` together with its structural layout.  It is reconstructed only
from the `PolyProg` endpoint indices, so a route, registry entry, carrier
equality, or same-shape custom codec cannot supply or relabel it.
-/
structure EncoderBoundEndpointIdentities where
  source : EncoderBoundIdentity
  target : EncoderBoundIdentity

/-- Recover the complete encoder-bound endpoint identities fixed by a program's type indices. -/
def encoderBoundEndpointIdentities {source target : LawfulEncodedType}
    (_program : PolyProg source target) : EncoderBoundEndpointIdentities :=
  ⟨source.encoderBoundIdentity, target.encoderBoundIdentity⟩

/-- The encoder-bound source observation is exactly the program's source presentation identity. -/
@[simp]
theorem encoderBoundEndpointIdentities_source {source target : LawfulEncodedType}
    (program : PolyProg source target) :
    program.encoderBoundEndpointIdentities.source = source.encoderBoundIdentity :=
  rfl

/-- The encoder-bound target observation is exactly the program's target presentation identity. -/
@[simp]
theorem encoderBoundEndpointIdentities_target {source target : LawfulEncodedType}
    (program : PolyProg source target) :
    program.encoderBoundEndpointIdentities.target = target.encoderBoundIdentity :=
  rfl

/-- The encoder-bound observation refines the structural source observation used by layouts. -/
@[simp]
theorem encoderBoundEndpointIdentities_source_structuralIdentity
    {source target : LawfulEncodedType} (program : PolyProg source target) :
    program.encoderBoundEndpointIdentities.source.structuralIdentity =
      program.endpointIdentities.source :=
  rfl

/-- The encoder-bound observation refines the structural target observation used by layouts. -/
@[simp]
theorem encoderBoundEndpointIdentities_target_structuralIdentity
    {source target : LawfulEncodedType} (program : PolyProg source target) :
    program.encoderBoundEndpointIdentities.target.structuralIdentity =
      program.endpointIdentities.target :=
  rfl

/-- Sequential composition preserves the encoder-bound identities of its outer endpoints. -/
@[simp]
theorem encoderBoundEndpointIdentities_comp {source middle target : LawfulEncodedType}
    (after : PolyProg middle target) (before : PolyProg source middle) :
    (PolyProg.comp after before).encoderBoundEndpointIdentities =
      ⟨before.encoderBoundEndpointIdentities.source,
        after.encoderBoundEndpointIdentities.target⟩ :=
  rfl

/--
The two operands of one `PolyProg.comp` share the same complete
encoder-bound middle endpoint, not merely a same-carrier or same-shape
structural coincidence.
-/
@[simp]
theorem comp_sharedMiddle_encoderBoundEndpointIdentity
    {source middle target : LawfulEncodedType}
    (after : PolyProg middle target) (before : PolyProg source middle) :
    after.encoderBoundEndpointIdentities.source =
      before.encoderBoundEndpointIdentities.target :=
  rfl

@[simp]
theorem run_id (presentation : LawfulEncodedType) (input : presentation.Carrier) :
    (PolyProg.id presentation).run input = input :=
  rfl

@[simp]
theorem run_comp {source middle target : LawfulEncodedType}
    (after : PolyProg middle target) (before : PolyProg source middle) (input : source.Carrier) :
    (PolyProg.comp after before).run input = after.run (before.run input) :=
  rfl

@[simp]
theorem run_const (source target : LawfulEncodedType) (value : target.Carrier)
    (input : source.Carrier) :
    (PolyProg.const source target value).run input = value :=
  rfl

@[simp]
theorem run_fst (left right : LawfulEncodedType)
    (input : (StandardInstances.prod left right).Carrier) :
    (PolyProg.fst left right).run input = input.1 :=
  rfl

@[simp]
theorem run_snd (left right : LawfulEncodedType)
    (input : (StandardInstances.prod left right).Carrier) :
    (PolyProg.snd left right).run input = input.2 :=
  rfl

@[simp]
theorem run_pair {source left right : LawfulEncodedType}
    (first : PolyProg source left) (second : PolyProg source right) (input : source.Carrier) :
    (PolyProg.pair first second).run input = (first.run input, second.run input) :=
  rfl

@[simp]
theorem run_inl (left right : LawfulEncodedType) (input : left.Carrier) :
    (PolyProg.inl left right).run input = .inl input :=
  rfl

@[simp]
theorem run_inr (left right : LawfulEncodedType) (input : right.Carrier) :
    (PolyProg.inr left right).run input = .inr input :=
  rfl

@[simp]
theorem run_sumCase {left right target : LawfulEncodedType}
    (leftProgram : PolyProg left target) (rightProgram : PolyProg right target)
    (input : (StandardInstances.sum left right).Carrier) :
    (PolyProg.sumCase leftProgram rightProgram).run input =
      match input with
      | .inl value => leftProgram.run value
      | .inr value => rightProgram.run value :=
  rfl

@[simp]
theorem run_listMap {source target : LawfulEncodedType}
    (program : PolyProg source target) (input : (StandardInstances.list source).Carrier) :
    (PolyProg.listMap program).run input = input.map program.run :=
  rfl

@[simp]
theorem run_listAppend (element : LawfulEncodedType)
    (input :
      (StandardInstances.prod
        (StandardInstances.list element) (StandardInstances.list element)).Carrier) :
    (PolyProg.listAppend element).run input = List.append input.1 input.2 :=
  rfl

@[simp]
theorem run_boundedFold {element accumulator : LawfulEncodedType}
    (data : BoundedFold element accumulator) (input : (StandardInstances.list element).Carrier) :
    (PolyProg.boundedFold data).run input =
      input.foldl (fun current next => data.step.run (current, next)) data.init :=
  rfl

@[simp]
theorem run_atom {source target : LawfulEncodedType}
    (primitive : Primitive source target) (input : source.Carrier) :
    (PolyProg.atom primitive).run input = primitive.run input :=
  rfl

/--
The only open executable constructor is backed by the direct-TM witness carried by its exact
`Primitive`; an arbitrary carrier-level function cannot inhabit this constructor.
-/
theorem run_atom_directTM {source target : LawfulEncodedType}
    (primitive : Primitive source target) :
    ComplexityReduction.TMPolyTimeMap source.encodedType target.encodedType
      (PolyProg.atom primitive).run :=
  primitive.tmPolyTime

/--
Extensional semantic agreement of two programs at the same exact representations.

This relation is intentionally indexed by both lawful endpoints.  Equal Lean carrier types, such
as unary and binary naturals, are insufficient to state or use this agreement without an explicit
presentation change.
-/
def SemanticallyEquivalent {source target : LawfulEncodedType}
    (first second : PolyProg source target) : Prop :=
  ∀ input, first.run input = second.run input

namespace SemanticallyEquivalent

/--
Semantic agreement retains the exact endpoints of both programs.

The relation can only be formed for two terms with the same `source` and
`target` `LawfulEncodedType` indices, so carrier equality alone cannot turn
programs at different codecs into semantically equivalent programs.
-/
theorem endpointIdentities_eq {source target : LawfulEncodedType}
    {first second : PolyProg source target}
    (_agreement : SemanticallyEquivalent first second) :
    first.endpointIdentities = second.endpointIdentities :=
  rfl

/-- Semantic agreement is formed only at one pair of complete encoder-bound program endpoints. -/
theorem encoderBoundEndpointIdentities_eq {source target : LawfulEncodedType}
    {first second : PolyProg source target}
    (_agreement : SemanticallyEquivalent first second) :
    first.encoderBoundEndpointIdentities = second.encoderBoundEndpointIdentities :=
  rfl

/-- Semantic agreement is reflexive for one exact syntax tree. -/
theorem refl {source target : LawfulEncodedType} (program : PolyProg source target) :
    SemanticallyEquivalent program program :=
  fun _ => rfl

/-- Semantic agreement is symmetric without changing either representation endpoint. -/
theorem symm {source target : LawfulEncodedType} {first second : PolyProg source target} :
    SemanticallyEquivalent first second → SemanticallyEquivalent second first := by
  intro agreement input
  exact (agreement input).symm

/-- Semantic agreement composes only through the same exact source and target representations. -/
theorem trans {source target : LawfulEncodedType} {first second third : PolyProg source target} :
    SemanticallyEquivalent first second → SemanticallyEquivalent second third →
      SemanticallyEquivalent first third := by
  intro firstSecond secondThird input
  exact (firstSecond input).trans (secondThird input)

/-- Sequential composition respects semantic agreement of both endpoint-compatible programs. -/
theorem comp {source middle target : LawfulEncodedType}
    {after₁ after₂ : PolyProg middle target} {before₁ before₂ : PolyProg source middle}
    (afterAgreement : SemanticallyEquivalent after₁ after₂)
    (beforeAgreement : SemanticallyEquivalent before₁ before₂) :
    SemanticallyEquivalent (PolyProg.comp after₁ before₁) (PolyProg.comp after₂ before₂) := by
  intro input
  rw [run_comp, run_comp, beforeAgreement input, afterAgreement (before₂.run input)]

/-- Composing on the target side with the exact identity leaves execution unchanged. -/
theorem id_comp {source target : LawfulEncodedType} (program : PolyProg source target) :
    SemanticallyEquivalent (PolyProg.comp (PolyProg.id target) program) program :=
  fun _ => rfl

/-- Composing on the source side with the exact identity leaves execution unchanged. -/
theorem comp_id {source target : LawfulEncodedType} (program : PolyProg source target) :
    SemanticallyEquivalent (PolyProg.comp program (PolyProg.id source)) program :=
  fun _ => rfl

/-- The first projection of a pair recovers the exact first program. -/
theorem fst_pair {source left right : LawfulEncodedType}
    (first : PolyProg source left) (second : PolyProg source right) :
    SemanticallyEquivalent (PolyProg.comp (PolyProg.fst left right) (PolyProg.pair first second)) first :=
  fun _ => rfl

/-- The second projection of a pair recovers the exact second program. -/
theorem snd_pair {source left right : LawfulEncodedType}
    (first : PolyProg source left) (second : PolyProg source right) :
    SemanticallyEquivalent (PolyProg.comp (PolyProg.snd left right) (PolyProg.pair first second)) second :=
  fun _ => rfl

/-- Sum elimination after left injection executes precisely the left branch. -/
theorem sumCase_inl {left right target : LawfulEncodedType}
    (leftProgram : PolyProg left target) (rightProgram : PolyProg right target) :
    SemanticallyEquivalent
      (PolyProg.comp (PolyProg.sumCase leftProgram rightProgram) (PolyProg.inl left right)) leftProgram :=
  fun _ => rfl

/-- Sum elimination after right injection executes precisely the right branch. -/
theorem sumCase_inr {left right target : LawfulEncodedType}
    (leftProgram : PolyProg left target) (rightProgram : PolyProg right target) :
    SemanticallyEquivalent
      (PolyProg.comp (PolyProg.sumCase leftProgram rightProgram) (PolyProg.inr left right)) rightProgram :=
  fun _ => rfl

end SemanticallyEquivalent

end PolyProg
end Program
end ComplexityReduction
