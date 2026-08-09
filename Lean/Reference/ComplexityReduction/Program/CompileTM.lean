/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.Sum
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.TMComplexityTransport
import ComplexityReduction.Program.Semantics

/-!
Canonical direct-TM compilation for V2 programs.

Compilation follows the same `PolyProg` syntax whose evaluator supplies the executable map.  Its
compatibility cost witness is deliberately projected only from the resulting direct-TM witness's
output-size theorem; there is no API here that promotes a bare `CostedMap` to a V2 program.
-/

namespace ComplexityReduction
namespace Program

open Encoding

/--
Project a compatibility `TMBackedCostedMap` from direct-TM evidence for one exact V2 endpoint
pair.  The cost and output-size fields are both derived from `TMPolyTimeMap.outputSizeBound`.
-/
def tmBackedOfTM {source target : LawfulEncodedType}
    {run : source.Carrier → target.Carrier}
    (directTM : ComplexityReduction.TMPolyTimeMap source.encodedType target.encodedType run) :
    ComplexityReduction.TMBackedCostedMap source.encodedType target.encodedType run where
  costed := ComplexityReduction.CostedMap.of_encodedPolynomialSizeBound
    (ComplexityReduction.TMPolyTimeMap.outputSizeBound directTM)
  tm_polytime := directTM

/-- `tmBackedOfTM` retains exactly the direct-TM witness from which it was projected. -/
@[simp]
theorem tmBackedOfTM_tmPolyTime {source target : LawfulEncodedType}
    {run : source.Carrier → target.Carrier}
    (directTM : ComplexityReduction.TMPolyTimeMap source.encodedType target.encodedType run) :
    (tmBackedOfTM directTM).tm_polytime = directTM :=
  rfl

/-- The compatibility cost is mechanically derived from the same direct-TM output-size bound. -/
@[simp]
theorem tmBackedOfTM_costed {source target : LawfulEncodedType}
    {run : source.Carrier → target.Carrier}
    (directTM : ComplexityReduction.TMPolyTimeMap source.encodedType target.encodedType run) :
    (tmBackedOfTM directTM).costed =
      ComplexityReduction.CostedMap.of_encodedPolynomialSizeBound
        (ComplexityReduction.TMPolyTimeMap.outputSizeBound directTM) :=
  rfl

namespace PolyProg

/-- Compile the restricted fold constructor from its exact step primitive and growth bounds. -/
def compileBoundedFoldTM {element accumulator : LawfulEncodedType}
    (data : BoundedFold element accumulator) :
    ComplexityReduction.TMPolyTimeMap
      (StandardInstances.list element).encodedType accumulator.encodedType
      (PolyProg.boundedFold data).run := by
  rcases data.step.tmPolyTime with ⟨stepTM⟩
  exact ComplexityReduction.TMPolyTimeMap.list_foldl_typed_growth_bounded
    element.encodedType accumulator.encodedType data.step.run data.init stepTM
    data.base data.grow data.initialBound data.stepGrowth

/--
Transport the backend sum-elimination witness to the exact standard-sum presentation used by V2.
The only transport is the representation bridge required by that presentation; the underlying
machine evidence remains `TMPolyTimeMap.sum_elim` on the two exact branch compilers.
-/
def compileSumCaseTM {left right target : LawfulEncodedType}
    {leftRun : left.Carrier → target.Carrier} {rightRun : right.Carrier → target.Carrier}
    (leftTM : ComplexityReduction.TMPolyTimeMap left.encodedType target.encodedType leftRun)
    (rightTM : ComplexityReduction.TMPolyTimeMap right.encodedType target.encodedType rightRun) :
    ComplexityReduction.TMPolyTimeMap
      (StandardInstances.sum left right).encodedType target.encodedType
      (fun input =>
        match input with
        | .inl value => leftRun value
        | .inr value => rightRun value) := by
  convert ComplexityReduction.TMPolyTimeMap.sum_elim
    leftTM rightTM using 1
  funext input
  cases input <;> rfl

/-- Compile the exact executable denotation of a V2 program to a direct TM2 witness. -/
def compileTM {source target : LawfulEncodedType} (program : PolyProg source target) :
    ComplexityReduction.TMPolyTimeMap source.encodedType target.encodedType program.run := by
  induction program with
  | id presentation =>
      exact ComplexityReduction.TMPolyTimeMap.id presentation.encodedType
  | comp after before afterTM beforeTM =>
      simpa [Function.comp] using ComplexityReduction.TMPolyTimeMap.comp afterTM beforeTM
  | const source target value =>
      exact ComplexityReduction.TMPolyTimeMap.const source.encodedType target.encodedType value
  | fst left right =>
      exact ComplexityReduction.TMPolyTimeMap.fst left.encodedType right.encodedType
  | snd left right =>
      exact ComplexityReduction.TMPolyTimeMap.snd left.encodedType right.encodedType
  | pair first second firstTM secondTM =>
      exact ComplexityReduction.TMPolyTimeMap.prod_mk firstTM secondTM
  | inl left right =>
      exact ComplexityReduction.TMPolyTimeMap.inl left.encodedType right.encodedType
  | inr left right =>
      exact ComplexityReduction.TMPolyTimeMap.inr left.encodedType right.encodedType
  | sumCase left right leftTM rightTM =>
      exact compileSumCaseTM leftTM rightTM
  | listMap inner innerTM =>
      exact ComplexityReduction.TMPolyTimeMap.list_map innerTM
  | listAppend element =>
      exact ComplexityReduction.TMPolyTimeMap.list_append element.encodedType
  | @boundedFold element accumulator data =>
      exact compileBoundedFoldTM data
  | atom primitive =>
      exact primitive.tmPolyTime

/-- Identity syntax compiles to the backend identity witness at the same representation. -/
@[simp]
theorem compileTM_id (presentation : LawfulEncodedType) :
    (PolyProg.id presentation).compileTM =
      ComplexityReduction.TMPolyTimeMap.id presentation.encodedType :=
  rfl

/-- Constant syntax compiles to the backend constant witness for that exact value. -/
@[simp]
theorem compileTM_const (source target : LawfulEncodedType) (value : target.Carrier) :
    (PolyProg.const source target value).compileTM =
      ComplexityReduction.TMPolyTimeMap.const source.encodedType target.encodedType value :=
  rfl

/-- The first structural projection compiles to the backend first-projection witness. -/
@[simp]
theorem compileTM_fst (left right : LawfulEncodedType) :
    (PolyProg.fst left right).compileTM =
      ComplexityReduction.TMPolyTimeMap.fst left.encodedType right.encodedType :=
  rfl

/-- The second structural projection compiles to the backend second-projection witness. -/
@[simp]
theorem compileTM_snd (left right : LawfulEncodedType) :
    (PolyProg.snd left right).compileTM =
      ComplexityReduction.TMPolyTimeMap.snd left.encodedType right.encodedType :=
  rfl

/-- A structural pair compiles by applying the backend product constructor to its subcompilers. -/
@[simp]
theorem compileTM_pair {source left right : LawfulEncodedType}
    (first : PolyProg source left) (second : PolyProg source right) :
    (PolyProg.pair first second).compileTM =
      ComplexityReduction.TMPolyTimeMap.prod_mk first.compileTM second.compileTM :=
  rfl

/-- Left injection syntax compiles to the backend left-injection witness. -/
@[simp]
theorem compileTM_inl (left right : LawfulEncodedType) :
    (PolyProg.inl left right).compileTM =
      ComplexityReduction.TMPolyTimeMap.inl left.encodedType right.encodedType :=
  rfl

/-- Right injection syntax compiles to the backend right-injection witness. -/
@[simp]
theorem compileTM_inr (left right : LawfulEncodedType) :
    (PolyProg.inr left right).compileTM =
      ComplexityReduction.TMPolyTimeMap.inr left.encodedType right.encodedType :=
  rfl

/--
Sum dispatch compiles to the backend branch-elimination witness applied to the exact branch
subcompilers.  Thus the executable dispatch and its direct-TM evidence stay indexed by one tree.
-/
@[simp]
theorem compileTM_sumCase {left right target : LawfulEncodedType}
    (leftProgram : PolyProg left target) (rightProgram : PolyProg right target) :
    (PolyProg.sumCase leftProgram rightProgram).compileTM =
      compileSumCaseTM leftProgram.compileTM rightProgram.compileTM :=
  rfl

/-- An embedded primitive compiles to the direct-TM witness stored for its exact executable. -/
@[simp]
theorem compileTM_atom {source target : LawfulEncodedType}
    (primitive : Primitive source target) :
    (PolyProg.atom primitive).compileTM = primitive.tmPolyTime :=
  rfl

/-- Sequential V2 syntax compiles by reusing the backend's direct-TM sequential combinator. -/
@[simp]
theorem compileTM_comp {source middle target : LawfulEncodedType}
    (after : PolyProg middle target) (before : PolyProg source middle) :
    (PolyProg.comp after before).compileTM =
      ComplexityReduction.TMPolyTimeMap.comp after.compileTM before.compileTM := by
  rfl

/-- List-map compilation is exactly the backend direct-TM list combinator on the inner compiler. -/
@[simp]
theorem compileTM_listMap {source target : LawfulEncodedType}
    (inner : PolyProg source target) :
    (PolyProg.listMap inner).compileTM =
      ComplexityReduction.TMPolyTimeMap.list_map inner.compileTM :=
  rfl

/-- List append compiles to the existing backend direct-TM append combinator. -/
@[simp]
theorem compileTM_listAppend (element : LawfulEncodedType) :
    (PolyProg.listAppend element).compileTM =
      ComplexityReduction.TMPolyTimeMap.list_append element.encodedType :=
  rfl

/-- Restricted fold compilation is exactly its direct-TM fold combinator projection. -/
@[simp]
theorem compileTM_boundedFold {element accumulator : LawfulEncodedType}
    (data : BoundedFold element accumulator) :
    (PolyProg.boundedFold data).compileTM = compileBoundedFoldTM data :=
  rfl

/--
Reify a closed V2 program as a primitive-shaped value when a shared
combinator requires an atom.  Its only direct-TM field is the compiler output
for that exact program; this helper cannot accept a separately supplied map
or machine witness.
-/
def reifyPrimitive {source target : LawfulEncodedType}
    (program : PolyProg source target) : Primitive source target :=
  Primitive.ofTMPolyTime program.run program.compileTM

/-- Reification preserves the program's executable denotation exactly. -/
@[simp]
theorem reifyPrimitive_run {source target : LawfulEncodedType}
    (program : PolyProg source target) :
    (program.reifyPrimitive).run = program.run :=
  rfl

/-- Reification uses exactly the same program compiler output as its direct-TM field. -/
@[simp]
theorem reifyPrimitive_tmPolyTime {source target : LawfulEncodedType}
    (program : PolyProg source target) :
    (program.reifyPrimitive).tmPolyTime = program.compileTM :=
  rfl

/--
Compatibility cost/TM evidence for the same exact program and its exact executable denotation.
No bare cost certificate can construct this value.
-/
def compile {source target : LawfulEncodedType} (program : PolyProg source target) :
    ComplexityReduction.TMBackedCostedMap source.encodedType target.encodedType program.run :=
  tmBackedOfTM program.compileTM

/--
The complete compatibility facade is reconstructed from the direct-TM compiler of the exact
same syntax tree.  This is the public compiler boundary used by certificates: it rules out a
separate cost/TM package for `program.run`.
-/
@[simp]
theorem compile_eq_tmBackedOfTM_compileTM {source target : LawfulEncodedType}
    (program : PolyProg source target) :
    program.compile = tmBackedOfTM program.compileTM :=
  rfl

/-- Recover the direct-TM witness from the compilation of the same syntax tree. -/
theorem compile_tmPolyTime {source target : LawfulEncodedType} (program : PolyProg source target) :
    ComplexityReduction.TMPolyTimeMap source.encodedType target.encodedType program.run :=
  program.compile.tm_polytime

/-- The direct-TM field of `compile` is definitionally the compilation of that same program. -/
@[simp]
theorem compile_tmPolyTime_eq_compileTM {source target : LawfulEncodedType}
    (program : PolyProg source target) :
    program.compile.tm_polytime = program.compileTM :=
  rfl

/-- Project compatibility cost evidence only after direct-TM compilation of the same program. -/
def compatibilityCost {source target : LawfulEncodedType} (program : PolyProg source target) :
    ComplexityReduction.CostedMap source.encodedType target.encodedType program.run :=
  program.compile.costed

/--
Compatibility cost is not a second program annotation: it is exactly the cost field of the
direct-TM-derived compilation of this same syntax tree.
-/
@[simp]
theorem compatibilityCost_eq_compile_costed {source target : LawfulEncodedType}
    (program : PolyProg source target) :
    program.compatibilityCost = program.compile.costed :=
  rfl

/-- The compatibility cost is the output-size projection of this program's direct-TM compiler. -/
@[simp]
theorem compile_costed_eq_outputSizeBound {source target : LawfulEncodedType}
    (program : PolyProg source target) :
    program.compile.costed = ComplexityReduction.CostedMap.of_encodedPolynomialSizeBound
      (ComplexityReduction.TMPolyTimeMap.outputSizeBound program.compileTM) :=
  rfl

/-- `compatibilityCost` is only the cost field projected from the same direct-TM compilation. -/
@[simp]
theorem compatibilityCost_eq_outputSizeBound {source target : LawfulEncodedType}
    (program : PolyProg source target) :
    program.compatibilityCost = ComplexityReduction.CostedMap.of_encodedPolynomialSizeBound
      (ComplexityReduction.TMPolyTimeMap.outputSizeBound program.compileTM) :=
  rfl

/--
The executable, direct-TM witness, and compatibility cost have one compiler origin.

The dependent type of `program.compile` fixes its executable to `program.run`; the three
equalities below expose the remaining projections.  Consequently a client can transport the
whole chain through the one `PolyProg` value without admitting a bare `CostedMap` or an
independently supplied TM witness.
-/
theorem compile_coherence {source target : LawfulEncodedType}
    (program : PolyProg source target) :
    program.compile = tmBackedOfTM program.compileTM ∧
    program.compile.tm_polytime = program.compileTM ∧
    program.compile.costed = program.compatibilityCost ∧
    program.compatibilityCost =
      ComplexityReduction.CostedMap.of_encodedPolynomialSizeBound
        (ComplexityReduction.TMPolyTimeMap.outputSizeBound program.compileTM) :=
  ⟨compile_eq_tmBackedOfTM_compileTM program,
    compile_tmPolyTime_eq_compileTM program,
    (compatibilityCost_eq_compile_costed program).symm,
    compatibilityCost_eq_outputSizeBound program⟩

/--
Transport the complete program-indexed compiler chain along an exact direct-TM compiler
identification.

Structural compiler clauses often expose their reused backend combinator more conveniently than
the recursive compiler term itself.  This theorem is the sole bridge from such an identification
to the compatibility facade and its cost: the supplied witness must already have the exact
`program.run` index, and the resulting cost is still projected from that witness's output-size
bound.  In particular, it offers no way to start from a bare `CostedMap`.
-/
theorem compile_coherence_of_compileTM_eq {source target : LawfulEncodedType}
    (program : PolyProg source target)
    (directTM : ComplexityReduction.TMPolyTimeMap
      source.encodedType target.encodedType program.run)
    (compiled : program.compileTM = directTM) :
    program.compile = tmBackedOfTM directTM ∧
    program.compile.tm_polytime = directTM ∧
    program.compile.costed = program.compatibilityCost ∧
    program.compatibilityCost =
      ComplexityReduction.CostedMap.of_encodedPolynomialSizeBound
        (ComplexityReduction.TMPolyTimeMap.outputSizeBound directTM) := by
  rcases compile_coherence program with ⟨facade, machine, cost, outputSize⟩
  rw [compiled] at facade machine outputSize
  exact ⟨facade, machine, cost, outputSize⟩

/--
The list-append syntax derives its complete compatibility chain from the existing backend
append compiler.  Its direct TM and compatibility cost therefore have the exact same syntax-tree
origin; a client cannot substitute an independently constructed cost map.
-/
theorem compile_listAppend_coherence (element : LawfulEncodedType) :
    (PolyProg.listAppend element).compile =
      tmBackedOfTM (ComplexityReduction.TMPolyTimeMap.list_append element.encodedType) ∧
    (PolyProg.listAppend element).compile.tm_polytime =
      ComplexityReduction.TMPolyTimeMap.list_append element.encodedType ∧
    (PolyProg.listAppend element).compile.costed =
      (PolyProg.listAppend element).compatibilityCost ∧
    (PolyProg.listAppend element).compatibilityCost =
      ComplexityReduction.CostedMap.of_encodedPolynomialSizeBound
        (ComplexityReduction.TMPolyTimeMap.outputSizeBound
          (ComplexityReduction.TMPolyTimeMap.list_append element.encodedType)) :=
  compile_coherence_of_compileTM_eq (PolyProg.listAppend element)
    (ComplexityReduction.TMPolyTimeMap.list_append element.encodedType)
    (compileTM_listAppend element)

/--
The compatibility cost of a sequential program is still projected from the direct-TM compilation
of that one syntax tree, here displayed through the reused backend sequential combinator.
-/
@[simp]
theorem compatibilityCost_comp_eq_directTMOutputSizeBound
    {source middle target : LawfulEncodedType}
    (after : PolyProg middle target) (before : PolyProg source middle) :
    (PolyProg.comp after before).compatibilityCost =
      ComplexityReduction.CostedMap.of_encodedPolynomialSizeBound
        (ComplexityReduction.TMPolyTimeMap.outputSizeBound
          (ComplexityReduction.TMPolyTimeMap.comp after.compileTM before.compileTM)) := by
  rw [compatibilityCost_eq_outputSizeBound, compileTM_comp]
  rfl

/-- View the direct-TM-derived compatibility cost as the legacy closure-model map evidence. -/
theorem toCostedPolyTimeMap {source target : LawfulEncodedType} (program : PolyProg source target) :
    ComplexityReduction.CostedPolyTimeMap
      (X := source.encodedType) (Y := target.encodedType) program.run :=
  .of_costed program.compatibilityCost

/-- The compatibility-model projection has no independent cost source. -/
@[simp]
theorem toCostedPolyTimeMap_eq_of_costed {source target : LawfulEncodedType}
    (program : PolyProg source target) :
    program.toCostedPolyTimeMap = .of_costed program.compatibilityCost :=
  rfl

end PolyProg
end Program
end ComplexityReduction
