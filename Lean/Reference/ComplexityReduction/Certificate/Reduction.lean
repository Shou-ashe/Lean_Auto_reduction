/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Program.CompileTM

/-!
Canonical V2 certificates for many-one reductions.

The one stored construction is a `PolyProg` between exact presented-problem representations.
Semantic, direct-TM, and compatibility cost projections are all derived from that same program;
this certificate never stores parallel cost, size, machine, metadata, or legacy route evidence.
It imports the generic program compiler leaf directly, not the broad `V2.Program` aggregate.
-/

namespace ComplexityReduction
namespace Certificate

open Encoding Program

/--
A semantic many-one reduction whose exact executable construction is one typed V2 `PolyProg`.

The program endpoints are fixed by the source and target presentations, and `correct` refers to
that program's own `run` function.  Thus neither a same-carrier presentation mismatch nor a
different executable can be paired with this certificate's direct-TM projection.
-/
structure CertifiedReduction (source target : PresentedProblem) where
  program : PolyProg source.representation target.representation
  correct : ∀ input, source.accepts input ↔ target.accepts (program.run input)

namespace CertifiedReduction

/-- At fixed presented-problem endpoints, a certificate is determined by its one program. -/
@[ext]
theorem ext {source target : PresentedProblem}
    (first second : CertifiedReduction source target)
    (programEquality : first.program = second.program) : first = second := by
  cases first
  cases second
  cases programEquality
  rfl

/-- The identity reduction at one exact presented problem. -/
def refl (problem : PresentedProblem) : CertifiedReduction problem problem where
  program := .id problem.representation
  correct := fun _ => Iff.rfl

/--
Build one V2 reduction from an encoder-coherent executable and its semantic
correctness theorem.  The stored program is the atom created by
`Primitive.ofEncodingEquiv`, so both direct-TM and compatibility-cost
projections remain indexed by this one program.
-/
def ofEncodingEquiv {source target : PresentedProblem}
    (run : source.Instance → target.Instance)
    (alphabetEquiv : source.representation.encodedType.Symbol ≃
      target.representation.encodedType.Symbol)
    (encodeCoherence : ∀ input,
      target.representation.encodedType.encode (run input) =
        (source.representation.encodedType.encode input).map alphabetEquiv)
    (correct : ∀ input, source.accepts input ↔ target.accepts (run input)) :
    CertifiedReduction source target where
  program := .atom (Primitive.ofEncodingEquiv run alphabetEquiv encodeCoherence)
  correct := by
    intro input
    simpa using correct input

/-- Compose endpoint-compatible certified reductions by composing their one typed programs. -/
def comp {source middle target : PresentedProblem}
    (after : CertifiedReduction middle target) (before : CertifiedReduction source middle) :
    CertifiedReduction source target where
  program := .comp after.program before.program
  correct := by
    intro input
    simpa using (before.correct input).trans (after.correct (before.program.run input))

/-- Forget only the direct-TM-independent semantic content at the exact encoded endpoints. -/
def toEncodedSemanticReduction {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    ComplexityReduction.SemanticReduction
      source.toEncodedDecisionProblem target.toEncodedDecisionProblem where
  f := reduction.program.run
  correct := reduction.correct

/-- The sole direct-TM witness of a certificate is the compiler output for its stored program. -/
def directTM {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    ComplexityReduction.TMPolyTimeMap
      source.representation.encodedType target.representation.encodedType reduction.program.run :=
  reduction.program.compileTM

/-- The sole compatibility cost witness is the compiler-derived cost of the stored program. -/
def compatibilityCost {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    ComplexityReduction.CostedMap
      source.representation.encodedType target.representation.encodedType reduction.program.run :=
  reduction.program.compatibilityCost

/--
Compatibility map evidence derived by compiling the certificate's sole program.

This is a projection, not a constructor: no bare `CostedMap` can enter a `CertifiedReduction`.
-/
def toTMBackedCostedMap {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    ComplexityReduction.TMBackedCostedMap
      source.representation.encodedType target.representation.encodedType reduction.program.run :=
  reduction.program.compile

/-- Direct-TM and compatibility-cost reduction evidence projected from the same program. -/
def toTMBackedCostedReduction {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    ComplexityReduction.TMBackedCostedReduction
      source.toEncodedDecisionProblem target.toEncodedDecisionProblem :=
  ComplexityReduction.TMBackedCostedReduction.ofTMBackedCostedMap
    reduction.toTMBackedCostedMap reduction.correct

/-- The direct TM2 Karp reduction projection of a certified V2 reduction. -/
def toTMKarpReduction {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    ComplexityReduction.TMKarpReduction
      source.toEncodedDecisionProblem target.toEncodedDecisionProblem :=
  reduction.toTMBackedCostedReduction.toTMKarpReduction

/-- The compatibility closure-model Karp projection, derived only after V2 program compilation. -/
def toCostedKarpReduction {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    ComplexityReduction.KarpReductionM ComplexityReduction.CostedPolyTimeModel
      source.toEncodedDecisionProblem target.toEncodedDecisionProblem :=
  reduction.toTMBackedCostedReduction.toCostedKarpReduction

/-- Direct-TM reducibility follows from the program-derived direct-TM Karp projection. -/
theorem toTMPolyReducible {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    ComplexityReduction.TMPolyReducible
      source.toEncodedDecisionProblem target.toEncodedDecisionProblem :=
  ⟨reduction.toTMKarpReduction⟩

/-- Compatibility-model reducibility follows from the program-derived cost projection. -/
theorem toCostedPolyReducible {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    ComplexityReduction.PolyReducibleM ComplexityReduction.CostedPolyTimeModel
      source.toEncodedDecisionProblem target.toEncodedDecisionProblem :=
  ⟨reduction.toCostedKarpReduction⟩

@[simp]
theorem refl_program (problem : PresentedProblem) :
    (refl problem).program = PolyProg.id problem.representation :=
  rfl

@[simp]
theorem comp_program {source middle target : PresentedProblem}
    (after : CertifiedReduction middle target) (before : CertifiedReduction source middle) :
    (comp after before).program = PolyProg.comp after.program before.program :=
  rfl

/-- The semantic projection runs precisely the certificate's stored program. -/
@[simp]
theorem toEncodedSemanticReduction_f {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    reduction.toEncodedSemanticReduction.f = reduction.program.run :=
  rfl

/-- The semantic projection's correctness proof is indexed by the stored program. -/
@[simp]
theorem toEncodedSemanticReduction_correct {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) (input : source.Instance) :
    source.accepts input ↔ target.accepts (reduction.toEncodedSemanticReduction.f input) :=
  reduction.toEncodedSemanticReduction.correct input

/-- The certificate's direct-TM projection is definitionally its program compiler output. -/
@[simp]
theorem directTM_eq_compileTM {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    reduction.directTM = reduction.program.compileTM :=
  rfl

/-- The certificate's compatibility cost is definitionally its program compiler projection. -/
@[simp]
theorem compatibilityCost_eq_program_compatibilityCost {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    reduction.compatibilityCost = reduction.program.compatibilityCost :=
  rfl

/-- The compatibility map is the complete direct-TM compilation of the stored program. -/
@[simp]
theorem toTMBackedCostedMap_eq_compile {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    reduction.toTMBackedCostedMap = reduction.program.compile :=
  rfl

/-- The compatibility map's direct-TM field is the certificate's program-derived witness. -/
@[simp]
theorem toTMBackedCostedMap_tmPolyTime {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    reduction.toTMBackedCostedMap.tm_polytime = reduction.directTM :=
  rfl

/-- The compatibility map's cost field is the certificate's program-derived cost projection. -/
@[simp]
theorem toTMBackedCostedMap_costed {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    reduction.toTMBackedCostedMap.costed = reduction.compatibilityCost :=
  rfl

/-- The legacy reduction projection preserves the stored program's exact executable. -/
@[simp]
theorem toTMBackedCostedReduction_f {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    reduction.toTMBackedCostedReduction.f = reduction.program.run :=
  rfl

/-- The legacy reduction projection preserves the program-derived direct-TM witness. -/
@[simp]
theorem toTMBackedCostedReduction_tmPolyTime {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    reduction.toTMBackedCostedReduction.tm_polytime = reduction.directTM :=
  rfl

/-- The legacy reduction's compatibility map is the closure projection of the same compiled cost. -/
@[simp]
theorem toTMBackedCostedReduction_costed {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    reduction.toTMBackedCostedReduction.costed = .of_costed reduction.compatibilityCost :=
  rfl

/--
The complete TM-backed reduction facade is constructed from the compilation of
the certificate's one stored program and its program-indexed semantic proof.

This is deliberately an equality to the direct-TM constructor rather than an
alternative constructor for certificates: it makes the one-way compatibility
projection available to legacy consumers without admitting a bare `CostedMap`.
-/
@[simp]
theorem toTMBackedCostedReduction_eq_of_program_compile {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    reduction.toTMBackedCostedReduction =
      ComplexityReduction.TMBackedCostedReduction.ofTMBackedCostedMap
        reduction.program.compile reduction.correct :=
  rfl

/-- The TM-backed facade's semantic proof is the certificate's stored program proof. -/
@[simp]
theorem toTMBackedCostedReduction_correct {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) (input : source.Instance) :
    source.accepts input ↔
      target.accepts (reduction.toTMBackedCostedReduction.f input) :=
  reduction.correct input

/-- The direct-TM Karp projection preserves the stored program's exact executable. -/
@[simp]
theorem toTMKarpReduction_f {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    reduction.toTMKarpReduction.f = reduction.program.run :=
  rfl

/-- The direct-TM Karp projection is the direct-TM projection of the stored program. -/
@[simp]
theorem toTMKarpReduction_polytime {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    reduction.toTMKarpReduction.polytime = reduction.directTM :=
  rfl

/-- The costed Karp facade keeps the exact executable of the stored program. -/
@[simp]
theorem toCostedKarpReduction_f {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    reduction.toCostedKarpReduction.f.toFun = reduction.program.run :=
  rfl

/-- The costed Karp facade is admitted only after compiling the stored program. -/
@[simp]
theorem toCostedKarpReduction_polytime {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    reduction.toCostedKarpReduction.f.polytime = reduction.program.toCostedPolyTimeMap :=
  rfl

/-- The costed Karp facade reuses the certificate's same program-indexed semantic proof. -/
@[simp]
theorem toCostedKarpReduction_correct {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) (input : source.Instance) :
    source.accepts input ↔ target.accepts (reduction.toCostedKarpReduction.f.toFun input) :=
  reduction.correct input

/--
The complete executable evidence chain for a certificate is indexed by its one stored program.

This packages the boundary invariant used by route and registry layers: semantic execution,
direct-TM evidence, compatibility cost/TM evidence, and the legacy TM-Karp facade cannot refer to
separately supplied functions or machines.  In particular, every equality below reduces to the
same `reduction.program`, so a bare `CostedMap` has no admission path into the chain.
-/
theorem projections_share_one_program {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    reduction.toEncodedSemanticReduction.f = reduction.program.run ∧
    (∀ input, source.accepts input ↔ target.accepts (reduction.program.run input)) ∧
    reduction.directTM = reduction.program.compileTM ∧
    reduction.compatibilityCost = reduction.program.compatibilityCost ∧
    reduction.toTMBackedCostedMap.tm_polytime = reduction.program.compileTM ∧
    reduction.toTMBackedCostedMap.costed = reduction.program.compatibilityCost ∧
    reduction.toTMKarpReduction.f = reduction.program.run ∧
    reduction.toTMKarpReduction.polytime = reduction.program.compileTM :=
  ⟨rfl, reduction.correct, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
The legacy compatibility facades retain the same executable, compiler witness,
and semantic theorem as the stored program.  This is the full boundary theorem
for consumers that still require `TMBackedCostedReduction` or a costed Karp
reduction; neither facade contributes an independent computation certificate.
-/
theorem compatibility_facades_share_one_program {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    reduction.toTMBackedCostedReduction.f = reduction.program.run ∧
    reduction.toTMBackedCostedReduction.tm_polytime = reduction.program.compileTM ∧
    reduction.toTMBackedCostedReduction.costed =
      .of_costed reduction.program.compatibilityCost ∧
    (∀ input, source.accepts input ↔
      target.accepts (reduction.toTMBackedCostedReduction.f input)) ∧
    reduction.toCostedKarpReduction.f.toFun = reduction.program.run ∧
    reduction.toCostedKarpReduction.f.polytime = reduction.program.toCostedPolyTimeMap ∧
    (∀ input, source.accepts input ↔
      target.accepts (reduction.toCostedKarpReduction.f.toFun input)) :=
  ⟨rfl, rfl, rfl, reduction.correct, rfl, rfl, reduction.correct⟩

/--
The complete compiler boundary at the exact presented-problem endpoints.

Besides retaining the source and target representation identities in the
stored `PolyProg`, this states the two trusted complexity projections in
terms of the *fields of the same* `program.compile`: direct-TM evidence is
its `tm_polytime` field and compatibility cost is its `costed` field.  Thus
neither field can be supplied by an independent TM or bare `CostedMap` when
constructing a `CertifiedReduction`.
-/
theorem endpoint_exact_compile_coherence {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    reduction.program.endpointIdentities =
      ⟨source.representation.representation, target.representation.representation⟩ ∧
    reduction.toEncodedSemanticReduction.f = reduction.program.run ∧
    (∀ input, source.accepts input ↔ target.accepts (reduction.program.run input)) ∧
    reduction.toTMBackedCostedMap = reduction.program.compile ∧
    reduction.directTM = reduction.program.compile.tm_polytime ∧
    reduction.compatibilityCost = reduction.program.compile.costed ∧
    reduction.toTMKarpReduction.f = reduction.program.run ∧
    reduction.toTMKarpReduction.polytime = reduction.program.compile.tm_polytime := by
  rcases PolyProg.compile_coherence reduction.program with
    ⟨_, compiledTM, compiledCost, _⟩
  exact
    ⟨rfl, rfl, reduction.correct, rfl,
      (directTM_eq_compileTM reduction).trans compiledTM.symm,
      (compatibilityCost_eq_program_compatibilityCost reduction).trans compiledCost.symm,
      rfl,
      (toTMKarpReduction_polytime reduction).trans
        ((directTM_eq_compileTM reduction).trans compiledTM.symm)⟩

/-- Composing certificates composes the executables of their only two stored programs. -/
@[simp]
theorem comp_run {source middle target : PresentedProblem}
    (after : CertifiedReduction middle target) (before : CertifiedReduction source middle)
    (input : source.Instance) :
    (comp after before).program.run input = after.program.run (before.program.run input) :=
  rfl

/--
The semantic projection of a composite executes the very `PolyProg.comp`
stored by that composite, rather than a separately assembled semantic map.
-/
@[simp]
theorem comp_toEncodedSemanticReduction_f {source middle target : PresentedProblem}
    (after : CertifiedReduction middle target) (before : CertifiedReduction source middle) :
    (comp after before).toEncodedSemanticReduction.f =
      (PolyProg.comp after.program before.program).run :=
  rfl

/--
The semantic iff of a composite is indexed by the same `PolyProg.comp` value
as its executable projection.
-/
theorem comp_correct {source middle target : PresentedProblem}
    (after : CertifiedReduction middle target) (before : CertifiedReduction source middle)
    (input : source.Instance) :
    source.accepts input ↔
      target.accepts ((PolyProg.comp after.program before.program).run input) :=
  (comp after before).correct input

/--
The direct-TM projection of a composite is compilation of its one stored
`PolyProg.comp` program.
-/
@[simp]
theorem comp_directTM {source middle target : PresentedProblem}
    (after : CertifiedReduction middle target) (before : CertifiedReduction source middle) :
    (comp after before).directTM =
      (PolyProg.comp after.program before.program).compileTM :=
  rfl

/--
The compatibility cost of a composite is derived only from the same stored
`PolyProg.comp` program.
-/
@[simp]
theorem comp_compatibilityCost {source middle target : PresentedProblem}
    (after : CertifiedReduction middle target) (before : CertifiedReduction source middle) :
    (comp after before).compatibilityCost =
      (PolyProg.comp after.program before.program).compatibilityCost :=
  rfl

/--
The complete compatibility facade of a composite is compiled from its one
stored `PolyProg.comp` program.
-/
@[simp]
theorem comp_toTMBackedCostedMap {source middle target : PresentedProblem}
    (after : CertifiedReduction middle target) (before : CertifiedReduction source middle) :
    (comp after before).toTMBackedCostedMap =
      (PolyProg.comp after.program before.program).compile :=
  rfl

/-- The facade direct-TM field is the compiler output of the composite program. -/
@[simp]
theorem comp_toTMBackedCostedMap_tmPolyTime {source middle target : PresentedProblem}
    (after : CertifiedReduction middle target) (before : CertifiedReduction source middle) :
    (comp after before).toTMBackedCostedMap.tm_polytime =
      (PolyProg.comp after.program before.program).compileTM :=
  rfl

/-- The facade cost field is the compiler-derived cost of the composite program. -/
@[simp]
theorem comp_toTMBackedCostedMap_costed {source middle target : PresentedProblem}
    (after : CertifiedReduction middle target) (before : CertifiedReduction source middle) :
    (comp after before).toTMBackedCostedMap.costed =
      (PolyProg.comp after.program before.program).compatibilityCost :=
  rfl

/-- The direct-TM Karp facade runs precisely the stored composite program. -/
@[simp]
theorem comp_toTMKarpReduction_f {source middle target : PresentedProblem}
    (after : CertifiedReduction middle target) (before : CertifiedReduction source middle) :
    (comp after before).toTMKarpReduction.f =
      (PolyProg.comp after.program before.program).run :=
  rfl

/-- The direct-TM Karp facade retains the compiler witness of the composite program. -/
@[simp]
theorem comp_toTMKarpReduction_polytime {source middle target : PresentedProblem}
    (after : CertifiedReduction middle target) (before : CertifiedReduction source middle) :
    (comp after before).toTMKarpReduction.polytime =
      (PolyProg.comp after.program before.program).compileTM :=
  rfl

/--
Composition preserves the exact compiler boundary: the composite has one
syntax tree, and both its direct-TM and costed projections are the respective
fields of that tree's one `compile` result.
-/
theorem comp_endpoint_exact_compile_coherence {source middle target : PresentedProblem}
    (after : CertifiedReduction middle target) (before : CertifiedReduction source middle) :
    (comp after before).program.endpointIdentities =
      ⟨source.representation.representation, target.representation.representation⟩ ∧
    (comp after before).toTMBackedCostedMap =
      (PolyProg.comp after.program before.program).compile ∧
    (comp after before).directTM =
      (PolyProg.comp after.program before.program).compile.tm_polytime ∧
    (comp after before).compatibilityCost =
      (PolyProg.comp after.program before.program).compile.costed := by
  rcases PolyProg.compile_coherence (PolyProg.comp after.program before.program) with
    ⟨_, compiledTM, compiledCost, _⟩
  exact
    ⟨rfl, rfl,
      (comp_directTM after before).trans compiledTM.symm,
      (comp_compatibilityCost after before).trans compiledCost.symm⟩

/--
Three-way certificate composition has one nested `PolyProg.comp` provenance chain.

The semantic map, complete compiler facade, direct-TM witness, compatibility
cost, and Karp facade below all reduce to the same nested syntax tree.  The
component direct-TM equation is exposed only by structurally compiling that
tree; it is not an alternative source of machine or cost evidence.
-/
theorem nested_comp_compile_provenance
    {source firstMiddle secondMiddle target : PresentedProblem}
    (after : CertifiedReduction secondMiddle target)
    (middle : CertifiedReduction firstMiddle secondMiddle)
    (before : CertifiedReduction source firstMiddle) :
    (comp after (comp middle before)).program =
      PolyProg.comp after.program (PolyProg.comp middle.program before.program) ∧
    (comp after (comp middle before)).toEncodedSemanticReduction.f =
      (PolyProg.comp after.program (PolyProg.comp middle.program before.program)).run ∧
    (∀ input, source.accepts input ↔ target.accepts
      ((PolyProg.comp after.program (PolyProg.comp middle.program before.program)).run input)) ∧
    (comp after (comp middle before)).toTMBackedCostedMap =
      (PolyProg.comp after.program (PolyProg.comp middle.program before.program)).compile ∧
    (comp after (comp middle before)).directTM =
      (PolyProg.comp after.program (PolyProg.comp middle.program before.program)).compileTM ∧
    (comp after (comp middle before)).directTM =
      ComplexityReduction.TMPolyTimeMap.comp after.program.compileTM
        (ComplexityReduction.TMPolyTimeMap.comp middle.program.compileTM before.program.compileTM) ∧
    (comp after (comp middle before)).compatibilityCost =
      (PolyProg.comp after.program (PolyProg.comp middle.program before.program)).compatibilityCost ∧
    (comp after (comp middle before)).toTMKarpReduction.f =
      (PolyProg.comp after.program (PolyProg.comp middle.program before.program)).run ∧
    (comp after (comp middle before)).toTMKarpReduction.polytime =
      (PolyProg.comp after.program (PolyProg.comp middle.program before.program)).compileTM := by
  refine ⟨rfl, rfl, (comp after (comp middle before)).correct, rfl, rfl, ?_, rfl, rfl, rfl⟩
  rfl

end CertifiedReduction
end Certificate
end ComplexityReduction
