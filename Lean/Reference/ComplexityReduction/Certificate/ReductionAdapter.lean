/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Certificate.Reduction

/-!
Thin V2 route-authoring adapters.

`CertifiedIRRoute` is only a spelling for the canonical `CertifiedReduction`.  Authors supply an
exact typed program and the semantic iff for that program; a domain construction may be used only
when it is tied back to the program by a pointwise run equality.  No route metadata or independent
size, cost, TM, provider, slot, Boolean, or string evidence enters this layer.
-/

namespace ComplexityReduction
namespace Certificate

open Encoding Program

/-- The sole thin V2 IR-route surface is the canonical typed reduction certificate itself. -/
abbrev CertifiedIRRoute (source target : PresentedProblem) : Type 2 :=
  CertifiedReduction source target

namespace CertifiedIRRoute

/-- Build a route directly from one exact program and its semantic iff. -/
def ofProgram {source target : PresentedProblem}
    (program : PolyProg source.representation target.representation)
    (correct : ∀ input, source.accepts input ↔ target.accepts (program.run input)) :
    CertifiedIRRoute source target :=
  ⟨program, correct⟩

/--
Build a route from a typed domain construction only after proving that the exact program executes
that construction pointwise.  The construction itself contributes no computational capability.
-/
def ofConstruction {source target : PresentedProblem}
    (program : PolyProg source.representation target.representation)
    (construction : source.Instance → target.Instance)
    (run_eq : ∀ input, program.run input = construction input)
    (correct : ∀ input, source.accepts input ↔ target.accepts (construction input)) :
    CertifiedIRRoute source target :=
  ofProgram program (by
    intro input
    simpa [run_eq input] using correct input)

/--
Reuse an existing `ComplexityReduction` semantic reduction only after tying
its executable pointwise to the exact V2 program being certified.

The semantic reduction supplies mathematical correctness alone.  Direct-TM
and compatibility evidence still come exclusively from `program.compileTM`
and `program.compile`; therefore this adapter cannot promote a semantic lemma,
an arbitrary function, or a bare cost map into computational capability.
-/
def ofSemanticReduction {source target : PresentedProblem}
    (program : PolyProg source.representation target.representation)
    (semantic : ComplexityReduction.SemanticReduction
      source.toEncodedDecisionProblem target.toEncodedDecisionProblem)
    (run_eq : ∀ input, program.run input = semantic.f input) :
    CertifiedIRRoute source target :=
  ofProgram program (by
    intro input
    simpa [run_eq input] using semantic.correct input)

/-- The exact program supplied to `ofProgram` is retained without replacement. -/
@[simp]
theorem program_ofProgram {source target : PresentedProblem}
    (program : PolyProg source.representation target.representation)
    (correct : ∀ input, source.accepts input ↔ target.accepts (program.run input)) :
    (ofProgram program correct).program = program :=
  rfl

/-- Builder/run coherence: a route built from a program executes that exact program. -/
@[simp]
theorem run_ofProgram {source target : PresentedProblem}
    (program : PolyProg source.representation target.representation)
    (correct : ∀ input, source.accepts input ↔ target.accepts (program.run input))
    (input : source.Instance) :
    (ofProgram program correct).program.run input = program.run input :=
  rfl

/-- An `ofProgram` route receives its direct-TM witness only by compiling that exact program. -/
@[simp]
theorem directTM_ofProgram {source target : PresentedProblem}
    (program : PolyProg source.representation target.representation)
    (correct : ∀ input, source.accepts input ↔ target.accepts (program.run input)) :
    (ofProgram program correct).directTM = program.compileTM :=
  rfl

/-- An `ofProgram` route receives compatibility cost only from that exact program compiler. -/
@[simp]
theorem toTMBackedCostedMap_ofProgram {source target : PresentedProblem}
    (program : PolyProg source.representation target.representation)
    (correct : ∀ input, source.accepts input ↔ target.accepts (program.run input)) :
    (ofProgram program correct).toTMBackedCostedMap = program.compile :=
  rfl

/-- Builder/run coherence for a domain construction follows only from its supplied run equality. -/
theorem run_ofConstruction {source target : PresentedProblem}
    (program : PolyProg source.representation target.representation)
    (construction : source.Instance → target.Instance)
    (run_eq : ∀ input, program.run input = construction input)
    (correct : ∀ input, source.accepts input ↔ target.accepts (construction input))
    (input : source.Instance) :
    (ofConstruction program construction run_eq correct).program.run input = construction input :=
  run_eq input

/-- A domain construction supplies no separate direct-TM evidence beyond its tied program. -/
@[simp]
theorem directTM_ofConstruction {source target : PresentedProblem}
    (program : PolyProg source.representation target.representation)
    (construction : source.Instance → target.Instance)
    (run_eq : ∀ input, program.run input = construction input)
    (correct : ∀ input, source.accepts input ↔ target.accepts (construction input)) :
    (ofConstruction program construction run_eq correct).directTM = program.compileTM :=
  rfl

/--
A domain construction supplies no separate compatibility-cost evidence beyond its tied program.
-/
@[simp]
theorem toTMBackedCostedMap_ofConstruction {source target : PresentedProblem}
    (program : PolyProg source.representation target.representation)
    (construction : source.Instance → target.Instance)
    (run_eq : ∀ input, program.run input = construction input)
    (correct : ∀ input, source.accepts input ↔ target.accepts (construction input)) :
    (ofConstruction program construction run_eq correct).toTMBackedCostedMap = program.compile :=
  rfl

/-- The semantic adapter retains precisely the program supplied at its boundary. -/
@[simp]
theorem program_ofSemanticReduction {source target : PresentedProblem}
    (program : PolyProg source.representation target.representation)
    (semantic : ComplexityReduction.SemanticReduction
      source.toEncodedDecisionProblem target.toEncodedDecisionProblem)
    (run_eq : ∀ input, program.run input = semantic.f input) :
    (ofSemanticReduction program semantic run_eq).program = program :=
  rfl

/-- The stored program executes the reused semantic reduction's function by its supplied tie. -/
theorem run_ofSemanticReduction {source target : PresentedProblem}
    (program : PolyProg source.representation target.representation)
    (semantic : ComplexityReduction.SemanticReduction
      source.toEncodedDecisionProblem target.toEncodedDecisionProblem)
    (run_eq : ∀ input, program.run input = semantic.f input)
    (input : source.Instance) :
    (ofSemanticReduction program semantic run_eq).program.run input = semantic.f input :=
  run_eq input

/-- The semantic proof is reusable only at the run-identical stored program. -/
theorem correct_ofSemanticReduction {source target : PresentedProblem}
    (program : PolyProg source.representation target.representation)
    (semantic : ComplexityReduction.SemanticReduction
      source.toEncodedDecisionProblem target.toEncodedDecisionProblem)
    (run_eq : ∀ input, program.run input = semantic.f input)
    (input : source.Instance) :
    source.accepts input ↔
      target.accepts ((ofSemanticReduction program semantic run_eq).program.run input) := by
  simpa [run_eq input] using semantic.correct input

/-- Reusing a semantic reduction adds no TM authority beyond the program compiler. -/
@[simp]
theorem directTM_ofSemanticReduction {source target : PresentedProblem}
    (program : PolyProg source.representation target.representation)
    (semantic : ComplexityReduction.SemanticReduction
      source.toEncodedDecisionProblem target.toEncodedDecisionProblem)
    (run_eq : ∀ input, program.run input = semantic.f input) :
    (ofSemanticReduction program semantic run_eq).directTM = program.compileTM :=
  rfl

/-- Its compatibility facade is likewise exactly compilation of the stored program. -/
@[simp]
theorem toTMBackedCostedMap_ofSemanticReduction {source target : PresentedProblem}
    (program : PolyProg source.representation target.representation)
    (semantic : ComplexityReduction.SemanticReduction
      source.toEncodedDecisionProblem target.toEncodedDecisionProblem)
    (run_eq : ∀ input, program.run input = semantic.f input) :
    (ofSemanticReduction program semantic run_eq).toTMBackedCostedMap = program.compile :=
  rfl

/-- The semantic iff in an `ofConstruction` route is the construction iff rewritten by coherence. -/
theorem correct_ofConstruction {source target : PresentedProblem}
    (program : PolyProg source.representation target.representation)
    (construction : source.Instance → target.Instance)
    (run_eq : ∀ input, program.run input = construction input)
    (correct : ∀ input, source.accepts input ↔ target.accepts (construction input))
    (input : source.Instance) :
    source.accepts input ↔
      target.accepts ((ofConstruction program construction run_eq correct).program.run input) :=
  (correct input).trans (by rw [run_ofConstruction program construction run_eq correct input])

end CertifiedIRRoute
end Certificate
end ComplexityReduction
