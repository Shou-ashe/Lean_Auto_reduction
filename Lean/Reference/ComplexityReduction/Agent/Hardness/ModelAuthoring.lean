/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Certificate.Reduction
import ComplexityReduction.Core.ComponentRole
import Lean.Attributes

/-!
Lightweight Phase-7 authoring ABI.

Model-authored checkpoint files import this module instead of the registry and
meta-level discovery implementation. It fixes the exact dependent types used
by the public skeleton while granting no registry capability.
-/

namespace ComplexityReduction.Agent.Hardness.Authoring

open ComplexityReduction.Encoding ComplexityReduction.Program

def ExecutableDirectTMEvidence
    (source target : PresentedProblem)
    (run : source.Instance → target.Instance) : Prop :=
  ComplexityReduction.TMPolyTimeMap
    source.representation.encodedType target.representation.encodedType run

def ExecutableSemanticProof
    (source target : PresentedProblem)
    (run : source.Instance → target.Instance) : Prop :=
  ∀ input, source.accepts input ↔ target.accepts (run input)

def ProgramSemanticProof
    (source target : PresentedProblem)
    (program : PolyProg source.representation target.representation) : Prop :=
  ∀ input, source.accepts input ↔ target.accepts (program.run input)

def ProgramDirectTMEvidence
    (source target : PresentedProblem)
    (program : PolyProg source.representation target.representation) : Prop :=
  ComplexityReduction.TMPolyTimeMap
    source.representation.encodedType target.representation.encodedType program.run

/-- Discovery-only public skeleton with no semantic theorem parameter. -/
structure ProgramIndexedModelTemplate
    (role : ComplexityReduction.ReductionComponentRole)
    (source target : PresentedProblem)
    (run : source.Instance → target.Instance)
    (directTM : ExecutableDirectTMEvidence source target run) : Prop where
  witness : True

namespace ProgramIndexedModelTemplate

/-- Reindex the public direct-TM witness to the exact generated executable. -/
def toExecutableDirectTM {source target : PresentedProblem}
    {templateRun : source.Instance → target.Instance}
    (templateDirectTM : ExecutableDirectTMEvidence source target templateRun)
    (run : source.Instance → target.Instance) (run_eq : run = templateRun) :
    ExecutableDirectTMEvidence source target run := by
  simpa [ExecutableDirectTMEvidence, run_eq] using templateDirectTM

/-- Construct the exact primitive from the generated executable and its witness. -/
def toPrimitive {source target : PresentedProblem}
    (run : source.Instance → target.Instance)
    (directTM : ExecutableDirectTMEvidence source target run) :
    Primitive source.representation target.representation :=
  Primitive.ofTMPolyTime run directTM

/-- Embed the exact generated primitive as the one-atom program. -/
def toProgram {source target : PresentedProblem}
    (primitive : Primitive source.representation target.representation) :
    PolyProg source.representation target.representation :=
  .atom primitive

/-- Reindex the exact executable witness to the generated one-atom program. -/
def toProgramDirectTM {source target : PresentedProblem}
    {run : source.Instance → target.Instance}
    (directTM : ExecutableDirectTMEvidence source target run)
    (program : PolyProg source.representation target.representation)
    (run_eq : program.run = run) :
    ProgramDirectTMEvidence source target program := by
  simpa [ExecutableDirectTMEvidence, ProgramDirectTMEvidence, run_eq] using directTM

/-- Package the exact program selected by the semantic checkpoint. -/
def toReduction {source target : PresentedProblem}
    (program : PolyProg source.representation target.representation)
    (semantic : ProgramSemanticProof source target program) :
    ComplexityReduction.Certificate.CertifiedReduction source target where
  program := program
  correct := semantic

end ProgramIndexedModelTemplate

initialize programIndexedModelTemplateAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `complexity_reduction_ir_hardness_program_model_template
    "marks a program-indexed model-authoring skeleton; grants no trusted capability"

end ComplexityReduction.Agent.Hardness.Authoring
