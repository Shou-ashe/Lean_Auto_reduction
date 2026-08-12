/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case03PositiveNAE3
import ComplexityReduction.Agent.Hardness.BooleanCSPAuthoringSources

/-! Exact-endpoint regression for the public positive-NAE3 authoring seed. -/

namespace ComplexityReduction.Agent.Hardness.Regression.BooleanCSPAuthoring

open ComplexityReduction

noncomputable def exactExecutable :
    Problems.Karp21.Satisfiability.threeSATStructuredProblem.Instance →
      Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case03PositiveNAE3.problem.Instance :=
  BooleanCSPAuthoringSources.PositiveNAE3CSP.executable

theorem exactExecutableDirectTM :
    Hardness.Authoring.ExecutableDirectTMEvidence
      Problems.Karp21.Satisfiability.threeSATStructuredProblem
      Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case03PositiveNAE3.problem
      exactExecutable := by
  simpa only [exactExecutable] using
      BooleanCSPAuthoringSources.PositiveNAE3CSP.executable_tmPolyTime

theorem exactExecutableCorrect :
    Hardness.Authoring.ExecutableSemanticProof
      Problems.Karp21.Satisfiability.threeSATStructuredProblem
      Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case03PositiveNAE3.problem
      exactExecutable := by
  intro formula
  change SAT.ThreeCNF.Satisfiable formula ↔
    CSP.Formula.Satisfiable
      (BooleanCSPAuthoringSources.PositiveNAE3CSP.executable formula)
  exact BooleanCSPAuthoringSources.PositiveNAE3CSP.executable_correct formula

/-! The exact staged whole-reduction declarations emitted by the authoring runtime. -/

noncomputable def clauseConstraint :
    NAEThreeSAT.Clause →
      CSP.Constraint
        Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case03PositiveNAE3.gamma :=
  BooleanCSPAuthoringSources.PositiveNAE3CSP.clauseConstraint

noncomputable def complementConstraint :
    SAT.Literal →
      CSP.Constraint
        Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case03PositiveNAE3.gamma :=
  BooleanCSPAuthoringSources.PositiveNAE3CSP.complementConstraint

noncomputable def clauseGadget :
    NAEThreeSAT.Clause →
      Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case03PositiveNAE3.problem.Instance :=
  fun clause =>
    [ clauseConstraint clause,
      complementConstraint clause.first,
      complementConstraint clause.second,
      complementConstraint clause.third ]

noncomputable def referenceExecutable :
    NAEThreeSAT.Formula →
      Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case03PositiveNAE3.problem.Instance :=
  BooleanCSPAuthoringSources.PositiveNAE3CSP.referenceExecutable

theorem clauseGadgetDirectTM :
    TMPolyTimeMap Presentation.NAEThreeSAT.clauseEncodedType
      Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case03PositiveNAE3.problem.representation.encodedType
      clauseGadget := by
  simpa only [clauseGadget, clauseConstraint, complementConstraint,
      BooleanCSPAuthoringSources.PositiveNAE3CSP.clauseBlock] using
    BooleanCSPAuthoringSources.PositiveNAE3CSP.clauseBlock_tmPolyTime

theorem referenceDirectTM :
    TMPolyTimeMap Presentation.NAEThreeSAT.formulaEncodedType
      Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case03PositiveNAE3.problem.representation.encodedType
      referenceExecutable := by
  simpa only [referenceExecutable] using
    BooleanCSPAuthoringSources.PositiveNAE3CSP.referenceExecutable_tmPolyTime

theorem referenceSemanticForward (formula : NAEThreeSAT.Formula) :
    NAEThreeSAT.Formula.Satisfiable formula →
      Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case03PositiveNAE3.problem.accepts
        (referenceExecutable formula) := by
  exact (BooleanCSPAuthoringSources.PositiveNAE3CSP.referenceExecutable_correct formula).mp

theorem referenceSemanticReverse (formula : NAEThreeSAT.Formula) :
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case03PositiveNAE3.problem.accepts
        (referenceExecutable formula) →
      NAEThreeSAT.Formula.Satisfiable formula := by
  exact (BooleanCSPAuthoringSources.PositiveNAE3CSP.referenceExecutable_correct formula).mpr

noncomputable def synthesizedExecutable :
    Problems.Karp21.Satisfiability.threeSATStructuredProblem.Instance →
      Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case03PositiveNAE3.problem.Instance := by
  exact BooleanCSPAuthoringSources.PositiveNAE3CSP.executable

theorem synthesizedDirectTM :
    TMPolyTimeMap
      Problems.Karp21.Satisfiability.threeSATStructuredProblem.representation.encodedType
      Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case03PositiveNAE3.problem.representation.encodedType
      synthesizedExecutable := by
  simpa only [synthesizedExecutable] using
    BooleanCSPAuthoringSources.PositiveNAE3CSP.executable_tmPolyTime

noncomputable def synthesizedPrimitive :
    Program.Primitive
      Problems.Karp21.Satisfiability.threeSATStructuredProblem.representation
      Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case03PositiveNAE3.problem.representation :=
  Program.Primitive.ofTMPolyTime synthesizedExecutable synthesizedDirectTM

noncomputable def synthesizedProgram :
    Program.PolyProg
      Problems.Karp21.Satisfiability.threeSATStructuredProblem.representation
      Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case03PositiveNAE3.problem.representation :=
  Program.PolyProg.atom synthesizedPrimitive

theorem programRunCoherence (input) :
    synthesizedProgram.run input = synthesizedExecutable input := by
  rfl

theorem semanticForward (input)
    (accepted :
      Problems.Karp21.Satisfiability.threeSATStructuredProblem.accepts input) :
    Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case03PositiveNAE3.problem.accepts
      (synthesizedProgram.run input) := by
  rw [programRunCoherence input]
  exact (BooleanCSPAuthoringSources.PositiveNAE3CSP.executable_correct input).mp accepted

theorem semanticReverse (input)
    (accepted :
      Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case03PositiveNAE3.problem.accepts
        (synthesizedProgram.run input)) :
    Problems.Karp21.Satisfiability.threeSATStructuredProblem.accepts input := by
  rw [programRunCoherence input] at accepted
  exact (BooleanCSPAuthoringSources.PositiveNAE3CSP.executable_correct input).mpr accepted

theorem semanticCorrect (input) :
    Problems.Karp21.Satisfiability.threeSATStructuredProblem.accepts input ↔
      Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case03PositiveNAE3.problem.accepts
        (synthesizedProgram.run input) := by
  exact ⟨semanticForward input, semanticReverse input⟩

assert_standard_axioms
  exactExecutable,
  exactExecutableDirectTM,
  exactExecutableCorrect,
  clauseConstraint,
  complementConstraint,
  clauseGadget,
  referenceExecutable,
  clauseGadgetDirectTM,
  referenceDirectTM,
  referenceSemanticForward,
  referenceSemanticReverse,
  synthesizedExecutable,
  synthesizedDirectTM,
  synthesizedPrimitive,
  synthesizedProgram,
  programRunCoherence,
  semanticForward,
  semanticReverse,
  semanticCorrect

end ComplexityReduction.Agent.Hardness.Regression.BooleanCSPAuthoring
