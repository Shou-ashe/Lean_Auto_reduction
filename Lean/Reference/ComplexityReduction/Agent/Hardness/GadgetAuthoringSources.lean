/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.Authoring
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Domain.NAEThreeSATToMaxCut
import ComplexityReduction.Domain.ThreeSATToNAEThreeSAT

/-!
Public, endpoint-indexed sources for staged gadget authoring.

The packet below exposes independently typed construction checkpoints, but no
`CertifiedReduction`, native hardness theorem, or direct source-to-target
`TMKarpReduction`.  In particular, the structured MaxCut task must reconstruct
the reference normalization, gadget executable, parameter audit, directional
semantics, direct-TM program, and final composition as separate declarations.
-/

namespace ComplexityReduction.Agent.Hardness.GadgetAuthoringSources

open ComplexityReduction.Encoding ComplexityReduction.Program

/--
One exact three-endpoint gadget packet.

`referenceAudit` and `normalizationAudit` are packet-owned propositions so the
closed public instance can bind problem-specific mathematical invariants while
the planner and runtime remain entirely endpoint/kind driven.  `parameterAudit`
likewise binds the gadget's parameter/size contract without teaching Python any
target name or theorem spelling.
-/
structure GadgetIndexedAdmissionPacket
    (source reference target : PresentedProblem) where
  sourceExecutable : source.Instance → reference.Instance
  sourceExecutableDirectTM :
    Authoring.ExecutableDirectTMEvidence source reference sourceExecutable
  sourceExecutableCorrect :
    Authoring.ExecutableSemanticProof source reference sourceExecutable
  referenceAudit : Prop
  referenceAuditProof : referenceAudit
  normalizationAudit : Prop
  normalizationAuditProof : normalizationAudit
  gadgetExecutable : reference.Instance → target.Instance
  parameterAudit : Prop
  parameterAuditProof : parameterAudit
  gadgetExecutableDirectTM :
    Authoring.ExecutableDirectTMEvidence reference target gadgetExecutable
  gadgetSemanticForward : ∀ input,
    reference.accepts input → target.accepts (gadgetExecutable input)
  gadgetSemanticReverse : ∀ input,
    target.accepts (gadgetExecutable input) → reference.accepts input

namespace GadgetIndexedAdmissionPacket

/-- First frozen mathematical checkpoint: the source/reference audit. -/
def toReferenceAudit {source reference target : PresentedProblem}
    (packet : GadgetIndexedAdmissionPacket source reference target) :
    packet.referenceAudit :=
  packet.referenceAuditProof

/-- The normalization checkpoint is admitted only after the reference audit. -/
def toNormalizationAudit {source reference target : PresentedProblem}
    (packet : GadgetIndexedAdmissionPacket source reference target)
    (_referenceAudit : packet.referenceAudit) : packet.normalizationAudit :=
  packet.normalizationAuditProof

/-- Re-export the exact gadget executable after both normalization audits. -/
def toGadgetExecutable {source reference target : PresentedProblem}
    (packet : GadgetIndexedAdmissionPacket source reference target)
    (_referenceAudit : packet.referenceAudit)
    (_normalizationAudit : packet.normalizationAudit) :
    reference.Instance → target.Instance :=
  packet.gadgetExecutable

/-- Reindex the packet's parameter/size audit to the authored executable. -/
def toParameterAudit {source reference target : PresentedProblem}
    (packet : GadgetIndexedAdmissionPacket source reference target)
    (executable : reference.Instance → target.Instance)
    (_executable_eq : executable = packet.gadgetExecutable) :
    packet.parameterAudit :=
  packet.parameterAuditProof

/-- Reindex the exact forward implication to the authored executable. -/
def toSemanticForward {source reference target : PresentedProblem}
    (packet : GadgetIndexedAdmissionPacket source reference target)
    (executable : reference.Instance → target.Instance)
    (executable_eq : executable = packet.gadgetExecutable)
    (_parameterAudit : packet.parameterAudit) : ∀ input,
      reference.accepts input → target.accepts (executable input) := by
  intro input accepted
  rw [executable_eq]
  exact packet.gadgetSemanticForward input accepted

/-- Reindex the exact reverse implication to the authored executable. -/
def toSemanticReverse {source reference target : PresentedProblem}
    (packet : GadgetIndexedAdmissionPacket source reference target)
    (executable : reference.Instance → target.Instance)
    (executable_eq : executable = packet.gadgetExecutable)
    (_parameterAudit : packet.parameterAudit) : ∀ input,
      target.accepts (executable input) → reference.accepts input := by
  intro input accepted
  rw [executable_eq] at accepted
  exact packet.gadgetSemanticReverse input accepted

/-- Reindex direct-TM evidence only after all semantic gadget checkpoints. -/
def toGadgetDirectTM {source reference target : PresentedProblem}
    (packet : GadgetIndexedAdmissionPacket source reference target)
    (executable : reference.Instance → target.Instance)
    (executable_eq : executable = packet.gadgetExecutable)
    (_parameterAudit : packet.parameterAudit)
    (_forward : ∀ input,
      reference.accepts input → target.accepts (executable input))
    (_reverse : ∀ input,
      target.accepts (executable input) → reference.accepts input) :
    Authoring.ExecutableDirectTMEvidence reference target executable := by
  simpa [Authoring.ExecutableDirectTMEvidence, executable_eq] using
    packet.gadgetExecutableDirectTM

/-- Assemble the exact one-atom gadget program from the authored executable. -/
def toGadgetProgram {source reference target : PresentedProblem}
    (_packet : GadgetIndexedAdmissionPacket source reference target)
    (executable : reference.Instance → target.Instance)
    (directTM : Authoring.ExecutableDirectTMEvidence reference target executable) :
    PolyProg reference.representation target.representation :=
  .atom (Primitive.ofTMPolyTime executable directTM)

/-- Compose the packet-owned source normalization with the authored gadget. -/
def toComposedProgram {source reference target : PresentedProblem}
    (packet : GadgetIndexedAdmissionPacket source reference target)
    (gadgetProgram : PolyProg reference.representation target.representation) :
    PolyProg source.representation target.representation :=
  .comp gadgetProgram
    (.atom (Primitive.ofTMPolyTime packet.sourceExecutable
      packet.sourceExecutableDirectTM))

/--
Close the exact source-to-target semantic iff from the two directional gadget
proofs and the packet-owned source normalization.  Equality premises bind the
proof to the two authored program declarations and prevent a parallel map.
-/
def toComposedSemanticProof {source reference target : PresentedProblem}
    (packet : GadgetIndexedAdmissionPacket source reference target)
    (executable : reference.Instance → target.Instance)
    (forward : ∀ input,
      reference.accepts input → target.accepts (executable input))
    (reverse : ∀ input,
      target.accepts (executable input) → reference.accepts input)
    (gadgetProgram : PolyProg reference.representation target.representation)
    (gadget_run_eq : gadgetProgram.run = executable)
    (composedProgram : PolyProg source.representation target.representation)
    (composed_eq : composedProgram = toComposedProgram packet gadgetProgram) :
    Authoring.ProgramSemanticProof source target composedProgram := by
  intro input
  change source.accepts input ↔ target.accepts (composedProgram.run input)
  rw [composed_eq]
  change source.accepts input ↔
    target.accepts (gadgetProgram.run (packet.sourceExecutable input))
  rw [gadget_run_eq]
  constructor
  · intro accepted
    exact forward _ ((packet.sourceExecutableCorrect input).1 accepted)
  · intro accepted
    exact (packet.sourceExecutableCorrect input).2 (reverse _ accepted)

end GadgetIndexedAdmissionPacket

/-!
The concrete MaxCut packet remains separate from the successor-only shortcut
module.  Consequently, the structured target prompt sees the ten staged
components below but cannot see a raw source-to-MaxCut reduction.
-/

open ComplexityReduction

/-- Exact 3SAT → NAE-3SAT → structured-MaxCut staged gadget packet. -/
@[complexity_reduction_ir_component_shared_gadget]
noncomputable def threeSATToMaxCutGadgetPacket :
    GadgetIndexedAdmissionPacket
      Domain.ThreeSATToNAEThreeSAT.sourceProblem
      Domain.ThreeSATToNAEThreeSAT.targetProblem
      Domain.NAEThreeSATToMaxCut.targetProblem where
  sourceExecutable := Domain.ThreeSATToNAEThreeSAT.executable
  sourceExecutableDirectTM := by
    simpa [Authoring.ExecutableDirectTMEvidence,
      Domain.ThreeSATToNAEThreeSAT.sourceProblem,
      Domain.ThreeSATToNAEThreeSAT.targetProblem,
      Problems.Karp21.Satisfiability.threeSATStructuredProblem,
      Problems.Karp21.Satisfiability.threeSATStructuredPresentation,
      Presentation.NAEThreeSAT.structuredProblem,
      Presentation.NAEThreeSAT.structuredPresentation] using
        Domain.ThreeSATToNAEThreeSAT.executable_tmPolyTime
  sourceExecutableCorrect := by
    intro formula
    change SAT.ThreeCNF.Satisfiable formula ↔
      NAEThreeSAT.Formula.Satisfiable
        (Domain.ThreeSATToNAEThreeSAT.executable formula)
    exact Domain.ThreeSATToNAEThreeSAT.executable_correct formula
  referenceAudit := ∀ {formula : SAT.ThreeCNF} {clause : SAT.Clause},
    clause ∈ formula.clauses → ∀ {literal : SAT.Literal}, literal ∈ clause →
      literal.var < Domain.ThreeSATToNAEThreeSAT.referenceVar formula
  referenceAuditProof := by
    intro formula clause clauseMember literal literalMember
    exact Domain.ThreeSATToNAEThreeSAT.sourceLiteral_var_lt_reference
      clauseMember literalMember
  normalizationAudit := ∀ {first second third reference : Bool},
    Domain.ThreeSATToNAEThreeSAT.nae4Values first second third reference →
      Domain.ThreeSATToNAEThreeSAT.nae3Values first second
          (Domain.ThreeSATToNAEThreeSAT.splitWitness first second third) ∧
        Domain.ThreeSATToNAEThreeSAT.nae3Values
          (!(Domain.ThreeSATToNAEThreeSAT.splitWitness first second third))
          third reference
  normalizationAuditProof := by
    intro first second third reference four
    exact Domain.ThreeSATToNAEThreeSAT.splitWitness_correct four
  gadgetExecutable := Domain.NAEThreeSATToMaxCut.executable
  parameterAudit :=
    (∀ formula : NAEThreeSAT.Formula,
      Domain.NAEThreeSATToMaxCut.gadgetThreshold formula =
        Domain.NAEThreeSATToMaxCut.variableHorizon formula + 2 * formula.length) ∧
    PolynomialSizeBound
      (fun formula => Domain.NAEThreeSATToMaxCut.sourceEncoding.inputSize formula)
      (fun output => Domain.NAEThreeSATToMaxCut.targetEncoding.inputSize output)
      Domain.NAEThreeSATToMaxCut.executable
  parameterAuditProof := ⟨
    Domain.NAEThreeSATToMaxCut.gadgetThreshold_eq_horizon_add_two_mul,
    Domain.NAEThreeSATToMaxCut.executable_polynomialSizeBound⟩
  gadgetExecutableDirectTM := by
    simpa [Authoring.ExecutableDirectTMEvidence,
      Domain.ThreeSATToNAEThreeSAT.targetProblem,
      Domain.NAEThreeSATToMaxCut.targetProblem,
      Presentation.NAEThreeSAT.structuredProblem,
      Presentation.NAEThreeSAT.structuredPresentation,
      Presentation.MaxCut.structuredProblem,
      Presentation.MaxCut.structuredPresentation] using
        Domain.NAEThreeSATToMaxCut.executable_tmPolyTime
  gadgetSemanticForward := by
    intro formula accepted
    change NAEThreeSAT.Formula.Satisfiable formula at accepted
    change Combinatorics.Graph.MaxCut
      (Domain.NAEThreeSATToMaxCut.executable formula)
    rcases accepted with ⟨assignment, satisfies⟩
    exact Domain.NAEThreeSATToMaxCut.maxCut_of_satisfies
      formula assignment satisfies
  gadgetSemanticReverse := by
    intro formula accepted
    change Combinatorics.Graph.MaxCut
      (Domain.NAEThreeSATToMaxCut.executable formula) at accepted
    change NAEThreeSAT.Formula.Satisfiable formula
    exact Domain.NAEThreeSATToMaxCut.satisfies_of_maxCut formula accepted

assert_standard_axioms threeSATToMaxCutGadgetPacket

end ComplexityReduction.Agent.Hardness.GadgetAuthoringSources
