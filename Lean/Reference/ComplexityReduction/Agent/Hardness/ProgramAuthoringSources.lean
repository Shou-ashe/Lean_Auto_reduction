/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.Authoring
import ComplexityReduction.Domain.SetCoveringToSeeingSet

/-!
Public, endpoint-indexed sources for staged program authoring.

This module deliberately exports neither a certified route nor a hardness
theorem.  A packet only binds one executable to direct-TM evidence and its
pointwise semantic theorem.  Generated code must still materialize every
program layer, and the final route remains runner-owned and Lean-checked.
-/

namespace ComplexityReduction.Agent.Hardness.ProgramAuthoringSources

open ComplexityReduction.Encoding ComplexityReduction.Program

/--
One public executable packet at exact presented endpoints.

Unlike the discovery-only template marker, this is an ordinary typed value:
the observer recognizes its elaborated type in this one allowlisted module and
generated code may use only its dependent projections.
-/
structure ProgramIndexedAdmissionPacket (source target : PresentedProblem) where
  executable : source.Instance → target.Instance
  executableDirectTM :
    Authoring.ExecutableDirectTMEvidence source target executable
  executableCorrect :
    Authoring.ExecutableSemanticProof source target executable

namespace ProgramIndexedAdmissionPacket

/-- Re-export exactly the packet executable at the first authored checkpoint. -/
def toExecutable {source target : PresentedProblem}
    (packet : ProgramIndexedAdmissionPacket source target) :
    source.Instance → target.Instance :=
  packet.executable

/-- Build a primitive only from the authored executable and this packet's witness. -/
def toPrimitive {source target : PresentedProblem}
    (packet : ProgramIndexedAdmissionPacket source target)
    (executable : source.Instance → target.Instance)
    (executable_eq : executable = packet.executable) :
    Primitive source.representation target.representation :=
  Primitive.ofTMPolyTime executable (by
    simpa [Authoring.ExecutableDirectTMEvidence, executable_eq] using
      packet.executableDirectTM)

/-- Embed exactly the authored primitive as the authored one-atom program. -/
def toProgram {source target : PresentedProblem}
    (primitive : Primitive source.representation target.representation) :
    PolyProg source.representation target.representation :=
  .atom primitive

/--
The program-indexed admission gate combines actual compiled direct-TM evidence
with equality to the packet executable.  It is neither route metadata nor a
Boolean readiness marker.
-/
structure ProgramRunCoherenceDirectTM {source target : PresentedProblem}
    (packet : ProgramIndexedAdmissionPacket source target)
    (program : PolyProg source.representation target.representation) : Prop where
  directTM : Authoring.ProgramDirectTMEvidence source target program
  run_eq : program.run = packet.executable

namespace ProgramRunCoherenceDirectTM

/-- Close the exact program gate from the compiler and executable coherence. -/
def ofProgram {source target : PresentedProblem}
    (packet : ProgramIndexedAdmissionPacket source target)
    (program : PolyProg source.representation target.representation)
    (run_eq : program.run = packet.executable) :
    ProgramRunCoherenceDirectTM packet program where
  directTM := program.compileTM
  run_eq := run_eq

end ProgramRunCoherenceDirectTM

/--
Reindex the packet semantics only after the exact authored program has passed
the combined run-coherence/direct-TM admission gate.
-/
def toSemanticProof {source target : PresentedProblem}
    (packet : ProgramIndexedAdmissionPacket source target)
    (program : PolyProg source.representation target.representation)
    (admission : ProgramRunCoherenceDirectTM packet program) :
    Authoring.ProgramSemanticProof source target program := by
  intro input
  change source.accepts input ↔ target.accepts (program.run input)
  rw [admission.run_eq]
  exact packet.executableCorrect input

end ProgramIndexedAdmissionPacket

/-- Public Set Covering → Seeing Set packet; no route or hardness is exported. -/
def seeingSetProgramPacket : ProgramIndexedAdmissionPacket
    Domain.SetCoveringToSeeingSet.source Domain.SetCoveringToSeeingSet.target where
  executable := Domain.SetCoveringToSeeingSet.executable
  executableDirectTM := Domain.SetCoveringToSeeingSet.executableDirectTM
  executableCorrect := Domain.SetCoveringToSeeingSet.executableCorrect

end ComplexityReduction.Agent.Hardness.ProgramAuthoringSources
