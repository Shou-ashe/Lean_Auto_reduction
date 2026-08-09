/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.Encoding
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Encoding.StandardInstances

/-!
Concrete V2 ownership of Karp21 structured satisfiability endpoints.

This domain leaf owns the exact lawful presentation and semantic problem used
by V2 SAT routes.  It contains no route certificate, machine, registry, or
legacy descriptor authority.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace Satisfiability

open Encoding

/-- The explicit product layout of the existing faithful structured literal encoding. -/
def literalStructuredShape : CodecShape :=
  .prod .unaryNat .bool

/--
A faithful explicit V2 presentation of the legacy structured literal encoding.

The carrier remains the project-local `SAT.Literal` structure, while the
identity records its complete `(unary variable, Boolean polarity)` layout.
It is intentionally a concrete lawful presentation rather than a structural
admission: the legacy carrier is not definitionally the standard product
carrier.
-/
def literalStructuredPresentation : LawfulEncodedType where
  encodedType := ComplexityReduction.Karp21.literalStructuredEncodedType
  representation := literalStructuredShape.identity
  faithful := ⟨ComplexityReduction.Karp21.literalStructuredEncodedType_encode_injective⟩

/-- The literal presentation retains precisely the existing structured literal encoder. -/
@[simp]
theorem literalStructuredPresentation_encodedType :
    literalStructuredPresentation.encodedType =
      ComplexityReduction.Karp21.literalStructuredEncodedType :=
  rfl

/-- The literal presentation retains its complete variable/polarity codec identity. -/
@[simp]
theorem literalStructuredPresentation_representation :
    literalStructuredPresentation.representation = literalStructuredShape.identity :=
  rfl

/-- The literal presentation carrier is exactly the legacy SAT literal syntax carrier. -/
theorem literalStructuredPresentation_carrier_eq_Literal :
    literalStructuredPresentation.Carrier = ComplexityReduction.SAT.Literal :=
  rfl

/-- The only executable encoding exposed by this presentation is the existing literal encoder. -/
@[simp]
theorem literalStructuredPresentation_encode
    (literal : literalStructuredPresentation.Carrier) :
    literalStructuredPresentation.encode literal =
      ComplexityReduction.Karp21.literalStructuredEncodedType.encode literal :=
  rfl

/-- The explicit list-of-structured-literals layout of the existing Clause encoding. -/
def clauseStructuredShape : CodecShape :=
  .list literalStructuredShape

/--
A faithful explicit V2 presentation of the legacy structured Clause encoding.

The carrier is the project-local `SAT.Clause` syntax (a list of literals),
and the representation identity records that its delimiters range over the
same explicit structured literal layout as `literalStructuredPresentation`.
This is a concrete lawful presentation, not an inferred codec admission.
-/
def clauseStructuredPresentation : LawfulEncodedType where
  encodedType := ComplexityReduction.Karp21.clauseStructuredEncodedType
  representation := clauseStructuredShape.identity
  faithful := ⟨ComplexityReduction.Karp21.clauseStructuredEncodedType_encode_injective⟩

/-- The Clause presentation retains precisely the existing structured Clause encoder. -/
@[simp]
theorem clauseStructuredPresentation_encodedType :
    clauseStructuredPresentation.encodedType =
      ComplexityReduction.Karp21.clauseStructuredEncodedType :=
  rfl

/-- The Clause presentation retains its complete literal-list codec identity. -/
@[simp]
theorem clauseStructuredPresentation_representation :
    clauseStructuredPresentation.representation = clauseStructuredShape.identity :=
  rfl

/-- The Clause presentation carrier is exactly the legacy SAT Clause syntax carrier. -/
theorem clauseStructuredPresentation_carrier_eq_Clause :
    clauseStructuredPresentation.Carrier = ComplexityReduction.SAT.Clause :=
  rfl

/-- The only executable encoding exposed by this presentation is the existing Clause encoder. -/
@[simp]
theorem clauseStructuredPresentation_encode
    (clause : clauseStructuredPresentation.Carrier) :
    clauseStructuredPresentation.encode clause =
      ComplexityReduction.Karp21.clauseStructuredEncodedType.encode clause :=
  rfl

/-- The explicit shape of the existing faithful structured CNF syntax encoding. -/
def cnfSATStructuredShape : CodecShape :=
  .list clauseStructuredShape

/-- A faithful explicit V2 presentation of the legacy structured CNF encoding. -/
def cnfSATStructuredPresentation : LawfulEncodedType where
  encodedType := ComplexityReduction.Karp21.cnfStructuredEncodedType
  representation := cnfSATStructuredShape.identity
  faithful := ⟨ComplexityReduction.Karp21.cnfStructuredEncodedType_encode_injective⟩

/-- The CNF presentation retains precisely the existing structured CNF encoder. -/
@[simp]
theorem cnfSATStructuredPresentation_encodedType :
    cnfSATStructuredPresentation.encodedType =
      ComplexityReduction.Karp21.cnfStructuredEncodedType :=
  rfl

/-- The CNF presentation retains its complete explicit structured-layout identity. -/
@[simp]
theorem cnfSATStructuredPresentation_representation :
    cnfSATStructuredPresentation.representation = cnfSATStructuredShape.identity :=
  rfl

/-- The CNF presentation carrier is exactly the legacy structured CNF syntax carrier. -/
theorem cnfSATStructuredPresentation_carrier_eq_CNF :
    cnfSATStructuredPresentation.Carrier = ComplexityReduction.SAT.CNF :=
  rfl

/-- The only executable encoding exposed by this presentation is the existing CNF encoder. -/
@[simp]
theorem cnfSATStructuredPresentation_encode (formula : cnfSATStructuredPresentation.Carrier) :
    cnfSATStructuredPresentation.encode formula =
      ComplexityReduction.Karp21.cnfStructuredEncodedType.encode formula :=
  rfl

/-- The exact CNF satisfiability predicate indexed by the custom CNF presentation. -/
def cnfSATStructuredProblemAt : ProblemAt cnfSATStructuredPresentation where
  isYes := ComplexityReduction.SAT.CNF.Satisfiable

/-- The custom CNF syntax is explicitly selected; this leaf exports no structural admission. -/
@[complexity_reduction_ir_typed_problem]
def cnfSATStructuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt cnfSATStructuredPresentation cnfSATStructuredProblemAt

/-- The CNF endpoint remains indexed by exactly the presentation defined above. -/
@[simp]
theorem cnfSATStructuredProblem_representation :
    cnfSATStructuredProblem.representation = cnfSATStructuredPresentation :=
  rfl

/-- The CNF endpoint backend projection retains the existing CNF encoder. -/
@[simp]
theorem cnfSATStructuredProblem_backendEndpoint_instance :
    cnfSATStructuredProblem.backendEndpoint.Instance =
      ComplexityReduction.Karp21.cnfStructuredEncodedType :=
  rfl

/-- The CNF endpoint retains the full custom structured-layout identity. -/
@[simp]
theorem cnfSATStructuredProblem_representationIdentity :
    cnfSATStructuredProblem.representationIdentity = cnfSATStructuredShape.identity :=
  rfl

/-- The exact CNF endpoint predicate is the semantic CNF satisfiability predicate. -/
@[simp]
theorem cnfSATStructuredProblemAt_isYes (formula : cnfSATStructuredPresentation.Carrier) :
    cnfSATStructuredProblemAt.isYes formula ↔ ComplexityReduction.SAT.CNF.Satisfiable formula :=
  Iff.rfl

@[simp]
theorem cnfSATStructuredProblem_accepts (formula : cnfSATStructuredProblem.Instance) :
    cnfSATStructuredProblem.accepts formula ↔ ComplexityReduction.SAT.CNF.Satisfiable formula :=
  Iff.rfl

/-- The explicit shape of the existing faithful structured bundled-3SAT syntax encoding. -/
def threeSATStructuredShape : CodecShape :=
  .list (.list (.prod .unaryNat .bool))

/-- A faithful explicit V2 presentation of the legacy structured bundled-3SAT encoding. -/
def threeSATStructuredPresentation : LawfulEncodedType where
  encodedType := ComplexityReduction.Karp21.threeCNFStructuredEncodedType
  representation := threeSATStructuredShape.identity
  faithful := ⟨ComplexityReduction.Karp21.threeCNFStructuredEncodedType_encode_injective⟩

/-- The bundled-3SAT presentation retains precisely the existing structured 3SAT encoder. -/
@[simp]
theorem threeSATStructuredPresentation_encodedType :
    threeSATStructuredPresentation.encodedType =
      ComplexityReduction.Karp21.threeCNFStructuredEncodedType :=
  rfl

/-- The bundled-3SAT presentation retains its complete explicit structured-layout identity. -/
@[simp]
theorem threeSATStructuredPresentation_representation :
    threeSATStructuredPresentation.representation = threeSATStructuredShape.identity :=
  rfl

/-- The bundled-3SAT presentation carrier is exactly the proof-carrying ThreeCNF syntax carrier. -/
theorem threeSATStructuredPresentation_carrier_eq_ThreeCNF :
    threeSATStructuredPresentation.Carrier = ComplexityReduction.SAT.ThreeCNF :=
  rfl

/--
The only executable encoding exposed by this presentation is the existing
bundled-3SAT encoder.
-/
@[simp]
theorem threeSATStructuredPresentation_encode (formula : threeSATStructuredPresentation.Carrier) :
    threeSATStructuredPresentation.encode formula =
      ComplexityReduction.Karp21.threeCNFStructuredEncodedType.encode formula :=
  rfl

/-- The exact bundled-3SAT satisfiability predicate indexed by its custom presentation. -/
def threeSATStructuredProblemAt : ProblemAt threeSATStructuredPresentation where
  isYes := ComplexityReduction.SAT.ThreeCNF.Satisfiable

/-- The bundled-3SAT syntax is explicitly selected; this leaf exports no structural admission. -/
@[complexity_reduction_ir_typed_problem]
def threeSATStructuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt threeSATStructuredPresentation threeSATStructuredProblemAt

/-- The bundled-3SAT endpoint remains indexed by exactly the presentation defined above. -/
@[simp]
theorem threeSATStructuredProblem_representation :
    threeSATStructuredProblem.representation = threeSATStructuredPresentation :=
  rfl

/-- The bundled-3SAT endpoint backend projection retains the existing bundled-3SAT encoder. -/
@[simp]
theorem threeSATStructuredProblem_backendEndpoint_instance :
    threeSATStructuredProblem.backendEndpoint.Instance =
      ComplexityReduction.Karp21.threeCNFStructuredEncodedType :=
  rfl

/-- The bundled-3SAT endpoint retains the full custom structured-layout identity. -/
@[simp]
theorem threeSATStructuredProblem_representationIdentity :
    threeSATStructuredProblem.representationIdentity = threeSATStructuredShape.identity :=
  rfl

/-- The exact bundled-3SAT endpoint predicate is the semantic bundled-3SAT predicate. -/
@[simp]
theorem threeSATStructuredProblemAt_isYes (formula : threeSATStructuredPresentation.Carrier) :
    threeSATStructuredProblemAt.isYes formula ↔
      ComplexityReduction.SAT.ThreeCNF.Satisfiable formula :=
  Iff.rfl

@[simp]
theorem threeSATStructuredProblem_accepts (formula : threeSATStructuredProblem.Instance) :
    threeSATStructuredProblem.accepts formula ↔
      ComplexityReduction.SAT.ThreeCNF.Satisfiable formula :=
  Iff.rfl

/-- The standard structured witness presentation for finite Boolean assignments. -/
abbrev finiteAssignmentPresentation : LawfulEncodedType :=
  StandardInstances.list StandardInstances.bool

/--
The finite-assignment witness presentation is structurally generated from the
exact standard Boolean presentation; no custom codec or bare equivalence is
used by the verifier adapter.
-/
@[complexity_reduction_ir_typed_presentation]
def finiteAssignmentStructuralCertificate :
    StructuralRepresentationCertificate finiteAssignmentPresentation.encodedType
      finiteAssignmentPresentation.representation :=
  StandardInstances.listStructuralCertificate StandardInstances.bool
    StandardInstances.boolStructuralCertificate

/-- The structural witness certificate reconstructs exactly the one finite-assignment presentation. -/
theorem finiteAssignmentStructuralCertificate_presentation :
    finiteAssignmentStructuralCertificate.toLawfulEncodedType = finiteAssignmentPresentation :=
  LawfulEncodedType.structuralCertificate_toLawfulEncodedType_eq _ _

/-- The declaration-local marker preserves the witness presentation's exact list-of-Boolean identity. -/
theorem finiteAssignmentStructuralCertificate_representation :
    finiteAssignmentStructuralCertificate.toLawfulEncodedType.representation =
      finiteAssignmentPresentation.representation := by
  simp only [finiteAssignmentStructuralCertificate_presentation]

end Satisfiability
end Karp21
end Problems
end ComplexityReduction
