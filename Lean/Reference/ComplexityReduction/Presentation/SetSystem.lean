/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Combinatorics.SetSystem
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Encoding.StandardInstances

/-!
Canonical V2 presentations for the structured set-system family.

The reusable set, set-family, and witness layouts are assembled from the
closed standard structural constructors.  In contrast, the existing
`SetSystemInput` and Karp target encoders are faithful custom wrappers around
those layouts.  They remain explicit user-selected lawful presentations: this
module deliberately exports no structural-admission certificate for any of
the custom wrapper encoders.
-/

namespace ComplexityReduction
namespace Presentation
namespace SetSystem

open Encoding
open ComplexityReduction.Combinatorics

/-- The exact unary layout of one set object. -/
def setObjectShape : CodecShape :=
  .list .unaryNat

/-- The canonical structural presentation of one finite set object. -/
abbrev setObjectPresentation : LawfulEncodedType :=
  StandardInstances.list StandardInstances.unaryNat

/-- One set object uses exactly the established structured set encoder. -/
@[simp]
theorem setObjectPresentation_encodedType :
    setObjectPresentation.encodedType = setStructuredEncodedType :=
  rfl

/-- The set-object representation identity records its unary element layout. -/
@[simp]
theorem setObjectPresentation_representation :
    setObjectPresentation.representation = setObjectShape.identity :=
  rfl

/-- One set object has a closed structural origin and may be selected automatically. -/
@[complexity_reduction_ir_typed_presentation]
def setObjectStructuralCertificate : setObjectPresentation.StructuralCertificate :=
  StandardInstances.listStructuralCertificate StandardInstances.unaryNat
    StandardInstances.unaryNatStructuralCertificate

/-- The set-object certificate reconstructs exactly the canonical unary-set presentation. -/
theorem setObjectStructuralCertificate_presentation :
    setObjectStructuralCertificate.toLawfulEncodedType = setObjectPresentation :=
  LawfulEncodedType.structuralCertificate_toLawfulEncodedType_eq _ _

/-- The exact layout of an ordered family of set objects. -/
def setFamilyShape : CodecShape :=
  .list setObjectShape

/-- The canonical structural presentation of an ordered family of set objects. -/
abbrev setFamilyPresentation : LawfulEncodedType :=
  StandardInstances.list setObjectPresentation

/-- The set-family presentation reuses exactly the established structured family encoder. -/
@[simp]
theorem setFamilyPresentation_encodedType :
    setFamilyPresentation.encodedType = setFamilyStructuredEncodedType :=
  rfl

/-- The set-family representation retains the full recursive object layout. -/
@[simp]
theorem setFamilyPresentation_representation :
    setFamilyPresentation.representation = setFamilyShape.identity :=
  rfl

/-- A set family is structurally generated from the exact set-object certificate. -/
@[complexity_reduction_ir_typed_presentation]
def setFamilyStructuralCertificate : setFamilyPresentation.StructuralCertificate :=
  StandardInstances.listStructuralCertificate setObjectPresentation setObjectStructuralCertificate

/-- A family presentation certificate reconstructs precisely the selected family presentation. -/
theorem setFamilyStructuralCertificate_presentation :
    setFamilyStructuralCertificate.toLawfulEncodedType = setFamilyPresentation :=
  LawfulEncodedType.structuralCertificate_toLawfulEncodedType_eq _ _

/-- The explicit layout of a set-system's universe size and ordered set family. -/
def setSystemStructuredShape : CodecShape :=
  .prod .unaryNat setFamilyShape

/-- The faithful, explicitly selected presentation of legacy structured set-system inputs. -/
def structuredPresentation : LawfulEncodedType where
  encodedType := setSystemStructuredEncodedType
  representation := setSystemStructuredShape.identity
  faithful := ⟨setSystemStructuredEncodedType_encode_injective⟩

/-- The set-system presentation retains precisely the existing structured wrapper encoder. -/
@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = setSystemStructuredEncodedType :=
  rfl

/-- The custom set-system wrapper retains the complete explicit layout identity. -/
@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = setSystemStructuredShape.identity :=
  rfl

/-- The presentation carrier is exactly the legacy set-system input carrier. -/
theorem structuredPresentation_carrier_eq_SetSystemInput :
    structuredPresentation.Carrier = SetSystemInput :=
  rfl

/-- The only encoder exposed by the set-system presentation is the legacy structured encoder. -/
@[simp]
theorem structuredPresentation_encode (input : structuredPresentation.Carrier) :
    structuredPresentation.encode input = setSystemStructuredEncodedType.encode input :=
  rfl

/-- The exact well-formedness predicate at the explicit structured set-system presentation. -/
def wellFormedProblemAt : ProblemAt structuredPresentation where
  isYes := SetSystemWellFormed

/--
The V2 endpoint for well-formed structured set-system instances.  The custom
wrapper has no closed structural origin, so this declaration intentionally
does not expose automatic-presentation admission.
-/
@[complexity_reduction_ir_typed_problem]
def wellFormedProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation wellFormedProblemAt

/-- The well-formedness endpoint is indexed by the exact custom set-system presentation. -/
@[simp]
theorem wellFormedProblem_representation :
    wellFormedProblem.representation = structuredPresentation :=
  rfl

/-- The endpoint backend projection retains exactly the legacy structured set-system encoder. -/
@[simp]
theorem wellFormedProblem_backendEndpoint_instance :
    wellFormedProblem.backendEndpoint.Instance = setSystemStructuredEncodedType :=
  rfl

/-- The endpoint identity retains the full explicit set-system layout. -/
@[simp]
theorem wellFormedProblem_representationIdentity :
    wellFormedProblem.representationIdentity = setSystemStructuredShape.identity :=
  rfl

/-- The typed set-system predicate is definitionally the legacy well-formedness predicate. -/
@[simp]
theorem wellFormedProblemAt_isYes (input : structuredPresentation.Carrier) :
    wellFormedProblemAt.isYes input ↔ SetSystemWellFormed input :=
  Iff.rfl

@[simp]
theorem wellFormedProblem_accepts (input : wellFormedProblem.Instance) :
    wellFormedProblem.accepts input ↔ SetSystemWellFormed input :=
  Iff.rfl

/-- The common custom layout of Karp target instances formed from a system and unary bound. -/
def boundedTargetShape : CodecShape :=
  .prod setSystemStructuredShape .unaryNat

/-- The exact witness representation for selected set families. -/
abbrev selectedSetFamilyWitnessPresentation : LawfulEncodedType :=
  setFamilyPresentation

/-- A selected-family witness is definitionally the canonical set-family presentation. -/
theorem selectedSetFamilyWitnessPresentation_eq_setFamilyPresentation :
    selectedSetFamilyWitnessPresentation = setFamilyPresentation :=
  rfl

/-- The selected-family witness keeps the complete nested set-family representation identity. -/
@[simp]
theorem selectedSetFamilyWitnessPresentation_representation :
    selectedSetFamilyWitnessPresentation.representation = setFamilyShape.identity :=
  rfl

/-- Selected set-family witnesses inherit the closed structural family certificate. -/
def selectedSetFamilyWitnessStructuralCertificate :
    selectedSetFamilyWitnessPresentation.StructuralCertificate :=
  setFamilyStructuralCertificate

/-- The selected-family witness certificate reconstructs its one exact presentation. -/
theorem selectedSetFamilyWitnessStructuralCertificate_presentation :
    selectedSetFamilyWitnessStructuralCertificate.toLawfulEncodedType =
      selectedSetFamilyWitnessPresentation :=
  LawfulEncodedType.structuralCertificate_toLawfulEncodedType_eq _ _

/-- The exact witness representation for a selected hitting set of unary objects. -/
abbrev hittingSetWitnessPresentation : LawfulEncodedType :=
  setObjectPresentation

/-- A hitting-set witness is definitionally the canonical unary set-object presentation. -/
theorem hittingSetWitnessPresentation_eq_setObjectPresentation :
    hittingSetWitnessPresentation = setObjectPresentation :=
  rfl

/-- The hitting-set witness keeps the exact unary-set representation identity. -/
@[simp]
theorem hittingSetWitnessPresentation_representation :
    hittingSetWitnessPresentation.representation = setObjectShape.identity :=
  rfl

/-- Hitting-set witnesses inherit the closed structural set-object certificate. -/
def hittingSetWitnessStructuralCertificate : hittingSetWitnessPresentation.StructuralCertificate :=
  setObjectStructuralCertificate

/-- The hitting-set witness certificate reconstructs its one exact presentation. -/
theorem hittingSetWitnessStructuralCertificate_presentation :
    hittingSetWitnessStructuralCertificate.toLawfulEncodedType = hittingSetWitnessPresentation :=
  LawfulEncodedType.structuralCertificate_toLawfulEncodedType_eq _ _

/-- The faithful, explicit presentation of structured Set Packing instances. -/
def setPackingStructuredPresentation : LawfulEncodedType where
  encodedType := setPackingStructuredEncodedType
  representation := boundedTargetShape.identity
  faithful := ⟨setPackingStructuredEncodedType_encode_injective⟩

/-- The Set Packing presentation retains exactly its legacy structured encoder. -/
@[simp]
theorem setPackingStructuredPresentation_encodedType :
    setPackingStructuredPresentation.encodedType = setPackingStructuredEncodedType :=
  rfl

/-- The Set Packing presentation retains the full source-and-bound layout identity. -/
@[simp]
theorem setPackingStructuredPresentation_representation :
    setPackingStructuredPresentation.representation = boundedTargetShape.identity :=
  rfl

/-- The exact Set Packing predicate at its lawful presentation. -/
def setPackingStructuredProblemAt : ProblemAt setPackingStructuredPresentation where
  isYes := SetPacking

/-- The typed endpoint for the existing structured Set Packing decision problem. -/
@[complexity_reduction_ir_typed_problem]
def setPackingStructuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt setPackingStructuredPresentation setPackingStructuredProblemAt

/-- The Set Packing endpoint is indexed by its exact explicit target presentation. -/
@[simp]
theorem setPackingStructuredProblem_representation :
    setPackingStructuredProblem.representation = setPackingStructuredPresentation :=
  rfl

/-- The Set Packing endpoint retains the complete source-and-bound representation identity. -/
@[simp]
theorem setPackingStructuredProblem_representationIdentity :
    setPackingStructuredProblem.representationIdentity = boundedTargetShape.identity :=
  rfl

/-- The typed Set Packing endpoint projects exactly the existing structured decision problem. -/
@[simp]
theorem setPackingStructuredProblem_backendEndpoint_eq_legacy :
    setPackingStructuredProblem.backendEndpoint = setPackingStructuredDecisionProblem :=
  rfl

/-- The typed Set Packing predicate is definitionally the existing semantic predicate. -/
@[simp]
theorem setPackingStructuredProblem_accepts (input : setPackingStructuredProblem.Instance) :
    setPackingStructuredProblem.accepts input ↔ SetPacking input :=
  Iff.rfl

/-- The fixed-presentation Set Packing predicate is exactly the legacy semantic predicate. -/
@[simp]
theorem setPackingStructuredProblemAt_isYes (input : setPackingStructuredPresentation.Carrier) :
    setPackingStructuredProblemAt.isYes input ↔ SetPacking input :=
  Iff.rfl

/-- The faithful, explicit presentation of structured Set Covering instances. -/
def setCoveringStructuredPresentation : LawfulEncodedType where
  encodedType := setCoveringStructuredEncodedType
  representation := boundedTargetShape.identity
  faithful := ⟨setCoveringStructuredEncodedType_encode_injective⟩

/-- The Set Covering presentation retains exactly its legacy structured encoder. -/
@[simp]
theorem setCoveringStructuredPresentation_encodedType :
    setCoveringStructuredPresentation.encodedType = setCoveringStructuredEncodedType :=
  rfl

/-- The Set Covering presentation retains the full source-and-bound layout identity. -/
@[simp]
theorem setCoveringStructuredPresentation_representation :
    setCoveringStructuredPresentation.representation = boundedTargetShape.identity :=
  rfl

/-- The exact Set Covering predicate at its lawful presentation. -/
def setCoveringStructuredProblemAt : ProblemAt setCoveringStructuredPresentation where
  isYes := SetCovering

/-- The typed endpoint for the existing structured Set Covering decision problem. -/
@[complexity_reduction_ir_typed_problem]
def setCoveringStructuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt setCoveringStructuredPresentation setCoveringStructuredProblemAt

/-- The Set Covering endpoint is indexed by its exact explicit target presentation. -/
@[simp]
theorem setCoveringStructuredProblem_representation :
    setCoveringStructuredProblem.representation = setCoveringStructuredPresentation :=
  rfl

/-- The Set Covering endpoint retains the complete source-and-bound representation identity. -/
@[simp]
theorem setCoveringStructuredProblem_representationIdentity :
    setCoveringStructuredProblem.representationIdentity = boundedTargetShape.identity :=
  rfl

/-- The typed Set Covering endpoint projects exactly the existing structured decision problem. -/
@[simp]
theorem setCoveringStructuredProblem_backendEndpoint_eq_legacy :
    setCoveringStructuredProblem.backendEndpoint = setCoveringStructuredDecisionProblem :=
  rfl

/-- The typed Set Covering predicate is definitionally the existing semantic predicate. -/
@[simp]
theorem setCoveringStructuredProblem_accepts (input : setCoveringStructuredProblem.Instance) :
    setCoveringStructuredProblem.accepts input ↔ SetCovering input :=
  Iff.rfl

/-- The fixed-presentation Set Covering predicate is exactly the legacy semantic predicate. -/
@[simp]
theorem setCoveringStructuredProblemAt_isYes (input : setCoveringStructuredPresentation.Carrier) :
    setCoveringStructuredProblemAt.isYes input ↔ SetCovering input :=
  Iff.rfl

/-- The faithful, explicit presentation of structured Exact Cover instances. -/
def exactCoverStructuredPresentation : LawfulEncodedType where
  encodedType := exactCoverStructuredEncodedType
  representation := setSystemStructuredShape.identity
  faithful := ⟨exactCoverStructuredEncodedType_encode_injective⟩

/-- The Exact Cover presentation retains exactly its legacy structured encoder. -/
@[simp]
theorem exactCoverStructuredPresentation_encodedType :
    exactCoverStructuredPresentation.encodedType = exactCoverStructuredEncodedType :=
  rfl

/-- The Exact Cover presentation retains the complete set-system layout identity. -/
@[simp]
theorem exactCoverStructuredPresentation_representation :
    exactCoverStructuredPresentation.representation = setSystemStructuredShape.identity :=
  rfl

/-- The exact Exact Cover predicate at its lawful presentation. -/
def exactCoverStructuredProblemAt : ProblemAt exactCoverStructuredPresentation where
  isYes := ExactCover

/-- The typed endpoint for the existing structured Exact Cover decision problem. -/
@[complexity_reduction_ir_typed_problem]
def exactCoverStructuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt exactCoverStructuredPresentation exactCoverStructuredProblemAt

/-- The Exact Cover endpoint is indexed by its exact explicit target presentation. -/
@[simp]
theorem exactCoverStructuredProblem_representation :
    exactCoverStructuredProblem.representation = exactCoverStructuredPresentation :=
  rfl

/-- The Exact Cover endpoint retains the complete set-system representation identity. -/
@[simp]
theorem exactCoverStructuredProblem_representationIdentity :
    exactCoverStructuredProblem.representationIdentity = setSystemStructuredShape.identity :=
  rfl

/-- The typed Exact Cover endpoint projects exactly the existing structured decision problem. -/
@[simp]
theorem exactCoverStructuredProblem_backendEndpoint_eq_legacy :
    exactCoverStructuredProblem.backendEndpoint = exactCoverStructuredDecisionProblem :=
  rfl

/-- The typed Exact Cover predicate is definitionally the existing semantic predicate. -/
@[simp]
theorem exactCoverStructuredProblem_accepts (input : exactCoverStructuredProblem.Instance) :
    exactCoverStructuredProblem.accepts input ↔ ExactCover input :=
  Iff.rfl

/-- The fixed-presentation Exact Cover predicate is exactly the legacy semantic predicate. -/
@[simp]
theorem exactCoverStructuredProblemAt_isYes (input : exactCoverStructuredPresentation.Carrier) :
    exactCoverStructuredProblemAt.isYes input ↔ ExactCover input :=
  Iff.rfl

/-- The faithful, explicit presentation of structured Hitting Set instances. -/
def hittingSetStructuredPresentation : LawfulEncodedType where
  encodedType := hittingSetStructuredEncodedType
  representation := boundedTargetShape.identity
  faithful := ⟨hittingSetStructuredEncodedType_encode_injective⟩

/-- The Hitting Set presentation retains exactly its legacy structured encoder. -/
@[simp]
theorem hittingSetStructuredPresentation_encodedType :
    hittingSetStructuredPresentation.encodedType = hittingSetStructuredEncodedType :=
  rfl

/-- The Hitting Set presentation retains the full source-and-bound layout identity. -/
@[simp]
theorem hittingSetStructuredPresentation_representation :
    hittingSetStructuredPresentation.representation = boundedTargetShape.identity :=
  rfl

/-- The exact Hitting Set predicate at its lawful presentation. -/
def hittingSetStructuredProblemAt : ProblemAt hittingSetStructuredPresentation where
  isYes := HittingSet

/-- The typed endpoint for the existing structured Hitting Set decision problem. -/
@[complexity_reduction_ir_typed_problem]
def hittingSetStructuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt hittingSetStructuredPresentation hittingSetStructuredProblemAt

/-- The Hitting Set endpoint is indexed by its exact explicit target presentation. -/
@[simp]
theorem hittingSetStructuredProblem_representation :
    hittingSetStructuredProblem.representation = hittingSetStructuredPresentation :=
  rfl

/-- The Hitting Set endpoint retains the complete source-and-bound representation identity. -/
@[simp]
theorem hittingSetStructuredProblem_representationIdentity :
    hittingSetStructuredProblem.representationIdentity = boundedTargetShape.identity :=
  rfl

/-- The typed Hitting Set endpoint projects exactly the existing structured decision problem. -/
@[simp]
theorem hittingSetStructuredProblem_backendEndpoint_eq_legacy :
    hittingSetStructuredProblem.backendEndpoint = hittingSetStructuredDecisionProblem :=
  rfl

/-- The typed Hitting Set predicate is definitionally the existing semantic predicate. -/
@[simp]
theorem hittingSetStructuredProblem_accepts (input : hittingSetStructuredProblem.Instance) :
    hittingSetStructuredProblem.accepts input ↔ HittingSet input :=
  Iff.rfl

/-- The fixed-presentation Hitting Set predicate is exactly the legacy semantic predicate. -/
@[simp]
theorem hittingSetStructuredProblemAt_isYes (input : hittingSetStructuredPresentation.Carrier) :
    hittingSetStructuredProblemAt.isYes input ↔ HittingSet input :=
  Iff.rfl

/-
No `UniversalRelIR` erasure is exported for this family.  The available
one-way erasure API is indexed by `V2.Schema.RelInstance`, while the existing
SetSystem encodings are `SetSystemInput` wrappers; this leaf has no exact
SetSystemInput-to-RelInstance construction or semantic theorem from which an
erased presentation could be certified.  The canonical SetSystem presentations
therefore remain their direct structured encodings.
-/

end SetSystem
end Presentation
end ComplexityReduction
