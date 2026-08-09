/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Encoding.StandardInstances
import ComplexityReduction.Program.Primitive

/-!
Typed V2 registry identities.

Each identity is a value in a type indexed by the exact V2 term it identifies.
There is no serialized identifier, hash, or carrier-only fallback.  An exporter
can therefore recover endpoints from an elaborated declaration type without
accepting external metadata as a trusted identity source.
-/

namespace ComplexityReduction
namespace Registry

open Encoding Program

/--
An identity for one exact lawful representation and one structural shape.
The presentation is already a type index, so this ID retains the complete
encoder-bound identity derived from that exact `LawfulEncodedType`; the shape
is a compatibility projection rather than the registry's sole identity.
-/
inductive RepresentationInstanceId (presentation : LawfulEncodedType) :
    CodecShape.Identity → Type 2 where
  | of : RepresentationInstanceId presentation presentation.representation

namespace RepresentationInstanceId

/-- Create the identity attached to exactly the supplied lawful presentation. -/
def ofLawfulEncodedType (presentation : LawfulEncodedType) :
    RepresentationInstanceId presentation presentation.representation :=
  .of

/-- Any representation identity value exposes exactly the representation identity in its index. -/
theorem shape_eq_representation {presentation : LawfulEncodedType} {shape : CodecShape.Identity}
    (id : RepresentationInstanceId presentation shape) :
    shape = presentation.representation := by
  cases id
  rfl

/-- Expose the complete encoder-bound identity carried by a representation ID's presentation index. -/
def encoderBoundIdentity {presentation : LawfulEncodedType} {shape : CodecShape.Identity}
    (_ : RepresentationInstanceId presentation shape) :
    EncoderBoundIdentity :=
  presentation.encoderBoundIdentity

/-- The exposed encoder-bound identity is precisely the identity derived from the presentation. -/
theorem encoderBoundIdentity_eq_lawful {presentation : LawfulEncodedType}
    {shape : CodecShape.Identity} (id : RepresentationInstanceId presentation shape) :
    id.encoderBoundIdentity = presentation.encoderBoundIdentity :=
  rfl

/-- The structural component of the exposed codec identity agrees with the legacy shape index. -/
theorem encoderBoundIdentity_structuralIdentity_eq_shape {presentation : LawfulEncodedType}
    {shape : CodecShape.Identity} (id : RepresentationInstanceId presentation shape) :
    id.encoderBoundIdentity.structuralIdentity = shape := by
  cases id
  rfl

/-- At one complete lawful presentation and representation identity, the ID has one inhabitant. -/
theorem subsingleton {presentation : LawfulEncodedType} {shape : CodecShape.Identity}
    (first second : RepresentationInstanceId presentation shape) : first = second := by
  cases first
  cases second
  rfl

/-- An ID can be reindexed only along equality of the full lawful presentation. -/
def reindex {left right : LawfulEncodedType}
    (id : RepresentationInstanceId left left.representation) (equality : left = right) :
    RepresentationInstanceId right right.representation := by
  cases equality
  exact id

/-- Equality of exact presentations preserves their complete representation identities. -/
theorem presentation_eq_implies_representation_eq {left right : LawfulEncodedType}
    (equality : left = right) : left.representation = right.representation :=
  congrArg (fun presentation : LawfulEncodedType => presentation.representation) equality

/-- Equality of exact presentations preserves their complete encoder-bound identities. -/
theorem presentation_eq_implies_encoderBoundIdentity_eq {left right : LawfulEncodedType}
    (equality : left = right) : left.encoderBoundIdentity = right.encoderBoundIdentity :=
  congrArg LawfulEncodedType.encoderBoundIdentity equality

/-- Different codec identities prevent their lawful presentations and IDs from being reindexed. -/
theorem presentation_ne_of_representation_ne {left right : LawfulEncodedType}
    (representation_ne : left.representation ≠ right.representation) : left ≠ right :=
  fun equality => representation_ne (presentation_eq_implies_representation_eq equality)

/-- Different complete codecs prevent reindexing even when their shapes and carriers agree. -/
theorem presentation_ne_of_encoderBoundIdentity_ne {left right : LawfulEncodedType}
    (identityNe : left.encoderBoundIdentity ≠ right.encoderBoundIdentity) : left ≠ right :=
  fun equality => identityNe (presentation_eq_implies_encoderBoundIdentity_eq equality)

/-- Standard unary and binary natural presentations cannot be identified. -/
theorem standardUnaryNat_ne_standardBinaryNat :
    StandardInstances.unaryNat ≠ StandardInstances.binaryNat := by
  exact presentation_ne_of_representation_ne
    StandardInstances.unaryNat_representation_ne_binaryNat_representation

/-- Unary and binary naturals share a carrier but cannot share a representation identity. -/
theorem standardUnaryNat_same_carrier_different_representation :
    StandardInstances.unaryNat.Carrier = StandardInstances.binaryNat.Carrier ∧
      StandardInstances.unaryNat.representation ≠ StandardInstances.binaryNat.representation :=
  ⟨StandardInstances.unaryNat_carrier_eq_binaryNat_carrier,
    StandardInstances.unaryNat_representation_ne_binaryNat_representation⟩

/-- A unary-to-binary ID reindex would require impossible full presentation equality. -/
theorem standardUnaryNat_reindex_to_standardBinaryNat_impossible
    (_ : RepresentationInstanceId StandardInstances.unaryNat
      StandardInstances.unaryNat.representation)
    (equality : StandardInstances.unaryNat = StandardInstances.binaryNat) : False :=
  standardUnaryNat_ne_standardBinaryNat equality

end RepresentationInstanceId

/-- An identity for one exact typed problem presentation. -/
inductive ProblemInstanceId (problem : PresentedProblem) : Type 2 where
  | of : ProblemInstanceId problem

namespace ProblemInstanceId

/-- Create the identity attached to exactly the supplied presented problem. -/
def ofPresentedProblem (problem : PresentedProblem) : ProblemInstanceId problem :=
  .of

/-- Reindex a problem ID only along equality of the complete presented-problem term. -/
def reindex {left right : PresentedProblem}
    (id : ProblemInstanceId left) (equality : left = right) : ProblemInstanceId right := by
  cases equality
  exact id

/-- At one complete presented-problem term, the problem identity has one inhabitant. -/
theorem subsingleton {problem : PresentedProblem}
    (first second : ProblemInstanceId problem) : first = second := by
  cases first
  cases second
  rfl

/-- Equality of problem terms entails equality of their exact lawful presentations. -/
theorem problem_eq_implies_presentation_eq {left right : PresentedProblem}
    (equality : left = right) : left.representation = right.representation :=
  congrArg (fun problem : PresentedProblem => problem.representation) equality

/-- Equality of problem terms retains the complete encoder-bound representation identity. -/
theorem problem_eq_implies_encoderBoundIdentity_eq {left right : PresentedProblem}
    (equality : left = right) :
    left.representation.encoderBoundIdentity = right.representation.encoderBoundIdentity :=
  congrArg (fun problem : PresentedProblem => problem.representation.encoderBoundIdentity) equality

/-- Different presentation identities prevent complete presented-problem terms from being equal. -/
theorem problem_ne_of_representation_ne {left right : PresentedProblem}
    (representation_ne : left.representation ≠ right.representation) : left ≠ right :=
  fun equality => representation_ne (problem_eq_implies_presentation_eq equality)

/-- Same-shape problems remain distinct whenever their complete codecs differ. -/
theorem problem_ne_of_encoderBoundIdentity_ne {left right : PresentedProblem}
    (identityNe : left.representation.encoderBoundIdentity ≠
      right.representation.encoderBoundIdentity) : left ≠ right :=
  fun equality => identityNe (problem_eq_implies_encoderBoundIdentity_eq equality)

/-- Recover the exact representation identity required by this presented problem. -/
def representationId (problem : PresentedProblem) :
    RepresentationInstanceId problem.representation problem.representation.representation :=
  .of

/-- Recover the exact encoder-bound representation identity of a problem endpoint. -/
def representationEncoderBoundIdentity (problem : PresentedProblem) : EncoderBoundIdentity :=
  (representationId problem).encoderBoundIdentity

/-- The endpoint codec identity is mechanically fixed by its lawful presentation. -/
@[simp]
theorem representationEncoderBoundIdentity_eq_lawful (problem : PresentedProblem) :
    representationEncoderBoundIdentity problem = problem.representation.encoderBoundIdentity :=
  rfl

/--
The complete identity bundle for one presented-problem endpoint.

The problem declaration and the representation it uses remain separate
dependent fields: a registry client which needs both cannot reconstruct this
bundle from the endpoint carrier, a descriptor string, or a codec hash.  Its
representation component exposes the complete encoder-bound identity, not
only the compatibility shape projection.
-/
structure EndpointIds (endpoint : PresentedProblem) where
  problemId : ProblemInstanceId endpoint
  representationId :
    RepresentationInstanceId endpoint.representation endpoint.representation.representation

/-- Recover the complete typed identity bundle fixed by a presented-problem term. -/
def endpointIds (problem : PresentedProblem) : EndpointIds problem where
  problemId := ofPresentedProblem problem
  representationId := representationId problem

/-- Expose the complete encoder-bound representation identity in an endpoint bundle. -/
def EndpointIds.encoderBoundRepresentationIdentity {endpoint : PresentedProblem}
    (ids : EndpointIds endpoint) : EncoderBoundIdentity :=
  ids.representationId.encoderBoundIdentity

/-- An endpoint bundle's codec identity is fixed by its exact endpoint presentation. -/
theorem EndpointIds.encoderBoundRepresentationIdentity_eq_lawful {endpoint : PresentedProblem}
    (ids : EndpointIds endpoint) :
    ids.encoderBoundRepresentationIdentity = endpoint.representation.encoderBoundIdentity :=
  RepresentationInstanceId.encoderBoundIdentity_eq_lawful ids.representationId

/--
Transport a complete endpoint identity bundle only along equality of the
complete presented-problem term.  In particular, equality of endpoint
carriers is not an admissible argument to this operation.
-/
def EndpointIds.reindex {left right : PresentedProblem}
    (ids : EndpointIds left) (equality : left = right) : EndpointIds right := by
  cases equality
  exact ids

/--
Reindexing an endpoint bundle retains the exact representation identity of
the target presented problem.  The conclusion is indexed by `right` itself,
not by its carrier, a descriptor name, or serialized metadata.
-/
theorem EndpointIds.reindex_representationId {left right : PresentedProblem}
    (ids : EndpointIds left) (equality : left = right) :
    (EndpointIds.reindex ids equality).representationId =
      ProblemInstanceId.representationId right := by
  cases equality
  exact RepresentationInstanceId.subsingleton _ _

/-- Reindexing an endpoint bundle preserves the complete target codec identity. -/
theorem EndpointIds.reindex_encoderBoundRepresentationIdentity {left right : PresentedProblem}
    (ids : EndpointIds left) (equality : left = right) :
    (EndpointIds.reindex ids equality).encoderBoundRepresentationIdentity =
      right.representation.encoderBoundIdentity := by
  cases equality
  exact ids.encoderBoundRepresentationIdentity_eq_lawful

/-- The problem component of a canonical endpoint bundle is its exact problem identity. -/
@[simp]
theorem endpointIds_problem (problem : PresentedProblem) :
    (endpointIds problem).problemId = ofPresentedProblem problem :=
  rfl

/-- The representation component of a canonical endpoint bundle is its exact representation ID. -/
@[simp]
theorem endpointIds_representation (problem : PresentedProblem) :
    (endpointIds problem).representationId = representationId problem :=
  rfl

/-- The canonical endpoint bundle exposes exactly its endpoint's full codec identity. -/
@[simp]
theorem endpointIds_encoderBoundRepresentationIdentity (problem : PresentedProblem) :
    (endpointIds problem).encoderBoundRepresentationIdentity =
      problem.representation.encoderBoundIdentity :=
  (endpointIds problem).encoderBoundRepresentationIdentity_eq_lawful

/-- A complete endpoint-identity bundle has one inhabitant at an exact presented problem. -/
theorem endpointIds_subsingleton {problem : PresentedProblem}
    (first second : EndpointIds problem) : first = second := by
  cases first with
  | mk firstProblem firstRepresentation =>
      cases second with
      | mk secondProblem secondRepresentation =>
          cases subsingleton firstProblem secondProblem
          cases RepresentationInstanceId.subsingleton firstRepresentation secondRepresentation
          rfl

end ProblemInstanceId

/-- An identity for one exact direct-TM-backed V2 primitive declaration term. -/
inductive AtomInstanceId : {source target : LawfulEncodedType} →
    Primitive source target → Type 2 where
  | of {source target : LawfulEncodedType} (primitive : Primitive source target) :
      AtomInstanceId primitive

namespace AtomInstanceId

/-- Create the identity attached to exactly the supplied indexed primitive. -/
def ofPrimitive {source target : LawfulEncodedType} (primitive : Primitive source target) :
    AtomInstanceId primitive :=
  .of primitive

/-- Reindex an atom identity only along equality of the exact primitive declaration term. -/
def reindex {source target : LawfulEncodedType} {left right : Primitive source target}
    (id : AtomInstanceId left) (equality : left = right) : AtomInstanceId right := by
  cases equality
  exact id

/-- At one exact direct-TM-backed primitive term, the atom identity has one inhabitant. -/
theorem subsingleton {source target : LawfulEncodedType} {primitive : Primitive source target}
    (first second : AtomInstanceId primitive) : first = second := by
  cases first
  cases second
  rfl

/-- Recover the exact source representation identity carried by an atom endpoint. -/
def sourceRepresentationId {source target : LawfulEncodedType} (_ : Primitive source target) :
    RepresentationInstanceId source source.representation :=
  .of

/-- Recover the exact target representation identity carried by an atom endpoint. -/
def targetRepresentationId {source target : LawfulEncodedType} (_ : Primitive source target) :
    RepresentationInstanceId target target.representation :=
  .of

/-- Recover the full encoder-bound identity of a primitive's source endpoint. -/
def sourceEncoderBoundIdentity {source target : LawfulEncodedType} (primitive : Primitive source target) :
    EncoderBoundIdentity :=
  (sourceRepresentationId primitive).encoderBoundIdentity

/-- Recover the full encoder-bound identity of a primitive's target endpoint. -/
def targetEncoderBoundIdentity {source target : LawfulEncodedType} (primitive : Primitive source target) :
    EncoderBoundIdentity :=
  (targetRepresentationId primitive).encoderBoundIdentity

/-- A primitive source identity is indexed by its exact source codec. -/
@[simp]
theorem sourceEncoderBoundIdentity_eq_lawful {source target : LawfulEncodedType}
    (primitive : Primitive source target) :
    sourceEncoderBoundIdentity primitive = source.encoderBoundIdentity :=
  rfl

/-- A primitive target identity is indexed by its exact target codec. -/
@[simp]
theorem targetEncoderBoundIdentity_eq_lawful {source target : LawfulEncodedType}
    (primitive : Primitive source target) :
    targetEncoderBoundIdentity primitive = target.encoderBoundIdentity :=
  rfl

/--
The two endpoint representation identities recovered from one exact primitive.
The primitive occurs in the index, so this bundle can only be obtained after
Lean has fixed both typed V2 endpoints; carrier equality and declaration names
do not participate in its construction.
-/
structure EndpointIds {source target : LawfulEncodedType} (primitive : Primitive source target) where
  source : RepresentationInstanceId source source.representation
  target : RepresentationInstanceId target target.representation

/-- Recover both endpoint identities from one exact typed primitive. -/
def endpointIds {source target : LawfulEncodedType} (primitive : Primitive source target) :
    EndpointIds primitive where
  source := sourceRepresentationId primitive
  target := targetRepresentationId primitive

/-- Expose the source's complete encoder-bound identity in a primitive endpoint bundle. -/
def EndpointIds.sourceEncoderBoundIdentity {source target : LawfulEncodedType}
    {primitive : Primitive source target} (ids : EndpointIds primitive) : EncoderBoundIdentity :=
  ids.source.encoderBoundIdentity

/-- Expose the target's complete encoder-bound identity in a primitive endpoint bundle. -/
def EndpointIds.targetEncoderBoundIdentity {source target : LawfulEncodedType}
    {primitive : Primitive source target} (ids : EndpointIds primitive) : EncoderBoundIdentity :=
  ids.target.encoderBoundIdentity

/-- The source bundle component is fixed by the primitive's exact source presentation. -/
theorem EndpointIds.sourceEncoderBoundIdentity_eq_lawful {source target : LawfulEncodedType}
    {primitive : Primitive source target} (ids : EndpointIds primitive) :
    ids.sourceEncoderBoundIdentity = source.encoderBoundIdentity :=
  RepresentationInstanceId.encoderBoundIdentity_eq_lawful ids.source

/-- The target bundle component is fixed by the primitive's exact target presentation. -/
theorem EndpointIds.targetEncoderBoundIdentity_eq_lawful {source target : LawfulEncodedType}
    {primitive : Primitive source target} (ids : EndpointIds primitive) :
    ids.targetEncoderBoundIdentity = target.encoderBoundIdentity :=
  RepresentationInstanceId.encoderBoundIdentity_eq_lawful ids.target

/-- Any source endpoint reindex requires equality of the complete source codec identity. -/
theorem EndpointIds.source_reindex_requires_encoderBoundIdentity_eq
    {source target source' : LawfulEncodedType} {primitive : Primitive source target}
    (ids : EndpointIds primitive) (equality : source = source') :
    ids.sourceEncoderBoundIdentity = source'.encoderBoundIdentity := by
  rw [ids.sourceEncoderBoundIdentity_eq_lawful]
  exact congrArg LawfulEncodedType.encoderBoundIdentity equality

/-- Any target endpoint reindex requires equality of the complete target codec identity. -/
theorem EndpointIds.target_reindex_requires_encoderBoundIdentity_eq
    {source target target' : LawfulEncodedType} {primitive : Primitive source target}
    (ids : EndpointIds primitive) (equality : target = target') :
    ids.targetEncoderBoundIdentity = target'.encoderBoundIdentity := by
  rw [ids.targetEncoderBoundIdentity_eq_lawful]
  exact congrArg LawfulEncodedType.encoderBoundIdentity equality

/-- The source endpoint in the canonical bundle is exactly the primitive's source identity. -/
@[simp]
theorem endpointIds_source {source target : LawfulEncodedType} (primitive : Primitive source target) :
    (endpointIds primitive).source = sourceRepresentationId primitive :=
  rfl

/-- The target endpoint in the canonical bundle is exactly the primitive's target identity. -/
@[simp]
theorem endpointIds_target {source target : LawfulEncodedType} (primitive : Primitive source target) :
    (endpointIds primitive).target = targetRepresentationId primitive :=
  rfl

/-- The canonical primitive bundle exposes its exact source codec identity. -/
@[simp]
theorem endpointIds_sourceEncoderBoundIdentity {source target : LawfulEncodedType}
    (primitive : Primitive source target) :
    (endpointIds primitive).sourceEncoderBoundIdentity = source.encoderBoundIdentity :=
  (endpointIds primitive).sourceEncoderBoundIdentity_eq_lawful

/-- The canonical primitive bundle exposes its exact target codec identity. -/
@[simp]
theorem endpointIds_targetEncoderBoundIdentity {source target : LawfulEncodedType}
    (primitive : Primitive source target) :
    (endpointIds primitive).targetEncoderBoundIdentity = target.encoderBoundIdentity :=
  (endpointIds primitive).targetEncoderBoundIdentity_eq_lawful

/--
The complete atom bundle for a direct-TM primitive declaration.

Both representation identities are indexed by the primitive's already
elaborated source and target presentations, while `atom` is indexed by the
primitive declaration itself.  Thus neither an endpoint carrier nor external
metadata can retag an atom at another representation.
-/
structure IdentityBundle {source target : LawfulEncodedType} (primitive : Primitive source target) where
  atom : AtomInstanceId primitive
  endpoints : EndpointIds primitive

/-- Recover every typed identity fixed by one exact direct-TM primitive declaration. -/
def identityBundle {source target : LawfulEncodedType} (primitive : Primitive source target) :
    IdentityBundle primitive where
  atom := ofPrimitive primitive
  endpoints := endpointIds primitive

/-- The atom component of a canonical bundle is indexed by precisely its primitive declaration. -/
@[simp]
theorem identityBundle_atom {source target : LawfulEncodedType} (primitive : Primitive source target) :
    (identityBundle primitive).atom = ofPrimitive primitive :=
  rfl

/-- The endpoint component of a canonical bundle retains both exact representation identities. -/
@[simp]
theorem identityBundle_endpoints {source target : LawfulEncodedType} (primitive : Primitive source target) :
    (identityBundle primitive).endpoints = endpointIds primitive :=
  rfl

/-- A complete atom bundle has one inhabitant for one exact direct-TM primitive declaration. -/
theorem identityBundle_subsingleton {source target : LawfulEncodedType}
    {primitive : Primitive source target} (first second : IdentityBundle primitive) : first = second := by
  cases first with
  | mk firstAtom firstEndpoints =>
      cases second with
      | mk secondAtom secondEndpoints =>
          cases subsingleton firstAtom secondAtom
          cases firstEndpoints with
          | mk firstSource firstTarget =>
              cases secondEndpoints with
              | mk secondSource secondTarget =>
                  cases RepresentationInstanceId.subsingleton firstSource secondSource
                  cases RepresentationInstanceId.subsingleton firstTarget secondTarget
                  rfl

end AtomInstanceId
end Registry
end ComplexityReduction
