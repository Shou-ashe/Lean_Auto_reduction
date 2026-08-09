/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean.Attributes
import ComplexityReduction.Core.ComponentRole

/-!
Declaration-local V2 annotations.

These markers are deliberately only environment tags: they neither validate a
declaration's type nor construct a program, certificate, registry entry, or
trusted capability.  A later shared environment exporter must inspect the
elaborated declaration independently before it can recognize any usable entry.
-/

namespace ComplexityReduction
namespace Annotations

/--
Marks a concrete declaration as a candidate exact V2 `PresentedProblem`.
The marker only makes the declaration discoverable; the exporter must still
inspect its elaborated type before it can recognize any capability.
-/
initialize typedProblemAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `complexity_reduction_ir_typed_problem
    "marks a candidate CR_IR V2 presented problem; grants no trusted capability"

/--
Marks a concrete declaration as candidate structural presentation evidence.
The marker cannot turn a bare encoding, injectivity proof, or carrier equality
into a structural presentation certificate.
-/
initialize typedPresentationAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `complexity_reduction_ir_typed_presentation
    "marks candidate structural presentation evidence; grants no trusted capability"

/--
Marks a concrete declaration as a candidate V2 typed edge for later environment discovery.

The attribute is intentionally non-authoritative: applying it does not establish semantic
correctness, presentation lawfulness, program realizability, certificate validity, or registry
capability.
-/
initialize typedEdgeAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `complexity_reduction_ir_typed_edge
    "marks a candidate CR_IR V2 typed-edge declaration; grants no trusted capability"

/--
Marks a concrete declaration as a candidate V2 certified equivalence.  The
attribute does not validate either direction or grant registry capability.
-/
initialize typedEquivAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `complexity_reduction_ir_typed_equiv
    "marks a candidate CR_IR V2 typed-equivalence declaration; grants no trusted capability"

/--
Marks a concrete declaration as a candidate V2 direct-TM primitive.  Applying
the tag cannot create a primitive or validate its direct-TM witness.
-/
initialize typedPrimitiveAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `complexity_reduction_ir_typed_primitive
    "marks a candidate CR_IR V2 typed-primitive declaration; grants no trusted capability"

/--
Marks a concrete declaration as a candidate V2 native verifier.  The tag is
not a verifier certificate or encoding-discipline capability.
-/
initialize typedVerifierAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `complexity_reduction_ir_typed_verifier
    "marks a candidate CR_IR V2 typed-verifier declaration; grants no trusted capability"

/--
Marks a candidate V2 verifier encoding-discipline declaration.  The eventual
exporter must inspect its elaborated type and proof term independently.
-/
initialize typedVerifierDisciplineAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `complexity_reduction_ir_typed_verifier_discipline
    "marks a candidate CR_IR V2 verifier-discipline declaration; grants no trusted capability"

/--
Marks a candidate native verifier-membership capability.  The tag is not a
membership theorem and cannot upgrade backend-only verifier evidence.
-/
initialize typedNativeMembershipAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `complexity_reduction_ir_typed_native_membership
    "marks candidate native verifier membership; grants no trusted capability"

/--
Marks a candidate exact native NP-hardness declaration.  The tag is discovery
metadata only; the registry must still classify the declaration's elaborated
type as `NativeTMNPHard` at one exact presented problem.
-/
initialize typedNativeHardnessAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `complexity_reduction_ir_typed_native_hardness
    "marks candidate exact native NP-hardness evidence; grants no trusted capability"

/--
Marks a candidate exact completeness declaration.  The elaborated declaration
type, rather than this marker, determines which completeness capability exists.
-/
initialize typedCompleteAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `complexity_reduction_ir_typed_complete
    "marks candidate exact completeness evidence; grants no trusted capability"

/--
Marks a candidate V2 certified presentation change.  This tag cannot turn a
bare equivalence or carrier equality into a trusted presentation change.
-/
initialize typedPresentationChangeAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `complexity_reduction_ir_typed_presentation_change
    "marks a candidate CR_IR V2 presentation-change declaration; grants no trusted capability"

/--
Marks the final result selected for a caller.  This is an export-discovery
marker only and cannot make an intermediate declaration a trusted result.
-/
initialize typedFinalResultAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `complexity_reduction_ir_typed_final_result
    "marks a candidate CR_IR V2 final result; grants no trusted capability"

/-- A declaration-local component role observed by candidate discovery only. -/
structure ComponentRoleCandidateProvenance where
  declaration : Lean.Name
  role : ReductionComponentRole

private structure ComponentRoleTagAttributes where
  ingress : Lean.TagAttribute
  sharedGadget : Lean.TagAttribute
  egress : Lean.TagAttribute
  finalComposition : Lean.TagAttribute
  deriving Inhabited

private def ComponentRoleTagAttributes.role? (tags : ComponentRoleTagAttributes)
    (environment : Lean.Environment) (declaration : Lean.Name) : Option ReductionComponentRole :=
  if tags.ingress.hasTag environment declaration then some .ingress
  else if tags.sharedGadget.hasTag environment declaration then some .sharedGadget
  else if tags.egress.hasTag environment declaration then some .egress
  else if tags.finalComposition.hasTag environment declaration then some .finalComposition
  else none

private initialize componentRoleTagAttributesRef : IO.Ref (Option ComponentRoleTagAttributes) ←
  IO.mkRef none

/-- Reject attaching a second component role to one declaration. -/
private def ensureNoComponentRoleConflict (role : ReductionComponentRole)
    (declaration : Lean.Name) : Lean.AttrM Unit := do
  let tags? ← componentRoleTagAttributesRef.get
  match tags? with
  | none => pure ()
  | some tags =>
      match tags.role? (← Lean.getEnv) declaration with
      | none => pure ()
      | some existing =>
          throwError "declaration `{declaration}` already carries CR_IR V2 component role \
            `{existing}`; cannot add conflicting component role `{role}`"

/--
Marks a declaration as a non-authoritative ingress-normalization candidate.
The tag is planning provenance only; it never constructs a capability.
-/
initialize componentIngressAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `complexity_reduction_ir_component_ingress
    "marks a non-authoritative CR_IR V2 ingress component role; grants no trusted capability"
    (ensureNoComponentRoleConflict .ingress)

/--
Marks a declaration as a non-authoritative shared-gadget candidate.  This role
does not establish that the declaration is reusable or certified.
-/
initialize componentSharedGadgetAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `complexity_reduction_ir_component_shared_gadget
    "marks a non-authoritative CR_IR V2 shared-gadget component role; grants no trusted capability"
    (ensureNoComponentRoleConflict .sharedGadget)

/--
Marks a declaration as a non-authoritative egress-realization candidate.
The tag is not a program, direct-TM witness, or certificate.
-/
initialize componentEgressAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `complexity_reduction_ir_component_egress
    "marks a non-authoritative CR_IR V2 egress component role; grants no trusted capability"
    (ensureNoComponentRoleConflict .egress)

/--
Marks a declaration as a non-authoritative final-composition candidate.  This
role cannot make an untyped final result or a metadata value trusted.
-/
initialize componentFinalCompositionAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `complexity_reduction_ir_component_final_composition
    "marks a non-authoritative CR_IR V2 final-composition component role; grants no trusted capability"
    (ensureNoComponentRoleConflict .finalComposition)

private initialize componentRoleTagAttributes : ComponentRoleTagAttributes ← do
  let tags := {
    ingress := componentIngressAttr
    sharedGadget := componentSharedGadgetAttr
    egress := componentEgressAttr
    finalComposition := componentFinalCompositionAttr
  }
  componentRoleTagAttributesRef.set (some tags)
  pure tags

/--
Recover a declaration's unique non-authoritative component role, if any.

This is only candidate-discovery provenance.  It neither reads a declaration
body nor validates its elaborated type, so it cannot construct a certified
reduction, registry entry, or final capability.
-/
def componentRole? (environment : Lean.Environment) (declaration : Lean.Name) :
    Option ReductionComponentRole :=
  componentRoleTagAttributes.role? environment declaration

/-- Test only whether a declaration has one non-authoritative component-role tag. -/
def isComponentRoleCandidate (environment : Lean.Environment) (declaration : Lean.Name) : Bool :=
  (componentRole? environment declaration).isSome

/-- Recover declaration-local role provenance without granting any capability. -/
def componentRoleCandidateProvenance? (environment : Lean.Environment) (declaration : Lean.Name) :
    Option ComponentRoleCandidateProvenance :=
  (componentRole? environment declaration).map fun role => ⟨declaration, role⟩

/--
The non-authoritative tags which may contribute declaration names to a later
type-directed capability scan.

This is deliberately a list of `Lean.TagAttribute`s, rather than a registry
entry type or a payload-bearing descriptor.  In particular, looking up a name
through this list yields only a Boolean discovery fact; it supplies neither a
proof nor a value of any V2 capability.  `typedFinalResultAttr` is omitted on
purpose: selecting a caller-facing result is not itself a capability class.
The component-role tags are also omitted: their separate provenance API does
not make a declaration a capability candidate before type validation.
-/
def capabilityCandidateAttributes : List Lean.TagAttribute :=
  [typedEdgeAttr,
    typedEquivAttr,
    typedPrimitiveAttr,
    typedVerifierAttr,
    typedVerifierDisciplineAttr,
    typedPresentationChangeAttr,
    typedProblemAttr,
    typedPresentationAttr,
    typedNativeMembershipAttr,
    typedNativeHardnessAttr,
    typedCompleteAttr]

/--
Test declaration-local discoverability only.

The result is intentionally a `Bool` supplied by Lean's environment metadata.
It is not an admission function: callers that need a V2 certificate must
inspect the declaration's elaborated type and construct or recover that
certificate independently.
-/
def isCapabilityCandidate (environment : Lean.Environment) (declaration : Lean.Name) : Bool :=
  capabilityCandidateAttributes.any (fun tag => tag.hasTag environment declaration)

end Annotations
end ComplexityReduction
