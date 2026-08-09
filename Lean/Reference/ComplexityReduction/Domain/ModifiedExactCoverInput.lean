/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.SetSystemToIncidenceAdapter
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.SetSystem
import ComplexityReduction.Program.CompileTM
import ComplexityReduction.Protocol.ComponentResolver

/-!
The modified Exact-Cover source representation used by the incidence reuse
pilot.

The Boolean field is deliberate metadata: the source predicate ignores it and
the only executable introduced here is the canonical product second
projection.  That projection composes with the one original-source ingress
certificate, so this module introduces neither a modified-source primitive
nor a second hub gadget, TM, or final route construction.
-/

namespace ComplexityReduction
namespace Domain
namespace ModifiedExactCoverInput

open Encoding
open Program
open Certificate

/-- The pre-existing structured Exact-Cover presentation. -/
abbrev originalPresentation : LawfulEncodedType :=
  Presentation.SetSystem.exactCoverStructuredPresentation

/--
The exact modified product representation.  Its carrier is definitionally
`Bool × ExactCoverInput` and its codec identity retains both product fields.
-/
abbrev modifiedPresentation : LawfulEncodedType :=
  StandardInstances.prod StandardInstances.bool originalPresentation

/-- The modified carrier is the requested Boolean-tagged Exact-Cover input. -/
theorem modifiedPresentation_carrier :
    modifiedPresentation.Carrier =
      (Bool × ComplexityReduction.Combinatorics.ExactCoverInput) :=
  rfl

/-- The modified representation keeps the Boolean field in its encoder-bound identity. -/
@[simp] theorem modifiedPresentation_representation :
    modifiedPresentation.representation =
      (CodecShape.prod CodecShape.bool
        Presentation.SetSystem.setSystemStructuredShape).identity :=
  rfl

/-- The original Exact-Cover endpoint at its exact structured presentation. -/
abbrev originalProblem : PresentedProblem :=
  Presentation.SetSystem.exactCoverStructuredProblem

/-- The modified predicate deliberately ignores the Boolean metadata field. -/
def modifiedProblemAt : ProblemAt modifiedPresentation where
  isYes := fun input => originalProblem.accepts input.2

/-- The canonical presented problem for the Boolean-tagged source representation. -/
def modifiedProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt modifiedPresentation modifiedProblemAt

/-- The modified endpoint has exactly the product presentation. -/
@[simp] theorem modifiedProblem_representation :
    modifiedProblem.representation = modifiedPresentation :=
  rfl

/-- The semantic predicate ignores metadata and delegates to the original endpoint. -/
@[simp] theorem modifiedProblem_accepts (input : modifiedProblem.Instance) :
    modifiedProblem.accepts input ↔ originalProblem.accepts input.2 :=
  Iff.rfl

/--
Erase the Boolean metadata by the canonical structural second projection.
No domain primitive is introduced for this representation change.
-/
def eraseMetadata : PolyProg modifiedPresentation originalPresentation :=
  PolyProg.snd StandardInstances.bool originalPresentation

/-- The metadata-erasure program is definitionally the canonical second projection. -/
@[simp] theorem eraseMetadata_eq_snd :
    eraseMetadata = PolyProg.snd StandardInstances.bool originalPresentation :=
  rfl

/-- Metadata erasure runs by selecting precisely the product's second field. -/
@[simp] theorem eraseMetadata_run (input : modifiedPresentation.Carrier) :
    eraseMetadata.run input = input.2 :=
  rfl

/-- The direct-TM evidence is definitionally the compiler output of this one projection program. -/
@[simp] theorem eraseMetadata_directTM :
    eraseMetadata.compileTM =
      ComplexityReduction.TMPolyTimeMap.snd StandardInstances.bool.encodedType
        originalPresentation.encodedType :=
  rfl

/-- The projection preserves the Exact-Cover predicate exactly because metadata is ignored. -/
theorem eraseMetadata_correct (input : modifiedProblem.Instance) :
    modifiedProblem.accepts input ↔ originalProblem.accepts (eraseMetadata.run input) :=
  Iff.rfl

/-- The exact ingress request for the structural metadata-erasure adapter. -/
abbrev MetadataErasureRequest : Type 2 :=
  Protocol.ComponentRequest .ingress modifiedProblem originalProblem

/-- The unique request for the product-to-original structural adapter. -/
def metadataErasureRequest : MetadataErasureRequest := .exact

/--
The accepted structural half of the modified-input ingress.

This is deliberately a certificate for `Bool × ExactCoverInput →
ExactCoverInput`, not a fabricated certificate to the incidence hub.  Its
sole program is `PolyProg.snd`, so its direct-TM and compatibility-cost
evidence are compiler projections of that one structural program.
-/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_ingress]
def metadataErasureAdapter : CertifiedReduction modifiedProblem originalProblem where
  program := eraseMetadata
  correct := eraseMetadata_correct

/-- The structural adapter stores exactly the canonical second-projection program. -/
@[simp] theorem metadataErasureAdapter_program :
    metadataErasureAdapter.program = eraseMetadata :=
  rfl

/-- Its direct-TM evidence is exactly compilation of the stored projection program. -/
@[simp] theorem metadataErasureAdapter_directTM :
    metadataErasureAdapter.directTM = eraseMetadata.compileTM :=
  rfl

/-- The accepted component result is indexed by the product/original endpoints. -/
def metadataErasureResolution :
    Protocol.ComponentResolution .ingress modifiedProblem originalProblem :=
  Protocol.ComponentResolver.accept metadataErasureRequest metadataErasureAdapter

/-- The structural component is accepted without granting any hub capability. -/
@[simp] theorem metadataErasureResolution_exact :
    metadataErasureResolution = .accepted metadataErasureAdapter :=
  rfl

/-- The canonical incidence hub remains the target requested by the original ingress. -/
abbrev hubProblem : PresentedProblem :=
  SetSystemToIncidenceAdapter.hubProblem

/--
The exact modified ingress endpoint: erase metadata first, then require the
same original ingress component.  It reuses the Protocol component endpoint
owner and contains no executable beyond the fixed structural projection above.
-/
abbrev ModifiedIngressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .ingress modifiedProblem hubProblem

/-- The canonical component request for the modified ingress endpoint. -/
abbrev ModifiedIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress modifiedProblem hubProblem

/-- The unique modified ingress request to the canonical incidence hub. -/
def modifiedIngressRequest : ModifiedIngressRequest :=
  .exact

/--
Compose the original certified ingress with metadata erasure.  This is the
only modified-input source adapter; no new atom or direct-TM proof appears.
-/
noncomputable def modifiedSourceAdapterOf
    (originalSourceAdapter : CertifiedReduction originalProblem hubProblem) :
    CertifiedReduction modifiedProblem hubProblem :=
  CertifiedReduction.comp originalSourceAdapter metadataErasureAdapter

/-- The concrete modified ingress reuses the one original source adapter. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_ingress]
noncomputable def modifiedSourceAdapter : CertifiedReduction modifiedProblem hubProblem :=
  modifiedSourceAdapterOf SetSystemToIncidenceAdapter.sourceAdapter

/-- The modified adapter's construction is the required original-adapter/projection composition. -/
@[simp] theorem modifiedSourceAdapter_program :
    modifiedSourceAdapter.program =
      PolyProg.comp SetSystemToIncidenceAdapter.sourceAdapter.program eraseMetadata :=
  rfl

/-- Its direct-TM evidence is compiled from that same composite program. -/
@[simp] theorem modifiedSourceAdapter_directTM :
    modifiedSourceAdapter.directTM = modifiedSourceAdapter.program.compileTM :=
  rfl

/-- The existing original ingress resolution is the shared exact component result. -/
abbrev originalIngressComponentResolution : Type 2 :=
  Protocol.ComponentResolution .ingress originalProblem hubProblem

/-- The original component is the accepted canonical source-to-hub certificate. -/
noncomputable def originalIngressResolution : originalIngressComponentResolution :=
  SetSystemToIncidenceAdapter.resolve

/--
The modified composition has the shared final resolver shape.  A blocker may
retain the original ingress endpoint, so it is not retagged as a fabricated
modified-source component certificate.
-/
abbrev ModifiedIngressResolution : Type 2 :=
  Protocol.ResolverOutcome modifiedProblem hubProblem

/-- Resolve the modified ingress by composing its structural projection and original adapter. -/
noncomputable def modifiedIngressCompositionOutcome : ModifiedIngressResolution :=
  Protocol.ComponentResolver.composeTwoStage originalIngressResolution metadataErasureResolution

/- The original ingress component is accepted at exactly its canonical endpoint. -/
@[simp] theorem originalIngressResolution_exact :
    originalIngressResolution = .accepted SetSystemToIncidenceAdapter.sourceAdapter :=
  rfl

/- The modified composition is accepted with the sole composed source adapter. -/
@[simp] theorem modifiedIngressCompositionOutcome_exact :
    modifiedIngressCompositionOutcome = .accepted modifiedSourceAdapter :=
  rfl

/-- The eventual modified source adapter has the required explicit program composition. -/
@[simp] theorem modifiedSourceAdapterOf_program
    (originalSourceAdapter : CertifiedReduction originalProblem hubProblem) :
    (modifiedSourceAdapterOf originalSourceAdapter).program =
      PolyProg.comp originalSourceAdapter.program eraseMetadata :=
  rfl

/-- Its direct-TM witness is compilation of that same composite program. -/
@[simp] theorem modifiedSourceAdapterOf_directTM
    (originalSourceAdapter : CertifiedReduction originalProblem hubProblem) :
    (modifiedSourceAdapterOf originalSourceAdapter).directTM =
      (PolyProg.comp originalSourceAdapter.program eraseMetadata).compileTM :=
  rfl


end ModifiedExactCoverInput
end Domain
end ComplexityReduction
