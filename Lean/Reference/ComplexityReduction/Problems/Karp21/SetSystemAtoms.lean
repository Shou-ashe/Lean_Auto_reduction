/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.HittingSet.StructuredRoute
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ListLookupTM
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.SetSystem
import ComplexityReduction.Program.CompileTM
import ComplexityReduction.Protocol.MissingCapability

/-!
Direct-TM-backed primitive atoms for the canonical V2 set-system layouts.

The admitted operations are the source-family filter and dual-table
transformation used by the existing Set-Covering-to-Hitting-Set construction,
plus total indexed lookup in a set family.  Each reuses the legacy direct-TM
theorem for its exact executable and exact structured encoders.  This leaf
owns neither a reduction route nor an additional machine, cost map, packet,
provider, slot, or descriptor.

The older IR pair-list, right-set filter/lookup, and source-to-table chains
are deliberately not imported here.  Their endpoints are based on the legacy
`UniversalRelIR`/construction-table carriers, for which this V2 domain has no
lawful presentation with the same representation identity.  In particular,
their `TMPolyTimeMap` fields cannot be retargeted by a bare carrier equality
or by a cost-map projection.  The typed blockers at the end of this file
record those exact unavailable primitive requests.  The separately audited
Set-Covering-to-Exact-Cover route remains a route-level `.directTM` blocker;
this atom leaf never promotes its native-axiom-dependent evidence.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace SetSystemAtoms

open Encoding
open Program

/-- The canonical structural presentation of one unary natural index. -/
abbrev indexPresentation : LawfulEncodedType :=
  StandardInstances.unaryNat

/-- The canonical structural presentation of one set in a set-system family. -/
abbrev setPresentation : LawfulEncodedType :=
  Presentation.SetSystem.setObjectPresentation

/-- The canonical structural presentation of an ordered set family. -/
abbrev familyPresentation : LawfulEncodedType :=
  Presentation.SetSystem.setFamilyPresentation

/-- The exact input layout for filtering one family by a unary element. -/
abbrev familyMemberIndexSourcePresentation : LawfulEncodedType :=
  StandardInstances.prod indexPresentation familyPresentation

/-- The exact output layout of the resulting family-position list. -/
abbrev familyMemberIndexTargetPresentation : LawfulEncodedType :=
  StandardInstances.list indexPresentation

/-- The exact input layout for a total family lookup by a unary position. -/
abbrev familyLookupSourcePresentation : LawfulEncodedType :=
  StandardInstances.prod familyPresentation indexPresentation

/-- The exact output layout for a total family lookup. -/
abbrev familyLookupTargetPresentation : LawfulEncodedType :=
  setPresentation

/-- The exact input layout for the source-family dual-table transformation. -/
abbrev familyDualTableSourcePresentation : LawfulEncodedType :=
  familyLookupSourcePresentation

/-- The exact output layout of the source-family dual table. -/
abbrev familyDualTableTargetPresentation : LawfulEncodedType :=
  familyPresentation

/--
The exact structured Exact-Cover source presentation required by a future
Incidence-to-RoleGraph EON consumer.  This is an alias of the canonical
SetSystem presentation, not a route-local wrapper or construction table.
-/
abbrev exactCoverIncidenceSourcePresentation : LawfulEncodedType :=
  Presentation.SetSystem.exactCoverStructuredPresentation

/-- The exact faithful structured Set Covering input layout. -/
abbrev setCoveringToHittingSetSourcePresentation : LawfulEncodedType :=
  Presentation.SetSystem.setCoveringStructuredPresentation

/-- The exact faithful structured Hitting Set output layout. -/
abbrev setCoveringToHittingSetTargetPresentation : LawfulEncodedType :=
  Presentation.SetSystem.hittingSetStructuredPresentation

/-- Structural admission for the element-and-family filtering input. -/
def familyMemberIndexSourceStructuralCertificate :
    familyMemberIndexSourcePresentation.StructuralCertificate :=
  StandardInstances.prodStructuralCertificate indexPresentation familyPresentation
    StandardInstances.unaryNatStructuralCertificate
    Presentation.SetSystem.setFamilyStructuralCertificate

/-- Structural admission for the list of selected family positions. -/
def familyMemberIndexTargetStructuralCertificate :
    familyMemberIndexTargetPresentation.StructuralCertificate :=
  StandardInstances.listStructuralCertificate indexPresentation
    StandardInstances.unaryNatStructuralCertificate

/-- Structural admission for a family-and-index lookup input. -/
def familyLookupSourceStructuralCertificate :
    familyLookupSourcePresentation.StructuralCertificate :=
  StandardInstances.prodStructuralCertificate familyPresentation indexPresentation
    Presentation.SetSystem.setFamilyStructuralCertificate
    StandardInstances.unaryNatStructuralCertificate

/-- Structural admission for a returned set object. -/
def familyLookupTargetStructuralCertificate :
    familyLookupTargetPresentation.StructuralCertificate :=
  Presentation.SetSystem.setObjectStructuralCertificate

/-- Structural admission for the direct-TM-produced source-family dual table. -/
def familyDualTableTargetStructuralCertificate :
    familyDualTableTargetPresentation.StructuralCertificate :=
  Presentation.SetSystem.setFamilyStructuralCertificate

/-- Set-system primitive operations whose exact V2 presentations are fixed below. -/
inductive PrimitiveRequest where
  | familyMemberIndices
  | familyLookup
  | familyDualTable
  | setCoveringToHittingSet
  deriving DecidableEq, Repr

/-- The exact V2 source presentation required by each set-system primitive request. -/
def sourcePresentation : PrimitiveRequest → LawfulEncodedType
  | .familyMemberIndices => familyMemberIndexSourcePresentation
  | .familyLookup => familyLookupSourcePresentation
  | .familyDualTable => familyLookupSourcePresentation
  | .setCoveringToHittingSet => setCoveringToHittingSetSourcePresentation

/-- The exact V2 target presentation required by each set-system primitive request. -/
def targetPresentation : PrimitiveRequest → LawfulEncodedType
  | .familyMemberIndices => familyMemberIndexTargetPresentation
  | .familyLookup => familyLookupTargetPresentation
  | .familyDualTable => familyDualTableTargetPresentation
  | .setCoveringToHittingSet => setCoveringToHittingSetTargetPresentation

/-- The direct-TM primitive type required to answer one typed set-system request. -/
abbrev RequiredPrimitive (request : PrimitiveRequest) : Type :=
  Primitive (sourcePresentation request) (targetPresentation request)

/--
The existing source-family scan that returns exactly the indices of sets
containing the requested unary element.  Its direct-TM proof is the reusable
`setIndexIndicesFromFamily_tm_polytime` theorem, for precisely this executable.
-/
@[complexity_reduction_ir_typed_primitive]
noncomputable def familyMemberIndicesPrimitive :
    Primitive (sourcePresentation .familyMemberIndices) (targetPresentation .familyMemberIndices) :=
  Primitive.ofTMPolyTime ComplexityReduction.Karp21.HittingSet.setIndexIndicesFromFamily (by
    simpa [sourcePresentation, targetPresentation] using
      ComplexityReduction.Karp21.HittingSet.setIndexIndicesFromFamily_tm_polytime)

/-- The filtering primitive executes exactly the legacy source-family scanner. -/
@[simp]
theorem familyMemberIndicesPrimitive_run
    (input : (sourcePresentation .familyMemberIndices).Carrier) :
    familyMemberIndicesPrimitive.run input =
      ComplexityReduction.Karp21.HittingSet.setIndexIndicesFromFamily input :=
  rfl

/-- The filtering primitive stores direct-TM evidence for that same executable. -/
theorem familyMemberIndicesPrimitive_directTM :
    ComplexityReduction.TMPolyTimeMap
      (sourcePresentation .familyMemberIndices).encodedType
      (targetPresentation .familyMemberIndices).encodedType
      ComplexityReduction.Karp21.HittingSet.setIndexIndicesFromFamily := by
  simpa only [familyMemberIndicesPrimitive_run] using familyMemberIndicesPrimitive.tmPolyTime

/-- The canonical V2 program atom for the direct-TM-backed family filter. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def familyMemberIndices :
    PolyProg (sourcePresentation .familyMemberIndices) (targetPresentation .familyMemberIndices) :=
  .atom familyMemberIndicesPrimitive

/-- The filter program has exactly the admitted family-scanner executable. -/
@[simp]
theorem familyMemberIndices_run
    (input : (sourcePresentation .familyMemberIndices).Carrier) :
    familyMemberIndices.run input =
      ComplexityReduction.Karp21.HittingSet.setIndexIndicesFromFamily input :=
  rfl

/-- Compiling the filter atom retains direct-TM evidence for its exact executable. -/
theorem familyMemberIndices_compileTM :
    ComplexityReduction.TMPolyTimeMap
      (sourcePresentation .familyMemberIndices).encodedType
      (targetPresentation .familyMemberIndices).encodedType
      ComplexityReduction.Karp21.HittingSet.setIndexIndicesFromFamily := by
  simpa only [familyMemberIndices_run] using familyMemberIndices.compileTM

/--
The existing total list lookup on a set family, with `[]` as the formal
out-of-range fallback.  Its direct-TM proof is the generic reusable
`EncodedListLookup.getD_tm_polytime` theorem instantiated at the set layout.
-/
@[complexity_reduction_ir_typed_primitive]
noncomputable def familyLookupPrimitive :
    Primitive (sourcePresentation .familyLookup) (targetPresentation .familyLookup) :=
  Primitive.ofTMPolyTime
    (ComplexityReduction.Karp21.EncodedListLookup.getD
      ComplexityReduction.Combinatorics.setStructuredEncodedType [])
    (by
      simpa [sourcePresentation, targetPresentation] using
        (ComplexityReduction.Karp21.EncodedListLookup.getD_tm_polytime
          ComplexityReduction.Combinatorics.setStructuredEncodedType []))

/-- The lookup primitive executes exactly the legacy total family lookup. -/
@[simp]
theorem familyLookupPrimitive_run (input : (sourcePresentation .familyLookup).Carrier) :
    familyLookupPrimitive.run input =
      ComplexityReduction.Karp21.EncodedListLookup.getD
        ComplexityReduction.Combinatorics.setStructuredEncodedType [] input :=
  rfl

/-- The lookup primitive stores direct-TM evidence for that same executable. -/
theorem familyLookupPrimitive_directTM :
    ComplexityReduction.TMPolyTimeMap
      (sourcePresentation .familyLookup).encodedType
      (targetPresentation .familyLookup).encodedType
      (ComplexityReduction.Karp21.EncodedListLookup.getD
        ComplexityReduction.Combinatorics.setStructuredEncodedType []) := by
  simpa only [familyLookupPrimitive_run] using familyLookupPrimitive.tmPolyTime

/-- The canonical V2 program atom for direct-TM-backed total family lookup. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def familyLookup :
    PolyProg (sourcePresentation .familyLookup) (targetPresentation .familyLookup) :=
  .atom familyLookupPrimitive

/-- The lookup program has exactly the admitted total-lookup executable. -/
@[simp]
theorem familyLookup_run (input : (sourcePresentation .familyLookup).Carrier) :
    familyLookup.run input =
      ComplexityReduction.Karp21.EncodedListLookup.getD
        ComplexityReduction.Combinatorics.setStructuredEncodedType [] input :=
  rfl

/-- Compiling the lookup atom retains direct-TM evidence for its exact executable. -/
theorem familyLookup_compileTM :
    ComplexityReduction.TMPolyTimeMap
      (sourcePresentation .familyLookup).encodedType
      (targetPresentation .familyLookup).encodedType
      (ComplexityReduction.Karp21.EncodedListLookup.getD
        ComplexityReduction.Combinatorics.setStructuredEncodedType []) := by
  simpa only [familyLookup_run] using familyLookup.compileTM

/--
The existing source-family table transformation for the structured
Set-Covering-to-Hitting-Set construction.  It scans the family at every unary
element position and emits the exact dual family, reusing the legacy direct-TM
theorem for that executable.
-/
@[complexity_reduction_ir_typed_primitive]
noncomputable def familyDualTablePrimitive :
    Primitive (sourcePresentation .familyDualTable) (targetPresentation .familyDualTable) :=
  Primitive.ofTMPolyTime ComplexityReduction.Karp21.HittingSet.dualFamilyFromSetFamily (by
    simpa [sourcePresentation, targetPresentation] using
      ComplexityReduction.Karp21.HittingSet.dualFamilyFromSetFamily_tm_polytime)

/-- The dual-table primitive executes exactly the legacy source-family transformation. -/
@[simp]
theorem familyDualTablePrimitive_run (input : (sourcePresentation .familyDualTable).Carrier) :
    familyDualTablePrimitive.run input =
      ComplexityReduction.Karp21.HittingSet.dualFamilyFromSetFamily input :=
  rfl

/-- The dual-table primitive stores direct-TM evidence for that same executable. -/
theorem familyDualTablePrimitive_directTM :
    ComplexityReduction.TMPolyTimeMap
      (sourcePresentation .familyDualTable).encodedType
      (targetPresentation .familyDualTable).encodedType
      ComplexityReduction.Karp21.HittingSet.dualFamilyFromSetFamily := by
  simpa only [familyDualTablePrimitive_run] using familyDualTablePrimitive.tmPolyTime

/-- The canonical V2 program atom for the direct-TM-backed dual source-family table. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def familyDualTable :
    PolyProg (sourcePresentation .familyDualTable) (targetPresentation .familyDualTable) :=
  .atom familyDualTablePrimitive

/-- The dual-table program has exactly the admitted source-family executable. -/
@[simp]
theorem familyDualTable_run (input : (sourcePresentation .familyDualTable).Carrier) :
    familyDualTable.run input =
      ComplexityReduction.Karp21.HittingSet.dualFamilyFromSetFamily input :=
  rfl

/-- Compiling the dual-table atom retains direct-TM evidence for its exact executable. -/
theorem familyDualTable_compileTM :
    ComplexityReduction.TMPolyTimeMap
      (sourcePresentation .familyDualTable).encodedType
      (targetPresentation .familyDualTable).encodedType
      ComplexityReduction.Karp21.HittingSet.dualFamilyFromSetFamily := by
  simpa only [familyDualTable_run] using familyDualTable.compileTM

/--
The family-dual atom is intentionally not an Exact-Cover incidence source
program: its input representation orders the family and unary universe index
oppositely to the canonical Exact-Cover wrapper.  A future EON construction
must therefore provide an explicit typed prefix program rather than retagging
this primitive at the Exact-Cover endpoint.
-/
theorem familyDualTable_sourceRepresentation_ne_exactCoverIncidenceSource :
    (sourcePresentation .familyDualTable).representationIdentity ≠
      exactCoverIncidenceSourcePresentation.representationIdentity := by
  decide

/-- Distinct representation identities prevent the dual-table source from being reused as Exact Cover. -/
theorem familyDualTable_sourcePresentation_ne_exactCoverIncidenceSource :
    sourcePresentation .familyDualTable ≠ exactCoverIncidenceSourcePresentation :=
  PresentedProblem.exactPresentation_ne_of_representationIdentity_ne
    familyDualTable_sourceRepresentation_ne_exactCoverIncidenceSource

/--
Compose an exact typed prefix with the one canonical family-dual-table atom.

This is the only SetSystemAtoms assembly API for a future consumer (including
an Incidence/EON route) that needs the dual table: it stores the existing
`familyDualTable` program as the second component and does not reconstruct a
source-to-table or incidence construction locally.
-/
noncomputable def composeIntoFamilyDualTable {source : LawfulEncodedType}
    (inputProgram : PolyProg source familyDualTableSourcePresentation) :
    PolyProg source familyDualTableTargetPresentation :=
  .comp familyDualTable inputProgram

/-- The composition executes the exact existing dual-table program after its typed prefix. -/
@[simp]
theorem composeIntoFamilyDualTable_run {source : LawfulEncodedType}
    (inputProgram : PolyProg source familyDualTableSourcePresentation) (input : source.Carrier) :
    (composeIntoFamilyDualTable inputProgram).run input =
      familyDualTable.run (inputProgram.run input) :=
  rfl

/-- The composition retains the prefix source identity and the canonical dual-table target identity. -/
@[simp]
theorem composeIntoFamilyDualTable_endpointIdentities {source : LawfulEncodedType}
    (inputProgram : PolyProg source familyDualTableSourcePresentation) :
    (composeIntoFamilyDualTable inputProgram).endpointIdentities =
      ⟨inputProgram.endpointIdentities.source, familyDualTable.endpointIdentities.target⟩ :=
  rfl

/-- The composed direct-TM witness is the backend composition whose second component is this atom. -/
theorem composeIntoFamilyDualTable_compileTM {source : LawfulEncodedType}
    (inputProgram : PolyProg source familyDualTableSourcePresentation) :
    (composeIntoFamilyDualTable inputProgram).compileTM =
      ComplexityReduction.TMPolyTimeMap.comp familyDualTablePrimitive.tmPolyTime inputProgram.compileTM :=
  rfl

/--
The concrete identity-prefix composition is semantically the same exact
family-dual-table program.  It is a regression-facing composition identity,
not a second implementation of the dual table.
-/
theorem composeIntoFamilyDualTable_exactSourceIdentity_semanticallyEquivalent :
    PolyProg.SemanticallyEquivalent
      (composeIntoFamilyDualTable (PolyProg.id familyDualTableSourcePresentation))
      familyDualTable :=
  PolyProg.SemanticallyEquivalent.comp_id familyDualTable

/--
The complete faithful Set-Covering-to-Hitting-Set construction already has a
direct-TM theorem at precisely the two canonical V2 target presentations.
This atom reuses that theorem directly; it does not project the legacy cost
map or reassemble the construction locally.
-/
@[complexity_reduction_ir_typed_primitive]
noncomputable def setCoveringToHittingSetPrimitive :
    Primitive (sourcePresentation .setCoveringToHittingSet)
      (targetPresentation .setCoveringToHittingSet) :=
  Primitive.ofTMPolyTime ComplexityReduction.Karp21.HittingSet.map (by
    simpa [sourcePresentation, targetPresentation,
      setCoveringToHittingSetSourcePresentation,
      setCoveringToHittingSetTargetPresentation] using
      ComplexityReduction.Karp21.HittingSet.setCoveringToHittingSetStructured_tm_polytime)

/-- The construction atom executes exactly the established structured map. -/
@[simp]
theorem setCoveringToHittingSetPrimitive_run
    (input : (sourcePresentation .setCoveringToHittingSet).Carrier) :
    setCoveringToHittingSetPrimitive.run input =
      ComplexityReduction.Karp21.HittingSet.map input :=
  rfl

/-- The construction atom retains direct-TM evidence for its exact executable. -/
theorem setCoveringToHittingSetPrimitive_directTM :
    ComplexityReduction.TMPolyTimeMap
      (sourcePresentation .setCoveringToHittingSet).encodedType
      (targetPresentation .setCoveringToHittingSet).encodedType
      ComplexityReduction.Karp21.HittingSet.map := by
  simpa only [setCoveringToHittingSetPrimitive_run] using
    setCoveringToHittingSetPrimitive.tmPolyTime

/-- The canonical V2 program atom for the direct-TM complete construction. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def setCoveringToHittingSet :
    PolyProg (sourcePresentation .setCoveringToHittingSet)
      (targetPresentation .setCoveringToHittingSet) :=
  .atom setCoveringToHittingSetPrimitive

/-- The construction program executes exactly the established structured map. -/
@[simp]
theorem setCoveringToHittingSet_run
    (input : (sourcePresentation .setCoveringToHittingSet).Carrier) :
    setCoveringToHittingSet.run input = ComplexityReduction.Karp21.HittingSet.map input :=
  rfl

/-- Compiling the construction atom preserves direct-TM evidence for its map. -/
theorem setCoveringToHittingSet_compileTM :
    ComplexityReduction.TMPolyTimeMap
      (sourcePresentation .setCoveringToHittingSet).encodedType
      (targetPresentation .setCoveringToHittingSet).encodedType
      ComplexityReduction.Karp21.HittingSet.map := by
  simpa only [setCoveringToHittingSet_run] using setCoveringToHittingSet.compileTM

/--
The complete atom's source is the one canonical structured Set-Covering
presentation, not merely a carrier-compatible set-system wrapper.
-/
@[simp]
theorem setCoveringToHittingSet_sourcePresentation_exact :
    sourcePresentation .setCoveringToHittingSet =
      Presentation.SetSystem.setCoveringStructuredPresentation :=
  rfl

/--
The complete atom's target is the one canonical structured Hitting-Set
presentation, not merely a carrier-compatible set-system wrapper.
-/
@[simp]
theorem setCoveringToHittingSet_targetPresentation_exact :
    targetPresentation .setCoveringToHittingSet =
      Presentation.SetSystem.hittingSetStructuredPresentation :=
  rfl

/--
The legacy Set-Covering-to-Hitting-Set semantic theorem is admitted only at
the exact V2 endpoints and for this atom's own executable.  Consequently a
future `CertifiedReduction` can reuse this one program-indexed statement;
neither a source-to-table map nor a separately named target construction can
be substituted for it.
-/
theorem setCoveringToHittingSet_correct
    (input : (sourcePresentation .setCoveringToHittingSet).Carrier) :
    Presentation.SetSystem.setCoveringStructuredProblem.accepts input ↔
      Presentation.SetSystem.hittingSetStructuredProblem.accepts
        (setCoveringToHittingSet.run input) := by
  simpa only [Presentation.SetSystem.setCoveringStructuredProblem_accepts,
    Presentation.SetSystem.hittingSetStructuredProblem_accepts,
    setCoveringToHittingSet_run] using
    ComplexityReduction.Karp21.HittingSet.map_correct input

/-- Resolve a set-system request only by its exact direct-TM-backed V2 atom. -/
noncomputable def resolvePrimitive (request : PrimitiveRequest) :
    Except (Protocol.MissingCapability PrimitiveRequest) (RequiredPrimitive request) :=
  match request with
  | .familyMemberIndices => .ok familyMemberIndicesPrimitive
  | .familyLookup => .ok familyLookupPrimitive
  | .familyDualTable => .ok familyDualTablePrimitive
  | .setCoveringToHittingSet => .ok setCoveringToHittingSetPrimitive

/-- The source-family filtering request resolves to its direct-TM primitive. -/
@[simp]
theorem resolvePrimitive_familyMemberIndices :
    resolvePrimitive .familyMemberIndices = .ok familyMemberIndicesPrimitive :=
  rfl

/-- The total family-lookup request resolves to its direct-TM primitive. -/
@[simp]
theorem resolvePrimitive_familyLookup :
    resolvePrimitive .familyLookup = .ok familyLookupPrimitive :=
  rfl

/-- The source-family dual-table request resolves to its direct-TM primitive. -/
@[simp]
theorem resolvePrimitive_familyDualTable :
    resolvePrimitive .familyDualTable = .ok familyDualTablePrimitive :=
  rfl

/-- The complete Set-Covering-to-Hitting-Set request resolves to its direct-TM atom. -/
@[simp]
theorem resolvePrimitive_setCoveringToHittingSet :
    resolvePrimitive .setCoveringToHittingSet = .ok setCoveringToHittingSetPrimitive :=
  rfl

/--
Legacy set-system operations that have no endpoint-equal canonical V2
presentation.  These names describe the requested computation, not a packet,
provider, slot, descriptor, executable, or theorem-name capability.

The right-set operations are intentionally distinct: a pair-list materializer
does not establish either a filter or a keyed lookup capability.  Likewise,
the four target-construction requests remain distinct rather than being
collapsed into an untyped "set-system construction" flag.
-/
inductive MissingPrimitiveRequest where
  | legacyRightSetPairList
  | legacyRightSetFilter
  | legacyRightSetLookup
  | legacySourceToConstructionTable
  | legacyExactCoverConstruction
  | legacyHittingSetConstruction
  | legacySetCoveringConstruction
  | legacySetPackingConstruction
  deriving DecidableEq, Repr

/--
Every legacy construction-table request is blocked first by the lack of an
endpoint-equal V2 lawful presentation.  This value contains neither an
executable nor direct-TM/cost evidence, so an old `UniversalRelIR` map cannot
be mistaken for a canonical set-system primitive.
-/
def missingPrimitive (request : MissingPrimitiveRequest) :
    Protocol.MissingCapability MissingPrimitiveRequest :=
  .lawfulPresentation request

/--
The only result shape for an unavailable legacy set-system operation.  The
success branch is `Empty`: neither a legacy projection nor a route-local
function has a place where it could be supplied while the canonical V2
presentation is absent.
-/
abbrev MissingPrimitiveResolution (_request : MissingPrimitiveRequest) : Type :=
  Except (Protocol.MissingCapability MissingPrimitiveRequest) Empty

/--
Resolve a legacy construction-table request only to its exact typed blocker.
The empty success branch prevents a local function, TM, or old packet from
being supplied in place of a canonical V2 primitive.
-/
def resolveMissingPrimitive (request : MissingPrimitiveRequest) :
    MissingPrimitiveResolution request :=
  .error (missingPrimitive request)

/-- Every legacy blocker retains the exact requested operation. -/
@[simp]
theorem missingPrimitive_endpoint (request : MissingPrimitiveRequest) :
    (missingPrimitive request).endpoint = request :=
  rfl

/-- Every legacy blocker records the missing representation, not a fabricated TM claim. -/
@[simp]
theorem missingPrimitive_reason (request : MissingPrimitiveRequest) :
    (missingPrimitive request).reason = .lawfulPresentation :=
  rfl

/--
Every audited legacy projection retains both the exact operation request and
the precise absent-presentation cause.  In particular, an old direct-TM or
cost projection cannot silently change this diagnostic into a V2 primitive.
-/
theorem missingPrimitive_exactBoundary (request : MissingPrimitiveRequest) :
    (missingPrimitive request).endpoint = request ∧
      (missingPrimitive request).reason = .lawfulPresentation :=
  ⟨rfl, rfl⟩

/-- Pair-list materialization cannot be upgraded from the legacy table carrier. -/
@[simp]
theorem resolveMissingPrimitive_legacyRightSetPairList :
    resolveMissingPrimitive .legacyRightSetPairList =
      .error (missingPrimitive .legacyRightSetPairList) :=
  rfl

/-- Right-set filtering cannot be upgraded from the legacy table carrier. -/
@[simp]
theorem resolveMissingPrimitive_legacyRightSetFilter :
    resolveMissingPrimitive .legacyRightSetFilter =
      .error (missingPrimitive .legacyRightSetFilter) :=
  rfl

/-- Keyed right-set lookup cannot be upgraded from the legacy table carrier. -/
@[simp]
theorem resolveMissingPrimitive_legacyRightSetLookup :
    resolveMissingPrimitive .legacyRightSetLookup =
      .error (missingPrimitive .legacyRightSetLookup) :=
  rfl

/-- Source-to-table assembly cannot be upgraded from the legacy table carrier. -/
@[simp]
theorem resolveMissingPrimitive_legacySourceToConstructionTable :
    resolveMissingPrimitive .legacySourceToConstructionTable =
      .error (missingPrimitive .legacySourceToConstructionTable) :=
  rfl

/-- Exact-Cover target assembly remains a presentation blocker at this atom boundary. -/
@[simp]
theorem resolveMissingPrimitive_legacyExactCoverConstruction :
    resolveMissingPrimitive .legacyExactCoverConstruction =
      .error (missingPrimitive .legacyExactCoverConstruction) :=
  rfl

/-- Hitting-Set target assembly remains a presentation blocker at this atom boundary. -/
@[simp]
theorem resolveMissingPrimitive_legacyHittingSetConstruction :
    resolveMissingPrimitive .legacyHittingSetConstruction =
      .error (missingPrimitive .legacyHittingSetConstruction) :=
  rfl

/-- Set-Covering target assembly remains a presentation blocker at this atom boundary. -/
@[simp]
theorem resolveMissingPrimitive_legacySetCoveringConstruction :
    resolveMissingPrimitive .legacySetCoveringConstruction =
      .error (missingPrimitive .legacySetCoveringConstruction) :=
  rfl

/-- Set-Packing target assembly remains a presentation blocker at this atom boundary. -/
@[simp]
theorem resolveMissingPrimitive_legacySetPackingConstruction :
    resolveMissingPrimitive .legacySetPackingConstruction =
      .error (missingPrimitive .legacySetPackingConstruction) :=
  rfl

/--
No unavailable legacy set-system request has a success branch from which a
canonical V2 primitive can arise.  This is intentionally stronger than merely
rejecting the currently known packet types: the resolver's success carrier is
empty before any legacy or native-axiom evidence is considered.
-/
theorem resolveMissingPrimitive_no_success (request : MissingPrimitiveRequest) :
    ¬ ∃ result, resolveMissingPrimitive request = .ok result := by
  rintro ⟨result, resolution⟩
  cases resolution

end SetSystemAtoms
end Karp21
end Problems
end ComplexityReduction
