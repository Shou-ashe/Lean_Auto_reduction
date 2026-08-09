/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Reduction
import ComplexityReduction.Presentation.SetSystem
import ComplexityReduction.Problems.Karp21.SetSystemAtoms
import ComplexityReduction.Protocol.ComponentRequest

/-!
The canonical structured Set-Covering-to-Hitting-Set V2 route.

`SetSystemAtoms` owns the one complete direct-TM-backed construction atom at
the faithful structured endpoints.  This route stores precisely that atom as
its program and reuses its program-indexed semantic theorem.  Thus the
executable, semantic iff, direct-TM evidence, and compatibility cost all
refer to one V2 syntax value; this module neither reconstructs a dual-family
machine nor wraps a separate legacy reduction or cost map.
-/

namespace ComplexityReduction
namespace Routes
namespace SetCoveringToHittingSet

open Certificate Encoding Program

/-- The exact faithful structured Set Covering presentation used by this route. -/
abbrev sourcePresentation : LawfulEncodedType :=
  Presentation.SetSystem.setCoveringStructuredPresentation

/-- The exact faithful structured Hitting Set presentation used by this route. -/
abbrev targetPresentation : LawfulEncodedType :=
  Presentation.SetSystem.hittingSetStructuredPresentation

/-- The exact V2 structured Set Covering endpoint. -/
abbrev sourceProblem : PresentedProblem :=
  Presentation.SetSystem.setCoveringStructuredProblem

/-- The exact V2 structured Hitting Set endpoint. -/
abbrev targetProblem : PresentedProblem :=
  Presentation.SetSystem.hittingSetStructuredProblem

/-- The exact canonical dual-system shared-gadget endpoint. -/
abbrev SetCoveringToHittingSetSharedGadgetEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .sharedGadget sourceProblem targetProblem

/-- The unique exact shared component endpoint; it is not a route-local request language. -/
def setCoveringToHittingSetSharedGadgetRequest : SetCoveringToHittingSetSharedGadgetEndpoint :=
  .exact

/-- The route source is definitionally the complete atom's exact source presentation. -/
@[simp]
theorem sourcePresentation_eq_atomSource :
    sourcePresentation =
      Problems.Karp21.SetSystemAtoms.sourcePresentation .setCoveringToHittingSet :=
  rfl

/-- The route target is definitionally the complete atom's exact target presentation. -/
@[simp]
theorem targetPresentation_eq_atomTarget :
    targetPresentation =
      Problems.Karp21.SetSystemAtoms.targetPresentation .setCoveringToHittingSet :=
  rfl

/--
The read-only structured direct-TM Karp witness at the exact two canonical
V2 endpoints.  It is retained solely as an audit source: the V2 certificate
below is built from the already admitted endpoint-indexed primitive, rather
than by importing a costed reduction or a second construction.
-/
noncomputable def structuredTMKarpReduction :
    ComplexityReduction.TMKarpReduction sourceProblem.toEncodedDecisionProblem
      targetProblem.toEncodedDecisionProblem := by
  simpa [sourceProblem, sourcePresentation, targetProblem, targetPresentation] using
    ComplexityReduction.Karp21.HittingSet.setCoveringToHittingSetStructuredTMKarpReduction

/-- The audited structured Karp witness has exactly the established dual-system map. -/
@[simp]
theorem structuredTMKarpReduction_run (input : sourceProblem.Instance) :
    structuredTMKarpReduction.f input = ComplexityReduction.Karp21.HittingSet.map input :=
  rfl

/--
The audited Karp witness's direct-TM field is exactly the direct-TM evidence
stored by the canonical endpoint primitive.  This is an equality of
same-executable evidence, not a cost-map conversion.
-/
@[simp]
theorem structuredTMKarpReduction_directTM_eq_atom :
    structuredTMKarpReduction.polytime =
      Problems.Karp21.SetSystemAtoms.setCoveringToHittingSetPrimitive.tmPolyTime :=
  rfl

/--
Legacy-named axiom-audit theorem for the complete atom's direct-TM witness.
This is neither a second route nor an executable, machine construction, or
cost projection; canonical route evidence below refers directly to the atom.
-/
theorem legacyStructuredReduction :
    ComplexityReduction.TMPolyTimeMap sourcePresentation.encodedType targetPresentation.encodedType
      Problems.Karp21.SetSystemAtoms.setCoveringToHittingSet.run :=
  Problems.Karp21.SetSystemAtoms.setCoveringToHittingSet_compileTM

/--
The sole canonical V2 Set-Covering-to-Hitting-Set certificate.  It stores the
complete Set-System atom itself, and obtains its semantic iff from the
theorem indexed by that atom's `run` function.
-/
@[complexity_reduction_ir_typed_edge]
noncomputable def certifiedReduction : CertifiedReduction sourceProblem targetProblem where
  program := Problems.Karp21.SetSystemAtoms.setCoveringToHittingSet
  correct := Problems.Karp21.SetSystemAtoms.setCoveringToHittingSet_correct

/-- The certificate stores exactly the complete Set-System atom. -/
@[simp]
theorem certifiedReduction_program :
    certifiedReduction.program =
      Problems.Karp21.SetSystemAtoms.setCoveringToHittingSet :=
  rfl

/-- The stored program is exactly the atom of the resolved direct-TM primitive. -/
@[simp]
theorem certifiedReduction_program_eq_atom :
    certifiedReduction.program =
      PolyProg.atom Problems.Karp21.SetSystemAtoms.setCoveringToHittingSetPrimitive :=
  rfl

/-- The stored program runs exactly the established Set-Covering-to-Hitting-Set map. -/
@[simp]
theorem certifiedReduction_run (input : sourceProblem.Instance) :
    certifiedReduction.program.run input = ComplexityReduction.Karp21.HittingSet.map input :=
  rfl

/-- The route's semantic iff is the Set-System atom theorem for the stored program. -/
theorem certifiedReduction_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔ targetProblem.accepts (certifiedReduction.program.run input) :=
  Problems.Karp21.SetSystemAtoms.setCoveringToHittingSet_correct input

/-- Direct-TM evidence is derived by compiling this same stored atom. -/
theorem certifiedReduction_directTM :
    ComplexityReduction.TMPolyTimeMap sourcePresentation.encodedType targetPresentation.encodedType
      certifiedReduction.program.run :=
  certifiedReduction.directTM

/-- The certificate's direct-TM field is precisely the complete atom compiler output. -/
@[simp]
theorem certifiedReduction_directTM_eq_atom_compileTM :
    certifiedReduction.directTM =
      Problems.Karp21.SetSystemAtoms.setCoveringToHittingSet.compileTM :=
  rfl

/-- The certificate program compiler is exactly the complete atom compiler. -/
@[simp]
theorem certifiedReduction_compileTM_eq_atom :
    certifiedReduction.program.compileTM =
      Problems.Karp21.SetSystemAtoms.setCoveringToHittingSet.compileTM :=
  rfl

/--
Compatibility declaration name retained for the axiom-audit surface; its
statement now identifies the atom primitive's direct-TM evidence, not a
separate legacy reduction.
-/
@[simp]
theorem certifiedReduction_compileTM_eq_legacy :
    certifiedReduction.program.compileTM =
      Problems.Karp21.SetSystemAtoms.setCoveringToHittingSetPrimitive.tmPolyTime :=
  rfl

/--
The certificate's compiler output is exactly the direct-TM field of the
read-only structured Karp witness, while still being obtained by compiling
the certificate's sole atom program.
-/
@[simp]
theorem certifiedReduction_compileTM_eq_structuredTMKarp :
    certifiedReduction.program.compileTM = structuredTMKarpReduction.polytime :=
  rfl

/-- The certificate's direct-TM facade is the same audited structured direct-TM witness. -/
@[simp]
theorem certifiedReduction_directTM_eq_structuredTMKarp :
    certifiedReduction.directTM = structuredTMKarpReduction.polytime :=
  rfl

/--
Projecting the canonical certificate back to a TM Karp reduction preserves
the complete structured direct-TM evidence.  No legacy reduction is used as
a V2 constructor: this is only the one-way projection of the certificate.
-/
@[simp]
theorem certifiedReduction_tmKarpReduction_eq_structuredTMKarp :
    certifiedReduction.toTMKarpReduction = structuredTMKarpReduction :=
  rfl

/--
The canonical certificate, its compiler, and its one-way TM-Karp projection
all coincide with the read-only structured CR witness at these exact
presentations.  The legacy witness is compared only after the certificate has
been constructed from its one stored atom.
-/
theorem certifiedReduction_structuredTMKarpCoherence :
    certifiedReduction.toTMKarpReduction = structuredTMKarpReduction ∧
      certifiedReduction.toTMKarpReduction.f = certifiedReduction.program.run ∧
      certifiedReduction.toTMKarpReduction.polytime = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM = structuredTMKarpReduction.polytime ∧
      certifiedReduction.program.compileTM = structuredTMKarpReduction.polytime := by
  exact ⟨certifiedReduction_tmKarpReduction_eq_structuredTMKarp,
    CertifiedReduction.toTMKarpReduction_f certifiedReduction, by
      rw [CertifiedReduction.toTMKarpReduction_polytime,
        CertifiedReduction.directTM_eq_compileTM],
    certifiedReduction_directTM_eq_structuredTMKarp,
    certifiedReduction_compileTM_eq_structuredTMKarp⟩

/-- The compatibility map is derived from the complete atom program compiler. -/
@[simp]
theorem certifiedReduction_tmBackedCostedMap :
    certifiedReduction.toTMBackedCostedMap =
      Problems.Karp21.SetSystemAtoms.setCoveringToHittingSet.compile :=
  rfl

/-- The route compatibility cost is only the compiler projection of the complete atom. -/
@[simp]
theorem certifiedReduction_compatibilityCost :
    certifiedReduction.compatibilityCost =
      Problems.Karp21.SetSystemAtoms.setCoveringToHittingSet.compatibilityCost :=
  rfl

/-- The compatibility cost follows only from this atom compiler's direct-TM output-size theorem. -/
@[simp]
theorem certifiedReduction_compatibilityCost_eq_outputSizeBound :
    certifiedReduction.compatibilityCost =
      ComplexityReduction.CostedMap.of_encodedPolynomialSizeBound
        (ComplexityReduction.TMPolyTimeMap.outputSizeBound
          Problems.Karp21.SetSystemAtoms.setCoveringToHittingSet.compileTM) :=
  Problems.Karp21.SetSystemAtoms.setCoveringToHittingSet.compatibilityCost_eq_outputSizeBound

/-- The concrete route keeps semantic, executable, TM, and cost evidence on its one atom. -/
theorem certifiedReduction_oneProgramChain :
    (∀ input,
      sourceProblem.accepts input ↔ targetProblem.accepts (certifiedReduction.program.run input)) ∧
      certifiedReduction.program =
        PolyProg.atom Problems.Karp21.SetSystemAtoms.setCoveringToHittingSetPrimitive ∧
      certifiedReduction.directTM = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM =
        Problems.Karp21.SetSystemAtoms.setCoveringToHittingSetPrimitive.tmPolyTime ∧
      certifiedReduction.compatibilityCost = certifiedReduction.program.compatibilityCost := by
  refine ⟨certifiedReduction.correct, certifiedReduction_program_eq_atom, ?_, ?_, ?_⟩
  · exact CertifiedReduction.directTM_eq_compileTM certifiedReduction
  · rfl
  · exact CertifiedReduction.compatibilityCost_eq_program_compatibilityCost certifiedReduction

/--
The shared component is indexed by the same faithful endpoints, and the route
stores the primitive as its only program atom.  This is the concrete provenance boundary for this
already-admitted edge: neither a cost map nor the read-only CR Karp record
appears as a constructor of the certificate.
-/
theorem sharedGadget_has_exact_complete_atom :
    certifiedReduction.program =
        PolyProg.atom Problems.Karp21.SetSystemAtoms.setCoveringToHittingSetPrimitive := by
  exact certifiedReduction_program_eq_atom

/--
The exact CR structured direct-TM theorem is the origin of the complete
atom's compiler witness.  This equality is evidence provenance only: the V2
certificate is still constructed from the typed atom above, not from this
legacy theorem value.
-/
@[simp]
theorem certifiedReduction_compileTM_eq_CRStructuredDirectTM :
    certifiedReduction.program.compileTM =
      ComplexityReduction.Karp21.HittingSet.setCoveringToHittingSetStructured_tm_polytime :=
  rfl

/--
The certificate's direct-TM facade is compiled from its stored atom and is
therefore the same exact structured direct-TM witness reused from CR.
-/
@[simp]
theorem certifiedReduction_directTM_eq_CRStructuredDirectTM :
    certifiedReduction.directTM =
      ComplexityReduction.Karp21.HittingSet.setCoveringToHittingSetStructured_tm_polytime :=
  rfl

/--
The compatibility-named legacy direct-TM observation is not an independent
machine: it is exactly the compiler output of the certificate's one atom.
-/
@[simp]
theorem legacyStructuredReduction_eq_certifiedReduction_compileTM :
    legacyStructuredReduction = certifiedReduction.program.compileTM :=
  rfl

/--
The full concrete structured-witness provenance chain.  In particular the
legacy Karp facade is only a one-way projection after the V2 certificate has
been assembled from its complete primitive atom.
-/
theorem certifiedReduction_completeAtomStructuredDirectTMProvenance :
    certifiedReduction.program =
        PolyProg.atom Problems.Karp21.SetSystemAtoms.setCoveringToHittingSetPrimitive ∧
      certifiedReduction.program.run = structuredTMKarpReduction.f ∧
      certifiedReduction.program.compileTM =
        ComplexityReduction.Karp21.HittingSet.setCoveringToHittingSetStructured_tm_polytime ∧
      certifiedReduction.directTM = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM = structuredTMKarpReduction.polytime ∧
      certifiedReduction.compatibilityCost = certifiedReduction.program.compatibilityCost ∧
      certifiedReduction.toTMKarpReduction = structuredTMKarpReduction := by
  exact ⟨certifiedReduction_program_eq_atom, rfl,
    certifiedReduction_compileTM_eq_CRStructuredDirectTM,
    CertifiedReduction.directTM_eq_compileTM certifiedReduction,
    certifiedReduction_directTM_eq_structuredTMKarp,
    CertifiedReduction.compatibilityCost_eq_program_compatibilityCost certifiedReduction,
    certifiedReduction_tmKarpReduction_eq_structuredTMKarp⟩

end SetCoveringToHittingSet
end Routes
end ComplexityReduction
