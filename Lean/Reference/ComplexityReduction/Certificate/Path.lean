/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Core.ComponentRole
import ComplexityReduction.Certificate.PresentationChange
import ComplexityReduction.Certificate.Provenance

/-!
Arbitrary-length, endpoint-indexed composition of canonical V2 certificates.

`CertifiedPath` contains only exact `CertifiedReduction` atoms.  Its sole
certificate projection is structural composition of those atoms, so the final
semantic executable, direct-TM witness, and compatibility-cost projection are
all inherited from the one nested `PolyProg.comp` tree.  It never accepts a
second route-level map, cost, TM, or semantic proof.

`CertifiedPathProvenance` adds one non-capability component role to every
atomic edge.  Both the atom and its exact endpoints remain indices of the
provenance term; the final certificate is likewise an index and is provably
the path's canonical composite.  This generalizes the fixed 2--3 component
`CertifiedRouteProvenance` without replacing that compatibility view.
-/

namespace ComplexityReduction
namespace Certificate

open Encoding Program

/-- An arbitrary-length chain of endpoint-compatible canonical V2 reductions. -/
inductive CertifiedPath : PresentedProblem → PresentedProblem → Type 2 where
  | refl (problem : PresentedProblem) : CertifiedPath problem problem
  | step {source target : PresentedProblem} (certificate : CertifiedReduction source target) :
      CertifiedPath source target
  | cons {source middle target : PresentedProblem}
      (initial : CertifiedPath source middle) (last : CertifiedReduction middle target) :
      CertifiedPath source target

namespace CertifiedPath

/-- The canonical certificate for a path, assembled only from its atomic certificates. -/
def toCertifiedReduction : {source target : PresentedProblem} →
    CertifiedPath source target → CertifiedReduction source target
  | _, _, .refl problem => CertifiedReduction.refl problem
  | _, _, .step certificate => certificate
  | _, _, .cons initial last => CertifiedReduction.comp last initial.toCertifiedReduction

/-- The number of stored atomic certificate edges; reflexivity contributes none. -/
def length : {source target : PresentedProblem} → CertifiedPath source target → Nat
  | _, _, .refl _ => 0
  | _, _, .step _ => 1
  | _, _, .cons initial _ => initial.length + 1

/-- Append two endpoint-compatible paths without introducing any new certificate atom. -/
def append : {source middle target : PresentedProblem} →
    CertifiedPath source middle → CertifiedPath middle target → CertifiedPath source target
  | _, _, _, .refl _, after => after
  | _, _, _, before, .refl _ => before
  | _, _, _, before, .step after => .cons before after
  | _, _, _, before, .cons initial last => .cons (before.append initial) last

/-- A one-edge path compiles to that exact edge rather than a route-level wrapper. -/
@[simp] theorem toCertifiedReduction_step {source target : PresentedProblem}
    (certificate : CertifiedReduction source target) :
    (step certificate).toCertifiedReduction = certificate :=
  by
    unfold toCertifiedReduction
    rfl

/-- Reflexive paths compile to the exact identity certificate at their endpoint. -/
@[simp] theorem toCertifiedReduction_refl (problem : PresentedProblem) :
    (refl problem).toCertifiedReduction = CertifiedReduction.refl problem :=
  by
    unfold toCertifiedReduction
    rfl

/-- Extending a path composes its final program with precisely the new final atom. -/
@[simp] theorem toCertifiedReduction_cons {source middle target : PresentedProblem}
    (initial : CertifiedPath source middle) (last : CertifiedReduction middle target) :
    (cons initial last).toCertifiedReduction =
      CertifiedReduction.comp last initial.toCertifiedReduction :=
  by
    induction initial generalizing target with
    | refl =>
        unfold toCertifiedReduction
        rw [toCertifiedReduction_refl]
    | step =>
        unfold toCertifiedReduction
        rw [toCertifiedReduction_step]
    | cons initial previous ih =>
        unfold toCertifiedReduction
        rw [ih previous]

/-- The one-edge path retains exactly one atomic certificate. -/
@[simp] theorem length_step {source target : PresentedProblem}
    (certificate : CertifiedReduction source target) :
    (step certificate).length = 1 :=
  by
    unfold length
    rfl

/-- Composition adds no atom beyond the final certificate already stored by `cons`. -/
@[simp] theorem length_refl (problem : PresentedProblem) :
    (refl problem).length = 0 := by
  unfold length
  rfl

@[simp] theorem length_step' {source target : PresentedProblem}
    (certificate : CertifiedReduction source target) :
    (step certificate).length = 1 :=
  length_step certificate

@[simp] theorem length_cons {source middle target : PresentedProblem}
    (initial : CertifiedPath source middle) (last : CertifiedReduction middle target) :
    (cons initial last).length = initial.length + 1 :=
  by
    induction initial generalizing target with
    | refl =>
        unfold length
        rw [length_refl]
    | step =>
        unfold length
        rw [length_step']
    | cons initial previous ih =>
        unfold length
        rw [ih previous]

/-- A composite path's program is the nested composition of its atomic programs. -/
@[simp] theorem toCertifiedReduction_cons_program {source middle target : PresentedProblem}
    (initial : CertifiedPath source middle) (last : CertifiedReduction middle target) :
    (cons initial last).toCertifiedReduction.program =
      PolyProg.comp last.program initial.toCertifiedReduction.program :=
  by
    induction initial generalizing target with
    | refl =>
        unfold toCertifiedReduction
        rw [toCertifiedReduction_refl]
        exact CertifiedReduction.comp_program last (CertifiedReduction.refl source)
    | step certificate =>
        unfold toCertifiedReduction
        rw [toCertifiedReduction_step]
        exact CertifiedReduction.comp_program last _
    | cons initial previous ih =>
        unfold toCertifiedReduction
        rw [CertifiedReduction.comp_program]
        rw [ih previous]
        rw [CertifiedReduction.comp_program]

/-- Direct-TM reducibility is projected only from the final canonical composite. -/
theorem toTMPolyReducible {source target : PresentedProblem}
    (path : CertifiedPath source target) :
    ComplexityReduction.TMPolyReducible
      source.toEncodedDecisionProblem target.toEncodedDecisionProblem :=
  path.toCertifiedReduction.toTMPolyReducible

/-- The direct-TM Karp projection is the canonical projection of the final composite. -/
def toTMKarpReduction {source target : PresentedProblem}
    (path : CertifiedPath source target) :
    ComplexityReduction.TMKarpReduction
      source.toEncodedDecisionProblem target.toEncodedDecisionProblem :=
  path.toCertifiedReduction.toTMKarpReduction

/-- The compatibility Karp projection is likewise derived only from the final composite. -/
def toCostedKarpReduction {source target : PresentedProblem}
    (path : CertifiedPath source target) :
    ComplexityReduction.KarpReductionM ComplexityReduction.CostedPolyTimeModel
      source.toEncodedDecisionProblem target.toEncodedDecisionProblem :=
  path.toCertifiedReduction.toCostedKarpReduction

/-- The path's direct-TM Karp facade is exactly the final certificate facade. -/
@[simp] theorem toTMKarpReduction_eq_final {source target : PresentedProblem}
    (path : CertifiedPath source target) :
    path.toTMKarpReduction = path.toCertifiedReduction.toTMKarpReduction :=
  rfl

/-- The path's compatibility Karp facade is exactly the final certificate facade. -/
@[simp] theorem toCostedKarpReduction_eq_final {source target : PresentedProblem}
    (path : CertifiedPath source target) :
    path.toCostedKarpReduction = path.toCertifiedReduction.toCostedKarpReduction :=
  rfl

/-- The final direct-TM witness is compiled from the same nested program as the final certificate. -/
@[simp] theorem directTM_eq_final_compileTM {source target : PresentedProblem}
    (path : CertifiedPath source target) :
    path.toCertifiedReduction.directTM = path.toCertifiedReduction.program.compileTM :=
  rfl

end CertifiedPath

/--
Role-indexed provenance for an arbitrary-length certified path.

The final certificate index can only be the structural composition of the
stored atomic certificates.  `ReductionComponentRole` is intentionally only
provenance: changing it cannot construct, replace, or upgrade a certificate.
-/
inductive CertifiedPathProvenance :
    {source target : PresentedProblem} →
    (path : CertifiedPath source target) →
    (finalCertificate : CertifiedReduction source target) → Type 2 where
  | refl (problem : PresentedProblem) :
      CertifiedPathProvenance (.refl problem) (CertifiedReduction.refl problem)
  | step {source target : PresentedProblem}
      (role : ReductionComponentRole) (certificate : CertifiedReduction source target) :
      CertifiedPathProvenance (.step certificate) certificate
  | cons {source middle target : PresentedProblem}
      (role : ReductionComponentRole) (initial : CertifiedPath source middle)
      (initialCertificate : CertifiedReduction source middle)
      (initialProvenance : CertifiedPathProvenance initial initialCertificate)
      (last : CertifiedReduction middle target) :
      CertifiedPathProvenance (.cons initial last)
        (CertifiedReduction.comp last initialCertificate)

namespace CertifiedPathProvenance

/-- Introduce a one-edge role-indexed provenance record. -/
def atomic {source target : PresentedProblem}
    (role : ReductionComponentRole) (certificate : CertifiedReduction source target) :
    CertifiedPathProvenance (.step certificate) certificate :=
  .step role certificate

/-- Extend role-indexed provenance by one exact target-side atomic certificate. -/
def appendAtomic {source middle target : PresentedProblem}
    (role : ReductionComponentRole) {initial : CertifiedPath source middle}
    {initialCertificate : CertifiedReduction source middle}
    (initialProvenance : CertifiedPathProvenance initial initialCertificate)
    (last : CertifiedReduction middle target) :
    CertifiedPathProvenance (.cons initial last)
      (CertifiedReduction.comp last initialCertificate) :=
  .cons role initial initialCertificate initialProvenance last

/--
Project the legacy fixed two-component provenance shape into arbitrary-length
atomic provenance.  The original final index is preserved exactly; this is a
one-way compatibility projection and does not add a second certificate.
-/
def ofIdentityRouteProvenance {source hub target : PresentedProblem}
    {ingress : CertifiedReduction source hub}
    {sharedGadget : CertifiedReduction hub target}
    (provenance : CertifiedRouteProvenance ingress sharedGadget .identity
      (CertifiedReduction.comp sharedGadget ingress)) :
    CertifiedPathProvenance
      (.cons (.step ingress) sharedGadget)
      (CertifiedReduction.comp sharedGadget ingress) :=
  match provenance with
  | .identity ingress sharedGadget =>
      .cons .sharedGadget (.step ingress) ingress (.step .ingress ingress) sharedGadget

/--
Project the legacy fixed three-component provenance shape into arbitrary-length
atomic provenance while retaining the ingress, shared, and egress atoms.
-/
def ofExplicitRouteProvenance {source hub egressSource target : PresentedProblem}
    {ingress : CertifiedReduction source hub}
    {sharedGadget : CertifiedReduction hub egressSource}
    {egress : CertifiedReduction egressSource target}
    (provenance : CertifiedRouteProvenance ingress sharedGadget (.explicit egress)
      (CertifiedReduction.comp egress (CertifiedReduction.comp sharedGadget ingress))) :
    CertifiedPathProvenance
      (.cons (.cons (.step ingress) sharedGadget) egress)
      (CertifiedReduction.comp egress (CertifiedReduction.comp sharedGadget ingress)) :=
  match provenance with
  | .explicit ingress sharedGadget egress =>
      .cons .egress (.cons (.step ingress) sharedGadget)
        (CertifiedReduction.comp sharedGadget ingress)
        (.cons .sharedGadget (.step ingress) ingress (.step .ingress ingress) sharedGadget)
        egress

/-- The final certificate carried by provenance is definitionally the path's canonical composite. -/
theorem final_eq_toCertifiedReduction
    {source target : PresentedProblem} {path : CertifiedPath source target}
    {finalCertificate : CertifiedReduction source target}
    (provenance : CertifiedPathProvenance path finalCertificate) :
    finalCertificate = path.toCertifiedReduction := by
  induction provenance with
  | refl => simp
  | step => simp
  | cons _ _ _ _ _ inductionHypothesis =>
      simp only [CertifiedPath.toCertifiedReduction_cons]
      rw [inductionHypothesis]

/-- Appending records a final program which is exactly the nested program composition. -/
theorem appendAtomic_program {source middle target : PresentedProblem}
    (_role : ReductionComponentRole) {initial : CertifiedPath source middle}
    {initialCertificate : CertifiedReduction source middle}
    (_initialProvenance : CertifiedPathProvenance initial initialCertificate)
    (last : CertifiedReduction middle target) :
    (CertifiedReduction.comp last initialCertificate).program =
      PolyProg.comp last.program initialCertificate.program :=
  rfl

end CertifiedPathProvenance

end Certificate
end ComplexityReduction
