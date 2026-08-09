/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Certificate.NativeCompleteness
import ComplexityReduction.Certificate.Path

/-!
Transport of exact native NP-completeness along a certified forward path.

The direction is deliberately `hub -> target`.  Native membership of the
target is an explicit premise, while hardness is obtained by composing each
exact native source-to-hub certificate with the path's canonical
hub-to-target certificate.  A path in the opposite direction has the wrong
type and cannot enter this constructor.
-/

namespace ComplexityReduction
namespace Certificate
namespace CompletenessTransport

open Encoding

/--
Transport native completeness from one exact complete hub to one exact native-NP target.

No backend membership or backend completeness proposition occurs in the
signature.  The only hardness construction is the program-indexed
`CertifiedReduction.comp` of the path certificate after the source-to-hub
certificate supplied by the native completeness premise.
-/
def alongPath {hub target : PresentedProblem}
    (hubCompleteness : NativeTMNPComplete hub)
    (path : CertifiedPath hub target)
    (targetMembership : NativeTMInNP target) : NativeTMNPComplete target where
  membership := targetMembership
  hardness := by
    intro source sourceMembership
    rcases hubCompleteness.certifiedHardness sourceMembership with ⟨sourceToHub⟩
    exact ⟨CertifiedReduction.comp path.toCertifiedReduction sourceToHub⟩

@[simp]
theorem alongPath_membership {hub target : PresentedProblem}
    (hubCompleteness : NativeTMNPComplete hub)
    (path : CertifiedPath hub target)
    (targetMembership : NativeTMInNP target) :
    (alongPath hubCompleteness path targetMembership).membership = targetMembership :=
  rfl

end CompletenessTransport

namespace NativeTMNPHard

open Encoding

/--
Transport exact native hardness along a certified forward path.

The path direction is fixed by its type: the hard hub is the source and the
new hard problem is the target.  No membership premise is needed for the
target because this constructor proves hardness only.
-/
def alongPath {hub target : PresentedProblem}
    (hubHardness : NativeTMNPHard hub)
    (path : CertifiedPath hub target) : NativeTMNPHard target := by
  intro source sourceMembership
  rcases hubHardness source sourceMembership with ⟨sourceToHub⟩
  exact ⟨CertifiedReduction.comp path.toCertifiedReduction sourceToHub⟩

/--
Transport exact native hardness from a complete hub along an already certified
forward path.  Unlike completeness transport, this construction needs no
membership premise for the target and therefore proves only `NativeTMNPHard`.
-/
def ofCompleteAlongPath {hub target : PresentedProblem}
    (hubCompleteness : NativeTMNPComplete hub)
    (path : CertifiedPath hub target) : NativeTMNPHard target :=
  alongPath hubCompleteness.nativeHardness path

end NativeTMNPHard
end Certificate
end ComplexityReduction
