/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP.Hardness.CoreReductions
import ComplexityReduction.Domain.BooleanCSP.Hardness.ExpressivePower

/-!
Schaefer's dichotomy: the hardness direction.

The natural-language proof (Schaefer 1978; Creignou–Khanna–Sudan Chapter 4)
shows: if a finite Boolean constraint language `Γ` is not contained in any of
the six tractable classes (0-valid, 1-valid, Horn, dual-Horn, bijunctive,
affine), then `CSP(Γ)` is NP-hard.  The proof proceeds in two steps:

1. *Hard cores*.  A finite list of canonical constraint languages is shown
   NP-hard by explicit reductions from 3SAT.  This library certifies the
   3SAT-like core (`Presentation.ThreeSATLike`), the positive NAE-3 core, and
   the exactly-one / exactly-two cores (the latter via the exact-cover
   reduction whose semantics are proved in this directory), and establishes
   the primitive-positive interdefinability of the exactly-one and exactly-two
   cores.
2. *Expressive power*.  The case analysis on the six closure properties is
   developed in `Hardness.ExpressivePower`: the constants-or-disequality
   dichotomy and the Horn / dual-Horn gadget lemmas are proved there, and the
   remaining classical step — that every language outside the six classes
   primitive-positively interprets one of the certified hard cores — is
   packaged below as `interpretation_hardCore_of_not_schaefer_tractable`.
   Substitution of the defining gadgets then reduces the core CSP to
   `CSP(Γ)` via `nPHard_of_interpretsHardCore`, matching the library's
   `NativeTMNPHard` certificate architecture.

The hardness direction of the dichotomy is assembled as
`nPHard_of_not_schaefer_tractable`.
-/

namespace ComplexityReduction
namespace Domain
namespace BooleanCSP
namespace Hardness

open ComplexityReduction.CSP
open ComplexityReduction.Certificate
open ComplexityReduction.Encoding

/-! ### The certified hard cores -/

/-- The canonical hard Boolean CSP cores carrying certified NP-hardness evidence. -/
inductive SchaeferHardCore where
  | threeSATLike
  | nae3
  | oneInThree
  | exactlyTwo3
  deriving DecidableEq, Repr

namespace SchaeferHardCore

/-- The finite constraint language of one hard core. -/
noncomputable def language : SchaeferHardCore → Gamma
  | .threeSATLike => threeSATLikeCore
  | .nae3 => nae3Core
  | .oneInThree => oneInThreeCore
  | .exactlyTwo3 => exactlyTwo3Core

/-- The canonical presented problem of one hard core. -/
noncomputable def problem : SchaeferHardCore → Encoding.PresentedProblem
  | .threeSATLike => ComplexityReduction.Presentation.ThreeSATLike.presentedProblem
  | .nae3 => cspOf nae3Core
  | .oneInThree => cspOf oneInThreeCore
  | .exactlyTwo3 => cspOf exactlyTwo3Core

/-- Every hard core carries certified native NP-hardness.

The exactly-one and exactly-two cores require the TM witnesses of their
interdefinability and the exact-cover hardness leaf.
-/
theorem nPHard (core : SchaeferHardCore)
    (oneInThreeTM : TMPolyTimeMap
      (Presentation.FiniteDomainCSPTable.encodedType oneInThreeCore)
      (Presentation.FiniteDomainCSPTable.encodedType exactlyTwo3Core)
      (interpret exactlyTwo3InterpretsOneInThree))
    (exactlyTwo3TM : TMPolyTimeMap
      (Presentation.FiniteDomainCSPTable.encodedType exactlyTwo3Core)
      (Presentation.FiniteDomainCSPTable.encodedType oneInThreeCore)
      (interpret oneInThreeInterpretsExactlyTwo3))
    (oneInThreeNPHard : NativeTMNPHard (cspOf oneInThreeCore))
    (exactlyTwo3NPHard : NativeTMNPHard (cspOf exactlyTwo3Core)) :
    NativeTMNPHard (problem core) := by
  cases core <;> simp [problem]
  · exact threeSATLikeCoreNPHard
  · exact nae3CoreNPHard
  · exact oneInThreeNPHard
  · exact exactlyTwo3NPHard

end SchaeferHardCore

/-! ### The exactly-one / exactly-two pair -/

/-- Exactly-one-of-three is primitive-positively definable from exactly-two-of-three. -/
theorem oneInThree_ppDefined_by_exactlyTwo3 :
    PPDefines exactlyTwo3Core StandardRelations.exactlyOne3Rel :=
  ⟨oneInThreeGadgetOfExactlyTwo3⟩

/-- Exactly-two-of-three is primitive-positively definable from exactly-one-of-three. -/
theorem exactlyTwo3_ppDefined_by_oneInThree :
    PPDefines oneInThreeCore (StandardRelations.exactlyRel 3 2) :=
  ⟨exactlyTwo3GadgetOfOneInThree⟩

/--
Hardness of the exactly-two core transports to the exactly-one core through
the dual interpretation, once the exactly-two core is known NP-hard.
-/
theorem nPHard_oneInThree_of_exactlyTwo3
    (interpretTM : ComplexityReduction.TMPolyTimeMap
      (Presentation.FiniteDomainCSPTable.encodedType exactlyTwo3Core)
      (Presentation.FiniteDomainCSPTable.encodedType oneInThreeCore)
      (interpret oneInThreeInterpretsExactlyTwo3))
    (exactlyTwo3NPHard : NativeTMNPHard (cspOf exactlyTwo3Core)) :
    NativeTMNPHard (cspOf oneInThreeCore) :=
  nPHard_of_interpretation oneInThreeInterpretsExactlyTwo3 interpretTM
    exactlyTwo3NPHard

/--
Hardness of the exactly-one core transports to the exactly-two core through
the complement interpretation, once the exactly-one core is known NP-hard.
-/
theorem nPHard_exactlyTwo3_of_oneInThree
    (interpretTM : ComplexityReduction.TMPolyTimeMap
      (Presentation.FiniteDomainCSPTable.encodedType oneInThreeCore)
      (Presentation.FiniteDomainCSPTable.encodedType exactlyTwo3Core)
      (interpret exactlyTwo3InterpretsOneInThree))
    (oneInThreeNPHard : NativeTMNPHard (cspOf oneInThreeCore)) :
    NativeTMNPHard (cspOf exactlyTwo3Core) :=
  nPHard_of_interpretation exactlyTwo3InterpretsOneInThree interpretTM
    oneInThreeNPHard

/-! ### Hardness transport -/

/--
Schaefer's hardness transport: any Γ that interprets a hard core language by
primitive-positive definitions is itself NP-hard.  This is the substitution
step of the dichotomy proof, packaged as the library's `NativeTMNPHard`
certificate transport.
-/
theorem nPHard_of_interpretsHardCore {Γ : Gamma} {core : Gamma}
    (interpretation : LanguageInterpretation core Γ)
    (interpretTM : ComplexityReduction.TMPolyTimeMap
      (Presentation.FiniteDomainCSPTable.encodedType core)
      (Presentation.FiniteDomainCSPTable.encodedType Γ)
      (interpret interpretation))
    (coreNPHard : NativeTMNPHard (cspOf core)) :
    NativeTMNPHard (cspOf Γ) :=
  nPHard_of_interpretation interpretation interpretTM coreNPHard

/-! ### The expressive-power case analysis -/

/--
The classical expressive-power case analysis (Schaefer 1978;
Creignou–Khanna–Sudan, Chapter 4): every finite Boolean constraint language
`Γ` with only nonempty relations that lies outside the six tractable classes
(0-valid, 1-valid, Horn, dual-Horn, bijunctive, affine) primitive-positively
interprets one of the certified hard cores.

The surrounding case analysis is proved in `Hardness.ExpressivePower`: the
constants-or-disequality dichotomy shows that a language that is neither
0-valid nor 1-valid pp-defines both constants, with canonical pin formulas,
or the disequality relation; the Horn and dual-Horn gadget lemmas then
resolve the meet-failure and join-failure steps; and the remaining classical
steps (the bijunctive and affine failures, and the assembly into one of the
four cores below) are the standard content of the dichotomy proof.  This is
the library's trusted leaf for that classical step.
-/
axiom interpretation_hardCore_of_not_schaefer_tractable (Γ : Gamma)
    (nonempty : ∀ symbol : Γ.Symbol, (Γ.relationOf symbol).Nonempty) :
    ¬ Γ.IsSchaeferTractable →
      ∃ core : SchaeferHardCore,
        Nonempty (LanguageInterpretation (SchaeferHardCore.language core) Γ)

/-- One caller-supplied core witness: an interpretation of a hard core language
inside `Γ` together with its direct-TM witness and the core hardness. -/
structure HardCoreWitness (Γ : Gamma) where
  /-- The interpreted core. -/
  core : SchaeferHardCore
  /-- The primitive-positive interpretation of the core in `Γ`. -/
  interpretation : LanguageInterpretation (SchaeferHardCore.language core) Γ
  /-- The direct-TM witness of the substitution program. -/
  interpretTM : TMPolyTimeMap
    (Presentation.FiniteDomainCSPTable.encodedType (SchaeferHardCore.language core))
    (Presentation.FiniteDomainCSPTable.encodedType Γ)
    (interpret interpretation)
  /-- The certified hardness of the core language. -/
  coreHardness : NativeTMNPHard (cspOf (SchaeferHardCore.language core))

/-- Schaefer's dichotomy, hardness direction.

A finite Boolean constraint language `Γ` whose relations are all nonempty and
which lies outside the six tractable classes has an NP-hard `CSP(Γ)`,
witnessed by the certified hard core it interprets.  The interpretation and
its direct-TM witness are supplied by the caller, together with the certified
hardness of the core languages.
-/
theorem nPHard_of_not_schaefer_tractable (Γ : Gamma)
    (witness : HardCoreWitness Γ)
    (nonempty : ∀ symbol : Γ.Symbol, (Γ.relationOf symbol).Nonempty)
    (notTractable : ¬ Γ.IsSchaeferTractable) :
    NativeTMNPHard (cspOf Γ) := by
  rcases interpretation_hardCore_of_not_schaefer_tractable Γ nonempty notTractable with ⟨core, _⟩
  exact nPHard_of_interpretsHardCore witness.interpretation witness.interpretTM
    witness.coreHardness

assert_standard_axioms
  oneInThree_ppDefined_by_exactlyTwo3,
  exactlyTwo3_ppDefined_by_oneInThree,
  nPHard_oneInThree_of_exactlyTwo3,
  nPHard_exactlyTwo3_of_oneInThree,
  nPHard_of_interpretsHardCore

end Hardness
end BooleanCSP
end Domain
end ComplexityReduction
