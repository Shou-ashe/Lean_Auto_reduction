/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP.Hardness.CoreReductions
import ComplexityReduction.Domain.BooleanCSP.Hardness.CanonicalHardCores

/-!
Schaefer's dichotomy: the hardness direction.

The natural-language proof (Schaefer 1978; Creignou–Khanna–Sudan Chapter 4)
shows: if a finite Boolean constraint language `Γ` is not contained in any of
the six tractable classes (0-valid, 1-valid, Horn, dual-Horn, bijunctive,
affine), then `CSP(Γ)` is NP-hard.  The proof proceeds in two steps:

1. *Hard cores*.  Positive 1-IN-3 receives an explicit direct-TM reduction
   from the library's fixed-three-colouring construction; positive 2-IN-3 is
   then obtained through the certified pp-interpretation compiler.  The
   existing direct reductions close the 3SAT-like and positive NAE-3 cores.
2. *Expressive power*.  `Hardness.SchaeferAlgebra` proves that pp-formulas
   preserve every Boolean operation preserving `Γ`, and performs the finite
   ternary-operation classification.  `Hardness.CanonicalDatabase` turns a
   separating polymorphism argument into a pp-definition automatically.
   Consequently `Hardness.CanonicalHardCores` constructs, without an axiom,
   an interpretation of positive 1-IN-3 or positive NAE-3 according as `Γ`
   fails or preserves complementation.  The generic direct-TM interpretation
   compiler then transports the corresponding closed core hardness proof.

The closed hardness direction is exposed as
`NativeTMNPHard_of_notSchaeferTractable`.
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

/-- Every hard core carries a closed certified native NP-hardness proof. -/
theorem nPHard (core : SchaeferHardCore) :
    NativeTMNPHard (problem core) := by
  cases core <;> simp [problem]
  · exact threeSATLikeCoreNPHard
  · exact nae3CoreNPHard
  · exact oneInThreeCoreNPHard
  · exact exactlyTwo3CoreNPHard

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
    (exactlyTwo3NPHard : NativeTMNPHard (cspOf exactlyTwo3Core)) :
    NativeTMNPHard (cspOf oneInThreeCore) :=
  nPHard_of_interpretation_auto oneInThreeInterpretsExactlyTwo3
    exactlyTwo3NPHard

/--
Hardness of the exactly-one core transports to the exactly-two core through
the complement interpretation, once the exactly-one core is known NP-hard.
-/
theorem nPHard_exactlyTwo3_of_oneInThree
    (oneInThreeNPHard : NativeTMNPHard (cspOf oneInThreeCore)) :
    NativeTMNPHard (cspOf exactlyTwo3Core) :=
  nPHard_of_interpretation_auto exactlyTwo3InterpretsOneInThree
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
    (coreNPHard : NativeTMNPHard (cspOf core)) :
    NativeTMNPHard (cspOf Γ) :=
  nPHard_of_interpretation_auto interpretation coreNPHard

/-! ### The expressive-power case analysis -/

/-- Schaefer's hardness theorem with every algebraic, semantic, and direct-TM
leaf closed in the kernel. -/
theorem NativeTMNPHard_of_notSchaeferTractable {Γ : Gamma} :
    (∀ symbol : Γ.Symbol, (Γ.relationOf symbol).Nonempty) →
    ¬ Γ.IsSchaeferTractable →
    NativeTMNPHard (cspOf Γ) := by
  intro nonempty notTractable
  rcases CanonicalHardCores.oneInThree_or_nae_interpretation
      nonempty notTractable with oneInThree | nae
  · rcases oneInThree with ⟨interpretation⟩
    exact nPHard_of_interpretsHardCore interpretation oneInThreeCoreNPHard
  · rcases nae with ⟨interpretation⟩
    exact nPHard_of_interpretsHardCore interpretation nae3CoreNPHard

/-- Compatibility wrapper for clients that used to supply the now-closed
positive 1-IN-3 hardness leaf. -/
theorem NativeTMNPHard_of_notSchaeferTractable_with_oneInThree
    (Γ : Gamma)
    (_oneInThreeNPHard : NativeTMNPHard (cspOf oneInThreeCore))
    (nonempty : ∀ symbol : Γ.Symbol, (Γ.relationOf symbol).Nonempty)
    (notTractable : ¬ Γ.IsSchaeferTractable) :
    NativeTMNPHard (cspOf Γ) :=
  NativeTMNPHard_of_notSchaeferTractable nonempty notTractable

assert_standard_axioms
  oneInThree_ppDefined_by_exactlyTwo3,
  exactlyTwo3_ppDefined_by_oneInThree,
  nPHard_oneInThree_of_exactlyTwo3,
  nPHard_exactlyTwo3_of_oneInThree,
  SchaeferHardCore.nPHard,
  nPHard_of_interpretsHardCore,
  NativeTMNPHard_of_notSchaeferTractable,
  NativeTMNPHard_of_notSchaeferTractable_with_oneInThree

end Hardness
end BooleanCSP
end Domain
end ComplexityReduction
