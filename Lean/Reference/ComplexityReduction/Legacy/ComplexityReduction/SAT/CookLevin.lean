/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Core.Completeness
import ComplexityReduction.Legacy.ComplexityReduction.SAT.ThreeSATInNP
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.Tableau
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.WindowGrid

/-!
Cook-Levin theorem surface for the reusable SAT library layer.

The full theorem surface is represented by `CookLevinTheorem`: a proof object
that turns each explicit costed NP verifier into a syntactic, costed Karp
reduction to local 3SAT.  The current local construction covers
`MachineBackedNPVerifier`, where a finite verifier-machine syntax and a Cook
tableau certificate are supplied explicitly.  This file packages the standard
consequences without introducing an oracle-style or decision-dependent
reduction.
-/

namespace ComplexityReduction
namespace SAT

/--
Cook-Levin output for one explicit NP verifier.

The fields are intentionally syntactic: callers must provide the tableau-to-3CNF
map and its costed polynomial-time certificate.  In particular, this structure
does not permit a proof that only branches on source satisfiability.
-/
structure CookLevinVerifierReduction {L : EncodedDecisionProblem}
    (V : NPVerifier CostedPolyTimeModel L) where
  cookTableauThreeCNF : L.Instance.Carrier → ThreeCNF
  cookTableauThreeCNF_polytime :
    CostedPolyTimeModel.IsPolyTimeMap
      (X := L.Instance) (Y := threeSATDecisionProblem.Instance) cookTableauThreeCNF
  cookTableauThreeCNF_correct :
    ∀ x, L.isYes x ↔ ThreeCNF.Satisfiable (cookTableauThreeCNF x)

namespace CookLevinVerifierReduction

/-- View a Cook-Levin verifier reduction as a model-level Karp reduction to 3SAT. -/
def toKarpReduction {L : EncodedDecisionProblem}
    {V : NPVerifier CostedPolyTimeModel L} (R : CookLevinVerifierReduction V) :
    KarpReductionM CostedPolyTimeModel L threeSATDecisionProblem where
  f := { toFun := R.cookTableauThreeCNF, polytime := R.cookTableauThreeCNF_polytime }
  correct := by
    intro x
    exact R.cookTableauThreeCNF_correct x

end CookLevinVerifierReduction

/--
Semantic correctness shape for the Cook tableau 3CNF: satisfiability is
equivalent to the verifier accepting some certificate.
-/
theorem cookTableauThreeCNF_satisfiable_iff_accepts {L : EncodedDecisionProblem}
    {V : NPVerifier CostedPolyTimeModel L} (R : CookLevinVerifierReduction V)
    (x : L.Instance.Carrier) :
    ThreeCNF.Satisfiable (R.cookTableauThreeCNF x) ↔ ∃ c, V.verify x c = true :=
  (R.cookTableauThreeCNF_correct x).symm.trans (V.correct_iff x)

/--
Machine-backed NP verifier.

This is the local foundation needed by the actual Cook tableau construction:
the verifier is still exposed as the existing `NPVerifier`, but it also carries
an explicit finite machine syntax and a costed Cook tableau whose accepting-run
predicate is proved equivalent to `verify`.
-/
structure MachineBackedNPVerifier (L : EncodedDecisionProblem) where
  machine : CookLevin.BoundedMachineSyntax
  verifier : NPVerifier CostedPolyTimeModel L
  tableau : CookLevin.CostedCookTableauConstruction L verifier.Cert
  accepts_iff_verify :
    ∀ x c, tableau.tableau.accepts x c ↔ verifier.verify x c = true

namespace MachineBackedNPVerifier

/-- Forget the machine/tableau witness and expose the legacy verifier surface. -/
def toNPVerifier {L : EncodedDecisionProblem} (V : MachineBackedNPVerifier L) :
    NPVerifier CostedPolyTimeModel L :=
  V.verifier

/-- Package a machine-backed verifier as a local direct NP witness. -/
def toLocalNPVerifier {L : EncodedDecisionProblem} (V : MachineBackedNPVerifier L) :
    LocalNPVerifier CostedPolyTimeModel L where
  verifier := V.verifier
  cookTableauThreeCNF := V.tableau.tableau.cookTableauThreeCNF
  cookTableauThreeCNF_polytime := V.tableau.cookTableauThreeCNF_polytime
  cookTableauThreeCNF_correct := by
    intro x
    have hVerifier := V.verifier.correct_iff x
    have hTableau :=
      V.tableau.tableau.cookTableauThreeCNF_satisfiable_iff_accepts x
    constructor
    · intro hx
      rcases hVerifier.1 hx with ⟨c, hc⟩
      exact hTableau.2 ⟨c, (V.accepts_iff_verify x c).2 hc⟩
    · intro hSat
      rcases hTableau.1 hSat with ⟨c, hc⟩
      exact hVerifier.2 ⟨c, (V.accepts_iff_verify x c).1 hc⟩

/-- Machine-backed verifiers still prove ordinary encoded NP membership. -/
theorem inNP {L : EncodedDecisionProblem} (V : MachineBackedNPVerifier L) :
    InNPEnc CostedPolyTimeModel L :=
  InNPEnc.intro V.toLocalNPVerifier

/-- The local Cook tableau of a machine-backed verifier is equivalent to verifier acceptance. -/
theorem cookTableauThreeCNF_satisfiable_iff_verify {L : EncodedDecisionProblem}
    (V : MachineBackedNPVerifier L) (x : L.Instance.Carrier) :
    (V.tableau.tableau.cookTableauThreeCNF x).Satisfiable ↔
      ∃ c, V.verifier.verify x c = true := by
  have hTableau :=
    V.tableau.tableau.cookTableauThreeCNF_satisfiable_iff_accepts x
  constructor
  · intro hSat
    rcases hTableau.1 hSat with ⟨c, hc⟩
    exact ⟨c, (V.accepts_iff_verify x c).1 hc⟩
  · rintro ⟨c, hc⟩
    exact hTableau.2 ⟨c, (V.accepts_iff_verify x c).2 hc⟩

/-- Convert a machine-backed verifier into the standard Cook-Levin reduction object. -/
def toCookLevinVerifierReduction {L : EncodedDecisionProblem}
    (V : MachineBackedNPVerifier L) :
    CookLevinVerifierReduction V.toNPVerifier where
  cookTableauThreeCNF := V.tableau.tableau.cookTableauThreeCNF
  cookTableauThreeCNF_polytime := V.tableau.cookTableauThreeCNF_polytime
  cookTableauThreeCNF_correct := by
    intro x
    have hVerifier := V.verifier.correct_iff x
    have hTableau := V.cookTableauThreeCNF_satisfiable_iff_verify x
    constructor
    · intro hx
      exact hTableau.2 (hVerifier.1 hx)
    · intro hSat
      exact hVerifier.2 (hTableau.1 hSat)

end MachineBackedNPVerifier

/--
Machine-backed encoded NP: direct members have explicit verifier machines and
Cook tableau certificates, then the class is closed downward under reductions.
-/
inductive InNPMachineEnc : EncodedDecisionProblem → Prop
  | of_machine_verifier {L : EncodedDecisionProblem}
      (V : MachineBackedNPVerifier L) : InNPMachineEnc L
  | reduction_closure {A B : EncodedDecisionProblem}
      (hAB : PolyReducibleM CostedPolyTimeModel A B)
      (hB : InNPMachineEnc B) : InNPMachineEnc A

namespace InNPMachineEnc

/-- Build machine-backed encoded NP membership from an explicit verifier machine. -/
theorem intro {L : EncodedDecisionProblem} (V : MachineBackedNPVerifier L) :
    InNPMachineEnc L :=
  InNPMachineEnc.of_machine_verifier V

/-- Machine-backed encoded NP is downward closed under costed reductions. -/
theorem of_reduction {A B : EncodedDecisionProblem}
    (hAB : PolyReducibleM CostedPolyTimeModel A B) (hB : InNPMachineEnc B) :
    InNPMachineEnc A :=
  InNPMachineEnc.reduction_closure hAB hB

/-- Forget machine-backed membership to the existing encoded NP class. -/
theorem toInNPEnc {L : EncodedDecisionProblem} (hL : InNPMachineEnc L) :
    InNPEnc CostedPolyTimeModel L := by
  induction hL with
  | of_machine_verifier V =>
      exact V.inNP
  | reduction_closure hAB _ ih =>
      exact InNPEnc.of_reduction hAB ih

end InNPMachineEnc

/-- The machine-backed encoded NP subclass as a reusable complexity-class object. -/
def machineNPClass : ComplexityClass CostedPolyTimeModel where
  mem := InNPMachineEnc
  of_reduction := InNPMachineEnc.of_reduction

/-- Completeness for the machine-backed encoded NP subclass. -/
abbrev MachineCompleteFor (L : EncodedDecisionProblem) : Prop :=
  CompleteFor CostedPolyTimeModel machineNPClass L

/-- 3SAT completeness for the machine-backed NP subclass. -/
def MachineNPCompleteEnc (L : EncodedDecisionProblem) : Prop :=
  InNPEnc CostedPolyTimeModel L ∧
    ∀ L', InNPMachineEnc L' → PolyReducibleM CostedPolyTimeModel L' L

namespace ThreeSATMachineVerifier

/-- A minimal dummy machine syntax for the already-3CNF verifier specialization. -/
def machine : CookLevin.BoundedMachineSyntax where
  State := Unit
  stateFinite := inferInstance
  stateDecidableEq := inferInstance
  Symbol := Unit
  symbolFinite := inferInstance
  symbolDecidableEq := inferInstance
  start := ()
  accept := ()
  reject := ()
  blank := ()
  step := fun _ _ => ((), (), CookLevin.HeadMove.stay)

/-- Cook blocks for local 3SAT: the input is already a CNF formula. -/
def blocks : CookLevin.TableauConstraintBlocks threeSATDecisionProblem where
  initialRows := fun φ => φ.clauses
  certificateRows := fun _ => []
  transitionWindows := fun _ => []
  frameConditions := fun _ => []
  acceptingRows := fun _ => []

@[simp]
theorem blocks_cnf (φ : ThreeCNF) :
    blocks.cnf φ = φ.clauses := by
  simp [blocks, CookLevin.TableauConstraintBlocks.cnf]

/-- The already-3CNF tableau construction for the standard 3SAT verifier. -/
def tableauConstruction :
    CookLevin.CookTableauConstruction threeSATDecisionProblem threeSATVerifier.Cert where
  blocks := blocks
  accepts := fun φ a => φ.Satisfies a
  runToAssignment := by
    intro _ a _
    exact a
  runToAssignment_satisfies := by
    intro φ a h
    simpa [blocks_cnf] using h
  assignmentToRun := by
    intro φ a h
    exact ⟨a, by simpa [blocks_cnf] using h⟩

/-- The local 3SAT tableau map has linear encoded output size. -/
theorem tableauConstruction_polynomialSizeBound :
    PolynomialSizeBound
      (fun φ : threeSATDecisionProblem.Instance.Carrier =>
        threeSATDecisionProblem.Instance.inputSize φ)
      (fun ψ : ThreeCNF => threeSATDecisionProblem.Instance.inputSize ψ)
      tableauConstruction.cookTableauThreeCNF :=
  PolynomialSizeBound.intro_with 1 1 0 (by
    intro φ
    calc
      threeSATDecisionProblem.Instance.inputSize (tableauConstruction.cookTableauThreeCNF φ)
          = threeSATDecisionProblem.Instance.inputSize (CNF.splitToThreeCNF φ.clauses) := by
            simp [CookLevin.CookTableauConstruction.cookTableauThreeCNF,
              CookLevin.CookTableauConstruction.cookTableauCNF, tableauConstruction, blocks_cnf]
      _ = threeSATDecisionProblem.Instance.inputSize φ :=
            CNF.splitToThreeCNF_encodedLength_eq_self_of_isThree φ
      _ ≤ 1 * (threeSATDecisionProblem.Instance.inputSize φ) ^ 1 + 0 := by
            simp)

/-- Costed Cook tableau package for the local 3SAT verifier. -/
def costedTableauConstruction :
    CookLevin.CostedCookTableauConstruction threeSATDecisionProblem threeSATVerifier.Cert where
  tableau := tableauConstruction
  cookTableauThreeCNF_polynomialSizeBound := tableauConstruction_polynomialSizeBound

theorem accepts_iff_verify (φ : ThreeCNF) (a : Assignment) :
    tableauConstruction.accepts φ a ↔ threeSATVerifier.verify φ a = true := by
  classical
  by_cases h : φ.Satisfies a
  · simp [tableauConstruction, threeSATVerifier, h]
  · simp [tableauConstruction, threeSATVerifier, h]

end ThreeSATMachineVerifier

/-- Machine-backed witness for the standard local 3SAT NP verifier. -/
noncomputable def threeSATMachineBackedVerifier :
    MachineBackedNPVerifier threeSATDecisionProblem where
  machine := ThreeSATMachineVerifier.machine
  verifier := threeSATVerifier
  tableau := ThreeSATMachineVerifier.costedTableauConstruction
  accepts_iff_verify := ThreeSATMachineVerifier.accepts_iff_verify

/-- Local 3SAT belongs to the machine-backed encoded NP subclass. -/
theorem threeSAT_inMachineNP : InNPMachineEnc threeSATDecisionProblem :=
  InNPMachineEnc.intro threeSATMachineBackedVerifier

/-- Direct Cook-Levin reduction for one machine-backed verifier. -/
theorem cookLevin_reduction_of_machineVerifier {L : EncodedDecisionProblem}
    (V : MachineBackedNPVerifier L) :
    PolyReducibleM CostedPolyTimeModel L threeSATDecisionProblem :=
  ⟨V.toCookLevinVerifierReduction.toKarpReduction⟩

/-- Every machine-backed encoded NP language reduces to local 3SAT. -/
theorem cookLevin_reduction_of_inMachineNP {L : EncodedDecisionProblem}
    (hL : InNPMachineEnc L) :
    PolyReducibleM CostedPolyTimeModel L threeSATDecisionProblem := by
  induction hL with
  | of_machine_verifier V =>
      exact cookLevin_reduction_of_machineVerifier V
  | reduction_closure hAB _ ih =>
      exact PolyReducibleM.trans hAB ih

/-- Every locally verified encoded NP language reduces to local 3SAT. -/
theorem localCookLevin_reduction_of_inNP {L : EncodedDecisionProblem}
    (hL : InNPEnc CostedPolyTimeModel L) :
    PolyReducibleM CostedPolyTimeModel L threeSATDecisionProblem := by
  induction hL with
  | of_local_verifier V =>
      exact ⟨V.toKarpReduction⟩
  | reduction_closure hAB _ ih =>
      exact PolyReducibleM.trans hAB ih

/--
Local 3SAT is NP-complete for the locally verified encoded NP class.  This is
the P14e boundary discharge: direct `InNPEnc` leaves already include the
syntax-level Cook-Levin map used in the induction above.
-/
theorem localCookLevinTheorem :
    NPCompleteEnc CostedPolyTimeModel threeSATDecisionProblem := by
  constructor
  · exact threeSAT_inNP
  · intro L hL
    exact localCookLevin_reduction_of_inNP hL

/--
Local 3SAT is complete for the machine-backed encoded NP subclass.  This is the
P14b/P14c local theorem; the broader `InNPEnc` theorem still requires a
compatibility theorem showing that arbitrary existing verifiers are
machine-backed.
-/
theorem threeSAT_complete_for_machineNP :
    MachineNPCompleteEnc threeSATDecisionProblem := by
  constructor
  · exact threeSAT_inNP
  · intro L hL
    exact cookLevin_reduction_of_inMachineNP hL

/-- Local 3SAT is complete for the machine-backed NP complexity-class wrapper. -/
theorem threeSAT_completeFor_machineNP :
    MachineCompleteFor threeSATDecisionProblem := by
  constructor
  · exact threeSAT_inMachineNP
  · intro L hL
    exact cookLevin_reduction_of_inMachineNP hL

/--
Bundled local Cook-Levin theorem: every explicit costed NP verifier has a
syntactic, costed Karp reduction to local 3SAT.
-/
structure CookLevinTheorem where
  reduceVerifier :
    {L : EncodedDecisionProblem} →
      (V : NPVerifier CostedPolyTimeModel L) → CookLevinVerifierReduction V

/-- Any language in the inductively generated encoded NP class reduces to local 3SAT. -/
theorem cookLevin_reduction_of_inNP (H : CookLevinTheorem)
    {L : EncodedDecisionProblem} (hL : InNPEnc CostedPolyTimeModel L) :
    PolyReducibleM CostedPolyTimeModel L threeSATDecisionProblem := by
  induction hL with
  | of_local_verifier V =>
      exact ⟨(H.reduceVerifier V.verifier).toKarpReduction⟩
  | reduction_closure hAB _hB ih =>
      exact PolyReducibleM.trans hAB ih

/-- Local 3SAT NP-completeness from a supplied Cook-Levin theorem. -/
theorem threeSAT_npCompleteEnc_ofCookLevin (H : CookLevinTheorem) :
    NPCompleteEnc CostedPolyTimeModel threeSATDecisionProblem := by
  constructor
  · exact threeSAT_inNP
  · intro L hL
    exact cookLevin_reduction_of_inNP H hL

/--
An explicit compatibility package for turning legacy opaque verifiers into
machine-backed verifiers.  The repository does not manufacture this from a
`CostedPolyTimeMap`: callers must supply a real machine/tableau witness.
-/
structure CookLevinCompatibility where
  toMachineBacked :
    {L : EncodedDecisionProblem} →
      (V : NPVerifier CostedPolyTimeModel L) → MachineBackedNPVerifier L
  toMachineBacked_verifier :
    {L : EncodedDecisionProblem} →
      (V : NPVerifier CostedPolyTimeModel L) → (toMachineBacked V).toNPVerifier = V

namespace CookLevinCompatibility

/-- A compatibility package embeds ordinary encoded NP into machine-backed NP. -/
theorem inNPEnc_to_inNPMachineEnc (H : CookLevinCompatibility)
    {L : EncodedDecisionProblem} :
    InNPEnc CostedPolyTimeModel L → InNPMachineEnc L := by
  intro hL
  induction hL with
  | of_local_verifier V =>
      exact InNPMachineEnc.intro (H.toMachineBacked V.verifier)
  | reduction_closure hAB _ ih =>
      exact InNPMachineEnc.of_reduction hAB ih

/-- A compatibility package instantiates the full Cook-Levin theorem surface. -/
def toCookLevinTheorem (H : CookLevinCompatibility) : CookLevinTheorem where
  reduceVerifier := fun V => by
    simpa [H.toMachineBacked_verifier V] using
      (H.toMachineBacked V).toCookLevinVerifierReduction

/-- Full local 3SAT NP-completeness from an explicit compatibility package. -/
theorem threeSAT_npCompleteEnc (H : CookLevinCompatibility) :
    NPCompleteEnc CostedPolyTimeModel threeSATDecisionProblem :=
  threeSAT_npCompleteEnc_ofCookLevin H.toCookLevinTheorem

end CookLevinCompatibility

end SAT
end ComplexityReduction
