/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Nat.Pairing
import ComplexityReduction.Legacy.ComplexityReduction.Certificates.CostedMap
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CNFTo3SATCosted

/-!
Reusable Cook tableau syntax and proof-object layer.

Cook's construction encodes a bounded accepting computation by propositional
variables for time, tape position, symbol, head position, and state, then
conjoins initial-row, certificate, transition-window, frame, and accepting-row
constraints.  This module provides that standard tableau surface in a way that
is explicit enough for downstream machine-backed verifiers, without pretending
that an opaque Lean function `x -> cert -> Bool` can be inspected as a machine.
-/

namespace ComplexityReduction
namespace SAT

/-
Existing bundled 3CNF formulas are stable under the generic splitter.  This
supports the machine-backed 3SAT verifier specialization used by the P14d
compatibility audit.
-/
namespace CNF

theorem splitToThreeCNF_encodedLength_eq_self_of_isThree (φ : ThreeCNF) :
  threeSATDecisionProblem.Instance.inputSize (splitToThreeCNF φ.clauses) =
      threeSATDecisionProblem.Instance.inputSize φ := by
  simp [EncodedType.inputSize, threeSATDecisionProblem, threeSATSatLike, threeCNFEncodedType,
    splitToThreeCNF, splitTo3CNFList_eq_self_of_isThree _ φ.isThree]

end CNF

namespace CookLevin

/-- Head movement in a one-tape verifier machine. -/
inductive HeadMove where
  | left
  | stay
  | right
deriving DecidableEq, Repr

/-- Minimal deterministic verifier-machine syntax used by the tableau layer. -/
structure BoundedMachineSyntax where
  State : Type
  stateFinite : Fintype State
  stateDecidableEq : DecidableEq State
  Symbol : Type
  symbolFinite : Fintype Symbol
  symbolDecidableEq : DecidableEq Symbol
  start : State
  accept : State
  reject : State
  blank : Symbol
  step : State → Symbol → State × Symbol × HeadMove

namespace BoundedMachineSyntax

instance instStateFintype (M : BoundedMachineSyntax) : Fintype M.State :=
  M.stateFinite

instance instStateDecidableEq (M : BoundedMachineSyntax) : DecidableEq M.State :=
  M.stateDecidableEq

instance instSymbolFintype (M : BoundedMachineSyntax) : Fintype M.Symbol :=
  M.symbolFinite

instance instSymbolDecidableEq (M : BoundedMachineSyntax) : DecidableEq M.Symbol :=
  M.symbolDecidableEq

/-- A bounded-time configuration view. The tape is still indexed by natural cells. -/
structure Configuration (M : BoundedMachineSyntax) where
  state : M.State
  head : Nat
  tape : Nat → M.Symbol

/-- One deterministic machine step between configurations. -/
def Step (M : BoundedMachineSyntax) (c d : Configuration M) : Prop :=
  let next := M.step c.state (c.tape c.head)
  d.state = next.1 ∧ d.tape c.head = next.2.1

/-- Accepting configurations are exactly those whose state is the accept state. -/
def IsAccepting (M : BoundedMachineSyntax) (c : Configuration M) : Prop :=
  c.state = M.accept

end BoundedMachineSyntax

/-- Tableau variable families used by the Cook construction. -/
inductive TableauVarKind where
  | symbol
  | head
  | state
  | accept
  | aux
deriving DecidableEq, Repr

namespace TableauVarKind

/-- Stable numeric tag for a tableau variable family. -/
def tag : TableauVarKind → Nat
  | symbol => 0
  | head => 1
  | state => 2
  | accept => 3
  | aux => 4

theorem tag_injective : Function.Injective tag := by
  intro a b h
  cases a <;> cases b <;> simp [tag] at h ⊢

end TableauVarKind

/-- Coordinate in the time-by-cell Cook tableau grid. -/
structure TableauCoord where
  time : Nat
  cell : Nat
deriving DecidableEq, Repr

namespace TableauCoord

/-- Encode a tableau coordinate into the local SAT variable namespace. -/
def encode (p : TableauCoord) : Nat :=
  Nat.pair p.time p.cell

theorem encode_injective : Function.Injective encode := by
  intro a b h
  cases a
  cases b
  simp [encode, Nat.pair_eq_pair] at h
  simp [h.1, h.2]

end TableauCoord

/-- A stable SAT variable number for one tableau atom. -/
def tableauVar (kind : TableauVarKind) (time cell payload : Nat) : Nat :=
  Nat.pair kind.tag (Nat.pair time (Nat.pair cell payload))

/-- Positive tableau atom. -/
def tableauAtom (kind : TableauVarKind) (time cell payload : Nat) : Literal :=
  { var := tableauVar kind time cell payload, neg := false }

/-- Negative tableau atom. -/
def negTableauAtom (kind : TableauVarKind) (time cell payload : Nat) : Literal :=
  { var := tableauVar kind time cell payload, neg := true }

/-- A CNF block requiring at least one of the listed literals. -/
def atLeastOneCNF (xs : List Literal) : CNF :=
  [xs]

/-- Pairwise clauses requiring a fixed literal not to co-occur with later literals. -/
def atMostOneWithCNF (x : Literal) : List Literal → CNF
  | [] => []
  | y :: ys => [Clause.negate x, Clause.negate y] :: atMostOneWithCNF x ys

/-- A quadratic pairwise CNF block requiring at most one listed literal. -/
def atMostOneCNF : List Literal → CNF
  | [] => []
  | x :: xs => atMostOneWithCNF x xs ++ atMostOneCNF xs

/-- A standard exactly-one CNF block. Long at-least-one clauses are split later. -/
def exactlyOneCNF (xs : List Literal) : CNF :=
  atLeastOneCNF xs ++ atMostOneCNF xs

theorem atLeastOneCNF_satisfies (xs : List Literal) (a : Assignment) :
    CNF.Satisfies (atLeastOneCNF xs) a ↔ ∃ l ∈ xs, l.eval a = true := by
  simp [atLeastOneCNF, CNF.Satisfies, Clause.Satisfies]

/-- The five reusable constraint blocks in Cook's tableau construction. -/
structure TableauConstraintBlocks (L : EncodedDecisionProblem) where
  initialRows : L.Instance.Carrier → CNF
  certificateRows : L.Instance.Carrier → CNF
  transitionWindows : L.Instance.Carrier → CNF
  frameConditions : L.Instance.Carrier → CNF
  acceptingRows : L.Instance.Carrier → CNF

namespace TableauConstraintBlocks

/-- Conjoin all Cook tableau constraint blocks for one input. -/
def cnf {L : EncodedDecisionProblem} (B : TableauConstraintBlocks L)
    (x : L.Instance.Carrier) : CNF :=
  B.initialRows x ++ B.certificateRows x ++ B.transitionWindows x ++
    B.frameConditions x ++ B.acceptingRows x

theorem cnf_satisfies_iff {L : EncodedDecisionProblem} (B : TableauConstraintBlocks L)
    (x : L.Instance.Carrier) (a : Assignment) :
    CNF.Satisfies (B.cnf x) a ↔
      CNF.Satisfies (B.initialRows x) a ∧
      CNF.Satisfies (B.certificateRows x) a ∧
      CNF.Satisfies (B.transitionWindows x) a ∧
      CNF.Satisfies (B.frameConditions x) a ∧
      CNF.Satisfies (B.acceptingRows x) a := by
  simp [cnf, CNF.satisfies_append]

end TableauConstraintBlocks

/--
A Cook tableau construction for a verifier with certificate type `Cert`.

The fields separate the syntactic CNF blocks from the semantic run
interpretation.  The two proof fields are the usual Cook-Levin directions:
an accepting run extends to a satisfying assignment, and any satisfying
assignment projects back to an accepting run and certificate.
-/
structure CookTableauConstruction (L : EncodedDecisionProblem) (Cert : EncodedType) where
  blocks : TableauConstraintBlocks L
  accepts : L.Instance.Carrier → Cert.Carrier → Prop
  runToAssignment : ∀ {x : L.Instance.Carrier} {c : Cert.Carrier}, accepts x c → Assignment
  runToAssignment_satisfies :
    ∀ {x : L.Instance.Carrier} {c : Cert.Carrier} (h : accepts x c),
      CNF.Satisfies (blocks.cnf x) (runToAssignment h)
  assignmentToRun :
    ∀ {x : L.Instance.Carrier} {a : Assignment},
      CNF.Satisfies (blocks.cnf x) a → ∃ c : Cert.Carrier, accepts x c

namespace CookTableauConstruction

/-- The unsplit Cook tableau CNF. -/
def cookTableauCNF {L : EncodedDecisionProblem} {Cert : EncodedType}
    (T : CookTableauConstruction L Cert) (x : L.Instance.Carrier) : CNF :=
  T.blocks.cnf x

theorem cookTableauCNF_satisfiable_iff_accepts {L : EncodedDecisionProblem}
    {Cert : EncodedType} (T : CookTableauConstruction L Cert) (x : L.Instance.Carrier) :
    CNF.Satisfiable (T.cookTableauCNF x) ↔ ∃ c : Cert.Carrier, T.accepts x c := by
  constructor
  · rintro ⟨a, ha⟩
    exact T.assignmentToRun ha
  · rintro ⟨c, hc⟩
    exact ⟨T.runToAssignment hc, T.runToAssignment_satisfies hc⟩

/-- The standard 3CNF obtained by applying the reusable CNF splitter. -/
def cookTableauThreeCNF {L : EncodedDecisionProblem} {Cert : EncodedType}
    (T : CookTableauConstruction L Cert) (x : L.Instance.Carrier) : ThreeCNF :=
  CNF.splitToThreeCNF (T.cookTableauCNF x)

/-- Semantic correctness of the split Cook tableau 3CNF. -/
theorem cookTableauThreeCNF_satisfiable_iff_accepts {L : EncodedDecisionProblem}
    {Cert : EncodedType} (T : CookTableauConstruction L Cert) (x : L.Instance.Carrier) :
    (T.cookTableauThreeCNF x).Satisfiable ↔ ∃ c : Cert.Carrier, T.accepts x c := by
  rw [cookTableauThreeCNF, CNF.splitToThreeCNF_satisfiable_iff,
    cookTableauCNF_satisfiable_iff_accepts]

end CookTableauConstruction

/-- A Cook tableau construction with a polynomial encoded-size certificate. -/
structure CostedCookTableauConstruction (L : EncodedDecisionProblem) (Cert : EncodedType) where
  tableau : CookTableauConstruction L Cert
  cookTableauThreeCNF_polynomialSizeBound :
    PolynomialSizeBound
      (fun x : L.Instance.Carrier => L.Instance.inputSize x)
      (fun φ : ThreeCNF => threeSATDecisionProblem.Instance.inputSize φ)
      tableau.cookTableauThreeCNF

namespace CostedCookTableauConstruction

/-- The Cook tableau map is a costed polynomial-time map once its size bound is supplied. -/
theorem cookTableauThreeCNF_polytime {L : EncodedDecisionProblem} {Cert : EncodedType}
    (T : CostedCookTableauConstruction L Cert) :
    CostedPolyTimeModel.IsPolyTimeMap
      (X := L.Instance) (Y := threeSATDecisionProblem.Instance)
      T.tableau.cookTableauThreeCNF := by
  exact CostedPolyTimeMap.of_costed
    (CostedMap.of_encodedPolynomialSizeBound T.cookTableauThreeCNF_polynomialSizeBound)

end CostedCookTableauConstruction

end CookLevin
end SAT
end ComplexityReduction
