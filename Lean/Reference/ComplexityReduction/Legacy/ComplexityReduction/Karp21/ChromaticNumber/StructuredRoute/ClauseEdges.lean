import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ChromaticNumber.StructuredRoute

namespace ComplexityReduction
namespace Karp21
namespace ChromaticNumber

open ComplexityReduction.Combinatorics.Graph

/-!
Checked clause-edge runners for the P16c Chromatic Number route.

The runner first folds over a clause to retain its first three literals and a
capped length counter.  This avoids an ad-hoc recursive parser and keeps the
later `clauseEdgesFor` branch finite: empty clauses emit the self-loop, and
nonempty clauses use the already checked nine-edge gadget emitter.
-/

def defaultLiteralForClauseEdges : SAT.Literal :=
  ⟨0, false⟩

def clausePrefixStateEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod literalStructuredEncodedType
      (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType))

abbrev ClausePrefixState := Nat × (SAT.Literal × (SAT.Literal × SAT.Literal))

def clausePrefixStepInputEncodedType : EncodedType :=
  EncodedType.prod clausePrefixStateEncodedType literalStructuredEncodedType

abbrev ClausePrefixStepInput := ClausePrefixState × SAT.Literal

def clausePrefixInit : ClausePrefixState :=
  ((0 : Nat),
    (defaultLiteralForClauseEdges,
      (defaultLiteralForClauseEdges, defaultLiteralForClauseEdges)))

def clausePrefixStep
    (p : ClausePrefixState × SAT.Literal) :
    ClausePrefixState :=
  if p.1.1 = (0 : Nat) then
    ((1 : Nat), (p.2, (p.1.2.2.1, p.1.2.2.2)))
  else if p.1.1 = (1 : Nat) then
    ((2 : Nat), (p.1.2.1, (p.2, p.1.2.2.2)))
  else if p.1.1 = (2 : Nat) then
    ((3 : Nat), (p.1.2.1, (p.1.2.2.1, p.2)))
  else
    p.1

def clausePrefixFromClause (c : SAT.Clause) :
    ClausePrefixState :=
  c.foldl (fun acc lit => clausePrefixStep (acc, lit)) clausePrefixInit

theorem natEqConst_tm_polytime
    (X : EncodedType) {f : X.Carrier → Nat}
    (hf : TMPolyTimeMap X EncodedType.nat f) (k : Nat) :
    TMPolyTimeMap X EncodedType.bool (fun x => decide (f x = k)) := by
  have hConst : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => k) :=
    TMPolyTimeMap.const X EncodedType.nat k
  have hPair :
      TMPolyTimeMap X natAddInputEncodedType (fun x : X.Carrier => (f x, k)) := by
    simpa [natAddInputEncodedType] using TMPolyTimeMap.prod_mk hf hConst
  have hEq := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hPair
  simpa [Function.comp] using hEq

theorem clausePrefixState_mk_tm_polytime
    {X : EncodedType} {count : X.Carrier → Nat}
    {l₀ l₁ l₂ : X.Carrier → SAT.Literal}
    (hCount : TMPolyTimeMap X EncodedType.nat count)
    (h₀ : TMPolyTimeMap X literalStructuredEncodedType l₀)
    (h₁ : TMPolyTimeMap X literalStructuredEncodedType l₁)
    (h₂ : TMPolyTimeMap X literalStructuredEncodedType l₂) :
    TMPolyTimeMap X clausePrefixStateEncodedType
      (fun x => (count x, (l₀ x, (l₁ x, l₂ x)))) := by
  have h₁₂ :
      TMPolyTimeMap X
        (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
        (fun x => (l₁ x, l₂ x)) :=
    TMPolyTimeMap.prod_mk h₁ h₂
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod literalStructuredEncodedType
          (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType))
        (fun x => (l₀ x, (l₁ x, l₂ x))) :=
    TMPolyTimeMap.prod_mk h₀ h₁₂
  simpa [clausePrefixStateEncodedType] using TMPolyTimeMap.prod_mk hCount hTail

theorem clausePrefixStep_tm_polytime :
    TMPolyTimeMap
      clausePrefixStepInputEncodedType
      clausePrefixStateEncodedType
      clausePrefixStep := by
  let X := clausePrefixStepInputEncodedType
  have hAcc : TMPolyTimeMap X clausePrefixStateEncodedType
      (fun p : ClausePrefixStepInput => p.1) := by
    simpa [X, clausePrefixStepInputEncodedType, ClausePrefixStepInput] using
      TMPolyTimeMap.fst clausePrefixStateEncodedType literalStructuredEncodedType
  have hLit : TMPolyTimeMap X literalStructuredEncodedType
      (fun p : ClausePrefixStepInput => p.2) := by
    simpa [X, clausePrefixStepInputEncodedType, ClausePrefixStepInput] using
      TMPolyTimeMap.snd clausePrefixStateEncodedType literalStructuredEncodedType
  have hCount : TMPolyTimeMap X EncodedType.nat
      (fun p : ClausePrefixStepInput => p.1.1) := by
    have hFst :=
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod literalStructuredEncodedType
          (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType))
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, clausePrefixStateEncodedType, X, clausePrefixStepInputEncodedType,
      ClausePrefixStepInput] using hComp
  have hLitTail :
      TMPolyTimeMap X
        (EncodedType.prod literalStructuredEncodedType
          (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType))
        (fun p : ClausePrefixStepInput => p.1.2) := by
    have hSnd :=
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod literalStructuredEncodedType
          (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType))
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, clausePrefixStateEncodedType, X, clausePrefixStepInputEncodedType,
      ClausePrefixStepInput] using hComp
  have hL₀ : TMPolyTimeMap X literalStructuredEncodedType
      (fun p : ClausePrefixStepInput => p.1.2.1) := by
    have hFst :=
      TMPolyTimeMap.fst literalStructuredEncodedType
        (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hLitTail
    simpa [Function.comp, X, clausePrefixStepInputEncodedType, ClausePrefixStepInput] using hComp
  have hL₁₂ :
      TMPolyTimeMap X
        (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
        (fun p : ClausePrefixStepInput => p.1.2.2) := by
    have hSnd :=
      TMPolyTimeMap.snd literalStructuredEncodedType
        (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hLitTail
    simpa [Function.comp, X, clausePrefixStepInputEncodedType, ClausePrefixStepInput] using hComp
  have hL₁ : TMPolyTimeMap X literalStructuredEncodedType
      (fun p : ClausePrefixStepInput => p.1.2.2.1) := by
    have hFst := TMPolyTimeMap.fst literalStructuredEncodedType literalStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hL₁₂
    simpa [Function.comp, X, clausePrefixStepInputEncodedType, ClausePrefixStepInput] using hComp
  have hL₂ : TMPolyTimeMap X literalStructuredEncodedType
      (fun p : ClausePrefixStepInput => p.1.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd literalStructuredEncodedType literalStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hL₁₂
    simpa [Function.comp, X, clausePrefixStepInputEncodedType, ClausePrefixStepInput] using hComp
  have hOne : TMPolyTimeMap X EncodedType.nat
      (fun _ : ClausePrefixStepInput => (1 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (1 : Nat)
  have hTwo : TMPolyTimeMap X EncodedType.nat
      (fun _ : ClausePrefixStepInput => (2 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (2 : Nat)
  have hThree : TMPolyTimeMap X EncodedType.nat
      (fun _ : ClausePrefixStepInput => (3 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (3 : Nat)
  have hSetFirst :
      TMPolyTimeMap X clausePrefixStateEncodedType
        (fun p : ClausePrefixStepInput =>
          ((1 : Nat), (p.2, (p.1.2.2.1, p.1.2.2.2)))) :=
    clausePrefixState_mk_tm_polytime hOne hLit hL₁ hL₂
  have hSetSecond :
      TMPolyTimeMap X clausePrefixStateEncodedType
        (fun p : ClausePrefixStepInput =>
          ((2 : Nat), (p.1.2.1, (p.2, p.1.2.2.2)))) :=
    clausePrefixState_mk_tm_polytime hTwo hL₀ hLit hL₂
  have hSetThird :
      TMPolyTimeMap X clausePrefixStateEncodedType
        (fun p : ClausePrefixStepInput =>
          ((3 : Nat), (p.1.2.1, (p.1.2.2.1, p.2)))) :=
    clausePrefixState_mk_tm_polytime hThree hL₀ hL₁ hLit
  have hKeep :
      TMPolyTimeMap X clausePrefixStateEncodedType
        (fun p : ClausePrefixStepInput => p.1) :=
    hAcc
  have hEq₂ :
      TMPolyTimeMap X EncodedType.bool
        (fun p : ClausePrefixStepInput => decide (p.1.1 = (2 : Nat))) :=
    natEqConst_tm_polytime X hCount (2 : Nat)
  have hBranchInput₂ :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : ClausePrefixStepInput => (decide (p.1.1 = (2 : Nat)), p)) :=
    TMPolyTimeMap.prod_mk hEq₂ (TMPolyTimeMap.id X)
  have hBranch₂ :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) clausePrefixStateEncodedType
        (fun p : Bool × ClausePrefixStepInput =>
          match p.1 with
          | true => ((3 : Nat), (p.2.1.2.1, (p.2.1.2.2.1, p.2.2)))
          | false => p.2.1) :=
    Clique.boolProduct_dispatch_tm_polytime X clausePrefixStateEncodedType
      (fFalse := fun p : ClausePrefixStepInput => p.1)
      (fTrue := fun p : ClausePrefixStepInput =>
        ((3 : Nat), (p.1.2.1, (p.1.2.2.1, p.2))))
      hKeep hSetThird
  have hTail₂ :
      TMPolyTimeMap X clausePrefixStateEncodedType
        (fun p : ClausePrefixStepInput =>
          if p.1.1 = (2 : Nat) then
            ((3 : Nat), (p.1.2.1, (p.1.2.2.1, p.2)))
          else
            p.1) := by
    have hComp := TMPolyTimeMap.comp hBranch₂ hBranchInput₂
    convert hComp using 1
    funext p
    by_cases h : p.1.1 = (2 : Nat) <;> simp [Function.comp, h]
  have hEq₁ :
      TMPolyTimeMap X EncodedType.bool
        (fun p : ClausePrefixStepInput => decide (p.1.1 = (1 : Nat))) :=
    natEqConst_tm_polytime X hCount (1 : Nat)
  have hBranchInput₁ :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : ClausePrefixStepInput => (decide (p.1.1 = (1 : Nat)), p)) :=
    TMPolyTimeMap.prod_mk hEq₁ (TMPolyTimeMap.id X)
  have hBranch₁ :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) clausePrefixStateEncodedType
        (fun p : Bool × ClausePrefixStepInput =>
          match p.1 with
          | true => ((2 : Nat), (p.2.1.2.1, (p.2.2, p.2.1.2.2.2)))
          | false =>
              if p.2.1.1 = (2 : Nat) then
                ((3 : Nat), (p.2.1.2.1, (p.2.1.2.2.1, p.2.2)))
              else
                p.2.1) :=
    Clique.boolProduct_dispatch_tm_polytime X clausePrefixStateEncodedType
      (fFalse := fun p : ClausePrefixStepInput =>
        if p.1.1 = (2 : Nat) then
          ((3 : Nat), (p.1.2.1, (p.1.2.2.1, p.2)))
        else
          p.1)
      (fTrue := fun p : ClausePrefixStepInput =>
        ((2 : Nat), (p.1.2.1, (p.2, p.1.2.2.2))))
      hTail₂ hSetSecond
  have hTail₁ :
      TMPolyTimeMap X clausePrefixStateEncodedType
        (fun p : ClausePrefixStepInput =>
          if p.1.1 = (1 : Nat) then
            ((2 : Nat), (p.1.2.1, (p.2, p.1.2.2.2)))
          else if p.1.1 = (2 : Nat) then
            ((3 : Nat), (p.1.2.1, (p.1.2.2.1, p.2)))
          else
            p.1) := by
    have hComp := TMPolyTimeMap.comp hBranch₁ hBranchInput₁
    convert hComp using 1
    funext p
    by_cases h₁ : p.1.1 = (1 : Nat) <;> by_cases h₂ : p.1.1 = (2 : Nat) <;>
      simp [Function.comp, h₁, h₂]
  have hEq₀ :
      TMPolyTimeMap X EncodedType.bool
        (fun p : ClausePrefixStepInput => decide (p.1.1 = (0 : Nat))) :=
    natEqConst_tm_polytime X hCount (0 : Nat)
  have hBranchInput₀ :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : ClausePrefixStepInput => (decide (p.1.1 = (0 : Nat)), p)) :=
    TMPolyTimeMap.prod_mk hEq₀ (TMPolyTimeMap.id X)
  have hBranch₀ :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) clausePrefixStateEncodedType
        (fun p : Bool × ClausePrefixStepInput =>
          match p.1 with
          | true => ((1 : Nat), (p.2.2, (p.2.1.2.2.1, p.2.1.2.2.2)))
          | false =>
              if p.2.1.1 = (1 : Nat) then
                ((2 : Nat), (p.2.1.2.1, (p.2.2, p.2.1.2.2.2)))
              else if p.2.1.1 = (2 : Nat) then
                ((3 : Nat), (p.2.1.2.1, (p.2.1.2.2.1, p.2.2)))
              else
                p.2.1) :=
    Clique.boolProduct_dispatch_tm_polytime X clausePrefixStateEncodedType
      (fFalse := fun p : ClausePrefixStepInput =>
        if p.1.1 = (1 : Nat) then
          ((2 : Nat), (p.1.2.1, (p.2, p.1.2.2.2)))
        else if p.1.1 = (2 : Nat) then
          ((3 : Nat), (p.1.2.1, (p.1.2.2.1, p.2)))
        else
          p.1)
      (fTrue := fun p : ClausePrefixStepInput =>
        ((1 : Nat), (p.2, (p.1.2.2.1, p.1.2.2.2))))
      hTail₁ hSetFirst
  have hOut := TMPolyTimeMap.comp hBranch₀ hBranchInput₀
  convert hOut using 1
  funext p
  by_cases h₀ : p.1.1 = (0 : Nat) <;> by_cases h₁ : p.1.1 = (1 : Nat) <;>
    by_cases h₂ : p.1.1 = (2 : Nat) <;>
      simp [clausePrefixStep, Function.comp, h₀, h₁, h₂] <;> rfl

theorem clausePrefixStep_growth
    (source : SAT.Clause) (acc : ClausePrefixState) (lit : SAT.Literal)
    (hlit : literalStructuredEncodedType.inputSize lit ≤
      clauseStructuredEncodedType.inputSize source) :
    clausePrefixStateEncodedType.inputSize (clausePrefixStep (acc, lit)) ≤
      clausePrefixStateEncodedType.inputSize acc +
        (Polynomial.C 10 * Polynomial.X + Polynomial.C 20).eval
          (clauseStructuredEncodedType.inputSize source) := by
  rcases acc with ⟨count, l₀, l₁, l₂⟩
  by_cases h₀ : count = 0
  · simp [clausePrefixStep, h₀, clausePrefixStateEncodedType,
      Polynomial.eval_add, Polynomial.eval_mul] at hlit ⊢
    omega
  · by_cases h₁ : count = 1
    · simp [clausePrefixStep, h₁, clausePrefixStateEncodedType,
        Polynomial.eval_add, Polynomial.eval_mul] at hlit ⊢
      omega
    · by_cases h₂ : count = 2
      · simp [clausePrefixStep, h₂, clausePrefixStateEncodedType,
          Polynomial.eval_add, Polynomial.eval_mul] at hlit ⊢
        omega
      · simp [clausePrefixStep, h₀, h₁, h₂, Polynomial.eval_add, Polynomial.eval_mul]

theorem clausePrefixFromClause_tm_polytime :
    TMPolyTimeMap
      clauseStructuredEncodedType
      clausePrefixStateEncodedType
      clausePrefixFromClause := by
  rcases clausePrefixStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      literalStructuredEncodedType clausePrefixStateEncodedType
      clausePrefixStep clausePrefixInit hStep
      (Polynomial.C 100) (Polynomial.C 10 * Polynomial.X + Polynomial.C 20) ?_ ?_
  · intro source
    simpa using
      (show clausePrefixStateEncodedType.inputSize clausePrefixInit ≤ (100 : Nat) by
        native_decide)
  · intro source acc lit hlit
    exact clausePrefixStep_growth source acc lit hlit

theorem clausePrefixFold_keep_after_three
    (l₀ l₁ l₂ : SAT.Literal) (rest : SAT.Clause) :
    rest.foldl (fun acc lit => clausePrefixStep (acc, lit))
        ((3 : Nat), (l₀, (l₁, l₂))) =
      ((3 : Nat), (l₀, (l₁, l₂))) := by
  induction rest with
  | nil =>
      rfl
  | cons lit rest ih =>
      change rest.foldl (fun acc lit => clausePrefixStep (acc, lit))
          (clausePrefixStep (((3 : Nat), (l₀, (l₁, l₂))), lit)) =
        ((3 : Nat), (l₀, (l₁, l₂)))
      simpa [clausePrefixStep] using ih

theorem clausePrefixFromClause_nil :
    clausePrefixFromClause [] = clausePrefixInit := by
  rfl

theorem clausePrefixFromClause_singleton (l₀ : SAT.Literal) :
    clausePrefixFromClause [l₀] =
      ((1 : Nat), (l₀, (defaultLiteralForClauseEdges, defaultLiteralForClauseEdges))) := by
  simp [clausePrefixFromClause, clausePrefixStep, clausePrefixInit]

theorem clausePrefixFromClause_pair (l₀ l₁ : SAT.Literal) :
    clausePrefixFromClause [l₀, l₁] =
      ((2 : Nat), (l₀, (l₁, defaultLiteralForClauseEdges))) := by
  simp [clausePrefixFromClause, clausePrefixStep, clausePrefixInit]

theorem clausePrefixFromClause_three_or_more
    (l₀ l₁ l₂ : SAT.Literal) (rest : SAT.Clause) :
    clausePrefixFromClause (l₀ :: l₁ :: l₂ :: rest) =
      ((3 : Nat), (l₀, (l₁, l₂))) := by
  simpa [clausePrefixFromClause, clausePrefixStep, clausePrefixInit] using
    clausePrefixFold_keep_after_three l₀ l₁ l₂ rest

def clauseEdgesForPrefixInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat clausePrefixStateEncodedType)

abbrev ClauseEdgesForPrefixInput := Nat × (Nat × ClausePrefixState)

def clauseGadgetInputOfPrefix
    (p : ClauseEdgesForPrefixInput) :
    clauseGadgetInputEncodedType.Carrier :=
  let n := p.1
  let j := p.2.1
  let l₀ := p.2.2.2.1
  let l₁ := p.2.2.2.2.1
  let l₂ := p.2.2.2.2.2
  if p.2.2.1 = (1 : Nat) then
    (n, (j, (l₀, (l₀, l₀))))
  else if p.2.2.1 = (2 : Nat) then
    (n, (j, (l₀, (l₁, l₁))))
  else
    (n, (j, (l₀, (l₁, l₂))))

def clauseLoopEdgeList : List (Nat × Nat) :=
  [(baseVertex, baseVertex)]

def clauseEdgesForFromPrefix
    (p : ClauseEdgesForPrefixInput) :
    List (Nat × Nat) :=
  if p.2.2.1 = (0 : Nat) then
    clauseLoopEdgeList
  else
    clauseGadgetEdgesFromInput (clauseGadgetInputOfPrefix p)

theorem clauseEdgesForFromPrefix_eq_clauseEdgesFor
    (n j : Nat) (c : SAT.Clause) :
    clauseEdgesForFromPrefix (n, (j, clausePrefixFromClause c)) =
      clauseEdgesFor n j c := by
  cases c with
  | nil =>
      simp [clauseEdgesForFromPrefix, clausePrefixFromClause_nil, clauseLoopEdgeList,
        clauseEdgesFor, paddedClause, clausePrefixInit]
  | cons l₀ rest =>
      cases rest with
      | nil =>
          simp [clauseEdgesForFromPrefix, clausePrefixFromClause_singleton,
            clauseGadgetInputOfPrefix, clauseGadgetEdgesFromInput, clauseEdgesFor,
            paddedClause]
      | cons l₁ rest =>
          cases rest with
          | nil =>
              simp [clauseEdgesForFromPrefix, clausePrefixFromClause_pair,
                clauseGadgetInputOfPrefix, clauseGadgetEdgesFromInput, clauseEdgesFor,
                paddedClause]
          | cons l₂ rest =>
              simp [clauseEdgesForFromPrefix, clausePrefixFromClause_three_or_more,
                clauseGadgetInputOfPrefix, clauseGadgetEdgesFromInput, clauseEdgesFor,
                paddedClause]

theorem clauseGadgetInput_mk_tm_polytime
    {X : EncodedType} {n j : X.Carrier → Nat}
    {l₀ l₁ l₂ : X.Carrier → SAT.Literal}
    (hN : TMPolyTimeMap X EncodedType.nat n)
    (hJ : TMPolyTimeMap X EncodedType.nat j)
    (h₀ : TMPolyTimeMap X literalStructuredEncodedType l₀)
    (h₁ : TMPolyTimeMap X literalStructuredEncodedType l₁)
    (h₂ : TMPolyTimeMap X literalStructuredEncodedType l₂) :
    TMPolyTimeMap X clauseGadgetInputEncodedType
      (fun x => (n x, (j x, (l₀ x, (l₁ x, l₂ x))))) := by
  have h₁₂ :
      TMPolyTimeMap X
        (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
        (fun x => (l₁ x, l₂ x)) :=
    TMPolyTimeMap.prod_mk h₁ h₂
  have hLits :
      TMPolyTimeMap X
        (EncodedType.prod literalStructuredEncodedType
          (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType))
        (fun x => (l₀ x, (l₁ x, l₂ x))) :=
    TMPolyTimeMap.prod_mk h₀ h₁₂
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod literalStructuredEncodedType
            (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)))
        (fun x => (j x, (l₀ x, (l₁ x, l₂ x)))) :=
    TMPolyTimeMap.prod_mk hJ hLits
  simpa [clauseGadgetInputEncodedType] using TMPolyTimeMap.prod_mk hN hTail

theorem clauseGadgetInputOfPrefix_tm_polytime :
    TMPolyTimeMap
      clauseEdgesForPrefixInputEncodedType
      clauseGadgetInputEncodedType
      clauseGadgetInputOfPrefix := by
  let X := clauseEdgesForPrefixInputEncodedType
  let Tail := EncodedType.prod EncodedType.nat clausePrefixStateEncodedType
  let LitTail :=
    EncodedType.prod literalStructuredEncodedType
      (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
  let LitPair := EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType
  have hN : TMPolyTimeMap X EncodedType.nat
      (fun p : ClauseEdgesForPrefixInput => p.1) := by
    simpa [X, clauseEdgesForPrefixInputEncodedType, Tail, ClauseEdgesForPrefixInput] using
      TMPolyTimeMap.fst EncodedType.nat Tail
  have hTail : TMPolyTimeMap X Tail
      (fun p : ClauseEdgesForPrefixInput => p.2) := by
    simpa [X, clauseEdgesForPrefixInputEncodedType, Tail, ClauseEdgesForPrefixInput] using
      TMPolyTimeMap.snd EncodedType.nat Tail
  have hJ : TMPolyTimeMap X EncodedType.nat
      (fun p : ClauseEdgesForPrefixInput => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat clausePrefixStateEncodedType
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X, Tail, ClauseEdgesForPrefixInput] using hComp
  have hState : TMPolyTimeMap X clausePrefixStateEncodedType
      (fun p : ClauseEdgesForPrefixInput => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat clausePrefixStateEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X, Tail, ClauseEdgesForPrefixInput] using hComp
  have hCount : TMPolyTimeMap X EncodedType.nat
      (fun p : ClauseEdgesForPrefixInput => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat LitTail
    have hComp := TMPolyTimeMap.comp hFst hState
    simpa [Function.comp, X, LitTail, clausePrefixStateEncodedType,
      ClauseEdgesForPrefixInput] using hComp
  have hLitTail : TMPolyTimeMap X LitTail
      (fun p : ClauseEdgesForPrefixInput => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat LitTail
    have hComp := TMPolyTimeMap.comp hSnd hState
    simpa [Function.comp, X, LitTail, clausePrefixStateEncodedType,
      ClauseEdgesForPrefixInput] using hComp
  have hL₀ : TMPolyTimeMap X literalStructuredEncodedType
      (fun p : ClauseEdgesForPrefixInput => p.2.2.2.1) := by
    have hFst := TMPolyTimeMap.fst literalStructuredEncodedType LitPair
    have hComp := TMPolyTimeMap.comp hFst hLitTail
    simpa [Function.comp, X, LitTail, LitPair, ClauseEdgesForPrefixInput] using hComp
  have hL₁₂ : TMPolyTimeMap X LitPair
      (fun p : ClauseEdgesForPrefixInput => p.2.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd literalStructuredEncodedType LitPair
    have hComp := TMPolyTimeMap.comp hSnd hLitTail
    simpa [Function.comp, X, LitTail, LitPair, ClauseEdgesForPrefixInput] using hComp
  have hL₁ : TMPolyTimeMap X literalStructuredEncodedType
      (fun p : ClauseEdgesForPrefixInput => p.2.2.2.2.1) := by
    have hFst := TMPolyTimeMap.fst literalStructuredEncodedType literalStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hL₁₂
    simpa [Function.comp, X, LitPair, ClauseEdgesForPrefixInput] using hComp
  have hL₂ : TMPolyTimeMap X literalStructuredEncodedType
      (fun p : ClauseEdgesForPrefixInput => p.2.2.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd literalStructuredEncodedType literalStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hL₁₂
    simpa [Function.comp, X, LitPair, ClauseEdgesForPrefixInput] using hComp
  have hDefault :
      TMPolyTimeMap X clauseGadgetInputEncodedType
        (fun p : ClauseEdgesForPrefixInput =>
          (p.1, (p.2.1, (p.2.2.2.1, (p.2.2.2.2.1, p.2.2.2.2.2))))) :=
    clauseGadgetInput_mk_tm_polytime hN hJ hL₀ hL₁ hL₂
  have hSetOne :
      TMPolyTimeMap X clauseGadgetInputEncodedType
        (fun p : ClauseEdgesForPrefixInput =>
          (p.1, (p.2.1, (p.2.2.2.1, (p.2.2.2.1, p.2.2.2.1))))) :=
    clauseGadgetInput_mk_tm_polytime hN hJ hL₀ hL₀ hL₀
  have hSetTwo :
      TMPolyTimeMap X clauseGadgetInputEncodedType
        (fun p : ClauseEdgesForPrefixInput =>
          (p.1, (p.2.1, (p.2.2.2.1, (p.2.2.2.2.1, p.2.2.2.2.1))))) :=
    clauseGadgetInput_mk_tm_polytime hN hJ hL₀ hL₁ hL₁
  have hEq₂ :
      TMPolyTimeMap X EncodedType.bool
        (fun p : ClauseEdgesForPrefixInput => decide (p.2.2.1 = (2 : Nat))) :=
    natEqConst_tm_polytime X hCount (2 : Nat)
  have hBranchInput₂ :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : ClauseEdgesForPrefixInput => (decide (p.2.2.1 = (2 : Nat)), p)) :=
    TMPolyTimeMap.prod_mk hEq₂ (TMPolyTimeMap.id X)
  have hBranch₂ :=
    Clique.boolProduct_dispatch_tm_polytime X clauseGadgetInputEncodedType
      (fFalse := fun p : ClauseEdgesForPrefixInput =>
        (p.1, (p.2.1, (p.2.2.2.1, (p.2.2.2.2.1, p.2.2.2.2.2)))))
      (fTrue := fun p : ClauseEdgesForPrefixInput =>
        (p.1, (p.2.1, (p.2.2.2.1, (p.2.2.2.2.1, p.2.2.2.2.1)))))
      hDefault hSetTwo
  have hTail₂ :
      TMPolyTimeMap X clauseGadgetInputEncodedType
        (fun p : ClauseEdgesForPrefixInput =>
          if p.2.2.1 = (2 : Nat) then
            (p.1, (p.2.1, (p.2.2.2.1, (p.2.2.2.2.1, p.2.2.2.2.1))))
          else
            (p.1, (p.2.1, (p.2.2.2.1, (p.2.2.2.2.1, p.2.2.2.2.2))))) := by
    have hComp := TMPolyTimeMap.comp hBranch₂ hBranchInput₂
    convert hComp using 1
    funext p
    by_cases h : p.2.2.1 = (2 : Nat) <;> simp [Function.comp, h]
  have hEq₁ :
      TMPolyTimeMap X EncodedType.bool
        (fun p : ClauseEdgesForPrefixInput => decide (p.2.2.1 = (1 : Nat))) :=
    natEqConst_tm_polytime X hCount (1 : Nat)
  have hBranchInput₁ :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : ClauseEdgesForPrefixInput => (decide (p.2.2.1 = (1 : Nat)), p)) :=
    TMPolyTimeMap.prod_mk hEq₁ (TMPolyTimeMap.id X)
  have hBranch₁ :=
    Clique.boolProduct_dispatch_tm_polytime X clauseGadgetInputEncodedType
      (fFalse := fun p : ClauseEdgesForPrefixInput =>
        if p.2.2.1 = (2 : Nat) then
          (p.1, (p.2.1, (p.2.2.2.1, (p.2.2.2.2.1, p.2.2.2.2.1))))
        else
          (p.1, (p.2.1, (p.2.2.2.1, (p.2.2.2.2.1, p.2.2.2.2.2)))))
      (fTrue := fun p : ClauseEdgesForPrefixInput =>
        (p.1, (p.2.1, (p.2.2.2.1, (p.2.2.2.1, p.2.2.2.1)))))
      hTail₂ hSetOne
  have hOut := TMPolyTimeMap.comp hBranch₁ hBranchInput₁
  convert hOut using 1
  funext p
  by_cases h₁ : p.2.2.1 = (1 : Nat) <;> by_cases h₂ : p.2.2.1 = (2 : Nat) <;>
    simp [clauseGadgetInputOfPrefix, Function.comp, h₁, h₂]

theorem clauseEdgesForFromPrefix_tm_polytime :
    TMPolyTimeMap
      clauseEdgesForPrefixInputEncodedType
      edgeListStructuredEncodedType
      clauseEdgesForFromPrefix := by
  let X := clauseEdgesForPrefixInputEncodedType
  let Tail := EncodedType.prod EncodedType.nat clausePrefixStateEncodedType
  let LitTail :=
    EncodedType.prod literalStructuredEncodedType
      (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
  have hTail : TMPolyTimeMap X Tail
      (fun p : ClauseEdgesForPrefixInput => p.2) := by
    simpa [X, clauseEdgesForPrefixInputEncodedType, Tail, ClauseEdgesForPrefixInput] using
      TMPolyTimeMap.snd EncodedType.nat Tail
  have hState : TMPolyTimeMap X clausePrefixStateEncodedType
      (fun p : ClauseEdgesForPrefixInput => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat clausePrefixStateEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X, Tail, ClauseEdgesForPrefixInput] using hComp
  have hCount : TMPolyTimeMap X EncodedType.nat
      (fun p : ClauseEdgesForPrefixInput => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat LitTail
    have hComp := TMPolyTimeMap.comp hFst hState
    simpa [Function.comp, X, LitTail, clausePrefixStateEncodedType,
      ClauseEdgesForPrefixInput] using hComp
  have hEq₀ :
      TMPolyTimeMap X EncodedType.bool
        (fun p : ClauseEdgesForPrefixInput => decide (p.2.2.1 = (0 : Nat))) :=
    natEqConst_tm_polytime X hCount (0 : Nat)
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : ClauseEdgesForPrefixInput => (decide (p.2.2.1 = (0 : Nat)), p)) :=
    TMPolyTimeMap.prod_mk hEq₀ (TMPolyTimeMap.id X)
  have hLoop :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun _ : ClauseEdgesForPrefixInput => clauseLoopEdgeList) :=
    TMPolyTimeMap.const X edgeListStructuredEncodedType clauseLoopEdgeList
  have hGadget :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : ClauseEdgesForPrefixInput =>
          clauseGadgetEdgesFromInput (clauseGadgetInputOfPrefix p)) := by
    have hComp :=
      TMPolyTimeMap.comp clauseGadgetEdgesFromInput_tm_polytime
        clauseGadgetInputOfPrefix_tm_polytime
    simpa [Function.comp, X] using hComp
  have hBranch :=
    Clique.boolProduct_dispatch_tm_polytime X edgeListStructuredEncodedType
      (fFalse := fun p : ClauseEdgesForPrefixInput =>
        clauseGadgetEdgesFromInput (clauseGadgetInputOfPrefix p))
      (fTrue := fun _ : ClauseEdgesForPrefixInput => clauseLoopEdgeList)
      hGadget hLoop
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext p
  by_cases h : p.2.2.1 = (0 : Nat) <;>
    simp [clauseEdgesForFromPrefix, Function.comp, h]

def clauseEdgesForInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat clauseStructuredEncodedType)

abbrev ClauseEdgesForInput := Nat × (Nat × SAT.Clause)

def clauseEdgesForFromInput (p : ClauseEdgesForInput) :
    List (Nat × Nat) :=
  clauseEdgesFor p.1 p.2.1 p.2.2

def clauseEdgesForPrefixInputOfInput
    (p : ClauseEdgesForInput) :
    ClauseEdgesForPrefixInput :=
  (p.1, (p.2.1, clausePrefixFromClause p.2.2))

theorem clauseEdgesForPrefixInputOfInput_tm_polytime :
    TMPolyTimeMap
      clauseEdgesForInputEncodedType
      clauseEdgesForPrefixInputEncodedType
      clauseEdgesForPrefixInputOfInput := by
  let X := clauseEdgesForInputEncodedType
  let Tail := EncodedType.prod EncodedType.nat clauseStructuredEncodedType
  have hN : TMPolyTimeMap X EncodedType.nat
      (fun p : ClauseEdgesForInput => p.1) := by
    simpa [X, clauseEdgesForInputEncodedType, Tail, ClauseEdgesForInput] using
      TMPolyTimeMap.fst EncodedType.nat Tail
  have hTail : TMPolyTimeMap X Tail
      (fun p : ClauseEdgesForInput => p.2) := by
    simpa [X, clauseEdgesForInputEncodedType, Tail, ClauseEdgesForInput] using
      TMPolyTimeMap.snd EncodedType.nat Tail
  have hJ : TMPolyTimeMap X EncodedType.nat
      (fun p : ClauseEdgesForInput => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat clauseStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X, Tail, ClauseEdgesForInput] using hComp
  have hClause : TMPolyTimeMap X clauseStructuredEncodedType
      (fun p : ClauseEdgesForInput => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat clauseStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X, Tail, ClauseEdgesForInput] using hComp
  have hPrefix : TMPolyTimeMap X clausePrefixStateEncodedType
      (fun p : ClauseEdgesForInput => clausePrefixFromClause p.2.2) := by
    have hComp := TMPolyTimeMap.comp clausePrefixFromClause_tm_polytime hClause
    simpa [Function.comp, X] using hComp
  have hJPrefix :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat clausePrefixStateEncodedType)
        (fun p : ClauseEdgesForInput => (p.2.1, clausePrefixFromClause p.2.2)) :=
    TMPolyTimeMap.prod_mk hJ hPrefix
  have hOut :
      TMPolyTimeMap X clauseEdgesForPrefixInputEncodedType
        (fun p : ClauseEdgesForInput =>
          (p.1, (p.2.1, clausePrefixFromClause p.2.2))) :=
    TMPolyTimeMap.prod_mk hN hJPrefix
  simpa [clauseEdgesForPrefixInputOfInput, X, clauseEdgesForPrefixInputEncodedType,
    clauseEdgesForInputEncodedType, ClauseEdgesForInput, ClauseEdgesForPrefixInput] using hOut

theorem clauseEdgesFor_tm_polytime :
    TMPolyTimeMap
      clauseEdgesForInputEncodedType
      edgeListStructuredEncodedType
      clauseEdgesForFromInput := by
  have hComp :=
    TMPolyTimeMap.comp clauseEdgesForFromPrefix_tm_polytime
      clauseEdgesForPrefixInputOfInput_tm_polytime
  convert hComp using 1
  funext p
  simp [Function.comp, clauseEdgesForFromInput, clauseEdgesForPrefixInputOfInput,
    clauseEdgesForFromPrefix_eq_clauseEdgesFor]

theorem clauseEdgesForFromInput_structured_inputSize_le
    (p : ClauseEdgesForInput) :
    edgeListStructuredEncodedType.inputSize (clauseEdgesForFromInput p) ≤
      200 * clauseEdgesForInputEncodedType.inputSize p ^ 2 + 200 := by
  rcases p with ⟨n, j, c⟩
  cases c with
  | nil =>
      simp [clauseEdgesForFromInput, clauseEdgesFor, paddedClause,
        clauseEdgesForInputEncodedType, clauseStructuredEncodedType, edgeListStructuredEncodedType,
        edgeStructuredEncodedType, EncodedType.inputSize, EncodedType.list, EncodedType.prod,
        EncodedType.nat, baseVertex]
  | cons l₀ rest =>
      cases rest with
      | nil =>
          cases l₀ with
          | mk v₀ b₀ =>
              cases b₀ <;>
                simp [clauseEdgesForFromInput, clauseEdgesFor, paddedClause, clauseGadgetEdges,
                  literalVertex, posVertex, negVertex, clauseA0, clauseA1, clauseA2,
                  clauseA3, clauseBase, variableLimit, clauseEdgesForInputEncodedType,
                  clauseStructuredEncodedType, literalStructuredEncodedType,
                  literalTupleStructuredEncodedType, edgeListStructuredEncodedType,
                  edgeStructuredEncodedType, EncodedType.inputSize, EncodedType.list,
                  EncodedType.prod, EncodedType.nat, EncodedType.bool, trueVertex] <;>
                ring_nf <;> omega
      | cons l₁ rest =>
          cases rest with
          | nil =>
              cases l₀ with
              | mk v₀ b₀ =>
                  cases l₁ with
                  | mk v₁ b₁ =>
                      cases b₀ <;> cases b₁ <;>
                        simp [clauseEdgesForFromInput, clauseEdgesFor, paddedClause,
                          clauseGadgetEdges, literalVertex, posVertex, negVertex, clauseA0,
                          clauseA1, clauseA2, clauseA3, clauseBase, variableLimit,
                          clauseEdgesForInputEncodedType, clauseStructuredEncodedType,
                          literalStructuredEncodedType, literalTupleStructuredEncodedType,
                          edgeListStructuredEncodedType, edgeStructuredEncodedType,
                          EncodedType.inputSize, EncodedType.list, EncodedType.prod,
                          EncodedType.nat, EncodedType.bool, trueVertex] <;>
                        ring_nf <;> omega
          | cons l₂ tail =>
              cases l₀ with
              | mk v₀ b₀ =>
                  cases l₁ with
                  | mk v₁ b₁ =>
                      cases l₂ with
                      | mk v₂ b₂ =>
                          cases b₀ <;> cases b₁ <;> cases b₂ <;>
                            simp [clauseEdgesForFromInput, clauseEdgesFor, paddedClause,
                              clauseGadgetEdges, literalVertex, posVertex, negVertex,
                              clauseA0, clauseA1, clauseA2, clauseA3, clauseBase,
                              variableLimit, clauseEdgesForInputEncodedType,
                              clauseStructuredEncodedType, literalStructuredEncodedType,
                              literalTupleStructuredEncodedType, edgeListStructuredEncodedType,
                              edgeStructuredEncodedType, EncodedType.inputSize,
                              EncodedType.list, EncodedType.prod, EncodedType.nat,
                              EncodedType.bool, trueVertex] <;>
                            ring_nf <;> omega

theorem clauseEdgesFor_polynomialSizeBound :
    PolynomialSizeBound
      (fun p : ClauseEdgesForInput => clauseEdgesForInputEncodedType.inputSize p)
      (fun edges : edgeListStructuredEncodedType.Carrier =>
        edgeListStructuredEncodedType.inputSize edges)
      clauseEdgesForFromInput := by
  refine PolynomialSizeBound.intro_with 2 200 200 ?_
  intro p
  exact clauseEdgesForFromInput_structured_inputSize_le p

noncomputable def clauseEdgesForTMBackedMap :
    TMBackedCostedMap
      clauseEdgesForInputEncodedType
      edgeListStructuredEncodedType
      clauseEdgesForFromInput where
  costed := CostedMap.of_encodedPolynomialSizeBound clauseEdgesFor_polynomialSizeBound
  tm_polytime := clauseEdgesFor_tm_polytime

end ChromaticNumber
end Karp21
end ComplexityReduction
