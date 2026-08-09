import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ZeroOneIP.StructuredTM.Rows

namespace ComplexityReduction
namespace Karp21
namespace ZeroOneIP

def clausePrefixStepInputEncodedType : EncodedType :=
  EncodedType.prod clausePrefixStateEncodedType literalStructuredEncodedType

abbrev ClausePrefixStepInput := ClausePrefixState × SAT.Literal

theorem natEqConst_tm_polytime
    (X : EncodedType) {f : X.Carrier → Nat}
    (hf : TMPolyTimeMap X EncodedType.nat f) (k : Nat) :
    TMPolyTimeMap X EncodedType.bool (fun x => decide (f x = k)) := by
  have hConst : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => k) :=
    TMPolyTimeMap.const X EncodedType.nat k
  have hPair :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun x : X.Carrier => (f x, k)) :=
    TMPolyTimeMap.prod_mk hf hConst
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

end ZeroOneIP
end Karp21
end ComplexityReduction
