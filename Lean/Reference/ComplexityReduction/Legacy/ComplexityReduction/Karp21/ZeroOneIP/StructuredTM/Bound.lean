import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ZeroOneIP.StructuredTM.Prefix

namespace ComplexityReduction
namespace Karp21
namespace ZeroOneIP

def boolPairEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool EncodedType.bool

def boolTripleEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool boolPairEncodedType

def prefixBoundOneFromNeg (b : Bool) : Int :=
  if b then 0 else -1

def prefixBoundTwoFromNegs (p : Bool × Bool) : Int :=
  match p with
  | (false, false) => -1
  | (true, false) => 0
  | (false, true) => 0
  | (true, true) => 1

def prefixBoundThreeFromNegs (p : Bool × (Bool × Bool)) : Int :=
  match p with
  | (false, (false, false)) => -1
  | (true, (false, false)) => 0
  | (false, (true, false)) => 0
  | (false, (false, true)) => 0
  | (true, (true, false)) => 1
  | (true, (false, true)) => 1
  | (false, (true, true)) => 1
  | (true, (true, true)) => 2

def prefixBound (q : ClausePrefixState) : Int :=
  if q.1 = (0 : Nat) then
    -1
  else if q.1 = (1 : Nat) then
    prefixBoundOneFromNeg q.2.1.neg
  else if q.1 = (2 : Nat) then
    prefixBoundTwoFromNegs (q.2.1.neg, q.2.2.1.neg)
  else
    prefixBoundThreeFromNegs (q.2.1.neg, (q.2.2.1.neg, q.2.2.2.neg))

theorem boolToInt_tm_polytime (f : Bool → Int) :
    TMPolyTimeMap EncodedType.bool EncodedType.int f := by
  have hPair :
      TMPolyTimeMap EncodedType.bool
        (EncodedType.prod EncodedType.bool (EncodedType.raw Unit))
        (fun b : Bool => (b, ())) := by
    simpa using
      TMPolyTimeMap.prod_id_const_emptyRight
        EncodedType.bool (EncodedType.raw Unit) () rfl
  have hFalse :
      TMPolyTimeMap (EncodedType.raw Unit) EncodedType.int
        (fun _ : Unit => f false) :=
    TMPolyTimeMap.const (EncodedType.raw Unit) EncodedType.int (f false)
  have hTrue :
      TMPolyTimeMap (EncodedType.raw Unit) EncodedType.int
        (fun _ : Unit => f true) :=
    TMPolyTimeMap.const (EncodedType.raw Unit) EncodedType.int (f true)
  have hBranch :=
    Clique.boolProduct_dispatch_tm_polytime (EncodedType.raw Unit) EncodedType.int
      (fFalse := fun _ : Unit => f false)
      (fTrue := fun _ : Unit => f true)
      hFalse hTrue
  have hComp := TMPolyTimeMap.comp hBranch hPair
  convert hComp using 1
  funext b
  cases b <;> rfl

theorem boolPairToInt_tm_polytime (f : Bool × Bool → Int) :
    TMPolyTimeMap boolPairEncodedType EncodedType.int f := by
  have hFalse :
      TMPolyTimeMap EncodedType.bool EncodedType.int
        (fun b : Bool => f (false, b)) :=
    boolToInt_tm_polytime (fun b : Bool => f (false, b))
  have hTrue :
      TMPolyTimeMap EncodedType.bool EncodedType.int
        (fun b : Bool => f (true, b)) :=
    boolToInt_tm_polytime (fun b : Bool => f (true, b))
  have hBranch :=
    Clique.boolProduct_dispatch_tm_polytime EncodedType.bool EncodedType.int
      (fFalse := fun b : Bool => f (false, b))
      (fTrue := fun b : Bool => f (true, b))
      hFalse hTrue
  convert hBranch using 1
  funext p
  rcases p with ⟨a, b⟩
  cases a <;> rfl

theorem boolTripleToInt_tm_polytime (f : Bool × (Bool × Bool) → Int) :
    TMPolyTimeMap boolTripleEncodedType EncodedType.int f := by
  have hFalse :
      TMPolyTimeMap boolPairEncodedType EncodedType.int
        (fun p : Bool × Bool => f (false, p)) :=
    boolPairToInt_tm_polytime (fun p : Bool × Bool => f (false, p))
  have hTrue :
      TMPolyTimeMap boolPairEncodedType EncodedType.int
        (fun p : Bool × Bool => f (true, p)) :=
    boolPairToInt_tm_polytime (fun p : Bool × Bool => f (true, p))
  have hBranch :=
    Clique.boolProduct_dispatch_tm_polytime boolPairEncodedType EncodedType.int
      (fFalse := fun p : Bool × Bool => f (false, p))
      (fTrue := fun p : Bool × Bool => f (true, p))
      hFalse hTrue
  convert hBranch using 1
  funext p
  rcases p with ⟨a, b⟩
  cases a <;> rfl

theorem prefixBoundOneFromNeg_tm_polytime :
    TMPolyTimeMap EncodedType.bool EncodedType.int prefixBoundOneFromNeg :=
  boolToInt_tm_polytime prefixBoundOneFromNeg

theorem prefixBoundTwoFromNegs_tm_polytime :
    TMPolyTimeMap boolPairEncodedType EncodedType.int prefixBoundTwoFromNegs :=
  boolPairToInt_tm_polytime prefixBoundTwoFromNegs

theorem prefixBoundThreeFromNegs_tm_polytime :
    TMPolyTimeMap boolTripleEncodedType EncodedType.int prefixBoundThreeFromNegs :=
  boolTripleToInt_tm_polytime prefixBoundThreeFromNegs

theorem prefixBound_tm_polytime :
    TMPolyTimeMap clausePrefixStateEncodedType EncodedType.int prefixBound := by
  let X := clausePrefixStateEncodedType
  have hCount : TMPolyTimeMap X EncodedType.nat (fun q : ClausePrefixState => q.1) := by
    simpa [X, clausePrefixStateEncodedType, ClausePrefixState] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod literalStructuredEncodedType
          (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType))
  have hLitTail :
      TMPolyTimeMap X
        (EncodedType.prod literalStructuredEncodedType
          (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType))
        (fun q : ClausePrefixState => q.2) := by
    simpa [X, clausePrefixStateEncodedType, ClausePrefixState] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod literalStructuredEncodedType
          (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType))
  have hLit0 : TMPolyTimeMap X literalStructuredEncodedType
      (fun q : ClausePrefixState => q.2.1) := by
    have hFst :=
      TMPolyTimeMap.fst literalStructuredEncodedType
        (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hLitTail
    simpa [Function.comp, X] using hComp
  have hLit12 :
      TMPolyTimeMap X
        (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
        (fun q : ClausePrefixState => q.2.2) := by
    have hSnd :=
      TMPolyTimeMap.snd literalStructuredEncodedType
        (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hLitTail
    simpa [Function.comp, X] using hComp
  have hLit1 : TMPolyTimeMap X literalStructuredEncodedType
      (fun q : ClausePrefixState => q.2.2.1) := by
    have hFst := TMPolyTimeMap.fst literalStructuredEncodedType literalStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hLit12
    simpa [Function.comp, X] using hComp
  have hLit2 : TMPolyTimeMap X literalStructuredEncodedType
      (fun q : ClausePrefixState => q.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd literalStructuredEncodedType literalStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hLit12
    simpa [Function.comp, X] using hComp
  have hNeg0 : TMPolyTimeMap X EncodedType.bool
      (fun q : ClausePrefixState => q.2.1.neg) := by
    have hComp := TMPolyTimeMap.comp Clique.literal_neg_tm_polytime hLit0
    simpa [Function.comp, X] using hComp
  have hNeg1 : TMPolyTimeMap X EncodedType.bool
      (fun q : ClausePrefixState => q.2.2.1.neg) := by
    have hComp := TMPolyTimeMap.comp Clique.literal_neg_tm_polytime hLit1
    simpa [Function.comp, X] using hComp
  have hNeg2 : TMPolyTimeMap X EncodedType.bool
      (fun q : ClausePrefixState => q.2.2.2.neg) := by
    have hComp := TMPolyTimeMap.comp Clique.literal_neg_tm_polytime hLit2
    simpa [Function.comp, X] using hComp
  have hOne : TMPolyTimeMap X EncodedType.int
      (fun q : ClausePrefixState => prefixBoundOneFromNeg q.2.1.neg) := by
    have hComp := TMPolyTimeMap.comp prefixBoundOneFromNeg_tm_polytime hNeg0
    simpa [Function.comp, X] using hComp
  have hNegPair :
      TMPolyTimeMap X boolPairEncodedType
        (fun q : ClausePrefixState => (q.2.1.neg, q.2.2.1.neg)) :=
    TMPolyTimeMap.prod_mk hNeg0 hNeg1
  have hTwo : TMPolyTimeMap X EncodedType.int
      (fun q : ClausePrefixState =>
        prefixBoundTwoFromNegs (q.2.1.neg, q.2.2.1.neg)) := by
    have hComp := TMPolyTimeMap.comp prefixBoundTwoFromNegs_tm_polytime hNegPair
    simpa [Function.comp, X] using hComp
  have hNegTail :
      TMPolyTimeMap X boolPairEncodedType
        (fun q : ClausePrefixState => (q.2.2.1.neg, q.2.2.2.neg)) :=
    TMPolyTimeMap.prod_mk hNeg1 hNeg2
  have hNegTriple :
      TMPolyTimeMap X boolTripleEncodedType
        (fun q : ClausePrefixState => (q.2.1.neg, (q.2.2.1.neg, q.2.2.2.neg))) :=
    TMPolyTimeMap.prod_mk hNeg0 hNegTail
  have hThree : TMPolyTimeMap X EncodedType.int
      (fun q : ClausePrefixState =>
        prefixBoundThreeFromNegs (q.2.1.neg, (q.2.2.1.neg, q.2.2.2.neg))) := by
    have hComp := TMPolyTimeMap.comp prefixBoundThreeFromNegs_tm_polytime hNegTriple
    simpa [Function.comp, X] using hComp
  have hZero : TMPolyTimeMap X EncodedType.int (fun _ : ClausePrefixState => (-1 : Int)) :=
    TMPolyTimeMap.const X EncodedType.int (-1 : Int)
  have hEq2 : TMPolyTimeMap X EncodedType.bool
      (fun q : ClausePrefixState => decide (q.1 = (2 : Nat))) :=
    natEqConst_tm_polytime X hCount 2
  have hBranchInput2 :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun q : ClausePrefixState => (decide (q.1 = (2 : Nat)), q)) :=
    TMPolyTimeMap.prod_mk hEq2 (TMPolyTimeMap.id X)
  have hBranch2 :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) EncodedType.int
        (fun p : Bool × ClausePrefixState =>
          match p.1 with
          | true => prefixBoundTwoFromNegs (p.2.2.1.neg, p.2.2.2.1.neg)
          | false =>
              prefixBoundThreeFromNegs
                (p.2.2.1.neg, (p.2.2.2.1.neg, p.2.2.2.2.neg))) :=
    Clique.boolProduct_dispatch_tm_polytime X EncodedType.int
      (fFalse := fun q : ClausePrefixState =>
        prefixBoundThreeFromNegs (q.2.1.neg, (q.2.2.1.neg, q.2.2.2.neg)))
      (fTrue := fun q : ClausePrefixState =>
        prefixBoundTwoFromNegs (q.2.1.neg, q.2.2.1.neg))
      hThree hTwo
  have hTail2 : TMPolyTimeMap X EncodedType.int
      (fun q : ClausePrefixState =>
        if q.1 = (2 : Nat) then
          prefixBoundTwoFromNegs (q.2.1.neg, q.2.2.1.neg)
        else
          prefixBoundThreeFromNegs (q.2.1.neg, (q.2.2.1.neg, q.2.2.2.neg))) := by
    have hComp := TMPolyTimeMap.comp hBranch2 hBranchInput2
    convert hComp using 1
    funext q
    by_cases h : q.1 = (2 : Nat) <;> simp [Function.comp, h]
  have hEq1 : TMPolyTimeMap X EncodedType.bool
      (fun q : ClausePrefixState => decide (q.1 = (1 : Nat))) :=
    natEqConst_tm_polytime X hCount 1
  have hBranchInput1 :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun q : ClausePrefixState => (decide (q.1 = (1 : Nat)), q)) :=
    TMPolyTimeMap.prod_mk hEq1 (TMPolyTimeMap.id X)
  have hBranch1 :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) EncodedType.int
        (fun p : Bool × ClausePrefixState =>
          match p.1 with
          | true => prefixBoundOneFromNeg p.2.2.1.neg
          | false =>
              if p.2.1 = (2 : Nat) then
                prefixBoundTwoFromNegs (p.2.2.1.neg, p.2.2.2.1.neg)
              else
                prefixBoundThreeFromNegs
                  (p.2.2.1.neg, (p.2.2.2.1.neg, p.2.2.2.2.neg))) :=
    Clique.boolProduct_dispatch_tm_polytime X EncodedType.int
      (fFalse := fun q : ClausePrefixState =>
        if q.1 = (2 : Nat) then
          prefixBoundTwoFromNegs (q.2.1.neg, q.2.2.1.neg)
        else
          prefixBoundThreeFromNegs (q.2.1.neg, (q.2.2.1.neg, q.2.2.2.neg)))
      (fTrue := fun q : ClausePrefixState => prefixBoundOneFromNeg q.2.1.neg)
      hTail2 hOne
  have hTail1 : TMPolyTimeMap X EncodedType.int
      (fun q : ClausePrefixState =>
        if q.1 = (1 : Nat) then
          prefixBoundOneFromNeg q.2.1.neg
        else if q.1 = (2 : Nat) then
          prefixBoundTwoFromNegs (q.2.1.neg, q.2.2.1.neg)
        else
          prefixBoundThreeFromNegs (q.2.1.neg, (q.2.2.1.neg, q.2.2.2.neg))) := by
    have hComp := TMPolyTimeMap.comp hBranch1 hBranchInput1
    convert hComp using 1
    funext q
    by_cases h : q.1 = (1 : Nat) <;> simp [Function.comp, h]
  have hEq0 : TMPolyTimeMap X EncodedType.bool
      (fun q : ClausePrefixState => decide (q.1 = (0 : Nat))) :=
    natEqConst_tm_polytime X hCount 0
  have hBranchInput0 :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun q : ClausePrefixState => (decide (q.1 = (0 : Nat)), q)) :=
    TMPolyTimeMap.prod_mk hEq0 (TMPolyTimeMap.id X)
  have hBranch0 :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) EncodedType.int
        (fun p : Bool × ClausePrefixState =>
          match p.1 with
          | true => (-1 : Int)
          | false =>
              if p.2.1 = (1 : Nat) then
                prefixBoundOneFromNeg p.2.2.1.neg
              else if p.2.1 = (2 : Nat) then
                prefixBoundTwoFromNegs (p.2.2.1.neg, p.2.2.2.1.neg)
              else
                prefixBoundThreeFromNegs
                  (p.2.2.1.neg, (p.2.2.2.1.neg, p.2.2.2.2.neg))) :=
    Clique.boolProduct_dispatch_tm_polytime X EncodedType.int
      (fFalse := fun q : ClausePrefixState =>
        if q.1 = (1 : Nat) then
          prefixBoundOneFromNeg q.2.1.neg
        else if q.1 = (2 : Nat) then
          prefixBoundTwoFromNegs (q.2.1.neg, q.2.2.1.neg)
        else
          prefixBoundThreeFromNegs (q.2.1.neg, (q.2.2.1.neg, q.2.2.2.neg)))
      (fTrue := fun _ : ClausePrefixState => (-1 : Int))
      hTail1 hZero
  have hOut := TMPolyTimeMap.comp hBranch0 hBranchInput0
  convert hOut using 1
  funext q
  by_cases h0 : q.1 = (0 : Nat)
  · simp [prefixBound, Function.comp, h0]
  · simp [prefixBound, Function.comp, h0]
    rfl

theorem prefixBound_clausePrefix_eq_clauseBound {c : SAT.Clause}
    (hlen : c.length ≤ 3) :
    prefixBound (clausePrefixFromClause c) = clauseBound c := by
  cases c with
  | nil =>
      simp [prefixBound, clausePrefixFromClause_nil, clausePrefixInit, clauseBound,
        clauseNegWeight]
  | cons l0 rest =>
      cases rest with
      | nil =>
          cases l0 with
          | mk var0 neg0 =>
              cases neg0 <;>
                norm_num [prefixBound, clausePrefixFromClause_singleton,
                  prefixBoundOneFromNeg, clauseBound, clauseNegWeight, literalNegWeight]
      | cons l1 rest =>
          cases rest with
          | nil =>
              cases l0 with
              | mk var0 neg0 =>
                  cases l1 with
                  | mk var1 neg1 =>
                      cases neg0 <;> cases neg1 <;>
                        norm_num [prefixBound, clausePrefixFromClause_pair,
                          prefixBoundTwoFromNegs, clauseBound, clauseNegWeight,
                          literalNegWeight]
          | cons l2 rest =>
              cases rest with
              | nil =>
                  cases l0 with
                  | mk var0 neg0 =>
                      cases l1 with
                      | mk var1 neg1 =>
                          cases l2 with
                          | mk var2 neg2 =>
                              cases neg0 <;> cases neg1 <;> cases neg2 <;>
                                norm_num [prefixBound, clausePrefixFromClause_three_or_more,
                                  prefixBoundThreeFromNegs, clauseBound, clauseNegWeight,
                                  literalNegWeight]
              | cons _ _ =>
                  simp at hlen
                  omega

end ZeroOneIP
end Karp21
end ComplexityReduction
