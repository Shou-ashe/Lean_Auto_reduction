import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ZeroOneIP.StructuredTM.Bound

namespace ComplexityReduction
namespace Karp21
namespace ZeroOneIP

def bool4EncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool boolTripleEncodedType

def bool5EncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool bool4EncodedType

def bool6EncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool bool5EncodedType

abbrev Bool4 := Bool × (Bool × (Bool × Bool))
abbrev Bool5 := Bool × Bool4
abbrev Bool6 := Bool × Bool5

theorem bool4ToInt_tm_polytime (f : Bool4 → Int) :
    TMPolyTimeMap bool4EncodedType EncodedType.int f := by
  have hFalse :
      TMPolyTimeMap boolTripleEncodedType EncodedType.int
        (fun p : Bool × (Bool × Bool) => f (false, p)) :=
    boolTripleToInt_tm_polytime (fun p : Bool × (Bool × Bool) => f (false, p))
  have hTrue :
      TMPolyTimeMap boolTripleEncodedType EncodedType.int
        (fun p : Bool × (Bool × Bool) => f (true, p)) :=
    boolTripleToInt_tm_polytime (fun p : Bool × (Bool × Bool) => f (true, p))
  have hBranch :=
    Clique.boolProduct_dispatch_tm_polytime boolTripleEncodedType EncodedType.int
      (fFalse := fun p : Bool × (Bool × Bool) => f (false, p))
      (fTrue := fun p : Bool × (Bool × Bool) => f (true, p))
      hFalse hTrue
  convert hBranch using 1
  funext p
  rcases p with ⟨a, rest⟩
  cases a <;> rfl

theorem bool5ToInt_tm_polytime (f : Bool5 → Int) :
    TMPolyTimeMap bool5EncodedType EncodedType.int f := by
  have hFalse : TMPolyTimeMap bool4EncodedType EncodedType.int
      (fun p : Bool4 => f (false, p)) :=
    bool4ToInt_tm_polytime (fun p : Bool4 => f (false, p))
  have hTrue : TMPolyTimeMap bool4EncodedType EncodedType.int
      (fun p : Bool4 => f (true, p)) :=
    bool4ToInt_tm_polytime (fun p : Bool4 => f (true, p))
  have hBranch :=
    Clique.boolProduct_dispatch_tm_polytime bool4EncodedType EncodedType.int
      (fFalse := fun p : Bool4 => f (false, p))
      (fTrue := fun p : Bool4 => f (true, p))
      hFalse hTrue
  convert hBranch using 1
  funext p
  rcases p with ⟨a, rest⟩
  cases a <;> rfl

theorem bool6ToInt_tm_polytime (f : Bool6 → Int) :
    TMPolyTimeMap bool6EncodedType EncodedType.int f := by
  have hFalse : TMPolyTimeMap bool5EncodedType EncodedType.int
      (fun p : Bool5 => f (false, p)) :=
    bool5ToInt_tm_polytime (fun p : Bool5 => f (false, p))
  have hTrue : TMPolyTimeMap bool5EncodedType EncodedType.int
      (fun p : Bool5 => f (true, p)) :=
    bool5ToInt_tm_polytime (fun p : Bool5 => f (true, p))
  have hBranch :=
    Clique.boolProduct_dispatch_tm_polytime bool5EncodedType EncodedType.int
      (fFalse := fun p : Bool5 => f (false, p))
      (fTrue := fun p : Bool5 => f (true, p))
      hFalse hTrue
  convert hBranch using 1
  funext p
  rcases p with ⟨a, rest⟩
  cases a <;> rfl

def literalCoeffFromFlags (hit neg : Bool) : Int :=
  if hit then
    if neg then 1 else -1
  else
    0

def prefixCoeffTwoFromFlags (p : Bool4) : Int :=
  literalCoeffFromFlags p.1 p.2.1 +
    literalCoeffFromFlags p.2.2.1 p.2.2.2

def prefixCoeffThreeFromFlags (p : Bool6) : Int :=
  literalCoeffFromFlags p.1 p.2.1 +
    literalCoeffFromFlags p.2.2.1 p.2.2.2.1 +
      literalCoeffFromFlags p.2.2.2.2.1 p.2.2.2.2.2

theorem prefixCoeffTwoFromFlags_tm_polytime :
    TMPolyTimeMap bool4EncodedType EncodedType.int prefixCoeffTwoFromFlags :=
  bool4ToInt_tm_polytime prefixCoeffTwoFromFlags

theorem prefixCoeffThreeFromFlags_tm_polytime :
    TMPolyTimeMap bool6EncodedType EncodedType.int prefixCoeffThreeFromFlags :=
  bool6ToInt_tm_polytime prefixCoeffThreeFromFlags

def prefixCoeffInputEncodedType : EncodedType :=
  EncodedType.prod clausePrefixStateEncodedType EncodedType.nat

abbrev PrefixCoeffInput := ClausePrefixState × Nat

def prefixCoeffAtComputed (p : PrefixCoeffInput) : Int :=
  if p.1.1 = (0 : Nat) then
    0
  else if p.1.1 = (1 : Nat) then
    literalCoeffAt p.1.2.1 p.2
  else if p.1.1 = (2 : Nat) then
    prefixCoeffTwoFromFlags
      (decide (p.2 = p.1.2.1.var),
        (p.1.2.1.neg, (decide (p.2 = p.1.2.2.1.var), p.1.2.2.1.neg)))
  else
    prefixCoeffThreeFromFlags
      (decide (p.2 = p.1.2.1.var),
        (p.1.2.1.neg,
          (decide (p.2 = p.1.2.2.1.var),
            (p.1.2.2.1.neg,
              (decide (p.2 = p.1.2.2.2.var), p.1.2.2.2.neg)))))

theorem literalCoeffFromFlags_eq (l : SAT.Literal) (i : Nat) :
    literalCoeffFromFlags (decide (i = l.var)) l.neg = literalCoeffAt l i := by
  cases l with
  | mk var neg =>
      by_cases h : i = var <;> cases neg <;> simp [literalCoeffFromFlags, literalCoeffAt, h]

theorem prefixCoeffTwoFromFlags_eq (l0 l1 : SAT.Literal) (i : Nat) :
    prefixCoeffTwoFromFlags
        (decide (i = l0.var), (l0.neg, (decide (i = l1.var), l1.neg))) =
      literalCoeffAt l0 i + literalCoeffAt l1 i := by
  have h0 := literalCoeffFromFlags_eq l0 i
  have h1 := literalCoeffFromFlags_eq l1 i
  simp [prefixCoeffTwoFromFlags, h0, h1]

theorem prefixCoeffThreeFromFlags_eq (l0 l1 l2 : SAT.Literal) (i : Nat) :
    prefixCoeffThreeFromFlags
        (decide (i = l0.var),
          (l0.neg,
            (decide (i = l1.var),
              (l1.neg, (decide (i = l2.var), l2.neg))))) =
      literalCoeffAt l0 i + literalCoeffAt l1 i + literalCoeffAt l2 i := by
  have h0 := literalCoeffFromFlags_eq l0 i
  have h1 := literalCoeffFromFlags_eq l1 i
  have h2 := literalCoeffFromFlags_eq l2 i
  simp [prefixCoeffThreeFromFlags, h0, h1, h2, Int.add_assoc]

theorem prefixCoeffAtComputed_eq_prefixCoeffAt (p : PrefixCoeffInput) :
    prefixCoeffAtComputed p = prefixCoeffAt p.1 p.2 := by
  rcases p with ⟨⟨count, l0, l1, l2⟩, i⟩
  cases count with
  | zero =>
      simp [prefixCoeffAtComputed, prefixCoeffAt]
  | succ count =>
      cases count with
      | zero =>
          simp [prefixCoeffAtComputed, prefixCoeffAt]
      | succ count =>
          cases count with
          | zero =>
              simp [prefixCoeffAtComputed, prefixCoeffAt, prefixCoeffTwoFromFlags_eq]
          | succ count =>
              simp [prefixCoeffAtComputed, prefixCoeffAt, prefixCoeffThreeFromFlags_eq,
                Int.add_assoc]

theorem prefixCoeffAtComputed_tm_polytime :
    TMPolyTimeMap prefixCoeffInputEncodedType EncodedType.int prefixCoeffAtComputed := by
  let X := prefixCoeffInputEncodedType
  have hState : TMPolyTimeMap X clausePrefixStateEncodedType
      (fun p : PrefixCoeffInput => p.1) := by
    simpa [X, prefixCoeffInputEncodedType, PrefixCoeffInput] using
      TMPolyTimeMap.fst clausePrefixStateEncodedType EncodedType.nat
  have hIndex : TMPolyTimeMap X EncodedType.nat
      (fun p : PrefixCoeffInput => p.2) := by
    simpa [X, prefixCoeffInputEncodedType, PrefixCoeffInput] using
      TMPolyTimeMap.snd clausePrefixStateEncodedType EncodedType.nat
  have hCount : TMPolyTimeMap X EncodedType.nat
      (fun p : PrefixCoeffInput => p.1.1) := by
    have hFst :=
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod literalStructuredEncodedType
          (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType))
    have hComp := TMPolyTimeMap.comp hFst hState
    simpa [Function.comp, clausePrefixStateEncodedType, X, PrefixCoeffInput] using hComp
  have hLitTail :
      TMPolyTimeMap X
        (EncodedType.prod literalStructuredEncodedType
          (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType))
        (fun p : PrefixCoeffInput => p.1.2) := by
    have hSnd :=
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod literalStructuredEncodedType
          (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType))
    have hComp := TMPolyTimeMap.comp hSnd hState
    simpa [Function.comp, clausePrefixStateEncodedType, X, PrefixCoeffInput] using hComp
  have hLit0 : TMPolyTimeMap X literalStructuredEncodedType
      (fun p : PrefixCoeffInput => p.1.2.1) := by
    have hFst :=
      TMPolyTimeMap.fst literalStructuredEncodedType
        (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hLitTail
    simpa [Function.comp, X, PrefixCoeffInput] using hComp
  have hLit12 :
      TMPolyTimeMap X
        (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
        (fun p : PrefixCoeffInput => p.1.2.2) := by
    have hSnd :=
      TMPolyTimeMap.snd literalStructuredEncodedType
        (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hLitTail
    simpa [Function.comp, X, PrefixCoeffInput] using hComp
  have hLit1 : TMPolyTimeMap X literalStructuredEncodedType
      (fun p : PrefixCoeffInput => p.1.2.2.1) := by
    have hFst := TMPolyTimeMap.fst literalStructuredEncodedType literalStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hLit12
    simpa [Function.comp, X, PrefixCoeffInput] using hComp
  have hLit2 : TMPolyTimeMap X literalStructuredEncodedType
      (fun p : PrefixCoeffInput => p.1.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd literalStructuredEncodedType literalStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hLit12
    simpa [Function.comp, X, PrefixCoeffInput] using hComp
  have hVar0 : TMPolyTimeMap X EncodedType.nat
      (fun p : PrefixCoeffInput => p.1.2.1.var) := by
    have hComp := TMPolyTimeMap.comp Clique.literal_var_tm_polytime hLit0
    simpa [Function.comp, X] using hComp
  have hVar1 : TMPolyTimeMap X EncodedType.nat
      (fun p : PrefixCoeffInput => p.1.2.2.1.var) := by
    have hComp := TMPolyTimeMap.comp Clique.literal_var_tm_polytime hLit1
    simpa [Function.comp, X] using hComp
  have hVar2 : TMPolyTimeMap X EncodedType.nat
      (fun p : PrefixCoeffInput => p.1.2.2.2.var) := by
    have hComp := TMPolyTimeMap.comp Clique.literal_var_tm_polytime hLit2
    simpa [Function.comp, X] using hComp
  have hNeg0 : TMPolyTimeMap X EncodedType.bool
      (fun p : PrefixCoeffInput => p.1.2.1.neg) := by
    have hComp := TMPolyTimeMap.comp Clique.literal_neg_tm_polytime hLit0
    simpa [Function.comp, X] using hComp
  have hNeg1 : TMPolyTimeMap X EncodedType.bool
      (fun p : PrefixCoeffInput => p.1.2.2.1.neg) := by
    have hComp := TMPolyTimeMap.comp Clique.literal_neg_tm_polytime hLit1
    simpa [Function.comp, X] using hComp
  have hNeg2 : TMPolyTimeMap X EncodedType.bool
      (fun p : PrefixCoeffInput => p.1.2.2.2.neg) := by
    have hComp := TMPolyTimeMap.comp Clique.literal_neg_tm_polytime hLit2
    simpa [Function.comp, X] using hComp
  have hMatch0 : TMPolyTimeMap X EncodedType.bool
      (fun p : PrefixCoeffInput => decide (p.2 = p.1.2.1.var)) := by
    have hPair := TMPolyTimeMap.prod_mk hIndex hVar0
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hPair
    simpa [Function.comp, X] using hComp
  have hMatch1 : TMPolyTimeMap X EncodedType.bool
      (fun p : PrefixCoeffInput => decide (p.2 = p.1.2.2.1.var)) := by
    have hPair := TMPolyTimeMap.prod_mk hIndex hVar1
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hPair
    simpa [Function.comp, X] using hComp
  have hMatch2 : TMPolyTimeMap X EncodedType.bool
      (fun p : PrefixCoeffInput => decide (p.2 = p.1.2.2.2.var)) := by
    have hPair := TMPolyTimeMap.prod_mk hIndex hVar2
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hPair
    simpa [Function.comp, X] using hComp
  have hCoeff0Input :
      TMPolyTimeMap X literalCoeffAtInputEncodedType
        (fun p : PrefixCoeffInput => (p.1.2.1, p.2)) :=
    TMPolyTimeMap.prod_mk hLit0 hIndex
  have hOne : TMPolyTimeMap X EncodedType.int
      (fun p : PrefixCoeffInput => literalCoeffAt p.1.2.1 p.2) := by
    have hComp := TMPolyTimeMap.comp literalCoeffAt_tm_polytime hCoeff0Input
    simpa [Function.comp, literalCoeffAtInputEncodedType, X] using hComp
  have hMatch1Neg1 :
      TMPolyTimeMap X boolPairEncodedType
        (fun p : PrefixCoeffInput => (decide (p.2 = p.1.2.2.1.var), p.1.2.2.1.neg)) :=
    TMPolyTimeMap.prod_mk hMatch1 hNeg1
  have hNeg0Tail :
      TMPolyTimeMap X boolTripleEncodedType
        (fun p : PrefixCoeffInput =>
          (p.1.2.1.neg, (decide (p.2 = p.1.2.2.1.var), p.1.2.2.1.neg))) :=
    TMPolyTimeMap.prod_mk hNeg0 hMatch1Neg1
  have hFlags2 :
      TMPolyTimeMap X bool4EncodedType
        (fun p : PrefixCoeffInput =>
          (decide (p.2 = p.1.2.1.var),
            (p.1.2.1.neg, (decide (p.2 = p.1.2.2.1.var), p.1.2.2.1.neg)))) :=
    TMPolyTimeMap.prod_mk hMatch0 hNeg0Tail
  have hTwo : TMPolyTimeMap X EncodedType.int
      (fun p : PrefixCoeffInput =>
        prefixCoeffTwoFromFlags
          (decide (p.2 = p.1.2.1.var),
            (p.1.2.1.neg, (decide (p.2 = p.1.2.2.1.var), p.1.2.2.1.neg)))) := by
    have hComp := TMPolyTimeMap.comp prefixCoeffTwoFromFlags_tm_polytime hFlags2
    simpa [Function.comp, X] using hComp
  have hMatch2Neg2 :
      TMPolyTimeMap X boolPairEncodedType
        (fun p : PrefixCoeffInput => (decide (p.2 = p.1.2.2.2.var), p.1.2.2.2.neg)) :=
    TMPolyTimeMap.prod_mk hMatch2 hNeg2
  have hNeg1Tail :
      TMPolyTimeMap X boolTripleEncodedType
        (fun p : PrefixCoeffInput =>
          (p.1.2.2.1.neg, (decide (p.2 = p.1.2.2.2.var), p.1.2.2.2.neg))) :=
    TMPolyTimeMap.prod_mk hNeg1 hMatch2Neg2
  have hMatch1Tail :
      TMPolyTimeMap X bool4EncodedType
        (fun p : PrefixCoeffInput =>
          (decide (p.2 = p.1.2.2.1.var),
            (p.1.2.2.1.neg, (decide (p.2 = p.1.2.2.2.var), p.1.2.2.2.neg)))) :=
    TMPolyTimeMap.prod_mk hMatch1 hNeg1Tail
  have hNeg0Tail3 :
      TMPolyTimeMap X bool5EncodedType
        (fun p : PrefixCoeffInput =>
          (p.1.2.1.neg,
            (decide (p.2 = p.1.2.2.1.var),
              (p.1.2.2.1.neg,
                (decide (p.2 = p.1.2.2.2.var), p.1.2.2.2.neg))))) :=
    TMPolyTimeMap.prod_mk hNeg0 hMatch1Tail
  have hFlags3 :
      TMPolyTimeMap X bool6EncodedType
        (fun p : PrefixCoeffInput =>
          (decide (p.2 = p.1.2.1.var),
            (p.1.2.1.neg,
              (decide (p.2 = p.1.2.2.1.var),
                (p.1.2.2.1.neg,
                  (decide (p.2 = p.1.2.2.2.var), p.1.2.2.2.neg)))))) :=
    TMPolyTimeMap.prod_mk hMatch0 hNeg0Tail3
  have hThree : TMPolyTimeMap X EncodedType.int
      (fun p : PrefixCoeffInput =>
        prefixCoeffThreeFromFlags
          (decide (p.2 = p.1.2.1.var),
            (p.1.2.1.neg,
              (decide (p.2 = p.1.2.2.1.var),
                (p.1.2.2.1.neg,
                  (decide (p.2 = p.1.2.2.2.var), p.1.2.2.2.neg)))))) := by
    have hComp := TMPolyTimeMap.comp prefixCoeffThreeFromFlags_tm_polytime hFlags3
    simpa [Function.comp, X] using hComp
  have hZero : TMPolyTimeMap X EncodedType.int (fun _ : PrefixCoeffInput => (0 : Int)) :=
    TMPolyTimeMap.const X EncodedType.int (0 : Int)
  have hEq2 : TMPolyTimeMap X EncodedType.bool
      (fun p : PrefixCoeffInput => decide (p.1.1 = (2 : Nat))) :=
    natEqConst_tm_polytime X hCount 2
  have hBranchInput2 :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : PrefixCoeffInput => (decide (p.1.1 = (2 : Nat)), p)) :=
    TMPolyTimeMap.prod_mk hEq2 (TMPolyTimeMap.id X)
  have hBranch2 :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) EncodedType.int
        (fun p : Bool × PrefixCoeffInput =>
          match p.1 with
          | true =>
              prefixCoeffTwoFromFlags
                (decide (p.2.2 = p.2.1.2.1.var),
                  (p.2.1.2.1.neg,
                    (decide (p.2.2 = p.2.1.2.2.1.var), p.2.1.2.2.1.neg)))
          | false =>
              prefixCoeffThreeFromFlags
                (decide (p.2.2 = p.2.1.2.1.var),
                  (p.2.1.2.1.neg,
                    (decide (p.2.2 = p.2.1.2.2.1.var),
                      (p.2.1.2.2.1.neg,
                        (decide (p.2.2 = p.2.1.2.2.2.var), p.2.1.2.2.2.neg)))))) :=
    Clique.boolProduct_dispatch_tm_polytime X EncodedType.int
      (fFalse := fun p : PrefixCoeffInput =>
        prefixCoeffThreeFromFlags
          (decide (p.2 = p.1.2.1.var),
            (p.1.2.1.neg,
              (decide (p.2 = p.1.2.2.1.var),
                (p.1.2.2.1.neg,
                  (decide (p.2 = p.1.2.2.2.var), p.1.2.2.2.neg))))))
      (fTrue := fun p : PrefixCoeffInput =>
        prefixCoeffTwoFromFlags
          (decide (p.2 = p.1.2.1.var),
            (p.1.2.1.neg, (decide (p.2 = p.1.2.2.1.var), p.1.2.2.1.neg))))
      hThree hTwo
  have hTail2 : TMPolyTimeMap X EncodedType.int
      (fun p : PrefixCoeffInput =>
        if p.1.1 = (2 : Nat) then
          prefixCoeffTwoFromFlags
            (decide (p.2 = p.1.2.1.var),
              (p.1.2.1.neg, (decide (p.2 = p.1.2.2.1.var), p.1.2.2.1.neg)))
        else
          prefixCoeffThreeFromFlags
            (decide (p.2 = p.1.2.1.var),
              (p.1.2.1.neg,
                (decide (p.2 = p.1.2.2.1.var),
                  (p.1.2.2.1.neg,
                    (decide (p.2 = p.1.2.2.2.var), p.1.2.2.2.neg)))))) := by
    have hComp := TMPolyTimeMap.comp hBranch2 hBranchInput2
    convert hComp using 1
    funext p
    by_cases h : p.1.1 = (2 : Nat) <;> simp [Function.comp, h]
  have hEq1 : TMPolyTimeMap X EncodedType.bool
      (fun p : PrefixCoeffInput => decide (p.1.1 = (1 : Nat))) :=
    natEqConst_tm_polytime X hCount 1
  have hBranchInput1 :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : PrefixCoeffInput => (decide (p.1.1 = (1 : Nat)), p)) :=
    TMPolyTimeMap.prod_mk hEq1 (TMPolyTimeMap.id X)
  have hBranch1 :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) EncodedType.int
        (fun p : Bool × PrefixCoeffInput =>
          match p.1 with
          | true => literalCoeffAt p.2.1.2.1 p.2.2
          | false =>
              if p.2.1.1 = (2 : Nat) then
                prefixCoeffTwoFromFlags
                  (decide (p.2.2 = p.2.1.2.1.var),
                    (p.2.1.2.1.neg,
                      (decide (p.2.2 = p.2.1.2.2.1.var), p.2.1.2.2.1.neg)))
              else
                prefixCoeffThreeFromFlags
                  (decide (p.2.2 = p.2.1.2.1.var),
                    (p.2.1.2.1.neg,
                      (decide (p.2.2 = p.2.1.2.2.1.var),
                        (p.2.1.2.2.1.neg,
                          (decide (p.2.2 = p.2.1.2.2.2.var), p.2.1.2.2.2.neg)))))) :=
    Clique.boolProduct_dispatch_tm_polytime X EncodedType.int
      (fFalse := fun p : PrefixCoeffInput =>
        if p.1.1 = (2 : Nat) then
          prefixCoeffTwoFromFlags
            (decide (p.2 = p.1.2.1.var),
              (p.1.2.1.neg, (decide (p.2 = p.1.2.2.1.var), p.1.2.2.1.neg)))
        else
          prefixCoeffThreeFromFlags
            (decide (p.2 = p.1.2.1.var),
              (p.1.2.1.neg,
                (decide (p.2 = p.1.2.2.1.var),
                  (p.1.2.2.1.neg,
                    (decide (p.2 = p.1.2.2.2.var), p.1.2.2.2.neg))))))
      (fTrue := fun p : PrefixCoeffInput => literalCoeffAt p.1.2.1 p.2)
      hTail2 hOne
  have hTail1 : TMPolyTimeMap X EncodedType.int
      (fun p : PrefixCoeffInput =>
        if p.1.1 = (1 : Nat) then
          literalCoeffAt p.1.2.1 p.2
        else if p.1.1 = (2 : Nat) then
          prefixCoeffTwoFromFlags
            (decide (p.2 = p.1.2.1.var),
              (p.1.2.1.neg, (decide (p.2 = p.1.2.2.1.var), p.1.2.2.1.neg)))
        else
          prefixCoeffThreeFromFlags
            (decide (p.2 = p.1.2.1.var),
              (p.1.2.1.neg,
                (decide (p.2 = p.1.2.2.1.var),
                  (p.1.2.2.1.neg,
                    (decide (p.2 = p.1.2.2.2.var), p.1.2.2.2.neg)))))) := by
    have hComp := TMPolyTimeMap.comp hBranch1 hBranchInput1
    convert hComp using 1
    funext p
    by_cases h : p.1.1 = (1 : Nat) <;> simp [Function.comp, h]
  have hEq0 : TMPolyTimeMap X EncodedType.bool
      (fun p : PrefixCoeffInput => decide (p.1.1 = (0 : Nat))) :=
    natEqConst_tm_polytime X hCount 0
  have hBranchInput0 :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : PrefixCoeffInput => (decide (p.1.1 = (0 : Nat)), p)) :=
    TMPolyTimeMap.prod_mk hEq0 (TMPolyTimeMap.id X)
  have hBranch0 :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) EncodedType.int
        (fun p : Bool × PrefixCoeffInput =>
          match p.1 with
          | true => (0 : Int)
          | false =>
              if p.2.1.1 = (1 : Nat) then
                literalCoeffAt p.2.1.2.1 p.2.2
              else if p.2.1.1 = (2 : Nat) then
                prefixCoeffTwoFromFlags
                  (decide (p.2.2 = p.2.1.2.1.var),
                    (p.2.1.2.1.neg,
                      (decide (p.2.2 = p.2.1.2.2.1.var), p.2.1.2.2.1.neg)))
              else
                prefixCoeffThreeFromFlags
                  (decide (p.2.2 = p.2.1.2.1.var),
                    (p.2.1.2.1.neg,
                      (decide (p.2.2 = p.2.1.2.2.1.var),
                        (p.2.1.2.2.1.neg,
                          (decide (p.2.2 = p.2.1.2.2.2.var), p.2.1.2.2.2.neg)))))) :=
    Clique.boolProduct_dispatch_tm_polytime X EncodedType.int
      (fFalse := fun p : PrefixCoeffInput =>
        if p.1.1 = (1 : Nat) then
          literalCoeffAt p.1.2.1 p.2
        else if p.1.1 = (2 : Nat) then
          prefixCoeffTwoFromFlags
            (decide (p.2 = p.1.2.1.var),
              (p.1.2.1.neg, (decide (p.2 = p.1.2.2.1.var), p.1.2.2.1.neg)))
        else
          prefixCoeffThreeFromFlags
            (decide (p.2 = p.1.2.1.var),
              (p.1.2.1.neg,
                (decide (p.2 = p.1.2.2.1.var),
                  (p.1.2.2.1.neg,
                    (decide (p.2 = p.1.2.2.2.var), p.1.2.2.2.neg))))))
      (fTrue := fun _ : PrefixCoeffInput => (0 : Int))
      hTail1 hZero
  have hOut := TMPolyTimeMap.comp hBranch0 hBranchInput0
  convert hOut using 1
  funext p
  by_cases h : p.1.1 = (0 : Nat)
  · simp [prefixCoeffAtComputed, Function.comp, h]
  · simp [prefixCoeffAtComputed, Function.comp, h]
    rfl

end ZeroOneIP
end Karp21
end ComplexityReduction
