/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP.Hardness.PPDefinability
import ComplexityReduction.Program.List
import ComplexityReduction.Program.ContextListMap
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.BoolDispatch
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatPair
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatArithmetic
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ListLookupTM

/-!
The general direct-TM compiler for primitive-positive interpretations.

A `LanguageInterpretation Γ' Γ` substitutes every constraint of a `Γ'`-formula by
its Γ-gadget, renaming auxiliary variables to fresh keys above the formula's
maximum variable (`Hardness.PPDefinability.interpret`).  This module proves,
once and for all, that this substitution is polynomial-time computable on the
canonical finite-table formula encodings:

* every gadget is compiled to a fixed *table* of target rows (one row per
  gadget constraint, with each position tagged either as an output position of
  the gadget or as a fresh auxiliary variable),
* the substitution is replayed on the *code* of the formula (`interpretCode`),
  using only unary-natural arithmetic, list scans, and fixed finite lookups,
* `interpretCode` agrees exactly with `formulaCode Γ (interpret ...)` on every
  well-formed formula code, and
* the code-level computation is assembled from the library's direct-TM2
  combinators (`interpretation_tmPolyTime`), so every pp-interpretation
  automatically carries a `TMPolyTimeMap` witness of its substitution program.

The transport theorems `certifiedReduction_of_interpretation_auto` and
`nPHard_of_interpretation_auto` then build the certified reduction and the
NP-hardness transport without any caller-supplied machine.
-/

namespace ComplexityReduction
namespace Domain
namespace BooleanCSP
namespace Hardness

open ComplexityReduction.CSP
open ComplexityReduction.Encoding
open ComplexityReduction.Program
open Presentation.FiniteDomainCSPTable

noncomputable section

/-! ### Code-level variable bounds -/

/-- The maximum variable of one constraint variable list. -/
def varsMaxCode (vars : List Nat) : Nat :=
  vars.foldl Nat.max 0

/-- The maximum variable of one formula code (list of constraint codes). -/
def codeMaxVar (code : List (Nat × List Nat)) : Nat :=
  code.foldl (fun acc p => Nat.max acc (varsMaxCode p.2)) 0

/-- The code-level variable maximum agrees with the constraint maximum. -/
theorem varsMaxCode_eq_constraintMaxVar {Γ : Gamma} (constraint : Constraint Γ) :
    varsMaxCode constraint.varsList = Constraint.maxVar constraint :=
  rfl

theorem foldl_map_constraintCode {Γ : Gamma} :
    ∀ (cs : List (Constraint Γ)) (acc : Nat),
      (cs.map constraintCode).foldl (fun acc p => Nat.max acc (varsMaxCode p.2)) acc =
        cs.foldl (fun acc c => Nat.max acc (Constraint.maxVar c)) acc := by
  intro cs
  induction cs with
  | nil => intro acc; rfl
  | cons c cs' ih =>
      intro acc
      simp [constraintCode, varsMaxCode_eq_constraintMaxVar c]
      exact ih (Nat.max acc (Constraint.maxVar c))

/-- The code-level formula maximum agrees with the formula maximum. -/
theorem codeMaxVar_eq_formulaMaxVar {Γ : Gamma} (formula : Formula Γ) :
    codeMaxVar (formulaCode Γ formula) = Formula.maxVar formula := by
  unfold codeMaxVar formulaCode Formula.maxVar
  exact foldl_map_constraintCode formula 0

/-- Every list member is bounded by the maximum fold. -/
theorem le_varsMaxCode {vars : List Nat} {v : Nat} (member : v ∈ vars) :
    v ≤ varsMaxCode vars := by
  unfold varsMaxCode
  exact le_foldl_max member

/-- A member of an encoded list is bounded by the list's input size. -/
theorem member_le_list_inputSize (X : EncodedType) {xs : List X.Carrier} {x : X.Carrier}
    (member : x ∈ xs) :
    X.inputSize x ≤ (EncodedType.list X).inputSize xs := by
  induction xs with
  | nil => cases member
  | cons y ys ih =>
      cases member with
      | head =>
          rw [EncodedType.inputSize_list_cons]
          omega
      | tail _ member' =>
          have hrec := ih member'
          rw [EncodedType.inputSize_list_cons]
          omega

def natListInputSize (xs : List Nat) : Nat :=
  (EncodedType.list EncodedType.nat).inputSize xs

@[simp]
theorem natListInputSize_nil : natListInputSize [] = 0 := by
  rfl

@[simp]
theorem natListInputSize_cons (x : Nat) (xs : List Nat) :
    natListInputSize (x :: xs) = x + 2 + natListInputSize xs := by
  unfold natListInputSize
  simp [EncodedType.inputSize, EncodedType.list, EncodedType.nat]
  omega

/-- The singleton of a member of a natural list is bounded by the list's input size. -/
theorem singleton_le_listInputSize_of_mem {xs : List Nat} {v : Nat} (member : v ∈ xs) :
    natListInputSize [v] ≤ natListInputSize xs := by
  induction xs with
  | nil => cases member
  | cons w ws ih =>
      cases member with
      | head =>
          have hv : natListInputSize [v] = v + 2 := by
            simp [natListInputSize, EncodedType.inputSize, EncodedType.list, EncodedType.nat]
          have hw : natListInputSize (v :: ws) = v + 2 + natListInputSize ws := by
            simp [natListInputSize_cons]
          rw [hv, hw]
          omega
      | tail _ member' =>
          have hrec := ih member'
          have hv : natListInputSize [v] = v + 2 := by
            simp [natListInputSize, EncodedType.inputSize, EncodedType.list, EncodedType.nat]
          have hw : natListInputSize (w :: ws) = w + 2 + natListInputSize ws := by
            simp [natListInputSize_cons]
          rw [hw, hv]
          omega

theorem inputSize_entry (c : Nat × List Nat) :
    natListInputSize c.2 + 1 ≤
      (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat)).inputSize c := by
  have hEq : (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat)).inputSize c =
      c.1 + 2 + natListInputSize c.2 := by
    simp [EncodedType.inputSize_prod, EncodedType.inputSize_nat, natListInputSize]
  rw [hEq]
  omega

/-- The variable maximum of one constraint code entry is bounded by the entry's code size. -/
theorem varsMaxCode_le_entryCodeSize (c : Nat × List Nat) :
    varsMaxCode c.2 + 1 ≤
      (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat)).inputSize c := by
  let Code := EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat)
  have hEntryVars : natListInputSize c.2 + 1 ≤ Code.inputSize c :=
    inputSize_entry c
  by_cases hEmpty : c.2 = []
  · rw [hEmpty]
    simp [varsMaxCode, EncodedType.inputSize_list_nil]
    omega
  · have hVars : varsMaxCode c.2 ≤ natListInputSize c.2 := by
      -- each element contributes its value plus its delimiter to the list code
      have hFoldAdd : ∀ (l : List Nat) (acc : Nat),
          l.foldl (fun a v => a + v + 1) acc = acc + l.foldl (fun a v => a + v + 1) 0 := by
        intro l
        induction l with
        | nil => intro acc; simp
        | cons w ws ih =>
            intro acc
            calc
              (w :: ws).foldl (fun a v => a + v + 1) acc
                  = ws.foldl (fun a v => a + v + 1) (acc + w + 1) := by
                    rw [List.foldl_cons]
              _ = (acc + w + 1) + ws.foldl (fun a v => a + v + 1) 0 := ih (acc + w + 1)
              _ = acc + (w + 1 + ws.foldl (fun a v => a + v + 1) 0) := by omega
              _ = acc + (w :: ws).foldl (fun a v => a + v + 1) 0 := by
                    rw [List.foldl_cons]
                    rw [ih (0 + w + 1)]
                    omega
      have hSumLe : c.2.foldl (fun acc v => acc + v + 1) 0 ≤ natListInputSize c.2 := by
        induction c.2 with
        | nil => simp
        | cons w ws ih =>
            rw [List.foldl_cons]
            rw [hFoldAdd ws (0 + w + 1)]
            simp [natListInputSize_cons]
            omega
      have hMaxLeSum : c.2.foldl Nat.max 0 ≤ c.2.foldl (fun acc v => acc + v + 1) 0 := by
        have hAux : ∀ (l : List Nat) (acc acc' : Nat), acc ≤ acc' →
            l.foldl Nat.max acc ≤ l.foldl (fun a v => a + v + 1) acc' := by
          intro l
          induction l with
          | nil => intro acc acc' h; exact h
          | cons w ws ih =>
              intro acc acc' h
              have hmax : Nat.max acc w ≤ acc + w := max_le_iff.mpr ⟨by omega, by omega⟩
              have hrec := ih (Nat.max acc w) (acc' + w + 1)
                (Nat.le_trans hmax (by omega))
              rw [List.foldl_cons]
              exact hrec
        exact hAux c.2 0 0 (by omega)
      unfold varsMaxCode
      exact Nat.le_trans hMaxLeSum hSumLe
    exact Nat.le_trans (by omega) hEntryVars

/-- The variable maximum of one constraint code entry is bounded by the formula code size. -/
theorem varsMaxCode_le_codeInputSize {code : List (Nat × List Nat)} {c : Nat × List Nat}
    (hEntry : (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat)).inputSize c ≤
      (EncodedType.list (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))).inputSize
        code) :
    varsMaxCode c.2 + 1 ≤
      (EncodedType.list (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))).inputSize
        code := by
  exact Nat.le_trans (varsMaxCode_le_entryCodeSize c) hEntry

/-- Unary natural comparison `a ≤ b` as a Boolean. -/
def natLeBool (p : Nat × Nat) : Bool :=
  ComplexityReduction.natLtBool (p.1, p.2 + 1)

/-- The maximum of two unary naturals, computed by comparison and selection. -/
def natMaxCode (p : Nat × Nat) : Nat :=
  match natLeBool p with
  | true => p.2
  | false => p.1

/-- Unary natural maximum is direct-TM polynomial time. -/
theorem natMaxCode_tmPolyTime :
    TMPolyTimeMap (EncodedType.prod EncodedType.nat EncodedType.nat) EncodedType.nat natMaxCode := by
  let X := EncodedType.prod EncodedType.nat EncodedType.nat
  have hFst : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hSnd : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hSucc : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.2 + 1) := by
    have hAdd := ComplexityReduction.nat_add_const_tm_polytime 1
    have hComp := TMPolyTimeMap.comp hAdd hSnd
    simpa [Function.comp] using hComp
  have hLtInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : Nat × Nat => (p.1, p.2 + 1)) :=
    TMPolyTimeMap.prod_mk hFst hSucc
  have hLt : TMPolyTimeMap X EncodedType.bool
      (fun p : Nat × Nat => ComplexityReduction.natLtBool (p.1, p.2 + 1)) := by
    have hComp := TMPolyTimeMap.comp ComplexityReduction.natLtBool_tm_polytime hLtInput
    simpa [Function.comp] using hComp
  have hFlag : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun p : Nat × Nat => (natLeBool p, p)) :=
    TMPolyTimeMap.prod_mk (by simpa [natLeBool] using hLt) (TMPolyTimeMap.id X)
  have hDispatch := ComplexityReduction.boolProduct_dispatch_tm_polytime X EncodedType.nat
    (fFalse := fun p : X.Carrier => p.1) (fTrue := fun p : X.Carrier => p.2)
    hFst hSnd
  have hComp := TMPolyTimeMap.comp hDispatch hFlag
  simpa [natMaxCode, Function.comp] using hComp

/-- `natMaxCode` computes the natural maximum. -/
theorem natMaxCode_eq_max (acc x : Nat) : natMaxCode (acc, x) = Nat.max acc x := by
  unfold natMaxCode
  cases hb : natLeBool (acc, x)
  · have hnot : ¬ acc < x + 1 := by
      intro h
      have hTrue : ComplexityReduction.natLtBool (acc, x + 1) = true := by
        simp [ComplexityReduction.natLtBool, h]
      exact (by simpa [natLeBool, hb] : ¬ ComplexityReduction.natLtBool (acc, x + 1) = true) hTrue
    have hge : x ≤ acc := by omega
    simp [hb, hge]
  · have hle : acc ≤ x := by
      have hTrue : ComplexityReduction.natLtBool (acc, x + 1) = true := by
        simpa [natLeBool] using hb
      exact Nat.le_of_lt_succ (of_decide_eq_true (by simpa [ComplexityReduction.natLtBool] using hTrue))
    simp [hb, hle]

theorem foldl_natMaxCode_eq_foldl_max (xs : List Nat) :
    xs.foldl (fun acc x => natMaxCode (acc, x)) 0 = varsMaxCode xs := by
  have hFold : ∀ (l : List Nat) (acc : Nat),
      l.foldl (fun a x => natMaxCode (a, x)) acc = l.foldl Nat.max acc := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons x xs' ih =>
        intro acc
        rw [List.foldl_cons]
        rw [List.foldl_cons]
        rw [natMaxCode_eq_max acc x]
        exact ih (Nat.max acc x)
  unfold varsMaxCode
  exact hFold xs 0

/-- The code-level variable-maximum fold is direct-TM polynomial time. -/
theorem varsMaxCode_tmPolyTime :
    TMPolyTimeMap (EncodedType.list EncodedType.nat) EncodedType.nat varsMaxCode := by
  rcases natMaxCode_tmPolyTime with ⟨stepTM⟩
  have hFold : TMPolyTimeMap (EncodedType.list EncodedType.nat) EncodedType.nat
      (fun xs : List Nat => xs.foldl (fun acc x => natMaxCode (acc, x)) (0 : Nat)) := by
    refine TMPolyTimeMap.list_foldl_typed_growth_bounded
      EncodedType.nat EncodedType.nat natMaxCode (0 : Nat) stepTM
      (Polynomial.C 1) (Polynomial.X + Polynomial.C 1) ?_ ?_
    · intro source
      simp [EncodedType.inputSize_nat]
    · intro source accumulator item itemBound
      let acc' : Nat := accumulator
      let item' : Nat := item
      have hItemLe : item' + 1 ≤ (EncodedType.list EncodedType.nat).inputSize source := by
        have hsub : EncodedType.nat.inputSize item ≤ (EncodedType.list EncodedType.nat).inputSize source := by
          simpa [acc', item'] using itemBound
        simpa [EncodedType.inputSize_nat, item'] using hsub
      have hMaxLe : Nat.max acc' item' + 1 ≤ acc' + 1 + item' + 1 := by omega
      simp [EncodedType.inputSize_nat, natMaxCode_eq_max, acc', item'] at *
      omega
  convert hFold using 1
  funext xs
  exact (foldl_natMaxCode_eq_foldl_max xs).symm

/-- The code-level formula-maximum fold is direct-TM polynomial time. -/
theorem codeMaxVar_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.list (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat)))
      EncodedType.nat codeMaxVar := by
  let Code := EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat)
  have hVars : TMPolyTimeMap Code EncodedType.nat
      (fun p : Nat × List Nat => varsMaxCode p.2) := by
    have h := TMPolyTimeMap.comp varsMaxCode_tmPolyTime
      (TMPolyTimeMap.snd EncodedType.nat (EncodedType.list EncodedType.nat))
    simpa [Code, Function.comp] using h
  have hStep : TMPolyTimeMap (EncodedType.prod EncodedType.nat Code) EncodedType.nat
      (fun p : Nat × (Nat × List Nat) => Nat.max p.1 (varsMaxCode p.2.2)) := by
    have hAcc : TMPolyTimeMap (EncodedType.prod EncodedType.nat Code) EncodedType.nat
        (fun p : Nat × (Nat × List Nat) => p.1) := by
      simpa [Code] using TMPolyTimeMap.fst EncodedType.nat Code
    have hItem : TMPolyTimeMap (EncodedType.prod EncodedType.nat Code) EncodedType.nat
        (fun p : Nat × (Nat × List Nat) => varsMaxCode p.2.2) := by
      have h := TMPolyTimeMap.comp hVars (TMPolyTimeMap.snd EncodedType.nat Code)
      simpa [Function.comp, Code] using h
    have hInput : TMPolyTimeMap (EncodedType.prod EncodedType.nat Code)
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × (Nat × List Nat) => (p.1, varsMaxCode p.2.2)) :=
      TMPolyTimeMap.prod_mk hAcc hItem
    have hMax := TMPolyTimeMap.comp natMaxCode_tmPolyTime hInput
    convert hMax using 1
    funext p
    change Nat.max p.1 (varsMaxCode p.2.2) = natMaxCode (p.1, varsMaxCode p.2.2)
    rw [natMaxCode_eq_max]
  rcases hStep with ⟨stepTM⟩
  refine TMPolyTimeMap.list_foldl_typed_growth_bounded
    Code EncodedType.nat
    (fun p : Nat × (Nat × List Nat) => Nat.max p.1 (varsMaxCode p.2.2)) (0 : Nat) stepTM
    (Polynomial.C 1) (Polynomial.X + Polynomial.C 1) ?_ ?_
  · intro source
    simp [EncodedType.inputSize_nat]
  · intro source accumulator item itemBound
    have hItemLe : varsMaxCode item.2 + 1 ≤
        (EncodedType.list Code).inputSize source := by
      exact varsMaxCode_le_codeInputSize (c := item) itemBound
    let acc : Nat := accumulator
    have hmax : Nat.max acc (varsMaxCode item.2) ≤ acc + varsMaxCode item.2 :=
      max_le_iff.mpr ⟨by omega, by omega⟩
    have hGrowth : Nat.max acc (varsMaxCode item.2) + 1 ≤ acc + 1 + varsMaxCode item.2 + 1 := by omega
    simp [EncodedType.inputSize_nat]
    omega

/-! ### Maximal relation arity -/

/-- The maximal arity of one finite relation language. -/
noncomputable def maxRelationArity (Γ : Gamma) : Nat :=
  (Finset.univ : Finset Γ.Symbol).sup (fun s => (Γ.relationOf s).arity)

/-- Every relation arity is bounded by the maximal arity. -/
theorem arity_le_maxRelationArity (Γ : Gamma) (symbol : Γ.Symbol) :
    (Γ.relationOf symbol).arity ≤ maxRelationArity Γ := by
  unfold maxRelationArity
  exact Finset.le_sup (α := Nat) (β := Γ.Symbol)
    (s := (Finset.univ : Finset Γ.Symbol))
    (f := fun s => (Γ.relationOf s).arity) (b := symbol)
    (show symbol ∈ (Finset.univ : Finset Γ.Symbol) from by simp)

/-- Every constraint variable list has length at most the maximal arity. -/
theorem varsList_length_le_maxRelationArity {Γ : Gamma} (constraint : Constraint Γ) :
    constraint.varsList.length ≤ maxRelationArity Γ := by
  calc
    constraint.varsList.length = (Γ.relationOf constraint.symbol).arity := by
      rw [Constraint.varsList_length]
      rfl
    _ ≤ maxRelationArity Γ := arity_le_maxRelationArity Γ constraint.symbol

/-! ### The clamped list code -/

/-- Reversal by cons-fold is exactly `List.reverse`. -/
theorem reverse_eq_foldl_cons {α : Type} (vars : List α) :
    vars.reverse = vars.foldl (fun acc x => x :: acc) [] := by
  induction vars with
  | nil => rfl
  | cons x xs ih =>
      rw [List.reverse_cons]
      have hFoldApp : ∀ (l : List α) (acc acc' : List α),
          l.foldl (fun a x => x :: a) (acc ++ acc') = (l.foldl (fun a x => x :: a) acc) ++ acc' := by
        intro l
        induction l with
        | nil => intro acc acc'; rfl
        | cons y ys ih' =>
            intro acc acc'
            rw [List.foldl_cons]
            rw [List.foldl_cons]
            exact ih' (y :: acc) acc'
      have hApp : xs.foldl (fun a x => x :: a) [] ++ [x] =
          xs.foldl (fun a x => x :: a) [x] := by
        simpa using (hFoldApp xs [] [x]).symm
      rw [List.foldl_cons]
      rw [← hApp]
      rw [ih]

/-- List reversal is direct-TM polynomial time. -/
theorem reverse_tmPolyTime (X : EncodedType) :
    TMPolyTimeMap (EncodedType.list X) (EncodedType.list X) List.reverse := by
  let step (p : List X.Carrier × X.Carrier) : List X.Carrier := p.2 :: p.1
  have hStep : TMPolyTimeMap (EncodedType.prod (EncodedType.list X) X)
      (EncodedType.list X) step := by
    have hCons := TMPolyTimeMap.list_cons X
    have hPair : TMPolyTimeMap (EncodedType.prod (EncodedType.list X) X)
        (EncodedType.prod X (EncodedType.list X))
        (fun p : List X.Carrier × X.Carrier => (p.2, p.1)) := by
      have hFst : TMPolyTimeMap (EncodedType.prod (EncodedType.list X) X) X
          (fun p : List X.Carrier × X.Carrier => p.2) := by
        simpa using TMPolyTimeMap.snd (EncodedType.list X) X
      have hSnd : TMPolyTimeMap (EncodedType.prod (EncodedType.list X) X)
          (EncodedType.list X) (fun p : List X.Carrier × X.Carrier => p.1) := by
        simpa using TMPolyTimeMap.fst (EncodedType.list X) X
      exact TMPolyTimeMap.prod_mk hFst hSnd
    have hComp := TMPolyTimeMap.comp hCons hPair
    simpa [step, Function.comp] using hComp
  rcases hStep with ⟨stepTM⟩
  have hFold : TMPolyTimeMap (EncodedType.list X) (EncodedType.list X)
      (fun xs : List X.Carrier => xs.foldl (fun acc x => step (acc, x)) []) := by
    refine TMPolyTimeMap.list_foldl_typed_growth_bounded
      X (EncodedType.list X) step [] stepTM
      (Polynomial.C 0) (Polynomial.X + Polynomial.C 1) ?_ ?_
    · intro source
      simp [EncodedType.inputSize_list_nil]
    · intro source accumulator item itemBound
      simp [step, EncodedType.inputSize_list_cons]
      omega
  convert hFold using 1
  funext vars
  change vars.reverse = vars.foldl (fun acc x => x :: acc) []
  exact reverse_eq_foldl_cons vars

/-- The list-pair code is a right fold over the reversed list. -/
theorem listPairEncode_eq_reverse_foldl (vars : List Nat) :
    listPairEncode vars = vars.reverse.foldl (fun acc x => Nat.pair x acc + 1) 0 := by
  induction vars with
  | nil => rfl
  | cons x xs ih =>
      simp [listPairEncode, List.reverse_cons, ih]

/-- The clamped unary-injective list code: agrees with `listPairEncode` on lists of
length at most `maxArity`, and stays polynomially bounded on every input. -/
def listPairEncodeClamped (maxArity : Nat) (vars : List Nat) : Nat :=
  (Program.contextListMapExecutable (C := EncodedType.nat) (X := EncodedType.nat)
    ((varsMaxCode vars + 2) ^ (2 ^ (maxArity + 1)), vars.reverse)).foldl
      (fun acc item => if acc ≤ item.1 then Nat.pair item.2 acc + 1 else acc) 0

/-- The clamped list code agrees with the list-pair code on length-bounded lists. -/
theorem listPairEncodeClamped_eq_listPairEncode {maxArity : Nat} {vars : List Nat}
    (hLength : vars.length ≤ maxArity) :
    listPairEncodeClamped maxArity vars = listPairEncode vars := by
  classical
  unfold listPairEncodeClamped
  let M := varsMaxCode vars + 2
  let threshold := M ^ (2 ^ (maxArity + 1))
  have hM2 : 2 ≤ M := by unfold M; omega
  have hMpos : 1 ≤ M := by omega
  have hMpow : 4 ≤ M ^ 2 := by
    have h4 : 4 ≤ M * M := by nlinarith
    simpa [pow_two] using h4
  have hVM : ∀ v ∈ vars, v + 2 ≤ M := by
    intro v hv
    have hvMax : v ≤ varsMaxCode vars := le_varsMaxCode hv
    unfold M
    omega
  -- invariant: after k processed elements the accumulator is bounded by M^(2^(k+2)-2)
  have hMain : ∀ (ℓ : List Nat) (k : Nat), ℓ.length + k ≤ maxArity →
      (∀ v ∈ ℓ, v + 2 ≤ M) →
      ∀ acc : Nat, acc ≤ M ^ (2 ^ (k + 2) - 2) →
        (ℓ.map (fun v : Nat => (threshold, v))).foldl
          (fun acc item => if acc ≤ item.1 then Nat.pair item.2 acc + 1 else acc) acc =
        ℓ.foldl (fun acc x => Nat.pair x acc + 1) acc := by
    intro ℓ
    induction ℓ with
    | nil =>
        intro k hK hElem acc hAcc
        simp
    | cons v vs ih =>
        intro k hK hElem acc hAcc
        have hvM : v + 2 ≤ M := hElem v (by simp)
        have hStep : acc ≤ threshold := by
          have hExp : 2 ^ (k + 2) - 2 ≤ 2 ^ (maxArity + 1) := by
            have hLen : (v :: vs).length = vs.length + 1 := by simp
            have hk : k + 2 ≤ maxArity + 1 := by omega
            have hPow : 2 ^ (k + 2) ≤ 2 ^ (maxArity + 1) :=
              pow_le_pow_right' (by omega : 1 ≤ 2) hk
            exact Nat.le_trans (Nat.sub_le (2 ^ (k + 2)) 2) hPow
          unfold threshold
          exact Nat.le_trans hAcc (pow_le_pow_right' hMpos hExp)
        have hPairLe : Nat.pair v acc + 1 ≤ M ^ (2 ^ (k + 3) - 2) := by
          have hPair : Nat.pair v acc + 1 ≤ (Nat.max v acc + 1) ^ 2 :=
            Nat.pair_lt_max_add_one_sq v acc
          have he : 2 ^ (k + 2) - 2 ≠ 0 := by
            have hpow2 : 2 ^ (k + 2) ≥ 2 ^ 2 := pow_le_pow_right' (by omega : 1 ≤ 2) (by omega)
            omega
          have hMPowGe : M ≤ M ^ (2 ^ (k + 2) - 2) := by
            exact le_self_pow hMpos he
          have hAccV : acc + v + 1 ≤ 2 * M ^ (2 ^ (k + 2) - 2) := by
            have h1 : acc ≤ M ^ (2 ^ (k + 2) - 2) := hAcc
            have h2 : v + 1 ≤ M - 1 := by omega
            have h3 : M - 1 ≤ M ^ (2 ^ (k + 2) - 2) := by omega
            omega
          have hSq2 : (acc + v + 1) ^ 2 ≤ (2 * M ^ (2 ^ (k + 2) - 2)) ^ 2 :=
            Nat.pow_le_pow_left hAccV 2
          have hExpEq : (2 ^ (k + 2) - 2) * 2 + 2 = 2 ^ (k + 3) - 2 := by
            have hpow : 2 ^ (k + 3) = 2 ^ (k + 2) * 2 := by
              have hk3 : k + 3 = (k + 2) + 1 := by omega
              rw [hk3, pow_succ]
            rw [hpow]
            have h2 : 4 ≤ 2 ^ (k + 2) := by
              have h4 : 2 ^ 2 ≤ 2 ^ (k + 2) := pow_le_pow_right' (by omega : 1 ≤ 2) (by omega)
              norm_num at h4
              exact h4
            omega
          have hSq3 : (2 * M ^ (2 ^ (k + 2) - 2)) ^ 2 ≤ M ^ ((2 ^ (k + 2) - 2) * 2 + 2) := by
            calc
              (2 * M ^ (2 ^ (k + 2) - 2)) ^ 2
                  = 2 ^ 2 * (M ^ (2 ^ (k + 2) - 2)) ^ 2 := by rw [mul_pow]
              _ = 4 * M ^ ((2 ^ (k + 2) - 2) * 2) := by
                    rw [pow_two, pow_mul]
                    omega
              _ ≤ M ^ ((2 ^ (k + 2) - 2) * 2) * M ^ 2 := by
                    have h4le : 4 ≤ M ^ 2 := hMpow
                    calc
                      4 * M ^ ((2 ^ (k + 2) - 2) * 2)
                          ≤ M ^ 2 * M ^ ((2 ^ (k + 2) - 2) * 2) :=
                            Nat.mul_le_mul_right (M ^ ((2 ^ (k + 2) - 2) * 2)) h4le
                      _ = M ^ ((2 ^ (k + 2) - 2) * 2) * M ^ 2 := by rw [Nat.mul_comm]
              _ = M ^ ((2 ^ (k + 2) - 2) * 2 + 2) := by
                    rw [← pow_add]
          have hMainBound : (acc + v + 1) ^ 2 ≤ M ^ (2 ^ (k + 3) - 2) := by
            rw [← hExpEq]
            exact Nat.le_trans hSq2 hSq3
          have hMaxV : Nat.max v acc ≤ acc + v := max_le_iff.mpr ⟨by omega, by omega⟩
          have hSq : (Nat.max v acc + 1) ^ 2 ≤ (acc + v + 1) ^ 2 := by
            exact Nat.pow_le_pow_left (by omega) 2
          exact Nat.le_trans hPair (Nat.le_trans hSq hMainBound)
        have hStepVal : (if acc ≤ (threshold, v).1 then Nat.pair (threshold, v).2 acc + 1 else acc)
            = Nat.pair v acc + 1 := by
          simp [hStep]
        -- unfold the fold over the cons
        rw [List.map_cons, List.foldl_cons]
        rw [hStepVal]
        have hK' : vs.length + (k + 1) ≤ maxArity := by
          have hLen : (v :: vs).length = vs.length + 1 := by simp
          omega
        exact ih (k + 1) hK' (by
          intro w hw
          exact hElem w (by simp [hw])) (Nat.pair v acc + 1) hPairLe
  have hElemRev : ∀ v ∈ vars.reverse, v + 2 ≤ M := by
    intro v hv
    exact hVM v (List.mem_reverse.mp hv)
  have hApplied := hMain vars.reverse 0 (by
    have hRev : vars.reverse.length = vars.length := List.length_reverse
    omega) hElemRev 0 (by
      have hpow : 0 ≤ M ^ (2 ^ (0 + 2) - 2) := Nat.zero_le _
      exact hpow)
  have hTarget : vars.reverse.foldl (fun acc x => Nat.pair x acc + 1) 0 = listPairEncode vars := by
    exact (listPairEncode_eq_reverse_foldl vars).symm
  -- the clamped fold processes the attached reversed list
  have hAttached : Program.contextListMapExecutable (C := EncodedType.nat) (X := EncodedType.nat)
      ((varsMaxCode vars + 2) ^ (2 ^ (maxArity + 1)), vars.reverse) =
        vars.reverse.map (fun v : Nat => ((varsMaxCode vars + 2) ^ (2 ^ (maxArity + 1)), v)) := by
    exact Program.contextListMapExecutable_eq_map (C := EncodedType.nat) (X := EncodedType.nat)
      ((varsMaxCode vars + 2) ^ (2 ^ (maxArity + 1))) vars.reverse
  rw [hAttached]
  exact hApplied.trans hTarget

/-! ### Gadget tables -/

/-- One gadget row: the target relation code and, per position, an output position or a fresh variable. -/
noncomputable def gadgetRow {Γ : Gamma} {relation : BooleanRelation}
    (gadget : Gadget Γ relation) (d : Constraint Γ) : Nat × List (Bool × Nat) :=
  (Presentation.FiniteDomainCSPTable.relationCode Γ d.symbol,
    List.ofFn (fun j =>
      if h : d.vars j ∈ Set.range gadget.outputs then
        (true, (Classical.choose h).val)
      else (false, d.vars j)))

/-- The rows of one relation symbol of the source language. -/
noncomputable def rowsOfSymbol {Γ' Γ : Gamma} (interpretation : LanguageInterpretation Γ' Γ)
    (symbol : Γ'.Symbol) : List (Nat × List (Bool × Nat)) :=
  (interpretation.gadgetOf symbol).formula.map (gadgetRow (interpretation.gadgetOf symbol))

/-- The rows of a source relation code, defaulting to the empty table off-range. -/
noncomputable def rowsOfCode {Γ' Γ : Gamma} (interpretation : LanguageInterpretation Γ' Γ)
    (code : Nat) : List (Nat × List (Bool × Nat)) :=
  if h : code < Fintype.card Γ'.Symbol then
    rowsOfSymbol interpretation (Presentation.FiniteDomainCSPTable.relationSymbol Γ' ⟨code, h⟩)
  else []

/-- The rows of a source relation code, by fixed finite lookup over the code range. -/
noncomputable def rowsByCode {Γ' Γ : Gamma} (interpretation : LanguageInterpretation Γ' Γ)
    (code : Nat) : List (Nat × List (Bool × Nat)) :=
  (List.range (Fintype.card Γ'.Symbol)).foldl
    (fun acc c => if code = c then rowsOfCode interpretation c else acc)
    (rowsOfCode interpretation 0)

/-- Splitting a range at a fixed code: `range n = range code ++ [code] ++ shifted tail`. -/
theorem range_split (n code : Nat) (h : code < n) :
    List.range n = List.range code ++ [code] ++
      (List.range (n - code - 1)).map (fun i => i + code + 1) := by
  induction n with
  | zero => cases h
  | succ n ih =>
      by_cases hc : code = n
      · subst code
        have hSub : (n + 1) - n - 1 = 0 := by omega
        simp [List.range_succ, hSub]
      · have h' : code < n := by omega
        have hrec := ih h'
        calc
          List.range (n + 1) = List.range n ++ [n] := by rw [List.range_succ]
          _ = List.range code ++ [code] ++
                (List.range (n - code - 1)).map (fun i => i + code + 1) ++ [n] := by
                rw [hrec]
          _ = List.range code ++ [code] ++
                ((List.range (n - code - 1)).map (fun i => i + code + 1) ++ [n]) := by
                rw [List.append_assoc, List.append_assoc]
          _ = List.range code ++ [code] ++
                (List.range (n + 1 - code - 1)).map (fun i => i + code + 1) := by
                have hSub : (n + 1) - code - 1 = (n - code - 1) + 1 := by omega
                have hMap : (List.range (n - code - 1)).map (fun i => i + code + 1) ++ [n] =
                    (List.range (n + 1 - code - 1)).map (fun i => i + code + 1) := by
                  rw [hSub, List.range_succ, List.map_append]
                  simp
                  omega
                rw [hMap]

/-- The table lookup returns the rows of the unique symbol with the given code. -/
theorem rowsByCode_eq_rowsOfSymbol {Γ' Γ : Gamma} (interpretation : LanguageInterpretation Γ' Γ)
    (symbol : Γ'.Symbol) :
    rowsByCode interpretation (Presentation.FiniteDomainCSPTable.relationCode Γ' symbol) =
      rowsOfSymbol interpretation symbol := by
  classical
  unfold rowsByCode
  let code := Presentation.FiniteDomainCSPTable.relationCode Γ' symbol
  have hCodeLt : code < Fintype.card Γ'.Symbol := by
    exact Presentation.FiniteDomainCSPTable.relationCode_lt_card Γ' symbol
  have hFound : rowsOfCode interpretation code = rowsOfSymbol interpretation symbol := by
    unfold rowsOfCode
    rw [dif_pos hCodeLt]
    congr 1
    exact Presentation.FiniteDomainCSPTable.relationSymbol_relationIndex Γ' symbol
  -- every other code in the range is skipped
  have hSkip : ∀ {acc : List (Nat × List (Bool × Nat))} {rest : List Nat},
      (∀ d ∈ rest, d ≠ code) →
        rest.foldl (fun acc c => if code = c then rowsOfCode interpretation c else acc) acc = acc := by
    intro acc rest hAll
    induction rest with
    | nil => rfl
    | cons d ds ih =>
        have hd : code ≠ d := fun hEq => hAll d (by simp) hEq.symm
        simp [hd, ih (fun e he => hAll e (by simp [he]))]
  have hSplit : List.range (Fintype.card Γ'.Symbol) =
      List.range code ++ [code] ++
        (List.range (Fintype.card Γ'.Symbol - code - 1)).map (fun i => i + code + 1) :=
    range_split (Fintype.card Γ'.Symbol) code hCodeLt
  rw [hSplit]
  rw [List.foldl_append, List.foldl_append]
  -- the prefix before the match keeps the default
  have hAllBefore : ∀ d ∈ List.range code, d ≠ code := by
    intro d hd
    have hd' : d < code := List.mem_range.mp hd
    omega
  rw [hSkip (rest := List.range code)]
  -- the match
  have hMid : (fun acc c => if code = c then rowsOfCode interpretation c else acc)
      (rowsOfCode interpretation 0) code = rowsOfSymbol interpretation symbol := by
    simp [hFound]
  simp [hMid]
  -- the suffix after the match keeps the rows
  have hAllAfter : ∀ d ∈ (List.range (Fintype.card Γ'.Symbol - code - 1)).map (fun i => i + code + 1),
      d ≠ code := by
    intro d hd
    rcases List.mem_map.mp hd with ⟨i, hi, rfl⟩
    have hi' : i < Fintype.card Γ'.Symbol - code - 1 := List.mem_range.mp hi
    omega
  rw [hSkip (rest := (List.range (Fintype.card Γ'.Symbol - code - 1)).map (fun i => i + code + 1))]
  rfl

/-! ### Code-level instantiation -/

/-- One instantiated target variable, computed from the row position table. -/
def instantiateVarCode (maxArity reference symbolCode : Nat) (vars : List Nat)
    (position : Bool × Nat) : Nat :=
  if position.1 then vars.getD position.2 0
  else reference + Nat.pair (Nat.pair symbolCode (listPairEncodeClamped maxArity vars))
    position.2 + 1

/-- One gadget row instantiated at one source constraint code. -/
def instantiateRow (maxArity : Nat) :
    (Nat × (Nat × List Nat)) × (Nat × List (Bool × Nat)) → Nat × List Nat :=
  fun (input, row) =>
    (row.1, row.2.map (fun position =>
      instantiateVarCode maxArity input.1 input.2.1 input.2.2 position))

/-- The code-level instantiation of one source constraint code. -/
noncomputable def instantiateCode {Γ' Γ : Gamma} (interpretation : LanguageInterpretation Γ' Γ)
    (reference symbolCode : Nat) (vars : List Nat) : List (Nat × List Nat) :=
  (rowsByCode interpretation symbolCode).map (fun row =>
    instantiateRow (maxRelationArity Γ') (reference, (symbolCode, vars), row))

/-- The code-level substitution of a whole formula code. -/
noncomputable def interpretCode {Γ' Γ : Gamma} (interpretation : LanguageInterpretation Γ' Γ)
    (code : List (Nat × List Nat)) : List (Nat × List Nat) :=
  let reference := codeMaxVar code
  code.flatMap (fun constraint =>
    instantiateCode interpretation reference constraint.1 constraint.2)

/-! ### Agreement of the code-level substitution -/

/-- The code-level instantiated variable agrees with the semantic one. -/
theorem instantiateVarCode_eq_instantiateVar {Γ' Γ : Gamma}
    (interpretation : LanguageInterpretation Γ' Γ)
    {constraint : Constraint Γ'} (reference : Nat) {d : Constraint Γ}
    (dMember : d ∈ (interpretation.gadgetOf constraint.symbol).formula)
    (j : Fin (Γ.relationOf d.symbol).arity) :
    instantiateVarCode (maxRelationArity Γ') reference
        (Presentation.FiniteDomainCSPTable.relationCode Γ' constraint.symbol)
        constraint.varsList
        (gadgetRow (interpretation.gadgetOf constraint.symbol) d).2[j.val] =
      instantiateVar interpretation reference constraint (d.vars j) := by
  classical
  let gadget := interpretation.gadgetOf constraint.symbol
  unfold instantiateVarCode gadgetRow instantiateVar freshVar constraintKey
  by_cases hMem : d.vars j ∈ Set.range gadget.outputs
  · have hEntry : (List.ofFn (fun k : Fin (Γ.relationOf d.symbol).arity =>
        if h : d.vars k ∈ Set.range gadget.outputs then
          (true, (Classical.choose h).val)
        else (false, d.vars k)))[j.val] =
        (true, (Classical.choose hMem).val) := by
      rw [List.getElem_ofFn]
      simp [hMem]
    have hSelect : (fun p : Bool × Nat => if p.1 then constraint.varsList.getD p.2 0 else
        reference + Nat.pair (Nat.pair (Presentation.FiniteDomainCSPTable.relationCode Γ' constraint.symbol)
          (listPairEncodeClamped (maxRelationArity Γ') constraint.varsList)) p.2 + 1)
          (true, (Classical.choose hMem).val) = constraint.varsList.getD (Classical.choose hMem).val 0 := by
      simp
    have hChoose : (Classical.choose hMem).val < constraint.varsList.length := by
      have hlt : (Classical.choose hMem).val < (Γ'.relationOf constraint.symbol).arity :=
        (Classical.choose hMem).isLt
      simpa using hlt
    have hGetD : constraint.varsList.getD (Classical.choose hMem).val 0 =
        constraint.vars (Classical.choose hMem) := by
      rw [List.getD_eq_getElem constraint.varsList 0 hChoose]
      rw [Constraint.varsList]
      simp
    rw [dif_pos hMem]
    rw [hSelect, hGetD]
  · have hEntry : (List.ofFn (fun k : Fin (Γ.relationOf d.symbol).arity =>
        if h : d.vars k ∈ Set.range gadget.outputs then
          (true, (Classical.choose h).val)
        else (false, d.vars k)))[j.val] = (false, d.vars j) := by
      rw [List.getElem_ofFn]
      simp [hMem]
    have hCode : listPairEncodeClamped (maxRelationArity Γ') constraint.varsList =
        listPairEncode constraint.varsList :=
      listPairEncodeClamped_eq_listPairEncode
        (varsList_length_le_maxRelationArity constraint)
    have hSelect : (fun p : Bool × Nat => if p.1 then constraint.varsList.getD p.2 0 else
        reference + Nat.pair (Nat.pair (Presentation.FiniteDomainCSPTable.relationCode Γ' constraint.symbol)
          (listPairEncodeClamped (maxRelationArity Γ') constraint.varsList)) p.2 + 1)
        (false, d.vars j) =
        reference + Nat.pair (Nat.pair (Presentation.FiniteDomainCSPTable.relationCode Γ' constraint.symbol)
          (listPairEncode constraint.varsList)) (d.vars j) + 1 := by
      simp [hCode]
    rw [dif_neg hMem]
    rw [hSelect]
    rfl

/-- One gadget row's code equals the code of its instantiated constraint. -/
theorem instantiateRow_eq_constraintCode {Γ' Γ : Gamma}
    (interpretation : LanguageInterpretation Γ' Γ)
    {constraint : Constraint Γ'} (reference : Nat) {d : Constraint Γ}
    (dMember : d ∈ (interpretation.gadgetOf constraint.symbol).formula) :
    instantiateRow (maxRelationArity Γ') (reference,
        (Presentation.FiniteDomainCSPTable.relationCode Γ' constraint.symbol,
        constraint.varsList), gadgetRow (interpretation.gadgetOf constraint.symbol) d) =
      constraintCode { symbol := d.symbol
        vars := fun j => instantiateVar interpretation reference constraint (d.vars j) } := by
  classical
  unfold instantiateRow
  apply Prod.ext
  · rfl
  · -- both variable lists agree entrywise
    have hMapOfFn :
        (List.ofFn (fun k : Fin (Γ.relationOf d.symbol).arity =>
          if h : d.vars k ∈ Set.range (interpretation.gadgetOf constraint.symbol).outputs then
            (true, (Classical.choose h).val)
          else (false, d.vars k))).map (fun position =>
            instantiateVarCode (maxRelationArity Γ') reference
              (Presentation.FiniteDomainCSPTable.relationCode Γ' constraint.symbol)
              constraint.varsList position) =
          List.ofFn (fun k : Fin (Γ.relationOf d.symbol).arity =>
            instantiateVarCode (maxRelationArity Γ') reference
              (Presentation.FiniteDomainCSPTable.relationCode Γ' constraint.symbol)
              constraint.varsList
              (if h : d.vars k ∈ Set.range (interpretation.gadgetOf constraint.symbol).outputs then
                (true, (Classical.choose h).val)
              else (false, d.vars k))) := by
      rw [List.map_ofFn]
    rw [hMapOfFn]
    -- the semantic varsList is the same ofFn of the semantic instantiation
    have hVarsList : Constraint.varsList
        { symbol := d.symbol
          vars := fun j => instantiateVar interpretation reference constraint (d.vars j) } =
        List.ofFn (fun j : Fin (Γ.relationOf d.symbol).arity =>
          instantiateVar interpretation reference constraint (d.vars j)) := by
      rfl
    rw [hVarsList]
    congr 1
    funext k
    exact instantiateVarCode_eq_instantiateVar interpretation (constraint := constraint) reference
      (d := d) dMember k

/-- The code-level instantiation agrees with the semantic one, per constraint. -/
theorem instantiateCode_eq_formulaCode {Γ' Γ : Gamma}
    (interpretation : LanguageInterpretation Γ' Γ)
    (constraint : Constraint Γ') (reference : Nat) :
    instantiateCode interpretation reference
        (Presentation.FiniteDomainCSPTable.relationCode Γ' constraint.symbol)
        constraint.varsList =
      formulaCode Γ (instantiate interpretation reference constraint) := by
  classical
  unfold instantiateCode
  rw [rowsByCode_eq_rowsOfSymbol]
  unfold rowsOfSymbol formulaCode
  apply List.map_congr_left
  intro d dMember
  exact instantiateRow_eq_constraintCode interpretation (constraint := constraint) reference
    (d := d) dMember

/-- The code-level substitution agrees with the semantic substitution on every formula. -/
theorem interpretCode_eq_formulaCode {Γ' Γ : Gamma}
    (interpretation : LanguageInterpretation Γ' Γ) (formula : Formula Γ') :
    interpretCode interpretation (formulaCode Γ' formula) =
      formulaCode Γ (interpret interpretation formula) := by
  classical
  unfold interpretCode interpret formulaCode
  have hReference : codeMaxVar (formula.map constraintCode) = Formula.maxVar formula := by
    exact codeMaxVar_eq_formulaMaxVar formula
  rw [hReference]
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro constraint _
  exact instantiateCode_eq_formulaCode interpretation constraint (Formula.maxVar formula)

/-! ### Direct-TM compilation of the code-level substitution -/

/-- The clamped list code is direct-TM polynomial time. -/
theorem listPairEncodeClamped_tmPolyTime (maxArity : Nat) :
    TMPolyTimeMap (EncodedType.list EncodedType.nat) EncodedType.nat
      (listPairEncodeClamped maxArity) := by
  classical
  unfold listPairEncodeClamped
  let X := EncodedType.list EncodedType.nat
  let Item := EncodedType.prod EncodedType.nat EncodedType.nat
  let E := 2 ^ (maxArity + 1)
  -- threshold = (varsMaxCode vars + 2) ^ E
  have hVarsMax : TMPolyTimeMap X EncodedType.nat varsMaxCode := varsMaxCode_tmPolyTime
  have hBase : TMPolyTimeMap X EncodedType.nat (fun vars : List Nat => varsMaxCode vars + 2) := by
    have hAdd := ComplexityReduction.nat_add_const_tm_polytime 2
    have hComp := TMPolyTimeMap.comp hAdd hVarsMax
    simpa [Function.comp] using hComp
  have hThreshold : TMPolyTimeMap X EncodedType.nat
      (fun vars : List Nat => (varsMaxCode vars + 2) ^ E) := by
    have hPoly := ComplexityReduction.nat_poly_monomial_tm_polytime E 1 0
    have hComp := TMPolyTimeMap.comp hPoly hBase
    simpa [Function.comp] using hComp
  -- reverse the variables
  have hReversed : TMPolyTimeMap X X List.reverse := reverse_tmPolyTime EncodedType.nat
  -- attach the threshold to each reversed variable
  have hAttached := Program.contextListMapExecutable_tmPolyTime EncodedType.nat EncodedType.nat
  have hAttachedInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat X)
      (fun vars : List Nat => ((varsMaxCode vars + 2) ^ E, vars.reverse)) :=
    TMPolyTimeMap.prod_mk hThreshold hReversed
  have hAttachedComp := TMPolyTimeMap.comp hAttached hAttachedInput
  -- the clamped fold step
  let step (p : Nat × (Nat × Nat)) : Nat :=
    if p.1 ≤ p.2.1 then Nat.pair p.2.2 p.1 + 1 else p.1
  have hStep : TMPolyTimeMap (EncodedType.prod EncodedType.nat Item) EncodedType.nat step := by
    let Input := EncodedType.prod EncodedType.nat Item
    have hAcc : TMPolyTimeMap Input EncodedType.nat (fun p : Nat × (Nat × Nat) => p.1) := by
      simpa [Input, Item] using TMPolyTimeMap.fst EncodedType.nat Item
    have hThr : TMPolyTimeMap Input EncodedType.nat (fun p : Nat × (Nat × Nat) => p.2.1) := by
      have h := TMPolyTimeMap.comp (TMPolyTimeMap.fst EncodedType.nat EncodedType.nat)
        (TMPolyTimeMap.snd EncodedType.nat Item)
      simpa [Input, Item, Function.comp] using h
    have hVal : TMPolyTimeMap Input EncodedType.nat (fun p : Nat × (Nat × Nat) => p.2.2) := by
      have h := TMPolyTimeMap.comp (TMPolyTimeMap.snd EncodedType.nat EncodedType.nat)
        (TMPolyTimeMap.snd EncodedType.nat Item)
      simpa [Input, Item, Function.comp] using h
    have hSuccThr : TMPolyTimeMap Input EncodedType.nat (fun p : Nat × (Nat × Nat) => p.2.1 + 1) := by
      have hAdd := ComplexityReduction.nat_add_const_tm_polytime 1
      have hComp := TMPolyTimeMap.comp hAdd hThr
      simpa [Function.comp] using hComp
    have hLtInput : TMPolyTimeMap Input (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × (Nat × Nat) => (p.1, p.2.1 + 1)) :=
      TMPolyTimeMap.prod_mk hAcc hSuccThr
    have hLe : TMPolyTimeMap Input EncodedType.bool
        (fun p : Nat × (Nat × Nat) => ComplexityReduction.natLtBool (p.1, p.2.1 + 1)) := by
      have hComp := TMPolyTimeMap.comp ComplexityReduction.natLtBool_tm_polytime hLtInput
      simpa [Function.comp] using hComp
    -- pair v acc + 1
    have hPairInput : TMPolyTimeMap Input (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × (Nat × Nat) => (p.2.2, p.1)) :=
      TMPolyTimeMap.prod_mk hVal hAcc
    have hPair := TMPolyTimeMap.comp ComplexityReduction.natPair_tm_polytime hPairInput
    have hPairAdd : TMPolyTimeMap Input EncodedType.nat
        (fun p : Nat × (Nat × Nat) => Nat.pair p.2.2 p.1 + 1) := by
      have hAdd := ComplexityReduction.nat_add_const_tm_polytime 1
      have hComp := TMPolyTimeMap.comp hAdd hPair
      simpa [Function.comp] using hComp
    -- dispatch: if acc ≤ thr then pair v acc + 1 else acc
    have hFlagged : TMPolyTimeMap Input
        (EncodedType.prod EncodedType.bool (EncodedType.prod EncodedType.nat EncodedType.nat))
        (fun p : Nat × (Nat × Nat) =>
          (ComplexityReduction.natLtBool (p.1, p.2.1 + 1), (Nat.pair p.2.2 p.1 + 1, p.1))) :=
      TMPolyTimeMap.prod_mk hLe (TMPolyTimeMap.prod_mk hPairAdd hAcc)
    have hDispatch := ComplexityReduction.boolProduct_dispatch_tm_polytime
      (EncodedType.prod EncodedType.nat EncodedType.nat) EncodedType.nat
      (fFalse := fun p : Nat × Nat => p.2) (fTrue := fun p : Nat × Nat => p.1)
      (TMPolyTimeMap.snd EncodedType.nat EncodedType.nat)
      (TMPolyTimeMap.fst EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hDispatch hFlagged
    simpa [step, Function.comp] using hComp
  rcases hStep with ⟨stepTM⟩
  -- the explicit clamped bound: B(N) = ((N+2)^E + N + 2)^2 + 2
  let bound : Polynomial Nat :=
    ((Polynomial.X + Polynomial.C 2) ^ E + Polynomial.X + Polynomial.C 2) ^ 2 + Polynomial.C 2
  have hFold : TMPolyTimeMap (EncodedType.list Item) EncodedType.nat
      (fun xs : List Item.Carrier => xs.foldl step 0) := by
    refine TMPolyTimeMap.list_foldl_typed_bounded
      Item EncodedType.nat step (0 : Nat) stepTM bound ?_ ?_
    · intro source
      simp [bound, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X]
      omega
    · intro source accumulator item accumulatorBound itemBound
      let N := (EncodedType.list Item).inputSize source
      have hThrLe : item.1 ≤ N := by
        have hsub : Item.inputSize item ≤ N := by simpa [N] using itemBound
        rw [EncodedType.inputSize_prod] at hsub
        omega
      have hValLe : item.2 ≤ N := by
        have hsub : Item.inputSize item ≤ N := by simpa [N] using itemBound
        rw [EncodedType.inputSize_prod] at hsub
        omega
      by_cases hLe : accumulator ≤ item.1
      · -- the clamped branch: pair item.2 accumulator + 1
        have hPair : Nat.pair item.2 accumulator + 1 ≤ (Nat.max item.2 accumulator + 1) ^ 2 :=
          Nat.pair_lt_max_add_one_sq item.2 accumulator
        have hAccN : accumulator ≤ N := by
          exact Nat.le_trans hLe (by simpa [N] using hThrLe)
        have hOut : Nat.pair item.2 accumulator + 1 ≤ (2 * N + 1) ^ 2 := by
          have hsum : item.2 + accumulator + 1 ≤ 2 * N + 1 := by omega
          have hpow : (item.2 + accumulator + 1) ^ 2 ≤ (2 * N + 1) ^ 2 :=
            Nat.pow_le_pow_left hsum 2
          omega
        have hB : (2 * N + 1) ^ 2 ≤ bound.eval N := by
          have hEne0 : E ≠ 0 := by
            unfold E
            exact Nat.pow_ne_zero _ (by omega : 2 ≠ 0)
          have hBaseLe : N + 2 ≤ (N + 2) ^ E := le_self_pow (by omega) hEne0
          have hTwo : 2 * N + 1 ≤ (N + 2) ^ E + N + 2 := by omega
          have hSqB : (2 * N + 1) ^ 2 ≤ ((N + 2) ^ E + N + 2) ^ 2 :=
            Nat.pow_le_pow_left hTwo 2
          have hBound : ((N + 2) ^ E + N + 2) ^ 2 ≤ bound.eval N := by
            simp [bound, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X]
            omega
          exact Nat.le_trans hSqB hBound
        -- inputSize of the output nat is the value plus one
        have hSize : (EncodedType.nat).inputSize (Nat.pair item.2 accumulator + 1) =
            Nat.pair item.2 accumulator + 2 := by
          simp [EncodedType.inputSize_nat]
        rw [hSize]
        omega
      · -- the unclamped branch keeps the accumulator
        have hSize : (EncodedType.nat).inputSize accumulator = accumulator + 1 := by
          simp [EncodedType.inputSize_nat]
        rw [hSize]
        omega
  have hComp := TMPolyTimeMap.comp hFold hAttachedComp
  -- the composed map is exactly the clamped list code
  simpa [listPairEncodeClamped, step, Function.comp] using hComp

/-! ### Direct-TM compilation of the interpretation -/

/-- The finite code-table lookup is direct-TM polynomial time. -/
theorem rowsByCode_tmPolyTime {Γ' Γ : Gamma} (interpretation : LanguageInterpretation Γ' Γ) :
    TMPolyTimeMap EncodedType.nat
      (EncodedType.list (EncodedType.prod EncodedType.nat
        (EncodedType.list (EncodedType.prod EncodedType.bool EncodedType.nat))))
      (rowsByCode interpretation) := by
  let Row := EncodedType.prod EncodedType.nat
    (EncodedType.list (EncodedType.prod EncodedType.bool EncodedType.nat))
  let Table := EncodedType.list Row
  let rows := rowsOfCode interpretation
  have hLookup : ∀ codes : List Nat, TMPolyTimeMap EncodedType.nat Table
      (fun code : Nat => codes.foldl
        (fun acc c => if code = c then rows c else acc) (rows 0)) := by
    intro codes
    induction codes with
    | nil =>
        simpa using (TMPolyTimeMap.const EncodedType.nat Table (rows 0) :
          TMPolyTimeMap EncodedType.nat Table (fun _ : Nat => rows 0))
    | cons c cs ih =>
        have hEq : TMPolyTimeMap EncodedType.nat EncodedType.bool
            (fun code : Nat => decide (code = c)) := by
          have hInput : TMPolyTimeMap EncodedType.nat
              (EncodedType.prod EncodedType.nat EncodedType.nat)
              (fun code : Nat => (code, c)) :=
            TMPolyTimeMap.prod_mk (TMPolyTimeMap.id EncodedType.nat)
              (TMPolyTimeMap.const EncodedType.nat EncodedType.nat c)
          have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hInput
          simpa [Function.comp] using hComp
        have hConst : TMPolyTimeMap EncodedType.nat Table
            (fun _ : Nat => rows c) :=
          TMPolyTimeMap.const EncodedType.nat Table (rows c)
        have hFlagged : TMPolyTimeMap EncodedType.nat
            (EncodedType.prod EncodedType.bool EncodedType.nat)
            (fun code : Nat => (decide (code = c), code)) :=
          TMPolyTimeMap.prod_mk hEq (TMPolyTimeMap.id EncodedType.nat)
        have hDispatch := ComplexityReduction.boolProduct_dispatch_tm_polytime
          EncodedType.nat Table
          (fFalse := fun code : Nat => cs.foldl
            (fun acc d => if code = d then rows d else acc) (rows 0))
          (fTrue := fun _ : Nat => rows c)
          ih hConst
        have hComp := TMPolyTimeMap.comp hDispatch hFlagged
        simpa [List.foldl_cons, Function.comp] using hComp
  simpa [rowsByCode, rows] using hLookup (List.range (Fintype.card Γ'.Symbol))

/-- The per-position instantiation step is direct-TM polynomial time. -/
theorem instantiateVarCode_tmPolyTime (maxArity : Nat) :
    TMPolyTimeMap
      (EncodedType.prod (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat)))
        (EncodedType.prod EncodedType.bool EncodedType.nat))
      EncodedType.nat
      (fun p : (Nat × (Nat × List Nat)) × (Bool × Nat) =>
        instantiateVarCode maxArity p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  let Input := EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
  let Position := EncodedType.prod EncodedType.bool EncodedType.nat
  let X := EncodedType.prod Input Position
  have hReference : TMPolyTimeMap X EncodedType.nat
      (fun p : (Nat × (Nat × List Nat)) × (Bool × Nat) => p.1.1) := by
    have h := TMPolyTimeMap.comp (TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))) (TMPolyTimeMap.fst Input Position)
    simpa [X, Input, Function.comp] using h
  have hSymbolCode : TMPolyTimeMap X EncodedType.nat
      (fun p : (Nat × (Nat × List Nat)) × (Bool × Nat) => p.1.2.1) := by
    have h1 := TMPolyTimeMap.comp (TMPolyTimeMap.fst EncodedType.nat (EncodedType.list EncodedType.nat))
      (TMPolyTimeMap.snd Input Position)
    have h2 := TMPolyTimeMap.comp h1 (TMPolyTimeMap.fst Input Position)
    simpa [X, Input, Function.comp] using h2
  have hVars : TMPolyTimeMap X (EncodedType.list EncodedType.nat)
      (fun p : (Nat × (Nat × List Nat)) × (Bool × Nat) => p.1.2.2) := by
    have h1 := TMPolyTimeMap.comp (TMPolyTimeMap.snd EncodedType.nat (EncodedType.list EncodedType.nat))
      (TMPolyTimeMap.snd Input Position)
    have h2 := TMPolyTimeMap.comp h1 (TMPolyTimeMap.fst Input Position)
    simpa [X, Input, Function.comp] using h2
  have hFlag : TMPolyTimeMap X EncodedType.bool
      (fun p : (Nat × (Nat × List Nat)) × (Bool × Nat) => p.2.1) := by
    have h := TMPolyTimeMap.comp (TMPolyTimeMap.fst EncodedType.bool EncodedType.nat)
      (TMPolyTimeMap.snd Input Position)
    simpa [X, Input, Function.comp] using h
  have hValue : TMPolyTimeMap X EncodedType.nat
      (fun p : (Nat × (Nat × List Nat)) × (Bool × Nat) => p.2.2) := by
    have h := TMPolyTimeMap.comp (TMPolyTimeMap.snd EncodedType.bool EncodedType.nat)
      (TMPolyTimeMap.snd Input Position)
    simpa [X, Input, Function.comp] using h
  -- getD branch: vars.getD value 0
  have hGetDInput : TMPolyTimeMap X (EncodedType.prod (EncodedType.list EncodedType.nat) EncodedType.nat)
      (fun p : (Nat × (Nat × List Nat)) × (Bool × Nat) => (p.1.2.2, p.2.2)) :=
    TMPolyTimeMap.prod_mk hVars hValue
  have hGetD := TMPolyTimeMap.comp (Karp21.EncodedListLookup.getD_tm_polytime EncodedType.nat 0) hGetDInput
  -- listPairEncodeClamped vars
  have hListPair := TMPolyTimeMap.comp (listPairEncodeClamped_tmPolyTime maxArity) hVars
  -- fresh branch: reference + pair (pair symbolCode (listPairEncodeClamped vars)) value + 1
  have hPairInnerInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : (Nat × (Nat × List Nat)) × (Bool × Nat) =>
        (p.1.2.1, listPairEncodeClamped maxArity p.1.2.2)) :=
    TMPolyTimeMap.prod_mk hSymbolCode hListPair
  have hPairInner := TMPolyTimeMap.comp ComplexityReduction.natPair_tm_polytime hPairInnerInput
  have hPairOuterInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : (Nat × (Nat × List Nat)) × (Bool × Nat) =>
        (Nat.pair p.1.2.1 (listPairEncodeClamped maxArity p.1.2.2), p.2.2)) :=
    TMPolyTimeMap.prod_mk hPairInner hValue
  have hPairOuter := TMPolyTimeMap.comp ComplexityReduction.natPair_tm_polytime hPairOuterInput
  have hAddReference : TMPolyTimeMap X EncodedType.nat
      (fun p : (Nat × (Nat × List Nat)) × (Bool × Nat) =>
        Nat.pair (Nat.pair p.1.2.1 (listPairEncodeClamped maxArity p.1.2.2)) p.2.2 + p.1.1) := by
    have hAddInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : (Nat × (Nat × List Nat)) × (Bool × Nat) =>
          (p.1.1, Nat.pair (Nat.pair p.1.2.1 (listPairEncodeClamped maxArity p.1.2.2)) p.2.2)) :=
      TMPolyTimeMap.prod_mk hReference hPairOuter
    have hAdd := TMPolyTimeMap.comp ComplexityReduction.natAdd_tm_polytime hAddInput
    simpa [Function.comp] using hAdd
  have hFresh := TMPolyTimeMap.comp (ComplexityReduction.nat_add_const_tm_polytime 1) hAddReference
  -- dispatch on the flag
  have hFlagged : TMPolyTimeMap X (EncodedType.prod EncodedType.bool
      (EncodedType.prod EncodedType.nat EncodedType.nat))
      (fun p : (Nat × (Nat × List Nat)) × (Bool × Nat) =>
        (p.2.1, (p.1.2.2.getD p.2.2 0,
          Nat.pair (Nat.pair p.1.2.1 (listPairEncodeClamped maxArity p.1.2.2)) p.2.2 + p.1.1 + 1))) :=
    TMPolyTimeMap.prod_mk hFlag (TMPolyTimeMap.prod_mk hGetD hFresh)
  have hDispatch := ComplexityReduction.boolProduct_dispatch_tm_polytime
    (EncodedType.prod EncodedType.nat EncodedType.nat) EncodedType.nat
    (fFalse := fun p : Nat × Nat => p.1) (fTrue := fun p : Nat × Nat => p.2)
    (TMPolyTimeMap.fst EncodedType.nat EncodedType.nat)
    (TMPolyTimeMap.snd EncodedType.nat EncodedType.nat)
  have hComp := TMPolyTimeMap.comp hDispatch hFlagged
  simpa [instantiateVarCode, Function.comp] using hComp

/-- One row instantiation is direct-TM polynomial time. -/
theorem instantiateRow_tmPolyTime (maxArity : Nat) :
    TMPolyTimeMap
      (EncodedType.prod (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat)))
        (EncodedType.prod EncodedType.nat
          (EncodedType.list (EncodedType.prod EncodedType.bool EncodedType.nat))))
      (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
      (fun p : (Nat × (Nat × List Nat)) × (Nat × List (Bool × Nat)) =>
        instantiateRow maxArity p) := by
  let Input := EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
  let Row := EncodedType.prod EncodedType.nat
    (EncodedType.list (EncodedType.prod EncodedType.bool EncodedType.nat))
  let X := EncodedType.prod Input Row
  let Position := EncodedType.prod EncodedType.bool EncodedType.nat
  -- attach the input as context to the positions of the row
  have hAttached := Program.contextListMapExecutable_tmPolyTime Input Position
  have hAttachedInput : TMPolyTimeMap X (EncodedType.prod Input
      (EncodedType.list Position))
      (fun p : (Nat × (Nat × List Nat)) × (Nat × List (Bool × Nat)) =>
        (p.1, p.2.2)) := by
    have hFst : TMPolyTimeMap X Input (fun p : (Nat × (Nat × List Nat)) × (Nat × List (Bool × Nat)) => p.1) := by
      simpa [X, Input] using TMPolyTimeMap.fst Input Row
    have hRowSnd : TMPolyTimeMap X (EncodedType.list Position)
        (fun p : (Nat × (Nat × List Nat)) × (Nat × List (Bool × Nat)) => p.2.2) := by
      have h := TMPolyTimeMap.comp (TMPolyTimeMap.snd EncodedType.nat (EncodedType.list Position))
        (TMPolyTimeMap.snd Input Row)
      simpa [X, Input, Function.comp] using h
    exact TMPolyTimeMap.prod_mk hFst hRowSnd
  have hAttachedComp := TMPolyTimeMap.comp hAttached hAttachedInput
  have hPerPosition : TMPolyTimeMap (EncodedType.prod Input Position) EncodedType.nat
      (fun p : (Nat × (Nat × List Nat)) × (Bool × Nat) =>
        instantiateVarCode maxArity p.1.1 p.1.2.1 p.1.2.2 p.2) := by
    simpa [Input, Position] using instantiateVarCode_tmPolyTime maxArity
  have hMapped := TMPolyTimeMap.list_map hPerPosition
  have hMappedComp := TMPolyTimeMap.comp hMapped hAttachedComp
  -- pair with the target relation code of the row
  have hCode : TMPolyTimeMap X EncodedType.nat
      (fun p : (Nat × (Nat × List Nat)) × (Nat × List (Bool × Nat)) => p.2.1) := by
    have h := TMPolyTimeMap.comp (TMPolyTimeMap.fst EncodedType.nat (EncodedType.list Position))
      (TMPolyTimeMap.snd Input Row)
    simpa [X, Input, Function.comp] using h
  have hFinal := TMPolyTimeMap.prod_mk hCode hMappedComp
  simpa [instantiateRow, Function.comp] using hFinal

/-- The code-level instantiation of one constraint is direct-TM polynomial time. -/
theorem instantiateCode_tmPolyTime {Γ' Γ : Gamma}
    (interpretation : LanguageInterpretation Γ' Γ) :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat)))
      (EncodedType.list (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat)))
      (fun input : Nat × (Nat × List Nat) =>
        instantiateCode interpretation input.1 input.2.1 input.2.2) := by
  let Input := EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
  let Row := EncodedType.prod EncodedType.nat
    (EncodedType.list (EncodedType.prod EncodedType.bool EncodedType.nat))
  let Table := EncodedType.list Row
  let Code := EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat)
  -- symbol code from the input
  have hSymbol : TMPolyTimeMap Input EncodedType.nat (fun input : Nat × (Nat × List Nat) => input.2.1) := by
    have h := TMPolyTimeMap.comp (TMPolyTimeMap.fst EncodedType.nat (EncodedType.list EncodedType.nat))
      (TMPolyTimeMap.snd EncodedType.nat (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat)))
    simpa [Input, Function.comp] using h
  have hRows := TMPolyTimeMap.comp (rowsByCode_tmPolyTime interpretation) hSymbol
  -- attach the input as context to the rows
  have hAttached := Program.contextListMapExecutable_tmPolyTime Input Row
  have hPair : TMPolyTimeMap Input (EncodedType.prod Input Table)
      (fun input : Nat × (Nat × List Nat) => (input, rowsByCode interpretation input.2.1)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id Input) hRows
  have hAttachedComp := TMPolyTimeMap.comp hAttached hPair
  have hPerRow : TMPolyTimeMap (EncodedType.prod Input Row) Code
      (fun p : (Nat × (Nat × List Nat)) × (Nat × List (Bool × Nat)) => instantiateRow
        (maxRelationArity Γ') p) := by
    simpa [Input, Row, Code] using instantiateRow_tmPolyTime (maxRelationArity Γ')
  have hMapped := TMPolyTimeMap.list_map hPerRow
  have hComp := TMPolyTimeMap.comp hMapped hAttachedComp
  simpa [instantiateCode, rowsByCode, Function.comp] using hComp

/-- The code-level substitution is direct-TM polynomial time. -/
theorem interpretCode_tmPolyTime {Γ' Γ : Gamma}
    (interpretation : LanguageInterpretation Γ' Γ) :
    TMPolyTimeMap
      (EncodedType.list (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat)))
      (EncodedType.list (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat)))
      (interpretCode interpretation) := by
  let Code := EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat)
  let FormulaCode := EncodedType.list Code
  -- reference
  have hReference : TMPolyTimeMap FormulaCode EncodedType.nat codeMaxVar := by
    simpa [FormulaCode, Code] using codeMaxVar_tmPolyTime
  have hPaired : TMPolyTimeMap FormulaCode (EncodedType.prod EncodedType.nat FormulaCode)
      (fun code : List (Nat × List Nat) => (codeMaxVar code, code)) :=
    TMPolyTimeMap.prod_mk hReference (TMPolyTimeMap.id FormulaCode)
  -- per-constraint instantiation with the reference as context
  have hAttached := Program.contextListMapExecutable_tmPolyTime EncodedType.nat Code
  have hAttachedComp := TMPolyTimeMap.comp hAttached hPaired
  have hPerConstraint : TMPolyTimeMap (EncodedType.prod EncodedType.nat Code)
      (EncodedType.list (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat)))
      (fun p : Nat × (Nat × List Nat) => instantiateCode interpretation p.1 p.2.1 p.2.2) := by
    simpa [Code] using instantiateCode_tmPolyTime interpretation
  have hMapped := TMPolyTimeMap.list_map hPerConstraint
  have hMappedComp := TMPolyTimeMap.comp hMapped hAttachedComp
  -- flatten
  have hFlatten := Program.listFlatten_tmPolyTime Code
  have hComp := TMPolyTimeMap.comp hFlatten hMappedComp
  simpa [interpretCode, Function.comp] using hComp

/-! ### The automatic transport -/

/-- Every pp-interpretation is realizable by a direct-TM polynomial-time substitution. -/
theorem interpretation_tmPolyTime {Γ' Γ : Gamma}
    (interpretation : LanguageInterpretation Γ' Γ) :
    TMPolyTimeMap (Presentation.FiniteDomainCSPTable.encodedType Γ')
      (Presentation.FiniteDomainCSPTable.encodedType Γ)
      (interpret interpretation) := by
  classical
  have hFormulaCode : TMPolyTimeMap (Presentation.FiniteDomainCSPTable.encodedType Γ')
      Presentation.FiniteDomainCSPTable.formulaCodeEncodedType
      (fun formula => formulaCode Γ' formula) := by
    exact TMPolyTimeMap.of_encodingEquiv (Presentation.FiniteDomainCSPTable.encodedType Γ')
      Presentation.FiniteDomainCSPTable.formulaCodeEncodedType
      (fun formula => formulaCode Γ' formula) (Equiv.refl _) (by intro formula; rfl)
  have hCode : TMPolyTimeMap (Presentation.FiniteDomainCSPTable.encodedType Γ')
      Presentation.FiniteDomainCSPTable.formulaCodeEncodedType
      (fun formula => interpretCode interpretation (formulaCode Γ' formula)) := by
    have hComp := TMPolyTimeMap.comp (interpretCode_tmPolyTime interpretation) hFormulaCode
    simpa [Function.comp] using hComp
  exact Presentation.FiniteDomainCSPTable.formula_tmPolyTime_of_code hCode
    (interpretCode_eq_formulaCode interpretation)

/-- The substitution of a pp-interpretation is a certified reduction, automatically. -/
noncomputable def certifiedReduction_of_interpretation_auto {Γ' Γ : Gamma}
    (interpretation : LanguageInterpretation Γ' Γ) :
    CertifiedReduction (cspOf Γ') (cspOf Γ) := by
  let program : PolyProg (cspOf Γ').representation (cspOf Γ).representation :=
    .atom (Primitive.ofTMPolyTime (interpret interpretation)
      (interpretation_tmPolyTime interpretation))
  refine ⟨program, ?_⟩
  intro formula
  have hrun : program.run formula = interpret interpretation formula := rfl
  simpa [cspOf_accepts, hrun] using
    (interpret_satisfiable_iff interpretation formula).symm

/-- NP-hardness transports along a pp-interpretation, automatically. -/
theorem nPHard_of_interpretation_auto {Γ' Γ : Gamma}
    (interpretation : LanguageInterpretation Γ' Γ)
    (coreNPHard : NativeTMNPHard (cspOf Γ')) :
    NativeTMNPHard (cspOf Γ) :=
  NativeTMNPHard.alongPath coreNPHard
    (CertifiedPath.step (certifiedReduction_of_interpretation_auto interpretation))

end

end Hardness
end BooleanCSP
end Domain
end ComplexityReduction
