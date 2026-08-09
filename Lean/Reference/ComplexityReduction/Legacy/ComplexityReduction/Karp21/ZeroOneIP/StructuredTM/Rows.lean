import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ZeroOneIP.StructuredTM

namespace ComplexityReduction
namespace Karp21
namespace ZeroOneIP

open ComplexityReduction.Combinatorics

/-!
Row-level semantic target for the direct structured 0-1-IP route.

The checked TM runner will compute rows from the bounded input size and the
three-slot clause prefix parser already used by the Chromatic Number route.
This file pins down the exact row function and proves it agrees with the
textbook `clauseRow` on the `SAT.ThreeCNF` length invariant.
-/

def clauseRowFrom (start : Nat) (n : Nat) : SAT.Clause → List Int
  | [] => zeroRow n
  | l :: ls => addRows (literalRowFrom start n l) (clauseRowFrom start n ls)

theorem clauseRowFrom_zero (n : Nat) (c : SAT.Clause) :
    clauseRowFrom 0 n c = clauseRow n c := by
  induction c with
  | nil =>
      simp [clauseRowFrom, clauseRow]
  | cons l ls ih =>
      simp [clauseRowFrom, clauseRow, literalRow, ih]

def defaultLiteralForIPRows : SAT.Literal :=
  ⟨0, false⟩

def clausePrefixStateEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod literalStructuredEncodedType
      (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType))

abbrev ClausePrefixState := Nat × (SAT.Literal × (SAT.Literal × SAT.Literal))

def clausePrefixInit : ClausePrefixState :=
  ((0 : Nat),
    (defaultLiteralForIPRows,
      (defaultLiteralForIPRows, defaultLiteralForIPRows)))

def clausePrefixStep (p : ClausePrefixState × SAT.Literal) : ClausePrefixState :=
  if p.1.1 = (0 : Nat) then
    ((1 : Nat), (p.2, (p.1.2.2.1, p.1.2.2.2)))
  else if p.1.1 = (1 : Nat) then
    ((2 : Nat), (p.1.2.1, (p.2, p.1.2.2.2)))
  else if p.1.1 = (2 : Nat) then
    ((3 : Nat), (p.1.2.1, (p.1.2.2.1, p.2)))
  else
    p.1

def clausePrefixFromClause (c : SAT.Clause) : ClausePrefixState :=
  c.foldl (fun acc lit => clausePrefixStep (acc, lit)) clausePrefixInit

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
      ((1 : Nat), (l₀, (defaultLiteralForIPRows, defaultLiteralForIPRows))) := by
  simp [clausePrefixFromClause, clausePrefixStep, clausePrefixInit]

theorem clausePrefixFromClause_pair (l₀ l₁ : SAT.Literal) :
    clausePrefixFromClause [l₀, l₁] =
      ((2 : Nat), (l₀, (l₁, defaultLiteralForIPRows))) := by
  simp [clausePrefixFromClause, clausePrefixStep, clausePrefixInit]

theorem clausePrefixFromClause_three_or_more
    (l₀ l₁ l₂ : SAT.Literal) (rest : SAT.Clause) :
    clausePrefixFromClause (l₀ :: l₁ :: l₂ :: rest) =
      ((3 : Nat), (l₀, (l₁, l₂))) := by
  simpa [clausePrefixFromClause, clausePrefixStep, clausePrefixInit] using
    clausePrefixFold_keep_after_three l₀ l₁ l₂ rest

def prefixCoeffAt (q : ClausePrefixState) (i : Nat) : Int :=
  match q.1 with
  | 0 => 0
  | 1 => literalCoeffAt q.2.1 i
  | 2 => literalCoeffAt q.2.1 i + literalCoeffAt q.2.2.1 i
  | _ => literalCoeffAt q.2.1 i + literalCoeffAt q.2.2.1 i +
      literalCoeffAt q.2.2.2 i

def prefixRowFrom (start : Nat) : Nat → ClausePrefixState → List Int
  | 0, _ => []
  | n + 1, q => prefixCoeffAt q start :: prefixRowFrom (start + 1) n q

def prefixRow (n : Nat) (q : ClausePrefixState) : List Int :=
  prefixRowFrom 0 n q

theorem prefixRowFrom_count_zero_eq
    (start n : Nat) (l₀ l₁ l₂ : SAT.Literal) :
    prefixRowFrom start n ((0 : Nat), (l₀, (l₁, l₂))) =
      clauseRowFrom start n ([] : SAT.Clause) := by
  induction n generalizing start with
  | zero =>
      simp [prefixRowFrom, clauseRowFrom, zeroRow]
  | succ n ih =>
      simp [prefixRowFrom, prefixCoeffAt, clauseRowFrom, zeroRow, ih]

theorem prefixRowFrom_count_one_eq
    (start n : Nat) (l₀ l₁ l₂ : SAT.Literal) :
    prefixRowFrom start n ((1 : Nat), (l₀, (l₁, l₂))) =
      clauseRowFrom start n [l₀] := by
  induction n generalizing start with
  | zero =>
      simp [prefixRowFrom, clauseRowFrom, literalRowFrom, zeroRow, addRows]
  | succ n ih =>
      simp [prefixRowFrom, prefixCoeffAt, clauseRowFrom, literalRowFrom, zeroRow,
        addRows, ih]

theorem prefixRowFrom_count_two_eq
    (start n : Nat) (l₀ l₁ l₂ : SAT.Literal) :
    prefixRowFrom start n ((2 : Nat), (l₀, (l₁, l₂))) =
      clauseRowFrom start n [l₀, l₁] := by
  induction n generalizing start with
  | zero =>
      simp [prefixRowFrom, clauseRowFrom, literalRowFrom, zeroRow, addRows]
  | succ n ih =>
      simp [prefixRowFrom, prefixCoeffAt, clauseRowFrom, literalRowFrom, zeroRow,
        addRows, ih]

theorem prefixRowFrom_count_three_eq
    (start n : Nat) (l₀ l₁ l₂ : SAT.Literal) :
    prefixRowFrom start n ((3 : Nat), (l₀, (l₁, l₂))) =
      clauseRowFrom start n [l₀, l₁, l₂] := by
  induction n generalizing start with
  | zero =>
      simp [prefixRowFrom, clauseRowFrom, literalRowFrom, zeroRow, addRows]
  | succ n ih =>
      simp [prefixRowFrom, prefixCoeffAt, clauseRowFrom, literalRowFrom, zeroRow,
        addRows, ih, Int.add_assoc]

theorem prefixRowFrom_clausePrefix_eq_clauseRowFrom
    (start n : Nat) {c : SAT.Clause} (hlen : c.length ≤ 3) :
    prefixRowFrom start n (clausePrefixFromClause c) =
      clauseRowFrom start n c := by
  cases c with
  | nil =>
      simp [clausePrefixFromClause_nil, clausePrefixInit, defaultLiteralForIPRows,
        prefixRowFrom_count_zero_eq]
  | cons l₀ rest =>
      cases rest with
      | nil =>
          simp [clausePrefixFromClause_singleton, defaultLiteralForIPRows,
            prefixRowFrom_count_one_eq]
      | cons l₁ rest =>
          cases rest with
          | nil =>
              simp [clausePrefixFromClause_pair, defaultLiteralForIPRows,
                prefixRowFrom_count_two_eq]
          | cons l₂ rest =>
              cases rest with
              | nil =>
                  simp [clausePrefixFromClause_three_or_more, prefixRowFrom_count_three_eq]
              | cons _ _ =>
                  simp at hlen
                  omega

theorem prefixRow_clausePrefix_eq_clauseRow {c : SAT.Clause}
    (n : Nat) (hlen : c.length ≤ 3) :
    prefixRow n (clausePrefixFromClause c) =
      clauseRow n c := by
  rw [prefixRow, prefixRowFrom_clausePrefix_eq_clauseRowFrom 0 n hlen,
    clauseRowFrom_zero]

end ZeroOneIP
end Karp21
end ComplexityReduction
