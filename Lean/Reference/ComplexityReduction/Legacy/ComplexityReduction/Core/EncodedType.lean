/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs

namespace ComplexityReduction

/-- A type together with a finite alphabet encoding. -/
structure EncodedType : Type 1 where
  Carrier : Type
  Symbol : Type
  finite_symbol : Fintype Symbol
  encode : Carrier → List Symbol

namespace EncodedType

instance (X : EncodedType) : Fintype X.Symbol :=
  X.finite_symbol

/-- Encoded input length. -/
def inputSize (X : EncodedType) (x : X.Carrier) : Nat :=
  (X.encode x).length

/-- Trivial compatibility encoding for unencoded objects. -/
def raw (α : Type) : EncodedType where
  Carrier := α
  Symbol := Unit
  finite_symbol := inferInstance
  encode := fun _ => []

/-- Boolean values encoded as one symbol. -/
def bool : EncodedType where
  Carrier := Bool
  Symbol := Bool
  finite_symbol := inferInstance
  encode := fun b => [b]

/-- Natural numbers with unary finite-alphabet encoding. -/
def nat : EncodedType where
  Carrier := Nat
  Symbol := Bool
  finite_symbol := inferInstance
  encode := fun n => List.replicate n true ++ [false]

/-- Integers encoded by a sign tag followed by a unary magnitude payload. -/
def int : EncodedType where
  Carrier := Int
  Symbol := Bool
  finite_symbol := inferInstance
  encode := fun z =>
    match z with
    | Int.ofNat n => false :: nat.encode n
    | Int.negSucc n => true :: nat.encode n

/-- Natural numbers with a base-two finite-alphabet encoding. -/
def binaryNat : EncodedType where
  Carrier := Nat
  Symbol := Bool
  finite_symbol := inferInstance
  encode := fun n => (Nat.digits 2 n).map fun d => decide (d = 1)

/-- Integers encoded by a sign tag followed by a base-two magnitude payload. -/
def binaryInt : EncodedType where
  Carrier := Int
  Symbol := Bool ⊕ binaryNat.Symbol
  finite_symbol := inferInstance
  encode := fun z =>
    match z with
    | Int.ofNat n => [Sum.inl false] ++ (binaryNat.encode n).map Sum.inr
    | Int.negSucc n => [Sum.inl true] ++ (binaryNat.encode n).map Sum.inr

/-- Finite values encoded by their numeric value in unary. -/
def fin (n : Nat) : EncodedType where
  Carrier := Fin n
  Symbol := Bool
  finite_symbol := inferInstance
  encode := fun i => List.replicate i.val true ++ [false]

/-- Product encoding with a delimiter. -/
def prod (X Y : EncodedType) : EncodedType where
  Carrier := X.Carrier × Y.Carrier
  Symbol := Option (X.Symbol ⊕ Y.Symbol)
  finite_symbol := inferInstance
  encode := fun p =>
    (X.encode p.1).map (fun s => some (Sum.inl s)) ++ [none] ++
      (Y.encode p.2).map (fun s => some (Sum.inr s))

/-- Sum encoding with a Boolean tag. -/
def sum (X Y : EncodedType) : EncodedType where
  Carrier := X.Carrier ⊕ Y.Carrier
  Symbol := Bool ⊕ (X.Symbol ⊕ Y.Symbol)
  finite_symbol := inferInstance
  encode := fun z =>
    match z with
    | Sum.inl x => [Sum.inl false] ++ (X.encode x).map (fun s => Sum.inr (Sum.inl s))
    | Sum.inr y => [Sum.inl true] ++ (Y.encode y).map (fun s => Sum.inr (Sum.inr s))

/-- List encoding with element delimiters. -/
def list (X : EncodedType) : EncodedType where
  Carrier := List X.Carrier
  Symbol := Option X.Symbol
  finite_symbol := inferInstance
  encode := fun xs => xs.flatMap (fun x => (X.encode x).map some ++ [none])

@[simp] theorem inputSize_bool (b : Bool) :
    bool.inputSize b = 1 := by
  simp [inputSize, bool]

@[simp] theorem inputSize_nat (n : Nat) :
    nat.inputSize n = n + 1 := by
  simp [inputSize, nat]

@[simp] theorem inputSize_int_ofNat (n : Nat) :
    int.inputSize (Int.ofNat n) = n + 2 := by
  simp [inputSize, int, nat]

@[simp] theorem inputSize_int_negSucc (n : Nat) :
    int.inputSize (Int.negSucc n) = n + 2 := by
  simp [inputSize, int, nat]

@[simp] theorem inputSize_prod (X Y : EncodedType) (p : X.Carrier × Y.Carrier) :
    (prod X Y).inputSize p = X.inputSize p.1 + 1 + Y.inputSize p.2 := by
  simp [inputSize, prod]
  omega

@[simp] theorem inputSize_list_nil (X : EncodedType) :
    (list X).inputSize ([] : List X.Carrier) = 0 := by
  simp [inputSize, list]

@[simp] theorem inputSize_list_cons (X : EncodedType) (x : X.Carrier)
    (xs : List X.Carrier) :
    (list X).inputSize (x :: xs) =
      X.inputSize x + 1 + (list X).inputSize xs := by
  simp [inputSize, list]
  omega

/--
Split a list over `Option α` into segments separated by `none`.

This parser is only used for proving injectivity of the generic list encoding.
Malformed inputs without a final delimiter are still assigned a segment, but the
theorem below only relies on its behavior on strings produced by `EncodedType.list`.
-/
def splitOptionSegments {α : Type} : List (Option α) → List (List α)
  | [] => []
  | none :: xs => [] :: splitOptionSegments xs
  | some x :: xs =>
      match splitOptionSegments xs with
      | [] => [[x]]
      | ys :: yss => (x :: ys) :: yss

theorem splitOptionSegments_map_some_append_none {α : Type} (xs : List α)
    (rest : List (Option α)) :
    splitOptionSegments (xs.map some ++ none :: rest) = xs :: splitOptionSegments rest := by
  induction xs with
  | nil =>
      simp [splitOptionSegments]
  | cons x xs ih =>
      simp [splitOptionSegments, ih]

theorem splitOptionSegments_list_encode (X : EncodedType) (xs : List X.Carrier) :
    splitOptionSegments ((list X).encode xs) = xs.map X.encode := by
  induction xs with
  | nil =>
      simp [list, splitOptionSegments]
  | cons x xs ih =>
      have ih' :
          splitOptionSegments
              (xs.flatMap fun x => (X.encode x).map some ++ [none]) =
            xs.map X.encode := by
        simpa [list] using ih
      simp [list, List.append_assoc, ih', splitOptionSegments_map_some_append_none]

/-- Boolean encoding is injective. -/
theorem bool_encode_injective : Function.Injective bool.encode := by
  intro b c h
  simpa [bool] using h

/-- Unary natural-number encoding is injective. -/
theorem nat_encode_injective : Function.Injective nat.encode := by
  intro n m h
  have hlen := congrArg List.length h
  have hlen' : Nat.succ n = Nat.succ m := by
    simpa [nat] using hlen
  exact Nat.succ.inj hlen'

/-- Tagged unary integer encoding is injective. -/
theorem int_encode_injective : Function.Injective int.encode := by
  intro z w h
  cases z <;> cases w <;> simp [int] at h ⊢
  · exact nat_encode_injective h
  · exact nat_encode_injective h

/-- Decoding the Boolean binary payload recovers `Nat.digits 2`. -/
theorem binaryNat_decode_encode (n : Nat) :
    (binaryNat.encode n).map (fun b : Bool => if b then 1 else 0) = Nat.digits 2 n := by
  change ((Nat.digits 2 n).map (fun d => decide (d = 1))).map
      (fun b : Bool => if b then 1 else 0) = Nat.digits 2 n
  rw [List.map_map]
  calc
    List.map (((fun b : Bool => if b then 1 else 0) ∘ fun d => decide (d = 1)))
        (Nat.digits 2 n) =
        List.map id (Nat.digits 2 n) := by
          apply List.map_congr_left
          intro d hd
          have hdlt : d < 2 := Nat.digits_lt_base (by decide : 1 < 2) hd
          cases d with
          | zero =>
              simp
          | succ d =>
              cases d with
              | zero =>
                  simp
              | succ d =>
                  exact False.elim
                    ((Nat.not_lt.mpr
                        (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le d)))) hdlt)
    _ = Nat.digits 2 n := List.map_id (Nat.digits 2 n)

/-- Base-two natural-number encoding is injective. -/
theorem binaryNat_encode_injective : Function.Injective binaryNat.encode := by
  intro n m h
  have hDigits := congrArg (List.map fun b : Bool => if b then 1 else 0) h
  rw [binaryNat_decode_encode n, binaryNat_decode_encode m] at hDigits
  exact Nat.digits.injective 2 hDigits

/-- Tagged base-two integer encoding is injective. -/
theorem binaryInt_encode_injective : Function.Injective binaryInt.encode := by
  intro z w h
  cases z <;> cases w <;> simp [binaryInt] at h ⊢
  · exact binaryNat_encode_injective
      ((List.map_injective_iff.2 (fun _ _ hxy => Sum.inr.inj hxy)) h)
  · exact binaryNat_encode_injective
      ((List.map_injective_iff.2 (fun _ _ hxy => Sum.inr.inj hxy)) h)

def prodLeftSymbol {α β : Type} : Option (α ⊕ β) → Option α
  | some (Sum.inl x) => some x
  | _ => none

def prodRightSymbol {α β : Type} : Option (α ⊕ β) → Option β
  | some (Sum.inr y) => some y
  | _ => none

theorem prod_left_filter_encode (X Y : EncodedType) (p : X.Carrier × Y.Carrier) :
    List.filterMap prodLeftSymbol ((prod X Y).encode p) = X.encode p.1 := by
  cases p
  simp [prod, prodLeftSymbol]

theorem prod_right_filter_encode (X Y : EncodedType) (p : X.Carrier × Y.Carrier) :
    List.filterMap prodRightSymbol ((prod X Y).encode p) = Y.encode p.2 := by
  cases p
  simp [prod, prodRightSymbol]

/-- Product encodings are injective when the component encodings are injective. -/
theorem prod_encode_injective {X Y : EncodedType}
    (hX : Function.Injective X.encode) (hY : Function.Injective Y.encode) :
    Function.Injective (prod X Y).encode := by
  intro p q h
  have hLeft := congrArg (List.filterMap (@prodLeftSymbol X.Symbol Y.Symbol)) h
  have hRight := congrArg (List.filterMap (@prodRightSymbol X.Symbol Y.Symbol)) h
  rw [prod_left_filter_encode X Y p, prod_left_filter_encode X Y q] at hLeft
  rw [prod_right_filter_encode X Y p, prod_right_filter_encode X Y q] at hRight
  exact Prod.ext (hX hLeft) (hY hRight)

/-- List encodings are injective when the element encoding is injective. -/
theorem list_encode_injective {X : EncodedType} (hX : Function.Injective X.encode) :
    Function.Injective (list X).encode := by
  intro xs ys h
  have hSegments := congrArg (@splitOptionSegments X.Symbol) h
  rw [splitOptionSegments_list_encode X xs, splitOptionSegments_list_encode X ys] at hSegments
  exact (List.map_injective_iff.2 hX) hSegments

/-- The string type over a finite alphabet, encoded as itself. -/
def ofAlphabet (A : Type) [Fintype A] : EncodedType where
  Carrier := List A
  Symbol := A
  finite_symbol := inferInstance
  encode := id

end EncodedType

/-- Typeclass form for adding an encoding to an existing Lean type. -/
class HasEncoding (α : Type) where
  Symbol : Type
  finite_symbol : Fintype Symbol
  encode : α → List Symbol

namespace HasEncoding

instance (α : Type) [h : HasEncoding α] : Fintype h.Symbol :=
  h.finite_symbol

/-- Convert a typeclass encoding into an `EncodedType`. -/
def toEncodedType (α : Type) [h : HasEncoding α] : EncodedType where
  Carrier := α
  Symbol := h.Symbol
  finite_symbol := h.finite_symbol
  encode := h.encode

/-- Encoded input length for a typeclass encoding. -/
def inputSize {α : Type} [h : HasEncoding α] (x : α) : Nat :=
  (h.encode x).length

end HasEncoding

end ComplexityReduction
