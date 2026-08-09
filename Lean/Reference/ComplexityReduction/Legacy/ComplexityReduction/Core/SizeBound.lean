/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace ComplexityReduction

/-- Linear output-size growth relative to chosen input and output measures. -/
def LinearSizeBound {α β : Type}
    (inputSize : α → Nat) (outputSize : β → Nat) (f : α → β) : Prop :=
  ∃ coeff const : Nat, ∀ x, outputSize (f x) ≤ coeff * inputSize x + const

/-- Polynomial output-size growth relative to chosen input and output measures. -/
def PolynomialSizeBound {α β : Type}
    (inputSize : α → Nat) (outputSize : β → Nat) (f : α → β) : Prop :=
  ∃ degree coeff const : Nat,
    ∀ x, outputSize (f x) ≤ coeff * (inputSize x) ^ degree + const

namespace LinearSizeBound

/-- Build a linear size-bound witness from explicit constants. -/
theorem intro_with {α β : Type} {inputSize : α → Nat} {outputSize : β → Nat}
    {f : α → β} (coeff const : Nat)
    (h : ∀ x, outputSize (f x) ≤ coeff * inputSize x + const) :
    LinearSizeBound inputSize outputSize f :=
  ⟨coeff, const, h⟩

/-- A size-nonincreasing map has a linear bound with coefficient 1. -/
theorem of_le {α β : Type} {inputSize : α → Nat} {outputSize : β → Nat}
    {f : α → β}
    (h : ∀ x, outputSize (f x) ≤ inputSize x) :
    LinearSizeBound inputSize outputSize f :=
  ⟨1, 0, by intro x; simpa using h x⟩

/-- Constant-size output has a linear bound with coefficient 0. -/
theorem const {α β : Type} {inputSize : α → Nat} {outputSize : β → Nat}
    {f : α → β} (c : Nat) (h : ∀ x, outputSize (f x) ≤ c) :
    LinearSizeBound inputSize outputSize f :=
  ⟨0, c, by intro x; simpa using h x⟩

/-- Identity maps are linearly size-bounded. -/
theorem id {α : Type} {size : α → Nat} :
    LinearSizeBound size size id :=
  of_le (by intro x; exact Nat.le_refl _)

/-- Composition of linear size bounds is polynomially reusable as another linear bound. -/
theorem comp {α β γ : Type}
    {sizeα : α → Nat} {sizeβ : β → Nat} {sizeγ : γ → Nat}
    {f : α → β} {g : β → γ}
    (hg : LinearSizeBound sizeβ sizeγ g)
    (hf : LinearSizeBound sizeα sizeβ f) :
    LinearSizeBound sizeα sizeγ (fun x => g (f x)) := by
  rcases hg with ⟨cg, kg, hg⟩
  rcases hf with ⟨cf, kf, hf⟩
  refine ⟨cg * cf, cg * kf + kg, ?_⟩
  intro x
  have h1 := hg (f x)
  have h2 := hf x
  calc
    sizeγ (g (f x)) ≤ cg * sizeβ (f x) + kg := h1
    _ ≤ cg * (cf * sizeα x + kf) + kg := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_left cg h2) kg
    _ = (cg * cf) * sizeα x + (cg * kf + kg) := by
      rw [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

end LinearSizeBound

namespace PolynomialSizeBound

/-- Build a polynomial size-bound witness from explicit constants. -/
theorem intro_with {α β : Type} {inputSize : α → Nat} {outputSize : β → Nat}
    {f : α → β} (degree coeff const : Nat)
    (h : ∀ x, outputSize (f x) ≤ coeff * (inputSize x) ^ degree + const) :
    PolynomialSizeBound inputSize outputSize f :=
  ⟨degree, coeff, const, h⟩

/-- Linear output-size bounds are polynomial output-size bounds. -/
theorem of_linear {α β : Type} {inputSize : α → Nat} {outputSize : β → Nat}
    {f : α → β}
    (h : LinearSizeBound inputSize outputSize f) :
    PolynomialSizeBound inputSize outputSize f := by
  rcases h with ⟨coeff, const, hBound⟩
  exact ⟨1, coeff, const, by
    intro x
    simpa using hBound x⟩

/-- Identity maps have a polynomial size bound. -/
theorem id {α : Type} {size : α → Nat} :
    PolynomialSizeBound size size id :=
  of_linear LinearSizeBound.id

/-- Constant-size output has a polynomial size bound. -/
theorem const {α β : Type} {inputSize : α → Nat} {outputSize : β → Nat}
    {f : α → β} (c : Nat) (h : ∀ x, outputSize (f x) ≤ c) :
    PolynomialSizeBound inputSize outputSize f :=
  of_linear (LinearSizeBound.const c h)

end PolynomialSizeBound

end ComplexityReduction
