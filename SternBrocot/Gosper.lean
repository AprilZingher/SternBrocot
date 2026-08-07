/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Gosper's tensor

`rigidity` says addition can never be a Boolean operation on this encoding, so it
has to be **stateful**. The tensor is what that state looks like: eight integers
carrying

  `z = (a₁xy + b₁x + c₁y + d₁) / (a₂xy + b₂x + c₂y + d₂)`

with two kinds of move. *Absorb* consumes a move from an input and adjusts the
tensor; *emit* produces a move of the output and adjusts the tensor. All six are
integer arithmetic — no rationals are ever formed.

This file proves each step correct: absorbing a move from an input is the same as
having applied that move to the input in the first place, and emitting leaves
exactly the right residue. Those are the equations a corecursive implementation
gets to assume. Running the machine forever, and proving it productive, is the
layer above and is where Lean 4 is genuinely harder than Coq.

## Why fixed-size state is the point

The hand-derived rewrite rules at the bottom are all *instances* of this one
machine, and they are correct — but rewriting grows the expression at every step,
while the tensor stays at eight integers forever.

## Main results

* `SternBrocot.Tensor.value_absorbLeftS` and friends — the six step-correctness
  theorems.
* `SternBrocot.Tensor.value_add`, `value_mul` — the machine started at `x + y`
  and `x * y` computes them.
* `SternBrocot.rule_S_sub_L`, `rule_L_sub_L` — the two rules that needed
  correcting.
-/

namespace SternBrocot

/-- The right move on values: `q ↦ q + 1`. -/
def moveS (q : ℚ) : ℚ := q + 1

/-- The left move on values: `q ↦ q / (q + 1)`. -/
def moveL (q : ℚ) : ℚ := q / (q + 1)

@[simp] theorem moveS_apply (q : ℚ) : moveS q = q + 1 := rfl
@[simp] theorem moveL_apply (q : ℚ) : moveL q = q / (q + 1) := rfl

/-! ### The tensor -/

/-- Gosper's `2 × 2 × 2` tensor: eight integers, read as a bilinear fraction in
the two inputs. -/
structure Tensor where
  /-- `xy` coefficient of the numerator -/
  a₁ : ℤ
  /-- `x` coefficient of the numerator -/
  b₁ : ℤ
  /-- `y` coefficient of the numerator -/
  c₁ : ℤ
  /-- constant term of the numerator -/
  d₁ : ℤ
  /-- `xy` coefficient of the denominator -/
  a₂ : ℤ
  /-- `x` coefficient of the denominator -/
  b₂ : ℤ
  /-- `y` coefficient of the denominator -/
  c₂ : ℤ
  /-- constant term of the denominator -/
  d₂ : ℤ
deriving DecidableEq, Repr

namespace Tensor

/-- The numerator, as a function of the two inputs. -/
def num (t : Tensor) (x y : ℚ) : ℚ := t.a₁ * x * y + t.b₁ * x + t.c₁ * y + t.d₁

/-- The denominator, as a function of the two inputs. -/
def den (t : Tensor) (x y : ℚ) : ℚ := t.a₂ * x * y + t.b₂ * x + t.c₂ * y + t.d₂

/-- The value the tensor currently represents. -/
def value (t : Tensor) (x y : ℚ) : ℚ := t.num x y / t.den x y

/-! ### Absorbing a move from an input

The `S` substitutions are exact polynomial identities, so they hold
unconditionally. The `L` substitutions multiply numerator and denominator by the
same factor `x + 1`, so they need that factor nonzero. -/

/-- Absorb a right move from the left input: `x ↦ x + 1`. -/
def absorbLeftS (t : Tensor) : Tensor :=
  ⟨t.a₁, t.b₁, t.c₁ + t.a₁, t.d₁ + t.b₁, t.a₂, t.b₂, t.c₂ + t.a₂, t.d₂ + t.b₂⟩

/-- Absorb a left move from the left input: `x ↦ x / (x + 1)`. -/
def absorbLeftL (t : Tensor) : Tensor :=
  ⟨t.a₁ + t.c₁, t.b₁ + t.d₁, t.c₁, t.d₁, t.a₂ + t.c₂, t.b₂ + t.d₂, t.c₂, t.d₂⟩

/-- Absorb a right move from the right input: `y ↦ y + 1`. -/
def absorbRightS (t : Tensor) : Tensor :=
  ⟨t.a₁, t.b₁ + t.a₁, t.c₁, t.d₁ + t.c₁, t.a₂, t.b₂ + t.a₂, t.c₂, t.d₂ + t.c₂⟩

/-- Absorb a left move from the right input: `y ↦ y / (y + 1)`. -/
def absorbRightL (t : Tensor) : Tensor :=
  ⟨t.a₁ + t.b₁, t.b₁, t.c₁ + t.d₁, t.d₁, t.a₂ + t.b₂, t.b₂, t.c₂ + t.d₂, t.d₂⟩

theorem num_absorbLeftS (t : Tensor) (x y : ℚ) :
    (absorbLeftS t).num x y = t.num (moveS x) y := by
  simp only [num, absorbLeftS, moveS_apply]; push_cast; ring

theorem den_absorbLeftS (t : Tensor) (x y : ℚ) :
    (absorbLeftS t).den x y = t.den (moveS x) y := by
  simp only [den, absorbLeftS, moveS_apply]; push_cast; ring

/-- **Absorbing a right move from the left input.** -/
@[simp] theorem value_absorbLeftS (t : Tensor) (x y : ℚ) :
    (absorbLeftS t).value x y = t.value (moveS x) y := by
  rw [value, num_absorbLeftS, den_absorbLeftS, value]

theorem num_absorbRightS (t : Tensor) (x y : ℚ) :
    (absorbRightS t).num x y = t.num x (moveS y) := by
  simp only [num, absorbRightS, moveS_apply]; push_cast; ring

theorem den_absorbRightS (t : Tensor) (x y : ℚ) :
    (absorbRightS t).den x y = t.den x (moveS y) := by
  simp only [den, absorbRightS, moveS_apply]; push_cast; ring

/-- **Absorbing a right move from the right input.** -/
@[simp] theorem value_absorbRightS (t : Tensor) (x y : ℚ) :
    (absorbRightS t).value x y = t.value x (moveS y) := by
  rw [value, num_absorbRightS, den_absorbRightS, value]

theorem num_absorbLeftL (t : Tensor) (x y : ℚ) (hx : x + 1 ≠ 0) :
    (absorbLeftL t).num x y = (x + 1) * t.num (moveL x) y := by
  simp only [num, absorbLeftL, moveL_apply]
  push_cast
  field_simp
  ring

theorem den_absorbLeftL (t : Tensor) (x y : ℚ) (hx : x + 1 ≠ 0) :
    (absorbLeftL t).den x y = (x + 1) * t.den (moveL x) y := by
  simp only [den, absorbLeftL, moveL_apply]
  push_cast
  field_simp
  ring

/-- **Absorbing a left move from the left input.** -/
theorem value_absorbLeftL (t : Tensor) (x y : ℚ) (hx : x + 1 ≠ 0) :
    (absorbLeftL t).value x y = t.value (moveL x) y := by
  rw [value, num_absorbLeftL t x y hx, den_absorbLeftL t x y hx,
    mul_div_mul_left _ _ hx, value]

theorem num_absorbRightL (t : Tensor) (x y : ℚ) (hy : y + 1 ≠ 0) :
    (absorbRightL t).num x y = (y + 1) * t.num x (moveL y) := by
  simp only [num, absorbRightL, moveL_apply]
  push_cast
  field_simp
  ring

theorem den_absorbRightL (t : Tensor) (x y : ℚ) (hy : y + 1 ≠ 0) :
    (absorbRightL t).den x y = (y + 1) * t.den x (moveL y) := by
  simp only [den, absorbRightL, moveL_apply]
  push_cast
  field_simp
  ring

/-- **Absorbing a left move from the right input.** -/
theorem value_absorbRightL (t : Tensor) (x y : ℚ) (hy : y + 1 ≠ 0) :
    (absorbRightL t).value x y = t.value x (moveL y) := by
  rw [value, num_absorbRightL t x y hy, den_absorbRightL t x y hy,
    mul_div_mul_left _ _ hy, value]

/-! ### Emitting a move of the output

`emitS` is the legal move when the current value is `≥ 1` and `emitL` when it is
`< 1`. The guard decides which move the *tree* permits; the equations below hold
whenever the denominators are nonzero. Deciding that guard is exactly where the
undecidability lives — the test never resolves by finite inspection when the
value sits precisely on the branch point. -/

/-- Emit a right move: the residue is `z - 1`. -/
def emitS (t : Tensor) : Tensor :=
  ⟨t.a₁ - t.a₂, t.b₁ - t.b₂, t.c₁ - t.c₂, t.d₁ - t.d₂, t.a₂, t.b₂, t.c₂, t.d₂⟩

/-- Emit a left move: the residue is `z / (1 - z)`. -/
def emitL (t : Tensor) : Tensor :=
  ⟨t.a₁, t.b₁, t.c₁, t.d₁, t.a₂ - t.a₁, t.b₂ - t.b₁, t.c₂ - t.c₁, t.d₂ - t.d₁⟩

/-- **Emitting a right move leaves `z - 1`.** -/
theorem value_emitS (t : Tensor) (x y : ℚ) (h : t.den x y ≠ 0) :
    (emitS t).value x y = t.value x y - 1 := by
  have hnum : (emitS t).num x y = t.num x y - t.den x y := by
    simp only [num, den, emitS]; push_cast; ring
  have hden : (emitS t).den x y = t.den x y := by simp only [den, emitS]
  rw [value, hnum, hden, value, sub_div, div_self h]

/-- **Emitting a left move leaves `z / (1 - z)`.** -/
theorem value_emitL (t : Tensor) (x y : ℚ) (h : t.den x y ≠ 0)
    (h' : t.den x y - t.num x y ≠ 0) :
    (emitL t).value x y = t.value x y / (1 - t.value x y) := by
  have hnum : (emitL t).num x y = t.num x y := by simp only [num, emitL]
  have hden : (emitL t).den x y = t.den x y - t.num x y := by
    simp only [num, den, emitL]; push_cast; ring
  rw [value, hnum, hden, value]
  field_simp

/-! ### Starting the machine -/

/-- The tensor for `x + y`. -/
def add : Tensor := ⟨0, 1, 1, 0, 0, 0, 0, 1⟩

/-- The tensor for `x * y`. -/
def mul : Tensor := ⟨1, 0, 0, 0, 0, 0, 0, 1⟩

/-- The tensor for `x - y`. -/
def sub : Tensor := ⟨0, 1, -1, 0, 0, 0, 0, 1⟩

/-- The tensor for `x / y`. -/
def divT : Tensor := ⟨0, 1, 0, 0, 0, 0, 1, 0⟩

@[simp] theorem value_add (x y : ℚ) : add.value x y = x + y := by
  simp only [value, num, den, add]; push_cast; ring_nf

@[simp] theorem value_mul (x y : ℚ) : mul.value x y = x * y := by
  simp only [value, num, den, mul]; push_cast; ring_nf

@[simp] theorem value_sub (x y : ℚ) : sub.value x y = x - y := by
  simp only [value, num, den, sub]; push_cast; ring_nf

@[simp] theorem value_divT (x y : ℚ) : divT.value x y = x / y := by
  simp only [value, num, den, divT]; push_cast; ring_nf

end Tensor

/-! ### The hand-derived rules

Each is an instance of the tensor above. They are stated for nonnegative inputs,
which is where the tree lives. -/

section Rules

variable {a b : ℚ}

theorem rule_SS_mul (a b : ℚ) : moveS a * moveS b = moveS (a + b + a * b) := by
  simp only [moveS_apply]; ring

theorem rule_LL_mul (ha : 0 ≤ a) (hb : 0 ≤ b) :
    moveL a * moveL b = moveL (a * b / moveS (a + b)) := by
  have h1 : a + 1 ≠ 0 := by linarith
  have h2 : b + 1 ≠ 0 := by linarith
  have h3 : a + b + 1 ≠ 0 := by linarith
  have h4 : a * b + (a + b + 1) ≠ 0 := by nlinarith
  simp only [moveS_apply, moveL_apply]
  field_simp
  ring

theorem rule_recip_S (ha : 0 < a) : (moveS a)⁻¹ = moveL a⁻¹ := by
  have h1 : a + 1 ≠ 0 := by linarith
  simp only [moveS_apply, moveL_apply]
  field_simp
  ring

theorem rule_recip_L (ha : 0 < a) : (moveL a)⁻¹ = moveS a⁻¹ := by
  have h1 : a + 1 ≠ 0 := by linarith
  simp only [moveS_apply, moveL_apply]
  field_simp
  ring

/-- Rule 7, the `S` branch. -/
theorem rule_LL_add_S (ha : 0 ≤ a) (hb : 0 ≤ b) :
    moveL a + moveL b = moveS ((a * b - 1) / (moveS a * moveS b)) := by
  have h1 : a + 1 ≠ 0 := by linarith
  have h2 : b + 1 ≠ 0 := by linarith
  simp only [moveS_apply, moveL_apply]
  field_simp
  ring

/-- Rule 7, the `L` branch. Note this is the *same* identity: the guard `a ≥ 1/b`
decides which move the tree permits, not which equation is true. -/
theorem rule_LL_add_L (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 1 - a * b ≠ 0) :
    moveL a + moveL b = moveL ((2 * (a * b) + a + b) / (1 - a * b)) := by
  have h1 : a + 1 ≠ 0 := by linarith
  have h2 : b + 1 ≠ 0 := by linarith
  have hprod : (a + 1) * (b + 1) ≠ 0 := mul_ne_zero h1 h2
  have hu : (2 * (a * b) + a + b) / (1 - a * b) + 1
      = ((a + 1) * (b + 1)) / (1 - a * b) := by
    field_simp
    ring
  simp only [moveL_apply]
  rw [hu, div_div_eq_mul_div, div_mul_cancel₀ _ hab]
  field_simp
  ring

/-! #### The two corrected rules

Rule 14 needs `1/Sb`, not `1/Lb`; rule 8's negated branch needs `SSb*a`, the
arguments swapping. -/

/-- **Rule 14, corrected**: `Sa - Lb = a + 1/Sb`. -/
theorem rule_S_sub_L (hb : 0 ≤ b) : moveS a - moveL b = a + (moveS b)⁻¹ := by
  have h2 : b + 1 ≠ 0 := by linarith
  simp only [moveS_apply, moveL_apply]
  field_simp
  ring

/-- **Rule 8, corrected**: `La - Lb = -L((b-a) / S(SSb * a))`.

Stated originally for the `a < b` branch, but like rule 7 the identity does not
need the guard — both sides are `(a-b) / ((a+1)(b+1))` either way. The guard
decides which move the tree permits to be emitted, not which equation is true. -/
theorem rule_L_sub_L (ha : 0 ≤ a) (hb : 0 ≤ b) :
    moveL a - moveL b = -(moveL ((b - a) / moveS (moveS (moveS b) * a))) := by
  have h1 : a + 1 ≠ 0 := by linarith
  have h2 : b + 1 ≠ 0 := by linarith
  have h3 : (b + 1 + 1) * a + 1 ≠ 0 := by nlinarith
  have hu : (b - a) / ((b + 1 + 1) * a + 1) + 1
      = ((a + 1) * (b + 1)) / ((b + 1 + 1) * a + 1) := by
    field_simp
    ring
  simp only [moveS_apply, moveL_apply]
  rw [hu, div_div_eq_mul_div, div_mul_cancel₀ _ h3]
  field_simp
  ring

/-! ### The machine, running

A few steps by hand, to confirm the tensor does what the theorems say. -/

example : Tensor.add.value 1 2 = 3 := by norm_num

/-- Absorbing a right move from the left input is the same as having added one
to it: `(1+1) + 2 = 4`. -/
example : (Tensor.absorbLeftS Tensor.add).value 1 2 = 4 := by
  rw [Tensor.value_absorbLeftS]; norm_num

/-- Absorbing a left move from the right input: `1 + 2/3`. -/
example : (Tensor.absorbRightL Tensor.add).value 1 2 = 1 + 2 / 3 := by
  rw [Tensor.value_absorbRightL _ _ _ (by norm_num)]; norm_num

/-- Emitting a right move from `1 + 2 = 3` leaves `2`. -/
example : (Tensor.emitS Tensor.add).value 1 2 = 2 := by
  rw [Tensor.value_emitS _ _ _ (by norm_num [Tensor.den, Tensor.add])]; norm_num

end Rules

end SternBrocot
