/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Tree nodes and their values

The countable dense subset of `P(ω)/∼` is the set of tree *nodes* — finite
paths. On a finite path the Stern–Brocot value is a finite computation in `ℚ`,
with no limits and no analysis, which is what makes this the tractable half of
building `Φ`.

A finite path is a `List Bool`, read left to right, `true = R` (the successor
move `S`) and `false = L`. The value is defined by the two Möbius maps that the
moves induce on `[0, ∞]`:

* `R : t ↦ t + 1`
* `L : t ↦ t / (t + 1)`

These are inverse-conjugate: `J R J = L` for `J : t ↦ 1/t`, which is the identity
`recip_L` proved upstairs.

## Why this Φ and not the cheap one

There is a much cheaper order isomorphism `P(ω)/∼ ≃o [0,1]`, namely reading `x`
as a binary expansion. Its fibres are also exactly the tail pairs, so it would
discharge "the carrier supports a complete ordered field" for a fraction of the
work. It is the wrong map: it differs from the Stern–Brocot map by an order
automorphism of `[0,1]` (Minkowski's question mark function), so arithmetic
transported along it is *not* the arithmetic Gosper's algorithm computes. This
file therefore builds the genuine mediant value.

## Main results

* `SternBrocot.nodeValue` — the value of a finite path, by recursion.
* `SternBrocot.nodeValue_append_false` — trailing `L` moves are invisible, which
  is why finite *sets* rather than lists are the right index for nodes.
* `SternBrocot.pathMat_det` — **unimodularity**: the Möbius matrix of any finite
  path has determinant `1`. This is the `SL₂(ℤ)` fact everything downstream rests
  on.
* `SternBrocot.nodeValue_eq_div` — the value is `b / d` for the matrix entries.
* `SternBrocot.nodeValue_num_den_coprime` — consequently every node value is a
  nonnegative rational **already in lowest terms**. Half of the Stern–Brocot
  enumeration theorem.
-/

namespace SternBrocot

/-! ### The value of a finite path -/

/-- The Stern–Brocot value of a finite path. `true` is the right move `t ↦ t + 1`
(the successor `S`), `false` is the left move `t ↦ t / (t + 1)`. -/
def nodeValue : List Bool → ℚ
  | [] => 0
  | true :: bs => nodeValue bs + 1
  | false :: bs => nodeValue bs / (nodeValue bs + 1)

@[simp] theorem nodeValue_nil : nodeValue [] = 0 := rfl

@[simp] theorem nodeValue_true (bs : List Bool) :
    nodeValue (true :: bs) = nodeValue bs + 1 := rfl

@[simp] theorem nodeValue_false (bs : List Bool) :
    nodeValue (false :: bs) = nodeValue bs / (nodeValue bs + 1) := rfl

/-- Node values are nonnegative: the tree lives in `[0, ∞]`. -/
theorem nodeValue_nonneg (bs : List Bool) : 0 ≤ nodeValue bs := by
  induction bs with
  | nil => exact le_refl 0
  | cons b bs ih =>
    cases b
    · exact div_nonneg ih (by linarith)
    · simp only [nodeValue_true]; linarith

theorem nodeValue_denom_pos (bs : List Bool) : 0 < nodeValue bs + 1 := by
  have := nodeValue_nonneg bs
  linarith

/-- **Trailing left moves are invisible.** `L` fixes `0`, so padding a finite
path with `false`s does not change its value.

This is why the tree nodes are indexed by finite *sets* — an element of `P(ω)`
whose bits are eventually `0` — rather than by lists. -/
theorem nodeValue_append_false (bs : List Bool) :
    nodeValue (bs ++ [false]) = nodeValue bs := by
  induction bs with
  | nil => norm_num [nodeValue]
  | cons b bs ih =>
    cases b <;> simp [nodeValue, ih]

/-! ### The Möbius matrix

The path matrix acts as `t ↦ (a t + b) / (c t + d)`. Prepending a move
left-multiplies by that move's matrix:

* `R = ![![1, 1], ![0, 1]]`
* `L = ![![1, 0], ![1, 1]]`
-/

/-- The Möbius matrix `(a, b, c, d)` of a finite path, acting as
`t ↦ (a t + b) / (c t + d)`. -/
def pathMat : List Bool → ℤ × ℤ × ℤ × ℤ
  | [] => (1, 0, 0, 1)
  | true :: bs =>
      let m := pathMat bs
      (m.1 + m.2.2.1, m.2.1 + m.2.2.2, m.2.2.1, m.2.2.2)
  | false :: bs =>
      let m := pathMat bs
      (m.1, m.2.1, m.1 + m.2.2.1, m.2.1 + m.2.2.2)

@[simp] theorem pathMat_nil : pathMat [] = (1, 0, 0, 1) := rfl

/-- **Unimodularity.** Every finite path has determinant `1`: the path matrices
land in `SL₂(ℤ)`. Both moves are elementary matrices, so the determinant is
preserved on the nose. -/
theorem pathMat_det (bs : List Bool) :
    (pathMat bs).1 * (pathMat bs).2.2.2 - (pathMat bs).2.1 * (pathMat bs).2.2.1 = 1 := by
  induction bs with
  | nil => norm_num
  | cons b bs ih =>
    cases b <;> simp only [pathMat] <;> linear_combination ih

/-- The bottom row stays nonnegative with positive `d`, so the value `b / d` is
well defined. -/
theorem pathMat_den_pos (bs : List Bool) :
    0 ≤ (pathMat bs).2.1 ∧ 0 < (pathMat bs).2.2.2 := by
  induction bs with
  | nil => exact ⟨le_refl 0, one_pos⟩
  | cons b bs ih =>
    obtain ⟨hb, hd⟩ := ih
    cases b
    · exact ⟨hb, by simp only [pathMat]; linarith⟩
    · exact ⟨by simp only [pathMat]; linarith, hd⟩

/-- The value of a path is the image of `0` under its Möbius matrix, namely
`b / d`. -/
theorem nodeValue_eq_div (bs : List Bool) :
    nodeValue bs = ((pathMat bs).2.1 : ℚ) / ((pathMat bs).2.2.2 : ℚ) := by
  induction bs with
  | nil => norm_num
  | cons b bs ih =>
    obtain ⟨hb, hd⟩ := pathMat_den_pos bs
    have hd' : ((pathMat bs).2.2.2 : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    cases b
    · -- left move: `v / (v + 1) = b / (b + d)`
      have hbd : ((pathMat bs).2.1 : ℚ) + ((pathMat bs).2.2.2 : ℚ) ≠ 0 := by
        have : (0 : ℚ) ≤ ((pathMat bs).2.1 : ℚ) := by exact_mod_cast hb
        have : (0 : ℚ) < ((pathMat bs).2.2.2 : ℚ) := by exact_mod_cast hd
        positivity
      simp only [nodeValue_false, pathMat, ih]
      push_cast
      field_simp
    · -- right move: `v + 1 = (b + d) / d`
      simp only [nodeValue_true, pathMat, ih]
      push_cast
      field_simp

/-- **Node values are already in lowest terms.** Unimodularity forces the
numerator and denominator produced by the tree to be coprime — a common factor
would divide the determinant `1`.

This is half of the statement that the Stern–Brocot tree enumerates `ℚ≥0`
exactly once; the other half is that the map is onto and injective. -/
theorem nodeValue_num_den_coprime (bs : List Bool) :
    IsCoprime (pathMat bs).2.1 (pathMat bs).2.2.2 := by
  exact ⟨-(pathMat bs).2.2.1, (pathMat bs).1, by linear_combination pathMat_det bs⟩

end SternBrocot
