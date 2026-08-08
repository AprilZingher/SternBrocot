/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.CF.Convergent

/-!
# Consecutive convergents: unimodularity and straddling

Two facts about *pairs* of consecutive convergents that `Convergent.lean` has
the ingredients for but never states, because the estimates there only ever
needed one convergent at a time. Both are inputs to Legendre's theorem and to
the theory of best approximation.

## What is here

* `contin_det` — `pₖ qₖ₊₁ − pₖ₊₁ qₖ = ±1`, with the sign alternating according
  to `runBit`. This is `pathMat_det` read through `boundaryMat_eq_contin`: the
  columns of the prefix matrix at a run boundary *are* the two convergents, so
  the determinant of that matrix is exactly this expression, up to the swap that
  `runBit` records.
* `contin_straddle` — `Φ₀ x` lies strictly *between* `pₖ/qₖ` and `pₖ₊₁/qₖ₊₁`,
  again with sides alternating. `Convergent.lean` proves `|Φ₀x − pₖ/qₖ|` is
  small; this says which *side* the error is on, which the absolute value throws
  away.

## Why the two are stated together

They are the same computation seen twice. `column_errors` already proves the
signed statements

  `t − B/D = s/(D(Cs+D)) > 0`  and  `A/C − t = 1/(C(Cs+D)) > 0`,

so the `B`-column is below `t` and the `A`-column above; `boundaryMat_eq_contin`
then says which of those columns is `contin x (k+2)` and which is
`contin x (k+3)`, and that assignment swaps with `runBit x (k+1)`. The
determinant is the same swap applied to `pathMat_det`. So both theorems here are
one case split over `runBit`, and neither needs a new estimate.

## Indexing

As everywhere downstream of `Convergent.lean`, statements are at `k + 2`: the
seeds `contin x 0`, `contin x 1` are not convergents, and `q₁ = 0`.
-/

open Set

namespace SternBrocot

/-! ### Unimodularity of consecutive convergents -/

/-- **Consecutive convergents are unimodular**, with the sign of the determinant
alternating according to the run bit.

This is `pathMat_det` transported along `boundaryMat_eq_contin`. The two cases
are not two proofs: they are the same determinant read off a matrix whose
columns have been swapped, which is exactly what `runBit` records. -/
theorem contin_det {x : Set ℕ} (h : InfFlips x) (k : ℕ) :
    (runBit x (k + 1) = true →
      (contin x (k + 2)).1 * (contin x (k + 3)).2
        - (contin x (k + 3)).1 * (contin x (k + 2)).2 = 1) ∧
    (runBit x (k + 1) = false →
      (contin x (k + 3)).1 * (contin x (k + 2)).2
        - (contin x (k + 2)).1 * (contin x (k + 3)).2 = 1) := by
  obtain ⟨hT, hF⟩ := boundaryMat_eq_contin h (k + 1)
  have hdet := pathMat_det (prefixWord x (runBoundary x (k + 2)))
  constructor
  · intro hb
    have hm : pathMat (prefixWord x (runBoundary x (k + 2)))
        = ((contin x (k + 2)).1, (contin x (k + 3)).1,
           (contin x (k + 2)).2, (contin x (k + 3)).2) := hT hb
    rw [hm] at hdet
    exact hdet
  · intro hb
    have hm : pathMat (prefixWord x (runBoundary x (k + 2)))
        = ((contin x (k + 3)).1, (contin x (k + 2)).1,
           (contin x (k + 3)).2, (contin x (k + 2)).2) := hF hb
    rw [hm] at hdet
    exact hdet

/-- The sign-free form: consecutive convergent columns have determinant `±1`.

This is the shape the lattice argument in the theory of best approximation
wants — every integer pair `(p, q)` is an integer combination of two consecutive
convergents precisely because this determinant is a unit. -/
theorem abs_contin_det {x : Set ℕ} (h : InfFlips x) (k : ℕ) :
    |(contin x (k + 2)).1 * (contin x (k + 3)).2
      - (contin x (k + 3)).1 * (contin x (k + 2)).2| = 1 := by
  obtain ⟨hT, hF⟩ := contin_det h k
  cases hb : runBit x (k + 1)
  · have := hF hb
    rw [show (contin x (k + 2)).1 * (contin x (k + 3)).2
          - (contin x (k + 3)).1 * (contin x (k + 2)).2
        = -((contin x (k + 3)).1 * (contin x (k + 2)).2
          - (contin x (k + 2)).1 * (contin x (k + 3)).2) by ring, this]
    norm_num
  · rw [hT hb]; norm_num

/-- Coprimality of every convergent, an immediate consequence: a common divisor
of `pₖ` and `qₖ` divides the determinant, which is a unit. So the convergents
are already in lowest terms, matching `nodeValue_num_den_coprime` for the finite
nodes. -/
theorem contin_coprime {x : Set ℕ} (h : InfFlips x) (k : ℕ) :
    IsCoprime (contin x (k + 2)).1 (contin x (k + 2)).2 := by
  obtain ⟨hT, hF⟩ := contin_det h k
  cases hb : runBit x (k + 1)
  · exact ⟨-(contin x (k + 3)).2, (contin x (k + 3)).1, by linear_combination hF hb⟩
  · exact ⟨(contin x (k + 3)).2, -(contin x (k + 3)).1, by linear_combination hT hb⟩

/-! ### The convergents straddle the value

`Convergent.lean` bounds `|Φ₀x − pₖ/qₖ|`. The absolute value there discards
which side the convergent is on, and that is the information Legendre's theorem
runs on: consecutive convergents bracket the value, so the intervals they cut
out nest. -/

/-- **Consecutive convergents lie on opposite sides of `Φ₀ x`**, and which side
is which alternates with the run bit.

The proof is `column_errors` without the final `abs` — that lemma already
produces both differences as manifestly *positive* quantities, so no new
estimate is involved, only a reading of which column is which convergent. -/
theorem contin_straddle {x : Set ℕ} (hirr : Irrational (toReal₀ x)) (k : ℕ) :
    (runBit x (k + 1) = true →
      ((contin x (k + 3)).1 : ℝ) / ((contin x (k + 3)).2 : ℝ) < toReal₀ x ∧
        toReal₀ x < ((contin x (k + 2)).1 : ℝ) / ((contin x (k + 2)).2 : ℝ)) ∧
    (runBit x (k + 1) = false →
      ((contin x (k + 2)).1 : ℝ) / ((contin x (k + 2)).2 : ℝ) < toReal₀ x ∧
        toReal₀ x < ((contin x (k + 3)).1 : ℝ) / ((contin x (k + 3)).2 : ℝ)) := by
  have h := infFlips_of_irrational hirr
  obtain ⟨hT, hF⟩ := boundaryMat_eq_contin h (k + 1)
  -- the shared analytic core: for the prefix matrix at boundary `k+2`, the
  -- `B`-column is strictly below the value and the `A`-column strictly above
  have core : ∀ A B C D : ℤ, 0 < C → 0 < D →
      pathMat (prefixWord x (runBoundary x (k + 2))) = (A, B, C, D) →
      (B : ℝ) / (D : ℝ) < toReal₀ x ∧ toReal₀ x < (A : ℝ) / (C : ℝ) := by
    intro A B C D hC hD hm
    set n := runBoundary x (k + 2) with hn
    set s := toReal₀ (shift^[n] x) with hsdef
    have hne := iterate_shift_ne_univ_of_irrational hirr n
    have hs : 0 < s := toReal₀_pos_of_irrational (irrational_toReal₀_iterate_shift hirr n)
    have hCr : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
    have hDr : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
    have hdetr : (A : ℝ) * (D : ℝ) - (B : ℝ) * (C : ℝ) = 1 := by
      have := pathMat_det (prefixWord x n)
      rw [hm] at this
      exact_mod_cast this
    have ht : toReal₀ x = ((A : ℝ) * s + (B : ℝ)) / ((C : ℝ) * s + (D : ℝ)) := by
      rw [toReal₀_eq_mobius_prefixWord x n hne, hm, mobius]
    obtain ⟨hlow, hhigh⟩ := column_errors hCr hDr hs hdetr ht
    have hden : (0 : ℝ) < (C : ℝ) * s + (D : ℝ) := by positivity
    constructor
    · have : (0 : ℝ) < toReal₀ x - (B : ℝ) / (D : ℝ) := by rw [hlow]; positivity
      linarith
    · have : (0 : ℝ) < (A : ℝ) / (C : ℝ) - toReal₀ x := by rw [hhigh]; positivity
      linarith
  have hq2 : 0 < (contin x (k + 2)).2 := contin_den_pos h k
  have hq3 : 0 < (contin x (k + 3)).2 := contin_den_pos h (k + 1)
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · have hm : pathMat (prefixWord x (runBoundary x (k + 2)))
        = ((contin x (k + 2)).1, (contin x (k + 3)).1,
           (contin x (k + 2)).2, (contin x (k + 3)).2) := hT hb
    exact core _ _ _ _ hq2 hq3 hm
  · have hm : pathMat (prefixWord x (runBoundary x (k + 2)))
        = ((contin x (k + 3)).1, (contin x (k + 2)).1,
           (contin x (k + 3)).2, (contin x (k + 2)).2) := hF hb
    exact core _ _ _ _ hq3 hq2 hm

/-- The straddling, stated without reference to `runBit`: the value is strictly
between two consecutive convergents, in one order or the other. -/
theorem toReal₀_strictly_between_contin {x : Set ℕ} (hirr : Irrational (toReal₀ x)) (k : ℕ) :
    (((contin x (k + 2)).1 : ℝ) / ((contin x (k + 2)).2 : ℝ) < toReal₀ x ∧
        toReal₀ x < ((contin x (k + 3)).1 : ℝ) / ((contin x (k + 3)).2 : ℝ)) ∨
      (((contin x (k + 3)).1 : ℝ) / ((contin x (k + 3)).2 : ℝ) < toReal₀ x ∧
        toReal₀ x < ((contin x (k + 2)).1 : ℝ) / ((contin x (k + 2)).2 : ℝ)) := by
  obtain ⟨hT, hF⟩ := contin_straddle hirr k
  cases hb : runBit x (k + 1)
  · exact Or.inl (hF hb)
  · exact Or.inr (hT hb)

/-- A convergent is never *equal* to the value, which is the degenerate case the
straddling rules out. Irrationality is doing the work: a convergent is rational.

Stated because the best-approximation argument needs `qₖ Φ₀x − pₖ ≠ 0` before it
can divide by it. -/
theorem contin_ne_toReal₀ {x : Set ℕ} (hirr : Irrational (toReal₀ x)) (k : ℕ) :
    ((contin x (k + 2)).1 : ℝ) / ((contin x (k + 2)).2 : ℝ) ≠ toReal₀ x := by
  rcases toReal₀_strictly_between_contin hirr k with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact ne_of_lt h1
  · exact ne_of_gt h2

end SternBrocot
