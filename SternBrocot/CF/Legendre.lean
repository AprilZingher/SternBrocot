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

/-! ### The denominators grow — but not from where you would guess

Legendre's theorem picks the index `k` with `qₖ ≤ q < qₖ₊₁`, which needs the
denominators to actually increase. `contin_den_le_succ` gives only `≤`, and the
strict version is **false at the first step**: `contin_goldenPath` makes
`q₂ = q₃ = 1`, recorded as `contin_den_eq_goldenPath` in `Examples.lean`.

The reason is the `a₀ = 0` seed swap. One of `q₀, q₁` is `0`, so the recurrence
`qₖ₊₂ = aₖ qₖ₊₁ + qₖ` has nothing to add at the first step and `a₁ = 1` leaves
`q₃ = q₂`. From index `3` on, both `qₖ` and `qₖ₊₁` are positive and the strict
increase is immediate. So every statement below starts at `k + 3`, one higher
than the `k + 2` used everywhere else — do not "simplify" it back down. -/

/-- **The convergent denominators strictly increase**, from index `3`.

Not from index `2`: see `contin_den_eq_goldenPath`. -/
theorem contin_den_lt_succ {x : Set ℕ} (h : InfFlips x) (k : ℕ) :
    (contin x (k + 3)).2 < (contin x (k + 4)).2 := by
  have hrec : (contin x (k + 4)).2
      = (partialQuot x (k + 2) : ℤ) * (contin x (k + 3)).2 + (contin x (k + 2)).2 :=
    contin_den_add_two x (k + 2)
  have ha : 1 ≤ (partialQuot x (k + 2) : ℤ) := by
    exact_mod_cast partialQuot_pos h (k + 2)
  have h3 : 0 < (contin x (k + 3)).2 := contin_den_pos h (k + 1)
  have h2 : 0 < (contin x (k + 2)).2 := contin_den_pos h k
  nlinarith

/-- A linear lower bound, which is what makes the denominators unbounded. -/
theorem contin_den_ge {x : Set ℕ} (h : InfFlips x) (k : ℕ) :
    (k : ℤ) + 1 ≤ (contin x (k + 3)).2 := by
  induction k with
  | zero =>
    have h1 : 0 < (contin x 3).2 := contin_den_pos h 1
    show ((0 : ℕ) : ℤ) + 1 ≤ (contin x 3).2
    push_cast
    omega
  | succ j ih =>
    have hlt := contin_den_lt_succ h j
    -- `j + 1 + 3` and `j + 4` are defeq but not syntactically equal; see the
    -- indexing trap noted above
    have hidx : (contin x (j + 1 + 3)).2 = (contin x (j + 4)).2 := rfl
    rw [hidx]
    push_cast
    omega

/-- **The denominators are unbounded**, which is what lets Legendre's theorem
choose an index bracketing a given `q`. -/
theorem exists_contin_den_gt {x : Set ℕ} (h : InfFlips x) (M : ℤ) :
    ∃ k : ℕ, M < (contin x (k + 3)).2 := by
  refine ⟨M.toNat, lt_of_lt_of_le ?_ (contin_den_ge h M.toNat)⟩
  have := Int.self_le_toNat M
  omega

/-! ### Best approximation of the second kind

The lattice step. Unimodularity makes two consecutive convergents a basis of
`ℤ²`, so *every* integer pair `(p, q)` is `u·(pₖ,qₖ) + v·(pₖ₊₁,qₖ₊₁)`; the
straddling makes the two errors `qₖα − pₖ` and `qₖ₊₁α − pₖ₊₁` opposite in sign,
so the contributions can never cancel. The bound `q < qₖ₊₁` forces `u` and `v`
to have opposite signs too, and opposite-signed coefficients against
opposite-signed errors point the *same* way — so the two terms add in absolute
value instead of cancelling.

Stated as pure arithmetic: nothing below mentions continued fractions, and
keeping it separate is what makes the case analysis readable. -/

/-- Unimodularity makes the two columns a basis of `ℤ²`. -/
theorem exists_lattice_coords {a b c d : ℤ} (hdet : a * d - b * c = 1 ∨ a * d - b * c = -1)
    (p q : ℤ) : ∃ u v : ℤ, p = u * a + v * b ∧ q = u * c + v * d := by
  rcases hdet with he | he
  · exact ⟨d * p - b * q, a * q - c * p,
      by linear_combination (-p) * he, by linear_combination (-q) * he⟩
  · exact ⟨b * q - d * p, c * p - a * q,
      by linear_combination p * he, by linear_combination q * he⟩

/-- **The lattice estimate.** With `A`, `B` the two signed errors — opposite in
sign, which is `contin_straddle` — and `0 < q < d`, no integer combination
realising such a `q` can beat `|A|`. -/
theorem abs_le_of_lattice {c d q u v : ℤ} {A B : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hAB : A * B < 0)
    (hq0 : 0 < q) (hqd : q < d) (hqe : q = u * c + v * d) :
    |A| ≤ |(u : ℝ) * A + (v : ℝ) * B| := by
  have hA0 : A ≠ 0 := by rintro rfl; simp at hAB
  -- `u = 0` would force `d ≤ q`
  have hu0 : u ≠ 0 := by
    rintro rfl
    have hv : 1 ≤ v := by nlinarith
    nlinarith
  rcases eq_or_ne v 0 with rfl | hv0
  · -- `v = 0`: then `q = u c` with `u ≥ 1`, so the term is a multiple of `A`
    have hu : 1 ≤ u := by nlinarith
    have huR : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
    rw [Int.cast_zero, zero_mul, add_zero, abs_mul,
      abs_of_pos (by linarith : (0 : ℝ) < (u : ℝ))]
    nlinarith [abs_nonneg A]
  · -- both nonzero, hence of opposite signs: same signs would break `0 < q < d`
    have hopp : (1 ≤ u ∧ v ≤ -1) ∨ (u ≤ -1 ∧ 1 ≤ v) := by
      rcases lt_trichotomy u 0 with h1 | h1 | h1
      · rcases lt_trichotomy v 0 with h2 | h2 | h2
        · exfalso; nlinarith
        · exact absurd h2 hv0
        · exact Or.inr ⟨by omega, by omega⟩
      · exact absurd h1 hu0
      · rcases lt_trichotomy v 0 with h2 | h2 | h2
        · exact Or.inl ⟨by omega, by omega⟩
        · exact absurd h2 hv0
        · exfalso; nlinarith
    rcases hopp with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · have huR : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
      have hvR : (v : ℝ) ≤ -1 := by exact_mod_cast hv
      rcases lt_or_gt_of_ne hA0 with hAneg | hApos
      · have hB : 0 < B := by nlinarith
        rw [abs_of_neg hAneg,
          abs_of_neg (by nlinarith : (u : ℝ) * A + (v : ℝ) * B < 0)]
        nlinarith
      · have hB : B < 0 := by nlinarith
        rw [abs_of_pos hApos,
          abs_of_pos (by nlinarith : (0 : ℝ) < (u : ℝ) * A + (v : ℝ) * B)]
        nlinarith
    · have huR : (u : ℝ) ≤ -1 := by exact_mod_cast hu
      have hvR : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
      rcases lt_or_gt_of_ne hA0 with hAneg | hApos
      · have hB : 0 < B := by nlinarith
        rw [abs_of_neg hAneg,
          abs_of_pos (by nlinarith : (0 : ℝ) < (u : ℝ) * A + (v : ℝ) * B)]
        nlinarith
      · have hB : B < 0 := by nlinarith
        rw [abs_of_pos hApos,
          abs_of_neg (by nlinarith : (u : ℝ) * A + (v : ℝ) * B < 0)]
        nlinarith

end SternBrocot
