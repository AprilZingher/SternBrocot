/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.CF.Convergent

/-!
# Legendre's theorem

> `|Φ₀x − p/q| < 1/(2q²)` with `q > 0` and `gcd(p, q) = 1` implies `p/q` is a
> convergent.

`legendre` at the end of the file. Everything before it is the machinery, in
four layers, each with its own section:

1. **Consecutive convergents** — unimodularity (`contin_det`) and straddling
   (`contin_straddle`). `Convergent.lean` has the ingredients but never states
   them, because its estimates only ever needed one convergent at a time.
2. **Denominator growth** — strict from index `3`, not `2`; see that section.
3. **Best approximation of the second kind** — the lattice argument, stated
   first as pure arithmetic and then at the convergents.
4. **Where the convergent list starts** — `startIdx`, which is what makes the
   bracketing step work at all.

## The trap that shaped this file

The obvious route to the bracketing step — choose `k` with `qₖ ≤ q < qₖ₊₁` —
fails on the indexing inherited from `Convergent.lean`, and the reason is the
`a₀ = 0` seed swap showing up for the third time. Stated at `k + 2`, the
smallest available denominator is `q₂`, which is `1` on a right-starting path
but `a₀` on a left-starting one — arbitrarily large. So a small `q` would have
no bracket.

The resolution is not to patch the proof but to notice that the convergent list
genuinely starts one index lower on the left branch: `contin x 1 = (0, 1)` *is*
the classical `p₀/q₀` there. `startIdx` names the right index on each branch and
`contin_den_startIdx` shows the denominator is `1` at that index either way, so
every `q ≥ 1` is bracketable after all.

Note also that bracketing needs only **monotonicity and unboundedness**, not
strict increase — take the *greatest* index with `qⱼ ≤ q`. That is why the
`q₂ = q₃` repeat, which forced `contin_den_lt_succ` up to `k + 3`, costs nothing
here.

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

Not used by anything here — `abs_le_of_lattice` never divides by the error, so
the justification this docstring used to give was fiction. Kept as a leaf for
the Legendre finish, which compares `p/q` against `pₖ/qₖ` as fractions and does
need them distinct. -/
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

/-! ### The estimate at the convergents

Instantiating the lattice lemma. The only work is clearing denominators:
`contin_straddle` compares *fractions* `pₖ/qₖ` against `Φ₀x`, while
`abs_le_of_lattice` wants the sign of `qₖ Φ₀x − pₖ`. -/

/-- The two signed errors at consecutive convergents have opposite signs. This is
`contin_straddle` with the positive denominators cleared. -/
theorem contin_err_mul_neg {x : Set ℕ} (hirr : Irrational (toReal₀ x)) (k : ℕ) :
    (((contin x (k + 2)).2 : ℝ) * toReal₀ x - ((contin x (k + 2)).1 : ℝ))
      * (((contin x (k + 3)).2 : ℝ) * toReal₀ x - ((contin x (k + 3)).1 : ℝ)) < 0 := by
  have h := infFlips_of_irrational hirr
  have hq2 : (0 : ℝ) < ((contin x (k + 2)).2 : ℝ) := by exact_mod_cast contin_den_pos h k
  have hq3 : (0 : ℝ) < ((contin x (k + 3)).2 : ℝ) := by exact_mod_cast contin_den_pos h (k + 1)
  rcases toReal₀_strictly_between_contin hirr k with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [div_lt_iff₀ hq2] at h1
    rw [lt_div_iff₀ hq3] at h2
    nlinarith
  · rw [div_lt_iff₀ hq3] at h1
    rw [lt_div_iff₀ hq2] at h2
    nlinarith

/-- **Best approximation of the second kind, at the convergents.** No integer
pair with `0 < q < qₖ₊₁` approximates `Φ₀x` better than `(pₖ, qₖ)` does, measured
by `|qα − p|`. -/
theorem contin_best_approx {x : Set ℕ} (hirr : Irrational (toReal₀ x)) (k : ℕ)
    {p q : ℤ} (hq0 : 0 < q) (hqd : q < (contin x (k + 3)).2) :
    |((contin x (k + 2)).2 : ℝ) * toReal₀ x - ((contin x (k + 2)).1 : ℝ)|
      ≤ |(q : ℝ) * toReal₀ x - (p : ℝ)| := by
  have h := infFlips_of_irrational hirr
  have hc : 0 < (contin x (k + 2)).2 := contin_den_pos h k
  have hd : 0 < (contin x (k + 3)).2 := contin_den_pos h (k + 1)
  have hdet : (contin x (k + 2)).1 * (contin x (k + 3)).2
        - (contin x (k + 3)).1 * (contin x (k + 2)).2 = 1
      ∨ (contin x (k + 2)).1 * (contin x (k + 3)).2
        - (contin x (k + 3)).1 * (contin x (k + 2)).2 = -1 := by
    have := abs_contin_det h k
    rcases abs_eq (by norm_num : (0:ℤ) ≤ 1) |>.1 this with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  obtain ⟨u, v, hp, hqe⟩ := exists_lattice_coords hdet p q
  have hkey := abs_le_of_lattice (c := (contin x (k + 2)).2) (d := (contin x (k + 3)).2)
    (A := ((contin x (k + 2)).2 : ℝ) * toReal₀ x - ((contin x (k + 2)).1 : ℝ))
    (B := ((contin x (k + 3)).2 : ℝ) * toReal₀ x - ((contin x (k + 3)).1 : ℝ))
    hc hd (contin_err_mul_neg hirr k) hq0 hqd hqe
  refine le_trans hkey (le_of_eq ?_)
  congr 1
  subst hp
  subst hqe
  push_cast
  ring

/-! ### Lowering the index: where the convergent list really starts

Everything above is stated at `k + 2`, inherited from `Convergent.lean`. For
Legendre that is one too high, and the reason is again the `a₀ = 0` seed swap.

The convergent list *does* start at denominator `1` — but at a different index
on each branch:

| first run | `contin x 1` | `contin x 2` |
|---|---|---|
| right (`runBit x 0 = true`) | `(1, 0)` = `1/0`, not a convergent | `(a₀, 1)` — the classical `p₀/q₀` |
| left (`runBit x 0 = false`) | `(0, 1)` — the classical `p₀/q₀` | `(1, a₀)` = `p₁/q₁` |

So on a left-starting path the genuine first convergent sits at index `1`, below
the range every estimate above is stated on, and skipping it is what made
`q₃` look like an unbounded obstruction. `startIdx` names the right starting
index and `contin_den_startIdx` says the denominator there is `1` on both
branches — so *every* `q ≥ 1` is bracketable after all.

Note the bracketing needs only **monotonicity and unboundedness**, not strict
increase: take the *greatest* index with `qⱼ ≤ q`. That is why the `q₂ = q₃`
repeat, which forced `contin_den_lt_succ` up to `k + 3`, costs nothing here. -/

/-- The index at which the genuine convergents begin: `2` on a right-starting
path, `1` on a left-starting one. -/
noncomputable def startIdx (x : Set ℕ) : ℕ := if runBit x 0 then 2 else 1

theorem one_le_startIdx (x : Set ℕ) : 1 ≤ startIdx x := by
  unfold startIdx; split <;> omega

/-- **The convergent list starts at denominator `1`**, on both branches. -/
theorem contin_den_startIdx (x : Set ℕ) : (contin x (startIdx x)).2 = 1 := by
  cases hb : runBit x 0
  · have hs : startIdx x = 1 := by simp [startIdx, hb]
    rw [hs]
    show (contin x 1).2 = 1
    simp [contin_one, hb]
  · have hs : startIdx x = 2 := by simp [startIdx, hb]
    rw [hs]
    have e2 := contin_den_add_two x 0
    have h0 : contin x 0 = (0, 1) := by simp [contin_zero, hb]
    have h1 : contin x 1 = (1, 0) := by simp [contin_one, hb]
    rw [h0, h1] at e2
    show (contin x 2).2 = 1
    simpa using e2

/-- Monotonicity of the denominators from index `1` on. -/
theorem contin_den_mono {x : Set ℕ} (h : InfFlips x) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    (contin x i).2 ≤ (contin x j).2 := by
  obtain ⟨m, rfl⟩ : ∃ m, j = i + m := ⟨j - i, by omega⟩
  clear hij
  induction m with
  | zero => simp
  | succ n ih =>
    refine le_trans ih ?_
    obtain ⟨t, ht⟩ : ∃ t, i + n = t + 1 := ⟨i + n - 1, by omega⟩
    have ht2 : i + (n + 1) = t + 2 := by omega
    rw [ht, ht2]
    exact contin_den_le_succ h t

theorem contin_den_pos_of_startIdx {x : Set ℕ} (h : InfFlips x) {j : ℕ}
    (hj : startIdx x ≤ j) : 0 < (contin x j).2 := by
  have := contin_den_mono h (one_le_startIdx x) hj
  rw [contin_den_startIdx] at this
  omega

/-! ### The pair lemmas, one index lower

Restatements of `contin_det` and `contin_straddle` at `(j+1, j+2)` rather than
`(k+2, k+3)`, with positivity passed in rather than derived. The proofs are the
same reading of `boundaryMat_eq_contin`, at boundary `j+1` instead of `k+2`. -/

theorem contin_det_gen {x : Set ℕ} (h : InfFlips x) (j : ℕ) :
    (contin x (j + 1)).1 * (contin x (j + 2)).2
        - (contin x (j + 2)).1 * (contin x (j + 1)).2 = 1
      ∨ (contin x (j + 1)).1 * (contin x (j + 2)).2
        - (contin x (j + 2)).1 * (contin x (j + 1)).2 = -1 := by
  obtain ⟨hT, hF⟩ := boundaryMat_eq_contin h j
  have hdet := pathMat_det (prefixWord x (runBoundary x (j + 1)))
  cases hb : runBit x j
  · have hm : pathMat (prefixWord x (runBoundary x (j + 1)))
        = ((contin x (j + 2)).1, (contin x (j + 1)).1,
           (contin x (j + 2)).2, (contin x (j + 1)).2) := hF hb
    rw [hm] at hdet
    exact Or.inr (by linarith)
  · have hm : pathMat (prefixWord x (runBoundary x (j + 1)))
        = ((contin x (j + 1)).1, (contin x (j + 2)).1,
           (contin x (j + 1)).2, (contin x (j + 2)).2) := hT hb
    rw [hm] at hdet
    exact Or.inl hdet

theorem contin_err_mul_neg_gen {x : Set ℕ} (hirr : Irrational (toReal₀ x)) (j : ℕ)
    (h1 : 0 < (contin x (j + 1)).2) (h2 : 0 < (contin x (j + 2)).2) :
    (((contin x (j + 1)).2 : ℝ) * toReal₀ x - ((contin x (j + 1)).1 : ℝ))
      * (((contin x (j + 2)).2 : ℝ) * toReal₀ x - ((contin x (j + 2)).1 : ℝ)) < 0 := by
  have h := infFlips_of_irrational hirr
  obtain ⟨hT, hF⟩ := boundaryMat_eq_contin h j
  have h1r : (0 : ℝ) < ((contin x (j + 1)).2 : ℝ) := by exact_mod_cast h1
  have h2r : (0 : ℝ) < ((contin x (j + 2)).2 : ℝ) := by exact_mod_cast h2
  have core : ∀ A B C D : ℤ, 0 < C → 0 < D →
      pathMat (prefixWord x (runBoundary x (j + 1))) = (A, B, C, D) →
      (B : ℝ) / (D : ℝ) < toReal₀ x ∧ toReal₀ x < (A : ℝ) / (C : ℝ) := by
    intro A B C D hC hD hm
    set n := runBoundary x (j + 1) with hn
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
    · have hpos : (0 : ℝ) < toReal₀ x - (B : ℝ) / (D : ℝ) := by rw [hlow]; positivity
      linarith
    · have hpos : (0 : ℝ) < (A : ℝ) / (C : ℝ) - toReal₀ x := by rw [hhigh]; positivity
      linarith
  cases hb : runBit x j
  · have hm : pathMat (prefixWord x (runBoundary x (j + 1)))
        = ((contin x (j + 2)).1, (contin x (j + 1)).1,
           (contin x (j + 2)).2, (contin x (j + 1)).2) := hF hb
    obtain ⟨hlo, hhi⟩ := core _ _ _ _ h2 h1 hm
    rw [div_lt_iff₀ h1r] at hlo
    rw [lt_div_iff₀ h2r] at hhi
    nlinarith
  · have hm : pathMat (prefixWord x (runBoundary x (j + 1)))
        = ((contin x (j + 1)).1, (contin x (j + 2)).1,
           (contin x (j + 1)).2, (contin x (j + 2)).2) := hT hb
    obtain ⟨hlo, hhi⟩ := core _ _ _ _ h1 h2 hm
    rw [div_lt_iff₀ h2r] at hlo
    rw [lt_div_iff₀ h1r] at hhi
    nlinarith

/-- **Best approximation of the second kind**, at the true starting index. -/
theorem contin_best_approx_gen {x : Set ℕ} (hirr : Irrational (toReal₀ x)) (j : ℕ)
    (h1 : 0 < (contin x (j + 1)).2) (h2 : 0 < (contin x (j + 2)).2)
    {p q : ℤ} (hq0 : 0 < q) (hqd : q < (contin x (j + 2)).2) :
    |((contin x (j + 1)).2 : ℝ) * toReal₀ x - ((contin x (j + 1)).1 : ℝ)|
      ≤ |(q : ℝ) * toReal₀ x - (p : ℝ)| := by
  have h := infFlips_of_irrational hirr
  obtain ⟨u, v, hp, hqe⟩ := exists_lattice_coords (contin_det_gen h j) p q
  have hkey := abs_le_of_lattice (c := (contin x (j + 1)).2) (d := (contin x (j + 2)).2)
    (A := ((contin x (j + 1)).2 : ℝ) * toReal₀ x - ((contin x (j + 1)).1 : ℝ))
    (B := ((contin x (j + 2)).2 : ℝ) * toReal₀ x - ((contin x (j + 2)).1 : ℝ))
    h1 h2 (contin_err_mul_neg_gen hirr j h1 h2) hq0 hqd hqe
  refine le_trans hkey (le_of_eq ?_)
  congr 1
  subst hp
  subst hqe
  push_cast
  ring

theorem startIdx_le_two (x : Set ℕ) : startIdx x ≤ 2 := by
  unfold startIdx; split <;> omega

/-- Coprimality of the convergent at any index, from the general determinant. -/
theorem contin_coprime_gen {x : Set ℕ} (h : InfFlips x) (j : ℕ) :
    IsCoprime (contin x (j + 1)).1 (contin x (j + 1)).2 := by
  rcases contin_det_gen h j with he | he
  · exact ⟨(contin x (j + 2)).2, -(contin x (j + 2)).1, by linear_combination he⟩
  · exact ⟨-(contin x (j + 2)).2, (contin x (j + 2)).1, by linear_combination -he⟩

/-! ### Bracketing

The denominators are monotone from index `1`, unbounded, and equal to `1` at
`startIdx`. So for any `q ≥ 1` the *greatest* index with `qⱼ ≤ q` exists and
brackets `q`. Strict increase is not needed — which is what makes the `q₂ = q₃`
repeat harmless here. -/

theorem exists_bracket {x : Set ℕ} (h : InfFlips x) {q : ℤ} (hq : 1 ≤ q) :
    ∃ j : ℕ, startIdx x ≤ j ∧ (contin x j).2 ≤ q ∧ q < (contin x (j + 1)).2 := by
  classical
  obtain ⟨N0, hN0⟩ := exists_contin_den_gt h q
  set N := N0 + 3 with hNdef
  set P : ℕ → Prop := fun j => (contin x j).2 ≤ q with hPdef
  have hPstart : P (startIdx x) := by
    show (contin x (startIdx x)).2 ≤ q
    rw [contin_den_startIdx]; exact hq
  have hsN : startIdx x ≤ N := le_trans (startIdx_le_two x) (by omega)
  have hNnot : ¬ P N := by show ¬ ((contin x N).2 ≤ q); push_neg; exact hN0
  set j := Nat.findGreatest P N with hjdef
  have hjs : startIdx x ≤ j := Nat.le_findGreatest hsN hPstart
  have hPj : P j := Nat.findGreatest_spec hsN hPstart
  have hjN : j ≤ N := Nat.findGreatest_le N
  have hjltN : j < N := lt_of_le_of_ne hjN (fun heq => hNnot (heq ▸ hPj))
  have hnext : ¬ P (j + 1) :=
    Nat.findGreatest_is_greatest (by rw [← hjdef]; omega) (by omega)
  refine ⟨j, hjs, hPj, ?_⟩
  show q < (contin x (j + 1)).2
  by_contra hc
  exact hnext (by show (contin x (j + 1)).2 ≤ q; omega)

/-! ### Legendre's theorem

If `p/q` approximates `Φ₀x` to better than `1/(2q²)`, it **is** a convergent.

The classical proof. Bracket `q` between consecutive convergent denominators;
best approximation gives `|qⱼα − pⱼ| ≤ |qα − p| < 1/(2q)`; then if `p/q` and
`pⱼ/qⱼ` were distinct they would differ by at least `1/(q qⱼ)`, while the
triangle inequality caps the difference at exactly that — a strict-versus-
non-strict contradiction. Coprimality upgrades equality of fractions to equality
of pairs. -/

/-- **Legendre's theorem.** -/
theorem legendre {x : Set ℕ} (hirr : Irrational (toReal₀ x)) {p q : ℤ}
    (hq0 : 0 < q) (hcop : IsCoprime p q)
    (happrox : |toReal₀ x - (p : ℝ) / (q : ℝ)| < 1 / (2 * (q : ℝ) ^ 2)) :
    ∃ j : ℕ, startIdx x ≤ j ∧ contin x j = (p, q) := by
  have h := infFlips_of_irrational hirr
  obtain ⟨j, hjs, hle, hlt⟩ := exists_bracket h hq0
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by have := one_le_startIdx x; omega⟩
  set pj := (contin x (i + 1)).1 with hpj
  set qj := (contin x (i + 1)).2 with hqj
  have hd1 : 0 < qj := contin_den_pos_of_startIdx h hjs
  have hd2 : 0 < (contin x (i + 2)).2 := contin_den_pos_of_startIdx h (by omega)
  have hbest := contin_best_approx_gen hirr i hd1 hd2 (p := p) hq0 hlt
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hd1R : (0 : ℝ) < (qj : ℝ) := by exact_mod_cast hd1
  -- `|qα − p| < 1/(2q)`
  have hqp : |(q : ℝ) * toReal₀ x - (p : ℝ)| < 1 / (2 * (q : ℝ)) := by
    have hfac : (q : ℝ) * toReal₀ x - (p : ℝ)
        = (q : ℝ) * (toReal₀ x - (p : ℝ) / (q : ℝ)) := by field_simp
    rw [hfac, abs_mul, abs_of_pos hqR]
    have := mul_lt_mul_of_pos_left happrox hqR
    calc (q : ℝ) * |toReal₀ x - (p : ℝ) / (q : ℝ)|
        < (q : ℝ) * (1 / (2 * (q : ℝ) ^ 2)) := this
      _ = 1 / (2 * (q : ℝ)) := by field_simp
  -- hence `|α − pⱼ/qⱼ| < 1/(2 q qⱼ)`
  have hconv : |toReal₀ x - (pj : ℝ) / (qj : ℝ)| < 1 / (2 * (q : ℝ) * (qj : ℝ)) := by
    have hqjne : (qj : ℝ) ≠ 0 := ne_of_gt hd1R
    have hfac2 : (qj : ℝ) * toReal₀ x - (pj : ℝ)
        = (qj : ℝ) * (toReal₀ x - (pj : ℝ) / (qj : ℝ)) := by field_simp
    rw [hfac2, abs_mul, abs_of_pos hd1R] at hbest
    have h2 := lt_of_le_of_lt hbest hqp
    rw [lt_div_iff₀ (by positivity)] at h2
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  -- the two fractions coincide
  have hcross : p * qj = pj * q := by
    by_contra hne
    have hDne : p * qj - pj * q ≠ 0 := fun h0 => hne (by linarith)
    have hZ : (1 : ℤ) ≤ |p * qj - pj * q| := Int.one_le_abs hDne
    have hR : (1 : ℝ) ≤ |((p * qj - pj * q : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast hZ
    push_cast at hR
    have hsplit : |(p : ℝ) / (q : ℝ) - (pj : ℝ) / (qj : ℝ)|
        = |(p : ℝ) * (qj : ℝ) - (pj : ℝ) * (q : ℝ)| / ((q : ℝ) * (qj : ℝ)) := by
      rw [div_sub_div _ _ (ne_of_gt hqR) (ne_of_gt hd1R), abs_div,
        abs_of_pos (by positivity : (0 : ℝ) < (q : ℝ) * (qj : ℝ)),
        show (q : ℝ) * (pj : ℝ) = (pj : ℝ) * (q : ℝ) from mul_comm _ _]
    have hqjq : (qj : ℝ) ≤ (q : ℝ) := by exact_mod_cast hle
    have htri : |(p : ℝ) / (q : ℝ) - (pj : ℝ) / (qj : ℝ)|
        ≤ |toReal₀ x - (p : ℝ) / (q : ℝ)| + |toReal₀ x - (pj : ℝ) / (qj : ℝ)| := by
      have := abs_sub_le ((p : ℝ) / (q : ℝ)) (toReal₀ x) ((pj : ℝ) / (qj : ℝ))
      rwa [abs_sub_comm ((p : ℝ) / (q : ℝ)) (toReal₀ x)] at this
    rw [hsplit, div_le_iff₀ (by positivity)] at htri
    have hstep : 1 / (2 * (q : ℝ) ^ 2) ≤ 1 / (2 * (q : ℝ) * (qj : ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    -- the two errors together are smaller than `1/(q qⱼ)`, so the product is `< 1`
    have hsum : |toReal₀ x - (p : ℝ) / (q : ℝ)| + |toReal₀ x - (pj : ℝ) / (qj : ℝ)|
        < 2 * (1 / (2 * (q : ℝ) * (qj : ℝ))) := by
      have h1 : |toReal₀ x - (p : ℝ) / (q : ℝ)| < 1 / (2 * (q : ℝ) * (qj : ℝ)) :=
        lt_of_lt_of_le happrox hstep
      linarith [hconv]
    have hfin : (|toReal₀ x - (p : ℝ) / (q : ℝ)| + |toReal₀ x - (pj : ℝ) / (qj : ℝ)|)
        * ((q : ℝ) * (qj : ℝ)) < 1 := by
      have hpos : (0 : ℝ) < (q : ℝ) * (qj : ℝ) := by positivity
      have hmul := mul_lt_mul_of_pos_right hsum hpos
      rwa [show 2 * (1 / (2 * (q : ℝ) * (qj : ℝ))) * ((q : ℝ) * (qj : ℝ)) = 1 by
        field_simp] at hmul
    linarith [hR, htri, hfin]
  -- coprimality upgrades that to equality of pairs
  have hcopj : IsCoprime pj qj := contin_coprime_gen h i
  have hdvd1 : q ∣ qj := (hcop.symm).dvd_of_dvd_mul_left ⟨pj, by rw [hcross]; ring⟩
  have hdvd2 : qj ∣ q := (hcopj.symm).dvd_of_dvd_mul_left ⟨p, by rw [← hcross]; ring⟩
  have hqeq : q = qj := Int.dvd_antisymm (le_of_lt hq0) (le_of_lt hd1) hdvd1 hdvd2
  have hpeq : pj = p := by
    have hmul : p * qj = pj * qj := by rw [hcross, ← hqeq]
    have hne0 : qj ≠ 0 := by omega
    exact (mul_right_cancel₀ hne0 hmul).symm
  exact ⟨i + 1, hjs, Prod.ext_iff.mpr ⟨hpeq, hqeq.symm⟩⟩

end SternBrocot



