/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Convergent
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Hurwitz's theorem

Every irrational `t` is approximated by infinitely many rationals to within
`1/(√5 q²)`, and `√5` cannot be improved.

## The shape of the proof in this encoding

`Convergent.lean` gives the error of a convergent **exactly**:

  `|Φ₀ x − pⱼ/qⱼ| = 1/(qⱼ (qⱼ wⱼ + qⱼ₊₁))`,

so dividing by `qⱼ²`, the `j`-th convergent beats `1/(√5 q²)` precisely when

  `λⱼ := wⱼ + ρⱼ > √5`,   `ρⱼ = qⱼ₊₁/qⱼ`.

The two recurrences `1/wⱼ = aⱼ + wⱼ₊₁` and `ρⱼ₊₁ = aⱼ + 1/ρⱼ` carry the *same*
partial quotient, so they combine into the one relation the whole theorem needs:

  `λⱼ₊₁ = 1/wⱼ + 1/ρⱼ`.

Hurwitz is then a statement about a pair of positive reals. If three consecutive
`λ` are all `≤ √5` then, writing `X = 1/wⱼ` and `Y = 1/ρⱼ`,

  `X + Y ≤ √5`,  `1/X + 1/Y ≤ √5`,  `X − Y ≥ 1`,

and those three force `X + Y = √5` and `X Y = 1` exactly — hence `ρⱼ = φ`. But
`ρⱼ` is a ratio of integers. That contradiction is the theorem: among any three
consecutive convergents at least one satisfies the bound.

## Why `√5` is the right constant, visibly

`ρⱼ = φ` is the impossible conclusion, and `φ` is exactly the value the ratio of
successive convergent denominators *approaches* for the all-run-length-one path.
So the extremal case is the golden path `{n | Even n}`, whose partial quotients
are all `1` (`partialQuot_goldenPath`) and whose continuants are the Fibonacci
numbers (`contin_goldenPath`). `sqrt5_optimal` makes that precise.

## Main results

* `SternBrocot.exists_hurwitz_approx` — **Hurwitz**: for every bound `M` there is
  a `p/q` with `q > M` and `|Φ₀ x − p/q| < 1/(√5 q²)`. This is "infinitely many"
  without the `Set.Infinite` bookkeeping.
* `SternBrocot.sqrt5_optimal` — no constant larger than `√5` works for `φ`.
-/

open Set

namespace SternBrocot

/-! ### Two lemmas about a pair of positive reals

Both are the same computation: for `s = X + Y` and `P = X Y`, the hypothesis
`1/X + 1/Y ≤ √5` says `s ≤ √5 P`, and `√5 s² − 4 s − √5` factors as
`(s − √5)(√5 s + 1)`. -/

private theorem sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

private theorem sqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)

private theorem inv_add_inv_le {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (h : X⁻¹ + Y⁻¹ ≤ Real.sqrt 5) : X + Y ≤ Real.sqrt 5 * (X * Y) := by
  have hP : 0 < X * Y := mul_pos hX hY
  have he : X⁻¹ + Y⁻¹ = (X + Y) / (X * Y) := by field_simp; ring
  rw [he, div_le_iff₀ hP] at h
  linarith

/-- **Hurwitz's lemma, first half.** If `X + Y` and `1/X + 1/Y` are both at most
`√5` then `X` and `Y` differ by at most `1`. -/
private theorem sq_sub_le_one {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (h1 : X + Y ≤ Real.sqrt 5) (h2 : X⁻¹ + Y⁻¹ ≤ Real.sqrt 5) : (X - Y) ^ 2 ≤ 1 := by
  have h5 := sqrt5_sq
  have h5pos := sqrt5_pos
  have h2' := inv_add_inv_le hX hY h2
  have hfac : 0 ≤ (Real.sqrt 5 - (X + Y)) * (Real.sqrt 5 * (X + Y) + 1) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith [hfac, h2', h5, h5pos]

/-- **Hurwitz's lemma, second half.** Adding `X − Y ≥ 1` to the same hypotheses
pins `X` and `Y` down completely: the inequalities become equalities and `Y` is
`1/φ`. -/
private theorem eq_of_sub_one_le {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (h1 : X + Y ≤ Real.sqrt 5) (h2 : X⁻¹ + Y⁻¹ ≤ Real.sqrt 5) (h3 : 1 ≤ X - Y) :
    Y = (Real.sqrt 5 - 1) / 2 := by
  have h5 := sqrt5_sq
  have h5pos := sqrt5_pos
  have h2' := inv_add_inv_le hX hY h2
  -- `(X−Y)² ≥ 1` bounds the product, and that forces `X + Y = √5`
  have hsq : 1 ≤ (X - Y) ^ 2 := by nlinarith
  have hs : X + Y = Real.sqrt 5 := by
    refine le_antisymm h1 ?_
    nlinarith [hsq, h2', h5, h5pos, mul_pos hX hY]
  have hP : X * Y = 1 := by nlinarith [hsq, h2', hs, h5]
  have hdiff : X - Y = 1 := by nlinarith [hs, hP, h3, h5]
  linarith

/-! ### The failure condition

The `j`-th convergent misses the Hurwitz bound exactly when `wⱼ + ρⱼ ≤ √5`. -/

/-- `λⱼ = wⱼ + ρⱼ`: the quantity that decides whether convergent `j` beats
`1/(√5 q²)`. -/
noncomputable def hurwitzSum (x : Set ℕ) (j : ℕ) : ℝ := tailQuot x j + denRatio x j

/-- **The one relation Hurwitz needs.** The complete quotients and the
denominator ratios satisfy recurrences with the same partial quotient, so it
cancels. -/
theorem hurwitzSum_succ {x : Set ℕ} (hirr : Irrational (toReal₀ x)) (k : ℕ) :
    hurwitzSum x (k + 3) = (tailQuot x (k + 2))⁻¹ + (denRatio x (k + 2))⁻¹ := by
  have h := infFlips_of_irrational hirr
  have hw := inv_tailQuot hirr (k + 2)
  have hr := denRatio_succ h k
  rw [hurwitzSum, hr]
  have : tailQuot x (k + 3) = (tailQuot x (k + 2))⁻¹ - (partialQuot x (k + 2) : ℝ) := by
    rw [hw]; ring
  rw [this]
  ring

theorem tailQuot_pos' {x : Set ℕ} (hirr : Irrational (toReal₀ x)) (j : ℕ) : 0 < tailQuot x j :=
  tailQuot_pos hirr j

theorem denRatio_pos {x : Set ℕ} (h : InfFlips x) (k : ℕ) : 0 < denRatio x (k + 2) :=
  lt_of_lt_of_le one_pos (one_le_denRatio h k)

/-- **Missing the bound is `λⱼ ≤ √5`.** -/
theorem hurwitzSum_le_iff {x : Set ℕ} (hirr : Irrational (toReal₀ x)) (k : ℕ) :
    ¬ |toReal₀ x - ((contin x (k + 2)).1 : ℝ) / ((contin x (k + 2)).2 : ℝ)|
        < 1 / (Real.sqrt 5 * ((contin x (k + 2)).2 : ℝ) ^ 2)
      ↔ hurwitzSum x (k + 2) ≤ Real.sqrt 5 := by
  have h := infFlips_of_irrational hirr
  have hq : (0 : ℝ) < ((contin x (k + 2)).2 : ℝ) := by exact_mod_cast contin_den_pos h k
  have hq' : (0 : ℝ) < ((contin x (k + 3)).2 : ℝ) := by exact_mod_cast contin_den_pos h (k + 1)
  have hw : 0 < tailQuot x (k + 2) := tailQuot_pos hirr (k + 2)
  have h5 := sqrt5_pos
  have hpos : 0 < ((contin x (k + 2)).2 : ℝ) * tailQuot x (k + 2) + ((contin x (k + 3)).2 : ℝ) := by
    positivity
  rw [abs_sub_contin_eq hirr k, not_lt, hurwitzSum, denRatio,
    div_le_div_iff₀ (by positivity) (by positivity)]
  constructor
  · intro hle
    have h2 : ((contin x (k + 3)).2 : ℝ) / ((contin x (k + 2)).2 : ℝ)
        ≤ Real.sqrt 5 - tailQuot x (k + 2) := by
      rw [div_le_iff₀ hq]; nlinarith
    linarith
  · intro hle
    have h2 : ((contin x (k + 3)).2 : ℝ) / ((contin x (k + 2)).2 : ℝ)
        ≤ Real.sqrt 5 - tailQuot x (k + 2) := by linarith
    rw [div_le_iff₀ hq] at h2
    nlinarith

/-! ### Three consecutive convergents cannot all fail -/

/-- **The heart of Hurwitz.** If the convergents at `k`, `k+1` and `k+2` all miss
the bound then the ratio `qₖ₊₃/qₖ₊₂` is forced to be exactly `φ` — impossible,
since it is a ratio of integers. -/
theorem not_three_consecutive_fail {x : Set ℕ} (hirr : Irrational (toReal₀ x)) (k : ℕ)
    (h0 : hurwitzSum x (k + 2) ≤ Real.sqrt 5)
    (h1 : hurwitzSum x (k + 3) ≤ Real.sqrt 5)
    (h2 : hurwitzSum x (k + 4) ≤ Real.sqrt 5) : False := by
  have h := infFlips_of_irrational hirr
  have hw := tailQuot_pos hirr (k + 2)
  have hw1 := tailQuot_pos hirr (k + 3)
  have hr := denRatio_pos h k
  have hr1 := denRatio_pos h (k + 1)
  have ha : (1 : ℝ) ≤ (partialQuot x (k + 2) : ℝ) := by
    exact_mod_cast partialQuot_pos h (k + 2)
  -- the pair at `k+3`: its `λ` and the next one bound the difference by 1
  have hstep : (denRatio x (k + 3) - tailQuot x (k + 3)) ^ 2 ≤ 1 := by
    have hA : tailQuot x (k + 3) + denRatio x (k + 3) ≤ Real.sqrt 5 := h1
    have hB : (tailQuot x (k + 3))⁻¹ + (denRatio x (k + 3))⁻¹ ≤ Real.sqrt 5 := by
      rw [← hurwitzSum_succ hirr (k + 1)]
      exact h2
    have := sq_sub_le_one hw1 hr1 (by linarith [hA]) hB
    nlinarith [this]
  -- unwind both recurrences: the difference is `2aₖ₊₂ + 1/ρ − 1/w`
  have hwrec := inv_tailQuot hirr (k + 2)
  have hrrec := denRatio_succ h k
  have hlt : tailQuot x (k + 3) < denRatio x (k + 3) := by
    have := tailQuot_lt_one hirr (k + 3)
    linarith [one_le_denRatio h (k + 1)]
  have hdiff : denRatio x (k + 3) - tailQuot x (k + 3) ≤ 1 := by
    nlinarith [hstep, hlt]
  have hkey : 1 ≤ (tailQuot x (k + 2))⁻¹ - (denRatio x (k + 2))⁻¹ := by
    rw [hrrec] at hdiff
    have hexp : tailQuot x (k + 3) = (tailQuot x (k + 2))⁻¹ - (partialQuot x (k + 2) : ℝ) := by
      rw [hwrec]; ring
    rw [hexp] at hdiff
    linarith
  -- now the forcing lemma, with `X = 1/w` and `Y = 1/ρ`
  have hXY1 : (tailQuot x (k + 2))⁻¹ + (denRatio x (k + 2))⁻¹ ≤ Real.sqrt 5 := by
    rw [← hurwitzSum_succ hirr k]; exact h1
  have hXY2 : ((tailQuot x (k + 2))⁻¹)⁻¹ + ((denRatio x (k + 2))⁻¹)⁻¹ ≤ Real.sqrt 5 := by
    rw [inv_inv, inv_inv]; exact h0
  have hforced : (denRatio x (k + 2))⁻¹ = (Real.sqrt 5 - 1) / 2 :=
    eq_of_sub_one_le (by positivity) (by positivity) hXY1 hXY2 hkey
  -- but `ρ` is a ratio of integers, so `√5` would be rational
  have hirr5 : Irrational (Real.sqrt 5) := by
    have h5p : Nat.Prime 5 := by norm_num
    simpa using h5p.irrational_sqrt
  have hq : (0 : ℝ) < ((contin x (k + 2)).2 : ℝ) := by exact_mod_cast contin_den_pos h k
  have hq' : (0 : ℝ) < ((contin x (k + 3)).2 : ℝ) := by exact_mod_cast contin_den_pos h (k + 1)
  have hq'0 : ((contin x (k + 3)).2 : ℚ) ≠ 0 := by
    have : (0 : ℤ) < (contin x (k + 3)).2 := contin_den_pos h (k + 1)
    exact_mod_cast this.ne'
  have hrho : (denRatio x (k + 2))⁻¹ = ((contin x (k + 2)).2 : ℝ) / ((contin x (k + 3)).2 : ℝ) := by
    rw [denRatio, inv_div]
  rw [hrho] at hforced
  have hval : Real.sqrt 5
      = 2 * (((contin x (k + 2)).2 : ℝ) / ((contin x (k + 3)).2 : ℝ)) + 1 := by
    linarith [hforced]
  refine hirr5 ⟨(2 * ((contin x (k + 2)).2 : ℚ) + ((contin x (k + 3)).2 : ℚ))
      / ((contin x (k + 3)).2 : ℚ), ?_⟩
  rw [hval]
  push_cast
  field_simp

/-! ### Hurwitz -/

/-- The convergent denominators are unbounded: from index `3` on they strictly
increase, because `qⱼ₊₂ = aⱼ qⱼ₊₁ + qⱼ` with `qⱼ ≥ 1`. -/
theorem le_contin_den {x : Set ℕ} (h : InfFlips x) (k : ℕ) :
    (k : ℤ) + 1 ≤ (contin x (k + 3)).2 := by
  induction k with
  | zero =>
    have h3 : 0 < (contin x 3).2 := contin_den_pos h 1
    show ((0 : ℕ) : ℤ) + 1 ≤ (contin x 3).2
    omega
  | succ j ih =>
    have hq : 0 < (contin x (j + 2)).2 := contin_den_pos h j
    have ha : (1 : ℤ) ≤ (partialQuot x (j + 2) : ℤ) := by
      exact_mod_cast partialQuot_pos h (j + 2)
    have hq3 : 0 < (contin x (j + 3)).2 := contin_den_pos h (j + 1)
    have hrec : (contin x (j + 4)).2
        = (partialQuot x (j + 2) : ℤ) * (contin x (j + 3)).2 + (contin x (j + 2)).2 :=
      contin_den_add_two x (j + 2)
    have hgt : (contin x (j + 3)).2 < (contin x (j + 4)).2 := by rw [hrec]; nlinarith
    have hcast : (((j + 1 : ℕ)) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
    show (((j + 1 : ℕ)) : ℤ) + 1 ≤ (contin x (j + 4)).2
    rw [hcast]
    omega

/-- **Hurwitz's theorem.** For every bound `M` there is a rational `p/q` with
`q > M` approximating `Φ₀ x` to within `1/(√5 q²)`.

Stated this way rather than with `Set.Infinite`: the content is that the
solutions cannot stop, and a lower bound on `q` says exactly that. -/
theorem exists_hurwitz_approx {x : Set ℕ} (hirr : Irrational (toReal₀ x)) (M : ℤ) :
    ∃ p q : ℤ, M < q ∧
      |toReal₀ x - (p : ℝ) / (q : ℝ)| < 1 / (Real.sqrt 5 * (q : ℝ) ^ 2) := by
  have h := infFlips_of_irrational hirr
  -- pick a starting index whose denominator already exceeds `M`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, M < (N : ℤ) + 1 := ⟨(M.toNat + 1), by omega⟩
  -- among the three convergents at `N+1, N+2, N+3` one beats the bound
  have hone : ∃ j, N + 1 ≤ j ∧
      ¬ (hurwitzSum x (j + 2) ≤ Real.sqrt 5) := by
    by_contra hc
    have hc' : ∀ j, N + 1 ≤ j → hurwitzSum x (j + 2) ≤ Real.sqrt 5 := by
      intro j hjj
      by_contra hne
      exact hc ⟨j, hjj, hne⟩
    exact not_three_consecutive_fail hirr (N + 1)
      (hc' (N + 1) le_rfl) (hc' (N + 2) (by omega)) (hc' (N + 3) (by omega))
  obtain ⟨j, hj, hfail⟩ := hone
  refine ⟨(contin x (j + 2)).1, (contin x (j + 2)).2, ?_, ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, j + 2 = i + 3 := ⟨j - 1, by omega⟩
    have hden := le_contin_den h i
    rw [← hi] at hden
    have hij : N ≤ i := by omega
    have hNi : (N : ℤ) ≤ (i : ℤ) := by exact_mod_cast hij
    omega
  · by_contra hc
    exact hfail ((hurwitzSum_le_iff hirr j).1 hc)

/-! ### `√5` cannot be improved

The extremal case is `φ`, whose partial quotients are all `1`
(`partialQuot_goldenPath`) — the smallest they can be, so its convergents
converge as slowly as convergents can. Quantitatively, `p² − pq − q²` is the norm
form of `ℤ[φ]`, it never vanishes, and being an integer it is therefore at least
`1` in absolute value. That single fact bounds how well `φ` can be approximated. -/

/-- **The norm form of `ℤ[φ]` never vanishes.** A zero would make `√5` the ratio
of two integers. -/
theorem norm_form_ne_zero {p q : ℤ} (hq : q ≠ 0) : p ^ 2 - p * q - q ^ 2 ≠ 0 := by
  intro hz
  have hirr5 : Irrational (Real.sqrt 5) := by
    have h5p : Nat.Prime 5 := by norm_num
    simpa using h5p.irrational_sqrt
  have hqr : ((q : ℝ)) ≠ 0 := Int.cast_ne_zero.2 hq
  have h5 := sqrt5_sq
  have hz' : ((p : ℝ)) ^ 2 - (p : ℝ) * (q : ℝ) - (q : ℝ) ^ 2 = 0 := by exact_mod_cast hz
  have hfac : (Real.sqrt 5 * (q : ℝ) - (2 * (p : ℝ) - (q : ℝ)))
      * (Real.sqrt 5 * (q : ℝ) + (2 * (p : ℝ) - (q : ℝ))) = 0 := by nlinarith [h5, hz']
  rcases mul_eq_zero.1 hfac with hc | hc
  · exact hirr5 ⟨(2 * (p : ℚ) - (q : ℚ)) / (q : ℚ), by
      push_cast
      field_simp
      linarith⟩
  · exact hirr5 ⟨-((2 * (p : ℚ) - (q : ℚ)) / (q : ℚ)), by
      push_cast
      field_simp
      linarith⟩

/-- **`√5` is optimal.** For any constant larger than `√5`, the rationals
approximating `φ` that well have bounded denominator — so there are only finitely
many of them, and Hurwitz's constant cannot be increased. -/
theorem sqrt5_optimal {c : ℝ} (hc : Real.sqrt 5 < c) :
    ∃ M : ℤ, ∀ p q : ℤ, 0 < q → M < q →
      ¬ |Real.goldenRatio - (p : ℝ) / (q : ℝ)| < 1 / (c * (q : ℝ) ^ 2) := by
  have h5 := sqrt5_sq
  have h5pos := sqrt5_pos
  have hcpos : 0 < c := lt_trans h5pos hc
  have hgap : 0 < c - Real.sqrt 5 := by linarith
  set B : ℝ := 1 / (c * (c - Real.sqrt 5)) with hB
  have hBpos : 0 < B := by rw [hB]; positivity
  refine ⟨⌈B⌉, ?_⟩
  intro p q hq0 hqM hlt
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqr
  have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
  -- the norm form is a nonzero integer, hence at least `1` in absolute value
  have hge1 : (1 : ℝ) ≤ |((p ^ 2 - p * q - q ^ 2 : ℤ) : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |p ^ 2 - p * q - q ^ 2| := Int.one_le_abs (norm_form_ne_zero (ne_of_gt hq0))
    have : ((1 : ℤ) : ℝ) ≤ ((|p ^ 2 - p * q - q ^ 2| : ℤ) : ℝ) := by exact_mod_cast h1
    simpa using this
  have hfactor : ((p : ℝ) - (q : ℝ) * Real.goldenRatio)
      * ((p : ℝ) - (q : ℝ) * Real.goldenConj) = ((p ^ 2 - p * q - q ^ 2 : ℤ) : ℝ) := by
    have hsum := Real.goldenRatio_add_goldenConj
    have hmul := Real.goldenRatio_mul_goldenConj
    push_cast
    linear_combination (-(p : ℝ) * (q : ℝ)) * hsum + ((q : ℝ) ^ 2) * hmul
  have habs : (1 : ℝ) ≤ |(p : ℝ) - (q : ℝ) * Real.goldenRatio|
      * |(p : ℝ) - (q : ℝ) * Real.goldenConj| := by
    rw [← abs_mul, hfactor]; exact hge1
  set ε : ℝ := |Real.goldenRatio - (p : ℝ) / (q : ℝ)| with hε
  have hε0 : 0 ≤ ε := abs_nonneg _
  have e1 : |(p : ℝ) - (q : ℝ) * Real.goldenRatio| = (q : ℝ) * ε := by
    have hpq : (q : ℝ) * ((p : ℝ) / (q : ℝ)) = (p : ℝ) := by field_simp
    have hrw : (p : ℝ) - (q : ℝ) * Real.goldenRatio
        = -((q : ℝ) * (Real.goldenRatio - (p : ℝ) / (q : ℝ))) := by
      rw [mul_sub, hpq]; ring
    rw [hrw, abs_neg, abs_mul, abs_of_pos hqr, hε]
  have e2 : |(p : ℝ) - (q : ℝ) * Real.goldenConj| ≤ (q : ℝ) * (ε + Real.sqrt 5) := by
    have hd : (p : ℝ) - (q : ℝ) * Real.goldenConj
        = ((p : ℝ) - (q : ℝ) * Real.goldenRatio)
          + (q : ℝ) * (Real.goldenRatio - Real.goldenConj) := by ring
    rw [hd]
    refine le_trans (abs_add_le _ _) ?_
    rw [e1, abs_mul, abs_of_pos hqr, Real.goldenRatio_sub_goldenConj, abs_of_pos h5pos]
    linarith
  rw [e1] at habs
  have hmain : (1 : ℝ) ≤ (q : ℝ) ^ 2 * (ε * (ε + Real.sqrt 5)) := by
    nlinarith [habs, e2, mul_nonneg hqr.le hε0, abs_nonneg ((p : ℝ) - (q : ℝ) * Real.goldenConj)]
  -- clear the denominator in the hypothesis
  have hδ : ε * (c * (q : ℝ) ^ 2) < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hlt
    linarith
  set T : ℝ := ε * (c * (q : ℝ) ^ 2) with hT
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hkey := mul_le_mul_of_nonneg_left hmain (by positivity : (0 : ℝ) ≤ c ^ 2 * (q : ℝ) ^ 2)
  have hfin : c ^ 2 * (q : ℝ) ^ 2 - Real.sqrt 5 * c * (q : ℝ) ^ 2 < 1 := by
    nlinarith [hkey, mul_nonneg hT0 (by linarith : (0 : ℝ) ≤ 1 - T),
      mul_pos (by positivity : (0 : ℝ) < Real.sqrt 5 * c * (q : ℝ) ^ 2)
        (by linarith : (0 : ℝ) < 1 - T)]
  have hqB : (q : ℝ) ^ 2 < B := by
    rw [hB, lt_div_iff₀ (by positivity)]
    nlinarith [hfin]
  have hqceil : B < (q : ℝ) := by
    have h1 : ((⌈B⌉ : ℤ) : ℝ) < (q : ℝ) := by exact_mod_cast hqM
    linarith [Int.le_ceil B]
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
  nlinarith [hqB, hqceil, mul_nonneg (by linarith : (0 : ℝ) ≤ (q : ℝ))
    (by linarith : (0 : ℝ) ≤ (q : ℝ) - 1)]

/-- **Hurwitz on `ℝ`.** The encoding is surjective onto `ℝ≥0` and negation is
complement, so the statement transfers off the carrier: every irrational real is
approximated infinitely often to within `1/(√5 q²)`. -/
theorem exists_hurwitz_approx_real {t : ℝ} (ht : Irrational t) (M : ℤ) :
    ∃ p q : ℤ, M < q ∧ |t - (p : ℝ) / (q : ℝ)| < 1 / (Real.sqrt 5 * (q : ℝ) ^ 2) := by
  rcases le_or_gt 0 t with h0 | h0
  · obtain ⟨x, -, hxt⟩ := exists_toReal₀_eq h0
    obtain ⟨p, q, hq, hb⟩ := exists_hurwitz_approx (x := x) (by rwa [hxt]) M
    exact ⟨p, q, hq, by rwa [hxt] at hb⟩
  · obtain ⟨x, -, hxt⟩ := exists_toReal₀_eq (le_of_lt (neg_pos.2 h0))
    obtain ⟨p, q, hq, hb⟩ := exists_hurwitz_approx (x := x) (by rw [hxt]; exact ht.neg) M
    rw [hxt] at hb
    refine ⟨-p, q, hq, ?_⟩
    have harg : t - ((-p : ℤ) : ℝ) / (q : ℝ) = -((-t) - ((p : ℤ) : ℝ) / (q : ℝ)) := by
      push_cast; ring
    rw [harg, abs_neg]
    exact hb

end SternBrocot
