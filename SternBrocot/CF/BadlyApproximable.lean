/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.CF.Legendre

/-!
# Badly approximable ⟺ bounded partial quotients

> An irrational `Φ₀x` is badly approximable — no rational beats `c/q²` for some
> fixed `c > 0` — **iff** its partial quotients are bounded.

`badlyApproximable_iff_boundedPartialQuot`.

## The route

Both directions run on a single identity, which is the real content of the file:

  `qₖ₊₁|qₖα − pₖ| + qₖ|qₖ₊₁α − pₖ₊₁| = 1`   (`contin_err_sum`)

This is unimodularity and straddling combined. `qₖ₊₁Aₖ − qₖBₖ` telescopes to
`±(pₖ₊₁qₖ − pₖqₖ₊₁) = ∓1`, and because `Aₖ` and `Bₖ` have *opposite* signs the
subtraction is an addition in absolute value. Both estimates fall out:

* `contin_err_le` — `|Aₖ| ≤ 1/qₖ₊₁`, since the other term is non-negative.
* `contin_err_ge` — `|Aₖ| ≥ 1/(2qₖ₊₁)`, since the other term is at most `1/2`:
  `|Bₖ| ≤ 1/qₖ₊₂` by the same identity one step along, and
  `qₖ₊₂ ≥ qₖ₊₁ + qₖ ≥ 2qₖ`.

Notably this needs **neither Legendre nor the exact error formula**
`abs_sub_contin_eq`. The first plan for this file went through Legendre — "a
rational that is not a convergent is already `1/(2q²)` away" — and then had to
handle the convergents separately with `abs_sub_contin_eq` and `tailQuot`. Going
through best approximation instead removes the case split entirely: *every*
rational is compared against the bracketing convergent, whether or not it is one.

That also means no coprimality hypothesis is needed anywhere, so
`BadlyApproximable` quantifies over **all** `p, q` with `q > 0` rather than over
fractions in lowest terms.

## Indexing

As in `Legendre.lean`, the pair at index `j` is
`(contin x (j+1), contin x (j+2))`, and `startIdx x ≤ j + 1` is the hypothesis
that puts it in the genuine-convergent range. See that file's `startIdx` section
for why the range differs by branch.
-/

open Set

namespace SternBrocot

/-! ### Definitions -/

/-- The partial quotients of the path are bounded. -/
def BoundedPartialQuot (x : Set ℕ) : Prop := ∃ M : ℕ, ∀ k, partialQuot x k ≤ M

/-- `α` is **badly approximable**: some `c > 0` bounds every rational
approximation away by `c/q²`. Quantified over all integer pairs, not only those
in lowest terms. -/
def BadlyApproximable (α : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ p q : ℤ, 0 < q → c / (q : ℝ) ^ 2 ≤ |α - (p : ℝ) / (q : ℝ)|

/-! ### One index down, again

`contin_den_le_succ` starts at index 1. On a left-starting path the pair at
`j = 0` is legitimate, and there `q₀ = 0 ≤ 1 = q₁` holds for a different reason
— the seed, not the recurrence. -/

theorem contin_den_le_succ_of_startIdx {x : Set ℕ} (h : InfFlips x) {j : ℕ}
    (hj : startIdx x ≤ j + 1) : (contin x j).2 ≤ (contin x (j + 1)).2 := by
  match j with
  | 0 =>
    -- `startIdx x ≤ 1` forces the left branch, where `q₀ = 0` and `q₁ = 1`
    have hb : runBit x 0 = false := by
      by_contra hc
      have : runBit x 0 = true := by
        cases hbb : runBit x 0 with
        | false => exact absurd hbb hc
        | true => rfl
      have : startIdx x = 2 := by simp [startIdx, this]
      omega
    have h0 : contin x 0 = (1, 0) := by simp [contin_zero, hb]
    have h1 : contin x 1 = (0, 1) := by simp [contin_one, hb]
    rw [h0, h1]
    norm_num
  | (i + 1) => exact contin_den_le_succ h i

/-! ### The identity

Everything else in this file is arithmetic on `contin_err_sum`. -/

/-- Opposite-signed quantities subtract into a sum of absolute values. The
arithmetic heart of `contin_err_sum`, isolated so the sign analysis is not
tangled with the continued-fraction indexing. -/
theorem abs_sub_eq_add_abs {c d u v : ℝ} (hc : 0 < c) (hd : 0 < d) (huv : u * v < 0) :
    |c * u - d * v| = c * |u| + d * |v| := by
  rcases lt_trichotomy u 0 with hu | hu | hu
  · have hv : 0 < v := by
      by_contra hcon
      rw [not_lt] at hcon
      nlinarith
    rw [abs_of_neg hu, abs_of_pos hv, abs_of_neg (by nlinarith : c * u - d * v < 0)]
    ring
  · exact absurd huv (by rw [hu, zero_mul]; exact lt_irrefl 0)
  · have hv : v < 0 := by
      by_contra hcon
      rw [not_lt] at hcon
      nlinarith
    rw [abs_of_pos hu, abs_of_neg hv, abs_of_pos (by nlinarith : 0 < c * u - d * v)]
    ring

/-- **The error identity.** `qₖ₊₁|Aₖ| + qₖ|Bₖ| = 1`, where `Aₖ`, `Bₖ` are the two
signed errors at consecutive convergents.

Unimodularity gives `|qₖ₊₁Aₖ − qₖBₖ| = 1`; the straddling turns that subtraction
into an addition of absolute values, because the two errors point opposite
ways. -/
theorem contin_err_sum {x : Set ℕ} (hirr : Irrational (toReal₀ x)) (j : ℕ)
    (h1 : 0 < (contin x (j + 1)).2) (h2 : 0 < (contin x (j + 2)).2) :
    ((contin x (j + 2)).2 : ℝ)
        * |((contin x (j + 1)).2 : ℝ) * toReal₀ x - ((contin x (j + 1)).1 : ℝ)|
      + ((contin x (j + 1)).2 : ℝ)
        * |((contin x (j + 2)).2 : ℝ) * toReal₀ x - ((contin x (j + 2)).1 : ℝ)| = 1 := by
  have h := infFlips_of_irrational hirr
  set A := ((contin x (j + 1)).2 : ℝ) * toReal₀ x - ((contin x (j + 1)).1 : ℝ) with hA
  set B := ((contin x (j + 2)).2 : ℝ) * toReal₀ x - ((contin x (j + 2)).1 : ℝ) with hB
  have h1r : (0 : ℝ) < ((contin x (j + 1)).2 : ℝ) := by exact_mod_cast h1
  have h2r : (0 : ℝ) < ((contin x (j + 2)).2 : ℝ) := by exact_mod_cast h2
  have hAB : A * B < 0 := contin_err_mul_neg_gen hirr j h1 h2
  -- the telescoping identity: everything in `α` cancels
  have hkey : ((contin x (j + 2)).2 : ℝ) * A - ((contin x (j + 1)).2 : ℝ) * B
      = -(((contin x (j + 1)).1 : ℝ) * ((contin x (j + 2)).2 : ℝ)
          - ((contin x (j + 2)).1 : ℝ) * ((contin x (j + 1)).2 : ℝ)) := by
    rw [hA, hB]; ring
  have hone : |((contin x (j + 2)).2 : ℝ) * A - ((contin x (j + 1)).2 : ℝ) * B| = 1 := by
    rcases contin_det_gen h j with hd | hd
    · have hdr : ((contin x (j + 1)).1 : ℝ) * ((contin x (j + 2)).2 : ℝ)
          - ((contin x (j + 2)).1 : ℝ) * ((contin x (j + 1)).2 : ℝ) = 1 := by exact_mod_cast hd
      rw [hkey, hdr]; norm_num
    · have hdr : ((contin x (j + 1)).1 : ℝ) * ((contin x (j + 2)).2 : ℝ)
          - ((contin x (j + 2)).1 : ℝ) * ((contin x (j + 1)).2 : ℝ) = -1 := by exact_mod_cast hd
      rw [hkey, hdr]; norm_num
  rw [abs_sub_eq_add_abs h2r h1r hAB] at hone
  exact hone

/-- The upper bound: the other term of the identity is non-negative. -/
theorem contin_err_le {x : Set ℕ} (hirr : Irrational (toReal₀ x)) (j : ℕ)
    (h1 : 0 < (contin x (j + 1)).2) (h2 : 0 < (contin x (j + 2)).2) :
    |((contin x (j + 1)).2 : ℝ) * toReal₀ x - ((contin x (j + 1)).1 : ℝ)|
      ≤ 1 / ((contin x (j + 2)).2 : ℝ) := by
  have hsum := contin_err_sum hirr j h1 h2
  have h1r : (0 : ℝ) < ((contin x (j + 1)).2 : ℝ) := by exact_mod_cast h1
  have h2r : (0 : ℝ) < ((contin x (j + 2)).2 : ℝ) := by exact_mod_cast h2
  rw [le_div_iff₀ h2r]
  nlinarith [abs_nonneg (((contin x (j + 2)).2 : ℝ) * toReal₀ x - ((contin x (j + 2)).1 : ℝ))]

/-- **The lower bound**, and the point of the identity: no convergent is closer
than half the reciprocal of the next denominator. -/
theorem contin_err_ge {x : Set ℕ} (hirr : Irrational (toReal₀ x)) (j : ℕ)
    (hj : startIdx x ≤ j + 1) :
    1 / (2 * ((contin x (j + 2)).2 : ℝ))
      ≤ |((contin x (j + 1)).2 : ℝ) * toReal₀ x - ((contin x (j + 1)).1 : ℝ)| := by
  have h := infFlips_of_irrational hirr
  have h1 : 0 < (contin x (j + 1)).2 := contin_den_pos_of_startIdx h hj
  have h2 : 0 < (contin x (j + 2)).2 := contin_den_pos_of_startIdx h (by omega)
  have h3 : 0 < (contin x (j + 3)).2 := contin_den_pos_of_startIdx h (by omega)
  have h1r : (0 : ℝ) < ((contin x (j + 1)).2 : ℝ) := by exact_mod_cast h1
  have h2r : (0 : ℝ) < ((contin x (j + 2)).2 : ℝ) := by exact_mod_cast h2
  have h3r : (0 : ℝ) < ((contin x (j + 3)).2 : ℝ) := by exact_mod_cast h3
  have hsum := contin_err_sum hirr j h1 h2
  -- `|B| ≤ 1/q₍ⱼ₊₃₎`, the same bound one step along
  have hBle : |((contin x (j + 2)).2 : ℝ) * toReal₀ x - ((contin x (j + 2)).1 : ℝ)|
      ≤ 1 / ((contin x (j + 3)).2 : ℝ) := contin_err_le hirr (j + 1) h2 h3
  -- `q₍ⱼ₊₃₎ ≥ q₍ⱼ₊₂₎ + q₍ⱼ₊₁₎ ≥ 2 q₍ⱼ₊₁₎`
  have hrec : (contin x (j + 3)).2
      = (partialQuot x (j + 1) : ℤ) * (contin x (j + 2)).2 + (contin x (j + 1)).2 :=
    contin_den_add_two x (j + 1)
  have ha : (1 : ℤ) ≤ (partialQuot x (j + 1) : ℤ) := by
    exact_mod_cast partialQuot_pos h (j + 1)
  have hmono : (contin x (j + 1)).2 ≤ (contin x (j + 2)).2 :=
    contin_den_le_succ_of_startIdx h (by omega)
  have hgrow : 2 * (contin x (j + 1)).2 ≤ (contin x (j + 3)).2 := by nlinarith
  have hgrowr : 2 * ((contin x (j + 1)).2 : ℝ) ≤ ((contin x (j + 3)).2 : ℝ) := by
    exact_mod_cast hgrow
  -- so the second term of the identity is at most `1/2`
  have hhalf : ((contin x (j + 1)).2 : ℝ)
      * |((contin x (j + 2)).2 : ℝ) * toReal₀ x - ((contin x (j + 2)).1 : ℝ)| ≤ 1 / 2 := by
    calc ((contin x (j + 1)).2 : ℝ)
        * |((contin x (j + 2)).2 : ℝ) * toReal₀ x - ((contin x (j + 2)).1 : ℝ)|
        ≤ ((contin x (j + 1)).2 : ℝ) * (1 / ((contin x (j + 3)).2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hBle (le_of_lt h1r)
      _ ≤ 1 / 2 := by
          rw [mul_one_div, div_le_div_iff₀ h3r (by norm_num)]
          linarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-! ### Bounded partial quotients ⟹ badly approximable

Bracket `q`, compare against the bracketing convergent by best approximation,
and bound that convergent's error from below. No case split on whether `p/q` is
itself a convergent, and no coprimality. -/

theorem badlyApproximable_of_bounded {x : Set ℕ} (hirr : Irrational (toReal₀ x))
    (hb : BoundedPartialQuot x) : BadlyApproximable (toReal₀ x) := by
  obtain ⟨M, hM⟩ := hb
  have h := infFlips_of_irrational hirr
  refine ⟨1 / (2 * ((M : ℝ) + 1)), by positivity, ?_⟩
  intro p q hq0
  obtain ⟨j', hjs, hle, hlt⟩ := exists_bracket h hq0
  obtain ⟨j, rfl⟩ : ∃ j, j' = j + 1 := ⟨j' - 1, by have := one_le_startIdx x; omega⟩
  have hd1 : 0 < (contin x (j + 1)).2 := contin_den_pos_of_startIdx h hjs
  have hd2 : 0 < (contin x (j + 2)).2 := contin_den_pos_of_startIdx h (by omega)
  have hbest := contin_best_approx_gen hirr j hd1 hd2 (p := p) hq0 hlt
  have hlow := contin_err_ge hirr j hjs
  -- `q₍ⱼ₊₂₎ ≤ (M+1) q₍ⱼ₊₁₎ ≤ (M+1) q`
  have hrec : (contin x (j + 2)).2
      = (partialQuot x j : ℤ) * (contin x (j + 1)).2 + (contin x j).2 :=
    contin_den_add_two x j
  have haM : (partialQuot x j : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM j
  have hmono : (contin x j).2 ≤ (contin x (j + 1)).2 :=
    contin_den_le_succ_of_startIdx h hjs
  have hstep : (contin x (j + 2)).2 ≤ ((M : ℤ) + 1) * (contin x (j + 1)).2 := by nlinarith
  have hstepR : ((contin x (j + 2)).2 : ℝ) ≤ ((M : ℝ) + 1) * (q : ℝ) := by
    have h1 : ((contin x (j + 2)).2 : ℝ) ≤ ((M : ℝ) + 1) * ((contin x (j + 1)).2 : ℝ) := by
      exact_mod_cast hstep
    have h2 : ((contin x (j + 1)).2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hle
    nlinarith [Nat.cast_nonneg (α := ℝ) M]
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  -- assemble
  have hqp : 1 / (2 * ((M : ℝ) + 1) * (q : ℝ)) ≤ |(q : ℝ) * toReal₀ x - (p : ℝ)| := by
    refine le_trans ?_ (le_trans hlow hbest)
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) M]
  have hfac : (q : ℝ) * toReal₀ x - (p : ℝ)
      = (q : ℝ) * (toReal₀ x - (p : ℝ) / (q : ℝ)) := by field_simp
  rw [hfac, abs_mul, abs_of_pos hqR] at hqp
  -- multiply through by `q` once more to land on the `c/q²` shape
  have hmul := mul_le_mul_of_nonneg_left hqp (le_of_lt hqR)
  rw [show (q : ℝ) * (1 / (2 * ((M : ℝ) + 1) * (q : ℝ))) = 1 / (2 * ((M : ℝ) + 1)) by
    field_simp] at hmul
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) ^ 2)]
  nlinarith [hmul]

/-! ### Unbounded partial quotients ⟹ not badly approximable

A large partial quotient makes the *next* denominator large, and
`|Φ₀x − pₖ/qₖ| < 1/(qₖqₖ₊₁)` then beats any fixed `c/q²`. -/

theorem not_badlyApproximable_of_unbounded {x : Set ℕ} (hirr : Irrational (toReal₀ x))
    (hb : ¬ BoundedPartialQuot x) : ¬ BadlyApproximable (toReal₀ x) := by
  rintro ⟨c, hc, hbad⟩
  have h := infFlips_of_irrational hirr
  -- pick a partial quotient exceeding `1/c`, at a positive index
  set M : ℕ := max (Nat.ceil (1 / c)) (partialQuot x 0) with hMdef
  have hnot : ¬ ∀ k, partialQuot x k ≤ M := fun hall => hb ⟨M, hall⟩
  simp only [not_forall, not_le] at hnot
  obtain ⟨m, hm⟩ := hnot
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact absurd hm (by simp [hMdef])
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  -- the estimate at that index
  have hd2 : 0 < (contin x (k + 2)).2 := contin_den_pos h k
  have hd3 : 0 < (contin x (k + 3)).2 := contin_den_pos h (k + 1)
  have hd2R : (0 : ℝ) < ((contin x (k + 2)).2 : ℝ) := by exact_mod_cast hd2
  have hd3R : (0 : ℝ) < ((contin x (k + 3)).2 : ℝ) := by exact_mod_cast hd3
  have hest := abs_sub_contin_lt hirr k
  have hgood := hbad (contin x (k + 2)).1 (contin x (k + 2)).2 hd2
  -- `q₍ₖ₊₃₎ ≥ a₍ₖ₊₁₎ q₍ₖ₊₂₎ > (1/c) q₍ₖ₊₂₎`
  have hrec : (contin x (k + 3)).2
      = (partialQuot x (k + 1) : ℤ) * (contin x (k + 2)).2 + (contin x (k + 1)).2 :=
    contin_den_add_two x (k + 1)
  have hnn : 0 ≤ (contin x (k + 1)).2 := contin_den_nonneg x (k + 1)
  have hbig : (M : ℤ) * (contin x (k + 2)).2 < (contin x (k + 3)).2 := by
    have : (M : ℤ) < (partialQuot x (k + 1) : ℤ) := by exact_mod_cast hm
    nlinarith
  have hbigR : (M : ℝ) * ((contin x (k + 2)).2 : ℝ) < ((contin x (k + 3)).2 : ℝ) := by
    exact_mod_cast hbig
  have hMc : 1 / c ≤ (M : ℝ) := by
    refine le_trans (Nat.le_ceil (1 / c)) ?_
    exact_mod_cast Nat.le_max_left (Nat.ceil (1 / c)) (partialQuot x 0)
  -- `c/q² > 1/(q q')`, contradicting the estimate
  have hlt : 1 / (((contin x (k + 2)).2 : ℝ) * ((contin x (k + 3)).2 : ℝ))
      < c / ((contin x (k + 2)).2 : ℝ) ^ 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have hcq : ((contin x (k + 2)).2 : ℝ) < c * ((contin x (k + 3)).2 : ℝ) := by
      have h1 : (1 : ℝ) ≤ (M : ℝ) * c := by rwa [div_le_iff₀ hc] at hMc
      nlinarith
    nlinarith
  linarith [hgood, hest, hlt]

/-! ### The theorem -/

/-- **Badly approximable ⟺ bounded partial quotients.** -/
theorem badlyApproximable_iff_boundedPartialQuot {x : Set ℕ} (hirr : Irrational (toReal₀ x)) :
    BadlyApproximable (toReal₀ x) ↔ BoundedPartialQuot x := by
  constructor
  · intro hba
    by_contra hnb
    exact not_badlyApproximable_of_unbounded hirr hnb hba
  · exact badlyApproximable_of_bounded hirr

end SternBrocot
