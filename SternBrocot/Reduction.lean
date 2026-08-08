/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Convergent

/-!
# Reduction theory: the forms along a path have bounded coefficients

The hard direction of Lagrange — a quadratic irrational has an eventually
periodic path — runs on the binary quadratic form carried along the path. This
file builds that form and proves the estimate the pigeonhole needs.

## The form

If `t` is a root of `A t² + B t + C = 0` and `t = (a s + b)/(c s + d)` for a
matrix in `SL₂(ℤ)`, then `s` is a root of the *transformed* form

  `formAt (a,c) · s² + formMid · s + formAt (b,d) = 0`,

whose coefficients are the usual `SL₂(ℤ)` action on binary quadratic forms. Two
things make the argument work:

* `formDisc_transform` — the discriminant is **invariant**, because the matrix
  is unimodular;
* `abs_formAt_le` — `formAt (a,c)` is **bounded** whenever `a/c` approximates `t`
  to within `1/c²`, because `formAt (a,c) = c² (a/c − t) (A (a/c + t) + B)` and
  the `c²` cancels.

Bounded coefficients with a fixed discriminant leaves finitely many forms, so
some complete quotient repeats, so the path is eventually periodic.

## The trap, and why run boundaries are the answer

`CLAUDE.md` records that the naive version of this fails: the bound needs
`|a/c − t| ≤ 1/c²`, and along a *bit path* the prefix `Lⁿ` has `c/d = n`, so no
such estimate holds at an arbitrary prefix. It holds at **run boundaries**,
where the columns are consecutive convergents and `qₖ ≤ qₖ₊₁` is available —
which is exactly `abs_sub_contin_lt_one_div_sq`. So the whole file is indexed by
`runBoundary`, and `boundaryMat_eq_contin` is what connects the two columns of
the matrix to the two convergents the estimate applies to.

## Status

Complete and `sorry`-free, estimate and pigeonhole alike. The conclusion is
`degLeTwo_eventuallyPeriodic`.

## The pigeonhole

`finite_range_tailValue` is where the estimate is cashed in. At every run
boundary the outer coefficients are bounded by a single constant `⌈Kr⌉` coming
from `abs_formAt_contin_le`, and the middle one is then bounded too because the
discriminant is fixed: `mid² = disc + 4·outer·outer`. So the triples
`(formAt, formMid, formAt)` all lie in one finite box of integers, and each
triple — nonzero leading coefficient, since the tail is irrational — has at most
two real roots. The complete quotients are among those roots, hence finitely
many; `eventuallyPeriodic_of_finite_range` turns a repeat into periodicity.
-/

open Set

namespace SternBrocot

/-! ### The binary quadratic form and its `SL₂(ℤ)` action -/

/-- The value of the form `A X² + B X Y + C Y²` at a column `(a, c)`. -/
def formAt (A B C a c : ℤ) : ℤ := A * a ^ 2 + B * a * c + C * c ^ 2

/-- The middle coefficient of the transformed form. -/
def formMid (A B C a b c d : ℤ) : ℤ := 2 * A * a * b + B * (a * d + b * c) + 2 * C * c * d

/-- **The transformed form.** If `t` is a root and `t = (a s + b)/(c s + d)`,
then `s` is a root of the form transformed by the matrix. -/
theorem formAt_transform {A B C a b c d : ℤ} {s t : ℝ}
    (hroot : (A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ) = 0)
    (hden : (c : ℝ) * s + (d : ℝ) ≠ 0)
    (ht : t = ((a : ℝ) * s + (b : ℝ)) / ((c : ℝ) * s + (d : ℝ))) :
    (formAt A B C a c : ℝ) * s ^ 2 + (formMid A B C a b c d : ℝ) * s
      + (formAt A B C b d : ℝ) = 0 := by
  have hexp : (A : ℝ) * ((a : ℝ) * s + (b : ℝ)) ^ 2
      + (B : ℝ) * ((a : ℝ) * s + (b : ℝ)) * ((c : ℝ) * s + (d : ℝ))
      + (C : ℝ) * ((c : ℝ) * s + (d : ℝ)) ^ 2 = 0 := by
    have htD : t * ((c : ℝ) * s + (d : ℝ)) = (a : ℝ) * s + (b : ℝ) := by
      rw [ht, div_mul_cancel₀ _ hden]
    linear_combination (((c : ℝ) * s + (d : ℝ)) ^ 2) * hroot
      - ((A : ℝ) * (((a : ℝ) * s + (b : ℝ)) + t * ((c : ℝ) * s + (d : ℝ)))
        + (B : ℝ) * ((c : ℝ) * s + (d : ℝ))) * htD
  simp only [formAt, formMid]
  push_cast
  linear_combination hexp

/-- **The discriminant is invariant** under the action, because the matrix is
unimodular. This is what pins the transformed forms into finitely many classes
once their coefficients are bounded. -/
theorem formDisc_transform (A B C a b c d : ℤ) :
    formMid A B C a b c d ^ 2 - 4 * formAt A B C a c * formAt A B C b d
      = (B ^ 2 - 4 * A * C) * (a * d - b * c) ^ 2 := by
  simp only [formAt, formMid]
  ring

/-! ### The estimate

`formAt (a,c) = c² (a/c − t) (A (a/c + t) + B)`. The `c²` cancels against the
approximation quality, and what is left depends only on `A`, `B` and `t`. -/

/-- **The coefficient bound.** A column that approximates `t` to within `1/c²`
gives a bounded form value — with a bound depending only on the original
coefficients and `t`, not on the column. -/
theorem abs_formAt_le {A B C : ℤ} {t : ℝ}
    (hroot : (A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ) = 0)
    {a c : ℤ} (hc : 0 < c) (hest : |(a : ℝ) / (c : ℝ) - t| ≤ 1 / (c : ℝ) ^ 2) :
    |(formAt A B C a c : ℝ)| ≤ |(A : ℝ)| * (2 * |t| + 1) + |(B : ℝ)| := by
  have hcr : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hc1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  set u : ℝ := (a : ℝ) / (c : ℝ) with hu
  have hac : (a : ℝ) = u * (c : ℝ) := by rw [hu]; field_simp
  -- the factorisation
  have hfac : (formAt A B C a c : ℝ) = (c : ℝ) ^ 2 * ((u - t) * ((A : ℝ) * (u + t) + (B : ℝ))) := by
    simp only [formAt]
    push_cast
    rw [hac]
    linear_combination ((c : ℝ) ^ 2) * hroot
  -- `1/c² ≤ 1`, so `u` is within `1` of `t`
  have hinv : 1 / (c : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hut : |u - t| ≤ 1 := le_trans hest hinv
  have hsum : |u + t| ≤ 2 * |t| + 1 := by
    have : u + t = (u - t) + 2 * t := by ring
    rw [this]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul]
    simp only [abs_two]
    linarith
  -- put it together
  rw [hfac, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (c : ℝ) ^ 2)]
  have hb1 : |(A : ℝ) * (u + t) + (B : ℝ)| ≤ |(A : ℝ)| * (2 * |t| + 1) + |(B : ℝ)| := by
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul]
    have : |(A : ℝ)| * |u + t| ≤ |(A : ℝ)| * (2 * |t| + 1) :=
      mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    linarith
  have hb2 : (c : ℝ) ^ 2 * |u - t| ≤ 1 := by
    rw [← le_div_iff₀' (by positivity)]
    simpa using hest
  have hnn : (0 : ℝ) ≤ |(A : ℝ) * (u + t) + (B : ℝ)| := abs_nonneg _
  nlinarith [mul_nonneg (mul_nonneg (le_of_lt (by positivity : (0:ℝ) < (c:ℝ)^2))
    (abs_nonneg (u - t))) hnn]

/-! ### The estimate at a run boundary

Both columns of the prefix matrix at a run boundary are convergents, so
`abs_sub_contin_lt_one_div_sq` applies to each. This is the step the trap in
`CLAUDE.md` is about: at an arbitrary prefix one column is an intermediate
mediant and no such estimate is available. -/

/-- A convergent column satisfies the hypothesis of `abs_formAt_le`. -/
theorem contin_est {x : Set ℕ} (hirr : Irrational (toReal₀ x)) (k : ℕ) :
    |((contin x (k + 2)).1 : ℝ) / ((contin x (k + 2)).2 : ℝ) - toReal₀ x|
      ≤ 1 / ((contin x (k + 2)).2 : ℝ) ^ 2 := by
  rw [abs_sub_comm]
  exact le_of_lt (abs_sub_contin_lt_one_div_sq hirr k)

/-- **The form values at the two columns of a boundary matrix are bounded**, by
a constant depending only on the original quadratic and on `t`. -/
theorem abs_formAt_contin_le {x : Set ℕ} (hirr : Irrational (toReal₀ x)) {A B C : ℤ}
    (hroot : (A : ℝ) * toReal₀ x ^ 2 + (B : ℝ) * toReal₀ x + (C : ℝ) = 0) (k : ℕ) :
    |(formAt A B C (contin x (k + 2)).1 (contin x (k + 2)).2 : ℝ)|
      ≤ |(A : ℝ)| * (2 * |toReal₀ x| + 1) + |(B : ℝ)| :=
  abs_formAt_le hroot (contin_den_pos (infFlips_of_irrational hirr) k) (contin_est hirr k)

/-- **The form carried to a run boundary has the complete quotient as a root.**
This is `formAt_transform` with the matrix being the prefix matrix at boundary
`j` and `s` the value of the tail from there — the concrete form in which the
pigeonhole will meet it. -/
theorem formAt_boundaryMat_root {x : Set ℕ} (hirr : Irrational (toReal₀ x)) {A B C : ℤ}
    (hroot : (A : ℝ) * toReal₀ x ^ 2 + (B : ℝ) * toReal₀ x + (C : ℝ) = 0) (j : ℕ) :
    (formAt A B C (boundaryMat x j).1 (boundaryMat x j).2.2.1 : ℝ) * tailValue x j ^ 2
      + (formMid A B C (boundaryMat x j).1 (boundaryMat x j).2.1
          (boundaryMat x j).2.2.1 (boundaryMat x j).2.2.2 : ℝ) * tailValue x j
      + (formAt A B C (boundaryMat x j).2.1 (boundaryMat x j).2.2.2 : ℝ) = 0 := by
  have hne := iterate_shift_ne_univ_of_irrational hirr (runBoundary x j)
  have hs : 0 ≤ tailValue x j := le_of_lt (tailValue_pos hirr j)
  have hden : (0 : ℝ) < ((boundaryMat x j).2.2.1 : ℝ) * tailValue x j
      + ((boundaryMat x j).2.2.2 : ℝ) := pathMat_den_pos_real _ hs
  refine formAt_transform hroot (ne_of_gt hden) ?_
  rw [toReal₀_eq_mobius_prefixWord x (runBoundary x j) hne, mobius]
  rfl

/-! ### From a repeated complete quotient to periodicity

The last step of the argument, and the one the encoding makes cheap: equal
values of `Φ₀` at two shifts give tail-equivalence, and a tail pair has a
*rational* common value — one side of it is eventually all `0`s and the other
eventually all `1`s — so irrationality forces the two shifted points to be
literally **equal**, which is `EventuallyPeriodic` on the nose. No algorithm and
no reconstruction step. -/

theorem eventuallyConstant_of_tailPair_left {a b : Set ℕ} (h : TailPair a b) :
    EventuallyConstant a := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, Or.inl fun m hm => hn.left_top m (by omega)⟩

theorem eventuallyConstant_of_tailPair_right {a b : Set ℕ} (h : TailPair a b) :
    EventuallyConstant b := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, Or.inr fun m hm => hn.right_tail m (by omega)⟩

/-- **Irrational points with the same value are equal.** The tail quotient only
ever identifies points of rational value, so it is invisible here. -/
theorem eq_of_toReal₀_eq_of_irrational {x y : Set ℕ} (hx : Irrational (toReal₀ x))
    (h : toReal₀ x = toReal₀ y) : x = y := by
  have hxu := ne_univ_of_irrational hx
  have hyu : y ≠ univ := by
    intro hc
    rw [hc, toReal₀_univ] at h
    exact not_irrational_of_eq_rat (q := 0) (by rw [h]; norm_num) hx
  rcases toReal₀_injective hxu hyu h with rfl | hp | hp
  · rfl
  · obtain ⟨q, hq⟩ :=
      (eventuallyConstant_iff_rat hxu).1 (eventuallyConstant_of_tailPair_left hp)
    exact absurd hx (not_irrational_of_eq_rat hq)
  · obtain ⟨q, hq⟩ :=
      (eventuallyConstant_iff_rat hxu).1 (eventuallyConstant_of_tailPair_right hp)
    exact absurd hx (not_irrational_of_eq_rat hq)

theorem runBoundary_strictMono {x : Set ℕ} (h : InfFlips x) : StrictMono (runBoundary x) :=
  strictMono_nat_of_lt_succ (runBoundary_lt_succ h)

/-- **A repeated complete quotient makes the path eventually periodic.** -/
theorem eventuallyPeriodic_of_tailValue_eq {x : Set ℕ} (hirr : Irrational (toReal₀ x))
    {k l : ℕ} (hkl : k < l) (h : tailValue x k = tailValue x l) : EventuallyPeriodic x := by
  have hf := infFlips_of_irrational hirr
  have hlt : runBoundary x k < runBoundary x l := runBoundary_strictMono hf hkl
  have heq : shift^[runBoundary x k] x = shift^[runBoundary x l] x :=
    eq_of_toReal₀_eq_of_irrational (irrational_toReal₀_iterate_shift hirr _) h
  refine ⟨runBoundary x k, runBoundary x l - runBoundary x k, by omega, ?_⟩
  rw [← Function.iterate_add_apply,
    show runBoundary x l - runBoundary x k + runBoundary x k = runBoundary x l from by omega,
    ← heq]

/-! ### Finitely many roots, and non-degeneracy

Two elementary facts the pigeonhole needs. Neither is about continued
fractions. -/

/-- **A nonzero quadratic has finitely many real roots** — at most the two the
quadratic formula names. Proved from `(2az+b)² = b² − 4ac`, which also shows the
discriminant is nonnegative as soon as a root exists. -/
theorem finite_quadratic_roots {a b c : ℝ} (ha : a ≠ 0) :
    {z : ℝ | a * z ^ 2 + b * z + c = 0}.Finite := by
  refine Set.Finite.subset (Set.toFinite
    ({(-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a),
      (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)} : Set ℝ)) ?_
  intro z hz
  simp only [Set.mem_setOf_eq] at hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hkey : (2 * a * z + b) ^ 2 = b ^ 2 - 4 * a * c := by linear_combination (4 * a) * hz
  have hsq : Real.sqrt (b ^ 2 - 4 * a * c) = |2 * a * z + b| := by
    rw [← hkey, Real.sqrt_sq_eq_abs]
  have ha2 : (2 : ℝ) * a ≠ 0 := by simpa using ha
  rcases abs_cases (2 * a * z + b) with ⟨he, -⟩ | ⟨he, -⟩
  · refine Or.inl ?_
    rw [hsq, he]
    field_simp
    ring
  · refine Or.inr ?_
    rw [hsq, he]
    field_simp
    ring

/-- The leading coefficient of a quadratic with an irrational root is nonzero:
otherwise the root solves a linear equation over `ℤ`. -/
theorem degLeTwo_leading_ne_zero {t : ℝ} (hirr : Irrational t) {A B C : ℤ}
    (hne : ¬(A = 0 ∧ B = 0 ∧ C = 0))
    (hroot : (A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ) = 0) : A ≠ 0 := by
  intro hA0
  rw [hA0] at hroot hne
  push_cast at hroot
  by_cases hB : B = 0
  · rw [hB] at hroot hne
    push_cast at hroot
    exact hne ⟨rfl, rfl, by exact_mod_cast (by linarith : (C : ℝ) = 0)⟩
  · refine hirr ⟨-(C : ℚ) / (B : ℚ), ?_⟩
    have hBr : (B : ℝ) ≠ 0 := Int.cast_ne_zero.2 hB
    push_cast
    field_simp
    linarith

/-- **The discriminant of a quadratic with an irrational root is nonzero.** A
zero discriminant makes the root a double root, hence `−B/(2A)`, hence
rational. -/
theorem degLeTwo_disc_ne_zero {t : ℝ} (hirr : Irrational t) {A B C : ℤ}
    (hne : ¬(A = 0 ∧ B = 0 ∧ C = 0))
    (hroot : (A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ) = 0) : B ^ 2 - 4 * A * C ≠ 0 := by
  have hA := degLeTwo_leading_ne_zero hirr hne hroot
  intro hD
  have hAr : (A : ℝ) ≠ 0 := Int.cast_ne_zero.2 hA
  have hDr : (B : ℝ) ^ 2 - 4 * (A : ℝ) * (C : ℝ) = 0 := by exact_mod_cast hD
  have hkey : (2 * (A : ℝ) * t + (B : ℝ)) ^ 2 = 0 := by
    linear_combination (4 * (A : ℝ)) * hroot + hDr
  have hlin : 2 * (A : ℝ) * t + (B : ℝ) = 0 := by
    have := sq_eq_zero_iff.1 hkey
    linarith [this]
  refine hirr ⟨-(B : ℚ) / (2 * (A : ℚ)), ?_⟩
  have h2A : (2 : ℝ) * (A : ℝ) ≠ 0 := by simpa using hAr
  push_cast
  field_simp
  linarith

/-! ### The pigeonhole, and what is left

With the last step in hand the whole theorem reduces to a single statement: the
complete quotients take only **finitely many values**. That is exactly what
bounded coefficients plus a fixed discriminant give — the triples
`(formAt (a,c), formMid, formAt (b,d))` lie in a box, each triple is a genuinely
quadratic form (its leading coefficient cannot vanish, or the complete quotient
would be rational), and a quadratic has at most two roots. -/

/-- **The pigeonhole.** Finitely many complete quotients force a repeat, and a
repeat is periodicity. -/
theorem eventuallyPeriodic_of_finite_range {x : Set ℕ} (hirr : Irrational (toReal₀ x))
    (hfin : (Set.range (fun k : ℕ => tailValue x (k + 2))).Finite) : EventuallyPeriodic x := by
  obtain ⟨k, -, l, -, hne, heq⟩ :=
    Set.infinite_univ.exists_ne_map_eq_of_mapsTo
      (f := fun k : ℕ => tailValue x (k + 2)) (fun a _ => Set.mem_range_self a) hfin
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact eventuallyPeriodic_of_tailValue_eq hirr (by omega : k + 2 < l + 2) heq
  · exact eventuallyPeriodic_of_tailValue_eq hirr (by omega : l + 2 < k + 2) heq.symm

/-- **The complete quotients of a quadratic irrational take finitely many
values.**

The three coefficients of the transformed form are bounded — the outer two by
`abs_formAt_contin_le`, the middle one because `formMid² = D + 4 formAt formAt`
with `D` fixed by `formDisc_transform` — so the triples lie in a finite box.
Each triple is a genuinely quadratic form, since a vanishing leading coefficient
would make its root rational, and a quadratic has at most two roots. -/
theorem finite_range_tailValue {x : Set ℕ} (hirr : Irrational (toReal₀ x))
    (h : DegLeTwo (toReal₀ x)) :
    (Set.range (fun k : ℕ => tailValue x (k + 2))).Finite := by
  classical
  obtain ⟨A, B, C, hne, hroot⟩ := h
  have hfl := infFlips_of_irrational hirr
  have hDne := degLeTwo_disc_ne_zero hirr hne hroot
  -- the root equation and the invariant discriminant, at every boundary
  have hrootk : ∀ k : ℕ,
      (formAt A B C (boundaryMat x (k + 2)).1 (boundaryMat x (k + 2)).2.2.1 : ℝ)
          * tailValue x (k + 2) ^ 2
        + (formMid A B C (boundaryMat x (k + 2)).1 (boundaryMat x (k + 2)).2.1
            (boundaryMat x (k + 2)).2.2.1 (boundaryMat x (k + 2)).2.2.2 : ℝ)
          * tailValue x (k + 2)
        + (formAt A B C (boundaryMat x (k + 2)).2.1 (boundaryMat x (k + 2)).2.2.2 : ℝ) = 0 :=
    fun k => formAt_boundaryMat_root hirr hroot (k + 2)
  have hdisc : ∀ k : ℕ,
      formMid A B C (boundaryMat x (k + 2)).1 (boundaryMat x (k + 2)).2.1
          (boundaryMat x (k + 2)).2.2.1 (boundaryMat x (k + 2)).2.2.2 ^ 2
        - 4 * formAt A B C (boundaryMat x (k + 2)).1 (boundaryMat x (k + 2)).2.2.1
            * formAt A B C (boundaryMat x (k + 2)).2.1 (boundaryMat x (k + 2)).2.2.2
        = B ^ 2 - 4 * A * C := by
    intro k
    have hdet : (boundaryMat x (k + 2)).1 * (boundaryMat x (k + 2)).2.2.2
        - (boundaryMat x (k + 2)).2.1 * (boundaryMat x (k + 2)).2.2.1 = 1 :=
      pathMat_det (prefixWord x (runBoundary x (k + 2)))
    rw [formDisc_transform, hdet]
    ring
  -- the tails are irrational, which is what makes the forms genuinely quadratic
  have htirr : ∀ k : ℕ, Irrational (tailValue x (k + 2)) :=
    fun k => irrational_toReal₀_iterate_shift hirr _
  have hlead : ∀ k : ℕ,
      formAt A B C (boundaryMat x (k + 2)).1 (boundaryMat x (k + 2)).2.2.1 ≠ 0 := by
    intro k hz
    have hd := hdisc k
    rw [hz] at hd
    have hbne : formMid A B C (boundaryMat x (k + 2)).1 (boundaryMat x (k + 2)).2.1
        (boundaryMat x (k + 2)).2.2.1 (boundaryMat x (k + 2)).2.2.2 ≠ 0 := by
      intro hb0
      rw [hb0] at hd
      exact hDne (by linarith [hd])
    have hr := hrootk k
    rw [hz] at hr
    push_cast at hr
    refine htirr k ⟨-(formAt A B C (boundaryMat x (k + 2)).2.1 (boundaryMat x (k + 2)).2.2.2 : ℚ)
      / (formMid A B C (boundaryMat x (k + 2)).1 (boundaryMat x (k + 2)).2.1
          (boundaryMat x (k + 2)).2.2.1 (boundaryMat x (k + 2)).2.2.2 : ℚ), ?_⟩
    have hbr : (formMid A B C (boundaryMat x (k + 2)).1 (boundaryMat x (k + 2)).2.1
        (boundaryMat x (k + 2)).2.2.1 (boundaryMat x (k + 2)).2.2.2 : ℝ) ≠ 0 :=
      Int.cast_ne_zero.2 hbne
    push_cast
    field_simp
    linarith
  -- the outer coefficients are bounded, because both columns are convergents
  set Kr : ℝ := |(A : ℝ)| * (2 * |toReal₀ x| + 1) + |(B : ℝ)| with hKr
  have hbnd : ∀ k : ℕ,
      |(formAt A B C (boundaryMat x (k + 2)).1 (boundaryMat x (k + 2)).2.2.1 : ℝ)| ≤ Kr ∧
      |(formAt A B C (boundaryMat x (k + 2)).2.1 (boundaryMat x (k + 2)).2.2.2 : ℝ)| ≤ Kr := by
    intro k
    obtain ⟨hT, hF⟩ := boundaryMat_eq_contin hfl (k + 1)
    cases hb : runBit x (k + 1)
    · have hMk : boundaryMat x (k + 2) = ((contin x (k + 3)).1, (contin x (k + 2)).1,
          (contin x (k + 3)).2, (contin x (k + 2)).2) := hF hb
      rw [hMk]
      exact ⟨abs_formAt_contin_le hirr hroot (k + 1), abs_formAt_contin_le hirr hroot k⟩
    · have hMk : boundaryMat x (k + 2) = ((contin x (k + 2)).1, (contin x (k + 3)).1,
          (contin x (k + 2)).2, (contin x (k + 3)).2) := hT hb
      rw [hMk]
      exact ⟨abs_formAt_contin_le hirr hroot k, abs_formAt_contin_le hirr hroot (k + 1)⟩
  -- turn the real bound into an integer one
  set N : ℤ := ⌈Kr⌉ with hN
  have hbndZ : ∀ k : ℕ,
      |formAt A B C (boundaryMat x (k + 2)).1 (boundaryMat x (k + 2)).2.2.1| ≤ N ∧
      |formAt A B C (boundaryMat x (k + 2)).2.1 (boundaryMat x (k + 2)).2.2.2| ≤ N := by
    intro k
    obtain ⟨h1, h2⟩ := hbnd k
    constructor
    · have : |(formAt A B C (boundaryMat x (k + 2)).1 (boundaryMat x (k + 2)).2.2.1 : ℝ)|
          ≤ (N : ℝ) := le_trans h1 (Int.le_ceil Kr)
      rw [← Int.cast_abs] at this
      exact_mod_cast this
    · have : |(formAt A B C (boundaryMat x (k + 2)).2.1 (boundaryMat x (k + 2)).2.2.2 : ℝ)|
          ≤ (N : ℝ) := le_trans h2 (Int.le_ceil Kr)
      rw [← Int.cast_abs] at this
      exact_mod_cast this
  have hN0 : 0 ≤ N := le_trans (abs_nonneg _) (hbndZ 0).1
  -- and the middle coefficient, via the fixed discriminant
  set Mb : ℤ := |B ^ 2 - 4 * A * C| + 4 * N ^ 2 + 1 with hMb
  have hbndM : ∀ k : ℕ,
      |formMid A B C (boundaryMat x (k + 2)).1 (boundaryMat x (k + 2)).2.1
        (boundaryMat x (k + 2)).2.2.1 (boundaryMat x (k + 2)).2.2.2| ≤ Mb := by
    intro k
    obtain ⟨h1, h2⟩ := hbndZ k
    have hd := hdisc k
    have habs1 := abs_le.1 h1
    have habs2 := abs_le.1 h2
    have hsq : formMid A B C (boundaryMat x (k + 2)).1 (boundaryMat x (k + 2)).2.1
        (boundaryMat x (k + 2)).2.2.1 (boundaryMat x (k + 2)).2.2.2 ^ 2
        ≤ |B ^ 2 - 4 * A * C| + 4 * N ^ 2 := by
      have hle : B ^ 2 - 4 * A * C ≤ |B ^ 2 - 4 * A * C| := le_abs_self _
      nlinarith [habs1.1, habs1.2, habs2.1, habs2.2, hd, hle]
    nlinarith [sq_abs (formMid A B C (boundaryMat x (k + 2)).1 (boundaryMat x (k + 2)).2.1
      (boundaryMat x (k + 2)).2.2.1 (boundaryMat x (k + 2)).2.2.2),
      abs_nonneg (formMid A B C (boundaryMat x (k + 2)).1 (boundaryMat x (k + 2)).2.1
        (boundaryMat x (k + 2)).2.2.1 (boundaryMat x (k + 2)).2.2.2), hsq, hN0]
  -- the finite box of admissible triples
  set NB : ℤ := max N Mb with hNB
  set Bx : Finset (ℤ × ℤ × ℤ) :=
    ((Finset.Icc (-NB) NB) ×ˢ ((Finset.Icc (-NB) NB) ×ˢ (Finset.Icc (-NB) NB))).filter
      (fun t => t.1 ≠ 0) with hBx
  have hNle : N ≤ NB := le_max_left _ _
  have hMle : Mb ≤ NB := le_max_right _ _
  -- each admissible triple contributes only its (at most two) roots
  have hfin : (⋃ t ∈ (Bx : Set (ℤ × ℤ × ℤ)),
      {z : ℝ | (t.1 : ℝ) * z ^ 2 + (t.2.1 : ℝ) * z + (t.2.2 : ℝ) = 0}).Finite := by
    refine Set.Finite.biUnion Bx.finite_toSet fun t ht => ?_
    have ht0 : t.1 ≠ 0 := by
      have ht' : t ∈ Bx := Finset.mem_coe.1 ht
      rw [hBx, Finset.mem_filter] at ht'
      exact ht'.2
    exact finite_quadratic_roots (Int.cast_ne_zero.2 ht0)
  refine hfin.subset ?_
  rintro z ⟨k, rfl⟩
  have hmemBx : (formAt A B C (boundaryMat x (k + 2)).1 (boundaryMat x (k + 2)).2.2.1,
      formMid A B C (boundaryMat x (k + 2)).1 (boundaryMat x (k + 2)).2.1
        (boundaryMat x (k + 2)).2.2.1 (boundaryMat x (k + 2)).2.2.2,
      formAt A B C (boundaryMat x (k + 2)).2.1 (boundaryMat x (k + 2)).2.2.2) ∈ Bx := by
    obtain ⟨h1, h2⟩ := hbndZ k
    have h3 := hbndM k
    obtain ⟨p1, q1⟩ := abs_le.1 h1
    obtain ⟨p2, q2⟩ := abs_le.1 h2
    obtain ⟨p3, q3⟩ := abs_le.1 h3
    simp only [hBx, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, by omega⟩, hlead k⟩
  exact Set.mem_biUnion (Finset.mem_coe.2 hmemBx) (hrootk k)

/-- **Lagrange, hard direction.** A quadratic irrational has an eventually
periodic path. -/
theorem degLeTwo_eventuallyPeriodic {x : Set ℕ} (hirr : Irrational (toReal₀ x))
    (h : DegLeTwo (toReal₀ x)) : EventuallyPeriodic x :=
  eventuallyPeriodic_of_finite_range hirr (finite_range_tailValue hirr h)

/-! ### Lagrange's theorem

Both directions, on `P(ω)`. The rational case is not a degenerate edge here: in
this encoding a rational has an eventually *constant* path, which is eventually
periodic, and `degLeTwo_of_rat` puts it on the other side too. So the statement
is `≤ 2`, not "quadratic irrational" — a transcendental is excluded by
`DegLeTwo` carrying an actual nonzero integer relation, not by
`Module.finrank ≤ 2`, which is vacuously true in infinite dimension. -/

/-- **Lagrange's theorem.** The path of `x` is eventually periodic **iff** its
value is rational or a quadratic irrational. -/
theorem eventuallyPeriodic_iff_degLeTwo {x : Set ℕ} (hx : x ≠ univ) :
    EventuallyPeriodic x ↔ DegLeTwo (toReal₀ x) := by
  refine ⟨degLeTwo_of_eventuallyPeriodic hx, fun h => ?_⟩
  by_cases hirr : Irrational (toReal₀ x)
  · exact degLeTwo_eventuallyPeriodic hirr h
  · obtain ⟨q, hq⟩ := not_not.1 hirr
    exact eventuallyPeriodic_of_eventuallyConstant
      ((eventuallyConstant_iff_rat hx).2 ⟨q, hq.symm⟩)

/-- The signed form, on all of `ℝ`: the path of a finite point of `P(ω+1)` is
eventually periodic iff its value has degree at most two. -/
theorem eventuallyPeriodic_iff_degLeTwo_toReal {x : Signed} (hx : IsFinite x) :
    EventuallyPeriodic (finPart x) ↔ DegLeTwo (toReal x) := by
  refine ⟨degLeTwo_toReal_of_eventuallyPeriodic hx, fun h => ?_⟩
  by_cases hs : none ∈ x
  · rw [toReal_of_neg hs] at h
    have h' : DegLeTwo (toReal₀ (magnitude x)) := by
      have hn := h.neg
      rwa [_root_.neg_neg] at hn
    have hmag : EventuallyPeriodic (magnitude x) := (eventuallyPeriodic_iff_degLeTwo hx).2 h'
    rw [magnitude_of_neg hs] at hmag
    have : EventuallyPeriodic (finPart x)ᶜᶜ := hmag.compl
    rwa [compl_compl] at this
  · rw [toReal_of_pos hs] at h
    have hmag : EventuallyPeriodic (magnitude x) := (eventuallyPeriodic_iff_degLeTwo hx).2 h
    rwa [magnitude_of_pos hs] at hmag

end SternBrocot
