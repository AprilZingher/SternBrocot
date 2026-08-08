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

The estimate is complete and `sorry`-free. The pigeonhole that consumes it, and
the conclusion, are `degLeTwo_eventuallyPeriodic` — a named `sorry`, with what it
needs recorded in `HANDOFF.md`.
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

/-- **The one remaining gap.** The complete quotients of a quadratic irrational
take finitely many values.

Not proved. Everything it needs is above: `abs_formAt_contin_le` bounds the outer
coefficients uniformly, `formDisc_transform` then bounds the middle one, and
`formAt_boundaryMat_root` says each complete quotient is a root of its own
triple. What is missing is only the packaging — a finite box of integer triples,
and "a nonzero quadratic has finitely many roots". -/
theorem finite_range_tailValue {x : Set ℕ} (hirr : Irrational (toReal₀ x))
    (h : DegLeTwo (toReal₀ x)) :
    (Set.range (fun k : ℕ => tailValue x (k + 2))).Finite := by
  sorry

/-- **Lagrange, hard direction.** A quadratic irrational has an eventually
periodic path. -/
theorem degLeTwo_eventuallyPeriodic {x : Set ℕ} (hirr : Irrational (toReal₀ x))
    (h : DegLeTwo (toReal₀ x)) : EventuallyPeriodic x :=
  eventuallyPeriodic_of_finite_range hirr (finite_range_tailValue hirr h)

end SternBrocot
