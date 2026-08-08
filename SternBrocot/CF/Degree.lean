/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination

/-!
# Algebraic degree at most two

The right-hand side of Lagrange's theorem. Nothing in this file mentions the
Stern–Brocot tree; it is the statement `[ℚ(t) : ℚ] ≤ 2` in the concrete form the
tree argument produces, plus the two facts about that form which the tree
argument needs.

## The concrete form, and why

The tree hands over an explicit integer quadratic satisfied by the value, so
`DegLeTwo` is stated that way — a root of a nonzero integer polynomial of degree
at most two. `DegLeTwo.finrank_adjoin_le` and `DegLeTwo.finiteDimensional`
translate it back into field theory, and *both* are needed to read the result
correctly: `Module.finrank` is `0` on an infinite-dimensional space, so
`finrank ℚ ℚ⟮t⟯ ≤ 2` on its own is also true of every transcendental number and
says nothing. With finite-dimensionality alongside it, it is the honest
`[ℚ(t) : ℚ] ≤ 2`.

Note that this is `≤ 2`, not `= 2`: rationals are included, and they have to be
(see `SternBrocot.eventuallyConstant_iff_rat`).

## Main results

* `SternBrocot.DegLeTwo` — the predicate.
* `SternBrocot.DegLeTwo.mobius` — **degree ≤ 2 survives the `SL₂(ℤ)` action**.
  The transformed coefficients are the usual action of `M⁻¹` on binary quadratic
  forms; unimodularity is exactly what stops them all vanishing.
* `SternBrocot.DegLeTwo.finrank_adjoin_le`, `SternBrocot.DegLeTwo.finiteDimensional`
  — the field-theoretic reading.
-/

open Polynomial

namespace SternBrocot

/-- `t` has **degree at most two over `ℚ`**: it is a root of a nonzero integer
polynomial of degree at most two. Equivalently `[ℚ(t) : ℚ] ≤ 2`; see
`DegLeTwo.finrank_adjoin_le` together with `DegLeTwo.finiteDimensional`. -/
def DegLeTwo (t : ℝ) : Prop :=
  ∃ A B C : ℤ, ¬(A = 0 ∧ B = 0 ∧ C = 0) ∧ (A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ) = 0

theorem DegLeTwo.of_eq {t s : ℝ} (h : DegLeTwo t) (hts : s = t) : DegLeTwo s := hts ▸ h

/-- Degree ≤ 2 is symmetric under negation: replace `B` by `-B`. -/
theorem DegLeTwo.neg {t : ℝ} (h : DegLeTwo t) : DegLeTwo (-t) := by
  obtain ⟨A, B, C, hne, heq⟩ := h
  refine ⟨A, -B, C, ?_, ?_⟩
  · rintro ⟨h1, h2, h3⟩
    exact hne ⟨h1, by omega, h3⟩
  · push_cast
    linear_combination heq

/-- Rationals have degree one, hence at most two. -/
theorem degLeTwo_of_rat (q : ℚ) : DegLeTwo (q : ℝ) := by
  have hd : ((q.den : ℤ) : ℝ) ≠ 0 := by
    have : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.2 q.den_nz
    exact_mod_cast this
  refine ⟨0, (q.den : ℤ), -q.num, ?_, ?_⟩
  · rintro ⟨-, hb, -⟩
    exact q.den_nz (by exact_mod_cast hb)
  · rw [Rat.cast_def]
    push_cast
    field_simp
    ring

/-! ### The `SL₂(ℤ)` action -/

/-- **Möbius images inherit degree ≤ 2.**

If `u` is a root of `A Y² + B Y + C` and `t = (a u + b)/(c u + d)`, then `t` is a
root of the form obtained by acting with `M⁻¹`. That action is invertible
because `det M = 1` — acting back with `M` multiplies the coefficients by
`(ad - bc)² = 1` — which is why the new coefficients cannot all be zero. -/
theorem DegLeTwo.mobius {a b c d : ℤ} (hdet : a * d - b * c = 1) {u t : ℝ}
    (hden : (c : ℝ) * u + (d : ℝ) ≠ 0)
    (ht : t * ((c : ℝ) * u + (d : ℝ)) = (a : ℝ) * u + (b : ℝ))
    (h : DegLeTwo u) : DegLeTwo t := by
  obtain ⟨A, B, C, hne, heq⟩ := h
  refine ⟨A * d ^ 2 - B * c * d + C * c ^ 2,
          -2 * A * b * d + B * (a * d + b * c) - 2 * C * a * c,
          A * b ^ 2 - B * a * b + C * a ^ 2, ?_, ?_⟩
  · -- acting back with `M` recovers `(A, B, C)`, so the image is not zero
    rintro ⟨h1, h2, h3⟩
    refine hne ⟨?_, ?_, ?_⟩
    · linear_combination (a ^ 2) * h1 + (a * c) * h2 + (c ^ 2) * h3 -
        (A * (a * d - b * c + 1)) * hdet
    · linear_combination (2 * a * b) * h1 + (a * d + b * c) * h2 + (2 * c * d) * h3 -
        (B * (a * d - b * c + 1)) * hdet
    · linear_combination (b ^ 2) * h1 + (b * d) * h2 + (d ^ 2) * h3 -
        (C * (a * d - b * c + 1)) * hdet
  · push_cast
    have key : ((c : ℝ) * u + (d : ℝ)) ^ 2 *
        (((A : ℝ) * (d : ℝ) ^ 2 - (B : ℝ) * (c : ℝ) * (d : ℝ) + (C : ℝ) * (c : ℝ) ^ 2) * t ^ 2 +
          (-2 * (A : ℝ) * (b : ℝ) * (d : ℝ) + (B : ℝ) * ((a : ℝ) * (d : ℝ) + (b : ℝ) * (c : ℝ)) -
            2 * (C : ℝ) * (a : ℝ) * (c : ℝ)) * t +
          ((A : ℝ) * (b : ℝ) ^ 2 - (B : ℝ) * (a : ℝ) * (b : ℝ) + (C : ℝ) * (a : ℝ) ^ 2))
        = ((a : ℝ) * (d : ℝ) - (b : ℝ) * (c : ℝ)) ^ 2 *
          ((A : ℝ) * u ^ 2 + (B : ℝ) * u + (C : ℝ)) := by
      linear_combination
        (((A : ℝ) * (d : ℝ) ^ 2 - (B : ℝ) * (c : ℝ) * (d : ℝ) + (C : ℝ) * (c : ℝ) ^ 2) *
            (t * ((c : ℝ) * u + (d : ℝ)) + ((a : ℝ) * u + (b : ℝ))) +
          (-2 * (A : ℝ) * (b : ℝ) * (d : ℝ) +
              (B : ℝ) * ((a : ℝ) * (d : ℝ) + (b : ℝ) * (c : ℝ)) -
              2 * (C : ℝ) * (a : ℝ) * (c : ℝ)) * ((c : ℝ) * u + (d : ℝ))) * ht
    rw [heq, mul_zero] at key
    have := (mul_eq_zero.1 key).resolve_left (pow_ne_zero 2 hden)
    linear_combination this

/-! ### The field-theoretic reading -/

/-- A monic rational polynomial of degree at most two killing `t`. Dividing by
the leading coefficient is a case split, because that coefficient is allowed to
be zero — the degree-one case is the rationals. -/
theorem DegLeTwo.exists_monic {t : ℝ} (h : DegLeTwo t) :
    ∃ p : ℚ[X], p.Monic ∧ p.natDegree ≤ 2 ∧ aeval t p = 0 := by
  obtain ⟨A, B, C, hne, heq⟩ := h
  by_cases hA : A = 0
  · subst hA
    have hB : B ≠ 0 := by
      rintro rfl
      refine hne ⟨rfl, rfl, ?_⟩
      have : ((C : ℤ) : ℝ) = 0 := by push_cast at heq ⊢; linarith
      exact_mod_cast this
    have hBR : ((B : ℚ) : ℝ) ≠ 0 := by
      simpa using (show ((B : ℚ)) ≠ 0 by exact_mod_cast hB)
    refine ⟨X + Polynomial.C ((C : ℚ) / (B : ℚ)), monic_X_add_C _, by compute_degree!, ?_⟩
    simp only [map_add, aeval_X, aeval_C, eq_ratCast]
    push_cast at heq ⊢
    field_simp
    linarith
  · have hAR : ((A : ℚ) : ℝ) ≠ 0 := by
      simpa using (show ((A : ℚ)) ≠ 0 by exact_mod_cast hA)
    refine ⟨X ^ 2 + Polynomial.C ((B : ℚ) / (A : ℚ)) * X + Polynomial.C ((C : ℚ) / (A : ℚ)),
      by monicity!, by compute_degree!, ?_⟩
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, eq_ratCast]
    push_cast at heq ⊢
    field_simp
    linarith

theorem DegLeTwo.isIntegral {t : ℝ} (h : DegLeTwo t) : IsIntegral ℚ t := by
  obtain ⟨p, hm, -, he⟩ := h.exists_monic
  exact ⟨p, hm, he⟩

theorem DegLeTwo.natDegree_minpoly_le {t : ℝ} (h : DegLeTwo t) :
    (minpoly ℚ t).natDegree ≤ 2 := by
  obtain ⟨p, hm, hd, he⟩ := h.exists_monic
  exact le_trans (natDegree_le_natDegree (minpoly.min ℚ t hm he)) hd

/-- `ℚ(t)` is finite over `ℚ`. Stated because `Module.finrank` is `0` on an
infinite-dimensional space, so the bound below is only meaningful with this
alongside it. -/
theorem DegLeTwo.finiteDimensional {t : ℝ} (h : DegLeTwo t) :
    FiniteDimensional ℚ (IntermediateField.adjoin ℚ {t}) :=
  IntermediateField.adjoin.finiteDimensional h.isIntegral

/-- **`[ℚ(t) : ℚ] ≤ 2`.** -/
theorem DegLeTwo.finrank_adjoin_le {t : ℝ} (h : DegLeTwo t) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {t}) ≤ 2 := by
  rw [IntermediateField.adjoin.finrank h.isIntegral]
  exact h.natDegree_minpoly_le

end SternBrocot
