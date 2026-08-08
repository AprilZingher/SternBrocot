/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Magnitude
import SternBrocot.ToReal

/-!
# `Φ : P(ω + 1) → ℝ`

The signed value map, obtained by mirroring `Φ₀` across the sign coordinate.

Under the mirrored convention the stored bits are the magnitude's Stern–Brocot
path on the positive branch and its **complement** on the negative branch, so the
magnitude is recovered uniformly by

  `magnitude x = {n | ¬(n ∈ x ↔ x is negative)}`

— the stored bit exclusive-or'd with the sign. Then `Φ x` is `±Φ₀(magnitude x)`.

## What this buys

* `magnitude_neg` — negation leaves the magnitude alone, on the nose. This is
  where the mirrored convention pays: `|-x| = |x|` is a rewriting identity
  rather than a case split.
* `toReal_neg` — `Φ(-x) = -Φ(x)`, immediately.
* `toReal_empty` and `toReal_univ` are both `0`, so `-0 = 0` is respected by the value
  map without any special casing — the zero adjacency is already invisible to `Φ`.

## Main results

* `SternBrocot.toReal_lift` — on positives, `Φ` is `Φ₀`, so the naturals land where
  they should.
* `SternBrocot.toReal_neg` — `Φ` intertwines complement with negation in `ℝ`.
* `SternBrocot.toReal_of_seqv` — `Φ` is constant on the full quotient, so it
  descends to `P(ω+1)/SEqv`.
-/

open Set
open scoped symmDiff

namespace SternBrocot

/-! ### The signed value map -/

open Classical in
/-- `Φ x = ±Φ₀(magnitude x)`, with the sign taken from the sign coordinate. -/
noncomputable def toReal (x : Signed) : ℝ :=
  if none ∈ x then -(toReal₀ (magnitude x)) else toReal₀ (magnitude x)

theorem toReal_of_pos {x : Signed} (h : none ∉ x) : toReal x = toReal₀ (magnitude x) := by
  rw [toReal, if_neg h]

theorem toReal_of_neg {x : Signed} (h : none ∈ x) : toReal x = -(toReal₀ (magnitude x)) := by
  rw [toReal, if_pos h]

/-- On the positive branch `Φ` is `Φ₀`, so the naturals land exactly where the
unsigned development puts them. -/
@[simp] theorem toReal_lift (y : Set ℕ) : toReal (lift y) = toReal₀ y := by
  rw [toReal_of_pos (none_notMem_lift y), magnitude_lift]

@[simp] theorem toReal_empty : toReal (∅ : Signed) = 0 := by
  rw [toReal_of_pos (by simp), magnitude_empty, toReal₀_empty]

/-- `-0` also lands on `0`: the zero adjacency is invisible to `Φ`, so no special
casing is needed to make `-0 = 0` hold downstream. -/
@[simp] theorem toReal_univ : toReal (univ : Signed) = 0 := by
  rw [toReal_of_neg (mem_univ _), magnitude_univ, toReal₀_empty, neg_zero]

/-- **`Φ` intertwines complement with negation in `ℝ`.** -/
@[simp] theorem toReal_neg (x : Signed) : toReal (neg x) = - toReal x := by
  by_cases h : none ∈ x
  · rw [toReal_of_pos (by simp [h]), toReal_of_neg h, magnitude_neg, _root_.neg_neg]
  · rw [toReal_of_neg (by simp [h]), toReal_of_pos h, magnitude_neg]

theorem toReal_nonneg_of_pos {x : Signed} (h : none ∉ x) : 0 ≤ toReal x := by
  rw [toReal_of_pos h]
  exact toReal₀_nonneg _

theorem toReal_nonpos_of_neg {x : Signed} (h : none ∈ x) : toReal x ≤ 0 := by
  rw [toReal_of_neg h]
  simpa using toReal₀_nonneg (magnitude x)

/-! ### Descending to the quotient -/

/-- Complementing both sides of a tail pair gives a tail pair again, so the
negative branch is as well-behaved as the positive one. -/
theorem toReal₀_compl_of_tailPair {a b : Set ℕ} (h : TailPair a b) :
    toReal₀ aᶜ = toReal₀ bᶜ := by
  obtain ⟨n, hn⟩ := h
  exact (toReal₀_of_tailPair ⟨n, hn.compl⟩).symm

theorem toReal_of_stailPair {a b : Signed} (h : STailPair a b) : toReal a = toReal b := by
  by_cases hs : none ∈ a
  · have hs' : none ∈ b := h.1.1 hs
    rw [toReal_of_neg hs, toReal_of_neg hs', magnitude_of_neg hs, magnitude_of_neg hs',
      toReal₀_compl_of_tailPair h.2]
  · have hs' : none ∉ b := fun hc => hs (h.1.2 hc)
    rw [toReal_of_pos hs, toReal_of_pos hs', magnitude_of_pos hs, magnitude_of_pos hs',
      toReal₀_of_tailPair h.2]

/-- **`Φ` is constant on the full quotient** — the tail rule *and* the zero
adjacency — so it descends to `P(ω+1)/SEqv`. -/
theorem toReal_of_seqv {a b : Signed} (h : SEqv a b) : toReal a = toReal b := by
  rcases h with (rfl | hp | hp) | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact toReal_of_stailPair hp
  · exact (toReal_of_stailPair hp).symm
  · rw [toReal_empty, toReal_univ]
  · rw [toReal_univ, toReal_empty]

/-! ### Monotone

Two cases, matching `SLexLt`. Across the sign boundary the comparison is
`≤ 0 ≤`; within a sign it is `toReal₀_mono`, on the complemented paths when
negative — where `compl_lexLt_compl` supplies the reversal that the extra minus
sign then undoes. -/

theorem toReal_mono {x y : Signed} (h : x <ₛ y) (hx : IsFinite x) (hy : IsFinite y) :
    toReal x ≤ toReal y := by
  rcases h with ⟨hxs, hys⟩ | ⟨hs, hf⟩
  · exact le_trans (toReal_nonpos_of_neg hxs) (toReal_nonneg_of_pos hys)
  · by_cases hxn : none ∈ x
    · have hyn : none ∈ y := hs.1 hxn
      rw [toReal_of_neg hxn, toReal_of_neg hyn, neg_le_neg_iff,
        magnitude_of_neg hxn, magnitude_of_neg hyn]
      refine toReal₀_mono (compl_lexLt_compl.2 hf) ?_
      rwa [IsFinite, magnitude_of_neg hxn] at hx
    · have hyn : none ∉ y := fun hc => hxn (hs.2 hc)
      rw [toReal_of_pos hxn, toReal_of_pos hyn, magnitude_of_pos hxn, magnitude_of_pos hyn]
      refine toReal₀_mono hf ?_
      rwa [IsFinite, magnitude_of_pos hyn] at hy

/-! ### Surjectivity onto all of `ℝ`

Nonnegative reals come from `exists_toReal₀_eq` on the positive branch; negative
ones are the negation of the corresponding positive point. -/

/-- **Surjectivity.** Every real is the value of a finite point of `P(ω+1)`. -/
theorem exists_toReal_eq (r : ℝ) : ∃ x : Signed, IsFinite x ∧ toReal x = r := by
  rcases le_or_gt 0 r with hr | hr
  · obtain ⟨y, hy, hv⟩ := exists_toReal₀_eq hr
    exact ⟨lift y, isFinite_lift hy, by rw [toReal_lift, hv]⟩
  · obtain ⟨y, hy, hv⟩ := exists_toReal₀_eq (by linarith : (0 : ℝ) ≤ -r)
    refine ⟨neg (lift y), by simpa using isFinite_lift hy, ?_⟩
    rw [toReal_neg, toReal_lift, hv, _root_.neg_neg]

/-! ### Injectivity on the quotient -/

theorem eq_empty_of_tailEqv_empty {x : Set ℕ} (h : TailEqv x ∅) : x = ∅ := by
  rcases h with rfl | hp | hp
  · rfl
  · exact absurd hp not_tailPair_empty_right
  · exact absurd hp not_tailPair_empty_left

theorem toReal₀_eq_zero {x : Set ℕ} (hx : x ≠ univ) (h : toReal₀ x = 0) : x = ∅ :=
  eq_empty_of_tailEqv_empty
    (toReal₀_injective hx Set.empty_ne_univ (by rw [h, toReal₀_empty]))

/-- Complementing both sides of a tail pair gives a tail pair the other way
round, so tail-equivalence survives the mirror. -/
theorem tailPair_of_compl {a b : Set ℕ} (h : TailPair aᶜ bᶜ) : TailPair b a := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  have hc := hn.compl
  rwa [compl_compl, compl_compl] at hc

/-- **Injectivity.** Points with the same value are identified by the full
quotient — including the two zeros, which is the mixed-sign case. -/
theorem toReal_injective {x y : Signed} (hx : IsFinite x) (hy : IsFinite y)
    (h : toReal x = toReal y) : SEqv x y := by
  by_cases hxn : none ∈ x <;> by_cases hyn : none ∈ y
  · -- both negative: compare the complemented paths
    rw [toReal_of_neg hxn, toReal_of_neg hyn, neg_inj,
      magnitude_of_neg hxn, magnitude_of_neg hyn] at h
    have ht := toReal₀_injective (by rwa [IsFinite, magnitude_of_neg hxn] at hx)
      (by rwa [IsFinite, magnitude_of_neg hyn] at hy) h
    rcases ht with heq | hp | hp
    · exact Or.inl (Or.inl (signed_ext (compl_injective heq) (by simp [hxn, hyn])))
    · exact Or.inl (Or.inr (Or.inr ⟨by simp [hxn, hyn], tailPair_of_compl hp⟩))
    · exact Or.inl (Or.inr (Or.inl ⟨by simp [hxn, hyn], tailPair_of_compl hp⟩))
  · -- `x` negative, `y` positive: both values are squeezed to `0`
    have hx0 : toReal x = 0 := by
      have h1 := toReal_nonpos_of_neg hxn
      have h2 := toReal_nonneg_of_pos hyn
      linarith
    have hy0 : toReal y = 0 := by rw [← h]; exact hx0
    have hxu : x = univ := by
      rw [toReal_of_neg hxn, neg_eq_zero, magnitude_of_neg hxn] at hx0
      have := toReal₀_eq_zero (by rwa [IsFinite, magnitude_of_neg hxn] at hx) hx0
      exact signed_ext (by rw [finPart_univ, ← compl_compl (finPart x), this, compl_empty])
        (by simp [hxn])
    have hye : y = ∅ := by
      rw [toReal_of_pos hyn, magnitude_of_pos hyn] at hy0
      have := toReal₀_eq_zero (by rwa [IsFinite, magnitude_of_pos hyn] at hy) hy0
      exact signed_ext (by rw [finPart_empty, this]) (by simp [hyn])
    exact Or.inr (Or.inr ⟨hxu, hye⟩)
  · -- mirror image of the previous case
    have hy0 : toReal y = 0 := by
      have h1 := toReal_nonpos_of_neg hyn
      have h2 := toReal_nonneg_of_pos hxn
      linarith
    have hx0 : toReal x = 0 := by rw [h]; exact hy0
    have hyu : y = univ := by
      rw [toReal_of_neg hyn, neg_eq_zero, magnitude_of_neg hyn] at hy0
      have := toReal₀_eq_zero (by rwa [IsFinite, magnitude_of_neg hyn] at hy) hy0
      exact signed_ext (by rw [finPart_univ, ← compl_compl (finPart y), this, compl_empty])
        (by simp [hyn])
    have hxe : x = ∅ := by
      rw [toReal_of_pos hxn, magnitude_of_pos hxn] at hx0
      have := toReal₀_eq_zero (by rwa [IsFinite, magnitude_of_pos hxn] at hx) hx0
      exact signed_ext (by rw [finPart_empty, this]) (by simp [hxn])
    exact Or.inr (Or.inl ⟨hxe, hyu⟩)
  · -- both positive: straight from the unsigned case
    rw [toReal_of_pos hxn, toReal_of_pos hyn,
      magnitude_of_pos hxn, magnitude_of_pos hyn] at h
    have ht := toReal₀_injective (by rwa [IsFinite, magnitude_of_pos hxn] at hx)
      (by rwa [IsFinite, magnitude_of_pos hyn] at hy) h
    rcases ht with heq | hp | hp
    · exact Or.inl (Or.inl (signed_ext heq (by simp [hxn, hyn])))
    · exact Or.inl (Or.inr (Or.inl ⟨by simp [hxn, hyn], hp⟩))
    · exact Or.inl (Or.inr (Or.inr ⟨by simp [hxn, hyn], hp⟩))

end SternBrocot
