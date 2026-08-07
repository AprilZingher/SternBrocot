/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.SignedOrder
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

/-! ### Magnitude -/

/-- The magnitude's Stern–Brocot path: the stored bit exclusive-or'd with the
sign. On positives this is the stored bits; on negatives, their complement. -/
def magnitude (x : Signed) : Set ℕ := {n | ¬ (some n ∈ x ↔ none ∈ x)}

theorem magnitude_of_pos {x : Signed} (h : none ∉ x) : magnitude x = finPart x := by
  ext n
  simp only [magnitude, Set.mem_setOf_eq, mem_finPart]
  tauto

theorem magnitude_of_neg {x : Signed} (h : none ∈ x) : magnitude x = (finPart x)ᶜ := by
  ext n
  simp only [magnitude, Set.mem_setOf_eq, Set.mem_compl_iff, mem_finPart]
  tauto

@[simp] theorem magnitude_lift (y : Set ℕ) : magnitude (lift y) = y := by
  rw [magnitude_of_pos (none_notMem_lift y), finPart_lift]

@[simp] theorem magnitude_empty : magnitude (∅ : Signed) = ∅ := by
  rw [magnitude_of_pos (by simp), finPart_empty]

@[simp] theorem magnitude_univ : magnitude (univ : Signed) = ∅ := by
  rw [magnitude_of_neg (mem_univ _), finPart_univ, compl_univ]

/-- **Negation preserves the magnitude**, on the nose. `|-x| = |x|` is a rewrite,
not a case split — this is the payoff of the mirrored convention. -/
@[simp] theorem magnitude_neg (x : Signed) : magnitude (neg x) = magnitude x := by
  by_cases h : none ∈ x
  · rw [magnitude_of_pos (by simp [h]), magnitude_of_neg h, finPart_neg]
  · rw [magnitude_of_neg (by simp [h]), magnitude_of_pos h, finPart_neg, compl_compl]

/-- Reciprocal complements the magnitude, in both signs. -/
@[simp] theorem magnitude_recipS (x : Signed) : magnitude (recipS x) = (magnitude x)ᶜ := by
  by_cases h : none ∈ x
  · rw [magnitude_of_neg (by simp [h]), magnitude_of_neg h, finPart_recipS, compl_compl]
  · rw [magnitude_of_pos (by simp [h]), magnitude_of_pos h, finPart_recipS]

/-- A point is finite when its magnitude is not `∞`. The two infinities are
dropped when the field structure goes on, so that reciprocal becomes partial
at `0`. -/
def IsFinite (x : Signed) : Prop := magnitude x ≠ univ

theorem isFinite_lift {y : Set ℕ} (h : y ≠ univ) : IsFinite (lift y) := by
  rwa [IsFinite, magnitude_lift]

@[simp] theorem isFinite_neg {x : Signed} : IsFinite (neg x) ↔ IsFinite x := by
  rw [IsFinite, IsFinite, magnitude_neg]

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

end SternBrocot
