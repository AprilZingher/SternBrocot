/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.SignedOrder
import SternBrocot.Density

/-!
# Magnitude and finiteness

**`ℝ`-free**, and verifiably so: `Real` is not reachable through this file's
transitive import closure. That matters because `IsFinite` is the side condition
on every intrinsic operation, so if it lived downstream of `ℝ` then so would the
operations, and "the construction never mentions `ℝ`" could only be checked by
reading proofs rather than by the import graph.

`magnitude x` is the stored bit exclusive-or'd with the sign: on positives the
stored bits, on negatives their complement. That single formula is what makes
`|-x| = |x|` a rewrite rather than a case split (`magnitude_neg`), which is the
payoff of the mirrored convention.

`IsFinite x` says the magnitude is not `∞`. The two infinities are dropped when
the field structure goes on, so that reciprocal becomes partial at `0`.
-/

open Set

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

end SternBrocot
