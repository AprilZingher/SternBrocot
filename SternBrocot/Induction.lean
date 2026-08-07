/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Bridge

/-!
# Induction along the tree

The tree gives an induction principle: start at `0`, close under the two moves.
Because the nodes are exactly `ℚ≥0` (`nodeValue_bijOn`), that principle proves
statements about **all** nonnegative rationals, and with negation, about all of
`ℚ`.

## What this is good for, and what it is not

It is a genuinely different induction from Mathlib's, which goes `ℕ → ℤ → ℚ`
through `num` and `den`. Inducting along the tree is the right move when the tree
structure *is* the subject — mediants, Farey neighbours, the Euclidean algorithm,
`SL₂(ℤ)` actions, continued-fraction statements. For a generic fact like
`q + 0 = q` it is strictly worse than what already exists.

**It does not extend to `ℝ` on its own.** The moves generate the nodes, and the
nodes are exactly `ℚ≥0`; every real other than a rational is only a *limit* of
nodes. So getting from here to `ℝ` requires the predicate to survive limits —
i.e. to be closed — and at that point it is the ordinary density argument, which
Mathlib already supports (`DenseRange.equalizer`, `Continuous.ext_on`). Nothing
about the tree makes that step easier.

Where the tree is decisive is the opposite direction: statements about the
*expansion itself* (periodicity, approximation quality) and computation on the
streams, neither of which density arguments reach at all.

## Main results

* `SternBrocot.toSet_cons_true` / `toSet_cons_false` — a path's set is built by
  the moves `S` and `L` of `Basic.lean`, so the path picture and the original
  set-theoretic definition agree step by step.
* `SternBrocot.finite_induction` — induction over the finite subsets of `ω`.
* `SternBrocot.nonneg_rat_induction` — `P 0`, closed under `q ↦ q + 1` and
  `q ↦ q / (q + 1)`, proves `P` for every nonnegative rational.
* `SternBrocot.rat_induction` — with negation, for every rational.
-/

open Set

namespace SternBrocot

/-! ### The moves, on sets

A path prepends bits; `S` and `L` prepend to the set. These say the two pictures
are the same construction. -/

@[simp] theorem toSet_cons_true (bs : List Bool) : toSet (true :: bs) = S (toSet bs) := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp

@[simp] theorem toSet_cons_false (bs : List Bool) : toSet (false :: bs) = L (toSet bs) := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp

/-! ### Induction over the finite sets -/

/-- **Induction over `P(ω)`'s finite points.** Start at `∅` and close under the
two moves. -/
theorem finite_induction {P : Set ℕ → Prop} (h0 : P ∅)
    (hL : ∀ x : Set ℕ, P x → P (L x)) (hS : ∀ x : Set ℕ, P x → P (S x))
    {x : Set ℕ} (hx : x.Finite) : P x := by
  obtain ⟨bs, rfl⟩ := exists_path_of_finite hx
  clear hx
  induction bs with
  | nil => simpa using h0
  | cons b bs ih =>
    cases b
    · rw [toSet_cons_false]; exact hL _ ih
    · rw [toSet_cons_true]; exact hS _ ih

/-! ### Induction over the rationals

The two moves act on values as `q ↦ q + 1` and `q ↦ q / (q + 1)`, and the nodes
are exactly `ℚ≥0`, so this really does reach every nonnegative rational. -/

/-- **Induction over `ℚ≥0` along the tree.** -/
theorem nonneg_rat_induction {P : ℚ → Prop} (h0 : P 0)
    (hS : ∀ q : ℚ, 0 ≤ q → P q → P (q + 1))
    (hL : ∀ q : ℚ, 0 ≤ q → P q → P (q / (q + 1)))
    {q : ℚ} (hq : 0 ≤ q) : P q := by
  obtain ⟨bs, -, rfl⟩ := exists_canonical_of_nonneg hq
  clear hq
  induction bs with
  | nil => simpa using h0
  | cons b bs ih =>
    cases b
    · exact hL _ (nodeValue_nonneg bs) ih
    · exact hS _ (nodeValue_nonneg bs) ih

/-- **Induction over `ℚ` along the tree**, with negation for the other half. -/
theorem rat_induction {P : ℚ → Prop} (h0 : P 0)
    (hS : ∀ q : ℚ, 0 ≤ q → P q → P (q + 1))
    (hL : ∀ q : ℚ, 0 ≤ q → P q → P (q / (q + 1)))
    (hneg : ∀ q : ℚ, P q → P (-q)) (q : ℚ) : P q := by
  rcases le_or_gt 0 q with hq | hq
  · exact nonneg_rat_induction h0 hS hL hq
  · have hp := nonneg_rat_induction h0 hS hL (by linarith : (0 : ℚ) ≤ -q)
    simpa using hneg _ hp

end SternBrocot
