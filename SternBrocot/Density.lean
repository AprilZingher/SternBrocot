/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Bridge
import SternBrocot.Completeness

/-!
# Density of the nodes

**This file mentions `ℝ` nowhere, and neither does anything it imports.** That is
the point of it: these are the facts that make the tree nodes a dense copy of `ℚ`
inside `P(ω)`, and every one of them is a statement about the lex order alone.

They used to live in `ToReal.lean` and so inherited its `ℝ` import for no reason.
Splitting them out is the first step of making "the construction never mentions
`ℝ`" a claim checkable from the **import graph** rather than by reading proofs.

## Why these are the load-bearing ones

An `ℝ`-free development of the field axioms goes through Dedekind cuts, not
limits — the carrier has no topology and does not need one. What a cut argument
needs is exactly:

* a node above any point that is not `∞` (`exists_node_above`), so cuts are
  bounded;
* a node strictly between any two points the tail rule does not identify
  (`exists_node_between_points`), so a point is determined by the nodes below it.

`Completeness.lean` supplies the third ingredient, the least upper bound itself.
Together those three are enough to characterise `+` and `×` by their cuts with no
mention of `ℝ` at any point.

## Main results

* `SternBrocot.exists_node_above` — a node above any non-`∞` point.
* `SternBrocot.exists_node_between_points` — **density**: a node lies strictly
  between any two tail-inequivalent points.
* `SternBrocot.not_tailEqv_node` — a node is never tail-equivalent to something
  strictly above it, which is what stops the density argument degenerating.
-/

open Set

namespace SternBrocot

/-! ### A node above any non-`∞` point -/

/-- Any point other than `∞` has a tree node strictly above it: truncate at a
missing bit and set that bit. -/
theorem exists_node_above {x : Set ℕ} (h : x ≠ univ) : ∃ p : List Bool, x <ₗ toSet p := by
  have hex : ∃ n, n ∉ x := by
    by_contra hc
    rw [not_exists] at hc
    exact h (eq_univ_of_forall fun n => not_not.1 (hc n))
  obtain ⟨n, hn⟩ := hex
  have hfin : ((x ∩ Iio n) ∪ {n}).Finite := by
    apply Set.Finite.subset (Set.finite_lt_nat (n + 1))
    rintro k (⟨-, hk⟩ | hk)
    · exact Nat.lt_succ_of_lt (mem_Iio.1 hk)
    · rw [mem_singleton_iff] at hk
      exact hk ▸ Nat.lt_succ_self n
  obtain ⟨p, hp⟩ := exists_path_of_finite hfin
  refine ⟨p, n, fun k hk => ?_, hn, ?_⟩
  · rw [hp]
    simp only [Set.mem_union, Set.mem_inter_iff, mem_Iio, mem_singleton_iff]
    constructor
    · intro hkx; exact Or.inl ⟨hkx, hk⟩
    · rintro (⟨hkx, -⟩ | rfl)
      · exact hkx
      · exact absurd hk (lt_irrefl k)
  · rw [hp]; exact Or.inr rfl

/-- A node is a finite set, so it is never `∞`. -/
theorem toSet_ne_univ (bs : List Bool) : toSet bs ≠ univ := by
  intro hc
  have hmem : bs.length ∈ toSet bs := hc ▸ mem_univ _
  exact absurd (mem_Iio.1 (toSet_subset_Iio bs hmem)) (lt_irrefl _)

/-! ### A node strictly between two points -/

/-- Truncating `y` at the first place it exceeds `x` gives a node above `x` and
no higher than `y`. -/
theorem exists_node_ge {x y : Set ℕ} (h : x <ₗ y) : ∃ p, x <ₗ toSet p ∧ toSet p ≤ₗ y := by
  obtain ⟨n, hagree, hnx, hny⟩ := h
  have hfin : ((x ∩ Iio n) ∪ {n}).Finite := by
    apply Set.Finite.subset (Set.finite_lt_nat (n + 1))
    rintro k (⟨-, hk⟩ | hk)
    · exact Nat.lt_succ_of_lt (mem_Iio.1 hk)
    · rw [mem_singleton_iff] at hk
      exact hk ▸ Nat.lt_succ_self n
  obtain ⟨p, hp⟩ := exists_path_of_finite hfin
  refine ⟨p, ⟨n, fun k hk => ?_, hnx, ?_⟩, ?_⟩
  · rw [hp]
    simp only [Set.mem_union, Set.mem_inter_iff, mem_Iio, mem_singleton_iff]
    exact ⟨fun hkx => Or.inl ⟨hkx, hk⟩, by
      rintro (⟨hkx, -⟩ | rfl)
      · exact hkx
      · exact absurd hk (lt_irrefl k)⟩
  · rw [hp]; exact Or.inr rfl
  · -- nothing in the truncation can push it past `y`
    rintro ⟨m, hagree', hmy, hmp⟩
    rw [hp] at hmp
    rcases hmp with ⟨hmx, hmlt⟩ | hmn
    · exact hmy ((hagree m (mem_Iio.1 hmlt)).1 hmx)
    · rw [mem_singleton_iff] at hmn
      exact hmy (hmn ▸ hny)

/-- A node is finite, but the lower side of a tail pair is cofinite, so a node is
never tail-equivalent to something strictly above it. -/
theorem not_tailEqv_node {p : List Bool} {y : Set ℕ} (h : toSet p <ₗ y) :
    ¬ TailEqv (toSet p) y := by
  rintro (rfl | hpair | hpair)
  · exact lexLt_irrefl _ h
  · exact lexLt_asymm h (lexLt_of_tailPair hpair)
  · -- `TailPair y (toSet p)` makes `toSet p` the cofinite side, yet it is finite
    obtain ⟨n, hn⟩ := hpair
    obtain ⟨N, hN⟩ := (toSet_finite p).bddAbove
    have hmem : max n N + 1 ∈ toSet p := hn.right_tail _ (by omega)
    have := hN hmem
    omega

/-- **A node lies strictly between any two tail-inequivalent points.** -/
theorem exists_node_between_points {x y : Set ℕ} (hlt : x <ₗ y) (hne : ¬ TailEqv x y) :
    ∃ p, x <ₗ toSet p ∧ toSet p <ₗ y := by
  obtain ⟨z, hxz, hzy⟩ := exists_between_of_not_tailEqv hlt hne
  obtain ⟨p, hp1, hp2⟩ := exists_node_ge hxz
  refine ⟨p, hp1, ?_⟩
  rcases (lexLe_iff (toSet p) z).1 hp2 with rfl | hlt'
  · exact hzy
  · exact lexLt_trans hlt' hzy

end SternBrocot
