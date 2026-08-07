/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Bridge
import SternBrocot.Completeness
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# `Φ₀ : P(ω) → ℝ≥0`

The unsigned half of the order isomorphism. Every point of `P(ω)` is sent to the
supremum of the tree nodes strictly below it:

  `Φ₀ x = sSup { nodeValue bs | toSet bs <ₗ x }`

Because the nodes are order-isomorphic to `ℚ≥0` (`nodeValue_bijOn`,
`lexLt_toSet_iff`), the set being supped is exactly a downward-closed set of
nonnegative rationals — so this is a Dedekind cut, with the Stern–Brocot tree
supplying the copy of `ℚ`.

## Why `univ` must be excluded

`univ` is `∞`: every node lies below it, and node values are unbounded, so the
supremum does not exist. This is the concrete form of "drop the class of `ω` so
reciprocal goes partial at `0`". For every other `x` the set is bounded, and
`exists_node_above` produces the witness: if `n ∉ x`, then `(x ∩ [0,n)) ∪ {n}` is
a finite set strictly above `x`.

At the bottom nothing needs excluding: `below ∅` is empty and `Real.sSup ∅ = 0`,
so `Φ₀ ∅ = 0` comes out right on its own.

## Main results

* `SternBrocot.toReal₀_toSet` — **the correctness statement**: `Φ₀` agrees with
  `nodeValue` on the nodes. This is what pins `Φ₀` down as *the* Stern–Brocot
  map rather than some other order isomorphism.
* `SternBrocot.toReal₀_mono` — monotone.
* `SternBrocot.toReal₀_of_tailEqv` — constant on tail classes, so it descends to
  the quotient.
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

/-! ### The cut below a point -/

/-- The set of node values strictly below `x`, as reals. Downward closed in
`ℚ≥0`, so this is a Dedekind cut. -/
def below (x : Set ℕ) : Set ℝ := {r | ∃ bs : List Bool, toSet bs <ₗ x ∧ (nodeValue bs : ℝ) = r}

theorem below_nonneg {x : Set ℕ} {r : ℝ} (h : r ∈ below x) : 0 ≤ r := by
  obtain ⟨bs, -, rfl⟩ := h
  exact_mod_cast nodeValue_nonneg bs

theorem below_mono {x y : Set ℕ} (h : x <ₗ y) : below x ⊆ below y := by
  rintro r ⟨bs, hbs, rfl⟩
  exact ⟨bs, lexLt_trans hbs h, rfl⟩

@[simp] theorem below_empty : below (∅ : Set ℕ) = ∅ := by
  ext r
  simp only [below, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨bs, ⟨n, -, -, hmem⟩, -⟩
  exact hmem

/-- For any `x ≠ ∞` the cut is bounded, by the value of a node above `x`. -/
theorem bddAbove_below {x : Set ℕ} (h : x ≠ univ) : BddAbove (below x) := by
  obtain ⟨p, hp⟩ := exists_node_above h
  refine ⟨(nodeValue p : ℝ), ?_⟩
  rintro r ⟨bs, hbs, rfl⟩
  have : nodeValue bs < nodeValue p := (lexLt_toSet_iff bs p).1 (lexLt_trans hbs hp)
  exact_mod_cast this.le

/-! ### The map -/

/-- `Φ₀ x` is the supremum of the tree nodes strictly below `x`. -/
noncomputable def toReal₀ (x : Set ℕ) : ℝ := sSup (below x)

@[simp] theorem toReal₀_empty : toReal₀ (∅ : Set ℕ) = 0 := by
  rw [toReal₀, below_empty, Real.sSup_empty]

theorem toReal₀_nonneg (x : Set ℕ) : 0 ≤ toReal₀ x := by
  rcases Set.eq_empty_or_nonempty (below x) with h | ⟨r, hr⟩
  · rw [toReal₀, h, Real.sSup_empty]
  · rcases Classical.em (BddAbove (below x)) with hb | hb
    · exact le_trans (below_nonneg hr) (le_csSup hb hr)
    · -- at `∞` the supremum does not exist; `Real.sSup` returns `0` there
      rw [toReal₀, Real.sSup_def, dif_neg (by tauto)]

/-- **Monotonicity.** -/
theorem toReal₀_mono {x y : Set ℕ} (hxy : x <ₗ y) (hy : y ≠ univ) : toReal₀ x ≤ toReal₀ y := by
  rcases Set.eq_empty_or_nonempty (below x) with h | hne
  · rw [toReal₀, h, Real.sSup_empty]
    exact toReal₀_nonneg y
  · exact csSup_le hne fun r hr => le_csSup (bddAbove_below hy) (below_mono hxy hr)

/-! ### Correctness on the nodes

`Φ₀` agrees with `nodeValue` where both are defined. This is what identifies
`Φ₀` as the Stern–Brocot map: any other order isomorphism onto `ℝ≥0` would
disagree here. -/

/-- Every nonnegative rational strictly below a node's value is itself realised
by a node strictly below it — the tree is dense in itself. -/
theorem exists_node_between {cs : List Bool} {q : ℚ} (hq : 0 ≤ q) (hlt : q < nodeValue cs) :
    ∃ bs, toSet bs <ₗ toSet cs ∧ nodeValue bs = q := by
  obtain ⟨bs, -, hv⟩ := exists_canonical_of_nonneg hq
  exact ⟨bs, (lexLt_toSet_iff bs cs).2 (by rw [hv]; exact hlt), hv⟩

/-- **Correctness.** `Φ₀` reproduces `nodeValue` on the tree nodes. -/
theorem toReal₀_toSet (cs : List Bool) : toReal₀ (toSet cs) = (nodeValue cs : ℝ) := by
  have hub : ∀ r ∈ below (toSet cs), r ≤ (nodeValue cs : ℝ) := by
    rintro r ⟨bs, hbs, rfl⟩
    exact_mod_cast ((lexLt_toSet_iff bs cs).1 hbs).le
  rcases eq_or_lt_of_le (nodeValue_nonneg cs) with hzero | hpos
  · -- the node is `0`: nothing lies below it, and `sSup ∅ = 0`
    have hemp : below (toSet cs) = ∅ := by
      ext r
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨bs, hbs, rfl⟩
      have hlt := (lexLt_toSet_iff bs cs).1 hbs
      rw [← hzero] at hlt
      exact absurd hlt (not_lt.2 (nodeValue_nonneg bs))
    rw [toReal₀, hemp, Real.sSup_empty, ← hzero]
    norm_num
  · -- the node is positive: rationals below it are cofinal, by density of `ℚ`
    have hne : (below (toSet cs)).Nonempty :=
      ⟨0, [], (lexLt_toSet_iff [] cs).2 (by rw [nodeValue_nil]; exact hpos), by simp⟩
    refine le_antisymm (csSup_le hne hub) ?_
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hcon
    have hq0 : (0 : ℚ) ≤ q := by
      have h1 : (0 : ℝ) < (q : ℝ) := lt_of_le_of_lt (toReal₀_nonneg (toSet cs)) hq1
      exact_mod_cast h1.le
    obtain ⟨bs, hbs, hv⟩ := exists_node_between hq0 (by exact_mod_cast hq2)
    have hmem : ((q : ℚ) : ℝ) ∈ below (toSet cs) := ⟨bs, hbs, by rw [hv]⟩
    exact absurd (le_csSup (bddAbove_below (toSet_ne_univ cs)) hmem) (not_le.2 hq1)

/-! ### Descending to the quotient -/

/-- **`Φ₀` is constant on tail classes**, so it descends to `P(ω)/∼`.

A tail pair is an adjacent pair (`tailPair_iff_isAdjacent`), and nothing lies
strictly between adjacent points — in particular no node does — so the two cuts
coincide. -/
theorem toReal₀_of_tailPair {a b : Set ℕ} (h : TailPair a b) : toReal₀ a = toReal₀ b := by
  have hadj : IsAdjacent b a := isAdjacent_of_tailPair h
  -- The *right* element of a tail pair is cofinite, so it is never itself a node.
  -- Without this the two cuts would differ by exactly the point `b`.
  have hbinf : ¬ b.Finite := by
    rintro hfin
    obtain ⟨n, hn⟩ := h
    obtain ⟨N, hN⟩ := hfin.bddAbove
    have hmem : max n N + 1 ∈ b := hn.right_tail _ (by omega)
    have := hN hmem
    omega
  have hsub : below a ⊆ below b := by
    rintro r ⟨bs, hbs, rfl⟩
    rcases lexLt_trichotomy (toSet bs) b with hlt | heq | hgt
    · exact ⟨bs, hlt, rfl⟩
    · exact absurd (heq ▸ toSet_finite bs) hbinf
    · exact (hadj.2 _ hgt hbs).elim
  have hsup : below b ⊆ below a := below_mono hadj.1
  rw [toReal₀, toReal₀, Set.Subset.antisymm hsub hsup]

theorem toReal₀_of_tailEqv {a b : Set ℕ} (h : TailEqv a b) : toReal₀ a = toReal₀ b := by
  rcases h with rfl | h | h
  · rfl
  · exact toReal₀_of_tailPair h
  · exact (toReal₀_of_tailPair h).symm



/-! ### Surjectivity onto `ℝ≥0`

Given `r ≥ 0`, cut `P(ω)` at `r`: take the lex supremum of the nodes whose value
is below `r`. Completeness upstairs (`isLexLUB_lexSup`) supplies the point, and
density of `ℚ` pins its image to `r` exactly. -/

/-- The nodes whose value lies strictly below `r`. -/
def nodesBelow (r : ℝ) : Set (Set ℕ) := {z | ∃ bs, z = toSet bs ∧ (nodeValue bs : ℝ) < r}

/-- **Surjectivity.** Every nonnegative real is the image of a point of `P(ω)`
other than `∞`. -/
theorem exists_toReal₀_eq {r : ℝ} (hr : 0 ≤ r) : ∃ x : Set ℕ, x ≠ univ ∧ toReal₀ x = r := by
  classical
  -- A node strictly above `r`, to bound the cut.
  obtain ⟨Q, hQ⟩ := exists_rat_gt r
  have hQ0 : (0 : ℚ) ≤ Q := by
    have h1 : (0 : ℝ) < (Q : ℝ) := lt_of_le_of_lt hr hQ
    exact_mod_cast h1.le
  obtain ⟨p, -, hpv⟩ := exists_canonical_of_nonneg hQ0
  have hub : ∀ z ∈ nodesBelow r, z ≤ₗ toSet p := by
    rintro z ⟨bs, rfl, hv⟩
    refine lexLe_of_lexLt ((lexLt_toSet_iff bs p).2 ?_)
    rw [hpv]
    exact_mod_cast lt_trans hv hQ
  have hxle : lexSup (nodesBelow r) ≤ₗ toSet p := lexSup_least _ _ hub
  have hxne : lexSup (nodesBelow r) ≠ univ := by
    intro hc
    rw [hc] at hxle
    exact hxle (lexLt_univ_of_ne (toSet_ne_univ p))
  refine ⟨lexSup (nodesBelow r), hxne, ?_⟩
  -- Nothing below the cut reaches `r`: a node at or above `r` bounds the cut.
  have hbelow_lt : ∀ s ∈ below (lexSup (nodesBelow r)), s < r := by
    rintro s ⟨bs, hbs, rfl⟩
    by_contra hc
    rw [not_lt] at hc
    refine (lexSup_least (nodesBelow r) (toSet bs) ?_) hbs
    rintro z ⟨cs, rfl, hv⟩
    refine lexLe_of_lexLt ((lexLt_toSet_iff cs bs).2 ?_)
    exact_mod_cast lt_of_lt_of_le hv hc
  -- Every rational in `[0, r)` is realised strictly below the cut.
  have hlow : ∀ q : ℚ, 0 ≤ q → (q : ℝ) < r → ((q : ℚ) : ℝ) ∈ below (lexSup (nodesBelow r)) := by
    intro q hq0 hqr
    obtain ⟨bs, -, hv⟩ := exists_canonical_of_nonneg hq0
    -- a second node between `q` and `r` supplies the strictness
    obtain ⟨q', hq1, hq2⟩ := exists_rat_btwn hqr
    have hq'0 : (0 : ℚ) ≤ q' := le_trans hq0 (by exact_mod_cast hq1.le)
    obtain ⟨cs, -, hv'⟩ := exists_canonical_of_nonneg hq'0
    have hmem : toSet cs ∈ nodesBelow r := ⟨cs, rfl, by rw [hv']; exact hq2⟩
    have h1 : toSet bs <ₗ toSet cs :=
      (lexLt_toSet_iff bs cs).2 (by rw [hv, hv']; exact_mod_cast hq1)
    refine ⟨bs, ?_, by rw [hv]⟩
    rcases (lexLe_iff (toSet cs) _).1 (lexSup_upperBound _ _ hmem) with heq | hlt
    · rw [← heq]; exact h1
    · exact lexLt_trans h1 hlt
  rcases eq_or_lt_of_le hr with hzero | hpos
  · -- `r = 0`: the cut is empty and `lexSup ∅ = ∅`
    have hSempty : nodesBelow r = ∅ := by
      ext z
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨bs, rfl, hv⟩
      rw [← hzero] at hv
      exact absurd hv (not_lt.2 (by exact_mod_cast nodeValue_nonneg bs))
    have : lexSup (nodesBelow r) = ∅ :=
      (eq_lexSup_of_isLexLUB (S := nodesBelow r) (u := ∅)
        ⟨by rw [hSempty]; rintro x ⟨⟩, fun v _ => empty_lexLe v⟩).symm
    rw [this, toReal₀_empty, ← hzero]
  · -- `r > 0`: bounded above by `r`, and the rationals below `r` are cofinal
    have hne : (below (lexSup (nodesBelow r))).Nonempty := by
      refine ⟨((0 : ℚ) : ℝ), hlow 0 le_rfl ?_⟩
      exact_mod_cast hpos
    refine le_antisymm (csSup_le hne fun s hs => (hbelow_lt s hs).le) ?_
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hcon
    have hq0 : (0 : ℚ) ≤ q := by
      have h1 : (0 : ℝ) < (q : ℝ) := lt_of_le_of_lt (toReal₀_nonneg _) hq1
      exact_mod_cast h1.le
    exact absurd (le_csSup (bddAbove_below hxne) (hlow q hq0 hq2)) (not_le.2 hq1)

/-! ### Injectivity on the quotient

`Φ₀` separates points that the tail rule does not identify. The work is finding
*two* nodes strictly between them: one bounds `Φ₀ x` from above, the second makes
the comparison with `Φ₀ y` strict. -/

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

/-- **Strict monotonicity modulo the tail rule.** -/
theorem toReal₀_lt_of_not_tailEqv {x y : Set ℕ} (hlt : x <ₗ y) (hne : ¬ TailEqv x y)
    (hy : y ≠ univ) : toReal₀ x < toReal₀ y := by
  obtain ⟨p, hp1, hp2⟩ := exists_node_between_points hlt hne
  -- a second node, strictly above the first, still below `y`
  obtain ⟨q, hq1, hq2⟩ := exists_node_between_points hp2 (not_tailEqv_node hp2)
  have hxp : toReal₀ x ≤ (nodeValue p : ℝ) := by
    rcases Set.eq_empty_or_nonempty (below x) with hemp | hnem
    · rw [toReal₀, hemp, Real.sSup_empty]
      exact_mod_cast nodeValue_nonneg p
    · refine csSup_le hnem ?_
      rintro s ⟨bs, hbs, rfl⟩
      exact_mod_cast ((lexLt_toSet_iff bs p).1 (lexLt_trans hbs hp1)).le
  have hpq : (nodeValue p : ℝ) < (nodeValue q : ℝ) := by
    exact_mod_cast (lexLt_toSet_iff p q).1 hq1
  have hqy : (nodeValue q : ℝ) ≤ toReal₀ y := le_csSup (bddAbove_below hy) ⟨q, hq2, rfl⟩
  linarith

/-- **`Φ₀` is injective on the tail quotient.** Distinct classes have distinct
images, so together with `exists_toReal₀_eq` it is a bijection onto `ℝ≥0`. -/
theorem toReal₀_injective {x y : Set ℕ} (hx : x ≠ univ) (hy : y ≠ univ)
    (h : toReal₀ x = toReal₀ y) : TailEqv x y := by
  by_contra hne
  rcases lexLt_trichotomy x y with hlt | rfl | hgt
  · exact absurd h (ne_of_lt (toReal₀_lt_of_not_tailEqv hlt hne hy))
  · exact hne (TailEqv.refl x)
  · exact absurd h.symm (ne_of_lt (toReal₀_lt_of_not_tailEqv hgt (fun hc => hne hc.symm) hx))

end SternBrocot
