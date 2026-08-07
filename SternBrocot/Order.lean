/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Tail
import Mathlib.Order.PiLex
import Mathlib.Order.PropInstances
import Mathlib.Data.Nat.Find
import Mathlib.Order.Interval.Set.Basic

/-!
# The lexicographic order, and the key lemma

`P(ω)` is ordered by *least point of difference*: `x < y` when at the first bit
where they differ, `y` has the bit and `x` does not. Since a `1` bit is a step
right in the Stern–Brocot tree, this is the order induced from `[0, ∞]`.

The main result is the lemma flagged as the one most likely to bite:

> `x ∼ y` (the tail relation) **iff** `x` and `y` are adjacent in the lex order.

This is what makes the quotient `P(ω)/∼` *densely* ordered: the tail relation
collapses exactly the jumps and nothing else. Everything downstream — density,
the countable dense subset, and Cantor's back-and-forth — rests on it.

## Main results

* `SternBrocot.lexLt_trans`, `lexLt_trichotomy`, `lexLt_irrefl` — `<ₗ` is a
  strict linear order, from well-foundedness of `ω` (a least point of difference
  exists).
* `SternBrocot.tailPair_iff_isAdjacent` — **the key lemma**: `TailPair a b` iff
  `b < a` with nothing strictly between.
* `SternBrocot.lexLt_of_tailPair` — a tail pair is always oriented `b < a`: the
  side carrying the branch point is the larger one.
-/

open Set
open scoped symmDiff

namespace SternBrocot

/-! ### Least point of difference -/

/-- Well-foundedness of `ω`, in the form used throughout: a nonempty predicate on
`ℕ` has a least witness. -/
theorem exists_least {P : ℕ → Prop} (h : ∃ n, P n) : ∃ n, P n ∧ ∀ k < n, ¬ P k := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, fun _ hk => Nat.find_min h hk⟩

/-- Distinct subsets of `ω` have a least point of difference. This is the only
place well-foundedness is used, and it is what makes the lex order linear. -/
theorem exists_least_diff {x y : Set ℕ} (h : x ≠ y) :
    ∃ n, ¬(n ∈ x ↔ n ∈ y) ∧ ∀ k < n, (k ∈ x ↔ k ∈ y) := by
  have hex : ∃ n, ¬(n ∈ x ↔ n ∈ y) := by
    by_contra hc
    exact h (Set.ext fun n => not_not.mp fun hn => hc ⟨n, hn⟩)
  obtain ⟨n, hn, hmin⟩ := exists_least hex
  exact ⟨n, hn, fun k hk => not_not.mp (hmin k hk)⟩

/-! ### The lexicographic order -/

/-- `x < y` in the lex order: at the least point of difference `n`, `y` has the
bit and `x` does not. A `1` bit is a step right in the tree, so this is the order
inherited from `[0, ∞]`. -/
def LexLt (x y : Set ℕ) : Prop :=
  ∃ n, (∀ k < n, (k ∈ x ↔ k ∈ y)) ∧ n ∉ x ∧ n ∈ y

@[inherit_doc] scoped infix:50 " <ₗ " => LexLt

theorem lexLt_irrefl (x : Set ℕ) : ¬ (x <ₗ x) := by
  rintro ⟨n, -, hx, hx'⟩
  exact hx hx'

theorem lexLt_trans {x y z : Set ℕ} (hxy : x <ₗ y) (hyz : y <ₗ z) : x <ₗ z := by
  obtain ⟨n₁, hb₁, hx₁, hy₁⟩ := hxy
  obtain ⟨n₂, hb₂, hy₂, hz₂⟩ := hyz
  rcases lt_trichotomy n₁ n₂ with hlt | rfl | hgt
  · -- The first difference of `x` and `z` is at `n₁`.
    exact ⟨n₁, fun k hk => (hb₁ k hk).trans (hb₂ k (hk.trans hlt)), hx₁, (hb₂ n₁ hlt).mp hy₁⟩
  · -- Impossible: `n₁ ∈ y` and `n₁ ∉ y`.
    exact absurd hy₁ hy₂
  · -- The first difference of `x` and `z` is at `n₂`.
    exact ⟨n₂, fun k hk => (hb₁ k (hk.trans hgt)).trans (hb₂ k hk),
      fun hmem => hy₂ ((hb₁ n₂ hgt).mp hmem), hz₂⟩

theorem lexLt_asymm {x y : Set ℕ} (h : x <ₗ y) : ¬ (y <ₗ x) :=
  fun h' => lexLt_irrefl x (lexLt_trans h h')

theorem lexLt_trichotomy (x y : Set ℕ) : x <ₗ y ∨ x = y ∨ y <ₗ x := by
  by_cases hxy : x = y
  · exact Or.inr (Or.inl hxy)
  obtain ⟨n, hn, hmin⟩ := exists_least_diff hxy
  by_cases hx : n ∈ x
  · refine Or.inr (Or.inr ⟨n, fun k hk => (hmin k hk).symm, ?_, hx⟩)
    exact fun hmem => hn ⟨fun _ => hmem, fun _ => hx⟩
  · refine Or.inl ⟨n, hmin, hx, ?_⟩
    by_contra hy
    exact hn ⟨fun h => absurd h hx, fun h => absurd h hy⟩

/-! ### Tail pairs are adjacent -/

/-- `b` is immediately below `a`: `b < a` with nothing strictly between. -/
def IsAdjacent (b a : Set ℕ) : Prop :=
  b <ₗ a ∧ ∀ z, b <ₗ z → ¬ (z <ₗ a)

/-- A tail pair is oriented: the side carrying the branch point is the larger.
`s ⌢ 1 ⌢ 0^∞` sits above `s ⌢ 0 ⌢ 1^∞`. -/
theorem lexLt_of_isTailPairAt {n : ℕ} {a b : Set ℕ} (h : IsTailPairAt n a b) : b <ₗ a :=
  ⟨n, fun k hk => (h.below k hk).symm, h.notMem_right, h.mem_left⟩

theorem lexLt_of_tailPair {a b : Set ℕ} (h : TailPair a b) : b <ₗ a :=
  let ⟨_, h⟩ := h; lexLt_of_isTailPairAt h

/-- **Tail pairs are adjacent.** Nothing sits strictly between the two
representations of a node. -/
theorem isAdjacent_of_tailPair {a b : Set ℕ} (hab : TailPair a b) : IsAdjacent b a := by
  obtain ⟨n, h⟩ := hab
  refine ⟨lexLt_of_isTailPairAt h, ?_⟩
  rintro z ⟨p, hbp, hbz, hzp⟩ ⟨q, hqz, hqz', hqa⟩
  rcases lt_trichotomy p n with hlt | rfl | hgt
  · -- `z` overtakes `b` strictly below the branch point, hence also overtakes
    -- `a`, which agrees with `b` there. So `a <ₗ z`, contradicting `z <ₗ a`.
    refine lexLt_asymm (y := z) ⟨p, fun k hk => ?_, ?_, hzp⟩ ⟨q, hqz, hqz', hqa⟩
    · exact (h.below k (hk.trans hlt)).trans (hbp k hk)
    · exact fun hmem => hbz ((h.below p hlt).mp hmem)
  · -- `z` and `a` agree below the branch point and both contain it, so they can
    -- only differ above it — but `a` is empty above it.
    have hqp : ¬ (p < q) := fun hlt => h.left_top q hlt hqa
    rcases lt_or_eq_of_le (not_lt.mp hqp) with hq | rfl
    · exact hqz' ((hbp q hq).mp ((h.below q hq).mp hqa))
    · exact hqz' hzp
  · -- `b` contains everything above the branch point, so it cannot be the one
    -- missing a bit at `p > n`.
    exact hbz (h.right_tail p hgt)

/-! ### Adjacent pairs are tail pairs

The direction with content. If `b < a` with nothing between, then `a` must stop
at the branch point and `b` must be full above it — otherwise we exhibit an
explicit intermediate point. -/

/-- If `a` carries a bit above the branch point, truncating `a` just after the
branch point produces a point strictly between `b` and `a`. -/
theorem exists_between_of_mem_above {a b : Set ℕ} {n : ℕ}
    (hbelow : ∀ k < n, (k ∈ b ↔ k ∈ a)) (hnb : n ∉ b) (hna : n ∈ a)
    (hex : ∃ k, n < k ∧ k ∈ a) : ∃ z, b <ₗ z ∧ z <ₗ a := by
  obtain ⟨q, ⟨hqn, hqa⟩, hqmin⟩ := exists_least hex
  refine ⟨(a ∩ Iio n) ∪ {n}, ⟨n, ?_, hnb, ?_⟩, ⟨q, ?_, ?_, hqa⟩⟩
  · -- `b` and `z` agree strictly below `n`.
    intro j hj
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iio, Set.mem_singleton_iff]
    constructor
    · exact fun hjb => Or.inl ⟨(hbelow j hj).mp hjb, hj⟩
    · rintro (⟨hja, -⟩ | rfl)
      · exact (hbelow j hj).mpr hja
      · exact absurd hj (lt_irrefl _)
  · simp
  · -- `z` and `a` agree strictly below `q`.
    intro j hj
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iio, Set.mem_singleton_iff]
    rcases lt_trichotomy j n with hjn | rfl | hjn
    · constructor
      · rintro (⟨hja, -⟩ | rfl)
        · exact hja
        · exact absurd hjn (lt_irrefl _)
      · exact fun hja => Or.inl ⟨hja, hjn⟩
    · exact ⟨fun _ => hna, fun _ => Or.inr rfl⟩
    · constructor
      · rintro (⟨-, hlt⟩ | rfl)
        · exact absurd hlt (not_lt.2 hjn.le)
        · exact absurd hjn (lt_irrefl _)
      · exact fun hja => absurd ⟨hjn, hja⟩ (hqmin j hj)
  · -- `q` lies above `n`, so it is outside the truncation.
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iio, Set.mem_singleton_iff]
    rintro (⟨-, hlt⟩ | rfl)
    · exact absurd hlt (not_lt.2 hqn.le)
    · exact absurd hqn (lt_irrefl _)

/-- If `b` misses a bit above the branch point, filling `b` in above the branch
point produces a point strictly between `b` and `a`. -/
theorem exists_between_of_notMem_above {a b : Set ℕ} {n : ℕ}
    (hbelow : ∀ k < n, (k ∈ b ↔ k ∈ a)) (hnb : n ∉ b) (hna : n ∈ a)
    (hex : ∃ k, n < k ∧ k ∉ b) : ∃ z, b <ₗ z ∧ z <ₗ a := by
  obtain ⟨q, ⟨hqn, hqb⟩, hqmin⟩ := exists_least hex
  refine ⟨(b ∩ Iio n) ∪ Ioi n, ⟨q, ?_, hqb, ?_⟩, ⟨n, ?_, ?_, hna⟩⟩
  · -- `b` and `z` agree strictly below `q`.
    intro j hj
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi]
    rcases lt_trichotomy j n with hjn | rfl | hjn
    · constructor
      · exact fun hjb => Or.inl ⟨hjb, hjn⟩
      · rintro (⟨hjb, -⟩ | hlt)
        · exact hjb
        · exact absurd hlt (not_lt.2 hjn.le)
    · constructor
      · exact fun hjb => absurd hjb hnb
      · rintro (⟨-, hlt⟩ | hlt) <;> exact absurd hlt (lt_irrefl _)
    · constructor
      · exact fun _ => Or.inr hjn
      · exact fun _ => not_not.mp fun hb => hqmin j hj ⟨hjn, hb⟩
  · simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi]
    exact Or.inr hqn
  · -- `z` and `a` agree strictly below `n`.
    intro j hj
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi]
    constructor
    · rintro (⟨hjb, -⟩ | hlt)
      · exact (hbelow j hj).mp hjb
      · exact absurd (hj.trans hlt) (lt_irrefl _)
    · exact fun hja => Or.inl ⟨(hbelow j hj).mpr hja, hj⟩
  · simp

/-- **Adjacent pairs are tail pairs.** -/
theorem tailPair_of_isAdjacent {a b : Set ℕ} (h : IsAdjacent b a) : TailPair a b := by
  obtain ⟨⟨n, hbelow, hnb, hna⟩, hbetween⟩ := h
  refine ⟨n, ⟨fun k hk => (hbelow k hk).symm, hna, ?_, hnb, ?_⟩⟩
  · -- `a` has nothing above `n`.
    intro k hk hka
    obtain ⟨z, hbz, hza⟩ := exists_between_of_mem_above hbelow hnb hna ⟨k, hk, hka⟩
    exact hbetween z hbz hza
  · -- `b` contains everything above `n`.
    intro k hk
    by_contra hkb
    obtain ⟨z, hbz, hza⟩ := exists_between_of_notMem_above hbelow hnb hna ⟨k, hk, hkb⟩
    exact hbetween z hbz hza

/-- **The key lemma.** The tail relation is exactly adjacency in the lex order:
the quotient `P(ω)/∼` collapses precisely the jumps, and nothing else.

Consequently the quotient is densely ordered, which is what Cantor's
back-and-forth argument needs. -/
theorem tailPair_iff_isAdjacent (a b : Set ℕ) : TailPair a b ↔ IsAdjacent b a :=
  ⟨isAdjacent_of_tailPair, tailPair_of_isAdjacent⟩

/-- Distinct tail-equivalent points are adjacent, in one order or the other. -/
theorem isAdjacent_of_tailEqv {a b : Set ℕ} (h : TailEqv a b) (hne : a ≠ b) :
    IsAdjacent b a ∨ IsAdjacent a b := by
  rcases h with (rfl | h | h)
  · exact absurd rfl hne
  · exact Or.inl (isAdjacent_of_tailPair h)
  · exact Or.inr (isAdjacent_of_tailPair h)

/-! ### The non-strict order -/

/-- `x ≤ y` in the lex order. -/
def LexLe (x y : Set ℕ) : Prop := ¬ (y <ₗ x)

@[inherit_doc] scoped infix:50 " ≤ₗ " => LexLe

theorem lexLe_iff (x y : Set ℕ) : x ≤ₗ y ↔ x = y ∨ x <ₗ y := by
  constructor
  · intro h
    rcases lexLt_trichotomy x y with hlt | heq | hgt
    · exact Or.inr hlt
    · exact Or.inl heq
    · exact absurd hgt h
  · rintro (rfl | h)
    · exact lexLt_irrefl x
    · exact lexLt_asymm h

theorem lexLe_refl (x : Set ℕ) : x ≤ₗ x := lexLt_irrefl x

theorem lexLe_of_lexLt {x y : Set ℕ} (h : x <ₗ y) : x ≤ₗ y := lexLt_asymm h

theorem lexLe_trans {x y z : Set ℕ} (hxy : x ≤ₗ y) (hyz : y ≤ₗ z) : x ≤ₗ z := by
  rw [lexLe_iff] at hxy hyz ⊢
  rcases hxy with rfl | hxy
  · exact hyz
  rcases hyz with rfl | hyz
  · exact Or.inr hxy
  · exact Or.inr (lexLt_trans hxy hyz)

/-- `∅` is the least element: it is the point `0`. -/
theorem empty_lexLe (x : Set ℕ) : (∅ : Set ℕ) ≤ₗ x := by
  rintro ⟨n, -, -, hmem⟩
  exact hmem

/-- `univ` is the greatest element: it is the point `∞`, which is `recip ∅`. -/
theorem lexLe_univ (x : Set ℕ) : x ≤ₗ (univ : Set ℕ) := by
  rintro ⟨n, -, hnot, -⟩
  exact hnot (mem_univ n)

theorem lexLt_univ_of_ne {x : Set ℕ} (h : x ≠ univ) : x <ₗ univ := by
  rcases lexLt_trichotomy x univ with h1 | h1 | h1
  · exact h1
  · exact absurd h1 h
  · exact absurd h1 (lexLe_univ x)

/-! ### This is Mathlib's lexicographic order

Recorded so the development is on the record as using the standard order rather
than a bespoke one — the first thing a reader should be able to check. Mathlib's
instance fires on `Lex (ℕ → Prop)` but not on `Lex (Set ℕ)`, since instance
search will not unfold `Set`, which is why the order is carried here as a bare
relation instead of an instance. -/

/-- **The lex order here is Mathlib's `Pi.Lex` order.** In `Prop`, `p < q` means
`¬p ∧ q`, which is exactly "the branch point is absent from `x` and present in
`y`". -/
theorem lexLt_iff_piLex (x y : Set ℕ) :
    (toLex (fun n => n ∈ x) < toLex (fun n => n ∈ y)) ↔ (x <ₗ y) := by
  constructor
  · rintro ⟨n, hagree, hlt⟩
    have hnx : ¬ (toLex (fun n => n ∈ x) n) := fun hc => (lt_iff_le_not_ge.1 hlt).2 (fun _ => hc)
    have hny : toLex (fun n => n ∈ y) n := by
      by_contra hc
      exact (lt_iff_le_not_ge.1 hlt).2 (fun h => absurd h hc)
    exact ⟨n, fun k hk => iff_of_eq (hagree k hk), hnx, hny⟩
  · rintro ⟨n, hagree, hnx, hny⟩
    exact ⟨n, fun k hk => propext (hagree k hk),
      lt_iff_le_not_ge.2 ⟨fun h => absurd h hnx, fun h => hnx (h hny)⟩⟩

/-! ### Complement reverses the order

The fact underlying the mirrored sign convention: negating by complementing every
bit turns the lex order upside down. With a mirrored negative branch this is what
makes same-sign comparison forward lex on *both* sides, with no reversal case. -/

/-- **Complement is order-reversing for the lex order.** -/
theorem compl_lexLt_compl {x y : Set ℕ} : xᶜ <ₗ yᶜ ↔ y <ₗ x := by
  constructor
  · rintro ⟨n, hagree, hnx, hny⟩
    refine ⟨n, fun k hk => ?_, ?_, ?_⟩
    · have := hagree k hk
      simp only [Set.mem_compl_iff] at this
      exact (not_iff_not.1 this).symm
    · exact fun hc => hny hc
    · exact not_not.1 hnx
  · rintro ⟨n, hagree, hny, hnx⟩
    refine ⟨n, fun k hk => ?_, ?_, ?_⟩
    · simp only [Set.mem_compl_iff]
      exact not_iff_not.2 (hagree k hk).symm
    · exact fun hc => hc hnx
    · exact hny

/-- Restated: complement is an order isomorphism onto the reversed order. -/
theorem lexLt_compl_iff {x y : Set ℕ} : x <ₗ y ↔ yᶜ <ₗ xᶜ := by
  rw [compl_lexLt_compl]

end SternBrocot
