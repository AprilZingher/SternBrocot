/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Signed
import SternBrocot.Order

/-!
# The signed order, and the full quotient

The order on `P(ω + 1)` is *sign first, then lex, reversed on the negative side*
— `none ∈ x` marks `x` as negative. This is what makes `ℝ` rather than `ℝ≥0` the
target of `Φ`.

## The zero degeneracy is an adjacency

`neg_ne_self` says no Boolean mask has a fixed point, so `∅` and `{ω}` are
distinct points denoting `+0` and `-0`. In the signed order they sit next to each
other with **nothing strictly between** (`nothing_between_zeros`) — structurally
the same phenomenon as a tail pair. So the full quotient

  `SEqv = STailEqv ∪ ZeroDegen`

collapses adjacencies and nothing else, and `SEqv` is already an equivalence
relation with classes of size at most two: `∅` and `{ω}` belong to no tail pair
(`not_stailPair_empty`), so the two relations never interact.

## Main results

* `SternBrocot.slexLt_trichotomy` — the signed order is a strict linear order.
* `SternBrocot.slexLt_neg` — negation is order-**reversing**, on the nose.
* `SternBrocot.lift_slexLt_iff` — the positive half is an order-embedded copy of
  `(P(ω), <ₗ)`, so the unsigned development transfers unchanged.
* `SternBrocot.nothing_between_zeros` — `+0` and `-0` are adjacent.
* `SternBrocot.seqv_equivalence` — the full quotient is an equivalence relation.
-/

open Set
open scoped symmDiff

namespace SternBrocot

/-! ### The signed order -/

/-- The signed lex order: negatives below positives; positives compared by the
lex order on their finite parts; negatives compared by the **reverse** of it,
since `-a < -b` exactly when `b < a`. -/
def SLexLt (x y : Signed) : Prop :=
  (none ∈ x ∧ none ∉ y) ∨
  (none ∉ x ∧ none ∉ y ∧ finPart x <ₗ finPart y) ∨
  (none ∈ x ∧ none ∈ y ∧ finPart y <ₗ finPart x)

@[inherit_doc] scoped infix:50 " <ₛ " => SLexLt

theorem slexLt_irrefl (x : Signed) : ¬ (x <ₛ x) := by
  rintro (⟨h1, h2⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩)
  · exact h2 h1
  · exact lexLt_irrefl _ h
  · exact lexLt_irrefl _ h

theorem slexLt_trans {x y z : Signed} (hxy : x <ₛ y) (hyz : y <ₛ z) : x <ₛ z := by
  rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy, hf⟩ | ⟨hx, hy, hf⟩ <;>
    rcases hyz with ⟨hy', hz⟩ | ⟨hy', hz, hf'⟩ | ⟨hy', hz, hf'⟩
  · exact absurd hy' hy
  · exact Or.inl ⟨hx, hz⟩
  · exact absurd hy' hy
  · exact absurd hy' hy
  · exact Or.inr (Or.inl ⟨hx, hz, lexLt_trans hf hf'⟩)
  · exact absurd hy' hy
  · exact Or.inl ⟨hx, hz⟩
  · exact absurd hy hy'
  · exact Or.inr (Or.inr ⟨hx, hz, lexLt_trans hf' hf⟩)

theorem slexLt_asymm {x y : Signed} (h : x <ₛ y) : ¬ (y <ₛ x) :=
  fun h' => slexLt_irrefl x (slexLt_trans h h')

theorem slexLt_trichotomy (x y : Signed) : x <ₛ y ∨ x = y ∨ y <ₛ x := by
  by_cases hx : none ∈ x <;> by_cases hy : none ∈ y
  · -- both negative: compare finite parts in reverse
    rcases lexLt_trichotomy (finPart x) (finPart y) with h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hy, hx, h⟩)))
    · exact Or.inr (Or.inl (signed_ext h (by simp [hx, hy])))
    · exact Or.inl (Or.inr (Or.inr ⟨hx, hy, h⟩))
  · exact Or.inl (Or.inl ⟨hx, hy⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hy, hx⟩))
  · -- both positive: compare finite parts directly
    rcases lexLt_trichotomy (finPart x) (finPart y) with h | h | h
    · exact Or.inl (Or.inr (Or.inl ⟨hx, hy, h⟩))
    · exact Or.inr (Or.inl (signed_ext h (by simp [hx, hy])))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hy, hx, h⟩)))

/-! ### The two operations, ordered -/

/-- **Negation reverses the order.** -/
theorem slexLt_neg {x y : Signed} (h : x <ₛ y) : neg y <ₛ neg x := by
  have hn : ∀ z : Signed, (none ∈ neg z) ↔ none ∉ z := none_mem_neg
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy, hf⟩ | ⟨hx, hy, hf⟩
  · -- `x` negative, `y` positive: the images swap sides
    exact Or.inl ⟨(hn y).2 hy, fun hc => (hn x).1 hc hx⟩
  · -- both positive: images are both negative, order reverses
    refine Or.inr (Or.inr ⟨(hn y).2 hy, (hn x).2 hx, ?_⟩)
    rw [finPart_neg, finPart_neg]
    exact hf
  · -- both negative: images are both positive, order reverses back
    refine Or.inr (Or.inl ⟨fun hc => (hn y).1 hc hy, fun hc => (hn x).1 hc hx, ?_⟩)
    rw [finPart_neg, finPart_neg]
    exact hf

/-- The positive half is an order-embedded copy of `(P(ω), <ₗ)`, so everything
proved about the unsigned order transfers verbatim. -/
theorem lift_slexLt_iff (y z : Set ℕ) : lift y <ₛ lift z ↔ y <ₗ z := by
  constructor
  · rintro (⟨hc, -⟩ | ⟨-, -, hf⟩ | ⟨hc, -, -⟩)
    · exact absurd hc (none_notMem_lift y)
    · rwa [finPart_lift, finPart_lift] at hf
    · exact absurd hc (none_notMem_lift y)
  · intro h
    refine Or.inr (Or.inl ⟨none_notMem_lift y, none_notMem_lift z, ?_⟩)
    rwa [finPart_lift, finPart_lift]

/-! ### `+0` and `-0` are adjacent -/

@[simp] theorem finPart_empty : finPart (∅ : Signed) = ∅ := by
  ext n; simp [finPart]

@[simp] theorem finPart_singleton_none : finPart ({none} : Signed) = ∅ := by
  ext n; simp [finPart]

theorem singleton_none_slexLt_empty : ({none} : Signed) <ₛ (∅ : Signed) :=
  Or.inl ⟨rfl, by simp⟩

/-- **Nothing lies strictly between `-0` and `+0`.** The zero degeneracy collapses
an adjacent pair, exactly as the tail rule does — which is why adjoining it keeps
the quotient densely ordered rather than tearing a hole in it. -/
theorem nothing_between_zeros (z : Signed) :
    ¬ (({none} : Signed) <ₛ z ∧ z <ₛ (∅ : Signed)) := by
  have hbot : ∀ y : Set ℕ, ¬ (y <ₗ (∅ : Set ℕ)) := by
    rintro y ⟨n, -, -, hmem⟩
    exact hmem
  rintro ⟨h1, h2⟩
  by_cases hz : none ∈ z
  · -- `z` negative: `-0 < z` forces `finPart z <ₗ ∅`, and `∅` is the bottom
    rcases h1 with ⟨-, hc⟩ | ⟨hc, -, -⟩ | ⟨-, -, hf⟩
    · exact hc hz
    · exact hc rfl
    · rw [finPart_singleton_none] at hf
      exact hbot _ hf
  · -- `z` positive: `z < +0` forces the same
    rcases h2 with ⟨hc, -⟩ | ⟨-, -, hf⟩ | ⟨hc, -, -⟩
    · exact hz hc
    · rw [finPart_empty] at hf
      exact hbot _ hf
    · exact hz hc

/-! ### The full quotient: tail rule plus `-0 = 0` -/

theorem not_tailPair_empty_right {y : Set ℕ} : ¬ TailPair y (∅ : Set ℕ) := by
  rintro ⟨n, h⟩
  exact h.right_tail (n + 1) (Nat.lt_succ_self n)

theorem not_tailPair_empty_left {y : Set ℕ} : ¬ TailPair (∅ : Set ℕ) y := by
  rintro ⟨n, h⟩
  exact h.mem_left

/-- `∅` and `{ω}` belong to no tail pair, so the tail relation and the zero
degeneracy never interact. -/
theorem not_stailPair_of_finPart_empty {a b : Signed} (h : finPart a = ∅) :
    ¬ STailPair a b ∧ ¬ STailPair b a := by
  constructor
  · rintro ⟨-, hf⟩
    rw [h] at hf
    exact not_tailPair_empty_left hf
  · rintro ⟨-, hf⟩
    rw [h] at hf
    exact not_tailPair_empty_right hf

/-- A point whose finite part is empty is alone in its tail class. Applied to
`∅` and `{ω}`, this is what keeps the tail rule and the zero degeneracy from
interacting. -/
theorem eq_of_stailEqv_of_finPart_empty {a b : Signed} (hb : finPart b = ∅)
    (h : STailEqv a b) : a = b := by
  rcases h with h | h | h
  · exact h
  · exact absurd h (not_stailPair_of_finPart_empty hb).2
  · exact absurd h (not_stailPair_of_finPart_empty hb).1

theorem stailEqv_zero {a : Signed} (h : STailEqv a ∅) : a = ∅ :=
  eq_of_stailEqv_of_finPart_empty finPart_empty h

theorem stailEqv_negZero {a : Signed} (h : STailEqv a {none}) : a = {none} :=
  eq_of_stailEqv_of_finPart_empty finPart_singleton_none h

/-- The full equivalence on `P(ω + 1)`: the tail rule, together with `-0 = 0`. -/
def SEqv (a b : Signed) : Prop := STailEqv a b ∨ ZeroDegen a b

theorem SEqv.refl (a : Signed) : SEqv a a := Or.inl (STailEqv.refl a)

theorem SEqv.symm {a b : Signed} : SEqv a b → SEqv b a := by
  rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr ⟨h2, h1⟩)
  · exact Or.inr (Or.inl ⟨h2, h1⟩)

theorem SEqv.trans {a b c : Signed} : SEqv a b → SEqv b c → SEqv a c := by
  rintro (hab | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) hbc
  · rcases hbc with hbc | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (hab.trans hbc)
    · rw [stailEqv_zero hab]
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rw [stailEqv_negZero hab]
      exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rcases hbc with hbc | ⟨hc, -⟩ | ⟨-, rfl⟩
    · rw [stailEqv_negZero hbc.symm]
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact absurd hc.symm (by simp)
    · exact Or.inl (STailEqv.refl _)
  · rcases hbc with hbc | ⟨-, rfl⟩ | ⟨hc, -⟩
    · rw [stailEqv_zero hbc.symm]
      exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inl (STailEqv.refl _)
    · exact absurd hc (by simp)

/-- **The full quotient is an equivalence relation.** The tail rule and `-0 = 0`
compose without interference. -/
theorem seqv_equivalence : Equivalence SEqv :=
  ⟨SEqv.refl, SEqv.symm, SEqv.trans⟩

end SternBrocot
