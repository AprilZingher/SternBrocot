/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Signed
import SternBrocot.Order

/-!
# The signed order, and the full quotient

`none ∈ x` marks `x` as negative, and the negative branch stores the complement
of the magnitude's path. Because complement reverses the lex order
(`compl_lexLt_compl`), same-sign comparison is **forward lex on both sides**, so
the order needs only two cases:

* a negative point is below a positive one;
* points of the same sign compare by their stored bits, forward.

There is no reversed negative branch. That is the point of the mirrored
convention, and it is what makes `slexLt_neg` — negation is order-reversing —
fall out of `compl_lexLt_compl` uniformly rather than by case analysis.

## `-0 = 0` is an adjacency, not a postulate

`neg_ne_self` says no Boolean mask has a fixed point, so `∅` and `univ` — that
is `+0` and `-0` — are distinct points. In the signed order they are the largest
negative and the smallest positive, with **nothing strictly between**
(`nothing_between_zeros`).

So the full quotient identifies exactly the *adjacent* pairs: tail pairs inside
each sign (`tailPair_iff_isAdjacent`), and `(univ, ∅)` across the sign boundary.
One rule, no special case. Note `±∞` are the endpoints of the order, with
everything between them, so they are correctly left distinct.

What makes this safe is that neither `∅` nor `univ` lies in a tail pair
(`not_tailPair_empty_left` and friends), so the new pair cannot chain with an old
one and classes stay at size at most two.

## Main results

* `SternBrocot.slexLt_trichotomy` — the signed order is a strict linear order.
* `SternBrocot.slexLt_neg` — negation is order-reversing.
* `SternBrocot.lift_slexLt_iff` — the positive half is an order-embedded copy of
  `(P(ω), <ₗ)`, so the unsigned development transfers unchanged.
* `SternBrocot.nothing_between_zeros` — `-0` and `+0` are adjacent.
* `SternBrocot.seqv_equivalence` — the full quotient is an equivalence relation.
-/

open Set
open scoped symmDiff

namespace SternBrocot

/-! ### The signed order -/

/-- The signed lex order: negatives below positives, and same-sign points by
forward lex on their stored bits. The mirrored convention makes the negative
branch forward too, so there are only two cases. -/
def SLexLt (x y : Signed) : Prop :=
  (none ∈ x ∧ none ∉ y) ∨ ((none ∈ x ↔ none ∈ y) ∧ finPart x <ₗ finPart y)

@[inherit_doc] scoped infix:50 " <ₛ " => SLexLt

theorem slexLt_irrefl (x : Signed) : ¬ (x <ₛ x) := by
  rintro (⟨h1, h2⟩ | ⟨-, h⟩)
  · exact h2 h1
  · exact lexLt_irrefl _ h

theorem slexLt_trans {x y z : Signed} (hxy : x <ₛ y) (hyz : y <ₛ z) : x <ₛ z := by
  rcases hxy with ⟨hx, hy⟩ | ⟨hs, hf⟩ <;> rcases hyz with ⟨hy', hz⟩ | ⟨hs', hf'⟩
  · exact absurd hy' hy
  · exact Or.inl ⟨hx, fun hc => hy (hs'.2 hc)⟩
  · exact Or.inl ⟨hs.2 hy', hz⟩
  · exact Or.inr ⟨hs.trans hs', lexLt_trans hf hf'⟩

theorem slexLt_asymm {x y : Signed} (h : x <ₛ y) : ¬ (y <ₛ x) :=
  fun h' => slexLt_irrefl x (slexLt_trans h h')

theorem slexLt_trichotomy (x y : Signed) : x <ₛ y ∨ x = y ∨ y <ₛ x := by
  by_cases hx : none ∈ x <;> by_cases hy : none ∈ y
  · rcases lexLt_trichotomy (finPart x) (finPart y) with h | h | h
    · exact Or.inl (Or.inr ⟨by simp [hx, hy], h⟩)
    · exact Or.inr (Or.inl (signed_ext h (by simp [hx, hy])))
    · exact Or.inr (Or.inr (Or.inr ⟨by simp [hx, hy], h⟩))
  · exact Or.inl (Or.inl ⟨hx, hy⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hy, hx⟩))
  · rcases lexLt_trichotomy (finPart x) (finPart y) with h | h | h
    · exact Or.inl (Or.inr ⟨by simp [hx, hy], h⟩)
    · exact Or.inr (Or.inl (signed_ext h (by simp [hx, hy])))
    · exact Or.inr (Or.inr (Or.inr ⟨by simp [hx, hy], h⟩))

/-! ### The two operations, ordered -/

/-- **Negation reverses the order**, uniformly: complement flips the sign and
mirrors the finite bits, and mirroring reverses lex (`compl_lexLt_compl`). -/
theorem slexLt_neg {x y : Signed} (h : x <ₛ y) : neg y <ₛ neg x := by
  rcases h with ⟨hx, hy⟩ | ⟨hs, hf⟩
  · -- `x` negative, `y` positive: the images swap sides
    exact Or.inl ⟨by simpa using hy, by simpa using hx⟩
  · -- same sign: both images flip sign together, and the bits mirror
    refine Or.inr ⟨?_, ?_⟩
    · simp only [none_mem_neg]
      exact not_congr hs.symm
    · rw [finPart_neg, finPart_neg, compl_lexLt_compl]
      exact hf

/-- The positive half is an order-embedded copy of `(P(ω), <ₗ)`, so everything
proved about the unsigned order transfers verbatim — and the naturals keep the
form they have in `Basic.lean`. -/
theorem lift_slexLt_iff (y z : Set ℕ) : lift y <ₛ lift z ↔ y <ₗ z := by
  constructor
  · rintro (⟨hc, -⟩ | ⟨-, hf⟩)
    · exact absurd hc (none_notMem_lift y)
    · rwa [finPart_lift, finPart_lift] at hf
  · intro h
    refine Or.inr ⟨?_, ?_⟩
    · simp
    · rwa [finPart_lift, finPart_lift]

/-! ### `+0` and `-0` are adjacent -/

/-- `-0 = univ` sits immediately below `+0 = ∅`. -/
theorem univ_slexLt_empty : (univ : Signed) <ₛ (∅ : Signed) :=
  Or.inl ⟨mem_univ _, by simp⟩

/-- **Nothing lies strictly between `-0` and `+0`.** The zero identification
collapses an adjacent pair, exactly as the tail rule does — so the quotient
identifies adjacencies and nothing else. -/
theorem nothing_between_zeros (z : Signed) :
    ¬ ((univ : Signed) <ₛ z ∧ z <ₛ (∅ : Signed)) := by
  rintro ⟨h1, h2⟩
  by_cases hz : none ∈ z
  · -- `z` negative: `-0 < z` forces `univ <ₗ finPart z`, but `univ` is the top
    rcases h1 with ⟨-, hc⟩ | ⟨-, hf⟩
    · exact hc hz
    · rw [finPart_univ] at hf
      exact lexLe_univ _ hf
  · -- `z` positive: `z < +0` forces `finPart z <ₗ ∅`, but `∅` is the bottom
    rcases h2 with ⟨hc, -⟩ | ⟨-, hf⟩
    · exact hz hc
    · rw [finPart_empty] at hf
      exact empty_lexLe _ hf

/-! ### The full quotient: adjacencies, uniformly -/

theorem not_tailPair_empty_right {y : Set ℕ} : ¬ TailPair y (∅ : Set ℕ) := by
  rintro ⟨n, h⟩
  exact h.right_tail (n + 1) (Nat.lt_succ_self n)

theorem not_tailPair_empty_left {y : Set ℕ} : ¬ TailPair (∅ : Set ℕ) y := by
  rintro ⟨n, h⟩
  exact h.mem_left

/-- `univ` is in no tail pair either: it is unbounded, so never the bounded side,
and it omits nothing, so never the cofinite side. -/
theorem not_tailPair_univ_left {y : Set ℕ} : ¬ TailPair (univ : Set ℕ) y := by
  rintro ⟨n, h⟩
  exact h.left_top (n + 1) (Nat.lt_succ_self n) (mem_univ _)

theorem not_tailPair_univ_right {y : Set ℕ} : ¬ TailPair y (univ : Set ℕ) := by
  rintro ⟨n, h⟩
  exact h.notMem_right (mem_univ n)

/-- A point whose finite part is `∅` is alone in its tail class. -/
theorem not_stailPair_of_finPart_empty {a b : Signed} (h : finPart a = ∅) :
    ¬ STailPair a b ∧ ¬ STailPair b a := by
  refine ⟨?_, ?_⟩
  · rintro ⟨-, hf⟩; rw [h] at hf; exact not_tailPair_empty_left hf
  · rintro ⟨-, hf⟩; rw [h] at hf; exact not_tailPair_empty_right hf

/-- A point whose finite part is `univ` is alone in its tail class. -/
theorem not_stailPair_of_finPart_univ {a b : Signed} (h : finPart a = univ) :
    ¬ STailPair a b ∧ ¬ STailPair b a := by
  refine ⟨?_, ?_⟩
  · rintro ⟨-, hf⟩; rw [h] at hf; exact not_tailPair_univ_left hf
  · rintro ⟨-, hf⟩; rw [h] at hf; exact not_tailPair_univ_right hf

theorem stailEqv_zero {a : Signed} (h : STailEqv a ∅) : a = ∅ := by
  rcases h with h | h | h
  · exact h
  · exact absurd h (not_stailPair_of_finPart_empty finPart_empty).2
  · exact absurd h (not_stailPair_of_finPart_empty finPart_empty).1

theorem stailEqv_negZero {a : Signed} (h : STailEqv a univ) : a = univ := by
  rcases h with h | h | h
  · exact h
  · exact absurd h (not_stailPair_of_finPart_univ finPart_univ).2
  · exact absurd h (not_stailPair_of_finPart_univ finPart_univ).1

/-- The full equivalence on `P(ω + 1)`: the tail rule, together with the zero
adjacency `univ ∼ ∅`, i.e. `-0 = 0`. -/
def SEqv (a b : Signed) : Prop := STailEqv a b ∨ ZeroDegen a b

theorem SEqv.refl (a : Signed) : SEqv a a := Or.inl (STailEqv.refl a)

theorem SEqv.symm {a b : Signed} : SEqv a b → SEqv b a := by
  rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr ⟨h2, h1⟩)
  · exact Or.inr (Or.inl ⟨h2, h1⟩)

theorem empty_ne_univ_signed : (∅ : Signed) ≠ univ := by
  intro h
  have : (none : Option ℕ) ∈ (∅ : Signed) := h ▸ mem_univ _
  exact this

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
    · exact absurd hc.symm empty_ne_univ_signed
    · exact Or.inl (STailEqv.refl _)
  · rcases hbc with hbc | ⟨-, rfl⟩ | ⟨hc, -⟩
    · rw [stailEqv_zero hbc.symm]
      exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inl (STailEqv.refl _)
    · exact absurd hc empty_ne_univ_signed

/-- **The full quotient is an equivalence relation.** The tail rule and the zero
adjacency compose without interference: `∅` and `univ` lie in no tail pair, so
the two relations never chain. -/
theorem seqv_equivalence : Equivalence SEqv :=
  ⟨SEqv.refl, SEqv.symm, SEqv.trans⟩

end SternBrocot
