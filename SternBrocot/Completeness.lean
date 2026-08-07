/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Order

/-!
# Completeness of the lex order, and density of the quotient

Two steps of the `Φ` programme.

**Completeness upstairs.** Every subset of `P(ω)` has a least upper bound in the
lex order, computed *bitwise*: bit `n` of the supremum is set exactly when some
member of `S` agrees with the supremum on all bits below `n` and carries bit `n`.
The greedy definition is self-referential, so it is built up along a prefix
recursion (`supPrefix`) and then read off (`lexSup`).

Note that no nonemptiness hypothesis is needed: `∅` is the least element of the
lex order (it is `0`) and `univ` is the greatest (it is `∞`), so the order is
bounded and *unconditionally* complete.

**Density downstairs.** The quotient `P(ω)/∼` is densely ordered. This is
immediate from the key lemma: a gap with nothing strictly inside it is exactly an
adjacent pair, which is exactly a tail pair, which the quotient collapses.

## Main results

* `SternBrocot.isLexLUB_lexSup` — every `S : Set (Set ℕ)` has `lexSup S` as its
  least upper bound.
* `SternBrocot.exists_between_of_not_tailEqv` — density of the quotient.

The non-strict order `≤ₗ` and the endpoint facts (`empty_lexLe`, `lexLe_univ`)
live in `Order.lean`, with the rest of the order.
-/

open Set
open scoped symmDiff

namespace SternBrocot

/-! ### The bitwise supremum

`supPrefix S n` collects the bits below `n` that the supremum carries, decided
greedily from the bottom up: bit `n` goes in exactly when some member of `S`
matches everything already decided and carries bit `n`. -/

/-- The bits of `lexSup S` below `n`, chosen greedily. -/
def supPrefix (S : Set (Set ℕ)) : ℕ → Set ℕ
  | 0 => ∅
  | n + 1 =>
      supPrefix S n ∪
        {m | m = n ∧ ∃ x ∈ S, (∀ k < n, (k ∈ x ↔ k ∈ supPrefix S n)) ∧ n ∈ x}

/-- The least upper bound of `S` in the lex order. -/
def lexSup (S : Set (Set ℕ)) : Set ℕ := {n | n ∈ supPrefix S (n + 1)}

theorem supPrefix_subset (S : Set (Set ℕ)) (n : ℕ) : supPrefix S n ⊆ Iio n := by
  induction n with
  | zero => intro k hk; exact absurd hk (by simp [supPrefix])
  | succ n ih =>
    intro k hk
    simp only [supPrefix, Set.mem_union, Set.mem_setOf_eq] at hk
    rcases hk with hk | ⟨rfl, -⟩
    · exact Set.mem_Iio.2 ((Set.mem_Iio.1 (ih hk)).trans (Nat.lt_succ_self n))
    · exact Set.mem_Iio.2 (Nat.lt_succ_self k)

/-- The prefixes are coherent: extending the recursion never revisits a bit that
has already been decided. -/
theorem supPrefix_agree (S : Set (Set ℕ)) {m n : ℕ} (h : m ≤ n) {k : ℕ} (hk : k < m) :
    (k ∈ supPrefix S m ↔ k ∈ supPrefix S n) := by
  induction n, h using Nat.le_induction with
  | base => exact Iff.rfl
  | succ n hmn ih =>
    rw [ih]
    simp only [supPrefix, Set.mem_union, Set.mem_setOf_eq]
    refine ⟨Or.inl, ?_⟩
    rintro (h | ⟨heq, -⟩)
    · exact h
    · exact absurd heq (by omega)

/-- Below `n`, the supremum is exactly the prefix — the bridge between the
recursion and the set it defines. -/
theorem mem_lexSup_iff_of_lt (S : Set (Set ℕ)) {k n : ℕ} (hk : k < n) :
    (k ∈ lexSup S ↔ k ∈ supPrefix S n) :=
  supPrefix_agree S (Nat.succ_le_of_lt hk) (Nat.lt_succ_self k)

/-- **The greedy characterisation.** Bit `n` of the supremum is set exactly when
some member of `S` agrees with the supremum below `n` and carries bit `n`. -/
theorem mem_lexSup_iff (S : Set (Set ℕ)) (n : ℕ) :
    n ∈ lexSup S ↔ ∃ x ∈ S, (∀ k < n, (k ∈ x ↔ k ∈ lexSup S)) ∧ n ∈ x := by
  have h1 : n ∈ lexSup S ↔ n ∈ supPrefix S (n + 1) := Iff.rfl
  rw [h1]
  simp only [supPrefix, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (hmem | ⟨-, x, hxS, hagree, hnx⟩)
    · exact absurd (Set.mem_Iio.1 (supPrefix_subset S n hmem)) (lt_irrefl n)
    · exact ⟨x, hxS, fun k hk => (hagree k hk).trans (mem_lexSup_iff_of_lt S hk).symm, hnx⟩
  · rintro ⟨x, hxS, hagree, hnx⟩
    exact Or.inr ⟨trivial, x, hxS, fun k hk => (hagree k hk).trans (mem_lexSup_iff_of_lt S hk), hnx⟩

/-! ### Completeness -/

/-- `u` is a least upper bound of `S` in the lex order. -/
def IsLexLUB (S : Set (Set ℕ)) (u : Set ℕ) : Prop :=
  (∀ x ∈ S, x ≤ₗ u) ∧ ∀ v, (∀ x ∈ S, x ≤ₗ v) → u ≤ₗ v

/-- `lexSup S` is an upper bound: if some `x ∈ S` exceeded it, the greedy rule
would have set the bit where they first differ. -/
theorem lexSup_upperBound (S : Set (Set ℕ)) : ∀ x ∈ S, x ≤ₗ lexSup S := by
  rintro x hxS ⟨n, hagree, hnot, hnx⟩
  refine hnot ((mem_lexSup_iff S n).2 ⟨x, hxS, ?_, hnx⟩)
  exact fun k hk => (hagree k hk).symm

/-- `lexSup S` is the *least* upper bound: any point strictly below it is already
overtaken by some member of `S`, by the greedy rule. -/
theorem lexSup_least (S : Set (Set ℕ)) (v : Set ℕ) (hv : ∀ x ∈ S, x ≤ₗ v) :
    lexSup S ≤ₗ v := by
  rintro ⟨n, hagree, hnv, hns⟩
  obtain ⟨x, hxS, hxagree, hnx⟩ := (mem_lexSup_iff S n).1 hns
  refine hv x hxS ⟨n, fun k hk => ?_, hnv, hnx⟩
  exact (hagree k hk).trans (hxagree k hk).symm

/-- **Completeness upstairs.** Every subset of `P(ω)` has a least upper bound in
the lex order, computed bitwise. No nonemptiness hypothesis is needed: the order
has endpoints `∅ = 0` and `univ = ∞`. -/
theorem isLexLUB_lexSup (S : Set (Set ℕ)) : IsLexLUB S (lexSup S) :=
  ⟨lexSup_upperBound S, lexSup_least S⟩

/-- Least upper bounds are unique, so `lexSup` is *the* supremum. -/
theorem IsLexLUB.unique {S : Set (Set ℕ)} {u v : Set ℕ}
    (hu : IsLexLUB S u) (hv : IsLexLUB S v) : u = v := by
  rcases (lexLe_iff u v).1 (hu.2 v hv.1) with h | h
  · exact h
  · exact absurd h (hv.2 u hu.1)

theorem eq_lexSup_of_isLexLUB {S : Set (Set ℕ)} {u : Set ℕ} (hu : IsLexLUB S u) :
    u = lexSup S :=
  hu.unique (isLexLUB_lexSup S)

/-! ### Density of the quotient

The tail relation collapses exactly the jumps, so what is left is dense. -/

/-- **The quotient is densely ordered.** If `x < y` and they are not identified
by the tail relation, something lies strictly between.

This is the contrapositive of the key lemma: a gap with empty interior is an
adjacent pair, and adjacent pairs are precisely tail pairs. -/
theorem exists_between_of_not_tailEqv {x y : Set ℕ} (hlt : x <ₗ y) (h : ¬ TailEqv x y) :
    ∃ z, x <ₗ z ∧ z <ₗ y := by
  by_contra hc
  refine h (Or.inr (Or.inr (tailPair_of_isAdjacent ⟨hlt, ?_⟩)))
  intro z hxz hzy
  exact hc ⟨z, hxz, hzy⟩

/-- Contrapositive form: tail-inequivalent points always have a point between
them, so the quotient has no jumps. -/
theorem tailEqv_of_no_between {x y : Set ℕ} (hlt : x <ₗ y)
    (h : ¬ ∃ z, x <ₗ z ∧ z <ₗ y) : TailEqv x y := by
  by_contra hc
  exact h (exists_between_of_not_tailEqv hlt hc)

end SternBrocot
