/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Set.SymmDiff
import Mathlib.Data.Set.Image
import Mathlib.Order.Interval.Set.Basic

/-!
# Stern–Brocot reals as subsets of `ω`

The carrier is `P(ω) = Set ℕ`. A set `x ⊆ ω` is read as the bit stream
`b n = (n ∈ x)`, which is the path down the Stern–Brocot tree: bit `n` records
the `n`-th move.

The two tree moves, in von Neumann notation (`y ∪ {y} = y + 1`):

* `L x = {y ∪ {y} : y ∈ x}` — prepend a `0` bit;
* `S x = {y ∪ {y} : y ∈ x} ∪ {0}` — prepend a `1` bit (the usual successor on `ω`).

Reciprocal is complement, which swaps the two moves (`recip_L`, `recip_S`); this
is the identity `J R J = L` in `PGL₂`.

## Main definitions

* `SternBrocot.L`, `SternBrocot.S` — the two moves.
* `SternBrocot.IsTailPairAt` / `SternBrocot.TailPair` — the tail relation
  `s ⌢ 1 ⌢ 0^∞ ∼ s ⌢ 0 ⌢ 1^∞`, i.e. `s R L^∞ = s L R^∞`, the unique redundancy
  in the encoding.

## Main results

* `SternBrocot.eq_empty_or_univ_of_tail_trivial` — if every up-set `Ici n` is
  either disjoint from `m` or contained in `m`, then `m = ∅` or `m = univ`.
* `SternBrocot.symmDiff_preservesTail_iff` — **the rigidity theorem**: the
  Boolean translation `x ↦ x ∆ m` respects the tail relation iff `m = ∅` or
  `m = univ`, i.e. iff it is the identity or reciprocal.

The rigidity theorem is the no-go statement explaining why reciprocal and
negation are the only operations this encoding makes cheap: the Boolean
structure supports exactly the `PGL₂` torsion elements and nothing else, so
addition was never going to be a Boolean operation.
-/

open Set
open scoped symmDiff

namespace SternBrocot

/-! ### The two moves -/

/-- `L x = {y ∪ {y} : y ∈ x}`: a step left in the Stern–Brocot tree.
As a bit stream this prepends a `0`. -/
def L (x : Set ℕ) : Set ℕ := Nat.succ '' x

/-- `S x = {y ∪ {y} : y ∈ x} ∪ {0}`: a step right, and the usual von Neumann
successor when `x` is a natural number. As a bit stream this prepends a `1`. -/
def S (x : Set ℕ) : Set ℕ := insert 0 (Nat.succ '' x)

/-- Reciprocal is complement: it exchanges left and right moves. -/
def recip (x : Set ℕ) : Set ℕ := xᶜ

@[simp] theorem zero_notMem_L (x : Set ℕ) : 0 ∉ L x := by
  rintro ⟨a, -, ha⟩
  exact Nat.succ_ne_zero a ha

@[simp] theorem succ_mem_L {x : Set ℕ} {n : ℕ} : n + 1 ∈ L x ↔ n ∈ x := by
  constructor
  · rintro ⟨a, ha, h⟩
    rwa [Nat.succ_injective h] at ha
  · exact fun h => ⟨n, h, rfl⟩

@[simp] theorem zero_mem_S (x : Set ℕ) : 0 ∈ S x := mem_insert _ _

@[simp] theorem succ_mem_S {x : Set ℕ} {n : ℕ} : n + 1 ∈ S x ↔ n ∈ x := by
  simp only [S, mem_insert_iff, Nat.succ_ne_zero, false_or]
  exact succ_mem_L

theorem S_eq_insert_L (x : Set ℕ) : S x = insert 0 (L x) := rfl

/-- Reciprocal conjugates the left move into the right move: `J L J = S`. -/
theorem recip_L (x : Set ℕ) : recip (L x) = S (recip x) := by
  ext n
  cases n with
  | zero => simp [recip]
  | succ n => simp [recip]

/-- Reciprocal conjugates the right move into the left move: `J S J = L`. -/
theorem recip_S (x : Set ℕ) : recip (S x) = L (recip x) := by
  ext n
  cases n with
  | zero => simp [recip]
  | succ n => simp [recip]

@[simp] theorem recip_recip (x : Set ℕ) : recip (recip x) = x := compl_compl x

/-! ### The tail relation

The single redundancy in the encoding: a `1` followed by all `0`s denotes the
same point as a `0` followed by all `1`s. In tree language `s R L^∞ = s L R^∞`;
in the user's phrasing, "including `n` is the same as including everything
above `n`". -/

/-- `IsTailPairAt n a b` : `a` and `b` are a tail pair branching at `n`. They
agree strictly below `n`; `a` contains `n` and nothing above it; `b` omits `n`
and contains everything above it. -/
structure IsTailPairAt (n : ℕ) (a b : Set ℕ) : Prop where
  /-- The two sets agree strictly below the branch point. -/
  below : ∀ k < n, (k ∈ a ↔ k ∈ b)
  /-- The left element contains the branch point. -/
  mem_left : n ∈ a
  /-- The left element contains nothing above the branch point. -/
  left_top : ∀ k, n < k → k ∉ a
  /-- The right element omits the branch point. -/
  notMem_right : n ∉ b
  /-- The right element contains everything above the branch point. -/
  right_tail : ∀ k, n < k → k ∈ b

/-- `a` and `b` are a tail pair: `a = s ∪ {n}` and `b = s ∪ (n, ∞)` for some
finite prefix `s ⊆ [0, n)`. -/
def TailPair (a b : Set ℕ) : Prop := ∃ n, IsTailPairAt n a b

/-- The canonical tail pair branching at `n` with empty prefix: `{n}` and
`(n, ∞)`. -/
theorem isTailPairAt_singleton (n : ℕ) : IsTailPairAt n {n} (Ioi n) where
  below := by
    intro k hk
    simp only [mem_singleton_iff, mem_Ioi]
    constructor
    · rintro rfl; exact absurd hk (lt_irrefl _)
    · intro h; exact absurd (hk.trans h) (lt_irrefl _)
  mem_left := rfl
  left_top := by
    intro k hk h
    rw [mem_singleton_iff] at h
    exact absurd h.symm (ne_of_lt hk)
  notMem_right := lt_irrefl n
  right_tail := fun _ hk => hk

/-- The branch point of a tail pair is determined: it is the unique place where
the two sets first differ. -/
theorem IsTailPairAt.eq_of_agree {n n' : ℕ} {a b : Set ℕ}
    (h : IsTailPairAt n' a b) (hbelow : ∀ k < n, (k ∈ a ↔ k ∈ b))
    (hdiff : ¬(n ∈ a ↔ n ∈ b)) : n' = n := by
  rcases lt_trichotomy n' n with hlt | heq | hgt
  · -- `n' < n`: the hypothesis says they agree at `n'`, but a tail pair differs there.
    exact absurd ((hbelow n' hlt).mp h.mem_left) h.notMem_right
  · exact heq
  · -- `n < n'`: the tail pair says they agree at `n`, contradicting `hdiff`.
    exact absurd (h.below n hgt) hdiff

/-! ### Reciprocal respects the tail relation

Complement swaps the two sides of a tail pair — the left element becomes the
right one. This is the `m = univ` half of the rigidity theorem. -/

/-- Complement turns a tail pair into the reversed tail pair at the same branch
point. -/
theorem IsTailPairAt.compl {n : ℕ} {a b : Set ℕ} (h : IsTailPairAt n a b) :
    IsTailPairAt n bᶜ aᶜ where
  below := by
    intro k hk
    simp only [mem_compl_iff]
    exact not_congr (h.below k hk).symm
  mem_left := h.notMem_right
  left_top := fun k hk hmem => hmem (h.right_tail k hk)
  notMem_right := fun hmem => hmem h.mem_left
  right_tail := fun k hk => h.left_top k hk

/-! ### The rigidity theorem -/

/-- Every up-set is either disjoint from `m` or contained in `m`. This is the
condition that `x ↦ x ∆ m` must satisfy to respect the tail relation. -/
def TailTrivial (m : Set ℕ) : Prop := ∀ n : ℕ, m ∩ Ici n = ∅ ∨ Ici n ⊆ m

theorem Ici_zero_eq_univ : Ici (0 : ℕ) = univ := by
  ext n; simp

/-- **The two-sided masks.** A mask whose every up-set is either disjoint from
it or contained in it is trivial: only `∅` and `ω` survive.

Testing at `n = 0` already settles it, since `Ici 0 = ω`; the content of the
rigidity theorem is that `TailTrivial` is *forced*, which is
`tailTrivial_of_preservesTail`. -/
theorem eq_empty_or_univ_of_tail_trivial {m : Set ℕ} (h : TailTrivial m) :
    m = ∅ ∨ m = univ := by
  rcases h 0 with h0 | h0
  · left
    rwa [Ici_zero_eq_univ, inter_univ] at h0
  · right
    rw [Ici_zero_eq_univ] at h0
    exact eq_univ_of_univ_subset h0

/-- The translation `x ↦ x ∆ m` **respects the tail relation**: it sends tail
pairs to tail pairs, possibly with the two sides exchanged (as reciprocal
does). -/
def PreservesTail (m : Set ℕ) : Prop :=
  ∀ a b : Set ℕ, TailPair a b → TailPair (a ∆ m) (b ∆ m) ∨ TailPair (b ∆ m) (a ∆ m)

/-- **Necessity.** If `x ↦ x ∆ m` respects the tail relation then every up-set
is either disjoint from `m` or contained in `m`.

The proof tests the map on the canonical tail pair `({n}, (n, ∞))`. The image
pair still agrees below `n` and still differs at `n`, so its branch point is
again `n`; then requiring the side containing `n` to have an empty tail forces
`m ∩ Ici n = ∅`, and the exchanged case forces `Ici n ⊆ m`. -/
theorem tailTrivial_of_preservesTail {m : Set ℕ} (h : PreservesTail m) :
    TailTrivial m := by
  intro n
  -- The canonical tail pair at `n`.
  have hpair : TailPair ({n} : Set ℕ) (Ioi n) := ⟨n, isTailPairAt_singleton n⟩
  -- Both images agree below `n` ...
  have hbelow : ∀ k < n, (k ∈ ({n} : Set ℕ) ∆ m ↔ k ∈ (Ioi n) ∆ m) := by
    intro k hk
    simp only [Set.mem_symmDiff, mem_singleton_iff, mem_Ioi]
    have h1 : ¬ (k = n) := ne_of_lt hk
    have h2 : ¬ (n < k) := not_lt.2 hk.le
    tauto
  -- ... and differ at `n`.
  have hdiff : ¬(n ∈ ({n} : Set ℕ) ∆ m ↔ n ∈ (Ioi n) ∆ m) := by
    simp only [Set.mem_symmDiff, mem_singleton_iff, mem_Ioi, lt_irrefl]
    by_cases hm : n ∈ m <;> simp [hm]
  rcases h _ _ hpair with ⟨n', hn'⟩ | ⟨n', hn'⟩
  · -- `{n} ∆ m` is the left side: it contains `n` and nothing above.
    left
    have hn'n : n' = n := hn'.eq_of_agree hbelow hdiff
    subst hn'n
    apply eq_empty_of_forall_notMem
    intro k hk
    obtain ⟨hkm, hkn⟩ := hk
    rw [mem_Ici, le_iff_lt_or_eq] at hkn
    rcases hkn with hlt | rfl
    · -- `k > n'` : `k ∉ {n'} ∆ m`, but `k ∈ m` and `k ∉ {n'}` give `k ∈ {n'} ∆ m`.
      refine hn'.left_top k hlt ?_
      rw [Set.mem_symmDiff]
      right
      exact ⟨hkm, by simp [ne_of_gt hlt]⟩
    · -- `k = n'` : `n' ∈ {n'} ∆ m` fails because `n' ∈ {n'}` and `n' ∈ m`.
      have := hn'.mem_left
      rw [Set.mem_symmDiff] at this
      rcases this with ⟨-, hcon⟩ | ⟨-, hcon⟩
      · exact hcon hkm
      · exact hcon rfl
  · -- `Ioi n ∆ m` is the left side: it contains `n` and nothing above.
    right
    have hbelow' : ∀ k < n, (k ∈ (Ioi n) ∆ m ↔ k ∈ ({n} : Set ℕ) ∆ m) :=
      fun k hk => (hbelow k hk).symm
    have hdiff' : ¬(n ∈ (Ioi n) ∆ m ↔ n ∈ ({n} : Set ℕ) ∆ m) :=
      fun hiff => hdiff hiff.symm
    have hn'n : n' = n := hn'.eq_of_agree hbelow' hdiff'
    subst hn'n
    intro k hk
    rw [mem_Ici, le_iff_lt_or_eq] at hk
    rcases hk with hlt | rfl
    · -- `k > n'` : `k ∉ Ioi n' ∆ m` and `k ∈ Ioi n'` force `k ∈ m`.
      by_contra hkm
      refine hn'.left_top k hlt ?_
      rw [Set.mem_symmDiff]
      left
      exact ⟨hlt, hkm⟩
    · -- `k = n'` : `n' ∈ Ioi n' ∆ m` and `n' ∉ Ioi n'` force `n' ∈ m`.
      have := hn'.mem_left
      rw [Set.mem_symmDiff] at this
      rcases this with ⟨hcon, -⟩ | ⟨h1, -⟩
      · exact absurd (mem_Ioi.mp hcon) (lt_irrefl _)
      · exact h1

/-- **Sufficiency, identity case.** `x ∆ ∅ = x`. -/
theorem preservesTail_empty : PreservesTail (∅ : Set ℕ) := by
  intro a b hab
  left
  have h0 : ∀ s : Set ℕ, s ∆ (∅ : Set ℕ) = s := by
    intro s; ext k; simp [Set.mem_symmDiff]
  rw [h0, h0]
  exact hab

/-- **Sufficiency, reciprocal case.** `x ∆ ω = xᶜ`, and complement exchanges the
two sides of a tail pair. -/
theorem preservesTail_univ : PreservesTail (univ : Set ℕ) := by
  intro a b hab
  right
  obtain ⟨n, hn⟩ := hab
  refine ⟨n, ?_⟩
  have hc : ∀ s : Set ℕ, s ∆ (univ : Set ℕ) = sᶜ := by
    intro s; ext k; simp [Set.mem_symmDiff]
  rw [hc, hc]
  exact hn.compl

/-- **The rigidity theorem.**

For `m ⊆ ω`, the Boolean translation `x ↦ x ∆ m` descends to the tail quotient
if and only if `m = ∅` or `m = ω` — that is, if and only if it is the identity
or reciprocal.

Together with the sign coordinate this gives exactly the Klein four-group
`{∅, ω, {ω}, ω + 1} ≅ {x, -x, 1/x, -1/x}`: the Boolean structure on `P(ω)`
supports the `PGL₂` torsion elements and nothing else. In particular addition
is not a Boolean operation on this encoding. -/
theorem symmDiff_preservesTail_iff (m : Set ℕ) :
    PreservesTail m ↔ m = ∅ ∨ m = univ := by
  constructor
  · exact fun h => eq_empty_or_univ_of_tail_trivial (tailTrivial_of_preservesTail h)
  · rintro (rfl | rfl)
    · exact preservesTail_empty
    · exact preservesTail_univ

end SternBrocot
