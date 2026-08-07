/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.PathOrder
import SternBrocot.Order
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice

/-!
# Paths and the carrier

Everything about values lives in `List Bool`; everything about the carrier lives
in `Set ℕ`. This file joins them.

A path denotes the set of positions carrying a right move (`toSet`), and this is
a bijection between paths-up-to-trailing-left-moves and the **finite** subsets of
`ω`. Crucially the two orders agree: `PathLt` on paths is exactly `<ₗ` on the
sets they denote, so the order embedding of `PathOrder.lean` transfers to the
carrier without any reindexing.

The reverse direction is stated as an existence theorem rather than a function.
Producing a path *as data* from an arbitrary `x : Set ℕ` would need `Classical`,
since membership is not decidable; proving one exists needs only case analysis
and keeps the upstream files computable.

## Main results

* `SternBrocot.pathLt_iff_lexLt` — **the bridge**: `bs <ₚ cs ↔ toSet bs <ₗ toSet cs`.
* `SternBrocot.lexLt_toSet_iff` — composed with the order embedding: the lex
  order on nodes is the order of their values in `ℚ`.
* `SternBrocot.range_toSet` — the paths denote exactly the finite sets.
* `SternBrocot.toSet_injOn_canonical` — canonical paths biject with finite sets.
-/

open Set

namespace SternBrocot

/-! ### The set denoted by a path -/

/-- The finite subset of `ω` denoted by a path: the positions carrying a right
move. -/
def toSet (bs : List Bool) : Set ℕ := {n | bit bs n = true}

@[simp] theorem mem_toSet {bs : List Bool} {n : ℕ} : n ∈ toSet bs ↔ bit bs n = true := Iff.rfl

theorem notMem_toSet {bs : List Bool} {n : ℕ} : n ∉ toSet bs ↔ bit bs n = false := by
  simp

@[simp] theorem toSet_nil : toSet [] = (∅ : Set ℕ) := by
  ext n; simp

/-! ### Paths denote exactly the finite sets -/

theorem bit_eq_false_of_length_le {bs : List Bool} {n : ℕ} (h : bs.length ≤ n) :
    bit bs n = false := by
  induction bs generalizing n with
  | nil => simp
  | cons b bs ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      apply ih
      simp only [List.length_cons] at h
      omega

theorem toSet_subset_Iio (bs : List Bool) : toSet bs ⊆ Iio bs.length := by
  intro n hn
  rw [mem_toSet] at hn
  by_contra hc
  rw [mem_Iio, not_lt] at hc
  rw [bit_eq_false_of_length_le hc] at hn
  exact absurd hn (by simp)

theorem toSet_finite (bs : List Bool) : (toSet bs).Finite :=
  (Set.finite_lt_nat bs.length).subset (toSet_subset_Iio bs)

/-- Every set contained in `[0, N)` is denoted by some path. Stated as existence
rather than built as a function, so no `Classical` choice of representative is
needed — the case split lives in the proof. -/
theorem exists_path_of_subset_Iio :
    ∀ (N : ℕ) (x : Set ℕ), x ⊆ Iio N → ∃ bs, toSet bs = x := by
  intro N
  induction N with
  | zero =>
    intro x hx
    have hempty : x = ∅ :=
      eq_empty_of_forall_notMem fun n hn => absurd (mem_Iio.1 (hx hn)) (Nat.not_lt_zero n)
    exact ⟨[], by rw [hempty, toSet_nil]⟩
  | succ N ih =>
    intro x hx
    obtain ⟨bs, hbs⟩ := ih {m | m + 1 ∈ x} (by
      intro m hm
      have := mem_Iio.1 (hx hm)
      exact mem_Iio.2 (by omega))
    have htail : ∀ n : ℕ, (n ∈ toSet bs) ↔ (n + 1 ∈ x) := by
      intro n
      rw [hbs]
      exact Iff.rfl
    by_cases h0 : 0 ∈ x
    · refine ⟨true :: bs, ?_⟩
      ext n
      cases n with
      | zero => simpa using h0
      | succ n => rw [mem_toSet, bit_cons_succ, ← mem_toSet]; exact htail n
    · refine ⟨false :: bs, ?_⟩
      ext n
      cases n with
      | zero => simpa using h0
      | succ n => rw [mem_toSet, bit_cons_succ, ← mem_toSet]; exact htail n

/-- **The paths denote exactly the finite sets.** -/
theorem range_toSet : range toSet = {x : Set ℕ | x.Finite} := by
  ext x
  constructor
  · rintro ⟨bs, rfl⟩
    exact toSet_finite bs
  · intro hx
    obtain ⟨N, hN⟩ := hx.bddAbove
    exact exists_path_of_subset_Iio (N + 1) x fun n hn =>
      mem_Iio.2 (Nat.lt_succ_of_le (hN hn))

theorem exists_path_of_finite {x : Set ℕ} (hx : x.Finite) : ∃ bs, toSet bs = x := by
  have hmem : x ∈ range toSet := by rw [range_toSet]; exact hx
  exact hmem

/-! ### The orders agree

This is the point of the file: the lex order on `P(ω)` restricted to finite sets
is exactly `PathLt`, so nothing about the order has to be reproved downstream. -/

private theorem bool_iff_eq {b c : Bool} : (b = true ↔ c = true) ↔ b = c := by
  cases b <;> cases c <;> simp

/-- **The bridge.** The lex order on paths is the lex order on the sets they
denote. -/
theorem pathLt_iff_lexLt (bs cs : List Bool) : bs <ₚ cs ↔ toSet bs <ₗ toSet cs := by
  constructor
  · rintro ⟨n, hagree, hb, hc⟩
    refine ⟨n, fun k hk => ?_, ?_, ?_⟩
    · rw [mem_toSet, mem_toSet, hagree k hk]
    · rw [notMem_toSet]; exact hb
    · rw [mem_toSet]; exact hc
  · rintro ⟨n, hagree, hb, hc⟩
    refine ⟨n, fun k hk => ?_, ?_, ?_⟩
    · exact bool_iff_eq.1 (by simpa using hagree k hk)
    · rw [← notMem_toSet]; exact hb
    · rw [← mem_toSet]; exact hc

/-- The order embedding, on the carrier: for nodes, the lex order **is** the
order of their Stern–Brocot values. -/
theorem lexLt_toSet_iff (bs cs : List Bool) :
    toSet bs <ₗ toSet cs ↔ nodeValue bs < nodeValue cs := by
  rw [← pathLt_iff_lexLt, pathLt_iff_nodeValue_lt]

/-- Distinct paths denoting the same set have the same value. -/
theorem nodeValue_eq_of_toSet_eq {bs cs : List Bool} (h : toSet bs = toSet cs) :
    nodeValue bs = nodeValue cs := by
  refine nodeValue_eq_of_bit_eq bs cs fun n => ?_
  have := Set.ext_iff.mp h n
  rw [mem_toSet, mem_toSet] at this
  exact bool_iff_eq.1 this

/-- Canonical paths are determined by the set they denote, so they biject with
the finite subsets of `ω`. -/
theorem toSet_injOn_canonical : InjOn toSet {bs | Canonical bs} := by
  intro bs hbs cs hcs h
  exact nodeValue_injective_canonical hbs hcs (nodeValue_eq_of_toSet_eq h)

/-- Every finite set is denoted by a *canonical* path — the normal form. -/
theorem exists_canonical_path_of_finite {x : Set ℕ} (hx : x.Finite) :
    ∃ bs, Canonical bs ∧ toSet bs = x := by
  obtain ⟨bs, rfl⟩ := exists_path_of_finite hx
  obtain ⟨cs, hcs, hv⟩ := exists_canonical_of_nonneg (nodeValue_nonneg bs)
  refine ⟨cs, hcs, ?_⟩
  ext n
  rw [mem_toSet, mem_toSet]
  exact bool_iff_eq.2 (bit_eq_of_nodeValue_eq hv n)

end SternBrocot
