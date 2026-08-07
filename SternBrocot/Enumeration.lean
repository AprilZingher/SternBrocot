/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Node
import Mathlib.Data.Set.Function
import Mathlib.Data.Rat.Floor

/-!
# The tree enumerates `ℚ≥0` exactly once

The Stern–Brocot theorem, in the form this development needs: `nodeValue` is a
**bijection** from canonical finite paths onto the nonnegative rationals.

A path is *canonical* when it is empty or ends in a right move. Trailing left
moves are invisible (`nodeValue_append_false`), so canonical paths are exactly
the normal forms, and they correspond to the finite subsets of `ω` — the tree
nodes, which form the countable dense subset needed for `Φ`.

* **Surjectivity** is the Euclidean algorithm. Given `a / b`, either it is `≥ 1`
  and we strip a right move (`a ↦ a - b`), or it is in `(0, 1)` and we strip a
  left move (`b ↦ b - a`). Either way `a + b` drops, so the recursion halts.
* **Injectivity** is a head-comparison: right-headed paths have value `≥ 1`,
  left-headed paths have value `< 1`, so the first move is determined by the
  value, and both moves are injective.

## Main results

* `SternBrocot.nodeValue_injOn` — injectivity on canonical paths.
* `SternBrocot.exists_canonical_of_nonneg` — surjectivity onto `ℚ≥0`.
* `SternBrocot.nodeValue_bijOn` — **the enumeration theorem**: `nodeValue` is a
  bijection from canonical paths onto `{q : ℚ | 0 ≤ q}`.
-/

open Set

namespace SternBrocot

/-! ### Canonical paths -/

/-- A path is canonical when it is empty or ends in a right move. Trailing left
moves do not change the value, so these are the normal forms. -/
inductive Canonical : List Bool → Prop
  /-- The empty path, denoting `0`. -/
  | nil : Canonical []
  /-- The one-step right path, denoting `1`. -/
  | single : Canonical [true]
  /-- Any move may be prepended to a nonempty canonical path. -/
  | cons {b : Bool} {bs : List Bool} (hne : bs ≠ []) (h : Canonical bs) :
      Canonical (b :: bs)

theorem Canonical.tail {b : Bool} {bs : List Bool} (h : Canonical (b :: bs)) :
    Canonical bs := by
  cases h with
  | single => exact Canonical.nil
  | cons _ h => exact h

/-- A canonical path cannot end in a left move, so `[false]` is not canonical and
more generally a left-headed canonical path has a nonempty tail. -/
theorem Canonical.ne_nil_of_false {bs : List Bool} (h : Canonical (false :: bs)) :
    bs ≠ [] := by
  cases h with
  | cons hne _ => exact hne

/-- Any path ending in a right move is canonical. -/
theorem canonical_append_true (bs : List Bool) : Canonical (bs ++ [true]) := by
  induction bs with
  | nil => exact Canonical.single
  | cons b bs ih => exact Canonical.cons (by simp) ih

/-- ...and conversely. So `Canonical` really is "empty, or ends in a right
move" — the normal forms for `nodeValue_append_false`. -/
theorem Canonical.eq_nil_or_append_true {bs : List Bool} (h : Canonical bs) :
    bs = [] ∨ ∃ cs, bs = cs ++ [true] := by
  induction h with
  | nil => exact Or.inl rfl
  | single => exact Or.inr ⟨[], rfl⟩
  | cons hne _ ih =>
    rcases ih with rfl | ⟨cs, rfl⟩
    · exact absurd rfl hne
    · exact Or.inr ⟨_ :: cs, rfl⟩

/-- `Canonical` characterised. -/
theorem canonical_iff (bs : List Bool) :
    Canonical bs ↔ bs = [] ∨ ∃ cs, bs = cs ++ [true] := by
  refine ⟨Canonical.eq_nil_or_append_true, ?_⟩
  rintro (rfl | ⟨cs, rfl⟩)
  · exact Canonical.nil
  · exact canonical_append_true cs

/-! ### Head comparison

The first move of a path is determined by whether its value is `≥ 1`. -/

theorem one_le_nodeValue_true (bs : List Bool) : 1 ≤ nodeValue (true :: bs) := by
  have := nodeValue_nonneg bs
  simp only [nodeValue_true]
  linarith

theorem nodeValue_false_lt_one (bs : List Bool) : nodeValue (false :: bs) < 1 := by
  have h := nodeValue_nonneg bs
  have hd := nodeValue_denom_pos bs
  simp only [nodeValue_false]
  rw [div_lt_one hd]
  linarith

/-- The left move is injective on nonnegative values. -/
theorem nodeValue_false_inj {bs cs : List Bool}
    (h : nodeValue (false :: bs) = nodeValue (false :: cs)) : nodeValue bs = nodeValue cs := by
  have hb := nodeValue_denom_pos bs
  have hc := nodeValue_denom_pos cs
  simp only [nodeValue_false] at h
  field_simp at h
  linarith

/-- Only the all-left paths have value `0`, and the only canonical one is empty. -/
theorem eq_nil_of_nodeValue_eq_zero {bs : List Bool} (hc : Canonical bs)
    (h : nodeValue bs = 0) : bs = [] := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b
    · -- left move: forces the tail to have value `0` too
      have hd := nodeValue_denom_pos bs
      have htail : nodeValue bs = 0 := by
        simp only [nodeValue_false] at h
        field_simp at h
        linarith
      exact absurd (ih hc.tail htail) hc.ne_nil_of_false
    · -- right move: value is at least `1`
      have := one_le_nodeValue_true bs
      rw [h] at this
      linarith

/-! ### Injectivity -/

/-- **Injectivity.** Distinct canonical paths have distinct values. -/
theorem nodeValue_injective_canonical :
    ∀ {bs cs : List Bool}, Canonical bs → Canonical cs → nodeValue bs = nodeValue cs → bs = cs := by
  intro bs
  induction bs with
  | nil =>
    intro cs _ hcs h
    exact (eq_nil_of_nodeValue_eq_zero hcs h.symm).symm
  | cons b bs ih =>
    intro cs hbs hcs h
    cases cs with
    | nil =>
      -- `nodeValue cs = 0`, so the left side must be `[]` too — impossible.
      exact absurd (eq_nil_of_nodeValue_eq_zero hbs h) (List.cons_ne_nil b bs)
    | cons c cs =>
      cases b <;> cases c
      · -- both left
        have := nodeValue_false_inj h
        exact congrArg (List.cons false) (ih hbs.tail hcs.tail this)
      · -- left vs right: `< 1` versus `≥ 1`
        have h1 := nodeValue_false_lt_one bs
        have h2 := one_le_nodeValue_true cs
        rw [h] at h1
        linarith
      · -- right vs left
        have h1 := one_le_nodeValue_true bs
        have h2 := nodeValue_false_lt_one cs
        rw [h] at h1
        linarith
      · -- both right
        simp only [nodeValue_true, add_left_inj] at h
        exact congrArg (List.cons true) (ih hbs.tail hcs.tail h)

theorem nodeValue_injOn : InjOn nodeValue {bs | Canonical bs} :=
  fun _ hb _ hc h => nodeValue_injective_canonical hb hc h

/-! ### Surjectivity

The Euclidean algorithm, with `a + b` as the decreasing measure. -/

/-- Every nonnegative fraction `a / b` is the value of a canonical path.

The recursion is the Euclidean algorithm: strip a right move when `a ≥ b`
(replacing `a` by `a - b`), a left move when `0 < a < b` (replacing `b` by
`b - a`). Both steps decrease `a + b`, which is the fuel. -/
theorem exists_canonical_aux :
    ∀ (n a b : ℕ), a + b ≤ n → 0 < b → ∃ bs, Canonical bs ∧ nodeValue bs = (a : ℚ) / (b : ℚ) := by
  intro n
  induction n with
  | zero => intro a b hab hb; omega
  | succ n ih =>
    intro a b hab hb
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · exact ⟨[], Canonical.nil, by simp⟩
    by_cases hba : b ≤ a
    · -- `a / b ≥ 1`: strip a right move.
      obtain ⟨w, hw, hwv⟩ := ih (a - b) b (by omega) hb
      refine ⟨true :: w, ?_, ?_⟩
      · cases w with
        | nil => exact Canonical.single
        | cons c cs => exact Canonical.cons (List.cons_ne_nil c cs) hw
      · have hbQ : ((b : ℕ) : ℚ) ≠ 0 := by positivity
        have hsub : (((a - b : ℕ)) : ℚ) = (a : ℚ) - (b : ℚ) := by
          push_cast [Nat.cast_sub hba]; ring
        rw [nodeValue_true, hwv, hsub]
        field_simp
        ring
    · -- `0 < a / b < 1`: strip a left move.
      replace hba : a < b := by omega
      obtain ⟨w, hw, hwv⟩ := ih a (b - a) (by omega) (by omega)
      have haQ : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
      have hsub : (((b - a : ℕ)) : ℚ) = (b : ℚ) - (a : ℚ) := by
        push_cast [Nat.cast_sub hba.le]; ring
      have hpos : (0 : ℚ) < (b : ℚ) - (a : ℚ) := by
        rw [← hsub]
        have : 0 < b - a := by omega
        exact_mod_cast this
      have hwpos : 0 < nodeValue w := by
        rw [hwv, hsub]
        positivity
      refine ⟨false :: w, Canonical.cons ?_ hw, ?_⟩
      · intro hnil
        rw [hnil] at hwpos
        simp at hwpos
      · rw [nodeValue_false, hwv, hsub]
        have hbQ : ((b : ℕ) : ℚ) ≠ 0 := by positivity
        field_simp
        ring

/-- **Surjectivity.** Every nonnegative rational is the value of a canonical
path. -/
theorem exists_canonical_of_nonneg {q : ℚ} (hq : 0 ≤ q) :
    ∃ bs, Canonical bs ∧ nodeValue bs = q := by
  obtain ⟨bs, hbs, hv⟩ :=
    exists_canonical_aux (q.num.toNat + q.den) q.num.toNat q.den le_rfl q.den_pos
  refine ⟨bs, hbs, ?_⟩
  rw [hv]
  have hnum : ((q.num.toNat : ℕ) : ℚ) = (q.num : ℚ) := by
    have : 0 ≤ q.num := Rat.num_nonneg.2 hq
    exact_mod_cast Int.toNat_of_nonneg this
  rw [hnum]
  exact Rat.num_div_den q

/-! ### The enumeration theorem -/

/-- **The Stern–Brocot tree enumerates `ℚ≥0` exactly once.**

`nodeValue` is a bijection from canonical finite paths onto the nonnegative
rationals. Combined with `nodeValue_num_den_coprime`, each rational appears at
exactly one node, already in lowest terms.

This is the countable dense subset that `Φ` is built from. -/
theorem nodeValue_bijOn : BijOn nodeValue {bs | Canonical bs} {q : ℚ | 0 ≤ q} := by
  refine ⟨fun bs _ => nodeValue_nonneg bs, nodeValue_injOn, ?_⟩
  intro q hq
  obtain ⟨bs, hbs, hv⟩ := exists_canonical_of_nonneg hq
  exact ⟨bs, hbs, hv⟩

end SternBrocot
