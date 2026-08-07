/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Enumeration

/-!
# `nodeValue` is an order embedding

The last ingredient before the supremum extension: the tree's value map respects
order. A finite path denotes a finite subset of `ω`, and the lex order on those
subsets is read off the path directly, padding with left moves past the end
(`bit`). The theorem is that this order is exactly the order of the values.

No canonicity hypothesis is needed. Two paths differing only by trailing left
moves are `PathLt`-incomparable *and* equal-valued, so the correspondence is
exact on the nose rather than merely on normal forms.

## The orientation, checked rather than assumed

Both moves are strictly increasing on `[0, ∞)`, and they have disjoint ranges:
`t ↦ t/(t+1)` lands in `[0, 1)` while `t ↦ t + 1` lands in `[1, ∞)`. So a
left-headed path is below every right-headed path, and within each branch order
is preserved. There is no orientation flip — the lex order on paths and the
numeric order agree uniformly.

## Main results

* `SternBrocot.nodeValue_pos_iff` — a path has positive value iff it has a right
  move somewhere.
* `SternBrocot.nodeValue_lt_of_pathLt` — monotonicity.
* `SternBrocot.pathLt_iff_nodeValue_lt` — **the order embedding**, both
  directions.
-/

namespace SternBrocot

/-! ### Bits of a path, padded with left moves -/

/-- Bit `n` of a path, `false` past the end. Padding with left moves is the right
convention because trailing left moves do not change the value
(`nodeValue_append_false`). -/
def bit : List Bool → ℕ → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: bs, n + 1 => bit bs n

@[simp] theorem bit_nil (n : ℕ) : bit [] n = false := by cases n <;> rfl

@[simp] theorem bit_cons_zero (b : Bool) (bs : List Bool) : bit (b :: bs) 0 = b := rfl

@[simp] theorem bit_cons_succ (b : Bool) (bs : List Bool) (n : ℕ) :
    bit (b :: bs) (n + 1) = bit bs n := rfl

/-! ### The lex order on paths -/

/-- The lex order on paths: at the least index where they differ, the larger path
has a right move. This is the lex order of `Order.lean` transported along
"a finite path denotes the finite set of positions carrying a right move". -/
def PathLt (bs cs : List Bool) : Prop :=
  ∃ n, (∀ k < n, bit bs k = bit cs k) ∧ bit bs n = false ∧ bit cs n = true

@[inherit_doc] scoped infix:50 " <ₚ " => PathLt

theorem pathLt_false_true (bs cs : List Bool) : (false :: bs) <ₚ (true :: cs) :=
  ⟨0, fun k hk => absurd hk (Nat.not_lt_zero k), rfl, rfl⟩

theorem not_pathLt_true_false (bs cs : List Bool) : ¬ ((true :: bs) <ₚ (false :: cs)) := by
  rintro ⟨n, hagree, hb, hc⟩
  cases n with
  | zero => simp at hb
  | succ n =>
    have := hagree 0 (Nat.succ_pos n)
    simp at this

/-- Prepending the same move on both sides does not change the comparison. -/
theorem pathLt_cons_iff (b : Bool) (bs cs : List Bool) :
    (b :: bs) <ₚ (b :: cs) ↔ bs <ₚ cs := by
  constructor
  · rintro ⟨n, hagree, hb, hc⟩
    cases n with
    | zero =>
      rw [bit_cons_zero] at hb hc
      simp [hb] at hc
    | succ n => exact ⟨n, fun k hk => hagree (k + 1) (by omega), hb, hc⟩
  · rintro ⟨n, hagree, hb, hc⟩
    refine ⟨n + 1, ?_, hb, hc⟩
    intro k hk
    cases k with
    | zero => rfl
    | succ k => exact hagree k (by omega)

/-! ### Positivity -/

/-- A path has positive value exactly when it contains a right move. -/
theorem nodeValue_pos_iff (bs : List Bool) : 0 < nodeValue bs ↔ ∃ n, bit bs n = true := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    cases b
    · have hd := nodeValue_denom_pos bs
      constructor
      · intro hp
        have hv : 0 < nodeValue bs := by
          by_contra hc
          have hz : nodeValue bs = 0 := le_antisymm (not_lt.1 hc) (nodeValue_nonneg bs)
          rw [nodeValue_false, hz] at hp
          simp at hp
        obtain ⟨n, hn⟩ := ih.1 hv
        exact ⟨n + 1, hn⟩
      · rintro ⟨n, hn⟩
        cases n with
        | zero => simp at hn
        | succ n =>
          rw [bit_cons_succ] at hn
          rw [nodeValue_false]
          exact div_pos (ih.2 ⟨n, hn⟩) hd
    · constructor
      · intro _; exact ⟨0, rfl⟩
      · intro _
        have := one_le_nodeValue_true bs
        linarith

/-- A path has value `0` exactly when it is all left moves. -/
theorem nodeValue_eq_zero_iff (bs : List Bool) : nodeValue bs = 0 ↔ ∀ n, bit bs n = false := by
  constructor
  · intro h n
    by_contra hc
    have hn : bit bs n = true := by simpa using hc
    have hp := (nodeValue_pos_iff bs).2 ⟨n, hn⟩
    rw [h] at hp
    exact lt_irrefl 0 hp
  · intro h
    refine le_antisymm (not_lt.1 fun hp => ?_) (nodeValue_nonneg bs)
    obtain ⟨n, hn⟩ := (nodeValue_pos_iff bs).1 hp
    rw [h n] at hn
    exact absurd hn (by simp)

/-! ### Monotonicity -/

/-- The left move `t ↦ t / (t + 1)` is strictly increasing on `[0, ∞)`. -/
theorem leftMove_strictMono {v w : ℚ} (hv : 0 ≤ v) (h : v < w) :
    v / (v + 1) < w / (w + 1) := by
  have hv1 : (0 : ℚ) < v + 1 := by linarith
  have hw1 : (0 : ℚ) < w + 1 := by linarith
  rw [← sub_pos]
  have key : w / (w + 1) - v / (v + 1) = (w - v) / ((v + 1) * (w + 1)) := by
    field_simp
    ring
  rw [key]
  exact div_pos (by linarith) (by positivity)

/-- **Monotonicity.** A path lower in the lex order has a strictly smaller
value. -/
theorem nodeValue_lt_of_pathLt : ∀ (bs cs : List Bool), bs <ₚ cs →
    nodeValue bs < nodeValue cs := by
  intro bs
  induction bs with
  | nil =>
    intro cs h
    obtain ⟨n, -, -, hc⟩ := h
    rw [nodeValue_nil]
    exact (nodeValue_pos_iff cs).2 ⟨n, hc⟩
  | cons b bs ih =>
    intro cs h
    cases cs with
    | nil =>
      obtain ⟨n, -, -, hc⟩ := h
      rw [bit_nil] at hc
      exact absurd hc (by simp)
    | cons c cs =>
      cases b <;> cases c
      · -- both left moves
        have h' := (pathLt_cons_iff false bs cs).1 h
        simp only [nodeValue_false]
        exact leftMove_strictMono (nodeValue_nonneg bs) (ih cs h')
      · -- left below right
        have h1 := nodeValue_false_lt_one bs
        have h2 := one_le_nodeValue_true cs
        linarith
      · -- right is never below left
        exact absurd h (not_pathLt_true_false bs cs)
      · -- both right moves
        have h' := (pathLt_cons_iff true bs cs).1 h
        have := ih cs h'
        simp only [nodeValue_true]
        linarith

/-! ### The embedding -/

/-- Paths with the same padded bit stream have the same value. -/
theorem nodeValue_eq_of_bit_eq : ∀ (bs cs : List Bool), (∀ n, bit bs n = bit cs n) →
    nodeValue bs = nodeValue cs := by
  intro bs
  induction bs with
  | nil =>
    intro cs h
    rw [nodeValue_nil, (nodeValue_eq_zero_iff cs).2 (fun n => (h n).symm.trans (bit_nil n))]
  | cons b bs ih =>
    intro cs h
    cases cs with
    | nil =>
      rw [nodeValue_nil, (nodeValue_eq_zero_iff (b :: bs)).2 (fun n => (h n).trans (bit_nil n))]
    | cons c cs =>
      have hbc : b = c := h 0
      subst hbc
      have htail : nodeValue bs = nodeValue cs := ih cs (fun n => h (n + 1))
      cases b <;> simp [htail]

/-- The lex order on paths is trichotomous, up to having the same padded stream. -/
theorem pathLt_trichotomy (bs cs : List Bool) :
    bs <ₚ cs ∨ cs <ₚ bs ∨ ∀ n, bit bs n = bit cs n := by
  classical
  by_cases h : ∀ n, bit bs n = bit cs n
  · exact Or.inr (Or.inr h)
  rw [not_forall] at h
  obtain ⟨n₀, hn₀⟩ := h
  have hex : ∃ n, bit bs n ≠ bit cs n := ⟨n₀, hn₀⟩
  set m := Nat.find hex with hm_def
  have hm : bit bs m ≠ bit cs m := Nat.find_spec hex
  have hmin : ∀ k < m, bit bs k = bit cs k := by
    intro k hk
    simpa using Nat.find_min hex hk
  cases hbm : bit bs m with
  | false =>
    refine Or.inl ⟨m, hmin, hbm, ?_⟩
    cases hcm : bit cs m with
    | false => exact absurd (hbm.trans hcm.symm) hm
    | true => rfl
  | true =>
    refine Or.inr (Or.inl ⟨m, fun k hk => (hmin k hk).symm, ?_, hbm⟩)
    cases hcm : bit cs m with
    | false => rfl
    | true => exact absurd (hbm.trans hcm.symm) hm

/-- **The order embedding.** `nodeValue` translates the lex order on paths into
the order on `ℚ`, in both directions.

With `nodeValue_bijOn` this makes the tree nodes an order-isomorphic copy of
`ℚ≥0` inside `P(ω)/∼` — the countable dense subset the supremum extension needs. -/
theorem pathLt_iff_nodeValue_lt (bs cs : List Bool) :
    bs <ₚ cs ↔ nodeValue bs < nodeValue cs := by
  refine ⟨nodeValue_lt_of_pathLt bs cs, fun h => ?_⟩
  rcases pathLt_trichotomy bs cs with hlt | hgt | heq
  · exact hlt
  · exact absurd (nodeValue_lt_of_pathLt cs bs hgt) (not_lt.2 h.le)
  · exact absurd (nodeValue_eq_of_bit_eq bs cs heq) (ne_of_lt h)

/-- Consequently the value determines the padded stream. -/
theorem bit_eq_of_nodeValue_eq {bs cs : List Bool} (h : nodeValue bs = nodeValue cs) :
    ∀ n, bit bs n = bit cs n := by
  rcases pathLt_trichotomy bs cs with hlt | hgt | heq
  · exact absurd ((pathLt_iff_nodeValue_lt bs cs).1 hlt) (by rw [h]; exact lt_irrefl _)
  · exact absurd ((pathLt_iff_nodeValue_lt cs bs).1 hgt) (by rw [h]; exact lt_irrefl _)
  · exact heq

end SternBrocot
