/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Induction
import SternBrocot.ToReal

/-!
# The shift, and what the moves do to values

Everything about periodicity is a statement about the *shift* `σ x = {n | n+1 ∈ x}`
— drop the first bit — and about how the two moves act on values. This file
supplies both, and packages a finite word of moves as a Möbius transformation.

## The two half-steps

`Node.lean` defines `nodeValue` by the recursion `R : t ↦ t + 1`,
`L : t ↦ t/(t+1)` on *finite* paths, where it is a finite computation. The
content here is that the same recursion holds for `Φ₀ = toReal₀` on **all** of
`P(ω)`, where the value is a supremum and not a computation:

* `toReal₀_S` : `Φ₀ (S y) = Φ₀ y + 1`
* `toReal₀_L` : `Φ₀ (L y) = Φ₀ y / (Φ₀ y + 1)`

Both need `y ≠ univ`, because `Φ₀` is junk at `∞` (`Real.sSup` of an unbounded
set is `0`). Read backwards along the shift they say what dropping a bit does:
`x ↦ x - 1` after a right move, `x ↦ x/(1 - x)` after a left move.

The proofs are cut manipulations. Splitting the nodes below `S y` by their first
bit, the ones starting `0` are all below `1` and the ones starting `1` are
exactly `1 +` the nodes below `y`; below `L y` only the nodes starting `0`
survive, and they are the image of the nodes below `y` under `t ↦ t/(t+1)`.

## Main results

* `SternBrocot.toReal₀_S`, `SternBrocot.toReal₀_L` — the recursion, on all of
  `P(ω)`.
* `SternBrocot.exists_applyPath` — every point is its own `k`-th shift with the
  first `k` moves put back on top.
* `SternBrocot.toReal₀_applyPath` — **prefixes act by Möbius transformations**:
  putting a word `w` back on top of `y` sends `Φ₀ y` to `pathMat w • Φ₀ y`. With
  `pathMat_det` this is the `SL₂(ℤ)` action, and it is what turns periodicity
  into a fixed-point equation.
-/

open Set

namespace SternBrocot

/-! ### The shift -/

/-- Drop the first bit: `σ x = {n | n + 1 ∈ x}`. -/
def shift (x : Set ℕ) : Set ℕ := {n | n + 1 ∈ x}

@[simp] theorem mem_shift {x : Set ℕ} {n : ℕ} : n ∈ shift x ↔ n + 1 ∈ x := Iff.rfl

@[simp] theorem shift_S (x : Set ℕ) : shift (S x) = x := by
  ext n; simp

@[simp] theorem shift_L (x : Set ℕ) : shift (L x) = x := by
  ext n; simp

/-- A point whose first bit is `1` is a right move applied to its shift. -/
theorem S_shift {x : Set ℕ} (h : 0 ∈ x) : S (shift x) = x := by
  ext n
  cases n with
  | zero => simpa using h
  | succ n => simp

/-- A point whose first bit is `0` is a left move applied to its shift. -/
theorem L_shift {x : Set ℕ} (h : 0 ∉ x) : L (shift x) = x := by
  ext n
  cases n with
  | zero => simpa using h
  | succ n => simp

@[simp] theorem shift_univ : shift (univ : Set ℕ) = univ := by
  ext n; simp

@[simp] theorem shift_empty : shift (∅ : Set ℕ) = ∅ := by
  ext n; simp

/-- The `k`-th shift reads the bits from position `k` on. -/
theorem iterate_shift (k : ℕ) (x : Set ℕ) : shift^[k] x = {n | n + k ∈ x} := by
  induction k generalizing x with
  | zero => ext n; simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    ext n
    show n + k ∈ shift x ↔ n + (k + 1) ∈ x
    rw [mem_shift, ← Nat.add_assoc]

theorem iterate_shift_eq_univ_iff {k : ℕ} {x : Set ℕ} :
    shift^[k] x = univ ↔ ∀ n, k ≤ n → n ∈ x := by
  rw [iterate_shift]
  constructor
  · intro h n hn
    have : n - k ∈ {m | m + k ∈ x} := h ▸ mem_univ _
    simpa [Nat.sub_add_cancel hn] using this
  · intro h
    ext n
    simp only [Set.mem_setOf_eq, mem_univ, iff_true]
    exact h _ (by omega)

/-! ### The moves and the lex order

Comparing two points whose first bits are known is comparing their shifts, and a
`0` beats a `1` at the first bit. -/

theorem L_lexLt_S (a b : Set ℕ) : L a <ₗ S b :=
  ⟨0, fun k hk => absurd hk (Nat.not_lt_zero k), zero_notMem_L a, zero_mem_S b⟩

theorem not_S_lexLt_L {a b : Set ℕ} : ¬ (S a <ₗ L b) := by
  rintro ⟨n, hagree, hna, hnb⟩
  cases n with
  | zero => exact hna (zero_mem_S a)
  | succ m => exact zero_notMem_L b ((hagree 0 (Nat.succ_pos m)).1 (zero_mem_S a))

@[simp] theorem lexLt_S_S {a b : Set ℕ} : S a <ₗ S b ↔ a <ₗ b := by
  constructor
  · rintro ⟨n, hagree, hna, hnb⟩
    cases n with
    | zero => exact absurd (zero_mem_S a) hna
    | succ m =>
      exact ⟨m, fun k hk => by simpa using hagree (k + 1) (by omega), by simpa using hna,
        by simpa using hnb⟩
  · rintro ⟨n, hagree, hna, hnb⟩
    refine ⟨n + 1, fun k hk => ?_, by simpa using hna, by simpa using hnb⟩
    cases k with
    | zero => simp
    | succ j => simpa using hagree j (by omega)

@[simp] theorem lexLt_L_L {a b : Set ℕ} : L a <ₗ L b ↔ a <ₗ b := by
  constructor
  · rintro ⟨n, hagree, hna, hnb⟩
    cases n with
    | zero => exact absurd hnb (zero_notMem_L b)
    | succ m =>
      exact ⟨m, fun k hk => by simpa using hagree (k + 1) (by omega), by simpa using hna,
        by simpa using hnb⟩
  · rintro ⟨n, hagree, hna, hnb⟩
    refine ⟨n + 1, fun k hk => ?_, by simpa using hna, by simpa using hnb⟩
    cases k with
    | zero => simp
    | succ j => simpa using hagree j (by omega)

/-! ### The moves and the two extreme points -/

theorem L_ne_univ (x : Set ℕ) : L x ≠ univ := fun h => zero_notMem_L x (h ▸ mem_univ 0)

@[simp] theorem S_eq_univ_iff {x : Set ℕ} : S x = univ ↔ x = univ := by
  constructor
  · intro h
    ext n
    simpa using Set.ext_iff.1 h (n + 1)
  · rintro rfl
    ext n
    cases n <;> simp

@[simp] theorem L_eq_empty_iff {x : Set ℕ} : L x = ∅ ↔ x = ∅ := by
  constructor
  · intro h
    ext n
    have := Set.ext_iff.1 h (n + 1)
    simpa using this
  · rintro rfl
    ext n
    cases n <;> simp

theorem S_ne_empty (x : Set ℕ) : S x ≠ ∅ := fun h => (h ▸ zero_mem_S x : (0 : ℕ) ∈ (∅ : Set ℕ))

/-! ### The right move adds one

`Φ₀ (S y) = Φ₀ y + 1`. The nodes below `S y` are the nodes starting with `0`,
all of which are below `1`, together with `1 +` the nodes below `y`. -/

theorem toReal₀_S {y : Set ℕ} (hy : y ≠ univ) : toReal₀ (S y) = toReal₀ y + 1 := by
  rcases eq_or_ne y ∅ with rfl | hy0
  · have : S (∅ : Set ℕ) = toSet [true] := by rw [toSet_cons_true, toSet_nil]
    rw [this, toReal₀_toSet, toReal₀_empty]
    norm_num [nodeValue]
  have hne : (below y).Nonempty := ⟨0, [], by rw [toSet_nil]; exact empty_lexLt hy0, by simp⟩
  have hbdd : BddAbove (below y) := bddAbove_below hy
  have hy0' : (0 : ℝ) ≤ toReal₀ y := toReal₀_nonneg y
  have hSne : (below (S y)).Nonempty :=
    ⟨0, [], by rw [toSet_nil]; exact empty_lexLt (S_ne_empty y), by simp⟩
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt hSne ?_ ?_
  · rintro r ⟨bs, hbs, rfl⟩
    cases bs with
    | nil => simp only [nodeValue_nil, Rat.cast_zero]; linarith
    | cons b cs =>
      cases b
      · -- a node starting with a left move is below `1`
        have hv : (0 : ℚ) ≤ nodeValue cs := nodeValue_nonneg cs
        have hle : nodeValue (false :: cs) ≤ 1 := by
          rw [nodeValue_false]
          rw [div_le_one (by linarith)]
          linarith
        have : ((nodeValue (false :: cs) : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hle
        linarith
      · -- a node starting with a right move is `1 +` a node below `y`
        rw [toSet_cons_true] at hbs
        have hcs : toSet cs <ₗ y := lexLt_S_S.1 hbs
        have hmem : ((nodeValue cs : ℚ) : ℝ) ∈ below y := ⟨cs, hcs, rfl⟩
        have hle : ((nodeValue cs : ℚ) : ℝ) ≤ toReal₀ y := le_csSup hbdd hmem
        rw [nodeValue_true]
        push_cast
        linarith
  · intro w hw
    obtain ⟨r, ⟨cs, hcs, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne (show w - 1 < toReal₀ y by linarith)
    refine ⟨((nodeValue (true :: cs) : ℚ) : ℝ), ⟨true :: cs, ?_, rfl⟩, ?_⟩
    · rw [toSet_cons_true]; exact lexLt_S_S.2 hcs
    · rw [nodeValue_true]; push_cast; linarith

/-! ### The left move

`Φ₀ (L y) = Φ₀ y / (Φ₀ y + 1)`. Only nodes starting with `0` are below `L y`,
and they are the image of the nodes below `y` under the increasing map
`t ↦ t/(t+1)`. -/

private theorem frac_mono {u v : ℝ} (hu : -1 < u) (huv : u < v) : u / (u + 1) < v / (v + 1) := by
  have h1 : (0 : ℝ) < u + 1 := by linarith
  have h2 : (0 : ℝ) < v + 1 := by linarith
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith

private theorem frac_mono_le {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : u / (u + 1) ≤ v / (v + 1) := by
  have h1 : (0 : ℝ) < u + 1 := by linarith
  have h2 : (0 : ℝ) < v + 1 := by linarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith

theorem toReal₀_L {y : Set ℕ} (hy : y ≠ univ) :
    toReal₀ (L y) = toReal₀ y / (toReal₀ y + 1) := by
  rcases eq_or_ne y ∅ with rfl | hy0
  · rw [show L (∅ : Set ℕ) = ∅ from L_eq_empty_iff.2 rfl, toReal₀_empty]
    norm_num
  have hne : (below y).Nonempty := ⟨0, [], by rw [toSet_nil]; exact empty_lexLt hy0, by simp⟩
  have hbdd : BddAbove (below y) := bddAbove_below hy
  have ht0 : (0 : ℝ) ≤ toReal₀ y := toReal₀_nonneg y
  have hLne : (below (L y)).Nonempty :=
    ⟨0, [], by rw [toSet_nil]; exact empty_lexLt (fun hc => hy0 (L_eq_empty_iff.1 hc)), by simp⟩
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt hLne ?_ ?_
  · rintro r ⟨bs, hbs, rfl⟩
    cases bs with
    | nil =>
      have : (0 : ℝ) ≤ toReal₀ y / (toReal₀ y + 1) := div_nonneg ht0 (by linarith)
      simpa using this
    | cons b cs =>
      cases b
      · rw [toSet_cons_false] at hbs
        have hcs : toSet cs <ₗ y := lexLt_L_L.1 hbs
        have hmem : ((nodeValue cs : ℚ) : ℝ) ∈ below y := ⟨cs, hcs, rfl⟩
        have hle := le_csSup hbdd hmem
        have hv0 : (0 : ℝ) ≤ ((nodeValue cs : ℚ) : ℝ) := by
          exact_mod_cast nodeValue_nonneg cs
        have : ((nodeValue (false :: cs) : ℚ) : ℝ)
            = ((nodeValue cs : ℚ) : ℝ) / (((nodeValue cs : ℚ) : ℝ) + 1) := by
          rw [nodeValue_false]; push_cast; ring
        rw [this]
        exact frac_mono_le hv0 hle
      · rw [toSet_cons_true] at hbs
        exact absurd hbs not_S_lexLt_L
  · intro w hw
    -- `w < t/(t+1) ≤ 1`, so `u = w/(1-w)` is a real strictly below `t` with `u/(u+1) = w`
    have hw1 : w < 1 := lt_of_lt_of_le hw (by rw [div_le_one (by linarith)]; linarith)
    have h1w : (0 : ℝ) < 1 - w := by linarith
    set u : ℝ := w / (1 - w) with hu
    have hu1 : (0 : ℝ) < u + 1 := by
      rw [hu]
      have h : w / (1 - w) + 1 = 1 / (1 - w) := by field_simp; ring
      rw [h]
      positivity
    have huw : u / (u + 1) = w := by
      rw [hu]; field_simp; ring
    have hut : u < toReal₀ y := by
      rw [hu, div_lt_iff₀ h1w]
      rw [lt_div_iff₀ (show (0:ℝ) < toReal₀ y + 1 by linarith)] at hw
      nlinarith
    obtain ⟨r, ⟨cs, hcs, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne hut
    refine ⟨((nodeValue (false :: cs) : ℚ) : ℝ), ⟨false :: cs, ?_, rfl⟩, ?_⟩
    · rw [toSet_cons_false]; exact lexLt_L_L.2 hcs
    · have : ((nodeValue (false :: cs) : ℚ) : ℝ)
          = ((nodeValue cs : ℚ) : ℝ) / (((nodeValue cs : ℚ) : ℝ) + 1) := by
        rw [nodeValue_false]; push_cast; ring
      rw [this, ← huw]
      exact frac_mono (by linarith) hlt

/-! ### Reading the shift backwards -/

theorem toReal₀_shift_of_mem {x : Set ℕ} (h0 : 0 ∈ x) (hx : shift x ≠ univ) :
    toReal₀ (shift x) = toReal₀ x - 1 := by
  have := toReal₀_S (y := shift x) hx
  rw [S_shift h0] at this
  linarith

theorem toReal₀_shift_of_notMem {x : Set ℕ} (h0 : 0 ∉ x) (hx : shift x ≠ univ) :
    toReal₀ x = toReal₀ (shift x) / (toReal₀ (shift x) + 1) := by
  have := toReal₀_L (y := shift x) hx
  rwa [L_shift h0] at this

/-! ### Putting a finite word back on top -/

/-- Apply a finite word of moves to a point. The head of the list is the move
nearest the root, matching `toSet`. -/
def applyPath : List Bool → Set ℕ → Set ℕ
  | [], x => x
  | true :: bs, x => S (applyPath bs x)
  | false :: bs, x => L (applyPath bs x)

@[simp] theorem applyPath_nil (x : Set ℕ) : applyPath [] x = x := rfl

@[simp] theorem applyPath_cons_true (bs : List Bool) (x : Set ℕ) :
    applyPath (true :: bs) x = S (applyPath bs x) := rfl

@[simp] theorem applyPath_cons_false (bs : List Bool) (x : Set ℕ) :
    applyPath (false :: bs) x = L (applyPath bs x) := rfl

/-- On `∅` the word is just the node it denotes. -/
@[simp] theorem applyPath_empty (bs : List Bool) : applyPath bs ∅ = toSet bs := by
  induction bs with
  | nil => simp
  | cons b bs ih => cases b <;> simp [ih]

theorem applyPath_ne_univ (bs : List Bool) {y : Set ℕ} (hy : y ≠ univ) :
    applyPath bs y ≠ univ := by
  induction bs with
  | nil => exact hy
  | cons b bs ih =>
    cases b
    · exact L_ne_univ _
    · exact fun hc => ih (S_eq_univ_iff.1 hc)

/-- **Every point is its own `k`-th shift with the first `k` moves put back.** -/
theorem exists_applyPath (x : Set ℕ) (k : ℕ) :
    ∃ bs : List Bool, bs.length = k ∧ applyPath bs (shift^[k] x) = x := by
  classical
  induction k generalizing x with
  | zero => exact ⟨[], rfl, rfl⟩
  | succ k ih =>
    obtain ⟨bs, hlen, hap⟩ := ih (shift x)
    rw [Function.iterate_succ_apply]
    by_cases h0 : 0 ∈ x
    · exact ⟨true :: bs, by simp [hlen], by rw [applyPath_cons_true, hap]; exact S_shift h0⟩
    · exact ⟨false :: bs, by simp [hlen], by rw [applyPath_cons_false, hap]; exact L_shift h0⟩

/-! ### Words act by Möbius transformations -/

/-- The Möbius action of an integer matrix `(a, b, c, d)` on a real:
`t ↦ (a t + b)/(c t + d)`. -/
noncomputable def mobius (m : ℤ × ℤ × ℤ × ℤ) (t : ℝ) : ℝ :=
  ((m.1 : ℝ) * t + (m.2.1 : ℝ)) / ((m.2.2.1 : ℝ) * t + (m.2.2.2 : ℝ))

/-- The four entries of a path matrix: the diagonal is positive and the
off-diagonal nonnegative. Stronger than `pathMat_den_pos`, and what makes the
Möbius denominator positive on `[0, ∞)`. -/
theorem pathMat_entries (bs : List Bool) :
    0 < (pathMat bs).1 ∧ 0 ≤ (pathMat bs).2.1 ∧ 0 ≤ (pathMat bs).2.2.1 ∧
      0 < (pathMat bs).2.2.2 := by
  induction bs with
  | nil => exact ⟨one_pos, le_refl 0, le_refl 0, one_pos⟩
  | cons b bs ih =>
    obtain ⟨ha, hb, hc, hd⟩ := ih
    cases b
    · exact ⟨ha, hb, by simp only [pathMat]; linarith, by simp only [pathMat]; linarith⟩
    · exact ⟨by simp only [pathMat]; linarith, by simp only [pathMat]; linarith, hc, hd⟩

theorem pathMat_den_pos_real (bs : List Bool) {t : ℝ} (ht : 0 ≤ t) :
    (0 : ℝ) < ((pathMat bs).2.2.1 : ℝ) * t + ((pathMat bs).2.2.2 : ℝ) := by
  obtain ⟨-, -, hc, hd⟩ := pathMat_entries bs
  have hc' : (0 : ℝ) ≤ ((pathMat bs).2.2.1 : ℝ) := by exact_mod_cast hc
  have hd' : (0 : ℝ) < ((pathMat bs).2.2.2 : ℝ) := by exact_mod_cast hd
  have := mul_nonneg hc' ht
  linarith

theorem pathMat_num_nonneg_real (bs : List Bool) {t : ℝ} (ht : 0 ≤ t) :
    (0 : ℝ) ≤ ((pathMat bs).1 : ℝ) * t + ((pathMat bs).2.1 : ℝ) := by
  obtain ⟨ha, hb, -, -⟩ := pathMat_entries bs
  have ha' : (0 : ℝ) < ((pathMat bs).1 : ℝ) := by exact_mod_cast ha
  have hb' : (0 : ℝ) ≤ ((pathMat bs).2.1 : ℝ) := by exact_mod_cast hb
  have := mul_nonneg ha'.le ht
  linarith

private theorem frac_div (A D : ℝ) (hD : D ≠ 0) (_hAD : A + D ≠ 0) :
    (A / D) / (A / D + 1) = A / (A + D) := by
  rw [div_add' _ _ _ hD, div_div_div_cancel_right₀ hD, one_mul]

/-- **Prefixes act by Möbius transformations.** Putting the word `bs` back on top
of `y` sends `Φ₀ y` to `pathMat bs • Φ₀ y`.

With `pathMat_det` — the matrix is in `SL₂(ℤ)` — this is what converts an
eventually periodic path into a fixed-point equation, hence a quadratic. -/
theorem toReal₀_applyPath (bs : List Bool) {y : Set ℕ} (hy : y ≠ univ) :
    toReal₀ (applyPath bs y) = mobius (pathMat bs) (toReal₀ y) := by
  have ht : (0 : ℝ) ≤ toReal₀ y := toReal₀_nonneg y
  induction bs with
  | nil => simp [mobius]
  | cons b bs ih =>
    have hne := applyPath_ne_univ bs hy
    have hden := pathMat_den_pos_real bs ht
    have hnum := pathMat_num_nonneg_real bs ht
    have hd : ((pathMat bs).2.2.1 : ℝ) * toReal₀ y + ((pathMat bs).2.2.2 : ℝ) ≠ 0 := ne_of_gt hden
    have hs : (((pathMat bs).1 : ℝ) * toReal₀ y + ((pathMat bs).2.1 : ℝ))
        + (((pathMat bs).2.2.1 : ℝ) * toReal₀ y + ((pathMat bs).2.2.2 : ℝ)) ≠ 0 := by
      intro hc; linarith
    cases b
    · rw [applyPath_cons_false, toReal₀_L hne, ih]
      simp only [mobius, pathMat]
      push_cast
      rw [frac_div _ _ hd hs]
      ring_nf
    · rw [applyPath_cons_true, toReal₀_S hne, ih]
      simp only [mobius, pathMat]
      push_cast
      rw [div_add' _ _ _ hd, one_mul]
      congr 1
      ring

end SternBrocot
