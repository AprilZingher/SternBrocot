/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Lagrange
import Mathlib.NumberTheory.Real.Irrational

/-!
# The convergents

In this encoding the convergents of `x` are **not** the prefixes of the bit path.
They are the prefixes at the **run boundaries** — the positions where an `R`-run
flips to an `L`-run or back. A prefix in the middle of a run is an intermediate
mediant, and the classical estimates fail there. This file builds the run
decomposition and the two estimates on it.

## The dictionary

A prefix `w` of the path acts on the value of the tail by the Möbius map of
`pathMat w` (`toReal₀_applyPath`), so with `pathMat w = (A, B, C, D)` and
`s = Φ₀ (σ^n x) ≥ 0`,

  `Φ₀ x = (A s + B) / (C s + D)`.

The two *columns* `(B, D)` and `(A, C)` are the two fractions bracketing `x`:
they are the images of `s = 0` and `s = ∞`. Unimodularity (`pathMat_det`) makes
the gap between them exactly `1 / (C D)`, which is the whole source of the
approximation estimates. At a run boundary those two columns are **consecutive
convergents**; in mid-run one of them is an intermediate mediant instead.

## Main definitions

* `SternBrocot.prefixWord` — the first `n` bits of a path, as a word.
* `SternBrocot.runBoundary` — the increasing sequence of flip positions.
  `SternBrocot.partialQuot` — the run lengths, i.e. the partial quotients.
* `SternBrocot.contin` — the continuants `(pₖ, qₖ)`, by the classical
  recurrence `cₖ₊₂ = aₖ cₖ₊₁ + cₖ`.

## Main results

* `SternBrocot.boundaryMat_eq_contin` — **the recurrence**: at run boundary
  `k` the prefix matrix has columns `contin x k` and `contin x (k+1)`, in an
  order that alternates with the run's bit. This is where `pₖ = aₖ pₖ₋₁ + pₖ₋₂`
  lives.
* `SternBrocot.contin_den_le_succ` — `qₖ ≤ qₖ₊₁`, for `k ≥ 1`. False for
  arbitrary prefixes, which is why this file is indexed by runs.
* `SternBrocot.abs_sub_contin_lt` — `|Φ₀ x − pₖ/qₖ| < 1/(qₖ qₖ₊₁)`.

## Indexing

`contin x 0` and `contin x 1` are the seeds `(0,1)` and `(1,0)`, *swapped* when
the path starts with a left move. The swap is what makes one recurrence serve
both `x ≥ 1` and `x < 1`: for `x < 1` the classical `a₀ = 0` is not stored as a
run, so the whole sequence shifts by one. Consequently `contin x k` is a genuine
convergent for `k ≥ 2` in either case, and no statement below uses `k ≤ 1`.
-/

open Set

namespace SternBrocot

/-! ### Reading the bits of a path -/

open Classical in
/-- The `n`-th bit of the path of `x`. -/
noncomputable def bitAt (x : Set ℕ) (n : ℕ) : Bool := if n ∈ x then true else false

@[simp] theorem bitAt_eq_true {x : Set ℕ} {n : ℕ} : bitAt x n = true ↔ n ∈ x := by
  classical simp [bitAt]

@[simp] theorem bitAt_eq_false {x : Set ℕ} {n : ℕ} : bitAt x n = false ↔ n ∉ x := by
  classical simp [bitAt]

/-- The first `n` bits of the path of `x`, head nearest the root. -/
noncomputable def prefixWord (x : Set ℕ) : ℕ → List Bool
  | 0 => []
  | n + 1 => prefixWord x n ++ [bitAt x n]

@[simp] theorem prefixWord_zero (x : Set ℕ) : prefixWord x 0 = [] := rfl

theorem prefixWord_succ (x : Set ℕ) (n : ℕ) :
    prefixWord x (n + 1) = prefixWord x n ++ [bitAt x n] := rfl

@[simp] theorem length_prefixWord (x : Set ℕ) (n : ℕ) : (prefixWord x n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [prefixWord_succ, List.length_append, ih]; rfl

/-! ### Words compose, matrices multiply

`applyPath` on a concatenation is composition, and `pathMat` turns that into a
product. Everything downstream is bookkeeping with these two. -/

/-- The product of two Möbius matrices, in the `(a, b, c, d)` encoding. -/
def matMul (m n : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (m.1 * n.1 + m.2.1 * n.2.2.1, m.1 * n.2.1 + m.2.1 * n.2.2.2,
   m.2.2.1 * n.1 + m.2.2.2 * n.2.2.1, m.2.2.1 * n.2.1 + m.2.2.2 * n.2.2.2)

theorem matMul_assoc (m n p : ℤ × ℤ × ℤ × ℤ) :
    matMul (matMul m n) p = matMul m (matMul n p) := by
  simp only [matMul, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem applyPath_append (v w : List Bool) (y : Set ℕ) :
    applyPath (v ++ w) y = applyPath v (applyPath w y) := by
  induction v with
  | nil => rfl
  | cons b v ih => cases b <;> simp [ih]

theorem pathMat_append (v w : List Bool) :
    pathMat (v ++ w) = matMul (pathMat v) (pathMat w) := by
  induction v with
  | nil => simp [matMul]
  | cons b v ih =>
    cases b <;>
      · simp only [List.cons_append, pathMat, ih, matMul, Prod.mk.injEq]
        and_intros <;> first | trivial | ring

/-- A run of `n` right moves is the shear `t ↦ t + n`. -/
theorem pathMat_replicate_true (n : ℕ) :
    pathMat (List.replicate n true) = (1, (n : ℤ), 0, 1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ]; simp only [pathMat, ih]; push_cast; ring_nf

/-- A run of `n` left moves is `t ↦ t / (n t + 1)`. -/
theorem pathMat_replicate_false (n : ℕ) :
    pathMat (List.replicate n false) = (1, 0, (n : ℤ), 1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ]; simp only [pathMat, ih]; push_cast; ring_nf

/-! ### The prefix puts the path back together

`exists_applyPath` says *some* word of length `n` rebuilds `x` from its `n`-th
shift; here it is, named. -/

theorem applyPath_prefixWord (x : Set ℕ) (n : ℕ) :
    applyPath (prefixWord x n) (shift^[n] x) = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [prefixWord_succ, applyPath_append]
    have hstep : applyPath [bitAt x n] (shift^[n + 1] x) = shift^[n] x := by
      rw [Function.iterate_succ_apply']
      by_cases h : n ∈ x
      · have hb : bitAt x n = true := bitAt_eq_true.2 h
        rw [hb, applyPath_cons_true, applyPath_nil]
        exact S_shift (by rw [iterate_shift]; simpa using h)
      · have hb : bitAt x n = false := bitAt_eq_false.2 h
        rw [hb, applyPath_cons_false, applyPath_nil]
        exact L_shift (by rw [iterate_shift]; simpa using h)
    rw [hstep, ih]

/-- **A prefix is a Möbius map applied to the tail.** This is `toReal₀_applyPath`
with the word made explicit, and it is the only analytic input the rest of the
file needs. -/
theorem toReal₀_eq_mobius_prefixWord (x : Set ℕ) (n : ℕ) (h : shift^[n] x ≠ univ) :
    toReal₀ x = mobius (pathMat (prefixWord x n)) (toReal₀ (shift^[n] x)) := by
  conv_lhs => rw [← applyPath_prefixWord x n]
  exact toReal₀_applyPath _ h

/-! ### Irrational values

Every hypothesis the estimates need — no shift is `∞`, no tail value is `0`, the
path flips infinitely often — is a consequence of irrationality of `Φ₀ x`, so
that is the single standing hypothesis below. -/

theorem nodeValue_replicate_true (n : ℕ) : nodeValue (List.replicate n true) = (n : ℚ) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, nodeValue_true, ih]; push_cast; ring

/-- `Φ₀` is junk at `∞`, and the junk value is `0`: the cut below `univ` is
unbounded, and `Real.sSup` of an unbounded set is `0`. -/
theorem toReal₀_univ : toReal₀ (univ : Set ℕ) = 0 := by
  have hnb : ¬ BddAbove (below (univ : Set ℕ)) := by
    rintro ⟨b, hb⟩
    obtain ⟨n, hn⟩ := exists_nat_gt b
    have hmem : ((n : ℝ)) ∈ below (univ : Set ℕ) :=
      ⟨List.replicate n true, lexLt_univ_of_ne (toSet_ne_univ _), by
        rw [nodeValue_replicate_true]; push_cast; ring⟩
    exact absurd (hb hmem) (not_le.2 hn)
  rw [toReal₀, Real.sSup_def, dif_neg (by tauto)]

theorem not_irrational_of_eq_rat {r : ℝ} {q : ℚ} (h : r = q) : ¬ Irrational r :=
  fun hi => hi ⟨q, h.symm⟩

/-- No shift of an irrational path is `∞`: a path that becomes all `1`s is the
upper representative of a rational. -/
theorem iterate_shift_ne_univ_of_irrational {x : Set ℕ} (h : Irrational (toReal₀ x)) (n : ℕ) :
    shift^[n] x ≠ univ := by
  intro hc
  rcases eq_or_ne x univ with rfl | hx
  · exact not_irrational_of_eq_rat (q := 0) (by rw [toReal₀_univ]; norm_num) h
  · obtain ⟨q, hq⟩ := exists_rat_of_iterate_shift_univ hx hc
    exact not_irrational_of_eq_rat hq h

theorem ne_univ_of_irrational {x : Set ℕ} (h : Irrational (toReal₀ x)) : x ≠ univ :=
  iterate_shift_ne_univ_of_irrational h 0

/-- **Irrationality passes to the tails.** A rational tail would make the whole
value rational, since the prefix acts by an integer Möbius map. -/
theorem irrational_toReal₀_iterate_shift {x : Set ℕ} (h : Irrational (toReal₀ x)) (n : ℕ) :
    Irrational (toReal₀ (shift^[n] x)) := by
  rintro ⟨q, hq⟩
  have hne := iterate_shift_ne_univ_of_irrational h n
  set M := pathMat (prefixWord x n) with hM
  obtain ⟨-, -, hc, hd⟩ := pathMat_entries (prefixWord x n)
  have hq0 : (0 : ℚ) ≤ q := by
    have := toReal₀_nonneg (shift^[n] x)
    rw [← hq] at this
    exact_mod_cast this
  have hden : (M.2.2.1 : ℚ) * q + (M.2.2.2 : ℚ) ≠ 0 := by
    have h1 : (0 : ℚ) ≤ (M.2.2.1 : ℚ) := by exact_mod_cast hc
    have h2 : (0 : ℚ) < (M.2.2.2 : ℚ) := by exact_mod_cast hd
    nlinarith
  refine h ⟨((M.1 : ℚ) * q + (M.2.1 : ℚ)) / ((M.2.2.1 : ℚ) * q + (M.2.2.2 : ℚ)), ?_⟩
  rw [toReal₀_eq_mobius_prefixWord x n hne, ← hq, mobius, ← hM]
  push_cast
  ring

theorem toReal₀_pos_of_irrational {y : Set ℕ} (h : Irrational (toReal₀ y)) : 0 < toReal₀ y := by
  rcases (toReal₀_nonneg y).lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd h (not_irrational_of_eq_rat (q := 0) (by rw [← heq]; norm_num))

/-! ### Run boundaries

The partial quotients are the run lengths, so the data to extract from `x` is the
increasing sequence of positions where the bit flips. It is infinite exactly when
`x` is irrational (`eventuallyConstant_iff_rat`), which is why the irrational case
is the one with a full sequence of convergents. -/

/-- The path of `x` flips infinitely often. -/
def InfFlips (x : Set ℕ) : Prop := ∀ n : ℕ, ∃ m, n < m ∧ bitAt x m ≠ bitAt x n

/-- **The run sequence is infinite exactly for the irrationals.** A path that
stops flipping is eventually constant, hence rational. -/
theorem infFlips_of_irrational {x : Set ℕ} (h : Irrational (toReal₀ x)) : InfFlips x := by
  intro n
  by_contra hc
  have hc' : ∀ m, n < m → bitAt x m = bitAt x n := fun m hm => by
    by_contra hne; exact hc ⟨m, hm, hne⟩
  have hconst : EventuallyConstant x := by
    refine ⟨n, ?_⟩
    by_cases hn : n ∈ x
    · refine Or.inr fun m hm => ?_
      rcases eq_or_lt_of_le hm with rfl | hlt
      · exact hn
      · exact bitAt_eq_true.1 (by rw [hc' m hlt]; exact bitAt_eq_true.2 hn)
    · refine Or.inl fun m hm => ?_
      rcases eq_or_lt_of_le hm with rfl | hlt
      · exact hn
      · exact bitAt_eq_false.1 (by rw [hc' m hlt]; exact bitAt_eq_false.2 hn)
  obtain ⟨q, hq⟩ := (eventuallyConstant_iff_rat (ne_univ_of_irrational h)).1 hconst
  exact not_irrational_of_eq_rat hq h

/-- The next position after `n` at which the bit differs from the bit at `n`. -/
noncomputable def nextFlip (x : Set ℕ) (n : ℕ) : ℕ := sInf {m | n < m ∧ bitAt x m ≠ bitAt x n}

theorem nextFlip_spec {x : Set ℕ} (h : InfFlips x) (n : ℕ) :
    n < nextFlip x n ∧ bitAt x (nextFlip x n) ≠ bitAt x n :=
  Nat.sInf_mem (h n)

theorem lt_nextFlip {x : Set ℕ} (h : InfFlips x) (n : ℕ) : n < nextFlip x n :=
  (nextFlip_spec h n).1

/-- **The run is constant.** Everything strictly before the next flip repeats the
bit at `n`; this is minimality of `sInf`, and it is what makes the segment word a
`List.replicate`. -/
theorem bitAt_eq_of_lt_nextFlip {x : Set ℕ} {n j : ℕ} (h1 : n ≤ j) (h2 : j < nextFlip x n) :
    bitAt x j = bitAt x n := by
  rcases eq_or_lt_of_le h1 with rfl | hlt
  · rfl
  · by_contra hne
    exact Nat.notMem_of_lt_sInf h2 ⟨hlt, hne⟩

/-- The `k`-th run boundary: the prefix length at which run `k` starts. -/
noncomputable def runBoundary (x : Set ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => nextFlip x (runBoundary x k)

@[simp] theorem runBoundary_zero (x : Set ℕ) : runBoundary x 0 = 0 := rfl

theorem runBoundary_succ (x : Set ℕ) (k : ℕ) :
    runBoundary x (k + 1) = nextFlip x (runBoundary x k) := rfl

/-- The `k`-th **partial quotient**: the length of run `k`. -/
noncomputable def partialQuot (x : Set ℕ) (k : ℕ) : ℕ :=
  runBoundary x (k + 1) - runBoundary x k

theorem runBoundary_lt_succ {x : Set ℕ} (h : InfFlips x) (k : ℕ) :
    runBoundary x k < runBoundary x (k + 1) := lt_nextFlip h _

theorem partialQuot_pos {x : Set ℕ} (h : InfFlips x) (k : ℕ) : 0 < partialQuot x k :=
  Nat.sub_pos_of_lt (runBoundary_lt_succ h k)

theorem runBoundary_succ_eq {x : Set ℕ} (h : InfFlips x) (k : ℕ) :
    runBoundary x (k + 1) = runBoundary x k + partialQuot x k :=
  (Nat.add_sub_cancel' (runBoundary_lt_succ h k).le).symm

/-- The bit of run `k`. -/
noncomputable def runBit (x : Set ℕ) (k : ℕ) : Bool := bitAt x (runBoundary x k)

/-- **Runs alternate.** By construction the bit at a boundary differs from the
bit at the previous one, and there are only two bits. -/
theorem runBit_succ {x : Set ℕ} (h : InfFlips x) (k : ℕ) :
    runBit x (k + 1) = !(runBit x k) := by
  have := (nextFlip_spec h (runBoundary x k)).2
  simp only [runBit, runBoundary_succ]
  revert this
  cases bitAt x (nextFlip x (runBoundary x k)) <;> cases bitAt x (runBoundary x k) <;> simp

/-! ### The word of a run -/

theorem prefixWord_add {x : Set ℕ} {n a : ℕ} {b : Bool}
    (hb : ∀ j, n ≤ j → j < n + a → bitAt x j = b) :
    prefixWord x (n + a) = prefixWord x n ++ List.replicate a b := by
  induction a with
  | zero => simp
  | succ a ih =>
    have ih' := ih fun j h1 h2 => hb j h1 (by omega)
    rw [show n + (a + 1) = (n + a) + 1 from rfl, prefixWord_succ, ih',
      hb (n + a) (by omega) (by omega), List.append_assoc, ← List.replicate_succ']

/-- **The prefix at a run boundary extends by a whole run.** -/
theorem prefixWord_runBoundary_succ {x : Set ℕ} (h : InfFlips x) (k : ℕ) :
    prefixWord x (runBoundary x (k + 1))
      = prefixWord x (runBoundary x k) ++ List.replicate (partialQuot x k) (runBit x k) := by
  rw [runBoundary_succ_eq h k]
  refine prefixWord_add fun j h1 h2 => ?_
  refine bitAt_eq_of_lt_nextFlip h1 ?_
  rw [← runBoundary_succ, runBoundary_succ_eq h k]
  exact h2

/-! ### The continuants

`contin x k = (pₖ, qₖ)`. The seeds are `(0,1)` and `(1,0)` — the classical
`p₋₁/q₋₁ = 1/0` and `p₀/q₀` — **swapped** when the path starts with a left move.
The swap is exactly the classical `a₀ = 0`: for `x < 1` the tree stores no leading
`R`-run, so the sequence starts one step further along. With it, one recurrence
serves both cases. -/

/-- The continuants `(pₖ, qₖ)`, by the recurrence `cₖ₊₂ = aₖ cₖ₊₁ + cₖ`. -/
noncomputable def contin (x : Set ℕ) : ℕ → ℤ × ℤ
  | 0 => if runBit x 0 then (0, 1) else (1, 0)
  | 1 => if runBit x 0 then (1, 0) else (0, 1)
  | k + 2 => ((partialQuot x k : ℤ) * (contin x (k + 1)).1 + (contin x k).1,
              (partialQuot x k : ℤ) * (contin x (k + 1)).2 + (contin x k).2)

theorem contin_zero (x : Set ℕ) : contin x 0 = if runBit x 0 then (0, 1) else (1, 0) := rfl

theorem contin_one (x : Set ℕ) : contin x 1 = if runBit x 0 then (1, 0) else (0, 1) := rfl

theorem contin_add_two (x : Set ℕ) (k : ℕ) :
    contin x (k + 2) = ((partialQuot x k : ℤ) * (contin x (k + 1)).1 + (contin x k).1,
              (partialQuot x k : ℤ) * (contin x (k + 1)).2 + (contin x k).2) := rfl

/-- **The recurrence for the denominators**, `qₖ₊₂ = aₖ qₖ₊₁ + qₖ`. -/
theorem contin_den_add_two (x : Set ℕ) (k : ℕ) :
    (contin x (k + 2)).2 = (partialQuot x k : ℤ) * (contin x (k + 1)).2 + (contin x k).2 := rfl

/-- **The recurrence for the numerators**, `pₖ₊₂ = aₖ pₖ₊₁ + pₖ`. -/
theorem contin_num_add_two (x : Set ℕ) (k : ℕ) :
    (contin x (k + 2)).1 = (partialQuot x k : ℤ) * (contin x (k + 1)).1 + (contin x k).1 := rfl

theorem contin_den_nonneg (x : Set ℕ) (k : ℕ) : 0 ≤ (contin x k).2 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => by_cases hb : runBit x 0 <;> simp [contin, hb]
    | 1 => by_cases hb : runBit x 0 <;> simp [contin, hb]
    | (j + 2) =>
      have h1 := ih (j + 1) (by omega)
      have h2 := ih j (by omega)
      rw [contin_den_add_two]
      positivity

theorem contin_num_nonneg (x : Set ℕ) (k : ℕ) : 0 ≤ (contin x k).1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => by_cases hb : runBit x 0 <;> simp [contin, hb]
    | 1 => by_cases hb : runBit x 0 <;> simp [contin, hb]
    | (j + 2) =>
      have h1 := ih (j + 1) (by omega)
      have h2 := ih j (by omega)
      rw [contin_num_add_two]
      positivity

/-- **The denominators are positive from index 2 on.** Index `1` is the seed
`1/0`, whose denominator is `0`; that is the only exception, and it is why every
estimate below starts at `k = 2`. -/
theorem contin_den_pos {x : Set ℕ} (h : InfFlips x) (k : ℕ) : 0 < (contin x (k + 2)).2 := by
  induction k with
  | zero =>
    have ha : 0 < partialQuot x 0 := partialQuot_pos h 0
    have ha' : (1 : ℤ) ≤ (partialQuot x 0 : ℤ) := by exact_mod_cast ha
    rw [contin_den_add_two]
    cases hb : runBit x 0 <;> simp [contin_zero, contin_one, hb, ha]
  | succ j ih =>
    have ha : 0 < partialQuot x (j + 1) := partialQuot_pos h (j + 1)
    have ha' : (1 : ℤ) ≤ (partialQuot x (j + 1) : ℤ) := by exact_mod_cast ha
    have hn := contin_den_nonneg x (j + 1)
    rw [contin_den_add_two]
    nlinarith

/-- **`qₖ ≤ qₖ₊₁`.** This is the estimate that fails for prefixes in the middle
of a run — `L^n` has denominator pair `(n, 1)` — and holds here because a partial
quotient is at least `1`. -/
theorem contin_den_le_succ {x : Set ℕ} (h : InfFlips x) (k : ℕ) :
    (contin x (k + 1)).2 ≤ (contin x (k + 2)).2 := by
  have ha : (1 : ℤ) ≤ (partialQuot x k : ℤ) := by exact_mod_cast partialQuot_pos h k
  have h1 := contin_den_nonneg x k
  have h2 := contin_den_nonneg x (k + 1)
  rw [contin_den_add_two]
  nlinarith

/-! ### The prefix matrix at a run boundary -/

/-- The Möbius matrix of the prefix ending at run boundary `k`. -/
noncomputable def boundaryMat (x : Set ℕ) (k : ℕ) : ℤ × ℤ × ℤ × ℤ :=
  pathMat (prefixWord x (runBoundary x k))

@[simp] theorem boundaryMat_zero (x : Set ℕ) : boundaryMat x 0 = (1, 0, 0, 1) := by
  simp [boundaryMat]

/-- A right run multiplies on the right by the shear `t ↦ t + aₖ`. -/
theorem boundaryMat_succ_true {x : Set ℕ} (h : InfFlips x) {k : ℕ} (hb : runBit x k = true) :
    boundaryMat x (k + 1) = matMul (boundaryMat x k) (1, (partialQuot x k : ℤ), 0, 1) := by
  rw [boundaryMat, boundaryMat, prefixWord_runBoundary_succ h k, pathMat_append, hb,
    pathMat_replicate_true]

/-- A left run multiplies on the right by `t ↦ t / (aₖ t + 1)`. -/
theorem boundaryMat_succ_false {x : Set ℕ} (h : InfFlips x) {k : ℕ} (hb : runBit x k = false) :
    boundaryMat x (k + 1) = matMul (boundaryMat x k) (1, 0, (partialQuot x k : ℤ), 1) := by
  rw [boundaryMat, boundaryMat, prefixWord_runBoundary_succ h k, pathMat_append, hb,
    pathMat_replicate_false]

/-- **The convergents are the columns of the prefix matrix at a run boundary.**

At boundary `k+1` the two columns of the matrix are `contin x (k+1)` and
`contin x (k+2)` — consecutive convergents. Which of the two is the newer one
alternates with the run's bit, because a right run adds a multiple of the first
column to the second and a left run does the reverse. Unfolding the induction
step of this statement *is* the recurrence `pₖ₊₂ = aₖ pₖ₊₁ + pₖ`.

For a prefix in the middle of a run the same computation produces a column that
is an intermediate mediant rather than a convergent, which is why nothing below
is stated for arbitrary prefixes. -/
theorem boundaryMat_eq_contin {x : Set ℕ} (h : InfFlips x) (k : ℕ) :
    (runBit x k = true →
        boundaryMat x (k + 1) = ((contin x (k + 1)).1, (contin x (k + 2)).1,
                                 (contin x (k + 1)).2, (contin x (k + 2)).2)) ∧
    (runBit x k = false →
        boundaryMat x (k + 1) = ((contin x (k + 2)).1, (contin x (k + 1)).1,
                                 (contin x (k + 2)).2, (contin x (k + 1)).2)) := by
  induction k with
  | zero =>
    constructor
    · intro hb
      rw [boundaryMat_succ_true h hb, boundaryMat_zero]
      simp [matMul, contin_add_two, contin_zero, contin_one, hb]
    · intro hb
      rw [boundaryMat_succ_false h hb, boundaryMat_zero]
      simp [matMul, contin_add_two, contin_zero, contin_one, hb]
  | succ j ih =>
    have hrec1 : (contin x (j + 3)).1
        = (partialQuot x (j + 1) : ℤ) * (contin x (j + 2)).1 + (contin x (j + 1)).1 :=
      contin_num_add_two x (j + 1)
    have hrec2 : (contin x (j + 3)).2
        = (partialQuot x (j + 1) : ℤ) * (contin x (j + 2)).2 + (contin x (j + 1)).2 :=
      contin_den_add_two x (j + 1)
    have halt := runBit_succ h j
    show (runBit x (j + 1) = true →
            boundaryMat x (j + 2) = ((contin x (j + 2)).1, (contin x (j + 3)).1,
                                     (contin x (j + 2)).2, (contin x (j + 3)).2)) ∧
         (runBit x (j + 1) = false →
            boundaryMat x (j + 2) = ((contin x (j + 3)).1, (contin x (j + 2)).1,
                                     (contin x (j + 3)).2, (contin x (j + 2)).2))
    cases hb : runBit x j
    · have hb1 : runBit x (j + 1) = true := by rw [halt, hb]; rfl
      refine ⟨fun _ => ?_, fun hc => absurd (hb1.symm.trans hc) (by simp)⟩
      rw [show j + 2 = (j + 1) + 1 from rfl, boundaryMat_succ_true h hb1, ih.2 hb, hrec1, hrec2]
      simp only [matMul, Prod.mk.injEq]
      and_intros <;> first | trivial | ring
    · have hb1 : runBit x (j + 1) = false := by rw [halt, hb]; rfl
      refine ⟨fun hc => absurd (hb1.symm.trans hc) (by simp), fun _ => ?_⟩
      rw [show j + 2 = (j + 1) + 1 from rfl, boundaryMat_succ_false h hb1, ih.1 hb, hrec1, hrec2]
      simp only [matMul, Prod.mk.injEq]
      and_intros <;> first | trivial | ring

/-! ### The two estimates

Everything analytic is in one algebraic identity. With `t = (A s + B)/(C s + D)`
and `A D − B C = 1`,

  `t − B/D = s / (D (C s + D))`,   `A/C − t = 1 / (C (C s + D))`,

so `t` sits strictly between the two column fractions and the gap between them is
`1/(C D)`. Both estimates are that one computation read twice. -/

/-- **The exact error of the two column fractions.** The estimates below only use
the resulting inequalities, but the equalities themselves are what Hurwitz's
argument needs, so they are stated and kept. -/
theorem column_errors {A B C D s t : ℝ} (hC : 0 < C) (hD : 0 < D) (hs : 0 < s)
    (hdet : A * D - B * C = 1) (ht : t = (A * s + B) / (C * s + D)) :
    t - B / D = s / (D * (C * s + D)) ∧ A / C - t = 1 / (C * (C * s + D)) := by
  have hden : (0 : ℝ) < C * s + D := by positivity
  constructor
  · rw [ht, div_sub_div _ _ (ne_of_gt hden) (ne_of_gt hD),
      div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (s * D * (C * s + D)) * hdet
  · rw [ht, div_sub_div _ _ (ne_of_gt hC) (ne_of_gt hden),
      div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (C * (C * s + D)) * hdet

/-- **Both columns of a prefix matrix approximate `Φ₀ x` to within `1/(C D)`.**

This holds for *every* prefix, run boundary or not — the content of the run
decomposition is not this inequality but the fact that at a boundary `C` and `D`
are consecutive *convergent* denominators, so that the bound is the classical
`1/(qₖ qₖ₊₁)`. -/
theorem abs_sub_columns_lt {x : Set ℕ} (hirr : Irrational (toReal₀ x)) {n : ℕ}
    {A B C D : ℤ} (hm : pathMat (prefixWord x n) = (A, B, C, D)) (hC : 0 < C) :
    |toReal₀ x - (B : ℝ) / (D : ℝ)| < 1 / ((C : ℝ) * (D : ℝ)) ∧
      |toReal₀ x - (A : ℝ) / (C : ℝ)| < 1 / ((C : ℝ) * (D : ℝ)) := by
  set s := toReal₀ (shift^[n] x) with hsdef
  have hne := iterate_shift_ne_univ_of_irrational hirr n
  have hs : 0 < s := toReal₀_pos_of_irrational (irrational_toReal₀_iterate_shift hirr n)
  have hDz : 0 < D := by
    have := (pathMat_entries (prefixWord x n)).2.2.2
    rwa [hm] at this
  have hdet : A * D - B * C = 1 := by
    have := pathMat_det (prefixWord x n)
    rwa [hm] at this
  have hCr : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  have hDr : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDz
  have hdetr : (A : ℝ) * (D : ℝ) - (B : ℝ) * (C : ℝ) = 1 := by exact_mod_cast hdet
  have ht : toReal₀ x = ((A : ℝ) * s + (B : ℝ)) / ((C : ℝ) * s + (D : ℝ)) := by
    rw [toReal₀_eq_mobius_prefixWord x n hne, hm, mobius]
  obtain ⟨hlow, hhigh⟩ := column_errors hCr hDr hs hdetr ht
  have hden : (0 : ℝ) < (C : ℝ) * s + (D : ℝ) := by positivity
  constructor
  · rw [abs_of_pos (by rw [hlow]; positivity), hlow, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · rw [abs_sub_comm, abs_of_pos (by rw [hhigh]; positivity), hhigh,
      div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (mul_pos hCr hCr) hs]

/-- **The convergent estimate:** `|Φ₀ x − pₖ/qₖ| < 1/(qₖ qₖ₊₁)`.

Indexed from `2`, where the continuants stop being seeds. The proof reads the
prefix matrix at run boundary `k+2`: its two columns are `contin x (k+2)` and
`contin x (k+3)`, and `Φ₀ x` lies between the two fractions they name. -/
theorem abs_sub_contin_lt {x : Set ℕ} (hirr : Irrational (toReal₀ x)) (k : ℕ) :
    |toReal₀ x - ((contin x (k + 2)).1 : ℝ) / ((contin x (k + 2)).2 : ℝ)|
      < 1 / (((contin x (k + 2)).2 : ℝ) * ((contin x (k + 3)).2 : ℝ)) := by
  have h := infFlips_of_irrational hirr
  have hq : 0 < (contin x (k + 2)).2 := contin_den_pos h k
  have hq' : 0 < (contin x (k + 3)).2 := contin_den_pos h (k + 1)
  obtain ⟨hT, hF⟩ := boundaryMat_eq_contin h (k + 1)
  cases hb : runBit x (k + 1)
  · have hm : pathMat (prefixWord x (runBoundary x (k + 2)))
        = ((contin x (k + 3)).1, (contin x (k + 2)).1,
           (contin x (k + 3)).2, (contin x (k + 2)).2) := hF hb
    have := (abs_sub_columns_lt hirr hm hq').1
    rwa [mul_comm ((contin x (k + 3)).2 : ℝ)] at this
  · have hm : pathMat (prefixWord x (runBoundary x (k + 2)))
        = ((contin x (k + 2)).1, (contin x (k + 3)).1,
           (contin x (k + 2)).2, (contin x (k + 3)).2) := hT hb
    exact (abs_sub_columns_lt hirr hm hq).2

/-- **The `1/q²` form.** Immediate from the estimate and `qₖ ≤ qₖ₊₁`; recorded
because it is the shape the classical approximation theorems are stated in. -/
theorem abs_sub_contin_lt_one_div_sq {x : Set ℕ} (hirr : Irrational (toReal₀ x)) (k : ℕ) :
    |toReal₀ x - ((contin x (k + 2)).1 : ℝ) / ((contin x (k + 2)).2 : ℝ)|
      < 1 / ((contin x (k + 2)).2 : ℝ) ^ 2 := by
  have h := infFlips_of_irrational hirr
  have hq : 0 < (contin x (k + 2)).2 := contin_den_pos h k
  have hqr : (0 : ℝ) < ((contin x (k + 2)).2 : ℝ) := by exact_mod_cast hq
  have hmono : ((contin x (k + 2)).2 : ℝ) ≤ ((contin x (k + 3)).2 : ℝ) := by
    exact_mod_cast contin_den_le_succ h (k + 1)
  refine lt_of_lt_of_le (abs_sub_contin_lt hirr k) ?_
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

/-! ### The complete quotients

The estimate `1/(qₖ qₖ₊₁)` is not sharp; the sharp statement replaces `qₖ₊₁` by
`qₖ wₖ + qₖ₊₁`, where `wₖ` is the tail of the continued fraction read from run
`k` on. Two facts about `wₖ` carry the whole of Hurwitz:

* `inv_tailQuot` : `1/wⱼ = aⱼ + wⱼ₊₁` — so `wⱼ = [0; aⱼ, aⱼ₊₁, …]`;
* `denRatio_succ` : `ρⱼ₊₁ = aⱼ + 1/ρⱼ` for `ρⱼ = qⱼ₊₁/qⱼ`.

The two recurrences share the same `aⱼ`, which is why `λⱼ = wⱼ + ρⱼ` satisfies
`λⱼ₊₁ = 1/wⱼ + 1/ρⱼ`. That single relation is Hurwitz's lemma. -/

theorem bitAt_iterate_shift (x : Set ℕ) (n i : ℕ) : bitAt (shift^[n] x) i = bitAt x (i + n) := by
  by_cases hm : i + n ∈ x
  · rw [bitAt_eq_true.2 (by rw [iterate_shift]; exact hm), bitAt_eq_true.2 hm]
  · rw [bitAt_eq_false.2 (by rw [iterate_shift]; exact hm), bitAt_eq_false.2 hm]

/-- The value of the path from run boundary `j` on. -/
noncomputable def tailValue (x : Set ℕ) (j : ℕ) : ℝ := toReal₀ (shift^[runBoundary x j] x)

/-- **One run at a time.** The path at boundary `j` is the run put back on top of
the path at boundary `j+1`. -/
theorem shift_runBoundary_succ {x : Set ℕ} (h : InfFlips x) (j : ℕ) :
    shift^[runBoundary x j] x
      = applyPath (List.replicate (partialQuot x j) (runBit x j))
          (shift^[runBoundary x (j + 1)] x) := by
  set n := runBoundary x j with hn
  set a := partialQuot x j with ha
  have hbits : ∀ i, 0 ≤ i → i < 0 + a → bitAt (shift^[n] x) i = runBit x j := by
    intro i _ hi
    rw [bitAt_iterate_shift]
    refine bitAt_eq_of_lt_nextFlip (Nat.le_add_left _ _) ?_
    rw [← runBoundary_succ, runBoundary_succ_eq h j, ← hn, ← ha]
    omega
  have hw : prefixWord (shift^[n] x) a = List.replicate a (runBit x j) := by
    have := prefixWord_add (x := shift^[n] x) (n := 0) (a := a) (b := runBit x j) hbits
    simpa using this
  have hback := applyPath_prefixWord (shift^[n] x) a
  rw [hw] at hback
  rw [← hback, ← Function.iterate_add_apply, runBoundary_succ_eq h j, ← hn, ← ha, Nat.add_comm]

theorem tailValue_succ_true {x : Set ℕ} (h : InfFlips x) {j : ℕ} (hb : runBit x j = true)
    (hne : shift^[runBoundary x (j + 1)] x ≠ univ) :
    tailValue x j = tailValue x (j + 1) + (partialQuot x j : ℝ) := by
  rw [tailValue, tailValue, shift_runBoundary_succ h j, hb]
  rw [toReal₀_applyPath _ hne, pathMat_replicate_true, mobius]
  have hd : ((0 : ℤ) : ℝ) * toReal₀ (shift^[runBoundary x (j + 1)] x) + ((1 : ℤ) : ℝ) = 1 := by
    push_cast; ring
  rw [hd, div_one]
  push_cast
  ring

theorem tailValue_succ_false {x : Set ℕ} (h : InfFlips x) {j : ℕ} (hb : runBit x j = false)
    (hne : shift^[runBoundary x (j + 1)] x ≠ univ) :
    tailValue x j
      = tailValue x (j + 1) / ((partialQuot x j : ℝ) * tailValue x (j + 1) + 1) := by
  rw [tailValue, tailValue, shift_runBoundary_succ h j, hb]
  rw [toReal₀_applyPath _ hne, pathMat_replicate_false, mobius]
  push_cast
  ring_nf

/-- The `j`-th **complete quotient**, normalised to `(0,1)`: the value
`[0; aⱼ, aⱼ₊₁, …]`. The `if` is the alternation of the two moves — the tree
stores `1/t` on left runs and `t` on right runs. -/
noncomputable def tailQuot (x : Set ℕ) (j : ℕ) : ℝ :=
  if runBit x j then (tailValue x j)⁻¹ else tailValue x j

theorem tailValue_pos {x : Set ℕ} (hirr : Irrational (toReal₀ x)) (j : ℕ) :
    0 < tailValue x j :=
  toReal₀_pos_of_irrational (irrational_toReal₀_iterate_shift hirr _)

theorem tailQuot_pos {x : Set ℕ} (hirr : Irrational (toReal₀ x)) (j : ℕ) : 0 < tailQuot x j := by
  rw [tailQuot]
  cases hb : runBit x j
  · simpa using tailValue_pos hirr j
  · simpa using tailValue_pos hirr j

/-- **`1/wⱼ = aⱼ + wⱼ₊₁`.** Both moves give the same recurrence, which is the
point of the normalisation in `tailQuot`: on a right run the tree stores `t` and
the recurrence is `t ↦ t + a`, on a left run it stores `1/t` and the recurrence
is `1/t ↦ 1/t + a`. -/
theorem inv_tailQuot {x : Set ℕ} (hirr : Irrational (toReal₀ x)) (j : ℕ) :
    (tailQuot x j)⁻¹ = (partialQuot x j : ℝ) + tailQuot x (j + 1) := by
  have h := infFlips_of_irrational hirr
  have hne : shift^[runBoundary x (j + 1)] x ≠ univ :=
    iterate_shift_ne_univ_of_irrational hirr _
  have hpos := tailValue_pos hirr (j + 1)
  have halt := runBit_succ h j
  cases hb : runBit x j
  · -- left run: the tree stores the value itself, and `1/s` picks up `a`
    have hb1 : runBit x (j + 1) = true := by rw [halt, hb]; rfl
    rw [tailQuot, tailQuot, hb, hb1, if_neg (by simp), if_pos rfl,
      tailValue_succ_false h hb hne]
    rw [inv_div]
    field_simp
  · have hb1 : runBit x (j + 1) = false := by rw [halt, hb]; rfl
    rw [tailQuot, tailQuot, hb, hb1, if_pos rfl, if_neg (by simp),
      tailValue_succ_true h hb hne]
    rw [inv_inv]
    ring

/-- `0 < wⱼ < 1`: a partial quotient is at least `1` and the next tail is
positive. -/
theorem tailQuot_lt_one {x : Set ℕ} (hirr : Irrational (toReal₀ x)) (j : ℕ) :
    tailQuot x j < 1 := by
  have h := infFlips_of_irrational hirr
  have hinv := inv_tailQuot hirr j
  have hpos := tailQuot_pos hirr j
  have hpos' := tailQuot_pos hirr (j + 1)
  have ha : (1 : ℝ) ≤ (partialQuot x j : ℝ) := by exact_mod_cast partialQuot_pos h j
  have hlt : (1 : ℝ) < (tailQuot x j)⁻¹ := by rw [hinv]; linarith
  have hkey : tailQuot x j * (tailQuot x j)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
  nlinarith [mul_pos hpos (sub_pos.2 hlt)]

/-- The ratio `ρⱼ = qⱼ₊₁/qⱼ` of consecutive convergent denominators. -/
noncomputable def denRatio (x : Set ℕ) (j : ℕ) : ℝ :=
  ((contin x (j + 1)).2 : ℝ) / ((contin x j).2 : ℝ)

theorem one_le_denRatio {x : Set ℕ} (h : InfFlips x) (k : ℕ) : 1 ≤ denRatio x (k + 2) := by
  have h1 : (0 : ℝ) < ((contin x (k + 2)).2 : ℝ) := by exact_mod_cast contin_den_pos h k
  have h2 : ((contin x (k + 2)).2 : ℝ) ≤ ((contin x (k + 3)).2 : ℝ) := by
    exact_mod_cast contin_den_le_succ h (k + 1)
  rw [denRatio, le_div_iff₀ h1, one_mul]
  exact h2

/-- **`ρⱼ₊₁ = aⱼ + 1/ρⱼ`** — the denominator recurrence, read as a ratio. It
carries the *same* `aⱼ` as `inv_tailQuot`, which is the whole of Hurwitz's
lemma. -/
theorem denRatio_succ {x : Set ℕ} (h : InfFlips x) (k : ℕ) :
    denRatio x (k + 3) = (partialQuot x (k + 2) : ℝ) + (denRatio x (k + 2))⁻¹ := by
  have h1 : (0 : ℝ) < ((contin x (k + 2)).2 : ℝ) := by exact_mod_cast contin_den_pos h k
  have h2 : (0 : ℝ) < ((contin x (k + 3)).2 : ℝ) := by exact_mod_cast contin_den_pos h (k + 1)
  have hrec : ((contin x (k + 4)).2 : ℝ)
      = (partialQuot x (k + 2) : ℝ) * ((contin x (k + 3)).2 : ℝ) + ((contin x (k + 2)).2 : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (contin_den_add_two x (k + 2))
  rw [denRatio, denRatio, hrec, inv_div]
  field_simp
  try ring

/-! ### The sharp error

`|Φ₀ x − pⱼ/qⱼ| = 1/(qⱼ (qⱼ wⱼ + qⱼ₊₁))`. Dividing through by `qⱼ²`, the
approximation quality of the `j`-th convergent is governed by the single real
number `wⱼ + ρⱼ`. -/

/-- **The exact error of a convergent.** -/
theorem abs_sub_contin_eq {x : Set ℕ} (hirr : Irrational (toReal₀ x)) (k : ℕ) :
    |toReal₀ x - ((contin x (k + 2)).1 : ℝ) / ((contin x (k + 2)).2 : ℝ)|
      = 1 / (((contin x (k + 2)).2 : ℝ)
          * (((contin x (k + 2)).2 : ℝ) * tailQuot x (k + 2) + ((contin x (k + 3)).2 : ℝ))) := by
  have h := infFlips_of_irrational hirr
  have hq : (0 : ℝ) < ((contin x (k + 2)).2 : ℝ) := by exact_mod_cast contin_den_pos h k
  have hq' : (0 : ℝ) < ((contin x (k + 3)).2 : ℝ) := by exact_mod_cast contin_den_pos h (k + 1)
  have hne := iterate_shift_ne_univ_of_irrational hirr (runBoundary x (k + 2))
  have hs : 0 < tailValue x (k + 2) := tailValue_pos hirr (k + 2)
  have halt := runBit_succ h (k + 1)
  obtain ⟨hT, hF⟩ := boundaryMat_eq_contin h (k + 1)
  cases hb : runBit x (k + 1)
  · -- the newer column is the first one; `wⱼ = 1/sⱼ`
    have hb1 : runBit x (k + 2) = true := by rw [halt, hb]; rfl
    have hm : pathMat (prefixWord x (runBoundary x (k + 2)))
        = ((contin x (k + 3)).1, (contin x (k + 2)).1,
           (contin x (k + 3)).2, (contin x (k + 2)).2) := hF hb
    obtain ⟨hlow, -⟩ := column_errors (A := ((contin x (k + 3)).1 : ℝ))
      (B := ((contin x (k + 2)).1 : ℝ)) (C := ((contin x (k + 3)).2 : ℝ))
      (D := ((contin x (k + 2)).2 : ℝ)) (s := tailValue x (k + 2)) (t := toReal₀ x) hq' hq hs
      (by
        have := pathMat_det (prefixWord x (runBoundary x (k + 2)))
        rw [hm] at this
        exact_mod_cast this)
      (by
        rw [tailValue, toReal₀_eq_mobius_prefixWord x (runBoundary x (k + 2)) hne, hm, mobius])
    rw [abs_of_pos (by rw [hlow]; positivity), hlow, tailQuot, hb1, if_pos rfl, tailValue]
    rw [tailValue] at hs
    field_simp
    ring
  · -- the newer column is the second one; `wⱼ = sⱼ`
    have hb1 : runBit x (k + 2) = false := by rw [halt, hb]; rfl
    have hm : pathMat (prefixWord x (runBoundary x (k + 2)))
        = ((contin x (k + 2)).1, (contin x (k + 3)).1,
           (contin x (k + 2)).2, (contin x (k + 3)).2) := hT hb
    obtain ⟨-, hhigh⟩ := column_errors (A := ((contin x (k + 2)).1 : ℝ))
      (B := ((contin x (k + 3)).1 : ℝ)) (C := ((contin x (k + 2)).2 : ℝ))
      (D := ((contin x (k + 3)).2 : ℝ)) (s := tailValue x (k + 2)) (t := toReal₀ x) hq hq' hs
      (by
        have := pathMat_det (prefixWord x (runBoundary x (k + 2)))
        rw [hm] at this
        exact_mod_cast this)
      (by
        rw [tailValue, toReal₀_eq_mobius_prefixWord x (runBoundary x (k + 2)) hne, hm, mobius])
    rw [abs_sub_comm, abs_of_pos (by rw [hhigh]; positivity), hhigh, tailQuot, hb1,
      if_neg (by simp), tailValue]

end SternBrocot
