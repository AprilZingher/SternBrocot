/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Order
import SternBrocot.Node
import SternBrocot.Enumeration
import SternBrocot.PathOrder
import SternBrocot.Bridge
import SternBrocot.ToReal
import SternBrocot.SignedToReal
import SternBrocot.Lagrange
import SternBrocot.Convergent
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Sanity checks

Machine-checked confirmation that the definitions in this development really do
encode the intended object. These are the concrete claims made when the
construction was described; if any of them failed, a definition would be wrong.
-/

open Set
open scoped symmDiff

namespace SternBrocot

/-! ### The naturals sit inside as von Neumann ordinals -/

example : S ∅ = ({0} : Set ℕ) := by
  ext n
  match n with
  | 0 => simp
  | (k + 1) => simp

/-- `2 = {0, 1}`: the successor really is the usual von Neumann successor. -/
theorem two_eq_pair : S (S ∅) = ({0, 1} : Set ℕ) := by
  ext n
  match n with
  | 0 => simp
  | 1 => simp
  | (k + 2) => simp

/-! ### The tail rule

"`2` is equivalent to the set containing all natural numbers EXCEPT `1`, and
this equivalence holds down the tree." -/

/-- `ω \ {1}` written as a prefix plus a full tail. -/
theorem compl_singleton_one : ({n : ℕ | n ≠ 1}) = ({0} ∪ Ioi 1 : Set ℕ) := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioi]
  omega

/-- **The stated example, verified**: `2 = {0,1}` and `ω \ {1}` are a tail pair,
i.e. two representations of the same point. -/
theorem two_tailPair : TailPair ({0, 1} : Set ℕ) {n : ℕ | n ≠ 1} := by
  refine ⟨1, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp
  · simp
  · intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · simp
  · intro k hk
    simp only [Set.mem_setOf_eq]
    omega

/-- The same fact, seen through the key lemma: the two representations of `2`
are adjacent in the lex order, with `ω \ {1}` immediately below `{0,1}`. -/
example : IsAdjacent ({n : ℕ | n ≠ 1}) ({0, 1} : Set ℕ) :=
  isAdjacent_of_tailPair two_tailPair

/-! ### Reciprocal is complement -/

/-- `1/2` is the complement of `2`. -/
example : recip ({0, 1} : Set ℕ) = Ioi 1 := by
  ext n
  simp only [recip, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_Ioi]
  omega

/-! ### Rigidity, on the nose

Only two masks work. Anything else — even a single stray point — breaks the
quotient. -/

/-- `x ↦ x ∆ {0}` does **not** descend: the Boolean structure has no room for a
third operation. -/
example : ¬ Descends (· ∆ ({0} : Set ℕ)) := by
  intro h
  rcases (rigidity _).mp h with h0 | h0
  · have h1 : (0 : ℕ) ∈ ({0} : Set ℕ) := rfl
    rw [h0] at h1
    exact h1
  · have : (1 : ℕ) ∈ ({0} : Set ℕ) := h0 ▸ mem_univ 1
    simp at this

/-- Not even a cofinite mask works: `x ↦ x ∆ [1, ∞)` fails too. -/
example : ¬ Descends (· ∆ (Ici 1 : Set ℕ)) := by
  intro h
  rcases (rigidity _).mp h with h0 | h0
  · have : (1 : ℕ) ∈ (Ici 1 : Set ℕ) := le_refl 1
    rw [h0] at this
    exact this
  · have : (0 : ℕ) ∈ (Ici 1 : Set ℕ) := h0 ▸ mem_univ 0
    simp at this

/-! ### The value map really is the Stern–Brocot tree

The first three levels, checked against the mediant construction. Lists are read
with the head applied *last*, so a word ending in `true` is a tree node and
`nodeValue` is the value of that path padded with left moves — which is exactly
the point of `P(ω)` that the corresponding finite set denotes. -/

example : nodeValue [true] = 1 := by norm_num [nodeValue]
example : nodeValue [true, true] = 2 := by norm_num [nodeValue]
example : nodeValue [false, true] = 1 / 2 := by norm_num [nodeValue]
example : nodeValue [true, false, true] = 3 / 2 := by norm_num [nodeValue]
example : nodeValue [false, false, true] = 1 / 3 := by norm_num [nodeValue]
example : nodeValue [false, true, true] = 2 / 3 := by norm_num [nodeValue]

/-- Padding with left moves changes nothing: `1/2` again. -/
example : nodeValue [false, true, false, false] = 1 / 2 := by norm_num [nodeValue]

/-- The matrix of `R L R`, with determinant `1` and value `3/2`. -/
example : pathMat [true, false, true] = (2, 3, 1, 2) := by norm_num [pathMat]

/-! ### Canonicity is the intended notion

A path is canonical exactly when it ends in a right move. These pin that down:
without them, `Canonical` could be some other predicate and the enumeration
theorem would still typecheck. -/

/-- A path ending in a left move is *not* canonical — `[false]` denotes `0`, which
is already denoted by `[]`. -/
theorem not_canonical_false : ¬ Canonical [false] := by
  intro h
  cases h with
  | cons hne _ => exact hne rfl

example : ¬ Canonical [true, false] := fun h => not_canonical_false h.tail

/-! ### The Euclidean algorithm, run by hand

`22/7` takes three right moves down to `1/7`, then six left moves to `1`. If
`nodeValue` or the enumeration were subtly wrong, this would fail. -/

/-- The canonical path for `22/7`. -/
def path22over7 : List Bool :=
  [true, true, true, false, false, false, false, false, false, true]

example : Canonical path22over7 :=
  canonical_append_true [true, true, true, false, false, false, false, false, false]

example : nodeValue path22over7 = 22 / 7 := by norm_num [path22over7, nodeValue]

/-- The matrix reproduces `22/7` as an already-reduced fraction: numerator `22`,
denominator `7`, determinant `1`. -/
example : (pathMat path22over7).2.1 = 22 ∧ (pathMat path22over7).2.2.2 = 7 := by
  constructor <;> norm_num [path22over7, pathMat]

/-- Six left moves then a right move is `1/7` — the tree really does walk the
Stern–Brocot mediants. -/
example : nodeValue [false, false, false, false, false, false, true] = 1 / 7 := by
  norm_num [nodeValue]

/-! ### The order embedding, and its orientation

The in-order traversal of the tree down to level three, checked to be increasing:

`1/3 < 1/2 < 2/3 < 1 < 3/2 < 2 < 3`

Each step is stated as a `PathLt` claim and discharged through
`pathLt_iff_nodeValue_lt`, so it exercises the embedding in the direction that
matters. If the orientation were flipped anywhere — in particular on the
left-headed paths, where `t ↦ t/(t+1)` is increasing yet lands *below* every
right-headed path — these would fail. -/

example : [false, false, true] <ₚ [false, true] :=
  (pathLt_iff_nodeValue_lt _ _).2 (by norm_num [nodeValue])

example : [false, true] <ₚ [false, true, true] :=
  (pathLt_iff_nodeValue_lt _ _).2 (by norm_num [nodeValue])

example : [false, true, true] <ₚ [true] :=
  (pathLt_iff_nodeValue_lt _ _).2 (by norm_num [nodeValue])

example : [true] <ₚ [true, false, true] :=
  (pathLt_iff_nodeValue_lt _ _).2 (by norm_num [nodeValue])

example : [true, false, true] <ₚ [true, true] :=
  (pathLt_iff_nodeValue_lt _ _).2 (by norm_num [nodeValue])

example : [true, true] <ₚ [true, true, true] :=
  (pathLt_iff_nodeValue_lt _ _).2 (by norm_num [nodeValue])

/-- A left-headed path is never above a right-headed one. -/
example : ¬ ([true] <ₚ [false, true]) := by
  rw [pathLt_iff_nodeValue_lt]
  norm_num [nodeValue]

/-- Trailing left moves are invisible to the order too: `[false, true]` and
`[false, true, false]` both denote `1/2` and are incomparable. -/
example : ¬ ([false, true] <ₚ [false, true, false]) := by
  rw [pathLt_iff_nodeValue_lt]
  norm_num [nodeValue]

example : ¬ ([false, true, false] <ₚ [false, true]) := by
  rw [pathLt_iff_nodeValue_lt]
  norm_num [nodeValue]

/-- `22/7` sits above `3` — three right moves in, and the left moves after only
walk it back down within `[3, 4)`. -/
example : [true, true, true] <ₚ path22over7 :=
  (pathLt_iff_nodeValue_lt _ _).2 (by norm_num [path22over7, nodeValue])

/-! ### The bridge: paths and the carrier are the same object

End-to-end checks. The value map was built on `List Bool`; the carrier is
`Set ℕ`. These confirm the two really do describe one structure. -/

example : toSet [true] = ({0} : Set ℕ) := by
  ext n
  match n with
  | 0 => simp
  | (k + 1) => simp

example : toSet [false, true] = ({1} : Set ℕ) := by
  ext n
  match n with
  | 0 => simp
  | 1 => simp
  | (k + 2) => simp

/-- **The keystone check.** The von Neumann `2` — built as `S (S ∅)` with the
successor from `Basic.lean` — is exactly the tree node whose Stern–Brocot value
is `2`. The set-theoretic side and the arithmetic side agree. -/
example : toSet [true, true] = S (S ∅) := by
  rw [two_eq_pair]
  ext n
  match n with
  | 0 => simp
  | 1 => simp
  | (k + 2) => simp

example : nodeValue [true, true] = 2 := by norm_num [nodeValue]

/-- `1/2 < 1` stated on the carrier, discharged by a rational comparison. -/
example : toSet [false, true] <ₗ toSet [true] :=
  (lexLt_toSet_iff _ _).2 (by norm_num [nodeValue])

example : ∃ bs, Canonical bs ∧ toSet bs = ({0, 1} : Set ℕ) :=
  exists_canonical_path_of_finite (Set.toFinite _)

/-! ### `Φ₀` lands on the right real numbers

The cut construction reproduces the tree, and the tree reproduces the encoding.
The last of these is the end-to-end statement of the whole development so far:
the von Neumann `2`, built from `∅` by the successor `S`, is sent by `Φ₀` to the
real number `2`. -/

example : toReal₀ (toSet [true]) = 1 := by
  rw [toReal₀_toSet]; norm_num [nodeValue]

example : toReal₀ (toSet [false, true]) = 1 / 2 := by
  rw [toReal₀_toSet]; norm_num [nodeValue]

example : toReal₀ (toSet path22over7) = 22 / 7 := by
  rw [toReal₀_toSet]; norm_num [path22over7, nodeValue]

/-- **The end-to-end check.** `S (S ∅)` is the von Neumann `2` as a subset of `ω`,
built with the successor from `Basic.lean`. `Φ₀` sends it to `(2 : ℝ)`. -/
example : toReal₀ (S (S ∅)) = 2 := by
  have h : toSet [true, true] = S (S ∅) := by
    rw [two_eq_pair]
    ext n
    match n with
    | 0 => simp
    | 1 => simp
    | (k + 2) => simp
  rw [← h, toReal₀_toSet]
  norm_num [nodeValue]

/-- The two representations of `2` — `{0,1}` and `ω \ {1}` — have the same image,
since `Φ₀` is constant on tail classes. -/
example : toReal₀ ({0, 1} : Set ℕ) = toReal₀ {n : ℕ | n ≠ 1} :=
  toReal₀_of_tailPair two_tailPair

/-! ### The signed map: negatives, end to end

`S (S ∅)` is the von Neumann `2`. Lifted into `P(ω+1)` it is `+2`; its
complement is `-2`. Both zeros land on `0` with no special casing. -/

/-- The canonical path for `2`, as a subset of `ω`. -/
theorem toSet_two_eq : toSet [true, true] = S (S ∅) := by
  rw [two_eq_pair]; exact toSet_two

example : toReal (lift (S (S ∅))) = 2 := by
  rw [toReal_lift, ← toSet_two_eq, toReal₀_toSet]; norm_num [nodeValue]

/-- **Negation, end to end.** The complement of the lifted von Neumann `2` is the
real number `-2`. -/
example : toReal (neg (lift (S (S ∅)))) = -2 := by
  rw [toReal_neg, toReal_lift, ← toSet_two_eq, toReal₀_toSet]; norm_num [nodeValue]

/-! ### The golden ratio — why `φ` is not the name of the map

`φ = (1+√5)/2` has continued fraction `[1; 1, 1, 1, …]`, so its Stern–Brocot path
alternates `R L R L …`, and as a subset of `ω` that is exactly the **even
numbers**. Truncating the path gives the Fibonacci convergents
`1, 2, 3/2, 5/3, 8/5, …`.

This is why the value map is called `toReal` and not `phi`: in this development
`φ` is a specific real number with a specific and rather pretty encoding, and the
name should stay available for it. -/

/-- Five moves down the golden ratio's path: the even numbers below `5`. -/
example : toSet [true, false, true, false, true] = ({0, 2, 4} : Set ℕ) := by
  ext n
  match n with
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | 3 => simp
  | 4 => simp
  | (k + 5) => simp

/-- The convergents are the Fibonacci ratios; `1` and `3/2` are checked above, and
the path continues `8/5`. -/
example : nodeValue [true, false, true, false, true] = 8 / 5 := by norm_num [nodeValue]

/-- ...and they climb towards `φ ≈ 1.618` from alternating sides. -/
example : nodeValue [true, false, true] < nodeValue [true, false, true, false, true] := by
  norm_num [nodeValue]

/-! ### `φ` on the nose

The truncations above only say the *convergents* are the Fibonacci ratios. The
claim itself — the even numbers **are** `φ` — is a statement about the infinite
path, and `toReal₀_S`/`toReal₀_L` prove it: the path is fixed by two shifts, so
its value satisfies `t = t/(t+1) + 1`, which is `t² = t + 1`. -/

/-- The golden ratio's path: `R L R L …`, i.e. the even numbers. -/
def goldenPath : Set ℕ := {n | Even n}

theorem goldenPath_ne_univ : goldenPath ≠ univ := by
  intro h
  have : (1 : ℕ) ∈ goldenPath := h ▸ mem_univ 1
  simp [goldenPath, Nat.even_iff] at this

/-- **The path repeats with period two**, which is what makes `φ` quadratic. -/
theorem shift_two_goldenPath : shift^[2] goldenPath = goldenPath := by
  rw [iterate_shift]
  ext n
  simp only [Set.mem_setOf_eq, goldenPath, Nat.even_iff]
  omega

theorem goldenPath_eventuallyPeriodic : EventuallyPeriodic goldenPath :=
  ⟨0, 2, by norm_num, shift_two_goldenPath⟩

/-- One period, written out: a right move then a left move returns the path. -/
theorem goldenPath_eq : goldenPath = S (L goldenPath) := by
  ext n
  match n with
  | 0 => simp [goldenPath]
  | 1 => simp [goldenPath, Nat.even_iff]
  | (k + 2) =>
    simp only [goldenPath, Set.mem_setOf_eq, succ_mem_S, succ_mem_L, Nat.even_iff]
    omega

/-- **The even numbers are `φ`.** -/
theorem toReal₀_goldenPath : toReal₀ goldenPath = Real.goldenRatio := by
  set t : ℝ := toReal₀ goldenPath with ht
  have ht0 : 0 ≤ t := toReal₀_nonneg _
  -- the fixed-point equation, from one period of the path
  have hfix : t = t / (t + 1) + 1 := by
    conv_lhs => rw [ht, goldenPath_eq]
    rw [toReal₀_S (L_ne_univ _), toReal₀_L goldenPath_ne_univ]
  have hquad : t ^ 2 = t + 1 := by
    have h1 : (0 : ℝ) < t + 1 := by linarith
    field_simp at hfix
    linarith
  -- `t ≥ 1`, so the positive root is the one
  have ht1 : 1 ≤ t := by nlinarith
  have h5 : Real.sqrt 5 = 2 * t - 1 := by
    rw [show (5 : ℝ) = (2 * t - 1) ^ 2 by nlinarith]
    exact Real.sqrt_sq (by linarith)
  rw [Real.goldenRatio, h5]
  ring

/-- **Lagrange, on `φ`.** Not a fresh proof that `φ` is quadratic — a check that
the general theorem, applied to a path that is visibly periodic, gives it. -/
example : DegLeTwo Real.goldenRatio :=
  toReal₀_goldenPath ▸ degLeTwo_of_eventuallyPeriodic goldenPath_ne_univ
    goldenPath_eventuallyPeriodic

/-! ### The convergents of `φ` are the Fibonacci ratios

`contin` is built from run boundaries of a *bit set*; `Nat.fib` is defined in
Mathlib with no reference to any of this. That they agree on `{n | Even n}` is
the check that the run decomposition computes the classical continued fraction
and not something else. With `toReal₀_goldenPath` it says: the convergents of
`φ` are `1/1, 2/1, 3/2, 5/3, …`. -/

theorem bitAt_goldenPath_succ_ne (n : ℕ) : bitAt goldenPath (n + 1) ≠ bitAt goldenPath n := by
  rcases Nat.even_or_odd n with he | ho
  · rw [bitAt_eq_true.2 (show n ∈ goldenPath from he),
      bitAt_eq_false.2 (show (n + 1) ∉ goldenPath from fun h => (Nat.even_add_one.1 h) he)]
    simp
  · rw [bitAt_eq_false.2 (show n ∉ goldenPath from Nat.not_even_iff_odd.2 ho),
      bitAt_eq_true.2 (show (n + 1) ∈ goldenPath from Nat.even_add_one.2
        (Nat.not_even_iff_odd.2 ho))]
    simp

theorem infFlips_goldenPath : InfFlips goldenPath :=
  fun n => ⟨n + 1, Nat.lt_succ_self n, bitAt_goldenPath_succ_ne n⟩

/-- `φ` flips at every position, so every run has length one. -/
theorem nextFlip_goldenPath (n : ℕ) : nextFlip goldenPath n = n + 1 := by
  have hmem : (n + 1) ∈ {m | n < m ∧ bitAt goldenPath m ≠ bitAt goldenPath n} :=
    ⟨Nat.lt_succ_self n, bitAt_goldenPath_succ_ne n⟩
  exact le_antisymm (Nat.sInf_le hmem) (Nat.sInf_mem ⟨n + 1, hmem⟩).1

theorem runBoundary_goldenPath (k : ℕ) : runBoundary goldenPath k = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [runBoundary_succ, ih, nextFlip_goldenPath]

/-- **Every partial quotient of `φ` is `1`.** -/
theorem partialQuot_goldenPath (k : ℕ) : partialQuot goldenPath k = 1 := by
  rw [partialQuot, runBoundary_goldenPath, runBoundary_goldenPath]
  omega

theorem runBit_goldenPath_zero : runBit goldenPath 0 = true := by
  rw [runBit, runBoundary_goldenPath]
  exact bitAt_eq_true.2 (show (0 : ℕ) ∈ goldenPath from ⟨0, rfl⟩)

/-- **The continuants of `φ` are consecutive Fibonacci numbers.** -/
theorem contin_goldenPath (k : ℕ) :
    contin goldenPath (k + 1) = ((Nat.fib (k + 1) : ℤ), (Nat.fib k : ℤ)) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => rw [contin_one, runBit_goldenPath_zero]; norm_num
    | 1 =>
      have h0 : contin goldenPath 0 = (0, 1) := by
        rw [contin_zero, runBit_goldenPath_zero]; norm_num
      have h1 : contin goldenPath 1 = (1, 0) := by
        rw [contin_one, runBit_goldenPath_zero]; norm_num
      rw [contin_add_two, partialQuot_goldenPath, h0, h1]
      norm_num
    | (j + 2) =>
      have h1 : contin goldenPath (j + 2) = ((Nat.fib (j + 2) : ℤ), (Nat.fib (j + 1) : ℤ)) :=
        ih (j + 1) (by omega)
      have h2 : contin goldenPath (j + 1) = ((Nat.fib (j + 1) : ℤ), (Nat.fib j : ℤ)) :=
        ih j (by omega)
      have hrec : contin goldenPath (j + 3)
          = ((partialQuot goldenPath (j + 1) : ℤ) * (contin goldenPath (j + 2)).1
                + (contin goldenPath (j + 1)).1,
             (partialQuot goldenPath (j + 1) : ℤ) * (contin goldenPath (j + 2)).2
                + (contin goldenPath (j + 1)).2) := contin_add_two goldenPath (j + 1)
      show contin goldenPath (j + 3) = ((Nat.fib (j + 3) : ℤ), (Nat.fib (j + 2) : ℤ))
      rw [hrec, partialQuot_goldenPath, h1, h2,
        show Nat.fib (j + 3) = Nat.fib (j + 1) + Nat.fib (j + 2) from Nat.fib_add_two,
        show Nat.fib (j + 2) = Nat.fib j + Nat.fib (j + 1) from Nat.fib_add_two]
      simp only [Prod.mk.injEq]
      constructor <;> · push_cast; ring

end SternBrocot
