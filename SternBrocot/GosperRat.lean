/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Gosper
import SternBrocot.Enumeration

/-!
# Gosper on the rationals

Rational inputs are **finite** paths, so the machine terminates: absorbing
consumes a move and the recursion runs on the remaining path, with no coinduction
and no productivity obligation. This is the tractable half of the Gosper project,
and it is tractable for a specific reason — with finite inputs the emit guard
`z ≥ 1` is decidable, whereas on infinite paths it is exactly where the
undecidability lives.

Absorbing consumes the *head* of a path first, because a path is read with its
head applied last: `nodeValue (b :: bs) = moveᵦ (nodeValue bs)`, so the outermost
move is the one to take off first, and what remains is `bs`.

Once both paths are exhausted the remaining inputs are `0`, and the tensor's
value is a plain rational — whose canonical path is supplied by
`exists_canonical_of_nonneg`, itself the Euclidean algorithm.

## Main results

* `SternBrocot.Tensor.value_absorbLeftPath` / `value_absorbRightPath` — feeding a
  whole path in is the same as supplying its value.
* `SternBrocot.Tensor.add_paths` / `mul_paths` — the tensor, fed both paths,
  computes the sum and the product.
-/

namespace SternBrocot

namespace Tensor

/-! ### Feeding a whole path into an input -/

/-- Absorb an entire path from the left input, outermost move first. -/
def absorbLeftPath : List Bool → Tensor → Tensor
  | [], t => t
  | true :: bs, t => absorbLeftPath bs (absorbLeftS t)
  | false :: bs, t => absorbLeftPath bs (absorbLeftL t)

/-- Absorb an entire path from the right input, outermost move first. -/
def absorbRightPath : List Bool → Tensor → Tensor
  | [], t => t
  | true :: bs, t => absorbRightPath bs (absorbRightS t)
  | false :: bs, t => absorbRightPath bs (absorbRightL t)

/-- **Feeding a path in is the same as supplying its value.** After the whole
path has been absorbed the remaining input is the empty path, whose value is
`0`. -/
theorem value_absorbLeftPath (bs : List Bool) (t : Tensor) (y : ℚ) :
    (absorbLeftPath bs t).value 0 y = t.value (nodeValue bs) y := by
  induction bs generalizing t with
  | nil => rw [absorbLeftPath, nodeValue_nil]
  | cons b bs ih =>
    cases b
    · rw [absorbLeftPath, ih, value_absorbLeftL _ _ _ (by
        have := nodeValue_nonneg bs; linarith), nodeValue_false, moveL_apply]
    · rw [absorbLeftPath, ih, value_absorbLeftS, nodeValue_true, moveS_apply]

theorem value_absorbRightPath (cs : List Bool) (t : Tensor) (x : ℚ) :
    (absorbRightPath cs t).value x 0 = t.value x (nodeValue cs) := by
  induction cs generalizing t with
  | nil => rw [absorbRightPath, nodeValue_nil]
  | cons c cs ih =>
    cases c
    · rw [absorbRightPath, ih, value_absorbRightL _ _ _ (by
        have := nodeValue_nonneg cs; linarith), nodeValue_false, moveL_apply]
    · rw [absorbRightPath, ih, value_absorbRightS, nodeValue_true, moveS_apply]

/-- Absorbing on the left does not disturb the right input, so the two phases
commute and can be run in either order. -/
theorem value_absorbLeftPath_zero (bs cs : List Bool) (t : Tensor) :
    (absorbRightPath cs (absorbLeftPath bs t)).value 0 0
      = t.value (nodeValue bs) (nodeValue cs) := by
  rw [value_absorbRightPath, value_absorbLeftPath]

/-! ### The machine computes rational arithmetic -/

/-- **Addition.** The tensor started at `x + y`, fed both paths, has the sum as
its value. -/
theorem add_paths (bs cs : List Bool) :
    (absorbRightPath cs (absorbLeftPath bs add)).value 0 0
      = nodeValue bs + nodeValue cs := by
  rw [value_absorbLeftPath_zero, value_add]

/-- **Multiplication.** -/
theorem mul_paths (bs cs : List Bool) :
    (absorbRightPath cs (absorbLeftPath bs mul)).value 0 0
      = nodeValue bs * nodeValue cs := by
  rw [value_absorbLeftPath_zero, value_mul]

/-- **Subtraction.** -/
theorem sub_paths (bs cs : List Bool) :
    (absorbRightPath cs (absorbLeftPath bs sub)).value 0 0
      = nodeValue bs - nodeValue cs := by
  rw [value_absorbLeftPath_zero, value_sub]

end Tensor

/-! ### The result is again a node

Closing the loop: the value the machine lands on is a nonnegative rational when
the inputs are, so it is the value of a canonical path — which is what makes the
node arithmetic total on the tree. -/

/-- The sum of two node values is again a node value. -/
theorem exists_canonical_add (bs cs : List Bool) :
    ∃ ds, Canonical ds ∧ nodeValue ds = nodeValue bs + nodeValue cs :=
  exists_canonical_of_nonneg (by
    have h1 := nodeValue_nonneg bs
    have h2 := nodeValue_nonneg cs
    linarith)

/-- The product of two node values is again a node value. -/
theorem exists_canonical_mul (bs cs : List Bool) :
    ∃ ds, Canonical ds ∧ nodeValue ds = nodeValue bs * nodeValue cs :=
  exists_canonical_of_nonneg (mul_nonneg (nodeValue_nonneg bs) (nodeValue_nonneg cs))

/-! ### The emit phase, as a function

`exists_canonical_of_nonneg` only says an output path *exists*. To close the loop
the Euclidean algorithm has to be a definition, so that the machine takes paths
in and gives a path out. Termination is on `a + b`: subtracting the smaller from
the larger strictly decreases it. -/

/-- The canonical path of `a / b`, by the Euclidean algorithm. Junk (`[]`) when
`b = 0`, matching `a / 0 = 0` in `ℚ`. -/
def pathOf : ℕ → ℕ → List Bool
  | _, 0 => []
  | 0, _ => []
  | a + 1, b + 1 =>
      if b + 1 ≤ a + 1 then true :: pathOf (a + 1 - (b + 1)) (b + 1)
      else false :: pathOf (a + 1) (b + 1 - (a + 1))
  termination_by a b => a + b
  decreasing_by all_goals omega

@[simp] theorem pathOf_zero_right (a : ℕ) : pathOf a 0 = [] := by
  cases a <;> simp [pathOf]

@[simp] theorem pathOf_zero_left (b : ℕ) : pathOf 0 b = [] := by
  cases b <;> simp [pathOf]

theorem pathOf_ne_nil (a b : ℕ) : pathOf (a + 1) (b + 1) ≠ [] := by
  rw [pathOf]
  split <;> exact List.cons_ne_nil _ _

/-- **The emit phase is correct.** -/
theorem nodeValue_pathOf (a b : ℕ) : nodeValue (pathOf a b) = (a : ℚ) / (b : ℚ) := by
  induction a, b using pathOf.induct with
  | case1 a => simp
  | case2 b => simp
  | case3 a b hle ih =>
    have hba : b ≤ a := by omega
    have heq : a + 1 - (b + 1) = a - b := by omega
    rw [pathOf, if_pos hle, nodeValue_true, ih, heq, Nat.cast_sub hba]
    have hb : ((b : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  | case4 a b hle ih =>
    have hab : a < b := by omega
    have heq : b + 1 - (a + 1) = b - a := by omega
    rw [pathOf, if_neg hle, nodeValue_false, ih, heq, Nat.cast_sub hab.le]
    have hba : ((b : ℚ) - (a : ℚ)) ≠ 0 := by
      have hlt : (a : ℚ) < (b : ℚ) := by exact_mod_cast hab
      linarith
    have hb1 : ((b : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    have hu : ((a : ℚ) + 1) / ((b : ℚ) - (a : ℚ)) + 1
        = ((b : ℚ) + 1) / ((b : ℚ) - (a : ℚ)) := by
      field_simp
      ring
    rw [hu, div_div_eq_mul_div, div_mul_cancel₀ _ hba]

theorem canonical_pathOf (a b : ℕ) : Canonical (pathOf a b) := by
  induction a, b using pathOf.induct with
  | case1 a => simp [Canonical.nil]
  | case2 b => simp [Canonical.nil]
  | case3 a b hle ih =>
    rw [pathOf, if_pos hle]
    cases h : pathOf (a + 1 - (b + 1)) (b + 1) with
    | nil => exact Canonical.single
    | cons c cs => exact Canonical.cons (by simp) (h ▸ ih)
  | case4 a b hle ih =>
    rw [pathOf, if_neg hle]
    exact Canonical.cons (by
      have hlt : (a : ℕ) < b := by omega
      obtain ⟨k, hk⟩ : ∃ k, b + 1 - (a + 1) = k + 1 := ⟨b - a - 1, by omega⟩
      rw [hk]; exact pathOf_ne_nil a k) ih

/-- The canonical path of a nonnegative rational. -/
def toPath (q : ℚ) : List Bool := pathOf q.num.toNat q.den

theorem nodeValue_toPath {q : ℚ} (hq : 0 ≤ q) : nodeValue (toPath q) = q := by
  rw [toPath, nodeValue_pathOf]
  have hnum : ((q.num.toNat : ℕ) : ℚ) = (q.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 hq)
  rw [hnum]
  exact Rat.num_div_den q

theorem canonical_toPath (q : ℚ) : Canonical (toPath q) := canonical_pathOf _ _

/-! ### Paths in, path out

The loop closed: `gosperAdd` and `gosperMul` take two canonical paths and return
a canonical path, computed entirely through the tensor, and their values are the
sum and the product. -/

/-- Add two paths through the tensor. -/
def gosperAdd (bs cs : List Bool) : List Bool :=
  toPath ((Tensor.absorbRightPath cs (Tensor.absorbLeftPath bs Tensor.add)).value 0 0)

/-- Multiply two paths through the tensor. -/
def gosperMul (bs cs : List Bool) : List Bool :=
  toPath ((Tensor.absorbRightPath cs (Tensor.absorbLeftPath bs Tensor.mul)).value 0 0)

/-- **Addition on paths is correct.** -/
theorem nodeValue_gosperAdd (bs cs : List Bool) :
    nodeValue (gosperAdd bs cs) = nodeValue bs + nodeValue cs := by
  rw [gosperAdd, Tensor.add_paths,
    nodeValue_toPath (by have := nodeValue_nonneg bs; have := nodeValue_nonneg cs; linarith)]

/-- **Multiplication on paths is correct.** -/
theorem nodeValue_gosperMul (bs cs : List Bool) :
    nodeValue (gosperMul bs cs) = nodeValue bs * nodeValue cs := by
  rw [gosperMul, Tensor.mul_paths,
    nodeValue_toPath (mul_nonneg (nodeValue_nonneg bs) (nodeValue_nonneg cs))]

theorem canonical_gosperAdd (bs cs : List Bool) : Canonical (gosperAdd bs cs) :=
  canonical_toPath _

theorem canonical_gosperMul (bs cs : List Bool) : Canonical (gosperMul bs cs) :=
  canonical_toPath _

/-! ### The machine, run

Concrete arithmetic through the tensor, discharged via `add_paths` and
`mul_paths` so the checks exercise the theorems rather than bypassing them. -/

open Tensor in
/-- `1/2 + 2 = 5/2`, computed by feeding both paths to the tensor. -/
example : (absorbRightPath [true, true] (absorbLeftPath [false, true] add)).value 0 0 = 5 / 2 := by
  rw [add_paths]; norm_num [nodeValue]

open Tensor in
/-- `1/2 × 2 = 1`. -/
example : (absorbRightPath [true, true] (absorbLeftPath [false, true] mul)).value 0 0 = 1 := by
  rw [mul_paths]; norm_num [nodeValue]

open Tensor in
/-- `2 - 1/2 = 3/2`. -/
example : (absorbRightPath [false, true] (absorbLeftPath [true, true] sub)).value 0 0 = 3 / 2 := by
  rw [sub_paths]; norm_num [nodeValue]

end SternBrocot
