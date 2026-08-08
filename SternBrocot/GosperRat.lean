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
