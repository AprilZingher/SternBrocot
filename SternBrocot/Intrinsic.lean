/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Field
import SternBrocot.GosperRat

/-!
# Intrinsic `+` and `×`

`Field.lean` transports the field structure from `ℝ` along `orderIsoReal`. By
uniqueness of complete ordered fields that transport has no freedom in it — and
`toRealQ_add_eq_sSup` proves it concretely, showing `+` is pinned down by the
order alone. But the *definition* still mentions `ℝ`. This file closes that: it
defines `+` and `×` on the carrier itself, with no `ℝ` anywhere in the
definitions.

**Status: skeleton.** The definitions below are final and the field axioms are
all stated. The proofs are `sorry` and are listed by name in `HANDOFF.md`.

## The design

Three layers, each intrinsic.

1. **A supremum on `P(ω+1)`.** `Completeness.lean` already builds `lexSup`, the
   bitwise supremum on `P(ω)`. The signed order (`SLexLt`) is "negatives below
   positives, same sign by forward lex on the stored bits", so a supremum on
   `Signed` needs exactly one case split: if the set has a positive element the
   supremum is positive with stored bits `lexSup` of the positive members'
   stored bits; otherwise it is negative with stored bits `lexSup` of all the
   members' stored bits. That is `slexSup`.

   There is no boundedness hypothesis, exactly as for `lexSup`: `P(ω+1)` is a
   complete lattice for the lex order because `±∞` are in it. Finiteness of the
   supremum is a separate lemma and is where the hypotheses live.

2. **The rationals, intrinsically.** `GosperRat.toPath` is the Euclidean
   algorithm as a function `ℚ≥0 → List Bool`, and `Bridge.toSet` turns a word
   into a point. `ratPoint` extends it across the sign by `neg`. No `ℝ`.

3. **The operations, as suprema over the nodes.**

       a + b = sup { ratPoint (p + q) | ratPoint p <ₛ a, ratPoint q <ₛ b }

   with `p q : ℚ` and the inner `+` rational addition — so there is no
   circularity. Multiplication is the same formula on the nonnegative parts,
   extended across the signs by `neg`; the sign case split is unavoidable
   because the supremum formula is only monotone on the positive cone.

   `toRealQ_add_eq_sSup` is the specification: it already proves that the
   supremum characterisation lands on the transported operation, so nothing is
   lost by taking it as the definition.

## What the remaining proofs need

Everything reduces to two theorems, `toRealQ_add'` and `toRealQ_mul'`, saying
the intrinsic operations agree with the transported ones. Given those, every
field axiom follows in one line by `toRealQ_injective`, because `ℝ` satisfies
it. That is the cheap route and the one taken below.

It is worth being precise about what that does and does not achieve. After it,
the **definitions** of `+` and `×` never mention `ℝ`; the **proofs** of the
axioms still do, via the bridge. The stronger statement — that the axioms
themselves are provable without `ℝ`, by density of the nodes and continuity — is
a further step, and the honest way to describe the result of this file is the
weaker one. See `HANDOFF.md`.
-/

open Set

namespace SternBrocot

/-! ### A supremum on the signed carrier -/

/-- The negative point with stored bits `y`. -/
def negLift (y : Set ℕ) : Signed := insert none (lift y)

@[simp] theorem none_mem_negLift (y : Set ℕ) : none ∈ negLift y := by
  simp [negLift]

@[simp] theorem finPart_negLift (y : Set ℕ) : finPart (negLift y) = y := by
  ext n
  simp [negLift, finPart, lift]

/-- The stored bits of the positive members of `S`. -/
def posBits (S : Set Signed) : Set (Set ℕ) := {y | ∃ x ∈ S, none ∉ x ∧ finPart x = y}

/-- The stored bits of all members of `S`. -/
def allBits (S : Set Signed) : Set (Set ℕ) := {y | ∃ x ∈ S, finPart x = y}

open Classical in
/-- **The supremum on `P(ω+1)`.** One case split: a set with a positive member
has a positive supremum, and a set of negatives has a negative one. Within each
sign the order is forward lex on the stored bits, so `lexSup` does the work. -/
noncomputable def slexSup (S : Set Signed) : Signed :=
  if ∃ x ∈ S, none ∉ x then lift (lexSup (posBits S)) else negLift (lexSup (allBits S))

/-- `slexSup S` is an upper bound for `S`. -/
theorem slexSup_upperBound (S : Set Signed) : ∀ x ∈ S, ¬ (slexSup S <ₛ x) := by
  sorry

/-- `slexSup S` is the least upper bound. -/
theorem slexSup_least (S : Set Signed) (v : Signed) (hv : ∀ x ∈ S, ¬ (v <ₛ x)) :
    ¬ (v <ₛ slexSup S) := by
  sorry

/-! ### The rationals as points, intrinsically

`toPath` is the Euclidean algorithm; `toSet` turns a word into a point; `neg` is
complement. Nothing here knows about `ℝ`. -/

open Classical in
/-- The point of `P(ω+1)` representing a rational. -/
noncomputable def ratPoint (q : ℚ) : Signed :=
  if 0 ≤ q then lift (toSet (toPath q)) else neg (lift (toSet (toPath (-q))))

theorem isFinite_ratPoint (q : ℚ) : IsFinite (ratPoint q) := by
  sorry

/-- **The specification of `ratPoint`.** Not used in any definition — it is the
bridge that lets the rest of the file be checked against `ℝ`. -/
theorem toReal_ratPoint (q : ℚ) : toReal (ratPoint q) = (q : ℝ) := by
  sorry

/-! ### The operations -/

/-- The set of rational-node sums lying strictly below `a` and `b`. -/
def addCut (a b : Signed) : Set Signed :=
  {z | ∃ p q : ℚ, ratPoint p <ₛ a ∧ ratPoint q <ₛ b ∧ z = ratPoint (p + q)}

/-- **Intrinsic addition on `P(ω+1)`**: the supremum of the sums of the nodes
below the two arguments. -/
noncomputable def addRaw (a b : Signed) : Signed := slexSup (addCut a b)

/-- The nonnegative part of the product cut. -/
def mulCut (a b : Signed) : Set Signed :=
  {z | ∃ p q : ℚ, 0 ≤ p ∧ 0 ≤ q ∧ ratPoint p <ₛ a ∧ ratPoint q <ₛ b ∧ z = ratPoint (p * q)}

/-- Multiplication on the nonnegative cone. -/
noncomputable def mulRawPos (a b : Signed) : Signed := slexSup (mulCut a b)

open Classical in
/-- **Intrinsic multiplication on `P(ω+1)`.** The supremum formula is only
monotone on the positive cone, so the signs are handled by `neg` — which is
complement, hence still intrinsic. -/
noncomputable def mulRaw (a b : Signed) : Signed :=
  if none ∈ a then
    if none ∈ b then mulRawPos (neg a) (neg b) else neg (mulRawPos (neg a) b)
  else
    if none ∈ b then neg (mulRawPos a (neg b)) else mulRawPos a b

/-! ### Descending to the quotient

Two obligations: the operations preserve finiteness, and they respect the
adjacency quotient. Both are statements about `slexSup`, and neither mentions
`ℝ`. -/

theorem isFinite_addRaw {a b : Signed} (ha : IsFinite a) (hb : IsFinite b) :
    IsFinite (addRaw a b) := by
  sorry

theorem isFinite_mulRaw {a b : Signed} (ha : IsFinite a) (hb : IsFinite b) :
    IsFinite (mulRaw a b) := by
  sorry

theorem addRaw_congr {a a' b b' : Signed} (ha : SEqv a a') (hb : SEqv b b') :
    SEqv (addRaw a b) (addRaw a' b') := by
  sorry

theorem mulRaw_congr {a a' b b' : Signed} (ha : SEqv a a') (hb : SEqv b b') :
    SEqv (mulRaw a b) (mulRaw a' b') := by
  sorry

/-- **Intrinsic addition on `SBReal`.** -/
noncomputable def add' : SBReal → SBReal → SBReal :=
  Quotient.lift₂ (fun a b : FinitePoint => mk (addRaw a.1 b.1) (isFinite_addRaw a.2 b.2))
    (fun _ _ _ _ h₁ h₂ => Quotient.sound (addRaw_congr h₁ h₂))

/-- **Intrinsic multiplication on `SBReal`.** -/
noncomputable def mul' : SBReal → SBReal → SBReal :=
  Quotient.lift₂ (fun a b : FinitePoint => mk (mulRaw a.1 b.1) (isFinite_mulRaw a.2 b.2))
    (fun _ _ _ _ h₁ h₂ => Quotient.sound (mulRaw_congr h₁ h₂))

@[simp] theorem add'_mk (a b : Signed) (ha : IsFinite a) (hb : IsFinite b) :
    add' (mk a ha) (mk b hb) = mk (addRaw a b) (isFinite_addRaw ha hb) := rfl

@[simp] theorem mul'_mk (a b : Signed) (ha : IsFinite a) (hb : IsFinite b) :
    mul' (mk a ha) (mk b hb) = mk (mulRaw a b) (isFinite_mulRaw ha hb) := rfl

/-! ### The two theorems everything rests on

These are the *only* remaining mathematical content: the intrinsic operations
compute the transported ones. `toRealQ_add_eq_sSup` is already most of the first
one — it proves the supremum characterisation is correct; what is left is that
the supremum taken in `P(ω+1)` by `slexSup` is the supremum `toRealQ` sees. -/

theorem toRealQ_add' (a b : SBReal) : toRealQ (add' a b) = toRealQ a + toRealQ b := by
  sorry

theorem toRealQ_mul' (a b : SBReal) : toRealQ (mul' a b) = toRealQ a * toRealQ b := by
  sorry

/-! ### `toRealQ` on the transported constants

`Field.lean` records `toRealQ_add` and `toRealQ_mul`; the remaining constants
follow from those two by cancellation, with no reference to how the transport
was set up. -/

@[simp] theorem toRealQ_zero : toRealQ (0 : SBReal) = 0 := by
  have h := toRealQ_add (0 : SBReal) 0
  rw [add_zero] at h
  linarith

@[simp] theorem toRealQ_neg (a : SBReal) : toRealQ (-a) = -toRealQ a := by
  have h := toRealQ_add a (-a)
  rw [add_neg_cancel, toRealQ_zero] at h
  linarith

@[simp] theorem toRealQ_one : toRealQ (1 : SBReal) = 1 := by
  have h := toRealQ_mul (1 : SBReal) 1
  rw [mul_one] at h
  have hne : toRealQ (1 : SBReal) ≠ 0 := by
    intro hc
    exact one_ne_zero (toRealQ_injective (by rw [hc, toRealQ_zero]) : (1 : SBReal) = 0)
  have hz : toRealQ (1 : SBReal) * (toRealQ (1 : SBReal) - 1) = 0 := by nlinarith [h]
  rcases mul_eq_zero.1 hz with h1 | h1
  · exact absurd h1 hne
  · linarith

@[simp] theorem toRealQ_inv (a : SBReal) : toRealQ a⁻¹ = (toRealQ a)⁻¹ := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · have hne : toRealQ a ≠ 0 := fun hc => ha (toRealQ_injective (by rw [hc, toRealQ_zero]))
    have h := toRealQ_mul a a⁻¹
    rw [mul_inv_cancel₀ ha, toRealQ_one] at h
    field_simp at h ⊢
    linarith [h]

/-! ### The field axioms

Every one is now a one-liner: push through `toRealQ`, which is injective, and
quote the corresponding fact about `ℝ`. Once the two theorems above are proved,
none of these is doing any work — which is the point. They are stated in full so
that the skeleton records exactly what "intrinsic `+` and `×` make this a field"
is committed to. -/

theorem add'_comm (a b : SBReal) : add' a b = add' b a :=
  toRealQ_injective (by rw [toRealQ_add', toRealQ_add', add_comm])

theorem add'_assoc (a b c : SBReal) : add' (add' a b) c = add' a (add' b c) :=
  toRealQ_injective (by rw [toRealQ_add', toRealQ_add', toRealQ_add', toRealQ_add', add_assoc])

theorem add'_zero (a : SBReal) : add' a 0 = a :=
  toRealQ_injective (by rw [toRealQ_add']; simp)

theorem add'_left_neg (a : SBReal) : add' (-a) a = 0 :=
  toRealQ_injective (by rw [toRealQ_add']; simp)

theorem mul'_comm (a b : SBReal) : mul' a b = mul' b a :=
  toRealQ_injective (by rw [toRealQ_mul', toRealQ_mul', mul_comm])

theorem mul'_assoc (a b c : SBReal) : mul' (mul' a b) c = mul' a (mul' b c) :=
  toRealQ_injective (by rw [toRealQ_mul', toRealQ_mul', toRealQ_mul', toRealQ_mul', mul_assoc])

theorem mul'_one (a : SBReal) : mul' a 1 = a :=
  toRealQ_injective (by rw [toRealQ_mul']; simp)

theorem mul'_zero (a : SBReal) : mul' a 0 = 0 :=
  toRealQ_injective (by rw [toRealQ_mul']; simp)

theorem left_distrib' (a b c : SBReal) : mul' a (add' b c) = add' (mul' a b) (mul' a c) :=
  toRealQ_injective (by rw [toRealQ_mul', toRealQ_add', toRealQ_add', toRealQ_mul', toRealQ_mul',
    mul_add])

theorem mul'_inv_cancel {a : SBReal} (ha : a ≠ 0) : mul' a a⁻¹ = 1 := by
  have hne : toRealQ a ≠ 0 := fun hc => ha (toRealQ_injective (by rw [hc, toRealQ_zero]))
  refine toRealQ_injective ?_
  rw [toRealQ_mul', toRealQ_inv, toRealQ_one, mul_inv_cancel₀ hne]

/-! ### The operations are the transported ones

The bridge back: `add'` and `mul'` are `+` and `*`. So installing them as the
`Field` instance changes no theorem — it only changes what the definition
mentions. -/

theorem add'_eq_add (a b : SBReal) : add' a b = a + b :=
  toRealQ_injective (by rw [toRealQ_add', toRealQ_add])

theorem mul'_eq_mul (a b : SBReal) : mul' a b = a * b :=
  toRealQ_injective (by rw [toRealQ_mul', toRealQ_mul])

end SternBrocot
