/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Field
import SternBrocot.IntrinsicCore

/-!
# Intrinsic `+` and `×`

`Field.lean` transports the field structure from `ℝ` along `orderIsoReal`. By
uniqueness of complete ordered fields that transport has no freedom in it — and
`toRealQ_add_eq_sSup` proves it concretely, showing `+` is pinned down by the
order alone. But the *definition* still mentions `ℝ`. This file closes that: it
defines `+` and `×` on the carrier itself, with no `ℝ` anywhere in the
definitions.

**Status: complete, no `sorry`.** `+` and `×` are defined without mentioning
`ℝ`, all ten field axioms are proved, and `add'_eq_add` / `mul'_eq_mul` show they
are the operations `Field.lean` transported — so installing them as the instance
would change no existing theorem.

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

## How the proofs go

Everything rests on two theorems, `toReal_addRaw` and `toReal_mulRaw`, stated at
the *raw* level: the supremum has the value it should. Each is proved by
antisymmetry, and both halves are the same move — a rational strictly on the
wrong side of the supremum is exhibited either as an upper bound of the cut
(contradicting `slexSup_least`) or as a member of it (contradicting
`slexSup_upperBound`).

Stating them raw rather than on the quotient is what makes the rest collapse.
The congruence lemmas are `toReal_injective` applied to them — **not** a
comparison of cuts, which genuinely fails: when the lower element of an adjacent
pair happens to be a rational point, the two cuts differ by exactly that point.
And the quotient versions are `Quotient.inductionOn`. From there every field
axiom is one line.

It is worth being precise about what this does and does not achieve. The
**definitions** of `+` and `×` never mention `ℝ`; the **proofs** of the axioms
do, via `toReal`. The stronger statement — that the axioms are provable without
`ℝ` at all, by density of the nodes and continuity — is a further step, and it
needs different proofs, not different definitions. Everything below is already
arranged so that swapping them in changes nothing else.
-/

open Set

namespace SternBrocot

/-- **The specification of `ratPoint`.** Not used in any definition — it is the
bridge that lets the rest of the file be checked against `ℝ`. -/
theorem toReal_ratPoint (q : ℚ) : toReal (ratPoint q) = (q : ℝ) := by
  classical
  unfold ratPoint
  split_ifs with hq
  · rw [toReal_of_pos (none_notMem_lift _), magnitude_of_pos (none_notMem_lift _), finPart_lift,
      toReal₀_toSet, nodeValue_toPath hq]
  · have hq' : (0 : ℚ) ≤ -q := by linarith [not_le.1 hq]
    rw [toReal_of_neg (by simp), magnitude_of_neg (by simp), finPart_neg, finPart_lift,
      compl_compl, toReal₀_toSet, nodeValue_toPath hq']
    push_cast
    ring

/-! ### The agreement theorem for addition

This is the load-bearing lemma, and it is stated at the *raw* level rather than
on the quotient because everything else falls out of it: the congruence is
`toReal_injective`, and the quotient version is `Quotient.induction`. -/

/-- A rational strictly below a point sits strictly below it. -/
theorem ratPoint_slexLt {p : ℚ} {a : Signed} (ha : IsFinite a) (h : (p : ℝ) < toReal a) :
    ratPoint p <ₛ a :=
  slexLt_of_toReal_lt (isFinite_ratPoint p) ha (by rw [toReal_ratPoint]; exact h)

/-- ...and conversely its value does not exceed the point's. Only `≤`, because
the rational point may *be* the point. -/
theorem le_toReal_of_ratPoint_slexLt {p : ℚ} {a : Signed} (ha : IsFinite a)
    (h : ratPoint p <ₛ a) : (p : ℝ) ≤ toReal a := by
  have := toReal_mono h (isFinite_ratPoint p) ha
  rwa [toReal_ratPoint] at this

/-- **Intrinsic addition computes addition.** Both halves are the same move: a
rational strictly on the wrong side of the supremum is exhibited either as an
upper bound of the cut (contradicting leastness) or as a member of it
(contradicting upper-boundedness). -/
theorem toReal_addRaw {a b : Signed} (ha : IsFinite a) (hb : IsFinite b) :
    toReal (addRaw a b) = toReal a + toReal b := by
  have hfin := isFinite_addRaw ha hb
  refine le_antisymm ?_ ?_
  · by_contra hcon
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (not_le.1 hcon)
    have hub : ∀ z ∈ addCut a b, ¬ (ratPoint r <ₛ z) := by
      rintro z ⟨p, q, hp, hq, rfl⟩ hlt
      have hpA := le_toReal_of_ratPoint_slexLt ha hp
      have hqB := le_toReal_of_ratPoint_slexLt hb hq
      have hr' := le_toReal_of_ratPoint_slexLt (isFinite_ratPoint (p + q)) hlt
      rw [toReal_ratPoint] at hr'
      push_cast at hr'
      linarith
    exact slexSup_least (addCut a b) (ratPoint r) hub
      (slexLt_of_toReal_lt (isFinite_ratPoint r) hfin (by rw [toReal_ratPoint]; exact hr2))
  · by_contra hcon
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (not_le.1 hcon)
    obtain ⟨r₁, hr₁1, hr₁2⟩ :=
      exists_rat_btwn (show toReal a - (toReal a + toReal b - (r : ℝ)) < toReal a by linarith)
    have hmem : ratPoint r ∈ addCut a b := by
      refine ⟨r₁, r - r₁, ratPoint_slexLt ha hr₁2, ratPoint_slexLt hb ?_, by congr 1; ring⟩
      push_cast
      linarith
    exact slexSup_upperBound (addCut a b) (ratPoint r) hmem
      (slexLt_of_toReal_lt hfin (isFinite_ratPoint r) (by rw [toReal_ratPoint]; exact hr1))

/-- **Addition respects the quotient.** Not by comparing cuts — those genuinely
differ, by one point, when the lower element of an adjacent pair happens to be a
rational point. It is `toReal_injective` applied to `toReal_addRaw`. -/
theorem addRaw_congr {a a' b b' : Signed} (ha : IsFinite a) (ha' : IsFinite a')
    (hb : IsFinite b) (hb' : IsFinite b') (hea : SEqv a a') (heb : SEqv b b') :
    SEqv (addRaw a b) (addRaw a' b') :=
  toReal_injective (isFinite_addRaw ha hb) (isFinite_addRaw ha' hb')
    (by rw [toReal_addRaw ha hb, toReal_addRaw ha' hb', toReal_of_seqv hea,
      toReal_of_seqv heb])

/-! ### The agreement theorem for multiplication

The supremum formula is monotone only on the nonnegative cone, so `mulRaw`
splits on the signs and hands `mulRawPos` two arguments of nonnegative value.
That is all `toReal_mulRawPos` ever needs to assume. -/

theorem toReal_le_of_not_slexLt {x y : Signed} (hx : IsFinite x) (hy : IsFinite y)
    (h : ¬ (x <ₛ y)) : toReal y ≤ toReal x := by
  rcases slexLt_trichotomy x y with h1 | rfl | h1
  · exact absurd h1 h
  · exact le_rfl
  · exact toReal_mono h1 hy hx

/-- **On the nonnegative cone, the supremum formula computes the product.** -/
theorem toReal_mulRawPos {a b : Signed} (ha : IsFinite a) (hb : IsFinite b)
    (hA : 0 ≤ toReal a) (hB : 0 ≤ toReal b) :
    toReal (mulRawPos a b) = toReal a * toReal b := by
  have hfin := isFinite_mulRawPos ha hb
  have hmem0 : ratPoint 0 ∈ mulCut a b := Or.inl rfl
  have hlow0 : 0 ≤ toReal (mulRawPos a b) := by
    have h1 := toReal_le_of_not_slexLt hfin (isFinite_ratPoint 0)
      (slexSup_upperBound (mulCut a b) (ratPoint 0) hmem0)
    rw [toReal_ratPoint] at h1
    push_cast at h1
    exact h1
  -- the degenerate cases: one factor is zero, and then so is the supremum
  have hzero : ∀ {c d : Signed}, IsFinite c → IsFinite d → toReal c = 0 →
      toReal (mulRawPos c d) = 0 := by
    intro c d hc hd hc0
    have hfin' := isFinite_mulRawPos hc hd
    have hub : ∀ z ∈ mulCut c d, ¬ (ratPoint 0 <ₛ z) := by
      rintro z (rfl | ⟨p, q, hp0, hq0, hpa, hqb, rfl⟩) hlt
      · exact slexLt_irrefl _ hlt
      · have hpA := le_toReal_of_ratPoint_slexLt hc hpa
        rw [hc0] at hpA
        have hp0' : (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp0
        have hp : p = 0 := by
          have : (p : ℝ) = 0 := le_antisymm hpA hp0'
          exact_mod_cast this
        rw [hp, zero_mul] at hlt
        exact slexLt_irrefl _ hlt
    have h2 := toReal_le_of_not_slexLt (isFinite_ratPoint 0) hfin'
      (slexSup_least (mulCut c d) (ratPoint 0) hub)
    rw [toReal_ratPoint] at h2
    push_cast at h2
    have h3 : 0 ≤ toReal (mulRawPos c d) := by
      have h4 := toReal_le_of_not_slexLt hfin' (isFinite_ratPoint 0)
        (slexSup_upperBound (mulCut c d) (ratPoint 0) (Or.inl rfl))
      rw [toReal_ratPoint] at h4
      push_cast at h4
      exact h4
    linarith
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · rw [hzero ha hb hA0.symm, ← hA0, zero_mul]
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · -- symmetric, but `mulCut` is not symmetric in form, so redo the bound
    have hub : ∀ z ∈ mulCut a b, ¬ (ratPoint 0 <ₛ z) := by
      rintro z (rfl | ⟨p, q, hp0, hq0, hpa, hqb, rfl⟩) hlt
      · exact slexLt_irrefl _ hlt
      · have hqB := le_toReal_of_ratPoint_slexLt hb hqb
        rw [← hB0] at hqB
        have hq0' : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
        have hq : q = 0 := by
          have : (q : ℝ) = 0 := le_antisymm hqB hq0'
          exact_mod_cast this
        rw [hq, mul_zero] at hlt
        exact slexLt_irrefl _ hlt
    have h2 := toReal_le_of_not_slexLt (isFinite_ratPoint 0) hfin
      (slexSup_least (mulCut a b) (ratPoint 0) hub)
    rw [toReal_ratPoint] at h2
    push_cast at h2
    rw [← hB0, mul_zero]
    linarith
  -- both values strictly positive
  refine le_antisymm ?_ ?_
  · by_contra hcon
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (not_le.1 hcon)
    have hub : ∀ z ∈ mulCut a b, ¬ (ratPoint r <ₛ z) := by
      rintro z (rfl | ⟨p, q, hp0, hq0, hpa, hqb, rfl⟩) hlt
      · have h1 := le_toReal_of_ratPoint_slexLt (isFinite_ratPoint 0) hlt
        rw [toReal_ratPoint] at h1
        push_cast at h1
        nlinarith [mul_pos hApos hBpos]
      · have hpA := le_toReal_of_ratPoint_slexLt ha hpa
        have hqB := le_toReal_of_ratPoint_slexLt hb hqb
        have hr' := le_toReal_of_ratPoint_slexLt (isFinite_ratPoint (p * q)) hlt
        rw [toReal_ratPoint] at hr'
        push_cast at hr'
        have hp0' : (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp0
        have hq0' : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
        nlinarith
    exact slexSup_least (mulCut a b) (ratPoint r) hub
      (slexLt_of_toReal_lt (isFinite_ratPoint r) hfin (by rw [toReal_ratPoint]; exact hr2))
  · by_contra hcon
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (not_le.1 hcon)
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := le_trans hlow0 (le_of_lt hr1)
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn
      (show (r : ℝ) / toReal b < toReal a by rw [div_lt_iff₀ hBpos]; exact hr2)
    have hppos : (0 : ℝ) < (p : ℝ) :=
      lt_of_le_of_lt (div_nonneg hr0 (le_of_lt hBpos)) hp1
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
      (show (r : ℝ) / (p : ℝ) < toReal b by
        rw [div_lt_iff₀ hppos]
        rw [div_lt_iff₀ hBpos] at hp1
        linarith)
    have hqpos : (0 : ℝ) < (q : ℝ) :=
      lt_of_le_of_lt (div_nonneg hr0 (le_of_lt hppos)) hq1
    have hmem : ratPoint (p * q) ∈ mulCut a b :=
      Or.inr ⟨p, q, by exact_mod_cast hppos.le, by exact_mod_cast hqpos.le,
        ratPoint_slexLt ha hp2, ratPoint_slexLt hb hq2, rfl⟩
    refine slexSup_upperBound (mulCut a b) (ratPoint (p * q)) hmem
      (slexLt_of_toReal_lt hfin (isFinite_ratPoint (p * q)) ?_)
    rw [toReal_ratPoint]
    show toReal (mulRawPos a b) < ((p * q : ℚ) : ℝ)
    rw [div_lt_iff₀ hppos] at hq1
    have hstep : (r : ℝ) < ((p * q : ℚ) : ℝ) := by push_cast; nlinarith [hq1]
    linarith

/-- **Intrinsic multiplication computes multiplication.** -/
theorem toReal_mulRaw {a b : Signed} (ha : IsFinite a) (hb : IsFinite b) :
    toReal (mulRaw a b) = toReal a * toReal b := by
  classical
  have ha' : IsFinite (neg a) := isFinite_neg.2 ha
  have hb' : IsFinite (neg b) := isFinite_neg.2 hb
  unfold mulRaw
  split_ifs with hsa hsb hsb
  · have hA := toReal_nonpos_of_neg hsa
    have hB := toReal_nonpos_of_neg hsb
    rw [toReal_mulRawPos ha' hb' (by rw [toReal_neg]; linarith) (by rw [toReal_neg]; linarith),
      toReal_neg, toReal_neg]
    ring
  · have hA := toReal_nonpos_of_neg hsa
    have hB := toReal_nonneg_of_pos hsb
    rw [toReal_neg, toReal_mulRawPos ha' hb (by rw [toReal_neg]; linarith) hB, toReal_neg]
    ring
  · have hA := toReal_nonneg_of_pos hsa
    have hB := toReal_nonpos_of_neg hsb
    rw [toReal_neg, toReal_mulRawPos ha hb' hA (by rw [toReal_neg]; linarith), toReal_neg]
    ring
  · exact toReal_mulRawPos ha hb (toReal_nonneg_of_pos hsa) (toReal_nonneg_of_pos hsb)

/-- **Multiplication respects the quotient**, for the same reason addition does. -/
theorem mulRaw_congr {a a' b b' : Signed} (ha : IsFinite a) (ha' : IsFinite a')
    (hb : IsFinite b) (hb' : IsFinite b') (hea : SEqv a a') (heb : SEqv b b') :
    SEqv (mulRaw a b) (mulRaw a' b') :=
  toReal_injective (isFinite_mulRaw ha hb) (isFinite_mulRaw ha' hb')
    (by rw [toReal_mulRaw ha hb, toReal_mulRaw ha' hb', toReal_of_seqv hea,
      toReal_of_seqv heb])

/-- **Intrinsic addition on `SBReal`.** -/
noncomputable def add' : SBReal → SBReal → SBReal :=
  Quotient.lift₂ (fun a b : FinitePoint => mk (addRaw a.1 b.1) (isFinite_addRaw a.2 b.2))
    (fun a b a' b' h₁ h₂ => Quotient.sound (addRaw_congr a.2 a'.2 b.2 b'.2 h₁ h₂))

/-- **Intrinsic multiplication on `SBReal`.** -/
noncomputable def mul' : SBReal → SBReal → SBReal :=
  Quotient.lift₂ (fun a b : FinitePoint => mk (mulRaw a.1 b.1) (isFinite_mulRaw a.2 b.2))
    (fun a b a' b' h₁ h₂ => Quotient.sound (mulRaw_congr a.2 a'.2 b.2 b'.2 h₁ h₂))

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
  induction a using Quotient.inductionOn with
  | _ a =>
    induction b using Quotient.inductionOn with
    | _ b => exact toReal_addRaw a.2 b.2

theorem toRealQ_mul' (a b : SBReal) : toRealQ (mul' a b) = toRealQ a * toRealQ b := by
  induction a using Quotient.inductionOn with
  | _ a =>
    induction b using Quotient.inductionOn with
    | _ b => exact toReal_mulRaw a.2 b.2

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
