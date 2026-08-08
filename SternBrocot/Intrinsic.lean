/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Field
import SternBrocot.GosperRat
import SternBrocot.Shift

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
  classical
  intro x hx
  unfold slexSup
  split_ifs with hpos
  · rintro (⟨hc, -⟩ | ⟨hs, hf⟩)
    · exact none_notMem_lift _ hc
    · have hxpos : none ∉ x := fun hc => none_notMem_lift _ (hs.2 hc)
      rw [finPart_lift] at hf
      exact lexSup_upperBound (posBits S) (finPart x) ⟨x, hx, hxpos, rfl⟩ hf
  · have hxneg : none ∈ x := by
      by_contra hcx
      exact hpos ⟨x, hx, hcx⟩
    rintro (⟨-, hc⟩ | ⟨-, hf⟩)
    · exact hc hxneg
    · rw [finPart_negLift] at hf
      exact lexSup_upperBound (allBits S) (finPart x) ⟨x, hx, rfl⟩ hf

/-- `slexSup S` is the least upper bound. In the all-negative case a positive
`v` is above it for free, which is the only place the sign split does any work. -/
theorem slexSup_least (S : Set Signed) (v : Signed) (hv : ∀ x ∈ S, ¬ (v <ₛ x)) :
    ¬ (v <ₛ slexSup S) := by
  classical
  unfold slexSup
  split_ifs with hpos
  · obtain ⟨x₀, hx₀S, hx₀⟩ := hpos
    rintro (⟨hvneg, -⟩ | ⟨hs, hf⟩)
    · exact hv x₀ hx₀S (Or.inl ⟨hvneg, hx₀⟩)
    · have hvpos : none ∉ v := fun hc => none_notMem_lift _ (hs.1 hc)
      rw [finPart_lift] at hf
      refine lexSup_least (posBits S) (finPart v) ?_ hf
      rintro y ⟨x, hxS, hxpos, rfl⟩
      intro hlt
      exact hv x hxS (Or.inr ⟨iff_of_false hvpos hxpos, hlt⟩)
  · rintro (⟨-, hc⟩ | ⟨hs, hf⟩)
    · exact hc (none_mem_negLift _)
    · have hvneg : none ∈ v := hs.2 (none_mem_negLift _)
      rw [finPart_negLift] at hf
      refine lexSup_least (allBits S) (finPart v) ?_ hf
      rintro y ⟨x, hxS, rfl⟩
      intro hlt
      have hxneg : none ∈ x := by
        by_contra hcx
        exact hpos ⟨x, hxS, hcx⟩
      exact hv x hxS (Or.inr ⟨iff_of_true hvneg hxneg, hlt⟩)

/-! ### The rationals as points, intrinsically

`toPath` is the Euclidean algorithm; `toSet` turns a word into a point; `neg` is
complement. Nothing here knows about `ℝ`. -/

open Classical in
/-- The point of `P(ω+1)` representing a rational. -/
noncomputable def ratPoint (q : ℚ) : Signed :=
  if 0 ≤ q then lift (toSet (toPath q)) else neg (lift (toSet (toPath (-q))))

theorem isFinite_ratPoint (q : ℚ) : IsFinite (ratPoint q) := by
  classical
  unfold ratPoint
  split_ifs with hq
  · show magnitude (lift (toSet (toPath q))) ≠ univ
    rw [magnitude_of_pos (none_notMem_lift _), finPart_lift]
    exact toSet_ne_univ _
  · show magnitude (neg (lift (toSet (toPath (-q))))) ≠ univ
    rw [magnitude_of_neg (by simp), finPart_neg, finPart_lift, compl_compl]
    exact toSet_ne_univ _

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

/-! ### The operations -/

/-- The set of rational-node sums lying strictly below `a` and `b`. -/
def addCut (a b : Signed) : Set Signed :=
  {z | ∃ p q : ℚ, ratPoint p <ₛ a ∧ ratPoint q <ₛ b ∧ z = ratPoint (p + q)}

/-- **Intrinsic addition on `P(ω+1)`**: the supremum of the sums of the nodes
below the two arguments. -/
noncomputable def addRaw (a b : Signed) : Signed := slexSup (addCut a b)

/-- The nonnegative part of the product cut.

**`ratPoint 0` has to be in it.** Without that disjunct the cut is empty when
either argument is `+0`, and the supremum of the empty set is `−∞`, not `+0` —
`slexSup ∅` takes the negative branch and lands on `{none}`. That would make
`mulRawPos` infinite exactly at zero. Adding the floor is the standard Dedekind
fix and costs nothing: `ratPoint 0 = ∅` is already the bottom of the cone. -/
def mulCut (a b : Signed) : Set Signed :=
  {z | z = ratPoint 0 ∨
    ∃ p q : ℚ, 0 ≤ p ∧ 0 ≤ q ∧ ratPoint p <ₛ a ∧ ratPoint q <ₛ b ∧ z = ratPoint (p * q)}

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

/-! ### The endpoints, and density of the rational points

`IsFinite` excludes exactly two points, and they do not look alike: `+∞` is
`lift univ` and `−∞` is `{none}`. That asymmetry is the mirrored convention
again — a negative point stores the *complement* of its magnitude, so the
negative infinity is the point with no finite bits at all. -/

theorem ratPoint_of_nonneg {q : ℚ} (hq : 0 ≤ q) : ratPoint q = lift (toSet (toPath q)) := by
  classical
  unfold ratPoint; rw [if_pos hq]

theorem ratPoint_of_neg {q : ℚ} (hq : ¬ 0 ≤ q) :
    ratPoint q = neg (lift (toSet (toPath (-q)))) := by
  classical
  unfold ratPoint; rw [if_neg hq]

/-- The two points `IsFinite` excludes. -/
theorem eq_top_or_bot_of_not_isFinite {x : Signed} (h : ¬ IsFinite x) :
    x = lift univ ∨ x = ({none} : Signed) := by
  rw [IsFinite, not_not] at h
  by_cases hs : none ∈ x
  · right
    rw [magnitude_of_neg hs] at h
    have hfp : finPart x = ∅ := by
      rw [← compl_univ, ← h, compl_compl]
    ext o
    cases o with
    | none => simpa using hs
    | some n =>
      have : n ∉ finPart x := by rw [hfp]; exact notMem_empty n
      simpa using this
  · left
    rw [magnitude_of_pos hs] at h
    ext o
    cases o with
    | none => simpa using hs
    | some n =>
      have : n ∈ finPart x := by rw [h]; exact mem_univ n
      simp only [mem_finPart] at this
      simp [lift, this]

/-- Everything finite is strictly below `+∞`. -/
theorem slexLt_top {x : Signed} (hx : IsFinite x) : x <ₛ lift (univ : Set ℕ) := by
  by_cases hs : none ∈ x
  · exact Or.inl ⟨hs, none_notMem_lift _⟩
  · refine Or.inr ⟨iff_of_false hs (none_notMem_lift _), ?_⟩
    rw [finPart_lift]
    rw [IsFinite, magnitude_of_pos hs] at hx
    exact lexLt_univ_of_ne hx

/-- Everything finite is strictly above `−∞`. -/
theorem bot_slexLt {x : Signed} (hx : IsFinite x) : ({none} : Signed) <ₛ x := by
  by_cases hs : none ∈ x
  · refine Or.inr ⟨iff_of_true rfl hs, ?_⟩
    rw [finPart_singleton_none]
    rw [IsFinite, magnitude_of_neg hs] at hx
    exact empty_lexLt fun hc => hx (by rw [hc, compl_empty])
  · exact Or.inl ⟨rfl, hs⟩

/-- **A rational point above any finite point.** -/
theorem exists_lt_ratPoint {a : Signed} (ha : IsFinite a) : ∃ p : ℚ, a <ₛ ratPoint p := by
  by_cases hs : none ∈ a
  · exact ⟨0, Or.inl ⟨hs, by rw [ratPoint_of_nonneg le_rfl]; exact none_notMem_lift _⟩⟩
  · rw [IsFinite, magnitude_of_pos hs] at ha
    obtain ⟨w, hw⟩ := exists_node_above ha
    refine ⟨nodeValue w + 1, ?_⟩
    have hp : (0 : ℚ) ≤ nodeValue w + 1 := by linarith [nodeValue_nonneg w]
    rw [ratPoint_of_nonneg hp]
    refine Or.inr ⟨iff_of_false hs (none_notMem_lift _), ?_⟩
    rw [finPart_lift]
    refine lexLt_trans hw ((lexLt_toSet_iff w _).2 ?_)
    rw [nodeValue_toPath hp]
    linarith

/-- **A rational point below any finite point.** -/
theorem exists_ratPoint_lt {a : Signed} (ha : IsFinite a) : ∃ p : ℚ, ratPoint p <ₛ a := by
  by_cases hs : none ∈ a
  · rw [IsFinite, magnitude_of_neg hs] at ha
    obtain ⟨w, hw⟩ := exists_node_above ha
    have hp : (0 : ℚ) ≤ nodeValue w + 1 := by linarith [nodeValue_nonneg w]
    refine ⟨-(nodeValue w + 1), ?_⟩
    have hneg : ¬ (0 : ℚ) ≤ -(nodeValue w + 1) := by
      have := nodeValue_nonneg w; linarith
    rw [ratPoint_of_neg hneg, _root_.neg_neg]
    refine Or.inr ⟨iff_of_true (by simp) hs, ?_⟩
    rw [finPart_neg, finPart_lift]
    have hlt : (finPart a)ᶜ <ₗ toSet (toPath (nodeValue w + 1)) :=
      lexLt_trans hw ((lexLt_toSet_iff w _).2 (by rw [nodeValue_toPath hp]; linarith))
    have := compl_lexLt_compl (x := toSet (toPath (nodeValue w + 1))) (y := (finPart a)ᶜ)
    rw [compl_compl] at this
    exact this.2 hlt
  · exact ⟨-1, Or.inl ⟨by rw [ratPoint_of_neg (by norm_num)]; simp, hs⟩⟩

/-! ### Finiteness of the operations -/

/-- A supremum of finite points with a finite upper bound is finite. -/
theorem isFinite_slexSup {S : Set Signed} {z u : Signed} (hz : z ∈ S) (hzf : IsFinite z)
    (hu : IsFinite u) (hub : ∀ x ∈ S, ¬ (u <ₛ x)) : IsFinite (slexSup S) := by
  by_contra hbad
  rcases eq_top_or_bot_of_not_isFinite hbad with htop | hbot
  · refine slexSup_least S u hub ?_
    rw [htop]
    exact slexLt_top hu
  · refine slexSup_upperBound S z hz ?_
    rw [hbot]
    exact bot_slexLt hzf

/-- `ratPoint` reflects the order, via `toReal_mono` — enough for the bounds
below, which never need strictness. -/
theorem ratPoint_le_of_slexLt {p q : ℚ} (h : ratPoint p <ₛ ratPoint q) : p ≤ q := by
  have := toReal_mono h (isFinite_ratPoint p) (isFinite_ratPoint q)
  rw [toReal_ratPoint, toReal_ratPoint] at this
  exact_mod_cast this

theorem isFinite_addRaw {a b : Signed} (ha : IsFinite a) (hb : IsFinite b) :
    IsFinite (addRaw a b) := by
  obtain ⟨p₀, hp₀⟩ := exists_ratPoint_lt ha
  obtain ⟨q₀, hq₀⟩ := exists_ratPoint_lt hb
  obtain ⟨P, hP⟩ := exists_lt_ratPoint ha
  obtain ⟨Q, hQ⟩ := exists_lt_ratPoint hb
  refine isFinite_slexSup (z := ratPoint (p₀ + q₀)) ⟨p₀, q₀, hp₀, hq₀, rfl⟩
    (isFinite_ratPoint _) (u := ratPoint (P + Q)) (isFinite_ratPoint _) ?_
  rintro x ⟨p, q, hpa, hqb, rfl⟩ hlt
  have hp : p ≤ P := ratPoint_le_of_slexLt (slexLt_trans hpa hP)
  have hq : q ≤ Q := ratPoint_le_of_slexLt (slexLt_trans hqb hQ)
  have hge : P + Q ≤ p + q := ratPoint_le_of_slexLt hlt
  have heq : p + q = P + Q := le_antisymm (by linarith) hge
  rw [heq] at hlt
  exact slexLt_irrefl _ hlt

theorem isFinite_mulRawPos {a b : Signed} (ha : IsFinite a) (hb : IsFinite b) :
    IsFinite (mulRawPos a b) := by
  obtain ⟨P, hP⟩ := exists_lt_ratPoint ha
  obtain ⟨Q, hQ⟩ := exists_lt_ratPoint hb
  -- the bounds may as well be nonnegative
  refine isFinite_slexSup (z := ratPoint 0) (Or.inl rfl) (isFinite_ratPoint _)
    (u := ratPoint (max P 0 * max Q 0)) (isFinite_ratPoint _) ?_
  have hP0 : (0 : ℚ) ≤ max P 0 := le_max_right _ _
  have hQ0 : (0 : ℚ) ≤ max Q 0 := le_max_right _ _
  rintro x (rfl | ⟨p, q, hp0, hq0, hpa, hqb, rfl⟩) hlt
  · have := ratPoint_le_of_slexLt hlt
    have hzero : max P 0 * max Q 0 = 0 := le_antisymm this (by positivity)
    rw [hzero] at hlt
    exact slexLt_irrefl _ hlt
  · have hp : p ≤ max P 0 := le_trans (ratPoint_le_of_slexLt (slexLt_trans hpa hP))
      (le_max_left _ _)
    have hq : q ≤ max Q 0 := le_trans (ratPoint_le_of_slexLt (slexLt_trans hqb hQ))
      (le_max_left _ _)
    have hge : max P 0 * max Q 0 ≤ p * q := ratPoint_le_of_slexLt hlt
    have hle : p * q ≤ max P 0 * max Q 0 := by nlinarith
    rw [le_antisymm hle hge] at hlt
    exact slexLt_irrefl _ hlt

theorem isFinite_mulRaw {a b : Signed} (ha : IsFinite a) (hb : IsFinite b) :
    IsFinite (mulRaw a b) := by
  classical
  have ha' : IsFinite (neg a) := isFinite_neg.2 ha
  have hb' : IsFinite (neg b) := isFinite_neg.2 hb
  unfold mulRaw
  split_ifs
  · exact isFinite_mulRawPos ha' hb'
  · exact isFinite_neg.2 (isFinite_mulRawPos ha' hb)
  · exact isFinite_neg.2 (isFinite_mulRawPos ha hb')
  · exact isFinite_mulRawPos ha hb

/-! ### The agreement theorem for addition

This is the load-bearing lemma, and it is stated at the *raw* level rather than
on the quotient because everything else falls out of it: the congruence is
`toReal_injective`, and the quotient version is `Quotient.induction`. -/

/-- The converse of `toReal_mono`, by trichotomy. Non-strict monotonicity is all
`SignedToReal` gives — the quotient is why — but reflecting a *strict*
inequality needs nothing more. -/
theorem slexLt_of_toReal_lt {x y : Signed} (hx : IsFinite x) (hy : IsFinite y)
    (h : toReal x < toReal y) : x <ₛ y := by
  rcases slexLt_trichotomy x y with h1 | rfl | h1
  · exact h1
  · exact absurd h (lt_irrefl _)
  · exact absurd (toReal_mono h1 hy hx) (not_le.2 h)

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
