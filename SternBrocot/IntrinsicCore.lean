/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Magnitude
import SternBrocot.GosperRat

/-!
# Intrinsic `+` and `×`: the definitions

**`ℝ`-free**, and verifiably so: `Real` is not reachable through this file's
transitive import closure. That is the whole point of splitting it off. The
claim "the construction never mentions `ℝ`" is now checkable from the import
graph rather than by reading proofs.

Three layers, all here.

1. **A supremum on `P(ω+1)`.** `Completeness.lean` already builds `lexSup` on
   `P(ω)`. The signed order is "negatives below positives, same sign by forward
   lex on the stored bits", so a supremum needs exactly one case split, and
   `slexSup` is it.

2. **The rationals, intrinsically.** `GosperRat.toPath` is the Euclidean
   algorithm as a function; `Bridge.toSet` makes it a point; `neg` — complement —
   carries it across the sign. `ratPoint_slexLt_iff` proves it is an order
   embedding of `ℚ`, again with no `ℝ`.

3. **The operations, as suprema over the nodes.**

       a + b = sup { ratPoint (p + q) | ratPoint p <ₛ a, ratPoint q <ₛ b }

   with `p q : ℚ` and the inner `+` **rational** addition, so nothing is
   circular. Multiplication is the same formula on the nonnegative cone,
   extended by `neg`, because the supremum formula is monotone only there.

`Intrinsic.lean` sits on top of this and proves, using `ℝ`, that these
operations *are* the ones `Field.lean` transported. That is a theorem about the
definitions, not part of them.

## The `mulCut` floor

`ratPoint 0` is a member of `mulCut` unconditionally. Without it the cut is
empty when either argument is `+0`, and `slexSup ∅` is not `+0` — with no
positive member it takes the negative branch and returns `{none}`, which is
`−∞`. That would make `mulRawPos` infinite exactly where the product is zero.
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

/-! ### `ratPoint` is an order embedding

Proved here **without `ℝ`**. It is `lexLt_toSet_iff` — the tree orders its nodes
by their values — plus the sign split, with `compl_lexLt_compl` handling the
negative branch, where the stored bits are the complement and the order reverses
twice. -/

theorem ratPoint_strictMono {p q : ℚ} (h : p < q) : ratPoint p <ₛ ratPoint q := by
  rcases le_or_gt 0 p with hp | hp
  · have hq : (0 : ℚ) ≤ q := le_of_lt (lt_of_le_of_lt hp h)
    rw [ratPoint_of_nonneg hp, ratPoint_of_nonneg hq, lift_slexLt_iff]
    refine (lexLt_toSet_iff _ _).2 ?_
    rw [nodeValue_toPath hp, nodeValue_toPath hq]
    exact h
  · rcases le_or_gt 0 q with hq | hq
    · rw [ratPoint_of_neg (not_le.2 hp), ratPoint_of_nonneg hq]
      exact Or.inl ⟨by simp, none_notMem_lift _⟩
    · have hp' : (0 : ℚ) ≤ -p := by linarith
      have hq' : (0 : ℚ) ≤ -q := by linarith
      rw [ratPoint_of_neg (not_le.2 hp), ratPoint_of_neg (not_le.2 hq)]
      refine Or.inr ⟨iff_of_true (by simp) (by simp), ?_⟩
      rw [finPart_neg, finPart_neg, finPart_lift, finPart_lift, compl_lexLt_compl]
      refine (lexLt_toSet_iff _ _).2 ?_
      rw [nodeValue_toPath hq', nodeValue_toPath hp']
      linarith

/-- **`ratPoint` is an order embedding of `ℚ`.** -/
theorem ratPoint_slexLt_iff {p q : ℚ} : ratPoint p <ₛ ratPoint q ↔ p < q := by
  refine ⟨fun hlt => ?_, ratPoint_strictMono⟩
  by_contra hc
  rcases eq_or_lt_of_le (not_lt.1 hc) with rfl | hqp
  · exact slexLt_irrefl _ hlt
  · exact slexLt_asymm hlt (ratPoint_strictMono hqp)

theorem ratPoint_le_of_slexLt {p q : ℚ} (h : ratPoint p <ₛ ratPoint q) : p ≤ q :=
  le_of_lt (ratPoint_slexLt_iff.1 h)

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

end SternBrocot
