/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Degree
import SternBrocot.Shift
import SternBrocot.SignedToReal

/-!
# Lagrange: eventually periodic paths and algebraic degree two

Every real *is* a subset of `ω + 1` here (`exists_toReal_eq`), so "the continued
fraction of `x` is eventually periodic" is a property of that set — no algorithm
and no productivity result is needed to state it or to prove things about it.

## The correct statement

Classical Lagrange says: an *infinite* continued fraction is eventually periodic
iff its value is a quadratic irrational, the word "infinite" quietly excluding
the rationals. That exclusion does **not** survive translation. In this encoding
a rational has an eventually **constant** path — all `0`s, or all `1`s for the
other representative of the same class — and eventually constant is a special
case of eventually periodic. So the true statement is

> the path of `x` is eventually periodic **iff** `[ℚ(Φ₀ x) : ℚ] ≤ 2`

— rational *or* quadratic irrational. Stating it as "iff quadratic irrational"
would be false, and would compile perfectly well as a skeleton.

## What is proved here

* `SternBrocot.degLeTwo_of_eventuallyPeriodic` — **the forward direction**:
  eventually periodic ⟹ degree ≤ 2. Periodicity makes the value a fixed point
  of the Möbius map of the repeating word, which lies in `SL₂(ℤ)`
  (`pathMat_det`); clearing denominators gives the quadratic, and the
  coefficients are not all zero because a nonempty word is never the identity
  matrix (`pathMat_ne_one`).
* `SternBrocot.eventuallyConstant_iff_rat` — the degree-one case, both ways:
  the path is eventually constant iff the value is rational. This is the
  analogue of Mathlib's `GenContFract.terminates_iff_rat`.
* `SternBrocot.eventuallyPeriodic_of_rat` — hence the converse holds for
  rationals.
* `SternBrocot.finrank_adjoin_le_two_of_eventuallyPeriodic` — the same statement
  read as `[ℚ(Φ₀ x) : ℚ] ≤ 2`, with
  `SternBrocot.finiteDimensional_of_eventuallyPeriodic` alongside it, which is
  what stops the bound being vacuous (`Degree.lean` explains why).
* `SternBrocot.degLeTwo_toReal_of_eventuallyPeriodic` — the signed version, on
  all of `ℝ` rather than `ℝ≥0`.

## What is not proved here

The remaining half of the converse — a quadratic **irrational** has an eventually
periodic path — is the hard direction of classical Lagrange, and is not in this
file. It needs the reduction theory of binary quadratic forms: the forms carried
along the path have bounded coefficients, so some complete quotient repeats.

One thing to know before attempting it. The naive bound on the transformed form
`q(a, c)` is `|A|(1/d² + (c/d)|t - t'|)`, and `c/d` is **not** bounded along a
bit path — the prefix `L^n` has `c/d = n`. The classical argument survives only
because convergent denominators satisfy `qₙ ≤ qₙ₊₁`, which the prefixes in the
middle of a run do not, so the pigeonhole has to run on the subsequence of run
boundaries rather than on every shift. Nothing here depends on any of it.
-/

open Set

namespace SternBrocot

/-! ### Periodicity -/

/-- The path of `x` is **eventually periodic**: some shift of `x` is fixed by a
further nonzero shift. -/
def EventuallyPeriodic (x : Set ℕ) : Prop :=
  ∃ k p : ℕ, 0 < p ∧ shift^[p] (shift^[k] x) = shift^[k] x

/-- The path of `x` is **eventually constant**: all `0`s from some point on, or
all `1`s. These are the two representatives of a rational. -/
def EventuallyConstant (x : Set ℕ) : Prop :=
  ∃ N : ℕ, (∀ n, N ≤ n → n ∉ x) ∨ (∀ n, N ≤ n → n ∈ x)

theorem iterate_shift_eq_empty_iff {k : ℕ} {x : Set ℕ} :
    shift^[k] x = ∅ ↔ ∀ n, k ≤ n → n ∉ x := by
  rw [iterate_shift]
  constructor
  · intro h n hn hmem
    have : n - k ∈ {m | m + k ∈ x} := by
      simp only [Set.mem_setOf_eq, Nat.sub_add_cancel hn]; exact hmem
    rw [h] at this
    exact this
  · intro h
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact h _ (by omega)

/-- Eventually constant is a special case of eventually periodic: both `∅` and
`univ` are fixed by the shift. -/
theorem eventuallyPeriodic_of_eventuallyConstant {x : Set ℕ} (h : EventuallyConstant x) :
    EventuallyPeriodic x := by
  obtain ⟨N, h⟩ := h
  refine ⟨N, 1, one_pos, ?_⟩
  rcases h with h | h
  · rw [iterate_shift_eq_empty_iff.2 h]
    simp
  · rw [iterate_shift_eq_univ_iff.2 h]
    simp

/-! ### A nonempty word is never the identity

The nondegeneracy input. If the Möbius map of the repeating block were the
identity the "quadratic" would be `0 = 0`; it is not, because the two move
matrices generate a free monoid — concretely, the entry signs of `pathMat`
already rule it out. -/

theorem pathMat_ne_one {bs : List Bool} (h : bs ≠ []) : pathMat bs ≠ (1, 0, 0, 1) := by
  cases bs with
  | nil => exact absurd rfl h
  | cons b cs =>
    obtain ⟨ha, hb, hc, hd⟩ := pathMat_entries cs
    cases b
    · intro hc'
      simp only [pathMat, Prod.ext_iff] at hc'
      omega
    · intro hc'
      simp only [pathMat, Prod.ext_iff] at hc'
      omega

/-! ### The degenerate case: a path of all `1`s

`Φ₀` is junk at `∞`, so the Möbius recursion needs every shift to stay away from
`univ`. The points it excludes are exactly the cofinite ones — the upper
representatives of the rationals — and they are handled directly: such a point is
the right-hand side of a tail pair whose left-hand side is a node. -/

theorem exists_rat_of_eventually_mem {x : Set ℕ} (hx : x ≠ univ) :
    ∀ N : ℕ, (∀ n, N ≤ n → n ∈ x) → ∃ q : ℚ, toReal₀ x = q := by
  intro N
  induction N with
  | zero => exact fun h => absurd (eq_univ_of_forall fun n => h n (Nat.zero_le n)) hx
  | succ N ih =>
    intro h
    by_cases hN : N ∈ x
    · refine ih fun n hn => ?_
      rcases Nat.eq_or_lt_of_le hn with rfl | hlt
      · exact hN
      · exact h n (by omega)
    · -- `x` is the cofinite side of the tail pair branching at `N`
      have hfin : ((x ∩ Iio N) ∪ {N}).Finite := by
        apply Set.Finite.subset (Set.finite_lt_nat (N + 1))
        rintro k (⟨-, hk⟩ | hk)
        · exact Nat.lt_succ_of_lt (mem_Iio.1 hk)
        · rw [mem_singleton_iff] at hk
          exact hk ▸ Nat.lt_succ_self N
      obtain ⟨bs, hbs⟩ := exists_path_of_finite hfin
      have hpair : TailPair (toSet bs) x := by
        refine ⟨N, ?_, ?_, ?_, hN, ?_⟩
        · intro k hk
          rw [hbs]
          simp only [Set.mem_union, Set.mem_inter_iff, mem_Iio, mem_singleton_iff]
          exact ⟨by rintro (⟨hkx, -⟩ | rfl); · exact hkx
                    · exact absurd hk (lt_irrefl _),
                 fun hkx => Or.inl ⟨hkx, hk⟩⟩
        · rw [hbs]; exact Or.inr rfl
        · intro k hk
          rw [hbs]
          simp only [Set.mem_union, Set.mem_inter_iff, mem_Iio, mem_singleton_iff]
          rintro (⟨-, hlt⟩ | rfl)
          · omega
          · omega
        · intro k hk
          exact h k (by omega)
      exact ⟨nodeValue bs, by rw [← toReal₀_of_tailPair hpair, toReal₀_toSet]⟩

theorem exists_rat_of_iterate_shift_univ {x : Set ℕ} (hx : x ≠ univ) {k : ℕ}
    (h : shift^[k] x = univ) : ∃ q : ℚ, toReal₀ x = q :=
  exists_rat_of_eventually_mem hx k (iterate_shift_eq_univ_iff.1 h)

/-! ### The forward direction -/

/-- **Eventually periodic paths have values of degree at most two.**

Let `y` be the shift at which the period starts and `w` the repeating block. Then
`applyPath w y = y`, so `Φ₀ y` is a *fixed point* of the Möbius map of `w`;
clearing the denominator turns that into `c t² + (d - a) t - b = 0`. The
coefficients cannot all vanish: `c = 0`, `b = 0` and `a = d` together with
`det = 1` and positive diagonal force `pathMat w = (1, 0, 0, 1)`, which
`pathMat_ne_one` rules out for a nonempty block. Finally the prefix before the
period is another Möbius map, and `DegLeTwo.mobius` carries the degree bound from
`Φ₀ y` back to `Φ₀ x`. -/
theorem degLeTwo_of_eventuallyPeriodic {x : Set ℕ} (hx : x ≠ univ)
    (h : EventuallyPeriodic x) : DegLeTwo (toReal₀ x) := by
  obtain ⟨k, p, hp, hper⟩ := h
  by_cases huniv : ∃ j, shift^[j] x = univ
  · obtain ⟨j, hj⟩ := huniv
    obtain ⟨q, hq⟩ := exists_rat_of_iterate_shift_univ hx hj
    exact (degLeTwo_of_rat q).of_eq hq
  simp only [not_exists] at huniv
  set y : Set ℕ := shift^[k] x with hydef
  have hyu : y ≠ univ := huniv k
  have hy0 : (0 : ℝ) ≤ toReal₀ y := toReal₀_nonneg y
  -- the repeating block, as a word
  obtain ⟨w, hwlen, hw⟩ := exists_applyPath y p
  rw [hper] at hw
  have hwne : w ≠ [] := by
    intro hc
    rw [hc] at hwlen
    simp at hwlen
    omega
  -- the value of `y` is a fixed point of the block's Möbius map
  have hfix : toReal₀ y = mobius (pathMat w) (toReal₀ y) := by
    conv_lhs => rw [← hw]
    exact toReal₀_applyPath w hyu
  have hden := pathMat_den_pos_real w hy0
  have hquad : (((pathMat w).2.2.1 : ℝ)) * toReal₀ y ^ 2 +
      (((pathMat w).2.2.2 : ℝ) - ((pathMat w).1 : ℝ)) * toReal₀ y - ((pathMat w).2.1 : ℝ) = 0 := by
    rw [mobius, eq_div_iff (ne_of_gt hden)] at hfix
    linear_combination hfix
  have hdegy : DegLeTwo (toReal₀ y) := by
    refine ⟨(pathMat w).2.2.1, (pathMat w).2.2.2 - (pathMat w).1, -(pathMat w).2.1, ?_, ?_⟩
    · rintro ⟨h1, h2, h3⟩
      obtain ⟨ha, hb, hc, hd⟩ := pathMat_entries w
      have hdet := pathMat_det w
      refine pathMat_ne_one hwne ?_
      have hb0 : (pathMat w).2.1 = 0 := by omega
      have had : (pathMat w).1 = (pathMat w).2.2.2 := by omega
      have ha1 : (pathMat w).1 = 1 := by nlinarith
      have : (pathMat w).2.2.2 = 1 := by omega
      rw [Prod.ext_iff, Prod.ext_iff, Prod.ext_iff]
      exact ⟨ha1, hb0, h1, this⟩
    · push_cast
      linear_combination hquad
  -- carry it back along the prefix
  obtain ⟨v, -, hv⟩ := exists_applyPath x k
  rw [← hydef] at hv
  have hvval : toReal₀ x = mobius (pathMat v) (toReal₀ y) := by
    conv_lhs => rw [← hv]
    exact toReal₀_applyPath v hyu
  have hvden := pathMat_den_pos_real v hy0
  refine hdegy.mobius (a := (pathMat v).1) (b := (pathMat v).2.1) (c := (pathMat v).2.2.1)
    (d := (pathMat v).2.2.2) (pathMat_det v) (ne_of_gt hvden) ?_
  rw [hvval, mobius, div_mul_cancel₀ _ (ne_of_gt hvden)]

/-! ### Degree one: eventually constant paths are exactly the rationals -/

/-- **The rational case, both ways.** A point of `P(ω)` other than `∞` has a
rational value iff its path is eventually constant.

Both representatives occur: a node has a path of eventually `0`s, and the other
side of its tail pair has a path of eventually `1`s. This is the analogue of
Mathlib's `GenContFract.terminates_iff_rat`. -/
theorem eventuallyConstant_iff_rat {x : Set ℕ} (hx : x ≠ univ) :
    EventuallyConstant x ↔ ∃ q : ℚ, toReal₀ x = q := by
  constructor
  · rintro ⟨N, h | h⟩
    · -- eventually `0`: `x` is finite, hence a node
      have hfin : x.Finite := by
        apply Set.Finite.subset (Set.finite_lt_nat N)
        intro n hn
        simp only [Set.mem_setOf_eq]
        by_contra hc
        exact h n (by omega) hn
      obtain ⟨bs, rfl⟩ := exists_path_of_finite hfin
      exact ⟨nodeValue bs, toReal₀_toSet bs⟩
    · exact exists_rat_of_eventually_mem hx N h
  · rintro ⟨q, hq⟩
    have hq0 : (0 : ℚ) ≤ q := by
      have := toReal₀_nonneg x
      rw [hq] at this
      exact_mod_cast this
    obtain ⟨cs, -, hcs⟩ := exists_canonical_of_nonneg hq0
    have hval : toReal₀ x = toReal₀ (toSet cs) := by rw [hq, toReal₀_toSet, hcs]
    rcases toReal₀_injective hx (toSet_ne_univ cs) hval with rfl | hpair | hpair
    · refine ⟨cs.length, Or.inl fun n hn hmem => ?_⟩
      exact absurd (mem_Iio.1 (toSet_subset_Iio cs hmem)) (by omega)
    · -- `x` is the lower side: it stops at the branch point
      obtain ⟨N, hN⟩ := hpair
      exact ⟨N + 1, Or.inl fun n hn => hN.left_top n (by omega)⟩
    · -- `x` is the upper side: it is full above the branch point
      obtain ⟨N, hN⟩ := hpair
      exact ⟨N + 1, Or.inr fun n hn => hN.right_tail n (by omega)⟩

/-- **The converse, for rationals.** Together with
`degLeTwo_of_eventuallyPeriodic` this settles the degree-one case of Lagrange in
both directions. -/
theorem eventuallyPeriodic_of_rat {x : Set ℕ} (hx : x ≠ univ) {q : ℚ}
    (h : toReal₀ x = q) : EventuallyPeriodic x :=
  eventuallyPeriodic_of_eventuallyConstant ((eventuallyConstant_iff_rat hx).2 ⟨q, h⟩)

/-! ### The statement in field-theoretic form -/

/-- **Lagrange, forward direction, as `[ℚ(x) : ℚ] ≤ 2`.** The companion
`finiteDimensional_of_eventuallyPeriodic` is what makes this say something:
`Module.finrank` is `0` on an infinite-dimensional space. -/
theorem finrank_adjoin_le_two_of_eventuallyPeriodic {x : Set ℕ} (hx : x ≠ univ)
    (h : EventuallyPeriodic x) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {toReal₀ x}) ≤ 2 :=
  (degLeTwo_of_eventuallyPeriodic hx h).finrank_adjoin_le

theorem finiteDimensional_of_eventuallyPeriodic {x : Set ℕ} (hx : x ≠ univ)
    (h : EventuallyPeriodic x) :
    FiniteDimensional ℚ (IntermediateField.adjoin ℚ {toReal₀ x}) :=
  (degLeTwo_of_eventuallyPeriodic hx h).finiteDimensional

/-! ### The signed version

`P(ω)` only carries the nonnegative reals. On `P(ω+1)` the stored bits are the
magnitude's path on the positive branch and its complement on the negative one,
and complementing a set neither creates nor destroys eventual periodicity, so
the statement transfers with a single extra lemma. -/

theorem shift_compl (x : Set ℕ) : shift xᶜ = (shift x)ᶜ := by
  ext n; simp

theorem iterate_shift_compl (k : ℕ) (x : Set ℕ) : shift^[k] xᶜ = (shift^[k] x)ᶜ := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, shift_compl, ih]

theorem EventuallyPeriodic.compl {x : Set ℕ} (h : EventuallyPeriodic x) :
    EventuallyPeriodic xᶜ := by
  obtain ⟨k, p, hp, hper⟩ := h
  refine ⟨k, p, hp, ?_⟩
  rw [iterate_shift_compl, iterate_shift_compl, hper]

/-- **The forward direction on all of `ℝ`.** `x` is a point of `P(ω+1)` other
than `±∞`, and the hypothesis is eventual periodicity of the *stored* bits. -/
theorem degLeTwo_toReal_of_eventuallyPeriodic {x : Signed} (hx : IsFinite x)
    (h : EventuallyPeriodic (finPart x)) : DegLeTwo (toReal x) := by
  by_cases hs : none ∈ x
  · have hmag : EventuallyPeriodic (magnitude x) := by
      rw [magnitude_of_neg hs]; exact h.compl
    rw [toReal_of_neg hs]
    exact DegLeTwo.neg (degLeTwo_of_eventuallyPeriodic hx hmag)
  · have hmag : EventuallyPeriodic (magnitude x) := by
      rw [magnitude_of_pos hs]; exact h
    rw [toReal_of_pos hs]
    exact degLeTwo_of_eventuallyPeriodic hx hmag

end SternBrocot
