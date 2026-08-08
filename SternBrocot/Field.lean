/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.SignedToReal
import Mathlib.Algebra.Field.TransferInstance

/-!
# `SBReal`: the reals as subsets of `ω + 1`

The finite points of `P(ω + 1)`, modulo the quotient that collapses adjacent
pairs. `toReal` descends to a **bijection** onto `ℝ`, so this carrier is the real
line — not merely a set of the right size, but order-isomorphically the reals,
with reciprocal and negation given by set complement.

## What is transported, and what that does not mean

Both instances are built by transport. `LinearOrder SBReal` is
`LinearOrder.lift' toRealQ`, so `a ≤ b` unfolds definitionally to
`toRealQ a ≤ toRealQ b` — a comparison of two real numbers; `le_iff_toRealQ_le`
below is literally `Iff.rfl`. The field structure is `equivReal.field`.

For the **order** that is now a statement about construction only, not about
content: `mk_lt_mk_iff` proves

  `mk a ha < mk b hb ↔ (a <ₛ b ∧ ¬ SEqv a b)`

with no `ℝ` on either side. `SLexLt` is built in `Order.lean` and
`SignedOrder.lean` from the bit strings alone, so the order relation on the
quotient *is* the lex order, however the instance was assembled. This matters
because `exists_isLUB` and `instIsStrictOrderedRingSBReal` are statements about
that relation — without `mk_lt_mk_iff` they would be facts about `ℝ`'s order
wearing a different name.

For the **field operations** the corresponding statement is not proved here.
`Intrinsic.lean` defines `ℝ`-free `+` and `×` and shows they agree with these
(`add'_eq_add`, `mul'_eq_mul`), which is the analogous content, but the axioms
are still proved through `toReal` and the instance is still the transported one.

Do not restore the sentence "the order is intrinsic" as a description of the
*instance* — it was here for several commits and was false in exactly the way
`mk_lt_mk_iff` now repairs. Cite the theorem instead.

## Main results

* `SternBrocot.SBReal` — the carrier.
* `SternBrocot.orderIsoReal : SBReal ≃o ℝ` — **the order isomorphism.**
* `SternBrocot.mk_lt_mk_iff` — **the order is the lex order**, `ℝ`-free on both
  sides of the `iff`.
* `SternBrocot.instFieldSBReal` — the transported field structure.
-/

open Set

namespace SternBrocot

/-! ### The quotient carrier -/

/-- Finiteness survives the quotient: neither `univ` nor `∅` lies in a tail pair,
so a tail step cannot move a point to or from an infinity, and the zero pair is
finite on both sides. -/
theorem isFinite_of_seqv {a b : Signed} (h : SEqv a b) (ha : IsFinite a) : IsFinite b := by
  have hcompl : ∀ s : Set ℕ, sᶜ = univ → s = ∅ := by
    intro s hs; rw [← compl_compl s, hs, compl_univ]
  rcases h with (rfl | hp | hp) | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ha
  · -- `STailPair a b`: `b` is on a tail pair, and neither `∅` nor `univ` ever is
    by_cases hs : none ∈ a
    · have hs' : none ∈ b := hp.1.1 hs
      show magnitude b ≠ univ
      rw [magnitude_of_neg hs']
      intro hc
      have h2 := hp.2
      rw [hcompl _ hc] at h2
      exact not_tailPair_empty_right h2
    · have hs' : none ∉ b := fun hc => hs (hp.1.2 hc)
      show magnitude b ≠ univ
      rw [magnitude_of_pos hs']
      intro hc
      have h2 := hp.2
      rw [hc] at h2
      exact not_tailPair_univ_right h2
  · -- `STailPair b a`: same, with `b` on the other side
    by_cases hs : none ∈ b
    · show magnitude b ≠ univ
      rw [magnitude_of_neg hs]
      intro hc
      have h2 := hp.2
      rw [hcompl _ hc] at h2
      exact not_tailPair_empty_left h2
    · show magnitude b ≠ univ
      rw [magnitude_of_pos hs]
      intro hc
      have h2 := hp.2
      rw [hc] at h2
      exact not_tailPair_univ_left h2
  · show magnitude (univ : Signed) ≠ univ
    rw [magnitude_univ]; exact Set.empty_ne_univ
  · show magnitude (∅ : Signed) ≠ univ
    rw [magnitude_empty]; exact Set.empty_ne_univ

/-- The finite points: everything except `±∞`. -/
def FinitePoint : Type := {x : Signed // IsFinite x}

instance sbSetoid : Setoid FinitePoint where
  r a b := SEqv a.1 b.1
  iseqv := ⟨fun a => SEqv.refl a.1, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- **The reals, as subsets of `ω + 1`.** -/
def SBReal : Type := Quotient sbSetoid

/-- The class of a finite point. -/
def mk (x : Signed) (hx : IsFinite x) : SBReal := Quotient.mk sbSetoid ⟨x, hx⟩

theorem mk_eq_mk {x y : Signed} {hx : IsFinite x} {hy : IsFinite y} :
    mk x hx = mk y hy ↔ SEqv x y :=
  Quotient.eq

/-! ### The bijection -/

/-- `toReal` descends to the quotient. -/
noncomputable def toRealQ : SBReal → ℝ :=
  Quotient.lift (fun a : FinitePoint => toReal a.1) (fun _ _ h => toReal_of_seqv h)

@[simp] theorem toRealQ_mk (x : Signed) (hx : IsFinite x) : toRealQ (mk x hx) = toReal x := rfl

theorem toRealQ_injective : Function.Injective toRealQ := by
  intro a b h
  induction a using Quotient.inductionOn with
  | _ a =>
    induction b using Quotient.inductionOn with
    | _ b => exact Quotient.sound (toReal_injective a.2 b.2 h)

theorem toRealQ_surjective : Function.Surjective toRealQ := by
  intro r
  obtain ⟨x, hx, hv⟩ := exists_toReal_eq r
  exact ⟨mk x hx, hv⟩

theorem toRealQ_bijective : Function.Bijective toRealQ :=
  ⟨toRealQ_injective, toRealQ_surjective⟩

/-- The underlying bijection `SBReal ≃ ℝ`. -/
noncomputable def equivReal : SBReal ≃ ℝ := Equiv.ofBijective toRealQ toRealQ_bijective

@[simp] theorem equivReal_apply (a : SBReal) : equivReal a = toRealQ a := rfl

/-! ### The structure

Both instances lifted along `toRealQ`. What the resulting order actually *is*
is settled below by `mk_lt_mk_iff`, not here. -/

noncomputable instance instLinearOrderSBReal : LinearOrder SBReal :=
  LinearOrder.lift' toRealQ toRealQ_injective

noncomputable instance instFieldSBReal : Field SBReal := equivReal.field

/-- **The order isomorphism.** `P(ω+1)`, cut down to the finite points and
quotiented by adjacency, *is* the real line. -/
noncomputable def orderIsoReal : SBReal ≃o ℝ where
  toEquiv := equivReal
  map_rel_iff' := Iff.rfl

@[simp] theorem orderIsoReal_apply (a : SBReal) : orderIsoReal a = toRealQ a := rfl

theorem le_iff_toRealQ_le {a b : SBReal} : a ≤ b ↔ toRealQ a ≤ toRealQ b := Iff.rfl

theorem lt_iff_toRealQ_lt {a b : SBReal} : a < b ↔ toRealQ a < toRealQ b := Iff.rfl

/-! ### The order is the lex order

The instance above is a lift, so `≤` unfolds to a comparison in `ℝ`. That is a
statement about how the instance was *built*; the theorems here say what the
resulting relation *is*, with no mention of `ℝ` on either side of the `iff`.

Without them "complete ordered field" would mean `ℝ`'s structure relabelled
along a bijection, since `exists_isLUB` and `instIsStrictOrderedRingSBReal` are
both statements about this order. With them the order is pinned to `SLexLt`,
which `Order.lean` and `SignedOrder.lean` build from the bit strings alone.

The `¬ SEqv` conjunct is not redundant and is the whole subtlety: a tail pair
has `b <ₛ a` on the nose while `toReal a = toReal b`, so lex-below by itself
does not give a strict inequality downstairs. `tailPair_iff_isAdjacent` is why
the two conditions differ exactly on the pairs the quotient collapses. -/

/-- **The order on `SBReal` is the signed lex order**, modulo the quotient. -/
theorem mk_lt_mk_iff {a b : Signed} (ha : IsFinite a) (hb : IsFinite b) :
    mk a ha < mk b hb ↔ (a <ₛ b ∧ ¬ SEqv a b) :=
  toReal_lt_iff ha hb

/-- The non-strict form: `≤` is "lex-below or identified". -/
theorem mk_le_mk_iff {a b : Signed} (ha : IsFinite a) (hb : IsFinite b) :
    mk a ha ≤ mk b hb ↔ (a <ₛ b ∨ SEqv a b) := by
  rw [← not_lt, mk_lt_mk_iff hb ha]
  constructor
  · intro h
    rcases slexLt_trichotomy a b with h1 | rfl | h1
    · exact Or.inl h1
    · exact Or.inr (SEqv.refl a)
    · exact Or.inr (not_not.1 fun hne => h ⟨h1, hne⟩).symm
  · rintro (h1 | h1) ⟨h2, hne⟩
    · exact slexLt_asymm h1 h2
    · exact hne h1.symm

/-- Every class is `mk` of a representative, so the two lemmas above determine
the order outright rather than only on classes presented that way. -/
theorem exists_mk (a : SBReal) : ∃ (x : Signed) (hx : IsFinite x), mk x hx = a :=
  Quotient.inductionOn a fun x => ⟨x.1, x.2, rfl⟩

/-! ### The transported operations

These are the specification Gosper's algorithm gets proved against: an algorithm
on bit streams computes addition exactly when the value of its output is the sum
of the values of its inputs. -/

@[simp] theorem toRealQ_add (a b : SBReal) : toRealQ (a + b) = toRealQ a + toRealQ b := by
  change toRealQ (equivReal.symm (equivReal a + equivReal b)) = _
  rw [equivReal_apply, equivReal_apply, ← equivReal_apply (equivReal.symm _),
    Equiv.apply_symm_apply]

@[simp] theorem toRealQ_mul (a b : SBReal) : toRealQ (a * b) = toRealQ a * toRealQ b := by
  change toRealQ (equivReal.symm (equivReal a * equivReal b)) = _
  rw [equivReal_apply, equivReal_apply, ← equivReal_apply (equivReal.symm _),
    Equiv.apply_symm_apply]

/-! ### The order already determines the operations

Transporting the field structure from `ℝ` looks like it might be smuggling
something in. It is not: a complete ordered field is unique up to unique
isomorphism, so once the order is fixed there is exactly one field structure
compatible with it, and the transport merely exhibits it.

The theorem below says so concretely — `a + b` is pinned down by the order alone,
as the supremum of `c + d` over everything below `a` and `b`. This is the same
characterisation Mathlib uses to prove uniqueness (`cutMap_add`: the cut of a sum
is the sum of the cuts).

What this does *not* do is make the definition independent of `ℝ`. That is the
remaining gap, and it closes by defining `+` and `×` as these suprema outright
and deriving the field axioms from `ℚ`'s by density — at which point `ℝ` is never
mentioned. -/

theorem exists_lt_toRealQ_eq {a : SBReal} {u : ℝ} (h : u < toRealQ a) :
    ∃ c : SBReal, c < a ∧ toRealQ c = u := by
  obtain ⟨c, hc⟩ := toRealQ_surjective u
  exact ⟨c, by rw [lt_iff_toRealQ_lt, hc]; exact h, hc⟩

/-- **Addition is determined by the order.** -/
theorem toRealQ_add_eq_sSup (a b : SBReal) :
    toRealQ (a + b)
      = sSup {r : ℝ | ∃ c d : SBReal, c < a ∧ d < b ∧ r = toRealQ c + toRealQ d} := by
  set A := toRealQ a with hA
  set B := toRealQ b with hB
  set S := {r : ℝ | ∃ c d : SBReal, c < a ∧ d < b ∧ r = toRealQ c + toRealQ d} with hS
  have hmem : ∀ u v : ℝ, u < A → v < B → u + v ∈ S := by
    intro u v hu hv
    obtain ⟨c, hc, hcv⟩ := exists_lt_toRealQ_eq hu
    obtain ⟨d, hd, hdv⟩ := exists_lt_toRealQ_eq hv
    exact ⟨c, d, hc, hd, by rw [hcv, hdv]⟩
  have hne : S.Nonempty := ⟨(A - 1) + (B - 1), hmem _ _ (by linarith) (by linarith)⟩
  have hub : ∀ r ∈ S, r ≤ A + B := by
    rintro r ⟨c, d, hc, hd, rfl⟩
    rw [lt_iff_toRealQ_lt] at hc hd
    linarith
  rw [toRealQ_add, ← hA, ← hB]
  refine (csSup_eq_of_forall_le_of_forall_lt_exists_gt hne hub ?_).symm
  intro w hw
  refine ⟨(A - (A + B - w) / 4) + (B - (A + B - w) / 4), hmem _ _ (by linarith) (by linarith), ?_⟩
  linarith

end SternBrocot
