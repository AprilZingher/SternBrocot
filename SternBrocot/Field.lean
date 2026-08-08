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

## What is transported

**Both the order and the field structure**, as things stand. `LinearOrder
SBReal` is `LinearOrder.lift' toRealQ`, so `a ≤ b` unfolds definitionally to
`toRealQ a ≤ toRealQ b` — a comparison of two real numbers; `le_iff_toRealQ_le`
below is literally `Iff.rfl`. The field structure is `equivReal.field`.

It is tempting to call the order intrinsic on the grounds that `toReal` was
itself built from the lex order and the bitwise supremum, both proved here from
scratch. That is true of `toReal` and false of the instance: nothing in this
development connects `≤` on the quotient back to `SLexLt`. The missing statement
is `mk a ha < mk b hb ↔ (a <ₛ b ∧ ¬ SEqv a b)`, and its ingredients
(`slexLt_of_toReal_lt`, `toReal_mono`, `toReal_injective`) all exist — but until
it is proved, the carrier faithfully represents `ℝ` and every piece of structure
on it is a pullback.

Making the operations intrinsic is the Gosper project, and `toReal₀_toSet` is the
specification it gets proved against: an algorithm on bit streams is correct
exactly when its output has the value the transported operation gives.

## Main results

* `SternBrocot.SBReal` — the carrier.
* `SternBrocot.orderIsoReal : SBReal ≃o ℝ` — **the order isomorphism.**
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

Both lifted along `toRealQ`. See the module docstring: calling the order
intrinsic would be a claim about a theorem that does not exist yet. -/

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
