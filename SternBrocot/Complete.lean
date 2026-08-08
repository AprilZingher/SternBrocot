/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Intrinsic

/-!
# `SBReal` is a complete ordered field

`Field.lean` gives `SBReal` a `Field` instance and a `LinearOrder`, and
`orderIsoReal : SBReal ≃o ℝ`. Those together *imply* that the carrier is a
complete ordered field, but none of the three defining clauses was ever stated:
nothing said the order is compatible with `+` and `×`, and nothing said the
order is complete. This file states them.

## What was and was not already there

The subtlety is worth being explicit about, because "we have an order
isomorphism with `ℝ`" is easy to mistake for "we have proved the axioms".

* `LinearOrder SBReal` was there — but a linear order on a field says nothing
  about how the order and the operations interact.
* **Compatibility** — `a ≤ b → a + c ≤ b + c` and `0 < a → 0 < b → 0 < a * b` —
  was *not* there. It is `instIsStrictOrderedRingSBReal` below, pulled back
  along `toRealQ` from `ℝ`.
* **Completeness** — every nonempty bounded-above set has a least upper bound —
  was *not* there either, in any form: no `sSup`, no `IsLUB`, no
  `ConditionallyCompleteLinearOrder`. It is `exists_isLUB` below.

## Where the content actually lives

Neither proof here is deep, and that is the point: both are pullbacks along
`toRealQ`, and the work that makes them available was done elsewhere.
`toRealQ_injective` and `toRealQ_surjective` come from the rigidity and density
theorems; the order on `SBReal` is `toRealQ`-reflecting by construction; and
`toRealQ_add`, `toRealQ_mul` are what `Intrinsic.lean` reproves for the
`ℝ`-free operations (`toRealQ_add'`, `toRealQ_mul'`) — so the same statements
hold of those.

## Main results

* `SternBrocot.instIsStrictOrderedRingSBReal` — the order is compatible with the
  field operations.
* `SternBrocot.exists_isLUB` — **completeness**.
* `SternBrocot.isLUB_iff_isLUB_image` — completeness stated so that it is visibly
  the *order* that is complete, with no reference to how a supremum is computed.
-/

open Set

namespace SternBrocot

/-! ### The order is compatible with the operations -/

/-- **`SBReal` is an ordered field.** Pulled back along `toRealQ`, which is
injective and reflects `≤` by construction. Together with `Field SBReal` this is
the "ordered field" half. -/
noncomputable instance instIsStrictOrderedRingSBReal : IsStrictOrderedRing SBReal :=
  Function.Injective.isStrictOrderedRing toRealQ toRealQ_zero toRealQ_one
    toRealQ_add toRealQ_mul (fun {_ _} => Iff.rfl) (fun {_ _} => Iff.rfl)

/-! ### The instance really fires

These are not restatements of the theorem above: they are Mathlib's *generic*
order-algebra lemmas, which typeclass resolution can only apply if `SBReal`
genuinely carries the ordered-ring structure. -/

example (a b c : SBReal) (h : a ≤ b) : a + c ≤ b + c := by gcongr

example (a b : SBReal) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := mul_pos ha hb

example (a : SBReal) : 0 ≤ a ^ 2 := sq_nonneg a

-- `linarith` needs the full ordered-field structure to fire at all.
example (a b : SBReal) (h : a < b) : a < (a + b) / 2 := by linarith

/-! ### Completeness -/

theorem bddAbove_image {S : Set SBReal} (hbdd : BddAbove S) : BddAbove (toRealQ '' S) := by
  obtain ⟨b, hb⟩ := hbdd
  refine ⟨toRealQ b, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  exact hb hs

/-- Being a least upper bound is the same upstairs and downstairs, because
`toRealQ` is an order isomorphism onto `ℝ`. -/
theorem isLUB_iff_isLUB_image {S : Set SBReal} {u : SBReal} :
    IsLUB S u ↔ IsLUB (toRealQ '' S) (toRealQ u) := by
  constructor
  · rintro ⟨hub, hle⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨s, hs, rfl⟩
      exact hub hs
    · intro r hr
      obtain ⟨v, rfl⟩ := toRealQ_surjective r
      exact hle fun s hs => hr ⟨s, hs, rfl⟩
  · rintro ⟨hub, hle⟩
    refine ⟨fun s hs => hub ⟨s, hs, rfl⟩, fun v hv => hle ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact hv hs

/-- **Completeness.** Every nonempty set of Stern–Brocot reals that is bounded
above has a least upper bound.

With `instIsStrictOrderedRingSBReal` and the `Field` instance, this is the
statement that `P(ω+1)`, cut down to the finite points and quotiented by
adjacency, is a **complete ordered field** — and hence, by uniqueness of such,
*the* real line. `orderIsoReal` exhibits that uniqueness concretely. -/
theorem exists_isLUB {S : Set SBReal} (hne : S.Nonempty) (hbdd : BddAbove S) :
    ∃ u : SBReal, IsLUB S u := by
  obtain ⟨r, hr⟩ := Real.exists_isLUB (hne.image toRealQ) (bddAbove_image hbdd)
  obtain ⟨u, hu⟩ := toRealQ_surjective r
  exact ⟨u, isLUB_iff_isLUB_image.2 (hu ▸ hr)⟩

/-- The same statement with the bound named, which is the form the
`ConditionallyCompleteLinearOrder` instance would be built from. -/
theorem exists_isLUB_of_forall_le {S : Set SBReal} (hne : S.Nonempty) {b : SBReal}
    (hb : ∀ s ∈ S, s ≤ b) : ∃ u : SBReal, IsLUB S u :=
  exists_isLUB hne ⟨b, hb⟩

end SternBrocot
