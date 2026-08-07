/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Completeness
import Mathlib.Order.PiLex
import Mathlib.Order.PropInstances

/-!
# The lex order as a `LinearOrder` instance

`Set ℕ` already carries an order — `≤` is `⊆`, from its `CompleteBooleanAlgebra`
instance — and Lean permits one `LinearOrder` per type. So the lex order cannot
be registered on `Set ℕ` directly, and up to this point it has lived as the bare
relations `<ₗ` and `≤ₗ`. That is why none of Mathlib's order vocabulary applied,
and in particular why `≃o` could not even be *stated*: `OrderIso` needs `LE`
instances on both sides.

`SB` is the type synonym that fixes this: definitionally `Set ℕ`, but distinct
for instance resolution, exactly as Mathlib does with `Lex`, `OrderDual` and
`WithBot`.

## Why not reuse `Lex (∀ i, β i)`

Mathlib's `Pi.Lex` really does give this order — `lexLt_iff_piLex` below proves
it, since in `Prop` the relation `p < q` unfolds to `¬p ∧ q`, i.e. "absent from
`x`, present in `y`". But the instance fires on `Lex (ℕ → Prop)` and *not* on
`Lex (Set ℕ)`, because instance search will not unfold `Set`. Using it would mean
moving between `Set ℕ` and `ℕ → Prop` at every boundary while `∆`, `Set.Finite`
and `∈` all live on the `Set` side.

The agreement lemma is kept anyway: it records that this development uses the
standard lexicographic order and not a bespoke one.
-/

open Set

namespace SternBrocot

/-! ### Agreement with Mathlib's `Pi.Lex` -/

/-- **The lex order here is Mathlib's `Pi.Lex` order.** In `Prop`, `p < q` means
`¬p ∧ q`, which is exactly "the branch point is absent from `x` and present in
`y`". -/
theorem lexLt_iff_piLex (x y : Set ℕ) :
    (toLex (fun n => n ∈ x) < toLex (fun n => n ∈ y)) ↔ (x <ₗ y) := by
  constructor
  · rintro ⟨n, hagree, hlt⟩
    have hnx : ¬ (toLex (fun n => n ∈ x) n) := fun hc => (lt_iff_le_not_ge.1 hlt).2 (fun _ => hc)
    have hny : toLex (fun n => n ∈ y) n := by
      by_contra hc
      exact (lt_iff_le_not_ge.1 hlt).2 (fun h => absurd h hc)
    exact ⟨n, fun k hk => iff_of_eq (hagree k hk), hnx, hny⟩
  · rintro ⟨n, hagree, hnx, hny⟩
    exact ⟨n, fun k hk => propext (hagree k hk),
      lt_iff_le_not_ge.2 ⟨fun h => absurd h hnx, fun h => hnx (h hny)⟩⟩

/-! ### The lex-ordered carrier -/

/-- `P(ω)` carrying the **lex** order rather than `⊆`. Definitionally `Set ℕ`,
but a distinct type for instance resolution. -/
def SB : Type := Set ℕ

/-- View a subset of `ω` in the lex-ordered copy. -/
def toSB (x : Set ℕ) : SB := x

/-- View a lex-ordered point as a subset of `ω`. -/
def ofSB (a : SB) : Set ℕ := a

@[simp] theorem ofSB_toSB (x : Set ℕ) : ofSB (toSB x) = x := rfl

@[simp] theorem toSB_ofSB (a : SB) : toSB (ofSB a) = a := rfl

theorem toSB_injective : Function.Injective toSB := fun _ _ h => h

instance : LT SB := ⟨fun a b => LexLt (ofSB a) (ofSB b)⟩
instance : LE SB := ⟨fun a b => LexLe (ofSB a) (ofSB b)⟩

theorem SB.lt_def (a b : SB) : a < b ↔ ofSB a <ₗ ofSB b := Iff.rfl

theorem SB.le_def (a b : SB) : a ≤ b ↔ ofSB a ≤ₗ ofSB b := Iff.rfl

@[simp] theorem toSB_lt_toSB (x y : Set ℕ) : toSB x < toSB y ↔ x <ₗ y := Iff.rfl

@[simp] theorem toSB_le_toSB (x y : Set ℕ) : toSB x ≤ toSB y ↔ x ≤ₗ y := Iff.rfl

/-- The lex order is a linear order. Every field comes from a theorem already
proved in `Order.lean` and `Completeness.lean`; this only packages them so that
Mathlib's order vocabulary — `Monotone`, `StrictMono`, `OrderIso` — applies. -/
noncomputable instance : LinearOrder SB where
  le_refl a := lexLe_refl (ofSB a)
  le_trans _ _ _ hab hbc := lexLe_trans hab hbc
  lt_iff_le_not_ge a b := by
    constructor
    · exact fun h => ⟨lexLe_of_lexLt h, fun hc => hc h⟩
    · exact fun h => not_not.1 h.2
  le_antisymm a b hab hba := by
    rcases (lexLe_iff (ofSB a) (ofSB b)).1 hab with h | h
    · exact h
    · exact absurd h hba
  le_total a b := by
    rcases lexLt_trichotomy (ofSB a) (ofSB b) with h | h | h
    · exact Or.inl (lexLe_of_lexLt h)
    · exact Or.inl (by rw [SB.le_def, h]; exact lexLe_refl _)
    · exact Or.inr (lexLe_of_lexLt h)
  toDecidableLE := Classical.decRel _

/-- `∅` is the bottom: the point `0`. -/
instance : OrderBot SB where
  bot := toSB ∅
  bot_le a := empty_lexLe (ofSB a)

/-- `univ` is the top: the point `∞`, which is dropped when the field structure
goes on. -/
instance : OrderTop SB where
  top := toSB univ
  le_top a := lexLe_univ (ofSB a)

end SternBrocot
