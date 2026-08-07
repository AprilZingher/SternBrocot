/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Tail

/-!
# The sign coordinate: `P(ω + 1)`

Negation cannot be a Boolean translation on `P(ω)` — that is exactly
`SternBrocot.rigidity`, which says the only masks that descend to the tail
quotient are `∅` and `ω`, giving the identity and reciprocal. So one point must
be adjoined. Here `ω + 1` is modelled as `Option ℕ`, with `none` playing the
adjoined sign point `ω`.

With the sign coordinate in place:

* negation is `ν x = x ∆ {ω}`,
* reciprocal is `ρ x = x ∆ ω` (flips every finite bit, leaves the sign alone,
  which is what `1/(-x) = -(1/x)` requires).

## Main results

* `SternBrocot.klein_four` — the four masks `{∅, ω, {ω}, ω+1}` are closed under
  `∆` and form a Klein four-group, isomorphic to `{x, -x, 1/x, -1/x}` in `PGL₂`.
* `SternBrocot.signedRigidity` — **the sharp statement**: for `m ⊆ ω + 1`, the
  translation `x ↦ x ∆ m` descends to the tail quotient **iff** `m` is one of
  those four. So adjoining a single point buys exactly one new operation
  (negation) and its composite with reciprocal, and nothing more. Addition is
  still not Boolean, and never will be.

## Two warnings, both load-bearing

**Do not extend the tail rule to level `ω`.** The identification "including `n`
is the same as including everything above `n`", applied at `ω`, would identify
`x` with `neg x` for *every* `x` and collapse the sign bit entirely. `STailPair`
below therefore requires the sign coordinate to *agree*, and only relates the
finite parts.

**`-0 = 0` does not come for free.** Translation in a Boolean group is
fixed-point-free, so no mask fixes anything; `∅` and `{ω}` are genuinely
distinct points here, denoting `0` and `-0`. Identifying them is an *extra*
quotient (`ZeroDegen`), not a consequence of the tail rule. It is the same move
as `θ` being meaningless at `r = 0` in polar coordinates.
-/

open Set
open scoped symmDiff

namespace SternBrocot

/-- The carrier with a sign coordinate: `P(ω + 1)`, with `none` as the adjoined
point `ω`. -/
abbrev Signed := Set (Option ℕ)

/-- The finite coordinates `ω ⊆ ω + 1`, as a mask. -/
def finCoords : Signed := {x | x ≠ none}

/-- The finite part of a signed point: its `P(ω)` shadow. -/
def finPart (x : Signed) : Set ℕ := {n | some n ∈ x}

/-- Embed `P(ω)` into `P(ω + 1)` with positive sign. -/
def lift (y : Set ℕ) : Signed := some '' y

@[simp] theorem mem_finPart {x : Signed} {n : ℕ} : n ∈ finPart x ↔ some n ∈ x := Iff.rfl

@[simp] theorem some_mem_finCoords (n : ℕ) : some n ∈ finCoords := by simp [finCoords]

@[simp] theorem none_notMem_finCoords : none ∉ finCoords := by simp [finCoords]

@[simp] theorem finPart_lift (y : Set ℕ) : finPart (lift y) = y := by
  ext n; simp [finPart, lift]

@[simp] theorem none_notMem_lift (y : Set ℕ) : none ∉ lift y := by
  simp [lift]

/-- A signed point is determined by its finite part and its sign. -/
theorem signed_ext {a b : Signed} (hfin : finPart a = finPart b)
    (hsgn : none ∈ a ↔ none ∈ b) : a = b := by
  ext x
  cases x with
  | none => exact hsgn
  | some n => exact Set.ext_iff.mp hfin n

/-- Symmetric difference acts coordinatewise on the finite part. -/
@[simp] theorem finPart_symmDiff (x m : Signed) : finPart (x ∆ m) = finPart x ∆ finPart m := by
  ext n
  simp only [mem_finPart, Set.mem_symmDiff]

theorem none_mem_symmDiff (x m : Signed) :
    (none ∈ x ∆ m) ↔ (none ∈ x ↔ none ∉ m) := by
  simp only [Set.mem_symmDiff]
  by_cases h : none ∈ m <;> simp [h]

/-! ### The two operations -/

/-- Negation: symmetric difference with the sign point. This is the mask that
*cannot* live in `P(ω)`. -/
def neg (x : Signed) : Signed := x ∆ {none}

/-- Reciprocal: symmetric difference with the finite coordinates. It flips every
finite bit and leaves the sign alone, as `1/(-x) = -(1/x)` demands. -/
def recipS (x : Signed) : Signed := x ∆ finCoords

@[simp] theorem finPart_neg (x : Signed) : finPart (neg x) = finPart x := by
  ext n; simp [neg, Set.mem_symmDiff]

@[simp] theorem finPart_recipS (x : Signed) : finPart (recipS x) = (finPart x)ᶜ := by
  ext n; simp [recipS, Set.mem_symmDiff]

theorem none_mem_neg (x : Signed) : none ∈ neg x ↔ none ∉ x := by
  simp [neg, Set.mem_symmDiff]

@[simp] theorem none_mem_recipS (x : Signed) : none ∈ recipS x ↔ none ∈ x := by
  simp [recipS, Set.mem_symmDiff]

theorem neg_neg (x : Signed) : neg (neg x) = x := by
  simp [neg]

theorem recipS_recipS (x : Signed) : recipS (recipS x) = x := by
  simp [recipS]

/-- Negation and reciprocal commute — they are the two independent generators. -/
theorem neg_recipS (x : Signed) : neg (recipS x) = recipS (neg x) := by
  simp only [neg, recipS, symmDiff_assoc]
  rw [symmDiff_comm finCoords {none}]

/-! ### The Klein four-group -/

/-- The four masks `{∅, ω, {ω}, ω + 1}`. -/
def kleinMasks : Set Signed := {∅, finCoords, {none}, univ}

theorem finCoords_symmDiff_singleton_none : finCoords ∆ ({none} : Signed) = univ := by
  ext x
  cases x <;> simp [finCoords, Set.mem_symmDiff]

/-- The four masks are exactly those whose finite part is trivial. The sign
coordinate is unconstrained — which is the whole point: the tail relation never
touches it, so it is free to carry an operation. -/
theorem mem_kleinMasks_iff (m : Signed) :
    m ∈ kleinMasks ↔ (finPart m = ∅ ∨ finPart m = univ) := by
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact Or.inl (by ext n; simp [finPart])
    · exact Or.inr (by ext n; simp [finPart])
    · exact Or.inl (by ext n; simp [finPart])
    · exact Or.inr (by ext n; simp [finPart])
  · intro h
    by_cases hnone : none ∈ m
    · rcases h with h | h
      · exact Or.inr (Or.inr (Or.inl
          (signed_ext (by rw [h]; ext n; simp [finPart]) (by simp [hnone]))))
      · exact Or.inr (Or.inr (Or.inr
          (signed_ext (by rw [h]; ext n; simp [finPart]) (by simp [hnone]))))
    · rcases h with h | h
      · exact Or.inl (signed_ext (by rw [h]; ext n; simp [finPart]) (by simp [hnone]))
      · exact Or.inr (Or.inl
          (signed_ext (by rw [h]; ext n; simp [finPart]) (by simp [hnone])))

/-- **The Klein four-group.** The four masks are closed under symmetric
difference and each is an involution, so they form `(ℤ/2)²` — isomorphic to
`{x, -x, 1/x, -1/x}` in `PGL₂`. -/
theorem klein_four :
    (∀ m : Signed, m ∆ m = (∅ : Signed)) ∧
    (∀ m ∈ kleinMasks, ∀ m' ∈ kleinMasks, m ∆ m' ∈ kleinMasks) := by
  refine ⟨fun m => symmDiff_self m, fun m hm m' hm' => ?_⟩
  rw [mem_kleinMasks_iff] at hm hm' ⊢
  rw [finPart_symmDiff]
  rcases hm with h | h <;> rcases hm' with h' | h' <;> rw [h, h']
  · exact Or.inl (symmDiff_self _)
  · exact Or.inr (bot_symmDiff _)
  · exact Or.inr (symmDiff_bot _)
  · exact Or.inl (symmDiff_self _)

/-! ### The extended tail relation

The tail rule relates only the *finite* parts, and requires the sign coordinate
to agree. Extending it to level `ω` would identify every `x` with `neg x`. -/

/-- A tail pair in `P(ω + 1)`: same sign, and finite parts forming a tail pair. -/
def STailPair (a b : Signed) : Prop :=
  (none ∈ a ↔ none ∈ b) ∧ TailPair (finPart a) (finPart b)

/-- The tail equivalence on `P(ω + 1)`. -/
def STailEqv (a b : Signed) : Prop := a = b ∨ STailPair a b ∨ STailPair b a

theorem STailPair.ne {a b : Signed} (h : STailPair a b) : a ≠ b := by
  rintro rfl
  exact h.2.ne rfl

theorem STailPair.left_unique {a b b' : Signed} (h : STailPair a b) (h' : STailPair a b') :
    b = b' :=
  signed_ext (h.2.left_unique h'.2) (h.1.symm.trans h'.1)

theorem STailPair.right_unique {a a' b : Signed} (h : STailPair a b) (h' : STailPair a' b) :
    a = a' :=
  signed_ext (h.2.right_unique h'.2) (h.1.trans h'.1.symm)

theorem not_stailPair_of_stailPair_left {a b c : Signed} (hab : STailPair a b) :
    ¬ STailPair b c := fun hbc => not_tailPair_of_tailPair_left hab.2 hbc.2

theorem not_stailPair_of_stailPair_right {a b c : Signed} (hab : STailPair a b) :
    ¬ STailPair c a := fun hca => not_tailPair_of_tailPair_right hab.2 hca.2

theorem STailEqv.refl (a : Signed) : STailEqv a a := Or.inl rfl

theorem STailEqv.symm {a b : Signed} : STailEqv a b → STailEqv b a := by
  rintro (rfl | h | h)
  · exact Or.inl rfl
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

theorem STailEqv.trans {a b c : Signed} : STailEqv a b → STailEqv b c → STailEqv a c := by
  rintro (rfl | hab | hba) hbc
  · exact hbc
  · rcases hbc with (rfl | hbc | hcb)
    · exact Or.inr (Or.inl hab)
    · exact absurd hbc (not_stailPair_of_stailPair_left hab)
    · exact Or.inl (hab.right_unique hcb)
  · rcases hbc with (rfl | hbc | hcb)
    · exact Or.inr (Or.inr hba)
    · exact Or.inl (hba.left_unique hbc)
    · exact absurd hcb (not_stailPair_of_stailPair_right hba)

theorem stailEqv_equivalence : Equivalence STailEqv :=
  ⟨STailEqv.refl, STailEqv.symm, STailEqv.trans⟩

/-- A map descends to the signed tail quotient. -/
def SDescends (f : Signed → Signed) : Prop := ∀ a b, STailEqv a b → STailEqv (f a) (f b)

/-! ### Signed rigidity -/

theorem symmDiff_left_cancel_signed {a b m : Signed} (h : a ∆ m = b ∆ m) : a = b := by
  ext k
  have := Set.ext_iff.mp h k
  simp only [Set.mem_symmDiff] at this
  by_cases hm : k ∈ m <;> tauto

/-- **Negation descends.** `{ω}` does not meet the finite coordinates, so it
leaves every finite part untouched, and it flips both signs of a tail pair
equally — preserving the agreement `STailPair` requires. -/
theorem sdescends_neg : SDescends neg := by
  intro a b hab
  rcases hab with (rfl | hab | hba)
  · exact STailEqv.refl _
  · refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · rw [none_mem_neg, none_mem_neg]
      exact not_congr hab.1
    · rw [finPart_neg, finPart_neg]; exact hab.2
  · refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · rw [none_mem_neg, none_mem_neg]
      exact not_congr hba.1
    · rw [finPart_neg, finPart_neg]; exact hba.2

/-- **Reciprocal descends**, exchanging the two sides of a tail pair, exactly as
it does on `P(ω)`. -/
theorem sdescends_recipS : SDescends recipS := by
  intro a b hab
  rcases hab with (rfl | hab | hba)
  · exact STailEqv.refl _
  · obtain ⟨n, hn⟩ := hab.2
    refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · rw [none_mem_recipS, none_mem_recipS]; exact hab.1.symm
    · rw [finPart_recipS, finPart_recipS]; exact ⟨n, hn.compl⟩
  · obtain ⟨n, hn⟩ := hba.2
    refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · rw [none_mem_recipS, none_mem_recipS]; exact hba.1.symm
    · rw [finPart_recipS, finPart_recipS]; exact ⟨n, hn.compl⟩

/-- The finite part of a descending mask must itself descend on `P(ω)`, so by
`rigidity` it is `∅` or `ω`. The sign coordinate is unconstrained, because the
tail relation never touches it. -/
theorem finPart_eq_of_sdescends {m : Signed} (h : SDescends (· ∆ m)) :
    finPart m = ∅ ∨ finPart m = univ := by
  rw [← symmDiff_preservesTail_iff]
  intro y z hyz
  have hlift : STailPair (lift y) (lift z) := by
    refine ⟨?_, ?_⟩
    · simp
    · rw [finPart_lift, finPart_lift]; exact hyz
  have := h _ _ (Or.inr (Or.inl hlift))
  rcases this with heq | hl | hr
  · exact absurd (by
      have := congrArg finPart heq
      rwa [finPart_symmDiff, finPart_symmDiff, finPart_lift, finPart_lift,
        symmDiff_left_inj] at this) hyz.ne
  · refine Or.inl ?_
    have := hl.2
    rwa [finPart_symmDiff, finPart_symmDiff, finPart_lift, finPart_lift] at this
  · refine Or.inr ?_
    have := hr.2
    rwa [finPart_symmDiff, finPart_symmDiff, finPart_lift, finPart_lift] at this

/-- **Signed rigidity.** For `m ⊆ ω + 1`, the Boolean translation `x ↦ x ∆ m`
descends to the tail quotient **iff** `m ∈ {∅, ω, {ω}, ω + 1}`.

Adjoining one point to the carrier buys exactly one new operation — negation —
together with its composite with reciprocal, and nothing else. Addition is still
not a Boolean operation, and no further adjunction of this shape will make it
one. -/
theorem signedRigidity (m : Signed) : SDescends (· ∆ m) ↔ m ∈ kleinMasks := by
  rw [mem_kleinMasks_iff]
  constructor
  · exact finPart_eq_of_sdescends
  · intro h
    rw [← mem_kleinMasks_iff] at h
    rcases h with (rfl | rfl | rfl | rfl)
    · intro a b hab
      have h0 : ∀ x : Signed, x ∆ (∅ : Signed) = x := by
        intro x; ext k; simp [Set.mem_symmDiff]
      show STailEqv (a ∆ ∅) (b ∆ ∅)
      rw [h0, h0]
      exact hab
    · have hr : ∀ x : Signed, x ∆ finCoords = recipS x := fun _ => rfl
      simpa only [hr] using sdescends_recipS
    · have hn : ∀ x : Signed, x ∆ {none} = neg x := fun _ => rfl
      simpa only [hn] using sdescends_neg
    · intro a b hab
      have hsplit : ∀ x : Signed, x ∆ (univ : Signed) = neg (recipS x) := by
        intro x
        rw [neg, recipS, symmDiff_assoc, finCoords_symmDiff_singleton_none]
      simpa only [hsplit] using sdescends_neg _ _ (sdescends_recipS a b hab)

/-! ### `-0 = 0` is an extra quotient

Translation in a Boolean group has no fixed points, so `∅` and `{ω}` — that is
`0` and `-0` — are genuinely distinct points of `P(ω + 1)`. Identifying them is
an additional quotient, not a consequence of the tail rule. -/

/-- No mask fixes any point, so nothing makes `-0 = 0` automatic. -/
theorem neg_ne_self (x : Signed) : neg x ≠ x := by
  intro h
  have := congrArg (fun s => none ∈ s) h
  simp only [none_mem_neg, eq_iff_iff] at this
  tauto

/-- The degeneracy to impose at zero: the sign coordinate carries no information
where there is no side to be on. -/
def ZeroDegen (a b : Signed) : Prop :=
  (a = ∅ ∧ b = {none}) ∨ (a = {none} ∧ b = ∅)

theorem zeroDegen_neg : ZeroDegen ∅ (neg ∅) := by
  left
  refine ⟨rfl, ?_⟩
  ext x
  cases x <;> simp [neg, Set.mem_symmDiff]

end SternBrocot
