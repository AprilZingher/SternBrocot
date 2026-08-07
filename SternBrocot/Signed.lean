/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import SternBrocot.Tail

/-!
# The sign coordinate: `P(ω + 1)`

Negation cannot be a Boolean translation on `P(ω)` — that is exactly
`SternBrocot.rigidity`, which says the only masks descending to the tail quotient
are `∅` and `ω`, giving the identity and reciprocal. So one point must be
adjoined. Here `ω + 1` is modelled as `Option ℕ`, with `none` playing the
adjoined sign point `ω`.

## The mirrored convention

`none ∈ x` marks `x` as **negative**, so positives carry no sign bit and the
von Neumann naturals keep exactly the form they have in `Basic.lean`: `1 = {0}`,
`2 = {0,1}`. That is the property the whole encoding is built around, so it is
the one that gets protected.

On the negative branch the finite bits store the **complement** of the
magnitude's Stern–Brocot path — the negative side is drawn as a mirror image of
the positive side, which is how the signed tree actually looks. Consequently:

* negation is `ν x = x ∆ (ω ∪ {ω})`, i.e. **complement** — it flips the sign and
  mirrors the path in one move;
* reciprocal is `ρ x = x ∆ ω`, flipping the finite bits and leaving the sign
  alone, and this is the *same* operation in both signs;
* `x ∆ {ω}` is `-1/x`.

The payoff is in `SignedOrder.lean`: because complement reverses the lex order
(`compl_lexLt_compl`), same-sign comparison is forward lex on **both** sides,
with no reversed branch.

## Main results

* `SternBrocot.klein_four` — the four masks `{∅, ω, {ω}, ω+1}` are closed under
  `∆` and form a Klein four-group, isomorphic to `{x, -x, 1/x, -1/x}` in `PGL₂`.
* `SternBrocot.signedRigidity` — **the sharp statement**: for `m ⊆ ω + 1`, the
  translation `x ↦ x ∆ m` descends to the tail quotient **iff** `m` is one of
  those four. Adjoining a single point buys exactly one new operation and its
  composite with reciprocal, and nothing more.

## The one warning that survives

The tail rule relates the finite parts only, with the sign coordinate
*agreeing* (`STailPair`). Applying "including `n` ≡ including everything above
`n`" *at* `ω` would collapse the sign bit. The separate identification `-0 = 0`
is handled in `SignedOrder.lean`, where it appears as the adjacency `univ ∼ ∅`
rather than as a special postulate.
-/

open Set
open scoped symmDiff

namespace SternBrocot

/-- The carrier with a sign coordinate: `P(ω + 1)`, with `none` as the adjoined
point `ω`. Membership of `none` marks a *negative* point. -/
abbrev Signed := Set (Option ℕ)

/-- The finite coordinates `ω ⊆ ω + 1`, as a mask. -/
def finCoords : Signed := {x | x ≠ none}

/-- The finite part of a signed point: the stored bits. On the positive branch
this is the Stern–Brocot path; on the negative branch it is its complement. -/
def finPart (x : Signed) : Set ℕ := {n | some n ∈ x}

/-- Embed `P(ω)` into `P(ω + 1)` with positive sign. The naturals land here
unchanged. -/
def lift (y : Set ℕ) : Signed := some '' y

@[simp] theorem mem_finPart {x : Signed} {n : ℕ} : n ∈ finPart x ↔ some n ∈ x := Iff.rfl

@[simp] theorem some_mem_finCoords (n : ℕ) : some n ∈ finCoords := by simp [finCoords]

@[simp] theorem none_notMem_finCoords : none ∉ finCoords := by simp [finCoords]

@[simp] theorem finPart_lift (y : Set ℕ) : finPart (lift y) = y := by
  ext n; simp [finPart, lift]

@[simp] theorem none_notMem_lift (y : Set ℕ) : none ∉ lift y := by
  simp [lift]

@[simp] theorem finPart_empty : finPart (∅ : Signed) = ∅ := by
  ext n; simp [finPart]

@[simp] theorem finPart_univ : finPart (univ : Signed) = univ := by
  ext n; simp [finPart]

@[simp] theorem finPart_singleton_none : finPart ({none} : Signed) = ∅ := by
  ext n; simp [finPart]

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

/-! ### The two operations -/

/-- Negation: **complement** in `P(ω + 1)`. It flips the sign and mirrors the
finite bits together, which is exactly what the mirrored convention needs. This
is the mask that cannot live in `P(ω)`. -/
def neg (x : Signed) : Signed := x ∆ univ

/-- Reciprocal: symmetric difference with the finite coordinates. It flips every
finite bit and leaves the sign alone, and — because the negative branch stores a
complemented path — it is the *same* operation in both signs, as
`1/(-x) = -(1/x)` demands. -/
def recipS (x : Signed) : Signed := x ∆ finCoords

theorem neg_eq_compl (x : Signed) : neg x = xᶜ := by
  ext k; simp [neg, Set.mem_symmDiff]

@[simp] theorem finPart_neg (x : Signed) : finPart (neg x) = (finPart x)ᶜ := by
  ext n; simp [neg, Set.mem_symmDiff]

@[simp] theorem finPart_recipS (x : Signed) : finPart (recipS x) = (finPart x)ᶜ := by
  ext n; simp [recipS, Set.mem_symmDiff]

@[simp] theorem none_mem_neg (x : Signed) : none ∈ neg x ↔ none ∉ x := by
  simp [neg, Set.mem_symmDiff]

@[simp] theorem none_mem_recipS (x : Signed) : none ∈ recipS x ↔ none ∈ x := by
  simp [recipS, Set.mem_symmDiff]

theorem neg_neg (x : Signed) : neg (neg x) = x := by
  rw [neg_eq_compl, neg_eq_compl, compl_compl]

theorem recipS_recipS (x : Signed) : recipS (recipS x) = x := by
  simp [recipS]

/-- Negation and reciprocal commute — they are the two independent generators. -/
theorem neg_recipS (x : Signed) : neg (recipS x) = recipS (neg x) := by
  simp only [neg, recipS, symmDiff_assoc]
  rw [symmDiff_comm finCoords univ]

/-- `-0` is `univ`: everything, sign included. This is the point the zero
identification pairs with `∅`. -/
@[simp] theorem neg_empty : neg (∅ : Signed) = univ := by
  rw [neg_eq_compl, compl_empty]

@[simp] theorem neg_univ : neg (univ : Signed) = ∅ := by
  rw [neg_eq_compl, compl_univ]

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

/-- **Negation descends.** Complement flips both signs of a tail pair equally,
preserving the agreement `STailPair` requires, and mirrors both finite parts,
which exchanges the two sides exactly as reciprocal does. -/
theorem sdescends_neg : SDescends neg := by
  intro a b hab
  rcases hab with (rfl | hab | hba)
  · exact STailEqv.refl _
  · obtain ⟨n, hn⟩ := hab.2
    refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · rw [none_mem_neg, none_mem_neg]; exact not_congr hab.1.symm
    · rw [finPart_neg, finPart_neg]; exact ⟨n, hn.compl⟩
  · obtain ⟨n, hn⟩ := hba.2
    refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · rw [none_mem_neg, none_mem_neg]; exact not_congr hba.1.symm
    · rw [finPart_neg, finPart_neg]; exact ⟨n, hn.compl⟩

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
    · -- `{ω}` is `-1/x`, the composite of the two generators
      intro a b hab
      have hmask : finCoords ∆ (univ : Signed) = {none} := by
        ext k; cases k <;> simp [finCoords, Set.mem_symmDiff]
      have hsplit : ∀ x : Signed, x ∆ ({none} : Signed) = neg (recipS x) := by
        intro x
        rw [neg, recipS, symmDiff_assoc, hmask]
      simpa only [hsplit] using sdescends_neg _ _ (sdescends_recipS a b hab)
    · have hn : ∀ x : Signed, x ∆ (univ : Signed) = neg x := fun _ => rfl
      simpa only [hn] using sdescends_neg

/-! ### No mask has a fixed point

Translation in a Boolean group is fixed-point-free, so `∅` and `univ` — that is
`+0` and `-0` — are genuinely distinct points. They are identified in
`SignedOrder.lean`, where they turn out to be *adjacent*, so the identification
is an instance of the same "collapse adjacencies" rule as the tail relation
rather than a separate postulate. -/

theorem neg_ne_self (x : Signed) : neg x ≠ x := by
  intro h
  have := congrArg (fun s => none ∈ s) h
  simp only [none_mem_neg, eq_iff_iff] at this
  tauto

/-- The zero identification: `+0 = ∅` and `-0 = univ = neg ∅`. -/
def ZeroDegen (a b : Signed) : Prop :=
  (a = ∅ ∧ b = univ) ∨ (a = univ ∧ b = ∅)

theorem zeroDegen_neg : ZeroDegen ∅ (neg ∅) := Or.inl ⟨rfl, neg_empty⟩

end SternBrocot
