# SternBrocot — reals as subsets of ω

Lean 4 + Mathlib formalization of the Stern–Brocot representation of the reals,
where the carrier is literally `P(ω) = Set ℕ`, reciprocal is literally set
complement, and negation is symmetric difference with one adjoined point.

## Setup

- Toolchain: `leanprover/lean4:v4.32.2` (installed via `brew install elan-init`)
- Mathlib: `v4.32.2`, rev `905b95818eb32af7874a58b427f50c1711a5e96c`
- Build: `lake build` from this directory. Mathlib oleans came from
  `lake exe cache get`; do not `lake build` from inside `.lake/packages/mathlib`.

## The encoding

A set `x ⊆ ω` is the bit stream `b n = (n ∈ x)`, read as a path down the
Stern–Brocot tree. Bit `0` is a left move, bit `1` a right move.

| object | definition |
|---|---|
| left move | `L x = {y ∪ {y} : y ∈ x}` — prepend a `0` bit |
| right move | `S x = L x ∪ {0}` — prepend a `1` bit; the von Neumann successor |
| reciprocal | `recip x = xᶜ` — flips every bit, so `J L J = S` |
| tail rule | `s ⌢ 1 ⌢ 0^∞ ∼ s ⌢ 0 ⌢ 1^∞`, i.e. `s R L^∞ = s L R^∞` |

The tail rule is the *only* redundancy. Verified concretely in `Examples.lean`:
`2 = {0,1}` and `ω \ {1}` are a tail pair, matching the original description.

## Files

| file | contents | status |
|---|---|---|
| `SternBrocot/Basic.lean` | moves, reciprocal, `IsTailPairAt`/`TailPair`, rigidity in pair form | complete |
| `SternBrocot/Tail.lean` | tail classes have ≤ 2 elements; rigidity in quotient form | complete |
| `SternBrocot/Order.lean` | lex order is a strict linear order; **tail relation = adjacency** | complete |
| `SternBrocot/Completeness.lean` | bitwise sup; every subset has a LUB; quotient is dense | complete |
| `SternBrocot/Node.lean` | value of a finite path; unimodularity; values in lowest terms | complete |
| `SternBrocot/Enumeration.lean` | **the tree enumerates `ℚ≥0` exactly once** | complete |
| `SternBrocot/PathOrder.lean` | lex order on paths; `nodeValue` is an order embedding | complete |
| `SternBrocot/Bridge.lean` | `toSet`: paths ↔ finite subsets of `ω`; the orders agree | complete |
| `SternBrocot/Signed.lean` | `P(ω+1)`; negation = complement; **signed rigidity** | complete |
| `SternBrocot/SignedOrder.lean` | mirrored sign order; full quotient = adjacencies | complete |
| `SternBrocot/ToReal.lean` | `Φ₀ = toReal₀ : P(ω) → ℝ≥0` as a Dedekind cut | complete |
| `SternBrocot/SignedToReal.lean` | `Φ = toReal : P(ω+1) → ℝ`; monotone, bijective on the quotient | complete |
| `SternBrocot/Induction.lean` | induction along the tree: `ℚ` yes, `ℝ` no | complete |
| `SternBrocot/Field.lean` | **`SBReal ≃o ℝ`**; transported field structure | complete |
| `SternBrocot/Examples.lean` | machine-checked sanity checks of the encoding | complete |

No `sorry`, no `native_decide`. All results depend only on
`propext`, `Classical.choice`, `Quot.sound`.

## Headline results

- `SternBrocot.rigidity` — **the rigidity theorem**. For `m ⊆ ω`, the Boolean
  translation `x ↦ x ∆ m` descends to `P(ω)/∼` **iff** `m = ∅` or `m = ω`. This
  is the no-go theorem: the Boolean structure supports exactly the `PGL₂`
  torsion elements (identity and reciprocal, plus negation once `ω` is
  adjoined), and nothing else. Addition was never going to be Boolean.
- `SternBrocot.tailPair_iff_isAdjacent` — **the key lemma**. `TailPair a b` iff
  `b <ₗ a` with nothing strictly between. The quotient collapses precisely the
  jumps, so `P(ω)/∼` is densely ordered. Everything downstream depends on this.
- `SternBrocot.nodeValue_bijOn` — **the enumeration theorem**. `nodeValue` is a
  bijection from canonical finite paths onto `ℚ≥0`; with
  `nodeValue_num_den_coprime`, each rational appears at exactly one node,
  already in lowest terms. Surjectivity is the Euclidean algorithm with `a + b`
  as the decreasing measure; injectivity is a head comparison, since right-headed
  paths have value `≥ 1` and left-headed paths `< 1`.
- `SternBrocot.pathLt_iff_nodeValue_lt` — **the order embedding**. The lex order
  on finite paths is exactly the order of their values. With `nodeValue_bijOn`,
  the tree nodes are an order-isomorphic copy of `ℚ≥0`.
- `SternBrocot.pathLt_iff_lexLt` — **the bridge**. The lex order on paths is the
  lex order on the finite sets they denote, so the order embedding transfers to
  the carrier with no reindexing. `range_toSet` says paths denote exactly the
  finite sets; `toSet_injOn_canonical` makes it a bijection on normal forms.
- `SternBrocot.signedRigidity` — **rigidity with the sign coordinate**. For
  `m ⊆ ω + 1`, `x ↦ x ∆ m` descends **iff** `m ∈ {∅, ω, {ω}, ω+1}`. Adjoining one
  point buys exactly negation and its composite with reciprocal, nothing more.
  The reason: `kleinMasks` is precisely "finite part is `∅` or `ω`, sign free" —
  the finite part is pinned by `rigidity`, and the sign coordinate is free
  because the tail relation never touches it.
- `SternBrocot.orderIsoReal : SBReal ≃o ℝ` — **the construction, complete.** The
  finite points of `P(ω+1)` modulo adjacency *are* the real line, with reciprocal
  and negation given by set complement. The order is intrinsic (built from the lex
  order and the bitwise supremum); the field operations are transported, which is
  what makes item 5 the remaining work rather than a flourish.
- `SternBrocot.rat_induction` — **induction along the tree**. `P 0`, closed under
  `q ↦ q + 1`, `q ↦ q / (q+1)` and negation, proves `P` for every rational. A
  genuinely different induction from Mathlib's `num`/`den` one, and the right
  tool when the tree structure is the subject. It does **not** reach `ℝ`: the
  moves generate exactly `ℚ`, so the extension step is density plus closure,
  which is ordinary and which Mathlib already supports. That boundary is stated
  in the file rather than left implicit.
- `SternBrocot.tailEqv_iff_eqvGen` — the equivalence relation generated by
  `TailPair` adds nothing: every class has at most two elements. This is what
  makes the quotient statement of rigidity honest rather than a proxy.

## Roadmap

Ordered as planned. Items 1a–1c are done.

1. **Rigidity theorem** ✅ — done, including the quotient form and the
   `≤ 2 elements per class` structure lemma.
2. **`Φ : P(ω)/∼ ≃o ℝ`** — the order isomorphism.
   - ✅ completeness upstairs: `isLexLUB_lexSup`, computed bitwise;
   - ✅ density of the quotient: `exists_between_of_not_tailEqv`;
   - ✅ the countable dense subset: `nodeValue_bijOn`, canonical paths ≃ `ℚ≥0`;
   - ✅ the order embedding: `pathLt_iff_nodeValue_lt`. No canonicity needed —
     paths differing only by trailing left moves are `PathLt`-incomparable *and*
     equal-valued. There is **no** orientation flip: both moves are strictly
     increasing and their ranges `[0,1)` and `[1,∞)` are disjoint, so lex and
     numeric order agree uniformly. (I expected a flip here; there isn't one.)
   - ✅ the bridge: `pathLt_iff_lexLt`, `range_toSet`, `toSet_injOn_canonical`.
     Canonical paths biject with the finite subsets of `ω`, and `PathLt` is `<ₗ`
     on the nose. No `Classical` was needed after all — the `Set ℕ → List Bool`
     direction is stated as existence (`exists_path_of_subset_Iio`) rather than
     built as a function, so the case split lives in a proof.
   - ✅ (a) `toReal₀` defined and monotone (`toReal₀_mono`); (b) constant on tail
     classes (`toReal₀_of_tailEqv`); and `toReal₀_toSet` — it reproduces `nodeValue`
     on the nodes, which is what pins it down as *the* Stern–Brocot map.
   - 🔨 **next: (c) surjectivity onto `ℝ≥0` and (d) injectivity on the
     quotient.** For (c): given `r ≥ 0`, take `x = {n | ...}` cut out by the
     nodes below `r`; concretely, `x` should be the sup in `P(ω)` of
     `{toSet bs | nodeValue bs < r}`, which `isLexLUB_lexSup` supplies. For (d):
     if `¬ TailEqv x y` and `x <ₗ y`, density (`exists_between_of_not_tailEqv`)
     gives a point between, and then a *node* between, so the cuts differ.
     Watch: (d) needs **two** nodes between, or one node plus strictness.
     **Codomain settled: `Φ₀` targets `ℝ≥0` and is scaffolding.** The final map
     is signed, `Φ : Signed/SEqv ≃o ℝ`, obtained by mirroring `Φ₀` across the
     sign coordinate. `Φ₀` is unsigned only because the sup formula runs on the
     lex order where the nodes are `ℚ≥0`; writing it signed directly means a
     case split in every proof for no extra result. The class of `ω` (all finite
     bits) is dropped, so reciprocal goes partial at `0`.
   - ✅ the signed order (`SignedOrder.lean`): sign first, then lex, reversed on
     negatives. `slexLt_neg` (negation antitone), `lift_slexLt_iff` (the positive
     half is an order-embedded copy of `(P(ω), <ₗ)`, so `Φ₀` transfers), and
     `seqv_equivalence` for the full quotient `SEqv = STailEqv ∪ ZeroDegen`.
   - ⬜ extend to all of `P(ω)/∼` by `Φ x = sup {ι q | q < x}`, using
     completeness on both sides;
   - ✅ the sign coordinate: `magnitude` (stored bit xor sign), `toReal`, and
     `toReal_neg : Φ(-x) = -Φ(x)`. `magnitude_neg` is a rewrite, not a case split —
     the mirrored convention's payoff. Both zeros land on `0` (`toReal_empty`,
     `toReal_univ`), so `-0 = 0` needs no special casing. `toReal_of_seqv` descends it
     to the full quotient.
   - ✅ `Φ` monotone (`toReal_mono`), surjective onto **all of `ℝ`**
     (`exists_toReal_eq`) and injective on the quotient (`toReal_injective`).
     The mixed-sign case of injectivity is exactly the two zeros: equal values
     across the sign boundary squeeze both to `0`, forcing `x = univ` and
     `y = ∅`, which is the `ZeroDegen` pair. So the zero adjacency is not an
     extra hypothesis anywhere — it *falls out* of injectivity.
   - ✅ packaged: `SBReal` (finite points modulo adjacency), `orderIsoReal :
     SBReal ≃o ℝ`, and `Field SBReal` transported along the bijection. `ring`
     works on `SBReal`. **Item 2 is complete.**
   Transport the field structure across `Φ`; the axioms then come for free.

   **Do not substitute the binary-expansion map for `Φ`.** Reading `x` as
   `Σ_{n∈x} 2^(-(n+1))` is also an order iso with exactly the tail pairs as
   fibres, and it is far less work — but it differs from the Stern–Brocot map by
   an order automorphism of `[0,1]` (Minkowski's `?`), so arithmetic transported
   along it is not the arithmetic Gosper computes, and item 5 below would
   silently become false.

   Order of work: **the field comes from transport, before and independent of
   Gosper.** Gosper's correctness is stated *against* the transported
   operations, so it needs them to already exist.
3. **Lagrange's theorem** — CF expansion is eventually periodic iff the number
   is a quadratic irrational. Periodicity of the `L`/`S` sequence is immediate
   in this encoding; the proof route is `SL₂(ℤ)` eigenvectors. Check current
   Mathlib first — `GenContFract` exists, this theorem did not as of writing.
4. **`Gosper.lean`** — the `2×2×2` integer tensor, with absorb/emit as integer
   matrix multiplications. The hand-derived rewrite rules become `#eval` test
   cases against the tensor. Two of the sixteen original rules were wrong and
   need the corrected forms:
   - `Sa - Lb → a + 1/Sb` (not `1/Lb`)
   - `La - Lb → -L((b-a)/S(SSb*a))` in the `a < b` branch (arguments swap)
5. **Intrinsic `+` and `×`** — prove the corecursive operations agree with the
   transported ones. Hard: Lean 4's productivity support is weaker than Coq's,
   which is precisely what makes it a CPP/ITP-shaped contribution.

## Watch out in `Phi.lean`

- `below a ⊆ below b` for a tail pair `(a, b)` is **not** immediate — it fails if
  `b` is itself a node. It holds because the *right* element of a tail pair is
  cofinite, hence infinite, hence never a node. That step is load-bearing; I got
  it wrong first time.
- `toReal₀` is junk at `univ` (`Real.sSup` of an unbounded set is `0`), so every
  lemma about it carries an `x ≠ univ` hypothesis. `toSet_ne_univ` discharges it
  for nodes.

## Conventions

- Everything lives in `namespace SternBrocot`.
- `<ₗ` is scoped notation for `LexLt`; `∆` is Mathlib's `symmDiff`
  (`open scoped symmDiff`).
- Lists in `Node.lean` are read with the **head applied last**, so the head is
  the move nearest the root. A word ending in `true` is a tree node.
  `nodeValue` is `M(0)`, the value of the path padded with left moves — which is
  the point of `P(ω)` the corresponding finite set denotes, *not* the mediant
  label `M(1)`. `nodeValue_append_false` is what makes this coherent.
- No `LinearOrder` instance yet: `Set ℕ` already carries the `⊆` order, so the
  lex order lives as bare relations `<ₗ` and `≤ₗ`. Introduce a type synonym with
  the instance when assembling the ordered field, not before.
- **The mirrored sign convention (B′).** `none ∈ x` means *negative*, so
  positives carry no sign bit and the naturals keep their `Basic.lean` form —
  `1 = {0}`, `2 = {0,1}`. Protecting that is why the sign polarity is this way
  round and not the other. The negative branch stores the **complement** of the
  magnitude's path, so:
    * `neg = complement` (`x ∆ (ω ∪ {ω})`), `recipS = x ∆ ω`, `x ∆ {ω}` = `-1/x`;
    * `+0 = ∅`, `-0 = univ`, `-∞ = {ω}`, `+∞ = ω`;
    * same-sign comparison is **forward lex on both sides**, because
      `compl_lexLt_compl` says complement reverses lex. `SLexLt` has two
      disjuncts, not three, and `slexLt_neg` needs no case analysis.
  Do not flip the polarity to make the order plain lex — that costs the naturals,
  which is the wrong trade for this project.
- **`-0 = 0` is an adjacency, not a postulate.** `univ` and `∅` are the largest
  negative and smallest positive with nothing between (`nothing_between_zeros`),
  so the quotient identifies exactly the *adjacent* pairs: tail pairs inside each
  sign, plus `(univ, ∅)` at the sign boundary. `zeroPair_isolated` is what makes
  it safe — neither endpoint is in a tail pair, so classes stay at size ≤ 2.
  `±∞` are the order's endpoints, so correctly left distinct.
- Tail pairs are written `(a, b)` with `a` the side carrying the branch point,
  which is always the *larger* one: `lexLt_of_tailPair : TailPair a b → b <ₗ a`.
  Getting this orientation backwards is the easiest mistake in this development.

## Known environment issue

Several files written during initial project creation landed on disk with
correct metadata size but no readable content — `lake new`'s templates
(`lakefile.toml`, `lean-toolchain`, `README.md`, and the stub `.lean` files) and
a number of Mathlib's `.github`/`.docker` files. The Lean templates were
rewritten by hand; Mathlib's `Mathlib/**.lean` sources spot-checked clean and
the oleans are intact, so builds are unaffected. `git status` inside the Mathlib
checkout still reports `short read while indexing` for the affected files.
