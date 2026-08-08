# SternBrocot — the reals as subsets of ω

Lean 4 + Mathlib. The carrier is literally `P(ω+1) = Set (Option ℕ)`, reciprocal
is literally set complement, negation is complement too, and the naturals are the
von Neumann ordinals unchanged.

## Status in one paragraph

**The construction is complete**: `orderIsoReal : SBReal ≃o ℝ`, and `SBReal`
carries a `Field` instance (`ring` works on it). The *order* is intrinsic — built
here from the lex order and a bitwise supremum, never mentioning `ℝ`. The *field
operations* are transported from `ℝ` along the isomorphism. By uniqueness of
complete ordered fields that transport had no freedom in it (see
`toRealQ_add_eq_sSup`: the order alone determines `+`), so the mathematics is
settled — but the *definition* still mentions `ℝ`, and closing that is the main
remaining work. ~4,200 lines, no `sorry`, everything on `propext`,
`Classical.choice`, `Quot.sound`.

## Setup

- Toolchain `leanprover/lean4:v4.32.2`; Mathlib `v4.32.2` rev `905b9581…`
- `lake build` from this directory. Oleans came from `lake exe cache get`.
- **Never `lake build` from inside `.lake/packages/mathlib`** — a stray `cd`
  there once made the build target Mathlib itself.

## The encoding

A set `x ⊆ ω` is the bit stream `b n = (n ∈ x)`: a path down the tree.

| object | definition |
|---|---|
| left move | `L x = {y ∪ {y} : y ∈ x}` — prepend a `0` bit |
| right move | `S x = L x ∪ {0}` — prepend a `1`; the von Neumann successor |
| reciprocal | `recip x = xᶜ` |
| negation | complement in `P(ω+1)` |
| tail rule | `s ⌢ 1 ⌢ 0^∞ ∼ s ⌢ 0 ⌢ 1^∞` |

The quotient identifies exactly the **adjacent** pairs: tail pairs within each
sign, plus `(univ, ∅)` = `(-0, +0)` at the sign boundary. One rule, no special
cases.

## Next steps

In the order they should be done. Items 1 and 2 are the real remaining work;
3 and 4 are independent.

1. **Gosper on ℚ** — 🔨 in progress in `GosperRat.lean`. ✅ the absorb phase:
   `absorbLeftPath`/`absorbRightPath` feed a whole path into an input, and
   `add_paths`/`mul_paths`/`sub_paths` say the tensor fed both paths has the sum,
   product, difference as its value. It *runs* — `#eval` gives `5/2` for
   `1/2 + 2`. No coinduction needed: rational inputs are finite paths, and the
   emit guard `z ≥ 1` is decidable here, which is exactly why this half is easy
   and the real case is not.
   **Next in this file**: the emit phase as a *function* — currently
   `exists_canonical_of_nonneg` only gives existence of the output path, so the
   Euclidean algorithm needs writing as a definition (`decreasing_by` on
   `num + den`). Then package as `Field` on canonical paths and give `≃+*` to
   Mathlib's `ℚ`.

2. **Intrinsic `+` and `×` on ℝ by density — closes the independence gap.**
   Define them as suprema of their values on nodes (`toRealQ_add_eq_sSup` shows
   the sup-definition lands on the same operation, so nothing is lost), then
   derive the field axioms from ℚ's by density and continuity. After this the
   construction never mentions `ℝ`. **This does not need Gosper**, which is the
   key realisation — Gosper was blocking something it never actually blocked.

3. **Gosper productivity — the open/paper piece.** Running the machine forever
   on irrational inputs and proving it always eventually emits. Lean 4 has no
   native cofixpoint with a guardedness checker, so this is genuinely harder than
   Coq, which is precisely what makes it CPP/ITP-shaped. Note: **continuity
   arguments cannot supply this** — proving a function continuous presupposes it
   is total, which is what productivity would establish.

4. **Lagrange's theorem** (independent, Mathlib-contribution-shaped). CF
   expansion is eventually periodic iff quadratic irrational. Periodicity of the
   `L`/`S` sequence is immediate in this encoding; route is `SL₂(ℤ)`
   eigenvectors. Verify against current Mathlib first — `GenContFract` exists,
   this theorem did not as of writing.

## Files

| file | contents |
|---|---|
| `Basic.lean` | moves, reciprocal, `TailPair`, **rigidity** |
| `Tail.lean` | tail classes have ≤ 2 elements; rigidity on the quotient |
| `Order.lean` | lex order; `≤ₗ`; **tail relation = adjacency**; complement reverses lex |
| `Completeness.lean` | the bitwise supremum; density of the quotient |
| `Node.lean` | values of finite paths; unimodularity |
| `Enumeration.lean` | **the tree enumerates `ℚ≥0` exactly once** |
| `PathOrder.lean` | `nodeValue` is an order embedding |
| `Bridge.lean` | paths ↔ finite subsets of `ω`; addition is not Boolean |
| `Signed.lean` | `P(ω+1)`; negation = complement; **signed rigidity** |
| `SignedOrder.lean` | the mirrored sign order; the full quotient |
| `ToReal.lean` | `Φ₀ = toReal₀ : P(ω) → ℝ≥0`, a Dedekind cut |
| `SignedToReal.lean` | `Φ = toReal : P(ω+1) → ℝ`; monotone, bijective |
| `Induction.lean` | induction along the tree (reaches `ℚ`, not `ℝ`) |
| `Field.lean` | **`SBReal ≃o ℝ`**; the field structure |
| `Gosper.lean` | the 2×2×2 tensor; absorb/emit correctness; the rules |
| `Examples.lean` | machine-checked checks that the definitions mean what is claimed |

## Headline results

- `rigidity` — `x ↦ x ∆ m` descends to `P(ω)/∼` **iff** `m = ∅` or `m = ω`. The
  no-go theorem: the Boolean structure carries exactly the `PGL₂` torsion
  elements. `signedRigidity` is the `P(ω+1)` version — adjoining one point buys
  negation and `-1/x` and nothing else. `addOne_not_symmDiff` is the concrete
  form: no mask implements "add one".
- `tailPair_iff_isAdjacent` — **the key lemma**, on which everything downstream
  rests. Tail pairs are exactly adjacent pairs.
- `nodeValue_bijOn` — the tree enumerates `ℚ≥0` exactly once, in lowest terms.
- `orderIsoReal : SBReal ≃o ℝ` — the construction.
- `rat_induction` — induction along the tree. Reaches `ℚ`; **not** `ℝ`.

## Traps

Things that cost time to rediscover.

- **Orientation.** Tail pairs are written `(a, b)` with `a` the side carrying the
  branch point, which is the *larger*: `lexLt_of_tailPair : TailPair a b → b <ₗ a`.
  Easiest mistake in the development.
- **Lists have the head applied last**, so the head is the move nearest the root.
  A word ending in `true` is a node. `nodeValue` is `M(0)` — the value of the path
  padded with left moves, *not* the mediant label `M(1)`.
- **The mirrored sign convention.** `none ∈ x` means *negative*, so positives
  carry no sign bit and `1 = {0}`, `2 = {0,1}` are untouched. The negative branch
  stores the **complement** of the magnitude's path, which is why same-sign
  comparison is forward lex on *both* sides (`compl_lexLt_compl`) and `SLexLt`
  has two disjuncts, not three. **Do not flip the polarity** to make the order
  plain lex — it costs the naturals, which is the wrong trade here.
- **`toReal₀` is junk at `univ`** (`Real.sSup` of an unbounded set is `0`), so its
  lemmas carry `x ≠ univ`. `toSet_ne_univ` discharges it for nodes.
- **`below a ⊆ below b` for a tail pair is not immediate** — it fails if `b` is a
  node. It holds because the *right* element of a tail pair is cofinite, hence
  never a node. Load-bearing; I got it wrong first time.
- **No `LinearOrder` on `Set ℕ`** — it already carries `⊆`. The lex order lives as
  bare relations `<ₗ`, `≤ₗ`. A type synonym was tried and deleted as dead weight:
  the *quotient* carries the order instead, which is the better design.
  `lexLt_iff_piLex` records that this is Mathlib's standard `Pi.Lex` order.

## Style

- Prefer examples that pin a **definition** to intent by connecting things defined
  independently (`toSet [true,true] = S (S ∅)`). Delete examples that merely
  restate a theorem — they only fail if a theorem stops being itself.
- Everything in `namespace SternBrocot`. `∆` needs `open scoped symmDiff`.

## Known environment issue

Some files written at project creation landed with correct metadata size but no
readable content — `lake new`'s templates, and some of Mathlib's `.github`
files. The templates were rewritten by hand; Mathlib's `.lean` sources and oleans
are intact, so builds are unaffected. `git status` inside the Mathlib checkout
still reports `short read while indexing`.
