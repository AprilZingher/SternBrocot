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

1. **Gosper on ℚ** — ✅ **the loop is closed** (`GosperRat.lean`).
   `Tensor.absorbLeftPath`/`Tensor.absorbRightPath` feed whole paths in; `pathOf` is the
   Euclidean algorithm as a *function* (well-founded on `a + b`); `gosperAdd`
   and `gosperMul` take two paths and return a canonical path, with
   `nodeValue_gosperAdd`/`nodeValue_gosperMul` proving the values are the sum and
   product. It runs: `#eval gosperAdd [false,true] [true,true]` gives
   `[true,true,false,true]` = `5/2`, and `toPath (22/7)` reproduces the
   hand-derived `path22over7` exactly.
   **Next in this file**: package as a `Field` instance on canonical paths (or on
   `ℚ` via the bijection) and give `≃+*` to Mathlib's `ℚ`. Note `pathOf` is
   well-founded recursion, so it does **not** reduce by `rfl`/`decide` — concrete
   checks need `#eval` or the general theorems, not kernel computation.

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

4. **Lagrange's theorem** — independent, Mathlib-shaped, and **available now**:
   it does *not* need productivity. Productivity is about computing a path; every
   real already *is* a subset of `ω+1` (`exists_toReal_eq`), so periodicity is
   just a property of that set and needs no algorithm. What it needs: the shift
   on paths and its effect on values (drop bit `0`: `x ↦ x - 1` after `S`,
   `x ↦ x/(1-x)` after `L`), then periodicity ⟺ `x` is a fixed point of a Möbius
   map in `SL₂(ℤ)`, giving a quadratic. The `SL₂` half is already built —
   `pathMat`, `pathMat_det`.

   **State it correctly.** In this encoding a *rational* has an eventually
   **constant** path, hence an eventually periodic one. Classical Lagrange
   excludes rationals via "infinite continued fraction", and that exclusion does
   not survive translation. The true statement is

   > the path of `x` is eventually periodic **iff** `[ℚ(x) : ℚ] ≤ 2`

   — rational *or* quadratic irrational. "iff quadratic irrational" is **false**
   here and would compile fine as a skeleton.

   Verify against current Mathlib before starting — `GenContFract` exists, this
   theorem did not as of writing.

5. **Other classical CF theorems Mathlib lacks.** Surveyed against this Mathlib;
   all confirmed absent (beware false positives — the `Hurwitz`, `Legendre` and
   `Steinhaus` hits are Hurwitz *zeta*, Legendre *symbol*, Banach–*Steinhaus*).

   | theorem | encoding helps? |
   |---|---|
   | **Hurwitz** — `1/(√5 q²)` infinitely often, √5 optimal | yes: φ is the all-run-length-1 path, visibly extremal |
   | **Legendre** — `< 1/(2q²)` ⟹ `p/q` is a convergent | partly: convergents are the nodes along the path |
   | **badly approximable ↔ bounded partial quotients** | yes: bounded run-lengths in the bit string |
   | three-distance / Steinhaus | not obviously |
   | Gauss–Kuzmin | no — needs ergodic theory |

   Mathlib *has*: CF basics, continuants, determinant, convergence,
   `TerminatesIffRat`, Dirichlet approximation, and
   `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational` (the `1/q²` version;
   needs `import Mathlib.NumberTheory.DiophantineApproximation.Basic`, not currently
   in this project's import closure).
   Hurwitz is the natural next one — the `1/q²` case and `goldenRatio` are both
   already there, so it is the √5 refinement that is missing.

   These are *classical results missing from a library*, not open problems. The
   wall at algebraic degree ≥ 3 is real and none of these touch it. But together
   they make this a plausible small library rather than a single contribution.

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
| `GosperRat.lean` | the machine on rational inputs: paths in, path out |
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
