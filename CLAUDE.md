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
remaining work. ~5,500 lines, no `sorry`, everything on `propext`,
`Classical.choice`, `Quot.sound`.

The first classical continued-fraction theorem is now in: **Lagrange's theorem,
forward direction** (`degLeTwo_of_eventuallyPeriodic`), together with the
degree-one case in both directions (`eventuallyConstant_iff_rat`).

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

**Recommended order: 5 (convergents) → 6 (Hurwitz) → 2 (intrinsic ops) → the
hard half of 4.** Item 5 is shared infrastructure that both 6 and the rest of 4
need, so it is cheapest first; Hurwitz is the smallest theorem on top of it and
validates that layer before a big proof bets on it. Item 2 is the only item that
changes what the project *is* — it removes `ℝ` from the definition — and it does
not invalidate any CF theorem proved before it (nothing in the Lagrange import
chain reaches `Field.lean`), so deferring it costs exposure, not rework.

**The ordering turns on a question this file has not settled**: is this a
*construction* ("the reals **are** `P(ω+1)`"), in which case item 2 is the
thesis and belongs before the library — or a *CF library* ("classical theorems
Mathlib lacks"), in which case the theorems are the thesis and item 2 can wait?
The status paragraph above claims the first, item 6 pitches the second. Decide.

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

4. **Lagrange's theorem** — 🟡 **forward direction done** (`Shift.lean`,
   `Degree.lean`, `Lagrange.lean`). It did *not* need productivity, as expected:
   every real already *is* a subset of `ω+1` (`exists_toReal_eq`), so
   periodicity is a property of that set.

   The statement, correctly: in this encoding a *rational* has an eventually
   **constant** path, hence an eventually periodic one, so the theorem is

   > the path of `x` is eventually periodic **iff** `[ℚ(x) : ℚ] ≤ 2`

   — rational *or* quadratic irrational. "iff quadratic irrational" is **false**
   here. `DegLeTwo` is the concrete form (a nonzero integer quadratic);
   `DegLeTwo.finrank_adjoin_le` plus `DegLeTwo.finiteDimensional` is the field
   theory. **Both** are needed: `Module.finrank` is `0` on an infinite-dimensional
   space, so `finrank ≤ 2` alone also holds of every transcendental.

   What is proved:
   - `toReal₀_S`, `toReal₀_L` — the move recursion `t ↦ t+1`, `t ↦ t/(t+1)`
     holds for `Φ₀` on *all* of `P(ω)`, not just the nodes. Both need
     `y ≠ univ`, since `Φ₀` is junk at `∞`. This is the analytic content;
     the rest is algebra.
   - `toReal₀_applyPath` — a finite prefix acts by `pathMat` as a Möbius map.
   - `degLeTwo_of_eventuallyPeriodic` — periodicity makes the value a fixed
     point of the block's Möbius map; `pathMat_ne_one` (a nonempty word is never
     the identity matrix) is the nondegeneracy.
   - `eventuallyConstant_iff_rat` — the degree-one case both ways; the analogue
     of Mathlib's `GenContFract.terminates_iff_rat`.
   - `degLeTwo_toReal_of_eventuallyPeriodic` — the signed version, on all of `ℝ`.
   - `Examples.lean` closes the loop concretely: `toReal₀ goldenPath = φ`, where
     `goldenPath = {n | Even n}`. Previously only the truncations were checked.

   **Remaining: the hard direction** — a quadratic *irrational* has an eventually
   periodic path. This is genuinely classical Lagrange and is a separate
   development: it needs the reduction theory of binary quadratic forms
   (bounded transformed coefficients along the path, then pigeonhole).
   One trap found while scoping it: the naive bound on the transformed form
   `q(a,c)` is `|A|(1/d² + (c/d)|t - t'|)`, and `c/d` is **not** bounded along a
   bit path (`L^n` gives `c/d = n`). The classical argument works because
   convergent denominators satisfy `qₙ ≤ qₙ₊₁`; the bit-path prefixes in the
   middle of a run do not, so the pigeonhole has to be run on the subsequence of
   run boundaries, not on every shift.

   Confirmed absent from this Mathlib before starting — `GenContFract` exists,
   this theorem does not.

   **Do item 5 first.** The pigeonhole runs on the convergents, which is exactly
   what item 5 builds.

5. **The convergents — shared infrastructure, and the thing to build next.**
   Both Hurwitz and the hard half of Lagrange need it, so it is paid for once.

   In this encoding the convergents are **not** the prefixes of the bit path.
   They are the prefixes at **run boundaries** — the positions where an `R`-run
   flips to an `L`-run or back. A prefix in the middle of a run is an
   intermediate mediant, not a convergent, and that distinction is the whole
   difficulty: the classical estimates hold at run boundaries and fail between
   them. This is the same fact as the `c/d` trap recorded under item 4.

   What to build:
   - **Run-boundary extraction.** From `x : Set ℕ` produce the increasing
     sequence of indices where the bit flips. The partial quotients are the run
     lengths. For an irrational `x` this sequence is infinite (the path is not
     eventually constant, by `eventuallyConstant_iff_rat`); for a rational it
     terminates, so statements will carry an irrationality hypothesis where
     classical ones say "infinite continued fraction".
   - **The recurrence** `pₙ = aₙ pₙ₋₁ + pₙ₋₂`, `qₙ = aₙ qₙ₋₁ + qₙ₋₂`. This
     should come out of `pathMat` evaluated at run boundaries almost directly —
     `pathMat` of an `R`-run and of an `L`-run are the two elementary matrices
     raised to the run length, and `pathMat_det` already gives `pₙqₙ₋₁ − pₙ₋₁qₙ
     = ±1`.
   - **The two estimates**: `qₙ ≤ qₙ₊₁` (this is what fails mid-run and is why
     the subsequence is necessary) and `|Φ₀ x − pₙ/qₙ| < 1/(qₙ qₙ₊₁)`.

   Relation to Mathlib: `GenContFract` has continuants, the determinant identity
   and convergence, but for *its* representation. Whether to bridge to it or
   rebuild here is an open call — bridging costs a translation between the run-
   length encoding and `GenContFract.of`, rebuilding costs the estimates. The
   estimates are probably cheaper than the bridge, and rebuilding keeps the
   development self-contained, but check before committing.

6. **Other classical CF theorems Mathlib lacks.** Surveyed against this Mathlib;
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

   **Hurwitz is the one to do first**, once item 5 is in place. Only the `√5`
   refinement is missing — Mathlib supplies the `1/q²` case and `goldenRatio`,
   and `Examples.toReal₀_goldenPath` now proves `Φ₀ {n | Even n} = φ` outright,
   which is the extremality witness. The standard proof takes any three
   consecutive convergents and shows at least one satisfies the bound, so it
   consumes item 5 and nothing else. It is the smallest theorem that
   demonstrates the convergent layer works.

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
| `Shift.lean` | the shift; **the move recursion for `Φ₀`**; prefixes act by Möbius |
| `Degree.lean` | `DegLeTwo`; the `SL₂(ℤ)` action on it; `[ℚ(t) : ℚ] ≤ 2` |
| `Lagrange.lean` | **eventually periodic ⟹ degree ≤ 2**; rational ⟺ eventually constant |
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
- `toReal₀_S` / `toReal₀_L` — the move recursion holds for the *supremum* value
  map, not just for `nodeValue` on finite paths. Everything about the shift
  rests on these two.
- `degLeTwo_of_eventuallyPeriodic` — Lagrange, forward direction.

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
- **The shift does not preserve `x ≠ univ`.** `{n | n ≥ 1}` is not `univ` but its
  shift is. So any argument iterating `toReal₀_S`/`toReal₀_L` down a path needs a
  separate branch for "some shift hits `univ`" — those points are exactly the
  cofinite ones, i.e. the upper representatives of the rationals, and
  `exists_rat_of_eventually_mem` disposes of them. Skipping this branch is the
  easiest way to prove a false lemma here.
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
