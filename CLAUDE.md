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
remaining work. ~7,000 lines, no `sorry`, everything on `propext`,
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

**Items 2, 5 and the Hurwitz half of 6 are done.** Remaining recommended order:
**the hard half of 4 → the rest of 6 → 3 (productivity).** Item 2 is the
only item that changes what the project *is* — it removes `ℝ` from the
definition — and it does not invalidate any CF theorem proved before it (nothing
in the Lagrange import chain reaches `Field.lean`), so deferring it costs
exposure, not rework.

The exact-error layer that Hurwitz needed is now in `Convergent.lean` and the
hard half of 4 should reuse it: `tailQuot` (`= [0; aⱼ, aⱼ₊₁, …]`, with
`inv_tailQuot : 1/wⱼ = aⱼ + wⱼ₊₁`), `denRatio` (with
`denRatio_succ : ρⱼ₊₁ = aⱼ + 1/ρⱼ`), and `abs_sub_contin_eq`.

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

2. **Intrinsic `+` and `×`** — ✅ **done** (`Intrinsic.lean`, no `sorry`). The
   definitions are `ℝ`-free: `slexSup` (the signed bitwise supremum — one case
   split off `lexSup`), `ratPoint : ℚ → Signed` (via `GosperRat.toPath`, the
   Euclidean algorithm), and
   `a + b = sup {ratPoint (p+q) : ratPoint p <ₛ a, ratPoint q <ₛ b}` with the
   inner `+` rational, so no circularity. All ten field axioms are proved, and
   `add'_eq_add` / `mul'_eq_mul` show they are the operations `Field.lean`
   transported — so installing them as the instance changes no theorem. That
   swap is the one thing left, and it is mechanical.

   **A distinction this file forced.** The *definitions* are now `ℝ`-free; the
   *proofs* of the axioms still go through `toReal`. The density argument is
   what would make the proofs `ℝ`-free too, and it is a separate step — the
   statements are already arranged so that swapping it in changes nothing else.
   Do not claim the strong form until the proofs stop mentioning `ℝ`.
   **This does not need Gosper**, which is the key realisation — Gosper was
   blocking something it never actually blocked.

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

   **Item 5 is now available.** The pigeonhole runs on the convergents, which is
   exactly what `Convergent.lean` builds: `runBoundary`, `contin`,
   `contin_den_le_succ` and `abs_sub_contin_lt`.

5. **The convergents** — ✅ **done** (`Convergent.lean`). The run-boundary
   decomposition, the recurrence, and both estimates, with no `sorry`.

   Confirmed while building it: the convergents are the prefixes at **run
   boundaries**, and `boundaryMat_eq_contin` is where that fact lives — at
   boundary `k+1` the two columns of `pathMat` of the prefix are `contin x (k+1)`
   and `contin x (k+2)`, consecutive convergents, in an order alternating with
   the run's bit. Mid-run one column is an intermediate mediant instead.

   One correction to what this file previously said. The bound
   `|Φ₀x − B/D| < 1/(CD)` holds at **every** prefix, not only at run boundaries —
   it is just `AD − BC = 1` plus `Φ₀x = (As+B)/(Cs+D)`. What the run boundary
   buys is that `C` and `D` are then consecutive *convergent* denominators, so
   that the bound reads `1/(qₖqₖ₊₁)` and `qₖ ≤ qₖ₊₁` is available. The estimate
   was never the hard part; the indexing is.

   **Indexing trap.** `contin x 0`, `contin x 1` are the seeds `(0,1)`, `(1,0)`,
   *swapped* when the path starts with a left move. That swap is the classical
   `a₀ = 0`: for `x < 1` no leading `R`-run is stored, so the sequence shifts by
   one. It is what lets one recurrence serve both `x ≥ 1` and `x < 1`. The price
   is that `contin x k` is a convergent only for `k ≥ 2` (and `q₁ = 0`), so every
   estimate is stated at `k + 2`.

   **Mathlib bridge: decided against, with measurements** — see `HANDOFF.md`.
   Short version: `GenContFract.of` is built from `⌊·⌋` and `Int.fract`, so
   bridging still requires identifying the run lengths with its partial
   quotients, which is the expensive half of the file; and Mathlib's estimate is
   non-strict where the one here is strict.

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

   **Hurwitz is ✅ done** (`Hurwitz.lean`), both the `1/(√5 q²)` statement and
   the optimality of `√5`. It consumed item 5 and nothing else, as predicted.
   The remaining rows — Legendre, badly approximable ↔ bounded partial
   quotients — are now the cheap ones: both are statements about `contin` and
   `partialQuot`, which exist.

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
| `Convergent.lean` | run boundaries; the continuants; **the two estimates** |
| `Hurwitz.lean` | **`1/(√5 q²)` infinitely often**; `√5` is optimal |
| `Field.lean` | **`SBReal ≃o ℝ`**; the field structure |
| `Intrinsic.lean` | **intrinsic `+`, `×` as suprema over nodes** |
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
- `toReal_addRaw` / `toReal_mulRaw` — the intrinsic operations, defined as
  suprema over the rational nodes with no mention of `ℝ`, compute `+` and `×`.
- `rat_induction` — induction along the tree. Reaches `ℚ`; **not** `ℝ`.
- `toReal₀_S` / `toReal₀_L` — the move recursion holds for the *supremum* value
  map, not just for `nodeValue` on finite paths. Everything about the shift
  rests on these two.
- `degLeTwo_of_eventuallyPeriodic` — Lagrange, forward direction.
- `boundaryMat_eq_contin` — the convergents are the columns of the prefix matrix
  **at run boundaries**; the classical recurrence falls out of `pathMat`.
- `abs_sub_contin_lt` — `|Φ₀x − pₖ/qₖ| < 1/(qₖqₖ₊₁)`, strictly.
- `abs_sub_contin_eq` — the **exact** error `1/(qₖ(qₖwₖ + qₖ₊₁))`. Hurwitz is
  this identity plus one relation between consecutive `wₖ + ρₖ`.
- `exists_hurwitz_approx_real` — Hurwitz on `ℝ`; `sqrt5_optimal` — `√5` is best.

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
- **The convergents are at run boundaries, and `contin` is indexed from 2.** The
  seeds `contin x 0`, `contin x 1` are `(0,1)`, `(1,0)` *swapped* when the path
  starts with a left move — that swap is the classical `a₀ = 0`, and it is what
  lets one recurrence serve both `x ≥ 1` and `x < 1`. So `q₁ = 0`, and every
  estimate is stated at `k + 2`. Do not special-case `x < 1` instead.
- **`{none}` is `−∞`, not `−0`.** `−0` is `univ` — negative, *all* finite bits
  set, magnitude `∅`. `{none}` is negative with *no* finite bits, so its
  magnitude is `univ` and it is the bottom of the order. The empty supremum
  lands on `{none}`, which is why a Dedekind cut used to define a product must
  carry an explicit `0` floor (`mulCut`); without it multiplication is infinite
  exactly at zero. Cost an hour to find.
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
