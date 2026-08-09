# SternBrocot

A Lean 4 + Mathlib formalization in which the real numbers are literally subsets
of `ω + 1`. The carrier is `P(ω+1) = Set (Option ℕ)`, reciprocal is set
complement, negation is set complement, and the naturals are the von Neumann
ordinals unchanged.

A set `x ⊆ ω` is read as the bit stream `b n = (n ∈ x)`, which is a path down
the Stern–Brocot tree:

| object | definition |
|---|---|
| left move | `L x = {y ∪ {y} : y ∈ x}` — prepend a `0` bit |
| right move | `S x = L x ∪ {0}` — prepend a `1` bit; the von Neumann successor |
| reciprocal | `recip x = xᶜ` — flips every bit, so `J L J = S` |
| negation | complement in `P(ω+1)` |
| tail rule | `s ⌢ 1 ⌢ 0^∞ ∼ s ⌢ 0 ⌢ 1^∞`, i.e. `s R L^∞ = s L R^∞` |

The tail rule is the only redundancy. The quotient identifies exactly the
**adjacent** pairs — tail pairs within each sign, plus `(univ, ∅) = (−0, +0)` at
the sign boundary. One rule, no special cases.

**Nothing in the repository has a `sorry`**, and every result depends only on
`propext`, `Classical.choice`, and `Quot.sound`.

## The construction

`SBReal` — the finite points of `P(ω+1)` modulo adjacency — is a **complete
ordered field**, with each defining clause stated rather than merely implied:

- `Field SBReal`;
- `instIsStrictOrderedRingSBReal` — the order is compatible with `+` and `×`;
- `exists_isLUB` — every nonempty bounded-above set has a least upper bound;
- `orderIsoReal : SBReal ≃o ℝ` — exhibiting the uniqueness.

`ring` and `linarith` both work on it.

### The order is the lex order

```lean
mk_lt_mk_iff : mk a ha < mk b hb ↔ (a <ₛ b ∧ ¬ SEqv a b)
```

with `mk_le_mk_iff` for `≤`. No `ℝ` appears on either side. This matters more
than it looks: `SLexLt` is built from the bit strings alone, so the theorem is
what stops `exists_isLUB` and `instIsStrictOrderedRingSBReal` — both statements
*about this relation* — from being facts about `ℝ`'s order under another name.

The `¬ SEqv` conjunct is the whole content and is not redundant. A tail pair is
strictly lex-below **on the nose** while having equal value, so lex-below alone
does not give a strict inequality on the quotient. The two conditions differ
exactly on the pairs the quotient collapses.

### What is and is not `ℝ`-free

Being precise about this, because it is easy to overstate and this project has
overstated it before:

| | status |
|---|---|
| the carrier, the moves, the order | `ℝ`-free |
| the order **on the quotient** | pinned to `SLexLt` by `mk_lt_mk_iff` |
| the *definitions* of `+` and `×` | `ℝ`-free (`Core/IntrinsicCore.lean`) |
| the *proofs* of the field axioms | still routed through `toReal` |

`a + b` is defined as `sup {ratPoint (p+q) : ratPoint p <ₛ a, ratPoint q <ₛ b}`
with the inner `+` rational, so there is no circularity, and
`add'_eq_add` / `mul'_eq_mul` prove these are the operations `Real/Field.lean`
transports. Installing them as the instance is not a mechanical swap — the axiom
statements use `0`, `1`, `-a`, `a⁻¹` from the transported instance, so it needs
intrinsic versions of those first.

The `ℝ`-free claim is **structural**: `SternBrocot/Core/` is closed under
imports and reaches `Mathlib`'s `Real` nowhere, which `scripts/check-core-closed.sh`
verifies with a grep rather than a build.

## Results

### The encoding is forced, not chosen

- **The rigidity theorem** (`rigidity`). For `m ⊆ ω`, the Boolean translation
  `x ↦ x ∆ m` descends to the tail quotient **iff** `m = ∅` or `m = ω` — iff it
  is the identity or reciprocal. A no-go theorem: the Boolean structure on
  `P(ω)` supports exactly the `PGL₂` torsion elements and nothing else, so
  addition was never going to be a Boolean operation here. `signedRigidity` is
  the `P(ω+1)` version — adjoining one point buys negation and `-1/x` and
  nothing more; `addOne_not_symmDiff` is the concrete form.
- **The key lemma** (`tailPair_iff_isAdjacent`). Two sets form a tail pair
  exactly when they are adjacent in the lex order, so the quotient collapses
  precisely the jumps.
- **The enumeration theorem** (`nodeValue_bijOn`). The tree enumerates `ℚ≥0`
  exactly once, and by unimodularity (`pathMat_det`) each value arrives already
  in lowest terms.

### Continued fractions

Confirmed absent from this Mathlib before starting; `GenContFract` exists, these
theorems do not.

- **Lagrange's theorem, both directions** (`eventuallyPeriodic_iff_degLeTwo`).
  The path of `x` is eventually periodic **iff** `[ℚ(Φ₀x) : ℚ] ≤ 2`.

  Stated as degree ≤ 2, not "quadratic irrational" — in this encoding a rational
  has an eventually **constant** path, so it is on both sides. The forward half
  is a Möbius fixed point; the hard half is reduction theory of binary quadratic
  forms, where the estimate `abs_formAt_le` and the invariance of the
  discriminant confine the forms along the path to a finite box.

  The encoding earns its keep in the back end: equal values of `Φ₀` at two
  shifts give tail-equivalence, and a tail pair always has a *rational* common
  value, so irrationality makes the two shifted points literally **equal**.
  Periodicity comes out on the nose, with no reconstruction step.

- **Hurwitz's theorem** (`exists_hurwitz_approx_real`), with `√5` optimal
  (`sqrt5_optimal`).

- **Legendre's theorem** (`legendre`). For **irrational** `Φ₀x`: if
  `|Φ₀x − p/q| < 1/(2q²)` with `q > 0` and `p/q` in lowest terms, then `p/q` is a
  convergent. Via best approximation of the second
  kind (`contin_best_approx_gen`), which is the lattice argument: unimodularity
  makes two consecutive convergents a basis of `ℤ²` and the straddling makes the
  two errors opposite in sign, so they add rather than cancel.

- **Badly approximable ⟺ bounded partial quotients**
  (`badlyApproximable_iff_boundedPartialQuot`). Both directions run on a single
  identity — `qₖ₊₁|qₖα − pₖ| + qₖ|qₖ₊₁α − pₖ₊₁| = 1`, unimodularity and
  straddling combined. `goldenRatio_badlyApproximable` is the extremal instance:
  every partial quotient of `φ` is `1`.

- **The convergents** (`CF/Convergent.lean`). The convergents are the prefixes at
  **run boundaries** — `boundaryMat_eq_contin` is where that lives — with the
  classical recurrence falling out of `pathMat`, the estimate
  `|Φ₀x − pₖ/qₖ| < 1/(qₖqₖ₊₁)` strictly, and the exact error
  `1/(qₖ(qₖwₖ + qₖ₊₁))`.

### Gosper's algorithm

`Core/GosperRat.lean` closes the loop on `ℚ`: whole paths in, a canonical path
out, with `nodeValue_gosperAdd` / `nodeValue_gosperMul` proving the values are
the sum and product. Running it forever on irrational inputs — productivity — is
the open piece.

## Layout

The directory split is load-bearing, not cosmetic: `Core/` is closed under
imports, which is what makes its `ℝ`-freeness checkable without a build.

```
SternBrocot/
  Core/     the construction — ℝ-free, imports nothing outside Core/
  Real/     the map to ℝ
  CF/       the continued-fraction library, built on Real/
  Examples.lean
```

| file | contents |
|---|---|
| `Core/Basic.lean` | moves, reciprocal, `TailPair`, **rigidity** |
| `Core/Tail.lean` | tail classes have ≤ 2 elements; rigidity on the quotient |
| `Core/Order.lean` | lex order; **tail relation = adjacency**; complement reverses lex |
| `Core/Completeness.lean` | the bitwise supremum; density of the quotient |
| `Core/Node.lean` | values of finite paths; unimodularity |
| `Core/Enumeration.lean` | **the tree enumerates `ℚ≥0` exactly once** |
| `Core/PathOrder.lean` | `nodeValue` is an order embedding |
| `Core/Bridge.lean` | paths ↔ finite subsets of `ω`; addition is not Boolean |
| `Core/Density.lean` | density of the nodes |
| `Core/Signed.lean` | `P(ω+1)`; negation = complement; **signed rigidity** |
| `Core/SignedOrder.lean` | the mirrored sign order; the full quotient |
| `Core/Magnitude.lean` | magnitude and `IsFinite` |
| `Core/Induction.lean` | induction along the tree (reaches `ℚ`, not `ℝ`) |
| `Core/Gosper.lean` | the 2×2×2 tensor; absorb/emit correctness |
| `Core/GosperRat.lean` | the machine on rational inputs: paths in, path out |
| `Core/IntrinsicCore.lean` | **the intrinsic `+`, `×`, and `ratPoint`** |
| `Real/ToReal.lean` | `Φ₀ = toReal₀ : P(ω) → ℝ≥0`, a Dedekind cut |
| `Real/SignedToReal.lean` | `Φ = toReal : P(ω+1) → ℝ`; monotone, bijective |
| `Real/Field.lean` | **`SBReal ≃o ℝ`**; the field structure; **`mk_lt_mk_iff`** |
| `Real/IntrinsicAgreement.lean` | the intrinsic operations agree with the transported ones |
| `Real/Complete.lean` | **the ordered-field axioms and completeness**, stated |
| `CF/Degree.lean` | `DegLeTwo`; the `SL₂(ℤ)` action on it; `[ℚ(t) : ℚ] ≤ 2` |
| `CF/Shift.lean` | the shift; **the move recursion for `Φ₀`**; prefixes act by Möbius |
| `CF/Lagrange.lean` | eventually periodic ⟹ degree ≤ 2; rational ⟺ eventually constant |
| `CF/Convergent.lean` | run boundaries; the continuants; **the two estimates** |
| `CF/Hurwitz.lean` | **`1/(√5 q²)` infinitely often**; `√5` is optimal |
| `CF/Legendre.lean` | **Legendre's theorem**; best approximation of the second kind |
| `CF/BadlyApproximable.lean` | **badly approximable ⟺ bounded partial quotients** |
| `CF/Reduction.lean` | **Lagrange's hard half** — bounded forms; the pigeonhole; the `iff` |
| `Examples.lean` | machine-checked checks that the definitions mean what is claimed |

`Examples.lean` is worth reading first if you want to know what is actually
being claimed. It pins definitions to intent by connecting things defined
independently — `toReal₀ goldenPath = φ` where `goldenPath = {n | Even n}`, and
`contin {n | Even n} (k+1) = (fib (k+1), fib k)`, which is a real check that the
run decomposition computes the classical continued fraction, since `Nat.fib` is
defined in Mathlib with no reference to any of this.

## Building

```bash
lake exe cache get   # fetch prebuilt Mathlib oleans (~7.7 GB); skip and you
                     # compile Mathlib from source for hours
lake build
./scripts/check-core-closed.sh   # no Lean needed
```

Toolchain `leanprover/lean4:v4.32.2`, Mathlib `v4.32.2`.

## Status and provenance

Work in progress. The roadmap, conventions, traps, and open decisions are in
`CLAUDE.md`; per-item detail is in `HANDOFF.md`.

Two things are deliberately not claimed. The *proofs* of the field axioms still
route through `ℝ`, so this is a construction whose definitions are independent
of Mathlib's reals and whose justifications are not yet. And the continued
fraction theorems are stated about this encoding's paths, not about Mathlib's
`GenContFract` — bridging the two is one theorem (run lengths = partial
quotients) that has not been written.

Developed with Claude Code. Everything here is machine-checked — Lean either
accepts a proof or it does not — but the *statements* are the part a reader
should scrutinise, which is what `Examples.lean` exists to support. An
adversarial review of the prose found three claims that the Lean did not
support; they are recorded in `CLAUDE.md` rather than quietly corrected, because
the failure mode they represent is the one most worth guarding against here.
