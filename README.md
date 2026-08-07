# SternBrocot

A Lean 4 + Mathlib formalization of the Stern–Brocot representation of the
reals, in which the carrier is literally `P(ω) = Set ℕ`, reciprocal is literally
set complement, and negation is symmetric difference with one adjoined point.

The encoding reads a set `x ⊆ ω` as a bit stream `b n = (n ∈ x)`, which is a path
down the Stern–Brocot tree:

| object | definition |
|---|---|
| left move | `L x = {y ∪ {y} : y ∈ x}` — prepend a `0` bit |
| right move | `S x = L x ∪ {0}` — prepend a `1` bit; the von Neumann successor |
| reciprocal | `recip x = xᶜ` — flips every bit, so `J L J = S` |
| tail rule | `s ⌢ 1 ⌢ 0^∞ ∼ s ⌢ 0 ⌢ 1^∞`, i.e. `s R L^∞ = s L R^∞` |

The tail rule is the only redundancy in the encoding.

## Results so far

- **The rigidity theorem** (`SternBrocot.rigidity`). For `m ⊆ ω`, the Boolean
  translation `x ↦ x ∆ m` descends to the tail quotient **iff** `m = ∅` or
  `m = ω` — that is, iff it is the identity or reciprocal. This is a no-go
  theorem: the Boolean structure on `P(ω)` supports exactly the `PGL₂` torsion
  elements and nothing else, so addition was never going to be a Boolean
  operation on this encoding.
- **The key lemma** (`tailPair_iff_isAdjacent`). Two sets form a tail pair
  exactly when they are adjacent in the lex order. The quotient collapses
  precisely the jumps, so `P(ω)/∼` is densely ordered.
- **Completeness** (`isLexLUB_lexSup`). Every subset of `P(ω)` has a least upper
  bound in the lex order, computed bitwise. No nonemptiness hypothesis is
  needed: `∅` is `0` and `univ` is `∞`.
- **The enumeration theorem** (`nodeValue_bijOn`). The tree enumerates `ℚ≥0`
  exactly once: `nodeValue` is a bijection from canonical finite paths onto the
  nonnegative rationals, and by unimodularity (`pathMat_det`) each value arrives
  already in lowest terms.
- **The order embedding** (`pathLt_iff_nodeValue_lt`) and **the bridge**
  (`pathLt_iff_lexLt`). Canonical paths biject with the finite subsets of `ω`,
  and the lex order on the carrier is exactly the order of the values.

- **The construction** (`orderIsoReal : SBReal ≃o ℝ`). The finite points of
  `P(ω+1)`, modulo the quotient that collapses adjacent pairs, are *order
  isomorphic to the real line*. Negation is set complement; reciprocal is
  complement of the finite coordinates. `SBReal` carries a `Field` instance, so
  `ring` works on it.

The order is intrinsic — built here from the lex order and a bitwise supremum.
The field operations are transported across the isomorphism, which is the honest
status of the current state: this shows the carrier *faithfully represents* `ℝ`.
Making `+` and `×` intrinsic — Gosper's algorithm on the bit streams, proved
correct against `toReal₀_toSet` — is the work in progress.

No `sorry`, no `native_decide`. Every result depends only on `propext`,
`Classical.choice`, and `Quot.sound`.

## Layout

| file | contents |
|---|---|
| `SternBrocot/Basic.lean` | the moves, reciprocal, the tail relation, rigidity |
| `SternBrocot/Tail.lean` | tail classes have ≤ 2 elements; rigidity on the quotient |
| `SternBrocot/Order.lean` | the lex order; tail relation = adjacency |
| `SternBrocot/Completeness.lean` | the bitwise supremum; density of the quotient |
| `SternBrocot/Node.lean` | values of finite paths; unimodularity |
| `SternBrocot/Enumeration.lean` | the tree enumerates `ℚ≥0` exactly once |
| `SternBrocot/PathOrder.lean` | `nodeValue` is an order embedding |
| `SternBrocot/Bridge.lean` | paths ↔ finite subsets of `ω` |
| `SternBrocot/Signed.lean` | `P(ω+1)`, negation as complement, signed rigidity |
| `SternBrocot/SignedOrder.lean` | the mirrored sign order; the full quotient |
| `SternBrocot/ToReal.lean` | `Φ₀ : P(ω) → ℝ≥0` as a Dedekind cut |
| `SternBrocot/SignedToReal.lean` | `Φ : P(ω+1) → ℝ`, monotone and bijective |
| `SternBrocot/Field.lean` | `SBReal ≃o ℝ` and the field structure |
| `SternBrocot/Examples.lean` | machine-checked sanity checks of the encoding |

`Examples.lean` is worth reading first if you want to know what is actually being
claimed: it restates the concrete facts about the encoding as theorems, so that
the compiler checks the definitions mean what they are described as meaning.

## Building

```bash
lake exe cache get   # fetch prebuilt Mathlib oleans (~7.7 GB); skip and you
                     # compile Mathlib from source for hours
lake build
```

Toolchain `leanprover/lean4:v4.32.2`, Mathlib `v4.32.2`.

## Status and provenance

Work in progress. The roadmap, conventions, and open decisions are in
`CLAUDE.md`.

Developed with Claude Code. Everything here is machine-checked — Lean either
accepts a proof or it does not — but the *statements* are the part a reader
should scrutinise, which is what `Examples.lean` exists to support.
