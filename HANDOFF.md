# Handoff

One section per queue item. Everything claimed here was checked by `lake build`
from the repo root; every named theorem below was checked with `#print axioms`
and depends only on `propext`, `Classical.choice`, `Quot.sound`.

## Environment note (read first)

The container came up with **no Lean toolchain at all** — no `elan`, no `lake`,
no `.lake/`. Install with

```
sh <(curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh) \
   -y --default-toolchain leanprover/lean4:v4.32.2
export PATH="$HOME/.elan/bin:$PATH"      # elan is NOT on the default PATH here
lake exe cache get && lake build
```

`lake exe cache get` makes two passes; the first (against the `mathlib4-master`
bucket) downloads 0 files and that is normal — the second, against `mathlib4`,
gets all 8639.

`Mathlib.Data.Real.Irrational` **does not exist** in this Mathlib revision.
`Irrational` lives in `Mathlib.NumberTheory.Real.Irrational`.

## Item 1 — COMPLETED

New file `SternBrocot/Convergent.lean` (585 lines, no `sorry`), plus a section
at the end of `Examples.lean`. Wired into `SternBrocot.lean`.

### What was proved

Infrastructure:

* `prefixWord x n` — the first `n` bits of the path, as a word;
  `applyPath_prefixWord` puts them back: `applyPath (prefixWord x n) (σⁿ x) = x`.
  This is `exists_applyPath` with the word made explicit, which is what lets us
  name the matrix.
* `matMul`, `pathMat_append`, `pathMat_replicate_true/false` — words concatenate,
  matrices multiply, and a run of length `a` is one of the two elementary
  matrices to the `a`.
* `toReal₀_eq_mobius_prefixWord` — `Φ₀ x = (A s + B)/(C s + D)` for
  `s = Φ₀ (σⁿ x)` and `(A,B,C,D) = pathMat (prefixWord x n)`. The only analytic
  input in the file; everything else is algebra and bookkeeping.

Irrationality, which is the standing hypothesis:

* `toReal₀_univ : Φ₀ univ = 0` — names the junk value at `∞` (the cut is
  unbounded and `Real.sSup` returns `0`). Was missing and is needed to rule out
  `x = univ` from irrationality.
* `iterate_shift_ne_univ_of_irrational` — no shift of an irrational path is `∞`.
* `irrational_toReal₀_iterate_shift` — irrationality passes to every tail.
* `toReal₀_pos_of_irrational` — hence every tail value is `> 0`, which is what
  makes the second estimate strict rather than `≤`.

(a) Run-boundary extraction:

* `InfFlips x` — the path flips infinitely often.
* `infFlips_of_irrational` — **the "infinite exactly when irrational" half**,
  via `eventuallyConstant_iff_rat`. The converse direction is not stated because
  it is not needed; a rational path stops flipping, and `EventuallyConstant` is
  already the right statement of that.
* `nextFlip`, `runBoundary`, `partialQuot`, `runBit`, with
  `bitAt_eq_of_lt_nextFlip` (the run is constant — minimality of `sInf`),
  `runBit_succ` (runs alternate), `partialQuot_pos`.
* `prefixWord_runBoundary_succ` — the prefix at boundary `k+1` is the prefix at
  boundary `k` followed by `List.replicate (partialQuot x k) (runBit x k)`.

(b) The recurrence:

* `contin x k = (pₖ, qₖ)` with `contin_num_add_two` / `contin_den_add_two` the
  recurrences `pₖ₊₂ = aₖ pₖ₊₁ + pₖ`, `qₖ₊₂ = aₖ qₖ₊₁ + qₖ`.
* `boundaryMat_eq_contin` — **the load-bearing theorem**: at run boundary `k+1`
  the two columns of `pathMat` of the prefix are `contin x (k+1)` and
  `contin x (k+2)`, in an order that alternates with `runBit x k`. This is where
  the recurrence comes from `pathMat`, as the queue asked.

(c) The estimates:

* `contin_den_pos` — `qₖ > 0` for `k ≥ 2`.
* `contin_den_le_succ` — **`qₖ ≤ qₖ₊₁` for `k ≥ 1`**.
* `abs_sub_columns_lt` — both columns of *any* prefix matrix approximate `Φ₀ x`
  to within `1/(C D)`, strictly.
* `abs_sub_contin_lt` — **`|Φ₀ x − pₖ/qₖ| < 1/(qₖ qₖ₊₁)`** for `k ≥ 2`.
* `abs_sub_contin_lt_one_div_sq` — the `1/q²` form.

Example (in `Examples.lean`), pinning the definitions to intent:

* `partialQuot_goldenPath : partialQuot {n | Even n} k = 1` — every partial
  quotient of `φ` is `1`.
* `contin_goldenPath : contin {n | Even n} (k+1) = (fib (k+1), fib k)` — the
  continuants are consecutive Fibonacci numbers. `contin` is built from run
  boundaries of a bit set and `Nat.fib` is defined in Mathlib with no reference
  to any of it, so this is a real check that the run decomposition computes the
  classical continued fraction. With `toReal₀_goldenPath` it says the
  convergents of `φ` are `1/1, 2/1, 3/2, 5/3, …`.

### Remaining `sorry`s

None.

### The GenContFract question — decided: REBUILD, do not bridge

Measured rather than guessed.

* **Rebuild, actual cost:** the estimates section is 92 lines end to end
  (`column_errors` 12, `abs_sub_columns_lt` 30, the two convergent corollaries
  ~30, prose the rest). The whole file is 585 lines including the run
  decomposition, which the bridge would *also* need.
* **Bridge, cost:** Mathlib's `abs_sub_convs_le` is stated for
  `GenContFract.of v`, which is built from `IntFractPair.stream` — i.e. from
  `⌊v⌋` and `Int.fract`. Using it requires proving
  `partialQuot x k = (GenContFract.of (Φ₀ x)).partDens k` modulo the index
  shift, which means redoing the `toReal₀_S`/`toReal₀_L` analysis in the floor
  language, and then translating `continuantsAux` (different indexing, stated
  over a general `LinearOrderedField`, side conditions in terms of
  `TerminatedAt`) into this one. `Computation/Approximations.lean` alone is 491
  lines and `CorrectnessTerminating.lean` another 242; the bridge is the size of
  the thing it would save.
* Mathlib's estimate is also **non-strict** (`≤ 1/(bₙ bₙ₊₁)`) where the one
  proved here is strict, and strictness is what Hurwitz's three-convergent
  argument consumes.

The deciding fact is that the expensive half of this file is the run
decomposition, and bridging does not avoid it: `GenContFract.of` knows nothing
about bit paths, so the run lengths have to be identified with its partial
quotients either way. Rebuilding keeps the development self-contained and
drags no continued-fraction API into the import closure.

### Indexing — read before using this file

`contin x 0` and `contin x 1` are the seeds `(0,1)` and `(1,0)`, **swapped when
the path starts with a left move**. That swap *is* the classical `a₀ = 0`: for
`x < 1` the tree stores no leading `R`-run, so the whole sequence shifts by one.
With it, one recurrence serves both `x ≥ 1` and `x < 1`. The cost is that
`contin x k` is a genuine convergent only for `k ≥ 2`, and `q₁ = 0`. Every
estimate is therefore stated at `k + 2`. Do not "fix" this by special-casing
`x < 1`; the swap is the fix.

### Follow-up added while doing item 2

`column_errors` is now public, and the exact-error layer predicted here was
built on top of it in the same file:

* `tailValue`, `shift_runBoundary_succ`, `tailValue_succ_true/false` — the value
  seen from run boundary `j`, and what one run does to it.
* `tailQuot x j` = `wⱼ` = `[0; aⱼ, aⱼ₊₁, …]`, normalised so that a right run and
  a left run give the *same* recurrence: `inv_tailQuot` proves
  `1/wⱼ = aⱼ + wⱼ₊₁`. `tailQuot_pos`, `tailQuot_lt_one` bracket it in `(0,1)`.
* `denRatio x j` = `ρⱼ = qⱼ₊₁/qⱼ`, with `denRatio_succ : ρⱼ₊₁ = aⱼ + 1/ρⱼ` and
  `one_le_denRatio`.
* `abs_sub_contin_eq` — **the sharp error**
  `|Φ₀ x − pⱼ/qⱼ| = 1/(qⱼ (qⱼ wⱼ + qⱼ₊₁))`.

Item 4 should use these rather than rebuilding them.

### What the next person should do first

Nothing is blocked.


## Item 2 — COMPLETED

New file `SternBrocot/Hurwitz.lean` (no `sorry`), plus the exact-error layer
added to `Convergent.lean` and listed under item 1 above. Wired into
`SternBrocot.lean`.

### What was proved

The reduction to a statement about two positive reals:

* `hurwitzSum x j` = `λⱼ = wⱼ + ρⱼ`.
* `hurwitzSum_succ` — **the one relation the theorem needs**:
  `λⱼ₊₁ = 1/wⱼ + 1/ρⱼ`. It holds because `inv_tailQuot` and `denRatio_succ`
  carry the *same* partial quotient `aⱼ`, which therefore cancels.
* `hurwitzSum_le_iff` — the `j`-th convergent misses `1/(√5 q²)` exactly when
  `λⱼ ≤ √5`. This is `abs_sub_contin_eq` divided by `qⱼ²`.

The core:

* `not_three_consecutive_fail` — three consecutive misses are impossible. With
  `X = 1/wⱼ`, `Y = 1/ρⱼ`, misses at `j` and `j+1` give `X + Y ≤ √5` and
  `1/X + 1/Y ≤ √5`; the miss at `j+2` feeds `sq_sub_le_one` at index `j+1` and,
  after unwinding both recurrences, yields `X − Y ≥ 2aⱼ − 1 ≥ 1`. Those three
  inequalities force `X + Y = √5` and `X Y = 1` exactly (`eq_of_sub_one_le`),
  hence `ρⱼ = φ` — impossible, since `ρⱼ` is a ratio of integers.
* `le_contin_den` — `qⱼ₊₃ ≥ j + 1`, so the denominators are unbounded.
* `exists_hurwitz_approx` — **Hurwitz**, on the carrier.
* `exists_hurwitz_approx_real` — **Hurwitz on `ℝ`**, for every irrational real,
  positive or negative, via `exists_toReal₀_eq` and negation-is-complement.

Optimality:

* `norm_form_ne_zero` — `p² − pq − q² ≠ 0` for `q ≠ 0`; a zero would make `√5`
  a ratio of integers.
* `sqrt5_optimal` — for `c > √5` the rationals with
  `|φ − p/q| < 1/(c q²)` all have `q ≤ ⌈1/(c(c−√5))⌉`. So `√5` cannot be
  increased.

### Remaining `sorry`s

None.

### A simplification worth recording

The textbook proof deduces `aⱼ = 1` from two consecutive misses and only then
finishes. That step is unnecessary here. Unwinding
`ρⱼ₊₁ − wⱼ₊₁ = 2aⱼ + 1/ρⱼ − 1/wⱼ ≤ 1` gives `1/wⱼ − 1/ρⱼ ≥ 2aⱼ − 1`, and since
`aⱼ ≥ 1` the bound `≥ 1` follows immediately — no case analysis on the partial
quotient at all. `not_three_consecutive_fail` is correspondingly short.

### Statement shape

`exists_hurwitz_approx` is stated as "for every `M` there is a solution with
`q > M`" rather than with `Set.Infinite`. That is the same content and avoids
having to prove that the convergents are in lowest terms in order to talk about
`Rat.den`. If a `Set.Infinite` form is ever wanted, the missing ingredient is
`IsCoprime pⱼ qⱼ`, which is `pathMat_det` at a run boundary plus
`boundaryMat_eq_contin` — a short derivation, not a new idea.

### What the next person should do first

Nothing here is blocked. `Examples.lean` could cheaply close one more loop:
`partialQuot_goldenPath` and `contin_goldenPath` are already there, so
`toReal₀_goldenPath ▸ sqrt5_optimal` states the extremality of `φ` directly in
terms of the golden *path*. It is a two-line corollary and was left out only for
time.


## Item 3 — COMPLETED

New file `SternBrocot/Intrinsic.lean`, **no `sorry`**. Nothing in the repository
has a `sorry`. The skeleton was committed first with ten, as the queue
specified, and all ten were then discharged.

### The design

Three intrinsic layers. (1) `slexSup` — a supremum on `P(ω+1)`.
`Completeness.lean` already has `lexSup` on `P(ω)`, and `SLexLt` is "negatives
below positives, same sign by forward lex on the stored bits", so one case split
suffices: a set with a positive member has a positive supremum whose bits are
`lexSup` of the positive members' bits, and a set of negatives has a negative one
whose bits are `lexSup` of all of them. No boundedness hypothesis, exactly as for
`lexSup`. (2) `ratPoint : ℚ → Signed` — `GosperRat.toPath` is the Euclidean
algorithm as a function, `Bridge.toSet` makes it a point, `neg` extends it across
the sign. (3) The operations as suprema over the nodes:
`a + b = sup { ratPoint (p+q) | ratPoint p <ₛ a, ratPoint q <ₛ b }` with `p q : ℚ`
and the inner `+` **rational** addition, so there is no circularity; `×` is the
same formula on the nonnegative cone, extended by `neg`, because the supremum
formula is monotone only there.

### What was proved

* `slexSup_upperBound`, `slexSup_least` — the supremum layer. Each is the sign
  case split followed by `lexSup_upperBound` / `lexSup_least`. In the
  all-negative case a *positive* upper bound dominates the supremum for free,
  which is the only place the sign split does any work.
* `isFinite_ratPoint`, `toReal_ratPoint` — the rational embedding.
* `eq_top_or_bot_of_not_isFinite`, `slexLt_top`, `bot_slexLt` — the two points
  `IsFinite` excludes and that everything finite lies strictly between them.
* `exists_lt_ratPoint`, `exists_ratPoint_lt` — density of the rational points.
* `slexLt_of_toReal_lt`, `toReal_le_of_not_slexLt` — the converses of
  `toReal_mono`, by trichotomy. `SignedToReal` only gives non-strict
  monotonicity (the quotient is why), but reflecting a *strict* inequality needs
  nothing more.
* `isFinite_addRaw`, `isFinite_mulRawPos`, `isFinite_mulRaw` — finiteness.
* **`toReal_addRaw`, `toReal_mulRawPos`, `toReal_mulRaw`** — the agreement
  theorems, and the whole mathematical content of the file.
* `addRaw_congr`, `mulRaw_congr`, `toRealQ_add'`, `toRealQ_mul'`, all ten field
  axioms, and `add'_eq_add` / `mul'_eq_mul`.
* `toRealQ_zero`, `toRealQ_one`, `toRealQ_neg`, `toRealQ_inv` — the missing
  companions to `Field.lean`'s transport lemmas, derived by cancellation.

### Two things I got wrong, and the fixes

**A design bug in `mulCut`.** As first written it was
`{z | ∃ p q, 0 ≤ p ∧ 0 ≤ q ∧ ratPoint p <ₛ a ∧ ratPoint q <ₛ b ∧ z = ratPoint (p*q)}`,
and that is **wrong at zero**: when either argument is `+0` the cut is empty, and
`slexSup ∅` is not `+0` — with no positive member it takes the negative branch and
returns `negLift (lexSup ∅) = {none}`, which is `−∞`. So `mulRawPos` was infinite
exactly where the product is zero. Fixed with the standard Dedekind floor:
`ratPoint 0` is now unconditionally a member. `addCut` needed no such fix.

The underlying trap, now in CLAUDE.md: `{none}` and `univ` are both negative
points and mean opposite things. `univ` is `−0` (all finite bits set, magnitude
`∅`); `{none}` is `−∞` (no finite bits, magnitude `univ`). The empty supremum
lands on the second.

**A wrong plan for the congruence lemmas.** An earlier handoff said they would
follow because the cut of rational points below `a` is unchanged when `a` moves
to its tail partner. That is false: if the lower element of the adjacent pair is
itself a rational point, the two cuts differ by exactly that point. The fix was
not a density argument but a restructuring — prove the agreement theorem at the
**raw** level first, and the congruence is then `toReal_injective`. That also
made `toRealQ_add'`/`toRealQ_mul'` immediate, collapsing four sorries into two.

### What the next person should do first

Install `add'`/`mul'` as the `Field` instance in `Field.lean`, replacing
`equivReal.field`. `add'_eq_add` and `mul'_eq_mul` guarantee no theorem changes;
it is a mechanical edit, deliberately left undone so that this commit adds
nothing and breaks nothing.

Then, if the strong form is wanted: reprove the ten field axioms without
`toRealQ`, by density of the nodes. The statements are already `ℝ`-free, so only
the proof bodies change.

## Item 4 — PARTIAL

New file `SternBrocot/Reduction.lean`. **One named `sorry`**,
`degLeTwo_eventuallyPeriodic` — the theorem itself. Everything it consumes is
proved.

### What was proved

* `formAt`, `formMid` — the binary quadratic form and the middle coefficient of
  its transform, as the usual `SL₂(ℤ)` action.
* `formAt_transform` — if `t` is a root of `A X² + B X + C` and
  `t = (a s + b)/(c s + d)`, then `s` is a root of the transformed form.
* `formDisc_transform` — **the discriminant is invariant**,
  `formMid² − 4 formAt(a,c) formAt(b,d) = (B² − 4AC)(ad − bc)²`. Unimodularity
  is what makes the second factor `1`.
* **`abs_formAt_le`** — the estimate, and the point of the file. A column with
  `|a/c − t| ≤ 1/c²` has `|formAt A B C a c| ≤ |A|(2|t| + 1) + |B|`, a bound
  depending on the original quadratic and `t` only. The proof is the
  factorisation `formAt (a,c) = c² (a/c − t) (A(a/c + t) + B)`: the `c²` cancels
  against the approximation quality and nothing column-dependent survives.
* `contin_est`, `abs_formAt_contin_le` — the estimate applied at the convergents.
* `formAt_boundaryMat_root` — the form carried to run boundary `j` has
  `tailValue x j` as a root. This is the concrete shape the pigeonhole meets.

### The trap, resolved

`CLAUDE.md` records that the naive bound fails because `c/d` is unbounded along
a bit path — `Lⁿ` has `c/d = n`. That is exactly right, and the resolution is
that the estimate is only ever applied at **run boundaries**, where both columns
are convergents and `qₖ ≤ qₖ₊₁` gives `|t − pₖ/qₖ| < 1/qₖ²`
(`abs_sub_contin_lt_one_div_sq`). So the trap costs nothing here: the file is
indexed by `runBoundary` from the start, and `boundaryMat_eq_contin` connects
the matrix columns to the convergents. Nothing in this file is stated for an
arbitrary prefix.

### The remaining `sorry`

`degLeTwo_eventuallyPeriodic {x} (hirr : Irrational (Φ₀ x)) (h : DegLeTwo (Φ₀ x))
 : EventuallyPeriodic x`. Three steps remain, in order of cost:

1. **Bounded ⟹ finitely many forms.** `abs_formAt_contin_le` bounds the two outer
   coefficients uniformly in `k`; `formDisc_transform` then bounds the middle
   one, since `formMid² = D + 4 formAt formAt` with `D = B² − 4AC` fixed. So the
   triple lands in a finite subset of `ℤ³`. In Lean this wants an explicit
   `Finset` (a box of integers) plus `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`,
   or the range-finiteness route via `Set.Finite`.
2. **Pigeonhole to a repeated complete quotient.** Each triple has at most two
   real roots and the `tailValue`s are all roots of their triple's form, so the
   set `{tailValue x k | k}` is finite; `Set.Infinite.exists_ne_map_eq_of_mapsTo`
   then gives `k ≠ l` with `tailValue x k = tailValue x l`. Note the form is
   genuinely quadratic at every `k`: `formAt = 0` would make `tailValue x k`
   rational, and it is not.
3. **Repeated quotient ⟹ periodic.** This is the cheap step in this encoding,
   and worth doing first to check the shape. Equal values of `Φ₀` give
   `TailEqv` by `toReal₀_injective`; a tail pair has a *rational* common value
   (one side is a node), and `irrational_toReal₀_iterate_shift` rules that out —
   so the two shifted points are literally **equal**, which is
   `EventuallyPeriodic` on the nose.

Step 3 is a few lines and would de-risk the rest. Do it first.


