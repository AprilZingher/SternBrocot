/-
Independence and deadness claims, checked.

Every adversarial review of this repository so far has found the Lean sound and
the prose wrong, and the false claims cluster hard: "the order is intrinsic",
"`contin_den_lt_succ` is not used by `legendre`", "both directions run on one
identity", "seventeen modules are ℝ-free". Almost all are of the form

    X does not depend on Y     /     nothing uses X

which is exactly the shape a grep cannot check and a human does not check.
`scripts/check-core-closed.sh` already turned one such claim into a structural
invariant. This does the same for the rest.

Add a claim here whenever a docstring, README, CLAUDE.md or PR body asserts that
something is *not* used. If the claim is false the check fails.

## Three ways this check can lie, and what stops each

1. **The collector silently returns nothing.** `ConstantInfo.value?` returns
   `none` for **every** theorem — not just imported ones, which is what an
   earlier version of this comment claimed; the default `allowOpaque := false`
   makes it `none` for `.thmInfo` regardless of provenance. A collector built on
   it reports empty dependency sets and passes everything. Guarded by the
   *positive controls* below: dependencies that must be found.
2. **A claim names a constant that does not exist.** A typo or a rename makes
   `env.find?` return `none`, the closure comes back empty, and the claim passes
   silently *forever*. This is not hypothetical — this repo has already renamed
   `contin_best_approx → contin_best_approx_gen` and `contin_coprime →
   contin_coprime_gen`. An adversarial review caught the first version of this
   file passing two deliberately-misspelled claims about a real dependency while
   printing "canary passed". Guarded by resolving every name up front.
3. **The closure is incomplete.** Hand-rolled traversals drop `inductInfo →
   ctors`, `recInfo → all` and `opaqueInfo → value`. Do not hand-roll it; use
   `ConstantInfo.getUsedConstantsAsSet`, which Lean core already ships.

## And one way it cannot check anything at all

An anonymous `example` has no `Name`, so `projectDecls` cannot see it and no
claim can be written about it. A coverage claim attached to an `example` is
therefore outside this file's reach *by construction* — which is how a false one
shipped in PR #6: the prose said a set of computed values was what put a lemma's
seed branch under test, and the `example` making that claim used none of them.
Name anything a docstring or PR body makes a dependency claim about.
-/
import SternBrocot

open Lean

/-- Transitive closure of the constants a declaration uses. -/
partial def transDeps (env : Environment) (start : Name) : NameSet :=
  let rec go (worklist : List Name) (seen : NameSet) : NameSet :=
    match worklist with
    | [] => seen
    | n :: rest =>
      if seen.contains n then go rest seen
      else
        let next := match env.find? n with
          | none => []
          | some info => info.getUsedConstantsAsSet.toList
        go (next ++ rest) (seen.insert n)
  go [start] {}

/-- `source` must not use `target`, anywhere in its transitive closure. -/
structure Claim where
  source : Name
  target : Name
  why : String

/-- Claims asserted in prose somewhere in the repository. -/
def claims : List Claim := [
  { source := `SternBrocot.badlyApproximable_iff_boundedPartialQuot
    target := `SternBrocot.legendre
    why := "CF/BadlyApproximable.lean: 'uses neither Legendre nor the exact error formula'" },
  { source := `SternBrocot.badlyApproximable_iff_boundedPartialQuot
    target := `SternBrocot.abs_sub_contin_eq
    why := "CF/BadlyApproximable.lean: 'uses neither Legendre nor the exact error formula'" },
  { source := `SternBrocot.badlyApproximable_iff_boundedPartialQuot
    target := `SternBrocot.tailQuot
    why := "CF/BadlyApproximable.lean: the tailQuot layer is not used" },
  { source := `SternBrocot.not_badlyApproximable_of_unbounded
    target := `SternBrocot.contin_err_sum
    why := "CF/BadlyApproximable.lean: the -> direction runs on abs_sub_contin_lt, not the identity" },
  { source := `SternBrocot.eventuallyPeriodic_iff_degLeTwo
    target := `SternBrocot.orderIsoReal
    why := "CLAUDE.md: 'nothing in the Lagrange import chain reaches Real/Field.lean'" },
  -- The two cross-check pairs in `Examples.lean`. Each pair states one fact
  -- twice: once from a general lemma, once from the computed convergents. The
  -- claim that makes it a cross-check rather than a restatement is that the
  -- primed proof does *not* go through the general lemma — otherwise both
  -- halves would fail or succeed together and nothing is being compared. The
  -- matching canaries below assert the unprimed halves DO use it.
  { source := `SternBrocot.contin_den_startIdx_slowPath'
    target := `SternBrocot.contin_den_startIdx
    why := "Examples.lean: 'mentioning neither contin_den_startIdx nor its proof'" },
  { source := `SternBrocot.abs_contin_det_slowPath'
    target := `SternBrocot.abs_contin_det
    why := "Examples.lean: 'the same statement from the computed values instead'" }
]

/-- **Positive controls.** Dependencies that must be found. If one of these is
reported absent the collector is broken and every claim above is vacuous.

The second is the claim I got wrong in an earlier PR — asserting that `legendre`
does not use `contin_den_lt_succ`, when in fact it does, four hops away through
`exists_bracket → exists_contin_den_gt → contin_den_ge`. Keeping it as a control
means the day someone reroutes `exists_contin_den_gt` and makes the
independence *real*, this fails and asks to be reclassified rather than
silently becoming a true claim nobody noticed. -/
def canaries : List Claim := [
  { source := `SternBrocot.badlyApproximable_of_bounded
    target := `SternBrocot.contin_err_ge
    why := "control: the <- direction really does run on the identity" },
  { source := `SternBrocot.legendre
    target := `SternBrocot.contin_den_lt_succ
    why := "control: legendre DOES use contin_den_lt_succ, via exists_bracket" },
  { source := `SternBrocot.contin_den_startIdx_slowPath
    target := `SternBrocot.contin_den_startIdx
    why := "control: the unprimed half of the startIdx cross-check is the general lemma" },
  { source := `SternBrocot.abs_contin_det_slowPath
    target := `SternBrocot.abs_contin_det
    why := "control: the unprimed half of the determinant cross-check is the general lemma" }
]

/-- Declarations claimed to be unreferenced. `HANDOFF.md` says these three are
dead, superseded by their `_gen` versions. -/
def deadDecls : List (Name × String) := [
  (`SternBrocot.contin_best_approx, "HANDOFF.md: superseded by contin_best_approx_gen"),
  (`SternBrocot.contin_coprime, "HANDOFF.md: superseded by contin_coprime_gen"),
  (`SternBrocot.contin_ne_toReal₀, "HANDOFF.md: unused; docstring has twice claimed a consumer")
]

/-- Every `SternBrocot.*` declaration in the environment. -/
def projectDecls (env : Environment) : Array Name :=
  env.constants.fold (init := #[]) fun acc n _ =>
    if (`SternBrocot).isPrefixOf n then acc.push n else acc

def main : IO UInt32 := do
  let env ← importModules #[{ module := `SternBrocot }] {}
  let mut bad := 0
  -- (2) every name must resolve, or its claim is vacuous
  let allNames := (claims ++ canaries).flatMap (fun c => [c.source, c.target])
                    ++ deadDecls.map Prod.fst
  for n in allNames do
    if (env.find? n).isNone then
      IO.println s!"FAIL: unknown constant `{n}`."
      IO.println "  A claim naming a constant that does not exist passes vacuously."
      bad := bad + 1
  if bad > 0 then return 1
  -- (1) positive controls
  for c in canaries do
    if !(transDeps env c.source).contains c.target then
      IO.println s!"FAIL (control): {c.source} should depend on {c.target}, and does not."
      IO.println s!"  {c.why}"
      IO.println "  The collector is broken; every independence claim below is vacuous."
      bad := bad + 1
  if bad > 0 then return 1
  -- the independence claims themselves, one closure per distinct source
  let mut cache : Std.HashMap Name NameSet := {}
  for c in claims do
    let deps ← match cache[c.source]? with
      | some d => pure d
      | none => let d := transDeps env c.source; cache := cache.insert c.source d; pure d
    if deps.contains c.target then
      IO.println s!"FAIL: {c.source} DOES transitively depend on {c.target}."
      IO.println s!"  claimed otherwise by: {c.why}"
      bad := bad + 1
  -- deadness: nothing in the project may reference these
  let decls := projectDecls env
  for (dead, why) in deadDecls do
    let mut users : Array Name := #[]
    for d in decls do
      if d == dead || dead.isPrefixOf d then continue
      match env.find? d with
      | none => pure ()
      | some info => if info.getUsedConstantsAsSet.contains dead then users := users.push d
    if users.size > 0 then
      IO.println s!"FAIL: {dead} is referenced by {users.size} declaration(s), e.g. {users[0]!}."
      IO.println s!"  claimed dead by: {why}"
      bad := bad + 1
  if bad == 0 then
    IO.println s!"OK: {claims.length} independence claims, {deadDecls.length} deadness claims, \
{canaries.length} positive controls."
    return 0
  else
    return 1
