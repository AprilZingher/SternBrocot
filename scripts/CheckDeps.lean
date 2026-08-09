/-
Independence claims, checked.

Every adversarial review of this repository so far has found the Lean sound and
the prose wrong, and the false claims cluster hard: "the order is intrinsic",
"`contin_den_lt_succ` is not used by `legendre`", "both directions run on one
identity", "seventeen modules are ℝ-free". Almost all are of the form

    X does not depend on Y

which is exactly the shape a grep cannot check and a human does not check.
`scripts/check-core-closed.sh` already turned one such claim into a structural
invariant. This does the same for the rest.

Add a claim here whenever a docstring, README, CLAUDE.md or PR body asserts that
something is *not* used. If the claim is false the check fails.

**The trap this file exists to avoid**: `ConstantInfo.value?` returns `none` for
*imported* theorems, so the naive collector silently reports an empty dependency
set and every claim passes. Theorems must be read out of `.thmInfo` directly.
-/
import SternBrocot

open Lean

/-- Constants appearing in a declaration's type and value. `thmInfo` is handled
separately because `value?` is `none` for imported theorems. -/
def directDeps (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some info =>
    let fromType := info.type.getUsedConstants
    let fromValue :=
      match info with
      | .thmInfo ti => ti.value.getUsedConstants
      | _ => match info.value? with
             | some e => e.getUsedConstants
             | none => #[]
    fromType ++ fromValue

/-- Transitive closure, breadth-first with an explicit visited set. -/
partial def transDeps (env : Environment) (start : Name) : NameSet :=
  let rec go (worklist : List Name) (seen : NameSet) : NameSet :=
    match worklist with
    | [] => seen
    | n :: rest =>
      if seen.contains n then go rest seen
      else go ((directDeps env n).toList ++ rest) (seen.insert n)
  go [start] {}

/-- `target` must not appear anywhere in `source`'s transitive dependencies. -/
structure Claim where
  source : Name
  target : Name
  why : String

/-- Claims asserted in prose somewhere in the repository. -/
def claims : List Claim := [
  -- CF/BadlyApproximable.lean docstring, README, CLAUDE.md, PR #4
  { source := `SternBrocot.badlyApproximable_iff_boundedPartialQuot
    target := `SternBrocot.legendre
    why := "BadlyApproximable.lean: 'uses neither Legendre nor the exact error formula'" },
  { source := `SternBrocot.badlyApproximable_iff_boundedPartialQuot
    target := `SternBrocot.abs_sub_contin_eq
    why := "BadlyApproximable.lean: 'uses neither Legendre nor the exact error formula'" },
  { source := `SternBrocot.badlyApproximable_iff_boundedPartialQuot
    target := `SternBrocot.tailQuot
    why := "BadlyApproximable.lean: the tailQuot layer is not used" },
  -- CF/BadlyApproximable.lean: the -> direction does NOT use the new identity.
  -- This is the claim I got backwards in PR #4 and had to withdraw.
  { source := `SternBrocot.not_badlyApproximable_of_unbounded
    target := `SternBrocot.contin_err_sum
    why := "BadlyApproximable.lean: the -> direction runs on abs_sub_contin_lt, not the identity" }
]

/-- Sanity: a dependency that MUST be present. If this reports absent, the
collector is broken and every claim above is passing vacuously. -/
def canary : Claim :=
  { source := `SternBrocot.badlyApproximable_of_bounded
    target := `SternBrocot.contin_err_ge
    why := "canary — this dependency is real, so it must be found" }

def main : IO UInt32 := do
  let env ← importModules #[{ module := `SternBrocot }] {}
  let mut bad := 0
  -- the canary first: a broken collector makes everything else meaningless
  let canaryDeps := transDeps env canary.source
  if !canaryDeps.contains canary.target then
    IO.println s!"FAIL (canary): {canary.source} should depend on {canary.target}."
    IO.println "  The dependency collector is broken; all other results are vacuous."
    bad := bad + 1
  for c in claims do
    let deps := transDeps env c.source
    if deps.contains c.target then
      IO.println s!"FAIL: {c.source} DOES transitively depend on {c.target}."
      IO.println s!"  claimed otherwise by: {c.why}"
      bad := bad + 1
  if bad == 0 then
    IO.println s!"OK: {claims.length} independence claims hold (canary passed)."
    return 0
  else
    return 1
