#!/usr/bin/env bash
# The core of the construction must not depend on `ℝ`.
#
# This used to be checked by probing each module with a `#check`, which needs a
# built Mathlib and was got wrong twice: once in the module count, and once by
# probing for `Real.pi`, which lives in the trigonometry files and so fails to
# resolve *everywhere* — reporting even `Real/ToReal.lean` as ℝ-free.
#
# Since `SternBrocot/Core/` is closed under imports and no file in it imports
# `Mathlib.Data.Real.Basic` or anything above it, ℝ-freeness follows from a
# property of the import graph that costs no build to check. Keep it that way:
# if `Core/` ever needs something from `Real/`, the dependency is backwards and
# the fix is to move the definition down, not to relax this test.
set -euo pipefail

cd "$(dirname "$0")/.."

fail=0

offenders=$(grep -rn '^import SternBrocot' SternBrocot/Core/ \
  | grep -v 'import SternBrocot\.Core\.' || true)
if [ -n "$offenders" ]; then
  echo "FAIL: SternBrocot/Core/ imports outside Core/:"
  echo "$offenders"
  fail=1
fi

realish=$(grep -rn '^import Mathlib\..*Real' SternBrocot/Core/ || true)
if [ -n "$realish" ]; then
  echo "FAIL: SternBrocot/Core/ imports ℝ from Mathlib directly:"
  echo "$realish"
  fail=1
fi

# Layering: Real/ is the bridge, CF/ is the library built on top of it.
backwards=$(grep -rn '^import SternBrocot\.CF' SternBrocot/Real/ || true)
if [ -n "$backwards" ]; then
  echo "FAIL: SternBrocot/Real/ imports SternBrocot/CF/ — layering is backwards:"
  echo "$backwards"
  fail=1
fi

if [ "$fail" -eq 0 ]; then
  n=$(find SternBrocot/Core -name '*.lean' | wc -l | tr -d ' ')
  echo "OK: Core/ is closed under imports and ℝ-free ($n modules)."
fi

exit "$fail"
