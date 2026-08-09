#!/usr/bin/env bash
# Checks the independence claims in scripts/CheckDeps.lean.
# Needs a built SternBrocot; run after `lake build`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean --run scripts/CheckDeps.lean
