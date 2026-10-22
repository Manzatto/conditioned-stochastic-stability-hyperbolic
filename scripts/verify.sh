#!/usr/bin/env bash
# Build the library, re-check every module with warnings as errors, then run the axiom audit.
# VERIFY_JOBS sets the number of parallel checks (default 8).
set -euo pipefail

root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd -- "$root"
jobs=${VERIFY_JOBS:-8}

if [[ ${1-} != --inside-lake-environment ]]; then
  lake build
  exec lake env bash "$root/scripts/verify.sh" --inside-lake-environment
fi

find LeanShared AbsorbingMarkovChains ConditionedStochasticStabilityHyperbolic -name '*.lean' -print0 |
  xargs -0 -n 1 -P "$jobs" lean -DautoImplicit=false -DwarningAsError=true

lean -DautoImplicit=false -DwarningAsError=true Audit.lean
printf 'All modules checked and the axiom audit passed.\n'
