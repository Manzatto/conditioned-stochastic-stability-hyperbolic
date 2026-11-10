#!/usr/bin/env bash
# Build the library, re-check every module with warnings as errors, then run the axiom audit.
# VERIFY_JOBS sets the number of parallel checks (default 8).
set -euo pipefail

root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd -- "$root"
jobs=${VERIFY_JOBS:-8}

if [[ ${1-} == --palomar ]]; then
  shift
  no_sandbox=false
  if (( $# > 0 )); then
    if (( $# != 1 )) || [[ $1 != --inadvisably-no-sandbox ]]; then
      printf 'Usage: bash scripts/verify.sh --palomar [--inadvisably-no-sandbox]\n' >&2
      exit 2
    fi
    no_sandbox=true
  fi
  lake build --wfail Solution
  lake build Challenge GlobalChallenge CompactChallenge FiltrationChallenge
  lean_prefix=$(lean --print-prefix)
  for kernel in nanoda_bin con-ron; do
    if [[ ! -x "$lean_prefix/bin/$kernel" ]]; then
      printf 'Required bundled kernel is missing: %s\n' "$kernel" >&2
      exit 2
    fi
  done
  config_dir=$(mktemp -d "${TMPDIR:-/tmp}/palomar-configs.XXXXXX")
  trap 'rm -rf -- "$config_dir"' EXIT
  for config in comparator.json comparator-global.json comparator-compact.json comparator-filtration.json; do
    python3 - "$config" "$config_dir/$config" "$lean_prefix" <<'PYCONFIG'
import json
import pathlib
import sys

source, destination, prefix = sys.argv[1:]
config = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
if "external_kernels" in config:
    raise SystemExit("external_kernels is not a submitter field")
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PYCONFIG
    comparator_args=(--config "$config_dir/$config")
    if [[ $no_sandbox == true ]]; then
      comparator_args+=(--inadvisably-no-sandbox)
    fi
    printf 'Checking %s\n' "$config"
    lake comparator "${comparator_args[@]}"
  done
  printf 'All four Palomar comparisons and independent kernel checks passed.\n'
  exit 0
fi

if [[ ${1-} != --inside-lake-environment ]]; then
  lake build --wfail LeanShared AbsorbingMarkovChains ConditionedStochasticStabilityHyperbolic Solution
  exec lake env bash "$root/scripts/verify.sh" --inside-lake-environment
fi

find LeanShared AbsorbingMarkovChains ConditionedStochasticStabilityHyperbolic -name '*.lean' -print0 |
  xargs -0 -n 1 -P "$jobs" lean -DautoImplicit=false -DwarningAsError=true

lean -DautoImplicit=false -DwarningAsError=true Solution.lean
lean -DautoImplicit=false -DwarningAsError=true Audit.lean
printf 'All modules checked and the axiom audit passed.\n'
