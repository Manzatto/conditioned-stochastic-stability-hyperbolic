# Local Lean verification — 22 October 2026

This report supports the **Lean / local verification** GitHub commit status.
The verification ran locally on macOS (Apple Silicon), using Lean 4.35.0.
It records local verification, rather than a successful GitHub-hosted Actions run.

## Results

- **Fresh library build:** passed for `LeanShared`, `AbsorbingMarkovChains`, and
  `ConditionedStochasticStabilityHyperbolic`, with warnings treated as errors.
  All 7,021 build jobs were satisfied using the existing local build artifacts;
  the cached build took 48.87 seconds.
- **Fresh axiom audit:** passed for 26,392 declarations, including 19,683 theorems.
  Only `propext`, `Classical.choice`, and `Quot.sound` were permitted. The audit
  command took 136.15 seconds.
- **Full strict source check:** the earlier successful check of all 2,983 library
  modules was reused after verifying that every Lean source file and all the
  configuration inputs listed below were byte-for-byte unchanged. That pass used
  `autoImplicit=false` and `warningAsError=true`; it was not repeated for this
  workflow-only update.
- **Workflow validation:** `actionlint` passed after adding the Markdown filters.

The fresh local commands completed at **20:24 BST on 22 October 2026**:

```bash
lake build --wfail LeanShared AbsorbingMarkovChains ConditionedStochasticStabilityHyperbolic
lake env lean -DautoImplicit=false -DwarningAsError=true Audit.lean
```

## Source identity

All **2,987 Lean source files**, plus `lean-toolchain`, `lakefile.toml`,
`lake-manifest.json`, and `scripts/verify.sh`, matched the earlier verified inputs
in the working folder, the upload checkout, and the local audit checkout.
All nine dependency checkouts matched their pinned revisions and had no tracked
source changes. Mathlib is pinned to
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

The SHA-256 of the sorted 2,991-entry input manifest is:

```text
3f6d89d47dff3e0fe7b305c7ae14f60e61797e4d37c76b60c3013d9a24ddf576
```

Each manifest entry is the file's lowercase SHA-256, two spaces, its relative
POSIX path, and a newline. The manifest digest hashes their UTF-8 concatenation
in path order. Generated `.lake` files are excluded.

The earlier full verification log ended with:

```text
Axiom audit passed: 26392 declarations, including 19683 theorems; only standard classical axioms.
All modules checked and the axiom audit passed.
```

Its SHA-256 is
`f5dcc3be2026bd26600579793bc72a51ce8fc85f1ff94aa7f727b240657b6b38`.

## Markdown-only changes

Every push and pull request gets a lightweight source-fingerprint check, so a
Markdown-only commit receives its own green check. When the Lean verification
inputs match this verified snapshot, or a later successful workflow run, the
expensive build, strict source check, and axiom audit are skipped. Otherwise the
full verification runs. Manual runs always request fresh verification.

The fingerprint covers all tracked `.lean` files and the four configuration and
script files listed above. A Markdown edit therefore preserves the verified
inputs, while a changed, added, or deleted Lean source or dependency pin requires
fresh verification unless that exact source state has already passed. A new
documentation commit does not cancel a verification already in progress.
