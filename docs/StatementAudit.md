# Statement audit

This document compares the Lean theorems with the statements of the article. They cover `thm:qem-local`, `thm:local`, `thm:global-existence`, `thm:global` and `thm:global-global`.

`#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound` for each of them.

| Manuscript | Lean theorem |
|---|---|
| `thm:qem-local`, `thm:local` | `Paper.NativeLocalTheorem.stability_and_retention` |
| `thm:global-existence`, `thm:global` | `Paper.NativeMainTheorems.global_existence` |
| `thm:global-global` | `Paper.NativeMainTheorems.global_global` |

`ConditionedStochasticStabilityHyperbolic.MainTheorems` restates them under the numbering of the article:

- `Theorem2_7` (the existence part of `stability_and_retention`);
- `Theorem2_8` (its `Stability` conjunct);
- `Theorem2_10` (the spectral and QEM clauses of `global_existence`);
- `Theorem2_11` (all of `global_existence`);
- `Theorem6_5` (`global_global`).

`Theorem3_15` is the compact embedding; see the README.

## Shared definitions

**Quasi-ergodic measure.** The article definition (eq. `eq:qem-cond`) asks that, for every observable, the conditioned Birkhoff average converges ν-almost surely. `AbsorbingMarkovChains.CanonicalChain.IsQuasiErgodic` requires a probability measure `ν` such that, for every bounded measurable `f`, the averages `∫ n⁻¹ S_n f d(conditioned path law from x, n)` converge to `∫ f dν` for ν-a.e. `x`. The conditioned path law is the law of the weighted killed chain normalized by its survival mass, as in eq. `eq:qem`. The observable class is bounded measurable functions, as recorded in the README.

**Spectral data.** The article's eigen-data `g_ε`, `μ_ε`, `λ_ε` are captured by `LocalConclusions.SpectralWitness C R ν`. It provides:

- a nonnegative eigenfunction `g_ε ∈ C⁰`;
- a finite eigenmeasure `μ_ε`;
- the right eigenrelation `P_ε g_ε = λ_ε g_ε` and the left eigenrelation `P_ε* μ_ε = λ_ε μ_ε`, for `P_ε = R • (transfer operator of C)`;
- the normalization `μ_ε(g_ε) = 1`;
- the product formula `ν = μ_ε(· g_ε)`;
- the radius `spectralRadius (P_ε) = λ_ε` on `C⁰`.

`SimpleSpectralWitness` adds uniqueness of the eigenfunction and of the eigenmeasure up to scaling, as in items (i) and (ii) of `thm:global-existence`.

**Normalizer `R`.** The Lean chain uses the weight `e^φ / R`. Then `R •` its transfer operator is exactly the article's `P_ε` (respectively `P̂_ε`). Quasi-ergodic measures, supports, uniqueness and eigen-data do not depend on `R`; the transports are in `ChainNormalizationTransport`. The local theorem asserts that a suitable `R` exists, and the global theorems hold for every `R` bounding `e^φ`. Since `e^φ` is bounded on the compact `M`, such an `R` always exists. `R` is therefore an encoding device, not a restriction.

**Noise.** `RegularNoise.Maps` and `RegularNoise.Laws` model the random perturbations `T_ω` and their laws (§ `sec:random_perturb`). The process uses the actual shrinking control cube of size `ε`. This modelling is not compared in detail here.

## `thm:qem-local` and `thm:local`

### Hypotheses

**`h : HL T g Λ V`** corresponds to Hypothesis (HL).

| HL item | Lean field |
|---|---|
| (i) `T` is a `C^r` diffeomorphism, `r > 1` | `map_regular`, `inverse_regular`, `regularity_gt_one` |
| (ii) `Λ` is a basic set with isolating neighbourhood `V` | `basic` |
| (iii) `g ∈ C^{r-1}`, supported in `V`, `g > 0` on `Λ` | `weight_regular`, `weight_supported`, `weight_positive` |
| (iv) `T` is mixing on `Λ` | `mixing` |

`weight_nonnegative` is the article's standing convention on the reference weight.

**Weight `e^φ`.**

- The article assumes `e^φ ∈ C^{r-1}(V̄)` with `e^φ = g` on `Λ`.
- Lean takes a function `w` that is `C^{r-1}` (fractional) on `M`, with:
  - `w ≥ 0`,
  - `w = g` on `Λ`,
  - `w = e^φ` on `V̄`.
- *Difference (encoding):* the global extension `w` is how `C^{r-1}(V̄)` is represented. A `C^{r-1}` function on a closed domain is the restriction of a `C^{r-1}` function on `M`. Nonnegativity can be arranged with a smooth cutoff equal to 1 near `V̄`, because `e^φ > 0` there.

**Noise.** `P` and `L` are the perturbed maps and laws.

### Conclusion

The Lean conclusion is `∃ (continuity of e^φ on V̄) R (0 < R) (bound), Stability ∧ GapRetention`, with `K = V̄`.

`Stability` gives `ν₀` and `ν_eq` with:

- `ν₀.map val = ν_eq`;
- `ν_eq` is an equilibrium state for `φ − log|det DT|E^u|` on `Λ`, and it is unique;
- a window `δ > 0` and a family `ν_ε` with `ν_ε → ν₀` weakly as `ε → 0⁺`;
- for every `0 < ε ≤ δ`, `Point`, which consists of:
  - `ν_ε` is quasi-ergodic for the chain on `V̄`;
  - `Λ ⊆ supp ν_ε`;
  - uniqueness among quasi-ergodic measures whose support contains `Λ`;
  - a `SpectralWitness` (the formula `ν_ε = μ_ε(· g_ε)`, both eigenrelations, the normalization, and `λ_ε = r(P_ε | C⁰(V̄))`).

This is exactly `thm:qem-local` (all clauses) together with `thm:local` (weak convergence to the unique equilibrium state).

`GapRetention` is an additional normalized spectral-gap statement. It is stronger than the article and is not needed for the correspondence.

## `thm:global-existence` and `thm:global`

### Hypotheses

**`h : HG1 D g A`** corresponds to Hypothesis (HG1).

| HG1 item | Lean |
|---|---|
| (i) Axiom A | `axiomA` |
| (i) `A` open | `absorbing_open` |
| (i) `T(Ā) ⊂ A` | `strict : MapsTo T (closure A) A` |
| (ii) `C^r` with `r > 1` | `map_regular`, `inverse_regular`, `regularity_gt_one` |
| (ii) `g ∈ C^{r-1}`, `g ≥ 0` | `weight_regular`, `weight_nonnegative` |
| (ii) `g > 0` on basic sets in `M ∖ A` | `weight_positive` |
| (iii) the spectral decomposition `D` has no cycles | `no_cycles` |
| (iv) unique dominant pressure in `M ∖ A`, realized by the unique equilibrium state | `dominant`, `dominant_live`, `pressure_dominant`, `deterministic_equilibrium` |
| (v) mixing on the dominant set | `dominant_mixing` |

**Weight `e^φ`.**

- The article assumes `e^φ ∈ C^{r-1}` on every basic set `Λ_i ⊂ M ∖ A`.
- Lean takes:
  - `localWeightX`: `C^{r-1}` regularity of `e^φ` near each basic set in `Aᶜ`;
  - `coreAgreement`: `e^φ = g` on those basic sets;
  - `hw`: continuity of `e^φ` on `M`.
- *Status:*
  - The agreement `e^φ = g` on these basic sets is the one stated in Hypothesis (HG2).
  - Continuity is the standing assumption on the potential.
  - The local regularity is the reading of the wording "near each retained basic set".

### Conclusion

The Lean conclusion provides the following.

- `initial`, with `initial.map val = ν^g`, the deterministic equilibrium state of the dominant set.
- `ν^g` is an equilibrium state for `φ − log|det DT|E^u|` on the dominant `Λ_i`, and it is unique.
- `ν_ε → initial` weakly.
- For small `ε`, for the chain `CL` on `Aᶜ`:
  - a normalized gap;
  - `ν_ε` is quasi-ergodic;
  - `Λ_i ⊆ supp ν_ε`;
  - uniqueness under the support condition;
  - a `SimpleSpectralWitness` for `CL`.

The witness gives the unique-up-to-scaling `g_ε` and `μ_ε` of items (i) and (ii), with `λ_ε = r(P̂_ε | C⁰(M ∖ A))` and `μ_ε(g_ε) = 1`. The quasi-ergodicity, support and uniqueness clauses give item (iii) of `thm:global-existence`. The weak convergence gives `thm:global`.

## `thm:global-global`

### Hypotheses

**`h : HG2 D0 g A`** extends `HG1` with:

- (ii) pairwise distinct pressures on retained sets: `pressures_distinct`;
- (iii) mixing on every retained set: `retained_mixing`.

The weight hypotheses are the same as above. The article's `e^φ = g ∈ C^{r-1}` on `Λ` corresponds to `coreAgreement` plus `localWeightX`.

`hφ : Measurable φ` is redundant: it follows from `hw`. It is kept because the internal geometry uses it.

**Statement form.** The statement is `type_of%` of `NativeProvedHG2.complete_with_local_strata_native`, instantiated with the toral auxiliary factor and the proved product and first-projection calculi. The filtration is the prescribed greedy filtration `filtration D0 g A h σP strict` built in Lean. It plays the role of "the filtration ordering presented above". Its selected indices `j s` play the role of `i_0 > … > i_{t-1}`. The strata `U s = stratum … (j s)` play the role of `M_{i_s} ∖ M_{i_s − 1}`.

### Clauses (`LiteralHG2Clauses.Clauses`, `LabelledHG2Clauses.Clauses`, local strata clause)

**Item (i).**

- `uniform_prefix` gives one `δ` that works for every point of the prefix level `M_{i_{s−1}−1}` approaching `Λ_j`, for every bounded measurable `φ`: the conditioned Birkhoff limit equals `∫ φ dν_{ε,s}`.
- The approach condition `StableApproach` asks that the forward orbit come arbitrarily close to `Λ_j`. This is implied by `x ∈ W^s(Λ_j)`, so the Lean clause is *stronger*.
- `ν_{ε,s}` is the unique QEM on `Aᶜ` whose support contains `Λ_{i_s}`.
- The local strata clause identifies it with the unique QEM `ν_U` of the chain on the stratum `U s = M_{i_s} ∖ M_{i_s−1}`: `ν_U.map val = ν_{ε,s}.map val`, with `ν_U` quasi-ergodic, `Λ_{i_s} ⊆ supp ν_U`, and uniqueness. These are exactly the properties of the QEM in `thm:qem-local`.
- "Theorem `thm:global-existence` holds" is provided by `global_existence` and by the `SimpleSpectralWitness` clause for the first selected stratum.

**Item (ii).** `all_stable` gives the same limit with a point-dependent `δ(x)` for every `x` approaching `Λ_j`. This again covers all of `W^s(Λ_j)`.

**Item (iii).**

- `equilibrium_limit` gives `ν_{ε,s} → equilibrium s` weakly.
- The first two conjuncts state that `(equilibrium s).map val` is the unique equilibrium state for `φ − log|det DT|E^u|` on `Λ_{i_s}`.
- For `s = 0` under HG1 alone, see `global_existence`.

**Item (iv).** `absorption` says: if `x` eventually enters `A`, there are `N` and `δ_x` such that for every `0 < ε < δ_x` and every control sequence, the entrance time is at most `N`. This is *stronger* than "there exist `ε` and `N`".

**Additional clauses.** `number_selected` (`0 < t ≤ ℓ`) and `distinct` (different strata give different QEMs) are extra.

## Summary

- **Hypotheses.** All hypotheses of the three Lean theorems are hypotheses of the article or encodings of them:
  - the global `C^{r-1}` extension of `e^φ|V̄`;
  - the normalizer `R`;
  - the redundant `Measurable φ`.
- **Conclusions.** Every conclusion of the five article statements is present, in places in a stronger form.
- **Auxiliary data.** No auxiliary existence data (auxiliary Anosov factor, calculi, sources, spectral or leading inputs) remains as a hypothesis.

## Not covered by this audit

- The noise model (`RegularNoise.Maps` / `Laws`) is not compared in detail with § `sec:random_perturb`.
- The Lean definitions of Axiom A, spectral decomposition, basic data and equilibrium state are not compared in detail here.
