# Conditioned stochastic stability of equilibrium states on uniformly hyperbolic sets — Lean formalization

This repository is a complete Lean 4 formalization of the main results of the article
*Conditioned stochastic stability of equilibrium states on uniformly hyperbolic sets* ([arxiv.org/abs/2506.15503](https://arxiv.org/abs/2506.15503)).

- Every theorem is proved.
- The sources contain no `sorry` and no `axiom`.
- Every declaration depends only on the three standard axioms `propext`, `Classical.choice` and
  `Quot.sound`.

The project uses Lean 4.35.0 and Mathlib.

## Main theorems

The theorems are named after their numbers in the article. They are in
[MainTheorems.lean](ConditionedStochasticStabilityHyperbolic/MainTheorems.lean), in the namespace
`ConditionedStochasticStabilityHyperbolic`.

| Article | Content | Lean |
| --- | --- | --- |
| Theorem 2.7 | Under (HL), for small noise the process conditioned to stay in `V̄` has a unique quasi-ergodic measure `ν_ε` with `Λ ⊆ supp ν_ε`, and `ν_ε = μ_ε(· g_ε)` for the leading eigen-data of `P_ε` | `Theorem2_7` |
| Theorem 2.8 | `ν_ε` converges weakly to the unique equilibrium state of `φ − log\|det DT\|_{E^u}\|` on `Λ` | `Theorem2_8` |
| Theorem 2.10 | Under (HG1), the process killed in `A` has simple leading eigen-data, a normalized spectral gap, and a unique quasi-ergodic measure supported on the dominant basic set | `Theorem2_10` |
| Theorem 2.11 | These quasi-ergodic measures converge weakly to the equilibrium state of the dominant basic set | `Theorem2_11` |
| Theorem 3.15 | Compact embedding of the anisotropic spaces: `B^{Θ',t',s'}` embeds compactly in `B^{Θ,t,s}` | `Theorem3_15` (see below) |
| Theorem 6.5 | Under (HG2), items (i)–(iv): conditioned limits on stable sets, weak limits on each retained basic set, finite-time absorption | `Theorem6_5` |

[docs/StatementAudit.md](docs/StatementAudit.md) compares each hypothesis and conclusion with the
article. Most hypotheses are the article's own; the rest are encodings:

- `e^φ ∈ C^{r−1}(V̄)` is given as the restriction of a nonnegative `C^{r−1}` function on `M`;
- the transfer operator is normalized by a bound `R ≥ e^φ`, which changes none of the conclusions;
- `Measurable φ` is stated separately in Theorem 6.5.

The global theorems assume `T(Ā) ⊂ A` and that the weight agrees with the reference weight on the
retained basic sets. Quasi-ergodicity is tested on bounded measurable observables, and the
Riemannian metric is continuous.

In places the conclusions are stronger than the article's. For example, Theorem 2.10 also gives a
normalized spectral gap, and the absorption time in Theorem 6.5 is uniform over all noise
realizations.

## The compact embedding theorem (Theorem 3.15)

The article proves Theorem 3.15 by reducing it to a compact domain `K ⊂ ℝ^d` in one chart.
`Theorem3_15` is this local statement:

- **Statement.** For cone systems `Θ < Θ'` and `s ≤ t`, the space `B^{Θ',t,s}(K)` embeds
  compactly and injectively in `B^{Θ,t−η−δ₊,s−η−δ₋}(K)`, for every `η > 0` and `δ₊, δ₋ ≥ 0`. This
  covers every pair of exponents in the theorem.
- **Proof.** It is `AllFakeLeafCanonicalCrossCone.compact_injective_embedding`. Its only
  hypotheses are the cone ordering (`C ⊆ D`, and every unit vector outside `D` lies in `Cm`) and
  `s ≤ t`.
- **Fake leaves.** The spaces are built from the article's leaf family: all embedded `C¹`
  submanifolds of the unstable dimension satisfying the cone condition (`AllFakeLeafModel`).

Other forms of the theorem in the Baladi folder:

- **Smooth-core comparison.** `AllFakeLeafOrderedConeCoreComparison.exists_ordered_core_comparison`
  is the comparison of norms on the smooth core for ordered cones (Proposition 3.14, Baladi
  Corollary 5.19).
- **Manifold version, as used in the proof.** `ManifoldCompactEmbedding`, `GlobalCompactEmbedding`
  and `PhysicalModelCompactWeak` assemble the local embeddings over finitely many charts with a
  partition of unity. They give the compact strong-to-weak inclusion of the transfer-operator
  spaces, which is assumption (iii) of the Keller–Liverani theorem in Lemma 4.5.

## Results from *Dynamical Zeta Functions and Dynamical Determinants for Hyperbolic Maps* on Axiom A diffeomorphisms

The folder
[Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps/](ConditionedStochasticStabilityHyperbolic/Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps/)
(241 modules) collects the theory of transfer operators of hyperbolic basic sets developed in
Chapters 4–5 of V. Baladi, *Dynamical Zeta Functions and Dynamical Determinants for Hyperbolic
Maps: A Functional Approach* (Ergebnisse der Mathematik und ihrer Grenzgebiete (3) 68, Springer,
2018), and in V. Baladi and M. Tsujii, *Dynamical determinants and spectrum for hyperbolic
diffeomorphisms* (Contemp. Math. 469, 2008). In the table below, "Baladi" refers to the book and
"Baladi–Tsujii" to their paper.

The article cites these results. Here they are proved, for the transfer operator
`P_g φ = g · (φ ∘ T)` of a `C^r` diffeomorphism (`r > 1`) with a hyperbolic basic set `Λ` and a
`C^{r−1}` weight `g`.

| Article (source) | What was formalized | Main modules |
| --- | --- | --- |
| Definitions 3.2–3.5 (Baladi Def. 4.10, 4.11, 4.14, 4.15): cone systems, adapted charts and partitions of unity | Frequency cones around the stable and unstable axes of the adapted charts, satisfying the fake-leaf cone requirements. Finitely many smooth charts and the partition of unity are constructed. | `AdaptedHalfConeData`, `PhysicalManifoldModel`, `ConstructedHolderPhysicalModel` |
| Definition 3.7 (Baladi Def. 5.10): fake unstable leaves | The family of *all* `C¹` leaves satisfying the cone condition, with graph maps, slopes and induced volume | `AllFakeLeafModel`, `AllFakeLeaf*` |
| Definitions 3.8 (Baladi Def. 5.12) and 3.13: the spaces `B^{Θ,t,s}(K)` and `B^{t,s}(T,V)` | Completions of `C^u_c` under the dyadic anisotropic norms, locally and on the manifold | `AllFakeLeafCanonicalDistribution`, `PhysicalManifold*` |
| Proposition 3.9 (Baladi Lemma 5.14) | `C^u` functions belong to `B^{t,s}`, and the completion embeds faithfully into distributions | `AllFakeLeafDistribution`, `AllFakeLeafCanonicalDistribution` |
| Proposition 3.14 (Baladi Cor. 5.19): Leibniz and cone comparison bounds | Smooth-core comparison for ordered cones, and bounded multiplication by smooth functions | `AllFakeLeafOrderedConeCoreComparison`, `PhysicalModelAnalyticMultiplier` |
| Theorem 3.15: compact embedding | See the previous section | `AllFakeLeafCanonicalCompact`, `ManifoldCompactEmbedding` |
| Theorem 4.3 (Baladi Thm. 5.1, Baladi–Tsujii Thm. 1.1): boundedness and essential spectral radius | Boundedness of `P_g` on `B^{t,s}`, and a Lasota–Yorke inequality from the Baladi–Tsujii block estimates (Lemmas 4.6, 4.14). Outside a radius `ρ < r(P_g)`, the spectrum consists of isolated eigenvalues of finite multiplicity. The explicit formula `Q^{t,s}(T,g)` for `ρ` is not stated, because the proof only needs `ρ < r(P_g)`. | `AllFakeLeafNativeTwoNormBound`, `AllFakeLeafLocalizedTransfer`, `AdmissibleExponents`, `PhysicalManifoldPressureSources` |
| Remark 4.4 (Baladi–Tsujii Rem. 1.6, Lemmas 3.2, 3.5): `r(P_g) = exp P_top(T, Λ, log g − log\|det DT\|_{E^u}\|)` | Upper bound from the strict pressure cover blocks; lower bound from the growth of orbit integrals | `DomainPressureStrictBlock`, `IntrinsicPressureBlock`, `PhysicalModelNativeCoefficients`, `PhysicalModelNativeRadiusUpper`, `PhysicalCarrierPressureFromCoefficients` |
| Remark 4.4 (Gouëzel–Liverani Thm. 5.1): `r(P_g)` is a simple eigenvalue, and the only one of its modulus | `e^P` lies in the spectrum (positive cone). Jordan blocks are excluded and the leading projector has rank one (regularized traces). | `PhysicalModelPositiveCone`, `PhysicalModelSpectralLeading`, `PhysicalModelTraceLeading`, `AdaptedTubeUnitCarrierLeading` |
| Remark 4.4 (Gouëzel–Liverani Lemmas 6.1–6.2, Thm. 6.4): `ν^g(f) = μ(f γ)` | The product of the leading left and right eigenvectors is the equilibrium state, via the pressure tangent (Jensen) | `PhysicalModelNativeProductIdentification`, `Spectral/DeterministicLeading*`, `Paper/LocalEquilibriumIdentification` |

Other classical results proved in the formalization:

- **Equilibrium states** (Baladi Theorem 7.5, Bowen). Existence and uniqueness of the equilibrium
  state of a `C^{r−1}` positive weight on a mixing hyperbolic basic set is
  `LeanShared.HyperbolicBasicSet.BasicData.exists_proved_equilibriumPackage`
  (`LeanShared/Dynamics/ProvedHyperbolicEquilibriumPackage.lean`).
- **Keller–Liverani perturbation** (Theorem A.1), in the form the proof uses:
  `KellerLiveraniProjectorSource.classicalContract` (in `Spectral/`).
  - It covers a simple isolated leading eigenvalue: spectral confinement, a unique simple
    perturbed eigenvalue `λ_ε → λ`, persistence of the spectral gap, and the coercivity estimate
    `‖Π_ε f‖ ≤ K₂ |Π_ε f|`.
  - Item (1) is proved as the convergence `Π_ε → Π_0` in the weak norm, without the explicit rate
    `τ(ε)^η`.
  - Hypothesis (iii) enters through the absence of residual spectrum above `α`, which
    `EssentialRadiusSource` derives from the compactness of the weak inclusion.
- **Eigenvalues across two spaces** (Proposition A.2, Baladi–Tsujii Appendix A). The comparison of
  eigenvalues and generalized eigenspaces is in `Spectral/GeneralizedSpectralComparison` and
  `Spectral/CommonAmbient*`.

## Layout

```
.
├── README.md
├── LICENSE
├── lakefile.toml, lake-manifest.json, lean-toolchain
├── ConditionedStochasticStabilityHyperbolic.lean     root: main theorems and folder indices
├── Audit.lean                                        axiom audit of every declaration
├── ConditionedStochasticStabilityHyperbolic/
│   ├── MainTheorems.lean                             Theorems 2.7, 2.8, 2.10, 2.11, 3.15, 6.5
│   ├── Baladi_…_for_Hyperbolic_Maps/                 anisotropic spaces and transfer operators (§3–4)
│   ├── Spectral/                                     annealed operators, Keller–Liverani, QEMs (§4–5)
│   ├── Restriction/                                  restriction to neighbourhoods and strata (§5)
│   ├── Neighborhoods/                                isolating neighbourhoods and collars
│   ├── Global/                                       filtrations and global assembly (§6)
│   └── Paper/                                        hypotheses, noise model, final assembly
├── LeanShared/                                       general mathematics used by the proofs
├── AbsorbingMarkovChains/                            absorbing Markov chains and quasi-ergodic measures
├── docs/
│   └── StatementAudit.md                             statement-by-statement comparison with the article
└── scripts/
    └── verify.sh                                     strict check of every module and the axiom audit
```

Each folder `F/` has an index module `F.lean` that imports all of its files.

The repository has three Lean libraries:

- `ConditionedStochasticStabilityHyperbolic` is specific to the article.
- `LeanShared` contains the general mathematics the proofs rely on, stated outside the setting of
  the article: shadowing, Markov coding, pressure and equilibrium states for hyperbolic basic sets;
  dyadic Fourier blocks and anisotropic norm estimates; resolvents, Riesz projectors and trace
  arguments for operators; and the needed manifold geometry and measure theory.
- `AbsorbingMarkovChains` develops Markov chains with an absorbing state, their conditioned laws and quasi-ergodic measures.

`LeanShared` and `AbsorbingMarkovChains` include only the parts used by this formalization.

## Build

Install Lean through [elan](https://github.com/leanprover/elan). Then, from this directory:

```sh
lake exe cache get   # download the compiled Mathlib
lake build
```

The first build compiles about 3,000 modules; some of the final files take several minutes each.
The build produces no warnings.

To check that every declaration of the three libraries depends only on the standard axioms, run:

```sh
lake env lean Audit.lean
```

`bash scripts/verify.sh` also re-checks every module with warnings treated as errors.

Lean 4.35 can also export the whole development, Mathlib included, and replay it through the
kernel:

```sh
lake check               # Lean's kernel
lake check --paranoid    # also the bundled independent checkers (lean4lean, nanoda, …)
```

`lake check` runs inside a `bubblewrap` sandbox, which exists only on Linux. On macOS, add
`--inadvisably-no-sandbox`. The sandbox only protects the machine from untrusted code; it does not
change what is checked.

## License

Apache License 2.0; see [LICENSE](LICENSE).
