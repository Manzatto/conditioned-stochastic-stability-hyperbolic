module
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeMainTheorems
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafCanonicalCompact

/-!
# Main theorems, numbered as in the manuscript

The manuscript is *Conditioned stochastic stability of equilibrium states on uniformly hyperbolic
sets*. Each theorem below is named after its number in the manuscript and is proved by the final
theorem of the corresponding chain.

| Manuscript | Label | Lean |
| --- | --- | --- |
| Theorem 2.7 | `thm:qem-local` | `Theorem2_7` |
| Theorem 2.8 | `thm:local` | `Theorem2_8` |
| Theorem 2.10 | `thm:global-existence` | `Theorem2_10` |
| Theorem 2.11 | `thm:global` | `Theorem2_11` |
| Theorem 3.15 | `thm:compact_embedding` | `Theorem3_15` |
| Theorem 6.5 | `thm:global-global` | `Theorem6_5` |

All of them depend only on `propext`, `Classical.choice` and `Quot.sound`.
`docs/StatementAudit.md` compares each hypothesis and conclusion with the manuscript.
-/

public noncomputable section
open Set Function MeasureTheory Filter IsManifold Bundle
open scoped Manifold ContDiff Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic
open LeanShared HyperbolicBasicSet Paper Paper.RegularNoise

section Local

variable {X E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace X] [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (TangentSpace (𝓘(ℝ,E)) : X → Type _)]
  {ι : Type} [Fintype ι] {T : X ≃ₜ X} {g : X → ℝ} {Λ V : Set X}

local instance mainCompactClosure (W : Set X) : CompactSpace (closure W) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact

/-- **Theorem 2.7** (`thm:qem-local`). Under Hypothesis (HL), for every small noise scale `ε` the
process on `V̄` weighted by `e^φ` and killed outside `V̄` has a quasi-ergodic measure `ν_ε` with
`Λ ⊆ supp ν_ε`, unique among quasi-ergodic measures whose support contains `Λ`, and
`ν_ε = μ_ε(· g_ε)` for the leading eigenfunction `g_ε` and eigenmeasure `μ_ε` of `P_ε`, whose
eigenvalue is the spectral radius on `C⁰(V̄)`. The weight `e^φ ∈ C^{r-1}(V̄)` is given as the
restriction of a nonnegative `C^{r-1}` function `w` on `M` equal to `g` on `Λ`. -/
theorem Theorem2_7 (h : HL (E := E) T g Λ V)
    (P : Maps (E := E) (ι := ι) T h.r) (L : Laws (ι := ι))
    (w : X → ℝ) (hwRegular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (h.r - 1) w)
    (hw0 : ∀ x, 0 ≤ w x) (agree : EqOn w g Λ)
    (φ : X → ℝ) (weight_exp : ∀ x : closure V, w x.val = Real.exp (φ x.val)) :
    ∃ (hwExp : Continuous (fun x : closure V => Real.exp (φ x.val)))
      (R : ℝ) (hR : 0 < R) (bound : ∀ x : closure V, Real.exp (φ x.val) ≤ R),
      LocalConclusions.Existence P L (closure V) Λ isClosed_closure.measurableSet
        (fun x => Real.exp (φ x.val)) hwExp.measurable R hR bound := by
  obtain ⟨hwExp, R, hR, bound, stable, -⟩ :=
    NativeLocalTheorem.stability_and_retention h P L w hwRegular hw0 agree φ weight_exp
  exact ⟨hwExp, R, hR, bound, stable.existence⟩

/-- **Theorem 2.8** (`thm:local`). The quasi-ergodic measures `ν_ε` of Theorem 2.7 converge
weakly, as `ε → 0⁺`, to the unique equilibrium state of `φ - log |det DT|_{E^u}|` on `Λ`. -/
theorem Theorem2_8 (h : HL (E := E) T g Λ V)
    (P : Maps (E := E) (ι := ι) T h.r) (L : Laws (ι := ι))
    (w : X → ℝ) (hwRegular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (h.r - 1) w)
    (hw0 : ∀ x, 0 ≤ w x) (agree : EqOn w g Λ)
    (φ : X → ℝ) (weight_exp : ∀ x : closure V, w x.val = Real.exp (φ x.val)) :
    ∃ (hwExp : Continuous (fun x : closure V => Real.exp (φ x.val)))
      (R : ℝ) (hR : 0 < R) (bound : ∀ x : closure V, Real.exp (φ x.val) ≤ R),
      LocalConclusions.Stability P L (closure V) Λ isClosed_closure.measurableSet
        (fun x => Real.exp (φ x.val)) hwExp.measurable R hR bound
        (fun x => φ x - Real.log (h.basic.hyperbolic.unstableJacobian x)) := by
  obtain ⟨hwExp, R, hR, bound, stable, -⟩ :=
    NativeLocalTheorem.stability_and_retention h P L w hwRegular hw0 agree φ weight_exp
  exact ⟨hwExp, R, hR, bound, stable⟩

end Local

section Global

variable {E ι : Type*} {X : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace X] [CompactSpace X] [SecondCountableTopology X] [ChartedSpace E X]
  [IsManifold (𝓘(ℝ, E)) ∞ X]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι]
  {T : X ≃ₜ X} (D : SpectralDecomposition (E := E) T) {g : X → ℝ} {A : Set X}

/-- **Theorem 2.10** (`thm:global-existence`). Under Hypothesis (HG1), for every small noise scale
`ε` the process killed on entering `A` has a normalized spectral gap, a quasi-ergodic measure `ν_ε`
whose support contains the dominant basic set `Λ_i`, unique under that support condition, and
eigen-data `g_ε`, `μ_ε` unique up to scaling with `ν_ε = μ_ε(· g_ε)` and
`λ_ε = r(P̂_ε | C⁰(M \ A))`. -/
theorem Theorem2_10 (h : HG1 D g A) (P : Maps (E := E) (ι := ι) T h.r)
    (L : Laws (ι := ι)) (φ : X → ℝ) (hw : Continuous (fun x => Real.exp (φ x)))
    (R : ℝ) (hR : 0 < R) (bound : ∀ x, Real.exp (φ x) ≤ R)
    (strict : MapsTo T (closure A) A)
    (coreAgreement : ∀ i, D.core i ⊆ Aᶜ → EqOn (fun x => Real.exp (φ x)) g (D.core i))
    (localWeightX : ∀ i, D.core i ⊆ Aᶜ → ∃ W : Set X, IsOpen W ∧ D.core i ⊆ W ∧
      ∀ ζ : X → ℝ, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ ζ → tsupport ζ ⊆ W →
        FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (h.r - 1)
          (ζ * fun x => Real.exp (φ x))) :
    letI : CompactSpace ↥(Aᶜ) := isCompact_iff_compactSpace.mp h.absorbing_open.isClosed_compl.isCompact
    ∃ ν : ℝ≥0 → ProbabilityMeasure ↥(Aᶜ),
      ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ (hε : 0 < ε) (hwindow : ε ≤ P.window),
        let CL := RestrictedNoise.chain (L.law ε)
          (fun z : X × cube (ι := ι) ε => P.family ε z.2.val z.1)
          (P.raw_measurable ε hε hwindow) Aᶜ h.absorbing_open.measurableSet.compl
          (fun x => Real.exp (φ x.val)) (hw.comp continuous_subtype_val).measurable R hR
          (fun x => bound x.val)
        let core := {x : ↥(Aᶜ) | x.val ∈ D.core h.dominant}
        LocalConclusions.NormalizedGap CL core (ν ε) ∧
        CL.IsQuasiErgodic (ν ε : Measure _) ∧ core ⊆ (ν ε : Measure _).support ∧
        (∀ ζ : Measure _, CL.IsQuasiErgodic ζ → core ⊆ ζ.support → ζ = (ν ε : Measure _)) ∧
        Nonempty (LocalConclusions.SimpleSpectralWitness CL R (ν ε)) := by
  obtain ⟨-, ν, -, -, -, -, points⟩ := NativeMainTheorems.global_existence D h P L φ hw R hR bound
    strict coreAgreement localWeightX
  exact ⟨ν, points⟩

/-- **Theorem 2.11** (`thm:global`). The quasi-ergodic measures `ν_ε` of Theorem 2.10 converge
weakly, as `ε → 0⁺`, to the unique equilibrium state `ν^g` of `φ - log |det DT|_{E^u}|` on the
dominant basic set. -/
theorem Theorem2_11 (h : HG1 D g A) (P : Maps (E := E) (ι := ι) T h.r)
    (L : Laws (ι := ι)) (φ : X → ℝ) (hw : Continuous (fun x => Real.exp (φ x)))
    (R : ℝ) (hR : 0 < R) (bound : ∀ x, Real.exp (φ x) ≤ R)
    (strict : MapsTo T (closure A) A)
    (coreAgreement : ∀ i, D.core i ⊆ Aᶜ → EqOn (fun x => Real.exp (φ x)) g (D.core i))
    (localWeightX : ∀ i, D.core i ⊆ Aᶜ → ∃ W : Set X, IsOpen W ∧ D.core i ⊆ W ∧
      ∀ ζ : X → ℝ, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ ζ → tsupport ζ ⊆ W →
        FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (h.r - 1)
          (ζ * fun x => Real.exp (φ x))) :
    letI : CompactSpace ↥(Aᶜ) := isCompact_iff_compactSpace.mp h.absorbing_open.isClosed_compl.isCompact
    ∃ initial : ProbabilityMeasure ↥(Aᶜ), ∃ ν : ℝ≥0 → ProbabilityMeasure ↥(Aᶜ),
      (initial : Measure ↥(Aᶜ)).map Subtype.val = (h.deterministic_equilibrium.state : Measure X) ∧
      ThermodynamicDefinitions.IsEquilibriumState T
        (fun x => φ x - Real.log ((D.basic h.dominant).hyperbolic.unstableJacobian x))
        (D.core h.dominant) h.deterministic_equilibrium.state ∧
      (∀ ζ : ProbabilityMeasure X, ThermodynamicDefinitions.IsEquilibriumState T
        (fun x => φ x - Real.log ((D.basic h.dominant).hyperbolic.unstableJacobian x))
        (D.core h.dominant) ζ → ζ = h.deterministic_equilibrium.state) ∧
      Tendsto ν (𝓝[>] (0 : ℝ≥0)) (𝓝 initial) ∧
      ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ (hε : 0 < ε) (hwindow : ε ≤ P.window),
        let CL := RestrictedNoise.chain (L.law ε)
          (fun z : X × cube (ι := ι) ε => P.family ε z.2.val z.1)
          (P.raw_measurable ε hε hwindow) Aᶜ h.absorbing_open.measurableSet.compl
          (fun x => Real.exp (φ x.val)) (hw.comp continuous_subtype_val).measurable R hR
          (fun x => bound x.val)
        let core := {x : ↥(Aᶜ) | x.val ∈ D.core h.dominant}
        LocalConclusions.NormalizedGap CL core (ν ε) ∧
        CL.IsQuasiErgodic (ν ε : Measure _) ∧ core ⊆ (ν ε : Measure _).support ∧
        (∀ ζ : Measure _, CL.IsQuasiErgodic ζ → core ⊆ ζ.support → ζ = (ν ε : Measure _)) ∧
        Nonempty (LocalConclusions.SimpleSpectralWitness CL R (ν ε)) :=
  NativeMainTheorems.global_existence D h P L φ hw R hR bound strict coreAgreement localWeightX

/-- **Theorem 6.5** (`thm:global-global`). Under Hypothesis (HG2), with the greedy filtration
`M_{i_0} ⊃ ⋯ ⊃ M_{i_{t-1}}` built from the spectral decomposition, items (i)–(iv) of the
manuscript hold: uniform and pointwise conditioned limits on the stable sets, weak convergence of
each `ν_{ε,s}` to the equilibrium state on `Λ_{i_s}`, and finite-time absorption. The statement is
the one of `NativeProvedHG2.complete_with_local_strata_native`; `docs/StatementAudit.md` lists its
clauses against the manuscript. -/
theorem Theorem6_5 [MeasurableSpace E] [BorelSpace E] (D0 : SpectralDecomposition (E := E) T)
    (g φ : X → ℝ) (A : Set X) (h : HG2 D0 g A) (strict : MapsTo T (closure A) A)
    (P : Maps (E := E) (ι := ι) T h.r) (L : Laws (ι := ι))
    (hw : Continuous (fun x => Real.exp (φ x)))
    (R : ℝ) (hR : 0 < R) (bound : ∀ x, Real.exp (φ x) ≤ R) (hφ : Measurable φ)
    (coreAgreement : ∀ i, D0.core i ⊆ Aᶜ → EqOn (fun x => Real.exp (φ x)) g (D0.core i))
    (localWeightX : ∀ i, D0.core i ⊆ Aᶜ → ∃ W : Set X, IsOpen W ∧ D0.core i ⊆ W ∧
      ∀ ζ : X → ℝ, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ ζ → tsupport ζ ⊆ W →
        FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (h.r - 1)
          (ζ * fun x => Real.exp (φ x))) :
    type_of% (NativeMainTheorems.global_global D0 g φ A h strict P L hw R hR bound hφ
      coreAgreement localWeightX) :=
  NativeMainTheorems.global_global D0 g φ A h strict P L hw R hR bound hφ coreAgreement
    localWeightX

end Global

section CompactEmbedding

open AllFakeLeafModel AllFakeLeafCanonicalDistribution

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Theorem 3.15** (`thm:compact_embedding`), in the local form to which the manuscript reduces
it: on a compact `K ⊆ ℝ^d`, for cone systems `Θ = (C, Cm, Φ)` and `Θ' = (D, Dm, Ψ)` with `Θ < Θ'`
(encoded as `C ⊆ D` and every unit vector outside `D` lying in `Cm`) and `s ≤ t`, the anisotropic
space `B^{Θ',t,s}(K)` built from all `C¹` fake unstable leaves embeds compactly and injectively in
`B^{Θ,t',s'}(K)` with `t' = t - η - δ true` and `s' = s - η - δ false`, for every `η > 0` and
`δ ≥ 0`. -/
theorem Theorem3_15 (U : Submodule ℝ E) {C D Cm Dm : Set E}
    (coneC : ConeData U C) (coneD : ConeData U D) (basis : OrthonormalBasis ι ℝ U)
    (χ ψ : ConeDyadicSymbols.RadialCutoff)
    (Φ : ConeDyadicSymbols.AngularCutoff C Cm) (Ψ : ConeDyadicSymbols.AngularCutoff D Dm)
    {K : Set E} (compact : IsCompact K) (t s : ℝ) {η : ℝ} (positive : 0 < η) (δ : Bool → ℝ)
    (nonnegative : ∀ b, 0 ≤ δ b) (inside : C ⊆ D)
    (ordered : ∀ ξ : E, ‖ξ‖ = 1 → ξ ∉ D → ξ ∈ Cm) (order : s ≤ t) :
    IsCompactOperator (AllFakeLeafCanonicalCrossCone.embedding U coneC coneD basis χ ψ Φ Ψ compact
        t s positive δ nonnegative) ∧
      Injective (AllFakeLeafCanonicalCrossCone.embedding U coneC coneD basis χ ψ Φ Ψ compact
        t s positive δ nonnegative) :=
  AllFakeLeafCanonicalCrossCone.compact_injective_embedding U coneC coneD basis χ ψ Φ Ψ compact
    t s positive δ nonnegative inside ordered order

end CompactEmbedding

end ConditionedStochasticStabilityHyperbolic
