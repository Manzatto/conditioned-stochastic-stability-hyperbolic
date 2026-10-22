module

public import ConditionedStochasticStabilityHyperbolic.Global.PressureLayerBounds
public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniConfinement
public import ConditionedStochasticStabilityHyperbolic.Spectral.PowerCompactRadiusComparison
public import ConditionedStochasticStabilityHyperbolic.Spectral.ScaledStrongFellerCompact

/-!
# Positive-noise pressure/KL/density inputs produce actual stratum bounds

This consumer keeps the cited KL confinement and cross-space spectral
comparison explicit. It internally chooses common pressure slack, applies
non-rank-one KL confinement, uses complex Gelfand bounds, transfers them to
the actual real killed operators, and deletes reference-null layer boundaries.
It assumes no subordinate mixing and no all-word/global growth conclusion.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.Global.PositiveNoiseEigenPressureGrowthEventually

open KellerLiverani1999 PressureLayerBounds ComplexStrongFeller

/-- The complete finite subordinate analytic-to-probabilistic producer.
All density laws concern the actual closed-layer transition measures, and
all output bounds concern the actual Borel-stratum real transfer powers. -/
theorem eventually_stratum_bounds_from_KL_and_eigen_comparison
    {I : Type*} (E W X : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    [∀ i, CompleteSpace (E i)] [∀ i, Nontrivial (E i)]
    [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℂ (W i)]
    [∀ i, MetricSpace (X i)] [∀ i, CompactSpace (X i)] [∀ i, Nonempty (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)]
    (J : Finset I) (pressure : I → ℝ) (dominantPressure : ℝ)
    (hgap : ∀ i ∈ J, pressure i < dominantPressure)
    (P : ∀ i, NNReal → (E i) →L[ℂ] (E i))
    (embed : ∀ i, (E i) →L[ℂ] (W i))
    (hyp : ∀ i, Hypotheses (P i) (embed i))
    (hKL : ∀ i ∈ J, ClassicalConfinementContract (E := E i) (W := W i))
    (scale : I → ℝ) (hscale : ∀ i ∈ J, 0 < scale i)
    (hdet : ∀ i ∈ J, spectralRadius ℂ ((scale i : ℂ) • P i 0) ≤ ENNReal.ofReal (Real.exp (pressure i)))
    (hessential : ∀ i ∈ J, scale i * (hyp i).alpha ≤ Real.exp (pressure i))
    (dominantRate : NNReal → ℝ)
    (hdom : Tendsto dominantRate (𝓝 0) (𝓝 (Real.exp dominantPressure)))
    (C : ∀ i, NNReal → AbsorbingMarkovChains.CanonicalChain (X i))
    (hSF : ∀ i ε, 0 < ε → HasStrongFellerKernel (C i ε)) (rawScale : I → ℝ)
    (hUltra : ∀ i ∈ J, StrongFellerSquareCompact.UltraFellerContract (X := X i))
    (hFredholm : ∀ i ∈ J, PowerCompactGap.SquareCompactFredholm (F := (X i) →ᵇ ℂ))
    (hcompare : ∀ i ∈ J, ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ (hε : 0 < ε) (f : (X i) →ᵇ ℂ), f ≠ 0 → ∀ z : ℂ,
      (rawScale i • transferOperator (𝕜 := ℂ) (C i ε) (hSF i ε hε)) f = z • f →
      scale i * (hyp i).alpha < ‖z‖ → z ∈ spectrum ℂ ((scale i : ℂ) • P i ε))
    (U : ∀ i, Set (X i)) (hU : ∀ i, MeasurableSet (U i))
    (σ : ∀ i, Measure (X i)) (q : ∀ i, NNReal → (X i) × (X i) → ENNReal)
    (htransition : ∀ i ∈ J, ∀ ε, 0 < ε → ∀ x, (C i ε).killedTransition x =
      (σ i).withDensity (fun y => q i ε (x, y)))
    (hnull : ∀ i ∈ J, σ i (U i)ᶜ = 0) :
    ∃ β : ℝ, 0 < β ∧ ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ hε : 0 < ε, β < dominantRate ε ∧
      ∀ i ∈ J, ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
        ‖(rawScale i • transferOperator (𝕜 := ℝ) (RestrictedLayerChain.chain (C i ε) (U i) (hU i))
          (RestrictedLayerChain.strongFeller (C i ε) (hSF i ε hε) (U i) (hU i))) ^ n‖ ≤ K * β ^ n := by
  obtain ⟨β, hβ, hβdom, hpiβ⟩ := exists_common_pressure_slack J pressure dominantPressure hgap
  have hconf : ∀ i ∈ J, ∀ᶠ ε : NNReal in 𝓝 0,
      spectralRadius ℂ ((scale i : ℂ) • P i ε) < ENNReal.ofReal β := by
    intro i hi
    exact eventually_subordinate_raw_radius_lt (hKL i hi) (hyp i)
      (scale i) (Real.exp (pressure i)) β (hscale i hi) (Real.exp_pos _).le
      (hdet i hi) (hpiβ i hi) ((hessential i hi).trans_lt (hpiβ i hi))
  have hs : ∀ᶠ ε : NNReal in 𝓝 0, ∀ i ∈ J,
      spectralRadius ℂ ((scale i : ℂ) • P i ε) < ENNReal.ofReal β :=
    (J.eventually_all).mpr hconf
  have hd : ∀ᶠ ε in 𝓝 (0 : NNReal), β < dominantRate ε := hdom.eventually (lt_mem_nhds hβdom)
  have hcomp := (J.eventually_all).mpr hcompare
  refine ⟨β, hβ, ?_⟩
  filter_upwards [hd.filter_mono nhdsWithin_le_nhds, hs.filter_mono nhdsWithin_le_nhds, hcomp] with ε hdom hspec hcomparisons
  intro hε
  refine ⟨hdom, ?_⟩
  intro i hi
  let : Nontrivial ((X i) →ᵇ ℂ) := ⟨⟨0, 1, by
    intro he
    have hpoint := congrArg (fun f : (X i) →ᵇ ℂ => f (Classical.choice (inferInstance : Nonempty (X i)))) he
    exact zero_ne_one hpoint⟩⟩
  have hraw : spectralRadius ℂ (rawScale i • transferOperator (𝕜 := ℂ)
      (C i ε) (hSF i ε hε)) < ENNReal.ofReal β := by
    have he : (rawScale i • transferOperator (𝕜 := ℂ) (C i ε) (hSF i ε hε)) =
        ((rawScale i : ℂ) • transferOperator (𝕜 := ℂ) (C i ε) (hSF i ε hε)) := by
      ext f x
      rfl
    have hc : IsCompactOperator ((rawScale i • transferOperator (𝕜 := ℂ)
        (C i ε) (hSF i ε hε)) ^ 2 : ((X i) →ᵇ ℂ) →L[ℂ] ((X i) →ᵇ ℂ)) := by
      rw [he]
      exact StrongFellerSquareCompact.raw_square_compact (hUltra i hi) (C i ε) (hSF i ε hε) (rawScale i)
    exact PowerCompactRadiusComparison.radius_lt_of_eigenvalue_comparison
      (hFredholm i hi) ((scale i : ℂ) • P i ε)
      (rawScale i • transferOperator (𝕜 := ℂ) (C i ε) (hSF i ε hε)) hc
      (scale i * (hyp i).alpha) β (mul_nonneg (hscale i hi).le (hyp i).alpha_pos.le)
      ((hessential i hi).trans_lt (hpiβ i hi)) (hspec i hi) (hcomparisons i hi hε)
  obtain ⟨r, hr, hrβ, K, hK, hbound⟩ := exists_stratum_bound_of_complex_radius_and_density
    (C i ε) (hSF i ε hε) (U i) (hU i) (rawScale i) (σ i) (q i ε)
    (htransition i hi ε hε) (hnull i hi) hβ hraw
  exact ⟨K, hK, fun n => (hbound n).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hr.le hrβ.le n) hK)⟩

end ConditionedStochasticStabilityHyperbolic.Global.PositiveNoiseEigenPressureGrowthEventually
