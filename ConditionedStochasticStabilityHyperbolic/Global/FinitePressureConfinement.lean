module

public import ConditionedStochasticStabilityHyperbolic.Global.PressureLayerBounds
public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniConfinement

/-!
# Finite pressure/KL/density inputs produce actual subordinate stratum bounds

This consumer keeps the cited KL confinement and cross-space spectral
comparison explicit. It internally chooses common pressure slack, applies
non-rank-one KL confinement, uses complex Gelfand bounds, transfers them to
the actual real killed operators, and deletes reference-null layer boundaries.
It assumes no subordinate mixing and no all-word/global growth conclusion.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.Global.FinitePressureConfinement

open KellerLiverani1999 PressureLayerBounds ComplexStrongFeller

/-- The complete finite subordinate analytic-to-probabilistic producer.
All density laws concern the actual closed-layer transition measures, and
all output bounds concern the actual Borel-stratum real transfer powers. -/
theorem eventually_actual_stratum_bounds_from_finite_KL
    {I : Type*} (E W X : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    [∀ i, CompleteSpace (E i)] [∀ i, Nontrivial (E i)]
    [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℂ (W i)]
    [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, OpensMeasurableSpace (X i)]
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
    (hSF : ∀ i ε, HasStrongFellerKernel (C i ε)) (rawScale : I → ℝ)
    (hcompare : ∀ i ∈ J, ∀ ε, spectralRadius ℂ
      (rawScale i • transferOperator (𝕜 := ℂ) (C i ε) (hSF i ε)) ≤
        spectralRadius ℂ ((scale i : ℂ) • P i ε))
    (U : ∀ i, Set (X i)) (hU : ∀ i, MeasurableSet (U i))
    (σ : ∀ i, Measure (X i)) (q : ∀ i, NNReal → (X i) × (X i) → ENNReal)
    (htransition : ∀ i ∈ J, ∀ ε x, (C i ε).killedTransition x =
      (σ i).withDensity (fun y => q i ε (x, y)))
    (hnull : ∀ i ∈ J, σ i (U i)ᶜ = 0) :
    ∃ β : ℝ, 0 < β ∧ ∀ᶠ ε : NNReal in 𝓝 0, β < dominantRate ε ∧
      ∀ i ∈ J, ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
        ‖(rawScale i • transferOperator (𝕜 := ℝ) (RestrictedLayerChain.chain (C i ε) (U i) (hU i))
          (RestrictedLayerChain.strongFeller (C i ε) (hSF i ε) (U i) (hU i))) ^ n‖ ≤ K * β ^ n := by
  obtain ⟨β, hβ, hβdom, hpiβ⟩ := exists_common_pressure_slack J pressure dominantPressure hgap
  have hconf : ∀ i ∈ J, ∀ᶠ ε : NNReal in 𝓝 0,
      spectralRadius ℂ (rawScale i • transferOperator (𝕜 := ℂ) (C i ε) (hSF i ε)) < ENNReal.ofReal β := by
    intro i hi
    have ha := eventually_subordinate_raw_radius_lt (hKL i hi) (hyp i)
      (scale i) (Real.exp (pressure i)) β (hscale i hi) (Real.exp_pos _).le
      (hdet i hi) (hpiβ i hi) ((hessential i hi).trans_lt (hpiβ i hi))
    filter_upwards [ha] with ε hε
    exact (hcompare i hi ε).trans_lt hε
  have hs : ∀ᶠ ε : NNReal in 𝓝 0, ∀ i ∈ J,
      spectralRadius ℂ (rawScale i • transferOperator (𝕜 := ℂ) (C i ε) (hSF i ε)) < ENNReal.ofReal β :=
    (J.eventually_all).mpr hconf
  have hd : ∀ᶠ ε in 𝓝 (0 : NNReal), β < dominantRate ε := hdom.eventually (lt_mem_nhds hβdom)
  refine ⟨β, hβ, ?_⟩
  filter_upwards [hd, hs] with ε hε hspec
  refine ⟨hε, ?_⟩
  intro i hi
  obtain ⟨r, hr, hrβ, K, hK, hbound⟩ := exists_stratum_bound_of_complex_radius_and_density
    (C i ε) (hSF i ε) (U i) (hU i) (rawScale i) (σ i) (q i ε)
    (htransition i hi ε) (hnull i hi) hβ (hspec i hi)
  exact ⟨K, hK, fun n => (hbound n).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hr.le hrβ.le n) hK)⟩

end ConditionedStochasticStabilityHyperbolic.Global.FinitePressureConfinement
