module

public import ConditionedStochasticStabilityHyperbolic.Paper.ControlSubmersionSources
public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedAllScaleMaps
public import LeanShared.Probability.NormalizedKilledAmbientDensity

/-! The literal represented global killed chain has a jointly measurable
bounded density relative to ambient volume at each positive small scale.
There is no regularity assumption in ε and no uniform density bound as ε→0.
Ambient nonsingularity remains the ordinary diffeomorphism/volume fact.
-/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared
variable {E M ι Parameters : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [MetricSpace Parameters]
  {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
  {evaluate : Parameters → M → M}

omit [FiniteDimensional ℝ E] in
theorem Representation.exists_bounded_global_density
    (p : Representation F Parameters evaluate) (L : Laws (ι := ι))
    (σ : Measure M) [IsFiniteMeasure σ]
    (source : ControlSubmersionSources (E := E) (ι := ι) σ)
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ p.window)
    (Live : Set M) (hLive : MeasurableSet Live)
    (w : M → ℝ) (hwt : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∃ q : M × M → ℝ≥0∞,
      Measurable q ∧ (∀ z, q z ≤ B) ∧ ∀ x,
      (NoiseKernel.chain (L.fixedLaw ε)
        (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1)
        (p.allScale_measurable ε) Live hLive w hwt R hR hwR).killedTransition x =
          σ.withDensity (fun y => q (x, y)) := by
  obtain ⟨C, hC, vol⟩ := F.volume_bound_from_submersion σ source ε hε (hw.trans p.window_le)
  obtain ⟨B, hB, q, hq, hqB, repr⟩ :=
    p.exists_bounded_fixed_transition_density L σ ε hε hw C hC vol
  obtain ⟨q', hq', hqB', repr'⟩ := NormalizedKilledAmbientDensity.exists_density (L.fixedLaw ε)
    (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1)
    (p.allScale_measurable ε) σ q hq repr B hqB Live hLive w hwt R hR hwR
  refine ⟨B, hB, q', hq', hqB', ?_⟩
  intro x
  simpa only [NoiseKernel.chain, WeightedKernel.ofBoundedWeight_killedTransition] using repr' x

omit [FiniteDimensional ℝ E] in
theorem Representation.exists_global_density_family
    (p : Representation F Parameters evaluate) (L : Laws (ι := ι))
    (σ : Measure M) [IsFiniteMeasure σ]
    (source : ControlSubmersionSources (E := E) (ι := ι) σ)
    (Live : Set M) (hLive : MeasurableSet Live)
    (w : M → ℝ) (hwt : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) :
    ∃ density : ℝ≥0 → M × M → ℝ≥0∞, (∀ ε, Measurable (density ε)) ∧
      ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ x,
        (NoiseKernel.chain (L.fixedLaw ε)
          (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1)
          (p.allScale_measurable ε) Live hLive w hwt R hR hwR).killedTransition x =
            σ.withDensity (fun y => density ε (x, y)) := by
  classical
  have all : ∀ ε : ℝ≥0, ∃ q : M × M → ℝ≥0∞, Measurable q ∧
      (0 < ε ∧ ε ≤ p.window → ∀ x,
        (NoiseKernel.chain (L.fixedLaw ε)
          (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1)
          (p.allScale_measurable ε) Live hLive w hwt R hR hwR).killedTransition x =
            σ.withDensity (fun y => q (x, y))) := by
    intro ε
    by_cases he : 0 < ε ∧ ε ≤ p.window
    · obtain ⟨B, _hB, q, hq, _hqB, repr⟩ :=
        p.exists_bounded_global_density L σ source ε he.1 he.2 Live hLive w hwt R hR hwR
      exact ⟨q, hq, fun _ => repr⟩
    · exact ⟨0, measurable_const, fun h => (he h).elim⟩
  choose density hm hd using all
  refine ⟨density, hm, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds p.window_positive)] with ε he hw
  exact hd ε ⟨he, hw.le⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
