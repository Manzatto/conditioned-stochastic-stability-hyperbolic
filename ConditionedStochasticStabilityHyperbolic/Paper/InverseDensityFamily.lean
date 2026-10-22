module

public import ConditionedStochasticStabilityHyperbolic.Paper.InverseDensityFixedCube
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseCloseness

/-! A law-independent family of ordinary inverse/Jacobian/plaque facts produces
all sufficiently small actual density certificates. The geometric tolerance is
chosen before the noise law; no supplied inverse closeness, spectral density,
averaged adjoint or smoothing is hidden in this source record. -/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared ControlledPlaqueClosure
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {T : M ≃ₜ M} {r : ℝ}

structure InverseDensityOrdinarySources (F : Maps (E := E) (ι := ι) T r)
    (σ : Measure M) (V K G : Set M) (w : K → ℝ) (R : ℝ) where
  window : ℝ≥0
  window_positive : 0 < window
  window_le : window ≤ F.window
  geometry : ∀ ε : ℝ≥0, 0 < ε → ε ≤ window → InverseCubeGeometry F ε V G
  weight : (ε : ℝ≥0) → M × cube (ι := ι) ε → ℝ
  measurable_weight : ∀ ε, 0 < ε → ε ≤ window → Measurable (weight ε)
  nonnegative_weight : ∀ ε, 0 < ε → ε ≤ window → ∀ x a, 0 ≤ weight ε (x, a)
  continuous_weight : ∀ ε, 0 < ε → ε ≤ window → ∀ a, Continuous (fun x => weight ε (x, a))
  bounded_weight : ∀ ε, 0 < ε → ε ≤ window → ∃ B : ℝ, 0 ≤ B ∧ ∀ x a, ‖weight ε (x, a)‖ ≤ B
  positive_weight : ∀ ε, 0 < ε → ε ≤ window → ∀ x, x ∈ K → x ∈ G → ∀ a, 0 < weight ε (x, a)
  change_variables : ∀ ε hε hw, ∀ f g : M → ℝ≥0∞, Measurable f → Measurable g →
    ∀ a : cube (ι := ι) ε,
    (∫⁻ x, g x * (ENNReal.ofReal (weight ε (x, a)) *
      K.indicator f ((geometry ε hε hw).actualMap (x, a))) ∂σ.restrict K) =
      ∫⁻ x, f x * (ENNReal.ofReal (SubtypeKernel.zeroExtend K w x / R) *
        K.indicator g (F.family ε a.val x)) ∂σ.restrict K

namespace InverseDensityOrdinarySources
variable {F : Maps (E := E) (ι := ι) T r} {σ : Measure M}
  {V K G : Set M} {w : K → ℝ} {R : ℝ}

omit [FiniteDimensional ℝ E] in
theorem eventually_fixed_inputs
    (d : InverseDensityOrdinarySources F σ V K G w R)
    [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
    (source : ControlSubmersionSources (E := E) (ι := ι) σ)
    (hK : IsCompact K) (hV : IsOpen V) (hG : IsOpen G) (hVK : V ⊆ K)
    (hcoreV : isolatedCore T K ⊆ V) (hcoreG : isolatedCore T K ⊆ G)
    (hwt : Measurable w) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), ∀ (L : Laws (ι := ι)), ∀ (hε : 0 < ε) (hw : ε ≤ F.window),
      Nonempty (Global.NoFullSupportCollarDensityCertificate.Inputs T V K G hK (L.fixedLaw ε)
        (fun z : M × FixedControl (ι := ι) => F.fixedMap ε z.1 z.2)
        (F.fixedMap_measurable ε hε hw) w hwt R η) := by
  obtain ⟨ε₀, hε₀, inverse_close⟩ := F.inverse_closeness_threshold η hη
  have he : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, (ε : ℝ) < ε₀ :=
    ((NNReal.continuous_coe.tendsto (0 : ℝ≥0)).mono_left nhdsWithin_le_nhds).eventually
      (gt_mem_nhds hε₀)
  have hp : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ε < d.window :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds d.window_positive)
  filter_upwards [he, hp] with ε he hd L hε hw
  obtain ⟨B, hB, hb⟩ := d.bounded_weight ε hε hd.le
  obtain ⟨c⟩ := F.inverse_density_inputs L σ source ε hε hw V K G hK hV hG hVK hcoreV hcoreG
    (d.geometry ε hε hd.le) η (fun x _ a => inverse_close ε hε hw he V G (d.geometry ε hε hd.le) x a)
    w hwt R hR hwR (d.weight ε) (d.measurable_weight ε hε hd.le) (d.nonnegative_weight ε hε hd.le)
    (d.continuous_weight ε hε hd.le) B hB hb (d.positive_weight ε hε hd.le) (d.change_variables ε hε hd.le)
  exact ⟨F.fixed_density_inputs L ε hε hw V K G hK w hwt R η c⟩

end InverseDensityOrdinarySources
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
