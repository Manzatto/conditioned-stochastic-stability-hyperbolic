module

public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedFixedCubeNoise

/-! Every fixed geometric tolerance holds eventually for the literal
Whitney-close perturbation, before any control law is chosen. -/

@[expose] public noncomputable section
open Set Filter
open scoped Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M ι Parameters : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MetricSpace Parameters] {T : M ≃ₜ M} {r : ℝ}

omit [FiniteDimensional ℝ E] in
theorem Maps.eventually_uniform_close (F : Maps (E := E) (ι := ι) T r)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), 0 < ε ∧ ε ≤ F.window ∧
      ∀ x : M, ∀ z : FixedControl (ι := ι), dist (F.fixedMap ε x z) (T x) < δ := by
  have hmul : Tendsto (fun ε : ℝ≥0 => F.constant * (ε : ℝ)) (𝓝 0) (𝓝 0) := by
    simpa only [NNReal.coe_zero, mul_zero] using (NNReal.continuous_coe.tendsto (0 : ℝ≥0)).const_mul F.constant
  have hw : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), ε < F.window :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds F.window_positive)
  have hb : ∀ᶠ (ε : ℝ≥0) in 𝓝[>] (0 : ℝ≥0), F.constant * (ε : ℝ) < δ :=
    (hmul.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hδ)
  filter_upwards [self_mem_nhdsWithin, hw, hb] with ε he hw hb
  exact ⟨he, hw.le, fun x z => (F.fixedMap_uniform_close ε he hw.le x z).trans_lt hb⟩

omit [FiniteDimensional ℝ E] in
theorem Representation.eventually_parameters_close
    {F : Maps (E := E) (ι := ι) T r} {evaluate : Parameters → M → M}
    (p : Representation F Parameters evaluate) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), 0 < ε ∧ ε ≤ p.window ∧
      ∀ z : FixedControl (ι := ι), dist (p.fixedParameters ε z) p.reference < δ := by
  have hmul : Tendsto (fun ε : ℝ≥0 => p.constant * (ε : ℝ)) (𝓝 0) (𝓝 0) := by
    simpa only [NNReal.coe_zero, mul_zero] using (NNReal.continuous_coe.tendsto (0 : ℝ≥0)).const_mul p.constant
  have hw : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), ε < p.window :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds p.window_positive)
  have hb : ∀ᶠ (ε : ℝ≥0) in 𝓝[>] (0 : ℝ≥0), p.constant * (ε : ℝ) < δ :=
    (hmul.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hδ)
  filter_upwards [self_mem_nhdsWithin, hw, hb] with ε he hw hb
  exact ⟨he, hw.le, fun z => (p.fixedParameters_close ε z).trans_lt hb⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
