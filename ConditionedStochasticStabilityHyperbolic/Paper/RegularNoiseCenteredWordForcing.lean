module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseUniformChartWords
public import LeanShared.Geometry.CenteredManifoldCoordinates
public import Mathlib.Tactic.FieldSimp

/-! After the local contraction radius has been fixed, the actual centered
forcing can be made independently small by shrinking only the noise window.
This avoids a circular choice of radius and forcing tolerance. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold
open scoped Topology Manifold ContDiff NNReal
open LeanShared.FiniteJetComposition LeanShared.CenteredManifoldCoordinates

theorem Maps.centered_word_forcing_window
    {E M ι P Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
    (hd : d ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) (N : ℕ)
    (K : Set E) (compact : IsCompact K)
    (inside : K ⊆ c.target ∩ ((T : M → M)^[N] ∘ c.symm) ⁻¹' d.source)
    (C θ : ℝ) (positiveC : 0 < C) (positiveθ : 0 < θ) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ η →
      ∀ controls : ℕ → cube (ι := ι) ε, ∀ a ∈ K,
      ∀ (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] E), ‖R.symm.toContinuousLinearMap‖ ≤ C →
      let f := d ∘ word (fun n => F.family ε (controls n).val) N ∘ c.symm
      let g := d ∘ (T : M → M)^[N] ∘ c.symm
      ‖centered L R a (g a) f 0‖ ≤ θ := by
  obtain ⟨η, positiveη, bounds⟩ := F.uniform_chart_word_jets regularity deterministic c d hc hd
    N K compact inside (θ / C) (div_pos positiveθ positiveC)
  refine ⟨η, positiveη, fun ε hp hw controls a ha L R boundR => ?_⟩
  have values := (le_add_of_nonneg_right (norm_nonneg _)).trans (bounds ε hp hw controls a ha)
  change ‖R.symm ((d ∘ word (fun n => F.family ε (controls n).val) N ∘ c.symm)
    (a + L 0) - (d ∘ (T : M → M)^[N] ∘ c.symm) a)‖ ≤ θ
  rw [_root_.map_zero, add_zero]
  calc
    _ ≤ ‖R.symm.toContinuousLinearMap‖ * ‖(d ∘ word (fun n => F.family ε (controls n).val) N ∘ c.symm) a -
        (d ∘ (T : M → M)^[N] ∘ c.symm) a‖ := R.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ C * (θ / C) := mul_le_mul boundR values (norm_nonneg _) positiveC.le
    _ = θ := by field_simp

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
