module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseArbitraryWordCharts
public import LeanShared.Analysis.JetUniformDifferentiability

/-! A common positive window of genuine differentiability for the actual
finite noisy coordinate word, uniformly over controls and compact centers. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold
open scoped Topology Manifold ContDiff NNReal
open LeanShared.FiniteJetComposition

theorem Maps.uniformly_differentiable_chart_words
    {E M ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
    (hd : d ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) (N : ℕ)
    (K : Set E) (compact : IsCompact K)
    (inside : K ⊆ c.target ∩ ((T : M → M)^[N] ∘ c.symm) ⁻¹' d.source) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ η →
      ∀ controls : ℕ → cube (ι := ι) ε, ∀ x ∈ K,
      DifferentiableAt ℝ
        (d ∘ word (fun n => F.family ε (controls n).val) N ∘ c.symm) x := by
  apply uniformly_differentiable_on_compact (fun ε => ℕ → cube (ι := ι) ε) _
    (d ∘ (T : M → M)^[N] ∘ c.symm)
    (c.target ∩ ((T : M → M)^[N] ∘ c.symm) ⁻¹' d.source) K compact inside
  intro ε controls limit positive
  exact F.actual_word_jets_in_charts regularity deterministic ε
    (fun n a => controls a n) atTop limit (Eventually.of_forall positive) c d hc hd N

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
