module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseArbitraryWordCharts
public import LeanShared.Analysis.JetUniformOnCompact
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Uniform actual N-step Whitney estimates in arbitrary fixed chart pairs,
including a whole positive coordinate tube around any valid compact set. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold
open scoped Topology Manifold ContDiff NNReal
open LeanShared.FiniteJetComposition

theorem Maps.uniform_chart_word_jets
    {E M ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
    (hd : d ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) (N : ℕ)
    (K : Set E) (compact : IsCompact K)
    (inside : K ⊆ c.target ∩ ((T : M → M)^[N] ∘ c.symm) ⁻¹' d.source)
    (δ : ℝ) (positive : 0 < δ) :
    let g := d ∘ (T : M → M)^[N] ∘ c.symm
    ∃ η : ℝ≥0, 0 < η ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ η →
      ∀ controls : ℕ → cube (ι := ι) ε, ∀ x ∈ K,
      let f := d ∘ word (fun n => F.family ε (controls n).val) N ∘ c.symm
      ‖f x - g x‖ + ‖fderiv ℝ f x - fderiv ℝ g x‖ ≤ δ := by
  apply uniform_on_compact (fun ε => ℕ → cube (ι := ι) ε) _ _
    (c.target ∩ ((T : M → M)^[N] ∘ c.symm) ⁻¹' d.source) K compact inside
  · intro x hx
    have first : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 c.symm x :=
      (contMDiffAt_symm_of_mem_maximalAtlas hc hx.1).of_le (by simp)
    have last : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 d ((T : M → M)^[N] (c.symm x)) :=
      (contMDiffAt_of_mem_maximalAtlas hd hx.2).of_le (by simp)
    exact (last.comp x ((deterministic.iterate N).contMDiffAt.comp x first)).contDiffAt
  · intro ε controls limit pos
    exact F.actual_word_jets_in_charts regularity deterministic ε
      (fun n a => controls a n) atTop limit (Eventually.of_forall pos) c d hc hd N
  · exact positive

theorem Maps.uniform_chart_word_tube
    {E M ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
    (hd : d ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) (N : ℕ)
    (K : Set E) (compact : IsCompact K)
    (inside : K ⊆ c.target ∩ ((T : M → M)^[N] ∘ c.symm) ⁻¹' d.source)
    (δ : ℝ) (positive : 0 < δ) :
    ∃ radius : ℝ, 0 < radius ∧ ∃ η : ℝ≥0, 0 < η ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ η → ∀ controls : ℕ → cube (ι := ι) ε,
      ∀ x ∈ K, ∀ y : E, dist y x ≤ radius →
      let f := d ∘ word (fun n => F.family ε (controls n).val) N ∘ c.symm
      let g := d ∘ (T : M → M)^[N] ∘ c.symm
      ‖f y - g y‖ + ‖fderiv ℝ f y - fderiv ℝ g y‖ ≤ δ := by
  have openDomain : IsOpen (c.target ∩ ((T : M → M)^[N] ∘ c.symm) ⁻¹' d.source) :=
    ((T.continuous.iterate N).comp_continuousOn c.symm.continuousOn).isOpen_inter_preimage
      c.open_target d.open_source
  obtain ⟨radius, positiveRadius, contained⟩ := compact.exists_cthickening_subset_open openDomain inside
  obtain ⟨η, positiveη, estimates⟩ := F.uniform_chart_word_jets regularity deterministic
    c d hc hd N (Metric.cthickening radius K) compact.cthickening contained δ positive
  refine ⟨radius, positiveRadius, η, positiveη, fun ε hp hw controls x hx y hxy => ?_⟩
  exact estimates ε hp hw controls y (Metric.mem_cthickening_of_dist_le y x radius K hx hxy)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
