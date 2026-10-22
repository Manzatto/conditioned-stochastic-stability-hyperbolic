module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedChartDomains
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedForcing
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanCalculus
import Mathlib.Tactic.Linarith

/-! Actual partial-chart domains and origin forcing in the genuine
Euclidean adapted model. All conversion constants are explicit. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open LeanShared.CenteredManifoldCoordinates
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

theorem Maps.adapted_euclidean_domains {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
    {system : PatchSystem b} (atlas : ChartAtlas system) :
    ∃ radius > 0, ∃ η > 0, ∃ cutoff : ℝ≥0, 0 < cutoff ∧ cutoff ≤ F.window ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ cutoff → ∀ control : cube (ι := ι) ε,
      ∀ c ∈ atlas.centers, ∀ d ∈ atlas.centers,
      ∀ x (hx : x ∈ atlas.patch c), ∀ y, y ∈ atlas.patch d →
      dist (T x.val) y.val < η →
      let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
        (system.euclideanReferenceFrame c ⟨x, atlas.inside c hx⟩)
      ∀ z, ‖z‖ ≤ radius →
        (chartAt E c.val) x.val + L z ∈ (chartAt E c.val).target ∧
        F.family ε control.val ((chartAt E c.val).symm ((chartAt E c.val) x.val + L z)) ∈
          (chartAt E d.val).source := by
  obtain ⟨radius, positiveRadius, η, positiveη, cutoff, positiveCutoff, cap, estimates⟩ :=
    F.adapted_chart_domains atlas
  refine ⟨radius, positiveRadius, η, positiveη, cutoff, positiveCutoff, cap, ?_⟩
  intro ε hp hw control c hc d hd x hx y hy near
  dsimp only
  intro z small
  have inverseSmall : ‖system.euclideanEquiv.symm z‖ ≤ radius := by
    have bound := (system.euclideanEquiv.symm.toContinuousLinearMap.le_opNorm z).trans
      (mul_le_mul_of_nonneg_right system.euclideanEquiv_norm.2 (norm_nonneg z))
    have bound' : ‖system.euclideanEquiv.symm z‖ ≤ ‖z‖ := by
      simpa only [ContinuousLinearEquiv.coe_coe, one_mul] using bound
    exact bound'.trans small
  rw [system.euclidean_chartFrame c ⟨x, atlas.inside c hx⟩]
  exact estimates ε hp hw control c hc d hd x hx y hy near (system.euclideanEquiv.symm z) inverseSmall

theorem Maps.adapted_euclidean_forcing {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
    (regularity : 1 ≤ r) (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    {system : PatchSystem b} (atlas : ChartAtlas system) (τ : ℝ) (positiveτ : 0 < τ) :
    ∃ η > 0, ∃ cutoff : ℝ≥0, 0 < cutoff ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ cutoff → ∀ control : cube (ι := ι) ε,
      ∀ c ∈ atlas.centers, ∀ d ∈ atlas.centers,
      ∀ x (hx : x ∈ atlas.patch c), ∀ y (hy : y ∈ atlas.patch d),
      dist (T x.val) y.val < η →
      let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
        (system.euclideanReferenceFrame c ⟨x, atlas.inside c hx⟩)
      let R := ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
        (system.euclideanReferenceFrame d ⟨y, atlas.inside d hy⟩)
      ‖centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
        (chartAt E d.val ∘ F.family ε control.val ∘ (chartAt E c.val).symm) 0‖ < τ := by
  obtain ⟨η, positiveη, cutoff, positiveCutoff, estimates⟩ :=
    F.adapted_forcing_window regularity forward atlas (τ / 2) (half_pos positiveτ)
  refine ⟨η, positiveη, cutoff, positiveCutoff, ?_⟩
  intro ε hp hw control c hc d hd x hx y hy near
  have data := estimates ε hp hw control c hc d hd x hx y hy near
  dsimp only
  rw [system.euclidean_chartFrame c ⟨x, atlas.inside c hx⟩,
    system.euclidean_chartFrame d ⟨y, atlas.inside d hy⟩, system.centered_euclidean_eq]
  simp only [Function.comp_apply, _root_.map_zero]
  exact ((system.euclideanEquiv.toContinuousLinearMap.le_opNorm _).trans
    (mul_le_mul_of_nonneg_right system.euclideanEquiv_norm.1 (norm_nonneg _))).trans_lt
      (by linarith)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
