module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedChartWindow
public import LeanShared.Dynamics.HyperbolicAdaptedForcing
import Mathlib.Tactic.Linarith

/-! The literal noisy centered map has arbitrarily small origin offset.
This threshold can be chosen after fixing the derivative radius, so its
size may scale with that radius in the cutoff construction. -/
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

theorem Maps.adapted_forcing_window {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
    (regularity : 1 ≤ r) (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    {system : PatchSystem b} (atlas : ChartAtlas system) (τ : ℝ) (positiveτ : 0 < τ) :
    ∃ η > 0, ∃ cutoff : ℝ≥0, 0 < cutoff ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ cutoff → ∀ control : cube (ι := ι) ε,
      ∀ c ∈ atlas.centers, ∀ d ∈ atlas.centers,
      ∀ x (hx : x ∈ atlas.patch c), ∀ y (hy : y ∈ atlas.patch d),
      dist (T x.val) y.val < η →
      let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
        (system.referenceFrame c ⟨x, atlas.inside c hx⟩)
      let R := ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
        (system.referenceFrame d ⟨y, atlas.inside d hy⟩)
      ‖centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
        (chartAt E d.val ∘ F.family ε control.val ∘ (chartAt E c.val).symm) 0‖ < τ := by
  obtain ⟨radius, positiveRadius, η₀, positiveη₀, cutoff, positiveCutoff, noisy⟩ :=
    F.adapted_chart_noise_window regularity forward atlas (τ / 2) (half_pos positiveτ)
  obtain ⟨η₁, positiveη₁, reference⟩ := atlas.forcing_window (τ / 2) (half_pos positiveτ)
  refine ⟨min η₀ η₁, lt_min positiveη₀ positiveη₁, cutoff, positiveCutoff, ?_⟩
  intro ε hp hw control c hc d hd x hx y hy near
  have noiseBounds := noisy ε hp hw control c hc d hd x hx y hy
    (near.trans_le (min_le_left _ _)) 0 (by simpa only [norm_zero] using positiveRadius.le)
  have referenceBounds := reference c hc d hd x hx y hy (near.trans_le (min_le_right _ _))
  let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
    (system.referenceFrame c ⟨x, atlas.inside c hx⟩)
  let R := ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
    (system.referenceFrame d ⟨y, atlas.inside d hy⟩)
  let f := centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
    (chartAt E d.val ∘ F.family ε control.val ∘ (chartAt E c.val).symm)
  let g := centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
    (chartAt E d.val ∘ T ∘ (chartAt E c.val).symm)
  have difference : ‖f 0 - g 0‖ ≤ τ / 2 :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans noiseBounds.2
  have estimate := norm_le_norm_sub_add (f 0) (g 0)
  have referenceSmall : ‖g 0‖ < τ / 2 := referenceBounds.2
  change ‖f 0‖ < τ
  linarith

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
