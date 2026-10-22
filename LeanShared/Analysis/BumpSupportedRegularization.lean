module
public import LeanShared.Analysis.BumpHolderRegularization
public import Mathlib.Topology.MetricSpace.Thickening

/-! Actual smooth bounded convolution, with an internally proved norm bound
and support propagation. Compactly supported inputs stay in the EXACT
prescribed open region once the bump radius is sufficiently small. -/
public noncomputable section
open MeasureTheory Filter Set ContinuousLinearMap Metric
open scoped Topology Convolution BoundedContinuousFunction ContDiff
namespace LeanShared.BumpSupportedRegularization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure] (φ : ContDiffBump (0 : E))

@[expose] def function (f : E →ᵇ ℂ) : E → ℂ :=
  φ.normed μ ⋆[lsmul ℝ ℝ, μ] (fun y => f y)

theorem smooth (f : E →ᵇ ℂ) : ContDiff ℝ ∞ (function μ φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed f.continuous.locallyIntegrable

theorem norm_bound (f : E →ᵇ ℂ) (x : E) : ‖function μ φ f x‖ ≤ ‖f‖ := by
  rw [function, ← BumpHolderRegularization.average_eq μ φ f x]
  simpa [TranslationHolderAverage.average] using
    norm_integral_le_of_norm_le_const (μ := BumpHolderRegularization.law μ φ)
      (f := fun w => f (x - w)) (C := ‖f‖)
      (Eventually.of_forall fun w => f.norm_coe_le_norm (x - w))

/-- Literal BCF realization; its bound is proved from probability mass one. -/
@[expose] def bounded (f : E →ᵇ ℂ) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (function μ φ f)
    (smooth μ φ f).continuous ‖f‖ (norm_bound μ φ f)

/-- The closed support expands only by the actual mollifier radius. -/
theorem support_subset (f : E →ᵇ ℂ) :
    tsupport (function μ φ f) ⊆ cthickening φ.rOut (tsupport f) := by
  apply closure_minimal ?_ isClosed_cthickening
  intro x hx
  obtain ⟨u, hu, v, hv, rfl⟩ := support_convolution_subset_swap (lsmul ℝ ℝ) hx
  have hv' : ‖v‖ < φ.rOut := by
    have hball : v ∈ ball (0 : E) φ.rOut := by
      rw [← φ.support_normed_eq (μ := μ)]
      exact hv
    simpa only [mem_ball, dist_zero_right] using hball
  apply mem_cthickening_of_dist_le (u + v) u φ.rOut (tsupport f) (subset_tsupport f hu)
  simpa only [dist_eq_norm, add_sub_cancel_left] using hv'.le

/-- Exact open-region support is retained; no enlargement of V occurs in
this conclusion. The safety radius follows from compactness and openness. -/
theorem exists_support_radius (f : E →ᵇ ℂ) (hc : HasCompactSupport f)
    {V : Set E} (hV : IsOpen V) (hf : tsupport f ⊆ V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ψ : ContDiffBump (0 : E), ψ.rOut ≤ δ →
      tsupport (function μ ψ f) ⊆ V := by
  obtain ⟨δ, hδ, hδV⟩ := hc.exists_cthickening_subset_open hV hf
  refine ⟨δ, hδ, fun ψ hψ => ?_⟩
  exact (support_subset μ ψ f).trans ((cthickening_mono hψ _).trans hδV)
end LeanShared.BumpSupportedRegularization
