module
public import LeanShared.Geometry.SupportedChartExtension
public import LeanShared.Geometry.LinearRechartedIdentity

/-! A supported smooth input in the genuine recharted Fourier model
decodes to a smooth function on the original normed-model manifold. The
points and function are unchanged; smoothness follows through the actual
identity diffeomorphism, without an inner product on the original model. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.SupportedChartExtension
variable {E Z M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [T2Space M]

theorem smooth_linearRechart (e : E ≃L[ℝ] Z) (c : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) {f : Z → ℂ}
    (smooth : ContDiff ℝ ∞ f) (compact : HasCompactSupport f)
    (support : tsupport f ⊆ (LinearRechartedManifold.chartImage e c).target) :
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞
      (function (LinearRechartedManifold.chartImage e c) f) := by
  let := LinearRechartedManifold.charts (M := M) e
  let := LinearRechartedManifold.manifold (M := M) e
  have chart := LinearRechartedManifold.chartImage_mem_maximal e c hc
  have decoded := SupportedChartExtension.smooth
    (LinearRechartedManifold.chartImage e c) chart smooth compact support
  exact decoded.comp (LinearRechartedManifold.identity_forward (M := M) e)

end LeanShared.SupportedChartExtension
