module
public import LeanShared.Geometry.NormalizedChartLinearRechart

/-! Pulling the actual tangent frame back along a fixed linear model
change gives an original-model normalized chart whose chart image is
exactly the desired normalized chart, including its partial inverse. -/
@[expose] public noncomputable section
open IsManifold
open scoped Manifold ContDiff
namespace LeanShared.ContinuousCenteredFrameCharts
variable {E P M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]

theorem chartFrame_pullback (e : E ≃L[ℝ] P) (center p : M)
    (inside : p ∈ (chartAt E center).source)
    (A : P ≃L[ℝ] TangentSpace (𝓘(ℝ,E)) p) :
    chartFrame center p inside (e.trans A) = e.trans (chartFrame center p inside A) := by
  apply ContinuousLinearEquiv.ext
  funext v
  rfl

theorem normalizedChart_chartImage (e : E ≃L[ℝ] P) (center p : M)
    (inside : p ∈ (chartAt E center).source)
    (A : P ≃L[ℝ] TangentSpace (𝓘(ℝ,E)) p) :
    LinearRechartedManifold.chartImage e (normalizedChart center p inside (e.trans A)) =
      normalizedChart center p inside A := by
  unfold normalizedChart
  rw [chartFrame_pullback]
  exact NormalizedChartLinearRechart.affine_chartImage e (chartAt E center)
    (chartFrame center p inside A) ((chartAt E center) p)

end LeanShared.ContinuousCenteredFrameCharts
