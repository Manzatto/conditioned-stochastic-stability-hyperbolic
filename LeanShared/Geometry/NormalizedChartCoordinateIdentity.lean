module
public import LeanShared.Geometry.ContinuousCenteredFrameCharts
public import LeanShared.Analysis.CenteredFrameDerivative

/-! A literal centered map is exactly the coordinate expression in the
constructed normalized partial charts, including their actual inverses. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.ContinuousCenteredFrameCharts
variable {E P M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]

theorem normalized_coordinate_eq (c d p q : M)
    (hp : p ∈ (chartAt E c).source) (hq : q ∈ (chartAt E d).source)
    (A : P ≃L[ℝ] TangentSpace (𝓘(ℝ,E)) p)
    (B : P ≃L[ℝ] TangentSpace (𝓘(ℝ,E)) q) (f : M → M) :
    normalizedChart d q hq B ∘ f ∘ (normalizedChart c p hp A).symm =
      CenteredManifoldCoordinates.centered (chartFrame c p hp A) (chartFrame d q hq B)
        ((chartAt E c) p) ((chartAt E d) q)
        (chartAt E d ∘ f ∘ (chartAt E c).symm) := by
  funext z
  rfl

end LeanShared.ContinuousCenteredFrameCharts
