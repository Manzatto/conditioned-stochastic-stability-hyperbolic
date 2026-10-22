module

public import LeanShared.Geometry.BoundedRiemannianMetric

/-! The constructed bounded Riemannian length metric has diameter at most
one, including points in different connected components. -/
public section
namespace LeanShared.BoundedRiemannianMetric
open Bundle
open scoped Manifold ContDiff ENNReal
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [T3Space M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) 1 M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

theorem dist_le_one (x y : M) :
    let _ : MetricSpace M := metric (E := E)
    dist x y ≤ 1 := by
  let _ : MetricSpace M := metric (E := E)
  have bound : edist x y ≤ 1 := by rw [metric_edist]; exact min_le_right _ _
  have realBound := ENNReal.toReal_mono (by simp) bound
  simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg, ENNReal.toReal_one] using realBound

end LeanShared.BoundedRiemannianMetric
