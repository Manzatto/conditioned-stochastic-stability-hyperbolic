module
public import LeanShared.Geometry.RiemannianInverseChartPairBound

/-! The inverse extended chart is genuinely locally Lipschitz for the
bounded Riemannian length metric, with both endpoints varying. -/
public noncomputable section
namespace LeanShared.BoundedRiemannianMetric
open Set Manifold Metric Bundle
open scoped Topology Manifold ContDiff Bundle ENNReal NNReal

set_option maxHeartbeats 1600000 in
theorem inverse_chart_local_lipschitz
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [T3Space M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) 1 M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    (x : M) :
    let _ : MetricSpace M := metric (E := E)
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ≥0, 0 < C ∧
      ball (extChartAt (𝓘(ℝ,E)) x x) r ⊆ (extChartAt (𝓘(ℝ,E)) x).target ∧
      ∀ y ∈ ball (extChartAt (𝓘(ℝ,E)) x x) r,
      ∀ z ∈ ball (extChartAt (𝓘(ℝ,E)) x x) r,
      dist ((extChartAt (𝓘(ℝ,E)) x).symm y) ((extChartAt (𝓘(ℝ,E)) x).symm z) ≤ C*dist y z := by
  let _ : MetricSpace M := metric (E := E)
  obtain ⟨r,hr,C,hC,safe,bound⟩ := inverse_chart_pair_bound (E := E) x
  refine ⟨r,hr,C,hC,safe,fun y hy z hz => ?_⟩
  have estimate : edist ((extChartAt (𝓘(ℝ,E)) x).symm y)
      ((extChartAt (𝓘(ℝ,E)) x).symm z) ≤ C*edist y z := by
    rw [metric_edist]
    exact (min_le_left _ _).trans (bound y hy z hz)
  have realBound := ENNReal.toReal_mono (by finiteness) estimate
  simpa only [ENNReal.toReal_mul,ENNReal.coe_toReal,edist_dist,ENNReal.toReal_ofReal dist_nonneg] using realBound

end LeanShared.BoundedRiemannianMetric
