module
public import LeanShared.Geometry.FiniteSmoothReferenceJacobian
public import LeanShared.MeasureTheory.ContinuousDensityUniqueness
import all LeanShared.Geometry.FiniteSmoothReferencePushforwardDensity
import all LeanShared.Geometry.FiniteSmoothReferenceLocalDensity

/-! The computed global Jacobian has its actual density-ratio formula in
EVERY fixed smooth chart. No continuity of the chosen chartAt map is used. -/
public noncomputable section
namespace LeanShared.FiniteSmoothReferenceCharts
open Set MeasureTheory Measure IsManifold
open scoped Topology Manifold ContDiff ENNReal

set_option maxHeartbeats 2400000 in
theorem Data.jacobian_eq_chart_ratio
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (d : Data (E := E) (M := M)) (μ : Measure E) [IsAddHaarMeasure μ]
    (H : M ≃ₜ M) (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 H)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 H.symm)
    (c : OpenPartialHomeomorph M E) (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) :
    EqOn (d.jacobian H)
      (fun x => d.pushforwardDensity H c (c x) / d.localDensity c (c x)) c.source := by
  have global := d.jacobian_continuous_positive_map μ H forward inverse
  have measurableP : Measurable (d.localDensity c) := by
    apply Finset.measurable_sum
    intro i _
    exact CoordinateJacobianDensity.measurable _ _ _
      (transition_regular _ _ (chart_mem_maximalAtlas i) hc)
      (d.smooth i).continuous (d.compact_support i) (d.support i)
  have measurableQ : Measurable (d.pushforwardDensity H c) := by
    apply Finset.measurable_sum
    intro i _
    exact CoordinateJacobianDensity.measurable _ _ _
      (transported_regular d H inverse i _ hc)
      (d.smooth i).continuous (d.compact_support i) (d.support i)
  have continuousRatio := ((d.pushforwardDensity_continuousOn H inverse c hc).comp
    c.continuousOn (fun _ hy => c.map_source hy)).div
    ((d.localDensity_continuousOn c hc).comp c.continuousOn (fun _ hy => c.map_source hy))
    (fun y hy => (d.localDensity_positive c hc _ (c.map_source hy)).ne')
  have positiveRatio (x : M) (hx : x ∈ c.source) :
      0 < d.pushforwardDensity H c (c x) / d.localDensity c (c x) :=
    div_pos (d.pushforwardDensity_positive H (forward.mdifferentiable (by norm_num))
      (inverse.mdifferentiable (by norm_num)) c hc _ (c.map_source hx))
      (d.localDensity_positive c hc _ (c.map_source hx))
  have localLaw := CoordinateDensityRatio.local_law c μ (d.measure μ) ((d.measure μ).map H)
    (d.localDensity c) (d.pushforwardDensity H c) measurableP measurableQ
    (fun y hy => d.localDensity_positive c hc y hy)
    (d.local_measure μ c hc) (d.pushforward_local_measure μ H inverse c hc)
  apply ContinuousDensityUniqueness.eqOn (d.measure μ) c.source c.open_source
    _ _ global.1.continuousOn continuousRatio
    (fun x _ => (global.2.1 x).le) (fun x hx => (positiveRatio x hx).le)
  change ((d.measure μ).restrict c.source).withDensity (fun x => ENNReal.ofReal (d.jacobian H x)) =
    ((d.measure μ).restrict c.source).withDensity (fun x => ENNReal.ofReal
      (d.pushforwardDensity H c (c x) / d.localDensity c (c x)))
  rw [← localLaw, global.2.2, restrict_withDensity c.open_source.measurableSet]

end LeanShared.FiniteSmoothReferenceCharts
