module
public import LeanShared.Geometry.FiniteSmoothReferencePushforwardDensity
public import LeanShared.Geometry.FiniteSmoothReferenceLocalMeasure
public import LeanShared.Geometry.FiniteSmoothReferenceSupport
public import LeanShared.MeasureTheory.CoordinateDensityRatio
public import LeanShared.MeasureTheory.ContinuousDensityGluing
import all LeanShared.Geometry.FiniteSmoothReferencePushforwardDensity
import all LeanShared.Geometry.FiniteSmoothReferenceLocalDensity

/-! A genuine C1 diffeomorphism has an explicitly constructed positive
continuous Jacobian for the actual finite smooth reference measure. Its
change-of-variables law is proved, not a source field. -/
public noncomputable section
namespace LeanShared.FiniteSmoothReferenceCharts
open Set MeasureTheory Measure IsManifold
open scoped Topology Manifold ContDiff ENNReal

@[expose] def Data.jacobian
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (d : Data (E := E) (M := M)) (H : M ≃ₜ M) (x : M) : ℝ :=
  d.pushforwardDensity H (chartAt E x) (chartAt E x x) /
    d.localDensity (chartAt E x) (chartAt E x x)

set_option maxHeartbeats 2400000 in
theorem Data.jacobian_continuous_positive_map
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (d : Data (E := E) (M := M)) (μ : Measure E) [IsAddHaarMeasure μ]
    (H : M ≃ₜ M) (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 H)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 H.symm) :
    Continuous (d.jacobian H) ∧ (∀ x, 0 < d.jacobian H x) ∧
      (d.measure μ).map H = (d.measure μ).withDensity (fun x => ENNReal.ofReal (d.jacobian H x)) := by
  let U := fun x : M => (chartAt E x).source
  let p := fun x : M => d.localDensity (chartAt E x)
  let q := fun x : M => d.pushforwardDensity H (chartAt E x)
  let f := fun x y : M => q x (chartAt E x y) / p x (chartAt E x y)
  have measurableP (x : M) : Measurable (p x) := by
    apply Finset.measurable_sum
    intro i _
    exact CoordinateJacobianDensity.measurable _ _ _
      (transition_regular _ _ (chart_mem_maximalAtlas i) (chart_mem_maximalAtlas x))
      (d.smooth i).continuous (d.compact_support i) (d.support i)
  have measurableQ (x : M) : Measurable (q x) := by
    apply Finset.measurable_sum
    intro i _
    exact CoordinateJacobianDensity.measurable _ _ _
      (transported_regular d H inverse i _ (chart_mem_maximalAtlas x))
      (d.smooth i).continuous (d.compact_support i) (d.support i)
  have continuousF (x : M) : ContinuousOn (f x) (U x) := by
    have numerator := (d.pushforwardDensity_continuousOn H inverse _ (chart_mem_maximalAtlas x)).comp
      (chartAt E x).continuousOn (fun _ hy => (chartAt E x).map_source hy)
    have denominator := (d.localDensity_continuousOn _ (chart_mem_maximalAtlas x)).comp
      (chartAt E x).continuousOn (fun _ hy => (chartAt E x).map_source hy)
    exact numerator.div denominator (fun y hy =>
      (d.localDensity_positive _ (chart_mem_maximalAtlas x) _ ((chartAt E x).map_source hy)).ne')
  have positiveF (x : M) (y : M) (hy : y ∈ U x) : 0 < f x y :=
    div_pos
      (d.pushforwardDensity_positive H (forward.mdifferentiable (by norm_num))
        (inverse.mdifferentiable (by norm_num)) _ (chart_mem_maximalAtlas x) _ ((chartAt E x).map_source hy))
      (d.localDensity_positive _ (chart_mem_maximalAtlas x) _ ((chartAt E x).map_source hy))
  have localLaw (x : M) : ((d.measure μ).map H).restrict (U x) =
      ((d.measure μ).restrict (U x)).withDensity (fun y => ENNReal.ofReal (f x y)) := by
    exact CoordinateDensityRatio.local_law (chartAt E x) μ (d.measure μ) ((d.measure μ).map H)
      (p x) (q x) (measurableP x) (measurableQ x)
      (fun y hy => d.localDensity_positive _ (chart_mem_maximalAtlas x) y hy)
      (d.local_measure μ _ (chart_mem_maximalAtlas x))
      (d.pushforward_local_measure μ H inverse _ (chart_mem_maximalAtlas x))
  obtain ⟨g,continuousG,positiveG,law,same⟩ := ContinuousDensityGluing.exists_density
    (d.measure μ) ((d.measure μ).map H) U (fun x => (chartAt E x).open_source)
    (fun x => mem_chart_source E x) f continuousF positiveF localLaw
  have eq : g = d.jacobian H := funext (fun x => same x (mem_chart_source E x))
  rw [eq] at continuousG positiveG law
  exact ⟨continuousG,positiveG,law⟩

end LeanShared.FiniteSmoothReferenceCharts
