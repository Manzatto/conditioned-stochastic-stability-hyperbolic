module
public import LeanShared.Geometry.FiniteSmoothReferenceLocalMeasure
public import LeanShared.Geometry.FiniteSmoothReferenceDensityRegularity
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Literal integration in each chart of the constructed smooth reference. -/
public noncomputable section
open Set MeasureTheory IsManifold
open scoped Manifold ContDiff ENNReal
namespace LeanShared.FiniteSmoothReferenceCharts.Data
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]

set_option maxHeartbeats 800000 in
theorem integral_chart (d : Data (E := E) (M := M))
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (c : OpenPartialHomeomorph M E) (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (f : M → ℂ) (continuous : Continuous f) :
    ∫ x in c.source, f x ∂d.measure μ =
      ∫ y in c.target, (d.localDensity c y : ℂ) * f (c.symm y) ∂μ := by
  have measurableC := c.continuousOn.aemeasurable
    (μ := d.measure μ) c.open_source.measurableSet
  have continuousG : ContinuousOn (fun y => f (c.symm y)) c.target :=
    continuous.comp_continuousOn c.symm.continuousOn
  have measurableG := continuousG.aestronglyMeasurable c.open_target.measurableSet
    (μ := μ)
  have mapG : AEStronglyMeasurable (fun y => f (c.symm y))
      (((d.measure μ).restrict c.source).map c) := by
    rw [d.local_measure μ c hc]
    exact measurableG.mono_ac (withDensity_absolutelyContinuous _ _)
  have mapIntegral := integral_map measurableC mapG
  have density := ((d.localDensity_contDiffOn c hc).continuousOn.aemeasurable
    c.open_target.measurableSet (μ := μ)).ennreal_ofReal
  calc
    ∫ x in c.source, f x ∂d.measure μ =
        ∫ x in c.source, f (c.symm (c x)) ∂d.measure μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem c.open_source.measurableSet] with x hx
      rw [c.left_inv hx]
    _ = ∫ y, f (c.symm y) ∂(((d.measure μ).restrict c.source).map c) := mapIntegral.symm
    _ = ∫ y in c.target, (d.localDensity c y : ℂ) * f (c.symm y) ∂μ := by
      rw [d.local_measure μ c hc,
        integral_withDensity_eq_integral_toReal_smul₀ density (by
          filter_upwards [] with y
          exact ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [ENNReal.toReal_ofReal (d.localDensity_nonnegative c y)]
      rfl

end LeanShared.FiniteSmoothReferenceCharts.Data
