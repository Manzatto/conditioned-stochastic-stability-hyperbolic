module
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Forward operator bounds give uniform upper Haar-volume bounds. -/
public noncomputable section
namespace LeanShared.UniformLinearHaarUpperBound
open Set MeasureTheory MeasureTheory.Measure Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem exists_bound (μ : Measure E) [IsAddHaarMeasure μ] (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : E ≃L[ℝ] E, ‖F.toContinuousLinearMap‖ ≤ M →
      ∀ s : Set E, μ (F '' s) ≤ ENNReal.ofReal C * μ s := by
  obtain ⟨D, bound⟩ := (isCompact_closedBall (0 : E →L[ℝ] E) M).exists_bound_of_continuousOn
    ContinuousLinearMap.continuous_det.continuousOn
  refine ⟨max 1 D, zero_lt_one.trans_le (le_max_left _ _), fun F hF s => ?_⟩
  have determinant : |F.toContinuousLinearMap.det| ≤ max 1 D := by
    have member : F.toContinuousLinearMap ∈ closedBall (0 : E →L[ℝ] E) M := by
      simpa only [mem_closedBall, dist_zero_right] using hF
    simpa only [Real.norm_eq_abs] using (bound _ member).trans (le_max_right _ _)
  have formula := addHaar_image_linearMap μ F.toLinearMap s
  exact formula.trans_le (mul_le_mul' (ENNReal.ofReal_le_ofReal determinant) le_rfl)

end LeanShared.UniformLinearHaarUpperBound
