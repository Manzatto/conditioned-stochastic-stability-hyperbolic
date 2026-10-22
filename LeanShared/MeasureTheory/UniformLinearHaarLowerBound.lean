module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Uniform inverse operator bounds give an actual uniform lower Haar
volume bound for every coordinate equivalence. -/
public noncomputable section
namespace LeanShared.UniformLinearHaarLowerBound
open Set MeasureTheory MeasureTheory.Measure Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem exists_bound (μ : Measure E) [IsAddHaarMeasure μ] (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : E ≃L[ℝ] E, ‖F.symm.toContinuousLinearMap‖ ≤ M →
      ∀ s : Set E, μ s ≤ ENNReal.ofReal C * μ (F '' s) := by
  obtain ⟨D, bound⟩ := (isCompact_closedBall (0 : E →L[ℝ] E) M).exists_bound_of_continuousOn
    ContinuousLinearMap.continuous_det.continuousOn
  refine ⟨max 1 D, (zero_lt_one.trans_le (le_max_left _ _)), fun F hF s => ?_⟩
  have determinant : |F.symm.toContinuousLinearMap.det| ≤ max 1 D := by
    have member : F.symm.toContinuousLinearMap ∈ closedBall (0 : E →L[ℝ] E) M := by
      simpa only [mem_closedBall, dist_zero_right] using hF
    simpa only [Real.norm_eq_abs] using (bound _ member).trans (le_max_right _ _)
  have image : F.symm.toLinearMap '' (F '' s) = s := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      change F.symm (F z) ∈ s
      rw [F.symm_apply_apply]
      exact hz
    · intro hx
      exact ⟨F x, ⟨x, hx, rfl⟩, F.symm_apply_apply x⟩
  have formula := addHaar_image_linearMap μ F.symm.toLinearMap (F '' s)
  rw [image] at formula
  calc
    μ s = ENNReal.ofReal |F.symm.toContinuousLinearMap.det| * μ (F '' s) := formula
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal determinant) le_rfl

end LeanShared.UniformLinearHaarLowerBound
