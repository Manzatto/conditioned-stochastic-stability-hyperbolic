module

public import LeanShared.MeasureTheory.UniformLinearHaarUpperBound

/-! Uniform forward bounds on the actual coordinate frames give upper volume
comparison with a single fixed Haar normalization. -/
public noncomputable section
namespace LeanShared.UniformCoordinateHaarUpperBound
open Set MeasureTheory MeasureTheory.Measure
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace P] [BorelSpace P]

theorem exists_bound (μ : Measure E) [IsAddHaarMeasure μ] (L₀ : P ≃L[ℝ] E) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : P ≃L[ℝ] E, ‖L.toContinuousLinearMap‖ ≤ M →
      ∀ s : Set P, MeasurableSet s → μ (L '' s) ≤ ENNReal.ofReal C * (μ.map L₀.symm) s := by
  obtain ⟨C, positive, estimate⟩ := UniformLinearHaarUpperBound.exists_bound μ
    (M * ‖L₀.symm.toContinuousLinearMap‖)
  refine ⟨C, positive, fun L forward s hs => ?_⟩
  let F : E ≃L[ℝ] E := L₀.symm.trans L
  have forwardBound : ‖F.toContinuousLinearMap‖ ≤ M * ‖L₀.symm.toContinuousLinearMap‖ :=
    (ContinuousLinearMap.opNorm_comp_le L.toContinuousLinearMap L₀.symm.toContinuousLinearMap).trans
      (mul_le_mul_of_nonneg_right forward (norm_nonneg _))
  have bound := estimate F forwardBound (L₀ '' s)
  have images : F '' (L₀ '' s) = L '' s := by
    rw [Set.image_image]
    congr 1
    funext x
    exact congrArg L (L₀.symm_apply_apply x)
  rw [images] at bound
  have preimage : L₀.symm ⁻¹' s = L₀ '' s := by
    ext x
    constructor
    · intro hx
      exact ⟨L₀.symm x, hx, L₀.apply_symm_apply x⟩
    · rintro ⟨x, hx, rfl⟩
      simpa only [Set.mem_preimage, L₀.symm_apply_apply] using hx
  rw [Measure.map_apply L₀.symm.continuous.measurable hs, preimage]
  exact bound

end LeanShared.UniformCoordinateHaarUpperBound
