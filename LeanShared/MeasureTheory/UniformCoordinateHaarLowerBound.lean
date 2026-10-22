module

public import LeanShared.MeasureTheory.UniformLinearHaarLowerBound

/-! Varying finite-dimensional coordinate frames with uniformly bounded
inverses preserve one fixed positive Haar-volume normalization uniformly. -/
public noncomputable section
namespace LeanShared.UniformCoordinateHaarLowerBound
open Set MeasureTheory MeasureTheory.Measure
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace P] [BorelSpace P]

theorem exists_bound (μ : Measure E) [IsAddHaarMeasure μ] (L₀ : P ≃L[ℝ] E) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : P ≃L[ℝ] E, ‖L.symm.toContinuousLinearMap‖ ≤ M →
      ∀ s : Set P, MeasurableSet s → (μ.map L₀.symm) s ≤ ENNReal.ofReal C * μ (L '' s) := by
  obtain ⟨C, positive, estimate⟩ := UniformLinearHaarLowerBound.exists_bound μ
    (‖L₀.toContinuousLinearMap‖ * M)
  refine ⟨C, positive, fun L inverse s hs => ?_⟩
  let F : E ≃L[ℝ] E := L₀.symm.trans L
  have inverseBound : ‖F.symm.toContinuousLinearMap‖ ≤ ‖L₀.toContinuousLinearMap‖ * M :=
    (ContinuousLinearMap.opNorm_comp_le L₀.toContinuousLinearMap L.symm.toContinuousLinearMap).trans
      (mul_le_mul_of_nonneg_left inverse (norm_nonneg _))
  have bound := estimate F inverseBound (L₀ '' s)
  have images : F '' (L₀ '' s) = L '' s := by
    rw [Set.image_image]
    congr 1
    funext x
    change L (L₀.symm (L₀ x)) = L x
    rw [L₀.symm_apply_apply]
  rw [images] at bound
  have preimage : L₀.symm ⁻¹' s = L₀ '' s := by
    ext x
    constructor
    · intro hx
      exact ⟨L₀.symm x, hx, L₀.apply_symm_apply x⟩
    · rintro ⟨x, hx, rfl⟩
      change L₀.symm (L₀ x) ∈ s
      rw [L₀.symm_apply_apply]
      exact hx
  rw [Measure.map_apply L₀.symm.continuous.measurable hs, preimage]
  exact bound

end LeanShared.UniformCoordinateHaarLowerBound
