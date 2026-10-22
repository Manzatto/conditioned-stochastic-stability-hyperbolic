module
public import LeanShared.Analysis.GraphProjectionDistance
public import LeanShared.Analysis.ProjectedEndpointMap

/-! Actual kernel planes of close stable projections are close in the true
orthogonal-projection norm, with fixed explicit constants. -/
public noncomputable section
namespace LeanShared.NearOrthogonalStableProjection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem kernel_close (V : Submodule ℝ E) (R : E→L[ℝ]E)
    (dimension : Module.finrank ℝ R.ker=Module.finrank ℝ V)
    (close : ‖R-Vᗮ.starProjection‖≤(1/64:ℝ)) :
    ‖V.starProjection-R.ker.starProjection‖≤(1/16:ℝ) := by
  apply (GraphProjectionDistance.bound V R.ker dimension (by norm_num : (0:ℝ)≤1/32) ?_).trans_eq
    (by norm_num)
  intro v
  have zero : R v.val=0 := v.property
  have error := ((R-Vᗮ.starProjection).le_opNorm v.val).trans
    (mul_le_mul_of_nonneg_right close (norm_nonneg _))
  change ‖R v.val-Vᗮ.starProjection v.val‖≤_ at error
  rw [zero,zero_sub,norm_neg] at error
  have triangle : ‖v.val‖≤‖V.starProjection v.val‖+‖Vᗮ.starProjection v.val‖ := by
    simpa only [V.starProjection_add_starProjection_orthogonal] using
      norm_add_le (V.starProjection v.val) (Vᗮ.starProjection v.val)
  change ‖Vᗮ.starProjection v.val‖≤(1/32:ℝ)*‖V.starProjection v.val‖
  nlinarith [norm_nonneg (V.starProjection v.val)]

theorem complement_close (V : Submodule ℝ E) (R:E→L[ℝ]E)
    (close : ‖R-Vᗮ.starProjection‖≤(1/64:ℝ)) :
    ‖(ContinuousLinearMap.id ℝ E-R)-V.starProjection‖≤(1/16:ℝ) := by
  have equality : (ContinuousLinearMap.id ℝ E-R)-V.starProjection=
      -(R-Vᗮ.starProjection) := by
    rw [V.starProjection_orthogonal]
    abel
  rw [equality,norm_neg]
  exact close.trans (by norm_num)
end LeanShared.NearOrthogonalStableProjection
