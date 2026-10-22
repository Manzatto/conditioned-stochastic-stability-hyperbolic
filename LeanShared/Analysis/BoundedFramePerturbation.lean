module
public import LeanShared.Analysis.BoundedFrameNonlinearRadius
import all LeanShared.Analysis.BoundedFrameNonlinearRadius

/-! An actual first-derivative perturbation transforms under bounded frames
with the two operator-norm factors. This applies directly to literal Whitney
bounds and does not assume a perturbed adapted-coordinate estimate. -/
public noncomputable section
namespace LeanShared.BoundedFramePerturbation
open LeanShared.CenteredManifoldCoordinates

theorem derivative_difference_le
    {P Q E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] F) (a : E) (b : F) (h g : E → F)
    (z : P) (dh : DifferentiableAt ℝ h (a + L z))
    (dg : DifferentiableAt ℝ g (a + L z))
    (δ : ℝ) (close : ‖fderiv ℝ h (a + L z) - fderiv ℝ g (a + L z)‖ ≤ δ) :
    ‖fderiv ℝ (centered L R a b h) z - fderiv ℝ (centered L R a b g) z‖ ≤
      ‖R.symm.toContinuousLinearMap‖ * (δ * ‖L.toContinuousLinearMap‖) := by
  rw [BoundedFrameNonlinearRadius.derivative_at L R a b h z dh,
    BoundedFrameNonlinearRadius.derivative_at L R a b g z dg,
    ← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right close (norm_nonneg _))) (norm_nonneg _))

end LeanShared.BoundedFramePerturbation
