module
public import LeanShared.Geometry.CenteredManifoldCoordinates
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Exact affine-frame derivative transport, valid also when the totalized
derivative is zero at a nondifferentiability point. -/
public noncomputable section
namespace LeanShared.CenteredManifoldCoordinates
variable {P Q E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_centered (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] F)
    (a : E) (b : F) (h : E → F) (z : P) :
    fderiv ℝ (centered L R a b h) z = R.symm.toContinuousLinearMap.comp
      ((fderiv ℝ h (a + L z)).comp L.toContinuousLinearMap) := by
  have identity : centered L R a b h =
      R.symm ∘ (fun v => h (a + v) - b) ∘ L := rfl
  rw [identity, ContinuousLinearEquiv.comp_fderiv,
    ContinuousLinearEquiv.comp_right_fderiv, fderiv_sub_const,
    fderiv_comp_add_left]

theorem centered_derivative_difference_le (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] F)
    (a : E) (b : F) (h g : E → F) (z : P) :
    ‖fderiv ℝ (centered L R a b h) z - fderiv ℝ (centered L R a b g) z‖ ≤
      ‖R.symm.toContinuousLinearMap‖ *
        (‖fderiv ℝ h (a + L z) - fderiv ℝ g (a + L z)‖ * ‖L.toContinuousLinearMap‖) := by
  rw [fderiv_centered, fderiv_centered,
    ← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))

theorem centered_value_difference_le (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] F)
    (a : E) (b : F) (h g : E → F) (z : P) :
    ‖centered L R a b h z - centered L R a b g z‖ ≤
      ‖R.symm.toContinuousLinearMap‖ * ‖h (a + L z) - g (a + L z)‖ := by
  simp only [centered, ← map_sub, sub_sub_sub_cancel_right]
  exact R.symm.toContinuousLinearMap.le_opNorm _

end LeanShared.CenteredManifoldCoordinates
