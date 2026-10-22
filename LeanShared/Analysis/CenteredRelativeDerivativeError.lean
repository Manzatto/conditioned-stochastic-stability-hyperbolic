module
public import LeanShared.Analysis.CenteredTargetFrameChange
public import LeanShared.Analysis.NearIdentityEquivalenceBounds

/-! Target-frame perturbation measured against the derivative in the
bounded reference frame. No bound on the inverse frame at a nearby point
outside the smaller compact patch is assumed. -/
public noncomputable section
namespace LeanShared.CenteredManifoldCoordinates
variable {P Q E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem relative_target_derivative_error (L : P ≃L[ℝ] E) (R S : Q ≃L[ℝ] F)
    (a : E) (b c : F) (h : E → F) (z : P) (θ : ℝ) (small : θ < 1)
    (relative : ‖S.symm.toContinuousLinearMap.comp R.toContinuousLinearMap -
      ContinuousLinearMap.id ℝ Q‖ ≤ θ) :
    ‖fderiv ℝ (centered L S a c h) z - fderiv ℝ (centered L R a b h) z‖ ≤
      (θ / (1 - θ)) * ‖fderiv ℝ (centered L S a c h) z‖ := by
  let A := R.trans S.symm
  let D := fderiv ℝ (centered L S a c h) z
  let B := fderiv ℝ (centered L R a b h) z
  have forward : D = A.toContinuousLinearMap.comp B :=
    fderiv_centered_target_frame L R S a b c h z
  have backward : B = A.symm.toContinuousLinearMap.comp D := by
    rw [forward]
    ext v
    change B v = A.symm (A (B v))
    rw [A.symm_apply_apply]
  have error := NearIdentityEquivalenceBounds.inverse_sub_id_norm_le A θ small relative
  have identity : D - B = (ContinuousLinearMap.id ℝ Q - A.symm.toContinuousLinearMap).comp D := by
    rw [backward, ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp]
  change ‖D - B‖ ≤ (θ / (1 - θ)) * ‖D‖
  rw [identity]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (by simpa only [norm_sub_rev] using error) (norm_nonneg _))

end LeanShared.CenteredManifoldCoordinates
