module
public import LeanShared.Analysis.NearIdentityEquivalenceBounds

/-! A common bound for inverse perturbations, with constants depending only
on the actual inverse bound. This supplies one hyperbolic block-image
radius for all bounded diagonal reference blocks. -/
public noncomputable section
namespace LeanShared.UniformInversePerturbationBounds
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem bound (A B : E≃L[ℝ]E) (M δ : ℝ) (nonnegativeM : 0≤M)
    (nonnegativeδ : 0≤δ) (small : M*δ≤1/2)
    (inverseBound : ‖A.symm.toContinuousLinearMap‖≤M)
    (close : ‖B.toContinuousLinearMap-A.toContinuousLinearMap‖≤δ) :
    ‖B.symm.toContinuousLinearMap-A.symm.toContinuousLinearMap‖≤2*M ^ 2*δ := by
  let R := B.trans A.symm
  have difference : R.toContinuousLinearMap-ContinuousLinearMap.id ℝ E=
      A.symm.toContinuousLinearMap.comp (B.toContinuousLinearMap-A.toContinuousLinearMap) := by
    ext v
    change A.symm (B v)-v=A.symm (B v-A v)
    rw [map_sub,A.symm_apply_apply]
  have near : ‖R.toContinuousLinearMap-ContinuousLinearMap.id ℝ E‖≤M*δ := by
    rw [difference]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul inverseBound close (norm_nonneg _) nonnegativeM)
  have half : M*δ<1 := small.trans_lt (by norm_num)
  have inverseError := NearIdentityEquivalenceBounds.inverse_sub_id_norm_le R (M*δ) half near
  have ratio : M*δ/(1-M*δ)≤2*(M*δ) := by
    apply (div_le_iff₀ (sub_pos.mpr half)).mpr
    nlinarith [mul_nonneg nonnegativeM nonnegativeδ]
  have identity : B.symm.toContinuousLinearMap-A.symm.toContinuousLinearMap=
      (R.symm.toContinuousLinearMap-ContinuousLinearMap.id ℝ E).comp A.symm.toContinuousLinearMap := by
    ext v
    change B.symm v-A.symm v=B.symm (A (A.symm v))-A.symm v
    rw [A.apply_symm_apply]
  rw [identity]
  calc
    _ ≤ ‖R.symm.toContinuousLinearMap-ContinuousLinearMap.id ℝ E‖*‖A.symm.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (2*(M*δ))*M := mul_le_mul (inverseError.trans ratio) inverseBound (norm_nonneg _) (by positivity)
    _ = _ := by ring

end LeanShared.UniformInversePerturbationBounds
