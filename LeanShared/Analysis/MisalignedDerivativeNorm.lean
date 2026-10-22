module
public import LeanShared.Analysis.NearIdentityEquivalenceBounds

/-! Actual centered derivative error caused by the inverse nearby-target
coordinate transport. All factors remain the native operator norms. -/
public noncomputable section
namespace LeanShared.MisalignedDerivativeNorm
variable {E P Q:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]

theorem inverse_transport_error (R:E≃L[ℝ]E) (L:Q≃L[ℝ]E) (A:P→L[ℝ]E)
    {θ:ℝ} (small:θ<1) (bound:‖R.toContinuousLinearMap-ContinuousLinearMap.id ℝ E‖≤θ) :
    ‖L.symm.toContinuousLinearMap.comp A-
      L.symm.toContinuousLinearMap.comp (R.symm.toContinuousLinearMap.comp A)‖≤
      ‖L.symm.toContinuousLinearMap‖*(θ/(1-θ))*‖A‖ := by
  have identity : L.symm.toContinuousLinearMap.comp A-
      L.symm.toContinuousLinearMap.comp (R.symm.toContinuousLinearMap.comp A)=
      L.symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.id ℝ E-R.symm.toContinuousLinearMap).comp A) := by
    ext v
    simp only [sub_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply,map_sub]
  rw [identity]
  calc
    _ ≤ ‖L.symm.toContinuousLinearMap‖*
        ‖(ContinuousLinearMap.id ℝ E-R.symm.toContinuousLinearMap).comp A‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖L.symm.toContinuousLinearMap‖*
        (‖ContinuousLinearMap.id ℝ E-R.symm.toContinuousLinearMap‖*‖A‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ ‖L.symm.toContinuousLinearMap‖*((θ/(1-θ))*‖A‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa only [norm_sub_rev] using NearIdentityEquivalenceBounds.inverse_sub_id_norm_le R θ small bound
    _ = _ := (mul_assoc _ _ _).symm
end LeanShared.MisalignedDerivativeNorm
